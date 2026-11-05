module
public import Goldilocks.AC.State
public import Goldilocks.Broadcast
public import Spec2.Defs.Notation

@[expose] public section

/-!
# The fork choice and the Goldfish vote

The Goldfish fork choice walks from a start block down a tree of blocks, at each step to the child
with the highest Goldfish score among those the walk may step onto, and stops where there is none.
The Goldfish vote duty votes for the block the walk returns in the tree the voter has seen by the
previous slot's view freeze.

This file declares, in the namespace `Goldilocks`:

- the score: `supports` (whether a vote supports a block) and `goldfish_score`;
- the walk `ghost(anchor, tree, score, eligible)` and its parts `outranks`, `is_best_in`,
  `argmax?`, `ghost_children`, `ghost_step`, `ghost_walk`;
- `goldfish_eligible`, whether the walk may step onto a block, and `goldfish_fork_choice`;
- `viable_tree`, the blocks of a tree that descend from the frame's root of the fork choice and
  lead to one of its viable heads; `get_anchor`, the block every walk of a duty starts from;
  `get_head_in_tree` and `get_head`, the head;
- `voter_block_tree`, the blocks the voter of a slot has seen, and `goldfish_vote`, the duty.

Ties between two blocks, in the walk and in the deepest block, are decided by the root order
`RootOrder`. The score, the walk and the eligibility test may raise: a vote's head is looked up by
root in the frame's tree, and the lookup raises when two blocks of the tree share that root. The
walk takes the score and the eligibility test as arguments, so it raises where they do.

This file holds definitions only.
-/

open scoped DC

open DC (DRE)

namespace Goldilocks

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-! ## The Goldfish score -/

/-- `supports Φ B vote`: whether the Goldfish vote `vote` supports the block `B`: `Φ.tree` holds a
block whose root is the vote's head root `vote.head`, and `B` is an ancestor of that block or the
block itself. A head that `Φ.tree` does not hold supports nothing.

Raises when two blocks of `Φ.tree` have the root `vote.head`: roots name blocks uniquely. -/
@[no_expose] def supports (Φ : Frame V) (B : Block V) (vote : GoldfishVote V) : DRE Bool := do
  let H? ← blockWithRoot Φ.tree vote.head
  if H? ≠ none then
    return B.ancestorEq H?.value
  return false

/-- `goldfish_score Φ votes support_votes s B`: the Goldfish score of the block `B` in slot `s`:
the number of validators that hold two distinct votes in `votes` (`equivocators`, which count for
every block), plus the number of the other validators with a slot-`s` vote in `support_votes` that
supports `B` (`supports`).

Raises when two blocks of `Φ.tree` share the head root of a vote of `support_votes`. -/
@[no_expose] def goldfish_score (Φ : Frame V) (votes support_votes : Finset (GoldfishVote V)) (s : Slot)
    (B : Block V) : DRE Nat := do
  let equivocators := equivocators votes
  let supporting ← {vote ∈ᴹ support_votes | vote.val_index ∉ equivocators && vote.slot = s &&
    (← supports Φ B vote)}
  let supporters := {vote.val_index | vote ∈ supporting}
  return |equivocators| + |supporters|

/-! ## The walk -/

/-- `outranks score B C`: whether the block `B` beats the block `C` in the walk's order: a higher
score, or the same score and the root of `C` before the root of `B` in the root order
(`RootOrder.before`).

Raises when the score of `B` or of `C` raises. -/
@[no_expose] def outranks (score : (B : Block V) → DRE Nat) (B C : Block V) : DRE Bool := do
  let score_B ← score B
  let score_C ← score C
  return (score_C < score_B) || ((score_C = score_B) && RootOrder.before C.root B.root)

/-- `is_best_in score children B`: whether no block of `children` beats the block `B`
(`outranks`).

Raises when a score raises. -/
@[no_expose] def is_best_in (score : (B : Block V) → DRE Nat) (children : Finset (Block V)) (B : Block V) :
    DRE Bool := do
  let beaters ← children.filterM fun C => outranks score C B
  return beaters = ∅

/-- `argmax? score children`: the one block of `children` that no other beats (`is_best_in`), or
none when `children` is empty or when two blocks share the best score and root.

Raises when a score raises. -/
@[no_expose] def argmax? (score : (B : Block V) → DRE Nat) (children : Finset (Block V)) :
    DRE (Option (Block V)) := do
  let best ← children.filterM (is_best_in score children)
  return pickUnique? best (fun _ => true)

/-- `ghost_children tree eligible H`: the children of `H` in `tree` on which the walk may step:
the blocks of `tree` whose parent is `H` and that are `eligible`.

Raises when the eligibility test raises. -/
@[no_expose] def ghost_children (tree : Finset (Block V)) (eligible : (B : Block V) → DRE Bool)
    (H : Block V) : DRE (Finset (Block V)) :=
  tree.filterM fun B => do
    if B.parent? = H then eligible B else return false

/-- `ghost_step tree score eligible H`: one step of the walk from `H`: the best of its eligible
children (`argmax?`), or none.

Raises when the score or the eligibility test raises. -/
@[no_expose] def ghost_step (tree : Finset (Block V)) (score : (B : Block V) → DRE Nat)
    (eligible : (B : Block V) → DRE Bool) (H : Block V) : DRE (Option (Block V)) := do
  let children ← ghost_children tree eligible H
  argmax? score children

/-- `ghost_walk tree score eligible n H`: the descent of at most `n` steps from `H`: stop at `H`
when no step is possible (`ghost_step`), otherwise continue from the best child.

Raises when the score or the eligibility test raises. -/
@[no_expose] def ghost_walk (tree : Finset (Block V)) (score : (B : Block V) → DRE Nat)
    (eligible : (B : Block V) → DRE Bool) : (n : Nat) → (H : Block V) → DRE (Block V)
  | 0, H => return H
  | n + 1, H => do
    let C? ← ghost_step tree score eligible H
    if C? ≠ none then
      ghost_walk tree score eligible n C?.value
    else
      return H

/-- `ghost(anchor, tree, score, eligible)`: from `anchor`, descend through eligible children in
`tree`, taking the highest score at each step, and stop where no child is eligible; at most
`|tree|` steps (`ghost_walk`), since every step moves to a member of `tree` of greater depth. The
walk starts at `anchor` also when `anchor` is not in `tree`.

Raises when the score or the eligibility test raises. -/
@[no_expose] def ghost (anchor : Block V) (tree : Finset (Block V)) (score : (B : Block V) → DRE Nat)
    (eligible : (B : Block V) → DRE Bool) : DRE (Block V) :=
  ghost_walk tree score eligible |tree| anchor

/-! ## The Goldfish fork choice -/

/-- Whether the walk may step onto the block `B`, at the time `t`:

1. `true` when `B`'s parent is not a viable head of the frame (`Φ.viable_heads`);
2. otherwise, `true` when `B` is a block of the current slot `C.slot t`;
3. otherwise, whether twice `B`'s Goldfish score (`goldfish_score`) is more than the number of
   validators with a vote in `votes` (`voters_count`).

Raises when `goldfish_score` does: when two blocks of `Φ.tree` share the head root of a vote of
`support_votes`. -/
@[no_expose] def goldfish_eligible (C : Config) (Φ : Frame V) (t : Time)
    (votes support_votes : Finset (GoldfishVote V)) (s : Slot) (B : Block V) : DRE Bool := do
  if B.parent ∉ Φ.viable_heads then
    return true
  if B.slot = C.slot t then
    return true
  let voters_count := voters_count votes
  let score ← goldfish_score Φ votes support_votes s B
  return voters_count < 2 * score

/-- The Goldfish fork choice from `anchor` through `tree`, at the time `t`: the walk `ghost` with
the score `goldfish_score` and the eligibility test `goldfish_eligible` of the votes `votes`, the
support votes `support_votes` and the slot `s`.

Raises when a score raises: when two blocks of `Φ.tree` share the head root of a vote of
`support_votes`. -/
@[no_expose] def goldfish_fork_choice (C : Config) (Φ : Frame V) (t : Time) (anchor : Block V)
    (tree : Finset (Block V)) (votes support_votes : Finset (GoldfishVote V)) (s : Slot) :
    DRE (Block V) :=
  ghost anchor tree (goldfish_score Φ votes support_votes s)
    (goldfish_eligible C Φ t votes support_votes s)

/-! ## The viable tree, the anchor and the head -/

/-- `viable_tree Φ tree`: the blocks `B` of `tree` that are `Φ.fc_root` or a descendant of it,
and are an ancestor of, or equal to, a block of `tree` that is a viable head of the frame
(`Φ.viable_heads`). -/
@[no_expose] def viable_tree (Φ : Frame V) (tree : Finset (Block V)) : Finset (Block V) :=
  {B ∈ tree | Φ.fc_root.ancestorEq B && ∃ W ∈ tree ∩ Φ.viable_heads, B.ancestorEq W}

/-- `get_anchor A Φ t`: the block every walk of a duty starts from, at the time `t`: the deepest
block (`Block.deepest?`) of the viable tree of `Φ.tree` that is locked (`is_locked`), or
`Φ.fc_root` when there is none. -/
@[no_expose] def get_anchor (A : ACState V) (Φ : Frame V) (t : Time) : Block V := Id.run do
  let anchor := Block.deepest? {B ∈ viable_tree Φ Φ.tree | is_locked A Φ t B}
  if anchor ≠ none then
    return anchor.value
  return Φ.fc_root

/-- `get_head_in_tree C A Φ t tree votes support_votes s`: the Goldfish fork choice
(`goldfish_fork_choice`) through `tree`, from the anchor `get_anchor A Φ t`.

Raises when the fork choice does. -/
@[no_expose] def get_head_in_tree (C : Config) (A : ACState V) (Φ : Frame V) (t : Time)
    (tree : Finset (Block V)) (votes support_votes : Finset (GoldfishVote V)) (s : Slot) :
    DRE (Block V) := do
  let anchor := get_anchor A Φ t
  goldfish_fork_choice C Φ t anchor tree votes support_votes s

/-- `get_head C A Φ t votes support_votes s`: the head (`get_head_in_tree`) through the viable tree
of `Φ.tree`.

Raises when the fork choice does. -/
@[no_expose] def get_head (C : Config) (A : ACState V) (Φ : Frame V) (t : Time)
    (votes support_votes : Finset (GoldfishVote V)) (s : Slot) : DRE (Block V) :=
  get_head_in_tree C A Φ t (viable_tree Φ Φ.tree) votes support_votes s

/-! ## The Goldfish vote -/

/-- `voter_block_tree C A Φ s`: the blocks the voter of slot `s` has seen: each block `B` of
`Φ.tree` stamped strictly before the view freeze of slot `s − 1`, `C.t_ (s - 1) + 3 * C.Δ`,
together with each block of `Φ.tree` that is an ancestor of, or equal to, a slot-`s` block of
`Φ.tree`. At `s = 0` the slot `s − 1` reads as slot `0`.

Raises when a block of `Φ.tree` has no stamp. -/
@[no_expose] def voter_block_tree (C : Config) (A : ACState V) (Φ : Frame V) (s : Slot) :
    DRE (Finset (Block V)) := do
  let freeze := C.t_ (s - 1) + 3 * C.Δ
  let proposals := {B' ∈ Φ.tree | B'.slot = s}
  let blocks ← {B ∈ᴹ Φ.tree | ((← A.timestamp_block B) < (freeze : Stamp)) ||
    (∃ B' ∈ proposals, B.ancestorEq B')}
  return blocks

/-- The Goldfish vote duty of the validator `v` at the time `t`, in the slot `s := C.slot t`.
Write `freeze` for the view freeze of slot `s − 1`, `C.t_ (s - 1) + 3 * C.Δ`; at `s = 0` the slot
`s − 1` reads as slot `0`.

1. `votes`: the slot-`(s − 1)` votes of `A` stamped strictly before `freeze`; `support_votes`: the
   votes of `votes` whose resolution time (`A.tau`) is strictly before `freeze`.
2. The votes included in the slot-`s` blocks of `Φ.tree` are added to `votes`
   (`included_votes`), and the support votes they include whose head is resolved in `Φ.tree`
   (`resolved`) to `support_votes`.
3. `tree`: the viable tree of the blocks the voter has seen (`voter_block_tree`).
4. `H`: the head of `tree` for the slot `s − 1` (`get_head_in_tree`).
5. If `v` is in the committee `P.committee s`, its vote for `H` is broadcast and admitted
   (`on_goldfish_vote`); otherwise `A` is returned unchanged.

Raises when a vote of `A.pool (s − 1)` or a block of `Φ.tree` has no stamp, or when two blocks of
`Φ.tree` share a root. -/
@[no_expose] def goldfish_vote (C : Config) (P : Provisional V) (A : ACState V) (Φ : Frame V) (t : Time)
    (v : V) : DREB V (ACState V) := do
  let s := C.slot t
  let freeze := C.t_ (s - 1) + 3 * C.Δ
  let mut votes ← beforeCutoff A.timestamp_vote freeze (A.pool (s - 1))
  let mut support_votes ← {vote ∈ᴹ votes | occurrenceBefore (← A.tau Φ vote) freeze}
  votes ← votes ∪ included_votes Φ s
  let included_support ← {vote ∈ᴹ included_support_votes Φ s | (← resolved Φ.tree vote)}
  support_votes ← support_votes ∪ included_support
  let tree := viable_tree Φ (← voter_block_tree C A Φ s)
  let H ← get_head_in_tree C A Φ t tree votes support_votes (s - 1)
  if v ∈ P.committee s then
    let vote := GoldfishVote.mk (val_index := v) (slot := s) (head := H.root)
    broadcast (NamedObject.gfVote vote)
    return on_goldfish_vote C P A t vote
  return A

end Goldilocks
