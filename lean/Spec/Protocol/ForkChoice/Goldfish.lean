import Spec.Store

/-!
# The Goldfish votes, the walk and the filtered block tree

The functions of `Spec` behind the Goldfish fork choice, in the namespace
`Spec.Protocol`:

- on a set of Goldfish votes: `votes_by` (the votes of one validator), `equivocates` (two
  distinct votes of one validator), `participates` (at least one vote), the sets
  `raw_equivocators` and `raw_participants` and the count `raw_voters_count`, and
  `no_second_vote_in` (whether a set holds no second vote of a vote's validator);
- the Goldfish score: `targets_under` (whether a vote supports a block), `raw_supporters` and
  `raw_goldfish_score`;
- the walk `ghost(anchor, tree, score, eligible)` and its parts `outranks`, `is_best_in`,
  `argmax?`, `ghost_children`, `ghost_step`, `ghost_walk`;
- the viability test: `finalized_descendants`, `viable`, `viable_tree`;
- the routines that read the store: `get_fg_root`, the block the finality gadget's walk starts
  from; `get_filtered_block_tree_from` and `get_filtered_block_tree`, the blocks of a block set
  (of the store's tree) that pass the viability test and are descendants of that root; and
  `goldfish_eligible` and `goldfish_fork_choice`, the eligibility test and the walk with the
  Goldfish score.

The resolution of a vote, `resolved` and `resolution_time`, is in `lean/Spec/Objects.lean`,
since the store's reader `Store.tau` calls it.

The score, the walk and the eligibility test may raise: a vote's head is looked up by root in a
tree, and the lookup raises when two blocks of the tree share that root. The walk takes the score
and the eligibility test as arguments, so it raises where they do.

This file holds definitions only.
-/


open scoped DC

open DC (DRE)

namespace Spec.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Sets of Goldfish votes -/

/-- `votes_by votes v`: the votes of `votes` whose validator is `v`. -/
def votes_by (votes : Finset (GoldfishVote V)) (v : V) : Finset (GoldfishVote V) :=
  {vote ∈ votes | vote.val_index = v}

/-- `equivocates votes v`: whether `votes` holds two distinct votes of the validator `v`, of any
slots. -/
def equivocates (votes : Finset (GoldfishVote V)) (v : V) : Bool :=
  2 ≤ |votes_by votes v|

/-- `participates votes v`: whether `votes` holds a vote of the validator `v`. -/
def participates (votes : Finset (GoldfishVote V)) (v : V) : Bool :=
  0 < |votes_by votes v|

/-- `no_second_vote_in late vote`: whether every vote of `late` is `vote` itself or a vote of
another validator than `vote`'s. -/
def no_second_vote_in (late : Finset (GoldfishVote V)) (vote : GoldfishVote V) : Bool :=
  ∀ u ∈ late, u = vote ∨ u.val_index ≠ vote.val_index

/-- `targets_under T B vote`: whether the Goldfish vote `vote` supports the block `B` in the block
tree `T`: `T` holds a block `B'` whose root is the vote's head root `vote.head`, `B'`'s slot is at
most the vote's slot, and `B` is an ancestor of `B'` or `B'` itself. A head that `T` does not
hold supports nothing.

Raises when two blocks of `T` have the root `vote.head`: roots name blocks uniquely. -/
def targets_under (T : Finset (Block V)) (B : Block V) (vote : GoldfishVote V) :
    DRE Bool := do
  let B'? ← blockWithRoot T vote.head
  if B'? ≠ none then
    let B' := B'?.value
    return (B'.slot ≤ vote.slot) && B.ancestorEq B'
  return false

/-- `raw_equivocators votes`: the validators that equivocate in `votes`. -/
def raw_equivocators (votes : Finset (GoldfishVote V)) : Finset V :=
  {v ∈ Finset.univ | equivocates votes v = true}

/-- `raw_participants votes`: the validators with a vote in `votes`. -/
def raw_participants (votes : Finset (GoldfishVote V)) : Finset V :=
  {v ∈ Finset.univ | participates votes v = true}

/-- `raw_voters_count votes`: the number of validators with a vote in `votes`. -/
def raw_voters_count (votes : Finset (GoldfishVote V)) : Nat :=
  |raw_participants votes|

/-- `raw_supporters T votes support_votes s B`: the validators that support the block `B` in slot
`s`: the validators that do not equivocate in `votes` and have a slot-`s` vote in
`support_votes` that supports `B` in the tree `T` (`targets_under`).

Raises when `targets_under` does: when two blocks of `T` share the head root of a slot-`s` vote
of `support_votes`. -/
def raw_supporters (T : Finset (Block V))
    (votes support_votes : Finset (GoldfishVote V)) (s : Slot) (B : Block V) :
    DRE (Finset V) := do
  let supporting ← support_votes.filterM fun vote => do
    if vote.slot = s then targets_under T B vote else return false
  return {v ∈ Finset.univ | equivocates votes v = false && ∃ vote ∈ supporting, vote.val_index = v}

/-- `raw_goldfish_score T votes support_votes s B`: the Goldfish score of the block `B` in slot
`s`: the number of validators that equivocate in `votes` (they count for every block) plus the
number of supporters of `B` (`raw_supporters`).

Raises when `raw_supporters` does. -/
def raw_goldfish_score (T : Finset (Block V))
    (votes support_votes : Finset (GoldfishVote V)) (s : Slot) (B : Block V) : DRE Nat := do
  let supporters ← raw_supporters T votes support_votes s B
  return |raw_equivocators votes| + |supporters|

/-! ## The walk -/

/-- `outranks score B C`: whether the block `B` beats the block `C` in the walk's order: a higher
score, or the same score and a greater root.

Raises when the score of `B` or of `C` raises. -/
def outranks (score : Block V → DRE Nat) (B C : Block V) : DRE Bool := do
  let score_B ← score B
  let score_C ← score C
  return (score_C < score_B) || ((score_C = score_B) && (C.root < B.root))

/-- `is_best_in score children B`: whether no block of `children` beats the block `B`
(`outranks`).

Raises when a score raises. -/
def is_best_in (score : Block V → DRE Nat) (children : Finset (Block V)) (B : Block V) :
    DRE Bool := do
  let beaters ← children.filterM fun C => outranks score C B
  return beaters = ∅

/-- `argmax? score children`: the one block of `children` that no other beats (`is_best_in`), or
none when `children` is empty or when two blocks share the best score and root.

Raises when a score raises. -/
def argmax? (score : Block V → DRE Nat) (children : Finset (Block V)) :
    DRE (Option (Block V)) := do
  let best ← children.filterM (is_best_in score children)
  return pickUnique? best (fun _ => true)

/-- `ghost_children tree eligible H`: the children of `H` in `tree` on which the walk may step:
the blocks of `tree` whose parent is `H` and that are `eligible`.

Raises when the eligibility test raises. -/
def ghost_children (tree : Finset (Block V)) (eligible : Block V → DRE Bool) (H : Block V) :
    DRE (Finset (Block V)) :=
  tree.filterM fun B => do
    if B.parent? = H then eligible B else return false

/-- `ghost_step tree score eligible H`: one step of the walk from `H`: the best of its eligible
children (`argmax?`), or none.

Raises when the score or the eligibility test raises. -/
def ghost_step (tree : Finset (Block V)) (score : Block V → DRE Nat)
    (eligible : Block V → DRE Bool) (H : Block V) : DRE (Option (Block V)) := do
  let children ← ghost_children tree eligible H
  argmax? score children

/-- `ghost_walk tree score eligible n H`: the descent of at most `n` steps from `H`: stop at `H`
when no step is possible (`ghost_step`), otherwise continue from the best child.

Raises when the score or the eligibility test raises. -/
def ghost_walk (tree : Finset (Block V)) (score : Block V → DRE Nat)
    (eligible : Block V → DRE Bool) : Nat → Block V → DRE (Block V)
  | 0, H => return H
  | n + 1, H => do
    let C? ← ghost_step tree score eligible H
    if C? ≠ none then
      ghost_walk tree score eligible n C?.value
    else
      return H

/-- `ghost(anchor, tree, score, eligible)`: from `anchor`, descend through eligible children in
`tree`, taking the highest score at each step, and stop where no child is eligible; at most
`|tree|` steps (`ghost_walk`), since every step moves to a member of `tree` of greater depth.

Raises when the score or the eligibility test raises. -/
def ghost (anchor : Block V) (tree : Finset (Block V)) (score : Block V → DRE Nat)
    (eligible : Block V → DRE Bool) : DRE (Block V) :=
  ghost_walk tree score eligible |tree| anchor

/-! ## The viability test -/

/-- `finalized_descendants F T`: the blocks of `T` that are descendants of the block `F`, `F`
itself included. -/
def finalized_descendants (F : Block V) (T : Finset (Block V)) : Finset (Block V) :=
  {B ∈ T | F.ancestorEq B = true}

/-- `viable σ h_max T B`: whether `B` is an ancestor of, or equal to, a block `W` of `T` whose
chain-state height `(σ W).h` is at least `h_max − 1` (in natural numbers, so at least `0` when
`h_max = 0`). -/
def viable (σ : Block V → ChainState V) (h_max : Height) (T : Finset (Block V))
    (B : Block V) : Bool :=
  ∃ W ∈ T, B.AncestorEq W ∧ h_max - 1 ≤ (σ W).h

/-- `viable_tree σ F h_max T`: the blocks of `T` that are descendants of `F` (`F` itself
included) and pass the viability test `viable σ h_max T`. -/
def viable_tree (σ : Block V → ChainState V) (F : Block V) (h_max : Height)
    (T : Finset (Block V)) : Finset (Block V) :=
  {B ∈ finalized_descendants F T | viable σ h_max T B = true}

/-! ## The routines that read the store -/

/-- `get_fg_root(st)`: the block the walk starts from. It is the justified block `st.J` when the
largest chain-state height `st.h_max` the store has seen is exactly one above the justified
height `st.h_j`, and the finalized block `st.F` otherwise. -/
def get_fg_root (st : Store V) : Block V := Id.run do
  if st.h_max = st.h_j + 1 then
    return st.J
  return st.F

/-- The tree the composed head walks in, computed inside the block set `blocks`: the blocks of
`blocks` that are descendants of the store's finalized block `st.F` and pass the viability test
with every witness taken from `blocks`, and that are descendants of the root `get_fg_root st`
(the root itself included). The state map `st.σ`, the finalized block `st.F`, the largest
chain-state height `st.h_max` and the root are the store's own, not recomputed inside `blocks`. -/
def get_filtered_block_tree_from (st : Store V) (blocks : Finset (Block V)) :
    Finset (Block V) := Id.run do
  let root := get_fg_root st
  return {B ∈ viable_tree st.σ st.F st.h_max blocks | root.ancestorEq B = true}

/-- `get_filtered_block_tree(st)`: the tree the composed head walks in, computed inside the
store's whole tree `st.T`. -/
def get_filtered_block_tree (st : Store V) : Finset (Block V) :=
  get_filtered_block_tree_from st st.T

/-- Whether the walk may step onto the block `B`: the chain-state height of `B`'s parent is
below `h_max − 1`, or twice `B`'s Goldfish score `raw_goldfish_score` is more than the number
of validators with a vote in `votes` (`raw_voters_count`), or `B` is a block of the current slot
`cur`.

Raises when `raw_goldfish_score` does: when two blocks of `T` share the head root of a slot-`s`
vote of `support_votes`. -/
def goldfish_eligible (σ : (B : Block V) → ChainState V) (h_max : Height)
    (T : Finset (Block V)) (cur : Slot) (votes support_votes : Finset (GoldfishVote V))
    (s : Slot) (B : Block V) : DRE Bool := do
  let score ← raw_goldfish_score T votes support_votes s B
  return ((σ B.parent).h < h_max - 1) ||
    (raw_voters_count votes < 2 * score) ||
    (B.slot = cur)

/-- The Goldfish fork choice from `anchor` through `tree`: the walk `ghost` with the score
`raw_goldfish_score` and the eligibility test `goldfish_eligible` of the votes `votes`, the support
votes `support_votes` and the slot `s`, ancestry read in the block tree `T`, `σ` the state map,
`h_max` the largest chain-state height and `cur` the current slot.

Raises when a score raises: when two blocks of `T` share the head root of a slot-`s` vote of
`support_votes`. -/
def goldfish_fork_choice (σ : (B : Block V) → ChainState V) (h_max : Height)
    (T : Finset (Block V)) (cur : Slot) (anchor : Block V) (tree : Finset (Block V))
    (votes support_votes : Finset (GoldfishVote V)) (s : Slot) : DRE (Block V) :=
  ghost anchor tree (raw_goldfish_score T votes support_votes s)
    (goldfish_eligible σ h_max T cur votes support_votes s)

end Spec.Protocol
