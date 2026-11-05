module
public import Mathlib.Data.Finset.Option
public import Goldilocks.AC.ForkChoice
public import Spec2.Defs.Notation
public import Spec2.Defs.Raise

@[expose] public section

/-!
# The confirmation update and the locks

At the support cutoff of slot `s`, the available chain evaluates slot `s − 1` once: it walks from
the frame's finalized block `Φ.F` through the children that hold a strict majority of the slot's
participants, saves the result, and, unless a live lock conflicts with it, advances the record of
the confirmed tip and writes one lock entry. At the vote time of slot `s`, before the vote, it
moves each live lock entry back to the deepest block that fewer than half of the committee of slot
`s − 1` oppose.

This file declares, in the namespace `Goldilocks`:

- the revocation of the locks: `opposes` (whether a vote's head conflicts with a block),
  `opponents`, `live_entries`, `moved_entry`, `present` and `revoke_locks`;
- the advance of the record of the confirmed tip, `advance`;
- the two lock tests of the confirmation update: `fast_test`, and `slow_test` with
  `slots_before` and `saved_extends`;
- `update_confirmation`, the confirmation update.

This file holds definitions only.
-/

open scoped DC

open DC (DRE)

namespace Goldilocks

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-! ## The revocation of the locks -/

/-- `opposes Φ B' vote`: whether the head of the Goldfish vote `vote` conflicts with the block
`B'`: `Φ.tree` holds a block whose root is `vote.head`, and that block conflicts with `B'`. A head
that `Φ.tree` does not hold opposes nothing.

Raises when two blocks of `Φ.tree` have the root `vote.head`: roots name blocks uniquely. -/
@[no_expose] def opposes (Φ : Frame V) (B' : Block V) (vote : GoldfishVote V) : DRE Bool := do
  let H? ← blockWithRoot Φ.tree vote.head
  if H? ≠ none then
    return H?.value.conflicts B'
  return false

/-- `opponents A Φ votes equivocators B'`: the validators not in `equivocators` with a vote in
`votes` that resolves (its resolution time `A.tau Φ vote` is not `none`) and whose head conflicts
with `B'` (`opposes`).

Raises when a resolution time or a head lookup raises: when two blocks of `Φ.tree` share a root,
or when a vote of `votes` or a block of `Φ.tree` has no stamp. -/
@[no_expose] def opponents (A : ACState V) (Φ : Frame V) (votes : Finset (GoldfishVote V))
    (equivocators : Finset V) (B' : Block V) : DRE (Finset V) := do
  let opposing ← {vote ∈ᴹ votes | vote.val_index ∉ equivocators && (← A.tau Φ vote) ≠ none &&
    (← opposes Φ B' vote)}
  return {vote.val_index | vote ∈ opposing}

/-- `live_entries A Φ t`: the lock entries of `A` that are live at the time `t` (`is_live`). -/
@[no_expose] def live_entries (A : ACState V) (Φ : Frame V) (t : Time) : Finset (LockEntry V) :=
  {e ∈ A.lock_entries | is_live Φ t e}

/-- `moved_entry P A Φ votes equivocators s e`: the lock entry `e` moved back to the deepest block
(`Block.deepest?`) `B'` of `Φ.tree` that is not the genesis block, is an ancestor of `e.B` or
`e.B` itself, and whose opponents (`opponents A Φ votes equivocators B'`) are, counted twice, fewer
than the committee `P.committee (s - 1)`; the entry keeps its deadline `e.d`. `none` when there is
no such block.

Raises when `opponents` does. -/
@[no_expose] def moved_entry (P : Provisional V) (A : ACState V) (Φ : Frame V)
    (votes : Finset (GoldfishVote V)) (equivocators : Finset V) (s : Slot) (e : LockEntry V) :
    DRE (Option (LockEntry V)) := do
  let candidates ← {B' ∈ᴹ Φ.tree | B' ≠ Block.genesis && B'.ancestorEq e.B &&
    2 * |(← opponents A Φ votes equivocators B')| < |P.committee (s - 1)|}
  let moved := Block.deepest? candidates
  if moved ≠ none then
    return LockEntry.mk (B := moved.value) (d := e.d)
  return none

/-- `present S`: the values held by the members of `S` that are not `none`. -/
@[no_expose] def present {α : Type} [DecidableEq α] (S : Finset (Option α)) : Finset α :=
  S.biUnion Option.toFinset

/-- The revocation of the locks at the time `t`, the vote time of slot `s`, against the votes of
slot `s − 1`. At `s = 0` there is no earlier slot and `A` is returned unchanged; so `s − 1` is read
only when `s ≥ 1`.

Write `votes` for `A.pool (s − 1)` and `equivocators` for the validators that hold two distinct
votes in it. The lock entries become the live entries (`live_entries`), each moved back
(`moved_entry`); an entry with no block to move to is deleted.

Raises when `moved_entry` does. -/
@[no_expose] def revoke_locks (P : Provisional V) (A : ACState V) (Φ : Frame V) (t : Time) (s : Slot) :
    DRE (ACState V) := do
  let mut A := A
  if s = 0 then
    return A
  let votes := A.pool (s - 1)
  let equivocators := equivocators votes
  let moved ← (live_entries A Φ t).imageM (moved_entry P A Φ votes equivocators s)
  A.lock_entries ← present moved
  return A

/-! ## The record of the confirmed tip -/

/-- `advance Φ old C?`: the record of the confirmed tip `old` after the confirmation `C?`:

1. `old` when there is no confirmation (`C?` is `none`);
2. `old` when `old` is in `Φ.tree` and the confirmation is an ancestor of `old` or `old` itself;
3. otherwise the confirmation: an extension of `old` or a block that conflicts with it. -/
@[no_expose] def advance (Φ : Frame V) (old : Block V) (C? : Option (Block V)) : Block V := Id.run do
  if C? ≠ none then
    if old ∈ Φ.tree && C?.value.ancestorEq old then
      return old
    return C?.value
  return old

/-! ## The lock tests -/

/-- `slots_before s' k`: the `k − 1` slots before the slot `s'`, from `s' + 1 − k` to `s' − 1`,
when `k − 1 ≤ s'`. -/
@[no_expose] def slots_before (s' : Slot) (k : Nat) : Finset Slot :=
  {s' + 1 - k + i | i ∈ Finset.range (k - 1)}

/-- `saved_extends A Φ s'' B`: whether the saved confirmation of the slot `s''` is a block of
`Φ.tree` of which `B` is an ancestor, or which is `B`. `false` when slot `s''` has no saved
confirmation. -/
@[no_expose] def saved_extends (A : ACState V) (Φ : Frame V) (s'' : Slot) (B : Block V) : Bool := Id.run do
  if A.saved_confirmation[s''] ≠ none then
    let saved := A.saved_confirmation[s''].value
    return saved ∈ Φ.tree && B.ancestorEq saved
  return false

/-- `slow_test C A Φ s' B`: the slow test of the block `B` in the update of the slot `s'`: the
saved confirmations of the `C.k − 1` slots before `s'` (`slots_before`) are all blocks of `Φ.tree`
of which `B` is an ancestor or which are `B` (`saved_extends`). The test is false when
`s' < C.k − 1`: some of those slots would come before slot `0`, and such a slot has no saved
confirmation. -/
@[no_expose] def slow_test (C : Config) (A : ACState V) (Φ : Frame V) (s' : Slot) (B : Block V) : Bool :=
  C.k - 1 ≤ s' ∧ ∀ s'' ∈ slots_before s' C.k, saved_extends A Φ s'' B

/-- `fast_test P Φ support_votes s' B`: the fast test of the block `B` in the update of the slot
`s'`: twice its Goldfish score (`goldfish_score` over `support_votes`, for the slot `s'`) is at
least the size of the committee `P.committee s'`.

Raises when `goldfish_score` does. -/
@[no_expose] def fast_test (P : Provisional V) (Φ : Frame V) (support_votes : Finset (GoldfishVote V))
    (s' : Slot) (B : Block V) : DRE Bool := do
  let score ← goldfish_score Φ support_votes support_votes s' B
  return |P.committee s'| ≤ 2 * score

/-! ## The confirmation update -/

/-- The confirmation update at the time `t`, the support cutoff of slot `s`, for the slot
`s' := s − 1`. At `s = 0` there is no earlier slot and `A` is returned unchanged; so `s − 1` is
read only when `s ≥ 1`.

1. `early_votes`: the votes of `A.pool s'` whose resolution time is strictly before
   `C.t_ s' + 2 * C.Δ`; `late_votes`: those stamped strictly before `C.t_ s' + 6 * C.Δ`;
   `support_votes`: the early votes whose validator has no second vote among the late votes;
   `voters_count`: the number of validators with a late vote.
2. `score B` is the Goldfish score of `B` over `support_votes` for the slot `s'`, and `B` is
   `eligible` when `voters_count < 2 * score B`. `H` is the end of the walk `ghost` from `Φ.F`
   through `Φ.tree`; the confirmation `C?` is `H` when `H` is eligible, and `none` otherwise.
3. `C?` is saved as the confirmation of slot `s'`, and the fast blocks are emptied.
4. If `C?` is a block and no live lock conflicts with it (`live_lock_vetoes`): the record of the
   confirmed tip advances (`advance`); `path` is the blocks of `Φ.tree`, other than the genesis
   block, that are ancestors of `C?` or `C?` itself; the fast blocks become the blocks of `path`
   that pass the fast test (`fast_test`); and when some block of `path` passes the fast test or
   the slow test (`slow_test`), a lock entry is added on the deepest such block
   (`Block.deepest?`), with the deadline `C.t_ (s' + C.k) + 5 * C.Δ`.

Raises when a vote of `A.pool s'` or a block of `Φ.tree` has no stamp, or when two blocks of
`Φ.tree` share a root. -/
@[no_expose] def update_confirmation (C : Config) (P : Provisional V) (A : ACState V) (Φ : Frame V)
    (t : Time) (s : Slot) : DRE (ACState V) := do
  let mut A := A
  if s = 0 then
    return A
  let s' := s - 1
  let early_votes ← {vote ∈ᴹ A.pool s' | occurrenceBefore (← A.tau Φ vote) (C.t_ s' + 2 * C.Δ)}
  let late_votes ← beforeCutoff A.timestamp_vote (C.t_ s' + 6 * C.Δ) (A.pool s')
  let support_votes := {vote ∈ early_votes | no_second_vote_in late_votes vote}
  let voters_count := voters_count late_votes
  let score : (B : Block V) → DRE Nat := goldfish_score Φ support_votes support_votes s'
  let eligible : (B : Block V) → DRE Bool := fun B => do
    return voters_count < 2 * (← score B)
  let H ← ghost Φ.F Φ.tree score eligible
  let mut C? : Option (Block V) := none
  if (← eligible H) then
    C? ← H
  A.saved_confirmation[s'] ← C?
  A.fast_blocks ← ∅
  if C? ≠ none then
    if !live_lock_vetoes A Φ t C?.value then
      A.latest_confirmed ← advance Φ A.latest_confirmed C?
      let path := {B ∈ Φ.tree | B ≠ Block.genesis && B.ancestorEq C?.value}
      let fast_blocks ← {B ∈ᴹ path | (← fast_test P Φ support_votes s' B)}
      A.fast_blocks ← fast_blocks
      let lockable ← {B ∈ᴹ path | (← fast_test P Φ support_votes s' B) || slow_test C A Φ s' B}
      let lock_block := Block.deepest? lockable
      if lock_block ≠ none then
        A.lock_entries ← A.lock_entries ∪
          {LockEntry.mk (B := lock_block.value) (d := C.t_ (s' + C.k) + 5 * C.Δ)}
  return A

end Goldilocks
