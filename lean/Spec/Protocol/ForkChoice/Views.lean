import Spec.Store
import Spec.Defs.Notation

/-!
# The voter's and the proposer's views, over the flat store

The routines that read, off the flat store `Store V` of `lean/Spec/Store.lean`, the votes and
the blocks the voter or the proposer of slot `s` counts, in the namespace
`Spec.Protocol`:

- `voter_view`: the votes the slot-`s` voter counts;
- `voter_support_view`: the votes the slot-`s` voter counts as support;
- `voter_processed_block_tree`: the blocks the slot-`s` voter walks over;
- `proposer_view`: the votes the slot-`s` proposer counts;
- `proposer_support_view`: the votes the slot-`s` proposer counts as support.

They call `beforeCutoff`, `occurrenceBefore` and `resolved`, declared in
`lean/Spec/Objects.lean`.

Four of them raise: on a vote of the store's slot votes or a block of the tree with no stamp, and
on two blocks of the tree sharing the head root of a vote. `proposer_view` reads one field and
does not raise.

This file holds definitions only.
-/

open scoped DC

open DC (DRE)

namespace Spec.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]
variable (C : Config)

/-- The votes the slot-`s` voter counts: the slot-`(s − 1)` votes of the store's pool whose stamp
is strictly before the view freeze of slot `s − 1`, together with every slot-`(s − 1)` vote
included in a slot-`s` block of the store's tree.

Raises when a vote of the pool `st.pool (s − 1)` has no stamp: every pooled vote was stamped when
it was admitted. -/
def voter_view (st : Store V) (s : Slot) : DRE (Finset (GoldfishVote V)) := do
  let received ← beforeCutoff st.timestamp_vote (C.view_freeze (s - 1)) (st.pool (s - 1))
  return received ∪ st.included_votes s

/-- The votes the slot-`s` voter counts as support: the slot-`(s − 1)` votes of the store's pool
whose resolution time `st.tau` is strictly before the view freeze of slot `s − 1`, together with
the slot-`(s − 1)` support votes included in a slot-`s` block of the store's tree whose head is in
the tree (`resolved`).

Raises when a resolution time or a head lookup raises: when two blocks of `st.T` share a root,
when a block of `st.T` has no stamp, or when a pooled vote has no stamp. -/
def voter_support_view (st : Store V) (s : Slot) : DRE (Finset (GoldfishVote V)) := do
  let t₀ := C.view_freeze (s - 1)
  let resolvedPooled ← {vote ∈ᴹ st.pool (s - 1) | occurrenceBefore (← st.tau vote) t₀}
  let carried := st.included_support_votes s
  let resolvedCarried ← {vote ∈ᴹ carried | (← resolved st.T vote)}
  return resolvedPooled ∪ resolvedCarried

/-- The blocks the slot-`s` voter walks over: each block `B` of the store's tree `st.T` whose
stamp is strictly before the view freeze of slot `s − 1`, together with each block of `st.T` that
is an ancestor of, or equal to, some slot-`s` block of `st.T` (a current proposal).

Raises when a block of `st.T` has no stamp: every block of the tree was stamped when it entered
it. -/
def voter_processed_block_tree (st : Store V) (s : Slot) : DRE (Finset (Block V)) := do
  let t₀ := C.view_freeze (s - 1)
  let proposals := {P ∈ st.T | P.slot = s}
  let blocks ← {B ∈ᴹ st.T | ((← st.timestamp_block B) < (t₀ : Stamp)) ||
    (∃ P ∈ proposals, B.ancestorEq P = true)}
  return blocks

/-- The votes the slot-`s` proposer counts: the store's whole list `st.gf_votes (s − 1)`, with no
cutoff. It is a list because the proposal carries it as it is. -/
def proposer_view (st : Store V) (s : Slot) : List (GoldfishVote V) :=
  st.gf_votes[s - 1]

/-- The votes the slot-`s` proposer counts as support: the votes of the store's list
`st.gf_votes (s − 1)` whose head is in the store's tree (`resolved`), in list order.

Raises when two blocks of `st.T` share the head root of one of those votes. -/
def proposer_support_view (st : Store V) (s : Slot) : DRE (List (GoldfishVote V)) :=
  st.gf_votes[s - 1].filterM fun vote => resolved st.T vote

end Spec.Protocol
