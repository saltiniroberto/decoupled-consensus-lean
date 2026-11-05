module
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.ACStoreDefs
public import GoldilocksCorrectness.Proofs.Routines.ACStore

@[expose] public section

/-!
# Relations between two node states' votes, over a model

The definitions of `GoldilocksCorrectness/Proofs/Routines/ACStore.lean` over a model `M`, read
on node states `n n' : M.N`: the relations between two node states' Goldfish votes and stamps that
the routines keep, and the conditions on one node state's votes. They are on a page of their own,
which imports no facts, because the facts of the AC-store family name them. At the spec's model each
is the landed definition applied to the node states' AC states (the equations `goldilocks_…`, in the
simp set `record_goldilocks`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Record
open GoldilocksCorrectness.Record.Statements.Routines (PoolKeyed PoolStamped)

variable {V : Type} [DecidableEq V] [Fintype V]

/-- `VotesInv M P n t`: the node state `n` holds `PoolKeyed` and `PoolStamped`, and every vote it
holds is stamped at the time `t` or earlier.

The variables:
- `M`: the model;
- `P`: the values given to the node; `n`: the node state; `t`: the time.

Read aloud: the node's votes are filed under their slots by committee members, stamped, and stamped
no later than `t`. -/
def VotesInv (M : GoldilocksModel V) (P : Provisional V) (n : M.N) (t : Time) : Prop :=
  PoolKeyed M P n ∧ PoolStamped M n ∧
    ∀ s : Slot, ∀ vote ∈ n.votesHeld s, ∀ τ : Stamp,
      n.voteStamp vote = some τ → τ ≤ (t : Stamp)

/-- `KeepsVotes M n n'`: the node state `n'` holds the votes, the vote stamps and the block
stamps of `n`.

The variables:
- `M`: the model;
- `n`, `n'`: the node states.

Read aloud: `n'` has `n`'s votes and stamps. -/
def KeepsVotes (M : GoldilocksModel V) (n n' : M.N) : Prop :=
  n'.votesHeld = n.votesHeld ∧ n'.voteStamp = n.voteStamp ∧
    n'.blockStamp = n.blockStamp

/-- `SlotKeyed M n`: every vote the node state `n` holds under the slot `s` has the slot `s`.

The variables:
- `M`: the model;
- `n`: the node state.

Read aloud: the node files each vote under its slot. -/
def SlotKeyed (M : GoldilocksModel V) (n : M.N) : Prop :=
  ∀ s : Slot, ∀ vote ∈ n.votesHeld s, vote.slot = s

/-- `ACGrows M n n'`: for every slot, the votes `n` holds are a prefix of those `n'` holds, and
every vote `n` holds has the same stamp in `n'`.

The variables:
- `M`: the model;
- `n`, `n'`: the node states.

Read aloud: `n'` extends `n`'s votes and keeps their stamps. -/
def ACGrows (M : GoldilocksModel V) (n n' : M.N) : Prop :=
  (∀ s : Slot, n.votesHeld s <+: n'.votesHeld s) ∧
    ∀ s : Slot, ∀ vote ∈ n.votesHeld s, n'.voteStamp vote = n.voteStamp vote

/-- `ACStampsAt M n n' τ`: every vote `n'` holds under a slot that `n` does not hold under it is
stamped at `τ` in `n'`.

The variables:
- `M`: the model;
- `n`, `n'`: the node states.
- `τ`: the time.

Read aloud: the votes `n'` has and `n` lacks are stamped at `τ`. -/
def ACStampsAt (M : GoldilocksModel V) (n n' : M.N) (τ : Time) : Prop :=
  ∀ s : Slot, ∀ vote ∈ n'.votesHeld s, vote ∉ n.votesHeld s →
    n'.voteStamp vote = some (τ : Stamp)

/-! ## At the spec's model -/

/-- At the spec's model, `VotesInv` is the landed definition.

The variables:
- `P`, `n`, `t`: as in `VotesInv`, at the spec's model.

Read aloud: the spec's model has the landed `VotesInv`. -/
@[record_goldilocks]
theorem goldilocks_VotesInv (P : Provisional V) (n : NodeState V) (t : Time) :
    GoldilocksCorrectness.Proofs.Routines.VotesInv P n.A t =
      VotesInv (Model.goldilocks (V := V)) P n t := rfl

/-- At the spec's model, `KeepsVotes` is the landed definition.

The variables:
- `n`, `n'`: as in `KeepsVotes`, at the spec's model.

Read aloud: the spec's model has the landed `KeepsVotes`. -/
@[record_goldilocks]
theorem goldilocks_KeepsVotes (n n' : NodeState V) :
    GoldilocksCorrectness.Proofs.Routines.KeepsVotes n.A n'.A =
      KeepsVotes (Model.goldilocks (V := V)) n n' := rfl

/-- At the spec's model, `SlotKeyed` is the landed definition.

The variables:
- `n`: as in `SlotKeyed`, at the spec's model.

Read aloud: the spec's model has the landed `SlotKeyed`. -/
@[record_goldilocks]
theorem goldilocks_SlotKeyed (n : NodeState V) :
    GoldilocksCorrectness.Proofs.Routines.SlotKeyed n.A =
      SlotKeyed (Model.goldilocks (V := V)) n := rfl

/-- At the spec's model, `ACGrows` is the landed definition.

The variables:
- `n`, `n'`: as in `ACGrows`, at the spec's model.

Read aloud: the spec's model has the landed `ACGrows`. -/
@[record_goldilocks]
theorem goldilocks_ACGrows (n n' : NodeState V) :
    GoldilocksCorrectness.Proofs.Routines.ACGrows n.A n'.A =
      ACGrows (Model.goldilocks (V := V)) n n' := rfl

/-- At the spec's model, `ACStampsAt` is the landed definition.

The variables:
- `n`, `n'`, `τ`: as in `ACStampsAt`, at the spec's model.

Read aloud: the spec's model has the landed `ACStampsAt`. -/
@[record_goldilocks]
theorem goldilocks_ACStampsAt (n n' : NodeState V) (τ : Time) :
    GoldilocksCorrectness.Proofs.Routines.ACStampsAt n.A n'.A τ =
      ACStampsAt (Model.goldilocks (V := V)) n n' τ := rfl

end GoldilocksCorrectness.Record.Proofs.Routines
