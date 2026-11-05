module
public import GoldilocksCorrectness.Record.ModelSpellings
public import GoldilocksCorrectness.Record.ModelGoldilocks
public import GoldilocksCorrectness.Statements.Routines.ACStoreDefs

@[expose] public section

/-!
# Conditions on a node's Goldfish votes, over a model

The definitions of `GoldilocksCorrectness/Statements/Routines/ACStoreDefs.lean` over a model
`M`: conditions on the Goldfish votes a node state `n : M.N` holds, `n.votesHeld s`. At the spec's
model each is the landed definition applied to the node's AC state (the equations `goldilocks_…`, in
the simp set `record_goldilocks`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Statements.Routines

open Goldilocks
open GoldilocksCorrectness.Record

variable {V : Type} [DecidableEq V] [Fintype V]

/-- `PoolKeyed M P n`: every Goldfish vote the node state `n` holds under the slot `s` has the
slot `s` and a validator of slot `s`'s committee.

The variables:
- `M`: the model;
- `P`: the values given to the node; `n`: the node state.

Read aloud: every vote the node holds under a slot has that slot and a committee member of it as
its validator. -/
def PoolKeyed (M : GoldilocksModel V) (P : Provisional V) (n : M.N) : Prop :=
  ∀ s : Slot, ∀ vote ∈ n.votesHeld s, vote.slot = s ∧ vote.val_index ∈ P.committee s

/-- `PoolStamped M n`: every Goldfish vote the node state `n` holds has a stamp in `n`.

The variables:
- `M`: the model;
- `n`: the node state.

Read aloud: every vote the node holds is stamped. -/
def PoolStamped (M : GoldilocksModel V) (n : M.N) : Prop :=
  ∀ s : Slot, ∀ vote ∈ n.votesHeld s, n.voteStamp vote ≠ none

/-! ## At the spec's model -/

/-- At the spec's model, `PoolKeyed` is the landed definition.

The variables:
- `P`, `n`: as in `PoolKeyed`, at the spec's model.

Read aloud: the spec's model has the landed `PoolKeyed`. -/
@[record_goldilocks]
theorem goldilocks_PoolKeyed (P : Provisional V) (n : NodeState V) :
    GoldilocksCorrectness.Statements.Routines.PoolKeyed P n.A =
      PoolKeyed (Model.goldilocks (V := V)) P n := rfl

/-- At the spec's model, `PoolStamped` is the landed definition.

The variables:
- `n`: as in `PoolStamped`, at the spec's model.

Read aloud: the spec's model has the landed `PoolStamped`. -/
@[record_goldilocks]
theorem goldilocks_PoolStamped (n : NodeState V) :
    GoldilocksCorrectness.Statements.Routines.PoolStamped n.A =
      PoolStamped (Model.goldilocks (V := V)) n := rfl

end GoldilocksCorrectness.Record.Statements.Routines
