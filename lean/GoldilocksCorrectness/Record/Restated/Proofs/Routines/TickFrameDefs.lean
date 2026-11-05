module
public import GoldilocksCorrectness.Record.ModelSpellings
public import GoldilocksCorrectness.Record.ModelGoldilocks
public import GoldilocksCorrectness.Proofs.Routines.TickFrame

@[expose] public section

/-!
# The confirmation of two node states, over a model

The definition `KeepsConfirmation` of `GoldilocksCorrectness/Proofs/Routines/TickFrame.lean` over
a model `M`, a relation between two node states `n n' : M.N`. It is on a page of its own, which
imports no facts, because the facts of the AC-store family name it. At the spec's model it is the
landed definition applied to the node states' AC states (the equation
`goldilocks_KeepsConfirmation`, in the simp set `record_goldilocks`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Record

variable {V : Type} [DecidableEq V] [Fintype V]

/-- `KeepsConfirmation M n n'`: the node state `n'` holds the lock entries, the saved
confirmations, the fast blocks and the record of the confirmed tip of `n`.

The variables:
- `M`: the model;
- `n`, `n'`: the node states.

Read aloud: `n'` has `n`'s confirmation state. -/
def KeepsConfirmation (M : GoldilocksModel V) (n n' : M.N) : Prop :=
  n'.lockEntries = n.lockEntries ∧ n'.savedConfirmation = n.savedConfirmation ∧
    n'.fastBlocks = n.fastBlocks ∧ n'.latestConfirmed = n.latestConfirmed

/-! ## At the spec's model -/

/-- At the spec's model, `KeepsConfirmation` is the landed definition.

The variables:
- `n`, `n'`: as in `KeepsConfirmation`, at the spec's model.

Read aloud: the spec's model has the landed `KeepsConfirmation`. -/
@[record_goldilocks]
theorem goldilocks_KeepsConfirmation (n n' : NodeState V) :
    GoldilocksCorrectness.Proofs.Routines.KeepsConfirmation n.A n'.A =
      KeepsConfirmation (Model.goldilocks (V := V)) n n' := rfl

end GoldilocksCorrectness.Record.Proofs.Routines
