module
public import Proofs.Claims.Spec2Claims.Claim13bGrades
public import Proofs.Claims.Spec2Claims.Claim13bModel_author
public import Proofs.Claims.Spec2Claims.Claim13bModel_compatible
public import Proofs.Claims.Spec2Claims.Claim13bModel_Preceq
public import Proofs.Claims.Spec2Claims.Claim13bModel_actionStoreAt
public import Proofs.Vocabulary.ModelProperties.NamedDuties_update_confirmation_with
public import Proofs.Vocabulary.ModelProperties.Store_toHealing
public import Proofs.Vocabulary.ModelProperties.confirmationReadFrom

@[expose] public section

/-!
# The tick step at an instant

`tickStepAt x n t` says that step `n` of the sts execution `x` is the tick of every awake validator
at the instant `t`.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The label of step `n` is the tick of every awake validator at the instant `t`. -/
def tickStepAt {S : Setup V} {Sched : Schedule V} (x : AtomicExec (protocol S) Sched)
    (n : Nat) (t : Int) : Prop :=
  ∃ t' : Nat, x.lbl n = AtomicAction.tickAllAwake t' ∧ (t' : Int) = t

end DecoupledConsensusModel.Sts
