module
public import Mathlib.Order.Interval.Finset.Nat
public import Proofs.Claims.Spec2Claims.Claim13bModel_Slashable
public import Proofs.Claims.Spec2Claims.Claim13bModel_conflictsWithFinality
public import Proofs.Claims.Spec2Claims.Claim13bModel_e1Fields
public import Proofs.Claims.Spec2Claims.Claim13bModel_e2Fields
public import Proofs.Claims.Spec2Claims.Claim13bModel_NamedAttestation_erase
public import Proofs.Claims.Spec2Claims.Claim13bModel_HasIntersectionWeight
public import Proofs.Claims.TransferH
public import Model.Vocabulary.Statements
public import Proofs.Claims.Spec2Claims.Claim13bModel_author

@[expose] public section

/-!
# The length of the healing phase

`healingLength S gap` is the length of the healing phase, in instants.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The length of the healing phase: the startup lag `finalityStartup gap`, then the liveness
    deadline `gap * period + finalityDeadline gap`, then one more round `period`. -/
noncomputable def healingLength (S : Setup V) (gap : Nat) : Int :=
  (constants S).finalityStartup gap + (gap : Int) * (constants S).period +
    (constants S).finalityDeadline gap + (constants S).period

end DecoupledConsensusModel.Sts
