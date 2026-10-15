import Proofs.Claims.Spec2Claims.Claim13bStepAnchor
import Proofs.Claims.Spec2Claims.Claim13bModel_gradeContract_inclG1
import Proofs.Claims.Spec2Claims.Claim13bModel_setClock
import Proofs.Claims.Spec2Claims.Claim13bModel_toHealing
import Proofs.Claims.Spec2Claims.Claim13bModel_update_confirmation_with_phase
import Proofs.Claims.Spec2Claims.Claim13bModel_compatible
import Proofs.Claims.Spec2Claims.Claim13bModel_setClock_inclG1
import Proofs.Claims.Spec2Claims.Claim13bModel_frameGradeRead_attest
import Proofs.Claims.Spec2Claims.Claim13bModel_fg_source_with_mk
import Proofs.Claims.Spec2Claims.Claim13bModel_get_fg_root_mk
import Proofs.Claims.Spec2Claims.Claim13bModel_currentSGVote_mk

/-!
# The finality-gadget source of a round action

The block `actionFGSourceFrom` that a validator's round action reads its height from.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The finality-gadget source that a validator's round-`r₁` action selects, computed from the node
    state `before` it holds before the round's tick. -/
def actionFGSourceFrom (S : Setup V) (before : NamedNodeState V) (r₁ : Round) :
    Option (Block V) :=
  Proofs.HealingSurface.actionFGSource (Setup.alwaysAwake S)
    (NamedActionReads.actionReadFrom (Setup.alwaysAwake S) before r₁)

end DecoupledConsensusModel.Sts
