import Proofs.Claims.Spec2Claims.Claim13bStepKitConfirm
import Proofs.Claims.Spec2Claims.Claim13bModel_gradeBool_against
import Proofs.Claims.Spec2Claims.Claim13bModel_early_mk
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedDuties_attest_with
import Proofs.Claims.Spec2Claims.Claim13bModel_gradeContract
import Proofs.Claims.Spec2Claims.Claim13bModel_update_confirmation_with_phase
import Proofs.Claims.Spec2Claims.Claim13bModel_confirmationReadFrom
import Proofs.Claims.Spec2Claims.Claim13bModel_setClock
import Proofs.Claims.Spec2Claims.Claim13bModel_toHealing
import Proofs.Claims.Spec2Claims.Claim13bModel_activePrefix
import Proofs.Claims.Spec2Claims.Claim13bModel_get_fg_root_mk
import Proofs.Claims.Spec2Claims.Claim13bModel_anchor_mk
import Proofs.Claims.Spec2Claims.Claim13bModel_grade2Block_mk
import Proofs.Claims.Spec2Claims.Claim13bModel_currentSGVote_mk

/-!
# The store of a round action, and the active prefix

The healing store `actionHealingStore` that a validator's round action reads, and the fact that the
active prefix of a root is an ancestor of that root.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The healing store that a validator's round-`r₁` action reads, computed from the node state
    `before` it holds before the round's tick. -/
def actionHealingStore (S : Setup V) (before : NamedNodeState V) (r₁ : Round) :
    Protocol.HealingStore V :=
  (NamedActionReads.actionReadFrom (Setup.alwaysAwake S) before r₁).st.core.toHealing

omit [Fintype V] in
/-- The active prefix of `root` in `tree`, when it exists, is an ancestor of `root`. -/
theorem activePrefix_preceq {tree : Finset (Block V)} {root B : Block V}
    (h : Protocol.activePrefix tree root = some B) : Block.preceq B root = true := by
  exact preceq_eq_true_iff_Preceq.mpr (preceq_of_activePrefix_eq_some h)

end DecoupledConsensusModel.Sts
