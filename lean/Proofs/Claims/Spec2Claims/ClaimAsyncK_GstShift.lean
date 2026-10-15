import Model.Sts.Spec2Claims.ClaimStableThroughAsyncPeriod
import Proofs.Claims.Spec2Claims.Claim13beRoute3_97
import Proofs.Claims.Spec2Claims.Claim13bModel_named_transition
import Proofs.Claims.Spec2Claims.Claim13bModel_Env_committee
import Proofs.Claims.Spec2Claims.Claim13bModel_confirmation_time
import Proofs.Claims.Spec2Claims.Claim13bModel_opening
import Proofs.Claims.Spec2Claims.Claim13bModel_proposal_time_inclG1
import Proofs.Claims.Spec2Claims.Claim13bModel_vote_time
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedNode_tick_gst
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedNode_process_gst

/-!
# The setup with a new GST

Two facts about `setupWithGST`: it commutes with `Setup.alwaysAwake`, and, when `S.E.t_GST ≤ b₁`,
the deadline `deadlineOutside S b₀ b₁ t` is at most `max t b₁ + Δ`.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

noncomputable section

/-- Replacing the GST commutes with `Setup.alwaysAwake`. -/
theorem alwaysAwake_setupWithGST (S : Setup V) (g : Int) (hg : 0 ≤ g) :
    Setup.alwaysAwake (setupWithGST S g hg) = setupWithGST (Setup.alwaysAwake S) g hg := rfl

attribute [local irreducible] protocol

section
variable (S : Setup V) (g : Int) (hg : 0 ≤ g) (Sched : Schedule V)
  (x : AtomicExec (protocol S) Sched)

end

/-- When `S.E.t_GST ≤ b₁`, the deadline `deadlineOutside S b₀ b₁ t` is at most `max t b₁ + S.E.Δ`. -/
theorem deadlineOutside_le (S : Setup V) {b₀ b₁ : Int} (_hb : b₀ ≤ b₁)
    (hg : S.E.t_GST ≤ b₁) (t : Int) :
    deadlineOutside S b₀ b₁ t ≤ max t b₁ + S.E.Δ := by
  unfold deadlineOutside
  split_ifs with h
  · linarith [max_le_max (le_refl t) hg]
  · rw [max_eq_left hg]

end

end DecoupledConsensusModel.Sts
