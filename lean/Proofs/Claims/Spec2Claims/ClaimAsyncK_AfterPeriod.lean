import Proofs.Claims.Spec2Claims.Claim13bModel_deepest_clear
import Proofs.Claims.Spec2Claims.Claim13bModel_floor_on_stable_incl
import Proofs.Claims.Spec2Claims.Claim13bModel_update_confirmation_with_incl
import Proofs.Claims.Spec2Claims.Claim13bModel_gradeBool_cs
import Proofs.Claims.Spec2Claims.Claim13bK_ProposalVotesWalk
import Proofs.Claims.Spec2Claims.Claim13bModel_gradeBool_attest
import Proofs.Claims.Spec2Claims.ClaimAsyncK_NoConflictingQuorum
import Proofs.Claims.Spec2Claims.ClaimAsyncK_StableRecord
import Proofs.Claims.Spec2Claims.Claim13bModel_readyView_find
import Proofs.Claims.Spec2Claims.Claim13bModel_Preceq
import Proofs.Claims.Spec2Claims.Claim13bModel_compatible
import Proofs.Claims.Spec2Claims.Claim13bModel_gradeView
import Proofs.Claims.Spec2Claims.Claim13bModel_setClock_incl
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.RetainedRows

/-!
# Deadlines after the asynchronous period

Facts about the deadline `deadlineOutside S b₀ b₁ t` around the asynchronous period `[b₀, b₁)`: it
is at least one delay after the send, monotone in the send's time, and at most one delay after a
send at or after both `b₁` and `t_GST`.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- A send's deadline is at least one delay after the send: `t + Δ ≤ deadlineOutside S b₀ b₁ t`. -/
theorem le_deadlineOutside (S : Setup V) (b₀ b₁ t : Int) :
    t + S.E.Δ ≤ deadlineOutside S b₀ b₁ t := by
  unfold deadlineOutside
  split_ifs
  · have := le_max_left t S.E.t_GST; linarith
  · have := le_max_left t (max b₁ S.E.t_GST); linarith

/-- When `b₀ ≤ b₁`, the deadline `deadlineOutside S b₀ b₁ t` is monotone in the send's time `t`. -/
theorem deadlineOutside_mono (S : Setup V) {b₀ b₁ : Int} (hb : b₀ ≤ b₁) {t t' : Int}
    (h : t ≤ t') : deadlineOutside S b₀ b₁ t ≤ deadlineOutside S b₀ b₁ t' := by
  unfold deadlineOutside
  have hΔ := S.E.Δ_pos
  have hm1 := max_le_max h (le_refl S.E.t_GST)
  have hm2 := max_le_max h (le_refl (max b₁ S.E.t_GST))
  have hb1 : b₁ ≤ max t' (max b₁ S.E.t_GST) :=
    le_trans (le_max_left b₁ S.E.t_GST) (le_max_right _ _)
  split_ifs with h1 h2 h2
  · linarith
  · linarith
  · exfalso; exact h1 (by linarith)
  · linarith

/-- If `t_GST ≤ t` and `b₁ ≤ t`, the deadline `deadlineOutside S b₀ b₁ t` is at most `t + Δ`. -/
theorem deadline_le_of_after (S : Setup V) {b₀ b₁ t : Int} (hgst : S.E.t_GST ≤ t)
    (hb₁ : b₁ ≤ t) : deadlineOutside S b₀ b₁ t ≤ t + S.E.Δ := by
  unfold deadlineOutside
  split_ifs
  · rw [max_eq_left hgst]
  · rw [max_eq_left (max_le hb₁ hgst)]

end DecoupledConsensusModel.Sts
