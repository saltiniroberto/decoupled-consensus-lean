import Proofs.Claims.Spec2Claims.Claim13bRelay
import Proofs.Claims.Spec2Claims.Claim13bModel_domain_attest
import Proofs.Claims.Spec2Claims.Claim13bModel_domain
import Model.Sts.Spec2Claims.ClaimStableThroughAsyncPeriod
import Proofs.Claims.Spec2Claims.Claim13bModel_Env_q

/-!
# Awake windows, the attester window, and the deadline before the period

Small facts used around the asynchronous period `[b₀, b₁)`: membership in `Sched.awakeThroughout`,
the length of the attester window `wAttest S`, and the deadline `deadlineOutside` of a send whose
ordinary deadline is at most `b₀`.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

noncomputable section

variable {V : Type} [DecidableEq V] [Fintype V]

/-- A validator awake throughout `[a, b]` is awake at every time `t` with `a ≤ t ≤ b`. -/
theorem mem_awake_of_mem_awakeThroughout (Sched : Schedule V) {a b t : Int} {w : V}
    (h : w ∈ Sched.awakeThroughout a b) (h0 : a ≤ t) (h1 : t ≤ b) : w ∈ Sched.awake t := by
  have hle : Sched.awakeThroughout a b ≤ Sched.awake t :=
    Finset.inf_le (Finset.mem_Icc.2 ⟨h0, h1⟩)
  exact hle h

/-- If `a ≤ a'` and `b' ≤ b`, a validator awake throughout `[a, b]` is awake throughout `[a', b']`. -/
theorem awakeThroughout_sub (Sched : Schedule V) {a b a' b' : Int} {w : V}
    (ha : a ≤ a') (hb : b' ≤ b) (h : w ∈ Sched.awakeThroughout a b) :
    w ∈ Sched.awakeThroughout a' b' :=
  mem_awakeThroughout_of_forall Sched fun _ h0 h1 =>
    mem_awake_of_mem_awakeThroughout Sched h (ha.trans h0) (h1.trans hb)

/-- The attester window `wAttest S` is at least `12Δ`. -/
theorem twelve_delta_le_wAttest_kit (S : Setup V) : 12 * S.E.Δ ≤ wAttest S := by
  have hΔ : (0 : Int) < S.E.Δ := S.E.Δ_pos
  have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
  unfold wAttest
  nlinarith

/-! ## Delivery before the period -/

/-- If `max t S.E.t_GST + Δ ≤ b₀`, the deadline `deadlineOutside S b₀ b₁ t` is the ordinary one,
    `max t S.E.t_GST + Δ`. -/
theorem deadlineOutside_of_le (S : Setup V) {b₀ b₁ t : Int}
    (h : max t S.E.t_GST + S.E.Δ ≤ b₀) :
    deadlineOutside S b₀ b₁ t = max t S.E.t_GST + S.E.Δ := by
  unfold deadlineOutside
  rw [if_pos h]

end

end DecoupledConsensusModel.Sts
