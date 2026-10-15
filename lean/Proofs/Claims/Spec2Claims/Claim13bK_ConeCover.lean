import Proofs.Claims.Spec2Claims.Claim13bStepCone
import Proofs.Claims.Spec2Claims.Claim13bModel_weightOf
import Proofs.Claims.Spec2Claims.Claim13bModel_Env_slotOf

/-!
# A validator awake for a whole delay

`HonestAwakeCover S Sched t` says some validator is awake throughout `[t, t + Δ]` and not held by
the adversary at its end. The file gives it inside the phase, together with the arithmetic on the
vote window and slot starts it uses.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Arithmetic -/

/-- Five delays are at most the vote window `wVote S`. -/
theorem five_delta_le_wVote (S : Setup V) : 5 * S.E.Δ ≤ wVote S := by
  have hd := S.E.Δ_pos
  have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
  have hprod : 12 * S.E.Δ ≤ 4 * (S.hc.R : Int) * S.E.Δ := by nlinarith
  have hexp : wVote S = 4 * (S.hc.R : Int) * S.E.Δ + 2 * S.E.Δ := by
    simp only [wVote]; ring
  rw [hexp]
  linarith

/-- For `t ≥ 0`, the slot after the slot of `t` starts strictly after `t` and at most four delays
    after it. -/
theorem slotStart_succ_slotOf_bounds (S : Setup V) {t : Int} (ht : 0 ≤ t) :
    t < slotStart S.E.Δ (S.E.slotOf t + 1) ∧
      slotStart S.E.Δ (S.E.slotOf t + 1) ≤ t + 4 * S.E.Δ :=
  slotStart_slotOf_succ_bounds S.E ht

/-! ## A validator awake for a whole delay -/

/-- Some validator is awake at every instant of `[t, t + Δ]` and is not held by the adversary at
    `t + Δ`. -/
def HonestAwakeCover (S : Setup V) (Sched : Schedule V) (t : Int) : Prop :=
  ∃ v : V, v ∈ Sched.awakeThroughout t (t + S.E.Δ) ∧ v ∉ Sched.adv (t + S.E.Δ)

/-- If the adversary at `t` holds less than a third of the total weight, some validator is not held
    by it at `t`. -/
theorem exists_nonAdv_of_third (S : Setup V) (Sched : Schedule V) {t : Int}
    (h : 3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight) :
    ∃ v : V, v ∉ Sched.adv t := by
  by_contra hex
  have hall : ∀ v : V, v ∈ Sched.adv t := fun v => by
    by_contra hv
    exact hex ⟨v, hv⟩
  have huniv : Sched.adv t = Finset.univ := Finset.eq_univ_of_forall hall
  have hw : S.E.electorate.weightOf (Sched.adv t) = S.E.electorate.totalWeight := by
    rw [huniv]; exact weightOf_univ S.E.electorate
  omega

/-- Under monotone corruption, if the adversary at `t + Δ` holds less than a third of the total
    weight, every validator the adversary does not hold at an instant of `[tGAT, tE]` is awake then,
    and `[t, t + Δ]` lies inside `[tGAT, tE]`, then `HonestAwakeCover S Sched t` holds. -/
theorem honestAwakeCover_of_phase (S : Setup V) (Sched : Schedule V)
    (hmono : Sched.MonotoneCorruption) {tGAT tE t : Int}
    (hthird : 3 * S.E.electorate.weightOf (Sched.adv (t + S.E.Δ))
      < S.E.electorate.totalWeight)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (ht : tGAT ≤ t) (htE : t + S.E.Δ ≤ tE) :
    HonestAwakeCover S Sched t := by
  obtain ⟨v, hv⟩ := exists_nonAdv_of_third S Sched hthird
  refine ⟨v, mem_awakeThroughout_of_forall Sched (fun t' h0 h1 => ?_), hv⟩
  exact hawake t' (le_trans ht h0) (le_trans h1 htE) v
    (fun hm => hv (hmono t' (t + S.E.Δ) h1 hm))

end DecoupledConsensusModel.Sts
