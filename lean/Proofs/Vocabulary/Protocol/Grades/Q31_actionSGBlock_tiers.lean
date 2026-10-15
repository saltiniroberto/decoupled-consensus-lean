module
public import Proofs.Vocabulary.Internal.Definitions.PhaseGradeQueries
public import Proofs.Vocabulary.Protocol.ValidatorClient.Engine
public import Proofs.Vocabulary.ModelProperties.currentSGVote
public import Proofs.Vocabulary.ModelProperties.deepest_clear
public import Proofs.Vocabulary.ModelProperties.get_sg_vote_with
public import Proofs.Vocabulary.ModelProperties.Store_toHealing
public import Proofs.Vocabulary.ModelProperties.NamedDuties_update_confirmation_with
public import Proofs.Vocabulary.ModelProperties.update_confirmation_with
public import Proofs.Vocabulary.ModelProperties.confirmationReadFrom
import Proofs.Vocabulary.ModelVocabulary.Healing.Schedule
import Mathlib.Order.Interval.Finset.Box

@[expose] public section

/-!
# The four values of the action's SG block

The action's SG block `actionSGBlockAt` is one of the four values of `currentSGVote`: the deepest
clear block between the anchor and `live_confirmed`, the active G2 candidate, `get_fg_root`, or the
anchor.
-/


namespace DecoupledConsensusModel
namespace Proofs
namespace HealingLemmas
namespace Rows

open Internal Execution Internal.PhaseGrades Proofs.HealingSurface
variable {V : Type} [DecidableEq V] [Fintype V]

/-- A time inside slot `s`'s window lies in slot `s`. -/
private theorem q31_slotOfTime_add (Δ : Time) (hΔ : 0 < Δ) (s : Slot) (r : Time)
    (hr0 : 0 ≤ r) (hr : r < 4 * Δ) : slotOfTime Δ (4 * Δ * (s : Time) + r) = s := by
  have hne : (4 : Time) * Δ ≠ 0 := by
    have h : ∀ d : Int, 0 < d → (4 : Int) * d ≠ 0 := by intro d hd; omega
    exact h Δ hΔ
  unfold slotOfTime
  have hrw : 4 * Δ * (s : Time) + r = r + (s : Time) * (4 * Δ) := by ring
  rw [hrw, Int.add_mul_fdiv_right _ _ hne, Int.fdiv_eq_zero_of_lt hr0 hr, zero_add]
  simp

/-- The slot-`s` confirmation time lies in slot `s + 1`. -/
private theorem q31_slotOf_confirmation_time (E : Env V) (s : Slot) :
    E.slotOf (Protocol.confirmation_time E s) = s + 1 := by
  have h : ∀ d : Int, 0 < d → (0 : Int) ≤ 2 * d ∧ 2 * d < 4 * d := by intro d hd; omega
  obtain ⟨h0, h1⟩ := h E.Δ E.Δ_pos
  have hrw : Protocol.confirmation_time E s
      = 4 * E.Δ * ((s + 1 : Slot) : Time) + 2 * E.Δ := by
    unfold Protocol.confirmation_time Env.t slotStart
    push_cast
    ring
  rw [Env.slotOf, hrw]
  exact q31_slotOfTime_add E.Δ E.Δ_pos (s + 1) (2 * E.Δ) h0 h1

/-- The slot after round `r`'s opening slot lies in round `r`. -/
private theorem q31_round_of_opening_succ (hc : Protocol.HealConfig) (r : Round) :
    hc.round_of (hc.opening_slot r + 1) = r := by
  have key : ∀ R n : Nat, 2 ≤ R → (n * R + 1) / R = n := by
    intro R n hR
    have hR0 : 0 < R := by omega
    have hcomm : n * R + 1 = 1 + R * n := by ring
    rw [hcomm, Nat.add_mul_div_left _ _ hR0, Nat.div_eq_of_lt (by omega), Nat.zero_add]
  simp only [Protocol.HealConfig.round_of, Protocol.HealConfig.opening_slot]
  exact key hc.R r hc.R_ge_two

/-- The action time `S.a r` lies in round `r`. -/
private theorem q31_round_of_slotOf_a (S : Setup V) (r : Round) :
    S.hc.round_of (S.E.slotOf (S.a r)) = r := by
  have hslot : S.E.slotOf (S.a r) = S.hc.opening_slot r + 1 := by
    rw [Setup.a, Protocol.a_eq_confirmation_time]
    exact q31_slotOf_confirmation_time S.E (S.hc.opening_slot r)
  rw [hslot, q31_round_of_opening_succ]

/-- The slot of `v`'s round-`r` action read lies in round `r`. -/
private theorem q31_action_round_eq (S : Setup V) (rho : Run V) (v : V) (r : Round) :
    S.hc.round_of (actionReadAt S rho v r).st.core.s = r := by
  have h : (actionReadAt S rho v r).st.core.s = S.E.slotOf (S.a r) := by
    show (Protocol.NamedDuties.update_confirmation_with _ S.E S.hc
      (NamedActionReads.confirmationReadFrom S _ (S.a r)).st _).core.s = _
    rw [Proofs.ModelProperties.named_update_confirmation_with_core,
      Proofs.ModelProperties.update_confirmation_with_s,
      Proofs.ModelProperties.confirmationReadFrom_st_core_s]
  rw [h]
  exact q31_round_of_slotOf_a S r

theorem q31_actionsgblock_tiers (S : Setup V) (rho : Run V) :
    Internal.PhaseGrades.Q31_actionSGBlock_tiers S rho := by
  intro v r n A
  set st := n.st.core.toHealing with hst_def
  set c := n.cache with hc_def
  have hk : S.hc.round_of st.s = r := by
    rw [hst_def, Proofs.ModelProperties.toHealing_s]
    exact q31_action_round_eq S rho v r
  set grades := (NamedProfile.gradeContract c).read S.E S.hc st r with hgrades_def
  have heq : actionSGBlockAt S rho v r = Protocol.currentSGVote st grades := by
    show Protocol.get_sg_vote_with (NamedProfile.gradeContract c) S.E S.hc st
        (S.hc.round_of st.s)
        (Protocol.grade2_block_with (NamedProfile.gradeContract c) S.E S.hc st
          (S.hc.round_of st.s))
      = Protocol.currentSGVote st grades
    rw [hk]
    exact Proofs.ModelProperties.get_sg_vote_with_gradeContract_grade2 c S.E S.hc st r
  rcases hdc : Protocol.deepest_clear (some grades.anchor) st.live_confirmed grades.clear
      with _ | B
  · rcases hq2 : grades.Q2 with _ | Q
    · by_cases hraw : grades.rawG2
      · have hval : Protocol.currentSGVote st grades = Protocol.get_fg_root st.toFG :=
          Proofs.ModelProperties.currentSGVote_of_rawG2 hdc hq2 hraw
        rw [heq, hval]
        exact Or.inr (Or.inr (Or.inl ⟨hq2, hraw, rfl⟩))
      · have hval : Protocol.currentSGVote st grades = grades.anchor :=
          Proofs.ModelProperties.currentSGVote_of_not_rawG2 hdc hq2 hraw
        rw [heq, hval]
        exact Or.inr (Or.inr (Or.inr ⟨hq2, hraw, rfl⟩))
    · have hval : Protocol.currentSGVote st grades = Q :=
        Proofs.ModelProperties.currentSGVote_of_Q2 hdc hq2
      rw [heq, hval]
      exact Or.inr (Or.inl ⟨Q, hq2, rfl⟩)
  · have hval : Protocol.currentSGVote st grades = B :=
      Proofs.ModelProperties.currentSGVote_of_deepest_clear hdc
    rw [heq, hval]
    have hlive : Block.Preceq B st.live_confirmed :=
      Proofs.ModelProperties.deepest_clear_Preceq hdc
    rw [hst_def, Proofs.ModelProperties.toHealing_live_confirmed] at hlive
    exact Or.inl ⟨Proofs.ModelProperties.deepest_clear_floor_Preceq hdc, hlive,
      Proofs.ModelProperties.deepest_clear_test hdc⟩

#print axioms q31_actionsgblock_tiers

end Rows
end HealingLemmas
end Proofs
end DecoupledConsensusModel

end
