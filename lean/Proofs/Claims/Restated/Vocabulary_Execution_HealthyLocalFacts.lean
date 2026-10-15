import Proofs.Vocabulary.Execution.HealthyLocalFacts
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_ModelVocabulary_Healing_Schedule
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring

/-!
# Action times, slots and opening proposals

Arithmetic over a model `M : Record.Model V` and its facts `facts : Record.Facts M` about the action
time `a r` of a round `r`: the slot of `a r` names round `r`, the slot of a time in
`[a r, a r + Δ)`, the view freeze at `a r + Δ`, the monotonicity of `a`, and the distance from `a r`
to later opening proposals.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingLemmas
open Protocol (HealConfig)
open Internal
open Execution

/-- The round of the slot of round `r`'s action time is `r`. -/
theorem Vocabulary.Proofs.HealingLemmas.round_of_slotOf_a (facts : Record.Facts M) (S : Setup V) (r : Round) :
    (M.round_of S.hc (S.E.slotOf ((Restated.Vocabulary.Execution.Setup.a M S r)))) = r := by
  have hslot : S.E.slotOf ((Restated.Vocabulary.Execution.Setup.a M S r)) = (M.opening_slot S.hc r) + 1 := by
    rw [Restated.Vocabulary.Execution.Setup.a, facts.sch.a_eq_confirmation_time]
    exact facts.sch.Optimistic_slotOf_confirmation_time
      S.E ((M.opening_slot S.hc r))
  rw [hslot, facts.gr.HealingLemmas_round_of_opening_succ]

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingLemmas
open Protocol (HealConfig)
open Internal
open Execution

/-- Round `r`'s action time plus `S.E.Δ` is the view freeze of the slot after round `r`'s opening
    slot. -/
theorem Vocabulary.Proofs.HealingLemmas.a_add_delta_eq_view_freeze (facts : Record.Facts M) (S : Setup V) (r : Round) :
    (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ = M.view_freeze S.E ((M.opening_slot S.hc r) + 1) :=
  facts.sch.a_add_delta_eq_view_freeze S r

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingLemmas
open Protocol (HealConfig)
open Internal
open Execution

/-- A time `p` with `a r ≤ p < a r + S.E.Δ`, where `a r` is round `r`'s action time, is in the slot
    after round `r`'s opening slot. -/
theorem Vocabulary.Proofs.HealingLemmas.slotOf_of_between_a (facts : Record.Facts M) (S : Setup V) (r : Round) {p : Time}
    (hlo : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ p) (hhi : p < (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ) :
    S.E.slotOf p = (M.opening_slot S.hc r) + 1 := by
  refine facts.sch.slotOf_of_between' S.E _ ?_ ?_
  · rw [← Restated.Vocabulary.Protocol.a_eq_support_cutoff_succ facts]; exact hlo
  · rw [← Restated.Vocabulary.Proofs.HealingLemmas.a_add_delta_eq_view_freeze facts]; exact hhi

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingLemmas
open Protocol (HealConfig)
open Internal
open Execution

/-- For rounds `r < q`, round `r`'s action time plus `S.E.Δ` is at most the proposal time of round
    `q`'s opening slot. -/
theorem Vocabulary.Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt (facts : Record.Facts M)
    (S : Setup V) {r q : Round} (hrq : r < q) :
    (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ ≤
      M.proposal_time S.E ((M.opening_slot S.hc q)) := by
  have hslots :
      (M.opening_slot S.hc r) + 2 ≤ (M.opening_slot S.hc q) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hrq
    rw [Nat.add_assoc, facts.gr.opening_slot_add S.hc r (k + 1)]
    have h2 : 2 ≤ (k + 1) * S.hc.R :=
      le_trans S.hc.R_ge_two (Nat.le_mul_of_pos_left _ (Nat.succ_pos k))
    exact Nat.add_le_add_left h2 _
  have hlt : (Restated.Vocabulary.Execution.Setup.a M S r) < M.proposal_time S.E (M.opening_slot S.hc q) := by
    rw [Restated.Vocabulary.Execution.Setup.a, facts.sch.a_eq_confirmation_time]
    exact facts.sch.confirmationTime_lt_proposalTime_of_two_le S.E hslots
  have hx : S.E.Δ ∣ (Restated.Vocabulary.Execution.Setup.a M S r) := by
    rw [Restated.Vocabulary.Execution.Setup.a, Restated.Vocabulary.Protocol.a_eq_support_cutoff_succ facts]
    exact Int.dvd_of_emod_eq_zero (facts.sch.support_cutoff_emod_delta S _)
  have hy : S.E.Δ ∣ M.proposal_time S.E (M.opening_slot S.hc q) :=
    Int.dvd_of_emod_eq_zero (facts.sch.proposal_time_emod_delta_inclX S.E _)
  obtain ⟨x, hx⟩ := hx
  obtain ⟨y, hy⟩ := hy
  rw [hx, hy] at hlt ⊢
  have hd := S.E.Δ_pos
  have hxy : x < y := lt_of_mul_lt_mul_left hlt hd.le
  nlinarith

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingLemmas
open Protocol (HealConfig)
open Internal
open Execution

/-- The proposal time of round `r`'s opening slot plus `gap` round periods is at most the action
    time of round `r + gap`. -/
theorem Vocabulary.Proofs.HealingLemmas.openingProposal_window_le_action (facts : Record.Facts M) (S : Setup V) (r gap : Round) :
    M.proposal_time S.E ((M.opening_slot S.hc r)) +
      gap * ((Restated.Vocabulary.Execution.Setup.a M S 1) - (Restated.Vocabulary.Execution.Setup.a M S 0)) ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + gap)) := by
  have hperiod : (Restated.Vocabulary.Execution.Setup.a M S 1) - (Restated.Vocabulary.Execution.Setup.a M S 0) = 4 * S.E.Δ * (S.hc.R : Time) := by
    have h := facts.gr.a_add_rounds S 0 1
    rw [Nat.zero_add] at h
    simp only [Restated.Vocabulary.Execution.Setup.a]
    rw [h]
    push_cast
    ring
  have haction : M.proposal_time S.E ((M.opening_slot S.hc r)) ≤ (Restated.Vocabulary.Execution.Setup.a M S r) := by
    rw [Restated.Vocabulary.Execution.Setup.a, facts.sch.a_eq_confirmation_time]
    exact facts.sch.proposal_time_le_confirmation_time S.E _
  rw [hperiod]
  simp only [Restated.Vocabulary.Execution.Setup.a] at haction ⊢
  rw [facts.gr.a_add_rounds S r gap]
  push_cast
  nlinarith [S.E.Δ_pos]

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.Assembly
open Execution

/-- For `r ≤ r'`, round `r`'s action time is at most round `r'`'s. -/
theorem Vocabulary.Proofs.Assembly.a_mono (facts : Record.Facts M) (S : Setup V) {r r' : Round} (h : r ≤ r') : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (Restated.Vocabulary.Execution.Setup.a M S r') := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  simp only [Restated.Vocabulary.Execution.Setup.a]
  rw [facts.gr.a_add_rounds S r k]
  have hadd : ∀ x p : Int, 0 ≤ p → x ≤ x + p := by intro x p hp; omega
  exact hadd _ _ (Proofs.HealingLemmas.bound_nonneg S k)

end

end DecoupledConsensusModel.Sts.Restated
