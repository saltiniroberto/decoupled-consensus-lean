import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13beRoute3_85d
import Proofs.Claims.Restated.Claim13beRoute3_92
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13beRoute3_72
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13bd
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_96

/-!
# A strong window at the sharp spacing

The recurrence of strong openings gives, between two instants `gap` periods apart, a round whose
openings `o_c`, `o_{c − 1}`, `o_{c − 2}` and slots `o_c + 1`, `o_c + 2` all have proposers not held
at their confirmation instants, over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Framework.StsMultisetLog

/-- If `strongOpeningsRecurFrom` holds from `tGAT` to `tL`, `tGAT ≤ (a − 2) · period + 1` and
    `(a − 2) · period + 1 + gap · period ≤ tL`, then some round `c` with `a + 1 ≤ c` and
    `c + 2 ≤ a + gap` has the proposers of `o_c`, `o_c + 1`, `o_c + 2`, `o_{c − 1}` and `o_{c − 2}`
    each not held at its own slot's confirmation instant. -/
theorem strongWindow_sharp_f7 (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    {tGAT tL : Int} {gap : Nat}
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tL gap) {a : Round}
    (hstart : tGAT ≤ ((a : Int) - 2) * (Restated.constants M S).period + 1)
    (hend : ((a : Int) - 2) * (Restated.constants M S).period + 1 + (gap : Int) * (Restated.constants M S).period
      ≤ tL) :
    ∃ c : Round, a + 1 ≤ c ∧ c + 2 ≤ a + gap ∧
      (∀ k < 3, S.E.proposer ((M.opening_slot S.hc c) + k) ∈
        notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c) + k))) ∧
      S.E.proposer ((M.opening_slot S.hc (c - 1))) ∈
        notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc (c - 1)))) ∧
      S.E.proposer ((M.opening_slot S.hc (c - 2))) ∈
        notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc (c - 2)))) := by
  obtain ⟨s, hlo, hhi, hmp, hprevs⟩ := hrec _ hstart hend
  obtain ⟨c, rfl⟩ := hmp.1
  have hΔ : (1 : Int) ≤ S.E.Δ := S.E.Δ_pos
  have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
  have hP : (12 : Int) ≤ 4 * S.E.Δ * (S.hc.R : Int) := by nlinarith
  have hper : (Restated.constants M S).period = 4 * S.E.Δ * (S.hc.R : Int) := Restated.period_eq facts S
  have hlo' : ((a : Int) - 2) * (Restated.constants M S).period + 1 + 2 * (Restated.constants M S).period ≤
      M.proposal_time S.E ((M.opening_slot S.hc c)) := hlo
  have hhi' : M.proposal_time S.E ((M.opening_slot S.hc c)) ≤
      ((a : Int) - 2) * (Restated.constants M S).period + 1 + (gap : Int) * (Restated.constants M S).period := hhi
  rw [Restated.proposal_time_opening_eq_l85d facts, hper] at hlo' hhi'
  have hac : a + 1 ≤ c := by
    have h2 : 4 * S.E.Δ * (S.hc.R : Int) * (a : Int) < 4 * S.E.Δ * (S.hc.R : Int) * (c : Int) := by
      nlinarith
    have := lt_of_mul_lt_mul_left h2 (by linarith)
    exact_mod_cast this
  have hcg : c + 2 ≤ a + gap := by
    by_contra hne
    have h1 : (a : Int) + (gap : Int) + 1 ≤ (c : Int) + 2 := by
      have : a + gap + 1 ≤ c + 2 := nat_sharpUpper_f7 a gap c hne
      exact_mod_cast this
    nlinarith
  have hprevAt : ∀ j : Nat, 1 ≤ j → j ≤ 2 →
      S.E.proposer ((M.opening_slot S.hc (c - j))) ∈
        notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc (c - j)))) := by
    intro j hj1 hj2
    obtain ⟨hb1, hb2⟩ := nat_prevOpenings_f7 c j hj1 hj2 (le_trans (Nat.le_add_left 1 a) hac)
    have h1 : (Restated.interface M S Sched).proposalTime ((M.opening_slot S.hc c)) - 2 * (Restated.constants M S).period ≤
        (Restated.interface M S Sched).proposalTime ((M.opening_slot S.hc (c - j))) := by
      change M.proposal_time S.E ((M.opening_slot S.hc c)) - 2 * (Restated.constants M S).period ≤
        M.proposal_time S.E ((M.opening_slot S.hc (c - j)))
      rw [Restated.proposal_time_opening_eq_l85d facts, Restated.proposal_time_opening_eq_l85d facts, hper]
      nlinarith
    have h2 : (Restated.interface M S Sched).proposalTime ((M.opening_slot S.hc (c - j))) <
        (Restated.interface M S Sched).proposalTime ((M.opening_slot S.hc c)) := by
      change M.proposal_time S.E ((M.opening_slot S.hc (c - j))) <
        M.proposal_time S.E ((M.opening_slot S.hc c))
      rw [Restated.proposal_time_opening_eq_l85d facts, Restated.proposal_time_opening_eq_l85d facts]
      nlinarith
    have hh := hprevs ((M.opening_slot S.hc (c - j))) ⟨c - j, rfl⟩ h1 h2
    exact mem_notHeldAt.mpr (hh _ le_rfl)
  refine ⟨c, hac, hcg, ?_, hprevAt 1 le_rfl (by decide), hprevAt 2 (by decide) le_rfl⟩
  intro k hk
  exact mem_notHeldAt.mpr (hmp.2 k hk _ le_rfl)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Framework.StsMultisetLog

/-- If `t_GST ≤ tGAT`, `tGAT + healingLengthη S gap ≤ tL`, `strongOpeningsRecurFrom` holds from
    `tGAT` to `tL`, `deadlineRoundW S tGAT gap + 2 ≤ a` and `a + gap ≤ switchRound S tL + 1`, then
    some round `c` with `a + 1 ≤ c` and `c + 2 ≤ a + gap` has the proposers of `o_c`, `o_c + 1`,
    `o_c + 2`, `o_{c − 1}` and `o_{c − 2}` each not held at its own slot's confirmation instant. -/
theorem strongWindow_sharp_ofRound_f7 (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    {tGAT tL : Int} {gap : Nat}
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tL gap)
    (hgst : S.E.t_GST ≤ tGAT) (hlen' : tGAT + Restated.healingLengthη M S gap ≤ tL) {a : Round}
    (ha : Restated.deadlineRoundW M S tGAT gap + 2 ≤ a) (hag : a + gap ≤ Restated.switchRound M S tL + 1) :
    ∃ c : Round, a + 1 ≤ c ∧ c + 2 ≤ a + gap ∧
      (∀ k < 3, S.E.proposer ((M.opening_slot S.hc c) + k) ∈
        notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c) + k))) ∧
      S.E.proposer ((M.opening_slot S.hc (c - 1))) ∈
        notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc (c - 1)))) ∧
      S.E.proposer ((M.opening_slot S.hc (c - 2))) ∈
        notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc (c - 2)))) := by
  obtain ⟨hd2, hg2, hd1, hg1, ha2, ha1⟩ :=
    nat_sharpRounds_f7 (Restated.deadlineRoundW M S tGAT gap) a gap (Restated.switchRound M S tL) ha hag
  obtain ⟨hst, -⟩ := Restated.recurrenceWindow_fits_l92 facts S hgst hlen' hd2 hg2
  obtain ⟨-, hwi⟩ := Restated.recurrenceWindow_fits_l92 facts S hgst hlen' hd1 hg1
  have hΔ : (1 : Int) ≤ S.E.Δ := S.E.Δ_pos
  have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
  have hper : (Restated.constants M S).period = 4 * S.E.Δ * (S.hc.R : Int) := Restated.period_eq facts S
  have hper1 : (Restated.Vocabulary.Execution.Setup.a M S 1) - (Restated.Vocabulary.Execution.Setup.a M S 0) = 4 * S.E.Δ * (S.hc.R : Int) := by
    rw [Restated.action_eq_l85d facts, Restated.action_eq_l85d facts]; push_cast; ring
  rw [Restated.proposal_time_opening_eq_l85d facts] at hst hwi
  rw [hper1] at hwi
  rw [ha2] at hst
  rw [ha1] at hwi
  have hP : (12 : Int) ≤ 4 * S.E.Δ * (S.hc.R : Int) := by nlinarith
  refine Restated.strongWindow_sharp_f7 facts S Sched hrec ?_ ?_
  · rw [hper]; nlinarith
  · rw [hper]; nlinarith

end

end DecoupledConsensusModel.Sts.Restated
