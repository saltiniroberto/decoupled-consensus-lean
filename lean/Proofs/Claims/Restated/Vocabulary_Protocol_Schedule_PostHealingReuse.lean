import Proofs.Vocabulary.Protocol.Schedule.PostHealingReuse
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring

/-!
# Vote times around a round's action

The vote times of a round's opening slot and of the next slot are before the round's action time,
and the vote time of the slot after those is after it, stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Protocol
open Internal
open Execution

/-- The vote time of round `r`'s opening slot is strictly before round `r`'s action time. -/
theorem Vocabulary.Protocol.opening_vote_time_lt_action (facts : Record.Facts M)
    (S : Setup V) (r : Round) :
    M.vote_time S.E ((M.opening_slot S.hc r)) < (Restated.Vocabulary.Execution.Setup.a M S r) := by
  rw [Restated.Vocabulary.Execution.Setup.a, facts.sch.a_eq_confirmation_time]
  have h := facts.sch.vote_time_add_delta_le_confirmation_time S (M.opening_slot S.hc r)
  have hd := S.E.Δ_pos
  linarith

end

section
open DecoupledConsensusModel.Protocol
open Internal
open Execution

/-- The vote time of the slot after round `r`'s opening slot is strictly before round `r`'s action
    time. -/
theorem Vocabulary.Protocol.next_vote_time_lt_action (facts : Record.Facts M)
    (S : Setup V) (r : Round) :
    M.vote_time S.E ((M.opening_slot S.hc r) + 1) < (Restated.Vocabulary.Execution.Setup.a M S r) := by
  rw [Restated.Vocabulary.Execution.Setup.a, facts.sch.a_eq_confirmation_time,
    facts.sch.confirmation_time_eq_support_cutoff_succ]
  have hp : M.proposal_time S.E ((M.opening_slot S.hc r) + 1) ≤
      M.support_cutoff S.E ((M.opening_slot S.hc r) + 1) := by
    have h := facts.sch.proposal_time_slotOf_le S.E
      (le_of_lt (facts.sch.support_cutoff_pos S ((M.opening_slot S.hc r) + 1)))
    rwa [facts.sch.slotOf_support_cutoff] at h
  rcases lt_or_gt_of_ne (facts.sch.support_cutoff_ne_vote_time S.E ((M.opening_slot S.hc r) + 1))
    with h | h
  · exact absurd (facts.sch.support_cutoff_lt_vote_time_imp_lt_proposal_time S.E h) (not_lt.mpr hp)
  · exact h

end

section
open DecoupledConsensusModel.Protocol
open Internal
open Execution

/-- Round `r`'s action time is strictly before the vote time of round `r`'s opening slot plus two. -/
theorem Vocabulary.Protocol.action_lt_vote_time_two_after (facts : Record.Facts M)
    (S : Setup V) (r : Round) :
    (Restated.Vocabulary.Execution.Setup.a M S r) < M.vote_time S.E ((M.opening_slot S.hc r) + 2) := by
  rw [Restated.Vocabulary.Execution.Setup.a, facts.sch.a_eq_confirmation_time,
    facts.sch.confirmation_time_eq_support_cutoff_succ]
  exact lt_trans (facts.sch.Optimistic_support_cutoff_lt_view_freeze S.E _)
    (facts.sch.view_freeze_lt_vote_time_succ S.E ((M.opening_slot S.hc r) + 1))

end

end DecoupledConsensusModel.Sts.Restated
