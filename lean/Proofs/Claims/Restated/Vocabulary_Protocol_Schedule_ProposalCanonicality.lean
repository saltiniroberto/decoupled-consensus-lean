import Proofs.Vocabulary.Protocol.Schedule.ProposalCanonicality
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring

/-!
# The previous action plus one delay precedes a proposal

The action time of the round before a slot's round, plus one delay, is at most the slot's proposal
time, stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Statements.Instantiation
open Internal
open Execution

/-- If slot `s` is in a positive round, the action time of the round before it plus `Δ` is at most
    slot `s`'s proposal time. -/
theorem Vocabulary.Protocol.previous_action_add_delta_le_proposal (facts : Record.Facts M)
    (S : Setup V) {s : Slot}
    (hr : 0 < (M.round_of S.hc s)) :
    (Restated.Vocabulary.Execution.Setup.a M S ((M.round_of S.hc s) - 1)) + S.E.Δ ≤
      M.proposal_time S.E s := by
  have hR : 3 ≤ S.hc.R := S.hc.R_ge_three
  have hopen : M.opening_slot S.hc ((M.round_of S.hc s) - 1) + S.hc.R ≤ s := by
    have h1 := facts.gr.opening_slot_succ_eq S.hc ((M.round_of S.hc s) - 1)
    rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hr)] at h1
    rw [← h1]
    exact facts.gr.opening_slot_round_of_le_slot S.hc s
  have hlt : M.confirmation_time S.E (M.opening_slot S.hc ((M.round_of S.hc s) - 1) + 1) <
      M.proposal_time S.E s :=
    facts.sch.confirmationTime_lt_proposalTime_of_two_le S.E
      (le_trans (Nat.add_le_add_left hR _) hopen)
  have hvf := facts.sch.view_freeze_lt_confirmation_time S.E
    (M.opening_slot S.hc ((M.round_of S.hc s) - 1) + 1)
  show M.a S.hc S.E.Δ ((M.round_of S.hc s) - 1) + S.E.Δ ≤ _
  rw [facts.sch.a_add_delta_eq_view_freeze S ((M.round_of S.hc s) - 1)]
  exact le_of_lt (hvf.trans hlt)

end

end DecoupledConsensusModel.Sts.Restated
