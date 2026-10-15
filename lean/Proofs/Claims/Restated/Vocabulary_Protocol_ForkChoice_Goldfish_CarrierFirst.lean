import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring

/-!
# The second proposal after a round's action

A theorem over a model `M : Record.Model V` and its facts `facts : Record.Facts M`: a round's action
time plus `S.E.Δ` is at most the proposal time of the second slot after the round's opening slot.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Internal
open Execution
open Internal.HealingSurface

/-- Round `q`'s action time plus `S.E.Δ` is at most the proposal time of the second slot after round
    `q`'s opening slot. -/
theorem Vocabulary.Proofs.HealingSurface.action_add_delta_le_plusTwo_proposal_time (facts : Record.Facts M)
    (S : Setup V) (q : Round) :
    (Restated.Vocabulary.Execution.Setup.a M S q) + S.E.Δ ≤
      M.proposal_time S.E ((M.opening_slot S.hc q) + 2) := by
  -- the view freeze of slot `o + 1` is at or before the proposal instant of slot `o + 2`:
  -- otherwise that proposal instant would lie in slot `o + 1`
  have hvf : M.view_freeze S.E ((M.opening_slot S.hc q) + 1) ≤
      M.proposal_time S.E ((M.opening_slot S.hc q) + 2) := by
    by_contra hlt
    have hslot := facts.sch.slotOf_of_proposal_before_freeze S.E ((M.opening_slot S.hc q) + 1)
      (facts.sch.proposal_time_mono S.E (Nat.le_succ _)) (lt_of_not_ge hlt)
    rw [facts.sch.slotOf_proposal_time] at hslot
    exact Nat.succ_ne_self _ hslot
  show M.a S.hc S.E.Δ q + S.E.Δ ≤ _
  rw [facts.sch.a_add_delta_eq_view_freeze S q]
  exact hvf

end

end DecoupledConsensusModel.Sts.Restated
