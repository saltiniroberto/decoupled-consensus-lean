import Proofs.Vocabulary.ModelVocabulary.Healing.Schedule
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Conditions.Vocabulary_ModelVocabulary_Healing_Schedule
import Model.Record.Wiring

/-!
# The healing schedule

Theorems over a model `M : Record.Model V` and its facts `facts : Record.Facts M`: `Γ_0` of a round
is its opening slot's proposal time, and a round's action time is its opening slot's confirmation
time and the support cutoff of the next slot.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Protocol

/-- `Γ_0` of round `r` is the proposal time of round `r`'s opening slot. -/
theorem Vocabulary.Protocol.Γ_0_eq_proposal_time (facts : Record.Facts M) (hc : HealConfig) (E : Env V) (r : Round) :
    Restated.Vocabulary.Protocol.HealConfig.Γ_0 M hc E.Δ r = M.proposal_time E ((M.opening_slot hc r)) :=
  facts.sch.Γ_0_eq_proposal_time hc E r

end

section
open DecoupledConsensusModel.Protocol

/-- Round `r`'s action time `M.a hc E.Δ r` is the confirmation time of round `r`'s opening slot. -/
theorem Vocabulary.Protocol.a_eq_confirmation_time (facts : Record.Facts M) (hc : HealConfig) (E : Env V) (r : Round) :
    (M.a hc E.Δ r) = M.confirmation_time E ((M.opening_slot hc r)) :=
  facts.sch.a_eq_confirmation_time hc E r

end

section
open DecoupledConsensusModel.Protocol

/-- Round `r`'s action time `M.a hc E.Δ r` is the support cutoff of the slot after round `r`'s
    opening slot. -/
theorem Vocabulary.Protocol.a_eq_support_cutoff_succ (facts : Record.Facts M) (hc : HealConfig) (E : Env V) (r : Round) :
    (M.a hc E.Δ r) = M.support_cutoff E ((M.opening_slot hc r) + 1) :=
  (facts.sch.a_eq_confirmation_time hc E r).trans
    (facts.sch.confirmation_time_eq_support_cutoff_succ E ((M.opening_slot hc r)))

end

end DecoupledConsensusModel.Sts.Restated
