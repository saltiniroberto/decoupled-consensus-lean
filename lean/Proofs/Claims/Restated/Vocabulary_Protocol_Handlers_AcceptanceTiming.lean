import Proofs.Vocabulary.Protocol.Handlers.AcceptanceTiming
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Conditions.Vocabulary_Protocol_Handlers_AcceptanceTiming
import Model.Record.Wiring

/-!
# Support cutoffs and view freezes are public times

The support cutoff and the Goldfish view freeze of a slot are public tick times, stated over a model
`M : Record.Model V`.
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

/-- The support cutoff of slot `s` is a public tick time. -/
theorem Vocabulary.Protocol.publicTime_support_cutoff (facts : Record.Facts M) (S : Setup V) (s : Slot) :
    PublicTime S (M.support_cutoff S.E s) :=
  (facts.sch.publicTime_iff S _).mpr ⟨s, Or.inr (Or.inr (Or.inl rfl))⟩

end

section
open DecoupledConsensusModel.Protocol
open Internal
open Execution

/-- The Goldfish view freeze of slot `s` is a public tick time. -/
theorem Vocabulary.Protocol.publicTime_view_freeze (facts : Record.Facts M) (S : Setup V) (s : Slot) :
    PublicTime S (M.view_freeze S.E s) :=
  (facts.sch.publicTime_iff S _).mpr ⟨s, Or.inr (Or.inr (Or.inr rfl))⟩

end

end DecoupledConsensusModel.Sts.Restated
