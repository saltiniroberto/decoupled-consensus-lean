import Proofs.Vocabulary.Protocol.Handlers.Blocks
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Conditions.Vocabulary_Protocol_Handlers_Blocks
import Model.Record.Wiring

/-!
# Block steps are reflexive and transitive

The relation `BlockStep` between stores is reflexive and transitive, stated over a model
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
open DecoupledConsensusModel.Protocol.BlockStep
open Protocol (HeightConfig)
open Protocol (HealConfig)
open Internal
open Execution

/-- `BlockStep` is reflexive. -/
theorem Vocabulary.Protocol.BlockStep.refl' (facts : Record.Facts M) (st : M.S) : Restated.Vocabulary.Protocol.BlockStep M st st :=
  fun h => ⟨⟨fun _ hB => hB, fun _ _ hc => hc⟩, h⟩

end

section
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol.BlockStep
open Protocol (HeightConfig)
open Protocol (HealConfig)
open Internal
open Execution

/-- `BlockStep` is transitive. -/
theorem Vocabulary.Protocol.BlockStep.trans' (facts : Record.Facts M) {st st' st'' : M.S} (h₁ : Restated.Vocabulary.Protocol.BlockStep M st st') (h₂ : Restated.Vocabulary.Protocol.BlockStep M st' st'') :
    Restated.Vocabulary.Protocol.BlockStep M st st'' := by
  intro hs
  obtain ⟨hc₁, hs'⟩ := h₁ hs
  obtain ⟨hc₂, hs''⟩ := h₂ hs'
  exact ⟨⟨fun B hB => hc₂.mem B (hc₁.mem B hB),
    fun B c hc => hc₂.stamp B c (hc₁.stamp B c hc)⟩, hs''⟩

end

end DecoupledConsensusModel.Sts.Restated
