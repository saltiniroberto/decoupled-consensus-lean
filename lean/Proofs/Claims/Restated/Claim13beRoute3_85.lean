import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_85

/-!
# The entry of a block's height

A theorem over a model `M : Record.Model V` and its facts naming the entry of a block's height as
one of its ancestors.
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
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs

/-- Some ancestor `E₀` of `B` erases to `B`'s entry `T_h(B)`, is at `B`'s height, and has `T_h(B)`'s
    slot. -/
theorem entry_named_l85 (facts : Record.Facts M) (E : Env V) (cfg : Protocol.HeightConfig) (B : NamedBlock V) :
    ∃ E₀ : NamedBlock V, NamedBlock.Preceq E₀ B ∧
      E₀.erase = (M.derive_named E cfg B).T_h ∧
      (M.derive_named E cfg E₀).h = (M.derive_named E cfg B).h ∧
      E₀.slot = (M.derive_named E cfg B).T_h.slot := by
  obtain ⟨E₀, h1, h2, h3⟩ := facts.cs.entry_ancestor_same_height E cfg B
  refine ⟨E₀, h1, h2, h3, ?_⟩
  rw [← h2, Proofs.NamedWire.erase_slot]

end

end DecoupledConsensusModel.Sts.Restated
