import Proofs.Vocabulary.Protocol.ChainState.EntryHeight
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Record.Wiring

/-!
# The height entry is an ancestor

A theorem over a model `M : Record.Model V` and its facts `facts : Record.Facts M`: the height entry
`T_h` of the chain state derived from a named block is an ancestor of the block's erasure.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedEntryHeight
open Protocol

/-- The height entry `T_h` of the chain state derived from `B` is an ancestor of `B`'s erasure. -/
theorem Vocabulary.Proofs.NamedEntryHeight.entry_geometry_ancestor (facts : Record.Facts M) (E : Env V) (cfg : HeightConfig) (B : NamedBlock V) :
    Block.Preceq (M.derive_named E cfg B).T_h B.erase := by
  obtain ⟨entry, hentry, he, _⟩ := facts.cs.entry_ancestor_same_height E cfg B
  rw [← he]
  exact Proofs.NamedWire.erase_preceq hentry

end

end DecoupledConsensusModel.Sts.Restated
