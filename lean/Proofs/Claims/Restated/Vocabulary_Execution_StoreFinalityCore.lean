import Proofs.Vocabulary.Execution.StoreFinalityCore
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Record.Wiring

/-!
# The finalized block is an ancestor of the FG root

A theorem over a model `M : Record.Model V` and its facts `facts : Record.Facts M`: in a store whose
finalized block is an ancestor of its justified block, the finalized block is an ancestor of the FG
root.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.StoreFinality
open Protocol (HealConfig)
open Internal

/-- If the finalized block of `st` is an ancestor of its justified block, it is an ancestor of the
    FG root of `st`'s healing store. -/
theorem Vocabulary.Proofs.StoreFinality.finalized_preceq_fgRoot (facts : Record.Facts M) {st : M.S}
    (hFJ : Block.preceq st.F st.J = true) :
    Block.Preceq st.F (M.get_fg_root (M.toHealing st).toFG) := by
  have h := facts.fc.preceq_get_fg_root_of_F (st := (M.toHealing st).toFG)
    (by rw [facts.sto.ModelProperties_toHealing_F, facts.sto.ModelProperties_toHealing_J]; exact hFJ)
  rw [facts.sto.ModelProperties_toHealing_F] at h
  unfold Block.Preceq
  exact h

end

end DecoupledConsensusModel.Sts.Restated
