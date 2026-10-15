import Proofs.Vocabulary.Execution.FinalizedViable
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Proofs.Vocabulary.Protocol.Schedule.NamedTick
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Proofs.Vocabulary.Protocol.Handlers.Invariants2
import Proofs.Vocabulary.ModelVocabulary
import Model.Record.Wiring

/-!
# Finalized blocks are viable

A theorem over a model `M : Record.Model V` and its facts `facts : Record.Facts M`: in every world
before a time of a run, every validator's core store satisfies
`Restated.Vocabulary.Proofs.FinalizedViable`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedFinalizedViable
open Execution Protocol

/-- In every world before time `t` of `rho`, `v`'s core store satisfies
    `Restated.Vocabulary.Proofs.FinalizedViable`. -/
theorem Vocabulary.Proofs.NamedFinalizedViable.finalizedViable_stateBeforeTime (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (t : Time) (v : V) : ∀ w₁ ∈ Restated.Vocabulary.Execution.Run.stateBeforeTime M S rho t, 
    Restated.Vocabulary.Proofs.FinalizedViable M ((w₁ v)).st.core := by
  intro w₁ hw
  unfold Restated.Vocabulary.Proofs.FinalizedViable Restated.Vocabulary.Protocol.V_tree
    Record.Model.FGS.T
  rw [facts.sto.ModelProperties_toHealing_σ, facts.sto.ModelProperties_toHealing_F,
    facts.sto.ModelProperties_toHealing_h_max, facts.sto.toHealing_T,
    facts.fc.mem_viable_tree_iff]
  obtain ⟨hT, W, hW, hFW, hh⟩ := facts.hdRun.finalizedViable_stateBeforeTime S rho t v w₁ hw
  exact ⟨⟨hT, Proofs.ModelProperties.Preceq_self _⟩, W, hW, hFW, hh⟩

end

end DecoupledConsensusModel.Sts.Restated
