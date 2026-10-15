import Proofs.Vocabulary.Internal.Legacy.Assumptions.Weight
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Record.Wiring

/-!
# Slashable weight bound

The bound on the slashable weight that the chains of two blocks of a run can expose, over a model
`M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Execution
open Protocol

/-- For any two blocks of `ρ` read along the path `W`, the attestations of their chains, with the
    blocks' evidence erased, have no slashable weight between them. -/
def Vocabulary.Execution.SlashableBound (M : Record.Model V) (S : Setup V) (ρ : Record.Run V)
    (W : Nat → V → M.N) : Prop :=
  ∀ B₁ B₂ : NamedBlock V, Restated.Vocabulary.Execution.RunBlock M S ρ W B₁ → Restated.Vocabulary.Execution.RunBlock M S ρ W B₂ →
    ¬ M.HasSlashableWeightBetween S.E
      (M.chain_attestations B₁.erase) (M.chain_attestations B₂.erase)

end

end DecoupledConsensusModel.Sts.Restated
