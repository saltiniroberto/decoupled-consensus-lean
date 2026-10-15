import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Record.Wiring
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Objects

/-!
# Fresh deliveries

The condition `DeliveryFreshAt` that a delivered object is new to its receiver, stated over a model
`M : Record.Model V` along a path `W` of the run.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- In the world `W i`, whatever the event at index `i` delivers, its receiver has not processed it. -/
def DeliveryFreshAt (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N)
    (i : Nat) : Prop :=
  ∀ (v : V) (o : NamedObject V) (t : Time), rho.events[i]? = some (.deliver v o t) →
    Restated.Vocabulary.Execution.Object.processed M (W i v).st o = false

end

end DecoupledConsensusModel.Sts.Restated
