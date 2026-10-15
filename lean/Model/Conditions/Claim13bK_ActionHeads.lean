import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.RunAll
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedHeadReads
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Statements_Instantiation_Proposals
import Model.Record.Wiring

/-!
# The honest action heads of a strong window

The condition `HonestActionHeadsAtStrongWindow` on the action heads of a round, stated over a model
`M : Record.Model V`.
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
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Statements.Instantiation
open Framework.StsMultisetLog

/-- If the proposal `p` is the block `P₁`, then every validator `v` not held at round `c`'s action
    time has `head v`, its round-`c` action head, equal to `P₁`'s block. -/
def HonestActionHeadsAtStrongWindow (M : Record.Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v₀ : V) (n : Nat) (c : Round)
    (p : Option (NamedBlock V)) (head : V → Block V) : Prop :=
  ∀ P₁ : NamedBlock V, p = some P₁ →
    ∀ v ∈ notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M S c)), head v = P₁.erase

end

end DecoupledConsensusModel.Sts.Restated
