import Proofs.Vocabulary.Protocol.ChainState.W4FKChainFinalityWrite
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Record.Wiring

/-!
# Finality quorum covered by a child

The condition that a finality quorum of a chain state is covered by a child block's attestations,
over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Internal
open Execution
open Internal.HealingSurface
open Protocol
open Protocol (ChainState HeightConfig derive_named fold_rows
  process_attestation_with TimeoutBinding)

/-- `sigma`'s justification is `(h_j, J)`, and some quorum's members are each in `M.finalize sigma`
    or have an attestation included in `B` with finality pair `(h_j, J.root)`. -/
def Vocabulary.Proofs.HealingSurface.NamedFinalityQuorumCoveredByChild (M : Record.Model V)
    (E : Env V) (sigma : M.CS) (B : NamedBlock V)
    (h_j : Height) (J : Block V) : Prop :=
  sigma.h_j = h_j ∧ sigma.J = J ∧
    ∃ Q : Finset V, E.electorate.IsQuorum Q ∧
      ∀ i ∈ Q,
        i ∈ M.finalize sigma ∨
        ∃ a ∈ B.attestations,
          a.val_index = i ∧
          a.finality_pair = some ⟨h_j, J.root⟩

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Internal
open Execution
open Internal.HealingSurface
open Protocol
open Protocol (ChainState HeightConfig derive_named fold_rows
  process_attestation_with TimeoutBinding)

end

end DecoupledConsensusModel.Sts.Restated
