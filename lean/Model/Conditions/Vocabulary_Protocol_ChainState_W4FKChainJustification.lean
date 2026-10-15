import Proofs.Vocabulary.Protocol.ChainState.W4FKChainJustification
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Record.Wiring

/-!
# Target quorum covered by a child

The condition that a target quorum of a chain state is covered by a child block's attestations, over
a model `M : Record.Model V`.
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

/-- Some quorum's members are each in `sigma.target_participation` or have an attestation included
    in `B` whose height pair is the vote for `sigma.h` and `sigma.T_h.root`. -/
def Vocabulary.Proofs.HealingSurface.NamedTargetQuorumCoveredByChild (M : Record.Model V)
    (E : Env V) (sigma : M.CS) (B : NamedBlock V) : Prop :=
  ∃ Q : Finset V, E.electorate.IsQuorum Q ∧
    ∀ i ∈ Q,
      i ∈ sigma.target_participation ∨
      ∃ a ∈ B.attestations,
        a.val_index = i ∧
        a.height_pair = NamedHeightPair.vote sigma.h sigma.T_h.root false

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
