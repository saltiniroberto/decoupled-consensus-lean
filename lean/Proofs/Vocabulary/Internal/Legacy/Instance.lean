module
public import Proofs.Vocabulary.Internal.Legacy.Interface
public import Model.Vocabulary.Statements.Instantiation.Deadlines
public import Proofs.Vocabulary.Internal.Legacy.Definitions.ProposalSourcesInternal
public import Mathlib.Algebra.Order.Floor.Div
public import Proofs.Vocabulary.Internal.ModelVocabulary.Execution.Run
public import Model.Vocabulary.Protocol.Evidence
public import Model.Vocabulary.Statements.Instantiation.Certificates
public import Model.Vocabulary.Statements.Instantiation.Proposals
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Star
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
public import Proofs.Vocabulary.Internal.Legacy.Definitions.LeakLedger
public import Model.Vocabulary.Execution.Setup

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# The protocol instance of the public interface

Each field of `Interface` filled with a protocol definition.
-/

namespace DecoupledConsensusModel
namespace Statements

open DecoupledConsensusModel.Internal DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol
open Proofs.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The closed protocol instance of the public interface. -/
def «instance» (S : Setup V) : Interface V where
  confirmed := Protocol.get_confirmed
  stable := Protocol.get_stable
  finalized := fun st => st.F
  proposer := S.E.proposer
  proposalTime := Protocol.proposal_time S.E
  proposedBlock := fun rho s => proposedBlockAt S rho s
  committee := fun s => S.E.committee s
  Certificate := NamedBlock V
  finalizes := fun c T => ∃ h, NamedFinalizedAt S.E S.cfg c T h
  collisionFree := fun c c' => RootInjectiveOnAncestors c.erase c'.erase
  evidence := fun c c' =>
    HasSlashableWeightBetween S.E (chain_attestations c.erase) (chain_attestations c'.erase)
  slashable := fun st st' =>
    HasSlashableWeightBetween S.E (store_attestations st) (store_attestations st')
  inRun := fun rho c => RunBlock S rho c

end Statements
end DecoupledConsensusModel

end
