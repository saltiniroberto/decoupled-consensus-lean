module
public import Model.Vocabulary.Execution.Run

@[expose] public section

/-!
# Proposal observers

The node state a slot's proposer reads at its proposal time, and the block its proposal duty
computes.
-/
namespace DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel DecoupledConsensusModel.Execution
variable {V : Type} [DecidableEq V] [Fintype V]

/-- The node state of slot `s`'s proposer read at the proposal time: `confirmationReadAt` at
    `proposal_time`. -/
def proposerReadAt (S : Setup V) (rho : Run V) (s : Slot) : NamedNodeState V :=
  NamedActionReads.confirmationReadAt S rho (S.E.proposer s) (Protocol.proposal_time S.E s)

/-- The block the named proposal duty computes from `proposerReadAt`, with pool and carried
    attestations; `none` when the parent's named block is not held. -/
def proposedBlockAt (S : Setup V) (rho : Run V) (s : Slot) : Option (NamedBlock V) :=
  let n := proposerReadAt S rho s
  Protocol.NamedActions.proposal_with (NamedProfile.gradeContract n.cache) .poolAndCarried
    S.E S.hc (S.node (S.E.proposer s)) n.st

end DecoupledConsensusModel.Statements.Instantiation

end
