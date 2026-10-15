module
public import Proofs.Vocabulary.Internal.Definitions.TickReads
public import Proofs.Vocabulary.Protocol.Grades.LegacyVocabulary

@[expose] public section

/-!
# Proposal source store

The store from which an honest proposer computes its block.
-/

namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The store from which the slot-`s` proposer computes its block: its store before slot `s`'s
    proposal time, after the clock tick. -/
def proposerDutyStore (S : Setup V) (rho : Run V) (s : Slot) : Protocol.Store V :=
  Proofs.Optimistic.tickStore S
    (rho.storeBeforeTime S (S.E.proposer s) (Protocol.proposal_time S.E s)).core
    (Protocol.proposal_time S.E s)


end Protocol
end DecoupledConsensusModel

end
