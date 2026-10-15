module
public import Proofs.Vocabulary.Internal.ModelVocabulary.Execution.Run

@[expose] public section

/-!
# Tick and vote-duty stores

The store a tick hands its first duty, and the store the vote duty reads.
-/

namespace DecoupledConsensusModel
namespace Proofs.Optimistic

open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The store the tick at `t` hands its first duty: the node's store with the clock set to `t` and
    the slot to the slot of `t`. -/
def tickStore (S : Setup V) (st : Protocol.Store V) (t : Time) : Protocol.Store V :=
  { st with t := t, s := S.E.slotOf t }


/-- The store the vote duty reads at slot `s`: the tick's store at the vote time of `s`. -/
def voteStore (S : Setup V) (st : Protocol.Store V) (s : Slot) : Protocol.Store V :=
  tickStore S st (Protocol.vote_time S.E s)

/-- The core store of `w`'s vote duty at slot `s`: `voteStore` applied to `w`'s store strictly
    before the vote time. -/
def voteDutyStore (S : Setup V) (ρ : Run V) (w : V) (s : Slot) : Protocol.Store V :=
  voteStore S (ρ.storeBeforeTime S w (Protocol.vote_time S.E s)).core s

end Proofs.Optimistic
end DecoupledConsensusModel

end
