module
public import Model.Vocabulary.Execution.Run

@[expose] public section

/-!
# Action reads

The node state a round action reads.
-/
namespace DecoupledConsensusModel.Execution.NamedActionReads
open DecoupledConsensusModel.Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

/-- The node state the action of round `r` reads: the confirmation read at `a_r` with the
    confirmation duty applied, keeping the earlier record. -/
def actionReadFrom (S : Setup V) (before : NamedNodeState V) (r : Round) :
    NamedNodeState V :=
  let t := S.a r
  let n := confirmationReadFrom S before t
  let st := Protocol.NamedDuties.update_confirmation_with
    (NamedProfile.gradeContract n.cache) S.E S.hc n.st (S.E.slotOf t - 1)
  ⟨st, before.record, n.cache⟩

def actionReadAt (S : Setup V) (rho : NamedRun V) (v : V) (r : Round) :
    NamedNodeState V :=
  actionReadFrom S (NamedRun.stateBeforeTime S rho (S.a r) v) r


end DecoupledConsensusModel.Execution.NamedActionReads

end
