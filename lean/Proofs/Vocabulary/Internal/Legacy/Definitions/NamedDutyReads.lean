module
public import Proofs.Vocabulary.Internal.Legacy.Definitions.ActionSources

@[expose] public section

/-!
# Prepared duty reads

The node states the vote, confirmation and action duties read: the strict read with the clock staged
and the cache prepared.
-/


namespace DecoupledConsensusModel.Internal.NamedRecoveryRead
open Execution Proofs.HealingSurface
variable {V : Type} [DecidableEq V] [Fintype V]

/-- The voter's prepared read at the vote time of slot `s`. -/
def voteDutyRead (S : Setup V) (rho : Run V) (v : V) (s : Slot) : NamedNodeState V :=
  NamedActionReads.confirmationReadAt S rho v (Protocol.vote_time S.E s)

/-- The confirmation duty's prepared input at the confirmation time. -/
def confirmationInputRead (S : Setup V) (rho : Run V) (v : V) (s : Slot) : NamedNodeState V :=
  NamedActionReads.confirmationReadAt S rho v (Protocol.confirmation_time S.E s)

/-- The action's prepared read after the same-tick confirmation duty. -/
def actionDutyRead (S : Setup V) (rho : Run V) (v : V) (r : Round) : NamedNodeState V :=
  actionReadAt S rho v r

end DecoupledConsensusModel.Internal.NamedRecoveryRead

end
