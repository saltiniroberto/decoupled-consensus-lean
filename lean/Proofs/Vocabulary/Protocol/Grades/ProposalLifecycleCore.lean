module
public import Proofs.Vocabulary.Protocol.Schedule.SlotInduction
public import Proofs.Vocabulary.Internal.Definitions.NamedResult23Statements
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.Walk

@[expose] public section

/-!
# Confirmation under a grade contract

The structure `GenuineConfirmationWith`: a confirmation duty under a grade contract records the
result of its walk, and that result passes the confirmation test.
-/


namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution
open Internal.NamedRecoveryRead

variable {V : Type} [DecidableEq V] [Fintype V]


/-- The slot-`s` confirmation under `contract` records `B`, and `B` is the walk's result and passes
    the confirmation test. -/
structure GenuineConfirmationWith (contract : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.Store V) (s : Slot)
    (B : Block V) : Prop where
  selected : (Protocol.update_confirmation_with contract E hc st s).live_confirmed = B
  genuine : confEligible E st s (confWalkWith contract E hc st s) = true

end Protocol
end DecoupledConsensusModel

end
