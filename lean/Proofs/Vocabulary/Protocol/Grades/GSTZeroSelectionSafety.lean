module
public import Model.Vocabulary.Protocol.Schedule
import Proofs.Vocabulary.Execution.HealthyLocalFacts
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

@[expose] public section

/-!
# Monotone vote times

Vote times are monotone in the slot.
-/

namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution
open Internal.NamedRecoveryRead

variable {V : Type} [DecidableEq V] [Fintype V]


/-- Vote times are monotone in the slot. -/
theorem vote_time_mono_slots (E : Env V) {a b : Slot} (hab : a ≤ b) :
    Protocol.vote_time E a ≤ Protocol.vote_time E b := by
  unfold Protocol.vote_time
  exact Int.add_le_add_right (proposal_time_mono E hab) E.Δ


end Protocol
end DecoupledConsensusModel

end
