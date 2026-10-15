module
public import Proofs.Vocabulary.Internal.Legacy.Definitions.NamedHeadReads
import Proofs.Vocabulary.Execution.HealthyLocalFacts
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Slot-time inequalities between proposals and confirmations

The next slot's proposal time is before the current slot's confirmation time, and a slot's support
cutoff is before the next slot's proposal time.
-/


namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The slot-`(s + 1)` proposal time is before the slot-`s` confirmation time. -/
theorem proposal_time_succ_lt_confirmation_time
    (E : Env V) (s : Slot) :
    Protocol.proposal_time E (s + 1) < Protocol.confirmation_time E s := by
  unfold Protocol.proposal_time Protocol.confirmation_time Env.t slotStart
  push_cast
  have h46 : 4 * E.Δ < 6 * E.Δ :=
    Int.mul_lt_mul_of_pos_right (by decide : (4 : Time) < 6) E.Δ_pos
  calc
    4 * E.Δ * ((s : Time) + 1) =
        4 * E.Δ * (s : Time) + 4 * E.Δ := by ring
    _ < 4 * E.Δ * (s : Time) + 6 * E.Δ :=
      Int.add_lt_add_left h46 _

/-- The slot-`s` support cutoff is before the slot-`(s + 1)` proposal time. -/
theorem support_cutoff_lt_proposal_time_succ
    (E : Env V) (s : Slot) :
    Protocol.support_cutoff E s < Protocol.proposal_time E (s + 1) := by
  unfold Protocol.support_cutoff Protocol.proposal_time Env.t slotStart
  push_cast
  have h24 : 2 * E.Δ < 4 * E.Δ :=
    Int.mul_lt_mul_of_pos_right (by decide : (2 : Time) < 4) E.Δ_pos
  calc
    4 * E.Δ * (s : Time) + 2 * E.Δ <
        4 * E.Δ * (s : Time) + 4 * E.Δ :=
      Int.add_lt_add_left h24 _
    _ = 4 * E.Δ * ((s : Time) + 1) := by ring


#print axioms proposal_time_succ_lt_confirmation_time
#print axioms support_cutoff_lt_proposal_time_succ

end Protocol
end DecoupledConsensusModel

end
