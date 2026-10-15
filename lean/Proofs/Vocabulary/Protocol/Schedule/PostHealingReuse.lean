module
public import Proofs.Vocabulary.Protocol.Schedule.CanonicalSuffixPostGSTCore
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar

@[expose] public section

/-!
# Vote times around a round's action time

The vote times of round `r`'s opening slot and of the next slot are before `S.a r`, and the vote
time two slots after the opening slot is after it.
-/


namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]


/-- The vote time of round `r`'s opening slot is before `S.a r`. -/
theorem opening_vote_time_lt_action
    (S : Setup V) (r : Round) :
    Protocol.vote_time S.E (S.hc.opening_slot r) < S.a r := by
  unfold Setup.a Protocol.HealConfig.a Protocol.vote_time Env.t slotStart
  have hd := S.E.Δ_pos
  have h : S.E.Δ < 6 * S.E.Δ := by
    simpa using Int.mul_lt_mul_of_pos_right (show (1 : Int) < 6 by omega) hd
  exact Int.add_lt_add_left h _

/-- The vote time of the slot after round `r`'s opening slot is before `S.a r`. -/
theorem next_vote_time_lt_action
    (S : Setup V) (r : Round) :
    Protocol.vote_time S.E (S.hc.opening_slot r + 1) < S.a r := by
  unfold Setup.a Protocol.HealConfig.a Protocol.vote_time Env.t slotStart
  push_cast
  have hd := S.E.Δ_pos
  ring_nf
  have h : S.E.Δ * 5 < S.E.Δ * 6 :=
    Int.mul_lt_mul_of_pos_left (show (5 : Int) < 6 by omega) hd
  exact Int.add_lt_add_right h _

/-- `S.a r` is before the vote time two slots after round `r`'s opening slot. -/
theorem action_lt_vote_time_two_after
    (S : Setup V) (r : Round) :
    S.a r < Protocol.vote_time S.E (S.hc.opening_slot r + 2) := by
  unfold Setup.a Protocol.HealConfig.a Protocol.vote_time Env.t slotStart
  push_cast
  have hd := S.E.Δ_pos
  ring_nf
  have h : S.E.Δ * 6 < S.E.Δ * 9 :=
    Int.mul_lt_mul_of_pos_left (show (6 : Int) < 9 by omega) hd
  exact Int.add_lt_add_right h _

end Protocol
end DecoupledConsensusModel

end
