import Model.Vocabulary.Protocol.Schedule
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Proofs.Claims.ModelIrreducible

/-!
# Facts about `Protocol.proposal_time`: multiples of `Δ`

A slot's proposal instant is a multiple of `Δ`, and only slot `0` is proposed at `0`.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Env.t
  DecoupledConsensusModel.Protocol.proposal_time DecoupledConsensusModel.slotStart

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- A slot's proposal instant `4Δs` is a multiple of `Δ`. -/
theorem proposal_time_emod_delta_inclX (E : Env V) (s : Slot) :
    Protocol.proposal_time E s % E.Δ = 0 := by
  have hrw : Protocol.proposal_time E s = E.Δ * (4 * (s : Int)) := by
    unfold Protocol.proposal_time Env.t slotStart
    ring
  rw [hrw]
  exact Int.mul_emod_right _ _

/-- If `s`'s proposal instant is strictly greater than `0`, then `0 < s`. -/
theorem slot_pos_of_proposal_time_pos_inclX (E : Env V) {s : Slot}
    (h : 0 < Protocol.proposal_time E s) : 0 < s := by
  rcases Nat.eq_zero_or_pos s with h0 | h0
  · subst h0
    unfold Protocol.proposal_time Env.t slotStart at h
    simp at h
  · exact h0

end DecoupledConsensusModel.Sts
