import Model.Vocabulary.Protocol.Schedule
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Proofs.Claims.ModelIrreducible

/-!
# Facts about `Protocol.proposal_time` against later slots

A slot's proposal instant, compared with its confirmation instant and with the proposal instants of
later slots.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Env.t
  DecoupledConsensusModel.Protocol.confirmation_time DecoupledConsensusModel.Protocol.proposal_time
  DecoupledConsensusModel.slotStart

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- `proposal_time s + 6Δ = confirmation_time s`. -/
theorem proposal_time_add_six_delta (E : Env V) (s : Slot) :
    Protocol.proposal_time E s + 6 * E.Δ = Protocol.confirmation_time E s := rfl

/-- If the environments `E` and `E'` have the same delay `Δ`, then slot `s`'s proposal instant is
    the same in both. -/
theorem proposal_time_eq_of_delta_eq {E E' : Env V} (h : E.Δ = E'.Δ) (s : Slot) :
    Protocol.proposal_time E s = Protocol.proposal_time E' s := by
  unfold Protocol.proposal_time Env.t
  rw [h]

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The proposal instant of slot `s + 1` is the proposal instant of slot `s` plus `4Δ`. -/
theorem proposal_time_succ (E : Env V) (s : Slot) :
    Protocol.proposal_time E (s + 1) = Protocol.proposal_time E s + 4 * E.Δ := by
  unfold Protocol.proposal_time Env.t slotStart
  push_cast
  ring

/-- The proposal instant of slot `s + n` is the proposal instant of slot `s` plus `4Δ * n`. -/
theorem proposal_time_add (E : Env V) (s n : Slot) :
    Protocol.proposal_time E (s + n) = Protocol.proposal_time E s + 4 * E.Δ * (n : Int) := by
  unfold Protocol.proposal_time Env.t slotStart
  push_cast
  ring

end DecoupledConsensusModel.Sts
