module
public import Model.Vocabulary.Protocol.Schedule
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# Facts about `Protocol.confirmation_time`

The confirmation time of a slot, in closed form.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Env.t
  DecoupledConsensusModel.Protocol.confirmation_time DecoupledConsensusModel.slotStart

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Slot `s`'s confirmation time is `4Δs + 6Δ`. -/
theorem confirmation_time_closed (E : Env V) (s : Slot) :
    Protocol.confirmation_time E s = 4 * E.Δ * (s : Int) + 6 * E.Δ := rfl

/-- The confirmation time of slot `s` is the start of slot `s` plus `6Δ`. -/
theorem slotStart_add_six_delta_eq_confirmation_time (E : Env V) (s : Slot) :
    slotStart E.Δ s + 6 * E.Δ = Protocol.confirmation_time E s := rfl

/-- Two environments with the same delay `Δ` give every slot the same confirmation time. -/
theorem confirmation_time_eq_of_delta_eq {E E' : Env V} (h : E.Δ = E'.Δ) (s : Slot) :
    Protocol.confirmation_time E s = Protocol.confirmation_time E' s := by
  unfold Protocol.confirmation_time Env.t
  rw [h]

end DecoupledConsensusModel.Sts
