module
public import Model.Vocabulary.Protocol.Schedule
public import Proofs.Claims.ModelIrreducible
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Facts on `Protocol.vote_time`

The Goldfish vote instant of a slot.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Env.t
  DecoupledConsensusModel.Protocol.vote_time DecoupledConsensusModel.slotStart

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The Goldfish vote instant of slot `s` is the start of slot `s` plus `Δ`. -/
theorem slotStart_add_delta_eq_vote_time (E : Env V) (s : Slot) :
    slotStart E.Δ s + E.Δ = Protocol.vote_time E s := rfl

/-- Goldfish vote instants are monotone in the slot: if `s ≤ s'`, the vote instant of `s` is at most
    that of `s'`. -/
theorem vote_time_mono (E : Env V) {s s' : Slot} (h : s ≤ s') :
    Protocol.vote_time E s ≤ Protocol.vote_time E s' := by
  have hΔ : (0 : Int) ≤ E.Δ := le_of_lt E.Δ_pos
  have hs : ((s : Nat) : Int) ≤ ((s' : Nat) : Int) := by exact_mod_cast h
  unfold Protocol.vote_time Env.t slotStart
  have := Int.mul_le_mul_of_nonneg_left hs (by linarith : (0 : Int) ≤ 4 * E.Δ)
  linarith

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

end DecoupledConsensusModel.Sts
