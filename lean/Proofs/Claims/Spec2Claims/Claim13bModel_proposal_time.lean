module
public import Model.Vocabulary.Protocol.Schedule
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# Facts about `Protocol.proposal_time`

A slot's proposal instant, against the slot's start `slotStart`.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Env.t
  DecoupledConsensusModel.Protocol.proposal_time DecoupledConsensusModel.slotStart

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The start of slot `s` is slot `s`'s proposal instant. -/
theorem slotStart_eq_proposal_time (E : Env V) (s : Slot) :
    slotStart E.Δ s = Protocol.proposal_time E s := rfl

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The proposal instant of slot `0` is `0`. -/
theorem proposal_time_zero (E : Env V) : Protocol.proposal_time E 0 = 0 := by
  unfold Protocol.proposal_time Env.t slotStart
  simp

/-- The proposal instant of every slot is at least `0`. -/
theorem zero_le_proposal_time (E : Env V) (s : Slot) : 0 ≤ Protocol.proposal_time E s := by
  have hΔ : (0 : Int) ≤ 4 * E.Δ := by
    have h : (0 : Int) < E.Δ := E.Δ_pos
    omega
  unfold Protocol.proposal_time Env.t slotStart
  exact Int.mul_nonneg hΔ (Int.natCast_nonneg s)

end DecoupledConsensusModel.Sts
