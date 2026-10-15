import Proofs.Claims.Spec2Claims.Claim13bK_LiveConfirmedSlots
import Proofs.Claims.Spec2Claims.ClaimAsyncK_DeliveryUpTo
import Proofs.Claims.Spec2Claims.Claim13bModel_frameGradeRead_attest
import Proofs.Claims.Spec2Claims.Claim13bModel_setClock_incl
import Proofs.Claims.Spec2Claims.Claim13bModel_toHealing
import Proofs.Claims.Spec2Claims.Claim13bModel_proposal_time_inclG1
import Proofs.Claims.Spec2Claims.Claim13bModel_opening
import Proofs.Claims.Spec2Claims.Claim13bModel_compatible
import Proofs.Claims.Spec2Claims.Claim13bModel_round_of

/-!
# Slot arithmetic for an upper slot

Three facts relating a slot `sEnd` to the round of slot `sEnd − 2`.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution
variable {V : Type} [DecidableEq V] [Fintype V]

/-- An index into an sts execution is always valid, so `get_elem_tactic` is answered by
    `True.intro`. -/
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If round `ρ`'s third slot is at or before `sEnd`, then `ρ ≤ round_of (sEnd − 2)`. -/
theorem le_round_of_sub_two (hc : Protocol.HealConfig) {ρ : Nat} {sEnd : Nat}
    (h : hc.opening_slot ρ + 2 ≤ sEnd) : ρ ≤ hc.round_of (sEnd - 2) := by
  refine le_round_of_of_opening_slot_le hc ?_
  obtain ⟨P, hP⟩ : ∃ P : Nat, hc.opening_slot ρ = P := ⟨_, rfl⟩
  rw [hP] at h ⊢
  have h' : P + 2 ≤ sEnd := h
  show P ≤ sEnd - 2
  omega

/-- Slot `sEnd` is at or before the slot after the opening slot of the round after the round of
    `sEnd − 2`: `sEnd ≤ opening_slot (round_of (sEnd − 2) + 1) + 1`. -/
theorem le_opening_round_of_sub_two (hc : Protocol.HealConfig) (sEnd : Nat) :
    sEnd ≤ hc.opening_slot (hc.round_of (sEnd - 2) + 1) + 1 := by
  have h := lt_opening_slot_round_of_succ hc (sEnd - 2)
  obtain ⟨P, hP⟩ : ∃ P : Nat, hc.opening_slot (hc.round_of (sEnd - 2) + 1) = P := ⟨_, rfl⟩
  rw [hP] at h ⊢
  have h' : sEnd - 2 < P := h
  show sEnd ≤ P + 1
  omega

/-- If `0 < ρ` and `sEnd ≤ opening_slot ρ + 1`, then `round_of (sEnd − 2) < ρ`. -/
theorem round_of_sub_two_lt (hc : Protocol.HealConfig) {ρ : Nat} {sEnd : Nat} (hρ : 0 < ρ)
    (h : sEnd ≤ hc.opening_slot ρ + 1) : hc.round_of (sEnd - 2) < ρ := by
  by_contra hne
  have h1 := opening_slot_le_of_le_round_of hc (Nat.le_of_not_lt hne)
  have h2 := opening_slot_pos_of_round_pos hc hρ
  obtain ⟨P, hP⟩ : ∃ P : Nat, hc.opening_slot ρ = P := ⟨_, rfl⟩
  rw [hP] at h h1 h2
  have h1' : P ≤ sEnd - 2 := h1
  have h2' : 0 < P := h2
  have h' : sEnd ≤ P + 1 := h
  omega

end DecoupledConsensusModel.Sts
