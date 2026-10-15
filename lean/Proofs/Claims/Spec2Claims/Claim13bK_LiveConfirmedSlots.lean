import Proofs.Claims.Spec2Claims.Claim13bK_ConfirmedSettle
import Proofs.Claims.Spec2Claims.Claim13bInvariantActiveSinceW
import Batteries.Classes.Order
import Mathlib.AlgebraicGeometry.Gluing
import StsMultisetLog.Spec.Message
import StsMultisetLog.Spec.Schedule
import Proofs.Claims.Spec2Claims.Claim13bModel_vote_time

/-!
# The round range of a slot

Every slot at or after round `r`'s third slot lies, for some `k`, between round `(r + k)`'s third
slot and the slot after round `(r + k + 1)`'s opening slot.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- An index into an sts execution is always valid, so `get_elem_tactic` is answered by
    `True.intro`. -/
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

section AtRn

open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-! ## Slot arithmetic -/

/-- For every slot `s` at or after round `r`'s third slot there is a `k` such that `s` is at or
    after round `(r + k)`'s third slot and at or before the slot after round `(r + k + 1)`'s opening
    slot. -/
theorem exists_round_of_slot (hc : Protocol.HealConfig) (r : Round) {s : Nat}
    (hs : hc.opening_slot r + 2 ≤ s) :
    ∃ k : Nat, hc.opening_slot (r + k) + 2 ≤ s ∧ s ≤ hc.opening_slot (r + k + 1) + 1 := by
  have hR : 0 < hc.R := lt_of_lt_of_le (by decide) hc.R_ge_two
  rw [opening_slot_closed] at hs
  obtain ⟨q, ρ, hq, hρ⟩ : ∃ q ρ : Nat, s - (r * hc.R + 2) = q * hc.R + ρ ∧ ρ < hc.R :=
    ⟨_, _, (Nat.div_add_mod' (s - (r * hc.R + 2)) hc.R).symm, Nat.mod_lt _ hR⟩
  have hs2 : s = r * hc.R + 2 + (q * hc.R + ρ) := by
    rw [← hq]; exact (Nat.add_sub_of_le hs).symm
  refine ⟨q, ?_, ?_⟩
  · rw [opening_slot_closed, Nat.add_mul, hs2]
    calc r * hc.R + q * hc.R + 2 = r * hc.R + 2 + (q * hc.R + 0) := by ring
      _ ≤ r * hc.R + 2 + (q * hc.R + ρ) :=
        Nat.add_le_add_left (Nat.add_le_add_left (Nat.zero_le ρ) _) _
  · rw [opening_slot_closed, Nat.add_mul, Nat.add_mul, Nat.one_mul, hs2]
    have h1 : ρ + 1 ≤ hc.R := hρ
    calc r * hc.R + 2 + (q * hc.R + ρ) = r * hc.R + q * hc.R + (ρ + 1) + 1 := by ring
      _ ≤ r * hc.R + q * hc.R + hc.R + 1 :=
        Nat.add_le_add_right (Nat.add_le_add_left h1 _) _

end AtRn

end DecoupledConsensusModel.Sts
