module
public import Model.Vocabulary.Protocol.Grades
import Proofs.Vocabulary.ModelVocabulary.Healing.Schedule
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
public import Model.Vocabulary.Execution.Objects
public import Mathlib.Data.DFinsupp.Notation
public import Mathlib.Data.Finsupp.Notation
public import Proofs.Vocabulary.Internal.Legacy.Definitions.LeakLedger

@[expose] public section

/-!
# Slot arithmetic between round openings

Arithmetic facts about the slots from the opening slot of round `q` to the opening slot of round
`q + 1`. They assume nothing about the run.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The round grid -/

/-- Consecutive round openings are separated by exactly `R` slots. -/
theorem opening_slot_succ_eq (hc : Protocol.HealConfig) (q : Round) :
    hc.opening_slot (q + 1) = hc.opening_slot q + hc.R := by
  simp [Protocol.HealConfig.opening_slot, Nat.add_mul]

/-- For a positive round `q`, with `r = q - 1` and `s = opening_slot q - 1`:
    `opening_slot r + 1 ≤ s`, `s < opening_slot (r + 1)` and `s + 1 = opening_slot q`. -/
theorem lastInteriorSlot_before_opening
    (hc : Protocol.HealConfig) {q : Round} (hq : 0 < q) :
    let r := q - 1
    let s := hc.opening_slot q - 1
    hc.opening_slot r + 1 ≤ s ∧
      s < hc.opening_slot (r + 1) ∧
      s + 1 = hc.opening_slot q := by
  dsimp only
  have hqpred : q - 1 + 1 = q :=
    Nat.sub_add_cancel (Nat.succ_le_iff.mpr hq)
  have hopen : hc.opening_slot q =
      hc.opening_slot (q - 1) + hc.R := by
    have h := opening_slot_succ_eq hc (q - 1)
    rw [hqpred] at h
    exact h
  have hslotPos : 1 ≤ hc.opening_slot q := by
    apply Nat.succ_le_iff.mpr
    unfold Protocol.HealConfig.opening_slot
    exact Nat.mul_pos hq
      (lt_of_lt_of_le Nat.zero_lt_two hc.R_ge_two)
  have hsucc :
      (hc.opening_slot q - 1) + 1 = hc.opening_slot q :=
    Nat.sub_add_cancel hslotPos
  refine ⟨?_, ?_, hsucc⟩
  · apply Nat.le_sub_of_add_le
    rw [hopen]
    simpa [Nat.add_assoc] using
      Nat.add_le_add_left hc.R_ge_two
        (hc.opening_slot (q - 1))
  · rw [hqpred]
    exact Nat.sub_lt (Nat.succ_le_iff.mp hslotPos)
      (by decide : 0 < 1)

/-- The opening slot of round `q` lies in round `q`. -/
theorem round_of_opening_slot_eq_schedule
    (hc : Protocol.HealConfig) (q : Round) :
    hc.round_of (hc.opening_slot q) = q := by
  simp only [Protocol.HealConfig.round_of, Protocol.HealConfig.opening_slot]
  have hR : 0 < hc.R := lt_of_lt_of_le Nat.zero_lt_two hc.R_ge_two
  simpa only [Nat.mul_comm] using Nat.mul_div_cancel_left q hR

/-- Every slot `k` with `opening_slot q + 1 ≤ k < opening_slot (q + 1)` lies in round `q`. -/
theorem round_of_eq_of_opening_succ_le_of_lt_next_opening
    (hc : Protocol.HealConfig) {q k : Nat}
    (hlo : hc.opening_slot q + 1 ≤ k)
    (hhi : k < hc.opening_slot (q + 1)) :
    hc.round_of k = q := by
  have hR : 0 < hc.R := lt_of_lt_of_le Nat.zero_lt_two hc.R_ge_two
  have hlow : q * hc.R ≤ k := by
    have hlo' : q * hc.R + 1 ≤ k := by
      simpa only [Protocol.HealConfig.opening_slot] using hlo
    omega
  have hhigh : k < q * hc.R + hc.R := by
    have hnext := opening_slot_succ_eq hc q
    rw [hnext] at hhi
    simpa only [Protocol.HealConfig.opening_slot] using hhi
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hlow
  have hdlt : d < hc.R := by omega
  have hrewrite : k = d + hc.R * q := by
    calc
      k = q * hc.R + d := hd
      _ = d + hc.R * q := by rw [Nat.mul_comm q hc.R, Nat.add_comm]
  simp only [Protocol.HealConfig.round_of]
  rw [hrewrite, Nat.add_mul_div_left _ _ hR, Nat.div_eq_of_lt hdlt,
    Nat.zero_add]


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
