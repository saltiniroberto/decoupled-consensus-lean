import Proofs.Vocabulary.Internal.Legacy.Instance
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Statements_Instantiation_RoundTimes
import Model.Record.Wiring

/-!
# Every time is at most the action time of its round

A theorem over a model `M : Record.Model V` and its facts `facts : Record.Facts M`: every time `t`
is at most the action time of the round `roundAt` gives it.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Statements
open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel.Internal DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol
open Proofs.HealingSurface

/-- Every time `t` is at most the action time of the round `roundAt` gives `t`. -/
theorem Vocabulary.Statements.roundAt_spec (facts : Record.Facts M) (S : Setup V) (t : Time) :
    t ≤ (Restated.Vocabulary.Execution.Setup.a M S (Restated.Vocabulary.Statements.Instantiation.roundAt M S t)) := by
  have h01 : Restated.Vocabulary.Execution.Setup.a M S 1 =
      Restated.Vocabulary.Execution.Setup.a M S 0 + 4 * S.E.Δ * ((S.hc.R * 1 : Nat) : Time) := by
    simpa only [zero_add] using facts.gr.a_add_rounds S 0 1
  have action_time_formula : ∀ r : Round, Restated.Vocabulary.Execution.Setup.a M S r =
      Restated.Vocabulary.Execution.Setup.a M S 0 + (r : Time) *
        ((Restated.Vocabulary.Execution.Setup.a M S 1) - (Restated.Vocabulary.Execution.Setup.a M S 0)) := by
    intro r
    have hr : Restated.Vocabulary.Execution.Setup.a M S r =
        Restated.Vocabulary.Execution.Setup.a M S 0 + 4 * S.E.Δ * ((S.hc.R * r : Nat) : Time) := by
      simpa only [zero_add] using facts.gr.a_add_rounds S 0 r
    rw [hr, h01]
    push_cast
    ring
  have roundPeriod_time_pos :
      0 < (Restated.Vocabulary.Execution.Setup.a M S 1) - (Restated.Vocabulary.Execution.Setup.a M S 0) := by
    rw [h01]
    have hR : (0 : Int) < (S.hc.R : Int) := by
      have hR3 : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
      omega
    have hΔ : (0 : Int) < S.E.Δ := S.E.Δ_pos
    have hp : (0 : Int) < 4 * S.E.Δ * (S.hc.R : Int) := by positivity
    push_cast
    simpa using hp
  have roundPeriod_pos : 0 < Restated.Vocabulary.Statements.Instantiation.roundPeriod M S := by
    unfold Restated.Vocabulary.Statements.Instantiation.roundPeriod
    exact Int.lt_toNat.mpr (by exact_mod_cast roundPeriod_time_pos)
  by_cases h : 0 ≤ t - (Restated.Vocabulary.Execution.Setup.a M S 0)
  · let d : Nat := Int.toNat (t - (Restated.Vocabulary.Execution.Setup.a M S 0))
    let L : Nat := Restated.Vocabulary.Statements.Instantiation.roundPeriod M S
    have hd : (d : Time) = t - (Restated.Vocabulary.Execution.Setup.a M S 0) := by
      dsimp [d]
      exact Int.toNat_of_nonneg h
    have hL : 0 < L := roundPeriod_pos
    have hLtime : (L : Time) = (Restated.Vocabulary.Execution.Setup.a M S 1) - (Restated.Vocabulary.Execution.Setup.a M S 0) := by
      dsimp [L, Restated.Vocabulary.Statements.Instantiation.roundPeriod]
      exact Int.toNat_of_nonneg roundPeriod_time_pos.le
    have hceil : d ≤ L * (d ⌈/⌉ L) := by
      simpa [nsmul_eq_mul] using (le_smul_ceilDiv (α := Nat) (β := Nat) hL)
    have hceilInt : (d : Time) ≤ (L : Time) * ((d ⌈/⌉ L : Nat) : Time) := by
      exact_mod_cast hceil
    have hdiff : t - (Restated.Vocabulary.Execution.Setup.a M S 0) ≤
        (L : Time) * ((d ⌈/⌉ L : Nat) : Time) := by
      rw [← hd]
      exact hceilInt
    calc
      t = (Restated.Vocabulary.Execution.Setup.a M S 0) + (t - (Restated.Vocabulary.Execution.Setup.a M S 0)) := by ring
      _ ≤ (Restated.Vocabulary.Execution.Setup.a M S 0) + (L : Time) * ((d ⌈/⌉ L : Nat) : Time) :=
        Int.add_le_add_left hdiff _
      _ = (Restated.Vocabulary.Execution.Setup.a M S 0) + ((d ⌈/⌉ L : Nat) : Time) * ((Restated.Vocabulary.Execution.Setup.a M S 1) - (Restated.Vocabulary.Execution.Setup.a M S 0)) := by
        rw [hLtime]
        ring
      _ = (Restated.Vocabulary.Execution.Setup.a M S (Restated.Vocabulary.Statements.Instantiation.roundAt M S t)) := by
        rw [action_time_formula (Restated.Vocabulary.Statements.Instantiation.roundAt M S t)]
        rfl
  · have ht : t ≤ (Restated.Vocabulary.Execution.Setup.a M S 0) := le_of_lt (sub_neg.mp (lt_of_not_ge h))
    have hd0 : Int.toNat (t - (Restated.Vocabulary.Execution.Setup.a M S 0)) = 0 :=
      Int.toNat_eq_zero.mpr (sub_nonpos.mpr ht)
    have hq0 : Restated.Vocabulary.Statements.Instantiation.roundAt M S t = 0 := by
      simp [Restated.Vocabulary.Statements.Instantiation.roundAt,
        Restated.Vocabulary.Statements.Instantiation.nextRound, hd0]
    rw [hq0]
    exact ht

end

end DecoupledConsensusModel.Sts.Restated
