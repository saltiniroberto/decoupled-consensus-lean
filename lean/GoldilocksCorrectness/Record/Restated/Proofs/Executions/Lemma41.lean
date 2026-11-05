module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.BlockPropagation
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Proofs.Executions.BlockPropagation
public import GoldilocksCorrectness.Proofs.Routines.Schedule

@[expose] public section

/-!
# Lemma41, over a model

The theorem of `GoldilocksCorrectness/Proofs/Executions/Lemma41.lean` over a model `M` whose facts
`F` hold: Lemma 41, the slot of a live lock entry, read at the model's vote time.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (voteTime)
open GoldilocksCorrectness.Proofs.Routines (voteTime_cast)

open GoldilocksCorrectness.Proofs.Routines (t_eq_mul)

namespace GoldilocksCorrectness.Record.Proofs.Executions

open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

omit [RootOrder] in
/-- **Lemma 41, the slot of a live lock entry.** The proof; the audited statement is in
`Statements/Executions/LockProvenanceStatements.lean`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `s₀`: the slot whose vote time `C.k` slots later bounds `t`; `s`: the slot of
  the lock; `t`: the time; `e`: the lock entry.

Read aloud: a lock entry of slot `s` still live at a time from the vote time `k` slots after slot
`s₀` has `s₀ ≤ s`. -/
theorem lem41_slot_of_live_entry (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (s₀ s t : ℕ) (e : M.LE)
    (hd : e.d = S.C.t_ (s + S.C.k) + 5 * S.C.Δ)
    (hlive : (t : Int) < e.d)
    (ht : M.voteTime S.C (s₀ + S.C.k) ≤ t) :
    s₀ ≤ s := by
  -- `omega` reads facts stated at `Time`, an `abbrev` of `Int`, only once restated at `Int`
  have h1 : ((M.voteTime S.C (s₀ + S.C.k) : ℕ) : Int) =
      4 * (S.C.Δ : Int) * (s₀ : Int) + 4 * (S.C.Δ : Int) * (S.C.k : Int) + (S.C.Δ : Int) := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.voteTime_cast M.toSlotLayout F.sched U)]
    simp only [t_eq_mul]
    push_cast
    rw [Int.mul_add]
  have hd' : @Eq Int e.d
      (4 * (S.C.Δ : Int) * (s : Int) + 4 * (S.C.Δ : Int) * (S.C.k : Int) + 5 * (S.C.Δ : Int)) := by
    rw [hd]
    simp only [t_eq_mul]
    push_cast
    rw [Int.mul_add]
  have hlive' : @LT.lt Int _ (t : Int) e.d := hlive
  have hΔ : (0 : Int) < (S.C.Δ : Int) := S.C.Δ_pos
  have h2 : ((M.voteTime S.C (s₀ + S.C.k) : ℕ) : Int) ≤ (t : Int) := by exact_mod_cast ht
  by_contra hlt
  have hb : (s : Int) + 1 ≤ (s₀ : Int) := by
    have : s + 1 ≤ s₀ := by omega
    exact_mod_cast this
  have h4 : (0 : Int) ≤ 4 * (S.C.Δ : Int) := by omega
  have h5 : @LE.le Int _ (4 * (S.C.Δ : Int) * ((s : Int) + 1)) (4 * (S.C.Δ : Int) * (s₀ : Int)) :=
    Int.mul_le_mul_of_nonneg_left hb h4
  rw [Int.mul_add, Int.mul_one] at h5
  omega

end GoldilocksCorrectness.Record.Proofs.Executions

