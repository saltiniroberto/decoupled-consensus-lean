module
public import GoldilocksCorrectness.Proofs.Executions.BlockPropagation
public import GoldilocksCorrectness.Proofs.Routines.Schedule

@[expose] public section

/-!
# Lemma 41: the slot of a live lock entry

The proof of `lem41_slot_of_live_entry`, stated in
`GoldilocksCorrectness/Statements/Executions/LockProvenanceStatements.lean`, and of the fact that
a lock entry's deadline names its slot (`lockDeadline_injective`), which Lemma 39 reads.

The route: the vote time of slot `s₀ + C.k`, read back as an integer, is
`4 · C.Δ · (s₀ + C.k) + C.Δ` (`voteTime_cast`); the deadline of a lock of slot `s` is
`4 · C.Δ · (s + C.k) + 5 · C.Δ`; a time at or after the first and strictly before the second
forces `s₀ + C.k < s + C.k + 1`, since `C.Δ` is positive.
-/

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (voteTime)
open GoldilocksCorrectness.Proofs.Routines (voteTime_cast)

open GoldilocksCorrectness.Proofs.Routines (t_eq_mul)

namespace GoldilocksCorrectness.Proofs.Executions

open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Statements.Executions

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

omit [RootOrder] in
/-- **Lemma 41, the slot of a live lock entry.** The proof; the audited statement is in
`Statements/Executions/LockProvenanceStatements.lean`.

The variables:
- `S`: the setup; `s₀`: the slot whose vote time `C.k` slots later bounds `t`; `s`: the slot of
  the lock; `t`: the time; `e`: the lock entry. -/
theorem lem41_slot_of_live_entry (S : Setup V) (s₀ s t : ℕ) (e : LockEntry V)
    (hd : e.d = S.C.t_ (s + S.C.k) + 5 * S.C.Δ)
    (hlive : (t : Int) < e.d)
    (ht : voteTime S (s₀ + S.C.k) ≤ t) :
    s₀ ≤ s := by
  -- `omega` reads facts stated at `Time`, an `abbrev` of `Int`, only once restated at `Int`
  have h1 : ((voteTime S (s₀ + S.C.k) : ℕ) : Int) =
      4 * (S.C.Δ : Int) * (s₀ : Int) + 4 * (S.C.Δ : Int) * (S.C.k : Int) + (S.C.Δ : Int) := by
    rw [voteTime_cast]
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
  have h2 : ((voteTime S (s₀ + S.C.k) : ℕ) : Int) ≤ (t : Int) := by exact_mod_cast ht
  by_contra hlt
  have hb : (s : Int) + 1 ≤ (s₀ : Int) := by
    have : s + 1 ≤ s₀ := by omega
    exact_mod_cast this
  have h4 : (0 : Int) ≤ 4 * (S.C.Δ : Int) := by omega
  have h5 : @LE.le Int _ (4 * (S.C.Δ : Int) * ((s : Int) + 1)) (4 * (S.C.Δ : Int) * (s₀ : Int)) :=
    Int.mul_le_mul_of_nonneg_left hb h4
  rw [Int.mul_add, Int.mul_one] at h5
  omega

end GoldilocksCorrectness.Proofs.Executions
