module
public import GoldilocksCorrectness.Statements.Executions.Lemma89CountDefs
public import GoldilocksCorrectness.Proofs.Executions.Lemma89
public import GoldilocksCorrectness.Proofs.Executions.Lemma89Climb
public import GoldilocksCorrectness.Proofs.Executions.Lemma89StabilityB6

@[expose] public section

/-!
# Lemma 89, part B: the climb's count and assembly

The proofs of the climb's count on the premise the recount supports, from `scratch/goldilocks_healed/probe_recount_1.lean`
:

- the anchor: every opening's window starts after the committee premise's anchor
  (`window_after_anchor`);
- the placement: a fork-choice change within one delay after a time `τ`, in an opening's window
  read up to the support cutoff of its first slot, puts the opening in the span of `k + 2` slots
  from the slot of `τ` (`fork_choice_change_in_window_span`).
-/

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff anchorCW)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slotStart_eq supportCutoff_eq voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (anchorCW_eq)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  genesis_ancestorEq ancestorEq_compatible ancestorEq_antisymm)
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn expireLocks)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-! ## The anchor -/

omit [RootOrder] in
/-- **Every opening's window starts at or after the committee premise's anchor.** With the sequence
premise `hSeq` (its first opening's slot starting at least `3k + 1` slots after `tGAT`) and a slot
`s` at or after the first opening's, `2k ≤ s` and `anchorCW S tGAT ≤ slotStart S (s − 2k + 1)`.

Why: `4Δ · s ≥ 4Δ · s_0 ≥ tGAT + 4Δ(3k + 1)`, and `4Δ(3k + 1) = 4Δ(k + 2) + 4Δ(2k − 1)`.

Read aloud: the front of `3k + 1` slots leaves `2k − 1` slots of window after the anchor's `k + 2`;
the first opening's span of the count is not needed. -/
theorem window_after_anchor (S : Setup V) (Sched : Schedule V) (rs : ℕ → ℕ)
    (m tGAT tAwakeEnd s : ℕ)
    (hSeq : HonestOpeningSeq S Sched rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hs : rs 0 * S.C.R ≤ s) :
    2 * S.C.k ≤ s ∧ anchorCW S tGAT ≤ slotStart S (s - 2 * S.C.k + 1) := by
  have hfirst := hSeq.first
  have hΔ := one_le_Δ S
  have hk := S.C.k_ge_two
  simp only [healFrontSlots, anchorCW_eq, slotStart_eq] at hfirst ⊢
  set D := 4 * Δ S with hD
  have hD1 : 0 < D := by omega
  have h31 : D * (3 * S.C.k + 1) ≤ D * (rs 0 * S.C.R) := by omega
  have hs0 : 3 * S.C.k + 1 ≤ rs 0 * S.C.R := Nat.le_of_mul_le_mul_left h31 hD1
  have h2k : 2 * S.C.k ≤ s := by omega
  refine ⟨h2k, ?_⟩
  have e1 : D * s = D * (s - 2 * S.C.k + 1) + D * (2 * S.C.k - 1) := by
    rw [← Nat.mul_add]
    congr 1
    omega
  have e2 : D * (3 * S.C.k + 1) = D * (S.C.k + 2) + D * (2 * S.C.k - 1) := by
    rw [← Nat.mul_add]
    congr 1
    omega
  have e3 : D * (rs 0 * S.C.R) ≤ D * s := Nat.mul_le_mul_left D hs
  omega

/-! ## The placement -/

omit [RootOrder] in
/-- **A fork-choice change in an opening's window lies in the span of its kind.** With `σ` the slot of
a time `τ` and a change at `t'` from `τ` to `τ + Δ`: when `t'` is at or after the vote time of
slot `s − k − 1` and before the support cutoff of slot `s` (`k + 1 ≤ s`), the slot `s` is in
`[σ, σ + k + 2)`. The landed `broken_window_in_window_span` with the window's end moved from the vote
time of slot `s` to its support cutoff: a change from the vote time to the support cutoff of slot
`s` puts `τ` in slot `s` itself.

The variables:
- `S`: the setup; `s`: the honest round opening slot; `σ`: the slot of `τ`;
- `τ`: the time the kind starts at; `t'`: the time of the change. -/
theorem fork_choice_change_in_window_span (S : Setup V) (s σ τ t' : ℕ) (hk : S.C.k + 1 ≤ s)
    (hσ : slotStart S σ ≤ τ) (hσ' : τ < slotStart S (σ + 1))
    (ht : τ ≤ t') (ht' : t' ≤ τ + Δ S)
    (hw₁ : voteTime S (s - S.C.k - 1) ≤ t') (hw₂ : t' < supportCutoff S s) :
    InSpan σ (S.C.k + 2) s := by
  by_cases hv : t' < voteTime S s
  · exact broken_window_in_window_span S s σ τ t' hk hσ hσ' ht ht' hw₁ hv
  · have hΔ := one_le_Δ S
    have e₃ := voteTime_eq S s
    have e₄ := supportCutoff_eq S s
    rw [slotStart_eq] at e₃ hσ hσ'
    have e₅ : slotStart S (s + 1) = slotStart S s + 4 * Δ S := by
      rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
    rw [slotStart_eq, slotStart_eq] at e₅
    have h₁ : 4 * Δ S * s < 4 * Δ S * (σ + 1) := by omega
    have h₂ : 4 * Δ S * σ < 4 * Δ S * (s + 1) := by omega
    have h₁' := Nat.lt_of_mul_lt_mul_left h₁
    have h₂' := Nat.lt_of_mul_lt_mul_left h₂
    have hk2 := S.C.k_ge_two
    unfold InSpan
    exact ⟨by omega, by omega⟩

end GoldilocksCorrectness.Proofs.Executions
