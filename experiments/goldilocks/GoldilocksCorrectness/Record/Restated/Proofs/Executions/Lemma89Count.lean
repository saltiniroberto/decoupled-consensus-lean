module
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.Lemma89CountDefs
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89Climb
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89StabilityB6
public import GoldilocksCorrectness.Statements.Executions.Lemma89CountDefs
public import GoldilocksCorrectness.Proofs.Executions.Lemma89
public import GoldilocksCorrectness.Proofs.Executions.Lemma89Climb
public import GoldilocksCorrectness.Proofs.Executions.Lemma89StabilityB6

@[expose] public section

/-!
# Lemma89Count, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma89Count.lean`, over a model `M` whose
facts `F` hold, for an execution `x` of `protocolOf M S`: the window after the anchor, and a
fork-choice change in the window's span. The page's routine-level theorems are the facts' fields or
have their twins in phase A.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff anchorCW)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slotStart_eq supportCutoff_eq voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (anchorCW_eq)

namespace GoldilocksCorrectness.Record.Proofs.Executions

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor hMax le_hMax IsEntry VoterTreeAt JustifiedInTree AnchorAt)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (InSpan healFrontSlots)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  genesis_ancestorEq ancestorEq_compatible ancestorEq_antisymm)
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn expireLocks)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-! ## The anchor -/

omit [RootOrder] in
/-- **Every opening's window starts at or after the committee premise's anchor.** With the sequence
premise `hSeq` (its first opening's slot starting at least `3k + 1` slots after `tGAT`) and a slot
`s` at or after the first opening's, `2k ≤ s` and `anchorCW S tGAT ≤ M.slotStart S.C (s − 2k + 1)`.

Why: `4Δ · s ≥ 4Δ · s_0 ≥ tGAT + 4Δ(3k + 1)`, and `4Δ(3k + 1) = 4Δ(k + 2) + 4Δ(2k − 1)`.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: the front of `3k + 1` slots leaves `2k − 1` slots of window after the anchor's `k + 2`;
the first opening's span of the count is not needed. -/
theorem window_after_anchor (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N) (rs : ℕ → ℕ)
    (m tGAT tAwakeEnd s : ℕ)
    (hSeq : HonestOpeningSeq M S A x rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hs : rs 0 * S.C.R ≤ s) :
    2 * S.C.k ≤ s ∧ anchorCW S tGAT ≤ M.slotStart S.C (s - 2 * S.C.k + 1) := by
  have hfirst := hSeq.first
  have hΔ := one_le_Δ S
  have hk := S.C.k_ge_two
  simp only [healFrontSlots, anchorCW_eq, (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U)] at hfirst ⊢
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
/-- **A fork-choice change in an opening's window lies in the span of its kind.** With `σ` the slot
of a time `τ` and a change at `t'` from `τ` to `τ + Δ`: when `t'` is at or after the vote time of
slot `s − k − 1` and before the support cutoff of slot `s` (`k + 1 ≤ s`), the slot `s` is in
`[σ, σ + k + 2)`. The landed `broken_window_in_window_span` with the window's end moved from the
vote time of slot `s` to its support cutoff: a change from the vote time to the support cutoff of
slot `s` puts `τ` in slot `s` itself.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `s`: the honest round opening slot; `σ`: the slot of `τ`;
- `τ`: the time the kind starts at; `t'`: the time of the change.

Read aloud: a fork-choice change from the vote time of slot `s − k − 1` to before the support cutoff
of slot `s` puts `s` in the `k + 2` slots from the slot of the time the change's window starts at.
-/
theorem fork_choice_change_in_window_span (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (s σ τ t' : ℕ) (hk : S.C.k + 1 ≤ s)
    (hσ : M.slotStart S.C σ ≤ τ) (hσ' : τ < M.slotStart S.C (σ + 1))
    (ht : τ ≤ t') (ht' : t' ≤ τ + Δ S)
    (hw₁ : M.voteTime S.C (s - S.C.k - 1) ≤ t') (hw₂ : t' < M.supportCutoff S.C s) :
    InSpan σ (S.C.k + 2) s := by
  by_cases hv : t' < M.voteTime S.C s
  · exact (broken_window_in_window_span M F U) S s σ τ t' hk hσ hσ' ht ht' hw₁ hv
  · have hΔ := one_le_Δ S
    have e₃ := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s
    have e₄ := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U)] at e₃ hσ hσ'
    have e₅ : M.slotStart S.C (s + 1) = M.slotStart S.C s + 4 * Δ S := by
      rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add, Nat.mul_one]
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U)] at e₅
    have h₁ : 4 * Δ S * s < 4 * Δ S * (σ + 1) := by omega
    have h₂ : 4 * Δ S * σ < 4 * Δ S * (s + 1) := by omega
    have h₁' := Nat.lt_of_mul_lt_mul_left h₁
    have h₂' := Nat.lt_of_mul_lt_mul_left h₂
    have hk2 := S.C.k_ge_two
    unfold InSpan
    exact ⟨by omega, by omega⟩

omit [RootOrder] in
/-- **An opening whose window holds a change of a kind is in the span of that kind.** For a clock value
`τ` at most the support cutoff of slot `s` (`k + 1 ≤ s`), with the vote time of slot `s − k − 1` at
most `τ + Δ`, the slot `s` is in the `k + 2` slots from the slot `τ / (4Δ)` of `τ`.

It replaces `fork_choice_change_in_window_span` where the change is at a step: the
change's real time `t` gives `τ` at most every clock value at least `t` (so at most the support cutoff
when `t` is less than it), and `t ≤ τ + Δ`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `s`: the honest round opening slot; `τ`: the clock value the kind starts at.

Read aloud: a clock value at most the support cutoff of slot `s`, at most one delay before which the
window of slot `s` starts, has slot `s` within the `k + 2` slots from its own. -/
theorem kind_span_of_le_cutoff (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (s τ : ℕ) (hk : S.C.k + 1 ≤ s)
    (hτ : τ ≤ M.supportCutoff S.C s)
    (hv : M.voteTime S.C (s - S.C.k - 1) ≤ τ + Δ S) :
    InSpan (τ / (4 * Δ S)) (S.C.k + 2) s := by
  have hΔ := one_le_Δ S
  have e₁ := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s
  have e₂ := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s
  have e₃ := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s - S.C.k - 1)
  rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U)] at e₂ e₃
  have h4 : 0 < 4 * Δ S := by omega
  have hlo := Nat.div_mul_le_self τ (4 * Δ S)
  have hhi := Nat.lt_div_mul_add (a := τ) h4
  set σ := τ / (4 * Δ S) with hσ
  have f₁ : 4 * Δ S * (s + 1) = 4 * Δ S * s + 4 * Δ S := by ring
  have f₂ : 4 * Δ S * (σ + 1) = σ * (4 * Δ S) + 4 * Δ S := by ring
  have f₃ : 4 * Δ S * σ = σ * (4 * Δ S) := by ring
  unfold InSpan
  constructor
  · have : 4 * Δ S * σ < 4 * Δ S * (s + 1) := by omega
    have := Nat.lt_of_mul_lt_mul_left this
    omega
  · have : 4 * Δ S * (s - S.C.k - 1) < 4 * Δ S * (σ + 1) := by omega
    have := Nat.lt_of_mul_lt_mul_left this
    omega

omit [RootOrder] in
/-- **A kind's clock value with `τ + Δ` in the slots from `s − k − 1` to `s` puts `s` in the span of the kind.** For a
clock value `τ` with `τ + Δ` greater than the start of slot `s − k − 1` and less than the start of slot `s + 1`
(`k + 1 ≤ s`), the slot `s` is in the `k + 2` slots from the slot `(τ + Δ) / (4Δ)` of `τ + Δ`.

It replaces `kind_span_of_le_cutoff` in `climb_count_before` under the clock bounds: a change at a step
`j` of `w` before the support cutoff of slot `s` gives `τ + Δ` less than the start of slot `s + 1` (from the change's
real time and `w`'s clock value after it, which is less than that time plus `ΔClockAhead < Δ`), and a change at or
after the vote time of slot `s − k − 1`, before `w`'s tick to `τ + Δ`, gives `τ + Δ` greater than the start of slot
`s − k − 1` (that tick is at a real time at most `τ + Δ + ΔClockBehind < τ + 2Δ`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `s`: the honest round opening slot; `τ`: the clock value the kind starts at.

Read aloud: a clock value `τ` such that `τ + Δ` is after the start of slot `s − k − 1` and before the start of
slot `s + 1` has slot `s` within the `k + 2` slots from the slot of `τ + Δ`. -/
theorem kind_span_of_bounds (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (s τ : ℕ) (hk : S.C.k + 1 ≤ s)
    (hU : τ + Δ S < M.slotStart S.C (s + 1))
    (hL : M.slotStart S.C (s - S.C.k - 1) < τ + Δ S) :
    InSpan ((τ + Δ S) / (4 * Δ S)) (S.C.k + 2) s := by
  have hΔ := one_le_Δ S
  rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U)] at hU hL
  have h4 : 0 < 4 * Δ S := by omega
  have hlo := Nat.div_mul_le_self (τ + Δ S) (4 * Δ S)
  have hhi := Nat.lt_div_mul_add (a := τ + Δ S) h4
  set σ := (τ + Δ S) / (4 * Δ S) with hσ
  have f₂ : 4 * Δ S * (σ + 1) = σ * (4 * Δ S) + 4 * Δ S := by ring
  have f₃ : 4 * Δ S * σ = σ * (4 * Δ S) := by ring
  unfold InSpan
  constructor
  · have : 4 * Δ S * σ < 4 * Δ S * (s + 1) := by omega
    have := Nat.lt_of_mul_lt_mul_left this
    omega
  · have : 4 * Δ S * (s - S.C.k - 1) < 4 * Δ S * (σ + 1) := by omega
    have := Nat.lt_of_mul_lt_mul_left this
    omega

end GoldilocksCorrectness.Record.Proofs.Executions

