module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.PeriodCertificateEntry
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.PeriodBridges
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.AsyncDeliveryBoundary
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.PeriodFastSupport
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.PeriodInduction
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89CountJUpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma81
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma43
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma45
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89f
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Attestation
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Confirmation
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# PeriodEntryDeliveryLine, over a model

The kit of the delivery line `DelTLine`, over a model `M` whose
facts `F` hold, for an execution `x` of `protocolOf M S`:

1. `envFactsOutside_of_trace`: the synchrony premise at `Δ` and the catch-up premise at `Δw`, both
   suspended on `[b₀, b₁)`, give the promises `EnvFactsOutside`.
2. `delT_relay_deadline_add_le`, `delT_restart_deadline_le`: a relay by the start of the voter's duty
   window is due one delay before the view freeze, and a restart by then catches up by the view freeze.
3. `delT_of_promises`: the line from the synchrony and catch-up promises, at the voter's tick to the view
   freeze, through `mem_tree_of_admitted_delivery`.
4. `delT_of_envFactsOutside`: the line from the suspended promises.
5. `delT_of_catchUp`, `delT_of_catchUp_Δ`: the line from the synchrony premise, parents held at
   delivery, the recovery bound at the hand-over cutoff, the period's bounds, and the catch-up premise at
   a catch-up delay at most `max (Δ S) Δs` (at `Δ S` for the second).

`delT_of_catchUp` and `delT_of_catchUp_Δ` take the fields of the period's bundle they read as separate
hypotheses, since the bundle carries the line.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff viewFreeze
  dutyWindowStart)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery EnvFactsBy EnvFactsOutside
  EnvFactsUpTo EnvFactsSync)
open GoldilocksCorrectness.Record.Statements.Routines (ProgressCertOn)
open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_trans compatible_of_ancestorEq_compatible
  compatible_iff slot_mono_int)
open GoldilocksCorrectness.Statements.AbstractTrace (add_le_deadlineOutside)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **Kit fact, the relay's deadline around the period**. On the uniform schedule (slot `σ`
starting at `4 · Δ · σ`), a message on the wire at a real time `τ` at most `A + B` after the duty window's
start `D` of slot `σ + 1` (`D + 4 · Δ · k = 4 · Δ · σ + 5 · Δ`, or `D = 0` when that start is negative), with the
period's bounds `hb₀`, `hb`, `hb₁` and the recovery bound `hGST` after the hand-over slot `s`, `s + 1 ≤ σ`,
has its suspended deadline at a delay `Δn ≤ Δ` at least one delay before the view freeze of slot `σ`,
`4 · Δ · σ + 3 · Δ`. `m` is `max Δ Δs`.

Why: in the synchronous case the deadline is `max τ GST + Δn`, at most `D + Δ` or `GST + Δ`, and `k ≥ 2`
(from `hΔs`); in the other case `τ + Δn` is after `b₀ ≥ supportCutoff (s + 1)`, which puts slot `σ` at
least `k` slots after `s` (`hSkew`: the two clock bounds together are less than one delay), and `hb₁` puts
`b₁ + m` at most the vote time of slot `s + k`.

The variables:
- `Δ`, `Δn`: the delay and the delay of the promise; `k`: the slow window; `s`: the hand-over slot; `σ`: the
  slot before the vote; `GST`, `b₀`, `b₁`: the promise's times; `m`: `max Δ Δs`; `A`, `B`: the clock bounds;
  `τ`: the relay's real time; `D`: the duty window's start of slot `σ + 1`.

Read aloud: a relay by the two clock bounds after the start of the voter's duty window is due a delay before
the view freeze. -/
theorem delT_relay_deadline_add_le {Δ Δn k s σ GST b₀ b₁ : ℕ} {m A B τ D : ℝ}
    (hΔ : 1 ≤ Δ) (hΔn : Δn ≤ Δ) (hmΔ : (Δ : ℝ) ≤ m) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hSkew : A + B < Δ)
    (hΔs : m + 3 * Δ + A + B < 4 * Δ * k)
    (hGST : (GST : ℝ) + m ≤ 4 * Δ * s + 6 * Δ)
    (hb₀ : 4 * (Δ : ℝ) * s + 6 * Δ ≤ b₀) (hb : (b₀ : ℝ) ≤ b₁)
    (hb₁ : (b₁ : ℝ) + m ≤ 4 * Δ * s + 4 * Δ * k + Δ)
    (hs : (s : ℝ) + 1 ≤ σ)
    (hD : D + 4 * Δ * k = 4 * Δ * σ + 5 * Δ ∨ (D = 0 ∧ 4 * (Δ : ℝ) * σ + 5 * Δ < 4 * Δ * k))
    (hτ : τ ≤ D + A + B) :
    GoldilocksCorrectness.Statements.AbstractTrace.deadlineOutsideR Δn GST b₀ b₁ τ + Δ ≤
      4 * Δ * σ + 3 * Δ := by
  have hΔr : (1 : ℝ) ≤ Δ := by exact_mod_cast hΔ
  have hΔnr : (Δn : ℝ) ≤ Δ := by exact_mod_cast hΔn
  have hΔ0 : (0 : ℝ) ≤ 4 * Δ := by positivity
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have hσ0 : (0 : ℝ) ≤ σ := Nat.cast_nonneg σ
  have hk2 : (2 : ℝ) ≤ k := by
    by_contra h
    push_neg at h
    have hk1 : (k : ℝ) ≤ 1 := by
      have : k < 2 := by exact_mod_cast h
      exact_mod_cast Nat.lt_succ_iff.1 this
    have : 4 * (Δ : ℝ) * k ≤ 4 * Δ * 1 := mul_le_mul_of_nonneg_left hk1 hΔ0
    linarith
  have htk : 4 * (Δ : ℝ) * 2 ≤ 4 * Δ * k := mul_le_mul_of_nonneg_left hk2 hΔ0
  have hts : 4 * (Δ : ℝ) * (s + 1) ≤ 4 * Δ * σ := mul_le_mul_of_nonneg_left hs hΔ0
  have hsσ : 0 ≤ 4 * (Δ : ℝ) * s := mul_nonneg hΔ0 hs0
  have hσσ : 0 ≤ 4 * (Δ : ℝ) * σ := mul_nonneg hΔ0 hσ0
  have hGSTΔ : (GST : ℝ) + Δ ≤ b₀ := by linarith
  unfold GoldilocksCorrectness.Statements.AbstractTrace.deadlineOutsideR
  split_ifs with h
  · rcases le_total τ GST with hτG | hτG
    · rw [max_eq_right hτG]; linarith
    · rw [max_eq_left hτG]
      rcases hD with hD | ⟨hD0, -⟩
      · linarith
      · rw [hD0] at hτ; linarith
  · push_neg at h
    have hτG : (GST : ℝ) < τ := by
      by_contra h'
      push_neg at h'
      rw [max_eq_right h'] at h
      linarith
    rw [max_eq_left hτG.le] at h
    rcases hD with hD | ⟨hD0, -⟩
    swap
    · rw [hD0] at hτ; linarith
    -- slot `σ` is at least `k` slots after `s` (with the slack, no longer more than `k`)
    have hskR : (s : ℝ) + k ≤ σ := by
      by_contra hc
      push_neg at hc
      have hlt : σ + 1 ≤ s + k := by
        have : (σ : ℝ) < s + k := hc
        have h' : σ < s + k := by exact_mod_cast this
        omega
      have hltR : (σ : ℝ) + 1 ≤ s + k := by exact_mod_cast hlt
      have : 4 * (Δ : ℝ) * (σ + 1) ≤ 4 * Δ * (s + k) := mul_le_mul_of_nonneg_left hltR hΔ0
      linarith
    have htsk : 4 * (Δ : ℝ) * (s + k) ≤ 4 * Δ * σ := mul_le_mul_of_nonneg_left hskR hΔ0
    have hGb : (GST : ℝ) ≤ b₁ := by linarith
    rw [max_eq_left hGb]
    rcases le_total τ b₁ with hτb | hτb
    · rw [max_eq_right hτb]; linarith
    · rw [max_eq_left hτb]; linarith

/-- **Kit fact, a restart's catch-up deadline before the view freeze**. On the uniform
schedule, a restart at a real time `ρ` at most `ΔClockBehind` after the duty window's start `D` of slot
`σ + 1` (`D + 4 · Δ · k = 4 · Δ · σ + 5 · Δ`), with a catch-up delay `Δw ≤ m = max Δ Δs`, the recovery bound
`hGST` and the votes of slot `σ` not owed inside the period (`hOwed`), has its suspended catch-up deadline
at most the view freeze of slot `σ`, `4 · Δ · σ + 3 · Δ`.

Why: `ρ + Δw` and `GST + Δw` are at most the support cutoff of slot `σ` (`hΔs`, `hGST`), so in the
synchronous case the deadline is at most that cutoff; in the other case `b₀` is before that cutoff, and
`hOwed` gives `b₁ + m` at most the view freeze.

The variables:
- `Δ`, `Δw`: the delay and the catch-up delay; `k`: the slow window; `s`: the hand-over slot; `σ`: the slot
  before the vote; `GST`, `b₀`, `b₁`: the promise's times; `m`: `max Δ Δs`; `A`, `B`: the clock bounds; `ρ`:
  the restart's real time; `D`: the duty window's start of slot `σ + 1`.

Read aloud: a restart by the start of the voter's duty window catches up by the view freeze. -/
theorem delT_restart_deadline_le {Δ Δw k s σ GST b₀ b₁ : ℕ} {m A B ρ D : ℝ}
    (hmΔ : (Δ : ℝ) ≤ m) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hΔs : m + 3 * Δ + A + B < 4 * Δ * k)
    (hGST : (GST : ℝ) + m ≤ 4 * Δ * s + 6 * Δ)
    (hΔw : (Δw : ℝ) ≤ m) (hs : (s : ℝ) + 1 ≤ σ)
    (hOwed : (b₀ : ℝ) < 4 * Δ * σ + 2 * Δ → (b₁ : ℝ) + m ≤ 4 * Δ * σ + 3 * Δ)
    (hD : D + 4 * Δ * k = 4 * Δ * σ + 5 * Δ)
    (hρ : ρ ≤ D + B) :
    GoldilocksCorrectness.Statements.AbstractTrace.deadlineOutsideR Δw GST b₀ b₁ ρ ≤
      4 * Δ * σ + 3 * Δ := by
  have hΔ0 : (0 : ℝ) ≤ 4 * Δ := by positivity
  have hΔ0' : (0 : ℝ) ≤ Δ := by positivity
  have hts : 4 * (Δ : ℝ) * (s + 1) ≤ 4 * Δ * σ := mul_le_mul_of_nonneg_left hs hΔ0
  have hρw : ρ + Δw ≤ 4 * Δ * σ + 2 * Δ := by linarith
  have hGw : (GST : ℝ) + Δw ≤ 4 * Δ * σ + 2 * Δ := by linarith
  have hmax : max ρ (GST : ℝ) + Δw ≤ 4 * Δ * σ + 2 * Δ := by
    rcases le_total ρ GST with h | h
    · rw [max_eq_right h]; exact hGw
    · rw [max_eq_left h]; exact hρw
  unfold GoldilocksCorrectness.Statements.AbstractTrace.deadlineOutsideR
  split_ifs with h
  · linarith
  · push_neg at h
    have hb₁w : (b₁ : ℝ) + Δw ≤ 4 * Δ * σ + 3 * Δ := by
      have := hOwed (by linarith)
      linarith
    rcases le_total ρ (max (b₁ : ℝ) GST) with hρm | hρm
    · rw [max_eq_right hρm]
      rcases le_total (b₁ : ℝ) GST with hbG | hbG
      · rw [max_eq_right hbG]; linarith
      · rw [max_eq_left hbG]; exact hb₁w
    · rw [max_eq_left hρm]; linarith

/-- **Kit fact, a suspended deadline at most a bound.** A message on the wire at a real time `τ` at
most `X` has its suspended deadline at the delay `Δn` at most `c`, when `GST + Δn` is at most `b₀` and
at most `c`, `X + Δn` is at most `c`, and either `X + Δn` is at most `b₀` (the deadline is the ordinary
one) or `b₁ + Δn` is at most `c`.

Why: in the ordinary case the deadline is `max τ GST + Δn`, at most `c`; in the other case `max τ GST + Δn`
is after `b₀`, which rules out the first disjunct, and the deadline `max τ (max b₁ GST) + Δn` is at most
`c` by the second.

The variables:
- `Δn`: the delay; `GST`, `b₀`, `b₁`: the promise's times; `τ`: the send's real time; `X`: a bound on it;
  `c`: the bound on the deadline.

Read aloud: a send by `X` is due by `c` when `X` and `GST` are a delay before `c`, and either `X` is a delay
before `b₀` or `b₁` is a delay before `c`. -/
theorem deadlineOutsideR_le_of {Δn GST b₀ b₁ : ℕ} {τ X c : ℝ} (hτ : τ ≤ X)
    (hGb : (GST : ℝ) + Δn ≤ b₀) (hG : (GST : ℝ) + Δn ≤ c) (hX : X + Δn ≤ c)
    (hcase : X + Δn ≤ b₀ ∨ (b₁ : ℝ) + Δn ≤ c) :
    GoldilocksCorrectness.Statements.AbstractTrace.deadlineOutsideR Δn GST b₀ b₁ τ ≤ c := by
  unfold GoldilocksCorrectness.Statements.AbstractTrace.deadlineOutsideR
  split_ifs with h
  · have : max τ (GST : ℝ) ≤ c - Δn := max_le (by linarith) (by linarith)
    linarith
  · rcases hcase with h1 | h1
    · exfalso
      apply h
      have : max τ (GST : ℝ) ≤ b₀ - Δn := max_le (by linarith) (by linarith)
      linarith
    · have : max τ (max (b₁ : ℝ) GST) ≤ c - Δn :=
        max_le (by linarith) (max_le (by linarith) (by linarith))
      linarith

section Instance
variable (M : GoldilocksModel V)

/-- The synchrony premise at `Δ` and the catch-up premise at `Δw`, both suspended on `[b₀, b₁)`,
beside the non-delivery facts of any instance `E`, give the promises `EnvFactsOutside` on a
wake-shaped trace, for `Δ ≥ 1`. The proof is `envFactsSync_of_trace`'s, with the deadlines around
the period.

The variables:
- `M`: the model;
- `R`: the execution's run facts (not read); `E`: an instance of the environment facts, of which
  only the fields that are not delivery promises are read; (not
  read); `hΔ`: `1 ≤ Δ` (not read);
- `Δ`, `Δw`: the delay and the catch-up delay; `GST`: the time from which the network is
  synchronous outside the period; `b₀`, `b₁`: the start and the end of the period.

Read aloud: the two suspended trace premises are the suspended promises. -/
theorem envFactsOutside_of_trace {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N}
    (R : RunFacts M S x)
    {deadline : SignedMsg V (NamedObject V) → ℝ → Option ℝ}
    {ok' : NamedObject V → Prop}
    {B : Type} {W : ViewVocab V B (NamedObject V)}
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline (releaseOf M S.C) ΔRedeliver ok' W)
    {Δ Δw GST b₀ b₁ : ℕ} {ok : NamedObject V → Prop} (hΔ : 1 ≤ Δ)
    (hs : x.SynchronyFromWakeOutside A Δ ΔRedeliver GST (releaseOf M S.C) ok b₀ b₁)
    (hc : x.CatchUpOnWakeOutside A Δw ΔRedeliver GST (releaseOf M S.C) ok b₀ b₁) :
    EnvFactsOutside A x ΔClockAhead ΔClockBehind Δ Δw ΔRedeliver GST (releaseOf M S.C) ok W b₀ b₁ := by
  exact
    -- every field but `caught_up` is the delivery promise read from `hs` beside `E`'s other fields
    { (envFactsBy_of_synchronyFromWakeBy M) x E hs with
      caught_up := fun i k v sm t keep c k' c' hsend hok hk hik hc' hkk' hk' hcc' hact hrel => by
        have hc'' : max (GoldilocksCorrectness.Statements.AbstractTrace.deadlineOutsideR Δ GST b₀ b₁ (x.time (i + 1)))
            (GoldilocksCorrectness.Statements.AbstractTrace.deadlineOutsideR Δw GST b₀ b₁ (x.time k)) = c := Option.some.inj hc'
        have h3 : GoldilocksCorrectness.Statements.AbstractTrace.deadlineOutsideR Δw GST b₀ b₁ (x.time k) ≤ c := hc'' ▸ le_max_right _ _
        -- the catch-up premise at the restart's own suspended deadline, at most `c`, read at the
        -- same tick of the receiver, at a clock value at least `c`
        exact GoldilocksCorrectness.Statements.AbstractTrace.Trace.CatchUpOnWakeBy.apply_tick hc hsend hok hk hik hkk' hk' (le_trans h3 hcc') hact hrel }

end Instance

variable (M : GoldilocksModel V) (F : Facts M)
include F

-- An index `x[i]` into an execution has the valid-index predicate `fun _ _ => True`.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- **Kit theorem, the line `hDelT` from the two promises, at the voter's tick**. The
synchrony promise at a delay `Δn ≤ Δ S` and the catch-up promise at the catch-up delay `Δw ≤ max (Δ S) Δs`,
both suspended on the period `[b₀, b₁)`, with the period's bounds, the recovery bound `hGST`, parents held
at delivery and the bounds `hΔs`, `hSkew`, `hRedeliver`, give the line.

Why, with `s' = σ + 1`: the holder put `T` on the wire at a step `ie` at a real time at most
`ΔClockBehind` after the duty window's start `D` of slot `σ + 1` (`tree_block_relayed_entry`; in the
antecedent's second case the holder's step is at or before a tick of `u` to a clock value at most that
start, at a real time at most that value plus `ΔClockBehind`, `tick_active`). The voter `u` ticks to the view freeze
`c` of slot `σ` at `kc` and to the support cutoff `c₀` of slot `σ` before (`tick_of_active` inside its
window, `honestActiveAt_window`). If no restart of `u` falls between `ie` and `kc`, `u` is active from the
relay to `kc`, the relay is due at least one delay before `c` (`delT_relay_deadline_add_le`), so before
`kc`, and the synchrony promise delivers it before `kc`. Otherwise the last such restart is at a real time
at most `D + ΔClockBehind` (the reader's two cases), its catch-up deadline is at most `c`
(`delT_restart_deadline_le`), and the catch-up promise delivers it before `kc`, read at its clock value `c`.
The re-delivery premise comes from `u`'s tick to `c₀` (`redeliver_before_of_tick`, `hRedeliver`), the start
of `T`'s slot being at most `c₀` (the holder's clock). The delivered block is in `u`'s tree at `kc`
(`mem_tree_of_admitted_delivery`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `R`, `E`: the execution's run facts and environment facts; `hSync`, `hCatch`: the two suspended
  promises; `Δn`, `Δw`: their delays; `GST`, `b₀`, `b₁`: their times; `s`: the hand-over slot; `B`: its
  proposal; `Δs`: the sync delay.

Read aloud: when the network keeps its delivery and catch-up promises outside the period, every certified
entry an honest validator held by the start of the voter's duty window is in the state the voter's tick to
the view freeze starts from. -/
theorem delT_of_promises (U : UniformSchedule M.toSlotLayout)
    {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x)
    {deadline} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline (releaseOf M S.C) ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    {Δn Δw GST s b₀ b₁ : ℕ} {B : Block V} (hΔn : Δn ≤ Δ S) (hΔw : Δw ≤ max (Δ S) Δs)
    (hSync : x.SynchronyFromWakeBy A
      (GoldilocksCorrectness.Statements.AbstractTrace.deadlineOutsideR Δn GST b₀ b₁)
      (releaseOf M S.C) ΔRedeliver acObject)
    (hCatch : GoldilocksCorrectness.Statements.AbstractTrace.CatchUpAfterRestartBy A x
      (fun _ a t => some (max (GoldilocksCorrectness.Statements.AbstractTrace.deadlineOutsideR Δn GST b₀ b₁ a)
        (GoldilocksCorrectness.Statements.AbstractTrace.deadlineOutsideR Δw GST b₀ b₁ t)))
      (releaseOf M S.C) ΔRedeliver acObject)
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C (s + 1))
    (hb₀ : M.supportCutoff S.C (s + 1) ≤ b₀) (hb : b₀ ≤ b₁)
    (hb₁ : b₁ + max (Δ S) Δs ≤ M.voteTime S.C (s + S.C.k)) :
    DelTLine M S A x s B b₀ b₁ Δs := by
  intro s' u Y T h hRootsU hs' hgood hu hY hTY hJ hTB hF hhold
  obtain ⟨j, v, hjT0, hvj, hTj⟩ := hhold
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔ := GoldilocksCorrectness.Proofs.Routines.one_le_Δ S
  have hΔr : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  -- the slot `σ := s' − 1`
  obtain ⟨σ, rfl⟩ : ∃ σ, s' = σ + 1 := ⟨s' - 1, by omega⟩
  unfold VotesOwedInPeriod at hgood
  simp only [Nat.add_sub_cancel] at hgood hF ⊢
  have hsσ : s + 1 ≤ σ := by omega
  -- the schedule, as real numbers
  have hss : ∀ t : ℕ, M.slotStart S.C t = 4 * Δ S * t :=
    (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S
  have hvtE : ∀ t : ℕ, M.voteTime S.C t = M.slotStart S.C t + Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S
  have hscE : ∀ t : ℕ, M.supportCutoff S.C t = M.voteTime S.C t + Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S
  have hvfE : ∀ t : ℕ, M.viewFreeze S.C t = M.slotStart S.C t + 3 * Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_eq M.toSlotLayout F.sched U) S
  have hcR : ((M.viewFreeze S.C σ : ℕ) : ℝ) = 4 * (Δ S : ℝ) * σ + 3 * Δ S := by
    rw [hvfE, hss]; push_cast; ring
  have hc₀R : ((M.supportCutoff S.C σ : ℕ) : ℝ) = 4 * (Δ S : ℝ) * σ + 2 * Δ S := by
    rw [hscE, hvtE, hss]; push_cast; ring
  have hvR : ((M.voteTime S.C (σ + 1) : ℕ) : ℝ) = 4 * (Δ S : ℝ) * σ + 5 * Δ S := by
    rw [hvtE, hss]; push_cast; ring
  have hc₂R : ((M.supportCutoff S.C (σ + 1 + 1) : ℕ) : ℝ) = 4 * (Δ S : ℝ) * σ + 10 * Δ S := by
    rw [hscE, hvtE, hss]; push_cast; ring
  have hcs1R : ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) = 4 * (Δ S : ℝ) * s + 6 * Δ S := by
    rw [hscE, hvtE, hss]; push_cast; ring
  have hvkR : ((M.voteTime S.C (s + S.C.k) : ℕ) : ℝ) = 4 * (Δ S : ℝ) * s + 4 * Δ S * S.C.k + Δ S := by
    rw [hvtE, hss]; push_cast; ring
  have hdwR : ((M.dutyWindowStart S.C (σ + 1) : ℕ) : ℝ) + 4 * Δ S * S.C.k = 4 * (Δ S : ℝ) * σ + 5 * Δ S ∨
      (((M.dutyWindowStart S.C (σ + 1) : ℕ) : ℝ) = 0 ∧ 4 * (Δ S : ℝ) * σ + 5 * Δ S < 4 * Δ S * S.C.k) := by
    rcases (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_cases M.toSlotLayout F.sched U) S
      (σ + 1) with h | ⟨h0, h⟩
    · left
      have : ((M.dutyWindowStart S.C (σ + 1) + 4 * Δ S * S.C.k : ℕ) : ℝ) = ((4 * Δ S * (σ + 1) + Δ S : ℕ) : ℝ) := by
        rw [h]
      push_cast at this; linarith
    · right
      refine ⟨by rw [h0]; simp, ?_⟩
      have : ((4 * Δ S * (σ + 1) + Δ S : ℕ) : ℝ) < ((4 * Δ S * S.C.k : ℕ) : ℝ) := by exact_mod_cast h
      push_cast at this; linarith
  -- the margins, with `max (Δ S) Δs` as a real number
  have hmΔ : ((Δ S : ℕ) : ℝ) ≤ max ((Δ S : ℕ) : ℝ) (Δs : ℝ) := le_max_left _ _
  have hmw : (Δw : ℝ) ≤ max ((Δ S : ℕ) : ℝ) (Δs : ℝ) := by
    have : ((Δw : ℕ) : ℝ) ≤ ((max (Δ S) Δs : ℕ) : ℝ) := by exact_mod_cast hΔw
    rwa [Nat.cast_max] at this
  have hΔsm : max ((Δ S : ℕ) : ℝ) (Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k := hΔs
  have hGSTR : (GST : ℝ) + max ((Δ S : ℕ) : ℝ) (Δs : ℝ) ≤ 4 * (Δ S : ℝ) * s + 6 * Δ S := by
    have : ((GST + max (Δ S) Δs : ℕ) : ℝ) ≤ ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) := by exact_mod_cast hGST
    push_cast at this; rw [hcs1R] at this; exact this
  have hb₀R : 4 * (Δ S : ℝ) * s + 6 * Δ S ≤ b₀ := by
    have : ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) ≤ (b₀ : ℝ) := by exact_mod_cast hb₀
    rw [hcs1R] at this; exact this
  have hbR : (b₀ : ℝ) ≤ b₁ := by exact_mod_cast hb
  have hb₁R : (b₁ : ℝ) + max ((Δ S : ℕ) : ℝ) (Δs : ℝ) ≤ 4 * (Δ S : ℝ) * s + 4 * Δ S * S.C.k + Δ S := by
    have : ((b₁ + max (Δ S) Δs : ℕ) : ℝ) ≤ ((M.voteTime S.C (s + S.C.k) : ℕ) : ℝ) := by exact_mod_cast hb₁
    push_cast at this; rw [hvkR] at this; exact this
  have hσR : (s : ℝ) + 1 ≤ σ := by exact_mod_cast hsσ
  have hΔ0 : (0 : ℝ) ≤ 4 * Δ S := by positivity
  have hσσ : (0 : ℝ) ≤ 4 * Δ S * σ := mul_nonneg hΔ0 (Nat.cast_nonneg σ)
  have hσs : 4 * (Δ S : ℝ) * (s + 1) ≤ 4 * Δ S * σ := mul_le_mul_of_nonneg_left hσR hΔ0
  have hss0 : (0 : ℝ) ≤ 4 * Δ S * s := mul_nonneg hΔ0 (Nat.cast_nonneg s)
  obtain ⟨D, hD⟩ : ∃ D : ℝ, ((M.dutyWindowStart S.C (σ + 1) : ℕ) : ℝ) = D := ⟨_, rfl⟩
  rw [hD] at hdwR
  have hDc₀ : D + ΔClockAhead + ΔClockBehind < 4 * (Δ S : ℝ) * σ + 2 * Δ S := by
    rcases hdwR with h | ⟨h0, -⟩ <;> linarith
  -- `u`'s window, up to its tick `kR` to the support cutoff of slot `σ + 1`
  have hvw := (honestActiveAt_window M F) S A (σ + 1) u E hu
  have hdle := (duty_window_start_le_real M F U) S (σ + 1)
  rw [hD] at hdle
  -- the holder's step is at a real time at most `D + ΔClockBehind`: at most `D`, or at or before a tick of
  -- `u` to a clock value at most the window's start, at a real time at most that value plus `ΔClockBehind`
  have hjT : x.time j ≤ D + ΔClockBehind := by
    rcases hjT0 with h | ⟨k, c₀, hjk, hk, hc⟩
    · rw [hD] at h; linarith
    · have h1 := htime hjk
      have h2 := (E.tick_active k u _ hk).2.2
      have h3 : ((c₀ : ℤ) : ℝ) ≤ ((duty_window_start S.C (σ + 1) : ℤ) : ℝ) := by exact_mod_cast hc
      push_cast at h3
      linarith
  obtain ⟨kR, hkR, hwin⟩ := (tick_window_of_activeThroughoutToTick_int M) x R E hvw
    (t₀ := ((M.supportCutoff S.C σ : ℕ) : ℝ) - ΔClockAhead) (by rw [hc₀R]; linarith)
  have hkRt := (E.tick_active kR u _ hkR).2.1
  rw [hc₂R] at hkRt
  -- `u`'s ticks to the view freeze `c` of slot `σ` (at `kc`) and to the support cutoff `c₀` (at `k₀`)
  have hinwin : ∀ (t : ℕ) (i : ℕ), ((M.supportCutoff S.C σ : ℕ) : ℝ) ≤ t →
      (t : ℝ) ≤ ((M.viewFreeze S.C σ : ℕ) : ℝ) →
      (t : ℝ) - ΔClockAhead ≤ x.time i → x.time i ≤ t + ΔClockBehind → u ∈ A.active i := by
    intro t i ht1 ht2 h1 h2
    refine hwin i (by linarith) ?_
    exact ((lt_of_time_lt M) x R (by rw [hcR] at ht2; linarith)).le
  have hc1 : 1 ≤ M.viewFreeze S.C σ := by
    have : (1 : ℝ) ≤ ((M.viewFreeze S.C σ : ℕ) : ℝ) := by rw [hcR]; linarith
    exact_mod_cast this
  have hc₀1 : 1 ≤ M.supportCutoff S.C σ := by
    have : (1 : ℝ) ≤ ((M.supportCutoff S.C σ : ℕ) : ℝ) := by rw [hc₀R]; linarith
    exact_mod_cast this
  obtain ⟨kc, hkc, hkc1, hkc2⟩ := E.tick_of_active (M.viewFreeze S.C σ) hc1 u fun i h1 h2 =>
    hinwin _ i (by rw [hcR, hc₀R]; linarith) le_rfl h1 h2
  obtain ⟨k₀, hk₀, -, -⟩ := E.tick_of_active (M.supportCutoff S.C σ) hc₀1 u fun i h1 h2 =>
    hinwin _ i le_rfl (by rw [hcR, hc₀R]; linarith) h1 h2
  have hvkc : u ∉ A.corrupted kc := E.not_mem_corrupted_of_tick hkc
  have hukc : u ∈ A.awake kc := Activity.mem_awake_of_mem_active (E.tick_active kc u _ hkc).1
  have hti : x.tickInput u (M.viewFreeze S.C σ) = x.st kc u := by
    unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hkc]
  rw [hti] at hF ⊢
  -- the genesis block is in every tree
  by_cases hg : T = Block.genesis
  · subst hg
    exact (GoldilocksCorrectness.Record.Statements.Executions.genesis_mem_T_of_exec M F) S A x R E kc u
  -- the holder's relay of `T`, at a real time at most `D`
  obtain ⟨ie, hiej, hput, hvie, -, -⟩ := (tree_block_relayed_entry M F) x R E hTj hg
  have hsendT : x.HonestSendAt A ie (⟨v, NamedObject.block T⟩ : SignedMsg V (NamedObject V)) := ⟨hput, hvie⟩
  have htie : x.time (ie + 1) ≤ D + ΔClockBehind := le_trans (htime (show ie + 1 ≤ j by omega)) hjT
  have hiekc : ie < kc := by
    have : ie + 1 < kc := (lt_of_time_lt M) x R (by rw [hcR] at hkc1; linarith)
    omega
  -- the start of `T`'s slot is at most the support cutoff `c₀` of slot `σ`
  have hsl : ∀ t : ℕ, M.slot S.C t = S.C.slot (t : Int) := fun t => by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U),
      GoldilocksCorrectness.Proofs.Routines.slot_natCast]
  have hrel : M.slotStart S.C T.slot ≤ M.supportCutoff S.C σ := by
    have hTs := (slot_le_clockValue_of_mem_tree M F) R E hvj hTj
    rw [← hsl] at hTs
    have hle := ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_le_iff M.toSlotLayout F.sched) S
      T.slot _).2 hTs
    have hcv := (clockValue_le_time_add_ahead M F) x R E j v
    have hD0 : (0 : ℝ) ≤ D := by rw [← hD]; positivity
    have hcvD : ((x.clockValue j v : ℕ) : ℝ) ≤ ((M.supportCutoff S.C σ : ℕ) : ℝ) := by
      rw [hc₀R]
      refine le_trans hcv (max_le (by linarith) (by linarith))
    exact le_trans hle (by exact_mod_cast hcvD)
  have hrelc : M.slotStart S.C T.slot ≤ M.viewFreeze S.C σ := by
    have : ((M.supportCutoff S.C σ : ℕ) : ℝ) ≤ ((M.viewFreeze S.C σ : ℕ) : ℝ) := by
      rw [hcR, hc₀R]; linarith
    exact le_trans hrel (by exact_mod_cast this)
  -- the re-delivery premise, from `u`'s tick to `c₀`
  have hprem := redeliver_before_of_tick M F R E (r := M.slotStart S.C T.slot) hk₀ hkc
    (by rw [hcR, hc₀R]; linarith) hrel
  -- a delivery before `kc` puts `T` in `u`'s tree at `kc`
  have hkct := (E.tick_active kc u _ hkc).2.2
  have hfin : ∀ jd : ℕ, jd < kc →
      x.lbl jd = Event.deliver u (⟨v, NamedObject.block T⟩ : SignedMsg V (NamedObject V)) →
      (∀ r : ℕ, releaseOf M S.C (NamedObject.block T) = some r → r ≤ M.viewFreeze S.C σ →
        x.ReactedAtLeast jd u r) →
      T ∈ (x.st kc u).tree := by
    intro jd hjdk hlj hadm
    have hTjd : x.time jd ≤ ((M.voteTime S.C (σ + 1) : ℕ) : ℝ) := by
      have := htime hjdk.le
      rw [hvR]; rw [hcR] at hkct; linarith
    have hTj' : x.time j ≤ ((M.voteTime S.C (σ + 1) : ℕ) : ℝ) := by rw [hvR]; linarith
    exact (mem_tree_of_admitted_delivery M F U) R E hRootsU hParent hvj hTj' hTj hlj hTjd
      (hadm _ rfl hrelc) hjdk hvkc hF
  have hrelmap : ∀ (P : ℕ → Prop), (∀ (j₀ k₁ t₁ : ℕ), ¬ x.ReactedAtLeast j₀ u (M.slotStart S.C T.slot) →
      j₀ < k₁ → x.lbl k₁ = Event.tick u t₁ →
      (∀ (l t' : ℕ), j₀ < l → l < k₁ → x.lbl l = Event.tick u t' → t' < M.slotStart S.C T.slot) →
      x.time (k₁ + 1) + ΔRedeliver ≤ x.time kc) →
      ∀ (r j₀ k₁ t₁ : ℕ), releaseOf M S.C (NamedObject.block T) = some r → P j₀ →
        x.lbl j₀ = Event.deliver u (⟨v, NamedObject.block T⟩ : SignedMsg V (NamedObject V)) →
        ¬ x.ReactedAtLeast j₀ u r → j₀ < k₁ → k₁ ≤ kc → x.lbl k₁ = Event.tick u t₁ → r ≤ t₁ →
        (∀ (l t' : ℕ), j₀ < l → l < k₁ → x.lbl l = Event.tick u t' → t' < r) →
        x.time (k₁ + 1) + ΔRedeliver ≤ x.time kc := by
    intro P hp r j₀ k₁ t₁ hr _ _ hnr hjk₁ _ hlk₁ _ hfirst
    have hr' : M.slotStart S.C T.slot = r := Option.some.inj hr
    subst hr'
    exact hp j₀ k₁ t₁ hnr hjk₁ hlk₁ hfirst
  -- the relay's deadline is at least one delay before `c`
  have hdl := delT_relay_deadline_add_le (Δn := Δn) (k := S.C.k) (s := s) (σ := σ) (GST := GST) (b₀ := b₀) (b₁ := b₁)
    (τ := x.time (ie + 1)) (D := D) hΔ hΔn hmΔ hA0 hB0 hSkew hΔsm
    hGSTR hb₀R hbR hb₁R hσR hdwR (by linarith)
  by_cases hrs : ∃ r : ℕ, ie < r ∧ r < kc ∧ ∃ (tR : ℕ) (keep : Bool), x.lbl r = Event.restart u tR keep
  · -- the last restart `r` of `u` before `kc`, after the relay: the catch-up promise
    obtain ⟨r, ⟨hier, hrkc, tR, keep, hlr⟩, hmax⟩ : ∃ r : ℕ,
        (ie < r ∧ r < kc ∧ ∃ (tR : ℕ) (keep : Bool), x.lbl r = Event.restart u tR keep) ∧
        ∀ r' : ℕ, r < r' → r' ≤ kc →
          ¬ (ie < r' ∧ r' < kc ∧ ∃ (tR : ℕ) (keep : Bool), x.lbl r' = Event.restart u tR keep) := by
      classical
      obtain ⟨r, hr⟩ := hrs
      exact ⟨Nat.findGreatest (fun r => ie < r ∧ r < kc ∧ ∃ (tR : ℕ) (keep : Bool),
          x.lbl r = Event.restart u tR keep) kc,
        Nat.findGreatest_spec (P := fun r => ie < r ∧ r < kc ∧ ∃ (tR : ℕ) (keep : Bool),
          x.lbl r = Event.restart u tR keep) (le_of_lt hr.2.1) hr,
        fun r' h1 h2 => Nat.findGreatest_is_greatest h1 h2⟩
    have hact : ∀ i : ℕ, r < i → i ≤ kc → u ∈ A.active i := by
      intro i h1 h2
      refine Activity.mem_active.2 ⟨?_, fun hc => hvkc (E.corrupted_mono i kc h2 hc)⟩
      by_contra hni
      obtain ⟨m', hm1, hm2, tR', keep', hm'⟩ := (exists_restart_of_not_awake M) x E h2 hni hukc
      exact hmax m' (by omega) hm2.le ⟨by omega, hm2, tR', keep', hm'⟩
    -- the restart is at a real time at most `D + ΔClockBehind`, and `D` is the formula's
    have hnaw : u ∉ A.awake r := (E.restart_crashed r u tR keep hlr).1
    have hkckR : kc ≤ kR := ((lt_of_time_lt M) x R (by rw [hcR] at hkct; linarith)).le
    obtain ⟨k'', hk'', hcase⟩ := Activity.mem_activeThroughoutToTick.1 hvw
    have hk''R : k'' = kR := E.tick_unique _ _ u _ hk'' hkR
    subst hk''R
    have hrT : x.time r ≤ D + ΔClockBehind ∧ 1 ≤ M.dutyWindowStart S.C (σ + 1) := by
      rcases hcase with h1 | ⟨ka, -, ca, hca, hka, h2⟩
      · -- never restarted up to its tick to the cutoff: not so, `r` is a restart before it
        exact absurd (Activity.mem_awake_of_mem_active (h1 r (by omega))) hnaw
      · -- after its last restart it ticked to `ca ≤ duty_window_start S.C (σ + 1)`, so that start is not
        -- negative, and the restart is before that tick, at a real time at most `ca + ΔClockBehind`
        have hrka : r < ka := by
          by_contra hc
          exact hnaw (Activity.mem_awake_of_mem_active (h2 r (by omega) (by omega)))
        have := htime hrka.le
        have hkat := (E.tick_active ka u _ hka).2.2
        have hca' : ((ca : ℤ) : ℝ) ≤ ((duty_window_start S.C (σ + 1) : ℤ) : ℝ) := by exact_mod_cast hca
        have h1le : 1 ≤ M.dutyWindowStart S.C (σ + 1) := by
          rcases (GoldilocksCorrectness.Record.Proofs.Routines.lt_zero_or_one_le_dutyWindowStart_of_le
            M.toSlotLayout F.sched U) S (σ + 1) hca with h | h
          · omega
          · exact h
        push_cast at hca'
        exact ⟨by linarith, h1le⟩
    have hDf : D + 4 * Δ S * S.C.k = 4 * (Δ S : ℝ) * σ + 5 * Δ S := by
      rcases hdwR with h | ⟨h0, -⟩
      · exact h
      · exfalso
        have : (1 : ℝ) ≤ ((M.dutyWindowStart S.C (σ + 1) : ℕ) : ℝ) := by exact_mod_cast hrT.2
        rw [hD] at this
        linarith
    have hcd := delT_restart_deadline_le (Δw := Δw) (k := S.C.k) (s := s) (σ := σ) (GST := GST) (b₀ := b₀)
      (b₁ := b₁) (ρ := x.time r) (D := D) hmΔ hA0 hB0 hΔsm
      hGSTR hmw hσR
      (fun hb0 => by
        have hb0' : b₀ < M.supportCutoff S.C σ := by
          have : (b₀ : ℝ) < ((M.supportCutoff S.C σ : ℕ) : ℝ) := by rw [hc₀R]; exact hb0
          exact_mod_cast this
        have h2 : b₁ + max (Δ S) Δs ≤ M.supportCutoff S.C σ + Δ S := by
          by_contra hc
          exact hgood ⟨hb0', not_le.mp hc⟩
        have : ((b₁ + max (Δ S) Δs : ℕ) : ℝ) ≤ ((M.supportCutoff S.C σ + Δ S : ℕ) : ℝ) := by
          exact_mod_cast h2
        push_cast at this
        rw [hc₀R] at this
        linarith) hDf hrT.1
    obtain ⟨jd, -, hjdk, hlj, hadm, -⟩ := hCatch ie r u ⟨v, NamedObject.block T⟩ tR keep _ kc
      (M.viewFreeze S.C σ) hsendT trivial hlr hier rfl hrkc hkc
      (max_le (by rw [hcR]; linarith) (by rw [hcR]; exact hcd)) hact
      (hrelmap (fun j₀ => r < j₀) hprem)
    exact hfin jd hjdk hlj hadm
  · -- no restart of `u` between the relay and `kc`: the synchrony promise
    have hawk : ∀ i : ℕ, ie + 1 ≤ i → i ≤ kc → u ∈ A.active i := by
      intro i h1 h2
      refine Activity.mem_active.2 ⟨?_, fun hc => hvkc (E.corrupted_mono i kc h2 hc)⟩
      by_contra hni
      obtain ⟨m', hm1, hm2, tR', keep', hm'⟩ := (exists_restart_of_not_awake M) x E h2 hni hukc
      exact hrs ⟨m', by omega, hm2, tR', keep', hm'⟩
    obtain ⟨jd, -, hjdk, hlj, hadm, -⟩ := hSync ie kc u ⟨v, NamedObject.block T⟩ (M.viewFreeze S.C σ)
      hsendT trivial hkc hiekc hawk (by rw [hcR] at hkc1; linarith)
      (hrelmap (fun j₀ => ie < j₀) hprem)
    exact hfin jd hjdk hlj hadm

/-- **Kit fact, an honest active validator ticks inside its window.** A member `w` of
`honestActiveAt M S A x s₁` ticks to every clock value `t ≥ 1` that is more than both clock bounds after
the duty window's start of `s₁` and more than both clock bounds before the support cutoff of `s₁ + 1`, at a
step whose real time is in `[t − ΔClockAhead, t + ΔClockBehind]`.

Why: `w` is active after every step from the first one whose time is `t − ΔClockAhead` up to its tick to the
support cutoff of `s₁ + 1` (`tick_window_of_activeThroughoutToTick_int`), which is at a real time at least
that cutoff minus `ΔClockAhead`, so after every step of the window around `t`; the environment's facts then
give the tick (`tick_of_active`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `R`, `E`: the run's facts and the environment's facts; `s₁`: the slot; `t`: the clock value; `w`: the
  member.

Read aloud: an honest active validator of slot `s₁` ticks to every clock value well inside its window. -/
theorem tick_of_honestActiveAt (U : UniformSchedule M.toSlotLayout)
    {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {s₁ t : ℕ} {w : V} (hw : w ∈ honestActiveAt M S A x s₁) (ht1 : 1 ≤ t)
    (hlo : ((M.dutyWindowStart S.C s₁ : ℕ) : ℝ) + ΔClockAhead + ΔClockBehind < t)
    (hhi : (t : ℝ) + ΔClockAhead + ΔClockBehind < ((M.supportCutoff S.C (s₁ + 1) : ℕ) : ℝ)) :
    ∃ k : ℕ, x.lbl k = Event.tick w t ∧ (t : ℝ) - ΔClockAhead ≤ x.time k ∧
      x.time k ≤ t + ΔClockBehind := by
  have hdle := (duty_window_start_le_real M F U) S s₁
  obtain ⟨kR, hkR, hwin⟩ := (tick_window_of_activeThroughoutToTick_int M) x R E
    ((honestActiveAt_window M F) S A s₁ w E hw) (t₀ := (t : ℝ) - ΔClockAhead) (by linarith)
  have hkRt := (E.tick_active kR w _ hkR).2.1
  exact E.tick_of_active t ht1 w fun i h1 h2 => hwin i h1 ((lt_of_time_lt M) x R (by linarith)).le

/-- **Kit theorem, a holder's relay reaches the voter's tick to the view freeze, or the line's antecedent
holds.** For the voter `u ∈ honestActiveAt M S A x (σ + 1)` and an honest holder `v` of `T` at a step `j`
whose time is at most `ΔClockBehind` after the support cutoff of slot `σ`, with the suspended synchrony
promise at a delay whose deadline for every relay by the time of `j` is at most `ΔClockAhead` before the
view freeze of slot `σ`: either `T` is in the state `u`'s tick to that view freeze starts from, or some
validator, outside the adversary set at a step whose time is at most the start of `u`'s duty window, or at
a step at or before a tick of `u` to a clock value at most the spec's start of that window, holds `T` at
that step (the antecedent of `DelTLine`).

Why: `v` put `T` on the wire at a step `ie < j`, its tree holding `T` after it (`tree_block_relayed_entry`).
If that step's successor is at a time at most the window's start, or at or before `u`'s tick that opens its
window (the second case of `activeThroughoutToTick`), the antecedent holds at `ie + 1`. Otherwise `u` is
active after every step from `ie + 1` to its tick `kc` to the view freeze, which is at a real time at least
the deadline, and the promise delivers `T` before `kc`; the re-delivery premise comes from `u`'s tick to the
support cutoff of slot `σ` (`T`'s slot starts by then: `v`'s clock at `j` is before the start of slot
`σ + 1`), and the delivered block is in `u`'s tree at `kc` (`mem_tree_of_admitted_delivery`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `R`, `E`: the execution's run facts and environment facts; `hSync`: the suspended synchrony promise at
  the delay `Δn`; `GST`, `b₀`, `b₁`: its times; `Δs`: the sync delay; `σ`: the slot before the vote; `u`:
  the voter; `j`, `v`: the holder's step and the holder; `T`: the block.

Read aloud: a block an honest validator holds by the support cutoff of slot `σ`, plus the clock bound,
reaches the voter by its tick to the view freeze of slot `σ`, unless a validator held it early enough for
the delivery line. -/
theorem held_reaches_voter_or_line (U : UniformSchedule M.toSlotLayout)
    {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x)
    {deadline} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline (releaseOf M S.C) ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    {Δn GST b₀ b₁ : ℕ}
    (hSync : x.SynchronyFromWakeBy A
      (GoldilocksCorrectness.Statements.AbstractTrace.deadlineOutsideR Δn GST b₀ b₁)
      (releaseOf M S.C) ΔRedeliver acObject)
    (hParent : ParentHeldAtDelivery M x)
    (σ : ℕ) (u : V) (hu : u ∈ honestActiveAt M S A x (σ + 1))
    (hRootsU : RootsNameBlocksUntil M A x (M.voteTime S.C (σ + 1)))
    {j : ℕ} {v : V} {T : Block V} (hvj : v ∉ A.corrupted j) (hTj : T ∈ (x.st j v).tree)
    (hjc : x.time j ≤ ((M.supportCutoff S.C σ : ℕ) : ℝ) + ΔClockBehind)
    (hdl : ∀ τ : ℝ, τ ≤ x.time j →
      GoldilocksCorrectness.Statements.AbstractTrace.deadlineOutsideR Δn GST b₀ b₁ τ ≤
        ((M.viewFreeze S.C σ : ℕ) : ℝ) - ΔClockAhead)
    (hF : (x.tickInput u (M.viewFreeze S.C σ)).finalized.compatible T = true) :
    T ∈ (x.tickInput u (M.viewFreeze S.C σ)).tree ∨
      ∃ (j' : ℕ) (v' : V), (x.time j' ≤ M.dutyWindowStart S.C (σ + 1) ∨
          ∃ (k c₀ : ℕ), j' ≤ k ∧ x.lbl k = Event.tick u c₀ ∧
            (c₀ : ℤ) ≤ Goldilocks.duty_window_start S.C (σ + 1)) ∧
        v' ∉ A.corrupted j' ∧ T ∈ (x.st j' v').tree := by
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔ := GoldilocksCorrectness.Proofs.Routines.one_le_Δ S
  have hΔr : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  -- the schedule, as real numbers
  have hss : ∀ t : ℕ, M.slotStart S.C t = 4 * Δ S * t :=
    (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S
  have hvtE : ∀ t : ℕ, M.voteTime S.C t = M.slotStart S.C t + Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S
  have hscE : ∀ t : ℕ, M.supportCutoff S.C t = M.voteTime S.C t + Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S
  have hvfE : ∀ t : ℕ, M.viewFreeze S.C t = M.slotStart S.C t + 3 * Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_eq M.toSlotLayout F.sched U) S
  have hcR : ((M.viewFreeze S.C σ : ℕ) : ℝ) = 4 * (Δ S : ℝ) * σ + 3 * Δ S := by
    rw [hvfE, hss]; push_cast; ring
  have hc₀R : ((M.supportCutoff S.C σ : ℕ) : ℝ) = 4 * (Δ S : ℝ) * σ + 2 * Δ S := by
    rw [hscE, hvtE, hss]; push_cast; ring
  have hvR : ((M.voteTime S.C (σ + 1) : ℕ) : ℝ) = 4 * (Δ S : ℝ) * σ + 5 * Δ S := by
    rw [hvtE, hss]; push_cast; ring
  have hc₂R : ((M.supportCutoff S.C (σ + 1 + 1) : ℕ) : ℝ) = 4 * (Δ S : ℝ) * σ + 10 * Δ S := by
    rw [hscE, hvtE, hss]; push_cast; ring
  have hss1R : ((M.slotStart S.C (σ + 1) : ℕ) : ℝ) = 4 * (Δ S : ℝ) * σ + 4 * Δ S := by
    rw [hss]; push_cast; ring
  have hΔ0 : (0 : ℝ) ≤ 4 * Δ S := by positivity
  have hσσ : (0 : ℝ) ≤ 4 * Δ S * σ := mul_nonneg hΔ0 (Nat.cast_nonneg σ)
  -- the start of `u`'s window is more than both clock bounds before the support cutoff of `σ`
  have hdle := (duty_window_start_le_real M F U) S (σ + 1)
  have hDc₀ : ((M.dutyWindowStart S.C (σ + 1) : ℕ) : ℝ) + ΔClockAhead + ΔClockBehind <
      4 * (Δ S : ℝ) * σ + 2 * Δ S := by
    have hmΔ : ((Δ S : ℕ) : ℝ) ≤ max ((Δ S : ℕ) : ℝ) (Δs : ℝ) := le_max_left _ _
    have hΔsm : max ((Δ S : ℕ) : ℝ) (Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind <
        4 * Δ S * S.C.k := hΔs
    rcases (GoldilocksCorrectness.Record.Proofs.Routines.dutyWindowStart_cases M.toSlotLayout F.sched U) S
      (σ + 1) with h | ⟨h0, h⟩
    · have : ((M.dutyWindowStart S.C (σ + 1) + 4 * Δ S * S.C.k : ℕ) : ℝ) =
          ((4 * Δ S * (σ + 1) + Δ S : ℕ) : ℝ) := by
        rw [h]
      push_cast at this; linarith
    · rw [h0]; push_cast; linarith
  -- `u`'s window, up to its tick `kR` to the support cutoff of slot `σ + 1`
  have hvw := (honestActiveAt_window M F) S A (σ + 1) u E hu
  obtain ⟨kR, hkR, hwin⟩ := (tick_window_of_activeThroughoutToTick_int M) x R E hvw
    (t₀ := ((M.supportCutoff S.C σ : ℕ) : ℝ) - ΔClockAhead) (by rw [hc₀R]; linarith)
  have hkRt := (E.tick_active kR u _ hkR).2.1
  rw [hc₂R] at hkRt
  -- `u`'s ticks to the view freeze `c` of slot `σ` (at `kc`) and to the support cutoff `c₀` (at `k₀`)
  have hinwin : ∀ (t : ℕ) (i : ℕ), ((M.supportCutoff S.C σ : ℕ) : ℝ) ≤ t →
      (t : ℝ) ≤ ((M.viewFreeze S.C σ : ℕ) : ℝ) →
      (t : ℝ) - ΔClockAhead ≤ x.time i → x.time i ≤ t + ΔClockBehind → u ∈ A.active i := by
    intro t i ht1 ht2 h1 h2
    refine hwin i (by linarith) ?_
    exact ((lt_of_time_lt M) x R (by rw [hcR] at ht2; linarith)).le
  have hc1 : 1 ≤ M.viewFreeze S.C σ := by
    have : (1 : ℝ) ≤ ((M.viewFreeze S.C σ : ℕ) : ℝ) := by rw [hcR]; linarith
    exact_mod_cast this
  have hc₀1 : 1 ≤ M.supportCutoff S.C σ := by
    have : (1 : ℝ) ≤ ((M.supportCutoff S.C σ : ℕ) : ℝ) := by rw [hc₀R]; linarith
    exact_mod_cast this
  obtain ⟨kc, hkc, hkc1, hkc2⟩ := E.tick_of_active (M.viewFreeze S.C σ) hc1 u fun i h1 h2 =>
    hinwin _ i (by rw [hcR, hc₀R]; linarith) le_rfl h1 h2
  obtain ⟨k₀, hk₀, -, -⟩ := E.tick_of_active (M.supportCutoff S.C σ) hc₀1 u fun i h1 h2 =>
    hinwin _ i le_rfl (by rw [hcR, hc₀R]; linarith) h1 h2
  have hvkc : u ∉ A.corrupted kc := E.not_mem_corrupted_of_tick hkc
  have hti : x.tickInput u (M.viewFreeze S.C σ) = x.st kc u := by
    unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hkc]
  rw [hti] at hF ⊢
  have hkct := (E.tick_active kc u _ hkc).2.2
  have hkckR : kc ≤ kR := ((lt_of_time_lt M) x R (by rw [hcR] at hkct; linarith)).le
  -- the genesis block is in every tree
  by_cases hg : T = Block.genesis
  · subst hg
    exact Or.inl ((GoldilocksCorrectness.Record.Statements.Executions.genesis_mem_T_of_exec M F) S A x R E kc u)
  -- the holder's relay of `T`
  obtain ⟨ie, hiej, hput, hvie, -, hTie⟩ := (tree_block_relayed_entry M F) x R E hTj hg
  have hvie1 : v ∉ A.corrupted (ie + 1) := fun hc => hvj (E.corrupted_mono _ _ (by omega) hc)
  -- the relay at a time at most the window's start: the antecedent
  by_cases hearly : x.time (ie + 1) ≤ M.dutyWindowStart S.C (σ + 1)
  · exact Or.inr ⟨ie + 1, v, Or.inl hearly, hvie1, hTie⟩
  -- the relay at or before `u`'s tick that opens its window: the antecedent; otherwise `u` is active
  -- after every step from the relay to `kc`
  obtain ⟨k'', hk'', hcase⟩ := Activity.mem_activeThroughoutToTick.1 hvw
  have hk''R : k'' = kR := E.tick_unique _ _ u _ hk'' hkR
  subst hk''R
  by_cases hopen : ∃ (ka ca : ℕ), ie + 1 ≤ ka ∧ x.lbl ka = Event.tick u ca ∧
      (ca : ℤ) ≤ Goldilocks.duty_window_start S.C (σ + 1)
  · obtain ⟨ka, ca, h1, h2, h3⟩ := hopen
    exact Or.inr ⟨ie + 1, v, Or.inr ⟨ka, ca, h1, h2, h3⟩, hvie1, hTie⟩
  have hawk : ∀ i : ℕ, ie + 1 ≤ i → i ≤ kc → u ∈ A.active i := by
    rcases hcase with h1 | ⟨ka, -, ca, hca, hka, h2⟩
    · exact fun i _ h => h1 i (by omega)
    · have hka' : ka < ie + 1 := by
        by_contra hc
        exact hopen ⟨ka, ca, by omega, hka, hca⟩
      exact fun i h h' => h2 i (by omega) (by omega)
  left
  have hsendT : x.HonestSendAt A ie (⟨v, NamedObject.block T⟩ : SignedMsg V (NamedObject V)) :=
    ⟨hput, hvie⟩
  have hiekc : ie < kc := by
    have : ie + 1 < kc := (lt_of_time_lt M) x R (by
      have := htime (show ie + 1 ≤ j by omega)
      rw [hcR] at hkc1; rw [hc₀R] at hjc; linarith)
    omega
  -- the start of `T`'s slot is at most the support cutoff `c₀` of slot `σ`: `v`'s clock at `j` is before
  -- the start of slot `σ + 1`
  have hsl : ∀ t : ℕ, M.slot S.C t = S.C.slot (t : Int) := fun t => by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U),
      GoldilocksCorrectness.Proofs.Routines.slot_natCast]
  have hrel : M.slotStart S.C T.slot ≤ M.supportCutoff S.C σ := by
    have hTs := (slot_le_clockValue_of_mem_tree M F) R E hvj hTj
    rw [← hsl] at hTs
    have hcv := (clockValue_le_time_add_ahead M F) x R E j v
    have hcvlt : x.clockValue j v < M.slotStart S.C (σ + 1) := by
      have : ((x.clockValue j v : ℕ) : ℝ) < ((M.slotStart S.C (σ + 1) : ℕ) : ℝ) := by
        rw [hss1R]
        refine lt_of_le_of_lt hcv (max_lt (by linarith) (by rw [hc₀R] at hjc; linarith))
      exact_mod_cast this
    have hsσ := (GoldilocksCorrectness.Record.Proofs.Routines.slot_lt_of_lt_slotStart M.toSlotLayout
      F.sched) S hcvlt
    have h1 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S
      (show T.slot ≤ σ from le_trans hTs (Nat.lt_succ_iff.1 hsσ))
    have h2 : M.slotStart S.C σ ≤ M.supportCutoff S.C σ := by rw [hscE, hvtE]; omega
    omega
  have hrelc : M.slotStart S.C T.slot ≤ M.viewFreeze S.C σ := by
    have : ((M.supportCutoff S.C σ : ℕ) : ℝ) ≤ ((M.viewFreeze S.C σ : ℕ) : ℝ) := by
      rw [hcR, hc₀R]; linarith
    exact le_trans hrel (by exact_mod_cast this)
  -- the re-delivery premise, from `u`'s tick to `c₀`
  have hprem := redeliver_before_of_tick M F R E (r := M.slotStart S.C T.slot) hk₀ hkc
    (by rw [hcR, hc₀R]; linarith) hrel
  have hrelmap : ∀ (r j₀ k₁ t₁ : ℕ), releaseOf M S.C (NamedObject.block T) = some r → ie < j₀ →
      x.lbl j₀ = Event.deliver u (⟨v, NamedObject.block T⟩ : SignedMsg V (NamedObject V)) →
      ¬ x.ReactedAtLeast j₀ u r → j₀ < k₁ → k₁ ≤ kc → x.lbl k₁ = Event.tick u t₁ → r ≤ t₁ →
      (∀ (l t' : ℕ), j₀ < l → l < k₁ → x.lbl l = Event.tick u t' → t' < r) →
      x.time (k₁ + 1) + ΔRedeliver ≤ x.time kc := by
    intro r j₀ k₁ t₁ hr _ _ hnr hjk₁ _ hlk₁ _ hfirst
    have hr' : M.slotStart S.C T.slot = r := Option.some.inj hr
    subst hr'
    exact hprem j₀ k₁ t₁ hnr hjk₁ hlk₁ hfirst
  obtain ⟨jd, -, hjdk, hlj, hadm, -⟩ := hSync ie kc u ⟨v, NamedObject.block T⟩ (M.viewFreeze S.C σ)
    hsendT trivial hkc hiekc hawk (le_trans (hdl _ (htime (show ie + 1 ≤ j by omega))) hkc1) hrelmap
  -- the delivered block is in `u`'s tree at `kc`
  have hTjd : x.time jd ≤ ((M.voteTime S.C (σ + 1) : ℕ) : ℝ) := by
    have := htime hjdk.le
    rw [hvR]; rw [hcR] at hkct; linarith
  have hTj' : x.time j ≤ ((M.voteTime S.C (σ + 1) : ℕ) : ℝ) := by
    rw [hvR]; rw [hc₀R] at hjc; linarith
  exact (mem_tree_of_admitted_delivery M F U) R E hRootsU hParent hvj hTj' hTj hlj hTjd
    (hadm _ rfl hrelc) hjdk hvkc hF

/-- **The line `hDelT` from the suspended promises.** Under `EnvFactsOutside` with the catch-up
delay `Δw ≤ max (Δ S) Δs`, `Δs + 3Δ ≤ 4Δk`, `GST + max (Δ S) Δs` at most the support cutoff of the
hand-over slot's successor, and parents held at delivery, the line holds.

Why: `delT_of_promises`, with the suspended promises' delivery field at the delay `ΔNet ≤ Δ S` (`hNet`
and the two clock bounds not negative) and their catch-up field.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `R`: the execution's run facts; `EO`: the suspended promises at the delay `Δ S` and the catch-up
  delay `Δw`; `s`: the hand-over slot; `B`: its proposal; `b₀`, `b₁`: the period; `Δs`: the sync
  delay.

Read aloud: when the network keeps its delivery and catch-up promises outside the period, every
certified entry an honest validator held at a step whose time is at most the start of the voter's
duty window reaches the voter by the view freeze of the slot before its vote. -/
theorem delT_of_envFactsOutside (U : UniformSchedule M.toSlotLayout)
    {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x)
    {Δw GST s b₀ b₁ Δs : ℕ} {B : Block V}
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (EO : EnvFactsOutside A x ΔClockAhead ΔClockBehind ΔNet Δw ΔRedeliver GST (releaseOf M S.C) acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks b₀ b₁) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
 (hParent : ParentHeldAtDelivery M x)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) (hΔw : Δw ≤ max (Δ S) Δs)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C (s + 1))
    -- the period starts at or after the hand-over update, is an interval, and ends, with its recovery, by the
    -- vote time of slot `s + k` (the period's bundle `AsyncHypsOfChainBlockGSTBeforeVotes`, T-RC9-1)
    (hb₀ : M.supportCutoff S.C (s + 1) ≤ b₀) (hb : b₀ ≤ b₁)
    (hb₁ : b₁ + max (Δ S) Δs ≤ M.voteTime S.C (s + S.C.k)) :
    DelTLine M S A x s B b₀ b₁ Δs := by
  have hA0 := EO.ahead_nonneg
  have hB0 := EO.behind_nonneg
  have hΔn : ΔNet ≤ Δ S := by
    have : (ΔNet : ℝ) ≤ Δ S := by linarith
    exact_mod_cast this
  exact (delT_of_promises M F U) R EO.toEnvFactsBy hSkew hRedeliver hΔs hΔn hΔw
    (fun i k v sm t hs hok hk hik hwin hdl hrel =>
      EO.delivered i k v sm t _ hs hok hk hik hwin rfl hdl hrel)
    EO.caught_up hParent hGST hb₀ hb hb₁

/-- **The line `hDelT` from the trace premises and the catch-up premise.** The trace's atomic shape
`hWS`, the synchrony premise `hSync` suspended on the period, parents held at delivery `hParent`,
the recovery bound `hGST` at the support cutoff of slot `s + 1` and the period's bounds `hb₀`, `hb`, `hb₁`
(fields of the period's bundle `AsyncHypsOfChainBlockGSTBeforeVotes` the derivation reads, taken as
separate hypotheses since the bundle carries the line; T-RC9-1), and the catch-up premise `hCatch` at a catch-up delay
`Δw ≤ max (Δ S) Δs`, suspended on the period, give the line; `E` supplies the non-delivery facts,
`hΔs` bounds the sync delay.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `R`, `E`: the execution's run facts and environment facts; `GST`: the time from which the network
  is synchronous outside the period; `s`: the hand-over slot; `B`: its proposal; `b₀`, `b₁`: the
  period; `Δs`: the sync delay; `Δw`: the catch-up delay.

Read aloud: the period's trace premises and the catch-up promise outside the period give `hDelT`. -/
theorem delT_of_catchUp (U : UniformSchedule M.toSlotLayout)
    {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x)
    {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) {GST s : ℕ} {B : Block V} {b₀ b₁ : ℕ}

    (hSync : x.SynchronyFromWakeOutside A (Δ S) ΔRedeliver GST (releaseOf M S.C) acObject b₀ b₁)
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C (s + 1))
    -- the period starts at or after the hand-over update, is an interval, and ends, with its recovery, by the
    -- vote time of slot `s + k` (the period's bundle `AsyncHypsOfChainBlockGSTBeforeVotes`, T-RC9-1)
    (hb₀ : M.supportCutoff S.C (s + 1) ≤ b₀) (hb : b₀ ≤ b₁)
    (hb₁ : b₁ + max (Δ S) Δs ≤ M.voteTime S.C (s + S.C.k))
    {Δw : ℕ} (hΔw : Δw ≤ max (Δ S) Δs)
    (hCatch : x.CatchUpOnWakeOutside A Δw ΔRedeliver GST (releaseOf M S.C) acObject b₀ b₁) :
    DelTLine M S A x s B b₀ b₁ Δs := by
  -- `delT_of_promises` at the delay `Δ S`, the catch-up premise read at the restart's own deadline, at most
  -- the later of the two
  exact (delT_of_promises M F U) R E hSkew hRedeliver hΔs le_rfl hΔw hSync
    (fun i k v sm t keep c k' c' hsend hok hk hik hc' hkk' hk' hcc' hact hrel => by
      have hc'' : max (GoldilocksCorrectness.Statements.AbstractTrace.deadlineOutsideR (Δ S) GST b₀ b₁
          (x.time (i + 1))) (GoldilocksCorrectness.Statements.AbstractTrace.deadlineOutsideR Δw GST b₀ b₁
          (x.time k)) = c := Option.some.inj hc'
      have h3 : GoldilocksCorrectness.Statements.AbstractTrace.deadlineOutsideR Δw GST b₀ b₁ (x.time k) ≤ c :=
        hc'' ▸ le_max_right _ _
      exact GoldilocksCorrectness.Statements.AbstractTrace.Trace.CatchUpOnWakeBy.apply_tick hCatch hsend hok hk
        hik hkk' hk' (le_trans h3 hcc') hact hrel)
    hParent hGST hb₀ hb hb₁

/-- **The line `hDelT` at the catch-up delay `Δ S`** (Goldilocks's own catch-up premise today):
`delT_of_catchUp` at `Δw = Δ S`.

The variables: as `delT_of_catchUp`'s, with the catch-up delay `Δ S`.

Read aloud: the period's trace premises and the catch-up promise within one delay give `hDelT`. -/
theorem delT_of_catchUp_Δ (U : UniformSchedule M.toSlotLayout)
    {S : Setup V} {A : Activity V} {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x)
    {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) {GST s : ℕ} {B : Block V} {b₀ b₁ : ℕ}

    (hSync : x.SynchronyFromWakeOutside A (Δ S) ΔRedeliver GST (releaseOf M S.C) acObject b₀ b₁)
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C (s + 1))
    -- the period starts at or after the hand-over update, is an interval, and ends, with its recovery, by the
    -- vote time of slot `s + k` (the period's bundle `AsyncHypsOfChainBlockGSTBeforeVotes`, T-RC9-1)
    (hb₀ : M.supportCutoff S.C (s + 1) ≤ b₀) (hb : b₀ ≤ b₁)
    (hb₁ : b₁ + max (Δ S) Δs ≤ M.voteTime S.C (s + S.C.k))
    (hCatch : x.CatchUpOnWakeOutside A (Δ S) ΔRedeliver GST (releaseOf M S.C) acObject b₀ b₁) :
    DelTLine M S A x s B b₀ b₁ Δs :=
  (delT_of_catchUp M F U) R E hNet hSkew hRedeliver hΔs hSync hParent hGST hb₀ hb hb₁ (le_max_left _ _) hCatch

end GoldilocksCorrectness.Record.Proofs.Executions
