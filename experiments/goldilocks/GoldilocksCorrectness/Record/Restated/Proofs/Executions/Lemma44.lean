module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma43
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma39
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma41
public import GoldilocksCorrectness.Proofs.Executions.Lemma43
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Lemma44, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma44.lean`, over a model `M` whose facts
`F` hold, for an execution `x` of `protocolOf M S`: Lemma 44, after `GST` plus `L` every two live
honest locks are compatible. The page's routine-level theorems are the facts' fields or have their
twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (t_le_of_le)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (acObject)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

variable {S : Setup V} {A : Activity V}

/-- A lock entry of `v`'s node state at its tick to the clock value `c`, live at `c` by `v`'s clock,
with `c` at or after the vote time of slot `s₁ + S.C.k`, has a deadline at least that of a lock of slot
`s₁`: it is a lock of a slot `s'` (Lemma 39) with `s₁ ≤ s'` (Lemma 41).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `x`: the execution; `s₁`: the slot; `c`: the clock value; `v`: the validator; `e`: the lock entry.

Read aloud: a lock still live at `v`'s tick to a clock value `S.C.k` slots after `s₁` was made at `s₁`
or later. -/
theorem deadline_ge_of_live_after (U : UniformSchedule M.toSlotLayout)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (s₁ c : ℕ) (v : V) (e : M.LE)
    (ht : M.voteTime S.C (s₁ + S.C.k) ≤ c)
    (he : e ∈ (x.tickInput v c).lockEntries)
    (hlive : M.is_live (x.tickInput v c) (c : Int) e = true) :
    S.C.t_ (s₁ + S.C.k) + 5 * S.C.Δ ≤ e.d := by
  obtain ⟨s', hd, -⟩ :=
    (lem39_lock_entry_provenance M F U) S A x R (x.tickStep v c) v e E he
  have hl : (c : Int) < e.d ∧ e.B ∈ (M.fg_to_ac (x.tickInput v c)).tree := by
    exact ((GoldilocksCorrectness.Record.Proofs.Routines.is_live_iff M F) _ _ _).1 hlive
  have hb := (lem41_slot_of_live_entry M F U) S s₁ s' c e hd hl.1
    ht
  rw [hd]
  exact Int.add_le_add_right (t_le_of_le S (show s₁ + S.C.k ≤ s' + S.C.k by omega)) _

/-- **Lemma 44, after `GST` plus `L`, every two live honest locks are compatible.** The proof;
the audited statement is in `Statements/Executions/HealingStatements.lean`.

Every state is read at its validator's own tick to the clock value `c`; Lemma 43,
which the proof calls, reads the same.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: from the vote time of slot `s₁ + S.C.k` on, at a clock value `c` of a slot `s` that has
started, any two lock entries held by `v` and `w` at their own ticks to `c`, live at `c` by their
clocks, the two validators active from their ticks to a clock value at most `tStart` (before the
support cutoff of slot `s − S.C.k`) up to their ticks to `c` and in the delay before the real time `c`,
are on compatible blocks, when `GST` is at most the vote time of slot `s₁` and each validator's
finalized block at its tick to `c` is compatible with the other's lock block. -/
theorem lem44_live_locks_compatible_from_GST_plus_L (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (GST s₁ s c : ℕ) (v w : V) (e_v e_w : M.LE)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (max (x.time (x.tickStep v c)) (x.time (x.tickStep w c))))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₁)
    (ht : M.voteTime S.C (s₁ + S.C.k) ≤ c)
    (hsc : M.slotStart S.C s ≤ c)
    (tStart : ℕ) (htStart : tStart < M.supportCutoff S.C (s - S.C.k))
    (hv : v ∈ A.activeThroughoutToTick x (tStart : ℤ) c)
    (hw : w ∈ A.activeThroughoutToTick x (tStart : ℤ) c)
    (hHoldV : v ∈ A.activeThroughout x ((c - Δ S : ℕ) : ℝ) (c : ℝ))
    (hHoldW : w ∈ A.activeThroughout x ((c - Δ S : ℕ) : ℝ) (c : ℝ))
    (he_v : e_v ∈ (x.tickInput v c).lockEntries)
    (hlive_v : M.is_live (x.tickInput v c) (c : Int) e_v = true)
    (he_w : e_w ∈ (x.tickInput w c).lockEntries)
    (hlive_w : M.is_live (x.tickInput w c) (c : Int) e_w = true)
    (hFwv : (x.tickInput w c).finalized.compatible e_v.B = true)
    (hFvw : (x.tickInput v c).finalized.compatible e_w.B = true) :
    e_v.B.compatible e_w.B = true :=
  (lem43_live_locks_after_GST_compatible M F U) S A x R GST s₁ s
    c v w e_v e_w E hNet hSkew hRedeliver Sy hΔs hRoots hParent hGST hsc tStart htStart hv hw hHoldV
    hHoldW he_v hlive_v ((deadline_ge_of_live_after M F U) x R E s₁ c v e_v ht he_v hlive_v) he_w
    hlive_w ((deadline_ge_of_live_after M F U) x R E s₁ c w e_w ht he_w hlive_w) hFwv hFvw

end GoldilocksCorrectness.Record.Proofs.Executions

