module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.PeriodEntryDelivery
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89CountJ
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89Stability
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.PhaseKit
public import GoldilocksCorrectness.Proofs.Routines.WalkEnd
public import Mathlib.Tactic.Ring
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ChainStateOf
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.FGStateReaders
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ForkChoiceFacts
public import GoldilocksCorrectness.Proofs.Executions.PeriodEntryDelivery
public import GoldilocksCorrectness.Proofs.Executions.Lemma89CountJ
public import GoldilocksCorrectness.Proofs.Executions.Lemma89Stability
public import GoldilocksCorrectness.Proofs.Executions.PhaseKit
public import GoldilocksCorrectness.Proofs.Routines.ChainStateOf
public import GoldilocksCorrectness.Proofs.Routines.FGStateReaders
public import GoldilocksCorrectness.Proofs.Routines.ForkChoiceFacts
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# PeriodJustifiedPast, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/PeriodJustifiedPast.lean`, over a model `M`
whose facts `F` hold, for an execution `x` of `protocolOf M S`: a justification past the hand-over
block `B` held by an honest active voter of slot `σ` reaches every honest active voter of the timely
slot `σ + 1` whose finalized block is `B` or an ancestor of `B`, before its vote. The page's
routine-level theorems are the facts' fields or have their twins in phase A.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff viewFreeze
  dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_le_supportCutoff one_le_Δ slotStart_eq
  supportCutoff_eq viewFreeze_eq voteTime_eq voteTime_mono)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor hMax le_hMax IsEntry VoterTreeAt JustifiedInTree AnchorAt)
open GoldilocksCorrectness.Record.Statements.Routines (CachesCompatibleWith)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans ancestorEq_compatible
  compatible_iff compatible_of_ancestorEq_compatible ghost_mem_tree_or_eq deepest?_mem)

variable {V : Type} [DecidableEq V] [Fintype V]
variable (M : GoldilocksModel V) (F : Facts M)
include F

-- An index `x[i]` into an execution has the valid-index predicate `fun _ _ => True`; this rule,
-- local to the file, proves it at once.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- `omega` after the `abbrev`s `Height` and `Slot` are unfolded. -/
local macro "omega_nat" : tactic =>
  `(tactic| ((try dsimp only) <;> (try unfold Height at *) <;> (try unfold Slot at *) <;> omega))

/-! ## The viable heads of a state justified past `B` -/

/-! ## The viable tree, the root of the fork choice, the anchor, the walk -/

/-! ## The vote of a state justified past `B` -/

/-! ## The vote descends from the voter's finalized block -/

/-! ## The spread of a justification past `B` -/

/-- **A block an honest validator holds at its tick is in a receiver's tree at its tick, the sync fact read at a
real time.** The twin of `block_at_tick_of_held_tick` (`ReadingPoints.lean`) for any deadline and any sync fact, with
the window's start a real time `a` at or before the holder's tick `kU` (the read Lemma 12's per-voter form takes,
`lem12_vote_held_at_tick_core_until`): the holder's finalized block at its last step before `a` is then an ancestor of
its finalized block at `kU`, so the premise `hFa` of `block_at_tick_of_held_tick` follows from `hFU`.

A proof-page helper for `justified_past_spreads`.

Why: as `block_at_tick_of_held_tick`. `u` relayed `D` when it entered its tree (`tree_block_relayed_entry`), before
`kU`. A relay at a real time at least `a` is delivered before `kR` (`delivered`, its deadline `hdl`); a relay before
`a` makes `u` serve `D` at its last step before `a` (`exists_step_before_real`), and the sync fact read at `a`
delivers it before `kR`, or `w` serves it already. The re-delivery premise comes from `w`'s tick to `c₂`
(`redeliver_before_of_tick`); the delivered block enters `w`'s tree (`mem_tree_of_admitted_delivery`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`, `R`, `E`: the setup, the activity, the execution, its facts and the environment's facts with the
  deadline `deadline`; `Sy`: the sync fact with the sync deadline `sync` and the holder's online time
  `ΔHolderOnline`; `cu`, `kU`: the clock value and the step of `u`'s tick; `a`: the window's start; `c`, `kR`: the
  clock value and the step of `w`'s tick; `c₂`, `k₂`: those of `w`'s earlier tick; `u`: the holder; `w`: the
  receiver; `D`: the block.

Read aloud: a block an honest holder has at its tick to `cu`, compatible with its finalized block there, is in every
receiver's tree at its tick to `c`, when the receiver is up from a real time `a` at or before the holder's tick, the
holder is up from `a` to the sync delay after the clock value `⌈a⌉₊`, and the receiver's finalized block is
compatible with the block. -/
theorem block_at_tick_of_held_tick_real (U : UniformSchedule M.toSlotLayout)
    {S : Setup V} {A : Activity V} [RootOrder]
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x)
    {deadline} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : GoldilocksCorrectness.Statements.AbstractTrace.EnvFactsBy A x ΔClockAhead ΔClockBehind deadline
      (releaseOf M S.C) ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {sync : V → SignedMsg V (NamedObject V) → ℕ → Option ℕ} {ΔHolderOnline : ℝ}
    (Sy : GoldilocksCorrectness.Statements.AbstractTrace.SyncedWithinBy A x (servesMin M S.C) acObject
      (releaseOf M S.C) ΔRedeliver sync ΔHolderOnline)
    (hHO : 0 ≤ ΔHolderOnline)
    {cu kU c kR c₂ k₂ : ℕ} {u w : V} {D : Block V} {a : ℝ}
    (hRoots : RootsNameBlocksUntil M A x (x.time kR)) (hParent : ParentHeldAtDelivery M x)
    -- `u` holds `D` at its tick `kU` to `cu`, at a real time at least `a`, compatible with its finalized block
    (hkU : x.lbl kU = Event.tick u cu) (haU : a ≤ x.time kU)
    (hD : D ∈ (x.st kU u).tree) (hFU : (x.st kU u).finalized.compatible D = true) (hg : D ≠ Block.genesis)
    -- a message on the wire at a real time at most `ΔClockBehind` after `cu` is due `ΔClockAhead` before `c`
    (hdl : ∀ (sm : SignedMsg V (NamedObject V)) (t : ℝ), t ≤ (cu : ℝ) + ΔClockBehind →
      ∃ d : ℝ, deadline sm t = some d ∧ d + ΔClockAhead ≤ c)
    -- the sync deadline at the clock value `⌈a⌉₊` is at most `c`
    (hsync : ∀ sm, ∃ d : ℕ, sync w sm ⌈a⌉₊ = some d ∧ d ≤ c)
    -- `u` is active in every configuration in force at a real time of `[a, ⌈a⌉₊ + ΔHolderOnline]`
    (hu₀ : u ∈ A.activeThroughout x a ((⌈a⌉₊ : ℝ) + ΔHolderOnline))
    -- `w` ticks to `c` at `kR`, active at every step from `a` up to `kR`
    (hkR : x.lbl kR = Event.tick w c) (hwin : ∀ i : ℕ, a ≤ x.time i → i ≤ kR → w ∈ A.active i)
    (hcu : (cu : ℝ) + ΔClockBehind < (c : ℝ) - ΔClockAhead)
    -- `w` ticked to `c₂`, at least the start of `D`'s slot, early enough for a re-delivery before `kR`
    (hk₂ : x.lbl k₂ = Event.tick w c₂)
    (hgap : (c₂ : ℝ) + ΔClockBehind + ΔRedeliver ≤ (c : ℝ) - ΔClockAhead)
    (hDc₂ : M.slotStart S.C D.slot ≤ c₂)
    (hFw : (x.st kR w).finalized.compatible D = true) :
    D ∈ (x.st kR w).tree := by
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hR0 : (0 : ℝ) ≤ ΔRedeliver := by positivity
  have hu : u ∉ A.corrupted kU := E.not_mem_corrupted_of_tick hkU
  have hwkR : w ∉ A.corrupted kR := E.not_mem_corrupted_of_tick hkR
  have hkRt := (E.tick_active kR w c hkR).2.1
  have hkUt := (E.tick_active kU u cu hkU).2.2
  have hc₂c : c₂ ≤ c := by
    have : (c₂ : ℝ) ≤ c := by linarith
    exact_mod_cast this
  obtain ⟨ie, hie, hsende, hhone, -, hie1⟩ := (tree_block_relayed_entry M F) x R E hD hg
  have hsk : kU < kR := (lt_of_time_lt M) x R (by linarith)
  have hprem := redeliver_before_of_tick M F R E (r := M.slotStart S.C D.slot) hk₂ hkR hgap hDc₂
  by_cases hlate : a ≤ x.time (ie + 1)
  · -- the relay from `a` on: the delivery promise
    have hiek : ie < kR := by omega
    have hieT : x.time (ie + 1) ≤ x.time kU := htime (show ie + 1 ≤ kU by omega)
    obtain ⟨d, hd, hdle⟩ := hdl ⟨u, NamedObject.block D⟩ (x.time (ie + 1)) (by linarith)
    obtain ⟨j, -, hjk, hlj, hadm, -⟩ := E.delivered ie kR w ⟨u, NamedObject.block D⟩ c d ⟨hsende, hhone⟩
      trivial hkR hiek (fun j h1 h2 => hwin j (le_trans hlate (htime h1)) h2) hd (by linarith)
      (fun r j₀ k₁ t₁ hr _ _ hnr hjk₁ _ hlk₁ _ hfirst => by
        have hr' : M.slotStart S.C D.slot = r := Option.some.inj hr
        subst hr'
        exact hprem j₀ k₁ t₁ hnr hjk₁ hlk₁ hfirst)
    exact (mem_tree_of_admitted_delivery M F U) R E hRoots hParent hu (htime hsk.le) hD hlj
      (htime hjk.le) (hadm _ rfl (by omega)) hjk hwkR hFw
  · -- the relay before `a`: `u` serves `D` at its last step before `a`, and the sync fact read at `a`
    push_neg at hlate
    have h0 : (0 : ℝ) ≤ x.time (ie + 1) := (time_nonneg M) x R (ie + 1)
    obtain ⟨kb, hk1, hk2⟩ := (exists_step_before_real M F) R E (lt_of_le_of_lt h0 hlate)
    have hiek : ie < kb := by
      have := (lt_of_time_lt M) x R (show x.time (ie + 1) < x.time (kb + 1) by linarith)
      omega
    have hkbU : kb < kU := (lt_of_time_lt M) x R (by linarith)
    have hceil := Nat.le_ceil a
    have hvk : u ∈ A.active kb := Activity.mem_activeThroughout.1 hu₀ _ (by linarith) hk2
    have hserve : servesMin M S.C (x.st kb u) (x.clockValue kb u) (NamedObject.block D) :=
      ⟨(mem_T_mono M F) x R E u (show ie + 1 ≤ kb by omega) hie1,
        GoldilocksCorrectness.Proofs.Routines.compatible_of_ancestorEq_compatible
          ((F_ancestorEq_of_le M F) x R E u hkbU.le) hFU, hg⟩
    obtain ⟨d, hd, hdle⟩ := hsync ⟨u, NamedObject.block D⟩
    rcases Sy a kb u w (NamedObject.block D) d c kR hk1 hk2 hvk hserve trivial
        (fun j h1 h2 => Activity.mem_activeThroughout.1 hu₀ j h2 (le_trans h1 (htime (Nat.le_succ j))))
        hd hkR hdle (fun j h1 h2 => hwin j h1 h2)
        (fun r j₀ k₁ t₁ hr _ hnr hjk₁ _ hlk₁ _ hfirst => by
          have hr' : M.slotStart S.C D.slot = r := Option.some.inj hr
          subst hr'
          exact hprem j₀ k₁ t₁ hnr hjk₁ hlk₁ hfirst)
      with hw | ⟨j, k'', hk''j, hk''t, hk''o, hlj, hjk, hadm, -⟩
    · exact (mem_T_mono M F) x R E w (show kb ≤ kR by omega) hw.1
    · have hk''U : k'' ≤ kU := ((lt_of_time_lt M) x R (show x.time k'' < x.time kU by linarith)).le
      have hk''T : x.time k'' ≤ x.time kR := htime (show k'' ≤ kR by omega)
      exact (mem_tree_of_admitted_delivery M F U) R E hRoots hParent
        (fun h => hu (E.corrupted_mono k'' kU hk''U h)) hk''T hk''o.1
        hlj (htime hjk.le) (hadm _ rfl (by omega)) hjk hwkR hFw

/-- **A justification past `B` spreads in one delay.** The proof; the audited statement is in
`Statements/Executions/PeriodJustifiedPastStatements.lean`. Every state is read at the validator's own
tick. `w`'s caches at its tick to `M.voteTime S.C σ` are witnessed by a held block `D`
(`cachesWitnessed_of_exec`) with `w`'s justified block and justification height; `B ⪯ J_w` (compatible
and higher) and `J_w ⪯ D` (`chainStateOf_J_spec`), so `B ⪯ D`. `D` reaches `u` by its tick to
`M.supportCutoff S.C σ` when the previous votes were due before the period, and by its tick to
`M.viewFreeze S.C σ` when they were due after it (`block_at_tick_of_held_tick`); `mem_T_mono` carries it
to `u`'s tick to `M.voteTime S.C (σ + 1)`. `u`'s finalized block there is an ancestor of `B`, so of `D`,
and Lemma 57's cache bound (`h_j_of_mem_T_of_exec`) gives `(M.chainStateOf S.C D).h_j ≤ h_j(u)`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `P`: the hypotheses; `σ`: the slot of `w`'s vote; `w`: the voter justified past `B`; `u`: the
  voter of slot `σ + 1`.
- `T`: the time up to which `P`'s premises are read; the proof reads neither premise.

Read aloud: when an honest active voter of slot `σ` has justified a block higher than `B`, every
honest active voter of the timely slot `σ + 1` whose finalized block is `B` or an ancestor of `B`
has too, at its tick to its vote time. -/
theorem justified_past_spreads (U : UniformSchedule M.toSlotLayout)
    {S : Setup V} {A : Activity V} [RootOrder]
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind tW : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) {GST s : ℕ} {B : Block V}
      {H t₀ anchor tAwakeEnd b₀ b₁ Δs_F T : ℕ}
    (P : AsyncHypsOfChainBlockGSTBeforeVotesUntil M S A x GST s B H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F T (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet tW)
    (σ : ℕ) (w u : V)
    (hRoots : RootsNameBlocksUntil M A x (M.voteTime S.C (σ + 1)))
    (hσ : s + 1 ≤ σ) (hgood : ¬ VotesOwedInPeriod M S Δs b₀ b₁ (σ + 1))
    (hw : w ∈ honestActiveAt M S A x σ)
    (hCw : CachesCompatibleWith M S B H (x.tickInput w (M.voteTime S.C σ)))
    (hjw : (M.chainStateOf S.C B).h + 1 ≤ (x.tickInput w (M.voteTime S.C σ)).justifiedHeight)
    (hu : u ∈ honestActiveAt M S A x (σ + 1))
    (hFu : (x.tickInput u (M.voteTime S.C (σ + 1))).finalized.AncestorEq B) :
    (M.chainStateOf S.C B).h + 1 ≤
      (x.tickInput u (M.voteTime S.C (σ + 1))).justifiedHeight := by
  -- `w`'s caches at its tick `kU` to the vote time of `σ` are witnessed by a held block `D` with `B ⪯ D`; `D` reaches
  -- `u` by its tick to `c` (the support cutoff of `σ` when the previous votes were due before the period, the view
  -- freeze of `σ` when after it), the sync fact read at the real time `a`, the earlier of `vt(σ) − ΔClockAhead` and
  -- `cut(σ) − max (2 * Δ S) Δs` (`block_at_tick_of_held_tick_real`), so at or before `w`'s tick; then Lemma 57's bound
  have hΔ := one_le_Δ S
  have hk := S.C.k_ge_two
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hR0 : (0 : ℝ) ≤ ΔRedeliver := by positivity
  have hN0 : (0 : ℝ) ≤ ΔNet := by positivity
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  -- the slot times of `σ`, `σ + 1`, `σ + 2`, as real numbers
  have hssn : ∀ n : ℕ, M.slotStart S.C n = 4 * Δ S * n := fun n =>
    (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S n
  have hvtn : ∀ n : ℕ, M.voteTime S.C n = M.slotStart S.C n + Δ S := fun n =>
    (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S n
  have hscn : ∀ n : ℕ, M.supportCutoff S.C n = M.voteTime S.C n + Δ S := fun n =>
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S n
  have hvfσ : M.viewFreeze S.C σ = M.slotStart S.C σ + 3 * Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_eq M.toSlotLayout F.sched U) S σ
  have hss1 : M.slotStart S.C (σ + 1) = M.slotStart S.C σ + 4 * Δ S := by
    rw [hssn, hssn, Nat.mul_add, Nat.mul_one]
  have hss2 : M.slotStart S.C (σ + 1 + 1) = M.slotStart S.C σ + 8 * Δ S := by
    rw [hssn, hssn]; ring
  have hsσR : ((M.slotStart S.C σ : ℕ) : ℝ) = 4 * Δ S * (σ : ℝ) := by rw [hssn]; push_cast; ring
  have hvtR : ((M.voteTime S.C σ : ℕ) : ℝ) = 4 * Δ S * (σ : ℝ) + Δ S := by rw [hvtn, hsσR.symm]; push_cast; ring
  have hcR : ((M.supportCutoff S.C σ : ℕ) : ℝ) = 4 * Δ S * (σ : ℝ) + 2 * Δ S := by
    rw [hscn, hvtn, ← hsσR]; push_cast; ring
  have hvfR : ((M.viewFreeze S.C σ : ℕ) : ℝ) = 4 * Δ S * (σ : ℝ) + 3 * Δ S := by
    rw [hvfσ, ← hsσR]; push_cast; ring
  have hvt1R : ((M.voteTime S.C (σ + 1) : ℕ) : ℝ) = 4 * Δ S * (σ : ℝ) + 5 * Δ S := by
    rw [hvtn, hss1, ← hsσR]; push_cast; ring
  have hc1R : ((M.supportCutoff S.C (σ + 1) : ℕ) : ℝ) = 4 * Δ S * (σ : ℝ) + 6 * Δ S := by
    rw [hscn, hvtn, hss1, ← hsσR]; push_cast; ring
  have hc2R : ((M.supportCutoff S.C (σ + 1 + 1) : ℕ) : ℝ) = 4 * Δ S * (σ : ℝ) + 10 * Δ S := by
    rw [hscn, hvtn, hss2, ← hsσR]; push_cast; ring
  have hdw0 := duty_window_start_real S σ
  have hdw1 := duty_window_start_real S (σ + 1)
  push_cast at hdw0 hdw1
  have hdw1' : ((duty_window_start S.C (σ + 1) : ℤ) : ℝ) = 4 * Δ S * (σ : ℝ) + 5 * Δ S - 4 * Δ S * S.C.k := by
    rw [hdw1]; ring
  have hkR8 : (8 : ℝ) * Δ S ≤ 4 * Δ S * S.C.k := by
    have : 4 * Δ S * 2 ≤ 4 * Δ S * S.C.k := Nat.mul_le_mul_left _ hk
    exact_mod_cast (by omega : 8 * Δ S ≤ 4 * Δ S * S.C.k)
  have hmxs : (Δs : ℝ) ≤ (max (Δ S) Δs : ℝ) := le_max_right _ _
  have hmxΔ : (Δ S : ℝ) ≤ (max (Δ S) Δs : ℝ) := le_max_left _ _
  -- the network has recovered by the support cutoff of `σ`
  have hGSTσ : GST + max (Δ S) Δs ≤ M.supportCutoff S.C σ := le_trans P.hGST
    ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S (by omega))
  have hgood' : M.supportCutoff S.C σ ≤ b₀ ∨ b₁ + max (Δ S) Δs ≤ M.supportCutoff S.C σ + Δ S := by
    unfold VotesOwedInPeriod at hgood
    simp only [Nat.add_sub_cancel] at hgood
    omega
  -- the read time `rt := cut(σ) − max (2 * Δ S) Δs` and the window's start `a`
  set rt : ℕ := M.supportCutoff S.C σ - max (2 * Δ S) Δs with hrt
  have hm1 := le_max_left (Δ S) Δs
  have hm2 := le_max_right (Δ S) Δs
  have hm3 := le_max_left (2 * Δ S) Δs
  have hm4 := le_max_right (2 * Δ S) Δs
  have hrtΔs : rt + Δs ≤ M.supportCutoff S.C σ := by omega
  have hrtR : ((M.supportCutoff S.C σ : ℕ) : ℝ) ≤ (rt : ℝ) + ((max (2 * Δ S) Δs : ℕ) : ℝ) := by
    exact_mod_cast (by omega : M.supportCutoff S.C σ ≤ rt + max (2 * Δ S) Δs)
  have hstart_rt : ((duty_window_start S.C (σ + 1) : ℤ) : ℝ) + ΔClockBehind < (rt : ℝ) := by
    rw [hdw1']
    rw [hcR] at hrtR
    rcases max_cases (2 * Δ S) Δs with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] at hrtR <;> push_cast at hrtR <;> linarith
  have hstart_vt : ((duty_window_start S.C (σ + 1) : ℤ) : ℝ) + ΔClockBehind <
      ((M.voteTime S.C σ : ℕ) : ℝ) - ΔClockAhead := by
    rw [hdw1', hvtR]; linarith
  set a : ℝ := min (((M.voteTime S.C σ : ℕ) : ℝ) - ΔClockAhead) (rt : ℝ) with ha
  have hart : a ≤ (rt : ℝ) := min_le_right _ _
  have hstart : ((duty_window_start S.C (σ + 1) : ℤ) : ℝ) + ΔClockBehind < a := lt_min hstart_vt hstart_rt
  have hceil : ⌈a⌉₊ ≤ rt := Nat.ceil_le.2 hart
  have hceilR : ((⌈a⌉₊ : ℕ) : ℝ) ≤ (rt : ℝ) := by exact_mod_cast hceil
  have hrtΔsR : (rt : ℝ) + Δs ≤ ((M.supportCutoff S.C σ : ℕ) : ℝ) := by exact_mod_cast hrtΔs
  -- `w`'s tick `kU` to the vote time of `σ`, at a real time at least `a`
  have hwW := (honestActiveAt_window M F) S A σ w E hw
  have hwV : w ∈ A.activeThroughoutToTick x (duty_window_start S.C σ) (M.voteTime S.C σ) :=
    (mem_activeThroughoutToTick_of_inside M F) R E hwW (by rw [hvtn]; omega)
      (by rw [hdw0, hvtR]; linarith) (by rw [hvtR, hc1R]; linarith)
  obtain ⟨kU, hkU, -⟩ := (tick_window_of_activeThroughoutToTick_int M) x R E hwV
    (t₀ := ((M.voteTime S.C σ : ℕ) : ℝ) - ΔClockAhead) (by rw [hdw0, hvtR]; linarith)
  have hkUt := (E.tick_active kU w _ hkU).2
  have haU : a ≤ x.time kU := le_trans (min_le_left _ _) hkUt.1
  have hwkU : w ∉ A.corrupted kU := E.not_mem_corrupted_of_tick hkU
  have hti_w : x.tickInput w (M.voteTime S.C σ) = x.st kU w := by
    unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hkU]
  rw [hti_w] at hCw hjw
  -- `w` holds from `a` to the sync delay after `⌈a⌉₊`
  have hu₀ : w ∈ A.activeThroughout x a (((⌈a⌉₊ : ℕ) : ℝ) + Δs) :=
    (mem_activeThroughout_of_mem_activeThroughoutToTick_real M F) R E hwW
      (by rw [hdw0]; rw [hdw1'] at hstart; linarith) (by rw [hc1R]; rw [hcR] at hrtΔsR; linarith)
  -- `u`'s ticks: to the vote time of `σ + 1` (`i₀`), and its window from the duty window's start of `σ + 1`
  have hu1 : u ∈ A.activeThroughoutToTick x (duty_window_start S.C (σ + 1)) (M.supportCutoff S.C (σ + 1)) :=
    (mem_activeThroughoutToTick_of_inside M F) R E ((honestActiveAt_window M F) S A (σ + 1) u E hu)
      (by rw [hscn, hvtn]; omega) (by rw [hdw1', hc1R]; linarith) (by rw [hc1R, hc2R]; linarith)
  have hutick : ∀ c' : ℕ, M.voteTime S.C σ ≤ c' → (c' : ℝ) ≤ 4 * Δ S * (σ : ℝ) + 5 * Δ S →
      ∃ k : ℕ, x.lbl k = Event.tick u c' ∧ ∀ i : ℕ, a ≤ x.time i → i ≤ k → u ∈ A.active i := by
    intro c' hc'v hc'R
    have hc'vR : ((M.voteTime S.C σ : ℕ) : ℝ) ≤ (c' : ℝ) := by exact_mod_cast hc'v
    have hu' : u ∈ A.activeThroughoutToTick x (duty_window_start S.C (σ + 1)) c' :=
      (mem_activeThroughoutToTick_of_inside M F) R E hu1 (by rw [hvtn] at hc'v; omega)
        (by linarith) (by rw [hc1R]; linarith)
    exact (tick_window_of_activeThroughoutToTick_int M) x R E hu' hstart
  -- `u`'s tick `i₀` to the vote time of `σ + 1`; its ticks to clock values before it come before `i₀`
  obtain ⟨i₀, hi₀, -⟩ := hutick (M.voteTime S.C (σ + 1)) (by rw [hvtn, hvtn, hss1]; omega) (le_of_eq hvt1R)
  have hti_u : x.tickInput u (M.voteTime S.C (σ + 1)) = x.st i₀ u := by
    unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hi₀]
  rw [hti_u] at hFu ⊢
  have hbefore : ∀ (k c' : ℕ), x.lbl k = Event.tick u c' → c' < M.voteTime S.C (σ + 1) → k ≤ i₀ := by
    intro k c' hk hc'
    by_contra hcon
    have hle := E.clock_mono i₀ k u _ c' (by omega) (E.not_mem_corrupted_of_tick hk) (Or.inl hi₀) (Or.inl hk)
    omega
  have hRootsk : ∀ (k c' : ℕ), x.lbl k = Event.tick u c' → (c' : ℝ) ≤ 4 * Δ S * (σ : ℝ) + 3 * Δ S →
      RootsNameBlocksUntil M A x (x.time k) := by
    intro k c' hk hc'
    have h1 := (E.tick_active k u _ hk).2.2
    exact (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M)
      (show x.time k ≤ ((M.voteTime S.C (σ + 1) : ℕ) : ℝ) by rw [hvt1R]; linarith) hRoots
  -- the block `D` witnessing `w`'s caches at `kU`, with `B ⪯ D`
  obtain ⟨⟨D, hDT, hJD, hhD⟩, -, -⟩ := (cachesWitnessed_of_exec M F) S A x R E kU w
  obtain ⟨-, hJB, -, hJh, hFJ⟩ := hCw
  have hBJ : B.AncestorEq (x.st kU w).justified := by
    rcases hJB with h | h
    · exfalso
      have hm := (GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_height_mono M F) S.C h
      omega_nat
    · exact h
  have hJD' : (x.st kU w).justified.AncestorEq D := by
    rw [hJD]; exact ((GoldilocksCorrectness.Record.Proofs.Routines.chainStateOf_J_spec M F) S.C D).1
  have hBD : B.AncestorEq D := ancestorEq_trans hBJ hJD'
  have hFuD : (x.st i₀ u).finalized.AncestorEq D := ancestorEq_trans hFu hBD
  suffices hDu : D ∈ (x.st i₀ u).tree by
    have h := (GoldilocksCorrectness.Record.Statements.Executions.h_j_of_mem_T_of_exec M F) S A x R E i₀ u D
      hDu hFuD
    omega_nat
  by_cases hg : D = Block.genesis
  · rw [hg]; exact (GoldilocksCorrectness.Record.Statements.Executions.genesis_mem_T_of_exec M F) S A x R E _ u
  have hFU : (x.st kU w).finalized.compatible D = true :=
    (compatible_iff _ _).2 (Or.inl (ancestorEq_trans hFJ hJD'))
  -- `D`'s slot is at most `σ`
  have hDslot : M.slotStart S.C D.slot ≤ M.voteTime S.C σ := by
    have hcvU : x.clockValue kU w ≤ M.voteTime S.C σ := E.clockValue_le_of_set hwkU (Or.inl hkU)
    have h := (slot_le_clockValue_of_mem_tree M F) R E hwkU hDT
    have hsl : M.slot S.C (M.voteTime S.C σ) = S.C.slot ((M.voteTime S.C σ : ℕ) : Int) := by
      rw [(GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U),
        GoldilocksCorrectness.Proofs.Routines.slot_natCast]
    have hslotv : S.C.slot ((M.voteTime S.C σ : ℕ) : Int) = σ :=
      hsl ▸ (GoldilocksCorrectness.Record.Proofs.Routines.slot_eq_of_mem M.toSlotLayout F.sched) S
        (by rw [hvtn]; omega) (by rw [hvtn, hss1]; omega)
    have hDσ : D.slot ≤ σ := by
      rw [← hslotv]
      exact h.trans (GoldilocksCorrectness.Proofs.Routines.slot_mono_int S (by exact_mod_cast hcvU))
    have := Nat.mul_le_mul_left (4 * Δ S) hDσ
    rw [hssn, hvtn, hssn]; omega
  have hvfc : M.viewFreeze S.C σ = M.supportCutoff S.C σ + Δ S := by rw [hvfσ, hscn, hvtn]; ring
  have hGR : (GST : ℝ) + Δ S ≤ ((M.supportCutoff S.C σ : ℕ) : ℝ) := by
    exact_mod_cast (by omega : GST + Δ S ≤ M.supportCutoff S.C σ)
  have hNetR := hNet
  rcases hgood' with hb | hb
  · -- before the period: the network up to the support cutoff of `σ`, `u`'s tick to it
    obtain ⟨kR, hkR, hwinR⟩ := hutick (M.supportCutoff S.C σ) (by rw [hscn]; omega) (by rw [hcR]; linarith)
    obtain ⟨k₂, hk₂, -⟩ := hutick (M.voteTime S.C σ) le_rfl (by rw [hvtR]; linarith)
    have hkRi₀ : kR ≤ i₀ := hbefore kR _ hkR (by rw [hscn, hvtn, hvtn, hss1]; omega)
    have hDR : D ∈ (x.st kR u).tree := (block_at_tick_of_held_tick_real M F U) R
      ((envFactsBy_of_synchronyFromWakeUpTo M) x E (((synchronyFromWakeUpTo_of_outside M) P.hSync).mono M hb))
      (P.Sy.upTo.mono hb) (Nat.cast_nonneg _) (hRootsk kR _ hkR (by rw [hcR]; linarith)) P.hParent hkU haU hDT
      hFU hg
      (fun sm t ht => by
        have hmx : max t (GST : ℝ) ≤ ((M.voteTime S.C σ : ℕ) : ℝ) + ΔClockBehind :=
          max_le ht (by rw [hvtR]; rw [hcR] at hGR; linarith)
        refine ⟨_, GoldilocksCorrectness.Statements.AbstractTrace.deadlineUpTo_eq_some.2 ⟨?_, rfl⟩, ?_⟩ <;>
          (push_cast; rw [hcR]; rw [hvtR] at hmx; linarith))
      (fun sm => by
        refine ⟨_, GoldilocksCorrectness.Statements.AbstractTrace.deadlineUpTo_eq_some.2 ⟨?_, rfl⟩, ?_⟩ <;>
          (rcases max_cases ⌈a⌉₊ GST with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> omega))
      hu₀ hkR hwinR (by rw [hvtR, hcR]; linarith) hk₂ (by rw [hvtR, hcR]; linarith) hDslot
      ((compatible_iff _ _).2 (Or.inl (ancestorEq_trans ((F_ancestorEq_of_le M F) x R E u hkRi₀) hFuD)))
    exact (mem_T_mono M F) x R E u hkRi₀ hDR
  · -- after the period: the synchronous network from `max b₁ GST`, `u`'s tick to the view freeze of `σ`
    obtain ⟨kR, hkR, hwinR⟩ := hutick (M.viewFreeze S.C σ) (by rw [hvfc, hscn]; omega) (by rw [hvfR]; linarith)
    obtain ⟨k₂, hk₂, -⟩ := hutick (M.supportCutoff S.C σ) (by rw [hscn]; omega) (by rw [hcR]; linarith)
    have hkRi₀ : kR ≤ i₀ := hbefore kR _ hkR (by rw [hvfc, hscn, hvtn, hvtn, hss1]; omega)
    have EB : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver (max b₁ GST) (releaseOf M S.C) acObject
        GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks :=
      (envFactsBy_of_synchronyFromWakeBy M) x E ((synchronyFromWake_of_outside_after M) P.hSync)
    have hbG : max b₁ GST + Δ S ≤ M.viewFreeze S.C σ := by
      rcases max_cases b₁ GST with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> omega
    have hbGR : ((max b₁ GST : ℕ) : ℝ) + Δ S ≤ ((M.viewFreeze S.C σ : ℕ) : ℝ) := by exact_mod_cast hbG
    -- the sync fact after the period (`syncedWithin_after_period_of_outside`, written out: that page imports this one)
    have SyB : GoldilocksCorrectness.Statements.AbstractTrace.SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C)
        ΔRedeliver Δs (max b₁ GST) :=
      GoldilocksCorrectness.Statements.AbstractTrace.SyncedWithinBy.of_le (fun _ _ t d' h => ⟨_, rfl, by
        have h' : max t (max b₁ GST) + Δs = d' := Option.some.inj h
        rw [← h']
        exact GoldilocksCorrectness.Statements.AbstractTrace.deadlineOutside_le_after Δs GST b₀ b₁ t⟩) P.Sy
    have hDR : D ∈ (x.st kR u).tree := (block_at_tick_of_held_tick_real M F U) R EB SyB (Nat.cast_nonneg _)
      (hRootsk kR _ hkR (by rw [hvfR])) P.hParent hkU haU hDT hFU hg
      (fun sm t ht => by
        refine ⟨_, rfl, ?_⟩
        have hmx : max t ((max b₁ GST : ℕ) : ℝ) ≤ ((M.viewFreeze S.C σ : ℕ) : ℝ) - ΔNet - ΔClockAhead :=
          max_le (by rw [hvfR]; rw [hvtR] at ht; linarith) (by linarith)
        linarith)
      (fun sm => by
        refine ⟨_, rfl, ?_⟩
        have hmx : max ⌈a⌉₊ (max b₁ GST) ≤ M.viewFreeze S.C σ - Δs :=
          max_le (by omega) (max_le (by omega) (by omega))
        omega)
      hu₀ hkR hwinR (by rw [hvtR, hvfR]; linarith) hk₂ (by rw [hcR, hvfR]; linarith) (le_trans hDslot (by rw [hscn]; omega))
      ((compatible_iff _ _).2 (Or.inl (ancestorEq_trans ((F_ancestorEq_of_le M F) x R E u hkRi₀) hFuD)))
    exact (mem_T_mono M F) x R E u hkRi₀ hDR

end GoldilocksCorrectness.Record.Proofs.Executions

