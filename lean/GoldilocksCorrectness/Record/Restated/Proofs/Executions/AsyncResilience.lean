module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.PeriodInductionCompat
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma90
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.AsyncHandover
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.HealedTopUpTo
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma81UpTo
public import GoldilocksCorrectness.Proofs.Executions.AsyncResilience
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# AsyncResilience, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/AsyncResilience.lean`, over a model `M`
whose facts `F` hold, for an execution `x` of `protocolOf M S`: Lemma 105 (the confirmed tip
persists through one asynchronous period, from the hand-over facts), the asynchrony top statement up
to a time `t` and read forever, and the facts they are proved from (a confirmed tip extends `B` when
the record does and the finalized block is compatible with `B`; the period's facts from the
hand-over update on; `GST` at most the vote time of slot `s + 1`). The page's routine-level theorems
are the facts' fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ Δ_F slotStart voteTime supportCutoff
  proposalWindowStart anchorCW)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slotStart_mono slot_le_of_supportCutoff_lt
  supportCutoff_eq supportCutoff_mono times_eq voteTime_eq)

open GoldilocksCorrectness.Statements.Routines (confirmedOf)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDeliveryOutside SyncedWithinOutside)

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
open GoldilocksCorrectness.Statements.Executions (OpeningsOutsideWaitsAndWindows Vocab.goldilocks
  acObject fgObject healFrontSlots)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans ancestorEq_compatible)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

-- An index `x[i]` into an execution has the valid-index predicate `fun _ _ => True`; this rule,
-- local to the file, proves it at once. No statement and no proof term changes.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

omit [RootOrder] in
/-- **The confirmed tip extends `B` when the record does and the finalized block is compatible
with `B`.** For a node state `n`: when `B` is the record `n.latestConfirmed` or an ancestor of
it, the record is in `n`'s tree, and the finalized block `n.finalized` is compatible with `B`, then
`B` is the confirmed tip `M.ac_confirmed n` or an ancestor of it.

Why: the confirmed tip is the record when the record is in the frame's tree, the finalized block
otherwise (the reader fact `ac_confirmed_eq`). In the first case the record extends `B`. In the
second the finalized block is not an ancestor of the record (else the record, held in `n.tree`,
would be in the frame's tree), so it is not `B` or an ancestor of `B` (which is an ancestor of the
record): by compatibility it is a descendant of `B`.

The landed theorem was promoted from `scratch/goldilocks_async/probe_outside_1.lean:104`.

The variables:
- `M`: the model; `F`: its facts;
- `n`: the node state; `B`: the block.

Read aloud: whether the validator is awake or asleep, its confirmed tip extends `B` as long as its
record extends `B` and its finalized block is compatible with `B`. -/
theorem preceq_confirmedOf_of_record_and_F (n : M.N) (B : Block V)
    (hrec : B.AncestorEq n.latestConfirmed) (hT : n.latestConfirmed ∈ n.tree)
    (hF : n.finalized.AncestorEq B ∨ B.AncestorEq n.finalized) :
    B.AncestorEq (M.ac_confirmed n) := by
  -- the confirmed tip is the record when the record is in the frame's tree, the finalized block otherwise (the
  -- reader fact `ac_confirmed_eq`)
  rw [F.rd.ac_confirmed_eq]
  split
  · exact hrec
  · rename_i hout
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.fg_to_ac_F M F)]
    rcases hF with hFB | hBF
    · exfalso
      exact hout (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) n _).2
        ⟨hT, ancestorEq_trans hFB hrec⟩)
    · exact hBF

omit [RootOrder] in
/-- The finalized block of a node state whose caches are compatible with `B` is compatible with
`B`: it is the justified block or an ancestor of it, and the justified block is compatible with
`B`.

The variables:
- `M`: the model; `F`: its facts;
- `S`: the setup; `B`: the block; `H`: the threshold; `n`: the node state.

Read aloud: a validator whose caches are compatible with `B` has its finalized block compatible with
`B`. -/
theorem F_compatible_of_caches {S : Setup V} {B : Block V} {H : ℕ} {n : M.N}
    (hC : CachesCompatibleWith M S B H n) : n.finalized.AncestorEq B ∨
      B.AncestorEq n.finalized := by
  rcases hC.2.1 with hJB | hBJ
  · exact Or.inl (ancestorEq_trans hC.2.2.2.2 hJB)
  · exact ancestorEq_compatible hC.2.2.2.2 hBJ

/-- **The period's facts at a step after the hand-over update.** Under the hypotheses `P` of the
period: at every step `j` after every updater's tick to the hand-over cutoff `c` and at a time at least `c`
, with roots naming blocks
among what honest validators hold up to `x[j].time`, every lock holder honest through `j` records
`B` or a descendant of `B` and holds its record, and every validator honest at `j` has its
finalized block compatible with `B`.

Why: the second and third clauses of `PeriodInvCompatDueByCutoff` (`period_inv_compat_from`).




A configuration in the hand-over window: some configuration's real time is
at least the hand-over cutoff `M.supportCutoff S.C (s + 1)` and at most `ΔClockBehind` after it, where the hand-over
facts' third to fifth clauses say something; Lemma 101's step and the induction's base read the fifth
clause there.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `P`: the hypotheses of the period; `j`: the step.
- `T`: the time up to which `P`'s premises are read; `hjT`: the time of step `j` is at most `T`;
  `hTk`: every tick at a step before `j` is to a clock value at most `T`.

Read aloud: after the hand-over update, every lock holder honest so far records `B` or a
descendant of `B` and holds its record, and every honest validator has its finalized block
compatible with `B`. -/
theorem period_facts_from_handover (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind tW : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) {GST s : ℕ} {B : Block V}
    {H t₀ anchor tAwakeEnd b₀ b₁ Δs_F T : ℕ}
    (P : AsyncHypsOfChainBlockGSTBeforeVotesUntil M S A x GST s B H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F T (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet tW)
    -- some configuration's real time lies in the hand-over facts' window
    (hWin : ∃ j₀ : ℕ, ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) ≤ x.time j₀ ∧ x.time j₀ ≤ ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) + ΔClockBehind)
    (j : ℕ) (hTick : ∀ w ∈ updaterAt M S A x s, x.tickStep w (M.supportCutoff S.C (s + 1)) < j)
    (hj : M.supportCutoff S.C (s + 1) ≤ x.time j)
    -- the time of step `j` is at most `T`
    (hjT : x.time j ≤ T)
    -- the step is within the hand-over facts' window, or the facts cover the whole window
    (hjW : x.time j ≤ tW ∨ ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) + ΔClockBehind ≤ tW)
    -- every tick at a step before `j` is to a clock value at most `T`
    (hTk : ∀ (k : ℕ) (v : V) (c' : ℕ), k < j → x.lbl k = Event.tick v c' → c' ≤ T)
    (hRoots : RootsNameBlocksUntil M A x (x.time j)) :
    (∀ w ∈ updaterAt M S A x s, x.HonestThrough A j w →
      B.AncestorEq (x.st j w).latestConfirmed ∧
      (x.st j w).latestConfirmed ∈ (x.st j w).tree) ∧
    (∀ u : V, u ∉ A.corrupted j →
      (x.st j u).finalized.AncestorEq B ∨ B.AncestorEq (x.st j u).finalized) := by
  have I := (period_inv_compat_from M F U Fx R E hNet hSkew hRedeliver hΔs) P hWin j hTick hj hjT hjW hTk hRoots
  exact ⟨I.2.1, fun u hu => (F_compatible_of_caches M F) (I.2.2.1 u hu)⟩

/-- **The finalized blocks from the hand-over update on.** Under the hypotheses `P` of the period, read
up to `T`: at every step `j` at a time at least the hand-over update `c := M.supportCutoff S.C (s + 1)`
and at most `T`, with roots naming blocks among what honest validators hold up to `x[j].time`, every
validator honest at `j` has its finalized block compatible with `B`.

Why: at a time after `c` this is `period_facts_from_handover`. At the time `c` itself, `j` is at or
before the last step at `c`; the finalized block at `j` is that step's finalized block or an ancestor
of it (`F_ancestorEq_of_le`), and the hand-over facts make that step's caches compatible with `B`
(`F_compatible_of_caches`). No hypothesis on the order of the ticks at `c`.



A configuration in the hand-over window: some configuration's real time is
at least the hand-over cutoff `M.supportCutoff S.C (s + 1)` and at most `ΔClockBehind` after it, where the hand-over
facts' third to fifth clauses say something; Lemma 101's step and the induction's base read the fifth
clause there.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `P`: the hypotheses of the period, read up to `T`; `j`: the step; `hjT`: the time of step `j` is
  at most `T`; `hTk`: every tick at a step before `j` is to a clock value at most `T`.

Read aloud: from the hand-over update on, every honest validator has its finalized block compatible
with `B`. -/
theorem finalized_compatible_from_cutoff (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind tW : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) {GST s : ℕ} {B : Block V}
    {H t₀ anchor tAwakeEnd b₀ b₁ Δs_F T : ℕ}
    (P : AsyncHypsOfChainBlockGSTBeforeVotesUntil M S A x GST s B H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F T (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet tW)
    -- some configuration's real time lies in the hand-over facts' window
    (hWin : ∃ j₀ : ℕ, ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) ≤ x.time j₀ ∧ x.time j₀ ≤ ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) + ΔClockBehind)
    (j : ℕ) (hj : M.supportCutoff S.C (s + 1) ≤ x.time j)
    -- the time of step `j` is at most `T`
    (hjT : x.time j ≤ T)
    -- the step is within the hand-over facts' window, or the facts cover the whole window
    (hjW : x.time j ≤ tW ∨ ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) + ΔClockBehind ≤ tW)
    -- every tick at a step before `j` is to a clock value at most `T`
    (hTk : ∀ (k : ℕ) (v : V) (c' : ℕ), k < j → x.lbl k = Event.tick v c' → c' ≤ T)
    (hRoots : RootsNameBlocksUntil M A x (x.time j)) :
    ∀ u : V, u ∉ A.corrupted j →
      (x.st j u).finalized.AncestorEq B ∨ B.AncestorEq (x.st j u).finalized := by
  intro u hu
  rcases le_or_gt (x.time j) ((M.supportCutoff S.C (s + 1) : ℝ) + ΔClockBehind) with hle | hlt
  · -- up to `ΔClockBehind` after the hand-over cutoff: the hand-over facts' caches clause
    exact (F_compatible_of_caches M F) (P.hHand.2.2.1 j u hj (hjW.elim id (fun h => le_trans hle h)) hu)
  · -- later: every updater has ticked to the cutoff before `j` (its tick is at a real time at most
    -- `ΔClockBehind` after the cutoff), and the invariant's caches clause at `j`
    have hTick : ∀ w ∈ updaterAt M S A x s, x.tickStep w (M.supportCutoff S.C (s + 1)) < j := by
      intro w hw
      obtain ⟨k', hk', -⟩ := Activity.mem_activeThroughoutToTick.1 ((updaterAt_window M F) S A s w E hw)
      rw [(tickStep_eq_of_lbl M) x E hk']
      exact (lt_of_time_lt M) x R (by linarith [((time_of_lbl_tick M) x R E hk').1.2])
    exact (F_compatible_of_caches M F)
      (((period_inv_compat_from M F U Fx R E hNet hSkew hRedeliver hΔs) P hWin j hTick hj hjT hjW hTk hRoots).2.2.1 u hu)

/-- **Lemma 105.** The proof; the audited statement is in
`Statements/Executions/AsyncResilienceStatements.lean`.

A configuration in the hand-over window: some configuration's real time is
at least the hand-over cutoff `M.supportCutoff S.C (s + 1)` and at most `ΔClockBehind` after it, where the hand-over
facts' third to fifth clauses say something; Lemma 101's step and the induction's base read the fifth
clause there.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous outside the period; `s`: the hand-over slot; `B`: its proposal; `H`: the
  height threshold; `t₀`: the time from which the attestations are new; `anchor`: the time from
  which committee sleepiness holds; `tAwakeEnd`: the time from which the confirmed tips are read
; `b₀`, `b₁`: the start and the end of the period; `t`: the time up to
  which the steps are read; `T`: the bound up to which the premises are counted, at least `t` and at least the
  clock value of every tick at a step at a time at most `t`.

Read aloud: for every time `t`, if a root names one block among what honest validators hold by `t`,
every block confirmed from `tAwakeEnd` to the hand-over update is an ancestor of the confirmed tip
of every validator that ran that update, at every step from `b₀` up to `t`, and compatible with
every honest finalized block at those steps.

The premises are bounded: fewer than a quorum corrupted up to `t`, and
committee sleepiness for every slot whose support cutoff is at most `t`. under the clock bounds such a tick is to a clock value up to
`t + ΔClockAhead`, and the induction reads the premises at that clock value.

The hand-over facts are read up to the window's end `tW`, which is at least `t` or at least the end of the whole
window `M.supportCutoff S.C (s + 1) + ΔClockBehind` (`htW`): every step at which the proof reads them is at a real time
at most `t` and at most that end. -/
theorem confirmedPersists_throughPeriod_until (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s : ℕ) (B : Block V)
    (H t₀ anchor tAwakeEnd b₀ b₁ t T : ℕ)
    -- the premises are counted up to a bound `T` that every clock value reached by a tick at a step at a time at
    -- most `t` respects
    (hTt : t ≤ T) (hTk : ∀ (k : ℕ) (v : V) (c : ℕ), x.time k ≤ t → x.lbl k = Event.tick v c → c ≤ T)
    {Δs Δs_F : ℕ}
    -- blocks and Goldfish votes are delivered within `Δ` of the later of their time and `GST` when that
    -- is at or before `b₀`, and of the latest of their time, `b₁` and `GST` otherwise; attestations
    -- likewise within `Δ_F`
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryOutside A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks b₀ b₁) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {ΔNet_F : ℕ} (E_F : EnvFactsDeliveryOutside A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks b₀ b₁) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)
    -- what an honest active validator would serve at `t` reaches every validator active from `t`
    -- within `Δs` (`Δs_F` for attestations) of the later of `t` and `GST` when that is at or before
    -- `b₀`, and of the latest of `t`, `b₁` and `GST` otherwise
    (Sy : SyncedWithinOutside A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST b₀ b₁)
    (Sy_F : SyncedWithinOutside A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST b₀ b₁)
    -- the trace is wake-shaped; the sync delay is at most the slow window less three delays
 (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hParent : ParentHeldAtDelivery M x)
    -- fewer than a quorum of validators have been in the adversary set up to `T`
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) T)
    -- from `anchor` on, the honest active members of each committee counted up to `T` outnumber
    -- the rest: committee sleepiness for every slot whose support cutoff is at most `T`
    (hSleepK : CommitteeSleepinessUntil M S A x anchor T)
    (hAnchor : anchor ≤ M.slotStart S.C (s + 1))
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C (s + 1))
    (hb₀ : M.supportCutoff S.C (s + 1) ≤ b₀) (hb : b₀ ≤ b₁)
    (hb₁ : b₁ + max (Δ S) Δs ≤ M.voteTime S.C (s + S.C.k))
    (hHold : HoldersOutweighWhereOwed M S A x s Δs b₀ b₁)
    (hDelT : DelTLine M S A x s B b₀ b₁ Δs)
    (ht₀ : t₀ ≤ M.supportCutoff S.C (s + 1))
    -- the window's end up to which the hand-over facts are read: at least `t`, or the end of the whole window
    (tW : ℝ) (htW : (t : ℝ) ≤ tW ∨ ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) + ΔClockBehind ≤ tW)
    (hHand : HandoverFactsOfChainBlock M S A x tW s B H t₀ tAwakeEnd)
    -- some configuration's real time lies in the hand-over facts' window
    (hWin : ∃ j₀ : ℕ, ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) ≤ x.time j₀ ∧ x.time j₀ ≤ ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) + ΔClockBehind)
    (hRoots : RootsNameBlocksUntil M A x t) :
    ConfirmedPersistsBetween M S A x s tAwakeEnd b₀ t ∧
      FinalizedCompatibleBetween M S A x s tAwakeEnd b₀ t := by
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  -- the attestations' network delay is at most `Δ_F S`: `hNet_F` with the two clock bounds nonnegative
  have hΔnF : ΔNet_F ≤ Δ_F S := by
    have := E_F.ahead_nonneg; have := E_F.behind_nonneg
    exact_mod_cast (show (ΔNet_F : ℝ) ≤ Δ_F S by linarith)
  have P : AsyncHypsOfChainBlockGSTBeforeVotesUntil M S A x GST s B H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F T (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet tW :=
    ⟨ fun i k v sm t hs hok hk hik hwin hdk hrel => E.delivered i k v sm t _ hs hok hk hik hwin rfl hdk hrel, Sy,
      fun i k v sm t hs hok hk hik hwin hdk hrel => E_F.delivered i k v sm t _ hs hok hk hik hwin rfl
        (le_trans (GoldilocksCorrectness.Statements.AbstractTrace.deadlineOutsideR_mono_delay hΔnF) hdk) hrel,
      Sy_F, hParent, hAdvQ, hSleepK, hAnchor, hGST, hb₀, hb, hb₁, hHold, ht₀, hHand, hDelT⟩
  have E' := envFactsDelivery_of_outside_after M E htime
  have hB0 := E.behind_nonneg
  -- a step at a time from `b₀` is at a time at least the cutoff `c`
  have hcb : ∀ j : ℕ, (b₀ : ℝ) ≤ x.time j → ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) ≤ x.time j := fun j h =>
    le_trans (by exact_mod_cast hb₀) h
  have hTtR : (t : ℝ) ≤ T := by exact_mod_cast hTt
  -- a step at a time at most `t` is within the facts' window, or the facts cover the whole window
  have hjWt : ∀ j : ℕ, x.time j ≤ t → x.time j ≤ tW ∨ ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) + ΔClockBehind ≤ tW := fun j hj => htW.imp_left (le_trans hj)
  -- at a step at a time at most `t`, every tick before it is to a clock value at most `T`
  have hTkj : ∀ j : ℕ, x.time j ≤ t → ∀ (k : ℕ) (v : V) (c' : ℕ), k < j → x.lbl k = Event.tick v c' → c' ≤ T :=
    fun j hj k v c' hk hl => hTk k v c' (le_trans (htime hk.le) hj) hl
  refine ⟨fun v Tv Pb hv hTE hTv hTkv hP w j hw hupd htick hb₀j hjt => ?_,
    fun v Tv Pb hv hTE hTv hTkv hP w j hw hb₀j hjt => ?_⟩
  · have hPB := hHand.2.2.2.2.2.2 v Tv Pb hv hTE hTv hTkv hP
    have hcj := hcb j hb₀j
    have hRj := (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) hjt hRoots
    have hcT : M.supportCutoff S.C (s + 1) ≤ T := by exact_mod_cast le_trans (le_trans hcj hjt) hTtR
    -- `w`'s record at `j`: in the hand-over window by the holder invariant there, after it by the period facts
    obtain ⟨hrec, hheld⟩ : B.AncestorEq (x.st j w).latestConfirmed ∧ (x.st j w).latestConfirmed ∈ (x.st j w).tree := by
      by_cases hwin : x.time j ≤ ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) + ΔClockBehind
      · have hI := (holderInv_in_handover_window M F U R E' hNet hSkew hRedeliver) P hcT w hupd j htick hw hwin (le_trans hjt hTtR) (hjWt j hjt) hRj
        exact ⟨hI.2.1, hI.2.2.1⟩
      · push Not at hwin
        refine ((period_facts_from_handover M F U Fx R E' hNet hSkew hRedeliver hΔs) P hWin j (fun u hu => ?_) hcj (le_trans hjt hTtR) (hjWt j hjt)
          (hTkj j hjt) hRj).1 w hupd hw
        obtain ⟨hl, -⟩ := (tick_honest_of_activeThroughoutToTick M F E') ((updaterAt_window M F) S A s u E' hu)
        exact (lt_of_time_lt M) x R (lt_of_le_of_lt (E'.tick_active _ _ _ hl).2.2 hwin)
    exact ancestorEq_trans hPB ((preceq_confirmedOf_of_record_and_F M F) _ B hrec hheld
      ((finalized_compatible_from_cutoff M F U Fx R E' hNet hSkew hRedeliver hΔs) P hWin j hcj (le_trans hjt hTtR) (hjWt j hjt) (hTkj j hjt) hRj w (hw _ le_rfl)))
  · have hPB := hHand.2.2.2.2.2.2 v Tv Pb hv hTE hTv hTkv hP
    rcases (finalized_compatible_from_cutoff M F U Fx R E' hNet hSkew hRedeliver hΔs) P hWin j (hcb j hb₀j)
        (le_trans hjt hTtR) (hjWt j hjt) (hTkj j hjt)
        ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) hjt hRoots) w (hw _ le_rfl) with hFB | hBF
    · exact ancestorEq_compatible hPB hFB
    · exact Or.inl (ancestorEq_trans hPB hBF)

omit [RootOrder] in
/-- **`GST` is at most the vote time of slot `s + 1`** under the top statement's premises: `GST` at
most `tGAT`, the honest round opening slots from `tGAT + 4Δ · healFrontSlots S` to `tAwakeEnd`, and
the slot `s` starting after `tAwakeEnd`.

Why: `GST ≤ tGAT ≤` the start of the first opening's slot `≤` the support cutoff of the last
opening's slot `≤ tAwakeEnd < M.slotStart S.C s < M.voteTime S.C (s + 1)`.

The landed theorem was promoted from `scratch/goldilocks_async/probe_ar4_replan.lean:127`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`: the setup, the schedule; `GST`: the time from which the network is synchronous;
  `tGAT`, `tAwakeEnd`: the start and end of the healing phase; `m`: the index of the last honest round opening slot;
  `s`: the hand-over slot; `r`: the rounds of the honest round opening slots.

Read aloud: the network is synchronous by the first votes after the hand-over proposal. -/
theorem gst_le_voteTime_succ_of_top (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)
    (GST tGAT tAwakeEnd m s : ℕ) (r : ℕ → ℕ)
    (hGST : GST ≤ tGAT)
    (hSeq : HonestOpeningSeq M S A x r m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hs : tAwakeEnd < M.slotStart S.C s) :
    GST ≤ M.voteTime S.C (s + 1) := by
  have hΔ := one_le_Δ S
  have h0m : r 0 ≤ r m := by
    have key : ∀ i, i ≤ m → r 0 ≤ r i := by
      intro i hi
      induction i with
      | zero => exact le_rfl
      | succ n ih =>
        exact le_trans (ih (Nat.le_of_succ_le hi)) (le_of_lt (hSeq.mono n (by omega)))
    exact key m le_rfl
  have h1 := hSeq.first
  have h2 := hSeq.last
  have h3 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (Nat.mul_le_mul_right S.C.R h0m)
  have h4 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (r m * S.C.R)
  have h5 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (r m * S.C.R)
  have h6 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s + 1)
  have h7 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (show s ≤ s + 1 by omega)
  have h8 : tGAT ≤ tGAT + 4 * Δ S * healFrontSlots S := Nat.le_add_right _ _
  omega


omit [RootOrder] in
/-- Every `EnvFactsBy` gives the two bounds nonnegative (`ahead_nonneg`, `behind_nonneg`).

Why: `GST + 4Δ(3k + 1) ≤ tGAT + 4Δ · healFrontSlots S ≤` the start of the first opening's slot `≤ tAwakeEnd
< M.slotStart S.C s`; the two bounds nonnegative turn `hΔs` into `max (Δ S) Δs + 3Δ < 4Δk` over the natural
numbers; and the support cutoff of `s + 1` is `M.slotStart S.C s + 6Δ`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`: the setup, the activity, the trace; `GST`: the time from which the network is synchronous;
  `tGAT`, `tAwakeEnd`: the start and end of the healing phase; `m`: the index of the last honest round
  opening slot; `s`: the hand-over slot; `r`: the rounds of the honest round opening slots; `Δs`: the
  sync delay; `hA`, `hB`: the two clock bounds are nonnegative.

Read aloud: the network has recovered, for one sync delay, by the hand-over cutoff, given that the two clock
bounds are not negative. -/
theorem gst_sync_succ_of_top_of_clock_nonneg (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)
    (GST tGAT tAwakeEnd m s : ℕ) (r : ℕ → ℕ) {Δs : ℕ}
    (hGST : GST ≤ tGAT) {ΔClockAhead ΔClockBehind : ℝ} (hA : 0 ≤ ΔClockAhead) (hB : 0 ≤ ΔClockBehind)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hSeq : HonestOpeningSeq M S A x r m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hs : tAwakeEnd < M.slotStart S.C s) :
    GST + max (Δ S) Δs ≤ M.supportCutoff S.C (s + 1) := by
  have hΔsN : max (Δ S) Δs + 3 * Δ S < 4 * Δ S * S.C.k := by
    have h : ((max (Δ S) Δs + 3 * Δ S : ℕ) : ℝ) < ((4 * Δ S * S.C.k : ℕ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast h
  have hΔ := one_le_Δ S
  have h0m : r 0 ≤ r m := by
    have key : ∀ i, i ≤ m → r 0 ≤ r i := by
      intro i hi
      induction i with
      | zero => exact le_rfl
      | succ n ih =>
        exact le_trans (ih (Nat.le_of_succ_le hi)) (le_of_lt (hSeq.mono n (by omega)))
    exact key m le_rfl
  have h1 := hSeq.first
  have h2 := hSeq.last
  have h3 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (Nat.mul_le_mul_right S.C.R h0m)
  have h4 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (r m * S.C.R)
  have h5 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (r m * S.C.R)
  obtain ⟨h6, h7, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (s + 1)
  have h8 := (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (show s ≤ s + 1 by omega)
  have h9 : 4 * Δ S * healFrontSlots S = 3 * (4 * Δ S * S.C.k) + 4 * Δ S := by
    unfold healFrontSlots
    ring
  omega

open Classical in
/-- **The asynchrony top statement.** The proof; the audited statement is in
`Statements/Executions/AsyncResilienceStatements.lean`.

Route: when `t < b₀` no step is read. Otherwise roots name blocks up to `t` or a collision hit by
`t` (`rootsNameBlocksUntil_or_collision`); the facts after the hand-over read up to `b₀`
(`healed_handover_facts_until_upTo` at `b := b₀`, `t := b₀`, the delivery premises up to `b₀` from the
suspended ones), which cover every updater of the slots up to `s`: every tick to the update of a slot before `s`
is before the real time `c := M.supportCutoff S.C (s + 1)`, and every tick to `c` is by `b₀` (`hTicks₀`); the
confirmations of the slots from `s₀` to `s` form one chain; the chain invariant and the lock invariant at the
slots after `s₀` and at most `s` (`lem81_inv_before_upTo` at `n := s + 1`); the lock invariant at `s₀`
(`base_locks_on_chain`); the voter condition at slot `s + 1` (`voterFrame_after_handover_until_upTo`, with
`confirmation_holder_at_window_start_until`); the records on the honest chain
(`lem90a_latest_confirmed_honest_at`); the caches up to `tW := min t (c + ΔClockBehind)` (the hand-over facts'
row up to `b₀`, `lem84_caches_stay_on_chain_from` after it); Lemma 99's two theorems
(`handoverFacts_six_of_healed_upTo` at `tW`, `confirmed_tips_preceq_handover_upTo`, the latter read from
`tAwakeEnd ≥ x[i₂].time` on), which give `HandoverFactsOfChainBlock` at `tW` with the lower end
`tAwakeEnd`; and Lemma 105 at `tW` with `anchor := anchorCW S tGAT` and `GST` one sync delay before `c`
(`gst_sync_succ_of_top_of_clock_nonneg`).

A configuration in the hand-over window: some configuration's real time is
at least the hand-over cutoff `M.supportCutoff S.C (s + 1)` and at most `ΔClockBehind` after it, where the hand-over
facts' third to fifth clauses say something; Lemma 101's step and the induction's base read the fifth
clause there.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous outside the period; `tGAT`, `tAwakeEnd`: the start and end of the healing
  phase; `m`: the index of the last honest round opening slot; `r`: the rounds of the honest round opening slots; `s`: the hand-over
  slot; `b₀`, `b₁`: the start and the end of the period.

Read aloud: after the healing phase, for every time `t`: a digest collision hit an honest round opening slot's
proposal, or two blocks honest validators hold by `t` share a root, or, for every block `B` the
hand-over slot's proposer puts on the wire at the start of its slot, `B` collides by root with a
block the proposer held, or every block confirmed from `tAwakeEnd` to `B`'s update persists at every
validator that ran that update, at every step from `b₀` to `t`, and no honest validator finalizes a
conflicting block by `t`: one asynchronous period of fewer than `k` slots, started after that
update, abandons nothing confirmed from `tAwakeEnd` on before it. -/
theorem confirmedPersists_asyncPeriod_until (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd m : ℕ) (r : ℕ → ℕ) (s b₀ b₁ : ℕ)
    (hGST : GST ≤ tGAT)
    {Δs Δs_F : ℕ}
    -- blocks and Goldfish votes are delivered within `Δ` of the later of their time and `GST` when that
    -- is at or before `b₀`, and of the latest of their time, `b₁` and `GST` otherwise; attestations
    -- likewise within `Δ_F`
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryOutside A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks b₀ b₁) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {ΔNet_F : ℕ} (E_F : EnvFactsDeliveryOutside A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks b₀ b₁) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)
    -- what an honest active validator would serve at `t` reaches every validator active from `t`
    -- within `Δs` (`Δs_F` for attestations) of the later of `t` and `GST` when that is at or before
    -- `b₀`, and of the latest of `t`, `b₁` and `GST` otherwise
    (Sy : SyncedWithinOutside A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST b₀ b₁)
    (Sy_F : SyncedWithinOutside A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST b₀ b₁)
    -- the trace is wake-shaped; the sync delay is at most the slow window less three delays
 (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hΔs_F : (Δs_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S ∨ (Δs_F : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind ≤ 4 * Δ S * S.C.k)
    -- for each honest round opening slot, every validator outside the adversary set at the support cutoff of the slot
    -- after its first slot is active through the attestations' sync delay after the later of that first slot's duty
    -- window's start and `GST`
    (hHoldF : ∀ i, i < m → ∀ v, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (r i * S.C.R + 1)) →
      v ∈ A.activeThroughout x ((max (M.dutyWindowStart S.C (r i * S.C.R)) GST : ℕ) : ℝ)
        (((max (M.dutyWindowStart S.C (r i * S.C.R)) GST : ℕ) : ℝ) + Δs_F))
    (hParent : ParentHeldAtDelivery M x)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    -- the time up to which the execution is read
    (t T : ℕ)
    -- the premises are counted up to a bound `T` that every clock value reached by a tick at a step at a time at
    -- most `t` respects
    (hTt : t ≤ T) (hTk : ∀ (k : ℕ) (v : V) (c : ℕ), x.time k ≤ t → x.lbl k = Event.tick v c → c ≤ T)
    -- `t` is not inside any slot's update: at every slot whose update is at most `t`, or to whose update some
    -- validator ticked at a real time at most `t`, every tick to a clock value at most that update is at a real
    -- time at most `t`
    (hTicksBy : TicksToUpdatesBy M S x t)
    -- committee sleepiness from `anchorCW S tGAT`, for the slots whose update is at most `T`
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) T)
    -- every updater of a slot from the first honest round opening slot `r 0 * S.C.R` on, whose update is at
    -- most `T`, is active for the sync delay after the real time of its own tick to the support cutoff of the
    -- next slot
    (hStay : ∀ σ : ℕ, r 0 * S.C.R ≤ σ → M.supportCutoff S.C (σ + 1) ≤ T → ∀ u ∈ updaterAt M S A x σ,
      u ∈ A.activeThroughout x (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))))
        (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))) + Δs))
    (hSeq : HonestOpeningSeq M S A x r m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hOpenings : OpeningsOutsideWaitsAndWindows S r m)
    -- fewer than two thirds of the validators corrupted up to `t`
    (hAdvQ : A.AdversaryFewerThanTwoThirdsUntil x (validator_count V) T)
    (hs : tAwakeEnd < M.slotStart S.C s)
    (hp : S.P.proposer s ∈ A.activeThroughoutToTick x (Goldilocks.proposal_window_start S.C s)
        (M.supportCutoff S.C (s + 1)) ∧
      S.P.proposer s ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) ∪
        Finset.univ.filter (fun u => ∃ (k : ℕ) (w : V),
          x.lbl k = Event.tick w (M.supportCutoff S.C (s + 1)) ∧ w ∉ A.corrupted k ∧ u ∈ A.corrupted k))
    -- the honest voters of slots `s - 1` and `s` are active through the sync delay after Lemma 12's read time of
    -- their slot
    (hHoldV : ∀ s' : ℕ, s - 1 ≤ s' → s' ≤ s → ∀ u ∈ honestActiveAt M S A x s', u ∈ S.P.committee s' →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    -- the proposer of slot `s` is active through the sync delay after `M.slotStart S.C s - max (Δ S) Δs`
    (hHoldP : S.P.proposer s ∈ A.activeThroughout x ((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hb₀ : M.supportCutoff S.C (s + 1) ≤ b₀)
    -- every validator's tick to the hand-over update is at a real time at most `b₀`
    (hTicks₀ : ∀ (k : ℕ) (u : V), x.lbl k = Event.tick u (M.supportCutoff S.C (s + 1)) → (x.time k : ℝ) ≤ b₀)
    (hb : b₀ ≤ b₁)
    -- some configuration's real time lies in the hand-over facts' window
    (hWin : ∃ j₀ : ℕ, ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) ≤ x.time j₀ ∧ x.time j₀ ≤ ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) + ΔClockBehind)
    (hb₁ : b₁ + max (Δ S) Δs ≤ M.voteTime S.C (s + S.C.k))
    (hHold : HoldersOutweighWhereOwed M S A x s Δs b₀ b₁)
    (hDelT : ∀ B : Block V, DelTLine M S A x s B b₀ b₁ Δs) :
    RootCollisionAtOpening M S A x r m ∨ RootCollisionHeldBy M S A x t ∨
      ∀ (i : ℕ) (B : Block V), x.lbl i = Event.tick (S.P.proposer s) (M.slotStart S.C s) →
        (⟨S.P.proposer s, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
          x.sent (i + 1) - x.sent i →
        RootCollisionAtProposal M S A x s B ∨
          (ConfirmedPersistsBetween M S A x s tAwakeEnd b₀ t ∧
            FinalizedCompatibleBetween M S A x s tAwakeEnd b₀ t) := by
  have hAdvQ' := (adversaryFewerThanQuorumUntil_of_adversaryFewerThanTwoThirdsUntil M F) A x T hAdvQ
  rcases Nat.lt_or_ge t b₀ with htb | htb
  · -- no step at a time from `b₀` to `t`
    have htbR : (t : ℝ) < b₀ := by exact_mod_cast htb
    refine Or.inr (Or.inr fun i B _ _ => Or.inr ⟨?_, ?_⟩)
    · intro v T' P _ _ _ _ _ w j _ _ _ hj1 hj2
      exact absurd (lt_of_le_of_lt (le_trans hj1 hj2) htbR) (lt_irrefl _)
    · intro v T' P _ _ _ _ _ w j _ hj1 hj2
      exact absurd (lt_of_le_of_lt (le_trans hj1 hj2) htbR) (lt_irrefl _)
  rcases (rootsNameBlocksUntil_or_collision M) x t with hRootsT | hCol
  swap
  · exact Or.inr (Or.inl hCol)
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔ := one_le_Δ S
  have hΔR : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  have hcm : ∀ a b : ℕ, a ≤ b → M.supportCutoff S.C a ≤ M.supportCutoff S.C b := fun a b h =>
    (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S h
  obtain ⟨hvS, hcS, hfS, hsS, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S s
  obtain ⟨hvS1, hcS1, -, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.times_eq M.toSlotLayout F.sched U) S (s + 1)
  -- the times: `tAwakeEnd < slotStart S s < c := supportCutoff S (s + 1) ≤ b₀ ≤ t ≤ T`
  have hTc : tAwakeEnd ≤ M.supportCutoff S.C (s + 1) := by omega
  have hb₀t : b₀ ≤ t := htb
  have hct : M.supportCutoff S.C (s + 1) ≤ t := le_trans hb₀ htb
  have hcT : M.supportCutoff S.C (s + 1) ≤ T := le_trans hct hTt
  have hb₀T : b₀ ≤ T := le_trans htb hTt
  have hb₀R : (b₀ : ℝ) ≤ t := by exact_mod_cast htb
  have htTR : (t : ℝ) ≤ T := by exact_mod_cast hTt
  have hcb₀R : ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) ≤ b₀ := by exact_mod_cast hb₀
  have hTEb : (tAwakeEnd : ℝ) ≤ b₀ := by exact_mod_cast le_trans hTc hb₀
  -- the support cutoff of slot `s + 1` is `4Δ` after that of slot `s`
  have hcsR : ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) = (M.supportCutoff S.C s : ℕ) + 4 * Δ S := by
    have := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_succ_eq M.toSlotLayout F.sched U) S s
    rw [this]; push_cast; ring
  -- every tick to the update of a slot at most `s` is at a real time at most `b₀`
  have hTb : ∀ σ : ℕ, σ ≤ s → ∀ (k : ℕ) (u : V), x.lbl k = Event.tick u (M.supportCutoff S.C (σ + 1)) →
      x.time k ≤ b₀ := by
    intro σ hσ k u hk
    rcases Nat.eq_or_lt_of_le hσ with rfl | hlt
    · exact hTicks₀ k u hk
    · have h1 := (E.tick_active k u _ hk).2.2
      have h2 : ((M.supportCutoff S.C (σ + 1) : ℕ) : ℝ) ≤ (M.supportCutoff S.C s : ℕ) := by
        exact_mod_cast hcm _ _ hlt
      linarith
  have hUb : ∀ σ : ℕ, σ ≤ s → ∀ v ∈ updaterAt M S A x σ,
      x.time (x.tickStep v (M.supportCutoff S.C (σ + 1))) ≤ b₀ := by
    intro σ hσ v hv
    have hv' := hv
    unfold updaterAt at hv'
    obtain ⟨K, hK, -⟩ := (Activity.mem_activeThroughoutToTick).1 hv'
    rw [(tickStep_eq_of_lbl M) x E hK]
    exact hTb σ hσ K v hK
  -- the delivery promises and the sync facts up to `b₀`, from the suspended ones
  have E₀ := envFactsDeliveryUpTo_of_outside M E
  have Sy₀ := Sy.upTo
  have hlast : M.slotStart S.C (r m * S.C.R) ≤ b₀ := by
    have h1 := hSeq.last
    have h2 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S (r m * S.C.R)
    have h3 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (r m * S.C.R)
    omega
  have hOwner : VotesCastByOwner M A x := (votesCastByOwner_of_unforgeability M F) S A x R E₀
  -- the facts after the hand-over, read up to `b₀`
  rcases (healed_handover_facts_until_upTo M F U Fx) S A x R GST tGAT tAwakeEnd m r hGST
      E₀ hNet hSkew hRedeliver Sy₀ hΔs ((envFactsDeliveryUpTo_of_outside M E_F).mono hlast) hNet_F hSkew_F
      (Sy_F.upTo.mono hlast) hΔs_F hHoldF hParent hThird hAwake hActive b₀ (le_trans hTc hb₀)
      (hCommittees.mono M hb₀T)
      (fun k u c hk hkb => hCommittees.mono M (hTk k u c (le_trans hkb hb₀R) hk))
      (fun σ h1 h2 => hStay σ h1 (le_trans h2 hb₀T)) hSeq hOpenings
      (hAdvQ'.mono (by exact_mod_cast hb₀T)) le_rfl with
    hCol | hCol | ⟨s₀, i₂, B₀, ⟨hsc, hscTick⟩, hx2, hx2s, h0, hGST', hAnc, hB₀slot, hBase, hBaseSaved, hUpd, hOld,
      hCachesJ, -, hVF, hUF, hChain⟩
  · exact Or.inl hCol
  · obtain ⟨B₁, B₂, h1, h2, h3, hne⟩ := hCol
    exact absurd (((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) hb₀R hRootsT)
      B₁ B₂ h1 h2 h3) hne
  right; right
  have hGSTs : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀ :=
    gst_sync_of_anchor M F U S hGST hΔs hAnc (by linarith)
  intro i B hlbl hsent
  by_cases hCol : RootCollisionAtProposal M S A x s B
  · exact Or.inl hCol
  right
  -- the slots and the anchor
  have hx2b₀ : x.time i₂ ≤ b₀ := le_trans hx2 hTEb
  have hsS' : (tAwakeEnd : ℝ) < M.slotStart S.C s := by exact_mod_cast hs
  have hs₀s : s₀ + 2 ≤ s := by
    have h1 : ((M.supportCutoff S.C (s₀ + 1) : ℕ) : ℝ) < (M.voteTime S.C s : ℕ) := by
      have : ((M.voteTime S.C s : ℕ) : ℝ) = (M.slotStart S.C s : ℕ) + Δ S := by rw [hvS]; push_cast; ring
      linarith
    exact ((GoldilocksCorrectness.Record.Proofs.Routines.slot_le_of_supportCutoff_lt M.toSlotLayout F.sched) S s₀ s).1
      (by exact_mod_cast h1)
  have hAncS : anchorCW S tGAT ≤ M.slotStart S.C (s + 1) :=
    le_trans hAnc ((GoldilocksCorrectness.Record.Proofs.Routines.slotStart_mono M.toSlotLayout F.sched) S (by omega))
  have hAnc₂ : anchorCW S tGAT ≤ x.time i₂ := by
    have h1 : M.slotStart S.C (s₀ + 1) ≤ M.supportCutoff S.C (s₀ + 1) := by
      rw [(GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U),
        (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U)]
      omega
    have h2 : ((anchorCW S tGAT : ℕ) : ℝ) ≤ ((M.supportCutoff S.C (s₀ + 1) : ℕ) : ℝ) := by
      exact_mod_cast le_trans hAnc h1
    linarith
  have hcsc : M.supportCutoff S.C s ≤ M.supportCutoff S.C (s + 1) := hcm _ _ (Nat.le_succ s)
  have hc₀T : M.supportCutoff S.C (s₀ + 1) ≤ T := le_trans (hcm _ _ (by omega)) hcT
  -- the confirmations of the slots from `s₀` to `s` form one chain: every updater of such a slot ticked to its
  -- update by `b₀`
  have hstep : ∀ σ : ℕ, σ ≤ s → ConfirmationsChainBefore M S A x s₀ σ →
      ConfirmationsChainBefore M S A x s₀ (σ + 1) := by
    intro σ hσ hC
    by_cases hex : ∃ (k : ℕ) (u : V), x.lbl k = Event.tick u (M.supportCutoff S.C (σ + 1))
    · obtain ⟨k, u, hk⟩ := hex
      obtain ⟨-, hHalf⟩ := hChain σ k u hk (hTb σ hσ k u hk)
      intro s' s'' v v' C C' hs' hss hs'' hv hv' hC₁ hC₂
      rcases Nat.lt_or_ge s'' σ with hlt | hge
      · exact hC s' s'' v v' C C' hs' hss hlt hv hv' hC₁ hC₂
      obtain rfl : σ = s'' := by omega
      obtain ⟨hAnc', -⟩ := hHalf v' hv' (hUb _ hσ v' hv') C' hC₂
      refine ⟨fun hlt => hAnc' C ⟨s', hlt, hs', v, hv, C, hC₁, ancestorEq_refl C⟩, fun heq => ?_⟩
      subst heq
      obtain ⟨-, hComp⟩ := hHalf v hv (hUb _ hσ v hv) C hC₁
      exact hComp hs' v' hv' (hUb _ hσ v' hv') C' hC₂
    · intro s' s'' v v' C C' hs' hss hs'' hv hv' hC₁ hC₂
      rcases Nat.lt_or_ge s'' σ with hlt | hge
      · exact hC s' s'' v v' C C' hs' hss hlt hv hv' hC₁ hC₂
      obtain rfl : σ = s'' := by omega
      unfold updaterAt at hv'
      obtain ⟨K, hK, -⟩ := (Activity.mem_activeThroughoutToTick).1 hv'
      exact absurd ⟨K, v', hK⟩ hex
  have hChainUp : ∀ σ : ℕ, σ ≤ s → ConfirmationsChainBefore M S A x s₀ (σ + 1) := by
    intro σ
    induction σ with
    | zero =>
      intro h
      exact hstep 0 h (fun s' s'' v v' C C' _ _ h3 => absurd h3 (Nat.not_lt_zero _))
    | succ n ih => exact fun h => hstep (n + 1) h (ih (by omega))
  have hChainS1 : ConfirmationsChainBefore M S A x s₀ (s + 1) := hChainUp s le_rfl
  have hChainSm : ConfirmationsChainBefore M S A x s₀ (s - 1) := by
    intro a b v v' C C' h1 h2 h3
    exact hChainS1 a b v v' C C' h1 h2 (by omega)
  -- the chain invariant and the lock invariant at the slots after `s₀` and at most `s`
  have hcs1 : M.supportCutoff S.C (s + 1 - 1) ≤ b₀ := by
    rw [Nat.add_sub_cancel]
    exact le_trans hcsc hb₀
  have hInvAll := (lem81_inv_before_upTo M F U) S A x R GST s₀ (anchorCW S tGAT)
    (s + 1) B₀ (E₀.mono hcs1) hNet hSkew hRedeliver (Sy₀.mono hcs1) hΔs
    ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M)
      (by exact_mod_cast le_trans hcs1 htb) hRootsT)
    (fun k u c hk hc => (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M)
      (by
        have h1 := (E.tick_active k u c hk).2.2
        have h2 : (c : ℝ) ≤ (M.supportCutoff S.C s : ℕ) := by
          rw [Nat.add_sub_cancel] at hc; exact_mod_cast hc
        linarith) hRootsT)
    hParent hOwner hGSTs (hCommittees.mono M hcT) hAnc hB₀slot hBase hBaseSaved
    (fun s' h₁ h₂ w hw => hVF s' h₁ (le_trans (hcm _ _ (by omega)) hb₀) w hw)
    (fun s' h₁ h₂ v hv => hUF s' h₁ v hv (hUb s' (by omega) v hv))
  have hInv : ∀ s' : ℕ, s₀ < s' → s' ≤ s →
      ChainInvFor M S A x (honestActiveAt M S A x s') (OnHonestChainBefore M S A x s₀ s') s' :=
    fun s' h₁ h₂ => (hInvAll s' h₁ (by omega)).1
  have hLocks : ∀ s' : ℕ, s₀ < s' → s' ≤ s → ∀ u ∈ honestActiveAt M S A x s',
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ s') s' u :=
    fun s' h₁ h₂ => (hInvAll s' h₁ (by omega)).2
  have hLocks₀ : ∀ u ∈ honestActiveAt M S A x s₀,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ (s₀ + 1)) s₀ u :=
    fun u hu => (base_locks_on_chain M F U) S A x R s₀ (anchorCW S tGAT) B₀ u E₀
      (hCommittees.mono M hc₀T) hAnc hB₀slot hBase hBaseSaved hu
  -- the voter condition at slot `s + 1`
  have hvc : M.voteTime S.C (s + 1) ≤ M.supportCutoff S.C (s + 1) := by omega
  have hFrames : ∀ w ∈ honestActiveAt M S A x (s + 1), VoterFrameOnChainAt M S A x s₀ (s + 1) w := by
    intro w hw
    obtain ⟨kw, hkw⟩ := (tick_voteTime_of_honestActiveAt_succ M F U) S A x R E₀ hSkew s w hw
    have hkwT : x.time (x.tickStep w (M.voteTime S.C (s + 1))) ≤ b₀ := by
      rw [(tickStep_eq_of_lbl M) x E hkw]
      have h1 := (E.tick_active kw w _ hkw).2.2
      have h2 : ((M.voteTime S.C (s + 1) : ℕ) : ℝ) ≤ ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) := by
        exact_mod_cast hvc
      have h3 : ((M.voteTime S.C (s + 1) : ℕ) : ℝ) + Δ S = ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) := by
        rw [hvS1, hcS1]; push_cast; ring
      linarith
    exact (voterFrame_after_handover_until_upTo M F U Fx) S A x R GST s₀ i₂
      (M.chainStateOf S.C B₀).h (s + 1) w (E₀.mono (le_trans hvc hb₀))
      hNet hSkew hRedeliver (Sy₀.mono (le_trans hvc hb₀)) hΔs
      ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) (le_trans hkwT hb₀R) hRootsT)
      hParent (hAdvQ'.mono (max_le (le_trans hkwT (le_trans hb₀R htTR)) (by exact_mod_cast hc₀T)))
      ((gst_sync_le_viewFreeze M F U) S hGSTs (by omega))
      ((confirmation_holder_at_window_start_until M F U) S A x R E₀ hSkew s₀ (s + 1) (anchorCW S tGAT) T Δs
        hCommittees hAnc hcT
        (fun σ h1 h2 => ⟨hVF σ h1 (le_trans (hcm _ _ (by omega)) hb₀),
          fun v hv => hUF σ h1 v hv (hUb σ (by omega) v hv)⟩)
        (fun σ h1 h2 u hu => hStay σ (le_trans h0 h1) h2 u hu))
      (fun σ h1 h2 u hu => hStay σ (le_trans h0 h1) (le_trans (hcm _ _ (by omega)) hcT) u hu)
      hOld
      (fun j u h₁ h₂ hu => hCachesJ j u h₁.le (le_trans h₂ hkwT) hu)
      (by
        rw [Nat.add_sub_cancel]
        have : ((M.viewFreeze S.C s : ℕ) : ℝ) = (M.slotStart S.C s : ℕ) + 3 * Δ S := by rw [hfS]; push_cast; ring
        linarith)
      hChainS1 hw
  -- the records, on the chain at a slot whose update ran by then
  have hLatest0 := (lem90a_latest_confirmed_honest_at M F U) S A x R s₀ B₀ E₀ hSkew
    hB₀slot hBase hBaseSaved hUpd
  have hLatest : ∀ (j : ℕ) (u : V), x.time i₂ ≤ x.time j → x.time j ≤ M.supportCutoff S.C (s + 1) →
      u ∉ A.corrupted j → (∃ σ : ℕ,
        x.lbl (x.tickStep u (M.supportCutoff S.C (σ + 1))) = Event.tick u (M.supportCutoff S.C (σ + 1)) ∧
        x.tickStep u (M.supportCutoff S.C (σ + 1)) < j ∧
        OnHonestChainAt M S A x s₀ σ (x.st j u).latestConfirmed) ∧
        (x.st j u).latestConfirmed ∈ (x.st j u).tree := by
    intro j v h _ hv
    classical
    have hvU : v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s₀ + 1)) := Activity.not_mem_corruptedAtTime.2
      fun k hk => E.not_mem_corrupted_of_le ((lt_of_time_lt M) x R (lt_of_le_of_lt hk (lt_of_lt_of_le hsc h))).le hv
    have hvS : v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s₀ + 1)) ∪
        Finset.univ.filter (fun u => ∃ (k : ℕ) (w : V),
          x.lbl k = Event.tick w (M.supportCutoff S.C (s₀ + 1)) ∧ w ∉ A.corrupted k ∧ u ∈ A.corrupted k) := by
      rw [Finset.mem_union, not_or]
      refine ⟨hvU, fun hm => ?_⟩
      obtain ⟨-, k, w, hk, -, hvk⟩ := Finset.mem_filter.1 hm
      exact E.not_mem_corrupted_of_le ((lt_of_time_lt M) x R (lt_of_lt_of_le (hscTick k w hk) h)).le hv hvk
    have hvu := hUpd v hvU
    unfold updaterAt at hvu
    obtain ⟨K, hK, -⟩ := (Activity.mem_activeThroughoutToTick).1 hvu
    have hKi : x.tickStep v (M.supportCutoff S.C (s₀ + 1)) < j := by
      rw [(tickStep_eq_of_lbl M) x E hK]
      exact (lt_of_time_lt M) x R (lt_of_lt_of_le (hscTick K v hK) h)
    obtain ⟨⟨σ, hσ, hl, hlt, u, hu, hsv⟩, hmem⟩ := hLatest0 j v hvS hKi hv
    exact ⟨⟨σ, hl, hlt, hσ, u, hu, _, hsv, ancestorEq_refl _⟩, hmem⟩
  -- the window's end up to which Lemma 99 and Lemma 105 read the hand-over facts
  set tW : ℝ := min (t : ℝ) (((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) + ΔClockBehind) with htWdef
  have htWt : tW ≤ t := min_le_left _ _
  have htWc : tW ≤ ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) + ΔClockBehind := min_le_right _ _
  have htW : (t : ℝ) ≤ tW ∨ ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) + ΔClockBehind ≤ tW :=
    (le_total (t : ℝ) (((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) + ΔClockBehind)).imp
      (fun h => le_of_eq (min_eq_left h).symm) (fun h => le_of_eq (min_eq_right h).symm)
  -- the caches up to `tW`: the hand-over facts' row up to `b₀`, Lemma 84 from `i₂` after it
  have hCachesW : ∀ (j : ℕ) (u : V), x.time i₂ ≤ x.time j → x.time j ≤ tW →
      u ∉ A.corrupted j → CachesOnChain M S A x s₀ (M.chainStateOf S.C B₀).h (x.st j u) := by
    intro j u h1 h2 hu
    by_cases hjb : x.time j ≤ b₀
    · exact hCachesJ j u h1 hjb hu
    push Not at hjb
    have hij : i₂ < j := (lt_of_time_lt M) x R (lt_of_le_of_lt hx2b₀ hjb)
    have hui : u ∉ A.corrupted i₂ := E.not_mem_corrupted_of_le hij.le hu
    exact (lem84_caches_stay_on_chain_from M F U Fx) S A x R s₀ (M.supportCutoff S.C (s₀ + 1))
      (M.chainStateOf S.C B₀).h i₂ t u E₀ hRootsT
      (hAdvQ'.mono (by exact_mod_cast max_le hTt hc₀T))
      ((lem82_honest_attestations_on_chain M F U) S A x R s₀ E₀) hOld
      (hCachesJ i₂ u le_rfl hx2b₀ hui) j hij.le (le_trans h2 htWt) hu
  have hs' : x.time i₂ < M.slotStart S.C s ∧
      ∀ k : ℕ, x.lbl k = Event.tick (S.P.proposer s) (M.slotStart S.C s) → x.time i₂ < x.time k :=
    ⟨(hx2s s hs.le).1, fun k hk => (hx2s s hs.le).2 k _ hk⟩
  have hp' : S.P.proposer s ∈ A.activeThroughoutToTick x (Goldilocks.proposal_window_start S.C s)
        (M.supportCutoff S.C (s + 1)) ∧
      S.P.proposer s ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) :=
    ⟨hp.1, fun h => hp.2 (Finset.mem_union_left _ h)⟩
  have hRootsU : ∀ v ∈ updaterAt M S A x s,
      RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C (s + 1)))) := fun v hv =>
    (GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) (le_trans (hUb s le_rfl v hv) hb₀R) hRootsT
  have hAdvQU : ∀ v ∈ updaterAt M S A x s,
      A.AdversaryFewerThanQuorumUntil x (quorum V) (x.time (x.tickStep v (M.supportCutoff S.C (s + 1)))) :=
    fun v hv => hAdvQ'.mono (le_trans (hUb s le_rfl v hv) (le_trans hb₀R htTR))
  have hCachesU : ∀ v ∈ updaterAt M S A x s, ∀ (j : ℕ) (u : V), x.time i₂ ≤ x.time j →
      x.time j ≤ x.time (x.tickStep v (M.supportCutoff S.C (s + 1))) →
      u ∉ A.corrupted j → CachesOnChain M S A x s₀ (M.chainStateOf S.C B₀).h (x.st j u) :=
    fun v hv j u h1 h2 hu => hCachesJ j u h1 (le_trans h2 (hUb s le_rfl v hv)) hu
  have E_S := E₀.mono (le_trans hcsc hb₀)
  have Sy_S := Sy₀.mono (le_trans hcsc hb₀)
  -- Lemma 99: the hand-over facts up to `tW`, the confirmed tips read from `tAwakeEnd` on
  have hSix := (handoverFacts_six_of_healed_upTo M F U Fx) S A x R GST s₀
    (anchorCW S tGAT) i₂ (M.chainStateOf S.C B₀).h s B E_S hNet hSkew hRedeliver Sy_S hΔs tW htWc
    ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) htWt hRootsT) hParent
    (hAdvQ'.mono (le_trans htWt htTR)) (hCommittees.mono M hcT) hAnc₂ hGSTs hsc.le hChainSm hInv hLocks hLocks₀ hOld
    hCachesW hRootsU hAdvQU hCachesU hFrames hs' hHoldV hp' hHoldP ⟨i, hlbl, hsent⟩ hCol
  have hTips := (confirmed_tips_preceq_handover_upTo M F U Fx) S A x R GST s₀
    (anchorCW S tGAT) i₂ (M.chainStateOf S.C B₀).h s B E_S hNet hSkew hRedeliver Sy_S hΔs
    ((GoldilocksCorrectness.Record.Proofs.Executions.RootsNameBlocksUntil.mono M) (by exact_mod_cast hct) hRootsT)
    hParent (hAdvQ'.mono (by exact_mod_cast hcT)) (hCommittees.mono M hcT) hAnc₂ hGSTs hsc.le hChainSm hInv hLocks
    hLocks₀ hOld (fun j u h1 h2 hu => hCachesJ j u h1 (le_trans h2 hcb₀R) hu) hRootsU hAdvQU hCachesU hLatest hs'
    hHoldV hp' hHoldP ⟨i, hlbl, hsent⟩ hCol
  have hHand : HandoverFactsOfChainBlock M S A x tW s B (M.chainStateOf S.C B₀).h
      (M.supportCutoff S.C (s₀ + 1)) tAwakeEnd := by
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hSix
    exact ⟨h1, h2, h3, h4, h5, h6, fun v T' P hv hTE hT _ hP => hTips v T' P hv (le_trans hx2 hTE) hT hP⟩
  -- Lemma 105
  exact (confirmedPersists_throughPeriod_until M F U Fx) S A x R GST s B
    (M.chainStateOf S.C B₀).h (M.supportCutoff S.C (s₀ + 1)) (anchorCW S tGAT) tAwakeEnd b₀ b₁ t T hTt hTk
    E hNet hSkew hRedeliver E_F hNet_F hSkew_F Sy Sy_F hΔs hParent hAdvQ' hCommittees hAncS
    ((gst_sync_succ_of_top_of_clock_nonneg M F U) S A x GST tGAT tAwakeEnd m s r hGST hA0 hB0 hΔs hSeq hs)
    hb₀ hb hb₁ hHold (hDelT B) (hcm _ _ (by omega)) tW htW hHand hWin hRootsT

open Classical in
/-- **The asynchrony top statement, read forever.** The proof; the audited statement is in
`Statements/Executions/AsyncResilienceStatements.lean`.

Route: when the root collision at an honest round opening slot or a root collision among held blocks at some
time `t` occurred, the first two disjuncts. Otherwise, for a proposal `B` of the hand-over slot
with no root collision at its proposal, `confirmedPersists_asyncPeriod_until` at every time `t`
leaves only its last disjunct, so `ConfirmedPersistsBetween M S Sched x s tAwakeEnd b₀ t` and
`FinalizedCompatibleBetween M S Sched x s tAwakeEnd b₀ t` hold at every `t`, which are the unbounded
forms (`confirmedPersistsFrom_iff`, `finalizedCompatibleFrom_iff`).

A configuration in the hand-over window: some configuration's real time is
at least the hand-over cutoff `M.supportCutoff S.C (s + 1)` and at most `ΔClockBehind` after it, where the hand-over
facts' third to fifth clauses say something; Lemma 101's step and the induction's base read the fifth
clause there.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous outside the period; `tGAT`, `tAwakeEnd`: the start and end of the healing
  phase; `m`: the index of the last honest round opening slot; `r`: the rounds of the honest round opening slots; `s`: the hand-over
  slot; `b₀`, `b₁`: the start and the end of the period.

Read aloud: after the healing phase, a digest collision hit an honest round opening slot's proposal, or two
blocks honest validators hold at some time share a root, or, for every block `B` the hand-over
slot's proposer puts on the wire at the start of its slot, `B` collides by root with a block the
proposer held, or every block confirmed from `tAwakeEnd` to `B`'s update persists forever, from `b₀`
on, at every validator that ran that update, and no honest validator ever finalizes a conflicting
block from `b₀` on. -/
theorem confirmedPersists_asyncPeriod (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd m : ℕ) (r : ℕ → ℕ) (s b₀ b₁ : ℕ)
    (hGST : GST ≤ tGAT)
    {Δs Δs_F : ℕ}
    -- blocks and Goldfish votes are delivered within `Δ` of the later of their time and `GST` when that
    -- is at or before `b₀`, and of the latest of their time, `b₁` and `GST` otherwise; attestations
    -- likewise within `Δ_F`
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryOutside A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks b₀ b₁) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {ΔNet_F : ℕ} (E_F : EnvFactsDeliveryOutside A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks b₀ b₁) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)
    -- what an honest active validator would serve at `t` reaches every validator active from `t`
    -- within `Δs` (`Δs_F` for attestations) of the later of `t` and `GST` when that is at or before
    -- `b₀`, and of the latest of `t`, `b₁` and `GST` otherwise
    (Sy : SyncedWithinOutside A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST b₀ b₁)
    (Sy_F : SyncedWithinOutside A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST b₀ b₁)
    -- the trace is wake-shaped; the sync delay is at most the slow window less three delays
 (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hΔs_F : (Δs_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S ∨ (Δs_F : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind ≤ 4 * Δ S * S.C.k)
    -- for each honest round opening slot, every validator outside the adversary set at the support cutoff of the slot
    -- after its first slot is active through the attestations' sync delay after the later of that first slot's duty
    -- window's start and `GST`
    (hHoldF : ∀ i, i < m → ∀ v, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (r i * S.C.R + 1)) →
      v ∈ A.activeThroughout x ((max (M.dutyWindowStart S.C (r i * S.C.R)) GST : ℕ) : ℝ)
        (((max (M.dutyWindowStart S.C (r i * S.C.R)) GST : ℕ) : ℝ) + Δs_F))
    (hParent : ParentHeldAtDelivery M x)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : CommitteeSleepiness M S A x (anchorCW S tGAT))
    -- every updater of a slot from the first honest round opening slot `r 0 * S.C.R` on is active for the
    -- sync delay after the real time of its own tick to the support cutoff of the next slot
    --
    (hStay : ∀ σ : ℕ, r 0 * S.C.R ≤ σ → ∀ u ∈ updaterAt M S A x σ,
      u ∈ A.activeThroughout x (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))))
        (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))) + Δs))
    (hSeq : HonestOpeningSeq M S A x r m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hOpenings : OpeningsOutsideWaitsAndWindows S r m)
    (hAdvQ : ∀ t : ℕ, A.AdversaryFewerThanTwoThirdsUntil x (validator_count V) t)
    (hs : tAwakeEnd < M.slotStart S.C s)
    (hp : S.P.proposer s ∈ A.activeThroughoutToTick x (Goldilocks.proposal_window_start S.C s)
        (M.supportCutoff S.C (s + 1)) ∧
      S.P.proposer s ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) ∪
        Finset.univ.filter (fun u => ∃ (k : ℕ) (w : V),
          x.lbl k = Event.tick w (M.supportCutoff S.C (s + 1)) ∧ w ∉ A.corrupted k ∧ u ∈ A.corrupted k))
    -- the honest voters of slots `s - 1` and `s` are active through the sync delay after Lemma 12's read time of
    -- their slot
    (hHoldV : ∀ s' : ℕ, s - 1 ≤ s' → s' ≤ s → ∀ u ∈ honestActiveAt M S A x s', u ∈ S.P.committee s' →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    -- the proposer of slot `s` is active through the sync delay after `M.slotStart S.C s - max (Δ S) Δs`
    (hHoldP : S.P.proposer s ∈ A.activeThroughout x ((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hb₀ : M.supportCutoff S.C (s + 1) ≤ b₀)
    -- every validator's tick to the hand-over update is at a real time at most `b₀`
    (hTicks₀ : ∀ (k : ℕ) (u : V), x.lbl k = Event.tick u (M.supportCutoff S.C (s + 1)) → (x.time k : ℝ) ≤ b₀)
    (hb : b₀ ≤ b₁)
    -- some configuration's real time lies in the hand-over facts' window
    (hWin : ∃ j₀ : ℕ, ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) ≤ x.time j₀ ∧ x.time j₀ ≤ ((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) + ΔClockBehind)
    (hb₁ : b₁ + max (Δ S) Δs ≤ M.voteTime S.C (s + S.C.k))
    (hHold : HoldersOutweighWhereOwed M S A x s Δs b₀ b₁)
    (hDelT : ∀ B : Block V, DelTLine M S A x s B b₀ b₁ Δs) :
    RootCollisionAtOpening M S A x r m ∨ (∃ t : ℕ, RootCollisionHeldBy M S A x t) ∨
      ∀ (i : ℕ) (B : Block V), x.lbl i = Event.tick (S.P.proposer s) (M.slotStart S.C s) →
        (⟨S.P.proposer s, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
          x.sent (i + 1) - x.sent i →
        RootCollisionAtProposal M S A x s B ∨
          (ConfirmedPersistsFrom M S A x s tAwakeEnd b₀ ∧
            FinalizedCompatibleFrom M S A x s tAwakeEnd b₀) := by
  -- at every `t`, the premises counted up to `⌈t + ΔClockAhead⌉₊`
  have hA0 := E.ahead_nonneg
  -- at every slot start `t₂ = M.slotStart S.C t ≥ t`, at which no slot's update is half run
  have h := fun t : ℕ => (confirmedPersists_asyncPeriod_until M F U Fx) S A x R GST tGAT tAwakeEnd m r
    s b₀ b₁ hGST E hNet hSkew hRedeliver E_F hNet_F hSkew_F Sy Sy_F hΔs hΔs_F hHoldF hParent hThird hAwake hActive
    (M.slotStart S.C t) ⌈((M.slotStart S.C t : ℕ) : ℝ) + ΔClockAhead⌉₊
    (by have := Nat.le_ceil (((M.slotStart S.C t : ℕ) : ℝ) + ΔClockAhead)
        exact_mod_cast (show ((M.slotStart S.C t : ℕ) : ℝ) ≤ ⌈((M.slotStart S.C t : ℕ) : ℝ) + ΔClockAhead⌉₊ by linarith))
    ((GoldilocksCorrectness.Record.Proofs.Executions.tick_clock_le_of_time_le M F) E (Nat.le_ceil _))
    ((exists_ticksBy_ge M F U) S x E hSkew t).2
    (committeeSleepinessUntil_of_committeeSleepiness M S A x _ _ hCommittees) (fun σ h1 _ => hStay σ h1) hSeq hOpenings
    (hAdvQ _) hs hp hHoldV hHoldP hb₀ hTicks₀ hb hWin
    hb₁ hHold hDelT
  by_cases hO : RootCollisionAtOpening M S A x r m
  · exact Or.inl hO
  by_cases hH : ∃ t : ℕ, RootCollisionHeldBy M S A x t
  · exact Or.inr (Or.inl hH)
  refine Or.inr (Or.inr fun i B hl hsent => ?_)
  by_cases hP : RootCollisionAtProposal M S A x s B
  · exact Or.inl hP
  have hall : ∀ t : ℕ, ConfirmedPersistsBetween M S A x s tAwakeEnd b₀ t ∧
      FinalizedCompatibleBetween M S A x s tAwakeEnd b₀ t := by
    intro t
    have htt₂ := ((exists_ticksBy_ge M F U) S x E hSkew t).1
    rcases h t with h1 | h1 | h1
    · exact absurd h1 hO
    · exact absurd ⟨_, h1⟩ hH
    · rcases h1 i B hl hsent with h2 | ⟨h2, h3⟩
      · exact absurd h2 hP
      -- the readings up to the slot start `t₂ ≥ t` give the readings up to `t`
      exact ⟨fun v i' P h4 h5 h6 h7 v' j h8 h9 h10 h11 h12 h13 =>
          h2 v i' P h4 h5 h6 h7 v' j h8 h9 h10 h11 h12 (le_trans h13 (by exact_mod_cast htt₂)),
        fun v i' P h4 h5 h6 h7 v' j h8 h9 h10 h11 =>
          h3 v i' P h4 h5 h6 h7 v' j h8 h9 h10 (le_trans h11 (by exact_mod_cast htt₂))⟩
  exact Or.inr ⟨((GoldilocksCorrectness.Record.Statements.Executions.confirmedPersistsFrom_iff M) S A x s tAwakeEnd b₀).2 fun t => (hall t).1,
    ((GoldilocksCorrectness.Record.Statements.Executions.finalizedCompatibleFrom_iff M) S A x s tAwakeEnd b₀).2 fun t => (hall t).2⟩

end GoldilocksCorrectness.Record.Proofs.Executions

