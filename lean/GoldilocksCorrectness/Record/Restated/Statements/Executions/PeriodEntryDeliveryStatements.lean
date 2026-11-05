module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.PeriodEntryDelivery
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# PeriodEntryDeliveryStatements, over a model

The statements of `GoldilocksCorrectness/Statements/Executions/PeriodEntryDeliveryStatements.lean`,
over a model `M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: the certified entry
reaches the voter before the view freeze, namely the fast blocks an updater of slot `s'` holds right
after its update are ancestors of, or are, the confirmation it saved for `s'`, and a certified block
of a chain an honest active voter holds before its vote was in the voter's tree before its view
froze; each is the theorem of the same name of
`Record/Restated/Proofs/Executions/PeriodEntryDelivery.lean`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (voteTime supportCutoff viewFreeze)

namespace GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor hMax le_hMax IsEntry VoterTreeAt JustifiedInTree AnchorAt)
open GoldilocksCorrectness.Record.Statements.Routines (ProgressCertOn)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- **The fast blocks of an update are ancestors of its saved confirmation.** In an execution
that reaches every time, with permanent corruption: for an updater `u` of slot `s'`, when the
state right after its tick at `M.supportCutoff S.C (s' + 1)` has saved `C'` as the confirmation of
slot `s'`, every fast block of that state is `C'` or an ancestor of `C'`.

Why: the tick ran the confirmation update of slot `s' + 1`, whose answer's saved confirmation and
fast blocks are the state's; the update's fast blocks are blocks of its path, the ancestors of the
confirmation it saves (`fast_blocks_ancestorEq_saved`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s'`: the slot; `u`: the updater;
  `C'`: the saved confirmation.

Read aloud: an updater's fast blocks of slot `s'` are on the chain of the confirmation it saved
for `s'`. -/
theorem fast_blocks_ancestorEq_saved_of_updater (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s' : ℕ) (u : V) (C' : Block V)
    -- the execution reaches every time
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    -- a validator in the adversary set stays in it
    -- `u` is awake and honest through the update of slot `s'`
    (hu : u ∈ updaterAt M S A x s')
    -- the update saved `C'` as the confirmation of slot `s'`
    (hSaved : (x.tickOutput u (M.supportCutoff S.C (s' + 1))).savedConfirmation s' = some C')
      :
    ∀ D ∈ (x.tickOutput u (M.supportCutoff S.C (s' + 1))).fastBlocks, D.AncestorEq C' :=
  (GoldilocksCorrectness.Record.Proofs.Executions.fast_blocks_ancestorEq_saved_of_updater M F U) S
    A x R s' u C' E hu hSaved

/-- **Kit fact K3: the certified entry reaches the voter before its view freezes.** Under the
hypotheses `P` of the period after the hand-over slot `s` (with `GST` at or before the vote time
of slot `s + 1`), and with roots naming blocks among what honest validators hold up to the vote
time of slot `s'`, `s + 2 ≤ s'`: take a slot `s'` whose previous slot's votes were not owed inside
the period, a validator `u ∈ honestActiveAt M S Sched s'`, a block `Y` that `u` holds before its
tick at the vote time of `s'`, and a progress certificate on the chain of `Y` at the height `h`
naming the block `T`, `T` an ancestor of `Y` or `Y`. When `T`'s chain-state height is greater than
`B`'s and `u`'s finalized block before the view freeze of slot `s' − 1` is compatible with `T`, then
`u` held `T` before that view freeze.

Why: the certificate's honest attester `uₐ` held `T` before its tick at
`M.supportCutoff S.C (sₐ + 1)`, with `sₐ + 1 ≤ s' − 1` (K1, `cert_entry_held_by_attester`). When the
previous votes were due after the period, `T` reaches `u` one delay after
`M.supportCutoff S.C (s' − 1)`, the view freeze. When they were due before it, `T` reaches `u` one
delay after `M.voteTime S.C (s' − 1)`, from the attester when `sₐ + 1 < s' − 1`, and otherwise from
an honest active supporter at slot `sₐ` of the fast block `T` descends from (K2,
`fast_block_has_honest_supporter`); the case `sₐ = s` is empty, the hand-over update's fast blocks
being ancestors of `B`, of height at most `B`'s.

 every
hypothesis is read.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `P`: the hypotheses of the period; `s'`: the slot of the vote; `u`: the voter; `Y`: the held
  block; `T`: the certified block; `h`: its height.

Read aloud: at a slot whose previous votes were not owed inside the period, a certified block of a
chain an honest active voter holds before its vote, of chain-state height greater than `B`'s and
compatible with the voter's finalized block, was in the voter's tree before its view froze.



Read aloud: a certified block on the chain of a block the voter's vote tick reads, compatible
with the finalized block its view-freeze tick reads, is in the tree that tick reads. -/
theorem cert_entry_held_before_freeze (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind tW : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) {GST s : ℕ} {B : Block V}
      {H t₀ anchor tAwakeEnd b₀ b₁ Δs_F : ℕ}
    -- the hypotheses of the period, with `GST` at or before the vote time of slot `s + 1`
    (P : AsyncHypsOfChainBlockGSTBeforeVotes M S A x GST s B H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet tW)
    (s' : ℕ) (u : V)
    (Y T : Block V) (h : Height)
    -- roots name blocks among what honest validators hold up to the later of the vote time of `s'` and the real
    -- time of `u`'s tick to it
    (hRoots : RootsNameBlocksUntil M A x (max ((M.voteTime S.C s' : ℕ) : ℝ) (x.time (x.tickStep u (M.voteTime S.C s')))))
    -- the slot is at least two after the hand-over slot
    (hs' : s + 2 ≤ s')
    -- the votes of slot `s' − 1` were not owed inside the period
    (hgood : ¬ VotesOwedInPeriod M S Δs b₀ b₁ s')
    -- `u` is awake through the duties of `s'` and honest at its update
    (hu : u ∈ honestActiveAt M S A x s')
    -- `u` holds `Y` before its tick at the vote time of `s'`
    (hY : Y ∈ (x.tickInput u (M.voteTime S.C s')).tree)
    -- `T` is an ancestor of `Y`, or `Y`
    (hTY : T.AncestorEq Y)
    -- the chain of `Y` carries a progress certificate at `h` naming `T`
    (hJ : ProgressCertOn M Y h T)
    -- `T` is higher than `B`
    (hTB : (M.chainStateOf S.C B).h < (M.chainStateOf S.C T).h)
    -- `u`'s finalized block before the view freeze of `s' − 1` is compatible with `T`
    (hF : (x.tickInput u (M.viewFreeze S.C (s' - 1))).finalized.compatible T = true) :
    T ∈ (x.tickInput u (M.viewFreeze S.C (s' - 1))).tree :=
  (GoldilocksCorrectness.Record.Proofs.Executions.cert_entry_held_before_freeze M F U Fx R E hNet hSkew hRedeliver hΔs)
    ((GoldilocksCorrectness.Record.Proofs.Executions.AsyncHypsOfChainBlockGSTBeforeVotes.toUntil M F) P (M.supportCutoff S.C s')) s' u Y T
    h (by
      have h1 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S s'
      have hΔ : (1 : ℝ) ≤ Δ S := by exact_mod_cast GoldilocksCorrectness.Proofs.Routines.one_le_Δ S
      have hA0 := E.ahead_nonneg
      have hB0 := E.behind_nonneg
      refine max_le (by rw [h1]; push_cast; linarith) ?_
      by_cases hk : ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s')
      · have := (E.tick_active _ u _ (x.lbl_tickStep hk)).2.2
        rw [h1]; push_cast; linarith
      · unfold Trace.tickStep
        rw [dif_neg hk, R.time_zero]
        positivity) hRoots hs' hgood hu hY hTY hJ hTB hF

end GoldilocksCorrectness.Record.Statements.Executions

