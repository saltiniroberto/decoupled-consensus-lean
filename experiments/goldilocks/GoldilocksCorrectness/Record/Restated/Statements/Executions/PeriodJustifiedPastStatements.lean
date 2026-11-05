module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.PeriodJustifiedPast
public import GoldilocksCorrectness.Statements.Routines.FGStateStatements
public import GoldilocksCorrectness.Statements.Routines.ForkChoiceStatements
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# PeriodJustifiedPastStatements, over a model

The statements of `GoldilocksCorrectness/Statements/Executions/PeriodJustifiedPastStatements.lean`,
over a model `M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: a block compatible
with `B` whose chain-state height is greater than `B`'s is `B` or a descendant of `B` (as stated on
`Record/Restated/Proofs/Routines/ChainStateOf.lean`), and a justification past the hand-over block
`B` held by an honest active voter of slot `σ` reaches every honest active voter of the timely slot
`σ + 1` whose finalized block is `B` or an ancestor of `B`, before its vote (as stated on
`Record/Restated/Proofs/Executions/PeriodJustifiedPast.lean`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (voteTime)

namespace GoldilocksCorrectness.Record.Statements.Executions
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

variable {V : Type} [DecidableEq V] [Fintype V]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- **A block on `B`'s side higher than `B` descends from `B`.** A block compatible with `B` whose
chain-state height is greater than `B`'s is `B` or a descendant of `B`.

Why: an ancestor of `B` has a chain-state height at most `B`'s.

The variables:
- `M`: the model; `F`: its facts;
- `C`: the parameters; `B`: the block; `E`: the block compatible with `B`.

Read aloud: a block on `B`'s side that is higher than `B` is `B` or a descendant of `B`. -/
theorem descends_of_compatible_higher (C : Config) {B E : Block V}
    -- `E` is compatible with `B`
    (hc : E.AncestorEq B ∨ B.AncestorEq E)
    -- `E` is higher than `B`
    (hh : (M.chainStateOf C B).h < (M.chainStateOf C E).h) :
    B.AncestorEq E :=
  (GoldilocksCorrectness.Record.Proofs.Routines.descends_of_compatible_higher M F) C hc hh

/-- **A justification past `B` spreads in one delay.** Under the hypotheses `P` of the period
after the hand-over slot `s` (with `GST` at or before the vote time of slot `s + 1`), with roots
naming blocks among what honest validators hold up to the vote time of slot `σ + 1`: take a slot
`σ ≥ s + 1` such that the votes of `σ` were not owed inside the period, a validator
`w ∈ honestActiveAt M S Sched σ` whose caches at its tick to the vote time of `σ` are compatible with
`B` with justification height at least `h(B) + 1`, and a validator
`u ∈ honestActiveAt M S Sched (σ + 1)` whose finalized block at its tick to the vote time of `σ + 1` is
`B` or an ancestor of `B`. Then `u`'s justification height at that tick is at least `h(B) + 1`. Each
state is read at the validator's own tick to the vote time.

Why: `w` holds a block `D` whose chain state carries `w`'s justification (the witness of its
caches), and `B ⪯ D`; `D` reaches `u` by its tick to `M.supportCutoff S.C σ` (the previous votes due
before the period) or to `M.viewFreeze S.C σ` (due after it), before its tick to `M.voteTime S.C (σ + 1)`;
`u`'s finalized block is an ancestor of `D`, and Lemma 57's cache bound makes `u`'s justification
height at least `D`'s.

 every
hypothesis is read.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `P`: the hypotheses of the period; `σ`: the slot of `w`'s vote; `w`: the voter justified past
  `B`; `u`: the voter of slot `σ + 1`.

Read aloud: when an honest active voter of slot `σ` has justified a block higher than `B`, every
honest active voter of the timely slot `σ + 1` whose finalized block is `B` or an ancestor of `B`
has too, at its tick to its vote time. -/
theorem justified_past_spreads (U : UniformSchedule M.toSlotLayout)
    {S : Setup V} {A : Activity V} [RootOrder]
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind tW : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k) {GST s : ℕ} {B : Block V}
      {H t₀ anchor tAwakeEnd b₀ b₁ Δs_F : ℕ}
    -- the hypotheses of the period, with `GST` at or before the vote time of slot `s + 1`
    (P : AsyncHypsOfChainBlockGSTBeforeVotes M S A x GST s B H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet tW)
    (σ : ℕ) (w u : V)
    -- roots name blocks among what honest validators hold up to the vote time of `σ + 1`
    (hRoots : RootsNameBlocksUntil M A x (M.voteTime S.C (σ + 1)))
    -- the slot is after the hand-over slot
    (hσ : s + 1 ≤ σ)
    -- the votes of slot `σ` were not owed inside the period
    (hgood : ¬ VotesOwedInPeriod M S Δs b₀ b₁ (σ + 1))
    -- `w` is awake through the duties of `σ` and honest at its update
    (hw : w ∈ honestActiveAt M S A x σ)
    -- `w`'s caches at its tick to the vote time of `σ` are compatible with `B`
    (hCw : CachesCompatibleWith M S B H (x.tickInput w (M.voteTime S.C σ)))
    -- `w` is justified past `B` at its tick to the vote time of `σ`
    (hjw : (M.chainStateOf S.C B).h + 1 ≤ (x.tickInput w (M.voteTime S.C σ)).justifiedHeight)
    -- `u` is awake through the duties of `σ + 1` and honest at its update
    (hu : u ∈ honestActiveAt M S A x (σ + 1))
    -- `u`'s finalized block at its tick to the vote time of `σ + 1` is `B` or an ancestor of `B`
    (hFu : (x.tickInput u (M.voteTime S.C (σ + 1))).finalized.AncestorEq B) :
    (M.chainStateOf S.C B).h + 1 ≤
      (x.tickInput u (M.voteTime S.C (σ + 1))).justifiedHeight :=
  (GoldilocksCorrectness.Record.Proofs.Executions.justified_past_spreads M F U R E hNet hSkew hRedeliver hΔs)
    ((GoldilocksCorrectness.Record.Proofs.Executions.AsyncHypsOfChainBlockGSTBeforeVotes.toUntil M F) P (M.voteTime S.C (σ + 1))) σ w u hRoots hσ
    hgood hw hCw hjw hu hFu

end GoldilocksCorrectness.Record.Statements.Executions

