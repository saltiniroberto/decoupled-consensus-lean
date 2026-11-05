module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.PeriodInduction
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# PeriodInductionStatements, over a model

The statements of `GoldilocksCorrectness/Statements/Executions/PeriodInductionStatements.lean`, over
a model `M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: the bundle
`AsyncHypsOfChainBlockGSTBeforeVotes` gives the bundles `AsyncHypsOfChainBlock` and `AsyncHyps`; the
theorems of the same names of `Record/Restated/Proofs/Executions/PeriodInduction.lean`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (supportCutoff)

namespace GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery)

open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor hMax le_hMax IsEntry VoterTreeAt JustifiedInTree AnchorAt)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-! ## The copied bundle -/

/-- **The bundle with `GST` before the hand-over votes gives the bundle over the copied clauses.**
Every field is kept, the delivery promise at the network delay giving it at the slot delay when
`ΔNet ≤ Δ S` (a deadline no earlier, `deadlineOutsideR_mono_delay`), and `GST ≤ b₀` follows from `GST ≤ M.voteTime S.C (s + 1)`, since the vote time
of slot `s + 1` is before its support cutoff, which is at or before `b₀`.

So every step lemma over `AsyncHypsOfChainBlock` (`attestations_step_ofHeldEntry`, …) is called
with `P.toAsyncHypsOfChainBlock`, with no copy of it.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `s`, `B`, `H`, `t₀`,
  `anchor`, `b₀`, `b₁`: the parameters of the bundle; `P`: the copied hypotheses;
  `hΔn`: the network delay `ΔNet` is at most the slot delay `Δ S`.

Read aloud: when the network delay is at most the slot delay, the hypotheses with `GST` before the
hand-over votes are at least the hypotheses with `GST` before the period. -/
theorem AsyncHypsOfChainBlockGSTBeforeVotes.toAsyncHypsOfChainBlock
    (U : UniformSchedule M.toSlotLayout)
    {S : Setup V}
    {A : Activity V} {x : Trace V (NamedObject V) M.N} {GST s : ℕ} {B : Block V}
    {H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F : ℕ}
    {release ΔRedeliver} {ΔClockAhead ΔClockBehind tW : ℝ} {ΔNet : ℕ} (P : AsyncHypsOfChainBlockGSTBeforeVotes M S A x GST s B H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F release ΔRedeliver ΔClockAhead ΔClockBehind ΔNet tW)
    (hΔn : ΔNet ≤ Δ S) :
    AsyncHypsOfChainBlock M S A x GST s B H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F release ΔRedeliver ΔClockAhead ΔClockBehind tW :=
  (GoldilocksCorrectness.Record.Proofs.Executions.AsyncHypsOfChainBlockGSTBeforeVotes.toAsyncHypsOfChainBlock M F U)
    P hΔn

/-- **The bundle with `GST` before the hand-over votes gives `AsyncHyps`.** Through
`AsyncHypsOfChainBlock` and its own conversion
`AsyncHypsOfChainBlock.toAsyncHyps`.



The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `s`, `B`, `H`, `t₀`,
  `anchor`, `b₀`, `b₁`: the parameters of the bundle; `P`: the copied hypotheses.

Read aloud: the hypotheses with `GST` before the hand-over votes are at least the original
hypotheses. -/
theorem AsyncHypsOfChainBlockGSTBeforeVotes.toAsyncHyps (U : UniformSchedule M.toSlotLayout)
    {S : Setup V} {A : Activity V}
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind tW : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) {GST s : ℕ} {B : Block V}
      {H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F : ℕ}
    (P : AsyncHypsOfChainBlockGSTBeforeVotes M S A x GST s B H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind ΔNet tW) :
    AsyncHyps M S A x GST s B H t₀ anchor tAwakeEnd b₀ b₁ Δs Δs_F (releaseOf M S.C) ΔRedeliver ΔClockAhead ΔClockBehind tW :=
  (GoldilocksCorrectness.Record.Proofs.Executions.AsyncHypsOfChainBlockGSTBeforeVotes.toAsyncHyps M F U R E)
    hNet hSkew hRedeliver P
end GoldilocksCorrectness.Record.Statements.Executions
