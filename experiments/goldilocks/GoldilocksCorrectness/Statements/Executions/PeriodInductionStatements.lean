module
public import GoldilocksCorrectness.Proofs.Executions.PeriodInduction

@[expose] public section

/-!
Every landed definition and statement of record stays byte-identical; Proved in `GoldilocksCorrectness/Proofs/Executions/PeriodInduction.lean`.

- `AsyncHypsOfChainBlockGSTBeforeVotes.toAsyncHypsOfChainBlock`, `.toAsyncHyps`: the copied bundle
  gives the landed bundles.

 Statement 2
(`confirmation_extends_B_of_timely_votes`), the original of statement 2′
`confirmation_compatible_of_timely_votes` (`Statements/Executions/PeriodInductionCompatStatements.lean`),
was deleted then.
-/

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (supportCutoff)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-! ## The copied bundle -/

/-- **The bundle with `GST` before the hand-over votes gives the bundle over the copied clauses.**
Every field is kept, and `GST ≤ b₀` follows from `GST ≤ voteTime S (s + 1)`, since the vote time of
slot `s + 1` is before its support cutoff, which is at or before `b₀`.

So every step lemma over `AsyncHypsOfChainBlock` (`attestations_step_ofHeldEntry`, …) is called
with `P.toAsyncHypsOfChainBlock`, with no copy of it.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `s`, `B`, `H`, `t₀`,
  `anchor`, `b₀`, `b₁`: the parameters of the bundle; `P`: the copied hypotheses.

Read aloud: the hypotheses with `GST` before the hand-over votes are at least the hypotheses with
`GST` before the period. -/
theorem AsyncHypsOfChainBlockGSTBeforeVotes.toAsyncHypsOfChainBlock {S : Setup V}
    {Sched : Schedule V} {x : AtomicExec (protocol S) Sched} {GST s : ℕ} {B : Block V}
    {H t₀ anchor tAwakeEnd b₀ b₁ : ℕ}
    (P : AsyncHypsOfChainBlockGSTBeforeVotes S Sched x GST s B H t₀ anchor tAwakeEnd b₀ b₁) :
    AsyncHypsOfChainBlock S Sched x GST s B H t₀ anchor tAwakeEnd b₀ b₁ :=
  GoldilocksCorrectness.Proofs.Executions.AsyncHypsOfChainBlockGSTBeforeVotes.toAsyncHypsOfChainBlock
    P

/-- **The bundle with `GST` before the hand-over votes gives `AsyncHyps`.** Through
`AsyncHypsOfChainBlock` and its own conversion `AsyncHypsOfChainBlock.toAsyncHyps`.



The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `s`, `B`, `H`, `t₀`,
  `anchor`, `b₀`, `b₁`: the parameters of the bundle; `P`: the copied hypotheses.

Read aloud: the hypotheses with `GST` before the hand-over votes are at least the original
hypotheses. -/
theorem AsyncHypsOfChainBlockGSTBeforeVotes.toAsyncHyps {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (protocol S) Sched} {GST s : ℕ} {B : Block V} {H t₀ anchor tAwakeEnd b₀ b₁ : ℕ}
    (P : AsyncHypsOfChainBlockGSTBeforeVotes S Sched x GST s B H t₀ anchor tAwakeEnd b₀ b₁) :
    AsyncHyps S Sched x GST s B H t₀ anchor tAwakeEnd b₀ b₁ :=
  GoldilocksCorrectness.Proofs.Executions.AsyncHypsOfChainBlockGSTBeforeVotes.toAsyncHyps P
end GoldilocksCorrectness.Statements.Executions
