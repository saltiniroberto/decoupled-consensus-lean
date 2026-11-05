module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.PeriodFastSupport

@[expose] public section

/-!
# PeriodFastSupportStatements, over a model

The statements of `GoldilocksCorrectness/Statements/Executions/PeriodFastSupportStatements.lean`,
over a model `M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: a fast block has an
honest active supporter; the theorem of the same name of
`Record/Restated/Proofs/Executions/PeriodFastSupport.lean`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (slotStart voteTime supportCutoff)

namespace GoldilocksCorrectness.Record.Statements.Executions

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor hMax le_hMax IsEntry VoterTreeAt JustifiedInTree AnchorAt)
open GoldilocksCorrectness.Record.Statements.Routines (SupportVotes EarlyVotes)

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

/-- **Kit fact K2: a fast block has an honest active supporter who held it.** In an execution
that reaches every time, with permanent corruption and no vote cast in an honest validator's
name, with roots naming blocks among what honest validators hold up to
`M.supportCutoff S.C (s'' + 1)` and committee sleepiness from `anchor`, at most the start of slot
`s'' + 1`: for every fast block `D` of the state right after the tick at
`M.supportCutoff S.C (s'' + 1)` of an updater `u'` of slot `s''`, some member `v` of the committee
of `s''` in `honestActiveAt M S Sched s''` held, before its tick at the vote time of `s''`, a block
`H_v` that is `D` or a descendant of `D`.

Why: `D` passed the fast test of the update of slot `s'' + 1`: the committee of `s''` is at most
twice `D`'s score, the equivocators and the supporters of `D` among the votes counted. Committee
sleepiness makes the committee members outside `honestActiveAt M S Sched s''` fewer than half of the
committee, so some equivocator or supporter is in it (`fast_test_fails_of_minority`). It is no
equivocator (one vote per honest owner); as a supporter, its counted vote names, by its head, a
block of `u'`'s frame tree that is `D` or a descendant of `D`, and that vote is the one its tick
sent at the vote time of `s''`, for a block `H_v` it held then (Lemma 14); one root, one block.



The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `anchor`: the time from which
  committee sleepiness holds; `s''`: the slot of the votes; `u'`: the updater.

Read aloud: a block an honest updater fast-confirmed at the update of slot `s''` is an ancestor of,
or is, a block some honest active committee member of `s''` held at the vote time of `s''`. -/
theorem fast_block_has_honest_supporter (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (anchor s'' : ℕ) (u' : V)
    -- the execution reaches every time
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    -- nobody votes in an honest validator's name
    (hOwner : VotesCastByOwner M A x)
    -- roots name blocks among what honest validators hold up to the cutoff of slot `s'' + 1`
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C (s'' + 1)))
    -- committee sleepiness from `anchor` for the slots whose update is at most `M.supportCutoff S.C (s'' + 1)`
    (hSleepK : CommitteeSleepinessUntil M S A x anchor (M.supportCutoff S.C (s'' + 1))) (hAnchor : anchor ≤ M.slotStart S.C (s'' + 1))
    -- `u'` is awake and honest through the update of slot `s''`
    (hu' : u' ∈ updaterAt M S A x s'') :
    ∀ D ∈ (x.tickOutput u' (M.supportCutoff S.C (s'' + 1))).fastBlocks,
      ∃ v ∈ honestActiveAt M S A x s'' ∩ S.P.committee s'',
        ∃ H_v ∈ (x.tickInput v (M.voteTime S.C s'')).tree, D.AncestorEq H_v :=
  (GoldilocksCorrectness.Record.Proofs.Executions.fast_block_has_honest_supporter M F U) S A x R
    anchor s'' u' E hSkew hOwner hRoots hSleepK hAnchor hu'

end GoldilocksCorrectness.Record.Statements.Executions

