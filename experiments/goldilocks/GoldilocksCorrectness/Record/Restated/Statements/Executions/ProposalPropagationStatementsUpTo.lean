module
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.ProposalPropagationStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.AsyncDeliveryStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma22UpTo
public import GoldilocksCorrectness.Statements.Executions.ProposalPropagationStatements
public import GoldilocksCorrectness.Statements.Executions.AsyncDeliveryStatements
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# ProposalPropagationStatementsUpTo, over a model

The statement of
`GoldilocksCorrectness/Statements/Executions/ProposalPropagationStatementsUpTo.lean` over a model
`M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: Lemma 22 with the delivery
premises up to the vote time, an honest proposal reaches every validator awake and honest for the
next delay. It is the theorem of `Record/Restated/Proofs/Executions/Lemma22UpTo.lean`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime)

namespace GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDeliveryUpTo)

open GoldilocksCorrectness.Statements.Executions (acObject)

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

/-- **Lemma 22, an honest proposal reaches the next slot's voter.** In an execution where every
time is reached, corruption is permanent, blocks and Goldfish votes are delivered within `Δ`
after `GST` (synchrony from the receiver's wake, and catch-up on wake),
a root names one block among what honest validators hold, and a block reaches a validator
only once it holds the parent: if `GST` is at most the vote time of slot `s`; `p` is honest at the
start `t₁` of slot `s + 1`; `w` is active from a time `tStart`, more than `ΔClockAhead + ΔClockBehind` before `t₁`, up to its tick to
the vote time `t₃` of slot `s + 1`; the step `i` is the tick of every awake validator at `t₁`, put
`p`'s block `B` on the wire, and left `p` holding `B`; and `w`'s finalized block on the node state its tick to `t₃` starts from
is compatible with `B` — then `w` holds `B` in that node state.

This is the second half of `hBw`'s discharge; the tick step `i` is named, rather than `lem20`'s
existential `hPropose`, so that the state `x[i + 1][p].st` it leaves can be spoken of.



Why: `p`'s send is honest and its block is in `p`'s tree right after it, so the block passed every
test `w`'s `on_block` makes that reads the block alone; synchrony delivers it to `w` strictly
before `t₁ + Δ = t₃`, at a step where `w`'s clock is current, `w` holds the parent
(`ParentHeldAtDelivery`, the block being compatible with `w`'s finalized block), and a block of
`w`'s tree with `B`'s root would be `B` itself. So `w` holds `B` before `t₃`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `Sched`: the schedule; `x`: the execution; `GST`: the time from which the
  network is synchronous; `s`: the slot before the proposal's;
- `i`: the step of `p`'s tick at the start of slot `s + 1`; `B`: the block; `p`: the proposer;
  `w`: the voter of slot `s + 1`.

Read aloud: a block an honest proposer put on the wire at its tick at the start of slot `s + 1`,
and holds right after it, is held, in the node state its tick to the vote time of slot `s + 1` starts from, by every validator
active from more than both clock bounds before the start of slot `s + 1` up to that tick whose finalized
block there is compatible with it.

Roots name blocks until the real time of `w`'s tick to the vote time of slot `s + 1`: the proof
compares the block `w` holds at the delivery of `B`, a step before that tick, with `B`, which `p`
holds right after its tick. The proposer's honesty is read at its own tick `i`
(`tick_active`); no honesty of `p` at a real time is asked.

Restated with the delivery premises up to `M.voteTime S.C (s + 1)`: the proposal of slot `s + 1`
reaches `w` by then (`mem_T_before_of_send_upTo`). -/
theorem lem22_proposal_held_by_voter_upTo (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s i : ℕ) (B : Block V) (p w : V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.voteTime S.C (s + 1))) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    -- roots name blocks until the real time of `w`'s tick to the vote time of slot `s + 1`
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep w (M.voteTime S.C (s + 1)))))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ M.voteTime S.C s)
    -- `w`'s window starts at `tStart`, more than `ΔClockAhead + ΔClockBehind` before the start of slot `s + 1`, and
    -- ends at its tick to the vote time of slot `s + 1`
    (tStart : ℤ) (htStart : (tStart : ℝ) + ΔClockAhead + ΔClockBehind < M.slotStart S.C (s + 1))
    (hw : w ∈ A.activeThroughoutToTick x tStart (M.voteTime S.C (s + 1)))
    -- `p`'s tick at the start of slot `s + 1` is the step `i`, put `B` on the wire, and left
    -- `p` holding `B`
    (hl : x.lbl i = Event.tick p (M.slotStart S.C (s + 1)))
    (hsent : (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
      x.sent (i + 1) - x.sent i)
    (hBp : B ∈ (x.st (i + 1) p).tree)
    -- `w`'s finalized block before its vote is compatible with `B`
    (hF : (x.tickInput w (M.voteTime S.C (s + 1))).finalized.compatible B = true) :
    B ∈ (x.tickInput w (M.voteTime S.C (s + 1))).tree := by
  exact (GoldilocksCorrectness.Record.Proofs.Executions.lem22_proposal_held_by_voter_upTo M F U) S A x R GST s i B
    p w E hNet hSkew hRedeliver hRoots hParent hGST (GoldilocksCorrectness.Record.Proofs.Executions.tick_window_ahead_of_activeThroughoutToTick_int M x R E hw htStart) hl hsent hBp hF

end GoldilocksCorrectness.Record.Statements.Executions

