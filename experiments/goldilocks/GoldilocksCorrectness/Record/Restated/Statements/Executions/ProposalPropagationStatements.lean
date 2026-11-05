module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma22
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# ProposalPropagationStatements, over a model

The statements of `GoldilocksCorrectness/Statements/Executions/ProposalPropagationStatements.lean`,
over a model `M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: Lemma 22a, an
honest proposer holds its own proposal by the vote time of its slot, and Lemma 22, the proposal
reaches every validator awake and honest for the next delay. Each is the theorem of
`Record/Restated/Proofs/Executions/Lemma22.lean`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime)

namespace GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery)

open GoldilocksCorrectness.Statements.Executions (acObject)

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

/-- **Lemma 22a, an honest proposer holds its own proposal.** In an execution where every time is
reached and corruption is permanent: if the step `i` is the tick of every awake validator at the
start `t₁` of slot `s + 1` and put `p`'s block `B` on the wire; and on `p`'s node state before
`t₁`, no block of the tree has `B`'s root, the tree holds `B`'s parent, and the finalized block is
compatible with `B` — then `B` is in `p`'s tree right after that tick.

 `hParentHeld` and `hF`
are what `lem20`'s `hApX` and `hF3p` give at `p`, with Lemma 46
: there the finalized
block is `B` or an ancestor of `B`, which is compatible with `B`.







Why: the block `p`'s tick sent was sent by its proposal (Lemma 19's route), on the node state the
tick of the available chain left: at the start of a slot that tick only deletes expired lock
entries, so the proposal read `p`'s FG state, its pool and the clock `t₁`. The proposal then
receives its block through `on_block`, whose test passes: the block is well formed (its
attestations are of the pool, which holds only well-formed attestations by the node invariant;
the votes of the pool are filed by slot and committee; and the digest of its content holds by
construction),
its slot is the slot of `t₁`, its root is new, its parent is held, the finalized block is
compatible with it (when it is a descendant of `B`, `p`'s tree already holds `B` and nothing is
admitted), its proposer is the slot's (the tick's `if`), its parent's slot is at most
the slot `s` of `t₁ − 1` (a block held before `t₁` entered the tree at an earlier time), and its
attestations are those of the pool valid against the parent's chain state. The attestation duty
that may follow keeps the tree.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `Sched`: the schedule; `x`: the execution; `s`: the slot before the proposal's;
- `i`: the step of `p`'s tick at the start of slot `s + 1`; `B`: the block; `p`: the proposer.

Read aloud: a proposer whose tick at the start of slot `s + 1` put `B` on the wire, with
`B`'s root new to it, `B`'s parent in its tree and its finalized block compatible with `B`, holds
`B` right after that tick. -/
theorem lem22a_proposer_holds_own_proposal (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s i : ℕ) (B : Block V) (p : V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    -- `p`'s tick at the start of slot `s + 1` is the step `i`, and put `B` on the wire
    (hl : x.lbl i = Event.tick p (M.slotStart S.C (s + 1)))
    (hsent : (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
      x.sent (i + 1) - x.sent i)
    -- the root of `B` is new to `p`
    (hRootNew : ∀ B' ∈ (x.tickInput p (M.slotStart S.C (s + 1))).tree, B'.root ≠ B.root)
    -- `p` holds `B`'s parent, and its finalized block is compatible with `B`
    (hParentHeld : B.parent ∈ (x.tickInput p (M.slotStart S.C (s + 1))).tree)
    (hF : (x.tickInput p (M.slotStart S.C (s + 1))).finalized.compatible B = true) :
    B ∈ (x.st (i + 1) p).tree :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem22a_proposer_holds_own_proposal M F U) S A x R s i B p
    E hl hsent hRootNew hParentHeld hF

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
(`tick_active`); no honesty of `p` at a real time is asked. The delivery finds `w`'s
clock at the start of slot `s + 1` or later: the environment's promise is for the release clock values
`releaseOf M S.C`, and a re-delivery after `w`'s tick to the start of slot `s + 1` fits in
one delay. -/
theorem lem22_proposal_held_by_voter (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s i : ℕ) (B : Block V) (p w : V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
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
    B ∈ (x.tickInput w (M.voteTime S.C (s + 1))).tree :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem22_proposal_held_by_voter M F U) S A x R GST s i B p w
    E hNet hSkew hRedeliver hRoots hParent hGST (GoldilocksCorrectness.Record.Proofs.Executions.tick_window_ahead_of_activeThroughoutToTick_int M x R E hw htStart) hl hsent hBp hF

end GoldilocksCorrectness.Record.Statements.Executions

