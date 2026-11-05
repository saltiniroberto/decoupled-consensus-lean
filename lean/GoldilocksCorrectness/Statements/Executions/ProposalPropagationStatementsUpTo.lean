module
public import GoldilocksCorrectness.Statements.Executions.ProposalPropagationStatements
public import GoldilocksCorrectness.Statements.Executions.AsyncDeliveryStatements
public import GoldilocksCorrectness.Proofs.Executions.Lemma22UpTo

@[expose] public section

/-!
# `ProposalPropagationStatements.lean` with the delivery premises up to a bound

The theorems of `GoldilocksCorrectness/Statements/Executions/ProposalPropagationStatements.lean`
that name a delivery premise, restated with `SynchronyFromWakeUpTo` and `CatchUpOnWakeUpTo` at a
bound on the deadlines.
The bound of each twin is the latest ordinary deadline `max t GST + Δ` of a send its proof reads,
written in the twin's own parameters.

* `lem22_proposal_held_by_voter`

No `axiom`, no `native_decide`, no `sorry`. The landed page is imported, never edited.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **Lemma 22, an honest proposal reaches the next slot's voter.** In an execution where every
time is reached, corruption is permanent, blocks and Goldfish votes are delivered within `Δ`
after `GST` (synchrony from the receiver's wake, and catch-up on wake),
a root names one block among what honest validators hold, and a block reaches a validator
only once it holds the parent: if `GST` is at most the vote time of slot `s`; `p` is honest at the
start `t₁` of slot `s + 1`; `w` is awake and honest at every time from `t₁` to the vote time `t₃`
of slot `s + 1`; the step `i` is the tick of every awake validator at `t₁`, put
`p`'s block `B` on the wire, and left `p` holding `B`; and `w`'s finalized block before `t₃` is
compatible with `B` — then `w` holds `B` before `t₃`.

This is the second half of `hBw`'s discharge; the tick step `i` is named, rather than `lem20`'s
existential `hPropose`, so that the state `x[i + 1][p].st` it leaves can be spoken of.



Why: `p`'s send is honest and its block is in `p`'s tree right after it, so the block passed every
test `w`'s `on_block` makes that reads the block alone; synchrony delivers it to `w` strictly
before `t₁ + Δ = t₃`, at a step where `w`'s clock is current, `w` holds the parent
(`ParentHeldAtDelivery`, the block being compatible with `w`'s finalized block), and a block of
`w`'s tree with `B`'s root would be `B` itself. So `w` holds `B` before `t₃`.

The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution; `GST`: the time from which the
  network is synchronous; `s`: the slot before the proposal's;
- `i`: the step of `p`'s tick at the start of slot `s + 1`; `B`: the block; `p`: the proposer;
  `w`: the voter of slot `s + 1`.

Read aloud: a block an honest proposer put on the wire at its tick at the start of slot `s + 1`,
and holds right after it, is held before the vote time of slot `s + 1` by every validator awake
and honest from the start of slot `s + 1` to that vote time whose finalized block is compatible with it.

Roots name blocks until `voteTime S (s + 1)`: the proof compares the block `w` holds at the
delivery of `B`, a step at a time before the vote time of slot `s + 1`, with `B`, which `p`
holds right after its tick.

Restated with the delivery premises up to `voteTime S (s + 1)`: the proposal of slot `s + 1` reaches `w` by then (`mem_T_before_of_send_upTo`). -/
theorem lem22_proposal_held_by_voter_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s i : ℕ) (B : Block V) (p w : V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (voteTime S (s + 1)))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (voteTime S (s + 1)))
    (hRoots : RootsNameBlocksUntil S Sched x (voteTime S (s + 1)))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hGST : GST ≤ voteTime S s)
    (hp : p ∉ Sched.adv (slotStart S (s + 1) : Int))
    (hw : ∀ t : ℕ, slotStart S (s + 1) ≤ t → t ≤ voteTime S (s + 1) →
      w ∈ Sched.awake (t : Int) ∧ w ∉ Sched.adv (t : Int))
    -- `p`'s tick at the start of slot `s + 1` is the step `i`, put `B` on the wire, and left
    -- `p` holding `B`
    (hl : x.lbl i = AtomicAction.tickAllAwake (slotStart S (s + 1)))
    (hsent : (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
      x[i + 1].sent - x[i].sent)
    (hBp : B ∈ (x[i + 1][p].st).S.T)
    -- `w`'s finalized block before its vote is compatible with `B`
    (hF : (stateBefore x (voteTime S (s + 1)) w).S.F.compatible B = true) :
    B ∈ (stateBefore x (voteTime S (s + 1)) w).S.T :=
  GoldilocksCorrectness.Proofs.Executions.lem22_proposal_held_by_voter_upTo S Sched x GST s i B p w
    hDiv hMono hSync hCatch hRoots hParent hGST hp hw hl hsent hBp hF

end GoldilocksCorrectness.Statements.Executions

