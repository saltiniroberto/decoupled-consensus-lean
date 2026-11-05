module
public import GoldilocksCorrectness.Proofs.Executions.Lemma22

@[expose] public section

/-!
# An honest proposal is held by its proposer, and reaches the next slot's voter

The audited statements `lem22a_proposer_holds_own_proposal` and `lem22_proposal_held_by_voter`,
proved in `GoldilocksCorrectness/Proofs/Executions/Lemma22.lean`.
Together they discharge the hypothesis `hBw` of `lem20_goldfish_vote_names_honest_proposal`
("`w` holds `B` before its vote"), under the two named hypotheses of Lemma 22a (judgement J46) and
`lem20`'s own hypotheses on `p`'s start; the composition is not written as a theorem, and `lem20`
keeps `hBw` (judgement J38).
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
- `S`: the setup; `Sched`: the schedule; `x`: the execution; `s`: the slot before the proposal's;
- `i`: the step of `p`'s tick at the start of slot `s + 1`; `B`: the block; `p`: the proposer.

Read aloud: a proposer whose tick at the start of slot `s + 1` put `B` on the wire, with
`B`'s root new to it, `B`'s parent in its tree and its finalized block compatible with `B`, holds
`B` right after that tick. -/
theorem lem22a_proposer_holds_own_proposal (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s i : ℕ) (B : Block V) (p : V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    -- `p`'s tick at the start of slot `s + 1` is the step `i`, and put `B` on the wire
    (hl : x.lbl i = AtomicAction.tickAllAwake (slotStart S (s + 1)))
    (hsent : (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
      x[i + 1].sent - x[i].sent)
    -- the root of `B` is new to `p`
    (hRootNew : ∀ B' ∈ (stateBefore x (slotStart S (s + 1)) p).S.T, B'.root ≠ B.root)
    -- `p` holds `B`'s parent, and its finalized block is compatible with `B`
    (hParentHeld : B.parent ∈ (stateBefore x (slotStart S (s + 1)) p).S.T)
    (hF : (stateBefore x (slotStart S (s + 1)) p).S.F.compatible B = true) :
    B ∈ (x[i + 1][p].st).S.T :=
  GoldilocksCorrectness.Proofs.Executions.lem22a_proposer_holds_own_proposal S Sched x s i B p
    hDiv hMono hl hsent hRootNew hParentHeld hF

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
holds right after its tick. -/
theorem lem22_proposal_held_by_voter (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s i : ℕ) (B : Block V) (p w : V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
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
  GoldilocksCorrectness.Proofs.Executions.lem22_proposal_held_by_voter S Sched x GST s i B p w
    hDiv hMono hSync hCatch hRoots hParent hGST hp hw hl hsent hBp hF

end GoldilocksCorrectness.Statements.Executions
