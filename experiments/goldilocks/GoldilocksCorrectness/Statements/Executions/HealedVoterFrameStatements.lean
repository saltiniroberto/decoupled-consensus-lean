module
public import GoldilocksCorrectness.Proofs.Executions.HealedVoterFrame

@[expose] public section

/-!
# The voter frame after the hand-over

The audited statements, proved in `GoldilocksCorrectness/Proofs/Executions/HealedVoterFrame.lean`:

- `chain_block_held_before_freeze`: a block on the honest chain before slot `s` is held by every
  honest active voter of slot `s` before the view freeze of slot `s − 1`, when its finalized block
  there is compatible with the block;
- `voterFrame_after_handover`: after the hand-over, every honest active voter of slot `s` has the
  frame `VoterFrameOnChainAt` relative to the honest chain before `s`.


-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC

open GoldilocksCorrectness.Statements.Routines (Δ voteTime supportCutoff viewFreeze)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec Schedule)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **A block on the honest chain before `s` reaches every honest active voter of `s` before the
view freeze of slot `s − 1`.** Under synchrony from `GST`, with `w` honest and active at slot `s`
and its finalized block before that freeze compatible with the block.

Why: the block is an ancestor of, or equal to, the confirmation `C` of a slot `μ < s` saved by an
updater `u`, which held `C` before the support cutoff of slot `μ`; when `w`'s finalized block is
an ancestor of the block, the network delivers `C` to `w`, awake and honest from the support cutoff
of slot `s − 1` to the view freeze of slot `s − 1` (inside its duty window of slot `s`), within one
delay; otherwise the block is an ancestor of `w`'s finalized block, which `w` holds.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the first slot of the chain; `s`: the slot; `w`: the voter; `B`:
  the block.



Roots name blocks until `viewFreeze S (s - 1)`: the confirmation the updater holds reaches `w` by
the view freeze of slot `s − 1`, one delay after the support cutoff of slot `s − 1`.

Read aloud: an honest active voter holds the honest chain so far when its voter tree is frozen. -/
theorem chain_block_held_before_freeze (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ s : ℕ) (w : V) (B : Block V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (viewFreeze S (s - 1)))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hGST : GST ≤ voteTime S s₀)
    (hw : w ∈ honestActiveAt S Sched s)
    (hB : OnHonestChainBefore S Sched x s₀ s B)
    (hF : (stateBefore x (viewFreeze S (s - 1)) w).S.F.compatible B = true) :
    B ∈ (stateBefore x (viewFreeze S (s - 1)) w).S.T :=
  GoldilocksCorrectness.Proofs.Executions.chain_block_held_before_freeze S Sched x GST s₀ s w B
    hDiv hMono hSync hCatch hRoots hParent hGST hw hB hF

/-- **The voter frame after the hand-over.** With the confirmations of the slots before `s`
forming one chain, the old attestations at most `H`, the caches from `i₂`, fewer than a quorum ever
corrupted, the view freeze of slot `s − 1` after `x[i₂].time`, and `w` honest and active at slot
`s`: `w`'s frame before the vote time of slot `s` follows the honest chain before `s`.

Why: the root of `w`'s fork choice is on the chain before `s` (Lemma 91 (f)), so compatible with
every block `B` of it. When the root is `B` or an ancestor of `B`, the state is not contested and
its `head_height_floor` (the least chain-state height a viable block may have) is `h_max − 1` (Lemma 91 (d)); some block `E` of the chain before `s` has a chain-state
height at least `h_max − 1` (the justified block when `h_max ≤ H + 1`; otherwise the entry named by
the progress certificate at `h_max − 1` of the block that raised the chain, Lemma 67); the later of
`B` and `E` is held before the view freeze of slot `s − 1` (`chain_block_held_before_freeze`), so
it is in the voter tree and a viable head.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `i₂`: the step from which the caches are on the
  chain; `H`: the threshold; `s`: the slot of the vote; `w`: the voter.



Roots name blocks until `voteTime S s`: the proof reads `w`'s state before the vote time of slot
`s`, and the blocks of the chain `w` holds by the view freeze of slot `s − 1`.

Read aloud: after the hand-over, an honest active voter's fork-choice root is compatible with the
honest chain before its slot, and, when the root is a block of that chain or an ancestor of one,
some block of its voter tree that is that block or a descendant of it is a viable head. -/
theorem voterFrame_after_handover (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ i₂ H s : ℕ) (w : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (voteTime S s))
    (hParent : ParentHeldAtDelivery S Sched x) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hGST : GST ≤ voteTime S s₀)
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x[i₂].time ≤ x[j].time → u ∉ Sched.adv (x[j].time : Int) →
      CachesOnChain S Sched x s₀ H (x[j][u].st))
    -- the view freeze of slot `s − 1`, where the voter tree is read, is after `x[i₂].time`
    (hs : x[i₂].time < viewFreeze S (s - 1))
    (hChain : ConfirmationsChainBefore S Sched x s₀ s)
    (hw : w ∈ honestActiveAt S Sched s) :
    VoterFrameOnChainAt S Sched x s₀ s w :=
  GoldilocksCorrectness.Proofs.Executions.voterFrame_after_handover S Sched x GST s₀ i₂ H s w hDiv
    hMono hSync hCatch hRoots hParent hU hAdvQ hGST hOld hCaches hs hChain hw

/-- **The voter frame after the hand-over.** With the confirmations of the slots before `s` forming
one chain, the old attestations at most `H`, the caches from `i₂` to the vote time of slot `s`,
fewer than a quorum ever corrupted, the view freeze of slot `s − 1` after `x[i₂].time`, and `w`
honest and active at slot `s`: `w`'s frame before the vote time of slot `s` follows the honest chain
before `s`.

Why: the root of `w`'s fork choice is on the chain before `s` (Lemma 91 (f)), so compatible with
every block `B` of it. When the root is `B` or an ancestor of `B`, the state is not contested and
its `head_height_floor` is `h_max − 1` (Lemma 91 (d)); some block `E` of the chain before `s` has a chain-state
height at least `h_max − 1` (the justified block when `h_max ≤ H + 1`; otherwise the entry named by
the progress certificate at `h_max − 1` of the block that raised the chain, Lemma 67); the later of
`B` and `E` is held before the view freeze of slot `s − 1` (`chain_block_held_before_freeze`), so
it is in the voter tree and a viable head.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `i₂`: the step from which the caches are on the
  chain; `H`: the threshold; `s`: the slot of the vote; `w`: the voter.



Roots name blocks until `voteTime S s`: the proof reads `w`'s state before the vote time of slot
`s`, and the blocks of the chain `w` holds by the view freeze of slot `s − 1`.

Read aloud: after the hand-over, an honest active voter's fork-choice root is compatible with the
honest chain before its slot, and, when the root is a block of that chain or an ancestor of one,
some block of its voter tree that is that block or a descendant of it is a viable head.

Caches up to `voteTime S s`: the proof reads `w`'s caches before the vote time of slot `s`.  -/
theorem voterFrame_after_handover_until (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ i₂ H s : ℕ) (w : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (voteTime S s))
    (hParent : ParentHeldAtDelivery S Sched x) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hGST : GST ≤ voteTime S s₀)
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x[i₂].time ≤ x[j].time → x[j].time ≤ voteTime S s →
      u ∉ Sched.adv (x[j].time : Int) → CachesOnChain S Sched x s₀ H (x[j][u].st))
    -- the view freeze of slot `s − 1`, where the voter tree is read, is after `x[i₂].time`
    (hs : x[i₂].time < viewFreeze S (s - 1))
    (hChain : ConfirmationsChainBefore S Sched x s₀ s)
    (hw : w ∈ honestActiveAt S Sched s) :
    VoterFrameOnChainAt S Sched x s₀ s w :=
  GoldilocksCorrectness.Proofs.Executions.voterFrame_after_handover_until S Sched x GST s₀ i₂ H s w
    hDiv hMono hSync hCatch hRoots hParent hU hAdvQ hGST hOld hCaches hs hChain hw

end GoldilocksCorrectness.Statements.Executions
