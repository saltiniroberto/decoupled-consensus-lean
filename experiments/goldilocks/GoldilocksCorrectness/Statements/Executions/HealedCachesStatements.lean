module
public import GoldilocksCorrectness.Proofs.Executions.Lemma84
public import GoldilocksCorrectness.Proofs.Executions.Lemma85

@[expose] public section

/-!
# The finality caches after the healed round

The audited statements about the finality caches of honest validators after the healed round,
proved in `GoldilocksCorrectness/Proofs/Executions/Lemma84.lean` and
`GoldilocksCorrectness/Proofs/Executions/Lemma85.lean`:

- `H_of_h_max`: a bound on every honest `h_max` before `t₀` bounds every honest attestation sent
  before `t₀`;
- Lemma 84, `lem84_caches_stay_on_chain`: once the caches of every honest validator are on the
  honest chain at a height greater than the threshold, they stay there;
- Lemma 85, `lem85_honest_finalized_on_chain`: then the finalized block of every validator honest
  at a step is on the honest chain, at every step; `lem85_honest_finalized_on_chain_at`, the same
  with the slot of the honest chain named, its update at most the later of the step's time and
  the time of step `i₁`.


-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC

open GoldilocksCorrectness.Statements.Routines (supportCutoff)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec Schedule)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **`H_of_h_max`, a bound on the honest `h_max` bounds the old attestations.** When every
validator honest at a step before `t₀` has, at that step, its cache `h_max` at most `H`, every
attestation an honest awake validator put on the wire at a tick before `t₀` has height at most
`H`.

Why: the attestation has the chain-state height of a block of the sender's tree, at most the
sender's `h_max` at the end of the tick (Lemma 46), a step whose time is the tick's.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t₀`: the time before which the
  attestations are read; `H`: the bound.



Read aloud: when every validator honest at a step before `t₀` has, at that step, its cache
`h_max` at most `H`, every honest attestation sent before `t₀` has height at most `H`. -/
theorem H_of_h_max (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (t₀ H : ℕ)
    -- every validator honest at a step before `t₀` has, at that step, `h_max` at most `H`
    (hH : ∀ (i : ℕ) (v : V), x[i].time < t₀ → v ∉ Sched.adv (x[i].time : Int) →
      (x[i][v].st).S.h_max ≤ H) :
    OldAttestationsAtMost S Sched x t₀ H :=
  GoldilocksCorrectness.Proofs.Executions.H_of_h_max S Sched x t₀ H hH

/-- **Lemma 84, the finality caches stay on the honest chain.** Under unforgeability, monotone
corruption and roots naming blocks among what honest validators hold by `t`, with fewer than a
quorum of validators in the adversary set up to every time, every honest attestation sent at or
after `t₀` naming the honest chain's entry at its height, and every one sent before `t₀` at a
height at most `H`: when the caches of every validator honest at step `i₁` satisfy
`CachesOnChain`, so do those of every validator honest at any later step at a time at most `t`.

Why: a validator's caches change only in the finality update of a block it accepts; the update
moves the justified block only to a justification at a height at least the old one, so greater
than `H`, whose block is the honest chain's entry there (Lemmas 66 and 83), and only when the
finalized block is that block or an ancestor of it; it moves the finalized block only to an
ancestor of the justified block, or that block.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `t₀`: the time
  from which the honest attestations name the honest chain; `H`: the threshold; `i₁`: the step
  from which the caches are on the chain; `t`: the bound on the times of the steps.



Roots name blocks until `t`: the conclusion is for the steps at times at most `t`, and at each
such step `i + 1` the proof reads `justifiedOnChainWith_of_exec`, which takes blocks as held up to
`x[i + 1].time`.

Read aloud: when the caches of every validator honest at step `i₁` are on the honest chain with
`h_j > H`, so are those of every validator honest at any later step at a time at most `t`. -/
theorem lem84_caches_stay_on_chain (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ t₀ H i₁ t : ℕ)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hRoots : RootsNameBlocksUntil S Sched x t)
    -- fewer than a quorum of validators have been in the adversary set up to every time
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    -- every honest attestation sent at or after `t₀` names the honest chain's entry at its height
    (hAgree : HonestAttestationsOnChain S Sched x s₀ t₀)
    -- every honest attestation sent before `t₀` has height at most `H`
    (hOld : OldAttestationsAtMost S Sched x t₀ H)
    -- the caches of every validator honest at step `i₁` are on the honest chain
    (hStart : ∀ v : V, v ∉ Sched.adv (x[i₁].time : Int) →
      CachesOnChain S Sched x s₀ H (x[i₁][v].st)) :
    ∀ (i : ℕ) (v : V), i₁ ≤ i → x[i].time ≤ t → v ∉ Sched.adv (x[i].time : Int) →
      CachesOnChain S Sched x s₀ H (x[i][v].st) :=
  GoldilocksCorrectness.Proofs.Executions.lem84_caches_stay_on_chain S Sched x s₀ t₀ H i₁ t hU
    hMono hRoots hAdvQ hAgree hOld hStart

/-- **Lemma 85, every honest finalized block is on the honest chain.** Under the hypotheses of
Lemma 84, with fewer than a third of the validators in the adversary set up to the time of step
`i₁`, and roots naming blocks among what honest validators hold by the later of `t` and the time
of step `i₁`: the block finalized in the node state of a validator honest at a step is on the
honest chain from slot `s₀`, at every step at a time at most `t`.

Why: from `i₁` on, the finalized block is an ancestor of the justified block, or that block, on
the chain (Lemma 84). Before `i₁`, it is finalized at a height `h_F`: when `h_F > H` its
justification certificate names the honest chain's entry at `h_F` (Lemmas 66 and 83); when
`h_F ≤ H`, it is an ancestor of the justified block of a validator honest at `i₁`, or that block
(Lemma 68's honest corollary), at a height greater than `H`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `t₀`: the time
  from which the honest attestations name the honest chain; `H`: the threshold; `i₁`: the step
  from which the caches are on the chain; `t`: the bound on the times of the steps.



Roots name blocks until `max t x[i₁].time`: the conclusion is for the steps at times at most `t`;
at a step `i` from `i₁` on the proof reads Lemma 84 up to `t`; at a step `i` before `i₁` it compares
the finalized block, held after `i` steps, with the entry of the honest chain at a slot whose update
ran by `x[i].time` (Lemma 83), and, by Lemma 89a, with `w`'s justified block after `i₁` steps.

Read aloud: the block finalized in the node state of a validator honest at a step at a time at
most `t` is on the honest chain. -/
theorem lem85_honest_finalized_on_chain (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ t₀ H i₁ t : ℕ)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hRoots : RootsNameBlocksUntil S Sched x (max t x[i₁].time))
    -- fewer than a third of the validators have been in the adversary set up to the time of step
    -- `i₁`
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (x[i₁].time : Int))
    -- fewer than a quorum of validators have been in the adversary set up to every time
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    -- every honest attestation sent at or after `t₀` names the honest chain's entry at its height
    (hAgree : HonestAttestationsOnChain S Sched x s₀ t₀)
    -- every honest attestation sent before `t₀` has height at most `H`
    (hOld : OldAttestationsAtMost S Sched x t₀ H)
    -- the caches of every validator honest at step `i₁` are on the honest chain
    (hStart : ∀ v : V, v ∉ Sched.adv (x[i₁].time : Int) →
      CachesOnChain S Sched x s₀ H (x[i₁][v].st)) :
    ∀ (i : ℕ) (v : V), x[i].time ≤ t → v ∉ Sched.adv (x[i].time : Int) →
      OnHonestChain S Sched x s₀ (x[i][v].st).S.F :=
  GoldilocksCorrectness.Proofs.Executions.lem85_honest_finalized_on_chain S Sched x s₀ t₀ H i₁ t
    hU hMono hRoots hThird hAdvQ hAgree hOld hStart


/-- **Lemma 85, keeping the slot.** Under the hypotheses of Lemma 85: the block finalized in the
node state of a validator honest at a step at a time at most `t` is on the honest chain from slot
`s₀` at a slot `s_a` whose support cutoff of slot `s_a + 1` is at most the later of the time of
that step and the time of step `i₁`.

Why: Lemma 85's proof, with the slot each case finds kept. From `i₁` on, the finalized block is an
ancestor of the justified block, or that block (Lemma 84), and the justified block, above the
threshold, is the honest chain's entry its justification certificate names, at a slot whose update
ran by the step (Lemmas 66 and 83). Before `i₁`, when `h_F > H`, the finalized block is the entry
its own certificate names, at such a slot; when `h_F ≤ H`, it is an ancestor of the justified
block of a validator honest at `i₁`, or that block (Lemma 68's honest corollary), whose slot's
update ran by the time of step `i₁`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `t₀`: the time
  from which the honest attestations name the honest chain; `H`: the threshold; `i₁`: the step
  from which the caches are on the chain; `t`: the bound on the times of the steps.



Roots name blocks until `max t x[i₁].time`, as Lemma 85's.

Read aloud: the block finalized in the node state of a validator honest at a step at a time at
most `t` is on the honest chain at a slot whose update ran by that step, or by step `i₁` when that
is later. -/
theorem lem85_honest_finalized_on_chain_at (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ t₀ H i₁ t : ℕ)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hRoots : RootsNameBlocksUntil S Sched x (max t x[i₁].time))
    -- fewer than a third of the validators have been in the adversary set up to the time of step
    -- `i₁`
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (x[i₁].time : Int))
    -- fewer than a quorum of validators have been in the adversary set up to every time
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    -- every honest attestation sent at or after `t₀` names the honest chain's entry at its height
    (hAgree : HonestAttestationsOnChain S Sched x s₀ t₀)
    -- every honest attestation sent before `t₀` has height at most `H`
    (hOld : OldAttestationsAtMost S Sched x t₀ H)
    -- the caches of every validator honest at step `i₁` are on the honest chain
    (hStart : ∀ v : V, v ∉ Sched.adv (x[i₁].time : Int) →
      CachesOnChain S Sched x s₀ H (x[i₁][v].st)) :
    ∀ (i : ℕ) (v : V), x[i].time ≤ t → v ∉ Sched.adv (x[i].time : Int) →
      ∃ s_a : ℕ, supportCutoff S (s_a + 1) ≤ max x[i].time x[i₁].time ∧
        OnHonestChainAt S Sched x s₀ s_a (x[i][v].st).S.F :=
  GoldilocksCorrectness.Proofs.Executions.lem85_honest_finalized_on_chain_at S Sched x s₀ t₀ H i₁ t
    hU hMono hRoots hThird hAdvQ hAgree hOld hStart

end GoldilocksCorrectness.Statements.Executions
