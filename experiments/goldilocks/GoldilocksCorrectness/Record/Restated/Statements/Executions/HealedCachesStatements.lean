module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma84
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma85

@[expose] public section

/-!
# HealedCachesStatements, over a model

The statements of `GoldilocksCorrectness/Statements/Executions/HealedCachesStatements.lean`, over a
model `M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: the old attestations from
the greatest chain-state height, Lemma 84 (the caches stay on the honest chain) and Lemma 85 (the
honest finalized blocks are on the honest chain). Each is the theorem of the same name of
`Record/Restated/Proofs/Executions/Lemma84.lean` or
`Record/Restated/Proofs/Executions/Lemma85.lean`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

open GoldilocksCorrectness.Statements.Routines (supportCutoff)

namespace GoldilocksCorrectness.Record.Statements.Executions

open GoldilocksCorrectness.Record.Statements.Routines (hMax)
open GoldilocksCorrectness.Statements.Executions (Vocab.goldilocks)

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

/-- **`H_of_h_max`, a bound on the honest greatest chain-state heights bounds the old
attestations.** When every validator honest up to `t₀` has, right after each of its ticks to a clock
value less than `t₀`, its greatest chain-state height at most `H`, every attestation such a validator
put on the wire at a tick to a clock value less than `t₀` has height at most `H`.

Why: the attestation has the chain-state height of a block of the sender's tree, at most the
sender's greatest chain-state height after the tick (Lemma 46). The bound `hH` is read at the
sender's own tick, not at a real time, under per-node clocks; with both clock bounds `0`
it follows from the form read at every step before `t₀`.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t₀`: the time before which the
  attestations are read; `H`: the bound.



Read aloud: when every validator honest up to `t₀` has, right after each of its ticks to a clock value
less than `t₀`, its greatest chain-state height at most `H`, every attestation such a validator sent at a
tick to a clock value less than `t₀` has height at most `H`. -/
theorem H_of_h_max (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (t₀ H : ℕ)
    -- every validator honest up to `t₀` has, right after each of its ticks to a clock value less than
    -- `t₀`, greatest chain-state height at most `H`
    (hH : ∀ (i : ℕ) (v : V) (t : ℕ), x.lbl i = Event.tick v t → t < t₀ →
      v ∉ A.corruptedAtTime x t₀ → hMax M S.C (x.st (i + 1) v) ≤ H) :
    OldAttestationsAtMostHonestAt M S A x t₀ t₀ H :=
  (GoldilocksCorrectness.Record.Proofs.Executions.H_of_h_max M F) S A x R E t₀ H hH

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
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `t₀`: the time
  from which the honest attestations name the honest chain; `H`: the threshold; `i₁`: the step
  from which the caches are on the chain; `t`: the bound on the times of the steps.



Roots name blocks until `t`: the conclusion is for the steps at times at most `t`, and at each
such step `i + 1` the proof reads `justifiedOnChainWith_of_exec`, which takes blocks as held up to
`x[i + 1].time`.

Read aloud: when the caches of every validator honest at the time of step `i₁` are on the honest
chain with `h_j > H`, so are those of every validator honest at the time of any later step at a time
at most `t`. -/
theorem lem84_caches_stay_on_chain (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ t₀ H i₁ t : ℕ)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hRoots : RootsNameBlocksUntil M A x t)
    -- fewer than a quorum of validators have been in the adversary set up to the later of `t` and `t₀`
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (max t t₀))
    -- every honest attestation sent at or after `t₀` names the honest chain's entry at its height
    (hAgree : HonestAttestationsOnChain M S A x s₀ t₀)
    -- every honest attestation sent before `t₀` has height at most `H`
    (hOld : OldAttestationsAtMostHonestAt M S A x t₀ t₀ H)
    -- the caches of every validator outside the adversary set after every step whose time is that of
    -- step `i₁` are on the honest chain (B19-2 (a))
    (hStart : ∀ v : V, v ∉ A.corruptedAtTime x (x.time i₁) →
      CachesOnChain M S A x s₀ H (x.st i₁ v)) :
    ∀ (i : ℕ) (v : V), i₁ ≤ i → x.time i ≤ t → v ∉ A.corruptedAtTime x (x.time i) →
      CachesOnChain M S A x s₀ H (x.st i v) :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem84_caches_stay_on_chain M F U Fx) S A x R s₀
    t₀ H i₁ t E hRoots hAdvQ hAgree hOld hStart

/-- **Lemma 85, keeping the slot.** Under the hypotheses of Lemma 85: the block finalized in the
node state of a validator honest at a step at a time at most `t` is on the honest chain from slot
`s₀` at a slot `s_a` whose update some validator ran at a step before that step, or before step
`i₁` when that is later: a tick of some validator to the support cutoff of slot `s_a + 1` at a step
before the later of the two.

Why: Lemma 85's proof, with the slot each case finds kept. From `i₁` on, the finalized block is an
ancestor of the justified block, or that block (Lemma 84), and the justified block, above the
threshold, is the honest chain's entry its justification certificate names, at a slot whose update
ran by the step (Lemmas 66 and 83). Before `i₁`, when `h_F > H`, the finalized block is the entry
its own certificate names, at such a slot; when `h_F ≤ H`, it is an ancestor of the justified
block of a validator honest at `i₁`, or that block (Lemma 68's honest corollary), whose slot's
update ran by the time of step `i₁`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `t₀`: the time
  from which the honest attestations name the honest chain; `H`: the threshold; `i₁`: the step
  from which the caches are on the chain; `t`: the bound on the times of the steps.



Roots name blocks until `max t x[i₁].time`, as Lemma 85's.

Read aloud: the block finalized in the node state of a validator honest at a step at a time at
most `t` is on the honest chain at a slot whose update ran by that step, or by step `i₁` when that
is later. -/
theorem lem85_honest_finalized_on_chain_at (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ t₀ H i₁ t : ℕ)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hRoots : RootsNameBlocksUntil M A x (max t (x.time i₁)))
    -- fewer than a third of the validators have been in the adversary set up to the time of step
    -- `i₁`
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) (x.time i₁))
    -- fewer than a quorum of validators have been in the adversary set up to the later of `max t (x.time i₁)` and `t₀`
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (max (max t (x.time i₁)) t₀))
    -- every honest attestation sent at or after `t₀` names the honest chain's entry at its height
    (hAgree : HonestAttestationsOnChain M S A x s₀ t₀)
    -- every honest attestation sent before `t₀` has height at most `H`
    (hOld : OldAttestationsAtMostHonestAt M S A x t₀ t₀ H)
    -- the caches of every validator outside the adversary set after every step whose time is that of
    -- step `i₁` are on the honest chain (B19-2 (a))
    (hStart : ∀ v : V, v ∉ A.corruptedAtTime x (x.time i₁) →
      CachesOnChain M S A x s₀ H (x.st i₁ v)) :
    ∀ (i : ℕ) (v : V), x.time i ≤ t → v ∉ A.corrupted i →
      ∃ s_a : ℕ, (∃ (k : ℕ) (u : V), k < max i i₁ ∧ x.lbl k = Event.tick u (M.supportCutoff S.C (s_a + 1))) ∧
        OnHonestChainAt M S A x s₀ s_a (x.st i v).finalized :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem85_honest_finalized_on_chain_at M F U Fx) S
    A x R s₀ t₀ H i₁ t E hRoots hThird hAdvQ hAgree hOld hStart

end GoldilocksCorrectness.Record.Statements.Executions

