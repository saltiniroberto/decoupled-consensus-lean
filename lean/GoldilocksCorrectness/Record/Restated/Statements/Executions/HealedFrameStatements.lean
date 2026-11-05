module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma91
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# HealedFrameStatements, over a model

The statements of `GoldilocksCorrectness/Statements/Executions/HealedFrameStatements.lean`, over a
model `M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: Lemma 91 (b) to (f), the
frame facts after healing, read with the greatest chain-state height `hMax M S.C n` of the node's
tree in place of the cache `h_max`. Each is the theorem of the same name of
`Record/Restated/Proofs/Executions/Lemma91.lean`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff)

namespace GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery EnvFactsDeliveryUpTo SyncedWithin SyncedWithinUpTo)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (IsEntry hMax)
open GoldilocksCorrectness.Record.Statements.Routines (JustificationCertOn ProgressCertOn)
open GoldilocksCorrectness.Statements.Executions (Vocab.goldilocks acObject)

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

/-- **Lemma 91 (b), `head_height_floor` at the voter is at most the proposal's parent's height**
. In an execution where every time is reached and corruption is permanent, under
unforgeability and when fewer than a quorum of validators are ever in the adversary set: let `w` tick to
the vote time of slot `s` at the step `iw`, at a time at least `x[i₁].time`; let every tick to a
support cutoff of a slot `s_a + 1` at a step before `iw` be for a slot `s_a` with `s_a + 1 < s`; let the updaters' confirmations of the slots from `s₀` to
before `s − 1` form one chain (`ConfirmationsChainBefore`); let every honest
attestation sent before the support cutoff of slot `s₀ + 1` have height at most `H`; let every
validator honest at a step at a time at least `x[i₁].time` have its caches on the honest chain with
justification height greater than `H` (`CachesOnChain`); and let `Q` be a block that every block on the
honest chain before slot `s − 1` is an ancestor of, or equal to. Then `head_height_floor` of `w`'s FG state at its tick to the vote time of slot `s` is at most
`Q`'s chain-state height.

Why: `w`'s FG state is not contested (Lemma 91 (d)), so `head_height_floor` at `w` is `h_w − 1`,
with `h_w` the greatest chain-state height of `w`'s tree, and `h_w ≥ H + 2`. `w`
holds a block at `h_w` and the block that raised its chain past `h_w − 1` carries a progress
certificate at `h_w − 1 > H` (Lemma 67); the certificate route names an entry of the chain at
that height, confirmed at a slot `s_a` whose support cutoff of slot `s_a + 1` some validator ticked
to at a step before `iw`, so `s_a + 2 ≤ s` (`hs'`): the entry is on the chain before `s − 1`, an ancestor of `Q`,
and its height is at most `Q`'s (Lemma 47 (d)).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `s`: the slot
  of the proposal; `i₁`: the step at the phase's end; `H`: the threshold;
- `w`: the voter; `Q`: the block (the proposal's parent where it is used); `iw`: the step of `w`'s
  tick to the vote time of slot `s`.

Read aloud: after healing the voter's least viable height never passes a block that extends the
chain before `s − 1`, such as the honest proposal's parent.

 -/
theorem lem91b_voter_head_height_floor_le_parent (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ s i₁ H iw : ℕ) (w : V) (Q : Block V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hAdvQ : ∀ t : ℕ, A.AdversaryFewerThanQuorumUntil x (quorum V) t)
    -- the voter's tick to its vote time, at or after `x[i₁].time`
    (hlw : x.lbl iw = Event.tick w (M.voteTime S.C s)) (hiw : x.time i₁ ≤ x.time iw)
    -- every tick to a support cutoff at a step before the voter's tick is for a slot before `s − 1`
    (hs' : ∀ s_a : ℕ, (∃ (k : ℕ) (u : V), k < iw ∧ x.lbl k = Event.tick u (M.supportCutoff S.C (s_a + 1))) →
      s_a + 1 < s)
    (hChain : ConfirmationsChainBefore M S A x s₀ (s - 1))
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x.time i₁ ≤ x.time j → u ∉ A.corrupted j →
      CachesOnChain M S A x s₀ H (x.st j u))
    (hParentChain : ∀ C : Block V, OnHonestChainBefore M S A x s₀ (s - 1) C → C.AncestorEq Q) :
    M.head_height_floor (x.tickInput w (M.voteTime S.C s)) ≤ (M.chainStateOf S.C Q).h :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem91b_voter_head_height_floor_le_parent M F U Fx)
    S A x R s₀ s i₁ H iw w Q E hAdvQ hlw hiw hs' hChain hOld hCaches hParentChain

/-- **Lemma 91 (b), `head_height_floor` at the voter is at most the proposal's parent's height**
. In an execution where every time is reached and corruption is permanent, under
unforgeability and when fewer than a quorum of validators are ever in the adversary set: let `w` tick to
the vote time of slot `s` at the step `iw`, at a time at least `x[i₁].time`; let every tick to a
support cutoff of a slot `s_a + 1` at a step before `iw` be for a slot `s_a` with `s_a + 1 < s`; let the updaters' confirmations of the slots from `s₀` to
before `s − 1` form one chain (`ConfirmationsChainBefore`); let every honest attestation sent before
the support cutoff of slot `s₀ + 1` have height at most `H`; let every validator honest at a step at
a time from `x[i₁].time` to `M.voteTime S.C s` have its caches on the honest chain with
justification height greater than `H` (`CachesOnChain`); and let `Q` be a block that every block on the honest
chain before slot `s − 1` is an ancestor of, or equal to. Then
`head_height_floor` of `w`'s FG state at its tick to the vote time of slot `s` is at most `Q`'s
chain-state height.

Why: `w`'s FG state is not contested (Lemma 91 (d)), so `head_height_floor` at `w` is `h_w − 1`,
with `h_w` the greatest chain-state height of `w`'s tree, and `h_w ≥ H + 2`. `w`
holds a block at `h_w` and the block that raised its chain past `h_w − 1` carries a progress
certificate at `h_w − 1 > H` (Lemma 67); the certificate route names an entry of the chain at
that height, confirmed at a slot `s_a` whose support cutoff of slot `s_a + 1` some validator ticked
to at a step before `iw`, so `s_a + 2 ≤ s` (`hs'`): the entry is on the chain before `s − 1`, an ancestor of `Q`,
and its height is at most `Q`'s (Lemma 47 (d)).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `s`: the slot
  of the proposal; `H`: the threshold;
- `w`: the voter; `Q`: the block (the proposal's parent where it is used); `iw`: the step of `w`'s
  tick to the vote time of slot `s`.

Read aloud: after healing the voter's least viable height never passes a block that extends the
chain before `s − 1`, such as the honest proposal's parent.



Caches at `iw`: the one caches fact the proof reads, `w`'s at `iw`.  -/
theorem lem91b_voter_head_height_floor_le_parent_until (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ s H iw : ℕ) (w : V) (Q : Block V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    -- fewer than a quorum of validators have been in the adversary set up to the later of the voter's tick and the hand-over cutoff
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (max (x.time iw) (M.supportCutoff S.C (s₀ + 1))))
    -- the voter's tick to its vote time
    (hlw : x.lbl iw = Event.tick w (M.voteTime S.C s))
    -- every tick to a support cutoff at a step before the voter's tick is for a slot before `s − 1`
    (hs' : ∀ s_a : ℕ, (∃ (k : ℕ) (u : V), k < iw ∧ x.lbl k = Event.tick u (M.supportCutoff S.C (s_a + 1))) →
      s_a + 1 < s)
    (hChain : ConfirmationsChainBefore M S A x s₀ (s - 1))
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hCaches : CachesOnChain M S A x s₀ H (x.st iw w))
    (hParentChain : ∀ C : Block V, OnHonestChainBefore M S A x s₀ (s - 1) C → C.AncestorEq Q) :
    M.head_height_floor (x.tickInput w (M.voteTime S.C s)) ≤ (M.chainStateOf S.C Q).h :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem91b_voter_head_height_floor_le_parent_until M F U Fx)
    S A x R s₀ s H iw w Q E hAdvQ hlw hs' hChain hOld hCaches hParentChain

/-- **Lemma 91 (c) at the two validators' ticks.** In an execution where every time is reached,
corruption is permanent, blocks and Goldfish votes are delivered within `Δ` after `GST` to a
receiver awake by a time at most `b` (synchrony from the receiver's wake, and catch-up on wake, up
to `b`), a root names one block among what honest validators hold by the real time of `w`'s tick
`kw`, and a block reaches a validator only once it holds the parent; under unforgeability and when
fewer than a quorum of validators are in the adversary set up to the later of the real time of `kw`
and the hand-over cutoff: let `p` tick to the clock value `cp` at step `kp`, and `w` tick to a clock
value `cw` at least `cp + Δ S` at step `kw`, and earlier to a value `c₂` from `cp` up to `cw − Δ S` at
step `k₂`; let `GST + max(Δ, Δs)` be at most `cp + Δ S`, and the phase's end step `i₁` be at a time
at most that of every tick of `p` to `cp`; let the honest confirmations form a chain from
slot `s₀`; let every honest attestation sent before the support cutoff of slot `s₀ + 1` have height
at most `H`; let every validator honest at a step at a time at least `x[i₁].time` have its caches on
the honest chain with justification height greater than `H`; let `p` be active from
`a₀ := cp + Δ S − max(Δ, Δs)` through the sync delay after it, and `w` from `a₀` up to `kw`; and let
`cw` be at most `b`. Then the greatest chain-state height of `p`'s tree at its tick to `cp` is at most
that of `w`'s tree at its tick to `cw`.

Why: `lem91c_at_until` with the chain of every slot's confirmations and the caches at every step
after the phase's end; the bound on the slots of the chain is `cw + Δ S`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `A`, `x`, `R`: the setup, the activity, the execution, the run's facts; `GST`: the time from
  which the network is synchronous; `s₀`: the healed slot; `cp`, `kp`: the clock value and the step of
  `p`'s tick; `i₁`: the step at the phase's end; `H`: the threshold; `b`: the bound on the delivery
  premises; `cw`, `kw`: those of `w`'s tick; `c₂`, `k₂`: those of `w`'s earlier tick; `p`: the
  proposer; `w`: the voter.



Read aloud: after healing, a validator that ticks to a clock value at least one delay after another's
tick, having ticked earlier to a value from that tick's up to one delay before, knows at its tick a
greatest chain-state height at least the other's at its tick. -/
theorem lem91c_at (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ cp i₁ H b kp cw kw c₂ k₂ : ℕ) (p w : V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks b) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST b)
    -- roots name blocks up to the real time of `w`'s tick
    (hRoots : RootsNameBlocksUntil M A x (x.time kw))
    (hParent : ParentHeldAtDelivery M x)
    -- fewer than a quorum of validators have been in the adversary set up to the later of the real time of
    -- `w`'s tick and the hand-over cutoff
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (max (x.time kw) (M.supportCutoff S.C (s₀ + 1))))
    -- `p` ticks to `cp`; `w` ticks to `cw`, at least one delay after `cp`, and earlier to `c₂`, from `cp` up
    -- to one delay before `cw`
    (hkp : x.lbl kp = Event.tick p cp)
    (hkw : x.lbl kw = Event.tick w cw) (hcw : cp + Δ S ≤ cw)
    (hk₂ : x.lbl k₂ = Event.tick w c₂) (hc₂ : cp ≤ c₂) (hc₂w : c₂ + Δ S ≤ cw)
    (hGST : GST + max (Δ S) Δs ≤ cp + Δ S)
    -- the phase's end step is before every tick of `p` to `cp`
    (hi : ∀ k : ℕ, x.lbl k = Event.tick p cp → x.time i₁ ≤ x.time k)
    (hChain : ConfirmationsChain M S A x s₀)
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x.time i₁ ≤ x.time j → u ∉ A.corrupted j →
      CachesOnChain M S A x s₀ H (x.st j u))
    -- `p` is active from `cp + Δ − max(Δ, Δs)` through the sync delay after it
    (hp : p ∈ A.activeThroughout x ((cp + Δ S - max (Δ S) Δs : ℕ) : ℝ)
      (((cp + Δ S - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- `w` is active from the same start up to its tick
    (hw : w ∈ A.activeThroughout x ((cp + Δ S - max (Δ S) Δs : ℕ) : ℝ) (x.time kw))
    -- the deliveries are read up to at least `cw`
    (hb : cw ≤ b) :
    hMax M S.C (x.tickInput p cp) ≤ hMax M S.C (x.tickInput w cw) :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem91c_at M F U Fx) S A x R GST s₀ cp i₁ H b kp cw kw c₂ k₂ p w
    E hNet hSkew hRedeliver Sy hRoots hParent hAdvQ hkp hkw hcw hk₂ hc₂ hc₂w hGST hi hChain hOld hCaches hp hw hb

/-- **Lemma 91 (c) at the two validators' ticks, on the chain before a slot.** In an execution where
every time is reached, corruption is permanent, blocks and Goldfish votes are delivered within `Δ`
after `GST` to a receiver awake by a time at most `b` (synchrony from the receiver's wake, and catch-up
on wake, up to `b`), a root names one block among what honest validators hold by the real time of
`w`'s tick `kw`, and a block reaches a validator only once it holds the parent; under unforgeability
and when fewer than a quorum of validators are in the adversary set up to the later of the real time
of `kw` and the hand-over cutoff: let `p` tick to the clock value `cp` at step `kp`, and `w` tick to a
clock value `cw` at least `cp + Δ S` at step `kw`, and earlier to a value `c₂` from `cp` up to
`cw − Δ S` at step `k₂`; let `GST + max(Δ, Δs)` be at most `cp + Δ S`, and the phase's end step `i₁`
be at a time at most that of every tick of `p` to `cp`; let the updaters'
confirmations of the slots from `s₀` to before `s'` form one chain (`ConfirmationsChainBefore`), `s'`
greater than every slot whose update ran at a tick (of any validator) at a step before `kw`; let every
honest attestation sent before the support cutoff of slot `s₀ + 1` have height at most `H`; let every
validator honest at a step at a time from `x[i₁].time` to the real time of `kw` have its caches on the
honest chain with justification height greater than `H`; let `p` be active from
`a₀ := cp + Δ S − max(Δ, Δs)` through the sync delay after it, and `w` from `a₀` up to `kw`; and let
`cw` be at most `b`. Then the greatest chain-state height of `p`'s tree at its tick to `cp` is at most
that of `w`'s tree at its tick to `cw`.

Why: `p` holds a block `Y` at `m`, the greatest chain-state height of its tree at `kp`; the block that
raised `Y`'s chain past `m − 1` carries a progress certificate at `m − 1 > H`, naming the chain's entry
`Eb` at `m − 1`, an ancestor of `Y`. `w`'s justified block `J_w` at `kw` is on the chain, an entry. If
`J_w`'s height is at least `m`, done. Otherwise `J_w` is `Eb` or an ancestor of it, and a block `Z` of
`p`'s tree at `kp` at height at least `m` (`Y`, or `p`'s justified block), with `p`'s finalized block and
`Eb` ancestors of it, reaches `w` by `kw` when `p`'s finalized block at its last step before `a₀` is
compatible with `Z`; when it is not, that step is after `kp`, and `p`'s justified block there is on the
chain, a strict descendant of `Eb`, so at height at least `m`, and it reaches `w` by `kw`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `A`, `x`, `R`: the setup, the activity, the execution, the run's facts; `GST`: the time from
  which the network is synchronous; `s₀`: the healed slot; `cp`, `kp`: the clock value and the step of
  `p`'s tick; `i₁`: the step at the phase's end; `H`: the threshold; `b`: the bound on the delivery
  premises; `s'`: the bound on the slots of the chain; `cw`, `kw`: those of `w`'s tick; `c₂`, `k₂`:
  those of `w`'s earlier tick; `p`: the proposer; `w`: the voter.




Read aloud: after healing, a validator that ticks to a clock value at least one delay after another's
tick, having ticked earlier to a value from that tick's up to one delay before, knows at its tick a
greatest chain-state height at least the other's at its tick. -/
theorem lem91c_at_until (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ cp i₁ H b s' kp cw kw c₂ k₂ : ℕ) (p w : V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks b) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST b)
    -- roots name blocks up to the real time of `w`'s tick
    (hRoots : RootsNameBlocksUntil M A x (x.time kw))
    (hParent : ParentHeldAtDelivery M x)
    -- fewer than a quorum of validators have been in the adversary set up to the later of the real time of
    -- `w`'s tick and the hand-over cutoff
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (max (x.time kw) (M.supportCutoff S.C (s₀ + 1))))
    -- `p` ticks to `cp`; `w` ticks to `cw`, at least one delay after `cp`, and earlier to `c₂`, from `cp` up
    -- to one delay before `cw`
    (hkp : x.lbl kp = Event.tick p cp)
    (hkw : x.lbl kw = Event.tick w cw) (hcw : cp + Δ S ≤ cw)
    (hk₂ : x.lbl k₂ = Event.tick w c₂) (hc₂ : cp ≤ c₂) (hc₂w : c₂ + Δ S ≤ cw)
    (hGST : GST + max (Δ S) Δs ≤ cp + Δ S)
    -- the phase's end step is before every tick of `p` to `cp`
    (hi : ∀ k : ℕ, x.lbl k = Event.tick p cp → x.time i₁ ≤ x.time k)
    (hChain : ConfirmationsChainBefore M S A x s₀ s')
    -- every slot updated at a tick before `kw` is less than `s'`
    (hs' : ∀ s_a : ℕ, (∃ (k : ℕ) (u : V), k < kw ∧ x.lbl k = Event.tick u (M.supportCutoff S.C (s_a + 1))) →
      s_a < s')
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x.time i₁ ≤ x.time j → x.time j ≤ x.time kw →
      u ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st j u))
    -- `p` is active from `cp + Δ − max(Δ, Δs)` through the sync delay after it
    (hp : p ∈ A.activeThroughout x ((cp + Δ S - max (Δ S) Δs : ℕ) : ℝ)
      (((cp + Δ S - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- `w` is active from the same start up to its tick
    (hw : w ∈ A.activeThroughout x ((cp + Δ S - max (Δ S) Δs : ℕ) : ℝ) (x.time kw))
    -- the deliveries are read up to at least `cw`
    (hb : cw ≤ b) :
    hMax M S.C (x.tickInput p cp) ≤ hMax M S.C (x.tickInput w cw) :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem91c_at_until M F U Fx) S A x R GST s₀ cp i₁ H b s' kp cw kw
    c₂ k₂ p w E hNet hSkew hRedeliver Sy hRoots hParent hAdvQ hkp hkw hcw hk₂ hc₂ hc₂w hGST hi hChain hs' hOld
    hCaches hp hw hb

/-- **Lemma 91 (c), the voter is at least as far as the proposer.** In an execution where every
time is reached, corruption is permanent, blocks and Goldfish votes are delivered within `Δ` after
`GST` (synchrony from the receiver's wake, and catch-up on wake), a root names one block among what
honest validators hold by the real time of `w`'s tick `kw` to the vote time of slot `s`, and a block
reaches a validator only once it holds the parent; under unforgeability and when fewer than a quorum
of validators are in the adversary set up to the later of the real time of `kw` and the hand-over
cutoff: let `GST + max(Δ, Δs)` be at most the vote time of slot `s`; let the phase's end step `i₁` be
at a time at most that of every tick of `p` to the start of slot `s`; let `p` tick to the start of slot `s` at step `kp`, and `w` tick to the start of slot `s`
at step `kS` and to its vote time at step `kw`; let the honest confirmations form a chain from slot
`s₀`; let every honest attestation sent before the support cutoff of slot `s₀ + 1` have height at most
`H`; let every validator honest at a step at a time at least `x[i₁].time` have its caches on the honest
chain with justification height greater than `H`; let `p` be active from one delay or one sync delay
before the vote time through the sync delay after that, and `w` from the same start up to `kw`. Then
the greatest chain-state height of `p`'s tree at its tick to the start of slot `s` is at most that of
`w`'s tree at its tick to the vote time of slot `s`.

Why: `lem91c_proposer_h_max_le_voter_h_max_until` with the chain of every slot's confirmations and the
caches at every step after the phase's end.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `A`, `x`, `R`: the setup, the activity, the execution, the run's facts; `GST`: the time from
  which the network is synchronous; `s₀`: the healed slot; `s`: the slot; `i₁`: the step at the phase's
  end; `H`: the threshold; `kp`: `p`'s tick to the slot's start; `kw`, `kS`: `w`'s ticks to the slot's
  vote time and start; `p`: the proposer; `w`: the voter.



Read aloud: after healing, a voter that ticks to the slot's start and to its vote time knows, at its
vote tick, a height at least as great as the proposer knows at its tick to the slot's start. -/
theorem lem91c_proposer_h_max_le_voter_h_max (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ s i₁ H kp kw kS : ℕ) (p w : V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hRoots : RootsNameBlocksUntil M A x (x.time kw))
    (hParent : ParentHeldAtDelivery M x)
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (max (x.time kw) (M.supportCutoff S.C (s₀ + 1))))
    (hGST : GST + max (Δ S) Δs ≤ M.voteTime S.C s)
    -- the proposer ticks to the slot's start; the voter ticks to the slot's start and to its vote time
    (hkp : x.lbl kp = Event.tick p (M.slotStart S.C s)) (hkw : x.lbl kw = Event.tick w (M.voteTime S.C s))
    (hkS : x.lbl kS = Event.tick w (M.slotStart S.C s))
    -- the phase's end step is before every tick of the proposer to the slot's start
    (hs : ∀ k : ℕ, x.lbl k = Event.tick p (M.slotStart S.C s) → x.time i₁ ≤ x.time k)
    (hChain : ConfirmationsChain M S A x s₀)
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x.time i₁ ≤ x.time j → u ∉ A.corrupted j →
      CachesOnChain M S A x s₀ H (x.st j u))
    (hp : p ∈ A.activeThroughout x ((M.voteTime S.C s - max (Δ S) Δs : ℕ) : ℝ)
      (((M.voteTime S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hw : w ∈ A.activeThroughout x ((M.voteTime S.C s - max (Δ S) Δs : ℕ) : ℝ) (x.time kw)) :
    hMax M S.C (x.tickInput p (M.slotStart S.C s)) ≤ hMax M S.C (x.tickInput w (M.voteTime S.C s)) :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem91c_proposer_h_max_le_voter_h_max M F U Fx) S
    A x R GST s₀ s i₁ H kp kw kS p w E hNet hSkew hRedeliver Sy hRoots hParent hAdvQ hGST hkp hkw hkS hs hChain
    hOld hCaches hp hw

/-- **Lemma 91 (c), the voter is at least as far as the proposer, on the chain before `s − 1`.** In an
execution where every time is reached, corruption is permanent, blocks and Goldfish votes are delivered
within `Δ` after `GST` (synchrony from the receiver's wake, and catch-up on wake), a root names one
block among what honest validators hold by the real time of `w`'s tick `kw` to the vote time of slot
`s`, and a block reaches a validator only once it holds the parent; under unforgeability and when fewer
than a quorum of validators are in the adversary set up to the later of the real time of `kw` and the
hand-over cutoff: let `GST + max(Δ, Δs)` be at most the vote time of slot `s`; let the phase's end step
`i₁` be at a time at most that of every tick of `p` to the start of slot `s`; let `p` tick to the start of slot `s` at step `kp`, and `w` tick to the start of slot `s`
at step `kS` and to its vote time at step `kw`; let the updaters' confirmations of the slots from `s₀`
to before `s − 1` form one chain (`ConfirmationsChainBefore`); let every honest attestation sent before
the support cutoff of slot `s₀ + 1` have height at most `H`; let every validator honest at a step at a
time from `x[i₁].time` to the real time of `kw` have its caches on the honest chain with justification
height greater than `H`; let `p` be active from one delay or one sync delay before the vote time through
the sync delay after that, and `w` from the same start up to `kw`. Then the greatest chain-state height
of `p`'s tree at its tick to the start of slot `s` is at most that of `w`'s tree at its tick to the vote
time of slot `s`.

Why: `lem91c_at_until` at `cp := M.slotStart S.C s`, `cw := M.voteTime S.C s`, `c₂ := M.slotStart S.C s`,
`b := M.voteTime S.C s`; a tick before `kw` is to a clock value less than the vote time plus one delay,
the support cutoff of slot `s`, so it updates a slot less than `s − 1`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `A`, `x`, `R`: the setup, the activity, the execution, the run's facts; `GST`: the time from
  which the network is synchronous; `s₀`: the healed slot; `s`: the slot; `i₁`: the step at the phase's
  end; `H`: the threshold; `kp`: `p`'s tick to the slot's start; `kw`, `kS`: `w`'s ticks to the slot's
  vote time and start; `p`: the proposer; `w`: the voter.



Read aloud: after healing, a voter that ticks to the slot's start and to its vote time knows, at its
vote tick, a height at least as great as the proposer knows at its tick to the slot's start. -/
theorem lem91c_proposer_h_max_le_voter_h_max_until (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ s i₁ H kp kw kS : ℕ) (p w : V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hRoots : RootsNameBlocksUntil M A x (x.time kw))
    (hParent : ParentHeldAtDelivery M x)
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (max (x.time kw) (M.supportCutoff S.C (s₀ + 1))))
    (hGST : GST + max (Δ S) Δs ≤ M.voteTime S.C s)
    -- the proposer ticks to the slot's start; the voter ticks to the slot's start and to its vote time
    (hkp : x.lbl kp = Event.tick p (M.slotStart S.C s)) (hkw : x.lbl kw = Event.tick w (M.voteTime S.C s))
    (hkS : x.lbl kS = Event.tick w (M.slotStart S.C s))
    -- the phase's end step is before every tick of the proposer to the slot's start
    (hs : ∀ k : ℕ, x.lbl k = Event.tick p (M.slotStart S.C s) → x.time i₁ ≤ x.time k)
    (hChain : ConfirmationsChainBefore M S A x s₀ (s - 1))
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x.time i₁ ≤ x.time j → x.time j ≤ x.time kw →
      u ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st j u))
    (hp : p ∈ A.activeThroughout x ((M.voteTime S.C s - max (Δ S) Δs : ℕ) : ℝ)
      (((M.voteTime S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hw : w ∈ A.activeThroughout x ((M.voteTime S.C s - max (Δ S) Δs : ℕ) : ℝ) (x.time kw)) :
    hMax M S.C (x.tickInput p (M.slotStart S.C s)) ≤ hMax M S.C (x.tickInput w (M.voteTime S.C s)) :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem91c_proposer_h_max_le_voter_h_max_until M F U Fx)
    S A x R GST s₀ s i₁ H kp kw kS p w E hNet hSkew hRedeliver Sy hRoots hParent hAdvQ hGST hkp hkw hkS hs hChain
    hOld hCaches hp hw

/-- **Lemma 91 (d), no honest FG state is contested after healing.** In an execution where every
time is reached and corruption is permanent, under unforgeability and when fewer than a quorum of
validators are ever in the adversary set: let the updaters' confirmations of the slots from `s₀`
to before `s'` form one chain (`ConfirmationsChainBefore`); let every honest attestation sent
before the support cutoff of slot `s₀ + 1` have height at most `H`; let every validator honest at
a step at a time at least `x[i₁].time` have its caches on the honest chain with justification
height greater than `H`. Then at every step `i` at a time at least `x[i₁].time` such that every slot `s_a` to whose support cutoff of slot `s_a + 1` some validator ticked at a step before that step is less than `s'`, the FG
state of a validator `v` honest at that time is not contested (`fg_contest`), and its
`head_height_floor` is its greatest chain-state height minus one.

Why: a contested state holds a block `D` at the greatest chain-state height, `h_j + 1`, of which the
justified block `J` is not an ancestor. The block that raised `D`'s chain past `h_j` carries a
progress certificate at `h_j > H` for the `T_h` of its parent (Lemma 67), an ancestor of `D`; the
certificate route names by its root an entry of the honest chain at `h_j`, confirmed at a slot whose
update ran at a tick before the step, so before slot `s'`; `J`'s own justification certificate (Lemma 66) names by
`J`'s root another such entry, and the two entries are one block (two entries at one height on the
chain before `s'` are one block). So the `T_h` and `J` have one root and are in `v`'s tree, so they
are one block (`RootsNameBlocksIn`), and `J` is an ancestor of `D`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `i₁`: the step
  at the phase's end; `i`: the step; `s'`: the bound on the slot; `H`: the threshold; `v`: the
  validator.

Read aloud: after healing there is one justification per height, so nothing contests, and the
least viable height is the greatest chain-state height minus one.

 -/
theorem lem91d_not_contested (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ i₁ i s' H : ℕ) (v : V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hAdvQ : ∀ t : ℕ, A.AdversaryFewerThanQuorumUntil x (quorum V) t)
    (hChain : ConfirmationsChainBefore M S A x s₀ s')
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x.time i₁ ≤ x.time j → u ∉ A.corrupted j →
      CachesOnChain M S A x s₀ H (x.st j u))
    (hi : x.time i₁ ≤ x.time i) (hv : v ∉ A.corrupted i)
    (hs' : ∀ s_a : ℕ, (∃ (k : ℕ) (u : V), k < i ∧ x.lbl k = Event.tick u (M.supportCutoff S.C (s_a + 1))) →
      s_a < s') :
    M.fg_contest (x.st i v) = false ∧
      M.head_height_floor (x.st i v) = hMax M S.C (x.st i v) - 1 :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem91d_not_contested M F U Fx) S A x R s₀ i₁ i
    s' H v E hAdvQ hChain hOld hCaches hi hv hs'

/-- **Lemma 91 (d), no honest FG state is contested after healing.** In an execution where every
time is reached and corruption is permanent, under unforgeability and when fewer than a quorum of
validators are ever in the adversary set: let the updaters' confirmations of the slots from `s₀`
to before `s'` form one chain (`ConfirmationsChainBefore`); let every honest attestation sent
before the support cutoff of slot `s₀ + 1` have height at most `H`; let every validator honest at
a step at a time from `x[i₁].time` to `x[i].time` have its caches on the honest chain with
justification height greater than `H`. Then at every step `i` at a time at least `x[i₁].time` such
that every slot `s_a` to whose support cutoff of slot `s_a + 1` some validator ticked at a step before that step is less than `s'`, the FG state of a validator `v` honest at that time is not contested (`fg_contest`), and its
`head_height_floor` is its greatest chain-state height minus one.

Why: a contested state holds a block `D` at the greatest chain-state height, `h_j + 1`, of which the
justified block `J` is not an ancestor. The block that raised `D`'s chain past `h_j` carries a
progress certificate at `h_j > H` for the `T_h` of its parent (Lemma 67), an ancestor of `D`; the
certificate route names by its root an entry of the honest chain at `h_j`, confirmed at a slot whose
update ran at a tick before the step, so before slot `s'`; `J`'s own justification certificate (Lemma 66) names by
`J`'s root another such entry, and the two entries are one block (two entries at one height on the
chain before `s'` are one block). So the `T_h` and `J` have one root and are in `v`'s tree, so they
are one block (`RootsNameBlocksIn`), and `J` is an ancestor of `D`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `i`: the step; `s'`: the bound on the slot; `H`: the threshold; `v`: the
  validator.

Read aloud: after healing there is one justification per height, so nothing contests, and the
least viable height is the greatest chain-state height minus one.



Caches at step `i`: the one caches fact the proof reads, `v`'s at step `i`.  -/
theorem lem91d_not_contested_until (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ i s' H : ℕ) (v : V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    -- fewer than a quorum of validators have been in the adversary set up to the later of `x.time i` and the hand-over cutoff
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (max (x.time i) (M.supportCutoff S.C (s₀ + 1))))
    (hChain : ConfirmationsChainBefore M S A x s₀ s')
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hCaches : CachesOnChain M S A x s₀ H (x.st i v))
    (hv : v ∉ A.corrupted i)
    (hs' : ∀ s_a : ℕ, (∃ (k : ℕ) (u : V), k < i ∧ x.lbl k = Event.tick u (M.supportCutoff S.C (s_a + 1))) →
      s_a < s') :
    M.fg_contest (x.st i v) = false ∧
      M.head_height_floor (x.st i v) = hMax M S.C (x.st i v) - 1 :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem91d_not_contested_until M F U Fx) S A x R s₀
    i s' H v E hAdvQ hChain hOld hCaches hv hs'

/-- **Lemma 91 (e), the honest proposal reaches the proposer's greatest chain-state height.** In an
execution where every time is reached and corruption is permanent, a root names one block among what
honest validators hold; under unforgeability and when fewer than a quorum of validators are ever in
the adversary set: let slot `s` start after `x[i₁].time`; let the updaters' confirmations of the
slots from `s₀` to before `s − 1` form one chain (`ConfirmationsChainBefore`); let every honest
attestation sent before the support cutoff of slot `s₀ + 1` have height at most `H`; let every
validator honest at a step at a time at least `x[i₁].time` have its caches on the honest chain
with justification height greater than `H`; let `p` be honest at the start of slot `s`, and its
tick at the start of slot `s` put `B` on the wire; let `B`'s parent have a chain-state height at
least `head_height_floor` of `p`'s FG state before the start of slot `s`, and every block on the
honest chain before slot `s − 1` be an ancestor of `B`'s parent, or it. Then `B`'s chain-state
height is at least `m`, the greatest chain-state height of `p`'s tree before the start of slot `s`.

Why: `p` holds a block `Y` at `m`; the block `Y₁` that raised `Y`'s chain past `m − 1` carries a
progress certificate at `m − 1 > H` for its parent's `T_h`, which is the chain's entry `E` at
`m − 1`, confirmed at a slot `s_a` with `s_a + 2 ≤ s`, so an ancestor of `B`'s parent; every
attestation of the certificate is in `p`'s pool (`pool_holds_chain_attestations`). If `B`'s parent
is at `m` or more, so is `B`. Otherwise the parent is at `m − 1` (Lemma 91 (d)), `E` is its `T_h`,
and Lemma 53 puts `B` at `m`, or at `m − 1` with `B.slot < E.slot + δt`; the second is excluded by
the branch that raised `Y₁`'s chain (Lemma 67 (b)): a justification certificate makes Lemma 53's
second part put `B` at `m`, and a timeout gives `E.slot + δt ≤ Y₁.slot ≤ s = B.slot`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `s`: the slot;
  `i₁`: the step at the phase's end; `H`: the threshold; `p`: the proposer; `B`: the proposal.

Read aloud: an honest proposer always includes the certificate that reached the greatest height it
knows.



Roots name blocks until the real time of `p`'s tick to `M.slotStart S.C s`: the proof
compares a block `p` holds at that tick (the entry `T_h` of a chain state on `p`'s chain) with the
entry of the honest chain at a slot whose update ran by then. -/
theorem lem91e_proposal_height_ge_h_max (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ s i₁ H : ℕ) (p : V) (B : Block V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    -- the two clock bounds together are less than one delay
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    -- roots name blocks up to the real time of the proposer's tick to the slot's start
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep p (M.slotStart S.C s))))
    -- fewer than a quorum of validators have been in the adversary set up to the later of the real time of that tick
    -- and the hand-over cutoff
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V)
      (max (x.time (x.tickStep p (M.slotStart S.C s))) (M.supportCutoff S.C (s₀ + 1))))
    -- the slot starts after the phase's end, and every tick of the proposer to that start is at or after it
    (hs : x.time i₁ < M.slotStart S.C s ∧
      ∀ k : ℕ, x.lbl k = Event.tick p (M.slotStart S.C s) → x.time i₁ ≤ x.time k)
    (hChain : ConfirmationsChainBefore M S A x s₀ (s - 1))
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x.time i₁ ≤ x.time j → u ∉ A.corrupted j →
      CachesOnChain M S A x s₀ H (x.st j u))
    (hp : p ∉ A.corruptedAtTime x (M.slotStart S.C s))
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C s) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    (hParentHeightP : M.head_height_floor (x.tickInput p (M.slotStart S.C s)) ≤
      (M.chainStateOf S.C B.parent).h)
    (hParentChain : ∀ C : Block V, OnHonestChainBefore M S A x s₀ (s - 1) C →
      C.AncestorEq B.parent) :
    hMax M S.C (x.tickInput p (M.slotStart S.C s)) ≤ (M.chainStateOf S.C B).h :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem91e_proposal_height_ge_h_max M F U Fx) S A
    x R s₀ s i₁ H p B E hSkew hRoots hAdvQ hs hChain hOld hCaches hp hPropose hParentHeightP
    hParentChain

/-- **Lemma 91 (e), the honest proposal reaches the proposer's greatest chain-state height.** In an
execution where every time is reached and corruption is permanent, a root names one block among what
honest validators hold; under unforgeability and when fewer than a quorum of validators are ever in
the adversary set: let slot `s` start after `x[i₁].time`; let the updaters' confirmations of the
slots from `s₀` to before `s − 1` form one chain (`ConfirmationsChainBefore`); let every honest
attestation sent before the support cutoff of slot `s₀ + 1` have height at most `H`; let every
validator honest at a step at a time from `x[i₁].time` to `M.slotStart S.C s` have its caches on the
honest chain with justification height greater than `H`; let `p` be honest at the start of slot `s`,
and its tick at the start of slot `s` put `B` on the wire; let `B`'s parent have a chain-state
height at least `head_height_floor` of `p`'s FG state before the start of slot `s`, and every block
on the honest chain before slot `s − 1` be an ancestor of `B`'s parent, or it. Then `B`'s
chain-state height is at least `m`, the greatest chain-state height of `p`'s tree before the start
of slot `s`.

Why: `p` holds a block `Y` at `m`; the block `Y₁` that raised `Y`'s chain past `m − 1` carries a
progress certificate at `m − 1 > H` for its parent's `T_h`, which is the chain's entry `E` at
`m − 1`, confirmed at a slot `s_a` with `s_a + 2 ≤ s`, so an ancestor of `B`'s parent; every
attestation of the certificate is in `p`'s pool (`pool_holds_chain_attestations`). If `B`'s parent
is at `m` or more, so is `B`. Otherwise the parent is at `m − 1` (Lemma 91 (d)), `E` is its `T_h`,
and Lemma 53 puts `B` at `m`, or at `m − 1` with `B.slot < E.slot + δt`; the second is excluded by
the branch that raised `Y₁`'s chain (Lemma 67 (b)): a justification certificate makes Lemma 53's
second part put `B` at `m`, and a timeout gives `E.slot + δt ≤ Y₁.slot ≤ s = B.slot`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `s`: the slot;
  `i₁`: the step at the phase's end; `H`: the threshold; `p`: the proposer; `B`: the proposal.

Read aloud: an honest proposer always includes the certificate that reached the greatest height it
knows.



Roots name blocks until the real time of `p`'s tick to `M.slotStart S.C s`: the proof
compares a block `p` holds at that tick (the entry `T_h` of a chain state on `p`'s chain) with the
entry of the honest chain at a slot whose update ran by then.

Caches at `p`'s tick to `M.slotStart S.C s`: the one caches fact the proof reads.  -/
theorem lem91e_proposal_height_ge_h_max_until (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ s i₁ H : ℕ) (p : V) (B : Block V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    -- the two clock bounds together are less than one delay
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    -- roots name blocks up to the real time of the proposer's tick to the slot's start
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep p (M.slotStart S.C s))))
    -- fewer than a quorum of validators have been in the adversary set up to the later of the real time of that tick
    -- and the hand-over cutoff
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V)
      (max (x.time (x.tickStep p (M.slotStart S.C s))) (M.supportCutoff S.C (s₀ + 1))))
    -- the slot starts after the phase's end, and every tick of the proposer to that start is at or after it
    (hs : x.time i₁ < M.slotStart S.C s ∧
      ∀ k : ℕ, x.lbl k = Event.tick p (M.slotStart S.C s) → x.time i₁ ≤ x.time k)
    (hChain : ConfirmationsChainBefore M S A x s₀ (s - 1))
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    -- the proposer's caches at its tick to the slot's start are on the honest chain
    (hCaches : CachesOnChain M S A x s₀ H (x.tickInput p (M.slotStart S.C s)))
    (hp : p ∉ A.corruptedAtTime x (M.slotStart S.C s))
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C s) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    (hParentHeightP : M.head_height_floor (x.tickInput p (M.slotStart S.C s)) ≤
      (M.chainStateOf S.C B.parent).h)
    (hParentChain : ∀ C : Block V, OnHonestChainBefore M S A x s₀ (s - 1) C →
      C.AncestorEq B.parent) :
    hMax M S.C (x.tickInput p (M.slotStart S.C s)) ≤ (M.chainStateOf S.C B).h :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem91e_proposal_height_ge_h_max_until M F U Fx) S
    A x R s₀ s i₁ H p B E hSkew hRoots hAdvQ hs hChain hOld hCaches hp hPropose
    hParentHeightP hParentChain

/-- **Lemma 91 (f), the root of an honest fork choice is on the chain before `s'`.** In an execution
where every time is reached and corruption is permanent, a root names one block among what honest
validators hold; under unforgeability and when fewer than a quorum of validators are ever in the
adversary set: let every honest attestation sent before the support cutoff of slot `s₀ + 1` have
height at most `H`; let every validator honest at a step at a time at least
`x[i₁].time` have its caches on the honest chain with justification height greater than `H`. Then
at a step `j` at a time at least `x[i₁].time`, for `w` honest at that time and a slot `s'` such
that every slot `s_a` to whose support cutoff of slot `s_a + 1` some validator ticked at a step before that step is less than `s'`, the root of `w`'s fork choice (`fc_root` of the frame) is on the honest chain before slot
`s'`.

Why: the root is the justified block `J` or the finalized block, an ancestor of `J`. `J` is the
justified block of a chain state of a block `D` of `w`'s tree (`CachesWitnessed`), certified on
`D`'s chain at `h_j > H` (Lemma 66); the certificate route names an entry of the chain at `h_j`,
confirmed at a slot `s_a` to whose support cutoff the attester ticked at a step before the step, so `s_a < s'`; that
entry and `J` have one root and are held by honest validators, so they are one block
.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `i₁`: the step
  at the phase's end; `j`: the step; `s'`: the bound on the slot; `H`: the threshold; `w`: the
  validator.

Read aloud: the root of an honest fork choice is on the chain confirmed by the attestations sent
by then.



Roots name blocks until `x[j].time`: the proof compares `w`'s justified block, held after `j`
steps, with the entry of the honest chain at a slot whose update ran by `x[j].time`. -/
theorem lem91f_voter_root_on_chain_before (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ i₁ j s' H : ℕ) (w : V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hRoots : RootsNameBlocksUntil M A x (x.time j))
    -- fewer than a quorum of validators have been in the adversary set up to the later of `x.time j` and the hand-over cutoff
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (max (x.time j) (M.supportCutoff S.C (s₀ + 1))))
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x.time i₁ ≤ x.time j → u ∉ A.corrupted j →
      CachesOnChain M S A x s₀ H (x.st j u))
    (hj : x.time i₁ ≤ x.time j) (hw : w ∉ A.corrupted j)
    (hs' : ∀ s_a : ℕ, (∃ (k : ℕ) (u : V), k < j ∧ x.lbl k = Event.tick u (M.supportCutoff S.C (s_a + 1))) →
      s_a < s') :
    OnHonestChainBefore M S A x s₀ s' (M.fg_to_ac (x.st j w)).fc_root :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem91f_voter_root_on_chain_before M F U Fx) S
    A x R s₀ i₁ j s' H w E hRoots hAdvQ hOld hCaches hj hw hs'

/-- **Lemma 91 (f), the root of an honest fork choice is on the chain before `s'`.** In an execution
where every time is reached and corruption is permanent, a root names one block among what honest
validators hold; under unforgeability and when fewer than a quorum of validators are ever in the
adversary set: let every honest attestation sent before the support cutoff of slot `s₀ + 1` have
height at most `H`; let every validator honest at a step at a time from `x[i₁].time` to `x[j].time`
have its caches on the honest chain with justification height greater than `H`. Then at a step `j`
at a time at least `x[i₁].time`, for `w` honest at that time and a slot `s'` such that every slot `s_a` to whose support cutoff of slot `s_a + 1` some validator ticked at a step before that step is less than `s'`, the root of
`w`'s fork choice (`fc_root` of the frame) is on the honest chain before slot `s'`.

Why: the root is the justified block `J` or the finalized block, an ancestor of `J`. `J` is the
justified block of a chain state of a block `D` of `w`'s tree (`CachesWitnessed`), certified on
`D`'s chain at `h_j > H` (Lemma 66); the certificate route names an entry of the chain at `h_j`,
confirmed at a slot `s_a` to whose support cutoff the attester ticked at a step before the step, so `s_a < s'`; that
entry and `J` have one root and are held by honest validators, so they are one block
.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `j`: the step; `s'`: the bound on the slot; `H`: the threshold; `w`: the
  validator.

Read aloud: the root of an honest fork choice is on the chain confirmed by the attestations sent
by then.



Roots name blocks until `x[j].time`: the proof compares `w`'s justified block, held after `j`
steps, with the entry of the honest chain at a slot whose update ran by `x[j].time`.

Caches at step `j`: the one caches fact the proof reads, `w`'s at step `j`.  -/
theorem lem91f_voter_root_on_chain_before_until (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s₀ j s' H : ℕ) (w : V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hRoots : RootsNameBlocksUntil M A x (x.time j))
    -- fewer than a quorum of validators have been in the adversary set up to the later of `x.time j` and the hand-over cutoff
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (max (x.time j) (M.supportCutoff S.C (s₀ + 1))))
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hCaches : CachesOnChain M S A x s₀ H (x.st j w))
    (hw : w ∉ A.corrupted j)
    (hs' : ∀ s_a : ℕ, (∃ (k : ℕ) (u : V), k < j ∧ x.lbl k = Event.tick u (M.supportCutoff S.C (s_a + 1))) →
      s_a < s') :
    OnHonestChainBefore M S A x s₀ s' (M.fg_to_ac (x.st j w)).fc_root :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem91f_voter_root_on_chain_before_until M F U Fx)
    S A x R s₀ j s' H w E hRoots hAdvQ hOld hCaches hw hs'

end GoldilocksCorrectness.Record.Statements.Executions

