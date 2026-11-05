module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.HealedTop
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.Lemma89Statements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.ConfirmedTipStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.HealedVoterFrameStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.HealedChainBeforeStatements
public import GoldilocksCorrectness.Statements.Executions.Lemma89Statements
public import GoldilocksCorrectness.Statements.Executions.ConfirmedTipStatements
public import GoldilocksCorrectness.Statements.Executions.HealedVoterFrameStatements
public import GoldilocksCorrectness.Statements.Executions.HealedChainBeforeStatements
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# HealedTopStatements, over a model

The statements of `GoldilocksCorrectness/Statements/Executions/HealedTopStatements.lean`, over a
model `M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: the frames at every slot
after the healed slot, the facts after the hand-over, Lemma 86 (finality safety after healing) and
Lemma 90 (the confirmed tip after healing), each also for the readings up to a time `t`. Each is a
one-line call of its proof page's twin of the same name, under `Record/Restated/Proofs/Executions/`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

open GoldilocksCorrectness.Statements.Routines (Δ Δ_F slotStart voteTime supportCutoff anchorCW)

namespace GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Statements.Executions (healFrontSlots)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor hMax le_hMax IsEntry VoterTreeAt JustifiedInTree AnchorAt)
open GoldilocksCorrectness.Statements.Executions (OpeningsOutsideWaitsAndWindows Vocab.goldilocks
  acObject fgObject healFrontSlots)

open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-! ## The frames at every slot after the healed slot -/

/-- **The frames at every slot after the healed slot.** Lemma 81's base facts and execution
assumptions; the old attestations at most `H`; the caches from `i₂` to `t`, `i₂` a step before
the view freeze of slot `s_m`; Lemma 89's frames for `s₀ < s < s_m`, the voter frame at
`roundMembers M S Sched (s + 1)` and the updater frame at `updaterAt M S A x s`;
and the voter frame at `s_m` for every validator honest at `M.voteTime S.C s_m`: then the voter frame
holds at every slot after `s₀` whose update, at the support cutoff of the next slot, is at most `t`,
at the honest active validators, and the updater frame at every updater of a slot after `s₀` whose
own tick to the support cutoff of the next slot is at a real time at most `t`.

The hypotheses, in words: every time is reached; corruption is permanent; blocks and Goldfish votes
are delivered within `Δ` after `GST`; a root names one block among what
honest validators hold at steps at times at most `t`; a block reaches a validator only once it holds
the parent; nobody votes in an honest validator's name; unforgeability; fewer than a quorum of
validators have been in the adversary set up to every time; `GST` is at most the vote time of slot
`s₀`; committee sleepiness holds from `anchor`, at or before the start of slot `s₀ + 1`; `B₀`'s slot
is at least `s₀`; `HonestChainExtends` holds for `B₀` at slot `s₀`; every updater of slot `s₀` saved
`B₀`; every honest attestation sent before the support cutoff of slot `s₀ + 1` has height at most
`H`; step `i₂` is before the view freeze of slot `s_m`; every validator outside the adversary set at
a step at a time from `x[i₂].time` to `t` has its caches on the honest chain in the state that step
leaves; at every slot `s` with
`s₀ < s < s_m`, every member of `roundMembers M S Sched (s + 1)` has the voter frame at `s` and every
validator of `updaterAt M S A x s` (awake and honest up to its own tick to the support cutoff of slot
`s + 1`) has the updater frame at `s`; every
validator outside the adversary set at `M.voteTime S.C s_m` has the voter frame at `s_m`.

Why: by strong induction on the slot. Before `s_m`, Lemma 89's frames, since the honest active
validators of `s` are members of `roundMembers M S Sched (s + 1)`; from `s_m` on,
the frames at the slots before `s` make the confirmations before `s` one chain
(`lem81_chain_before`), and the voter frame comes from Lemma 89's clause at `s_m` and from
`voterFrame_after_handover` after it, the updater frame from `updaterFrame_after_handover`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `s_m`: the last honest round opening slot; `i₂`:
  the step from which the caches are on the chain; `H`: the threshold; `anchor`: the time from
  which committee sleepiness holds; `t`: the bound on the slots' update times; `B₀`: the block
  every updater of slot `s₀` saved.



Roots name blocks until `t`: the conclusions are for the slots `s` whose update, at the support
cutoff of slot `s + 1`, is at most `t`; at such a slot the proof reads `lem81_chain_before` up to
the support cutoff of slot `s`, `voterFrame_after_handover` up to the vote time of slot `s` and
`updaterFrame_after_handover` up to the support cutoff of slot `s + 1`.
Every updater of a slot from the healed slot `s₀` on, whose
update is at most `t`, stays active for `Δs` after the real time of its own tick to the support cutoff
of the next slot.

Read aloud: the phase's frames, carried past the hand-over by strong induction on the slot, at
every slot whose update is at most `t`.

Caches up to `t`: at a slot `s` the proof reads the caches up to the support cutoff of slot `s + 1`,
at most `t`.  -/
theorem frames_after_healed_slot_until (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ s_m i₂ H anchor t : ℕ) (B₀ : Block V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x t)
    (hParent : ParentHeldAtDelivery M x)
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) t)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀)
    (hSleepK : CommitteeSleepinessUntil M S A x anchor t)
    -- every tick at a real time at most `t`, to a clock value `c`: committee sleepiness from `anchor` read up to `c`
    --
    (hSleepKTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → (x.time k : ℝ) ≤ t →
      CommitteeSleepinessUntil M S A x anchor c)
    -- every updater of a slot from the healed slot `s₀` on, whose update is at most `t`, is active for the
    -- sync delay after the real time of its own tick to the support cutoff of the next slot
    --
    (hStay : ∀ σ : ℕ, s₀ ≤ σ → M.supportCutoff S.C (σ + 1) ≤ t → ∀ u ∈ updaterAt M S A x σ,
      u ∈ A.activeThroughout x (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))))
        (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))) + Δs))
    (hAnchor : anchor ≤ M.slotStart S.C (s₀ + 1))
    (hB₀slot : s₀ ≤ B₀.slot)
    (hBase : HonestChainExtends M S A x (honestActiveAt M S A x s₀) B₀ s₀)
    (hBaseSaved : ∀ v ∈ updaterAt M S A x s₀,
      (x.tickOutput v (M.supportCutoff S.C (s₀ + 1))).savedConfirmation s₀ = some B₀)
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hi₂ : x.time i₂ < M.viewFreeze S.C s_m)
    (hCaches : ∀ (j : ℕ) (u : V), x.time i₂ ≤ x.time j → x.time j ≤ t →
      u ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st (j + 1) u))
    (hPhase : ∀ s : ℕ, s₀ < s → s < s_m →
      (∀ w ∈ roundMembers M S A x (s + 1), VoterFrameOnChainAt M S A x s₀ s w) ∧
      (∀ v ∈ updaterAt M S A x s, UpdaterFinalizedOnChainAt M S A x s₀ s v))
    (hLast : ∀ w : V, w ∉ A.corruptedAtTime x (M.voteTime S.C s_m) →
      VoterFrameOnChainAt M S A x s₀ s_m w) :
    (∀ s : ℕ, s₀ < s → M.supportCutoff S.C (s + 1) ≤ t →
      ∀ w ∈ honestActiveAt M S A x s, VoterFrameOnChainAt M S A x s₀ s w) ∧
    (∀ s : ℕ, s₀ < s → ∀ v ∈ updaterAt M S A x s,
      x.time (x.tickStep v (M.supportCutoff S.C (s + 1))) ≤ t → UpdaterFinalizedOnChainAt M S A x s₀ s v) :=
  (GoldilocksCorrectness.Record.Proofs.Executions.frames_after_healed_slot_until M F U Fx) S A x R
    GST s₀ s_m i₂ H anchor t B₀ E hNet hSkew hRedeliver Sy hΔs hRoots hParent hAdvQ hGST hSleepK hSleepKTick hStay
    hAnchor hB₀slot hBase hBaseSaved hOld hi₂ hCaches hPhase hLast

/-! ## The facts after the hand-over -/

/-- **The facts after the hand-over, for the readings up to a time `t`.** Under the top statements'
premises without a premise on roots, for every time `t` from `tAwakeEnd` on: some honest round opening slot's
proposal has the root of a block its proposer held (`RootCollisionAtOpening`); or two distinct
blocks that honest validators hold at steps at times at most `t` have the same root
(`RootCollisionHeldBy M S Sched x t`); or there are a healed slot `s₀` with its block `B₀` and a
step `i₂` one time unit after the vote time of the last opening's first slot, with Lemma 81's base
facts, the times every later lemma reads, the old attestations at most `H := h(B₀)`, the caches
from `i₂` at, and after, every step at a time at most `t`, the voter frame at every slot after `s₀` whose
update, the support cutoff of the next slot, is at most `t`, the updater frame at every updater of
such a slot whose own tick to that cutoff is at a real time at most `t`, and, for every slot `σ` whose
update some validator ran at a step by the time `t`, the updaters' confirmations of the slots from `s₀` to before `σ` forming one chain and
the confirmations of slot `σ` saved by the updaters whose tick to that cutoff is by `t` extending it
and, when `σ` is `s₀` or a later slot, compatible with each other.

 every validator's tick to the
healed slot's update is before `i₂`. The healed slot `s₀` is at or after the first honest round
opening slot `r 0 * S.C.R`. A slot start is a multiple of `4Δ`, the time of `i₂` is one time unit after
the vote time of slot `s_m`, and `tAwakeEnd` is at least the support cutoff of slot `s_m`. Lemma
90's inclusion reads the slots starting at or after `tAwakeEnd` through it.

The hypotheses, in words: `GST` is at most `tGAT`; every time is reached; corruption is permanent;
blocks, Goldfish votes and attestations are delivered within their delays after `GST`;
a block reaches a validator only once it holds the parent; unforgeability;
fewer than a third of the validators have been in the adversary set up to `tAwakeEnd`; every
validator outside the adversary set at a time from `tGAT` to `tAwakeEnd` is awake then; committee
sleepiness from `anchorCW S tGAT`; the honest round opening slots of the rounds `r 0 < … < r m` lie between
`tGAT + 4Δ · healFrontSlots S` and `tAwakeEnd`; nine honest round opening slots lie outside every
two spans of `δt` slots and five spans of `k + 2` slots; fewer than a quorum of validators have been
in the adversary set up to every time. No premise on roots: the conclusion names the collision.
Every updater of a slot from the first honest round opening slot `r 0 * S.C.R` on, whose
update is at most `t`, stays active for `Δs` after the real time of its own tick to the support cutoff
of the next slot.

Why: when no collision has hit by `t`, roots name blocks up to `t`, and `healed_handover_facts`'s
route reads nothing after `t`: Lemma 89 up to `tAwakeEnd`, the caches from `i₂` up to `t`
(`caches_after_handover`), the frames at the slots whose update is at most `t`
(`frames_after_healed_slot_until`), and the chain before the slot after each such slot
(`lem81_chain_before`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `tGAT`, `tAwakeEnd`: the start and end of the healing phase; `m`: the
  index of the last honest round opening slot; `r`: the rounds of the honest round opening slots.


`tAwakeEnd ≤ t`: the phase's proof (Lemma 89) compares blocks held up to the support cutoff of the
last opening's first slot, at most `tAwakeEnd`, whatever `t` is.

Read aloud: for every time `t` after the phase, unless a collision has hit an honest proposal or two
blocks held by `t`, the honest chain after healing exists up to `t` and every honest validator's
caches stay on it up to `t`. -/
theorem healed_handover_facts_until (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd m : ℕ) (r : ℕ → ℕ)
    (hGST : GST ≤ tGAT)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {ΔNet_F : ℕ} (E_F : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    {Δs_F : ℕ} (Sy_F : SyncedWithin A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST)
    (hΔs_F : (Δs_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S ∨ (Δs_F : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind ≤ 4 * Δ S * S.C.k)
    -- for each honest round opening slot, every validator outside the adversary set at the support cutoff of the slot
    -- after its first slot is active through the attestations' sync delay after the later of that first slot's duty
    -- window's start and `GST`
    (hHoldF : ∀ i, i < m → ∀ v, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (r i * S.C.R + 1)) →
      v ∈ A.activeThroughout x ((max (M.dutyWindowStart S.C (r i * S.C.R)) GST : ℕ) : ℝ)
        (((max (M.dutyWindowStart S.C (r i * S.C.R)) GST : ℕ) : ℝ) + Δs_F))
    (hParent : ParentHeldAtDelivery M x)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    -- at every slot of the phase, every validator honest at the slot's update is an honest active validator and an
    -- updater of the slot
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (t : ℕ) (ht : tAwakeEnd ≤ t)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) t)
    -- every tick at a real time at most `t`, to a clock value `c`: committee sleepiness from `anchorCW S tGAT` read up
    -- to `c`
    (hCommitteesTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → (x.time k : ℝ) ≤ t →
      CommitteeSleepinessUntil M S A x (anchorCW S tGAT) c)
    -- every updater of a slot from the first honest round opening slot `r 0 * S.C.R` on, whose update is at
    -- most `t`, is active for the sync delay after the real time of its own tick to the support cutoff of the
    -- next slot
    (hStay : ∀ σ : ℕ, r 0 * S.C.R ≤ σ → M.supportCutoff S.C (σ + 1) ≤ t → ∀ u ∈ updaterAt M S A x σ,
      u ∈ A.activeThroughout x (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))))
        (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))) + Δs))
    (hSeq : HonestOpeningSeq M S A x r m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hOpenings : OpeningsOutsideWaitsAndWindows S r m)
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) t) :
      RootCollisionAtOpening M S A x r m ∨ RootCollisionHeldBy M S A x t ∨
      ∃ (s₀ i₂ : ℕ) (B₀ : Block V),
        (M.supportCutoff S.C (s₀ + 1) < x.time i₂ ∧
          ∀ (k : ℕ) (u : V), x.lbl k = Event.tick u (M.supportCutoff S.C (s₀ + 1)) → x.time k < x.time i₂) ∧
        x.time i₂ ≤ tAwakeEnd ∧
        (∀ s : ℕ, tAwakeEnd ≤ M.slotStart S.C s → x.time i₂ < M.slotStart S.C s ∧
          ∀ (k : ℕ) (u : V), x.lbl k = Event.tick u (M.slotStart S.C s) → x.time i₂ < x.time k) ∧
        r 0 * S.C.R ≤ s₀ ∧
        GST ≤ M.voteTime S.C s₀ ∧ anchorCW S tGAT ≤ M.slotStart S.C (s₀ + 1) ∧ s₀ ≤ B₀.slot ∧
        HonestChainExtends M S A x (honestActiveAt M S A x s₀) B₀ s₀ ∧
        (∀ v ∈ updaterAt M S A x s₀,
          (x.tickOutput v (M.supportCutoff S.C (s₀ + 1))).savedConfirmation s₀ = some B₀) ∧
        (∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s₀ + 1)) →
          v ∈ updaterAt M S A x s₀) ∧
        OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) (M.chainStateOf S.C B₀).h ∧
        (∀ (j : ℕ) (u : V), x.time i₂ ≤ x.time j → x.time j ≤ t →
          u ∉ A.corrupted j →
          CachesOnChain M S A x s₀ (M.chainStateOf S.C B₀).h (x.st j u)) ∧
        (∀ (j : ℕ) (u : V), x.time i₂ ≤ x.time j → x.time j ≤ t →
          u ∉ A.corrupted j →
          CachesOnChain M S A x s₀ (M.chainStateOf S.C B₀).h (x.st (j + 1) u)) ∧
        (∀ s : ℕ, s₀ < s → M.supportCutoff S.C (s + 1) ≤ t →
          ∀ w ∈ honestActiveAt M S A x s, VoterFrameOnChainAt M S A x s₀ s w) ∧
        (∀ s : ℕ, s₀ < s → ∀ v ∈ updaterAt M S A x s,
          x.time (x.tickStep v (M.supportCutoff S.C (s + 1))) ≤ t → UpdaterFinalizedOnChainAt M S A x s₀ s v) ∧
        (∀ (σ k : ℕ) (u : V), x.lbl k = Event.tick u (M.supportCutoff S.C (σ + 1)) →
          x.time k ≤ t → ConfirmationsChainBefore M S A x s₀ σ ∧
          ∀ v ∈ updaterAt M S A x σ, x.time (x.tickStep v (M.supportCutoff S.C (σ + 1))) ≤ t →
          ∀ C' : Block V, (x.tickOutput v (M.supportCutoff S.C (σ + 1))).savedConfirmation σ = some C' →
          (∀ C : Block V, OnHonestChainBefore M S A x s₀ σ C → C.AncestorEq C') ∧
          (s₀ ≤ σ → ∀ v' ∈ updaterAt M S A x σ, x.time (x.tickStep v' (M.supportCutoff S.C (σ + 1))) ≤ t →
          ∀ C'' : Block V, (x.tickOutput v' (M.supportCutoff S.C (σ + 1))).savedConfirmation σ = some C'' →
          C'.compatible C'' = true)) :=
  (GoldilocksCorrectness.Record.Proofs.Executions.healed_handover_facts_until M F U Fx) S A x R
    GST tGAT tAwakeEnd m r hGST E hNet hSkew hRedeliver E_F hNet_F hSkew_F Sy hΔs Sy_F hΔs_F hHoldF hParent hThird hAwake hActive
    t ht hCommittees hCommitteesTick hStay hSeq hOpenings hAdvQ

/-! ## Lemma 86, finality safety after healing -/

/-- **Lemma 86, finality safety after healing.** Under the execution
assumptions, the healing phase's premises with nine honest round opening slots outside every two
spans of `δt` slots and five spans of `k + 2` slots (`OpeningsOutsideWaitsAndWindows`), and fewer
than two thirds of the validators ever in the adversary set: either some honest round opening slot's proposal has the
root of a block its proposer held, or the finalized blocks of any two validators, each at a step
through which it has been honest, are compatible.

The hypotheses, in words: `GST` is at most `tGAT`; every time is reached; corruption is permanent;
blocks, Goldfish votes and attestations are delivered within their delays after `GST`;
a root names one block among what honest validators hold; a block reaches a
validator only once it holds the parent; unforgeability; fewer than a third of the validators have
been in the adversary set up to `tAwakeEnd`; every validator outside the adversary set at a time
from `tGAT` to `tAwakeEnd` is awake then; committee sleepiness from `anchorCW S tGAT`; the honest
openings `r 0 < … < r m` lie between `tGAT + 4Δ · healFrontSlots S` and `tAwakeEnd`; nine
honest round opening slots lie outside every two spans of `δt` slots and five spans of `k + 2`
slots; fewer than two thirds of the validators have been in the adversary set up to every time.
Every updater of a slot from the first honest round opening slot `r 0 * S.C.R` on stays active for
`Δs` after the real time of its own tick to the support cutoff of the next slot.

Why: `lem86_healed_finality_safety_until` at `t := max tAwakeEnd (max x[i].time x[j].time)` for the
two steps, the premises at `t` given by the ones for all time; a collision among the
blocks held by `t` contradicts roots naming blocks for all time.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `tGAT`, `tAwakeEnd`: the start and end of the healing phase; `m`: the
  index of the last honest round opening slot; `r`: the rounds of the honest round opening slots.



Read aloud: once the phase has lasted through enough honest round opening slots, two honest validators never
finalize conflicting blocks, at any two steps, unless a digest collision hit an honest proposal. -/
theorem lem86_healed_finality_safety
    (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd m : ℕ) (r : ℕ → ℕ)
    (hGST : GST ≤ tGAT)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {ΔNet_F : ℕ} (E_F : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    {Δs_F : ℕ} (Sy_F : SyncedWithin A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST)
    (hΔs_F : (Δs_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S ∨ (Δs_F : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind ≤ 4 * Δ S * S.C.k)
    -- for each honest round opening slot, every validator outside the adversary set at the support cutoff of the slot
    -- after its first slot is active through the attestations' sync delay after the later of that first slot's duty
    -- window's start and `GST`
    (hHoldF : ∀ i, i < m → ∀ v, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (r i * S.C.R + 1)) →
      v ∈ A.activeThroughout x ((max (M.dutyWindowStart S.C (r i * S.C.R)) GST : ℕ) : ℝ)
        (((max (M.dutyWindowStart S.C (r i * S.C.R)) GST : ℕ) : ℝ) + Δs_F))
    (hRoots : RootsNameBlocks M A x)
    (hParent : ParentHeldAtDelivery M x)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    -- at every slot of the phase, every validator honest at the slot's update is an honest active validator and an
    -- updater of the slot
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : CommitteeSleepiness M S A x (anchorCW S tGAT))
    -- every updater of a slot from the first honest round opening slot `r 0 * S.C.R` on is active for the
    -- sync delay after the real time of its own tick to the support cutoff of the next slot
    --
    (hStay : ∀ σ : ℕ, r 0 * S.C.R ≤ σ → ∀ u ∈ updaterAt M S A x σ,
      u ∈ A.activeThroughout x (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))))
        (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))) + Δs))
    (hSeq : HonestOpeningSeq M S A x r m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hOpenings : OpeningsOutsideWaitsAndWindows S r m)
    (hAdvQ : ∀ t : ℕ, A.AdversaryFewerThanTwoThirdsUntil x (validator_count V) t) :
    RootCollisionAtOpening M S A x r m ∨
      ∀ (v₁ v₂ : V) (i j : ℕ), x.HonestThrough A i v₁ → x.HonestThrough A j v₂ →
        (x.st i v₁).finalized.compatible (x.st j v₂).finalized = true :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem86_healed_finality_safety M F U Fx) S A x R
    GST tGAT tAwakeEnd m r hGST E hNet hSkew hRedeliver E_F hNet_F hSkew_F Sy hΔs Sy_F hΔs_F hHoldF hRoots hParent hThird
    hAwake hActive hCommittees hStay hSeq hOpenings hAdvQ

/-- **Lemma 86, finality safety after healing, for the readings up to a time `t`.** Under the top
statements' premises without a premise on roots, for every time `t` from `tAwakeEnd` on: some
honest round opening slot's proposal has the root of a block its proposer held (`RootCollisionAtOpening`); or
two distinct blocks that honest validators hold at steps at times at most `t` have the same root
(`RootCollisionHeldBy M S Sched x t`); or the finalized blocks of any two validators, each at a step
at a time at most `t` through which it has been honest, are compatible.

The hypotheses, in words: `GST` is at most `tGAT`; every time is reached; corruption is permanent;
blocks, Goldfish votes and attestations are delivered within their delays after `GST`;
a block reaches a validator only once it holds the parent; unforgeability;
fewer than a third of the validators have been in the adversary set up to `tAwakeEnd`; every
validator outside the adversary set at a time from `tGAT` to `tAwakeEnd` is awake then; committee
sleepiness from `anchorCW S tGAT` for the slots whose update is at most `t`; the honest round
opening slots of the rounds `r 0 < … < r m` lie between `tGAT + 4Δ · healFrontSlots S` and
`tAwakeEnd`; nine honest round opening slots lie outside every two spans of `δt` slots and five
spans of `k + 2` slots; fewer than two thirds of the validators have been in the adversary set up
to `t`. No premise on roots: the conclusion names the collision.
Every updater of a slot from the first honest round opening slot `r 0 * S.C.R` on, whose
update is at most `t`, stays active for `Δs` after the real time of its own tick to the support cutoff
of the next slot.

Why: the facts after the hand-over up to `t` (`healed_handover_facts_until`); Lemma 85 at the step
`i₂`, keeping the slot (`lem85_honest_finalized_on_chain_at`), puts every such finalized block on
the honest chain at a slot whose update is at most `t`; two such blocks are compatible, the
updaters' confirmations up to the later slot forming one chain.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `tGAT`, `tAwakeEnd`: the start and end of the healing phase; `m`: the
  index of the last honest round opening slot; `r`: the rounds of the honest round opening slots.


`tAwakeEnd ≤ t`: the phase's proof (Lemma 89) compares blocks held up to the support cutoff of the
last opening's first slot, at most `tAwakeEnd`, whatever `t` is.

Read aloud: for every time `t` after the phase, unless a collision has hit by `t`, no two honest
validators have finalized conflicting blocks by `t`. -/
theorem lem86_healed_finality_safety_until (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd m : ℕ) (r : ℕ → ℕ)
    (hGST : GST ≤ tGAT)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {ΔNet_F : ℕ} (E_F : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    {Δs_F : ℕ} (Sy_F : SyncedWithin A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST)
    (hΔs_F : (Δs_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S ∨ (Δs_F : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind ≤ 4 * Δ S * S.C.k)
    -- for each honest round opening slot, every validator outside the adversary set at the support cutoff of the slot
    -- after its first slot is active through the attestations' sync delay after the later of that first slot's duty
    -- window's start and `GST`
    (hHoldF : ∀ i, i < m → ∀ v, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (r i * S.C.R + 1)) →
      v ∈ A.activeThroughout x ((max (M.dutyWindowStart S.C (r i * S.C.R)) GST : ℕ) : ℝ)
        (((max (M.dutyWindowStart S.C (r i * S.C.R)) GST : ℕ) : ℝ) + Δs_F))
    (hParent : ParentHeldAtDelivery M x)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    -- at every slot of the phase, every validator honest at the slot's update is an honest active validator and an
    -- updater of the slot
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    -- the time up to which the execution is read, after the phase
    (t : ℕ) (ht : tAwakeEnd ≤ t)
    -- committee sleepiness from `anchorCW S tGAT`, for the slots whose update is at most `t`
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) t)
    -- every tick at a real time at most `t`, to a clock value `c`: committee sleepiness from `anchorCW S tGAT` read up
    -- to `c`
    (hCommitteesTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → (x.time k : ℝ) ≤ t →
      CommitteeSleepinessUntil M S A x (anchorCW S tGAT) c)
    -- every updater of a slot from the first honest round opening slot `r 0 * S.C.R` on, whose update is at
    -- most `t`, is active for the sync delay after the real time of its own tick to the support cutoff of the
    -- next slot
    (hStay : ∀ σ : ℕ, r 0 * S.C.R ≤ σ → M.supportCutoff S.C (σ + 1) ≤ t → ∀ u ∈ updaterAt M S A x σ,
      u ∈ A.activeThroughout x (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))))
        (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))) + Δs))
    (hSeq : HonestOpeningSeq M S A x r m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hOpenings : OpeningsOutsideWaitsAndWindows S r m)
    -- fewer than two thirds of the validators corrupted up to `t`
    (hAdvQ : A.AdversaryFewerThanTwoThirdsUntil x (validator_count V) t) :
    RootCollisionAtOpening M S A x r m ∨ RootCollisionHeldBy M S A x t ∨
      ∀ (v₁ v₂ : V) (i j : ℕ), x.HonestThrough A i v₁ → x.HonestThrough A j v₂ →
        x.time i ≤ t → x.time j ≤ t →
        (x.st i v₁).finalized.compatible (x.st j v₂).finalized = true :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem86_healed_finality_safety_until M F U Fx) S
    A x R GST tGAT tAwakeEnd m r hGST E hNet hSkew hRedeliver E_F hNet_F hSkew_F Sy hΔs Sy_F hΔs_F hHoldF hParent hThird
    hAwake hActive t ht hCommittees hCommitteesTick hStay hSeq hOpenings hAdvQ

/-! ## Lemma 90, the confirmed tip after healing -/

/-- **Lemma 90, the confirmed tip after healing.** The hypotheses of
`lem86_healed_finality_safety`, name for name and in its order. Either some honest round opening slot's
proposal has the root of a block its proposer held, or, from `tAwakeEnd` on, the confirmed tips of
two validators honest through their steps are compatible (`ConfirmedAgreeAfterHealing`), the
confirmed tip of a validator honest through the later of two steps only extends
(`ConfirmedMonotoneAfterHealing`), and every honest proposal of a slot starting after `tAwakeEnd`
is the confirmed tip of every honest active validator of its slot right after its update and stays
an ancestor of, or equal to, the confirmed tips that follow (`ConfirmedIncludedAfterHealing`), and
every honest proposal of a slot starting after `tAwakeEnd`, unless its proposer held a block with
its root, is a strict descendant of every confirmed tip a validator honest through its step had
from `tAwakeEnd` until the proposal's slot started (`ConfirmedExtendedByHonestProposals`).

The hypotheses, in words: `GST` is at most `tGAT`; every time is reached; corruption is permanent;
blocks, Goldfish votes and attestations are delivered within their delays after `GST`;
a root names one block among what honest validators hold; a block reaches a
validator only once it holds the parent; unforgeability; fewer than a third of the validators have
been in the adversary set up to `tAwakeEnd`; every validator outside the adversary set at a time
from `tGAT` to `tAwakeEnd` is awake then; committee sleepiness from `anchorCW S tGAT`; the honest
openings `r 0 < … < r m` lie between `tGAT + 4Δ · healFrontSlots S` and `tAwakeEnd`; nine
honest round opening slots lie outside every two spans of `δt` slots and five spans of `k + 2`
slots; fewer than two thirds of the validators have been in the adversary set up to every time. At
every slot whose next slot starts at or after `tAwakeEnd`, its honest active committee members, and
the proposer when the slot has an honest opener, stay active for `Δs` after the times the synchrony
condition reads them.
Every updater of a slot from the first honest round opening slot `r 0 * S.C.R` on stays active for
`Δs` after the real time of its own tick to the support cutoff of the next slot.

Why: `lem90_healed_confirmed_until` at every time `t` from `tAwakeEnd` on, the premises at `t` given
by the ones for all time; a collision among the blocks held by `t` contradicts roots
naming blocks for all time; the agreement and the growth from `tAwakeEnd` on are those read up to
the later step's time, and the inclusion from `tAwakeEnd` on is the inclusion read up to every time
(`confirmedIncludedAfterHealing_iff`); the fourth from the agreement and the inclusion
(`confirmedExtended_of_agree_included`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `tGAT`, `tAwakeEnd`: the start and end of the healing phase; `m`: the
  index of the last honest round opening slot; `r`: the rounds of the honest round opening slots.



`hHoldF`: the attestations' holders at each honest round opening slot
stay active for their sync delay. The form read up to `t` is called at slot starts at which no
slot's update is half run.

Read aloud: after the phase, honest validators agree on the confirmed tip, it only grows, every
honest proposal joins it and strictly extends what was confirmed before it, unless a digest
collision hit an honest proposal. -/
theorem lem90_healed_confirmed
    (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd m : ℕ) (r : ℕ → ℕ)
    (hGST : GST ≤ tGAT)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {ΔNet_F : ℕ} (E_F : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    {Δs_F : ℕ} (Sy_F : SyncedWithin A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST)
    (hΔs_F : (Δs_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S ∨ (Δs_F : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind ≤ 4 * Δ S * S.C.k)
    -- for each honest round opening slot, every validator outside the adversary set at the support cutoff of the slot
    -- after its first slot is active through the attestations' sync delay after the later of that first slot's duty
    -- window's start and `GST`
    (hHoldF : ∀ i, i < m → ∀ v, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (r i * S.C.R + 1)) →
      v ∈ A.activeThroughout x ((max (M.dutyWindowStart S.C (r i * S.C.R)) GST : ℕ) : ℝ)
        (((max (M.dutyWindowStart S.C (r i * S.C.R)) GST : ℕ) : ℝ) + Δs_F))
    (hRoots : RootsNameBlocks M A x)
    (hParent : ParentHeldAtDelivery M x)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    -- at every slot of the phase, every validator honest at the slot's update is an honest active validator and an
    -- updater of the slot
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : CommitteeSleepiness M S A x (anchorCW S tGAT))
    -- every updater of a slot from the first honest round opening slot `r 0 * S.C.R` on is active for the
    -- sync delay after the real time of its own tick to the support cutoff of the next slot
    --
    (hStay : ∀ σ : ℕ, r 0 * S.C.R ≤ σ → ∀ u ∈ updaterAt M S A x σ,
      u ∈ A.activeThroughout x (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))))
        (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))) + Δs))
    (hSeq : HonestOpeningSeq M S A x r m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hOpenings : OpeningsOutsideWaitsAndWindows S r m)
    (hAdvQ : ∀ t : ℕ, A.AdversaryFewerThanTwoThirdsUntil x (validator_count V) t)
    -- at every slot whose next slot starts at or after `tAwakeEnd`, the honest active committee
    -- members are active through the sync delay after Lemma 12's read time of the slot; at every such slot with an
    -- honest opener, its proposer through the sync delay after one delay or one sync delay before its start
    --
    (hHold : ∀ s' : ℕ, tAwakeEnd ≤ M.slotStart S.C (s' + 1) →
      ∀ u ∈ honestActiveAt M S A x s', u ∈ S.P.committee s' →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hHoldP : ∀ s : ℕ, tAwakeEnd ≤ M.slotStart S.C s → HonestOpenerAt M S A x s →
      S.P.proposer s ∈ A.activeThroughout x ((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ)
        (((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs)) :
    RootCollisionAtOpening M S A x r m ∨
      (ConfirmedAgreeAfterHealing M S A x tAwakeEnd ∧
        ConfirmedMonotoneAfterHealing M S A x tAwakeEnd ∧
        ConfirmedIncludedAfterHealing M S A x tAwakeEnd ∧
        ConfirmedExtendedByHonestProposals M S A x tAwakeEnd) :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem90_healed_confirmed M F U Fx) S A x R GST
    tGAT tAwakeEnd m r hGST E hNet hSkew hRedeliver E_F hNet_F hSkew_F Sy hΔs Sy_F hΔs_F hHoldF hRoots hParent hThird hAwake hActive
    hCommittees hStay hSeq hOpenings hAdvQ hHold hHoldP

/-- **Lemma 90, the confirmed tip after healing, for the readings up to a time `t`.** Under the top
statements' premises without a premise on roots, for every time `t` from `tAwakeEnd` on: some
honest round opening slot's proposal has the root of a block its proposer held (`RootCollisionAtOpening`); or
two distinct blocks that honest validators hold at steps at times at most `t` have the same root
(`RootCollisionHeldBy M S Sched x t`); or, from `tAwakeEnd` to `t`, the confirmed tips of two
validators honest through their steps are compatible (`ConfirmedAgreeBetween`), the confirmed tip
of a validator honest through the later of two steps only extends (`ConfirmedMonotoneBetween`), and
every honest proposal of a slot starting after `tAwakeEnd` whose update is at most `t` is the
confirmed tip of every honest active validator of its slot right after its update and stays an
ancestor of, or equal to, the confirmed tips that follow up to `t` (`ConfirmedIncludedBetween`),
and every honest proposal of a slot starting after `tAwakeEnd` whose update is at most `t`, unless
its proposer held a block with its root, is a strict descendant of every confirmed tip a validator
honest through its step had from `tAwakeEnd` until the proposal's slot started
(`ConfirmedExtendedByHonestProposalsBetween`).

The hypotheses, in words: `GST` is at most `tGAT`; every time is reached; corruption is permanent;
blocks, Goldfish votes and attestations are delivered within their delays after `GST`;
a block reaches a validator only once it holds the parent; unforgeability;
fewer than a third of the validators have been in the adversary set up to `tAwakeEnd`; every
validator outside the adversary set at a time from `tGAT` to `tAwakeEnd` is awake then; committee
sleepiness from `anchorCW S tGAT` for the slots whose update is at most `t`; the honest round
opening slots of the rounds `r 0 < … < r m` lie between `tGAT + 4Δ · healFrontSlots S` and
`tAwakeEnd`; nine honest round opening slots lie outside every two spans of `δt` slots and five
spans of `k + 2` slots; fewer than two thirds of the validators have been in the adversary set up
to `t`; at every slot whose next slot starts at or after `tAwakeEnd` and whose update is at most
`t`, its honest active committee members, and the proposer when the slot has an honest opener,
stay active for `Δs` after the times the synchrony condition reads them.
No premise on roots: the conclusion names the collision.
Every updater of a slot from the first honest round opening slot `r 0 * S.C.R` on, whose
update is at most `t`, stays active for `Δs` after the real time of its own tick to the support cutoff
of the next slot.

Why: the facts after the hand-over up to `t` (`healed_handover_facts_until`); every honest record
after the support cutoff of slot `s₀ + 1` is the confirmation of a slot whose update ran by then
(`lem90a_latest_confirmed_honest_at`); the chain invariant and the lock invariant at every slot
whose update is at most `t` (`lem81_inv_before`); Lemma 90's agreement, growth and inclusion on the
chain before a slot from the time of `i₂` to `t` (`lem90_confirmed_agree_before`,
`lem90_confirmed_monotone_before`, `lem90_confirmed_included_before`); the agreement and the growth
moved from the time of `i₂` to `tAwakeEnd`, and the inclusion read from `tAwakeEnd` itself
; the fourth from the agreement and the inclusion
(`confirmedExtendedBetween_of_agree_included`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `tGAT`, `tAwakeEnd`: the start and end of the healing phase; `m`: the
  index of the last honest round opening slot; `r`: the rounds of the honest round opening slots.


`tAwakeEnd ≤ t`: the phase's proof (Lemma 89) compares blocks held up to the support cutoff of the
last opening's first slot, at most `tAwakeEnd`, whatever `t` is.

`hTicksBy`: `t` is a time at which no slot's update is half run
(`TicksToUpdatesBy`), so that the facts after the hand-over up to `t` cover every updater of every
slot the kits read; the unbounded form calls this one at slot starts (`exists_ticksBy_ge`).
`hHoldF`: the attestations' holders at each honest round opening slot
stay active for their sync delay, as the facts after the hand-over read them.

Read aloud: for every time `t` after the phase, unless a collision has hit by `t`, up to `t` honest
validators agree on the confirmed tip, it only grows, and every honest proposal joins it and
strictly extends what was confirmed before it. -/
theorem lem90_healed_confirmed_until (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd m : ℕ) (r : ℕ → ℕ)
    (hGST : GST ≤ tGAT)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {ΔNet_F : ℕ} (E_F : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    {Δs_F : ℕ} (Sy_F : SyncedWithin A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST)
    (hΔs_F : (Δs_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S ∨ (Δs_F : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind ≤ 4 * Δ S * S.C.k)
    -- for each honest round opening slot, every validator outside the adversary set at the support cutoff of the slot
    -- after its first slot is active through the attestations' sync delay after the later of that first slot's duty
    -- window's start and `GST`
    (hHoldF : ∀ i, i < m → ∀ v, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (r i * S.C.R + 1)) →
      v ∈ A.activeThroughout x ((max (M.dutyWindowStart S.C (r i * S.C.R)) GST : ℕ) : ℝ)
        (((max (M.dutyWindowStart S.C (r i * S.C.R)) GST : ℕ) : ℝ) + Δs_F))
    (hParent : ParentHeldAtDelivery M x)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    -- at every slot of the phase, every validator honest at the slot's update is an honest active validator and an
    -- updater of the slot
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    -- the time up to which the execution is read, after the phase
    (t : ℕ) (ht : tAwakeEnd ≤ t)
    -- `t` is not inside any slot's update: at every slot whose update is at most `t`, or to whose update some
    -- validator ticked at a real time at most `t`, every tick to a clock value at most that update is at a real
    -- time at most `t`
    (hTicksBy : TicksToUpdatesBy M S x t)
    -- committee sleepiness from `anchorCW S tGAT`, for the slots whose update is at most `t`
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) t)
    -- every tick at a real time at most `t`, to a clock value `c`: committee sleepiness from `anchorCW S tGAT` read up
    -- to `c`
    (hCommitteesTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → (x.time k : ℝ) ≤ t →
      CommitteeSleepinessUntil M S A x (anchorCW S tGAT) c)
    -- every updater of a slot from the first honest round opening slot `r 0 * S.C.R` on, whose update is at
    -- most `t`, is active for the sync delay after the real time of its own tick to the support cutoff of the
    -- next slot
    (hStay : ∀ σ : ℕ, r 0 * S.C.R ≤ σ → M.supportCutoff S.C (σ + 1) ≤ t → ∀ u ∈ updaterAt M S A x σ,
      u ∈ A.activeThroughout x (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))))
        (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))) + Δs))
    (hSeq : HonestOpeningSeq M S A x r m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hOpenings : OpeningsOutsideWaitsAndWindows S r m)
    -- fewer than two thirds of the validators corrupted up to `t`
    (hAdvQ : A.AdversaryFewerThanTwoThirdsUntil x (validator_count V) t)
    -- at every slot whose next slot starts at or after `tAwakeEnd` and whose update is at most `t`, the honest active committee
    -- members are active through the sync delay after Lemma 12's read time of the slot; at every such slot with an
    -- honest opener, its proposer through the sync delay after one delay or one sync delay before its start
    --
    (hHold : ∀ s' : ℕ, tAwakeEnd ≤ M.slotStart S.C (s' + 1) → M.supportCutoff S.C (s' + 1) ≤ t →
      ∀ u ∈ honestActiveAt M S A x s', u ∈ S.P.committee s' →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hHoldP : ∀ s : ℕ, tAwakeEnd ≤ M.slotStart S.C s → M.supportCutoff S.C (s + 1) ≤ t → HonestOpenerAt M S A x s →
      S.P.proposer s ∈ A.activeThroughout x ((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ)
        (((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs)) :
    RootCollisionAtOpening M S A x r m ∨ RootCollisionHeldBy M S A x t ∨
      (ConfirmedAgreeBetween M S A x tAwakeEnd t ∧
        ConfirmedMonotoneBetween M S A x tAwakeEnd t ∧
        ConfirmedIncludedBetween M S A x tAwakeEnd t ∧
        ConfirmedExtendedByHonestProposalsBetween M S A x tAwakeEnd t) :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem90_healed_confirmed_until M F U Fx) S A x R
    GST tGAT tAwakeEnd m r hGST E hNet hSkew hRedeliver E_F hNet_F hSkew_F Sy hΔs Sy_F hΔs_F hHoldF hParent hThird hAwake hActive t ht hTicksBy
    hCommittees hCommitteesTick hStay hSeq hOpenings hAdvQ hHold hHoldP

end GoldilocksCorrectness.Record.Statements.Executions

