module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma94
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma95
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma96
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma107
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma94Pair
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma95Pair
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma97
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# FinalityLivenessStatements, over a model

The statements of `GoldilocksCorrectness/Statements/Executions/FinalityLivenessStatements.lean`,
over a model `M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: the round steps of
finality liveness after healing, namely the round's attesters' targets, the height step of two
consecutive honest round opening slots, Lemmas 96, 107, 94 and 95, three facts the composition
reads, and Lemma 97; each round step is the theorem of the same name of its proof page's twin
(`Record/Restated/Proofs/Executions/Lemma94.lean`, `Lemma95.lean`, `Lemma96.lean`, `Lemma107.lean`,
`Lemma94Pair.lean`, `Lemma95Pair.lean`, `Lemma97.lean`).
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

open GoldilocksCorrectness.Statements.Routines (Δ Δ_F slotStart voteTime supportCutoff)

namespace GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Statements.Executions (OpeningsOutsideSpans
  OpeningsOutsideWaitsAndWindows)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor hMax le_hMax IsEntry VoterTreeAt JustifiedInTree AnchorAt)
open GoldilocksCorrectness.Record.Statements.Routines (RecordConsistent)
open GoldilocksCorrectness.Statements.Executions (Vocab.goldilocks acObject)
open GoldilocksCorrectness.Statements.Executions (Vocab.goldilocks acObject fgObject)
open GoldilocksCorrectness.Record.Statements.Routines (FinalityCertOn JustificationCertOn)
open GoldilocksCorrectness.Record.Statements.Routines (AttestationFrom)
open GoldilocksCorrectness.Record.Statements.Routines (ProgressCertOn)
open GoldilocksCorrectness.Statements.Executions (Vocab.goldilocks acObject)
open GoldilocksCorrectness.Statements.AbstractTrace.View (AwakeForDelayWithin)

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

/-- **The round's attesters after healing: their targets (the part of Lemma 94 that holds).** In
an execution where every time is reached, corruption is permanent, blocks and Goldfish votes are
delivered within `Δ` after `GST` (synchrony from the receiver's wake, and catch-up on wake), a root
names one block among what honest validators hold by the support cutoff of slot `s + 1`, a block
reaches a validator only once it holds the parent, and nobody votes in an honest validator's name;
under unforgeability, with fewer than a quorum of validators ever in the adversary set and committee
sleepiness from `anchor`, at or before `x[i₂].time`; with `GST` at most the vote time of slot `s₀`
and the support cutoff of slot `s₀ + 1` at or before `x[i₂].time`; with the updaters'
confirmations of the slots from `s₀` to `s` forming one chain, the chain invariant and the lock
invariant at every slot after `s₀` and at most `s`, the lock invariant at the healed slot `s₀`
itself, every honest attestation sent before the support cutoff of slot `s₀ + 1` of height at most
`H`, and the caches of every validator honest at a step at a time from `x[i₂].time` to the support
cutoff of slot `s + 1` on the honest chain with justification height greater than `H`: for the
round `r` whose first slot `s = r * R` starts after `x[i₂].time` and is an honest round opening slot
(`HonestOpenerAt M S Sched s`), whose proposer's tick at the start of slot `s` put `B` on the wire,
with no block the proposer held before the start of slot `s` having `B`'s root, every member `u` of
`honestActiveAt M S Sched s` put on the wire, at a tick at a time at most the support cutoff of slot
`s + 1`, a target of its own at the height of `B`'s chain state naming the root of `B`'s `T_h`.

Why: `u` updates slot `s + 1` saving `B` fast, with its fork-choice root on `B`'s chain, its
`head_height_floor` at most `B`'s height (Lemma 91 (d) and the certificate route), `B` in its tree
and its record at `B`'s height clean of a lock on another block (Lemma 83's justification form);
Lemma 61 then gives the attestation at the action time, or one already sent at that height naming
the same root; either is a target (`no_honest_timeout_after_healing` on the chain before slot
`s + 1`).

Read aloud: every honest active validator of an honest round opening slot after healing attests
for the proposal's height by the round's action time, with a target.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₂`: the hand-over step; `H`: the threshold;
- `r`: the round; `s`: its first slot; `B`: the proposal; `u`: the member.

 the probe's statement without its clause on
the finality pair (finding F1). The probe's `hTicks` is gone; `hChain` is read before
slot `s + 1`, `ht₀` is the non-strict form the inclusion takes. -/
theorem round_attesters_target_after_healing (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ anchor i₂ H r s : ℕ) (B : Block V) (u : V)
    -- every time is reached
    -- blocks and Goldfish votes are delivered within `Δ` after `GST`
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- roots name blocks up to the real time of each updater's tick to the support cutoff of the next slot (T-RC86-1,)
    (hRootsU : ∀ v ∈ updaterAt M S A x s, RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C (s + 1)))))
    -- a block reaches a validator only once it holds the parent
    (hParent : ParentHeldAtDelivery M x)
    -- fewer than a quorum in the adversary set up to that real time (T-RC86-1,)
    (hAdvQU : ∀ v ∈ updaterAt M S A x s, A.AdversaryFewerThanQuorumUntil x (quorum V) (x.time (x.tickStep v (M.supportCutoff S.C (s + 1)))))
    -- committee sleepiness from `anchor` for the slots whose update is at most `M.supportCutoff S.C (s + 1)`, at or before the hand-over step's time
    (hSleepK : CommitteeSleepinessUntil M S A x anchor (M.supportCutoff S.C (s + 1))) (hAnchor : anchor ≤ x.time i₂)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀) (ht₀ : M.supportCutoff S.C (s₀ + 1) ≤ x.time i₂)
    -- the updaters' confirmations of the slots from `s₀` to `s` form one chain
    (hChain : ConfirmationsChainBefore M S A x s₀ (s + 1))
    -- the chain invariant and the lock invariant at the slots after `s₀` and at most `s`
    (hInv : ∀ s' : ℕ, s₀ < s' → s' ≤ s →
      ChainInvFor M S A x (honestActiveAt M S A x s')
        (OnHonestChainBefore M S A x s₀ s') s')
    (hLocks : ∀ s' : ℕ, s₀ < s' → s' ≤ s → ∀ w ∈ honestActiveAt M S A x s',
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ s') s' w)
    -- the lock invariant at the healed slot itself
    (hLocks₀ : ∀ w ∈ honestActiveAt M S A x s₀,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ (s₀ + 1)) s₀ w)
    -- every honest attestation sent before the support cutoff of `s₀ + 1` has height at most `H`
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    -- the caches of every honest validator from the hand-over step to that real time (T-RC86-1,)
    (hCachesU : ∀ v ∈ updaterAt M S A x s, ∀ (j : ℕ) (w : V), x.time i₂ ≤ x.time j →
      x.time j ≤ x.time (x.tickStep v (M.supportCutoff S.C (s + 1))) → w ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st j w))
    -- `s` is the first slot of round `r`, starting after the hand-over step's time
    (hs : s = r * S.C.R) (hAfter : x.time i₂ < M.slotStart S.C s ∧
      ∀ k : ℕ, x.lbl k = Event.tick (S.P.proposer s) (M.slotStart S.C s) → x.time i₂ < x.time k)
    -- `s` is an honest round opening slot
    (hOpener : HonestOpenerAt M S A x s)
    -- the proposer's tick at the start of `s` put `B` on the wire
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick (S.P.proposer s) (M.slotStart S.C s) ∧
      (⟨S.P.proposer s, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i)
    -- no block the proposer held before the start of `s` has `B`'s root
    (hNoCollision : ¬ RootCollisionAtProposal M S A x s B)
    -- the honest committee voters of the slot and of the slot before it, and the proposer, stay active for the sync delay
    -- after the time the synchronous delivery reads them (T-RC86-2,)
    (hHold : ∀ s' : ℕ, s - 1 ≤ s' → s' ≤ s → ∀ u ∈ honestActiveAt M S A x s', u ∈ S.P.committee s' →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hHoldP : S.P.proposer s ∈ A.activeThroughout x ((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- `u` is an honest active validator of `s`
    (hu : u ∈ honestActiveAt M S A x s) :
    ∃ (i t : ℕ) (a : Attestation V), x.lbl i = Event.tick u t ∧
      t ≤ M.supportCutoff S.C (s + 1) ∧
      (⟨u, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i ∧
      a.val_index = u ∧ a.h = (M.chainStateOf S.C B).h ∧ a.T = (M.chainStateOf S.C B).T_h.root ∧
      a.τ = false :=
  (GoldilocksCorrectness.Record.Proofs.Executions.round_attesters_target_after_healing M F U Fx) S
    A x R GST s₀ anchor i₂ H r s B u E hNet hSkew hRedeliver Sy hΔs hRootsU hParent hAdvQU
    hSleepK hAnchor hGST ht₀ hChain hInv hLocks hLocks₀ hOld hCachesU hs hAfter hOpener hPropose
    hNoCollision hHold hHoldP hu

/-- **Two consecutive honest round opening slots after healing: the height step (Lemma 95, its
first two conjuncts).** In an execution where every time is reached, corruption is permanent,
blocks and Goldfish votes are delivered within `Δ` after `GST` and attestations within `Δ_F`
(synchrony from the receiver's wake, and catch-up on wake), a root names one block among what
honest validators hold by the vote time of slot `(r + 1) * R`, a block reaches a validator only once
it holds the parent, and nobody votes in an honest validator's name; under unforgeability, with
fewer than a quorum of validators ever in the adversary set and committee sleepiness from `anchor`,
at or before `x[i₂].time`; with `GST` at most the vote time of slot `s₀` and the support cutoff of
slot `s₀ + 1` at or before `x[i₂].time`; with the updaters' confirmations of the slots from `s₀` to
before `(r + 1) * R − 1` forming one chain, the chain invariant and the lock invariant at every slot
after `s₀` and at most `(r + 1) * R − 1`, the lock invariant at the healed slot `s₀` itself, every
honest attestation sent before the support cutoff of slot `s₀ + 1` of height at most `H`, and the
caches of every validator honest at a step at a time from `x[i₂].time` to the vote time of slot
`(r + 1) * R` on the honest chain with justification height greater than `H`; with
`Δ_F + Δ ≤ 4Δ(k + 1)`; with roots naming blocks and the honest caches on the honest
chain also up to the real time of every tick to a clock value at most the vote time of slot
`(r + 1) * R`, and the honest committee voters of the slot before each opener's slot and of the first
opener's slot, and each opener, active for the sync delay after the time the synchronous delivery
reads them: for the rounds `r` and `r + 1` whose first slots are honest round opening
slots, the first starting after `x[i₂].time`, and so does every tick of its proposer to that start, and with a quorum of honest active validators
(`QuorumActiveAt`), whose proposers' ticks at their starts put `B` and `B'` on the wire, with no
block either proposer held before its slot's start having its proposal's root: `B` is `B'` or an
ancestor of `B'`, and `B'`'s chain-state height is at least `B`'s plus one.

Why: `B'`'s parent extends the chain before slot `(r + 1) * R − 1`, which holds `B`; when the
parent is at `B`'s height, the quorum's targets at that height naming `T_h(B)`'s root reach the
proposer of `(r + 1) * R` by its slot's start (each delivered by `hDel`, whose premise on the member's
justified height Lemma 107 at round `r` gives), and Lemma 53 puts `B'` at the next height.

The delivery line `hDel`: every attestation an honest active member of round `r`
put on the wire at a tick up to the round's action time, with the member's justified height at the
proposal window's start of slot `(r + 1) * R` at most its height, is delivered to the proposer of
`(r + 1) * R` before that proposer's tick to its slot's start. It replaces the line that every member is active
at that proposal window's start.

Read aloud: the next honest round opening slot extends the previous one's proposal and raises the
height.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₂`: the hand-over step; `H`: the threshold;
- `r`: the first round; `B`, `B'`: the two proposals.

 the probe's statement without its third
conjunct (finding F1). The probe's `hTicks` is gone; `hChain`, `hInv` and `hLocks` are
read before slot `(r + 1) * R − 1`, `ht₀` is the non-strict form the inclusion takes. -/
theorem consecutive_openings_height_step (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ anchor i₂ H r : ℕ) (B B' : Block V)
    -- every time is reached
    -- blocks and Goldfish votes are delivered within `Δ` after `GST`
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    -- attestations are delivered within `Δ_F` after `GST`
    {ΔNet_F : ℕ} (E_F : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    {Δs_F : ℕ} (Sy_F : SyncedWithin A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST)
    (hΔs_F : (Δs_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S ∨ (Δs_F : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind ≤ 4 * Δ S * S.C.k)
    -- a root names one block among what honest validators hold by the vote time of `(r + 1) R`
    (hRoots : RootsNameBlocksUntil M A x (M.voteTime S.C ((r + 1) * S.C.R)))
    -- roots name blocks up to the real time of every tick to a clock value at most the vote time of slot
    -- `(r + 1) * S.C.R` (, the callees' per-tick rows, T-RC86-1)
    (hRootsK : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.voteTime S.C ((r + 1) * S.C.R) →
      RootsNameBlocksUntil M A x (x.time k))
    -- a block reaches a validator only once it holds the parent
    (hParent : ParentHeldAtDelivery M x)
    -- fewer than a quorum of validators have been in the adversary set up to the support cutoff of slot `(r + 1) * S.C.R + 1`
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (M.supportCutoff S.C ((r + 1) * S.C.R + 1)))
    -- committee sleepiness from `anchor` for the slots whose update is at most `M.supportCutoff S.C ((r + 1) * S.C.R)`, at or before the hand-over step's time
    (hSleepK : CommitteeSleepinessUntil M S A x anchor (M.supportCutoff S.C ((r + 1) * S.C.R))) (hAnchor : anchor ≤ x.time i₂)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀) (ht₀ : M.supportCutoff S.C (s₀ + 1) ≤ x.time i₂)
    -- the updaters' confirmations of the slots from `s₀` to before `(r + 1) R − 1` form one chain
    (hChain : ConfirmationsChainBefore M S A x s₀ ((r + 1) * S.C.R - 1))
    -- the chain invariant and the lock invariant at the slots after `s₀`, at most `(r + 1) R − 1`
    (hInv : ∀ s' : ℕ, s₀ < s' → s' ≤ (r + 1) * S.C.R - 1 →
      ChainInvFor M S A x (honestActiveAt M S A x s')
        (OnHonestChainBefore M S A x s₀ s') s')
    (hLocks : ∀ s' : ℕ, s₀ < s' → s' ≤ (r + 1) * S.C.R - 1 → ∀ w ∈ honestActiveAt M S A x s',
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ s') s' w)
    -- the lock invariant at the healed slot itself
    (hLocks₀ : ∀ w ∈ honestActiveAt M S A x s₀,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ (s₀ + 1)) s₀ w)
    -- every honest attestation sent before the support cutoff of `s₀ + 1` has height at most `H`
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    -- the caches of the honest validators from the hand-over to the vote time of `(r + 1) R`
    (hCaches : ∀ (j : ℕ) (w : V), x.time i₂ ≤ x.time j →
      x.time j ≤ M.voteTime S.C ((r + 1) * S.C.R) →
      w ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st j w))
    -- the caches of every honest validator from the hand-over step up to the real time of every such tick
    -- (, T-RC86-1)
    (hCachesK : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.voteTime S.C ((r + 1) * S.C.R) →
      ∀ (j : ℕ) (w : V), x.time i₂ ≤ x.time j → x.time j ≤ x.time k → w ∉ A.corrupted j →
        CachesOnChain M S A x s₀ H (x.st j w))
    -- the attestations of a round reach a proposer that woke at its proposal window's start
    (hParam : Δ_F S + Δ S ≤ 4 * Δ S * (S.C.k + 1))
    -- the first slot of round `r` starts after the hand-over step's time, and so does every tick of its proposer
    -- to that start (, the clause made strict)
    (hAfter : x.time i₂ < M.slotStart S.C (r * S.C.R) ∧
      ∀ k : ℕ, x.lbl k = Event.tick (S.P.proposer (r * S.C.R)) (M.slotStart S.C (r * S.C.R)) → x.time i₂ < x.time k)
    -- the two first slots are honest round opening slots
    (hOpener : HonestOpenerAt M S A x (r * S.C.R))
    (hOpener' : HonestOpenerAt M S A x ((r + 1) * S.C.R))
    -- a quorum of honest active validators at the first
    (hQuorum : QuorumActiveAt M S A x (r * S.C.R))
    -- every attestation a member of round `r`'s honest active validators put on the wire at a tick up to the round's
    -- action time, with the member's justified height at the next opener's proposal-window start at most its
    -- height, is delivered to the next opener before its tick to its slot's start
    (hDel : ∀ u ∈ honestActiveAt M S A x (r * S.C.R), ∀ (j t' : ℕ) (a : Attestation V),
      x.lbl j = Event.tick u t' → t' ≤ M.supportCutoff S.C (r * S.C.R + 1) →
      (⟨u, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (j + 1) - x.sent j →
      M.justifiedHeight (x.stateBefore (M.proposalWindowStart S.C ((r + 1) * S.C.R)) u) ≤ a.h →
      ∃ d : ℕ, x.lbl d = Event.deliver (S.P.proposer ((r + 1) * S.C.R)) ⟨u, NamedObject.attest a⟩ ∧
        d < x.tickStep (S.P.proposer ((r + 1) * S.C.R)) (M.slotStart S.C ((r + 1) * S.C.R)))
    -- the two proposers' ticks put `B` and `B'` on the wire
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick (S.P.proposer (r * S.C.R)) (M.slotStart S.C (r * S.C.R)) ∧
      (⟨S.P.proposer (r * S.C.R), NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i)
    (hPropose' : ∃ i : ℕ, x.lbl i = Event.tick (S.P.proposer ((r + 1) * S.C.R)) (M.slotStart S.C ((r + 1) * S.C.R)) ∧
      (⟨S.P.proposer ((r + 1) * S.C.R), NamedObject.block B'⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i)
    -- no block either proposer held before its slot's start has its proposal's root
    (hNoCol : ¬ RootCollisionAtProposal M S A x (r * S.C.R) B)
    (hNoCol' : ¬ RootCollisionAtProposal M S A x ((r + 1) * S.C.R) B')
    -- the honest committee voters of the slot before each honest round opening slot and of the first one, and each
    -- opener, stay active for the sync delay after the time the synchronous delivery reads them
    -- T-RC86-2,)
    (hHold : ∀ σ : ℕ, r * S.C.R - 1 ≤ σ → σ ≤ r * S.C.R → ∀ u ∈ honestActiveAt M S A x σ, u ∈ S.P.committee σ →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C σ - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C σ - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hHold' : ∀ u ∈ honestActiveAt M S A x ((r + 1) * S.C.R - 1), u ∈ S.P.committee ((r + 1) * S.C.R - 1) →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C ((r + 1) * S.C.R - 1) - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C ((r + 1) * S.C.R - 1) - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hHoldP : S.P.proposer (r * S.C.R) ∈ A.activeThroughout x ((M.slotStart S.C (r * S.C.R) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C (r * S.C.R) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hHoldP' : S.P.proposer ((r + 1) * S.C.R) ∈ A.activeThroughout x ((M.slotStart S.C ((r + 1) * S.C.R) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C ((r + 1) * S.C.R) - max (Δ S) Δs : ℕ) : ℝ) + Δs)) :
    B.AncestorEq B' ∧ (M.chainStateOf S.C B).h + 1 ≤ (M.chainStateOf S.C B').h :=
  (GoldilocksCorrectness.Record.Proofs.Executions.consecutive_openings_height_step M F U Fx) S A x R GST s₀
    anchor i₂ H r B B' E hNet hSkew hRedeliver E_F hNet_F hSkew_F Sy hΔs Sy_F hΔs_F hRoots hRootsK hParent hAdvQ hSleepK hAnchor hGST ht₀ hChain hInv
    hLocks hLocks₀ hOld hCaches hCachesK hParam hAfter hOpener hOpener' hQuorum
    (fun u hu j t' a h₁ h₂ h₃ h₄ => Or.inl (hDel u hu j t' a h₁ h₂ h₃ h₄)) hPropose hPropose' hNoCol hNoCol' hHold hHold' hHoldP hHoldP'

/-- **Lemma 96, three consecutive honest round opening slots justify the middle proposal's
height.** In an execution where every time is reached, corruption is permanent, blocks and
Goldfish votes are delivered within `Δ` after `GST` and attestations within `Δ_F` (synchrony from
the receiver's wake, and catch-up on wake), a root names one block among what honest validators
hold by the vote time of slot `(r + 1) * R`, a block reaches a validator only once it holds the
parent, and nobody votes in an honest validator's name; under unforgeability, with fewer than a
quorum of validators ever in the adversary set and committee sleepiness from `anchor`, at or before
`x[i₂].time`; with `GST` at most the vote time of slot `s₀` and the support cutoff of slot `s₀ + 1`
at or before `x[i₂].time`; with the updaters' confirmations of the slots from `s₀` to before
`(r + 1) * R − 1` forming one chain, the chain invariant and the lock invariant at every slot after
`s₀` and at most `(r + 1) * R − 1`, the lock invariant at the healed slot `s₀` itself, every honest
attestation sent before the support cutoff of slot `s₀ + 1` of height at most `H`, and the caches
of every validator honest at a step at a time from `x[i₂].time` to the vote time of slot
`(r + 1) * R` on the honest chain with justification height greater than `H`; with
`Δ_F + Δ ≤ 4Δ(k + 1)` and `2R ≤ δt + 1`; with roots naming blocks and the honest
caches on the honest chain also up to the real time of every tick to a clock value at most the vote
time of slot `(r + 1) * R`, and the honest committee voters of the slot before each opener's slot and
of the first two openers' slots, and each opener, active for the sync delay after the time the
synchronous delivery reads them: for the rounds `r − 1`, `r`, `r + 1`, with `r ≥ 1`,
whose first slots are honest round opening slots, the first starting after `x[i₂].time`, and so does
every tick of its proposer to that start, the first two with a quorum of honest active validators (`QuorumActiveAt`), whose proposers' ticks
at their starts put `Bprev`, `B` and `B'` on the wire, with no block any of the three proposers held
before its slot's start having its proposal's root: the justification height of `B'`'s chain state
is at least the height of `B`'s.

Why: the height step at `r − 1`, `r` puts `B`'s entry `T_h(B)` strictly after `Bprev`, at a slot
after `(r − 1) R`. The block `Y` that takes `B'`'s chain past `h(B)` either justified `h(B)`, and
the justification height only rises along a chain, or passed the timeout test,
`T_h(B).slot + δt ≤ Y.slot ≤ (r + 1) R`; with `2R ≤ δt + 1` that leaves `Y = B'` with its parent at
`h(B)`, and then the quorum's targets make `B'` justify `T_h(B)` (Lemma 53), at the height `h(B)`.

The delivery lines `hDelPrev` and `hDel`: every attestation an honest active member
of round `r − 1` (of round `r`) put on the wire at a tick up to that round's action time, with the
member's justified height at the next round's proposal window's start at most its height, is
delivered to the next round's opener before that opener's tick to its slot's start. They replace the lines
that every member is active at that proposal window's start.

Read aloud: with the timeout longer than two rounds less one slot, the next honest round opening
slot justifies the height the previous one's proposal reached.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₂`: the hand-over step; `H`: the threshold;
- `r`: the middle round; `Bprev`, `B`, `B'`: the proposals of the rounds `r − 1`, `r`, `r + 1`.

 The probe's `hTicks` is gone; `hChain`,
`hInv` and `hLocks` are read before slot `(r + 1) * R − 1`, `ht₀` is the non-strict form the
inclusion takes. -/
theorem lem96_consecutive_openings_justified (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ anchor i₂ H r : ℕ) (Bprev B B' : Block V)
    -- every time is reached
    -- blocks and Goldfish votes are delivered within `Δ` after `GST`
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    -- attestations are delivered within `Δ_F` after `GST`
    {ΔNet_F : ℕ} (E_F : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    {Δs_F : ℕ} (Sy_F : SyncedWithin A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST)
    (hΔs_F : (Δs_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S ∨ (Δs_F : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind ≤ 4 * Δ S * S.C.k)
    -- a root names one block among what honest validators hold by the vote time of `(r + 1) R`
    (hRoots : RootsNameBlocksUntil M A x (M.voteTime S.C ((r + 1) * S.C.R)))
    -- roots name blocks up to the real time of every tick to a clock value at most the vote time of slot
    -- `(r + 1) * S.C.R` (, the callees' per-tick rows, T-RC86-1)
    (hRootsK : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.voteTime S.C ((r + 1) * S.C.R) →
      RootsNameBlocksUntil M A x (x.time k))
    -- a block reaches a validator only once it holds the parent
    (hParent : ParentHeldAtDelivery M x)
    -- fewer than a quorum of validators have been in the adversary set up to the support cutoff of slot `(r + 1) * S.C.R + 1`
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (M.supportCutoff S.C ((r + 1) * S.C.R + 1)))
    -- committee sleepiness from `anchor` for the slots whose update is at most `M.supportCutoff S.C ((r + 1) * S.C.R)`, at or before the hand-over step's time
    (hSleepK : CommitteeSleepinessUntil M S A x anchor (M.supportCutoff S.C ((r + 1) * S.C.R))) (hAnchor : anchor ≤ x.time i₂)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀) (ht₀ : M.supportCutoff S.C (s₀ + 1) ≤ x.time i₂)
    -- the updaters' confirmations of the slots from `s₀` to before `(r + 1) R − 1` form one chain
    (hChain : ConfirmationsChainBefore M S A x s₀ ((r + 1) * S.C.R - 1))
    -- the chain invariant and the lock invariant at the slots after `s₀`, at most `(r + 1) R − 1`
    (hInv : ∀ s' : ℕ, s₀ < s' → s' ≤ (r + 1) * S.C.R - 1 →
      ChainInvFor M S A x (honestActiveAt M S A x s')
        (OnHonestChainBefore M S A x s₀ s') s')
    (hLocks : ∀ s' : ℕ, s₀ < s' → s' ≤ (r + 1) * S.C.R - 1 → ∀ w ∈ honestActiveAt M S A x s',
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ s') s' w)
    -- the lock invariant at the healed slot itself
    (hLocks₀ : ∀ w ∈ honestActiveAt M S A x s₀,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ (s₀ + 1)) s₀ w)
    -- every honest attestation sent before the support cutoff of `s₀ + 1` has height at most `H`
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    -- the caches of the honest validators from the hand-over to the vote time of `(r + 1) R`
    (hCaches : ∀ (j : ℕ) (w : V), x.time i₂ ≤ x.time j →
      x.time j ≤ M.voteTime S.C ((r + 1) * S.C.R) →
      w ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st j w))
    -- the caches of every honest validator from the hand-over step up to the real time of every such tick
    -- (, T-RC86-1)
    (hCachesK : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.voteTime S.C ((r + 1) * S.C.R) →
      ∀ (j : ℕ) (w : V), x.time i₂ ≤ x.time j → x.time j ≤ x.time k → w ∉ A.corrupted j →
        CachesOnChain M S A x s₀ H (x.st j w))
    -- the attestations of a round reach a proposer that woke at its proposal window's start
    (hParam : Δ_F S + Δ S ≤ 4 * Δ S * (S.C.k + 1))
    -- the timeout is at least two rounds less one slot
    (hδt : 2 * S.C.R ≤ S.C.δt + 1)
    -- the middle round is not the first; the first slot of round `r − 1` starts after the hand-over step's time,
    -- and so does every tick of its proposer to that start (, the clause made strict)
    (hr : 1 ≤ r) (hAfter : x.time i₂ < M.slotStart S.C ((r - 1) * S.C.R) ∧
      ∀ k : ℕ, x.lbl k = Event.tick (S.P.proposer ((r - 1) * S.C.R)) (M.slotStart S.C ((r - 1) * S.C.R)) → x.time i₂ < x.time k)
    -- the three first slots are honest round opening slots
    (hOpenerPrev : HonestOpenerAt M S A x ((r - 1) * S.C.R))
    (hOpener : HonestOpenerAt M S A x (r * S.C.R))
    (hOpener' : HonestOpenerAt M S A x ((r + 1) * S.C.R))
    -- a quorum of honest active validators at the first two
    (hQuorumPrev : QuorumActiveAt M S A x ((r - 1) * S.C.R))
    -- every attestation a member of round `r − 1`'s honest active validators put on the wire at a tick up to that
    -- round's action time, with the member's justified height at round `r`'s proposal-window start at most its
    -- height, is delivered to round `r`'s opener before its tick to its slot's start
    (hDelPrev : ∀ u ∈ honestActiveAt M S A x ((r - 1) * S.C.R), ∀ (j t' : ℕ) (a : Attestation V),
      x.lbl j = Event.tick u t' → t' ≤ M.supportCutoff S.C ((r - 1) * S.C.R + 1) →
      (⟨u, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (j + 1) - x.sent j →
      M.justifiedHeight (x.stateBefore (M.proposalWindowStart S.C (r * S.C.R)) u) ≤ a.h →
      ∃ d : ℕ, x.lbl d = Event.deliver (S.P.proposer (r * S.C.R)) ⟨u, NamedObject.attest a⟩ ∧
        d < x.tickStep (S.P.proposer (r * S.C.R)) (M.slotStart S.C (r * S.C.R)))
    (hQuorum : QuorumActiveAt M S A x (r * S.C.R))
    -- every attestation a member of round `r`'s honest active validators put on the wire at a tick up to the round's
    -- action time, with the member's justified height at the next opener's proposal-window start at most its
    -- height, is delivered to the next opener before its tick to its slot's start
    (hDel : ∀ u ∈ honestActiveAt M S A x (r * S.C.R), ∀ (j t' : ℕ) (a : Attestation V),
      x.lbl j = Event.tick u t' → t' ≤ M.supportCutoff S.C (r * S.C.R + 1) →
      (⟨u, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (j + 1) - x.sent j →
      M.justifiedHeight (x.stateBefore (M.proposalWindowStart S.C ((r + 1) * S.C.R)) u) ≤ a.h →
      ∃ d : ℕ, x.lbl d = Event.deliver (S.P.proposer ((r + 1) * S.C.R)) ⟨u, NamedObject.attest a⟩ ∧
        d < x.tickStep (S.P.proposer ((r + 1) * S.C.R)) (M.slotStart S.C ((r + 1) * S.C.R)))
    -- the three proposers' ticks put `Bprev`, `B` and `B'` on the wire
    (hProposePrev : ∃ i : ℕ, x.lbl i = Event.tick (S.P.proposer ((r - 1) * S.C.R)) (M.slotStart S.C ((r - 1) * S.C.R)) ∧
      (⟨S.P.proposer ((r - 1) * S.C.R), NamedObject.block Bprev⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i)
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick (S.P.proposer (r * S.C.R)) (M.slotStart S.C (r * S.C.R)) ∧
      (⟨S.P.proposer (r * S.C.R), NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i)
    (hPropose' : ∃ i : ℕ, x.lbl i = Event.tick (S.P.proposer ((r + 1) * S.C.R)) (M.slotStart S.C ((r + 1) * S.C.R)) ∧
      (⟨S.P.proposer ((r + 1) * S.C.R), NamedObject.block B'⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i)
    -- no block any of the three proposers held before its slot's start has its proposal's root
    (hNoColPrev : ¬ RootCollisionAtProposal M S A x ((r - 1) * S.C.R) Bprev)
    (hNoCol : ¬ RootCollisionAtProposal M S A x (r * S.C.R) B)
    (hNoCol' : ¬ RootCollisionAtProposal M S A x ((r + 1) * S.C.R) B')
    -- the honest committee voters of the slot before each honest round opening slot and of the first one, and each
    -- opener, stay active for the sync delay after the time the synchronous delivery reads them
    -- T-RC86-2,)
    (hHoldPrev : ∀ σ : ℕ, (r - 1) * S.C.R - 1 ≤ σ → σ ≤ (r - 1) * S.C.R → ∀ u ∈ honestActiveAt M S A x σ, u ∈ S.P.committee σ →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C σ - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C σ - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hHold : ∀ σ : ℕ, r * S.C.R - 1 ≤ σ → σ ≤ r * S.C.R → ∀ u ∈ honestActiveAt M S A x σ, u ∈ S.P.committee σ →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C σ - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C σ - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hHold' : ∀ u ∈ honestActiveAt M S A x ((r + 1) * S.C.R - 1), u ∈ S.P.committee ((r + 1) * S.C.R - 1) →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C ((r + 1) * S.C.R - 1) - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C ((r + 1) * S.C.R - 1) - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hHoldPPrev : S.P.proposer ((r - 1) * S.C.R) ∈ A.activeThroughout x ((M.slotStart S.C ((r - 1) * S.C.R) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C ((r - 1) * S.C.R) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hHoldP : S.P.proposer (r * S.C.R) ∈ A.activeThroughout x ((M.slotStart S.C (r * S.C.R) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C (r * S.C.R) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hHoldP' : S.P.proposer ((r + 1) * S.C.R) ∈ A.activeThroughout x ((M.slotStart S.C ((r + 1) * S.C.R) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C ((r + 1) * S.C.R) - max (Δ S) Δs : ℕ) : ℝ) + Δs)) :
    (M.chainStateOf S.C B).h ≤ (M.chainStateOf S.C B').h_j :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem96_consecutive_openings_justified M F U Fx) S A x R GST
    s₀ anchor i₂ H r Bprev B B' E hNet hSkew hRedeliver E_F hNet_F hSkew_F Sy hΔs Sy_F hΔs_F hRoots hRootsK hParent hAdvQ hSleepK hAnchor hGST ht₀
    hChain hInv hLocks hLocks₀ hOld hCaches hCachesK hParam hδt hr hAfter hOpenerPrev hOpener hOpener' hQuorumPrev
    (fun u hu j t' a h₁ h₂ h₃ h₄ => Or.inl (hDelPrev u hu j t' a h₁ h₂ h₃ h₄)) hQuorum
    (fun u hu j t' a h₁ h₂ h₃ h₄ => Or.inl (hDel u hu j t' a h₁ h₂ h₃ h₄)) hProposePrev hPropose hPropose' hNoColPrev hNoCol hNoCol' hHoldPrev hHold hHold' hHoldPPrev hHoldP hHoldP'

/-- **Lemma 107, the honest attestations up to the next round's action time are at most the
opening proposal's height.** In an execution where every time is reached, corruption is permanent,
blocks and Goldfish votes are delivered within `Δ` after `GST` (synchrony from the receiver's wake,
and catch-up on wake), a root names one block among what honest validators hold by the support
cutoff of slot `s + 1`, a block reaches a validator only once it holds the parent, and nobody votes
in an honest validator's name; under unforgeability, with fewer than a quorum of validators ever in
the adversary set and committee sleepiness from `anchor`, at or before `x[i₂].time`; with `GST` at
most the vote time of slot `s₀` and the support cutoff of slot `s₀ + 1` at or before
`x[i₂].time`; with the updaters' confirmations of the slots from `s₀` to before `s` forming one
chain, the chain invariant and the lock invariant at every slot after `s₀` and at most `s`, the
lock invariant at the healed slot `s₀` itself, every honest attestation sent before the support
cutoff of slot `s₀ + 1` of height at most `H`, and the caches of every validator honest at a step
at a time from `x[i₂].time` to the support cutoff of slot `s + 1` on the honest chain with
justification height greater than `H`: for the round `r` whose first slot `s = r * R` starts after
`x[i₂].time` and is an honest round opening slot (`HonestOpenerAt M S Sched s`), whose proposer's
tick at the start of slot `s` put `B` on the wire, with no block the proposer held before the start
of slot `s` having `B`'s root, every attestation an honest awake validator put on the wire at a
tick before the support cutoff of slot `(r + 1) * R + 1` (the action time of round `r + 1`) has
height at most the height of `B`'s chain state.

Why: an attestation sent before the support cutoff of slot `s₀ + 1` has height at most `H`, which
is less than `B`'s height. From then on, Lemma 82 sends it at the support cutoff of a slot
`s_a + 1`, a round's first slot (the time is a round's action time, Lemma 49) before
`(r + 1) * R`, so `s_a ≤ s`, and names an entry `E` of the honest chain at slot `s_a` at its height;
`E` is `B` or an ancestor of `B` (the chain before `s` ends at `B`, and an updater's confirmation
of `s` is `B`), so its height is at most `B`'s (Lemma 47 (d)).

Read aloud: up to the next round's attestations, no honest validator has attested at a height
greater than the proposal of an honest round opening slot.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₂`: the hand-over step; `H`: the threshold;
- `r`: the round; `s`: its first slot; `B`: the proposal.

 -/
theorem lem107_honest_attestations_at_most_opening_height (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ anchor i₂ H r s : ℕ) (B : Block V)
    -- every time is reached
    -- blocks and Goldfish votes are delivered within `Δ` after `GST`
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- roots name blocks up to the real time of each updater's tick to the support cutoff of the next slot (T-RC86-1,)
    (hRootsU : ∀ v ∈ updaterAt M S A x s, RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C (s + 1)))))
    -- a block reaches a validator only once it holds the parent
    (hParent : ParentHeldAtDelivery M x)
    -- fewer than a quorum in the adversary set up to that real time (T-RC86-1,)
    (hAdvQU : ∀ v ∈ updaterAt M S A x s, A.AdversaryFewerThanQuorumUntil x (quorum V) (x.time (x.tickStep v (M.supportCutoff S.C (s + 1)))))
    -- committee sleepiness from `anchor` for the slots whose update is at most `M.supportCutoff S.C (s + 1)`, at or before the hand-over step's time
    (hSleepK : CommitteeSleepinessUntil M S A x anchor (M.supportCutoff S.C (s + 1))) (hAnchor : anchor ≤ x.time i₂)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀) (ht₀ : M.supportCutoff S.C (s₀ + 1) ≤ x.time i₂)
    -- the updaters' confirmations of the slots from `s₀` to before `s` form one chain
    (hChain : ConfirmationsChainBefore M S A x s₀ s)
    -- the chain invariant and the lock invariant at the slots after `s₀` and at most `s`
    (hInv : ∀ s' : ℕ, s₀ < s' → s' ≤ s →
      ChainInvFor M S A x (honestActiveAt M S A x s')
        (OnHonestChainBefore M S A x s₀ s') s')
    (hLocks : ∀ s' : ℕ, s₀ < s' → s' ≤ s → ∀ w ∈ honestActiveAt M S A x s',
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ s') s' w)
    -- the lock invariant at the healed slot itself
    (hLocks₀ : ∀ w ∈ honestActiveAt M S A x s₀,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ (s₀ + 1)) s₀ w)
    -- every honest attestation sent before the support cutoff of `s₀ + 1` has height at most `H`
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    -- the caches of every honest validator from the hand-over step to that real time (T-RC86-1,)
    (hCachesU : ∀ v ∈ updaterAt M S A x s, ∀ (j : ℕ) (w : V), x.time i₂ ≤ x.time j →
      x.time j ≤ x.time (x.tickStep v (M.supportCutoff S.C (s + 1))) → w ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st j w))
    -- `s` is the first slot of round `r`, starting after the hand-over step's time
    (hs : s = r * S.C.R) (hAfter : x.time i₂ < M.slotStart S.C s ∧
      ∀ k : ℕ, x.lbl k = Event.tick (S.P.proposer s) (M.slotStart S.C s) → x.time i₂ < x.time k)
    -- `s` is an honest round opening slot
    (hOpener : HonestOpenerAt M S A x s)
    -- the proposer's tick at the start of `s` put `B` on the wire
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick (S.P.proposer s) (M.slotStart S.C s) ∧
      (⟨S.P.proposer s, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i)
    -- no block the proposer held before the start of `s` has `B`'s root
    (hNoCollision : ¬ RootCollisionAtProposal M S A x s B)
    -- the honest committee voters of the slot and of the slot before it, and the proposer, stay active for the sync delay
    -- after the time the synchronous delivery reads them (T-RC86-2,)
    (hHold : ∀ s' : ℕ, s - 1 ≤ s' → s' ≤ s → ∀ u ∈ honestActiveAt M S A x s', u ∈ S.P.committee s' →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hHoldP : S.P.proposer s ∈ A.activeThroughout x ((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs)) :
    OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C ((r + 1) * S.C.R + 1)) (M.supportCutoff S.C ((r + 1) * S.C.R + 1))
      (M.chainStateOf S.C B).h :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem107_honest_attestations_at_most_opening_height M F U Fx)
    S A x R GST s₀ anchor i₂ H r s B E hNet hSkew hRedeliver Sy hΔs hRootsU hParent hAdvQU
    hSleepK hAnchor hGST ht₀ hChain hInv hLocks hLocks₀ hOld hCachesU hs hAfter hOpener hPropose
    hNoCollision hHold hHoldP

/-- **Lemma 94, the round's attesters after healing carry the finality pair.** In an execution
where every time is reached, corruption is permanent, blocks and Goldfish votes are delivered within
`Δ` after `GST` (synchrony from the receiver's wake, and catch-up on wake), a root names one block
among what honest validators hold by the support cutoff of slot `s + 1`, a block reaches a validator
only once it holds the parent, and nobody votes in an honest validator's name; under
unforgeability, with fewer than a quorum of validators ever in the adversary set and committee
sleepiness from `anchor`, at or before `x[i₂].time`; with `GST` at most the vote time of slot `s₀`
and the support cutoff of slot `s₀ + 1` at or before `x[i₂].time`; with the updaters'
confirmations of the slots from `s₀` to `s` forming one chain, the chain invariant and the lock
invariant at every slot after `s₀` and at most `s`, the lock invariant at the healed slot `s₀`
itself, every honest attestation sent before the support cutoff of slot `s₀ + 1` of height at most
`H`, and the caches of every validator honest at a step at a time from `x[i₂].time` to the support
cutoff of slot `s + 1` on the honest chain with justification height greater than `H`: for the
round `r` whose first slot `s = r * R` starts after `x[i₂].time` and is an honest round opening slot
(`HonestOpenerAt M S Sched s`), whose proposer's tick at the start of slot `s` put `B` on the wire,
with no block the proposer held before the start of slot `s` having `B`'s root; when every
attestation an honest awake validator put on the wire at a tick before the support cutoff of slot
`s + 1` (the round's action time) has height at most the justification height of `B`'s chain state
(`hOldJ`), and `H` is less than that justification height (`hHJ`): every member `u` of
`honestActiveAt M S Sched s` put on the wire, at its tick at the support cutoff of slot `s + 1`
itself, a target of its own at the height of `B`'s chain state naming the root of `B`'s `T_h`, which
carries the finality pair `(h_j(B), J(B))` (the justification height of `B`'s chain state and the
root of its justified block) when the finalization height of `B`'s chain state is less than its
justification height, unless `u` already holds, in the state its tick reads, a block `D` with `B` an ancestor of `D`
or `D` itself whose chain state finalizes at a height at least that justification height, provided
no block an honest active member of the round holds when it ticks to the round's action time includes
an attestation put on the wire at a tick to that action time. It excludes the run in
which a block of slot `s + 1`, including the targets the round's members ticking early sent and targets of the
adversary with no finality pair, justifies `B`'s height before a later member's tick: that member's pair then names
`B`'s height and `T_h(B)`, and nothing it holds finalizes `B`'s justification.

Why: `u`'s record holds nothing at `h(B)` (`hOldJ`, `h_j(B) < h(B)`), so its tick at the action
time builds a fresh target at `h(B)` from the head `D` the duty reads, `B` or a descendant of `B`
(Lemma 48b). A justification on `D`'s chain at a height greater than `h_j(B)`, or a finalization
at a height at least `h_j(B)`, would have an honest member whose attestation, sent before the action
time, has a height greater than `h_j(B)` (Lemma 66), against `hOldJ`: so `h_j(D) = h_j(B)`,
`h_F(D) < h_j(B)`, and `J(D) = J(B)`.
`u`'s record at `h_j(B) > H` holds no timeout, and no target or lock but `J(B)`'s root (Lemmas 82
and 83, the honest chain before `s` ending at `B`). Lemma 92 attaches the pair.

Read aloud: when no honest validator has attested above `B`'s justification height before the
round's action time, and that height is greater than the threshold, every honest active validator
of the honest round opening slot attests for `B`'s height at the action time, vouching for `B`'s
justification when it is not yet finalized, or already holds a block on `B`'s chain that finalizes it, provided no
member already holds, when it attests, a block including one of the round's own attestations.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₂`: the hand-over step; `H`: the threshold;
- `r`: the round; `s`: its first slot; `B`: the proposal; `u`: the member.

 -/
theorem lem94_round_attesters_after_healing (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ anchor i₂ H r s : ℕ) (B : Block V) (u : V)
    -- every time is reached
    -- blocks and Goldfish votes are delivered within `Δ` after `GST`
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- a root names one block among what honest validators hold by the support cutoff of `s + 1`
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C (s + 1)))
    -- roots name blocks up to the real time of each updater's tick to the support cutoff of the next slot (T-RC86-1,)
    (hRootsU : ∀ v ∈ updaterAt M S A x s, RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C (s + 1)))))
    -- a block reaches a validator only once it holds the parent
    (hParent : ParentHeldAtDelivery M x)
    -- fewer than a quorum of validators have been in the adversary set up to `M.supportCutoff S.C (s + 1)`
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (M.supportCutoff S.C (s + 1)))
    -- fewer than a quorum in the adversary set up to that real time (T-RC86-1,)
    (hAdvQU : ∀ v ∈ updaterAt M S A x s, A.AdversaryFewerThanQuorumUntil x (quorum V) (x.time (x.tickStep v (M.supportCutoff S.C (s + 1)))))
    -- committee sleepiness from `anchor` for the slots whose update is at most `M.supportCutoff S.C (s + 1)`, at or before the hand-over step's time
    (hSleepK : CommitteeSleepinessUntil M S A x anchor (M.supportCutoff S.C (s + 1))) (hAnchor : anchor ≤ x.time i₂)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀) (ht₀ : M.supportCutoff S.C (s₀ + 1) ≤ x.time i₂)
    -- the updaters' confirmations of the slots from `s₀` to `s` form one chain
    (hChain : ConfirmationsChainBefore M S A x s₀ (s + 1))
    -- the chain invariant and the lock invariant at the slots after `s₀` and at most `s`
    (hInv : ∀ s' : ℕ, s₀ < s' → s' ≤ s →
      ChainInvFor M S A x (honestActiveAt M S A x s')
        (OnHonestChainBefore M S A x s₀ s') s')
    (hLocks : ∀ s' : ℕ, s₀ < s' → s' ≤ s → ∀ w ∈ honestActiveAt M S A x s',
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ s') s' w)
    -- the lock invariant at the healed slot itself
    (hLocks₀ : ∀ w ∈ honestActiveAt M S A x s₀,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ (s₀ + 1)) s₀ w)
    -- every honest attestation sent before the support cutoff of `s₀ + 1` has height at most `H`
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    -- the caches of the honest validators from the hand-over to the support cutoff of `s + 1`
    (hCaches : ∀ (j : ℕ) (w : V), x.time i₂ ≤ x.time j → x.time j ≤ M.supportCutoff S.C (s + 1) →
      w ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st j w))
    -- the caches of every honest validator from the hand-over step to that real time (T-RC86-1,)
    (hCachesU : ∀ v ∈ updaterAt M S A x s, ∀ (j : ℕ) (w : V), x.time i₂ ≤ x.time j →
      x.time j ≤ x.time (x.tickStep v (M.supportCutoff S.C (s + 1))) → w ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st j w))
    -- `s` is the first slot of round `r`, starting after the hand-over step's time
    (hs : s = r * S.C.R) (hAfter : x.time i₂ < M.slotStart S.C s ∧
      ∀ k : ℕ, x.lbl k = Event.tick (S.P.proposer s) (M.slotStart S.C s) → x.time i₂ < x.time k)
    -- `s` is an honest round opening slot
    (hOpener : HonestOpenerAt M S A x s)
    -- the proposer's tick at the start of `s` put `B` on the wire
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick (S.P.proposer s) (M.slotStart S.C s) ∧
      (⟨S.P.proposer s, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i)
    -- no block the proposer held before the start of `s` has `B`'s root
    (hNoCollision : ¬ RootCollisionAtProposal M S A x s B)
    -- the honest committee voters of the slot and of the slot before it, and the proposer, stay active for the sync delay
    -- after the time the synchronous delivery reads them (T-RC86-2,)
    (hHold : ∀ s' : ℕ, s - 1 ≤ s' → s' ≤ s → ∀ u ∈ honestActiveAt M S A x s', u ∈ S.P.committee s' →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hHoldP : S.P.proposer s ∈ A.activeThroughout x ((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- hOldJ: no honest attestation at a height greater than `h_j(B)` before the action time
    (hOldJ : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s + 1)) (M.supportCutoff S.C (s + 1))
        (M.chainStateOf S.C B).h_j)
    -- hHJ: `B`'s justification height is greater than the threshold
    (hHJ : H < (M.chainStateOf S.C B).h_j)
    -- no block an honest active member of the round holds when it ticks to the round's action time includes an
    -- attestation put on the wire at a tick to that action time
    (hTickInputs : ∀ v ∈ honestActiveAt M S A x s, ∀ Z ∈ (x.tickInput v (M.supportCutoff S.C (s + 1))).tree,
      ∀ a ∈ Z.attestations, ∀ (j : ℕ) (w : V), x.lbl j = Event.tick w (M.supportCutoff S.C (s + 1)) →
      (⟨w, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∉ x.sent (j + 1) - x.sent j)
    -- `u` is an honest active validator of `s`
    (hu : u ∈ honestActiveAt M S A x s) :
    ∃ (i : ℕ) (a : Attestation V), x.lbl i = Event.tick u (M.supportCutoff S.C (s + 1)) ∧
      (⟨u, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i ∧
      a.val_index = u ∧ a.h = (M.chainStateOf S.C B).h ∧ a.T = (M.chainStateOf S.C B).T_h.root ∧
      a.τ = false ∧
      ((M.chainStateOf S.C B).h_F < (M.chainStateOf S.C B).h_j →
        a.finality_pair =
          some (FinalityPair.mk (M.chainStateOf S.C B).h_j (M.chainStateOf S.C B).J.root) ∨
        ∃ D ∈ (x.tickInput u (M.supportCutoff S.C (s + 1))).tree, B.AncestorEq D ∧
          (M.chainStateOf S.C B).h_j ≤ (M.chainStateOf S.C D).h_F) :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem94_round_attesters_after_healing M F U Fx) S
    A x R GST s₀ anchor i₂ H r s B u E hNet hSkew hRedeliver Sy hΔs hRoots hRootsU hParent hAdvQ hAdvQU
    hSleepK hAnchor hGST ht₀ hChain hInv hLocks hLocks₀ hOld hCaches hCachesU hs hAfter hOpener hPropose
    hNoCollision hHold hHoldP hOldJ hHJ hTickInputs hu

/-- **Lemma 95, two consecutive honest round opening slots after healing: the height step and the
finalization.** In an execution where every time is reached, corruption is permanent, blocks and
Goldfish votes are delivered within `Δ` after `GST` and attestations within `Δ_F` (synchrony from
the receiver's wake, and catch-up on wake), a root names one block among what honest validators
hold by the vote time of slot `(r + 1) * R`, a block reaches a validator only once it holds the
parent, and nobody votes in an honest validator's name; under unforgeability, with fewer than a
quorum of validators ever in the adversary set and committee sleepiness from `anchor`, at or before
`x[i₂].time`; with `GST` at most the vote time of slot `s₀` and the support cutoff of slot `s₀ + 1`
at or before `x[i₂].time`; with the updaters' confirmations of the slots from `s₀` to before
`(r + 1) * R − 1` forming one chain, the chain invariant and the lock invariant at every slot after
`s₀` and at most `(r + 1) * R − 1`, the lock invariant at the healed slot `s₀` itself, every honest
attestation sent before the support cutoff of slot `s₀ + 1` of height at most `H`, and the caches
of every validator honest at a step at a time from `x[i₂].time` to the vote time of slot
`(r + 1) * R` on the honest chain with justification height greater than `H`; with
`Δ_F + Δ ≤ 4Δ(k + 1)`; with roots naming blocks and the honest caches on the honest
chain also up to the real time of every tick to a clock value at most the vote time of slot
`(r + 1) * R`, and the honest committee voters of the slot before each opener's slot and of the first
opener's slot, and each opener, active for the sync delay after the time the synchronous delivery
reads them: for the rounds `r` and `r + 1` whose first slots are honest round opening
slots, the first starting after `x[i₂].time`, and so does every tick of its proposer to that start, and with a quorum of honest active validators
(`QuorumActiveAt`), whose proposers' ticks at their starts put `B` and `B'` on the wire, with no
block either proposer held before its slot's start having its proposal's root; when every
attestation an honest awake validator put on the wire at a tick before the support cutoff of slot
`r * R + 1` (the action time of round `r`) has height at most the justification height of `B`'s
chain state (`hOldJ`), and `H` is less than that justification height (`hHJ`), and
no block an honest active member of the round holds when it ticks to the round's action time includes
an attestation put on the wire at a tick to that action time. It excludes the run in
which a block of slot `r * R + 1`, including the targets the round's members ticking early sent and targets of the
adversary with no finality pair, justifies `B`'s height before a later member's tick: that member's pair then names
`B`'s height and `T_h(B)`, and nothing it holds finalizes `B`'s justification: `B` is `B'` or an
ancestor of `B'`, `B'`'s chain-state height is at least `B`'s plus one, and `B'`'s finalization
height is at least `B`'s justification height.

Why: the first two conjuncts are `consecutive_openings_height_step`'s. For the third, when
`h_F(B) < h_j(B)`: every member of the quorum sent at the action time of round `r` the target of
Lemma 94, carrying the pair `(h_j(B), J(B))`, and it reaches the proposer of `(r + 1) * R` before
its slot starts. Every justification on the chain from `B` to `B'`'s parent is at a height at most
`h(B)` (Lemma 107 at `r`, through the honest member of its certificate, Lemma 66), so the pair stays
pending there, with at most one pair after it (`K_W ≥ 2`), unless it is already finalized. A
member's attestation already on the parent's chain was counted for the pair; one not on it is
valid against the parent and included in `B'` (Lemma 52). Lemma 93 finalizes the pair at `B'`.

Read aloud: when no honest validator has attested above `B`'s justification height before round
`r`'s action time, and that height is greater than the threshold, the next honest round opening
slot extends the previous one's proposal, raises the height, and finalizes the previous proposal's
justification.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₂`: the hand-over step; `H`: the threshold;
- `r`: the first round; `B`, `B'`: the two proposals.

 -/
theorem lem95_consecutive_openings_step (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ anchor i₂ H r : ℕ) (B B' : Block V)
    -- every time is reached
    -- blocks and Goldfish votes are delivered within `Δ` after `GST`
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    -- attestations are delivered within `Δ_F` after `GST`
    {ΔNet_F : ℕ} (E_F : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    {Δs_F : ℕ} (Sy_F : SyncedWithin A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST)
    (hΔs_F : (Δs_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S ∨ (Δs_F : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind ≤ 4 * Δ S * S.C.k)
    -- a root names one block among what honest validators hold by the vote time of `(r + 1) R`
    (hRoots : RootsNameBlocksUntil M A x (M.voteTime S.C ((r + 1) * S.C.R)))
    -- roots name blocks up to the real time of every tick to a clock value at most the vote time of slot
    -- `(r + 1) * S.C.R` (, the callees' per-tick rows, T-RC86-1)
    (hRootsK : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.voteTime S.C ((r + 1) * S.C.R) →
      RootsNameBlocksUntil M A x (x.time k))
    -- a block reaches a validator only once it holds the parent
    (hParent : ParentHeldAtDelivery M x)
    -- fewer than a quorum of validators have been in the adversary set up to the support cutoff of slot `(r + 1) * S.C.R + 1`
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (M.supportCutoff S.C ((r + 1) * S.C.R + 1)))
    -- committee sleepiness from `anchor` for the slots whose update is at most `M.supportCutoff S.C ((r + 1) * S.C.R)`, at or before the hand-over step's time
    (hSleepK : CommitteeSleepinessUntil M S A x anchor (M.supportCutoff S.C ((r + 1) * S.C.R))) (hAnchor : anchor ≤ x.time i₂)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀) (ht₀ : M.supportCutoff S.C (s₀ + 1) ≤ x.time i₂)
    -- the updaters' confirmations of the slots from `s₀` to before `(r + 1) R − 1` form one chain
    (hChain : ConfirmationsChainBefore M S A x s₀ ((r + 1) * S.C.R - 1))
    -- the chain invariant and the lock invariant at the slots after `s₀`, at most `(r + 1) R − 1`
    (hInv : ∀ s' : ℕ, s₀ < s' → s' ≤ (r + 1) * S.C.R - 1 →
      ChainInvFor M S A x (honestActiveAt M S A x s')
        (OnHonestChainBefore M S A x s₀ s') s')
    (hLocks : ∀ s' : ℕ, s₀ < s' → s' ≤ (r + 1) * S.C.R - 1 → ∀ w ∈ honestActiveAt M S A x s',
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ s') s' w)
    -- the lock invariant at the healed slot itself
    (hLocks₀ : ∀ w ∈ honestActiveAt M S A x s₀,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ (s₀ + 1)) s₀ w)
    -- every honest attestation sent before the support cutoff of `s₀ + 1` has height at most `H`
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    -- the caches of the honest validators from the hand-over to the vote time of `(r + 1) R`
    (hCaches : ∀ (j : ℕ) (w : V), x.time i₂ ≤ x.time j →
      x.time j ≤ M.voteTime S.C ((r + 1) * S.C.R) →
      w ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st j w))
    -- the caches of every honest validator from the hand-over step up to the real time of every such tick
    -- (, T-RC86-1)
    (hCachesK : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.voteTime S.C ((r + 1) * S.C.R) →
      ∀ (j : ℕ) (w : V), x.time i₂ ≤ x.time j → x.time j ≤ x.time k → w ∉ A.corrupted j →
        CachesOnChain M S A x s₀ H (x.st j w))
    -- the attestations of a round reach a proposer that woke at its proposal window's start
    (hParam : Δ_F S + Δ S ≤ 4 * Δ S * (S.C.k + 1))
    -- the first slot of round `r` starts after the hand-over step's time, and so does every tick of its proposer
    -- to that start (, the clause made strict)
    (hAfter : x.time i₂ < M.slotStart S.C (r * S.C.R) ∧
      ∀ k : ℕ, x.lbl k = Event.tick (S.P.proposer (r * S.C.R)) (M.slotStart S.C (r * S.C.R)) → x.time i₂ < x.time k)
    -- the two first slots are honest round opening slots
    (hOpener : HonestOpenerAt M S A x (r * S.C.R))
    (hOpener' : HonestOpenerAt M S A x ((r + 1) * S.C.R))
    -- a quorum of honest active validators at the first
    (hQuorum : QuorumActiveAt M S A x (r * S.C.R))
    -- every attestation a member of round `r`'s honest active validators put on the wire at a tick up to the round's
    -- action time, with the member's justified height at the next opener's proposal-window start at most its
    -- height, is delivered to the next opener before its tick to its slot's start
    (hDel : ∀ u ∈ honestActiveAt M S A x (r * S.C.R), ∀ (j t' : ℕ) (a : Attestation V),
      x.lbl j = Event.tick u t' → t' ≤ M.supportCutoff S.C (r * S.C.R + 1) →
      (⟨u, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (j + 1) - x.sent j →
      M.justifiedHeight (x.stateBefore (M.proposalWindowStart S.C ((r + 1) * S.C.R)) u) ≤ a.h →
      ∃ d : ℕ, x.lbl d = Event.deliver (S.P.proposer ((r + 1) * S.C.R)) ⟨u, NamedObject.attest a⟩ ∧
        d < x.tickStep (S.P.proposer ((r + 1) * S.C.R)) (M.slotStart S.C ((r + 1) * S.C.R)))
    -- the two proposers' ticks put `B` and `B'` on the wire
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick (S.P.proposer (r * S.C.R)) (M.slotStart S.C (r * S.C.R)) ∧
      (⟨S.P.proposer (r * S.C.R), NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i)
    (hPropose' : ∃ i : ℕ, x.lbl i = Event.tick (S.P.proposer ((r + 1) * S.C.R)) (M.slotStart S.C ((r + 1) * S.C.R)) ∧
      (⟨S.P.proposer ((r + 1) * S.C.R), NamedObject.block B'⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i)
    -- no block either proposer held before its slot's start has its proposal's root
    (hNoCol : ¬ RootCollisionAtProposal M S A x (r * S.C.R) B)
    (hNoCol' : ¬ RootCollisionAtProposal M S A x ((r + 1) * S.C.R) B')
    -- the honest committee voters of the slot before each honest round opening slot and of the first one, and each
    -- opener, stay active for the sync delay after the time the synchronous delivery reads them
    -- T-RC86-2,)
    (hHold : ∀ σ : ℕ, r * S.C.R - 1 ≤ σ → σ ≤ r * S.C.R → ∀ u ∈ honestActiveAt M S A x σ, u ∈ S.P.committee σ →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C σ - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C σ - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hHold' : ∀ u ∈ honestActiveAt M S A x ((r + 1) * S.C.R - 1), u ∈ S.P.committee ((r + 1) * S.C.R - 1) →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C ((r + 1) * S.C.R - 1) - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C ((r + 1) * S.C.R - 1) - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hHoldP : S.P.proposer (r * S.C.R) ∈ A.activeThroughout x ((M.slotStart S.C (r * S.C.R) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C (r * S.C.R) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hHoldP' : S.P.proposer ((r + 1) * S.C.R) ∈ A.activeThroughout x ((M.slotStart S.C ((r + 1) * S.C.R) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C ((r + 1) * S.C.R) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- hOldJ: no honest attestation at a height greater than `h_j(B)` before round `r`'s action
    -- time
    (hOldJ : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (r * S.C.R + 1)) (M.supportCutoff S.C (r * S.C.R + 1))
      (M.chainStateOf S.C B).h_j)
    -- no block an honest active member of the round holds when it ticks to the round's action time includes an
    -- attestation put on the wire at a tick to that action time
    (hTickInputs : ∀ v ∈ honestActiveAt M S A x (r * S.C.R), ∀ Z ∈ (x.tickInput v (M.supportCutoff S.C (r * S.C.R + 1))).tree,
      ∀ a ∈ Z.attestations, ∀ (j : ℕ) (w : V), x.lbl j = Event.tick w (M.supportCutoff S.C (r * S.C.R + 1)) →
      (⟨w, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∉ x.sent (j + 1) - x.sent j)
    -- hHJ: `B`'s justification height is greater than the threshold
    (hHJ : H < (M.chainStateOf S.C B).h_j) :
    B.AncestorEq B' ∧ (M.chainStateOf S.C B).h + 1 ≤ (M.chainStateOf S.C B').h ∧
      (M.chainStateOf S.C B).h_j ≤ (M.chainStateOf S.C B').h_F :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem95_consecutive_openings_step M F U Fx) S A x R GST s₀
    anchor i₂ H r B B' E hNet hSkew hRedeliver E_F hNet_F hSkew_F Sy hΔs Sy_F hΔs_F hRoots hRootsK hParent hAdvQ hSleepK hAnchor hGST ht₀ hChain hInv
    hLocks hLocks₀ hOld hCaches hCachesK hParam hAfter hOpener hOpener' hQuorum
    (fun u hu j t' a h₁ h₂ h₃ h₄ => Or.inl (hDel u hu j t' a h₁ h₂ h₃ h₄)) hPropose hPropose' hNoCol hNoCol' hHold hHold' hHoldP hHoldP'
    hOldJ hTickInputs hHJ

/-! ## Three facts the composition reads -/

omit [RootOrder] in
/-- **The timeout is at least two rounds less one slot, from the phase's spacing clause.** When the
honest round opening slots `r 0 < … < r m` of `HonestOpeningSeq` number at least three (`2 ≤ m`),
`2R ≤ δt + 1`.

Why: the spacing clause at `i = 0` gives `r 2 * R ≤ r 0 * R + δt + 1`, and the sequence is strictly
increasing, so `r 0 + 2 ≤ r 2`.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`: the setup, the schedule; `r`: the rounds of the honest round opening slots; `m`:
  the index of the last one; `tF`, `tL`: the times the sequence lies between.

Read aloud: the phase's spacing clause, at two consecutive rounds, is the timeout condition Lemma
96 reads; the finality statement derives it and does not take it.

 -/
theorem two_R_le_δt_succ_of_seq (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N) (r : ℕ → ℕ)
    (m tF tL : ℕ)
    -- `r 0 < … < r m` are honest round opening slots between `tF` and `tL`
    (hSeq : HonestOpeningSeq M S A x r m tF tL)
    -- at least three of them
    (hm : 2 ≤ m) :
    2 * S.C.R ≤ S.C.δt + 1 := by
  have h01 : r 0 < r 1 := hSeq.mono 0 (by omega)
  have h12 : r 1 < r 2 := hSeq.mono 1 (by omega)
  have hsp : r 2 * S.C.R ≤ r 0 * S.C.R + S.C.δt + 1 := hSeq.spacing 0 hm
  have h2 : r 0 + 2 ≤ r 2 := by omega
  have hmul : r 0 * S.C.R + 2 * S.C.R ≤ r 2 * S.C.R := by
    rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ h2
  omega

omit [RootOrder] in
/-- **The phase has at least nine honest round opening slots.** The span premise of record,
`OpeningsOutsideWaitsAndWindows S r m`, asks nine of the honest round opening slots `r 0, …, r m`
outside every two spans of `δt` slots and five spans of `k + 2` slots; so `8 ≤ m`.

Why: at any choice of the spans, nine indices of `0, …, m` pass the filter, and the filter keeps at
most the `m + 1` indices.

The variables:
- `M`: the model; `F`: its facts;
- `S`: the setup; `r`: the rounds of the honest round opening slots; `m`: the index of the last
  one.

Read aloud: nine honest round opening slots outside the spans are nine of the sequence's.

 -/
theorem eight_le_m_of_openings (S : Setup V) (r : ℕ → ℕ) (m : ℕ)
    -- nine honest round opening slots outside every two spans of `δt` slots and five spans of
    -- `k + 2` slots
    (hm : OpeningsOutsideWaitsAndWindows S r m) : 8 ≤ m := by
  have h := hm (fun _ : Fin 2 => 0) (fun _ : Fin 5 => 0)
  have h9 : 9 ≤ (Finset.range (m + 1)).card := le_trans h (Finset.card_filter_le _ _)
  rw [Finset.card_range] at h9
  omega

/-- **A bound on the old honest attestations can be raised.** When every attestation an honest
awake validator put on the wire at a tick before `t₀` has height at most `H`, and `H ≤ H'`, every
such attestation has height at most `H'`.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t₀`: the time before which the
  attestations are read; `H`, `H'`: the two bounds.

Read aloud: a bound on the heights of the honest attestations before `t₀` stays a bound when it is
raised.

 -/
theorem oldAttestationsAtMost_mono (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (t₀ H H' : ℕ)
    -- every honest attestation sent before `t₀` has height at most `H`
    (h : OldAttestationsAtMostHonestAt M S A x t₀ t₀ H)
    -- `H` is at most `H'`
    (hle : H ≤ H') :
    OldAttestationsAtMostHonestAt M S A x t₀ t₀ H' :=
  fun i t v a hl ht hH hs => le_trans (h i t v a hl ht hH hs) hle

/-! ## The reader -/

/-- **Lemma 97, the reader finalizes what an honest proposal's chain finalized.** In an execution
where every time is reached, corruption is permanent, blocks and Goldfish votes are delivered
within `Δ` after `GST` (synchrony from the receiver's wake, and catch-up on wake), a root names one
block among what honest validators hold by the reading time `T`, a block reaches a validator only
once it holds the parent, and nobody votes in an honest validator's name; under unforgeability,
with fewer than a quorum of validators ever in the adversary set and committee sleepiness from
`anchor`, at or before `x[i₂].time`; with `GST` at least one delay or one sync delay, whichever is
longer, before the support cutoff of slot `s₀`, and the support cutoff of slot `s₀ + 1` at or before
`x[i₂].time`; with, for every slot whose update is at most
`T`, the updaters' confirmations from `s₀` up to it forming one chain and the chain invariant and
the lock invariant at it, the lock invariant at the healed slot `s₀` itself, every honest
attestation sent before the support cutoff of slot `s₀ + 1` of height at most `H`, and the caches
of every validator honest at a step at a time from `x[i₂].time` to `T` on the honest chain with
justification height greater than `H`: for the honest round opening slot `s_D = r_D * R` starting
after `x[i₂].time`, whose support cutoff is at most `T`, whose proposer's tick at its start put
`D` on the wire, with no block the proposer held before that start having `D`'s root, and with `D`'s
height greater than `H`, every validator `v` honest through a step `j` at or before some support
cutoff at most `T` (some slot `s'` with `x[j].time ≤ M.supportCutoff S.C s' ≤ T`) and awake for one
whole delay or one whole sync delay, whichever is longer, between the start of slot
`s_D` and the time of step `j` has, at step `j`, `D`'s finalized block or a descendant of it as its
finalized block.

Why: `D` is on the honest chain, so the honest justified blocks and the certificates' entries at
the rounds' first slots whose update ran by `T` are compatible with it. The reader receives `D`
within the interval it is awake for: by synchrony from the send when the interval starts at the
send, and otherwise from a validator active at the interval's start and holding `D` then
, through the sync fact. When `D` enters its tree, its justified block is `F(D)` or a
descendant of it, or of a smaller justification height, and every block of its tree higher than
`D` descends from `F(D)` (a certificate at `D`'s height names the honest chain's entry there), so
the finality update moves its finalized block to `F(D)` if it was not already at or past it.

Read aloud: whoever is awake for a delay after an honest round opening slot's proposal, at a step
at or before some support cutoff at most `T`, has finalized at least what that proposal's chain
finalized.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₂`: the hand-over step; `H`: the threshold; `T`: the reading time;
- `r_D`, `s_D`: the round and its first slot; `D`: the proposal; `j`: the reader's step, at or
  before some support cutoff at most `T`; `v`: the reader.

 -/
theorem lem97_reader_finalized (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ anchor i₂ H T r_D s_D j : ℕ) (D : Block V)
      (v : V)
    -- every time is reached
    -- blocks and Goldfish votes are delivered within `Δ` after `GST`
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- a root names one block among what honest validators hold by `T`
    (hRoots : RootsNameBlocksUntil M A x T)
    -- roots name blocks up to the real time of each updater's tick to the support cutoff of the next slot (T-RC86-1,)
    (hRootsU : ∀ v ∈ updaterAt M S A x s_D, RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C (s_D + 1)))))
    -- a block reaches a validator only once it holds the parent
    (hParent : ParentHeldAtDelivery M x)
    -- fewer than a quorum of validators have been in the adversary set up to `T`
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) T)
    -- fewer than a quorum in the adversary set up to that real time (T-RC86-1,)
    (hAdvQU : ∀ v ∈ updaterAt M S A x s_D, A.AdversaryFewerThanQuorumUntil x (quorum V) (x.time (x.tickStep v (M.supportCutoff S.C (s_D + 1)))))
    -- committee sleepiness from `anchor` for the slots whose update is at most `T`, at or before the hand-over step's time
    (hSleepK : CommitteeSleepinessUntil M S A x anchor T) (hAnchor : anchor ≤ x.time i₂)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀) (ht₀ : M.supportCutoff S.C (s₀ + 1) ≤ x.time i₂)
    -- the updaters' confirmations up to every slot whose update is at most `T` form one chain
    (hChain : ∀ σ : ℕ, M.supportCutoff S.C (σ + 1) ≤ T →
      ConfirmationsChainBefore M S A x s₀ (σ + 1))
    -- the chain invariant and the lock invariant at the slots whose update is at most `T`
    (hInv : ∀ s' : ℕ, s₀ < s' → M.supportCutoff S.C (s' + 1) ≤ T →
      ChainInvFor M S A x (honestActiveAt M S A x s')
        (OnHonestChainBefore M S A x s₀ s') s')
    (hLocks : ∀ s' : ℕ, s₀ < s' → M.supportCutoff S.C (s' + 1) ≤ T →
      ∀ w ∈ honestActiveAt M S A x s',
        LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ s') s' w)
    -- the lock invariant at the healed slot itself
    (hLocks₀ : ∀ w ∈ honestActiveAt M S A x s₀,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ (s₀ + 1)) s₀ w)
    -- every honest attestation sent before the support cutoff of `s₀ + 1` has height at most `H`
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    -- the caches of the honest validators from the hand-over to `T`
    (hCaches : ∀ (j' : ℕ) (w : V), x.time i₂ ≤ x.time j' → x.time j' ≤ T →
      w ∉ A.corrupted j' → CachesOnChain M S A x s₀ H (x.st j' w))
    -- the caches of every honest validator from the hand-over step to that real time (T-RC86-1,)
    (hCachesU : ∀ v ∈ updaterAt M S A x s_D, ∀ (j' : ℕ) (w : V), x.time i₂ ≤ x.time j' →
      x.time j' ≤ x.time (x.tickStep v (M.supportCutoff S.C (s_D + 1))) → w ∉ A.corrupted j' → CachesOnChain M S A x s₀ H (x.st j' w))
    -- `s_D` is the first slot of round `r_D`, its support cutoff at most `T`, starting after the
    -- hand-over step's time
    (hsD : s_D = r_D * S.C.R) (hT : M.supportCutoff S.C s_D ≤ T)
    (hAfter : x.time i₂ < M.slotStart S.C s_D ∧
      ∀ k : ℕ, x.lbl k = Event.tick (S.P.proposer s_D) (M.slotStart S.C s_D) → x.time i₂ < x.time k)
    -- `s_D` is an honest round opening slot
    (hOpener : HonestOpenerAt M S A x s_D)
    -- the proposer's tick at the start of `s_D` put `D` on the wire
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick (S.P.proposer s_D) (M.slotStart S.C s_D) ∧
      (⟨S.P.proposer s_D, NamedObject.block D⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i)
    -- no block the proposer held before the start of `s_D` has `D`'s root
    (hNoCol : ¬ RootCollisionAtProposal M S A x s_D D)
    -- the honest committee voters of the slot and of the slot before it, and the proposer, stay active for the sync delay
    -- after the time the synchronous delivery reads them (T-RC86-2,)
    (hHold : ∀ s' : ℕ, s_D - 1 ≤ s' → s' ≤ s_D → ∀ u ∈ honestActiveAt M S A x s', u ∈ S.P.committee s' →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    -- every honest committee member of every slot after `s_D` whose update is at most `T` is active from its duty window's
    -- start through the sync delay after that update; the proposer of `s_D` from one delay or one sync delay before its
    -- slot's start through the sync delay after its slot's update
    (hHoldC : ∀ σ' : ℕ, s_D + 1 ≤ σ' → M.supportCutoff S.C (σ' + 1) ≤ T → ∀ u ∈ honestActiveAt M S A x σ',
      u ∈ S.P.committee σ' → u ∈ A.activeThroughout x ((M.dutyWindowStart S.C σ' : ℕ) : ℝ)
        (((M.supportCutoff S.C (σ' + 1) : ℕ) : ℝ) + Δs))
    (hHoldP : S.P.proposer s_D ∈ A.activeThroughout x ((M.slotStart S.C s_D - max (Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C (s_D + 1) : ℕ) : ℝ) + Δs))
    -- `D`'s height is greater than the threshold
    (hHD : H < (M.chainStateOf S.C D).h)
    -- the reader: outside the adversary set after every step whose time is at most that of step `j`
    -- (B19-2 (a)), at or before some support cutoff at most `T`, awake for one whole delay between the
    -- start of `s_D` and the time of step `j`
    (hv : A.HonestThroughTime x (x.time j) v)
    (hjT : ∃ s' : ℕ, x.time j ≤ M.supportCutoff S.C s' ∧ M.supportCutoff S.C s' ≤ T)
    (hAwake : AwakeForDelayWithin S A x Δs v (M.slotStart S.C s_D) j) :
    (M.chainStateOf S.C D).F.AncestorEq (x.st j v).finalized :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem97_reader_finalized M F U Fx) S A x R GST s₀
    anchor i₂ H T r_D s_D j D v E hNet hSkew hRedeliver Sy hΔs hRoots hRootsU hParent hAdvQ hAdvQU hSleepK
    hAnchor hGST ht₀ hChain hInv hLocks hLocks₀ hOld hCaches hCachesU hsD hT hAfter hOpener hPropose hNoCol hHold hHoldC hHoldP
    hHD hv hjT hAwake

end GoldilocksCorrectness.Record.Statements.Executions

