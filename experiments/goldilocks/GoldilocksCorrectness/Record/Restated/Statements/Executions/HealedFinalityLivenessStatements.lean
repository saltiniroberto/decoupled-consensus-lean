module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.HealedFinalityLiveness
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# HealedFinalityLivenessStatements, over a model

The statement of
`GoldilocksCorrectness/Statements/Executions/HealedFinalityLivenessStatements.lean`, over a model
`M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: Lemma 98, finality liveness
after healing. Each is a one-line call of its proof page's twin of the same name, under
`Record/Restated/Proofs/Executions/`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

open GoldilocksCorrectness.Statements.Routines (Δ Δ_F anchorCW)

namespace GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Statements.Executions (healFrontSlots)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor hMax le_hMax IsEntry VoterTreeAt JustifiedInTree AnchorAt)
open GoldilocksCorrectness.Statements.Executions (OpeningsOutsideWaitsAndWindows Vocab.goldilocks
  acObject fgObject healFrontSlots)

open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- **Lemma 98, finality liveness after healing.** Under the top statements' premises without a
premise on roots, and the parameter condition `Δ_F + Δ + ΔClockAhead + ΔClockBehind < 4Δ(k + 1)`, for every time `t` from
`tAwakeEnd` on: some honest round opening slot's proposal of the phase has the root of a block its proposer
held (`RootCollisionAtOpening`); or two distinct blocks that honest validators hold at steps at
times at most `t` have the same root (`RootCollisionHeldBy M S Sched x t`); or, after `tAwakeEnd`
and up to `t`, every honest proposal followed by four consecutive honest round opening slots with
quorums at the first three, the last of them updated by `t`, is `B` or an ancestor of the finalized
block of every validator honest through a step at or before some support cutoff at most `t` and
awake for a delay after the fourth opening slot starts, a finalized block no validator had before the proposal
(`FinalityIncludedBetween M S Sched x Δs tAwakeEnd t`), unless a root collision hit one of the five
proposals, and, under the same conditions, that reader's finalized block is a strict descendant of
every finalized block a validator honest through its step had from `tAwakeEnd` until the proposal's
slot started (`FinalizedExtendedByHonestProposalsBetween`).

The hypotheses, in words: `GST` is at most `tGAT`; every time is reached; corruption is permanent;
blocks, Goldfish votes and attestations are delivered within their delays after `GST`; a block
reaches a validator only once it holds the parent; unforgeability; fewer than a third of the
validators have been in the adversary set up to `tAwakeEnd`; every validator outside the adversary
set at a time from `tGAT` to `tAwakeEnd` is awake then; committee sleepiness from
`anchorCW S tGAT` for the slots whose update is at most `t`; the honest round opening slots of the
rounds `rs 0 < … < rs m` lie between `tGAT + 4Δ · healFrontSlots S` and `tAwakeEnd`; nine honest
round opening slots lie outside every two spans of `δt` slots and five spans of `k + 2` slots;
fewer than two thirds of the validators have been in the adversary set up to `t`; and the attestations of a round reach the next round's
proposer even when it woke at the start of its proposal window (`Δ_F + Δ + ΔClockAhead + ΔClockBehind < 4Δ(k + 1)`); and, for every
round starting at or after `tAwakeEnd` whose next round's first slot is an honest round opening slot,
every attestation an honest active member of the round put on the wire at a tick up to the round's
action time, with the member's justified height at the next proposal window's start at most its
height, is delivered to the next opener before its tick to its slot's start, or is held by the next
opener before its proposal window starts; and `t` is a time at which no slot's update is half run: at every slot whose
update is at most `t`, or to whose update some validator ticked at a real time at most `t`, every
validator's tick to a clock value at most that update is at a real time at most `t`; and the premises of the three healed top statements it
calls: committee sleepiness up to the clock value of every tick at a real time at most `t`
(`hCommitteesTick`), every updater of a slot from the first honest round opening slot on whose update is at
most `t` active for the sync delay after its own tick to the next support cutoff (`hStay`), and, at every
slot whose update is at most `t`, the honest committee members (`hHold`, `hHoldC`) and an honest opener's
proposer (`hHoldP`) active for the sync delay after the times the synchronous delivery reads them; and, at every honest
round opening slot after the phase, no block an honest active member of the round holds when it ticks to the round's action time includes
an attestation put on the wire at a tick to that action time. It excludes the run in
which a block of the slot after the round's first slot, including the targets the round's members ticking early sent and targets of the
adversary with no finality pair, justifies that slot's proposal's height before a later member's tick: that member's pair then names
that slot's proposal's height and its `T_h`, and nothing it holds finalizes that slot's proposal's justification. No premise on roots and
none on any honest validator's state: the conclusion names the collisions.

Why: the facts after the hand-over and the inclusion up to `t` (Lemma 90 read up to `t`). For a
proposal `B` and the window's proposals `B₁` to `B₄`, with no root collision at the five: `B` is
`B₁` or an ancestor of it (the inclusion of `B`, read at the proposer of the window's first slot);
the first two rounds raise the height twice (Lemma 95); the third proposal justifies the second's
height (Lemma 96); up to the third round's action time no honest attestation is higher than the
second proposal (Lemma 107), so the fourth proposal finalizes the third's justification (Lemma 95),
at a height greater than `B`'s; the reader holds that finalization (Lemma 97). Its finalized block
has a slot greater than `B`'s, while every finalized block held before `B`'s slot starts has a
smaller slot. The second conclusion from the first and Lemma 86 read up to `t`
(`finalizedExtendedBetween_of_compatible_included`).



The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `tGAT`, `tAwakeEnd`: the start and end of the healing phase; `m`: the
  index of the last honest round opening slot; `rs`: the rounds of the honest round opening slots.

Read aloud: for every time `t` after the phase, unless a collision has hit by `t`, whenever four
consecutive honest round opening slots with quorums at the first three follow an honest proposal,
everyone awake for a delay after the fourth has, up to `t`, finalized that proposal or a descendant
of it, a block no validator had finalized before the proposal, and that finalized block strictly
extends every finalized block honest validators had before the proposal. -/
theorem lem98_healed_finality_liveness (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd m : ℕ) (rs : ℕ → ℕ)
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
    (hHoldF : ∀ i, i < m → ∀ v, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (rs i * S.C.R + 1)) →
      v ∈ A.activeThroughout x ((max (M.dutyWindowStart S.C (rs i * S.C.R)) GST : ℕ) : ℝ)
        (((max (M.dutyWindowStart S.C (rs i * S.C.R)) GST : ℕ) : ℝ) + Δs_F))
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
    -- time at most `t` (; the sentence of's `hLastTick` at every slot, which it replaces)
    (hTicksBy : TicksToUpdatesBy M S x t)
    -- committee sleepiness from `anchorCW S tGAT`, for the slots whose update is at most `t`
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) t)
    -- every tick at a real time at most `t`, to a clock value `c`: committee sleepiness from `anchorCW S tGAT` read up
    -- to `c`
    (hCommitteesTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → (x.time k : ℝ) ≤ t →
      CommitteeSleepinessUntil M S A x (anchorCW S tGAT) c)
    (hSeq : HonestOpeningSeq M S A x rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    -- every updater of a slot from the first honest round opening slot `rs 0 * S.C.R` on, whose update is at
    -- most `t`, is active for the sync delay after the real time of its own tick to the support cutoff of the
    -- next slot
    (hStay : ∀ σ : ℕ, rs 0 * S.C.R ≤ σ → M.supportCutoff S.C (σ + 1) ≤ t → ∀ u ∈ updaterAt M S A x σ,
      u ∈ A.activeThroughout x (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))))
        (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))) + Δs))
    (hOpenings : OpeningsOutsideWaitsAndWindows S rs m)
    -- fewer than two thirds of the validators corrupted up to `t`
    (hAdvQ : A.AdversaryFewerThanTwoThirdsUntil x (validator_count V) t)
    -- the attestations of a round reach a proposer that woke at its proposal window's start, with room for its clock
    --
    (hParam : (Δ_F S : ℝ) + Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * (S.C.k + 1))
    -- for every round starting at or after `tAwakeEnd` whose next round's first slot is an honest round
    -- opening slot, every attestation an honest active member of the round put on the wire at a tick up to
    -- the round's action time, with the member's justified height at the next proposal window's start at
    -- most its height, is delivered to the next opener before its tick to its slot's start, or is held by
    -- the next opener before its proposal window starts
    (hDelF : ∀ r' : ℕ, tAwakeEnd ≤ M.slotStart S.C (r' * S.C.R) → HonestOpenerAt M S A x ((r' + 1) * S.C.R) →
      ∀ u ∈ honestActiveAt M S A x (r' * S.C.R), ∀ (j t' : ℕ) (a : Attestation V), x.lbl j = Event.tick u t' →
      t' ≤ M.supportCutoff S.C (r' * S.C.R + 1) →
      (⟨u, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (j + 1) - x.sent j →
      M.justifiedHeight (x.stateBefore (M.proposalWindowStart S.C ((r' + 1) * S.C.R)) u) ≤ a.h →
      (∃ d : ℕ, x.lbl d = Event.deliver (S.P.proposer ((r' + 1) * S.C.R)) ⟨u, NamedObject.attest a⟩ ∧
      d < x.tickStep (S.P.proposer ((r' + 1) * S.C.R)) (M.slotStart S.C ((r' + 1) * S.C.R))) ∨
      a ∈ (x.stateBefore (M.proposalWindowStart S.C ((r' + 1) * S.C.R)) (S.P.proposer ((r' + 1) * S.C.R))).attestationsHeld)
    -- at every honest round opening slot after the phase, no block an honest active member of the round holds when it
    -- ticks to the round's action time includes an attestation put on the wire at a tick to that action time
    --
    (hTickInputs : ∀ r' : ℕ, tAwakeEnd ≤ M.slotStart S.C (r' * S.C.R) → HonestOpenerAt M S A x (r' * S.C.R) →
      ∀ v ∈ honestActiveAt M S A x (r' * S.C.R), ∀ Z ∈ (x.tickInput v (M.supportCutoff S.C (r' * S.C.R + 1))).tree,
      ∀ a ∈ Z.attestations, ∀ (j : ℕ) (w : V), x.lbl j = Event.tick w (M.supportCutoff S.C (r' * S.C.R + 1)) →
      (⟨w, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∉ x.sent (j + 1) - x.sent j)
    -- at every slot whose next slot starts at or after `tAwakeEnd` and whose update is at most `t`, the honest active
    -- committee members stay active for the sync delay after the time the synchronous delivery reads them (T-RC86-2,
    --
    (hHold : ∀ s' : ℕ, tAwakeEnd ≤ M.slotStart S.C (s' + 1) → M.supportCutoff S.C (s' + 1) ≤ t →
      ∀ u ∈ honestActiveAt M S A x s', u ∈ S.P.committee s' →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    -- every honest committee member of every slot starting at or after `tAwakeEnd` whose update is at most `t` is active
    -- from its duty window's start through the sync delay after that update; at every slot at or after `tAwakeEnd` with an
    -- honest opener whose update is at most `t`, its proposer through the sync delay after the slot's update
    --
    (hHoldC : ∀ σ' : ℕ, tAwakeEnd ≤ M.slotStart S.C σ' → M.supportCutoff S.C (σ' + 1) ≤ t →
      ∀ u ∈ honestActiveAt M S A x σ', u ∈ S.P.committee σ' →
      u ∈ A.activeThroughout x ((M.dutyWindowStart S.C σ' : ℕ) : ℝ) (((M.supportCutoff S.C (σ' + 1) : ℕ) : ℝ) + Δs))
    (hHoldP : ∀ s : ℕ, tAwakeEnd ≤ M.slotStart S.C s → M.supportCutoff S.C (s + 1) ≤ t → HonestOpenerAt M S A x s →
      S.P.proposer s ∈ A.activeThroughout x ((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) + Δs)) :
    RootCollisionAtOpening M S A x rs m ∨ RootCollisionHeldBy M S A x t ∨
      (FinalityIncludedBetween M S A x Δs tAwakeEnd t ∧
        FinalizedExtendedByHonestProposalsBetween M S A x Δs tAwakeEnd t) :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem98_healed_finality_liveness M F U Fx) S A x R
    GST tGAT tAwakeEnd m rs hGST E hNet hSkew hRedeliver E_F hNet_F hSkew_F Sy hΔs Sy_F hΔs_F hHoldF hParent hThird hAwake hActive t ht hTicksBy
    hCommittees hCommitteesTick hSeq hStay hOpenings hAdvQ hParam hDelF hTickInputs hHold hHoldC hHoldP

/-- **Lemma 98 with the sync fact.** The hypotheses of `lem98_healed_finality_liveness` with `hAttW`
in place of `hDelF`: after the phase, every honest active member of a round is still active from the
next round's proposal window start through one attestation sync delay after it; and `hHoldQ`: at every round after the phase whose next round's first slot is an honest round
opening slot, the next opener is active at every step at a real time from its proposal window's start to its
slot's start. The conclusion is
the same.

Why: `hDelF` from the sync fact, by `attestations_reach_opener_of_sync`: a round starting at or after
`tAwakeEnd` starts at least `4Δ(k + 1)` after `GST`, so the sync fact read at the next proposal
window's start delivers each attestation whose sender is active then, unless the next opener
already holds it, and synchrony from the send delivers one sent later.
`hAttW` is the clause the final review proposed for `FinalityWindowAt`, as a hypothesis.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- as `lem98_healed_finality_liveness`.

Read aloud: Lemma 98 holds when, after the phase, every honest active member of a round is still
active from the next round's proposal window start through one attestation sync delay after it, and each next opener
is active from its proposal window's start to its slot's start. -/
theorem lem98_healed_finality_liveness_ofSync (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd m : ℕ) (rs : ℕ → ℕ)
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
    (hHoldF : ∀ i, i < m → ∀ v, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (rs i * S.C.R + 1)) →
      v ∈ A.activeThroughout x ((max (M.dutyWindowStart S.C (rs i * S.C.R)) GST : ℕ) : ℝ)
        (((max (M.dutyWindowStart S.C (rs i * S.C.R)) GST : ℕ) : ℝ) + Δs_F))
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
    -- time at most `t` (; the sentence of's `hLastTick` at every slot, which it replaces)
    (hTicksBy : TicksToUpdatesBy M S x t)
    -- committee sleepiness from `anchorCW S tGAT`, for the slots whose update is at most `t`
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) t)
    -- every tick at a real time at most `t`, to a clock value `c`: committee sleepiness from `anchorCW S tGAT` read up
    -- to `c`
    (hCommitteesTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → (x.time k : ℝ) ≤ t →
      CommitteeSleepinessUntil M S A x (anchorCW S tGAT) c)
    (hSeq : HonestOpeningSeq M S A x rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    -- every updater of a slot from the first honest round opening slot `rs 0 * S.C.R` on, whose update is at
    -- most `t`, is active for the sync delay after the real time of its own tick to the support cutoff of the
    -- next slot
    (hStay : ∀ σ : ℕ, rs 0 * S.C.R ≤ σ → M.supportCutoff S.C (σ + 1) ≤ t → ∀ u ∈ updaterAt M S A x σ,
      u ∈ A.activeThroughout x (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))))
        (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))) + Δs))
    (hOpenings : OpeningsOutsideWaitsAndWindows S rs m)
    -- fewer than two thirds of the validators corrupted up to `t`
    (hAdvQ : A.AdversaryFewerThanTwoThirdsUntil x (validator_count V) t)
    -- the attestations of a round reach a proposer that woke at its proposal window's start, with room for its clock
    --
    (hParam : (Δ_F S : ℝ) + Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * (S.C.k + 1))
    -- after the phase, every honest active member of a round is still active from the next round's proposal
    -- window start through one attestation sync delay after it
    (hAttW : ∀ r' : ℕ, tAwakeEnd ≤ M.slotStart S.C (r' * S.C.R) → ∀ u ∈ honestActiveAt M S A x (r' * S.C.R),
      u ∈ A.activeThroughout x (M.proposalWindowStart S.C ((r' + 1) * S.C.R))
        ((M.proposalWindowStart S.C ((r' + 1) * S.C.R) : ℕ) + Δs_F))
    -- at every round after the phase whose next round's first slot is an honest round opening slot, the next opener is
    -- active at every step at a real time from its proposal window's start to its slot's start
    (hHoldQ : ∀ r' : ℕ, tAwakeEnd ≤ M.slotStart S.C (r' * S.C.R) → HonestOpenerAt M S A x ((r' + 1) * S.C.R) →
      S.P.proposer ((r' + 1) * S.C.R) ∈ A.activeThroughout x ((M.proposalWindowStart S.C ((r' + 1) * S.C.R) : ℕ) : ℝ)
        ((M.slotStart S.C ((r' + 1) * S.C.R) : ℕ) : ℝ))
    -- at every honest round opening slot after the phase, no block an honest active member of the round holds when it
    -- ticks to the round's action time includes an attestation put on the wire at a tick to that action time
    --
    (hTickInputs : ∀ r' : ℕ, tAwakeEnd ≤ M.slotStart S.C (r' * S.C.R) → HonestOpenerAt M S A x (r' * S.C.R) →
      ∀ v ∈ honestActiveAt M S A x (r' * S.C.R), ∀ Z ∈ (x.tickInput v (M.supportCutoff S.C (r' * S.C.R + 1))).tree,
      ∀ a ∈ Z.attestations, ∀ (j : ℕ) (w : V), x.lbl j = Event.tick w (M.supportCutoff S.C (r' * S.C.R + 1)) →
      (⟨w, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∉ x.sent (j + 1) - x.sent j)
    -- at every slot whose next slot starts at or after `tAwakeEnd` and whose update is at most `t`, the honest active
    -- committee members stay active for the sync delay after the time the synchronous delivery reads them (T-RC86-2,
    --
    (hHold : ∀ s' : ℕ, tAwakeEnd ≤ M.slotStart S.C (s' + 1) → M.supportCutoff S.C (s' + 1) ≤ t →
      ∀ u ∈ honestActiveAt M S A x s', u ∈ S.P.committee s' →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    -- every honest committee member of every slot starting at or after `tAwakeEnd` whose update is at most `t` is active
    -- from its duty window's start through the sync delay after that update; at every slot at or after `tAwakeEnd` with an
    -- honest opener whose update is at most `t`, its proposer through the sync delay after the slot's update
    --
    (hHoldC : ∀ σ' : ℕ, tAwakeEnd ≤ M.slotStart S.C σ' → M.supportCutoff S.C (σ' + 1) ≤ t →
      ∀ u ∈ honestActiveAt M S A x σ', u ∈ S.P.committee σ' →
      u ∈ A.activeThroughout x ((M.dutyWindowStart S.C σ' : ℕ) : ℝ) (((M.supportCutoff S.C (σ' + 1) : ℕ) : ℝ) + Δs))
    (hHoldP : ∀ s : ℕ, tAwakeEnd ≤ M.slotStart S.C s → M.supportCutoff S.C (s + 1) ≤ t → HonestOpenerAt M S A x s →
      S.P.proposer s ∈ A.activeThroughout x ((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) + Δs)) :
    RootCollisionAtOpening M S A x rs m ∨ RootCollisionHeldBy M S A x t ∨
      (FinalityIncludedBetween M S A x Δs tAwakeEnd t ∧
        FinalizedExtendedByHonestProposalsBetween M S A x Δs tAwakeEnd t) :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem98_healed_finality_liveness_ofSync M F U Fx) S A x R
    GST tGAT tAwakeEnd m rs hGST E hNet hSkew hRedeliver E_F hNet_F hSkew_F Sy hΔs Sy_F hΔs_F hHoldF hParent hThird hAwake hActive t ht hTicksBy
    hCommittees hCommitteesTick hSeq hStay hOpenings hAdvQ hParam hAttW hHoldQ hTickInputs hHold hHoldC hHoldP

/-- **Lemma 98 with the sync fact, for rounds of at most `k + 2` slots.** The hypotheses of
`lem98_healed_finality_liveness_ofSync` with
`hRk : 4ΔR + Δs_F + ΔClockAhead < 4Δ(k + 2) + Δ` in place of
`hAttW`. The conclusion is the same.

Why: `hAttW` from membership: by `hRk`, one attestation sync delay after the next round's proposal window start is
more than `ΔClockAhead` before the support cutoff of the round's first slot plus one, within the duties every
honest active member of that slot is active through.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- as `lem98_healed_finality_liveness`.

Read aloud: Lemma 98 holds with the sync fact alone when a round, plus the attestation sync delay and the
clock-ahead bound, is shorter than `k + 2` slots plus one delay, and each next opener is active from its proposal
window's start to its slot's start. -/
theorem lem98_healed_finality_liveness_ofSync_of_R_le (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd m : ℕ) (rs : ℕ → ℕ)
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
    (hHoldF : ∀ i, i < m → ∀ v, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (rs i * S.C.R + 1)) →
      v ∈ A.activeThroughout x ((max (M.dutyWindowStart S.C (rs i * S.C.R)) GST : ℕ) : ℝ)
        (((max (M.dutyWindowStart S.C (rs i * S.C.R)) GST : ℕ) : ℝ) + Δs_F))
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
    -- time at most `t` (; the sentence of's `hLastTick` at every slot, which it replaces)
    (hTicksBy : TicksToUpdatesBy M S x t)
    -- committee sleepiness from `anchorCW S tGAT`, for the slots whose update is at most `t`
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) t)
    -- every tick at a real time at most `t`, to a clock value `c`: committee sleepiness from `anchorCW S tGAT` read up
    -- to `c`
    (hCommitteesTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → (x.time k : ℝ) ≤ t →
      CommitteeSleepinessUntil M S A x (anchorCW S tGAT) c)
    (hSeq : HonestOpeningSeq M S A x rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    -- every updater of a slot from the first honest round opening slot `rs 0 * S.C.R` on, whose update is at
    -- most `t`, is active for the sync delay after the real time of its own tick to the support cutoff of the
    -- next slot
    (hStay : ∀ σ : ℕ, rs 0 * S.C.R ≤ σ → M.supportCutoff S.C (σ + 1) ≤ t → ∀ u ∈ updaterAt M S A x σ,
      u ∈ A.activeThroughout x (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))))
        (x.time (x.tickStep u (M.supportCutoff S.C (σ + 1))) + Δs))
    (hOpenings : OpeningsOutsideWaitsAndWindows S rs m)
    -- fewer than two thirds of the validators corrupted up to `t`
    (hAdvQ : A.AdversaryFewerThanTwoThirdsUntil x (validator_count V) t)
    -- the attestations of a round reach a proposer that woke at its proposal window's start, with room for its clock
    --
    (hParam : (Δ_F S : ℝ) + Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * (S.C.k + 1))
    -- a round's length in time, plus the attestation sync delay and the clock-ahead bound, is less than `k + 2` slots plus
    -- one delay (, strict by the delegation)
    (hRk : (4 * Δ S * S.C.R : ℝ) + Δs_F + ΔClockAhead < 4 * Δ S * (S.C.k + 2) + Δ S)
    -- at every round after the phase whose next round's first slot is an honest round opening slot, the next opener is
    -- active at every step at a real time from its proposal window's start to its slot's start
    (hHoldQ : ∀ r' : ℕ, tAwakeEnd ≤ M.slotStart S.C (r' * S.C.R) → HonestOpenerAt M S A x ((r' + 1) * S.C.R) →
      S.P.proposer ((r' + 1) * S.C.R) ∈ A.activeThroughout x ((M.proposalWindowStart S.C ((r' + 1) * S.C.R) : ℕ) : ℝ)
        ((M.slotStart S.C ((r' + 1) * S.C.R) : ℕ) : ℝ))
    -- at every honest round opening slot after the phase, no block an honest active member of the round holds when it
    -- ticks to the round's action time includes an attestation put on the wire at a tick to that action time
    --
    (hTickInputs : ∀ r' : ℕ, tAwakeEnd ≤ M.slotStart S.C (r' * S.C.R) → HonestOpenerAt M S A x (r' * S.C.R) →
      ∀ v ∈ honestActiveAt M S A x (r' * S.C.R), ∀ Z ∈ (x.tickInput v (M.supportCutoff S.C (r' * S.C.R + 1))).tree,
      ∀ a ∈ Z.attestations, ∀ (j : ℕ) (w : V), x.lbl j = Event.tick w (M.supportCutoff S.C (r' * S.C.R + 1)) →
      (⟨w, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∉ x.sent (j + 1) - x.sent j)
    -- at every slot whose next slot starts at or after `tAwakeEnd` and whose update is at most `t`, the honest active
    -- committee members stay active for the sync delay after the time the synchronous delivery reads them (T-RC86-2,
    --
    (hHold : ∀ s' : ℕ, tAwakeEnd ≤ M.slotStart S.C (s' + 1) → M.supportCutoff S.C (s' + 1) ≤ t →
      ∀ u ∈ honestActiveAt M S A x s', u ∈ S.P.committee s' →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C s' - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    -- every honest committee member of every slot starting at or after `tAwakeEnd` whose update is at most `t` is active
    -- from its duty window's start through the sync delay after that update; at every slot at or after `tAwakeEnd` with an
    -- honest opener whose update is at most `t`, its proposer through the sync delay after the slot's update
    --
    (hHoldC : ∀ σ' : ℕ, tAwakeEnd ≤ M.slotStart S.C σ' → M.supportCutoff S.C (σ' + 1) ≤ t →
      ∀ u ∈ honestActiveAt M S A x σ', u ∈ S.P.committee σ' →
      u ∈ A.activeThroughout x ((M.dutyWindowStart S.C σ' : ℕ) : ℝ) (((M.supportCutoff S.C (σ' + 1) : ℕ) : ℝ) + Δs))
    (hHoldP : ∀ s : ℕ, tAwakeEnd ≤ M.slotStart S.C s → M.supportCutoff S.C (s + 1) ≤ t → HonestOpenerAt M S A x s →
      S.P.proposer s ∈ A.activeThroughout x ((M.slotStart S.C s - max (Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C (s + 1) : ℕ) : ℝ) + Δs)) :
    RootCollisionAtOpening M S A x rs m ∨ RootCollisionHeldBy M S A x t ∨
      (FinalityIncludedBetween M S A x Δs tAwakeEnd t ∧
        FinalizedExtendedByHonestProposalsBetween M S A x Δs tAwakeEnd t) :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem98_healed_finality_liveness_ofSync_of_R_le M F U Fx) S A x R
    GST tGAT tAwakeEnd m rs hGST E hNet hSkew hRedeliver E_F hNet_F hSkew_F Sy hΔs Sy_F hΔs_F hHoldF hParent hThird hAwake hActive t ht hTicksBy
    hCommittees hCommitteesTick hSeq hStay hOpenings hAdvQ hParam hRk hHoldQ hTickInputs hHold hHoldC hHoldP

end GoldilocksCorrectness.Record.Statements.Executions

