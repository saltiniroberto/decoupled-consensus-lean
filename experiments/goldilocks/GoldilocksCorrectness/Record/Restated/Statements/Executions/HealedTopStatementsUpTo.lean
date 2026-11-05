module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.HealedTopUpTo
public import GoldilocksCorrectness.Statements.Executions.AsyncDeliveryStatements
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# HealedTopStatementsUpTo, over a model

The statements of `GoldilocksCorrectness/Statements/Executions/HealedTopStatementsUpTo.lean`, over a
model `M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: the facts after the
hand-over for the readings up to a time `t`, restated with `SynchronyFromWakeUpTo` and
`CatchUpOnWakeUpTo` at a bound on the deadlines. Each is a one-line call of its proof page's twin of
the same name, under `Record/Restated/Proofs/Executions/`. the catch-up vocabulary stays for phase E's bridge.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

open GoldilocksCorrectness.Statements.Routines (Δ Δ_F slotStart voteTime supportCutoff anchorCW)

namespace GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDeliveryUpTo SyncedWithinUpTo)
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
caches stay on it up to `t`.

Among the times: every validator's tick to the healed slot's update is before `i₂`; every slot starting at or after `tAwakeEnd` starts after the time of `i₂`, and so does every
validator's tick to its start; the healed slot `s₀` is at or after the first honest round opening slot `r 0 * S.C.R`.

Restated with the delivery premises up to `b`: the conclusion gains the upper end `t ≤ b`, and at
such a `t` its proof reads deliveries due by `t`; the attestations (`hSyncF`, `hCatchF`) up to
`M.slotStart S.C (r m * S.C.R)`, the bound of `lem89_phase_upTo`. -/
theorem healed_handover_facts_until_upTo (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd m : ℕ) (r : ℕ → ℕ)
    (hGST : GST ≤ tGAT)
     {b : ℕ}
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks b) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST b)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    {ΔNet_F : ℕ} (E_F : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.slotStart S.C (r m * S.C.R))) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S) {Δs_F : ℕ}
    (Sy_F : SyncedWithinUpTo A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST (M.slotStart S.C (r m * S.C.R)))
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
    t ≤ b →
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
  (GoldilocksCorrectness.Record.Proofs.Executions.healed_handover_facts_until_upTo M F) U Fx S A x R GST tGAT
    tAwakeEnd m r hGST E hNet hSkew hRedeliver Sy hΔs E_F hNet_F hSkew_F Sy_F hΔs_F hHoldF hParent hThird hAwake hActive t ht hCommittees hCommitteesTick hStay hSeq hOpenings hAdvQ

end GoldilocksCorrectness.Record.Statements.Executions

