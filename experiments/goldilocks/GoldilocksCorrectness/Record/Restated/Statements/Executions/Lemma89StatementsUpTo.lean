module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89HandoverVFUpTo
public import GoldilocksCorrectness.Statements.Executions.Lemma89Statements
public import GoldilocksCorrectness.Statements.Executions.AsyncDeliveryStatements
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Lemma89StatementsUpTo, over a model

The statements of `GoldilocksCorrectness/Statements/Executions/Lemma89StatementsUpTo.lean`, over a
model `M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: Lemma 89 of record
(`lem89_phase`), restated with `SynchronyFromWakeUpTo` and `CatchUpOnWakeUpTo` at a bound on the
deadlines. Each is a one-line call of its proof page's twin of the same name, under
`Record/Restated/Proofs/Executions/`. the catch-up vocabulary stays for phase E's bridge.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ Δ_F slotStart voteTime supportCutoff anchorCW)

namespace GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDeliveryUpTo SyncedWithinUpTo)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor hMax le_hMax IsEntry VoterTreeAt JustifiedInTree AnchorAt)
open GoldilocksCorrectness.Record.Statements.Routines (ProgressCertOn TreeClosed)
open GoldilocksCorrectness.Statements.Executions (OpeningsOutsideWaitsAndWindows OutsideSpans
  Vocab.goldilocks acObject fgObject healFrontSlots)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Statements.Routines (expireLocks)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- **Lemma 89 of record: the events of the phase.** Under the phase's
premises and nine honest round opening slots outside every two spans of `δt` slots and five spans
of `k + 2` slots (`OpeningsOutsideWaitsAndWindows`, `PhaseDefs.lean`): either some honest round opening slot's
proposal has the root of a block its proposer held, or some opening `j < m` is the healed round: its
first slot `s₀` and proposal `B₀`, of slot `s₀`; the slot invariant restricted to `B₀` at `s₀` over
the honest active validators of `s₀`; every updater of `s₀` saved `B₀`; every honest attestation
sent before the round's action time has height at most `h(B₀)`; at every slot `s` with
`s₀ < s < s_m`, every member of `roundMembers M S Sched (s + 1)` has its frame on the honest chain
before `s`; every validator that ticks to the vote time of slot `s_m`, honest at that tick, has in the state
the tick reads its caches on
the honest chain with `h_j > h(B₀)`; and every validator `w` outside the adversary set at the
vote time of slot `s_m` has its frame before that vote time on the honest chain before `s_m`
. Here `s_m := rs m * R`, the
first slot of the last opening.

Why the clause: the phase still runs at the vote time of slot `s_m` (its support cutoff is at most
`tAwakeEnd`, `HonestOpeningSeq.last`), so the phase's line invariant gives the voter frame there
(`PartAHyps.voterFrame_at_last_opening`); nothing after the hand-over reaches that time, the
caches being known only from each validator's tick to that vote time on.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the times;
  `m`, `rs`: the index of the last honest round opening slot and the rounds of the honest round opening slots.

Why: the climb `climb_to_fast_block` and the hand-over's copy with the voter frame
`handover_after_fast_block_vf` (part A's assembly is not needed: the hand-over reads the line
invariant directly).

Roots name blocks until `M.supportCutoff S.C (rs m * S.C.R)`: the hand-over's copy
(`handover_after_fast_block_vf`); the climb reads up to `aR M S (rs (m - 1))`, before it.

Read aloud: the conclusion of Lemma 89, and the voter frame at the last opening's slot.



Restated with the delivery premises up to `M.supportCutoff S.C (rs m * S.C.R)`: the bound of its
roots `hRoots`, for the votes (`hSync`, `hCatch`); the attestations (`hSyncF`, `hCatchF`) up to
`M.slotStart S.C (rs m * S.C.R)`, the bounds of its proof
`(GoldilocksCorrectness.Record.Proofs.Executions.lem89_phase_upTo M F U Fx)`. -/
theorem lem89_phase_upTo (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd m : ℕ) (rs : ℕ → ℕ)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.supportCutoff S.C (rs m * S.C.R))) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST (M.supportCutoff S.C (rs m * S.C.R)))
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    {ΔNet_F : ℕ} (E_F : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks (M.slotStart S.C (rs m * S.C.R))) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S) {Δs_F : ℕ}
    (Sy_F : SyncedWithinUpTo A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST (M.slotStart S.C (rs m * S.C.R)))
    (hΔs_F : (Δs_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S ∨ (Δs_F : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind ≤ 4 * Δ S * S.C.k)
    -- for each honest round opening slot, every validator outside the adversary set at the support cutoff of the slot
    -- after its first slot is active through the attestations' sync delay after the later of that first slot's duty
    -- window's start and `GST`
    (hHoldF : ∀ i, i < m → ∀ v, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (rs i * S.C.R + 1)) →
      v ∈ A.activeThroughout x ((max (M.dutyWindowStart S.C (rs i * S.C.R)) GST : ℕ) : ℝ)
        (((max (M.dutyWindowStart S.C (rs i * S.C.R)) GST : ℕ) : ℝ) + Δs_F))
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C (rs m * S.C.R)))
    -- roots name blocks up to the real time of every tick to a clock value at most the support cutoff of slot
    -- `rs m * R` (, stops_recheck_85)
    (hRootsTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (rs m * S.C.R) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST ≤ tGAT)
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    -- at every slot of the phase, every validator honest at the slot's update is an honest active validator and an
    -- updater of the slot
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    (hCommittees : CommitteeSleepinessUntil M S A x (anchorCW S tGAT) tAwakeEnd)
    (hSeq : HonestOpeningSeq M S A x rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    -- every tick to a clock value at most the support cutoff of slot `rs m * R` is at a real time at most
    -- `tAwakeEnd` (, stops_recheck_85)
    (hEndTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (rs m * S.C.R) →
      x.time k ≤ tAwakeEnd)
    (hm : OpeningsOutsideWaitsAndWindows S rs m) :
    RootCollisionAtOpening M S A x rs m ∨
    (∃ (j s₀ : ℕ) (B₀ : Block V),
      j < m ∧ s₀ = rs j * S.C.R ∧
      HonestChainExtends M S A x (honestActiveAt M S A x s₀) B₀ s₀ ∧
      (∀ u ∈ updaterAt M S A x s₀,
        (x.tickOutput u (M.supportCutoff S.C (s₀ + 1))).savedConfirmation s₀ = some B₀) ∧
      B₀.slot = s₀ ∧
      OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) (M.chainStateOf S.C B₀).h ∧
      (∀ s : ℕ, s₀ < s → s < rs m * S.C.R →
        (∀ w ∈ roundMembers M S A x (s + 1), VoterFrameOnChainAt M S A x s₀ s w) ∧
        (∀ v ∈ updaterAt M S A x s, UpdaterFinalizedOnChainAt M S A x s₀ s v)) ∧
      (∀ u : V, x.lbl (x.tickStep u (M.voteTime S.C (rs m * S.C.R))) = Event.tick u (M.voteTime S.C (rs m * S.C.R)) →
        u ∉ A.corruptedAtTime x (x.time (x.tickStep u (M.voteTime S.C (rs m * S.C.R)))) →
        CachesOnChain M S A x s₀ (M.chainStateOf S.C B₀).h (x.tickInput u (M.voteTime S.C (rs m * S.C.R)))) ∧
      (∀ w : V, w ∉ A.corruptedAtTime x (M.voteTime S.C (rs m * S.C.R)) →
        VoterFrameOnChainAt M S A x s₀ (rs m * S.C.R) w)) :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem89_phase_upTo M F) U Fx S A x R GST tGAT tAwakeEnd m rs E hNet hSkew hRedeliver
    Sy hΔs E_F hNet_F hSkew_F Sy_F hΔs_F hHoldF hRoots hRootsTick hParent hGST hThird hAwake hActive hCommittees hSeq hEndTick hm

end GoldilocksCorrectness.Record.Statements.Executions

