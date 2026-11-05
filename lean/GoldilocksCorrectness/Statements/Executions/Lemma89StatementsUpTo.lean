module
public import GoldilocksCorrectness.Statements.Executions.Lemma89Statements
public import GoldilocksCorrectness.Statements.Executions.AsyncDeliveryStatements
public import GoldilocksCorrectness.Proofs.Executions.Lemma89HandoverVFUpTo

@[expose] public section

/-!
# `Lemma89Statements.lean` with the delivery premises up to a bound

The theorems of `GoldilocksCorrectness/Statements/Executions/Lemma89Statements.lean` that name a
delivery premise, restated with `SynchronyFromWakeUpTo` and `CatchUpOnWakeUpTo` at a bound on the
deadlines. The bound of
each twin is the latest ordinary deadline `max t GST + Δ` of a send its proof reads, written in
the twin's own parameters.

* `lem89_phase`

No `axiom`, no `native_decide`, no `sorry`. The landed page is imported, never edited.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ Δ_F slotStart voteTime supportCutoff anchorCW)

open GoldilocksCorrectness.Statements.Routines (chainStateOf)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Routines (expireLocks ProgressCertOn)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
open GoldilocksCorrectness.Statements.Routines (JustificationCertOn)

/-- **Lemma 89 of record: the events of the phase.** Under the phase's
premises and nine honest round opening slots outside every two spans of `δt` slots and five spans
of `k + 2` slots (`OpeningsOutsideWaitsAndWindows`, `PhaseDefs.lean`): either some honest round opening slot's proposal has
the root of a block its proposer held, or some opening `j < m` is the healed round: its first slot
`s₀` and proposal `B₀`, of slot `s₀`; the slot invariant restricted to `B₀` at `s₀` over the
honest active validators of `s₀`; every updater of `s₀` saved `B₀`; every honest attestation sent
before the round's action time has height at most `h(B₀)`; at every slot `s` with
`s₀ < s < s_m`, every member of `roundMembers S Sched (s + 1)` has its frame on the honest chain
before `s`; at the step `i₁` at the vote time of slot `s_m`, every honest validator's caches are on
the honest chain with `h_j > h(B₀)`; and every validator `w` outside the adversary set at the
vote time of slot `s_m` has its frame before that vote time on the honest chain before `s_m`
. Here `s_m := rs m * R`, the
first slot of the last opening.

Why the clause: the phase still runs at the vote time of slot `s_m` (its support cutoff is at most
`tAwakeEnd`, `HonestOpeningSeq.last`), so the phase's line invariant gives the voter frame there
(`PartAHyps.voterFrame_at_last_opening`); nothing after the hand-over reaches that time, the
caches being known only from `i₁` on.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the times;
  `m`, `rs`: the index of the last honest round opening slot and the rounds of the honest round opening slots.

Why: the climb `climb_to_fast_block` and the hand-over's copy with the voter frame
`handover_after_fast_block_vf` (part A's assembly is not needed: the hand-over reads the line
invariant directly).

Roots name blocks until `supportCutoff S (rs m * S.C.R)`: the hand-over's copy
(`handover_after_fast_block_vf`); the climb reads up to `aR S (rs (m - 1))`, before it.

Read aloud: the conclusion of Lemma 89, and the voter frame at the last opening's slot.



Restated with the delivery premises up to `supportCutoff S (rs m * S.C.R)`: the bound of its roots `hRoots`, for the votes (`hSync`, `hCatch`); the attestations (`hSyncF`, `hCatchF`) up to `slotStart S (rs m * S.C.R)`, the bounds of its proof `GoldilocksCorrectness.Proofs.Executions.lem89_phase_upTo`. -/
theorem lem89_phase_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd m : ℕ) (rs : ℕ → ℕ)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S (rs m * S.C.R)))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S (rs m * S.C.R)))
    (hSyncF : SynchronyFromWakeUpTo S Sched x (Δ_F S) GST fgObject (slotStart S (rs m * S.C.R)))
    (hCatchF : CatchUpOnWakeUpTo S Sched x (Δ_F S) GST fgObject (slotStart S (rs m * S.C.R)))
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (rs m * S.C.R)))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hGST : GST ≤ tGAT)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ u : V, u ∉ Sched.adv (t : Int) → u ∈ Sched.awake (t : Int))
    (hCommittees : CommitteeSleepiness S Sched (anchorCW S tGAT))
    (hSeq : HonestOpeningSeq S Sched rs m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hm : OpeningsOutsideWaitsAndWindows S rs m) :
    RootCollisionAtOpening S Sched x rs m ∨
    (∃ (j s₀ i₁ : ℕ) (B₀ : Block V),
      j < m ∧ s₀ = rs j * S.C.R ∧ x[i₁].time = voteTime S (rs m * S.C.R) ∧
      HonestChainExtends S Sched x (honestActiveAt S Sched s₀) B₀ s₀ ∧
      (∀ u ∈ updaterAt S Sched s₀,
        (stateBefore x (supportCutoff S (s₀ + 1) + 1) u).A.saved_confirmation s₀ = some B₀) ∧
      B₀.slot = s₀ ∧
      OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) (chainStateOf S.C B₀).h ∧
      (∀ s : ℕ, s₀ < s → s < rs m * S.C.R →
        ∀ w ∈ roundMembers S Sched (s + 1),
          VoterFrameOnChainAt S Sched x s₀ s w ∧ UpdaterFinalizedOnChainAt S Sched x s₀ s w) ∧
      (∀ u : V, u ∉ Sched.adv (x[i₁].time : Int) →
        CachesOnChain S Sched x s₀ (chainStateOf S.C B₀).h (x[i₁][u].st)) ∧
      (∀ w : V, w ∉ Sched.adv ((voteTime S (rs m * S.C.R) : ℕ) : Int) →
        VoterFrameOnChainAt S Sched x s₀ (rs m * S.C.R) w)) :=
  GoldilocksCorrectness.Proofs.Executions.lem89_phase_upTo S Sched x GST tGAT tAwakeEnd m rs hDiv
    hMono hSync hCatch hSyncF hCatchF hRoots hParent hOwner hU hGST hThird hAwake hCommittees
    hSeq hm

end GoldilocksCorrectness.Statements.Executions

