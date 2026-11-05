module
public import GoldilocksCorrectness.Proofs.Executions.Lemma89HandoverVF
public import GoldilocksCorrectness.Proofs.Executions.Lemma89Count
public import GoldilocksCorrectness.Proofs.Executions.HealedVoterFrame
public import GoldilocksCorrectness.Proofs.Executions.HealedChainBefore
public import GoldilocksCorrectness.Proofs.Executions.Lemma90Inclusion
public import GoldilocksCorrectness.Proofs.Executions.Lemma85
public import GoldilocksCorrectness.Proofs.Executions.Unforgeability
public import GoldilocksCorrectness.Proofs.Executions.HonestProposalExtension

@[expose] public section

/-!
# The frames after the healed slot, the facts after the hand-over, Lemmas 86 and 90

The proofs of the facts stated in
`GoldilocksCorrectness/Statements/Executions/HealedTopStatements.lean`:

- `frames_after_healed_slot`: the frames at every slot after the healed slot, by strong induction
  on the slot;
- `healed_handover_facts`: either the collision, or the healed slot with the facts every later
  lemma reads;
- `lem86_healed_finality_safety`: Lemma 86, finality safety after healing;
- `lem90_healed_confirmed`: Lemma 90, the confirmed tip after healing.


-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ Δ_F slotStart voteTime supportCutoff
  dutyWindowStart anchorCW)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_of_anchor one_le_Δ slotStart_eq
  slotStart_mono supportCutoff_eq supportCutoff_mono viewFreeze_eq voteTime_eq voteTime_mono
  voteTime_succ)

open GoldilocksCorrectness.Statements.Routines (chainStateOf)

open GoldilocksCorrectness.Proofs.Routines (anchorCW_eq slot_after_healed_round)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

-- An index `x[i]` into an execution has the valid-index predicate `fun _ _ => True`; this rule,
-- local to the file, proves it at once.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-! ## The frames at every slot after the healed slot -/

/-- **The frames at every slot after the healed slot.** The proof; the audited statement is in
`Statements/Executions/HealedTopStatements.lean`. Why: by strong induction on the slot `s > s₀`.
For `s < s_m`, Lemma 89's frames at `roundMembers S Sched (s + 1)`, which contains the honest
active validators and the updaters of `s`. For `s ≥ s_m`, the frames at the slots before `s` give
`ConfirmationsChainBefore S Sched x s₀ s` (`lem81_chain_before`); then the voter frame at `s_m` is
Lemma 89's clause, the voter frame at `s > s_m` is `voterFrame_after_handover`, and the updater
frame at `s ≥ s_m` is `updaterFrame_after_handover`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `s_m`: the last honest round opening slot; `i₂`:
  the step from which the caches are on the chain; `H`: the threshold; `anchor`: the time from
  which committee sleepiness holds; `t`: the bound on the slots' update times; `B₀`: the block
  every updater of slot `s₀` saved.

Roots name blocks until `t`: the conclusions are for the slots `s` whose update, at the support
cutoff of slot `s + 1`, is at most `t`; at such a slot the proof reads `lem81_chain_before` up to
the support cutoff of slot `s`, `voterFrame_after_handover` up to the vote time of slot `s` and
`updaterFrame_after_handover` up to the support cutoff of slot `s + 1`.

Caches up to `t`: at a slot `s` the proof reads the caches up to the support cutoff of slot `s + 1`,
at most `t` (`voterFrame_after_handover_until`, `updaterFrame_after_handover_until`). -/
theorem frames_after_healed_slot_until (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ s_m i₂ H anchor t : ℕ) (B₀ : Block V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x t)
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hGST : GST ≤ voteTime S s₀)
    (hSleepK : CommitteeSleepiness S Sched anchor) (hAnchor : anchor ≤ slotStart S (s₀ + 1))
    (hB₀slot : s₀ ≤ B₀.slot)
    (hBase : HonestChainExtends S Sched x (honestActiveAt S Sched s₀) B₀ s₀)
    (hBaseSaved : ∀ v ∈ updaterAt S Sched s₀,
      (stateBefore x (supportCutoff S (s₀ + 1) + 1) v).A.saved_confirmation s₀ = some B₀)
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hi₂ : x[i₂].time = voteTime S s_m + 1)
    (hCaches : ∀ (j : ℕ) (u : V), x[i₂].time ≤ x[j].time → x[j].time ≤ t →
      u ∉ Sched.adv (x[j].time : Int) → CachesOnChain S Sched x s₀ H (x[j][u].st))
    (hPhase : ∀ s : ℕ, s₀ < s → s < s_m → ∀ w ∈ roundMembers S Sched (s + 1),
      VoterFrameOnChainAt S Sched x s₀ s w ∧ UpdaterFinalizedOnChainAt S Sched x s₀ s w)
    (hLast : ∀ w : V, w ∉ Sched.adv ((voteTime S s_m : ℕ) : Int) →
      VoterFrameOnChainAt S Sched x s₀ s_m w) :
    (∀ s : ℕ, s₀ < s → supportCutoff S (s + 1) ≤ t →
      ∀ w ∈ honestActiveAt S Sched s, VoterFrameOnChainAt S Sched x s₀ s w) ∧
    (∀ s : ℕ, s₀ < s → supportCutoff S (s + 1) ≤ t →
      ∀ v ∈ updaterAt S Sched s, UpdaterFinalizedOnChainAt S Sched x s₀ s v) := by
  have hΔ := one_le_Δ S
  have key : ∀ s : ℕ, s₀ < s → supportCutoff S (s + 1) ≤ t →
      (∀ w ∈ honestActiveAt S Sched s, VoterFrameOnChainAt S Sched x s₀ s w) ∧
      (∀ v ∈ updaterAt S Sched s, UpdaterFinalizedOnChainAt S Sched x s₀ s v) := by
    intro s
    induction s using Nat.strong_induction_on with
    | _ s ih =>
      intro hs hst
      -- the times the proof reads at slot `s`, all at most `t`
      have hcs : supportCutoff S s ≤ t := le_trans (supportCutoff_mono S (Nat.le_succ s)) hst
      have hvs : voteTime S s ≤ t := by
        have := supportCutoff_eq S s
        omega
      have hlt' : ∀ s' : ℕ, s' < s → supportCutoff S (s' + 1) ≤ t :=
        fun s' h => le_trans (supportCutoff_mono S h) hcs
      rcases Nat.lt_or_ge s s_m with hlt | hge
      · -- before the last opening: Lemma 89's frames at the round's members
        refine ⟨fun w hw => (hPhase s hs hlt w ?_).1, fun v hv => (hPhase s hs hlt v ?_).2⟩
        · unfold roundMembers
          unfold honestActiveAt at hw
          exact Finset.mem_sdiff.2 ⟨Finset.mem_univ _, (Finset.mem_sdiff.1 hw).2⟩
        · unfold roundMembers
          unfold updaterAt at hv
          exact Finset.mem_sdiff.2 ⟨Finset.mem_univ _, (Finset.mem_sdiff.1 hv).2⟩
      · -- from the last opening on: the chain before `s`, from the frames before `s`
        have hChain : ConfirmationsChainBefore S Sched x s₀ s :=
          Proofs.Executions.lem81_chain_before S Sched x GST s₀ anchor s B₀ hDiv hMono hSync
            hCatch (hRoots.mono hcs) hParent hOwner hGST hSleepK hAnchor hB₀slot hBase
            hBaseSaved
            (fun s' h1 h2 w hw => (ih s' h2 h1 (hlt' s' h2)).1 w hw)
            (fun s' h1 h2 v hv => (ih s' h2 h1 (hlt' s' h2)).2 v hv)
        refine ⟨fun w hw => ?_, fun v hv => ?_⟩
        · rcases Nat.eq_or_lt_of_le hge with heq | hgt
          · -- at the last opening's slot: Lemma 89's added clause
            subst heq
            refine hLast w (fun ha => (Finset.mem_sdiff.1 hw).2 (hMono _ _ ?_ ha))
            have h1 : voteTime S s_m ≤ supportCutoff S (s_m + 1) := by
              rw [supportCutoff_eq, voteTime_succ]
              omega
            exact_mod_cast h1
          · -- after it: the voter frame after the hand-over
            refine Proofs.Executions.voterFrame_after_handover_until S Sched x GST s₀ i₂ H s w
              hDiv hMono hSync hCatch (hRoots.mono hvs) hParent hU hAdvQ hGST hOld
              (fun j u h₁ h₂ h₃ => hCaches j u h₁ (le_trans h₂ hvs) h₃) ?_ hChain hw
            have h1 : 4 * Δ S * s_m ≤ 4 * Δ S * (s - 1) := Nat.mul_le_mul_left _ (by omega)
            rw [hi₂, voteTime_eq, viewFreeze_eq, slotStart_eq, slotStart_eq]
            omega
        · -- the updater frame after the hand-over
          refine Proofs.Executions.updaterFrame_after_handover_until S Sched x s₀ i₂ H s v hDiv
            hMono (hRoots.mono hst) hU hAdvQ hOld
            (fun j u h₁ h₂ h₃ => hCaches j u h₁ (le_trans h₂ hst) h₃) ?_ hChain hv
          have h1 : voteTime S s_m ≤ voteTime S s := voteTime_mono S hge
          have h2 : voteTime S (s + 1) = voteTime S s + 4 * Δ S := voteTime_succ S s
          rw [hi₂, supportCutoff_eq, h2]
          omega
  exact ⟨fun s hs hst => (key s hs hst).1, fun s hs hst => (key s hs hst).2⟩

/-- **The frames at every slot after the healed slot.** The proof; the audited statement is in
`Statements/Executions/HealedTopStatements.lean`. Why: by strong induction on the slot `s > s₀`.
For `s < s_m`, Lemma 89's frames at `roundMembers S Sched (s + 1)`, which contains the honest
active validators and the updaters of `s`. For `s ≥ s_m`, the frames at the slots before `s` give
`ConfirmationsChainBefore S Sched x s₀ s` (`lem81_chain_before`); then the voter frame at `s_m` is
Lemma 89's clause, the voter frame at `s > s_m` is `voterFrame_after_handover`, and the updater
frame at `s ≥ s_m` is `updaterFrame_after_handover`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `s_m`: the last honest round opening slot; `i₂`:
  the step from which the caches are on the chain; `H`: the threshold; `anchor`: the time from
  which committee sleepiness holds; `t`: the bound on the slots' update times; `B₀`: the block
  every updater of slot `s₀` saved.

Roots name blocks until `t`: the conclusions are for the slots `s` whose update, at the support
cutoff of slot `s + 1`, is at most `t`; at such a slot the proof reads `lem81_chain_before` up to
the support cutoff of slot `s`, `voterFrame_after_handover` up to the vote time of slot `s` and
`updaterFrame_after_handover` up to the support cutoff of slot `s + 1`.

It is `frames_after_healed_slot_until` with the caches restricted to the steps it reads. -/
theorem frames_after_healed_slot (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ s_m i₂ H anchor t : ℕ) (B₀ : Block V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x t)
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hGST : GST ≤ voteTime S s₀)
    (hSleepK : CommitteeSleepiness S Sched anchor) (hAnchor : anchor ≤ slotStart S (s₀ + 1))
    (hB₀slot : s₀ ≤ B₀.slot)
    (hBase : HonestChainExtends S Sched x (honestActiveAt S Sched s₀) B₀ s₀)
    (hBaseSaved : ∀ v ∈ updaterAt S Sched s₀,
      (stateBefore x (supportCutoff S (s₀ + 1) + 1) v).A.saved_confirmation s₀ = some B₀)
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hi₂ : x[i₂].time = voteTime S s_m + 1)
    (hCaches : ∀ (j : ℕ) (u : V), x[i₂].time ≤ x[j].time → u ∉ Sched.adv (x[j].time : Int) →
      CachesOnChain S Sched x s₀ H (x[j][u].st))
    (hPhase : ∀ s : ℕ, s₀ < s → s < s_m → ∀ w ∈ roundMembers S Sched (s + 1),
      VoterFrameOnChainAt S Sched x s₀ s w ∧ UpdaterFinalizedOnChainAt S Sched x s₀ s w)
    (hLast : ∀ w : V, w ∉ Sched.adv ((voteTime S s_m : ℕ) : Int) →
      VoterFrameOnChainAt S Sched x s₀ s_m w) :
    (∀ s : ℕ, s₀ < s → supportCutoff S (s + 1) ≤ t →
      ∀ w ∈ honestActiveAt S Sched s, VoterFrameOnChainAt S Sched x s₀ s w) ∧
    (∀ s : ℕ, s₀ < s → supportCutoff S (s + 1) ≤ t →
      ∀ v ∈ updaterAt S Sched s, UpdaterFinalizedOnChainAt S Sched x s₀ s v) :=
  frames_after_healed_slot_until S Sched x GST s₀ s_m i₂ H anchor t B₀ hDiv hMono hSync hCatch
    hRoots hParent hOwner hU hAdvQ hGST hSleepK hAnchor hB₀slot hBase hBaseSaved hOld hi₂
    (fun j u h₁ _ h₂ => hCaches j u h₁ h₂) hPhase hLast

/-! ## The facts after the hand-over -/

/-- **The facts after the hand-over.** The proof; the audited statement is in
`Statements/Executions/HealedTopStatements.lean`. Why: Lemma 89, with the voter frame at the last
opening's slot (`lem89_phase`), gives the collision, or the healed opening `j < m` with its
slot `s₀`, its block `B₀`, the base facts, the frames for `s₀ < s < s_m` and at `s_m`, and the
caches at the step `i₁` at the vote time of slot `s_m`; the caches from the step `i₂` one time
unit later (`caches_after_handover`); the times by arithmetic on the opening sequence; the updaters
of `s₀` from `hAwake`; the frames at every slot after `s₀` (`frames_after_healed_slot`); and the
chain from Lemma 81.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the
  times; `m`, `r`: the index of the last honest round opening slot and the rounds of the honest round opening slots. -/
theorem healed_handover_facts (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd m : ℕ) (r : ℕ → ℕ)
    (hGST : GST ≤ tGAT)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hSyncF : SynchronyFromWake Sched x.toTrace (Δ_F S) GST fgObject)
    (hCatchF : CatchUpOnWake Sched x.toTrace (Δ_F S) GST fgObject)
    (hRoots : RootsNameBlocks S Sched x)
    (hParent : ParentHeldAtDelivery S Sched x) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ v : V, v ∉ Sched.adv (t : Int) → v ∈ Sched.awake (t : Int))
    (hCommittees : CommitteeSleepiness S Sched (anchorCW S tGAT))
    (hSeq : HonestOpeningSeq S Sched r m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hOpenings : OpeningsOutsideWaitsAndWindows S r m)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t) :
    RootCollisionAtOpening S Sched x r m ∨
    ∃ (s₀ i₂ : ℕ) (B₀ : Block V),
      supportCutoff S (s₀ + 1) < x[i₂].time ∧ x[i₂].time ≤ tAwakeEnd ∧
      (∀ s : ℕ, tAwakeEnd ≤ slotStart S s → x[i₂].time < slotStart S s) ∧
      GST ≤ voteTime S s₀ ∧ anchorCW S tGAT ≤ slotStart S (s₀ + 1) ∧ s₀ ≤ B₀.slot ∧
      HonestChainExtends S Sched x (honestActiveAt S Sched s₀) B₀ s₀ ∧
      (∀ v ∈ updaterAt S Sched s₀,
        (stateBefore x (supportCutoff S (s₀ + 1) + 1) v).A.saved_confirmation s₀ = some B₀) ∧
      (∀ v : V, v ∉ Sched.adv ((supportCutoff S (s₀ + 1) : ℕ) : Int) → v ∈ updaterAt S Sched s₀) ∧
      OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) (chainStateOf S.C B₀).h ∧
      (∀ (j : ℕ) (u : V), x[i₂].time ≤ x[j].time → u ∉ Sched.adv (x[j].time : Int) →
        CachesOnChain S Sched x s₀ (chainStateOf S.C B₀).h (x[j][u].st)) ∧
      (∀ s : ℕ, s₀ < s → ∀ w ∈ honestActiveAt S Sched s, VoterFrameOnChainAt S Sched x s₀ s w) ∧
      (∀ s : ℕ, s₀ < s → ∀ v ∈ updaterAt S Sched s,
        UpdaterFinalizedOnChainAt S Sched x s₀ s v) ∧
      ConfirmationsChain S Sched x s₀ := by
  have hOwner : VotesCastByOwner S Sched x :=
    Proofs.Executions.votesCastByOwner_of_unforgeability S Sched x hU hMono
  have hRootsT : ∀ t : ℕ, RootsNameBlocksUntil S Sched x t :=
    fun t => rootsNameBlocksUntil_of_rootsNameBlocks x t hRoots
  rcases Proofs.Executions.lem89_phase S Sched x GST tGAT tAwakeEnd m r hDiv hMono hSync
      hCatch hSyncF hCatchF (hRootsT _) hParent hOwner hU hGST hThird hAwake hCommittees
      hSeq hOpenings with hCol | ⟨j, s₀, i₁, B₀, hjm, hs₀, hi₁, hBase, hBaseSaved, hB₀, hOld,
        hPhase, hStart, hLast⟩
  · exact Or.inl hCol
  right
  -- the caches from the step one time unit after the hand-over, at every later step: the bounded
  -- `caches_after_handover` at the time of each step
  obtain ⟨i₂, hi₂, -⟩ := Proofs.Executions.caches_after_handover S Sched x s₀
    (chainStateOf S.C B₀).h i₁ 0 hDiv hMono hU (hRootsT 0) hAdvQ hOld hStart
  have hCaches : ∀ (j : ℕ) (u : V), x[i₂].time ≤ x[j].time → u ∉ Sched.adv (x[j].time : Int) →
      CachesOnChain S Sched x s₀ (chainStateOf S.C B₀).h (x[j][u].st) := by
    intro j u hj hu
    obtain ⟨i₂', hi₂', hC⟩ := Proofs.Executions.caches_after_handover S Sched x s₀
      (chainStateOf S.C B₀).h i₁ x[j].time hDiv hMono hU (hRootsT _) hAdvQ hOld hStart
    exact hC j u (by omega) le_rfl hu
  have hΔ := one_le_Δ S
  have hk := S.C.k_ge_two
  have hR := S.C.R_ge_two
  have hmono := r_lt_of_lt_of_mono r m hSeq.mono
  -- the first slot of the last opening is at least two slots after `s₀`
  have hsm : s₀ + 2 ≤ r m * S.C.R := by
    have h1 : (r j + 1) * S.C.R ≤ r m * S.C.R := Nat.mul_le_mul_right _ (hmono j m hjm le_rfl)
    rw [Nat.add_mul, Nat.one_mul] at h1
    omega
  -- the first opening's slot is at most `s₀`
  have h0 : r 0 * S.C.R ≤ s₀ := by
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · subst hj0
      omega
    · rw [hs₀]
      exact Nat.mul_le_mul_right _ (hmono 0 j hjpos (by omega)).le
  have hfirst := hSeq.first
  have hlast := hSeq.last
  unfold healFrontSlots at hfirst
  rw [slotStart_eq] at hfirst
  rw [supportCutoff_eq, voteTime_eq, slotStart_eq] at hlast
  have e0 : 4 * Δ S * (r 0 * S.C.R) ≤ 4 * Δ S * s₀ := Nat.mul_le_mul_left _ h0
  have em : 4 * Δ S * (s₀ + 2) ≤ 4 * Δ S * (r m * S.C.R) := Nat.mul_le_mul_left _ hsm
  have ek : 4 * Δ S * (S.C.k + 2) ≤ 4 * Δ S * (3 * S.C.k + 1) := Nat.mul_le_mul_left _ (by omega)
  rw [Nat.mul_add] at em
  have hi₂' : x[i₂].time = voteTime S (r m * S.C.R) + 1 := by rw [hi₂, hi₁]
  -- the times
  have hsc : supportCutoff S (s₀ + 1) < x[i₂].time := by
    rw [hi₂', supportCutoff_eq, voteTime_eq, voteTime_eq, slotStart_eq, slotStart_eq,
      Nat.mul_add_one]
    omega
  have hx2 : x[i₂].time ≤ tAwakeEnd := by
    rw [hi₂', voteTime_eq, slotStart_eq]
    omega
  -- every slot starting at or after `tAwakeEnd` starts after the time of `i₂`: a slot start is a
  -- multiple of `4Δ`, and `tAwakeEnd` is at least the support cutoff of slot `r m * R`
  have hx2s : ∀ s : ℕ, tAwakeEnd ≤ slotStart S s → x[i₂].time < slotStart S s := by
    intro s hs
    rw [slotStart_eq] at hs
    have h1 : 4 * Δ S * (r m * S.C.R) < 4 * Δ S * s := by omega
    have h2 : 4 * Δ S * (r m * S.C.R + 1) ≤ 4 * Δ S * s :=
      Nat.mul_le_mul_left _ (Nat.lt_of_mul_lt_mul_left h1)
    rw [Nat.mul_add_one] at h2
    rw [hi₂', voteTime_eq, slotStart_eq, slotStart_eq]
    omega
  have hGST' : GST ≤ voteTime S s₀ := by
    rw [voteTime_eq, slotStart_eq]
    omega
  have hAnc : anchorCW S tGAT ≤ slotStart S (s₀ + 1) := by
    rw [anchorCW_eq]
    rw [slotStart_eq, Nat.mul_add_one (4 * Δ S) s₀]
    omega
  have hB₀slot : s₀ ≤ B₀.slot := hB₀.ge
  -- the updaters of `s₀`: every validator honest at the support cutoff of slot `s₀ + 1`
  have hscE : supportCutoff S (s₀ + 1) ≤ tAwakeEnd := le_trans hsc.le hx2
  have hdw : tGAT + Δ S ≤ dutyWindowStart S (s₀ + 1) :=
    dutyWindowStart_of_anchor S tGAT (s₀ + 1)
      (le_trans hAnc (slotStart_mono S (Nat.le_succ (s₀ + 1))))
  have hUpd : ∀ v : V, v ∉ Sched.adv ((supportCutoff S (s₀ + 1) : ℕ) : Int) →
      v ∈ updaterAt S Sched s₀ := by
    intro v hv
    refine Finset.mem_sdiff.2 ⟨mem_awakeThroughout_of_forall (fun t h1 h2 => ?_), hv⟩
    refine hAwake t (by omega) (le_trans h2 hscE) v (fun ha => hv (hMono _ _ ?_ ha))
    exact_mod_cast h2
  -- the frames at every slot after `s₀` (the bounded frames at the slot's update time), and the
  -- chain
  have hFr := fun s : ℕ => frames_after_healed_slot S Sched x GST s₀ (r m * S.C.R) i₂
    (chainStateOf S.C B₀).h (anchorCW S tGAT) (supportCutoff S (s + 1)) B₀ hDiv hMono hSync
    hCatch (hRootsT _) hParent hOwner hU hAdvQ hGST' hCommittees hAnc hB₀slot hBase
    hBaseSaved hOld hi₂' hCaches hPhase hLast
  have hVF : ∀ s : ℕ, s₀ < s → ∀ w ∈ honestActiveAt S Sched s,
      VoterFrameOnChainAt S Sched x s₀ s w := fun s hs => (hFr s).1 s hs le_rfl
  have hUF : ∀ s : ℕ, s₀ < s → ∀ v ∈ updaterAt S Sched s,
      UpdaterFinalizedOnChainAt S Sched x s₀ s v := fun s hs => (hFr s).2 s hs le_rfl
  have hChain : ConfirmationsChain S Sched x s₀ :=
    Proofs.Executions.lem81_confirmations_chain S Sched x GST s₀ (anchorCW S tGAT) B₀ hDiv hMono
      hSync hCatch hRoots hParent hOwner hGST' hCommittees hAnc hB₀slot hBase hBaseSaved
      hVF hUF
  exact ⟨s₀, i₂, B₀, hsc, hx2, hx2s, hGST', hAnc, hB₀slot, hBase, hBaseSaved, hUpd, hOld, hCaches,
    hVF, hUF, hChain⟩

/-- **The facts after the hand-over, for the readings up to a time `t`.** The proof; the audited
statement is in `Statements/Executions/HealedTopStatements.lean`. Why: for `t ≥ tAwakeEnd`, either a
root collision has hit two blocks honest validators hold by `t`, or roots name blocks up to `t`
(`rootsNameBlocksUntil_or_collision`); then `healed_handover_facts`'s proof with every reading up to
`t`: Lemma 89 reads up to the support cutoff of the last opening's first slot, at most `tAwakeEnd`;
the caches from `i₂` up to `t` (`caches_after_handover`); the frames at the slots whose update is at
most `t` (`frames_after_healed_slot_until`); and the chain before the slot after each such slot
(`lem81_chain_before`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the
  times; `m`, `r`: the index of the last honest round opening slot and the rounds of the honest round opening slots. -/
theorem healed_handover_facts_until (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd m : ℕ) (r : ℕ → ℕ)
    (hGST : GST ≤ tGAT)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hSyncF : SynchronyFromWake Sched x.toTrace (Δ_F S) GST fgObject)
    (hCatchF : CatchUpOnWake Sched x.toTrace (Δ_F S) GST fgObject)
    (hParent : ParentHeldAtDelivery S Sched x) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ v : V, v ∉ Sched.adv (t : Int) → v ∈ Sched.awake (t : Int))
    (hCommittees : CommitteeSleepiness S Sched (anchorCW S tGAT))
    (hSeq : HonestOpeningSeq S Sched r m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hOpenings : OpeningsOutsideWaitsAndWindows S r m)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t) :
    ∀ t : ℕ, tAwakeEnd ≤ t →
      RootCollisionAtOpening S Sched x r m ∨ RootCollisionHeldBy S Sched x t ∨
      ∃ (s₀ i₂ : ℕ) (B₀ : Block V),
        supportCutoff S (s₀ + 1) < x[i₂].time ∧ x[i₂].time ≤ tAwakeEnd ∧
        (∀ s : ℕ, tAwakeEnd ≤ slotStart S s → x[i₂].time < slotStart S s) ∧
        GST ≤ voteTime S s₀ ∧ anchorCW S tGAT ≤ slotStart S (s₀ + 1) ∧ s₀ ≤ B₀.slot ∧
        HonestChainExtends S Sched x (honestActiveAt S Sched s₀) B₀ s₀ ∧
        (∀ v ∈ updaterAt S Sched s₀,
          (stateBefore x (supportCutoff S (s₀ + 1) + 1) v).A.saved_confirmation s₀ = some B₀) ∧
        (∀ v : V, v ∉ Sched.adv ((supportCutoff S (s₀ + 1) : ℕ) : Int) →
          v ∈ updaterAt S Sched s₀) ∧
        OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) (chainStateOf S.C B₀).h ∧
        (∀ (j : ℕ) (u : V), x[i₂].time ≤ x[j].time → x[j].time ≤ t →
          u ∉ Sched.adv (x[j].time : Int) →
          CachesOnChain S Sched x s₀ (chainStateOf S.C B₀).h (x[j][u].st)) ∧
        (∀ s : ℕ, s₀ < s → supportCutoff S (s + 1) ≤ t →
          ∀ w ∈ honestActiveAt S Sched s, VoterFrameOnChainAt S Sched x s₀ s w) ∧
        (∀ s : ℕ, s₀ < s → supportCutoff S (s + 1) ≤ t →
          ∀ v ∈ updaterAt S Sched s, UpdaterFinalizedOnChainAt S Sched x s₀ s v) ∧
        (∀ σ : ℕ, supportCutoff S (σ + 1) ≤ t →
          ConfirmationsChainBefore S Sched x s₀ (σ + 1)) := by
  intro t ht
  rcases rootsNameBlocksUntil_or_collision x t with hRootsT | hCol
  swap
  · exact Or.inr (Or.inl hCol)
  have hOwner : VotesCastByOwner S Sched x :=
    Proofs.Executions.votesCastByOwner_of_unforgeability S Sched x hU hMono
  rcases Proofs.Executions.lem89_phase S Sched x GST tGAT tAwakeEnd m r hDiv hMono hSync
      hCatch hSyncF hCatchF (hRootsT.mono (le_trans hSeq.last ht)) hParent hOwner hU hGST
      hThird hAwake hCommittees hSeq hOpenings with
    hCol | ⟨j, s₀, i₁, B₀, hjm, hs₀, hi₁, hBase, hBaseSaved, hB₀, hOld, hPhase, hStart, hLast⟩
  · exact Or.inl hCol
  right; right
  -- the caches from the step one time unit after the hand-over, up to `t`
  obtain ⟨i₂, hi₂, hCaches⟩ := Proofs.Executions.caches_after_handover S Sched x s₀
    (chainStateOf S.C B₀).h i₁ t hDiv hMono hU hRootsT hAdvQ hOld hStart
  have hΔ := one_le_Δ S
  have hk := S.C.k_ge_two
  have hR := S.C.R_ge_two
  have hmono := r_lt_of_lt_of_mono r m hSeq.mono
  -- the first slot of the last opening is at least two slots after `s₀`
  have hsm : s₀ + 2 ≤ r m * S.C.R := by
    have h1 : (r j + 1) * S.C.R ≤ r m * S.C.R := Nat.mul_le_mul_right _ (hmono j m hjm le_rfl)
    rw [Nat.add_mul, Nat.one_mul] at h1
    omega
  -- the first opening's slot is at most `s₀`
  have h0 : r 0 * S.C.R ≤ s₀ := by
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · subst hj0
      omega
    · rw [hs₀]
      exact Nat.mul_le_mul_right _ (hmono 0 j hjpos (by omega)).le
  have hfirst := hSeq.first
  have hlast := hSeq.last
  unfold healFrontSlots at hfirst
  rw [slotStart_eq] at hfirst
  rw [supportCutoff_eq, voteTime_eq, slotStart_eq] at hlast
  have e0 : 4 * Δ S * (r 0 * S.C.R) ≤ 4 * Δ S * s₀ := Nat.mul_le_mul_left _ h0
  have em : 4 * Δ S * (s₀ + 2) ≤ 4 * Δ S * (r m * S.C.R) := Nat.mul_le_mul_left _ hsm
  have ek : 4 * Δ S * (S.C.k + 2) ≤ 4 * Δ S * (3 * S.C.k + 1) := Nat.mul_le_mul_left _ (by omega)
  rw [Nat.mul_add] at em
  have hi₂' : x[i₂].time = voteTime S (r m * S.C.R) + 1 := by rw [hi₂, hi₁]
  -- the times
  have hsc : supportCutoff S (s₀ + 1) < x[i₂].time := by
    rw [hi₂', supportCutoff_eq, voteTime_eq, voteTime_eq, slotStart_eq, slotStart_eq,
      Nat.mul_add_one]
    omega
  have hx2 : x[i₂].time ≤ tAwakeEnd := by
    rw [hi₂', voteTime_eq, slotStart_eq]
    omega
  -- every slot starting at or after `tAwakeEnd` starts after the time of `i₂`: a slot start is a
  -- multiple of `4Δ`, and `tAwakeEnd` is at least the support cutoff of slot `r m * R`
  have hx2s : ∀ s : ℕ, tAwakeEnd ≤ slotStart S s → x[i₂].time < slotStart S s := by
    intro s hs
    rw [slotStart_eq] at hs
    have h1 : 4 * Δ S * (r m * S.C.R) < 4 * Δ S * s := by omega
    have h2 : 4 * Δ S * (r m * S.C.R + 1) ≤ 4 * Δ S * s :=
      Nat.mul_le_mul_left _ (Nat.lt_of_mul_lt_mul_left h1)
    rw [Nat.mul_add_one] at h2
    rw [hi₂', voteTime_eq, slotStart_eq, slotStart_eq]
    omega
  have hGST' : GST ≤ voteTime S s₀ := by
    rw [voteTime_eq, slotStart_eq]
    omega
  have hAnc : anchorCW S tGAT ≤ slotStart S (s₀ + 1) := by
    rw [anchorCW_eq]
    rw [slotStart_eq, Nat.mul_add_one (4 * Δ S) s₀]
    omega
  have hB₀slot : s₀ ≤ B₀.slot := hB₀.ge
  -- the updaters of `s₀`: every validator honest at the support cutoff of slot `s₀ + 1`
  have hscE : supportCutoff S (s₀ + 1) ≤ tAwakeEnd := le_trans hsc.le hx2
  have hdw : tGAT + Δ S ≤ dutyWindowStart S (s₀ + 1) :=
    dutyWindowStart_of_anchor S tGAT (s₀ + 1)
      (le_trans hAnc (slotStart_mono S (Nat.le_succ (s₀ + 1))))
  have hUpd : ∀ v : V, v ∉ Sched.adv ((supportCutoff S (s₀ + 1) : ℕ) : Int) →
      v ∈ updaterAt S Sched s₀ := by
    intro v hv
    refine Finset.mem_sdiff.2 ⟨mem_awakeThroughout_of_forall (fun t h1 h2 => ?_), hv⟩
    refine hAwake t (by omega) (le_trans h2 hscE) v (fun ha => hv (hMono _ _ ?_ ha))
    exact_mod_cast h2
  -- the frames at the slots whose update is at most `t`, and the chain before the next slots
  have hFr := frames_after_healed_slot_until S Sched x GST s₀ (r m * S.C.R) i₂
    (chainStateOf S.C B₀).h (anchorCW S tGAT) t B₀ hDiv hMono hSync hCatch hRootsT hParent
    hOwner hU hAdvQ hGST' hCommittees hAnc hB₀slot hBase hBaseSaved hOld hi₂' hCaches hPhase hLast
  have hChain : ∀ σ : ℕ, supportCutoff S (σ + 1) ≤ t →
      ConfirmationsChainBefore S Sched x s₀ (σ + 1) := fun σ hσ =>
    Proofs.Executions.lem81_chain_before S Sched x GST s₀ (anchorCW S tGAT) (σ + 1) B₀ hDiv hMono
      hSync hCatch (hRootsT.mono hσ) hParent hOwner hGST' hCommittees hAnc hB₀slot hBase
      hBaseSaved
      (fun s h₁ h₂ => hFr.1 s h₁ (le_trans (supportCutoff_mono S (by omega)) hσ))
      (fun s h₁ h₂ => hFr.2 s h₁ (le_trans (supportCutoff_mono S (by omega)) hσ))
  exact ⟨s₀, i₂, B₀, hsc, hx2, hx2s, hGST', hAnc, hB₀slot, hBase, hBaseSaved, hUpd, hOld, hCaches,
    hFr.1, hFr.2, hChain⟩

/-! ## Lemma 86, finality safety after healing -/

/-- **Lemma 86.** The proof; the audited statement is in
`Statements/Executions/HealedTopStatements.lean`. Why: the facts after the hand-over
(`healed_handover_facts`) give the collision
or the healed slot `s₀` with the step `i₂`, the caches from `i₂` and the chain; Lemma 85 at `i₂`
(the adversary bound restricted from `tAwakeEnd` to the time of `i₂`, the agreement premise from
Lemma 82) puts every honest finalized block on the honest chain; two blocks on it are compatible.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the
  times; `m`, `r`: the index of the last honest round opening slot and the rounds of the honest round opening slots. -/
theorem lem86_healed_finality_safety
    (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd m : ℕ) (r : ℕ → ℕ)
    (hGST : GST ≤ tGAT)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hSyncF : SynchronyFromWake Sched x.toTrace (Δ_F S) GST fgObject)
    (hCatchF : CatchUpOnWake Sched x.toTrace (Δ_F S) GST fgObject)
    (hRoots : RootsNameBlocks S Sched x)
    (hParent : ParentHeldAtDelivery S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ v : V, v ∉ Sched.adv (t : Int) → v ∈ Sched.awake (t : Int))
    (hCommittees : CommitteeSleepiness S Sched (anchorCW S tGAT))
    (hSeq : HonestOpeningSeq S Sched r m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hOpenings : OpeningsOutsideWaitsAndWindows S r m)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t) :
    RootCollisionAtOpening S Sched x r m ∨
      ∀ (v₁ v₂ : V) (i j : ℕ), HonestThrough x i v₁ → HonestThrough x j v₂ →
        (x[i][v₁].st).S.F.compatible (x[j][v₂].st).S.F = true := by
  rcases healed_handover_facts S Sched x GST tGAT tAwakeEnd m r hGST hDiv hMono hSync hCatch
      hSyncF hCatchF hRoots hParent hU hThird hAwake hCommittees hSeq hOpenings hAdvQ with
    hCol | ⟨s₀, i₂, B₀, -, hx2, -, -, -, -, -, -, -, hOld, hCaches, -, -, hChain⟩
  · exact Or.inl hCol
  right
  have hThird₂ : AdversaryFewerThanThirdUntil Sched (validator_count V) (x[i₂].time : Int) :=
    Proofs.Executions.adversaryFewerThanThirdUntil_mono Sched (by exact_mod_cast hx2) hThird
  -- Lemma 85 at `i₂`, read up to the later of the two steps' times
  have hFin := fun t : ℕ => Proofs.Executions.lem85_honest_finalized_on_chain S Sched x s₀
    (supportCutoff S (s₀ + 1)) (chainStateOf S.C B₀).h i₂ t hU hMono
    (rootsNameBlocksUntil_of_rootsNameBlocks x _ hRoots) hThird₂ hAdvQ
    (Proofs.Executions.lem82_honest_attestations_on_chain S Sched x s₀ hDiv hMono) hOld
    (fun v hv => hCaches i₂ v le_rfl hv)
  intro v₁ v₂ i j h₁ h₂
  exact Proofs.Executions.onHonestChain_compatible S Sched x s₀ _ _ hChain
    (hFin (max x[i].time x[j].time) i v₁ (le_max_left _ _) (h₁ _ le_rfl))
    (hFin (max x[i].time x[j].time) j v₂ (le_max_right _ _) (h₂ _ le_rfl))

/-- **Lemma 86, for the readings up to a time `t`.** The proof; the audited statement is in
`Statements/Executions/HealedTopStatements.lean`. Why: for `t ≥ tAwakeEnd`, either a root collision
has hit two blocks honest validators hold by `t`, or roots name blocks up to `t`; then the facts
after the hand-over up to `t` (`healed_handover_facts_until`); Lemma 85 at `i₂`, keeping the slot
(`lem85_honest_finalized_on_chain_at`), puts every finalized block of a validator honest at a step
at a time at most `t` on the honest chain at a slot whose update is at most `t`; two such blocks are
compatible (`compatible_of_onHonestChainAt`, on the chain before the slot after the later one).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the
  times; `m`, `r`: the index of the last honest round opening slot and the rounds of the honest round opening slots. -/
theorem lem86_healed_finality_safety_until (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd m : ℕ) (r : ℕ → ℕ)
    (hGST : GST ≤ tGAT)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hSyncF : SynchronyFromWake Sched x.toTrace (Δ_F S) GST fgObject)
    (hCatchF : CatchUpOnWake Sched x.toTrace (Δ_F S) GST fgObject)
    (hParent : ParentHeldAtDelivery S Sched x) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ v : V, v ∉ Sched.adv (t : Int) → v ∈ Sched.awake (t : Int))
    (hCommittees : CommitteeSleepiness S Sched (anchorCW S tGAT))
    (hSeq : HonestOpeningSeq S Sched r m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hOpenings : OpeningsOutsideWaitsAndWindows S r m)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t) :
    ∀ t : ℕ, tAwakeEnd ≤ t →
      RootCollisionAtOpening S Sched x r m ∨ RootCollisionHeldBy S Sched x t ∨
        ∀ (v₁ v₂ : V) (i j : ℕ), HonestThrough x i v₁ → HonestThrough x j v₂ →
          x[i].time ≤ t → x[j].time ≤ t →
          (x[i][v₁].st).S.F.compatible (x[j][v₂].st).S.F = true := by
  intro t ht
  rcases rootsNameBlocksUntil_or_collision x t with hRootsT | hCol
  swap
  · exact Or.inr (Or.inl hCol)
  rcases healed_handover_facts_until S Sched x GST tGAT tAwakeEnd m r hGST hDiv hMono hSync hCatch
      hSyncF hCatchF hParent hU hThird hAwake hCommittees hSeq hOpenings hAdvQ t ht with
    hCol | hCol | ⟨s₀, i₂, B₀, -, hx2, -, -, -, -, -, -, -, hOld, hCaches, -, -, hChain⟩
  · exact Or.inl hCol
  · exact Or.inr (Or.inl hCol)
  right; right
  have hThird₂ : AdversaryFewerThanThirdUntil Sched (validator_count V) (x[i₂].time : Int) :=
    Proofs.Executions.adversaryFewerThanThirdUntil_mono Sched (by exact_mod_cast hx2) hThird
  have hx2t : x[i₂].time ≤ t := le_trans hx2 ht
  -- Lemma 85 at `i₂`, keeping the slot, read up to `t`
  have hFin := Proofs.Executions.lem85_honest_finalized_on_chain_at S Sched x s₀
    (supportCutoff S (s₀ + 1)) (chainStateOf S.C B₀).h i₂ t hU hMono
    (hRootsT.mono (max_le le_rfl hx2t)) hThird₂ hAdvQ
    (Proofs.Executions.lem82_honest_attestations_on_chain S Sched x s₀ hDiv hMono) hOld
    (fun v hv => hCaches i₂ v le_rfl hx2t hv)
  intro v₁ v₂ i j h₁ h₂ hit hjt
  obtain ⟨σ, hσ, hB⟩ := hFin i v₁ hit (h₁ _ le_rfl)
  obtain ⟨σ', hσ', hB'⟩ := hFin j v₂ hjt (h₂ _ le_rfl)
  exact Proofs.Executions.compatible_of_onHonestChainAt S Sched x s₀ t σ σ' _ _ hChain hB
    (le_trans hσ (max_le hit hx2t)) hB' (le_trans hσ' (max_le hjt hx2t))

/-! ## Lemma 90, the confirmed tip after healing -/

/-- **Lemma 90.** The proof; the audited statement is in
`Statements/Executions/HealedTopStatements.lean`. Why: as Lemma 86, the facts after the hand-over;
every honest record after the support cutoff of slot `s₀ + 1` is an honest confirmation it holds
(`lem90a_latest_confirmed_honest`); the three Lemma 90 theorems at `i₂` (the inclusion with the
invariants of Lemma 81's induction, `lem81_inv`, and the locks at `s₀`, `base_locks_on_chain`); then
the agreement and the growth moved from the time of `i₂` to `tAwakeEnd`, and the inclusion read from
`tAwakeEnd` itself.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the
  times; `m`, `r`: the index of the last honest round opening slot and the rounds of the honest round opening slots. -/
theorem lem90_healed_confirmed
    (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd m : ℕ) (r : ℕ → ℕ)
    (hGST : GST ≤ tGAT)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hSyncF : SynchronyFromWake Sched x.toTrace (Δ_F S) GST fgObject)
    (hCatchF : CatchUpOnWake Sched x.toTrace (Δ_F S) GST fgObject)
    (hRoots : RootsNameBlocks S Sched x)
    (hParent : ParentHeldAtDelivery S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ v : V, v ∉ Sched.adv (t : Int) → v ∈ Sched.awake (t : Int))
    (hCommittees : CommitteeSleepiness S Sched (anchorCW S tGAT))
    (hSeq : HonestOpeningSeq S Sched r m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hOpenings : OpeningsOutsideWaitsAndWindows S r m)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t) :
    RootCollisionAtOpening S Sched x r m ∨
      (ConfirmedAgreeAfterHealing S Sched x tAwakeEnd ∧
        ConfirmedMonotoneAfterHealing S Sched x tAwakeEnd ∧
        ConfirmedIncludedAfterHealing S Sched x tAwakeEnd ∧
        ConfirmedExtendedByHonestProposals S Sched x tAwakeEnd) := by
  have hOwner : VotesCastByOwner S Sched x :=
    Proofs.Executions.votesCastByOwner_of_unforgeability S Sched x hU hMono
  rcases healed_handover_facts S Sched x GST tGAT tAwakeEnd m r hGST hDiv hMono hSync hCatch
      hSyncF hCatchF hRoots hParent hU hThird hAwake hCommittees hSeq hOpenings hAdvQ with
    hCol | ⟨s₀, i₂, B₀, hsc, hx2, hx2s, hGST', hAnc, hB₀slot, hBase, hBaseSaved, hUpd, hOld,
      hCaches, hVF, hUF, hChain⟩
  · exact Or.inl hCol
  right
  have hLatest0 := Proofs.Executions.lem90a_latest_confirmed_honest S Sched x s₀ B₀ hDiv hMono
    hB₀slot hBase hBaseSaved hUpd
  have hLatest : ∀ (i : ℕ) (v : V), x[i₂].time ≤ x[i].time → v ∉ Sched.adv (x[i].time : Int) →
      IsHonestConfirmation S Sched x s₀ (x[i][v].st).A.latest_confirmed ∧
        (x[i][v].st).A.latest_confirmed ∈ (x[i][v].st).S.T :=
    fun i v h hv => hLatest0 i v (lt_of_lt_of_le hsc h) hv
  have hInv := Proofs.Executions.lem81_inv S Sched x GST s₀ (anchorCW S tGAT) B₀ hDiv hMono hSync
    hCatch hRoots hParent hOwner hGST' hCommittees hAnc hB₀slot hBase hBaseSaved hVF hUF
  have hAnc₂ : anchorCW S tGAT ≤ x[i₂].time := by
    have h1 : slotStart S (s₀ + 1) ≤ supportCutoff S (s₀ + 1) := by
      rw [supportCutoff_eq, voteTime_eq]
      omega
    omega
  have hAgree : ConfirmedAgreeAfterHealing S Sched x tAwakeEnd :=
    Proofs.Executions.confirmedAgree_mono S Sched x hx2
      (Proofs.Executions.lem90_confirmed_agree S Sched x s₀ (chainStateOf S.C B₀).h i₂ hChain
        (fun i v h hv => (hLatest i v h hv).1) hCaches)
  have hIncl : ConfirmedIncludedAfterHealing S Sched x tAwakeEnd :=
    Proofs.Executions.lem90_confirmed_included S Sched x GST s₀ (anchorCW S tGAT) i₂
        (chainStateOf S.C B₀).h tAwakeEnd hDiv hMono hSync hCatch hRoots hParent hOwner hU hAdvQ
        hCommittees hAnc₂ hGST' hsc.le hx2s hChain (fun s hs => (hInv s hs).1)
        (fun s hs => (hInv s hs).2)
        (fun u hu => Proofs.Executions.base_locks_on_chain S Sched x s₀ (anchorCW S tGAT) B₀ u hDiv
          hMono hCommittees hAnc hB₀slot hBase hBaseSaved hu)
        hOld hCaches hLatest
  -- every slot starting at or after `tAwakeEnd` starts after the support cutoff of slot `s₀ + 1`
  have h2 : ∀ s : ℕ, tAwakeEnd ≤ slotStart S s → 2 ≤ s := fun s hs =>
    le_trans (Nat.le_add_left 2 s₀)
      (slot_after_healed_round S s₀ s (lt_of_lt_of_le hsc (le_trans hx2 hs))).1
  refine ⟨hAgree, ?_, hIncl,
    Proofs.Executions.confirmedExtended_of_agree_included x tAwakeEnd hDiv hMono h2 hAgree hIncl⟩
  exact Proofs.Executions.confirmedMonotone_mono S Sched x hx2
    (Proofs.Executions.lem90_confirmed_monotone S Sched x s₀ (chainStateOf S.C B₀).h i₂
      hChain hLatest hCaches)

/-- **Lemma 90, for the readings up to a time `t`.** The proof; the audited statement is in
`Statements/Executions/HealedTopStatements.lean`. Why: for `t ≥ tAwakeEnd`, either a root collision
has hit two blocks honest validators hold by `t`, or roots name blocks up to `t`; then the facts
after the hand-over up to `t` (`healed_handover_facts_until`); every honest record after the support
cutoff of slot `s₀ + 1` is the confirmation of a slot whose update ran by then
(`lem90a_latest_confirmed_honest_at`); the chain invariant and the lock invariant at every slot
whose update is at most `t` (`lem81_inv_before`); Lemma 90's agreement, growth and inclusion on the
chain before a slot from the time of `i₂` to `t` (`lem90_confirmed_agree_before`,
`lem90_confirmed_monotone_before`, `lem90_confirmed_included_before`); the agreement and the growth
moved from the time of `i₂` to `tAwakeEnd`, and the inclusion read from `tAwakeEnd` itself
.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`, `tGAT`, `tAwakeEnd`: the
  times; `m`, `r`: the index of the last honest round opening slot and the rounds of the honest round opening slots. -/
theorem lem90_healed_confirmed_until (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd m : ℕ) (r : ℕ → ℕ)
    (hGST : GST ≤ tGAT)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hSyncF : SynchronyFromWake Sched x.toTrace (Δ_F S) GST fgObject)
    (hCatchF : CatchUpOnWake Sched x.toTrace (Δ_F S) GST fgObject)
    (hParent : ParentHeldAtDelivery S Sched x) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ v : V, v ∉ Sched.adv (t : Int) → v ∈ Sched.awake (t : Int))
    (hCommittees : CommitteeSleepiness S Sched (anchorCW S tGAT))
    (hSeq : HonestOpeningSeq S Sched r m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hOpenings : OpeningsOutsideWaitsAndWindows S r m)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t) :
    ∀ t : ℕ, tAwakeEnd ≤ t →
      RootCollisionAtOpening S Sched x r m ∨ RootCollisionHeldBy S Sched x t ∨
        (ConfirmedAgreeBetween S Sched x tAwakeEnd t ∧
          ConfirmedMonotoneBetween S Sched x tAwakeEnd t ∧
          ConfirmedIncludedBetween S Sched x tAwakeEnd t ∧
          ConfirmedExtendedByHonestProposalsBetween S Sched x tAwakeEnd t) := by
  intro t ht
  rcases rootsNameBlocksUntil_or_collision x t with hRootsT | hCol
  swap
  · exact Or.inr (Or.inl hCol)
  have hOwner : VotesCastByOwner S Sched x :=
    Proofs.Executions.votesCastByOwner_of_unforgeability S Sched x hU hMono
  rcases healed_handover_facts_until S Sched x GST tGAT tAwakeEnd m r hGST hDiv hMono hSync hCatch
      hSyncF hCatchF hParent hU hThird hAwake hCommittees hSeq hOpenings hAdvQ t ht with
    hCol | hCol | ⟨s₀, i₂, B₀, hsc, hx2, hx2s, hGST', hAnc, hB₀slot, hBase, hBaseSaved, hUpd, hOld,
      hCaches, hVF, hUF, hChain⟩
  · exact Or.inl hCol
  · exact Or.inr (Or.inl hCol)
  right; right
  -- the records, on the chain at a slot whose update ran by then
  have hLatest0 := Proofs.Executions.lem90a_latest_confirmed_honest_at S Sched x s₀ B₀ hDiv hMono
    hB₀slot hBase hBaseSaved hUpd
  have hLatest : ∀ (i : ℕ) (v : V), x[i₂].time ≤ x[i].time → x[i].time ≤ t →
      v ∉ Sched.adv (x[i].time : Int) → (∃ σ : ℕ, supportCutoff S (σ + 1) ≤ x[i].time ∧
        OnHonestChainAt S Sched x s₀ σ (x[i][v].st).A.latest_confirmed) ∧
        (x[i][v].st).A.latest_confirmed ∈ (x[i][v].st).S.T := by
    intro i v h _ hv
    obtain ⟨⟨σ, hσ₀, hσ, u, hu, hsv⟩, hT⟩ := hLatest0 i v (lt_of_lt_of_le hsc h) hv
    exact ⟨⟨σ, hσ, hσ₀, u, hu, _, hsv, GoldilocksCorrectness.Proofs.Routines.ancestorEq_refl _⟩, hT⟩
  -- the chain invariant and the lock invariant at the slots whose update is at most `t`
  have hInvT : ∀ s : ℕ, s₀ < s → supportCutoff S (s + 1) ≤ t →
      ChainInvFor S Sched x (honestActiveAt S Sched s) (OnHonestChainBefore S Sched x s₀ s) s ∧
      ∀ u ∈ honestActiveAt S Sched s,
        LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ s) s u := by
    intro s hs hst
    have hsr : supportCutoff S (s + 1 - 1) ≤ t := by
      rw [Nat.add_sub_cancel]
      exact le_trans (supportCutoff_mono S (Nat.le_succ s)) hst
    exact Proofs.Executions.lem81_inv_before S Sched x GST s₀ (anchorCW S tGAT) (s + 1) B₀ hDiv
      hMono hSync hCatch (hRootsT.mono hsr) hParent hOwner hGST' hCommittees hAnc hB₀slot
      hBase hBaseSaved
      (fun s' h₁ h₂ => hVF s' h₁ (le_trans (supportCutoff_mono S (by omega)) hst))
      (fun s' h₁ h₂ => hUF s' h₁ (le_trans (supportCutoff_mono S (by omega)) hst)) s hs
      (Nat.lt_succ_self s)
  have hAnc₂ : anchorCW S tGAT ≤ x[i₂].time := by
    have h1 : slotStart S (s₀ + 1) ≤ supportCutoff S (s₀ + 1) := by
      rw [supportCutoff_eq, voteTime_eq]
      omega
    omega
  have hAgree : ConfirmedAgreeBetween S Sched x tAwakeEnd t := by
    intro v₁ v₂ i j h₁ h₂ hi hj hit hjt
    exact Proofs.Executions.lem90_confirmed_agree_before S Sched x s₀ (chainStateOf S.C B₀).h i₂ t
      hDiv hMono hRootsT hU hAdvQ hOld hChain (fun i v h₁ h₂ hv => (hLatest i v h₁ h₂ hv).1)
      hCaches v₁ v₂ i j h₁ h₂ (le_trans hx2 hi) (le_trans hx2 hj) hit hjt
  have hIncl : ConfirmedIncludedBetween S Sched x tAwakeEnd t := by
    intro s hs hst hp
    exact Proofs.Executions.lem90_confirmed_included_before S Sched x GST s₀ (anchorCW S tGAT) i₂
      (chainStateOf S.C B₀).h t tAwakeEnd hDiv hMono hSync hCatch hRootsT hParent hOwner hU hAdvQ
      hCommittees hAnc₂ hGST' hsc.le hx2s hChain (fun s hs hst => (hInvT s hs hst).1)
      (fun s hs hst => (hInvT s hs hst).2)
      (fun u hu => Proofs.Executions.base_locks_on_chain S Sched x s₀ (anchorCW S tGAT) B₀ u hDiv
        hMono hCommittees hAnc hB₀slot hBase hBaseSaved hu)
      hOld hCaches hLatest s hs hst hp
  -- every slot starting at or after `tAwakeEnd` starts after the support cutoff of slot `s₀ + 1`
  have h2 : ∀ s : ℕ, tAwakeEnd ≤ slotStart S s → 2 ≤ s := fun s hs =>
    le_trans (Nat.le_add_left 2 s₀)
      (slot_after_healed_round S s₀ s (lt_of_lt_of_le hsc (le_trans hx2 hs))).1
  refine ⟨hAgree, ?_, hIncl,
    Proofs.Executions.confirmedExtendedBetween_of_agree_included x tAwakeEnd t hDiv hMono h2 hAgree
      hIncl⟩
  intro v i j hij hj hi hjt
  exact Proofs.Executions.lem90_confirmed_monotone_before S Sched x s₀ (chainStateOf S.C B₀).h i₂
    t hDiv hMono hRootsT hU hAdvQ hOld hChain hLatest hCaches v i j hij hj (le_trans hx2 hi) hjt

end GoldilocksCorrectness.Proofs.Executions
