module
public import GoldilocksCorrectness.Proofs.Executions.HealedTop
public import GoldilocksCorrectness.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Statements.Executions.AsyncDeliveryStatements
public import GoldilocksCorrectness.Proofs.Executions.HealedChainBeforeUpTo
public import GoldilocksCorrectness.Proofs.Executions.HealedVoterFrameUpTo
public import GoldilocksCorrectness.Proofs.Executions.Lemma89HandoverVFUpTo

@[expose] public section

/-!
# `HealedTop.lean` with the delivery premises up to a bound

The theorems of `GoldilocksCorrectness/Proofs/Executions/HealedTop.lean` that name a delivery
premise, restated with `SynchronyFromWakeUpTo` and `CatchUpOnWakeUpTo` at a bound on the deadlines
. The bound of each twin
is the latest ordinary deadline `max t GST + Δ` of a send its proof reads, written in the twin's
own parameters.

* `frames_after_healed_slot_until`, `healed_handover_facts_until`

No `axiom`, no `native_decide`, no `sorry`. The landed page is imported, never edited.
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

open GoldilocksCorrectness.Proofs.Routines (anchorCW_eq)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

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
at most `t` (`voterFrame_after_handover_until`, `updaterFrame_after_handover_until`).

Restated with the delivery premises up to `t`: the bound of its roots `hRoots`: the conclusions are for the slots whose update is at most `t`, and at such a slot `s` the proof reads deliveries due by the support cutoff of slot `s` (`lem81_chain_before_upTo`) and the vote time of slot `s` (`voterFrame_after_handover_until_upTo`). -/
theorem frames_after_healed_slot_until_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ s_m i₂ H anchor t : ℕ) (B₀ : Block V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject t)
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject t)
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
          Proofs.Executions.lem81_chain_before_upTo S Sched x GST s₀ anchor s B₀ hDiv hMono
            (hSync.mono hcs) (hCatch.mono hcs) (hRoots.mono hcs) hParent hOwner hGST hSleepK hAnchor hB₀slot hBase
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
            refine Proofs.Executions.voterFrame_after_handover_until_upTo S Sched x GST s₀ i₂ H s w
              hDiv hMono (hSync.mono hvs) (hCatch.mono hvs) (hRoots.mono hvs) hParent hU hAdvQ
              hGST hOld
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
  times; `m`, `r`: the index of the last honest round opening slot and the rounds of the honest round opening slots.

Restated with the delivery premises up to `b`: the conclusion gains the upper end `t ≤ b`, and at such a `t` the proof reads deliveries due by `t` (`frames_after_healed_slot_until_upTo`, `lem81_chain_before_upTo` at the slots whose update is at most `t`); the attestations (`hSyncF`, `hCatchF`) up to `slotStart S (r m * S.C.R)`, the bound of `lem89_phase_upTo`. -/
theorem healed_handover_facts_until_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd m : ℕ) (r : ℕ → ℕ)
    (hGST : GST ≤ tGAT)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption) {b : ℕ}
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject b)
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject b)
    (hSyncF : SynchronyFromWakeUpTo S Sched x (Δ_F S) GST fgObject (slotStart S (r m * S.C.R)))
    (hCatchF : CatchUpOnWakeUpTo S Sched x (Δ_F S) GST fgObject (slotStart S (r m * S.C.R)))
    (hParent : ParentHeldAtDelivery S Sched x) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ v : V, v ∉ Sched.adv (t : Int) → v ∈ Sched.awake (t : Int))
    (hCommittees : CommitteeSleepiness S Sched (anchorCW S tGAT))
    (hSeq : HonestOpeningSeq S Sched r m (tGAT + 4 * Δ S * healFrontSlots S) tAwakeEnd)
    (hOpenings : OpeningsOutsideWaitsAndWindows S r m)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t) :
    ∀ t : ℕ, tAwakeEnd ≤ t → t ≤ b →
      RootCollisionAtOpening S Sched x r m ∨ RootCollisionHeldBy S Sched x t ∨
      ∃ (s₀ i₂ : ℕ) (B₀ : Block V),
        supportCutoff S (s₀ + 1) < x[i₂].time ∧ x[i₂].time ≤ tAwakeEnd ∧
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
  intro t ht htb
  rcases rootsNameBlocksUntil_or_collision x t with hRootsT | hCol
  swap
  · exact Or.inr (Or.inl hCol)
  have hOwner : VotesCastByOwner S Sched x :=
    Proofs.Executions.votesCastByOwner_of_unforgeability S Sched x hU hMono
  rcases Proofs.Executions.lem89_phase_upTo S Sched x GST tGAT tAwakeEnd m r hDiv hMono
      (hSync.mono (le_trans hSeq.last (le_trans ht htb)))
      (hCatch.mono (le_trans hSeq.last (le_trans ht htb))) hSyncF hCatchF
      (hRootsT.mono (le_trans hSeq.last ht)) hParent hOwner hU hGST
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
  have hFr := frames_after_healed_slot_until_upTo S Sched x GST s₀ (r m * S.C.R) i₂
    (chainStateOf S.C B₀).h (anchorCW S tGAT) t B₀ hDiv hMono (hSync.mono htb) (hCatch.mono htb)
    hRootsT hParent
    hOwner hU hAdvQ hGST' hCommittees hAnc hB₀slot hBase hBaseSaved hOld hi₂' hCaches hPhase hLast
  have hChain : ∀ σ : ℕ, supportCutoff S (σ + 1) ≤ t →
      ConfirmationsChainBefore S Sched x s₀ (σ + 1) := fun σ hσ =>
    Proofs.Executions.lem81_chain_before_upTo S Sched x GST s₀ (anchorCW S tGAT) (σ + 1) B₀ hDiv hMono
      (hSync.mono (le_trans hσ htb)) (hCatch.mono (le_trans hσ htb))
      (hRootsT.mono hσ) hParent hOwner hGST' hCommittees hAnc hB₀slot hBase
      hBaseSaved
      (fun s h₁ h₂ => hFr.1 s h₁ (le_trans (supportCutoff_mono S (by omega)) hσ))
      (fun s h₁ h₂ => hFr.2 s h₁ (le_trans (supportCutoff_mono S (by omega)) hσ))
  exact ⟨s₀, i₂, B₀, hsc, hx2, hGST', hAnc, hB₀slot, hBase, hBaseSaved, hUpd, hOld, hCaches,
    hFr.1, hFr.2, hChain⟩

end GoldilocksCorrectness.Proofs.Executions

