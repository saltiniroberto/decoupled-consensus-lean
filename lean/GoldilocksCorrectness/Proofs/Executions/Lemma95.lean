module
public import GoldilocksCorrectness.Proofs.Executions.Lemma94
public import GoldilocksCorrectness.Proofs.Executions.Lemma89rTargets
public import GoldilocksCorrectness.Statements.Executions.HeightAttestationStatements
public import GoldilocksCorrectness.Proofs.Routines.Schedule

@[expose] public section

/-!
# Two consecutive honest round opening slots after healing: the height step

The part of the route of Lemma 95 that holds without
Lemma 94's clause on the finality pair, as kit theorems:

- `proposalWindowStart_add_Δ_F_le`: with `Δ_F + Δ ≤ 4Δ(k + 1)`, an attestation sent by the start
  of the proposal window of a slot of a later round arrives before the slot starts;
- `opener_mem_honestActiveAt`: the proposer of an honest round opening slot is an honest active
  validator of it;
- `consecutive_openings_step_kit`: for the honest round opening slots of the consecutive rounds
  `r`, `r + 1`, with a quorum of honest active validators at the first: the first proposal `B` is
  the second proposal `B'`'s parent or an ancestor of it, `B'`'s height is at least `B`'s plus one,
  and when `B'`'s parent is at `B`'s height, `B'`'s justified block is `B`'s `T_h`; with the slots
  and the second proposer's tree, which Lemma 96 reads.

Lemma 95's third conjunct, `h_j(B) ≤ h_F(B')`, is not here: its route reads Lemma 94's clause on
the finality pair, false as probed.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ Δ_F slotStart voteTime supportCutoff
  dutyWindowStart proposalWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_mono dutyWindowStart_succ_le_slotStart
  one_le_Δ proposalWindowStart_add_Δ_F_le proposalWindowStart_eq slotStart_eq slotStart_mono
  slot_after_healed_round supportCutoff_eq supportCutoff_succ_add_Δ_F_le_slotStart voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (lem47_chain_state_heights)
open GoldilocksCorrectness.Statements.Routines (chainStateOf)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (expireLocks FrameShape)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

-- An index `x[i]` into an execution has the valid-index predicate `fun _ _ => True`; this rule,
-- local to the file, proves it at once.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- `omega` after the `abbrev`s `Height` and `Slot` are unfolded in the goal and in every
hypothesis: `omega` does not see a fact stated at either. -/
local macro "omega_nat" : tactic =>
  `(tactic| ((try dsimp only) <;> (try unfold Height at *) <;> (try unfold Slot at *) <;> omega))

omit [RootOrder] in
/-- **Kit fact, the proposer of an honest round opening slot is an honest active validator of
it.** When the proposer of slot `q + 2` is awake and honest from the start of its proposal window
to the support cutoff of slot `q + 3`, it is in `honestActiveAt S Sched (q + 2)`.

Why: the proposal window of slot `q + 2` starts at the duty window of slot `q + 1`, at or before
the duty window of slot `q + 2`.

The variables:
- `S`: the setup; `Sched`: the schedule; `q`: the slot is `q + 2`. -/
theorem opener_mem_honestActiveAt (S : Setup V) (Sched : Schedule V) (q : ℕ)
    (hOpener : HonestOpenerAt S Sched (q + 2)) :
    S.P.proposer (q + 2) ∈ honestActiveAt S Sched (q + 2) := by
  have hΔ := one_le_Δ S
  have hpw := proposalWindowStart_eq S q
  have hdw := dutyWindowStart_mono S (show q + 1 ≤ q + 2 by omega)
  have hdw1 : dutyWindowStart S (q + 1) ≤ slotStart S q := dutyWindowStart_succ_le_slotStart S q
  have hss : slotStart S (q + 2 + 1) = slotStart S q + 4 * Δ S + 4 * Δ S + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq S q]
    rw [show q + 2 + 1 = q + 1 + 1 + 1 from rfl, Nat.mul_add, Nat.mul_add, Nat.mul_add,
      Nat.mul_one]
  have hc := supportCutoff_eq S (q + 2 + 1)
  have hv := voteTime_eq S (q + 2 + 1)
  unfold honestActiveAt activeAt
  rw [Finset.mem_sdiff]
  exact ⟨mem_awakeThroughout_of_forall (fun t h1 h2 => (hOpener t (by omega) h2).1),
    (hOpener _ (by omega) le_rfl).2⟩

/-! ## The height step -/

/-- **Kit theorem, two consecutive honest round opening slots: the height step.** For the rounds
`r`, `r + 1` whose first slots `s = r * R` and `s' = (r + 1) * R` are honest round opening slots,
`s` starting after the hand-over step `i₂`, with a quorum of honest active validators at `s`, the
proposals `B` of `s` and `B'` of `s'` with no root collision at their proposers, and
`Δ_F + Δ ≤ 4Δ(k + 1)`: `B` is of slot `s` and `B'` of slot `s'`; `B` is `B'`'s parent or an
ancestor of it; `B'`'s parent is an ancestor of `B'`, which is not the genesis block and which the
proposer of `s'` holds before the vote time of `s'`; `B'`'s height is at least `B`'s plus one; and
when `B'`'s parent is at `B`'s height, `B'`'s justified block is `B`'s `T_h`.

Why: `B` is on the chain before `s' − 1` (every updater of `s` saves it), so `B'`'s parent extends
it (`honest_proposal_extends_chain_until` at `s'`). When the parent is at `B`'s height, its `T_h` is
`B`'s (Lemma 47 (e)); every member of the quorum has a target at `B`'s height naming `T_h(B)`'s
root in the proposer of `s'`'s pool before `t_{s'}` (`round_attestations_in_pool_targets` over the
frame of `round_member_frame_after_healing`, the window `[proposalWindowStart S s', t_{s'}]`
covering the delivery by the parameter condition); so Lemma 53 puts `B'` at the next height with
`T_h(B)` justified.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₂`: the hand-over step; `H`: the threshold;
- `r`: the round; `B`, `B'`: the two proposals. -/
theorem consecutive_openings_step_kit (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ anchor i₂ H r : ℕ) (B B' : Block V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hSyncF : SynchronyFromWake Sched x.toTrace (Δ_F S) GST fgObject)
    (hCatchF : CatchUpOnWake Sched x.toTrace (Δ_F S) GST fgObject)
    (hRoots : RootsNameBlocksUntil S Sched x (voteTime S ((r + 1) * S.C.R)))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hSleepK : CommitteeSleepiness S Sched anchor) (hAnchor : anchor ≤ x[i₂].time)
    (hGST : GST ≤ voteTime S s₀) (ht₀ : supportCutoff S (s₀ + 1) ≤ x[i₂].time)
    (hChain : ConfirmationsChainBefore S Sched x s₀ ((r + 1) * S.C.R - 1))
    (hInv : ∀ s' : ℕ, s₀ < s' → s' ≤ (r + 1) * S.C.R - 1 →
      ChainInvFor S Sched x (honestActiveAt S Sched s') (OnHonestChainBefore S Sched x s₀ s') s')
    (hLocks : ∀ s' : ℕ, s₀ < s' → s' ≤ (r + 1) * S.C.R - 1 → ∀ w ∈ honestActiveAt S Sched s',
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ s') s' w)
    (hLocks₀ : ∀ w ∈ honestActiveAt S Sched s₀,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ (s₀ + 1)) s₀ w)
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (w : V), x[i₂].time ≤ x[j].time →
      x[j].time ≤ voteTime S ((r + 1) * S.C.R) →
      w ∉ Sched.adv (x[j].time : Int) → CachesOnChain S Sched x s₀ H (x[j][w].st))
    (hParam : Δ_F S + Δ S ≤ 4 * Δ S * (S.C.k + 1))
    (hAfter : x[i₂].time < slotStart S (r * S.C.R))
    (hOpener : HonestOpenerAt S Sched (r * S.C.R))
    (hOpener' : HonestOpenerAt S Sched ((r + 1) * S.C.R))
    (hQuorum : QuorumActiveAt S Sched (r * S.C.R))
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S (r * S.C.R)) ∧
      (⟨S.P.proposer (r * S.C.R), NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent)
    (hPropose' : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S ((r + 1) * S.C.R)) ∧
      (⟨S.P.proposer ((r + 1) * S.C.R), NamedObject.block B'⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent)
    (hNoCol : ¬ RootCollisionAtProposal S Sched x (r * S.C.R) B)
    (hNoCol' : ¬ RootCollisionAtProposal S Sched x ((r + 1) * S.C.R) B') :
    B.slot = r * S.C.R ∧ B'.slot = (r + 1) * S.C.R ∧ B.AncestorEq B'.parent ∧
      B'.parent.AncestorEq B' ∧ B' ≠ Block.genesis ∧
      B' ∈ (stateBefore x (voteTime S ((r + 1) * S.C.R))
        (S.P.proposer ((r + 1) * S.C.R))).S.T ∧
      (chainStateOf S.C B).h + 1 ≤ (chainStateOf S.C B').h ∧
      ((chainStateOf S.C B'.parent).h = (chainStateOf S.C B).h →
        (chainStateOf S.C B').J = (chainStateOf S.C B).T_h) := by
  have hR := S.C.R_ge_two
  have hΔ := one_le_Δ S
  set s := r * S.C.R with hsdef
  set s' := (r + 1) * S.C.R with hs'def
  have hss' : s' = s + S.C.R := by rw [hs'def, hsdef, Nat.add_mul, Nat.one_mul]
  obtain ⟨hs2, -, -⟩ := slot_after_healed_round S s₀ s (lt_of_le_of_lt ht₀ hAfter)
  have hsle : slotStart S s ≤ slotStart S s' := slotStart_mono S (by omega)
  have hAfter' : x[i₂].time < slotStart S s' := lt_of_lt_of_le hAfter hsle
  -- the times of the round
  have hc1 := supportCutoff_eq S (s + 1)
  have hv1 := voteTime_eq S (s + 1)
  have hss1 : slotStart S (s + 1) = slotStart S s + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq S s, Nat.mul_add, Nat.mul_one]
  have hdel : supportCutoff S (s + 1) + Δ_F S ≤ slotStart S s' := by
    rw [hss']; exact supportCutoff_succ_add_Δ_F_le_slotStart S s
  have hvs' := voteTime_eq S s'
  -- the facts at `s`, for the round's members
  have hChainS : ConfirmationsChainBefore S Sched x s₀ s :=
    fun a b c d e f h1 h2 h3 => hChain a b c d e f h1 h2 (by omega)
  have hChainS1 : ConfirmationsChainBefore S Sched x s₀ (s + 1) :=
    fun a b c d e f h1 h2 h3 => hChain a b c d e f h1 h2 (by omega)
  have hRootsS : RootsNameBlocksUntil S Sched x (supportCutoff S (s + 1)) :=
    hRoots.mono (by omega)
  have hK := fun u (hu : u ∈ honestActiveAt S Sched s) =>
    round_member_frame_after_healing S Sched x GST s₀ anchor i₂ H s B u hDiv hMono hSync hCatch
      hRootsS hParent hOwner hU hAdvQ hSleepK hAnchor hGST ht₀ hChainS
      (fun s'' h₁ h₂ => hInv s'' h₁ (by omega)) (fun s'' h₁ h₂ => hLocks s'' h₁ (by omega))
      hLocks₀ hOld (fun j w h₁ h₂ h₃ => hCaches j w h₁ (by omega) h₃) hAfter hOpener hPropose
      hNoCol hu
  -- the chain at `s`: `B` is saved by every updater of `s`, among them the proposer of `s`
  obtain ⟨q, hq⟩ : ∃ q, s = q + 2 := ⟨s - 2, by omega⟩
  obtain ⟨ip, hl, hsent⟩ := hPropose
  have hLk := locks_before_of_locks_le S Sched x s₀ q (fun s'' h₁ h₂ => hLocks s'' h₁ (by omega))
    hLocks₀ (by omega)
  have hOpenerq : HonestOpenerAt S Sched (q + 2) := hq ▸ hOpener
  obtain ⟨-, hBslot, -, -, hSavedAll, -, -⟩ := honest_proposal_saved_until S Sched x GST s₀ anchor
    i₂ H q ip B hDiv hMono hSync hCatch (hq ▸ hRootsS) hParent hOwner hU hAdvQ hSleepK hAnchor
    hGST (fun a b c d e f h1 h2 h3 => hChain a b c d e f h1 h2 (by omega))
    (fun s'' h₁ h₂ => hInv s'' h₁ (by omega)) (fun s'' h₁ h₂ => hLocks s'' h₁ (by omega)) hOld
    (fun j w h₁ h₂ h₃ => hCaches j w h₁ (by rw [← hq] at h₂; omega) h₃) ht₀ (by omega)
    (hq ▸ hAfter) hLk hOpenerq (hq ▸ hl) (hq ▸ hsent)
    (fun B'' hB'' hr => hNoCol ⟨B'', hq ▸ hB'', hr⟩)
  have hpU : S.P.proposer (q + 2) ∈ updaterAt S Sched (q + 2) :=
    honestActiveAt_subset_updaterAt S Sched (q + 2) (opener_mem_honestActiveAt S Sched q hOpenerq)
  have hBon : OnHonestChainAt S Sched x s₀ s B :=
    ⟨by omega, S.P.proposer (q + 2), hq ▸ hpU, B, hq ▸ hSavedAll _ hpU, ancestorEq_refl B⟩
  -- the proposal of `s'` extends the chain before `s' − 1`
  obtain ⟨q', hq'⟩ : ∃ q', s' = q' + 2 := ⟨s' - 2, by omega⟩
  obtain ⟨ip', hl', hsent'⟩ := hPropose'
  have hOpenerq' : HonestOpenerAt S Sched (q' + 2) := hq' ▸ hOpener'
  have hLk' := locks_before_of_locks_le S Sched x s₀ q' (fun s'' h₁ h₂ => hLocks s'' h₁ (by omega))
    hLocks₀ (by omega)
  obtain ⟨hPC, hB'slot, hB'ne, hPB', -, hHold'⟩ := honest_proposal_extends_chain_until S Sched x GST
    s₀ anchor i₂ H q' ip' B' hDiv hMono hSync hCatch (hq' ▸ hRoots) hParent hOwner hU hAdvQ
    hSleepK hAnchor hGST (fun a b c d e f h1 h2 h3 => hChain a b c d e f h1 h2 (by omega))
    (fun s'' h₁ h₂ => hInv s'' h₁ (by omega)) (fun s'' h₁ h₂ => hLocks s'' h₁ (by omega)) hOld
    (fun j w h₁ h₂ h₃ => hCaches j w h₁ (by rw [hq']; exact h₂) h₃) ht₀ (by omega)
    (hq' ▸ hAfter') hLk' hOpenerq' (hq' ▸ hl') (hq' ▸ hsent')
    (fun B'' hB'' hr => hNoCol' ⟨B'', hq' ▸ hB'', hr⟩)
  have hBP : B.AncestorEq B'.parent := hPC B ⟨s, by omega, hBon⟩
  have hB'T : B' ∈ (stateBefore x (voteTime S s') (S.P.proposer s')).S.T := by
    have := hHold' _ (opener_mem_honestActiveAt S Sched q' hOpenerq')
    rw [hq']
    exact this
  refine ⟨by rw [hBslot, hq], by rw [hB'slot, hq'], hBP, hPB', hB'ne, hB'T, ?_⟩
  -- the height step
  have hPh := (lem47_chain_state_heights S.C B B'.parent).2.2.2.1 hBP
  have hB'h := (lem47_chain_state_heights S.C B'.parent B').2.2.2.1 hPB'
  by_cases heq : (chainStateOf S.C B'.parent).h = (chainStateOf S.C B).h
  · have hTh : (chainStateOf S.C B).T_h = (chainStateOf S.C B'.parent).T_h :=
      (lem47_chain_state_heights S.C B B'.parent).2.2.2.2 hBP heq.symm
    -- the round's members' targets reach the proposer of `s'`
    have hpool := round_attestations_in_pool_targets S Sched x GST r s (slotStart S s')
      (proposalWindowStart S s') (honestActiveAt S Sched s) B (S.P.proposer s')
      (fun u => head_height_floor (stateBefore x (supportCutoff S (s + 1)) u).S)
      (fun u => get_fc_root (stateBefore x (supportCutoff S (s + 1)) u).S) hDiv hMono hSyncF
      hCatchF hsdef (by
        have := slotStart_mono S (show s₀ ≤ s + 1 by omega)
        have := voteTime_eq S s₀
        omega) hdel
      (by rw [hBslot, hq])
      (fun u hu t h1 h2 => honestActiveAt_window S Sched s u hMono hu t
        (le_trans (dutyWindowStart_mono S (by omega)) h1) h2)
      (fun u hu => (hK u hu).2.2.2.2.1)
      (fun u hu => (hK u hu).2.2.2.2.2.1)
      (fun u hu => ⟨rfl, rfl⟩)
      (fun u hu => (hK u hu).2.2.2.2.2.2.1)
      (fun u hu => (hK u hu).2.2.2.2.2.2.2.2.1)
      (fun u hu => (hK u hu).2.2.2.2.2.2.2.2.2)
      (fun u hu => (hK u hu).2.2.2.2.2.2.2.1)
      (proposalWindowStart_add_Δ_F_le S (by omega) hParam)
      (fun t h1 h2 => hOpener' t h1 (by
        have := supportCutoff_eq S (s' + 1)
        have := voteTime_eq S (s' + 1)
        have := slotStart_mono S (show s' ≤ s' + 1 by omega)
        omega))
    have hTgt := hpool.2 (fun u hu j t' a hlj ht' haw hhon hsentj hah => by
      have hHB := (hK u hu).2.2.2.1
      rcases Nat.lt_or_ge t' (supportCutoff S (s₀ + 1)) with hlt | hge
      · have := hOld j t' u a hlj hlt haw hhon hsentj
        rw [hah] at this
        exact absurd this (Nat.not_le.mpr hHB)
      · exact no_honest_timeout_after_healing_before S Sched x s₀ H (s + 1) j t' u a hDiv hMono
          hChainS1 hOld hlj hge ht' haw hhon hsentj (by rw [hah]; exact hHB))
    have h53 := lem53_next_honest_proposal_carries_certificate S Sched x s' (S.P.proposer s') B'
      B'.parent (honestActiveAt S Sched s) ⟨ip', hq' ▸ hl', hq' ▸ hsent'⟩ rfl hQuorum
      (fun u hu => by
        obtain ⟨a, ha, hav, hah, haT⟩ := hpool.1 u hu
        exact ⟨a, ha, hav, by rw [hah, heq], by rw [haT, hTh]⟩)
    have h2 := h53.2 (fun u hu => by
      obtain ⟨a, ha, hav, hah, haT, hτ⟩ := hTgt u hu
      exact ⟨a, ha, hav, by rw [hah, heq], by rw [haT, hTh], hτ⟩)
    refine ⟨by rw [h2.1, heq], fun _ => by rw [h2.2, hTh]⟩
  · refine ⟨by omega_nat, fun h => absurd h heq⟩

/-- **Two consecutive honest round opening slots after healing: the height step (Lemma 95, its
first two conjuncts).** The proof; the audited statement is in
`Statements/Executions/FinalityLivenessStatements.lean`. It is `consecutive_openings_step_kit` with
`B'`'s parent an ancestor of `B'`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₂`: the hand-over step; `H`: the threshold;
- `r`: the first round; `B`, `B'`: the two proposals. -/
theorem consecutive_openings_height_step (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ anchor i₂ H r : ℕ) (B B' : Block V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hSyncF : SynchronyFromWake Sched x.toTrace (Δ_F S) GST fgObject)
    (hCatchF : CatchUpOnWake Sched x.toTrace (Δ_F S) GST fgObject)
    (hRoots : RootsNameBlocksUntil S Sched x (voteTime S ((r + 1) * S.C.R)))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hSleepK : CommitteeSleepiness S Sched anchor) (hAnchor : anchor ≤ x[i₂].time)
    (hGST : GST ≤ voteTime S s₀) (ht₀ : supportCutoff S (s₀ + 1) ≤ x[i₂].time)
    (hChain : ConfirmationsChainBefore S Sched x s₀ ((r + 1) * S.C.R - 1))
    (hInv : ∀ s' : ℕ, s₀ < s' → s' ≤ (r + 1) * S.C.R - 1 →
      ChainInvFor S Sched x (honestActiveAt S Sched s') (OnHonestChainBefore S Sched x s₀ s') s')
    (hLocks : ∀ s' : ℕ, s₀ < s' → s' ≤ (r + 1) * S.C.R - 1 → ∀ w ∈ honestActiveAt S Sched s',
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ s') s' w)
    (hLocks₀ : ∀ w ∈ honestActiveAt S Sched s₀,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ (s₀ + 1)) s₀ w)
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (w : V), x[i₂].time ≤ x[j].time →
      x[j].time ≤ voteTime S ((r + 1) * S.C.R) →
      w ∉ Sched.adv (x[j].time : Int) → CachesOnChain S Sched x s₀ H (x[j][w].st))
    (hParam : Δ_F S + Δ S ≤ 4 * Δ S * (S.C.k + 1))
    (hAfter : x[i₂].time < slotStart S (r * S.C.R))
    (hOpener : HonestOpenerAt S Sched (r * S.C.R))
    (hOpener' : HonestOpenerAt S Sched ((r + 1) * S.C.R))
    (hQuorum : QuorumActiveAt S Sched (r * S.C.R))
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S (r * S.C.R)) ∧
      (⟨S.P.proposer (r * S.C.R), NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent)
    (hPropose' : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S ((r + 1) * S.C.R)) ∧
      (⟨S.P.proposer ((r + 1) * S.C.R), NamedObject.block B'⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent)
    (hNoCol : ¬ RootCollisionAtProposal S Sched x (r * S.C.R) B)
    (hNoCol' : ¬ RootCollisionAtProposal S Sched x ((r + 1) * S.C.R) B') :
    B.AncestorEq B' ∧ (chainStateOf S.C B).h + 1 ≤ (chainStateOf S.C B').h := by
  obtain ⟨-, -, hBP, hPB', -, -, hstep, -⟩ := consecutive_openings_step_kit S Sched x GST s₀ anchor
    i₂ H r B B' hDiv hMono hSync hCatch hSyncF hCatchF hRoots hParent hOwner hU hAdvQ hSleepK
    hAnchor hGST ht₀ hChain hInv hLocks hLocks₀ hOld hCaches hParam hAfter hOpener hOpener'
    hQuorum hPropose hPropose' hNoCol hNoCol'
  exact ⟨ancestorEq_trans hBP hPB', hstep⟩

end GoldilocksCorrectness.Proofs.Executions
