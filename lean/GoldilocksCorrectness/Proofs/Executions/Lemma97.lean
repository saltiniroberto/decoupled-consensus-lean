module
public import GoldilocksCorrectness.Proofs.Executions.Lemma107
public import GoldilocksCorrectness.Proofs.Executions.Lemma84
public import GoldilocksCorrectness.Proofs.Executions.Lemma85
public import GoldilocksCorrectness.Proofs.Executions.BlockPropagation
public import GoldilocksCorrectness.Statements.Executions.FinalityLivenessDefs
public import GoldilocksCorrectness.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Proofs.Routines.ChainStateOfCertified
public import GoldilocksCorrectness.Proofs.Routines.FGCaches
public import GoldilocksCorrectness.Proofs.Routines.FGState
public import GoldilocksCorrectness.Proofs.Routines.FGStateReaders
public import GoldilocksCorrectness.Proofs.Routines.Node
public import GoldilocksCorrectness.Proofs.Routines.NodeReach
public import GoldilocksCorrectness.Proofs.Routines.Wiring

@[expose] public section

/-!
# Lemma 97: the reader finalizes what an honest proposal's chain finalized

The proof of Lemma 97, `lem97_reader_finalized` (stated in
`GoldilocksCorrectness/Statements/Executions/FinalityLivenessStatements.lean`), and its kit:

- `update_finality_F_reaches`, `fg_on_block_F_reaches`: accepting a block `D` moves the finalized
  block to `D`'s finalized block or a descendant of it, when the FG state is `ReadyFor` `D`;
- `ReachFrom` and its per-routine and per-step forms: along a validator's steps, the step that
  adds `D` to its tree leaves its finalized block at `F(D)` or a descendant of it;
- `cert_entry_at_round_slot`, `justified_onHonestChainAt_round`: a certificate above the threshold,
  and an honest justified block above it, name an entry of the honest chain at a round's first
  slot;
- `mem_T_before_add_delay_of_send`: block propagation from an honest send at an earlier time.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_succ_le_slotStart one_le_Δ slotStart_eq
  slotStart_le_of_le_slot slot_after_healed_round slot_eq_of_mem slot_lt_of_supportCutoff_le
  slot_mono slot_mono_int supportCutoff_eq supportCutoff_mono voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (DREBPost DREBPost.bind DREBPost.bind_any DREBPost.ite
  DREBPost.of_outcome DREBPost.pure chainStateOf_F_ancestorEq chainStateOf_F_ancestorEq_J
  chainStateOf_J_isEntry chainStateOf_J_spec compatible_of_ancestorEq_both
  lem47_chain_state_heights)
open GoldilocksCorrectness.Statements.Routines (IsEntry chainStateOf)

open GoldilocksCorrectness.Proofs.Routines (ReadyFor fg_on_block_F fg_on_block_F_reaches
  fg_on_block_eq)

open GoldilocksCorrectness.Proofs.Routines (ReachFrom block_admissible_of mem_T_receive_block
  on_attestation_caches on_block_reachFrom reachFrom_frame_trans reachFrom_of_frame tick_reachFrom)

open GoldilocksCorrectness.Proofs.Routines (fgState_initial_eq initial_eq)

open GoldilocksCorrectness.Proofs.Routines (receive_reachFrom)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (lem66_chain_state_certified lem67_first_advance
  ProgressCertOn)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  ancestorEq_compatible genesis_ancestorEq)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

-- An index `x[i]` into an execution has the valid-index predicate `fun _ _ => True`; this rule,
-- local to the file, proves it at once.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- `omega` after the `abbrev`s `Height` and `Slot` are unfolded in the goal and in every
hypothesis: `omega` does not see a fact stated at either. -/
local macro "omega_nat" : tactic =>
  `(tactic| ((try dsimp only) <;> (try unfold Height at *) <;> (try unfold Slot at *) <;> omega))

/-! ## Chain states -/

/-! ## The finality update reaches the block's finalized block -/

section Routines

end Routines

/-! ## Along a validator's steps -/

section Node

/-- Every step relates a validator's node state before it to its node state after it. -/
theorem step_reachFrom {S : Setup V} {Sched : Schedule V} (x : AtomicExec (protocol S) Sched)
    (D : Block V) (i : ℕ) (v : V) : ReachFrom S.C D (x[i][v].st) (x[i + 1][v].st) := by
  rcases step_cases x i v with h | ⟨t, n', sent, -, -, hok, h⟩ | ⟨sm, -, -, -, h⟩
  · rw [h]
    exact reachFrom_of_frame S.C D rfl rfl
  · rw [h]
    obtain ⟨hS, -, -⟩ := tickInputState_frame x i t v
    exact reachFrom_frame_trans S.C D hS
      (DREBPost.of_outcome (tick_reachFrom S.C S.P S.X D (tickInputState x i t v) (t : Int)) hok)
  · rw [h]
    exact receive_reachFrom S.C S.P S.X D _ _

/-- **Kit fact, the finalized block after `D` entered the tree.** When every step at which `D`
enters `v`'s tree, before step `j`, starts from an FG state `ReadyFor` `D`, and `v` holds `D` at
step `j`, `v`'s finalized block at step `j` is `D`'s finalized block or a descendant of it. -/
theorem F_reaches_of_mem {S : Setup V} {Sched : Schedule V} (x : AtomicExec (protocol S) Sched)
    (D : Block V) (v : V) (hDg : D ≠ Block.genesis) :
    ∀ j : ℕ, (∀ i : ℕ, i < j → D ∉ (x[i][v].st).S.T → D ∈ (x[i + 1][v].st).S.T →
        ReadyFor S.C D (x[i][v].st).S) →
      D ∈ (x[j][v].st).S.T → (chainStateOf S.C D).F.AncestorEq (x[j][v].st).S.F := by
  intro j
  induction j with
  | zero =>
      intro _ hD
      rw [getElem_zero_st, initial_eq, fgState_initial_eq] at hD
      exact absurd (Finset.mem_singleton.1 hD) hDg
  | succ j ih =>
      intro hR hD
      obtain ⟨-, hF, hacc⟩ := step_reachFrom x D j v
      by_cases hDj : D ∈ (x[j][v].st).S.T
      · exact ancestorEq_trans (ih (fun i hi => hR i (Nat.lt_succ_of_lt hi)) hDj) hF
      · exact hacc hDj hD (hR j (Nat.lt_succ_self j) hDj hD)

end Node

/-! ## The honest chain at a round's first slot -/

section Rounds

/-- **Kit fact, a certificate above the threshold names an entry at a round's first slot.**
`cert_entry_at_slot`, with the slot `s_a` of the entry a round's first slot: the honest member's
attestation was sent at a round's action time (`attest_time_round`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `H`: the
  bound on the old attestations' heights; `j`: the step; `w`: the holder; `Y`: the held block;
  `T`: the block the certificate names; `h`: its height. -/
theorem cert_entry_at_round_slot (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ H j : ℕ) (w : V) (Y T : Block V) (h : Height)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : AdversaryFewerThanQuorumUntil Sched (quorum V) (x[j].time : Int))
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hY : Y ∈ (x[j][w].st).S.T) (hJ : ProgressCertOn Y h T) (hH : H < h) :
    ∃ (s_a r' : ℕ) (E : Block V), s_a = r' * S.C.R ∧ supportCutoff S (s_a + 1) ≤ x[j].time ∧
      OnHonestChainAt S Sched x s₀ s_a E ∧ IsEntry S.C E ∧ (chainStateOf S.C E).h = h ∧
      T.root = E.root := by
  obtain ⟨A, hqA, hA⟩ := hJ
  obtain ⟨u, hu, hhon⟩ : ∃ u ∈ A, HonestThrough x j u := by
    by_contra hno
    have hall : ∀ v ∈ A, ∃ t' : Int, t' ≤ (x[j].time : Int) ∧ v ∈ Sched.adv t' := by
      intro v hv
      by_contra hn
      exact hno ⟨v, hv, fun t' ht' ha => hn ⟨t', ht', ha⟩⟩
    have h3 := hAdvQ A hall
    omega
  obtain ⟨a, hau, hah, haT, hon⟩ := hA u hu
  have hrec := lem74_honest_attestations_recorded S Sched x hU j w Y a hY hon
    (by rw [hau]; exact hhon)
  rw [hau] at hrec
  obtain ⟨j', t', a', hj', hl, hAw, hHon, hsent, -, hcont, -⟩ :=
    record_content_sent_step S Sched x u j _ hrec
  have hh' : a'.h = h := by
    rw [← hah]
    exact congrArg AttestationContent.h hcont
  have hT' : a'.T = T.root := by
    rw [← haT]
    exact congrArg AttestationContent.T hcont
  have htj : t' ≤ x[j].time := by
    rw [← (time_of_lbl_tickAllAwake x hl).2]
    exact time_mono x hj'
  rcases Nat.lt_or_ge t' (supportCutoff S (s₀ + 1)) with hlt | hge
  · have hle := hOld j' t' u a' hl hlt hAw hHon hsent
    rw [hh'] at hle
    exact absurd hle (Nat.not_le.mpr hH)
  · obtain ⟨s, E, C, hs₀, ht', hv, hSaved, hEC, hE, hEh, hEr⟩ :=
      lem82b_entry_at_slot S Sched x s₀ j' t' u a' hDiv hMono hl hge hAw hHon hsent
    obtain ⟨r', hr'⟩ := attest_time_round S Sched x hl hsent
    have hsa : s = r' * S.C.R := by
      have h1 : supportCutoff S (s + 1) = supportCutoff S (r' * S.C.R + 1) := by
        rw [← ht']; exact hr'
      have h2 := slot_lt_of_supportCutoff_le S (le_of_eq h1)
      have h3 := slot_lt_of_supportCutoff_le S (le_of_eq h1.symm)
      omega
    exact ⟨s, r', E, hsa, ht' ▸ htj, ⟨hs₀, u, hv, C, hSaved, hEC⟩, hE, hEh.trans hh',
      hT'.symm.trans hEr⟩

/-- **Kit fact, an honest justified block above the threshold is on the honest chain at a round's
first slot.** `justified_onHonestChainAt_of_caches`, with the round's first slot.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `H`: the
  threshold; `i`: the step; `v`: the validator. -/
theorem justified_onHonestChainAt_round (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ H i : ℕ) (v : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hRoots : RootsNameBlocksUntil S Sched x x[i].time)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hv : v ∉ Sched.adv (x[i].time : Int))
    (hH : H < (x[i][v].st).S.h_j) :
    ∃ s_a r' : ℕ, s_a = r' * S.C.R ∧ supportCutoff S (s_a + 1) ≤ x[i].time ∧
      OnHonestChainAt S Sched x s₀ s_a (x[i][v].st).S.J := by
  obtain ⟨⟨D, hD, hJD, hhjD⟩, -, -⟩ := cachesWitnessed_of_exec S Sched x i v
  have h1 : 1 ≤ (chainStateOf S.C D).h_j := by
    rw [← hhjD]; exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le H) hH)
  obtain ⟨hJC, -, -⟩ := (lem66_chain_state_certified S.C D).1 h1
  rw [← hJD, ← hhjD] at hJC
  obtain ⟨s_a, r', E, hsa, hcut, hE, -, -, hroot⟩ := cert_entry_at_round_slot S Sched x s₀ H i v
    D _ _ hDiv hMono hU (hAdvQ _) hOld hD (progressCertOn_of_justificationCertOn hJC) hH
  have hJT : (x[i][v].st).S.J ∈ (x[i][v].st).S.T :=
    (lem57_justification_cache_and_record S Sched x i v).2.2.1
  have hEq : (x[i][v].st).S.J = E := hRoots _ _ ⟨i, v, hv, le_rfl, hJT⟩
    (onHonestChainAt_inHonestTreeBy S Sched x hMono s₀ s_a _ E hE hcut) hroot
  exact ⟨s_a, r', hsa, hcut, by rw [hEq]; exact hE⟩

end Rounds

/-! ## Propagation from an honest send -/

section Propagation

/-- **Kit fact, block propagation from an honest send.** A block `B` that `u`, honest then, put on
the wire at a step `i`, on the wire at a time at most `t ≥ GST` (`x[i + 1].time ≤ t`), of slot at most the slot of the time after
step `i`, and that `u` holds at a step `k` at a time at most `t + Δ S` while honest, is held before
`t + Δ S` by every validator `w` awake and honest at every time from `t` to `t + Δ S` whose
finalized block before `t + Δ S` is compatible with `B`.

Why: `mem_T_before_add_delay_upTo`'s route, the send being given rather than read off a holding
before `t`.

The variables:
- `x`: the execution; `GST`: the time from which the network is synchronous; `t`: the time;
  `u`, `w`: the sender and the receiver; `B`: the block; `i`, `k`: the step of the send and a
  step at which `u` holds `B`. -/
theorem mem_T_before_add_delay_of_send {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (protocol S) Sched}
    (hdiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption) {GST t : ℕ}
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (t + Δ S))
    (hParent : ParentHeldAtDelivery S Sched x)
    {u w : V} {B : Block V} {i k : ℕ}
    (hsend : HonestSendAt Sched x.toTrace i ⟨u, NamedObject.block B⟩)
    (hit : x[i + 1].time ≤ t) (hGST : GST ≤ t)
    (hslot : B.slot ≤ S.C.slot ((x[i + 1].time : ℕ) : Int))
    (hk : B ∈ (x[k][u].st).S.T) (huk : u ∉ Sched.adv (x[k].time : Int))
    (hkt : x[k].time ≤ t + Δ S)
    (hw : ∀ t' : ℕ, t ≤ t' → t' ≤ t + Δ S →
      w ∈ Sched.awake (t' : Int) ∧ w ∉ Sched.adv (t' : Int))
    (hcompat : (stateBefore x (t + Δ S) w).S.F.compatible B = true) :
    B ∈ (stateBefore x (t + Δ S) w).S.T := by
  by_cases hg : B = Block.genesis
  · subst hg
    exact genesis_mem_T_of_exec S Sched x _ w
  rcases (compatible_iff _ _).1 hcompat with hFB | hBF
  swap
  · exact ancestors_mem_T_of_exec S Sched x _ w _ B
      (lem11_node_invariant S Sched x _ w).1.2.2.2.1 hBF
  obtain ⟨d, hid, hl, hdt⟩ := delivered_before_of_honest_send_upTo x
    (synchronyFromWakeUpTo_of_synchronyFromWake _ hSync)
    (catchUpOnWakeUpTo_of_catchUpOnWake _ hCatch) hMono hsend trivial hit hGST hw
  have hd : d < stepBefore x (t + Δ S) := deliver_before_of_time x hdiv hl hdt
  obtain ⟨-, hwh, hstep⟩ := deliver_step_state x hl
  suffices h : B ∈ (x[d + 1][w].st).S.T from mem_T_mono x w hd h
  by_cases hheld : B ∈ (x[d][w].st).S.T
  · exact mem_T_mono x w (Nat.le_succ d) hheld
  rw [hstep]
  apply mem_T_receive_block
  right
  have hInvU := (lem11_node_invariant S Sched x k u).1
  obtain ⟨hparU, hwf, hprop, hps⟩ := hInvU.2.2.1.2 B hk hg
  have hFd : (x[d][w].st).S.F.AncestorEq B :=
    ancestorEq_trans (F_ancestorEq_of_le x w (le_of_lt hd)) hFB
  have hpar : B.parent ∈ (x[d][w].st).S.T :=
    hParent d w _ B hl rfl hg ((compatible_iff _ _).2 (Or.inl hFd))
  have hInvW := (lem11_node_invariant S Sched x d w).1
  refine block_admissible_of _ _ _ _ _ hwf ?_ ?_ hpar hFd hprop hps ?_
  · rw [(slot_current_at_delivery hl).1]
    exact le_trans hslot (slot_mono S (time_mono x (Nat.succ_le_of_lt hid)))
  · intro B' hB' hr
    have hBB : B' = B := hRoots B' B ⟨d, w, hwh, le_of_lt hdt, hB'⟩ ⟨k, u, huk, hkt, hk⟩ hr
    exact hheld (hBB ▸ hB')
  · intro a ha
    have h1 := hInvU.2.2.2.2.2.2.1 B hk hg a ha
    rw [hInvU.2.2.2.2.2.1 B.parent hparU] at h1
    rw [hInvW.2.2.2.2.2.1 B.parent hpar]
    exact h1

end Propagation

/-! ## Lemma 97 -/

/-- **Lemma 97, the reader.** The proof; the audited statement is in
`Statements/Executions/FinalityLivenessStatements.lean`.

Why: the honest proposal `D` of slot `s_D` is on the honest chain: every chain block before
`s_D − 1` is an ancestor of its parent, and, once the update of `s_D` is read, `D` is saved at
`s_D`. An honest justified block, and a certificate's entry, at a round's first slot `s_a` whose
update ran by `T`, are therefore compatible with `D` (`s_a < s_D` gives `s_a ≤ s_D − 2`). The
reader, awake for a delay after the proposal, receives `D` (its finalized block, below its
justified block, being compatible with `D`). At the step that adds `D` to its tree, its FG state
is `ReadyFor` `D`: its justified block is `D`'s finalized block or a descendant of it, or of a
smaller justification height; and a block of its tree at `h_max > h(D)` carries a certificate at
`h(D) > H` naming an entry compatible with `D`, at `D`'s height, so `F(D)` is an ancestor of it.
So the finalized block reaches `F(D)` there and keeps descending.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₂`: the hand-over step; `H`: the threshold; `T`: the reading time;
- `r_D`, `s_D`: the round and the slot of `D`; `j`: the reader's step; `D`: the proposal; `v`:
  the reader. -/
theorem lem97_reader_finalized (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ anchor i₂ H T r_D s_D j : ℕ) (D : Block V) (v : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x T)
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hSleepK : CommitteeSleepiness S Sched anchor) (hAnchor : anchor ≤ x[i₂].time)
    (hGST : GST ≤ voteTime S s₀) (ht₀ : supportCutoff S (s₀ + 1) ≤ x[i₂].time)
    (hChain : ∀ σ : ℕ, supportCutoff S (σ + 1) ≤ T →
      ConfirmationsChainBefore S Sched x s₀ (σ + 1))
    (hInv : ∀ s' : ℕ, s₀ < s' → supportCutoff S (s' + 1) ≤ T →
      ChainInvFor S Sched x (honestActiveAt S Sched s') (OnHonestChainBefore S Sched x s₀ s') s')
    (hLocks : ∀ s' : ℕ, s₀ < s' → supportCutoff S (s' + 1) ≤ T →
      ∀ w ∈ honestActiveAt S Sched s',
        LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ s') s' w)
    (hLocks₀ : ∀ w ∈ honestActiveAt S Sched s₀,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ (s₀ + 1)) s₀ w)
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j' : ℕ) (w : V), x[i₂].time ≤ x[j'].time → x[j'].time ≤ T →
      w ∉ Sched.adv (x[j'].time : Int) → CachesOnChain S Sched x s₀ H (x[j'][w].st))
    (hsD : s_D = r_D * S.C.R) (hT : supportCutoff S s_D ≤ T)
    (hAfter : x[i₂].time < slotStart S s_D)
    (hOpener : HonestOpenerAt S Sched s_D)
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s_D) ∧
      (⟨S.P.proposer s_D, NamedObject.block D⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent)
    (hNoCol : ¬ RootCollisionAtProposal S Sched x s_D D)
    (hHD : H < (chainStateOf S.C D).h)
    (hv : HonestThrough x j v) (hjT : x[j].time ≤ T)
    (hAwake : AwakeForDelayWithin S Sched (Δ S) v (slotStart S s_D) x[j].time) :
    (chainStateOf S.C D).F.AncestorEq (x[j][v].st).S.F := by
  obtain ⟨hs2, -, -⟩ := slot_after_healed_round S s₀ s_D (lt_of_le_of_lt ht₀ hAfter)
  obtain ⟨q, rfl⟩ : ∃ q, s_D = q + 2 := ⟨s_D - 2, by omega⟩
  obtain ⟨ip, hl, hsent⟩ := hPropose
  have hΔ := one_le_Δ S
  have hR := S.C.R_ge_two
  have hc2 := supportCutoff_eq S (q + 2)
  have hv2 := voteTime_eq S (q + 2)
  have hc3 := supportCutoff_eq S (q + 2 + 1)
  have hv3 := voteTime_eq S (q + 2 + 1)
  have hss : slotStart S (q + 2 + 1) = slotStart S (q + 2) + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq S (q + 2), Nat.mul_add, Nat.mul_one]
  have hRootNew : ∀ B' ∈ (stateBefore x (slotStart S (q + 2)) (S.P.proposer (q + 2))).S.T,
      B'.root ≠ D.root := fun B' hB' hr => hNoCol ⟨B', hB', hr⟩
  have hcutT : ∀ s' : ℕ, s' ≤ q + 1 → supportCutoff S (s' + 1) ≤ T := fun s' hs' =>
    le_trans (supportCutoff_mono S (by omega)) hT
  have hLk := locks_before_of_locks_le S Sched x s₀ q
    (fun s' h₁ h₂ => hLocks s' h₁ (hcutT s' (by omega))) hLocks₀ (by omega)
  have hChainq : ConfirmationsChainBefore S Sched x s₀ (q + 1) := hChain q (hcutT q (by omega))
  -- `D`'s place on the honest chain, and the honest active validators holding it
  obtain ⟨hChainD, hDslot, hDg, hparD, -, hHold⟩ := honest_proposal_extends_chain_until S Sched x
    GST s₀ anchor i₂ H q ip D hDiv hMono hSync hCatch (hRoots.mono (by omega)) hParent hOwner hU
    hAdvQ hSleepK hAnchor hGST hChainq (fun s' h₁ h₂ => hInv s' h₁ (hcutT s' h₂))
    (fun s' h₁ h₂ => hLocks s' h₁ (hcutT s' h₂)) hOld
    (fun j' w h₁ h₂ h₃ => hCaches j' w h₁ (by omega) h₃) ht₀ (by omega) hAfter hLk hOpener hl
    hsent hRootNew
  have hp : S.P.proposer (q + 2) ∈ honestActiveAt S Sched (q + 2) :=
    opener_mem_honestActiveAt S Sched q hOpener
  have hpu : S.P.proposer (q + 2) ∈ updaterAt S Sched (q + 2) :=
    honestActiveAt_subset_updaterAt S Sched (q + 2) hp
  have hDon : supportCutoff S (q + 2 + 1) ≤ T → OnHonestChainAt S Sched x s₀ (q + 2) D := by
    intro hc
    obtain ⟨-, -, -, -, hSavedAll, -⟩ := honest_proposal_saved_until S Sched x GST s₀ anchor i₂ H q
      ip D hDiv hMono hSync hCatch (hRoots.mono hc) hParent hOwner hU hAdvQ hSleepK hAnchor hGST
      hChainq (fun s' h₁ h₂ => hInv s' h₁ (le_trans (supportCutoff_mono S (by omega)) hc))
      (fun s' h₁ h₂ => hLocks s' h₁ (le_trans (supportCutoff_mono S (by omega)) hc)) hOld
      (fun j' w h₁ h₂ h₃ => hCaches j' w h₁ (le_trans h₂ hc) h₃) ht₀ (by omega) hAfter hLk
      hOpener hl hsent hRootNew
    exact ⟨by omega, _, hpu, D, hSavedAll _ hpu, ancestorEq_refl D⟩
  -- an entry at a round's first slot whose update ran by `T` is compatible with `D`
  have hcompat : ∀ (E : Block V) (s_a r' : ℕ), s_a = r' * S.C.R →
      supportCutoff S (s_a + 1) ≤ T → OnHonestChainAt S Sched x s₀ s_a E →
      E.compatible D = true := by
    intro E s_a r' hsa hcut hE
    rcases Nat.lt_or_ge s_a (q + 2) with hlt | hge
    · have hrr : r' < r_D := by
        rw [hsa, hsD] at hlt
        exact Nat.lt_of_mul_lt_mul_right hlt
      have hm : (r' + 1) * S.C.R ≤ r_D * S.C.R := Nat.mul_le_mul_right _ hrr
      rw [Nat.succ_mul] at hm
      have hle : s_a < q + 1 := by omega
      have hEp := hChainD E ⟨s_a, hle, hE⟩
      exact (compatible_iff _ _).2 (Or.inl (ancestorEq_trans hEp hparD))
    · have hDc := hDon (le_trans (supportCutoff_mono S (by omega)) hcut)
      exact onHonestChainBefore_compatible S Sched x s₀ (s_a + 1) E D (hChain s_a hcut)
        ⟨s_a, by omega, hE⟩ ⟨q + 2, by omega, hDc⟩
  -- an honest justified block, read at a step from the hand-over to `T`, is compatible with `D`
  have hJcompat : ∀ k : ℕ, x[i₂].time ≤ x[k].time → x[k].time ≤ T →
      v ∉ Sched.adv (x[k].time : Int) → (x[k][v].st).S.J.compatible D = true := by
    intro k hk1 hk2 hvk
    obtain ⟨s_a, r', hsa, hcut, hJ⟩ := justified_onHonestChainAt_round S Sched x s₀ H k v hDiv
      hMono hU (hRoots.mono hk2) hAdvQ hOld hvk (hCaches k v hk1 hk2 hvk).1
    exact hcompat _ s_a r' hsa (le_trans hcut hk2) hJ
  have hvt : ∀ t' : ℕ, t' ≤ x[j].time → v ∉ Sched.adv (t' : Int) := fun t' ht' =>
    hv _ (by exact_mod_cast ht')
  -- the reader receives `D` within the delay it is awake for
  obtain ⟨τ, hτ1, hτ2, hτaw⟩ := hAwake
  rw [max_self] at hτ2 hτaw
  have hw : ∀ t' : ℕ, τ ≤ t' → t' ≤ τ + Δ S →
      v ∈ Sched.awake (t' : Int) ∧ v ∉ Sched.adv (t' : Int) := by
    intro t' h1 h2
    refine ⟨mem_awakeThroughout_iff.1 hτaw _ (by exact_mod_cast h1) (by exact_mod_cast h2),
      hvt t' (by omega)⟩
  have hk₁ : 1 ≤ τ + Δ S := by omega
  set k₁ := stepBefore x (τ + Δ S) with hk₁def
  have htk₁ : x[k₁].time + 1 = τ + Δ S := time_stepBefore_add_one x hDiv hk₁
  have hk₁j : k₁ ≤ j := by
    by_contra hn
    have := time_mono x (show j ≤ k₁ by omega)
    omega
  have hi2k₁ : x[i₂].time ≤ x[k₁].time := by omega
  have hvk₁ : v ∉ Sched.adv (x[k₁].time : Int) := hvt _ (by omega)
  have hFc : (stateBefore x (τ + Δ S) v).S.F.compatible D = true := by
    have hC := hCaches k₁ v hi2k₁ (by omega) hvk₁
    exact compatible_of_ancestorEq_both hC.2.2.2.2 (ancestorEq_refl D)
      (hJcompat k₁ hi2k₁ (by omega) hvk₁)
  -- the proposer holds `D` before the vote time of `s_D`, honest then
  set k₀ := stepBefore x (voteTime S (q + 2)) with hk₀def
  have htk₀ : x[k₀].time + 1 = voteTime S (q + 2) := time_stepBefore_add_one x hDiv (by omega)
  have hss1 : slotStart S (q + 2) = slotStart S (q + 1) + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq S (q + 1), show q + 2 = (q + 1) + 1 from rfl, Nat.mul_add,
      Nat.mul_one]
  have hdw : dutyWindowStart S (q + 2) ≤ slotStart S (q + 1) :=
    dutyWindowStart_succ_le_slotStart S (q + 1)
  have hpc : S.P.proposer (q + 2) ∉ Sched.adv ((supportCutoff S (q + 2 + 1) : ℕ) : Int) :=
    (honestActiveAt_window S Sched (q + 2) _ hMono hp _ (by omega) le_rfl).2
  have hpw : ∀ t' : ℕ, t' ≤ supportCutoff S (q + 2 + 1) →
      S.P.proposer (q + 2) ∉ Sched.adv (t' : Int) := by
    intro t' ht' had
    exact hpc (hMono _ _ (by exact_mod_cast ht') had)
  have hip := time_of_lbl_tickAllAwake x hl
  have hslotD : D.slot ≤ S.C.slot ((x[ip + 1].time : ℕ) : Int) := by
    rw [hip.2, hDslot, slot_eq_of_mem S le_rfl (by omega)]
  have hipτ : x[ip + 1].time ≤ τ := by have := hip.2; omega
  have hGSTτ : GST ≤ τ := by
    have := supportCutoff_eq S (s₀ + 1)
    have := voteTime_eq S (s₀ + 1)
    have := voteTime_eq S s₀
    have : slotStart S (s₀ + 1) = slotStart S s₀ + 4 * Δ S := by
      rw [slotStart_eq, slotStart_eq S s₀, Nat.mul_add, Nat.mul_one]
    omega
  have hk₀τ : x[k₀].time ≤ τ + Δ S := by omega
  have hk₀c : x[k₀].time ≤ supportCutoff S (q + 2 + 1) := by omega
  have hipc : x[ip].time ≤ supportCutoff S (q + 2 + 1) := by have := hip.1; omega
  have hτT : τ + Δ S ≤ T := by omega
  have hDin : D ∈ (stateBefore x (τ + Δ S) v).S.T :=
    mem_T_before_add_delay_of_send hDiv hMono hSync hCatch (hRoots.mono hτT) hParent
      (i := ip) (k := k₀) ⟨hsent, hpw _ hipc⟩ hipτ hGSTτ hslotD (hHold _ hp)
      (hpw _ hk₀c) hk₀τ hw hFc
  have hDj : D ∈ (x[j][v].st).S.T := mem_T_mono x v hk₁j hDin
  -- at the step that adds `D` to the reader's tree, its FG state is ready for `D`
  refine F_reaches_of_mem x D v hDg j (fun i hi hDi hDi1 => ?_) hDj
  obtain ⟨-, -, hslot1⟩ := step_tree_new x hDi1 hDi
  have hti1 : slotStart S (q + 2) ≤ x[i + 1].time := by
    apply slotStart_le_of_le_slot S
    rw [← hDslot]
    exact le_trans hslot1 (slot_mono_int S (clock_le_time x (i + 1) v))
  have hsucc := time_succ_le x i
  have hiT : x[i].time ≤ x[j].time := time_mono x hi.le
  have hi2 : x[i₂].time ≤ x[i].time := by omega
  have hvi : v ∉ Sched.adv (x[i].time : Int) := hvt _ hiT
  have hC := hCaches i v hi2 (by omega) hvi
  obtain ⟨hH, -, hJent, hJh, -⟩ := hC
  refine ⟨(lem11_node_invariant S Sched x i v).1.2.2.2.2.2.1, ?_, ?_⟩
  · -- the justification
    rcases (compatible_iff _ _).1 (hJcompat i hi2 (by omega) hvi) with hJD | hDJ
    · by_cases hlt : (x[i][v].st).S.h_j < (chainStateOf S.C D).h_j
      · exact Or.inr hlt
      left
      have hFJD := chainStateOf_F_ancestorEq_J S.C D
      by_cases hj0 : (chainStateOf S.C D).h_j = 0
      · rw [(chainStateOf_J_spec S.C D).2.1 hj0] at hFJD
        exact ancestorEq_trans hFJD (genesis_ancestorEq _)
      obtain ⟨-, hJDD, hJDh⟩ := (lem66_chain_state_certified S.C D).1 (by omega_nat)
      rcases ancestorEq_compatible hJD hJDD with hSJ | hJS
      · have hle := (lem47_chain_state_heights S.C _ _).2.2.2.1 hSJ
        have heq : (chainStateOf S.C (x[i][v].st).S.J).h =
            (chainStateOf S.C (chainStateOf S.C D).J).h := by
          rw [hJh, hJDh] at hle ⊢
          omega_nat
        have hTe := (lem47_chain_state_heights S.C _ _).2.2.2.2 hSJ heq
        have hJe := chainStateOf_J_isEntry S.C D (by omega_nat)
        unfold IsEntry at hJent hJe
        rw [hJent, hJe] at hTe
        rw [hTe]
        exact hFJD
      · exact ancestorEq_trans hFJD hJS
    · exact Or.inl (ancestorEq_trans (chainStateOf_F_ancestorEq S.C D) hDJ)
  · -- a viable descendant of `F(D)`
    obtain ⟨-, ⟨X, hX, hXh⟩, -⟩ := cachesWitnessed_of_exec S Sched x i v
    by_cases hle : (x[i][v].st).S.h_max ≤ (chainStateOf S.C D).h
    · exact Or.inl hle
    right
    have hlt : (chainStateOf S.C D).h < (chainStateOf S.C X).h := by
      rw [hXh]; exact Nat.lt_of_not_le hle
    obtain ⟨Y, hYX, -, -, -, hTY, hPC⟩ := lem67_first_advance S.C X (chainStateOf S.C D).h
      (by omega_nat) hlt
    have hYT := ancestors_mem_T_of_exec S Sched x i v X Y hX hYX
    obtain ⟨s_a, r', E, hsa, hcut, hE, -, hEh, hroot⟩ := cert_entry_at_round_slot S Sched x s₀ H
      i v Y _ _ hDiv hMono hU (hAdvQ _) hOld hYT hPC hHD
    have hTT := ancestors_mem_T_of_exec S Sched x i v Y _ hYT hTY
    have hEq : (chainStateOf S.C Y.parent).T_h = E := (hRoots.mono (by omega)) _ _
      ⟨i, v, hvi, le_rfl, hTT⟩ (onHonestChainAt_inHonestTreeBy S Sched x hMono s₀ s_a _ E hE hcut)
      hroot
    have hEX : E.AncestorEq X := hEq ▸ ancestorEq_trans hTY hYX
    have hFE : (chainStateOf S.C D).F.AncestorEq E := by
      by_cases hF0 : (chainStateOf S.C D).h_F = 0
      · rw [GoldilocksCorrectness.Proofs.Routines.chainStateOf_F_genesis S.C D hF0]
        exact genesis_ancestorEq E
      rcases (compatible_iff _ _).1 (hcompat E s_a r' hsa (by omega) hE) with hED | hDE
      · rcases ancestorEq_compatible (chainStateOf_F_ancestorEq S.C D) hED with h | h
        · exact h
        · exfalso
          have h1 := (lem47_chain_state_heights S.C _ _).2.2.2.1 h
          obtain ⟨-, -, -, hFh⟩ := (lem66_chain_state_certified S.C D).2.2 (by omega_nat)
          have hb := (lem47_chain_state_heights S.C D D).1
          rw [hFh, hEh] at h1
          omega_nat
      · exact ancestorEq_trans (chainStateOf_F_ancestorEq S.C D) hDE
    exact ⟨X, hX, ancestorEq_trans hFE hEX, max_le (by rw [hXh]) hlt.le⟩

end GoldilocksCorrectness.Proofs.Executions
