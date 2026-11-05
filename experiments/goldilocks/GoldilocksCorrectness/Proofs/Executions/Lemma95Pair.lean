module
public import GoldilocksCorrectness.Proofs.Executions.Lemma94Pair
public import GoldilocksCorrectness.Proofs.Routines.FinalityPair
public import GoldilocksCorrectness.Proofs.Routines.ChainState
public import GoldilocksCorrectness.Proofs.Routines.ChainStateCertified
public import GoldilocksCorrectness.Proofs.Routines.ChainStateOf
public import GoldilocksCorrectness.Proofs.Routines.FGStateReaders

@[expose] public section

/-! The kit theorems:

- on the chain states: `newest_append_of_length_le` (what `newest` keeps of a list with a short
  tail), `valid_attestation_of_pending` (the second case of `valid_attestation`),
  `chainStateOf_pending_last` (an unfinalized justification is the last pending pair),
  `pending_pair_step` (one state transition keeps a pending pair, with at most one pair after it,
  and its finality participation, unless it finalizes it), and `pending_pair_along_chain` (the
  same from `B` to a descendant, when every justification on the way is at a height at most
  `B`'s);
- on the execution: `attestation_in_pool_of_sent` (an attestation an honest validator sent
  reaches an awake honest validator's pool, the delivery step of
  `round_attestations_in_pool_targets`) and `proposal_attestations_of_tick` (the attestations of
  an honest proposal are its proposer's pool filtered on the parent, the first step of Lemma 53's
  proof).

 Every member of the quorum sent at the
action time of round `r` the attestation of Lemma 94, carrying `(h_j(B), J(B))`; it reaches the
proposer of `s'` before `t_{s'}`. Every justification on the chain from `B` to `B'`'s parent is at
a height at most `h(B)` (Lemma 107 at `r`, through the honest member of its certificate), so the
pair `(h_j(B), J(B))` stays pending there, with at most one pair after it (`K_W ≥ 2`), unless it is
finalized on the way. A member's attestation already on the parent's chain was counted for the pair
(it is not on `B`'s chain: it was sent after `B`'s proposer held `B`); one not on it is valid
against the parent and included in `B'` (Lemma 52). Lemma 93 concludes.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ Δ_F slotStart voteTime supportCutoff
  dutyWindowStart proposalWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_mono dutyWindowStart_succ_le_slotStart
  one_le_Δ proposalWindowStart_add_Δ_F_le slotStart_eq slotStart_mono slot_after_healed_round
  slot_eq_of_mem supportCutoff_eq supportCutoff_succ_add_Δ_F_le_slotStart voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (chainStateOf_h_j_h_F_mono_parent chainStateOf_node
  chainStateOf_pending_last lem47_chain_state_heights pending_pair_step
  valid_attestation_of_pending is_pending_iff)
open GoldilocksCorrectness.Statements.Routines (chainStateOf)

open GoldilocksCorrectness.Proofs.Routines (pending_pair_along_chain)
open GoldilocksCorrectness.Statements.Routines (ChainStatesComputed)

open GoldilocksCorrectness.Proofs.Routines (walk_end_mem_T)

open GoldilocksCorrectness.Proofs.Routines (on_attestation_pool)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (lem66_chain_state_certified
  lem93_block_finalizes_pending lem52_pool_attestation_included valid_attestation_of_height)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans ancestorEq_node_iff
  ancestorEq_genesis_iff process_attestations_eq process_attestations_eq_foldl
  foldl_finality_participation process_height_events_cases state_transition_eq advance_height_eq
  value_eq_of_eq_some)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

-- An index `x[i]` into an execution has the valid-index predicate `fun _ _ => True`; this rule,
-- local to the file, proves it at once.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- `omega` after the `abbrev`s `Height` and `Slot` are unfolded in the goal and in every
hypothesis: `omega` does not see a fact stated at either. -/
local macro "omega_nat" : tactic =>
  `(tactic| ((try dsimp only) <;> (try unfold Height at *) <;> (try unfold Slot at *) <;> omega))

/-! ## The pending justifications along a chain -/

/-! ## The execution: delivery to the pool, and the proposal's attestations -/

/-- **Kit fact, an honest attestation reaches an awake honest validator's pool.** An attestation
an honest validator's tick at `t' ≤ tsend` put on the wire, with `GST ≤ tsend`, is in the pool of
`q` before `t₁` when `tsend + Δ_F ≤ t₁` and `q` is awake and honest from `tq` to `t₁`, with
`tq + Δ_F ≤ t₁`.

Why: the delivery step of `round_attestations_in_pool_targets`
(`Proofs/Executions/Lemma89rTargets.lean`): synchrony and catch-up deliver it to `q` by
`max (max t' GST) tq + Δ_F`, the pool admits a well-formed attestation, and the pool only grows.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `tsend`: the bound on the time of the send; `t₁`: the time the pool is
  read before; `tq`: the time from which `q` is awake; `q`: the receiver;
- `j`, `t'`: the step and the time of the send; `v`: the sender; `a`: the attestation. -/
theorem attestation_in_pool_of_sent (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tsend t₁ tq : ℕ) (q : V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSyncF : SynchronyFromWake Sched x.toTrace (Δ_F S) GST fgObject)
    (hCatchF : CatchUpOnWake Sched x.toTrace (Δ_F S) GST fgObject)
    (hGST : GST ≤ tsend) (ht₁ : tsend + Δ_F S ≤ t₁) (htq : tq + Δ_F S ≤ t₁)
    (hqAwake : ∀ t : ℕ, tq ≤ t → t ≤ t₁ →
      q ∈ Sched.awake (t : Int) ∧ q ∉ Sched.adv (t : Int))
    (j t' : ℕ) (v : V) (a : Attestation V)
    (hl : x.lbl j = AtomicAction.tickAllAwake t') (ht' : t' ≤ tsend)
    (hsent : (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[j + 1].sent - x[j].sent)
    (hhon : v ∉ Sched.adv (t' : Int)) :
    a ∈ (stateBefore x t₁ q).S.attestations := by
  have hm2 : max (max t' GST) tq + Δ_F S ≤ t₁ := by
    have := le_max_left (max t' GST) tq
    have := le_max_right (max t' GST) tq
    have := max_le ht' hGST
    omega
  obtain ⟨hT1, hT2⟩ := time_of_lbl_tickAllAwake x hl
  have hhon' : v ∉ Sched.adv (x[j].time : Int) := fun h =>
    hhon (hMono _ _ (by exact_mod_cast (by omega : x[j].time ≤ t')) h)
  obtain ⟨d, -, hld, hd⟩ := delivered_before_stepBefore_of_honest_send x hDiv hSyncF hCatchF
    hMono (sm := ⟨v, NamedObject.attest a⟩) ⟨hsent, hhon'⟩ trivial
    (le_trans (by omega : x[j + 1].time ≤ t') (le_trans (le_max_left t' GST) (le_max_left _ tq)))
    (le_trans (le_max_right t' GST) (le_max_left _ tq))
    (fun t'' h1 h2 => hqAwake t'' (le_trans (le_max_right _ _) h1) (by omega))
  obtain ⟨-, -, hstep⟩ := deliver_step_state x hld
  have hin : a ∈ (x[d + 1][q].st).S.attestations := by
    rw [hstep]
    exact (on_attestation_pool _ a).2 (tick_attestation_well_formed S Sched x j t' v a hl hsent)
  have hin' : a ∈ (stateBefore x (max (max t' GST) tq + Δ_F S) q).S.attestations :=
    pool_grows_of_le x q hd a hin
  exact pool_grows_of_le x q (stepBefore_mono x hDiv hm2) a hin'

/-- **Kit fact, the attestations of an honest proposal.** When `q` put the block `B'` on the wire
at its tick at the start of slot `s''`, `B'`'s attestations are those of `q`'s pool before that
start that are valid against `B'`'s parent's chain state and not on its chain
(`proposal_attestations`), the parent is in `q`'s tree then, and `q`'s chain state of the parent is
the parent's own.

Why: the first steps of the proof of Lemma 53 (`Proofs/Executions/Lemma53.lean`): the tick ran the
proposal (Lemma 19), whose parent is the end of the walk, in the tree.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s''`: the slot; `q`: the proposer;
  `B'`: the block. -/
theorem proposal_attestations_of_tick (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s'' : ℕ) (q : V) (B' : Block V)
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s'') ∧
      (⟨q, NamedObject.block B'⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) :
    B'.attestations = proposal_attestations (stateBefore x (slotStart S s'') q).S B'.parent ∧
      B'.parent ∈ (stateBefore x (slotStart S s'') q).S.T ∧
      (stateBefore x (slotStart S s'') q).S.σ B'.parent = chainStateOf S.C B'.parent := by
  obtain ⟨i, hl, hsent⟩ := hPropose
  obtain ⟨s, rfl⟩ : ∃ s : ℕ, s'' = s + 1 := by
    rcases s'' with _ | s
    · exfalso
      have h1 := (time_of_lbl_tickAllAwake x hl).1
      have h0 : slotStart S 0 = 0 := by rw [slotStart_eq, Nat.mul_zero]
      omega
    · exact ⟨s, rfl⟩
  obtain ⟨-, -, -, hEnd⟩ := proposal_parent_walk_end S Sched x s i B' q hl hsent
  have hΔ := one_le_Δ S
  have hss' : slotStart S (s + 1 + 1) = slotStart S (s + 1) + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq S (s + 1), Nat.mul_add, Nat.mul_one]
  have hslot₁ : S.C.slot ((slotStart S (s + 1) : ℕ) : Int) = s + 1 :=
    slot_eq_of_mem S (le_refl _) (by omega)
  have hi : stepBefore x (slotStart S (s + 1)) = i := stepBefore_eq_of_lbl x hl
  obtain ⟨-, n₁', sent₁, hrun₁, hB₁⟩ := tick_send_of_honestSendAt hl hsent
  have hSp : (tickInputState x i (slotStart S (s + 1)) q).S =
      (stateBefore x (slotStart S (s + 1)) q).S := by
    rw [(tickInputState_frame x i _ q).1]
    unfold stateBefore
    rw [hi]
  obtain ⟨-, -, -, Hp, votes_pl, support_pl, -, -, -, hBdef⟩ :=
    GoldilocksCorrectness.Statements.Routines.lem19_tick_proposes S.C S.P S.X _ n₁' _ sent₁ B'
      hrun₁ hB₁
  rw [hslot₁, hSp] at hBdef
  have hHp : B'.parent = Hp := by rw [hBdef]; rfl
  rw [hHp] at hEnd ⊢
  have hatts : B'.attestations =
      proposal_attestations (stateBefore x (slotStart S (s + 1)) q).S Hp := by
    rw [hBdef]; rfl
  have hinv := (lem11_node_invariant S Sched x (stepBefore x (slotStart S (s + 1))) q).1
  have hCSC : ChainStatesComputed S.C (stateBefore x (slotStart S (s + 1)) q).S :=
    hinv.2.2.2.2.2.1
  have hHT : Hp ∈ (stateBefore x (slotStart S (s + 1)) q).S.T :=
    walk_end_mem_T _ _ _ Hp hEnd hinv.2.2.2.1
      (lem57_justification_cache_and_record S Sched x _ q).2.2.1
  exact ⟨hatts, hHT, hCSC Hp hHT⟩

/-! ## Lemma 95 -/

/-- **Lemma 95, two consecutive honest round opening slots: the height step and the
finalization.** The proof; the audited statement is in
`Statements/Executions/FinalityLivenessStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₂`: the hand-over step; `H`: the threshold;
- `r`: the first round; `B`, `B'`: the two proposals. -/
theorem lem95_consecutive_openings_step (S : Setup V) (Sched : Schedule V)
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
    (hNoCol' : ¬ RootCollisionAtProposal S Sched x ((r + 1) * S.C.R) B')
    (hOldJ : OldAttestationsAtMost S Sched x (supportCutoff S (r * S.C.R + 1))
      (chainStateOf S.C B).h_j)
    (hHJ : H < (chainStateOf S.C B).h_j) :
    B.AncestorEq B' ∧ (chainStateOf S.C B).h + 1 ≤ (chainStateOf S.C B').h ∧
      (chainStateOf S.C B).h_j ≤ (chainStateOf S.C B').h_F := by
  obtain ⟨-, -, hBP, hPB', -, hB'T, hstep, -⟩ := consecutive_openings_step_kit S Sched x GST s₀
    anchor i₂ H r B B' hDiv hMono hSync hCatch hSyncF hCatchF hRoots hParent hOwner hU hAdvQ
    hSleepK hAnchor hGST ht₀ hChain hInv hLocks hLocks₀ hOld hCaches hParam hAfter hOpener
    hOpener' hQuorum hPropose hPropose' hNoCol hNoCol'
  have hBB' : B.AncestorEq B' := ancestorEq_trans hBP hPB'
  refine ⟨hBB', hstep, ?_⟩
  by_cases hFj : (chainStateOf S.C B).h_j ≤ (chainStateOf S.C B).h_F
  · exact le_trans hFj (GoldilocksCorrectness.Proofs.Routines.chainStateOf_h_j_h_F_mono S.C B B' hBB').2
  have hFj' : (chainStateOf S.C B).h_F < (chainStateOf S.C B).h_j := Nat.lt_of_not_le hFj
  have hR := S.C.R_ge_two
  have hΔ := one_le_Δ S
  set s := r * S.C.R with hsdef
  set s' := (r + 1) * S.C.R with hs'def
  have hss' : s' = s + S.C.R := by rw [hs'def, hsdef, Nat.add_mul, Nat.one_mul]
  obtain ⟨hs2, hvs₀, -⟩ := slot_after_healed_round S s₀ s (lt_of_le_of_lt ht₀ hAfter)
  -- the times of the round
  have hc1 := supportCutoff_eq S (s + 1)
  have hv1 := voteTime_eq S (s + 1)
  have hcs' := supportCutoff_eq S (s' + 1)
  have hvs'1 := voteTime_eq S (s' + 1)
  have hvs' := voteTime_eq S s'
  have hss1 : slotStart S (s + 1) = slotStart S s + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq S s, Nat.mul_add, Nat.mul_one]
  have hss'1 : slotStart S (s' + 1) = slotStart S s' + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq S s', Nat.mul_add, Nat.mul_one]
  have hmono_ss : slotStart S (s + 1) ≤ slotStart S s' := slotStart_mono S (by omega)
  have hdel : supportCutoff S (s + 1) + Δ_F S ≤ slotStart S s' := by
    rw [hss']; exact supportCutoff_succ_add_Δ_F_le_slotStart S s
  -- the hypotheses at round `r`, read from those up to `(r + 1) R − 1`
  have hChainS : ConfirmationsChainBefore S Sched x s₀ s :=
    fun a b c d e f h1 h2 h3 => hChain a b c d e f h1 h2 (by omega)
  have hChainS1 : ConfirmationsChainBefore S Sched x s₀ (s + 1) :=
    fun a b c d e f h1 h2 h3 => hChain a b c d e f h1 h2 (by omega)
  have hRootsS : RootsNameBlocksUntil S Sched x (supportCutoff S (s + 1)) :=
    hRoots.mono (by omega)
  have hInvS := fun s'' (h₁ : s₀ < s'') (h₂ : s'' ≤ s) => hInv s'' h₁ (by omega)
  have hLocksS := fun s'' (h₁ : s₀ < s'') (h₂ : s'' ≤ s) => hLocks s'' h₁ (by omega)
  have hCachesS : ∀ (j : ℕ) (w : V), x[i₂].time ≤ x[j].time →
      x[j].time ≤ supportCutoff S (s + 1) →
      w ∉ Sched.adv (x[j].time : Int) → CachesOnChain S Sched x s₀ H (x[j][w].st) :=
    fun j w h₁ h₂ h₃ => hCaches j w h₁ (by omega) h₃
  -- Lemma 107 at `r`: every honest attestation before the action time of `r + 1` is at most `h(B)`
  have h107 := lem107_honest_attestations_at_most_opening_height S Sched x GST s₀ anchor i₂ H r s
    B hDiv hMono hSync hCatch hRootsS hParent hOwner hU hAdvQ hSleepK hAnchor hGST ht₀ hChainS
    hInvS hLocksS hLocks₀ hOld hCachesS rfl hAfter hOpener hPropose hNoCol
  -- every block from `B` to `B'`'s parent has a justification height at most `h(B)`
  have hcv : 1 ≤ voteTime S s' := by omega
  have htjv : x[stepBefore x (voteTime S s')].time + 1 = voteTime S s' :=
    time_stepBefore_add_one x hDiv hcv
  have hjv : x[stepBefore x (voteTime S s')].time < supportCutoff S ((r + 1) * S.C.R + 1) := by
    rw [← hs'def]; omega
  have hB'T' : B' ∈ (x[stepBefore x (voteTime S s')][S.P.proposer s'].st).S.T := hB'T
  have hbound : ∀ Y : Block V, B.AncestorEq Y → Y.AncestorEq B'.parent →
      (chainStateOf S.C Y).h_j ≤ (chainStateOf S.C B).h := by
    intro Y _ hYP
    have hYT := ancestors_mem_T_of_exec S Sched x _ _ B' Y hB'T' (ancestorEq_trans hYP hPB')
    rcases Nat.eq_zero_or_pos (chainStateOf S.C Y).h_j with h0 | h0
    · rw [h0]; exact Nat.zero_le _
    have hcert := ((lem66_chain_state_certified S.C Y).1 h0).1
    exact justification_cert_height_le S Sched x _ _ _ _ Y _ _ hU (hAdvQ _) h107 hjv hYT hcert
  rcases pending_pair_along_chain S.C B B'.parent hBP hFj' hbound with hle |
      ⟨⟨l₁, l₂, hpend, -⟩, hpart⟩
  · exact le_trans hle (GoldilocksCorrectness.Proofs.Routines.chainStateOf_h_j_h_F_mono S.C _ _ hPB').2
  -- Lemma 93 at `B'`
  have he₀P : PendingPair.mk (chainStateOf S.C B).h_j (chainStateOf S.C B).J ∈
      (chainStateOf S.C B'.parent).pending_finality := by
    rw [hpend]; simp
  refine lem93_block_finalizes_pending S.C B' B'.parent (chainStateOf S.C B).h_j
    (chainStateOf S.C B).J (honestActiveAt S Sched s) rfl ⟨_, he₀P, rfl, rfl⟩ hQuorum
    (fun v hv => ?_)
  -- the member's attestation of Lemma 94, carrying the pair
  obtain ⟨i, a, hl, hsent, hav, hah, haT, -, hpair⟩ := lem94_round_attesters_after_healing S Sched x
    GST s₀ anchor i₂ H r s B v hDiv hMono hSync hCatch hRootsS hParent hOwner hU hAdvQ hSleepK
    hAnchor hGST ht₀ hChainS1 hInvS hLocksS hLocks₀ hOld hCachesS rfl hAfter hOpener hPropose
    hNoCol hOldJ hHJ hv
  have hp := hpair hFj'
  -- `v` is honest up to the action time of `r`
  have hvw : ∀ t : ℕ, dutyWindowStart S s ≤ t → t ≤ supportCutoff S (s + 1) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int) :=
    honestActiveAt_window S Sched s v hMono hv
  have hdw : dutyWindowStart S s ≤ dutyWindowStart S (s + 1) := dutyWindowStart_mono S (by omega)
  have hdw' : dutyWindowStart S (s + 1) ≤ slotStart S s := dutyWindowStart_succ_le_slotStart S s
  have hvc : v ∉ Sched.adv ((supportCutoff S (s + 1) : ℕ) : Int) :=
    (hvw _ (by omega) le_rfl).2
  -- the attestation is not on `B`'s chain: it was sent after the action time of `r`
  have hnotB : on_chain a B = false := by
    by_contra hon
    have hon' : on_chain a B = true := by simpa using hon
    have hc1' : 1 ≤ supportCutoff S (s + 1) := by omega
    have htj₁ : x[stepBefore x (supportCutoff S (s + 1))].time + 1 = supportCutoff S (s + 1) :=
      time_stepBefore_add_one x hDiv hc1'
    obtain ⟨-, -, -, -, -, -, -, -, hBin, -⟩ := round_member_frame_after_healing S Sched x GST s₀
      anchor i₂ H s B v hDiv hMono hSync hCatch hRootsS hParent hOwner hU hAdvQ hSleepK hAnchor
      hGST ht₀ hChainS hInvS hLocksS hLocks₀ hOld hCachesS hAfter hOpener hPropose hNoCol hv
    have hBin' : B ∈ (x[stepBefore x (supportCutoff S (s + 1))][v].st).S.T := hBin
    have hhon : HonestThrough x (stepBefore x (supportCutoff S (s + 1))) a.val_index := by
      rw [hav]
      intro t' ht' hadv
      exact hvc (hMono _ _ (by omega) hadv)
    have hrec := lem74_honest_attestations_recorded S Sched x hU _ v B a hBin' hon' hhon
    rw [hav] at hrec
    obtain ⟨j', t', a', hj', hl', hAw', hHon', hsent', -, hcont, -⟩ :=
      record_content_sent_step S Sched x v _ _ hrec
    have ht'le : t' ≤ x[stepBefore x (supportCutoff S (s + 1))].time := by
      rw [← (time_of_lbl_tickAllAwake x hl').2]
      exact time_mono x hj'
    have hle := hOldJ j' t' v a' hl' (by omega) hAw' hHon' hsent'
    have ha'h : a'.h = a.h := congrArg AttestationContent.h hcont
    rw [ha'h, hah] at hle
    have := (lem47_chain_state_heights S.C B B).1.2.1
    omega_nat
  by_cases hon : on_chain a B'.parent = true
  · rcases hpart a hp hon with h | h
    · rw [hnotB] at h; cases h
    · left; rw [hav] at h; exact h
  right
  -- the attestation reaches the proposer of `s'` before `t_{s'}`
  have hl' := (time_of_lbl_tickAllAwake x hl).2
  have hpool := attestation_in_pool_of_sent S Sched x GST (supportCutoff S (s + 1)) (slotStart S s')
    (proposalWindowStart S s') (S.P.proposer s') hDiv hMono hSyncF hCatchF
    (by have := voteTime_eq S s₀; have := slotStart_mono S (show s₀ ≤ s by omega); omega) hdel
    (proposalWindowStart_add_Δ_F_le S (by omega) hParam)
    (fun t h1 h2 => hOpener' t h1 (by
      have := slotStart_mono S (show s' ≤ s' + 1 by omega)
      omega))
    i _ v a hl le_rfl hsent hvc
  obtain ⟨hatts, -, hσP⟩ := proposal_attestations_of_tick S Sched x s' (S.P.proposer s') B'
    hPropose'
  refine ⟨a, ?_, hav, hp⟩
  rw [hatts]
  refine lem52_pool_attestation_included _ _ a hpool ?_ (by simpa using hon)
  rw [hσP]
  -- valid against the parent: at its height naming its `T_h`, or through the pending pair
  have hPh := (lem47_chain_state_heights S.C B B'.parent).2.2.2.1 hBP
  rcases Nat.lt_or_ge (chainStateOf S.C B).h (chainStateOf S.C B'.parent).h with hgt | hle
  · refine valid_attestation_of_pending _ a _ hp ?_ ?_ (by rw [hah]; exact hgt)
    · exact (is_pending_iff _ _).2 ⟨_, he₀P, rfl, rfl⟩
    · rw [hah]; exact (lem47_chain_state_heights S.C B B).1.2.1
  · have heq : (chainStateOf S.C B).h = (chainStateOf S.C B'.parent).h := le_antisymm hPh hle
    have hTh := (lem47_chain_state_heights S.C B B'.parent).2.2.2.2 hBP heq
    exact valid_attestation_of_height _ a (by rw [hah, heq]) (by rw [haT, hTh])

end GoldilocksCorrectness.Proofs.Executions
