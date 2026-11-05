module
public import GoldilocksCorrectness.Proofs.Executions.PeriodChainBlock
public import GoldilocksCorrectness.Statements.Executions.PeriodCompatDefs

@[expose] public section

/-!
Copies of seven landed step lemmas, each with `VotesExtendAt` replaced by `VotesCompatibleAt`
(the copy of `PeriodCompatDefs.lean`) and the one step that reads "the vote is on `B`'s chain"
reading "the vote's block is compatible with `B`". The originals stay byte-identical. The bodies
are made by the script `scratch/goldilocks_async/laneAR4/mk_compat_copies.py` from the landed
proofs, each replacement an exact string matched once; the audited statements are in
`Statements/Executions/PeriodCompatCopiesStatements.lean`.

- `owed_slot_le_k`: a slot whose previous votes were owed inside the period is at most `s + k`;
- `holders_vote_compatible_of_votesCompatibleAt`, `active_vote_compatible_of_votesCompatibleAt`:
  the two conjuncts of `VotesCompatibleAt`, read as "the vote's block is compatible with `B`";
- the copies: `score_set_outside_ofCompat` (of `score_set_outside`),
  `fast_blocks_compatible_of_votes_updater_ofCompat`, `attestations_step_ofHeldEntry_ofCompat`,
  `opponent_not_compatible` (of `opponent_not_extender`), `opponents_fewer_than_half_ofCompat`,
  `holder_vote_extends_B_orTwoPast_ofCompat`, `holderInv_step_ofCompat`;


 the originals of the copies were
deleted then.

Every copy that reads the holders' conjunct reads it at a slot whose previous votes were owed
inside the period, so at a slot at most `s + k` (`owed_slot_le_k`), or at a slot of the
hand-over lock's life (`holder_vote_extends_B_orTwoPast_ofCompat` takes `s' ≤ s + k`).
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff)

open GoldilocksCorrectness.Statements.Routines (chainStateOf)

open GoldilocksCorrectness.Statements.Routines (CachesCompatibleWith)

open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_succ_lt_supportCutoff
  expireLocks_keepsVotes fast_test_eq_ok_true_iff fc_root_eq fg_to_ac_F goldfish_fork_choice_eq
  is_live_iff mem_viable_tree_iff mem_votes_by_iff pool_of_keepsVotes t_eq_mul wake_eq)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg AtomicHonest)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Proofs.Routines
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn expireLocks
  lem15_tick_updates_confirmation lem49_tick_attests ProgressCertOn)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

-- An index `x[i]` into an execution has the valid-index predicate `fun _ _ => True`; this rule,
-- local to the file, proves it at once. No statement and no proof term changes.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- `omega` after the `abbrev`s `Height` and `Slot` are unfolded. -/
local macro "omega_nat" : tactic =>
  `(tactic| ((try dsimp only) <;> (try unfold Height at *) <;> (try unfold Slot at *) <;> omega))

/-! ## Reading the compatible vote clause -/

omit [RootOrder] in
/-- **A slot whose previous votes were owed inside the period is at most `s + k`.** When the
period ends one delay before the vote time of slot `s + k`, a slot `s'` with
`supportCutoff S (s' − 1) < b₁` has `s' ≤ s + k`.

Why: `supportCutoff S (s' − 1) = voteTime S (s' − 1) + Δ < b₁ ≤ voteTime S (s + k) − Δ`, so
`s' − 1 < s + k`.

The variables:
- `S`: the setup; `s`: the hand-over slot; `b₀`, `b₁`: the start and the end of the period;
  `s'`: the slot. -/
theorem owed_slot_le_k {S : Setup V} {s b₀ b₁ s' : ℕ}
    (hb₁ : b₁ + Δ S ≤ voteTime S (s + S.C.k)) (h : VotesOwedInPeriod S b₀ b₁ s') :
    s' ≤ s + S.C.k := by
  have hΔ := one_le_Δ S
  obtain ⟨-, h2⟩ := h
  by_contra hc
  have hle : s + S.C.k ≤ s' - 1 := by omega
  have h3 : voteTime S (s + S.C.k) ≤ voteTime S (s' - 1) := by
    rw [voteTime_eq, voteTime_eq, slotStart_eq, slotStart_eq]
    exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hle) _
  have h4 := supportCutoff_eq S (s' - 1)
  omega

/-- The holders' conjunct of `VotesCompatibleAt`, at a slot `s' ≤ s + k`, read as "the vote's
block is compatible with `B`".

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the hand-over slot; `B`: the
  protected block; `b₀`, `b₁`: the start and the end of the period; `s'`: the slot of the votes. -/
theorem holders_vote_compatible_of_votesCompatibleAt {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (protocol S) Sched} {s : ℕ} {B : Block V} {b₀ b₁ s' : ℕ}
    (h : VotesCompatibleAt S Sched x s B b₀ b₁ s') (hk : s' ≤ s + S.C.k) :
    ∀ u ∈ holdersAt S Sched s s', ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s') ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) →
      ∃ H_u ∈ (stateBefore x (voteTime S s') u).S.T,
        vote = GoldfishVote.mk u s' H_u.root ∧ H_u.compatible B = true := by
  intro u hu vote hsend
  obtain ⟨H_u, hT, hv, hB⟩ := h.1 hk u hu vote hsend
  exact ⟨H_u, hT, hv, (compatible_iff _ _).2 (Or.inr hB)⟩

/-- The honest active voters' conjunct of `VotesCompatibleAt`, at a slot whose previous votes
were not owed inside the period, read as "the vote's block is compatible with `B`".

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the hand-over slot; `B`: the
  protected block; `b₀`, `b₁`: the start and the end of the period; `s'`: the slot of the votes. -/
theorem active_vote_compatible_of_votesCompatibleAt {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (protocol S) Sched} {s : ℕ} {B : Block V} {b₀ b₁ s' : ℕ}
    (h : VotesCompatibleAt S Sched x s B b₀ b₁ s') (hgood : ¬ VotesOwedInPeriod S b₀ b₁ s') :
    ∀ u ∈ honestActiveAt S Sched s', ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s') ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) →
      ∃ H_u ∈ (stateBefore x (voteTime S s') u).S.T,
        vote = GoldfishVote.mk u s' H_u.root ∧ H_u.compatible B = true := by
  intro u hu vote hsend
  obtain ⟨H_u, hT, hv, hB⟩ := h.2 hgood u hu vote hsend
  refine ⟨H_u, hT, hv, ?_⟩
  rcases hB with hB | ⟨hc, -⟩
  · exact (compatible_iff _ _).2 (Or.inr hB)
  · exact hc

/-! ## The copies -/

/-- **The votes a set of validators casts for blocks compatible with `B` do not count
for a block that conflicts with `B`.** `score_set_outside` with each member's vote for a block
`H_u` compatible with `B` in place of `B` or a descendant of `B`: the equivocators of `sv` and
the validators whose vote in `sv` supports a block `D` conflicting with `B` are members of the
committee of slot `s'` outside `G`.

 The one change is the premise `hGv`, which concludes `H_u.compatible B = true` in place of
`B.AncestorEq H_u`, and the step that reads it: `D` an ancestor of `H_u`, compatible with `B`, is
compatible with `B` (`compatible_of_ancestorEq_compatible`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s'`: the slot; `B`: the protected
  block; `D`: the conflicting block; `u`: the validator whose pool it is; `c`: the time; `G`: the
  set of validators; `sv`: the votes counted.

Roots name blocks until `c`: as `score_set_outside`. -/
theorem score_set_outside_ofCompat (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hOwner : VotesCastByOwner S Sched x) {s' c : ℕ} {B D : Block V} {u : V}
    (hc : voteTime S s' ≤ c)
    (hRoots : RootsNameBlocksUntil S Sched x c)
    (hu : u ∉ Sched.adv (c : Int))
    (G : Finset V) (hG : ∀ v' ∈ G, v' ∉ Sched.adv (c : Int))
    (hGv : ∀ v' ∈ G, ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s') ∧
        (⟨v', NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) →
      ∃ H_u ∈ (stateBefore x (voteTime S s') v').S.T,
        vote = GoldfishVote.mk v' s' H_u.root ∧ H_u.compatible B = true)
    (sv : Finset (GoldfishVote V)) (hsv : sv ⊆ (stateBefore x c u).A.pool s')
    (hDB : ¬ D.compatible B = true) :
    equivocators sv ∪ supportersOf (fg_to_ac (stateBefore x c u).S) sv sv s' D ⊆
      S.P.committee s' \ G := by
  have hΔ := one_le_Δ S
  have hv1 : 1 ≤ voteTime S s' := by rw [voteTime_eq]; omega
  have hc1 : 1 ≤ c := le_trans hv1 hc
  have hcomm : ∀ vote ∈ sv, vote.val_index ∈ S.P.committee s' := fun vote hvote =>
    pool_committee_of_exec S Sched x (stepBefore x c) u s' vote (hsv hvote)
  -- a vote of a member of `G` in the pool is that member's vote for `B`'s chain
  have hExt : ∀ v' ∈ G, ∀ vote ∈ sv, vote.val_index = v' →
      ∃ H_u ∈ (stateBefore x (voteTime S s') v').S.T,
        vote = GoldfishVote.mk v' s' H_u.root ∧ H_u.compatible B = true := by
    intro v' hv' vote hvote hval
    obtain ⟨k, t', hlk, hsk⟩ := pool_vote_tick_send hDiv hMono hOwner (hG v' hv') (hsv hvote) hval
    obtain ⟨-, n', sent, hrun, hsent⟩ := tick_send_of_honestSendAt hlk hsk
    obtain ⟨ht'', -, hvs, -⟩ :=
      GoldilocksCorrectness.Statements.Routines.lem14_tick_vote_walk S.C S.P S.X _ n' _ sent vote
        hrun hsent
    have hslot := pool_slot_of_stateBefore S Sched x c u s' vote (hsv hvote)
    have hvt : t' = voteTime S s' := by
      have h1 := voteTime_cast S (S.C.slot (t' : Int))
      rw [← ht''] at h1
      have h2 : t' = voteTime S (S.C.slot (t' : Int)) := by exact_mod_cast h1.symm
      rw [← hvs, hslot] at h2
      exact h2
    rw [hvt] at hlk
    exact hGv v' hv' vote ⟨k, hlk, hsk⟩
  intro v hv
  rcases Finset.mem_union.1 hv with hE | hS
  · -- an equivocator: two distinct votes of `v` in the pool, so `v` is not honest at `c`
    rw [mem_equivocators_iff] at hE
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (by omega :
      1 < (votes_by sv v).card)
    simp only [mem_votes_by_iff] at ha hb
    refine Finset.mem_sdiff.2 ⟨ha.2 ▸ hcomm a ha.1, fun hvG => hab ?_⟩
    exact unique_vote_of_owner hDiv hMono hOwner (hG v hvG) (hsv ha.1) (hsv hb.1) ha.2 hb.2
  · -- a supporter of `D`: its vote's head names a block of which `D` is an ancestor
    obtain ⟨vote, hvote, hval, -, -, H, hH, hHr, hDH⟩ := (mem_supportersOf_iff _ _ _ _ _ _).1 hS
    refine Finset.mem_sdiff.2 ⟨hval ▸ hcomm vote hvote, fun hvG => hDB ?_⟩
    obtain ⟨H_u, hHuT, hveq, hBH⟩ := hExt v hvG vote hvote hval
    obtain ⟨-, hlc, -⟩ := stepBefore_spec x hDiv hc1
    obtain ⟨-, hlv, -⟩ := stepBefore_spec x hDiv hv1
    have hHH : H = H_u := by
      refine hRoots H H_u ⟨stepBefore x c, u, ?_, by omega, ((mem_fg_to_ac_tree _ _).1 hH).1⟩
        ⟨stepBefore x (voteTime S s'), v, ?_, by omega, hHuT⟩ (by rw [hHr, hveq])
      · intro h
        exact hu (hMono _ _ (by omega) h)
      · intro h
        exact hG v hvG (hMono _ _ (by omega) h)
    rw [hHH] at hDH
    exact compatible_of_ancestorEq_compatible hDH hBH

/-- **No block that conflicts with `B` is a fast block of an updater's update of a slot
`s' ≥ s + 1`, under the compatible vote clause.** `fast_blocks_compatible_of_votes_updater` with
`VotesCompatibleAt` in place of `VotesExtendAt`: the counted set `G` (the lock holders when the
votes of slot `s' − 1` were owed inside the period, else the honest active validators of `s'`)
votes for blocks compatible with `B`, which is all `score_set_outside_ofCompat` needs.

 The one change is the premise `hVotes`; the holders' conjunct is read at a slot whose
previous votes were owed, so at most `s + k` (`owed_slot_le_k`).

The variables:
- `P`: the hypotheses; `s'`: the slot of the update; `u`: the updater.

Roots name blocks until `supportCutoff S (s' + 1)`: `score_set_outside_ofCompat` at the
update. -/
theorem fast_blocks_compatible_of_votes_updater_ofCompat {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (protocol S) Sched} {GST s : ℕ} {B : Block V} {H t₀ anchor tAwakeEnd b₀ b₁ : ℕ}
    (P : AsyncHyps S Sched x GST s B H t₀ anchor tAwakeEnd b₀ b₁) (s' : ℕ) (u : V)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s' + 1)))
    (hs' : s + 1 ≤ s') (hu : u ∈ updaterAt S Sched s')
    (hVotes : VotesCompatibleAt S Sched x s B b₀ b₁ s') :
    ∀ D ∈ (stateBefore x (supportCutoff S (s' + 1) + 1) u).A.fast_blocks,
      D.compatible B = true := by
  intro D hD
  have hΔ := one_le_Δ S
  have hwin := updaterAt_window S Sched s' u P.hMono hu
  have hdc := dutyWindowStart_succ_lt_supportCutoff S s'
  obtain ⟨hAwc, hHonc⟩ := hwin _ hdc.le le_rfl
  obtain ⟨τ, hτ, hτle⟩ := awakeSince_le_dutyWindowStart_b S Sched x (s' + 1)
    (supportCutoff S (s' + 1)) u P.hDiv P.hMono hdc (fun t' h1 h2 => (hwin t' h1 h2).1) hHonc
  obtain ⟨A'', hUpd, -, hfb, -, -⟩ :=
    update_state_of_duty S Sched x s' u P.hDiv ⟨hAwc, hHonc⟩ ⟨τ, hτ, hτle⟩
  rw [hfb] at hD
  obtain ⟨early, late, hE, -, hfast⟩ :=
    update_confirmation_fast_blocks_pass S.C S.P _ A'' _ _ (s' + 1) D (Nat.le_add_left 1 s') hUpd hD
  simp only [Nat.add_sub_cancel] at hE hfast
  by_contra hDB
  have hRΦ : GoldilocksCorrectness.Statements.Routines.RootsNameBlocksIn
      (fg_to_ac (stateBefore x (supportCutoff S (s' + 1)) u).S).tree :=
    rootsNameBlocksIn_frame_of_exec_node S Sched x (stepBefore x (supportCutoff S (s' + 1))) u
  rw [fast_test_eq_ok_true_iff _ hRΦ] at hfast
  -- the votes counted are votes of `u`'s pool of slot `s'` before the cutoff
  have hsv : {vote ∈ early | no_second_vote_in late vote = true} ⊆
      (stateBefore x (supportCutoff S (s' + 1)) u).A.pool s' := by
    intro vote hvote
    have h := ((hE vote).1 (Finset.mem_filter.1 hvote).1).1
    rwa [pool_of_keepsVotes (expireLocks_keepsVotes _ _)] at h
  have hvc : voteTime S s' ≤ supportCutoff S (s' + 1) := by
    rw [supportCutoff_eq, voteTime_eq, voteTime_eq, slotStart_eq, slotStart_eq]
    have := Nat.mul_le_mul_left (4 * Δ S) (show s' ≤ s' + 1 by omega)
    omega
  have hdisj : Disjoint (supportersOf (fg_to_ac (stateBefore x (supportCutoff S (s' + 1)) u).S)
      {vote ∈ early | no_second_vote_in late vote = true}
      {vote ∈ early | no_second_vote_in late vote = true} s' D)
      (equivocators {vote ∈ early | no_second_vote_in late vote = true}) :=
    disjoint_supportersOf_equivocators
  have hcard := Finset.card_union_of_disjoint hdisj.symm
  by_cases hOwed : VotesOwedInPeriod S b₀ b₁ s'
  · -- the votes of slot `s' − 1` were owed inside the period: the lock holders' majority
    have hs2 : s + 2 ≤ s' := by
      by_contra hc
      have h1 : s' - 1 ≤ s := by omega
      have h2 : supportCutoff S (s' - 1) < supportCutoff S (s + 1) := by
        rw [supportCutoff_eq, supportCutoff_eq, voteTime_eq, voteTime_eq, slotStart_eq,
          slotStart_eq]
        have := Nat.mul_le_mul_left (4 * Δ S) h1
        rw [Nat.mul_add, Nat.mul_one]
        omega
      have := P.hb₀
      exact absurd hOwed.1 (by omega)
    have hlt := P.hHold s' hs2 hOwed.1 hOwed.2
    have hsub := score_set_outside_ofCompat S Sched x P.hDiv P.hMono P.hOwner hvc hRoots
      hHonc (holdersAt S Sched s s')
      (fun v' hv' => (Finset.mem_sdiff.1 (Finset.mem_inter.1 hv').2).2)
      (holders_vote_compatible_of_votesCompatibleAt hVotes (owed_slot_le_k P.hb₁ hOwed))
      _ hsv hDB
    refine fast_test_fails_of_minority _ _ _ hsub hlt ?_
    rw [hcard]
    exact hfast
  · -- otherwise every honest active voter of slot `s'` voted on `B`'s chain
    have hlt := P.hSleepK (s' + 1) (by omega) (le_trans P.hAnchor (by
      rw [slotStart_eq, slotStart_eq]; exact Nat.mul_le_mul_left _ (by omega)))
    simp only [Nat.add_sub_cancel] at hlt
    have hsub := score_set_outside_ofCompat S Sched x P.hDiv P.hMono P.hOwner hvc hRoots
      hHonc (honestActiveAt S Sched s')
      (fun v' hv' => (Finset.mem_sdiff.1 hv').2)
      (active_vote_compatible_of_votesCompatibleAt hVotes hOwed) _ hsv hDB
    refine fast_test_fails_of_minority _ _ _ hsub hlt ?_
    rw [hcard]
    exact hfast

/-- **Lemma 101, the step, over the copied attestation clause and the compatible vote
clause.** `attestations_step_ofHeldEntry` with `VotesCompatibleAt` in place of `VotesExtendAt`:
the fast block an attestation's entry is taken from is compatible with `B` by
`fast_blocks_compatible_of_votes_updater_ofCompat`.

 The one change is the premise `hVotes`.

The variables:
- `P`: the hypotheses; `j`: the step.

Roots name blocks until `x[j + 1].time`: as `attestations_step_ofHeldEntry`. -/
theorem attestations_step_ofHeldEntry_ofCompat {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (protocol S) Sched} {GST s : ℕ} {B : Block V} {H t₀ anchor tAwakeEnd b₀ b₁ : ℕ}
    (P : AsyncHypsOfChainBlock S Sched x GST s B H t₀ anchor tAwakeEnd b₀ b₁) (j : ℕ)
    (hRoots : RootsNameBlocksUntil S Sched x x[j + 1].time)
    (hAtt : AttestationsCompatibleWithBeforeOfHeldEntry S Sched x B H t₀ j)
    (hVotes : ∀ s' : ℕ, s + 1 ≤ s' → voteTime S s' < x[j].time →
      VotesCompatibleAt S Sched x s B b₀ b₁ s') :
    AttestationsCompatibleWithBeforeOfHeldEntry S Sched x B H t₀ (j + 1) := by
  intro i t v a hi hl hAw hHon hsent
  rcases Nat.lt_or_ge i j with hij | hij
  · exact hAtt i t v a hij hl hAw hHon hsent
  have hij' : i = j := by omega
  subst hij'
  have hΔ := one_le_Δ S
  have htt := time_of_lbl_tickAllAwake x hl
  rcases Nat.lt_or_ge t (supportCutoff S (s + 1) + 1) with hlt | hge
  · -- a tick at or before the hand-over update: the copied hand-over facts
    have hj0 : i < stepBefore x (supportCutoff S (s + 1) + 1) :=
      (lt_stepBefore_iff x P.hDiv).2 (by omega)
    exact P.hHand.2.2.2.2.1 i t v a hj0 hl hAw hHon hsent
  · -- a later tick: the attestation's source is a fast block of the update it ran
    obtain ⟨s', E, F, ht, hv, hF, hFT, hEF, hE1, hE2, hE3⟩ :=
      attest_source_fast_block_updater_inTree S Sched x i t v a P.hDiv P.hMono hl hAw hHon hsent
    -- the entry is held by `v` before the tick, when `v` is honest
    have hET : E ∈ (x[i][v].st).S.T := ancestors_mem_T_of_exec S Sched x i v F E hFT hEF
    have hvi : AtomicHonest x i v := fun h =>
      hHon (P.hMono _ _ (by have := htt.1; omega) h)
    have hheld : inHonestTreeBy x t E := ⟨i, v, hvi, by have := htt.1; omega, hET⟩
    subst ht
    have hs' : s + 1 ≤ s' := by
      by_contra hc
      have h1 : s' + 1 ≤ s + 1 := by omega
      have h2 : supportCutoff S (s' + 1) ≤ supportCutoff S (s + 1) := by
        rw [supportCutoff_eq, supportCutoff_eq, voteTime_eq, voteTime_eq, slotStart_eq,
          slotStart_eq]
        have := Nat.mul_le_mul_left (4 * Δ S) h1
        omega
      omega
    have hvt : voteTime S s' < x[i].time := by
      have h1 : supportCutoff S (s' + 1) = voteTime S s' + 5 * Δ S := by
        rw [supportCutoff_eq, voteTime_eq, voteTime_eq, slotStart_eq, slotStart_eq,
          Nat.mul_add, Nat.mul_one]
        omega
      omega
    have hRoots' : RootsNameBlocksUntil S Sched x (supportCutoff S (s' + 1)) := by
      rw [← htt.2]
      exact hRoots
    have hFB := fast_blocks_compatible_of_votes_updater_ofCompat
      (AsyncHypsOfChainBlock.toAsyncHyps P) s' v
      hRoots' hs' hv (hVotes s' hs' hvt) F hF
    refine ⟨fun h => absurd (le_trans P.ht₀ (by omega)) (Nat.not_le.mpr h), fun _ => ?_⟩
    exact ⟨E, (compatible_iff E B).1 (compatible_of_ancestorEq_compatible hEF hFB), hE1, hE2, hE3,
      hheld⟩

/-- **An opponent of `B` at a revocation is a committee member whose vote was not for a
block compatible with `B`.** `opponent_not_extender` with "for a block it holds that is
compatible with `B`" in place of "that is `B` or a descendant of `B`": an opponent `u` of `B`
among the votes of slot `s' − 1` that `w` holds is in that slot's committee; and when `u` is
honest active at slot `s' − 1`, it is not the case that every slot-`(s' − 1)` vote `u` put on the
wire at its tick at the vote time is for a block it holds that is compatible with `B`.

 The one change is the premise of the second conjunct, `H_u.compatible B = true` in place of
`B.AncestorEq H_u`, and the last step, which reads it through `compatible_iff`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `B`: the locked block; `s'`: the slot
  of the revocation; `i`: the step of the tick; `w`: the revoking validator; `A`: the revocation's
  input; `opp`: the opponents; `u`: one of them; `tR`: the bound of the roots premise.

Roots name blocks until `voteTime S s'`: as `opponent_not_extender`. -/
theorem opponent_not_compatible (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption) {tR : ℕ}
    (hRoots : RootsNameBlocksUntil S Sched x tR) (hOwner : VotesCastByOwner S Sched x)
    (B : Block V) (s' i : ℕ) (w : V) (A : ACState V) (opp : Finset V)
    (hs' : 2 ≤ s')
    (hi : x[i].time + 1 = voteTime S s')
    (hw : AtomicHonest x i w)
    (hpool : A.pool (s' - 1) = (x[i][w].st).A.pool (s' - 1))
    (hopp : opponents A (fg_to_ac (x[i][w].st).S) (A.pool (s' - 1))
      (equivocators (A.pool (s' - 1))) B = .ok opp)
    -- the latest time the proof takes a block as held is at most the bound
    (htR : voteTime S s' ≤ tR)
    (u : V) (hu : u ∈ opp) :
    u ∈ S.P.committee (s' - 1) ∧
      (u ∈ honestActiveAt S Sched (s' - 1) →
        (∀ vote : GoldfishVote V,
          (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (s' - 1)) ∧
            (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
              x[i + 1].sent - x[i].sent) →
          ∃ H_u ∈ (stateBefore x (voteTime S (s' - 1)) u).S.T,
            vote = GoldfishVote.mk u (s' - 1) H_u.root ∧ H_u.compatible B = true) →
              False) := by
  have hΔ := one_le_Δ S
  obtain ⟨vote, hvote, hvu, hvopp⟩ := exists_vote_of_mem_opponents hopp hu
  rw [hpool] at hvote
  refine ⟨hvu ▸ pool_committee_of_exec S Sched x i w (s' - 1) vote hvote, fun hHon hExt => ?_⟩
  -- the vote is `u`'s own, sent at its tick at the vote time of slot `s' − 1`
  obtain ⟨i', hi', hnew, -, -⟩ := pool_vote_relayed S Sched x hMono i w (s' - 1) vote hvote
  have hsc : supportCutoff S (s' - 1 + 1) = voteTime S s' + Δ S := by
    rw [Nat.sub_add_cancel (by omega : 1 ≤ s')]
    exact supportCutoff_eq S s'
  have hti' : x[i'].time ≤ x[i].time := time_mono x (by omega)
  have huadv : vote.val_index ∉ Sched.adv (x[i'].time : Int) := by
    rw [hvu]
    intro h
    have hHon' := (Finset.mem_sdiff.1 hHon).2
    exact hHon' (hMono _ _ (by rw [hsc]; push_cast; omega) h)
  obtain ⟨k, t'', -, hlk, hmk⟩ := hOwner i' _ vote hnew (Or.inl rfl) huadv
  obtain ⟨-, n', sent, hrun, hsent⟩ := tick_send_of_honestSendAt hlk hmk
  obtain ⟨ht'', -, hvs, -⟩ :=
    GoldilocksCorrectness.Statements.Routines.lem14_tick_vote_walk S.C S.P S.X _ n' _ sent vote
      hrun hsent
  have hslot := pool_slot_of_exec S Sched x i w (s' - 1) vote hvote
  have hvt : t'' = voteTime S (s' - 1) := by
    have h1 := voteTime_cast S (S.C.slot (t'' : Int))
    rw [← ht''] at h1
    have h2 : t'' = voteTime S (S.C.slot (t'' : Int)) := by exact_mod_cast h1.symm
    rw [← hvs, hslot] at h2
    exact h2
  rw [hvt] at hlk
  rw [hvu] at hmk
  obtain ⟨H_u, hHuT, hveq, hBH⟩ := hExt vote ⟨k, hlk, hvu ▸ hmk⟩
  -- the vote's head names `H_u` in `w`'s frame tree, which does not conflict with `B`
  rw [opposes_eq_ok (rootsNameBlocksIn_frame_of_exec_node S Sched x i w)] at hvopp
  simp only [Except.ok.injEq, decide_eq_true_eq] at hvopp
  obtain ⟨H', hH', hroot, hconf⟩ := hvopp
  have hjb := stepBefore_spec x hDiv (show 1 ≤ voteTime S (s' - 1) by
    rw [voteTime_eq]; omega)
  have hvv : voteTime S (s' - 1) ≤ voteTime S s' := by
    rw [voteTime_eq, voteTime_eq, slotStart_eq, slotStart_eq]
    exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) _
  have hjt := hjb.2.1
  have hHuH' : H' = H_u := by
    refine hRoots H' H_u ⟨i, w, hw, by omega, ((mem_fg_to_ac_tree _ _).1 hH').1⟩
      ⟨stepBefore x (voteTime S (s' - 1)), u, ?_, by omega, hHuT⟩ (by rw [hroot, hveq])
    intro h
    have hHon' := (Finset.mem_sdiff.1 hHon).2
    refine hHon' (hMono _ _ ?_ h)
    have : voteTime S (s' - 1) ≤ voteTime S s' := by
      rw [voteTime_eq, voteTime_eq, slotStart_eq, slotStart_eq]
      exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) _
    rw [hsc]
    push_cast
    omega
  rw [hHuH', conflicts_iff, compatible_iff] at hconf
  exact hconf ((compatible_iff _ _).1 hBH)

/-- **The opponents of `B` at a revocation inside the period are fewer than half of the
committee, under the compatible vote clause.** `opponents_fewer_than_half` with `VotesCompatibleAt`
in place of `VotesExtendAt`: the opponents are committee members outside the voters whose votes
are for blocks compatible with `B` (`opponent_not_compatible`).

 The one change is the premise `hVotes`; the holders' conjunct is read at a slot `s' − 1`
whose previous votes were owed, so at most `s + k` (`owed_slot_le_k`).

The variables:
- `P`: the hypotheses; `s'`: the slot of the revocation; `i`: the step of the tick; `w`: the
  revoking validator; `A`: the revocation's input, with `w`'s pool.

Roots name blocks until `voteTime S s'`: `opponent_not_compatible` at the revocation. -/
theorem opponents_fewer_than_half_ofCompat {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (protocol S) Sched} {GST s : ℕ} {B : Block V} {H t₀ anchor tAwakeEnd b₀ b₁ : ℕ}
    (P : AsyncHyps S Sched x GST s B H t₀ anchor tAwakeEnd b₀ b₁) (s' i : ℕ) (w : V) (A : ACState V)
    (hRoots : RootsNameBlocksUntil S Sched x (voteTime S s'))
    (hs' : s + 2 ≤ s')
    (hi : x[i].time + 1 = voteTime S s')
    (hw : AtomicHonest x i w)
    (hpool : A.pool (s' - 1) = (x[i][w].st).A.pool (s' - 1))
    (hVotes : VotesCompatibleAt S Sched x s B b₀ b₁ (s' - 1)) :
    ∀ opp : Finset V, opponents A (fg_to_ac (x[i][w].st).S) (A.pool (s' - 1))
      (equivocators (A.pool (s' - 1))) B = .ok opp → 2 * |opp| < |S.P.committee (s' - 1)| := by
  intro opp hopp
  have hK := opponent_not_compatible S Sched x P.hDiv P.hMono hRoots P.hOwner B s' i w A
    opp (by omega) hi hw hpool hopp le_rfl
  by_cases hOwed : VotesOwedInPeriod S b₀ b₁ (s' - 1)
  · -- the votes of slot `s' − 2` were owed inside the period: the lock holders' majority
    have hs3 : s + 2 ≤ s' - 1 := by
      by_contra hc
      have h1 : s' - 1 - 1 ≤ s := by omega
      have h2 : supportCutoff S (s' - 1 - 1) < supportCutoff S (s + 1) := by
        rw [supportCutoff_eq, supportCutoff_eq, voteTime_eq, voteTime_eq, slotStart_eq,
          slotStart_eq]
        have := Nat.mul_le_mul_left (4 * Δ S) h1
        have := one_le_Δ S
        rw [Nat.mul_add, Nat.mul_one]
        omega
      have := P.hb₀
      exact absurd hOwed.1 (by omega)
    have hlt := P.hHold (s' - 1) hs3 hOwed.1 hOwed.2
    refine double_lt_of_sdiff (fun u hu => ?_) hlt
    obtain ⟨hC, hN⟩ := hK u hu
    refine Finset.mem_sdiff.2 ⟨hC, fun hG => hN (Finset.mem_inter.1 hG).2 ?_⟩
    exact fun vote hsend => holders_vote_compatible_of_votesCompatibleAt hVotes
      (owed_slot_le_k P.hb₁ hOwed) u hG vote hsend
  · -- otherwise every honest active voter of slot `s' − 1` voted on `B`'s chain
    have hlt := P.hSleepK s' (by omega) (le_trans P.hAnchor (by
      rw [slotStart_eq, slotStart_eq]; exact Nat.mul_le_mul_left _ (by omega)))
    refine double_lt_of_sdiff (fun u hu => ?_) hlt
    obtain ⟨hC, hN⟩ := hK u hu
    exact Finset.mem_sdiff.2 ⟨hC, fun hG => hN hG (fun vote hsend =>
      active_vote_compatible_of_votesCompatibleAt hVotes hOwed u hG vote hsend)⟩

/-- **A lock holder's vote inside the hand-over lock's life is on `B`'s chain, under the
compatible vote clause.** `holder_vote_extends_B_orTwoPast` with `VotesCompatibleAt` in place of
`VotesExtendAt` for the previous slot: the revocation keeps the lock on `B` because the opponents
of `B` are fewer than half of the committee (`opponents_fewer_than_half_ofCompat`).

 The one change is the premise `hVotes`.

The variables:
- `P`: the hypotheses; `s'`: the slot of the vote; `w`: the voter.

Roots name blocks until `voteTime S s'`: `opponents_fewer_than_half_ofCompat` at the revocation of
`w`'s tick at the vote time of slot `s'`. -/
theorem holder_vote_extends_B_orTwoPast_ofCompat {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (protocol S) Sched} {GST s : ℕ} {B : Block V} {H t₀ anchor tAwakeEnd b₀ b₁ : ℕ}
    (P : AsyncHyps S Sched x GST s B H t₀ anchor tAwakeEnd b₀ b₁) (s' : ℕ) (w : V)
    (hRoots : RootsNameBlocksUntil S Sched x (voteTime S s'))
    (hs' : s + 2 ≤ s') (hs'k : s' ≤ s + S.C.k)
    (hInv : HolderInvAt S Sched x s B (stepBefore x (voteTime S s')) w)
    (hC : CachesCompatibleWith S B H (stateBefore x (voteTime S s') w))
    (hTwo : ∀ D ∈ (stateBefore x (voteTime S s') w).S.T,
      (chainStateOf S.C B).h + 2 ≤ (chainStateOf S.C D).h → B.AncestorEq D)
    (hNC : fg_contest (stateBefore x (voteTime S s') w).S = false ∨
      (chainStateOf S.C B).h + 2 ≤ (stateBefore x (voteTime S s') w).S.h_max)
    (hVotes : VotesCompatibleAt S Sched x s B b₀ b₁ (s' - 1)) :
    ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s') ∧
        (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) →
      ∃ H_u ∈ (stateBefore x (voteTime S s') w).S.T,
        vote = GoldfishVote.mk w s' H_u.root ∧ B.AncestorEq H_u := by
  intro vote ⟨i, hl, hm⟩
  have hΔ := one_le_Δ S
  have hv₃ : voteTime S s' = slotStart S s' + Δ S := voteTime_eq S s'
  have hss : slotStart S (s' + 1) = slotStart S s' + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hslot₃ : S.C.slot ((voteTime S s' : ℕ) : Int) = s' :=
    slot_eq_of_mem S (by omega) (by omega)
  have hi : stepBefore x (voteTime S s') = i := stepBefore_eq_of_lbl x hl
  have hti := time_of_lbl_tickAllAwake x hl
  obtain ⟨hwa, n', sent, hrun, hvote⟩ := tick_send_of_honestSendAt hl hm
  have hst : stateBefore x (voteTime S s') w = x[i][w].st := by unfold stateBefore; rw [hi]
  have hA : (tickInputState x i (voteTime S s') w).A = (stateBefore x (voteTime S s') w).A := by
    rw [(tickInputState_frame x i _ w).2.1, hst]
  have hS : (tickInputState x i (voteTime S s') w).S = (stateBefore x (voteTime S s') w).S := by
    rw [(tickInputState_frame x i _ w).1, hst]
  obtain ⟨-, hvi, hvs, -, A', votes, support_votes, vbt, H_u, hrev, -, hvbt, hWalk, hhead, -⟩ :=
    GoldilocksCorrectness.Statements.Routines.lem14_tick_vote_walk S.C S.P S.X _ n' _ sent vote
      hrun hvote
  rw [hslot₃, hA, hS] at hrev hvbt
  rw [hslot₃, hS] at hWalk
  have hv : (tickInputState x i (voteTime S s') w).v = w := by
    have h := (lem11_node_invariant S Sched x i w).2.1
    unfold tickInputState
    split <;> (try rw [wake_eq]) <;> exact h
  rw [hv] at hvi
  rw [hslot₃] at hvs
  have hvote' : vote = GoldfishVote.mk w s' H_u.root := by
    rw [← hvi, ← hvs, ← hhead]
  -- the vote's block is held
  have hHT : H_u ∈ (stateBefore x (voteTime S s') w).S.T := by
    rcases ghost_mem_tree_or_eq ((goldfish_fork_choice_eq ..).symm.trans hWalk) with h | h
    · rw [h]
      exact get_anchor_mem_T _ _ _
        (lem11_node_invariant S Sched x (stepBefore x (voteTime S s')) w).1.2.2.2.1
        (lem57_justification_cache_and_record S Sched x (stepBefore x (voteTime S s')) w).2.2.1
    · have h1 := ((mem_viable_tree_iff _ _ _).1 h).1
      have h2 := ((mem_voter_block_tree_iff S.C _ _ s' vbt hvbt H_u).1 h1).1
      exact ((mem_fg_to_ac_tree _ _).1 h2).1
  -- the walk ends at the anchor or a descendant of it
  have hAH : (get_anchor A' (fg_to_ac (stateBefore x (voteTime S s') w).S)
      ((voteTime S s' : ℕ) : Int)).AncestorEq H_u := by
    rcases ghost_spec ((goldfish_fork_choice_eq ..).symm.trans hWalk) with hH | ⟨hAH, -⟩
    · rw [hH]
      exact ancestorEq_refl _
    · exact hAH
  refine ⟨H_u, hHT, hvote', ancestorEq_trans ?_ hAH⟩
  -- the anchor of the revoked state is `B` or a descendant of `B`
  rw [hst] at hrev hC hTwo hNC ⊢
  rw [hi] at hInv
  by_cases hgen : B = Block.genesis
  · rw [hgen]
    exact genesis_ancestorEq _
  have hlt : ((x[i].time : ℕ) : Int) < ((voteTime S s' : ℕ) : Int) := by
    have h := hti.1
    omega
  have hwi : AtomicHonest x i w := by
    intro h
    exact (Finset.mem_sdiff.1 hwa).2 (P.hMono _ _ (le_of_lt hlt) h)
  have hBT : B ∈ (x[i][w].st).S.T :=
    ancestors_mem_T_of_exec S Sched x i w _ B
      hInv.2.2.1 hInv.2.1
  have hJB := hC.2.1
  have hFJ := hC.2.2.2.2
  by_cases hBΦ : B ∈ (fg_to_ac (x[i][w].st).S).tree
  · -- the entry on `B` is live at the vote time, and the revocation keeps it
    have htd : ((voteTime S s' : ℕ) : Int) < S.C.t_ (s + S.C.k) + 5 * S.C.Δ := by
      have h1 : voteTime S s' ≤ voteTime S (s + S.C.k) := by
        rw [voteTime_eq, voteTime_eq, slotStart_eq, slotStart_eq]
        exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hs'k) _
      have h2 := voteTime_cast S (s + S.C.k)
      have h3 : ((voteTime S s' : ℕ) : Int) ≤ ((voteTime S (s + S.C.k) : ℕ) : Int) := by
        exact_mod_cast h1
      have h4 := S.C.Δ_pos
      have key : ∀ a b c δ : Int, a ≤ b → b = c + δ → 0 < δ → a < c + 5 * δ := by
        intro a b c δ h1 h2 h3; omega
      exact key _ _ _ _ h3 h2 h4
    have hlive : is_live (fg_to_ac (x[i][w].st).S) ((voteTime S s' : ℕ) : Int)
        (LockEntry.mk B (S.C.t_ (s + S.C.k) + 5 * S.C.Δ)) = true := by
      simp only [is_live_iff]
      exact ⟨htd, hBΦ⟩
    -- `B` is in the frame's tree, so not a strict ancestor of the finalized block: `w` holds the
    -- entry on `B`
    have hent : LockEntry.mk B (S.C.t_ (s + S.C.k) + 5 * S.C.Δ) ∈ (x[i][w].st).A.lock_entries :=
      hInv.1.resolve_right fun h => by
        obtain ⟨hne, hBF⟩ := ancestorStrict_iff.1 h
        exact hne (ancestorEq_antisymm hBF ((mem_fg_to_ac_tree _ _).1 hBΦ).2)
    have he : LockEntry.mk B (S.C.t_ (s + S.C.k) + 5 * S.C.Δ) ∈
        (expireLocks (x[i][w].st).A ((voteTime S s' : ℕ) : Int)).lock_entries :=
      Finset.mem_filter.2 ⟨hent, htd⟩
    have hkeep := GoldilocksCorrectness.Statements.Routines.revoke_locks_keeps_entry S.P _ A' _ _ s' _ (show (s' : ℕ) ≠ 0 by omega) hrev he hlive hgen
      (opponents_fewer_than_half_ofCompat P s' i w _ hRoots hs' hti.1 hwi
        (pool_of_keepsVotes (expireLocks_keepsVotes _ _) _) hVotes)
    -- every live entry of the revoked state is on a block compatible with `B`
    have hlocks : ∀ e ∈ A'.lock_entries,
        is_live (fg_to_ac (x[i][w].st).S) ((voteTime S s' : ℕ) : Int) e = true →
        e.B.compatible B = true := by
      intro e heA _
      obtain ⟨e₁, he₁, hl₁, -, heB, -⟩ :=
        GoldilocksCorrectness.Statements.Routines.lem38_revoke_locks_entries_moved S.P _ A' _ _ s'
          (show 1 ≤ (s' : ℕ) by omega) hrev e heA
      have he₁' := (Finset.mem_filter.1 he₁).1
      have hl₁' : is_live (fg_to_ac (x[i][w].st).S) (x[i].time : Int) e₁ = true := by
        simp only [is_live_iff] at hl₁ ⊢
        refine ⟨?_, hl₁.2⟩
        exact lt_trans hlt hl₁.1
      exact compatible_of_ancestorEq_compatible heB (hInv.2.2.2.2 e₁ he₁' hl₁')
    have hInvN := (lem11_node_invariant S Sched x i w).1
    exact anchor_extends_B_of_inv_orTwoPast S { x[i][w].st with A := A' } B ((voteTime S s' : ℕ) : Int) H
      (S.C.t_ (s + S.C.k) + 5 * S.C.Δ) hkeep hlive hlocks hC hTwo hNC
      (cachesWitnessed_of_exec S Sched x i w).2.1 hInvN.2.2.2.2.2.2.2.2.2.1.1 hInvN.2.2.2.2.2.1
  · -- `B` is a strict ancestor of the finalized block, an ancestor of the anchor
    have hFB : ¬ (x[i][w].st).S.F.AncestorEq B := fun h =>
      hBΦ ((mem_fg_to_ac_tree _ _).2 ⟨hBT, h⟩)
    have hBF : B.AncestorEq (x[i][w].st).S.F := by
      rcases hJB with hJB | hBJ
      · exact absurd (ancestorEq_trans hFJ hJB) hFB
      · rcases ancestorEq_compatible hFJ hBJ with h | h
        · exact absurd h hFB
        · exact h
    exact ancestorEq_trans hBF (ancestorEq_trans
      (GoldilocksCorrectness.Proofs.Routines.F_ancestorEq_get_fc_root _ hFJ)
      (by rw [← fc_root_eq]
          exact fc_root_ancestorEq_get_anchor A' (fg_to_ac (x[i][w].st).S) ((voteTime S s' : ℕ) : Int)))

section Steps

variable {S : Setup V} {Sched : Schedule V}

/-- **Lemma 100, the step of the lock holder's invariant, under the compatible vote
clause.** `holderInv_step` with `VotesCompatibleAt` in place of `VotesExtendAt`: the revocation
keeps the lock on `B` by `opponents_fewer_than_half_ofCompat`.

 The one change is the premise `hVotes`.

The variables:
- `P`: the hypotheses; `j`: the step; `w`: the lock holder.

Roots name blocks until `x[j + 1].time`: as `holderInv_step`. -/
theorem holderInv_step_ofCompat {GST s : ℕ} {B : Block V} {H t₀ anchor tAwakeEnd b₀ b₁ : ℕ}
    {x : AtomicExec (protocol S) Sched}
    (P : AsyncHyps S Sched x GST s B H t₀ anchor tAwakeEnd b₀ b₁) (j : ℕ) (w : V)
    (hRoots : RootsNameBlocksUntil S Sched x x[j + 1].time)
    (hj : supportCutoff S (s + 1) < x[j + 1].time)
    (hjd : x[j + 1].time < voteTime S (s + S.C.k + 1))
    (hInv : HolderInvAt S Sched x s B j w)
    (hC : CachesCompatibleWith S B H (x[j][w].st))
    (hVotes : ∀ s' : ℕ, s + 1 ≤ s' → voteTime S s' < x[j + 1].time →
      VotesCompatibleAt S Sched x s B b₀ b₁ s') :
    HolderInvAt S Sched x s B (j + 1) w := by
  have hΔ := one_le_Δ S
  -- the deadline of the entry on `B` is the vote time of slot `s + k + 1`
  have hdd : ((voteTime S (s + S.C.k + 1) : ℕ) : Int) = S.C.t_ (s + S.C.k) + 5 * S.C.Δ := by
    rw [voteTime_cast]
    simp only [t_eq_mul]
    push_cast
    rw [Int.mul_add]
    have key : ∀ a d : Int, a + 4 * d * 1 + d = a + 5 * d := fun a d => by omega
    exact key _ _
  have htd : ((x[j + 1].time : ℕ) : Int) < S.C.t_ (s + S.C.k) + 5 * S.C.Δ := by
    rw [← hdd]
    exact_mod_cast hjd
  have htj : x[j].time ≤ x[j + 1].time := time_mono x (Nat.le_succ j)
  have hFF : (x[j][w].st).S.F.AncestorEq (x[j + 1][w].st).S.F := F_ancestorEq_of_le x w (Nat.le_succ j)
  have hBT : B ∈ (x[j][w].st).S.T :=
    ancestors_mem_T_of_exec S Sched x j w _ B hInv.2.2.1 hInv.2.1
  -- `B` is in the frame's tree at `j`, or a strict ancestor of the finalized block
  have hdich : B ∈ (fg_to_ac (x[j][w].st).S).tree ∨
      (B.AncestorEq (x[j][w].st).S.F ∧ B ≠ (x[j][w].st).S.F) := by
    by_cases hFB : (x[j][w].st).S.F.AncestorEq B
    · exact Or.inl ((mem_fg_to_ac_tree _ _).2 ⟨hBT, hFB⟩)
    · refine Or.inr ⟨?_, fun h => hFB (by rw [← h]; exact ancestorEq_refl _)⟩
      rcases hC.2.1 with hJB | hBJ
      · exact absurd (ancestorEq_trans hC.2.2.2.2 hJB) hFB
      · rcases ancestorEq_compatible hC.2.2.2.2 hBJ with h | h
        · exact absurd h hFB
        · exact h
  -- a strict ancestor of the finalized block stays one
  have hstrict : B.AncestorEq (x[j][w].st).S.F → B ≠ (x[j][w].st).S.F →
      B.ancestorStrict (x[j + 1][w].st).S.F = true := by
    intro h1 h2
    refine ancestorStrict_iff.2 ⟨fun h => h2 (ancestorEq_antisymm h1 ?_), ancestorEq_trans h1 hFF⟩
    rw [h]
    exact hFF
  have hInv1 : LockEntry.mk B (S.C.t_ (s + S.C.k) + 5 * S.C.Δ) ∈ (x[j][w].st).A.lock_entries ∨
      (B.AncestorEq (x[j][w].st).S.F ∧ B ≠ (x[j][w].st).S.F) := by
    rcases hInv.1 with h | h
    · exact Or.inl h
    · obtain ⟨h1, h2⟩ := ancestorStrict_iff.1 h
      exact Or.inr ⟨h2, h1⟩
  -- in the frame's tree, `w` holds the entry on `B`
  have hent : B ∈ (fg_to_ac (x[j][w].st).S).tree →
      LockEntry.mk B (S.C.t_ (s + S.C.k) + 5 * S.C.Δ) ∈ (x[j][w].st).A.lock_entries :=
    fun hBΦ => hInv1.resolve_right fun ⟨h1, h2⟩ =>
      h2 (ancestorEq_antisymm h1 ((mem_fg_to_ac_tree _ _).1 hBΦ).2)
  -- an entry `w` held at `j` and live at `j + 1` was live at `j`
  have hback : ∀ e ∈ (x[j][w].st).A.lock_entries,
      is_live (fg_to_ac (x[j + 1][w].st).S) (x[j + 1].time : Int) e = true →
      is_live (fg_to_ac (x[j][w].st).S) (x[j].time : Int) e = true := by
    intro e he hl
    simp only [is_live_iff] at hl ⊢
    have hT := (mem_fg_to_ac_tree _ _).1 hl.2
    refine ⟨lt_of_le_of_lt (by exact_mod_cast htj) hl.1, (mem_fg_to_ac_tree _ _).2
      ⟨lock_entry_mem_T_of_exec S Sched x w j e he, ancestorEq_trans hFF hT.2⟩⟩
  -- with `B` an ancestor of the finalized block, every live entry is on a descendant of `B`
  have hc5strict : B.AncestorEq (x[j][w].st).S.F → ∀ e ∈ (x[j + 1][w].st).A.lock_entries,
      is_live (fg_to_ac (x[j + 1][w].st).S) (x[j + 1].time : Int) e = true →
      e.B.compatible B = true := by
    intro hBF e _ hl
    simp only [is_live_iff] at hl
    exact (compatible_iff _ _).2 (Or.inr (ancestorEq_trans (ancestorEq_trans hBF hFF)
      ((mem_fg_to_ac_tree _ _).1 hl.2).2))
  have hc2T := latest_confirmed_mem_T_of_exec x (j + 1) w
  rcases step_cases_period x j w with ⟨hLE, hLC, hFB⟩ | ⟨t, hl, hmem, hcase⟩
  · -- the step keeps the lock entries, the record and the fast blocks
    refine ⟨?_, by rw [hLC]; exact hInv.2.1, hc2T, by rw [hFB]; exact hInv.2.2.2.1, ?_⟩
    · rcases hInv1 with h | ⟨h1, h2⟩
      · exact Or.inl (by rw [hLE]; exact h)
      · exact Or.inr (hstrict h1 h2)
    · intro e he hl
      rw [hLE] at he
      exact hInv.2.2.2.2 e he (hback e he hl)
  obtain ⟨hti1, hti2⟩ := time_of_lbl_tickAllAwake x hl
  have htt : ((t : ℕ) : Int) < S.C.t_ (s + S.C.k) + 5 * S.C.Δ := by
    rw [← hti2]
    exact htd
  have hjt : ((x[j].time : ℕ) : Int) ≤ ((t : ℕ) : Int) := by exact_mod_cast (by omega : x[j].time ≤ t)
  rcases hcase with ⟨hLE, hLC, hFB⟩ | ⟨hvt, A', hA', hLE, hLC, hFB⟩ |
      ⟨hct, A'', hA'', hLE, hLC, hFB⟩
  · -- the tick deletes the expired entries only
    refine ⟨?_, by rw [hLC]; exact hInv.2.1, hc2T, by rw [hFB]; exact hInv.2.2.2.1, ?_⟩
    · rcases hInv1 with h | ⟨h1, h2⟩
      · exact Or.inl (by rw [hLE]; exact Finset.mem_filter.2 ⟨h, htt⟩)
      · exact Or.inr (hstrict h1 h2)
    · intro e he hl
      rw [hLE] at he
      have he' := (Finset.mem_filter.1 he).1
      exact hInv.2.2.2.2 e he' (hback e he' hl)
  · -- the revocation at the vote time of the slot `s'` of `t`
    obtain ⟨s', hs'⟩ : ∃ s' : ℕ, S.C.slot (t : Int) = s' := ⟨_, rfl⟩
    have hvt' : t = voteTime S s' := by
      have h1 := voteTime_cast S s'
      rw [hs'] at hvt
      have : (t : Int) = ((voteTime S s' : ℕ) : Int) := by rw [h1]; exact hvt
      exact_mod_cast this
    rw [hs'] at hA'
    have hss : ∀ a b : ℕ, a ≤ b → slotStart S a ≤ slotStart S b := fun a b hab => by
      rw [slotStart_eq, slotStart_eq]
      exact Nat.mul_le_mul_left _ hab
    have hs2 : s + 2 ≤ s' := by
      by_contra hc
      have h1 := hss s' (s + 1) (by omega)
      have h2 := supportCutoff_eq S (s + 1)
      have h3 := voteTime_eq S (s + 1)
      have h4 := voteTime_eq S s'
      rw [hti2] at hj
      omega
    have hvlt : voteTime S (s' - 1) < x[j + 1].time := by
      rw [hti2, hvt', voteTime_eq, voteTime_eq, slotStart_eq, slotStart_eq]
      have := Nat.mul_lt_mul_of_pos_left (show s' - 1 < s' by omega) (by omega : 0 < 4 * Δ S)
      omega
    have hwj : AtomicHonest x j w := fun h =>
      (Finset.mem_sdiff.1 hmem).2 (P.hMono _ _ hjt h)
    refine ⟨?_, by rw [hLC]; exact hInv.2.1, hc2T, by rw [hFB]; exact hInv.2.2.2.1, ?_⟩
    · rcases hdich with hBΦ | ⟨h1, h2⟩
      · left
        have he₀ := hent hBΦ
        have hlive : is_live (fg_to_ac (x[j][w].st).S) (t : Int)
            (LockEntry.mk B (S.C.t_ (s + S.C.k) + 5 * S.C.Δ)) = true := by
          simp only [is_live_iff]
          exact ⟨htt, hBΦ⟩
        have he : LockEntry.mk B (S.C.t_ (s + S.C.k) + 5 * S.C.Δ) ∈
            (expireLocks (x[j][w].st).A t).lock_entries := Finset.mem_filter.2 ⟨he₀, htt⟩
        rw [hLE]
        exact GoldilocksCorrectness.Proofs.Routines.revoke_locks_keeps_entry S.P _ A' _ _ s' _ (show (s' : ℕ) ≠ 0 by omega) hA' he
          hlive (lock_entry_ne_genesis_of_exec x w j _ he₀)
          (opponents_fewer_than_half_ofCompat P s' j w _ (hRoots.mono (by omega)) hs2
            (by rw [← hvt']; exact hti1) hwj (pool_of_keepsVotes (expireLocks_keepsVotes _ _) _)
            (hVotes (s' - 1) (by omega) hvlt))
      · exact Or.inr (hstrict h1 h2)
    · intro e he hl
      rw [hLE] at he
      obtain ⟨e₁, he₁, hl₁, -, heB, -⟩ :=
        GoldilocksCorrectness.Statements.Routines.lem38_revoke_locks_entries_moved S.P _ A' _ _
          s' (show 1 ≤ (s' : ℕ) by omega) hA' e he
      have he₁' := (Finset.mem_filter.1 he₁).1
      have hl₁' : is_live (fg_to_ac (x[j][w].st).S) (x[j].time : Int) e₁ = true := by
        simp only [is_live_iff] at hl₁ ⊢
        exact ⟨lt_of_le_of_lt hjt hl₁.1, hl₁.2⟩
      exact compatible_of_ancestorEq_compatible heB (hInv.2.2.2.2 e₁ he₁' hl₁')
  · -- the confirmation update at the support cutoff of the slot of `t`
    have hs0 : S.C.slot (t : Int) ≠ 0 := by
      intro h0
      rw [h0] at hct
      have h1 := supportCutoff_cast S (s + 1)
      have h3 : @Eq Int (S.C.t_ 0) 0 := by
        rw [t_eq_mul]
        simp
      have h2 : @LE.le Int _ 0 (S.C.t_ (s + 1)) := by
        rw [t_eq_mul]
        have := S.C.Δ_pos
        positivity
      have h4 : ((supportCutoff S (s + 1) : ℕ) : Int) < ((t : ℕ) : Int) := by
        rw [← hti2]
        exact_mod_cast hj
      have h5 : @LT.lt Int _ 0 S.C.Δ := S.C.Δ_pos
      have h6 : @Eq Int (t : Int) (S.C.t_ 0 + 2 * S.C.Δ) := hct
      have h7 : @Eq Int ((supportCutoff S (s + 1) : ℕ) : Int) (S.C.t_ (s + 1) + 2 * S.C.Δ) := h1
      omega
    rcases hdich with hBΦ | ⟨h1, h2⟩
    · -- `B` in the frame's tree: the update under the live lock on `B`
      have he₀ := hent hBΦ
      have hlive : is_live (fg_to_ac (x[j][w].st).S) (t : Int)
          (LockEntry.mk B (S.C.t_ (s + S.C.k) + 5 * S.C.Δ)) = true := by
        simp only [is_live_iff]
        exact ⟨htt, hBΦ⟩
      have he : LockEntry.mk B (S.C.t_ (s + S.C.k) + 5 * S.C.Δ) ∈
          (expireLocks (x[j][w].st).A t).lock_entries := Finset.mem_filter.2 ⟨he₀, htt⟩
      have hin : (expireLocks (x[j][w].st).A t).latest_confirmed ∈
          (fg_to_ac (x[j][w].st).S).tree :=
        (mem_fg_to_ac_tree _ _).2
          ⟨hInv.2.2.1, ancestorEq_trans ((mem_fg_to_ac_tree _ _).1 hBΦ).2 hInv.2.1⟩
      obtain ⟨hR1, hR2, hR3, -⟩ :=
        GoldilocksCorrectness.Proofs.Routines.update_confirmation_with_live_lock_of_mem S.C S.P _
          A'' _ _ _ B _ hs0 hA'' he hlive hin hInv.2.1
      have hsub := (update_confirmation_in_frame S.C S.P _ A'' _ _ _ hA'').2.2.2
      refine ⟨Or.inl (by rw [hLE]; exact hsub he), by rw [hLC]; exact hR1, hc2T,
        by rw [hFB]; exact hR2, ?_⟩
      intro e he' hl
      rw [hLE] at he'
      rcases hR3 e he' with h | h
      · have h' := (Finset.mem_filter.1 h).1
        exact hInv.2.2.2.2 e h' (hback e h' hl)
      · exact h
    · -- `B` a strict ancestor of the finalized block: the update stays among its descendants
      obtain ⟨hR1, hR2, -, -⟩ := update_confirmation_in_frame S.C S.P _ A'' _ _ _ hA''
      have hΦF : (fg_to_ac (x[j][w].st).S).F = (x[j][w].st).S.F := fg_to_ac_F _
      rw [hΦF] at hR1
      refine ⟨Or.inr (hstrict h1 h2), ?_, hc2T, ?_, hc5strict h1⟩
      · rw [hLC]
        rcases hR1 with h | h
        · rw [h]
          exact hInv.2.1
        · exact ancestorEq_trans h1 h
      · rw [hFB]
        intro D hD
        rcases hR2 D hD with h | h
        · exact hInv.2.2.2.1 D h
        · exact (compatible_iff _ _).2
            (Or.inr (ancestorEq_trans h1 ((mem_fg_to_ac_tree _ _).1 h).2))

end Steps

/-! ## A reader of the original vote clause -/

/-- **No block that conflicts with `B` is a fast block of an honest active validator's update of
a slot `s' ≥ s + 1`.** The proof; the audited statement is in
`Statements/Executions/PeriodCompatCopiesStatements.lean`. `fast_blocks_compatible_of_votes_updater_ofCompat`,
an honest active validator of `s'` being an updater of `s'` (`honestActiveAt_subset_updaterAt`), and
the votes' `VotesExtendAt` giving `VotesCompatibleAt` (`votesCompatibleAt_of_votesExtendAt`).

 the copy is on this page, which
imports that one.

The variables:
- `P`: the hypotheses; `s'`: the slot of the update; `u`: the validator.

Roots name blocks until `supportCutoff S (s' + 1)`: `fast_blocks_compatible_of_votes_updater_ofCompat`. -/
theorem fast_blocks_compatible_of_votes {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (protocol S) Sched} {GST s : ℕ} {B : Block V} {H t₀ anchor tAwakeEnd b₀ b₁ : ℕ}
    (P : AsyncHyps S Sched x GST s B H t₀ anchor tAwakeEnd b₀ b₁) (s' : ℕ) (u : V)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s' + 1)))
    (hs' : s + 1 ≤ s') (hu : u ∈ honestActiveAt S Sched s')
    (hVotes : VotesExtendAt S Sched x s B b₀ b₁ s') :
    ∀ D ∈ (stateBefore x (supportCutoff S (s' + 1) + 1) u).A.fast_blocks,
      D.compatible B = true :=
  fast_blocks_compatible_of_votes_updater_ofCompat P s' u hRoots hs'
    (honestActiveAt_subset_updaterAt S Sched s' hu) (votesCompatibleAt_of_votesExtendAt S Sched x hVotes)

end GoldilocksCorrectness.Proofs.Executions
