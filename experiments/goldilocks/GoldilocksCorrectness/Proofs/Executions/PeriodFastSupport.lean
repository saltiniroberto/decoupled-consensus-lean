module
public import GoldilocksCorrectness.Proofs.Executions.PeriodChainBlock

@[expose] public section

/-! kit statements, new. The audited statement is in
`Statements/Executions/PeriodFastSupportStatements.lean`.

- `tick_vote_held_block`: a Goldfish vote an honest validator's tick sent is for the vote time of
  its slot, for a block the validator held before that tick;
- `fast_block_has_honest_supporter`: a block an honest updater fast-confirmed at the update of
  slot `s''` is an ancestor of, or is, the block some honest active committee member of `s''`
  voted for, which that member held at the vote time.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff)

open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_succ_lt_supportCutoff
  expireLocks_keepsVotes fast_test_eq_ok_true_iff goldfish_fork_choice_eq mem_viable_tree_iff
  mem_votes_by_iff pool_of_keepsVotes wake_eq)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction AtomicHonest Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Proofs.Routines
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn expireLocks)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

-- An index `x[i]` into an execution has the valid-index predicate `fun _ _ => True`; this rule,
-- local to the file, proves it at once.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- **A Goldfish vote an honest tick sent is for a block held before the tick.** When the step
`k` ticks every awake validator at `t'` and puts on the wire `v`'s Goldfish vote `vote` for slot
`s`, then `t'` is the vote time of slot `s`, and `vote` is `v`'s vote for slot `s` whose head is
the root of a block `H_v` that `v` held before its tick at that vote time.

Why: Lemma 14 (`lem14_tick_vote_walk`): the tick at `t'` sends a vote only at the vote time of the
slot of `t'`, for that slot, as the validator's, with the head the root of the block the fork
choice's walk ends at; that block is the anchor of the revoked state or a block of the voter
tree, both held. The proof of `holder_vote_extends_B_orTwoPast`, up to `hHT`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `k`: the step of the tick; `t'`: its
  time; `v`: the voter; `s`: the slot of the vote; `vote`: the vote. -/
theorem tick_vote_held_block (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) {k t' : ℕ} {v : V} {s : ℕ} {vote : GoldfishVote V}
    (hl : x.lbl k = AtomicAction.tickAllAwake t')
    (hm : (⟨v, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
      x[k + 1].sent - x[k].sent)
    (hs : vote.slot = s) :
    t' = voteTime S s ∧ ∃ H_v ∈ (stateBefore x (voteTime S s) v).S.T,
      vote = GoldfishVote.mk v s H_v.root := by
  obtain ⟨-, n', sent, hrun, hvote⟩ := tick_send_of_honestSendAt hl hm
  obtain ⟨ht'', hvi, hvs, -, A', votes, support_votes, vbt, H_u, hrev, -, hvbt, hWalk, hhead, -⟩ :=
    GoldilocksCorrectness.Statements.Routines.lem14_tick_vote_walk S.C S.P S.X _ n' _ sent vote
      hrun hvote
  have hvt : t' = voteTime S s := by
    have h1 := voteTime_cast S (S.C.slot (t' : Int))
    rw [← ht''] at h1
    have h2 : t' = voteTime S (S.C.slot (t' : Int)) := by exact_mod_cast h1.symm
    rw [← hvs, hs] at h2
    exact h2
  subst hvt
  refine ⟨rfl, ?_⟩
  have hslot₃ : S.C.slot ((voteTime S s : ℕ) : Int) = s := by rw [← hvs, hs]
  have hi : stepBefore x (voteTime S s) = k := stepBefore_eq_of_lbl x hl
  have hst : stateBefore x (voteTime S s) v = x[k][v].st := by unfold stateBefore; rw [hi]
  have hA : (tickInputState x k (voteTime S s) v).A = (stateBefore x (voteTime S s) v).A := by
    rw [(tickInputState_frame x k _ v).2.1, hst]
  have hS : (tickInputState x k (voteTime S s) v).S = (stateBefore x (voteTime S s) v).S := by
    rw [(tickInputState_frame x k _ v).1, hst]
  rw [hslot₃, hA, hS] at hvbt
  rw [hslot₃, hS] at hWalk
  have hv : (tickInputState x k (voteTime S s) v).v = v := by
    have h := (lem11_node_invariant S Sched x k v).2.1
    unfold tickInputState
    split <;> (try rw [wake_eq]) <;> exact h
  rw [hv] at hvi
  refine ⟨H_u, ?_, ?_⟩
  · rcases ghost_mem_tree_or_eq ((goldfish_fork_choice_eq ..).symm.trans hWalk) with h | h
    · rw [h]
      exact get_anchor_mem_T _ _ _
        (lem11_node_invariant S Sched x (stepBefore x (voteTime S s)) v).1.2.2.2.1
        (lem57_justification_cache_and_record S Sched x (stepBefore x (voteTime S s)) v).2.2.1
    · have h1 := ((mem_viable_tree_iff _ _ _).1 h).1
      have h2 := ((mem_voter_block_tree_iff S.C _ _ s vbt hvbt H_u).1 h1).1
      exact ((mem_fg_to_ac_tree _ _).1 h2).1
  · rw [← hvi, ← hs, ← hhead]

/-- **Kit fact K2: a fast block has an honest active supporter who held it.** The proof; the
audited statement is in `Statements/Executions/PeriodFastSupportStatements.lean`. The proof of
`fast_blocks_compatible_of_votes_updater` up to the fast test, which `D` passed: the committee of
`s''` is at most twice `D`'s score, the equivocators and the supporters of `D` among the votes
counted. If none of them were in `honestActiveAt S Sched s''`, they would all be committee members
outside it, which `CommitteeSleepiness` makes fewer than half of the committee
(`fast_test_fails_of_minority`). An equivocator in it is impossible (one vote per honest owner,
`unique_vote_of_owner`); so a supporter `v` in it has a counted vote whose head names a block of
`u'`'s frame tree that is `D` or a descendant of `D`, and that vote is the one `v`'s tick sent at
the vote time of `s''`, for a block `H_v` it held (`tick_vote_held_block`); the two blocks have one
root, so are one block.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `anchor`: the time from which
  committee sleepiness holds; `s''`: the slot of the votes; `u'`: the updater. -/
theorem fast_block_has_honest_supporter (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (anchor s'' : ℕ) (u' : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hOwner : VotesCastByOwner S Sched x)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s'' + 1)))
    (hSleepK : CommitteeSleepiness S Sched anchor) (hAnchor : anchor ≤ slotStart S (s'' + 1))
    (hu' : u' ∈ updaterAt S Sched s'') :
    ∀ D ∈ (stateBefore x (supportCutoff S (s'' + 1) + 1) u').A.fast_blocks,
      ∃ v ∈ honestActiveAt S Sched s'' ∩ S.P.committee s'',
        ∃ H_v ∈ (stateBefore x (voteTime S s'') v).S.T, D.AncestorEq H_v := by
  intro D hD
  have hΔ := one_le_Δ S
  have hwin := updaterAt_window S Sched s'' u' hMono hu'
  have hdc := dutyWindowStart_succ_lt_supportCutoff S s''
  obtain ⟨hAwc, hHonc⟩ := hwin _ hdc.le le_rfl
  obtain ⟨τ, hτ, hτle⟩ := awakeSince_le_dutyWindowStart_b S Sched x (s'' + 1)
    (supportCutoff S (s'' + 1)) u' hDiv hMono hdc (fun t' h1 h2 => (hwin t' h1 h2).1) hHonc
  obtain ⟨A'', hUpd, -, hfb, -, -⟩ :=
    update_state_of_duty S Sched x s'' u' hDiv ⟨hAwc, hHonc⟩ ⟨τ, hτ, hτle⟩
  rw [hfb] at hD
  obtain ⟨early, late, hE, -, hfast⟩ :=
    update_confirmation_fast_blocks_pass S.C S.P _ A'' _ _ (s'' + 1) D (Nat.le_add_left 1 s'')
      hUpd hD
  simp only [Nat.add_sub_cancel] at hE hfast
  have hRΦ : RootsNameBlocksIn
      (fg_to_ac (stateBefore x (supportCutoff S (s'' + 1)) u').S).tree :=
    rootsNameBlocksIn_frame_of_exec_node S Sched x (stepBefore x (supportCutoff S (s'' + 1))) u'
  rw [fast_test_eq_ok_true_iff _ hRΦ] at hfast
  -- the votes counted are votes of `u'`'s pool of slot `s''` before the cutoff
  have hsv : {vote ∈ early | no_second_vote_in late vote = true} ⊆
      (stateBefore x (supportCutoff S (s'' + 1)) u').A.pool s'' := by
    intro vote hvote
    have h := ((hE vote).1 (Finset.mem_filter.1 hvote).1).1
    rwa [pool_of_keepsVotes (expireLocks_keepsVotes _ _)] at h
  have hvc : voteTime S s'' < supportCutoff S (s'' + 1) := by
    rw [supportCutoff_eq, voteTime_eq, voteTime_eq, slotStart_eq, slotStart_eq]
    have := Nat.mul_le_mul_left (4 * Δ S) (show s'' ≤ s'' + 1 by omega)
    omega
  have hc1 : 1 ≤ supportCutoff S (s'' + 1) := by omega
  have hdisj : Disjoint (supportersOf (fg_to_ac (stateBefore x (supportCutoff S (s'' + 1)) u').S)
      {vote ∈ early | no_second_vote_in late vote = true}
      {vote ∈ early | no_second_vote_in late vote = true} s'' D)
      (equivocators {vote ∈ early | no_second_vote_in late vote = true}) :=
    disjoint_supportersOf_equivocators
  have hcard := Finset.card_union_of_disjoint hdisj.symm
  have hlt := hSleepK (s'' + 1) (by omega) hAnchor
  simp only [Nat.add_sub_cancel] at hlt
  have hcomm : ∀ vote ∈ {vote ∈ early | no_second_vote_in late vote = true},
      vote.val_index ∈ S.P.committee s'' := fun vote hvote =>
    pool_committee_of_exec S Sched x (stepBefore x (supportCutoff S (s'' + 1))) u' s'' vote
      (hsv hvote)
  -- a member of `honestActiveAt S Sched s''` is honest at the cutoff
  have hHA : ∀ v ∈ honestActiveAt S Sched s'', v ∉ Sched.adv
      ((supportCutoff S (s'' + 1) : ℕ) : Int) := fun v hv => (Finset.mem_sdiff.1 hv).2
  by_contra hno
  have hsub : equivocators {vote ∈ early | no_second_vote_in late vote = true} ∪
      supportersOf (fg_to_ac (stateBefore x (supportCutoff S (s'' + 1)) u').S)
        {vote ∈ early | no_second_vote_in late vote = true}
        {vote ∈ early | no_second_vote_in late vote = true} s'' D ⊆
      S.P.committee s'' \ honestActiveAt S Sched s'' := by
    intro v hv
    rcases Finset.mem_union.1 hv with hEq | hS
    · -- an equivocator: two distinct votes of `v` in the pool, so `v` is not honest
      rw [mem_equivocators_iff] at hEq
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (by omega :
        1 < (votes_by {vote ∈ early | no_second_vote_in late vote = true} v).card)
      obtain ⟨ha1, ha2⟩ := (mem_votes_by_iff _ _ _).1 ha
      obtain ⟨hb1, hb2⟩ := (mem_votes_by_iff _ _ _).1 hb
      refine Finset.mem_sdiff.2 ⟨ha2 ▸ hcomm a ha1, fun hvG => hab ?_⟩
      exact unique_vote_of_owner hDiv hMono hOwner (hHA v hvG) (hsv ha1) (hsv hb1) ha2 hb2
    · -- a supporter of `D` in `honestActiveAt S Sched s''` would be the witness
      obtain ⟨vote, hvote, hval, -, -, H, hH, hHr, hDH⟩ := (mem_supportersOf_iff _ _ _ _ _ _).1 hS
      have hvK : v ∈ S.P.committee s'' := hval ▸ hcomm vote hvote
      refine Finset.mem_sdiff.2 ⟨hvK, fun hvG => hno ?_⟩
      obtain ⟨k, t', hlk, hsk⟩ :=
        pool_vote_tick_send hDiv hMono hOwner (hHA v hvG) (hsv hvote) hval
      have hslot := pool_slot_of_stateBefore S Sched x _ u' s'' vote (hsv hvote)
      obtain ⟨-, H_v, hHvT, hveq⟩ := tick_vote_held_block S Sched x hlk hsk hslot
      have hv1 : 1 ≤ voteTime S s'' := by rw [voteTime_eq]; omega
      obtain ⟨-, hlc, -⟩ := stepBefore_spec x hDiv hc1
      obtain ⟨-, hlv, -⟩ := stepBefore_spec x hDiv hv1
      have hHH : H = H_v := by
        refine hRoots H H_v ⟨stepBefore x (supportCutoff S (s'' + 1)), u', ?_, by omega,
          ((mem_fg_to_ac_tree _ _).1 hH).1⟩
          ⟨stepBefore x (voteTime S s''), v, ?_, by omega, hHvT⟩ (by rw [hHr, hveq])
        · intro h
          exact hHonc (hMono _ _ (by omega) h)
        · intro h
          exact hHA v hvG (hMono _ _ (by omega) h)
      rw [hHH] at hDH
      exact ⟨v, Finset.mem_inter.2 ⟨hvG, hvK⟩, H_v, hHvT, hDH⟩
  refine fast_test_fails_of_minority _ _ _ hsub hlt ?_
  rw [hcard]
  exact hfast

end GoldilocksCorrectness.Proofs.Executions
