module
public import GoldilocksCorrectness.Proofs.Executions.PeriodInduction
public import GoldilocksCorrectness.Proofs.Executions.Lemma26Held
public import GoldilocksCorrectness.Proofs.Executions.PeriodRevocation
public import GoldilocksCorrectness.Proofs.Executions.AsyncDeliveryBoundary
public import GoldilocksCorrectness.Proofs.Executions.PeriodFinalityChainBlock
public import GoldilocksCorrectness.Proofs.Executions.PeriodJustifiedPast
public import GoldilocksCorrectness.Proofs.Executions.Lemma78Compat
public import GoldilocksCorrectness.Proofs.Executions.PeriodCompatCopies
public import GoldilocksCorrectness.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Proofs.Routines.FGStateReaders

@[expose] public section

/-! The
audited statements are in `Statements/Executions/PeriodInductionCompatStatements.lean`. Write
`h(X)` for `(chainStateOf S.C X).h`, the chain-state height of a block `X`.

- `exists_votes_compatible`, `voters_compatible_majority`: the copies of `exists_votes_on_chain`
  and `voters_on_chain_majority` whose members' votes are for blocks compatible with `B`;
- `confirmation_compatible_of_timely_votes` (statement 2′): no honest confirmation of a slot whose
  votes are due by its support cutoff conflicts with `B`;
- `vote_compatible_of_timely_view` (statement 1′): at a timely slot, an honest active vote is on
  `B`'s chain, or is compatible with `B` from a voter justified past `B`;
- `period_inv_compat_all` (statement 3′): `PeriodInvCompatDueByCutoff` at every step after the
  hand-over update;
- `after_period_compat` (Lemma 104′) and the two corollaries.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff viewFreeze
  dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_le_supportCutoff dutyWindowStart_mono
  one_le_Δ slotStart_eq slotStart_mono slot_eq_of_mem slot_of_update_after_deadline
  supportCutoff_cast supportCutoff_eq supportCutoff_slot supportCutoff_slot_eq viewFreeze_cast
  viewFreeze_eq voteTime_eq voteTime_mono' voteTime_succ' votes_due_of_after_period)

open GoldilocksCorrectness.Proofs.Routines (chainStateOf_height_mono)
open GoldilocksCorrectness.Statements.Routines (chainStateOf)

open GoldilocksCorrectness.Proofs.Routines (fc_root_compatible fc_root_eq fg_to_ac_F
  h_max_of_contested head_height_floor_of_not_contested mem_fg_to_ac_tree mem_viable_heads_of)
open GoldilocksCorrectness.Statements.Routines (ChainStatesComputed)

open GoldilocksCorrectness.Proofs.Routines (get_anchor_mem_T vote_head_compatible_of_justified_past
  vote_head_descends_of_F)

open GoldilocksCorrectness.Proofs.Routines (wake_eq)

open GoldilocksCorrectness.Proofs.Routines (goldfish_fork_choice_eq)

open GoldilocksCorrectness.Proofs.Routines (mem_viable_tree_iff)

open GoldilocksCorrectness.Statements.Routines (CachesCompatibleWith)

open GoldilocksCorrectness.Proofs.Routines (duty_window_start_le_dutyWindowStart)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg AtomicHonest)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

-- An index `x[i]` into an execution has the valid-index predicate `fun _ _ => True`; this rule,
-- local to the file, proves it at once. No statement and no proof term changes.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- `omega` after the `abbrev`s `Height` and `Slot` are unfolded. -/
local macro "omega_nat" : tactic =>
  `(tactic| ((try dsimp only) <;> (try unfold Height at *) <;> (try unfold Slot at *) <;> omega))

/-! ## The voters of a slot whose votes are compatible with `B` -/

/-- The members of a set `Q` of honest active committee members of slot `σ`, each of whose
slot-`σ` votes is for a block it holds compatible with `B`, have such a vote: a block `H u` for
each, `u`'s slot-`σ` vote for `H u` is on the wire at its tick at the vote time of `σ`, `u` holds
`H u` then, `H u` is compatible with `B`, and `u` is a committee member honest at the support
cutoff of slot `σ + 1`. The copy of `exists_votes_on_chain` with "compatible with `B`" in place
of "`B` or a descendant of `B`".

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `σ`: the slot; `Q`: the voters;
  `B`: the block. -/
theorem exists_votes_compatible (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (σ : ℕ) (Q : Finset V) (B : Block V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hQ : Q ⊆ honestActiveAt S Sched σ ∩ S.P.committee σ)
    (hExt : ∀ u ∈ Q, ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S σ) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) →
      ∃ H_u ∈ (stateBefore x (voteTime S σ) u).S.T,
        vote = GoldfishVote.mk u σ H_u.root ∧ H_u.compatible B = true) :
    ∃ H : V → Block V, ∀ u ∈ Q, u ∈ S.P.committee σ ∧
      u ∉ Sched.adv ((supportCutoff S (σ + 1) : ℕ) : Int) ∧
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S σ) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u σ (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      H u ∈ (stateBefore x (voteTime S σ) u).S.T ∧ (H u).compatible B = true := by
  classical
  have key : ∀ u ∈ Q, ∃ Hu : Block V,
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S σ) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u σ Hu.root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      Hu ∈ (stateBefore x (voteTime S σ) u).S.T ∧ Hu.compatible B = true := by
    intro u hu
    obtain ⟨hA, hK⟩ := Finset.mem_inter.1 (hQ hu)
    obtain ⟨i, vote, hl, -, -, hsent⟩ :=
      GoldilocksCorrectness.Statements.Executions.honest_active_votes S Sched x σ u hDiv hMono hA hK
    obtain ⟨Hu, hHuT, hveq, hBH⟩ := hExt u hu vote ⟨i, hl, hsent⟩
    exact ⟨Hu, ⟨i, hl, hveq ▸ hsent⟩, hHuT, hBH⟩
  refine ⟨fun u => if h : u ∈ Q then Classical.choose (key u h) else B, fun u hu => ?_⟩
  obtain ⟨hA, hK⟩ := Finset.mem_inter.1 (hQ hu)
  have hspec := Classical.choose_spec (key u hu)
  simp only [dif_pos hu]
  exact ⟨hK, (Finset.mem_sdiff.1 hA).2, hspec⟩

/-- The voters of slot `s'` whose votes `VotesCompatibleAt` makes compatible with `B` outweigh the
rest of the committee: the lock holders' members of the committee when the previous votes were
owed inside the period (`P.hHold`; their conjunct is read at `s' ≤ s + k`, `owed_slot_le_k`), and
the honest active members otherwise (`P.hSleepK`). The copy of `voters_on_chain_majority`.

The variables:
- `P`: the hypotheses; `s'`: the slot. -/
theorem voters_compatible_majority {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (protocol S) Sched} {GST s : ℕ} {B : Block V} {H t₀ anchor tAwakeEnd b₀ b₁ : ℕ}
    (P : AsyncHypsOfChainBlockGSTBeforeVotes S Sched x GST s B H t₀ anchor tAwakeEnd b₀ b₁) (s' : ℕ)
    (hs' : s + 1 ≤ s') (hVotes : VotesCompatibleAt S Sched x s B b₀ b₁ s') :
    ∃ Q : Finset V, Q ⊆ honestActiveAt S Sched s' ∩ S.P.committee s' ∧
      (∀ u ∈ Q, ∀ vote : GoldfishVote V,
        (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s') ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x[i + 1].sent - x[i].sent) →
        ∃ H_u ∈ (stateBefore x (voteTime S s') u).S.T,
          vote = GoldfishVote.mk u s' H_u.root ∧ H_u.compatible B = true) ∧
      (S.P.committee s' \ Q).card < Q.card := by
  classical
  by_cases hOwed : VotesOwedInPeriod S b₀ b₁ s'
  · have hs2 : s + 2 ≤ s' := by
      by_contra hc
      have h1 : s' - 1 ≤ s + 1 := by omega
      have h2 := supportCutoff_eq S (s' - 1)
      have h3 := supportCutoff_eq S (s + 1)
      have h4 := voteTime_mono' S h1
      have h5 := P.hb₀
      exact absurd hOwed.1 (by omega)
    have hlt := P.hHold s' hs2 hOwed.1 hOwed.2
    refine ⟨holdersAt S Sched s s' ∩ S.P.committee s', ?_,
      fun u hu => holders_vote_compatible_of_votesCompatibleAt hVotes
        (owed_slot_le_k P.hb₁ hOwed) u (Finset.mem_inter.1 hu).1, ?_⟩
    · intro u hu
      simp only [holdersAt, Finset.mem_inter] at hu ⊢
      exact ⟨hu.1.2, hu.2⟩
    · have heq : S.P.committee s' \ (holdersAt S Sched s s' ∩ S.P.committee s') =
          S.P.committee s' \ holdersAt S Sched s s' := by
        ext u
        simp only [Finset.mem_sdiff, Finset.mem_inter]
        tauto
      rw [heq]
      exact hlt
  · refine ⟨honestActiveAt S Sched s' ∩ S.P.committee s', subset_rfl,
      fun u hu => active_vote_compatible_of_votesCompatibleAt hVotes hOwed u
        (Finset.mem_inter.1 hu).1, ?_⟩
    have hanchor : anchor ≤ slotStart S (s' + 1) :=
      le_trans P.hAnchor (slotStart_mono S (by omega))
    have hK := P.hSleepK (s' + 1) (by omega) hanchor
    rw [Nat.add_sub_cancel] at hK
    have hsub : S.P.committee s' \ (honestActiveAt S Sched s' ∩ S.P.committee s') ⊆
        S.P.committee s' \ honestActiveAt S Sched s' := by
      intro w hw
      simp only [Finset.mem_sdiff, Finset.mem_inter] at hw ⊢
      tauto
    exact lt_of_le_of_lt (Finset.card_le_card hsub) hK

/-! ## Statement 2′: the confirmations of a slot whose votes are due by its support cutoff -/

/-- **Statement 2′: no confirmation of a timely slot conflicts with `B`.** The proof; the audited
statement is in `Statements/Executions/PeriodInductionCompatStatements.lean`. Statement 2's proof
(`confirmation_extends_B_of_timely_votes`) with Lemma 78c and its twin in place of Lemma 78 and its
twin, and `voters_compatible_majority` in place of `voters_on_chain_majority`.

The variables:
- `P`: the hypotheses; `s'`: the slot; `v`: the validator whose update it is.

Roots name blocks until `supportCutoff S s'`: Lemma 78c (or its twin) at slot `s'`. -/
theorem confirmation_compatible_of_timely_votes {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (protocol S) Sched} {GST s : ℕ} {B : Block V} {H t₀ anchor tAwakeEnd b₀ b₁ : ℕ}
    (P : AsyncHypsOfChainBlockGSTBeforeVotes S Sched x GST s B H t₀ anchor tAwakeEnd b₀ b₁)
    (s' : ℕ) (v : V)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S s'))
    (hs' : s + 1 ≤ s') (hgood : VotesDueByCutoff S b₀ b₁ s')
    (hv : v ∈ honestActiveAt S Sched s')
    (hF : (stateBefore x (supportCutoff S (s' + 1)) v).S.F.compatible B = true)
    (hVotes : VotesCompatibleAt S Sched x s B b₀ b₁ s') :
    ∀ C' : Block V,
      (stateBefore x (supportCutoff S (s' + 1) + 1) v).A.saved_confirmation s' = some C' →
      C'.compatible B = true := by
  obtain ⟨Q, hQsub, hQext, hQcard⟩ := voters_compatible_majority P s' hs' hVotes
  obtain ⟨Hf, hHs⟩ := exists_votes_compatible S Sched x s' Q B P.hDiv P.hMono hQsub hQext
  have hVoters : voters_count ((stateBefore x (supportCutoff S (s' + 1)) v).A.pool s') <
      2 * Q.card :=
    GoldilocksCorrectness.Proofs.Routines.voters_count_lt_of_committee_majority
      (pool_committee_of_stateBefore S Sched x _ v s') hQcard
  have hv' : ∀ t : ℕ, dutyWindowStart S (s' + 1) ≤ t → t ≤ supportCutoff S (s' + 1) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int) := fun t h1 h2 =>
    honestActiveAt_window S Sched s' v P.hMono hv t
      (le_trans (dutyWindowStart_mono S (Nat.le_succ s')) h1) h2
  have hGSTs : GST ≤ voteTime S s' := le_trans P.hGST (voteTime_mono' S hs')
  rcases hgood with hA | hB
  · exact lem78c_update_confirmation_compatible_of_voter_majority_upTo
      S Sched x GST s' Q Hf B v P.hDiv P.hMono
      (SynchronyFromWakeUpTo.mono hA (synchronyFromWakeUpTo_of_outside P.hSync))
      (CatchUpOnWakeUpTo.mono hA (catchUpOnWakeUpTo_of_outside P.hCatch))
      hRoots P.hParent P.hOwner hGSTs hHs hVoters hv' hF
  · exact lem78c_update_confirmation_compatible_of_voter_majority
      S Sched x (max b₁ GST) s' Q Hf B v P.hDiv P.hMono
      (synchronyFromWake_of_outside_after P.hSync) (catchUpOnWake_of_outside_after P.hCatch)
      hRoots P.hParent P.hOwner (max_le hB hGSTs) hHs hVoters hv' hF

/-! ## Statement 1′: the votes of a timely slot -/

/-- **The vote a tick sends is the end of the Goldfish fork choice, on the state before the
tick.** For a Goldfish vote `w` put on the wire at its tick at the vote time of slot `s'`: the vote
is `w`'s slot-`s'` vote for a block `H_u` that `w` holds before the tick, and `H_u` is the end of
the Goldfish fork choice from the anchor of some revoked AC state `A'` through the viable tree of
some tree `vbt`, on `w`'s FG state before the tick. Lemma 14 (`lem14_tick_vote_walk`), read as
the proof of `holder_vote_extends_B_orTwoPast` reads it.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s'`: the slot; `w`: the voter;
  `vote`: the vote. -/
theorem tick_vote_fork_choice {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (protocol S) Sched} (s' : ℕ) (w : V) (vote : GoldfishVote V)
    (hsend : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s') ∧
      (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) :
    ∃ (A' : ACState V) (votes sv : Finset (GoldfishVote V)) (vbt : Finset (Block V))
      (H_u : Block V),
      H_u ∈ (stateBefore x (voteTime S s') w).S.T ∧ vote = GoldfishVote.mk w s' H_u.root ∧
      goldfish_fork_choice S.C (fg_to_ac (stateBefore x (voteTime S s') w).S)
        ((voteTime S s' : ℕ) : Int)
        (get_anchor A' (fg_to_ac (stateBefore x (voteTime S s') w).S) ((voteTime S s' : ℕ) : Int))
        (viable_tree (fg_to_ac (stateBefore x (voteTime S s') w).S) vbt) votes sv (s' - 1) =
        .ok H_u := by
  obtain ⟨i, hl, hm⟩ := hsend
  have hΔ := one_le_Δ S
  have hv₃ : voteTime S s' = slotStart S s' + Δ S := voteTime_eq S s'
  have hss : slotStart S (s' + 1) = slotStart S s' + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hslot₃ : S.C.slot ((voteTime S s' : ℕ) : Int) = s' :=
    slot_eq_of_mem S (by omega) (by omega)
  have hi : stepBefore x (voteTime S s') = i := stepBefore_eq_of_lbl x hl
  obtain ⟨-, n', sent, hrun, hvote⟩ := tick_send_of_honestSendAt hl hm
  have hst : stateBefore x (voteTime S s') w = x[i][w].st := by unfold stateBefore; rw [hi]
  have hA : (tickInputState x i (voteTime S s') w).A = (stateBefore x (voteTime S s') w).A := by
    rw [(tickInputState_frame x i _ w).2.1, hst]
  have hS : (tickInputState x i (voteTime S s') w).S = (stateBefore x (voteTime S s') w).S := by
    rw [(tickInputState_frame x i _ w).1, hst]
  obtain ⟨-, hvi, hvs, -, A', votes, support_votes, vbt, H_u, -, -, hvbt, hWalk, hhead, -⟩ :=
    GoldilocksCorrectness.Statements.Routines.lem14_tick_vote_walk S.C S.P S.X _ n' _ sent vote
      hrun hvote
  rw [hslot₃, hA, hS] at hvbt
  rw [hslot₃, hS] at hWalk
  have hv : (tickInputState x i (voteTime S s') w).v = w := by
    have h := (lem11_node_invariant S Sched x i w).2.1
    unfold tickInputState
    split <;> (try rw [wake_eq]) <;> exact h
  rw [hv] at hvi
  rw [hslot₃] at hvs
  have hvote' : vote = GoldfishVote.mk w s' H_u.root := by
    rw [← hvi, ← hvs, ← hhead]
  have hHT : H_u ∈ (stateBefore x (voteTime S s') w).S.T := by
    rcases GoldilocksCorrectness.Proofs.Routines.ghost_mem_tree_or_eq ((goldfish_fork_choice_eq ..).symm.trans hWalk) with h | h
    · rw [h]
      exact get_anchor_mem_T _ _ _
        (lem11_node_invariant S Sched x (stepBefore x (voteTime S s')) w).1.2.2.2.1
        (GoldilocksCorrectness.Statements.Executions.lem57_justification_cache_and_record S Sched x
          (stepBefore x (voteTime S s')) w).2.2.1
    · have h1 := ((mem_viable_tree_iff _ _ _).1 h).1
      have h2 := ((GoldilocksCorrectness.Proofs.Routines.mem_voter_block_tree_iff S.C _ _ s' vbt
        hvbt H_u).1 h1).1
      exact ((mem_fg_to_ac_tree _ _).1 h2).1
  exact ⟨A', votes, support_votes, vbt, H_u, hHT, hvote', hWalk⟩

/-- **Statement 1′'s core: the vote of a timely slot, given the previous votes on `B`'s chain
whenever the voter is not justified past `B` and its finalized block is `B` or an ancestor of
`B`.** Statement 1′'s proof with `hExt` in place of its hypotheses on the previous slot (`hCprev`,
`hVotes`), which statement 1′ turns into `hExt` (`justified_past_spreads`); the induction calls
this form at slot `s + 2`, where the previous votes are the hand-over facts' and no caches of the
previous slot's voters are at hand. Write `σ := s' − 1` and
`n_u := stateBefore x (voteTime S s') u`.

- `h(B) + 1 ≤ n_u.S.h_j`: Lemma 14, then `vote_head_compatible_of_justified_past` (the caches,
  `hTwo`, `h_j_lt_h_max`, Lemma 11's computed chain states): the second disjunct.
- `n_u.S.h_j ≤ h(B)` and `n_u.S.F` not an ancestor of `B`: `B` is an ancestor of it (the caches
  are compatible with `B`), and `vote_head_descends_of_F`: the first disjunct.
- `n_u.S.h_j ≤ h(B)` and `n_u.S.F ⪯ B`: not contested (`hNC` and `h_max_of_contested`). The votes
  of `σ` are on `B`'s chain (`hExt`). Then v3's route: the voters' majority (`voters_on_chain_majority`), the votes held (the twin of
  Lemma 12 when `supportCutoff S σ ≤ b₀`, Lemma 12 by a later delay at `max (voteTime S σ) b₁`
  otherwise), the locks (`revoked_entries_compatible_of_majority`), `hF2` from the caches, `hF3`
  from `B` itself when `n_u.S.h_max ≤ h(B) + 1` and from the certified entry at
  `n_u.S.h_max − 1` (Lemma 67, K3, `mem_voter_tree_of_held`) otherwise, and Lemma 26b from held
  votes with `R := B`: the first disjunct.

The variables:
- `P`: the hypotheses; `s'`: the slot of the vote; `u`: the voter. -/
theorem vote_compatible_of_timely_view_ofExtend {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (protocol S) Sched} {GST s : ℕ} {B : Block V} {H t₀ anchor tAwakeEnd b₀ b₁ : ℕ}
    (P : AsyncHypsOfChainBlockGSTBeforeVotes S Sched x GST s B H t₀ anchor tAwakeEnd b₀ b₁)
    (s' : ℕ) (u : V)
    (hRoots : RootsNameBlocksUntil S Sched x (voteTime S s'))
    (hs' : s + 2 ≤ s') (hgood : ¬ VotesOwedInPeriod S b₀ b₁ s')
    (hu : u ∈ honestActiveAt S Sched s')
    (hC : CachesCompatibleWith S B H (stateBefore x (voteTime S s') u))
    (hTwo : ∀ D ∈ (stateBefore x (voteTime S s') u).S.T,
      (chainStateOf S.C B).h + 2 ≤ (chainStateOf S.C D).h → B.AncestorEq D)
    (hNC : fg_contest (stateBefore x (voteTime S s') u).S = false ∨
      (chainStateOf S.C B).h + 2 ≤ (stateBefore x (voteTime S s') u).S.h_max)
    (hExt : (stateBefore x (voteTime S s') u).S.h_j ≤ (chainStateOf S.C B).h →
      (stateBefore x (voteTime S s') u).S.F.AncestorEq B →
      VotesExtendAt S Sched x s B b₀ b₁ (s' - 1)) :
    ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s') ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) →
      ∃ H_u ∈ (stateBefore x (voteTime S s') u).S.T,
        vote = GoldfishVote.mk u s' H_u.root ∧
        (B.AncestorEq H_u ∨ (H_u.compatible B = true ∧
          (chainStateOf S.C B).h + 1 ≤ (stateBefore x (voteTime S s') u).S.h_j)) := by
  intro vote hsend
  obtain ⟨σ, rfl⟩ : ∃ σ, s' = σ + 1 := ⟨s' - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hExt
  obtain ⟨-, hJB, -, hJh, hFJ⟩ := hC
  have hσc : ChainStatesComputed S.C (stateBefore x (voteTime S (σ + 1)) u).S :=
    fun D hD => σ_eq_of_stateBefore S Sched x _ u D hD
  -- the case the voter is justified past `B`
  by_cases hjust : (chainStateOf S.C B).h + 1 ≤ (stateBefore x (voteTime S (σ + 1)) u).S.h_j
  · obtain ⟨A', votes, sv, vbt, H_u, hHT, hveq, hWalk⟩ := tick_vote_fork_choice (σ + 1) u vote hsend
    exact ⟨H_u, hHT, hveq, Or.inr ⟨vote_head_compatible_of_justified_past S.C _ B hσc hJB hJh hFJ
      hTwo (h_j_lt_h_max S Sched x _ u) hjust A' _ vbt votes sv _ H_u hWalk, hjust⟩⟩
  -- the case `B` is a strict ancestor of the voter's finalized block
  by_cases hFB : (stateBefore x (voteTime S (σ + 1)) u).S.F.AncestorEq B
  swap
  · have hBF : B.AncestorEq (stateBefore x (voteTime S (σ + 1)) u).S.F := by
      rcases hJB with hJB' | hBJ
      · exact absurd (GoldilocksCorrectness.Proofs.Routines.ancestorEq_trans hFJ hJB') hFB
      · rcases GoldilocksCorrectness.Proofs.Routines.ancestorEq_compatible hFJ hBJ with h | h
        · exact absurd h hFB
        · exact h
    obtain ⟨A', votes, sv, vbt, H_u, hHT, hveq, hWalk⟩ := tick_vote_fork_choice (σ + 1) u vote hsend
    exact ⟨H_u, hHT, hveq, Or.inl (GoldilocksCorrectness.Proofs.Routines.ancestorEq_trans hBF
      (vote_head_descends_of_F S.C _ A' _ vbt votes sv _ H_u hFJ hWalk))⟩
  -- the case the voter's finalized block is `B` or an ancestor of `B`: Lemma 26b from held votes
  have hΔ := one_le_Δ S
  have hk := S.C.k_ge_two
  have hjle : (stateBefore x (voteTime S (σ + 1)) u).S.h_j ≤ (chainStateOf S.C B).h := by
    omega_nat
  -- not contested
  have hNC' : fg_contest (stateBefore x (voteTime S (σ + 1)) u).S = false := by
    rcases hNC with h | h
    · exact h
    · cases hc : fg_contest (stateBefore x (voteTime S (σ + 1)) u).S
      · rfl
      · have hm := h_max_of_contested _ hc
        omega_nat
  -- the times of slots `σ`, `σ + 1`, `σ + 2`, over the atom `slotStart S σ`
  have hss1 : slotStart S (σ + 1) = slotStart S σ + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hss2 : slotStart S (σ + 1 + 1) = slotStart S (σ + 1) + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hvtσ := voteTime_eq S σ
  have hscσ := supportCutoff_eq S σ
  have hvfσ := viewFreeze_eq S σ
  have hvt1 := voteTime_eq S (σ + 1)
  have hsc1 := supportCutoff_eq S (σ + 1)
  have hvt2 := voteTime_eq S (σ + 1 + 1)
  have hsc2 := supportCutoff_eq S (σ + 1 + 1)
  -- the votes of slot `σ` are on `B`'s chain
  have hExt := hExt hjle hFB
  -- the voters, their majority and their blocks
  obtain ⟨Q, hQsub, hQext, hQcard⟩ := voters_on_chain_majority P σ (by omega) hExt
  obtain ⟨Hf, hHs⟩ := exists_votes_on_chain S Sched x σ Q B P.hDiv P.hMono hQsub hQext
  have hcard : (S.P.committee σ).card < 2 * Q.card := by
    have := Finset.card_le_card_sdiff_add_card (s := S.P.committee σ) (t := Q)
    omega
  obtain ⟨u₀, hu₀⟩ : Q.Nonempty := Finset.card_pos.1 (by omega)
  have hQhon : ∀ u' ∈ Q, u' ∉ Sched.adv ((voteTime S (σ + 1) : ℕ) : Int) := fun u' hu' h =>
    (hHs u' hu').2.1 (P.hMono _ _ (by exact_mod_cast (by omega :
      voteTime S (σ + 1) ≤ supportCutoff S (σ + 1))) h)
  have hFH : ∀ u' ∈ Q, (stateBefore x (voteTime S (σ + 1)) u).S.F.AncestorEq (Hf u') :=
    fun u' hu' => GoldilocksCorrectness.Proofs.Routines.ancestorEq_trans hFB (hHs u' hu').2.2.2.2
  -- `u` is awake and honest from `voteTime S σ` to `viewFreeze S σ`
  have hσ1 : 1 ≤ σ := by omega
  have hdws : dutyWindowStart S (σ + 1) ≤ voteTime S σ := by
    have h1 := dutyWindowStart_le_supportCutoff S (s := σ + 1) (s' := σ - 1) (by omega)
    have h2 := supportCutoff_eq S (σ - 1)
    have h3 := voteTime_eq S (σ - 1)
    have h4 : slotStart S (σ - 1 + 1) = slotStart S (σ - 1) + 4 * Δ S := by
      rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
    have h5 : σ - 1 + 1 = σ := by omega
    rw [h5] at h4
    omega
  have hwin := honestActiveAt_window S Sched (σ + 1) u P.hMono hu
  have hGSTσ : GST ≤ voteTime S σ := le_trans P.hGST (voteTime_mono' S (by omega))
  have hgood' : supportCutoff S σ ≤ b₀ ∨ b₁ ≤ supportCutoff S σ := by
    unfold VotesOwedInPeriod at hgood
    simp only [Nat.add_sub_cancel] at hgood
    omega
  -- the votes of `Q` held by `u` before its vote, stamped and resolved before `tb`
  obtain ⟨tb, htb, hHeld⟩ : ∃ tb : ℕ, tb ≤ viewFreeze S σ ∧ ∀ u' ∈ Q,
      HeldEarlyVoteAt (stateBefore x (voteTime S (σ + 1)) u).A
        (fg_to_ac (stateBefore x (voteTime S (σ + 1)) u).S) ((tb : ℕ) : Int) σ (Hf u') u' := by
    rcases hgood' with hb | hb
    · refine ⟨supportCutoff S σ, by omega, fun u' hu' => ?_⟩
      have h := lem12_honest_vote_delivered_upTo S Sched x GST σ Q Hf u P.hDiv P.hMono
        (SynchronyFromWakeUpTo.mono hb (synchronyFromWakeUpTo_of_outside P.hSync))
        (CatchUpOnWakeUpTo.mono hb (catchUpOnWakeUpTo_of_outside P.hCatch))
        (hRoots.mono (by omega)) P.hParent P.hOwner hGSTσ
        (fun u' hu' => ⟨(hHs u' hu').1, hQhon u' hu', (hHs u' hu').2.2.1, (hHs u' hu').2.2.2.1⟩)
        (fun t h1 h2 => hwin t (by omega) (by omega)) hFH u' hu'
      rw [heldEarlyVoteFor_iff, ← supportCutoff_cast] at h
      exact h
    · have hmax : max (voteTime S σ) b₁ ≤ supportCutoff S σ := max_le (by omega) hb
      have hmax1 : voteTime S σ ≤ max (voteTime S σ) b₁ := le_max_left _ _
      have hGST' : max b₁ GST ≤ max (voteTime S σ) b₁ :=
        max_le (le_max_right _ _) (le_trans hGSTσ hmax1)
      refine ⟨max (voteTime S σ) b₁ + Δ S, by omega, ?_⟩
      exact lem12_honest_vote_delivered_by_until S Sched x (max b₁ GST) σ
        (max (voteTime S σ) b₁) (voteTime S (σ + 1)) Q Hf u P.hDiv P.hMono
        (synchronyFromWake_of_outside_after P.hSync) (catchUpOnWake_of_outside_after P.hCatch)
        (hRoots.mono (by omega)) P.hParent P.hOwner hGST' hmax1 (by omega) (by omega)
        (fun u' hu' => ⟨(hHs u' hu').1, hQhon u' hu', (hHs u' hu').2.2.1, (hHs u' hu').2.2.2.1⟩)
        (fun t h1 h2 => hwin t (by omega) (by omega)) hFH
  -- `hF3`: a viable head of the voter tree on `B`'s chain
  have hfl : head_height_floor (stateBefore x (voteTime S (σ + 1)) u).S =
      (stateBefore x (voteTime S (σ + 1)) u).S.h_max - 1 :=
    head_height_floor_of_not_contested _ hNC'
  have hF3 : (fg_to_ac (stateBefore x (voteTime S (σ + 1)) u).S).fc_root.AncestorEq B →
      ∀ tree : Finset (Block V),
        voter_block_tree S.C (stateBefore x (voteTime S (σ + 1)) u).A
          (fg_to_ac (stateBefore x (voteTime S (σ + 1)) u).S) (σ + 1) = .ok tree →
        ∃ W ∈ tree, W ∈ (fg_to_ac (stateBefore x (voteTime S (σ + 1)) u).S).viable_heads ∧
          B.AncestorEq W := by
    intro hrB tree htree
    rw [fc_root_eq] at hrB
    by_cases h2 : (chainStateOf S.C B).h + 2 ≤ (stateBefore x (voteTime S (σ + 1)) u).S.h_max
    · -- the certified entry one height under the top height
      obtain ⟨-, ⟨Z, hZT, hZh⟩, -⟩ :=
        cachesWitnessed_of_stateBefore S Sched x (voteTime S (σ + 1)) u
      have hBZ : B.AncestorEq Z := hTwo Z hZT (by rw [hZh]; exact h2)
      obtain ⟨Y, hYZ, -, hYp, -, hTY, hcert⟩ :=
        GoldilocksCorrectness.Proofs.Routines.lem67_first_advance S.C Z
          ((stateBefore x (voteTime S (σ + 1)) u).S.h_max - 1) (by omega_nat)
          (by rw [hZh]; omega_nat)
      have hT'h : (chainStateOf S.C (chainStateOf S.C Y.parent).T_h).h =
          (stateBefore x (voteTime S (σ + 1)) u).S.h_max - 1 := by
        rw [(GoldilocksCorrectness.Proofs.Routines.isEntry_T_h S.C Y.parent).2.1, hYp]
      have hT'Z := GoldilocksCorrectness.Proofs.Routines.ancestorEq_trans hTY hYZ
      have hYT : Y ∈ (stateBefore x (voteTime S (σ + 1)) u).S.T :=
        ancestors_mem_T_of_exec S Sched x _ u Z Y hZT hYZ
      have hT'T : (chainStateOf S.C Y.parent).T_h ∈ (stateBefore x (voteTime S (σ + 1)) u).S.T :=
        ancestors_mem_T_of_exec S Sched x _ u Z _ hZT hT'Z
      have hBT' : B.AncestorEq (chainStateOf S.C Y.parent).T_h := by
        rcases GoldilocksCorrectness.Proofs.Routines.ancestorEq_compatible hBZ hT'Z with h | h
        · exact h
        · have hm := chainStateOf_height_mono S.C h
          omega_nat
      have hFT' := GoldilocksCorrectness.Proofs.Routines.ancestorEq_trans hFB hBT'
      have hvf : viewFreeze S σ ≤ voteTime S (σ + 1) := by omega
      have hFvf : (stateBefore x (viewFreeze S (σ + 1 - 1)) u).S.F.compatible
          (chainStateOf S.C Y.parent).T_h = true := by
        rw [Nat.add_sub_cancel]
        exact (GoldilocksCorrectness.Proofs.Routines.compatible_iff _ _).2
          (Or.inl (GoldilocksCorrectness.Proofs.Routines.ancestorEq_trans
            (stateBefore_grows x P.hDiv u hvf).2.1 hFT'))
      have hheld := cert_entry_held_before_freeze P (σ + 1) u Y (chainStateOf S.C Y.parent).T_h
        ((stateBefore x (voteTime S (σ + 1)) u).S.h_max - 1) hRoots hs' hgood hu hYT hTY hcert
        (by rw [hT'h]; omega_nat) hFvf
      rw [Nat.add_sub_cancel] at hheld
      refine ⟨_, mem_voter_tree_of_held S Sched x P.hDiv (viewFreeze S σ) (σ + 1) u _ tree hheld
        (by rw [Nat.add_sub_cancel]) hvf hFT' htree,
        mem_viable_heads_of S.C _ _ hσc hT'T hFT'
          (GoldilocksCorrectness.Proofs.Routines.ancestorEq_trans hrB hBT')
          (by rw [hfl, hT'h]), hBT'⟩
    · -- `B` itself, held, stamped before the view freeze, viable
      obtain ⟨-, -, hHΦ, ⟨y, hy, hyb⟩, -⟩ := hHeld u₀ hu₀
      have hHT : Hf u₀ ∈ (stateBefore x (voteTime S (σ + 1)) u).S.T :=
        ((mem_fg_to_ac_tree _ _).1 hHΦ).1
      have hBH : B.AncestorEq (Hf u₀) := (hHs u₀ hu₀).2.2.2.2
      have hBT : B ∈ (stateBefore x (voteTime S (σ + 1)) u).S.T :=
        ancestors_mem_T_of_exec S Sched x _ u _ B hHT hBH
      have hBΦ : B ∈ (fg_to_ac (stateBefore x (voteTime S (σ + 1)) u).S).tree :=
        (mem_fg_to_ac_tree _ _).2 ⟨hBT, hFB⟩
      have h23 : ((((tb : ℕ) : Int) : Time) : Stamp) ≤ ((S.C.t_ σ + 3 * S.C.Δ : Time) : Stamp) := by
        apply WithBot.coe_le_coe.2
        rw [← viewFreeze_cast]
        exact_mod_cast htb
      obtain ⟨τP, τH, hτP, hτH, hle⟩ := ancestor_blockStamp_le S Sched x _ u (Hf u₀) B hHT hBH
      obtain ⟨τH', hτH', hle'⟩ := GoldilocksCorrectness.Proofs.Routines.tau_eq_some_blockStamp
        (rootsNameBlocksIn_frame_of_exec_node S Sched x _ u) hHΦ rfl hy
      have hτHH' : τH = τH' := Option.some_injective _ (hτH.symm.trans hτH')
      obtain ⟨y', hyy', hy'lt⟩ :=
        (GoldilocksCorrectness.Proofs.Routines.occurrenceBefore_eq_true_iff _ _).1 hyb
      have hyy : y = y' := Option.some_injective _ hyy'
      have hτlt : τP < ((S.C.t_ σ + 3 * S.C.Δ : Time) : Stamp) :=
        lt_of_le_of_lt hle (hτHH' ▸ lt_of_le_of_lt hle' (hyy ▸ lt_of_lt_of_le hy'lt h23))
      refine ⟨B, (GoldilocksCorrectness.Proofs.Routines.mem_voter_block_tree_iff S.C _ _ (σ + 1)
        tree htree B).2 ⟨hBΦ, τP, hτP, Or.inl ?_⟩,
        mem_viable_heads_of S.C _ _ hσc hBT hFB hrB (by rw [hfl]; omega_nat),
        GoldilocksCorrectness.Proofs.Routines.ancestorEq_refl B⟩
      rw [Nat.add_sub_cancel]
      exact hτlt
  -- Lemma 26b from held votes, with `R := B`
  obtain ⟨H_w, hT, hv, hB⟩ :=
    GoldilocksCorrectness.Proofs.Executions.lem26b_goldfish_vote_extends_voter_majority_block_of_held
      S Sched x σ tb Q Hf B u vote P.hDiv P.hMono P.hOwner htb
      (fun u' hu' => ⟨hQhon u' hu', (hHs u' hu').2.2.1, (hHs u' hu').2.2.2.2⟩)
      (fun _ => hHeld)
      (fun votes sv hCV => GoldilocksCorrectness.Proofs.Routines.voters_count_lt_of_committee_majority
        (countedVotes_committee S Sched x _ σ u votes sv hCV) hQcard)
      (by rw [fc_root_eq]; exact fc_root_compatible _ B hJB hFJ) hF3
      (fun _ => revoked_entries_compatible_of_majority S Sched x σ tb u Q Hf B hcard
        (fun u' hu' => (hHs u' hu').2.2.2.2) hHeld)
      hsend
  exact ⟨H_w, hT, hv, Or.inl hB⟩

/-- **Statement 1′: the vote of a timely slot is on `B`'s chain, or compatible with `B` from a
voter justified past `B`.** The proof; the audited statement is in
`Statements/Executions/PeriodInductionCompatStatements.lean`. `vote_compatible_of_timely_view_ofExtend`,
with the votes of `σ := s' − 1` on `B`'s chain when the voter `u` is not justified past `B` and its
finalized block is `B` or an ancestor of `B`: the holders' when the votes of `σ − 1` were owed
(`hVotes.1`, `σ ≤ s + k` by `owed_slot_le_k`), and every honest active voter's otherwise, since
one with the second disjunct would, by `justified_past_spreads` (`hCprev`), give `u` a
justification height at least `h(B) + 1`.

The variables:
- `P`: the hypotheses; `s'`: the slot of the vote; `u`: the voter. -/
theorem vote_compatible_of_timely_view {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (protocol S) Sched} {GST s : ℕ} {B : Block V} {H t₀ anchor tAwakeEnd b₀ b₁ : ℕ}
    (P : AsyncHypsOfChainBlockGSTBeforeVotes S Sched x GST s B H t₀ anchor tAwakeEnd b₀ b₁)
    (s' : ℕ) (u : V)
    (hRoots : RootsNameBlocksUntil S Sched x (voteTime S s'))
    (hs' : s + 2 ≤ s') (hgood : ¬ VotesOwedInPeriod S b₀ b₁ s')
    (hu : u ∈ honestActiveAt S Sched s')
    (hC : CachesCompatibleWith S B H (stateBefore x (voteTime S s') u))
    (hTwo : ∀ D ∈ (stateBefore x (voteTime S s') u).S.T,
      (chainStateOf S.C B).h + 2 ≤ (chainStateOf S.C D).h → B.AncestorEq D)
    (hNC : fg_contest (stateBefore x (voteTime S s') u).S = false ∨
      (chainStateOf S.C B).h + 2 ≤ (stateBefore x (voteTime S s') u).S.h_max)
    (hCprev : ∀ w ∈ honestActiveAt S Sched (s' - 1),
      CachesCompatibleWith S B H (stateBefore x (voteTime S (s' - 1)) w))
    (hVotes : VotesCompatibleAt S Sched x s B b₀ b₁ (s' - 1)) :
    ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s') ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) →
      ∃ H_u ∈ (stateBefore x (voteTime S s') u).S.T,
        vote = GoldfishVote.mk u s' H_u.root ∧
        (B.AncestorEq H_u ∨ (H_u.compatible B = true ∧
          (chainStateOf S.C B).h + 1 ≤ (stateBefore x (voteTime S s') u).S.h_j)) := by
  refine vote_compatible_of_timely_view_ofExtend P s' u hRoots hs' hgood hu hC hTwo hNC ?_
  intro hjle hFB
  obtain ⟨σ, rfl⟩ : ∃ σ, s' = σ + 1 := ⟨s' - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hCprev hVotes ⊢
  have hActive : ¬ VotesOwedInPeriod S b₀ b₁ σ → ∀ w ∈ honestActiveAt S Sched σ,
      ∀ vote' : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S σ) ∧
        (⟨w, NamedObject.gfVote vote'⟩ : SignedMsg V (NamedObject V)) ∈
          x[i + 1].sent - x[i].sent) →
      ∃ H_w ∈ (stateBefore x (voteTime S σ) w).S.T,
        vote' = GoldfishVote.mk w σ H_w.root ∧ B.AncestorEq H_w := by
    intro hgσ w hw vote' hsend'
    obtain ⟨H_w, hT, hv, hB | ⟨-, hjw⟩⟩ := hVotes.2 hgσ w hw vote' hsend'
    · exact ⟨H_w, hT, hv, hB⟩
    · exfalso
      have hsp := justified_past_spreads P σ w u hRoots (by omega) hgood hw (hCprev w hw) hjw hu
        hFB
      omega_nat
  refine ⟨fun w hw vote' hsend' => ?_, hActive⟩
  by_cases hOw : VotesOwedInPeriod S b₀ b₁ σ
  · exact hVotes.1 (owed_slot_le_k P.hb₁ hOw) w hw vote' hsend'
  · exact hActive hOw w (Finset.mem_inter.1 hw).2 vote' hsend'

/-! ## The updates of the period's updaters -/

/-- Statement 2′ for an updater of the slot: the proof of `confirmation_compatible_of_timely_votes`
with `v ∈ updaterAt S Sched s'` (awake through the duty window of slot `s' + 1`, honest at its
cutoff) in place of `v ∈ honestActiveAt S Sched s'`; Lemma 78c reads only that window. The
induction reads it at a lock holder's own update after the lock's deadline.

The variables:
- `P`: the hypotheses; `s'`: the slot; `v`: the updater. -/
theorem confirmation_compatible_of_updater {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (protocol S) Sched} {GST s : ℕ} {B : Block V} {H t₀ anchor tAwakeEnd b₀ b₁ : ℕ}
    (P : AsyncHypsOfChainBlockGSTBeforeVotes S Sched x GST s B H t₀ anchor tAwakeEnd b₀ b₁)
    (s' : ℕ) (v : V)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S s'))
    (hs' : s + 1 ≤ s') (hgood : VotesDueByCutoff S b₀ b₁ s')
    (hv : v ∈ updaterAt S Sched s')
    (hF : (stateBefore x (supportCutoff S (s' + 1)) v).S.F.compatible B = true)
    (hVotes : VotesCompatibleAt S Sched x s B b₀ b₁ s') :
    ∀ C' : Block V,
      (stateBefore x (supportCutoff S (s' + 1) + 1) v).A.saved_confirmation s' = some C' →
      C'.compatible B = true := by
  obtain ⟨Q, hQsub, hQext, hQcard⟩ := voters_compatible_majority P s' hs' hVotes
  obtain ⟨Hf, hHs⟩ := exists_votes_compatible S Sched x s' Q B P.hDiv P.hMono hQsub hQext
  have hVoters : voters_count ((stateBefore x (supportCutoff S (s' + 1)) v).A.pool s') <
      2 * Q.card :=
    GoldilocksCorrectness.Proofs.Routines.voters_count_lt_of_committee_majority
      (pool_committee_of_stateBefore S Sched x _ v s') hQcard
  have hv' := updaterAt_window S Sched s' v P.hMono hv
  have hGSTs : GST ≤ voteTime S s' := le_trans P.hGST (voteTime_mono' S hs')
  rcases hgood with hA | hB
  · exact lem78c_update_confirmation_compatible_of_voter_majority_upTo
      S Sched x GST s' Q Hf B v P.hDiv P.hMono
      (SynchronyFromWakeUpTo.mono hA (synchronyFromWakeUpTo_of_outside P.hSync))
      (CatchUpOnWakeUpTo.mono hA (catchUpOnWakeUpTo_of_outside P.hCatch))
      hRoots P.hParent P.hOwner hGSTs hHs hVoters hv' hF
  · exact lem78c_update_confirmation_compatible_of_voter_majority
      S Sched x (max b₁ GST) s' Q Hf B v P.hDiv P.hMono
      (synchronyFromWake_of_outside_after P.hSync) (catchUpOnWake_of_outside_after P.hCatch)
      hRoots P.hParent P.hOwner (max_le hB hGSTs) hHs hVoters hv' hF

/-- A validator whose tick at the support cutoff of slot `s' + 1` runs the update (awake and honest
at it, its tick starting from a record of awakeness since the duty window's start of `s' + 1` or
earlier) is an updater of slot `s'`. The step of `attest_source_fast_block_updater`'s proof.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `i`: the step of the tick; `s'`: the
  slot; `v`: the validator; `τ`: the record of awakeness. -/
theorem updaterAt_of_update_tick {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (protocol S) Sched} (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption) (i s' : ℕ) (v : V) (τ : Time)
    (hl : x.lbl i = AtomicAction.tickAllAwake (supportCutoff S (s' + 1)))
    (hAwake : v ∈ Sched.awake ((supportCutoff S (s' + 1) : ℕ) : Int))
    (hHon : v ∉ Sched.adv ((supportCutoff S (s' + 1) : ℕ) : Int))
    (hτ : (tickInputState x i (supportCutoff S (s' + 1)) v).awakeSince = some τ)
    (hτle : τ ≤ duty_window_start S.C (s' + 1)) :
    v ∈ updaterAt S Sched s' := by
  have hc1 : 1 ≤ supportCutoff S (s' + 1) := (supportCutoff_slot S s').2
  have hτ' : (tickInputState x (stepBefore x (supportCutoff S (s' + 1)))
      (supportCutoff S (s' + 1)) v).awakeSince = some τ := by
    rw [stepBefore_eq_of_lbl x hl]
    exact hτ
  have hawake := awake_of_tickInput_awakeSince x hDiv hMono hc1 hτ' hAwake hHon
  refine Finset.mem_sdiff.2 ⟨mem_awakeThroughout_of_forall (fun t'' h1 h2 => ?_), hHon⟩
  refine hawake t'' ?_ h2
  have h3 : duty_window_start S.C (s' + 1) ≤ ((dutyWindowStart S (s' + 1) : ℕ) : Int) :=
    duty_window_start_le_dutyWindowStart S (s' + 1)
  have h4 : ((dutyWindowStart S (s' + 1) : ℕ) : Int) ≤ (t'' : Int) := by exact_mod_cast h1
  exact le_trans hτle (le_trans h3 h4)

/-- The tick at `t` comes no later than step `j` when the configuration after step `j` is at the
time `t` or later.

The variables:
- `x`: the execution; `t`: the time; `j`: the step. -/
theorem stepBefore_le_of_le_time {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (protocol S) Sched} (hDiv : TimeDiverges x.toTrace) {t j : ℕ}
    (h : t ≤ x[j + 1].time) : stepBefore x t ≤ j := by
  by_contra hc
  have := (lt_stepBefore_iff x hDiv).1 (show j < stepBefore x t by omega)
  omega

/-! ## Statement 3′: the induction -/

/-- **The joint invariant under the compatible vote clause, from the hand-over update on.** For
every step `j` from `stepBefore x (supportCutoff S (s + 1) + 1)` (the configuration right after
the hand-over update) on, with roots naming blocks among what honest validators hold up to
`x[j].time`, `PeriodInvCompatDueByCutoff` holds at `j`.

Why: strong induction on the step. The base is the hand-over facts (`P.hHand`), the sixth clause
from their votes of slot `s + 1` (`votesCompatibleAt_of_votesExtendAt`), the seventh vacuous. At
the step `j + 1`: clause 6 at a slot `s' ≥ s + 2` from the invariant at the step before the vote
time of `s'` (the holders' conjunct by `holder_vote_extends_B_orTwoPast_ofCompat`, the honest
active voters' by statement 1′, or by its core with the hand-over votes when `s' = s + 2`); clause
1 by `holderInv_step_ofCompat`; clause 5 by `attestations_step_ofHeldEntry_ofCompat`; clause 4 by
the certificate step; clause 3 by `caches_step_ofChainBlock`; clause 7 by statement 2′ with the
caches at the step before the update; clause 2 by clause 1 before the lock's deadline, and after
it by the holder's own update (`step_cases_latest`): the record is kept, or becomes the saved
confirmation, compatible with `B` (`confirmation_compatible_of_updater`), not an ancestor of the
record, hence `B` or a descendant of `B`.

The variables:
- `P`: the hypotheses. -/
theorem period_inv_compat_from {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (protocol S) Sched} {GST s : ℕ} {B : Block V} {H t₀ anchor tAwakeEnd b₀ b₁ : ℕ}
    (P : AsyncHypsOfChainBlockGSTBeforeVotes S Sched x GST s B H t₀ anchor tAwakeEnd b₀ b₁) :
    ∀ j : ℕ, stepBefore x (supportCutoff S (s + 1) + 1) ≤ j →
      RootsNameBlocksUntil S Sched x x[j].time →
      PeriodInvCompatDueByCutoff S Sched x s B H t₀ b₀ b₁ j := by
  have hΔ := one_le_Δ S
  have hk := S.C.k_ge_two
  have hvs1 := voteTime_succ' S (s + 1)
  have hc := supportCutoff_eq S (s + 1)
  obtain ⟨-, hj₀t, hj₀t1⟩ :=
    stepBefore_spec x P.hDiv (show 1 ≤ supportCutoff S (s + 1) + 1 by omega)
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro hj hR
  rcases Nat.eq_or_lt_of_le hj with hj0 | hlt
  · -- the base: the hand-over facts
    subst hj0
    have ht : x[stepBefore x (supportCutoff S (s + 1) + 1)].time = supportCutoff S (s + 1) := by
      omega
    refine ⟨fun _ w hw _ => (P.hHand.2.1 w hw).2.2,
      fun w hw _ => ⟨(P.hHand.2.1 w hw).2.2.2.1, (P.hHand.2.1 w hw).2.2.2.2.1⟩,
      fun u hu => P.hHand.2.2.1 _ u ht hu,
      P.hHand.2.2.2.1, P.hHand.2.2.2.2.1, ?_, ?_⟩
    · intro s' hs' hvt
      obtain rfl : s' = s + 1 := by
        by_contra hne
        have := voteTime_mono' S (show s + 1 + 1 ≤ s' by omega)
        omega
      exact votesCompatibleAt_of_votesExtendAt S Sched x (P.hHand.2.2.2.2.2.1 b₀ b₁)
    · intro s' hs' _ hlt'
      exfalso
      have h1 := voteTime_mono' S (show s + 1 + 1 ≤ s' + 1 by omega)
      have h2 := supportCutoff_eq S (s' + 1)
      omega
  -- the step `j → j + 1`
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have hjj : stepBefore x (supportCutoff S (s + 1) + 1) ≤ j := by omega
  have IH : ∀ j' : ℕ, stepBefore x (supportCutoff S (s + 1) + 1) ≤ j' → j' ≤ j →
      PeriodInvCompatDueByCutoff S Sched x s B H t₀ b₀ b₁ j' := fun j' h1 h2 =>
    ih j' (by omega) h1 (hR.mono (time_mono x (by omega)))
  obtain ⟨I1, I2, I3, I4, I5, I6, -⟩ := IH j hjj le_rfl
  have htj : x[j].time ≤ x[j + 1].time := time_mono x (Nat.le_succ j)
  have hcj : supportCutoff S (s + 1) < x[j + 1].time := by
    have := time_mono x (show stepBefore x (supportCutoff S (s + 1) + 1) + 1 ≤ j + 1 by omega)
    omega
  have PA := AsyncHypsOfChainBlockGSTBeforeVotes.toAsyncHyps P
  have PC := AsyncHypsOfChainBlockGSTBeforeVotes.toAsyncHypsOfChainBlock P
  -- clause 6 at `j + 1`
  have C6 : ∀ s' : ℕ, s + 1 ≤ s' → voteTime S s' < x[j + 1].time →
      VotesCompatibleAt S Sched x s B b₀ b₁ s' := by
    intro s' hs' hvt
    rcases Nat.eq_or_lt_of_le hs' with heq | hs2
    · subst heq
      exact votesCompatibleAt_of_votesExtendAt S Sched x (P.hHand.2.2.2.2.2.1 b₀ b₁)
    have hvs2 := voteTime_mono' S (show s + 1 + 1 ≤ s' by omega)
    have hv1 : 1 ≤ voteTime S s' := by omega
    obtain ⟨-, hj't, -⟩ := stepBefore_spec x P.hDiv hv1
    have hj'0 : stepBefore x (supportCutoff S (s + 1) + 1) ≤ stepBefore x (voteTime S s') :=
      stepBefore_mono x P.hDiv (by omega)
    have hj'j : stepBefore x (voteTime S s') ≤ j := stepBefore_le_of_le_time P.hDiv (le_of_lt hvt)
    obtain ⟨J1, -, J3, J4, -, J6, -⟩ := IH _ hj'0 hj'j
    have hRv : RootsNameBlocksUntil S Sched x (voteTime S s') := hR.mono (le_of_lt hvt)
    have hsv := voteTime_succ' S (s' - 1)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ s')] at hsv
    have hsc' := supportCutoff_eq S (s' + 1)
    have hvs' := voteTime_succ' S s'
    -- an honest active voter of `s'` is honest at the step before its vote
    have hadv : ∀ w ∈ honestActiveAt S Sched s',
        HonestThrough x (stepBefore x (voteTime S s')) w := fun w hw t' ht' h =>
      (Finset.mem_sdiff.1 hw).2 (P.hMono _ _ (le_trans ht' (by exact_mod_cast (by omega :
        x[stepBefore x (voteTime S s')].time ≤ supportCutoff S (s' + 1)))) h)
    refine ⟨fun hk' w hw vote hsend => ?_, fun hgood w hw vote hsend => ?_⟩
    · -- the holders, during the hand-over lock's life
      have hwH := hadv w (Finset.mem_inter.1 hw).2
      have hwa : w ∉ Sched.adv (x[stepBefore x (voteTime S s')].time : Int) := hwH _ le_rfl
      have hdl : x[stepBefore x (voteTime S s')].time < voteTime S (s + S.C.k + 1) := by
        have := voteTime_mono' S hk'
        have := voteTime_succ' S (s + S.C.k)
        omega
      exact holder_vote_extends_B_orTwoPast_ofCompat PA s' w hRv hs2 hk'
        (J1 hdl w (Finset.mem_inter.1 hw).1 hwH) (J3 w hwa)
        (fun D hD hDh => blocksTwoPastDescend_at_ofChainBlock S Sched x _ P.hHand.1 J4 w D hwa hD
          hDh)
        (not_contested_or_two_past_of_certificates S Sched x _ w hwa J4 (J3 w hwa))
        (J6 (s' - 1) (by omega) (by omega)) vote hsend
    · -- the honest active voters of a timely slot
      have hwa : w ∉ Sched.adv (x[stepBefore x (voteTime S s')].time : Int) := hadv w hw _ le_rfl
      rcases Nat.eq_or_lt_of_le hs2 with heq2 | hs3
      · -- `s' = s + 2`: the previous votes are the hand-over facts'
        subst heq2
        refine vote_compatible_of_timely_view_ofExtend P (s + 1 + 1) w hRv le_rfl hgood hw (J3 w hwa)
          (fun D hD hDh => blocksTwoPastDescend_at_ofChainBlock S Sched x _ P.hHand.1 J4 w D hwa hD
            hDh)
          (not_contested_or_two_past_of_certificates S Sched x _ w hwa J4 (J3 w hwa))
          (fun _ _ => P.hHand.2.2.2.2.2.1 b₀ b₁) vote hsend
      · -- `s' ≥ s + 3`: statement 1′, the previous voters' caches at the step before their vote
        have hvsm := voteTime_eq S (s' - 1)
        have hscs := supportCutoff_eq S s'
        have hvp : 1 ≤ voteTime S (s' - 1) := by omega
        obtain ⟨-, hj''t, -⟩ := stepBefore_spec x P.hDiv hvp
        have hvs3 := voteTime_mono' S (show s + 1 + 1 ≤ s' - 1 by omega)
        have hj''0 : stepBefore x (supportCutoff S (s + 1) + 1) ≤ stepBefore x (voteTime S (s' - 1)) :=
          stepBefore_mono x P.hDiv (by omega)
        have hj''j : stepBefore x (voteTime S (s' - 1)) ≤ j :=
          stepBefore_le_of_le_time P.hDiv (by omega)
        obtain ⟨-, -, J3', -, -, -, -⟩ := IH _ hj''0 hj''j
        have hle1 : x[stepBefore x (voteTime S (s' - 1))].time ≤ supportCutoff S (s' - 1 + 1) := by
          rw [Nat.sub_add_cancel (by omega : 1 ≤ s')]
          omega
        exact vote_compatible_of_timely_view P s' w hRv (by omega) hgood hw (J3 w hwa)
          (fun D hD hDh => blocksTwoPastDescend_at_ofChainBlock S Sched x _ P.hHand.1 J4 w D hwa hD
            hDh)
          (not_contested_or_two_past_of_certificates S Sched x _ w hwa J4 (J3 w hwa))
          (fun w' hw' => J3' w' (fun h => (Finset.mem_sdiff.1 hw').2 (P.hMono _ _ (by
            exact_mod_cast hle1) h)))
          (J6 (s' - 1) (by omega) (by omega)) vote hsend
  -- clause 1 at `j + 1`
  have C1 : x[j + 1].time < voteTime S (s + S.C.k + 1) →
      ∀ w ∈ updaterAt S Sched s, HonestThrough x (j + 1) w → HolderInvAt S Sched x s B (j + 1) w := by
    intro hd w hw hH
    have hHj : HonestThrough x j w := fun t' ht' => hH t' (le_trans ht' (by exact_mod_cast htj))
    exact holderInv_step_ofCompat PA j w hR hcj hd (I1 (lt_of_le_of_lt htj hd) w hw hHj)
      (I3 w (hHj _ le_rfl)) C6
  -- clauses 5, 4 and 3 at `j + 1`
  have C5 : AttestationsCompatibleWithBeforeOfHeldEntry S Sched x B H t₀ (j + 1) :=
    attestations_step_ofHeldEntry_ofCompat PC j hR I5 I6
  have C4 : CertificatesCompatibleWithAtOfChainBlock S Sched x H B (j + 1) :=
    certificatesCompatibleWithAtOfChainBlock_of_attestations S Sched x (j + 1) P.hU hR
      (P.hAdvQ _) C5
  have C3 : ∀ u : V, u ∉ Sched.adv (x[j + 1].time : Int) →
      CachesCompatibleWith S B H (x[j + 1][u].st) := fun u hu =>
    caches_step_ofChainBlock S Sched x j u hu
      (I3 u (fun h => hu (P.hMono _ _ (by exact_mod_cast htj) h))) C4
  -- the caches give a finalized block compatible with `B`
  have hFcomp : ∀ n : NodeState V, CachesCompatibleWith S B H n → n.S.F.compatible B = true :=
    fun n hn => GoldilocksCorrectness.Proofs.Routines.compatible_of_ancestorEq_compatible hn.2.2.2.2
      ((GoldilocksCorrectness.Proofs.Routines.compatible_iff _ _).2 hn.2.1)
  -- clause 7 at `j + 1`
  have C7 : ∀ s' : ℕ, s + 1 ≤ s' → VotesDueByCutoff S b₀ b₁ s' →
      supportCutoff S (s' + 1) < x[j + 1].time →
      ∀ v ∈ honestActiveAt S Sched s', ∀ C' : Block V,
        (stateBefore x (supportCutoff S (s' + 1) + 1) v).A.saved_confirmation s' = some C' →
        C'.compatible B = true := by
    intro s' hs' hdue hlt' v hv C' hC'
    have hsc' := supportCutoff_eq S (s' + 1)
    have hsc0 := supportCutoff_eq S s'
    have hvs' := voteTime_succ' S s'
    have hvs2 := voteTime_mono' S (show s + 1 ≤ s' by omega)
    have hv1 : 1 ≤ supportCutoff S (s' + 1) := by omega
    obtain ⟨-, hj''t, -⟩ := stepBefore_spec x P.hDiv hv1
    have hj''0 : stepBefore x (supportCutoff S (s + 1) + 1) ≤
        stepBefore x (supportCutoff S (s' + 1)) := stepBefore_mono x P.hDiv (by omega)
    have hj''j : stepBefore x (supportCutoff S (s' + 1)) ≤ j :=
      stepBefore_le_of_le_time P.hDiv (le_of_lt hlt')
    obtain ⟨-, -, J3, -, -, -, -⟩ := IH _ hj''0 hj''j
    have hva : v ∉ Sched.adv (x[stepBefore x (supportCutoff S (s' + 1))].time : Int) := fun h =>
      (Finset.mem_sdiff.1 hv).2 (P.hMono _ _ (by exact_mod_cast (by omega :
        x[stepBefore x (supportCutoff S (s' + 1))].time ≤ supportCutoff S (s' + 1))) h)
    exact confirmation_compatible_of_timely_votes P s' v (hR.mono (by omega)) hs' hdue hv
      (hFcomp _ (J3 v hva)) (C6 s' hs' (by omega)) C' hC'
  -- clause 2 at `j + 1`
  have C2 : ∀ w ∈ updaterAt S Sched s, HonestThrough x (j + 1) w →
      B.AncestorEq (x[j + 1][w].st).A.latest_confirmed ∧
      (x[j + 1][w].st).A.latest_confirmed ∈ (x[j + 1][w].st).S.T := by
    intro w hw hH
    refine ⟨?_, latest_confirmed_mem_T_of_exec x (j + 1) w⟩
    by_cases hd : x[j + 1].time < voteTime S (s + S.C.k + 1)
    · exact (C1 hd w hw hH).2.1
    have hHj : HonestThrough x j w := fun t' ht' => hH t' (le_trans ht' (by exact_mod_cast htj))
    obtain ⟨hB2, hT2⟩ := I2 w hw hHj
    rcases step_cases_latest x j w with h | ⟨t, hl, hmem, ht, ⟨τ, hτ, hτle⟩, A'', hA'', hsc, hlc⟩
    · rw [h]
      exact hB2
    obtain ⟨htj1, htj2⟩ := time_of_lbl_tickAllAwake x hl
    -- the slot of the update
    have hst := supportCutoff_slot_eq S ht
    have hs0 : S.C.slot (t : Int) ≠ 0 := by
      intro h0
      rw [h0] at hst
      have := supportCutoff_eq S 0
      have := voteTime_mono' S (Nat.zero_le (s + 1))
      omega
    obtain ⟨s'', hs''⟩ : ∃ s'', S.C.slot (t : Int) = s'' + 1 :=
      ⟨S.C.slot (t : Int) - 1, by omega_nat⟩
    rw [hs''] at hst hτle hA''
    have hdead : s + S.C.k ≤ s'' :=
      slot_of_update_after_deadline S s s'' (by rw [hst, ← htj2]; omega)
    rcases GoldilocksCorrectness.Proofs.Routines.update_confirmation_latest_cases S.C S.P _ A''
        _ _ (s'' + 1) (Nat.succ_ne_zero s'') hA'' with
      ⟨-, hkeep⟩ | ⟨C', hsave, ⟨-, hkeep⟩ | ⟨-, hadv⟩⟩
    · rw [hlc, hkeep]
      exact hB2
    · rw [hlc, hkeep]
      exact hB2
    rw [hlc, hadv]
    rcases GoldilocksCorrectness.Proofs.Routines.advance_some (fg_to_ac (x[j][w].st).S)
        (GoldilocksCorrectness.Statements.Routines.expireLocks (x[j][w].st).A (t : Int)).latest_confirmed C' with ⟨-, -, ha⟩ | ⟨hn, ha⟩
    · rw [ha]
      exact hB2
    rw [ha]
    -- the confirmation saved is compatible with `B`
    rw [Nat.add_sub_cancel] at hsave
    have hjstep : stepBefore x t = j := stepBefore_eq_of_lbl x hl
    rw [← hst] at hl hmem hτ
    have hupd : w ∈ updaterAt S Sched s'' :=
      updaterAt_of_update_tick P.hDiv P.hMono j s'' w τ hl (Finset.mem_sdiff.1 hmem).1
        (Finset.mem_sdiff.1 hmem).2 hτ hτle
    have hkept := (stateBefore_succ_keepsConfirmation x P.hDiv w htj2).2.1
    have hsaved : (stateBefore x (supportCutoff S (s'' + 1) + 1) w).A.saved_confirmation s'' =
        some C' := by
      rw [hst, hkept, hsc]
      exact hsave
    have hsc'' := supportCutoff_eq S (s'' + 1)
    have hsc0 := supportCutoff_eq S s''
    have hvs'' := voteTime_succ' S s''
    have hwj : w ∉ Sched.adv (x[j].time : Int) := hHj _ le_rfl
    have hFst : (stateBefore x (supportCutoff S (s'' + 1)) w).S.F.compatible B = true := by
      rw [hst]
      unfold stateBefore
      rw [hjstep]
      exact hFcomp _ (I3 w hwj)
    have hCB := confirmation_compatible_of_updater P s'' w (hR.mono (by omega)) (by omega)
      (Or.inr (votes_due_of_after_period S s s'' b₁ P.hb₁ hdead)) hupd hFst
      (C6 s'' (by omega) (by omega)) C' hsaved
    rcases (GoldilocksCorrectness.Proofs.Routines.compatible_iff _ _).1 hCB with hC'B | hBC'
    · -- `C'` an ancestor of `B`: `B` an ancestor of the finalized block, or the record kept
      rcases (GoldilocksCorrectness.Proofs.Routines.compatible_iff _ _).1 (hFcomp _ (I3 w hwj)) with
        hFB | hBF
      · exfalso
        exact hn ⟨(mem_fg_to_ac_tree _ _).2 ⟨hT2, GoldilocksCorrectness.Proofs.Routines.ancestorEq_trans
          hFB hB2⟩, GoldilocksCorrectness.Proofs.Routines.ancestorEq_trans hC'B hB2⟩
      · have hFC := GoldilocksCorrectness.Statements.Routines.saved_confirmation_F_ancestorEq S.C S.P
          _ A'' _ _ (s'' + 1) (Nat.le_add_left 1 s'') hA''
        rw [Nat.add_sub_cancel, fg_to_ac_F] at hFC
        exact GoldilocksCorrectness.Proofs.Routines.ancestorEq_trans hBF (hFC C' hsave)
    · exact hBC'
  exact ⟨C1, C2, C3, C4, C5, fun s' hs' hvt => C6 s' hs' hvt, C7⟩

/-- **Statement 3′: the joint invariant under the compatible vote clause, for ever.** The proof; the
audited statement is in `Statements/Executions/PeriodInductionCompatStatements.lean`. A step `j`
whose time is after the hand-over cutoff comes after the configuration right after the hand-over
update (`time_lt_iff_le_stepBefore`), and `period_inv_compat_from` holds there.

The variables:
- `P`: the hypotheses. -/
theorem period_inv_compat_all {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (protocol S) Sched} {GST s : ℕ} {B : Block V} {H t₀ anchor tAwakeEnd b₀ b₁ : ℕ}
    (P : AsyncHypsOfChainBlockGSTBeforeVotes S Sched x GST s B H t₀ anchor tAwakeEnd b₀ b₁) :
    ∀ j : ℕ, supportCutoff S (s + 1) < x[j].time → RootsNameBlocksUntil S Sched x x[j].time →
      PeriodInvCompatDueByCutoff S Sched x s B H t₀ b₀ b₁ j := by
  intro j hj hR
  refine period_inv_compat_from P j ?_ hR
  by_contra hc
  have h := (time_lt_iff_le_stepBefore x P.hDiv (show 1 ≤ supportCutoff S (s + 1) + 1 by omega)
    (i := j)).2 (by omega)
  omega

/-! ## Lemma 104′ and the corollaries -/

/-- **Lemma 104′: from slot `s + k + 1` on, the honest votes and confirmations do not conflict
with `B`.** The proof; the audited statement is in
`Statements/Executions/PeriodInductionCompatStatements.lean`. The invariant at the step before the
update of `s'` (`stepBefore x (supportCutoff S (s' + 1))`, at a time after the hand-over cutoff,
with roots naming blocks up to it): its sixth clause at `s'`; its third clause for `v`'s finalized
block, and statement 2′ at `s'`, whose votes are due by its cutoff (`b₁ ≤ voteTime S s'`).

The variables:
- `P`: the hypotheses. -/
theorem after_period_compat {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (protocol S) Sched} {GST s : ℕ} {B : Block V} {H t₀ anchor tAwakeEnd b₀ b₁ : ℕ}
    (P : AsyncHypsOfChainBlockGSTBeforeVotes S Sched x GST s B H t₀ anchor tAwakeEnd b₀ b₁) :
    ∀ s' : ℕ, s + S.C.k + 1 ≤ s' → RootsNameBlocksUntil S Sched x (supportCutoff S (s' + 1)) →
      VotesCompatibleAt S Sched x s B b₀ b₁ s' ∧
      ∀ v ∈ honestActiveAt S Sched s', ∀ C' : Block V,
        (stateBefore x (supportCutoff S (s' + 1) + 1) v).A.saved_confirmation s' = some C' →
        C'.compatible B = true := by
  intro s' hs' hR
  have hΔ := one_le_Δ S
  have hk := S.C.k_ge_two
  have hsc' := supportCutoff_eq S (s' + 1)
  have hsc0 := supportCutoff_eq S s'
  have hvs' := voteTime_succ' S s'
  have hc := supportCutoff_eq S (s + 1)
  have hvs2 := voteTime_mono' S (show s + 1 + 1 ≤ s' by omega)
  have hvs1 := voteTime_succ' S (s + 1)
  have hv1 : 1 ≤ supportCutoff S (s' + 1) := by omega
  obtain ⟨-, hjt, -⟩ := stepBefore_spec x P.hDiv hv1
  obtain ⟨-, -, I3, -, -, I6, -⟩ := period_inv_compat_all P (stepBefore x (supportCutoff S (s' + 1)))
    (by omega) (hR.mono (by omega))
  refine ⟨I6 s' (by omega) (by omega), fun v hv C' hC' => ?_⟩
  have hva : v ∉ Sched.adv (x[stepBefore x (supportCutoff S (s' + 1))].time : Int) := fun h =>
    (Finset.mem_sdiff.1 hv).2 (P.hMono _ _ (by exact_mod_cast (by omega :
      x[stepBefore x (supportCutoff S (s' + 1))].time ≤ supportCutoff S (s' + 1))) h)
  have hn := I3 v hva
  have hF : (stateBefore x (supportCutoff S (s' + 1)) v).S.F.compatible B = true :=
    GoldilocksCorrectness.Proofs.Routines.compatible_of_ancestorEq_compatible hn.2.2.2.2
      ((GoldilocksCorrectness.Proofs.Routines.compatible_iff _ _).2 hn.2.1)
  exact confirmation_compatible_of_timely_votes P s' v (hR.mono (by omega)) (by omega)
    (Or.inr (votes_due_of_after_period S s s' b₁ P.hb₁ (by omega))) hv hF
    (I6 s' (by omega) (by omega)) C' hC'

/-- The certificate clause at every step: after the hand-over cutoff by statement 3′ (its fourth
clause); at or before it, the hand-over facts' attestation clause holds at every earlier step
(fewer attestations), and the certificate step concludes the clause there.

The variables:
- `P`: the hypotheses; `hRoots`: roots name blocks; `j`: the step. -/
theorem certificatesCompatibleWithAtOfChainBlock_all {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (protocol S) Sched} {GST s : ℕ} {B : Block V} {H t₀ anchor tAwakeEnd b₀ b₁ : ℕ}
    (P : AsyncHypsOfChainBlockGSTBeforeVotes S Sched x GST s B H t₀ anchor tAwakeEnd b₀ b₁)
    (hRoots : RootsNameBlocks S Sched x) (j : ℕ) :
    CertificatesCompatibleWithAtOfChainBlock S Sched x H B j := by
  have hR := fun t => rootsNameBlocksUntil_of_rootsNameBlocks x t hRoots
  rcases Nat.lt_or_ge (supportCutoff S (s + 1)) x[j].time with hlt | hge
  · exact (period_inv_compat_all P j hlt (hR _)).2.2.2.1
  · have hj : j ≤ stepBefore x (supportCutoff S (s + 1) + 1) :=
      (time_lt_iff_le_stepBefore x P.hDiv (show 1 ≤ supportCutoff S (s + 1) + 1 by omega)).1
        (by omega)
    refine certificatesCompatibleWithAtOfChainBlock_of_attestations S Sched x (t₀ := t₀) j P.hU
      (hR _) (P.hAdvQ _) ?_
    intro i t v a hi hl hAw hHon hsent
    exact P.hHand.2.2.2.2.1 i t v a (by omega) hl hAw hHon hsent

/-- **The certificate corollary.** The proof; the audited statement is in
`Statements/Executions/PeriodInductionCompatStatements.lean`.

The variables:
- `P`: the hypotheses; `hRoots`: roots name blocks. -/
theorem certificates_compatible_with_ofChainBlock {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (protocol S) Sched} {GST s : ℕ} {B : Block V} {H t₀ anchor tAwakeEnd b₀ b₁ : ℕ}
    (P : AsyncHypsOfChainBlockGSTBeforeVotes S Sched x GST s B H t₀ anchor tAwakeEnd b₀ b₁)
    (hRoots : RootsNameBlocks S Sched x) :
    CertificatesCompatibleWithOfChainBlock S Sched x H B :=
  fun j => certificatesCompatibleWithAtOfChainBlock_all P hRoots j

/-- **The two-past corollary.** The proof; the audited statement is in
`Statements/Executions/PeriodInductionCompatStatements.lean`. `blocksTwoPastDescend_at_ofChainBlock`
at every step, with the certificate clause there.

The variables:
- `P`: the hypotheses; `hRoots`: roots name blocks. -/
theorem blocks_two_past_descend {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (protocol S) Sched} {GST s : ℕ} {B : Block V} {H t₀ anchor tAwakeEnd b₀ b₁ : ℕ}
    (P : AsyncHypsOfChainBlockGSTBeforeVotes S Sched x GST s B H t₀ anchor tAwakeEnd b₀ b₁)
    (hRoots : RootsNameBlocks S Sched x) :
    BlocksTwoPastDescend S Sched x B :=
  fun j => blocksTwoPastDescend_at_ofChainBlock S Sched x j P.hHand.1
    (certificatesCompatibleWithAtOfChainBlock_all P hRoots j)

end GoldilocksCorrectness.Proofs.Executions
