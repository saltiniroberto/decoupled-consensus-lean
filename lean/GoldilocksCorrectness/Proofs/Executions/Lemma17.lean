module
public import GoldilocksCorrectness.Statements.Routines.TickStatements
public import GoldilocksCorrectness.Statements.Routines.WalkStatements
public import GoldilocksCorrectness.Statements.Routines.LockStatements
public import GoldilocksCorrectness.Statements.Executions.DeliveryStatements
public import GoldilocksCorrectness.Proofs.Executions.IncludedVotes
public import GoldilocksCorrectness.Proofs.Executions.Lemma26

@[expose] public section

/-!  Write `t₃ := voteTime S (s + 1)`,
`A := (stateBefore x t₃ w).A` and `Φ := fg_to_ac (stateBefore x t₃ w).S`. The proof:

1. F2 and Lemma 46 (`F_ancestorEq_fc_root_of_stateBefore`) make `w`'s finalized block compatible
   with `R` (`compatible_of_ancestorEq_compatible`),
   split by `compatible_iff`. When `R` is an ancestor of `w`'s finalized block: `w`'s vote entered
   the sent log at the tick step at `t₃`, so its tick at `t₃` answered and sent the vote
   (`tick_send_of_honestSendAt`); by Lemma 14 the vote's head is the root of the end `H_w` of the
   fork choice from the anchor, and `R` is an ancestor of `fc_root`, of the anchor and of `H_w`.
   The rest treats the case of `w`'s finalized block an ancestor of `R`, hence of every `H u`;
2. the delivered votes: Lemma 12 gives, for every `u ∈ Hs`, `HeldEarlyVoteFor S.C A Φ s (H u) u`;
3. the lock condition of Lemma 26: for every answer `A'` of the revocation of slot `s + 1` at `t₃`
   on `A` with its expired entries removed, Lemma 5 on `A'`, with each `u ∈ Hs` voting once in
   `A`'s pool for `H u`, and the slot-`s` committee at most twice `Hs`
   (`committee_card_le_of_majority`): every lock entry of `A'`, live or not, is on a block
   compatible with `R`;
4. the voter bound of Lemma 26: for every pair of counted sets `votes`, `support_votes`, every vote
   of `votes` is from the slot-`s` committee (a pool vote by `pool_committee_of_stateBefore`, an
   included vote by `ac_valid_payload_facts` on its block, well formed by Lemma 11's
   `TreeClosed`), so the voters are fewer than twice `Hs`
   (`voters_count_lt_of_committee_majority`);
5. Lemma 26.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slotStart_eq slot_eq_of_mem voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (mem_fg_to_ac_tree)

open GoldilocksCorrectness.Proofs.Routines (expireLocks_keepsVotes fc_root_eq
  votesOnceInPoolFor_of_keepsVotes)

open GoldilocksCorrectness.Proofs.Routines (goldfish_fork_choice_eq)

open GoldilocksCorrectness.Proofs.Routines (block_well_formed_iff mem_included_votes_iff)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction AtomicHonest Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (StartsTowards RootsNameBlocksIn VotesOnceFor
  CountedVotes expireLocks)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  fc_root_ancestorEq_get_anchor ac_valid_payload_facts compatible_of_ancestorEq_compatible
  committee_card_le_of_majority voters_count_lt_of_committee_majority)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- Lemma 17, the next slot's honest Goldfish vote extends a block a committee majority voted
for. Its reading is on the statement page,
`GoldilocksCorrectness/Statements/Executions/NextSlotVoteStatements.lean`. It is Lemma 26 with the
committee majority, which gives Lemma 26's voter bound because every vote `w` counts is from the
slot-`s` committee (the admission invariant), and its lock condition through Lemma 5.

Roots name blocks until `supportCutoff S s`: the bound of the Lemma 12 and Lemma 26 calls at
slot `s` it passes the premise to. -/
theorem lem17_goldfish_vote_extends_majority_block (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s : ℕ) (Hs : Finset V) (H : V → Block V)
    (R : Block V) (w : V) (vote : GoldfishVote V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S s))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    (hGST : GST ≤ voteTime S s)
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ Sched.adv (voteTime S (s + 1) : Int) ∧
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      H u ∈ (stateBefore x (voteTime S s) u).S.T ∧ R.AncestorEq (H u))
    (hMajority : (S.P.committee s \ Hs).card < Hs.card)
    -- `w` is awake and honest from slot `s`'s vote time to its support cutoff
    (hw : ∀ t : ℕ, voteTime S s ≤ t → t ≤ supportCutoff S s →
      w ∈ Sched.awake (t : Int) ∧ w ∉ Sched.adv (t : Int))
    (hF2 : (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).fc_root.compatible R = true)
    (hF3 : (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).fc_root.AncestorEq R →
      ∀ tree : Finset (Block V),
        voter_block_tree S.C (stateBefore x (voteTime S (s + 1)) w).A
          (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) (s + 1) = .ok tree →
        ∃ W ∈ tree, W ∈ (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).viable_heads ∧
          R.AncestorEq W)
    (hSend : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (s + 1)) ∧
      (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent) :
    ∃ H_w : Block V, vote.head = H_w.root ∧ R.AncestorEq H_w := by
  have hFroot : (stateBefore x (voteTime S (s + 1)) w).S.F.AncestorEq
      (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).fc_root := by
    rw [fc_root_eq]; exact F_ancestorEq_fc_root_of_stateBefore S Sched x (voteTime S (s + 1)) w
  have hRootsΦ : RootsNameBlocksIn (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).tree :=
    rootsNameBlocksIn_frame_of_exec_node S Sched x _ w
  -- step 1: the case `R` an ancestor of `w`'s finalized block: the walk's end is the anchor or a
  -- descendant of it, the anchor is `fc_root` or a descendant of it, and `fc_root` is `w`'s
  -- finalized block or a descendant of it
  rcases (compatible_iff _ _).1 (compatible_of_ancestorEq_compatible hFroot hF2) with hFR | hRF
  swap
  · have hΔ := one_le_Δ S
    have hss : slotStart S (s + 1) = slotStart S s + 4 * Δ S := by
      rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
    have hss' : slotStart S (s + 1 + 1) = slotStart S (s + 1) + 4 * Δ S := by
      rw [slotStart_eq, slotStart_eq S (s + 1), Nat.mul_add, Nat.mul_one]
    have hv₃ : voteTime S (s + 1) = slotStart S (s + 1) + Δ S := voteTime_eq S (s + 1)
    have hslot₃ : S.C.slot ((voteTime S (s + 1) : ℕ) : Int) = s + 1 :=
      slot_eq_of_mem S (by omega) (by omega)
    obtain ⟨i, hl, hm⟩ := hSend
    have hi : stepBefore x (voteTime S (s + 1)) = i := stepBefore_eq_of_lbl x hl
    obtain ⟨-, n', sent, hrun, hvote⟩ := tick_send_of_honestSendAt hl hm
    have hS : (tickInputState x i (voteTime S (s + 1)) w).S =
        (stateBefore x (voteTime S (s + 1)) w).S := by
      rw [(tickInputState_frame x i _ w).1]
      unfold stateBefore
      rw [hi]
    obtain ⟨-, -, -, -, A', votes, support_votes, vbt, H_w, -, -, -, hWalk, hhead, -⟩ :=
      GoldilocksCorrectness.Statements.Routines.lem14_tick_vote_walk S.C S.P S.X _ n' _ sent vote
        hrun hvote
    rw [hslot₃, hS, Nat.add_sub_cancel] at hWalk
    have hAH : (get_anchor A' (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
        ((voteTime S (s + 1) : ℕ) : Int)).AncestorEq H_w := by
      rcases GoldilocksCorrectness.Proofs.Routines.ghost_spec ((goldfish_fork_choice_eq ..).symm.trans hWalk) with hH | ⟨hAH, -⟩
      · rw [hH]
        exact ancestorEq_refl _
      · exact hAH
    exact ⟨H_w, hhead, ancestorEq_trans hRF (ancestorEq_trans hFroot
      (ancestorEq_trans (fc_root_ancestorEq_get_anchor _ _ _) hAH))⟩
  -- the case `w`'s finalized block an ancestor of `R`, hence of every `H u`
  have hF1 : ∀ u ∈ Hs, (stateBefore x (voteTime S (s + 1)) w).S.F.AncestorEq (H u) :=
    fun u hu => ancestorEq_trans hFR (hHs u hu).2.2.2.2
  -- step 2: the delivered votes
  have hHeld : ∀ u ∈ Hs, HeldEarlyVoteFor S.C (stateBefore x (voteTime S (s + 1)) w).A
      (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) s (H u) u :=
    GoldilocksCorrectness.Statements.Executions.lem12_honest_vote_delivered S Sched x GST s Hs H
      w hDiv hMono hSync hCatch hRoots hParent hOwner hGST
      (fun u hu => ⟨(hHs u hu).1, (hHs u hu).2.1, (hHs u hu).2.2.1, (hHs u hu).2.2.2.1⟩)
      hw hF1
  -- step 3: the lock condition, by Lemma 5 on every answer of the revocation
  have hLocks : ∀ A' : ACState V,
      revoke_locks S.P (expireLocks (stateBefore x (voteTime S (s + 1)) w).A
        ((voteTime S (s + 1) : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
        ((voteTime S (s + 1) : ℕ) : Int) (s + 1) = .ok A' →
      ∀ e ∈ A'.lock_entries,
        is_live (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
          ((voteTime S (s + 1) : ℕ) : Int) e = true → e.B.compatible R = true := by
    intro A' hRevoke e he _
    refine (GoldilocksCorrectness.Statements.Routines.lem5_revoke_locks_entries_compatible S.P _
      A' _ _ (s + 1) R Hs (Nat.le_add_left 1 s) hRootsΦ (fun u hu => ?_)
      (committee_card_le_of_majority hMajority) hRevoke e he).2
    refine (votesOnceInPoolFor_of_keepsVotes (expireLocks_keepsVotes _ _) _ _ _ _).2 ?_
    obtain ⟨hp, -, hHΦ, ⟨y, hy, -⟩, huniq⟩ := hHeld u hu
    exact ⟨_, hp, rfl, ⟨y, hy⟩, ⟨H u, hHΦ, rfl, (hHs u hu).2.2.2.2⟩, huniq⟩
  -- step 4: the voter bound, every counted vote being from the slot-`s` committee
  have hBne : ∀ B : Block V, B.slot = s + 1 → B ≠ Block.genesis := by
    rintro B hBs rfl
    exact Nat.succ_ne_zero s hBs.symm
  have hPayload : ∀ B ∈ (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).tree,
      B.slot = s + 1 → ac_valid_payload S.P B = true := by
    intro B hB hBs
    have hBT := ((mem_fg_to_ac_tree _ _).1 hB).1
    have hwf := (((lem11_node_invariant S Sched x (stepBefore x (voteTime S (s + 1))) w).1.2.2.1).2
      B hBT (hBne B hBs)).2.1
    rw [block_well_formed_iff] at hwf
    exact hwf.1.2
  have hVoters : ∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes S.C (stateBefore x (voteTime S (s + 1)) w).A
        (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) (s + 1) votes support_votes →
      voters_count votes < 2 * Hs.card := by
    intro votes support_votes hCounted
    obtain ⟨hCv, -⟩ := hCounted
    simp only [Nat.add_sub_cancel] at hCv
    refine voters_count_lt_of_committee_majority (Q := S.P.committee s) (fun vote' hv => ?_)
      hMajority
    rcases (hCv vote').1 hv with ⟨hp, -⟩ | hinc
    · exact pool_committee_of_stateBefore S Sched x _ w s vote' hp
    · simp only [mem_included_votes_iff,
        Nat.add_sub_cancel] at hinc
      obtain ⟨B, ⟨hB, hBs⟩, hvB, -⟩ := hinc
      have h := (ac_valid_payload_facts S.P B (hPayload B hB hBs)).2.2 vote' hvB
      rw [hBs, Nat.add_sub_cancel] at h
      exact h
  -- step 5: Lemma 26
  exact lem26_goldfish_vote_extends_voter_majority_block S Sched x GST s Hs H R w vote hDiv hMono
    hSync hCatch hRoots hParent hOwner hGST hHs hVoters hw hF2 hF3 hLocks hSend

end GoldilocksCorrectness.Proofs.Executions
