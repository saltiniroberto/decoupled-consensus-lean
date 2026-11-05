module
public import GoldilocksCorrectness.Proofs.Executions.Lemma26
public import GoldilocksCorrectness.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Statements.Executions.DeliveryStatementsUpTo

@[expose] public section

/-!
# `Lemma26.lean` with the delivery premises up to a bound

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma26.lean` that name a delivery
premise, restated with `SynchronyFromWakeUpTo` and `CatchUpOnWakeUpTo` at a bound on the deadlines
. The bound of each twin
is the latest ordinary deadline `max t GST + Δ` of a send its proof reads, written in the twin's
own parameters.

* `lem26b_goldfish_vote_extends_voter_majority_block_held`

No `axiom`, no `native_decide`, no `sorry`. The landed page is imported, never edited.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slotStart_eq slot_eq_of_mem voteTime_eq
  voteTime_succ)

open GoldilocksCorrectness.Proofs.Routines (mem_fg_to_ac_tree)

open GoldilocksCorrectness.Proofs.Routines (get_anchor_mem_T)

open GoldilocksCorrectness.Proofs.Routines (fc_root_eq)

open GoldilocksCorrectness.Proofs.Routines (block_well_formed_iff goldfish_fork_choice_eq
  mem_included_support_votes_iff mem_included_votes_iff mem_viable_tree_iff wake_eq)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction AtomicHonest Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (StartsTowards RootsNameBlocksIn VotesOnceFor
  CountedVotes expireLocks)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  fc_root_ancestorEq_get_anchor mem_voter_block_tree_iff ac_valid_payload_facts
  tau_eq_some_blockStamp occurrenceBefore_eq_true_iff compatible_of_ancestorEq_compatible)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- Lemma 26b, the next slot's honest Goldfish vote names a block the voter holds, on the chain
of a block a voter majority voted for. Its reading is on the statement page,
`GoldilocksCorrectness/Statements/Executions/NextSlotVoteStatements.lean`.

Roots name blocks until `supportCutoff S s`: the bound of the Lemma 12 call at slot `s` it
passes the premise to.

Restated with the delivery premises up to `supportCutoff S s`: the slot-`s` votes reach `w` by then (`lem12_honest_vote_delivered_upTo`). -/
theorem lem26b_goldfish_vote_extends_voter_majority_block_held_upTo (S : Setup V)
    (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s : ℕ) (Hs : Finset V) (H : V → Block V)
    (R : Block V) (w : V) (vote : GoldfishVote V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S s))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S s))
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S s))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    (hGST : GST ≤ voteTime S s)
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ Sched.adv (voteTime S (s + 1) : Int) ∧
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      H u ∈ (stateBefore x (voteTime S s) u).S.T ∧ R.AncestorEq (H u))
    -- the validators with a vote among those `w`'s slot-`(s + 1)` vote counts are fewer than
    -- twice `Hs`
    (hVoters : ∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes S.C (stateBefore x (voteTime S (s + 1)) w).A
        (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) (s + 1) votes support_votes →
      voters_count votes < 2 * Hs.card)
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
    -- the block of every lock entry live at `t₃` that `w`'s revocation leaves is compatible
    -- with `R`
    (hLocks : ∀ A' : ACState V,
      revoke_locks S.P (expireLocks (stateBefore x (voteTime S (s + 1)) w).A
        ((voteTime S (s + 1) : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
        ((voteTime S (s + 1) : ℕ) : Int) (s + 1) = .ok A' →
      ∀ e ∈ A'.lock_entries,
        is_live (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
          ((voteTime S (s + 1) : ℕ) : Int) e = true → e.B.compatible R = true)
    (hSend : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (s + 1)) ∧
      (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent) :
    ∃ H_w ∈ (stateBefore x (voteTime S (s + 1)) w).S.T,
      vote = GoldfishVote.mk w (s + 1) H_w.root ∧ R.AncestorEq H_w := by
  have hFroot : (stateBefore x (voteTime S (s + 1)) w).S.F.AncestorEq
      (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).fc_root :=
    by rw [fc_root_eq]; exact F_ancestorEq_fc_root_of_stateBefore S Sched x (voteTime S (s + 1)) w
  -- the times
  have hΔ := one_le_Δ S
  have hss : slotStart S (s + 1) = slotStart S s + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hss' : slotStart S (s + 1 + 1) = slotStart S (s + 1) + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq S (s + 1), Nat.mul_add, Nat.mul_one]
  have hv₃ : voteTime S (s + 1) = slotStart S (s + 1) + Δ S := voteTime_eq S (s + 1)
  have hv₁ : voteTime S s = slotStart S s + Δ S := voteTime_eq S s
  have hslot₃ : S.C.slot ((voteTime S (s + 1) : ℕ) : Int) = s + 1 :=
    slot_eq_of_mem S (by omega) (by omega)
  have hfreeze : ∀ a d : Int, 0 < d → a + 2 * d < a + 3 * d := by
    intro a d hd
    omega
  have h23 : ((S.C.t_ s + 2 * S.C.Δ : Time) : Stamp) < ((S.C.t_ s + 3 * S.C.Δ : Time) : Stamp) :=
    WithBot.coe_lt_coe.2 (hfreeze _ _ S.C.Δ_pos)
  -- step 1: the run
  obtain ⟨i, hl, hm⟩ := hSend
  have hi : stepBefore x (voteTime S (s + 1)) = i := stepBefore_eq_of_lbl x hl
  have hti : x[i].time + 1 = voteTime S (s + 1) := (time_of_lbl_tickAllAwake x hl).1
  obtain ⟨-, n', sent, hrun, hvote⟩ := tick_send_of_honestSendAt hl hm
  have hRootsΦ : RootsNameBlocksIn (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).tree :=
    rootsNameBlocksIn_frame_of_exec_node S Sched x _ w
  -- step 2: the walk
  have hA : (tickInputState x i (voteTime S (s + 1)) w).A =
      (stateBefore x (voteTime S (s + 1)) w).A := by
    rw [(tickInputState_frame x i _ w).2.1]
    unfold stateBefore
    rw [hi]
  have hS : (tickInputState x i (voteTime S (s + 1)) w).S =
      (stateBefore x (voteTime S (s + 1)) w).S := by
    rw [(tickInputState_frame x i _ w).1]
    unfold stateBefore
    rw [hi]
  obtain ⟨-, hvi, hvs, -, A', votes, support_votes, vbt, H_w, hRevoke, hCounted, hvbt, hWalk,
      hhead, -⟩ :=
    GoldilocksCorrectness.Statements.Routines.lem14_tick_vote_walk S.C S.P S.X _ n' _ sent vote
      hrun hvote
  rw [hslot₃, hA, hS] at hRevoke hCounted hvbt
  rw [hslot₃, hS, Nat.add_sub_cancel] at hWalk
  -- the vote is `w`'s slot-`(s + 1)` vote for `H_w`
  have hv : (tickInputState x i (voteTime S (s + 1)) w).v = w := by
    have h := (lem11_node_invariant S Sched x i w).2.1
    unfold tickInputState
    split <;> (try rw [wake_eq]) <;> exact h
  rw [hv] at hvi
  rw [hslot₃] at hvs
  have hvote' : vote = GoldfishVote.mk w (s + 1) H_w.root := by
    rw [← hvi, ← hvs, ← hhead]
  -- the walk's end is a block `w` holds: a block of the viable tree of the voter's tree, or the
  -- anchor
  have hHwT : H_w ∈ (stateBefore x (voteTime S (s + 1)) w).S.T := by
    rcases GoldilocksCorrectness.Proofs.Routines.ghost_mem_tree_or_eq ((goldfish_fork_choice_eq ..).symm.trans hWalk) with h | h
    · rw [h]
      exact get_anchor_mem_T _ _ _
        (lem11_node_invariant S Sched x (stepBefore x (voteTime S (s + 1))) w).1.2.2.2.1
        (lem57_justification_cache_and_record S Sched x (stepBefore x (voteTime S (s + 1)))
          w).2.2.1
    · have h1 := ((mem_viable_tree_iff _ _ _).1 h).1
      have h2 := ((mem_voter_block_tree_iff S.C _ _ (s + 1) vbt hvbt H_w).1 h1).1
      exact ((mem_fg_to_ac_tree _ _).1 h2).1
  -- the case `R` an ancestor of `w`'s finalized block: the walk's end is the anchor or a
  -- descendant of it, the anchor is `fc_root` or a descendant of it, and `fc_root` is `w`'s
  -- finalized block or a descendant of it
  rcases (compatible_iff _ _).1 (compatible_of_ancestorEq_compatible hFroot hF2) with hFR | hRF
  swap
  · have hAH : (get_anchor A' (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
        ((voteTime S (s + 1) : ℕ) : Int)).AncestorEq H_w := by
      rcases GoldilocksCorrectness.Proofs.Routines.ghost_spec ((goldfish_fork_choice_eq ..).symm.trans hWalk) with hH | ⟨hAH, -⟩
      · rw [hH]
        exact ancestorEq_refl _
      · exact hAH
    exact ⟨H_w, hHwT, hvote', ancestorEq_trans hRF (ancestorEq_trans hFroot
      (ancestorEq_trans (fc_root_ancestorEq_get_anchor _ _ _) hAH))⟩
  -- the case `w`'s finalized block an ancestor of `R`, hence of every `H u`
  have hF1 : ∀ u ∈ Hs, (stateBefore x (voteTime S (s + 1)) w).S.F.AncestorEq (H u) :=
    fun u hu => ancestorEq_trans hFR (hHs u hu).2.2.2.2
  have hVb : voters_count votes < 2 * Hs.card := hVoters votes support_votes hCounted
  obtain ⟨hCv, hCs⟩ := hCounted
  simp only [Nat.add_sub_cancel] at hCv hCs
  -- step 3: the delivered votes
  have hHeld : ∀ u ∈ Hs, HeldEarlyVoteFor S.C (stateBefore x (voteTime S (s + 1)) w).A
      (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) s (H u) u :=
    GoldilocksCorrectness.Statements.Executions.lem12_honest_vote_delivered_upTo S Sched x GST s Hs H
      w hDiv hMono hSync hCatch hRoots hParent hOwner hGST
      (fun u hu => ⟨(hHs u hu).1, (hHs u hu).2.1, (hHs u hu).2.2.1, (hHs u hu).2.2.2.1⟩)
      hw hF1
  obtain ⟨u₀, hu₀⟩ : Hs.Nonempty := Finset.card_pos.1 (by omega)
  -- step 4: the locks
  have hLocksLive : ∀ e ∈ A'.lock_entries,
      is_live (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
        ((voteTime S (s + 1) : ℕ) : Int) e = true → e.B.compatible R = true :=
    hLocks A' hRevoke
  -- step 5: the anchor
  have hAnchor : (get_anchor A' (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
      ((voteTime S (s + 1) : ℕ) : Int)).compatible R = true :=
    GoldilocksCorrectness.Statements.Routines.lem6_get_anchor_compatible A' _ _ R hLocksLive
      hF2
  -- step 6: the start
  have hStart : StartsTowards (get_anchor A' (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
      ((voteTime S (s + 1) : ℕ) : Int)) R
      (viable_tree (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) vbt) := by
    rcases (compatible_iff _ _).1 hF2 with hRoot | hRoot
    · obtain ⟨W, hW, hWv, hRW⟩ := hF3 hRoot vbt hvbt
      refine GoldilocksCorrectness.Statements.Routines.lem7_startsTowards_of_compatible _ vbt _ R
        W hAnchor (fc_root_ancestorEq_get_anchor _ _ _) ?_ ⟨hW, hWv⟩ hRW
      intro P hXP _ hPR
      obtain ⟨-, -, hHΦ, ⟨y, hy, hyb⟩, -⟩ := hHeld u₀ hu₀
      have hHT : H u₀ ∈ (stateBefore x (voteTime S (s + 1)) w).S.T :=
        ((mem_fg_to_ac_tree _ _).1 hHΦ).1
      have hPH : P.AncestorEq (H u₀) := ancestorEq_trans hPR (hHs u₀ hu₀).2.2.2.2
      have hPT : P ∈ (stateBefore x (voteTime S (s + 1)) w).S.T :=
        ancestors_mem_T_of_exec S Sched x _ w _ P hHT hPH
      have hFP : (stateBefore x (voteTime S (s + 1)) w).S.F.AncestorEq P :=
        ancestorEq_trans hFroot (ancestorEq_trans (fc_root_ancestorEq_get_anchor _ _ _) hXP)
      have hPΦ : P ∈ (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).tree :=
        (mem_fg_to_ac_tree _ _).2 ⟨hPT, hFP⟩
      obtain ⟨τP, τH, hτP, hτH, hle⟩ := ancestor_blockStamp_le S Sched x _ w (H u₀) P hHT hPH
      obtain ⟨τH', hτH', hle'⟩ := tau_eq_some_blockStamp hRootsΦ hHΦ rfl hy
      have hτHH' : τH = τH' := Option.some_injective _ (hτH.symm.trans hτH')
      obtain ⟨y', hyy', hy'lt⟩ := (occurrenceBefore_eq_true_iff _ _).1 hyb
      have hyy : y = y' := Option.some_injective _ hyy'
      have hτlt : τP < ((S.C.t_ s + 3 * S.C.Δ : Time) : Stamp) :=
        lt_of_le_of_lt hle (hτHH' ▸ lt_of_le_of_lt hle' (hyy ▸ lt_trans hy'lt h23))
      refine (mem_voter_block_tree_iff S.C _ _ (s + 1) vbt hvbt P).2 ⟨hPΦ, τP, hτP, Or.inl ?_⟩
      rw [Nat.add_sub_cancel]
      exact hτlt
    · exact Or.inl (ancestorEq_trans hRoot (fc_root_ancestorEq_get_anchor _ _ _))
  -- step 7: the fork choice
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
  have hIncl : ∀ vote' ∈ included_votes (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
      (s + 1), ∃ B ∈ (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).tree,
        B.slot = s + 1 ∧ vote' ∈ B.votes ∧ vote'.slot = s := by
    intro vote' hv
    simp only [mem_included_votes_iff,
      Nat.add_sub_cancel] at hv
    obtain ⟨B, ⟨hB, hBs⟩, hvB, hvs⟩ := hv
    exact ⟨B, hB, hBs, hvB, hvs⟩
  have hSupport : support_votes ⊆ votes := by
    intro vote' hv
    rcases (hCs vote').1 hv with ⟨hp, hτ, -⟩ | ⟨hinc, -⟩
    · exact (hCv vote').2 (Or.inl ⟨hp, hτ⟩)
    · simp only [mem_included_support_votes_iff,
        Nat.add_sub_cancel] at hinc
      obtain ⟨B, ⟨hB, hBs⟩, hvB, hvs⟩ := hinc
      have hvB' : vote' ∈ B.votes :=
        (ac_valid_payload_facts S.P B (hPayload B hB hBs)).2.1 vote' hvB
      refine (hCv vote').2 (Or.inr ?_)
      simp only [mem_included_votes_iff,
        Nat.add_sub_cancel]
      exact ⟨B, ⟨hB, hBs⟩, hvB', hvs⟩
  have ht₁₃ : voteTime S s ≤ voteTime S (s + 1) := by
    rw [voteTime_succ]
    omega
  have hVotes : ∀ u ∈ Hs, VotesOnceFor (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) votes
      support_votes s R u := by
    intro u hu
    obtain ⟨hp, ⟨τ, hτ, hτlt⟩, hHΦ, ⟨y, hy, hyb⟩, huniq⟩ := hHeld u hu
    obtain ⟨y', hyy', hy'lt⟩ := (occurrenceBefore_eq_true_iff _ _).1 hyb
    have hyy : y = y' := Option.some_injective _ hyy'
    refine ⟨GoldfishVote.mk u s (H u).root,
      (hCs _).2 (Or.inl ⟨hp, ⟨τ, hτ, lt_trans hτlt h23⟩, ⟨y, hy, hyy ▸ lt_trans hy'lt h23⟩⟩),
      rfl, rfl, ⟨H u, hHΦ, rfl, (hHs u hu).2.2.2.2⟩, ?_⟩
    intro vote' hv' hi'
    rcases (hCv vote').1 hv' with ⟨hp', -⟩ | hinc
    · exact huniq vote' hp' hi'
    · obtain ⟨B, hB, hBs, hvB, hvs⟩ := hIncl vote' hinc
      obtain ⟨-, hhon, ⟨i₁, hl₁, hsent₁⟩, -, -⟩ := hHs u hu
      exact included_vote_eq_of_owner S Sched x (voteTime S (s + 1)) i₁ (voteTime S s) w u B _
        vote' hDiv hMono hOwner hhon ((mem_fg_to_ac_tree _ _).1 hB).1 (hBne B hBs) hvB hi' hl₁
        ht₁₃ hsent₁ hvs
  exact ⟨H_w, hHwT, hvote',
    GoldilocksCorrectness.Statements.Routines.lem2_goldfish_fork_choice_extends_majority_block
      S.C _ _ votes support_votes s _ R H_w _ Hs hStart hRootsΦ hSupport hVotes hVb hWalk⟩

end GoldilocksCorrectness.Proofs.Executions

