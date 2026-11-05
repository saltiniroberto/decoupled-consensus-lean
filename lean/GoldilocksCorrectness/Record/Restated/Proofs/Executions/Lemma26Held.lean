module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma26
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Relay
public import GoldilocksCorrectness.Proofs.Executions.Lemma26
public import GoldilocksCorrectness.Proofs.Executions.Relay

@[expose] public section

/-!
# Lemma26Held, over a model

The theorem of `GoldilocksCorrectness/Proofs/Executions/Lemma26Held.lean` over a model `M` whose
facts `F` hold, for an execution `x` of `protocolOf M S`: Lemma 26b with the votes of `Hs` held by
the voter as a hypothesis, in place of their delivery. The page's routine-level theorems are the
facts' fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime viewFreeze)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slotStart_eq slot_eq_of_mem viewFreeze_cast
  voteTime_eq voteTime_succ)

open GoldilocksCorrectness.Proofs.Routines (wake_eq)

open GoldilocksCorrectness.Proofs.Routines (goldfish_fork_choice_eq)

open GoldilocksCorrectness.Proofs.Routines (block_well_formed_iff)

namespace GoldilocksCorrectness.Record.Proofs.Executions

open GoldilocksCorrectness.Record.Statements.Routines (CountedVotes AwakeFor AnchorAt VoterTree
  VoterTreeAt)
open GoldilocksCorrectness.Proofs.Routines (compatible_of_ancestorEq_compatible
  occurrenceBefore_eq_true_iff)
open GoldilocksCorrectness.Record.Statements.Executions (HeldEarlyVoteAt)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (StartsTowards RootsNameBlocksIn VotesOnceFor
  expireLocks)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  mem_voter_block_tree_iff tau_eq_some_blockStamp occurrenceBefore_eq_true_iff
  compatible_of_ancestorEq_compatible)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- **Lemma 26b from held votes.** The proof; the audited statement is in
`Statements/Executions/NextSlotVoteHeldStatements.lean`.

The variables:
- `M`: the model; `F`: its facts.

Read aloud: the Goldfish vote `w` sends at the vote time of slot `s + 1` is for a block `H_w` that
`w` holds and that is `R` or a descendant of `R`, when `w` holds the early votes of `Hs` (for `R` or
descendants of `R`) and they are more than half of the voters `w` counts. -/
theorem lem26b_goldfish_vote_extends_voter_majority_block_of_held
    (U : UniformSchedule M.toSlotLayout)
    (S : Setup V)
    (A : Activity V) (x : Trace V (NamedObject V) M.N) (Run : RunFacts M S x) (s tb : ℕ) (Hs : Finset V)
    (H : V → Block V) (R : Block V) (w : V) (vote : GoldfishVote V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (hOwner : VotesCastByOwner M A x)
    (htb : tb ≤ M.viewFreeze S.C s)
    (hHs : ∀ u ∈ Hs, u ∉ A.corrupted (x.tickStep w (M.voteTime S.C (s + 1))) ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      R.AncestorEq (H u))
    (hHeld : (x.tickInput w (M.voteTime S.C (s + 1))).finalized.AncestorEq R →
      ∀ u ∈ Hs, HeldEarlyVoteAt M (x.tickInput w (M.voteTime S.C (s + 1))) ((tb : ℕ) : Int) s
        (H u) u)
    (hVoters : ∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1) votes support_votes →
      M.voters_count votes < 2 * Hs.card)
    (hF2 : (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.compatible R = true)
    (hF3 : (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.AncestorEq R →
      ∃ W, VoterTreeAt M (x.tickInput w (M.voteTime S.C (s + 1)))
          (S.C.t_ ((s + 1) - 1) + 3 * S.C.Δ) (s + 1) W ∧
        W ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).viable_heads ∧ R.AncestorEq W)
    (hLocks : (x.tickInput w (M.voteTime S.C (s + 1))).finalized.AncestorEq R →
      ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C (s + 1)))
        ((M.voteTime S.C (s + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1) →
      ∀ e ∈ M.lockEntries n',
        M.is_live (x.tickInput w (M.voteTime S.C (s + 1)))
          ((M.voteTime S.C (s + 1) : ℕ) : Int) e = true → e.B.compatible R = true)
    (hSend : ∃ i : ℕ, x.lbl i = Event.tick w (M.voteTime S.C (s + 1)) ∧
      (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i) :
    ∃ H_w ∈ (x.tickInput w (M.voteTime S.C (s + 1))).tree,
      vote = GoldfishVote.mk w (s + 1) H_w.root ∧ R.AncestorEq H_w := by
  letI : GoldilocksCorrectness.Statements.Routines.TieBreak V := M.tieBreak
  have hFroot : (x.tickInput w (M.voteTime S.C (s + 1))).finalized.AncestorEq (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F)]
    exact (GoldilocksCorrectness.Record.Statements.Executions.F_ancestorEq_fc_root_of_exec M F) S A x Run E
      (x.tickStep w (M.voteTime S.C (s + 1))) w
  -- the times; the slot of `t₃`, read by the spec's clock (the model's slot of a natural-number
  -- time is the spec's, `U`)
  have hΔ := one_le_Δ S
  have hss : M.slotStart S.C (s + 1) = M.slotStart S.C s + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add, Nat.mul_one]
  have hss' : M.slotStart S.C (s + 1 + 1) = M.slotStart S.C (s + 1) + 4 * Δ S := by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S (s + 1), Nat.mul_add, Nat.mul_one]
  have hv₃ : M.voteTime S.C (s + 1) = M.slotStart S.C (s + 1) + Δ S :=
    (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S (s + 1)
  have hv₁ : M.voteTime S.C s = M.slotStart S.C s + Δ S := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S s
  have hslot₃ : S.C.slot ((M.voteTime S.C (s + 1) : ℕ) : Int) = s + 1 := by
    rw [GoldilocksCorrectness.Proofs.Routines.slot_natCast,
      ← (GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U)]
    exact (GoldilocksCorrectness.Record.Proofs.Routines.slot_eq_of_mem M.toSlotLayout F.sched) S (by omega) (by omega)
  have h23 : ((((tb : ℕ) : Int) : Time) : Stamp) ≤ ((S.C.t_ s + 3 * S.C.Δ : Time) : Stamp) := by
    refine WithBot.coe_le_coe.2 ?_
    rw [← (GoldilocksCorrectness.Record.Proofs.Routines.viewFreeze_cast M.toSlotLayout F.sched U)]
    exact_mod_cast htb
  -- step 1: the run: `w`'s vote entered the sent log at the step `i`, `w`'s tick to `t₃`, which
  -- answered the outcome `(n', sent)` holding the vote
  obtain ⟨i, hl, hm⟩ := hSend
  obtain ⟨hwact, n', sent, hrun, hvote⟩ := (tick_send_of_honestSendAt M F Run E) hl hm
  have hRootsΦ : RootsNameBlocksIn (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).tree :=
    (GoldilocksCorrectness.Record.Statements.Executions.rootsNameBlocksIn_frame_of_exec_node M F) S A x Run E _ w
  have hti : x.tickInput w (M.voteTime S.C (s + 1)) = x.st i w := by
    unfold Trace.tickInput
    rw [(tickStep_eq_of_lbl M) x E hl]
  have hInvT : M.nodeInv S.C S.P S.X (x.tickInput w (M.voteTime S.C (s + 1))) := by
    rw [hti]
    exact (lem11_node_invariant M F S A x Run E i w (E.not_mem_corrupted_of_tick hl)).1
  -- step 2: the walk (Lemma 14 over the record, the field `tick_vote_head` of `F.tk3`, from the
  -- tick's input state; the tick ran from `w`'s state before `t₃`, awake for the slot): `w`'s vote
  -- is for the end `H_w` of the walk through the viable part of `w`'s voter's tree (`VoterTree`),
  -- from the anchor over `w`'s frame with the lock entries the tick left (`AnchorAt`)
  obtain ⟨-, hvi, hvs, -, ⟨τw, hτw, hτwle⟩, H_w, ⟨votes, support_votes, hCounted, hWalk⟩, hhead⟩ :=
    (GoldilocksCorrectness.Record.Statements.Routines.lem14_tick_vote_walk F) S.C S.P S.X _ n' _ sent vote hrun hInvT hvote
  -- the tick reads `w`'s tick input itself (the kit's outcome is at it)
  have hTISw : x.tickInput w (M.voteTime S.C (s + 1)) = x.tickInput w (M.voteTime S.C (s + 1)) := rfl
  rw [hslot₃] at hτwle hvs
  have hAwake : AwakeFor M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1) := by
    refine ⟨τw, ?_, hτwle⟩
    rw [← hTISw]
    exact hτw
  have hrun' : .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C (s + 1))) ((M.voteTime S.C (s + 1) : ℕ) : Int) := by
    rw [← hTISw]
    exact hrun
  rw [hTISw, hslot₃] at hCounted hWalk
  rw [Nat.add_sub_cancel] at hWalk
  have hInvW : M.nodeInv S.C S.P S.X (x.tickInput w (M.voteTime S.C (s + 1))) := hInvT
  -- the vote is `w`'s slot-`(s + 1)` vote for `H_w` (the validator of the tick's input state is
  -- `w`, Lemma 11)
  rw [hti, (lem11_node_invariant M F S A x Run E i w (E.not_mem_corrupted_of_tick hl)).2.1] at hvi
  have hvote' : vote = GoldfishVote.mk w (s + 1) H_w.root := by
    rw [← hvi, ← hvs, ← hhead]
  -- the walk's end is a block `w` holds: a block of the viable part of the voter's tree, or the
  -- anchor, which is the fgroot (the justified or the finalized block) or a block of the viable
  -- tree
  have hHwT : H_w ∈ (x.tickInput w (M.voteTime S.C (s + 1))).tree := by
    have hmemT : ∀ D ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).tree, D ∈ (x.tickInput w (M.voteTime S.C (s + 1))).tree :=
      fun D hD => (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hD).1
    rcases GoldilocksCorrectness.Proofs.Routines.walkEnd_mem_tree_or_eq hWalk with h | h
    · rw [h]
      rcases GoldilocksCorrectness.Record.Proofs.Routines.anchorAt_cases M (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))) n'.lockEntries ((M.voteTime S.C (s + 1) : ℕ) : Int) with h' | h'
      · rw [h', (GoldilocksCorrectness.Record.Proofs.Routines.fc_root_eq M F), F.ndAdded.get_fc_root_eq hInvW]
        split
        · exact F.nd.nodeInv_justifiedInTree hInvW
        · exact F.nd.nodeInv_finalized_mem_tree hInvW
      · exact hmemT _ (((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_tree_iff M F) _ _ _).1 h').1
    · have h1 := (((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_tree_iff M F) _ _ _).1 h).1
      exact hmemT _ ((GoldilocksCorrectness.Record.Statements.Routines.mem_voter_block_tree_iff_at S.C _ (s + 1) H_w).1 h1).1
  -- the anchor is a descendant of the fgroot (or the fgroot)
  have hRAw : (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.AncestorEq (AnchorAt M (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))) n'.lockEntries ((M.voteTime S.C (s + 1) : ℕ) : Int)) := by
    rcases GoldilocksCorrectness.Record.Proofs.Routines.anchorAt_cases M (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))) n'.lockEntries ((M.voteTime S.C (s + 1) : ℕ) : Int) with h | h
    · rw [h]
      exact ancestorEq_refl _
    · exact (((GoldilocksCorrectness.Record.Proofs.Routines.mem_viable_tree_iff M F) _ _ _).1 h).2.1
  -- the case `R` an ancestor of `w`'s finalized block: the walk's end is the anchor or a
  -- descendant of it, the anchor is the fgroot or a descendant of it, and the fgroot is `w`'s
  -- finalized block or a descendant of it
  rcases (compatible_iff _ _).1 (compatible_of_ancestorEq_compatible hFroot hF2) with hFR | hRF
  swap
  · have hAH : (AnchorAt M (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))) n'.lockEntries ((M.voteTime S.C (s + 1) : ℕ) : Int)).AncestorEq H_w := GoldilocksCorrectness.Proofs.Routines.ancestorEq_of_walkSteps hWalk.1
    exact ⟨H_w, hHwT, hvote', ancestorEq_trans hRF (ancestorEq_trans hFroot (ancestorEq_trans hRAw hAH))⟩
  -- the case `w`'s finalized block an ancestor of `R`, hence of every `H u`
  have hVb : M.voters_count votes < 2 * Hs.card := hVoters votes support_votes hCounted
  have hCv := hCounted.1
  have hCs := hCounted.2
  simp only [Nat.add_sub_cancel] at hCv hCs
  -- step 3: the votes held
  have hHeld := hHeld hFR
  obtain ⟨u₀, hu₀⟩ : Hs.Nonempty := Finset.card_pos.1 (by omega)
  -- step 4: the locks: the block of every lock entry the tick at `t₃` left, live at `t₃`, is
  -- compatible with `R`
  have hLocksLive := hLocks hFR n' sent hrun' hAwake
  -- step 5: the anchor is compatible with `R`: it is the fgroot (compatible with `R` by F2), or an
  -- ancestor of the block of a live lock entry the tick left
  have hAnchor : (AnchorAt M (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))) n'.lockEntries ((M.voteTime S.C (s + 1) : ℕ) : Int)).compatible R = true := by
    rcases GoldilocksCorrectness.Record.Proofs.Routines.anchorAt_cases_locked M (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))) n'.lockEntries ((M.voteTime S.C (s + 1) : ℕ) : Int) with h | ⟨-, e, he, hd, heT, hAe⟩
    · rw [h]
      exact hF2
    · have hlive : M.is_live (x.tickInput w (M.voteTime S.C (s + 1))) ((M.voteTime S.C (s + 1) : ℕ) : Int) e = true := by
        simp only [(GoldilocksCorrectness.Record.Proofs.Routines.is_live_iff M F)]
        exact ⟨hd, heT⟩
      exact compatible_of_ancestorEq_compatible hAe (hLocksLive e he hlive)
  -- step 6: the start: when `R` is the fgroot or an ancestor of it, the anchor is a descendant of
  -- the fgroot; otherwise Lemma 7 with F3's viable head, every block after the anchor up to `R`
  -- being in the voter's tree: it is in `w`'s tree as an ancestor of `H u₀`, has `w`'s finalized
  -- block as an ancestor through the fgroot and the anchor, and is stamped no later than `H u₀`,
  -- which is stamped no later than the resolution of `u₀`'s vote, strictly before
  -- `S.C.t_ s + 2 · S.C.Δ`, hence before the view freeze `S.C.t_ s + 3 · S.C.Δ`
  have hStart : StartsTowards (AnchorAt M (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))) n'.lockEntries ((M.voteTime S.C (s + 1) : ℕ) : Int)) R (M.viable_tree (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))) (VoterTree M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1))) := by
    rcases (compatible_iff _ _).1 hF2 with hRoot | hRoot
    · obtain ⟨W, hW, hWv, hRW⟩ := hF3 hRoot
      refine (GoldilocksCorrectness.Record.Statements.Routines.lem7_startsTowards_of_compatible M F) _ _ _ R W hAnchor hRAw ?_
        ⟨(GoldilocksCorrectness.Record.Statements.Routines.mem_voter_block_tree_iff_at S.C _ (s + 1) W).2 hW, hWv⟩ hRW
      intro P hXP _ hPR
      obtain ⟨-, -, hHΦ, ⟨y, hy, hyb⟩, -⟩ := hHeld u₀ hu₀
      have hHT : H u₀ ∈ (x.tickInput w (M.voteTime S.C (s + 1))).tree := (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hHΦ).1
      have hPH : P.AncestorEq (H u₀) := ancestorEq_trans hPR (hHs u₀ hu₀).2.2
      have hPT : P ∈ (x.tickInput w (M.voteTime S.C (s + 1))).tree :=
        (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S A x Run E _ w _ P hHT hPH
      have hFP : (x.tickInput w (M.voteTime S.C (s + 1))).finalized.AncestorEq P :=
        ancestorEq_trans hFroot (ancestorEq_trans hRAw hXP)
      have hPΦ : P ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).tree := ((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).2 ⟨hPT, hFP⟩
      obtain ⟨τP, τH, hτP, hτH, hle⟩ := (ancestor_blockStamp_le M F) S A x Run E _ w (H u₀) P hHT hPH
      -- the resolution of `u₀`'s vote is the later of its stamp and its head block's
      obtain ⟨τv, τH', H', -, hH'Φ, hroot, -, hτH', hy'⟩ := hy
      have hH' : H' = H u₀ := hRootsΦ H' hH'Φ (H u₀) hHΦ hroot
      rw [hH'] at hτH'
      have hτHH' : τH = τH' := Option.some_injective _ (hτH.symm.trans hτH')
      obtain ⟨y', hyy', hy'lt⟩ := (occurrenceBefore_eq_true_iff _ _).1 hyb
      have hyy : y = y' := Option.some_injective _ hyy'
      have hτle : τH' ≤ y := by rw [hy']; exact le_max_right _ _
      have hτlt : τP < ((S.C.t_ s + 3 * S.C.Δ : Time) : Stamp) :=
        lt_of_le_of_lt hle (hτHH' ▸ lt_of_le_of_lt hτle (hyy ▸ lt_of_lt_of_le hy'lt h23))
      refine (GoldilocksCorrectness.Record.Statements.Routines.mem_voter_block_tree_iff_at S.C _ (s + 1) P).2 ⟨hPΦ, τP, hτP, Or.inl ?_⟩
      rw [Nat.add_sub_cancel]
      exact hτlt
    · exact Or.inl (ancestorEq_trans hRoot hRAw)
  -- step 7: the walk: Lemma 2 over the walk predicate with `Sup := Hs`, every support vote being
  -- counted (an included support vote is one of its block's votes, the block well formed by the
  -- node invariant), each `u ∈ Hs` voting once among the counted votes (a counted pool vote by
  -- `HeldEarlyVoteFor`'s uniqueness, a counted included vote by `included_vote_eq_of_owner`), and
  -- `hVoters` on the counted sets
  have hBne : ∀ B : Block V, B.slot = s + 1 → B ≠ Block.genesis := by
    rintro B hBs rfl
    exact Nat.succ_ne_zero s hBs.symm
  have hPayload : ∀ B ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).tree, B.slot = s + 1 → M.ac_valid_payload S.P B = true := by
    intro B hB hBs
    have hBT := (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hB).1
    have hwf := ((F.nd.nodeInv_treeClosed hInvW).2 B hBT (hBne B hBs)).2.1
    exact ((F.rd.block_well_formed_iff S.P S.X B).1 hwf).1.2
  have hIncl : ∀ vote' ∈ M.included_votes (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))) (s + 1), ∃ B ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).tree,
      B.slot = s + 1 ∧ vote' ∈ B.votes ∧ vote'.slot = s := by
    intro vote' hv
    simp only [(GoldilocksCorrectness.Record.Proofs.Routines.mem_included_votes_iff M F), Nat.add_sub_cancel] at hv
    obtain ⟨B, ⟨hB, hBs⟩, hvB, hvs⟩ := hv
    exact ⟨B, hB, hBs, hvB, hvs⟩
  have hSupport : support_votes ⊆ votes := by
    intro vote' hv
    rcases (hCs vote').1 hv with ⟨hp, hτ, -⟩ | ⟨hinc, -⟩
    · exact (hCv vote').2 (Or.inl ⟨hp, hτ⟩)
    · simp only [(GoldilocksCorrectness.Record.Proofs.Routines.mem_included_support_votes_iff M F), Nat.add_sub_cancel] at hinc
      obtain ⟨B, ⟨hB, hBs⟩, hvB, hvs⟩ := hinc
      have hvB' : vote' ∈ B.votes :=
        ((GoldilocksCorrectness.Record.Proofs.Routines.ac_valid_payload_facts M F) S.P B (hPayload B hB hBs)).2.1 vote' hvB
      refine (hCv vote').2 (Or.inr ?_)
      simp only [(GoldilocksCorrectness.Record.Proofs.Routines.mem_included_votes_iff M F), Nat.add_sub_cancel]
      exact ⟨B, ⟨hB, hBs⟩, hvB', hvs⟩
  have hVotes : ∀ u ∈ Hs, VotesOnceFor (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))) votes support_votes s R u := by
    intro u hu
    obtain ⟨hp, ⟨τ, hτ, hτlt⟩, hHΦ, ⟨y, hy, hyb⟩, huniq⟩ := hHeld u hu
    obtain ⟨y', hyy', hy'lt⟩ := (occurrenceBefore_eq_true_iff _ _).1 hyb
    have hyy : y = y' := Option.some_injective _ hyy'
    refine ⟨GoldfishVote.mk u s (H u).root,
      (hCs _).2 (Or.inl ⟨hp, ⟨τ, hτ, lt_of_lt_of_le hτlt h23⟩,
        ⟨y, hy, hyy ▸ lt_of_lt_of_le hy'lt h23⟩⟩),
      rfl, rfl, ⟨H u, hHΦ, rfl, (hHs u hu).2.2⟩, ?_⟩
    intro vote' hv' hi'
    rcases (hCv vote').1 hv' with ⟨hp', -⟩ | hinc
    · exact huniq vote' hp' hi'
    · obtain ⟨B, hB, hBs, hvB, hvs⟩ := hIncl vote' hinc
      obtain ⟨hhon, ⟨i₁, hl₁, hsent₁⟩, -⟩ := hHs u hu
      -- `u` is outside the adversary set at `w`'s tick step `i`, where `w`'s tree is read
      rw [(tickStep_eq_of_lbl M) x E hl] at hhon
      have hBi : B ∈ (x.st i w).tree := by
        rw [← hti]
        exact (((GoldilocksCorrectness.Record.Proofs.Routines.mem_fg_to_ac_tree M F) _ _).1 hB).1
      exact (included_vote_eq_of_owner_st M F) S A x Run i i₁ (M.voteTime S.C s) w u B
        _ vote' E hOwner hhon hBi (hBne B hBs) hvB hi' hl₁ hsent₁ hvs
  exact ⟨H_w, hHwT, hvote',
    GoldilocksCorrectness.Statements.Routines.lem2_goldfish_walkEnd_extends_majority_block
      S.C _ _ votes support_votes s _ R H_w _ Hs hStart hRootsΦ hSupport hVotes
      (by rw [← GoldilocksCorrectness.Record.Proofs.Routines.voters_count_eq_spec F]; exact hVb) hWalk⟩

end GoldilocksCorrectness.Record.Proofs.Executions

