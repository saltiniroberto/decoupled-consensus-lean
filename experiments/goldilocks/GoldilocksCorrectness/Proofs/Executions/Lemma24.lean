module
public import GoldilocksCorrectness.Proofs.Executions.ViableAgreement
public import GoldilocksCorrectness.Statements.Executions.ProposalVoteStatements
public import GoldilocksCorrectness.Statements.Executions.CountAgreementStatements
public import GoldilocksCorrectness.Statements.Executions.ProposalPropagationStatements

@[expose] public section

/-! G0F-2 (a), `B` passes `w`'s viability test
and `w` holds `B` by Lemmas 22a and 22; G0F-3 (a), `p`'s walk re-derived by
`proposal_parent_extends_majority_block`, `Lemma20.lean` unchanged. Write
`t₁ := slotStart S (s + 1)`, the time of `p`'s proposal, and `t₃ := voteTime S (s + 1)`, the time of
`w`'s vote; `S_p`, `A_p`, `Φ_p` for the FG state, the AC state and the frame of `p`'s state before
`t₁`, and `S_w`, `A_w`, `Φ_w` for those of `w`'s state before `t₃`. The proof composes `lem20` with
the lemmas that discharge five of its hypotheses:

1. the end of `p`'s walk (`proposal_parent_walk_end`): `B` is a non-genesis block of slot `s + 1`,
   and `B`'s parent is in `p`'s viable tree or is `p`'s anchor;
2. `B`'s parent is in `S_p.T`, and `p`'s finalized block is an ancestor of `B` (through `B`'s
   parent, by the frame tree or the anchor);
3. `p` holds `B` after its tick (Lemma 22a), so `w` holds `B` before `t₃` (Lemma 22): `hBw`;
4. `B` is in `Φ_w.tree`, and is a viable head of `Φ_w` (`mem_viable_heads_iff`, with `hBViable`);
5. the two validators count alike on the blocks that descend from both finalized blocks
   (Lemma 23): `hCount`, a child of a block from `X` to `B`'s parent past the root of `w`'s fork
   choice descending from `p`'s finalized block through `X` and from `w`'s through that root;
6. they agree on the viable heads along the path from `X` to `B`'s parent, past the root of `w`'s
   fork choice (`viable_heads_agree_of_floor_eq`): `hViableAgree`;
7. every child in `w`'s viable tree of a block of that path, other than `B`, is in `p`'s viable
   tree (`child_mem_proposer_viable_tree`): `hChild`;
8. Lemma 20.



 the root's ancestry to `B` is the hypothesis
itself, and the live locks go to Lemma 20 unchanged.

 it calls `proposal_parent_walk_end`, the conclusions that do not read the votes, and
step 2 derives `p`'s finalized block as an ancestor of `B` through `B`'s parent instead of `X`.
`hVoters` goes to Lemma 20 unchanged.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff viewFreeze)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slotStart_eq slot_eq_of_mem supportCutoff_eq
  viewFreeze_eq voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (mem_fg_to_ac_tree mem_viable_heads_iff)

open GoldilocksCorrectness.Proofs.Routines (fc_root_eq goldfish_fork_choice_eq is_viable_iff
  mem_viable_tree_iff)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (expireLocks CountedVotes)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_trans compatible_iff
  fc_root_ancestorEq_get_anchor ancestorEq_of_parent? ghost_mem_tree_or_eq)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- The honest proposal of slot `s + 1` is a block of that slot other than the genesis block, its
parent link names its parent, and that parent, where `p`'s walk ended, is in `p`'s viable tree or
is `p`'s anchor at the start `t₁` of slot `s + 1`. These are the conclusions of
`proposal_parent_extends_majority_block` that do not read the votes, from step 1 of its proof
(Lemma 19 on `p`'s tick) and the end of `p`'s walk (`ghost_mem_tree_or_eq`). They are all Lemma
24's proof reads of `p`'s walk: that `X` is `B`'s parent or an ancestor of it, the conclusion that
needs a bound on `p`'s voters, Lemma 20 derives itself. Lemma 24 cannot take that bound before
step 5: it has it only from Lemma 23 (`p` counts as many voters as `w`), which needs `w` to hold
`B`, which is derived from these.

The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution; `s`: the slot before the proposal's;
  `i`: the step of `p`'s tick at the start of slot `s + 1`;
- `B`: the block `p` proposed at the start of slot `s + 1`; `p`: the proposer of slot `s + 1`.

Read aloud: the block `p` put on the wire at its tick at the start of slot `s + 1` is a
non-genesis block of that slot whose parent is in `p`'s viable tree or is `p`'s anchor. -/
theorem proposal_parent_walk_end (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s i : ℕ) (B : Block V) (p : V)
    -- `p`'s tick at the start of slot `s + 1` is the step `i`, and put `B` on the wire
    (hl : x.lbl i = AtomicAction.tickAllAwake (slotStart S (s + 1)))
    (hsent : (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
      x[i + 1].sent - x[i].sent) :
    B.slot = s + 1 ∧ B ≠ Block.genesis ∧ B.parent? = some B.parent ∧
      (B.parent ∈ viable_tree (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S)
          (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).tree ∨
        B.parent = get_anchor (stateBefore x (slotStart S (s + 1)) p).A
          (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S)
          ((slotStart S (s + 1) : ℕ) : Int)) := by
  have hΔ := one_le_Δ S
  have hss : slotStart S (s + 1) = slotStart S s + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hss' : slotStart S (s + 1 + 1) = slotStart S (s + 1) + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq S (s + 1), Nat.mul_add, Nat.mul_one]
  have hslot₁ : S.C.slot ((slotStart S (s + 1) : ℕ) : Int) = s + 1 :=
    slot_eq_of_mem S (le_refl _) (by omega)
  have hi : stepBefore x (slotStart S (s + 1)) = i := stepBefore_eq_of_lbl x hl
  obtain ⟨-, n₁', sent₁, hrun₁, hB₁⟩ := tick_send_of_honestSendAt hl hsent
  have hAp : (tickInputState x i (slotStart S (s + 1)) p).A =
      (stateBefore x (slotStart S (s + 1)) p).A := by
    rw [(tickInputState_frame x i _ p).2.1]
    unfold stateBefore
    rw [hi]
  have hSp : (tickInputState x i (slotStart S (s + 1)) p).S =
      (stateBefore x (slotStart S (s + 1)) p).S := by
    rw [(tickInputState_frame x i _ p).1]
    unfold stateBefore
    rw [hi]
  obtain ⟨-, -, -, Hp, votes_pl, support_pl, -, -, hWalkP, hBdef⟩ :=
    GoldilocksCorrectness.Statements.Routines.lem19_tick_proposes S.C S.P S.X _ n₁' _ sent₁ B
      hrun₁ hB₁
  rw [hslot₁, Nat.add_sub_cancel, hAp, hSp] at hWalkP
  rw [hslot₁] at hBdef
  have hBpar : B.parent = Hp := by rw [hBdef]; rfl
  have hBslot : B.slot = s + 1 := by rw [hBdef]; rfl
  have hBne : B ≠ Block.genesis := by rw [hBdef]; exact fun h => by cases h
  have hBpar? : B.parent? = some Hp := by rw [hBdef]; rfl
  -- the end of `p`'s walk: `goldfish_fork_choice` is `ghost` (`goldfish_fork_choice_eq`)
  rw [goldfish_fork_choice_eq] at hWalkP
  have hEnd := ghost_mem_tree_or_eq (show ghost _ _ _ _ = .ok Hp from hWalkP)
  rw [hBpar]
  exact ⟨hBslot, hBne, hBpar?, hEnd.symm⟩

/-- Lemma 24, the next slot's honest vote names the honest proposal, composed (G0 over
executions). Its reading is on the statement page,
`GoldilocksCorrectness/Statements/Executions/ComposedProposalVoteStatements.lean`.

Roots name blocks until `voteTime S (s + 1)`: Lemma 22 and Lemma 23, which the proof calls, take
blocks as held up to `w`'s vote time of slot `s + 1`; Lemma 20 and
`child_mem_proposer_viable_tree` read earlier. -/
theorem lem24_goldfish_vote_names_honest_proposal_composed (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s : ℕ) (Hs : Finset V) (H : V → Block V)
    (X B : Block V) (p w : V) (vote : GoldfishVote V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (voteTime S (s + 1)))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    (hGST : GST ≤ voteTime S s)
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ Sched.adv (voteTime S (s + 1) : Int) ∧
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      H u ∈ (stateBefore x (voteTime S s) u).S.T ∧ X.AncestorEq (H u))
    (hVoters : ∀ votes_w support_w : Finset (GoldfishVote V),
      CountedVotes S.C (stateBefore x (voteTime S (s + 1)) w).A
        (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) (s + 1) votes_w support_w →
      voters_count votes_w < 2 * Hs.card)
    (hp : ∀ t : ℕ, voteTime S s ≤ t → t ≤ slotStart S (s + 1) →
      p ∈ Sched.awake (t : Int) ∧ p ∉ Sched.adv (t : Int))
    (hw : ∀ t : ℕ, voteTime S s ≤ t → t ≤ voteTime S (s + 1) →
      w ∈ Sched.awake (t : Int) ∧ w ∉ Sched.adv (t : Int))
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    (hSend : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (s + 1)) ∧
      (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent)
    (hOnly : ∀ B' ∈ (stateBefore x (voteTime S (s + 1)) w).S.T, B'.slot = s + 1 → B' = B)
    (hRootNew : ∀ B' ∈ (stateBefore x (slotStart S (s + 1)) p).S.T, B'.root ≠ B.root)
    (hF3p : ∃ W ∈ (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).tree,
      W ∈ (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).viable_heads ∧ X.AncestorEq W)
    (hApX : (get_anchor (stateBefore x (slotStart S (s + 1)) p).A
      (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S)
      ((slotStart S (s + 1) : ℕ) : Int)).AncestorEq X)
    (hF2w : (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).fc_root.AncestorEq B)
    (hLocksW : ∀ A' : ACState V,
      revoke_locks S.P (expireLocks (stateBefore x (voteTime S (s + 1)) w).A
        ((voteTime S (s + 1) : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
        ((voteTime S (s + 1) : ℕ) : Int) (s + 1) = .ok A' →
      ∀ e ∈ A'.lock_entries,
        is_live (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
          ((voteTime S (s + 1) : ℕ) : Int) e = true → e.B.AncestorEq B)
    -- `B` passes `w`'s viability test
    (hBViable : is_viable (stateBefore x (voteTime S (s + 1)) w).S B = true)
    -- the two validators have the same least viable height
    (hFloor : head_height_floor (stateBefore x (slotStart S (s + 1)) p).S =
      head_height_floor (stateBefore x (voteTime S (s + 1)) w).S) :
    vote.head = B.root := by
  have hF2p : (stateBefore x (slotStart S (s + 1)) p).S.F.AncestorEq
      (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).fc_root := by
    rw [fc_root_eq]; exact F_ancestorEq_fc_root_of_stateBefore S Sched x (slotStart S (s + 1)) p
  have hFroot : (stateBefore x (voteTime S (s + 1)) w).S.F.AncestorEq
      (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).fc_root := by
    rw [fc_root_eq]; exact F_ancestorEq_fc_root_of_stateBefore S Sched x (voteTime S (s + 1)) w
  -- the times
  have hΔ := one_le_Δ S
  have hss : slotStart S (s + 1) = slotStart S s + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hc₀ : supportCutoff S s = voteTime S s + Δ S := supportCutoff_eq S s
  have hv₁ : voteTime S s = slotStart S s + Δ S := voteTime_eq S s
  have hv₃ : voteTime S (s + 1) = slotStart S (s + 1) + Δ S := voteTime_eq S (s + 1)
  have hfz : viewFreeze S s = slotStart S s + 3 * Δ S := viewFreeze_eq S s
  -- the windows the callees read: `p` from the vote time of slot `s` to its support cutoff and
  -- from the view freeze of slot `s` to `t₁`; `w` from the vote time of slot `s` to its support
  -- cutoff and from `t₁` to `t₃`
  have hpC : ∀ t : ℕ, voteTime S s ≤ t → t ≤ supportCutoff S s →
      p ∈ Sched.awake (t : Int) ∧ p ∉ Sched.adv (t : Int) :=
    fun t h1 h2 => hp t h1 (by omega)
  have hpF : ∀ t : ℕ, viewFreeze S s ≤ t → t ≤ slotStart S (s + 1) →
      p ∈ Sched.awake (t : Int) ∧ p ∉ Sched.adv (t : Int) :=
    fun t h1 h2 => hp t (by omega) h2
  have hwC : ∀ t : ℕ, voteTime S s ≤ t → t ≤ supportCutoff S s →
      w ∈ Sched.awake (t : Int) ∧ w ∉ Sched.adv (t : Int) :=
    fun t h1 h2 => hw t h1 (by omega)
  have hwV : ∀ t : ℕ, slotStart S (s + 1) ≤ t → t ≤ voteTime S (s + 1) →
      w ∈ Sched.awake (t : Int) ∧ w ∉ Sched.adv (t : Int) :=
    fun t h1 h2 => hw t (by omega) h2
  have hpt₁ : p ∉ Sched.adv (slotStart S (s + 1) : Int) :=
    (hp (slotStart S (s + 1)) (by omega) le_rfl).2
  -- step 1: the end of `p`'s walk (that `X` is `B`'s parent or an ancestor of it is not needed
  -- here: Lemma 20 derives it)
  obtain ⟨i, hl, hsent⟩ := id hPropose
  obtain ⟨hBslot, -, hBpar?, hEnd⟩ := proposal_parent_walk_end S Sched x s i B p hl hsent
  have hPB : B.parent.AncestorEq B := ancestorEq_of_parent? hBpar?
  -- the ancestry facts at the two validators: `X` descends from `p`'s finalized block through
  -- the root of `p`'s fork choice and `p`'s anchor; `B` descends from `w`'s finalized block through
  -- the root of `w`'s fork choice
  have hRXp : (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).fc_root.AncestorEq X :=
    ancestorEq_trans (fc_root_ancestorEq_get_anchor _ _ _) hApX
  have hFXp : (stateBefore x (slotStart S (s + 1)) p).S.F.AncestorEq X :=
    ancestorEq_trans hF2p hRXp
  have hRBw : (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).fc_root.AncestorEq B :=
    hF2w
  -- step 2: `B`'s parent is in `p`'s tree, and `p`'s finalized block is an ancestor of `B`
  have hParentHeld : B.parent ∈ (stateBefore x (slotStart S (s + 1)) p).S.T := by
    rcases hEnd with hin | heq
    · exact ((mem_fg_to_ac_tree _ _).1 ((mem_viable_tree_iff _ _ _).1 hin).1).1
    · -- `B`'s parent is `p`'s anchor, an ancestor of `X`, which `p`'s tree holds by `hF3p`
      obtain ⟨W, hW, -, hXW⟩ := hF3p
      refine ancestors_mem_T_of_exec S Sched x _ p W B.parent ((mem_fg_to_ac_tree _ _).1 hW).1 ?_
      rw [heq]
      exact ancestorEq_trans hApX hXW
  have hFpB : (stateBefore x (slotStart S (s + 1)) p).S.F.AncestorEq B := by
    refine ancestorEq_trans ?_ hPB
    rcases hEnd with hin | heq
    · exact ((mem_fg_to_ac_tree _ _).1 ((mem_viable_tree_iff _ _ _).1 hin).1).2
    · -- `B`'s parent is `p`'s anchor, which has the root of `p`'s fork choice as an ancestor
      rw [heq]
      exact ancestorEq_trans hF2p (fc_root_ancestorEq_get_anchor _ _ _)
  -- step 3: `p` holds `B` after its tick (Lemma 22a), and `w` before `t₃` (Lemma 22)
  have hBp : B ∈ (x[i + 1][p].st).S.T :=
    GoldilocksCorrectness.Statements.Executions.lem22a_proposer_holds_own_proposal S Sched x s i B p
      hDiv hMono hl hsent hRootNew hParentHeld ((compatible_iff _ _).2 (Or.inl hFpB))
  have hFwB : (stateBefore x (voteTime S (s + 1)) w).S.F.AncestorEq B :=
    ancestorEq_trans hFroot hRBw
  have hBw : B ∈ (stateBefore x (voteTime S (s + 1)) w).S.T :=
    GoldilocksCorrectness.Statements.Executions.lem22_proposal_held_by_voter S Sched x GST s i B p
      w hDiv hMono hSync hCatch hRoots hParent hGST hpt₁ hwV hl hsent hBp
      ((compatible_iff _ _).2 (Or.inl hFwB))
  -- step 4: `B` is in `w`'s frame tree, and is a viable head there
  have hBΦ : B ∈ (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).tree :=
    (mem_fg_to_ac_tree _ _).2 ⟨hBw, hFwB⟩
  have hBfl : head_height_floor (stateBefore x (voteTime S (s + 1)) w).S ≤
      ((stateBefore x (voteTime S (s + 1)) w).S.σ B).h :=
    (is_viable_iff _ _).1 hBViable
  have hBVH : B ∈ (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).viable_heads :=
    (mem_viable_heads_iff _ _).2 ⟨hBw, hFwB, hRBw, hBfl⟩
  -- step 5: the two validators count alike (Lemma 23), on the blocks that descend from both
  -- finalized blocks
  have hCount := GoldilocksCorrectness.Statements.Executions.lem23_proposer_and_voter_count_alike
    S Sched x GST s B p w hDiv hMono hSync hCatch hRoots hParent hGST hpF hwV hPropose hBΦ
    hOnly
  -- step 6: the two validators agree on the viable heads along the path, past the root of `w`'s
  -- fork choice
  have hViableAgree := viable_heads_agree_of_floor_eq S Sched x s X B p w hParentHeld
    hBw hFXp hRXp hFloor
  -- step 7: every child in `w`'s viable tree of a block of the path, other than `B`, is in `p`'s
  have hChild := child_mem_proposer_viable_tree S Sched x GST s X B p w hDiv hMono hSync hCatch
    (hRoots.mono (by omega)) hParent hGST hpF hwV hOnly hEnd hApX (le_of_eq hFloor)
  -- step 8: Lemma 20; a child `D` of a path block `Y` past the root of `w`'s fork choice descends
  -- from `p`'s finalized block through `X`, and from `w`'s through that root
  exact GoldilocksCorrectness.Statements.Executions.lem20_goldfish_vote_names_honest_proposal S
    Sched x GST s Hs H X B p w vote hDiv hMono hSync hCatch (hRoots.mono (by omega)) hParent
    hOwner hGST hHs
    hVoters hpC hwC hPropose hSend hBw hF3p hApX hLocksW hBVH hViableAgree
    (fun vp sp vw sw h₁ h₂ => ⟨fun Y hXY hRY _ D hD => (hCount vp sp vw sw h₁ h₂).1 D
        (ancestorEq_trans hFXp (ancestorEq_trans hXY (ancestorEq_of_parent? hD)))
        (ancestorEq_trans hFroot (ancestorEq_trans hRY (ancestorEq_of_parent? hD))),
      (hCount vp sp vw sw h₁ h₂).2⟩)
    (fun vbt _ _ hvbt _ Y hXY _ hYB D hD hDpar hDB _ => hChild vbt hvbt Y hXY hYB D hD hDpar hDB)

end GoldilocksCorrectness.Proofs.Executions
