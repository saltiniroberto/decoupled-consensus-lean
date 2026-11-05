module
public import GoldilocksCorrectness.Proofs.Executions.RoundKit
public import GoldilocksCorrectness.Proofs.Executions.OrderedFloorVotes
public import GoldilocksCorrectness.Statements.Executions.ProposalViabilityStatements

@[expose] public section

/-!
# The base of the round: the slot invariant restricted to the honest proposal, at its slot

The kit theorem `round_base_steps`, read by the proofs of `lem80wq_round_height_advances_steps`
and of Lemma 80 (`GoldilocksCorrectness/Proofs/Executions/Lemma80.lean`). Write `s` for the first
slot of the round, `B` for the honest proposal `p` put on the wire at the start `t_s` of slot `s`,
`v_s` for the vote time of slot `s` and `a` for the support cutoff of slot `s + 1`. The frames are
read at three points: `p`'s before `t_s`, each member's before `v_s` and before `a`. The proof, in
order:

1. `p` holds `B` after its tick at `t_s` (Lemma 22a), so every member `u` of `Hon` holds `B` before
   `v_s` (Lemma 22);
2. every member's Goldfish vote of slot `s` is its vote for `B` (Lemma 59 with the proposer's
   `head_height_floor` at most the member's, with Lemma 14 for the vote's validator and slot);
3. every member's update of slot `s + 1` at `a` makes `B` fast (Lemma 60) and answers what the
   state after the tick holds (`update_state_of_duty`);
4. every lock entry a member's revocation of slot `s + 1` leaves is compatible with `B` (Lemma 42,
   with the member's own update making `B` fast; its finalized block before the vote time of slot
   `s + 1` is an ancestor of its finalized block before `a`);
5. every member's update saves `B` as the confirmation of slot `s` (Lemma 27).

Steps 2, 4 and 5 are the three clauses of `HonestChainExtends S Sched x Hon B s`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff viewFreeze
  dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_mono dutyWindowStart_succ_le_slotStart
  one_le_Δ slotStart_eq supportCutoff_eq viewFreeze_eq voteTime_eq)

open GoldilocksCorrectness.Statements.Routines (chainStateOf)

open GoldilocksCorrectness.Proofs.Routines (mem_fg_to_ac_tree)

open GoldilocksCorrectness.Proofs.Routines (mem_viable_tree_iff)

open GoldilocksCorrectness.Proofs.Routines (fc_root_eq)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (expireLocks CountedVotes FrameShape)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  ancestorEq_of_parent? compatible_of_ancestorEq_compatible fc_root_ancestorEq_get_anchor)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **Kit theorem, the base of the round, with the frames read at three points.** Write `s` for
the first slot of the round (`1 ≤ s`), `a` for the support cutoff of slot `s + 1`. In an execution
with the eight execution assumptions: if `GST` is at most the vote time of slot `s − 1`; the members
of `Hon` are awake and honest from the duty window's start of slot `s` to `a`; `p` is awake and
honest from the vote time of slot `s − 1` to the start of slot `s` and put `B` on the wire at its
tick then; the slot `s − 1` is as Lemma 59 reads it; every member of `Hs` is a member of `Hon` and
of the slot-`s` committee that put a slot-`s` vote on the wire; at every member the slot-`s` voters
of its pool before `a` are fewer than twice `Hs`; the slot-`s` committee is at most twice `Hs`;
`p`'s frame before the start of slot `s` has the root `ρp` and the `head_height_floor` `φ`; each
member `w`'s frame before the vote time of slot `s` has the root `ρw w`, on `B`'s parent's chain,
and the `head_height_floor` `φw w`, at least `φ` and at most the height of `B`'s parent; each
member `v`'s frame before `a` has the root `ρv v`, `B` or an ancestor of `B`; and some block of
`p`'s tree on `X`'s and `ρp`'s chains reaches `φ` — then every member holds `B` before the vote
time of slot `s`, `HonestChainExtends S Sched x Hon B s` holds, and every member's update of slot
`s + 1` at `a` answers an `A'` that saves `B` as the confirmation of slot `s` and has `B` among its
fast blocks.

Why: the steps of the module header.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the network
  is synchronous; `s`: the first slot of the round;
- `Hon`: the members; `Hs`: the honest voters of slot `s`; `Hprev`: those of slot `s − 1`, with `H`
  the block each one's vote is for; `X`: the block they extend; `B`: the proposal; `p`: its
  proposer;
- `φ`, `ρp`: the `head_height_floor` and the root of `p`'s frame before the start of slot `s`;
  `φw w`, `ρw w`: those of member `w`'s frame before the vote time of slot `s`; `φv v`, `ρv v`:
  those of member `v`'s frame before `a`.

Read aloud: in the round's first slot every member votes for the honest proposal, confirms it,
makes it fast and keeps no lock off its chain.

Roots name blocks until `supportCutoff S (s + 1)`: Lemma 42, which the proof calls at slot `s`
for each member's revocation of slot `s + 1`, takes blocks as held up to the support cutoff of
slot `s + 1`; Lemmas 22, 27, 59 and 60 read earlier. -/
theorem round_base_steps (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (GST s : ℕ) (Hon Hs Hprev : Finset V) (H : V → Block V) (X B : Block V) (p : V) (φ : Height)
    (φw φv : V → Height) (ρp : Block V) (ρw ρv : V → Block V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s + 1)))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    (hs1 : 1 ≤ s)
    (hGST : GST ≤ voteTime S (s - 1))
    (hHon : ∀ v ∈ Hon, ∀ t : ℕ, dutyWindowStart S s ≤ t → t ≤ supportCutoff S (s + 1) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    (hp : ∀ t : ℕ, voteTime S (s - 1) ≤ t → t ≤ slotStart S s →
      p ∈ Sched.awake (t : Int) ∧ p ∉ Sched.adv (t : Int))
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    (hHsPrev : ∀ u ∈ Hprev, u ∈ S.P.committee (s - 1) ∧
      u ∉ Sched.adv (voteTime S s : Int) ∧
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (s - 1)) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u (s - 1) (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      H u ∈ (stateBefore x (voteTime S (s - 1)) u).S.T ∧ X.AncestorEq (H u))
    (hVotersPrev : ∀ w ∈ Hon, ∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes S.C (stateBefore x (voteTime S s) w).A
        (fg_to_ac (stateBefore x (voteTime S s) w).S) s votes support_votes →
      voters_count votes < 2 * Hprev.card)
    (hApX : (get_anchor (stateBefore x (slotStart S s) p).A
      (fg_to_ac (stateBefore x (slotStart S s) p).S) ((slotStart S s : ℕ) : Int)).AncestorEq X)
    (hLocksW : ∀ w ∈ Hon, ∀ A' : ACState V,
      revoke_locks S.P (expireLocks (stateBefore x (voteTime S s) w).A
        ((voteTime S s : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S s) w).S)
        ((voteTime S s : ℕ) : Int) s = .ok A' →
      ∀ e ∈ A'.lock_entries,
        is_live (fg_to_ac (stateBefore x (voteTime S s) w).S) ((voteTime S s : ℕ) : Int) e =
          true → e.B.AncestorEq B.parent)
    (hOnly : ∀ w ∈ Hon, ∀ B₁ ∈ (stateBefore x (voteTime S s) w).S.T, B₁.slot = s → B₁ = B)
    (hRootNew : ∀ B₁ ∈ (stateBefore x (slotStart S s) p).S.T, B₁.root ≠ B.root)
    (hHs : ∀ u ∈ Hs, u ∈ Hon ∧ u ∈ S.P.committee s ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s ∧
        ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s) ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x[i + 1].sent - x[i].sent)
    (hVoters : ∀ v ∈ Hon,
      voters_count ((stateBefore x (supportCutoff S (s + 1)) v).A.pool s) < 2 * Hs.card)
    (hHalf : (S.P.committee s).card ≤ 2 * Hs.card)
    (hShapeP : FrameShape (stateBefore x (slotStart S s) p).S ρp φ)
    (hShapeW : ∀ w ∈ Hon, FrameShape (stateBefore x (voteTime S s) w).S (ρw w) (φw w))
    (hShapeV : ∀ v ∈ Hon, FrameShape (stateBefore x (supportCutoff S (s + 1)) v).S (ρv v) (φv v))
    (hFloorW : ∀ w ∈ Hon, φ ≤ φw w ∧ φw w ≤ (chainStateOf S.C B.parent).h)
    (hRootW : ∀ w ∈ Hon, (ρw w).AncestorEq B.parent)
    (hRootAr : ∀ v ∈ Hon, (ρv v).AncestorEq B)
    (hHeadP : ∃ W ∈ (stateBefore x (slotStart S s) p).S.T,
      X.AncestorEq W ∧ ρp.AncestorEq W ∧ φ ≤ (chainStateOf S.C W).h) :
    (∀ u ∈ Hon, B ∈ (stateBefore x (voteTime S s) u).S.T) ∧
    HonestChainExtends S Sched x Hon B s ∧
    ∀ v ∈ Hon, ∃ A' : ACState V,
      update_confirmation S.C S.P
        (expireLocks (stateBefore x (supportCutoff S (s + 1)) v).A
          ((supportCutoff S (s + 1) : ℕ) : Int))
        (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S)
        ((supportCutoff S (s + 1) : ℕ) : Int) (s + 1) = .ok A' ∧
      A'.saved_confirmation s = some B ∧ B ∈ A'.fast_blocks := by
  obtain ⟨s₀, rfl⟩ : ∃ s₀, s = s₀ + 1 := ⟨s - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hGST hHsPrev hp
  -- the times
  have hΔ := one_le_Δ S
  have hss₀ : slotStart S (s₀ + 1) = slotStart S s₀ + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hss₁ : slotStart S (s₀ + 1 + 1) = slotStart S (s₀ + 1) + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq S (s₀ + 1), Nat.mul_add, Nat.mul_one]
  have hv₀ : voteTime S s₀ = slotStart S s₀ + Δ S := voteTime_eq S s₀
  have hv₁ : voteTime S (s₀ + 1) = slotStart S (s₀ + 1) + Δ S := voteTime_eq S (s₀ + 1)
  have hv₂ : voteTime S (s₀ + 1 + 1) = slotStart S (s₀ + 1 + 1) + Δ S :=
    voteTime_eq S (s₀ + 1 + 1)
  have hc₁ : supportCutoff S (s₀ + 1) = voteTime S (s₀ + 1) + Δ S := supportCutoff_eq S (s₀ + 1)
  have hc₂ : supportCutoff S (s₀ + 1 + 1) = voteTime S (s₀ + 1 + 1) + Δ S :=
    supportCutoff_eq S (s₀ + 1 + 1)
  have hf₁ : viewFreeze S (s₀ + 1) = slotStart S (s₀ + 1) + 3 * Δ S := viewFreeze_eq S (s₀ + 1)
  have hdw₀ : dutyWindowStart S (s₀ + 1) ≤ slotStart S s₀ := dutyWindowStart_succ_le_slotStart S s₀
  have hdw₁ : dutyWindowStart S (s₀ + 1) ≤ dutyWindowStart S (s₀ + 1 + 1) :=
    dutyWindowStart_mono S (by omega)
  have hdw₂ : dutyWindowStart S (s₀ + 1 + 1) ≤ slotStart S (s₀ + 1) :=
    dutyWindowStart_succ_le_slotStart S (s₀ + 1)
  have hwin : ∀ v ∈ Hon, ∀ t : ℕ, voteTime S s₀ ≤ t → t ≤ supportCutoff S (s₀ + 1 + 1) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int) :=
    fun v hv t h1 h2 => hHon v hv t (by omega) h2
  have hwin₂ : ∀ v ∈ Hon, ∀ t : ℕ, dutyWindowStart S (s₀ + 1 + 1) ≤ t →
      t ≤ supportCutoff S (s₀ + 1 + 1) → v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int) :=
    fun v hv t h1 h2 => hHon v hv t (by omega) h2
  -- step 1: `p` holds `B` after its tick, and every member holds `B` before `v_s`
  obtain ⟨i, hl, hsent⟩ := id hPropose
  obtain ⟨-, hBne, hBpar?, hEnd⟩ := proposal_parent_walk_end S Sched x s₀ i B p hl hsent
  have hPB : B.parent.AncestorEq B := ancestorEq_of_parent? hBpar?
  have hParentHeld : B.parent ∈ (stateBefore x (slotStart S (s₀ + 1)) p).S.T := by
    rcases hEnd with hin | heq
    · exact ((mem_fg_to_ac_tree _ _).1 ((mem_viable_tree_iff _ _ _).1 hin).1).1
    · obtain ⟨W, hW, hXW, -, -⟩ := hHeadP
      refine ancestors_mem_T_of_exec S Sched x _ p W B.parent hW ?_
      rw [heq]
      exact ancestorEq_trans hApX hXW
  have hFpB : (stateBefore x (slotStart S (s₀ + 1)) p).S.F.AncestorEq B := by
    refine ancestorEq_trans ?_ hPB
    rcases hEnd with hin | heq
    · exact ((mem_fg_to_ac_tree _ _).1 ((mem_viable_tree_iff _ _ _).1 hin).1).2
    · rw [heq]
      exact ancestorEq_trans (F_ancestorEq_fc_root_of_stateBefore S Sched x _ p)
        (by rw [← fc_root_eq]
            exact fc_root_ancestorEq_get_anchor (stateBefore x (slotStart S (s₀ + 1)) p).A
              (fg_to_ac (stateBefore x (slotStart S (s₀ + 1)) p).S) _)
  have hBp : B ∈ (x[i + 1][p].st).S.T :=
    lem22a_proposer_holds_own_proposal S Sched x s₀ i B p hDiv hMono hl hsent hRootNew hParentHeld
      ((compatible_iff _ _).2 (Or.inl hFpB))
  have hpt₁ : p ∉ Sched.adv (slotStart S (s₀ + 1) : Int) :=
    (hp (slotStart S (s₀ + 1)) (by omega) le_rfl).2
  have hHeld : ∀ u ∈ Hon, B ∈ (stateBefore x (voteTime S (s₀ + 1)) u).S.T := by
    intro u hu
    have hShapeU := hShapeW u hu
    have hFu : (stateBefore x (voteTime S (s₀ + 1)) u).S.F.AncestorEq B := by
      refine ancestorEq_trans ?_ (ancestorEq_trans (hRootW u hu) hPB)
      rw [← hShapeU.1]
      exact F_ancestorEq_fc_root_of_stateBefore S Sched x _ u
    exact lem22_proposal_held_by_voter S Sched x GST s₀ i B p u hDiv hMono hSync hCatch
      (hRoots.mono (by omega)) hParent hGST hpt₁ (fun t h1 h2 => hwin u hu t (by omega) (by omega)) hl hsent hBp
      ((compatible_iff _ _).2 (Or.inl hFu))
  -- step 2: every member's slot-`s` vote is its vote for `B` (Lemma 59 with ordered
  -- `head_height_floor` values)
  have hVote : ∀ u ∈ Hon, ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (s₀ + 1)) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x[i + 1].sent - x[i].sent) →
      vote = GoldfishVote.mk u (s₀ + 1) B.root := by
    intro u hu vote hSend
    have hhead := lem59le_goldfish_vote_names_honest_proposal_frame S Sched x GST s₀ Hprev H X B
      p u vote ρp (ρw u) φ (φw u) hDiv hMono hSync hCatch (hRoots.mono (by omega)) hParent
      hOwner hGST
      hHsPrev (hVotersPrev u hu) hp (fun t h1 h2 => hwin u hu t h1 (by omega)) hPropose hSend
      (hOnly u hu) hRootNew hShapeP (hShapeW u hu) (hFloorW u hu).1 hHeadP hApX
      (ancestorEq_trans (hRootW u hu) hPB)
      (fun A' hA' e he hlive => ancestorEq_trans (hLocksW u hu A' hA' e he hlive) hPB)
      (hFloorW u hu).2
    obtain ⟨hvi, hvs⟩ := honest_vote_form S Sched x (s₀ + 1) u vote hSend
    cases vote with
    | mk vi vs vh =>
        simp only at hvi hvs hhead
        rw [hvi, hvs, hhead]
  -- the honest voters of slot `s` as Lemmas 60 and 27 read them
  have hHs' : ∀ u ∈ Hs, u ∈ S.P.committee (s₀ + 1) ∧
      u ∉ Sched.adv (supportCutoff S (s₀ + 1 + 1) : Int) ∧
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (s₀ + 1)) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u (s₀ + 1) B.root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      B ∈ (stateBefore x (voteTime S (s₀ + 1)) u).S.T := by
    intro u hu
    obtain ⟨huH, hcomm, vote, -, -, i', hl', hs'⟩ := hHs u hu
    have hv := hVote u huH vote ⟨i', hl', hs'⟩
    rw [hv] at hs'
    exact ⟨hcomm, (hwin u huH _ (by omega) le_rfl).2, ⟨i', hl', hs'⟩, hHeld u huH⟩
  have hGST₁ : GST ≤ voteTime S (s₀ + 1) := by omega
  -- the finalized block of a member before `a` is `B` or an ancestor of `B`
  have hFa : ∀ v ∈ Hon, (stateBefore x (supportCutoff S (s₀ + 1 + 1)) v).S.F.AncestorEq B := by
    intro v hv
    refine ancestorEq_trans ?_ (hRootAr v hv)
    rw [← (hShapeV v hv).1]
    exact F_ancestorEq_fc_root_of_stateBefore S Sched x _ v
  -- step 3: every member's update makes `B` fast, and the state after the tick holds its answer
  have hUpd : ∀ v ∈ Hon, ∃ A' : ACState V,
      update_confirmation S.C S.P
        (expireLocks (stateBefore x (supportCutoff S (s₀ + 1 + 1)) v).A
          ((supportCutoff S (s₀ + 1 + 1) : ℕ) : Int))
        (fg_to_ac (stateBefore x (supportCutoff S (s₀ + 1 + 1)) v).S)
        ((supportCutoff S (s₀ + 1 + 1) : ℕ) : Int) (s₀ + 1 + 1) = .ok A' ∧
      (stateBefore x (supportCutoff S (s₀ + 1 + 1) + 1) v).A.saved_confirmation =
        A'.saved_confirmation ∧ B ∈ A'.fast_blocks := by
    intro v hv
    have hfast := (lem60_update_confirmation_fast_locks_frame S Sched x GST (s₀ + 1) Hs B v hDiv
      hMono hSync hCatch (hRoots.mono (by omega)) hParent hOwner hGST₁ hHs' (hVoters v hv)
      hHalf hBne
      (hwin₂ v hv) (by rw [(hShapeV v hv).1]; exact hRootAr v hv)).1
    have hva := hwin₂ v hv (supportCutoff S (s₀ + 1 + 1)) (by omega) le_rfl
    have hAw := awakeSince_le_dutyWindowStart_b S Sched x (s₀ + 1 + 1)
      (supportCutoff S (s₀ + 1 + 1)) v hDiv hMono (by omega)
      (fun t h1 h2 => (hwin₂ v hv t h1 h2).1) hva.2
    obtain ⟨A'', hA'', hsave, hfb, -, -⟩ :=
      update_state_of_duty S Sched x (s₀ + 1) v hDiv hva hAw
    exact ⟨A'', hA'', hsave, by rw [← hfb]; exact hfast⟩
  -- step 4: every lock entry a member's revocation of slot `s + 1` leaves is compatible with
  -- `B`, by Lemma 42 with the member's own update making `B` fast
  have hLocks : ∀ w ∈ Hon, ∀ A'' : ACState V,
      revoke_locks S.P (expireLocks (stateBefore x (voteTime S (s₀ + 1 + 1)) w).A
        ((voteTime S (s₀ + 1 + 1) : ℕ) : Int))
        (fg_to_ac (stateBefore x (voteTime S (s₀ + 1 + 1)) w).S)
        ((voteTime S (s₀ + 1 + 1) : ℕ) : Int) (s₀ + 1 + 1) = .ok A'' →
      ∀ e ∈ A''.lock_entries, e.B.compatible B = true := by
    intro w hw
    obtain ⟨Aw, hAw, -, hAwf⟩ := hUpd w hw
    have hFw : (stateBefore x (voteTime S (s₀ + 1 + 1)) w).S.F.compatible B = true := by
      refine (compatible_iff _ _).2 (Or.inl (ancestorEq_trans ?_ (hFa w hw)))
      exact (stateBefore_grows x hDiv w (by omega)).2.1
    exact lem42_fast_lock_clears_conflicting_locks S Sched x GST (s₀ + 1) B w w Aw hDiv hMono
      hSync hCatch hRoots hParent (by omega) (fun t h1 h2 => hwin w hw t (by omega) h2)
      (fun t h1 h2 => hwin w hw t (by omega) (by omega)) hAw hAwf hFw
  -- step 5: every member's update saves `B` as the confirmation of slot `s`
  have hSaved : ∀ v ∈ Hon,
      (stateBefore x (supportCutoff S (s₀ + 1 + 1) + 1) v).A.saved_confirmation (s₀ + 1) =
        some B := by
    intro v hv
    exact (lem27_update_confirmation_confirms_voter_majority_block S Sched x GST (s₀ + 1) Hs B v
      hDiv hMono hSync hCatch (hRoots.mono (by omega)) hParent hOwner hGST₁ hHs'
      (hVoters v hv) hBne
      (hwin₂ v hv) (hFa v hv) (fun A'' hA'' e he _ => hLocks v hv A'' hA'' e he)).1
  refine ⟨hHeld, ⟨fun u hu vote hSend => ⟨B, hHeld u hu, hVote u hu vote hSend, ancestorEq_refl B⟩,
    fun w hw A'' hA'' e he _ => hLocks w hw A'' hA'' e he, fun v hv C' hC' => ?_⟩,
    fun v hv => ?_⟩
  · rw [hSaved v hv] at hC'
    cases hC'
    exact ancestorEq_refl B
  · obtain ⟨A'', hA'', hsave, hfb⟩ := hUpd v hv
    refine ⟨A'', hA'', ?_, hfb⟩
    rw [← hsave]
    exact hSaved v hv

end GoldilocksCorrectness.Proofs.Executions
