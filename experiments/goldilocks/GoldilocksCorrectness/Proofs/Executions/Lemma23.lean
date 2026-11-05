module
public import GoldilocksCorrectness.Proofs.Executions.CountAgreement
public import GoldilocksCorrectness.Statements.Routines.ProposalStatements

@[expose] public section

/-!
# Lemma 23: an honest proposer and the next slot's honest voter count alike

The proof of `lem23_proposer_and_voter_count_alike`, stated in
`GoldilocksCorrectness/Statements/Executions/CountAgreementStatements.lean`.

Write `t₁ := slotStart S (s + 1)`, the time of `p`'s proposal, `t₃ := voteTime S (s + 1)`, the time of
`w`'s vote, and `freeze := viewFreeze S s`, so that `freeze + Δ = t₁`; `A_p`, `Φ_p` for the AC state
and the frame of `p`'s node state before `t₁`, `A_w`, `Φ_w` for those of `w`'s node state before
`t₃`. The proof is the measurement's five steps:

1. `p`'s run: Lemma 19 gives `B.votes` as `A_p`'s list of slot `s` and `B.support_votes` as its
   votes that resolve; with `hOnly`, the votes `w` counts as included are `A_p.pool s`, and the
   support votes `w` counts as included are `p`'s support votes;
2. a vote `w` holds stamped before `freeze` reached `p` before `t₁`, or `p` holds two votes of its
   validator (`pool_vote_reaches_proposer`);
3. so the equivocators agree, the participants agree, and the vote in `w`'s counted set of a
   validator that does not equivocate is in `p`'s;
4. the support votes of such a validator agree, for a head block that has the other's finalized
   block as an ancestor: a head block `p` resolves reaches `w`, a head block `w` resolved before
   `freeze` reaches `p`, and roots name one block across the two honest trees;
5. the supporters of every block that has both finalized blocks as ancestors agree (a supporter's
   head block is a descendant of that block), and so the scores (`goldfish_score_eq_ok`) and the
   voter counts.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime viewFreeze)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slotStart_eq slot_eq_of_mem viewFreeze_cast
  viewFreeze_eq voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (mem_fg_to_ac_tree)

open GoldilocksCorrectness.Proofs.Routines (mem_pool_iff)

open GoldilocksCorrectness.Proofs.Routines (mem_included_support_votes_iff mem_included_votes_iff)

open GoldilocksCorrectness.Proofs.Routines (voters_count_eq)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction AtomicHonest Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (CountedVotes ProposalCountedVotes
  RootsNameBlocksIn)
open GoldilocksCorrectness.Proofs.Routines (compatible_iff mem_supportersOf_iff
  mem_participants_iff goldfish_score_eq_ok equivocators_subset_participants resolved_eq_ok_true
  tau_eq_ok_some tau_head_of_eq_some mem_equivocators_iff_two tau_eq_some_blockStamp
  supportersOf ancestorEq_trans)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **Lemma 23, an honest proposer and the next slot's honest voter count alike.** The proof; the
audited statement is in `Statements/Executions/CountAgreementStatements.lean`.

The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution; `GST`: the time from which the
  network is synchronous; `s`: the slot of the votes;
- `B`: the proposal of slot `s + 1`; `p`: its proposer; `w`: the voter of slot `s + 1`;
- `votes_p`, `support_p`: the sets `p`'s proposal counts; `votes_w`, `support_w`: the sets `w`'s
  vote counts.

Roots name blocks until `voteTime S (s + 1)`: the proof compares the blocks `w` holds before the
vote time of slot `s + 1` with those `p` holds before the start of slot `s + 1`, and takes
blocks as held by `w` one delay after the start of slot `s + 1` (`mem_T_before_add_delay`). -/
theorem lem23_proposer_and_voter_count_alike (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s : ℕ) (B : Block V) (p w : V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (voteTime S (s + 1)))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hGST : GST ≤ voteTime S s)
    (hp : ∀ t : ℕ, viewFreeze S s ≤ t → t ≤ slotStart S (s + 1) →
      p ∈ Sched.awake (t : Int) ∧ p ∉ Sched.adv (t : Int))
    (hw : ∀ t : ℕ, slotStart S (s + 1) ≤ t → t ≤ voteTime S (s + 1) →
      w ∈ Sched.awake (t : Int) ∧ w ∉ Sched.adv (t : Int))
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    (hBw : B ∈ (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).tree)
    (hOnly : ∀ B' ∈ (stateBefore x (voteTime S (s + 1)) w).S.T, B'.slot = s + 1 → B' = B) :
    ∀ votes_p support_p votes_w support_w : Finset (GoldfishVote V),
      ProposalCountedVotes (stateBefore x (slotStart S (s + 1)) p).A
        (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S) s votes_p support_p →
      CountedVotes S.C (stateBefore x (voteTime S (s + 1)) w).A
        (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) (s + 1) votes_w support_w →
      (∀ D : Block V, (stateBefore x (slotStart S (s + 1)) p).S.F.AncestorEq D →
        (stateBefore x (voteTime S (s + 1)) w).S.F.AncestorEq D → ∃ n : ℕ,
          goldfish_score (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S) votes_p support_p s
            D = .ok n ∧
          goldfish_score (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) votes_w support_w s
            D = .ok n) ∧
      voters_count votes_p = voters_count votes_w := by
  intro votes_p support_p votes_w support_w hPCV hCV
  obtain ⟨hVp, hSupP⟩ := hPCV
  obtain ⟨hCv, hCs⟩ := hCV
  simp only [Nat.add_sub_cancel] at hCv hCs
  -- step 0: the times
  have hΔ := one_le_Δ S
  have hss : slotStart S (s + 1) = slotStart S s + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hss' : slotStart S (s + 1 + 1) = slotStart S (s + 1) + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq S (s + 1), Nat.mul_add, Nat.mul_one]
  have hv₃ : voteTime S (s + 1) = slotStart S (s + 1) + Δ S := voteTime_eq S (s + 1)
  have hv₁ : voteTime S s = slotStart S s + Δ S := voteTime_eq S s
  have hfz : viewFreeze S s = slotStart S s + 3 * Δ S := viewFreeze_eq S s
  have hfzΔ : viewFreeze S s + Δ S = slotStart S (s + 1) := by omega
  have hfzc : ((S.C.t_ s + 3 * S.C.Δ : Time) : Stamp) =
      (((viewFreeze S s : ℕ) : Int) : Stamp) := by
    rw [viewFreeze_cast]
  have hslot₁ : S.C.slot ((slotStart S (s + 1) : ℕ) : Int) = s + 1 :=
    slot_eq_of_mem S (le_refl _) (by omega)
  -- step 1: `p`'s run and proposal
  obtain ⟨i₁, hl₁, hm₁⟩ := hPropose
  have hi₁ : stepBefore x (slotStart S (s + 1)) = i₁ := stepBefore_eq_of_lbl x hl₁
  have hti₁ : x[i₁].time + 1 = slotStart S (s + 1) := (time_of_lbl_tickAllAwake x hl₁).1
  obtain ⟨-, n₁', sent₁, hrun₁, hB₁⟩ := tick_send_of_honestSendAt hl₁ hm₁
  have hAp : (tickInputState x i₁ (slotStart S (s + 1)) p).A =
      (stateBefore x (slotStart S (s + 1)) p).A := by
    rw [(tickInputState_frame x i₁ _ p).2.1]
    unfold stateBefore
    rw [hi₁]
  have hSp : (tickInputState x i₁ (slotStart S (s + 1)) p).S =
      (stateBefore x (slotStart S (s + 1)) p).S := by
    rw [(tickInputState_frame x i₁ _ p).1]
    unfold stateBefore
    rw [hi₁]
  obtain ⟨-, -, -, Hp, votes_pl, support_pl, hvl, hsl, -, hBdef⟩ :=
    GoldilocksCorrectness.Statements.Routines.lem19_tick_proposes S.C S.P S.X _ n₁' _ sent₁ B
      hrun₁ hB₁
  rw [hslot₁, Nat.add_sub_cancel, hAp] at hvl
  rw [hAp, hSp] at hsl
  rw [hslot₁] at hBdef
  have hBvotes : B.votes = votes_pl := by rw [hBdef]; rfl
  have hBsupp : B.support_votes = support_pl := by rw [hBdef]; rfl
  have hBslot : B.slot = s + 1 := by rw [hBdef]; rfl
  -- the two validators are honest at the steps their states are read at
  have hph : AtomicHonest x (stepBefore x (slotStart S (s + 1))) p := by
    rw [hi₁]
    exact fun h => (hp (slotStart S (s + 1)) (by omega) le_rfl).2
      (hMono _ _ (by omega) h)
  obtain ⟨-, hti₃, -⟩ := stepBefore_spec x hDiv (by omega : 1 ≤ voteTime S (s + 1))
  have hwh : AtomicHonest x (stepBefore x (voteTime S (s + 1))) w := fun h =>
    (hw (voteTime S (s + 1)) (by omega) le_rfl).2 (hMono _ _ (by omega) h)
  have hRp : RootsNameBlocksIn (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).tree :=
    rootsNameBlocksIn_frame_of_exec_node S Sched x _ p
  have hRw : RootsNameBlocksIn (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).tree :=
    rootsNameBlocksIn_frame_of_exec_node S Sched x _ w
  -- `B`'s votes are `p`'s pool of slot `s`, its support votes those that resolve at `p`
  have hpoolB : ∀ vote : GoldfishVote V,
      vote ∈ (stateBefore x (slotStart S (s + 1)) p).A.pool s ↔ vote ∈ B.votes := by
    intro vote
    rw [hBvotes, hvl]
    exact mem_pool_iff _ _ _
  have hsupB : ∀ vote : GoldfishVote V, vote ∈ B.support_votes ↔
      vote ∈ (stateBefore x (slotStart S (s + 1)) p).A.pool s ∧
        ∃ y : Stamp, (stateBefore x (slotStart S (s + 1)) p).A.tau
          (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S) vote = .ok (some y) := by
    intro vote
    rw [hBsupp, hsl vote, ← hBvotes, ← hpoolB vote]
  have hsupP' : ∀ vote : GoldfishVote V, vote ∈ support_p ↔ vote ∈ B.support_votes :=
    fun vote => (hSupP vote).trans (hsupB vote).symm
  have hslotp : ∀ vote ∈ (stateBefore x (slotStart S (s + 1)) p).A.pool s, vote.slot = s :=
    pool_slot_of_stateBefore S Sched x _ p s
  -- the votes and support votes `w` counts as included are `p`'s
  have hIncl : ∀ vote : GoldfishVote V, vote ∈ included_votes
      (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) (s + 1) ↔
        vote ∈ (stateBefore x (slotStart S (s + 1)) p).A.pool s := by
    intro vote
    simp only [mem_included_votes_iff,
      Nat.add_sub_cancel]
    constructor
    · rintro ⟨B', ⟨hB', hBs⟩, hvB, -⟩
      rw [hOnly B' ((mem_fg_to_ac_tree _ _).1 hB').1 hBs] at hvB
      exact (hpoolB vote).2 hvB
    · intro hv
      exact ⟨B, ⟨hBw, hBslot⟩, (hpoolB vote).1 hv, hslotp vote hv⟩
  have hInclS : ∀ vote : GoldfishVote V, vote ∈ included_support_votes
      (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) (s + 1) ↔ vote ∈ support_p := by
    intro vote
    simp only [mem_included_support_votes_iff,
      Nat.add_sub_cancel]
    rw [hsupP' vote]
    constructor
    · rintro ⟨B', ⟨hB', hBs⟩, hvB, -⟩
      rw [hOnly B' ((mem_fg_to_ac_tree _ _).1 hB').1 hBs] at hvB
      exact hvB
    · intro hv
      exact ⟨B, ⟨hBw, hBslot⟩, hv, hslotp vote ((hsupB vote).1 hv).1⟩
  -- `p`'s counted votes are among `w`'s
  have hPW : ∀ vote ∈ votes_p, vote ∈ votes_w := by
    intro vote hv
    rw [hVp] at hv
    exact (hCv vote).2 (Or.inr ((hIncl vote).2 hv))
  -- step 2: a vote `w` counts is `p`'s, or its validator equivocates at `p`
  have hW2 : ∀ vote ∈ votes_w, vote ∈ votes_p ∨ vote.val_index ∈ equivocators votes_p := by
    intro vote hv
    rw [hVp]
    rcases (hCv vote).1 hv with ⟨hpw, τ, hτ, hτlt⟩ | hinc
    · rw [hfzc] at hτlt
      have hfr : vote ∈ (stateBefore x (viewFreeze S s) w).A.pool s :=
        (voteStamp_lt_iff hDiv hpw).1 ⟨τ, hτ, hτlt⟩
      rcases pool_vote_reaches_proposer S Sched x hDiv hMono GST hSync hCatch s p w vote
          hGST hp hfr with h | ⟨v₁, h₁, v₂, h₂, hne, hi₁', hi₂'⟩
      · exact Or.inl h
      · exact Or.inr ((mem_equivocators_iff_two _ _).2 ⟨v₁, h₁, v₂, h₂, hne, hi₁', hi₂'⟩)
    · exact Or.inl ((hIncl vote).1 hinc)
  -- step 3: the equivocators and the participants agree
  have hEq : equivocators votes_p = equivocators votes_w := by
    ext u
    rw [mem_equivocators_iff_two, mem_equivocators_iff_two]
    constructor
    · rintro ⟨v₁, h₁, v₂, h₂, hne, hi₁', hi₂'⟩
      exact ⟨v₁, hPW v₁ h₁, v₂, hPW v₂ h₂, hne, hi₁', hi₂'⟩
    · rintro ⟨v₁, h₁, v₂, h₂, hne, hi₁', hi₂'⟩
      rcases hW2 v₁ h₁ with h₁' | he
      · rcases hW2 v₂ h₂ with h₂' | he
        · exact ⟨v₁, h₁', v₂, h₂', hne, hi₁', hi₂'⟩
        · rw [hi₂'] at he
          exact (mem_equivocators_iff_two _ _).1 he
      · rw [hi₁'] at he
        exact (mem_equivocators_iff_two _ _).1 he
  have hPart : participants votes_p = participants votes_w := by
    ext u
    rw [mem_participants_iff, mem_participants_iff]
    constructor
    · rintro ⟨vote, hv, hi⟩
      exact ⟨vote, hPW vote hv, hi⟩
    · rintro ⟨vote, hv, hi⟩
      rcases hW2 vote hv with h | he
      · exact ⟨vote, h, hi⟩
      · rw [hi] at he
        exact (mem_participants_iff _ _).1 (equivocators_subset_participants _ he)
  have hNonEq : ∀ vote ∈ votes_w, vote.val_index ∉ equivocators votes_w → vote ∈ votes_p := by
    intro vote hv hne
    refine (hW2 vote hv).resolve_right ?_
    rw [hEq]
    exact hne
  have hSW : ∀ vote ∈ support_w, vote ∈ votes_w := by
    intro vote hv
    rcases (hCs vote).1 hv with ⟨hpw, hτ, -⟩ | ⟨hinc, -⟩
    · exact (hCv vote).2 (Or.inl ⟨hpw, hτ⟩)
    · refine hPW vote ?_
      rw [hVp]
      exact ((hSupP vote).1 ((hInclS vote).1 hinc)).1
  -- step 4: the head blocks propagate, `p` to `w` by `t₃` and `w` to `p` by `t₁`, when the other's
  -- finalized block is an ancestor of them
  have hToW : ∀ vote ∈ (stateBefore x (slotStart S (s + 1)) p).A.pool s,
      ∀ H ∈ (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).tree, H.root = vote.head →
        (stateBefore x (voteTime S (s + 1)) w).S.F.AncestorEq H →
        H ∈ (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).tree := by
    intro vote hv H hH hr hFH
    have hHT : H ∈ (stateBefore x (slotStart S (s + 1)) p).S.T := ((mem_fg_to_ac_tree _ _).1 hH).1
    have h := mem_T_before_add_delay hDiv hMono hSync hCatch (hRoots.mono (by omega))
      hParent (t := slotStart S (s + 1)) (u := p) (w := w) (by omega) (by omega)
      (hp _ (by omega) le_rfl).2 hHT (fun t' h1 h2 => hw t' h1 (by omega))
      (by rw [← hv₃]; exact (compatible_iff _ _).2 (Or.inl hFH))
    rw [← hv₃] at h
    exact (mem_fg_to_ac_tree _ _).2 ⟨h, hFH⟩
  have hToP : ∀ vote ∈ (stateBefore x (viewFreeze S s) w).A.pool s,
      ∀ H ∈ (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).tree, H.root = vote.head →
        H ∈ (stateBefore x (viewFreeze S s) w).S.T →
        (stateBefore x (slotStart S (s + 1)) p).S.F.AncestorEq H →
        H ∈ (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).tree := by
    intro vote hv H hH hr hHf hFH
    -- `w` is honest at the view freeze, being honest at `t₁` and corruption permanent
    have hwfz : w ∉ Sched.adv (viewFreeze S s : Int) := fun h =>
      (hw (slotStart S (s + 1)) le_rfl (by omega)).2 (hMono _ _ (by omega) h)
    have h := mem_T_before_add_delay hDiv hMono hSync hCatch (hRoots.mono (by omega))
      hParent (t := viewFreeze S s) (u := w) (w := p) (by omega) (by omega)
      hwfz hHf (fun t' h1 h2 => hp t' h1 (by omega))
      (by rw [hfzΔ]; exact (compatible_iff _ _).2 (Or.inl hFH))
    rw [hfzΔ] at h
    exact (mem_fg_to_ac_tree _ _).2 ⟨h, hFH⟩
  -- step 4: a support vote of `p` whose head block `H` in `p`'s frame tree has `w`'s finalized
  -- block as an ancestor is one of `w`'s, with `H` in `w`'s frame tree
  have hSupPW : ∀ vote ∈ support_p,
      ∀ H ∈ (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).tree, H.root = vote.head →
        (stateBefore x (voteTime S (s + 1)) w).S.F.AncestorEq H →
        vote ∈ support_w ∧ H ∈ (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).tree := by
    intro vote hv H hH hr hFH
    obtain ⟨hvp, y, hy⟩ := (hSupP vote).1 hv
    obtain ⟨Hp', hHp', hr', hs'⟩ := tau_head_of_eq_some hRp hy
    have hHH : Hp' = H := hRp Hp' hHp' H hH (hr'.trans hr.symm)
    rw [hHH] at hs'
    have hHw := hToW vote hvp H hH hr hFH
    exact ⟨(hCs vote).2 (Or.inr ⟨(hInclS vote).2 hv, resolved_eq_ok_true hRw hHw hr hs'⟩), hHw⟩
  -- step 4: a support vote of `w` of a validator that does not equivocate, whose head block `H` in
  -- `w`'s frame tree has `p`'s finalized block as an ancestor, is one of `p`'s, with `H` in `p`'s
  -- frame tree
  have hSupWP : ∀ vote ∈ support_w, vote.val_index ∉ equivocators votes_w →
      ∀ H ∈ (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).tree, H.root = vote.head →
        (stateBefore x (slotStart S (s + 1)) p).S.F.AncestorEq H →
        vote ∈ support_p ∧ H ∈ (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).tree := by
    intro vote hv hne H hH hr hFH
    rcases (hCs vote).1 hv with ⟨hpw, ⟨τ, hτ, hτlt⟩, y, hy, hylt⟩ | ⟨hinc, -⟩
    · -- the pool clause: the vote and its head block reached `p` before `t₁`
      obtain ⟨Hw, hHw, hrw, hsw⟩ := tau_head_of_eq_some hRw hy
      have hHH : H = Hw := hRw H hH Hw hHw (hr.trans hrw.symm)
      obtain ⟨τH, hτH, hτHy⟩ := tau_eq_some_blockStamp hRw hHw hrw hy
      rw [hfzc] at hτlt hylt
      have hfr : vote ∈ (stateBefore x (viewFreeze S s) w).A.pool s :=
        (voteStamp_lt_iff hDiv hpw).1 ⟨τ, hτ, hτlt⟩
      have hHwT : Hw ∈ (stateBefore x (voteTime S (s + 1)) w).S.T :=
        ((mem_fg_to_ac_tree _ _).1 hHw).1
      have hHf : Hw ∈ (stateBefore x (viewFreeze S s) w).S.T :=
        (blockStamp_lt_iff hDiv hHwT).1 ⟨τH, hτH, lt_of_le_of_lt hτHy hylt⟩
      have hHp : Hw ∈ (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).tree :=
        hToP vote hfr Hw hHw hrw hHf (by rw [← hHH]; exact hFH)
      have hvp : vote ∈ (stateBefore x (slotStart S (s + 1)) p).A.pool s := by
        rw [← hVp]
        exact hNonEq vote (hSW vote hv) hne
      have hInvP := (lem11_node_invariant S Sched x (stepBefore x (slotStart S (s + 1))) p).1
      obtain ⟨τv', hτv'⟩ := Option.ne_none_iff_exists'.1
        (hInvP.2.1 s vote ((mem_pool_iff _ _ _).1 hvp))
      obtain ⟨τH', hτH'⟩ := Option.ne_none_iff_exists'.1
        (hInvP.2.2.2.2.1 Hw ((mem_fg_to_ac_tree _ _).1 hHp).1)
      refine ⟨(hSupP vote).2 ⟨hvp, _, tau_eq_ok_some hRp hHp hrw hsw hτv' hτH'⟩, ?_⟩
      rw [hHH]
      exact hHp
    · -- the included clause: the vote is one of `p`'s support votes
      have hvs : vote ∈ support_p := (hInclS vote).1 hinc
      obtain ⟨-, y, hy⟩ := (hSupP vote).1 hvs
      obtain ⟨Hp', hHp', hr', -⟩ := tau_head_of_eq_some hRp hy
      refine ⟨hvs, ?_⟩
      have hTw := (stepBefore_spec x hDiv (show 1 ≤ voteTime S (s + 1) by omega)).2.1
      have hTp := (stepBefore_spec x hDiv (show 1 ≤ slotStart S (s + 1) by omega)).2.1
      have hHH : H = Hp' := hRoots H Hp'
        ⟨stepBefore x (voteTime S (s + 1)), w, hwh, by omega, ((mem_fg_to_ac_tree _ _).1 hH).1⟩
        ⟨stepBefore x (slotStart S (s + 1)), p, hph, by omega,
          ((mem_fg_to_ac_tree _ _).1 hHp').1⟩
        (hr.trans hr'.symm)
      rw [hHH]
      exact hHp'
  -- step 5: the supporters agree of every block that has both finalized blocks as ancestors: a
  -- supporter's head block `H` is a descendant of that block, so of both finalized blocks
  have hSupEq : ∀ D : Block V, (stateBefore x (slotStart S (s + 1)) p).S.F.AncestorEq D →
      (stateBefore x (voteTime S (s + 1)) w).S.F.AncestorEq D →
      supportersOf (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S) votes_p support_p s D =
        supportersOf (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) votes_w support_w s D := by
    intro D hFpD hFwD
    ext u
    rw [mem_supportersOf_iff, mem_supportersOf_iff]
    constructor
    · rintro ⟨vote, hv, hi, hne, hs', H, hH, hr, hD⟩
      obtain ⟨hvw, hT⟩ := hSupPW vote hv H hH hr (ancestorEq_trans hFwD hD)
      refine ⟨vote, hvw, hi, ?_, hs', H, hT, hr, hD⟩
      rw [← hEq]
      exact hne
    · rintro ⟨vote, hv, hi, hne, hs', H, hH, hr, hD⟩
      obtain ⟨hvp, hT⟩ := hSupWP vote hv (by rw [hi]; exact hne) H hH hr
        (ancestorEq_trans hFpD hD)
      refine ⟨vote, hvp, hi, ?_, hs', H, hT, hr, hD⟩
      rw [hEq]
      exact hne
  -- step 5: the scores and the voter counts
  refine ⟨fun D hFpD hFwD => ⟨_, goldfish_score_eq_ok hRp votes_p support_p s D, ?_⟩, ?_⟩
  · rw [goldfish_score_eq_ok hRw votes_w support_w s D, hEq, hSupEq D hFpD hFwD]
  · rw [voters_count_eq, voters_count_eq, hPart]

end GoldilocksCorrectness.Proofs.Executions
