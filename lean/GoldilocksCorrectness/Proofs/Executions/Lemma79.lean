module
public import GoldilocksCorrectness.Statements.Executions.HonestChainDefs
public import GoldilocksCorrectness.Statements.Executions.LockProvenanceStatements
public import GoldilocksCorrectness.Statements.Executions.NextSlotVoteStatements
public import GoldilocksCorrectness.Statements.Executions.WakeStatements
public import GoldilocksCorrectness.Statements.Routines.LockStatements
public import GoldilocksCorrectness.Proofs.Executions.Lemma43
public import GoldilocksCorrectness.Proofs.Executions.Lemma78
public import GoldilocksCorrectness.Proofs.Routines.Schedule

@[expose] public section

/-!
# Lemma 79: the slot invariant restricted to a block, its step

The proofs of the kit theorem `live_locks_compatible_of_honestChainExtends` and of Lemma 79 in four
theorems (`lem79a_honestChainExtends_votes_step`, `lem79b_honestChainExtends_locks_step`,
`lem79c_honestChainExtends_confirmations_step`, `lem79_honestChainExtends_step`), stated in
`GoldilocksCorrectness/Statements/Executions/HonestChainStatements.lean`.

The kit theorem: a lock entry `e` a member `w` holds before a time `t` after the support cutoff of
slot `s' + 1` and at most the vote time of slot `s' + 2`, alive at `t`, was added by `w`'s update
of a slot `s₁ + 1` with `s₁ ≤ s'` (Lemma 39). When `s₁ = s'`, the update's saved confirmation is
the one clause 3 of the invariant reads (`update_state_of_lock_entry`), `B` or a descendant of it,
and `e`'s block is that confirmation or an ancestor of it. When `s₁ < s'`, the entry is recent
enough (Lemma 41) for `w` to have been awake since that update, so `w`'s tick at the vote time of
slot `s' + 1` ran the revocation (Lemma 13), and an entry with `e`'s deadline, on a descendant of
`e`'s block, survived it; clause 2 of the invariant makes it compatible with `B`.

The step: clause 1 by Lemma 26b, clause 2 by Lemma 38 and the kit theorem, clause 3 by Lemma 78.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_le_supportCutoff dutyWindowStart_mono
  dutyWindowStart_succ_le_slotStart duty_window_start_mono one_le_Δ slotStart_eq slotStart_mono
  slot_eq_of_mem supportCutoff_eq voteTime_cast voteTime_eq voteTime_succ)

open GoldilocksCorrectness.Proofs.Routines (compatible_of_ancestorEq_both)

open GoldilocksCorrectness.Proofs.Routines (is_live_iff)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (CountedVotes expireLocks)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff
  compatible_of_ancestorEq_compatible revoke_locks_entry_mem_tree)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- The live locks of a member are compatible with `B`. The proof; the audited statement is in
`Statements/Executions/HonestChainStatements.lean`. -/
theorem live_locks_compatible_of_honestChainExtends (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (Hon : Finset V) (B : Block V) (s' t : ℕ) (w : V)
    (hDiv : TimeDiverges x.toTrace)
    (hInv : HonestChainExtends S Sched x Hon B s')
    (hw : w ∈ Hon)
    (hHon : ∀ t'' : ℕ, dutyWindowStart S (s' + 2) ≤ t'' → t'' ≤ t →
      w ∈ Sched.awake (t'' : Int) ∧ w ∉ Sched.adv (t'' : Int))
    (ht1 : supportCutoff S (s' + 1) < t)
    (ht2 : t ≤ voteTime S (s' + 2)) :
    ∀ e ∈ (stateBefore x t w).A.lock_entries, ((t : ℕ) : Int) < e.d →
      e.B.compatible B = true := by
  intro e he hlive
  -- the times
  have hΔ := one_le_Δ S
  have hv' : ∀ s : ℕ, voteTime S s = slotStart S s + Δ S := voteTime_eq S
  have hc' : ∀ s : ℕ, supportCutoff S s = voteTime S s + Δ S := supportCutoff_eq S
  have hss : ∀ s : ℕ, slotStart S (s + 1) = slotStart S s + 4 * Δ S := fun s => by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  -- where `e` comes from (Lemma 39)
  obtain ⟨s₁, hd₁, hcut₁, hτ₁, A', hA', e₀, -, -, -, -, ⟨C', hC', hBC⟩, -, htr⟩ :=
    GoldilocksCorrectness.Statements.Executions.lem39_lock_entry_provenance S Sched x t w e hDiv he
  obtain ⟨e₁, -, -, hB₁, hB₁₀⟩ := htr t hcut₁ le_rfl
  have heC : e.B.AncestorEq C' := ancestorEq_trans (ancestorEq_trans hB₁ hB₁₀) hBC
  -- the slot of `e` is at most `s'`
  have hs₁ : s₁ ≤ s' := by
    by_contra h
    have hm := slotStart_mono S (show s' + 2 ≤ s₁ + 1 by omega)
    have h1 := hv' (s' + 2)
    have h2 := hc' (s₁ + 1)
    have h3 := hv' (s₁ + 1)
    omega
  rcases Nat.lt_or_eq_of_le hs₁ with hlt | heq
  · -- `s₁ < s'`: the revocation at the vote time of slot `s' + 1` kept an entry for `e`
    have hk : s' + 1 ≤ s₁ + S.C.k := by
      by_cases hkle : S.C.k ≤ s' + 1
      · have h41 := GoldilocksCorrectness.Statements.Executions.lem41_slot_of_live_entry S
          (s' + 1 - S.C.k) s₁ t e hd₁ hlive (by
            rw [show s' + 1 - S.C.k + S.C.k = s' + 1 by omega]
            have := hc' (s' + 1)
            omega)
        omega
      · omega
    have hdw : dutyWindowStart S (s' + 2) ≤ supportCutoff S (s₁ + 1) :=
      dutyWindowStart_le_supportCutoff S (by omega)
    have hc₃ : supportCutoff S (s₁ + 1) ≤ voteTime S (s' + 1) := by
      have hm := slotStart_mono S (show s₁ + 1 ≤ s' by omega)
      have h1 := hc' (s₁ + 1)
      have h2 := hv' (s₁ + 1)
      have h3 := hv' (s' + 1)
      have h4 := hss s'
      omega
    have ht₃ : voteTime S (s' + 1) < t := by
      have := hc' (s' + 1)
      omega
    -- the tick at the vote time of slot `s' + 1`
    have hv₃ := hv' (s' + 1)
    obtain ⟨hl₃, -, hti₃'⟩ := stepBefore_spec x hDiv (by omega : 1 ≤ voteTime S (s' + 1))
    have hw₃ := hHon (voteTime S (s' + 1)) (by omega) (by omega)
    obtain ⟨n₃, sent₃, hrun₃, hst₃⟩ := tick_step_outcome x hl₃ hw₃.1 hw₃.2
    have hslot₃ : S.C.slot ((voteTime S (s' + 1) : ℕ) : Int) = s' + 1 := by
      have := hv' (s' + 1)
      have := hss (s' + 1)
      exact slot_eq_of_mem S (by omega) (by omega)
    obtain ⟨τ, hτ, hτle⟩ := hτ₁
    have hAw₃ : (tickInputState x (stepBefore x (voteTime S (s' + 1))) (voteTime S (s' + 1))
        w).awakeSince = some τ :=
      GoldilocksCorrectness.Statements.Executions.awakeSince_kept_of_awake_throughout S Sched x _ _
        w τ hDiv hc₃ hτ (fun t'' h1 h2 => (hHon t'' (by omega) (by omega)).1)
    have hτ₃ : τ ≤ duty_window_start S.C (s' + 1) :=
      le_trans hτle (duty_window_start_mono S (by omega))
    have hA₃ : (tickInputState x (stepBefore x (voteTime S (s' + 1))) (voteTime S (s' + 1)) w).A =
        (stateBefore x (voteTime S (s' + 1)) w).A := (tickInputState_frame x _ _ w).2.1
    have hS₃ : (tickInputState x (stepBefore x (voteTime S (s' + 1))) (voteTime S (s' + 1)) w).S =
        (stateBefore x (voteTime S (s' + 1)) w).S := (tickInputState_frame x _ _ w).1
    obtain ⟨A₃, hRevoke, hlock₃⟩ :=
      GoldilocksCorrectness.Statements.Routines.lem13_tick_revokes_locks S.C S.P S.X _ n₃ _ sent₃
        hrun₃ (by rw [hslot₃, voteTime_cast]) (by rw [hslot₃]; exact ⟨τ, hAw₃, hτ₃⟩)
    rw [hslot₃, hA₃, hS₃] at hRevoke
    have hkeep := stateBefore_succ_keepsConfirmation x hDiv w hti₃'
    rw [hst₃] at hkeep
    obtain ⟨k1, -, -, -⟩ := hkeep
    -- the entry for `e` right after that tick, an entry of the revocation's answer, live then
    obtain ⟨e', he', hd', heB', -⟩ := htr (voteTime S (s' + 1) + 1) (by omega) (by omega)
    rw [k1, hlock₃] at he'
    have hlive' : is_live (fg_to_ac (stateBefore x (voteTime S (s' + 1)) w).S)
        ((voteTime S (s' + 1) : ℕ) : Int) e' = true := by
      simp only [is_live_iff]
      refine ⟨?_, revoke_locks_entry_mem_tree (Nat.le_add_left 1 s') hRevoke e' he'⟩
      rw [hd']
      exact lt_trans (Int.ofNat_lt.2 ht₃) hlive
    exact compatible_of_ancestorEq_compatible heB' (hInv.2.1 w hw A₃ hRevoke e' he' hlive')
  · -- `s₁ = s'`: the update of slot `s' + 1` saved `C'`, which clause 3 puts on `B`'s chain
    subst heq
    obtain ⟨-, -, A'', hA'', hsave, -⟩ :=
      update_state_of_lock_entry S Sched x t s₁ w e hDiv he hd₁ hcut₁
    have hAA : A'' = A' := by
      rw [hA''] at hA'
      exact Except.ok.inj hA'
    have hsv : (stateBefore x (supportCutoff S (s₁ + 1) + 1) w).A.saved_confirmation s₁ =
        some C' := by
      rw [hsave, hAA]
      exact hC'
    have hBC' := hInv.2.2 w hw C' hsv
    exact compatible_of_ancestorEq_both heC hBC' ((compatible_iff _ _).2 (Or.inl (ancestorEq_refl _)))

/-- Lemma 79a, the first clause of the step. The proof; the audited statement is in
`Statements/Executions/HonestChainStatements.lean`.

Roots name blocks until `supportCutoff S s'`: Lemma 26b, which the proof calls at slot `s'`,
takes blocks as held up to the support cutoff of slot `s'`. -/
theorem lem79a_honestChainExtends_votes_step (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched)
    (GST s' : ℕ) (Hon : Finset V) (Hs : Finset V) (B : Block V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S s'))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    (hGST : GST ≤ voteTime S s')
    (hInv : HonestChainExtends S Sched x Hon B s')
    (hHon : ∀ v ∈ Hon, ∀ t : ℕ, dutyWindowStart S (s' + 1) ≤ t → t ≤ voteTime S (s' + 1) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    (hHs : ∀ u ∈ Hs, u ∈ Hon ∧ u ∈ S.P.committee s' ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s' ∧
        ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s') ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x[i + 1].sent - x[i].sent)
    (hVotersW : ∀ w ∈ Hon, ∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes S.C (stateBefore x (voteTime S (s' + 1)) w).A
        (fg_to_ac (stateBefore x (voteTime S (s' + 1)) w).S) (s' + 1) votes support_votes →
      voters_count votes < 2 * Hs.card)
    (hF2 : ∀ w ∈ Hon,
      (fg_to_ac (stateBefore x (voteTime S (s' + 1)) w).S).fc_root.compatible B = true)
    (hF3 : ∀ w ∈ Hon,
      (fg_to_ac (stateBefore x (voteTime S (s' + 1)) w).S).fc_root.AncestorEq B →
      ∀ tree : Finset (Block V),
        voter_block_tree S.C (stateBefore x (voteTime S (s' + 1)) w).A
          (fg_to_ac (stateBefore x (voteTime S (s' + 1)) w).S) (s' + 1) = .ok tree →
        ∃ W ∈ tree, W ∈ (fg_to_ac (stateBefore x (voteTime S (s' + 1)) w).S).viable_heads ∧
          B.AncestorEq W) :
    ∀ u ∈ Hon, ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (s' + 1)) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x[i + 1].sent - x[i].sent) →
      ∃ H_u ∈ (stateBefore x (voteTime S (s' + 1)) u).S.T,
        vote = GoldfishVote.mk u (s' + 1) H_u.root ∧ B.AncestorEq H_u := by
  intro w hw vote hSend
  -- the times
  have hΔ := one_le_Δ S
  have hdw : dutyWindowStart S (s' + 1) ≤ slotStart S s' := dutyWindowStart_succ_le_slotStart S s'
  have hv₁ : voteTime S s' = slotStart S s' + Δ S := voteTime_eq S s'
  have hc₁ : supportCutoff S s' = voteTime S s' + Δ S := supportCutoff_eq S s'
  have hv₂ : voteTime S (s' + 1) = voteTime S s' + 4 * Δ S := voteTime_succ S s'
  -- each voter of slot `s'` voted for a block it holds on `B`'s chain (clause 1)
  have hvote : ∀ u ∈ Hs, ∃ H_u : Block V,
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s') ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s' H_u.root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      H_u ∈ (stateBefore x (voteTime S s') u).S.T ∧ B.AncestorEq H_u := by
    intro u hu
    obtain ⟨huHon, -, vote', -, -, hsent⟩ := hHs u hu
    obtain ⟨H_u, hHT, hvt, hBH⟩ := hInv.1 u huHon vote' hsent
    subst hvt
    exact ⟨H_u, hsent, hHT, hBH⟩
  choose H hH using hvote
  let H' : V → Block V := fun u => if h : u ∈ Hs then H u h else B
  have hH' : ∀ u (hu : u ∈ Hs), H' u = H u hu := fun u hu => dif_pos hu
  exact GoldilocksCorrectness.Statements.Executions.lem26b_goldfish_vote_extends_voter_majority_block_held
    S Sched x GST s' Hs H' B w vote hDiv hMono hSync hCatch hRoots hParent hOwner hGST
    (fun u hu => by
      rw [hH' u hu]
      exact ⟨(hHs u hu).2.1, (hHon u (hHs u hu).1 (voteTime S (s' + 1)) (by omega) le_rfl).2,
        (hH u hu).1, (hH u hu).2.1, (hH u hu).2.2⟩)
    (hVotersW w hw) (fun t h1 h2 => hHon w hw t (by omega) (by omega)) (hF2 w hw) (hF3 w hw)
    (hInv.2.1 w hw) hSend

/-- Lemma 79b, the second clause of the step. The proof; the audited statement is in
`Statements/Executions/HonestChainStatements.lean`. -/
theorem lem79b_honestChainExtends_locks_step (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s' : ℕ) (Hon : Finset V) (B : Block V)
    (hDiv : TimeDiverges x.toTrace)
    (hInv : HonestChainExtends S Sched x Hon B s')
    (hHon : ∀ v ∈ Hon, ∀ t : ℕ, dutyWindowStart S (s' + 2) ≤ t → t ≤ voteTime S (s' + 2) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int)) :
    ∀ w ∈ Hon, ∀ A' : ACState V,
      revoke_locks S.P (expireLocks (stateBefore x (voteTime S (s' + 2)) w).A
        ((voteTime S (s' + 2) : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S (s' + 2)) w).S)
        ((voteTime S (s' + 2) : ℕ) : Int) (s' + 2) = .ok A' →
      ∀ e ∈ A'.lock_entries,
        is_live (fg_to_ac (stateBefore x (voteTime S (s' + 2)) w).S)
          ((voteTime S (s' + 2) : ℕ) : Int) e = true → e.B.compatible B = true := by
  intro w hw A' hRevoke e' he' _
  have hΔ := one_le_Δ S
  have hv₂ : voteTime S (s' + 2) = voteTime S (s' + 1) + 4 * Δ S := voteTime_succ S (s' + 1)
  have hc₁ : supportCutoff S (s' + 1) = voteTime S (s' + 1) + Δ S := supportCutoff_eq S (s' + 1)
  have hlt₂ : supportCutoff S (s' + 1) < voteTime S (s' + 2) := by omega
  obtain ⟨e, he, -, -, hB, -⟩ :=
    GoldilocksCorrectness.Statements.Routines.lem38_revoke_locks_entries_moved S.P _ A' _ _ (s' + 2)
      (Nat.le_add_left 1 (s' + 1)) hRevoke e' he'
  obtain ⟨heS, hlt⟩ := Finset.mem_filter.1 he
  exact compatible_of_ancestorEq_compatible hB
    (live_locks_compatible_of_honestChainExtends S Sched x Hon B s' (voteTime S (s' + 2)) w hDiv
      hInv hw (hHon w hw) hlt₂ le_rfl e heS hlt)

/-- Lemma 79c, the third clause of the step. The proof; the audited statement is in
`Statements/Executions/HonestChainStatements.lean`.

Roots name blocks until `supportCutoff S (s' + 1)`: Lemma 78, which the proof calls at slot `s'
+ 1`, takes blocks as held up to the support cutoff of slot `s' + 1`. -/
theorem lem79c_honestChainExtends_confirmations_step (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched)
    (GST s' : ℕ) (Hon : Finset V) (Hs : Finset V) (B : Block V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s' + 1)))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    (hGST : GST ≤ voteTime S (s' + 1))
    (hVotes : ∀ u ∈ Hon, ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (s' + 1)) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x[i + 1].sent - x[i].sent) →
      ∃ H_u ∈ (stateBefore x (voteTime S (s' + 1)) u).S.T,
        vote = GoldfishVote.mk u (s' + 1) H_u.root ∧ B.AncestorEq H_u)
    (hHon : ∀ v ∈ Hon, ∀ t : ℕ, dutyWindowStart S (s' + 2) ≤ t → t ≤ supportCutoff S (s' + 2) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    (hHs : ∀ u ∈ Hs, u ∈ Hon ∧ u ∈ S.P.committee (s' + 1) ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s' + 1 ∧
        ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (s' + 1)) ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x[i + 1].sent - x[i].sent)
    (hVotersV : ∀ v ∈ Hon,
      voters_count ((stateBefore x (supportCutoff S (s' + 2)) v).A.pool (s' + 1)) <
        2 * Hs.card)
    (hFv : ∀ v ∈ Hon, (stateBefore x (supportCutoff S (s' + 2)) v).S.F.compatible B = true) :
    ∀ v ∈ Hon, ∀ C' : Block V,
      (stateBefore x (supportCutoff S (s' + 2) + 1) v).A.saved_confirmation (s' + 1) = some C' →
      B.AncestorEq C' := by
  intro v hv
  -- the times
  have hΔ := one_le_Δ S
  have hdw : dutyWindowStart S (s' + 2) ≤ slotStart S (s' + 1) :=
    dutyWindowStart_succ_le_slotStart S (s' + 1)
  have hv₂ : voteTime S (s' + 2) = slotStart S (s' + 2) + Δ S := voteTime_eq S (s' + 2)
  have hc₂ : supportCutoff S (s' + 2) = voteTime S (s' + 2) + Δ S := supportCutoff_eq S (s' + 2)
  have hss : slotStart S (s' + 2) = slotStart S (s' + 1) + 4 * Δ S := by
    show slotStart S (s' + 1 + 1) = _
    rw [slotStart_eq, slotStart_eq S (s' + 1), Nat.mul_add, Nat.mul_one]
  -- each voter of slot `s' + 1` voted for a block it holds on `B`'s chain
  have hvote : ∀ u ∈ Hs, ∃ H_u : Block V,
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (s' + 1)) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u (s' + 1) H_u.root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      H_u ∈ (stateBefore x (voteTime S (s' + 1)) u).S.T ∧ B.AncestorEq H_u := by
    intro u hu
    obtain ⟨huHon, -, vote', -, -, hsent⟩ := hHs u hu
    obtain ⟨H_u, hHT, hvt, hBH⟩ := hVotes u huHon vote' hsent
    subst hvt
    exact ⟨H_u, hsent, hHT, hBH⟩
  choose H hH using hvote
  let H' : V → Block V := fun u => if h : u ∈ Hs then H u h else B
  have hH' : ∀ u (hu : u ∈ Hs), H' u = H u hu := fun u hu => dif_pos hu
  exact lem78_update_confirmation_extends_voter_majority_chain S Sched x GST (s' + 1) Hs H' B v
    hDiv hMono hSync hCatch hRoots hParent hOwner hGST
    (fun u hu => by
      rw [hH' u hu]
      exact ⟨(hHs u hu).2.1,
        (hHon u (hHs u hu).1 (supportCutoff S (s' + 2)) (by omega) le_rfl).2,
        (hH u hu).1, (hH u hu).2.1, (hH u hu).2.2⟩)
    (hVotersV v hv) (fun t h1 h2 => hHon v hv t h1 h2) (hFv v hv)

/-- Lemma 79, the step of the restricted slot invariant. The proof; the audited statement is in
`Statements/Executions/HonestChainStatements.lean`.

Roots name blocks until `supportCutoff S (s' + 1)`: Lemma 79c, which the proof calls, takes
blocks as held up to the support cutoff of slot `s' + 1`; Lemma 79a reads earlier. -/
theorem lem79_honestChainExtends_step (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched)
    (GST s' : ℕ) (Hon : Finset V) (Hs : ℕ → Finset V) (B : Block V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s' + 1)))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    (hGST : GST ≤ voteTime S s')
    (hInv : HonestChainExtends S Sched x Hon B s')
    (hHon : ∀ v ∈ Hon, ∀ t : ℕ, dutyWindowStart S (s' + 1) ≤ t → t ≤ supportCutoff S (s' + 2) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    (hHs : ∀ s₀ : ℕ, s₀ = s' ∨ s₀ = s' + 1 → ∀ u ∈ Hs s₀, u ∈ Hon ∧ u ∈ S.P.committee s₀ ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s₀ ∧
        ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s₀) ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x[i + 1].sent - x[i].sent)
    (hVotersW : ∀ w ∈ Hon, ∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes S.C (stateBefore x (voteTime S (s' + 1)) w).A
        (fg_to_ac (stateBefore x (voteTime S (s' + 1)) w).S) (s' + 1) votes support_votes →
      voters_count votes < 2 * (Hs s').card)
    (hVotersV : ∀ v ∈ Hon,
      voters_count ((stateBefore x (supportCutoff S (s' + 2)) v).A.pool (s' + 1)) <
        2 * (Hs (s' + 1)).card)
    (hF2 : ∀ w ∈ Hon,
      (fg_to_ac (stateBefore x (voteTime S (s' + 1)) w).S).fc_root.compatible B = true)
    (hF3 : ∀ w ∈ Hon,
      (fg_to_ac (stateBefore x (voteTime S (s' + 1)) w).S).fc_root.AncestorEq B →
      ∀ tree : Finset (Block V),
        voter_block_tree S.C (stateBefore x (voteTime S (s' + 1)) w).A
          (fg_to_ac (stateBefore x (voteTime S (s' + 1)) w).S) (s' + 1) = .ok tree →
        ∃ W ∈ tree, W ∈ (fg_to_ac (stateBefore x (voteTime S (s' + 1)) w).S).viable_heads ∧
          B.AncestorEq W)
    (hFv : ∀ v ∈ Hon,
      (stateBefore x (supportCutoff S (s' + 2)) v).S.F.compatible B = true) :
    HonestChainExtends S Sched x Hon B (s' + 1) := by
  -- the times
  have hΔ := one_le_Δ S
  have hv₁ : voteTime S (s' + 1) = voteTime S s' + 4 * Δ S := voteTime_succ S s'
  have hv₂ : voteTime S (s' + 2) = voteTime S (s' + 1) + 4 * Δ S := voteTime_succ S (s' + 1)
  have hc₂ : supportCutoff S (s' + 2) = voteTime S (s' + 2) + Δ S := supportCutoff_eq S (s' + 2)
  have hdw : dutyWindowStart S (s' + 1) ≤ dutyWindowStart S (s' + 2) :=
    dutyWindowStart_mono S (by omega)
  -- clause 1 (Lemma 79a)
  have hc₁ : supportCutoff S (s' + 1) = voteTime S (s' + 1) + Δ S := supportCutoff_eq S (s' + 1)
  have hc₀ : supportCutoff S s' = voteTime S s' + Δ S := supportCutoff_eq S s'
  have h1 := lem79a_honestChainExtends_votes_step S Sched x GST s' Hon (Hs s') B hDiv hMono hSync
    hCatch (hRoots.mono (by omega)) hParent hOwner hGST hInv
    (fun v hv t h1 h2 => hHon v hv t h1 (by omega)) (hHs s' (Or.inl rfl)) hVotersW hF2 hF3
  refine ⟨h1, ?_, ?_⟩
  · -- clause 2 (Lemma 79b)
    exact lem79b_honestChainExtends_locks_step S Sched x s' Hon B hDiv hInv
      (fun v hv t h1 h2 => hHon v hv t (le_trans (dutyWindowStart_mono S (by omega)) h1) (by omega))
  · -- clause 3 (Lemma 79c)
    exact lem79c_honestChainExtends_confirmations_step S Sched x GST s' Hon (Hs (s' + 1)) B hDiv
      hMono hSync hCatch hRoots hParent hOwner (by omega) h1
      (fun v hv t h1 h2 => hHon v hv t (by omega) h2) (hHs (s' + 1) (Or.inr rfl)) hVotersV hFv

end GoldilocksCorrectness.Proofs.Executions
