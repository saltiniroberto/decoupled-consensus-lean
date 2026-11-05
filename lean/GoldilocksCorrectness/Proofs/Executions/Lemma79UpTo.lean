module
public import GoldilocksCorrectness.Proofs.Executions.Lemma79
public import GoldilocksCorrectness.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Statements.Executions.NextSlotVoteStatementsUpTo
public import GoldilocksCorrectness.Proofs.Executions.Lemma78UpTo

@[expose] public section

/-!
# `Lemma79.lean` with the delivery premises up to a bound

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma79.lean` that name a delivery
premise, restated with `SynchronyFromWakeUpTo` and `CatchUpOnWakeUpTo` at a bound on the deadlines
. The bound of each twin
is the latest ordinary deadline `max t GST + Δ` of a send its proof reads, written in the twin's
own parameters.

* `lem79a_honestChainExtends_votes_step`, `lem79c_honestChainExtends_confirmations_step`,
  `lem79_honestChainExtends_step`

No `axiom`, no `native_decide`, no `sorry`. The landed page is imported, never edited.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_mono dutyWindowStart_succ_le_slotStart
  one_le_Δ slotStart_eq supportCutoff_eq voteTime_eq voteTime_succ)

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

/-- Lemma 79a, the first clause of the step. The proof; the audited statement is in
`Statements/Executions/HonestChainStatements.lean`.

Roots name blocks until `supportCutoff S s'`: Lemma 26b, which the proof calls at slot `s'`,
takes blocks as held up to the support cutoff of slot `s'`.

Restated with the delivery premises up to `supportCutoff S s'`: the slot-`s'` votes reach every voter of slot `s' + 1` by then (`lem26b_goldfish_vote_extends_voter_majority_block_held_upTo`). -/
theorem lem79a_honestChainExtends_votes_step_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched)
    (GST s' : ℕ) (Hon : Finset V) (Hs : Finset V) (B : Block V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S s'))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S s'))
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
  exact GoldilocksCorrectness.Statements.Executions.lem26b_goldfish_vote_extends_voter_majority_block_held_upTo
    S Sched x GST s' Hs H' B w vote hDiv hMono hSync hCatch hRoots hParent hOwner hGST
    (fun u hu => by
      rw [hH' u hu]
      exact ⟨(hHs u hu).2.1, (hHon u (hHs u hu).1 (voteTime S (s' + 1)) (by omega) le_rfl).2,
        (hH u hu).1, (hH u hu).2.1, (hH u hu).2.2⟩)
    (hVotersW w hw) (fun t h1 h2 => hHon w hw t (by omega) (by omega)) (hF2 w hw) (hF3 w hw)
    (hInv.2.1 w hw) hSend

/-- Lemma 79c, the third clause of the step. The proof; the audited statement is in
`Statements/Executions/HonestChainStatements.lean`.

Roots name blocks until `supportCutoff S (s' + 1)`: Lemma 78, which the proof calls at slot `s'
+ 1`, takes blocks as held up to the support cutoff of slot `s' + 1`.

Restated with the delivery premises up to `supportCutoff S (s' + 1)`: the slot-`(s' + 1)` votes reach every updater by then (`lem78_update_confirmation_extends_voter_majority_chain_upTo`). -/
theorem lem79c_honestChainExtends_confirmations_step_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched)
    (GST s' : ℕ) (Hon : Finset V) (Hs : Finset V) (B : Block V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S (s' + 1)))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S (s' + 1)))
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
  exact lem78_update_confirmation_extends_voter_majority_chain_upTo S Sched x GST (s' + 1) Hs H' B v
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
blocks as held up to the support cutoff of slot `s' + 1`; Lemma 79a reads earlier.

Restated with the delivery premises up to `supportCutoff S (s' + 1)`: the slot-`(s' + 1)` votes reach every updater by then (`lem79c_honestChainExtends_confirmations_step_upTo`). -/
theorem lem79_honestChainExtends_step_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched)
    (GST s' : ℕ) (Hon : Finset V) (Hs : ℕ → Finset V) (B : Block V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S (s' + 1)))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S (s' + 1)))
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
  have h1 := lem79a_honestChainExtends_votes_step_upTo S Sched x GST s' Hon (Hs s') B hDiv hMono
    (SynchronyFromWakeUpTo.mono (by omega) hSync) (CatchUpOnWakeUpTo.mono (by omega) hCatch)
    (hRoots.mono (by omega)) hParent hOwner hGST hInv
    (fun v hv t h1 h2 => hHon v hv t h1 (by omega)) (hHs s' (Or.inl rfl)) hVotersW hF2 hF3
  refine ⟨h1, ?_, ?_⟩
  · -- clause 2 (Lemma 79b)
    exact lem79b_honestChainExtends_locks_step S Sched x s' Hon B hDiv hInv
      (fun v hv t h1 h2 => hHon v hv t (le_trans (dutyWindowStart_mono S (by omega)) h1) (by omega))
  · -- clause 3 (Lemma 79c)
    exact lem79c_honestChainExtends_confirmations_step_upTo S Sched x GST s' Hon (Hs (s' + 1)) B hDiv
      hMono hSync hCatch hRoots hParent hOwner (by omega) h1
      (fun v hv t h1 h2 => hHon v hv t (by omega) h2) (hHs (s' + 1) (Or.inr rfl)) hVotersV hFv

end GoldilocksCorrectness.Proofs.Executions

