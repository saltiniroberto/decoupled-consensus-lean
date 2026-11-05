module
public import GoldilocksCorrectness.Proofs.Executions.Lemma78
public import GoldilocksCorrectness.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Statements.Executions.DeliveryStatementsUpTo

@[expose] public section

/-!
# `Lemma78.lean` with the delivery premises up to a bound

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma78.lean` that name a delivery
premise, restated with `SynchronyFromWakeUpTo` and `CatchUpOnWakeUpTo` at a bound on the deadlines
. The bound of each twin
is the latest ordinary deadline `max t GST + Δ` of a send its proof reads, written in the twin's
own parameters.

* `lem78_update_confirmation_extends_voter_majority_chain`

No `axiom`, no `native_decide`, no `sorry`. The landed page is imported, never edited.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_succ_le_slotStart one_le_Δ slotStart_eq
  supportCutoff_eq voteTime_eq)

open GoldilocksCorrectness.Statements.Routines (EarlySupporterOf)

open GoldilocksCorrectness.Proofs.Routines (earlySupporterOf_of_keepsVotes expireLocks_keepsVotes)

open GoldilocksCorrectness.Proofs.Routines (fg_to_ac_F pool_of_keepsVotes)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn expireLocks)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- Lemma 78, an honest confirmation update over a voter majority's chain. Its reading is on the
statement page, `GoldilocksCorrectness/Statements/Executions/HonestChainStatements.lean`.

Roots name blocks until `supportCutoff S s`: the bound of the Lemma 12 call at slot `s` it
passes the premise to.

Restated with the delivery premises up to `supportCutoff S s`: the slot-`s` votes reach `v` by then (`lem12_honest_vote_delivered_until_upTo`). -/
theorem lem78_update_confirmation_extends_voter_majority_chain_upTo (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (GST s : ℕ) (Hs : Finset V) (H : V → Block V) (B : Block V) (v : V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S s))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S s))
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S s))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    (hGST : GST ≤ voteTime S s)
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ Sched.adv (supportCutoff S (s + 1) : Int) ∧
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      H u ∈ (stateBefore x (voteTime S s) u).S.T ∧ B.AncestorEq (H u))
    (hVoters : voters_count ((stateBefore x (supportCutoff S (s + 1)) v).A.pool s) <
      2 * Hs.card)
    (hv : ∀ t : ℕ, dutyWindowStart S (s + 1) ≤ t → t ≤ supportCutoff S (s + 1) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    (hF : (stateBefore x (supportCutoff S (s + 1)) v).S.F.compatible B = true) :
    ∀ C' : Block V,
      (stateBefore x (supportCutoff S (s + 1) + 1) v).A.saved_confirmation s = some C' →
      B.AncestorEq C' := by
  intro C' hC'
  -- the times
  have hΔ := one_le_Δ S
  have hss : slotStart S (s + 1) = slotStart S s + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hv₃ : voteTime S (s + 1) = slotStart S (s + 1) + Δ S := voteTime_eq S (s + 1)
  have hv₂ : supportCutoff S (s + 1) = voteTime S (s + 1) + Δ S := supportCutoff_eq S (s + 1)
  have hc₁ : supportCutoff S s = voteTime S s + Δ S := supportCutoff_eq S s
  have hv₁ : voteTime S s = slotStart S s + Δ S := voteTime_eq S s
  have hdw : dutyWindowStart S (s + 1) ≤ slotStart S s := dutyWindowStart_succ_le_slotStart S s
  have hdwc : dutyWindowStart S (s + 1) < supportCutoff S (s + 1) := by omega
  -- the update at `c` and the state right after it
  have hvc := hv (supportCutoff S (s + 1)) hdwc.le le_rfl
  have hAw := awakeSince_le_dutyWindowStart_b S Sched x (s + 1) (supportCutoff S (s + 1)) v hDiv
    hMono hdwc (fun t h1 h2 => (hv t h1 h2).1) hvc.2
  obtain ⟨A'', hUpdate, hsave, -, -, -⟩ := update_state_of_duty S Sched x s v hDiv hvc hAw
  rw [hsave] at hC'
  rcases (compatible_iff _ _).1 hF with hFB | hBF
  · -- the finalized block is `B` or an ancestor of `B`: Lemma 12 at `c`, then Lemma 77
    have hHeld : ∀ u ∈ Hs, HeldEarlyVoteFor S.C (stateBefore x (supportCutoff S (s + 1)) v).A
        (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S) s (H u) u :=
      GoldilocksCorrectness.Statements.Executions.lem12_honest_vote_delivered_until_upTo S Sched x GST s
        (supportCutoff S (s + 1)) Hs H v hDiv hMono hSync hCatch hRoots hParent hOwner hGST
        (by omega)
        (fun u hu => ⟨(hHs u hu).1, (hHs u hu).2.1, (hHs u hu).2.2.1, (hHs u hu).2.2.2.1⟩)
        (fun t h1 h2 => hv t (by omega) (by omega))
        (fun u hu => ancestorEq_trans hFB (hHs u hu).2.2.2.2)
    obtain ⟨u₀, hu₀⟩ : Hs.Nonempty := Finset.card_pos.1 (by omega)
    have hRoots₂ : RootsNameBlocksIn
        (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S).tree :=
      rootsNameBlocksIn_frame_of_exec_node S Sched x _ v
    have hPathF : ∀ P' : Block V,
        (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S).F.AncestorEq P' →
        P'.AncestorEq B → P' ∈ (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S).tree :=
      fun P' h1 h2 => frame_path_of_exec S Sched x _ v (H u₀) P' (hHeld u₀ hu₀).2.2.1 h1
        (ancestorEq_trans h2 (hHs u₀ hu₀).2.2.2.2)
    have hSup : ∀ u ∈ Hs, EarlySupporterOf S.C
        (expireLocks (stateBefore x (supportCutoff S (s + 1)) v).A
          ((supportCutoff S (s + 1) : ℕ) : Int))
        (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S) (s + 1 - 1) B u :=
      fun u hu => (earlySupporterOf_of_keepsVotes (expireLocks_keepsVotes _ _) _ _ _ _ _).2
        (heldEarlyVoteFor_earlySupporterOf S.C _ _ s B (H u) u (hHeld u hu)
          (hHs u hu).2.2.2.2)
    have h77 :=
      GoldilocksCorrectness.Statements.Routines.lem77_update_confirmation_extends_voter_majority_chain
        S.C S.P (expireLocks (stateBefore x (supportCutoff S (s + 1)) v).A
          ((supportCutoff S (s + 1) : ℕ) : Int)) A''
        (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S)
        ((supportCutoff S (s + 1) : ℕ) : Int) (s + 1) B Hs (Nat.le_add_left 1 s) hRoots₂
        (by rw [fg_to_ac_F]; exact hFB) hPathF hSup
        (by rw [pool_of_keepsVotes (expireLocks_keepsVotes _ _)]
            exact pool_slot_of_stateBefore S Sched x _ v s)
        (by rw [pool_of_keepsVotes (expireLocks_keepsVotes _ _)]; exact hVoters) hUpdate
    rw [Nat.add_sub_cancel] at h77
    exact h77 C' hC'
  · -- `B` is an ancestor of the finalized block: the saved block descends from it
    have h := GoldilocksCorrectness.Statements.Routines.saved_confirmation_F_ancestorEq S.C S.P _
      A'' _ _ (s + 1) (Nat.le_add_left 1 s) hUpdate
    rw [Nat.add_sub_cancel] at h
    exact ancestorEq_trans hBF (by rw [← fg_to_ac_F]; exact h C' hC')

end GoldilocksCorrectness.Proofs.Executions

