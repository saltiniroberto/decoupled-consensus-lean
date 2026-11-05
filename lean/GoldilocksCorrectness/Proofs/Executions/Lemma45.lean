module
public import GoldilocksCorrectness.Statements.Executions.EligibleBlockVoteStatements
public import GoldilocksCorrectness.Statements.Executions.ConfirmationCompatibilityStatements
public import GoldilocksCorrectness.Statements.Executions.LockProvenanceStatements
public import GoldilocksCorrectness.Proofs.Executions.Lemma33
public import GoldilocksCorrectness.Proofs.Executions.Lemma42
public import GoldilocksCorrectness.Proofs.Routines.Schedule

@[expose] public section

/-!
# Lemma 45: a lock whose window is after `GST` is extended by the next slot's honest votes

The proof of `lem45_honest_vote_extends_lock_of_post_GST_window`, stated in
`GoldilocksCorrectness/Statements/Executions/HealingStatements.lean`, and two facts about times
it reads.

Write `c := supportCutoff S (s + 1)` (the time of `v`'s update of slot `s + 1`) and
`t₃ := voteTime S (s + 1)` (the time of `w`'s revocation and vote). The route:

1. Lemma 35 on `v`'s update: `e` is not an entry of the update's input, since such an entry was
   added by the update of its own slot, before `c` (Lemma 39), and the deadline names the slot;
   so `e`'s block is the saved confirmation `C'` of slot `s` or an ancestor of it, and it is a
   fast block of the answer or passes the slow test of slot `s`;
2. Lemma 36 gives `Sup`, early supporters of `e`'s block at `v` with `v`'s slot-`s` voters fewer
   than twice `Sup`;
3. the lock condition of Lemma 21 at `w`: when `e`'s block is fast, Lemma 42; when it passes the
   slow test, every entry `e'` that `w`'s revocation leaves comes from a live entry `e_w` of its
   input (Lemma 38), which is a lock of a slot `s'` with `s + 1 − k ≤ s' < s` (Lemmas 39 and
   41) on `w`'s saved confirmation `C_w` of slot `s'` or an ancestor of it; the slow test makes
   `e`'s block `v`'s saved confirmation `Cj` of slot `s'` or an ancestor of it (Lemma 37); the two
   updates of slot `s' + 1` that saved `C_w` and `Cj` (Lemma 40) save compatible blocks
   (Lemma 31, its windows inside `hv` and `hw` since `s' ≥ s + 1 − k`); so `e'`'s block is
   compatible with `e`'s;
4. Lemma 21.

The route of the brief's step 3 went through Lemma 33 for the slow case. Lemma 33 asks for the
compatibility of the two validators' saved confirmations at every slot from `s + 1 − k` to `s`,
read just after `c`, and at slot `s` this needs `w` honest at `c` (Lemma 31's honesty at the
support cutoff of slot `s + 1`), which `hw` does not give: `w`'s window ends at `t₃`. The proof
uses only the slot `s'` of each entry, where Lemma 31 applies directly, and so does not call
Lemma 33.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff viewFreeze
  dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_succ_le_slotStart
  dutyWindowStart_succ_le_supportCutoff lockDeadline_injective one_le_Δ slotStart_eq slotStart_mono
  supportCutoff_eq supportCutoff_lt_of_lt viewFreeze_eq voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (compatible_of_ancestorEq_both)
open GoldilocksCorrectness.Statements.Routines (EarlySupporterOf)

open GoldilocksCorrectness.Proofs.Routines (earlySupporterOf_of_keepsVotes expireLocks_keepsVotes
  fc_root_eq pool_of_keepsVotes)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn expireLocks)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_trans compatible_of_ancestorEq_compatible)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

-- An index `x[i]` into an execution, and `x[i][v]` into a configuration, has the valid-index
-- predicate `fun _ _ => True`; this rule, local to the file, proves it at once, as in
-- `Lemma21.lean`.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- **Lemma 45, a lock whose window is after `GST` is extended by the next slot's honest votes.**
The proof; the audited statement is in `Statements/Executions/HealingStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s`: the slot of the lock;
- `v`: the validator whose update of slot `s + 1` adds the lock entry `e`; `A'`: that update's
  answer; `w`: the voter of slot `s + 1`; `vote`: its Goldfish vote.

Roots name blocks until `supportCutoff S (s + 1)`: Lemma 21 and Lemma 42, which the proof calls
at slot `s`, take blocks as held up to the support cutoff of slot `s + 1`; Lemma 31 reads at an
earlier slot. -/
theorem lem45_honest_vote_extends_lock_of_post_GST_window (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched)
    (GST s : ℕ) (v w : V) (A' : ACState V) (e : LockEntry V) (vote : GoldfishVote V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s + 1)))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hGST : GST ≤ supportCutoff S (s + 1 - S.C.k))
    (hv : ∀ t : ℕ, dutyWindowStart S (s + 1) ≤ t → t ≤ supportCutoff S (s + 1) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    (hw : ∀ t : ℕ, dutyWindowStart S (s + 1) ≤ t → t ≤ voteTime S (s + 1) →
      w ∈ Sched.awake (t : Int) ∧ w ∉ Sched.adv (t : Int))
    (hUpdate : update_confirmation S.C S.P
        (expireLocks (stateBefore x (supportCutoff S (s + 1)) v).A
          ((supportCutoff S (s + 1) : ℕ) : Int))
        (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S)
        ((supportCutoff S (s + 1) : ℕ) : Int) (s + 1) = .ok A')
    (he : e ∈ A'.lock_entries)
    (hd : e.d = S.C.t_ (s + S.C.k) + 5 * S.C.Δ)
    (hF2 : (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).fc_root.compatible e.B = true)
    (hF3 : (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).fc_root.AncestorEq e.B →
      ∀ tree : Finset (Block V),
        voter_block_tree S.C (stateBefore x (voteTime S (s + 1)) w).A
          (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) (s + 1) = .ok tree →
        ∃ W ∈ tree, W ∈ (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).viable_heads ∧
          e.B.AncestorEq W)
    (hSend : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (s + 1)) ∧
      (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent) :
    ∃ H_w : Block V, vote.head = H_w.root ∧ e.B.AncestorEq H_w := by
  have hFroot : (stateBefore x (voteTime S (s + 1)) w).S.F.AncestorEq
      (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).fc_root := by
    rw [fc_root_eq]; exact F_ancestorEq_fc_root_of_stateBefore S Sched x (voteTime S (s + 1)) w
  -- the times
  have hΔ := one_le_Δ S
  have hb1 : 1 ≤ s + 1 := Nat.le_add_left 1 s
  have hss : slotStart S (s + 1) = slotStart S s + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hv₃ : voteTime S (s + 1) = slotStart S (s + 1) + Δ S := voteTime_eq S (s + 1)
  have hvb : voteTime S s = slotStart S s + Δ S := voteTime_eq S s
  have hcb : supportCutoff S s = voteTime S s + Δ S := supportCutoff_eq S s
  have ht₂ : supportCutoff S (s + 1) = voteTime S (s + 1) + Δ S := supportCutoff_eq S (s + 1)
  have hfr : viewFreeze S s = slotStart S s + 3 * Δ S := viewFreeze_eq S s
  have hdw : dutyWindowStart S (s + 1) ≤ slotStart S s := dutyWindowStart_succ_le_slotStart S s
  have hGSTb : GST ≤ supportCutoff S s := by
    have h := slotStart_mono S (show s + 1 - S.C.k ≤ s by have := S.C.k_ge_two; omega)
    rw [supportCutoff_eq S (s + 1 - S.C.k), voteTime_eq S (s + 1 - S.C.k)] at hGST
    omega
  have hRootsΦv : RootsNameBlocksIn
      (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S).tree :=
    rootsNameBlocksIn_frame_of_exec_node S Sched x _ v
  -- step 1: Lemma 35 on `v`'s update; `e` is an entry it adds
  obtain ⟨-, h35⟩ := GoldilocksCorrectness.Statements.Routines.lem35_update_confirmation_lock_entries
    S.C S.P _ A' _ _ (s + 1) hUpdate
  rcases h35 e he with hin | ⟨-, -, -, ⟨C', hSaved, hLC'⟩, hFS⟩
  · -- an entry of the input was added by the update of its own slot `s`, before `c`
    exfalso
    have hin' : e ∈ (stateBefore x (supportCutoff S (s + 1)) v).A.lock_entries := by
      simp only [expireLocks, Finset.mem_filter] at hin
      exact hin.1
    obtain ⟨s', hd', hlt, -⟩ :=
      GoldilocksCorrectness.Proofs.Executions.lem39_lock_entry_provenance S Sched x _ v e hDiv hin'
    have hbb : s' = s := lockDeadline_injective S (hd'.symm.trans hd)
    rw [hbb] at hlt
    exact lt_irrefl _ hlt
  -- step 2: Lemma 36 gives the early supporters of `e`'s block at `v`
  obtain ⟨Sup, hSup, hElig, -⟩ :=
    GoldilocksCorrectness.Statements.Routines.lem36_confirmed_ancestor_early_supporters S.C S.P
      _ A' _ _ (s + 1) C' e.B hb1 hRootsΦv
      (by rw [Nat.add_sub_cancel, pool_of_keepsVotes (expireLocks_keepsVotes _ _)]
          exact pool_vote_late S Sched x s v hDiv)
      hUpdate hSaved hLC'
  simp only [Nat.add_sub_cancel] at hSup hElig hFS
  -- `expireLocks` keeps the pool and the stamps
  have hSup' : ∀ u ∈ Sup, EarlySupporterOf S.C (stateBefore x (supportCutoff S (s + 1)) v).A
      (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S) s e.B u := fun u hu =>
    (earlySupporterOf_of_keepsVotes (expireLocks_keepsVotes _ _) _ _ _ _ _).1 (hSup u hu)
  have hElig' : voters_count ((stateBefore x (supportCutoff S (s + 1)) v).A.pool s) <
      2 * Sup.card := by
    rw [pool_of_keepsVotes (expireLocks_keepsVotes _ _)] at hElig; exact hElig
  -- step 3: the lock condition at `w`
  have hLocks : ∀ A'' : ACState V,
      revoke_locks S.P (expireLocks (stateBefore x (voteTime S (s + 1)) w).A
        ((voteTime S (s + 1) : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
        ((voteTime S (s + 1) : ℕ) : Int) (s + 1) = .ok A'' →
      ∀ e' ∈ A''.lock_entries,
        is_live (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
          ((voteTime S (s + 1) : ℕ) : Int) e' = true → e'.B.compatible e.B = true := by
    rcases hFS with hFast | hSlow
    · -- fast: Lemma 42
      intro A'' hRevoke e' he' _
      exact lem42_fast_lock_clears_conflicting_locks S Sched x GST s e.B v w A' hDiv hMono hSync
        hCatch hRoots hParent (by omega)
        (fun t h1 h2 => hv t (by omega) h2) (fun t h1 h2 => hw t (by omega) (by omega)) hUpdate
        hFast (compatible_of_ancestorEq_compatible hFroot hF2) A'' hRevoke e' he'
    · -- slow: through the slot of each entry `w`'s revocation reads
      intro A'' hRevoke e' he' _
      obtain ⟨e_w, he_w, -, -, he'w, -⟩ :=
        GoldilocksCorrectness.Statements.Routines.lem38_revoke_locks_entries_moved S.P _ A'' _ _
          (s + 1) hb1 hRevoke e' he'
      have he_w' : e_w ∈ (stateBefore x (voteTime S (s + 1)) w).A.lock_entries ∧
          ((voteTime S (s + 1) : ℕ) : Int) < e_w.d := by
        simp only [expireLocks, Finset.mem_filter] at he_w
        exact he_w
      -- the slot `s'` of `e_w`, and `w`'s saved confirmation of it
      obtain ⟨s', hd_w, hc_w, C_w, hC_w, hB_w⟩ :=
        lock_entry_saved_confirmation x hDiv _ w e_w he_w'.1
      -- `s' < s`: the update of slot `s' + 1` ran before `t₃`
      have hlt : s' < s := by
        by_contra h
        have h' : supportCutoff S (s + 1) ≤ supportCutoff S (s' + 1) := by
          rcases Nat.lt_or_eq_of_le (show s + 1 ≤ s' + 1 by omega) with h'' | h''
          · exact le_of_lt (supportCutoff_lt_of_lt S h'')
          · rw [h'']
        omega
      -- `s + 1 − k ≤ s'`: `e_w` is live at `t₃`
      have hlow : s + 1 - S.C.k ≤ s' := by
        by_cases hkb : S.C.k ≤ s + 1
        · refine GoldilocksCorrectness.Proofs.Executions.lem41_slot_of_live_entry S
            (s + 1 - S.C.k) s' (voteTime S (s + 1)) e_w hd_w he_w'.2 ?_
          rw [Nat.sub_add_cancel hkb]
        · omega
      -- `e`'s block is `v`'s saved confirmation of slot `s'` or an ancestor of it
      obtain ⟨-, hj⟩ :=
        GoldilocksCorrectness.Statements.Routines.lem37_slow_test_saved_confirmations S.C _ _ s
          e.B hSlow
      obtain ⟨Cj, hCj, -, hBj⟩ := hj s' hlow hlt
      have hCj' : (stateBefore x (supportCutoff S (s + 1)) v).A.saved_confirmation s' =
          some Cj := hCj
      -- the two updates of slot `s' + 1` that saved `Cj` and `C_w`
      obtain ⟨-, -, ⟨A_v, hUv, hSv⟩, -⟩ :=
        GoldilocksCorrectness.Proofs.Executions.lem40_saved_confirmation_provenance S Sched x
          (supportCutoff S (s + 1)) v s' Cj hDiv hCj'
      obtain ⟨-, -, ⟨A_w, hUw, hSw⟩, -⟩ :=
        GoldilocksCorrectness.Proofs.Executions.lem40_saved_confirmation_provenance S Sched x
          (voteTime S (s + 1)) w s' C_w hDiv hC_w
      -- the times of slot `s'`
      have hssw : slotStart S (s' + 1) = slotStart S s' + 4 * Δ S := by
        rw [slotStart_eq, slotStart_eq S s', Nat.mul_add, Nat.mul_one]
      have hssle : slotStart S (s' + 1) ≤ slotStart S s := slotStart_mono S hlt
      have hvw : voteTime S s' = slotStart S s' + Δ S := voteTime_eq S s'
      have hcw : supportCutoff S s' = voteTime S s' + Δ S := supportCutoff_eq S s'
      have hcw1 : supportCutoff S (s' + 1) = voteTime S (s' + 1) + Δ S :=
        supportCutoff_eq S (s' + 1)
      have hvw1 : voteTime S (s' + 1) = slotStart S (s' + 1) + Δ S := voteTime_eq S (s' + 1)
      have hfrw : viewFreeze S s' = slotStart S s' + 3 * Δ S := viewFreeze_eq S s'
      have hdww : dutyWindowStart S (s + 1) ≤ supportCutoff S s' :=
        dutyWindowStart_succ_le_supportCutoff S (by omega)
      have hGSTw : GST ≤ supportCutoff S s' := by
        have h := slotStart_mono S hlow
        rw [supportCutoff_eq S (s + 1 - S.C.k), voteTime_eq S (s + 1 - S.C.k)] at hGST
        omega
      have hcomp := GoldilocksCorrectness.Proofs.Executions.lem31_saved_confirmations_compatible S
        Sched x GST s' w v A_w A_v C_w Cj hDiv hMono hSync hCatch
        (hRoots.mono (by omega)) hGSTw
        (fun t h1 h2 => hw t (by omega) (by omega)) (fun t h1 h2 => hv t (by omega) (by omega))
        (hw _ (by omega) (by omega)).2 (hv _ (by omega) (by omega)).2 hUw hSw hUv hSv
      exact compatible_of_ancestorEq_both (ancestorEq_trans he'w hB_w) hBj hcomp
  -- step 4: Lemma 21
  exact GoldilocksCorrectness.Proofs.Executions.lem21_goldfish_vote_extends_eligible_block S Sched
    x GST s Sup e.B v w vote hDiv hMono hSync hCatch hRoots hParent (by omega)
    (fun t h1 h2 => hv t (by omega) h2) (fun t h1 h2 => hw t (by omega) (by omega))
    hSup' hElig' hF2 hF3 hLocks hSend

end GoldilocksCorrectness.Proofs.Executions
