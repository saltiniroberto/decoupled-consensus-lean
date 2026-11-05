module
public import GoldilocksCorrectness.Statements.Routines.ConfirmationStatements
public import GoldilocksCorrectness.Statements.Routines.LockStatements
public import GoldilocksCorrectness.Statements.Executions.ReadingPointStatements
public import GoldilocksCorrectness.Proofs.Executions.Lemma31
public import GoldilocksCorrectness.Proofs.Routines.Confirmation

@[expose] public section

/-!
# Lemma 42: a fast lock clears every conflicting lock

The proof of `lem42_fast_lock_clears_conflicting_locks`, stated in
`GoldilocksCorrectness/Statements/Executions/HealingStatements.lean`, and of the helper
`update_confirmation_fast_block_saved`: a fast block of a confirmation update's answer is the
saved confirmation of the slot before or an ancestor of it.

Write `c := supportCutoff S s`, `freeze := viewFreeze S s`, `t₃ := voteTime S (s + 1)` (the time
of `w`'s revocation) and `t₂ := supportCutoff S (s + 1)` (the time of `v`'s update of slot
`s + 1`). The route:

1. when `L` is `w`'s finalized block or an ancestor of it, every entry the revocation leaves is
   on a block of `w`'s frame tree, a descendant of that finalized block or it, hence compatible
   with `L`; otherwise `w`'s finalized block is an ancestor of `L`, or `L`;
2. `L` is a fast block of `v`'s update, so the update saved some `C'` with `L` an ancestor of it
   or it, and Lemma 36 gives `Sup`, early supporters of `L` at `v` with the slot-`s` committee at
   most twice `Sup`;
3. each member `u` of `Sup` votes once for `L`'s chain in `w`'s pool before `t₃`: Lemma 63 read
   on `w`'s pool (`supporters_vote_once_in_pool_at`,
   `GoldilocksCorrectness/Statements/Executions/ReadingPointStatements.lean`) at the reading points
   `c`, `freeze`, `t₃`, `t₂`, with `Sup`'s early support cast to the cutoff `c`
   (`supportCutoff_cast`);
4. Lemma 5 on `w`'s revocation, with `Sup`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff viewFreeze)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slotStart_eq supportCutoff_cast
  supportCutoff_eq viewFreeze_eq voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (earlySupporterOf_of_keepsVotes expireLocks_keepsVotes
  pool_of_keepsVotes votesOnceInPoolFor_of_keepsVotes)

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Statements.Routines

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

end GoldilocksCorrectness.Proofs.Routines

namespace GoldilocksCorrectness.Proofs.Executions

open GoldilocksCorrectness.Proofs.Routines (mem_fg_to_ac_tree)

open GoldilocksCorrectness.Statements.Routines (EarlySupporterOf)

open Framework.StsMultisetLog (AtomicExec AtomicAction AtomicHonest Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn VotesOnceInPoolFor expireLocks)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_trans compatible_iff
  revoke_locks_entry_mem_tree update_confirmation_fast_block_saved)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

-- An index `x[i]` into an execution, and `x[i][v]` into a configuration, has the valid-index
-- predicate `fun _ _ => True`; this rule, local to the file, proves it at once, as in
-- `Lemma21.lean`.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- **Lemma 42, a fast lock clears every conflicting lock.** The proof; the audited statement is
in `Statements/Executions/HealingStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s`: the slot whose votes `v`'s update of slot `s + 1` counts;
- `L`: the fast block; `v`: the validator whose update makes `L` fast; `w`: the validator whose
  revocation is read; `A'`: `v`'s update's answer.

Roots name blocks until `supportCutoff S (s + 1)`: `supporters_vote_once_in_pool_at`, which the
proof calls with `t_w := voteTime S (s + 1)`, takes blocks as held up to one delay after `w`'s
vote time of slot `s + 1`. -/
theorem lem42_fast_lock_clears_conflicting_locks (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s : ℕ) (L : Block V) (v w : V) (A' : ACState V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s + 1)))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hGST : GST ≤ supportCutoff S s)
    (hv : ∀ t : ℕ, voteTime S (s + 1) ≤ t → t ≤ supportCutoff S (s + 1) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    (hw : ∀ t : ℕ, supportCutoff S s ≤ t → t ≤ viewFreeze S s →
      w ∈ Sched.awake (t : Int) ∧ w ∉ Sched.adv (t : Int))
    (hUpdate : update_confirmation S.C S.P
        (expireLocks (stateBefore x (supportCutoff S (s + 1)) v).A
          ((supportCutoff S (s + 1) : ℕ) : Int))
        (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S)
        ((supportCutoff S (s + 1) : ℕ) : Int) (s + 1) = .ok A')
    (hFast : L ∈ A'.fast_blocks)
    (hF : (stateBefore x (voteTime S (s + 1)) w).S.F.compatible L = true) :
    ∀ A'' : ACState V,
      revoke_locks S.P (expireLocks (stateBefore x (voteTime S (s + 1)) w).A
        ((voteTime S (s + 1) : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
        ((voteTime S (s + 1) : ℕ) : Int) (s + 1) = .ok A'' →
      ∀ e ∈ A''.lock_entries, e.B.compatible L = true := by
  intro A'' hRevoke
  -- the times
  have hΔ := one_le_Δ S
  have hss : slotStart S (s + 1) = slotStart S s + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hss' : slotStart S (s + 1 + 1) = slotStart S (s + 1) + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq S (s + 1), Nat.mul_add, Nat.mul_one]
  have hss2 : slotStart S (s + 2) = slotStart S (s + 1) + 4 * Δ S := hss'
  have hv₃ : voteTime S (s + 1) = slotStart S (s + 1) + Δ S := voteTime_eq S (s + 1)
  have hv₁ : voteTime S s = slotStart S s + Δ S := voteTime_eq S s
  have hc : supportCutoff S s = voteTime S s + Δ S := supportCutoff_eq S s
  have ht₂ : supportCutoff S (s + 1) = voteTime S (s + 1) + Δ S := supportCutoff_eq S (s + 1)
  have hfr : viewFreeze S s = slotStart S s + 3 * Δ S := viewFreeze_eq S s
  have hb1 : 1 ≤ s + 1 := Nat.le_add_left 1 s
  have hRootsΦw : RootsNameBlocksIn (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).tree :=
    rootsNameBlocksIn_frame_of_exec_node S Sched x _ w
  have hRootsΦv : RootsNameBlocksIn
      (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S).tree :=
    rootsNameBlocksIn_frame_of_exec_node S Sched x _ v
  -- step 1: when `L` is `w`'s finalized block or an ancestor of it, every entry left is on a
  -- block of `w`'s frame tree, a descendant of the finalized block or it
  rcases (compatible_iff _ _).1 hF with hFL | hLF
  swap
  · intro e he
    have heT := revoke_locks_entry_mem_tree hb1 hRevoke e he
    exact (compatible_iff _ _).2 (Or.inr (ancestorEq_trans hLF ((mem_fg_to_ac_tree _ _).1 heT).2))
  -- step 2: Lemma 36 on `v`'s update
  obtain ⟨C', hSaved, hLC'⟩ :=
    update_confirmation_fast_block_saved S.C S.P _ _ _ _ (s + 1) L hb1 hUpdate hFast
  obtain ⟨Sup, hSup, -, hHalf⟩ :=
    GoldilocksCorrectness.Statements.Routines.lem36_confirmed_ancestor_early_supporters S.C S.P
      _ A' _ _ (s + 1) C' L hb1 hRootsΦv
      (by rw [Nat.add_sub_cancel, pool_of_keepsVotes (expireLocks_keepsVotes _ _)]
          exact pool_vote_late S Sched x s v hDiv)
      hUpdate hSaved hLC'
  have hHalf' := hHalf hFast
  simp only [Nat.add_sub_cancel] at hSup hHalf'
  -- `expireLocks` keeps the pool and the stamps
  have hSup' : ∀ u ∈ Sup, EarlySupporterOf S.C (stateBefore x (supportCutoff S (s + 1)) v).A
      (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S) s L u := fun u hu =>
    (earlySupporterOf_of_keepsVotes (expireLocks_keepsVotes _ _) _ _ _ _ _).1 (hSup u hu)
  -- step 3: each member of `Sup` votes once for `L`'s chain in `w`'s pool before `t₃`: Lemma 63
  -- read on `w`'s pool, with `t_e := c`, `t_f := freeze`, `t_w := t₃`, `t_v := t₂`
  have hSupAt : ∀ u ∈ Sup, EarlySupporterAt (stateBefore x (supportCutoff S (s + 1)) v).A
      (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S) ((supportCutoff S s : ℕ) : Int)
      s L u := by
    intro u hu
    rw [supportCutoff_cast]
    exact hSup' u hu
  have hPer : ∀ u ∈ Sup, VotesOnceInPoolFor (stateBefore x (voteTime S (s + 1)) w).A
      (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) s L u :=
    GoldilocksCorrectness.Statements.Executions.supporters_vote_once_in_pool_at S Sched x GST s
      (supportCutoff S s) (viewFreeze S s) (voteTime S (s + 1)) (supportCutoff S (s + 1))
      (supportCutoff S (s + 1)) Sup L v w hDiv hMono
      (synchronyFromWakeUpTo_of_synchronyFromWake _ hSync)
      (catchUpOnWakeUpTo_of_catchUpOnWake _ hCatch) hRoots hParent hGST (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (fun t h1 h2 => hw t h1 (by omega))
      (fun t h1 h2 => hv t h1 (by omega)) hSupAt hFL (by omega)
  -- step 4: Lemma 5 on `w`'s revocation
  intro e he
  exact (GoldilocksCorrectness.Statements.Routines.lem5_revoke_locks_entries_compatible S.P _ A''
    _ _ (s + 1) L Sup hb1 hRootsΦw (by rw [Nat.add_sub_cancel]; exact fun u hu =>
      (votesOnceInPoolFor_of_keepsVotes (expireLocks_keepsVotes _ _) _ _ _ _).2 (hPer u hu))
    (by rw [Nat.add_sub_cancel]; exact hHalf') hRevoke e he).2

end GoldilocksCorrectness.Proofs.Executions
