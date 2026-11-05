module
public import GoldilocksCorrectness.Statements.Routines.ConfirmationStatements
public import GoldilocksCorrectness.Proofs.Executions.Lemma21
public import GoldilocksCorrectness.Proofs.Executions.Lemma31

@[expose] public section

/-!
# Lemma 36a: a confirmed block is extended by the next slot's honest votes

The proof of `lem36a_confirmed_block_extended_by_next_honest_votes`, stated in
`GoldilocksCorrectness/Statements/Executions/EligibleBlockVoteStatements.lean`. Write
`t₂ := supportCutoff S (s + 1)`, the time of `v`'s update of slot `s + 1`. The route:

1. Lemma 36 at `L := C'` on `v`'s update gives a set `Sup` of early supporters of `C'` at `v`, with
   the validators holding a slot-`s` vote in the update's input pool fewer than twice `Sup`. Its
   hypothesis on the pool's stamps holds since every vote in the pool before `t₂` is stamped before
   `t₂` (`pool_vote_late`, through `voteStamp_lt_iff`).
2. The update's input is `v`'s AC state before `t₂` with its expired lock entries removed;
   `expireLocks` changes only the lock entries, so the pool and the stamps Lemma 36 speaks of are
   those of `v`'s AC state before `t₂`, which Lemma 21 reads.
3. Lemma 21 with `B := C'`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ voteTime supportCutoff viewFreeze)

open GoldilocksCorrectness.Statements.Routines (EarlySupporterOf)

open GoldilocksCorrectness.Proofs.Routines (earlySupporterOf_of_keepsVotes expireLocks_keepsVotes
  pool_of_keepsVotes)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn expireLocks)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **Lemma 36a, a confirmed block is extended by the next slot's honest votes.** The proof; the
audited statement is in `Statements/Executions/EligibleBlockVoteStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s`: the slot whose confirmation `v`'s update of slot `s + 1` saves;
- `C'`: the saved confirmation; `v`: the validator whose update saves it; `A'`: that update's
  answer; `w`: the voter of slot `s + 1`; `vote`: its Goldfish vote.

Roots name blocks until `supportCutoff S (s + 1)`: Lemma 21, which the proof calls, takes blocks
as held up to one delay after `w`'s vote time of slot `s + 1`. -/
theorem lem36a_confirmed_block_extended_by_next_honest_votes (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s : ℕ) (C' : Block V) (v w : V) (A' : ACState V)
    (vote : GoldfishVote V)
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
    (hSaved : A'.saved_confirmation s = some C')
    (hF2 : (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).fc_root.compatible C' = true)
    (hF3 : (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).fc_root.AncestorEq C' →
      ∀ tree : Finset (Block V),
        voter_block_tree S.C (stateBefore x (voteTime S (s + 1)) w).A
          (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) (s + 1) = .ok tree →
        ∃ W ∈ tree, W ∈ (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).viable_heads ∧
          C'.AncestorEq W)
    (hLocks : ∀ A'' : ACState V,
      revoke_locks S.P (expireLocks (stateBefore x (voteTime S (s + 1)) w).A
        ((voteTime S (s + 1) : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
        ((voteTime S (s + 1) : ℕ) : Int) (s + 1) = .ok A'' →
      ∀ e ∈ A''.lock_entries,
        is_live (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
          ((voteTime S (s + 1) : ℕ) : Int) e = true → e.B.compatible C' = true)
    (hSend : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (s + 1)) ∧
      (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent) :
    ∃ H_w : Block V, vote.head = H_w.root ∧ C'.AncestorEq H_w := by
  have hs1 : 1 ≤ s + 1 := Nat.le_add_left 1 s
  have hRootsΦv : RootsNameBlocksIn
      (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S).tree :=
    rootsNameBlocksIn_frame_of_exec_node S Sched x _ v
  -- step 1: Lemma 36 at `L := C'`
  obtain ⟨Sup, hSup, hElig, -⟩ :=
    GoldilocksCorrectness.Statements.Routines.lem36_confirmed_ancestor_early_supporters S.C S.P
      _ A' _ _ (s + 1) C' C' hs1 hRootsΦv
      (by rw [Nat.add_sub_cancel, pool_of_keepsVotes (expireLocks_keepsVotes _ _)]
          exact pool_vote_late S Sched x s v hDiv)
      hUpdate (by rw [Nat.add_sub_cancel]; exact hSaved) (ancestorEq_refl C')
  simp only [Nat.add_sub_cancel] at hSup hElig
  -- step 2: `expireLocks` keeps the pool and the stamps
  have hSup' : ∀ u ∈ Sup, EarlySupporterOf S.C (stateBefore x (supportCutoff S (s + 1)) v).A
      (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S) s C' u := fun u hu =>
    (earlySupporterOf_of_keepsVotes (expireLocks_keepsVotes _ _) _ _ _ _ _).1 (hSup u hu)
  have hElig' : voters_count ((stateBefore x (supportCutoff S (s + 1)) v).A.pool s) <
      2 * Sup.card := by
    rw [pool_of_keepsVotes (expireLocks_keepsVotes _ _)] at hElig; exact hElig
  -- step 3: Lemma 21
  exact GoldilocksCorrectness.Proofs.Executions.lem21_goldfish_vote_extends_eligible_block S Sched
    x GST s Sup C' v w vote hDiv hMono hSync hCatch hRoots hParent hGST hv hw hSup' hElig'
    hF2 hF3 hLocks hSend

end GoldilocksCorrectness.Proofs.Executions
