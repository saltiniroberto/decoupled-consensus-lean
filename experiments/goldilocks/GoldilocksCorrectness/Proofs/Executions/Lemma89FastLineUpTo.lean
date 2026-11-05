module
public import GoldilocksCorrectness.Proofs.Executions.Lemma89FastLine
public import GoldilocksCorrectness.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Proofs.Executions.Lemma81UpTo

@[expose] public section

/-!
# `Lemma89FastLine.lean` with the delivery premises up to a bound

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma89FastLine.lean` that name a
delivery premise, restated with `SynchronyFromWakeUpTo` and `CatchUpOnWakeUpTo` at a bound on the
deadlines. The bound of
each twin is the latest ordinary deadline `max t GST + Δ` of a send its proof reads, written in
the twin's own parameters.

* `lem36c_fast_ancestor_extended_held`

No `axiom`, no `native_decide`, no `sorry`. The landed page is imported, never edited.
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
open GoldilocksCorrectness.Statements.Routines (lem15_tick_updates_confirmation lem49_tick_attests
  RootsNameBlocksIn expireLocks)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ac_to_fg_source_mem
  ac_to_fg_source_fast tick_attest_awake awakeSince_of_record_awake create_attestation_cases)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- **A4, a confirmed block's ancestor is extended by the next slot's honest votes, the held
form.** The proof; the audited statement is in `Statements/Executions/Lemma89Statements.lean`.

The route: Lemma 36b's proof (`lem36b_confirmed_block_extended_held`), with Lemma 36 at the
ancestor `L` of the saved confirmation `C'` in place of `C'` itself, then Lemma 21 in the held form
at `L`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s`: the slot whose confirmation `v`'s update of slot `s + 1` saves;
- `C'`: the saved confirmation; `L`: `C'` or an ancestor of it; `v`: the validator whose update
  saves `C'`; `w`: the voter of slot `s + 1`; `A'`: the update's answer; `vote`: `w`'s Goldfish
  vote.

Roots name blocks until `supportCutoff S (s + 1)`: the proof reads Lemma 21 in the held form at
slot `s`, whose bound is that time.

Restated with the delivery premises up to `supportCutoff S (s + 1)`: Lemma 21b at slot `s` reads deliveries due by then (`lem21b_goldfish_vote_extends_eligible_block_held_upTo`). -/
theorem lem36c_fast_ancestor_extended_held_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s : ℕ) (C' L : Block V) (v w : V) (A' : ACState V)
    (vote : GoldfishVote V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S (s + 1)))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S (s + 1)))
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
    (hLC : L.AncestorEq C')
    (hF2 : (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).fc_root.compatible L = true)
    (hF3 : (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).fc_root.AncestorEq L →
      ∀ tree : Finset (Block V),
        voter_block_tree S.C (stateBefore x (voteTime S (s + 1)) w).A
          (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) (s + 1) = .ok tree →
        ∃ W ∈ tree, W ∈ (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).viable_heads ∧
          L.AncestorEq W)
    (hLocks : ∀ A'' : ACState V,
      revoke_locks S.P (expireLocks (stateBefore x (voteTime S (s + 1)) w).A
        ((voteTime S (s + 1) : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
        ((voteTime S (s + 1) : ℕ) : Int) (s + 1) = .ok A'' →
      ∀ e ∈ A''.lock_entries,
        is_live (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
          ((voteTime S (s + 1) : ℕ) : Int) e = true → e.B.compatible L = true)
    (hSend : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (s + 1)) ∧
      (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent) :
    ∃ H_w ∈ (stateBefore x (voteTime S (s + 1)) w).S.T,
      vote = GoldfishVote.mk w (s + 1) H_w.root ∧ L.AncestorEq H_w := by
  have hs1 : 1 ≤ s + 1 := Nat.le_add_left 1 s
  have hRootsΦv : RootsNameBlocksIn
      (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S).tree :=
    rootsNameBlocksIn_frame_of_exec_node S Sched x _ v
  -- Lemma 36 at `L`, an ancestor of `C'` or `C'` itself
  obtain ⟨Sup, hSup, hElig, -⟩ :=
    GoldilocksCorrectness.Statements.Routines.lem36_confirmed_ancestor_early_supporters S.C S.P
      _ A' _ _ (s + 1) C' L hs1 hRootsΦv
      (by rw [Nat.add_sub_cancel, pool_of_keepsVotes (expireLocks_keepsVotes _ _)]
          exact pool_vote_late S Sched x s v hDiv)
      hUpdate (by rw [Nat.add_sub_cancel]; exact hSaved) hLC
  simp only [Nat.add_sub_cancel] at hSup hElig
  -- `expireLocks` keeps the pool and the stamps
  have hSup' : ∀ u ∈ Sup, EarlySupporterOf S.C (stateBefore x (supportCutoff S (s + 1)) v).A
      (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S) s L u := fun u hu =>
    (earlySupporterOf_of_keepsVotes (expireLocks_keepsVotes _ _) _ _ _ _ _).1 (hSup u hu)
  have hElig' : voters_count ((stateBefore x (supportCutoff S (s + 1)) v).A.pool s) <
      2 * Sup.card := by
    rw [pool_of_keepsVotes (expireLocks_keepsVotes _ _)] at hElig; exact hElig
  -- Lemma 21, the held form, at `L`
  exact lem21b_goldfish_vote_extends_eligible_block_held_upTo S Sched x GST s Sup L v w vote hDiv
    hMono hSync hCatch hRoots hParent hGST hv hw hSup' hElig' hF2 hF3 hLocks hSend

end GoldilocksCorrectness.Proofs.Executions

