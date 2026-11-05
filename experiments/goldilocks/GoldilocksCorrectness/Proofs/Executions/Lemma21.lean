module
public import GoldilocksCorrectness.Statements.Executions.ReadingPointStatements

@[expose] public section

/-!  The proof:

0. the times: the clock facts relating the start of slots `s`, `s + 1`, `s + 2`, the vote times,
   the support cutoffs and the view freeze of slot `s`;
1. `w`'s run and walk: Lemma 14 on `w`'s tick at `voteTime S (s + 1)`;
2. the spec's cutoffs as reading points: `CountedVotes`, the answer of `voter_block_tree` and
   `EarlySupporterOf` are `CountedVotesAt`, `VoterTreeAt` and `EarlySupporterAt` at the casts of
   `viewFreeze S s` and `supportCutoff S s` (`viewFreeze_cast`, `supportCutoff_cast`);
3. Lemma 64 with `t_e := supportCutoff S s`, `t_f := viewFreeze S s`, `t_w := voteTime S (s + 1)`,
   `t_v := supportCutoff S (s + 1)`, its inequalities by `omega`; its two windows are `w`'s and
   `v`'s, one delay from the support cutoff of slot `s` and from the vote time of slot `s + 1`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff viewFreeze)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ slotStart_eq slot_eq_of_mem supportCutoff_cast
  supportCutoff_eq viewFreeze_cast viewFreeze_eq voteTime_eq)

open GoldilocksCorrectness.Statements.Routines (EarlySupporterOf)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (CountedVotesAt VoterTreeAt expireLocks)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

-- An index `x[i]` into an execution, and `x[i][v]` into a configuration, has the valid-index
-- predicate `fun _ _ => True`; this rule, local to the file, proves it at once
--. No statement and no proof term
-- changes.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Lemma 21, the next slot's honest vote extends a block an honest validator finds eligible (G2
over executions). Its reading is on the statement page,
`GoldilocksCorrectness/Statements/Executions/EligibleBlockVoteStatements.lean`.

Roots name blocks until `supportCutoff S (s + 1)`: Lemma 64, which the proof calls with `t_w :=
voteTime S (s + 1)`, takes blocks as held up to one delay after `w`'s fork choice. -/
theorem lem21_goldfish_vote_extends_eligible_block (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s : ℕ) (Sup : Finset V) (B : Block V) (v w : V)
    (vote : GoldfishVote V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s + 1)))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hGST : GST ≤ supportCutoff S s)
    -- `v`, awake and honest from the vote time to the support cutoff of slot `s + 1`
    (hv : ∀ t : ℕ, voteTime S (s + 1) ≤ t → t ≤ supportCutoff S (s + 1) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    -- `w`, awake and honest from the support cutoff to the view freeze of slot `s`
    (hw : ∀ t : ℕ, supportCutoff S s ≤ t → t ≤ viewFreeze S s →
      w ∈ Sched.awake (t : Int) ∧ w ∉ Sched.adv (t : Int))
    -- `B` is eligible at `v`'s update of slot `s`: each member of `Sup` is an early supporter of
    -- `B`'s chain at `v`, and `v`'s late voters are fewer than twice `Sup`
    (hSup : ∀ u ∈ Sup, EarlySupporterOf S.C (stateBefore x (supportCutoff S (s + 1)) v).A
      (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S) s B u)
    (hEligible : voters_count ((stateBefore x (supportCutoff S (s + 1)) v).A.pool s) <
      2 * Sup.card)
    -- the finality-gadget conditions at `w`, on its state before `voteTime S (s + 1)`
    (hF2 : (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).fc_root.compatible B = true)
    (hF3 : (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).fc_root.AncestorEq B →
      ∀ tree : Finset (Block V),
        voter_block_tree S.C (stateBefore x (voteTime S (s + 1)) w).A
          (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) (s + 1) = .ok tree →
        ∃ W ∈ tree, W ∈ (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).viable_heads ∧
          B.AncestorEq W)
    -- no live lock entry `w`'s revocation leaves conflicts with `B`
    (hLocks : ∀ A' : ACState V,
      revoke_locks S.P (expireLocks (stateBefore x (voteTime S (s + 1)) w).A
        ((voteTime S (s + 1) : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
        ((voteTime S (s + 1) : ℕ) : Int) (s + 1) = .ok A' →
      ∀ e ∈ A'.lock_entries,
        is_live (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
          ((voteTime S (s + 1) : ℕ) : Int) e = true → e.B.compatible B = true)
    (hSend : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (s + 1)) ∧
      (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent) :
    ∃ H_w : Block V, vote.head = H_w.root ∧ B.AncestorEq H_w := by
  -- step 0: the times
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
  have hslot₃ : S.C.slot ((voteTime S (s + 1) : ℕ) : Int) = s + 1 :=
    slot_eq_of_mem S (by omega) (by omega)
  -- step 1: `w`'s run and walk (Lemma 14 on `w`'s tick)
  obtain ⟨i, hl, hm⟩ := hSend
  have hi : stepBefore x (voteTime S (s + 1)) = i := stepBefore_eq_of_lbl x hl
  obtain ⟨-, n', sent, hrun, hvote⟩ := tick_send_of_honestSendAt hl hm
  have hA : (tickInputState x i (voteTime S (s + 1)) w).A =
      (stateBefore x (voteTime S (s + 1)) w).A := by
    rw [(tickInputState_frame x i _ w).2.1]
    unfold stateBefore
    rw [hi]
  have hS : (tickInputState x i (voteTime S (s + 1)) w).S =
      (stateBefore x (voteTime S (s + 1)) w).S := by
    rw [(tickInputState_frame x i _ w).1]
    unfold stateBefore
    rw [hi]
  obtain ⟨-, -, -, -, A', votes, support_votes, vbt, H_w, hRevoke, hCounted, hvbt, hWalk, hhead,
      -⟩ :=
    GoldilocksCorrectness.Statements.Routines.lem14_tick_vote_walk S.C S.P S.X _ n' _ sent vote
      hrun hvote
  rw [hslot₃, hA, hS] at hRevoke hCounted hvbt
  rw [hslot₃, hS, Nat.add_sub_cancel] at hWalk
  -- step 2: the spec's cutoffs are the reading points, cast
  have hCountedAt : CountedVotesAt (stateBefore x (voteTime S (s + 1)) w).A
      (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) ((viewFreeze S s : ℕ) : Int) (s + 1)
      votes support_votes := by
    rw [viewFreeze_cast]
    exact hCounted
  have hvbtAt : ∀ B' : Block V, B' ∈ vbt ↔ VoterTreeAt (stateBefore x (voteTime S (s + 1)) w).A
      (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) ((viewFreeze S s : ℕ) : Int) (s + 1)
      B' := by
    intro B'
    rw [viewFreeze_cast]
    exact GoldilocksCorrectness.Statements.Routines.mem_voter_block_tree_iff_at S.C _ _ (s + 1)
      vbt hvbt B'
  have hSupAt : ∀ u ∈ Sup, EarlySupporterAt (stateBefore x (supportCutoff S (s + 1)) v).A
      (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S) ((supportCutoff S s : ℕ) : Int)
      s B u := by
    intro u hu
    rw [supportCutoff_cast]
    exact hSup u hu
  -- step 3: Lemma 64 at the spec's times
  refine ⟨H_w, hhead,
    GoldilocksCorrectness.Statements.Executions.lem64_goldfish_vote_extends_eligible_block_at S
      Sched x GST s (supportCutoff S s) (viewFreeze S s) (voteTime S (s + 1))
      (supportCutoff S (s + 1)) (supportCutoff S (s + 1)) Sup B v w A' votes support_votes vbt
      H_w hDiv hMono (synchronyFromWakeUpTo_of_synchronyFromWake _ hSync)
      (catchUpOnWakeUpTo_of_catchUpOnWake _ hCatch) hRoots hParent hGST (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun t h1 h2 => hw t h1 (by omega)) (fun t h1 h2 => hv t h1 (by omega)) hSupAt hEligible
      hCountedAt hvbtAt hWalk hF2
      (fun hR => hF3 hR vbt hvbt) (hLocks A' hRevoke) (by omega)⟩

end GoldilocksCorrectness.Proofs.Executions
