module
public import GoldilocksCorrectness.Statements.Executions.ReadingPointStatements
public import GoldilocksCorrectness.Statements.Executions.HonestChainAfterHealingDefs
public import GoldilocksCorrectness.Statements.Executions.SleepyStatements
public import GoldilocksCorrectness.Statements.Executions.HonestChainStatements
public import GoldilocksCorrectness.Statements.Executions.ConfirmationCompatibilityStatements
public import GoldilocksCorrectness.Statements.Executions.LockProvenanceStatements
public import GoldilocksCorrectness.Statements.Executions.WakeStatements
public import GoldilocksCorrectness.Statements.Routines.LockStatements
public import GoldilocksCorrectness.Proofs.Executions.Lemma21
public import GoldilocksCorrectness.Proofs.Executions.Lemma26
public import GoldilocksCorrectness.Proofs.Executions.Lemma33
public import GoldilocksCorrectness.Proofs.Executions.Lemma36a
public import GoldilocksCorrectness.Proofs.Executions.Lemma79
public import GoldilocksCorrectness.Proofs.Routines.Schedule

@[expose] public section

/-! This file proves:

- `lem21b_goldfish_vote_extends_eligible_block_held`, Lemma 21 keeping the walk's end held: the
  proof of Lemma 21 (`GoldilocksCorrectness/Proofs/Executions/Lemma21.lean`) with the two facts
  Lemma 26b's proof adds (`GoldilocksCorrectness/Proofs/Executions/Lemma26.lean`): the vote is
  `w`'s slot-`(s + 1)` vote for the walk's end `H_w` (Lemma 14's validator and slot), and `H_w`
  is a block of `w`'s tree (`ghost_mem_tree_or_eq`, `get_anchor_mem_T`);
- Lemma 36b, `lem36b_confirmed_block_extended_held`: Lemma 36a's proof
  (`GoldilocksCorrectness/Proofs/Executions/Lemma36a.lean`) ending in the held form;
- the kit: the windows of `honestActiveAt` and `updaterAt`, a member of slot `s + 1` outside
  `honestActiveAt S Sched s` slept before the duty window of slot `s + 1`
  (`mem_honestActiveAt_or_slept`), a revocation from a state with no live lock leaves none
  (`revoke_locks_empty_of_lockFree`), where a live lock comes from (`live_lock_entry_source`,
  `revoked_lock_source`: `live_locks_compatible_of_honestChainExtends`'s proof without its
  invariant), the lock invariant's step (`liveLocksOnFamilyAt_step`), the invariant restricted to
  a block holds for its ancestors (`honestChainExtends_of_ancestorEq`), the votes of the first
  clause as a function (`voters_of_votes_clause`), and the updaters' confirmations extend the chain
  family (`chainInvFor_updater_confirmation`, Lemma 78);
- the chain step `lem89s_chain_step`: clause 1 by Lemma 26b for a block
  of the family and by Lemma 36b for a new confirmation, clause 2 by `revoked_lock_source` with
  Lemma 32 and the lock invariant, clause 3 by Lemma 78;
- Lemma 81b, `lem81b_chain_step`, its instance after the healed slot; the lock invariant at the
  healed slot from `B₀`'s slot (`liveLocksOnFamilyAt_base`); Lemma 81,
  `lem81_confirmations_chain`, by induction on the slot; and `onHonestChain_compatible`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff viewFreeze
  dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_le_supportCutoff dutyWindowStart_mono
  dutyWindowStart_succ_le_slotStart duty_window_start_mono one_le_Δ slotStart_eq slotStart_mono
  slot_eq_of_mem supportCutoff_cast supportCutoff_eq supportCutoff_lt_of_lt supportCutoff_slot
  supportCutoff_succ_le viewFreeze_cast viewFreeze_eq voteTime_cast voteTime_eq voteTime_succ)

open GoldilocksCorrectness.Proofs.Routines (compatible_of_ancestorEq_both compatible_symm')
open GoldilocksCorrectness.Statements.Routines (EarlySupporterOf)

open GoldilocksCorrectness.Proofs.Routines (mem_fg_to_ac_tree)

open GoldilocksCorrectness.Proofs.Routines (get_anchor_mem_T)

open GoldilocksCorrectness.Proofs.Routines (slot_lt_of_ancestorEq_of_treeClosed)
open GoldilocksCorrectness.Statements.Routines (TreeClosed)

open GoldilocksCorrectness.Proofs.Routines (earlySupporterOf_of_keepsVotes expireLocks_keepsVotes
  pool_of_keepsVotes)

open GoldilocksCorrectness.Proofs.Routines (wake_eq)

open GoldilocksCorrectness.Proofs.Routines (goldfish_fork_choice_eq)

open GoldilocksCorrectness.Proofs.Routines (is_live_iff)

open GoldilocksCorrectness.Proofs.Routines (mem_viable_tree_iff)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (CountedVotesAt VoterTreeAt RootsNameBlocksIn
  expireLocks)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans ancestorEq_compatible
  compatible_iff compatible_of_ancestorEq_compatible mem_voter_block_tree_iff
  revoke_locks_entry_mem_tree voters_count_lt_of_committee_majority)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

-- An index `x[i]` into an execution, and `x[i][v]` into a configuration, has the valid-index
-- predicate `fun _ _ => True`; this rule, local to the file, proves it at once
--. No statement and no proof term
-- changes.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-! ## Lemma 36b -/

/-- **Lemma 21, the held form.** Lemma 21's hypotheses; the conclusion names the block: `vote` is
`w`'s slot-`(s + 1)` vote for a block `H_w` of `w`'s tree before the vote time of slot `s + 1`,
and `H_w` is `B` or a descendant of `B`.

Why: Lemma 21's proof, keeping the walk's end. Lemma 14 gives the vote's validator and slot (the
validator of the tick's input state is `w`, Lemma 11) and the walk; its end is a block of the
viable tree of `w`'s voter tree or the walk's start, the anchor, which is in `w`'s tree
(`get_anchor_mem_T`); Lemma 64 puts it on `B`'s chain.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s`: the slot of the eligibility;
- `Sup`: the early supporters; `B`: the eligible block; `v`: the validator finding it eligible;
  `w`: the voter of slot `s + 1`; `vote`: its Goldfish vote.

Roots name blocks until `supportCutoff S (s + 1)`: Lemma 64, which the proof calls with `t_w :=
voteTime S (s + 1)`, takes blocks as held up to one delay after `w`'s fork choice. -/
theorem lem21b_goldfish_vote_extends_eligible_block_held (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s : ℕ) (Sup : Finset V) (B : Block V) (v w : V)
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
    (hSup : ∀ u ∈ Sup, EarlySupporterOf S.C (stateBefore x (supportCutoff S (s + 1)) v).A
      (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S) s B u)
    (hEligible : voters_count ((stateBefore x (supportCutoff S (s + 1)) v).A.pool s) <
      2 * Sup.card)
    (hF2 : (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).fc_root.compatible B = true)
    (hF3 : (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).fc_root.AncestorEq B →
      ∀ tree : Finset (Block V),
        voter_block_tree S.C (stateBefore x (voteTime S (s + 1)) w).A
          (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) (s + 1) = .ok tree →
        ∃ W ∈ tree, W ∈ (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).viable_heads ∧
          B.AncestorEq W)
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
    ∃ H_w ∈ (stateBefore x (voteTime S (s + 1)) w).S.T,
      vote = GoldfishVote.mk w (s + 1) H_w.root ∧ B.AncestorEq H_w := by
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
  have hslot₃ : S.C.slot ((voteTime S (s + 1) : ℕ) : Int) = s + 1 :=
    slot_eq_of_mem S (by omega) (by omega)
  -- `w`'s run and walk (Lemma 14 on `w`'s tick)
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
  obtain ⟨-, hvi, hvs, -, A', votes, support_votes, vbt, H_w, hRevoke, hCounted, hvbt, hWalk,
      hhead, -⟩ :=
    GoldilocksCorrectness.Statements.Routines.lem14_tick_vote_walk S.C S.P S.X _ n' _ sent vote
      hrun hvote
  rw [hslot₃, hA, hS] at hRevoke hCounted hvbt
  rw [hslot₃, hS, Nat.add_sub_cancel] at hWalk
  -- the vote is `w`'s slot-`(s + 1)` vote for `H_w`
  have hvw : (tickInputState x i (voteTime S (s + 1)) w).v = w := by
    have h := (lem11_node_invariant S Sched x i w).2.1
    unfold tickInputState
    split <;> (try rw [wake_eq]) <;> exact h
  rw [hvw] at hvi
  rw [hslot₃] at hvs
  have hvote' : vote = GoldfishVote.mk w (s + 1) H_w.root := by
    rw [← hvi, ← hvs, ← hhead]
  -- the walk's end is a block `w` holds
  have hHwT : H_w ∈ (stateBefore x (voteTime S (s + 1)) w).S.T := by
    rcases GoldilocksCorrectness.Proofs.Routines.ghost_mem_tree_or_eq ((goldfish_fork_choice_eq ..).symm.trans hWalk) with h | h
    · rw [h]
      exact get_anchor_mem_T _ _ _
        (lem11_node_invariant S Sched x (stepBefore x (voteTime S (s + 1))) w).1.2.2.2.1
        (lem57_justification_cache_and_record S Sched x (stepBefore x (voteTime S (s + 1)))
          w).2.2.1
    · have h1 := ((mem_viable_tree_iff _ _ _).1 h).1
      have h2 := ((mem_voter_block_tree_iff S.C _ _ (s + 1) vbt hvbt H_w).1 h1).1
      exact ((mem_fg_to_ac_tree _ _).1 h2).1
  -- the spec's cutoffs are the reading points, cast
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
  -- Lemma 64 at the spec's times
  exact ⟨H_w, hHwT, hvote',
    GoldilocksCorrectness.Statements.Executions.lem64_goldfish_vote_extends_eligible_block_at S
      Sched x GST s (supportCutoff S s) (viewFreeze S s) (voteTime S (s + 1))
      (supportCutoff S (s + 1)) (supportCutoff S (s + 1)) Sup B v w A' votes support_votes vbt
      H_w hDiv hMono (synchronyFromWakeUpTo_of_synchronyFromWake _ hSync)
      (catchUpOnWakeUpTo_of_catchUpOnWake _ hCatch) hRoots hParent hGST (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (fun t h1 h2 => hw t h1 (by omega)) (fun t h1 h2 => hv t h1 (by omega)) hSupAt hEligible
      hCountedAt hvbtAt hWalk hF2
      (fun hR => hF3 hR vbt hvbt) (hLocks A' hRevoke) (by omega)⟩

/-- **Lemma 36b, a confirmed block is extended by the next slot's honest votes, the held form.**
The proof; the audited statement is in
`Statements/Executions/HonestChainAfterHealingStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s`: the slot whose confirmation `v`'s update of slot `s + 1` saves;
- `C'`: the saved confirmation; `v`: the validator whose update saves it; `A'`: that update's
  answer; `w`: the voter of slot `s + 1`; `vote`: its Goldfish vote.

Roots name blocks until `supportCutoff S (s + 1)`: Lemma 21b, which the proof calls, takes
blocks as held up to one delay after `w`'s vote time of slot `s + 1`. -/
theorem lem36b_confirmed_block_extended_held (S : Setup V) (Sched : Schedule V)
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
    ∃ H_w ∈ (stateBefore x (voteTime S (s + 1)) w).S.T,
      vote = GoldfishVote.mk w (s + 1) H_w.root ∧ C'.AncestorEq H_w := by
  have hs1 : 1 ≤ s + 1 := Nat.le_add_left 1 s
  have hRootsΦv : RootsNameBlocksIn
      (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S).tree :=
    rootsNameBlocksIn_frame_of_exec_node S Sched x _ v
  -- Lemma 36 at `L := C'`
  obtain ⟨Sup, hSup, hElig, -⟩ :=
    GoldilocksCorrectness.Statements.Routines.lem36_confirmed_ancestor_early_supporters S.C S.P
      _ A' _ _ (s + 1) C' C' hs1 hRootsΦv
      (by rw [Nat.add_sub_cancel, pool_of_keepsVotes (expireLocks_keepsVotes _ _)]
          exact pool_vote_late S Sched x s v hDiv)
      hUpdate (by rw [Nat.add_sub_cancel]; exact hSaved) (ancestorEq_refl C')
  simp only [Nat.add_sub_cancel] at hSup hElig
  -- `expireLocks` keeps the pool and the stamps
  have hSup' : ∀ u ∈ Sup, EarlySupporterOf S.C (stateBefore x (supportCutoff S (s + 1)) v).A
      (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S) s C' u := fun u hu =>
    (earlySupporterOf_of_keepsVotes (expireLocks_keepsVotes _ _) _ _ _ _ _).1 (hSup u hu)
  have hElig' : voters_count ((stateBefore x (supportCutoff S (s + 1)) v).A.pool s) <
      2 * Sup.card := by
    rw [pool_of_keepsVotes (expireLocks_keepsVotes _ _)] at hElig; exact hElig
  -- Lemma 21, the held form
  exact lem21b_goldfish_vote_extends_eligible_block_held S Sched x GST s Sup C' v w vote hDiv
    hMono hSync hCatch hRoots hParent hGST hv hw hSup' hElig' hF2 hF3 hLocks hSend

/-! ## Kit: the windows of the sets of a slot, and a member that joined during a slot -/

omit [RootOrder] in
/-- A validator of `honestActiveAt S Sched s` is awake and honest at every time from the duty
window's start of slot `s` to the support cutoff of slot `s + 1`.

The variables:
- `S`: the setup; `Sched`: the schedule; `s`: the slot; `u`: the validator. -/
theorem honestActiveAt_window (S : Setup V) (Sched : Schedule V) (s : ℕ) (u : V)
    (hMono : Sched.MonotoneCorruption) (hu : u ∈ honestActiveAt S Sched s) :
    ∀ t : ℕ, dutyWindowStart S s ≤ t → t ≤ supportCutoff S (s + 1) →
      u ∈ Sched.awake (t : Int) ∧ u ∉ Sched.adv (t : Int) := by
  unfold honestActiveAt activeAt at hu
  rw [Finset.mem_sdiff, mem_awakeThroughout_iff] at hu
  intro t h1 h2
  exact ⟨hu.1 t (by exact_mod_cast h1) (by exact_mod_cast h2),
    fun h => hu.2 (hMono _ _ (by exact_mod_cast h2) h)⟩

omit [RootOrder] in
/-- A validator of `updaterAt S Sched s` is awake and honest at every time from the duty window's
start of slot `s + 1` to the support cutoff of slot `s + 1`.

The variables:
- `S`: the setup; `Sched`: the schedule; `s`: the slot; `v`: the validator. -/
theorem updaterAt_window (S : Setup V) (Sched : Schedule V) (s : ℕ) (v : V)
    (hMono : Sched.MonotoneCorruption) (hv : v ∈ updaterAt S Sched s) :
    ∀ t : ℕ, dutyWindowStart S (s + 1) ≤ t → t ≤ supportCutoff S (s + 1) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int) := by
  unfold updaterAt at hv
  rw [Finset.mem_sdiff, mem_awakeThroughout_iff] at hv
  intro t h1 h2
  exact ⟨hv.1 t (by exact_mod_cast h1) (by exact_mod_cast h2),
    fun h => hv.2 (hMono _ _ (by exact_mod_cast h2) h)⟩

omit [RootOrder] in
/-- With permanent corruption, an honest active validator of slot `s + 1` is an updater of slot
`s`: the duty window of slot `s + 1` to the support cutoff of slot `s + 1` is inside its window,
and its honesty at the support cutoff of slot `s + 2` gives its honesty at that of slot `s + 1`.

The variables:
- `S`: the setup; `Sched`: the schedule; `s`: the slot. -/
theorem honestActiveAt_succ_subset_updaterAt (S : Setup V) (Sched : Schedule V) (s : ℕ)
    (hMono : Sched.MonotoneCorruption) :
    honestActiveAt S Sched (s + 1) ⊆ updaterAt S Sched s := by
  intro u hu
  have hw := honestActiveAt_window S Sched (s + 1) u hMono hu
  have hc := supportCutoff_succ_le S s
  have hd : dutyWindowStart S (s + 1) ≤ supportCutoff S (s + 1) :=
    dutyWindowStart_le_supportCutoff S (by omega)
  unfold updaterAt
  rw [Finset.mem_sdiff]
  exact ⟨mem_awakeThroughout_of_forall (fun t h1 h2 => (hw t h1 (le_trans h2 hc)).1),
    (hw _ hd hc).2⟩

omit [RootOrder] in
/-- With permanent corruption, an honest active validator of slot `s + 1` is an honest active
validator of slot `s`, or was asleep at some time from the duty window's start of slot `s` to
before the duty window's start of slot `s + 1`.

Why: awake through both windows and honest at the support cutoff of slot `s + 2`, hence at the
support cutoff of slot `s + 1`, it is in `honestActiveAt S Sched s`.

The variables:
- `S`: the setup; `Sched`: the schedule; `s`: the slot; `u`: the validator. -/
theorem mem_honestActiveAt_or_slept (S : Setup V) (Sched : Schedule V) (s : ℕ) (u : V)
    (hMono : Sched.MonotoneCorruption) (hu : u ∈ honestActiveAt S Sched (s + 1)) :
    u ∈ honestActiveAt S Sched s ∨ ∃ t : ℕ, dutyWindowStart S s ≤ t ∧
      t < dutyWindowStart S (s + 1) ∧ u ∉ Sched.awake (t : Int) := by
  by_cases h : ∃ t : ℕ, dutyWindowStart S s ≤ t ∧ t < dutyWindowStart S (s + 1) ∧
      u ∉ Sched.awake (t : Int)
  · exact Or.inr h
  · left
    have hw := honestActiveAt_window S Sched (s + 1) u hMono hu
    have hc := supportCutoff_succ_le S s
    have hd : dutyWindowStart S (s + 1) ≤ supportCutoff S (s + 1) :=
      dutyWindowStart_le_supportCutoff S (by omega)
    unfold honestActiveAt activeAt
    rw [Finset.mem_sdiff]
    refine ⟨mem_awakeThroughout_of_forall (fun t h1 h2 => ?_), (hw _ hd hc).2⟩
    by_cases ht : t < dutyWindowStart S (s + 1)
    · by_contra hn
      exact h ⟨t, h1, ht, hn⟩
    · exact (hw t (by omega) (le_trans h2 hc)).1

omit [Fintype V] [RootOrder] in
/-- When `Q` has fewer than twice the members of `Q ∩ H`, the members of `Q` outside `Q ∩ H` are
fewer than those of `Q ∩ H`.

The variables:
- `Q`: the committee; `H`: the set counted in it. -/
theorem committee_sdiff_lt (Q H : Finset V) (h : |Q| < 2 * |Q ∩ H|) :
    |Q \ (Q ∩ H)| < |Q ∩ H| := by
  have := Finset.card_sdiff_add_card_eq_card (Finset.inter_subset_left : Q ∩ H ⊆ Q)
  omega

/-! ## Kit: the locks -/

/-- **A revocation from a state with no live lock leaves no lock.** When no lock entry of `u`'s
state before `t` is live at `t`, the revocation of a slot `s ≥ 1` at `t`, run on that state's AC
state with its expired entries removed, answers a state with no lock entry.

Why: every entry the revocation leaves comes from an entry of its input live at `t` (Lemma 38),
and the input's entries are entries of `u`'s state.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `s`: the slot of the
  revocation; `u`: the validator; `A'`: the revocation's answer. -/
theorem revoke_locks_empty_of_lockFree (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (t s : ℕ) (u : V) (A' : ACState V) (hs : 1 ≤ s)
    (hfree : ∀ e ∈ (stateBefore x t u).A.lock_entries,
      is_live (fg_to_ac (stateBefore x t u).S) ((t : ℕ) : Int) e = false)
    (hRevoke : revoke_locks S.P (expireLocks (stateBefore x t u).A ((t : ℕ) : Int))
      (fg_to_ac (stateBefore x t u).S) ((t : ℕ) : Int) s = .ok A') :
    ∀ e ∈ A'.lock_entries, False := by
  intro e he
  obtain ⟨e₁, he₁, hlive, -⟩ :=
    GoldilocksCorrectness.Statements.Routines.lem38_revoke_locks_entries_moved S.P _ A' _ _ s hs
      hRevoke e he
  have he₁' := (Finset.mem_filter.1 he₁).1
  rw [hfree e₁ he₁'] at hlive
  exact Bool.false_ne_true hlive

/-- **The lock invariant holds vacuously at a validator with no live lock.** When no lock entry of
`u`'s state before the vote time of slot `s + 1` is live then, `LiveLocksOnFamilyAt S Sched x 𝓒 s
u` holds for every family `𝓒`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `𝓒`: the family; `s`: the slot;
  `u`: the validator. -/
theorem liveLocksOnFamilyAt_of_lockFree (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (𝓒 : Block V → Prop) (s : ℕ) (u : V)
    (hfree : ∀ e ∈ (stateBefore x (voteTime S (s + 1)) u).A.lock_entries,
      is_live (fg_to_ac (stateBefore x (voteTime S (s + 1)) u).S)
        ((voteTime S (s + 1) : ℕ) : Int) e = false) :
    LiveLocksOnFamilyAt S Sched x 𝓒 s u := by
  intro A' hRevoke e he _
  exact (revoke_locks_empty_of_lockFree S Sched x _ (s + 1) u A' (Nat.le_add_left 1 s) hfree
    hRevoke e he).elim

/-- **Where a live lock entry between the update of slot `s' + 1` and the revocation of slot
`s' + 2` comes from.** In an execution where every time is reached:
when `w` is awake and honest at every time from the duty window's start of slot `s' + 2` to `t`,
and `t` is after the support cutoff of slot `s' + 1` and at most the vote time of slot `s' + 2`,
then every lock entry `e` that `w` holds before `t` with its deadline after `t` is on `w`'s saved
confirmation of slot `s'` (right after the support cutoff of slot `s' + 1`) or an ancestor of it,
or on the block of an entry live at the vote time of slot `s' + 1` that `w`'s revocation of slot
`s' + 1` left, or an ancestor of it.

Why: `live_locks_compatible_of_honestChainExtends`'s proof without its invariant. The entry was
added by `w`'s update of a slot `s₁ + 1` with `s₁ ≤ s'` (Lemma 39). When `s₁ = s'`, its block is
the saved confirmation of slot `s'` or an ancestor of it (`update_state_of_lock_entry`). When
`s₁ < s'`, `w` was awake since that update, its tick at the vote time of slot `s' + 1` ran the
revocation (Lemma 13), and an entry with `e`'s deadline, on a descendant of `e`'s block, survived it
live (Lemma 39's trace).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s'`: the slot; `t`: the time;
  `w`: the validator. -/
theorem live_lock_entry_source (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s' t : ℕ) (w : V)
    (hDiv : TimeDiverges x.toTrace)
    (hHon : ∀ t'' : ℕ, dutyWindowStart S (s' + 2) ≤ t'' → t'' ≤ t →
      w ∈ Sched.awake (t'' : Int) ∧ w ∉ Sched.adv (t'' : Int))
    (ht1 : supportCutoff S (s' + 1) < t)
    (ht2 : t ≤ voteTime S (s' + 2)) :
    ∀ e ∈ (stateBefore x t w).A.lock_entries, ((t : ℕ) : Int) < e.d →
      (∃ C' : Block V,
        (stateBefore x (supportCutoff S (s' + 1) + 1) w).A.saved_confirmation s' = some C' ∧
        e.B.AncestorEq C') ∨
      ∃ A₃ : ACState V,
        revoke_locks S.P (expireLocks (stateBefore x (voteTime S (s' + 1)) w).A
          ((voteTime S (s' + 1) : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S (s' + 1)) w).S)
          ((voteTime S (s' + 1) : ℕ) : Int) (s' + 1) = .ok A₃ ∧
        ∃ e' ∈ A₃.lock_entries,
          is_live (fg_to_ac (stateBefore x (voteTime S (s' + 1)) w).S)
            ((voteTime S (s' + 1) : ℕ) : Int) e' = true ∧ e.B.AncestorEq e'.B := by
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
    exact Or.inr ⟨A₃, hRevoke, e', he', hlive', heB'⟩
  · -- `s₁ = s'`: the update of slot `s' + 1` saved `C'`
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
    exact Or.inl ⟨C', hsv, heC⟩

/-- **Where a lock entry the revocation of slot `s' + 2` leaves comes from.** In an execution where
every time is reached: when `w` is awake and honest at every time
from the duty window's start of slot `s' + 2` to the vote time of slot `s' + 2`, every lock entry
that `w`'s revocation of slot `s' + 2` at its vote time leaves is on `w`'s saved confirmation of
slot `s'` or an ancestor of it, or on the block of an entry live at the vote time of slot `s' + 1`
that `w`'s revocation of slot `s' + 1` left, or an ancestor of it.

Why: the entry is on the block of an entry of `w`'s state then, or an ancestor of it, whose
deadline is after that time (Lemma 38); `live_lock_entry_source` at the vote time of slot `s' + 2`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s'`: the slot; `w`: the
  validator. -/
theorem revoked_lock_source (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s' : ℕ) (w : V)
    (hDiv : TimeDiverges x.toTrace)
    (hHon : ∀ t : ℕ, dutyWindowStart S (s' + 2) ≤ t → t ≤ voteTime S (s' + 2) →
      w ∈ Sched.awake (t : Int) ∧ w ∉ Sched.adv (t : Int)) :
    ∀ A' : ACState V,
      revoke_locks S.P (expireLocks (stateBefore x (voteTime S (s' + 2)) w).A
        ((voteTime S (s' + 2) : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S (s' + 2)) w).S)
        ((voteTime S (s' + 2) : ℕ) : Int) (s' + 2) = .ok A' →
      ∀ e ∈ A'.lock_entries,
        (∃ C' : Block V,
          (stateBefore x (supportCutoff S (s' + 1) + 1) w).A.saved_confirmation s' = some C' ∧
          e.B.AncestorEq C') ∨
        ∃ A₃ : ACState V,
          revoke_locks S.P (expireLocks (stateBefore x (voteTime S (s' + 1)) w).A
            ((voteTime S (s' + 1) : ℕ) : Int))
            (fg_to_ac (stateBefore x (voteTime S (s' + 1)) w).S)
            ((voteTime S (s' + 1) : ℕ) : Int) (s' + 1) = .ok A₃ ∧
          ∃ e' ∈ A₃.lock_entries,
            is_live (fg_to_ac (stateBefore x (voteTime S (s' + 1)) w).S)
              ((voteTime S (s' + 1) : ℕ) : Int) e' = true ∧ e.B.AncestorEq e'.B := by
  intro A' hRevoke e' he'
  have hΔ := one_le_Δ S
  have hv₂ : voteTime S (s' + 2) = voteTime S (s' + 1) + 4 * Δ S := voteTime_succ S (s' + 1)
  have hc₁ : supportCutoff S (s' + 1) = voteTime S (s' + 1) + Δ S := supportCutoff_eq S (s' + 1)
  have hlt₂ : supportCutoff S (s' + 1) < voteTime S (s' + 2) := by omega
  obtain ⟨e, he, -, -, hB, -⟩ :=
    GoldilocksCorrectness.Statements.Routines.lem38_revoke_locks_entries_moved S.P _ A' _ _ (s' + 2)
      (Nat.le_add_left 1 (s' + 1)) hRevoke e' he'
  obtain ⟨heS, hlt⟩ := Finset.mem_filter.1 he
  rcases live_lock_entry_source S Sched x s' (voteTime S (s' + 2)) w hDiv hHon hlt₂ le_rfl
      e heS hlt with ⟨C', h1, h2⟩ | ⟨A₃, h1, e'', h2, h3, h4⟩
  · exact Or.inl ⟨C', h1, ancestorEq_trans hB h2⟩
  · exact Or.inr ⟨A₃, h1, e'', h2, h3, ancestorEq_trans hB h4⟩

/-- **The lock invariant's step, at one member.** In an execution where every time is reached:
when `u` is awake and honest at every time from the duty window's start
of slot `s' + 2` to the vote time of slot `s' + 2`, every block of `𝓒` is a block of `𝓒'`, `u`'s
saved confirmation of slot `s'` (right after the support cutoff of slot `s' + 1`) is a block of
`𝓒'`, and `LiveLocksOnFamilyAt S Sched x 𝓒 s' u` holds, then `LiveLocksOnFamilyAt S Sched x 𝓒'
(s' + 1) u` holds.

Why: an entry `u`'s revocation of slot `s' + 2` leaves is on `u`'s saved confirmation of slot `s'`
or an ancestor of it, or on an ancestor of the block of an entry live after the revocation of slot
`s' + 1` (`revoked_lock_source`), which the invariant at slot `s'` puts on the chain of a block of
`𝓒`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `𝓒`, `𝓒'`: the families before and
  after the step; `s'`: the slot; `u`: the validator. -/
theorem liveLocksOnFamilyAt_step (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (𝓒 𝓒' : Block V → Prop) (s' : ℕ) (u : V)
    (hDiv : TimeDiverges x.toTrace)
    (hHon : ∀ t : ℕ, dutyWindowStart S (s' + 2) ≤ t → t ≤ voteTime S (s' + 2) →
      u ∈ Sched.awake (t : Int) ∧ u ∉ Sched.adv (t : Int))
    (hSub : ∀ C : Block V, 𝓒 C → 𝓒' C)
    (hOwn : ∀ C : Block V,
      (stateBefore x (supportCutoff S (s' + 1) + 1) u).A.saved_confirmation s' = some C → 𝓒' C)
    (hPrev : LiveLocksOnFamilyAt S Sched x 𝓒 s' u) :
    LiveLocksOnFamilyAt S Sched x 𝓒' (s' + 1) u := by
  intro A' hRevoke e he _
  rcases revoked_lock_source S Sched x s' u hDiv hHon A' hRevoke e he with
      ⟨C, hC, heC⟩ | ⟨A₃, hR₃, e', he', hl', hee'⟩
  · exact ⟨C, hOwn C hC, heC⟩
  · obtain ⟨D, hD, he'D⟩ := hPrev A₃ hR₃ e' he' hl'
    exact ⟨D, hSub D hD, ancestorEq_trans hee' he'D⟩

/-- **The invariant restricted to a block holds for its ancestors.** When `HonestChainExtends S
Sched x Hon B s'` holds and `C` is `B` or an ancestor of `B`, `HonestChainExtends S Sched x Hon C
s'` holds.

Why: a descendant of `B` is a descendant of `C`; a block compatible with `B` is compatible with
`C` (`compatible_of_ancestorEq_compatible`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `Hon`: the members; `B`, `C`: the
  blocks; `s'`: the slot. -/
theorem honestChainExtends_of_ancestorEq (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (Hon : Finset V) (B C : Block V) (s' : ℕ)
    (hCB : C.AncestorEq B) (h : HonestChainExtends S Sched x Hon B s') :
    HonestChainExtends S Sched x Hon C s' := by
  refine ⟨fun u hu vote hs => ?_, fun w hw A' hR e he hl => ?_, fun v hv C' hC' => ?_⟩
  · obtain ⟨H, hH, hvt, hBH⟩ := h.1 u hu vote hs
    exact ⟨H, hH, hvt, ancestorEq_trans hCB hBH⟩
  · exact compatible_symm'
      (compatible_of_ancestorEq_compatible hCB (compatible_symm' (h.2.1 w hw A' hR e he hl)))
  · exact ancestorEq_trans hCB (h.2.2 v hv C' hC')

/-! ## Kit: the honest voters and the updaters -/

omit [RootOrder] in
/-- **Committee sleepiness gives the committee majority.** With `CommitteeSleepiness` from
`anchor` and slot `s + 1` starting at or after `anchor`, the committee of slot `s` has fewer than
twice the members it shares with `honestActiveAt S Sched s`. Lemma 88's first conclusion, without
its validator and time.

The variables:
- `S`: the setup; `Sched`: the schedule; `anchor`: the time from which committee sleepiness
  holds; `s`: the slot. -/
theorem committee_majority_of_sleepiness (S : Setup V) (Sched : Schedule V) (anchor s : ℕ)
    (hSleepK : CommitteeSleepiness S Sched anchor) (hs : anchor ≤ slotStart S (s + 1)) :
    |S.P.committee s| < 2 * |S.P.committee s ∩ honestActiveAt S Sched s| := by
  have hK := hSleepK (s + 1) (by omega) hs
  rw [Nat.add_sub_cancel, Finset.inter_comm] at hK
  have h1 := Finset.card_sdiff_add_card_inter (S.P.committee s) (honestActiveAt S Sched s)
  omega

/-- **The votes of the first clause, as a function.** When every member of `Hs` is an honest
active validator of slot `s` in its committee, and the slot-`s` vote of every member is its vote
for a block it holds that is `C` or a descendant of `C`, then some `H : V → Block V` names, for
every member `u`, the block of a slot-`s` vote `u` put on the wire at its tick at the vote time of
slot `s`, a block `u` holds then that is `C` or a descendant of `C`.

Why: every member votes (`honest_active_votes`), and the clause names its block; `choose`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the slot; `Hs`: the voters;
  `C`: the block. -/
theorem voters_of_votes_clause (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s : ℕ) (Hs : Finset V) (C : Block V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hHs : ∀ u ∈ Hs, u ∈ honestActiveAt S Sched s ∧ u ∈ S.P.committee s)
    (hC1 : ∀ u ∈ Hs, ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x[i + 1].sent - x[i].sent) →
      ∃ H_u ∈ (stateBefore x (voteTime S s) u).S.T,
        vote = GoldfishVote.mk u s H_u.root ∧ C.AncestorEq H_u) :
    ∃ H : V → Block V, ∀ u ∈ Hs,
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      H u ∈ (stateBefore x (voteTime S s) u).S.T ∧ C.AncestorEq (H u) := by
  have hvote : ∀ u ∈ Hs, ∃ H_u : Block V,
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s H_u.root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      H_u ∈ (stateBefore x (voteTime S s) u).S.T ∧ C.AncestorEq H_u := by
    intro u hu
    obtain ⟨i, vote, hl, -, -, hsent⟩ :=
      GoldilocksCorrectness.Proofs.Executions.honest_active_votes S Sched x s u hDiv hMono
        (hHs u hu).1 (hHs u hu).2
    obtain ⟨H_u, hHT, hvt, hBH⟩ := hC1 u hu vote ⟨i, hl, hsent⟩
    subst hvt
    exact ⟨H_u, ⟨i, hl, hsent⟩, hHT, hBH⟩
  choose H hH using hvote
  refine ⟨fun u => if h : u ∈ Hs then H u h else C, fun u hu => ?_⟩
  simp only [dif_pos hu]
  exact hH u hu

/-- **The updaters' confirmations extend the chain family.** In an execution where every time is
reached, corruption is permanent, blocks and Goldfish votes are delivered within `Δ` after `GST`,
a root names one block among what honest validators hold, a block
reaches a validator only once it holds the parent, and nobody votes in an honest validator's name:
if `GST` is at most the vote time of slot `s`; `Hon` is a set of honest active validators of slot
`s` with more than half of the committee of slot `s`; `ChainInvFor S Sched x Hon 𝓒 s` holds; `v` is
an updater of slot `s`; and `v`'s finalized block before the support cutoff of slot `s + 1` is
compatible with every block of `𝓒` — then every block of `𝓒` is an ancestor of, or equal to, the
confirmation of slot `s` that `v` holds right after that cutoff.

Why: Lemma 78 at `v`, with the honest voters `S.P.committee s ∩ Hon`, each voting for a block it
holds on the block's chain (the first clause of the invariant), and the voters of `v`'s pool from
the committee (the node invariant).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s`: the slot; `Hon`: the voters; `𝓒`: the family; `v`: the updater.

Roots name blocks until `supportCutoff S s`: Lemma 78, which the proof calls at slot `s`, takes
blocks as held up to the support cutoff of slot `s`. -/
theorem chainInvFor_updater_confirmation (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s : ℕ) (Hon : Finset V) (𝓒 : Block V → Prop) (v : V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S s))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    (hGST : GST ≤ voteTime S s)
    (hHon : Hon ⊆ honestActiveAt S Sched s)
    (hCommittee : |S.P.committee s| < 2 * |S.P.committee s ∩ Hon|)
    (hInv : ChainInvFor S Sched x Hon 𝓒 s)
    (hv : v ∈ updaterAt S Sched s)
    (hF : ∀ C : Block V, 𝓒 C →
      (stateBefore x (supportCutoff S (s + 1)) v).S.F.compatible C = true) :
    ∀ C : Block V, 𝓒 C → ∀ C' : Block V,
      (stateBefore x (supportCutoff S (s + 1) + 1) v).A.saved_confirmation s = some C' →
      C.AncestorEq C' := by
  intro C hC
  have hdc : dutyWindowStart S s ≤ supportCutoff S (s + 1) :=
    dutyWindowStart_le_supportCutoff S (by omega)
  obtain ⟨H, hH⟩ := voters_of_votes_clause S Sched x s (S.P.committee s ∩ Hon) C hDiv hMono
    (fun u hu => ⟨hHon (Finset.mem_inter.1 hu).2, (Finset.mem_inter.1 hu).1⟩)
    (fun u hu => (hInv C hC).1 u (Finset.mem_inter.1 hu).2)
  exact GoldilocksCorrectness.Statements.Executions.lem78_update_confirmation_extends_voter_majority_chain
    S Sched x GST s (S.P.committee s ∩ Hon) H C v hDiv hMono hSync hCatch hRoots hParent
    hOwner hGST
    (fun u hu => ⟨(Finset.mem_inter.1 hu).1,
      (honestActiveAt_window S Sched s u hMono (hHon (Finset.mem_inter.1 hu).2)
        (supportCutoff S (s + 1)) hdc le_rfl).2, (hH u hu).1, (hH u hu).2.1, (hH u hu).2.2⟩)
    (voters_count_lt_of_committee_majority (pool_committee_of_stateBefore S Sched x _ v s)
      (committee_sdiff_lt _ _ hCommittee))
    (updaterAt_window S Sched s v hMono hv) (hF C hC)

/-! ## The chain step -/

/-- **The chain step.** The proof; the audited statement is in
`Statements/Executions/HonestChainAfterHealingStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s'`: the slot of the step;
- `Hon`: the voters of slot `s'`; `Hon'`: the members of slot `s' + 1`; `Upd`: the updaters whose
  confirmations of slot `s'` join the family; `𝓒`: the family.

Roots name blocks until `supportCutoff S (s' + 1)`: Lemmas 36b, 32 and 78, which the proof calls
at the slots `s'` and `s' + 1`, take blocks as held up to the support cutoff of slot `s' + 1`;
Lemma 26b reads earlier. -/
theorem lem89s_chain_step (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s' : ℕ) (Hon Hon' Upd : Finset V)
    (𝓒 : Block V → Prop)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s' + 1)))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    (hGST : GST ≤ voteTime S s')
    (hHon : Hon ⊆ honestActiveAt S Sched s')
    (hHon' : Hon' ⊆ honestActiveAt S Sched (s' + 1))
    (hUpd : Upd ⊆ updaterAt S Sched s')
    (hHonUpd : Hon' ⊆ Upd)
    (hCommittee : |S.P.committee s'| < 2 * |S.P.committee s' ∩ Hon|)
    (hCommittee' : |S.P.committee (s' + 1)| < 2 * |S.P.committee (s' + 1) ∩ Hon'|)
    (hInv : ChainInvFor S Sched x Hon 𝓒 s')
    (hNew : ∀ u ∈ Hon', u ∈ Hon ∨
      ∀ e ∈ (stateBefore x (voteTime S (s' + 1)) u).A.lock_entries,
        is_live (fg_to_ac (stateBefore x (voteTime S (s' + 1)) u).S)
          ((voteTime S (s' + 1) : ℕ) : Int) e = false)
    (hLocks : ∀ u ∈ Hon, LiveLocksOnFamilyAt S Sched x 𝓒 s' u)
    (hConfExt : ∀ C : Block V, 𝓒 C → ∀ v ∈ Upd, ∀ C' : Block V,
      (stateBefore x (supportCutoff S (s' + 1) + 1) v).A.saved_confirmation s' = some C' →
      C.AncestorEq C')
    (hStep : ∀ C : Block V, (𝓒 C ∨ ∃ v ∈ Upd,
        (stateBefore x (supportCutoff S (s' + 1) + 1) v).A.saved_confirmation s' = some C) →
      ∀ w ∈ Hon', StepFrameAt S Sched x C s' w) :
    ChainInvFor S Sched x Hon' (fun C => 𝓒 C ∨ ∃ v ∈ Upd, ∃ C' : Block V,
      (stateBefore x (supportCutoff S (s' + 1) + 1) v).A.saved_confirmation s' = some C' ∧
      C.AncestorEq C') (s' + 1) := by
  -- the blocks of the family and the new confirmations themselves; their ancestors follow
  suffices hcore : ∀ B : Block V, (𝓒 B ∨ ∃ v ∈ Upd,
      (stateBefore x (supportCutoff S (s' + 1) + 1) v).A.saved_confirmation s' = some B) →
      HonestChainExtends S Sched x Hon' B (s' + 1) by
    rintro B (hB | ⟨v, hv, C', hsv, hBC'⟩)
    · exact hcore B (Or.inl hB)
    · exact honestChainExtends_of_ancestorEq S Sched x Hon' C' B (s' + 1) hBC'
        (hcore C' (Or.inr ⟨v, hv, hsv⟩))
  intro B hB0
  have hB : 𝓒 B ∨ ∃ v ∈ Upd, ∃ C' : Block V,
      (stateBefore x (supportCutoff S (s' + 1) + 1) v).A.saved_confirmation s' = some C' ∧
      B.AncestorEq C' :=
    hB0.imp id (fun ⟨v, hv, hsv⟩ => ⟨v, hv, B, hsv, ancestorEq_refl B⟩)
  -- the times
  have hΔ := one_le_Δ S
  have hdw0 : dutyWindowStart S s' ≤ dutyWindowStart S (s' + 1) :=
    dutyWindowStart_mono S (Nat.le_succ s')
  have hdw1 : dutyWindowStart S (s' + 1) ≤ slotStart S s' := dutyWindowStart_succ_le_slotStart S s'
  have hdw12 : dutyWindowStart S (s' + 1) ≤ dutyWindowStart S (s' + 2) :=
    dutyWindowStart_mono S (by omega)
  have hv₁ : voteTime S s' = slotStart S s' + Δ S := voteTime_eq S s'
  have hc₁ : supportCutoff S s' = voteTime S s' + Δ S := supportCutoff_eq S s'
  have hv₂ : voteTime S (s' + 1) = voteTime S s' + 4 * Δ S := voteTime_succ S s'
  have hc₂ : supportCutoff S (s' + 1) = voteTime S (s' + 1) + Δ S := supportCutoff_eq S (s' + 1)
  have hv₃ : voteTime S (s' + 2) = voteTime S (s' + 1) + 4 * Δ S := voteTime_succ S (s' + 1)
  have hc₃ : supportCutoff S (s' + 2) = voteTime S (s' + 2) + Δ S := supportCutoff_eq S (s' + 2)
  have hfr : viewFreeze S s' = slotStart S s' + 3 * Δ S := viewFreeze_eq S s'
  -- the windows
  have hHonW : ∀ u ∈ Hon, ∀ t : ℕ, dutyWindowStart S s' ≤ t → t ≤ supportCutoff S (s' + 1) →
      u ∈ Sched.awake (t : Int) ∧ u ∉ Sched.adv (t : Int) :=
    fun u hu => honestActiveAt_window S Sched s' u hMono (hHon hu)
  have hHon'W : ∀ u ∈ Hon', ∀ t : ℕ, dutyWindowStart S (s' + 1) ≤ t →
      t ≤ supportCutoff S (s' + 2) → u ∈ Sched.awake (t : Int) ∧ u ∉ Sched.adv (t : Int) :=
    fun u hu => honestActiveAt_window S Sched (s' + 1) u hMono (hHon' hu)
  have hUpdW : ∀ v ∈ Upd, ∀ t : ℕ, dutyWindowStart S (s' + 1) ≤ t →
      t ≤ supportCutoff S (s' + 1) → v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int) :=
    fun v hv => updaterAt_window S Sched s' v hMono (hUpd hv)
  -- the live locks of a member after its revocation of slot `s' + 1`
  have hLk : ∀ u ∈ Hon', ∀ A₃ : ACState V,
      revoke_locks S.P (expireLocks (stateBefore x (voteTime S (s' + 1)) u).A
        ((voteTime S (s' + 1) : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S (s' + 1)) u).S)
        ((voteTime S (s' + 1) : ℕ) : Int) (s' + 1) = .ok A₃ →
      ∀ e ∈ A₃.lock_entries,
        is_live (fg_to_ac (stateBefore x (voteTime S (s' + 1)) u).S)
          ((voteTime S (s' + 1) : ℕ) : Int) e = true →
        (∀ C : Block V, 𝓒 C → e.B.compatible C = true) ∧ ∃ D : Block V, 𝓒 D ∧ e.B.AncestorEq D := by
    intro u hu A₃ hR e he hl
    rcases hNew u hu with hu0 | hfree
    · exact ⟨fun C hC => (hInv C hC).2.1 u hu0 A₃ hR e he hl, hLocks u hu0 A₃ hR e he hl⟩
    · exact (revoke_locks_empty_of_lockFree S Sched x _ (s' + 1) u A₃ (Nat.le_add_left 1 s')
        hfree hR e he).elim
  -- the first clause at slot `s' + 1`
  have hClause1 : ∀ u ∈ Hon', ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (s' + 1)) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x[i + 1].sent - x[i].sent) →
      ∃ H_u ∈ (stateBefore x (voteTime S (s' + 1)) u).S.T,
        vote = GoldfishVote.mk u (s' + 1) H_u.root ∧ B.AncestorEq H_u := by
    intro u hu vote hSend
    have huW := hHon'W u hu
    have hF := hStep B hB0 u hu
    rcases hB with hBold | ⟨v, hv, C', hsv, hBC'⟩
    · -- a block of the family: Lemma 26b over the voters of slot `s'`
      obtain ⟨H, hH⟩ := voters_of_votes_clause S Sched x s' (S.P.committee s' ∩ Hon) B hDiv hMono
        (fun u' hu' => ⟨hHon (Finset.mem_inter.1 hu').2, (Finset.mem_inter.1 hu').1⟩)
        (fun u' hu' => (hInv B hBold).1 u' (Finset.mem_inter.1 hu').2)
      exact GoldilocksCorrectness.Statements.Executions.lem26b_goldfish_vote_extends_voter_majority_block_held
        S Sched x GST s' (S.P.committee s' ∩ Hon) H B u vote hDiv hMono hSync hCatch
        (hRoots.mono (by omega)) hParent hOwner hGST
        (fun u' hu' => ⟨(Finset.mem_inter.1 hu').1,
          (hHonW u' (Finset.mem_inter.1 hu').2 (voteTime S (s' + 1)) (by omega) (by omega)).2,
          (hH u' hu').1, (hH u' hu').2.1, (hH u' hu').2.2⟩)
        (fun votes sv hC => voters_count_lt_of_committee_majority
          (countedVotes_committee S Sched x _ s' u votes sv hC) (committee_sdiff_lt _ _ hCommittee))
        (fun t h1 h2 => huW t (by omega) (by omega)) hF.1 hF.2.1
        (fun A₃ hR e he hl => (hLk u hu A₃ hR e he hl).1 B hBold) hSend
    · -- a block of a new confirmation: Lemma 36b at that confirmation
      have hvW := hUpdW v hv
      have hdc : dutyWindowStart S (s' + 1) < supportCutoff S (s' + 1) := by omega
      have hvc := hvW (supportCutoff S (s' + 1)) (le_of_lt hdc) le_rfl
      have hAw := GoldilocksCorrectness.Statements.Executions.awakeSince_le_dutyWindowStart_b S
        Sched x (s' + 1) (supportCutoff S (s' + 1)) v hDiv hMono hdc
        (fun t h1 h2 => (hvW t h1 h2).1) hvc.2
      obtain ⟨A'', hUp, hsave, -, -, -⟩ :=
        GoldilocksCorrectness.Statements.Executions.update_state_of_duty S Sched x s' v hDiv
          hvc hAw
      have hSaved : A''.saved_confirmation s' = some C' := by
        rw [← hsave]
        exact hsv
      have hFC' := hStep C' (Or.inr ⟨v, hv, hsv⟩) u hu
      obtain ⟨H_u, hHT, hvt, hCH⟩ := lem36b_confirmed_block_extended_held S Sched x GST s' C' v u
        A'' vote hDiv hMono hSync hCatch hRoots hParent (by omega)
        (fun t h1 h2 => hvW t (by omega) h2) (fun t h1 h2 => huW t (by omega) (by omega)) hUp
        hSaved hFC'.1 hFC'.2.1
        (fun A₃ hR e he hl => by
          obtain ⟨D, hD, heD⟩ := (hLk u hu A₃ hR e he hl).2
          exact (compatible_iff _ _).2 (Or.inl (ancestorEq_trans heD (hConfExt D hD v hv C' hsv))))
        hSend
      exact ⟨H_u, hHT, hvt, ancestorEq_trans hBC' hCH⟩
  -- the second clause at slot `s' + 1`
  have hrefl : ∀ X : Block V, X.compatible X = true :=
    fun X => (compatible_iff _ _).2 (Or.inl (ancestorEq_refl X))
  have hClause2 : ∀ w ∈ Hon', ∀ A' : ACState V,
      revoke_locks S.P (expireLocks (stateBefore x (voteTime S (s' + 2)) w).A
        ((voteTime S (s' + 2) : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S (s' + 2)) w).S)
        ((voteTime S (s' + 2) : ℕ) : Int) (s' + 2) = .ok A' →
      ∀ e ∈ A'.lock_entries,
        is_live (fg_to_ac (stateBefore x (voteTime S (s' + 2)) w).S)
          ((voteTime S (s' + 2) : ℕ) : Int) e = true → e.B.compatible B = true := by
    intro w hw A' hR e he _
    have hwW := hHon'W w hw
    rcases revoked_lock_source S Sched x s' w hDiv (fun t h1 h2 => hwW t (le_trans (dutyWindowStart_mono S (by omega)) h1) (by omega)) A'
        hR e he with ⟨Cw, hCw, heC⟩ | ⟨A₃, hR₃, e', he', hl', hee'⟩
    · rcases hB with hBold | ⟨v, hv, C', hsv, hBC'⟩
      · exact compatible_of_ancestorEq_both heC (hConfExt B hBold w (hHonUpd hw) Cw hCw)
          (hrefl Cw)
      · have h32 := GoldilocksCorrectness.Statements.Executions.lem32_saved_confirmations_compatible_state
          S Sched x GST s' w v Cw C' hDiv hMono hSync hCatch hRoots (by omega)
          (hUpdW w (hHonUpd hw)) (hUpdW v hv) hCw hsv
        exact compatible_of_ancestorEq_both heC hBC' h32
    · obtain ⟨hcomp, D, hD, he'D⟩ := hLk w hw A₃ hR₃ e' he' hl'
      rcases hB with hBold | ⟨v, hv, C', hsv, hBC'⟩
      · exact compatible_of_ancestorEq_compatible hee' (hcomp B hBold)
      · exact compatible_of_ancestorEq_both
          (ancestorEq_trans hee' (ancestorEq_trans he'D (hConfExt D hD v hv C' hsv))) hBC'
          (hrefl C')
  -- the third clause at slot `s' + 1`
  have hClause3 : ∀ v ∈ Hon', ∀ C' : Block V,
      (stateBefore x (supportCutoff S (s' + 2) + 1) v).A.saved_confirmation (s' + 1) = some C' →
      B.AncestorEq C' := by
    intro v hv
    obtain ⟨H, hH⟩ := voters_of_votes_clause S Sched x (s' + 1) (S.P.committee (s' + 1) ∩ Hon') B
      hDiv hMono
      (fun u hu => ⟨hHon' (Finset.mem_inter.1 hu).2, (Finset.mem_inter.1 hu).1⟩)
      (fun u hu => hClause1 u (Finset.mem_inter.1 hu).2)
    exact GoldilocksCorrectness.Statements.Executions.lem78_update_confirmation_extends_voter_majority_chain
      S Sched x GST (s' + 1) (S.P.committee (s' + 1) ∩ Hon') H B v hDiv hMono hSync hCatch
      hRoots hParent hOwner (by omega)
      (fun u hu => ⟨(Finset.mem_inter.1 hu).1,
        (hHon'W u (Finset.mem_inter.1 hu).2 (supportCutoff S (s' + 2)) (by omega) le_rfl).2,
        (hH u hu).1, (hH u hu).2.1, (hH u hu).2.2⟩)
      (voters_count_lt_of_committee_majority (pool_committee_of_stateBefore S Sched x _ v (s' + 1))
        (committee_sdiff_lt _ _ hCommittee'))
      (fun t h1 h2 => hHon'W v hv t (le_trans hdw12 h1) h2) (hStep B hB0 v hv).2.2
  exact ⟨hClause1, hClause2, hClause3⟩

/-! ## Lemma 81b and Lemma 81 -/

/-- **Lemma 81b, the chain step after the healed slot.** The proof; the audited statement is in
`Statements/Executions/HonestChainAfterHealingStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the first slot of the chain; `s`: the slot of the step;
  `anchor`: the time from which committee sleepiness holds.

Roots name blocks until `supportCutoff S (s + 1)`: the chain step, which the proof calls at slot
`s`, takes blocks as held up to the support cutoff of slot `s + 1`. -/
theorem lem81b_chain_step (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ s anchor : ℕ)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s + 1)))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    (hGST : GST ≤ voteTime S s)
    (hs₀ : s₀ ≤ s)
    (hSleepK : CommitteeSleepiness S Sched anchor)
    (hAnchor : anchor ≤ slotStart S (s + 1))
    (hInv : ChainInvFor S Sched x (honestActiveAt S Sched s) (OnHonestChainBefore S Sched x s₀ s) s)
    (hLocks : ∀ u ∈ honestActiveAt S Sched s,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ s) s u)
    (hVoterFrame : ∀ w ∈ honestActiveAt S Sched (s + 1),
      VoterFrameOnChainAt S Sched x s₀ (s + 1) w)
    (hUpdaterFrame : ∀ v ∈ updaterAt S Sched s, UpdaterFinalizedOnChainAt S Sched x s₀ s v)
    (hUpdaterFrame' : ∀ w ∈ honestActiveAt S Sched (s + 1),
      UpdaterFinalizedOnChainAt S Sched x s₀ (s + 1) w) :
    ChainInvFor S Sched x (honestActiveAt S Sched (s + 1))
      (OnHonestChainBefore S Sched x s₀ (s + 1)) (s + 1) := by
  have hcs : supportCutoff S s ≤ supportCutoff S (s + 1) := by
    have := supportCutoff_eq S s
    have := supportCutoff_eq S (s + 1)
    have := voteTime_succ S s
    omega
  have hCom := committee_majority_of_sleepiness S Sched anchor s hSleepK hAnchor
  have hCom' := committee_majority_of_sleepiness S Sched anchor (s + 1) hSleepK
    (le_trans hAnchor (slotStart_mono S (Nat.le_succ (s + 1))))
  have hstep := lem89s_chain_step S Sched x GST s (honestActiveAt S Sched s)
    (honestActiveAt S Sched (s + 1)) (updaterAt S Sched s) (OnHonestChainBefore S Sched x s₀ s)
    hDiv hMono hSync hCatch hRoots hParent hOwner hGST (subset_refl _) (subset_refl _)
    (subset_refl _) (honestActiveAt_succ_subset_updaterAt S Sched s hMono) hCom hCom' hInv
    (fun u hu => (mem_honestActiveAt_or_slept S Sched s u hMono hu).imp id
      (fun hsl => GoldilocksCorrectness.Statements.Executions.lock_free_after_wake S Sched x s u
        hDiv hMono hsl))
    hLocks
    (fun C hC v hv => chainInvFor_updater_confirmation S Sched x GST s (honestActiveAt S Sched s)
      (OnHonestChainBefore S Sched x s₀ s) v hDiv hMono hSync hCatch
      (hRoots.mono hcs) hParent hOwner hGST (subset_refl _)
      hCom hInv hv (fun D hD => hUpdaterFrame v hv D hD) C hC)
    (fun C hC w hw => by
      have hC' : OnHonestChainBefore S Sched x s₀ (s + 1) C := by
        rcases hC with ⟨s', hs', hAt⟩ | ⟨v, hv, hsv⟩
        · exact ⟨s', by omega, hAt⟩
        · exact ⟨s, by omega, hs₀, v, hv, C, hsv, ancestorEq_refl C⟩
      have hVF := hVoterFrame w hw
      exact ⟨(hVF C hC').1, (hVF C hC').2, hUpdaterFrame' w hw C hC'⟩)
  intro B hB
  apply hstep B
  obtain ⟨s', hs', hAt⟩ := hB
  rcases Nat.lt_or_ge s' s with hlt | hge
  · exact Or.inl ⟨s', hlt, hAt⟩
  · have hss : s' = s := by omega
    subst hss
    obtain ⟨-, v, hv, C', hsv, hBC'⟩ := hAt
    exact Or.inr ⟨v, hv, C', hsv, hBC'⟩

/-- **The lock invariant at the healed slot.** When `B₀`'s slot is at least `s₀` and every live
lock entry `u`'s revocation of slot `s₀ + 1` leaves is compatible with `B₀`, every such entry is on
`B₀` or an ancestor of `B₀`.

Why: such an entry is on an ancestor of the block an update of a slot `s₁ + 1` at most `s₀` locked
(Lemmas 38 and 39), a block `u` held at that update's support cutoff, of slot at most `s₁ + 1`. A
strict descendant of `B₀` has a slot greater than `B₀`'s, so compatible means `B₀` or an ancestor.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `B₀`: the
  block; `u`: the validator. -/
theorem liveLocksOnFamilyAt_base (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ : ℕ) (B₀ : Block V) (u : V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hB₀slot : s₀ ≤ B₀.slot)
    (hCompat : ∀ A₃ : ACState V,
      revoke_locks S.P (expireLocks (stateBefore x (voteTime S (s₀ + 1)) u).A
        ((voteTime S (s₀ + 1) : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S (s₀ + 1)) u).S)
        ((voteTime S (s₀ + 1) : ℕ) : Int) (s₀ + 1) = .ok A₃ →
      ∀ e ∈ A₃.lock_entries,
        is_live (fg_to_ac (stateBefore x (voteTime S (s₀ + 1)) u).S)
          ((voteTime S (s₀ + 1) : ℕ) : Int) e = true → e.B.compatible B₀ = true) :
    LiveLocksOnFamilyAt S Sched x (fun D => D.AncestorEq B₀) s₀ u := by
  intro A₃ hR e he hl
  refine ⟨B₀, ancestorEq_refl B₀, ?_⟩
  rcases (compatible_iff _ _).1 (hCompat A₃ hR e he hl) with h | hB₀e
  · exact h
  -- `B₀` an ancestor of `e`'s block: they are equal, `e`'s block having slot at most `s₀`
  obtain ⟨e₁, he₁, -, -, hee₁, -⟩ :=
    GoldilocksCorrectness.Statements.Routines.lem38_revoke_locks_entries_moved S.P _ A₃ _ _ (s₀ + 1)
      (Nat.le_add_left 1 s₀) hR e he
  have he₁' := (Finset.mem_filter.1 he₁).1
  obtain ⟨s₁, -, hcut₁, -, A₁, -, e₀, -, -, he₀T, -, -, -, htr⟩ :=
    GoldilocksCorrectness.Statements.Executions.lem39_lock_entry_provenance S Sched x
      (voteTime S (s₀ + 1)) u e₁ hDiv he₁'
  obtain ⟨e', -, -, he₁e', he'e₀⟩ := htr (voteTime S (s₀ + 1)) hcut₁ le_rfl
  have hee₀ := ancestorEq_trans hee₁ (ancestorEq_trans he₁e' he'e₀)
  have he₀T' : e₀.B ∈ (stateBefore x (supportCutoff S (s₁ + 1)) u).S.T :=
    ((mem_fg_to_ac_tree _ _).1 he₀T).1
  have hslot₀ : e₀.B.slot ≤ s₁ + 1 := by
    have := slot_le_of_mem_T_before hDiv hMono he₀T'
    rw [(supportCutoff_slot S s₁).1] at this
    exact this
  have hs₁ : s₁ + 1 ≤ s₀ := by
    by_contra h
    have hm := slotStart_mono S (show s₀ + 1 ≤ s₁ + 1 by omega)
    have h1 := voteTime_eq S (s₀ + 1)
    have h2 := supportCutoff_eq S (s₁ + 1)
    have h3 := voteTime_eq S (s₁ + 1)
    omega
  have hBe₀ := ancestorEq_trans hB₀e hee₀
  by_cases hEq : B₀ = e₀.B
  · rw [hEq]
    exact hee₀
  · have hTC : TreeClosed S.P S.X (stateBefore x (supportCutoff S (s₁ + 1)) u).S :=
      (lem11_node_invariant S Sched x (stepBefore x (supportCutoff S (s₁ + 1))) u).1.2.2.1
    have hlt := slot_lt_of_ancestorEq_of_treeClosed hTC he₀T' hBe₀ hEq
    have h2 : B₀.slot < s₁ + 1 := lt_of_lt_of_le hlt hslot₀
    exact absurd (lt_of_le_of_lt hB₀slot h2) (by omega)

/-- **Lemma 81, the honest confirmations form a chain from the healed slot.** The proof; the
audited statement is in `Statements/Executions/HonestChainAfterHealingStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `B₀`: the block every updater of slot `s₀` saved. -/
theorem lem81_confirmations_chain (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ anchor : ℕ) (B₀ : Block V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocks S Sched x)
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    (hGST : GST ≤ voteTime S s₀)
    (hSleepK : CommitteeSleepiness S Sched anchor)
    (hAnchor : anchor ≤ slotStart S (s₀ + 1))
    (hB₀slot : s₀ ≤ B₀.slot)
    (hBase : HonestChainExtends S Sched x (honestActiveAt S Sched s₀) B₀ s₀)
    (hBaseSaved : ∀ v ∈ updaterAt S Sched s₀,
      (stateBefore x (supportCutoff S (s₀ + 1) + 1) v).A.saved_confirmation s₀ = some B₀)
    (hVoterFrame : ∀ s : ℕ, s₀ < s → ∀ w ∈ honestActiveAt S Sched s,
      VoterFrameOnChainAt S Sched x s₀ s w)
    (hUpdaterFrame : ∀ s : ℕ, s₀ < s → ∀ v ∈ updaterAt S Sched s,
      UpdaterFinalizedOnChainAt S Sched x s₀ s v) :
    ConfirmationsChain S Sched x s₀ := by
  have hRootsAt : ∀ t : ℕ, RootsNameBlocksUntil S Sched x t :=
    fun t => rootsNameBlocksUntil_of_rootsNameBlocks x t hRoots
  -- the times and the counting
  have hΔ := one_le_Δ S
  have hGSTs : ∀ s : ℕ, s₀ ≤ s → GST ≤ voteTime S s := fun s hs => by
    have h1 := voteTime_eq S s₀
    have h2 := voteTime_eq S s
    have h3 := slotStart_mono S hs
    omega
  have hAnch : ∀ s : ℕ, s₀ ≤ s → anchor ≤ slotStart S (s + 1) :=
    fun s hs => le_trans hAnchor (slotStart_mono S (by omega))
  have hCom : ∀ s : ℕ, s₀ ≤ s →
      |S.P.committee s| < 2 * |S.P.committee s ∩ honestActiveAt S Sched s| :=
    fun s hs => committee_majority_of_sleepiness S Sched anchor s hSleepK (hAnch s hs)
  have hWin : ∀ s : ℕ, ∀ u ∈ honestActiveAt S Sched (s + 1), ∀ t : ℕ,
      dutyWindowStart S (s + 1) ≤ t → t ≤ voteTime S (s + 2) →
      u ∈ Sched.awake (t : Int) ∧ u ∉ Sched.adv (t : Int) := by
    intro s u hu t h1 h2
    have h3 := supportCutoff_eq S (s + 2)
    have h4 : voteTime S (s + 2) ≤ supportCutoff S (s + 2) := by omega
    exact honestActiveAt_window S Sched (s + 1) u hMono hu t h1 (le_trans h2 h4)
  have hNewAt : ∀ s : ℕ, ∀ u ∈ honestActiveAt S Sched (s + 1), u ∈ honestActiveAt S Sched s ∨
      ∀ e ∈ (stateBefore x (voteTime S (s + 1)) u).A.lock_entries,
        is_live (fg_to_ac (stateBefore x (voteTime S (s + 1)) u).S)
          ((voteTime S (s + 1) : ℕ) : Int) e = false :=
    fun s u hu => (mem_honestActiveAt_or_slept S Sched s u hMono hu).imp id
      (fun hsl => GoldilocksCorrectness.Statements.Executions.lock_free_after_wake S Sched x s u
        hDiv hMono hsl)
  -- `B₀` is on the chain at slot `s₀`
  obtain ⟨u₀, hu₀⟩ : (S.P.committee s₀ ∩ honestActiveAt S Sched s₀).Nonempty :=
    Finset.card_pos.1 (by have := hCom s₀ le_rfl; omega)
  have hv₀ : u₀ ∈ updaterAt S Sched s₀ :=
    GoldilocksCorrectness.Proofs.Executions.honestActiveAt_subset_updaterAt S Sched s₀
      (Finset.mem_inter.1 hu₀).2
  have hB₀chain : ∀ C : Block V, C.AncestorEq B₀ → OnHonestChainBefore S Sched x s₀ (s₀ + 1) C :=
    fun C hC => ⟨s₀, Nat.lt_succ_self s₀, le_rfl, u₀, hv₀, B₀, hBaseSaved u₀ hv₀, hC⟩
  -- the invariants at the healed slot
  have hBaseInv : ChainInvFor S Sched x (honestActiveAt S Sched s₀) (fun D => D.AncestorEq B₀) s₀ :=
    fun C hC => honestChainExtends_of_ancestorEq S Sched x _ B₀ C s₀ hC hBase
  have hBaseLocks : ∀ u ∈ honestActiveAt S Sched s₀,
      LiveLocksOnFamilyAt S Sched x (fun D => D.AncestorEq B₀) s₀ u :=
    fun u hu => liveLocksOnFamilyAt_base S Sched x s₀ B₀ u hDiv hMono hB₀slot (hBase.2.1 u hu)
  have hBaseConf : ∀ C : Block V, C.AncestorEq B₀ → ∀ v ∈ updaterAt S Sched s₀, ∀ C' : Block V,
      (stateBefore x (supportCutoff S (s₀ + 1) + 1) v).A.saved_confirmation s₀ = some C' →
      C.AncestorEq C' := by
    intro C hC v hv C' hC'
    rw [hBaseSaved v hv] at hC'
    cases hC'
    exact hC
  -- the slot invariant and the lock invariant at every slot after the healed one
  have hAll : ∀ s : ℕ, s₀ + 1 ≤ s →
      ChainInvFor S Sched x (honestActiveAt S Sched s) (OnHonestChainBefore S Sched x s₀ s) s ∧
      ∀ u ∈ honestActiveAt S Sched s,
        LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ s) s u := by
    intro s hs
    induction s, hs using Nat.le_induction with
    | base =>
      refine ⟨?_, fun u hu => ?_⟩
      · have h := lem89s_chain_step S Sched x GST s₀ (honestActiveAt S Sched s₀)
          (honestActiveAt S Sched (s₀ + 1)) (updaterAt S Sched s₀) (fun D => D.AncestorEq B₀)
          hDiv hMono hSync hCatch (hRootsAt _) hParent hOwner hGST (subset_refl _)
          (subset_refl _) (subset_refl _) (honestActiveAt_succ_subset_updaterAt S Sched s₀ hMono)
          (hCom s₀ le_rfl) (hCom (s₀ + 1) (by omega)) hBaseInv (hNewAt s₀) hBaseLocks hBaseConf
          (fun C hC w hw => by
            have hC' : OnHonestChainBefore S Sched x s₀ (s₀ + 1) C := by
              rcases hC with hCB | ⟨v, hv, hsv⟩
              · exact hB₀chain C hCB
              · exact ⟨s₀, Nat.lt_succ_self s₀, le_rfl, v, hv, C, hsv, ancestorEq_refl C⟩
            have hVF := hVoterFrame (s₀ + 1) (Nat.lt_succ_self s₀) w hw
            exact ⟨(hVF C hC').1, (hVF C hC').2,
              hUpdaterFrame (s₀ + 1) (Nat.lt_succ_self s₀) w
                (GoldilocksCorrectness.Proofs.Executions.honestActiveAt_subset_updaterAt S Sched
                  (s₀ + 1) hw) C hC'⟩)
        intro C hC
        apply h C
        obtain ⟨s', hs', hs₀', v, hv, C', hC', hCC'⟩ := hC
        have hss : s' = s₀ := by omega
        subst hss
        exact Or.inr ⟨v, hv, C', hC', hCC'⟩
      · refine liveLocksOnFamilyAt_step S Sched x (fun D => D.AncestorEq B₀)
          (OnHonestChainBefore S Sched x s₀ (s₀ + 1)) s₀ u hDiv (fun t h1 h2 => hWin s₀ u hu t (le_trans (dutyWindowStart_mono S (by omega)) h1) h2)
          hB₀chain
          (fun C hC => ⟨s₀, Nat.lt_succ_self s₀, le_rfl, u,
            honestActiveAt_succ_subset_updaterAt S Sched s₀ hMono hu, C, hC, ancestorEq_refl C⟩)
          ?_
        rcases hNewAt s₀ u hu with h0 | hfree
        · exact hBaseLocks u h0
        · exact liveLocksOnFamilyAt_of_lockFree S Sched x _ s₀ u hfree
    | succ s hs ih =>
      obtain ⟨ihInv, ihLocks⟩ := ih
      refine ⟨lem81b_chain_step S Sched x GST s₀ s anchor hDiv hMono hSync hCatch
          (hRootsAt _) hParent hOwner (hGSTs s (by omega)) (by omega) hSleepK (hAnch s (by omega))
          ihInv ihLocks
          (hVoterFrame (s + 1) (by omega)) (hUpdaterFrame s (by omega))
          (fun w hw => hUpdaterFrame (s + 1) (by omega) w
            (GoldilocksCorrectness.Proofs.Executions.honestActiveAt_subset_updaterAt S Sched
              (s + 1) hw)),
        fun u hu => ?_⟩
      refine liveLocksOnFamilyAt_step S Sched x (OnHonestChainBefore S Sched x s₀ s)
        (OnHonestChainBefore S Sched x s₀ (s + 1)) s u hDiv (fun t h1 h2 => hWin s u hu t (le_trans (dutyWindowStart_mono S (by omega)) h1) h2)
        (fun C ⟨s', hs', hAt⟩ => ⟨s', by omega, hAt⟩)
        (fun C hC => ⟨s, Nat.lt_succ_self s, by omega, u,
          honestActiveAt_succ_subset_updaterAt S Sched s hMono hu, C, hC, ancestorEq_refl C⟩) ?_
      rcases hNewAt s u hu with h0 | hfree
      · exact ihLocks u h0
      · exact liveLocksOnFamilyAt_of_lockFree S Sched x _ s u hfree
  -- the chain
  intro s s' v v' C C' hs hss' hv hv' hC hC'
  refine ⟨fun hlt => ?_, fun heq => ?_⟩
  · obtain ⟨hInv', -⟩ := hAll s' (by omega)
    exact chainInvFor_updater_confirmation S Sched x GST s' (honestActiveAt S Sched s')
      (OnHonestChainBefore S Sched x s₀ s') v' hDiv hMono hSync hCatch (hRootsAt _) hParent
      hOwner (hGSTs s' (by omega)) (subset_refl _) (hCom s' (by omega)) hInv' hv'
      (fun D hD => hUpdaterFrame s' (by omega) v' hv' D hD) C
      ⟨s, hlt, hs, v, hv, C, hC, ancestorEq_refl C⟩ C' hC'
  · subst heq
    have hc := supportCutoff_eq S s
    exact GoldilocksCorrectness.Statements.Executions.lem32_saved_confirmations_compatible_state S
      Sched x GST s v v' C C' hDiv hMono hSync hCatch (hRootsAt _)
      (by have := hGSTs s hs; omega)
      (updaterAt_window S Sched s v hMono hv) (updaterAt_window S Sched s v' hMono hv') hC hC'

/-- **Two blocks on the honest chain are compatible.** The proof; the audited statement is in
`Statements/Executions/HonestChainAfterHealingStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the first slot; `B`, `B'`:
  the blocks. -/
theorem onHonestChain_compatible (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ : ℕ) (B B' : Block V)
    (hChain : ConfirmationsChain S Sched x s₀)
    (hB : OnHonestChain S Sched x s₀ B) (hB' : OnHonestChain S Sched x s₀ B') :
    B.compatible B' = true := by
  obtain ⟨s, hs, v, hv, C, hC, hBC⟩ := hB
  obtain ⟨s', hs', v', hv', C', hC', hBC'⟩ := hB'
  have hcc : C.compatible C' = true := by
    rcases Nat.lt_trichotomy s s' with hlt | heq | hgt
    · exact (compatible_iff _ _).2
        (Or.inl ((hChain s s' v v' C C' hs hlt.le hv hv' hC hC').1 hlt))
    · exact (hChain s s' v v' C C' hs heq.le hv hv' hC hC').2 heq
    · exact (compatible_iff _ _).2
        (Or.inr ((hChain s' s v' v C' C hs' hgt.le hv' hv hC' hC).1 hgt))
  exact compatible_of_ancestorEq_both hBC hBC' hcc

/-- **Lemma 81's induction before a slot.** The proof; the audited statement is in
`Statements/Executions/HonestChainAfterHealingStatements.lean`. The induction of
`lem81_confirmations_chain`'s proof, stopped before the slot `n`: the frames are read only at the
slots `s` with `s₀ < s < n`, and the conclusion is for those slots.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `n`: the bound on the slots; `B₀`: the block every updater of slot `s₀`
  saved.

Roots name blocks until `supportCutoff S (n - 1)`: the conclusion at a slot `s` reads the chain
step at slot `s - 1` (`lem89s_chain_step` at `s₀`, then `lem81b_chain_step`), which takes blocks
as held up to `supportCutoff S s`, and `s ≤ n - 1`. -/
theorem lem81_inv_before (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ anchor n : ℕ) (B₀ : Block V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (n - 1)))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    (hGST : GST ≤ voteTime S s₀)
    (hSleepK : CommitteeSleepiness S Sched anchor)
    (hAnchor : anchor ≤ slotStart S (s₀ + 1))
    (hB₀slot : s₀ ≤ B₀.slot)
    (hBase : HonestChainExtends S Sched x (honestActiveAt S Sched s₀) B₀ s₀)
    (hBaseSaved : ∀ v ∈ updaterAt S Sched s₀,
      (stateBefore x (supportCutoff S (s₀ + 1) + 1) v).A.saved_confirmation s₀ = some B₀)
    (hVoterFrame : ∀ s : ℕ, s₀ < s → s < n → ∀ w ∈ honestActiveAt S Sched s,
      VoterFrameOnChainAt S Sched x s₀ s w)
    (hUpdaterFrame : ∀ s : ℕ, s₀ < s → s < n → ∀ v ∈ updaterAt S Sched s,
      UpdaterFinalizedOnChainAt S Sched x s₀ s v) :
    ∀ s : ℕ, s₀ < s → s < n →
      ChainInvFor S Sched x (honestActiveAt S Sched s) (OnHonestChainBefore S Sched x s₀ s) s ∧
      ∀ u ∈ honestActiveAt S Sched s,
        LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ s) s u := by
  -- the support cutoff grows with the slot
  have hcm : ∀ a b : ℕ, a ≤ b → supportCutoff S a ≤ supportCutoff S b := fun a b h => by
    rcases Nat.lt_or_eq_of_le h with h | h
    · exact le_of_lt (supportCutoff_lt_of_lt S h)
    · rw [h]
  -- the times and the counting
  have hΔ := one_le_Δ S
  have hGSTs : ∀ s : ℕ, s₀ ≤ s → GST ≤ voteTime S s := fun s hs => by
    have h1 := voteTime_eq S s₀
    have h2 := voteTime_eq S s
    have h3 := slotStart_mono S hs
    omega
  have hAnch : ∀ s : ℕ, s₀ ≤ s → anchor ≤ slotStart S (s + 1) :=
    fun s hs => le_trans hAnchor (slotStart_mono S (by omega))
  have hCom : ∀ s : ℕ, s₀ ≤ s →
      |S.P.committee s| < 2 * |S.P.committee s ∩ honestActiveAt S Sched s| :=
    fun s hs => committee_majority_of_sleepiness S Sched anchor s hSleepK (hAnch s hs)
  have hWin : ∀ s : ℕ, ∀ u ∈ honestActiveAt S Sched (s + 1), ∀ t : ℕ,
      dutyWindowStart S (s + 1) ≤ t → t ≤ voteTime S (s + 2) →
      u ∈ Sched.awake (t : Int) ∧ u ∉ Sched.adv (t : Int) := by
    intro s u hu t h1 h2
    have h3 := supportCutoff_eq S (s + 2)
    have h4 : voteTime S (s + 2) ≤ supportCutoff S (s + 2) := by omega
    exact honestActiveAt_window S Sched (s + 1) u hMono hu t h1 (le_trans h2 h4)
  have hNewAt : ∀ s : ℕ, ∀ u ∈ honestActiveAt S Sched (s + 1), u ∈ honestActiveAt S Sched s ∨
      ∀ e ∈ (stateBefore x (voteTime S (s + 1)) u).A.lock_entries,
        is_live (fg_to_ac (stateBefore x (voteTime S (s + 1)) u).S)
          ((voteTime S (s + 1) : ℕ) : Int) e = false :=
    fun s u hu => (mem_honestActiveAt_or_slept S Sched s u hMono hu).imp id
      (fun hsl => GoldilocksCorrectness.Statements.Executions.lock_free_after_wake S Sched x s u
        hDiv hMono hsl)
  -- `B₀` is on the chain at slot `s₀`
  obtain ⟨u₀, hu₀⟩ : (S.P.committee s₀ ∩ honestActiveAt S Sched s₀).Nonempty :=
    Finset.card_pos.1 (by have := hCom s₀ le_rfl; omega)
  have hv₀ : u₀ ∈ updaterAt S Sched s₀ :=
    GoldilocksCorrectness.Proofs.Executions.honestActiveAt_subset_updaterAt S Sched s₀
      (Finset.mem_inter.1 hu₀).2
  have hB₀chain : ∀ C : Block V, C.AncestorEq B₀ → OnHonestChainBefore S Sched x s₀ (s₀ + 1) C :=
    fun C hC => ⟨s₀, Nat.lt_succ_self s₀, le_rfl, u₀, hv₀, B₀, hBaseSaved u₀ hv₀, hC⟩
  -- the invariants at the healed slot
  have hBaseInv : ChainInvFor S Sched x (honestActiveAt S Sched s₀) (fun D => D.AncestorEq B₀) s₀ :=
    fun C hC => honestChainExtends_of_ancestorEq S Sched x _ B₀ C s₀ hC hBase
  have hBaseLocks : ∀ u ∈ honestActiveAt S Sched s₀,
      LiveLocksOnFamilyAt S Sched x (fun D => D.AncestorEq B₀) s₀ u :=
    fun u hu => liveLocksOnFamilyAt_base S Sched x s₀ B₀ u hDiv hMono hB₀slot (hBase.2.1 u hu)
  have hBaseConf : ∀ C : Block V, C.AncestorEq B₀ → ∀ v ∈ updaterAt S Sched s₀, ∀ C' : Block V,
      (stateBefore x (supportCutoff S (s₀ + 1) + 1) v).A.saved_confirmation s₀ = some C' →
      C.AncestorEq C' := by
    intro C hC v hv C' hC'
    rw [hBaseSaved v hv] at hC'
    cases hC'
    exact hC
  -- the slot invariant and the lock invariant at every slot after the healed one and before `n`
  have hAll : ∀ s : ℕ, s₀ + 1 ≤ s → s < n →
      ChainInvFor S Sched x (honestActiveAt S Sched s) (OnHonestChainBefore S Sched x s₀ s) s ∧
      ∀ u ∈ honestActiveAt S Sched s,
        LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ s) s u := by
    intro s hs
    induction s, hs using Nat.le_induction with
    | base =>
      intro hn
      refine ⟨?_, fun u hu => ?_⟩
      · have h := lem89s_chain_step S Sched x GST s₀ (honestActiveAt S Sched s₀)
          (honestActiveAt S Sched (s₀ + 1)) (updaterAt S Sched s₀) (fun D => D.AncestorEq B₀)
          hDiv hMono hSync hCatch (hRoots.mono (hcm _ _ (by omega))) hParent hOwner hGST
          (subset_refl _) (subset_refl _) (subset_refl _)
          (honestActiveAt_succ_subset_updaterAt S Sched s₀ hMono)
          (hCom s₀ le_rfl) (hCom (s₀ + 1) (by omega)) hBaseInv (hNewAt s₀) hBaseLocks hBaseConf
          (fun C hC w hw => by
            have hC' : OnHonestChainBefore S Sched x s₀ (s₀ + 1) C := by
              rcases hC with hCB | ⟨v, hv, hsv⟩
              · exact hB₀chain C hCB
              · exact ⟨s₀, Nat.lt_succ_self s₀, le_rfl, v, hv, C, hsv, ancestorEq_refl C⟩
            have hVF := hVoterFrame (s₀ + 1) (Nat.lt_succ_self s₀) hn w hw
            exact ⟨(hVF C hC').1, (hVF C hC').2,
              hUpdaterFrame (s₀ + 1) (Nat.lt_succ_self s₀) hn w
                (GoldilocksCorrectness.Proofs.Executions.honestActiveAt_subset_updaterAt S Sched
                  (s₀ + 1) hw) C hC'⟩)
        intro C hC
        apply h C
        obtain ⟨s', hs', hs₀', v, hv, C', hC', hCC'⟩ := hC
        have hss : s' = s₀ := by omega
        subst hss
        exact Or.inr ⟨v, hv, C', hC', hCC'⟩
      · refine liveLocksOnFamilyAt_step S Sched x (fun D => D.AncestorEq B₀)
          (OnHonestChainBefore S Sched x s₀ (s₀ + 1)) s₀ u hDiv
          (fun t h1 h2 => hWin s₀ u hu t (le_trans (dutyWindowStart_mono S (by omega)) h1) h2)
          hB₀chain
          (fun C hC => ⟨s₀, Nat.lt_succ_self s₀, le_rfl, u,
            honestActiveAt_succ_subset_updaterAt S Sched s₀ hMono hu, C, hC, ancestorEq_refl C⟩)
          ?_
        rcases hNewAt s₀ u hu with h0 | hfree
        · exact hBaseLocks u h0
        · exact liveLocksOnFamilyAt_of_lockFree S Sched x _ s₀ u hfree
    | succ s hs ih =>
      intro hn
      obtain ⟨ihInv, ihLocks⟩ := ih (by omega)
      refine ⟨lem81b_chain_step S Sched x GST s₀ s anchor hDiv hMono hSync hCatch
          (hRoots.mono (hcm _ _ (by omega))) hParent hOwner (hGSTs s (by omega)) (by omega)
          hSleepK (hAnch s (by omega)) ihInv ihLocks
          (hVoterFrame (s + 1) (by omega) hn) (hUpdaterFrame s (by omega) (by omega))
          (fun w hw => hUpdaterFrame (s + 1) (by omega) hn w
            (GoldilocksCorrectness.Proofs.Executions.honestActiveAt_subset_updaterAt S Sched
              (s + 1) hw)),
        fun u hu => ?_⟩
      refine liveLocksOnFamilyAt_step S Sched x (OnHonestChainBefore S Sched x s₀ s)
        (OnHonestChainBefore S Sched x s₀ (s + 1)) s u hDiv
        (fun t h1 h2 => hWin s u hu t (le_trans (dutyWindowStart_mono S (by omega)) h1) h2)
        (fun C ⟨s', hs', hAt⟩ => ⟨s', by omega, hAt⟩)
        (fun C hC => ⟨s, Nat.lt_succ_self s, by omega, u,
          honestActiveAt_succ_subset_updaterAt S Sched s hMono hu, C, hC, ancestorEq_refl C⟩) ?_
      rcases hNewAt s u hu with h0 | hfree
      · exact ihLocks u h0
      · exact liveLocksOnFamilyAt_of_lockFree S Sched x _ s u hfree
  exact fun s hs => hAll s hs

/-- **Lemma 81's induction.** The proof; the audited statement is in
`Statements/Executions/HonestChainAfterHealingStatements.lean`. The induction of
`lem81_confirmations_chain`'s proof, with the local facts it reads: at a slot `s`, the instance of
`lem81_inv_before` at `n := s + 1`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `B₀`: the block every updater of slot `s₀` saved. -/
theorem lem81_inv (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ anchor : ℕ) (B₀ : Block V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocks S Sched x)
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    (hGST : GST ≤ voteTime S s₀)
    (hSleepK : CommitteeSleepiness S Sched anchor)
    (hAnchor : anchor ≤ slotStart S (s₀ + 1))
    (hB₀slot : s₀ ≤ B₀.slot)
    (hBase : HonestChainExtends S Sched x (honestActiveAt S Sched s₀) B₀ s₀)
    (hBaseSaved : ∀ v ∈ updaterAt S Sched s₀,
      (stateBefore x (supportCutoff S (s₀ + 1) + 1) v).A.saved_confirmation s₀ = some B₀)
    (hVoterFrame : ∀ s : ℕ, s₀ < s → ∀ w ∈ honestActiveAt S Sched s,
      VoterFrameOnChainAt S Sched x s₀ s w)
    (hUpdaterFrame : ∀ s : ℕ, s₀ < s → ∀ v ∈ updaterAt S Sched s,
      UpdaterFinalizedOnChainAt S Sched x s₀ s v) :
    ∀ s : ℕ, s₀ < s →
      ChainInvFor S Sched x (honestActiveAt S Sched s) (OnHonestChainBefore S Sched x s₀ s) s ∧
      ∀ u ∈ honestActiveAt S Sched s,
        LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ s) s u := by
  intro s hs
  exact lem81_inv_before S Sched x GST s₀ anchor (s + 1) B₀ hDiv hMono hSync hCatch
    (rootsNameBlocksUntil_of_rootsNameBlocks x _ hRoots) hParent hOwner hGST hSleepK hAnchor
    hB₀slot hBase hBaseSaved (fun s' h1 _ => hVoterFrame s' h1)
    (fun s' h1 _ => hUpdaterFrame s' h1) s hs (Nat.lt_succ_self s)

end GoldilocksCorrectness.Proofs.Executions
