module
public import GoldilocksCorrectness.Proofs.Executions.Lemma81
public import GoldilocksCorrectness.Proofs.Executions.AsyncDelivery
public import GoldilocksCorrectness.Statements.Executions.HonestChainStatementsUpTo
public import GoldilocksCorrectness.Statements.Executions.NextSlotVoteStatementsUpTo
public import GoldilocksCorrectness.Statements.Executions.ConfirmationCompatibilityStatementsUpTo

@[expose] public section

/-!
# `Lemma81.lean` with the delivery premises up to a bound

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma81.lean` that name a delivery
premise, restated with `SynchronyFromWakeUpTo` and `CatchUpOnWakeUpTo` at a bound on the deadlines
. The bound of each twin
is the latest ordinary deadline `max t GST + Δ` of a send its proof reads, written in the twin's
own parameters.

* `lem21b_goldfish_vote_extends_eligible_block_held`, `lem36b_confirmed_block_extended_held`,
  `chainInvFor_updater_confirmation`, `lem89s_chain_step`, `lem81b_chain_step`, `lem81_inv_before`

No `axiom`, no `native_decide`, no `sorry`. The landed page is imported, never edited.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff viewFreeze
  dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_le_supportCutoff dutyWindowStart_mono
  dutyWindowStart_succ_le_slotStart one_le_Δ slotStart_eq slotStart_mono slot_eq_of_mem
  supportCutoff_cast supportCutoff_eq supportCutoff_lt_of_lt viewFreeze_cast viewFreeze_eq
  voteTime_eq voteTime_succ)

open GoldilocksCorrectness.Proofs.Routines (compatible_of_ancestorEq_both)
open GoldilocksCorrectness.Statements.Routines (EarlySupporterOf)

open GoldilocksCorrectness.Proofs.Routines (mem_fg_to_ac_tree)

open GoldilocksCorrectness.Proofs.Routines (get_anchor_mem_T)

open GoldilocksCorrectness.Proofs.Routines (earlySupporterOf_of_keepsVotes expireLocks_keepsVotes
  pool_of_keepsVotes)

open GoldilocksCorrectness.Proofs.Routines (wake_eq)

open GoldilocksCorrectness.Proofs.Routines (goldfish_fork_choice_eq)

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
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

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
voteTime S (s + 1)`, takes blocks as held up to one delay after `w`'s fork choice.

Restated with the delivery premises up to `supportCutoff S (s + 1)`: Lemma 64 reads the votes due one delay after the vote time of slot `s + 1`. -/
theorem lem21b_goldfish_vote_extends_eligible_block_held_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s : ℕ) (Sup : Finset V) (B : Block V) (v w : V)
    (vote : GoldfishVote V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S (s + 1)))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S (s + 1)))
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
      H_w hDiv hMono hSync hCatch hRoots hParent hGST (by omega)
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
blocks as held up to one delay after `w`'s vote time of slot `s + 1`.

Restated with the delivery premises up to `supportCutoff S (s + 1)`: Lemma 21b at slot `s` reads deliveries due by then (`lem21b_goldfish_vote_extends_eligible_block_held_upTo`). -/
theorem lem36b_confirmed_block_extended_held_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s : ℕ) (C' : Block V) (v w : V) (A' : ACState V)
    (vote : GoldfishVote V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
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
  exact lem21b_goldfish_vote_extends_eligible_block_held_upTo S Sched x GST s Sup C' v w vote hDiv
    hMono hSync hCatch hRoots hParent hGST hv hw hSup' hElig' hF2 hF3 hLocks hSend

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
blocks as held up to the support cutoff of slot `s`.

Restated with the delivery premises up to `supportCutoff S s`: Lemma 78 at slot `s` reads deliveries due by then (`lem78_update_confirmation_extends_voter_majority_chain_upTo`). -/
theorem chainInvFor_updater_confirmation_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s : ℕ) (Hon : Finset V) (𝓒 : Block V → Prop) (v : V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S s))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S s))
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
  exact GoldilocksCorrectness.Statements.Executions.lem78_update_confirmation_extends_voter_majority_chain_upTo
    S Sched x GST s (S.P.committee s ∩ Hon) H C v hDiv hMono hSync hCatch hRoots hParent
    hOwner hGST
    (fun u hu => ⟨(Finset.mem_inter.1 hu).1,
      (honestActiveAt_window S Sched s u hMono (hHon (Finset.mem_inter.1 hu).2)
        (supportCutoff S (s + 1)) hdc le_rfl).2, (hH u hu).1, (hH u hu).2.1, (hH u hu).2.2⟩)
    (voters_count_lt_of_committee_majority (pool_committee_of_stateBefore S Sched x _ v s)
      (committee_sdiff_lt _ _ hCommittee))
    (updaterAt_window S Sched s v hMono hv) (hF C hC)

/-- **The chain step.** The proof; the audited statement is in
`Statements/Executions/HonestChainAfterHealingStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s'`: the slot of the step;
- `Hon`: the voters of slot `s'`; `Hon'`: the members of slot `s' + 1`; `Upd`: the updaters whose
  confirmations of slot `s'` join the family; `𝓒`: the family.

Roots name blocks until `supportCutoff S (s' + 1)`: Lemmas 36b, 32 and 78, which the proof calls
at the slots `s'` and `s' + 1`, take blocks as held up to the support cutoff of slot `s' + 1`;
Lemma 26b reads earlier.

Restated with the delivery premises up to `supportCutoff S (s' + 1)`: Lemmas 36b and 78, which the proof calls at the slots `s'` and `s' + 1`, read deliveries due by then; Lemmas 26b and 32 read earlier. -/
theorem lem89s_chain_step_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s' : ℕ) (Hon Hon' Upd : Finset V)
    (𝓒 : Block V → Prop)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S (s' + 1)))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S (s' + 1)))
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
      exact GoldilocksCorrectness.Statements.Executions.lem26b_goldfish_vote_extends_voter_majority_block_held_upTo
        S Sched x GST s' (S.P.committee s' ∩ Hon) H B u vote hDiv hMono (hSync.mono (by omega))
        (hCatch.mono (by omega)) (hRoots.mono (by omega)) hParent hOwner hGST
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
      obtain ⟨H_u, hHT, hvt, hCH⟩ := lem36b_confirmed_block_extended_held_upTo S Sched x GST s' C' v u
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
      · have h32 := GoldilocksCorrectness.Statements.Executions.lem32_saved_confirmations_compatible_state_upTo
          S Sched x GST s' w v Cw C' hDiv hMono (hSync.mono (by omega)) (hCatch.mono (by omega)) hRoots
          (by omega)
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
    exact GoldilocksCorrectness.Statements.Executions.lem78_update_confirmation_extends_voter_majority_chain_upTo
      S Sched x GST (s' + 1) (S.P.committee (s' + 1) ∩ Hon') H B v hDiv hMono hSync hCatch
      hRoots hParent hOwner (by omega)
      (fun u hu => ⟨(Finset.mem_inter.1 hu).1,
        (hHon'W u (Finset.mem_inter.1 hu).2 (supportCutoff S (s' + 2)) (by omega) le_rfl).2,
        (hH u hu).1, (hH u hu).2.1, (hH u hu).2.2⟩)
      (voters_count_lt_of_committee_majority (pool_committee_of_stateBefore S Sched x _ v (s' + 1))
        (committee_sdiff_lt _ _ hCommittee'))
      (fun t h1 h2 => hHon'W v hv t (le_trans hdw12 h1) h2) (hStep B hB0 v hv).2.2
  exact ⟨hClause1, hClause2, hClause3⟩

/-- **Lemma 81b, the chain step after the healed slot.** The proof; the audited statement is in
`Statements/Executions/HonestChainAfterHealingStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the first slot of the chain; `s`: the slot of the step;
  `anchor`: the time from which committee sleepiness holds.

Roots name blocks until `supportCutoff S (s + 1)`: the chain step, which the proof calls at slot
`s`, takes blocks as held up to the support cutoff of slot `s + 1`.

Restated with the delivery premises up to `supportCutoff S (s + 1)`: the chain step at slot `s` reads deliveries due by then (`lem89s_chain_step_upTo`). -/
theorem lem81b_chain_step_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ s anchor : ℕ)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S (s + 1)))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S (s + 1)))
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
  have hstep := lem89s_chain_step_upTo S Sched x GST s (honestActiveAt S Sched s)
    (honestActiveAt S Sched (s + 1)) (updaterAt S Sched s) (OnHonestChainBefore S Sched x s₀ s)
    hDiv hMono hSync hCatch hRoots hParent hOwner hGST (subset_refl _) (subset_refl _)
    (subset_refl _) (honestActiveAt_succ_subset_updaterAt S Sched s hMono) hCom hCom' hInv
    (fun u hu => (mem_honestActiveAt_or_slept S Sched s u hMono hu).imp id
      (fun hsl => GoldilocksCorrectness.Statements.Executions.lock_free_after_wake S Sched x s u
        hDiv hMono hsl))
    hLocks
    (fun C hC v hv => chainInvFor_updater_confirmation_upTo S Sched x GST s (honestActiveAt S Sched s)
      (OnHonestChainBefore S Sched x s₀ s) v hDiv hMono (hSync.mono hcs)
      (hCatch.mono hcs) (hRoots.mono hcs) hParent hOwner hGST (subset_refl _)
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
as held up to `supportCutoff S s`, and `s ≤ n - 1`.

Restated with the delivery premises up to `supportCutoff S (n - 1)`: the conclusion at a slot `s ≤ n − 1` reads the chain step at slot `s − 1`, whose deliveries are due by `supportCutoff S s`. -/
theorem lem81_inv_before_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ anchor n : ℕ) (B₀ : Block V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S (n - 1)))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S (n - 1)))
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
      · have h := lem89s_chain_step_upTo S Sched x GST s₀ (honestActiveAt S Sched s₀)
          (honestActiveAt S Sched (s₀ + 1)) (updaterAt S Sched s₀) (fun D => D.AncestorEq B₀)
          hDiv hMono (hSync.mono (hcm _ _ (by omega)))
          (hCatch.mono (hcm _ _ (by omega))) (hRoots.mono (hcm _ _ (by omega))) hParent hOwner hGST
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
      refine ⟨lem81b_chain_step_upTo S Sched x GST s₀ s anchor hDiv hMono
          (hSync.mono (hcm _ _ (by omega))) (hCatch.mono (hcm _ _ (by omega)))
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

end GoldilocksCorrectness.Proofs.Executions

