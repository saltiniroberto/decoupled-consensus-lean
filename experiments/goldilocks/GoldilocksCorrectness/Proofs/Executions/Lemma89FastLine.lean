module
public import GoldilocksCorrectness.Statements.Executions.Lemma89Defs
public import GoldilocksCorrectness.Statements.Executions.PhaseFrameStatements
public import GoldilocksCorrectness.Statements.Executions.AccountableStatements
public import GoldilocksCorrectness.Statements.Executions.ChainStateStatements
public import GoldilocksCorrectness.Statements.Routines.ConfirmationStatements
public import GoldilocksCorrectness.Proofs.Executions.Lemma81
public import GoldilocksCorrectness.Proofs.Executions.Lemma82
public import GoldilocksCorrectness.Proofs.Executions.Lemma84
public import GoldilocksCorrectness.Proofs.Executions.PhaseKit
public import GoldilocksCorrectness.Proofs.Executions.PhaseFrame

@[expose] public section

/-!
# Lemma 89 on the fast-confirmation route: the first steps of the one line from the fast block

The proofs of the first four steps of part A of Lemma 89's skeleton on the fast-confirmation route
, stated in
`GoldilocksCorrectness/Statements/Executions/Lemma89Statements.lean`. Write `a_r := aR S r` for
the action time of round `r`:

- A1 `fast_block_of_honest_attestation`: an honest attestation at `a_r` is built from a fast block
  of the sender's confirmation update at `a_r`, held before `a_r`, at the attestation's height
  (Lemma 82's route, stopped at the fast block);
- A2 `held_height_le_before_action`: when every honest attestation sent before `a_r` has height at
  most `H₂`, every block a validator holds before a time `t ≤ a_r` has height at most `H₂ + 1`
  (`attested_height_bound` at the step `stepBefore x t`);
- A3 `finalized_ancestor_of_fast_block`: then every honest finalized block before such a `t` is
  `L` or an ancestor of `L`, for a block `L` an honest validator holds before `a_r` at height
  `H₂ + 1` (Lemma 89a with A2);
- A4 `lem36c_fast_ancestor_extended_held`: Lemma 36b with the frame and lock conditions read at an
  ancestor of the saved confirmation (Lemma 36b's proof, with Lemma 36 at that ancestor).
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ voteTime supportCutoff viewFreeze)
open GoldilocksCorrectness.Proofs.Routines (supportCutoff_cast supportCutoff_succ_times)

open GoldilocksCorrectness.Proofs.Routines (lem47_chain_state_heights)
open GoldilocksCorrectness.Statements.Routines (EarlySupporterOf chainStateOf)

open GoldilocksCorrectness.Proofs.Routines (mem_fg_to_ac_tree)

open GoldilocksCorrectness.Proofs.Routines (earlySupporterOf_of_keepsVotes expireLocks_keepsVotes
  pool_of_keepsVotes)

open GoldilocksCorrectness.Proofs.Routines (duty_window_start_lt_supportCutoff)

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

-- An index `x[i]` into an execution, and `x[i][v]` into a configuration, has the valid-index
-- predicate `fun _ _ => True`; this rule, local to the file, proves it at once
--. No statement and no proof term
-- changes.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- **A1, an honest attestation is built from a fast block of its sender's update.** The proof;
the audited statement is in `Statements/Executions/Lemma89Statements.lean`.

The route: Lemma 82's, stopped at the fast block. The tick's attestation is the duty's
(Lemma 49), built from the duty's source, whose chain-state height it carries; the tick passed the
duty test, so it ran the confirmation update of slot `r * R + 1` (Lemma 15) on the state the tick
starts from, which is `v`'s state before `a_r`; the source is a fast block of that update's answer
and a block of `v`'s tree.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `r`: the round; `v`: the attester;
  `a`: the attestation. -/
theorem fast_block_of_honest_attestation (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (r : ℕ) (v : V) (a : Attestation V)
    (hSend : HonestAttestationAt S Sched x (aR S r) v a) :
    ∃ (A' : ACState V) (L : Block V),
      update_confirmation S.C S.P
        (expireLocks (stateBefore x (aR S r) v).A ((aR S r : ℕ) : Int))
        (fg_to_ac (stateBefore x (aR S r) v).S) ((aR S r : ℕ) : Int) (r * S.C.R + 1) = .ok A' ∧
      L ∈ A'.fast_blocks ∧ L ∈ (stateBefore x (aR S r) v).S.T ∧
      (chainStateOf S.C L).h = a.h := by
  obtain ⟨s, hs⟩ : ∃ s : ℕ, s = r * S.C.R := ⟨_, rfl⟩
  have haR : aR S r = supportCutoff S (s + 1) := by rw [hs]; rfl
  rw [haR] at hSend ⊢
  rw [← hs]
  obtain ⟨i, hl, -, -, hSent⟩ := hSend
  -- the tick, and the attestation it built
  obtain ⟨-, n', sent, hrun, ha⟩ := tick_send_of_honestSendAt hl hSent
  obtain ⟨-, fi, source, hfi, hsrc, hca, -⟩ :=
    lem49_tick_attests S.C S.P S.X _ n' _ sent a hrun ha
  have hR := (tick_attest_awake S.C S.P S.X (tickInputState x i (supportCutoff S (s + 1)) v)
    ((supportCutoff S (s + 1) : ℕ) : Int)).of_outcome hrun
  have hawk := hR a ha
  obtain ⟨hslot, -, -, hcut⟩ := supportCutoff_succ_times S r s hs
  -- the duty test passed, on the stored `awakeSince`
  rw [hslot] at hawk
  have hdws : duty_window_start S.C (s + 1) < ((supportCutoff S (s + 1) : ℕ) : Int) :=
    duty_window_start_lt_supportCutoff S (s + 1)
  obtain ⟨τ, hτ, hτle⟩ := awakeSince_of_record_awake hawk hdws
  -- the confirmation update of slot `s + 1` ran in the tick
  obtain ⟨A'', hUpd, -, hfb, -, -⟩ := lem15_tick_updates_confirmation S.C S.P S.X _ n' _ sent
    hrun hcut ⟨τ, hτ, by rw [hslot]; exact hτle⟩
  rw [hslot] at hUpd
  have hfast : source ∈ A''.fast_blocks := by
    rw [← hfb]
    exact ac_to_fg_source_fast hfi hsrc
  -- the state the tick starts from is `v`'s state before the tick
  have hframe := tickInputState_frame x i (supportCutoff S (s + 1)) v
  have hSt : stateBefore x (supportCutoff S (s + 1)) v = x[i][v].st := by
    unfold stateBefore
    rw [stepBefore_eq_of_lbl x hl]
  rw [hframe.1, hframe.2.1] at hUpd
  have hsT : source ∈ (x[i][v].st).S.T := by
    rw [← hframe.1]
    exact ((mem_fg_to_ac_tree _ _).1 (ac_to_fg_source_mem hfi hsrc)).1
  have hσ : (x[i][v].st).S.σ source = chainStateOf S.C source :=
    (lem11_node_invariant S Sched x i v).1.2.2.2.2.2.1 source hsT
  refine ⟨A'', source, ?_, hfast, ?_, ?_⟩
  · rw [hSt]
    exact hUpd
  · rw [hSt]
    exact hsT
  · rcases create_attestation_cases _ _ _ _ _ _ _ with h0 | ⟨τ', fp', -, -, -, h1⟩
    · rw [h0] at hca
      cases hca
    · rw [h1] at hca
      injection hca with hca
      subst hca
      show _ = ((tickInputState x i (supportCutoff S (s + 1)) v).S.σ source).h
      rw [hframe.1, hσ]

/-- **A2, before `a_r` every honest-held block has height at most `H₂ + 1`.** The proof; the
audited statement is in `Statements/Executions/Lemma89Statements.lean`.

The route: `attested_height_bound` at the step `stepBefore x t`, whose time is at most `t − 1`
(`time_stepBefore_succ_le`), or `0` with no tick before it when `t = 0`; every tick at a time at
most that is before `a_r`, so `hOld` bounds its honest attestations.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tAwakeEnd`: the phase's end;
- `r`: the round; `H₂`: the bound; `t`: the time; `w`: the holder; `D`: the block. -/
theorem held_height_le_before_action (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (tAwakeEnd r H₂ t : ℕ) (w : V) (D : Block V)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hOld : OldAttestationsAtMost S Sched x (aR S r) H₂)
    (htr : t ≤ aR S r) (hEnd : aR S r ≤ tAwakeEnd)
    (hD : D ∈ (stateBefore x t w).S.T) :
    (chainStateOf S.C D).h ≤ H₂ + 1 := by
  have hle : x[stepBefore x t].time ≤ t := time_stepBefore_le x t
  have hAdv : AdversaryFewerThanThirdUntil Sched (validator_count V) (x[stepBefore x t].time : Int) :=
    adversaryFewerThanThirdUntil_of_le (by exact_mod_cast (show x[stepBefore x t].time ≤
      tAwakeEnd by omega)) hThird
  refine attested_height_bound S Sched x hU (stepBefore x t) H₂ w D hAdv ?_ hD
  intro i t₁ u a hl ht₁ hAw hHon hsent
  have h1 := (time_of_lbl_tickAllAwake x hl).1
  refine hOld i t₁ u a hl ?_ hAw hHon hsent
  rcases t with _ | t'
  · have h0 : x[0].time = 0 := x.init.1
    rw [stepBefore_zero x, h0] at ht₁
    omega
  · have := time_stepBefore_succ_le x t'
    omega

/-- **A3, before `a_r` every honest finalized block is `L` or an ancestor of `L`.** The proof; the
audited statement is in `Statements/Executions/Lemma89Statements.lean`.

The route: `w`'s finalized block before `t` is the finalized block of the chain state of a block
`D` `w` holds then (`finalizedFromChain_of_exec`); `h_F(D) ≤ h_j(D) < h(D) ≤ H₂ + 1` (Lemma 47 (a)
and A2), so `h_F(D) < h(L)`, and Lemma 89a gives `F ⪯ L`, both holders being honest at their steps
by permanent corruption.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `tAwakeEnd`: the phase's end;
- `r`: the round; `H₂`: the bound; `t`: the time; `v`: the holder of `L`; `w`: the validator
  whose finalized block is read; `L`: the block.

Roots name blocks until `aR S r`: the proof compares (Lemma 89a) the block `B` `w` holds before
`t` with `L`, which `v` holds before `aR S r`, and `t ≤ aR S r`. -/
theorem finalized_ancestor_of_fast_block (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (tAwakeEnd r H₂ t : ℕ) (v w : V) (L : Block V)
    (hMono : Sched.MonotoneCorruption)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace) (hRoots : RootsNameBlocksUntil S Sched x (aR S r))
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    (hOld : OldAttestationsAtMost S Sched x (aR S r) H₂)
    (hEnd : aR S r ≤ tAwakeEnd)
    (hv : v ∉ Sched.adv ((aR S r : ℕ) : Int)) (hLv : L ∈ (stateBefore x (aR S r) v).S.T)
    (hL : (chainStateOf S.C L).h = H₂ + 1)
    (htr : t ≤ aR S r) (hw : w ∉ Sched.adv (t : Int)) :
    (stateBefore x t w).S.F.AncestorEq L := by
  obtain ⟨B, hB, hF⟩ := finalizedFromChain_of_exec S Sched x (stepBefore x t) w
  have hBh := held_height_le_before_action S Sched x tAwakeEnd r H₂ t w B hU hThird hOld htr hEnd
    hB
  obtain ⟨-, hj, hFj⟩ := (lem47_chain_state_heights S.C B B).1
  have hlt : (chainStateOf S.C B).h_F < (chainStateOf S.C L).h := by
    rw [hL]
    exact lt_of_le_of_lt hFj (lt_of_lt_of_le hj hBh)
  have hti := time_stepBefore_le x t
  have htj := time_stepBefore_le x (aR S r)
  have hT : AdversaryFewerThanThirdUntil Sched (validator_count V)
      (max (x[stepBefore x t].time : Int) (x[stepBefore x (aR S r)].time : Int)) :=
    adversaryFewerThanThirdUntil_of_le (max_le (by exact_mod_cast (show x[stepBefore x t].time ≤
      tAwakeEnd by omega)) (by exact_mod_cast (show x[stepBefore x (aR S r)].time ≤ tAwakeEnd by
      omega))) hThird
  have hw' : w ∉ Sched.adv (x[stepBefore x t].time : Int) :=
    fun h => hw (hMono _ _ (by exact_mod_cast hti) h)
  have hv' : v ∉ Sched.adv (x[stepBefore x (aR S r)].time : Int) :=
    fun h => hv (hMono _ _ (by exact_mod_cast htj) h)
  have hFL := lem68_honest_past_finalized S Sched x hU hRoots (stepBefore x t)
    (stepBefore x (aR S r)) w v B L hT hw' hv' hB hLv hlt (max_le (by omega) htj)
  show (x[stepBefore x t][w].st).S.F.AncestorEq L
  rw [hF]
  exact hFL

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
slot `s`, whose bound is that time. -/
theorem lem36c_fast_ancestor_extended_held (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s : ℕ) (C' L : Block V) (v w : V) (A' : ACState V)
    (vote : GoldfishVote V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
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
  exact lem21b_goldfish_vote_extends_eligible_block_held S Sched x GST s Sup L v w vote hDiv
    hMono hSync hCatch hRoots hParent hGST hv hw hSup' hElig' hF2 hF3 hLocks hSend

end GoldilocksCorrectness.Proofs.Executions
