module
public import GoldilocksCorrectness.Proofs.Executions.Lemma107
public import GoldilocksCorrectness.Statements.Routines.FinalityPairStatements

@[expose] public section

/-! The kit theorems:

- `attestation_duty_sends_at_source_head`: `attestation_duty_sends_at_source` (`Lemma55.lean`)
  with the head the duty reads named: a block `D` that `v` holds before the action time, `B` or a
  descendant of `B`;
- `entry_eq_of_ancestorEq_common`: two entry blocks at one chain-state height, both `D` or
  ancestors of `D`, are one block;
- `justified_entry_facts`: a chain state's justified block is an entry block, `B` or an ancestor
  of `B`, at the justification height.

 The member's record holds nothing at
`h(B)` (`hOldJ`), so its tick at the action time builds and sends a fresh target at `h(B)` from the
head `D`; `h_j(D) = h_j(B)` and `h_F(D) < h_j(B)`, since a certificate on `D`'s chain at a greater
height has an honest member whose attestation, sent before the action time, is higher than
`h_j(B)` (`justification_cert_height_le`, `finality_cert_height_lt`, against `hOldJ`); `J(D) = J(B)`
(both entries at `h_j(B)` on `D`'s chain); the record at `h_j(B)` holds no timeout, and no target or
lock but `J(B)`'s root (`hHJ`, Lemmas 82 and 83, the honest chain before `s` ending at `B`); Lemma
92 attaches the pair.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_mono one_le_Δ supportCutoff_cast
  supportCutoff_eq supportCutoff_mono supportCutoff_succ_times voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (lem47_chain_state_heights)
open GoldilocksCorrectness.Statements.Routines (IsEntry chainStateOf lem47f_justified_is_entry)

open GoldilocksCorrectness.Proofs.Routines (mem_fg_to_ac_tree)
open GoldilocksCorrectness.Statements.Routines (ChainStatesComputed)

open GoldilocksCorrectness.Proofs.Routines (ac_to_fg_head_mem)

open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_succ_lt_supportCutoff is_live_iff
  is_locked_iff)

open GoldilocksCorrectness.Proofs.Routines (mem_viable_tree_iff)

open GoldilocksCorrectness.Proofs.Routines (t_eq_mul)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (expireLocks lem15_tick_updates_confirmation
  lem48_attestation_source lem48b_anchor_is_locked_block lem49b_attestation_duty_runs
  lem50_attestation_sent_at_source fast_blocks_ancestorEq_saved lem66_chain_state_certified
  lem92_attestation_carries_finality_pair)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans ancestorEq_compatible
  lock_entry_of_saved_fast tick_attest_input awake_since_record_awake)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

-- An index `x[i]` into an execution has the valid-index predicate `fun _ _ => True`; this rule,
-- local to the file, proves it at once.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- `omega` after the `abbrev`s `Height` and `Slot` are unfolded in the goal and in every
hypothesis: `omega` does not see a fact stated at either. -/
local macro "omega_nat" : tactic =>
  `(tactic| ((try dsimp only) <;> (try unfold Height at *) <;> (try unfold Slot at *) <;> omega))

/-! ## Entry blocks on one chain -/

omit [RootOrder] in
/-- Two entry blocks at one chain-state height, each `D` or an ancestor of `D`, are one block.

Why: they are compatible (`ancestorEq_compatible`); of two blocks of one chain at one height, the
`T_h` is one (Lemma 47 (e)), and each is its own `T_h`.

The variables:
- `C`: the parameters; `E`, `E'`: the two entries; `D`: the block they are on the chain of. -/
theorem entry_eq_of_ancestorEq_common (C : Config) {E E' D : Block V} (hE : E.AncestorEq D)
    (hE' : E'.AncestorEq D) (hEe : IsEntry C E) (hEe' : IsEntry C E')
    (hh : (chainStateOf C E).h = (chainStateOf C E').h) : E = E' := by
  rcases ancestorEq_compatible hE hE' with h1 | h1
  · have := (lem47_chain_state_heights C E E').2.2.2.2 h1 hh
    unfold IsEntry at hEe hEe'
    rw [hEe, hEe'] at this
    exact this
  · have := (lem47_chain_state_heights C E' E).2.2.2.2 h1 hh.symm
    unfold IsEntry at hEe hEe'
    rw [hEe, hEe'] at this
    exact this.symm

omit [RootOrder] in
/-- A chain state's justified block, when the justification height is at least `1`, is `B` or an
ancestor of `B`, an entry block, at the justification height.

Why: it is the `T_h` of a block `Y` of `B`'s chain at that height (Lemma 47 (f)), and a `T_h` is an
entry block of its block's height, `Y` or an ancestor of `Y` (`isEntry_T_h`).

The variables:
- `C`: the parameters; `B`: the block whose justification is read. -/
theorem justified_entry_facts (C : Config) (B : Block V) (h1 : 1 ≤ (chainStateOf C B).h_j) :
    (chainStateOf C B).J.AncestorEq B ∧ IsEntry C (chainStateOf C B).J ∧
      (chainStateOf C (chainStateOf C B).J).h = (chainStateOf C B).h_j := by
  obtain ⟨Y, hYB, hYh, hYJ⟩ := lem47f_justified_is_entry C B _ rfl h1
  obtain ⟨hE, hh, hanc⟩ := GoldilocksCorrectness.Proofs.Routines.isEntry_T_h C Y
  rw [hYJ] at hE hh hanc
  exact ⟨ancestorEq_trans hanc hYB, hE, hh.trans hYh⟩

/-! ## The duty's head -/

/-- **Kit fact, what the duty sends, with its head.** Under the hypotheses of
`attestation_duty_sends_at_source` (`Lemma55.lean`), some block `D`, `B` or a descendant of `B`,
that `v` holds before the support cutoff of slot `s + 1`, is the head the duty reads: with `J(D)`
the root of `B`'s `T_h` when `h_j(D)` is `B`'s height, every attestation the validator client
builds from `v`'s record before that cutoff, the height and the root of `B`'s `T_h`, and
`(h_j(D), J(D), h_F(D))`, is put on the wire by `v` at its tick at that cutoff.

Why: the proof of `attestation_duty_sends_at_source`, which names the head `fi.head` of the duty's
input: it descends from the anchor `B` (Lemma 48b) and is in the tree (`ac_to_fg_head_mem`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `r`: the round; `s`: its first slot;
- `B`: the source; `v`: the validator; `A'`: the answer of `v`'s update of slot `s + 1`. -/
theorem attestation_duty_sends_at_source_head (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched)
    (r s : ℕ) (B : Block V) (v : V) (A' : ACState V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hs : s = r * S.C.R)
    (hv : ∀ t : ℕ, dutyWindowStart S (s + 1) ≤ t → t ≤ supportCutoff S (s + 1) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    (hUpdate : update_confirmation S.C S.P
        (expireLocks (stateBefore x (supportCutoff S (s + 1)) v).A
          ((supportCutoff S (s + 1) : ℕ) : Int))
        (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S)
        ((supportCutoff S (s + 1) : ℕ) : Int) (s + 1) = .ok A')
    (hSaved : A'.saved_confirmation s = some B)
    (hFast : B ∈ A'.fast_blocks)
    (hLocks : ∀ e ∈ A'.lock_entries,
      is_live (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S)
        ((supportCutoff S (s + 1) : ℕ) : Int) e = true → e.B.AncestorEq B)
    (hViable : B ∈ viable_tree (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S)
      (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S).tree) :
    ∃ D : Block V, B.AncestorEq D ∧ D ∈ (stateBefore x (supportCutoff S (s + 1)) v).S.T ∧
      ((chainStateOf S.C D).h_j = (chainStateOf S.C B).h →
        (chainStateOf S.C D).J.root = (chainStateOf S.C B).T_h.root) ∧
      ∀ a : Attestation V,
        (create_attestation (stateBefore x (supportCutoff S (s + 1)) v).Λ v
          (chainStateOf S.C B).h (chainStateOf S.C B).T_h.root (chainStateOf S.C D).h_j
          (chainStateOf S.C D).J.root (chainStateOf S.C D).h_F).2 = some a →
        ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (supportCutoff S (s + 1)) ∧
          (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈
            x[i + 1].sent - x[i].sent := by
  obtain ⟨hslot, -, hAction, hCutoff⟩ := supportCutoff_succ_times S r s hs
  have hΔ := one_le_Δ S
  have hΔpos := S.C.Δ_pos
  have hc1 : 1 ≤ supportCutoff S (s + 1) := by rw [supportCutoff_eq, voteTime_eq]; omega
  have hdw : dutyWindowStart S (s + 1) < supportCutoff S (s + 1) :=
    dutyWindowStart_succ_lt_supportCutoff S s
  obtain ⟨hvA, hvH⟩ := hv _ (le_of_lt hdw) le_rfl
  have hl : x.lbl (stepBefore x (supportCutoff S (s + 1))) =
      AtomicAction.tickAllAwake (supportCutoff S (s + 1)) := (stepBefore_spec x hDiv hc1).1
  obtain ⟨n', sent, hrun, -⟩ := tick_step_outcome x hl hvA hvH
  have hnS : (tickInputState x (stepBefore x (supportCutoff S (s + 1)))
      (supportCutoff S (s + 1)) v).S = (stateBefore x (supportCutoff S (s + 1)) v).S :=
    (tickInputState_frame x _ _ v).1
  have hnA : (tickInputState x (stepBefore x (supportCutoff S (s + 1)))
      (supportCutoff S (s + 1)) v).A = (stateBefore x (supportCutoff S (s + 1)) v).A :=
    (tickInputState_frame x _ _ v).2.1
  have hnΛ : (tickInputState x (stepBefore x (supportCutoff S (s + 1)))
      (supportCutoff S (s + 1)) v).Λ = (stateBefore x (supportCutoff S (s + 1)) v).Λ :=
    (tickInputState_record x _ _ v).1
  have hnv : (tickInputState x (stepBefore x (supportCutoff S (s + 1)))
      (supportCutoff S (s + 1)) v).v = v :=
    (tickInputState_record x _ _ v).2.trans (lem11_node_invariant S Sched x _ v).2.1
  -- the duty test
  obtain ⟨τ, hτ, hτle⟩ := awakeSince_le_dutyWindowStart_b S Sched x (s + 1)
    (supportCutoff S (s + 1)) v hDiv hMono hdw (fun t' h1 h2 => (hv t' h1 h2).1) hvH
  have hAwake : ∃ τ : Time, (tickInputState x (stepBefore x (supportCutoff S (s + 1)))
      (supportCutoff S (s + 1)) v).awakeSince = some τ ∧
      τ ≤ duty_window_start S.C (S.C.slot ((supportCutoff S (s + 1) : ℕ) : Int)) :=
    ⟨τ, hτ, by rw [hslot]; exact hτle⟩
  -- the update inside the tick is `hUpdate`'s
  obtain ⟨A'', hA'', -, hfb, hle, -⟩ := lem15_tick_updates_confirmation S.C S.P S.X _ n' _ sent
    hrun hCutoff hAwake
  rw [hslot, hnA, hnS, hUpdate] at hA''
  injection hA'' with hA''
  subst hA''
  -- the source is `B`, and the head descends from `B`
  have hFast' : B ∈ n'.A.fast_blocks := by rw [hfb]; exact hFast
  have hAnc : ∀ B' ∈ n'.A.fast_blocks, B'.AncestorEq B := by
    rw [hfb]
    exact fast_blocks_ancestorEq_saved S.C S.P _ A' _ _ (s + 1) B (Nat.succ_ne_zero s)
      hUpdate hSaved
  obtain ⟨hLE, hBΦ⟩ := lock_entry_of_saved_fast S.C S.P _ A' _ _ (s + 1) B
    (Nat.succ_ne_zero s) hUpdate hSaved hFast
  have hdl : ((supportCutoff S (s + 1) : ℕ) : Int) <
      S.C.t_ (s + 1 - 1 + S.C.k) + 5 * S.C.Δ := by
    rw [Nat.add_sub_cancel, supportCutoff_cast]
    have h1 : S.C.t_ (s + 1) ≤ S.C.t_ (s + S.C.k) := by
      simp only [t_eq_mul]
      have hk := S.C.k_ge_two
      exact Int.mul_le_mul_of_nonneg_left (by exact_mod_cast (by omega : s + 1 ≤ s + S.C.k))
        (Int.mul_nonneg (by decide) (le_of_lt S.C.Δ_pos))
    have key : ∀ a b d : Int, a ≤ b → 0 < d → a + 2 * d < b + 5 * d := by
      intro a b d h1 h2; omega
    exact key _ _ _ h1 hΔpos
  have hLocked : is_locked n'.A (fg_to_ac (tickInputState x (stepBefore x
      (supportCutoff S (s + 1))) (supportCutoff S (s + 1)) v).S)
      ((supportCutoff S (s + 1) : ℕ) : Int) B = true := by
    rw [is_locked_iff]
    rw [hle, hnS]
    exact ⟨_, hLE, (is_live_iff _ _ _).2 ⟨hdl, hBΦ⟩, ancestorEq_refl B⟩
  have hLocks' : ∀ e ∈ n'.A.lock_entries, is_live (fg_to_ac (tickInputState x (stepBefore x
      (supportCutoff S (s + 1))) (supportCutoff S (s + 1)) v).S)
      ((supportCutoff S (s + 1) : ℕ) : Int) e = true → e.B.AncestorEq B := by
    rw [hle, hnS]; exact hLocks
  have hViable' : B ∈ viable_tree (fg_to_ac (tickInputState x (stepBefore x
      (supportCutoff S (s + 1))) (supportCutoff S (s + 1)) v).S)
      (fg_to_ac (tickInputState x (stepBefore x
      (supportCutoff S (s + 1))) (supportCutoff S (s + 1)) v).S).tree := by
    rw [hnS]; exact hViable
  have hsrc := lem48_attestation_source S.C n'.A _ ((supportCutoff S (s + 1) : ℕ) : Int) B
    hFast' hAnc hViable'
  have hhead := (lem48b_anchor_is_locked_block S.C n'.A _ _ B hLocked hLocks' hViable').2
  -- the duty's input
  have hin := (tick_attest_input S.C S.P S.X _ _).of_outcome hrun
  obtain ⟨fi, hfi⟩ := hin hAction (awake_since_record_awake hτ (by rw [hslot]; exact hτle))
  have hfs := hsrc fi hfi
  have hBh := hhead fi hfi
  -- the node invariant: the chain states of the tree are the blocks' own
  have hinv := (lem11_node_invariant S Sched x (stepBefore x (supportCutoff S (s + 1))) v).1
  have hCSC : ChainStatesComputed S.C (tickInputState x (stepBefore x (supportCutoff S (s + 1)))
      (supportCutoff S (s + 1)) v).S := by
    rw [(tickInputState_frame x _ _ v).1]; exact hinv.2.2.2.2.2.1
  have hheadT := (ac_to_fg_head_mem S.C n'.A _ _
    (by rw [(tickInputState_frame x _ _ v).1]; exact hinv.2.2.2.1)
    (by rw [(tickInputState_frame x _ _ v).1]
        exact (lem57_justification_cache_and_record S Sched x _ v).2.2.1)
    (by rw [(tickInputState_frame x _ _ v).1]
        exact (lem46_finality_caches S Sched x _ v).1) fi hfi).1
  have hBT : B ∈ (tickInputState x (stepBefore x (supportCutoff S (s + 1)))
      (supportCutoff S (s + 1)) v).S.T :=
    ((mem_fg_to_ac_tree _ _).1 ((mem_viable_tree_iff _ _ _).1 hViable').1).1
  have hσB := hCSC B hBT
  have hσh := hCSC fi.head hheadT
  refine ⟨fi.head, hBh, by rw [← hnS]; exact hheadT, fun h => ?_, fun a ha => ?_⟩
  · rw [J_eq_T_h_of_same_height S.C B fi.head hBh h]
  · have hbuilt : (create_attestation
        (tickInputState x (stepBefore x (supportCutoff S (s + 1))) (supportCutoff S (s + 1)) v).Λ
        (tickInputState x (stepBefore x (supportCutoff S (s + 1))) (supportCutoff S (s + 1)) v).v
        ((tickInputState x (stepBefore x (supportCutoff S (s + 1)))
          (supportCutoff S (s + 1)) v).S.σ B).h
        ((tickInputState x (stepBefore x (supportCutoff S (s + 1)))
          (supportCutoff S (s + 1)) v).S.σ B).T_h.root
        ((tickInputState x (stepBefore x (supportCutoff S (s + 1)))
          (supportCutoff S (s + 1)) v).S.σ fi.head).h_j
        ((tickInputState x (stepBefore x (supportCutoff S (s + 1)))
          (supportCutoff S (s + 1)) v).S.σ fi.head).J.root
        ((tickInputState x (stepBefore x (supportCutoff S (s + 1)))
          (supportCutoff S (s + 1)) v).S.σ fi.head).h_F).2 = some a := by
      rw [hnΛ, hnv, hσB, hσh]; exact ha
    have hsent := lem49b_attestation_duty_runs S.C S.P S.X _ n' _ sent a fi B hrun hAction
      hAwake hfi hfs hbuilt
    exact ⟨_, hl, step_sent_of_tick_send hl (Finset.mem_sdiff.2 ⟨hvA, hvH⟩) hrun hsent⟩

/-! ## Lemma 94 -/

/-- **Lemma 94, the round's attesters after healing carry the finality pair.** The proof; the
audited statement is in `Statements/Executions/FinalityLivenessStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₂`: the hand-over step; `H`: the threshold;
- `r`: the round; `s`: its first slot; `B`: the proposal; `u`: the member. -/
theorem lem94_round_attesters_after_healing (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ anchor i₂ H r s : ℕ) (B : Block V) (u : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s + 1)))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hSleepK : CommitteeSleepiness S Sched anchor) (hAnchor : anchor ≤ x[i₂].time)
    (hGST : GST ≤ voteTime S s₀) (ht₀ : supportCutoff S (s₀ + 1) ≤ x[i₂].time)
    (hChain : ConfirmationsChainBefore S Sched x s₀ (s + 1))
    (hInv : ∀ s' : ℕ, s₀ < s' → s' ≤ s →
      ChainInvFor S Sched x (honestActiveAt S Sched s') (OnHonestChainBefore S Sched x s₀ s') s')
    (hLocks : ∀ s' : ℕ, s₀ < s' → s' ≤ s → ∀ w ∈ honestActiveAt S Sched s',
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ s') s' w)
    (hLocks₀ : ∀ w ∈ honestActiveAt S Sched s₀,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ (s₀ + 1)) s₀ w)
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (w : V), x[i₂].time ≤ x[j].time → x[j].time ≤ supportCutoff S (s + 1) →
      w ∉ Sched.adv (x[j].time : Int) → CachesOnChain S Sched x s₀ H (x[j][w].st))
    (hs : s = r * S.C.R) (hAfter : x[i₂].time < slotStart S s)
    (hOpener : HonestOpenerAt S Sched s)
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s) ∧
      (⟨S.P.proposer s, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent)
    (hNoCollision : ¬ RootCollisionAtProposal S Sched x s B)
    (hOldJ : OldAttestationsAtMost S Sched x (supportCutoff S (s + 1)) (chainStateOf S.C B).h_j)
    (hHJ : H < (chainStateOf S.C B).h_j)
    (hu : u ∈ honestActiveAt S Sched s) :
    ∃ (i : ℕ) (a : Attestation V), x.lbl i = AtomicAction.tickAllAwake (supportCutoff S (s + 1)) ∧
      (⟨u, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent ∧
      a.val_index = u ∧ a.h = (chainStateOf S.C B).h ∧ a.T = (chainStateOf S.C B).T_h.root ∧
      a.τ = false ∧
      ((chainStateOf S.C B).h_F < (chainStateOf S.C B).h_j →
        a.finality_pair =
          some (FinalityPair.mk (chainStateOf S.C B).h_j (chainStateOf S.C B).J.root)) := by
  have hChain' : ConfirmationsChainBefore S Sched x s₀ s :=
    fun a b c d e f h1 h2 h3 => hChain a b c d e f h1 h2 (by omega)
  obtain ⟨hChainB, hBslot, -, -, ⟨A', hUpd, hSv, hFb⟩, hRev, hρ, hφ, hBin, hBox⟩ :=
    round_member_frame_after_healing S Sched x GST s₀ anchor i₂ H s B u hDiv hMono hSync hCatch
      hRoots hParent hOwner hU hAdvQ hSleepK hAnchor hGST ht₀ hChain' hInv hLocks hLocks₀ hOld
      hCaches hAfter hOpener hPropose hNoCollision hu
  have hΔ := one_le_Δ S
  have hdw : dutyWindowStart S s ≤ dutyWindowStart S (s + 1) := dutyWindowStart_mono S (by omega)
  have hv : ∀ t : ℕ, dutyWindowStart S (s + 1) ≤ t → t ≤ supportCutoff S (s + 1) →
      u ∈ Sched.awake (t : Int) ∧ u ∉ Sched.adv (t : Int) := fun t h1 h2 =>
    honestActiveAt_window S Sched s u hMono hu t (le_trans hdw h1) h2
  have hLk := update_lock_entries_ancestorEq S Sched x s B u A' hDiv hMono hv hUpd hSv hBslot hRev
  obtain ⟨hViable, hRecord⟩ := lem61_frame_hypotheses S Sched x s B u _ _ ⟨rfl, rfl⟩ hρ hφ hBin
    hBox
  have hBh := (lem47_chain_state_heights S.C B B).1
  -- the step before the action time
  have hc1 : 1 ≤ supportCutoff S (s + 1) := by rw [supportCutoff_eq, voteTime_eq]; omega
  set j₀ := stepBefore x (supportCutoff S (s + 1)) with hj₀
  have htj₀ : x[j₀].time + 1 = supportCutoff S (s + 1) := time_stepBefore_add_one x hDiv hc1
  have hlt₀ : x[j₀].time < supportCutoff S (s + 1) := by omega
  -- `u`'s record before the action time holds nothing at `h(B)` (`hOldJ`)
  have hFresh : ∀ b ∈ (stateBefore x (supportCutoff S (s + 1)) u).Λ.sent,
      b.h ≠ (chainStateOf S.C B).h := by
    intro b hb hbh
    obtain ⟨j, t', a, hl, ht', hAw, hHon, hsent, -, hac, -⟩ :=
      record_content_sent S Sched x _ u b hDiv hb
    have hle := hOldJ j t' u a hl ht' hAw hHon hsent
    have hah : a.h = b.h := by rw [← hac]; rfl
    rw [hah, hbh] at hle
    omega_nat
  -- the duty's head `D`, and the attestation it builds and sends
  obtain ⟨D, hBD, hDT, hJD, hsend⟩ := attestation_duty_sends_at_source_head S Sched x r s B u A'
    hDiv hMono hs hv hUpd hSv hFb hLk hViable
  have htimeout : (stateBefore x (supportCutoff S (s + 1)) u).Λ.timeout
      (chainStateOf S.C B).h = false := by
    cases h : (stateBefore x (supportCutoff S (s + 1)) u).Λ.timeout (chainStateOf S.C B).h with
    | false => rfl
    | true =>
        obtain ⟨b, hb, hbh, -⟩ := ((recordConsistent_of_exec S Sched x j₀ u).timeoutRec _).1 h
        exact absurd hbh (hFresh b hb)
  have htarget : (stateBefore x (supportCutoff S (s + 1)) u).Λ.target
      (chainStateOf S.C B).h = none := by
    cases h : (stateBefore x (supportCutoff S (s + 1)) u).Λ.target (chainStateOf S.C B).h with
    | none => rfl
    | some T =>
        obtain ⟨b, hb, hbh, -⟩ := target_sent_of_stateBefore S Sched x _ u _ _ h
        exact absurd hbh (hFresh b hb)
  obtain ⟨a, hbuilt, hav, hah, haT, hτ⟩ := (lem50_attestation_sent_at_source _ u _ _ _ _ _
      hRecord hJD (target_sent_of_stateBefore S Sched x _ u)
      (sent_target_recorded_of_stateBefore S Sched x _ u)
      (timeout_recorded_of_stateBefore S Sched x _ u)).2 hFresh htimeout htarget
  obtain ⟨i, hl, hm⟩ := hsend a hbuilt
  refine ⟨i, a, hl, hm, hav, hah, haT, hτ, fun hFj => ?_⟩
  -- the finality pair
  have hj1 : 1 ≤ (chainStateOf S.C B).h_j := by omega_nat
  have hjD := GoldilocksCorrectness.Proofs.Routines.chainStateOf_h_j_h_F_mono S.C B D hBD
  have hDT' : D ∈ (x[j₀][u].st).S.T := hDT
  -- `h_j(D) = h_j(B)`: a justification on `D`'s chain above `h_j(B)` has an honest member
  -- higher than `h_j(B)` before the action time
  have hjeq : (chainStateOf S.C D).h_j = (chainStateOf S.C B).h_j := by
    by_contra hne
    have hgt : (chainStateOf S.C B).h_j < (chainStateOf S.C D).h_j :=
      lt_of_le_of_ne hjD.1 (Ne.symm hne)
    have hcert := ((lem66_chain_state_certified S.C D).1 (by omega_nat)).1
    have := justification_cert_height_le S Sched x _ _ j₀ u D _ _ hU (hAdvQ _) hOldJ hlt₀ hDT'
      hcert
    omega_nat
  -- `h_F(D) < h_j(B)`: likewise for a finalization
  have hFlt : (chainStateOf S.C D).h_F < (chainStateOf S.C B).h_j := by
    by_contra hge
    have hF1 : 1 ≤ (chainStateOf S.C D).h_F := by omega_nat
    have hcert := ((lem66_chain_state_certified S.C D).2.2 hF1).2.1
    have := finality_cert_height_lt S Sched x _ _ j₀ u D _ _ hU (hAdvQ _) hOldJ hlt₀ hDT' hcert
    omega_nat
  -- `J(D) = J(B)`: both entries at `h_j(B)` on `D`'s chain
  obtain ⟨hJBB, hJBe, hJBh⟩ := justified_entry_facts S.C B hj1
  obtain ⟨hJDD, hJDe, hJDh⟩ := justified_entry_facts S.C D (by omega_nat)
  have hJeq : (chainStateOf S.C D).J = (chainStateOf S.C B).J :=
    entry_eq_of_ancestorEq_common S.C hJDD (ancestorEq_trans hJBB hBD) hJDe hJBe
      (by rw [hJDh, hJBh, hjeq])
  -- every attestation of `u` at `h_j(B)` sent before the action time is a target for `J(B)`
  have hrecJ : ∀ b ∈ (stateBefore x (supportCutoff S (s + 1)) u).Λ.sent,
      b.h = (chainStateOf S.C B).h_j → b.τ = false ∧ b.T = (chainStateOf S.C B).J.root := by
    intro b hb hbh
    obtain ⟨j, t', a', hl', ht', hAw', hHon', hsent', -, hac, -⟩ :=
      record_content_sent S Sched x _ u b hDiv hb
    have ha'h : a'.h = (chainStateOf S.C B).h_j := by rw [← hbh, ← hac]; rfl
    rcases Nat.lt_or_ge t' (supportCutoff S (s₀ + 1)) with hlt | hge
    · have := hOld j t' u a' hl' hlt hAw' hHon' hsent'
      rw [ha'h] at this
      omega_nat
    have hτ' := no_honest_timeout_after_healing_before S Sched x s₀ H (s + 1) j t' u a' hDiv hMono
      hChain hOld hl' hge ht'.le hAw' hHon' hsent' (by rw [ha'h]; exact hHJ)
    obtain ⟨s_a, E, -, hts, ⟨hs₀a, w, hw, C, hC, hEC⟩, hEe, hEh, hET⟩ :=
      lem82_honest_attestations_on_chain S Sched x s₀ hDiv hMono j t' u a' hl' hge hAw' hHon'
        hsent'
    have hsa : s_a < s := by
      by_contra hn
      have := supportCutoff_mono S (show s + 1 ≤ s_a + 1 by omega)
      omega
    have hEB := hChainB E ⟨s_a, hsa, hs₀a, w, hw, C, hC, hEC⟩
    have hEJ := entry_eq_of_ancestorEq_common S.C hEB hJBB hEe hJBe (by rw [hEh, hJBh, ha'h])
    refine ⟨by rw [← hac]; exact hτ', ?_⟩
    rw [← hac]
    show a'.T = _
    rw [hET, hEJ]
  have hTo : (stateBefore x (supportCutoff S (s + 1)) u).Λ.timeout
      (chainStateOf S.C B).h_j = false := by
    cases h : (stateBefore x (supportCutoff S (s + 1)) u).Λ.timeout (chainStateOf S.C B).h_j with
    | false => rfl
    | true =>
        obtain ⟨b, hb, hbh, hbτ⟩ := ((recordConsistent_of_exec S Sched x j₀ u).timeoutRec _).1 h
        have := (hrecJ b hb hbh).1
        rw [hbτ] at this
        cases this
  have hTg : (stateBefore x (supportCutoff S (s + 1)) u).Λ.target (chainStateOf S.C B).h_j = none ∨
      (stateBefore x (supportCutoff S (s + 1)) u).Λ.target (chainStateOf S.C B).h_j =
        some (chainStateOf S.C B).J.root := by
    cases h : (stateBefore x (supportCutoff S (s + 1)) u).Λ.target (chainStateOf S.C B).h_j with
    | none => exact Or.inl rfl
    | some T' =>
        obtain ⟨b, hb, hbh, hbT⟩ := target_sent_of_stateBefore S Sched x _ u _ _ h
        right
        rw [← hbT, (hrecJ b hb hbh).2]
  -- a lock at `h_j(B)` names the honest chain's entry there (Lemma 83), which is `J(B)`
  have hLkJ : (stateBefore x (supportCutoff S (s + 1)) u).Λ.lock (chainStateOf S.C B).h_j = none ∨
      (stateBefore x (supportCutoff S (s + 1)) u).Λ.lock (chainStateOf S.C B).h_j =
        some (chainStateOf S.C B).J.root := by
    cases hlk : (stateBefore x (supportCutoff S (s + 1)) u).Λ.lock (chainStateOf S.C B).h_j with
    | none => exact Or.inl rfl
    | some T' =>
        right
        obtain ⟨j', hj', D', hD'T, h1', hD'j, hD'J⟩ := lock_justified_of_exec S Sched x j₀ u _ T' hlk
        have hcert := ((lem66_chain_state_certified S.C D').1 (hD'j ▸ h1')).1
        rw [hD'j] at hcert
        obtain ⟨s_a, E, hcut, ⟨hs₀a, w, hw, C, hC, hEC⟩, hEe, hEh, hEr⟩ :=
          lem83_one_justification_greater_than_threshold S Sched x s₀ (supportCutoff S (s₀ + 1)) H
            j' u D' _ _ hU (hAdvQ _) (lem82_honest_attestations_on_chain S Sched x s₀ hDiv hMono)
            (oldAttestationsAtMostHonestAt_of_oldAttestationsAtMost S Sched x _ _ H hOld) hD'T
            hcert hHJ
        have hj'j : x[j'].time ≤ x[j₀].time := time_mono x (Nat.le_of_lt hj')
        have hsa : s_a < s := by
          by_contra hn
          have := supportCutoff_mono S (show s + 1 ≤ s_a + 1 by omega)
          omega
        have hEB := hChainB E ⟨s_a, hsa, hs₀a, w, hw, C, hC, hEC⟩
        have hEJ := entry_eq_of_ancestorEq_common S.C hEB hJBB hEe hJBe (by rw [hEh, hJBh])
        rw [← hD'J, hEr, hEJ]
  -- Lemma 92
  have hpair := lem92_attestation_carries_finality_pair _ u _ _ _ _ _ a hbuilt
    (by rw [hjeq]; exact hFlt) (by rw [hjeq]; exact hBh.2.1) (by rw [hjeq, hJeq]; exact hTg)
    (by rw [hjeq]; exact hTo) (by rw [hjeq, hJeq]; exact hLkJ)
  rw [hpair.2, hjeq, hJeq]

end GoldilocksCorrectness.Proofs.Executions
