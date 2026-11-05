module
public import GoldilocksCorrectness.Statements.Routines.AttestationStatements
public import GoldilocksCorrectness.Statements.Routines.TickStatements
public import GoldilocksCorrectness.Statements.Routines.ConfirmationStatements
public import GoldilocksCorrectness.Statements.Executions.InvariantStatements
public import GoldilocksCorrectness.Statements.Executions.ChainStateStatements
public import GoldilocksCorrectness.Statements.Executions.WakeStatements
public import GoldilocksCorrectness.Proofs.Executions.BlockPropagation
public import GoldilocksCorrectness.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Proofs.Routines.Confirmation
public import GoldilocksCorrectness.Proofs.Routines.NodeTick

@[expose] public section

/-!
# Lemma 55: every honest validator with the honest proposal as its source attests for its height

The proofs of `lem55_honest_validator_attests_for_height` and `lem55_target_of_fresh_height`,
stated in `GoldilocksCorrectness/Statements/Executions/HeightAttestationStatements.lean`, and the
kit facts they need: the lock entry an update adds on a saved fast confirmation
(`lock_entry_of_saved_fast`), the answer of `ac_to_fg` inside a tick that runs the attestation duty
(`tick_attest_input`), the times of the support cutoff of slot `s + 1` when `s` is the first slot
of a round (`supportCutoff_succ_times`), and what the duty sends (`attestation_duty_sends_at_source`).

The route: at the support cutoff of slot `s + 1`, which is the action time of the round, `v`'s
tick passes the duty test (Lemma 16b's route), runs the confirmation update of slot `s + 1`, whose
answer is the `A'` of the hypotheses (Lemma 15), and then the attestation duty on that answer. The
duty's source is `B` (Lemma 48) and its head descends from `B` (Lemma 48b, `B` being locked by the
entry the update added); the head's justification at `B`'s height is `B`'s `T_h`
(`J_eq_T_h_of_same_height`), so the validator client builds an attestation at `B`'s height naming
`B`'s `T_h`, or builds none because the record already sent one (Lemma 50, with the record facts of
the node invariant); and the tick sends what it builds (Lemma 49b).
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (supportCutoff dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ supportCutoff_cast supportCutoff_eq
  supportCutoff_succ_times voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (is_live_iff is_locked_iff mem_viable_tree_iff)

open GoldilocksCorrectness.Proofs.Routines (wake_eq)

open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_succ_lt_supportCutoff)

open GoldilocksCorrectness.Proofs.Routines (t_eq_mul)

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Statements.Routines
open GoldilocksCorrectness.Proofs.Routines (propose_block_sends record_awake_frame)
open GoldilocksCorrectness.Proofs.Routines (ac_on_tick_sends)
open GoldilocksCorrectness.Proofs.Routines (DREBEmits)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

end GoldilocksCorrectness.Proofs.Routines

namespace GoldilocksCorrectness.Proofs.Executions

open GoldilocksCorrectness.Proofs.Routines (ac_to_fg_head_mem)

open GoldilocksCorrectness.Proofs.Routines (mem_fg_to_ac_tree)
open GoldilocksCorrectness.Statements.Routines (ChainStatesComputed)

open GoldilocksCorrectness.Statements.Routines (chainStateOf)

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (expireLocks lem15_tick_updates_confirmation
  lem48_attestation_source lem48b_anchor_is_locked_block lem49b_attestation_duty_runs
  lem50_attestation_sent_at_source fast_blocks_ancestorEq_saved)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl lock_entry_of_saved_fast
  tick_attest_input awake_since_record_awake)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- The node state a tick starts from has the validator's record and validator field: a wake
writes `awakeSince` only.

The variables:
- `x`: the execution; `i`: the step; `t`: the time of the tick; `v`: the validator. -/
theorem tickInputState_record {S : Setup V} {Sched : Schedule V}
    (x : AtomicExec (protocol S) Sched) (i t : ℕ) (v : V) :
    (tickInputState x i t v).Λ = (x[i][v].st).Λ ∧ (tickInputState x i t v).v = (x[i][v].st).v := by
  unfold tickInputState
  split <;> (try rw [wake_eq]) <;> exact ⟨rfl, rfl⟩

/-- **Kit fact, what the duty sends.** Under Lemma 55's hypotheses other than the record's, some
justification height `h_j`, justified root `J` and finalization height `h_F`, with `J` the root of
`B`'s `T_h` when `h_j` is `B`'s height, are such that every attestation the validator client builds
from `v`'s record before the support cutoff of slot `s + 1`, the height and the root of `B`'s
`T_h`, and `(h_j, J, h_F)`, is put on the wire by `v` at its tick at that cutoff.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `r`: the round; `s`: its first slot;
- `B`: the source; `v`: the validator; `A'`: the answer of `v`'s update of slot `s + 1`.

Read aloud: `v`'s tick at the round's action time sends what the client builds for `B`'s height
and `T_h` from the head the duty reads. -/
theorem attestation_duty_sends_at_source (S : Setup V) (Sched : Schedule V)
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
    ∃ (h_j : Height) (J : BlockId) (h_F : Height),
      (h_j = (chainStateOf S.C B).h → J = (chainStateOf S.C B).T_h.root) ∧
      ∀ a : Attestation V,
        (create_attestation (stateBefore x (supportCutoff S (s + 1)) v).Λ v
          (chainStateOf S.C B).h (chainStateOf S.C B).T_h.root h_j J h_F).2 = some a →
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
  refine ⟨(chainStateOf S.C fi.head).h_j, (chainStateOf S.C fi.head).J.root,
    (chainStateOf S.C fi.head).h_F, fun h => ?_, fun a ha => ?_⟩
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


/-- **Lemma 55, every honest validator with the honest proposal as its source attests for its
height.** The proof; the audited statement is in
`Statements/Executions/HeightAttestationStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `r`: the round; `s`: its first slot;
- `B`: the source; `v`: the validator; `A'`: the answer of `v`'s update of slot `s + 1`. -/
theorem lem55_honest_validator_attests_for_height (S : Setup V) (Sched : Schedule V)
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
      (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S).tree)
    (hRecord : (stateBefore x (supportCutoff S (s + 1)) v).Λ.lock (chainStateOf S.C B).h = none ∨
      ((stateBefore x (supportCutoff S (s + 1)) v).Λ.lock (chainStateOf S.C B).h =
          some (chainStateOf S.C B).T_h.root ∧
        ∀ b ∈ (stateBefore x (supportCutoff S (s + 1)) v).Λ.sent,
          b.h = (chainStateOf S.C B).h → b.T = (chainStateOf S.C B).T_h.root)) :
    (∃ (i : ℕ) (a : Attestation V), x.lbl i = AtomicAction.tickAllAwake (supportCutoff S (s + 1)) ∧
      (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent ∧
      a.val_index = v ∧ a.h = (chainStateOf S.C B).h ∧ a.T = (chainStateOf S.C B).T_h.root) ∨
    (∃ b ∈ (stateBefore x (supportCutoff S (s + 1)) v).Λ.sent,
      b.h = (chainStateOf S.C B).h ∧ b.T = (chainStateOf S.C B).T_h.root) := by
  obtain ⟨h_j, J, h_F, hJ, hsend⟩ := attestation_duty_sends_at_source S Sched x r s B v A' hDiv
    hMono hs hv hUpdate hSaved hFast hLocks hViable
  rcases (lem50_attestation_sent_at_source _ v _ _ h_j J h_F hRecord hJ
      (target_sent_of_stateBefore S Sched x _ v) (sent_target_recorded_of_stateBefore S Sched x _ v)
      (timeout_recorded_of_stateBefore S Sched x _ v)).1 with
    ⟨a, hbuilt, hav, hah, haT⟩ | ⟨-, b, hb, hbh, hbT⟩
  · obtain ⟨i, hl, hm⟩ := hsend a hbuilt
    exact Or.inl ⟨i, a, hl, hm, hav, hah, haT⟩
  · exact Or.inr ⟨b, hb, hbh, hbT⟩

/-- **Corollary of Lemma 55, a fresh height gets a target.** The proof; the audited statement is
in `Statements/Executions/HeightAttestationStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `r`: the round; `s`: its first slot;
- `B`: the source; `v`: the validator; `A'`: the answer of `v`'s update of slot `s + 1`. -/
theorem lem55_target_of_fresh_height (S : Setup V) (Sched : Schedule V)
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
      (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S).tree)
    (hRecord : (stateBefore x (supportCutoff S (s + 1)) v).Λ.lock (chainStateOf S.C B).h = none ∨
      ((stateBefore x (supportCutoff S (s + 1)) v).Λ.lock (chainStateOf S.C B).h =
          some (chainStateOf S.C B).T_h.root ∧
        ∀ b ∈ (stateBefore x (supportCutoff S (s + 1)) v).Λ.sent,
          b.h = (chainStateOf S.C B).h → b.T = (chainStateOf S.C B).T_h.root))
    (hFresh : ∀ b ∈ (stateBefore x (supportCutoff S (s + 1)) v).Λ.sent,
      b.h ≠ (chainStateOf S.C B).h) :
    ∃ (i : ℕ) (a : Attestation V), x.lbl i = AtomicAction.tickAllAwake (supportCutoff S (s + 1)) ∧
      (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent ∧
      a.val_index = v ∧ a.h = (chainStateOf S.C B).h ∧ a.T = (chainStateOf S.C B).T_h.root ∧
      a.τ = false := by
  obtain ⟨h_j, J, h_F, hJ, hsend⟩ := attestation_duty_sends_at_source S Sched x r s B v A' hDiv
    hMono hs hv hUpdate hSaved hFast hLocks hViable
  have htimeout : (stateBefore x (supportCutoff S (s + 1)) v).Λ.timeout
      (chainStateOf S.C B).h = false := by
    cases h : (stateBefore x (supportCutoff S (s + 1)) v).Λ.timeout (chainStateOf S.C B).h with
    | false => rfl
    | true =>
        obtain ⟨b, hb, hbh, -⟩ := ((recordConsistent_of_exec S Sched x
          (stepBefore x (supportCutoff S (s + 1))) v).timeoutRec _).1 h
        exact absurd hbh (hFresh b hb)
  have htarget : (stateBefore x (supportCutoff S (s + 1)) v).Λ.target
      (chainStateOf S.C B).h = none := by
    cases h : (stateBefore x (supportCutoff S (s + 1)) v).Λ.target (chainStateOf S.C B).h with
    | none => rfl
    | some T =>
        obtain ⟨b, hb, hbh, -⟩ := target_sent_of_stateBefore S Sched x _ v _ _ h
        exact absurd hbh (hFresh b hb)
  obtain ⟨a, hbuilt, hav, hah, haT, hτ⟩ := (lem50_attestation_sent_at_source _ v _ _ h_j J h_F
      hRecord hJ (target_sent_of_stateBefore S Sched x _ v)
      (sent_target_recorded_of_stateBefore S Sched x _ v)
      (timeout_recorded_of_stateBefore S Sched x _ v)).2 hFresh htimeout htarget
  obtain ⟨i, hl, hm⟩ := hsend a hbuilt
  exact ⟨i, a, hl, hm, hav, hah, haT, hτ⟩

end GoldilocksCorrectness.Proofs.Executions
