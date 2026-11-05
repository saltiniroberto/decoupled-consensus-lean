module
public import GoldilocksCorrectness.Proofs.View.Bridges
public import GoldilocksCorrectness.Statements.Executions.ConfirmedTipDefs
public import GoldilocksCorrectness.Proofs.Routines.ConfirmedTip
public import GoldilocksCorrectness.Statements.Executions.SleepyStatements
public import GoldilocksCorrectness.Statements.Executions.HonestChainAfterHealingStatements
public import GoldilocksCorrectness.Statements.Executions.HealedCachesStatements
public import GoldilocksCorrectness.Statements.Executions.HonestChainStatements
public import GoldilocksCorrectness.Statements.Executions.LockProvenanceStatements
public import GoldilocksCorrectness.Statements.Executions.InvariantStatements
public import GoldilocksCorrectness.Statements.Executions.WakeStatements
public import GoldilocksCorrectness.Proofs.Executions.ConfirmationSteps
public import GoldilocksCorrectness.Proofs.Executions.LockSteps
public import GoldilocksCorrectness.Proofs.Executions.Monotone
public import GoldilocksCorrectness.Proofs.Executions.Clock
public import GoldilocksCorrectness.Proofs.Executions.Wake
public import GoldilocksCorrectness.Proofs.Executions.RoundKit
public import GoldilocksCorrectness.Proofs.Executions.Lemma84
public import GoldilocksCorrectness.Proofs.Executions.Lemma91
public import GoldilocksCorrectness.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Proofs.Routines.Locks
public import GoldilocksCorrectness.Proofs.Routines.ACInterfaceTick
public import GoldilocksCorrectness.Proofs.Routines.Node
public import GoldilocksCorrectness.Proofs.Routines.NodeTick

@[expose] public section

/-!
# Lemma 90: the confirmed tip after the healed slot

The proofs of `lem90a_latest_confirmed_honest` and of Lemma 90's agreement and growth
(`lem90_confirmed_agree`, `lem90_confirmed_monotone`), stated in
`GoldilocksCorrectness/Statements/Executions/ConfirmedTipStatements.lean`, and the kit facts they
use:

- what a tick and a step do to the record of the confirmed tip (`ac_on_tick_latest_cases`,
  `tick_latest_cases`, `step_cases_latest`): they keep it, except the validator's own
  confirmation update at a support cutoff;
- `latest_confirmed_mem_T_of_exec`: the record is a block of the validator's tree, at every step;
- `latest_confirmed_slot_le`: before the support cutoff of slot `s + 1`, the record's slot is at
  most `s`;
- `latest_confirmed_after_healed_update`: right after the update of the healed slot `s₀`, every
  validator honest at its time holds `B₀` as its record.


-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_succ_le_slotStart one_le_Δ slotStart_eq
  slot_eq_of_mem supportCutoff_cast supportCutoff_eq supportCutoff_lt_of_lt supportCutoff_slot_eq
  voteTime_cast voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (DREBPost DREBPost.bind DREBPost.ite DREBPost.liftM
  DREBPost.pure DREPost DREPost.bind_any DREPost.dite DREPost.ite DREPost.pure)

open GoldilocksCorrectness.Proofs.Routines (mem_fg_to_ac_tree)

open GoldilocksCorrectness.Proofs.Routines (revoke_locks_latest update_confirmation_saved_mem
  update_confirmation_zero)

open GoldilocksCorrectness.Proofs.Routines (confirmedOf_ancestorEq_of
  slot_lt_of_ancestorEq_of_treeClosed tick_latest_cases)
open GoldilocksCorrectness.Statements.Routines (confirmedOf)

open GoldilocksCorrectness.Proofs.Routines (acState_initial_eq fg_to_ac_F initial_eq is_live_iff)

open GoldilocksCorrectness.Proofs.Routines (fgState_initial_eq)

open GoldilocksCorrectness.Proofs.Routines (duty_window_start_le_dutyWindowStart)

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicAction AtomicExec Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (expireLocks)
open GoldilocksCorrectness.Proofs.Routines (KeepsConfirmation tick_ac_on_tick voteTime_ne_cutoff
  goldfish_vote_keepsConfirmation receive_keeps_confirmation update_confirmation_latest_cases
  update_confirmation_latest_confirmed advance_some ac_confirmed_cases)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-! ## What a tick and a step do to the record -/

section Steps

variable {S : Setup V} {Sched : Schedule V}

/-- What a step does to a validator's record of the confirmed tip: it keeps it; or it is the tick
of every awake validator at a time `t` at which the validator is awake and honest, `t` is the
support cutoff of its slot, the tick starts from a state whose `awakeSince` is some time at most
the duty window's start of that slot, and the step leaves the saved confirmations and the record
of the confirmation update of that slot on the validator's AC state with its expired entries
removed.

The variables:
- `x`: the execution; `i`: the step; `v`: the validator.

Read aloud: only the validator's own confirmation update, at its time, writes its record of the
confirmed tip. -/
theorem step_cases_latest (x : AtomicExec (protocol S) Sched) (i : ℕ) (v : V) :
    (x[i + 1][v].st).A.latest_confirmed = (x[i][v].st).A.latest_confirmed ∨
    (∃ t : ℕ, x.lbl i = AtomicAction.tickAllAwake t ∧
      v ∈ Sched.awake (t : Int) \ Sched.adv (t : Int) ∧
      (t : Int) = S.C.t_ (S.C.slot t) + 2 * S.C.Δ ∧
      (∃ τ : Time, (tickInputState x i t v).awakeSince = some τ ∧
        τ ≤ duty_window_start S.C (S.C.slot t)) ∧
      ∃ A'' : ACState V,
        update_confirmation S.C S.P (expireLocks (x[i][v].st).A t) (fg_to_ac (x[i][v].st).S) t
          (S.C.slot t) = .ok A'' ∧
        (x[i + 1][v].st).A.saved_confirmation = A''.saved_confirmation ∧
        (x[i + 1][v].st).A.latest_confirmed = A''.latest_confirmed) := by
  rcases step_cases x i v with h | ⟨t, n', sent, hl, hmem, hrun, h⟩ | ⟨sm, -, -, -, h⟩
  · rw [h]
    exact Or.inl rfl
  · obtain ⟨hS, hA, -⟩ := tickInputState_frame x i t v
    rw [h]
    rcases tick_latest_cases S.C S.P S.X _ n' (t : Int) sent hrun with
      h1 | ⟨h1, h2, A'', hA'', h3, h4⟩
    · rw [hA] at h1
      exact Or.inl h1
    · rw [hA, hS] at hA''
      exact Or.inr ⟨t, hl, hmem, h1, h2, A'', hA'', h3, h4⟩
  · rw [h]
    exact Or.inl (receive_keeps_confirmation S.C S.P S.X (x[i][v].st) sm.msg).2.2.2

end Steps

/-! ## The record over an execution -/

section Record

variable {S : Setup V} {Sched : Schedule V}

/-- **Kit fact, the record of the confirmed tip is held.** At every step of every execution, a
validator's record of the confirmed tip is a block of its FG state's tree.

Why: the record is the genesis block initially; a step that changes it is the validator's
confirmation update, which writes the confirmation it saves
(`update_confirmation_latest_confirmed`), held by the kit fact
`saved_confirmation_mem_T_of_exec`; and the tree only grows.

The variables:
- `x`: the execution; `i`: the step; `v`: the validator.

Read aloud: a validator holds the block it records as confirmed. -/
theorem latest_confirmed_mem_T_of_exec (x : AtomicExec (protocol S) Sched) (i : ℕ) (v : V) :
    (x[i][v].st).A.latest_confirmed ∈ (x[i][v].st).S.T := by
  induction i with
  | zero =>
      have h := (lem11_node_invariant S Sched x 0 v).1.2.2.2.1
      rw [getElem_zero_st x v, initial_eq, acState_initial_eq, fgState_initial_eq] at h ⊢
      exact h
  | succ i ih =>
      have hTs := mem_T_mono x v (Nat.le_succ i)
      rcases step_cases_latest x i v with h | ⟨t, -, -, -, -, A'', hA'', hsv, hlc⟩
      · rw [h]
        exact hTs ih
      · rw [hlc]
        by_cases hs0 : S.C.slot (t : Int) = 0
        · rw [hs0, update_confirmation_zero] at hA''
          cases hA''
          exact hTs ih
        · rcases update_confirmation_latest_confirmed _ _ _ _ _ _ _ hs0 hA'' with h | ⟨h, -⟩
          · rw [h]
            exact hTs ih
          · rw [← hsv] at h
            exact saved_confirmation_mem_T_of_exec S Sched x (i + 1) v _ _ h

/-- **Kit fact, the slot of the record before an update.** In an execution where every time is
reached and corruption is permanent: at every step at a time before the support cutoff of slot
`s + 1`, a validator's record of the confirmed tip has a slot at most `s`.

Why: the record is the genesis block, of slot `0`, initially; a step that changes it is the
validator's confirmation update at the support cutoff of the slot `r` of its time, which is before
the support cutoff of slot `s + 1`, so `r ≤ s`; it writes the confirmation it saves, a block of the
validator's tree before that time, whose slot is at most `r` (`slot_le_of_mem_T_before`).

The variables:
- `x`: the execution; `v`: the validator; `s`: the slot; `i`: the step.

Read aloud: before the update of slot `s`, a validator's record is of slot `s` or earlier. -/
theorem latest_confirmed_slot_le (x : AtomicExec (protocol S) Sched)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption) (v : V) (s : ℕ) :
    ∀ i : ℕ, x[i].time < supportCutoff S (s + 1) →
      (x[i][v].st).A.latest_confirmed.slot ≤ s := by
  intro i
  induction i with
  | zero =>
      intro _
      rw [getElem_zero_st x v, initial_eq, acState_initial_eq]
      exact Nat.zero_le _
  | succ i ih =>
      intro hi
      have hi' : x[i].time < supportCutoff S (s + 1) := lt_of_le_of_lt (time_le_succ x i) hi
      rcases step_cases_latest x i v with h | ⟨t, hl, -, ht, -, A'', hA'', -, hlc⟩
      · rw [h]
        exact ih hi'
      · rw [hlc]
        by_cases hs0 : S.C.slot (t : Int) = 0
        · rw [hs0, update_confirmation_zero] at hA''
          cases hA''
          exact ih hi'
        · rcases update_confirmation_latest_confirmed _ _ _ _ _ _ _ hs0 hA'' with h | ⟨h, -⟩
          · rw [h]
            exact ih hi'
          · -- the saved confirmation is a block of the tree before `t`
            have hmem := update_confirmation_saved_mem S.C S.P _ A'' _ _ _
              (Nat.one_le_iff_ne_zero.mpr hs0) hA'' _ h
            have hT : A''.latest_confirmed ∈ (x[i][v].st).S.T := by
              rcases hmem with h' | h'
              · rw [h', fg_to_ac_F]
                exact (lem11_node_invariant S Sched x i v).1.2.2.2.1
              · exact ((mem_fg_to_ac_tree _ _).1 h').1
            have hst : x[i][v].st = stateBefore x t v := by
              unfold stateBefore
              rw [stepBefore_eq_of_lbl x hl]
            rw [hst] at hT
            have hsl := slot_le_of_mem_T_before hDiv hMono hT
            -- the slot of `t` is at most `s`
            have ht1 : x[i + 1].time = t := (time_of_lbl_tickAllAwake x hl).2
            have hcut := supportCutoff_slot_eq S ht
            have hle : S.C.slot (t : Int) ≤ s := by
              by_contra hgt
              have h1 : supportCutoff S (s + 1) ≤ supportCutoff S (S.C.slot (t : Int)) := by
                rcases Nat.lt_or_eq_of_le (Nat.succ_le_of_lt (Nat.lt_of_not_le hgt)) with h2 | h2
                · exact le_of_lt (supportCutoff_lt_of_lt S h2)
                · rw [← h2]
              omega
            exact le_trans hsl hle

end Record

/-! ## The record right after the update of the healed slot -/

section Base

/-- **No live lock vetoes `B₀` at the update of the healed slot.** In an execution where every
time is reached and corruption is permanent: when `HonestChainExtends`
holds for `B₀` at slot `s₀` at the honest active validators of slot `s₀`, every lock entry of an
updater `v` of slot `s₀`, held before the support cutoff `c` of slot `s₀ + 1` and live at `c`, is
on a block compatible with `B₀`.

Why: `v`'s tick at the vote time of slot `s₀ + 1` ran the revocation of that slot (Lemma 13: `v`
is awake since the duty window's start of slot `s₀ + 1`), and from that tick to `c` the lock
entries only shrink (`stateBefore_lock_entries_subset`). When `v` is an honest active validator of
slot `s₀`, the second clause of `HonestChainExtends` makes every entry the revocation left, live at
the vote time, compatible with `B₀`. Otherwise `v` was asleep at some time from the duty window's
start of slot `s₀` to before that of slot `s₀ + 1`, so it held no entry live at the vote time
(`lock_free_after_wake`) and the revocation left none.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot;
- `B₀`: the block; `v`: the updater. -/
theorem live_locks_compatible_at_healed_update (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ : ℕ) (B₀ : Block V) (v : V)
    -- every time is reached
    (hDiv : TimeDiverges x.toTrace)
    -- corruption is permanent
    (hMono : Sched.MonotoneCorruption)
    -- the slot invariant restricted to `B₀` at slot `s₀`
    (hBase : HonestChainExtends S Sched x (honestActiveAt S Sched s₀) B₀ s₀)
    -- `v` is an updater of slot `s₀`
    (hv : v ∈ updaterAt S Sched s₀) :
    ∀ e ∈ (stateBefore x (supportCutoff S (s₀ + 1)) v).A.lock_entries,
      is_live (fg_to_ac (stateBefore x (supportCutoff S (s₀ + 1)) v).S)
        ((supportCutoff S (s₀ + 1) : ℕ) : Int) e = true → e.B.compatible B₀ = true := by
  intro e he₂ hlive
  have hvU := hv
  unfold updaterAt at hvU
  rw [Finset.mem_sdiff, mem_awakeThroughout_iff] at hvU
  obtain ⟨hAwI, hHon⟩ := hvU
  have hAw : ∀ t' : ℕ, dutyWindowStart S (s₀ + 1) ≤ t' → t' ≤ supportCutoff S (s₀ + 1) →
      v ∈ Sched.awake (t' : Int) :=
    fun t' h1 h2 => hAwI t' (by exact_mod_cast h1) (by exact_mod_cast h2)
  have hdl : ((supportCutoff S (s₀ + 1) : ℕ) : Int) < e.d := by
    rw [is_live_iff] at hlive
    exact hlive.1
  -- the times
  have hΔ := one_le_Δ S
  have hv₃ : voteTime S (s₀ + 1) = slotStart S (s₀ + 1) + Δ S := voteTime_eq S (s₀ + 1)
  have hv₂ : supportCutoff S (s₀ + 1) = voteTime S (s₀ + 1) + Δ S := supportCutoff_eq S (s₀ + 1)
  have hdw : dutyWindowStart S (s₀ + 1) ≤ slotStart S s₀ := dutyWindowStart_succ_le_slotStart S s₀
  have hss : slotStart S (s₀ + 1) = slotStart S s₀ + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  have hss' : slotStart S (s₀ + 1 + 1) = slotStart S (s₀ + 1) + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq S (s₀ + 1), Nat.mul_add, Nat.mul_one]
  have hslot : ∀ t : ℕ, voteTime S (s₀ + 1) ≤ t → t ≤ supportCutoff S (s₀ + 1) →
      S.C.slot (t : Int) = s₀ + 1 :=
    fun t h1 h2 => slot_eq_of_mem S (by omega) (by omega)
  have hslot₃ := hslot (voteTime S (s₀ + 1)) le_rfl (by omega)
  -- the tick at the vote time of slot `s₀ + 1` ran the revocation
  obtain ⟨hl₃, -, hti₃'⟩ := stepBefore_spec x hDiv (by omega : 1 ≤ voteTime S (s₀ + 1))
  have hv₃a : v ∈ Sched.awake ((voteTime S (s₀ + 1) : ℕ) : Int) ∧
      v ∉ Sched.adv ((voteTime S (s₀ + 1) : ℕ) : Int) :=
    ⟨hAw _ (by omega) (by omega),
      fun h => hHon (hMono _ _ (by exact_mod_cast (by omega : voteTime S (s₀ + 1) ≤
        supportCutoff S (s₀ + 1))) h)⟩
  obtain ⟨n₃, sent₃, hrun₃, hst₃⟩ := tick_step_outcome x hl₃ hv₃a.1 hv₃a.2
  have hAw₃ := awakeSince_le_dutyWindowStart_b S Sched x (s₀ + 1) (voteTime S (s₀ + 1)) v hDiv
    hMono (by omega) (fun t h1 h2 => hAw t h1 (by omega)) hv₃a.2
  have hA₃ : (tickInputState x (stepBefore x (voteTime S (s₀ + 1))) (voteTime S (s₀ + 1)) v).A =
      (stateBefore x (voteTime S (s₀ + 1)) v).A := (tickInputState_frame x _ _ v).2.1
  have hS₃ : (tickInputState x (stepBefore x (voteTime S (s₀ + 1))) (voteTime S (s₀ + 1)) v).S =
      (stateBefore x (voteTime S (s₀ + 1)) v).S := (tickInputState_frame x _ _ v).1
  obtain ⟨A₃, hRevoke, hlock₃⟩ :=
    GoldilocksCorrectness.Statements.Routines.lem13_tick_revokes_locks S.C S.P S.X _ n₃ _ sent₃
      hrun₃ (by rw [hslot₃, voteTime_cast]) (by rw [hslot₃]; exact hAw₃)
  rw [hslot₃, hA₃, hS₃] at hRevoke
  -- from the tick at the vote time to the cutoff the lock entries only shrink
  have hsub : (stateBefore x (supportCutoff S (s₀ + 1)) v).A.lock_entries ⊆ A₃.lock_entries := by
    rw [← hlock₃, ← hst₃]
    refine stateBefore_lock_entries_subset x hDiv v (by omega) (by omega) ?_
    intro t'' h1 h2
    rw [hti₃'] at h1
    rw [hslot t'' (by omega) (by omega), ← voteTime_cast, ← supportCutoff_cast]
    constructor <;> intro h <;> omega
  have heA := hsub he₂
  by_cases hA : v ∈ honestActiveAt S Sched s₀
  · -- an honest active validator: the second clause of `HonestChainExtends`
    refine hBase.2.1 v hA A₃ hRevoke e heA ?_
    rw [is_live_iff]
    have h32 : ((voteTime S (s₀ + 1) : ℕ) : Int) < ((supportCutoff S (s₀ + 1) : ℕ) : Int) :=
      Int.ofNat_lt.2 (by omega)
    exact ⟨lt_trans h32 hdl,
      GoldilocksCorrectness.Proofs.Routines.revoke_locks_entry_mem_tree (Nat.le_add_left 1 s₀)
        hRevoke e heA⟩
  · -- otherwise `v` slept in the duty window of slot `s₀`, and the revocation left no lock
    exfalso
    have hSlept : ∃ t : ℕ, dutyWindowStart S s₀ ≤ t ∧ t < dutyWindowStart S (s₀ + 1) ∧
        v ∉ Sched.awake (t : Int) := by
      by_contra hno
      apply hA
      unfold honestActiveAt activeAt
      rw [Finset.mem_sdiff, mem_awakeThroughout_iff]
      refine ⟨fun t'' h1 h2 => ?_, hHon⟩
      have h0 : (0 : Int) ≤ t'' := le_trans (Int.natCast_nonneg _) h1
      have hn : ((t''.toNat : ℕ) : Int) = t'' := Int.toNat_of_nonneg h0
      by_cases hlt : t''.toNat < dutyWindowStart S (s₀ + 1)
      · by_contra hna
        exact hno ⟨t''.toNat, by omega, hlt, by rw [hn]; exact hna⟩
      · exact hAwI t'' (by omega) h2
    exact GoldilocksCorrectness.Proofs.Executions.revoke_locks_empty_of_lockFree S Sched x
      (voteTime S (s₀ + 1)) (s₀ + 1) v A₃ (Nat.le_add_left 1 s₀)
      (GoldilocksCorrectness.Proofs.Executions.lock_free_after_wake S Sched x s₀ v hDiv hMono
        hSlept) hRevoke e heA

/-- **The record right after the update of the healed slot.** In an execution where every time
is reached and corruption is permanent: when `B₀`'s slot is at least
`s₀`, `HonestChainExtends` holds for `B₀` at slot `s₀` at the honest active validators of slot
`s₀`, and every updater of slot `s₀` saves `B₀` as its confirmation of slot `s₀`, then every
updater `v` of slot `s₀` holds `B₀` as its record of the confirmed tip right after the support
cutoff of slot `s₀ + 1`.

Why: `v`'s update of slot `s₀ + 1` ran (`update_state_of_duty`) and saved `B₀`; no live lock of
its input vetoes `B₀` (`live_locks_compatible_at_healed_update`), so it wrote
`advance Φ old (some B₀)`. That is `B₀` unless `old` is in `Φ.tree` and `B₀` is an ancestor of
`old` or `old` itself; but `old`, held before the support cutoff of slot `s₀ + 1`, has a slot at
most `s₀` (`latest_confirmed_slot_le`), which is at most `B₀`'s, and a strict ancestor of a tree
block has a smaller slot; so then `old = B₀`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot;
- `B₀`: the block every updater of slot `s₀` saved; `v`: the updater. -/
theorem latest_confirmed_after_healed_update (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ : ℕ) (B₀ : Block V) (v : V)
    -- every time is reached
    (hDiv : TimeDiverges x.toTrace)
    -- corruption is permanent
    (hMono : Sched.MonotoneCorruption)
    -- `B₀`'s slot is at least `s₀`
    (hB₀slot : s₀ ≤ B₀.slot)
    -- the slot invariant restricted to `B₀` at slot `s₀`
    (hBase : HonestChainExtends S Sched x (honestActiveAt S Sched s₀) B₀ s₀)
    -- every updater of slot `s₀` saved `B₀`
    (hBaseSaved : ∀ u ∈ updaterAt S Sched s₀,
      (stateBefore x (supportCutoff S (s₀ + 1) + 1) u).A.saved_confirmation s₀ = some B₀)
    -- `v` is an updater of slot `s₀`
    (hv : v ∈ updaterAt S Sched s₀) :
    (stateBefore x (supportCutoff S (s₀ + 1) + 1) v).A.latest_confirmed = B₀ := by
  have hvU := hv
  unfold updaterAt at hvU
  rw [Finset.mem_sdiff, mem_awakeThroughout_iff] at hvU
  obtain ⟨hAwI, hHon⟩ := hvU
  have hAw : ∀ t' : ℕ, dutyWindowStart S (s₀ + 1) ≤ t' → t' ≤ supportCutoff S (s₀ + 1) →
      v ∈ Sched.awake (t' : Int) :=
    fun t' h1 h2 => hAwI t' (by exact_mod_cast h1) (by exact_mod_cast h2)
  have hΔ := one_le_Δ S
  have hv₃ : voteTime S (s₀ + 1) = slotStart S (s₀ + 1) + Δ S := voteTime_eq S (s₀ + 1)
  have hv₂ : supportCutoff S (s₀ + 1) = voteTime S (s₀ + 1) + Δ S := supportCutoff_eq S (s₀ + 1)
  have hdw : dutyWindowStart S (s₀ + 1) ≤ slotStart S s₀ := dutyWindowStart_succ_le_slotStart S s₀
  have hss : slotStart S (s₀ + 1) = slotStart S s₀ + 4 * Δ S := by
    rw [slotStart_eq, slotStart_eq, Nat.mul_add, Nat.mul_one]
  -- the update of slot `s₀ + 1` ran and saved `B₀`
  have hτ := awakeSince_le_dutyWindowStart_b S Sched x (s₀ + 1) (supportCutoff S (s₀ + 1)) v hDiv
    hMono (by omega) hAw hHon
  obtain ⟨A'', hUpd, hSv, -, -, hLc⟩ := update_state_of_duty S Sched x s₀ v hDiv
    ⟨hAw _ (by omega) le_rfl, hHon⟩ hτ
  have hB : A''.saved_confirmation s₀ = some B₀ := by
    rw [← hSv]
    exact hBaseSaved v hv
  -- no live lock vetoes `B₀`
  have hNoVeto : live_lock_vetoes
      (expireLocks (stateBefore x (supportCutoff S (s₀ + 1)) v).A
        ((supportCutoff S (s₀ + 1) : ℕ) : Int))
      (fg_to_ac (stateBefore x (supportCutoff S (s₀ + 1)) v).S)
      ((supportCutoff S (s₀ + 1) : ℕ) : Int) B₀ = false := by
    apply GoldilocksCorrectness.Proofs.Routines.live_lock_vetoes_eq_false
    intro e he hlive
    exact live_locks_compatible_at_healed_update S Sched x s₀ B₀ v hDiv hMono hBase hv e
      (Finset.mem_filter.1 he).1 hlive
  rw [hLc]
  rcases update_confirmation_latest_cases _ _ _ _ _ _ _ (Nat.add_one_ne_zero s₀) hUpd with
    ⟨hn, -⟩ | ⟨C', hC', ⟨hv', -⟩ | ⟨-, hadv⟩⟩
  · rw [Nat.add_sub_cancel, hB] at hn
    cases hn
  · rw [Nat.add_sub_cancel, hB] at hC'
    cases hC'
    rw [hNoVeto] at hv'
    cases hv'
  · rw [Nat.add_sub_cancel, hB] at hC'
    cases hC'
    rw [hadv]
    rcases advance_some (fg_to_ac (stateBefore x (supportCutoff S (s₀ + 1)) v).S)
        (expireLocks (stateBefore x (supportCutoff S (s₀ + 1)) v).A
          ((supportCutoff S (s₀ + 1) : ℕ) : Int)).latest_confirmed B₀ with
      ⟨hin, hanc, ha⟩ | ⟨-, ha⟩
    · rw [ha]
      -- the old record is `B₀`: its slot is at most `s₀`
      have hoT := ((mem_fg_to_ac_tree _ _).1 hin).1
      obtain ⟨-, hti, -⟩ := stepBefore_spec x hDiv (by omega : 1 ≤ supportCutoff S (s₀ + 1))
      have hsl := latest_confirmed_slot_le x hDiv hMono v s₀
        (stepBefore x (supportCutoff S (s₀ + 1))) (by omega)
      by_contra hne
      have hTC := (lem11_node_invariant S Sched x (stepBefore x (supportCutoff S (s₀ + 1))) v).1.2.2.1
      have hlt := slot_lt_of_ancestorEq_of_treeClosed hTC hoT hanc (Ne.symm hne)
      have hsl' : (expireLocks (stateBefore x (supportCutoff S (s₀ + 1)) v).A
          ((supportCutoff S (s₀ + 1) : ℕ) : Int)).latest_confirmed.slot ≤ s₀ := hsl
      exact absurd (lt_of_lt_of_le hlt hsl') (Nat.not_lt.2 hB₀slot)
    · exact ha

/-- **`lem90a_latest_confirmed_honest_at`, the record after the healed round is an honest
confirmation, of a slot whose update ran by then.** The proof; the audited statement is in
`Statements/Executions/ConfirmedTipStatements.lean`.

Why: by induction on the steps from the tick at the time after the support cutoff `c` of slot
`s₀ + 1`. There, a validator honest at `c` is an updater of slot `s₀` (`hAwake`) and holds `B₀`
(`latest_confirmed_after_healed_update`), its saved confirmation of slot `s₀`. A later step keeps
the record (`step_cases_latest`), or is the validator's update of a slot `s + 1` after `c`, which
keeps it or writes the confirmation of slot `s ≥ s₀` it saves; the validator passed the duty test
of slot `s + 1` and is honest at that update, so it is an updater of slot `s`
(`awake_of_tickInput_awakeSince`). The record is held at every step
(`latest_confirmed_mem_T_of_exec`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot;
- `B₀`: the block every updater of slot `s₀` saved.

Keeping the slot: the slot `s` of the confirmation the record is, with its update at the support
cutoff of slot `s + 1` at most the time of the step read, the time of the update that wrote it. -/
theorem lem90a_latest_confirmed_honest_at (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ : ℕ) (B₀ : Block V)
    -- every time is reached
    (hDiv : TimeDiverges x.toTrace)
    -- corruption is permanent
    (hMono : Sched.MonotoneCorruption)
    -- `B₀`'s slot is at least `s₀`
    (hB₀slot : s₀ ≤ B₀.slot)
    -- the slot invariant restricted to `B₀` at slot `s₀`
    (hBase : HonestChainExtends S Sched x (honestActiveAt S Sched s₀) B₀ s₀)
    -- every updater of slot `s₀` saved `B₀`
    (hBaseSaved : ∀ v ∈ updaterAt S Sched s₀,
      (stateBefore x (supportCutoff S (s₀ + 1) + 1) v).A.saved_confirmation s₀ = some B₀)
    -- every validator honest at the support cutoff of slot `s₀ + 1` is an updater of slot `s₀`
    (hAwake : ∀ v : V, v ∉ Sched.adv ((supportCutoff S (s₀ + 1) : ℕ) : Int) →
      v ∈ updaterAt S Sched s₀) :
    ∀ (i : ℕ) (v : V), supportCutoff S (s₀ + 1) < x[i].time → v ∉ Sched.adv (x[i].time : Int) →
      (∃ s : ℕ, s₀ ≤ s ∧ supportCutoff S (s + 1) ≤ x[i].time ∧ ∃ u ∈ updaterAt S Sched s,
        (stateBefore x (supportCutoff S (s + 1) + 1) u).A.saved_confirmation s =
          some (x[i][v].st).A.latest_confirmed) ∧
        (x[i][v].st).A.latest_confirmed ∈ (x[i][v].st).S.T := by
  intro i v hi hv
  obtain ⟨-, hti₀, hti₀'⟩ := stepBefore_spec x hDiv (by omega : 1 ≤ supportCutoff S (s₀ + 1) + 1)
  have key : ∀ k : ℕ, ∀ u : V,
      u ∉ Sched.adv (x[stepBefore x (supportCutoff S (s₀ + 1) + 1) + k].time : Int) →
      ∃ s : ℕ, s₀ ≤ s ∧
        supportCutoff S (s + 1) ≤ x[stepBefore x (supportCutoff S (s₀ + 1) + 1) + k].time ∧
        ∃ w ∈ updaterAt S Sched s,
          (stateBefore x (supportCutoff S (s + 1) + 1) w).A.saved_confirmation s =
            some (x[stepBefore x (supportCutoff S (s₀ + 1) + 1) + k][u].st).A.latest_confirmed := by
    intro k
    induction k with
    | zero =>
        intro u hu
        have htc : x[stepBefore x (supportCutoff S (s₀ + 1) + 1) + 0].time =
            supportCutoff S (s₀ + 1) := by
          rw [Nat.add_zero]
          omega
        have hU := hAwake u (by rw [htc] at hu; exact hu)
        refine ⟨s₀, le_rfl, le_of_eq htc.symm, u, hU, ?_⟩
        have hst : x[stepBefore x (supportCutoff S (s₀ + 1) + 1) + 0][u].st =
            stateBefore x (supportCutoff S (s₀ + 1) + 1) u := rfl
        rw [hst, latest_confirmed_after_healed_update S Sched x s₀ B₀ u hDiv hMono hB₀slot
          hBase hBaseSaved hU]
        exact hBaseSaved u hU
    | succ k ih =>
        intro u hu
        have hu' : u ∉ Sched.adv (x[stepBefore x (supportCutoff S (s₀ + 1) + 1) + k].time : Int) :=
          fun h => hu (hMono _ _ (by exact_mod_cast time_le_succ x _) h)
        have lift : (∃ s : ℕ, s₀ ≤ s ∧
            supportCutoff S (s + 1) ≤ x[stepBefore x (supportCutoff S (s₀ + 1) + 1) + k].time ∧
            ∃ w ∈ updaterAt S Sched s,
              (stateBefore x (supportCutoff S (s + 1) + 1) w).A.saved_confirmation s =
                some
                  (x[stepBefore x (supportCutoff S (s₀ + 1) + 1) + k][u].st).A.latest_confirmed) →
            ∃ s : ℕ, s₀ ≤ s ∧
            supportCutoff S (s + 1) ≤ x[stepBefore x (supportCutoff S (s₀ + 1) + 1) + k + 1].time ∧
            ∃ w ∈ updaterAt S Sched s,
              (stateBefore x (supportCutoff S (s + 1) + 1) w).A.saved_confirmation s =
                some
                  (x[stepBefore x (supportCutoff S (s₀ + 1) + 1) + k][u].st).A.latest_confirmed :=
          fun ⟨s', hs', hle, hrest⟩ => ⟨s', hs', le_trans hle (time_le_succ x _), hrest⟩
        show ∃ s : ℕ, s₀ ≤ s ∧
          supportCutoff S (s + 1) ≤ x[stepBefore x (supportCutoff S (s₀ + 1) + 1) + k + 1].time ∧
          ∃ w ∈ updaterAt S Sched s,
            (stateBefore x (supportCutoff S (s + 1) + 1) w).A.saved_confirmation s =
              some (x[stepBefore x (supportCutoff S (s₀ + 1) + 1) + k + 1][u].st).A.latest_confirmed
        rcases step_cases_latest x (stepBefore x (supportCutoff S (s₀ + 1) + 1) + k) u with
          h | ⟨t, hl, hmem, ht, ⟨τ, hτ, hτle⟩, A'', hA'', hsv, hlc⟩
        · rw [h]
          exact lift (ih u hu')
        · rw [hlc]
          by_cases hs0 : S.C.slot (t : Int) = 0
          · rw [hs0, update_confirmation_zero] at hA''
            cases hA''
            exact lift (ih u hu')
          rcases update_confirmation_latest_confirmed _ _ _ _ _ _ _ hs0 hA'' with h | ⟨h, -⟩
          · rw [h]
            exact lift (ih u hu')
          obtain ⟨s, hs⟩ : ∃ s : ℕ, S.C.slot (t : Int) = s + 1 :=
            ⟨_, (Nat.succ_pred_eq_of_ne_zero hs0).symm⟩
          have hcut := supportCutoff_slot_eq S ht
          rw [hs] at hcut
          have ht1 := (time_of_lbl_tickAllAwake x hl).2
          have hge : supportCutoff S (s₀ + 1) + 1 ≤ t := by
            have := time_mono x (show stepBefore x (supportCutoff S (s₀ + 1) + 1) + 1 ≤
              stepBefore x (supportCutoff S (s₀ + 1) + 1) + k + 1 by omega)
            omega
          have hss₀ : s₀ ≤ s := by
            by_contra hlt
            have h1 : supportCutoff S (s + 1) ≤ supportCutoff S (s₀ + 1) := by
              rcases Nat.lt_or_eq_of_le (Nat.succ_le_succ (Nat.le_of_lt (Nat.lt_of_not_le hlt)))
                with h2 | h2
              · exact le_of_lt (supportCutoff_lt_of_lt S h2)
              · rw [Nat.succ.inj h2]
            omega
          refine ⟨s, hss₀, le_of_eq (hcut.trans ht1.symm), u, ?_, ?_⟩
          · -- `u` passed the duty test of slot `s + 1` and is honest at its update
            unfold updaterAt
            rw [Finset.mem_sdiff]
            refine ⟨mem_awakeThroughout_of_forall ?_, by rw [hcut]; exact (Finset.mem_sdiff.1 hmem).2⟩
            intro t' h1 h2
            have hτ' : (tickInputState x (stepBefore x t) t u).awakeSince = some τ := by
              rw [stepBefore_eq_of_lbl x hl]
              exact hτ
            refine awake_of_tickInput_awakeSince x hDiv hMono (by omega) hτ'
              (Finset.mem_sdiff.1 hmem).1 (Finset.mem_sdiff.1 hmem).2 t' ?_ (by omega)
            rw [hs] at hτle
            have h3 : duty_window_start S.C (s + 1) ≤ ((dutyWindowStart S (s + 1) : ℕ) : Int) :=
              duty_window_start_le_dutyWindowStart S (s + 1)
            have h4 : ((dutyWindowStart S (s + 1) : ℕ) : Int) ≤ (t' : Int) := by exact_mod_cast h1
            exact le_trans hτle (le_trans h3 h4)
          · -- its saved confirmation of slot `s`
            rw [hcut]
            have hk := stateBefore_succ_keepsConfirmation x hDiv u ht1
            rw [hk.2.1, hsv]
            rw [hs, Nat.add_sub_cancel] at h
            exact h
  have hle : stepBefore x (supportCutoff S (s₀ + 1) + 1) ≤ i := by
    by_contra hlt
    have := time_mono x (Nat.le_of_lt (Nat.lt_of_not_le hlt))
    omega
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  exact ⟨key k v hv, latest_confirmed_mem_T_of_exec x _ v⟩

/-- **`lem90a_latest_confirmed_honest`, the record after the healed round is an honest
confirmation.** The proof; the audited statement is in
`Statements/Executions/ConfirmedTipStatements.lean`. It is `lem90a_latest_confirmed_honest_at`
with the bound on the slot dropped.

Why: by induction on the steps from the tick at the time after the support cutoff `c` of slot
`s₀ + 1`. There, a validator honest at `c` is an updater of slot `s₀` (`hAwake`) and holds `B₀`
(`latest_confirmed_after_healed_update`), its saved confirmation of slot `s₀`. A later step keeps
the record (`step_cases_latest`), or is the validator's update of a slot `s + 1` after `c`, which
keeps it or writes the confirmation of slot `s ≥ s₀` it saves; the validator passed the duty test
of slot `s + 1` and is honest at that update, so it is an updater of slot `s`
(`awake_of_tickInput_awakeSince`). The record is held at every step
(`latest_confirmed_mem_T_of_exec`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot;
- `B₀`: the block every updater of slot `s₀` saved. -/
theorem lem90a_latest_confirmed_honest (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ : ℕ) (B₀ : Block V)
    -- every time is reached
    (hDiv : TimeDiverges x.toTrace)
    -- corruption is permanent
    (hMono : Sched.MonotoneCorruption)
    -- `B₀`'s slot is at least `s₀`
    (hB₀slot : s₀ ≤ B₀.slot)
    -- the slot invariant restricted to `B₀` at slot `s₀`
    (hBase : HonestChainExtends S Sched x (honestActiveAt S Sched s₀) B₀ s₀)
    -- every updater of slot `s₀` saved `B₀`
    (hBaseSaved : ∀ v ∈ updaterAt S Sched s₀,
      (stateBefore x (supportCutoff S (s₀ + 1) + 1) v).A.saved_confirmation s₀ = some B₀)
    -- every validator honest at the support cutoff of slot `s₀ + 1` is an updater of slot `s₀`
    (hAwake : ∀ v : V, v ∉ Sched.adv ((supportCutoff S (s₀ + 1) : ℕ) : Int) →
      v ∈ updaterAt S Sched s₀) :
    ∀ (i : ℕ) (v : V), supportCutoff S (s₀ + 1) < x[i].time → v ∉ Sched.adv (x[i].time : Int) →
      IsHonestConfirmation S Sched x s₀ (x[i][v].st).A.latest_confirmed ∧
        (x[i][v].st).A.latest_confirmed ∈ (x[i][v].st).S.T := fun i v hi hv =>
  let ⟨⟨s, hs, _, h⟩, hT⟩ := lem90a_latest_confirmed_honest_at S Sched x s₀ B₀ hDiv hMono
    hB₀slot hBase hBaseSaved hAwake i v hi hv
  ⟨⟨s, hs, h⟩, hT⟩

end Base

/-! ## Lemma 90, agreement and growth -/

section Lemma90

open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff)

variable {S : Setup V} {Sched : Schedule V}

/-- An honest confirmation is on the honest chain: it is the confirmation of its own slot.

The variables:
- `x`: the execution; `s₀`: the first slot of the chain; `L`: the block. -/
theorem onHonestChain_of_isHonestConfirmation {x : AtomicExec (protocol S) Sched} {s₀ : ℕ}
    {L : Block V}
    -- `L` is an honest confirmation from slot `s₀`
    (h : IsHonestConfirmation S Sched x s₀ L) : OnHonestChain S Sched x s₀ L := by
  obtain ⟨s, hs, v, hv, hL⟩ := h
  exact ⟨s, hs, v, hv, L, hL, ancestorEq_refl L⟩

/-- The confirmed tip of a node state whose record is an honest confirmation and whose caches are
on the honest chain is on the honest chain: it is the record, or the finalized block, an ancestor
of the justified block or that block.

The variables:
- `x`: the execution; `s₀`: the first slot of the chain; `H`: the threshold of the caches;
  `n`: the node state. -/
theorem confirmedOf_onHonestChain {x : AtomicExec (protocol S) Sched} {s₀ H : ℕ}
    {n : NodeState V}
    -- the record is an honest confirmation
    (hL : IsHonestConfirmation S Sched x s₀ n.A.latest_confirmed)
    -- the caches are on the honest chain
    (hC : CachesOnChain S Sched x s₀ H n) :
    OnHonestChain S Sched x s₀ (confirmedOf n) := by
  rcases ac_confirmed_cases n.A (fg_to_ac n.S) with ⟨-, h⟩ | ⟨-, h⟩
  · show OnHonestChain S Sched x s₀ (ac_confirmed n.A (fg_to_ac n.S))
    rw [h]
    exact onHonestChain_of_isHonestConfirmation hL
  · show OnHonestChain S Sched x s₀ (ac_confirmed n.A (fg_to_ac n.S))
    rw [h, fg_to_ac_F]
    exact onHonestChain_of_ancestorEq hC.2.1 hC.2.2.2.2

/-- **Lemma 90, agreement, read up to a time `t`.** The proof; the audited statement is in
`Statements/Executions/ConfirmedTipStatements.lean`.

Why: each of the two confirmed tips is its node state's record, an honest confirmation, or its
finalized block, an ancestor of a justified block on the honest chain or that block; so both are
on the honest chain (`confirmedOf_onHonestChain`), and two blocks on it are compatible
(`onHonestChain_compatible`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot;
- `H`: the threshold of the caches; `i₁`: the step from which the facts hold; `t`: the time up to
  which the confirmed tips are read.

Caches up to `t`: the proof reads the caches at the two steps compared, at times at most `t`. -/
theorem lem90_confirmed_agree_until (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ H i₁ t : ℕ)
    -- the honest confirmations form a chain from slot `s₀`
    (hChain : ConfirmationsChain S Sched x s₀)
    -- from the time of step `i₁` on, an honest validator's record is an honest confirmation
    (hLatest : ∀ (i : ℕ) (v : V), x[i₁].time ≤ x[i].time → v ∉ Sched.adv (x[i].time : Int) →
      IsHonestConfirmation S Sched x s₀ (x[i][v].st).A.latest_confirmed)
    -- from the time of step `i₁` to `t`, an honest validator's caches are on the honest chain
    (hCaches : ∀ (i : ℕ) (v : V), x[i₁].time ≤ x[i].time → x[i].time ≤ t →
      v ∉ Sched.adv (x[i].time : Int) → CachesOnChain S Sched x s₀ H (x[i][v].st)) :
    ConfirmedAgreeBetween S Sched x (x[i₁].time) t := by
  rw [GoldilocksCorrectness.Proofs.View.confirmedAgreeBetween_unfold]
  intro v₁ v₂ i j h₁ h₂ hi hj hit hjt
  have hh₁ : v₁ ∉ Sched.adv (x[i].time : Int) := h₁ _ le_rfl
  have hh₂ : v₂ ∉ Sched.adv (x[j].time : Int) := h₂ _ le_rfl
  exact GoldilocksCorrectness.Proofs.Executions.onHonestChain_compatible S Sched x s₀ _ _ hChain
    (confirmedOf_onHonestChain (hLatest i v₁ hi hh₁) (hCaches i v₁ hi hit hh₁))
    (confirmedOf_onHonestChain (hLatest j v₂ hj hh₂) (hCaches j v₂ hj hjt hh₂))

/-- **Lemma 90, agreement.** The proof; the audited statement is in
`Statements/Executions/ConfirmedTipStatements.lean`. It is `lem90_confirmed_agree_until` at every
time `t` (`confirmedAgreeAfterHealing_iff`).

Why: each of the two confirmed tips is its node state's record, an honest confirmation, or its
finalized block, an ancestor of a justified block on the honest chain or that block; so both are
on the honest chain (`confirmedOf_onHonestChain`), and two blocks on it are compatible
(`onHonestChain_compatible`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot;
- `H`: the threshold of the caches; `i₁`: the step from which the facts hold. -/
theorem lem90_confirmed_agree (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ H i₁ : ℕ)
    -- the honest confirmations form a chain from slot `s₀`
    (hChain : ConfirmationsChain S Sched x s₀)
    -- from the time of step `i₁` on, an honest validator's record is an honest confirmation
    (hLatest : ∀ (i : ℕ) (v : V), x[i₁].time ≤ x[i].time → v ∉ Sched.adv (x[i].time : Int) →
      IsHonestConfirmation S Sched x s₀ (x[i][v].st).A.latest_confirmed)
    -- from the time of step `i₁` on, an honest validator's caches are on the honest chain
    (hCaches : ∀ (i : ℕ) (v : V), x[i₁].time ≤ x[i].time → v ∉ Sched.adv (x[i].time : Int) →
      CachesOnChain S Sched x s₀ H (x[i][v].st)) :
    ConfirmedAgreeAfterHealing S Sched x (x[i₁].time) :=
  (confirmedAgreeAfterHealing_iff S Sched x _).2 fun t =>
    lem90_confirmed_agree_until S Sched x s₀ H i₁ t hChain hLatest
      (fun i v h₁ _ h₂ => hCaches i v h₁ h₂)

/-- **One step of Lemma 90's growth, from three compatibilities.** When, at steps `j` and `j + 1`,
`v`'s record is held in its tree, the record at step `j + 1` is compatible with the finalized block
at step `j + 1`, and the record at step `j` is compatible with the record at step `j + 1` and with
the finalized block at step `j`, then `v`'s confirmed tip at step `j` is an ancestor of, or equal
to, the one at step `j + 1`.

Why: `confirmedOf_step`'s proof, which reads the honest chain only for these three compatibilities.

The variables:
- `x`: the execution; `j`: the step; `v`: the validator. -/
theorem confirmedOf_step_of_compatible {x : AtomicExec (protocol S) Sched} (j : ℕ) (v : V)
    -- at step `j`, the record is held in the tree
    (hLT : (x[j][v].st).A.latest_confirmed ∈ (x[j][v].st).S.T)
    -- at step `j + 1`, the record is held in the tree
    (hL'T : (x[j + 1][v].st).A.latest_confirmed ∈ (x[j + 1][v].st).S.T)
    -- the three compatibilities
    (hL'F' : (x[j + 1][v].st).A.latest_confirmed.compatible (x[j + 1][v].st).S.F = true)
    (hLL' : (x[j][v].st).A.latest_confirmed.compatible (x[j + 1][v].st).A.latest_confirmed = true)
    (hLF : (x[j][v].st).A.latest_confirmed.compatible (x[j][v].st).S.F = true) :
    (confirmedOf (x[j][v].st)).AncestorEq (confirmedOf (x[j + 1][v].st)) := by
  have hFF := F_ancestorEq_of_le x v (Nat.le_succ j)
  refine confirmedOf_ancestorEq_of hFF hL'T hL'F' ?_
  rcases step_cases_latest x j v with h | ⟨t, -, -, -, -, A'', hA'', -, hlc⟩
  · right
    rw [h]
    exact ancestorEq_refl _
  by_cases hs0 : S.C.slot (t : Int) = 0
  · rw [hs0, update_confirmation_zero] at hA''
    cases hA''
    right
    rw [hlc]
    exact ancestorEq_refl _
  rcases update_confirmation_latest_cases _ _ _ _ _ _ _ hs0 hA'' with
    ⟨-, h⟩ | ⟨C', -, ⟨-, h⟩ | ⟨-, h⟩⟩
  · right
    rw [hlc, h]
    exact ancestorEq_refl _
  · right
    rw [hlc, h]
    exact ancestorEq_refl _
  rcases advance_some (fg_to_ac (x[j][v].st).S)
      (expireLocks (x[j][v].st).A (t : Int)).latest_confirmed C' with
    ⟨-, -, ha⟩ | ⟨hnot, ha⟩
  · right
    rw [hlc, h, ha]
    exact ancestorEq_refl _
  have hL'eq : (x[j + 1][v].st).A.latest_confirmed = C' := by rw [hlc, h, ha]
  rw [hL'eq] at hLL'
  rcases (compatible_iff _ _).1 hLL' with h1 | h1
  · right
    rw [hL'eq]
    exact h1
  · -- `C'` is an ancestor of the old record, which is then not in the frame's tree
    left
    have hnin : ¬ (x[j][v].st).S.F.AncestorEq (x[j][v].st).A.latest_confirmed :=
      fun hFL => hnot ⟨(mem_fg_to_ac_tree _ _).2 ⟨hLT, hFL⟩, h1⟩
    rcases (compatible_iff _ _).1 hLF with
      h2 | h2
    · exact ancestorEq_trans h2 hFF
    · exact absurd h2 hnin

/-- **One step of Lemma 90's growth.** When, at steps `j` and `j + 1`, `v`'s record is an honest
confirmation held in its tree and its finalized block is on the honest chain, and the honest
confirmations form a chain, `v`'s confirmed tip at step `j` is an ancestor of, or equal to, the
one at step `j + 1`.

Why: `confirmedOf_ancestorEq_of`, with the finalized block only moving to a descendant
(`F_ancestorEq_of_le`) and the record at step `j` an ancestor of, or equal to, the finalized block
or the record at step `j + 1`: the step keeps the record (`step_cases_latest`), or is `v`'s
update, which keeps it or writes the confirmation `C'` it saves when `advance` does not keep it.
The record at step `j` and `C'`, both on the honest chain, are compatible; when `C'` is an
ancestor of the old record, `advance` not keeping the old record means it is not in the frame's
tree, so (held, and compatible with the finalized block) it is an ancestor of the finalized block.

The variables:
- `x`: the execution; `s₀`: the healed slot; `j`: the step; `v`: the validator.

It is `confirmedOf_step_of_compatible`, the three compatibilities read on the honest chain. -/
theorem confirmedOf_step {x : AtomicExec (protocol S) Sched} {s₀ : ℕ} (j : ℕ) (v : V)
    -- the honest confirmations form a chain from slot `s₀`
    (hChain : ConfirmationsChain S Sched x s₀)
    -- at step `j`, the record is an honest confirmation held in the tree
    (hL : IsHonestConfirmation S Sched x s₀ (x[j][v].st).A.latest_confirmed)
    (hLT : (x[j][v].st).A.latest_confirmed ∈ (x[j][v].st).S.T)
    -- at step `j`, the finalized block is on the honest chain
    (hF : OnHonestChain S Sched x s₀ (x[j][v].st).S.F)
    -- at step `j + 1`, the record is an honest confirmation held in the tree
    (hL' : IsHonestConfirmation S Sched x s₀ (x[j + 1][v].st).A.latest_confirmed)
    (hL'T : (x[j + 1][v].st).A.latest_confirmed ∈ (x[j + 1][v].st).S.T)
    -- at step `j + 1`, the finalized block is on the honest chain
    (hF' : OnHonestChain S Sched x s₀ (x[j + 1][v].st).S.F) :
    (confirmedOf (x[j][v].st)).AncestorEq (confirmedOf (x[j + 1][v].st)) :=
  have hcomp : ∀ B B' : Block V, OnHonestChain S Sched x s₀ B → OnHonestChain S Sched x s₀ B' →
      B.compatible B' = true := fun B B' hB hB' =>
    GoldilocksCorrectness.Proofs.Executions.onHonestChain_compatible S Sched x s₀ B B' hChain hB hB'
  confirmedOf_step_of_compatible j v hLT hL'T
    (hcomp _ _ (onHonestChain_of_isHonestConfirmation hL') hF')
    (hcomp _ _ (onHonestChain_of_isHonestConfirmation hL)
      (onHonestChain_of_isHonestConfirmation hL'))
    (hcomp _ _ (onHonestChain_of_isHonestConfirmation hL) hF)

/-- **Lemma 90, growth, read up to a time `t`.** The proof; the audited statement is in
`Statements/Executions/ConfirmedTipStatements.lean`.

Why: by induction on the later step, with `confirmedOf_step` at each step: `v` is honest at every
step up to the later one, so the records and the caches at those steps are on the honest chain by
the two hypotheses.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot;
- `H`: the threshold of the caches; `i₁`: the step from which the facts hold; `t`: the time up to
  which the later confirmed tip is read.

Caches up to `t`: the proof reads the caches at the steps up to the later one, at times at most
`t`. -/
theorem lem90_confirmed_monotone_until (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ H i₁ t : ℕ)
    -- the honest confirmations form a chain from slot `s₀`
    (hChain : ConfirmationsChain S Sched x s₀)
    -- from the time of step `i₁` on, an honest validator's record is an honest confirmation it
    -- holds
    (hLatest : ∀ (i : ℕ) (v : V), x[i₁].time ≤ x[i].time → v ∉ Sched.adv (x[i].time : Int) →
      IsHonestConfirmation S Sched x s₀ (x[i][v].st).A.latest_confirmed ∧
        (x[i][v].st).A.latest_confirmed ∈ (x[i][v].st).S.T)
    -- from the time of step `i₁` to `t`, an honest validator's caches are on the honest chain
    (hCaches : ∀ (i : ℕ) (v : V), x[i₁].time ≤ x[i].time → x[i].time ≤ t →
      v ∉ Sched.adv (x[i].time : Int) → CachesOnChain S Sched x s₀ H (x[i][v].st)) :
    ConfirmedMonotoneBetween S Sched x (x[i₁].time) t := by
  intro v i j hij hj hi hjt
  revert hjt
  induction j, hij using Nat.le_induction with
  | base => exact fun _ => ancestorEq_refl _
  | succ j hij ih =>
      intro hjt
      have hjj : HonestThrough x j v := fun t' ht' =>
        hj t' (le_trans ht' (by exact_mod_cast time_le_succ x j))
      have htj : x[i₁].time ≤ x[j].time := le_trans hi (time_mono x hij)
      have htj1 : x[i₁].time ≤ x[j + 1].time := le_trans htj (time_le_succ x j)
      have hvj : v ∉ Sched.adv (x[j].time : Int) := hjj _ le_rfl
      have hvj1 : v ∉ Sched.adv (x[j + 1].time : Int) := hj _ le_rfl
      obtain ⟨hL, hLT⟩ := hLatest j v htj hvj
      obtain ⟨hL', hL'T⟩ := hLatest (j + 1) v htj1 hvj1
      have hjt' : x[j].time ≤ t := le_trans (time_le_succ x j) hjt
      have hC := hCaches j v htj hjt' hvj
      have hC' := hCaches (j + 1) v htj1 hjt hvj1
      exact ancestorEq_trans (ih hjj hjt') (confirmedOf_step j v hChain hL hLT
        (onHonestChain_of_ancestorEq hC.2.1 hC.2.2.2.2) hL' hL'T
        (onHonestChain_of_ancestorEq hC'.2.1 hC'.2.2.2.2))

/-- **Lemma 90, growth.** The proof; the audited statement is in
`Statements/Executions/ConfirmedTipStatements.lean`. It is `lem90_confirmed_monotone_until` at every
time `t` (`confirmedMonotoneAfterHealing_iff`).

Why: by induction on the later step, with `confirmedOf_step` at each step: `v` is honest at every
step up to the later one, so the records and the caches at those steps are on the honest chain by
the two hypotheses.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot;
- `H`: the threshold of the caches; `i₁`: the step from which the facts hold. -/
theorem lem90_confirmed_monotone (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ H i₁ : ℕ)
    -- the honest confirmations form a chain from slot `s₀`
    (hChain : ConfirmationsChain S Sched x s₀)
    -- from the time of step `i₁` on, an honest validator's record is an honest confirmation it
    -- holds
    (hLatest : ∀ (i : ℕ) (v : V), x[i₁].time ≤ x[i].time → v ∉ Sched.adv (x[i].time : Int) →
      IsHonestConfirmation S Sched x s₀ (x[i][v].st).A.latest_confirmed ∧
        (x[i][v].st).A.latest_confirmed ∈ (x[i][v].st).S.T)
    -- from the time of step `i₁` on, an honest validator's caches are on the honest chain
    (hCaches : ∀ (i : ℕ) (v : V), x[i₁].time ≤ x[i].time → v ∉ Sched.adv (x[i].time : Int) →
      CachesOnChain S Sched x s₀ H (x[i][v].st)) :
    ConfirmedMonotoneAfterHealing S Sched x (x[i₁].time) :=
  (confirmedMonotoneAfterHealing_iff S Sched x _).2 fun t =>
    lem90_confirmed_monotone_until S Sched x s₀ H i₁ t hChain hLatest
      (fun i v h₁ _ h₂ => hCaches i v h₁ h₂)

/-- **Kit fact, two blocks on the honest chain at slots whose update is at most `t` are
compatible**, when the updaters' confirmations of the slots whose update is at most `t` form one
chain from slot `s₀`.

Why: both blocks are on the chain before the slot after the later of the two slots, whose update
is at most `t`; two blocks on the chain before a slot are compatible
(`onHonestChainBefore_compatible`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `t`: the
  bound; `σ`, `σ'`: the two slots; `B`, `B'`: the two blocks. -/
theorem compatible_of_onHonestChainAt (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ t σ σ' : ℕ) (B B' : Block V)
    -- the updaters' confirmations of the slots whose update is at most `t` form one chain
    (hChain : ∀ σ : ℕ, supportCutoff S (σ + 1) ≤ t → ConfirmationsChainBefore S Sched x s₀ (σ + 1))
    (hB : OnHonestChainAt S Sched x s₀ σ B) (hσ : supportCutoff S (σ + 1) ≤ t)
    (hB' : OnHonestChainAt S Sched x s₀ σ' B') (hσ' : supportCutoff S (σ' + 1) ≤ t) :
    B.compatible B' = true := by
  rcases le_total σ σ' with h | h
  · exact onHonestChainBefore_compatible S Sched x s₀ (σ' + 1) B B' (hChain σ' hσ')
      ⟨σ, Nat.lt_succ_of_le h, hB⟩ ⟨σ', Nat.lt_succ_self σ', hB'⟩
  · exact onHonestChainBefore_compatible S Sched x s₀ (σ + 1) B B' (hChain σ hσ)
      ⟨σ, Nat.lt_succ_self σ, hB⟩ ⟨σ', Nat.lt_succ_of_le h, hB'⟩

/-- **Kit fact, the finalized block of an honest state is on the chain at a slot whose update ran
by then.** Under the hypotheses of `justified_onHonestChainAt_of_caches` at the healed slot (the
honest attestations from the support cutoff of slot `s₀ + 1` on the chain, Lemma 82), when `v`'s
caches after `i` steps are on the honest chain: `v`'s finalized block is on the honest chain at a
slot whose next slot's support cutoff is at most the time of step `i`.

Why: the finalized block is the justified block or an ancestor of it (`CachesOnChain`), and the
justified block, above the threshold, is on the chain at such a slot
(`justified_onHonestChainAt_of_caches`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `H`: the
  threshold; `i`: the step; `v`: the validator. -/
theorem finalized_onHonestChainAt_of_caches (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ H i : ℕ) (v : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hRoots : RootsNameBlocksUntil S Sched x x[i].time) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hv : v ∉ Sched.adv (x[i].time : Int))
    (hC : CachesOnChain S Sched x s₀ H (x[i][v].st)) :
    ∃ σ : ℕ, supportCutoff S (σ + 1) ≤ x[i].time ∧
      OnHonestChainAt S Sched x s₀ σ (x[i][v].st).S.F := by
  obtain ⟨σ, hσ, hJ⟩ := justified_onHonestChainAt_of_caches S Sched x s₀ (supportCutoff S (s₀ + 1))
    H i v hU hMono hRoots hAdvQ (lem82_honest_attestations_on_chain S Sched x s₀ hDiv hMono) hOld hv
    hC.1
  exact ⟨σ, hσ, onHonestChainAt_of_ancestorEq hJ hC.2.2.2.2⟩

/-- **Kit fact, the confirmed tip of an honest state is on the chain at a slot whose update ran by
then.** When `v`'s record after `i` steps is on the honest chain at a slot whose next slot's
support cutoff is at most the time of step `i`, and its caches are on the honest chain, under the
hypotheses of `finalized_onHonestChainAt_of_caches`: so is `v`'s confirmed tip.

Why: the confirmed tip is the record or the finalized block (`ac_confirmed_cases`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `H`: the
  threshold; `i`: the step; `v`: the validator. -/
theorem confirmedOf_onHonestChainAt (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ H i : ℕ) (v : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hRoots : RootsNameBlocksUntil S Sched x x[i].time) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hv : v ∉ Sched.adv (x[i].time : Int))
    (hL : ∃ σ : ℕ, supportCutoff S (σ + 1) ≤ x[i].time ∧
      OnHonestChainAt S Sched x s₀ σ (x[i][v].st).A.latest_confirmed)
    (hC : CachesOnChain S Sched x s₀ H (x[i][v].st)) :
    ∃ σ : ℕ, supportCutoff S (σ + 1) ≤ x[i].time ∧
      OnHonestChainAt S Sched x s₀ σ (confirmedOf (x[i][v].st)) := by
  rcases ac_confirmed_cases (x[i][v].st).A (fg_to_ac (x[i][v].st).S) with ⟨-, h⟩ | ⟨-, h⟩
  · show ∃ σ : ℕ, supportCutoff S (σ + 1) ≤ x[i].time ∧
      OnHonestChainAt S Sched x s₀ σ (ac_confirmed (x[i][v].st).A (fg_to_ac (x[i][v].st).S))
    rw [h]
    exact hL
  · show ∃ σ : ℕ, supportCutoff S (σ + 1) ≤ x[i].time ∧
      OnHonestChainAt S Sched x s₀ σ (ac_confirmed (x[i][v].st).A (fg_to_ac (x[i][v].st).S))
    rw [h, fg_to_ac_F]
    exact finalized_onHonestChainAt_of_caches S Sched x s₀ H i v hDiv hMono hRoots hU hAdvQ hOld hv
      hC

/-- **Lemma 90, agreement, on the chain before a slot.** The proof; the audited statement is in
`Statements/Executions/ConfirmedTipStatements.lean`. From the time of step `i₁` to `t`: when the
updaters' confirmations of the slots whose update is at most `t` form one chain from slot `s₀`,
an honest validator's record is on the honest chain at a slot whose update ran by then, its caches
are on the honest chain, roots name blocks among what honest validators hold by `t`, and the
attestations behind the caches are as at the healed slot: the confirmed tips of two validators
honest through their steps are compatible.

Why: each confirmed tip is on the honest chain at a slot whose update ran by its step
(`confirmedOf_onHonestChainAt`), so at most `t`, and two such blocks are compatible
(`compatible_of_onHonestChainAt`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot;
- `H`: the threshold of the caches; `i₁`: the step from which the facts hold; `t`: the time up to
  which the confirmed tips are read.

On the chain before a slot: the two confirmed tips compared are on the chain at slots whose update
is at most `t`, which `ConfirmationsChainBefore` covers; the landed form reads `ConfirmationsChain`
at every slot. -/
theorem lem90_confirmed_agree_before (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ H i₁ t : ℕ)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hRoots : RootsNameBlocksUntil S Sched x t) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    -- the updaters' confirmations of the slots whose update is at most `t` form one chain
    (hChain : ∀ σ : ℕ, supportCutoff S (σ + 1) ≤ t → ConfirmationsChainBefore S Sched x s₀ (σ + 1))
    -- from the time of step `i₁` to `t`, an honest validator's record is on the honest chain at a
    -- slot whose update ran by then
    (hLatest : ∀ (i : ℕ) (v : V), x[i₁].time ≤ x[i].time → x[i].time ≤ t →
      v ∉ Sched.adv (x[i].time : Int) → ∃ σ : ℕ, supportCutoff S (σ + 1) ≤ x[i].time ∧
        OnHonestChainAt S Sched x s₀ σ (x[i][v].st).A.latest_confirmed)
    -- from the time of step `i₁` to `t`, an honest validator's caches are on the honest chain
    (hCaches : ∀ (i : ℕ) (v : V), x[i₁].time ≤ x[i].time → x[i].time ≤ t →
      v ∉ Sched.adv (x[i].time : Int) → CachesOnChain S Sched x s₀ H (x[i][v].st)) :
    ConfirmedAgreeBetween S Sched x (x[i₁].time) t := by
  rw [GoldilocksCorrectness.Proofs.View.confirmedAgreeBetween_unfold]
  intro v₁ v₂ i j h₁ h₂ hi hj hit hjt
  have hh₁ : v₁ ∉ Sched.adv (x[i].time : Int) := h₁ _ le_rfl
  have hh₂ : v₂ ∉ Sched.adv (x[j].time : Int) := h₂ _ le_rfl
  obtain ⟨σ, hσ, hB⟩ := confirmedOf_onHonestChainAt S Sched x s₀ H i v₁ hDiv hMono
    (hRoots.mono hit) hU hAdvQ hOld hh₁ (hLatest i v₁ hi hit hh₁) (hCaches i v₁ hi hit hh₁)
  obtain ⟨σ', hσ', hB'⟩ := confirmedOf_onHonestChainAt S Sched x s₀ H j v₂ hDiv hMono
    (hRoots.mono hjt) hU hAdvQ hOld hh₂ (hLatest j v₂ hj hjt hh₂) (hCaches j v₂ hj hjt hh₂)
  exact compatible_of_onHonestChainAt S Sched x s₀ t σ σ' _ _ hChain hB (le_trans hσ hit) hB'
    (le_trans hσ' hjt)

/-- **Lemma 90, growth, on the chain before a slot.** The proof; the audited statement is in
`Statements/Executions/ConfirmedTipStatements.lean`. Under the hypotheses of
`lem90_confirmed_agree_before`, the record also held in the tree: the confirmed tip of a validator
honest through the later of two steps, the later at a time at most `t`, only extends.

Why: by induction on the later step, with `confirmedOf_step_of_compatible` at each step: the
records and finalized blocks at the two steps of each step are on the honest chain at slots whose
update ran by then (the hypothesis on the record, `finalized_onHonestChainAt_of_caches`), so at
most `t`, and compatible (`compatible_of_onHonestChainAt`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot;
- `H`: the threshold of the caches; `i₁`: the step from which the facts hold; `t`: the time up to
  which the later confirmed tip is read.

On the chain before a slot: as `lem90_confirmed_agree_before`. -/
theorem lem90_confirmed_monotone_before (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ H i₁ t : ℕ)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hRoots : RootsNameBlocksUntil S Sched x t) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    -- the updaters' confirmations of the slots whose update is at most `t` form one chain
    (hChain : ∀ σ : ℕ, supportCutoff S (σ + 1) ≤ t → ConfirmationsChainBefore S Sched x s₀ (σ + 1))
    -- from the time of step `i₁` to `t`, an honest validator's record is on the honest chain at a
    -- slot whose update ran by then, and it holds it
    (hLatest : ∀ (i : ℕ) (v : V), x[i₁].time ≤ x[i].time → x[i].time ≤ t →
      v ∉ Sched.adv (x[i].time : Int) → (∃ σ : ℕ, supportCutoff S (σ + 1) ≤ x[i].time ∧
        OnHonestChainAt S Sched x s₀ σ (x[i][v].st).A.latest_confirmed) ∧
        (x[i][v].st).A.latest_confirmed ∈ (x[i][v].st).S.T)
    -- from the time of step `i₁` to `t`, an honest validator's caches are on the honest chain
    (hCaches : ∀ (i : ℕ) (v : V), x[i₁].time ≤ x[i].time → x[i].time ≤ t →
      v ∉ Sched.adv (x[i].time : Int) → CachesOnChain S Sched x s₀ H (x[i][v].st)) :
    ConfirmedMonotoneBetween S Sched x (x[i₁].time) t := by
  intro v i j hij hj hi hjt
  revert hjt
  induction j, hij using Nat.le_induction with
  | base => exact fun _ => ancestorEq_refl _
  | succ j hij ih =>
      intro hjt
      have hjj : HonestThrough x j v := fun t' ht' =>
        hj t' (le_trans ht' (by exact_mod_cast time_le_succ x j))
      have hjt' : x[j].time ≤ t := le_trans (time_le_succ x j) hjt
      have htj : x[i₁].time ≤ x[j].time := le_trans hi (time_mono x hij)
      have htj1 : x[i₁].time ≤ x[j + 1].time := le_trans htj (time_le_succ x j)
      have hvj : v ∉ Sched.adv (x[j].time : Int) := hjj _ le_rfl
      have hvj1 : v ∉ Sched.adv (x[j + 1].time : Int) := hj _ le_rfl
      obtain ⟨⟨σL, hσL, hL⟩, hLT⟩ := hLatest j v htj hjt' hvj
      obtain ⟨⟨σL', hσL', hL'⟩, hL'T⟩ := hLatest (j + 1) v htj1 hjt hvj1
      obtain ⟨σF, hσF, hF⟩ := finalized_onHonestChainAt_of_caches S Sched x s₀ H j v hDiv hMono
        (hRoots.mono hjt') hU hAdvQ hOld hvj (hCaches j v htj hjt' hvj)
      obtain ⟨σF', hσF', hF'⟩ := finalized_onHonestChainAt_of_caches S Sched x s₀ H (j + 1) v hDiv
        hMono (hRoots.mono hjt) hU hAdvQ hOld hvj1 (hCaches (j + 1) v htj1 hjt hvj1)
      have hc := fun σ σ' (B B' : Block V) => compatible_of_onHonestChainAt S Sched x s₀ t σ σ' B B'
        hChain
      exact ancestorEq_trans (ih hjj hjt') (confirmedOf_step_of_compatible j v hLT hL'T
        (hc _ _ _ _ hL' (le_trans hσL' hjt) hF' (le_trans hσF' hjt))
        (hc _ _ _ _ hL (le_trans hσL hjt') hL' (le_trans hσL' hjt))
        (hc _ _ _ _ hL (le_trans hσL hjt') hF (le_trans hσF hjt')))

/-- **Kit fact, the first step at a time.** In an execution where every time is reached, the step
right after the tick at `t ≥ 1` is the first step at the time `t`: a step at that time or later
comes no earlier.

Why: every step up to the tick at `t` is at a time before `t` (`time_lt_iff_le_stepBefore`), and
the step after it is at `t` (`stepBefore_spec`).

The variables:
- `x`: the execution; `t`: the time; `i`: the step.

Read aloud: a step at a time at least `t` comes at or after the first step at `t`. -/
theorem stepBefore_succ_le_of_time_le {x : AtomicExec (protocol S) Sched}
    -- every time is reached
    (hDiv : TimeDiverges x.toTrace) {t i : ℕ}
    -- `t` is at least `1`
    (ht : 1 ≤ t)
    -- step `i` is at a time at least that of the step after the tick at `t`
    (hi : x[stepBefore x t + 1].time ≤ x[i].time) :
    stepBefore x t + 1 ≤ i := by
  obtain ⟨-, -, h2⟩ := stepBefore_spec x hDiv ht
  by_contra hlt
  have := (time_lt_iff_le_stepBefore x hDiv (i := i) ht).2 (by omega)
  omega

end Lemma90

end GoldilocksCorrectness.Proofs.Executions
