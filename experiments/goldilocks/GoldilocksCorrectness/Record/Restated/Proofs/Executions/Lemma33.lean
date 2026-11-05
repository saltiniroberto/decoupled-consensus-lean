module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma39
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma40
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma41
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.ConfirmationSteps
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.TickUpdateState
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Proofs.Executions.Lemma39
public import GoldilocksCorrectness.Proofs.Executions.Lemma41
public import GoldilocksCorrectness.Proofs.Executions.ConfirmationSteps
public import GoldilocksCorrectness.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Proofs.Routines.Blocks

@[expose] public section

/-!
# Lemma33, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma33.lean`, over a model `M` whose facts
`F` hold, for an execution `x` of `protocolOf M S`: a saved confirmation is kept, the saved
confirmation of a lock entry's slot, and Lemma 33, a slow lock is compatible with the confirmations
saved slot by slot. The page's routine-level theorems are the facts' fields or have their twins in
phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart supportCutoff)
open GoldilocksCorrectness.Proofs.Routines (lockDeadline_injective one_le_Δ slotStart_eq
  slot_eq_of_mem supportCutoff_cast supportCutoff_eq supportCutoff_lt_of_lt voteTime_eq)

open GoldilocksCorrectness.Proofs.Routines (compatible_of_ancestorEq_both)

namespace GoldilocksCorrectness.Record.Proofs.Executions

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor ConfirmationUpdated)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (expireLocks)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_trans compatible_iff
  compatible_of_ancestorEq_compatible voteTime_ne_cutoff)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

variable {S : Setup V} {A : Activity V}

/-- A saved confirmation of slot `s` present on `v`'s node state after a step `i` later than `v`'s tick
to the support cutoff of slot `s + 1` is present with the same block after every later step `i'`
(T-RC5-1, at steps): a step that changes it is `v`'s tick to that support cutoff
(`step_saved_changed`), which is unique (`tick_unique`) and before `i`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `x`: the execution; `v`: the validator; `s`: the slot of the confirmation; `C'`: the block;
  `i ≤ i'`: the two steps.

Read aloud: once `v`'s update of slot `s + 1` is past, the saved confirmation of slot `s` stays. -/
theorem saved_confirmation_kept (U : UniformSchedule M.toSlotLayout)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (v : V) (s : ℕ) (C' : Block V) {i i' : ℕ}
    -- `v`'s tick to the support cutoff of slot `s + 1` is the step `x.tickStep v` names, before `i`
    (htick : x.lbl (x.tickStep v (M.supportCutoff S.C (s + 1))) = Event.tick v (M.supportCutoff S.C (s + 1)))
    (hc : x.tickStep v (M.supportCutoff S.C (s + 1)) < i)
    -- `i'` is `i` or later
    (hii' : i ≤ i')
    -- `v`'s node state after `i` steps has `C'` saved as the confirmation of slot `s`
    (hSaved : (x.st i v).savedConfirmation s = some C') :
    (x.st i' v).savedConfirmation s = some C' := by
  induction i', hii' using Nat.le_induction with
  | base => exact hSaved
  | succ j hj ih =>
    by_contra hne
    have hne' : (x.st (j + 1) v).savedConfirmation s ≠ (x.st j v).savedConfirmation s := by
      rw [ih]; exact hne
    obtain ⟨hl, -⟩ := (step_saved_changed M F U) x R E j v s hne'
    have := E.tick_unique j _ v _ hl htick
    omega

/-- Two outcomes `n₁`, `n₂` of the confirmation update of slot `s` from one node state `n` save the
same confirmations, slot by slot. For `s = 0` both keep `n`'s. For `s ≥ 1` both keep `n`'s at
every slot other than `s − 1`, and at `s − 1` one saves a block exactly when the other saves the
same block (`confirmationUpdated_saved_eq`, the update's walk ending at one block).

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`: the parameters; `n`: the node state before the update; `n₁`, `n₂`: two node states
  after it; `t`: the time; `s`: the slot.

Read aloud: every outcome of the update saves the same confirmations. -/
theorem confirmationUpdated_savedConfirmation_eq {C : Config} {P : Provisional V} {n n₁ n₂ : M.N}
    {t : Time} {s : Slot}
    -- `n₁` and `n₂` are what the update of slot `s` leaves from `n`
    (h₁ : ConfirmationUpdated M C P n t s n₁) (h₂ : ConfirmationUpdated M C P n t s n₂) :
    M.savedConfirmation n₁ = M.savedConfirmation n₂ := by
  rcases id h₁ with ⟨hs0, hS₁, -⟩ | ⟨hs, -, -, -, hO₁, -⟩
  · rcases h₂ with ⟨-, hS₂, -⟩ | ⟨hs, -⟩
    · exact hS₁.trans hS₂.symm
    · exact absurd hs0 (Nat.one_le_iff_ne_zero.1 hs)
  · have hO₂ : ∀ j : Slot, j ≠ s - 1 → n₂.savedConfirmation j = n.savedConfirmation j := by
      rcases id h₂ with ⟨hs0, -⟩ | ⟨-, -, -, -, hO₂, -⟩
      · exact absurd hs0 (Nat.one_le_iff_ne_zero.1 hs)
      · exact hO₂
    funext j
    by_cases hj : j = s - 1
    · subst hj
      cases hc₁ : n₁.savedConfirmation (s - 1) with
      | some H =>
          exact hc₁.trans ((confirmationUpdated_saved_eq M F) hs h₁ h₂ hc₁).symm
      | none =>
          cases hc₂ : n₂.savedConfirmation (s - 1) with
          | none => exact hc₁.trans hc₂.symm
          | some H =>
              have h := (confirmationUpdated_saved_eq M F) hs h₂ h₁ hc₂
              rw [hc₁] at h
              exact absurd h (by simp)
    · exact (hO₁ j hj).trans (hO₂ j hj).symm

/-- When `v`'s node state just after the support cutoff `c` of slot `s + 1` holds a lock entry with
the deadline of a lock of slot `s`, `v`'s saved confirmations just after are those of every outcome
`(n', sent)` of the tick at `c` from the state `v`'s tick to `c` starts from, when that state is awake
for slot `s + 1`.

Why: the tick at the cutoff `c` does one of three things (`step_cases_lock_saved`). It cannot keep
a subset of the entries: the entry would then be held before `c`, and Lemma 39 would place the
update that added it, the one of slot `s + 1` since the deadline names the slot, strictly before
`c`. It cannot revoke: `c` is not a vote time. So it ran the update of slot `s + 1` from the state it starts
from; `(n', sent)` is an update of slot `s + 1` from the same state (the field
`tick_supportCutoff_confirmation` of `F.tk2`), and two outcomes of the update save the same
confirmations (`confirmationUpdated_savedConfirmation_eq`). The outcome and the wake condition are read
at `v`'s tick input, the state its own tick reads (rule R3, finding F-50-5).

The landed hypothesis names the answer `A'` of the confirmation update; the twin takes an outcome
of the tick under the wake condition.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `U`: its slot layout is uniform;
- `x`: the execution; `v`: the validator; `s`: the slot of the lock; `e`: the lock entry;
  `n'`, `sent`: the outcome of the tick.

Read aloud: a lock of slot `s` held just after the update of slot `s + 1` means that update ran,
and the saved confirmations just after are those of every outcome of the tick there. -/
theorem saved_eq_update_of_entry (U : UniformSchedule M.toSlotLayout)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (v : V) (s : ℕ) (e : M.LE)
    -- `v` holds `e` just after the support cutoff of slot `s + 1`
    (he : e ∈ (x.tickOutput v (M.supportCutoff S.C (s + 1))).lockEntries)
    -- `e` has the deadline of a lock of slot `s`
    (hd : e.d = S.C.t_ (s + S.C.k) + 5 * S.C.Δ)
    (n' : M.N) (sent : List (NamedObject V))
    -- `(n', sent)` is an outcome of the tick at the support cutoff of slot `s + 1` from the state `v`'s
    -- tick to it starts from
    (hUpdate : .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (M.supportCutoff S.C (s + 1)))
      ((M.supportCutoff S.C (s + 1) : ℕ) : Int))
    -- that state is awake for slot `s + 1`
    (hAwake : AwakeFor M S.C (x.tickInput v (M.supportCutoff S.C (s + 1))) (s + 1)) :
    (x.tickOutput v (M.supportCutoff S.C (s + 1))).savedConfirmation =
      M.savedConfirmation n' := by
  -- `e` is traced to `v`'s tick to the support cutoff of its slot `s + 1` (Lemma 39), at a step before the step after
  -- `v`'s tick to that cutoff: that tick is the step `x.tickStep v (M.supportCutoff S.C (s + 1))` itself
  obtain ⟨s₂, hd₂, hk, hlk, -, -⟩ := (lockTracedAfterTick_of_mem M F U) S A x R E v
    (x.tickStep v (M.supportCutoff S.C (s + 1)) + 1) e he
  have hs₂ : s₂ = s := lockDeadline_injective S (hd₂.symm.trans hd)
  subst hs₂
  -- the cutoff, read as a time, is the support cutoff of its slot, which is `s + 1` (`U`)
  have hsl : S.C.slot ((M.supportCutoff S.C (s₂ + 1) : ℕ) : Int) = s₂ + 1 := by
    rw [GoldilocksCorrectness.Proofs.Routines.slot_natCast,
      ← (GoldilocksCorrectness.Record.Proofs.Routines.slot_natCast M.toSlotLayout F.sched U)]
    exact ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_slot M.toSlotLayout F.sched) S s₂).1
  have hcut : ((M.supportCutoff S.C (s₂ + 1) : ℕ) : Int) =
      S.C.t_ (S.C.slot ((M.supportCutoff S.C (s₂ + 1) : ℕ) : Int)) + 2 * S.C.Δ := by
    rw [hsl]
    exact (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_cast M.toSlotLayout F.sched U) S (s₂ + 1)
  -- the outcome `(n', sent)` is an update of slot `s + 1` from the state `v`'s tick starts from
  have hvk : v ∉ A.corrupted (x.tickStep v (M.supportCutoff S.C (s₂ + 1))) := E.not_mem_corrupted_of_tick hlk
  have hInv := (lem11_node_invariant M F S A x R E (x.tickStep v (M.supportCutoff S.C (s₂ + 1))) v hvk).1
  have hCU' := F.tk2.tick_supportCutoff_confirmation S.C S.P S.X _ _ n' sent hUpdate hInv hcut
    (by rw [hsl]; exact hAwake)
  unfold Trace.tickOutput
  rcases (step_cases_lock_saved M F) x R E (x.tickStep v (M.supportCutoff S.C (s₂ + 1))) v with
      ⟨-, hsub⟩ | ⟨t, hl', -, ht, -⟩ | ⟨t, hl', -, -, -, hCU⟩
  · -- the tick kept a subset of the entries: `e` was held at the step of `v`'s tick, impossible, since an entry held
    -- there was added at an earlier tick of `v` to the same cutoff
    exfalso
    have he' : e ∈ (x.st (x.tickStep v (M.supportCutoff S.C (s₂ + 1))) v).lockEntries := hsub he
    obtain ⟨s', hd', hlt, -, -, -⟩ := (lockTracedAfterTick_of_mem M F U) S A x R E v _ e he'
    have hb' : s' = s₂ := lockDeadline_injective S (hd'.symm.trans hd)
    rw [hb'] at hlt
    exact lt_irrefl _ hlt
  · -- the tick revoked: the cutoff is not a vote time
    exfalso
    have htc : t = M.supportCutoff S.C (s₂ + 1) := by
      have h := hlk.symm.trans hl'
      injection h with h h'
      exact h'.symm
    subst htc
    exact voteTime_ne_cutoff ht hcut
  · -- the tick ran the update from the state it starts from; the step's outcome and `(n', sent)` save the same
    -- confirmations
    have htc : t = M.supportCutoff S.C (s₂ + 1) := by
      have h := hlk.symm.trans hl'
      injection h with h h'
      exact h'.symm
    subst htc
    rw [hsl] at hCU hCU'
    exact (confirmationUpdated_savedConfirmation_eq M F) hCU hCU'

/-- Every lock entry `e` of `v`'s node state after the step `i` is a lock of a slot `s` whose update ran
at a step before `i`: the deadline of `e` is `S.C.t_ (s + S.C.k) + 5 · S.C.Δ`, `v`'s tick to the support
cutoff of slot `s + 1` is at a step before `i` and is the step `x.tickStep v` names, and `v`'s node state after the step `i` has a
saved confirmation of slot `s` that is `e`'s block or a descendant of it.

Why: `lockTracedAfterTick_of_mem` (Lemma 39) gives `v`'s tick to the cutoff, at a step before `i`, every
outcome of which holds an entry `e₀` with `e`'s deadline whose block is the confirmation of slot `s` the
outcome saves or an ancestor of it, with `e`'s block an ancestor of `e₀`'s or `e₀`'s itself; the tick's
own outcome is `v`'s state after it, and no later step changes the saved confirmation of slot `s`: a step
that does is `v`'s tick to that cutoff (`step_saved_changed`), which is unique (`tick_unique`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `x`: the execution; `i`: the step; `v`: the validator; `e`: the lock entry.

Read aloud: a lock entry is on its slot's saved confirmation or an ancestor of it. -/
theorem lock_entry_saved_confirmation (U : UniformSchedule M.toSlotLayout)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (i : ℕ) (v : V) (e : M.LE)
    -- `e` is a lock entry of `v`'s node state after the step `i`
    (he : e ∈ (x.st i v).lockEntries) :
    ∃ s : ℕ, e.d = S.C.t_ (s + S.C.k) + 5 * S.C.Δ ∧
      x.tickStep v (M.supportCutoff S.C (s + 1)) < i ∧
      x.lbl (x.tickStep v (M.supportCutoff S.C (s + 1))) = Event.tick v (M.supportCutoff S.C (s + 1)) ∧
      ∃ C' : Block V, (x.st i v).savedConfirmation s = some C' ∧
        e.B.AncestorEq C' := by
  obtain ⟨s, hd, hlt, hlab, hawk, hout⟩ := (lockTracedAfterTick_of_mem M F U) S A x R E v i e he
  -- the outcome `v`'s tick to the cutoff took
  obtain ⟨n', sent, hok, hst, -⟩ := R.tick _ v _ hlab
  have hok' : .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (M.supportCutoff S.C (s + 1)))
      ((M.supportCutoff S.C (s + 1) : ℕ) : Int) := by
    unfold Trace.tickInput
    exact hok
  obtain ⟨e₀, -, -, -, -, ⟨C', hC', hB₀⟩, -, heB, -⟩ := hout n' sent hok' hawk
  -- the saved confirmation of slot `s` after that tick is `C'`, and no later step up to `i` changes it:
  -- a step that does is `v`'s tick to the same cutoff (`step_saved_changed`), the same step (`tick_unique`)
  have hkeep : ∀ j : ℕ, x.tickStep v (M.supportCutoff S.C (s + 1)) + 1 ≤ j → j ≤ i →
      (x.st j v).savedConfirmation s = some C' := by
    intro j h1 h2
    induction j, h1 using Nat.le_induction with
    | base => rw [hst]; exact hC'
    | succ j hj ih =>
      have ih' := ih (by omega)
      by_contra hne
      have hne' : (x.st (j + 1) v).savedConfirmation s ≠ (x.st j v).savedConfirmation s := by
        rw [ih']; exact hne
      obtain ⟨hl, -⟩ := (step_saved_changed M F U) x R E j v s hne'
      have := E.tick_unique j _ v _ hl hlab
      omega
  exact ⟨s, hd, hlt, hlab, C', hkeep i (by omega) le_rfl, ancestorEq_trans heB hB₀⟩

/-- **Lemma 33, slot-by-slot compatible saved confirmations make a slow or same-slot lock
compatible.** The proof; the audited statement is in
`Statements/Executions/HealingStatements.lean`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the slot of `v`'s lock;
- `v`, `w`: the two validators; `e_v`, `e_w`: their lock entries.

Read aloud: when the two validators' confirmations saved for each slot are compatible, a lock of `v`
of slot `s` that is slow, or has the deadline of `w`'s live lock, is compatible with `w`'s lock. -/
theorem lem33_slow_lock_compatible_of_slotwise_confirmations (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (s : ℕ) (v w : V) (e_v e_w : M.LE)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    -- `v` and `w` each tick to the support cutoff `c` of slot `s + 1` (T-RC5-1)
    (htick_v : x.lbl (x.tickStep v (M.supportCutoff S.C (s + 1))) = Event.tick v (M.supportCutoff S.C (s + 1)))
    (htick_w : x.lbl (x.tickStep w (M.supportCutoff S.C (s + 1))) = Event.tick w (M.supportCutoff S.C (s + 1)))
    -- at the slot `s'` whose lock deadline `e_w` has, the saved confirmations of slot `s'` of `v`
    -- and `w`, on the states their ticks to `c` leave, are compatible
    (hCompat : ∀ s' : ℕ, e_w.d = S.C.t_ (s' + S.C.k) + 5 * S.C.Δ → ∀ Cv Cw : Block V,
      (x.tickOutput v (M.supportCutoff S.C (s + 1))).savedConfirmation s' = some Cv →
      (x.tickOutput w (M.supportCutoff S.C (s + 1))).savedConfirmation s' = some Cw →
      Cv.compatible Cw = true)
    -- `e_v` is a lock entry of slot `s` on the state `v`'s tick to `c` leaves
    (he_v : e_v ∈ (x.tickOutput v (M.supportCutoff S.C (s + 1))).lockEntries)
    (hd_v : e_v.d = S.C.t_ (s + S.C.k) + 5 * S.C.Δ)
    -- `e_w` is a lock entry on the state `w`'s tick to `c` leaves, with its deadline after `c + 1`
    (he_w : e_w ∈ (x.tickOutput w (M.supportCutoff S.C (s + 1))).lockEntries)
    (hlive_w : ((M.supportCutoff S.C (s + 1) + 1 : ℕ) : Int) < e_w.d)
    -- `e_v`'s block passes the slow test of slot `s` on the state `v`'s tick to `c` starts from, or
    -- `e_w` is a lock entry of slot `s` too
    (hSlowOrSame :
      M.slow_test S.C (x.tickInput v (M.supportCutoff S.C (s + 1))) s e_v.B = true ∨
        e_w.d = e_v.d) :
    e_v.B.compatible e_w.B = true := by
  have hΔ := one_le_Δ S
  -- the slot `s'` of `e_w`, `w`'s tick to its update, and `w`'s saved confirmation of it
  obtain ⟨s', hd_w, hc_w, hlab_w, C_w, hC_w, hB_w⟩ :=
    (lock_entry_saved_confirmation M F U) x R E (x.tickStep w (M.supportCutoff S.C (s + 1)) + 1) w e_w he_w
  -- `s' ≤ s`: `w` does not set its clock back between its tick to the support cutoff of slot
  -- `s' + 1` and its tick to `c`
  have hcc : M.supportCutoff S.C (s' + 1) ≤ M.supportCutoff S.C (s + 1) := by
    rcases Nat.lt_or_ge (x.tickStep w (M.supportCutoff S.C (s' + 1))) (x.tickStep w (M.supportCutoff S.C (s + 1))) with
      hlt | hge
    · exact E.clock_mono _ _ w _ _ hlt
        (Activity.not_mem_corrupted_of_mem_active (E.tick_active _ w _ htick_w).1)
        (Or.inl hlab_w) (Or.inl htick_w)
    · have heq : x.tickStep w (M.supportCutoff S.C (s' + 1)) = x.tickStep w (M.supportCutoff S.C (s + 1)) := by omega
      rw [heq, htick_w] at hlab_w
      injection hlab_w with _ h
      omega
  have hle : s' ≤ s := by
    by_contra h
    have := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_lt_of_lt M.toSlotLayout F.sched) S (show s + 1 < s' + 1 by omega)
    omega
  -- `s + 1 − k ≤ s'`: `e_w` is still live at `c + 1`
  have hlow : s + 1 - S.C.k ≤ s' := by
    by_cases hkb : S.C.k ≤ s + 1
    · refine (lem41_slot_of_live_entry M F U) S (s + 1 - S.C.k)
        s' (M.supportCutoff S.C (s + 1) + 1) e_w hd_w hlive_w ?_
      rw [Nat.sub_add_cancel hkb, (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U)]
      omega
    · omega
  rcases Nat.lt_or_eq_of_le hle with hlt | heq
  · -- `s' < s`: the two locks are of different slots, so `e_v` passed the slow test
    rcases hSlowOrSame with hSlow | hSame
    · obtain ⟨-, hj⟩ :=
        (GoldilocksCorrectness.Record.Statements.Routines.lem37_slow_test_saved_confirmations F) S.C _ s
          e_v.B hSlow
      obtain ⟨C', hCj, -, hBj⟩ := hj s' hlow hlt
      -- `v`'s tick to `c` keeps the saved confirmation of slot `s'`: a step that changes it is `v`'s
      -- tick to the support cutoff of slot `s' + 1`, earlier than `c`
      have hCj' : (x.tickOutput v (M.supportCutoff S.C (s + 1))).savedConfirmation s' = some C' := by
        by_contra hne
        have hne' : (x.st (x.tickStep v (M.supportCutoff S.C (s + 1)) + 1) v).savedConfirmation s' ≠
            (x.st (x.tickStep v (M.supportCutoff S.C (s + 1))) v).savedConfirmation s' := by
          intro h
          exact hne (by unfold Trace.tickOutput; rw [h]; exact hCj)
        obtain ⟨hl, -⟩ := (step_saved_changed M F U) x R E _ v s' hne'
        rw [htick_v] at hl
        injection hl with _ h
        have := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_lt_of_lt M.toSlotLayout F.sched) S (show s' + 1 < s + 1 by omega)
        omega
      exact compatible_of_ancestorEq_both hBj hB_w (hCompat s' hd_w C' C_w hCj' hC_w)
    · exfalso
      have : s' = s := lockDeadline_injective S (hd_w.symm.trans (hSame.trans hd_v))
      omega
  · -- `s' = s`: both locks are of slot `s`
    obtain ⟨s'', hd_v', -, -, C_v, hC_v, hB_v⟩ :=
      (lock_entry_saved_confirmation M F U) x R E (x.tickStep v (M.supportCutoff S.C (s + 1)) + 1) v e_v he_v
    have hbv : s'' = s := lockDeadline_injective S (hd_v'.symm.trans hd_v)
    rw [hbv] at hC_v
    rw [heq] at hC_w hd_w
    exact compatible_of_ancestorEq_both hB_v hB_w
      (hCompat s hd_w C_v C_w hC_v hC_w)

end GoldilocksCorrectness.Record.Proofs.Executions

