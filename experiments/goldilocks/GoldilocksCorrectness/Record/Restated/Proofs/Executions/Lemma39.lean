module
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.ConfirmationStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.LockSteps
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma40
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Wake
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Confirmation
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Locks
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.InvariantStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.TickDefs
public import GoldilocksCorrectness.Proofs.Executions.Lemma39

@[expose] public section

/-!
# Lemma39, over a model

The definition and the theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma39.lean`, over a
model `M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: the invariant `LockTraced`
of a validator's lock entries, kept by every step (the theorems `step_cases_lock_saved` of the
record's `LockSteps` page and the predicates `LocksRevoked`, `ConfirmationUpdated`), and Lemma 39,
where a lock entry comes from. The update's clause states every outcome of the tick at the support
cutoff under the wake condition (template A3); the entry one outcome adds has a counterpart in every
other (`confirmationUpdated_new_entry`). The page's routine-level theorems are the facts' fields or
have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (supportCutoff)
open GoldilocksCorrectness.Proofs.Routines (one_le_Δ supportCutoff_cast supportCutoff_eq)

open GoldilocksCorrectness.Proofs.Routines (acState_initial_eq initial_eq)

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
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- A lock entry `e` that one outcome `n₁` of the confirmation update of slot `s ≥ 1` from `n` adds
(the second case of `confirmationUpdated_entries_cases`: the update saves `H`, no live entry of `n`
vetoes it, `e`'s block is lockable under `H`, and `e` has the slot's deadline) has a counterpart
`e₀` in every other outcome `n₂`: an entry with that deadline on the deepest lockable block, which
is `e`'s block or a descendant of it; `e₀`'s block is a non-genesis block of the frame's tree on
the chain of the confirmation `n₂` saves, a fast block of `n₂` or passing the slow test. The update
saves the same confirmation in every outcome (`confirmationUpdated_saved_eq`), and locks the
deepest lockable block there.

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`: the parameters; `n`: the node state before the update; `n₁`, `n₂`: two node states
  after it; `t`: the time; `s`: the slot; `e`: the entry `n₁` adds.

Read aloud: the lock one outcome of the update adds is, pulled forward to the deepest lockable
block, a lock of every outcome. -/
theorem confirmationUpdated_new_entry {C : Config} {P : Provisional V} {n n₁ n₂ : M.N}
    {t : Time} {s : Slot} {e : M.LE}
    -- the slot is not the first
    (hs : 1 ≤ s)
    -- `n₁` and `n₂` are what the update of slot `s` leaves from `n`
    (h₁ : ConfirmationUpdated M C P n t s n₁) (h₂ : ConfirmationUpdated M C P n t s n₂)
    -- `n₁` adds `e`: it saves some `H` no live entry vetoes, under which `e`'s block is lockable,
    -- and `e` has the slot's deadline
    (hnew : ∃ H : Block V, n₁.savedConfirmation (s - 1) = some H ∧
      M.live_lock_vetoes n t H = false ∧
      GoldilocksCorrectness.Record.Statements.Routines.Lockable M C P n (s - 1) H e.B ∧
      e.d = C.t_ (s - 1 + C.k) + 5 * C.Δ) :
    ∃ e₀ ∈ n₂.lockEntries, e₀.d = e.d ∧ e.B.AncestorEq e₀.B ∧ e₀.B ∈ (M.fg_to_ac n).tree ∧
      e₀.B ≠ Block.genesis ∧
      (∃ C' : Block V, n₂.savedConfirmation (s - 1) = some C' ∧ e₀.B.AncestorEq C') ∧
      (e₀.B ∈ n₂.fastBlocks ∨ M.slow_test C n (s - 1) e₀.B = true) := by
  obtain ⟨H, hS, hv, hL, hd⟩ := hnew
  have hS₂ := confirmationUpdated_saved_eq M F hs h₁ h₂ hS
  obtain ⟨-, -, -, hv0⟩ :=
    GoldilocksCorrectness.Record.Proofs.Routines.confirmationUpdated_saved_some hs h₂ hS₂
  obtain ⟨-, hfast, -, hsome⟩ := hv0 hv
  obtain ⟨L, hLL, hall⟩ :=
    GoldilocksCorrectness.Record.Proofs.Routines.exists_deepest_lockable ⟨e.B, hL⟩
  obtain ⟨-, -, e₀, he₀, hB₀, hd₀⟩ := hsome L hLL hall
  obtain ⟨hT, hg, hBH, hft⟩ := hLL
  refine ⟨e₀, he₀, hd₀.trans hd.symm, hB₀ ▸ hall e.B hL, hB₀ ▸ hT, hB₀ ▸ hg,
    ⟨H, hS₂, hB₀ ▸ hBH⟩, ?_⟩
  rw [hB₀]
  rcases hft with hf | hsl
  · exact Or.inl ((hfast L).2 ⟨hT, hg, hBH, hf⟩)
  · exact Or.inr hsl

/-- `LockTraced M x v i e`: the lock entry `e`, held by the validator `v` at the step `i` of `x`,
was added by `v`'s confirmation update of the slot `s` its deadline names. Write `c` for the support
cutoff of slot `s + 1` and `X` for `v`'s node state before `c`. The deadline of `e` is
`S.C.t_ (s + S.C.k) + 5 · S.C.Δ`; the step `stepBefore M x c` comes before `i`; `v`'s tick at `c`
starts from a state whose `awakeSince` is some time at most the duty window's start of slot
`s + 1`; and every outcome `(n', sent)` of the tick at `c` from `X`, when `X` is awake for slot
`s + 1` (`AwakeFor`), holds an entry `e₀` with the deadline of `e`, on a block of the tree of
`M.fg_to_ac X` other than the genesis block that is the confirmation `n'` saves for slot `s` or an
ancestor of it, a fast block of `n'` or passing the slow test (`M.slow_test` on `X`), such that the
block of `e` is the block of `e₀` or an ancestor of it, and at every step after `stepBefore M x c`
up to `i`, `v` holds an entry with the deadline of `e` whose block is the block of `e` or a
descendant of it, and the block of `e₀` or an ancestor of it.

The landed definition names the update's answer; the record's states every outcome of the tick
under the wake condition. At the spec's model the two agree
(`goldilocks_LockTraced`).

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `v`: the validator; `i`: the step; `e`: the lock entry.

Read aloud: `e` was added by `v`'s update of the slot its deadline names, and has been traced
since by entries between it and the added one. -/
def LockTraced (S : Setup V) (x : Trace V (NamedObject V) M.N) (v : V)
    (i : ℕ) (e : M.LE) : Prop :=
  ∃ s : ℕ, e.d = S.C.t_ (s + S.C.k) + 5 * S.C.Δ ∧
    x.stepBefore (M.supportCutoff S.C (s + 1)) < i ∧
    (∃ τ : Time, (x.tickInput v (M.supportCutoff S.C (s + 1))).awakeSince = some τ ∧ τ ≤ duty_window_start S.C (s + 1)) ∧
    ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.stateBefore (M.supportCutoff S.C (s + 1)) v)
        ((M.supportCutoff S.C (s + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.stateBefore (M.supportCutoff S.C (s + 1)) v) (s + 1) →
      ∃ e₀ ∈ M.lockEntries n', e₀.d = e.d ∧
        e₀.B ∈ (M.fg_to_ac (x.stateBefore (M.supportCutoff S.C (s + 1)) v)).tree ∧
        e₀.B ≠ Block.genesis ∧
        (∃ C' : Block V, M.savedConfirmation n' s = some C' ∧ e₀.B.AncestorEq C') ∧
        (e₀.B ∈ M.fastBlocks n' ∨
          M.slow_test S.C (x.stateBefore (M.supportCutoff S.C (s + 1)) v) s e₀.B = true) ∧
        e.B.AncestorEq e₀.B ∧
        ∀ i' : ℕ, x.stepBefore (M.supportCutoff S.C (s + 1)) < i' → i' ≤ i →
          ∃ e' ∈ (x.st i' v).lockEntries, e'.d = e.d ∧ e.B.AncestorEq e'.B ∧
            e'.B.AncestorEq e₀.B

/-- A traced entry at the step `i` traces, at the step `i + 1`, every entry held then with its
deadline on its block or an ancestor of it: the same update added it.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `v`: the validator; `i`: the step; `e`: the entry at `i`; `e'`: the entry
  at `i + 1`.

Read aloud: a lock entry traced at step `i` traces every entry at step `i + 1` with its deadline on
its block or an ancestor of it. -/
theorem lockTraced_succ {S : Setup V} {x : Trace V (NamedObject V) M.N}
    {v : V} {i : ℕ} {e e' : M.LE}
    -- `e` is traced at the step `i`
    (h : LockTraced M S x v i e)
    -- `e'` has the deadline of `e`
    (hd : e'.d = e.d)
    -- the block of `e'` is the block of `e` or an ancestor of it
    (hB : e'.B.AncestorEq e.B)
    -- `v` holds `e'` at the step `i + 1`
    (he' : e' ∈ (x.st (i + 1) v).lockEntries) :
    LockTraced M S x v (i + 1) e' := by
  obtain ⟨s, hdb, h1, h2, h3⟩ := h
  refine ⟨s, hd.trans hdb, by omega, h2, fun n' sent hrun hA => ?_⟩
  obtain ⟨e₀, he₀, hd₀, hT, hG, hC, hF, hB₀, h4⟩ := h3 n' sent hrun hA
  refine ⟨e₀, he₀, hd₀.trans hd.symm, hT, hG, hC, hF, ancestorEq_trans hB hB₀,
    fun i' hi₁ hi₂ => ?_⟩
  rcases Nat.lt_or_eq_of_le hi₂ with hlt | heq
  · obtain ⟨e'', he'', hd'', hB₁, hB₂⟩ := h4 i' hi₁ (by omega)
    exact ⟨e'', he'', hd''.trans hd.symm, ancestorEq_trans hB hB₁, hB₂⟩
  · rw [heq]
    exact ⟨e', he', rfl, ancestorEq_refl _, ancestorEq_trans hB hB₀⟩

omit [RootOrder] in
/-- A natural-number time that is the support cutoff of its slot `s + 1`, read as an integer, is
`M.supportCutoff S.C (s + 1)`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `t`: the time; `s`: the slot before `t`'s slot.

Read aloud: a time that is the support cutoff of its slot `s + 1` is the support cutoff of slot
`s + 1`. -/
theorem eq_supportCutoff_of_cast (U : UniformSchedule M.toSlotLayout) (S : Setup V) {t s : ℕ}
    -- `t` is the support cutoff of its slot
    (ht : (t : Int) = S.C.t_ (S.C.slot (t : Int)) + 2 * S.C.Δ)
    -- the slot of `t` is `s + 1`
    (hslot : S.C.slot (t : Int) = s + 1) :
    t = M.supportCutoff S.C (s + 1) := by
  have h1 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_cast M.toSlotLayout F.sched U) S (s + 1)
  rw [hslot] at ht
  have : (t : Int) = ((M.supportCutoff S.C (s + 1) : ℕ) : Int) := by rw [h1]; exact ht
  exact_mod_cast this

/-- `LockTracedAfterTick M S x v i e`: the lock entry `e`, held by the validator `v` at the step `i`
of `x`, was added by `v`'s confirmation update of the slot `s` its deadline names, at `v`'s own tick
to the support cutoff `c` of slot `s + 1`. Write `X` for the node state `v`'s tick to `c` reads (`x.tickInput v c`). The deadline
of `e` is `S.C.t_ (s + S.C.k) + 5 · S.C.Δ`; the step `x.tickStep v c` comes before `i` and is `v`'s
tick to `c`; that tick starts from a state whose `awakeSince` is some time at most the duty window's
start of slot `s + 1`; and every outcome `(n', sent)` of the tick at `c` from `X`, when `X` is awake
for slot `s + 1` (`AwakeFor`), holds an entry `e₀` with the deadline of `e`, on a block of the tree
of `M.fg_to_ac X` other than the genesis block that is the confirmation `n'` saves for slot `s` or
an ancestor of it, a fast block of `n'` or passing the slow test (`M.slow_test` on `X`), such that
the block of `e` is the block of `e₀` or an ancestor of it, and at every step after `v`'s tick to
`c` up to `i`, `v` holds an entry with the deadline of `e` whose block is the block of `e` or a
descendant of it, and the block of `e₀` or an ancestor of it.

It is `LockTraced` with `v`'s own tick to `c` in place of `x.stepBefore c`: over the trace the
steps from `x.stepBefore c` to `v`'s tick come before the update, so `LockTraced`'s last clause
fails at them.

The variables:
- `M`: the model; `S`: the setup;
- `x`: the execution; `v`: the validator; `i`: the step; `e`: the lock entry.

Read aloud: `e` was added by `v`'s update of the slot its deadline names, at `v`'s own tick, and
has been traced since by entries between it and the added one. -/
def LockTracedAfterTick (S : Setup V) (x : Trace V (NamedObject V) M.N) (v : V)
    (i : ℕ) (e : M.LE) : Prop :=
  ∃ s : ℕ, e.d = S.C.t_ (s + S.C.k) + 5 * S.C.Δ ∧
    x.tickStep v (M.supportCutoff S.C (s + 1)) < i ∧
    x.lbl (x.tickStep v (M.supportCutoff S.C (s + 1))) = Event.tick v (M.supportCutoff S.C (s + 1)) ∧
    (∃ τ : Time, (x.tickInput v (M.supportCutoff S.C (s + 1))).awakeSince = some τ ∧
      τ ≤ duty_window_start S.C (s + 1)) ∧
    ∀ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (M.supportCutoff S.C (s + 1)))
        ((M.supportCutoff S.C (s + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput v (M.supportCutoff S.C (s + 1))) (s + 1) →
      ∃ e₀ ∈ M.lockEntries n', e₀.d = e.d ∧
        e₀.B ∈ (M.fg_to_ac (x.tickInput v (M.supportCutoff S.C (s + 1)))).tree ∧
        e₀.B ≠ Block.genesis ∧
        (∃ C' : Block V, M.savedConfirmation n' s = some C' ∧ e₀.B.AncestorEq C') ∧
        (e₀.B ∈ M.fastBlocks n' ∨
          M.slow_test S.C (x.tickInput v (M.supportCutoff S.C (s + 1))) s e₀.B = true) ∧
        e.B.AncestorEq e₀.B ∧
        ∀ i' : ℕ, x.tickStep v (M.supportCutoff S.C (s + 1)) < i' → i' ≤ i →
          ∃ e' ∈ (x.st i' v).lockEntries, e'.d = e.d ∧ e.B.AncestorEq e'.B ∧
            e'.B.AncestorEq e₀.B

/-- A traced entry at the step `i` (`LockTracedAfterTick`) traces, at the step `i + 1`, every entry
held then with its deadline on its block or an ancestor of it: the same update added it. It is the
copy of `lockTraced_succ` for `LockTracedAfterTick`.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `v`: the validator; `i`: the step; `e`: the entry at `i`; `e'`: the entry
  at `i + 1`.

Read aloud: a lock entry traced at step `i` traces every entry at step `i + 1` with its deadline on
its block or an ancestor of it. -/
theorem lockTracedAfterTick_succ {S : Setup V} {x : Trace V (NamedObject V) M.N}
    {v : V} {i : ℕ} {e e' : M.LE}
    -- `e` is traced at the step `i`
    (h : LockTracedAfterTick M S x v i e)
    -- `e'` has the deadline of `e`
    (hd : e'.d = e.d)
    -- the block of `e'` is the block of `e` or an ancestor of it
    (hB : e'.B.AncestorEq e.B)
    -- `v` holds `e'` at the step `i + 1`
    (he' : e' ∈ (x.st (i + 1) v).lockEntries) :
    LockTracedAfterTick M S x v (i + 1) e' := by
  obtain ⟨s, hdb, h1, hlab, h2, h3⟩ := h
  refine ⟨s, hd.trans hdb, by omega, hlab, h2, fun n' sent hrun hA => ?_⟩
  obtain ⟨e₀, he₀, hd₀, hT, hG, hC, hF, hB₀, h4⟩ := h3 n' sent hrun hA
  refine ⟨e₀, he₀, hd₀.trans hd.symm, hT, hG, hC, hF, ancestorEq_trans hB hB₀,
    fun i' hi₁ hi₂ => ?_⟩
  rcases Nat.lt_or_eq_of_le hi₂ with hlt | heq
  · obtain ⟨e'', he'', hd'', hB₁, hB₂⟩ := h4 i' hi₁ (by omega)
    exact ⟨e'', he'', hd''.trans hd.symm, ancestorEq_trans hB hB₁, hB₂⟩
  · rw [heq]
    exact ⟨e', he', rfl, ancestorEq_refl _, ancestorEq_trans hB hB₀⟩

/-- Every lock entry a validator holds at a step is traced there (`LockTracedAfterTick`): by
induction on the step, from the initial AC state, which holds no entry, through
`step_cases_lock_saved`. It is the copy of the deleted `lockTraced_of_mem` for `LockTracedAfterTick`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`: the setup, the activity, the execution; `R`: the run's facts; `E`: the
  environment's facts; `v`: the validator; `i`: the step.

Read aloud: every lock entry a validator holds at a step was added at its own tick and traced
since. -/
theorem lockTracedAfterTick_of_mem (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
        {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)

    (v : V) (i : ℕ) : ∀ e ∈ (x.st i v).lockEntries, LockTracedAfterTick M S x v i e := by
  induction i with
  | zero =>
      intro e he
      rw [(getElem_zero_st M F) x R, F.init.initial_lockEntries] at he
      exact absurd he (Finset.notMem_empty e)
  | succ i ih =>
      intro e he
      rcases (step_cases_lock_saved M F) x R E i v with ⟨-, hsub⟩ | ⟨t, hl, -, -, -, hLR, -⟩ |
          ⟨t, hl, hvA, ht, hAw, hCU⟩
      · -- the step keeps a subset of the entries
        exact lockTracedAfterTick_succ M F (ih e (hsub he)) rfl (ancestorEq_refl _) he
      · -- the revocation moves live entries to ancestors, from the node state the tick starts
        -- from, `v`'s at the step `i`
        have hti : x.tickInput v t = x.st i v := by
          unfold Trace.tickInput
          rw [(tickStep_eq_of_lbl M) x E hl]
        rw [hti] at hLR
        by_cases hs0 : S.C.slot (t : Int) = 0
        · rw [hs0] at hLR
          have he₁ := ((GoldilocksCorrectness.Record.Proofs.Routines.revoke_locks_zero hLR) e).1 he
          exact lockTracedAfterTick_succ M F (ih e he₁.1) rfl (ancestorEq_refl _) he
        · obtain ⟨e₁, he₁, -, hd, hB, -⟩ :=
            GoldilocksCorrectness.Record.Statements.Routines.lem38_revoke_locks_entries_moved
              (Nat.one_le_iff_ne_zero.mpr hs0) hLR e he
          exact lockTracedAfterTick_succ M F (ih e₁ he₁) hd hB he
      · -- the confirmation update keeps every unexpired entry and adds at most one
        have hti : x.tickInput v t = x.st i v := by
          unfold Trace.tickInput
          rw [(tickStep_eq_of_lbl M) x E hl]
        rcases GoldilocksCorrectness.Record.Proofs.Routines.confirmationUpdated_entries_cases hCU e he
          with ⟨hold, -⟩ | ⟨hs1, hnew⟩
        · exact lockTracedAfterTick_succ M F (ih e (hti ▸ hold)) rfl (ancestorEq_refl _) he
        -- a new entry: the update is the one of slot `s + 1`, `s` the slot before `t`'s, run at
        -- `v`'s tick `i` from `v`'s node state before `t` (it has a wake time, so no wake ran)
        obtain ⟨s, hb⟩ : ∃ s : ℕ, S.C.slot (t : Int) = s + 1 :=
          ⟨S.C.slot (t : Int) - 1, by
            -- `omega` reads facts stated at `Slot`, an `abbrev` of `ℕ`, only once restated at `ℕ`
            have h1 : @LE.le ℕ _ 1 (S.C.slot (t : Int)) := hs1
            show @Eq ℕ (S.C.slot (t : Int)) (S.C.slot (t : Int) - 1 + 1)
            omega⟩
        have htc := (eq_supportCutoff_of_cast M F U) S ht hb
        subst htc
        have hts : x.tickStep v (M.supportCutoff S.C (s + 1)) = i := (tickStep_eq_of_lbl M) x E hl
        have hΔ := one_le_Δ S
        have hc1 : 1 ≤ M.supportCutoff S.C (s + 1) := by
          rw [(GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U)]
          omega
        rw [hb] at hAw hCU hnew
        obtain ⟨τ, hτs, hτle⟩ := hAw
        have hd : e.d = S.C.t_ (s + S.C.k) + 5 * S.C.Δ := by
          obtain ⟨-, -, -, -, hd⟩ := hnew
          simp only [Nat.add_sub_cancel] at hd
          exact hd
        refine ⟨s, hd, by omega, by rw [hts]; exact hl, ⟨τ, hτs, hτle⟩, fun n' sent hrun hA => ?_⟩
        -- every outcome of that tick, from that state awake for the slot, is what the update of
        -- slot `s + 1` leaves from it, and holds the entry on the deepest lockable block
        have hCU' := F.tk2.tick_supportCutoff_confirmation S.C S.P S.X _ _ n' sent hrun
          (by rw [hti]; exact ((lem11_node_invariant M F S A x R E i v)
            (Activity.not_mem_corrupted_of_mem_active hvA)).1) ht
          (by rw [hb]; exact hA)
        rw [hb] at hCU'
        obtain ⟨e₀, he₀, hd₀, hBe, hT, hG, hC, hF⟩ :=
          confirmationUpdated_new_entry M F (Nat.le_add_left 1 s) hCU hCU' hnew
        simp only [Nat.add_sub_cancel] at hC hF
        refine ⟨e₀, he₀, hd₀, hT, hG, hC, hF, hBe, fun i' hi₁ hi₂ => ?_⟩
        have : i' = i + 1 := by omega
        rw [this]
        exact ⟨e, he, rfl, ancestorEq_refl _, hBe⟩

/-- **Lemma 39, where a lock entry comes from.** The proof; the audited statement is in
`Statements/Executions/LockProvenanceStatements.lean`. Write `c` for the support cutoff of slot
`s + 1` and `X` for `v`'s node state before `c`: every lock entry `e` of `v`'s node state before
`t` has the deadline of a lock of some slot `s`, `c` is before `t`, `v`'s tick at `c` starts from a
state awake since the duty window's start of slot `s + 1`, and every outcome `(n', sent)` of the
tick at `c` from `X`, when `X` is awake for slot `s + 1`, holds an entry `e₀` with the deadline of
`e`, on a non-genesis block of the tree of `M.fg_to_ac X` on the chain of the confirmation `n'`
saves for slot `s`, a fast block of `n'` or passing the slow test (`M.slow_test` on `X`); and at
every time `t'` after `c` up to `t`, `v`'s node state before `t'` holds an entry with the deadline
of `e` whose block is the block of `e` or a descendant of it, and the block of `e₀` or an ancestor
of it.

The landed statement names the answer of the confirmation update; the twin states every outcome of
the tick under the wake condition, and reads the lock entry as the
record's `M.LE`. Its recovery is exact: at the spec's model the tick at `c` has an outcome, which
holds the update's answer.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `i`: the step; `v`: the validator;
- `e`: the lock entry.

Read aloud: every lock entry `v` holds at the step `i` was added by `v`'s update of the slot its
deadline names, at its own tick at a step before `i`, and has been traced since by entries between it
and the added one. -/
theorem lem39_lock_entry_provenance (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (i : ℕ) (v : V) (e : M.LE)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (he : e ∈ (x.st i v).lockEntries) :
    ∃ s : ℕ, e.d = S.C.t_ (s + S.C.k) + 5 * S.C.Δ ∧
      x.tickStep v (M.supportCutoff S.C (s + 1)) < i ∧
      x.lbl (x.tickStep v (M.supportCutoff S.C (s + 1))) = Event.tick v (M.supportCutoff S.C (s + 1)) ∧
      (∃ τ : Time, (x.tickInput v (M.supportCutoff S.C (s + 1))).awakeSince = some τ ∧ τ ≤ duty_window_start S.C (s + 1)) ∧
      ∀ (n' : M.N) (sent : List (NamedObject V)),
        .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (M.supportCutoff S.C (s + 1)))
          ((M.supportCutoff S.C (s + 1) : ℕ) : Int) →
        AwakeFor M S.C (x.tickInput v (M.supportCutoff S.C (s + 1))) (s + 1) →
        ∃ e₀ ∈ M.lockEntries n', e₀.d = e.d ∧
          e₀.B ∈ (M.fg_to_ac (x.tickInput v (M.supportCutoff S.C (s + 1)))).tree ∧
          e₀.B ≠ Block.genesis ∧
          (∃ C' : Block V, M.savedConfirmation n' s = some C' ∧ e₀.B.AncestorEq C') ∧
          (e₀.B ∈ M.fastBlocks n' ∨
            M.slow_test S.C (x.tickInput v (M.supportCutoff S.C (s + 1))) s e₀.B = true) ∧
          e.B.AncestorEq e₀.B ∧
          ∀ i' : ℕ, x.tickStep v (M.supportCutoff S.C (s + 1)) < i' → i' ≤ i →
            ∃ e' ∈ (x.st i' v).lockEntries, e'.d = e.d ∧ e.B.AncestorEq e'.B ∧
              e'.B.AncestorEq e₀.B := by
  exact (lockTracedAfterTick_of_mem M F U) S A x R E v i e he

/-- A validator holding a lock entry whose deadline is that of a lock of slot `s` is active at the
support cutoff of slot `s + 1`: the entry was added at `v`'s own tick to that cutoff
(`lockTracedAfterTick_of_mem`), and a tick is by a validator active at its time
(`E.tick_active`). The deadline names the slot, since `S.C.t_` grows with the slot.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`: the setup, the activity, the execution; `R`: the run's facts; `E`: the
  environment's facts; `t`: the time; `v`: the validator;
  `e`: the lock entry; `s`: the slot its deadline names.

Read aloud: if `e` is a lock entry of `v`'s node state before `t` with the deadline
`S.C.t_ (s + S.C.k) + 5 · S.C.Δ`, then `v` is active at the support cutoff of slot `s + 1`. -/
theorem active_of_lock_entry (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (t : ℕ) (v : V) (e : M.LE)
        {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)

    (he : e ∈ (x.stateBefore t v).lockEntries) (s : ℕ)
    (hd : e.d = S.C.t_ (s + S.C.k) + 5 * S.C.Δ) :
    v ∈ A.active (x.tickStep v (M.supportCutoff S.C (s + 1))) := by
  obtain ⟨s₀, hd₀, -, hlab, -⟩ :=
    (lockTracedAfterTick_of_mem M F U) S A x R E v (x.stepBefore t) e he
  have h1 : S.C.t_ (s + S.C.k) = S.C.t_ (s₀ + S.C.k) := add_right_cancel (hd.symm.trans hd₀)
  have hs : s = s₀ := by
    rcases lt_trichotomy s s₀ with h | h | h
    · have := GoldilocksCorrectness.Proofs.Routines.t_lt_of_lt S (show s + S.C.k < s₀ + S.C.k by omega)
      rw [h1] at this
      exact absurd this (lt_irrefl _)
    · exact h
    · have := GoldilocksCorrectness.Proofs.Routines.t_lt_of_lt S (show s₀ + S.C.k < s + S.C.k by omega)
      rw [h1] at this
      exact absurd this (lt_irrefl _)
  subst hs
  exact (E.tick_active _ _ _ hlab).1

end GoldilocksCorrectness.Record.Proofs.Executions

