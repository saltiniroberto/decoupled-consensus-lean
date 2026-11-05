module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma39
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma40
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma41

@[expose] public section

/-!
# LockProvenanceStatements, over a model

The statements of `GoldilocksCorrectness/Statements/Executions/LockProvenanceStatements.lean`, over
a model `M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: Lemma 39, where a lock
entry comes from; Lemma 40, where a saved confirmation comes from; Lemma 41, the slot of a live lock
entry. The update's clause of Lemmas 39 and 40 states every outcome of the tick at the support
cutoff under the wake condition (template A3). Each is the theorem of its page under
`Record/Restated/Proofs/Executions/`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (voteTime supportCutoff)

namespace GoldilocksCorrectness.Record.Statements.Executions

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Statements.Routines (expireLocks)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- **Lemma 39, where a lock entry comes from.** In an execution that reaches every time, every
lock entry `e` of `v`'s node state after the step `i` was added by `v`'s confirmation update of the
slot `s` its deadline names, at `v`'s own tick to the support cutoff `c` of slot `s + 1`. Write `X`
for the node state that tick starts from (`x.tickInput v c`). The deadline of `e` is
`S.C.t_ (s + S.C.k) + 5 · S.C.Δ`; the step `x.tickStep v c` is before `i` and is `v`'s tick to `c`;
`X`'s `awakeSince` is some time at most the duty window's start of slot `s + 1`, so the duty test
passed; every outcome `(n', sent)` of the tick at `c` from `X`, when `X` is awake for slot `s + 1`,
holds an entry `e₀` with the deadline of `e`, on a block of the tree of `M.fg_to_ac X` other than
the genesis block that is the confirmation `n'` saves for slot `s` or an ancestor of it, a fast
block of `n'` or passing the slow test (`M.slow_test` on `X`), with `e`'s block `e₀`'s block or an
ancestor of it; and at every step after `x.tickStep v c` up to `i`, `v` holds an entry with the
deadline of `e` whose block is `e`'s block or a descendant of it, and `e₀`'s block or an ancestor
of it. Stated at a step, every clause at `v`'s tick: the support cutoff is a clock
value, and `v`'s tick to it runs at a real time within the two clock bounds of it.

Why: the lock entries are empty initially; a step keeps a subset of them, or, at the vote time,
the revocation moves live entries to ancestors keeping their deadlines (Lemma 38), or, at the
support cutoff with the duty test passing, the confirmation update deletes none and adds at most
one entry, with the slot's deadline and the block facts of Lemma 35. Each entry is traced along
the steps by an invariant proved by induction on the step; the entry one outcome of the tick adds
has a counterpart in every other.

The landed statement names the answer of the confirmation update; the twin states every outcome of
the tick under the wake condition, and reads the lock entry as the
record's `M.LE`. Each is the theorem of `Record/Restated/Proofs/Executions/Lemma39.lean`. Its
recovery is exact: at the spec's model the tick at `c` has an outcome, which holds the update's
answer.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `i`: the step; `v`: the validator;
- `e`: the lock entry; `s`: the slot of the lock; `n'`, `sent`: an outcome of the tick at `c`;
  `e₀`: the entry it added; `C'`: the confirmation it saves for slot `s`.

Read aloud: a lock entry `e` of `v`'s state at step `i` has a slot `s` with `e`'s deadline that of a
lock of slot `s`; the step `x.tickStep v c` (`c` the support cutoff of slot `s + 1`) is before `i` and
is `v`'s tick to `c`; its starting state's `awakeSince` is at most the duty window's start of slot
`s + 1`; and every outcome of that tick, when its starting state is awake for slot `s + 1`, holds an
entry `e₀` with `e`'s deadline (block in the starting state's tree, not genesis, the saved
confirmation of slot `s` or an ancestor of it, fast or passing the slow test), `e`'s block is `e₀`'s
block or an ancestor of it, and at every step after the tick's step up to `i` `v` holds an entry with
`e`'s deadline whose block is `e`'s block or a descendant of it and `e₀`'s block or an ancestor of it. -/
theorem lem39_lock_entry_provenance (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (i : ℕ) (v : V) (e : M.LE)
    -- the execution reaches every time
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    -- `e` is a lock entry of `v`'s node state after the step `i`
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
              e'.B.AncestorEq e₀.B :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem39_lock_entry_provenance M F U) S A x R i v e E he

/-- **Lemma 40, where a saved confirmation comes from.** In an execution that reaches every
time, a block `C'` saved as the confirmation of slot `s'` on `v`'s node state after the step `i` was
saved by `v`'s confirmation update of slot `s' + 1`, at `v`'s own tick to the support cutoff `c` of
slot `s' + 1`. Write `X` for the node state that tick starts from (`x.tickInput v c`). Then the step
`x.tickStep v c` is before `i` and is `v`'s tick to `c`; `X`'s `awakeSince` is some time at most the
duty window's start of slot `s' + 1`, so the duty test passed; every outcome `(n', sent)` of the tick
at `c` from `X`, when `X` is awake for slot `s' + 1`, saves `C'` as the confirmation of slot `s'`; and
at every step after `x.tickStep v c` up to `i`, `v`'s node state has `C'` saved as the confirmation of
slot `s'`. Stated at a step, every clause at `v`'s tick.

Why: the saved confirmation of slot `s'` is `none` initially, and the only step that changes it is
`v`'s tick at `c`, running the update of slot `s' + 1` with the duty test passing: a tick writes it
only through the update of the slot of its time, which writes the saved confirmation of the slot
before only; every time has one tick, and every outcome of the update from one state saves the
same confirmation.

The landed statement names the answer of the confirmation update; the twin states every outcome of
the tick under the wake condition. It is the theorem of
`Record/Restated/Proofs/Executions/Lemma40.lean`. Its recovery is exact: at the spec's model the
tick at `c` has an outcome, which holds the update's answer.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `i`: the step; `v`: the validator;
- `s'`: the slot of the confirmation; `C'`: the block saved; `n'`, `sent`: an outcome of the tick
  at `c`.

Read aloud: a saved confirmation of slot `s'` on `v`'s state at step `i` was saved by `v`'s update of
slot `s' + 1`, at `v`'s own tick to the support cutoff of slot `s' + 1`, a step before `i`, with the
duty test passing: every outcome of that tick, when its starting state is awake for the slot, saves
it; and the field keeps that value at every step from the tick's step to `i`. -/
theorem lem40_saved_confirmation_provenance (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (i : ℕ) (v : V) (s' : ℕ) (C' : Block V)
    -- the execution reaches every time
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    -- `v`'s node state after the step `i` has `C'` saved as the confirmation of slot `s'`
    (hSaved : (x.st i v).savedConfirmation s' = some C') :
    x.tickStep v (M.supportCutoff S.C (s' + 1)) < i ∧
      x.lbl (x.tickStep v (M.supportCutoff S.C (s' + 1))) = Event.tick v (M.supportCutoff S.C (s' + 1)) ∧
      (∃ τ : Time, (x.tickInput v (M.supportCutoff S.C (s' + 1))).awakeSince = some τ ∧ τ ≤ duty_window_start S.C (s' + 1)) ∧
      (∀ (n' : M.N) (sent : List (NamedObject V)),
        .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (M.supportCutoff S.C (s' + 1)))
          ((M.supportCutoff S.C (s' + 1) : ℕ) : Int) →
        AwakeFor M S.C (x.tickInput v (M.supportCutoff S.C (s' + 1))) (s' + 1) →
        M.savedConfirmation n' s' = some C') ∧
      ∀ i' : ℕ, x.tickStep v (M.supportCutoff S.C (s' + 1)) < i' → i' ≤ i →
        (x.st i' v).savedConfirmation s' = some C' :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem40_saved_confirmation_provenance M F U) S A x R i v s' C'
    E hSaved

omit [RootOrder] in
/-- **Lemma 41, the slot of a live lock entry.** A lock entry `e` with the deadline of a lock of
slot `s`, `S.C.t_ (s + S.C.k) + 5 · S.C.Δ`, whose deadline is after a time `t` that is at or after
the vote time of slot `s₀ + S.C.k`, is a lock of a slot `s` at least `s₀`.

Why: the vote time of slot `s₀ + S.C.k` is `4 · S.C.Δ · (s₀ + S.C.k) + S.C.Δ` and the deadline is
`4 · S.C.Δ · (s + S.C.k) + 5 · S.C.Δ`; a time at or after the first and strictly before the second
gives `s₀ + S.C.k < s + S.C.k + 1`, since `S.C.Δ` is positive.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `s₀`: the slot whose vote time `S.C.k` slots later bounds `t`; `s`: the slot of
  the lock; `t`: the time; `e`: the lock entry.

Read aloud: an entry with the deadline of a slot-`s` lock, whose deadline is after a time `t` at or
after the vote time of slot `s₀ + C.k`, is of a slot `s ≥ s₀`. -/
theorem lem41_slot_of_live_entry (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (s₀ s t : ℕ) (e : M.LE)
    -- `e` has the deadline of a lock of slot `s`
    (hd : e.d = S.C.t_ (s + S.C.k) + 5 * S.C.Δ)
    -- the deadline of `e` is after `t`
    (hlive : (t : Int) < e.d)
    -- `t` is at or after the vote time of slot `s₀ + S.C.k`
    (ht : M.voteTime S.C (s₀ + S.C.k) ≤ t) :
    s₀ ≤ s :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem41_slot_of_live_entry M F U) S s₀ s t e hd hlive ht

end GoldilocksCorrectness.Record.Statements.Executions

