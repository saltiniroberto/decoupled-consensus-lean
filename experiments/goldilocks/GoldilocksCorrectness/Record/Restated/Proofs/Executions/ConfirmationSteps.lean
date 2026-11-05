module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.BlockPropagation
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.TickFrameDefs
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.TickFrameACStore
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Schedule

@[expose] public section

/-!
# ConfirmationSteps, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/ConfirmationSteps.lean`, over a model `M`
whose facts `F` hold, for an execution `x` of `protocolOf M S`, in steps and labels only: between
two steps with no tick of a validator its locks and confirmations do not change; between two steps
whose ticks of it are all away from the vote time and the support cutoff of their slot its lock
entries only shrink (the field `tick_lock_entries` of `F.tk`, `receive_keeps_confirmation` of
`F.rcv`); two ticks of a validator come in the order of their clock values; and the corollaries from a
validator's tick output at one clock value to its tick input at a later one. The page's routine-level
theorems are the facts' fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

namespace GoldilocksCorrectness.Record.Proofs.Executions

open GoldilocksCorrectness.Record.Proofs.Routines (KeepsConfirmation)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Proofs.Routines (tick_lock_entries_subset receive_keeps_confirmation)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

variable {S : Setup V} {A : Activity V}

/-- Between two steps `j ≤ k` with no tick of `v` at a step from `j` to before `k`, `v` keeps its lock
entries, saved confirmations, fast blocks and confirmed tip: a delivery keeps the four fields
(`receive_keeps_confirmation`), a restart keeps them (`F.wk.wake_readers`), and another validator's step
leaves `v`'s state (`R.untouched`). Steps and labels only: no real time, no clock bound, no honesty.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `R`: the run's facts; `v`: the validator; `j`, `k`: the two steps.

Read aloud: between two steps with no tick of `v`, `v`'s locks and confirmations do not change. -/
theorem keepsConfirmation_of_no_tick_between
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (v : V) {j k : ℕ} (hjk : j ≤ k)
    -- no step from `j` to before `k` is a tick of `v`
    (hNoTick : ∀ i, j ≤ i → i < k → ∀ t', x.lbl i ≠ Event.tick v t') :
    KeepsConfirmation M (x.st j v) (x.st k v) := by
  refine GoldilocksCorrectness.Proofs.Executions.rel_of_forall_step (fun n n' => KeepsConfirmation M n n')
    (fun n => (GoldilocksCorrectness.Record.Proofs.Routines.KeepsConfirmation.refl M F) n)
    (fun _ _ _ h h' => (GoldilocksCorrectness.Record.Proofs.Routines.KeepsConfirmation.trans M F) h h')
    (fun i => x.st i v) hjk (fun i h1 h2 => ?_)
  show KeepsConfirmation M (x.st i v) (x.st (i + 1) v)
  rcases hl : x.lbl i with ⟨w, t⟩ | ⟨w, t, keep⟩ | ⟨w, sm⟩ | _
  · by_cases hw : v = w
    · subst hw; exact absurd hl (hNoTick i h1 h2 t)
    · rw [R.untouched i v (fun t' h => hw (by rw [hl] at h; cases h; rfl))
        (fun t' keep h => by rw [hl] at h; cases h) (fun sm h => by rw [hl] at h; cases h)]
      exact (GoldilocksCorrectness.Record.Proofs.Routines.KeepsConfirmation.refl M F) _
  · by_cases hw : v = w
    · subst hw
      rw [(R.restart i v t keep hl).1]
      obtain ⟨-, -, -, -, -, -, -, -, -, -, hsv, hle, hfb, hlc, -, -, -, -⟩ :=
        F.wk.wake_readers (x.st i v) (t : Int)
      exact ⟨hle, hsv, hfb, hlc⟩
    · rw [R.untouched i v (fun t' h => by rw [hl] at h; cases h)
        (fun t' keep' h => hw (by rw [hl] at h; cases h; rfl)) (fun sm h => by rw [hl] at h; cases h)]
      exact (GoldilocksCorrectness.Record.Proofs.Routines.KeepsConfirmation.refl M F) _
  · by_cases hw : v = w
    · subst hw
      rw [(R.deliver i v sm hl).2.1]
      have h := F.rcv.receive_keeps_confirmation S.C S.P S.X (x.st i v) sm.msg
      exact ⟨h.2.2.1, h.1, h.2.1, h.2.2.2.1⟩
    · rw [R.untouched i v (fun t' h => by rw [hl] at h; cases h)
        (fun t' keep h => by rw [hl] at h; cases h) (fun sm' h => hw (by rw [hl] at h; cases h; rfl))]
      exact (GoldilocksCorrectness.Record.Proofs.Routines.KeepsConfirmation.refl M F) _
  · rw [R.untouched i v (fun t' h => by rw [hl] at h; cases h)
      (fun t' keep h => by rw [hl] at h; cases h) (fun sm h => by rw [hl] at h; cases h)]
    exact (GoldilocksCorrectness.Record.Proofs.Routines.KeepsConfirmation.refl M F) _

/-- Between two steps `j ≤ k` whose ticks of `v` are all to clock values that are neither the vote
time nor the support cutoff of their slot, `v`'s lock entries only shrink: such a tick keeps exactly
the entries with deadline after its clock value (`F.tk.tick_lock_entries`), a delivery keeps them
(`receive_keeps_confirmation`), a restart keeps them (`F.wk.wake_readers`), another validator's step
leaves `v`'s state. Steps and labels only.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `R`: the run's facts; `v`: the validator; `j`, `k`: the two steps.

Read aloud: between two steps whose ticks of `v` are all away from the vote time and the support
cutoff of their slot, `v`'s lock entries only shrink. -/
theorem lockEntries_subset_of_ticks_off_duty_between
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (v : V) {j k : ℕ} (hjk : j ≤ k)
    -- every tick of `v` from `j` to before `k` is to a value that is neither the vote time nor the
    -- support cutoff of its slot
    (hOff : ∀ i, j ≤ i → i < k → ∀ t', x.lbl i = Event.tick v t' →
      (t' : Int) ≠ S.C.t_ (S.C.slot t') + S.C.Δ ∧ (t' : Int) ≠ S.C.t_ (S.C.slot t') + 2 * S.C.Δ) :
    (x.st k v).lockEntries ⊆ (x.st j v).lockEntries := by
  refine GoldilocksCorrectness.Proofs.Executions.rel_of_forall_step
    (fun n n' : M.N => n'.lockEntries ⊆ n.lockEntries)
    (fun n => le_rfl) (fun _ _ _ h h' => le_trans h' h)
    (fun i => x.st i v) hjk (fun i h1 h2 => ?_)
  show (x.st (i + 1) v).lockEntries ⊆ (x.st i v).lockEntries
  rcases hl : x.lbl i with ⟨w, t⟩ | ⟨w, t, keep⟩ | ⟨w, sm⟩ | _
  · by_cases hw : v = w
    · subst hw
      obtain ⟨n', sent, hrun, hst, -⟩ := R.tick i v t hl
      rw [hst]
      rcases F.tk.tick_lock_entries S.C S.P S.X (x.st i v) (t : Int) n' sent hrun with h | h | h
      · rw [h]; exact Finset.filter_subset _ _
      · exact absurd h (hOff i h1 h2 t hl).1
      · exact absurd h (hOff i h1 h2 t hl).2
    · rw [R.untouched i v (fun t' h => hw (by rw [hl] at h; cases h; rfl))
        (fun t' keep h => by rw [hl] at h; cases h) (fun sm h => by rw [hl] at h; cases h)]
  · by_cases hw : v = w
    · subst hw
      rw [(R.restart i v t keep hl).1]
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hle, -, -, -, -, -, -⟩ :=
        F.wk.wake_readers (x.st i v) (t : Int)
      show M.lockEntries (M.wake (x.st i v) (t : Int)) ⊆ M.lockEntries (x.st i v)
      rw [hle]
    · rw [R.untouched i v (fun t' h => by rw [hl] at h; cases h)
        (fun t' keep' h => hw (by rw [hl] at h; cases h; rfl)) (fun sm h => by rw [hl] at h; cases h)]
  · by_cases hw : v = w
    · subst hw
      rw [(R.deliver i v sm hl).2.1]
      show M.lockEntries (M.receive S.C S.P S.X (x.st i v) sm.msg) ⊆ M.lockEntries (x.st i v)
      rw [(F.rcv.receive_keeps_confirmation S.C S.P S.X (x.st i v) sm.msg).2.2.1]
    · rw [R.untouched i v (fun t' h => by rw [hl] at h; cases h)
        (fun t' keep h => by rw [hl] at h; cases h) (fun sm' h => hw (by rw [hl] at h; cases h; rfl))]
  · rw [R.untouched i v (fun t' h => by rw [hl] at h; cases h)
      (fun t' keep h => by rw [hl] at h; cases h) (fun sm h => by rw [hl] at h; cases h)]

/-- Two ticks of `v`, to clock values `t₁ < t₂`, come in that order, and every tick of `v` at a step
strictly between them is to a value strictly between `t₁` and `t₂`. A tick is by a validator outside the
adversary set at its step (`E.not_mem_corrupted_of_tick`), so `E.clock_mono` orders every pair of `v`'s
ticks; `E.tick_unique` excludes a second tick to `t₁` or `t₂`. No honesty hypothesis.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `E`: the environment's facts; `v`: the validator; `t₁`, `t₂`: the two clock
  values; `k`, `k'`: the steps of `v`'s ticks to them.

Read aloud: `v`'s tick to the smaller value comes first, and every tick of `v` between the two is to a
value between the two. -/
theorem ticks_between
    (x : Trace V (NamedObject V) M.N)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (v : V) {t₁ t₂ k k' : ℕ} (hlt : t₁ < t₂)
    (hk : x.lbl k = Event.tick v t₁) (hk' : x.lbl k' = Event.tick v t₂) :
    k < k' ∧ ∀ i, k < i → i < k' → ∀ t'', x.lbl i = Event.tick v t'' → t₁ < t'' ∧ t'' < t₂ := by
  have hkk' : k < k' := by
    rcases lt_or_ge k k' with h | h
    · exact h
    · exfalso
      rcases eq_or_lt_of_le h with h | h
      · subst h; rw [hk] at hk'; cases hk'; omega
      · have := E.clock_mono k' k v t₂ t₁ h (E.not_mem_corrupted_of_tick hk) (Or.inl hk') (Or.inl hk)
        omega
  refine ⟨hkk', fun i h1 h2 t'' hi => ?_⟩
  have ha := E.clock_mono k i v t₁ t'' h1 (E.not_mem_corrupted_of_tick hi) (Or.inl hk) (Or.inl hi)
  have hb := E.clock_mono i k' v t'' t₂ h2 (E.not_mem_corrupted_of_tick hk') (Or.inl hi) (Or.inl hk')
  refine ⟨lt_of_le_of_ne ha fun h => ?_, lt_of_le_of_ne hb fun h => ?_⟩
  · subst h; exact absurd (E.tick_unique _ _ v t₁ hi hk) (by omega)
  · subst h; exact absurd (E.tick_unique _ _ v t'' hi hk') (by omega)

/-- What `v`'s tick to `t` leaves of its lock entries, saved confirmations, fast blocks and confirmed
tip is what its tick to `t + 1` starts from: no tick of `v` comes between the two (`ticks_between`), so
`keepsConfirmation_of_no_tick_between` applies. No real time, no clock bound, no honesty hypothesis.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `v`: the validator;
  `t`: the clock value; `k`, `k'`: the steps of `v`'s ticks to `t` and `t + 1`.

Read aloud: what `v`'s tick to `t` leaves of its locks and confirmations is what its tick to the next
value reads. -/
theorem keepsConfirmation_tickOutput_tickInput_succ
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (v : V) {t k k' : ℕ} (hk : x.lbl k = Event.tick v t) (hk' : x.lbl k' = Event.tick v (t + 1)) :
    KeepsConfirmation M (x.tickOutput v t) (x.tickInput v (t + 1)) := by
  obtain ⟨hkk', hbet⟩ := ticks_between M F x E v (Nat.lt_succ_self t) hk hk'
  unfold Trace.tickOutput Trace.tickInput
  rw [(tickStep_eq_of_lbl M) x E hk, (tickStep_eq_of_lbl M) x E hk']
  exact keepsConfirmation_of_no_tick_between M F x R v hkk' (fun i h1 h2 t'' hi => by
    have := hbet i (by omega) h2 t'' hi; omega)

/-- From `v`'s tick output at `t₁` to its tick input at `t₂ > t₁`, `v`'s lock entries only shrink, when
no clock value strictly between `t₁` and `t₂` is the vote time or the support cutoff of its slot: every
tick of `v` between the two steps is to such a value (`ticks_between`), so
`lockEntries_subset_of_ticks_off_duty_between` applies. No real time, no clock bound, no honesty
hypothesis.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `v`: the validator;
  `t₁`, `t₂`: the two clock values; `k`, `k'`: the steps of `v`'s ticks to them.

Read aloud: between two of `v`'s ticks with no vote time and no support cutoff between their clock
values, `v`'s lock entries only shrink. -/
theorem lockEntries_tickInput_subset_tickOutput
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (v : V) {t₁ t₂ k k' : ℕ} (hlt : t₁ < t₂)
    (hk : x.lbl k = Event.tick v t₁) (hk' : x.lbl k' = Event.tick v t₂)
    -- no clock value strictly between the two is the vote time or the support cutoff of its slot
    (hNoDuty : ∀ t'' : ℕ, t₁ < t'' → t'' < t₂ →
      (t'' : Int) ≠ S.C.t_ (S.C.slot t'') + S.C.Δ ∧ (t'' : Int) ≠ S.C.t_ (S.C.slot t'') + 2 * S.C.Δ) :
    (x.tickInput v t₂).lockEntries ⊆ (x.tickOutput v t₁).lockEntries := by
  obtain ⟨hkk', hbet⟩ := ticks_between M F x E v hlt hk hk'
  unfold Trace.tickOutput Trace.tickInput
  rw [(tickStep_eq_of_lbl M) x E hk, (tickStep_eq_of_lbl M) x E hk']
  exact lockEntries_subset_of_ticks_off_duty_between M F x R v hkk' (fun i h1 h2 t'' hi => by
    obtain ⟨ha, hb⟩ := hbet i (by omega) h2 t'' hi; exact hNoDuty t'' ha hb)

end GoldilocksCorrectness.Record.Proofs.Executions

