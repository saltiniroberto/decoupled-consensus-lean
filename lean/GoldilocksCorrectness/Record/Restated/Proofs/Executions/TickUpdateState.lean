module
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.TickStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.ConfirmationSteps
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma39
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma40
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma41
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Proofs.Executions.TickUpdateState

@[expose] public section

/-!
# TickUpdateState, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/TickUpdateState.lean`, over a model `M`
whose facts `F` hold, for an execution `x` of `protocolOf M S`: the state the confirmation update
runs on at a duty, and at the update that added a lock entry. The page's routine-level theorems are
the facts' fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (supportCutoff)
open GoldilocksCorrectness.Proofs.Routines (lockDeadline_injective supportCutoff_cast
  supportCutoff_slot)

namespace GoldilocksCorrectness.Record.Proofs.Executions

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor)

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
open GoldilocksCorrectness.Proofs.Routines (voteTime_ne_cutoff)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- The deleted `cutoff_tick_outcome` (false over the trace) with the hypothesis that `v` is active at the support cutoff `c` of slot
`s + 1` added: over the trace a validator not active at `c` has no tick to `c`, and the node state
`x.tickInput v c` is then its initial state, whose `awakeSince` is present and early, while `v`'s
state before `c` need not be awake for slot `s + 1`. When `v` is active at `c` and the node state
its tick at `c` starts from has a wake time `τ` at most the duty window's start of slot `s + 1`, the
tick at `c` from `v`'s state before `c` has an outcome, and that state is awake for slot `s + 1`:
the state satisfies the model's node invariant and has a clock at most `c`
(`cutoff_state_facts_of_active`), so the tick there answers (the field `tick_ok` of `F.nd`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `hWS`: the trace is
  wake-shaped; `s`: the slot before the cutoff's; `v`: the validator; `τ`: the wake time.

Read aloud: a validator active at the support cutoff of slot `s + 1`, awake for the duty there, has
an outcome of its tick there, from its state before the cutoff. -/
theorem cutoff_tick_outcome_of_active (U : UniformSchedule M.toSlotLayout) {S : Setup V}
    {A : Activity V} (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
 (s : ℕ) (v : V) (τ : Time)
    -- `v` is active at the support cutoff of slot `s + 1`
    (hv : v ∈ A.activeAtTime x (M.supportCutoff S.C (s + 1)))
    -- the tick at the support cutoff starts from a node state awake since `τ`
    (hτ : (x.tickInput v (M.supportCutoff S.C (s + 1))).awakeSince = some τ)
    -- `τ` is at most the duty window's start of slot `s + 1`
    (hτle : τ ≤ duty_window_start S.C (s + 1)) :
    ∃ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (M.supportCutoff S.C (s + 1)))
        ((M.supportCutoff S.C (s + 1) : ℕ) : Int) ∧
      AwakeFor M S.C (x.tickInput v (M.supportCutoff S.C (s + 1))) (s + 1) := by
  obtain ⟨hA, hInv, hclk, -, -⟩ := (cutoff_state_facts_of_active M F U) x R E s v τ hv hτ hτle
  obtain ⟨⟨r, hr⟩, hne⟩ := F.nd.tick_ok S.C S.P S.X _ _ hInv hclk
  cases r with
  | error err => exact absurd hr (hne err)
  | ok p => exact ⟨p.1, p.2, hr, hA⟩

/-- The tick-to-update link, per tick. Write `c` for the support cutoff of slot `s + 1` and `X` for
`v`'s node state before `c`. When `v` ticks to `c` at the step `i` from a node state awake since the
duty window's start of slot `s + 1` or earlier, the tick at `c` from `X` has an outcome
`(n'', sent)`, `X` is awake for slot `s + 1`, and `v`'s state before `c + 1` has the saved
confirmation, fast blocks, lock entries and latest confirmation of `n''`.

Why: the tick reads `X`, since no restart of `v` comes between the step before `c` and the tick
(`no_restart_of_tickInput_awakeSince_some`, `tickInput_eq_stateBefore_of_tick`); the tick step's
outcome is an outcome of the tick from that state (`R.tick`); the steps after the tick, up to the
time `c`, keep the four fields (`keepsConfirmation_of_no_tick_between`). No activity at a
time is read: only the tick.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`, `R`, `E`, `hWS`: the setup, the activity, the execution, its run facts, its
  environment facts, its wake shape; `s`: the slot before the cutoff's slot; `v`: the validator;
  `i`: the step of `v`'s tick to the cutoff.

Read aloud: a validator that ticks to the support cutoff of slot `s + 1`, awake since the duty
window's start, leaves its tick there with what an outcome of that tick holds. -/
theorem update_state_of_tick (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s : ℕ) (v : V)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {i : ℕ} (hl₂ : x.lbl i = Event.tick v (M.supportCutoff S.C (s + 1)))
    (hAw : ∃ τ : Time, (x.tickInput v (M.supportCutoff S.C (s + 1))).awakeSince = some τ ∧ τ ≤ duty_window_start S.C (s + 1)) :
    ∃ (n'' : M.N) (sent : List (NamedObject V)),
      .ok (n'', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (M.supportCutoff S.C (s + 1)))
        ((M.supportCutoff S.C (s + 1) : ℕ) : Int) ∧
      AwakeFor M S.C (x.tickInput v (M.supportCutoff S.C (s + 1))) (s + 1) ∧
      (x.tickOutput v (M.supportCutoff S.C (s + 1))).savedConfirmation =
        M.savedConfirmation n'' ∧
      (x.tickOutput v (M.supportCutoff S.C (s + 1))).fastBlocks = M.fastBlocks n'' ∧
      (x.tickOutput v (M.supportCutoff S.C (s + 1))).lockEntries = M.lockEntries n'' ∧
      (x.tickOutput v (M.supportCutoff S.C (s + 1))).latestConfirmed =
        M.latestConfirmed n'' := by
  -- the tick reads `v`'s state at its own step `i` and leaves the outcome the step took (`RunFacts.tick`)
  have hti : x.tickInput v (M.supportCutoff S.C (s + 1)) = x.st i v := by
    unfold Trace.tickInput; rw [(tickStep_eq_of_lbl M) x E hl₂]
  have hto : x.tickOutput v (M.supportCutoff S.C (s + 1)) = x.st (i + 1) v := by
    unfold Trace.tickOutput; rw [(tickStep_eq_of_lbl M) x E hl₂]
  obtain ⟨n'', sent, hok, hst, -⟩ := R.tick i v _ hl₂
  refine ⟨n'', sent, by rw [hti]; exact hok, hAw, ?_, ?_, ?_, ?_⟩ <;> rw [hto, hst]

/-- The tick-to-update link, the lock-entry form. Write `c` for the support cutoff of slot `s + 1`
and `X` for `v`'s node state before `c`. When `v` holds before `t` a lock entry with the deadline of
a lock of slot `s`, and `c` is before `t`, then `v` was awake and honest at `c`, its tick at `c`
started from a record of awakeness since the duty window's start of slot `s + 1` or earlier, the
tick at `c` from `X` has an outcome `(n'', sent)`, `X` is awake for slot `s + 1`, and `v`'s state
before `c + 1` has `n''`'s saved confirmations and lock entries.

Why: the entry is traced (`lockTracedAfterTick_of_mem`) to the update of the slot its deadline names, which
is `s`; the tick at `c` from `X` has an outcome (`cutoff_tick_outcome_of_active`), and after the step
`i₀ := stepBefore x c` some entry with that deadline is held, and none is held at `i₀`, since an
entry held there would be traced to an update before `i₀`. So the step `i₀` changed the lock
entries, and of the three cases of `step_cases_lock_saved` only the update at the support cutoff
can: the first keeps a subset, the second adds only entries moved from held ones with their
deadlines, at a vote time, and `i₀` is the tick at `c`. The rest is `update_state_of_tick`.

The landed statement names the answer `A''` of the confirmation update; the twin names the outcome
of the tick the step took, under the wake condition (as `update_state_of_tick`).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `s`: the slot of the
  lock; `v`: the validator; `e`: the lock entry.

Read aloud: a lock entry of slot `s` held after the support cutoff of slot `s + 1` means the
validator was awake and honest there, passed the duty test, and left the tick with what an outcome
of that tick holds. -/
theorem update_state_of_lock_entry (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (t s : ℕ) (v : V) (e : M.LE)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (he : e ∈ (x.stateBefore t v).lockEntries)
    (hd : e.d = S.C.t_ (s + S.C.k) + 5 * S.C.Δ)
    (hts : M.supportCutoff S.C (s + 1) < t) :
    v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.supportCutoff S.C (s + 1)) ∧
    (∃ τ : Time, (x.tickInput v (M.supportCutoff S.C (s + 1))).awakeSince = some τ ∧ τ ≤ duty_window_start S.C (s + 1)) ∧
    ∃ (n'' : M.N) (sent : List (NamedObject V)),
      .ok (n'', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (M.supportCutoff S.C (s + 1)))
        ((M.supportCutoff S.C (s + 1) : ℕ) : Int) ∧
      AwakeFor M S.C (x.tickInput v (M.supportCutoff S.C (s + 1))) (s + 1) ∧
      (x.tickOutput v (M.supportCutoff S.C (s + 1))).savedConfirmation =
        M.savedConfirmation n'' ∧
      (x.tickOutput v (M.supportCutoff S.C (s + 1))).lockEntries = M.lockEntries n'' := by
  -- the entry is traced to `v`'s update of slot `s + 1`, at `v`'s own tick to the cutoff
  obtain ⟨s₂, hd₂, -, hlab, hAw, -⟩ :=
    (lockTracedAfterTick_of_mem M F U) S A x R E v (x.stepBefore t) e he
  have hs₂ : s₂ = s := lockDeadline_injective S (hd₂.symm.trans hd)
  subst hs₂
  obtain ⟨n'', sent, hrun, hA, hsv, -, hlk, -⟩ :=
    (update_state_of_tick M F U) S A x R s₂ v E hlab hAw
  refine ⟨?_, hAw, n'', sent, hrun, hA, hsv, hlk⟩
  -- `v`'s tick to the cutoff starts awake since the duty window's start of slot `s + 1` or earlier,
  -- so `v` is awake from that start up to the tick, and honest there (a tick is by an active
  -- validator)
  obtain ⟨τ, hτ, hτle⟩ := hAw
  have hex : ∃ i : ℕ, x.lbl i = Event.tick v (M.supportCutoff S.C (s₂ + 1)) := by
    first | exact hlab | exact ⟨_, hlab⟩
  have hlk := x.lbl_tickStep hex
  refine E.mem_activeThroughoutToTick_of_awakeThroughoutToTick ?_
  rcases (awake_of_tickInput_awakeSince_of_tick M F) x R E hex hτ with ⟨-, hall⟩ | ⟨k₁, τ', hk₁, hl₁, hτ', hall⟩
  · exact Activity.mem_awakeThroughoutToTick_of_forall hlk hall
  · exact Activity.mem_awakeThroughoutToTick_of_tick (by rw [hτ']; exact hτle) hk₁.le hlk hl₁ hall

end GoldilocksCorrectness.Record.Proofs.Executions

