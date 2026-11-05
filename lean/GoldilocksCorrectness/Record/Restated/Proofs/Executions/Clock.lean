module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Monotone
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.NoRaiseStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Node
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Wiring
public import GoldilocksCorrectness.Statements.Executions.NoRaiseStatements

@[expose] public section

/-!
# Clock, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Clock.lean` over a model `M` whose facts
`F` hold, for an execution `x` of `protocolOf M S`: what a step does to a validator's node state
(its own tick's outcome in the model, a delivery's `M.receive`, or nothing), the stamps a step
writes, and the clock along an execution, which is the clock value `x.clockValue i v` of the trace
(`clock_eq_clockValue`), from the facts of the tick (`F.tk.tick_step`), of the receipt (`F.rcv.receive_step`) and of the initial state
(`F.init`). The node state a tick starts from has the validator's tree, votes held and clock
(`tickInputState_frame`, which the record states through its readers where the landed theorem
equates the FG and AC states).
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Proofs.Routines (DREBPost DREBPost.bind DREBPost.bind_any DREBPost.dite
  DREBPost.ite DREBPost.of_outcome DREBPost.pure)

open GoldilocksCorrectness.Proofs.Routines (fg_on_attestation_keeps fg_on_block_eq)

open GoldilocksCorrectness.Proofs.Routines (ac_on_block_grows ac_on_tick_grows
  on_goldfish_vote_grows)

open GoldilocksCorrectness.Proofs.Routines (StepFrom on_ac_message_step on_attestation_step
  on_block_step tick_step)

open GoldilocksCorrectness.Proofs.Routines (acState_initial_eq fgState_initial_eq initial_eq
  wake_eq)

open GoldilocksCorrectness.Proofs.Routines (receive_step)

namespace GoldilocksCorrectness.Record.Proofs.Executions

open GoldilocksCorrectness.Record.Proofs.Routines (SlotKeyed StampsAt)

open Goldilocks
open GoldilocksCorrectness.Record.Statements.Executions

variable {V : Type} [DecidableEq V] [Fintype V]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-! ## The relation -/

section Relation

end Relation

/-! ## The routines -/

section Routines

variable [RootOrder]

end Routines

/-! ## The steps -/

section Steps

open Framework.StsMultisetLog (SignedMsg TickAllAwakeWake tickAllAwakeUpdate_getElem_react tickAllAwakeUpdate_getElem_st_of_not_react applyNodeStepResult_getElem receive_getElem nodeStep_iff_exists)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks.Sts (Setup)

variable [RootOrder] {S : Setup V} {A : Activity V}

/-- The pool of every validator is filed by slot, at every step (the clock-free part of Lemma 11,
`lem11_node_invariantCore_of_run`, which holds for every validator).

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `i`: the step; `v`: the validator.

Read aloud: every validator's votes are filed by slot, at every step. -/
theorem slotKeyed_of_exec (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (i : ℕ) (v : V) :
    SlotKeyed M (x.st i v) :=
  (GoldilocksCorrectness.Record.Proofs.Routines.SlotKeyed.of_poolKeyed M F)
    (F.nd.nodeInvCore_poolKeyed ((GoldilocksCorrectness.Record.Proofs.Executions.lem11_node_invariantCore_of_run M F) S x R i v).1)

/-- Every validator starts from Goldilocks's initial node state.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `v`: the validator.

Read aloud: every validator starts from the model's initial node state. -/
theorem getElem_zero_st (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (v : V) :
    x.st 0 v = M.initial S.C v := by
  exact R.init v

/-- **At the tick of every awake validator at `t`, a validator awake and outside the adversary set
at `t` holds the answer of an `.ok` outcome of its tick**, from `tickInputState`, and every object
of that outcome is on the wire under its signature after the step (the outcome the step took: the
model's tick may have several).

Why: the atomic step gives the validator a tick step from `tickInputState`; by `step_tick_iff` it
is an answer of the tick, or the state kept when the tick has no answer, and the second is
excluded because the tick never fails (`ticksSucceed_of_exec`).

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `i`: the step; `t`: the time of the tick; `v`: the validator.

Read aloud: after its tick, the validator holds a node state its tick could answer. -/
theorem tick_step_outcome (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) {i t : ℕ} {v : V}
    -- the step `i` is the tick of every awake validator at `t`
    (hl : x.lbl i = Event.tick v t)
    -- `v` is awake and outside the adversary set at `t`
    (hv : v ∈ A.awakeAtTime x t) (hadv : v ∉ A.corruptedAtTime x t) :
    ∃ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ (M.tick S.C S.P S.X (x.tickInput v t) (t : Int)) ∧
        x.st (i + 1) v = n' ∧ ∀ o ∈ sent, (⟨v, o⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i := by
  have hts := (tickStep_eq_of_lbl M) x E hl
  obtain ⟨n', sent, hok, hst, hsent⟩ := R.tick i v t hl
  refine ⟨n', sent, ?_, hst, fun o ho => ?_⟩
  · unfold Trace.tickInput
    rw [hts]
    exact hok
  · rw [hsent, add_tsub_cancel_left]
    exact Multiset.mem_map.2 ⟨o, Multiset.mem_coe.2 ho, rfl⟩

/-- What a step does to a validator's node state, per step: it keeps it; or it is the validator's
tick, with the validator active at the step, and the validator holds the answer of an `.ok` outcome
of its tick; or it delivers a signed message to the validator, active at the step, and the
validator holds what `receive` leaves; or it is the validator's restart, the validator not awake at
the step, and the validator holds its wake at the restart's clock value.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `i`: the step; `v`: the
  validator.

Read aloud: only the validator's own tick, a delivery to it and its restart change its node
state. -/
theorem step_cases_per_step (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (i : ℕ) (v : V) :
    x.st (i + 1) v = x.st i v ∨
      (∃ (t : ℕ) (n' : M.N) (sent : List (NamedObject V)),
        x.lbl i = Event.tick v t ∧
        v ∈ A.active i ∧
        .ok (n', sent) ∈ (M.tick S.C S.P S.X (x.tickInput v t) (t : Int)) ∧
        x.st (i + 1) v = n' ∧ ∀ o ∈ sent, (⟨v, o⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∨
      (∃ sm : SignedMsg V (NamedObject V), x.lbl i = Event.deliver v sm ∧
        v ∈ A.active i ∧
        x.st (i + 1) v = M.receive S.C S.P S.X (x.st i v) sm.msg) ∨
      ((∃ (tRestart : ℕ) (keep : Bool), x.lbl i = Event.restart v tRestart keep) ∧ v ∉ A.awake i ∧
        ∀ (tRestart : ℕ) (keep : Bool), x.lbl i = Event.restart v tRestart keep →
          x.st (i + 1) v = M.wake (x.st i v) (tRestart : Int)) := by
  by_cases hv' : (∃ t, x.lbl i = Event.tick v t) ∨
      (∃ (tRestart : ℕ) (keep : Bool), x.lbl i = Event.restart v tRestart keep) ∨
      ∃ sm, x.lbl i = Event.deliver v sm
  · rcases hv' with ⟨t, hl⟩ | ⟨tR, keep, hl⟩ | ⟨sm, hl⟩
    · have hact := (E.tick_active i v t hl).1
      have hts := (tickStep_eq_of_lbl M) x E hl
      obtain ⟨n', sent, hok, hst, hsent⟩ := R.tick i v t hl
      refine Or.inr (Or.inl ⟨t, n', sent, hl, hact, ?_, hst, fun o ho => ?_⟩)
      · unfold Trace.tickInput
        rw [hts]
        exact hok
      · rw [hsent, add_tsub_cancel_left]
        exact Multiset.mem_map.2 ⟨o, Multiset.mem_coe.2 ho, rfl⟩
    · exact Or.inr (Or.inr (Or.inr ⟨⟨tR, keep, hl⟩, (E.restart_crashed i v tR keep hl).1,
        fun tR' keep' hl' => (R.restart i v tR' keep' hl').1⟩))
    · exact Or.inr (Or.inr (Or.inl
        ⟨sm, hl, E.deliver_active i v sm hl, (R.deliver i v sm hl).2.1⟩))
  · push_neg at hv'
    exact Or.inl (R.untouched i v hv'.1 hv'.2.1 hv'.2.2)

/-- What a step does to a validator's node state: it keeps it; or it is the validator's tick, with
the validator active at the tick's step, and the validator holds the answer of an `.ok` outcome of
its tick; or it delivers a signed message to the validator, active at the step, and the validator
holds what `receive` leaves; or it is the validator's restart, the validator not awake at the step,
and the validator holds its wake at the step's time.

 the restart's validator is not awake at its step
(`restart_crashed`). This is `step_cases_per_step`, under the name its callers use.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `i`: the step; `v`: the
  validator.

Read aloud: only the validator's own tick, a delivery to it and its restart change its node
state. -/
theorem step_cases (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (i : ℕ) (v : V) :
    x.st (i + 1) v = x.st i v ∨
      (∃ (t : ℕ) (n' : M.N) (sent : List (NamedObject V)),
        x.lbl i = Event.tick v t ∧
        v ∈ A.active i ∧
        .ok (n', sent) ∈ (M.tick S.C S.P S.X (x.tickInput v t) (t : Int)) ∧
        x.st (i + 1) v = n' ∧ ∀ o ∈ sent, (⟨v, o⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∨
      (∃ sm : SignedMsg V (NamedObject V), x.lbl i = Event.deliver v sm ∧
        v ∈ A.active i ∧
        x.st (i + 1) v = M.receive S.C S.P S.X (x.st i v) sm.msg) ∨
      ((∃ (tRestart : ℕ) (keep : Bool), x.lbl i = Event.restart v tRestart keep) ∧ v ∉ A.awake i ∧
        ∀ (tRestart : ℕ) (keep : Bool), x.lbl i = Event.restart v tRestart keep →
          x.st (i + 1) v = M.wake (x.st i v) (tRestart : Int)) :=
  (step_cases_per_step M F) x R E i v

--

/-! ## The wake, per node: what it keeps (the fourth case of `step_cases`) -/

/-- At `v`'s wake, `v`'s tree is kept.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the trace; `R`: the run's facts; `E`: the environment's facts; `i`: the step; `v`: the
  validator.

Read aloud: a wake keeps the blocks a validator holds. -/
theorem wake_case_tree (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    
    {i : ℕ} {v : V} {tRestart : ℕ} {keep : Bool} (hl : x.lbl i = Event.restart v tRestart keep) : (x.st (i + 1) v).tree = (x.st i v).tree := by
  rw [(R.restart i v tRestart keep hl).1]
  exact (F.wk.wake_readers _ _).2.2.1

/-- At `v`'s wake, `v`'s held Goldfish votes are kept.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the trace; `R`: the run's facts; `E`: the environment's facts; `i`: the step; `v`: the
  validator.

Read aloud: a wake keeps the votes a validator holds. -/
theorem wake_case_votesHeld (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    
    {i : ℕ} {v : V} {tRestart : ℕ} {keep : Bool} (hl : x.lbl i = Event.restart v tRestart keep) :
    M.votesHeld (x.st (i + 1) v) = M.votesHeld (x.st i v) := by
  rw [(R.restart i v tRestart keep hl).1]
  exact (F.wk.wake_readers _ _).2.2.2.2.2.2.2.1

/-- At `v`'s wake, `v`'s finalized block is kept.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the trace; `R`: the run's facts; `E`: the environment's facts; `i`: the step; `v`: the
  validator.

Read aloud: a wake keeps a validator's finalized block. -/
theorem wake_case_finalized (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    
    {i : ℕ} {v : V} {tRestart : ℕ} {keep : Bool} (hl : x.lbl i = Event.restart v tRestart keep) :
    (x.st (i + 1) v).finalized = (x.st i v).finalized := by
  rw [(R.restart i v tRestart keep hl).1]
  exact (F.wk.wake_readers _ _).2.2.2.1

/-- At `v`'s wake, `v`'s clock is set to the restart's clock value.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the trace; `R`: the run's facts; `E`: the environment's facts (not read); `i`: the step; `v`:
  the validator.

Read aloud: a wake sets a validator's clock to the clock value of its restart. -/
theorem wake_case_clock (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (_E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {i : ℕ} {v : V} {tRestart : ℕ} {keep : Bool} (hl : x.lbl i = Event.restart v tRestart keep) :
    (x.st (i + 1) v).t = (tRestart : Int) := by
  rw [(R.restart i v tRestart keep hl).1]
  exact (F.wk.wake_readers _ _).2.1

/-- At `v`'s wake, `v`'s wake time is cleared.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the trace; `R`: the run's facts; `E`: the environment's facts; `i`: the step; `v`: the
  validator.

Read aloud: after a wake, a validator has no time it has been awake since. -/
theorem wake_case_awakeSince (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    
    {i : ℕ} {v : V} {tRestart : ℕ} {keep : Bool} (hl : x.lbl i = Event.restart v tRestart keep) : (x.st (i + 1) v).awakeSince = none := by
  rw [(R.restart i v tRestart keep hl).1]
  exact F.wk.wake_awakeSince _ _

/-- When `v`'s tick to `t` starts from a node state with a present `awakeSince`, no step `k` before
that tick, after which no tick of `v` comes before it, is `v`'s restart: a restart clears
`awakeSince`, and every later step up to the tick keeps it cleared (a delivery keeps it, a second
restart clears it again, and no tick of `v` is there).

The variables:
- `M`: the model; `F`: its facts;
- `x`: the trace; `R`: the run's facts; `E`: the environment's facts; `t`: the clock value; `v`: the
  validator; `τ`: the time the tick input records; `k`: the step; `hnt`: no tick of `v` after `k`
  and before its tick to `t`.

Read aloud: a tick that reads a wake time comes after no restart of its validator since its last
tick. -/
theorem no_restart_of_tickInput_awakeSince_some (x : Trace V (NamedObject V) M.N)
    (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {t : ℕ} {v : V} {τ : Time} (hτ : (x.tickInput v t).awakeSince = some τ) {k : ℕ}
    (hk : k < x.tickStep v t)
    -- no step after `k` and before `v`'s tick to `t` is a tick of `v`
    (hnt : ∀ (l t' : ℕ), k < l → l < x.tickStep v t → x.lbl l ≠ Event.tick v t') :
    ∀ (tRestart : ℕ) (keep : Bool), x.lbl k ≠ Event.restart v tRestart keep := by
  intro tR keep hl
  have key : ∀ m, k + 1 ≤ m → m ≤ x.tickStep v t → (x.st m v).awakeSince = none := by
    intro m hm1 hm2
    induction m, hm1 using Nat.le_induction with
    | base => exact (wake_case_awakeSince M F) x R hl
    | succ m hm ih =>
        have ih' := ih (by omega)
        rcases (step_cases_per_step M F) x R E m v with h | ⟨t', -, -, hl', -⟩ | ⟨sm, -, -, h⟩ |
            ⟨⟨tR', keep', hl'⟩, -, -⟩
        · rw [h]
          exact ih'
        · exact absurd hl' (hnt m t' (by omega) (by omega))
        · rw [h, (GoldilocksCorrectness.Record.Proofs.Routines.receive_awakeSince M F)]
          exact ih'
        · exact (wake_case_awakeSince M F) x R hl'
  have hnone : (x.tickInput v t).awakeSince = none := key (x.tickStep v t) (by omega) le_rfl
  rw [hnone] at hτ
  cases hτ

/-- Across a step, every block and vote a validator adds is stamped with the clock the step leaves
it at.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `i`: the step; `v`: the validator.

Read aloud: what a step adds to a validator's node state is stamped with its clock. -/
theorem step_stamps (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (i : ℕ) (v : V) :
    StampsAt M (x.st i v) (x.st (i + 1) v) := by
  have hk := (slotKeyed_of_exec M F) x R E i v
  rcases (step_cases_per_step M F) x R E i v with h | ⟨t, n', sent, hl, -, hok, h, -⟩ |
      ⟨sm, -, -, h⟩ | ⟨⟨tR, keep, hl⟩, -, h⟩
  · rw [h]
    exact (GoldilocksCorrectness.Record.Proofs.Routines.StampsAt.refl M F) _
  · rw [h]
    have hin : x.tickInput v t = x.st i v := by
      unfold Trace.tickInput
      rw [(tickStep_eq_of_lbl M) x E hl]
    rw [hin] at hok
    have hstep := F.tk.tick_step S.C S.P S.X _ (t : Int) n' sent hok hk
    unfold StampsAt
    rw [hstep.2.2.2]
    exact hstep.2.2.1
  · rw [h]
    exact (F.rcv.receive_step S.C S.P S.X _ sm.msg hk).2.2.1
  · rw [h tR keep hl]
    obtain ⟨-, -, hT, -, -, -, -, hV, -⟩ := F.wk.wake_readers (x.st i v) (tR : Int)
    exact (GoldilocksCorrectness.Record.Proofs.Routines.StampsAt.congr_left M F) hT hV
      ((GoldilocksCorrectness.Record.Proofs.Routines.StampsAt.refl M F) _)

/-- A validator's tick to the clock value `t` sets its clock to `t` (the clock-free part of Lemma 11,
`lem11_node_invariantCore_of_run`, and `tick_nodeInvCore`).

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `i`: the step; `t`: the clock value of the tick; `v`: the validator.

Read aloud: a validator's tick sets its clock to the tick's clock value. -/
theorem tick_step_clock {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (_E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) {i t : ℕ} {v : V}
    -- the step `i` is `v`'s tick to `t`
    (hl : x.lbl i = Event.tick v t) :
    (x.st (i + 1) v).t = (t : Int) := by
  obtain ⟨n', sent, hok, hst, -⟩ := R.tick i v t hl
  rw [hst]
  exact (F.nd.tick_nodeInvCore S.C S.P S.X _ (t : Int)
    ((lem11_node_invariantCore_of_run M F) S x R i v).1 n' sent hok).2.2

/-- A step other than a tick of `v` keeps `v`'s clock, or is `v`'s wake and sets the clock to the
restart's clock value.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `i`: the step; `v`: the validator.

Read aloud: a step other than a tick keeps every clock, except a wake, which sets the clock to the
clock value of the wake. -/
theorem step_clock_of_not_tick (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) {i : ℕ}
    -- the step `i` is not a tick of `v`
    (v : V) (hl : ∀ t, x.lbl i ≠ Event.tick v t) :
    (x.st (i + 1) v).t = (x.st i v).t ∨
      ((∃ (tRestart : ℕ) (keep : Bool), x.lbl i = Event.restart v tRestart keep) ∧
        ∀ (tRestart : ℕ) (keep : Bool), x.lbl i = Event.restart v tRestart keep →
          (x.st (i + 1) v).t = (tRestart : Int)) := by
  rcases (step_cases_per_step M F) x R E i v with h | ⟨t, -, -, hl', -⟩ | ⟨sm, -, -, h⟩ |
      ⟨hw, -, h⟩
  · rw [h]
    exact Or.inl rfl
  · exact absurd hl' (hl t)
  · rw [h]
    exact Or.inl (F.nd.receive_nodeInvCore S.C S.P S.X _ sm.msg
      ((lem11_node_invariantCore_of_run M F) S x R i v).1).2.2
  · exact Or.inr ⟨hw, fun tR keep hl => by rw [h tR keep hl]; exact (F.wk.wake_readers _ _).2.1⟩

end Steps

/-! ## The clock along an execution -/

section Clock

open Framework.StsMultisetLog (SignedMsg tickAllAwake_of_time atomic_clock_le_time)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks.Sts (Setup)

variable [RootOrder] {S : Setup V} {A : Activity V}

/-- At every step, every validator's node-state clock is its clock value `x.clockValue i v`: the
clock value of its last tick or restart before the step, or `0`, the initial clock. No hypothesis on
activity: a step that is no tick, restart or delivery of `v` leaves both untouched.

Why: by induction on the step, from the initial clock (`initial_clock`); a tick and a restart set the
clock to their clock value (`tick_nodeInvCore` on the clock-free part of Lemma 11, `wake_readers`), a
delivery keeps it (`receive_nodeInvCore`), any other step leaves `v`'s state as it is (`untouched`).

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `R`: the run's facts; `i`: the step; `v`: the validator.

Read aloud: a node's clock reads what its last tick or restart set it to. -/
theorem clock_eq_clockValue (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (i : ℕ) (v : V) :
    (x.st i v).t = (x.clockValue i v : Int) := by
  classical
  induction i with
  | zero =>
      rw [R.init v, Trace.clockValue_zero]
      exact_mod_cast (F.init.initial_clock S.C v).1
  | succ i ih =>
      have hcore := ((lem11_node_invariantCore_of_run M F) S x R i v).1
      by_cases ht : ∃ t : ℕ, x.lbl i = Event.tick v t
      · obtain ⟨t, hl⟩ := ht
        obtain ⟨n', sent, hok, hst, -⟩ := R.tick i v t hl
        rw [hst, x.clockValue_succ_of_tick hl]
        exact (F.nd.tick_nodeInvCore S.C S.P S.X _ (t : Int) hcore n' sent hok).2.2
      by_cases hr : ∃ (t : ℕ) (keep : Bool), x.lbl i = Event.restart v t keep
      · obtain ⟨t, keep, hl⟩ := hr
        rw [(R.restart i v t keep hl).1, x.clockValue_succ_of_restart hl]
        exact (F.wk.wake_readers _ _).2.1
      have ht' : ∀ t : ℕ, x.lbl i ≠ Event.tick v t := fun t h => ht ⟨t, h⟩
      have hr' : ∀ (t : ℕ) (keep : Bool), x.lbl i ≠ Event.restart v t keep :=
        fun t keep h => hr ⟨t, keep, h⟩
      rw [x.clockValue_succ_of_not ht' hr', ← ih]
      by_cases hd : ∃ sm, x.lbl i = Event.deliver v sm
      · obtain ⟨sm, hl⟩ := hd
        rw [(R.deliver i v sm hl).2.1]
        exact (F.nd.receive_nodeInvCore S.C S.P S.X _ sm.msg hcore).2.2
      · push Not at hd
        rw [R.untouched i v ht' hr' hd]

/-- A validator's clock value after a step is at most the real time of that step plus
`ΔClockAhead`, or `0`, the initial clock: the tick or restart that set it was at a real time at least
the clock value minus `ΔClockAhead` (`tick_active`, `restart_time`), and the time never decreases.
The `0` is needed for a negative `ΔClockAhead` (a clock always behind): the initial clock reads `0`
at the real time `0`.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `i`: the step; `v`: the
  validator.

Read aloud: a clock never reads more than the real time plus `ΔClockAhead`, past its initial `0`. -/
theorem clockValue_le_time_add_ahead (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (i : ℕ) (v : V) : (x.clockValue i v : ℝ) ≤ max 0 (x.time i + ΔClockAhead) := by
  rcases x.clockValue_cases i v with ⟨h0, -⟩ | ⟨j, hj, hset, -⟩
  · rw [h0, Nat.cast_zero]
    exact le_max_left _ _
  · have hle : x.time j ≤ x.time i := (time_mono M) x R hj.le
    have hb : (x.clockValue i v : ℝ) - ΔClockAhead ≤ x.time j := by
      rcases hset with hl | ⟨keep, hl⟩
      · exact (E.tick_active j v _ hl).2.1
      · exact (E.restart_time j v _ keep hl).1
    exact le_max_of_le_right (by linarith)

/-- A validator's node-state clock after a step is at most the real time of that step plus
`ΔClockAhead`, or `0`, the initial clock (`clock_eq_clockValue`, `clockValue_le_time_add_ahead`).

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `i`: the step; `v`: the
  validator.

Read aloud: a node's clock never reads more than the real time plus `ΔClockAhead`, past its initial
`0`. -/
theorem clock_le_time_add_ahead (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (i : ℕ) (v : V) : ((x.st i v).t : ℝ) ≤ max 0 (x.time i + ΔClockAhead) := by
  have h := (clockValue_le_time_add_ahead M F) x R E i v
  rw [(clock_eq_clockValue M F) x R i v]
  exact_mod_cast h

/-- From a step to a later one with no tick and no wake of `v` between them, `v`'s clock is kept.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `v`: the validator; `j ≤ i`: the two steps.

Read aloud: with no tick and no wake of `v` between two steps, `v`'s clock is kept. -/
theorem clock_keep (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (v : V) {j i : ℕ} (hji : j ≤ i)
    -- no step from `j` to `i` is a tick of `v`
    (hno : ∀ m : ℕ, j ≤ m → m < i → ∀ t : ℕ, x.lbl m ≠ Event.tick v t)
    -- no step from `j` to `i` is a wake of `v`
    (hnw : ∀ m : ℕ, j ≤ m → m < i → (∀ (tRestart : ℕ) (keep : Bool), x.lbl m ≠ Event.restart v tRestart keep)) :
    (x.st i v).t = (x.st j v).t := by
  induction i, hji using Nat.le_induction with
  | base => rfl
  | succ i hji ih =>
      rcases (step_clock_of_not_tick M F) x R E v (hno i hji (by omega)) with h | ⟨⟨tR, keep, hw⟩, -⟩
      · rw [h]
        exact ih (fun m h1 h2 => hno m h1 (by omega)) (fun m h1 h2 => hnw m h1 (by omega))
      · exact absurd hw (hnw i hji (by omega) tR keep)

/-- A validator's clock is never negative: it is its clock value, a natural number
(`clock_eq_clockValue`).

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts (not read); `i`: the step;
  `v`: the validator.

Read aloud: a validator's clock is never negative. -/
theorem clock_nonneg (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (_E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (i : ℕ) (v : V) :
    (0 : Int) ≤ (x.st i v).t := by
  rw [(clock_eq_clockValue M F) x R i v]
  exact Int.natCast_nonneg _

end Clock

/-! ## The stamps along an execution -/

section Stamps

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks.Sts (Setup)

variable [RootOrder] {S : Setup V} {A : Activity V}

/-- A block that enters a validator's tree at a step is stamped with the validator's clock after
that step (`step_stamps`).

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `k`: the step; `v`: the
  validator; `B`: the block.

Read aloud: a block is stamped with the clock of the step that admitted it. -/
theorem blockStamp_step_clock {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {k : ℕ} {v : V} {B : Block V}
    -- `B` is not in `v`'s tree before the step
    (hnk : B ∉ (x.st k v).tree)
    -- `B` is in `v`'s tree after the step
    (hk1 : B ∈ (x.st (k + 1) v).tree) :
    (x.st (k + 1) v).blockStamp B = some ((x.st (k + 1) v).t : Stamp) :=
  ((step_stamps M F) x R E k v).1 B hk1 hnk

/-- A Goldfish vote that enters a validator's pool of a slot at a step is stamped with the
validator's clock after that step (`step_stamps`).

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `k`: the step; `v`: the
  validator; `s`: the slot; `vote`: the vote.

Read aloud: a vote is stamped with the clock of the step that admitted it. -/
theorem voteStamp_step_clock {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {k : ℕ} {v : V} {s : Slot} {vote : GoldfishVote V}
    -- `vote` is not in `v`'s pool of slot `s` before the step
    (hnk : vote ∉ M.votesHeldSet (x.st k v) s)
    -- `vote` is in `v`'s pool of slot `s` after the step
    (hk1 : vote ∈ M.votesHeldSet (x.st (k + 1) v) s) :
    (x.st (k + 1) v).voteStamp vote = some ((x.st (k + 1) v).t : Stamp) :=
  ((step_stamps M F) x R E k v).2 s vote
    (((GoldilocksCorrectness.Record.Proofs.Routines.mem_pool_iff M F) _ _ _).1 hk1)
    (fun h => hnk (((GoldilocksCorrectness.Record.Proofs.Routines.mem_pool_iff M F) _ _ _).2 h))

/-- A block that enters a validator's tree at a step is stamped with the validator's clock value
after that step (`blockStamp_step_clock`, `clock_eq_clockValue`).

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `k`: the step; `v`: the
  validator; `B`: the block.

Read aloud: a block is stamped with the clock value of the step that admitted it. -/
theorem blockStamp_step_clockValue {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {k : ℕ} {v : V} {B : Block V}
    -- `B` is not in `v`'s tree before the step
    (hnk : B ∉ (x.st k v).tree)
    -- `B` is in `v`'s tree after the step
    (hk1 : B ∈ (x.st (k + 1) v).tree) :
    (x.st (k + 1) v).blockStamp B = some (((x.clockValue (k + 1) v : ℕ) : Int) : Stamp) := by
  rw [(blockStamp_step_clock M F R E) hnk hk1, (clock_eq_clockValue M F) x R (k + 1) v]

/-- A Goldfish vote that enters a validator's pool of a slot at a step is stamped with the
validator's clock value after that step (`voteStamp_step_clock`, `clock_eq_clockValue`).

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `k`: the step; `v`: the
  validator; `s`: the slot; `vote`: the vote.

Read aloud: a vote is stamped with the clock value of the step that admitted it. -/
theorem voteStamp_step_clockValue {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {k : ℕ} {v : V} {s : Slot} {vote : GoldfishVote V}
    -- `vote` is not in `v`'s pool of slot `s` before the step
    (hnk : vote ∉ M.votesHeldSet (x.st k v) s)
    -- `vote` is in `v`'s pool of slot `s` after the step
    (hk1 : vote ∈ M.votesHeldSet (x.st (k + 1) v) s) :
    (x.st (k + 1) v).voteStamp vote = some (((x.clockValue (k + 1) v : ℕ) : Int) : Stamp) := by
  rw [(voteStamp_step_clock M F R E) hnk hk1, (clock_eq_clockValue M F) x R (k + 1) v]

/-- A block other than the genesis block that a validator's tree holds entered it at an earlier
step, and is stamped with the validator's clock after that step.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `i`: the step; `v`: the
  validator; `B`: the block;
- `k`: the step at which `B` entered `v`'s tree.

Read aloud: a non-genesis block held entered the tree at an earlier step, stamped with that step's
clock. -/
theorem blockStamp_entry_clock {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {i : ℕ} {v : V} {B : Block V}
    -- `v`'s tree holds `B` at `i`
    (hB : B ∈ (x.st i v).tree)
    -- `B` is not the genesis block
    (hg : B ≠ Block.genesis) :
    ∃ k < i, B ∉ (x.st k v).tree ∧ B ∈ (x.st (k + 1) v).tree ∧
      (x.st i v).blockStamp B = some ((x.st (k + 1) v).t : Stamp) := by
  classical
  have hex : ∃ m : ℕ, B ∈ (x.st m v).tree := ⟨i, hB⟩
  have h0 : B ∉ (x.st 0 v).tree := by
    rw [(getElem_zero_st M F) x R, F.init.initial_tree S.C v]
    intro h
    exact hg (Finset.mem_singleton.1 h)
  have hpos : Nat.find hex ≠ 0 := by
    intro h
    exact h0 (h ▸ Nat.find_spec hex)
  have hle : Nat.find hex ≤ i := Nat.find_min' hex hB
  obtain ⟨k, hk⟩ : ∃ k : ℕ, Nat.find hex = k + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hnk : B ∉ (x.st k v).tree := Nat.find_min hex (by omega)
  have hk1 : B ∈ (x.st (k + 1) v).tree := hk ▸ Nat.find_spec hex
  refine ⟨k, by omega, hnk, hk1, ?_⟩
  rw [(blockStamp_kept M F) x R E v (show k + 1 ≤ i by omega) hk1]
  exact (blockStamp_step_clock M F R E) hnk hk1

/-- A Goldfish vote that a validator's pool of a slot holds entered it at an earlier step, and is
stamped with the validator's clock after that step.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `i`: the step; `v`: the
  validator; `s`: the slot; `vote`: the vote;
- `k`: the step at which `vote` entered `v`'s pool of slot `s`.

Read aloud: a vote held entered at an earlier step, stamped with that step's clock. -/
theorem voteStamp_entry_clock {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {i : ℕ} {v : V} {s : Slot} {vote : GoldfishVote V}
    -- `v`'s pool of slot `s` holds `vote` at `i`
    (hv : vote ∈ M.votesHeldSet (x.st i v) s) :
    ∃ k < i, vote ∉ M.votesHeldSet (x.st k v) s ∧ vote ∈ M.votesHeldSet (x.st (k + 1) v) s ∧
      (x.st i v).voteStamp vote = some ((x.st (k + 1) v).t : Stamp) := by
  classical
  have hex : ∃ m : ℕ, vote ∈ M.votesHeldSet (x.st m v) s := ⟨i, hv⟩
  have h0 : vote ∉ M.votesHeldSet (x.st 0 v) s := by
    rw [(getElem_zero_st M F) x R]
    intro h
    have h' := ((GoldilocksCorrectness.Record.Proofs.Routines.mem_pool_iff M F) _ _ _).1 h
    rw [F.init.initial_votesHeld S.C v s] at h'
    exact absurd h' List.not_mem_nil
  have hpos : Nat.find hex ≠ 0 := by
    intro h
    exact h0 (h ▸ Nat.find_spec hex)
  have hle : Nat.find hex ≤ i := Nat.find_min' hex hv
  obtain ⟨k, hk⟩ : ∃ k : ℕ, Nat.find hex = k + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hnk : vote ∉ M.votesHeldSet (x.st k v) s := Nat.find_min hex (by omega)
  have hk1 : vote ∈ M.votesHeldSet (x.st (k + 1) v) s := hk ▸ Nat.find_spec hex
  refine ⟨k, by omega, hnk, hk1, ?_⟩
  rw [(voteStamp_kept M F) x R E v (show k + 1 ≤ i by omega) hk1]
  exact (voteStamp_step_clock M F R E) hnk hk1

/-- The genesis block is stamped `⊥`, earlier than every time, at every step.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `i`: the step; `v`: the validator.

Read aloud: the genesis block is stamped earlier than every time, at every step. -/
theorem genesis_stamp (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (i : ℕ) (v : V) :
    (x.st i v).blockStamp Block.genesis = some ⊥ := by
  have h0 : (Block.genesis : Block V) ∈ (x.st 0 v).tree := by
    rw [(getElem_zero_st M F) x R, F.init.initial_tree S.C v]
    exact Finset.mem_singleton_self _
  rw [(blockStamp_kept M F) x R E v (Nat.zero_le i) h0, (getElem_zero_st M F) x R]
  rw [(F.init.initial_stamps S.C v).2 Block.genesis, if_pos rfl]

/-- A block stamped, in a validator's tree, before the clock value `c` is in the state the
validator's tick to `c` reads. When `v`'s tree holds `B` at step `i`, stamped `τ < c`, `v` ticks to
`c` at step `k`, and `v` is outside the adversary set after `i` steps, then `v`'s tree holds `B` at
`k`.

Why: the genesis block is in every tree (`mem_T_mono` from the initial tree). Any other block entered
`v`'s tree at a step `e + 1 ≤ i`, stamped with `v`'s clock value after that step
(`blockStamp_entry_clock`, `clock_eq_clockValue`). Were the tick at `k ≥ e + 1`, the tree would hold
`B` at `k` (`mem_T_mono`); were it at `k ≤ e`, `v`'s clock value after `k` would be `c`, and at
`e + 1` at least `c` (`clockValue_mono`, `v` honest after `e + 1` steps by the permanence of
corruption), against `τ < c`.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `i`: the step at which the
  tree is read; `k`: the step of the tick; `c`: its clock value; `v`: the validator; `B`: the block;
  `τ`: its stamp.

Read aloud: what a validator stamped before the clock value `c`, it holds when its clock reaches
`c`. -/
theorem mem_T_tick_of_blockStamp_lt (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {i k c : ℕ} {v : V} {B : Block V} {τ : Stamp}
    -- `v` ticks to `c` at step `k`
    (hl : x.lbl k = Event.tick v c)
    -- `v` is outside the adversary set after `i` steps
    (hv : v ∉ A.corrupted i)
    -- `v`'s tree holds `B` at `i`, stamped `τ`, before `c`
    (hB : B ∈ (x.st i v).tree) (hτ : (x.st i v).blockStamp B = some τ) (hlt : τ < ((c : Int) : Stamp)) :
    B ∈ (x.st k v).tree := by
  by_cases hg : B = Block.genesis
  · subst hg
    have h0 : (Block.genesis : Block V) ∈ (x.st 0 v).tree := by
      rw [(getElem_zero_st M F) x R, F.init.initial_tree S.C v]
      exact Finset.mem_singleton_self _
    exact (mem_T_mono M F) x R E v (Nat.zero_le k) h0
  obtain ⟨e, hei, -, he1, hst⟩ := (blockStamp_entry_clock M F) R E hB hg
  by_cases hek : e + 1 ≤ k
  · exact (mem_T_mono M F) x R E v hek he1
  · exfalso
    rw [hτ, (clock_eq_clockValue M F) x R (e + 1) v] at hst
    have hτe : τ = (((x.clockValue (e + 1) v : ℕ) : Int) : Stamp) := Option.some.inj hst
    have hve : v ∉ A.corrupted (e + 1) := fun h => hv (E.corrupted_mono _ _ (by omega) h)
    have hmono : x.clockValue (k + 1) v ≤ x.clockValue (e + 1) v := E.clockValue_mono (by omega) hve
    rw [x.clockValue_succ_of_tick hl] at hmono
    rw [hτe] at hlt
    have hlt' : ((x.clockValue (e + 1) v : ℕ) : Int) < (c : Int) := WithBot.coe_lt_coe.1 hlt
    omega

end Stamps

end GoldilocksCorrectness.Record.Proofs.Executions

