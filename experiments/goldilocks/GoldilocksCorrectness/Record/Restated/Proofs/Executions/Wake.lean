module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Clock
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Wiring
public import GoldilocksCorrectness.Proofs.Executions.Wake
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption

@[expose] public section

/-!
# Wake, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Wake.lean` over a model `M` whose facts `F`
hold, for an execution `x` of `protocolOf M S`: the time since which a validator has been awake,
`awakeSince`, along an execution: kept by every step but a wake, and read back from a tick input
to the validator's last restart; the carriers over a validator's own history between two steps
(`st_eq_fold_nodeEvents`, `st_eq_fold_deliveries`); from the facts of the tick
(`F.tk.tick_clock_validator_awakeSince`), of the receipt (`receive_awakeSince`), of the wake
(`F.wk.wake_awakeSince`) and of the initial state (`F.init.initial_awakeSince`).
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (dutyWindowStart)
open GoldilocksCorrectness.Proofs.Routines (proposal_window_start_zero_le
  proposal_window_start_zero_le_duty)

open GoldilocksCorrectness.Proofs.Routines (DREBPost DREBPost.bind DREBPost.bind_any DREBPost.dite
  DREBPost.ite DREBPost.of_outcome DREBPost.pure)

open GoldilocksCorrectness.Proofs.Routines (on_block_eq record_awake_awakeSince_none
  record_awake_awakeSince_some tick_awakeSince tick_step)

open GoldilocksCorrectness.Proofs.Routines (initial_eq wake_eq)

open GoldilocksCorrectness.Proofs.Routines (receive_step)

open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_eq_toNat)

namespace GoldilocksCorrectness.Record.Proofs.Executions

open GoldilocksCorrectness.Proofs.Executions (not_mem_entrants)

open GoldilocksCorrectness.Record.Proofs.Routines (SlotKeyed)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-! ## The routines -/

section Routines

end Routines

/-! ## The times -/

section Times

end Times

/-! ## The steps -/

section Steps

variable {S : Setup V} {A : Activity V}

/-- A step keeps a present `awakeSince` of `v` when, if it is a tick, `v` does not enter the awake
set at it: a delivery keeps `awakeSince`, and a tick from the stored state keeps a present value
(`record_awake`).

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `i`: the step; `v`: the validator; `τ`: the stored time.

Read aloud: a step keeps the time a validator has been awake since, unless it wakes it. -/
theorem step_keeps_awakeSince (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (i : ℕ) (v : V)
    -- the step is not `v`'s wake
    (hne : (∀ (tRestart : ℕ) (keep : Bool), x.lbl i ≠ Event.restart v tRestart keep))
    (τ : Time) (hτ : (x.st i v).awakeSince = some τ) :
    (x.st (i + 1) v).awakeSince = some τ := by
  rcases (step_cases_per_step M F) x R E i v with h | ⟨t, n', sent, hl, -, hok, h, -⟩ |
      ⟨sm, -, -, h⟩ | ⟨⟨tR, keep, hl⟩, -, -⟩
  · rw [h]
    exact hτ
  · have hin : x.tickInput v t = x.st i v := by
      unfold Trace.tickInput
      rw [(tickStep_eq_of_lbl M) x E hl]
    rw [hin] at hok
    rw [h, (F.tk.tick_clock_validator_awakeSince S.C S.P S.X _ (t : Int) n' sent hok).2.2, hτ]
  · rw [h, (GoldilocksCorrectness.Record.Proofs.Routines.receive_awakeSince M F)]
    exact hτ
  · exact absurd hl (hne tR keep)

/-- `e.isOf v`: the event `e` is a restart of `v` or a delivery to `v`.

The variables:
- `v`: the validator; `e`: the event.

Read aloud: `e` is one of `v`'s own restarts or deliveries. -/
def Event.isOf {Msg : Type} (v : V) : Event V Msg → Bool
  | Event.restart u _ _ => decide (u = v)
  | Event.deliver u _ => decide (u = v)
  | _ => false

/-- `x.nodeEvents v j k`: the events of `v` among the steps `j`, …, `k − 1`, in order: `v`'s wakes
and the deliveries to `v`. Ticks are left out: the carriers read it over ranges with no tick of
`v` (`st_eq_fold_nodeEvents`).

The variables:
- `x`: the trace; `v`: the validator; `j`, `k`: the first step and the step after the last.

Read aloud: `v`'s wakes and deliveries from step `j` to step `k − 1`. -/
def Trace.nodeEvents {Msg N : Type} (x : Trace V Msg N) (v : V) (j k : ℕ) :
    List (Event V Msg) :=
  ((List.range (k - j)).map (fun d => x.lbl (j + d))).filter (Event.isOf v)

/-- `applyEvent M S t n e`: what one of `v`'s own events does to `v`'s node state `n`: the model's
wake at the restart's clock value, or the model's receive of the delivered object; any other event
leaves `n`. The argument `t` is not read (the wake reads the restart's own clock value); it is kept
for the users of the `foldl_*` lemmas.

The variables:
- `M`: the model; `S`: the setup; `t`: not read; `n`: the node state; `e`: the event.

Read aloud: the node state after the event `e`. -/
def applyEvent (S : Setup V) (t : ℕ) (n : M.N) : Event V (NamedObject V) → M.N
  | Event.restart _ tRestart _ => M.wake n (tRestart : Int)
  | Event.deliver _ sm => M.receive S.C S.P S.X n sm.msg
  | _ => n

/-- The step `x.firstAt t` is the one after `x.stepBefore t`, for `t ≥ 1`: the time starts at `0`,
so `x.firstAt t` is not `0`.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the trace; `R`: the run's facts; `E`: the environment's facts; `t`: the time.

Read aloud: the first step at `t` comes right after the last step before `t`. -/
theorem firstAt_eq_stepBefore_succ (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {t : ℕ} (ht : 1 ≤ t) : x.firstAt t = x.stepBefore t + 1 := by
  have hle := E.le_time_firstAt t
  unfold Trace.stepBefore
  rcases Nat.eq_zero_or_pos (x.firstAt t) with h0 | h0
  · rw [h0, R.time_zero] at hle
    have : (1 : ℝ) ≤ t := by exact_mod_cast ht
    linarith
  · omega

/-- A present `awakeSince` of `v` after step `j` is kept to every later step `m` when `v` is awake
after every step from `j` to `m − 1`: no step there is a restart of `v` (a restart is by a validator
not awake at its step), and every other step keeps a present value (`step_keeps_awakeSince`).

The variables:
- `M`: the model; `F`: its facts;
- `x`: the trace; `R`: the run's facts; `E`: the environment's facts; `v`: the validator; `j ≤ m`:
  the two steps; `τ`: the stored time.

Read aloud: while a validator stays awake, the time it has been awake since is kept. -/
theorem awakeSince_kept_of_awake_steps (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {v : V} {j m : ℕ} (hjm : j ≤ m)
    -- `v` is awake after every step from `j` to `m − 1`
    (hawake : ∀ i : ℕ, j ≤ i → i < m → v ∈ A.awake i) {τ : Time}
    (hτ : (x.st j v).awakeSince = some τ) : (x.st m v).awakeSince = some τ := by
  revert hawake
  induction m, hjm using Nat.le_induction with
  | base => exact fun _ => hτ
  | succ m hjm ih =>
      intro hawake
      refine (step_keeps_awakeSince M F) x R E m v (fun tR keep hl => ?_) τ
        (ih fun i h1 h2 => hawake i h1 (by omega))
      exact (E.restart_crashed m v tR keep hl).1 (hawake m hjm (by omega))

/-- `Event.deliveredMsg e`: the signed message the event `e` delivers when `e` is a delivery, and
`none` for every other event.

The variables:
- `e`: the event.

Read aloud: the message `e` delivers, if `e` is a delivery. -/
def Event.deliveredMsg {Msg : Type} : Event V Msg → Option (SignedMsg V Msg)
  | Event.deliver _ sm => some sm
  | _ => none

omit F in
/-- An event is among `v`'s events from the step `j` to the step `k − 1` exactly when it is the
event of one of those steps and is `v`'s wake or a delivery to `v`.

The variables:
- `x`: the trace; `v`: the validator; `j`, `k`: the first step and the step after the last; `e`:
  the event.

Read aloud: `x.nodeEvents v j k` holds the events of `v` at the steps from `j` to `k − 1`. -/
theorem mem_nodeEvents {Msg N : Type} (x : Trace V Msg N) (v : V) (j k : ℕ) (e : Event V Msg) :
    e ∈ Trace.nodeEvents x v j k ↔
      ∃ i : ℕ, j ≤ i ∧ i < k ∧ x.lbl i = e ∧ Event.isOf v e = true := by
  unfold Trace.nodeEvents
  simp only [List.mem_filter, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨⟨d, hd, rfl⟩, he⟩
    exact ⟨j + d, by omega, by omega, rfl, he⟩
  · rintro ⟨i, h1, h2, rfl, he⟩
    exact ⟨⟨i - j, by omega, by rw [show j + (i - j) = i by omega]⟩, he⟩

omit F in
/-- Split at a step `m` from `j` to `k`, `v`'s events from `j` to `k − 1` are its events from `j` to
`m − 1` followed by its events from `m` to `k − 1`.

The variables:
- `x`: the trace; `v`: the validator; `j`, `m`, `k`: the steps.

Read aloud: `v`'s events of two adjacent ranges of steps, one after the other. -/
theorem nodeEvents_append {Msg N : Type} (x : Trace V Msg N) (v : V) {j m k : ℕ} (hjm : j ≤ m)
    (hmk : m ≤ k) :
    Trace.nodeEvents x v j k = Trace.nodeEvents x v j m ++ Trace.nodeEvents x v m k := by
  unfold Trace.nodeEvents
  rw [show k - j = (m - j) + (k - m) by omega, List.range_add, List.map_append,
    List.filter_append, List.map_map]
  congr 2
  apply List.map_congr_left
  intro d _
  simp only [Function.comp_apply]
  congr 1
  omega

omit F in
/-- `v`'s events at the one step `m` are that step's event when it is `v`'s, and none otherwise.

The variables:
- `x`: the trace; `v`: the validator; `m`: the step.

Read aloud: `v`'s events at one step. -/
theorem nodeEvents_single {Msg N : Type} (x : Trace V Msg N) (v : V) (m : ℕ) :
    Trace.nodeEvents x v m (m + 1) = [x.lbl m].filter (Event.isOf v) := by
  unfold Trace.nodeEvents
  rw [show m + 1 - m = 1 by omega]
  rfl

omit F in
/-- When no step from `j` to `k − 1` is `v`'s wake, no event among `v`'s events from `j` to `k − 1`
is a wake.

The variables:
- `x`: the trace; `v`: the validator; `j`, `k`: the first step and the step after the last.

Read aloud: with no wake of `v` in a range of steps, no wake among `v`'s events there. -/
theorem wake_not_mem_nodeEvents {Msg N : Type} (x : Trace V Msg N) (v : V) {j k : ℕ}
    -- no step from `j` to `k − 1` is `v`'s wake
    (hno : ∀ i : ℕ, j ≤ i → i < k → (∀ (tRestart : ℕ) (keep : Bool), x.lbl i ≠ Event.restart v tRestart keep)) :
    ∀ (u : V) (tRestart : ℕ) (keep : Bool), Event.restart u tRestart keep ∉ Trace.nodeEvents x v j k := by
  intro u tR keep hu
  obtain ⟨i, h1, h2, hl, he⟩ := (mem_nodeEvents x v j k _).1 hu
  have huv : u = v := by simpa [Event.isOf] using he
  subst huv
  exact hno i h1 h2 tR keep hl

/-- **The carrier between two steps of `v`'s own history.** Over a range of steps with no tick of
`v`, `v`'s state at the later step is its state at the earlier one with its own restarts (the
model's wake) and the deliveries to it (the model's receive) in between applied in order. No order
between a delivery and a tick is read: the range holds no tick of `v`.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the trace; `R`: the run's facts; `t`: the argument `applyEvent` does not read; `v`: the
  validator; `j ≤ k`: the two steps; `hnotick`: no step from `j` to `k − 1` is a tick of `v`.

Read aloud: `v`'s state at a later step is its state at an earlier one with its own deliveries and
restarts in between applied in order. -/
theorem st_eq_fold_nodeEvents (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (t : ℕ)
    {v : V} {j k : ℕ} (hjk : j ≤ k)
    -- no step from `j` to `k − 1` is a tick of `v`
    (hnotick : ∀ (l t' : ℕ), j ≤ l → l < k → x.lbl l ≠ Event.tick v t') :
    x.st k v = (Trace.nodeEvents x v j k).foldl (applyEvent M S t) (x.st j v) := by
  induction k, hjk using Nat.le_induction with
  | base => simp [Trace.nodeEvents]
  | succ k hjk ih =>
      have ih' := ih (fun l t' h1 h2 => hnotick l t' h1 (by omega))
      rw [nodeEvents_append x v hjk (Nat.le_succ k), nodeEvents_single, List.foldl_append, ← ih']
      cases hl : x.lbl k with
      | tick w t' =>
          by_cases hw : w = v
          · subst hw
            exact absurd hl (hnotick k t' hjk (by omega))
          · simp only [List.filter_cons, List.filter_nil, Event.isOf, Bool.false_eq_true, if_false,
              List.foldl_nil]
            exact R.untouched k v (fun t'' h => hw (Event.tick.inj (hl.symm.trans h)).1)
              (fun tR keep h => by cases hl.symm.trans h) (fun sm h => by cases hl.symm.trans h)
      | restart w tR keep =>
          by_cases hw : w = v
          · subst hw
            simp only [List.filter_cons, List.filter_nil, Event.isOf, decide_true, if_true,
              List.foldl_cons, List.foldl_nil, applyEvent]
            exact (R.restart k w tR keep hl).1
          · simp only [List.filter_cons, List.filter_nil, Event.isOf, hw, decide_false, Bool.false_eq_true,
              if_false, List.foldl_nil]
            exact R.untouched k v (fun t'' h => by cases hl.symm.trans h)
              (fun tR' keep' h => hw (Event.restart.inj (hl.symm.trans h)).1)
              (fun sm h => by cases hl.symm.trans h)
      | deliver w sm =>
          by_cases hw : w = v
          · subst hw
            simp only [List.filter_cons, List.filter_nil, Event.isOf, decide_true, if_true,
              List.foldl_cons, List.foldl_nil, applyEvent]
            exact (R.deliver k w sm hl).2.1
          · simp only [List.filter_cons, List.filter_nil, Event.isOf, hw, decide_false, Bool.false_eq_true,
              if_false, List.foldl_nil]
            exact R.untouched k v (fun t'' h => by cases hl.symm.trans h)
              (fun tR keep h => by cases hl.symm.trans h)
              (fun sm' h => hw (Event.deliver.inj (hl.symm.trans h)).1)
      | other =>
          simp only [List.filter_cons, List.filter_nil, Event.isOf, Bool.false_eq_true, if_false,
            List.foldl_nil]
          exact R.untouched k v (fun t'' h => by cases hl.symm.trans h)
            (fun tR keep h => by cases hl.symm.trans h) (fun sm h => by cases hl.symm.trans h)

/-- Over a list of events with no wake, applying each event is receiving each delivered message in
order: a delivery is the model's receive, and every other event but a wake leaves the state.

The variables:
- `M`: the model; `F`: its facts;
- `S`: the setup; `t`: the time of the events; `l`: the events; `n`: the node state.

Read aloud: with no wake among them, the events act as the receipt of the messages they
deliver. -/
theorem foldl_applyEvent_of_no_wake (S : Setup V) (t : ℕ) (l : List (Event V (NamedObject V)))
    (n : M.N)
    -- no event of the list is a wake
    (hl : ∀ (u : V) (tRestart : ℕ) (keep : Bool), Event.restart u tRestart keep ∉ l) :
    l.foldl (applyEvent M S t) n =
      (l.filterMap Event.deliveredMsg).foldl (fun n sm => M.receive S.C S.P S.X n sm.msg) n := by
  induction l generalizing n with
  | nil => rfl
  | cons e l ih =>
      have hl' : ∀ (u : V) (tRestart : ℕ) (keep : Bool), Event.restart u tRestart keep ∉ l :=
        fun u tR keep hu => hl u tR keep (List.mem_cons_of_mem _ hu)
      cases e with
      | restart u tR keep => exact (hl u tR keep List.mem_cons_self).elim
      | deliver u sm =>
          simp only [List.foldl_cons, List.filterMap_cons, Event.deliveredMsg, applyEvent]
          apply ih
          exact hl'
      | tick u t' =>
          simp only [List.foldl_cons, List.filterMap_cons, Event.deliveredMsg, applyEvent]
          apply ih
          exact hl'
      | other =>
          simp only [List.foldl_cons, List.filterMap_cons, Event.deliveredMsg, applyEvent]
          apply ih
          exact hl'

/-- Along a list of events with no wake, the clock is kept: a delivery keeps it
(`F.rcv.receive_keeps_confirmation`), and every other event but a wake leaves the state.

The variables:
- `M`: the model; `F`: its facts;
- `S`: the setup; `t`: the time of the events; `l`: the events; `n`: the node state.

Read aloud: along a validator's events at one time, only a wake writes the clock. -/
theorem foldl_keeps_clock (S : Setup V) (t : ℕ) (l : List (Event V (NamedObject V))) (n : M.N)
    -- no event of the list is a wake
    (hl : ∀ (u : V) (tRestart : ℕ) (keep : Bool), Event.restart u tRestart keep ∉ l) :
    (l.foldl (applyEvent M S t) n).t = n.t := by
  rw [(foldl_applyEvent_of_no_wake M F) S t l n hl]
  generalize l.filterMap Event.deliveredMsg = ms
  induction ms generalizing n with
  | nil => rfl
  | cons sm ms ih =>
      rw [List.foldl_cons, ih]
      exact (F.rcv.receive_keeps_confirmation S.C S.P S.X n sm.msg).2.2.2.2.2

/-- Along a list of events with no wake, `awakeSince` is kept: a delivery keeps it
(`receive_awakeSince`), and every other event but a wake leaves the state.

The variables:
- `M`: the model; `F`: its facts;
- `S`: the setup; `t`: the time of the events; `l`: the events; `n`: the node state.

Read aloud: along a validator's events at one time, only a wake writes the time it has been awake
since. -/
theorem foldl_keeps_awakeSince (S : Setup V) (t : ℕ) (l : List (Event V (NamedObject V)))
    (n : M.N)
    -- no event of the list is a wake
    (hl : ∀ (u : V) (tRestart : ℕ) (keep : Bool), Event.restart u tRestart keep ∉ l) :
    (l.foldl (applyEvent M S t) n).awakeSince = n.awakeSince := by
  rw [(foldl_applyEvent_of_no_wake M F) S t l n hl]
  generalize l.filterMap Event.deliveredMsg = ms
  induction ms generalizing n with
  | nil => rfl
  | cons sm ms ih =>
      rw [List.foldl_cons, ih]
      exact (GoldilocksCorrectness.Record.Proofs.Routines.receive_awakeSince M F) S.C S.P S.X n sm.msg

/-- Along a list of events, the validator is kept: a wake keeps it (`F.wk.wake_readers`), and so does
a delivery (`F.rcv.receive_validator`).

The variables:
- `M`: the model; `F`: its facts;
- `S`: the setup; `t`: the time of the events; `l`: the events; `n`: the node state.

Read aloud: a validator's events do not change the validator its node runs as. -/
theorem foldl_keeps_validator (S : Setup V) (t : ℕ) (l : List (Event V (NamedObject V)))
    (n : M.N) : (l.foldl (applyEvent M S t) n).v = n.v := by
  induction l generalizing n with
  | nil => rfl
  | cons e l ih =>
      rw [List.foldl_cons, ih]
      cases e with
      | restart u tR keep => exact (F.wk.wake_readers n (tR : Int)).1
      | deliver u sm => exact F.rcv.receive_validator S.C S.P S.X n sm.msg
      | tick u t' => rfl
      | other => rfl

/-- Along a list of events, the anti-slashing record and the attestations sent are kept: a wake keeps
them (`F.wk.wake_readers`), and so does a delivery (`F.rcv.receive_Λ`).

The variables:
- `M`: the model; `F`: its facts;
- `S`: the setup; `t`: the time of the events; `l`: the events; `n`: the node state.

Read aloud: a validator's events do not change what its node has signed. -/
theorem foldl_keeps_signingHistory (S : Setup V) (t : ℕ) (l : List (Event V (NamedObject V)))
    (n : M.N) :
    M.sentTarget (l.foldl (applyEvent M S t) n) = M.sentTarget n ∧
      M.sentTimeout (l.foldl (applyEvent M S t) n) = M.sentTimeout n ∧
      M.sentLock (l.foldl (applyEvent M S t) n) = M.sentLock n ∧
      M.sentAttestations (l.foldl (applyEvent M S t) n) = M.sentAttestations n := by
  induction l generalizing n with
  | nil => exact ⟨rfl, rfl, rfl, rfl⟩
  | cons e l ih =>
      obtain ⟨h1, h2, h3, h4⟩ := ih (applyEvent M S t n e)
      rw [List.foldl_cons, h1, h2, h3, h4]
      cases e with
      | restart u tR keep =>
          obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, h5, h6, h7, h8⟩ :=
            F.wk.wake_readers n (tR : Int)
          exact ⟨h5, h6, h7, h8⟩
      | deliver u sm => exact F.rcv.receive_Λ S.C S.P S.X n sm.msg
      | tick u t' => exact ⟨rfl, rfl, rfl, rfl⟩
      | other => exact ⟨rfl, rfl, rfl, rfl⟩

/-- Along a list of events, the tree only grows: a wake keeps it (`F.wk.wake_readers`), and a
delivery keeps every block of it (`F.rcv.receive_tree_mono`).

The variables:
- `M`: the model; `F`: its facts;
- `S`: the setup; `t`: the time of the events; `l`: the events; `n`: the node state.

Read aloud: a validator's events forget no block. -/
theorem foldl_tree_subset (S : Setup V) (t : ℕ) (l : List (Event V (NamedObject V))) (n : M.N) :
    n.tree ⊆ (l.foldl (applyEvent M S t) n).tree := by
  induction l generalizing n with
  | nil => intro B hB; exact hB
  | cons e l ih =>
      rw [List.foldl_cons]
      intro B hB
      apply ih
      cases e with
      | restart u tR keep =>
          show B ∈ (M.wake n (tR : Int)).tree
          rw [show (M.wake n (tR : Int)).tree = n.tree from (F.wk.wake_readers n (tR : Int)).2.2.1]
          exact hB
      | deliver u sm => exact F.rcv.receive_tree_mono S.C S.P S.X n sm.msg hB
      | tick u t' => exact hB
      | other => exact hB

/-- Along a list of events from a node state whose votes are filed by slot, the votes stay filed by
slot and the votes held of each slot only grow, as a prefix: a wake keeps them
(`F.wk.wake_readers`, `slotKeyed_wake`), and a delivery grows them (`F.rcv.receive_step`).

The variables:
- `M`: the model; `F`: its facts;
- `S`: the setup; `t`: the time of the events; `l`: the events; `n`: the node state; `hk`: `n`'s
  votes are filed by slot.

Read aloud: a validator's events forget no vote. -/
theorem foldl_votesHeld_subset (S : Setup V) (t : ℕ) (l : List (Event V (NamedObject V)))
    (n : M.N) (hk : SlotKeyed M n) :
    SlotKeyed M (l.foldl (applyEvent M S t) n) ∧
      ∀ s : Slot, n.votesHeld s <+: (l.foldl (applyEvent M S t) n).votesHeld s := by
  induction l generalizing n with
  | nil => exact ⟨hk, fun s => List.prefix_refl _⟩
  | cons e l ih =>
      rw [List.foldl_cons]
      have key : SlotKeyed M (applyEvent M S t n e) ∧
          ∀ s : Slot, n.votesHeld s <+: (applyEvent M S t n e).votesHeld s := by
        cases e with
        | restart u tR keep =>
            refine ⟨(GoldilocksCorrectness.Record.Proofs.Routines.slotKeyed_wake M F) hk,
              fun s => ?_⟩
            change n.votesHeld s <+: M.votesHeld (M.wake n (tR : Int)) s
            rw [(F.wk.wake_readers n (tR : Int)).2.2.2.2.2.2.2.1]
        | deliver u sm =>
            obtain ⟨h1, ⟨-, -, h3, -, -⟩, -⟩ := F.rcv.receive_step S.C S.P S.X n sm.msg hk
            exact ⟨h1, h3⟩
        | tick u t' => exact ⟨hk, fun s => List.prefix_refl _⟩
        | other => exact ⟨hk, fun s => List.prefix_refl _⟩
      obtain ⟨hk', hp⟩ := key
      obtain ⟨hk'', hp'⟩ := ih _ hk'
      exact ⟨hk'', fun s => (hp s).trans (hp' s)⟩

/-- Along a list of events at the time `t`, from a node state satisfying the model's node invariant
with a clock at most `t`, the invariant is kept, with the validator, and the clock stays at most
`t`: a wake keeps it when the clock is at most the wake's time (`F.nd.wake_nodeInv`, which sets the
clock to `t`), and a delivery keeps it and the clock (`F.nd.receive_nodeInv`).

The variables:
- `M`: the model; `F`: its facts;
- `S`: the setup; `t`: the time of the events; `l`: the events; `n`: the node state.

Read aloud: a validator's events at `t` keep its node invariant. -/
theorem foldl_nodeInv (S : Setup V) (t : ℕ) (l : List (Event V (NamedObject V))) (n : M.N)
    -- `n` satisfies the node invariant
    (hInv : M.nodeInv S.C S.P S.X n)
    -- `n`'s clock is at most `t`
    (hle : n.t ≤ (t : Int))
    -- every restart of the list is to the reading `t`
    (hrt : ∀ (u : V) (tRestart : ℕ) (keep : Bool), Event.restart u tRestart keep ∈ l → tRestart = t) :
    M.nodeInv S.C S.P S.X (l.foldl (applyEvent M S t) n) ∧
      (l.foldl (applyEvent M S t) n).v = n.v ∧ (l.foldl (applyEvent M S t) n).t ≤ (t : Int) := by
  induction l generalizing n with
  | nil => exact ⟨hInv, rfl, hle⟩
  | cons e l ih =>
      rw [List.foldl_cons]
      have hrt' : ∀ (u : V) (tRestart : ℕ) (keep : Bool), Event.restart u tRestart keep ∈ l →
          tRestart = t := fun u tR keep h => hrt u tR keep (List.mem_cons_of_mem _ h)
      have key : M.nodeInv S.C S.P S.X (applyEvent M S t n e) ∧
          (applyEvent M S t n e).v = n.v ∧ (applyEvent M S t n e).t ≤ (t : Int) := by
        cases e with
        | restart u tR keep =>
            have htR : tR = t := hrt u tR keep List.mem_cons_self
            subst htR
            obtain ⟨h1, h2, h3⟩ := F.nd.wake_nodeInv S.C S.P S.X n (tR : Int) hInv hle
            exact ⟨h1, h2, le_of_eq h3⟩
        | deliver u sm =>
            obtain ⟨h1, h2, h3⟩ := F.nd.receive_nodeInv S.C S.P S.X n sm.msg hInv
            refine ⟨h1, h2, ?_⟩
            show (M.receive S.C S.P S.X n sm.msg).t ≤ (t : Int)
            rw [h3]
            exact hle
        | tick u t' => exact ⟨hInv, rfl, hle⟩
        | other => exact ⟨hInv, rfl, hle⟩
      obtain ⟨h1, h2, h3⟩ := key
      obtain ⟨h4, h5, h6⟩ := ih _ h1 h3 hrt'
      exact ⟨h4, h5.trans h2, h6⟩

/-- **The carrier over deliveries only.** Over a range of steps with no tick and no restart of `v`,
`v`'s state at the later step is its state at the earlier one with the messages delivered to it in
between received in order (`st_eq_fold_nodeEvents`, `foldl_applyEvent_of_no_wake`).

The variables:
- `M`: the model; `F`: its facts;
- `x`: the trace; `R`: the run's facts; `v`: the validator; `j ≤ k`: the two steps; `hnotick`,
  `hnorestart`: no step from `j` to `k − 1` is a tick or a restart of `v`.

Read aloud: with no tick and no restart of `v` in between, `v`'s later state is its earlier state
with the deliveries in between received in order. -/
theorem st_eq_fold_deliveries (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {v : V} {j k : ℕ} (hjk : j ≤ k)
    -- no step from `j` to `k − 1` is a tick of `v`
    (hnotick : ∀ (l t' : ℕ), j ≤ l → l < k → x.lbl l ≠ Event.tick v t')
    -- no step from `j` to `k − 1` is a restart of `v`
    (hnorestart : ∀ l : ℕ, j ≤ l → l < k →
      ∀ (tRestart : ℕ) (keep : Bool), x.lbl l ≠ Event.restart v tRestart keep) :
    x.st k v =
      ((Trace.nodeEvents x v j k).filterMap Event.deliveredMsg).foldl
        (fun n sm => M.receive S.C S.P S.X n sm.msg) (x.st j v) := by
  rw [(st_eq_fold_nodeEvents M F) x R 0 hjk hnotick]
  exact (foldl_applyEvent_of_no_wake M F) S 0 _ _ (wake_not_mem_nodeEvents x v hnorestart)

/-- From `v`'s state at the step `j` to its state before `t`, a present `awakeSince` is kept when no
step in between is `v`'s wake (`step_keeps_awakeSince`).

The variables:
- `M`: the model; `F`: its facts;
- `x`: the trace; `R`: the run's facts; `E`: the environment's facts; `j`: the step; `t`: the time;
  `v`: the validator; `τ`: the stored time.

Read aloud: with no wake of `v` in between, the time `v` has been awake since is kept. -/
theorem awakeSince_keep_of_no_wake (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {j t : ℕ} {v : V} (hj : j ≤ x.stepBefore t)
    -- no step from `j` to the step before `t` is `v`'s wake
    (hno : ∀ m, j ≤ m → m < x.stepBefore t → (∀ (tRestart : ℕ) (keep : Bool), x.lbl m ≠ Event.restart v tRestart keep)) (τ : Time)
    (hτ : (x.st j v).awakeSince = some τ) : (x.stateBefore t v).awakeSince = some τ :=
  GoldilocksCorrectness.Proofs.Executions.rel_of_forall_step
    (fun n n' : M.N => ∀ τ : Time, n.awakeSince = some τ → n'.awakeSince = some τ)
    (fun _ _ h => h) (fun _ _ _ h h' τ hτ => h' τ (h τ hτ)) (fun i => x.st i v) hj
    (fun m hm1 hm2 τ hτ => (step_keeps_awakeSince M F) x R E m v (hno m hm1 hm2) τ hτ) τ hτ

/-- After `v`'s tick to `s`, no step at a real time at most `t` is `v`'s restart while `v` is awake
after every step whose real time is in `[s − ΔClockAhead, t]`: the tick is at a real time at least
`s − ΔClockAhead` (`time_tickStep`), and a restart is by a validator not awake at its step.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the trace; `R`: the run's facts; `E`: the environment's facts; `s`: the clock value of the
  tick; `t`: the real time; `v`: the validator; `m`: the step.

Read aloud: a validator that stays awake does not wake again after its tick. -/
theorem no_wake_after_tick (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {s t : ℕ} {v : V} (hk : ∃ i : ℕ, x.lbl i = Event.tick v s)
    -- `v` is awake after every step whose real time is in `[s − ΔClockAhead, t]`
    (hAwake : v ∈ A.awakeThroughout x ((s : ℝ) - ΔClockAhead) t) {m : ℕ}
    (hm1 : x.tickStep v s < m) (hm2 : x.time m ≤ t) :
    (∀ (tRestart : ℕ) (keep : Bool), x.lbl m ≠ Event.restart v tRestart keep) := by
  intro tR keep hl
  have hms : (s : ℝ) - ΔClockAhead ≤ x.time m :=
    le_trans (E.time_tickStep hk).1 ((time_mono M) x R hm1.le)
  exact (E.restart_crashed m v tR keep hl).1 (Activity.mem_awake_of_mem_awakeThroughout_of_time (fun _ _ h => (time_mono M) x R h) hAwake hms hm2)

end Steps

/-! ## The wake rule -/

section WakeRule

variable {S : Setup V} {A : Activity V}

/-- No step before `x.stepBefore t` is the wake of a validator awake at every time from `0` to `t`:
a wake is at a step whose time is at least `1` (`EnvFacts.wake_time_pos`), and its validator enters
the active set at that time, while `v` is awake at the time before.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `t`: the time; `v`: the validator; `m`: the step.

Read aloud: a validator awake from the start does not wake before `t`. -/
theorem no_wake_before_of_awake_from_zero (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) {t : ℕ} {v : V}
    -- `v` is awake at every time from `0` to `t`
    (hAwake : v ∈ A.awakeThroughout x 0 t) {m : ℕ}
    (hm : m < x.stepBefore t) : (∀ (tRestart : ℕ) (keep : Bool), x.lbl m ≠ Event.restart v tRestart keep) := by
  intro tR keep hl
  have h1 := ((lt_stepBefore_iff M) x R E).1 hm
  have h2 := (time_le_succ M) x R m
  exact (E.restart_crashed m v tR keep hl).1
    (Activity.mem_awake_of_mem_awakeThroughout_of_time (fun _ _ h => (time_mono M) x R h) hAwake
      (by simpa using (time_nonneg M) x R m) (by linarith))

/-- A validator awake after every step at a real time at most `t + ΔClockBehind` starts its tick to
`t` with the initial `awakeSince`, `proposal_window_start S.C 0`: that tick is at a real time at most
`t + ΔClockBehind` (`time_tickStep`), so no step before it is its restart, and every step keeps the
initial value; with no tick to `t`, the tick input is the initial state.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `t`: the clock value; `v`:
  the validator.

Read aloud: a validator awake from the start has been awake since the start. -/
theorem awakeSince_of_awake_all (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) {t : ℕ} {v : V}
    -- `v` is awake after every step at a real time at most `t + ΔClockBehind`
    (hall : ∀ i : ℕ, x.time i ≤ (t : ℝ) + ΔClockBehind → v ∈ A.awake i) :
    (x.tickInput v t).awakeSince = some (proposal_window_start S.C 0) := by
  have h0 : (x.st 0 v).awakeSince = some (proposal_window_start S.C 0) := by
    rw [(getElem_zero_st M F) x R, F.init.initial_awakeSince S.C v,
      GoldilocksCorrectness.Record.Proofs.Routines.proposal_window_start_zero_eq]
  unfold Trace.tickInput
  by_cases hex : ∃ i : ℕ, x.lbl i = Event.tick v t
  · have htk := (E.time_tickStep hex).2
    exact (awakeSince_kept_of_awake_steps M F) x R E (Nat.zero_le _)
      (fun i _ hi => hall i (by have := (time_mono M) x R hi.le; linarith)) h0
  · unfold Trace.tickStep
    rw [dif_neg hex]
    exact h0

/-- A validator awake at every real time from `0` to `t + ΔClockBehind` starts its tick to `t` with
the initial `awakeSince`, `proposal_window_start S.C 0` (`awakeSince_of_awake_all`).

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `t`: the clock value; `v`: the validator.

Read aloud: a validator awake from the start has been awake since the start. -/
theorem awakeSince_of_awake_from_zero (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) {t : ℕ} {v : V}
    -- `v` is awake at every real time from `0` to `t + ΔClockBehind`
    (hAwake : v ∈ A.awakeThroughout x 0 ((t : ℝ) + ΔClockBehind)) :
    (x.tickInput v t).awakeSince =
      some (proposal_window_start S.C 0) := by
  exact (awakeSince_of_awake_all M F) x R E fun i hi =>
    Activity.mem_awake_of_mem_awakeThroughout_of_time (fun _ _ h => (time_mono M) x R h) hAwake
      (by simpa using (time_nonneg M) x R i) hi

/-- A validator that ticks to `t` at some step, whose tick to `t` starts with
`awakeSince = some τ`, has `τ` the initial value and has been awake after every step up to that tick,
or ticked to the reading `τ` at a step `k₁` before that tick, after its last restart, and has been
awake after every step from `k₁` to that tick. A restart clears `awakeSince`, and the first tick after it writes its
reading; a validator that becomes awake was restarted.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `t`: the reading of the
  tick; `hex`: some step is `v`'s tick to `t`; `v`: the validator; `τ`: the stored time; `k₁`, `τ'`:
  the step and the reading of the tick that wrote `τ`.

Read aloud: a validator whose tick says "awake since `τ`" ticked to `τ` after its last restart, or
was never restarted, and stayed up to this tick. -/
theorem awake_of_tickInput_awakeSince_of_tick (x : Trace V (NamedObject V) M.N)
    (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) {t : ℕ} {v : V}
    {τ : Time} (hex : ∃ i : ℕ, x.lbl i = Event.tick v t)
    (hτ : (x.tickInput v t).awakeSince = some τ) :
    (τ = proposal_window_start S.C 0 ∧ ∀ i : ℕ, i ≤ x.tickStep v t → v ∈ A.awake i) ∨
      ∃ k₁ τ' : ℕ, k₁ < x.tickStep v t ∧ x.lbl k₁ = Event.tick v τ' ∧ (τ' : Int) = τ ∧
        ∀ i : ℕ, k₁ ≤ i → i ≤ x.tickStep v t → v ∈ A.awake i := by
  classical
  have hlk := x.lbl_tickStep hex
  have hvk : v ∈ A.awake (x.tickStep v t) :=
    Activity.mem_awake_of_mem_active (E.tick_active _ v t hlk).1
  unfold Trace.tickInput at hτ
  generalize hkdef : x.tickStep v t = k at hlk hvk hτ ⊢
  by_cases hr : ∃ r : ℕ, r < k ∧ ∃ (tR : ℕ) (keep : Bool), x.lbl r = Event.restart v tR keep
  · -- the last restart of `v` before `k`, at `r₀`
    obtain ⟨r₀, ⟨hr₀k, tR₀, keep₀, hl₀⟩, hmax⟩ : ∃ r₀ : ℕ,
        (r₀ < k ∧ ∃ (tR : ℕ) (keep : Bool), x.lbl r₀ = Event.restart v tR keep) ∧
        ∀ r' : ℕ, r₀ < r' → r' ≤ k →
          ¬ (r' < k ∧ ∃ (tR : ℕ) (keep : Bool), x.lbl r' = Event.restart v tR keep) := by
      obtain ⟨r, hr⟩ := hr
      exact ⟨Nat.findGreatest (fun r => r < k ∧ ∃ (tR : ℕ) (keep : Bool),
          x.lbl r = Event.restart v tR keep) k,
        Nat.findGreatest_spec (P := fun r => r < k ∧ ∃ (tR : ℕ) (keep : Bool),
          x.lbl r = Event.restart v tR keep) (le_of_lt hr.1) hr,
        fun r' h1 h2 => Nat.findGreatest_is_greatest h1 h2⟩
    -- `v` is awake after every step from `r₀ + 1` to `k`
    have hawk : ∀ i : ℕ, r₀ + 1 ≤ i → i ≤ k → v ∈ A.awake i := by
      intro i hi1 hi2
      by_contra hni
      obtain ⟨m, hm1, hm2, tR, keep, hm⟩ := (exists_restart_of_not_awake M) x E hi2 hni hvk
      exact hmax m (by omega) hm2.le ⟨hm2, tR, keep, hm⟩
    -- the first tick of `v` after `r₀`, at `k₁ ≤ k`
    have hQ : ∃ j : ℕ, r₀ < j ∧ j ≤ k ∧ ∃ t' : ℕ, x.lbl j = Event.tick v t' :=
      ⟨k, hr₀k, le_rfl, t, hlk⟩
    obtain ⟨k₁, ⟨hk₁1, hk₁2, τ', hl₁⟩, hmin⟩ : ∃ k₁ : ℕ,
        (r₀ < k₁ ∧ k₁ ≤ k ∧ ∃ t' : ℕ, x.lbl k₁ = Event.tick v t') ∧
        ∀ j : ℕ, j < k₁ → ¬ (r₀ < j ∧ j ≤ k ∧ ∃ t' : ℕ, x.lbl j = Event.tick v t') :=
      ⟨Nat.find hQ, Nat.find_spec hQ, fun j hj => Nat.find_min hQ hj⟩
    -- `awakeSince` is absent from the restart to that tick
    have hnone : ∀ j : ℕ, r₀ + 1 ≤ j → j ≤ k₁ → (x.st j v).awakeSince = none := by
      intro j hj1 hj2
      induction j, hj1 using Nat.le_induction with
      | base => exact (wake_case_awakeSince M F) x R hl₀
      | succ j hj ih =>
          have ih' := ih (by omega)
          rcases (step_cases_per_step M F) x R E j v with h | ⟨t'', -, -, hl, -⟩ |
              ⟨sm, -, -, h⟩ | ⟨⟨tR, keep, hl⟩, -, -⟩
          · rw [h]
            exact ih'
          · exact absurd ⟨by omega, by omega, t'', hl⟩ (hmin j (by omega))
          · rw [h, (GoldilocksCorrectness.Record.Proofs.Routines.receive_awakeSince M F)]
            exact ih'
          · exact absurd (hawk j (by omega) (by omega)) (E.restart_crashed j v tR keep hl).1
    -- the tick at `k₁` records its reading
    obtain ⟨n', sent, hok, hst, -⟩ := R.tick k₁ v τ' hl₁
    have haw := (F.tk.tick_clock_validator_awakeSince S.C S.P S.X _ (τ' : Int) n' sent hok).2.2
    have hk₁s : (x.st (k₁ + 1) v).awakeSince = some (τ' : Int) := by
      rw [hst, haw, hnone k₁ (by omega) le_rfl]
    rcases Nat.lt_or_ge k₁ k with hlt | hge
    · have hkept := (awakeSince_kept_of_awake_steps M F) x R E (show k₁ + 1 ≤ k by omega)
        (fun i hi1 hi2 => hawk i (by omega) (by omega)) hk₁s
      have heq : some τ = some (τ' : Int) := hτ.symm.trans hkept
      exact Or.inr ⟨k₁, τ', hlt, hl₁, (Option.some.inj heq).symm, fun i h1 h2 => hawk i (by omega) h2⟩
    · rw [hnone k (by omega) (by omega)] at hτ
      cases hτ
  · -- no restart of `v` before `k`: `v` is awake at every step up to `k`, with the initial value
    have hall : ∀ i : ℕ, i ≤ k → v ∈ A.awake i := by
      intro i hi
      by_contra hni
      obtain ⟨m, -, hm2, tR, keep, hm⟩ := (exists_restart_of_not_awake M) x E hi hni hvk
      exact hr ⟨m, hm2, tR, keep, hm⟩
    have h0 : (x.st 0 v).awakeSince = some (proposal_window_start S.C 0) := by
      rw [(getElem_zero_st M F) x R, F.init.initial_awakeSince S.C v,
        GoldilocksCorrectness.Record.Proofs.Routines.proposal_window_start_zero_eq]
    have hkept := (awakeSince_kept_of_awake_steps M F) x R E (Nat.zero_le k)
      (fun i _ hi => hall i hi.le) h0
    exact Or.inl ⟨Option.some.inj (hτ.symm.trans hkept), hall⟩

/-- A validator whose tick to `t ≥ 1` starts with `awakeSince = some τ`, and that is active after
every step whose real time is in `[t − ΔClockAhead, t + ΔClockBehind]`, has `τ` the initial value
and has been awake after every step up to that tick, or ticked to the clock value `τ` at a step `k₁`
after its last restart and has been awake after every step from `k₁` to that tick.
`awake_of_tickInput_awakeSince_of_tick`, with the tick to `t` given by the validator's activity
through the clock value's window (`tick_of_mem_activeThroughout`).

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `t`: the clock value of
  the tick; `v`: the validator; `τ`: the stored time; `k₁`, `τ'`: the step and the clock value of
  the tick that wrote `τ`.

Read aloud: a validator whose tick says "awake since `τ`" ticked to `τ` after its last restart, or
was never restarted, and stayed up to this tick. -/
theorem awake_of_tickInput_awakeSince (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) {t : ℕ} {v : V}
    {τ : Time} (h1 : 1 ≤ t)
    (hτ : (x.tickInput v t).awakeSince = some τ)
    -- `v` is active after every step whose real time is in `[t − ΔClockAhead, t + ΔClockBehind]`
    (hv : v ∈ A.activeThroughout x ((t : ℝ) - ΔClockAhead) ((t : ℝ) + ΔClockBehind)) :
    (τ = proposal_window_start S.C 0 ∧ ∀ i : ℕ, i ≤ x.tickStep v t → v ∈ A.awake i) ∨
      ∃ k₁ τ' : ℕ, k₁ < x.tickStep v t ∧ x.lbl k₁ = Event.tick v τ' ∧ (τ' : Int) = τ ∧
        ∀ i : ℕ, k₁ ≤ i → i ≤ x.tickStep v t → v ∈ A.awake i := by
  obtain ⟨k₀, hk₀, -⟩ := E.tick_of_mem_activeThroughout (fun _ _ h => (time_mono M) x R h) hv le_rfl le_rfl h1
  exact (awake_of_tickInput_awakeSince_of_tick M F) x R E ⟨k₀, hk₀⟩ hτ

/-- A validator awake after every step up to its tick to `b` at the step `k'` ticks to `b` from a node
state awake since the initial time `proposal_window_start S.C 0`: no step up to that tick is its
restart, and every step keeps the initial value.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `b`: the tick's value;
  `v`: the validator; `k'`: the step of its tick to `b`.

Read aloud: a validator awake since the trace's start up to its tick to `b` has been awake since the
start at that tick. -/
theorem tickInput_awakeSince_of_awake_up_to_tick (x : Trace V (NamedObject V) M.N)
    (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) {b k' : ℕ} {v : V}
    (hk' : x.lbl k' = Event.tick v b) (h : ∀ i : ℕ, i ≤ k' → v ∈ A.awake i) :
    (x.tickInput v b).awakeSince = some (proposal_window_start S.C 0) := by
  have h0s : (x.st 0 v).awakeSince = some (proposal_window_start S.C 0) := by
    rw [(getElem_zero_st M F) x R, F.init.initial_awakeSince S.C v,
      GoldilocksCorrectness.Record.Proofs.Routines.proposal_window_start_zero_eq]
  unfold Trace.tickInput
  rw [E.tick_unique _ _ v b (x.lbl_tickStep ⟨k', hk'⟩) hk']
  exact (awakeSince_kept_of_awake_steps M F) x R E (Nat.zero_le k') (fun i _ hi => h i hi.le) h0s

end WakeRule

end GoldilocksCorrectness.Record.Proofs.Executions

