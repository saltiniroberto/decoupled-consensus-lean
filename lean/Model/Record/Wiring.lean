import Model.Record.Model
import Proofs.Claims.Projection

/-!
# The wiring over the record, and what one step does to a node state

The wired protocol `protocolOf` of a model `M : Model V`, the theorems saying what one step of the
sts framework does to a validator's node state, and the runs over the record (`Record.Event`,
`Record.Run`). The fold theorems `fold_actionEventsOf`, `fold_veventsOf` and `stateBeforeOf_runOfM`
relate a validator's own run to its node state in an execution.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts.Record

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open scoped DC

/-! ## The record's events and runs -/

/-- An event of a validator's run over the record: the validator enters the awake set at `t`, its
    clock ticks at `t`, or one object is delivered to it at `t`. -/
protected inductive Event (V : Type) where
  | wake (v : V) (t : DecoupledConsensusModel.Time)
  | tick (v : V) (t : DecoupledConsensusModel.Time)
  | deliver (v : V) (object : NamedObject V) (t : DecoupledConsensusModel.Time)
  deriving DecidableEq

namespace Event

variable {V : Type}

/-- The time of an event. -/
def time : Record.Event V → DecoupledConsensusModel.Time
  | .wake _ t => t
  | .tick _ t => t
  | .deliver _ _ t => t

/-- The validator of an event. -/
def node : Record.Event V → V
  | .wake v _ => v
  | .tick v _ => v
  | .deliver v _ _ => v

/-- The object an event delivers: the delivered object for a delivery, nothing for a wake or a tick. -/
def object? : Record.Event V → Option (NamedObject V)
  | .wake _ _ => none
  | .tick _ _ => none
  | .deliver _ object _ => some object

/-- The phase of an event within its time: `0` for a wake or a tick, `1` for a delivery. -/
def phase : Record.Event V → Nat
  | .wake _ _ => 0
  | .tick _ _ => 0
  | .deliver _ _ _ => 1

/-- The order key of an event: its time, then its phase, compared lexicographically. -/
def key (e : Record.Event V) : Lex (DecoupledConsensusModel.Time × Nat) := toLex (e.time, e.phase)

/-- A `NamedEvent` as an event of the record: the same tick, or the same delivery. -/
def ofVocabulary : NamedEvent V → Record.Event V
  | .tick v t => .tick v t
  | .deliver v o t => .deliver v o t

end Event

/-- A run over the record: an honest set, a horizon, and a list of events of the record, wake events
    included. -/
protected structure Run (V : Type) where
  honest : Finset V
  horizon : DecoupledConsensusModel.Time
  events : List (Record.Event V)

/-- A `NamedRun` as a run over the record: the same honest set and horizon, and its events embedded
    one for one, no wake among them. -/
def Run.ofVocabulary {V : Type} (rho : NamedRun V) : Record.Run V :=
  { honest := rho.honest, horizon := rho.horizon, events := rho.events.map Record.Event.ofVocabulary }

/-! ## The equations of the embedding -/

section OfVocabulary

variable {V : Type}

/-- The embedded tick is the record's tick. -/
@[record_ofVocabulary] theorem Event.ofVocabulary_tick (v : V) (t : DecoupledConsensusModel.Time) :
    Record.Event.ofVocabulary (Generic.Event.tick v t : NamedEvent V) = .tick v t := rfl

/-- The embedded delivery is the record's delivery. -/
@[record_ofVocabulary] theorem Event.ofVocabulary_deliver (v : V) (o : NamedObject V) (t : DecoupledConsensusModel.Time) :
    Record.Event.ofVocabulary (Generic.Event.deliver v o t : NamedEvent V) = .deliver v o t := rfl

/-- An embedded event keeps its time. -/
@[record_ofVocabulary] theorem Event.ofVocabulary_time (e : NamedEvent V) :
    (Record.Event.ofVocabulary e).time = NamedEvent.time e := by
  cases e <;> rfl

/-- An embedded event keeps its validator. -/
@[record_ofVocabulary] theorem Event.ofVocabulary_node (e : NamedEvent V) :
    (Record.Event.ofVocabulary e).node = NamedEvent.node e := by
  cases e <;> rfl

/-- An embedded event delivers the same object. -/
@[record_ofVocabulary] theorem Event.ofVocabulary_object? (e : NamedEvent V) :
    (Record.Event.ofVocabulary e).object? = NamedEvent.object? e := by
  cases e <;> rfl

/-- An embedded event keeps its phase. -/
@[record_ofVocabulary] theorem Event.ofVocabulary_phase (e : NamedEvent V) :
    (Record.Event.ofVocabulary e).phase = Generic.Event.phase e := by
  cases e <;> rfl

/-- An embedded event keeps its order key. -/
@[record_ofVocabulary] theorem Event.ofVocabulary_key (e : NamedEvent V) :
    (Record.Event.ofVocabulary e).key = Generic.Event.key e := by
  cases e <;> rfl

/-- Two events with the same embedding are the same event. -/
theorem Event.ofVocabulary_injective : Function.Injective (Record.Event.ofVocabulary (V := V)) := by
  intro a b h
  cases a <;> cases b <;> simp_all [Record.Event.ofVocabulary]

/-- The embedding never produces a wake event. -/
@[record_ofVocabulary] theorem Event.ofVocabulary_ne_wake (e : NamedEvent V) (v : V) (t : DecoupledConsensusModel.Time) :
    (Record.Event.ofVocabulary e = .wake v t) ↔ False := by
  cases e <;> simp [Record.Event.ofVocabulary]

/-- The embedded run's events are the run's events, embedded. -/
@[record_ofVocabulary] theorem Run.ofVocabulary_events (rho : NamedRun V) :
    (Run.ofVocabulary rho).events = rho.events.map Record.Event.ofVocabulary := rfl

/-- The embedded run's honest set is the run's honest set. -/
@[record_ofVocabulary] theorem Run.ofVocabulary_honest (rho : NamedRun V) :
    (Run.ofVocabulary rho).honest = rho.honest := rfl

/-- The embedded run's horizon is the run's horizon. -/
@[record_ofVocabulary] theorem Run.ofVocabulary_horizon (rho : NamedRun V) :
    (Run.ofVocabulary rho).horizon = rho.horizon := rfl

/-- An embedded event list is as long as the list. -/
@[record_ofVocabulary] theorem Event.map_ofVocabulary_length (l : List (NamedEvent V)) :
    (l.map Record.Event.ofVocabulary).length = l.length := List.length_map _

/-- The first `i` embedded events are the first `i` events, embedded. -/
@[record_ofVocabulary] theorem Event.map_ofVocabulary_take (l : List (NamedEvent V)) (i : Nat) :
    (l.map Record.Event.ofVocabulary).take i = (l.take i).map Record.Event.ofVocabulary :=
  (List.map_take ..).symm

/-- The embedded list holds a delivery at index `i` exactly when the list does. -/
@[record_ofVocabulary] theorem Event.map_ofVocabulary_getElem?_deliver (l : List (NamedEvent V))
    (i : Nat) (v : V) (o : NamedObject V) (t : DecoupledConsensusModel.Time) :
    (l.map Record.Event.ofVocabulary)[i]? = some (.deliver v o t) ↔
      l[i]? = some (Generic.Event.deliver v o t) := by
  rw [List.getElem?_map]
  cases h : l[i]? with
  | none => simp
  | some e => cases e <;> simp [Record.Event.ofVocabulary]

/-- The embedded list holds a tick at index `i` exactly when the list does. -/
@[record_ofVocabulary] theorem Event.map_ofVocabulary_getElem?_tick (l : List (NamedEvent V))
    (i : Nat) (v : V) (t : DecoupledConsensusModel.Time) :
    (l.map Record.Event.ofVocabulary)[i]? = some (.tick v t) ↔
      l[i]? = some (Generic.Event.tick v t) := by
  rw [List.getElem?_map]
  cases h : l[i]? with
  | none => simp
  | some e => cases e <;> simp [Record.Event.ofVocabulary]

/-- The embedded list holds no wake at any index. -/
@[record_ofVocabulary] theorem Event.map_ofVocabulary_getElem?_wake (l : List (NamedEvent V))
    (i : Nat) (v : V) (t : DecoupledConsensusModel.Time) :
    (l.map Record.Event.ofVocabulary)[i]? = some (.wake v t) ↔ False := by
  rw [List.getElem?_map]
  cases h : l[i]? with
  | none => simp
  | some e => cases e <;> simp [Record.Event.ofVocabulary]

/-- A delivery is among the embedded events exactly when it is among the events. -/
@[record_ofVocabulary] theorem Event.mem_map_ofVocabulary_deliver (l : List (NamedEvent V)) (v : V)
    (o : NamedObject V) (t : DecoupledConsensusModel.Time) :
    Record.Event.deliver v o t ∈ l.map Record.Event.ofVocabulary ↔
      (Generic.Event.deliver v o t : NamedEvent V) ∈ l := by
  rw [← Event.ofVocabulary_deliver]
  exact List.mem_map_of_injective Event.ofVocabulary_injective

/-- A tick is among the embedded events exactly when it is among the events. -/
@[record_ofVocabulary] theorem Event.mem_map_ofVocabulary_tick (l : List (NamedEvent V)) (v : V)
    (t : DecoupledConsensusModel.Time) :
    Record.Event.tick v t ∈ l.map Record.Event.ofVocabulary ↔
      (Generic.Event.tick v t : NamedEvent V) ∈ l := by
  rw [← Event.ofVocabulary_tick]
  exact List.mem_map_of_injective Event.ofVocabulary_injective

/-- No wake is among the embedded events. -/
@[record_ofVocabulary] theorem Event.mem_map_ofVocabulary_wake (l : List (NamedEvent V)) (v : V)
    (t : DecoupledConsensusModel.Time) :
    Record.Event.wake v t ∈ l.map Record.Event.ofVocabulary ↔ False := by
  simp only [List.mem_map, iff_false, not_exists, not_and]
  intro e _ h
  exact (Event.ofVocabulary_ne_wake e v t).1 h

end OfVocabulary

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The wiring, over the record -/

/-- The reactions validator `p`, holding node state `n`, may have to the event `e` at the clock
    reading `t`. At a tick whose reading is a whole multiple of `S.E.Δ`, one reaction per successful
    outcome of `M.tick`; at any other tick, the reaction that does nothing; on a delivery, one per
    successful outcome of `M.process` on the delivered object; on a wake, the reaction with node
    state `M.wake n` that sends nothing. -/
def reactionsOf (M : Model V) (S : Setup V) (p : V) (n : M.N) (t : Int)
    (e : Event V (NamedObject V) Empty) : Set (NodeStepResult M.N (NamedObject V)) :=
  match e with
  | .tick =>
      if t % S.E.Δ = 0 then
        { res | ∃ out, M.tick (Setup.alwaysAwake S) p n t ⇢ out ∧
            res = { state := out.1, send := (out.2 : Multiset (NamedObject V)) } }
      else { { state := n, send := 0 } }
  | .recv m =>
      { res | ∃ n', M.process (Setup.alwaysAwake S) n m.msg ⇢ n' ∧
          res = { state := n', send := relayedObjects m.msg } }
  | .wake => { { state := M.wake n, send := 0 } }
  | .custom ev => ev.elim

/-- The wired protocol of a model: every validator `v` starts from
    `M.initial (Setup.alwaysAwake S) v`, and a step is one of the reactions `reactionsOf M S`
    allows, or, when it allows none, leaves the node state unchanged and sends nothing. -/
def protocolOf (M : Model V) (S : Setup V) :
    Framework.StsMultisetLog.Protocol V (NamedObject V) M.N Empty where
  init v := M.initial (Setup.alwaysAwake S) v
  step p r _view n e res :=
    res ∈ reactionsOf M S p n (r : Int) e ∨
      (reactionsOf M S p n (r : Int) e = ∅ ∧ res = { state := n, send := 0 })
  total := by
    classical
    intro p r _view n e
    by_cases h : (reactionsOf M S p n (r : Int) e).Nonempty
    · obtain ⟨res, hres⟩ := h
      exact ⟨res, Or.inl hres⟩
    · exact ⟨{ state := n, send := 0 }, Or.inr ⟨Set.not_nonempty_iff_eq_empty.mp h, rfl⟩⟩
  enabled _ _ ev := ev.elim

/-- `pure a`, as a set of outcomes, returns `b` exactly when `b = a`. -/
theorem returns_pure {α : Type} (a b : α) : (pure a : DC.NDRE α) ⇢ b ↔ b = a := by
  simp only [Returns, ExceptT.run_pure, Set.pure_def]
  rw [Set.mem_singleton_iff, Except.ok.injEq]

/-- Every reaction of validator `p` to a wake in `protocolOf M S` has node state `M.wake n` and
    sends nothing. -/
theorem protocolOf_step_wake (M : Model V) (S : Setup V) {p : V} {r : Nat}
    {view : View V (NamedObject V)} {n : M.N} {res : NodeStepResult M.N (NamedObject V)}
    (h : (protocolOf M S).step p r view n .wake res) : res = { state := M.wake n, send := 0 } := by
  rcases h with h | ⟨h, -⟩
  · exact Set.mem_singleton_iff.mp h
  · exact absurd h (Set.singleton_ne_empty _)

/-- The node state validator `v`'s tick stage reads at a `tickAllAwake` step at time `t` from
    configuration `c`: `M.wake` of `v`'s node state when `v` is awake and not adversarial at `t` and
    asleep at `t - 1`, `v`'s node state otherwise. -/
def wakeStage (M : Model V) (Sched : Schedule V) (t : Int)
    (c : Config V (NamedObject V) M.N) (v : V) : M.N :=
  if v ∈ (Sched.awake t \ Sched.adv t) \ Sched.awake (t - 1) then M.wake c[v].st else c[v].st

/-- At a natural time `t`, `wakeStage` applies `M.wake` exactly when `v` is in `entrants Sched t`. -/
theorem wakeStage_coe (M : Model V) (Sched : Schedule V) (t : Nat)
    (c : Config V (NamedObject V) M.N) (v : V) :
    wakeStage M Sched (t : Int) c v = if v ∈ entrants Sched t then M.wake c[v].st else c[v].st :=
  rfl

/-- The node state the wake stage of a `tickAllAwake t` step hands to `v`'s tick stage is
    `wakeStage M Sched t c v`. -/
theorem wakeStage_of_TickAllAwakeWake (M : Model V) (S : Setup V) (Sched : Schedule V) {t : Nat}
    {c : Config V (NamedObject V) M.N} {v : V} {w : NodeStepResult M.N (NamedObject V)}
    (hw : TickAllAwakeWake (protocolOf M S) Sched t c v w) :
    w.state = wakeStage M Sched (t : Int) c v := by
  unfold TickAllAwakeWake at hw
  unfold wakeStage
  by_cases he : v ∈ entrants Sched t
  · rw [if_pos he] at hw
    have he' : v ∈ (Sched.awake (t : Int) \ Sched.adv (t : Int)) \ Sched.awake ((t : Int) - 1) := he
    rw [if_pos he']
    rw [protocolOf_step_wake M S hw]
  · rw [if_neg he] at hw
    have he' : v ∉ (Sched.awake (t : Int) \ Sched.adv (t : Int)) \ Sched.awake ((t : Int) - 1) := he
    rw [if_neg he', hw]

/-- After validator `p`'s reaction to a tick at reading `r` in `protocolOf M S`, either `r` is a
    whole multiple of `S.E.Δ` and the node state is the first component of an answer of `M.tick`
    from `n` at `r`, or the node state is `n` and either `r` is not a whole multiple of `S.E.Δ` or
    `M.tick` from `n` at `r` returns nothing. -/
theorem protocolOf_step_tick (M : Model V) (S : Setup V) {p : V} {r : Nat}
    {view : View V (NamedObject V)} {n : M.N} {res : NodeStepResult M.N (NamedObject V)}
    (h : (protocolOf M S).step p r view n .tick res) :
    ((r : Int) % S.E.Δ = 0 ∧
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) p n (r : Int) ⇢ out ∧ res.state = out.1) ∨
    ((¬ (r : Int) % S.E.Δ = 0 ∨
        ∀ out : M.N × List (NamedObject V), ¬ M.tick (Setup.alwaysAwake S) p n (r : Int) ⇢ out) ∧
      res.state = n) := by
  by_cases hp : (r : Int) % S.E.Δ = 0
  · rcases h with h | ⟨hempty, h⟩
    · simp only [reactionsOf, if_pos hp, Set.mem_setOf_eq] at h
      obtain ⟨out, hout, hres⟩ := h
      exact Or.inl ⟨hp, out, hout, by rw [hres]⟩
    · refine Or.inr ⟨Or.inr fun out hout => ?_, by rw [h]⟩
      have hmem : ({ state := out.1, send := (out.2 : Multiset (NamedObject V)) } :
          NodeStepResult M.N (NamedObject V)) ∈ reactionsOf M S p n (r : Int) .tick := by
        simp only [reactionsOf, if_pos hp, Set.mem_setOf_eq]
        exact ⟨out, hout, rfl⟩
      rw [hempty] at hmem
      exact hmem
  · refine Or.inr ⟨Or.inl hp, ?_⟩
    rcases h with h | ⟨-, h⟩
    · simp only [reactionsOf, if_neg hp, Set.mem_singleton_iff] at h
      rw [h]
    · rw [h]

/-- After validator `p`'s reaction to the delivery of `m` in `protocolOf M S`, the node state is an
    answer of `M.process` on `n` and `m.msg`, or that receipt returns nothing and the node state is
    `n`. -/
theorem protocolOf_step_recv (M : Model V) (S : Setup V) {p : V} {r : Nat}
    {view : View V (NamedObject V)} {n : M.N} {m : SignedMsg V (NamedObject V)}
    {res : NodeStepResult M.N (NamedObject V)}
    (h : (protocolOf M S).step p r view n (.recv m) res) :
    M.process (Setup.alwaysAwake S) n m.msg ⇢ res.state ∨
    ((∀ n' : M.N, ¬ M.process (Setup.alwaysAwake S) n m.msg ⇢ n') ∧ res.state = n) := by
  rcases h with h | ⟨hempty, h⟩
  · simp only [reactionsOf, Set.mem_setOf_eq] at h
    obtain ⟨n', hn', hres⟩ := h
    exact Or.inl (by rw [hres]; exact hn')
  · refine Or.inr ⟨fun n' hn' => ?_, by rw [h]⟩
    have hmem : ({ state := n', send := relayedObjects m.msg } :
        NodeStepResult M.N (NamedObject V)) ∈ reactionsOf M S p n (r : Int) (.recv m) := by
      simp only [reactionsOf, Set.mem_setOf_eq]
      exact ⟨n', hn', rfl⟩
    rw [hempty] at hmem
    exact hmem

/-! ## What one step of the sts framework does to one validator's node state -/

/-- In the first configuration of an execution of `protocolOf M S`, validator `v`'s node state is
    `M.initial (Setup.alwaysAwake S) v`. -/
theorem st_zero (M : Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocolOf M S) Sched) (v : V) :
    x[0][v].st = M.initial (Setup.alwaysAwake S) v := by
  obtain ⟨-, hn, -⟩ := x.init
  show (x.cfg 0)[v].st = M.initial (Setup.alwaysAwake S) v
  rw [hn v]
  rfl

/-- If step `k` delivers `sm` to `w`, then `w`'s node state after the step is an answer of
    `M.process` on its node state before the step and the delivered object, or that receipt returns
    nothing and the node state is unchanged. -/
theorem st_succ_of_deliver (M : Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocolOf M S) Sched) {k : Nat} {w : V}
    {sm : SignedMsg V (NamedObject V)} (hl : x.lbl k = AtomicAction.deliver w sm) :
    M.process (Setup.alwaysAwake S) (x[k][w].st) sm.msg ⇢ x[k + 1][w].st ∨
    ((∀ n' : M.N, ¬ M.process (Setup.alwaysAwake S) (x[k][w].st) sm.msg ⇢ n') ∧
      x[k + 1][w].st = x[k][w].st) := by
  have hs : AtomicStep (protocolOf M S) Sched (x.lbl k) x[k] x[k + 1] := x.step k
  rw [hl] at hs
  obtain ⟨-, hns⟩ := hs
  have hstep : NodeStep (protocolOf M S) w (.recv sm) (receive w sm x[k]) x[k + 1] := hns
  have hst : (receive w sm x[k])[w].st = x[k][w].st := by simp [receive]
  have hres := hstep.1
  rw [hst] at hres
  have h2 : x[k + 1][w].st = (extract w (receive w sm x[k]) x[k + 1]).state := rfl
  rw [h2]
  exact protocolOf_step_recv M S hres

/-- A delivery step to `p` leaves the entry of every other validator `w` unchanged. -/
theorem getElem_succ_of_deliver_ne (M : Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocolOf M S) Sched) {k : Nat} {p w : V}
    {sm : SignedMsg V (NamedObject V)} (hl : x.lbl k = AtomicAction.deliver p sm)
    (hne : p ≠ w) : x[k + 1][w] = x[k][w] := by
  have hs : AtomicStep (protocolOf M S) Sched (x.lbl k) x[k] x[k + 1] := x.step k
  rw [hl] at hs
  obtain ⟨-, hns⟩ := hs
  have hstep : NodeStep (protocolOf M S) p (.recv sm) (receive p sm x[k]) x[k + 1] := hns
  rw [hstep.other w (fun h => hne h.symm)]
  simp only [receive, Config.setNode_apply, if_neg hne]

/-- An adversarial step leaves every validator's entry of the configuration unchanged. -/
theorem getElem_succ_of_adversarial (M : Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocolOf M S) Sched) {k : Nat} {p w : V} {m : NamedObject V}
    (hl : x.lbl k = AtomicAction.adversarial p m) : x[k + 1][w] = x[k][w] := by
  have hs : AtomicStep (protocolOf M S) Sched (x.lbl k) x[k] x[k + 1] := x.step k
  rw [hl] at hs
  rw [hs.2]; rfl

/-- A forward step leaves every validator's entry of the configuration unchanged. -/
theorem getElem_succ_of_forward (M : Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocolOf M S) Sched) {k : Nat} {p w : V}
    {m : SignedMsg V (NamedObject V)}
    (hl : x.lbl k = AtomicAction.forward p m) : x[k + 1][w] = x[k][w] := by
  have hs : AtomicStep (protocolOf M S) Sched (x.lbl k) x[k] x[k + 1] := x.step k
  rw [hl] at hs
  rw [hs.2]; rfl

/-- The wake stage of a `tickAllAwake` step leaves `v` with `M.wake` of its node state, or its node
    state. -/
private theorem wake_state (M : Model V) (S : Setup V) (Sched : Schedule V) {t : Nat}
    {c : Config V (NamedObject V) M.N} {v : V} {res : NodeStepResult M.N (NamedObject V)}
    (hww : TickAllAwakeWake (protocolOf M S) Sched t c v res) :
    res.state = M.wake c[v].st ∨ res.state = c[v].st := by
  unfold TickAllAwakeWake at hww
  by_cases he : v ∈ entrants Sched t
  · rw [if_pos he] at hww
    rw [protocolOf_step_wake M S hww]
    exact Or.inl rfl
  · rw [if_neg he] at hww
    rw [hww]
    exact Or.inr rfl

/-- After one step, `v`'s node state is its node state before the step, or `M.wake` of it, or the
    first component of an answer of `M.tick` on it or on `M.wake` of it, or an answer of `M.process`
    on it. -/
theorem st_succ_cases (M : Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocolOf M S) Sched) (v : V) (i : Nat) :
    x[i + 1][v].st = x[i][v].st ∨
    x[i + 1][v].st = M.wake (x[i][v].st) ∨
    (∃ (t : Int) (out : M.N × List (NamedObject V)),
      (M.tick (Setup.alwaysAwake S) v (x[i][v].st) t ⇢ out ∨
        M.tick (Setup.alwaysAwake S) v (M.wake (x[i][v].st)) t ⇢ out) ∧
      x[i + 1][v].st = out.1) ∨
    (∃ o : NamedObject V, M.process (Setup.alwaysAwake S) (x[i][v].st) o ⇢ x[i + 1][v].st) := by
  have hs : AtomicStep (protocolOf M S) Sched (x.lbl i) x[i] x[i + 1] := x.step i
  cases hl : x.lbl i with
  | tickAllAwake t =>
      rw [hl] at hs
      obtain ⟨-, w', tk, hwake, htick, hc⟩ := hs
      by_cases hv : v ∈ Sched.awake (t : Int) \ Sched.adv (t : Int)
      · have hx1 : x[i + 1][v].st = (tk v).state := by
          have h2 : x[i + 1][v] = (tickAllAwakeUpdate Sched t x[i] w' tk)[v] := by rw [hc]
          rw [h2, tickAllAwakeUpdate_getElem_awake (Finset.mem_sdiff.1 hv).1
            (Finset.mem_sdiff.1 hv).2]
        have htk := protocolOf_step_tick M S (htick v hv)
        rcases wake_state M S Sched (hwake v) with hwst | hwst
        · rw [hwst] at htk
          rcases htk with ⟨-, out, hout, hst⟩ | ⟨-, hst⟩
          · exact Or.inr (Or.inr (Or.inl ⟨(t : Int), out, Or.inr hout, by rw [hx1, hst]⟩))
          · exact Or.inr (Or.inl (by rw [hx1, hst]))
        · rw [hwst] at htk
          rcases htk with ⟨-, out, hout, hst⟩ | ⟨-, hst⟩
          · exact Or.inr (Or.inr (Or.inl ⟨(t : Int), out, Or.inl hout, by rw [hx1, hst]⟩))
          · exact Or.inl (by rw [hx1, hst])
      · refine Or.inl ?_
        have h2 : x[i + 1][v] = (tickAllAwakeUpdate Sched t x[i] w' tk)[v] := by rw [hc]
        rw [h2]
        by_cases haw : v ∈ Sched.awake (t : Int)
        · have hadv : v ∈ Sched.adv (t : Int) := by
            by_contra hn; exact hv (Finset.mem_sdiff.2 ⟨haw, hn⟩)
          exact (tickAllAwakeUpdate_getElem_adv hadv).1
        · rw [tickAllAwakeUpdate_getElem_asleep haw]
  | deliver p m =>
      by_cases hp : p = v
      · subst hp
        rcases st_succ_of_deliver M S Sched x hl with h | ⟨-, h⟩
        · exact Or.inr (Or.inr (Or.inr ⟨m.msg, h⟩))
        · exact Or.inl h
      · exact Or.inl (by rw [getElem_succ_of_deliver_ne M S Sched x hl hp])
  | custom _ ev => exact ev.elim
  | adversarial p m => exact Or.inl (by rw [getElem_succ_of_adversarial M S Sched x hl])
  | forward p m => exact Or.inl (by rw [getElem_succ_of_forward M S Sched x hl])

/-- A property of node states that holds of every initial node state and is kept by `M.wake`, by
    every answer of `M.tick` and by every answer of `M.process` holds of every validator's node
    state in every configuration of the execution. -/
theorem inv_sts (M : Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocolOf M S) Sched) (P : M.N → Prop)
    (h0 : ∀ v : V, P (M.initial (Setup.alwaysAwake S) v))
    (hw : ∀ n : M.N, P n → P (M.wake n))
    (ht : ∀ (v : V) (n : M.N) (t : Int) (out : M.N × List (NamedObject V)),
      M.tick (Setup.alwaysAwake S) v n t ⇢ out → P n → P out.1)
    (hp : ∀ (n : M.N) (o : NamedObject V) (n' : M.N),
      M.process (Setup.alwaysAwake S) n o ⇢ n' → P n → P n') :
    ∀ (i : Nat) (v : V), P (x[i][v].st) := by
  intro i v
  induction i with
  | zero => rw [st_zero M S Sched x v]; exact h0 v
  | succ i ih =>
      rcases st_succ_cases M S Sched x v i with h | h | ⟨t, out, hres | hres, h⟩ | ⟨o, h⟩
      · rw [h]; exact ih
      · rw [h]; exact hw _ ih
      · rw [h]; exact ht v _ t out hres ih
      · rw [h]; exact ht v _ t out hres (hw _ ih)
      · exact hp _ o _ h ih

/-- Real time never decreases along an execution. -/
theorem time_mono (M : Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocolOf M S) Sched) {i n : Nat} (h : i ≤ n) :
    x[i].time ≤ x[n].time := by
  induction n, h using Nat.le_induction with
  | base => exact Nat.le_refl _
  | succ n h ih =>
      rcases atomic_time_stepwise x n with hstep | hstep <;> omega

/-- If step `k` is `tickAllAwake t`, then the real time of configuration `k` plus one is `t`, and
    the real time of configuration `k + 1` is `t`. -/
theorem tickAllAwake_time (M : Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocolOf M S) Sched) {k t : Nat}
    (hl : x.lbl k = AtomicAction.tickAllAwake t) :
    x[k].time + 1 = t ∧ x[k + 1].time = t := by
  have hs : AtomicStep (protocolOf M S) Sched (x.lbl k) x[k] x[k + 1] := x.step k
  rw [hl] at hs
  obtain ⟨hen, w, tk, -, -, hc⟩ := hs
  exact ⟨hen, by rw [hc]; rfl⟩

/-! ## The runs over the record -/

/-- The events validator `v`'s run records for one sts action at real time `now`. At
    `tickAllAwake t`: the wake event when `M.wakeEvents` and `v` is in `entrants Sched t`, then the
    tick event when `v` is awake and not adversarial at `t` and `t` is a whole multiple of `S.E.Δ`.
    At a delivery to `v`: the delivery event. Nothing otherwise. -/
def actionEventsOf (M : Model V) (S : Setup V) (Sched : Schedule V) (v : V) (now : Int) :
    AtomicAction V (NamedObject V) Empty → List (Record.Event V)
  | .tickAllAwake t =>
      (if M.wakeEvents = true ∧ v ∈ entrants Sched t then [Record.Event.wake v (t : Int)] else []) ++
      (if v ∈ Sched.awake (t : Int) \ Sched.adv (t : Int) ∧ (t : Int) % S.E.Δ = 0
        then [Record.Event.tick v (t : Int)] else [])
  | .deliver p m => if p = v then [Record.Event.deliver v m.msg now] else []
  | .custom _ ev => ev.elim
  | .adversarial _ _ => []
  | .forward _ _ => []

/-- An event of one step is the wake or the tick of a `tickAllAwake` step, or the delivery of a
    delivery step to the validator. -/
theorem mem_actionEventsOf_cases {M : Model V} {S : Setup V} {Sched : Schedule V} {v : V}
    {now : Int} {a : AtomicAction V (NamedObject V) Empty} {e : Record.Event V}
    (he : e ∈ actionEventsOf M S Sched v now a) :
    (∃ t : Nat, a = .tickAllAwake t ∧
        (e = Record.Event.wake v (t : Int) ∨ e = Record.Event.tick v (t : Int))) ∨
      ∃ (p : V) (m : SignedMsg V (NamedObject V)), a = .deliver p m ∧ p = v ∧
        e = Record.Event.deliver v m.msg now := by
  cases a with
  | tickAllAwake t =>
      refine Or.inl ⟨t, rfl, ?_⟩
      simp only [actionEventsOf, List.mem_append] at he
      rcases he with he | he
      · split at he
        · exact Or.inl (List.mem_singleton.1 he)
        · exact absurd he List.not_mem_nil
      · split at he
        · exact Or.inr (List.mem_singleton.1 he)
        · exact absurd he List.not_mem_nil
  | deliver p m =>
      simp only [actionEventsOf] at he
      split at he
      · exact Or.inr ⟨p, m, rfl, by assumption, List.mem_singleton.1 he⟩
      · exact absurd he List.not_mem_nil
  | custom _ ev => exact ev.elim
  | adversarial p m =>
      simp only [actionEventsOf] at he
      exact absurd he List.not_mem_nil
  | forward p m =>
      simp only [actionEventsOf] at he
      exact absurd he List.not_mem_nil

/-- `actionEventsOf` at `v` produces only events of `v`. -/
theorem node_of_mem_actionEventsOf {M : Model V} {S : Setup V} {Sched : Schedule V} {v : V}
    {now : Int} {a : AtomicAction V (NamedObject V) Empty} {e : Record.Event V}
    (he : e ∈ actionEventsOf M S Sched v now a) : e.node = v := by
  rcases mem_actionEventsOf_cases he with ⟨t, -, rfl | rfl⟩ | ⟨p, m, -, -, rfl⟩ <;> rfl

/-- An event of step `k` has the real time of configuration `k + 1`, which is at least that of
    configuration `k` and at most one more. -/
theorem time_of_mem_actionEventsOf (M : Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocolOf M S) Sched) (k : Nat) {v : V} {e : Record.Event V}
    (he : e ∈ actionEventsOf M S Sched v (x[k].time : Int) (x.lbl k)) :
    (x[k + 1].time : Int) = e.time ∧ (x[k].time : Int) ≤ e.time ∧
      e.time ≤ (x[k].time : Int) + 1 := by
  rcases mem_actionEventsOf_cases he with ⟨t, hl, he'⟩ | ⟨p, m, hl, -, rfl⟩
  · have hte : e.time = (t : Int) := by rcases he' with rfl | rfl <;> rfl
    obtain ⟨h1, h2⟩ := tickAllAwake_time M S Sched x hl
    have e1 : (x[k + 1].time : Int) = (t : Int) := by exact_mod_cast h2
    have e2 : (x[k].time : Int) + 1 = (t : Int) := by exact_mod_cast h1
    rw [hte]
    refine ⟨e1, ?_, ?_⟩ <;> linarith
  · have hs : AtomicStep (protocolOf M S) Sched (x.lbl k) x[k] x[k + 1] := x.step k
    rw [hl] at hs
    have h : x[k + 1].time = x[k].time := by rw [hs.2.2]; rfl
    show (x[k + 1].time : Int) = (x[k].time : Int) ∧ (x[k].time : Int) ≤ (x[k].time : Int) ∧
      (x[k].time : Int) ≤ (x[k].time : Int) + 1
    rw [h]; exact ⟨rfl, le_refl _, by linarith⟩

/-- The worlds one event can lead to from the world `w`. A wake at `v` replaces `v`'s node state by
    `M.wake` of it; a tick at `v` by the first component of an answer of `M.tick`; a delivery at `v`
    by an answer of `M.process` on the delivered object. When the routine returns nothing, the world
    is unchanged. -/
def worldStepOf (M : Model V) (S : Setup V) (w : V → M.N) : Record.Event V → DC.NDR (V → M.N)
  | .wake v _ => {Function.update w v (M.wake (w v))}
  | .tick v t =>
      { w' | (∃ out : M.N × List (NamedObject V),
                M.tick S v (w v) t ⇢ out ∧ w' = Function.update w v out.1) ∨
             ((∀ out : M.N × List (NamedObject V), ¬ M.tick S v (w v) t ⇢ out) ∧ w' = w) }
  | .deliver v o _ =>
      { w' | (∃ n' : M.N, M.process S (w v) o ⇢ n' ∧ w' = Function.update w v n') ∨
             ((∀ n' : M.N, ¬ M.process S (w v) o ⇢ n') ∧ w' = w) }

/-- The worlds reached by folding `worldStepOf` over the first `i` events of `rho`, from the world
    where every validator `v` holds `M.initial S v`. -/
def stateBeforeOf (M : Model V) (S : Setup V) (rho : Record.Run V) (i : Nat) :
    DC.NDR (V → M.N) :=
  (rho.events.take i).foldlM (worldStepOf M S) (fun v => M.initial S v)

/-- The events validator `v` contributes to its own run over the first `n` steps of the execution
    `x`, in step order. -/
def veventsOf (M : Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocolOf M S) Sched) (v : V) : Nat → List (Record.Event V)
  | 0 => []
  | n + 1 => veventsOf M S Sched x v n ++ actionEventsOf M S Sched v (x[n].time : Int) (x.lbl n)

/-- Validator `v`'s own run over the first `n` steps of the execution `x`: every validator is
    honest, the horizon is the real time of configuration `n`, and the events are
    `veventsOf M S Sched x v n`. -/
def runOfM (M : Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocolOf M S) Sched) (v : V) (n : Nat) : Record.Run V :=
  { honest := Finset.univ
    horizon := (x[n].time : Int)
    events := veventsOf M S Sched x v n }

/-- For a model that records its wakes or whose wake changes nothing, folding the wake part of a
    `tickAllAwake t` step's events onto a world holding `v`'s node state in `c` can reach a world
    holding `wakeStage M Sched t c v` at `v`. -/
private theorem fold_wakePartOf (M : Model V) (S : Setup V) (Sched : Schedule V)
    (hwe : M.wakeEvents = true ∨ ∀ n : M.N, M.wake n = n) (t : Nat)
    (c : Config V (NamedObject V) M.N) (v : V) (w : V → M.N) (hw : w v = c[v].st) :
    ∃ w₁ ∈ (if M.wakeEvents = true ∧ v ∈ entrants Sched t then [Record.Event.wake v (t : Int)]
        else []).foldlM (worldStepOf M S) w, w₁ v = wakeStage M Sched (t : Int) c v := by
  by_cases hk : M.wakeEvents = true ∧ v ∈ entrants Sched t
  · rw [if_pos hk]
    simp only [List.foldlM_cons, List.foldlM_nil, bind_pure]
    refine ⟨Function.update w v (M.wake (w v)), Set.mem_singleton _, ?_⟩
    rw [Function.update_self, hw, wakeStage_coe, if_pos hk.2]
  · rw [if_neg hk, List.foldlM_nil]
    refine ⟨w, Set.mem_singleton w, ?_⟩
    rw [hw, wakeStage_coe]
    by_cases he : v ∈ entrants Sched t
    · rw [if_pos he]
      rcases hwe with h | hid
      · exact absurd ⟨h, he⟩ hk
      · exact (hid _).symm
    · rw [if_neg he]

/-- For a model that records its wakes or whose wake changes nothing: if `w` holds at `v` the node
    state `v` holds after `i` steps, then folding step `i`'s events from `w` can reach a world
    holding at `v` the node state `v` holds after `i + 1` steps. -/
theorem fold_actionEventsOf (M : Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocolOf M S) Sched)
    (hwe : M.wakeEvents = true ∨ ∀ n : M.N, M.wake n = n) (v : V) (i : Nat)
    (w : V → M.N) (hw : w v = x[i][v].st) :
    ∃ w' ∈ (actionEventsOf M S Sched v (x[i].time : Int) (x.lbl i)).foldlM
        (worldStepOf M (Setup.alwaysAwake S)) w, w' v = x[i + 1][v].st := by
  have hs : AtomicStep (protocolOf M S) Sched (x.lbl i) x[i] x[i + 1] := x.step i
  cases hl : x.lbl i with
  | tickAllAwake t =>
      rw [hl] at hs
      obtain ⟨-, w', tk, hwake, htick, hc⟩ := hs
      simp only [actionEventsOf]
      rw [List.foldlM_append, Set.bind_def]
      obtain ⟨w₁, hw₁, hw₁v⟩ :=
        fold_wakePartOf M (Setup.alwaysAwake S) Sched hwe t x[i] v w hw
      suffices h : ∃ w'' ∈ (if v ∈ Sched.awake (t : Int) \ Sched.adv (t : Int) ∧
          (t : Int) % S.E.Δ = 0 then [Record.Event.tick v (t : Int)] else []).foldlM
            (worldStepOf M (Setup.alwaysAwake S)) w₁, w'' v = x[i + 1][v].st by
        obtain ⟨w'', h1, h2⟩ := h
        exact ⟨w'', Set.mem_biUnion hw₁ h1, h2⟩
      by_cases hv : v ∈ Sched.awake (t : Int) \ Sched.adv (t : Int)
      · have hwst : (w' v).state = w₁ v := by
          rw [hw₁v]; exact wakeStage_of_TickAllAwakeWake M S Sched (hwake v)
        have hx1 : x[i + 1][v].st = (tk v).state := by
          have h2 : x[i + 1][v] = (tickAllAwakeUpdate Sched t x[i] w' tk)[v] := by rw [hc]
          rw [h2, tickAllAwakeUpdate_getElem_awake (Finset.mem_sdiff.1 hv).1
            (Finset.mem_sdiff.1 hv).2]
        have htk := protocolOf_step_tick M S (htick v hv)
        rw [hwst] at htk
        by_cases hp : (t : Int) % S.E.Δ = 0
        · have hcond : v ∈ Sched.awake (t : Int) \ Sched.adv (t : Int) ∧
              (t : Int) % S.E.Δ = 0 := ⟨hv, hp⟩
          simp only [if_pos hcond, List.foldlM_cons, List.foldlM_nil, bind_pure]
          rcases htk with ⟨-, out, hout, hst⟩ | ⟨hno, hst⟩
          · refine ⟨Function.update w₁ v out.1, Or.inl ⟨out, hout, rfl⟩, ?_⟩
            rw [Function.update_self, hx1, hst]
          · have hno' : ∀ out : M.N × List (NamedObject V),
                ¬ M.tick (Setup.alwaysAwake S) v (w₁ v) (t : Int) ⇢ out :=
              hno.resolve_left (fun h => h hp)
            refine ⟨w₁, Or.inr ⟨hno', rfl⟩, ?_⟩
            rw [hx1, hst]
        · have hne : ¬ (v ∈ Sched.awake (t : Int) \ Sched.adv (t : Int) ∧
              (t : Int) % S.E.Δ = 0) := fun h => hp h.2
          simp only [if_neg hne, List.foldlM_nil]
          refine ⟨w₁, Set.mem_singleton w₁, ?_⟩
          rcases htk with ⟨h, -⟩ | ⟨-, hst⟩
          · exact absurd h hp
          · rw [hx1, hst]
      · have hne : ¬ (v ∈ Sched.awake (t : Int) \ Sched.adv (t : Int) ∧
            (t : Int) % S.E.Δ = 0) := fun h => hv h.1
        have hent : v ∉ entrants Sched t := fun h => by
          have h' : v ∈ (Sched.awake (t : Int) \ Sched.adv (t : Int)) \
              Sched.awake ((t : Int) - 1) := h
          exact hv (Finset.mem_sdiff.1 h').1
        rw [wakeStage_coe, if_neg hent] at hw₁v
        have hx1 : x[i + 1][v].st = x[i][v].st := by
          have h2 : x[i + 1][v] = (tickAllAwakeUpdate Sched t x[i] w' tk)[v] := by rw [hc]
          rw [h2]
          by_cases haw : v ∈ Sched.awake (t : Int)
          · have hadv : v ∈ Sched.adv (t : Int) := by
              by_contra hn; exact hv (Finset.mem_sdiff.2 ⟨haw, hn⟩)
            exact (tickAllAwakeUpdate_getElem_adv hadv).1
          · rw [tickAllAwakeUpdate_getElem_asleep haw]
        simp only [if_neg hne, List.foldlM_nil]
        exact ⟨w₁, Set.mem_singleton w₁, by rw [hw₁v, hx1]⟩
  | deliver p m =>
      by_cases hp : p = v
      · subst hp
        have hev : actionEventsOf M S Sched p (x[i].time : Int) (AtomicAction.deliver p m)
            = [Record.Event.deliver p m.msg (x[i].time : Int)] := by simp [actionEventsOf]
        rw [hev]
        simp only [List.foldlM_cons, List.foldlM_nil, bind_pure]
        rcases st_succ_of_deliver M S Sched x hl with h | ⟨hno, h⟩
        · refine ⟨Function.update w p (x[i + 1][p].st), Or.inl ⟨_, by rw [hw]; exact h, rfl⟩, ?_⟩
          rw [Function.update_self]
        · refine ⟨w, Or.inr ⟨by rw [hw]; exact hno, rfl⟩, ?_⟩
          rw [hw, h]
      · have hx1 : x[i + 1][v] = x[i][v] := getElem_succ_of_deliver_ne M S Sched x hl hp
        simp only [actionEventsOf, if_neg hp, List.foldlM_nil]
        exact ⟨w, Set.mem_singleton w, by rw [hw, hx1]⟩
  | custom _ ev => exact ev.elim
  | adversarial p m =>
      have hx1 : x[i + 1][v] = x[i][v] := getElem_succ_of_adversarial M S Sched x hl
      simp only [actionEventsOf, List.foldlM_nil]
      exact ⟨w, Set.mem_singleton w, by rw [hw, hx1]⟩
  | forward p m =>
      have hx1 : x[i + 1][v] = x[i][v] := getElem_succ_of_forward M S Sched x hl
      simp only [actionEventsOf, List.foldlM_nil]
      exact ⟨w, Set.mem_singleton w, by rw [hw, hx1]⟩

/-- For a model that records its wakes or whose wake changes nothing, folding `v`'s own events of
    the first `n` steps from the world where every validator `v'` holds
    `M.initial (Setup.alwaysAwake S) v'` can reach a world holding at `v` the node state `v` holds
    after `n` steps. -/
theorem fold_veventsOf (M : Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocolOf M S) Sched)
    (hwe : M.wakeEvents = true ∨ ∀ n : M.N, M.wake n = n) (v : V) (n : Nat) :
    ∃ w ∈ (veventsOf M S Sched x v n).foldlM (worldStepOf M (Setup.alwaysAwake S))
        (fun v' => M.initial (Setup.alwaysAwake S) v'), w v = x[n][v].st := by
  induction n with
  | zero =>
      exact ⟨fun v' => M.initial (Setup.alwaysAwake S) v', Set.mem_singleton _,
        (st_zero M S Sched x v).symm⟩
  | succ n ih =>
      obtain ⟨w, hw, hwv⟩ := ih
      obtain ⟨w', hw', hw'v⟩ := fold_actionEventsOf M S Sched x hwe v n w hwv
      refine ⟨w', ?_, hw'v⟩
      rw [show veventsOf M S Sched x v (n + 1)
            = veventsOf M S Sched x v n ++ actionEventsOf M S Sched v (x[n].time : Int) (x.lbl n)
          from rfl, List.foldlM_append, Set.bind_def]
      exact Set.mem_biUnion hw hw'

/-- For a model that records its wakes or whose wake changes nothing, among the worlds reached at
    the end of the run `runOfM M S Sched x v n`, one holds at `v` the node state `v` holds after `n`
    steps. -/
theorem stateBeforeOf_runOfM (M : Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocolOf M S) Sched)
    (hwe : M.wakeEvents = true ∨ ∀ n : M.N, M.wake n = n) (v : V) (n : Nat) :
    ∃ w ∈ stateBeforeOf M (Setup.alwaysAwake S) (runOfM M S Sched x v n)
        (veventsOf M S Sched x v n).length, w v = x[n][v].st := by
  unfold stateBeforeOf
  show ∃ w ∈ ((veventsOf M S Sched x v n).take (veventsOf M S Sched x v n).length).foldlM
      (worldStepOf M (Setup.alwaysAwake S)) (fun v' => M.initial (Setup.alwaysAwake S) v'),
      w v = x[n][v].st
  rw [List.take_length]
  exact fold_veventsOf M S Sched x hwe v n

end DecoupledConsensusModel.Sts.Record
