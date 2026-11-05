module
public import GoldilocksCorrectness.Record.ModelGoldilocks
public import GoldilocksCorrectness.Statements.Executions.WiringDefs

@[expose] public section

/-!
# A model's node under the sts framework

`protocolOf M S` is the node of the model `M` in the framework's shape, ticking at every reading:
the wiring `GoldilocksCorrectness.Wiring.protocol` with the model's `initial`, `tick`, `receive`,
`relayedObjects` and `wake` in place of the spec's. A tick step is any answer among the outcomes
of `M.tick`, or, only when no outcome answers, the state kept and nothing sent.

- `reactionsOf`: the set of reactions of a validator to an event;
- `protocolOf`: the node, with the step relation over `reactionsOf`;
- the reading lemmas `mem_reactionsOf_tick_iff`, `reactionsOf_tick_eq_empty_iff`,
  `step_tick_iff`, `step_recv_iff` and `step_wake_iff`;
- `reactionsOf_goldilocks` and `protocolOf_goldilocks`: at the spec's model, the reactions and
  the node are the library's.
-/

set_option autoImplicit false

namespace GoldilocksCorrectness.Record

open Framework.StsMultisetLog
open DC (DRE)
open Goldilocks (NamedObject RootOrder)
open Goldilocks.Sts (Setup)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- The reactions a validator holding the node state `n` of the model `M` may have to the event
`e` at the clock reading `t`, each an answer:

- `tick`: for every `.ok` outcome of `M.tick` at `t`, the node state it answers and the objects it
  broadcast, as a multiset;
- `recv m`: `M.receive` on the delivered object, re-sending `M.relayedObjects m.msg`;
- `wake`: `M.wake` at the reading `t`, nothing sent.

Read aloud: at a tick the validator takes any answer of its tick and sends what that answer
broadcast; on a delivery it processes the object and re-sends what the model relays; on a wake it
takes the model's state after a wake at the reading and sends nothing. -/
def reactionsOf (M : GoldilocksModel V) (S : Setup V) (n : M.N) (t : Int)
    (e : Event V (NamedObject V) Empty) : Set (NodeStepResult M.N (NamedObject V)) :=
  match e with
  | .tick =>
      { res | ∃ r ∈ M.tick S.C S.P S.X n t,
          ∃ p : M.N × List (NamedObject V),
            r = .ok p ∧ res = { state := p.1, send := (p.2 : Multiset (NamedObject V)) } }
  | .recv m =>
      { res | res = { state := M.receive S.C S.P S.X n m.msg, send := M.relayedObjects m.msg } }
  | .wake => { res | res = { state := M.wake n t, send := 0 } }
  | .custom ev => ev.elim

/-- The node of the model `M` in the framework's shape, ticking at every reading: every validator
`p` starts from `M.initial S.C p`, and a step is any reaction in `reactionsOf`, or, only when there
is none, keeping the state and sending nothing.

Read aloud: the model's node, run by the framework. -/
def protocolOf (M : GoldilocksModel V) (S : Setup V) :
    Framework.StsMultisetLog.Protocol V (NamedObject V) M.N Empty where
  init p := M.initial S.C p
  step _ r _view n e res :=
    res ∈ reactionsOf M S n (r : Int) e ∨
      (reactionsOf M S n (r : Int) e = ∅ ∧ res = { state := n, send := 0 })
  total := by
    classical
    intro _ r _view n e
    by_cases h : (reactionsOf M S n (r : Int) e).Nonempty
    · obtain ⟨res, hres⟩ := h
      exact ⟨res, Or.inl hres⟩
    · exact ⟨{ state := n, send := 0 },
        Or.inr ⟨Set.not_nonempty_iff_eq_empty.mp h, rfl⟩⟩
  enabled _ _ ev := ev.elim

/-! ## Reading a step -/

/-- A reaction to a tick is an `.ok` outcome of the model's tick, read as a step result.

The variables:
- `M`: the model; `S`: the setup; `n`: the node state; `t`: the clock reading; `res`: the step
  result. -/
theorem mem_reactionsOf_tick_iff (M : GoldilocksModel V) (S : Setup V) (n : M.N) (t : Int)
    (res : NodeStepResult M.N (NamedObject V)) :
    res ∈ reactionsOf M S n t .tick ↔
      ∃ (n' : M.N) (sent : List (NamedObject V)),
        .ok (n', sent) ∈ M.tick S.C S.P S.X n t ∧
          res = { state := n', send := (sent : Multiset (NamedObject V)) } := by
  simp only [reactionsOf, Set.mem_setOf_eq]
  constructor
  · rintro ⟨r, hr, ⟨n', sent⟩, rfl, rfl⟩
    exact ⟨n', sent, hr, rfl⟩
  · rintro ⟨n', sent, hr, rfl⟩
    exact ⟨_, hr, (n', sent), rfl, rfl⟩

/-- No reaction to a tick exactly when no outcome of the model's tick is an answer.

The variables:
- `M`: the model; `S`: the setup; `n`: the node state; `t`: the clock reading. -/
theorem reactionsOf_tick_eq_empty_iff (M : GoldilocksModel V) (S : Setup V) (n : M.N) (t : Int) :
    reactionsOf M S n t .tick = ∅ ↔
      ∀ p : M.N × List (NamedObject V), .ok p ∉ M.tick S.C S.P S.X n t := by
  constructor
  · intro h p hp
    have hmem : ({ state := p.1, send := (p.2 : Multiset (NamedObject V)) } :
        NodeStepResult M.N (NamedObject V)) ∈ reactionsOf M S n t .tick :=
      (mem_reactionsOf_tick_iff M S n t _).2 ⟨p.1, p.2, hp, rfl⟩
    rw [h] at hmem
    exact hmem
  · intro h
    ext res
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hres
    obtain ⟨n', sent, hr, -⟩ := (mem_reactionsOf_tick_iff M S n t res).1 hres
    exact h (n', sent) hr

/-- **Reading a tick step.** The step relation at `.tick` holds of `res` exactly when `res` is an
`.ok` outcome of the model's tick at the reading, as a step result, or no outcome of the tick is
an answer and `res` keeps the state and sends nothing.

The variables:
- `M`: the model; `S`: the setup; `p`: the validator; `r`: the reading; `view`: its view; `n`: its
  node state; `res`: the step result.

Read aloud: a tick step is an answer of the model's tick, or, only when the tick cannot answer,
the validator doing nothing. -/
theorem step_tick_iff (M : GoldilocksModel V) (S : Setup V) (p : V) (r : ℕ)
    (view : View V (NamedObject V)) (n : M.N) (res : NodeStepResult M.N (NamedObject V)) :
    (protocolOf M S).step p r view n .tick res ↔
      (∃ (n' : M.N) (sent : List (NamedObject V)),
        .ok (n', sent) ∈ M.tick S.C S.P S.X n (r : Int) ∧
          res = { state := n', send := (sent : Multiset (NamedObject V)) }) ∨
      ((∀ q : M.N × List (NamedObject V), .ok q ∉ M.tick S.C S.P S.X n (r : Int)) ∧
        res = { state := n, send := 0 }) := by
  show (res ∈ reactionsOf M S n (r : Int) .tick ∨
    (reactionsOf M S n (r : Int) .tick = ∅ ∧ res = { state := n, send := 0 })) ↔ _
  rw [mem_reactionsOf_tick_iff, reactionsOf_tick_eq_empty_iff]

/-- **Reading a delivery step**: the model's `receive` on the object, re-sending what the model's
`relayedObjects` gives.

The variables:
- `M`: the model; `S`: the setup; `p`: the validator; `r`: the reading; `view`: its view; `n`: its
  node state; `m`: the delivered message; `res`: the step result.

Read aloud: a delivery step processes the object and re-sends what the model relays. -/
theorem step_recv_iff (M : GoldilocksModel V) (S : Setup V) (p : V) (r : ℕ)
    (view : View V (NamedObject V)) (n : M.N) (m : SignedMsg V (NamedObject V))
    (res : NodeStepResult M.N (NamedObject V)) :
    (protocolOf M S).step p r view n (.recv m) res ↔
      res = { state := M.receive S.C S.P S.X n m.msg, send := M.relayedObjects m.msg } := by
  show (res ∈ reactionsOf M S n (r : Int) (.recv m) ∨
    (reactionsOf M S n (r : Int) (.recv m) = ∅ ∧ res = { state := n, send := 0 })) ↔ _
  constructor
  · rintro (h | ⟨h, -⟩)
    · exact h
    · exact absurd h (Set.Nonempty.ne_empty ⟨_, rfl⟩)
  · intro h
    exact Or.inl h

/-- **Reading a wake step**: the model's `wake`, nothing sent.

The variables:
- `M`: the model; `S`: the setup; `p`: the validator; `r`: the reading; `view`: its view; `n`: its
  node state; `res`: the step result.

Read aloud: a wake step takes the model's state after a wake at the reading and sends nothing. -/
theorem step_wake_iff (M : GoldilocksModel V) (S : Setup V) (p : V) (r : ℕ)
    (view : View V (NamedObject V)) (n : M.N) (res : NodeStepResult M.N (NamedObject V)) :
    (protocolOf M S).step p r view n .wake res ↔
      res = { state := M.wake n (r : Int), send := 0 } := by
  show (res ∈ reactionsOf M S n (r : Int) .wake ∨
    (reactionsOf M S n (r : Int) .wake = ∅ ∧ res = { state := n, send := 0 })) ↔ _
  constructor
  · rintro (h | ⟨h, -⟩)
    · exact h
    · exact absurd h (Set.Nonempty.ne_empty ⟨_, rfl⟩)
  · intro h
    exact Or.inl h

/-! ## At the spec's model -/

/-- At the spec's model, the reactions are the library's `GoldilocksCorrectness.Wiring.reactions`.

Read aloud: the spec's model reacts as the library's wiring does. -/
@[record_goldilocks]
theorem reactionsOf_goldilocks (S : Setup V) :
    GoldilocksCorrectness.Wiring.reactions S = reactionsOf (Model.goldilocks (V := V)) S := rfl

/-- At the spec's model, the node is the library's `GoldilocksCorrectness.Wiring.protocol`, so an
execution of one is an execution of the other.

Read aloud: the spec's model, run by the framework, is the library's wiring. -/
theorem protocolOf_goldilocks (S : Setup V) :
    protocolOf (Model.goldilocks (V := V)) S = GoldilocksCorrectness.Wiring.protocol S := rfl

end GoldilocksCorrectness.Record
