module
public import GoldilocksSts
public import GoldilocksCorrectness.Proofs.Routines.DREPost
public import GoldilocksCorrectness.Statements.Routines.ObjectDefs

@[expose] public section

/-!
# Goldilocks's node under the sts framework, ticking at every reading

A copy of the wiring `Goldilocks.Sts.protocol` (`experiments/goldilocks/GoldilocksSts.lean`) with
one change. The statements about executions read this copy; the original is not edited.

**The change.** The node's `tick` runs at every reading, not only at the readings that are whole
multiples of `S.C.Δ`.

**Why.** The node's clock `n.t` is set only by its tick, and every delivered block and Goldfish
vote is stamped with that clock. With ticks only at multiples of `Δ`, a validator that wakes
between two multiples receives its backlog against the clock of its last tick before it slept: an
object is stamped with an earlier time than the one it arrived at, and a block of the current
slot is refused by `block_admissible`'s test that the block's slot is not later than the node's
slot, and is never offered again. Ticking at every reading keeps the clock current.

**What does not change.** The setup `Setup`, the dispatch `receive` and the re-sent objects
`relayedObjects` are the original's, reused. The node's routines are unchanged: its duties test
their own times exactly, and the lock expiry deletes an entry whose deadline is a multiple of `Δ`,
so each fires at the same tick either way. `record_awake` now records the first reading after a
wake rather than the first multiple of `Δ` after it; the wake rule compares `awakeSince` with
window starts that are multiples of `Δ`, and the two values pass those tests at exactly the same
window starts.

**Steps over outcome sets.** A tick step reads the node's `tick` through its outcome set
`(tick …).outcomes` (`Goldilocks.DREB.outcomes`): a step is any answer of the tick. An execution
page reads a step through `step_tick_iff`, `step_recv_iff` and `step_wake_iff`.

- `DREBOutcomesOk d`: the failure is not among the outcomes of `d`, and an outcome exists;
- `reaction`: the deterministic reaction of a validator to an event, ticking at every reading,
  kept for `step_iff_eq_reaction` only;
- `reactions`: the set of reactions of a validator to an event, each an answer;
- `protocol`: Goldilocks's node with the step relation over `reactions`, in the framework's shape;
- the reading lemmas `mem_reactions_tick_iff`, `reactions_tick_eq_empty_iff`, `step_tick_iff`,
  `step_recv_iff`, `step_wake_iff`, and `step_iff_eq_reaction`.
-/

set_option autoImplicit false

open scoped DC
open DC (DRE)

namespace GoldilocksCorrectness.Wiring

open Framework.StsMultisetLog
open Goldilocks (NamedObject NodeState wake initial tick DREB)
open Goldilocks.Sts (Setup receive relayedObjects)

/-! ## The outcome set of a duty -/

/-- If the run of `d` with nothing sent answers, the failure is not an outcome of `d` and an
outcome exists. -/
theorem DREBOutcomesOk.of_run_ok {V α : Type} {d : DREB V α}
    (h : ∃ p : α × List (NamedObject V), d.run [] = .ok p) : DREBOutcomesOk d := by
  obtain ⟨p, hp⟩ := h
  refine ⟨fun r hr => ⟨p, ?_⟩, ⟨_, DREB.run_mem_outcomes d⟩⟩
  rw [← DREB.run_eq_of_mem_outcomes hr, hp]

variable {V : Type} [DecidableEq V] [Fintype V] [Goldilocks.RootOrder]

/-! ## The wiring -/

/-- The deterministic reaction of a validator holding the node state `n` to the event `e` at the
clock reading `t`: the original's reaction (`Goldilocks.Sts.reaction`) with the `tick` case run at
every reading. It is kept for the equality `step_iff_eq_reaction` only; `protocol`'s step is the
relation over `reactions`.

- `tick`: the node's `tick` at `t`, applied to the setup's parameters `S.C` and its values `S.P`
  and `S.X`, run with nothing sent (`.run []`). If it answers with a node state and the list of
  objects it broadcast, the reaction's state is that node state and its `send` is that list. If it
  fails, the reaction keeps `n` and sends nothing; the failure is not a step, and this branch exists
  only so that the protocol is never stuck.
- `recv m`: `receive` with `S.C`, `S.P` and `S.X` on the delivered object `m.msg`; the reaction
  re-sends `relayedObjects m.msg`.
- `wake`: `wake` at the reading `t`, which sets `awakeSince` to `none` and the clock to `t`; nothing
  is sent.

Read aloud: at every reading the node ticks and, when the tick succeeds, the validator takes the
tick's state and sends what it broadcast, and when it fails, stays where it was and sends nothing;
on a delivery it processes the object and re-sends it, with a block's Goldfish votes and
attestations; on a wake it forgets the time it had been awake since, sets its clock to the
reading, and sends nothing. -/
def reaction (S : Setup V) (n : NodeState V) (t : Int)
    (e : Event V (NamedObject V) Empty) :
    NodeStepResult (NodeState V) (NamedObject V) :=
  match e with
  | .tick =>
      match (tick S.C S.P S.X n t).run [] with
      | Except.ok (n', sent) => { state := n', send := (sent : Multiset (NamedObject V)) }
      | Except.error _ => { state := n, send := 0 }
  | .recv m => { state := receive S.C S.P S.X n m.msg, send := relayedObjects m.msg }
  | .wake => { state := wake n t, send := 0 }
  | .custom ev => ev.elim

/-- The reactions a validator holding the node state `n` may have to the event `e` at the clock
reading `t`, each an answer: a failed outcome of the tick is no reaction.

- `tick`: for every `.ok` outcome of the node's `tick` at `t` (run with nothing sent), the node
  state it answers and the objects it broadcast, as a multiset;
- `recv m`: `receive` on the delivered object, re-sending `relayedObjects m.msg`;
- `wake`: `wake` at the reading `t`, nothing sent.

Read aloud: at a tick the validator takes any answer of its tick and sends what that answer
broadcast; a delivery and a wake react as `reaction` does. -/
def reactions (S : Setup V) (n : NodeState V) (t : Int)
    (e : Event V (NamedObject V) Empty) :
    Set (NodeStepResult (NodeState V) (NamedObject V)) :=
  match e with
  | .tick =>
      { res | ∃ r ∈ (tick S.C S.P S.X n t).outcomes,
          ∃ p : NodeState V × List (NamedObject V),
            r = .ok p ∧ res = { state := p.1, send := (p.2 : Multiset (NamedObject V)) } }
  | .recv m =>
      { res | res = { state := receive S.C S.P S.X n m.msg, send := relayedObjects m.msg } }
  | .wake => { res | res = { state := wake n t, send := 0 } }
  | .custom ev => ev.elim

/-- Goldilocks's node in the framework's shape, ticking at every reading: the step relation over
`reactions`, with the one fallback that keeps the protocol from being stuck when nothing reacts.

Read aloud: every validator starts from Goldilocks's initial node state, and a step of validator
`p` at reading `r` on event `e` is any reaction in `reactions S n r e`, or, only when there is
none, keeping the state and sending nothing. -/
def protocol (S : Setup V) :
    Framework.StsMultisetLog.Protocol V (NamedObject V) (NodeState V) Empty where
  init p := initial S.C p
  step _ r _view n e res :=
    res ∈ reactions S n (r : Int) e ∨
      (reactions S n (r : Int) e = ∅ ∧ res = { state := n, send := 0 })
  total := by
    classical
    intro _ r _view n e
    by_cases h : (reactions S n (r : Int) e).Nonempty
    · obtain ⟨res, hres⟩ := h
      exact ⟨res, Or.inl hres⟩
    · exact ⟨{ state := n, send := 0 },
        Or.inr ⟨Set.not_nonempty_iff_eq_empty.mp h, rfl⟩⟩
  enabled _ _ ev := ev.elim

/-! ## Reading a step -/

/-- A reaction to a tick is an `.ok` outcome of the node's tick, read as a step result.

The variables:
- `S`: the setup; `n`: the node state; `t`: the clock reading; `res`: the step result. -/
theorem mem_reactions_tick_iff (S : Setup V) (n : NodeState V) (t : Int)
    (res : NodeStepResult (NodeState V) (NamedObject V)) :
    res ∈ reactions S n t .tick ↔
      ∃ (n' : NodeState V) (sent : List (NamedObject V)),
        .ok (n', sent) ∈ (tick S.C S.P S.X n t).outcomes ∧
          res = { state := n', send := (sent : Multiset (NamedObject V)) } := by
  simp only [reactions, Set.mem_setOf_eq]
  constructor
  · rintro ⟨r, hr, ⟨n', sent⟩, rfl, rfl⟩
    exact ⟨n', sent, hr, rfl⟩
  · rintro ⟨n', sent, hr, rfl⟩
    exact ⟨_, hr, (n', sent), rfl, rfl⟩

/-- No reaction to a tick exactly when no outcome of the tick is an answer.

The variables:
- `S`: the setup; `n`: the node state; `t`: the clock reading. -/
theorem reactions_tick_eq_empty_iff (S : Setup V) (n : NodeState V) (t : Int) :
    reactions S n t .tick = ∅ ↔
      ∀ p : NodeState V × List (NamedObject V), .ok p ∉ (tick S.C S.P S.X n t).outcomes := by
  constructor
  · intro h p hp
    have hmem : ({ state := p.1, send := (p.2 : Multiset (NamedObject V)) } :
        NodeStepResult (NodeState V) (NamedObject V)) ∈ reactions S n t .tick :=
      (mem_reactions_tick_iff S n t _).2 ⟨p.1, p.2, hp, rfl⟩
    rw [h] at hmem
    exact hmem
  · intro h
    ext res
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hres
    obtain ⟨n', sent, hr, -⟩ := (mem_reactions_tick_iff S n t res).1 hres
    exact h (n', sent) hr

/-- **Reading a tick step.** The step relation at `.tick` holds of `res` exactly when `res` is an
`.ok` outcome of the node's tick at the reading, as a step result, or no outcome of the tick is
an answer and `res` keeps the state and sends nothing.

The variables:
- `S`: the setup; `p`: the validator; `r`: the reading; `view`: its view; `n`: its node state;
  `res`: the step result.

Read aloud: a tick step is an answer of the tick, or, only when the tick cannot answer, the
validator doing nothing. -/
theorem step_tick_iff (S : Setup V) (p : V) (r : ℕ) (view : View V (NamedObject V))
    (n : NodeState V) (res : NodeStepResult (NodeState V) (NamedObject V)) :
    (protocol S).step p r view n .tick res ↔
      (∃ (n' : NodeState V) (sent : List (NamedObject V)),
        .ok (n', sent) ∈ (tick S.C S.P S.X n (r : Int)).outcomes ∧
          res = { state := n', send := (sent : Multiset (NamedObject V)) }) ∨
      ((∀ q : NodeState V × List (NamedObject V),
          .ok q ∉ (tick S.C S.P S.X n (r : Int)).outcomes) ∧
        res = { state := n, send := 0 }) := by
  show (res ∈ reactions S n (r : Int) .tick ∨
    (reactions S n (r : Int) .tick = ∅ ∧ res = { state := n, send := 0 })) ↔ _
  rw [mem_reactions_tick_iff, reactions_tick_eq_empty_iff]

/-- **Reading a delivery step**: `receive` on the object, re-sending `relayedObjects`.

The variables:
- `S`: the setup; `p`: the validator; `r`: the reading; `view`: its view; `n`: its node state;
  `m`: the delivered message; `res`: the step result. -/
theorem step_recv_iff (S : Setup V) (p : V) (r : ℕ) (view : View V (NamedObject V))
    (n : NodeState V) (m : SignedMsg V (NamedObject V))
    (res : NodeStepResult (NodeState V) (NamedObject V)) :
    (protocol S).step p r view n (.recv m) res ↔
      res = { state := receive S.C S.P S.X n m.msg, send := relayedObjects m.msg } := by
  show (res ∈ reactions S n (r : Int) (.recv m) ∨
    (reactions S n (r : Int) (.recv m) = ∅ ∧ res = { state := n, send := 0 })) ↔ _
  constructor
  · rintro (h | ⟨h, -⟩)
    · exact h
    · exact absurd h (Set.Nonempty.ne_empty ⟨_, rfl⟩)
  · intro h
    exact Or.inl h

/-- **Reading a wake step**: `wake` at the reading, nothing sent.

The variables:
- `S`: the setup; `p`: the validator; `r`: the reading; `view`: its view; `n`: its node state;
  `res`: the step result. -/
theorem step_wake_iff (S : Setup V) (p : V) (r : ℕ) (view : View V (NamedObject V))
    (n : NodeState V) (res : NodeStepResult (NodeState V) (NamedObject V)) :
    (protocol S).step p r view n .wake res ↔ res = { state := wake n (r : Int), send := 0 } := by
  show (res ∈ reactions S n (r : Int) .wake ∨
    (reactions S n (r : Int) .wake = ∅ ∧ res = { state := n, send := 0 })) ↔ _
  constructor
  · rintro (h | ⟨h, -⟩)
    · exact h
    · exact absurd h (Set.Nonempty.ne_empty ⟨_, rfl⟩)
  · intro h
    exact Or.inl h

/-- Under the deterministic duty monad, the step relation is the graph of `reaction`: the one
`.ok` outcome of the tick is the reaction, and when the run fails nothing reacts and the fallback
is `reaction`'s failure branch.

The variables:
- `S`: the setup; `p`: the validator; `r`: the reading; `view`: its view; `n`: its node state;
  `e`: the event; `res`: the step result.

Read aloud: a step is exactly the deterministic reaction. -/
theorem step_iff_eq_reaction (S : Setup V) (p : V) (r : ℕ) (view : View V (NamedObject V))
    (n : NodeState V) (e : Event V (NamedObject V) Empty)
    (res : NodeStepResult (NodeState V) (NamedObject V)) :
    (protocol S).step p r view n e res ↔ res = reaction S n (r : Int) e := by
  cases e with
  | tick =>
      rw [step_tick_iff]
      simp only [reaction]
      have hm := DREB.run_mem_outcomes (tick S.C S.P S.X n (r : Int))
      cases h : (tick S.C S.P S.X n (r : Int)).run [] with
      | ok q =>
          obtain ⟨n', sent⟩ := q
          rw [h] at hm
          constructor
          · rintro (⟨n'', sent', hmem, rfl⟩ | ⟨hno, rfl⟩)
            · have h' := DREB.run_eq_of_mem_outcomes hmem
              rw [h] at h'
              cases h'
              rfl
            · exact absurd hm (hno (n', sent))
          · rintro rfl
            exact Or.inl ⟨n', sent, hm, rfl⟩
      | error err =>
          constructor
          · rintro (⟨n'', sent', hmem, rfl⟩ | ⟨-, rfl⟩)
            · have h' := DREB.run_eq_of_mem_outcomes hmem
              rw [h] at h'
              cases h'
            · rfl
          · rintro rfl
            refine Or.inr ⟨fun q hq => ?_, rfl⟩
            have h' := DREB.run_eq_of_mem_outcomes hq
            rw [h] at h'
            cases h'
  | recv m =>
      rw [step_recv_iff]
      exact Iff.rfl
  | wake =>
      rw [step_wake_iff]
      exact Iff.rfl
  | custom ev => exact ev.elim

end GoldilocksCorrectness.Wiring
