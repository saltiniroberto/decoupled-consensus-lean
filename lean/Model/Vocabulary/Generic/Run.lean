module
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Prod.Lex
public import Mathlib.Logic.Function.Basic
public import Model.Vocabulary.Objects.Time

@[expose] public section

/-!
# Generic execution model

Events, protocol specifications and runs: a protocol gives a node state, the objects it exchanges
and its handlers; a run gives an honest set, a horizon and an event list.
-/

namespace DecoupledConsensusModel.Generic

/-- A scheduler event at a node: its local clock tick, or the delivery of one object. -/
inductive Event (V Object : Type) where
  | tick (v : V) (t : Time)
  | deliver (v : V) (object : Object) (t : Time)
  deriving DecidableEq

namespace Event
variable {V Object : Type}
def time : Event V Object → Time
  | .tick _ t => t
  | .deliver _ _ t => t
def phase : Event V Object → Nat
  | .tick _ _ => 0
  | .deliver _ _ _ => 1
/-- Event order is lexicographic by time and phase. Ticks therefore precede
deliveries at the same time; equal-phase deliveries keep their list order. -/
def key (e : Event V Object) : Lex (Time × Nat) := toLex (e.time, e.phase)
end Event

/-- A protocol: the node state, the objects it exchanges, the initial state, the tick and delivery
    handlers, and the observation hooks used by statements. -/
structure ProtocolSpec (V : Type) where
  State : Type
  Object : Type
  init : State
  tick : V → State → Time → State × List Object
  process : State → Object → State
  /-- The validator an object is attributed to, if any. -/
  author : Object → Option V
  /-- Syntactic well-formedness of an object on the wire. -/
  wellFormed : Object → Bool
  /-- The node's state holds what the object depends on (e.g. the parent block). -/
  depsPresent : State → Object → Bool
  /-- The node's state already holds the object. -/
  processed : State → Object → Bool
  /-- The node's state excludes the object for good: the node rejects it now and in every later
      state. -/
  excludes : State → Object → Bool
  /-- In state `s`, event `e` makes the node handle object `o`, directly or as an object carried
      inside the delivered or emitted object; this can hold even when the object is rejected. -/
  handles : State → Event V Object → Object → Prop
  /-- The first object structurally contains the second, as a block contains a vote it includes. -/
  carries : Object → Object → Prop

namespace World
variable {V : Type} [DecidableEq V] {P : ProtocolSpec V}
end World

/-- A run: the honest set, the horizon, and the event list. -/
structure Run (V Object : Type) where
  honest : Finset V
  horizon : Time
  events : List (Event V Object)

namespace Run
variable {V : Type} [DecidableEq V] (P : ProtocolSpec V)

end Run
end DecoupledConsensusModel.Generic

end
