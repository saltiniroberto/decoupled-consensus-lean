module
public import Model.Vocabulary.Execution.Run

@[expose] public section

/-!
# The named event fold

The initial world, the world transition, and the observations of a named run.
-/
namespace DecoupledConsensusModel.Execution

namespace NamedWorld
variable {V : Type} [DecidableEq V]

end NamedWorld

namespace NamedRun
variable {V : Type}

abbrev horizon (rho : NamedRun V) : Time := Generic.Run.horizon rho

@[simp] theorem honest_eq (rho : NamedRun V) :
    NamedRun.honest rho = Generic.Run.honest rho := rfl

@[simp] theorem horizon_eq (rho : NamedRun V) :
    NamedRun.horizon rho = Generic.Run.horizon rho := rfl

@[simp] theorem events_eq (rho : NamedRun V) :
    NamedRun.events rho = Generic.Run.events rho := rfl
end NamedRun

namespace NamedRun
variable {V : Type} [DecidableEq V] [Fintype V]

def final (S : Setup V) (rho : NamedRun V) : NamedWorld V :=
  rho.events.foldl (NamedWorld.step S) NamedWorld.init

def emittedAt (S : Setup V) (rho : NamedRun V) (i : Nat) (v : V) (t : Time) :
    List (NamedObject V) :=
  (NamedNode.tick S v (stateBefore S rho i v) t).2

def emits (S : Setup V) (rho : NamedRun V) (v : V) (o : NamedObject V) (t : Time) : Prop :=
  ∃ i : Nat, rho.events[i]? = some (.tick v t) ∧ o ∈ emittedAt S rho i v t

/-- `v` emits `o` at `t`, or `o` is delivered to `v` at `t`. -/
def processes (S : Setup V) (rho : NamedRun V) (v : V) (o : NamedObject V) (t : Time) : Prop :=
  emits S rho v o t ∨ ∃ i : Nat, rho.events[i]? = some (.deliver v o t)

def processesAtIndex (S : Setup V) (rho : NamedRun V) (i : Nat) (v : V)
    (o : NamedObject V) : Prop :=
  (∃ t : Time, rho.events[i]? = some (.tick v t) ∧ o ∈ emittedAt S rho i v t) ∨
    ∃ t : Time, rho.events[i]? = some (.deliver v o t)

end NamedRun
end DecoupledConsensusModel.Execution

end
