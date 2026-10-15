module
public import Proofs.Vocabulary.Internal.ModelVocabulary.Execution.Event
public import Proofs.Vocabulary.Internal.ModelVocabulary.Execution.Node
public import Proofs.Vocabulary.Internal.ModelVocabulary.Execution.NamedReceiptCalls

@[expose] public section

/-!
# Run observations

The observations of a run, computed by the named event fold.
-/
namespace DecoupledConsensusModel.Execution

namespace Run
abbrev honest {V : Type} (rho : Run V) : Finset V := Generic.Run.honest rho
abbrev horizon {V : Type} (rho : Run V) : Time := Generic.Run.horizon rho
abbrev events {V : Type} (rho : Run V) : List (Event V) := Generic.Run.events rho
abbrev stateBefore {V : Type} [DecidableEq V] [Fintype V]
    (S : Setup V) (rho : Run V) (i : Nat) : World V :=
  NamedRun.stateBefore S rho i
abbrev stateAt := @NamedRun.readAt
abbrev readAt := @NamedRun.readAt
abbrev stateBeforeTime {V : Type} [DecidableEq V] [Fintype V]
    (S : Setup V) (rho : Run V) (t : Time) : World V :=
  NamedRun.stateBeforeTime S rho t
abbrev emits {V : Type} [DecidableEq V] [Fintype V]
    (S : Setup V) (rho : Run V) (v : V) (o : Object V) (t : Time) : Prop :=
  NamedRun.emits S rho v o t
abbrev processes := @NamedRun.processes
abbrev acceptsAt := @NamedRun.acceptsAt
variable {V : Type} [DecidableEq V] [Fintype V]

def storeBeforeTime (S : Setup V) (rho : Run V) (v : V) (t : Time) : Protocol.NamedStore V :=
  (NamedRun.stateBeforeTime S rho t v).st

def lastTickIn (v : V) : List (Event V) → Option Time
  | [] => none
  | e :: rest => match lastTickIn v rest with
    | some t => some t
    | none => match e with
      | .tick w t => if w = v then some t else none
      | .deliver _ _ _ => none
end Run

abbrev RunBlock := @NamedRun.blockInRun
namespace Run
variable {V : Type} [DecidableEq V] [Fintype V]

end Run

namespace Run

variable {V : Type} [DecidableEq V] [Fintype V]

end Run

namespace NamedRun

variable {V : Type} [DecidableEq V] [Fintype V]

end NamedRun

end DecoupledConsensusModel.Execution

end
