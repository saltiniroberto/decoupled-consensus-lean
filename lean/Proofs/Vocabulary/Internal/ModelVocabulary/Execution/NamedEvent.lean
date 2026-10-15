module
public import Model.Vocabulary.Execution.Objects
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow

@[expose] public section

/-!
# Named events

Named event data and its time and phase ordering.
-/
namespace DecoupledConsensusModel.Execution

namespace NamedEvent
variable {V : Type}

@[simp] theorem tick.injEq (v v' : V) (t t' : Time) :
    (NamedEvent.tick v t = NamedEvent.tick v' t') = (v = v' ∧ t = t') :=
  Generic.Event.tick.injEq v t v' t'

def phase : NamedEvent V → Nat
  | .tick _ _ => 0
  | .deliver _ _ _ => 1

def key (e : NamedEvent V) : Lex (Time × Nat) := toLex (e.time, e.phase)

end NamedEvent
end DecoupledConsensusModel.Execution

end
