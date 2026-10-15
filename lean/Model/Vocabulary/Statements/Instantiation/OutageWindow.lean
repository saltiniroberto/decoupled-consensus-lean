module
public import Model.Vocabulary.Execution.Setup

@[expose] public section

/-!
# Round length and next action

The round length of the healing schedule and the first round action at or after a given time.
-/
namespace DecoupledConsensusModel.Statements.Instantiation
open Execution DecoupledConsensusModel.Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

/-- The round length of the healing schedule, `a_{r+1} - a_r = 4·R·Δ`. -/
def roundLength (S : Setup V) : Time := 4 * S.E.Δ * (S.hc.R : Time)

/-- The first round whose action is at or after `T`: the least `s` with
`T ≤ S.a s`, computed from `S.a s = 6Δ + s·roundLength`. -/
def roundAfter (S : Setup V) (T : Time) : Round :=
  (Int.ediv (T - 6 * S.E.Δ + roundLength S - 1) (roundLength S)).toNat

/-- The first round action at or after `T`. -/
def nextAction (S : Setup V) (T : Time) : Time := S.a (roundAfter S T)

end DecoupledConsensusModel.Statements.Instantiation

end
