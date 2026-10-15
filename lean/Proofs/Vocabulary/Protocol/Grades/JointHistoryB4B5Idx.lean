module
public import Proofs.Vocabulary.Protocol.Duties.Inputs.LayerAHistoryIndices
public import Proofs.Vocabulary.Protocol.Store.JointHistoryB4B5
public import Proofs.Vocabulary.Protocol.Grades.HealthyHeadReady
import Proofs.Vocabulary.Protocol.Grades.Grades
import Proofs.Vocabulary.Protocol.Grades.JointHistoryProducers
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

@[expose] public section

/-!
# Event key order

An event whose key is at most another's has a time at most the other's.
-/


namespace DecoupledConsensusModel.Proofs.NamedOutageHistory.JointHistoryB4B5
open Execution Internal.NamedOutageEntry Protocol
open Internal.NamedOutageEntry.History
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol
open JointHistoryProducersTime JointHistoryB4B5Time
variable {V : Type} [DecidableEq V] [Fintype V]

omit [DecidableEq V] [Fintype V] in
private theorem time_le_of_key_le {e f : NamedEvent V} (h : e.key ≤ f.key) :
    e.time ≤ f.time := by
  rcases Prod.Lex.le_iff.mp h with hlt | ⟨heq, _⟩
  · exact hlt.le
  · exact heq.le

end DecoupledConsensusModel.Proofs.NamedOutageHistory.JointHistoryB4B5

end
