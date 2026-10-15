module
public import Proofs.Vocabulary.Protocol.Duties.Inputs.LayerAHistoryIndices
public import Proofs.Vocabulary.Protocol.Grades.JointHistoryProducers
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

@[expose] public section


namespace DecoupledConsensusModel.Proofs.NamedOutageHistory.IdxDriverHelpers
open Execution Internal.NamedOutageEntry Protocol
open Internal.NamedOutageEntry.History
variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Named ancestry is transitive -/

omit [Fintype V] in
theorem named_preceq_trans {A B C : NamedBlock V}
    (hAB : NamedBlock.Preceq A B) (hBC : NamedBlock.Preceq B C) :
    NamedBlock.Preceq A C := by
  induction C with
  | genesis =>
    have hB : B = .genesis := by
      simpa only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] using hBC
    exact hB ▸ hAB
  | node parent s root votes support rows proposer ih =>
    simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
      decide_eq_true_eq] at hBC
    rcases hBC with rfl | hBp
    · exact hAB
    · simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true]
      exact Or.inr (ih hBp)


end DecoupledConsensusModel.Proofs.NamedOutageHistory.IdxDriverHelpers

end
