module
public import Model.Vocabulary.Protocol.Grades

@[expose] public section

/-!
# Facts about `Protocol.phaseResult`

A frame's result for one phase.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

variable {V : Type} [DecidableEq V]

/-- The result of the frame `f` for the grade-2 phase is `f.g2`. -/
theorem phaseResult_g2 (f : DecoupledConsensusModel.Protocol.Frame V) :
    DecoupledConsensusModel.Protocol.phaseResult f .g2 = f.g2 := rfl

end DecoupledConsensusModel.Proofs.ModelProperties

end
