module
public import Model.Vocabulary.Objects.Parameters

@[expose] public section

/-!
# Facts about `Env.slotOf`

The slot of a time.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The time `0` is in slot `0`. -/
theorem slotOf_zero (E : Env V) : E.slotOf 0 = 0 := by
  unfold Env.slotOf slotOfTime
  simp

end DecoupledConsensusModel.Proofs.ModelProperties

end
