module
public import Model.Vocabulary.Protocol.ChainState

@[expose] public section

/-!
# Facts about `Protocol.Slashable`

The proposition `Protocol.Slashable` against the Boolean test `Protocol.slashable`.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

variable {V : Type} [DecidableEq V]

/-- `Protocol.Slashable a b` holds exactly when `Protocol.slashable a b` is `true`. -/
theorem Slashable_iff {a b : CombinedAttestation V} :
    Protocol.Slashable a b ↔ Protocol.slashable a b = true := Iff.rfl

end DecoupledConsensusModel.Proofs.ModelProperties

end
