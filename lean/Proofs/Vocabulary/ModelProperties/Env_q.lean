module
public import Model.Vocabulary.Objects.Parameters
public import Proofs.Vocabulary.Internal.ModelVocabulary.Substrate.Weights

@[expose] public section

/-!
# Facts about `Env.q`

The finality threshold of an environment against the quorum proposition.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

variable {V : Type} [DecidableEq V] [Fintype V]

/-- A set whose weight in `E`'s electorate is at least `E.q` is a quorum of that electorate. -/
theorem isQuorum_of_q_le (E : Env V) {S : Finset V} (h : E.q ≤ E.electorate.weightOf S) :
    E.electorate.IsQuorum S := by
  unfold Electorate.IsQuorum
  unfold Env.q at h
  exact h

end DecoupledConsensusModel.Proofs.ModelProperties

end
