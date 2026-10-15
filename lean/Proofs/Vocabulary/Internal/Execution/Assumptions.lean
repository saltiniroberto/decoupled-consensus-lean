module
public import Proofs.Vocabulary.Internal.ModelVocabulary.Execution.Run

@[expose] public section

/-!
# Weight assumptions

The fault assumptions on validator weight, `HonestWeightMajority` and `HonestQuorum`.
-/


namespace DecoupledConsensusModel
namespace Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Honest validators hold a strict majority of the total validator weight. -/
def HonestWeightMajority (S : Setup V) (H : Finset V) : Prop :=
  S.E.electorate.weightOf (Finset.univ \ H) <
    S.E.electorate.weightOf H

/-- Honest weight reaches the finality quorum `q`. -/
def HonestQuorum (S : Setup V) (H : Finset V) : Prop :=
  S.E.q ≤ S.E.electorate.weightOf H


end Execution
end DecoupledConsensusModel

end
