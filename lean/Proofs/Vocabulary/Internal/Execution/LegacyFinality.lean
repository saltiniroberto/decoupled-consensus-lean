module
public import Proofs.Vocabulary.Internal.ModelVocabulary.Execution.Run

@[expose] public section

/-!
# Finalized roots at a safety handover

The property `FinalizedRootsBelowAtRead`: the certificates held at any honest read, with finalized
height at most a cap, finalize ancestors of one fixed block.
-/

namespace DecoupledConsensusModel
namespace Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Every named body held by an honest reader whose derived finalized height is at most `cap`
    finalizes an ancestor of `P`. -/
def FinalizedRootsBelowAtRead (S : Setup V) (rho : Run V)
    (cap : Height) (P : Block V) : Prop :=
  ∀ v ∈ rho.honest, ∀ t : Time, ∀ C ∈ (rho.storeBeforeTime S v t).bodies,
    (Protocol.derive_named S.E S.cfg C).h_F ≤ cap →
      Block.Preceq (Protocol.derive_named S.E S.cfg C).F P

end Execution
end DecoupledConsensusModel

end
