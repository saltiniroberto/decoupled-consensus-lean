module
public import Model.Vocabulary.Protocol.ForkChoice.Goldfish

@[expose] public section

/-!
# Membership in the viable tree

A characterization of membership in `Protocol.viable_tree`.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

variable {V : Type} [DecidableEq V]

/-- `B` is in the viable tree of `σ`, `F`, `h_max` and `T` exactly when `B` is in `T`, `F` is an
    ancestor of `B` or `B` itself, and some `W` in `T` that is `B` or a descendant of `B` has
    chain-state height at least `h_max - 1`. -/
theorem mem_viable_tree_iff (σ : Block V → Protocol.ChainState V) (F : Block V) (h_max : Height)
    (T : Finset (Block V)) (B : Block V) :
    B ∈ Protocol.viable_tree σ F h_max T ↔
      (B ∈ T ∧ Block.Preceq F B) ∧ ∃ W ∈ T, Block.Preceq B W ∧ h_max - 1 ≤ (σ W).h := by
  simp only [Protocol.viable_tree, Protocol.finalized_descendants, Protocol.viable,
    Finset.mem_filter, decide_eq_true_eq]
  rfl

end DecoupledConsensusModel.Proofs.ModelProperties

end
