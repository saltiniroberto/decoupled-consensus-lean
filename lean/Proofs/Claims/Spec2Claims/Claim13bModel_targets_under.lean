import Model.Vocabulary.Protocol.ForkChoice.Goldfish
import Proofs.Claims.ModelIrreducible

/-!
# Facts about `Protocol.targets_under`

A lemma that unfolds the supporter test of a single Goldfish vote.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Block.Preceq
  DecoupledConsensusModel.Protocol.targets_under

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- The vote `u` passes the supporter test for `B` in the tree `T` exactly when `u`'s head resolves
    in `T` to a block `X` with `X.slot ≤ u.slot` and `B ⪯ X`. -/
theorem targets_under_eq_true_iff (T : Finset (Block V)) (B : Block V) (u : GoldfishVote V) :
    Protocol.targets_under T B u = true ↔
      ∃ X, Block.find? T u.head = some X ∧ X.slot ≤ u.slot ∧ Block.Preceq B X := by
  unfold Protocol.targets_under Block.Preceq
  cases Block.find? T u.head with
  | none => simp
  | some X => simp

end DecoupledConsensusModel.Sts
