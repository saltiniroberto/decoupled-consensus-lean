import Model.Vocabulary.Protocol.StoreBase
import Proofs.Claims.ModelIrreducible

/-!
# Facts about `Protocol.resolved`

A lemma that unfolds the resolution test of a Goldfish vote.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.resolved

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- `u` resolves in the tree `T` exactly when `Block.find?` finds a block `X` for `u`'s head root in
    `T` with `X.slot ≤ u.slot`. -/
theorem resolved_eq_true_iff (T : Finset (Block V)) (u : GoldfishVote V) :
    Protocol.resolved T u = true ↔
      ∃ X : Block V, Block.find? T u.head = some X ∧ X.slot ≤ u.slot := by
  unfold Protocol.resolved
  cases hf : Block.find? T u.head with
  | none => simp
  | some X => simp

end DecoupledConsensusModel.Sts
