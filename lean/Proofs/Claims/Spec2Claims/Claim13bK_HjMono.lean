import Proofs.Claims.Spec2Claims.Claim13bModel_AdvanceHeight
import Proofs.Claims.Spec2Claims.Claim13beRoute3_85
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedBlock_parent

/-!
# The justified height never decreases along a chain

If a named block is an ancestor of another, the justified height of its chain state is at most the
other's.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol (HeightConfig derive_named)

variable {V : Type} [DecidableEq V] [Fintype V]

/-- If the named block `A` is an ancestor of the named block `B`, then the justified height of `A`'s
    chain state is at most the justified height of `B`'s chain state. -/
theorem derive_named_h_j_mono (E : Env V) (cfg : HeightConfig) {A B : NamedBlock V}
    (hAB : NamedBlock.Preceq A B) :
    (derive_named E cfg A).h_j ≤ (derive_named E cfg B).h_j := by
  induction B with
  | genesis =>
      rw [namedPreceq_genesis_iff_l85.mp hAB]
  | node p s root gv gsv ats proposer ih =>
      rcases namedPreceq_node_iff_l85.mp hAB with rfl | hAp
      · exact le_refl _
      · have h := derive_named_h_j_parent_le E cfg (.node p s root gv gsv ats proposer)
        rw [namedBlock_parent_node] at h
        exact (ih hAp).trans h

end DecoupledConsensusModel.Sts
