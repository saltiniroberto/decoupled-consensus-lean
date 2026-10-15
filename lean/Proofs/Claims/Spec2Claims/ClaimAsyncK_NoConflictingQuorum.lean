import Proofs.Claims.Spec2Claims.ClaimAsyncK_Defs
import Proofs.Claims.Spec2Claims.Claim13beRoute3_83
import Proofs.Claims.Spec2Claims.Claim13bK_ConeChain
import Proofs.Claims.Spec2Claims.Claim13bModel_get_filtered_block_tree
import Proofs.Claims.Spec2Claims.Claim13bModel_matchesEntry
import Proofs.Claims.Spec2Claims.Claim13bModel_get_fg_root
import Proofs.Claims.Spec2Claims.Claim13bModel_Preceq
import Proofs.Claims.Spec2Claims.Claim13bModel_compatible

/-!
# Two facts on compatible blocks

Every block is compatible with genesis, and an ancestor of a block compatible with `P` is compatible
with `P`.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- Every block `P` is compatible with genesis. -/
theorem compatible_genesis_right (P : Block V) : Block.Compatible P Block.genesis :=
  compatible_iff_Compatible.mpr (compatible_of_cases
    (Or.inr (Sts.preceq_eq_true_iff_Preceq.mp (Protocol.preceq_genesis P))))

omit [Fintype V] in
/-- If `A` is an ancestor of `B` and `B` is compatible with `P`, then `A` is compatible with `P`. -/
theorem compatible_of_preceq_of_compatible {P A B : Block V} (hAB : Block.Preceq A B)
    (hB : Block.Compatible P B) : Block.Compatible P A := by
  rcases compatible_cases (compatible_iff_Compatible.mp hB) with hPB | hBP
  · exact compatible_iff_Compatible.mpr (compatible_of_preceq_common_Preceq hPB hAB)
  · exact compatible_iff_Compatible.mpr
      (compatible_of_cases (Or.inr (preceq_trans_Preceq hAB hBP)))

end DecoupledConsensusModel.Sts
