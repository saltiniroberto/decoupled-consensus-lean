import Model.Sts.Spec2Claims.Claim13bf
import Proofs.Claims.Spec2Claims.Claim13bK_ConeChain
import Proofs.Claims.Spec2Claims.Claim13bK_HeadsNewAnchor
import Proofs.Claims.Spec2Claims.Claim13beRoute3_83
import Proofs.Claims.Spec2Claims.Claim13bK_GradeDescendant
import Proofs.Claims.Spec2Claims.Claim13bModel_Preceq
import Proofs.Claims.Spec2Claims.Claim13bModel_vote_time
import Proofs.Claims.Spec2Claims.Claim13bModel_view_freeze
import Proofs.Claims.Spec2Claims.Claim13bModel_frameGradeRead_attest
import Proofs.Claims.Spec2Claims.Claim13bModel_proposal_time_inclG1
import Proofs.Claims.Spec2Claims.Claim13bModel_anchor
import Proofs.Claims.Spec2Claims.Claim13bModel_opening
import Proofs.Claims.Spec2Claims.Claim13bModel_compatible
import Proofs.Vocabulary.ModelProperties.Block_Preceq

/-!
# Compatibility with an ancestor

If `G` lies on one chain with `L` and `X` is an ancestor of `L`, then `G` and `X` lie on one chain.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)


omit [Fintype V] in
/-- If `G` lies on one chain with `L` and `X` is an ancestor of `L`, then `G` and `X` lie on one
    chain. -/
theorem compatible_of_compatible_of_preceq {G L X : Block V}
    (hGL : Block.compatible G L = true) (hXL : Block.Preceq X L) :
    Block.compatible G X = true := by
  rcases compatible_cases hGL with hGL' | hLG
  · exact compatible_of_preceq_common_Preceq hGL' hXL
  · exact compatible_of_preceq_common_Preceq (Proofs.ModelProperties.Preceq_self G)
      (preceq_trans_Preceq hXL hLG)


end DecoupledConsensusModel.Sts
