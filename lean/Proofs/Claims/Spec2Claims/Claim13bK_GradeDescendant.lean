import Proofs.Claims.Spec2Claims.Claim13bK_GradeOldHeads
import Proofs.Claims.Spec2Claims.Claim13bModel_frameGradeRead_attest
import Proofs.Claims.Spec2Claims.Claim13bModel_grade2Block

/-!
# Ancestors of blocks on one chain

Two ancestors of two blocks that lie on one chain lie on one chain.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- If `A` is an ancestor of `X`, `A'` an ancestor of `Y`, and `X` and `Y` lie on one chain, then
    `A` and `A'` lie on one chain. -/
theorem compatible_of_preceq_of_preceq {A A' X Y : Block V}
    (hA : Block.Preceq A X) (hA' : Block.Preceq A' Y)
    (hXY : Block.compatible X Y = true) : Block.compatible A A' = true :=
  Protocol.compatible_comm (Protocol.compatible_of_preceq_of_compatible hA'
    (Protocol.compatible_comm (Protocol.compatible_of_preceq_of_compatible hA hXY)))

end DecoupledConsensusModel.Sts
