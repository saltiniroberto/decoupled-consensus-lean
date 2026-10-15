import Proofs.Claims.Spec2Claims.ClaimAsyncK_GstShift
import Proofs.Claims.Spec2Claims.ClaimAsyncK_FinalizedAbove
import Proofs.Claims.Spec2Claims.ClaimAsyncK_Defs
import Proofs.Claims.Spec2Claims.Claim13bK_ConfirmedSettleEarlier

/-!
# The chain state at a new GST

The chain state of a named block is the same at the setup with a new GST.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

attribute [local irreducible] protocol

/-- The chain state derived for a named block `B` at the setup with GST `g` is the one derived at
    `S`. -/
theorem derive_named_setupWithGST (S : Setup V) (g : Int) (hg : 0 ≤ g) (B : NamedBlock V) :
    Protocol.derive_named (setupWithGST S g hg).E (setupWithGST S g hg).cfg B =
      Protocol.derive_named S.E S.cfg B := by
  exact derive_named_withGST S.E g hg S.cfg B

end DecoupledConsensusModel.Sts
