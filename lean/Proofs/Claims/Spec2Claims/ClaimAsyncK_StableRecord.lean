import Proofs.Claims.Spec2Claims.Claim13bK_StableRecord
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedTick_tick
import Proofs.Claims.Spec2Claims.Claim13bModel_frameStableRoot_cs
import Proofs.Claims.Spec2Claims.Claim13bModel_Preceq
import Proofs.Claims.Spec2Claims.Claim13bModel_compatible
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedNode_tick
import Proofs.Claims.Spec2Claims.Claim13bModel_proposal_time_inclG1

/-!
# The stable output from the stable record

When `P` is an ancestor of a store's stable record and is compatible with its finalized block, `P`
is an ancestor of the store's stable output.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog

variable {V : Type} [DecidableEq V] [Fintype V]

local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If `P` is an ancestor of the store's stable record `st.latest_stable` or that record itself, and
    `P` is compatible with the store's finalized block `st.F`, then `P` is an ancestor of the stable
    output `Protocol.get_stable st` or that output itself. -/
theorem preceq_get_stable_of_record (st : Protocol.Store V) {P : Block V}
    (hL : Block.Preceq P st.latest_stable) (hF : Block.Compatible P st.F) :
    Block.Preceq P (Protocol.get_stable st) :=
  Proofs.NamedOutageClosure.preceq_get_stable st hL (compatible_iff_Compatible.mp hF)

end DecoupledConsensusModel.Sts
