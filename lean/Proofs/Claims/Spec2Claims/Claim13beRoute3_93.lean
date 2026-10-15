import Proofs.Claims.Spec2Claims.Claim13beRoute3_85f
import Proofs.Claims.Spec2Claims.Claim13bK_ProposalAdoption
import Proofs.Claims.Spec2Claims.Claim13bK_ConfirmedAgree
import Proofs.Claims.Spec2Claims.Claim13bModel_support_cutoff
import Proofs.Claims.Spec2Claims.Claim13bModel_compatible
import Proofs.Claims.Spec2Claims.Claim13bModel_Preceq
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedBlock_parent

/-!
# Consecutive opening slots

Consecutive opening slots at least `R ≥ 3` apart leave room for two slots after the earlier one.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Framework.StsMultisetLog

variable {V : Type} [DecidableEq V] [Fintype V]

section RowsOrAbove

/-- Every index into an sts execution is valid, so `get_elem_tactic` is answered by `True.intro`. -/
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If `o₁ = o₂ + R` and `3 ≤ R`, then `o₂ + 2 ≤ o₁ + 1` and `o₂ + 2 ≤ o₁`. -/
theorem nat_openings_f2b (o₁ o₂ R : Nat) (h : o₁ = o₂ + R) (hR : 3 ≤ R) :
    o₂ + 2 ≤ o₁ + 1 ∧ o₂ + 2 ≤ o₁ := by omega

end RowsOrAbove

section AtTick

/-- Every index into an sts execution is valid, so `get_elem_tactic` is answered by `True.intro`. -/
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

end AtTick

section Assembly

/-- Every index into an sts execution is valid, so `get_elem_tactic` is answered by `True.intro`. -/
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

end Assembly

end DecoupledConsensusModel.Sts
