import Proofs.Claims.Spec2Claims.Claim13beRoute3_70b
import Proofs.Claims.Spec2Claims.Claim13bModel_opening_slot

/-!
# Round bounds

The three inequalities between the rounds `a`, `a + b` and `a + b + 2` over `Nat`.
-/

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

section FGSafetyFrontierBandNamed

local macro "fbn% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `DecoupledConsensusProofs.Generic.FGSafetyFrontierBandNamed)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

end FGSafetyFrontierBandNamed

section AtRn

open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- `a < a + b + 2`, `a ≤ a + b`, and `a + 1 ≤ a + b + 2 − b`. -/
theorem roundAt_bounds_nat_l71 (a b : Nat) :
    a < a + b + 2 ∧ a ≤ a + b ∧ a + 1 ≤ a + b + 2 - b := by
  omega

end AtRn

end DecoupledConsensusModel.Sts
