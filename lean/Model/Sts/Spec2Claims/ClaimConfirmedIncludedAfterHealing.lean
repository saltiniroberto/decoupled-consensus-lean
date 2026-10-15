module
public import Model.Sts.Spec2Claims.Claim13bf
public import Mathlib.Data.Rat.Floor

@[expose] public section

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

noncomputable section

variable {V : Type} [DecidableEq V] [Fintype V]

/-!
# Confirmed inclusion delay

The delay `confirmedInclusionDelay` from a slot's proposal instant to the instant its confirmation
is evaluated.
-/

/-- Six delays: the time from a slot's proposal instant to its confirmation instant
    `Protocol.confirmation_time`. -/
def confirmedInclusionDelay (S : Setup V) : Int := 6 * S.E.Δ

end

end DecoupledConsensusModel.Sts
