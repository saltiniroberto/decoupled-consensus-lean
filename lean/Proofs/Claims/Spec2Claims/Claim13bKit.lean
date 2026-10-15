module
public import Proofs.Claims.Spec2Claims.Claim13bAnchor
public import Proofs.Claims.Spec2Claims.Claim13bModel_round_action_with
public import Proofs.Claims.Spec2Claims.Claim13bModel_encodeHeight_mk

@[expose] public section

/-!
# The longer healing length

`healingLengthη S gap` is the healing length `healingLength S gap` plus `S.hc.η_SG` more rounds.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The healing length `healingLength S gap` plus `S.hc.η_SG` more rounds. -/
noncomputable def healingLengthη (S : Setup V) (gap : Nat) : Int :=
  healingLength S gap + (S.hc.η_SG : Int) * (constants S).period

end DecoupledConsensusModel.Sts
