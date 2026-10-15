import Proofs.Claims.Spec2Claims.Claim13bStepConeIter
import Proofs.Claims.Spec2Claims.Claim13bModel_confirmation_time

/-!
# The honest active attesters of a round

`HonRound S Sched r` is the set of validators active in round `r`'s attester window that the
adversary does not hold at the round's action instant.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The validators awake at every instant from `wAttest S` before round `r`'s action instant through
    that instant, and not held by the adversary at it: `activeRoundW S Sched r` minus `Sched.adv` at
    the round's action instant. -/
def HonRound (S : Setup V) (Sched : Schedule V) (r : Round) : Finset V :=
  activeRoundW S Sched r \ Sched.adv (S.hc.a S.E.Δ r)

end DecoupledConsensusModel.Sts
