module
public import Proofs.Vocabulary.Internal.ModelVocabulary.Execution.Setup

@[expose] public section

/-!
# Timeout-delay bounds

The bound on `S.cfg.timeoutDelay` in rounds given by `TimeoutDelayBound`.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Execution

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}

/-- Under `TimeoutDelayBound S delayExtra`, the timeout delay is at most
    `(2 + delayExtra) * S.hc.R`. -/
theorem timeoutDelay_le_roundBound (S : Setup V)
    (hdelay : TimeoutDelayBound S delayExtra) :
    S.cfg.timeoutDelay ≤ (2 + delayExtra) * S.hc.R :=
  Nat.le_of_eq hdelay


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
