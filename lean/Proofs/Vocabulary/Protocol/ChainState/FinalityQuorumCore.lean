module
public import Model.Vocabulary.Protocol.ChainState
import Proofs.Vocabulary.Protocol.ChainState.Chain

@[expose] public section

/-!
# The finality write of the height events

When `finalityReady` holds, `process_height_events` sets `F` to `J` and `h_F` to `h_j`.
-/

namespace DecoupledConsensusModel
namespace Proofs

open Protocol (ChainState HeightConfig)
open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

namespace HealingSurface


/-- When `finalityReady` holds, `process_height_events` sets `F` to `σ.J` and `h_F` to `σ.h_j`. -/
theorem process_height_events_actual_F
    (E : Env V) (cfg : HeightConfig) (σ : ChainState V)
    (hready : Protocol.finalityReady E σ) :
    let out := Protocol.process_height_events E cfg σ
    out.F = σ.J ∧ out.h_F = σ.h_j := by
  dsimp only
  constructor
  · rw [Protocol.process_height_events_F, Protocol.afterFin_F, if_pos hready]
  · rw [Protocol.process_height_events_h_F, Protocol.afterFin_h_F, if_pos hready]


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
