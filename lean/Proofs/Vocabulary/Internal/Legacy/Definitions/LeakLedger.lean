module
public import Model.Vocabulary.Protocol.ChainState
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow

@[expose] public section

/-!
# Per-layer inactivity charges

The charges `LayerCharges` of each layer and their scaling.
-/


namespace DecoupledConsensusModel
namespace Internal.LeakLedger
open Protocol
variable {V : Type} [DecidableEq V]

/-- The inactivity charges of each layer, kept separately. -/
structure LayerCharges where
  l1 : Nat
  l2Target : Nat
  l2Finalize : Nat

def LayerCharges.scale (slots : Nat) (c : LayerCharges) : LayerCharges :=
  ⟨slots * c.l1, slots * c.l2Target, slots * c.l2Finalize⟩

variable [Fintype V]

end Internal.LeakLedger
end DecoupledConsensusModel

end
