module
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.FinalityFilterInterference
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.Records
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
public import Proofs.Vocabulary.Internal.Internal.GradeReads

@[expose] public section

/-!
# Finality-filter retention

The condition that a block is in the filtered block tree of a validator's store at a read.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]

/-- `P` is in the filtered block tree of `w`'s store before time `read`. -/
def FinalityFilterRetainedAtRead
    (S : Setup V) (rho : Run V) (w : V) (read : Time)
    (P : Block V) : Prop :=
  P ∈ Protocol.get_filtered_block_tree
    (rho.storeBeforeTime S w read).toHealing.toFG


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
