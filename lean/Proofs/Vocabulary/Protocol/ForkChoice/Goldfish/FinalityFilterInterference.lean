module
public import Proofs.Vocabulary.Protocol.Handlers.StoreBridge
public import Proofs.Vocabulary.ModelProperties.Block_Preceq
public import Proofs.Vocabulary.ModelProperties.Block_prec
public import Proofs.Vocabulary.ModelProperties.Block_compatible
import Proofs.Vocabulary.Execution.Runtime
import Mathlib.RingTheory.WittVector.IsPoly

@[expose] public section

/-!
# Finality-filter interference at a read

The two ways the finality-gadget filter can remove a protected block `P` at a validator's read: the
FG root conflicts with `P`, or the FG root is a strict ancestor of `P` while the filtered block tree
drops `P`.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- In `w`'s store before time `read`, `P` is an ancestor of the FG root or `P` is in the filtered
    block tree. -/
def FinalityFilterNoninterferenceAtRead
    (S : Setup V) (rho : Run V) (w : V) (read : Time)
    (P : Block V) : Prop :=
  Block.Preceq P
      (Protocol.get_fg_root
        (rho.storeBeforeTime S w read).toHealing.toFG) ∨
    P ∈ Protocol.get_filtered_block_tree
      (rho.storeBeforeTime S w read).toHealing.toFG

/-- The FG root of the store conflicts with `P`. -/
def FGRootInterferenceAt (st : Protocol.NamedStore V) (P : Block V) : Prop :=
  Block.compatible
    (Protocol.get_fg_root st.toHealing.toFG) P = false

/-- The FG root of the store is a strict ancestor of `P`, but `P` is not in the filtered block tree. -/
def HeightFilterInterferenceAt (st : Protocol.NamedStore V) (P : Block V) : Prop :=
  Block.Prec (Protocol.get_fg_root st.toHealing.toFG) P ∧
    P ∉ Protocol.get_filtered_block_tree st.toHealing.toFG


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
