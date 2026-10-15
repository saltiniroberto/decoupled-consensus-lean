module
public import Model.Vocabulary.Objects.Blocks
import Proofs.Vocabulary.Objects.Ancestry
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
public import Model.Vocabulary.Execution.Objects
public import Mathlib.Data.DFinsupp.Notation
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Finsupp.Notation
public import Proofs.Vocabulary.Internal.Legacy.Definitions.LeakLedger

@[expose] public section

/-!
# Compatibility through an ancestor

An ancestor of a block compatible with `B` is compatible with `B`.
-/

namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]


omit [Fintype V] in
/-- If `A` is an ancestor of `C` and `C` is compatible with `B`, then `A` is compatible with `B`. -/
theorem compatible_of_preceq_of_compatible {A C B : Block V}
    (hAC : Block.Preceq A C) (hCB : Block.compatible C B = true) :
    Block.compatible A B = true := by
  simp only [Block.compatible, Bool.or_eq_true] at hCB ⊢
  rcases hCB with hCB | hBC
  · exact Or.inl (Block.preceq_trans hAC hCB)
  · simpa only [Block.compatible, Bool.or_eq_true] using
      (Block.compatible_of_preceq_common hAC hBC)


#print axioms compatible_of_preceq_of_compatible

end Protocol
end DecoupledConsensusModel

end
