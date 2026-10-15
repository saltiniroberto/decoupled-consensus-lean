module
public import Proofs.Vocabulary.Execution.Runtime
public import Proofs.Vocabulary.Execution.Wire
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

@[expose] public section

/-!
# Named ancestry of run blocks

In an admissible run, erased ancestry between run blocks gives named ancestry.
-/

namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]


/-- In an admissible run, a run block `X` whose erasure is an ancestor of the erasure of a run block
    `B` is a named ancestor of `B`. -/
theorem namedPreceq_of_runBlock_erase_preceq
    {S : Setup V} {rho : Run V}
    (adm : Admissible S rho) {X B : NamedBlock V}
    (hXrun : RunBlock S rho X) (hBrun : RunBlock S rho B)
    (h : Block.Preceq X.erase B.erase) :
    NamedBlock.Preceq X B := by
  obtain ⟨A, hAB, hAerase⟩ := Proofs.NamedAncestry.erased_ancestor_lift B h
  have hArun : RunBlock S rho A :=
    Proofs.NamedRuntime.blockInRun_of_ancestor S rho hBrun hAB
  have hrootEq : A.root = X.root := by
    rw [← Proofs.NamedWire.erase_root A, ← Proofs.NamedWire.erase_root X, hAerase]
  have hAX : A = X :=
    adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective
      A X hArun hXrun A X
      (Or.inl (Proofs.NamedAncestry.named_self A)) (Or.inr (Proofs.NamedAncestry.named_self X))
      hrootEq
  rw [← hAX]
  exact hAB


end Protocol
end DecoupledConsensusModel

end
