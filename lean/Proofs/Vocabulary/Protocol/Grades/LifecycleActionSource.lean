module
public import Proofs.Vocabulary.Protocol.Grades.VoteBelowSource
import Proofs.Vocabulary.Protocol.Grades.Grades
import Proofs.Vocabulary.Protocol.ValidatorClient.Engine
import Mathlib.Data.Rat.Floor
public import Proofs.Vocabulary.Internal.Internal.GradeReads

@[expose] public section

/-!
# The deepest clear block at a clear tip

`deepest_clear` selects the tip `C` itself when `C` passes the test and the floor is an ancestor of
`C`.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Protocol (HeightConfig)
open Protocol (own_lock)
open Internal
open Execution
open Internal.HealingSurface
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

set_option maxHeartbeats 300000

/-- `deepest_clear floor C test` is `C` when `C` passes `test` and `floor`, when present, is an
    ancestor of `C`. -/
theorem deepest_clear_eq_tip {floor : Option (Block V)} {C : Block V}
    {test : Block V → Bool}
    (hfloor : floor.elim True (fun a => Block.preceq a C = true))
  (htest : test C = true) :
    Protocol.deepest_clear floor C test = some C := by
  have hmem : C ∈ Protocol.chain_of C := by
    cases C with
    | genesis => simp [Protocol.chain_of, Protocol.chain_up, Block.depth]
    | node p s r gv gsv ats i =>
        simp [Protocol.chain_of, Protocol.chain_up, Block.depth, Block.parent?]
  have hsome : (Protocol.deepest_clear floor C test).isSome = true :=
    deepest_clear_isSome_of_mem hfloor hmem htest
  obtain ⟨L, hL⟩ := Option.isSome_iff_exists.mp hsome
  have hCmem : C ∈ ((Protocol.chain_of C).toFinset.filter (fun B =>
      floor.elim true (fun anchor => Block.preceq anchor B) = true ∧
        test B = true)) := by
    refine Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hmem, ?_, htest⟩
    cases floor with
    | none => rfl
    | some a => simpa using hfloor
  have hLC : Block.Preceq L C := Proofs.Engine.deepest_clear_preceq hL
  have hCL : Block.Preceq C L := by
    refine deepest?_dominates hL hCmem ?_
    exact Block.compatible_of_preceq_common (Block.preceq_self C) hLC
  have hEq : L = C := Block.preceq_antisymm hLC hCL
  simpa [hEq] using hL


#print axioms deepest_clear_eq_tip

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
