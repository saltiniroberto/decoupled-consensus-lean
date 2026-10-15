module
public import Model.Vocabulary.Execution.Node
import Proofs.Vocabulary.Protocol.Grades.Grades
import Proofs.Vocabulary.Protocol.ValidatorClient.Engine
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

@[expose] public section


namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Protocol (GradeView HealConfig)
open Internal
open Execution
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The deepest block of a chain -/

omit [Fintype V] in
/-- Two blocks of equal depth in a set of ancestors of one block `C` are equal. -/
theorem eq_of_depth_eq_of_chain {T : Finset (Block V)} {C : Block V}
    (hchain : ∀ X ∈ T, Block.preceq X C = true) {X Y : Block V}
    (hX : X ∈ T) (hY : Y ∈ T) (hd : X.depth = Y.depth) : X = Y := by
  rcases Block.preceq_linear (hchain X hX) (hchain Y hY) with h | h
  · exact Block.preceq_eq_of_depth_le h (le_of_eq hd.symm)
  · exact (Block.preceq_eq_of_depth_le h (le_of_eq hd)).symm

omit [Fintype V] in
/-- On a nonempty set of ancestors of one block, `Block.deepest?` returns a block. -/
theorem deepest?_isSome_of_chain {T : Finset (Block V)} {C : Block V}
    (hchain : ∀ X ∈ T, Block.preceq X C = true) (hne : T.Nonempty) :
    (Block.deepest? T).isSome = true := by
  obtain ⟨L, hLmem, hLeq⟩ := Finset.exists_mem_eq_sup' hne Block.depth
  have hLmax : ∀ X ∈ T, X.depth ≤ L.depth := by
    intro X hX
    rw [← hLeq]
    exact Finset.le_sup' Block.depth hX
  have hdeepL : Block.isDeepestIn T L = true := by
    simp only [Block.isDeepestIn, decide_eq_true_eq]
    intro X hX
    simp only [Block.deeper, Bool.or_eq_false_iff, Bool.and_eq_false_imp,
      decide_eq_false_iff_not, Nat.not_lt]
    refine ⟨hLmax X hX, ?_⟩
    intro heq
    have hXL : X = L :=
      eq_of_depth_eq_of_chain hchain hX hLmem (of_decide_eq_true heq).symm
    subst hXL
    simp
  have hex : ∃! a, a ∈ T ∧ Block.isDeepestIn T a = true := by
    refine ⟨L, ⟨hLmem, hdeepL⟩, ?_⟩
    rintro L' ⟨hL'mem, hL'deep⟩
    simp only [Block.isDeepestIn, decide_eq_true_eq] at hL'deep
    have hLL' := hL'deep L hLmem
    simp only [Block.deeper, Bool.or_eq_false_iff, Bool.and_eq_false_imp,
      decide_eq_false_iff_not, Nat.not_lt] at hLL'
    exact eq_of_depth_eq_of_chain hchain hL'mem hLmem
      (le_antisymm (hLmax L' hL'mem) hLL'.1)
  unfold Block.deepest? pickUnique?
  rw [dif_pos hex]
  rfl

omit [Fintype V] in
/-- `deepest_clear floor C test` returns a block when some `B` in `chain_of C` passes `test` and, if
    `floor` is a block, is a descendant of it. -/
theorem deepest_clear_isSome_of_mem {floor : Option (Block V)} {C B : Block V}
    {test : Block V → Bool} (hfloor : floor.elim True (fun a => Block.preceq a B = true))
    (hB : B ∈ Protocol.chain_of C) (htest : test B = true) :
    (Protocol.deepest_clear floor C test).isSome = true := by
  refine deepest?_isSome_of_chain (C := C) ?_ ⟨B, ?_⟩
  · intro X hX
    exact Proofs.Engine.mem_chain_of_preceq (List.mem_toFinset.mp (Finset.mem_filter.mp hX).1)
  · refine Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hB, ?_, htest⟩
    cases floor with
    | none => rfl
    | some a => simpa using hfloor

omit [Fintype V] in
/-- On a nonempty pairwise-compatible set, `Block.deepest?` returns a block. -/
theorem deepest?_isSome_of_compatible {T : Finset (Block V)}
    (hcmp : ∀ X ∈ T, ∀ Y ∈ T, Block.compatible X Y = true) (hne : T.Nonempty) :
    (Block.deepest? T).isSome = true := by
  obtain ⟨L, hLmem, hLeq⟩ := Finset.exists_mem_eq_sup' hne Block.depth
  have hLmax : ∀ X ∈ T, X.depth ≤ L.depth := by
    intro X hX
    rw [← hLeq]
    exact Finset.le_sup' Block.depth hX
  refine deepest?_isSome_of_chain (C := L) ?_ hne
  intro X hX
  have hc := hcmp X hX L hLmem
  simp only [Block.compatible, Bool.or_eq_true] at hc
  rcases hc with h | h
  · exact h
  · have : L = X := Block.preceq_eq_of_depth_le h (hLmax X hX)
    subst this
    exact Block.preceq_self _


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
