import Proofs.Vocabulary.Protocol.Grades.VoteBelowSource
import Proofs.Claims.ModelIrreducible

/-!
# Facts about `Protocol.freezeRoot`

The frozen root of a phase: the deepest block of the view's tree that passes `Protocol.gradeBool`.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Block.Preceq
  DecoupledConsensusModel.Protocol.freezeRoot

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- If `X` is in the view's tree and passes the grade test, and every two such blocks are
    compatible, then the frozen root is some block `D` with `X ⪯ D`. -/
theorem preceq_freezeRoot (E : Env V) (gv : Protocol.GradeView V) (F : Block V)
    (η r : Round) (early late : Time) {X : Block V} (hXT : X ∈ gv.T)
    (hX : Protocol.gradeBool E gv F η r early late X = true)
    (hcmp : ∀ D ∈ gv.T, ∀ D' ∈ gv.T, Protocol.gradeBool E gv F η r early late D = true →
      Protocol.gradeBool E gv F η r early late D' = true → Block.compatible D D' = true) :
    ∃ D : Block V, Protocol.freezeRoot E gv F η r early late = some D ∧ Block.Preceq X D := by
  unfold Protocol.freezeRoot
  have hXm : X ∈ gv.T.filter (fun B => Protocol.gradeBool E gv F η r early late B = true) :=
    Finset.mem_filter.2 ⟨hXT, hX⟩
  have hcmp' : ∀ A ∈ gv.T.filter (fun B => Protocol.gradeBool E gv F η r early late B = true),
      ∀ B ∈ gv.T.filter (fun B => Protocol.gradeBool E gv F η r early late B = true),
      Block.compatible A B = true := by
    intro A hA B hB
    exact hcmp A (Finset.mem_filter.1 hA).1 B (Finset.mem_filter.1 hB).1
      (Finset.mem_filter.1 hA).2 (Finset.mem_filter.1 hB).2
  have hsome := Proofs.HealingSurface.deepest?_isSome_of_compatible hcmp' ⟨X, hXm⟩
  obtain ⟨D, hD⟩ := Option.isSome_iff_exists.1 hsome
  exact ⟨D, hD, Proofs.HealingLemmas.deepest?_dominates hD hXm
    (hcmp' X hXm D (Proofs.Engine.deepest?_mem hD))⟩

/-- If the frozen root of the grade view `gv` is `D`, then `D` is in the tree of `gv`. -/
theorem mem_T_of_freezeRoot_eq_some {E : Env V} {gv : Protocol.GradeView V} {F : Block V}
    {η r : Round} {early late : Time} {D : Block V}
    (h : Protocol.freezeRoot E gv F η r early late = some D) : D ∈ gv.T := by
  unfold Protocol.freezeRoot at h
  exact (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem h)).1

/-- If the frozen root of `gv` is some block `D`, then `D` passes the grade test
    `Protocol.gradeBool` with the same arguments. -/
theorem gradeBool_of_freezeRoot_eq_some {E : Env V} {gv : Protocol.GradeView V} {F : Block V}
    {η r : Round} {early late : Time} {D : Block V}
    (h : Protocol.freezeRoot E gv F η r early late = some D) :
    Protocol.gradeBool E gv F η r early late D = true := by
  unfold Protocol.freezeRoot at h
  exact (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem h)).2

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

omit [DecidableEq V] [Fintype V] in
/-- A root `Protocol.freezeRoot` returns passes `Protocol.gradeBool`. -/
theorem gradeBool_of_freezeRoot [DecidableEq V] [Fintype V] {E : Env V}
    {gv : Protocol.GradeView V} {F : Block V} {eta r₁ : Round} {t_0 t_1 : Int} {B : Block V}
    (h : Protocol.freezeRoot E gv F eta r₁ t_0 t_1 = some B) :
    Protocol.gradeBool E gv F eta r₁ t_0 t_1 B = true := by
  unfold Protocol.freezeRoot at h
  exact (Finset.mem_filter.1 (Proofs.Engine.deepest?_mem h)).2

end DecoupledConsensusModel.Sts
