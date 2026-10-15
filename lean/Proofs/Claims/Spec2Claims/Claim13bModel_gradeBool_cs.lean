import Proofs.Claims.Spec2Claims.Claim13bModel_gradeBool
import Proofs.Vocabulary.Protocol.Grades.Grades

/-!
# Facts about `Protocol.gradeBool`: a graded block has a descendant in the tree

Lemmas that unfold `Protocol.gradeBool`, `Protocol.head_covers` and `weightOf`. A graded block has a
supporter, and a supporter's witness token resolves in the view's tree to a descendant of the block.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Block.Preceq
  DecoupledConsensusModel.Block.find? DecoupledConsensusModel.Electorate.weightOf
  DecoupledConsensusModel.Protocol.gradeBool DecoupledConsensusModel.Protocol.head_covers

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- If the key `key` covers `B` in the tree `T`, then `T` holds a block `H` with `B ⪯ H`. -/
theorem exists_mem_preceq_of_head_covers {T : Finset (Block V)} {B : Block V}
    {key : Option BlockId} (h : Protocol.head_covers T B key = true) :
    ∃ H ∈ T, Block.Preceq B H := by
  unfold Protocol.head_covers at h
  split at h
  · exact absurd h (by decide)
  · split at h
    · rename_i head hfind
      exact ⟨head, Proofs.HealingLemmas.find?_mem hfind, h⟩
    · exact absurd h (by decide)

/-- If the grade view `gv` grades `B`, then `gv.T` holds a block `H` with `B ⪯ H`. -/
theorem exists_mem_T_preceq_of_gradeBool (E : Env V) (gv : Protocol.GradeView V) (F : Block V)
    (η r : Round) (early late : Time) (B : Block V)
    (h : Protocol.gradeBool E gv F η r early late B = true) :
    ∃ H ∈ gv.T, Block.Preceq B H := by
  unfold Protocol.gradeBool at h
  rw [decide_eq_true_eq] at h
  have hpos : (Finset.univ.filter
      (fun v => Protocol.positive gv F η r early late v B = true)).Nonempty := by
    apply Finset.nonempty_of_sum_ne_zero (f := E.electorate.weight)
    have h' := h
    unfold Electorate.weightOf at h'
    omega
  obtain ⟨u, hu⟩ := hpos
  have hpu := (Finset.mem_filter.1 hu).2
  obtain ⟨u₀, -, -, hcov, -, -⟩ := conditions_of_positive gv F η r early late u B hpu
  exact exists_mem_preceq_of_head_covers hcov

end DecoupledConsensusModel.Sts
