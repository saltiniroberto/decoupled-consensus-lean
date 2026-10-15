module
public import Proofs.Vocabulary.Protocol.Grades.Grades

@[expose] public section

/-!
# Facts about `Protocol.gradeBool`

The executable local grade of a block.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

variable {V : Type} [DecidableEq V] [Fintype V]

/-- If the local grade of `Q` at `st` passes, `Q` is an ancestor of some block of `st`'s tree. -/
theorem exists_mem_T_preceq_of_gradeBool (E : Env V) (st : Protocol.HealingStore V)
    (F : Block V) (eta r : Round) (early late : Time) {Q : Block V}
    (h : DecoupledConsensusModel.Protocol.gradeBool E st.gradeView F eta r early late Q = true) :
    ∃ H ∈ st.T, Block.Preceq Q H := by
  simp only [DecoupledConsensusModel.Protocol.gradeBool, decide_eq_true_eq] at h
  have hne : (Finset.univ.filter fun s =>
      DecoupledConsensusModel.Protocol.positive st.gradeView F eta r early late s Q =
        true).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty.mp hempty] at h
    simp only [Electorate.weightOf, Finset.sum_empty] at h
    omega
  obtain ⟨s, hs⟩ := hne
  obtain ⟨tok, -, -, hcov, -, -⟩ := by
    simpa only [DecoupledConsensusModel.Protocol.positive, decide_eq_true_eq] using
      (Finset.mem_filter.mp hs).2
  cases hkey : tok.key with
  | none =>
    simp [DecoupledConsensusModel.Protocol.localCovers, Protocol.head_covers, hkey] at hcov
  | some root =>
    cases hfind : Block.find? st.gradeView.T root with
    | none =>
      simp [DecoupledConsensusModel.Protocol.localCovers, Protocol.head_covers, hkey,
        hfind] at hcov
    | some H =>
      have hQH : Block.Preceq Q H := by
        simpa [DecoupledConsensusModel.Protocol.localCovers, Protocol.head_covers,
          hkey, hfind, Block.Preceq] using hcov
      exact ⟨H, Proofs.HealingLemmas.find?_mem hfind, hQH⟩

end DecoupledConsensusModel.Proofs.ModelProperties

end
