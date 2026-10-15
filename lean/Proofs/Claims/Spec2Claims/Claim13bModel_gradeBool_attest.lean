import Proofs.Vocabulary.Protocol.Grades.Grades
import Proofs.Claims.ModelIrreducible

/-!
# Facts about `Protocol.gradeBool`: two graded blocks of one phase

A lemma that unfolds `Protocol.gradeBool` at a phase's two cutoffs `Protocol.early E hc r p` and
`Protocol.late E hc r p`: the blocks graded at one phase of one round lie on one chain.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Block.compatible
  DecoupledConsensusModel.Block.preceq DecoupledConsensusModel.Protocol.gradeBool

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- If the grade view `gv` grades both `B` and `B'` for round `r` with the cutoffs of the phase `p`,
    then `B` and `B'` lie on one chain. -/
theorem compatible_of_gradeBool_phase (E : Env V) (hc : Protocol.HealConfig)
    (gv : Protocol.GradeView V) (F : Block V) (r : Round) (p : Protocol.Phase)
    {B B' : Block V}
    (hB : Protocol.gradeBool E gv F hc.η_SG r (Protocol.early E hc r p)
      (Protocol.late E hc r p) B = true)
    (hB' : Protocol.gradeBool E gv F hc.η_SG r (Protocol.early E hc r p)
      (Protocol.late E hc r p) B' = true) :
    Block.compatible B B' = true := by
  by_contra hne
  have hcompatBB' : Block.compatible B B' = false := by
    cases h : Block.compatible B B' with
    | false => rfl
    | true => exact absurd h hne
  have hcompatB'B : Block.compatible B' B = false := by
    simp only [Block.compatible, Bool.or_eq_false_iff] at hcompatBB' ⊢
    exact ⟨hcompatBB'.2, hcompatBB'.1⟩
  have hconfBB' : Block.conflicts B B' = true := by
    simp [Block.conflicts, hcompatBB']
  have hconfB'B : Block.conflicts B' B = true := by
    simp [Block.conflicts, hcompatB'B]
  simp only [Protocol.gradeBool, decide_eq_true_eq] at hB hB'
  have hPB : ∀ v, Protocol.positive gv F hc.η_SG r (Protocol.early E hc r p)
      (Protocol.late E hc r p) v B = true →
      Protocol.opposing gv F hc.η_SG r (Protocol.early E hc r p)
        (Protocol.late E hc r p) v B' = true :=
    fun v hv => Proofs.GradeCutoffMono.opposing_of_positive_conflicts E hc gv F r p v hconfBB' hv
  have hPB' : ∀ v, Protocol.positive gv F hc.η_SG r (Protocol.early E hc r p)
      (Protocol.late E hc r p) v B' = true →
      Protocol.opposing gv F hc.η_SG r (Protocol.early E hc r p)
        (Protocol.late E hc r p) v B = true :=
    fun v hv => Proofs.GradeCutoffMono.opposing_of_positive_conflicts E hc gv F r p v hconfB'B hv
  exact absurd (lt_of_le_of_lt (Proofs.HealingLemmas.weightOf_filter_mono E hPB)
    (lt_of_lt_of_le hB' (Proofs.HealingLemmas.weightOf_filter_mono E hPB'))) (lt_asymm hB)

end DecoupledConsensusModel.Sts
