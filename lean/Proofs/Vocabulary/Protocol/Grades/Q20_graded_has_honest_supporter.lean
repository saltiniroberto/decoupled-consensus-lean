module
public import Proofs.Vocabulary.Protocol.Grades.Grades
import Proofs.Vocabulary.Objects.Weights
import Mathlib.Tactic.ENatToNat

@[expose] public section

/-!
# Support or opposition

A token view whose early set is non-empty and contained in its late set either supports or opposes a
block.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingLemmas
namespace Rows

open Internal.PhaseGrades DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol (Token Supports Opposes CleanFrom)

variable {V : Type} [DecidableEq V] [Fintype V]

/-- A token view whose early set is non-empty and contained in its late set supports or opposes `B`. -/
theorem supports_or_opposes {Key Blk : Type*} (c : Key → Blk → Prop)
    (early late raw : Finset (Token Key)) (B : Blk)
    (hne : early.Nonempty) (hsub : early ⊆ late) :
    Supports c early late raw B ∨ Opposes c early late raw B := by
  classical
  obtain ⟨u, hu, hmax⟩ := Finset.exists_max_image early (fun t => t.round) hne
  by_cases hcov : c u.key B
  · by_cases hclean : CleanFrom raw u.round
    · by_cases hsweep : ∀ x ∈ late, u.round < x.round → c x.key B
      · exact Or.inl ⟨u, hu, hmax, hcov, hclean, hsweep⟩
      · push_neg at hsweep
        obtain ⟨x, hx, hlt, hncov⟩ := hsweep
        exact Or.inr (Or.inl ⟨x, hx, fun v hv => le_trans (hmax v hv) hlt.le, hncov⟩)
    · unfold CleanFrom at hclean
      push_neg at hclean
      obtain ⟨x, hx, y, hy, hle, heq, hkey⟩ := hclean
      exact Or.inr (Or.inr ⟨x, hx, y, hy, fun v hv => le_trans (hmax v hv) hle, heq, hkey⟩)
  · exact Or.inr (Or.inl ⟨u, hsub hu, hmax, hcov⟩)


end Rows
end HealingLemmas
end Proofs
end DecoupledConsensusModel

end
