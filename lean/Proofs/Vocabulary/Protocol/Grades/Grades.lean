module
public import Proofs.Vocabulary.Internal.Definitions.PhaseGradeQueries
public import Proofs.Vocabulary.Protocol.Grades.Anchor
public import Proofs.Vocabulary.Protocol.Grades.GradeCutoffMono
import Proofs.Vocabulary.Objects.Weights
import Proofs.Vocabulary.Protocol.ChainState.AlignedRoundLemmas
import Proofs.Vocabulary.Protocol.ValidatorClient.Engine
import Mathlib.Tactic.ENatToNat

@[expose] public section


namespace DecoupledConsensusModel
namespace Proofs
namespace HealingLemmas

open Protocol (GradeView HealConfig)
open Protocol (SGVote)

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Weight monotonicity -/

/-- Weight is monotone along an implication between two decidable filters over `V`. -/
theorem weightOf_filter_mono (E : Env V) {p q : V → Prop} [DecidablePred p]
    [DecidablePred q] (h : ∀ v, p v → q v) :
    E.electorate.weightOf (Finset.univ.filter p) ≤
      E.electorate.weightOf (Finset.univ.filter q) :=
  E.electorate.weightOf_mono (fun i hi =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ i, h i (Finset.mem_filter.mp hi).2⟩)

/-! ## The cutoff order -/

/-- `Γ_r^{−1} < Γ_r^0`. -/
theorem Γ_neg1_lt_Γ_0 (hc : HealConfig) {Δ : Time} (hΔ : 0 < Δ) (r : Round) :
    hc.Γ_neg1 Δ r < hc.Γ_0 Δ r := by
  have key : ∀ a d : Int, 0 < d → a - d < a := by intro a d h; omega
  exact key (slotStart Δ (hc.opening_slot r)) Δ hΔ

/-- `Γ_r^0 < Γ_r^1`. -/
theorem Γ_0_lt_Γ_1 (hc : HealConfig) {Δ : Time} (hΔ : 0 < Δ) (r : Round) :
    hc.Γ_0 Δ r < hc.Γ_1 Δ r := by
  have key : ∀ a d : Int, 0 < d → a < a + d := by intro a d h; omega
  exact key (slotStart Δ (hc.opening_slot r)) Δ hΔ

/-! ## Root resolution -/


omit [Fintype V] in
/-- Root resolution returns a member of the tree. -/
theorem find?_mem {T : Finset (Block V)} {root : BlockId} {H : Block V}
    (h : Block.find? T root = some H) : H ∈ T := by
  unfold Block.find? at h
  exact Proofs.Engine.pickUnique?_mem h

omit [Fintype V] in
/-- Root resolution returns a block with the requested root. -/
theorem find?_root {T : Finset (Block V)} {root : BlockId} {H : Block V}
    (h : Block.find? T root = some H) : H.root = root := by
  unfold Block.find? pickUnique? at h
  split at h
  · rename_i hex
    rw [Option.some_inj] at h
    subst h
    exact of_decide_eq_true (Finset.choose_property _ _ hex)
  · exact absurd h (by simp)

omit [Fintype V] in
/-- A head root that covers `B` resolves in `T` to a member that is a descendant of `B`. -/
theorem exists_head_of_head_covers {T : Finset (Block V)} {B : Block V}
    {H : Option BlockId} (h : Protocol.head_covers T B H = true) :
    ∃ (root : BlockId) (head : Block V), H = some root ∧
      Block.find? T root = some head ∧ head ∈ T ∧ Block.preceq B head = true := by
  cases H with
  | none => exact absurd h (by simp [Protocol.head_covers])
  | some root =>
    simp only [Protocol.head_covers] at h
    cases hf : Block.find? T root with
    | none => rw [hf] at h; exact absurd h (by simp)
    | some head =>
      rw [hf] at h
      exact ⟨root, head, rfl, hf, find?_mem hf, h⟩


omit [Fintype V] in
/-- `Block.deepest?` is a descendant of every member of its set that is compatible with it. -/
theorem deepest?_dominates {T : Finset (Block V)} {L B : Block V}
    (hL : Block.deepest? T = some L) (hB : B ∈ T)
    (hcmp : Block.compatible B L = true) : Block.preceq B L = true := by
  have hLmem : L ∈ T := Proofs.Engine.deepest?_mem hL
  have hdeep : Block.isDeepestIn T L = true := by
    unfold Block.deepest? pickUnique? at hL
    split at hL
    · rename_i hex
      rw [Option.some_inj] at hL
      subst hL
      exact Finset.choose_property _ _ hex
    · exact absurd hL (by simp)
  simp only [Block.isDeepestIn, decide_eq_true_eq] at hdeep
  have hBL := hdeep B hB
  simp only [Block.deeper, Bool.or_eq_false_iff, Bool.and_eq_false_imp,
    decide_eq_false_iff_not, Nat.not_lt] at hBL
  exact AlignedRoundLemmas.preceq_of_compatible_of_depth_le hcmp hBL.1


/-- A head root is compatible with `B` when it is empty, does not resolve in `T`, or resolves to a
    block compatible with `B`. -/
def rootCompatible (T : Finset (Block V)) (B : Block V) : Option BlockId → Bool
  | none => true
  | some root =>
    match Block.find? T root with
    | some H => Block.compatible H B
    | none => true


end HealingLemmas
end Proofs
end DecoupledConsensusModel

end
