module
public import Proofs.Claims.Spec2Claims.Claim13bModel_gradeBool

@[expose] public section

/-!
# Facts about `Protocol.gradeBool`: a block opposed by a heavier side

Lemmas that unfold `Protocol.gradeBool`, `Protocol.positive`, `Protocol.opposing`,
`Protocol.localCovers` and `Protocol.head_covers`, at any two cutoffs `early ≤ late`. A validator
that supports a block `B` opposes every block not on one chain with `B`, and a block whose
supporters do not outweigh its opposers is not graded.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Block.Compatible
  DecoupledConsensusModel.Protocol.Opposes DecoupledConsensusModel.Protocol.gradeBool
  DecoupledConsensusModel.Protocol.head_covers DecoupledConsensusModel.Protocol.interpretedInputs
  DecoupledConsensusModel.Protocol.localCovers DecoupledConsensusModel.Protocol.opposing
  DecoupledConsensusModel.Protocol.rawInputs DecoupledConsensusModel.Protocol.rawView
  DecoupledConsensusModel.Protocol.readyView

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Proofs.GradeCutoffMono

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- If the key `key` covers both `B` and `B'` in the tree `T`, then `B` and `B'` lie on one chain. -/
theorem compatible_of_head_covers_two {T : Finset (Block V)} {B B' : Block V}
    {key : Option BlockId} (h : Protocol.head_covers T B key = true)
    (h' : Protocol.head_covers T B' key = true) :
    Block.compatible B B' = true := by
  cases key with
  | none => simp [Protocol.head_covers] at h
  | some root =>
    simp only [Protocol.head_covers] at h h'
    cases hf : Block.find? T root with
    | none => simp [hf] at h
    | some head =>
      simp only [hf] at h h'
      exact Block.compatible_of_preceq_common h h'

/-- If `early ≤ late`, `u` supports `B` in the grade view, and `B'` is not on one chain with `B`,
    then `u` opposes `B'`. -/
theorem opposing_of_positive_not_compatible (gv : Protocol.GradeView V) (F : Block V)
    (η r : Round) (early late : Time) (u : V) {B B' : Block V} (hel : early ≤ late)
    (hBB' : ¬ Block.Compatible B B')
    (h : Protocol.positive gv F η r early late u B = true) :
    Protocol.opposing gv F η r early late u B' = true := by
  obtain ⟨u₀, hmem, hlatest, hcov, -, -⟩ := conditions_of_positive gv F η r early late u B h
  unfold Protocol.opposing
  rw [decide_eq_true_eq]
  refine Or.inl ⟨u₀, readyView_mono gv F η r hel u hmem, hlatest, ?_⟩
  intro hcovB'
  have hcovB'' : Protocol.head_covers gv.T B' u₀.key = true := by
    simpa only [Protocol.localCovers] using hcovB'
  exact hBB' (compatible_of_head_covers_two hcov hcovB'')

/-- If the validators that support `B` in the grade view weigh at most as much as those that oppose
    it, then the view does not grade `B`. -/
theorem gradeBool_eq_false_of_weight_le (E : Env V) (gv : Protocol.GradeView V) (F : Block V)
    (η r : Round) (early late : Time) (B : Block V)
    (h : E.electorate.weightOf
        (Finset.univ.filter fun u => Protocol.positive gv F η r early late u B = true)
      ≤ E.electorate.weightOf
        (Finset.univ.filter fun u => Protocol.opposing gv F η r early late u B = true)) :
    Protocol.gradeBool E gv F η r early late B = false := by
  unfold Protocol.gradeBool
  rw [decide_eq_false_iff_not, not_lt]
  exact h

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- If the token `x` is in `u`'s ready view at the cutoff `late`, every token of `u`'s ready view at
    the cutoff `early` has a round at most `x`'s, and `x`'s key does not cover `B` in `gv`'s tree,
    then `u` opposes `B`. -/
theorem opposing_of_late_not_covers (gv : Protocol.GradeView V) (F : Block V) (η r : Round)
    (early late : Time) (u : V) (B : Block V) {x : Protocol.Token (Option BlockId)}
    (hx : x ∈ Protocol.readyView gv F η r late u)
    (hle : ∀ y ∈ Protocol.readyView gv F η r early u, y.round ≤ x.round)
    (hnot : ¬ Protocol.head_covers gv.T B x.key = true) :
    Protocol.opposing gv F η r early late u B = true := by
  unfold Protocol.opposing Protocol.localCovers
  exact decide_eq_true (Or.inl ⟨x, hx, hle, hnot⟩)

end DecoupledConsensusModel.Sts
