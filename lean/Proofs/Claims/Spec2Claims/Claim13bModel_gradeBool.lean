module

public import Proofs.Vocabulary.Protocol.Grades.GradeCutoffMono
public import Proofs.Vocabulary.Objects.Weights
public import Proofs.Claims.ModelIrreducible
public import Proofs.Claims.Spec2Claims.Claim13bModel_CleanFrom
public import Proofs.Claims.Spec2Claims.Claim13bModel_Opposes
public import Proofs.Claims.Spec2Claims.Claim13bModel_Supports

@[expose] public section

/-!
# Facts about `Protocol.gradeBool`

Lemmas that unfold the executable grade `Protocol.gradeBool` and the definitions it reads
(`Protocol.positive`, `Protocol.opposing`, `Protocol.Supports`, `Protocol.Opposes`,
`Protocol.CleanFrom`, `Protocol.rawView`, `Protocol.readyView`). A grade view grades a block `B`
when the weight of the validators opposing `B` is strictly less than the weight of those supporting
it.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.CleanFrom
  DecoupledConsensusModel.Protocol.Opposes DecoupledConsensusModel.Protocol.Supports
  DecoupledConsensusModel.Protocol.gradeBool DecoupledConsensusModel.Protocol.head_covers
  DecoupledConsensusModel.Protocol.interpretedInputs DecoupledConsensusModel.Protocol.latest_window
  DecoupledConsensusModel.Protocol.localCovers DecoupledConsensusModel.Protocol.opposing
  DecoupledConsensusModel.Protocol.positive DecoupledConsensusModel.Protocol.rawInputs
  DecoupledConsensusModel.Protocol.rawView DecoupledConsensusModel.Protocol.readyView

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Proofs.GradeCutoffMono

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- `Protocol.positive` holds for `u` and `B` when some token `u₀` of `u`'s early ready view has the
    largest round in that view, covers `B` in `gv.T`, no two raw tokens of `u` at the late cutoff of
    one round at least `u₀`'s carry different keys, and every late ready token of `u` of a larger
    round covers `B`. -/
theorem positive_of_conditions (gv : Protocol.GradeView V) (F : Block V) (η r : Round)
    (early late : Time) (u : V) (B : Block V) (u₀ : Protocol.Token (Option BlockId))
    (hmem : u₀ ∈ Protocol.readyView gv F η r early u)
    (hlatest : ∀ x ∈ Protocol.readyView gv F η r early u, x.round ≤ u₀.round)
    (hcov : Protocol.head_covers gv.T B u₀.key = true)
    (hclean : ∀ x ∈ Protocol.rawView gv η r late u, ∀ y ∈ Protocol.rawView gv η r late u,
      u₀.round ≤ x.round → x.round = y.round → x.key = y.key)
    (hlater : ∀ x ∈ Protocol.readyView gv F η r late u, u₀.round < x.round →
      Protocol.head_covers gv.T B x.key = true) :
    Protocol.positive gv F η r early late u B = true := by
  unfold Protocol.positive
  rw [decide_eq_true_eq]
  exact ⟨u₀, hmem, hlatest, hcov, hclean, hlater⟩

omit [Fintype V] in
/-- The converse of `positive_of_conditions`: if `u` supports `B` in the grade view, the four
    conditions hold for some token of `u`'s early ready view. -/
theorem conditions_of_positive (gv : Protocol.GradeView V) (F : Block V) (η r : Round)
    (early late : Time) (u : V) (B : Block V)
    (h : Protocol.positive gv F η r early late u B = true) :
    ∃ u₀ ∈ Protocol.readyView gv F η r early u,
      (∀ x ∈ Protocol.readyView gv F η r early u, x.round ≤ u₀.round) ∧
      Protocol.head_covers gv.T B u₀.key = true ∧
      (∀ x ∈ Protocol.rawView gv η r late u, ∀ y ∈ Protocol.rawView gv η r late u,
        u₀.round ≤ x.round → x.round = y.round → x.key = y.key) ∧
      (∀ x ∈ Protocol.readyView gv F η r late u, u₀.round < x.round →
        Protocol.head_covers gv.T B x.key = true) := by
  unfold Protocol.positive at h
  rw [decide_eq_true_eq] at h
  exact h

/-- If `early ≤ late` and `u` supports `B` in the grade view, then `u` does not oppose `B` there. -/
theorem opposing_false_of_positive (gv : Protocol.GradeView V) (F : Block V) (η r : Round)
    (early late : Time) (u : V) (B : Block V) (hel : early ≤ late)
    (h : Protocol.positive gv F η r early late u B = true) :
    Protocol.opposing gv F η r early late u B = false := by
  obtain ⟨u₀, hmem, hlatest, hcov, hclean, hlater⟩ :=
    conditions_of_positive gv F η r early late u B h
  have hu₀raw : u₀ ∈ Protocol.rawView gv η r late u :=
    rawView_mono gv η r hel u (readyView_subset_rawView gv F η r early u hmem)
  unfold Protocol.opposing
  rw [decide_eq_false_iff_not]
  rintro (⟨x, hx, hge, hnot⟩ | ⟨x, hx, y, hy, hge, hround, hkey⟩)
  · have hxraw := readyView_subset_rawView gv F η r late u hx
    have hle : u₀.round ≤ x.round := hge u₀ hmem
    rcases Nat.lt_or_eq_of_le hle with hlt | heq
    · exact hnot (hlater x hx hlt)
    · have hk : u₀.key = x.key := hclean u₀ hu₀raw x hxraw le_rfl heq
      apply hnot
      simpa only [Protocol.localCovers, ← hk] using hcov
  · exact hkey (hclean x hx y hy (hge u₀ hmem) hround)

/-- If `u` opposes `B` in the grade view, then `u`'s raw view at the late cutoff is nonempty. -/
theorem rawView_nonempty_of_opposing (gv : Protocol.GradeView V) (F : Block V) (η r : Round)
    (early late : Time) (u : V) (B : Block V)
    (h : Protocol.opposing gv F η r early late u B = true) :
    (Protocol.rawView gv η r late u).Nonempty := by
  unfold Protocol.opposing at h
  rw [decide_eq_true_eq] at h
  rcases h with ⟨x, hx, -⟩ | ⟨x, hx, -⟩
  · exact ⟨x, readyView_subset_rawView gv F η r late u hx⟩
  · exact ⟨x, hx⟩

/-- If `early ≤ late`, every member of `H` supports `B` in the grade view, and the validators
    outside `H` holding a raw token at the late cutoff weigh strictly less than `H`, then the view
    grades `B`. -/
theorem gradeBool_of_supporters (E : Env V) (gv : Protocol.GradeView V) (F : Block V)
    (η r : Round) (early late : Time) (B : Block V) (H : Finset V)
    (hel : early ≤ late)
    (hpos : ∀ u ∈ H, Protocol.positive gv F η r early late u B = true)
    (hw : E.electorate.weightOf
        ((Finset.univ.filter fun u => (Protocol.rawView gv η r late u).Nonempty) \ H)
      < E.electorate.weightOf H) :
    Protocol.gradeBool E gv F η r early late B = true := by
  have hpos_sub : H ⊆ Finset.univ.filter fun u =>
      Protocol.positive gv F η r early late u B = true := by
    intro u hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ u, hpos u hu⟩
  have hopp_sub : (Finset.univ.filter fun u =>
      Protocol.opposing gv F η r early late u B = true) ⊆
      (Finset.univ.filter fun u => (Protocol.rawView gv η r late u).Nonempty) \ H := by
    intro u hu
    have hopp := (Finset.mem_filter.mp hu).2
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ u,
      rawView_nonempty_of_opposing gv F η r early late u B hopp⟩, fun huH => ?_⟩
    have hfalse := opposing_false_of_positive gv F η r early late u B hel (hpos u huH)
    rw [hfalse] at hopp
    exact Bool.false_ne_true hopp
  unfold Protocol.gradeBool
  rw [decide_eq_true_eq]
  exact (E.electorate.weightOf_mono hopp_sub).trans_lt
    (hw.trans_le (E.electorate.weightOf_mono hpos_sub))

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- If the validators that oppose `B` in the grade view weigh strictly less than those that support
    it, then the view grades `B`. The converse of `gradeBool_eq_false_of_weight_le`. -/
theorem gradeBool_of_weight_lt (E : Env V) (gv : Protocol.GradeView V) (F : Block V)
    (η r : Round) (early late : Time) (B : Block V)
    (h : E.electorate.weightOf
        (Finset.univ.filter fun u => Protocol.opposing gv F η r early late u B = true)
      < E.electorate.weightOf
        (Finset.univ.filter fun u => Protocol.positive gv F η r early late u B = true)) :
    Protocol.gradeBool E gv F η r early late B = true := by
  unfold Protocol.gradeBool
  rw [decide_eq_true_eq]
  exact h

omit [Fintype V] in
/-- If `u` opposes `B` in the grade view, then either some token of `u`'s late ready view, of a
    round at least that of every token of `u`'s early ready view, does not cover `B`, or two tokens
    of `u`'s raw view at the late cutoff have the same round, at least that of every early ready
    token, and different keys. -/
theorem conditions_of_opposing (gv : Protocol.GradeView V) (F : Block V) (η r : Round)
    (early late : Time) (u : V) (B : Block V)
    (h : Protocol.opposing gv F η r early late u B = true) :
    (∃ x ∈ Protocol.readyView gv F η r late u,
        (∀ y ∈ Protocol.readyView gv F η r early u, y.round ≤ x.round) ∧
        ¬ Protocol.head_covers gv.T B x.key = true) ∨
      ∃ x ∈ Protocol.rawView gv η r late u, ∃ y ∈ Protocol.rawView gv η r late u,
        (∀ z ∈ Protocol.readyView gv F η r early u, z.round ≤ x.round) ∧
        x.round = y.round ∧ x.key ≠ y.key := by
  unfold Protocol.opposing at h
  rw [decide_eq_true_eq] at h
  exact h


end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- If the local grade of `B` passes in `gv`, every sender opposing `B'` in `gv'` opposes `B` in
    `gv`, and every sender supporting `B` in `gv` supports `B'` in `gv'`, then the local grade of
    `B'` passes in `gv'`. -/
theorem gradeBool_of_subsets (E : Env V) {gv gv' : Protocol.GradeView V} {F F' : Block V}
    {η r : Round} {early late early' late' : Time} {B B' : Block V}
    (hopp : (Finset.univ.filter fun u => Protocol.opposing gv' F' η r early' late' u B' = true) ⊆
      Finset.univ.filter fun u => Protocol.opposing gv F η r early late u B = true)
    (hpos : (Finset.univ.filter fun u => Protocol.positive gv F η r early late u B = true) ⊆
      Finset.univ.filter fun u => Protocol.positive gv' F' η r early' late' u B' = true)
    (h : Protocol.gradeBool E gv F η r early late B = true) :
    Protocol.gradeBool E gv' F' η r early' late' B' = true := by
  unfold Protocol.gradeBool at h ⊢
  rw [decide_eq_true_eq] at h ⊢
  exact (E.electorate.weightOf_mono hopp).trans_lt (h.trans_le (E.electorate.weightOf_mono hpos))

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- If `u` opposes `B` in the grade view, then either some token of `u`'s late ready view, of a
    round at least that of every token of `u`'s early ready view, has a key that does not cover `B`
    in `gv`, or two tokens `x`, `y` of `u`'s raw view at the late cutoff, `x` of a round at least
    that of every early ready token, have the same round and different keys. -/
theorem opposing_cases (gv : Protocol.GradeView V) (F : Block V) (η r : Round)
    (early late : Time) (u : V) (B : Block V)
    (h : Protocol.opposing gv F η r early late u B = true) :
    (∃ x ∈ Protocol.readyView gv F η r late u,
        (∀ y ∈ Protocol.readyView gv F η r early u, y.round ≤ x.round) ∧
        ¬ Protocol.localCovers gv x.key B = true) ∨
      ∃ x ∈ Protocol.rawView gv η r late u, ∃ y ∈ Protocol.rawView gv η r late u,
        (∀ z ∈ Protocol.readyView gv F η r early u, z.round ≤ x.round) ∧
        x.round = y.round ∧ x.key ≠ y.key := by
  unfold Protocol.opposing at h
  rw [decide_eq_true_eq] at h
  exact h

omit [Fintype V] in
/-- If `Protocol.Opposes` holds of `B` for `u`'s early ready, late ready and late raw views, with
    `Protocol.localCovers gv` as the cover test, then `u` opposes `B` in the grade view. -/
theorem opposing_of_Opposes (gv : Protocol.GradeView V) (F : Block V) (η r : Round)
    (early late : Time) (u : V) (B : Block V)
    (h : Protocol.Opposes (fun k b => Protocol.localCovers gv k b = true)
      (Protocol.readyView gv F η r early u) (Protocol.readyView gv F η r late u)
      (Protocol.rawView gv η r late u) B) :
    Protocol.opposing gv F η r early late u B = true := by
  unfold Protocol.opposing
  exact decide_eq_true h

omit [Fintype V] in
/-- If `Protocol.Supports` holds of `B` for `u`'s early ready, late ready and late raw views, with
    `Protocol.localCovers gv` as the cover test, then `u` supports `B` in the grade view. -/
theorem positive_of_Supports (gv : Protocol.GradeView V) (F : Block V) (η r : Round)
    (early late : Time) (u : V) (B : Block V)
    (h : Protocol.Supports (fun k b => Protocol.localCovers gv k b = true)
      (Protocol.readyView gv F η r early u) (Protocol.readyView gv F η r late u)
      (Protocol.rawView gv η r late u) B) :
    Protocol.positive gv F η r early late u B = true := by
  unfold Protocol.positive
  exact decide_eq_true h


/-- No block is graded at round `0`: the grade test of round `0` is false for every block `B`. -/
theorem gradeBool_round_zero (E : Env V) (gv : Protocol.GradeView V) (F : Block V) (η : Round)
    (early late : Time) (B : Block V) : Protocol.gradeBool E gv F η 0 early late B = false := by
  have hpos : ∀ u : V, Protocol.positive gv F η 0 early late u B = false := by
    intro u
    unfold Protocol.positive Protocol.readyView Protocol.interpretedInputs Protocol.rawInputs
      Protocol.latest_window
    simp [DecoupledConsensusModel.Protocol.Supports]
  unfold Protocol.gradeBool
  rw [decide_eq_false_iff_not, not_lt]
  apply E.electorate.weightOf_mono
  intro u hu
  simp [hpos] at hu


end DecoupledConsensusModel.Sts
