import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Record.Wiring

/-!
# No conflicting block is graded

A theorem over a model `M : Record.Model V` with facts `facts : Record.Facts M`: when the supporters
of `P` outweigh the other holders of a raw token, no block conflicting with `P` is graded.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
set_option autoImplicit false
open DecoupledConsensusModel.Proofs.GradeCutoffMono

/-- If the early cutoff is at or before the late one, every outcome of the test whether a member of
    `H` supports `P` in the grade view is `true`, for every choice `raw` of one outcome of the raw
    token view at the late cutoff per validator the validators `u` outside `H` with `raw u`
    non-empty weigh strictly less than `H`, and `Q` is not on one chain with `P`, then every outcome
    of the grade test of `Q` in the view is `false`. -/
theorem notGraded_of_conflicting_supporters (facts : Record.Facts M) (E : Env V) (gv : M.GV)
    (F : Block V) (η r : Round) (early late : Time) (P Q : Block V) (H : Finset V)
    (hel : early ≤ late)
    (hpos : ∀ u ∈ H, ∀ p : Bool, M.positive gv F η r early late u P ⇢ p → p = true)
    (hw : ∀ raw : V → Finset (Protocol.Token (Option BlockId)),
      (∀ u, M.rawView gv η r late u ⇢ raw u) →
      E.electorate.weightOf
        ((Finset.univ.filter fun u => (raw u).Nonempty) \ H)
      < E.electorate.weightOf H)
    (hPQ : ¬ Block.Compatible P Q) :
    ∀ g : Bool, M.gradeBool E gv F η r early late Q ⇢ g → g = false := by
  intro g hg
  have hposf : ∀ u, M.positive gv F η r early late u Q ⇢
      (fun u => (facts.gr.positive_nonempty gv F η r early late u Q).choose) u :=
    fun u => (facts.gr.positive_nonempty gv F η r early late u Q).choose_spec
  have hoppf : ∀ u, M.opposing gv F η r early late u Q ⇢
      (fun u => (facts.gr.opposing_nonempty gv F η r early late u Q).choose) u :=
    fun u => (facts.gr.opposing_nonempty gv F η r early late u Q).choose_spec
  have hrawf : ∀ u, M.rawView gv η r late u ⇢
      (fun u => (facts.gr.rawView_nonempty gv η r late u).choose) u :=
    fun u => (facts.gr.rawView_nonempty gv η r late u).choose_spec
  set pos := fun u => (facts.gr.positive_nonempty gv F η r early late u Q).choose
  set opp := fun u => (facts.gr.opposing_nonempty gv F η r early late u Q).choose
  set raw := fun u => (facts.gr.rawView_nonempty gv η r late u).choose
  have hcov : ∀ k, M.head_covers gv.T Q k ⇢
      (fun k => (facts.gr.head_covers_nonempty gv.T Q k).choose) k :=
    fun k => (facts.gr.head_covers_nonempty gv.T Q k).choose_spec
  have hopp : H ⊆ Finset.univ.filter fun u => opp u = true := by
    intro u hu
    obtain ⟨p, hp⟩ := facts.gr.positive_nonempty gv F η r early late u P
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ u,
      facts.gr.opposing_of_positive_not_compatible gv F η r early late u hel hPQ p hp
        (hpos u hu p hp) (opp u) (hoppf u)⟩
  have hposQ : (Finset.univ.filter fun u => pos u = true) ⊆
      (Finset.univ.filter fun u => (raw u).Nonempty) \ H := by
    intro u hu
    have hq := (Finset.mem_filter.mp hu).2
    obtain ⟨Re, hRe⟩ := facts.gr.readyView_nonempty gv F η r early u
    obtain ⟨Rl, hRl⟩ := facts.gr.readyView_nonempty gv F η r late u
    obtain ⟨We, hWe⟩ := facts.gr.rawView_nonempty gv η r early u
    obtain ⟨u₀, hmem, -⟩ := facts.gr.conditions_of_positive gv F η r early late u Q (pos u)
      (hposf u) hq Re hRe Rl hRl (raw u) (hrawf u) _ hcov
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ u,
      ⟨u₀, facts.gr.rawView_mono gv η r hel u We hWe (raw u) (hrawf u)
        (facts.gr.readyView_subset_rawView gv F η r early u Re hRe We hWe hmem)⟩⟩,
      fun huH => ?_⟩
    have hf := facts.gr.opposing_false_of_positive gv F η r early late u Q hel (pos u)
      (hposf u) hq (opp u) (hoppf u)
    have ht := (Finset.mem_filter.mp (hopp huH)).2
    rw [hf] at ht
    exact Bool.false_ne_true ht
  exact facts.gr.gradeBool_eq_false_of_weight_le E gv F η r early late Q pos hposf opp hoppf
    (((E.electorate.weightOf_mono hposQ).trans (hw raw hrawf).le).trans
      (E.electorate.weightOf_mono hopp)) g hg

end

end DecoupledConsensusModel.Sts.Restated
