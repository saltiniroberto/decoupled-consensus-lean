import Proofs.Vocabulary.Protocol.Grades.GuardedGradeHelpers
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGrades
import Model.Conditions.Vocabulary_ModelVocabulary_Execution_GradeRuntime_Transport
import Model.Vocabulary.Protocol.Grades
import Proofs.Vocabulary.ModelVocabulary
import Model.Record.Wiring

/-!
# The store grade and the weighted grade

The store grade equals the weighted grade over the store's token sets, and the weighted grade does
not depend on which of two agreeing head interpretations is used, stated over a model
`M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedOutageHistory
open DecoupledConsensusModel.Proofs.NamedOutageHistory.GuardedHelpers
open Internal Execution Internal.PhaseGrades DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol (Token EquivocationAt Supports Opposes)

/-- For every outcome `b` of the store grade of `B` at `st`, round `r` and phase `p`, and every
    choice of one outcome of each cover test, early ready view, late ready view and late raw view,
    `b` is `true` exactly when `B` passes the weighted grade over those views with those cover
    tests. -/
theorem Vocabulary.Proofs.NamedOutageHistory.GuardedHelpers.storeGrade_iff (facts : Record.Facts M) (S : Setup V) (st : M.NS) (r : Round)
    (p : Phase) (B : Block V) :
    ∀ b, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc st r p B ⇢ b →
    ∀ (cov : Option BlockId → Block V → Bool),
      (∀ key block, M.localCovers st.core.toHealing.gradeView key block ⇢ cov key block) →
    ∀ (e : V → Finset (Token (Option BlockId))),
      (∀ v, M.readyView st.core.toHealing.gradeView st.core.F S.hc.η_SG r
        (M.early S.E S.hc r p) v ⇢ e v) →
    ∀ (l : V → Finset (Token (Option BlockId))),
      (∀ v, M.readyView st.core.toHealing.gradeView st.core.F S.hc.η_SG r
        (M.late S.E S.hc r p) v ⇢ l v) →
    ∀ (raw : V → Finset (Token (Option BlockId))),
      (∀ v, M.rawView st.core.toHealing.gradeView S.hc.η_SG r
        (M.late S.E S.hc r p) v ⇢ raw v) →
    (b = true ↔
      Restated.Vocabulary.Protocol.grade M S.E.electorate.weight
        (fun key block => cov key block = true) e l raw B) := by
  classical
  intro b hb cov hcov e he l hl raw hraw
  choose pos hpos using fun v => facts.gr.positive_nonempty st.core.toHealing.gradeView st.core.F
    S.hc.η_SG r (M.early S.E S.hc r p) (M.late S.E S.hc r p) v B
  choose opp hopp using fun v => facts.gr.opposing_nonempty st.core.toHealing.gradeView st.core.F
    S.hc.η_SG r (M.early S.E S.hc r p) (M.late S.E S.hc r p) v B
  have hs : (Finset.univ.filter fun v => pos v = true) =
      Restated.Vocabulary.Protocol.coverSupporters M (fun key block => cov key block = true)
        e l raw B := by
    ext v
    simp only [Restated.Vocabulary.Protocol.coverSupporters, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact ⟨fun h => facts.gr.supports_of_positive (pos v) (hpos v) h cov hcov (e v) (he v)
        (l v) (hl v) (raw v) (hraw v),
      fun h => facts.gr.positive_of_Supports _ _ _ _ _ _ _ _ cov hcov (e v) (he v) (l v) (hl v)
        (raw v) (hraw v) h (pos v) (hpos v)⟩
  have ho : (Finset.univ.filter fun v => opp v = true) =
      Restated.Vocabulary.Protocol.opponents M (fun key block => cov key block = true)
        e l raw B := by
    ext v
    simp only [Restated.Vocabulary.Protocol.opponents, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact ⟨fun h => facts.gr.opposes_of_opposing (opp v) (hopp v) h cov hcov (e v) (he v)
        (l v) (hl v) (raw v) (hraw v),
      fun h => facts.gr.opposing_of_Opposes _ _ _ _ _ _ _ _ cov hcov (e v) (he v) (l v) (hl v)
        (raw v) (hraw v) h (opp v) (hopp v)⟩
  have hb' : M.gradeBool S.E st.core.toHealing.gradeView st.core.F S.hc.η_SG r
      (M.early S.E S.hc r p) (M.late S.E S.hc r p) B ⇢ b := hb
  have hg : b = true ↔
      S.E.electorate.weightOf (Finset.univ.filter fun v => opp v = true) <
        S.E.electorate.weightOf (Finset.univ.filter fun v => pos v = true) := by
    constructor
    · intro h
      by_contra hn
      rw [facts.gr.gradeBool_eq_false_of_weight_le _ _ _ _ _ _ _ _ pos hpos opp hopp
        (not_lt.mp hn) b hb'] at h
      cases h
    · intro h
      exact facts.gr.gradeBool_of_weight_lt _ _ _ _ _ _ _ _ opp hopp pos hpos h b hb'
  rw [hg, hs, ho]
  simp only [Restated.Vocabulary.Protocol.grade, DecoupledConsensusModel.Protocol.weight,
    Electorate.weightOf]

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedOutageHistory
open DecoupledConsensusModel.Proofs.NamedOutageHistory.GuardedHelpers
open Internal Execution Internal.PhaseGrades DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol (Token EquivocationAt Supports Opposes)

/-- If every early token set is contained in the late one and the two head interpretations `c` and
    `c'` agree on every late token, then a block graded under `c` is graded under `c'`. -/
theorem Vocabulary.Proofs.NamedOutageHistory.GuardedHelpers.grade_congr (facts : Record.Facts M) {Key Blk : Type} (w : V → Nat) (c c' : Key → Blk → Prop)
    {e l raw : V → Finset (Token Key)} {B : Blk}
    (hsub : ∀ v, e v ⊆ l v) (hiff : ∀ v, ∀ x ∈ l v, (c x.key B ↔ c' x.key B))
    (hg : Restated.Vocabulary.Protocol.grade M w c e l raw B) :
    Restated.Vocabulary.Protocol.grade M w c' e l raw B := by
  classical
  have hp : Restated.Vocabulary.Protocol.coverSupporters M c e l raw B ⊆
      Restated.Vocabulary.Protocol.coverSupporters M c' e l raw B := by
    intro v hv
    simp only [Restated.Vocabulary.Protocol.coverSupporters, Finset.mem_filter, Finset.mem_univ,
      true_and] at hv ⊢
    exact facts.gr.supports_congr c c' (hsub v) (hiff v) hv
  have hn : Restated.Vocabulary.Protocol.opponents M c' e l raw B ⊆
      Restated.Vocabulary.Protocol.opponents M c e l raw B := by
    intro v hv
    simp only [Restated.Vocabulary.Protocol.opponents, Finset.mem_filter, Finset.mem_univ,
      true_and] at hv ⊢
    exact facts.gr.opposes_congr c' c (fun x hx => (hiff v x hx).symm) hv
  exact lt_of_le_of_lt (weight_mono w hn) (lt_of_lt_of_le hg (weight_mono w hp))

end

end DecoupledConsensusModel.Sts.Restated
