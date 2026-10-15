import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bStepGrade
import Proofs.Claims.Restated.Claim13bStepKitTick
import Proofs.Claims.Restated.Claim13bStepSG
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bStepKitTick
import Model.Conditions.Claim13bStepPairwise
import Model.Conditions.Claim13bStepSG
import Model.Conditions.Sts_Conditions
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bStepPairwise

/-!
# Compatibility of SG walk outputs

Where the SG walk's output comes from, when the outputs of two stores' SG walks lie on one chain,
and the root a validator's round attestation says it confirms, stated over a model
`M : Record.Model V` and its facts `facts : Record.Facts M`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The block the SG walk `M.currentSGVote` returns is an ancestor of the store's confirmed block,
    or a graded block of the grade read, or the store's fork-choice root. -/
theorem sgVote_source (facts : Record.Facts M) {stH : M.HS} {grades : Protocol.GradeRead V} :
    Block.Preceq (M.currentSGVote stH grades) stH.live_confirmed ∨
      SGGraded grades (M.currentSGVote stH grades) ∨
      M.currentSGVote stH grades = M.get_fg_root stH.toFG := by
  cases hdc : M.deepest_clear (some grades.anchor) stH.live_confirmed grades.clear with
  | some B =>
      rw [facts.gr.Sts_currentSGVote_of_deepest_clear hdc]
      exact Or.inl (preceq_eq_true_iff_Preceq.mp (facts.gr.deepest_clear_preceq hdc))
  | none =>
      cases hQ : grades.Q2 with
      | some Q =>
          rw [facts.gr.Sts_currentSGVote_of_Q2 hdc hQ]
          exact Or.inr (Or.inl (Or.inl hQ))
      | none =>
          rcases facts.gr.currentSGVote_of_none_none hdc hQ with h | h
          · rw [h]
            exact Or.inr (Or.inr rfl)
          · rw [h]
            exact Or.inr (Or.inl (Or.inr rfl))

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The blocks two stores' SG walks return lie on one chain, whenever the two stores' confirmed
    blocks lie on one chain, each store's fork-choice root is an ancestor of `T'`, each walk's
    output lies on one chain with `T'`, and the two stores' graded blocks lie on one chain with each
    other's candidates (`hgrade`). -/
theorem sgVote_pairwise_compatible (facts : Record.Facts M) {stH₁ stH₂ : M.HS}
    {grades₁ grades₂ : Protocol.GradeRead V} {T' : Block V}
    (hlc : Block.compatible stH₁.live_confirmed stH₂.live_confirmed = true)
    (hfg₁ : Block.Preceq (M.get_fg_root stH₁.toFG) T')
    (hfg₂ : Block.Preceq (M.get_fg_root stH₂.toFG) T')
    (hcomp₁ : Block.compatible (M.currentSGVote stH₁ grades₁) T' = true)
    (hcomp₂ : Block.compatible (M.currentSGVote stH₂ grades₂) T' = true)
    (hgrade : Restated.GradePairwise M stH₁ stH₂ grades₁ grades₂) :
    Block.compatible (M.currentSGVote stH₁ grades₁)
      (M.currentSGVote stH₂ grades₂) = true := by
  classical
  have hgr : ∀ B₁ B₂ : Block V, Restated.SGCandidate M stH₁ grades₁ B₁ → Restated.SGCandidate M stH₂ grades₂ B₂ →
      (SGGraded grades₁ B₁ ∨ SGGraded grades₂ B₂) → Block.compatible B₁ B₂ = true := hgrade
  by_cases hf1 : M.currentSGVote stH₁ grades₁ = M.get_fg_root stH₁.toFG
  · refine Protocol.compatible_of_preceq_of_compatible ?_ (Protocol.compatible_comm hcomp₂)
    rw [hf1]
    exact hfg₁
  by_cases hf2 : M.currentSGVote stH₂ grades₂ = M.get_fg_root stH₂.toFG
  · refine Protocol.compatible_comm
      (Protocol.compatible_of_preceq_of_compatible ?_ (Protocol.compatible_comm hcomp₁))
    rw [hf2]
    exact hfg₂
  rcases Restated.sgVote_source facts (stH := stH₁) (grades := grades₁) with h1 | h1 | h1
  · rcases Restated.sgVote_source facts (stH := stH₂) (grades := grades₂) with h2 | h2 | h2
    · rcases compatible_cases hlc with hle | hge
      · exact compatible_of_preceq_common_Preceq (preceq_trans_Preceq h1 hle) h2
      · exact compatible_of_preceq_common_Preceq h1 (preceq_trans_Preceq h2 hge)
    · exact hgr _ _ (Or.inl h1) (Or.inr h2) (Or.inr h2)
    · exact absurd h2 hf2
  · rcases Restated.sgVote_source facts (stH := stH₂) (grades := grades₂) with h2 | h2 | h2
    · exact hgr _ _ (Or.inr h1) (Or.inl h2) (Or.inl h1)
    · exact hgr _ _ (Or.inr h1) (Or.inr h2) (Or.inl h1)
    · exact absurd h2 hf2
  · exact absurd h1 hf1

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For a node state `n` of the round-`r₁` action read from `before` and a grade read `g` of the
    frame of `n`'s cache, the block the SG walk returns at `n`'s healing store under `g` lies on one
    chain with `T`, whenever that store's confirmed block does, every grade-1 and grade-2 root the
    frame holds does, and so does that store's fork-choice root. -/
theorem sgVote_compatible_at_read (facts : Record.Facts M) (S : Setup V) (before : M.N) (r₁ : Round)
    (n : M.N)
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
      before r₁)
    (g : Protocol.GradeRead V)
    (hg : M.frameGradeRead n.cache S.E S.hc (M.toHealing n.st.core) r₁ ⇢ g)
    {T : Block V}
    (hconf : Block.compatible (M.toHealing n.st.core).live_confirmed T = true)
    (hg1 : ∀ root : Block V, (M.readFrame n.cache (M.toHealing n.st.core) r₁).g1 = some (some root) →
      Block.compatible root T = true)
    (hg2 : ∀ root : Block V, (M.readFrame n.cache (M.toHealing n.st.core) r₁).g2 = some (some root) →
      Block.compatible root T = true)
    (hfg : Block.compatible
      (M.get_fg_root (M.toHealing n.st.core).toFG) T = true) :
    Block.compatible (M.currentSGVote (M.toHealing n.st.core) g) T = true := by
  have hanchor : Block.compatible g.anchor T = true := by
    obtain ⟨A, hA⟩ := facts.gr.anchor_nonempty S.E S.hc (M.toHealing n.st.core) r₁
      (M.readFrame n.cache (M.toHealing n.st.core) r₁).g1
    rw [facts.gr.frameGradeRead_anchor n.cache S.E S.hc _ r₁ g hg A hA]
    exact facts.gr.anchor_compatible S (r₁ := r₁) hg1 hfg A hA
  have hQ2 : ∀ Q : Block V, g.Q2 = some Q → Block.compatible Q T = true := by
    intro Q hQ
    obtain ⟨o, ho⟩ := facts.gr.grade2Block_nonempty (M.toHealing n.st.core)
      (M.readFrame n.cache (M.toHealing n.st.core) r₁)
    have hgo : g.Q2 = o := facts.nd.ModelProperties_gradeContract_read_Q2 n.cache S.E S.hc _ r₁ g
      ((facts.nd.gradeContract_read n.cache S.E S.hc _ r₁ g).2 hg) o ho
    exact facts.gr.Q2_compatible hg2 o ho (hgo ▸ hQ)
  exact facts.gr.sgVote_compatible hconf hQ2 hanchor hfg

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The root the `confirmed` field of a round-`(r + 1)` attestation sent under the name of a
    validator `v` honest through `tH'` carries is, for every node state `n` of `v`'s own
    round-`(r + 1)` action read and every grade read `g` of the frame of `n`'s cache, the root of
    the block the SG walk returns at `n`'s healing store under `g`. -/
theorem attest_confirmed_sgVote_root (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    {tH' : Int} {r : Round} {n' : Nat} (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    (htH : (x[n' + 1].time : Int) ≤ tH')
    {v : V} (hv : v ∈ honestThroughSet Sched tH') {a : NamedAttestation V}
    (haround : a.round = r + 1) (hunf : Restated.Unforgeability M S x) (hidx : a.val_index = v)
    (hsent : (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n' + 1].sent)
    {root : BlockId} (hconfC : a.confirmed = some root) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
      (x[n'][v].st) (r + 1),
    ∀ g, M.frameGradeRead n.cache S.E S.hc (M.toHealing n.st.core) (r + 1) ⇢ g →
    root = (M.currentSGVote (M.toHealing n.st.core) g).root := by
  have _hr_0 : M.reachedNode (x[n'][v].st) := Record.reachedNode_sts facts S Sched x n' v
  have _hr_1 : M.reachedNode (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) x[n'] v) := Record.reachedNode_wakeStage facts S Sched x n' v (Restated.Vocabulary.Execution.Setup.a M S (r + 1))
  intro n hn g hg
  have hvh : HonestThroughTime Sched tH' v := mem_honestThroughSet.1 hv
  obtain ⟨-, k, -, htick, -, hemit⟩ :=
    Restated.attest_round_of_sent facts S Sched x hvh hunf hidx htH hsent
  rw [haround] at htick hemit
  have hkn : k = n' := Restated.tickStepAt_unique facts x htick hn'
  rw [hkn] at hemit
  obtain ⟨out, hout, hmem⟩ := hemit
  obtain ⟨D, hD⟩ := facts.dt.attest_with_nonempty (M.gradeContract n.cache)
    (Setup.alwaysAwake S).E (Setup.alwaysAwake S).hc ((Setup.alwaysAwake S).node v) n.st n.record
  have hn₂ : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
      (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) x[n'] v) (r + 1) := by
    unfold Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom at hn ⊢
    rw [Record.wakeStage_st facts, Record.wakeStage_cache facts, Record.wakeStage_record facts]
    exact hn
  have _hv_s1 := Record.runs_as_wakeStage facts S Sched x (n') v (Restated.Vocabulary.Execution.Setup.a M S (r + 1))
  have haeq : a = D.2.2 :=
    Restated.attest_of_tick_eq facts S v _ (r + 1) hout hmem D.2.2
      ⟨n, hn₂, D.1, D.2.1, hD⟩
  rw [haeq] at hconfC
  have h := (Restated.attest_confirmed_eq_sgVote facts S (x[n'][v].st) v (r + 1) n hn D hD g
    hg).symm.trans hconfC
  exact (Option.some_inj.mp h).symm

end

end DecoupledConsensusModel.Sts.Restated
