import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.ProcessedFlip
import Proofs.Claims.Restated.Redelivery
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_NamedNode
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActive
import Model.Conditions.Claim13bK_Frame
import Model.Conditions.Claim13bStepSG
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring

/-!
# Where the roots of a phase cache come from

That every root a validator's phase cache holds is an ancestor of a block its own store graded
before that phase's domain time, and the same for the grade-2 entry of a round's action frame,
stated over a model `M : Record.Model V`.
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

/-- If `FramePhaseProvenance S x v c` holds, it holds for `c` clipped to any block. -/
theorem framePhaseProvenance_clipCache (facts : Record.Facts M) (S : Setup V) {Sched : Schedule V}
    {x : AtomicExec (Record.protocolOf M S) Sched} {v : V} {c : M.Cache} (F : Block V)
    (h : Restated.FramePhaseProvenance M S x v c) :
    Restated.FramePhaseProvenance M S x v (M.clipCache F c) := by
  intro r₁ p root hr
  obtain ⟨root₀, h₀, hpre⟩ := facts.gr.phaseResult_clipCache hr
  obtain ⟨m, B, hm, hB, hpre'⟩ := h r₁ p root₀ h₀
  exact ⟨m, B, hm, hB, preceq_trans_Preceq hpre hpre'⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- There is a choice `g` of one outcome of `G B` for every `B` such that, whenever `g B` is `true`,
    every outcome of `G B` is `true`. -/
private theorem exists_choice_false_first {β : Type} (G : β → DC.NDRE Bool)
    (hne : ∀ B, ∃ b, G B ⇢ b) :
    ∃ g : β → Bool, (∀ B, G B ⇢ g B) ∧ ∀ B, g B = true → ∀ b, G B ⇢ b → b = true := by
  classical
  refine ⟨fun B => if G B ⇢ false then false else Classical.choose (hne B), ?_, ?_⟩
  · intro B
    by_cases hf : G B ⇢ false
    · simp only [if_pos hf]; exact hf
    · simp only [if_neg hf]; exact Classical.choose_spec (hne B)
  · intro B hB b hb
    by_cases hf : G B ⇢ false
    · simp only [if_pos hf] at hB; exact absurd hB Bool.false_ne_true
    · cases b
      · exact absurd hb hf
      · rfl

/-- If `FramePhaseProvenance` holds for the cache `v` held at the tick step `k` at `t`, it holds for
    every cache the phase tick at `t` can leave from `v`'s store at `k`. -/
theorem framePhaseProvenance_onPhaseTick (facts : Record.Facts M) (S : Setup V) {Sched : Schedule V}
    {x : AtomicExec (Record.protocolOf M S) Sched} {v : V} {k : Nat} {t : Int} (hk : Restated.tickStepAt M x k t)
    (h : Restated.FramePhaseProvenance M S x v (x[k][v].st).cache) :
    ∀ c' : M.Cache,
      M.onPhaseTick S.E S.hc (M.toHealing (x[k][v].st).st.core) t (x[k][v].st).cache ⇢ c' →
      Restated.FramePhaseProvenance M S x v c' := by
  intro c' hc' r₁ p root hr
  obtain ⟨g, hg, hall⟩ := exists_choice_false_first
    (fun B => M.gradeBool S.E (M.gradeView (M.toHealing (x[k][v].st).st.core))
      (M.toHealing (x[k][v].st).st.core).toFG.F S.hc.η_SG r₁ (M.early S.E S.hc r₁ p)
      (M.late S.E S.hc r₁ p) B)
    (fun B => facts.gr.gradeBool_nonempty S.E _ _ _ _ _ _ B)
  rcases facts.gr.phaseResult_onPhaseTick S.E S.hc _ t _ c' hc' hr g hg with
    ⟨root₀, h₀, hpre⟩ | ⟨ht, B, hB, hpre⟩
  · obtain ⟨m, B, hm, hB, hpre'⟩ := h r₁ p root₀ h₀
    exact ⟨m, B, hm, hB, preceq_trans_Preceq hpre hpre'⟩
  · have hB' := hall B hB
    rw [facts.sto.Sts_toHealing_F] at hB'
    refine ⟨k, B, ?_, hB', hpre⟩
    rw [← ht]
    exact Restated.stepBeforeInstant_of_tickStepAt facts x hk

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- At every step, every root `v`'s phase cache holds for a round and a phase is an ancestor of a
    block `v`'s own store graded at the step before that phase's domain time. -/
theorem framePhaseProvenance_sts (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (v : V) (k : Nat) :
    Restated.FramePhaseProvenance M S x v (x[k][v].st).cache := by
  have _hr_0 : M.reachedNode (x[0][v].st) := Record.reachedNode_sts facts S Sched x 0 v
  induction k with
  | zero =>
      obtain ⟨-, hn, -⟩ := x.init
      have h0 : (x[0][v].st) = M.initial (Setup.alwaysAwake S) v := by
        show ((x.cfg 0)[v]).st = _
        rw [hn v]; rfl
      intro r₁ p root hr
      rw [h0] at hr
      exact absurd hr (facts.nd.initial_cache_phaseResult_ne (Setup.alwaysAwake S) v r₁ p root)
  | succ k ih =>
      have _hr_k : M.reachedNode (x[k][v].st) := Record.reachedNode_sts facts S Sched x k v
      cases hl : x.lbl k with
      | tickAllAwake τ =>
          have _hr_w : M.reachedNode (Record.wakeStage M Sched (τ : Int) x[k] v) :=
            Record.reachedNode_wakeStage facts S Sched x k v τ
          rcases Restated.st_succ_of_tick facts S Sched x v hl with
            ⟨-, -, out₁, hout, hst⟩ | hst
          · obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc
              (x[k][v].st).st.core.toHealing (τ : Int) (x[k][v].st).cache
            have hc' : M.onPhaseTick S.E S.hc
                (Record.wakeStage M Sched (τ : Int) x[k] v).st.core.toHealing (τ : Int)
                (Record.wakeStage M Sched (τ : Int) x[k] v).cache ⇢ c := by
              rw [Record.wakeStage_st facts, Record.wakeStage_cache facts]
              exact hc
            rw [hst, Restated.Vocabulary.Proofs.NamedNode.tick_cache_eq facts _ v _ _ out₁ hout c hc']
            have hk : Restated.tickStepAt M x k (τ : Int) := ⟨τ, hl, rfl⟩
            exact Restated.framePhaseProvenance_clipCache facts S _
              (Restated.framePhaseProvenance_onPhaseTick facts S hk ih c hc)
          · rw [hst, Record.wakeStage_cache facts]; exact ih
      | deliver p m =>
          by_cases hp : p = v
          · subst hp
            rcases Restated.st_succ_of_deliver facts S Sched x hl with hproc | ⟨-, hst⟩
            · rw [facts.nd.process_cache_eq _ _ _ _ hproc]
              exact Restated.framePhaseProvenance_clipCache facts S _ ih
            · rw [hst]; exact ih
          · rw [Restated.getElem_succ_of_deliver_ne facts S Sched x hl hp]
            exact ih
      | custom _ ev => exact ev.elim
      | adversarial p m =>
          rw [Restated.getElem_succ_of_adversarial facts S Sched x hl]
          exact ih
      | forward p m =>
          rw [Restated.getElem_succ_of_forward facts S Sched x hl]
          exact ih

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If `n'` is the tick step at round `r₁`'s action time, and some round-`r₁` action frame `f` `v`
    can read from its node state after `n'` steps offers the root `root` for the phase `p`, then
    there are a step `m`, the last one before that phase's domain time, and a block `B` such that
    every outcome of the grade test of `B` on `v`'s store after `m` steps, for round `r₁` with that
    phase's cutoffs, is `true`, and `root` is an ancestor of `B`. -/
theorem phaseResult_actionFrame_provenance (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    {r₁ : Round} {n' : Nat} (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S r₁)))
    (v : V) (p : Protocol.Phase) (root : Block V)
    (f : M.Frame) (hf : f ∈ Restated.actionFrame M S (x[n'][v].st) r₁)
    (h : M.phaseResult f p = some (some root)) :
    ∃ (m : Nat) (B : Block V), Restated.stepBeforeInstant M x m (M.domain S.E S.hc r₁ p) ∧
      (∀ b : Bool, M.gradeBool S.E (M.gradeView (M.toHealing (x[m][v].st).st.core))
        (x[m][v].st).st.core.F S.hc.η_SG r₁ (M.early S.E S.hc r₁ p)
        (M.late S.E S.hc r₁ p) B ⇢ b → b = true) ∧
      Block.Preceq root B := by
  obtain ⟨m', ⟨c, hc, st0, -, rfl⟩, rfl⟩ := hf
  dsimp only at h
  rw [facts.nd.mkNode_cache] at h
  have hprep := Restated.framePhaseProvenance_onPhaseTick facts S hn'
    (Restated.framePhaseProvenance_sts facts S Sched x v n') c hc
  obtain ⟨root₀, h₀, hpre⟩ := facts.gr.readFrame_phase_provenance _ _ _ h
  obtain ⟨m, B, hm, hB, hpre'⟩ := hprep r₁ p root₀ h₀
  exact ⟨m, B, hm, hB, preceq_trans_Preceq hpre hpre'⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If some round-`r₁` action frame `f` `v` can read after the tick step at `S.a r₁` offers `root`
    as its grade-2 entry, then `root` is an ancestor of a block every outcome of whose grade test on
    `v`'s store, for round `r₁` at the step before the grade-2 domain time with the grade-2 cutoffs,
    is `true`. -/
theorem actionFrame_g2_provenance (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    {r₁ : Round} {n' : Nat} (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S r₁)))
    (v : V) (root : Block V)
    (f : M.Frame) (hf : f ∈ Restated.actionFrame M S (x[n'][v].st) r₁)
    (h : f.g2 = some (some root)) :
    ∃ (m : Nat) (B : Block V),
      Restated.stepBeforeInstant M x m (M.domain S.E S.hc r₁ .g2) ∧
      (∀ b : Bool, M.gradeBool S.E (M.gradeView (M.toHealing (x[m][v].st).st.core))
        (x[m][v].st).st.core.F S.hc.η_SG r₁ (M.early S.E S.hc r₁ .g2)
        (M.late S.E S.hc r₁ .g2) B ⇢ b → b = true) ∧
      Block.Preceq root B :=
  Restated.phaseResult_actionFrame_provenance facts S Sched x hn' v .g2 root f hf
    (by rw [facts.gr.Sts_phaseResult_g2]; exact h)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If every block whose grade test a member of `HonRound S Sched (r + 1)` runs for round `r + 1` at
    the step before a phase domain time at or before `S.a (r + 1)` can return `true` lies on one
    chain with `T`, then every grade-2 root of every round-`(r + 1)` action frame such a member can
    read after the tick step at `S.a (r + 1)` lies on one chain with `T`. -/
theorem frameG2Old_of_gradeOld (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (r : Round) (n' : Nat) (T : NamedBlock V)
    (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    (hgradeOld : ∀ v ∈ Restated.HonRound M S Sched (r + 1),
      ∀ p : Protocol.Phase, M.domain S.E S.hc (r + 1) p ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) →
      ∀ m : Nat, Restated.stepBeforeInstant M x m (M.domain S.E S.hc (r + 1) p) →
      ∀ B : Block V,
        M.gradeBool S.E (M.gradeView (M.toHealing (x[m][v].st).st.core))
            (x[m][v].st).st.core.F S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) p)
            (M.late S.E S.hc (r + 1) p) B ⇢ true →
        Block.compatible B T.erase = true) :
    ∀ v ∈ Restated.HonRound M S Sched (r + 1),
      ∀ f ∈ Restated.actionFrame M S (x[n'][v].st) (r + 1), ∀ root : Block V,
      f.g2 = some (some root) →
      Block.compatible root T.erase = true := by
  intro v hv f hf root hroot
  obtain ⟨m, B, hm, hB, hpre⟩ :=
    Restated.actionFrame_g2_provenance facts S Sched x hn' v root f hf hroot
  -- an outcome of the grade test exists, and every outcome is `true`
  obtain ⟨b, hb⟩ := facts.gr.gradeBool_nonempty S.E
    (M.gradeView (M.toHealing (x[m][v].st).st.core)) (x[m][v].st).st.core.F S.hc.η_SG (r + 1)
    (M.early S.E S.hc (r + 1) .g2) (M.late S.E S.hc (r + 1) .g2) B
  have hbt : b = true := hB b hb
  subst hbt
  exact Protocol.compatible_of_preceq_of_compatible hpre
    (hgradeOld v hv .g2 (facts.gr.domain_le_action S (r + 1) .g2) m hm B hb)

end

end DecoupledConsensusModel.Sts.Restated
