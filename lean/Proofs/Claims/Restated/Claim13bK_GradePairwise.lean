import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bInvariantActive
import Proofs.Claims.Restated.Claim13bK_FinBeforeTick
import Proofs.Claims.Restated.Claim13bK_Frame
import Proofs.Claims.Restated.Claim13bK_FreshAttestersW
import Proofs.Claims.Restated.Claim13bK_GradeDescendant
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActive
import Model.Conditions.Claim13bInvariantActiveTop
import Model.Conditions.Claim13bK_FinBeforeTick
import Model.Conditions.Claim13bK_FreshAttestersW
import Model.Conditions.Claim13bK_GradeDescendant
import Model.Conditions.Claim13bK_GradePairwise
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13bStepSG
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring

/-!
# Graded blocks of an action are ancestors of SG blocks or of the anchor

Theorems showing that a block graded at the round-`(r + 1)` action of a member of `HonRound` is an
ancestor of a round-`r` SG block or of the round-`r` anchor, and that blocks of these kinds are
pairwise compatible under the round-`r` invariant.
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

/-- If `n'` is the tick step at `S.a (r + 1)` and the round-`r` SG blocks are compatible with the
    confirmed block of every member of `HonRound S Sched (r + 1)`, they are compatible with the
    confirmed block of every member of `freshAttestersW S Sched x (r + 1) (n' + 1)`. -/
theorem confirmedCompatibleFreshSG_of_overHonRound (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {r : Round} {n n' : Nat}
    (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    (h : Restated.ConfirmedCompatibleFreshSGOverHonRound M S Sched x r n n') :
    Restated.ConfirmedCompatibleFreshSG M S Sched x r n n' := fun v hv =>
  h v (Restated.freshAttestersW_subset_honRound facts S Sched x (le_of_eq (Restated.tickStepAt_time facts x hn').1.symm) hv)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If `n'` is the tick step at `S.a r₁`, `nr` is a node state `v`'s round-`r₁` action can give, `g`
    is an outcome of its grade read, and `B` is the grade-2 candidate or the anchor block of `g`,
    then either `B` is an ancestor of a block that `v`'s store, at the last step before some phase's
    domain instant, grades for round `r₁` with that phase's cutoffs, or `B` is `M.get_fg_root` of
    `nr`'s healing store. -/
theorem sgGraded_preceq_graded_or_fgRoot (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {r₁ : Round} {n' : Nat}
    (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S r₁))) (v : V) {B : Block V}
    {nr : M.N}
    (hnr : nr ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
      (x[n'][v].st) r₁)
    {g : Protocol.GradeRead V}
    (hg : M.frameGradeRead nr.cache S.E S.hc (M.toHealing nr.st.core) r₁ ⇢ g)
    (hB : SGGraded g B) :
    (∃ (p : Protocol.Phase) (m : Nat) (G : Block V),
      Restated.stepBeforeInstant M x m (M.domain S.E S.hc r₁ p) ∧
      (∀ b : Bool, M.gradeBool S.E (M.gradeView (M.toHealing (x[m][v].st).st.core))
        (x[m][v].st).st.core.F S.hc.η_SG r₁ (M.early S.E S.hc r₁ p)
        (M.late S.E S.hc r₁ p) G ⇢ b → b = true) ∧
      Block.Preceq B G) ∨
    B = M.get_fg_root (M.toHealing nr.st.core).toFG := by
  have hgc := (facts.nd.gradeContract_read _ _ _ _ _ g).2 hg
  have hf : M.readFrame nr.cache (M.toHealing nr.st.core) r₁ ∈
      Restated.actionFrame M S (x[n'][v].st) r₁ := ⟨nr, hnr, rfl⟩
  rcases hB with hQ | hA
  · obtain ⟨o, ho⟩ := facts.gr.grade2Block_nonempty (M.toHealing nr.st.core)
      (M.readFrame nr.cache (M.toHealing nr.st.core) r₁)
    have hQo := facts.nd.ModelProperties_gradeContract_read_Q2 _ _ _ _ _ g hgc o ho
    obtain ⟨root, hroot, hQr⟩ := facts.gr.grade2Block_preceq_root o ho (hQo.symm.trans hQ)
    obtain ⟨m, G, hm, hG, hrG⟩ :=
      Restated.actionFrame_g2_provenance facts S Sched x hn' v root _ hf hroot
    exact Or.inl ⟨.g2, m, G, hm, hG, preceq_trans_Preceq hQr hrG⟩
  · obtain ⟨a, ha⟩ := facts.gr.anchor_nonempty S.E S.hc (M.toHealing nr.st.core) r₁
      (M.readFrame nr.cache (M.toHealing nr.st.core) r₁).g1
    have hga := facts.nd.ModelProperties_gradeContract_read_anchor _ _ _ _ _ g hgc a ha
    rcases facts.gr.anchor_cases S.E S.hc (M.toHealing nr.st.core) r₁ _ a ha with
      hfg | ⟨root, B', hg1, hact, hB'⟩
    · exact Or.inr (hA.trans (hga.trans hfg))
    · obtain ⟨m, G, hm, hG, hrG⟩ :=
        Restated.phaseResult_actionFrame_provenance facts S Sched x hn' v .g1 root _ hf
          ((facts.gr.phaseResult_g1 _).trans hg1)
      refine Or.inl ⟨.g1, m, G, hm, hG, ?_⟩
      rw [hA, hga, hB']
      exact preceq_trans_Preceq (preceq_eq_true_iff_Preceq.mp (facts.gr.activePrefix_preceq hact)) hrG

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If `n'` is the tick step at `S.a (r + 1)` and the justified block of every round-`(r + 1)`
    action of a validator honest through `S.a (r + 1)` is an ancestor of `T`, then every graded
    block of an outcome of the round-`(r + 1)` action of a member of `HonRound S Sched (r + 1)` is
    an ancestor of a round-`r` SG block of a member of `HonRound S Sched r`, or an ancestor of `T`. -/
theorem sgGraded_preceqFreshSG_or_preceq_anchor (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (hsync : Restated.SynchronyFromWake M S x) (hmult : AwakeAtMultiples S Sched)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE) (hcs : Restated.committeeSleepinessW M S Sched tE)
    {r : Round} {n n' : Nat} {T : NamedBlock V}
    (hr : Restated.switchRound M S tE ≤ r) (hinv : Restated.AfterPhaseInvariantOverActiveSetsTop M S Sched x r n T)
    (hcross : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepFinalizedCrossingUnderAnchor M S Sched x r n'' T)
    (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    (hJ : ∀ v ∈ honestThroughSet Sched ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))),
      ∀ hs ∈ Restated.actionHealingStore M S (x[n'][v].st) (r + 1), Block.Preceq hs.J T.erase)
    {v : V} (hv : v ∈ Restated.HonRound M S Sched (r + 1)) {B : Block V}
    {nr : M.N}
    (hnr : nr ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
      (x[n'][v].st) (r + 1))
    {g : Protocol.GradeRead V}
    (hg : M.frameGradeRead nr.cache S.E S.hc (M.toHealing nr.st.core) (r + 1) ⇢ g)
    (hB : SGGraded g B)
    (hneTick : ∀ v ∈ Restated.HonRound M S Sched (r + 1), ∀ (n' : Nat) (t' : Int),
      Restated.tickStepAt M x n' t' → t' % S.E.Δ = 0 → v ∈ Sched.awake t' \ Sched.adv t' → t' ≤ Restated.Vocabulary.Execution.Setup.a M S (r + 1) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched t' x[n'] v) t' ⇢ out)
    (hneAtt : ∀ v ∈ Restated.HonRound M S Sched r, ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S r) x[n] v) (Restated.Vocabulary.Execution.Setup.a M S r) ⇢ out) :
    Restated.PreceqFreshSG M S Sched x r n B ∨ Block.Preceq B T.erase := by
  rcases Restated.sgGraded_preceq_graded_or_fgRoot facts S Sched x hn' v hnr hg hB with
    ⟨p, m, G, hm, hG, hBG⟩ | hfg
  · obtain ⟨b, hb⟩ := facts.gr.gradeBool_nonempty S.E (M.gradeView (M.toHealing (x[m][v].st).st.core))
      (x[m][v].st).st.core.F S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) p)
      (M.late S.E S.hc (r + 1) p) G
    have hbt := hG b hb
    subst hbt
    obtain ⟨v_1, hv_1, a, har, hai, has, C, hC, hac, hGC⟩ :=
      Restated.graded_preceq_freshSG_of_premises facts (hcross := hcross) S Sched x tE hexec hmono htd hsync hmult tGAT gap hgst
        hlen hcv hthird hphase hrsW hcs hr hinv hv (facts.gr.domain_le_action S (r + 1) p) hm G hb
        hneTick hneAtt
    exact Or.inl ⟨v_1, hv_1, a, har, hai, has, C, hC, hac, preceq_trans_Preceq hBG hGC⟩
  · have hvH : v ∈ honestThroughSet Sched ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) :=
      Restated.honRound_subset_honestThroughSet facts S Sched (r + 1) hmono hv
    have hfin := Restated.fin_old_anchor_before_succ_tick_of_hypotheses facts (hcross := hcross) S Sched x tE hexec hmono tGAT gap
      hgst hlen hthird hphase hrsW hr hinv hn'
    have hhs : M.toHealing nr.st.core ∈ Restated.actionHealingStore M S (x[n'][v].st) (r + 1) :=
      ⟨nr, hnr, rfl⟩
    have hF := Restated.actionF_preceq_old_anchor facts S Sched x hn' hfin v hvH _ hhs
    rw [hfg]
    exact Or.inr (facts.fc.fgRoot_preceq hF (hJ v hvH _ hhs))

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Under the round-`r` invariant with anchor `T`: if `B₁` is an ancestor of a round-`r` SG block of
    a member of `HonRound S Sched r` or of `T`, and `B₂` is too, or is an ancestor of a confirmed
    block `LC` compatible with `T` and with every such SG block, then `B₁` and `B₂` are compatible. -/
theorem compatible_of_kinds (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {r : Round} {n : Nat} {T : NamedBlock V}
    (hinv : Restated.AfterPhaseInvariantOverActiveSetsTop M S Sched x r n T) {LC : Block V}
    (hconfT : Block.compatible LC T.erase = true)
    (hconfSG : ∀ v_1 ∈ Restated.HonRound M S Sched r,
      ∀ a : NamedAttestation V, a.round = r → a.val_index = v_1 →
      (⟨v_1, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n + 1].sent →
      ∀ C : NamedBlock V, C ∈ (x[n + 1][v_1].st).st.bodies → a.confirmed = some C.root →
      Block.compatible C.erase LC = true)
    {B₁ B₂ : Block V}
    (h₁ : Restated.PreceqFreshSG M S Sched x r n B₁ ∨ Block.Preceq B₁ T.erase)
    (h₂ : Restated.PreceqFreshSG M S Sched x r n B₂ ∨ Block.Preceq B₂ T.erase ∨ Block.Preceq B₂ LC) :
    Block.compatible B₁ B₂ = true := by
  rcases h₁ with ⟨v_1, hv_1, a, har, hai, has, C, hC, hac, hBC⟩ | hBT
  · rcases h₂ with ⟨v_2, hv_2, a', har', hai', has', C', hC', hac', hBC'⟩ | hBT' | hBL
    · exact compatible_of_preceq_of_preceq hBC hBC'
        (hinv.sgPairwise v_1 hv_1 v_2 hv_2 a a' har hai has har' hai' has' C C' hC hac hC' hac')
    · exact compatible_of_preceq_of_preceq hBC hBT'
        (hinv.sg v_1 hv_1 a har hai has C hC hac)
    · exact compatible_of_preceq_of_preceq hBC hBL
        (hconfSG v_1 hv_1 a har hai has C hC hac)
  · rcases h₂ with ⟨v_2, hv_2, a', har', hai', has', C', hC', hac', hBC'⟩ | hBT' | hBL
    · exact compatible_of_preceq_of_preceq hBT hBC'
        (Protocol.compatible_comm (hinv.sg v_2 hv_2 a' har' hai' has' C' hC' hac'))
    · exact compatible_of_preceq_common_Preceq hBT hBT'
    · exact compatible_of_preceq_of_preceq hBT hBL (Protocol.compatible_comm hconfT)

end

end DecoupledConsensusModel.Sts.Restated
