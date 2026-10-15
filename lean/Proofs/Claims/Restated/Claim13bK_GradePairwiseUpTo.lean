import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariantActive
import Proofs.Claims.Restated.Claim13bK_FinBeforeTick
import Proofs.Claims.Restated.Claim13bK_GradeDescendantUpTo
import Proofs.Claims.Restated.Claim13bK_GradePairwise
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActive
import Model.Conditions.Claim13bInvariantActiveTop
import Model.Conditions.Claim13bK_FinBeforeTick
import Model.Conditions.Claim13bK_GradePairwise
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13bStepSG
import Model.Conditions.ClaimAsyncK_DeliveryUpTo
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring

/-!
# Graded blocks of an action, with synchrony up to the next action instant

`sgGraded_preceqFreshSG_or_preceq_anchor_upTo`: a block graded at the round-`(r + 1)` action of a
member of `HonRound` is an ancestor of a round-`r` SG block or of the round-`r` anchor, with
synchrony assumed only up to `S.a (r + 1)`.
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

/-- With synchrony up to `S.a (r + 1)`: if `n'` is the tick step at `S.a (r + 1)` and the justified
    block of every round-`(r + 1)` action of a validator honest through `S.a (r + 1)` is an ancestor
    of `T`, then every graded block of an outcome of the round-`(r + 1)` action of a member of
    `HonRound S Sched (r + 1)` is an ancestor of a round-`r` SG block of a member of
    `HonRound S Sched r`, or an ancestor of `T`. -/
theorem sgGraded_preceqFreshSG_or_preceq_anchor_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    {r : Round} (hsync : Restated.SynchronyFromWakeBefore M S x ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    (hmult : AwakeAtMultiples S Sched)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE) (hcs : Restated.committeeSleepinessW M S Sched tE)
    {n n' : Nat} {T : NamedBlock V}
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
      Restated.graded_preceq_freshSG_of_premises_upTo facts (hcross := hcross) S Sched x tE hexec hmono htd hsync hmult tGAT gap hgst
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

end DecoupledConsensusModel.Sts.Restated
