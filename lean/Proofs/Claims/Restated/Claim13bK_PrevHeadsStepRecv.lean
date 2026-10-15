import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bInvariantActive
import Proofs.Claims.Restated.Claim13bK_ConeAnchor
import Proofs.Claims.Restated.Claim13bK_ConeChain
import Proofs.Claims.Restated.Claim13bK_ConeSlots
import Proofs.Claims.Restated.Claim13bK_ConfirmedOld
import Proofs.Claims.Restated.Claim13bK_FgJustified
import Proofs.Claims.Restated.Claim13bK_FinBeforeTick
import Proofs.Claims.Restated.Claim13bK_Frame
import Proofs.Claims.Restated.Claim13bK_FrameNew
import Proofs.Claims.Restated.Claim13bK_FreshAttestersW
import Proofs.Claims.Restated.Claim13bK_GradeLate
import Proofs.Claims.Restated.Claim13bK_GradeOld
import Proofs.Claims.Restated.Claim13bK_GradeOldHeads
import Proofs.Claims.Restated.Claim13bK_HeadsNewAnchor
import Proofs.Claims.Restated.Claim13bK_HolderMargins
import Proofs.Claims.Restated.Claim13bKit
import Proofs.Claims.Restated.Claim13bPhaseSleepiness
import Proofs.Claims.Restated.Claim13bStepActionF
import Proofs.Claims.Restated.Claim13bStepAssembly
import Proofs.Claims.Restated.Claim13bStepCone
import Proofs.Claims.Restated.Claim13bStepConeIter
import Proofs.Claims.Restated.Claim13bStepFin
import Proofs.Claims.Restated.Claim13bStepGrade
import Proofs.Claims.Restated.Claim13bStepKitConfirm
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bStepKitTick
import Proofs.Claims.Restated.Claim13bStepPairwise
import Proofs.Claims.Restated.Claim13bStepRoots
import Proofs.Claims.Restated.Claim13bStepSG
import Proofs.Claims.Restated.Claim13bStepSGMove
import Proofs.Claims.Restated.Claim13bW_Schedule
import Proofs.Claims.Restated.Claim13beRoute3_2
import Proofs.Claims.Restated.CommonViewOfFinalizedDescendantsFacts
import Proofs.Claims.Restated.Projection
import Proofs.Claims.Restated.Vocabulary_Execution_HealthyLocalFacts
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActive
import Model.Conditions.Claim13bInvariantActiveJoint
import Model.Conditions.Claim13bInvariantActiveTop
import Model.Conditions.Claim13bK_ConeAnchor
import Model.Conditions.Claim13bK_ConeSlots
import Model.Conditions.Claim13bK_FgJustified
import Model.Conditions.Claim13bK_FinBeforeTick
import Model.Conditions.Claim13bK_FreshAttestersW
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13bStepAssembly
import Model.Conditions.Claim13bStepCone
import Model.Conditions.Claim13bStepConeIter
import Model.Conditions.Claim13bStepKitTick
import Model.Conditions.Claim13bStepSG
import Model.Conditions.Claim13beRoute3_5
import Model.Conditions.Claim13beRoute3_7
import Model.Conditions.CommonViewOfFinalizedDescendantsFacts
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_Grades_Main
import Model.Conditions.Vocabulary_Statements_Instantiation_RoundTimes
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bK_PrevHeadsStep
import Proofs.Claims.Restated.WakeWindow
import Proofs.Claims.Restated.Claim13bK_ConeAnchorRecv

/-!
# The grade at a reader awake from t₀ is an ancestor of a fresh SG block, from a receipt

`graded_preceq_freshSG_at_awakeReader` of `Claim13bK_PrevHeadsStep.lean` with the reader `v` awake
from some `t₀` at or before the phase's late cutoff less `2 * Δ + 1` in place of `S.a r`, and its
receipt of round `r`'s honest attestations before the phase's first cutoff.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

/-! ## Helpers -/

section
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- A round opens at the start of its opening slot. -/
private theorem opening_eq_slotStart_phs (facts : Record.Facts M) (S : Setup V) (r : Round) :
    M.opening S.E S.hc r = slotStart S.E.Δ (M.opening_slot S.hc r) :=
  (facts.gr.opening_eq_proposal_time S.E S.hc r).trans
    (facts.sch.Γ_0_eq_proposal_time S.hc S.E r).symm

/-- A round's action instant is six delays after its opening. -/
private theorem action_eq_opening_add_phs (facts : Record.Facts M) (S : Setup V) (r : Round) :
    Restated.Vocabulary.Execution.Setup.a M S r = M.opening S.E S.hc r + 6 * S.E.Δ := by
  have h1 : Restated.Vocabulary.Execution.Setup.a M S r
      = M.confirmation_time S.E (M.opening_slot S.hc r) :=
    facts.sch.a_eq_confirmation_time S.hc S.E r
  have h2 := facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E (M.opening_slot S.hc r)
  rw [h1, opening_eq_slotStart_phs facts S r]
  linarith

/-- A round opens at or before its action instant. -/
private theorem opening_le_action_phs (facts : Record.Facts M) (S : Setup V) (r : Round) :
    M.opening S.E S.hc r ≤ Restated.Vocabulary.Execution.Setup.a M S r := by
  have h := action_eq_opening_add_phs facts S r
  have hd := S.E.Δ_pos
  linarith

/-- The round-`r` action read computed from `before` gives some node state. -/
private theorem actionReadFrom_nonempty_phs (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∃ n, n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r := by
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc (M.toHealing before.st.core)
    (Restated.Vocabulary.Execution.Setup.a M S r) before.cache
  obtain ⟨st, hst⟩ := facts.dt.duties_update_confirmation_with_nonempty (M.gradeContract c) S.E
    S.hc (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r))
    (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1)
  exact ⟨_, c, hc, st, hst, rfl⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If `v` is awake from `t₀` to the domain instant of a round-`(r + 1)` phase `p`, with `t₀` at or
    before `p`'s late cutoff less `2 * Δ + 1`, is not held by the adversary there, and receives
    round `r`'s honest attestations before `p`'s first cutoff, then every block `v`'s store grades for round `r + 1` at `p`'s cutoffs
    is an ancestor of a round-`r` SG block of some member of `HonRound S Sched r`. -/
theorem graded_preceq_freshSG_at_awakeReader_recv (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
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
    {r : Round} {n : Nat} {T : NamedBlock V}
    (hr : Restated.switchRound M S tE ≤ r) (hinv : Restated.AfterPhaseInvariantOverActiveSetsTop M S Sched x r n T)
    (hcross : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepFinalizedCrossingUnderAnchor M S Sched x r n'' T)
    {v : V} {p : Protocol.Phase}
    (hdom : M.domain S.E S.hc (r + 1) p ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)))
    (t₀ : Int) (ht₀ : t₀ ≤ M.late S.E S.hc (r + 1) p - 1 - 2 * S.E.Δ)
    (hawT : v ∈ Sched.awakeThroughout t₀ (M.domain S.E S.hc (r + 1) p))
    (hrecv : Restated.ReceivesRoundAttestationsBefore M S Sched x r v (M.early S.E S.hc (r + 1) p))
    (hvS : v ∉ Sched.adv (M.domain S.E S.hc (r + 1) p))
    {m : Nat} (hm : Restated.stepBeforeInstant M x m (M.domain S.E S.hc (r + 1) p))
    (B : Block V)
    (hgrade : M.gradeBool S.E (M.gradeView (M.toHealing (x[m][v].st).st.core))
      (x[m][v].st).st.core.F S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) p)
      (M.late S.E S.hc (r + 1) p) B ⇢ true) :
    ∃ v_1 ∈ Restated.HonRound M S Sched r, ∃ a : NamedAttestation V,
      a.round = r ∧ a.val_index = v_1 ∧
      (⟨v_1, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n + 1].sent ∧
      ∃ C : NamedBlock V, C ∈ (x[n + 1][v_1].st).st.bodies ∧ a.confirmed = some C.root ∧
        Block.Preceq B C.erase := by
  have hn := hinv.tick
  have hgstr : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S r) :=
    le_trans (Restated.gst_le_switchOpening facts S tGAT tE gap hgst hlen)
      (le_trans (Restated.switchOpening_le_opening facts S hr) (opening_le_action_phs facts S r))
  have htm := Restated.time_le_action_succ_of_stepBefore facts S Sched x htd hdom hm
  have htmd : (x[m].time : Int) ≤ M.domain S.E S.hc (r + 1) p :=
    le_of_lt (Restated.time_lt_domain_of_stepBefore facts S Sched x htd hm)
  have ham : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[m].time : Int) := Restated.action_le_time_of_stepBefore facts S Sched x htd hm
  have hrs := Restated.roundSleepinessW_switchOpening_of_phase facts S Sched tGAT tE gap hgst hlen hmono hthird
    hphase hrsW
  have hneAtt : ∀ v_1 ∈ Restated.HonRound M S Sched r, ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) v_1
        (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S r) x[n] v_1)
        (Restated.Vocabulary.Execution.Setup.a M S r) ⇢ out := fun v_1 hv_1 =>
    Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono hn
      (Restated.action_emod_delta facts S _)
      (Finset.mem_sdiff.2 ⟨Restated.awake_action_of_mem_honRound facts hv_1, (Finset.mem_sdiff.1 hv_1).2⟩)
  have hfsh := Restated.freshSGHeads_at_awakeReader_recv facts (hcross := hcross) S Sched x tE hexec
    hmono htd hsync hmult tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr hinv hdom t₀ ht₀ hawT hvS hm
    (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›) hneAtt
  obtain ⟨v_1, hv_1, C, hC, hconf, hBC⟩ := Restated.graded_preceq_freshSG_recv facts S Sched x hexec
    htd hn hgstr hm hrecv
    (fun t ht hin => hvS (hmono _ _ (le_trans ht htmd) hin))
    (Restated.hexp_of_domain facts S htm)
    (fun k hk v_2 hv_2 a ha _ => Restated.hroom_of_fresh facts S Sched x hexec hn
      (fun t ht => Restated.honestThrough_of_mem_freshAttestersW facts hv_2 t
        (le_trans ht (Restated.time_mono_int facts S Sched x (le_of_lt hk)))) a ha)
    (fun v_2 hv_2 a ha C hC hc => hfsh v_2 hv_2 C hC a ha hc)
    (fun v_2 _ a ha root hc => Restated.hhead_mem_of_tick facts S Sched x n r v_2 a ha root hc)
    (Restated.hhalf_of_roundSleepinessW facts S Sched x hexec htd hmono hrs
      (Restated.switchOpening_le_opening facts S (le_trans hr (Nat.le_succ r)))
      (Restated.eta_le_of_switchRound_le facts S tGAT tE gap hgst hlen hr) hdom hm)
    B hgrade (facts.ndRun.tick_outcome_sts S Sched x hexec.idealization.root_injective hexec.honestRootsNew)
    (fun v_2 hv_2 => hneAtt v_2 (Restated.hfreshH_of_stepBefore facts S Sched x htd hm hv_2))
  have hqr : v_1 ∉ Sched.adv ((Restated.Vocabulary.Execution.Setup.a M S r)) :=
    Restated.honestThrough_of_mem_freshAttestersW facts hv_1 _ (Restated.action_le_time_of_stepBefore facts S Sched x htd hm)
  have hsent := Restated.fresh_attests facts S Sched x hn
    (Restated.freshAttestersW_subset_freshAttesters facts S Sched x r m hv_1) hqr
    (hneAtt v_1 (Restated.hfreshH_of_stepBefore facts S Sched x htd hm hv_1))
    (by
      have hw := ((Restated.mem_freshAttestersW facts).mp hv_1).1
      obtain ⟨τ, hlbl, hτ⟩ := id hn
      refine Restated.run_fact_g2 facts S Sched x n τ r v_1 hlbl hτ ?_ (by
        rw [hτ]
        exact fun t ht => Restated.honestThrough_of_mem_freshAttestersW facts hv_1 t
          (le_trans ht (Restated.action_le_time_of_stepBefore facts S Sched x htd hm)))
      have h12 := twelve_delta_le_wAttest S
      have hΔ := S.E.Δ_pos
      simp only [Restated.activeRoundW, Restated.attestersAt, Schedule.awakeThroughout, Finset.mem_inf,
        Finset.mem_Icc] at hw ⊢
      try rw [facts.gr.early_g2_eq S r] at hw
      rw [facts.gr.early_g2_eq S r]
      intro t ht
      exact hw t ⟨by linarith [ht.1], ht.2⟩)
  obtain ⟨nr, hnr⟩ := actionReadFrom_nonempty_phs facts (Setup.alwaysAwake S) (x[n][v_1].st) r
  obtain ⟨D, hD⟩ := facts.dt.attest_with_nonempty (M.gradeContract nr.cache)
    (Setup.alwaysAwake S).E (Setup.alwaysAwake S).hc ((Setup.alwaysAwake S).node v_1) nr.st nr.record
  have ha : D.2.2 ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][v_1].st) v_1 r :=
    ⟨nr, hnr, D.1, D.2.1, hD⟩
  exact ⟨v_1, Restated.hfreshH_of_stepBefore facts S Sched x htd hm hv_1, D.2.2,
    Restated.actionAttestationFrom_round facts (Setup.alwaysAwake S) _ v_1 r _ ha,
    Restated.actionAttestationFrom_val_index facts (Setup.alwaysAwake S) _ v_1 r _ ha,
    hsent _ ha, C, hC, hconf _ ha, hBC⟩

end

end DecoupledConsensusModel.Sts.Restated
