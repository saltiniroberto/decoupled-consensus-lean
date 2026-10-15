import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bK_ConeAnchor
import Proofs.Claims.Restated.Claim13bK_FinBeforeTick
import Proofs.Claims.Restated.Claim13bK_FreshAttestersW
import Proofs.Claims.Restated.Claim13bK_GradeLateUpTo
import Proofs.Claims.Restated.Claim13bK_GradeOld
import Proofs.Claims.Restated.Claim13bK_GradeOldHeads
import Proofs.Claims.Restated.Claim13bK_GradeOldHeadsUpTo
import Proofs.Claims.Restated.Claim13bPhaseSleepiness
import Proofs.Claims.Restated.Claim13bStepAssembly
import Proofs.Claims.Restated.Claim13bStepCone
import Proofs.Claims.Restated.Claim13bStepConeIter
import Proofs.Claims.Restated.Claim13bStepGrade
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13beRoute3_3
import Proofs.Claims.Restated.CommonViewOfFinalizedDescendantsFacts
import Proofs.Claims.Restated.Projection
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActive
import Model.Conditions.Claim13bInvariantActiveTop
import Model.Conditions.Claim13bK_ConeSlots
import Model.Conditions.Claim13bK_FgJustified
import Model.Conditions.Claim13bK_FinBeforeTick
import Model.Conditions.Claim13bK_FreshAttestersW
import Model.Conditions.Claim13bK_GradeOldHeads
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13bStepAssembly
import Model.Conditions.Claim13bStepCone
import Model.Conditions.Claim13bStepKitTick
import Model.Conditions.ClaimAsyncK_DeliveryUpTo
import Model.Conditions.CommonViewOfFinalizedDescendantsFacts
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring
import Proofs.Claims.Restated.WakeWindow
import Proofs.Claims.Restated.Claim13bK_ConeAnchorRecv

/-!
# Grade-1 compatibility at a reader, from a receipt, with synchrony up to a cutoff

`freshSGHeads_at_awakeReader_upTo` and `grade1_compatible_at_awakeReader_upTo` of
`Claim13bK_ConeAnchorUpTo.lean` (synchrony up to the late cutoff)
with the reader `v` awake from some `t₀` in place of `S.a r`: `t₀` at or before the start of the
two-delay window before the phase's late cutoff, where the heads it grades reach it, and, for the
grade, the reader's receipt of round `r`'s honest attestations before the phase's first cutoff.
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

/-- If synchrony from wake holds for every send whose deadline is at or before `b'`, and `b ≤ b'`,
    then it holds for every send whose deadline is at or before `b`. -/
private theorem synchronyFromWakeBefore_mono {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (Record.protocolOf M S) Sched} {b b' : Int} (hb : b ≤ b')
    (hs : Restated.SynchronyFromWakeBefore M S x b') : Restated.SynchronyFromWakeBefore M S x b :=
  fun k w sm hsend hle haw => hs k w sm hsend (le_trans hle hb) haw

/-- With synchrony only up to the late cutoff of round `r + 1`'s phase `p`: for a validator `v`
    awake throughout `[t₀, domain (r + 1) p]`, with `t₀` at or before the phase's late cutoff less
    `2 * Δ + 1`, and not held by the adversary at `domain (r + 1) p`, where `p`'s domain instant is at or before `S.a (r + 1)` and `m` is the last
    step before that instant, and for every member `v_1` of `freshAttestersW S Sched x r m`, the
    block every attestation of `v_1`'s round-`r` action names is in `v`'s tree at `m` under its
    root, stamped before the phase's late cutoff, and compatible with `v`'s finalized block at `m`.
    The hypotheses `hneTick` and `hneAtt` ask that `v`'s tick have an outcome at every whole
    multiple of `Δ` up to `S.a (r + 1)` at which `v` is awake and not held, and that `M.tick` on
    every honest active attester of round `r` at `S.a r` have an outcome. -/
theorem freshSGHeads_at_awakeReader_upTo_recv (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    {r : Round} {p : Protocol.Phase}
    (hsync : Restated.SynchronyFromWakeBefore M S x (M.late S.E S.hc (r + 1) p))
    (hmult : AwakeAtMultiples S Sched)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE) (hcs : Restated.committeeSleepinessW M S Sched tE)
    {n : Nat} {T : NamedBlock V}
    (hr : Restated.switchRound M S tE ≤ r) (hinv : Restated.AfterPhaseInvariantOverActiveSetsTop M S Sched x r n T)
    (hcross : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepFinalizedCrossingUnderAnchor M S Sched x r n'' T)
    {v : V}
    (hdom : M.domain S.E S.hc (r + 1) p ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)))
    (t₀ : Int) (ht₀ : t₀ ≤ M.late S.E S.hc (r + 1) p - 1 - 2 * S.E.Δ)
    (hawT : v ∈ Sched.awakeThroughout t₀ (M.domain S.E S.hc (r + 1) p))
    (hvS : v ∉ Sched.adv (M.domain S.E S.hc (r + 1) p))
    {m : Nat} (hm : Restated.stepBeforeInstant M x m (M.domain S.E S.hc (r + 1) p))
    (hneTick : ∀ (n' : Nat) (t' : Int),
      Restated.tickStepAt M x n' t' → t' % S.E.Δ = 0 → v ∈ Sched.awake t' \ Sched.adv t' → t' ≤ Restated.Vocabulary.Execution.Setup.a M S (r + 1) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched t' x[n'] v) t' ⇢ out)
    (hneAtt : ∀ v_1 ∈ Restated.HonRound M S Sched r, ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) v_1 (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S r) x[n] v_1) (Restated.Vocabulary.Execution.Setup.a M S r) ⇢ out) :
    ∀ v_1 ∈ Restated.freshAttestersW M S Sched x r m, ∀ C : NamedBlock V,
      C ∈ (x[n + 1][v_1].st).st.bodies →
      ∀ a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][v_1].st) v_1 r,
      a.confirmed = some C.root →
      Block.find? (x[m][v].st).st.core.T C.root = some C.erase ∧
      stampedBefore (x[m][v].st).st.core.timestamp_block
        (M.late S.E S.hc (r + 1) p) C.erase = true ∧
      Block.compatible C.erase (x[m][v].st).st.core.F = true := by
  classical
  intro v_1 hv_1 C hCbody a ha hconf
  have hd := S.E.Δ_pos
  have hd1 : (1 : Int) ≤ S.E.Δ := hd
  obtain ⟨n', hn'⟩ := Restated.tick_field_at_succ facts S Sched x htd r
  have hfin := Restated.fin_old_anchor_before_succ_tick_of_hypotheses facts (hcross := hcross) S Sched x tE hexec hmono tGAT gap
    hgst hlen hthird hphase hrsW hr hinv hn'
  have hn := hinv.tick
  -- instants
  have hn1 : (x[n + 1].time : Int) = (Restated.Vocabulary.Execution.Setup.a M S r) := (Restated.tickStepAt_time facts x hn).1
  have hn'1 : (x[n' + 1].time : Int) = (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) := (Restated.tickStepAt_time facts x hn').1
  have ham : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[m].time : Int) := Restated.action_le_time_of_stepBefore facts S Sched x htd hm
  have htmd : (x[m].time : Int) ≤ M.domain S.E S.hc (r + 1) p :=
    le_of_lt (Restated.time_lt_domain_of_stepBefore facts S Sched x htd hm)
  have hlate := facts.gr.action_add_three_delta_le_late_succ S r p
  have hld := facts.gr.late_le_domain S (r + 1) p
  have hdm := Restated.domain_sub_one_le_time_of_stepBefore facts S Sched x htd hm
  -- a round opens at the proposal instant of its opening slot, which is at or before that slot's
  -- confirmation instant, the action instant
  have hopen : M.opening S.E S.hc r ≤ Restated.Vocabulary.Execution.Setup.a M S r := by
    show _ ≤ M.a S.hc S.E.Δ r
    rw [facts.gr.opening_eq_proposal_time, facts.sch.a_eq_confirmation_time]
    exact facts.sch.proposal_time_le_confirmation_time _ _
  have htGAT : tGAT ≤ (Restated.Vocabulary.Execution.Setup.a M S r) :=
    le_trans (Restated.tGAT_le_switchOpening facts S tGAT tE gap hgst hlen)
      (le_trans (Restated.switchOpening_le_opening facts S hr) hopen)
  -- honesty
  have hvm : Restated.HonestThrough M Sched x m v := fun t ht hin =>
    hvS (hmono t _ (le_trans ht htmd) hin)
  have hv1m : Restated.HonestThrough M Sched x m v_1 := Restated.honestThrough_of_mem_freshAttestersW facts hv_1
  have hv1n : Restated.HonestThrough M Sched x (n + 1) v_1 := fun t ht =>
    hv1m t (le_trans ht (by rw [hn1]; exact ham))
  -- `C` is compatible with the anchor
  have hqr : v_1 ∉ Sched.adv ((Restated.Vocabulary.Execution.Setup.a M S r)) := hv1m _ ham
  -- the grade-2 awake test of `v_1`'s tick at step `n`: `v_1` is awake through `wAttest S ≥ 12Δ`
  -- before `S.a r`, which covers round `r`'s grade-2 window from one delay before its early cutoff
  -- `S.a r − 11Δ`, so `run_fact_g2` gives it
  have hrun : M.awake_for_grade2 (Setup.alwaysAwake S) v_1
      (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S r) x[n] v_1) r := by
    have hw := ((Restated.mem_freshAttestersW facts).mp hv_1).1
    obtain ⟨τ, hlbl, hτ⟩ := hn
    refine Restated.run_fact_g2 facts S Sched x n τ r v_1 hlbl hτ ?_ (by
      -- `v_1` is not held by the adversary at any instant up to `S.a r` (`hv1m`, `ham`)
      rw [hτ]
      exact fun t ht => hv1m t (le_trans ht ham))
    have h12 := twelve_delta_le_wAttest S
    simp only [Restated.activeRoundW, Restated.attestersAt, Schedule.awakeThroughout, Finset.mem_inf,
      Finset.mem_Icc] at hw ⊢
    try rw [facts.gr.early_g2_eq S r] at hw
    rw [facts.gr.early_g2_eq S r]
    intro t ht
    exact hw t ⟨by linarith [ht.1], ht.2⟩
  have hsent := Restated.fresh_attests facts S Sched x hn
    (Restated.freshAttestersW_subset_freshAttesters facts S Sched x r m hv_1) hqr
    (hneAtt v_1 (Restated.hfreshH_of_stepBefore facts S Sched x htd hm hv_1)) hrun a ha
  have hCT : Block.compatible C.erase T.erase = true :=
    hinv.sg v_1 (Restated.hfreshH_of_stepBefore facts S Sched x htd hm hv_1) a
      (Restated.actionAttestationFrom_round facts (Setup.alwaysAwake S) _ v_1 r a ha)
      (Restated.actionAttestationFrom_val_index facts (Setup.alwaysAwake S) _ v_1 r a ha) hsent C
      hCbody hconf
  -- every honest finalized block up to `n'` is on one chain with `C`
  have hFC : ∀ (w : V) (d : Nat), d ≤ n' → Restated.HonestThrough M Sched x d w →
      Block.compatible (x[d][w].st).st.core.F C.erase = true := fun w d hd' hw =>
    Protocol.compatible_of_preceq_of_compatible (hfin w d hd' hw) (Protocol.compatible_comm hCT)
  have hmn' : m ≤ n' := Restated.stepBefore_le_tick facts x hm hn' (le_trans hdom le_rfl)
  have hlog : Restated.blockInLog M S Sched x C := Restated.blockInLog_of_mem_bodies facts S Sched hv1n hCbody
  -- the reader admits `C` at every delivery before `S.a (r + 1)`
  have hadm : Restated.ReaderAdmitsInPhase M S Sched x tGAT ((Restated.Vocabulary.Execution.Setup.a M S (r + 1)) - 1) v C := by
    intro d v_0 _ hvd _ hhi
    have hdn : d ≤ n' := by
      by_contra hcon
      have hle : n' + 1 ≤ d := by omega
      have h1 := Restated.time_mono_int facts S Sched x hle
      rw [hn'1] at h1
      linarith
    have hc := hFC v d hdn hvd
    rcases compatible_cases hc with hFCd | hCFd
    · exact Or.inl (preceq_eq_true_iff_Preceq.mpr hFCd)
    · exact Or.inr (Restated.mem_bodies_of_preceq_finalized facts S Sched x hexec hvd hlog hCFd)
  have hadmS : Restated.ReaderAdmitsAtStepsInPhase M S Sched x tGAT ((Restated.Vocabulary.Execution.Setup.a M S (r + 1)) - 1) v C := by
    intro d hvd _ hhi
    have hdn : d ≤ n' := by
      by_contra hcon
      have hle : n' + 1 ≤ d := by omega
      have h1 := Restated.time_mono_int facts S Sched x hle
      rw [hn'1] at h1
      linarith
    have hc := hFC v d hdn hvd
    rcases compatible_cases hc with hFCd | hCFd
    · exact Or.inl (preceq_eq_true_iff_Preceq.mpr hFCd)
    · exact Or.inr (Restated.mem_bodies_of_preceq_finalized facts S Sched x hexec hvd hlog hCFd)
  have hwaw : v ∈ Sched.awakeThroughout
      (M.late S.E S.hc (r + 1) p - 1 - 2 * S.E.Δ) (M.late S.E S.hc (r + 1) p - 1) :=
    awakeThroughout_mono Sched hawT (by linarith) (by linarith)
  obtain ⟨hmemT, σ, hσ, hσlt⟩ :=
    Restated.block_in_tree_of_holder_afterPhase_ofAdmits_upTo facts S Sched x hexec
      (synchronyFromWakeBefore_mono (by linarith) hsync) hmult htd hmono hgst hcv
      hphase hthird hcs (Restated.delta_le_of_healingLengthη facts S hlen) hadm hadmS hCbody hv1n
      (by rw [hn1]; exact htGAT) (by rw [hn1]; linarith) (by linarith) (by linarith)
      (fun hin => hvS (hmono _ _ htmd hin)) hwaw
      (fun n'' t' h1 hΔ hq _ h3 => hneTick n'' t' h1 hΔ hq (le_trans h3 (le_trans htmd hdom)))
  refine ⟨?_, ?_, ?_⟩
  · rw [← Proofs.NamedWire.erase_root]
    exact Restated.find_of_mem_tree_honest facts S Sched x hexec hvm hmemT
  · exact stampedBefore_of_lt hσ (lt_of_lt_of_le hσlt (WithBot.coe_le_coe.mpr (by linarith)))
  · exact Protocol.compatible_comm (hFC v m hmn' hvm)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- With synchrony only up to the late cutoff of round `r + 1`'s phase `p`: for a validator `v`
    awake at every instant from `t₀` to the domain instant of `p`, at or before `S.a (r + 1)`, with
    `t₀` at or before the phase's late cutoff less `2 * Δ + 1`, not held by the adversary at that
    instant, and receiving round `r`'s honest attestations before `p`'s first cutoff, every block `v` grades at least 1 for round
    `r + 1` at the last step before that instant, with `p`'s cutoffs, lies on one chain with the
    round-`r` anchor `T`. The hypotheses `hneTick` and `hneAtt` are those of
    `freshSGHeads_at_awakeReader_upTo_recv`. -/
theorem grade1_compatible_at_awakeReader_upTo_recv (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    {r : Round} {p : Protocol.Phase}
    (hsync : Restated.SynchronyFromWakeBefore M S x (M.late S.E S.hc (r + 1) p))
    (hmult : AwakeAtMultiples S Sched)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE) (hcs : Restated.committeeSleepinessW M S Sched tE)
    {n : Nat} {T : NamedBlock V}
    (hr : Restated.switchRound M S tE ≤ r) (hinv : Restated.AfterPhaseInvariantOverActiveSetsTop M S Sched x r n T)
    (hcross : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepFinalizedCrossingUnderAnchor M S Sched x r n'' T)
    {v : V}
    (hdom : M.domain S.E S.hc (r + 1) p ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)))
    (t₀ : Int) (ht₀ : t₀ ≤ M.late S.E S.hc (r + 1) p - 1 - 2 * S.E.Δ)
    (hawT : v ∈ Sched.awakeThroughout t₀ (M.domain S.E S.hc (r + 1) p))
    (hrecv : Restated.ReceivesRoundAttestationsBefore M S Sched x r v (M.early S.E S.hc (r + 1) p))
    (hvS : v ∉ Sched.adv (M.domain S.E S.hc (r + 1) p))
    {m : Nat} (hm : Restated.stepBeforeInstant M x m (M.domain S.E S.hc (r + 1) p))
    (B : Block V)
    (hgrade : M.gradeBool S.E (M.gradeView (M.toHealing (x[m][v].st).st.core))
      (x[m][v].st).st.core.F S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) p)
      (M.late S.E S.hc (r + 1) p) B ⇢ true)
    (hneTick : ∀ (n' : Nat) (t' : Int),
      Restated.tickStepAt M x n' t' → t' % S.E.Δ = 0 → v ∈ Sched.awake t' \ Sched.adv t' → t' ≤ Restated.Vocabulary.Execution.Setup.a M S (r + 1) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched t' x[n'] v) t' ⇢ out)
    (hneAtt : ∀ v_1 ∈ Restated.HonRound M S Sched r, ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) v_1 (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S r) x[n] v_1) (Restated.Vocabulary.Execution.Setup.a M S r) ⇢ out) :
    Block.compatible B T.erase = true := by
  have hn := hinv.tick
  -- a round opens at the proposal instant of its opening slot, which is at or before that slot's
  -- confirmation instant, the action instant
  have hopen : M.opening S.E S.hc r ≤ Restated.Vocabulary.Execution.Setup.a M S r := by
    show _ ≤ M.a S.hc S.E.Δ r
    rw [facts.gr.opening_eq_proposal_time, facts.sch.a_eq_confirmation_time]
    exact facts.sch.proposal_time_le_confirmation_time _ _
  have hgstr : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S r) :=
    le_trans (Restated.gst_le_switchOpening facts S tGAT tE gap hgst hlen)
      (le_trans (Restated.switchOpening_le_opening facts S hr) hopen)
  have htm := Restated.time_le_action_succ_of_stepBefore facts S Sched x htd hdom hm
  have htmd : (x[m].time : Int) ≤ M.domain S.E S.hc (r + 1) p :=
    le_of_lt (Restated.time_lt_domain_of_stepBefore facts S Sched x htd hm)
  have ham : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[m].time : Int) := Restated.action_le_time_of_stepBefore facts S Sched x htd hm
  have hrs := Restated.roundSleepinessW_switchOpening_of_phase facts S Sched tGAT tE gap hgst hlen hmono hthird
    hphase hrsW
  exact Restated.grade1_of_sg_prevLate_recv facts S Sched x hexec htd hn hgstr (Restated.HonRound M S Sched r) hinv.sg hm
    (Restated.hfreshH_of_stepBefore facts S Sched x htd hm) hrecv
    (fun t ht hin => hvS (hmono _ _ (le_trans ht htmd) hin))
    (Restated.hexp_of_domain facts S htm)
    (fun k hk v_1 hv_1 a ha _ => Restated.hroom_of_fresh facts S Sched x hexec hn
      (fun t ht => Restated.honestThrough_of_mem_freshAttestersW facts hv_1 t
        (le_trans ht (Restated.time_mono_int facts S Sched x (le_of_lt hk)))) a ha)
    (fun v_1 hv_1 a ha C hC hconf =>
      Restated.freshSGHeads_at_awakeReader_upTo_recv facts (hcross := hcross) S Sched x tE hexec hmono htd hsync hmult tGAT gap hgst hlen hcv
        hthird hphase hrsW hcs hr hinv hdom t₀ ht₀ hawT hvS hm hneTick hneAtt v_1 hv_1 C hC a ha hconf)
    (fun v_1 _ a ha root hconf => Restated.hhead_mem_of_tick facts S Sched x n r v_1 a ha root hconf)
    (Restated.hhalf_of_roundSleepinessW facts S Sched x hexec htd hmono hrs
      (Restated.switchOpening_le_opening facts S (le_trans hr (Nat.le_succ r)))
      (Restated.eta_le_of_switchRound_le facts S tGAT tE gap hgst hlen hr) hdom hm)
    B hgrade (facts.ndRun.tick_outcome_sts S Sched x hexec.idealization.root_injective hexec.honestRootsNew)
    (fun v_1 hv_1 => hneAtt v_1 (Restated.hfreshH_of_stepBefore facts S Sched x htd hm hv_1))
end

end DecoupledConsensusModel.Sts.Restated
