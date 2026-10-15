import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bK_Frame
import Proofs.Claims.Restated.Claim13bK_FreshAttestersW
import Proofs.Claims.Restated.Claim13bK_GradeLate
import Proofs.Claims.Restated.Claim13bK_GradeOld
import Proofs.Claims.Restated.Claim13bK_GradeOldHeads
import Proofs.Claims.Restated.Claim13bPhaseSleepiness
import Proofs.Claims.Restated.Claim13bStepAssembly
import Proofs.Claims.Restated.Claim13bStepGrade
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bStepSGMove
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActive
import Model.Conditions.Claim13bInvariantActiveTop
import Model.Conditions.Claim13bK_FinBeforeTick
import Model.Conditions.Claim13bK_FreshAttestersW
import Model.Conditions.Claim13bK_GradeDescendant
import Model.Conditions.Claim13bK_GradeOld
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13bStepAnchor
import Model.Conditions.Claim13bStepAssembly
import Model.Conditions.Claim13bStepGrade
import Model.Conditions.Claim13bStepKitTick
import Model.Conditions.Claim13bStepSG
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedActionReads
import Proofs.Claims.Spec2Claims.Claim13bStepSGMove
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bK_GradeDescendant
import Proofs.Claims.Restated.WakeWindow
import Proofs.Claims.Restated.Claim13bK_GradeLateRecv

/-!
# Graded blocks descend from fresh SG blocks

That a block an honest active attester of round `r + 1` grades is an ancestor of a round-`r` SG
block of an honest active attester, that two such graded blocks lie on one chain, and the field
`gradeDescendant` of `AfterPhaseStepHypothesesOverActiveSets` at one round. Stated over a model
`M : Record.Model V`.
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

/-- From any node state `before`, validator `v`'s round-`r` action read can compute some
    attestation. -/
private theorem actionAttestationFrom_nonempty_gd (facts : Record.Facts M) (S : Setup V)
    (before : M.N) (v : V) (r : Round) :
    ∃ a, a ∈ Restated.actionAttestationFrom M S before v r := by
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc before.st.core.toHealing
    (Restated.Vocabulary.Execution.Setup.a M S r) before.cache
  obtain ⟨st, hst⟩ := facts.dt.duties_update_confirmation_with_nonempty (M.gradeContract c) S.E S.hc
    (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r))
    (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1)
  obtain ⟨D, hD⟩ := facts.dt.attest_with_nonempty (M.gradeContract (M.mkNode st before.record c).cache)
    S.E S.hc (S.node v) (M.mkNode st before.record c).st (M.mkNode st before.record c).record
  exact ⟨D.2.2, M.mkNode st before.record c, ⟨c, hc, st, hst, rfl⟩, D.1, D.2.1, hD⟩

open scoped DC in
/-- `m >>= k` can return `b` exactly when `m` can return some `a` and `k a` can return `b`. -/
private theorem returns_bind_iff_gd {α β : Type} (m : DC.NDRE α) (k : α → DC.NDRE β)
    (b : β) : (m >>= k) ⇢ b ↔ ∃ a, m ⇢ a ∧ k a ⇢ b := by
  unfold Record.Returns
  simp only [ExceptT.run_bind, Set.bind_def]
  constructor
  · intro h
    obtain ⟨e, he, hb⟩ := Set.mem_iUnion₂.mp h
    cases e with
    | ok a => exact ⟨a, he, hb⟩
    | error err => simp at hb
  · rintro ⟨a, ha, hb⟩
    exact Set.mem_iUnion₂.mpr ⟨_, ha, hb⟩

/-- For every node state `n`, the finality-gadget source read at `n` can return some value. -/
private theorem actionFGSource_nonempty_gd (facts : Record.Facts M) (S : Setup V)
    (n : M.N) : ∃ o, Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n ⇢ o := by
  obtain ⟨A2, hA2⟩ := facts.dt.grade2_block_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s)
  obtain ⟨o, ho⟩ := facts.dt.fg_source_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s) A2
  exact ⟨o, (returns_bind_iff_gd _ _ _).2 ⟨A2, hA2, ho⟩⟩

/-- If step `n` is the tick at round `r`'s action time, `v_1` is in `freshAttestersW S Sched x r m`,
    and `v_1` is not held by the adversary at any time up to round `r`'s action time, then the node
    state `v_1`'s tick at step `n` reads passes the grade-2 awake test `M.awake_for_grade2` of round
    `r` under `Setup.alwaysAwake S`. -/
private theorem awake_for_grade2_of_mem_freshAttestersW_gd (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    {r : Round} {n m : Nat} {v_1 : V}
    (hn : Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S r)))
    (hq : v_1 ∈ Restated.freshAttestersW M S Sched x r m)
    (hhon : ∀ t' ≤ Restated.Vocabulary.Execution.Setup.a M S r, v_1 ∉ Sched.adv t') :
    M.awake_for_grade2 (Setup.alwaysAwake S) v_1
      (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S r) x[n] v_1) r := by
  obtain ⟨τ, hlbl, hτ⟩ := id hn
  have hw := ((Restated.mem_freshAttestersW facts).mp hq).1
  refine Restated.run_fact_g2 facts S Sched x n τ r v_1 hlbl hτ ?_ (by rw [hτ]; exact hhon)
  have h12 := twelve_delta_le_wAttest S
  have hΔ := S.E.Δ_pos
  simp only [Restated.activeRoundW, Restated.attestersAt, Schedule.awakeThroughout, Finset.mem_inf,
    Finset.mem_Icc] at hw ⊢
  try rw [facts.gr.early_g2_eq S r] at hw
  rw [facts.gr.early_g2_eq S r]
  intro t ht
  exact hw t ⟨by linarith [ht.1], ht.2⟩

/-- Under the premises of `freshSGHeadsAtLate_of_premises`, with every tick of the honest active
    attesters concerned having an outcome (`hneTick`, `hneAtt`): if `v` is a member of
    `HonRound S Sched (r + 1)`, `p` a phase of round `r + 1` whose domain time is at or before
    `S.a (r + 1)`, `m` the last step before that time, and the grade test of `B` on `v`'s store at
    `m` for round `r + 1` at `p`'s cutoffs can return `true`, then some member `v_1` of
    `HonRound S Sched r` sent at the round-`r` tick a round-`r` attestation `a` it signed, whose
    confirmed root names a body `C` of `v_1`'s store after that tick, and `B` is an ancestor of `C`. -/
theorem graded_preceq_freshSG_of_premises (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
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
    {v : V} (hv : v ∈ Restated.HonRound M S Sched (r + 1)) {p : Protocol.Phase}
    (hdom : M.domain S.E S.hc (r + 1) p ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)))
    {m : Nat} (hm : Restated.stepBeforeInstant M x m (M.domain S.E S.hc (r + 1) p))
    (B : Block V)
    (hgrade : M.gradeBool S.E (M.gradeView (M.toHealing (x[m][v].st).st.core))
      (x[m][v].st).st.core.F S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) p)
      (M.late S.E S.hc (r + 1) p) B ⇢ true)
    (hneTick : ∀ v ∈ Restated.HonRound M S Sched (r + 1), ∀ (n' : Nat) (t' : Int),
      Restated.tickStepAt M x n' t' → t' % S.E.Δ = 0 → v ∈ Sched.awake t' \ Sched.adv t' → t' ≤ Restated.Vocabulary.Execution.Setup.a M S (r + 1) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched t' x[n'] v) t' ⇢ out)
    (hneAtt : ∀ v ∈ Restated.HonRound M S Sched r, ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S r) x[n] v) (Restated.Vocabulary.Execution.Setup.a M S r) ⇢ out)
    (hrecvR : Restated.NextRoundReceipts M S Sched x r) :
    ∃ v_1 ∈ Restated.HonRound M S Sched r, ∃ a : NamedAttestation V,
      a.round = r ∧ a.val_index = v_1 ∧
      (⟨v_1, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n + 1].sent ∧
      ∃ C : NamedBlock V, C ∈ (x[n + 1][v_1].st).st.bodies ∧ a.confirmed = some C.root ∧
        Block.Preceq B C.erase := by
  have hn := hinv.tick
  -- a round opens at or before its action time
  have hopen : M.opening S.E S.hc r ≤ Restated.Vocabulary.Execution.Setup.a M S r := by
    show _ ≤ M.a S.hc S.E.Δ r
    rw [facts.gr.opening_eq_proposal_time, facts.sch.a_eq_confirmation_time]
    exact facts.sch.proposal_time_le_confirmation_time _ _
  have hgstr : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S r) :=
    le_trans (Restated.gst_le_switchOpening facts S tGAT tE gap hgst hlen)
      (le_trans (Restated.switchOpening_le_opening facts S hr) hopen)
  have htm := Restated.time_le_action_succ_of_stepBefore facts S Sched x htd hdom hm
  have hrs := Restated.roundSleepinessW_switchOpening_of_phase facts S Sched tGAT tE gap hgst hlen hmono hthird
    hphase hrsW
  have hheadsP := Restated.freshSGHeadsAtLate_of_premises facts (hcross := hcross) S Sched x tE hexec hmono htd hsync hmult tGAT
    gap hgst hlen hcv hthird hphase hrsW hcs hr hinv hneTick hneAtt
  have hara : Restated.Vocabulary.Execution.Setup.a M S r ≤ Restated.Vocabulary.Execution.Setup.a M S (r + 1) :=
    le_trans (Restated.action_le_time_of_stepBefore facts S Sched x htd hm) htm
  obtain ⟨v_1, hv_1, C, hC, hconf, hBC⟩ := Restated.graded_preceq_freshSG_recv facts S Sched x hexec htd hn
    hgstr hm (hrecvR.at facts hv p)
    (fun t ht hin => (Finset.mem_sdiff.1 hv).2 (hmono t _ (le_trans ht htm) hin))
    (Restated.hexp_of_domain facts S htm)
    (fun k hk v_2 hv_2 a ha _ => Restated.hroom_of_fresh facts S Sched x hexec hn
      (fun t ht => Restated.honestThrough_of_mem_freshAttestersW facts hv_2 t
        (le_trans ht (Restated.time_mono_int facts S Sched x (le_of_lt hk)))) a ha)
    (fun v_2 hv_2 a ha C hC hc => hheadsP v hv p hdom m hm v_2 hv_2 C hC a ha hc)
    (fun v_2 _ a ha root hc => Restated.hhead_mem_of_tick facts S Sched x n r v_2 a ha root hc)
    (Restated.hhalf_of_roundSleepinessW facts S Sched x hexec htd hmono hrs
      (Restated.switchOpening_le_opening facts S (le_trans hr (Nat.le_succ r)))
      (Restated.eta_le_of_switchRound_le facts S tGAT tE gap hgst hlen hr) hdom hm)
    B hgrade (facts.ndRun.tick_outcome_sts S Sched x hexec.idealization.root_injective hexec.honestRootsNew)
    (fun v_2 hv_2 => hneAtt v_2 (Restated.hfreshH_of_stepBefore facts S Sched x htd hm hv_2))
  have hqr : v_1 ∉ Sched.adv ((Restated.Vocabulary.Execution.Setup.a M S r)) :=
    Restated.honestThrough_of_mem_freshAttestersW facts hv_1 _ (Restated.action_le_time_of_stepBefore facts S Sched x htd hm)
  obtain ⟨a, ha⟩ := actionAttestationFrom_nonempty_gd facts (Setup.alwaysAwake S) (x[n][v_1].st) v_1 r
  have hsent := Restated.fresh_attests facts S Sched x hn
    (Restated.freshAttestersW_subset_freshAttesters facts S Sched x r m hv_1) hqr
    (hneAtt v_1 (Restated.hfreshH_of_stepBefore facts S Sched x htd hm hv_1))
    (awake_for_grade2_of_mem_freshAttestersW_gd facts S Sched x hn hv_1 (fun t ht =>
      Restated.honestThrough_of_mem_freshAttestersW facts hv_1 t
        (le_trans ht (Restated.action_le_time_of_stepBefore facts S Sched x htd hm)))) a ha
  exact ⟨v_1, Restated.hfreshH_of_stepBefore facts S Sched x htd hm hv_1, a,
    Restated.actionAttestationFrom_round facts (Setup.alwaysAwake S) _ v_1 r a ha,
    Restated.actionAttestationFrom_val_index facts (Setup.alwaysAwake S) _ v_1 r a ha, hsent, C, hC,
    hconf a ha, hBC⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Under the premises of `graded_preceq_freshSG_of_premises`, if `v` and `v'` are members of
    `HonRound S Sched (r + 1)`, the grade test of `B` on `v`'s store at the step before the domain
    time of a phase `p` and that of `B'` on `v'`'s store at the step before the domain time of a
    phase `p'` can return `true`, both times at or before `S.a (r + 1)`, then `B` and `B'` lie on
    one chain. -/
theorem graded_compatible_graded_of_premises (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
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
    {v v' : V} (hv : v ∈ Restated.HonRound M S Sched (r + 1)) (hv' : v' ∈ Restated.HonRound M S Sched (r + 1))
    {p p' : Protocol.Phase}
    (hdom : M.domain S.E S.hc (r + 1) p ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)))
    (hdom' : M.domain S.E S.hc (r + 1) p' ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)))
    {m m' : Nat} (hm : Restated.stepBeforeInstant M x m (M.domain S.E S.hc (r + 1) p))
    (hm' : Restated.stepBeforeInstant M x m' (M.domain S.E S.hc (r + 1) p'))
    {B B' : Block V}
    (hgrade : M.gradeBool S.E (M.gradeView (M.toHealing (x[m][v].st).st.core))
      (x[m][v].st).st.core.F S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) p)
      (M.late S.E S.hc (r + 1) p) B ⇢ true)
    (hgrade' : M.gradeBool S.E (M.gradeView (M.toHealing (x[m'][v'].st).st.core))
      (x[m'][v'].st).st.core.F S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) p')
      (M.late S.E S.hc (r + 1) p') B' ⇢ true)
    (hneTick : ∀ v ∈ Restated.HonRound M S Sched (r + 1), ∀ (n' : Nat) (t' : Int),
      Restated.tickStepAt M x n' t' → t' % S.E.Δ = 0 → v ∈ Sched.awake t' \ Sched.adv t' → t' ≤ Restated.Vocabulary.Execution.Setup.a M S (r + 1) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched t' x[n'] v) t' ⇢ out)
    (hneAtt : ∀ v ∈ Restated.HonRound M S Sched r, ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S r) x[n] v) (Restated.Vocabulary.Execution.Setup.a M S r) ⇢ out)
    (hrecvR : Restated.NextRoundReceipts M S Sched x r) :
    Block.compatible B B' = true := by
  obtain ⟨v_1, hv_1, a, har, hai, has, C, hC, hac, hBC⟩ :=
    Restated.graded_preceq_freshSG_of_premises (hrecvR := hrecvR) facts (hcross := hcross) S Sched x tE hexec hmono htd hsync hmult tGAT gap hgst hlen
      hcv hthird hphase hrsW hcs hr hinv hv hdom hm B hgrade hneTick hneAtt
  obtain ⟨v_2, hv_2, a', har', hai', has', C', hC', hac', hBC'⟩ :=
    Restated.graded_preceq_freshSG_of_premises (hrecvR := hrecvR) facts (hcross := hcross) S Sched x tE hexec hmono htd hsync hmult tGAT gap hgst hlen
      hcv hthird hphase hrsW hcs hr hinv hv' hdom' hm' B' hgrade' hneTick hneAtt
  exact compatible_of_preceq_of_preceq hBC hBC'
    (hinv.sgPairwise v_1 hv_1 v_2 hv_2 a a' har hai has har' hai' has' C C' hC hac hC' hac')

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Under the premises of `graded_preceq_freshSG_of_premises`, with `n'` the tick step at
    `S.a (r + 1)`, and if the round-`(r + 1)` confirmed block of every member of
    `freshAttestersW S Sched x (r + 1) (n' + 1)` lies on one chain with every round-`r` SG block of
    a member of `HonRound S Sched r`, then for a choice `att` of the round-`(r + 1)` action
    attestations, every block a member of `HonRound S Sched (r + 1)` grades at least 1 for round
    `r + 1`, at a phase whose domain time is at or before `S.a (r + 1)`, that has `T` as an
    ancestor, lies on one chain with the round-`(r + 1)` anchor read along `att`. -/
theorem gradeDescendant_ofConfirmedFreshSG (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
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
    {att : V → NamedAttestation V} (hatt : Restated.ActionAttestationsOf M S Sched x r n' att)
    (hconfSG : Restated.ConfirmedCompatibleFreshSG M S Sched x r n n')
    (hneTick : ∀ v ∈ Restated.HonRound M S Sched (r + 1), ∀ (n' : Nat) (t' : Int),
      Restated.tickStepAt M x n' t' → t' % S.E.Δ = 0 → v ∈ Sched.awake t' \ Sched.adv t' → t' ≤ Restated.Vocabulary.Execution.Setup.a M S (r + 1) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched t' x[n'] v) t' ⇢ out)
    (hneAtt : ∀ v ∈ Restated.HonRound M S Sched r, ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S r) x[n] v) (Restated.Vocabulary.Execution.Setup.a M S r) ⇢ out)
    (hrecvR : Restated.NextRoundReceipts M S Sched x r) :
    ∀ v ∈ Restated.HonRound M S Sched (r + 1),
    ∀ p : Protocol.Phase, M.domain S.E S.hc (r + 1) p ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) →
    ∀ m : Nat, Restated.stepBeforeInstant M x m (M.domain S.E S.hc (r + 1) p) →
    ∀ B : Block V,
      M.gradeBool S.E (M.gradeView (M.toHealing (x[m][v].st).st.core))
          (x[m][v].st).st.core.F S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) p)
          (M.late S.E S.hc (r + 1) p) B ⇢ true →
      Block.Preceq T.erase B → B ≠ T.erase →
      Block.compatible B (Restated.newAnchor M S Sched x r n' att T).erase = true := by
  classical
  intro v hv p hdom m hm B hgrade hTB _
  by_cases hex : ∃ C : NamedBlock V, Restated.NewAnchorSpec M S Sched x r n' att T C
  · have hchoice : Restated.newAnchor M S Sched x r n' att T = hex.choose := by
      show (if h : ∃ C : NamedBlock V, Restated.NewAnchorSpec M S Sched x r n' att T C then h.choose else T)
        = hex.choose
      rw [dif_pos hex]
    obtain ⟨q, hqW, hmem, h₀, tmo, hvote⟩ := hex.choose_spec.2.2.2
    have hq : q ∈ Restated.freshAttesters M S Sched x (r + 1) (n' + 1) :=
      Restated.freshAttestersW_subset_freshAttesters facts S Sched x (r + 1) (n' + 1) hqW
    -- the node state of the action read `att q` was computed from
    obtain ⟨nq, hnq, ns, rec, hD⟩ := hatt q hqW
    obtain ⟨o, ho⟩ := actionFGSource_nonempty_gd facts (Setup.alwaysAwake S) nq
    obtain ⟨Cfg, rfl, hpre⟩ :=
      Restated.entry_preceq_source facts S Sched x hexec hn' hq hmem rfl nq hnq (ns, rec, att q) hD
        hvote _ ho
    rw [hchoice]
    rcases Restated.source_cases facts S (x[n'][q].st) (r + 1) nq hnq Cfg ho with hlc | hQ
    · obtain ⟨v_1, hv_1, a, har, hai, has, C, hC, hac, hBC⟩ :=
        Restated.graded_preceq_freshSG_of_premises (hrecvR := hrecvR) facts (hcross := hcross) S Sched x tE hexec hmono htd hsync hmult tGAT gap hgst
          hlen hcv hthird hphase hrsW hcs hr hinv hv hdom hm B hgrade hneTick hneAtt
      exact compatible_of_preceq_of_preceq hBC (preceq_trans_Preceq hpre hlc)
        (hconfSG q hqW v_1 hv_1 a har hai has C hC hac _ ⟨nq, hnq, rfl⟩)
    · -- the grade-2 block of the grade read is `Cfg`
      obtain ⟨g, hg⟩ := facts.gr.read_nonempty (M.gradeContract nq.cache) S.E S.hc
        (M.toHealing nq.st.core) (r + 1)
      have hgQ : g.Q2 = some Cfg := hQ g ((facts.nd.gradeContract_read _ _ _ _ _ _).1 hg)
      obtain ⟨o₂, ho₂⟩ := facts.gr.grade2Block_nonempty (M.toHealing nq.st.core)
        (M.readFrame nq.cache (M.toHealing nq.st.core) (r + 1))
      have hgo : g.Q2 = o₂ :=
        facts.nd.ModelProperties_gradeContract_read_Q2 nq.cache S.E S.hc (M.toHealing nq.st.core)
          (r + 1) g hg o₂ ho₂
      obtain ⟨root, hroot, hQroot⟩ := facts.gr.grade2Block_preceq_root o₂ ho₂ (by rw [← hgo, hgQ])
      obtain ⟨m₂, G, hm₂, hG, hrootG⟩ :=
        Restated.actionFrame_g2_provenance facts S Sched x hn' q root _ ⟨nq, hnq, rfl⟩ hroot
      have hqH : q ∈ Restated.HonRound M S Sched (r + 1) :=
        Restated.freshAttestersW_subset_honRound facts S Sched x (le_of_eq (Restated.tickStepAt_time facts x hn').1.symm) hqW
      obtain ⟨b, hb⟩ := facts.gr.gradeBool_nonempty S.E (M.gradeView (M.toHealing (x[m₂][q].st).st.core))
        (x[m₂][q].st).st.core.F S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) .g2)
        (M.late S.E S.hc (r + 1) .g2) G
      have hbt := hG b hb
      subst hbt
      have hBG := Restated.graded_compatible_graded_of_premises (hrecvR := hrecvR) facts (hcross := hcross) S Sched x tE hexec hmono htd hsync hmult
        tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr hinv hv hqH hdom
        (facts.gr.domain_le_action S (r + 1) .g2) hm hm₂ hgrade hb hneTick hneAtt
      exact compatible_of_preceq_of_preceq (preceq_eq_true_iff_Preceq.mp (Block.preceq_self B))
        (preceq_trans_Preceq hpre (preceq_trans_Preceq hQroot hrootG)) hBG
  · have hchoice : Restated.newAnchor M S Sched x r n' att T = T := by
      show (if h : ∃ C : NamedBlock V, Restated.NewAnchorSpec M S Sched x r n' att T C then h.choose else T)
        = T
      rw [dif_neg hex]
    rw [hchoice]
    exact compatible_of_preceq_common_Preceq (preceq_eq_true_iff_Preceq.mp (Block.preceq_self B)) hTB

end

end DecoupledConsensusModel.Sts.Restated
