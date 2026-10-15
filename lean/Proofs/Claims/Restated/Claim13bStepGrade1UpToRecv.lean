import Proofs.Claims.Restated.Claim13bStepGrade1Recv
import Proofs.Claims.Restated.Claim13bK_GradeDescendantUpTo
import Proofs.Claims.Restated.Claim13bK_ConeAnchorUpToRecv
import Proofs.Claims.Restated.Claim13bK_PrevHeadsStepUpToRecv
import Proofs.Claims.Restated.Claim13bW_ReceiptBefore

/-!
# The round invariant's grade-1 clauses over the grade-1 performers, at the next round, with synchrony up to it

At one step of the round invariant, from round `r` to round `r + 1`: every block a grade-1 performer
of round `r + 1` grades at least 1 at the grade-1 phase lies on one chain with the round-`(r + 1)`
anchor, and is an ancestor of a round-`r` SG block of an honest active attester of round `r`. A
grade-1 performer need not be awake at `S.a r`: it reads round `r`'s attestations from its receipt,
here a hypothesis, `ReceivesRoundAttestationsBefore` for every grade-1 performer, since synchrony
is assumed only up to round `r + 1`'s action instant. Stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

local macro "pGD% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13bK_GradeDescendantUpTo)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Under the premises of `graded_preceq_freshSG_at_awakeReader_upTo_recv`, with synchrony up to
    `S.a (r + 1)` and the grade-1 performers' receipts:
    every block a grade-1 performer `v` of round `r + 1` grades at least 1 for round `r + 1` at the
    grade-1 phase, read at the last step `m` before that phase's domain instant, is an ancestor of
    the round-`r` SG block of some member of `HonRound S Sched r`, named by the attestation it sent
    at round `r`'s tick. -/
theorem graded_preceq_freshSG_of_grade1Performer_upTo (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    {r : Round}
    (hsync : Restated.SynchronyFromWakeBefore M S x ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    -- Every grade-1 performer of round `r + 1` receives round `r`'s honest attestations before round
    -- `r + 1`'s grade-1 first cutoff.
    (hrecvW : ∀ v ∈ Restated.grade1PerformersW M S Sched (r + 1),
      Restated.ReceivesRoundAttestationsBefore M S Sched x r v (M.early S.E S.hc (r + 1) .g1))
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
    {v : V} (hv : v ∈ Restated.grade1PerformersW M S Sched (r + 1))
    {m : Nat} (hm : Restated.stepBeforeInstant M x m (M.domain S.E S.hc (r + 1) .g1))
    (B : Block V)
    (hgrade : M.gradeBool S.E (M.gradeView (M.toHealing (x[m][v].st).st.core))
      (x[m][v].st).st.core.F S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) .g1)
      (M.late S.E S.hc (r + 1) .g1) B ⇢ true) :
    ∃ v_1 ∈ Restated.HonRound M S Sched r, ∃ a : NamedAttestation V,
      a.round = r ∧ a.val_index = v_1 ∧
      (⟨v_1, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n + 1].sent ∧
      ∃ C : NamedBlock V, C ∈ (x[n + 1][v_1].st).st.bodies ∧ a.confirmed = some C.root ∧
        Block.Preceq B C.erase := by
  have hopen : M.opening S.E S.hc r ≤ Restated.Vocabulary.Execution.Setup.a M S r := by
    show _ ≤ M.a S.hc S.E.Δ r
    rw [facts.gr.opening_eq_proposal_time, facts.sch.a_eq_confirmation_time]
    exact facts.sch.proposal_time_le_confirmation_time _ _
  have hgstr : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S r) :=
    le_trans (Restated.gst_le_switchOpening facts S tGAT tE gap hgst hlen)
      (le_trans (Restated.switchOpening_le_opening facts S hr) hopen)
  obtain ⟨hwin, hvS⟩ := Finset.mem_sdiff.1 hv
  exact Restated.graded_preceq_freshSG_at_awakeReader_upTo_recv facts (hcross := hcross) S Sched x tE hexec
    hmono htd hsync hmult tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr hinv
    (facts.gr.domain_le_action S (r + 1) .g1) _ (early_g1_sub_delta_le_late_g1_sub facts S (r + 1)) hwin
    (hrecvW v hv)
    hvS hm B hgrade

/-- Under the premises of `gradeDescendant_ofConfirmedFreshSG_upTo`, with the grade-1 performers'
    receipts: for a choice `att` of
    the round-`(r + 1)` action attestations, every block a grade-1 performer of round `r + 1` grades
    at least 1 for round `r + 1` at the grade-1 phase, that has `T` as a strict ancestor, lies on one
    chain with the round-`(r + 1)` anchor read along `att`. -/
theorem gradeDescendant_of_grade1Performer_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    {r : Round}
    (hsync : Restated.SynchronyFromWakeBefore M S x ((Restated.Vocabulary.Execution.Setup.a M S (r + 1)))) (hcatchB : Restated.CatchUpOnWakeBefore M S x ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    -- Every grade-1 performer of round `r + 1` receives round `r`'s honest attestations before round
    -- `r + 1`'s grade-1 first cutoff.
    (hrecvW : ∀ v ∈ Restated.grade1PerformersW M S Sched (r + 1),
      Restated.ReceivesRoundAttestationsBefore M S Sched x r v (M.early S.E S.hc (r + 1) .g1))
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
    {att : V → NamedAttestation V} (hatt : Restated.ActionAttestationsOf M S Sched x r n' att)
    (hconfSG : Restated.ConfirmedCompatibleFreshSG M S Sched x r n n')
    (hneTick : ∀ v ∈ Restated.HonRound M S Sched (r + 1), ∀ (n' : Nat) (t' : Int),
      Restated.tickStepAt M x n' t' → t' % S.E.Δ = 0 → v ∈ Sched.awake t' \ Sched.adv t' → t' ≤ Restated.Vocabulary.Execution.Setup.a M S (r + 1) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched t' x[n'] v) t' ⇢ out)
    (hneAtt : ∀ v ∈ Restated.HonRound M S Sched r, ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S r) x[n] v) (Restated.Vocabulary.Execution.Setup.a M S r) ⇢ out) :
    ∀ v ∈ Restated.grade1PerformersW M S Sched (r + 1),
    ∀ m : Nat, Restated.stepBeforeInstant M x m (M.domain S.E S.hc (r + 1) .g1) →
    ∀ B : Block V,
      M.gradeBool S.E (M.gradeView (M.toHealing (x[m][v].st).st.core))
          (x[m][v].st).st.core.F S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) .g1)
          (M.late S.E S.hc (r + 1) .g1) B ⇢ true →
      Block.Preceq T.erase B → B ≠ T.erase →
      Block.compatible B (Restated.newAnchor M S Sched x r n' att T).erase = true := by
  have hrecvR : Restated.NextRoundReceipts M S Sched x r :=
    Restated.nextRoundReceipts_of_before facts S Sched x hsync hcatchB
      (Restated.gst_le_action_of_switchRound_le facts S tGAT tE gap hgst hlen hr)
      (by have := Restated.early_g1_le_action_rb facts S (r + 1); have := S.E.Δ_pos; linarith)
  classical
  intro v hv m hm B hgrade hTB _
  have hBv := graded_preceq_freshSG_of_grade1Performer_upTo facts S Sched x tE hexec hmono htd hsync hrecvW
    hmult tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr hinv hcross hv hm B hgrade
  by_cases hex : ∃ C : NamedBlock V, Restated.NewAnchorSpec M S Sched x r n' att T C
  · have hchoice : Restated.newAnchor M S Sched x r n' att T = hex.choose := by
      show (if h : ∃ C : NamedBlock V, Restated.NewAnchorSpec M S Sched x r n' att T C then h.choose else T)
        = hex.choose
      rw [dif_pos hex]
    obtain ⟨q, hqW, hmem, h₀, tmo, hvote⟩ := hex.choose_spec.2.2.2
    have hq : q ∈ Restated.freshAttesters M S Sched x (r + 1) (n' + 1) :=
      Restated.freshAttestersW_subset_freshAttesters facts S Sched x (r + 1) (n' + 1) hqW
    obtain ⟨nq, hnq, ns, rec, hD⟩ := hatt q hqW
    obtain ⟨o, ho⟩ := (pGD% actionFGSource_nonempty_gdu) facts (Setup.alwaysAwake S) nq
    obtain ⟨Cfg, rfl, hpre⟩ :=
      Restated.entry_preceq_source facts S Sched x hexec hn' hq hmem rfl nq hnq (ns, rec, att q) hD
        hvote _ ho
    rw [hchoice]
    rcases Restated.source_cases facts S (x[n'][q].st) (r + 1) nq hnq Cfg ho with hlc | hQ
    · obtain ⟨v_1, hv_1, a, har, hai, has, C, hC, hac, hBC⟩ := hBv
      exact compatible_of_preceq_of_preceq hBC (preceq_trans_Preceq hpre hlc)
        (hconfSG q hqW v_1 hv_1 a har hai has C hC hac _ ⟨nq, hnq, rfl⟩)
    · obtain ⟨g, hg⟩ := facts.gr.read_nonempty (M.gradeContract nq.cache) S.E S.hc
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
      obtain ⟨v_1, hv_1, a, har, hai, has, C, hC, hac, hBC⟩ := hBv
      obtain ⟨v_2, hv_2, a', har', hai', has', C', hC', hac', hGC'⟩ :=
        Restated.graded_preceq_freshSG_of_premises_upTo (hrecvR := hrecvR) facts (hcross := hcross) S Sched x tE hexec hmono htd
          hsync hmult tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr hinv hqH
          (facts.gr.domain_le_action S (r + 1) .g2) hm₂ G hb hneTick hneAtt
      have hBG : Block.compatible B G = true :=
        compatible_of_preceq_of_preceq hBC hGC'
          (hinv.sgPairwise v_1 hv_1 v_2 hv_2 a a' har hai has har' hai' has' C C' hC hac hC' hac')
      exact compatible_of_preceq_of_preceq (preceq_eq_true_iff_Preceq.mp (Block.preceq_self B))
        (preceq_trans_Preceq hpre (preceq_trans_Preceq hQroot hrootG)) hBG
  · have hchoice : Restated.newAnchor M S Sched x r n' att T = T := by
      show (if h : ∃ C : NamedBlock V, Restated.NewAnchorSpec M S Sched x r n' att T C then h.choose else T)
        = T
      rw [dif_neg hex]
    rw [hchoice]
    exact compatible_of_preceq_common_Preceq (preceq_eq_true_iff_Preceq.mp (Block.preceq_self B)) hTB

/-- The `grade1` clause over the grade-1 performers at round `r + 1`, at the round-`(r + 1)` anchor
    read along `att`, under the premises of `gradeDescendant_of_grade1Performer_upTo` and with `T` an
    ancestor of that anchor: every block a grade-1 performer of round `r + 1` grades at least 1 for
    round `r + 1` at the grade-1 phase lies on one chain with it. -/
theorem grade1ClauseOverPerformers_at_succ_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    {r : Round}
    (hsync : Restated.SynchronyFromWakeBefore M S x ((Restated.Vocabulary.Execution.Setup.a M S (r + 1)))) (hcatchB : Restated.CatchUpOnWakeBefore M S x ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    -- Every grade-1 performer of round `r + 1` receives round `r`'s honest attestations before round
    -- `r + 1`'s grade-1 first cutoff.
    (hrecvW : ∀ v ∈ Restated.grade1PerformersW M S Sched (r + 1),
      Restated.ReceivesRoundAttestationsBefore M S Sched x r v (M.early S.E S.hc (r + 1) .g1))
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
    {att : V → NamedAttestation V} (hatt : Restated.ActionAttestationsOf M S Sched x r n' att)
    (hold : Block.Preceq T.erase (Restated.newAnchor M S Sched x r n' att T).erase)
    (hconfSG : Restated.ConfirmedCompatibleFreshSG M S Sched x r n n')
    (hneTick : ∀ v ∈ Restated.HonRound M S Sched (r + 1), ∀ (n' : Nat) (t' : Int),
      Restated.tickStepAt M x n' t' → t' % S.E.Δ = 0 → v ∈ Sched.awake t' \ Sched.adv t' → t' ≤ Restated.Vocabulary.Execution.Setup.a M S (r + 1) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched t' x[n'] v) t' ⇢ out)
    (hneAtt : ∀ v ∈ Restated.HonRound M S Sched r, ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S r) x[n] v) (Restated.Vocabulary.Execution.Setup.a M S r) ⇢ out) :
    Restated.Grade1ClauseOverPerformers M S Sched x (r + 1) (Restated.newAnchor M S Sched x r n' att T) := by
  classical
  intro v hv m hm B b hb hbt
  subst hbt
  have hopen : M.opening S.E S.hc r ≤ Restated.Vocabulary.Execution.Setup.a M S r := by
    show _ ≤ M.a S.hc S.E.Δ r
    rw [facts.gr.opening_eq_proposal_time, facts.sch.a_eq_confirmation_time]
    exact facts.sch.proposal_time_le_confirmation_time _ _
  have hgstr : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S r) :=
    le_trans (Restated.gst_le_switchOpening facts S tGAT tE gap hgst hlen)
      (le_trans (Restated.switchOpening_le_opening facts S hr) hopen)
  obtain ⟨hwin, hvS⟩ := Finset.mem_sdiff.1 hv
  have hBT : Block.compatible B T.erase = true :=
    Restated.grade1_compatible_at_awakeReader_upTo_recv facts (hcross := hcross) S Sched x tE hexec hmono htd
      (fun k w sm hsend hle haw => hsync k w sm hsend (le_trans hle (le_trans
        (facts.gr.late_le_domain S (r + 1) .g1) (facts.gr.domain_le_action S (r + 1) .g1))) haw) hmult tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr hinv
      (facts.gr.domain_le_action S (r + 1) .g1) _ (early_g1_sub_delta_le_late_g1_sub facts S (r + 1)) hwin
      (hrecvW v hv)
      hvS hm B hb
      (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›)
      hneAtt
  rcases compatible_cases hBT with hle | hge
  · exact compatible_of_preceq_common_Preceq (preceq_trans_Preceq hle hold)
      (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _))
  · by_cases heq : B = T.erase
    · rw [heq]
      exact compatible_of_preceq_common_Preceq hold
        (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _))
    · exact gradeDescendant_of_grade1Performer_upTo (hcatchB := hcatchB) facts S Sched x tE hexec hmono htd hsync hrecvW hmult tGAT gap
        hgst hlen hcv hthird hphase hrsW hcs hr hinv hcross hn' hatt hconfSG hneTick hneAtt v hv m hm B hb
        hge heq

/-- The `gradedUnderPrevSG` clause over the grade-1 performers at round `r + 1`, at round `r`'s tick
    step `n`, under the premises of `graded_preceq_freshSG_of_grade1Performer_upTo`. -/
theorem gradedUnderPrevSGOverPerformers_at_succ_upTo (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    {r : Round}
    (hsync : Restated.SynchronyFromWakeBefore M S x ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    -- Every grade-1 performer of round `r + 1` receives round `r`'s honest attestations before round
    -- `r + 1`'s grade-1 first cutoff.
    (hrecvW : ∀ v ∈ Restated.grade1PerformersW M S Sched (r + 1),
      Restated.ReceivesRoundAttestationsBefore M S Sched x r v (M.early S.E S.hc (r + 1) .g1))
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
      Restated.StepFinalizedCrossingUnderAnchor M S Sched x r n'' T) :
    Restated.GradedUnderPrevSGOverPerformers M S Sched x (r + 1) n := by
  intro v hv m hm B b hb hbt
  subst hbt
  simpa only [Nat.add_sub_cancel] using
    graded_preceq_freshSG_of_grade1Performer_upTo facts S Sched x tE hexec hmono htd hsync hrecvW hmult tGAT gap
      hgst hlen hcv hthird hphase hrsW hcs hr hinv hcross hv hm B hb

end

end DecoupledConsensusModel.Sts.Restated
