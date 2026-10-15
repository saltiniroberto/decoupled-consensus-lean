module
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.RecoverySelectedActionG2VoteCone
public import Proofs.Vocabulary.ModelProperties.grade2_block_with
public import Proofs.Vocabulary.ModelProperties.Store_toHealing
public import Proofs.Vocabulary.ModelProperties.fg_source_with
public import Proofs.Vocabulary.ModelProperties.deepest_clear
public import Proofs.Vocabulary.ModelProperties.update_confirmation_with
public import Proofs.Vocabulary.ModelProperties.Block_Preceq
public import Proofs.Vocabulary.Protocol.Grades.RelativeCrossReader
public import Proofs.Vocabulary.Protocol.Grades.HealthyHeadReady
public import Proofs.Vocabulary.Generic.SuffixHistory
public import Proofs.Vocabulary.Protocol.ForkChoice.Views.GoldfishCone
public import Proofs.Vocabulary.Protocol.Schedule.WeakProcessedTree
public import Proofs.Vocabulary.Execution.RecoveryActionLiveSourceSplit
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.RecoveryProposalConfirmationRead
public import Proofs.Vocabulary.Execution.ReleasedCertificateHeightProgress
import Proofs.Vocabulary.Objects.Final
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.GradeDelivery
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.ProposalVoteDuty
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.RecoveryFinalityFilterRetainedAdoption
import Proofs.Vocabulary.Protocol.Schedule.Action
import Proofs.Vocabulary.Protocol.Schedule.PostHealingReuse
import Proofs.Vocabulary.Protocol.ValidatorClient.RecoveryTimeout
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.Data.Rat.Floor
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar

@[expose] public section

/-!
# The next vote after a confirmation at a round opening

Facts that carry a block confirmed at a round's opening slot, and the G2 block selected at an honest
action, to the honest reads of the same round.
-/


namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Internal.PhaseGrades
open Internal.NamedRecoveryRead
open DecoupledConsensusModel.Protocol
open Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Inputs used when the action FG source is the selected Q2 block `B`: `B` is in every honest
    filtered tree at the G1 domain time and at the opening vote. -/
structure VoterAnchorSourceQ2Inputs
    (S : Setup V) (rho : Run V) (r : Round) (p : V) (B : Block V) : Prop where
  g1Target : ∀ w ∈ rho.honest,
    B ∈ filteredTree (readAt S rho (domain S.E S.hc r .g1) w)
  openingTarget : ∀ w ∈ rho.honest,
    B ∈ filteredTree (voteDutyRead S rho w (S.hc.opening_slot r))

/-- Inputs used at the first interior vote of round `r`: `B` is in every honest filtered tree there,
    and every honest prepared anchor there is compatible with `B`. -/
structure VoterAnchorSourceClearInputsMain
    (S : Setup V) (rho : Run V) (r : Round) (p : V) (B : Block V) : Prop where
  nextTarget : ∀ w ∈ rho.honest,
    B ∈ filteredTree (voteDutyRead S rho w (S.hc.opening_slot r + 1))
  anchorCompatible : ∀ w ∈ rho.honest, ∀ L,
    voterAnchorAt S rho w (S.hc.opening_slot r + 1) = L →
    Block.compatible L B = true

/-! ## Named-height handover -/


private theorem actionBody_runBlock_genuine
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) {r : Round} {D : NamedBlock V}
    (hD : D ∈ (actionStoreAt S rho v r).st.bodies) :
    RunBlock S rho D := by
  have hDpre : D ∈ (rho.stateBeforeTime S (S.a r) v).st.bodies := by
    simp only [actionStoreAt, actionReadAt, NamedActionReads.actionReadAt,
      NamedActionReads.actionReadFrom, NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime, Protocol.NamedStore.setClock]; exact hD
  obtain ⟨i, hi, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed.sorted (S.a r)
  change D ∈ (NamedRun.stateBeforeTime S rho (S.a r) v).st.bodies at hDpre
  rw [congrFun hi v] at hDpre
  exact Proofs.Bridges.runBlock_of_stateBefore_mem S hv hDpre

omit [Fintype V] in
private theorem named_self_genuine (D : NamedBlock V) :
    NamedBlock.Preceq D D := by
  cases D <;> simp [NamedBlock.Preceq, NamedBlock.preceq]

theorem actionBody_at_voteDuty_of_filtered
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} {p : V} (hp : p ∈ rho.honest)
    {B : NamedBlock V}
    (hBmem : B ∈ (actionStoreAt S rho p r).st.bodies)
    {w : V} (hw : w ∈ rho.honest) {s : Slot}
    (hfiltered : B.erase ∈ filteredTree
      (voteDutyRead S rho w s)) :
    B ∈ (voteDutyRead S rho w s).st.bodies := by
  let vote := Protocol.vote_time S.E s
  have hrawRead : B.erase ∈
      (voteDutyRead S rho w s).st.core.T :=
    Proofs.Records.get_filtered_block_tree_subset _ hfiltered
  have hrawPre : B.erase ∈
      (NamedRun.stateBeforeTime S rho vote w).st.core.T := by
    simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      vote] using hrawRead
  obtain ⟨D, hD, hDerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime
      S rho vote w hrawPre
  obtain ⟨n, hn, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix
    S rho adm.toNamedAdmissibleCore.toNamedScheduleWellFormed.sorted vote
  have hDprefix : D ∈ (NamedRun.stateBefore S rho n w).st.bodies := by
    rw [← hn]
    exact hD
  have hDrun : RunBlock S rho D :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S hw hDprefix
  have hBrun : RunBlock S rho B :=
    actionBody_runBlock_genuine S adm hp hBmem
  have hroot : D.root = B.root := by
    rw [← Proofs.NamedWire.erase_root D, hDerase, Proofs.NamedWire.erase_root]
  have hDB : D = B :=
    adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective
      D B hDrun hBrun D B (Or.inl (named_self_genuine D))
        (Or.inr (named_self_genuine B)) hroot
  subst D
  simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
    NamedActionReads.confirmationReadFrom,
    NamedActionReads.preparedCache, Protocol.NamedStore.setClock,
    vote] using hD

/-- If a body `B` of `p`'s round-`r` action store is in an honest `w`'s filtered tree at the first
    interior vote of round `r`, then `w`'s round-`r` action store holds `B`. -/
theorem actionBody_at_action_of_nextVoteFiltered
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} {p : V} (hp : p ∈ rho.honest)
    {B : NamedBlock V}
    (hBmem : B ∈ (actionStoreAt S rho p r).st.bodies)
    {w : V} (hw : w ∈ rho.honest)
    (hfiltered : B.erase ∈ filteredTree
      (voteDutyRead S rho w (S.hc.opening_slot r + 1))) :
    B ∈ (actionStoreAt S rho w r).st.bodies := by
  let vote := Protocol.vote_time S.E (S.hc.opening_slot r + 1)
  have hvote := actionBody_at_voteDuty_of_filtered
    S adm hp hBmem hw hfiltered
  have hvotePre : B ∈ (NamedRun.stateBeforeTime S rho vote w).st.bodies := by
    simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, Protocol.NamedStore.setClock,
      vote] using hvote
  have heqVote := congrFun (stateBeforeTime_eq_stateBefore_strictEventIndex
    S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed vote) w
  have heqAction := congrFun (stateBeforeTime_eq_stateBefore_strictEventIndex
    S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed (S.a r)) w
  rw [heqVote] at hvotePre
  have hactionPre : B ∈
      (NamedRun.stateBeforeTime S rho (S.a r) w).st.bodies := by
    rw [heqAction]
    exact NamedBodyRetention.stateBefore_bodies_mono S rho w
      (strictEventIndex_mono rho (next_vote_time_lt_action S r).le)
      hvotePre
  simp only [actionStoreAt, actionReadAt,
    NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
    NamedActionReads.confirmationReadFrom,
    NamedActionReads.preparedCache, NamedRun.stateBeforeTime, Protocol.NamedStore.setClock]; exact hactionPre

/-- The selected Q2 body of `p`'s round-`r` action is already held at `p`'s read before the
    round-`r` G2 domain time. -/
theorem selectedQ2_body_at_capture
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} {p : V} (hp : p ∈ rho.honest) {Q : NamedBlock V}
    (hselected : PhaseGrades.nodeQ2 S (actionReadAt S rho p r) r =
      some Q.erase)
    (hQmem : Q ∈ (actionStoreAt S rho p r).st.bodies) :
    Q ∈ (rho.stateBeforeTime S (domain S.E S.hc r .g2) p).st.bodies := by
  let i := strictEventIndex rho (S.a r)
  have hread := stateBeforeTime_eq_stateBefore_strictEventIndex
    S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed (S.a r)
  have hreadp := congrFun hread p
  have hselected0 := hselected
  simp only [PhaseGrades.nodeQ2, PhaseGrades.nodeRead,
    NamedProfile.gradeContract, DecoupledConsensusModel.Protocol.frameContract] at hselected0
  unfold actionReadAt NamedActionReads.actionReadAt at hselected0
  rw [hreadp] at hselected0
  have hselected' : Protocol.grade2_block_with
      (NamedProfile.gradeContract
        (NamedActionReads.actionReadFrom S
          (NamedRun.stateBefore S rho i p) r).cache)
      S.E S.hc
      (NamedActionReads.actionReadFrom S
        (NamedRun.stateBefore S rho i p) r).st.core.toHealing r =
        some Q.erase := by
    simp only [i]; exact hselected0
  obtain ⟨j, raw, -, hj, hfreeze, hQraw⟩ :=
    contractQ2_capture_at_action_index S rho i p r hselected'
  have hrawTree : raw ∈ (rho.stateBefore S j p).st.core.T := by
    exact (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hfreeze)).1
  have hQTree : Q.erase ∈ (rho.stateBefore S j p).st.core.T := by
    have hpc := Proofs.NamedStoreBridge.parentClosed_stateBefore S rho j p
    exact Proofs.Records.mem_of_preceq ((parentClosed_iff _).mp hpc).2
      Q.erase raw hrawTree hQraw
  obtain ⟨D, hD, hDerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore S rho j p hQTree
  have hDrun : RunBlock S rho D :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S hp hD
  have hQrun : RunBlock S rho Q :=
    actionBody_runBlock_genuine S adm hp hQmem
  have hroot : D.root = Q.root := by
    rw [← Proofs.NamedWire.erase_root D, hDerase, Proofs.NamedWire.erase_root]
  have hDQ : D = Q :=
    adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective
      D Q hDrun hQrun D Q (Or.inl (named_self_genuine D))
        (Or.inr (named_self_genuine Q)) hroot
  have hjState := Proofs.Optimistic.stateBefore_tick_eq_stateBeforeTime
    S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hj
  subst D
  rw [hjState] at hD
  exact hD

/-- A selected named Q2 body of an honest round-`r` action reaches every honest action read and
    opening-vote read, under a finality floor at the height one less than the body's height. -/
theorem selectedQ2_body_at_action_and_openingVote_of_floor
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} (ready : GradeRoundReady S rho r)
    {p : V} (hp : p ∈ rho.honest) {Q : NamedBlock V}
    (hselected : PhaseGrades.nodeQ2 S (actionReadAt S rho p r) r =
      some Q.erase)
    (hQmem : Q ∈ (actionStoreAt S rho p r).st.bodies)
    {stop : Nat} {blocked : Height} {Tprev : Block V}
    (hfloor : FinalityFloorAt S rho blocked stop Tprev)
    (hQheight : (Protocol.derive_named S.E S.cfg Q).h = blocked + 1)
    (hTQ : Block.Preceq Tprev Q.erase)
    (hactionPrefix : strictEventIndex rho (S.a r) ≤ stop)
    {reader : V} (hreader : reader ∈ rho.honest) :
    Q ∈ (actionStoreAt S rho reader r).st.bodies ∧
      Q ∈ (voteDutyRead S rho reader (S.hc.opening_slot r)).st.bodies := by
  let sourceCut := domain S.E S.hc r .g2
  let earlyCut := domain S.E S.hc r .g1
  let voteRead := Protocol.vote_time S.E (S.hc.opening_slot r)
  have hQsource : Q ∈
      (rho.stateBeforeTime S sourceCut p).st.bodies := by
    simpa only [sourceCut] using
      selectedQ2_body_at_capture S adm hp hselected hQmem
  have hQrun : RunBlock S rho Q :=
    actionBody_runBlock_genuine S adm hp hQmem
  have hpostSource : S.E.t_GST ≤ sourceCut := by
    exact ready.1.trans (NamedOutageClosure.early_le_domain S r)
  have hdeadline : max sourceCut S.E.t_GST + S.E.Δ ≤ earlyCut := by
    rw [max_eq_left hpostSource]
    dsimp only [sourceCut, earlyCut]
    change domain S.E S.hc r .g2 + S.E.Δ ≤
      domain S.E S.hc r .g1
    apply le_of_eq
    simp only [domain, Phase.domainOffset]
    ring
  have horder : earlyCut ≤ voteRead := by
    dsimp only [earlyCut, voteRead]
    rw [NamedOutageClosure.domain_g1_eq_opening]
    change Protocol.proposal_time S.E (S.hc.opening_slot r) ≤
      Protocol.vote_time S.E (S.hc.opening_slot r)
    exact (Protocol.proposal_time_lt_vote_time S.E _).le
  have hcut : earlyCut ≤ rho.horizon := by
    have hdomain : domain S.E S.hc r .g1 ≤ domain S.E S.hc r .g0 := by
      simp only [domain, Phase.domainOffset]
      exact Int.add_le_add_left
        (Int.mul_le_mul_of_nonneg_right (by norm_num) S.E.Δ_pos.le) _
    exact (by simpa only [earlyCut] using hdomain.trans ready.2)
  have hvoteAction : voteRead ≤ S.a r := by
    dsimp only [voteRead]
    calc
      Protocol.vote_time S.E (S.hc.opening_slot r) ≤
          Protocol.confirmation_time S.E (S.hc.opening_slot r) :=
        Protocol.vote_time_le_confirmation_time S.E _
      _ = S.a r := opening_confirmation_time_eq_action S r
  have hvotePrefix : strictEventIndex rho voteRead ≤ stop :=
    (strictEventIndex_mono rho hvoteAction).trans hactionPrefix
  have hFvote : Block.Preceq
      (rho.stateBeforeTime S voteRead reader).st.core.F Q.erase := by
    change Block.Preceq
      (NamedRun.stateBeforeTime S rho voteRead reader).st.core.F Q.erase
    rw [congrFun (stateBeforeTime_eq_stateBefore_strictEventIndex
      S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed voteRead) reader]
    exact hfloor.storeF_preceq_sourceHeightBlock hreader hvotePrefix
      hQrun hQheight hTQ
  have hQvote := NamedHealthyHeadReady.healthy_head_body_at_read_after_gst
    S rho adm.toNamedAdmissibleCore p hp reader hreader Q
      sourceCut earlyCut voteRead hQsource hdeadline horder hcut hFvote
  have hQvoteIndex := hQvote.1
  rw [congrFun (stateBeforeTime_eq_stateBefore_strictEventIndex
    S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed voteRead) reader]
    at hQvoteIndex
  have hQaction : Q ∈
      (rho.stateBeforeTime S (S.a r) reader).st.bodies := by
    change Q ∈
      (NamedRun.stateBeforeTime S rho (S.a r) reader).st.bodies
    rw [congrFun (stateBeforeTime_eq_stateBefore_strictEventIndex
      S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed (S.a r)) reader]
    exact NamedBodyRetention.stateBefore_bodies_mono S rho reader
      (strictEventIndex_mono rho hvoteAction) hQvoteIndex
  constructor
  · simp only [actionStoreAt, actionReadAt, NamedActionReads.actionReadAt,
      NamedActionReads.actionReadFrom, NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime, Protocol.NamedStore.setClock]; exact hQaction
  · simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
      Protocol.NamedStore.setClock, voteRead] using hQvote.1

#print axioms selectedQ2_body_at_action_and_openingVote_of_floor

omit [Fintype V] in
private theorem localCovers_of_preceq_genuine
    {A B : Block V} {gv : Protocol.GradeView V}
    {key : Option BlockId} (hAB : Block.Preceq A B)
    (hB : DecoupledConsensusModel.Protocol.localCovers gv key B = true) :
    DecoupledConsensusModel.Protocol.localCovers gv key A = true := by
  unfold DecoupledConsensusModel.Protocol.localCovers at hB ⊢
  unfold Protocol.head_covers at hB ⊢
  cases key with
  | none => exact hB
  | some root =>
      dsimp only at hB ⊢
      cases hfind : Block.find? gv.T root with
      | none =>
          rw [hfind] at hB
          exact absurd hB (by simp)
      | some head =>
          rw [hfind] at hB
          dsimp only at hB ⊢
          exact Block.preceq_trans hAB hB

omit [Fintype V] in
private theorem positive_of_preceq_genuine
    {A B : Block V} (hAB : Block.Preceq A B)
    (gv : Protocol.GradeView V) (F : Block V) (eta r : Round)
    (early late : Time) (v : V)
    (hB : DecoupledConsensusModel.Protocol.positive gv F eta r early late v B = true) :
    DecoupledConsensusModel.Protocol.positive gv F eta r early late v A = true := by
  simp only [DecoupledConsensusModel.Protocol.positive, decide_eq_true_eq] at hB ⊢
  rcases hB with ⟨u, hu, hmax, hcov, hclean, hlate⟩
  refine ⟨u, hu, hmax, localCovers_of_preceq_genuine hAB hcov, hclean, ?_⟩
  intro x hx hlt
  exact localCovers_of_preceq_genuine hAB (hlate x hx hlt)

omit [Fintype V] in
private theorem opposing_of_preceq_genuine
    {A B : Block V} (hAB : Block.Preceq A B)
    (gv : Protocol.GradeView V) (F : Block V) (eta r : Round)
    (early late : Time) (v : V)
    (hA : DecoupledConsensusModel.Protocol.opposing gv F eta r early late v A = true) :
    DecoupledConsensusModel.Protocol.opposing gv F eta r early late v B = true := by
  simp only [DecoupledConsensusModel.Protocol.opposing, decide_eq_true_eq] at hA ⊢
  rcases hA with ⟨x, hx, hmax, hnot⟩ |
      ⟨x, hx, y, hy, hmax, heq, hkey⟩
  · left
    refine ⟨x, hx, hmax, ?_⟩
    intro hcov
    exact hnot (localCovers_of_preceq_genuine hAB hcov)
  · exact Or.inr ⟨x, hx, y, hy, hmax, heq, hkey⟩

private theorem phaseGrade_of_preceq_genuine
    (E : Env V) (hc : Protocol.HealConfig) (gv : Protocol.GradeView V)
    (F : Block V) (r : Round) (phase : Phase) {A B : Block V}
    (hAB : Block.Preceq A B)
    (hB : PhaseGrades.phaseGrade E hc gv F r phase B = true) :
    PhaseGrades.phaseGrade E hc gv F r phase A = true := by
  simp only [PhaseGrades.phaseGrade, DecoupledConsensusModel.Protocol.gradeBool,
    decide_eq_true_eq] at hB ⊢
  have hOpp : (Finset.univ.filter fun v =>
      DecoupledConsensusModel.Protocol.opposing gv F hc.η_SG r
        (early E hc r phase) (late E hc r phase) v A = true) ⊆
      Finset.univ.filter fun v =>
        DecoupledConsensusModel.Protocol.opposing gv F hc.η_SG r
          (early E hc r phase) (late E hc r phase) v B = true := by
    intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ v,
      opposing_of_preceq_genuine hAB gv F hc.η_SG r
        (early E hc r phase) (late E hc r phase) v
        (Finset.mem_filter.mp hv).2⟩
  have hPos : (Finset.univ.filter fun v =>
      DecoupledConsensusModel.Protocol.positive gv F hc.η_SG r
        (early E hc r phase) (late E hc r phase) v B = true) ⊆
      Finset.univ.filter fun v =>
        DecoupledConsensusModel.Protocol.positive gv F hc.η_SG r
          (early E hc r phase) (late E hc r phase) v A = true := by
    intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ v,
      positive_of_preceq_genuine hAB gv F hc.η_SG r
        (early E hc r phase) (late E hc r phase) v
        (Finset.mem_filter.mp hv).2⟩
  exact lt_of_le_of_lt (E.electorate.weightOf_mono hOpp)
    (lt_of_lt_of_le hB (E.electorate.weightOf_mono hPos))

/-- An active prepared voter anchor inherits the G1 grade of the raw root frozen at the reader's G1
    domain time. -/
theorem activeVoterAnchor_storeGrade_g1
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} (hr : 0 < r) (ready : GradeRoundReady S rho r)
    {w : V} (hw : w ∈ rho.honest) {root L : Block V}
    (hframe :
      (DecoupledConsensusModel.Protocol.readFrame
        (voteDutyRead S rho w (S.hc.opening_slot r + 1)).cache
        (voteDutyRead S rho w
          (S.hc.opening_slot r + 1)).st.core.toHealing r).g1 =
        some (some root))
    (hactive : DecoupledConsensusModel.Protocol.activePrefix
      (filteredTree (voteDutyRead S rho w (S.hc.opening_slot r + 1)))
      root = some L) :
    storeGrade S.E S.hc
      (readAt S rho (domain S.E S.hc r .g1) w).st r .g1 L = true := by
  let t := Protocol.vote_time S.E (S.hc.opening_slot r + 1)
  let before := NamedRun.stateBeforeTime S rho t w
  let read := voteDutyRead S rho w (S.hc.opening_slot r + 1)
  have hround : S.hc.round_of (S.E.slotOf t) = r := by
    simpa only [t, Proofs.Optimistic.slotOf_vote_time] using
      Proofs.HealingLemmas.round_of_opening_succ S.hc r
  have hdomainVote : domain S.E S.hc r .g1 < t := by
    dsimp only [t]
    rw [NamedOutageClosure.domain_g1_eq_opening]
    exact (Protocol.proposal_time_mono S.E (Nat.le_succ _)).trans_lt
      (Protocol.proposal_time_lt_vote_time S.E _)
  have hvoteAction : t ≤ S.a r := by
    exact (next_vote_time_lt_action S r).le
  have hg1Horizon : domain S.E S.hc r .g1 ≤ rho.horizon := by
    have hle : domain S.E S.hc r .g1 ≤ domain S.E S.hc r .g0 := by
      simp only [domain, Phase.domainOffset]
      linarith [S.E.Δ_pos]
    exact hle.trans ready.2
  have hbase := FrameCompleted.frame_phase_completed
    S rho adm.toNamedAdmissibleCore w hw r hr .g1 t hdomainVote
      hvoteAction hg1Horizon
  have hbase' :
      (DecoupledConsensusModel.Protocol.readFrame before.cache
        before.st.core.toHealing r).g1 =
        some ((storeRoot S.E S.hc
          (readAt S rho (domain S.E S.hc r .g1) w).st r .g1).map
            (fun X => DecoupledConsensusModel.Protocol.clipGrade X
              before.st.core.F)) := by
    simp only [before, storeRoot, phaseRoot, PhaseGrades.readAt, Protocol.HealingStore.gradeView]; exact hbase
  have hprepared := NamedOutageClosure.frame_phase_prepared_eq
    S rho w r .g1 t hround _ hbase'
  have hreadFrame :
      (DecoupledConsensusModel.Protocol.readFrame read.cache
        read.st.core.toHealing r).g1 =
        some ((storeRoot S.E S.hc
          (readAt S rho (domain S.E S.hc r .g1) w).st r .g1).map
            (fun X => DecoupledConsensusModel.Protocol.clipGrade X
              read.st.core.F)) := by
    simp only [read, before, t, voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]; exact hprepared
  cases hstore : storeRoot S.E S.hc
      (readAt S rho (domain S.E S.hc r .g1) w).st r .g1 with
  | none =>
      simp only [hstore, Option.map_none] at hreadFrame
      rw [hframe] at hreadFrame
      cases hreadFrame
  | some raw =>
      have hrootEq : root =
          DecoupledConsensusModel.Protocol.clipGrade raw read.st.core.F := by
        have hopt : some (some root) = some
            (some (DecoupledConsensusModel.Protocol.clipGrade raw read.st.core.F)) :=
          hframe.symm.trans (by
            simpa only [hstore, Option.map_some] using hreadFrame)
        exact Option.some.inj (Option.some.inj hopt)
      have hLroot : Block.Preceq L root := by
        unfold DecoupledConsensusModel.Protocol.activePrefix at hactive
        exact (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hactive)).2
      have hLraw : Block.Preceq L raw := by
        rw [hrootEq] at hLroot
        exact Block.preceq_trans hLroot
          (NamedOutageClosure.q10_clip_preceq raw read.st.core.F)
      have hrawGrade : phaseGrade S.E S.hc
          (readAt S rho (domain S.E S.hc r .g1) w).st.core.toHealing.gradeView
          (readAt S rho (domain S.E S.hc r .g1) w).st.core.F
          r .g1 raw = true := by
        exact (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hstore)).2
      exact phaseGrade_of_preceq_genuine S.E S.hc _ _ r .g1
        hLraw hrawGrade


/-- The Q2 block selected at `p`'s round-`r` action is G2-graded at `p`'s read at the round-`r` G2
    domain time. -/
theorem selectedQ2_storeGrade_at_g2Domain
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} {p : V} {Q : Block V}
    (hselected : PhaseGrades.nodeQ2 S (actionReadAt S rho p r) r = some Q) :
    PhaseGrades.storeGrade S.E S.hc
      (readAt S rho (domain S.E S.hc r .g2) p).st r .g2 Q = true := by
  let i := strictEventIndex rho (S.a r)
  have hread := stateBeforeTime_eq_stateBefore_strictEventIndex
    S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed (S.a r)
  have hreadp := congrFun hread p
  have hselected0 := hselected
  simp only [PhaseGrades.nodeQ2, PhaseGrades.nodeRead,
    NamedProfile.gradeContract, DecoupledConsensusModel.Protocol.frameContract] at hselected0
  unfold actionReadAt NamedActionReads.actionReadAt at hselected0
  rw [hreadp] at hselected0
  have hselected' : Protocol.grade2_block_with
      (NamedProfile.gradeContract
        (NamedActionReads.actionReadFrom S
          (NamedRun.stateBefore S rho i p) r).cache)
      S.E S.hc
      (NamedActionReads.actionReadFrom S
        (NamedRun.stateBefore S rho i p) r).st.core.toHealing r = some Q := by
    simp only [i]; exact hselected0
  obtain ⟨j, raw, -, hj, hfreeze, hQraw⟩ :=
    contractQ2_capture_at_action_index S rho i p r hselected'
  have hrawGrade : PhaseGrades.phaseGrade S.E S.hc
      (NamedRun.stateBefore S rho j p).st.core.toHealing.gradeView
      (NamedRun.stateBefore S rho j p).st.core.F r .g2 raw = true := by
    simpa only [PhaseGrades.phaseGrade, DecoupledConsensusModel.Protocol.freezeRoot]
      using (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hfreeze)).2
  have hQgrade := phaseGrade_of_preceq_genuine S.E S.hc
    (NamedRun.stateBefore S rho j p).st.core.toHealing.gradeView
    (NamedRun.stateBefore S rho j p).st.core.F r .g2 hQraw hrawGrade
  have hjState := Proofs.Optimistic.stateBefore_tick_eq_stateBeforeTime
    S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hj
  change PhaseGrades.phaseGrade S.E S.hc
    (Run.stateBefore S rho j p).st.core.toHealing.gradeView
    (Run.stateBefore S rho j p).st.core.F r .g2 Q = true at hQgrade
  rw [hjState] at hQgrade
  simpa only [PhaseGrades.storeGrade, PhaseGrades.readAt] using hQgrade

#print axioms selectedQ2_storeGrade_at_g2Domain


/-! ## Named selector split -/

theorem actionFGSource_genuineClear_or_selectedG2_named
    (S : Setup V) (rho : Run V) (v : V) (r : Round)
    {Q B : Block V}
    (hQ : PhaseGrades.nodeQ2 S (actionReadAt S rho v r) r = some Q)
    (hB : actionFGSource S (actionStoreAt S rho v r) = some B) :
    (∃ C : Block V,
      GenuineConfirmationWith
        (NamedProfile.gradeContract
          (NamedActionReads.confirmationReadAt S rho v (S.a r)).cache)
        S.E S.hc (Proofs.Optimistic.confStore S rho v (S.hc.opening_slot r))
          (S.hc.opening_slot r) C ∧
      C = (actionStoreAt S rho v r).st.core.live_confirmed ∧
      Protocol.deepest_clear (some Q)
        (actionStoreAt S rho v r).st.core.live_confirmed
        ((NamedProfile.gradeContract
          (actionStoreAt S rho v r).cache).read S.E S.hc
          (actionStoreAt S rho v r).st.core.toHealing r).clear = some B ∧
      Block.Preceq Q B ∧ Block.Preceq B C) ∨
    B = Q := by
  let ast := actionStoreAt S rho v r
  let gc := NamedProfile.gradeContract ast.cache
  let st := ast.st.core.toHealing
  have hQ' : Protocol.grade2_block_with gc S.E S.hc st r = some Q := by
    rw [Proofs.ModelProperties.grade2_block_with_eq_read_Q2]
    exact hQ
  have hB' : Protocol.fg_source_with gc S.E S.hc st r
      (Protocol.grade2_block_with gc S.E S.hc st r) = some B := by
    have hround : S.hc.round_of st.s = r := by
      show S.hc.round_of ast.st.core.toHealing.s = r
      rw [Proofs.ModelProperties.toHealing_s]
      exact actionStoreAt_round S rho v r
    have h := hB
    change Protocol.fg_source_with
        (NamedProfile.gradeContract ast.cache) S.E S.hc st
        (S.hc.round_of st.s)
        (Protocol.grade2_block_with
          (NamedProfile.gradeContract ast.cache) S.E S.hc st
          (S.hc.round_of st.s)) = some B at h
    rw [hround] at h
    simpa only [gc] using h
  rw [hQ'] at hB'
  cases hwalk : Protocol.deepest_clear (some Q) st.live_confirmed
      (gc.read S.E S.hc st r).clear with
  | none =>
      right
      rw [Proofs.ModelProperties.fg_source_with_some_of_deepest_clear_none gc S.E S.hc st r
        hwalk] at hB'
      exact (Option.some.inj hB').symm
  | some W =>
      rw [Proofs.ModelProperties.fg_source_with_some_of_deepest_clear gc S.E S.hc st r
        hwalk] at hB'
      have hWB : W = B := Option.some.inj hB'
      have hQW : Block.Preceq Q W := Proofs.ModelProperties.deepest_clear_floor_Preceq hwalk
      rcases actionStoreAt_liveConfirmed_genuine_or_fgRoot S rho v r with
        hconfirmed | hroot
      · rcases hconfirmed with ⟨C, hC, hClive⟩
        left
        refine ⟨C, ?_, ?_, ?_, hWB ▸ hQW, ?_⟩
        · simpa only [ast, gc] using hC
        · simpa only [ast] using hClive
        · rw [← hWB]
          have h := hwalk
          rw [show st.live_confirmed = ast.st.core.live_confirmed from
            Proofs.ModelProperties.toHealing_live_confirmed _] at h
          exact h
        · have hWC : Block.Preceq W C := by
            rw [hClive]
            have h : Block.Preceq W ast.st.core.toHealing.live_confirmed :=
              Proofs.ModelProperties.deepest_clear_Preceq hwalk
            rw [Proofs.ModelProperties.toHealing_live_confirmed] at h
            exact h
          exact hWB ▸ hWC
      · rcases hroot with ⟨R, hRroot, hRlive⟩
        have hRast : R = Protocol.get_fg_root ast.st.core.toHealing.toFG := by
          calc
            R = Protocol.get_fg_root
                (Proofs.Optimistic.confStore S rho v (S.hc.opening_slot r)).toHealing.toFG :=
              hRroot
            _ = Protocol.get_fg_root ast.st.core.toHealing.toFG := by
              rw [actionStoreAt_eq_update_confirmation_confStore,
                Proofs.ModelProperties.update_confirmation_with_toHealing_fg_root]
        have hQfiltered : Q ∈ PhaseGrades.filteredTree
            (actionReadAt S rho v r) := by
          exact actionQ2_mem_filteredTree S rho v r hQ
        have hRQ : Block.Preceq R Q := by
          rw [hRast]
          exact Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mp
            (Proofs.Records.preceq_get_fg_root_of_mem_filtered hQfiltered)
        have hWR : Block.Preceq W R := by
          have hRlive' : R = ast.st.core.live_confirmed := by
            simpa only [ast] using hRlive
          have hpre : Block.Preceq W ast.st.core.toHealing.live_confirmed :=
            Proofs.ModelProperties.deepest_clear_Preceq hwalk
          rw [Proofs.ModelProperties.toHealing_live_confirmed, ← hRlive'] at hpre
          exact hpre
        have hWQ : Block.Preceq W Q := Proofs.ModelProperties.Preceq_trans hWR hRQ
        have hWQeq : W = Q := Proofs.ModelProperties.Preceq_antisymm hWQ hQW
        right
        exact hWB ▸ hWQeq

#print axioms actionFGSource_genuineClear_or_selectedG2_named


omit [Fintype V] in
private theorem named_ancestor_body_mem_genuine
    {st : Protocol.NamedStore V} (hpc : NamedStore.NamedParentClosed st)
    {A B : NamedBlock V} (hB : B ∈ st.bodies)
    (hAB : NamedBlock.Preceq A B) : A ∈ st.bodies := by
  revert hB hAB
  induction B with
  | genesis =>
      intro hB hAB
      simp only [NamedBlock.Preceq, NamedBlock.preceq,
        decide_eq_true_eq] at hAB
      exact hAB ▸ hB
  | node parent slot root votes support rows proposer ih =>
      intro hB hAB
      simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hAB
      rcases hAB with rfl | hparent
      · exact hB
      · exact ih (hpc.2 _ hB) hparent

/-- When an honest `p` confirms `C` at round `r`'s opening slot, every named ancestor `B` of `C`
    held at `p`'s action store reaches every honest first-interior vote read. -/
theorem ancestorGenuineConfirmation_body_at_nextVote_of_floor
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} (ready : GradeRoundReady S rho r)
    {p : V} (hp : p ∈ rho.honest) {B : NamedBlock V} {C : Block V}
    {contract : Protocol.GradeContract V}
    (hgenuine : GenuineConfirmationWith contract S.E S.hc
      (Proofs.Optimistic.confStore S rho p (S.hc.opening_slot r))
      (S.hc.opening_slot r) C)
    (hBC : Block.Preceq B.erase C)
    (hBmem : B ∈ (actionStoreAt S rho p r).st.bodies)
    {stop : Nat} {blocked : Height} {Tprev : Block V}
    (hfloor : FinalityFloorAt S rho blocked stop Tprev)
    (hBheight :
      (Protocol.derive_named S.E S.cfg B).h = blocked + 1)
    (hTB : Block.Preceq Tprev B.erase)
    (hactionPrefix : strictEventIndex rho (S.a r) ≤ stop)
    (hactionHor : S.a r ≤ rho.horizon)
    {reader : V} (hreader : reader ∈ rho.honest) :
    B ∈ (voteDutyRead S rho reader
      (S.hc.opening_slot r + 1)).st.bodies := by
  let s := S.hc.opening_slot r
  let support := Protocol.support_cutoff S.E s
  let view := Protocol.view_freeze S.E s
  let vote := Protocol.vote_time S.E (s + 1)
  have hBscope : NamedRun.blockInRun S rho B :=
    actionBody_runBlock_genuine S adm hp hBmem
  have hvoteAction : vote ≤ S.a r := by
    dsimp only [vote, s]
    exact (next_vote_time_lt_action S r).le
  have hvotePrefix : strictEventIndex rho vote ≤ stop :=
    (strictEventIndex_mono rho hvoteAction).trans hactionPrefix
  have hFvote : Block.Preceq
      (NamedRun.stateBeforeTime S rho vote reader).st.core.F B.erase := by
    rw [congrFun (stateBeforeTime_eq_stateBefore_strictEventIndex
      S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed vote) reader]
    exact hfloor.storeF_preceq_sourceHeightBlock hreader hvotePrefix
      hBscope hBheight hTB
  have hordinary : GenuineConfirmation (contract := contract) S.E S.hc
      (Proofs.Optimistic.confStore S rho p s) s C :=
    ⟨hgenuine.selected, hgenuine.genuine⟩
  have hN := confNumerator S.E (Proofs.Optimistic.confStore S rho p s) s
  have hpositive : 0 <
      (Protocol.goldfishSupporters S.E (Proofs.Optimistic.confStore S rho p s).T
        (confVotes S.E (Proofs.Optimistic.confStore S rho p s) s)
        (confVotes S.E (Proofs.Optimistic.confStore S rho p s) s) s C).card := by
    have heligible := hordinary.eligible
    rw [hN.score_eq_supporters] at heligible
    by_contra hnot
    have hzero :
        (Protocol.goldfishSupporters S.E (Proofs.Optimistic.confStore S rho p s).T
          (confVotes S.E (Proofs.Optimistic.confStore S rho p s) s)
          (confVotes S.E (Proofs.Optimistic.confStore S rho p s) s) s C).card = 0 :=
      Nat.eq_zero_of_not_pos hnot
    rw [hzero] at heligible
    simp at heligible
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hpositive
  rw [mem_supporters_iff] at hu
  obtain ⟨-, u, huBy, -, htargets⟩ := hu
  rw [Protocol.votes_by, Finset.mem_filter] at huBy
  obtain ⟨head, hfind, hChead⟩ := targets_under_iff.mp htargets
  by_cases hgen : head = Block.genesis
  · subst head
    have hCgen : C = Block.genesis :=
      Block.preceq_antisymm hChead.2 (Protocol.preceq_genesis C)
    subst C
    have hBgen : B.erase = Block.genesis :=
      Block.preceq_antisymm hBC (Protocol.preceq_genesis B.erase)
    have hBeq : B = NamedBlock.genesis := by
      cases B <;> simp_all [NamedBlock.erase]
    subst B
    exact (Proofs.NamedRuntime.stateBeforeTime_invariants
      S rho vote reader).1.1.1.2.2.1.1
  · have hheadSource : head ∈ (Proofs.Optimistic.confStore S rho p s).T :=
      Proofs.HealingLemmas.find?_mem hfind
    have hearly : u ∈ confEarly S.E (Proofs.Optimistic.confStore S rho p s) s :=
      (Finset.mem_filter.mp huBy.1).1
    have hresolved : stampedBefore
        (Proofs.Optimistic.confStore S rho p s).tau support u = true := by
      rw [confEarly, beforeCutoff, Finset.mem_filter] at hearly
      exact hearly.2
    have hheadStamp : stampedBefore
        (Proofs.Optimistic.confStore S rho p s).timestamp_block support head = true :=
      HonestWeightMajority.stampedBefore_block_of_resolution hfind hresolved
    have hheadPre : head ∈
        (NamedRun.stateBeforeTime S rho
          (Protocol.confirmation_time S.E s) p).st.core.T := by
      simpa only [Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore,
        Run.storeBeforeTime] using hheadSource
    obtain ⟨Hn, hHnPre, hHnErase⟩ :=
      Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime
        S rho (Protocol.confirmation_time S.E s) p hheadPre
    have hstampPre : stampedBefore
        (NamedRun.stateBeforeTime S rho
          (Protocol.confirmation_time S.E s) p).st.core.timestamp_block
        support Hn.erase = true := by
      simpa only [Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore,
        Run.storeBeforeTime, hHnErase] using hheadStamp
    have hsupportPublic : PublicTime S support := by
      dsimp only [support]
      exact Protocol.publicTime_support_cutoff S s
    have hHsupport : Hn ∈
        (NamedRun.stateBeforeTime S rho support p).st.bodies :=
      NamedPublicCutBody.body_mem_stateBeforeTime_of_public_stampedBefore
        S rho adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
          hsupportPublic hHnPre hstampPre
    have hpostSupport : S.E.t_GST ≤ support := by
      apply ready.1.trans
      dsimp only [support, s]
      unfold early opening Phase.earlyOffset Protocol.proposal_time
        Protocol.support_cutoff Env.t Protocol.HealConfig.opening_slot
        slotStart
      linarith [S.E.Δ_pos]
    have hdeadline : max support S.E.t_GST + S.E.Δ ≤ view := by
      rw [max_eq_left hpostSupport]
      dsimp only [support, view]
      exact le_of_eq
        (Protocol.support_cutoff_add_delta_eq_view_freeze S.E s)
    have hviewVote : view ≤ vote := by
      dsimp only [view, vote]
      exact (Protocol.view_freeze_lt_vote_time_succ S.E s).le
    have hviewHorizon : view ≤ rho.horizon :=
      hviewVote.trans (hvoteAction.trans hactionHor)
    have hFhead : Block.Preceq
        (NamedRun.stateBeforeTime S rho vote reader).st.core.F Hn.erase :=
      Block.preceq_trans hFvote (by
        rw [hHnErase]
        exact Block.preceq_trans hBC hChead.2)
    obtain ⟨hHvote, -, -⟩ :=
      NamedHealthyHeadReady.healthy_head_body_at_read_after_gst
        S rho adm.toNamedAdmissibleCore p hp reader hreader Hn
          support view vote hHsupport hdeadline hviewVote
          hviewHorizon hFhead
    have hHscope : NamedRun.blockInRun S rho Hn := by
      obtain ⟨n, hn, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix
        S rho adm.toNamedAdmissibleCore.sorted vote
      rw [hn] at hHvote
      exact Proofs.Bridges.runBlock_of_stateBefore_mem S hreader hHvote
    have hBH : NamedBlock.Preceq B Hn :=
      Protocol.namedPreceq_of_runBlock_erase_preceq
        adm hBscope hHscope (by
          rw [hHnErase]
          exact Block.preceq_trans hBC hChead.2)
    have hpc := (Proofs.NamedRuntime.stateBeforeTime_invariants
      S rho vote reader).1.1.1.2.2.1
    have hBvote := named_ancestor_body_mem_genuine hpc hHvote hBH
    simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, Protocol.NamedStore.setClock,
      vote] using hBvote

#print axioms ancestorGenuineConfirmation_body_at_nextVote_of_floor


private theorem voteDuty_hMax_le_of_noHeightProgress_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {H : Height} {through : Time} {w : V} (hw : w ∈ rho.honest)
    {s : Slot}
    (hno : ¬ HonestHeightFilterProgressAboveThrough S rho H through)
    (hread : Protocol.vote_time S.E s ≤ through) :
    (voteDutyRead S rho w s).st.core.h_max ≤ H + 1 := by
  let read := Protocol.vote_time S.E s
  have hstrict : rho.storeBeforeTime S w read =
      rho.storeAt S w (read - 1) :=
    storeBeforeTime_eq_storeAt_sub_one_recovery S rho w read
  have hlocal : (rho.storeBeforeTime S w read).core.h_max ≤
      (rho.storeAt S w read).core.h_max := by
    rw [hstrict]
    exact stateAt_h_max_mono S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed w
      (sub_le_self read (by norm_num : (0 : Time) ≤ 1))
  by_contra hnot
  have hgt : H + 1 < (voteDutyRead S rho w s).st.core.h_max :=
    Nat.lt_of_not_ge hnot
  have hgtAt : H + 1 < (rho.storeAt S w read).core.h_max := by
    apply lt_of_lt_of_le hgt
    simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, Protocol.NamedStore.setClock, read, Run.storeBeforeTime]
      using hlocal
  apply hno
  exact ⟨w, hw, read, hread, Nat.succ_le_iff.mpr hgtAt⟩

/-- In the case without height progress, the named ancestor `B` of the confirmed block is a
    candidate in the prepared next-vote read. -/
private theorem ancestorGenuineConfirmation_candidate_at_nextVote
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} (ready : GradeRoundReady S rho r)
    (hactionHor : S.a r ≤ rho.horizon)
    {p : V} (hp : p ∈ rho.honest)
    {B : NamedBlock V} {C : Block V}
    {contract : Protocol.GradeContract V}
    (hgenuine : GenuineConfirmationWith contract S.E S.hc
      (Proofs.Optimistic.confStore S rho p (S.hc.opening_slot r))
      (S.hc.opening_slot r) C)
    (hBC : Block.Preceq B.erase C)
    (hBheight : (Protocol.derive_named S.E S.cfg B).h = H + 1)
    {through : Time}
    (hno : ¬ HonestHeightFilterProgressAboveThrough S rho (H + 1) through)
    (hvoteThrough :
      Protocol.vote_time S.E (S.hc.opening_slot r + 1) ≤ through)
    {w : V} (hw : w ∈ rho.honest)
    (hBbody : B ∈
      (voteDutyRead S rho w (S.hc.opening_slot r + 1)).st.bodies)
    (hBfiltered : B.erase ∈
      filteredTree (voteDutyRead S rho w (S.hc.opening_slot r + 1))) :
    B.erase ∈ Proofs.Optimistic.voter_candidate_tree S.E
      (voteDutyRead S rho w
        (S.hc.opening_slot r + 1)).st.core.toHealing := by
  let s := S.hc.opening_slot r
  let read := voteDutyRead S rho w (s + 1)
  let duty := Proofs.Optimistic.voteDutyStore S rho w (s + 1)
  have hrootC : Block.Preceq
      (Protocol.get_fg_root duty.toHealing.toFG) C := by
    apply Block.preceq_trans _ hBC
    have hrootB := Proofs.Records.preceq_get_fg_root_of_mem_filtered hBfiltered
    simpa only [duty, read, s, filteredTree, voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock, Proofs.Optimistic.voteDutyStore,
      Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore, Protocol.Store.toHealing, Run.storeBeforeTime] using hrootB
  have hpost : S.E.t_GST ≤ Protocol.proposal_time S.E s := by
    apply ready.1.trans
    simp only [s, early, opening, Phase.earlyOffset,
      Protocol.proposal_time]
    linarith [S.E.Δ_pos]
  have hsourceHor : Protocol.confirmation_time S.E s ≤ rho.horizon := by
    simpa only [s, opening_confirmation_time_eq_action S r] using hactionHor
  have hCprocessed : C ∈ Protocol.voter_processed_block_tree S.E
      duty.toHealing.toFG.toSG.toGoldfishStore duty.toHealing.s := by
    have hg : GenuineConfirmation (contract := contract) S.E S.hc
        (Proofs.Optimistic.confStore S rho p s) s C :=
      ⟨hgenuine.selected, hgenuine.genuine⟩
    exact Protocol.voterProcessedTarget_of_genuineConfirmation_after_gst
      S adm hp hw hpost hsourceHor hg hrootC
  have hBprocessedDuty : B.erase ∈ Protocol.voter_processed_block_tree S.E
      duty.toHealing.toFG.toSG.toGoldfishStore duty.toHealing.s :=
    WeakGoldfish.ancestorProcessed_of_voterProcessed
      S adm.toNamedAdmissibleCore hw hCprocessed B.erase hBC
  have hBprocessed : B.erase ∈ Protocol.voter_processed_block_tree S.E
      read.st.core.toHealing.toFG.toSG.toGoldfishStore read.st.core.toHealing.s := by
    simpa only [duty, read, s, voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock, Proofs.Optimistic.voteDutyStore,
      Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore, Protocol.Store.toHealing, Run.storeBeforeTime] using hBprocessedDuty
  have hBpre : B ∈ (NamedRun.stateBeforeTime S rho
      (Protocol.vote_time S.E (s + 1)) w).st.bodies := by
    simpa only [read, s, voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, Protocol.NamedStore.setClock] using hBbody
  have hview := Proofs.NamedStoreBridge.derivedView_stateBeforeTime S rho
    (Protocol.vote_time S.E (s + 1)) w B hBpre
  have hstored : (read.st.core.σ B.erase).h = H + 1 := by
    have hheight := congrArg (fun st => st.h) hview
    calc
      (read.st.core.σ B.erase).h =
          (Protocol.derive_named S.E S.cfg B).h := by
        simpa only [read, voteDutyRead,
          NamedActionReads.confirmationReadAt,
          NamedActionReads.confirmationReadFrom,
          Protocol.NamedStore.setClock] using hheight
      _ = H + 1 := hBheight
  have hmax : read.st.core.h_max ≤ H + 2 := by
    simpa only [read, s] using
      (voteDuty_hMax_le_of_noHeightProgress_named
        S adm hw hno hvoteThrough)
  apply Protocol.voterCandidate_of_processed_self_and_filtered
    S.E read.st.core.toHealing hBprocessed
  · change read.st.core.h_max - 1 ≤ (read.st.core.σ B.erase).h
    rw [hstored]
    exact Nat.sub_le_iff_le_add.mpr (by simpa [Nat.add_assoc] using hmax)
  · exact hBfiltered

/-- When `B` passes the eligibility test at slot `s` and `w` adopts `B` at the next vote, `B`
    precedes `w`'s vote head at slot `s + 1`. -/
private theorem preceq_voterHeadAt_of_namedNextVoteAdoption
    (S : Setup V) {rho : Run V} {source : Protocol.Store V}
    {s : Slot} {B : Block V} {w : V}
    (heligible : Protocol.voters_count S.E (confLate S.E source s) s <
      2 * Protocol.goldfish_score S.E source.T
        (confVotes S.E source s) (confVotes S.E source s) s B)
    (hadopt : NamedNextVoteAdoption S rho source s B w) :
    Block.Preceq B (voterHeadAt S rho w (s + 1)) := by
  let read := voteDutyRead S rho w (s + 1)
  let st := read.st.core
  let tree := voterCandidateTreeAt S rho w (s + 1)
  let votes := Protocol.voter_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s
  let support := Protocol.voter_support_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s
  have hslot : st.s = s + 1 := by
    simpa only [st, read] using Proofs.Optimistic.voteDutyRead_slot S rho w (s + 1)
  have hprev : st.s - 1 = s := by
    rw [hslot]
    simp
  change Block.Preceq B
    (Protocol.get_head_in_tree_with_layer
      (NamedProfile.gradeContract read.cache) S.E S.hc st.toHealing
      tree votes support (st.s - 1))
  rw [Proofs.Optimistic.get_head_in_tree_split_with]
  rw [hprev]
  simp only [Protocol.Store.toHealing, read, st, NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock, Protocol.Store.sg_pool]; exact
    (Protocol.goldfish_fork_choice_captures_of_confirmation
      S.E st.σ st.h_max source.T st.T tree st.s
      (confEarly S.E source s) (confLate S.E source s)
      (confVotes S.E source s) votes support s
      (confNumerator S.E source s) hadopt.transport heligible
        hadopt.support_subset hadopt.anchor hadopt.path)

private theorem ancestorConfirmation_eligible_with_of_preceq
    (E : Env V) (hc : Protocol.HealConfig) (source : Protocol.Store V)
    (s : Slot) {T C : Block V} {contract : Protocol.GradeContract V}
    (hTC : Block.Preceq T C)
    (hC : GenuineConfirmationWith contract E hc source s C) :
    Protocol.voters_count E (confLate E source s) s <
      2 * Protocol.goldfish_score E source.T
        (confVotes E source s) (confVotes E source s) s T := by
  have hN := confNumerator E source s
  have hsupport := supporters_mono E source.T
    (confVotes E source s) (confVotes E source s) s hTC
  have hcard := Finset.card_le_card hsupport
  have hCg : GenuineConfirmation E hc source s C (contract := contract) :=
    ⟨hC.selected, hC.genuine⟩
  have hCeligible := hCg.eligible
  rw [hN.score_eq_supporters] at hCeligible ⊢
  exact lt_of_lt_of_le hCeligible (Nat.mul_le_mul_left 2 hcard)


/-- When an honest `p` confirms `C` at round `r`'s opening slot and
    `VoterAnchorSourceClearInputsMain` holds for a named ancestor `B` of `C` at height `H + 1`,
    either the height progresses past `H + 1` or the honest next votes are descendants of `B`. -/
theorem genuineClear_nextVoteCone_or_heightProgressThrough_of_mainInputs
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} (ready : GradeRoundReady S rho r)
    {p : V} (hp : p ∈ rho.honest) {B : NamedBlock V} {C : Block V}
    {contract : Protocol.GradeContract V}
    (hgenuine : GenuineConfirmationWith contract S.E S.hc
      (Proofs.Optimistic.confStore S rho p (S.hc.opening_slot r))
      (S.hc.opening_slot r) C)
    (hBC : Block.Preceq B.erase C)
    (hBmem : B ∈ (actionStoreAt S rho p r).st.bodies)
    {H : Height}
    (hBheight : (Protocol.derive_named S.E S.cfg B).h = H + 1)
    (hactionHor : S.a r ≤ rho.horizon)
    (hmain : VoterAnchorSourceClearInputsMain S rho r p B.erase)
    {through : Time}
    (hvoteThrough :
      Protocol.vote_time S.E (S.hc.opening_slot r + 1) ≤ through) :
    HonestHeightFilterProgressAboveThrough S rho (H + 1) through ∨
      ((∀ w ∈ rho.honest,
        Block.Preceq B.erase
          (voterHeadAt S rho w (S.hc.opening_slot r + 1))) ∧
        NamedHonestVotesCone S rho (S.hc.opening_slot r + 1)
          (fun X => Block.Preceq B.erase X)) := by
  let s := S.hc.opening_slot r
  have hpost : S.E.t_GST ≤ Protocol.proposal_time S.E s := by
    apply ready.1.trans
    simp only [s, early, opening, Phase.earlyOffset,
      Protocol.proposal_time]
    linarith [S.E.Δ_pos]
  have hsourceHor : Protocol.confirmation_time S.E s ≤ rho.horizon := by
    simpa only [s, opening_confirmation_time_eq_action S r] using hactionHor
  have hvoteHor : Protocol.vote_time S.E (s + 1) ≤ rho.horizon :=
    (next_vote_time_lt_action S r).le.trans hactionHor
  by_cases hprogress :
      HonestHeightFilterProgressAboveThrough S rho (H + 1) through
  · exact Or.inl hprogress
  · right
    have hfiltered : ∀ w ∈ rho.honest, B.erase ∈
        filteredTree (voteDutyRead S rho w (s + 1)) := by
      intro w hw
      simpa only [s] using hmain.nextTarget w hw
    have hbody : ∀ w ∈ rho.honest, B ∈
        (voteDutyRead S rho w (s + 1)).st.bodies := by
      intro w hw
      exact actionBody_at_voteDuty_of_filtered S adm hp hBmem hw
        (hfiltered w hw)
    have hheads : ∀ w ∈ rho.honest,
        Block.Preceq B.erase (voterHeadAt S rho w (s + 1)) := by
      intro w hw
      have adopt (hanchor : Block.Preceq
          (voterAnchorAt S rho w (s + 1)) B.erase) :
          Block.Preceq B.erase (voterHeadAt S rho w (s + 1)) := by
        have hcandidate := ancestorGenuineConfirmation_candidate_at_nextVote
          S adm ready hactionHor hp hgenuine hBC hBheight hprogress
            hvoteThrough hw (hbody w hw) (hfiltered w hw)
        have hanchor' : Block.Preceq
            (Protocol.get_sg_root_with
              (NamedProfile.gradeContract
                (voteDutyRead S rho w (s + 1)).cache)
              S.E S.hc
              (voteDutyRead S rho w (s + 1)).st.core.toHealing
              (S.hc.round_of
                (voteDutyRead S rho w (s + 1)).st.core.s)) B.erase := by
          exact hanchor
        have hadopt := nextVoteAdoption_of_frozenCandidateAtRead
          S adm hp hpost hsourceHor hw hcandidate hanchor'
        exact preceq_voterHeadAt_of_namedNextVoteAdoption S
          (ancestorConfirmation_eligible_with_of_preceq S.E S.hc
            (Proofs.Optimistic.confStore S rho p s) s hBC hgenuine) hadopt
      have hcompat := hmain.anchorCompatible w hw
        (voterAnchorAt S rho w (s + 1)) (by rfl)
      simp only [Block.compatible, Bool.or_eq_true] at hcompat
      rcases hcompat with hanchor | hsourceAnchor
      · exact adopt hanchor
      · exact Block.preceq_trans hsourceAnchor
          (voterAnchorAt_preceq_voterHeadAt S rho w (s + 1))
    refine ⟨hheads, ?_⟩
    intro w hw hcommittee
    obtain ⟨X, hXhead, hXrun, hXemit⟩ := named_voter_head_emits
      S adm hw (s := s + 1) (Nat.succ_pos s) hcommittee hvoteHor
    exact ⟨X, by rw [hXhead]; exact hheads w hw, hXrun, hXemit⟩

#print axioms genuineClear_nextVoteCone_or_heightProgressThrough_of_mainInputs


#print axioms selectedQ2_body_at_capture
#print axioms activeVoterAnchor_storeGrade_g1

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
