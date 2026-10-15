module
public import Proofs.Vocabulary.Generic.PrefixFGSelectorWitness
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedCeilingStep
public import Proofs.Vocabulary.Protocol.Grades.RelativeOneChain
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.GradeDelivery
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.ProposalVoteDuty
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.HeightProgressSeedRegime
import Proofs.Vocabulary.Protocol.Schedule.PostHealingReuse
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star

@[expose] public section

/-!
# The prepared voter anchor and the source round

The named body of an active prepared voter anchor reaches the source round's reads, and
`VoterAnchorSourceQ2Inputs` holds over the named height-regime frame.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Internal.PhaseGrades
open Internal.NamedRecoveryRead Protocol
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem actionBody_runBlock_k6
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) {r : Round} {D : NamedBlock V}
    (hD : D ∈ (actionStoreAt S rho v r).st.bodies) :
    RunBlock S rho D := by
  have hDpre : D ∈ (rho.stateBeforeTime S (S.a r) v).st.bodies := by
    simp only [actionStoreAt, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime]; exact hD
  obtain ⟨i, hi, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix
    S rho adm.toNamedScheduleWellFormed.sorted (S.a r)
  have hDi : D ∈ (rho.stateBefore S i v).st.bodies := by
    change D ∈ (NamedRun.stateBefore S rho i v).st.bodies
    rw [← hi]
    exact hDpre
  exact Proofs.Bridges.runBlock_of_stateBefore_mem S hv hDi


/-- The finalized block of an honest `p`'s round-`r` G0 domain read precedes every block in an
    honest `w`'s filtered tree at round `r`'s first interior vote. -/
theorem sourceG0Finalized_preceq_firstInteriorActive
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hbelow : BelowOneThird S rho.honest)
    {r : Round} (ready : GradeRoundReady S rho r)
    (hactionHor : S.a r ≤ rho.horizon)
    {p w : V} (hp : p ∈ rho.honest) (hw : w ∈ rho.honest)
    {L : Block V}
    (hL : L ∈ filteredTree
      (voteDutyRead S rho w (S.hc.opening_slot r + 1))) :
    Block.Preceq
      (readAt S rho (domain S.E S.hc r .g0) p).st.core.F L := by
  let source := domain S.E S.hc r .g0
  let out := source + S.E.Δ
  let vote := Protocol.vote_time S.E (S.hc.opening_slot r + 1)
  have hpost : S.E.t_GST ≤ source := by
    apply ready.1.trans
    dsimp only [source]
    simp only [early, domain, Phase.earlyOffset, Phase.domainOffset]
    linarith [S.E.Δ_pos]
  have houtVote : out ≤ vote := by
    dsimp only [out, source, vote, domain, opening, Phase.domainOffset,
      Protocol.vote_time, Protocol.proposal_time, Env.t, slotStart,
      Protocol.HealConfig.opening_slot]
    push_cast
    nlinarith [S.E.Δ_pos, S.hc.R_ge_three]
  have hvoteHor : vote ≤ rho.horizon := by
    dsimp only [vote]
    exact (next_vote_time_lt_action S r).le.trans hactionHor
  have hsb : SlashableBound S rho :=
    slashableBound_of_admissible_belowOneThird S adm hbelow
  have hrelay : Block.Preceq
      (NamedRun.stateBeforeTime S rho source p).st.core.F
      (NamedRun.stateBeforeTime S rho out w).st.core.F :=
    finalized_preceq_of_evidence_delivered
      S adm hsb hp hw hpost rfl (houtVote.trans hvoteHor)
  have hmono : Block.Preceq
      (NamedRun.stateBeforeTime S rho out w).st.core.F
      (NamedRun.stateBeforeTime S rho vote w).st.core.F := by
    rw [NamedOutageClosure.strict_read_eq_index S rho
        adm.toNamedScheduleWellFormed.sorted out,
      NamedOutageClosure.strict_read_eq_index S rho
        adm.toNamedScheduleWellFormed.sorted vote]
    exact Proofs.NamedRuntime.stateBefore_F_mono S rho w
      (NamedOutageClosure.strict_lengths_mono rho houtVote)
  have hvoteL : Block.Preceq
      (NamedRun.stateBeforeTime S rho vote w).st.core.F L := by
    apply GradeDeliveryRun.finalized_preceq_of_mem_filtered_at_read S rho
    simp only [filteredTree, voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      vote]; exact hL
  exact Block.preceq_trans hrelay (Block.preceq_trans hmono hvoteL)

#print axioms sourceG0Finalized_preceq_firstInteriorActive

/-- An active prepared voter anchor `L` has a named body held at the reader's round-`r` G1 domain
    read. -/
theorem activeVoterAnchor_namedBody_at_g1Domain
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
    ∃ Ln : NamedBlock V, Ln.erase = L ∧
      Ln ∈ (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc r .g1) w).st.bodies ∧ RunBlock S rho Ln := by
  let t := Protocol.vote_time S.E (S.hc.opening_slot r + 1)
  let before := NamedRun.stateBeforeTime S rho t w
  let read := voteDutyRead S rho w (S.hc.opening_slot r + 1)
  let domainRead := readAt S rho (domain S.E S.hc r .g1) w
  have hround : S.hc.round_of (S.E.slotOf t) = r := by
    simpa only [t, Proofs.Optimistic.slotOf_vote_time] using
      Proofs.HealingLemmas.round_of_opening_succ S.hc r
  have hdomainVote : domain S.E S.hc r .g1 < t := by
    dsimp only [t]
    rw [NamedOutageClosure.domain_g1_eq_opening]
    exact (Protocol.proposal_time_mono S.E (Nat.le_succ _)).trans_lt
      (Protocol.proposal_time_lt_vote_time S.E _)
  have hvoteAction : t ≤ S.a r := (next_vote_time_lt_action S r).le
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
        some ((storeRoot S.E S.hc domainRead.st r .g1).map
          (fun X => DecoupledConsensusModel.Protocol.clipGrade X
            before.st.core.F)) := by
    simp only [before, domainRead, storeRoot, phaseRoot, PhaseGrades.readAt]; exact hbase
  have hprepared := NamedOutageClosure.frame_phase_prepared_eq
    S rho w r .g1 t hround _ hbase'
  have hreadFrame :
      (DecoupledConsensusModel.Protocol.readFrame read.cache
        read.st.core.toHealing r).g1 =
        some ((storeRoot S.E S.hc domainRead.st r .g1).map
          (fun X => DecoupledConsensusModel.Protocol.clipGrade X
            read.st.core.F)) := by
    simp only [read, before, t, voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom]; exact hprepared
  cases hstore : storeRoot S.E S.hc domainRead.st r .g1 with
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
      have hrawTree : raw ∈ domainRead.st.core.T :=
        (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hstore)).1
      have hLtree : L ∈ domainRead.st.core.T := by
        have hpc := Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho
          (domain S.E S.hc r .g1) w
        exact Proofs.Records.mem_of_preceq ((parentClosed_iff _).mp hpc).2
          L raw hrawTree hLraw
      obtain ⟨Ln, hLn, hLnErase⟩ :=
        Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime
          S rho (domain S.E S.hc r .g1) w (by
            simpa only [domainRead, PhaseGrades.readAt] using hLtree)
      have hLnRun : RunBlock S rho Ln := by
        obtain ⟨i, hi, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix
          S rho adm.toNamedScheduleWellFormed.sorted
            (domain S.E S.hc r .g1)
        apply Proofs.Bridges.runBlock_of_stateBefore_mem S hw
        change Ln ∈ (NamedRun.stateBefore S rho i w).st.bodies
        rw [← hi]
        exact hLn
      exact ⟨Ln, hLnErase, hLn, hLnRun⟩

#print axioms activeVoterAnchor_namedBody_at_g1Domain

/-- The named body of an active prepared voter anchor is held at an honest `p`'s round-`r` G0 domain
    read and at `p`'s round-`r` action read. -/
theorem activeVoterAnchor_namedBody_at_sourceG0_and_action
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hbelow : BelowOneThird S rho.honest)
    {r : Round} (hr : 0 < r) (ready : GradeRoundReady S rho r)
    (hactionHor : S.a r ≤ rho.horizon)
    {p w : V} (hp : p ∈ rho.honest) (hw : w ∈ rho.honest)
    {root L : Block V}
    (hframe :
      (DecoupledConsensusModel.Protocol.readFrame
        (voteDutyRead S rho w (S.hc.opening_slot r + 1)).cache
        (voteDutyRead S rho w
          (S.hc.opening_slot r + 1)).st.core.toHealing r).g1 =
        some (some root))
    (hactive : DecoupledConsensusModel.Protocol.activePrefix
      (filteredTree (voteDutyRead S rho w (S.hc.opening_slot r + 1)))
      root = some L) :
    ∃ Ln : NamedBlock V, Ln.erase = L ∧
      Ln ∈ (readAt S rho (domain S.E S.hc r .g0) p).st.bodies ∧
      Ln ∈ (actionDutyRead S rho p r).st.bodies ∧ RunBlock S rho Ln := by
  obtain ⟨Ln, hLnErase, hLnG1, hLnRun⟩ :=
    activeVoterAnchor_namedBody_at_g1Domain
      S adm hr ready hw hframe hactive
  have hLvote : L ∈ filteredTree
      (voteDutyRead S rho w (S.hc.opening_slot r + 1)) := by
    unfold DecoupledConsensusModel.Protocol.activePrefix at hactive
    exact (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hactive)).1
  have htargetF : Block.Preceq
      (readAt S rho (domain S.E S.hc r .g0) p).st.core.F Ln.erase := by
    rw [hLnErase]
    exact sourceG0Finalized_preceq_firstInteriorActive
      S adm hbelow ready hactionHor hp hw hLvote
  have hpost : S.E.t_GST ≤ domain S.E S.hc r .g1 := by
    apply ready.1.trans
    simp only [early, domain, Phase.earlyOffset, Phase.domainOffset]
    linarith [S.E.Δ_pos]
  have hdeadline :
      max (domain S.E S.hc r .g1) S.E.t_GST + S.E.Δ ≤
        domain S.E S.hc r .g0 := by
    rw [max_eq_left hpost]
    apply le_of_eq
    simp only [domain, Phase.domainOffset]
    ring
  obtain ⟨hLnG0, -, -⟩ :=
    NamedHealthyHeadReady.healthy_head_body_at_read_after_gst
      S rho adm.toNamedAdmissibleCore w hw p hp Ln
        (domain S.E S.hc r .g1) (domain S.E S.hc r .g0)
        (domain S.E S.hc r .g0) hLnG1 hdeadline (le_refl _)
        ready.2 htargetF
  have hdomainAction : domain S.E S.hc r .g0 ≤ S.a r :=
    FrameForward.domain_le_a S r .g0
  have heqG0 := congrFun (stateBeforeTime_eq_stateBefore_strictEventIndex
    S adm.toNamedScheduleWellFormed (domain S.E S.hc r .g0)) p
  have heqAction := congrFun (stateBeforeTime_eq_stateBefore_strictEventIndex
    S adm.toNamedScheduleWellFormed (S.a r)) p
  have hLnG0Index := hLnG0
  rw [heqG0] at hLnG0Index
  have hLnAction : Ln ∈
      (NamedRun.stateBeforeTime S rho (S.a r) p).st.bodies := by
    rw [heqAction]
    exact NamedBodyRetention.stateBefore_bodies_mono S rho p
      (strictEventIndex_mono rho hdomainAction) hLnG0Index
  refine ⟨Ln, hLnErase, ?_, ?_, hLnRun⟩
  · simpa only [PhaseGrades.readAt] using hLnG0
  · simp only [actionDutyRead, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime]; exact hLnAction

#print axioms activeVoterAnchor_namedBody_at_sourceG0_and_action


/-- Over the named height-regime frame, `VoterAnchorSourceQ2Inputs` holds for a selected Q2 block of
    height `H + 1` that is the FG source of an honest `p`'s round-`r` action. -/
theorem voterAnchorSourceQ2Inputs_of_namedHeightRegimeFrame_at_source
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} (ready : GradeRoundReady S rho r)
    {stop : Nat} {H : Height} {Prev : NamedBlock V} {c0 : Round}
    (hframe : NamedHeightRegimeFrame S rho H stop Prev c0)
    (hactionPrefix : strictEventIndex rho (S.a r) ≤ stop)
    (hfrontier : honestHMaxBeforeIndex S rho stop < H + 2)
    (hactionHor : S.a r ≤ rho.horizon)
    {p : V} (hp : p ∈ rho.honest) (Q : NamedBlock V)
    (hselected : nodeQ2 S (actionReadAt S rho p r) r = some Q.erase)
    (hsource : actionFGSource S (actionStoreAt S rho p r) = some Q.erase)
    (hQmem : Q ∈ (actionStoreAt S rho p r).st.bodies)
    (hQheight : (Protocol.derive_named S.E S.cfg Q).h = H + 1) :
    VoterAnchorSourceQ2Inputs S rho r p Q.erase := by
  have hPrevQ : NamedBlock.Preceq Prev Q :=
    hframe.sourceAbove p hp r hactionPrefix hactionHor Q hQmem
      hsource hQheight
  have hPrevQErase : Block.Preceq Prev.erase Q.erase :=
    Proofs.NamedWire.erase_preceq hPrevQ
  have hQrun : RunBlock S rho Q := actionBody_runBlock_k6 S adm hp hQmem
  have hfloor : FinalityFloorAt S rho H stop Prev.erase := by
    intro v hv n hn X hXrun hXheight hPrevX
    exact hframe.floor v hv n hn X hXrun hXheight
      (Protocol.namedPreceq_of_runBlock_erase_preceq
        adm hframe.prevRun hXrun hPrevX)
  have hQsource : Q ∈ (NamedRun.stateBeforeTime S rho
      (domain S.E S.hc r .g2) p).st.bodies :=
    selectedQ2_body_at_capture S adm hp hselected hQmem
  refine ⟨?_, ?_⟩
  · intro w hw
    have hdomainAction : domain S.E S.hc r .g1 ≤ S.a r := by
      rw [NamedOutageClosure.domain_g1_eq_opening]
      exact (Protocol.proposal_time_lt_vote_time S.E _).le.trans
        ((Protocol.vote_time_le_confirmation_time S.E _).trans
          (by rw [opening_confirmation_time_eq_action]))
    have hdomainPrefix :
        strictEventIndex rho (domain S.E S.hc r .g1) ≤ stop :=
      (strictEventIndex_mono rho hdomainAction).trans hactionPrefix
    have htargetFQ : Block.Preceq
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc r .g1) w).st.core.F Q.erase := by
      rw [congrFun (stateBeforeTime_eq_stateBefore_strictEventIndex
        S adm.toNamedScheduleWellFormed (domain S.E S.hc r .g1)) w]
      exact hframe.floor w hw _ hdomainPrefix Q hQrun
        (by rw [hQheight]; exact Nat.le_succ H) hPrevQ
    have hpost : S.E.t_GST ≤ domain S.E S.hc r .g2 :=
      ready.1.trans (NamedOutageClosure.early_le_domain S r)
    have hdeadline :
        max (domain S.E S.hc r .g2) S.E.t_GST + S.E.Δ ≤
          domain S.E S.hc r .g1 := by
      rw [max_eq_left hpost]
      apply le_of_eq
      simp only [domain, Phase.domainOffset]
      ring
    have hg1Hor : domain S.E S.hc r .g1 ≤ rho.horizon := by
      have hle : domain S.E S.hc r .g1 ≤ domain S.E S.hc r .g0 := by
        simp only [domain, Phase.domainOffset]
        linarith [S.E.Δ_pos]
      exact hle.trans ready.2
    obtain ⟨hbody, -, -⟩ :=
      NamedHealthyHeadReady.healthy_head_body_at_read_after_gst
        S rho adm.toNamedAdmissibleCore p hp w hw Q
          (domain S.E S.hc r .g2) (domain S.E S.hc r .g1)
          (domain S.E S.hc r .g1) hQsource hdeadline (le_refl _)
          hg1Hor htargetFQ
    have heq := congrFun (stateBeforeTime_eq_stateBefore_strictEventIndex
      S adm.toNamedScheduleWellFormed (domain S.E S.hc r .g1)) w
    have hbody' := hbody
    rw [heq] at hbody'
    have hfiltered := hframe.fgRoot_preceq_and_filteredMem
      adm hfrontier hw hdomainPrefix hbody' hQheight hPrevQ
    rw [← heq] at hfiltered
    simpa only [filteredTree, PhaseGrades.readAt] using hfiltered.2
  · intro w hw
    let vote := Protocol.vote_time S.E (S.hc.opening_slot r)
    have hbodies := selectedQ2_body_at_action_and_openingVote_of_floor
      S adm ready hp hselected hQmem hfloor hQheight hPrevQErase
        hactionPrefix hw
    have hvoteAction : vote ≤ S.a r := by
      dsimp only [vote]
      exact (Protocol.vote_time_le_confirmation_time S.E _).trans
        (by rw [opening_confirmation_time_eq_action])
    have hvotePrefix : strictEventIndex rho vote ≤ stop :=
      (strictEventIndex_mono rho hvoteAction).trans hactionPrefix
    have hbody : Q ∈
        (NamedRun.stateBeforeTime S rho vote w).st.bodies := by
      simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom,
        NamedActionReads.preparedCache, Protocol.NamedStore.setClock,
        vote] using hbodies.2
    have heq := congrFun (stateBeforeTime_eq_stateBefore_strictEventIndex
      S adm.toNamedScheduleWellFormed vote) w
    have hbody' := hbody
    rw [heq] at hbody'
    have hfiltered := hframe.fgRoot_preceq_and_filteredMem
      adm hfrontier hw hvotePrefix hbody' hQheight hPrevQ
    rw [← heq] at hfiltered
    simp only [filteredTree, voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      vote]; exact hfiltered.2

#print axioms voterAnchorSourceQ2Inputs_of_namedHeightRegimeFrame_at_source


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
