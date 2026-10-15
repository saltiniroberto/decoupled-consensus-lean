module
public import Proofs.Vocabulary.Protocol.Grades.VoterAnchorSourceInputs
public import Proofs.Vocabulary.Protocol.ChainState.Emission
public import Proofs.Vocabulary.Protocol.Grades.RecoveryDelayedSourceSeed
public import Proofs.Vocabulary.Protocol.Duties.Inputs.FGSourceRawGrade
public import Proofs.Vocabulary.Protocol.Grades.RecoveryInitialSourceNamedHistory
public import Proofs.Vocabulary.Execution.HandoverLegacyFinality
import Proofs.Vocabulary.Objects.EmittedHeightBound
import Proofs.Vocabulary.Protocol.Schedule.PostHealingReuse

@[expose] public section

/-!
# Facts from a height-regime frame

The source body of a `PrefixFGSelectorConeAt` is held at every honest action read of its round, and
every honest maximum height from that action time on is at least `blocked + 1`.
-/


namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Protocol Proofs.Optimistic Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]


/-- Under a `PrefixFGSelectorConeAt` and a `NamedHeightRegimeFrame`, the source body `Cfg` is a body
    of every honest validator's action store at round `a.round`. -/
theorem PrefixFGSelectorConeAt.sourceMem_at_action_of_frame_named
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    {start first : Nat} {blocked : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg Tprev : NamedBlock V} {T : Block V} {c0 : Round}
    (hseed : PrefixFGSelectorConeAt S rho start first blocked i a ta Cfg T)
    (hframe : NamedHeightRegimeFrame S rho blocked (first - 1) Tprev c0)
    (ready : GradeRoundReady S rho a.round)
    {w : V} (hw : w ∈ rho.honest) :
    Cfg ∈ (actionStoreAt S rho w a.round).st.bodies := by
  have hactionPrefix : strictEventIndex rho (S.a a.round) ≤ first - 1 :=
    Nat.le_sub_one_of_lt
      (hseed.actionPrefix_lt adm.toNamedScheduleWellFormed)
  have hactionHor : S.a a.round ≤ rho.horizon := hseed.actionHorizon adm
  have hTprevCfg : NamedBlock.Preceq Tprev Cfg :=
    hframe.sourceAbove a.val_index hseed.signerHonest a.round
      hactionPrefix hactionHor Cfg hseed.sourceMem hseed.exactFGSource
        hseed.sourceDerivedHeight
  have hfloor : FinalityFloorAt S rho blocked (first - 1) Tprev.erase := by
    intro v hv n hn X hXrun hXheight hTX
    have hTXnamed := Protocol.namedPreceq_of_runBlock_erase_preceq
      adm hframe.prevRun hXrun hTX
    exact hframe.floor v hv n hn X hXrun hXheight hTXnamed
  obtain ⟨Q, hQ⟩ : ∃ Q : Block V, PhaseGrades.nodeQ2
      S (actionReadAt S rho a.val_index a.round) a.round = some Q := by
    cases hQ : PhaseGrades.nodeQ2
        S (actionReadAt S rho a.val_index a.round) a.round with
    | none =>
        have hsource := hseed.exactFGSource
        unfold actionFGSource at hsource
        dsimp only at hsource
        have hround : S.hc.round_of
            (actionStoreAt S rho a.val_index a.round).st.core.toHealing.s =
              a.round := by
          simpa only [Protocol.Store.toHealing] using
            actionStoreAt_round S rho a.val_index a.round
        rw [hround] at hsource
        change Protocol.grade2_block_with
          (NamedProfile.gradeContract
            (actionReadAt S rho a.val_index a.round).cache)
          S.E S.hc
          (actionReadAt S rho a.val_index a.round).st.core.toHealing
          a.round = none at hQ
        simp only [actionStoreAt] at hsource
        rw [Protocol.fg_source_with.eq_def, hQ] at hsource
        cases hsource
    | some Q => exact ⟨Q, rfl⟩
  rcases actionFGSource_genuineClear_or_selectedG2_named
      S rho a.val_index a.round hQ hseed.exactFGSource with
    hgenuine | hselected
  · obtain ⟨B, hgenuine, -, -, -, hCfgB⟩ := hgenuine
    have hvoteBody := ancestorGenuineConfirmation_body_at_nextVote_of_floor
      S adm ready hseed.signerHonest hgenuine hCfgB hseed.sourceMem
        hfloor hseed.sourceDerivedHeight (Proofs.NamedWire.erase_preceq hTprevCfg)
        hactionPrefix hactionHor hw
    let vote := Protocol.vote_time S.E (S.hc.opening_slot a.round + 1)
    have hvotePre : Cfg ∈
        (NamedRun.stateBeforeTime S rho vote w).st.bodies := by
      simpa only [Internal.NamedRecoveryRead.voteDutyRead,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom,
        NamedActionReads.preparedCache, Protocol.NamedStore.setClock,
        vote] using hvoteBody
    have heqVote := congrFun
      (stateBeforeTime_eq_stateBefore_strictEventIndex
        S adm.toNamedScheduleWellFormed vote) w
    have heqAction := congrFun
      (stateBeforeTime_eq_stateBefore_strictEventIndex
        S adm.toNamedScheduleWellFormed (S.a a.round)) w
    rw [heqVote] at hvotePre
    have hactionPre : Cfg ∈
        (NamedRun.stateBeforeTime S rho (S.a a.round) w).st.bodies := by
      rw [heqAction]
      exact NamedBodyRetention.stateBefore_bodies_mono S rho w
        (strictEventIndex_mono rho
          (Protocol.next_vote_time_lt_action S a.round).le)
        hvotePre
    simp only [actionStoreAt, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime, Protocol.NamedStore.setClock, Protocol.Store.toHealing]; exact hactionPre
  · have hselectedCfg : PhaseGrades.nodeQ2
        S (actionReadAt S rho a.val_index a.round) a.round =
          some Cfg.erase := by
      simpa only [hselected] using hQ
    exact (selectedQ2_body_at_action_and_openingVote_of_floor
      S adm ready hseed.signerHonest hselectedCfg hseed.sourceMem
        hfloor hseed.sourceDerivedHeight (Proofs.NamedWire.erase_preceq hTprevCfg)
        hactionPrefix hw).1

#print axioms PrefixFGSelectorConeAt.sourceMem_at_action_of_frame_named

/-- Under a `PrefixFGSelectorConeAt` and a `NamedHeightRegimeFrame`, every honest validator's
    `h_max` at any time from `S.a a.round` on is at least `blocked + 1`. -/
theorem PrefixFGSelectorConeAt.localFrontier_ge_from_source_of_frame_named
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    {start first : Nat} {blocked : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg Tprev : NamedBlock V} {T : Block V} {c0 : Round}
    (hseed : PrefixFGSelectorConeAt S rho start first blocked i a ta Cfg T)
    (hframe : NamedHeightRegimeFrame S rho blocked (first - 1) Tprev c0)
    (ready : GradeRoundReady S rho a.round)
    {read : Time} (hread : S.a a.round ≤ read)
    {w : V} (hw : w ∈ rho.honest) :
    blocked + 1 ≤ (rho.storeBeforeTime S w read).h_max := by
  have hsource := hseed.sourceMem_at_action_of_frame_named
    adm hframe ready hw
  have hsourcePre : Cfg ∈
      (NamedRun.stateBeforeTime S rho (S.a a.round) w).st.bodies := by
    simp only [actionStoreAt, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime, Protocol.NamedStore.setClock, Protocol.Store.toHealing]; exact hsource
  have heqSource := congrFun
    (stateBeforeTime_eq_stateBefore_strictEventIndex
      S adm.toNamedScheduleWellFormed (S.a a.round)) w
  have heqRead := congrFun
    (stateBeforeTime_eq_stateBefore_strictEventIndex
      S adm.toNamedScheduleWellFormed read) w
  rw [heqSource] at hsourcePre
  have hCfgRead : Cfg ∈
      (NamedRun.stateBeforeTime S rho read w).st.bodies := by
    rw [heqRead]
    exact NamedBodyRetention.stateBefore_bodies_mono S rho w
      (strictEventIndex_mono rho hread) hsourcePre
  have hheight := Proofs.NamedStoreBridge.heights_le_hMax_stateBeforeTime
    S rho read w Cfg hCfgRead
  simpa only [hseed.sourceDerivedHeight, Run.storeBeforeTime] using hheight

#print axioms PrefixFGSelectorConeAt.localFrontier_ge_from_source_of_frame_named


end HealingSurface

end Proofs
end DecoupledConsensusModel

end
