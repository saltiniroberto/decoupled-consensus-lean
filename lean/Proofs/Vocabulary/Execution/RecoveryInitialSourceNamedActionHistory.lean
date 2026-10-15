module
public import Proofs.Vocabulary.Protocol.Grades.VoterAnchorSourceInputs
public import Proofs.Vocabulary.Protocol.ChainState.Emission
public import Proofs.Vocabulary.Protocol.Grades.RecoveryDelayedSourceSeed
public import Proofs.Vocabulary.Protocol.Duties.Inputs.FGSourceRawGrade
public import Proofs.Vocabulary.ModelProperties.anchor
public import Proofs.Vocabulary.ModelProperties.NamedProfile_gradeContract
import Proofs.Vocabulary.Objects.EmittedHeightBound
import Proofs.Vocabulary.Protocol.Duties.Inputs.HeightRegimeInductionNamed
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.ProposalVoteDuty
import Proofs.Vocabulary.Protocol.Schedule.GSTZeroReorgResilience
import Proofs.Vocabulary.Protocol.Schedule.WeakGoldfishCone
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star

@[expose] public section

/-!
# Prepared anchor after an SG round

The prepared vote-duty anchor is compatible with a block with which every honest SG vote of the
preceding round is compatible.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Protocol Proofs.Optimistic Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
private theorem actionHistory_compatible_ancestor
    {A B T : Block V} (hAB : Block.Preceq A B)
    (hBT : Block.compatible B T = true) :
    Block.compatible A T = true := by
  rcases (show Block.Preceq B T ∨ Block.Preceq T B by
    simpa only [Block.compatible, Bool.or_eq_true, Block.Preceq] using hBT) with hBT | hTB
  · simp only [Block.compatible, Bool.or_eq_true]
    exact Or.inl (Block.preceq_trans hAB hBT)
  · exact Block.compatible_of_preceq_common hAB hTB


/-- If every honest SG vote of round `round_of (s + 1) − 1` is compatible with `T`, and `w`'s
    vote-duty FG root is compatible with `T`, then `w`'s prepared anchor for slot `s + 1` is
    compatible with `T`. -/
theorem voterAnchorAt_compatible_of_previousSGHistory_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hbelow : BelowOneThird S rho.honest)
    {s : Slot} {T : Block V}
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    (hc : 1 ≤ S.hc.round_of (s + 1))
    (hsg : HonestSGEmissionsCompatibleAtRound S rho
      (S.hc.round_of (s + 1) - 1) T)
    (hsgPost : S.E.t_GST ≤ S.a (S.hc.round_of (s + 1) - 1))
    {w : V} (hw : w ∈ rho.honest)
    (hroot : Block.compatible
      (Protocol.get_fg_root
        (Internal.NamedRecoveryRead.voteDutyRead S rho w
          (s + 1)).st.core.toHealing.toFG) T = true) :
    Block.compatible (voterAnchorAt S rho w (s + 1)) T = true := by
  let c := S.hc.round_of (s + 1)
  let q := c - 1
  have hqc : q + 1 = c := Nat.sub_add_cancel hc
  have hvoteHor : Protocol.vote_time S.E (s + 1) ≤ rho.horizon := by
    apply le_trans (le_of_lt ?_) hhor
    rw [← vote_time_succ_add_delta_eq_confirmation_time S.E s]
    exact Int.lt_add_of_pos_right _ S.E.Δ_pos
  rcases voterAnchorAt_cases S rho w (s + 1) with
    hfg | ⟨root, L, hframe, hactive, hanchor⟩
  · rw [hfg]
    exact hroot
  · rw [hanchor]
    have hround : S.hc.round_of (s + 1) = c := rfl
    have hslo : S.hc.opening_slot c ≤ s + 1 := by
      rw [← hround]
      exact Nat.div_mul_le_self (s + 1) S.hc.R
    have hshi : s + 1 < S.hc.opening_slot (c + 1) := by
      rw [← hround]
      apply (Nat.div_lt_iff_lt_mul
        (Nat.zero_lt_of_lt S.hc.R_ge_two)).mp
      exact Nat.lt_succ_self ((s + 1) / S.hc.R)
    have hnext : Protocol.vote_time S.E (s + 1) ≤
        DecoupledConsensusModel.Protocol.opening S.E S.hc (c + 1) := by
      have hvoteNext : Protocol.vote_time S.E (s + 1) <
          Protocol.proposal_time S.E (s + 2) := by
        apply lt_trans ?_ (support_cutoff_lt_proposal_time_succ S.E (s + 1))
        rw [← Proofs.Optimistic.vote_time_add_delta]
        exact Int.lt_add_of_pos_right _ S.E.Δ_pos
      exact hvoteNext.le.trans (by
        simpa only [DecoupledConsensusModel.Protocol.opening] using
          proposal_time_mono S.E (Nat.succ_le_iff.mpr hshi))
    have hframe' : (DecoupledConsensusModel.Protocol.readFrame
        (Internal.NamedRecoveryRead.voteDutyRead S rho w (s + 1)).cache
        (Internal.NamedRecoveryRead.voteDutyRead S rho w
          (s + 1)).st.core.toHealing c).g1 = some (some root) := by
      have hslot :
          (Internal.NamedRecoveryRead.voteDutyRead S rho w
            (s + 1)).st.core.s = s + 1 :=
        Proofs.Optimistic.voteDutyRead_slot S rho w (s + 1)
      simpa only [hslot, hround] using hframe
    obtain ⟨_, hLgrade⟩ := fixedRoot_activeVoterAnchor_g1_data
      S adm (Nat.zero_lt_of_lt hc) hslo hround hnext hvoteHor hw
        hframe' hactive
    rcases (show Block.Preceq
        (Protocol.get_fg_root
          (Internal.NamedRecoveryRead.voteDutyRead S rho w
            (s + 1)).st.core.toHealing.toFG) T ∨
        Block.Preceq T
          (Protocol.get_fg_root
            (Internal.NamedRecoveryRead.voteDutyRead S rho w
              (s + 1)).st.core.toHealing.toFG) by
      simpa only [Block.compatible, Bool.or_eq_true, Block.Preceq] using hroot) with
      hrootT | hTroot
    · have hdomainVote : DecoupledConsensusModel.Protocol.domain S.E S.hc c .g1 ≤
          Protocol.vote_time S.E (s + 1) := by
        rw [NamedOutageClosure.domain_g1_eq_opening]
        exact (Protocol.proposal_time_mono S.E hslo).trans
          (Protocol.proposal_time_lt_vote_time S.E (s + 1)).le
      have hdomainHor : DecoupledConsensusModel.Protocol.domain S.E S.hc c .g1 ≤
          rho.horizon := hdomainVote.trans hvoteHor
      have hqHor : S.a q ≤ rho.horizon := by
        have hactionDomain : S.a q ≤
            DecoupledConsensusModel.Protocol.domain S.E S.hc c .g1 := by
          apply (le_add_of_nonneg_right S.E.Δ_pos.le).trans
          rw [← hqc]
          apply (NamedOutageClosure.action_delta_le_early
            S S.hc.R_ge_three (Nat.lt_succ_self q)).trans
          simp only [DecoupledConsensusModel.Protocol.early,
            DecoupledConsensusModel.Protocol.Phase.earlyOffset,
            DecoupledConsensusModel.Protocol.domain,
            DecoupledConsensusModel.Protocol.Phase.domainOffset]
          linarith [S.E.Δ_pos]
        exact hactionDomain.trans hdomainHor
      have hvoteFroot : Block.Preceq
          (Internal.NamedRecoveryRead.voteDutyRead S rho w
            (s + 1)).st.core.F
          (Protocol.get_fg_root
            (Internal.NamedRecoveryRead.voteDutyRead S rho w
              (s + 1)).st.core.toHealing.toFG) :=
        StoreFinality.finalized_preceq_fgRoot
          (Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
            S rho (Protocol.vote_time S.E (s + 1)) w)
      have hdomainFvoteF : Block.Preceq
          (NamedRun.stateBeforeTime S rho
            (DecoupledConsensusModel.Protocol.domain S.E S.hc c .g1) w).st.core.F
          (Internal.NamedRecoveryRead.voteDutyRead S rho w
            (s + 1)).st.core.F := by
        simpa only [Internal.NamedRecoveryRead.voteDutyRead,
          NamedActionReads.confirmationReadAt,
          NamedActionReads.confirmationReadFrom,
          Protocol.NamedStore.setClock] using
            (by
              rw [NamedOutageClosure.strict_read_eq_index S rho
                    adm.toNamedScheduleWellFormed.sorted
                    (DecoupledConsensusModel.Protocol.domain S.E S.hc c .g1),
                  NamedOutageClosure.strict_read_eq_index S rho
                    adm.toNamedScheduleWellFormed.sorted
                    (Protocol.vote_time S.E (s + 1))]
              exact Proofs.NamedRuntime.stateBefore_F_mono S rho w
                (NamedOutageClosure.strict_lengths_mono rho hdomainVote))
      have hFT : Block.Preceq
          (NamedRun.stateBeforeTime S rho
            (DecoupledConsensusModel.Protocol.domain S.E S.hc c .g1) w).st.core.F T :=
        Block.preceq_trans hdomainFvoteF
          (Block.preceq_trans hvoteFroot hrootT)
      have hinputs : ∀ u ∈ rho.honest, ∃ y ∈
          DecoupledConsensusModel.Protocol.interpretedInputs
            (NamedRun.stateBeforeTime S rho
              (DecoupledConsensusModel.Protocol.domain S.E S.hc c .g1) w).st.core.toHealing.gradeView
            (NamedRun.stateBeforeTime S rho
              (DecoupledConsensusModel.Protocol.domain S.E S.hc c .g1) w).st.core.F
            S.hc.η_SG c (DecoupledConsensusModel.Protocol.early S.E S.hc c .g1) u,
          y.round = q := by
        intro u hu
        let b := actionAttestationAt S rho u q
        have hemit : NamedRun.emits S rho u (Object.attest b) (S.a q) :=
          honest_emits_exact_actionAttestationAt S adm hu q hqHor (by assumption)
        obtain ⟨j, hj, _, Hb, hHb, hconfirmed⟩ :=
          Proofs.NamedOutageInputs.emitted_attestation_head S rho hemit
        have hcarrierMem : actionSGBlockAt S rho u q ∈
            (NamedRun.stateBeforeTime S rho (S.a q) u).st.core.T :=
          actionSGBlockAt_mem_storeBeforeTime S rho u q
        obtain ⟨D, hDbody, hDerase⟩ :=
          Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime
            S rho (S.a q) u hcarrierMem
        obtain ⟨n, hn, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
          adm.toNamedScheduleWellFormed.sorted (S.a q)
        have hDprefix : D ∈ (NamedRun.stateBefore S rho n u).st.bodies := by
          rw [← hn]
          exact hDbody
        have hHbSource : Hb ∈
            (NamedRun.stateBeforeTime S rho (S.a q) u).st.bodies := by
          have hstate := NamedActionSources.action_read_index S rho
            adm.toNamedScheduleWellFormed j u b.round
              (by simpa only [b, (actionAttestationAt_shape S rho u q).2.1]
                using hj)
          change Hb ∈ (NamedRun.stateBefore S rho j u).st.bodies at hHb
          rw [← (actionAttestationAt_shape S rho u q).2.1, ← hstate]
          exact hHb
        have hHbPrefix : Hb ∈ (NamedRun.stateBefore S rho n u).st.bodies := by
          rw [← hn]
          exact hHbSource
        have hDrun : RunBlock S rho D :=
          Proofs.Bridges.runBlock_of_stateBefore_mem S hu hDprefix
        have hHbrun : RunBlock S rho Hb :=
          Proofs.Bridges.runBlock_of_stateBefore_mem S hu hHbPrefix
        have hrootDH : D.root = Hb.root := by
          rw [← Proofs.NamedWire.erase_root D, hDerase]
          exact Option.some.inj
            ((actionAttestationAt_shape S rho u q).2.2.symm.trans hconfirmed)
        have hDH : D = Hb :=
          adm.toNamedRootCollisionFree.root_injective D Hb hDrun hHbrun
            D Hb (Or.inl (Proofs.NamedAncestry.named_self D))
              (Or.inr (Proofs.NamedAncestry.named_self Hb)) hrootDH
        have hHbErase : Hb.erase = actionSGBlockAt S rho u q := by
          rw [← hDH, hDerase]
        have hcarrierT : Block.compatible Hb.erase T = true := by
          rw [hHbErase]
          exact hsg u hu hemit
        have hk : q ∈ Protocol.latest_window S.hc.η_SG c := by
          rw [← hqc]
          apply NamedOutageClosure.mem_latest_window
          · simpa only [Nat.add_sub_cancel] using
              Nat.sub_le_sub_left S.hc.η_SG_ge_one (q + 1)
          · exact Nat.lt_succ_self q
        have hdeadline : max (S.a b.round) S.E.t_GST + S.E.Δ ≤
            DecoupledConsensusModel.Protocol.early S.E S.hc c .g1 := by
          rw [show b.round = q from (actionAttestationAt_shape S rho u q).2.1,
            max_eq_left hsgPost, ← hqc]
          apply (NamedOutageClosure.action_delta_le_early
            S S.hc.R_ge_three (Nat.lt_succ_self q)).trans
          simp only [DecoupledConsensusModel.Protocol.early,
            DecoupledConsensusModel.Protocol.Phase.earlyOffset]
          linarith [S.E.Δ_pos]
        have horder : DecoupledConsensusModel.Protocol.early S.E S.hc c .g1 ≤
            DecoupledConsensusModel.Protocol.domain S.E S.hc c .g1 := by
          simp only [DecoupledConsensusModel.Protocol.early, DecoupledConsensusModel.Protocol.domain,
            DecoupledConsensusModel.Protocol.Phase.earlyOffset,
            DecoupledConsensusModel.Protocol.Phase.domainOffset]
          linarith [S.E.Δ_pos]
        have hcut : DecoupledConsensusModel.Protocol.early S.E S.hc c .g1 ≤
            rho.horizon := horder.trans hdomainHor
        have hhead : ∃ j : Nat,
            rho.events[j]? = some (.tick u (S.a q)) ∧
            Hb ∈ (NamedActionReads.actionReadFrom S
              (NamedRun.stateBefore S rho j u) b.round).st.bodies ∧
            b.confirmed = some Hb.root := by
          exact ⟨j, hj, hHb, hconfirmed⟩
        rcases (show Block.Preceq Hb.erase T ∨ Block.Preceq T Hb.erase by
          simpa only [Block.compatible, Bool.or_eq_true, Block.Preceq] using hcarrierT) with
          hHbT | hTHb
        · obtain ⟨y, hy, hyround, -⟩ :=
            interpretedInputs_exact_of_honest_window_vote_after_gst_common_upper
              S adm.toNamedAdmissibleCore .g1 hk hu hw
                ⟨(actionAttestationAt_shape S rho u q).1,
                  (actionAttestationAt_shape S rho u q).2.1, hemit⟩
                hhead hHbT hFT
                (by simpa only [b,
                  (actionAttestationAt_shape S rho u q).2.1] using hsgPost)
                hdeadline horder hcut
          exact ⟨y, hy, hyround⟩
        · obtain ⟨y, hy, hyround, -⟩ :=
            interpretedInputs_exact_of_honest_window_vote_after_gst_common_upper
              S adm.toNamedAdmissibleCore .g1 hk hu hw
                ⟨(actionAttestationAt_shape S rho u q).1,
                  (actionAttestationAt_shape S rho u q).2.1, hemit⟩
                hhead (Block.preceq_self Hb.erase)
                (Block.preceq_trans hFT hTHb)
                (by simpa only [b,
                  (actionAttestationAt_shape S rho u q).2.1] using hsgPost)
                hdeadline horder hcut
          exact ⟨y, hy, hyround⟩
      have hinterpreted : ∀ u ∈ rho.honest,
          (DecoupledConsensusModel.Protocol.interpretedInputs
            (NamedRun.stateBeforeTime S rho
              (DecoupledConsensusModel.Protocol.domain S.E S.hc c .g1) w).st.core.toHealing.gradeView
            (NamedRun.stateBeforeTime S rho
              (DecoupledConsensusModel.Protocol.domain S.E S.hc c .g1) w).st.core.F
            S.hc.η_SG c (DecoupledConsensusModel.Protocol.early S.E S.hc c .g1) u).Nonempty := by
        intro u hu
        obtain ⟨y, hy, -⟩ := hinputs u hu
        exact ⟨y, hy⟩
      have hwindow := windowMajorityAt_of_honestWeightMajority_of_interpreted
        S (AlignedRoundLemmas.honestWeightMajority_of_belowOneThird hbelow)
          hinterpreted
      have hgrade : DecoupledConsensusModel.Protocol.gradeBool S.E
          (NamedRun.stateBeforeTime S rho
            (DecoupledConsensusModel.Protocol.domain S.E S.hc c .g1) w).st.core.toHealing.gradeView
          (NamedRun.stateBeforeTime S rho
            (DecoupledConsensusModel.Protocol.domain S.E S.hc c .g1) w).st.core.F
          S.hc.η_SG c (DecoupledConsensusModel.Protocol.early S.E S.hc c .g1)
            (DecoupledConsensusModel.Protocol.late S.E S.hc c .g1) L = true := by
        simpa only [PhaseGrades.storeGrade, PhaseGrades.phaseGrade,
          PhaseGrades.readAt] using hLgrade
      obtain ⟨u, hu, _, _, _, _, _, _, _, hpositive⟩ :=
        exists_honest_positive_supporter_of_relativeGrade
          S.E S.hc hwindow hgrade
      simp only [DecoupledConsensusModel.Protocol.positive, decide_eq_true_eq]
        at hpositive
      obtain ⟨tok, htok, hmax, hcover, _, _⟩ := hpositive
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp htok
      obtain ⟨z, hz, hzRound⟩ := hinputs u hu
      have hyRoundLe : y.round < c := by
        have hyraw := (Finset.mem_filter.mp hy).1
        simp only [DecoupledConsensusModel.Protocol.rawInputs, Finset.mem_filter] at hyraw
        obtain ⟨k, hk, hyk⟩ := Finset.mem_biUnion.mp hyraw.1
        have hyRoundK := GradeDeliveryRun.projected_rounds_storeBeforeTime
          S adm.toNamedScheduleWellFormed w
            (DecoupledConsensusModel.Protocol.domain S.E S.hc c .g1) k y hyk
        rw [hyRoundK]
        exact (NamedOutageClosure.window_bounds (List.mem_toFinset.mp hk)).2
      have hyRound : y.round = q := by
        have hqLe : q ≤ y.round := by
          rw [← hzRound]
          exact hmax (DecoupledConsensusModel.Protocol.token z)
            (Finset.mem_image_of_mem DecoupledConsensusModel.Protocol.token hz)
        have hyLe : y.round ≤ q := by
          have hlt := hyRoundLe
          rw [← hqc] at hlt
          exact Nat.le_of_lt_succ hlt
        exact Nat.le_antisymm hyLe hqLe
      obtain ⟨key, Head, hyconfirmed, hyfind, _, hLHead⟩ :=
        Proofs.HealingLemmas.exists_head_of_head_covers hcover
      have hyPool : y ∈
          (NamedRun.stateBeforeTime S rho
            (DecoupledConsensusModel.Protocol.domain S.E S.hc c .g1) w).st.core.toHealing.sg_votes q := by
        have hyraw := (Finset.mem_filter.mp hy).1
        simp only [DecoupledConsensusModel.Protocol.rawInputs, Finset.mem_filter] at hyraw
        obtain ⟨k, _, hyk⟩ := Finset.mem_biUnion.mp hyraw.1
        have hyRoundK := GradeDeliveryRun.projected_rounds_storeBeforeTime
          S adm.toNamedScheduleWellFormed w
            (DecoupledConsensusModel.Protocol.domain S.E S.hc c .g1) k y hyk
        have hkq : k = q := hyRoundK.symm.trans hyRound
        simpa only [hkq, Protocol.HealingStore.gradeView] using hyk
      have hySender : y.val_index = u := by
        have hyraw := (Finset.mem_filter.mp hy).1
        simp only [DecoupledConsensusModel.Protocol.rawInputs, Finset.mem_filter] at hyraw
        exact hyraw.2.1
      have hHeadT := rootCompatible_of_emittedSGHistory_at_read
        S adm hw hsg hyPool (hySender ▸ hu)
      have hheadRoot : Head.root = key := Proofs.HealingLemmas.find?_root hyfind
      have hyconfirmed' : y.confirmed = some Head.root := by
        rw [hheadRoot]
        exact hyconfirmed
      have hyfind' : Block.find?
          (NamedRun.stateBeforeTime S rho
            (DecoupledConsensusModel.Protocol.domain S.E S.hc c .g1) w).st.core.T
          Head.root = some Head := by
        rw [hheadRoot]
        exact hyfind
      change rootCompatible
        (NamedRun.stateBeforeTime S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc c .g1) w).st.core.T
        T y.confirmed = true at hHeadT
      rw [hyconfirmed'] at hHeadT
      change (match Block.find?
        (NamedRun.stateBeforeTime S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc c .g1) w).st.core.T
          Head.root with
        | some H => Block.compatible H T
        | none => true) = true at hHeadT
      rw [hyfind'] at hHeadT
      exact actionHistory_compatible_ancestor hLHead hHeadT
    · have hrootL : Block.Preceq
          (Protocol.get_fg_root
            (Internal.NamedRecoveryRead.voteDutyRead S rho w
              (s + 1)).st.core.toHealing.toFG) L := by
        have hLmem : L ∈ PhaseGrades.filteredTree
            (Internal.NamedRecoveryRead.voteDutyRead S rho w (s + 1)) := by
          unfold DecoupledConsensusModel.Protocol.activePrefix at hactive
          exact (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hactive)).1
        exact Proofs.Records.preceq_get_fg_root_of_mem_filtered hLmem
      simp only [Block.compatible, Bool.or_eq_true]
      exact Or.inr (Block.preceq_trans hTroot hrootL)

#print axioms voterAnchorAt_compatible_of_previousSGHistory_named


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
