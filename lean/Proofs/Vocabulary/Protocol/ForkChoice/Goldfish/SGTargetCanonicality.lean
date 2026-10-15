module
public import Proofs.Vocabulary.Execution.ExcludesRefute
public import Proofs.Vocabulary.ModelProperties.Block_Preceq
public import Proofs.Vocabulary.ModelProperties.viable_tree
public import Proofs.Vocabulary.ModelProperties.get_fg_root
public import Proofs.Vocabulary.ModelProperties.currentSGVote
public import Proofs.Vocabulary.ModelProperties.get_sg_vote_with
public import Proofs.Vocabulary.ModelProperties.Store_toHealing
public import Proofs.Vocabulary.ModelProperties.NamedDuties_update_confirmation_with
public import Proofs.Vocabulary.ModelProperties.update_confirmation_with
public import Proofs.Vocabulary.ModelProperties.confirmationReadFrom
public import Proofs.Vocabulary.Objects.FixedHeightRootCore
public import Proofs.Vocabulary.Internal.Internal.GradeReads
public import Proofs.Vocabulary.Objects.ActionRound
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.Adoption
public import Proofs.Vocabulary.Protocol.Grades.ProposalLifecycleCore
import Proofs.Vocabulary.Execution.Acceptance
import Proofs.Vocabulary.Generic.PostGSTCarrierAdmissionCore
import Proofs.Vocabulary.Objects.SGTargetCompatibility
import Proofs.Vocabulary.Protocol.ChainState.SlashableBoundBridge
import Proofs.Vocabulary.Protocol.Grades.Grades
import Proofs.Vocabulary.Protocol.Handlers.AcceptanceTiming
import Proofs.Vocabulary.Protocol.Handlers.AdoptionConstructor
import Proofs.Vocabulary.Protocol.Handlers.FinalityMonotoneCore
import Proofs.Vocabulary.Protocol.Schedule.GSTZeroHeadResolution
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar

@[expose] public section

/-!
# Filtered-tree and voter-tree membership

A processed descendant of the FG root stays in the filtered block tree under a one-step height cap,
and a block that passes the confirmation test at an honest validator after GST is in later voters'
processed block trees.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]


/-! ## Filtered-tree membership under a height cap -/

/-- A named store body `Bn` whose erasure `B` is a descendant of the FG root `J` is in the filtered
    block tree when the store's `h_max` is at most `Bn`'s height plus one. -/
theorem mem_filtered_of_mem_tree_of_exactFGRoot_heightCap
    (S : Setup V) (rho : Run V) (w : V) (read : Time)
    {J B : Block V} {Bn : NamedBlock V}
    (hBn : Bn ∈ (rho.storeBeforeTime S w read).bodies)
    (hB : Bn.erase = B)
    (hroot : Protocol.get_fg_root
      (rho.storeBeforeTime S w read).toHealing.toFG = J)
    (hJB : Block.Preceq J B)
    (hcap : (rho.storeBeforeTime S w read).h_max ≤
      (Protocol.derive_named S.E S.cfg Bn).h + 1) :
    B ∈ Protocol.get_filtered_block_tree
      (rho.storeBeforeTime S w read).toHealing.toFG := by
  let st := rho.storeBeforeTime S w read
  have hcoh : Proofs.NamedStore.Coherent S.E S.cfg st := by
    simpa only [st, Run.storeBeforeTime] using
      (Proofs.NamedRuntime.stateBeforeTime_invariants S rho read w).1.1.1
  have hBmem : B ∈ st.core.T := by
    rw [hcoh.1, ← hB]
    exact Finset.mem_image_of_mem NamedBlock.erase hBn
  have hFJ : Block.Preceq st.F st.J :=
    Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime S rho read w
  have hFroot : Block.Preceq st.F
      (Protocol.get_fg_root st.toHealing.toFG) := by
    have h := Proofs.Records.preceq_get_fg_root_of_F (st := st.core.toHealing.toFG)
      (by
        rw [Proofs.ModelProperties.toHealing_F, Proofs.ModelProperties.toHealing_J]
        exact Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mpr hFJ)
    rw [Proofs.ModelProperties.toHealing_F] at h
    exact Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mp h
  have hrootB : Block.Preceq
      (Protocol.get_fg_root st.toHealing.toFG) B := by
    rw [hroot]
    exact hJB
  have hFB : Block.Preceq st.F B := Proofs.ModelProperties.Preceq_trans hFroot hrootB
  have hview := Proofs.NamedStoreBridge.derivedView_stateBeforeTime S rho read w Bn hBn
  have hσ : st.σ B = Protocol.derive_named S.E S.cfg Bn := by
    simpa only [st, hB, Run.storeBeforeTime] using hview
  have hheight : st.h_max - 1 ≤ (st.σ B).h := by
    rw [hσ]
    exact Nat.sub_le_iff_le_add.mpr hcap
  have hV : B ∈ Protocol.V_tree st.toHealing.toFG := by
    unfold Protocol.V_tree
    rw [Proofs.ModelProperties.mem_viable_tree_iff, Proofs.ModelProperties.toHealing_T,
      Proofs.ModelProperties.toHealing_F, Proofs.ModelProperties.toHealing_σ,
      Proofs.ModelProperties.toHealing_h_max]
    exact ⟨⟨hBmem, hFB⟩, B, hBmem, Proofs.ModelProperties.Preceq_self B, hheight⟩
  exact Proofs.Records.mem_filtered_of_mem_V_tree hV
    (Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mpr hrootB)


/-- If `B` passes the confirmation test at `v`'s slot-`source` confirmation store after GST
    (`GenuineConfirmation`), and the FG root of `w`'s vote-duty store at slot `k + 1`, with
    `source + 1 ≤ k`, is an ancestor of `B`, then `B` is in that store's voter processed block tree. -/
theorem voterProcessedTarget_of_genuineConfirmation_at_laterVoteDuty_after_gst
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    {source k : Slot}
    (hsourceNextLe : source + 1 ≤ k)
    (hpost : S.E.t_GST ≤ Protocol.proposal_time S.E source)
    (hhor : Protocol.vote_time S.E (k + 1) ≤ rho.horizon)
    {B : Block V} {contract : Protocol.GradeContract V}
    (hgenuine : GenuineConfirmation (contract := contract) S.E S.hc
      (Proofs.Optimistic.confStore S rho v source) source B)
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (Proofs.Optimistic.voteDutyStore S rho w (k + 1)).toHealing.toFG) B) :
    B ∈ Protocol.voter_processed_block_tree S.E
      (Proofs.Optimistic.voteDutyStore S rho w (k + 1)).toHealing.toFG.toSG.toGoldfishStore
      (Proofs.Optimistic.voteDutyStore S rho w (k + 1)).toHealing.s := by
  have hN := confNumerator S.E (Proofs.Optimistic.confStore S rho v source) source
  have hpositive : 0 <
      (Protocol.goldfishSupporters S.E (Proofs.Optimistic.confStore S rho v source).T
        (confVotes S.E (Proofs.Optimistic.confStore S rho v source) source)
        (confVotes S.E (Proofs.Optimistic.confStore S rho v source) source) source B).card := by
    have heligible := hgenuine.eligible
    rw [hN.score_eq_supporters] at heligible
    by_contra hnot
    have hzero :
        (Protocol.goldfishSupporters S.E (Proofs.Optimistic.confStore S rho v source).T
          (confVotes S.E (Proofs.Optimistic.confStore S rho v source) source)
          (confVotes S.E (Proofs.Optimistic.confStore S rho v source) source) source B).card = 0 :=
      Nat.eq_zero_of_not_pos hnot
    rw [hzero] at heligible
    simp at heligible
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hpositive
  rw [mem_supporters_iff] at hu
  obtain ⟨-, u, huBy, -, htargets⟩ := hu
  rw [Protocol.votes_by, Finset.mem_filter] at huBy
  obtain ⟨H, hfind, hBH⟩ := targets_under_iff.mp htargets
  let duty := Proofs.Optimistic.voteDutyStore S rho w (k + 1)
  have hslot : duty.toHealing.s = k + 1 := by
    simpa only [duty, Proofs.Optimistic.toHealing_slot] using
      Proofs.Optimistic.voteDutyStore_slot S rho w (k + 1)
  by_cases hgen : H = Block.genesis
  · subst H
    have hBgen : B = Block.genesis :=
      Block.preceq_antisymm hBH.2 (Protocol.preceq_genesis B)
    subst B
    have hgenesis := genesis_mem_and_stamp_storeBeforeTime
      S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed w
        (Protocol.vote_time S.E (k + 1))
        (Protocol.view_freeze S.E k)
    simp only [Protocol.voter_processed_block_tree, Finset.mem_filter]
    rw [hslot, Nat.add_sub_cancel]
    exact ⟨by
      simpa only [duty, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore, Protocol.Store.toHealing] using hgenesis.1,
      Or.inl (by
        simpa only [duty, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
          Proofs.Optimistic.tickStore, Protocol.Store.toHealing] using hgenesis.2)⟩
  · have hHsource : H ∈ (Proofs.Optimistic.confStore S rho v source).T :=
      Proofs.HealingLemmas.find?_mem hfind
    have hearly : u ∈ confEarly S.E (Proofs.Optimistic.confStore S rho v source) source :=
      (Finset.mem_filter.mp huBy.1).1
    have hresolved : stampedBefore
        (Proofs.Optimistic.confStore S rho v source).tau
        (Protocol.support_cutoff S.E source) u = true := by
      rw [confEarly, beforeCutoff, Finset.mem_filter] at hearly
      exact hearly.2
    have hHstamp : stampedBefore
        (Proofs.Optimistic.confStore S rho v source).timestamp_block
        (Protocol.support_cutoff S.E source) H = true :=
      HonestWeightMajority.stampedBefore_block_of_resolution hfind hresolved
    obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
        (Protocol.confirmation_time S.E source)
    have hHn : H ∈ (rho.stateBefore S n v).st.core.T := by
      simpa only [Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore,
        Run.storeBeforeTime, hn] using hHsource
    have hstampn : stampedBefore
        (rho.stateBefore S n v).st.core.timestamp_block
        (Protocol.support_cutoff S.E source) H = true := by
      simpa only [Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore,
        Run.storeBeforeTime, hn] using hHstamp
    obtain hgen' | ⟨D, hDerase, i, hin, t, hacc⟩ :=
      acceptsAt_block_of_processed_erased S rho v n hHn
    · exact False.elim (hgen hgen')
    · have htSupport : t < Protocol.support_cutoff S.E source :=
        Protocol.HonestWeightMajority.acceptsAt_block_lt_of_stamp_before
          S adm hv hacc (Nat.succ_le_of_lt hin)
            (publicTime_support_cutoff S source) (by
              simpa only [hDerase] using hstampn)
      have hDposErase : 0 < D.erase.slot :=
        Nat.zero_lt_of_lt (parent_slot_lt_of_acceptsAt_block S hacc)
      have hDpos : 0 < D.slot := by
        cases D <;> exact hDposErase
      have hfreezeHor : Protocol.view_freeze S.E k ≤ rho.horizon :=
        (le_of_lt (view_freeze_lt_vote_time_succ S.E k)).trans hhor
      have hpostCut : S.E.t_GST ≤ Protocol.support_cutoff S.E source := by
        apply le_trans hpost
        unfold Protocol.proposal_time Protocol.support_cutoff
        exact le_add_of_nonneg_right
          (Int.mul_nonneg (by norm_num) (le_of_lt S.E.Δ_pos))
      have hsourceLeK : source ≤ k :=
        le_trans (Nat.le_succ source) hsourceNextLe
      have hcutMono : Protocol.support_cutoff S.E source ≤
          Protocol.support_cutoff S.E k :=
        Proofs.Optimistic.support_cutoff_mono S.E hsourceLeK
      have htSupportK : t < Protocol.support_cutoff S.E k :=
        lt_of_lt_of_le htSupport hcutMono
      have hpostCutK : S.E.t_GST ≤ Protocol.support_cutoff S.E k :=
        hpostCut.trans hcutMono
      have hadmit : AdmittedBefore S rho w H
          (Protocol.view_freeze S.E k) := by
        simpa only [hDerase] using
          (Protocol.block_admittedBefore_of_accepted_after_cutoff
            S adm hv hw hDpos hacc
              htSupportK hpostCutK
            (support_cutoff_add_delta_eq_view_freeze S.E k) hfreezeHor
            (by
              intro j hj
              have hjVote := hj.trans (strict_filter_length_mono rho
                (le_of_lt (view_freeze_lt_vote_time_succ S.E k)))
              have hroot' : Block.Preceq
                  (Protocol.get_fg_root
                    (rho.storeBeforeTime S w
                      (Protocol.vote_time S.E (k + 1))).toHealing.toFG) B := by
                exact
                    (show Block.Preceq
                      (Protocol.get_fg_root
                        (Internal.NamedRecoveryRead.voteDutyRead S rho w
                          (k + 1)).st.core.toHealing.toFG) B by
                      exact hroot)
              exact Block.preceq_trans
                (finalized_preceq_at_prefix_of_storeBeforeRoot_preceq
                  S rho adm.toNamedAdmissibleCore.toNamedScheduleWellFormed.sorted
                  hroot' hjVote)
                (by simpa only [hDerase] using hBH.2)))
      have hvisibleB := Proofs.Optimistic.admittedBefore_ancestor_mem_and_stamp_at S
        adm hadmit hBH.2
          (le_of_lt (view_freeze_lt_vote_time_succ S.E k))
      simp only [Protocol.voter_processed_block_tree, Finset.mem_filter]
      rw [hslot, Nat.add_sub_cancel]
      exact ⟨by
        simpa only [duty, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
          Proofs.Optimistic.tickStore, Protocol.Store.toHealing] using hvisibleB.1,
        Or.inl (by
          simpa only [duty, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
            Proofs.Optimistic.tickStore, Protocol.Store.toHealing] using hvisibleB.2)⟩


omit [Fintype V] in
private theorem rootLock_named_genesis_of_erase_genesis
    {B : NamedBlock V} (hB : B.erase = Block.genesis) :
    B = NamedBlock.genesis := by
  cases B with
  | genesis => rfl
  | node parent slot root votes support rows proposer =>
      simp only [NamedBlock.erase] at hB
      exact absurd hB (by simp)


#print axioms mem_filtered_of_mem_tree_of_exactFGRoot_heightCap
#print axioms voterProcessedTarget_of_genuineConfirmation_at_laterVoteDuty_after_gst

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
