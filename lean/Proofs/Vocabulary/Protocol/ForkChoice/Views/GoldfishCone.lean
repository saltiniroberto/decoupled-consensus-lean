module
public import Proofs.Vocabulary.Protocol.Grades.GoldfishConePersistence
public import Proofs.Vocabulary.Protocol.Schedule.CanonicalSuffixPostGSTCore
public import Proofs.Vocabulary.Execution.ProposerCone
public import Proofs.Vocabulary.Execution.PreparedReadBridge
import Proofs.Vocabulary.Execution.Acceptance
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.Adoption
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.ConePersistence
import Proofs.Vocabulary.Protocol.ForkChoice.Views.VoteSetValidityCore
import Proofs.Vocabulary.Protocol.ForkChoice.Views.VoteViewValidity
import Proofs.Vocabulary.Protocol.Grades.GSTZeroSelectionSafety
import Proofs.Vocabulary.Protocol.Handlers.AdoptionConstructor
import Proofs.Vocabulary.Protocol.Handlers.FinalityMonotoneCore
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
public import Proofs.Vocabulary.Internal.Internal.GradeReads

@[expose] public section

/-!
# Goldfish cone propagation

If every honest Goldfish vote of slot `s` is for a descendant of `C`, then after GST the head of
every honest slot-`s + 1` vote is also a descendant of `C`; with the availability and eligibility
facts this uses.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Internal.NamedRecoveryRead
open Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem named_admittedBefore_of_voteDutyRead_mem_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {w : V} (hw : w ∈ rho.honest) {s : Slot} {B : NamedBlock V}
    (hmem : B.erase ∈ (voteDutyRead S rho w s).st.core.T) :
    ∃ C : NamedBlock V, C.erase = B.erase ∧
      (C = NamedBlock.genesis ∨
        NamedAdmittedBefore S rho w C (Protocol.vote_time S.E s)) := by
  let t := Protocol.vote_time S.E s
  obtain ⟨n, hn, _⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S
    adm.toNamedScheduleWellFormed t
  have hBn : B.erase ∈ (rho.stateBefore S n w).st.core.T := by
    simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore,
      Run.storeBeforeTime, t, hn] using hmem
  obtain ⟨C, hCmem, hCerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore S rho n w hBn
  have hprocessed : Object.processed (rho.stateBefore S n w).st
      (.block C) = true := by
    simpa only [Object.processed, NamedReceipt.processed, decide_eq_true_eq]
      using hCmem
  refine ⟨C, hCerase, ?_⟩
  rcases Protocol.acceptsAt_block_of_processed S rho w n C hprocessed with
    hgen | ⟨i, hi, ta, hacc⟩
  · exact Or.inl hgen
  · right
    have hstamp : stampedBefore
        (rho.stateBefore S n w).st.core.timestamp_block t C.erase = true := by
      have hbodyEq : (NamedRun.stateBeforeTime S rho t w).st.bodies =
          (NamedRun.stateBefore S rho n w).st.bodies := by
        exact congrArg (fun z => (z w).st.bodies) hn
      have hCtime : C ∈ (NamedRun.stateBeforeTime S rho t w).st.bodies := by
        rw [hbodyEq]
        exact hCmem
      have hstampTime := NamedBlockStamp.held_body_stampedBefore_stateBeforeTime
        S rho adm.toNamedScheduleWellFormed w t C hCtime
      simpa only [hn] using hstampTime
    have hta : ta < t :=
      Protocol.HonestWeightMajority.acceptsAt_block_lt_of_stamp_before_core
        S adm hw hacc (Nat.succ_le_of_lt hi)
        (Proofs.Optimistic.publicTime_vote_time S s) hstamp
    exact ⟨i, ta, hacc, hta⟩


theorem honestHeadsAvailableBefore_of_namedPostHealingCone_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {s : Slot} {v : V} (hv : v ∈ rho.honest)
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor : Protocol.support_cutoff S.E s ≤ rho.horizon)
    {B : Block V}
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (voteDutyRead S rho v (s + 1)).st.core.toHealing.toFG) B)
    (hnames : NamedHonestVotesCone S rho s
      (fun X => Block.Preceq B X)) :
    ∀ X : Block V, Proofs.Optimistic.HonestHead S rho s X →
      X = Block.genesis ∨ AdmittedBefore S rho v X
        (Protocol.support_cutoff S.E s) := by
  intro X hhead
  by_cases hgen : X = Block.genesis
  · exact Or.inl hgen
  right
  obtain ⟨x, hx, hcommittee, ⟨C, hCX, hCrun⟩, hXemit⟩ := hhead
  obtain ⟨Y, hBY, hYrun, hYemit⟩ := hnames x hx hcommittee
  have hvoteEq : (⟨x, s, X.root⟩ : GoldfishVote V) =
      ⟨x, s, Y.erase.root⟩ :=
    Proofs.Optimistic.emits_gfVote_unique S
      adm.toNamedScheduleWellFormed hXemit hYemit rfl
  have hrootEq : X.root = Y.erase.root :=
    congrArg GoldfishVote.head hvoteEq
  have hCY : C = Y := by
    apply adm.toNamedRootCollisionFree.root_injective
      C Y hCrun hYrun C Y (Or.inl (Proofs.NamedAncestry.named_self C))
      (Or.inr (Proofs.NamedAncestry.named_self Y))
    rw [← Proofs.NamedWire.erase_root C, ← Proofs.NamedWire.erase_root Y, hCX]
    exact hrootEq
  have hBX : Block.Preceq B X := by
    simpa only [← hCY, hCX] using hBY
  have hmem : C.erase ∈ (voteDutyRead S rho x s).st.core.T :=
    Proofs.Optimistic.voteDutyHead_mem_of_emission_core S adm hx hCrun
      (u := ⟨x, s, X.root⟩) hXemit (by simpa only [hCX])
  obtain ⟨D, hDe, hgenD | hadmitD⟩ :=
    named_admittedBefore_of_voteDutyRead_mem_core S adm hx hmem
  · have hXgen : X = Block.genesis := by
      rw [← hCX, ← hDe, hgenD]
      rfl
    exact False.elim (hgen hXgen)
  · obtain ⟨j, ta, hacc, hta⟩ := hadmitD
    have hDpos : 0 < D.slot := by
      simpa only [Proofs.NamedWire.erase_slot] using
        Nat.zero_lt_of_lt (Protocol.parent_slot_lt_of_acceptsAt_block S hacc)
    have hFhist : BlockFinalizedBelowAtDeliveriesBefore S rho v D
        (Protocol.support_cutoff S.E s) := by
      intro q hq
      have hqVote := hq.trans (strict_filter_length_mono rho
        ((Proofs.Optimistic.support_cutoff_lt_view_freeze S.E s).le.trans
          (view_freeze_lt_vote_time_succ S.E s).le))
      have hroot' : Block.Preceq
          (Protocol.get_fg_root
            (rho.storeBeforeTime S v (Protocol.vote_time S.E (s + 1))).toHealing.toFG) B := by
        simp only [voteDutyRead, NamedActionReads.confirmationReadAt,
          NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
          Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
          Proofs.Optimistic.tickStore, Protocol.Store.toHealing, Run.storeBeforeTime, Protocol.Store.sg_pool]
        exact hroot
      have hFD := finalized_preceq_at_prefix_of_storeBeforeRoot_preceq
        S rho adm.toNamedScheduleWellFormed.sorted hroot' hqVote
      have hDX : D.erase = X := hDe.trans hCX
      have hFDX : Block.Preceq
          (rho.stateBefore S q v).st.F X :=
        Block.preceq_trans hFD hBX
      simpa only [hDX] using hFDX
    have hadmit := Protocol.block_admittedBefore_of_accepted_after_cutoff_core
      S adm hx hv hDpos hacc hta hpost
      (by rw [← Proofs.Optimistic.vote_time_add_delta]) hhor hFhist
    simpa only [hDe.trans hCX] using hadmit

/-- If every honest slot-`s` vote is for a descendant of `B` and `B` is a descendant of `v`'s FG
    root at its slot-`s + 1` vote duty, then every honest slot-`s` vote head is genesis or admitted
    by `v` before slot `s`'s support cutoff. -/
theorem honestHeadsAvailableBefore_of_namedPostHealingCone
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {s : Slot} {v : V} (hv : v ∈ rho.honest)
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor : Protocol.support_cutoff S.E s ≤ rho.horizon)
    {B : Block V}
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (voteDutyRead S rho v (s + 1)).st.core.toHealing.toFG) B)
    (hnames : NamedHonestVotesCone S rho s
      (fun X => Block.Preceq B X)) :
    ∀ X : Block V, Proofs.Optimistic.HonestHead S rho s X →
      X = Block.genesis ∨ AdmittedBefore S rho v X
        (Protocol.support_cutoff S.E s) :=
  honestHeadsAvailableBefore_of_namedPostHealingCone_core
    S adm.toNamedAdmissibleCore hv hpost hhor hroot hnames

/-- An honest slot-`s` vote head `H` is in `w`'s voter processed block tree at the slot-`s + 1` vote
    duty, when every honest slot-`s` vote is for a descendant of `C` and `C` is a descendant of
    `w`'s FG root there. -/
theorem honestHead_voterProcessed_at_nextDuty_of_postHealingCone
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {s : Slot} (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {C H : Block V}
    (hvotes : NamedHonestVotesCone S rho s
      (fun X => Block.Preceq C X))
    (hH : Proofs.Optimistic.HonestHead S rho s H)
    {w : V} (hw : w ∈ rho.honest)
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG) C) :
    H ∈ Protocol.voter_processed_block_tree S.E
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.s := by
  let duty := Proofs.Optimistic.voteDutyStore S rho w (s + 1)
  have hcutHor : Protocol.support_cutoff S.E s ≤ rho.horizon :=
    (support_cutoff_le_confirmation_time S.E s).trans hhor
  have hroot' : Block.Preceq
      (Protocol.get_fg_root
        (voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG) C := by
    simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore, Protocol.Store.toHealing, Run.storeBeforeTime]
      using hroot
  have havailable := honestHeadsAvailableBefore_of_namedPostHealingCone
    S adm hw hpost hcutHor hroot' hvotes
  have hslot : duty.toHealing.s = s + 1 := by
    simpa only [duty, Proofs.Optimistic.toHealing_slot] using
      Proofs.Optimistic.voteDutyStore_slot S rho w (s + 1)
  rcases havailable H hH with hgen | hadmit
  · subst H
    have hgenesis := Protocol.genesis_mem_and_stamp_storeBeforeTime S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed w
      (Protocol.vote_time S.E (s + 1)) (Protocol.view_freeze S.E s)
    simp only [Protocol.voter_processed_block_tree, Finset.mem_filter]
    rw [hslot, Nat.add_sub_cancel]
    exact ⟨by
      simpa only [duty, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore, Protocol.Store.toHealing] using hgenesis.1,
      Or.inl (by
        simpa only [duty, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
          Proofs.Optimistic.tickStore, Protocol.Store.toHealing] using hgenesis.2)⟩
  · have hvisible := Protocol.admittedBefore_mem_and_stamp_at S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hadmit
      (le_trans
        (le_of_lt (Proofs.Optimistic.support_cutoff_lt_view_freeze S.E s))
        (le_of_lt (view_freeze_lt_vote_time_succ S.E s)))
    have hstampCut : stampedBefore duty.toHealing.toFG.toSG.toGoldfishStore.timestamp_block
        (Protocol.support_cutoff S.E s) H = true := by
      simpa only [duty, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore, Protocol.Store.toHealing] using hvisible.2
    have hstampFreeze : stampedBefore duty.toHealing.toFG.toSG.toGoldfishStore.timestamp_block
        (Protocol.view_freeze S.E s) H = true := by
      rw [stampedBefore_eq_occurrenceBefore] at hstampCut ⊢
      exact occurrenceBefore_mono
        (le_of_lt (Proofs.Optimistic.support_cutoff_lt_view_freeze S.E s)) hstampCut
    simp only [Protocol.voter_processed_block_tree, Finset.mem_filter]
    rw [hslot, Nat.add_sub_cancel]
    exact ⟨by
      simpa only [duty, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore, Protocol.Store.toHealing] using hvisible.1,
      Or.inl hstampFreeze⟩

private theorem prepared_vote_view_valid_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (w : V) (s : Slot) :
    Protocol.VoteSetValid S.E
      ((voteDutyRead S rho w s).st.core.s - 1)
      (Protocol.voter_view S.E
        (voteDutyRead S rho w s).st.core.toHealing.toFG.toSG.toGoldfishStore
        (voteDutyRead S rho w s).st.core.s) := by
  let t := Protocol.vote_time S.E s
  let read := voteDutyRead S rho w s
  obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S
    adm.toNamedScheduleWellFormed t
  have hpool := Protocol.voteSetValid_pool_stateBefore S
    adm.toNamedScheduleWellFormed w n
    (read.st.core.s - 1)
  have hcarried : ∀ B ∈ (rho.stateBefore S n w).st.core.T,
      ∀ u ∈ B.gf_votes, u.val_index ∈ S.E.committee u.slot := by
    intro B hB u hu
    exact Protocol.carriedVote_committee_of_mem_T_core S adm w n hB u hu
  have hvalid := Protocol.voteSetValid_voter_view_of_carried
    (E := S.E) (st := (rho.stateBefore S n w).st.core)
    (s := read.st.core.s) hpool hcarried
  simp only [read, t, voteDutyRead, NamedActionReads.confirmationReadAt,
    NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock, hn, Protocol.Store.toHealing]
  exact hvalid


private theorem named_voter_head_runBlock
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w : V} (hw : w ∈ rho.honest) (s : Slot) :
    ∃ C : NamedBlock V, C.erase = voterHeadAt S rho w s ∧
      NamedRun.blockInRun S rho C := by
  let t := Protocol.vote_time S.E s
  let pre := NamedRun.stateBeforeTime S rho t w
  let read := NamedActionReads.confirmationReadFrom S pre t
  let st := read.st.core
  let gc := NamedProfile.gradeContract read.cache
  let tree := Protocol.voter_filtered_block_tree S.E st st.s
  let votes := Protocol.voter_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s
  let support := Protocol.voter_support_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s
  let H := Protocol.get_head_in_tree_with_layer gc S.E S.hc st.toHealing
    tree votes support (st.s - 1)
  have hinvPre : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg pre.st :=
    (Proofs.NamedRuntime.stateBeforeTime_invariants S rho t w).1
  have hinv : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg read.st := by
    simpa only [read, pre, NamedActionReads.confirmationReadFrom] using
      Proofs.NamedConfirmationMembership.invariant_clock S.E S.cfg pre.st t hinvPre
  have hroot : Protocol.get_fg_root st.toHealing.toFG ∈ st.T :=
    Proofs.NamedStoreRoots.fg_root_mem read.st hinv.1.2
  have hanchor : Protocol.get_sg_root_with gc S.E S.hc st.toHealing
      (S.hc.round_of st.s) ∈ st.T := by
    exact Proofs.NamedConfirmationMembership.runtime_anchor_mem read.cache
      S.E S.hc st.toHealing (S.hc.round_of st.s) hroot
  have htree : tree ⊆ st.T := by
    dsimp only [tree]
    rw [← Proofs.Optimistic.voter_candidate_tree_eq_protocol_voter_filtered_block_tree]
    intro D hD
    simp only [Proofs.Optimistic.voter_candidate_tree,
      Protocol.get_filtered_block_tree_from,
      Protocol.viable_tree, Protocol.finalized_descendants,
      Protocol.voter_processed_block_tree, Finset.mem_filter] at hD
    exact hD.1.1.1.1
  have hHmem : H ∈ st.T := by
    dsimp only [H]
    rw [Proofs.Optimistic.get_head_in_tree_split_with]
    exact Proofs.Records.ghost_mem_of _ _ hanchor htree
  have hHpre : H ∈ pre.st.core.T := by
    simpa only [read, st, NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using hHmem
  obtain ⟨C, hCe, hCrun⟩ :=
    Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hw t hHpre
  refine ⟨C, ?_, hCrun⟩
  simp only [voterHeadAt, H, tree, votes, support, read, st,
    NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock, Protocol.Store.toHealing]
  exact hCe

theorem named_voter_head_emits
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w : V} (hw : w ∈ rho.honest) {s : Slot}
    (hs : 0 < s) (hcommittee : w ∈ S.E.committee s)
    (hhor : Protocol.vote_time S.E s ≤ rho.horizon) :
    ∃ C : NamedBlock V, C.erase = voterHeadAt S rho w s ∧
      NamedRun.blockInRun S rho C ∧
      NamedRun.emits S rho w
        (Object.gfVote ⟨w, s, C.erase.root⟩)
        (Protocol.vote_time S.E s) := by
  obtain ⟨C, hChead, hCrun⟩ := named_voter_head_runBlock S adm hw s
  let read := voteDutyRead S rho w s
  have hslot : read.st.core.s = s := Proofs.Optimistic.voteDutyRead_slot S rho w s
  have hcommittee' : (S.node w).val_index ∈ S.E.committee read.st.core.s := by
    rw [S.node_val_index, hslot]
    exact hcommittee
  have hout :
      (Protocol.NamedDuties.goldfish_vote_with
        (NamedProfile.gradeContract read.cache) S.E S.hc (S.node w) read.st).2 =
        some ⟨(S.node w).val_index, read.st.core.s,
          (voterHeadAt S rho w s).root⟩ := by
    simp only [Protocol.NamedDuties.goldfish_vote_with,
      Protocol.goldfish_vote_with]
    rw [if_pos]
    · rfl
    · rw [S.node_val_index, hslot]
      exact hcommittee
  have ho : Object.gfVote
      ⟨(S.node w).val_index, read.st.core.s, (voterHeadAt S rho w s).root⟩ ∈
      (on_tick_emit S w
        (rho.stateBeforeTime S (Protocol.vote_time S.E s) w)
        (Protocol.vote_time S.E s)).2 := by
    exact Proofs.Optimistic.on_tick_emit_vote_mem S w
      (rho.stateBeforeTime S (Protocol.vote_time S.E s) w) s hs hout
  have hem := Proofs.Optimistic.emits_of_on_tick_emit S
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hw
    (Proofs.Optimistic.publicTime_vote_time S s)
    (Proofs.Optimistic.vote_time_nonneg S.E s) hhor ho
  refine ⟨C, hChead, hCrun, ?_⟩
  simpa only [S.node_val_index, hslot, hChead] using hem

/-! ## The cone path -/

/-- If every honest slot-`s` vote is for a descendant of `C`, every block after `w`'s slot-`s + 1`
    vote anchor up to `C` is in the vote tree and passes the Goldfish eligibility test. -/
theorem goldfishCone_pathEligible_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {s : Slot} (hs : 0 < s)
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {C : Block V}
    (hnames : NamedHonestVotesCone S rho s
      (fun X => Block.Preceq C X))
    {w : V} (hw : w ∈ rho.honest)
    (hinputs : GoldfishConeVoteInputs S rho s C w) :
    let read := voteDutyRead S rho w (s + 1)
    let st := read.st.core
    let votes := Protocol.voter_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s
    let support := Protocol.voter_support_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s
    let tree := voterCandidateTreeAt S rho w (s + 1)
    Proofs.Optimistic.ConeSupport S.E st.T votes support votes (st.s - 1)
        rho.honest (fun X => Block.Preceq C X) ∧
      Protocol.voters_count S.E votes (st.s - 1) <
        2 * (Protocol.goldfishSupporters S.E st.T votes support (st.s - 1) C).card ∧
      ∀ D : Block V,
        Block.Preceq (voterAnchorAt S rho w (s + 1)) D →
        D ≠ voterAnchorAt S rho w (s + 1) →
        Block.Preceq D C →
        D ∈ tree ∧
          ((st.σ D.parent).h < st.h_max - 1 ∨
            Protocol.voters_count S.E votes (st.s - 1) <
              2 * Protocol.goldfish_score S.E st.T votes support
                (st.s - 1) D) ∧
          Protocol.goldfish_eligible S.E st.σ st.h_max st.T st.s
            votes support (st.s - 1) D = true := by
  let read := voteDutyRead S rho w (s + 1)
  let st := read.st.core
  let votes := Protocol.voter_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s
  let support := Protocol.voter_support_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s
  let tree := voterCandidateTreeAt S rho w (s + 1)
  have hcutHor : Protocol.support_cutoff S.E s ≤ rho.horizon :=
    (support_cutoff_le_confirmation_time S.E s).trans hhor
  have hroot : Block.Preceq
      (Protocol.get_fg_root st.toHealing.toFG) C := by
    exact hinputs.root
  have havailable := honestHeadsAvailableBefore_of_namedPostHealingCone_core
    S adm hw hpost hcutHor hroot hnames
  have hresolve0 := Protocol.headsResolveIn_storeBeforeTime_of_availableBefore_at_core
    S adm hw s (Proofs.Optimistic.support_cutoff_le_vote_time_succ S.E s) havailable
  have hresolve : Proofs.Optimistic.HeadsResolveIn S rho s st.T st.timestamp_block := by
    simpa only [st, read, voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock, Run.storeBeforeTime] using
      hresolve0
  have hbase := Protocol.canonicalSuffixConeSupportVoterView_core
    S adm hcom hs hpost hcutHor hnames hw
      (Proofs.Optimistic.support_cutoff_le_vote_time_succ S.E s)
      (gst := st.toHealing.toFG.toSG.toGoldfishStore) (by rfl) (by rfl) (by rfl)
      (hresolve.of_eq rfl rfl)
  have hslot : st.s = s + 1 := by
    simpa only [st, read] using Proofs.Optimistic.voteDutyRead_slot S rho w (s + 1)
  have hvalid := prepared_vote_view_valid_core S adm w (s + 1)
  have hcone : Proofs.Optimistic.ConeSupport S.E st.T votes support votes (st.s - 1)
      rho.honest (fun X => Block.Preceq C X) := by
    simp only [st, read, votes, support, hslot, Protocol.Store.toHealing]
    exact hbase
  have hmajority : Protocol.voters_count S.E votes (st.s - 1) <
      2 * (Protocol.goldfishSupporters S.E st.T votes support (st.s - 1) C).card :=
    Protocol.supporterMajority_of_cone S.E hcone hvalid
  refine ⟨hcone, hmajority, ?_⟩
  intro D hAD hDne hDC
  have hDmem : D ∈ tree := by
    by_cases hEq : D = C
    · subst D
      exact hinputs.candidate
    · exact hinputs.path D hAD hDne hDC hEq
  have hDmajority : Protocol.voters_count S.E votes (st.s - 1) <
      2 * Protocol.goldfish_score S.E st.T votes support (st.s - 1) D :=
    Protocol.eligible_of_supporter_majority hmajority hDC
  refine ⟨hDmem, Or.inr hDmajority, ?_⟩
  rw [Proofs.Optimistic.goldfish_eligible_iff]
  exact Or.inr (Or.inl hDmajority)

/-- If every honest slot-`s` vote is for a descendant of `C`, every block after `w`'s slot-`s + 1`
    vote anchor up to `C` is in the vote tree and passes the Goldfish eligibility test. -/
theorem goldfishCone_pathEligible
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    {s : Slot} (hs : 0 < s)
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {C : Block V}
    (hnames : NamedHonestVotesCone S rho s
      (fun X => Block.Preceq C X))
    {w : V} (hw : w ∈ rho.honest)
    (hinputs : GoldfishConeVoteInputs S rho s C w) :
    let read := voteDutyRead S rho w (s + 1)
    let st := read.st.core
    let votes := Protocol.voter_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s
    let support := Protocol.voter_support_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s
    let tree := voterCandidateTreeAt S rho w (s + 1)
    Proofs.Optimistic.ConeSupport S.E st.T votes support votes (st.s - 1)
        rho.honest (fun X => Block.Preceq C X) ∧
      Protocol.voters_count S.E votes (st.s - 1) <
        2 * (Protocol.goldfishSupporters S.E st.T votes support (st.s - 1) C).card ∧
      ∀ D : Block V,
        Block.Preceq (voterAnchorAt S rho w (s + 1)) D →
        D ≠ voterAnchorAt S rho w (s + 1) →
        Block.Preceq D C →
        D ∈ tree ∧
          ((st.σ D.parent).h < st.h_max - 1 ∨
            Protocol.voters_count S.E votes (st.s - 1) <
              2 * Protocol.goldfish_score S.E st.T votes support
                (st.s - 1) D) ∧
          Protocol.goldfish_eligible S.E st.σ st.h_max st.T st.s
            votes support (st.s - 1) D = true :=
  goldfishCone_pathEligible_core S adm.toNamedAdmissibleCore hcom hs hpost hhor
    hnames hw hinputs

/-- If every honest slot-`s` vote is for a descendant of `C`, then under `GoldfishConeVoteInputs`
    the head of honest `w`'s slot-`s + 1` vote is a descendant of `C`. -/
theorem goldfishCone_step
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    {s : Slot} (hs : 0 < s)
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {C : Block V}
    (hnames : NamedHonestVotesCone S rho s
      (fun X => Block.Preceq C X))
    {w : V} (hw : w ∈ rho.honest)
    (hinputs : GoldfishConeVoteInputs S rho s C w) :
    Block.Preceq C (voterHeadAt S rho w (s + 1)) := by
  let read := voteDutyRead S rho w (s + 1)
  let st := read.st.core
  let votes := Protocol.voter_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s
  let support := Protocol.voter_support_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s
  have hwalk := goldfishCone_pathEligible S adm hcom hs hpost hhor
    hnames hw hinputs
  have hslot : st.s = s + 1 := by
    simpa only [st, read] using Proofs.Optimistic.voteDutyRead_slot S rho w (s + 1)
  have hhead := Protocol.goldfish_fork_choice_captures_supporter_majority
    S.E st.σ st.h_max st.T (voterCandidateTreeAt S rho w (s + 1)) st.s
      votes support (st.s - 1) (Proofs.Optimistic.ConeSupport.sub hwalk.1)
      hwalk.2.1 hinputs.anchor
      (fun _ D hAD hDne hDC => (hwalk.2.2 D hAD hDne hDC).1)
  change Block.Preceq C
    (Protocol.get_head_in_tree_with_layer
      (NamedProfile.gradeContract read.cache) S.E S.hc st.toHealing
      (voterCandidateTreeAt S rho w (s + 1)) votes support (st.s - 1))
  simp only [get_head_in_tree_eq_voterHeadAt_of_anchor, read, st]
  exact hhead

/-- If every honest slot-`s` vote is for a descendant of `C`, then under `GoldfishConeVoteInputs'`,
    which also admits a `C` that is an ancestor of the FG root, the head of honest `w`'s
    slot-`s + 1` vote is a descendant of `C`. -/
theorem goldfishCone_step'
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    {s : Slot} (hs : 0 < s)
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {C : Block V}
    (hnames : NamedHonestVotesCone S rho s
      (fun X => Block.Preceq C X))
    {w : V} (hw : w ∈ rho.honest)
    (hinputs : GoldfishConeVoteInputs' S rho s C w) :
    Block.Preceq C (voterHeadAt S rho w (s + 1)) := by
  rcases hinputs.rootSide with hrootBelow | hbelowRoot
  · exact goldfishCone_step S adm hcom hs hpost hhor hnames hw
      { candidate := hrootBelow.2.1
        root := hrootBelow.1
        anchor := hinputs.anchor
        path := hrootBelow.2.2 }
  · let read := voteDutyRead S rho w (s + 1)
    let st := read.st.core
    let votes := Protocol.voter_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s
    let support := Protocol.voter_support_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s
    have hhead := get_head_in_tree_with_of_preceq_fgRoot
      read.cache S.E S.hc st.toHealing (voterCandidateTreeAt S rho w (s + 1))
      C votes support (st.s - 1) hbelowRoot
    change Block.Preceq C
      (Protocol.get_head_in_tree_with_layer
        (NamedProfile.gradeContract read.cache) S.E S.hc st.toHealing
        (voterCandidateTreeAt S rho w (s + 1)) votes support (st.s - 1))
    simp only [get_head_in_tree_eq_voterHeadAt_of_anchor, read, st]
    exact hhead


#print axioms goldfishCone_pathEligible
#print axioms honestHeadsAvailableBefore_of_namedPostHealingCone
#print axioms named_voter_head_emits
#print axioms honestHead_voterProcessed_at_nextDuty_of_postHealingCone

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
