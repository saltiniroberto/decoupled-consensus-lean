module
public import Proofs.Vocabulary.Execution.TimeoutDelay
public import Proofs.Vocabulary.ModelProperties.NamedNode_initial
public import Proofs.Vocabulary.Protocol.ValidatorClient.RecordTargetHistory
public import Proofs.Vocabulary.Generic.PostGSTCarrierAdmissionCore
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.GradeDelivery
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.GradeBootstrapCore
public import Proofs.Vocabulary.Protocol.ValidatorClient.RecoveryTimeout
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.FinalityFilterRetention
public import Proofs.Vocabulary.Generic.EvaluationStore
public import Proofs.Vocabulary.Protocol.ForkChoice.Views.ProposalCore
public import Proofs.Vocabulary.Objects.PostGSTSync
public import Proofs.Vocabulary.Protocol.ValidatorClient.RecordClean
public import Proofs.Vocabulary.Protocol.Handlers.JustificationBound
import Proofs.Vocabulary.Execution.BridgesCore
import Proofs.Vocabulary.Protocol.ChainState.ProgressQuorumCore
import Proofs.Vocabulary.Protocol.Handlers.HMaxCore
import Proofs.Vocabulary.Protocol.Schedule.Action
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Participation along a named chain at one height

Helpers on how matching rows enter `progress` and `target_participation` along a named chain whose
height does not change.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Protocol (ChainState HeightConfig)
open Protocol (Record height_pair own_lock record_attestation)
open Internal
open Execution
open Internal.HealingSurface
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}


omit [Fintype V] in
private theorem named_progress_subset_foldl
    (rows : List (NamedAttestation V))
    (sigma : Protocol.ChainState V) :
    sigma.progress ⊆
      (rows.foldl (Protocol.process_attestation_with
        (Protocol.TimeoutBinding.targeted V)) sigma).progress := by
  induction rows generalizing sigma with
  | nil => exact Finset.Subset.refl _
  | cons row rows ih =>
      rw [List.foldl_cons]
      apply Finset.Subset.trans _ (ih _)
      intro signer hsigner
      rw [(TargetedTimeoutBinding.process_height_fields sigma row).1]
      split_ifs
      · exact Finset.mem_insert_of_mem hsigner
      · exact hsigner

omit [Fintype V] in
private theorem named_mem_progress_foldl_of_matching
    {a : NamedAttestation V} :
    ∀ (rows : List (NamedAttestation V))
      (sigma : Protocol.ChainState V),
      a ∈ rows →
      a.height_pair.matchesEntry sigma.h sigma.T_h.root = true →
      a.val_index ∈
        (rows.foldl (Protocol.process_attestation_with
          (Protocol.TimeoutBinding.targeted V)) sigma).progress := by
  intro rows
  induction rows with
  | nil => intro sigma ha _; simp at ha
  | cons row rows ih =>
      intro sigma ha hmatch
      rw [List.foldl_cons]
      rcases List.mem_cons.mp ha with rfl | htail
      · apply named_progress_subset_foldl
        rw [(TargetedTimeoutBinding.process_height_fields sigma a).1,
          if_pos hmatch]
        exact Finset.mem_insert_self _ _
      · apply ih _ htail
        have hfields := TimeoutBindingDefaults.process_context_fields
          (Protocol.TimeoutBinding.targeted V) sigma row
        rw [hfields.2.1, hfields.2.2.1]
        exact hmatch


private theorem namedTransition_eq_afterFin_of_height_eq
    (E : Env V) (cfg : HeightConfig)
    (st : ChainState V) (B : NamedBlock V)
    (hh : (Protocol.named_transition E cfg st B).h = st.h) :
    Protocol.named_transition E cfg st B =
      Protocol.afterFin E (Protocol.fold_rows
        (Protocol.TimeoutBinding.targeted V)
        st B.erase B.attestations) := by
  unfold Protocol.named_transition
    Protocol.transition_rows at hh ⊢
  rw [Protocol.process_height_events_eq] at hh ⊢
  split_ifs at hh ⊢ with ht hp
  · have hfold := NamedDerivationGeometry.fold_context_fields
      (Protocol.TimeoutBinding.targeted V) B.attestations
      ({st with s := B.erase.slot})
    rw [Protocol.advance_height_h, Protocol.afterFin_h,
      show (Protocol.fold_rows
        (Protocol.TimeoutBinding.targeted V)
        st B.erase B.attestations).h = st.h by exact hfold.2.1] at hh
    exact False.elim (Nat.succ_ne_self _ hh)
  · have hfold := NamedDerivationGeometry.fold_context_fields
      (Protocol.TimeoutBinding.targeted V) B.attestations
      ({st with s := B.erase.slot})
    rw [Protocol.advance_height_h, Protocol.afterFin_h,
      show (Protocol.fold_rows
        (Protocol.TimeoutBinding.targeted V)
        st B.erase B.attestations).h = st.h by exact hfold.2.1] at hh
    exact False.elim (Nat.succ_ne_self _ hh)
  · rfl

private theorem namedProgress_subset_node_of_same_height
    (E : Env V) (cfg : HeightConfig)
    (p : NamedBlock V) (s : Slot) (root : BlockId)
    (votes support : List (GoldfishVote V))
    (rows : List (NamedAttestation V)) (proposer : V)
    (hh : (Protocol.derive_named E cfg
      (.node p s root votes support rows proposer)).h =
        (Protocol.derive_named E cfg p).h) :
    (Protocol.derive_named E cfg p).progress ⊆
      (Protocol.derive_named E cfg
        (.node p s root votes support rows proposer)).progress := by
  have hstay := namedTransition_eq_afterFin_of_height_eq E cfg
    (Protocol.derive_named E cfg p)
    (.node p s root votes support rows proposer) hh
  rw [Protocol.derive_named, hstay, Protocol.afterFin_progress]
  change (Protocol.derive_named E cfg p).progress ⊆
    (rows.foldl (Protocol.process_attestation_with
      (Protocol.TimeoutBinding.targeted V))
      {Protocol.derive_named E cfg p with s := s}).progress
  simpa only using named_progress_subset_foldl rows
    ({Protocol.derive_named E cfg p with s := s})

private theorem namedPair_mem_progress_node_of_same_height
    (E : Env V) (cfg : HeightConfig)
    (p : NamedBlock V) (s : Slot) (root : BlockId)
    (votes support : List (GoldfishVote V))
    (rows : List (NamedAttestation V)) (proposer : V)
    {a : NamedAttestation V} (ha : a ∈ rows)
    (hpair : a.height_pair = .vote
          (Protocol.derive_named E cfg p).h
          (Protocol.derive_named E cfg p).T_h.root false ∨
        a.height_pair = .vote
          (Protocol.derive_named E cfg p).h
          (Protocol.derive_named E cfg p).T_h.root true)
    (hh : (Protocol.derive_named E cfg
      (.node p s root votes support rows proposer)).h =
        (Protocol.derive_named E cfg p).h) :
    a.val_index ∈ (Protocol.derive_named E cfg
      (.node p s root votes support rows proposer)).progress := by
  have hstay := namedTransition_eq_afterFin_of_height_eq E cfg
    (Protocol.derive_named E cfg p)
    (.node p s root votes support rows proposer) hh
  rw [Protocol.derive_named, hstay, Protocol.afterFin_progress]
  change a.val_index ∈
    (rows.foldl (Protocol.process_attestation_with
      (Protocol.TimeoutBinding.targeted V))
      {Protocol.derive_named E cfg p with s := s}).progress
  apply named_mem_progress_foldl_of_matching rows _ ha
  rcases hpair with htarget | htimeout
  · simpa [htarget, NamedHeightPair.matchesEntry]
  · simpa [htimeout, NamedHeightPair.matchesEntry]

omit [Fintype V] in
private theorem namedTarget_subset_foldl
    (rows : List (NamedAttestation V)) (sigma : ChainState V) :
    sigma.target_participation ⊆
      (rows.foldl (Protocol.process_attestation_with
        (Protocol.TimeoutBinding.targeted V))
        sigma).target_participation := by
  induction rows generalizing sigma with
  | nil => exact Finset.Subset.refl _
  | cons row rows ih =>
      rw [List.foldl_cons]
      apply Finset.Subset.trans _ (ih _)
      rw [(TargetedTimeoutBinding.process_height_fields sigma row).2]
      split_ifs
      · exact Finset.subset_insert _ _
      · exact Finset.Subset.refl _

omit [Fintype V] in
private theorem namedTarget_mem_foldl {a : NamedAttestation V} :
    ∀ (rows : List (NamedAttestation V)) (sigma : ChainState V),
      a ∈ rows →
      a.height_pair = .vote sigma.h sigma.T_h.root false →
      a.val_index ∈
        (rows.foldl (Protocol.process_attestation_with
          (Protocol.TimeoutBinding.targeted V))
          sigma).target_participation := by
  intro rows
  induction rows with
  | nil => intro sigma ha _; simp at ha
  | cons row rows ih =>
      intro sigma ha hpair
      rw [List.foldl_cons]
      rcases List.mem_cons.mp ha with rfl | htail
      · apply namedTarget_subset_foldl rows
        rw [(TargetedTimeoutBinding.process_height_fields sigma a).2]
        have htest :
            (a.height_pair.matchesEntry sigma.h sigma.T_h.root &&
              a.height_pair.properTarget) = true := by
          rw [hpair]
          simp [NamedHeightPair.matchesEntry,
            NamedHeightPair.properTarget]
        rw [if_pos htest]
        exact Finset.mem_insert_self _ _
      · apply ih _ htail
        have hfields := TimeoutBindingDefaults.process_context_fields
          (Protocol.TimeoutBinding.targeted V) sigma row
        rw [hfields.2.1, hfields.2.2.1]
        exact hpair

private theorem namedTarget_subset_node_of_same_height
    (E : Env V) (cfg : HeightConfig)
    (p : NamedBlock V) (s : Slot) (root : BlockId)
    (votes support : List (GoldfishVote V))
    (rows : List (NamedAttestation V)) (proposer : V)
    (hh : (Protocol.derive_named E cfg
      (.node p s root votes support rows proposer)).h =
        (Protocol.derive_named E cfg p).h) :
    (Protocol.derive_named E cfg p).target_participation ⊆
      (Protocol.derive_named E cfg
        (.node p s root votes support rows proposer)).target_participation := by
  have hstay := namedTransition_eq_afterFin_of_height_eq E cfg
    (Protocol.derive_named E cfg p)
    (.node p s root votes support rows proposer) hh
  rw [Protocol.derive_named, hstay,
    Protocol.afterFin_target_participation]
  change (Protocol.derive_named E cfg p).target_participation ⊆
    (rows.foldl (Protocol.process_attestation_with
      (Protocol.TimeoutBinding.targeted V))
      {Protocol.derive_named E cfg p with s := s}).target_participation
  simpa only using namedTarget_subset_foldl rows
    ({Protocol.derive_named E cfg p with s := s})

private theorem namedTarget_mem_node_of_same_height
    (E : Env V) (cfg : HeightConfig)
    (p : NamedBlock V) (s : Slot) (root : BlockId)
    (votes support : List (GoldfishVote V))
    (rows : List (NamedAttestation V)) (proposer : V)
    {a : NamedAttestation V} (ha : a ∈ rows)
    (hpair : a.height_pair = .vote
      (Protocol.derive_named E cfg p).h
      (Protocol.derive_named E cfg p).T_h.root false)
    (hh : (Protocol.derive_named E cfg
      (.node p s root votes support rows proposer)).h =
        (Protocol.derive_named E cfg p).h) :
    a.val_index ∈ (Protocol.derive_named E cfg
      (.node p s root votes support rows proposer)).target_participation := by
  have hstay := namedTransition_eq_afterFin_of_height_eq E cfg
    (Protocol.derive_named E cfg p)
    (.node p s root votes support rows proposer) hh
  rw [Protocol.derive_named, hstay,
    Protocol.afterFin_target_participation]
  change a.val_index ∈
    (rows.foldl (Protocol.process_attestation_with
      (Protocol.TimeoutBinding.targeted V))
      {Protocol.derive_named E cfg p with s := s}).target_participation
  apply namedTarget_mem_foldl rows _ ha
  simpa only using hpair

private theorem namedPair_mem_progress_of_suffix_same_height
    (E : Env V) (cfg : HeightConfig)
    {C P : NamedBlock V} {a : NamedAttestation V}
    (hCP : NamedBlock.Preceq C P)
    (haP : a ∈ Protocol.named_chain_attestations P)
    (haC : a ∉ Protocol.named_chain_attestations C)
    (hh : (Protocol.derive_named E cfg P).h =
      (Protocol.derive_named E cfg C).h)
    (hpair : a.height_pair = .vote
          (Protocol.derive_named E cfg C).h
          (Protocol.derive_named E cfg C).T_h.root false ∨
        a.height_pair = .vote
          (Protocol.derive_named E cfg C).h
          (Protocol.derive_named E cfg C).T_h.root true) :
    a.val_index ∈ (Protocol.derive_named E cfg P).progress := by
  induction P with
  | genesis =>
      simp [Protocol.named_chain_attestations] at haP
  | node p s root votes support rows proposer ih =>
      simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hCP
      rcases hCP with rfl | hCp
      · exact False.elim (haC haP)
      · have hparentNode : NamedBlock.Preceq p
            (.node p s root votes support rows proposer) :=
          Proofs.NamedAncestry.named_extend s root votes support rows proposer
            (Proofs.NamedAncestry.named_self p)
        have hpHeight : (Protocol.derive_named E cfg p).h =
            (Protocol.derive_named E cfg C).h := by
          apply Nat.le_antisymm
          · exact (Proofs.NamedEntryHeight.derive_height_mono E cfg
              hparentNode).trans_eq hh
          · exact Proofs.NamedEntryHeight.derive_height_mono E cfg hCp
        have hnodeHeight : (Protocol.derive_named E cfg
            (.node p s root votes support rows proposer)).h =
              (Protocol.derive_named E cfg p).h :=
          hh.trans hpHeight.symm
        have htargetEq : (Protocol.derive_named E cfg p).T_h =
            (Protocol.derive_named E cfg C).T_h :=
          (Proofs.NamedEntryHeight.entry_eq_on_plateau
            E cfg hCp hpHeight.symm).symm
        have hpairParent : a.height_pair = .vote
              (Protocol.derive_named E cfg p).h
              (Protocol.derive_named E cfg p).T_h.root false ∨
            a.height_pair = .vote
              (Protocol.derive_named E cfg p).h
              (Protocol.derive_named E cfg p).T_h.root true := by
          simpa only [hpHeight, htargetEq] using hpair
        simp only [Protocol.named_chain_attestations,
          Finset.mem_union] at haP
        rcases haP with haParent | haOwn
        · exact namedProgress_subset_node_of_same_height
            E cfg p s root votes support rows proposer hnodeHeight
              (ih hCp haParent hpHeight)
        · exact namedPair_mem_progress_node_of_same_height
            E cfg p s root votes support rows proposer
              (List.mem_toFinset.mp haOwn) hpairParent hnodeHeight

private theorem namedTarget_mem_of_suffix_same_height
    (E : Env V) (cfg : HeightConfig)
    {C P : NamedBlock V} {a : NamedAttestation V}
    (hCP : NamedBlock.Preceq C P)
    (haP : a ∈ Protocol.named_chain_attestations P)
    (haC : a ∉ Protocol.named_chain_attestations C)
    (hh : (Protocol.derive_named E cfg P).h =
      (Protocol.derive_named E cfg C).h)
    (hpair : a.height_pair = .vote
      (Protocol.derive_named E cfg C).h
      (Protocol.derive_named E cfg C).T_h.root false) :
    a.val_index ∈
      (Protocol.derive_named E cfg P).target_participation := by
  induction P with
  | genesis =>
      simp [Protocol.named_chain_attestations] at haP
  | node p s root votes support rows proposer ih =>
      simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hCP
      rcases hCP with rfl | hCp
      · exact False.elim (haC haP)
      · have hparentNode : NamedBlock.Preceq p
            (.node p s root votes support rows proposer) :=
          Proofs.NamedAncestry.named_extend s root votes support rows proposer
            (Proofs.NamedAncestry.named_self p)
        have hpHeight : (Protocol.derive_named E cfg p).h =
            (Protocol.derive_named E cfg C).h := by
          apply Nat.le_antisymm
          · exact (Proofs.NamedEntryHeight.derive_height_mono E cfg
              hparentNode).trans_eq hh
          · exact Proofs.NamedEntryHeight.derive_height_mono E cfg hCp
        have hnodeHeight : (Protocol.derive_named E cfg
            (.node p s root votes support rows proposer)).h =
              (Protocol.derive_named E cfg p).h :=
          hh.trans hpHeight.symm
        have htargetEq : (Protocol.derive_named E cfg p).T_h =
            (Protocol.derive_named E cfg C).T_h :=
          (Proofs.NamedEntryHeight.entry_eq_on_plateau
            E cfg hCp hpHeight.symm).symm
        have hpairParent : a.height_pair = .vote
            (Protocol.derive_named E cfg p).h
            (Protocol.derive_named E cfg p).T_h.root false := by
          simpa only [hpHeight, htargetEq] using hpair
        simp only [Protocol.named_chain_attestations,
          Finset.mem_union] at haP
        rcases haP with haParent | haOwn
        · exact namedTarget_subset_node_of_same_height
            E cfg p s root votes support rows proposer hnodeHeight
              (ih hCp haParent hpHeight)
        · exact namedTarget_mem_node_of_same_height
            E cfg p s root votes support rows proposer
              (List.mem_toFinset.mp haOwn) hpairParent hnodeHeight

omit [Fintype V] in
private theorem chainRows_iff_named_chain
    {B : NamedBlock V} {a : NamedAttestation V} :
    a ∈ Protocol.NamedProposalRows.chainRows B ↔
      a ∈ Protocol.named_chain_attestations B := by
  induction B with
  | genesis =>
      simp [Protocol.NamedProposalRows.chainRows,
        Protocol.named_chain_attestations]
  | node p s root votes support rows proposer ih =>
      simp only [Protocol.NamedProposalRows.chainRows,
        Protocol.named_chain_attestations, List.mem_append,
        Finset.mem_union, List.mem_toFinset, ih, or_comm]

omit [Fintype V] in
private theorem namedChain_row_ancestor
    {B : NamedBlock V} {a : NamedAttestation V}
    (ha : a ∈ Protocol.named_chain_attestations B) :
    ∃ A : NamedBlock V, NamedBlock.Preceq A B ∧ a ∈ A.attestations := by
  induction B with
  | genesis => simp [Protocol.named_chain_attestations] at ha
  | node p s root votes support rows proposer ih =>
      simp only [Protocol.named_chain_attestations,
        Finset.mem_union] at ha
      rcases ha with haParent | haOwn
      · obtain ⟨A, hA, hrow⟩ := ih haParent
        exact ⟨A, Proofs.NamedAncestry.named_extend
          s root votes support rows proposer hA, hrow⟩
      · exact ⟨.node p s root votes support rows proposer,
          Proofs.NamedAncestry.named_self _, List.mem_toFinset.mp haOwn⟩


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
