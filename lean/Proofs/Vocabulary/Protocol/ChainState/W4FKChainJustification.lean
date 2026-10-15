module
public import Proofs.Vocabulary.Protocol.ChainState.RecurringFinality
public import Proofs.Vocabulary.Internal.Definitions.NamedDerived
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.GradeBootstrapCore
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.ReaderLocalCone
public import Proofs.Vocabulary.Protocol.ForkChoice.Views.ProposalCore
public import Proofs.Vocabulary.Protocol.ChainState.EntryHeight
public import Proofs.Vocabulary.Protocol.ChainState.TargetedTimeoutBinding
import Proofs.Vocabulary.Protocol.ChainState.Certificates
import Proofs.Vocabulary.Protocol.ChainState.NjGap
import Proofs.Vocabulary.Protocol.Schedule.Action
import Mathlib.Data.Rat.Floor

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation


namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol
open Protocol (ChainState HeightConfig derive_named fold_rows
  process_attestation_with TimeoutBinding)

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Target participation through the targeted row fold -/

omit [Fintype V] in
private theorem w4fkFold_targetParticipation_subset
    (rows : List (NamedAttestation V)) (sigma : ChainState V) :
    sigma.target_participation ⊆
      (rows.foldl (process_attestation_with (TimeoutBinding.targeted V))
        sigma).target_participation := by
  induction rows generalizing sigma with
  | nil => exact Finset.Subset.refl _
  | cons row rows ih =>
      rw [List.foldl_cons]
      refine Finset.Subset.trans ?_ (ih _)
      intro i hi
      rw [(TargetedTimeoutBinding.process_height_fields sigma row).2]
      split_ifs
      · exact Finset.mem_insert_of_mem hi
      · exact hi

omit [Fintype V] in
private theorem w4fkFold_mem_targetParticipation_of_target
    {a : NamedAttestation V} :
    ∀ (rows : List (NamedAttestation V)) (sigma : ChainState V),
      a ∈ rows →
      a.height_pair = .vote sigma.h sigma.T_h.root false →
      a.val_index ∈
        (rows.foldl (process_attestation_with (TimeoutBinding.targeted V))
          sigma).target_participation := by
  intro rows
  induction rows with
  | nil => intro sigma ha _; simp at ha
  | cons row rows ih =>
      intro sigma ha hpair
      rw [List.foldl_cons]
      rcases List.mem_cons.mp ha with rfl | htail
      · apply w4fkFold_targetParticipation_subset
        rw [(TargetedTimeoutBinding.process_height_fields sigma a).2]
        simp [hpair, NamedHeightPair.matchesEntry, NamedHeightPair.properTarget]
      · apply ih _ htail
        have hfields := TimeoutBindingDefaults.process_context_fields
          (TimeoutBinding.targeted V) sigma row
        rw [hfields.2.1, hfields.2.2.1]
        exact hpair

omit [Fintype V] in
private theorem w4fkFold_nj
    (rows : List (NamedAttestation V)) (sigma : ChainState V) :
    (rows.foldl (process_attestation_with (TimeoutBinding.targeted V))
      sigma).nj = sigma.nj := by
  induction rows generalizing sigma with
  | nil => rfl
  | cons row rows ih =>
      rw [List.foldl_cons, ih]
      exact NjGap.process_attestation_nj sigma _

omit [Fintype V] in
private theorem w4fkRows_h (sigma : ChainState V) (geometry : Block V)
    (rows : List (NamedAttestation V)) :
    (fold_rows (TimeoutBinding.targeted V) sigma geometry rows).h = sigma.h := by
  unfold fold_rows
  exact (NamedDerivationGeometry.fold_context_fields
    (TimeoutBinding.targeted V) rows { sigma with s := geometry.slot }).2.1

omit [Fintype V] in
private theorem w4fkRows_T_h (sigma : ChainState V) (geometry : Block V)
    (rows : List (NamedAttestation V)) :
    (fold_rows (TimeoutBinding.targeted V) sigma geometry rows).T_h = sigma.T_h := by
  unfold fold_rows
  exact (NamedDerivationGeometry.fold_context_fields
    (TimeoutBinding.targeted V) rows { sigma with s := geometry.slot }).2.2.1

omit [Fintype V] in
private theorem w4fkRows_nj (sigma : ChainState V) (geometry : Block V)
    (rows : List (NamedAttestation V)) :
    (fold_rows (TimeoutBinding.targeted V) sigma geometry rows).nj = sigma.nj := by
  unfold fold_rows
  exact w4fkFold_nj rows { sigma with s := geometry.slot }

omit [Fintype V] in
private theorem w4fkRows_targetParticipation (sigma : ChainState V)
    (geometry : Block V) (rows : List (NamedAttestation V)) :
    (fold_rows (TimeoutBinding.targeted V) sigma geometry rows).target_participation =
      (rows.foldl (process_attestation_with (TimeoutBinding.targeted V))
        { sigma with s := geometry.slot }).target_participation := rfl

/-! ## Named target coverage and the justification write -/

/-- Some quorum's members are each in `sigma.target_participation` or have an attestation of `B`
    with height pair `.vote sigma.h sigma.T_h.root false`. -/
def NamedTargetQuorumCoveredByChild
    (E : Env V) (sigma : ChainState V) (B : NamedBlock V) : Prop :=
  ∃ Q : Finset V, E.electorate.IsQuorum Q ∧
    ∀ i ∈ Q,
      i ∈ sigma.target_participation ∨
      ∃ a ∈ B.attestations,
        a.val_index = i ∧
        a.height_pair = NamedHeightPair.vote sigma.h sigma.T_h.root false

/-- Under `NamedTargetQuorumCoveredByChild E sigma B`, `target_participation` is a quorum after the
    targeted fold of `B`'s attestations from `sigma`. -/
theorem namedTargetQuorum_after_fold
    (E : Env V) {sigma : ChainState V} {B : NamedBlock V}
    (hcovered : NamedTargetQuorumCoveredByChild E sigma B) :
    E.electorate.IsQuorum
      (fold_rows (TimeoutBinding.targeted V) sigma B.erase
        B.attestations).target_participation := by
  obtain ⟨Q, hQ, hcov⟩ := hcovered
  apply Protocol.isQuorum_of_subset hQ
  intro i hi
  rw [w4fkRows_targetParticipation]
  rcases hcov i hi with hold | ⟨a, ha, hai, hpair⟩
  · exact w4fkFold_targetParticipation_subset _ _ hold
  · rw [← hai]
    exact w4fkFold_mem_targetParticipation_of_target _ _ ha hpair

/-- Under `NamedTargetQuorumCoveredByChild E sigma B` and `sigma.nj = false`, the targeted fold of
    `B`'s attestations from `sigma` is `targetReady`. -/
theorem namedTargetReady_of_covered
    (E : Env V) {sigma : ChainState V} {B : NamedBlock V}
    (hcovered : NamedTargetQuorumCoveredByChild E sigma B)
    (hnj : sigma.nj = false) :
    Protocol.targetReady E
      (fold_rows (TimeoutBinding.targeted V) sigma B.erase B.attestations) = true := by
  have hQ := namedTargetQuorum_after_fold E hcovered
  have hquorum :
      (fold_rows (TimeoutBinding.targeted V) sigma B.erase
        B.attestations).targetQuorum E = true := by
    simp only [ChainState.targetQuorum, ChainState.Q_target,
      Electorate.quorumCheck, decide_eq_true_eq]; exact hQ
  simp only [Protocol.targetReady, Bool.and_eq_true]
  refine ⟨?_, hquorum⟩
  rw [w4fkRows_nj, hnj]
  rfl

/-- For a non-genesis `B`, target coverage by its parent's derived state and `B`, with the parent's
    `nj` false, justifies the parent's entry `T_h` at the parent's height and advances `B`'s height
    to the parent's plus one. -/
theorem namedJustifiedAt_of_targetQuorumCoveredByChild
    (E : Env V) (cfg : HeightConfig) {B : NamedBlock V}
    (hBne : B ≠ NamedBlock.genesis)
    (hcovered : NamedTargetQuorumCoveredByChild E (derive_named E cfg B.parent) B)
    (hjustifiable : (derive_named E cfg B.parent).nj = false) :
    NamedJustifiedAt E cfg B
        (derive_named E cfg B.parent).T_h (derive_named E cfg B.parent).h ∧
      (derive_named E cfg B).h = (derive_named E cfg B.parent).h + 1 := by
  cases B with
  | genesis => exact (hBne rfl).elim
  | node p s root gv gsv ats proposer =>
      have htarget := namedTargetReady_of_covered E hcovered hjustifiable
      have htargetAfter :
          Protocol.targetReady E (Protocol.afterFin E
            (fold_rows (TimeoutBinding.targeted V) (derive_named E cfg p)
              (NamedBlock.node p s root gv gsv ats proposer).erase
              (NamedBlock.node p s root gv gsv ats proposer).attestations)) = true := by
        unfold Protocol.afterFin
        split
        · simp only [Protocol.targetReady]; exact htarget
        · exact htarget
      have hderive : derive_named E cfg (.node p s root gv gsv ats proposer) =
          Protocol.process_height_events E cfg
            (fold_rows (TimeoutBinding.targeted V) (derive_named E cfg p)
              (NamedBlock.node p s root gv gsv ats proposer).erase
              (NamedBlock.node p s root gv gsv ats proposer).attestations) := rfl
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [hderive, Protocol.process_height_events_eq, if_pos htargetAfter,
          Protocol.advance_height_J, Protocol.afterFin_T_h, w4fkRows_T_h]
        rfl
      · rw [hderive, Protocol.process_height_events_eq, if_pos htargetAfter,
          Protocol.advance_height_h_j, Protocol.afterFin_h, w4fkRows_h]
        rfl
      · rw [hderive, Protocol.process_height_events_eq, if_pos htargetAfter,
          Protocol.advance_height_h, Protocol.afterFin_h, w4fkRows_h]
        rfl


/-! ## The `nj` bit along a named plateau -/

private theorem w4fkNamedNj_eq_node_of_same_height
    (E : Env V) (cfg : HeightConfig)
    (p : NamedBlock V) (s : Slot) (root : BlockId)
    (gv gsv : List (GoldfishVote V)) (ats : List (NamedAttestation V)) (proposer : V)
    (hh : (derive_named E cfg (.node p s root gv gsv ats proposer)).h =
      (derive_named E cfg p).h) :
    (derive_named E cfg (.node p s root gv gsv ats proposer)).nj =
      (derive_named E cfg p).nj := by
  have hderive : derive_named E cfg (.node p s root gv gsv ats proposer) =
      Protocol.process_height_events E cfg
        (fold_rows (TimeoutBinding.targeted V) (derive_named E cfg p)
          (NamedBlock.node p s root gv gsv ats proposer).erase
          (NamedBlock.node p s root gv gsv ats proposer).attestations) := rfl
  rw [hderive, Protocol.process_height_events_eq]
  split_ifs with htarget hprogress
  · exfalso
    have hh' := hh
    rw [hderive, Protocol.process_height_events_eq, if_pos htarget,
      Protocol.advance_height_h, Protocol.afterFin_h, w4fkRows_h] at hh'
    exact (Nat.ne_of_lt (Nat.lt_succ_self _)) hh'.symm
  · exfalso
    have hh' := hh
    rw [hderive, Protocol.process_height_events_eq, if_neg htarget, if_pos hprogress,
      Protocol.advance_height_h, Protocol.afterFin_h, w4fkRows_h] at hh'
    exact (Nat.ne_of_lt (Nat.lt_succ_self _)) hh'.symm
  · rw [Protocol.afterFin_nj, w4fkRows_nj]

/-- If `C` is a named ancestor of `P` with the same derived height, `P` and `C` have the same `nj`
    bit. -/
theorem namedNj_eq_of_preceq_same_height
    (E : Env V) (cfg : HeightConfig) {C P : NamedBlock V}
    (hCP : NamedBlock.Preceq C P)
    (hh : (derive_named E cfg P).h = (derive_named E cfg C).h) :
    (derive_named E cfg P).nj = (derive_named E cfg C).nj := by
  induction P with
  | genesis =>
      simp only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] at hCP
      subst C
      rfl
  | node p s root gv gsv ats proposer ih =>
      simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hCP
      rcases hCP with rfl | hCp
      · rfl
      · have hmono := Proofs.NamedEntryHeight.derive_height_mono E cfg hCp
        rcases Proofs.NamedEntryHeight.derive_node_height_cases E cfg p s root gv gsv
          ats proposer with hc | hc
        · have hpHeight : (derive_named E cfg p).h = (derive_named E cfg C).h := by
            rw [← hc]; exact hh
          exact (w4fkNamedNj_eq_node_of_same_height E cfg p s root gv gsv ats proposer
            (by rw [hh, hpHeight])).trans (ih hCp hpHeight)
        · exfalso
          rw [hc] at hh
          rw [← hh] at hmono
          exact Nat.not_succ_le_self _ hmono

#print axioms namedTargetQuorum_after_fold
#print axioms namedTargetReady_of_covered
#print axioms namedJustifiedAt_of_targetQuorumCoveredByChild
#print axioms namedNj_eq_of_preceq_same_height

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
