module
public import Proofs.Vocabulary.Protocol.ChainState.TargetedTimeoutBinding
public import Proofs.Vocabulary.ModelProperties.Env_q
public import Proofs.Vocabulary.Internal.Definitions.NamedCertificates
public import Proofs.Vocabulary.Internal.Legacy.Assumptions.Weight
public import Proofs.Vocabulary.Internal.Legacy.Definitions.ActionSources
public import Model.Vocabulary.Statements.Instantiation.Certificates
public import Model.Vocabulary.Statements.Instantiation.Proposals
import Proofs.Vocabulary.Protocol.ChainState.Certificates
import Proofs.Vocabulary.Protocol.ChainState.FinalityQuorumCore
import Proofs.Vocabulary.Protocol.ChainState.ProposalBridge
import Proofs.Vocabulary.Protocol.Schedule.Action
import Mathlib.Data.Rat.Floor
public import Proofs.Vocabulary.Internal.Internal.GradeReads

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

/-! ## Finality bits through the targeted row fold -/

omit [Fintype V] in
private theorem w4fwFold_finalize_subset
    (rows : List (NamedAttestation V)) (sigma : ChainState V) :
    sigma.finalize ⊆
      (rows.foldl (process_attestation_with (TimeoutBinding.targeted V))
        sigma).finalize := by
  induction rows generalizing sigma with
  | nil => exact Finset.Subset.refl _
  | cons row rows ih =>
      rw [List.foldl_cons]
      refine Finset.Subset.trans ?_ (ih _)
      intro i hi
      rw [TargetedTimeoutBinding.process_finality_eq sigma row,
        Protocol.process_attestation_finalize]
      split_ifs
      · exact Finset.mem_insert_of_mem hi
      · exact hi

omit [Fintype V] in
private theorem w4fwFold_mem_finalize_of_finality
    {a : NamedAttestation V} :
    ∀ (rows : List (NamedAttestation V)) (sigma : ChainState V),
      a ∈ rows →
      sigma.h_F < sigma.h_j →
      a.finality_pair = some ⟨sigma.h_j, sigma.J.root⟩ →
      a.val_index ∈
        (rows.foldl (process_attestation_with (TimeoutBinding.targeted V))
          sigma).finalize := by
  intro rows
  induction rows with
  | nil => intro _ ha _ _; simp at ha
  | cons row rows ih =>
      intro sigma ha hlt hpair
      rw [List.foldl_cons]
      rcases List.mem_cons.mp ha with rfl | hmem
      · apply w4fwFold_finalize_subset
        rw [TargetedTimeoutBinding.process_finality_eq sigma a,
          Protocol.process_attestation_finalize]
        simp [hlt, hpair, NamedAttestation.erase]
      · apply ih _ hmem
        · have hfields := TimeoutBindingDefaults.process_context_fields
            (TimeoutBinding.targeted V) sigma row
          rw [hfields.2.2.2.2.1, hfields.2.2.2.2.2.2]
          exact hlt
        · have hfields := TimeoutBindingDefaults.process_context_fields
            (TimeoutBinding.targeted V) sigma row
          rw [hfields.2.2.2.2.1, hfields.2.2.2.1]
          exact hpair

omit [Fintype V] in
private theorem w4fwRows_h_j (sigma : ChainState V) (geometry : Block V)
    (rows : List (NamedAttestation V)) :
    (fold_rows (TimeoutBinding.targeted V) sigma geometry rows).h_j = sigma.h_j := by
  unfold fold_rows
  exact (NamedDerivationGeometry.fold_context_fields
    (TimeoutBinding.targeted V) rows { sigma with s := geometry.slot }).2.2.2.2.1

omit [Fintype V] in
private theorem w4fwRows_J (sigma : ChainState V) (geometry : Block V)
    (rows : List (NamedAttestation V)) :
    (fold_rows (TimeoutBinding.targeted V) sigma geometry rows).J = sigma.J := by
  unfold fold_rows
  exact (NamedDerivationGeometry.fold_context_fields
    (TimeoutBinding.targeted V) rows { sigma with s := geometry.slot }).2.2.2.1

omit [Fintype V] in
private theorem w4fwRows_h_F (sigma : ChainState V) (geometry : Block V)
    (rows : List (NamedAttestation V)) :
    (fold_rows (TimeoutBinding.targeted V) sigma geometry rows).h_F = sigma.h_F := by
  unfold fold_rows
  exact (NamedDerivationGeometry.fold_context_fields
    (TimeoutBinding.targeted V) rows { sigma with s := geometry.slot }).2.2.2.2.2.2

omit [Fintype V] in
private theorem w4fwRows_finalize (sigma : ChainState V) (geometry : Block V)
    (rows : List (NamedAttestation V)) :
    (fold_rows (TimeoutBinding.targeted V) sigma geometry rows).finalize =
      (rows.foldl (process_attestation_with (TimeoutBinding.targeted V))
        { sigma with s := geometry.slot }).finalize := rfl

/-! ## Named finality coverage -/

/-- The parent state `sigma` has justification `(h_j, J)`, and some quorum's members are each in
    `sigma.finalize` or have an attestation of `B` with finality pair `(h_j, J.root)`. -/
def NamedFinalityQuorumCoveredByChild
    (E : Env V) (sigma : ChainState V) (B : NamedBlock V)
    (h_j : Height) (J : Block V) : Prop :=
  sigma.h_j = h_j ∧ sigma.J = J ∧
    ∃ Q : Finset V, E.electorate.IsQuorum Q ∧
      ∀ i ∈ Q,
        i ∈ sigma.finalize ∨
        ∃ a ∈ B.attestations,
          a.val_index = i ∧
          a.finality_pair = some ⟨h_j, J.root⟩

/-- If `NamedFinalityQuorumCoveredByChild E sigma B h_j J` and `sigma.h_F < h_j`, the targeted fold
    of `B`'s attestations from `sigma` is `finalityReady`. -/
theorem namedFinalityReady_of_covered
    (E : Env V) {sigma : ChainState V} {B : NamedBlock V}
    {h_j : Height} {J : Block V}
    (hcovered : NamedFinalityQuorumCoveredByChild E sigma B h_j J)
    (hlt : sigma.h_F < h_j) :
    Protocol.finalityReady E
      (fold_rows (TimeoutBinding.targeted V) sigma B.erase B.attestations) = true := by
  obtain ⟨hhj, hJ, Q, hQ, hcov⟩ := hcovered
  have hltSigma : sigma.h_F < sigma.h_j := by simpa only [hhj] using hlt
  have hquorumSet : E.electorate.IsQuorum
      (fold_rows (TimeoutBinding.targeted V) sigma B.erase B.attestations).finalize := by
    apply Protocol.isQuorum_of_subset hQ
    intro i hi
    rw [w4fwRows_finalize]
    rcases hcov i hi with hold | ⟨a, ha, hai, hpair⟩
    · exact w4fwFold_finalize_subset _ _ hold
    · rw [← hai]
      refine w4fwFold_mem_finalize_of_finality _ _ ha hltSigma ?_
      simpa only [hhj, hJ] using hpair
  have hquorum :
      (fold_rows (TimeoutBinding.targeted V) sigma B.erase
        B.attestations).finalityQuorum E = true := by
    simp only [ChainState.finalityQuorum, ChainState.Q_finality,
      Electorate.quorumCheck, decide_eq_true_eq]; exact hquorumSet
  simp only [Protocol.finalityReady, Bool.and_eq_true]
  refine ⟨?_, hquorum⟩
  simp only [decide_eq_true_eq]
  rw [w4fwRows_h_F, w4fwRows_h_j, hhj]
  exact hlt

/-- For a non-genesis `B`, finality coverage of `(h, J)` by its parent's derived state and `B`, with
    the parent's `h_F < h`, gives `NamedFinalizedAt E cfg B J h`. -/
theorem namedFinalizedAt_of_finalityQuorumCoveredByChild
    (E : Env V) (cfg : HeightConfig) {B : NamedBlock V} {J : Block V} {h : Height}
    (hBne : B ≠ NamedBlock.genesis)
    (hcovered : NamedFinalityQuorumCoveredByChild E (derive_named E cfg B.parent) B h J)
    (hdebt : (derive_named E cfg B.parent).h_F < h) :
    NamedFinalizedAt E cfg B J h := by
  cases B with
  | genesis => exact (hBne rfl).elim
  | node p s root gv gsv ats proposer =>
      have hready := namedFinalityReady_of_covered E hcovered hdebt
      have hderive : derive_named E cfg (.node p s root gv gsv ats proposer) =
          Protocol.process_height_events E cfg
            (fold_rows (TimeoutBinding.targeted V) (derive_named E cfg p)
              (NamedBlock.node p s root gv gsv ats proposer).erase
              (NamedBlock.node p s root gv gsv ats proposer).attestations) := rfl
      have hwrite := process_height_events_actual_F E cfg
        (fold_rows (TimeoutBinding.targeted V) (derive_named E cfg p)
          (NamedBlock.node p s root gv gsv ats proposer).erase
          (NamedBlock.node p s root gv gsv ats proposer).attestations) hready
      obtain ⟨hhj, hJ, -⟩ := hcovered
      refine ⟨?_, ?_⟩
      · rw [hderive, hwrite.1, w4fwRows_J]
        exact hJ
      · rw [hderive, hwrite.2, w4fwRows_h_j]
        exact hhj

#print axioms namedFinalityReady_of_covered
#print axioms namedFinalizedAt_of_finalityQuorumCoveredByChild

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
