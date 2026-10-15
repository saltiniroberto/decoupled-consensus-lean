import Proofs.Instance.Model
import Proofs.Vocabulary.ModelVocabularyFacts

/-!
# The chain-state facts at `Model.specDraft`

The fields of `ChainStateFacts` and of `ChainStateRunFacts` proved at the chain-state part of
`Model.specDraft`, by rewriting each chain-state reader and each chain state a routine computes as
its image under `toProof`, and the bundle `Model.specDraft_facts_cs`.
-/

set_option autoImplicit false

namespace SpecDraftRecord

open DecoupledConsensusModel
open DecoupledConsensusModel.Sts.Record
open DecoupledConsensusModel.Protocol (HeightConfig)

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The image under `toProof` of `Member.derive_named E cfg B` is `Protocol.derive_named E cfg B`. -/
private theorem toProof_derive_named (E : Env V) (cfg : HeightConfig) (B : NamedBlock V) :
    (Member.derive_named E cfg B).toProof = Protocol.derive_named E cfg B := by
  induction B with
  | genesis =>
    rw [Protocol.derive_named.eq_1, Member.derive_named.eq_1]
    exact SpecDraftRecord.toProof_cs_initial.symm
  | node p s r gv gsv rows i ih =>
    rw [Proofs.BlockProcessingDefaults.derive_named_node, ← ih]
    show (Member.named_transition E cfg _ _).toProof = _
    rw [Member.named_transition, ← SpecDraftRecord.toProof_named_transition,
      Spec.Block.toProofNamed_toSpecNamed]

variable [Inhabited V]

/-- The image under `toProof` of `derive_named` at `Model.specDraft` is `Protocol.derive_named`. -/
private theorem specDraft_derive_named_toProof (E : Env V) (cfg : HeightConfig) (B : NamedBlock V) :
    Spec.Protocol.ChainState.toProof (V := V)
        ((Model.specDraft (V := V)).derive_named E cfg B) =
      Protocol.derive_named E cfg B :=
  toProof_derive_named E cfg B

/-- The image under `toProof` of `named_transition` at `Model.specDraft` is
    `Protocol.named_transition` at the image of the chain state. -/
private theorem specDraft_named_transition_toProof (E : Env V) (cfg : HeightConfig)
    (σ : (Model.specDraft (V := V)).CS) (B : NamedBlock V) :
    Spec.Protocol.ChainState.toProof (V := V)
        ((Model.specDraft (V := V)).named_transition E cfg σ B) =
      Protocol.named_transition E cfg (Spec.Protocol.ChainState.toProof (V := V) σ) B := by
  show (Member.named_transition E cfg σ B).toProof = _
  rw [Member.named_transition, ← SpecDraftRecord.toProof_named_transition,
    Spec.Block.toProofNamed_toSpecNamed]

/-- The image under `toProof` of `process_attestation_with b` at `Model.specDraft` is
    `Protocol.process_attestation_with` with the targeted interpretation, at the images. -/
private theorem specDraft_process_attestation_with_toProof {Row : Type}
    (b : (Model.specDraft (V := V)).Binding Row) (σ : (Model.specDraft (V := V)).CS) (row : Row) :
    Spec.Protocol.ChainState.toProof (V := V)
        ((Model.specDraft (V := V)).process_attestation_with b σ row) =
      Protocol.process_attestation_with (Protocol.TimeoutBinding.targeted V)
        (Spec.Protocol.ChainState.toProof (V := V) σ)
        (Spec.Attestation.toProofNamed (V := V) (b row)) := by
  show (Member.process_attestation_with b σ row).toProof = _
  rw [Member.process_attestation_with,
    ← SpecDraftRecord.toProof_process_attestation_with_targeted]

/-- The image under `toProof` of `advance_height` at `Model.specDraft` is `Protocol.advance_height`
    at the image of the chain state. -/
private theorem specDraft_advance_height_toProof (cfg : HeightConfig)
    (σ : (Model.specDraft (V := V)).CS) :
    Spec.Protocol.ChainState.toProof (V := V)
        ((Model.specDraft (V := V)).advance_height cfg σ) =
      Protocol.advance_height cfg (Spec.Protocol.ChainState.toProof (V := V) σ) :=
  (SpecDraftRecord.toProof_advance_height _ _ cfg σ).symm

/-- The image under `toProof` of `cs_initial` at `Model.specDraft` is `Protocol.ChainState.initial`. -/
private theorem specDraft_cs_initial_toProof :
    Spec.Protocol.ChainState.toProof (V := V) (Model.specDraft (V := V)).cs_initial =
      Protocol.ChainState.initial (V := V) :=
  SpecDraftRecord.toProof_cs_initial.symm

/-- `targetReady` at `Model.specDraft` is `Protocol.targetReady` at the image of the chain state. -/
private theorem specDraft_targetReady_eq (E : Env V) (σ : (Model.specDraft (V := V)).CS) :
    (Model.specDraft (V := V)).targetReady E σ =
      Protocol.targetReady E (Spec.Protocol.ChainState.toProof (V := V) σ) :=
  (SpecDraftRecord.toProof_targetReady E σ).symm

/-- `finalityReady` at `Model.specDraft` is `Protocol.finalityReady` at the image of the chain
    state. -/
private theorem specDraft_finalityReady_eq (E : Env V) (σ : (Model.specDraft (V := V)).CS) :
    (Model.specDraft (V := V)).finalityReady E σ =
      Protocol.finalityReady E (Spec.Protocol.ChainState.toProof (V := V) σ) :=
  (SpecDraftRecord.toProof_finalityReady E σ).symm

/-- `nonjustifiable` at `Model.specDraft` is `Protocol.nonjustifiable`. -/
private theorem specDraft_nonjustifiable_eq (cfg : HeightConfig) (h h_F : Height) :
    (Model.specDraft (V := V)).nonjustifiable cfg h h_F = Protocol.nonjustifiable cfg h h_F :=
  (SpecDraftRecord.toProof_nonjustifiable (V := Unit) ChainStateToHandlers.unreadEnv
    unreadHealConfig cfg h h_F).symm

/-- `targeted` at `Model.specDraft` is `Spec.Attestation.toSpecNamed`. -/
private theorem specDraft_targeted_eq :
    (Model.specDraft (V := V)).targeted = Spec.Attestation.toSpecNamed := rfl

/-- The height of `σ` is the height of its image `σ.toProof`. -/
private theorem specDraft_cs_h (σ : (Model.specDraft (V := V)).CS) :
    ChainStateModel.CS.h (M := (Model.specDraft (V := V)).toChainStateModel) σ =
      (Spec.Protocol.ChainState.toProof (V := V) σ).h := rfl

/-- The entry block of `σ` is the entry block of its image `σ.toProof`. -/
private theorem specDraft_cs_T_h (σ : (Model.specDraft (V := V)).CS) :
    ChainStateModel.CS.T_h (M := (Model.specDraft (V := V)).toChainStateModel) σ =
      (Spec.Protocol.ChainState.toProof (V := V) σ).T_h := rfl

/-- The `nj` bit of `σ` is the `nj` bit of its image `σ.toProof`. -/
private theorem specDraft_cs_nj (σ : (Model.specDraft (V := V)).CS) :
    ChainStateModel.CS.nj (M := (Model.specDraft (V := V)).toChainStateModel) σ =
      (Spec.Protocol.ChainState.toProof (V := V) σ).nj := rfl

/-- The justified block of `σ` is the justified block of its image `σ.toProof`. -/
private theorem specDraft_cs_J (σ : (Model.specDraft (V := V)).CS) :
    ChainStateModel.CS.J (M := (Model.specDraft (V := V)).toChainStateModel) σ =
      (Spec.Protocol.ChainState.toProof (V := V) σ).J := rfl

/-- The justified height of `σ` is the justified height of its image `σ.toProof`. -/
private theorem specDraft_cs_h_j (σ : (Model.specDraft (V := V)).CS) :
    ChainStateModel.CS.h_j (M := (Model.specDraft (V := V)).toChainStateModel) σ =
      (Spec.Protocol.ChainState.toProof (V := V) σ).h_j := rfl

/-- The finalized block of `σ` is the finalized block of its image `σ.toProof`. -/
private theorem specDraft_cs_F (σ : (Model.specDraft (V := V)).CS) :
    ChainStateModel.CS.F (M := (Model.specDraft (V := V)).toChainStateModel) σ =
      (Spec.Protocol.ChainState.toProof (V := V) σ).F := rfl

/-- The finalized height of `σ` is the finalized height of its image `σ.toProof`. -/
private theorem specDraft_cs_h_F (σ : (Model.specDraft (V := V)).CS) :
    ChainStateModel.CS.h_F (M := (Model.specDraft (V := V)).toChainStateModel) σ =
      (Spec.Protocol.ChainState.toProof (V := V) σ).h_F := rfl

/-- The progress set of `σ` is the progress set of its image `σ.toProof`. -/
private theorem specDraft_cs_progress (σ : (Model.specDraft (V := V)).CS) :
    ChainStateModel.CS.progress (M := (Model.specDraft (V := V)).toChainStateModel) σ =
      (Spec.Protocol.ChainState.toProof (V := V) σ).progress := rfl

/-- The target-participation set of `σ` is that of its image `σ.toProof`. -/
private theorem specDraft_cs_target_participation (σ : (Model.specDraft (V := V)).CS) :
    ChainStateModel.CS.target_participation (M := (Model.specDraft (V := V)).toChainStateModel) σ =
      (Spec.Protocol.ChainState.toProof (V := V) σ).target_participation := rfl

/-- The latest block of `σ` is the latest block of its image `σ.toProof`. -/
private theorem specDraft_cs_L (σ : (Model.specDraft (V := V)).CS) :
    (Model.specDraft (V := V)).L σ = (Spec.Protocol.ChainState.toProof (V := V) σ).L :=
  rfl

/-- The `finalize` set of `σ` is the `finalize` set of its image `σ.toProof`. -/
private theorem specDraft_cs_finalize (σ : (Model.specDraft (V := V)).CS) :
    (Model.specDraft (V := V)).finalize σ =
      (Spec.Protocol.ChainState.toProof (V := V) σ).finalize := rfl

end SpecDraftRecord

/-- Rewrites every chain-state reader, and every chain state a routine of `Model.specDraft`
    computes, as its image under `toProof`, by this file's equations. -/
local macro "sd_simp" : tactic => `(tactic| simp only [
  SpecDraftRecord.specDraft_derive_named_toProof,
  SpecDraftRecord.specDraft_named_transition_toProof,
  SpecDraftRecord.specDraft_process_attestation_with_toProof,
  SpecDraftRecord.specDraft_advance_height_toProof, SpecDraftRecord.specDraft_cs_initial_toProof,
  SpecDraftRecord.specDraft_targetReady_eq, SpecDraftRecord.specDraft_finalityReady_eq,
  SpecDraftRecord.specDraft_nonjustifiable_eq, SpecDraftRecord.specDraft_targeted_eq,
  SpecDraftRecord.specDraft_cs_h, SpecDraftRecord.specDraft_cs_T_h,
  SpecDraftRecord.specDraft_cs_nj, SpecDraftRecord.specDraft_cs_J,
  SpecDraftRecord.specDraft_cs_h_j, SpecDraftRecord.specDraft_cs_F,
  SpecDraftRecord.specDraft_cs_h_F, SpecDraftRecord.specDraft_cs_progress,
  SpecDraftRecord.specDraft_cs_target_participation,
  SpecDraftRecord.specDraft_cs_L, SpecDraftRecord.specDraft_cs_finalize,
  Spec.Attestation.toProofNamed_toSpecNamed,
  Spec.Protocol.ChainState.toProof_toSpec])

namespace SpecDraftRecord.ChainStateFacts

open DecoupledConsensusModel
open DecoupledConsensusModel.Sts
open DecoupledConsensusModel.Sts.Record
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Protocol (HeightConfig)

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-- At `Model.specDraft`, genesis's chain state has height `1`. -/
theorem specDraft_derive_named_genesis_h :
    ∀ (E : Env V) (cfg : HeightConfig),
      ((Model.specDraft (V := V)).derive_named E cfg (.genesis : NamedBlock V)).h = 1 := by
  sd_simp
  exact (vocabulary_facts (V := V)).derive_named_genesis_h

/-- At `Model.specDraft`, every named block's chain state has height at least `1`. -/
theorem specDraft_one_le_derive_named_h :
    ∀ (E : Env V) (cfg : HeightConfig) (B : NamedBlock V),
      1 ≤ ((Model.specDraft (V := V)).derive_named E cfg B).h := by
  sd_simp
  exact (vocabulary_facts (V := V)).one_le_derive_named_h

/-- At `Model.specDraft`, if `A ⪯ B`, then `h(A) ≤ h(B)`. -/
theorem specDraft_derive_height_mono :
    ∀ (E : Env V) (cfg : HeightConfig) {A B : NamedBlock V},
      NamedBlock.Preceq A B → ((Model.specDraft (V := V)).derive_named E cfg A).h ≤ ((Model.specDraft (V := V)).derive_named E cfg B).h := by
  sd_simp
  exact (vocabulary_facts (V := V)).derive_height_mono

/-- At `Model.specDraft`, if `A ⪯ B` and `h(A) = h(B)`, then `A` and `B` have the same entry. -/
theorem specDraft_entry_eq_on_plateau :
    ∀ (E : Env V) (cfg : HeightConfig) {A B : NamedBlock V},
      NamedBlock.Preceq A B → ((Model.specDraft (V := V)).derive_named E cfg A).h = ((Model.specDraft (V := V)).derive_named E cfg B).h →
        ((Model.specDraft (V := V)).derive_named E cfg A).T_h = ((Model.specDraft (V := V)).derive_named E cfg B).T_h := by
  sd_simp
  exact (vocabulary_facts (V := V)).entry_eq_on_plateau

/-- At `Model.specDraft`, some ancestor of `B` at `B`'s height erases to `B`'s entry. -/
theorem specDraft_entry_ancestor_same_height :
    ∀ (E : Env V) (cfg : HeightConfig) (B : NamedBlock V),
      ∃ entry : NamedBlock V, NamedBlock.Preceq entry B ∧
        entry.erase = ((Model.specDraft (V := V)).derive_named E cfg B).T_h ∧
        ((Model.specDraft (V := V)).derive_named E cfg entry).h = ((Model.specDraft (V := V)).derive_named E cfg B).h := by
  sd_simp
  exact (vocabulary_facts (V := V)).entry_ancestor_same_height

/-- At `Model.specDraft`, `B`'s entry is an ancestor of `B`'s erasure. -/
theorem specDraft_entry_geometry_ancestor :
    ∀ (E : Env V) (cfg : HeightConfig) (B : NamedBlock V),
      Block.Preceq ((Model.specDraft (V := V)).derive_named E cfg B).T_h B.erase := by
  sd_simp
  exact (vocabulary_facts (V := V)).entry_geometry_ancestor

/-- At `Model.specDraft`, every named block's chain state satisfies the two clauses of the chain
    order. -/
theorem specDraft_chainOrder_derive_named :
    ∀ (E : Env V) (cfg : HeightConfig) (B : NamedBlock V),
      ChainOrderOf (Model.specDraft (V := V)).toChainStateModel ((Model.specDraft (V := V)).derive_named E cfg B) := by
  intro E cfg B
  have h := (vocabulary_facts (V := V)).chainOrder_derive_named E cfg B
  exact ⟨by sd_simp; exact h.heights_ordered, by sd_simp; exact h.justified_below_height⟩

/-- At `Model.specDraft`, `B`'s finalized block and its justified block are ancestors of `B`'s
    erasure. -/
theorem specDraft_derive_named_anchors_preceq :
    ∀ (E : Env V) (cfg : HeightConfig) (B : NamedBlock V),
      Block.Preceq ((Model.specDraft (V := V)).derive_named E cfg B).F B.erase ∧
        Block.Preceq ((Model.specDraft (V := V)).derive_named E cfg B).J B.erase := by
  sd_simp
  exact (vocabulary_facts (V := V)).derive_named_anchors_preceq

/-- At `Model.specDraft`, `B`'s justified height is `0`, or some ancestor of `B` erases to `B`'s
    justified block and has `B`'s justified height. -/
theorem specDraft_justified_ancestor_height :
    ∀ (E : Env V) (cfg : HeightConfig) (B : NamedBlock V),
      ((Model.specDraft (V := V)).derive_named E cfg B).h_j = 0 ∨
        ∃ J : NamedBlock V, NamedBlock.Preceq J B ∧
          J.erase = ((Model.specDraft (V := V)).derive_named E cfg B).J ∧
          ((Model.specDraft (V := V)).derive_named E cfg J).h = ((Model.specDraft (V := V)).derive_named E cfg B).h_j := by
  sd_simp
  exact (vocabulary_facts (V := V)).justified_ancestor_height

/-- At `Model.specDraft`, if `B`'s justified height is positive, some ancestor `J` of `B` erases to
    `B`'s justified block, has `B`'s justified height, and is its own entry. -/
theorem specDraft_namedJustification_selfTarget :
    ∀ (E : Env V) (cfg : HeightConfig) (B : NamedBlock V),
      0 < ((Model.specDraft (V := V)).derive_named E cfg B).h_j →
        ∃ J : NamedBlock V, NamedBlock.Preceq J B ∧
          J.erase = ((Model.specDraft (V := V)).derive_named E cfg B).J ∧
          ((Model.specDraft (V := V)).derive_named E cfg J).h = ((Model.specDraft (V := V)).derive_named E cfg B).h_j ∧
          ((Model.specDraft (V := V)).derive_named E cfg J).T_h = J.erase := by
  sd_simp
  exact (vocabulary_facts (V := V)).namedJustification_selfTarget

/-- At `Model.specDraft`, if `B`'s finalized height is positive, some ancestor `F` of `B` erases to
    `B`'s finalized block, has `B`'s finalized height, and is its own entry. -/
theorem specDraft_namedFinalization_selfTarget_deadline :
    ∀ (E : Env V) (cfg : HeightConfig) (B : NamedBlock V),
      0 < ((Model.specDraft (V := V)).derive_named E cfg B).h_F →
        ∃ F : NamedBlock V, NamedBlock.Preceq F B ∧
          F.erase = ((Model.specDraft (V := V)).derive_named E cfg B).F ∧
          ((Model.specDraft (V := V)).derive_named E cfg F).h = ((Model.specDraft (V := V)).derive_named E cfg B).h_F ∧
          ((Model.specDraft (V := V)).derive_named E cfg F).T_h = F.erase := by
  sd_simp
  exact (vocabulary_facts (V := V)).namedFinalization_selfTarget_deadline

/-- At `Model.specDraft`, some ancestor `J` of `B` erases to `B`'s justified block and is its own
    entry. -/
theorem specDraft_namedJustification_entry_ancestor :
    ∀ (E : Env V) (cfg : HeightConfig) (B : NamedBlock V),
      ∃ J : NamedBlock V, NamedBlock.Preceq J B ∧
        J.erase = ((Model.specDraft (V := V)).derive_named E cfg B).J ∧
        ((Model.specDraft (V := V)).derive_named E cfg J).T_h = J.erase := by
  sd_simp
  exact (vocabulary_facts (V := V)).namedJustification_entry_ancestor

/-- At `Model.specDraft`, a justified height `0` names genesis. -/
theorem specDraft_justified_zero_is_genesis :
    ∀ (E : Env V) (cfg : HeightConfig) (D : NamedBlock V),
      ((Model.specDraft (V := V)).derive_named E cfg D).h_j = 0 → ((Model.specDraft (V := V)).derive_named E cfg D).J = Block.genesis := by
  sd_simp
  exact (vocabulary_facts (V := V)).justified_zero_is_genesis

/-- At `Model.specDraft`, a finalized height `0` names genesis. -/
theorem specDraft_finalized_zero_is_genesis :
    ∀ (E : Env V) (cfg : HeightConfig) (D : NamedBlock V),
      ((Model.specDraft (V := V)).derive_named E cfg D).h_F = 0 → ((Model.specDraft (V := V)).derive_named E cfg D).F = Block.genesis := by
  sd_simp
  exact (vocabulary_facts (V := V)).finalized_zero_is_genesis

/-- At `Model.specDraft`, if `D`'s finalized height is not `0`, some ancestor `F` of `D` erases to
    `D`'s finalized block, and a quorum of signers each have an attestation, included in an ancestor
    of `D`, whose finality pair is `D`'s finalized height with `F`'s root. -/
theorem specDraft_finality_certificate :
    ∀ (E : Env V) (cfg : HeightConfig) (D : NamedBlock V),
      ((Model.specDraft (V := V)).derive_named E cfg D).h_F ≠ 0 →
        ∃ F : NamedBlock V, NamedBlock.Preceq F D ∧
          F.erase = ((Model.specDraft (V := V)).derive_named E cfg D).F ∧
          ∃ Q : Finset V, E.electorate.IsQuorum Q ∧
            ∀ signer ∈ Q, ∃ carrier : NamedBlock V, ∃ a : NamedAttestation V,
              NamedBlock.Preceq carrier D ∧ a ∈ carrier.attestations ∧
              a.val_index = signer ∧
              a.finality_pair = some ⟨((Model.specDraft (V := V)).derive_named E cfg D).h_F, F.root⟩ := by
  sd_simp
  exact (vocabulary_facts (V := V)).finality_certificate

/-- At `Model.specDraft`, for every height `h` with `1 ≤ h < h(C)`, some ancestor `X` of `C` has
    height `h`, and a quorum of signers each have an attestation, included in an ancestor of `C`,
    whose height pair matches `h` and `X`'s root. -/
theorem specDraft_height_crossing :
    ∀ (E : Env V) (cfg : HeightConfig) (C : NamedBlock V) (h : Height),
      1 ≤ h → h < ((Model.specDraft (V := V)).derive_named E cfg C).h →
        ∃ X : NamedBlock V, NamedBlock.Preceq X C ∧
          ((Model.specDraft (V := V)).derive_named E cfg X).h = h ∧
          ∃ Q : Finset V, E.electorate.IsQuorum Q ∧
            ∀ signer ∈ Q, ∃ carrier : NamedBlock V, ∃ a : NamedAttestation V,
              NamedBlock.Preceq carrier C ∧ a ∈ carrier.attestations ∧
              a.val_index = signer ∧ a.height_pair.matchesEntry h X.root = true := by
  sd_simp
  exact (vocabulary_facts (V := V)).height_crossing

/-- At `Model.specDraft`, for every named block `B`, `h_j(B's parent) ≤ h_j(B)`. -/
theorem specDraft_derive_named_h_j_parent_le :
    ∀ (E : Env V) (cfg : HeightConfig) (B : NamedBlock V),
      ((Model.specDraft (V := V)).derive_named E cfg B.parent).h_j ≤ ((Model.specDraft (V := V)).derive_named E cfg B).h_j := by
  sd_simp
  exact (vocabulary_facts (V := V)).derive_named_h_j_parent_le

/-- At `Model.specDraft`, across one block the justified height is the parent's, or the parent's
    height with the parent's `nj` bit clear. -/
theorem specDraft_derive_named_h_j_step_cases :
    ∀ (E : Env V) (cfg : HeightConfig) (p : NamedBlock V)
      (s : Slot) (root : BlockId) (votes support : List (GoldfishVote V))
      (rows : List (NamedAttestation V)) (proposer : V),
      ((Model.specDraft (V := V)).derive_named E cfg (.node p s root votes support rows proposer)).h_j =
          ((Model.specDraft (V := V)).derive_named E cfg p).h_j ∨
        (((Model.specDraft (V := V)).derive_named E cfg (.node p s root votes support rows proposer)).h_j =
            ((Model.specDraft (V := V)).derive_named E cfg p).h ∧ ((Model.specDraft (V := V)).derive_named E cfg p).nj = false) := by
  sd_simp
  exact (vocabulary_facts (V := V)).derive_named_h_j_step_cases

/-- At `Model.specDraft`, if `h(node p …) = h(p)`, then `nj(node p …) = nj(p)`. -/
theorem specDraft_derive_named_node_nj_of_h_eq :
    ∀ (E : Env V) (cfg : HeightConfig) (p : NamedBlock V)
      (s : Slot) (root : BlockId) (votes support : List (GoldfishVote V))
      (rows : List (NamedAttestation V)) (proposer : V),
      ((Model.specDraft (V := V)).derive_named E cfg (.node p s root votes support rows proposer)).h =
          ((Model.specDraft (V := V)).derive_named E cfg p).h →
        ((Model.specDraft (V := V)).derive_named E cfg (.node p s root votes support rows proposer)).nj =
          ((Model.specDraft (V := V)).derive_named E cfg p).nj := by
  sd_simp
  exact (vocabulary_facts (V := V)).derive_named_node_nj_of_h_eq

/-- At `Model.specDraft`, the justified block of `B` is the erasure of an ancestor `J` of `B` that
    is its own height's entry, at `B`'s justified height unless that is `0` and `J` is genesis; the
    same for the finalized block. -/
theorem specDraft_derive_named_checkpoint_entries :
    ∀ (E : Env V) (cfg : HeightConfig) (B : NamedBlock V),
      (∃ J : NamedBlock V, NamedBlock.Preceq J B ∧ J.erase = ((Model.specDraft (V := V)).derive_named E cfg B).J ∧
          ((Model.specDraft (V := V)).derive_named E cfg J).T_h = J.erase ∧
          ((((Model.specDraft (V := V)).derive_named E cfg B).h_j = 0 ∧ J = .genesis) ∨
            ((Model.specDraft (V := V)).derive_named E cfg J).h = ((Model.specDraft (V := V)).derive_named E cfg B).h_j)) ∧
        (∃ F : NamedBlock V, NamedBlock.Preceq F B ∧ F.erase = ((Model.specDraft (V := V)).derive_named E cfg B).F ∧
          ((Model.specDraft (V := V)).derive_named E cfg F).T_h = F.erase ∧
          ((((Model.specDraft (V := V)).derive_named E cfg B).h_F = 0 ∧ F = .genesis) ∨
            ((Model.specDraft (V := V)).derive_named E cfg F).h = ((Model.specDraft (V := V)).derive_named E cfg B).h_F)) := by
  sd_simp
  exact (vocabulary_facts (V := V)).derive_named_checkpoint_entries

/-- At `Model.specDraft`, if `T_h(p).slot + timeoutDelay ≤ s`, and every member of a quorum `Q` is
    in `progress(p)` or signs a row of the block whose height pair matches `(h(p), T_h(p).root)`,
    then `h(node p s …) = h(p) + 1`. -/
theorem specDraft_derive_named_node_h_eq_succ_of_progressQuorum :
    ∀ (E : Env V) (cfg : HeightConfig)
      (p : NamedBlock V) (s : Slot) (root : BlockId) (gv gsv : List (GoldfishVote V))
      (rows : List (NamedAttestation V)) (proposer : V) (Q : Finset V),
      E.electorate.IsQuorum Q →
      ((Model.specDraft (V := V)).derive_named E cfg p).T_h.slot + cfg.timeoutDelay ≤ s →
      (∀ v ∈ Q, v ∈ ((Model.specDraft (V := V)).derive_named E cfg p).progress ∨
        ∃ a ∈ rows, a.val_index = v ∧
          a.height_pair.matchesEntry ((Model.specDraft (V := V)).derive_named E cfg p).h
            ((Model.specDraft (V := V)).derive_named E cfg p).T_h.root = true) →
      ((Model.specDraft (V := V)).derive_named E cfg (.node p s root gv gsv rows proposer)).h =
        ((Model.specDraft (V := V)).derive_named E cfg p).h + 1 := by
  sd_simp
  exact (vocabulary_facts (V := V)).derive_named_node_h_eq_succ_of_progressQuorum

/-- If `hp` is not the timeout vote at `p`'s height, and `hp` is a target vote at that height only
    for `p`'s target, then `hp` does not conflict with `p`. -/
theorem specDraft_conflictsWithFinality_eq_false_of :
    ∀ (hp : HeightPair) (p : FinalityPair),
      hp ≠ .timeout p.height → (∀ U : BlockId, hp = .target p.height U → U = p.target) →
        (Model.specDraft (V := V)).conflictsWithFinality hp p = false :=
  (vocabulary_facts (V := V)).conflictsWithFinality_eq_false_of

/-- If two target votes of `left` and `right` at one height always name one target, the pair is not
    an E2 field conflict. -/
theorem specDraft_e2Fields_eq_false_of :
    ∀ (left right : CombinedAttestation V),
      (∀ (h : Height) (T U : BlockId), left.height_pair = .target h T →
        right.height_pair = .target h U → T = U) →
      (Model.specDraft (V := V)).e2Fields left right = false :=
  (vocabulary_facts (V := V)).e2Fields_eq_false_of

/-- If neither attestation's finality pair conflicts with the other's height pair, and the pair is
    not an E2 field conflict, then the two attestations are not slashable. -/
theorem specDraft_not_Slashable_of_fields :
    ∀ (left right : CombinedAttestation V),
      (∀ p : FinalityPair, left.finality_pair = some p →
        (Model.specDraft (V := V)).conflictsWithFinality right.height_pair p = false) →
      (∀ q : FinalityPair, right.finality_pair = some q →
        (Model.specDraft (V := V)).conflictsWithFinality left.height_pair q = false) →
      (Model.specDraft (V := V)).e2Fields left right = false → ¬ (Model.specDraft (V := V)).Slashable left right :=
  (vocabulary_facts (V := V)).not_Slashable_of_fields

end SpecDraftRecord.ChainStateFacts

namespace SpecDraftRecord.ChainStateRunFacts

open DecoupledConsensusModel
open DecoupledConsensusModel.Sts
open DecoupledConsensusModel.Sts.Record
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Protocol (HeightConfig)

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-- At `Model.specDraft`, if `v`'s round-`r` action has the FG source `Cfg`, some body `C` of the
    action's store erases to `Cfg`, the store's height, entry and `nj` bit at `Cfg` are `C`'s, and
    the action's confirmation witness is `C`'s entry. -/
theorem specDraft_action_witness :
    ∀ (S : Setup V) (rho : Run V) (v : V) (r : Round) (Cfg : Block V),
      actionFGSource S (actionReadAt S rho v r) = some Cfg →
        ∃ C : NamedBlock V,
          C ∈ (actionReadAt S rho v r).st.bodies ∧ C.erase = Cfg ∧
          ((actionReadAt S rho v r).st.core.σ Cfg).h = ((Model.specDraft (V := V)).derive_named S.E S.cfg C).h ∧
          ((actionReadAt S rho v r).st.core.σ Cfg).T_h = ((Model.specDraft (V := V)).derive_named S.E S.cfg C).T_h ∧
          ((actionReadAt S rho v r).st.core.σ Cfg).nj = ((Model.specDraft (V := V)).derive_named S.E S.cfg C).nj ∧
          fgConfirmationWitness S (actionReadAt S rho v r) =
            some ((Model.specDraft (V := V)).derive_named S.E S.cfg C).T_h := by
  sd_simp
  exact (vocabulary_runFacts (V := V)).action_witness

/-- At `Model.specDraft`, every body `D` of `v`'s round-`r` action store has, in that store, the
    entry of its chain state. -/
theorem specDraft_derivedStateAgrees_actionStoreAtOn :
    ∀ (S : Setup V) {rho : Run V} (Hs : Int → Finset V)
      (Xb : Finset V) {lo : Int}, AdmissibleFieldsOn S rho Hs Xb lo →
      ∀ (v : V) (r : Round), ∀ D ∈ (actionStoreAt S rho v r).st.bodies,
        ((actionStoreAt S rho v r).st.core.σ D.erase).T_h = ((Model.specDraft (V := V)).derive_named S.E S.cfg D).T_h := by
  sd_simp
  exact (vocabulary_runFacts (V := V)).derivedStateAgrees_actionStoreAtOn

/-- At `Model.specDraft`, if `v ∈ Xb` and `D` is a body of `v`'s round-`r` action store, some body
    `K` of that store erases to `D`'s entry, has `D`'s height, is an ancestor of `D`, and is a run
    block read through `Xb`. -/
theorem specDraft_action_named_checkpointOn :
    ∀ (S : Setup V) {rho : Run V} (Hs : Int → Finset V)
      (Xb : Finset V) {lo : Int}, AdmissibleFieldsOn S rho Hs Xb lo →
      ∀ {v : V}, v ∈ Xb → ∀ {r : Round} {D : NamedBlock V},
        D ∈ (actionStoreAt S rho v r).st.bodies →
      ∃ K : NamedBlock V,
        K ∈ (actionStoreAt S rho v r).st.bodies ∧
        K.erase = ((Model.specDraft (V := V)).derive_named S.E S.cfg D).T_h ∧
        ((Model.specDraft (V := V)).derive_named S.E S.cfg K).h = ((Model.specDraft (V := V)).derive_named S.E S.cfg D).h ∧
        NamedBlock.Preceq K D ∧
        RunBlockOn S rho Xb K := by
  sd_simp
  exact (vocabulary_runFacts (V := V)).action_named_checkpointOn

/-- At `Model.specDraft`, if `a`'s signer, a member of `Xb`, emits `a` at `ta` with a height pair
    naming `h`, the signer's round action has FG source `D` at height `h` and confirmation witness
    the entry of a same-height body `K ⪯ D`, and `a`'s height pair targets `K`'s root at `h` or is
    the timeout at `h`. -/
theorem specDraft_honestHeightRow_confirmationWitnessOn :
    ∀ (S : Setup V) {rho : Run V} (Hs : Int → Finset V)
      (Xb : Finset V) {lo : Int}, AdmissibleFieldsOn S rho Hs Xb lo →
      ∀ {a : NamedAttestation V} {ta : Time} {h : Height},
      a.val_index ∈ Xb →
      rho.emits S a.val_index (Object.attest a) ta →
      a.height_pair.erase.height? = some h →
      ∃ D K : NamedBlock V,
        fgConfirmationWitness S
            (actionStoreAt S rho a.val_index a.round) =
          some ((Model.specDraft (V := V)).derive_named S.E S.cfg K).T_h ∧
        D ∈ (actionStoreAt S rho a.val_index a.round).st.bodies ∧
        actionFGSource S (actionStoreAt S rho a.val_index a.round) = some D.erase ∧
        ((Model.specDraft (V := V)).derive_named S.E S.cfg D).h = h ∧
        K ∈ (actionStoreAt S rho a.val_index a.round).st.bodies ∧
        K.erase = ((Model.specDraft (V := V)).derive_named S.E S.cfg D).T_h ∧
        ((Model.specDraft (V := V)).derive_named S.E S.cfg K).h = h ∧
        Block.Preceq K.erase D.erase ∧
        (a.height_pair.erase = HeightPair.target h K.erase.root ∨
          a.height_pair.erase = HeightPair.timeout h) := by
  sd_simp
  exact (vocabulary_runFacts (V := V)).honestHeightRow_confirmationWitnessOn

/-- At `Model.specDraft`, under `AdmissibleFieldsOn`, if the validators outside the set for the
    horizon weigh less than a third, `v ∈ Xb`, `T` is a run block of height `k ≥ 2` read through
    `Xb`, every height-`k` row emitted by a signer in the set for the horizon has `T` as its
    action's confirmation witness, and `v`'s `h_max` after `n` events is at most `k + 1`, then `v`'s
    finalized block there is an ancestor of `T.erase`. -/
theorem specDraft_storeF_preceq_checkpoint_of_windowOn :
    ∀ (S : Setup V) {rho : Run V} (Hs : Int → Finset V)
      (Xb : Finset V) {lo : Int}, AdmissibleFieldsOn S rho Hs Xb lo →
      (∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) → (∀ t : Int, Hs t ⊆ Xb) →
      Execution.BelowOneThird S (Hs rho.horizon) →
      ∀ {v : V}, v ∈ Xb → ∀ {n : Nat} {k : Height} {T : NamedBlock V},
      RunBlockOn S rho Xb T →
      ((Model.specDraft (V := V)).derive_named S.E S.cfg T).h = k → 2 ≤ k →
      (∀ (b : NamedAttestation V) (tb : Time), b.val_index ∈ Hs rho.horizon →
        NamedRun.emits S rho b.val_index (Object.attest b) tb →
        b.height_pair.erase.height? = some k →
        fgConfirmationWitness S (actionStoreAt S rho b.val_index b.round) = some T.erase) →
      (rho.stateBefore S n v).st.core.h_max ≤ k + 1 →
      Block.Preceq (rho.stateBefore S n v).st.core.F T.erase := by
  sd_simp
  exact (vocabulary_runFacts (V := V)).storeF_preceq_checkpoint_of_windowOn

end SpecDraftRecord.ChainStateRunFacts

namespace DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-- The chain-state part of `Model.specDraft` satisfies `ChainStateFacts`. -/
theorem Model.specDraft_facts_cs : ChainStateFacts (Model.specDraft (V := V)).toChainStateModel where
  derive_named_genesis_h := SpecDraftRecord.ChainStateFacts.specDraft_derive_named_genesis_h
  one_le_derive_named_h := SpecDraftRecord.ChainStateFacts.specDraft_one_le_derive_named_h
  derive_height_mono := SpecDraftRecord.ChainStateFacts.specDraft_derive_height_mono
  entry_eq_on_plateau := SpecDraftRecord.ChainStateFacts.specDraft_entry_eq_on_plateau
  entry_ancestor_same_height := SpecDraftRecord.ChainStateFacts.specDraft_entry_ancestor_same_height
  entry_geometry_ancestor := SpecDraftRecord.ChainStateFacts.specDraft_entry_geometry_ancestor
  chainOrder_derive_named := SpecDraftRecord.ChainStateFacts.specDraft_chainOrder_derive_named
  derive_named_anchors_preceq := SpecDraftRecord.ChainStateFacts.specDraft_derive_named_anchors_preceq
  justified_ancestor_height := SpecDraftRecord.ChainStateFacts.specDraft_justified_ancestor_height
  namedJustification_selfTarget := SpecDraftRecord.ChainStateFacts.specDraft_namedJustification_selfTarget
  namedFinalization_selfTarget_deadline := SpecDraftRecord.ChainStateFacts.specDraft_namedFinalization_selfTarget_deadline
  namedJustification_entry_ancestor := SpecDraftRecord.ChainStateFacts.specDraft_namedJustification_entry_ancestor
  justified_zero_is_genesis := SpecDraftRecord.ChainStateFacts.specDraft_justified_zero_is_genesis
  finalized_zero_is_genesis := SpecDraftRecord.ChainStateFacts.specDraft_finalized_zero_is_genesis
  finality_certificate := SpecDraftRecord.ChainStateFacts.specDraft_finality_certificate
  height_crossing := SpecDraftRecord.ChainStateFacts.specDraft_height_crossing
  derive_named_h_j_parent_le := SpecDraftRecord.ChainStateFacts.specDraft_derive_named_h_j_parent_le
  derive_named_h_j_step_cases := SpecDraftRecord.ChainStateFacts.specDraft_derive_named_h_j_step_cases
  derive_named_node_nj_of_h_eq := SpecDraftRecord.ChainStateFacts.specDraft_derive_named_node_nj_of_h_eq
  derive_named_checkpoint_entries := SpecDraftRecord.ChainStateFacts.specDraft_derive_named_checkpoint_entries
  derive_named_node_h_eq_succ_of_progressQuorum := SpecDraftRecord.ChainStateFacts.specDraft_derive_named_node_h_eq_succ_of_progressQuorum
  conflictsWithFinality_eq_false_of := SpecDraftRecord.ChainStateFacts.specDraft_conflictsWithFinality_eq_false_of
  e2Fields_eq_false_of := SpecDraftRecord.ChainStateFacts.specDraft_e2Fields_eq_false_of
  not_Slashable_of_fields := SpecDraftRecord.ChainStateFacts.specDraft_not_Slashable_of_fields

end DecoupledConsensusModel.Sts.Record
