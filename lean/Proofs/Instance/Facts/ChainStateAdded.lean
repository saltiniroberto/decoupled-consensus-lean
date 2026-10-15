import Proofs.Instance.Model
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Instance.Equalities.ContractImages

/-!
# The added chain-state facts at `Model.specDraft`

The fields of `ChainStateAddedFacts` proved at `Model.specDraft`, by rewriting each chain-state
reader and each chain state a routine computes as its image under `toProof`, and the bundle
`Model.specDraft_runFacts_csAdded` of `ChainStateAddedRunFacts`, which has no field.
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

/-- The `finalize` set of `process_attestation σ a` at `Model.specDraft` is that of
    `Protocol.process_attestation` at the image of the chain state. -/
private theorem specDraft_finalize_process_attestation (σ : (Model.specDraft (V := V)).CS)
    (a : CombinedAttestation V) :
    (Model.specDraft (V := V)).finalize ((Model.specDraft (V := V)).process_attestation σ a) =
      (Protocol.process_attestation (Spec.Protocol.ChainState.toProof (V := V) σ)
        a).finalize := by
  have h := (Model.vocabulary_facts_csAdded (V := V)).process_finality_eq
    (Spec.Protocol.ChainState.toProof (V := V) σ)
    (Spec.Attestation.toSpec a).toProofNamed
  rw [Spec.Attestation.toProofNamed_erase, Spec.Attestation.toProof_toSpec] at h
  show (Member.process_attestation σ a).toProof.finalize = _
  rw [Member.process_attestation, ← SpecDraftRecord.toProof_process_attestation_with_targeted]
  exact h

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

namespace SpecDraftRecord.ChainStateAddedFacts

open DecoupledConsensusModel
open DecoupledConsensusModel.Sts
open DecoupledConsensusModel.Sts.Record
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Protocol (HeightConfig)

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-- At `Model.specDraft`, if the named rows `a` and `b` have the same validator, `a`'s height pair
    matches the entry `entry` at height `h`, `b`'s finality pair is `(h, finalized)`, and
    `entry ≠ finalized`, then the erasures of `a` and `b` are slashable. -/
theorem specDraft_matching_finality_e1 :
    ∀ (a b : NamedAttestation V) (h : Height) (entry finalized : BlockId),
      a.val_index = b.val_index →
      a.height_pair.matchesEntry h entry = true →
      b.finality_pair = some ⟨h, finalized⟩ →
      entry ≠ finalized →
      (Model.specDraft (V := V)).Slashable a.erase b.erase :=
  (Model.vocabulary_facts_csAdded (V := V)).matching_finality_e1

/-- At `Model.specDraft`, the chain state derived from every named block satisfies `NjEntry`: some
    height `h_F'` at most its finalized height gives its `nj` bit as `nonjustifiable cfg` at its
    height and `h_F'`. -/
theorem specDraft_njEntry_derive_named :
    ∀ (E : Env V) (cfg : HeightConfig) (B : NamedBlock V),
      Restated.Vocabulary.Proofs.NjGap.NjEntry (Model.specDraft (V := V)) cfg ((Model.specDraft (V := V)).derive_named E cfg B) := by
  intro E cfg B
  unfold Restated.Vocabulary.Proofs.NjGap.NjEntry
  sd_simp
  exact (Model.vocabulary_facts_csAdded (V := V)).njEntry_derive_named E cfg B

/-- At `Model.specDraft`, if `B`'s justified height is positive, some ancestor `J` of `B` erases to
    `B`'s justified block, has `B`'s justified height, is its own entry, and has `nj` false. -/
theorem specDraft_namedJustification_ancestor_data :
    ∀ (E : Env V) (cfg : HeightConfig) (B : NamedBlock V),
      0 < ((Model.specDraft (V := V)).derive_named E cfg B).h_j →
        ∃ J : NamedBlock V, NamedBlock.Preceq J B ∧
          J.erase = ((Model.specDraft (V := V)).derive_named E cfg B).J ∧
          ((Model.specDraft (V := V)).derive_named E cfg J).h = ((Model.specDraft (V := V)).derive_named E cfg B).h_j ∧
          ((Model.specDraft (V := V)).derive_named E cfg J).T_h = J.erase ∧
          ((Model.specDraft (V := V)).derive_named E cfg J).nj = false := by
  sd_simp
  exact (Model.vocabulary_facts_csAdded (V := V)).namedJustification_ancestor_data

/-- At `Model.specDraft`, if `D`'s justified height is not `0`, some ancestor `J` of `D` erases to
    `D`'s justified block, and a quorum of signers each have an attestation, included in an ancestor
    of `D`, whose height pair is a vote for `D`'s justified height and `J`'s root with the timeout
    bit clear. -/
theorem specDraft_justification_certificate :
    ∀ (E : Env V) (cfg : HeightConfig) (D : NamedBlock V),
      ((Model.specDraft (V := V)).derive_named E cfg D).h_j ≠ 0 →
        ∃ J : NamedBlock V, NamedBlock.Preceq J D ∧
          J.erase = ((Model.specDraft (V := V)).derive_named E cfg D).J ∧
          ∃ Q : Finset V, E.electorate.IsQuorum Q ∧
            ∀ signer ∈ Q, ∃ carrier : NamedBlock V, ∃ a : NamedAttestation V,
              NamedBlock.Preceq carrier D ∧ a ∈ carrier.attestations ∧
              a.val_index = signer ∧
              a.height_pair = .vote ((Model.specDraft (V := V)).derive_named E cfg D).h_j J.root false := by
  sd_simp
  exact (Model.vocabulary_facts_csAdded (V := V)).justification_certificate

/-- At `Model.specDraft`, if the finalized height of `D`'s chain state is not `0`, some ancestor `F`
    of `D` erases to `D`'s finalized block, and some quorum `Q` has every member sign an
    attestation, included in an ancestor of `D`, whose finality pair is `D`'s finalized height with
    the root of `F`. -/
theorem specDraft_finality_certificate :
    ∀ (E : Env V) (cfg : HeightConfig) (D : NamedBlock V)
      (hnz : ((Model.specDraft (V := V)).derive_named E cfg D).h_F ≠ 0),
      ∃ F : NamedBlock V, NamedBlock.Preceq F D ∧
        F.erase = ((Model.specDraft (V := V)).derive_named E cfg D).F ∧
        ∃ Q : Finset V, E.electorate.IsQuorum Q ∧
          ∀ signer ∈ Q, ∃ carrier : NamedBlock V, ∃ a : NamedAttestation V,
            NamedBlock.Preceq carrier D ∧ a ∈ carrier.attestations ∧
            a.val_index = signer ∧
            a.finality_pair = some ⟨((Model.specDraft (V := V)).derive_named E cfg D).h_F, F.root⟩ := by
  sd_simp
  exact (Model.vocabulary_facts_csAdded (V := V)).finality_certificate

/-- At `Model.specDraft`, after `cs_with_F_h_F σ B h` the finalized block is `B`, its height is `h`,
    and `h`, `T_h`, `L`, `J`, `h_j`, `target_participation`, `progress`, `finalize` and `nj` are
    those of `σ`. -/
theorem specDraft_cs_with_F_h_F_fields :
    ∀ (σ : (Model.specDraft (V := V)).CS) (B : Block V) (h : Height),
      ((Model.specDraft (V := V)).cs_with_F_h_F σ B h).F = B ∧ ((Model.specDraft (V := V)).cs_with_F_h_F σ B h).h_F = h ∧
      ((Model.specDraft (V := V)).cs_with_F_h_F σ B h).h = σ.h ∧ ((Model.specDraft (V := V)).cs_with_F_h_F σ B h).T_h = σ.T_h ∧
      (Model.specDraft (V := V)).L ((Model.specDraft (V := V)).cs_with_F_h_F σ B h) = (Model.specDraft (V := V)).L σ ∧ ((Model.specDraft (V := V)).cs_with_F_h_F σ B h).J = σ.J ∧
      ((Model.specDraft (V := V)).cs_with_F_h_F σ B h).h_j = σ.h_j ∧
      ((Model.specDraft (V := V)).cs_with_F_h_F σ B h).target_participation = σ.target_participation ∧
      ((Model.specDraft (V := V)).cs_with_F_h_F σ B h).progress = σ.progress ∧
      (Model.specDraft (V := V)).finalize ((Model.specDraft (V := V)).cs_with_F_h_F σ B h) = (Model.specDraft (V := V)).finalize σ ∧ ((Model.specDraft (V := V)).cs_with_F_h_F σ B h).nj = σ.nj := by
  intro σ B h
  exact ⟨Spec.Block.toProof_toSpec B, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- At `Model.specDraft`, a validator `i` in the `finalize` set after `process_attestation σ a` was
    in `σ`'s `finalize` set, or is the validator of `a` and `a`'s finality pair is `σ`'s justified
    height with the root of `σ`'s justified block. -/
theorem specDraft_mem_finalize_process_attestation :
    ∀ (σ : (Model.specDraft (V := V)).CS) (a : CombinedAttestation V) {i : V}
      (h : i ∈ (Model.specDraft (V := V)).finalize ((Model.specDraft (V := V)).process_attestation σ a)),
      i ∈ (Model.specDraft (V := V)).finalize σ ∨ (i = a.val_index ∧ a.finality_pair = some ⟨σ.h_j, σ.J.root⟩) := by
  intro σ a i
  rw [SpecDraftRecord.specDraft_finalize_process_attestation]
  sd_simp
  exact (Model.vocabulary_facts_csAdded (V := V)).mem_finalize_process_attestation (Spec.Protocol.ChainState.toProof (V := V) σ) a

/-- At `Model.specDraft`, the chain state derived for the block
    `p.node s root votes support rows proposer` is the transition, by that block, of the chain state
    derived for `p`. -/
theorem specDraft_derive_named_node :
    ∀ (E : DecoupledConsensusModel.Env V) (cfg : DecoupledConsensusModel.Protocol.HeightConfig) (p : DecoupledConsensusModel.NamedBlock V) (s : DecoupledConsensusModel.Slot) (root : DecoupledConsensusModel.BlockId) (votes support : List (DecoupledConsensusModel.GoldfishVote V)) (rows : List (DecoupledConsensusModel.NamedAttestation V)) (proposer : V), (Model.specDraft (V := V)).derive_named E cfg (p.node s root votes support rows proposer) = (Model.specDraft (V := V)).named_transition E cfg ((Model.specDraft (V := V)).derive_named E cfg p) (p.node s root votes support rows proposer) := by
  intro E cfg p s root votes support rows proposer
  rfl

/-- At `Model.specDraft`, if `B` is not genesis, the chain state derived for `B` is the transition,
    by `B`, of the chain state derived for `B`'s parent. -/
theorem specDraft_derive_named_of_not_genesis :
    ∀ (E : DecoupledConsensusModel.Env V) (cfg : DecoupledConsensusModel.Protocol.HeightConfig) (B : DecoupledConsensusModel.NamedBlock V), B ≠ DecoupledConsensusModel.NamedBlock.genesis → (Model.specDraft (V := V)).derive_named E cfg B = (Model.specDraft (V := V)).named_transition E cfg ((Model.specDraft (V := V)).derive_named E cfg B.parent) B := by
  intro E cfg B hB
  cases B with
  | genesis => exact absurd rfl hB
  | node p s root votes support rows proposer =>
    simp only [NamedBlock.parent]
    exact specDraft_derive_named_node E cfg p s root votes support rows proposer

/-- At `Model.specDraft`, if `A ⪯ B`, then `h_j(A) < h_j(B)`, or `h_j(A) = h_j(B)` and
    `J(A) = J(B)`. -/
theorem specDraft_namedJustification_strict_or_eq_of_preceq :
    ∀ (E : Env V) (cfg : HeightConfig)
      {A B : NamedBlock V}, NamedBlock.Preceq A B →
        ((Model.specDraft (V := V)).derive_named E cfg A).h_j < ((Model.specDraft (V := V)).derive_named E cfg B).h_j ∨
          (((Model.specDraft (V := V)).derive_named E cfg A).h_j = ((Model.specDraft (V := V)).derive_named E cfg B).h_j ∧
            ((Model.specDraft (V := V)).derive_named E cfg A).J = ((Model.specDraft (V := V)).derive_named E cfg B).J) := by
  sd_simp
  exact (Model.vocabulary_facts_csAdded (V := V)).namedJustification_strict_or_eq_of_preceq

/-- At `Model.specDraft`, `h_j(genesis) = 0`. -/
theorem specDraft_ModelProperties_derive_named_genesis_h_j :
    ∀ (E : Env V) (cfg : HeightConfig),
      ((Model.specDraft (V := V)).derive_named E cfg (.genesis : NamedBlock V)).h_j = 0 := by
  sd_simp
  exact (Model.vocabulary_facts_csAdded (V := V)).ModelProperties_derive_named_genesis_h_j

/-- At `Model.specDraft`, if `A ⪯ B` and `h(B) = h(A)`, then `nj(B) = nj(A)`. -/
theorem specDraft_namedNj_eq_of_preceq_sameHeight :
    ∀ (E : Env V) (cfg : HeightConfig) {A B : NamedBlock V},
      NamedBlock.Preceq A B → ((Model.specDraft (V := V)).derive_named E cfg B).h = ((Model.specDraft (V := V)).derive_named E cfg A).h →
        ((Model.specDraft (V := V)).derive_named E cfg B).nj = ((Model.specDraft (V := V)).derive_named E cfg A).nj := by
  sd_simp
  exact (Model.vocabulary_facts_csAdded (V := V)).namedNj_eq_of_preceq_sameHeight

/-- At `Model.specDraft`, `B`'s finalized height is `0`, or some ancestor `F` of `B` erases to `B`'s
    finalized block and has `B`'s finalized height. -/
theorem specDraft_finalized_ancestor_height :
    ∀ (E : Env V) (cfg : HeightConfig) (B : NamedBlock V),
      ((Model.specDraft (V := V)).derive_named E cfg B).h_F = 0 ∨
        ∃ F : NamedBlock V, NamedBlock.Preceq F B ∧
          F.erase = ((Model.specDraft (V := V)).derive_named E cfg B).F ∧
          ((Model.specDraft (V := V)).derive_named E cfg F).h = ((Model.specDraft (V := V)).derive_named E cfg B).h_F := by
  sd_simp
  exact (Model.vocabulary_facts_csAdded (V := V)).finalized_ancestor_height

/-- At `Model.specDraft`, after the transition of `st` by `B`, the height is `h(st)` and the entry
    is `T_h(st)`, or the height is `h(st) + 1` and the entry is `B`'s erasure. -/
theorem specDraft_transition_height_entry_cases :
    ∀ (E : Env V) (cfg : HeightConfig) (st : (Model.specDraft (V := V)).CS)
      (B : NamedBlock V),
      (((Model.specDraft (V := V)).named_transition E cfg st B).h = st.h ∧ ((Model.specDraft (V := V)).named_transition E cfg st B).T_h = st.T_h) ∨
        (((Model.specDraft (V := V)).named_transition E cfg st B).h = st.h + 1 ∧
          ((Model.specDraft (V := V)).named_transition E cfg st B).T_h = B.erase) := by
  intro E cfg st B
  sd_simp
  exact (Model.vocabulary_facts_csAdded (V := V)).transition_height_entry_cases E cfg (Spec.Protocol.ChainState.toProof (V := V) st) B

/-- At `Model.specDraft`, if `h(node parent …) ≠ h(parent)`, then some quorum `Q` has, for each
    signer in `Q`, an attestation by that signer, included in an ancestor of `node parent …`, whose
    height pair matches `(h(parent), T_h(parent).root)`. -/
theorem specDraft_crossing_matching_quorum :
    ∀ (E : Env V) (cfg : HeightConfig) (parent : NamedBlock V)
      (slot : Slot) (root : BlockId) (votes support : List (GoldfishVote V))
      (rows : List (NamedAttestation V)) (proposer : V),
      ((Model.specDraft (V := V)).derive_named E cfg (.node parent slot root votes support rows proposer)).h ≠
          ((Model.specDraft (V := V)).derive_named E cfg parent).h →
        ∃ Q : Finset V, E.electorate.IsQuorum Q ∧
          ∀ signer ∈ Q, ∃ carrier : NamedBlock V, ∃ a : NamedAttestation V,
            NamedBlock.Preceq carrier (.node parent slot root votes support rows proposer) ∧
            a ∈ carrier.attestations ∧ a.val_index = signer ∧
            a.height_pair.matchesEntry ((Model.specDraft (V := V)).derive_named E cfg parent).h
              ((Model.specDraft (V := V)).derive_named E cfg parent).T_h.root = true := by
  sd_simp
  exact (Model.vocabulary_facts_csAdded (V := V)).crossing_matching_quorum

/-- At `Model.specDraft`, if `H` is a recovery height for `h_F0` and every ancestor of `B` has
    finalized height at most `h_F0`, then `h_j(B) ≠ H`. -/
theorem specDraft_h_j_ne_recovery_height_named :
    ∀ (E : Env V) (cfg : HeightConfig) {h_F0 H : Height},
      Proofs.NjGap.RecoveryHeight cfg h_F0 H → ∀ B : NamedBlock V,
        (∀ C : NamedBlock V, NamedBlock.Preceq C B → ((Model.specDraft (V := V)).derive_named E cfg C).h_F ≤ h_F0) →
          ((Model.specDraft (V := V)).derive_named E cfg B).h_j ≠ H := by
  sd_simp
  exact (Model.vocabulary_facts_csAdded (V := V)).h_j_ne_recovery_height_named

/-- At `Model.specDraft`, `T_h(B)` is an ancestor of `B`'s erasure. -/
theorem specDraft_derive_named_T_h_preceq :
    ∀ (E : Env V) (cfg : HeightConfig) (B : NamedBlock V),
      Block.Preceq ((Model.specDraft (V := V)).derive_named E cfg B).T_h B.erase := by
  sd_simp
  exact (Model.vocabulary_facts_csAdded (V := V)).derive_named_T_h_preceq

/-- If `a`'s height pair matches `(h, X)` and `X ≠ T`, then the height pair of `a`'s erasure
    conflicts with the finality pair `(h, T)`. -/
theorem specDraft_conflictsWithFinality_erase_of_matchesEntry :
    ∀ {a : NamedAttestation V} {h : Height}
      {X T : BlockId}, a.height_pair.matchesEntry h X = true → X ≠ T →
        (Model.specDraft (V := V)).conflictsWithFinality a.erase.height_pair ⟨h, T⟩ = true :=
  (Model.vocabulary_facts_csAdded (V := V)).conflictsWithFinality_erase_of_matchesEntry

/-- At `Model.specDraft`, if `σ` passes the justification test, its target-participation set is a
    quorum. -/
theorem specDraft_isQuorum_of_targetReady :
    ∀ {σ : (Model.specDraft (V := V)).CS} (E : Env V), (Model.specDraft (V := V)).targetReady E σ = true →
      E.electorate.IsQuorum σ.target_participation := by
  sd_simp
  exact (Model.vocabulary_facts_csAdded (V := V)).isQuorum_of_targetReady

/-- At `Model.specDraft`, if `Pc` is not genesis, `Pm ⪯ parent(Pc)`, `h(Pm) = h(Pc)`, and, when
    `parent(Pc)` has the height `h(Pc)` and the entry `T_h(Pm)`, some quorum's members are each in
    the parent's progress set or sign a row of `Pc` matching the parent's height and entry, then
    `Pc.slot < T_h(Pc).slot + timeoutDelay`. -/
theorem specDraft_climb_entryYoung_l85 :
    ∀ (E : Env V) (cfg : HeightConfig) {Pm Pc : NamedBlock V},
      Pc ≠ .genesis → NamedBlock.Preceq Pm Pc.parent →
      ((Model.specDraft (V := V)).derive_named E cfg Pm).h = ((Model.specDraft (V := V)).derive_named E cfg Pc).h →
      (((Model.specDraft (V := V)).derive_named E cfg Pc.parent).h = ((Model.specDraft (V := V)).derive_named E cfg Pc).h →
        ((Model.specDraft (V := V)).derive_named E cfg Pc.parent).T_h = ((Model.specDraft (V := V)).derive_named E cfg Pm).T_h →
        ∃ Q : Finset V, E.electorate.IsQuorum Q ∧ ∀ i ∈ Q,
          i ∈ ((Model.specDraft (V := V)).derive_named E cfg Pc.parent).progress ∨
            ∃ a ∈ Pc.attestations, a.val_index = i ∧
              a.height_pair.matchesEntry ((Model.specDraft (V := V)).derive_named E cfg Pc.parent).h
                ((Model.specDraft (V := V)).derive_named E cfg Pc.parent).T_h.root = true) →
      Pc.slot < ((Model.specDraft (V := V)).derive_named E cfg Pc).T_h.slot + cfg.timeoutDelay := by
  sd_simp
  exact (Model.vocabulary_facts_csAdded (V := V)).climb_entryYoung_l85

/-- At `Model.specDraft`, for a block `B` other than genesis, `F(B)` is `F(parent(B))` or
    `J(parent(B))`. -/
theorem specDraft_derive_named_F_cases :
    ∀ (E : Env V) (cfg : HeightConfig) {B : NamedBlock V},
      B ≠ .genesis →
        ((Model.specDraft (V := V)).derive_named E cfg B).F = ((Model.specDraft (V := V)).derive_named E cfg B.parent).F ∨
          ((Model.specDraft (V := V)).derive_named E cfg B).F = ((Model.specDraft (V := V)).derive_named E cfg B.parent).J := by
  sd_simp
  exact (Model.vocabulary_facts_csAdded (V := V)).derive_named_F_cases

/-- At `Model.specDraft`, `F(genesis) = genesis`. -/
theorem specDraft_derive_named_genesis_F :
    ∀ (E : Env V) (cfg : HeightConfig),
      ((Model.specDraft (V := V)).derive_named E cfg (.genesis : NamedBlock V)).F = Block.genesis := by
  sd_simp
  exact (Model.vocabulary_facts_csAdded (V := V)).derive_named_genesis_F

/-- At `Model.specDraft`, `h_j(genesis) = 0`. -/
theorem specDraft_Sts_derive_named_genesis_h_j :
    ∀ (E : Env V) (cfg : HeightConfig),
      ((Model.specDraft (V := V)).derive_named E cfg (.genesis : NamedBlock V)).h_j = 0 := by
  sd_simp
  exact (Model.vocabulary_facts_csAdded (V := V)).Sts_derive_named_genesis_h_j

/-- At `Model.specDraft`, if `A ⪯ B`, then `h_j(A) ≤ h_j(B)`. -/
theorem specDraft_derive_named_h_j_mono :
    ∀ (E : Env V) (cfg : HeightConfig) {A B : NamedBlock V},
      NamedBlock.Preceq A B → ((Model.specDraft (V := V)).derive_named E cfg A).h_j ≤ ((Model.specDraft (V := V)).derive_named E cfg B).h_j := by
  sd_simp
  exact (Model.vocabulary_facts_csAdded (V := V)).derive_named_h_j_mono

/-- At `Model.specDraft`, if `h(B) ≥ 2`, then some ancestor `N` of `B` has `h(N) = h(B)` and
    `h(N) = h(parent(N)) + 1`. -/
theorem specDraft_exists_crossing_ancestor :
    ∀ (E : Env V) (cfg : HeightConfig) (B : NamedBlock V),
      2 ≤ ((Model.specDraft (V := V)).derive_named E cfg B).h →
        ∃ N : NamedBlock V, NamedBlock.Preceq N B ∧
          ((Model.specDraft (V := V)).derive_named E cfg N).h = ((Model.specDraft (V := V)).derive_named E cfg B).h ∧
          ((Model.specDraft (V := V)).derive_named E cfg N).h = ((Model.specDraft (V := V)).derive_named E cfg N.parent).h + 1 := by
  sd_simp
  exact (Model.vocabulary_facts_csAdded (V := V)).exists_crossing_ancestor

/-- At `Model.specDraft`, if `h_F(D) ≠ 0`, there are ancestors `Fn` and `X` of `D` with `Fn`'s
    erasure equal to `F(D)`, `h(Fn) = h_F(D)`, `T_h(Fn)` equal to `Fn`'s erasure, `h(X) = h_F(D)`,
    and a quorum `Q` each of whose members has an attestation, included in an ancestor of `D`, whose
    height pair is a vote at height `h_F(D)` for `X`'s root. -/
theorem specDraft_finalized_entry_quorum :
    ∀ (E : Env V) (cfg : HeightConfig) (D : NamedBlock V),
      ((Model.specDraft (V := V)).derive_named E cfg D).h_F ≠ 0 →
        ∃ Fn X : NamedBlock V, NamedBlock.Preceq Fn D ∧ NamedBlock.Preceq X D ∧
          Fn.erase = ((Model.specDraft (V := V)).derive_named E cfg D).F ∧
          ((Model.specDraft (V := V)).derive_named E cfg Fn).h = ((Model.specDraft (V := V)).derive_named E cfg D).h_F ∧
          ((Model.specDraft (V := V)).derive_named E cfg Fn).T_h = Fn.erase ∧
          ((Model.specDraft (V := V)).derive_named E cfg X).h = ((Model.specDraft (V := V)).derive_named E cfg D).h_F ∧
          ∃ Q : Finset V, E.electorate.IsQuorum Q ∧ ∀ signer ∈ Q,
            ∃ (carrier : NamedBlock V) (a : NamedAttestation V) (tmo : Bool),
              NamedBlock.Preceq carrier D ∧ a ∈ carrier.attestations ∧ a.val_index = signer ∧
              a.height_pair = NamedHeightPair.vote ((Model.specDraft (V := V)).derive_named E cfg D).h_F X.root tmo := by
  sd_simp
  exact (Model.vocabulary_facts_csAdded (V := V)).finalized_entry_quorum

/-- At `Model.specDraft`, `h_F(D) = 0`, or some ancestor `Fn` of `D` erases to `F(D)`, has
    `h(Fn) = h_F(D)`, and has `T_h(Fn)` equal to `Fn`'s erasure. -/
theorem specDraft_finalized_is_entry :
    ∀ (E : Env V) (cfg : HeightConfig) (D : NamedBlock V),
      ((Model.specDraft (V := V)).derive_named E cfg D).h_F = 0 ∨
        ∃ Fn : NamedBlock V, NamedBlock.Preceq Fn D ∧
          Fn.erase = ((Model.specDraft (V := V)).derive_named E cfg D).F ∧
          ((Model.specDraft (V := V)).derive_named E cfg Fn).h = ((Model.specDraft (V := V)).derive_named E cfg D).h_F ∧
          ((Model.specDraft (V := V)).derive_named E cfg Fn).T_h = Fn.erase := by
  sd_simp
  exact (Model.vocabulary_facts_csAdded (V := V)).finalized_is_entry

/-- At `Model.specDraft`, if `h_j(B) ≤ h_F(B)`, then `J(B)` is an ancestor of `F(B)`. -/
theorem specDraft_justified_preceq_finalized_of_le_f1b1 :
    ∀ (E : Env V) (cfg : HeightConfig) (B : NamedBlock V),
      ((Model.specDraft (V := V)).derive_named E cfg B).h_j ≤ ((Model.specDraft (V := V)).derive_named E cfg B).h_F →
        Block.Preceq ((Model.specDraft (V := V)).derive_named E cfg B).J ((Model.specDraft (V := V)).derive_named E cfg B).F := by
  sd_simp
  exact (Model.vocabulary_facts_csAdded (V := V)).justified_preceq_finalized_of_le_f1b1

/-- At `Model.specDraft`, if `A ⪯ B` and `h(A) = h(B)`, then `nj(A) = nj(B)`. -/
theorem specDraft_nj_eq_on_plateau_l85 :
    ∀ (E : Env V) (cfg : HeightConfig) {A B : NamedBlock V},
      NamedBlock.Preceq A B → ((Model.specDraft (V := V)).derive_named E cfg A).h = ((Model.specDraft (V := V)).derive_named E cfg B).h →
        ((Model.specDraft (V := V)).derive_named E cfg A).nj = ((Model.specDraft (V := V)).derive_named E cfg B).nj := by
  sd_simp
  exact (Model.vocabulary_facts_csAdded (V := V)).nj_eq_on_plateau_l85

/-- At `Model.specDraft`, if `K` does not divide `h(B)`, then `nj(B) = false`. -/
theorem specDraft_nj_false_of_not_dvd_l85 :
    ∀ (E : Env V) (cfg : HeightConfig) (B : NamedBlock V),
      ¬ cfg.K ∣ ((Model.specDraft (V := V)).derive_named E cfg B).h → ((Model.specDraft (V := V)).derive_named E cfg B).nj = false := by
  sd_simp
  exact (Model.vocabulary_facts_csAdded (V := V)).nj_false_of_not_dvd_l85

/-- At `Model.specDraft`, if slots increase along `Z`'s chain, `A ⪯ Z`, `1 ≤ k`, `h_j(Z) < h(A)`, no
    `h(A) + j` with `1 ≤ j < k` is a multiple of `K`, and `h(A) + k ≤ h(Z)`, then
    `A.slot + 1 + (k − 1)·timeoutDelay ≤ Z.slot`. -/
theorem specDraft_progress_spacing_l85 :
    ∀ (E : Env V) (cfg : HeightConfig) {A Z : NamedBlock V},
      (∀ X : NamedBlock V, NamedBlock.Preceq X Z → X ≠ .genesis → X.parent.slot < X.slot) →
      NamedBlock.Preceq A Z → ∀ {k : Nat}, 1 ≤ k →
      ((Model.specDraft (V := V)).derive_named E cfg Z).h_j < ((Model.specDraft (V := V)).derive_named E cfg A).h →
      (∀ j : Nat, 1 ≤ j → j < k → ¬ cfg.K ∣ ((Model.specDraft (V := V)).derive_named E cfg A).h + j) →
      ((Model.specDraft (V := V)).derive_named E cfg A).h + k ≤ ((Model.specDraft (V := V)).derive_named E cfg Z).h →
      A.slot + 1 + (k - 1) * cfg.timeoutDelay ≤ Z.slot := by
  sd_simp
  exact (Model.vocabulary_facts_csAdded (V := V)).progress_spacing_l85

/-- At `Model.specDraft`, the latest block of the transition of `st` by `B` is `B`'s erasure. -/
theorem specDraft_named_transition_latest :
    ∀ (E : Env V) (cfg : HeightConfig) (st : (Model.specDraft (V := V)).CS) (B : NamedBlock V),
      (Model.specDraft (V := V)).L ((Model.specDraft (V := V)).named_transition E cfg st B) = B.erase := by
  intro E cfg st B
  sd_simp
  exact (Model.vocabulary_facts_csAdded (V := V)).named_transition_latest E cfg (Spec.Protocol.ChainState.toProof (V := V) st) B

/-- At `Model.specDraft`, the `finalize` set after applying `row` through the targeted
    interpretation equals the `finalize` set after applying `row`'s erasure directly. -/
theorem specDraft_process_finality_eq :
    ∀ (st : (Model.specDraft (V := V)).CS) (row : NamedAttestation V),
      (Model.specDraft (V := V)).finalize ((Model.specDraft (V := V)).process_attestation_with (Model.specDraft (V := V)).targeted st row) =
        (Model.specDraft (V := V)).finalize ((Model.specDraft (V := V)).process_attestation st row.erase) := by
  intro st row
  rw [SpecDraftRecord.specDraft_finalize_process_attestation]
  sd_simp
  exact (Model.vocabulary_facts_csAdded (V := V)).process_finality_eq (Spec.Protocol.ChainState.toProof (V := V) st) row

/-- At `Model.specDraft`, after one row applied through any interpretation, `L`, `h`, `T_h`, `J`,
    `h_j`, `F` and `h_F` are those of `st`. -/
theorem specDraft_process_context_fields :
    ∀ {Row : Type} (binding : (Model.specDraft (V := V)).Binding Row) (st : (Model.specDraft (V := V)).CS) (row : Row),
      (Model.specDraft (V := V)).L ((Model.specDraft (V := V)).process_attestation_with binding st row) = (Model.specDraft (V := V)).L st ∧
        ((Model.specDraft (V := V)).process_attestation_with binding st row).h = st.h ∧
        ((Model.specDraft (V := V)).process_attestation_with binding st row).T_h = st.T_h ∧
        ((Model.specDraft (V := V)).process_attestation_with binding st row).J = st.J ∧
        ((Model.specDraft (V := V)).process_attestation_with binding st row).h_j = st.h_j ∧
        ((Model.specDraft (V := V)).process_attestation_with binding st row).F = st.F ∧
        ((Model.specDraft (V := V)).process_attestation_with binding st row).h_F = st.h_F := by
  intro Row b st row
  sd_simp
  exact (Model.vocabulary_facts_csAdded (V := V)).process_context_fields (Protocol.TimeoutBinding.targeted V) (Spec.Protocol.ChainState.toProof (V := V) st)
    (Spec.Attestation.toProofNamed (V := V) (b row))

/-- At `Model.specDraft`, if `σ` passes the finality test, its `finalize` set is a quorum. -/
theorem specDraft_isQuorum_of_finalityReady :
    ∀ {σ : (Model.specDraft (V := V)).CS} (E : Env V), (Model.specDraft (V := V)).finalityReady E σ = true →
      E.electorate.IsQuorum ((Model.specDraft (V := V)).finalize σ) := by
  sd_simp
  exact (Model.vocabulary_facts_csAdded (V := V)).isQuorum_of_finalityReady

/-- At `Model.specDraft`, `J(advance_height cfg σ) = J(σ)`. -/
theorem specDraft_advance_height_J :
    ∀ {cfg : HeightConfig} {σ : (Model.specDraft (V := V)).CS}, ((Model.specDraft (V := V)).advance_height cfg σ).J = σ.J := by
  sd_simp
  exact (Model.vocabulary_facts_csAdded (V := V)).advance_height_J

/-- At `Model.specDraft`, `h_j(advance_height cfg σ) = h_j(σ)`. -/
theorem specDraft_advance_height_h_j :
    ∀ {cfg : HeightConfig} {σ : (Model.specDraft (V := V)).CS}, ((Model.specDraft (V := V)).advance_height cfg σ).h_j = σ.h_j := by
  sd_simp
  exact (Model.vocabulary_facts_csAdded (V := V)).advance_height_h_j

/-- At `Model.specDraft`, `h(advance_height cfg σ) = h(σ) + 1`. -/
theorem specDraft_advance_height_h :
    ∀ {cfg : HeightConfig} {σ : (Model.specDraft (V := V)).CS}, ((Model.specDraft (V := V)).advance_height cfg σ).h = σ.h + 1 := by
  sd_simp
  exact (Model.vocabulary_facts_csAdded (V := V)).advance_height_h

/-- At `Model.specDraft`, `left` and `right` are not slashable iff `slashable left right = false`. -/
theorem specDraft_not_Slashable_iff :
    ∀ (left right : CombinedAttestation V),
      ¬ (Model.specDraft (V := V)).Slashable left right ↔ (Model.specDraft (V := V)).slashable left right = false :=
  (Model.vocabulary_facts_csAdded (V := V)).not_Slashable_iff

/-- At `Model.specDraft`, `a` and `b` are slashable iff `slashable a b = true`. -/
theorem specDraft_Slashable_iff :
    ∀ {a b : CombinedAttestation V}, (Model.specDraft (V := V)).Slashable a b ↔ (Model.specDraft (V := V)).slashable a b = true :=
  (Model.vocabulary_facts_csAdded (V := V)).Slashable_iff

/-- At `Model.specDraft`, if `K` divides `h` and `D < h − h_F`, then
    `nonjustifiable cfg h h_F = true`. -/
theorem specDraft_nonjustifiable_of :
    ∀ {cfg : HeightConfig} {h h_F : Height},
      cfg.K ∣ h → cfg.D < h - h_F → (Model.specDraft (V := V)).nonjustifiable cfg h h_F = true := by
  sd_simp
  exact (Model.vocabulary_facts_csAdded (V := V)).nonjustifiable_of

/-- At `Model.specDraft`, if `h_F ≤ cap` and `h` is nonjustifiable given `cap`, then `h` is
    nonjustifiable given `h_F`. -/
theorem specDraft_nonjustifiable_of_le :
    ∀ {cfg : HeightConfig} {h h_F cap : Height},
      h_F ≤ cap → (Model.specDraft (V := V)).nonjustifiable cfg h cap = true → (Model.specDraft (V := V)).nonjustifiable cfg h h_F = true := by
  sd_simp
  exact (Model.vocabulary_facts_csAdded (V := V)).nonjustifiable_of_le

/-- At `Model.specDraft`, if no finality pair of `left` conflicts with `right`'s height pair and no
    finality pair of `right` conflicts with `left`'s height pair, then
    `e1Fields left right = false`. -/
theorem specDraft_e1Fields_eq_false_of :
    ∀ (left right : CombinedAttestation V),
      (∀ p : FinalityPair, left.finality_pair = some p →
        (Model.specDraft (V := V)).conflictsWithFinality right.height_pair p = false) →
      (∀ q : FinalityPair, right.finality_pair = some q →
        (Model.specDraft (V := V)).conflictsWithFinality left.height_pair q = false) →
      (Model.specDraft (V := V)).e1Fields left right = false :=
  (Model.vocabulary_facts_csAdded (V := V)).e1Fields_eq_false_of

/-- At `Model.specDraft`, if `e1Fields left right = false` and `e2Fields left right = false`, then
    `slashable left right = false`. -/
theorem specDraft_slashable_eq_false_of_fields :
    ∀ (left right : CombinedAttestation V),
      (Model.specDraft (V := V)).e1Fields left right = false → (Model.specDraft (V := V)).e2Fields left right = false →
        (Model.specDraft (V := V)).slashable left right = false :=
  (Model.vocabulary_facts_csAdded (V := V)).slashable_eq_false_of_fields

/-- At `Model.specDraft`, the height of the initial chain state is `1`. -/
theorem specDraft_chainState_initial_h :
    ((Model.specDraft (V := V)).cs_initial).h = 1 := by
  sd_simp
  exact (Model.vocabulary_facts_csAdded (V := V)).chainState_initial_h

/-- At `Model.specDraft`, the chain state derived for `B` in the environment `S.E` with its GST
    replaced by `g` is the one derived in `S.E`. -/
theorem specDraft_derive_named_setupWithGST :
    ∀ (S : Setup V) (g : Int) (hg : 0 ≤ g) (B : NamedBlock V),
      (Model.specDraft (V := V)).derive_named { S.E with t_GST := g, t_GST_nonneg := hg } S.cfg B =
        (Model.specDraft (V := V)).derive_named S.E S.cfg B := by
  intro S g hg B
  induction B with
  | genesis => rfl
  | node p s root votes support rows proposer ih =>
    rw [specDraft_derive_named_node, specDraft_derive_named_node, ih]
    rfl

/-- At `Model.specDraft`, if `B` is not genesis, the chain state of `B`'s parent has justified
    height `h` and justified block `J`, some quorum `Q` has each member in that chain state's
    finality set or signing a row of `B` with finality pair `(h, J.root)`, and the parent's
    finalized height is less than `h`, then the chain state derived for `B` has finalized block `J`
    at finalized height `h`. -/
theorem specDraft_namedFinalizedAt_of_finalityQuorumCoveredByChild : ∀ (E : Env V) (cfg : HeightConfig)
    {B : NamedBlock V} {J : Block V} {h : Height},
    B ≠ NamedBlock.genesis →
    (((Model.specDraft (V := V)).derive_named E cfg B.parent).h_j = h ∧ ((Model.specDraft (V := V)).derive_named E cfg B.parent).J = J ∧
      ∃ Q : Finset V, E.electorate.IsQuorum Q ∧
        ∀ i ∈ Q,
          i ∈ (Model.specDraft (V := V)).finalize ((Model.specDraft (V := V)).derive_named E cfg B.parent) ∨
          ∃ a ∈ B.attestations,
            a.val_index = i ∧
            a.finality_pair = some ⟨h, J.root⟩) →
    ((Model.specDraft (V := V)).derive_named E cfg B.parent).h_F < h →
    ((Model.specDraft (V := V)).derive_named E cfg B).F = J ∧ ((Model.specDraft (V := V)).derive_named E cfg B).h_F = h := by
  sd_simp
  exact (Model.vocabulary_facts_csAdded (V := V)).namedFinalizedAt_of_finalityQuorumCoveredByChild

/-- At `Model.specDraft`, if `B` is not genesis, some quorum `Q` has each member in the target
    participation of the chain state of `B`'s parent or signing a row of `B` that is the target vote
    for that chain state's height and entry, and that chain state's `nj` bit is clear, then the
    chain state derived for `B` has the parent's entry as its justified block, the parent's height
    as its justified height, and the parent's height plus one as its height. -/
theorem specDraft_namedJustifiedAt_of_targetQuorumCoveredByChild : ∀ (E : Env V) (cfg : HeightConfig)
    {B : NamedBlock V},
    B ≠ NamedBlock.genesis →
    (∃ Q : Finset V, E.electorate.IsQuorum Q ∧
      ∀ i ∈ Q,
        i ∈ ((Model.specDraft (V := V)).derive_named E cfg B.parent).target_participation ∨
        ∃ a ∈ B.attestations,
          a.val_index = i ∧
          a.height_pair = NamedHeightPair.vote ((Model.specDraft (V := V)).derive_named E cfg B.parent).h
            ((Model.specDraft (V := V)).derive_named E cfg B.parent).T_h.root false) →
    ((Model.specDraft (V := V)).derive_named E cfg B.parent).nj = false →
    (((Model.specDraft (V := V)).derive_named E cfg B).J = ((Model.specDraft (V := V)).derive_named E cfg B.parent).T_h ∧
      ((Model.specDraft (V := V)).derive_named E cfg B).h_j = ((Model.specDraft (V := V)).derive_named E cfg B.parent).h) ∧
    ((Model.specDraft (V := V)).derive_named E cfg B).h = ((Model.specDraft (V := V)).derive_named E cfg B.parent).h + 1 := by
  sd_simp
  exact (Model.vocabulary_facts_csAdded (V := V)).namedJustifiedAt_of_targetQuorumCoveredByChild

/-- At `Model.specDraft`, the finalized block of `B`'s chain state is an ancestor of, or equal to,
    its justified block. -/
theorem specDraft_derive_named_finalized_preceq_justified : ∀ (E : Env V) (cfg : HeightConfig)
    (B : NamedBlock V),
    Block.preceq ((Model.specDraft (V := V)).derive_named E cfg B).F ((Model.specDraft (V := V)).derive_named E cfg B).J = true := by
  sd_simp
  exact (Model.vocabulary_facts_csAdded (V := V)).derive_named_finalized_preceq_justified

/-- At `Model.specDraft`, if slots increase along `P2`'s chain, `Pc` and `P2` are not genesis,
    `Pc`'s `nj` bit is clear, `Pm ⪯ parent(Pc)`, `Pm` is at slot `om`, `Pc ⪯ parent(P2)`,
    `parent(P2).slot + 1 ≤ om + timeoutDelay`, and, when `parent(P2)` has the height and entry of
    `Pc`, some quorum's members are each in `parent(P2)`'s target participation or sign a row of
    `P2` that is the target vote for `parent(P2)`'s height and entry, and, when `Pm` and
    `parent(Pc)` have the height of `Pc` and `parent(Pc)` the entry of `Pm`, some quorum's members
    are each in `parent(Pc)`'s target participation or sign a row of `Pc` that is the target vote
    for `parent(Pc)`'s height and entry, then `h(Pc) ≤ h_j(P2)`. -/
theorem specDraft_windowJustified_l85d : ∀ (E : Env V) (cfg : HeightConfig) {Pm Pc P2 : NamedBlock V} {om : Slot},
    (∀ X : NamedBlock V, NamedBlock.Preceq X P2 → X ≠ .genesis → X.parent.slot < X.slot) →
    Pc ≠ .genesis → P2 ≠ .genesis →
    ((Model.specDraft (V := V)).derive_named E cfg Pc).nj = false →
    NamedBlock.Preceq Pm Pc.parent → Pm.slot = om →
    NamedBlock.Preceq Pc P2.parent →
    P2.parent.slot + 1 ≤ om + cfg.timeoutDelay →
    (((Model.specDraft (V := V)).derive_named E cfg P2.parent).h = ((Model.specDraft (V := V)).derive_named E cfg Pc).h →
      ((Model.specDraft (V := V)).derive_named E cfg P2.parent).T_h = ((Model.specDraft (V := V)).derive_named E cfg Pc).T_h →
      ∃ Q : Finset V, E.electorate.IsQuorum Q ∧ ∀ i ∈ Q,
        i ∈ ((Model.specDraft (V := V)).derive_named E cfg P2.parent).target_participation ∨
          ∃ a ∈ P2.attestations, a.val_index = i ∧
            a.height_pair = NamedHeightPair.vote ((Model.specDraft (V := V)).derive_named E cfg P2.parent).h
              ((Model.specDraft (V := V)).derive_named E cfg P2.parent).T_h.root false) →
    (((Model.specDraft (V := V)).derive_named E cfg Pm).h = ((Model.specDraft (V := V)).derive_named E cfg Pc).h →
      ((Model.specDraft (V := V)).derive_named E cfg Pc.parent).h = ((Model.specDraft (V := V)).derive_named E cfg Pc).h →
      ((Model.specDraft (V := V)).derive_named E cfg Pc.parent).T_h = ((Model.specDraft (V := V)).derive_named E cfg Pm).T_h →
      ∃ Q : Finset V, E.electorate.IsQuorum Q ∧ ∀ i ∈ Q,
        i ∈ ((Model.specDraft (V := V)).derive_named E cfg Pc.parent).target_participation ∨
          ∃ a ∈ Pc.attestations, a.val_index = i ∧
            a.height_pair = NamedHeightPair.vote ((Model.specDraft (V := V)).derive_named E cfg Pc.parent).h
              ((Model.specDraft (V := V)).derive_named E cfg Pc.parent).T_h.root false) →
    ((Model.specDraft (V := V)).derive_named E cfg Pc).h ≤ ((Model.specDraft (V := V)).derive_named E cfg P2).h_j := by
  sd_simp
  exact (Model.vocabulary_facts_csAdded (V := V)).windowJustified_l85d

/-- At `Model.specDraft`, if `C ⪯ P`, the attestation `a` is on `P`'s named chain and not on `C`'s,
    `P` and `C` have the same chain-state height, and `a`'s height pair is a vote or a timeout for
    `C`'s height and entry root, then `a`'s signer is in `P`'s progress set. -/
theorem specDraft_namedPair_mem_progress_of_suffix_same_height : ∀ (E : Env V) (cfg : HeightConfig)
    {C P : NamedBlock V} {a : NamedAttestation V},
    NamedBlock.Preceq C P → a ∈ Protocol.named_chain_attestations P →
    a ∉ Protocol.named_chain_attestations C →
    ((Model.specDraft (V := V)).derive_named E cfg P).h = ((Model.specDraft (V := V)).derive_named E cfg C).h →
    (a.height_pair = .vote ((Model.specDraft (V := V)).derive_named E cfg C).h ((Model.specDraft (V := V)).derive_named E cfg C).T_h.root false ∨
      a.height_pair = .vote ((Model.specDraft (V := V)).derive_named E cfg C).h ((Model.specDraft (V := V)).derive_named E cfg C).T_h.root true) →
    a.val_index ∈ ((Model.specDraft (V := V)).derive_named E cfg P).progress := by
  sd_simp
  exact (Model.vocabulary_facts_csAdded (V := V)).namedPair_mem_progress_of_suffix_same_height

/-- At `Model.specDraft`, if `C ⪯ P`, the attestation `a` is on `P`'s named chain and not on `C`'s,
    `P` and `C` have the same chain-state height, and `a`'s height pair is a vote for `C`'s height
    and entry root, then `a`'s signer is in `P`'s target participation set. -/
theorem specDraft_namedTarget_mem_of_suffix_same_height : ∀ (E : Env V) (cfg : HeightConfig)
    {C P : NamedBlock V} {a : NamedAttestation V},
    NamedBlock.Preceq C P → a ∈ Protocol.named_chain_attestations P →
    a ∉ Protocol.named_chain_attestations C →
    ((Model.specDraft (V := V)).derive_named E cfg P).h = ((Model.specDraft (V := V)).derive_named E cfg C).h →
    a.height_pair = .vote ((Model.specDraft (V := V)).derive_named E cfg C).h ((Model.specDraft (V := V)).derive_named E cfg C).T_h.root false →
    a.val_index ∈ ((Model.specDraft (V := V)).derive_named E cfg P).target_participation := by
  sd_simp
  exact (Model.vocabulary_facts_csAdded (V := V)).namedTarget_mem_of_suffix_same_height

/-- At `Model.specDraft`, if `A` is an ancestor of `B`, or `B` itself, and the outcome of the grade
    test of round `r` at phase `p` over the grade view `gv` for `B` is `true`, then the outcome of
    the same test for `A` is `true`. -/
theorem specDraft_confirmation_phaseGrade_mono : ∀ (E : Env V) (hc : Protocol.HealConfig) (gv : (Model.specDraft (V := V)).GV) (F : Block V)
    (r : Round) (p : Protocol.Phase) {A B : Block V}, Block.Preceq A B →
    ∀ bB : Bool, (Model.specDraft (V := V)).gradeBool E gv F hc.η_SG r ((Model.specDraft (V := V)).early E hc r p) ((Model.specDraft (V := V)).late E hc r p) B ⇢ bB →
    bB = true →
    ∀ bA : Bool, (Model.specDraft (V := V)).gradeBool E gv F hc.η_SG r ((Model.specDraft (V := V)).early E hc r p) ((Model.specDraft (V := V)).late E hc r p) A ⇢ bA →
    bA = true := by
  intro E hc gv F r p A B hAB bB hbB hB bA hbA
  rw [ContractImages.early_eq, ContractImages.late_eq,
    GradesImages.specDraft_gradeBool_eq] at hbB hbA
  exact (Model.vocabulary_facts_csAdded (V := V)).confirmation_phaseGrade_mono E hc _ F r p hAB bB
    hbB hB bA hbA

end SpecDraftRecord.ChainStateAddedFacts

namespace DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-- `Model.specDraft` satisfies `ChainStateAddedRunFacts`, which has no field. -/
theorem Model.specDraft_runFacts_csAdded :
    ChainStateAddedRunFacts (Model.specDraft (V := V)) where

end DecoupledConsensusModel.Sts.Record
