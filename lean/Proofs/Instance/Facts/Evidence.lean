import Proofs.Instance.Model
import Proofs.Vocabulary.ModelVocabularyFacts

/-!
# The evidence facts at `Model.spec`

The fields of `EvidenceFacts` proved at `Model.spec`, and the bundles
`Model.spec_facts_evidence` and `Model.spec_runFacts_evidence`.
-/

set_option autoImplicit false

namespace SpecRecord.EvidenceFacts

open DecoupledConsensusModel
open DecoupledConsensusModel.Sts
open DecoupledConsensusModel.Sts.Record
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Protocol (HeightConfig)

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-- If the set `H` of validators weighs less than one third under the setup `S`, and the set `X` has
    the weight of an intersection of two quorums of `S`'s environment, then some validator of `X` is
    in `H`. -/
theorem spec_no_faulty_intersection :
    ∀ {S : DecoupledConsensusModel.Execution.Setup V} {H X : Finset V}, DecoupledConsensusModel.Execution.BelowOneThird S H → (Model.spec (V := V)).HasIntersectionWeight S.E X → (∀ i ∈ X, i ∉ H) → False :=
  (Model.vocabulary_facts_evidence (V := V)).no_faulty_intersection

/-- If the evidence sets `A₁` and `A₂` have slashable weight, some set `Q` of validators has
    together the weight of an intersection of two quorums, and every validator of `Q` is slashable
    between `A₁` and `A₂`. -/
theorem spec_hasSlashableWeightBetween_elim :
    ∀ {E : DecoupledConsensusModel.Env V} {A₁ A₂ : Finset (DecoupledConsensusModel.CombinedAttestation V)}, (Model.spec (V := V)).HasSlashableWeightBetween E A₁ A₂ → ∃ Q, (Model.spec (V := V)).HasIntersectionWeight E Q ∧ ∀ i ∈ Q, (Model.spec (V := V)).SlashableBetween A₁ A₂ i :=
  (Model.vocabulary_facts_evidence (V := V)).hasSlashableWeightBetween_elim

/-- If the validators of `Q` have together the weight of an intersection of two quorums, and every
    validator of `Q` is slashable between `A₁` and `A₂`, then the evidence sets `A₁` and `A₂` have
    slashable weight. -/
theorem spec_ModelProperties_hasSlashableWeightBetween_intro :
    ∀ {E : DecoupledConsensusModel.Env V} {A₁ A₂ : Finset (DecoupledConsensusModel.CombinedAttestation V)} (Q : Finset V), (Model.spec (V := V)).HasIntersectionWeight E Q → (∀ i ∈ Q, (Model.spec (V := V)).SlashableBetween A₁ A₂ i) → (Model.spec (V := V)).HasSlashableWeightBetween E A₁ A₂ :=
  (Model.vocabulary_facts_evidence (V := V)).ModelProperties_hasSlashableWeightBetween_intro

/-- If `i` is slashable between `A₁` and `A₂`, then some `a` in `A₁` and some `b` in `A₂` are both
    attestations of `i`, and `a` and `b` together are slashable. -/
theorem spec_slashableBetween_elim :
    ∀ {A₁ A₂ : Finset (DecoupledConsensusModel.CombinedAttestation V)} {i : V}, (Model.spec (V := V)).SlashableBetween A₁ A₂ i → ∃ a ∈ A₁, ∃ b ∈ A₂, a.val_index = i ∧ b.val_index = i ∧ (Model.spec (V := V)).Slashable a b :=
  (Model.vocabulary_facts_evidence (V := V)).slashableBetween_elim

/-- If `a` is in `A₁`, `b` is in `A₂`, both are attestations of the validator `i`, and `a` and `b`
    together are slashable, then `i` is slashable between `A₁` and `A₂`. -/
theorem spec_ModelProperties_slashableBetween_intro :
    ∀ {A₁ A₂ : Finset (DecoupledConsensusModel.CombinedAttestation V)} {i : V}, ∀ a ∈ A₁, ∀ b ∈ A₂, a.val_index = i → b.val_index = i → (Model.spec (V := V)).Slashable a b → (Model.spec (V := V)).SlashableBetween A₁ A₂ i :=
  (Model.vocabulary_facts_evidence (V := V)).ModelProperties_slashableBetween_intro

/-- If `Q` and `Q'` are quorums of the electorate of `E`, then `Q ∩ Q'` has the weight of an
    intersection of two quorums of `E`. -/
theorem spec_quorum_intersection :
    ∀ (E : DecoupledConsensusModel.Env V) {Q Q' : Finset V}, E.electorate.IsQuorum Q → E.electorate.IsQuorum Q' → (Model.spec (V := V)).HasIntersectionWeight E (Q ∩ Q') :=
  (Model.vocabulary_facts_evidence (V := V)).quorum_intersection

/-- If the validators of `Q` have together the weight of an intersection of two quorums, and every
    validator of `Q` is slashable between `A₁` and `A₂`, then the evidence sets `A₁` and `A₂` have
    slashable weight. -/
theorem spec_Sts_hasSlashableWeightBetween_intro :
    ∀ {E : DecoupledConsensusModel.Env V} {A₁ A₂ : Finset (DecoupledConsensusModel.CombinedAttestation V)} (Q : Finset V), (Model.spec (V := V)).HasIntersectionWeight E Q → (∀ i ∈ Q, (Model.spec (V := V)).SlashableBetween A₁ A₂ i) → (Model.spec (V := V)).HasSlashableWeightBetween E A₁ A₂ :=
  (Model.vocabulary_facts_evidence (V := V)).Sts_hasSlashableWeightBetween_intro

/-- If `a` is in `A₁`, `b` is in `A₂`, both are attestations of the validator `i`, and `a` and `b`
    together are slashable, then `i` is slashable between `A₁` and `A₂`. -/
theorem spec_Sts_slashableBetween_intro :
    ∀ {A₁ A₂ : Finset (DecoupledConsensusModel.CombinedAttestation V)} {i : V}, ∀ a ∈ A₁, ∀ b ∈ A₂, a.val_index = i → b.val_index = i → (Model.spec (V := V)).Slashable a b → (Model.spec (V := V)).SlashableBetween A₁ A₂ i :=
  (Model.vocabulary_facts_evidence (V := V)).Sts_slashableBetween_intro

/-- If the set `X` of validators has the weight of an intersection of two quorums of `E`, then the
    total weight of `E`'s electorate is at most three times the weight of `X`. -/
theorem spec_totalWeight_le_three_mul_weightOf_of_hasIntersectionWeight :
    ∀ {E : DecoupledConsensusModel.Env V} {X : Finset V}, (Model.spec (V := V)).HasIntersectionWeight E X → E.electorate.totalWeight ≤ 3 * E.electorate.weightOf X :=
  (Model.vocabulary_facts_evidence (V := V)).totalWeight_le_three_mul_weightOf_of_hasIntersectionWeight

/-- For every named block `D`, every named block `carrier` with `carrier ⪯ D`, and every named
    attestation `a` that `carrier` includes, the erasure of `a` is among the chain attestations of
    the erasure of `D`. -/
theorem spec_erase_mem_chain_attestations :
    ∀ (D : NamedBlock V), ∀ carrier : NamedBlock V, NamedBlock.Preceq carrier D →
      ∀ a : NamedAttestation V, a ∈ carrier.attestations →
      a.erase ∈ (Model.spec (V := V)).chain_attestations D.erase :=
  (Model.vocabulary_facts_evidence (V := V)).erase_mem_chain_attestations

/-- At `Model.specBase`, the attestation `a` is in the store attestations of `st` exactly when
    some block `B` of `st.T` has `a` among its chain attestations. -/
theorem specBase_mem_store_attestations_iff :
    ∀ (st : (Model.specBase (V := V)).S) (a : CombinedAttestation V), a ∈ (Model.specBase (V := V)).store_attestations st ↔ ∃ B ∈ st.T, a ∈ (Model.specBase (V := V)).chain_attestations B := by
  intro st a
  show a ∈ ((Spec.Store.T (V := V) st).image Spec.Block.toProof).biUnion chain_attestations ↔ _
  rw [Finset.mem_biUnion]
  exact Iff.rfl

/-- At `Model.spec`, the attestation `a` is in the store attestations of `st` exactly when some
    block `B` of `st.T` has `a` among its chain attestations. -/
theorem spec_mem_store_attestations_iff :
    ∀ (st : (Model.spec (V := V)).S) (a : CombinedAttestation V), a ∈ (Model.spec (V := V)).store_attestations st ↔ ∃ B ∈ st.T, a ∈ (Model.spec (V := V)).chain_attestations B :=
  fun st a => specBase_mem_store_attestations_iff st.val a

/-- If the block `A` is an ancestor of the block `B`, or `B` itself, then every chain attestation of
    `A` is a chain attestation of `B`. -/
theorem spec_chain_attestations_mono :
    ∀ {A B : Block V} (h : Block.preceq A B = true), (Model.spec (V := V)).chain_attestations A ⊆ (Model.spec (V := V)).chain_attestations B :=
  (Model.vocabulary_facts_evidence (V := V)).chain_attestations_mono

/-- At `Model.specBase`, for a block `B` of `st.T`, every chain attestation of `B` is among the
    store attestations of `st`. -/
theorem specBase_chain_attestations_subset_store :
    ∀ {st : (Model.specBase (V := V)).S} {B : Block V} (hB : B ∈ st.T), (Model.specBase (V := V)).chain_attestations B ⊆ (Model.specBase (V := V)).store_attestations st := by
  intro st B hB
  show chain_attestations B ⊆ ((Spec.Store.T (V := V) st).image Spec.Block.toProof).biUnion chain_attestations
  exact Finset.subset_biUnion_of_mem chain_attestations hB

/-- At `Model.spec`, for a block `B` of `st.T`, every chain attestation of `B` is among the
    store attestations of `st`. -/
theorem spec_chain_attestations_subset_store :
    ∀ {st : (Model.spec (V := V)).S} {B : Block V} (hB : B ∈ st.T), (Model.spec (V := V)).chain_attestations B ⊆ (Model.spec (V := V)).store_attestations st :=
  fun {st} {B} hB => specBase_chain_attestations_subset_store (st := st.val) (B := B) hB

/-- If `HasSlashableWeightBetween E A₁ A₂` holds, `A₁ ⊆ A₁'` and `A₂ ⊆ A₂'`, then
    `HasSlashableWeightBetween E A₁' A₂'` holds. -/
theorem spec_hasSlashableWeightBetween_mono :
    ∀ {E : Env V} {A₁ A₂ A₁' A₂' : Finset (CombinedAttestation V)} (h : (Model.spec (V := V)).HasSlashableWeightBetween E A₁ A₂) (h₁ : A₁ ⊆ A₁') (h₂ : A₂ ⊆ A₂'), (Model.spec (V := V)).HasSlashableWeightBetween E A₁' A₂' :=
  (Model.vocabulary_facts_evidence (V := V)).hasSlashableWeightBetween_mono

/-- An attestation `a` of the list `ats` is among the chain attestations of the block
    `Block.node p s r gv gsv ats i`. -/
theorem spec_mem_chain_attestations_of_mem :
    ∀ {p : Block V} {s : Slot} {r : BlockId} {gv gsv : List (GoldfishVote V)} {ats : List (CombinedAttestation V)} {i : V} {a : CombinedAttestation V} (ha : a ∈ ats), a ∈ (Model.spec (V := V)).chain_attestations (Block.node p s r gv gsv ats i) :=
  (Model.vocabulary_facts_evidence (V := V)).mem_chain_attestations_of_mem

/-- If `carrier ⪯ tip` and `carrier` includes the named attestation `a`, then the erasure of `a` is
    among the chain attestations of the erasure of `tip`. -/
theorem spec_named_row_erase_mem :
    ∀ {tip carrier : NamedBlock V} {a : NamedAttestation V} (hc : NamedBlock.Preceq carrier tip) (ha : a ∈ carrier.attestations), a.erase ∈ (Model.spec (V := V)).chain_attestations tip.erase :=
  (Model.vocabulary_facts_evidence (V := V)).named_row_erase_mem

/-- For every named block `B`, every chain attestation `a` of the erasure of `B` is the erasure of
    an attestation that some named block `X ⪯ B` includes. -/
theorem spec_named_mem_chain_attestations_of_erase :
    ∀ {a : CombinedAttestation V}, ∀ B : NamedBlock V, a ∈ (Model.spec (V := V)).chain_attestations B.erase →
      ∃ X : NamedBlock V, NamedBlock.Preceq X B ∧
      ∃ row ∈ X.attestations, row.erase = a :=
  (Model.vocabulary_facts_evidence (V := V)).named_mem_chain_attestations_of_erase

end SpecRecord.EvidenceFacts

namespace DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-- `Model.spec` satisfies `EvidenceFacts`. -/
theorem Model.spec_facts_evidence : EvidenceFacts (Model.spec (V := V)) where
  no_faulty_intersection := SpecRecord.EvidenceFacts.spec_no_faulty_intersection
  hasSlashableWeightBetween_elim := SpecRecord.EvidenceFacts.spec_hasSlashableWeightBetween_elim
  ModelProperties_hasSlashableWeightBetween_intro := SpecRecord.EvidenceFacts.spec_ModelProperties_hasSlashableWeightBetween_intro
  slashableBetween_elim := SpecRecord.EvidenceFacts.spec_slashableBetween_elim
  ModelProperties_slashableBetween_intro := SpecRecord.EvidenceFacts.spec_ModelProperties_slashableBetween_intro
  quorum_intersection := SpecRecord.EvidenceFacts.spec_quorum_intersection
  Sts_hasSlashableWeightBetween_intro := SpecRecord.EvidenceFacts.spec_Sts_hasSlashableWeightBetween_intro
  Sts_slashableBetween_intro := SpecRecord.EvidenceFacts.spec_Sts_slashableBetween_intro
  totalWeight_le_three_mul_weightOf_of_hasIntersectionWeight := SpecRecord.EvidenceFacts.spec_totalWeight_le_three_mul_weightOf_of_hasIntersectionWeight
  erase_mem_chain_attestations := SpecRecord.EvidenceFacts.spec_erase_mem_chain_attestations
  mem_store_attestations_iff := SpecRecord.EvidenceFacts.spec_mem_store_attestations_iff
  chain_attestations_mono := SpecRecord.EvidenceFacts.spec_chain_attestations_mono
  chain_attestations_subset_store := SpecRecord.EvidenceFacts.spec_chain_attestations_subset_store
  hasSlashableWeightBetween_mono := SpecRecord.EvidenceFacts.spec_hasSlashableWeightBetween_mono
  mem_chain_attestations_of_mem := SpecRecord.EvidenceFacts.spec_mem_chain_attestations_of_mem
  named_row_erase_mem := SpecRecord.EvidenceFacts.spec_named_row_erase_mem
  named_mem_chain_attestations_of_erase := SpecRecord.EvidenceFacts.spec_named_mem_chain_attestations_of_erase

/-- `Model.spec` satisfies `EvidenceRunFacts`, which has no field. -/
theorem Model.spec_runFacts_evidence :
    EvidenceRunFacts (Model.spec (V := V)) where

end DecoupledConsensusModel.Sts.Record
