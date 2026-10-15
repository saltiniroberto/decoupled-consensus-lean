import Model.Record.Wiring

/-!
# Facts of the evidence family

The structure `EvidenceFacts`: facts that the evidence routines of a model `M : Model V` (chain
attestations, store attestations, slashable weight) satisfy on every input. The structure
`EvidenceRunFacts` is for facts about runs of the same family, and has no field.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Facts that the evidence routines of `M` satisfy on every input. -/
structure EvidenceFacts (M : Model V) : Prop where
  /-- If the validators outside `H` weigh less than a third (`BelowOneThird S H`) and `X` has the
      weight of an intersection of two quorums, then some validator of `X` is in `H`. -/
  no_faulty_intersection : ∀ {S : DecoupledConsensusModel.Execution.Setup V} {H X : Finset V}, DecoupledConsensusModel.Execution.BelowOneThird S H → M.HasIntersectionWeight S.E X → (∀ i ∈ X, i ∉ H) → False
  /-- If the evidence sets `A₁` and `A₂` carry slashable weight, then some set `Q` of validators has
      the weight of an intersection of two quorums and each of its members is slashable between `A₁`
      and `A₂`. -/
  hasSlashableWeightBetween_elim : ∀ {E : DecoupledConsensusModel.Env V} {A₁ A₂ : Finset (DecoupledConsensusModel.CombinedAttestation V)}, M.HasSlashableWeightBetween E A₁ A₂ → ∃ Q, M.HasIntersectionWeight E Q ∧ ∀ i ∈ Q, M.SlashableBetween A₁ A₂ i
  /-- If `Q` has the weight of an intersection of two quorums and each member of `Q` is slashable
      between `A₁` and `A₂`, then `A₁` and `A₂` carry slashable weight. -/
  ModelProperties_hasSlashableWeightBetween_intro : ∀ {E : DecoupledConsensusModel.Env V} {A₁ A₂ : Finset (DecoupledConsensusModel.CombinedAttestation V)} (Q : Finset V), M.HasIntersectionWeight E Q → (∀ i ∈ Q, M.SlashableBetween A₁ A₂ i) → M.HasSlashableWeightBetween E A₁ A₂
  /-- If `i` is slashable between `A₁` and `A₂`, then some `a ∈ A₁` and some `b ∈ A₂` are both
      attestations of `i`, and `a` and `b` are slashable. -/
  slashableBetween_elim : ∀ {A₁ A₂ : Finset (DecoupledConsensusModel.CombinedAttestation V)} {i : V}, M.SlashableBetween A₁ A₂ i → ∃ a ∈ A₁, ∃ b ∈ A₂, a.val_index = i ∧ b.val_index = i ∧ M.Slashable a b
  /-- If `a ∈ A₁` and `b ∈ A₂` are both attestations of `i`, and `a` and `b` are slashable, then `i`
      is slashable between `A₁` and `A₂`. -/
  ModelProperties_slashableBetween_intro : ∀ {A₁ A₂ : Finset (DecoupledConsensusModel.CombinedAttestation V)} {i : V}, ∀ a ∈ A₁, ∀ b ∈ A₂, a.val_index = i → b.val_index = i → M.Slashable a b → M.SlashableBetween A₁ A₂ i
  /-- If `Q` and `Q'` are quorums of the electorate of `E`, then `Q ∩ Q'` has the weight of an
      intersection of two quorums of `E`. -/
  quorum_intersection : ∀ (E : DecoupledConsensusModel.Env V) {Q Q' : Finset V}, E.electorate.IsQuorum Q → E.electorate.IsQuorum Q' → M.HasIntersectionWeight E (Q ∩ Q')
  /-- If `Q` has the weight of an intersection of two quorums and each member of `Q` is slashable
      between `A₁` and `A₂`, then `A₁` and `A₂` carry slashable weight. -/
  Sts_hasSlashableWeightBetween_intro : ∀ {E : DecoupledConsensusModel.Env V} {A₁ A₂ : Finset (DecoupledConsensusModel.CombinedAttestation V)} (Q : Finset V), M.HasIntersectionWeight E Q → (∀ i ∈ Q, M.SlashableBetween A₁ A₂ i) → M.HasSlashableWeightBetween E A₁ A₂
  /-- If `a ∈ A₁` and `b ∈ A₂` are both attestations of `i`, and `a` and `b` are slashable, then `i`
      is slashable between `A₁` and `A₂`. -/
  Sts_slashableBetween_intro : ∀ {A₁ A₂ : Finset (DecoupledConsensusModel.CombinedAttestation V)} {i : V}, ∀ a ∈ A₁, ∀ b ∈ A₂, a.val_index = i → b.val_index = i → M.Slashable a b → M.SlashableBetween A₁ A₂ i
  /-- If `X` has the weight of an intersection of two quorums of `E`, then the total weight of `E`'s
      electorate is at most three times the weight of `X`. -/
  totalWeight_le_three_mul_weightOf_of_hasIntersectionWeight : ∀ {E : DecoupledConsensusModel.Env V} {X : Finset V}, M.HasIntersectionWeight E X → E.electorate.totalWeight ≤ 3 * E.electorate.weightOf X
  /-- For every named block `carrier` with `carrier ⪯ D`, the erasure of every attestation `carrier`
      includes is among `M`'s chain attestations of the erasure of `D`. -/
  erase_mem_chain_attestations : ∀ (D : NamedBlock V), ∀ carrier : NamedBlock V, NamedBlock.Preceq carrier D →
    ∀ a : NamedAttestation V, a ∈ carrier.attestations →
    a.erase ∈ M.chain_attestations D.erase
  /-- The attestation `a` is among `M`'s store attestations of `st` exactly when some block `B` of
      `st`'s block tree has `a` among its chain attestations. -/
  mem_store_attestations_iff : ∀ (st : M.S) (a : CombinedAttestation V), a ∈ M.store_attestations st ↔ ∃ B ∈ st.T, a ∈ M.chain_attestations B
  /-- If `A ⪯ B`, then `M`'s chain attestations of `A` are among those of `B`. -/
  chain_attestations_mono : ∀ {A B : Block V} (h : Block.preceq A B = true), M.chain_attestations A ⊆ M.chain_attestations B
  /-- For a block `B` of the block tree of `st`, `M`'s chain attestations of `B` are among `M`'s
      store attestations of `st`. -/
  chain_attestations_subset_store : ∀ {st : M.S} {B : Block V} (hB : B ∈ st.T), M.chain_attestations B ⊆ M.store_attestations st
  /-- If `A₁` and `A₂` carry slashable weight in `E`, `A₁ ⊆ A₁'` and `A₂ ⊆ A₂'`, then `A₁'` and
      `A₂'` carry slashable weight in `E`. -/
  hasSlashableWeightBetween_mono : ∀ {E : Env V} {A₁ A₂ A₁' A₂' : Finset (CombinedAttestation V)} (h : M.HasSlashableWeightBetween E A₁ A₂) (h₁ : A₁ ⊆ A₁') (h₂ : A₂ ⊆ A₂'), M.HasSlashableWeightBetween E A₁' A₂'
  /-- An attestation of the list `ats` is among `M`'s chain attestations of the block
      `Block.node p s r gv gsv ats i`. -/
  mem_chain_attestations_of_mem : ∀ {p : Block V} {s : Slot} {r : BlockId} {gv gsv : List (GoldfishVote V)} {ats : List (CombinedAttestation V)} {i : V} {a : CombinedAttestation V} (ha : a ∈ ats), a ∈ M.chain_attestations (Block.node p s r gv gsv ats i)
  /-- If `carrier ⪯ tip` and `carrier` includes the named attestation `a`, then the erasure of `a`
      is among `M`'s chain attestations of the erasure of `tip`. -/
  named_row_erase_mem : ∀ {tip carrier : NamedBlock V} {a : NamedAttestation V} (hc : NamedBlock.Preceq carrier tip) (ha : a ∈ carrier.attestations), a.erase ∈ M.chain_attestations tip.erase
  /-- Every attestation among `M`'s chain attestations of the erasure of the named block `B` is the
      erasure of an attestation included in some `X ⪯ B`. -/
  named_mem_chain_attestations_of_erase : ∀ {a : CombinedAttestation V}, ∀ B : NamedBlock V, a ∈ M.chain_attestations B.erase →
    ∃ X : NamedBlock V, NamedBlock.Preceq X B ∧
    ∃ row ∈ X.attestations, row.erase = a

/-- Facts about runs of the evidence family of `M`; it has no field. -/
structure EvidenceRunFacts (M : Model V) : Prop where


end DecoupledConsensusModel.Sts.Record
