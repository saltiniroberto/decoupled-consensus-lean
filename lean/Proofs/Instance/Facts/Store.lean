import Proofs.Instance.Model
import Proofs.Vocabulary.ModelVocabularyFacts

/-!
# The store facts at `Model.spec`

Fields of `StoreFacts` proved at the spec's model `Model.spec`, one theorem `spec_<x>` per
field `<x>`. A field whose proof reads the spec's own store type is first proved at
`Model.specBase` as `specBase_<x>`, then taken at the values of the subtype stores.
-/

set_option autoImplicit false

namespace SpecRecord.StoreFacts

open DecoupledConsensusModel DecoupledConsensusModel.Execution DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-- The member `sgVote` of `Model.specBase` is `DecoupledConsensusModel.Protocol.sgVote`. -/
theorem specBase_sgVote_eq :
    (Model.specBase (V := V)).sgVote = DecoupledConsensusModel.Protocol.sgVote := by
  funext a
  show (Spec.Protocol.sgVote (Spec.Attestation.toSpec a)).toProof = _
  rw [← toProof_sgVote, Spec.Attestation.toProof_toSpec]

/-- The member `sgVote` of `Model.spec` is `DecoupledConsensusModel.Protocol.sgVote`. -/
theorem spec_sgVote_eq :
    (Model.spec (V := V)).sgVote = DecoupledConsensusModel.Protocol.sgVote := by
  funext a
  show (Spec.Protocol.sgVote (Spec.Attestation.toSpec a)).toProof = _
  rw [← toProof_sgVote, Spec.Attestation.toProof_toSpec]

/-! ## `StoreFacts` -/

/-- The field `pool_view_mem` of `StoreFacts` at `Model.specBase`: if every round's SG votes of
    `st`'s store part are the erasures of `st`'s rows of that round, then a named attestation `row`
    held in `st`'s rows of its round has its erasure in `store_sg_pool st.core row.round`. -/
theorem specBase_pool_view_mem :
    ∀ (st : (Model.specBase (V := V)).NS), (∀ r, st.core.sg_votes r = (st.sg_rows r).map NamedAttestation.erase) →
    ∀ (row : NamedAttestation V), row ∈ st.sg_rows row.round →
      row.erase ∈ (Model.specBase (V := V)).store_sg_pool st.core row.round := by
  intro st h row hrow
  have := (Model.vocabulary_facts_store (V := V)).pool_view_mem st.toProofNamed h row hrow
  change row.erase ∈ DecoupledConsensusModel.Protocol.Store.sg_pool st.toProof row.round at this
  rw [toProof_store_sg_pool] at this
  exact this

/-- The field `pool_view_mem` of `StoreFacts` at `Model.spec`: if every round's SG votes of
    `st`'s store part are the erasures of `st`'s rows of that round, then a named attestation `row`
    held in `st`'s rows of its round has its erasure in `store_sg_pool st.core row.round`. -/
theorem spec_pool_view_mem :
    ∀ (st : (Model.spec (V := V)).NS), (∀ r, st.core.sg_votes r = (st.sg_rows r).map NamedAttestation.erase) →
    ∀ (row : NamedAttestation V), row ∈ st.sg_rows row.round →
      row.erase ∈ (Model.spec (V := V)).store_sg_pool st.core row.round :=
  fun st => specBase_pool_view_mem st.val

/-- The field `store_with_σ_T_timestamp_block_σ` of `StoreFacts` at `Model.specBase`: the store
    `st` with its chain states written to `σ'`, its tree to `T'` and its block stamps to `τ'` has
    chain-state map `σ'`. -/
theorem specBase_store_with_σ_T_timestamp_block_σ :
    ∀ (st : (Model.specBase (V := V)).S) (σ' : Block V → (Model.specBase (V := V)).CS) (T' : Finset (Block V))
    (τ' : TimestampMap (Block V)), ((Model.specBase (V := V)).store_with_σ_T_timestamp_block st σ' T' τ').σ = σ' := by
  intro st σ' T' τ'
  funext B
  show σ' (Spec.Store.blockOfImage _ B).toProof = σ' B
  rw [Spec.Store.toProof_blockOfImage]

/-- The field `store_with_σ_T_timestamp_block_σ` of `StoreFacts` at `Model.spec`: the store
    `st` with its chain states written to `σ'`, its tree to `T'` and its block stamps to `τ'` has
    chain-state map `σ'`. -/
theorem spec_store_with_σ_T_timestamp_block_σ :
    ∀ (st : (Model.spec (V := V)).S) (σ' : Block V → (Model.spec (V := V)).CS) (T' : Finset (Block V))
    (τ' : TimestampMap (Block V)), ((Model.spec (V := V)).store_with_σ_T_timestamp_block st σ' T' τ').σ = σ' :=
  by
  intro st σ' T' τ'
  show Member.store_σ (OkMember.store_with_σ_T_timestamp_block st σ' T' τ').val = σ'
  unfold OkMember.store_with_σ_T_timestamp_block
  split
  · exact specBase_store_with_σ_T_timestamp_block_σ st.val σ' T' τ'
  · funext B
    show σ' (Spec.Store.blockOfImage _ B).toProof = σ' B
    rw [Spec.Store.toProof_blockOfImage]

/-- The field `store_with_σ_T_timestamp_block_F` of `StoreFacts` at `Model.specBase`: writing
    the chain states, the tree and the block stamps keeps the finalized block. -/
theorem specBase_store_with_σ_T_timestamp_block_F :
    ∀ (st : (Model.specBase (V := V)).S) (σ' : Block V → (Model.specBase (V := V)).CS) (T' : Finset (Block V))
    (τ' : TimestampMap (Block V)), ((Model.specBase (V := V)).store_with_σ_T_timestamp_block st σ' T' τ').F = st.F :=
  fun _ _ _ _ => rfl

/-- The field `store_with_σ_T_timestamp_block_F` of `StoreFacts` at `Model.spec`: writing the
    chain states, the tree and the block stamps keeps the finalized block. -/
theorem spec_store_with_σ_T_timestamp_block_F :
    ∀ (st : (Model.spec (V := V)).S) (σ' : Block V → (Model.spec (V := V)).CS) (T' : Finset (Block V))
    (τ' : TimestampMap (Block V)), ((Model.spec (V := V)).store_with_σ_T_timestamp_block st σ' T' τ').F = st.F :=
  by
  intro st σ' T' τ'
  show Member.store_F (OkMember.store_with_σ_T_timestamp_block st σ' T' τ').val = Member.store_F st.val
  unfold OkMember.store_with_σ_T_timestamp_block
  split
  · exact specBase_store_with_σ_T_timestamp_block_F st.val σ' T' τ'
  · rfl

omit [Fintype V] [Inhabited V] in
/-- At a store meeting `StoreOk`, the parent of `st.blockOfImage A` is `st.blockOfImage A.parent`. -/
theorem blockOfImage_parent_of_storeOk {st : Spec.Store V} (h : NoRaise.StoreOk st)
    (A : Block V) : (st.blockOfImage A).parent = st.blockOfImage A.parent := by
  cases A with
  | genesis =>
      simp only [Spec.Store.blockOfImage, Spec.Store.blockOfImageIn,
        DecoupledConsensusModel.Block.parent, Spec.Block.parent]
  | node p s r votes support ats proposer =>
      simp only [Spec.Store.blockOfImage, DecoupledConsensusModel.Block.parent]
      cases hpk : Spec.pickUnique? st.T
          (fun B' => decide (B'.toProof = Block.node p s r votes support ats proposer)) with
      | none =>
          simp only [Spec.Store.blockOfImageIn, hpk, Option.getD,
            Spec.Block.parent]
      | some B' =>
          obtain ⟨hB', himg⟩ := Spec.Store.blockWithImage?_eq_some st hpk
          have hlhs : Spec.Store.blockOfImageIn st.T
              (.node p s r votes support ats proposer) = B' := by
            simp only [Spec.Store.blockOfImageIn, hpk, Option.getD]
          rw [hlhs]
          cases B' with
          | genesis => cases himg
          | node p' s' r' votes' support' ats' proposer' =>
              simp only [Spec.Block.toProof, Block.node.injEq] at himg
              rw [← himg.1]
              exact (Spec.Store.blockOfImage_toProof_of_mem st h.2.1
                (h.2.2.1 _ hB')).symm

/-- The field `store_with_σ_T_timestamp_block_T` of `StoreFacts` at `Model.spec`: if no two
    distinct blocks of `T'` share a root, every block of `T'` is stamped under `τ'`, `T'` holds the
    parent of each of its blocks, and `T'` holds the finalized block of `st`, then the store `st`
    with its chain states written to `σ'`, its tree to `T'` and its block stamps to `τ'` has tree
    `T'`. -/
theorem spec_store_with_σ_T_timestamp_block_T :
    ∀ (st : (Model.spec (V := V)).S) (σ' : Block V → (Model.spec (V := V)).CS) (T' : Finset (Block V))
    (τ' : TimestampMap (Block V))
    -- no two blocks of the written tree share a root
    (hT : ∀ A ∈ T', ∀ D ∈ T', A.root = D.root → A = D)
    -- every block of the written tree has a stamp under the written stamp map
    (hτ : ∀ A ∈ T', (τ' A).isSome = true)
    -- the written tree holds every written block's parent
    (hpar : ∀ A ∈ T', A.parent ∈ T')
    -- the written tree holds the store's finalized block
    (hF : st.F ∈ T'),
    ((Model.spec (V := V)).store_with_σ_T_timestamp_block st σ' T' τ').T = T' := by
  intro st σ' T' τ' hT hτ hpar hF
  have hok : TreeOk (Member.store_with_σ_T_timestamp_block st.val σ' T' τ') := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro B hB
      obtain ⟨A, hA, rfl⟩ := Finset.mem_map.mp hB
      show τ' (st.val.blockOfImage A).toProof ≠ none
      rw [Spec.Store.toProof_blockOfImage]
      exact Option.isSome_iff_ne_none.mp (hτ A hA)
    · intro B hB B' hB' hr
      obtain ⟨A, hA, rfl⟩ := Finset.mem_map.mp hB
      obtain ⟨D, hD, rfl⟩ := Finset.mem_map.mp hB'
      have hAD : A.root = D.root := by
        have := congrArg Spec.BlockId.toProof hr
        rwa [← Spec.Block.toProof_root, ← Spec.Block.toProof_root,
          Spec.Store.coe_blockOfImageEmb, Spec.Store.toProof_blockOfImage,
          Spec.Store.toProof_blockOfImage] at this
      rw [hT A hA D hD hAD]
    · intro B hB
      obtain ⟨A, hA, rfl⟩ := Finset.mem_map.mp hB
      show (st.val.blockOfImage A).parent ∈ T'.map st.val.blockOfImageEmb
      rw [blockOfImage_parent_of_storeOk st.property A]
      exact Finset.mem_map_of_mem st.val.blockOfImageEmb (hpar A hA)
    · have hF' : st.val.F.toProof ∈ T' := hF
      show st.val.F ∈ T'.map st.val.blockOfImageEmb
      rw [← Spec.Store.blockOfImage_toProof_of_mem st.val st.property.2.1
        st.property.2.2.2]
      exact Finset.mem_map_of_mem st.val.blockOfImageEmb hF'
  show Member.store_T (OkMember.store_with_σ_T_timestamp_block st σ' T' τ').val = T'
  unfold OkMember.store_with_σ_T_timestamp_block
  rw [dif_pos hok]
  show Finset.image Spec.Block.toProof (T'.map st.val.blockOfImageEmb) = T'
  rw [Finset.map_eq_image, Finset.image_image]
  simp only [Spec.Store.coe_blockOfImageEmb, Function.comp_def,
    Spec.Store.toProof_blockOfImage, Finset.image_id']

/-- The field `store_with_t_s_s` of `StoreFacts` at `Model.spec`: the store `st` with its clock
    written to `t` and its slot to `s` has slot `s`. -/
theorem spec_store_with_t_s_s :
    ∀ (st : (Model.spec (V := V)).S) (t : Time) (s : Slot), ((Model.spec (V := V)).store_with_t_s st t s).s = s :=
  fun _ _ _ => rfl

/-- The field `committeePools_init` of `StoreFacts` at `Model.spec`: every Goldfish vote in the
    slot-`k` list of the initial store is signed by a member of `E.committee k`. -/
theorem spec_committeePools_init :
    ∀ (E : Env V) (k : Slot) (u : GoldfishVote V), u ∈ ((Model.spec (V := V)).store_init : (Model.spec (V := V)).S).gf_votes k → u.val_index ∈ E.committee k := by
  intro E k u hu
  have := (Model.vocabulary_facts_store (V := V)).committeePools_init E k u
  change u ∈ (DecoupledConsensusModel.Protocol.Store.init :
    DecoupledConsensusModel.Protocol.Store V).gf_votes k → _ at this
  rw [toProof_store_init] at this
  exact this hu

/-- The field `poolStep_tickStore` of `StoreFacts` at `Model.specBase`: if `st.t ≤ t` and `st`
    satisfies the four pool conditions (every vote in a slot's list is for that slot, every pooled
    vote is stamped, every stamped vote is pooled in its slot's list, no stamp is later than
    `st.t`), then `store_with_t_s st t s` keeps every vote and stamp of `st` and satisfies the same
    four conditions. -/
theorem specBase_poolStep_tickStore :
    ∀ (st : (Model.specBase (V := V)).S) (t : Time) (s : Slot), st.t ≤ t →
    ((∀ (k : Slot) (x : GoldfishVote V), x ∈ st.gf_votes k → x.slot = k) ∧
      (∀ (k : Slot) (x : GoldfishVote V), x ∈ st.gf_votes k → (st.timestamp_vote x).isSome = true) ∧
      (∀ x : GoldfishVote V, (st.timestamp_vote x).isSome = true → x ∈ st.gf_votes x.slot) ∧
      (∀ (x : GoldfishVote V) (c : Stamp), st.timestamp_vote x = some c → c ≤ (st.t : Stamp))) →
    ((∀ (k : Slot) (x : GoldfishVote V), x ∈ st.gf_votes k → x ∈ ((Model.specBase (V := V)).store_with_t_s st t s).gf_votes k) ∧
      (∀ (x : GoldfishVote V) (c : Stamp), st.timestamp_vote x = some c →
        ((Model.specBase (V := V)).store_with_t_s st t s).timestamp_vote x = some c)) ∧
    ((∀ (k : Slot) (x : GoldfishVote V), x ∈ ((Model.specBase (V := V)).store_with_t_s st t s).gf_votes k → x.slot = k) ∧
      (∀ (k : Slot) (x : GoldfishVote V), x ∈ ((Model.specBase (V := V)).store_with_t_s st t s).gf_votes k →
        (((Model.specBase (V := V)).store_with_t_s st t s).timestamp_vote x).isSome = true) ∧
      (∀ x : GoldfishVote V, (((Model.specBase (V := V)).store_with_t_s st t s).timestamp_vote x).isSome = true →
        x ∈ ((Model.specBase (V := V)).store_with_t_s st t s).gf_votes x.slot) ∧
      (∀ (x : GoldfishVote V) (c : Stamp), ((Model.specBase (V := V)).store_with_t_s st t s).timestamp_vote x = some c →
        c ≤ (((Model.specBase (V := V)).store_with_t_s st t s).t : Stamp))) :=
  fun st t s hle h => (Model.vocabulary_facts_store (V := V)).poolStep_tickStore st.toProof t s hle h

/-- The field `poolStep_tickStore` of `StoreFacts` at `Model.spec`: if `st.t ≤ t` and `st`
    satisfies the four pool conditions (every vote in a slot's list is for that slot, every pooled
    vote is stamped, every stamped vote is pooled in its slot's list, no stamp is later than
    `st.t`), then `store_with_t_s st t s` keeps every vote and stamp of `st` and satisfies the same
    four conditions. -/
theorem spec_poolStep_tickStore :
    ∀ (st : (Model.spec (V := V)).S) (t : Time) (s : Slot), st.t ≤ t →
    ((∀ (k : Slot) (x : GoldfishVote V), x ∈ st.gf_votes k → x.slot = k) ∧
      (∀ (k : Slot) (x : GoldfishVote V), x ∈ st.gf_votes k → (st.timestamp_vote x).isSome = true) ∧
      (∀ x : GoldfishVote V, (st.timestamp_vote x).isSome = true → x ∈ st.gf_votes x.slot) ∧
      (∀ (x : GoldfishVote V) (c : Stamp), st.timestamp_vote x = some c → c ≤ (st.t : Stamp))) →
    ((∀ (k : Slot) (x : GoldfishVote V), x ∈ st.gf_votes k → x ∈ ((Model.spec (V := V)).store_with_t_s st t s).gf_votes k) ∧
      (∀ (x : GoldfishVote V) (c : Stamp), st.timestamp_vote x = some c →
        ((Model.spec (V := V)).store_with_t_s st t s).timestamp_vote x = some c)) ∧
    ((∀ (k : Slot) (x : GoldfishVote V), x ∈ ((Model.spec (V := V)).store_with_t_s st t s).gf_votes k → x.slot = k) ∧
      (∀ (k : Slot) (x : GoldfishVote V), x ∈ ((Model.spec (V := V)).store_with_t_s st t s).gf_votes k →
        (((Model.spec (V := V)).store_with_t_s st t s).timestamp_vote x).isSome = true) ∧
      (∀ x : GoldfishVote V, (((Model.spec (V := V)).store_with_t_s st t s).timestamp_vote x).isSome = true →
        x ∈ ((Model.spec (V := V)).store_with_t_s st t s).gf_votes x.slot) ∧
      (∀ (x : GoldfishVote V) (c : Stamp), ((Model.spec (V := V)).store_with_t_s st t s).timestamp_vote x = some c →
        c ≤ (((Model.spec (V := V)).store_with_t_s st t s).t : Stamp))) :=
  fun st t s => specBase_poolStep_tickStore st.val t s

/-- The field `pool_set_clock_slot` of `StoreFacts` at `Model.spec`: setting the clock and the
    slot keeps the slot-`k` Goldfish votes. -/
theorem spec_pool_set_clock_slot :
    ∀ (st : (Model.spec (V := V)).S) (t : Int) (s k : Slot),
    ((Model.spec (V := V)).store_with_t_s st t s).pool k = st.pool k :=
  fun _ _ _ _ => rfl

/-- The field `mem_pool_iff` of `StoreFacts` at `Model.specBase`: `u ∈ store_pool st k` exactly
    when `u ∈ st.gf_votes k`. -/
theorem specBase_mem_pool_iff :
    ∀ (st : (Model.specBase (V := V)).S) (k : Slot) (u : GoldfishVote V),
    u ∈ (Model.specBase (V := V)).store_pool st k ↔ u ∈ st.gf_votes k := by
  intro st k u
  have := (Model.vocabulary_facts_store (V := V)).mem_pool_iff st.toProof k u
  change u ∈ DecoupledConsensusModel.Protocol.Store.pool st.toProof k ↔ _ at this
  rw [toProof_store_pool] at this
  exact this

/-- The field `mem_pool_iff` of `StoreFacts` at `Model.spec`: `u ∈ store_pool st k` exactly
    when `u ∈ st.gf_votes k`. -/
theorem spec_mem_pool_iff :
    ∀ (st : (Model.spec (V := V)).S) (k : Slot) (u : GoldfishVote V),
    u ∈ (Model.spec (V := V)).store_pool st k ↔ u ∈ st.gf_votes k :=
  fun st k u => specBase_mem_pool_iff st.val k u

/-- The field `ModelProperties_mem_sg_pool_iff` of `StoreFacts` at `Model.specBase`:
    `b ∈ store_sg_pool st r` exactly when `b ∈ st.sg_votes r`. -/
theorem specBase_ModelProperties_mem_sg_pool_iff :
    ∀ (st : (Model.specBase (V := V)).S) (r : Round) (b : CombinedAttestation V),
    b ∈ (Model.specBase (V := V)).store_sg_pool st r ↔ b ∈ st.sg_votes r := by
  intro st r b
  have := (Model.vocabulary_facts_store (V := V)).ModelProperties_mem_sg_pool_iff st.toProof r b
  change b ∈ DecoupledConsensusModel.Protocol.Store.sg_pool st.toProof r ↔ _ at this
  rw [toProof_store_sg_pool] at this
  exact this

/-- The field `ModelProperties_mem_sg_pool_iff` of `StoreFacts` at `Model.spec`:
    `b ∈ store_sg_pool st r` exactly when `b ∈ st.sg_votes r`. -/
theorem spec_ModelProperties_mem_sg_pool_iff :
    ∀ (st : (Model.spec (V := V)).S) (r : Round) (b : CombinedAttestation V),
    b ∈ (Model.spec (V := V)).store_sg_pool st r ↔ b ∈ st.sg_votes r :=
  fun st r b => specBase_ModelProperties_mem_sg_pool_iff st.val r b

/-- The field `ModelProperties_toHealing_F` of `StoreFacts` at `Model.spec`: the healing store
    of `st` has the finalized block of `st`. -/
theorem spec_ModelProperties_toHealing_F :
    ∀ (st : (Model.spec (V := V)).S), ((Model.spec (V := V)).toHealing st).toFG.F = st.F :=
  fun _ => rfl

/-- The field `ModelProperties_toHealing_J` of `StoreFacts` at `Model.spec`: the healing store
    of `st` has the justified block of `st`. -/
theorem spec_ModelProperties_toHealing_J :
    ∀ (st : (Model.spec (V := V)).S), ((Model.spec (V := V)).toHealing st).toFG.J = st.J :=
  fun _ => rfl

/-- The field `toHealing_T` of `StoreFacts` at `Model.specBase`: the healing store of `st` has
    the block tree `st.T`. -/
theorem specBase_toHealing_T :
    ∀ (st : (Model.specBase (V := V)).S), ((Model.specBase (V := V)).toHealing st).toFG.toSG.toGoldfishStore.T = st.T :=
  fun st => (toProof_gs_T st).trans (Spec.Store.toProof_T st).symm

/-- The field `toHealing_T` of `StoreFacts` at `Model.spec`: the healing store of `st` has the
    block tree `st.T`. -/
theorem spec_toHealing_T :
    ∀ (st : (Model.spec (V := V)).S), ((Model.spec (V := V)).toHealing st).toFG.toSG.toGoldfishStore.T = st.T :=
  fun st => specBase_toHealing_T st.val

/-- The field `ModelProperties_toHealing_h_max` of `StoreFacts` at `Model.spec`: the healing
    store of `st` has the largest seen height `st.h_max`. -/
theorem spec_ModelProperties_toHealing_h_max :
    ∀ (st : (Model.spec (V := V)).S), ((Model.spec (V := V)).toHealing st).toFG.h_max = st.h_max :=
  fun _ => rfl

/-- The field `toHealing_live_confirmed` of `StoreFacts` at `Model.specBase`: the healing store
    of `st` confirms for voting the block `st.live_confirmed`. -/
theorem specBase_toHealing_live_confirmed :
    ∀ (st : (Model.specBase (V := V)).S),
    ((Model.specBase (V := V)).toHealing st).toFG.toSG.toGoldfishStore.live_confirmed = st.live_confirmed :=
  fun st => (toProof_gs_live_confirmed st).trans (Spec.Store.toProof_live_confirmed st).symm

/-- The field `toHealing_live_confirmed` of `StoreFacts` at `Model.spec`: the healing store of
    `st` confirms for voting the block `st.live_confirmed`. -/
theorem spec_toHealing_live_confirmed :
    ∀ (st : (Model.spec (V := V)).S),
    ((Model.spec (V := V)).toHealing st).toFG.toSG.toGoldfishStore.live_confirmed = st.live_confirmed :=
  fun st => specBase_toHealing_live_confirmed st.val

/-- The field `toHealing_s` of `StoreFacts` at `Model.specBase`: the healing store of `st` has
    the current slot `st.s`. -/
theorem specBase_toHealing_s :
    ∀ (st : (Model.specBase (V := V)).S), ((Model.specBase (V := V)).toHealing st).toFG.toSG.toGoldfishStore.s = st.s :=
  fun st => (toProof_gs_s st).trans (Spec.Store.toProof_s st).symm

/-- The field `toHealing_s` of `StoreFacts` at `Model.spec`: the healing store of `st` has the
    current slot `st.s`. -/
theorem spec_toHealing_s :
    ∀ (st : (Model.spec (V := V)).S), ((Model.spec (V := V)).toHealing st).toFG.toSG.toGoldfishStore.s = st.s :=
  fun st => specBase_toHealing_s st.val

/-- The field `ModelProperties_toHealing_sg_votes` of `StoreFacts` at `Model.specBase`: the
    round-`r` SG votes of the healing store of `st` are the images under `sgVote` of
    `store_sg_pool st r`. -/
theorem specBase_ModelProperties_toHealing_sg_votes :
    ∀ (st : (Model.specBase (V := V)).S) (r : Round),
    ((Model.specBase (V := V)).toHealing st).toFG.toSG.sg_votes r = ((Model.specBase (V := V)).store_sg_pool st r).image (Model.specBase (V := V)).sgVote := by
  intro st r
  have := (Model.vocabulary_facts_store (V := V)).ModelProperties_toHealing_sg_votes st.toProof r
  change st.toProof.toHealing.toFG.toSG.sg_votes r =
    (DecoupledConsensusModel.Protocol.Store.sg_pool st.toProof r).image
      DecoupledConsensusModel.Protocol.sgVote at this
  rw [toProof_sgs_sg_votes, toProof_store_sg_pool] at this
  rw [specBase_sgVote_eq]
  exact this

/-- The field `ModelProperties_toHealing_sg_votes` of `StoreFacts` at `Model.spec`: the
    round-`r` SG votes of the healing store of `st` are the images under `sgVote` of
    `store_sg_pool st r`. -/
theorem spec_ModelProperties_toHealing_sg_votes :
    ∀ (st : (Model.spec (V := V)).S) (r : Round),
    ((Model.spec (V := V)).toHealing st).toFG.toSG.sg_votes r = ((Model.spec (V := V)).store_sg_pool st r).image (Model.spec (V := V)).sgVote :=
  fun st r => specBase_ModelProperties_toHealing_sg_votes st.val r

/-- The field `ModelProperties_toHealing_σ` of `StoreFacts` at `Model.spec`: the healing store
    of `st` has the chain-state map `st.σ`. -/
theorem spec_ModelProperties_toHealing_σ :
    ∀ (st : (Model.spec (V := V)).S), ((Model.spec (V := V)).toHealing st).toFG.σ = st.σ :=
  fun _ => rfl

/-- The field `sgVote_confirmed` of `StoreFacts` at `Model.spec`: the SG vote of `a.erase`
    names the confirmed block `a.confirmed`. -/
theorem spec_sgVote_confirmed :
    ∀ (a : NamedAttestation V), ((Model.spec (V := V)).sgVote a.erase).confirmed = a.confirmed := by
  intro a
  rw [spec_sgVote_eq]
  exact (Model.vocabulary_facts_store (V := V)).sgVote_confirmed a

/-- The field `sgVote_round` of `StoreFacts` at `Model.spec`: the SG vote of `a.erase` has the
    round `a.round`. -/
theorem spec_sgVote_round :
    ∀ (a : NamedAttestation V), ((Model.spec (V := V)).sgVote a.erase).round = a.round := by
  intro a
  rw [spec_sgVote_eq]
  exact (Model.vocabulary_facts_store (V := V)).sgVote_round a

/-- The field `sgVote_val` of `StoreFacts` at `Model.spec`: the SG vote of `a.erase` has the
    validator index `a.val_index`. -/
theorem spec_sgVote_val :
    ∀ (a : NamedAttestation V), ((Model.spec (V := V)).sgVote a.erase).val_index = a.val_index := by
  intro a
  rw [spec_sgVote_eq]
  exact (Model.vocabulary_facts_store (V := V)).sgVote_val a

/-- The field `toHealing_slot` of `StoreFacts` at `Model.specBase`: the healing store of `st`
    has the current slot `st.s`. -/
theorem specBase_toHealing_slot :
    ∀ (st : (Model.specBase (V := V)).S), ((Model.specBase (V := V)).toHealing st).toFG.toSG.toGoldfishStore.s = st.s :=
  fun st => (toProof_gs_s st).trans (Spec.Store.toProof_s st).symm

/-- The field `toHealing_slot` of `StoreFacts` at `Model.spec`: the healing store of `st` has
    the current slot `st.s`. -/
theorem spec_toHealing_slot :
    ∀ (st : (Model.spec (V := V)).S), ((Model.spec (V := V)).toHealing st).toFG.toSG.toGoldfishStore.s = st.s :=
  fun st => specBase_toHealing_slot st.val

/-- The field `mem_goldfishStore_pool_iff` of `StoreFacts` at `Model.specBase`:
    `u ∈ gs_pool gs s` exactly when `u ∈ gs.gf_votes s`. -/
theorem specBase_mem_goldfishStore_pool_iff :
    ∀ (gs : (Model.specBase (V := V)).GS) (s : Slot) (u : GoldfishVote V),
    u ∈ (Model.specBase (V := V)).gs_pool gs s ↔ u ∈ gs.gf_votes s := by
  intro gs s u
  have := (Model.vocabulary_facts_store (V := V)).mem_goldfishStore_pool_iff
    gs.toProof.toHealing.toFG.toSG.toGoldfishStore s u
  change u ∈ DecoupledConsensusModel.Protocol.GoldfishStore.pool
    gs.toProof.toHealing.toFG.toSG.toGoldfishStore s ↔ _ at this
  rw [toProof_gs_pool] at this
  exact this

/-- The field `mem_goldfishStore_pool_iff` of `StoreFacts` at `Model.spec`: `u ∈ gs_pool gs s`
    exactly when `u ∈ gs.gf_votes s`. -/
theorem spec_mem_goldfishStore_pool_iff :
    ∀ (gs : (Model.spec (V := V)).GS) (s : Slot) (u : GoldfishVote V),
    u ∈ (Model.spec (V := V)).gs_pool gs s ↔ u ∈ gs.gf_votes s :=
  fun gs s u => specBase_mem_goldfishStore_pool_iff gs.val s u

/-- The field `Sts_mem_sg_pool_iff` of `StoreFacts` at `Model.specBase`:
    `c ∈ store_sg_pool st r` exactly when `c ∈ st.sg_votes r`. -/
theorem specBase_Sts_mem_sg_pool_iff :
    ∀ (st : (Model.specBase (V := V)).S) (r : Round) (c : CombinedAttestation V),
    c ∈ (Model.specBase (V := V)).store_sg_pool st r ↔ c ∈ st.sg_votes r := by
  intro st r c
  have := (Model.vocabulary_facts_store (V := V)).Sts_mem_sg_pool_iff st.toProof r c
  change c ∈ DecoupledConsensusModel.Protocol.Store.sg_pool st.toProof r ↔ _ at this
  rw [toProof_store_sg_pool] at this
  exact this

/-- The field `Sts_mem_sg_pool_iff` of `StoreFacts` at `Model.spec`: `c ∈ store_sg_pool st r`
    exactly when `c ∈ st.sg_votes r`. -/
theorem spec_Sts_mem_sg_pool_iff :
    ∀ (st : (Model.spec (V := V)).S) (r : Round) (c : CombinedAttestation V),
    c ∈ (Model.spec (V := V)).store_sg_pool st r ↔ c ∈ st.sg_votes r :=
  fun st r c => specBase_Sts_mem_sg_pool_iff st.val r c

/-- The field `mem_store_pool_iff` of `StoreFacts` at `Model.specBase`: `u ∈ store_pool st s`
    exactly when `u ∈ st.gf_votes s`. -/
theorem specBase_mem_store_pool_iff :
    ∀ (st : (Model.specBase (V := V)).S) (s : Slot) (u : GoldfishVote V),
    u ∈ (Model.specBase (V := V)).store_pool st s ↔ u ∈ st.gf_votes s := by
  intro st s u
  have := (Model.vocabulary_facts_store (V := V)).mem_store_pool_iff st.toProof s u
  change u ∈ DecoupledConsensusModel.Protocol.Store.pool st.toProof s ↔ _ at this
  rw [toProof_store_pool] at this
  exact this

/-- The field `mem_store_pool_iff` of `StoreFacts` at `Model.spec`: `u ∈ store_pool st s`
    exactly when `u ∈ st.gf_votes s`. -/
theorem spec_mem_store_pool_iff :
    ∀ (st : (Model.spec (V := V)).S) (s : Slot) (u : GoldfishVote V),
    u ∈ (Model.spec (V := V)).store_pool st s ↔ u ∈ st.gf_votes s :=
  fun st s u => specBase_mem_store_pool_iff st.val s u

/-- The field `pool_eq_of_gf_votes_eq` of `StoreFacts` at `Model.specBase`: two stores with the
    same Goldfish vote lists have the same `store_pool` at every slot. -/
theorem specBase_pool_eq_of_gf_votes_eq :
    ∀ {st st' : (Model.specBase (V := V)).S} (h : st.gf_votes = st'.gf_votes) (k : Slot),
    (Model.specBase (V := V)).store_pool st k = (Model.specBase (V := V)).store_pool st' k := by
  intro st st' h k
  have := (Model.vocabulary_facts_store (V := V)).pool_eq_of_gf_votes_eq
    (st := st.toProof) (st' := st'.toProof) h k
  change DecoupledConsensusModel.Protocol.Store.pool st.toProof k =
    DecoupledConsensusModel.Protocol.Store.pool st'.toProof k at this
  rw [toProof_store_pool, toProof_store_pool] at this
  exact this

/-- The field `pool_eq_of_gf_votes_eq` of `StoreFacts` at `Model.spec`: two stores with the
    same Goldfish vote lists have the same `store_pool` at every slot. -/
theorem spec_pool_eq_of_gf_votes_eq :
    ∀ {st st' : (Model.spec (V := V)).S} (h : st.gf_votes = st'.gf_votes) (k : Slot),
    (Model.spec (V := V)).store_pool st k = (Model.spec (V := V)).store_pool st' k :=
  fun {st} {st'} h k => specBase_pool_eq_of_gf_votes_eq (st := st.val) (st' := st'.val) h k

/-- The field `sgVote_confirmed_eq` of `StoreFacts` at `Model.spec`: the SG vote of `A` names
    the confirmed block of `A`. -/
theorem spec_sgVote_confirmed_eq :
    ∀ (A : CombinedAttestation V), ((Model.spec (V := V)).sgVote A).confirmed = A.confirmed := by
  intro A
  rw [spec_sgVote_eq]
  exact (Model.vocabulary_facts_store (V := V)).sgVote_confirmed_eq A

/-- The field `sgVote_eq_of_fields` of `StoreFacts` at `Model.spec`: attestations with the same
    validator, round and confirmed block have the same SG vote. -/
theorem spec_sgVote_eq_of_fields :
    ∀ {A A' : CombinedAttestation V} (h₁ : A.val_index = A'.val_index)
    (h₂ : A.round = A'.round) (h₃ : A.confirmed = A'.confirmed), (Model.spec (V := V)).sgVote A = (Model.spec (V := V)).sgVote A' := by
  intro A A' h₁ h₂ h₃
  rw [spec_sgVote_eq]
  exact (Model.vocabulary_facts_store (V := V)).sgVote_eq_of_fields h₁ h₂ h₃

/-- The field `sgVote_erase_eq_of_fields` of `StoreFacts` at `Model.spec`: named attestations
    with the same validator, round and confirmed block have erasures with the same SG vote. -/
theorem spec_sgVote_erase_eq_of_fields :
    ∀ {a b : NamedAttestation V} (h₁ : a.val_index = b.val_index)
    (h₂ : a.round = b.round) (h₃ : a.confirmed = b.confirmed),
    (Model.spec (V := V)).sgVote a.erase = (Model.spec (V := V)).sgVote b.erase := by
  intro a b h₁ h₂ h₃
  rw [spec_sgVote_eq]
  exact (Model.vocabulary_facts_store (V := V)).sgVote_erase_eq_of_fields h₁ h₂ h₃

/-- The field `sgVote_round_eq_round` of `StoreFacts` at `Model.spec`: the SG vote of `A` has
    the round of `A`. -/
theorem spec_sgVote_round_eq_round :
    ∀ (A : CombinedAttestation V), ((Model.spec (V := V)).sgVote A).round = A.round := by
  intro A
  rw [spec_sgVote_eq]
  exact (Model.vocabulary_facts_store (V := V)).sgVote_round_eq_round A

/-- The field `sgVote_val_index_eq_val_index` of `StoreFacts` at `Model.spec`: the SG vote of
    `A` has the validator of `A`. -/
theorem spec_sgVote_val_index_eq_val_index :
    ∀ (A : CombinedAttestation V),
    ((Model.spec (V := V)).sgVote A).val_index = A.val_index := by
  intro A
  rw [spec_sgVote_eq]
  exact (Model.vocabulary_facts_store (V := V)).sgVote_val_index_eq_val_index A

/-- The field `Sts_toHealing_F` of `StoreFacts` at `Model.spec`: the healing store of `st` has
    the finalized block `st.F`. -/
theorem spec_Sts_toHealing_F :
    ∀ (st : (Model.spec (V := V)).S), ((Model.spec (V := V)).toHealing st).toFG.F = st.F :=
  fun _ => rfl

/-- The field `Sts_toHealing_J` of `StoreFacts` at `Model.spec`: the healing store of `st` has
    the justified block `st.J`. -/
theorem spec_Sts_toHealing_J :
    ∀ (st : (Model.spec (V := V)).S), ((Model.spec (V := V)).toHealing st).toFG.J = st.J :=
  fun _ => rfl

/-- The field `toHealing_gs_T` of `StoreFacts` at `Model.specBase`: the Goldfish store of the
    healing store of `st` has the block tree `st.T`. -/
theorem specBase_toHealing_gs_T :
    ∀ (st : (Model.specBase (V := V)).S), ((Model.specBase (V := V)).toHealing st).toFG.toSG.toGoldfishStore.T = st.T :=
  fun st => (toProof_gs_T st).trans (Spec.Store.toProof_T st).symm

/-- The field `toHealing_gs_T` of `StoreFacts` at `Model.spec`: the Goldfish store of the
    healing store of `st` has the block tree `st.T`. -/
theorem spec_toHealing_gs_T :
    ∀ (st : (Model.spec (V := V)).S), ((Model.spec (V := V)).toHealing st).toFG.toSG.toGoldfishStore.T = st.T :=
  fun st => specBase_toHealing_gs_T st.val

/-- The field `toHealing_gs_gf_votes` of `StoreFacts` at `Model.specBase`: the Goldfish store
    of the healing store of `st` has the slot-`s` Goldfish vote list `st.gf_votes s`. -/
theorem specBase_toHealing_gs_gf_votes :
    ∀ (st : (Model.specBase (V := V)).S) (s : Slot),
    ((Model.specBase (V := V)).toHealing st).toFG.toSG.toGoldfishStore.gf_votes s = st.gf_votes s :=
  fun st s => (toProof_gs_gf_votes st s).trans (Spec.Store.toProof_gf_votes st s).symm

/-- The field `toHealing_gs_gf_votes` of `StoreFacts` at `Model.spec`: the Goldfish store of
    the healing store of `st` has the slot-`s` Goldfish vote list `st.gf_votes s`. -/
theorem spec_toHealing_gs_gf_votes :
    ∀ (st : (Model.spec (V := V)).S) (s : Slot),
    ((Model.spec (V := V)).toHealing st).toFG.toSG.toGoldfishStore.gf_votes s = st.gf_votes s :=
  fun st s => specBase_toHealing_gs_gf_votes st.val s

/-- The field `toHealing_gs_pool` of `StoreFacts` at `Model.spec`: the slot-`s` Goldfish votes
    of the Goldfish store of the healing store of `st` are `store_pool st s`. -/
theorem spec_toHealing_gs_pool :
    ∀ (st : (Model.spec (V := V)).S) (s : Slot),
    (Model.spec (V := V)).gs_pool ((Model.spec (V := V)).toHealing st).toFG.toSG.toGoldfishStore s = (Model.spec (V := V)).store_pool st s :=
  fun _ _ => rfl

/-- The field `toHealing_gs_s` of `StoreFacts` at `Model.specBase`: the Goldfish store of the
    healing store of `st` has the current slot `st.s`. -/
theorem specBase_toHealing_gs_s :
    ∀ (st : (Model.specBase (V := V)).S), ((Model.specBase (V := V)).toHealing st).toFG.toSG.toGoldfishStore.s = st.s :=
  fun st => (toProof_gs_s st).trans (Spec.Store.toProof_s st).symm

/-- The field `toHealing_gs_s` of `StoreFacts` at `Model.spec`: the Goldfish store of the
    healing store of `st` has the current slot `st.s`. -/
theorem spec_toHealing_gs_s :
    ∀ (st : (Model.spec (V := V)).S), ((Model.spec (V := V)).toHealing st).toFG.toSG.toGoldfishStore.s = st.s :=
  fun st => specBase_toHealing_gs_s st.val

/-- The field `toHealing_gs_timestamp_block` of `StoreFacts` at `Model.specBase`: the Goldfish
    store of the healing store of `st` has the block stamps `st.timestamp_block`. -/
theorem specBase_toHealing_gs_timestamp_block :
    ∀ (st : (Model.specBase (V := V)).S),
    ((Model.specBase (V := V)).toHealing st).toFG.toSG.toGoldfishStore.timestamp_block = st.timestamp_block :=
  fun st => (Model.vocabulary_facts_store (V := V)).toHealing_gs_timestamp_block st.toProof

/-- The field `toHealing_gs_timestamp_block` of `StoreFacts` at `Model.spec`: the Goldfish
    store of the healing store of `st` has the block stamps `st.timestamp_block`. -/
theorem spec_toHealing_gs_timestamp_block :
    ∀ (st : (Model.spec (V := V)).S),
    ((Model.spec (V := V)).toHealing st).toFG.toSG.toGoldfishStore.timestamp_block = st.timestamp_block :=
  fun st => specBase_toHealing_gs_timestamp_block st.val

/-- The field `toHealing_gs_timestamp_vote` of `StoreFacts` at `Model.specBase`: the Goldfish
    store of the healing store of `st` has the vote stamps `st.timestamp_vote`. -/
theorem specBase_toHealing_gs_timestamp_vote :
    ∀ (st : (Model.specBase (V := V)).S),
    ((Model.specBase (V := V)).toHealing st).toFG.toSG.toGoldfishStore.timestamp_vote = st.timestamp_vote :=
  fun st => funext fun u =>
    (toProof_gs_timestamp_vote st u).trans (Spec.Store.toProof_timestamp_vote st u).symm

/-- The field `toHealing_gs_timestamp_vote` of `StoreFacts` at `Model.spec`: the Goldfish store
    of the healing store of `st` has the vote stamps `st.timestamp_vote`. -/
theorem spec_toHealing_gs_timestamp_vote :
    ∀ (st : (Model.spec (V := V)).S),
    ((Model.spec (V := V)).toHealing st).toFG.toSG.toGoldfishStore.timestamp_vote = st.timestamp_vote :=
  fun st => specBase_toHealing_gs_timestamp_vote st.val

/-- The field `toHealing_h_j` of `StoreFacts` at `Model.spec`: the healing store of `st` has
    the justified height `st.h_j`. -/
theorem spec_toHealing_h_j :
    ∀ (st : (Model.spec (V := V)).S), ((Model.spec (V := V)).toHealing st).toFG.h_j = st.h_j :=
  fun _ => rfl

/-- The field `Sts_toHealing_h_max` of `StoreFacts` at `Model.spec`: the healing store of `st`
    has the largest seen height `st.h_max`. -/
theorem spec_Sts_toHealing_h_max :
    ∀ (st : (Model.spec (V := V)).S), ((Model.spec (V := V)).toHealing st).toFG.h_max = st.h_max :=
  fun _ => rfl

/-- The field `Sts_toHealing_sg_votes` of `StoreFacts` at `Model.specBase`: the round-`r` SG
    votes of the healing store of `st` are the images under `sgVote` of `store_sg_pool st r`. -/
theorem specBase_Sts_toHealing_sg_votes :
    ∀ (st : (Model.specBase (V := V)).S) (r : Round),
    ((Model.specBase (V := V)).toHealing st).toFG.toSG.sg_votes r = ((Model.specBase (V := V)).store_sg_pool st r).image (Model.specBase (V := V)).sgVote := by
  intro st r
  have := (Model.vocabulary_facts_store (V := V)).Sts_toHealing_sg_votes st.toProof r
  change st.toProof.toHealing.toFG.toSG.sg_votes r =
    (DecoupledConsensusModel.Protocol.Store.sg_pool st.toProof r).image
      DecoupledConsensusModel.Protocol.sgVote at this
  rw [toProof_sgs_sg_votes, toProof_store_sg_pool] at this
  rw [specBase_sgVote_eq]
  exact this

/-- The field `Sts_toHealing_sg_votes` of `StoreFacts` at `Model.spec`: the round-`r` SG votes
    of the healing store of `st` are the images under `sgVote` of `store_sg_pool st r`. -/
theorem spec_Sts_toHealing_sg_votes :
    ∀ (st : (Model.spec (V := V)).S) (r : Round),
    ((Model.spec (V := V)).toHealing st).toFG.toSG.sg_votes r = ((Model.spec (V := V)).store_sg_pool st r).image (Model.spec (V := V)).sgVote :=
  fun st r => specBase_Sts_toHealing_sg_votes st.val r

/-- The field `Sts_toHealing_σ` of `StoreFacts` at `Model.spec`: the healing store of `st` has
    the chain-state map `st.σ`. -/
theorem spec_Sts_toHealing_σ :
    ∀ (st : (Model.spec (V := V)).S), ((Model.spec (V := V)).toHealing st).toFG.σ = st.σ :=
  fun _ => rfl

/-! ### The resolution test -/

omit [DecidableEq V] [Fintype V] [Inhabited V] in
/-- The spec form of a block has the spec form of its root. -/
private theorem block_toSpec_root (B : Block V) :
    (Spec.Block.toSpec B).root = Spec.BlockId.toSpec B.root := by
  cases B
  · simp only [Spec.Block.toSpec, Spec.Block.root, Block.root]
    rw [← Spec.BlockId.toProof_genesisRoot, Spec.BlockId.toSpec_toProof]
  · simp only [Spec.Block.toSpec, Spec.Block.root, Block.root]

omit [DecidableEq V] [Fintype V] [Inhabited V] in
/-- The spec form of a block has the block's slot. -/
private theorem block_toSpec_slot (B : Block V) :
    (Spec.Block.toSpec B).slot = B.slot := by
  cases B <;> simp only [Spec.Block.toSpec, Spec.Block.slot, Block.slot]

omit [Fintype V] [Inhabited V] in
/-- Looking up the spec form of the root `r` in the spec forms of `T` finds the spec form of the
    block `Block.find? T r` finds. -/
private theorem find?_map_toSpec (T : Finset (Block V)) (r : BlockId) :
    Spec.Block.find? (T.map ChainStateToHandlers.blockToSpecEmb)
        (Spec.BlockId.toSpec r) =
      (Block.find? T r).map Spec.Block.toSpec := by
  unfold Spec.Block.find? Block.find?
  rw [Spec.pickUnique?_eq, Spec.pickUnique?_map,
    ← Spec.pickUnique?_eq]
  congr 2
  funext B
  show decide ((Spec.Block.toSpec B).root = Spec.BlockId.toSpec r) = _
  rw [block_toSpec_root]
  exact decide_eq_decide.mpr ⟨fun h => by
    simpa using congrArg Spec.BlockId.toProof h, fun h => h ▸ rfl⟩

/-- The field `resolved_eq_true_iff` of `StoreFacts` at `Model.spec`: an outcome `b` of
    `resolved T u` is `true` exactly when `Block.find?` finds a block `X` with `u`'s head root in
    `T` and `X`'s slot is at most `u`'s. -/
theorem spec_resolved_eq_true_iff :
    ∀ (T : Finset (Block V)) (u : GoldfishVote V) (b : Bool),
    (Model.spec (V := V)).resolved T u ⇢ b →
    (b = true ↔ ∃ X : Block V, Block.find? T u.head = some X ∧ X.slot ≤ u.slot) := by
  intro T u b hb
  have h := (returns_successOutcomes _ _).mp hb
  simp only [Spec.Protocol.resolved, Spec.blockWithRoot] at h
  split_ifs at h with h2
  · cases h
    unfold DecoupledConsensusModel.Protocol.resolved
    cases Block.find? T u.head <;> simp
  · rw [show (Spec.GoldfishVote.toSpec u).head = Spec.BlockId.toSpec u.head
      from rfl, find?_map_toSpec] at h
    cases hf : Block.find? T u.head with
    | none =>
      rw [hf] at h
      simp only [Option.map_none, pure_bind, ne_eq, not_true_eq_false, dite_false] at h
      cases h
      simp
    | some X =>
      rw [hf] at h
      simp only [Option.map_some, pure_bind, ne_eq, reduceCtorEq, not_false_eq_true, dite_true,
        Option.value] at h
      cases h
      simp [Spec.GoldfishVote.toSpec, block_toSpec_slot]

section RunFacts

end RunFacts

end SpecRecord.StoreFacts
