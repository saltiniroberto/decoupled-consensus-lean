import Proofs.Instance.Objects
import Spec
import Model.Vocabulary

/-!
# Equalities for the store routines

For each member of the store family of the record, the `DecoupledConsensusModel` routine filling it,
applied to the `toProof` images of the spec's data, equals the image of the spec's routine. The
image of a store `st` as a Goldfish store is `st.toProof.toHealing.toFG.toSG.toGoldfishStore`. The
member `gs_timestamp_block` has no lemma here: two blocks of the tree can have one image.
-/

set_option autoImplicit false

namespace SpecDraftRecord

open Spec

variable {V : Type} [DecidableEq V]

private theorem getElem_fun {α β : Type} (f : α → β) (a : α) : f[a] = f a := rfl

/-! ## The readers of the Goldfish store -/

section GoldfishStore

/-- The record's member `gs_s`: the slot of the image of `st` as a Goldfish store is `st.s`. -/
theorem toProof_gs_s (st : Store V) :
    st.toProof.toHealing.toFG.toSG.toGoldfishStore.s = st.s := rfl

/-- The record's member `gs_T`: the tree of the image of `st` as a Goldfish store is the image of
    `st.T`. -/
theorem toProof_gs_T (st : Store V) :
    st.toProof.toHealing.toFG.toSG.toGoldfishStore.T = st.T.image Block.toProof := rfl

/-- The record's member `gs_timestamp_vote`: the image of `st` as a Goldfish store stamps `vote` as
    `st` stamps `GoldfishVote.toSpec vote`. -/
theorem toProof_gs_timestamp_vote (st : Store V)
    (vote : DecoupledConsensusModel.GoldfishVote V) :
    st.toProof.toHealing.toFG.toSG.toGoldfishStore.timestamp_vote vote =
      st.timestamp_vote (GoldfishVote.toSpec vote) := rfl

/-- The record's member `gs_gf_votes`: the Goldfish votes of slot `s` in the image of `st` as a
    Goldfish store are the images of `st`'s Goldfish votes of slot `s`. -/
theorem toProof_gs_gf_votes (st : Store V) (s : Slot) :
    st.toProof.toHealing.toFG.toSG.toGoldfishStore.gf_votes s =
      (st.gf_votes s).map GoldfishVote.toProof := rfl

/-- The record's member `gs_live_confirmed`: the `live_confirmed` of the image of `st` as a Goldfish
    store is the image of `st.live_confirmed`. -/
theorem toProof_gs_live_confirmed (st : Store V) :
    st.toProof.toHealing.toFG.toSG.toGoldfishStore.live_confirmed =
      st.live_confirmed.toProof := rfl

end GoldfishStore

/-! ## The vote sets -/

/-- The record's member `store_pool`: `DecoupledConsensusModel.Protocol.Store.pool` of the image of
    `st` at slot `s` is the image of the spec's `st.pool s`. -/
theorem toProof_store_pool (st : Store V) (s : Slot) :
    DecoupledConsensusModel.Protocol.Store.pool st.toProof s =
      (st.pool s).map GoldfishVote.toProofEmb := by
  ext x
  simp [DecoupledConsensusModel.Protocol.Store.pool, Store.pool, getElem_fun]

/-- The record's member `gs_pool`: `DecoupledConsensusModel.Protocol.GoldfishStore.pool` of the
    image of `st` as a Goldfish store, at slot `s`, is the image of the spec's `st.pool s`. -/
theorem toProof_gs_pool (st : Store V) (s : Slot) :
    DecoupledConsensusModel.Protocol.GoldfishStore.pool
        st.toProof.toHealing.toFG.toSG.toGoldfishStore s =
      (st.pool s).map GoldfishVote.toProofEmb :=
  toProof_store_pool st s

omit [DecidableEq V] in
/-- The record's member `sgVote`: the SG vote of the image of the attestation `a` is the image of
    the spec's `Protocol.sgVote a`. -/
theorem toProof_sgVote (a : Attestation V) :
    DecoupledConsensusModel.Protocol.sgVote a.toProof = (Protocol.sgVote a).toProof := rfl

/-- The record's member `store_sg_pool`: `DecoupledConsensusModel.Protocol.Store.sg_pool` of the
    image of `st` at round `r` is the image of the spec's `st.sg_pool r`. -/
theorem toProof_store_sg_pool (st : Store V) (r : Round) :
    DecoupledConsensusModel.Protocol.Store.sg_pool st.toProof r =
      (st.sg_pool r).image Attestation.toProof := by
  ext x
  simp [DecoupledConsensusModel.Protocol.Store.sg_pool, Store.sg_pool, getElem_fun]

/-! ## The initial store -/

/-- The block standing for `B` on the initial store is the genesis block exactly when `B` is the
    genesis block. -/
private theorem init_blockOfImage_eq_genesis (B : DecoupledConsensusModel.Block V) :
    (Store.init : Store V).blockOfImage B = Block.genesis ↔
      B = DecoupledConsensusModel.Block.genesis := by
  constructor
  · intro h
    have := Store.toProof_blockOfImage (Store.init : Store V) B
    rw [h] at this
    exact this.symm
  · rintro rfl
    rfl

/-- The record's member `store_init`: `DecoupledConsensusModel.Protocol.Store.init` is the image of
    the spec's `Store.init`. -/
theorem toProof_store_init :
    (DecoupledConsensusModel.Protocol.Store.init : DecoupledConsensusModel.Protocol.Store V) =
      (Store.init : Store V).toProof := by
  have hT : (Store.init : Store V).T.image Block.toProof =
      {DecoupledConsensusModel.Block.genesis} := by
    simp [Store.init]
  have hts : (fun B => (Store.init : Store V).timestamp_block
        ((Store.init : Store V).blockOfImage B)) =
      fun B => if B = DecoupledConsensusModel.Block.genesis then
        some DecoupledConsensusModel.genesisStamp else none := by
    funext B
    show (if (Store.init : Store V).blockOfImage B = Block.genesis then _ else _) = _
    simp only [init_blockOfImage_eq_genesis]
    rfl
  have hσ : (fun B => ((Store.init : Store V).σ ((Store.init : Store V).blockOfImage B)).toProof) =
      fun _ => DecoupledConsensusModel.Protocol.ChainState.initial := rfl
  simp only [Store.toProof, hT, hts, hσ]
  rfl

end SpecDraftRecord
