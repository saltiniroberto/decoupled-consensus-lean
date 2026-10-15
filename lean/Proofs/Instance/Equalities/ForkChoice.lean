import Proofs.Instance.Objects
import Spec
import Model.Vocabulary

/-!
# Equalities for the fork-choice routines

Each theorem `toProof_<member>` says that the `DecoupledConsensusModel` routine filling one member
of the fork-choice family of the record, applied to the `toProof` images of the spec's data, equals
the image of the spec's routine on the data. The members `fg_σ`, `finalized_descendants`, `viable`,
`viable_tree`, `get_filtered_block_tree_from` and `get_filtered_block_tree` have no theorem here:
`Block.toProof` is not injective, and their equality does not hold for every store and block.
-/

set_option autoImplicit false

namespace SpecRecord

open Spec

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The SG store and the FG store of a store's image -/

omit [DecidableEq V] [Fintype V] in
private theorem sgVote_toProof (a : Attestation V) :
    DecoupledConsensusModel.Protocol.sgVote a.toProof = (Protocol.sgVote a).toProof := rfl

omit [Fintype V] in
/-- The record's member `sgs_sg_votes`: the SG votes of round `r` in the SG store of the image of
    `st` are the images of `st`'s SG votes of round `r`. -/
theorem toProof_sgs_sg_votes (st : Store V) (r : Round) :
    st.toProof.toHealing.toFG.toSG.sg_votes r =
      (st.sg_votes r).map Protocol.SGVote.toProofEmb := by
  ext u
  simp [DecoupledConsensusModel.Protocol.Store.toHealing,
    DecoupledConsensusModel.Protocol.Store.sg_pool, Store.sg_votes, Store.sg_pool,
    sgVote_toProof, Finset.map', GetElem.getElem]

omit [Fintype V] in
/-- The record's member `fg_F`: the finalized block of the FG store of the image of `st` is the
    image of `st.F`. -/
theorem toProof_fg_F (st : Store V) : st.toProof.toHealing.toFG.F = st.F.toProof := rfl

omit [Fintype V] in
/-- The record's member `fg_J`: the justified block of the FG store of the image of `st` is the
    image of `st.J`. -/
theorem toProof_fg_J (st : Store V) : st.toProof.toHealing.toFG.J = st.J.toProof := rfl

omit [Fintype V] in
/-- The record's member `fg_h_j`: the justified height of the FG store of the image of `st` is
    `st.h_j`. -/
theorem toProof_fg_h_j (st : Store V) : st.toProof.toHealing.toFG.h_j = st.h_j := rfl

omit [Fintype V] in
/-- The record's member `fg_h_max`: the `h_max` of the FG store of the image of `st` is `st.h_max`. -/
theorem toProof_fg_h_max (st : Store V) : st.toProof.toHealing.toFG.h_max = st.h_max := rfl

/-! ## The fgroot -/

omit [Fintype V] in
/-- The record's member `get_fg_root`: the fgroot of the FG store of the image of `st` is the image
    of the spec's `Protocol.get_fg_root st`. -/
theorem toProof_get_fg_root (st : Store V) :
    DecoupledConsensusModel.Protocol.get_fg_root st.toProof.toHealing.toFG =
      (Protocol.get_fg_root st).toProof := by
  unfold DecoupledConsensusModel.Protocol.get_fg_root Protocol.get_fg_root
  rw [toProof_fg_h_max, toProof_fg_h_j, toProof_fg_J, toProof_fg_F]
  by_cases h : st.h_max = st.h_j + 1 <;> simp [h]

/-! ## Sets of Goldfish votes -/

omit [Fintype V] in
/-- The votes of `v` in the image of `votes` are the images of the votes of `v` in `votes`. -/
private theorem votes_by_map (votes : Finset (GoldfishVote V)) (v : V) :
    DecoupledConsensusModel.Protocol.votes_by (votes.map GoldfishVote.toProofEmb) v =
      (Protocol.votes_by votes v).map GoldfishVote.toProofEmb := by
  simp [DecoupledConsensusModel.Protocol.votes_by, Protocol.votes_by, Finset.filter_map,
    GoldfishVote.toProof]

omit [Fintype V] in
/-- `v` has a vote in the image of `votes` exactly when it has a vote in `votes`. -/
private theorem participates_map (votes : Finset (GoldfishVote V)) (v : V) :
    DecoupledConsensusModel.Protocol.participates (votes.map GoldfishVote.toProofEmb) v =
      Protocol.participates votes v := by
  simp [DecoupledConsensusModel.Protocol.participates, Protocol.participates, votes_by_map]

/-- The record's member `raw_participants`: the validators with a vote in the image of `votes` are
    the validators with a vote in `votes`. -/
theorem toProof_raw_participants (votes : Finset (GoldfishVote V)) :
    DecoupledConsensusModel.Protocol.raw_participants (votes.map GoldfishVote.toProofEmb) =
      Protocol.raw_participants votes := by
  simp only [DecoupledConsensusModel.Protocol.raw_participants, Protocol.raw_participants,
    participates_map]

/-- The record's member `voters_count`: `DecoupledConsensusModel.Protocol.voters_count E` of the
    image of `votes` at slot `s` is the spec's `Protocol.raw_voters_count votes`, for every `E` and
    `s`. -/
theorem toProof_voters_count (E : DecoupledConsensusModel.Env V)
    (votes : Finset (GoldfishVote V)) (s : Slot) :
    DecoupledConsensusModel.Protocol.voters_count E (votes.map GoldfishVote.toProofEmb) s =
      Protocol.raw_voters_count votes := by
  simp only [DecoupledConsensusModel.Protocol.voters_count,
    DecoupledConsensusModel.Protocol.raw_voters_count, Protocol.raw_voters_count,
    toProof_raw_participants]

omit [Fintype V] in
/-- The record's member `no_second_vote_in`: the image of `late` holds no second vote of the
    validator of the image of `vote` exactly when `late` holds no second vote of `vote`'s validator. -/
theorem toProof_no_second_vote_in (late : Finset (GoldfishVote V)) (vote : GoldfishVote V) :
    DecoupledConsensusModel.Protocol.no_second_vote_in (late.map GoldfishVote.toProofEmb)
        vote.toProof =
      Protocol.no_second_vote_in late vote := by
  have hval : ∀ u : GoldfishVote V, u.toProof.val_index = u.val_index := fun _ => rfl
  simp only [DecoupledConsensusModel.Protocol.no_second_vote_in, Protocol.no_second_vote_in,
    Finset.forall_mem_map, GoldfishVote.coe_toProofEmb, GoldfishVote.toProof_injective.eq_iff,
    hval]

/-! ## The rounds of the latest window and the proposer's view -/

/-- The record's member `latest_window`: `DecoupledConsensusModel.Protocol.latest_window η_SG r` is
    the spec's `Protocol.latest_window η_SG r`. -/
theorem toProof_latest_window (η_SG r : Round) :
    DecoupledConsensusModel.Protocol.latest_window η_SG r = Protocol.latest_window η_SG r := rfl

omit [Fintype V] in
/-- The record's member `proposer_view`: the votes the slot-`s` proposer counts in the Goldfish
    store of the image of `st` are the images, in order, of the spec's
    `Protocol.proposer_view st s`. -/
theorem toProof_proposer_view (st : Store V) (s : Slot) :
    DecoupledConsensusModel.Protocol.proposer_view
        st.toProof.toHealing.toFG.toSG.toGoldfishStore s =
      (Protocol.proposer_view st s).map GoldfishVote.toProof := rfl
