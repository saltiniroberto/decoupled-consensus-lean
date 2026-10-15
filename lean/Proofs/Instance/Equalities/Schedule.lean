import Proofs.Instance.Objects
import Spec
import Model.Vocabulary

/-!
# Equalities for the schedule routines

For each member of the schedule family of the record, the `DecoupledConsensusModel` routine filling
it equals the spec's routine at `Config.toSpec E hc cfg`. The five slot times read only the
environment `E`, so their lemmas hold for every `hc` and `cfg`.
-/

set_option autoImplicit false

namespace SpecRecord

open Spec

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The slot times -/

/-- The record's member `proposal_time`: `DecoupledConsensusModel.Protocol.proposal_time E s` is the
    spec's `C.proposal_time s` at `C = Config.toSpec E hc cfg`, for every `hc` and `cfg`. -/
theorem toProof_proposal_time (E : DecoupledConsensusModel.Env V)
    (hc : DecoupledConsensusModel.Protocol.HealConfig)
    (cfg : DecoupledConsensusModel.Protocol.HeightConfig) (s : Slot) :
    DecoupledConsensusModel.Protocol.proposal_time E s =
      (Config.toSpec E hc cfg).proposal_time s := rfl

/-- The record's member `vote_time`: `DecoupledConsensusModel.Protocol.vote_time E s` is the spec's
    `C.vote_time s` at `C = Config.toSpec E hc cfg`. -/
theorem toProof_vote_time (E : DecoupledConsensusModel.Env V)
    (hc : DecoupledConsensusModel.Protocol.HealConfig)
    (cfg : DecoupledConsensusModel.Protocol.HeightConfig) (s : Slot) :
    DecoupledConsensusModel.Protocol.vote_time E s = (Config.toSpec E hc cfg).vote_time s := rfl

/-- The record's member `support_cutoff`: `DecoupledConsensusModel.Protocol.support_cutoff E s` is
    the spec's `C.gf_confirmation_time s` at `C = Config.toSpec E hc cfg`. -/
theorem toProof_support_cutoff (E : DecoupledConsensusModel.Env V)
    (hc : DecoupledConsensusModel.Protocol.HealConfig)
    (cfg : DecoupledConsensusModel.Protocol.HeightConfig) (s : Slot) :
    DecoupledConsensusModel.Protocol.support_cutoff E s =
      (Config.toSpec E hc cfg).gf_confirmation_time s := rfl

/-- The record's member `view_freeze`: `DecoupledConsensusModel.Protocol.view_freeze E s` is the
    spec's `C.view_freeze s` at `C = Config.toSpec E hc cfg`. -/
theorem toProof_view_freeze (E : DecoupledConsensusModel.Env V)
    (hc : DecoupledConsensusModel.Protocol.HealConfig)
    (cfg : DecoupledConsensusModel.Protocol.HeightConfig) (s : Slot) :
    DecoupledConsensusModel.Protocol.view_freeze E s =
      (Config.toSpec E hc cfg).view_freeze s := rfl

/-- The record's member `confirmation_time`:
    `DecoupledConsensusModel.Protocol.confirmation_time E s` is the spec's `C.confirmation_time s`
    at `C = Config.toSpec E hc cfg`. -/
theorem toProof_confirmation_time (E : DecoupledConsensusModel.Env V)
    (hc : DecoupledConsensusModel.Protocol.HealConfig)
    (cfg : DecoupledConsensusModel.Protocol.HeightConfig) (s : Slot) :
    DecoupledConsensusModel.Protocol.confirmation_time E s =
      (Config.toSpec E hc cfg).confirmation_time s := rfl

/-! ## The votes of one validator -/

section Votes

omit [Fintype V]

/-- The record's member `votes_by`: the votes of `v` in the image of `votes` are the image of the
    spec's `Protocol.votes_by votes v`. -/
theorem toProof_votes_by (votes : Finset (GoldfishVote V)) (v : V) :
    DecoupledConsensusModel.Protocol.votes_by (votes.map GoldfishVote.toProofEmb) v =
      (Protocol.votes_by votes v).map GoldfishVote.toProofEmb := by
  simp only [DecoupledConsensusModel.Protocol.votes_by, Protocol.votes_by, Finset.filter_map]
  rfl

/-- The record's member `equivocates`: `v` equivocates in the image of `votes` exactly when the
    spec's `Protocol.equivocates votes v` holds. -/
theorem toProof_equivocates (votes : Finset (GoldfishVote V)) (v : V) :
    DecoupledConsensusModel.Protocol.equivocates (votes.map GoldfishVote.toProofEmb) v =
      Protocol.equivocates votes v := by
  simp only [DecoupledConsensusModel.Protocol.equivocates, Protocol.equivocates,
    toProof_votes_by, Finset.card_map]

/-- The record's member `participates`: `v` has a vote in the image of `votes` exactly when the
    spec's `Protocol.participates votes v` holds. -/
theorem toProof_participates (votes : Finset (GoldfishVote V)) (v : V) :
    DecoupledConsensusModel.Protocol.participates (votes.map GoldfishVote.toProofEmb) v =
      Protocol.participates votes v := by
  simp only [DecoupledConsensusModel.Protocol.participates, Protocol.participates,
    toProof_votes_by, Finset.card_map]

end Votes

end SpecRecord
