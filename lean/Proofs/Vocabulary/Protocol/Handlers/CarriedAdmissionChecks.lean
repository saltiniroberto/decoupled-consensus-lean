module
public import Proofs.Vocabulary.Protocol.Schedule.Alignment
public import Proofs.Vocabulary.Protocol.ValidatorClient.Schedule
public import Proofs.Vocabulary.Protocol.Handlers.Blocks
import Proofs.Vocabulary.Protocol.Handlers.Execution
import Proofs.Vocabulary.Protocol.Handlers.Pool

@[expose] public section

/-!
# Checks on carried rows

Facts about the SG vote handler `on_sg_vote` and its fold over carried rows: which fields they keep,
and the receipt stamps of new and held rows.
-/


namespace DecoupledConsensusModel.Proofs.CarriedAdmission
open DecoupledConsensusModel
open Protocol
open Internal Execution
variable {V : Type} [DecidableEq V]

/-- A fold of `on_sg_vote` keeps the clock, slot, block tree, block stamps, Goldfish votes and vote
    stamps. -/
theorem fold_rows_fixed_fields (hc : Protocol.HealConfig)
    (rows : List (CombinedAttestation V)) (st : Store V) :
    let out := rows.foldl (on_sg_vote hc) st
    out.t = st.t ∧ out.s = st.s ∧ out.T = st.T ∧
      out.timestamp_block = st.timestamp_block ∧ out.gf_votes = st.gf_votes ∧
      out.timestamp_vote = st.timestamp_vote := by
  induction rows generalizing st with
  | nil => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | cons a rows ih =>
    simpa only [List.foldl_cons, on_sg_vote_time, Proofs.Optimistic.on_sg_vote_slot,
      on_sg_vote_T, Protocol.on_sg_vote_timestamp_block,
      Protocol.on_sg_vote_gf_votes, Protocol.on_sg_vote_timestamp_vote]
      using ih (on_sg_vote hc st a)


/-- An attestation newly added to the SG pool by `on_sg_vote` is stamped with the store's clock. -/
theorem on_sg_vote_new_receipt_stamp (hc : Protocol.HealConfig)
    (st : Store V) (a : CombinedAttestation V)
    (hpre : a ∉ st.sg_pool a.round) (hpost : a ∈ (on_sg_vote hc st a).sg_pool a.round) :
    (on_sg_vote hc st a).timestamp_sg_vote (sgVote a) = some (st.t : Stamp) := by
  unfold on_sg_vote at hpost ⊢
  split at hpost
  · exact False.elim (hpre hpost)
  · rename_i hguard
    rw [if_neg hguard]
    simp

private theorem projection_in_round_votes (st : Store V) (a b : CombinedAttestation V)
    (hb : b ∈ st.sg_pool b.round) (hproj : sgVote a = sgVote b) :
    a.confirmed ∈ round_votes st a := by
  have hround : a.round = b.round := congrArg Protocol.SGVote.round hproj
  have hval : a.val_index = b.val_index := congrArg Protocol.SGVote.val_index hproj
  have hconfirmed : a.confirmed = b.confirmed := congrArg Protocol.SGVote.confirmed hproj
  unfold round_votes
  apply Finset.mem_image.mpr
  refine ⟨b, Finset.mem_filter.mpr ⟨?_, hval.symm⟩, hconfirmed.symm⟩
  simpa only [hround] using hb

/-- `on_sg_vote` leaves the store unchanged on an attestation whose SG projection equals that of a
    held attestation. -/
theorem on_sg_vote_duplicate_projection (hc : Protocol.HealConfig)
    (st : Store V) (a b : CombinedAttestation V)
    (hb : b ∈ st.sg_pool b.round) (hproj : sgVote a = sgVote b) :
    on_sg_vote hc st a = st := by
  have hdup := projection_in_round_votes st a b hb hproj
  exact if_pos (Or.inr (Or.inr (Or.inl hdup)))

/-- `on_sg_vote` keeps the receipt stamp of every attestation held in its own round's pool. -/
theorem on_sg_vote_existing_row_stamp (hc : Protocol.HealConfig)
    (st : Store V) (incoming b : CombinedAttestation V) (hb : b ∈ st.sg_pool b.round) :
    (on_sg_vote hc st incoming).timestamp_sg_vote (sgVote b) =
      st.timestamp_sg_vote (sgVote b) := by
  by_cases hproj : sgVote incoming = sgVote b
  · rw [on_sg_vote_duplicate_projection hc st incoming b hb hproj]
  · unfold on_sg_vote
    split
    · rfl
    · exact if_neg (Ne.symm hproj)


theorem fold_rows_preserve_existing_stamp (hc : Protocol.HealConfig)
    (rows : List (CombinedAttestation V)) (st : Store V) (b : CombinedAttestation V)
    (hb : b ∈ st.sg_pool b.round) :
    (rows.foldl (on_sg_vote hc) st).timestamp_sg_vote (sgVote b) =
      st.timestamp_sg_vote (sgVote b) := by
  induction rows generalizing st with
  | nil => rfl
  | cons a rows ih =>
    have hb' := Proofs.HealingLemmas.sg_pool_subset_on_sg_vote hc st a b.round hb
    exact (ih (on_sg_vote hc st a) hb').trans (on_sg_vote_existing_row_stamp hc st a b hb)


#print axioms fold_rows_fixed_fields
#print axioms on_sg_vote_new_receipt_stamp
#print axioms on_sg_vote_duplicate_projection
#print axioms on_sg_vote_existing_row_stamp
#print axioms fold_rows_preserve_existing_stamp
end DecoupledConsensusModel.Proofs.CarriedAdmission

end
