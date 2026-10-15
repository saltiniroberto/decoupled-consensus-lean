module
public import Proofs.Vocabulary.Execution.OutageProvenance
public import Proofs.Vocabulary.Execution.HealthyLocalFacts
import Proofs.Vocabulary.Execution.ReceiptCallsBase
import Proofs.Vocabulary.Protocol.Handlers.Execution
import Mathlib.RingTheory.WittVector.IsPoly

@[expose] public section

/-!
# Stamp carriers for SG rows

The store transitions that keep every held SG row in its own round's bucket with a receipt stamp no
later than a fixed bound.
-/
namespace DecoupledConsensusModel.Proofs.NamedOutageHistory.SGArrival
open Execution Internal.NamedOutageEntry Internal.NamedStableChainOutage
variable {V : Type} [DecidableEq V] [Fintype V]

def Carry (before after : Protocol.NamedStore V) : Prop :=
  ∀ a : NamedAttestation V, a ∈ before.sg_rows a.round →
    a ∈ after.sg_rows a.round ∧
      after.core.timestamp_sg_vote (Protocol.sgVote a.erase) =
        before.core.timestamp_sg_vote (Protocol.sgVote a.erase)

omit [Fintype V] in
theorem finality_stamp (st : Protocol.Store V) (sigma : Protocol.ChainState V) :
    (Protocol.update_finality st sigma).timestamp_sg_vote = st.timestamp_sg_vote := by
  simp only [Protocol.update_finality]
  split_ifs <;> rfl

theorem gf_checked_stamp (E : Env V) (st : Protocol.Store V) (u : GoldfishVote V) :
    (Protocol.on_goldfish_vote_checked E st u).timestamp_sg_vote = st.timestamp_sg_vote := by
  simp only [Protocol.on_goldfish_vote_checked, Protocol.on_goldfish_vote]
  split_ifs <;> rfl

theorem gf_fold_stamp (E : Env V) (st : Protocol.Store V) (rows : List (GoldfishVote V)) :
    (rows.foldl (Protocol.on_goldfish_vote_checked E) st).timestamp_sg_vote =
      st.timestamp_sg_vote := by
  induction rows generalizing st with
  | nil => rfl
  | cons a rows ih => rw [List.foldl_cons, ih, gf_checked_stamp]

theorem core_block_rows (S : Setup V) (st : Protocol.NamedStore V) (B : NamedBlock V) :
    (Protocol.NamedStore.process_block_core S.E S.hc S.cfg st B).sg_rows = st.sg_rows := by
  unfold Protocol.NamedStore.process_block_core
  split_ifs
  · exact NamedStore.commit_rows st _ B
  · rfl

theorem core_block_stamp (S : Setup V) (st : Protocol.NamedStore V) (B : NamedBlock V) :
    (Protocol.NamedStore.process_block_core S.E S.hc S.cfg st B).core.timestamp_sg_vote =
      st.core.timestamp_sg_vote := by
  unfold Protocol.NamedStore.process_block_core
  split_ifs
  · rw [NamedStore.commit_core]
    unfold Protocol.on_block_checked_using
    split_ifs
    · dsimp only [Protocol.on_block_using]
      split_ifs <;> first
        | rfl
        | (rw [finality_stamp, gf_fold_stamp])
    · rfl
  · rfl

theorem row_carry (S : Setup V) (st : Protocol.NamedStore V) (incoming : NamedAttestation V)
    (hcoh : Proofs.NamedStore.Coherent S.E S.cfg st) :
    Carry st (Protocol.NamedAdmission.admit_row S.hc st incoming) := by
  intro a ha
  exact ⟨NamedReceiptCallsF1.admit_row_mem_mono S.hc st incoming a ha,
    NamedAdmission.existing_row_stamp S.hc st hcoh.2.2.2.1 incoming a ha⟩

/-- The clock is at most `bound`, and every held row is in its own round's bucket with a first stamp
    at most `bound`. -/
def Data (bound : Time) (st : Protocol.NamedStore V) : Prop :=
  st.core.t ≤ bound ∧ ∀ k (a : NamedAttestation V), a ∈ st.sg_rows k →
    a.round = k ∧ ∃ stamp : Time, stamp ≤ bound ∧
      st.core.timestamp_sg_vote (Protocol.sgVote a.erase) = some (stamp : Stamp)

omit [Fintype V] in
theorem row_mem_cases_at (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (incoming a : NamedAttestation V) (k : Round)
    (ha : a ∈ (Protocol.NamedAdmission.admit_row hc st incoming).sg_rows k) :
    a ∈ st.sg_rows k ∨ (a = incoming ∧ k = incoming.round) := by
  dsimp only [Protocol.NamedAdmission.admit_row] at ha
  split_ifs at ha <;> aesop

theorem row_data (S : Setup V) (bound : Time) (st : Protocol.NamedStore V)
    (incoming : NamedAttestation V) (hcoh : Proofs.NamedStore.Coherent S.E S.cfg st)
    (hd : Data bound st) : Data bound (Protocol.NamedAdmission.admit_row S.hc st incoming) := by
  refine ⟨?_, ?_⟩
  · simpa only [(NamedAdmission.admit_row_fixed_fields S.hc st incoming).1] using hd.1
  · intro k a ha
    rcases row_mem_cases_at S.hc st incoming a k ha with hold | hnew
    · obtain ⟨hr, stamp, hstampBound, hstamp⟩ := hd.2 k a hold
      have hown : a ∈ st.sg_rows a.round := by simpa only [hr] using hold
      refine ⟨hr, stamp, hstampBound, ?_⟩
      exact ((row_carry S st incoming hcoh) a hown).2.trans hstamp
    · obtain ⟨haeq, hkeq⟩ := hnew
      subst a
      subst k
      by_cases hold : incoming ∈ st.sg_rows incoming.round
      · obtain ⟨_, stamp, hstampBound, hstamp⟩ := hd.2 incoming.round incoming hold
        exact ⟨rfl, stamp, hstampBound,
          ((row_carry S st incoming hcoh) incoming hold).2.trans hstamp⟩
      · exact ⟨rfl, st.core.t, hd.1,
          NamedReceiptCallsF1.full_new_row_stamp S.hc st incoming hold ha⟩

theorem rows_data (S : Setup V) (bound : Time) (st : Protocol.NamedStore V)
    (rows : List (NamedAttestation V)) (hcoh : Proofs.NamedStore.Coherent S.E S.cfg st)
    (hd : Data bound st) : Data bound (Protocol.NamedAdmission.admit_rows S.hc st rows) := by
  induction rows generalizing st with
  | nil => exact hd
  | cons a rows ih =>
    exact ih _ (NamedAdmission.coherent_admit_row S.E S.hc S.cfg st a hcoh)
      (row_data S bound st a hcoh hd)


theorem tick_rows_after_proposal (gc : Protocol.GradeContract V) (S : Setup V)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (record : Protocol.NamedRecord) (t : Time) :
    let s := S.E.slotOf t
    let st0 := Protocol.NamedStore.setClock S.E st t
    let st1 := if 0 < s ∧ t = Protocol.proposal_time S.E s ∧ S.E.proposer s = nd.val_index then
      (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg nd st0).1 else st0
    ∀ a : NamedAttestation V, a ∈ st1.sg_rows a.round →
      a ∈ (Protocol.NamedTick.tick gc S.E S.hc S.cfg nd st record t).1.sg_rows a.round := by
  let s := S.E.slotOf t
  let st0 := Protocol.NamedStore.setClock S.E st t
  let st1 := if 0 < s ∧ t = Protocol.proposal_time S.E s ∧ S.E.proposer s = nd.val_index then
    (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg nd st0).1 else st0
  let st2 := if 0 < s ∧ t = Protocol.vote_time S.E s then
    (Protocol.NamedDuties.goldfish_vote_with gc S.E S.hc nd st1).1 else st1
  let st3 := if 0 < s ∧ t = Protocol.support_cutoff S.E s then
    Protocol.NamedDuties.update_confirmation_with gc S.E S.hc st2 (s - 1) else st2
  have h32 : st3.sg_rows = st1.sg_rows := by dsimp only [st3, st2]; split_ifs <;> rfl
  have hstore : (Protocol.NamedTick.tick gc S.E S.hc S.cfg nd st record t).1 =
      (if t = S.hc.a S.E.Δ (S.hc.round_of st3.core.s) ∧ nd.awake (S.hc.round_of st3.core.s) = true
        then (Protocol.NamedDuties.attest_with gc S.E S.hc nd st3 record).1 else st3) := by
    rw [NamedTick.tick_computed_duties]
    dsimp only [st3, st2, st1, st0, s]
    split_ifs <;> rfl
  change ∀ row : NamedAttestation V, row ∈ st1.sg_rows row.round →
    row ∈ (Protocol.NamedTick.tick gc S.E S.hc S.cfg nd st record t).1.sg_rows row.round
  intro row hrow
  have ha3 : row ∈ st3.sg_rows row.round := by rw [h32]; exact hrow
  rw [hstore]
  split_ifs
  · exact NamedReceiptCallsF1.admit_row_mem_mono S.hc st3 _ row ha3
  · exact ha3

theorem action_tick_store (S : Setup V) (reader : V) (before : NamedNodeState V)
    (q : Round) (hawake : (S.node reader).awake q = true) :
    (NamedNode.tick S reader before (S.a q)).1.st =
      let n := actionReadFrom S before q
      (Protocol.NamedDuties.attest_with (NamedProfile.gradeContract n.cache)
        S.E S.hc (S.node reader) n.st n.record).1 := by
  have hpos : 0 < S.E.slotOf (S.a q) := by
    rw [Setup.a, Protocol.a_eq_support_cutoff_succ, Proofs.Optimistic.slotOf_support_cutoff]
    exact Nat.zero_lt_succ _
  have hs : S.a q = Protocol.support_cutoff S.E (S.E.slotOf (S.a q)) := by
    rw [Setup.a, Protocol.a_eq_support_cutoff_succ, Proofs.Optimistic.slotOf_support_cutoff]
  have hp : ¬ (0 < S.E.slotOf (S.a q) ∧ S.a q = Protocol.proposal_time S.E (S.E.slotOf (S.a q)) ∧
      S.E.proposer (S.E.slotOf (S.a q)) = (S.node reader).val_index) := by
    intro h
    exact Proofs.Optimistic.support_cutoff_ne_proposal_time S.E _ (hs.symm.trans h.2.1)
  have hv : ¬ (0 < S.E.slotOf (S.a q) ∧ S.a q = Protocol.vote_time S.E (S.E.slotOf (S.a q))) := by
    intro h
    exact Proofs.Optimistic.support_cutoff_ne_vote_time S.E _ (hs.symm.trans h.2)
  change (Protocol.NamedTick.tick (NamedProfile.gradeContract (preparedCache S before (S.a q)))
    S.E S.hc S.cfg (S.node reader) before.st before.record (S.a q)).1 = _
  rw [NamedTick.tick_computed_duties]
  simp only [if_neg hp, if_neg hv, if_pos (And.intro hpos hs)]
  have hround : S.hc.round_of (Protocol.NamedDuties.update_confirmation_with
      (NamedProfile.gradeContract (preparedCache S before (S.a q))) S.E S.hc
      (Protocol.NamedStore.setClock S.E before.st (S.a q)) (S.E.slotOf (S.a q) - 1)).core.s = q :=
    Proofs.HealingLemmas.round_of_slotOf_a S q
  simp only [hround, hawake, and_self, if_true]
  rfl


end DecoupledConsensusModel.Proofs.NamedOutageHistory.SGArrival

end
