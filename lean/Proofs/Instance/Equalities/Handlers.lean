import Proofs.Instance.Objects
import Proofs.Instance.ObjectConstants
import Proofs.Instance.Equalities.Store
import Proofs.Instance.Equalities.Schedule
import Proofs.Instance.Equalities.ChainState
import Proofs.Instance.Equalities.ForkChoice
import Spec
import Model.Vocabulary

/-!
# Equalities for the handler routines

For the members `carried_attestations_admissible`, `round_votes`, `on_goldfish_vote`,
`on_goldfish_vote_checked`, `on_sg_vote`, `admit_row`, `admit_rows` and `ns_initial` of the handlers
family of the record, the `DecoupledConsensusModel` routine filling the member, applied to the
images of the spec's data, equals the image of the spec's routine at `Config.toSpec E hc cfg` and
`Provisional.toSpec E`. The spec's `admit_attestation` is compared with `on_sg_vote` through
`Store.toProof` and with `admit_row` through `Store.toProofNamed`.
-/

set_option autoImplicit false

namespace SpecRecord

open Spec

variable {V : Type} [DecidableEq V]

private theorem getElem_fun {α β : Type} (f : α → β) (a : α) : f[a] = f a := rfl

/-! ## The test on a block's attestations, and the confirmed blocks of a round -/

section Window

variable [Fintype V]

/-- The record's member `carried_attestations_admissible`:
    `DecoupledConsensusModel.Protocol.carried_attestations_admissible hc` of the image of `B` is the
    spec's `Protocol.included_attestations_admissible` of `B` at `Config.toSpec E hc cfg`, for every
    `E` and `cfg`. -/
theorem toProof_carried_attestations_admissible (E : DecoupledConsensusModel.Env V)
    (hc : DecoupledConsensusModel.Protocol.HealConfig)
    (cfg : DecoupledConsensusModel.Protocol.HeightConfig) (B : Block V) :
    DecoupledConsensusModel.Protocol.carried_attestations_admissible hc B.toProof =
      Protocol.included_attestations_admissible (Config.toSpec E hc cfg) B := by
  simp [DecoupledConsensusModel.Protocol.carried_attestations_admissible,
    Protocol.included_attestations_admissible, List.all_map, Function.comp_def]
  rfl

end Window

/-- The record's member `round_votes`: the confirmed blocks the validator of the image of `a` has
    named in `a`'s round in the image of `st` are the images of those of the spec's
    `Protocol.round_votes st a`, `none` mapped to `none`. -/
theorem toProof_round_votes (st : Store V) (a : Attestation V) :
    DecoupledConsensusModel.Protocol.round_votes st.toProof a.toProof =
      (Protocol.round_votes st a).map (Function.Embedding.optionMap BlockId.toProofEmb) := by
  ext x
  simp [DecoupledConsensusModel.Protocol.round_votes, Protocol.round_votes,
    toProof_store_sg_pool, Finset.map']

/-! ## The admission of a Goldfish vote and of an attestation -/

/-- The record's member `on_goldfish_vote`: the image of `st` after it admits the image of `vote` is
    the image of the spec's `Protocol.on_goldfish_vote st vote`. -/
theorem toProof_on_goldfish_vote (st : Store V) (vote : GoldfishVote V) :
    DecoupledConsensusModel.Protocol.on_goldfish_vote st.toProof vote.toProof =
      (Protocol.on_goldfish_vote st vote).toProof := by
  have hc1 : (vote.toProof.slot < st.toProof.s - 1 ∨ st.toProof.s < vote.toProof.slot ∨
      vote.toProof ∈ st.toProof.gf_votes vote.toProof.slot) ↔
      (vote.slot < st.s - 1 ∨ st.s < vote.slot ∨ vote ∈ st.gf_votes vote.slot) := by
    simp [List.mem_map, GoldfishVote.toProof_injective.eq_iff]
  have hc2 : DecoupledConsensusModel.Protocol.equivocates (st.toProof.pool vote.toProof.slot)
      vote.toProof.val_index = Protocol.equivocates (st.pool vote.slot) vote.val_index := by
    rw [show vote.toProof.slot = vote.slot from rfl, toProof_store_pool]
    exact toProof_equivocates _ _
  unfold DecoupledConsensusModel.Protocol.on_goldfish_vote
  simp only [hc1, hc2]
  simp only [Protocol.on_goldfish_vote, Id.run, pure, getElem_fun, Bool.or_eq_true,
    decide_eq_true_eq, or_assoc]
  split_ifs
  · rfl
  · rfl
  · simp only [Store.toProof]
    congr 1
    · funext u
      by_cases hu : u = vote.toProof
      · subst hu; simp
      · have hu' : GoldfishVote.toSpec u ≠ vote := by
          rintro rfl; exact hu (GoldfishVote.toProof_toSpec u).symm
        simp [hu, hu']
    · funext k
      by_cases hk : k = vote.slot
      · subst hk; simp
      · simp [hk]

section Admission

variable [Fintype V]

/-- The record's member `on_goldfish_vote_checked`:
    `DecoupledConsensusModel.Protocol.on_goldfish_vote_checked E` on the images of `st` and `vote`
    is the image of the spec's `Protocol.on_goldfish_vote_checked` at `Provisional.toSpec E`. -/
theorem toProof_on_goldfish_vote_checked (E : DecoupledConsensusModel.Env V)
    (st : Store V) (vote : GoldfishVote V) :
    DecoupledConsensusModel.Protocol.on_goldfish_vote_checked E st.toProof vote.toProof =
      (Protocol.on_goldfish_vote_checked (Provisional.toSpec E) st vote).toProof := by
  unfold DecoupledConsensusModel.Protocol.on_goldfish_vote_checked
  simp only [Protocol.on_goldfish_vote_checked, Id.run, pure, Provisional.toSpec_committee,
    GoldfishVote.toProof_val_index, GoldfishVote.toProof_slot, toProof_on_goldfish_vote]
  split_ifs <;> rfl

omit [Fintype V] in
/-- The spec's `attestation_admissible` is true exactly when none of its four rejecting conditions
    holds. -/
private theorem attestation_admissible_iff (C : Config) (st : Store V) (a : Attestation V) :
    Protocol.attestation_admissible C st a = true ↔
      ¬ (a.round < C.round_of st.s - C.η_SG ∨ C.round_of st.s < a.round ∨
        a.confirmed ∈ Protocol.round_votes st a ∨ (Protocol.round_votes st a).card = 2) := by
  simp only [Protocol.attestation_admissible, Id.run, Bool.or_eq_true, decide_eq_true_eq, pure,
    or_assoc]
  split_ifs with h
  · simp [h]
  · simp [h]

/-- The record's member `on_sg_vote`: `DecoupledConsensusModel.Protocol.on_sg_vote hc` on the images
    of `st` and `a` is the image of the spec's `Protocol.admit_attestation` at
    `Config.toSpec E hc cfg`, for every `E` and `cfg`. -/
theorem toProof_on_sg_vote (E : DecoupledConsensusModel.Env V)
    (hc : DecoupledConsensusModel.Protocol.HealConfig)
    (cfg : DecoupledConsensusModel.Protocol.HeightConfig) (st : Store V)
    (a : Attestation V) :
    DecoupledConsensusModel.Protocol.on_sg_vote hc st.toProof a.toProof =
      (Protocol.admit_attestation (Config.toSpec E hc cfg) st a).toProof := by
  have hc1 : (a.toProof.round < hc.round_of st.toProof.s - hc.η_SG ∨
      hc.round_of st.toProof.s < a.toProof.round ∨
      a.toProof.confirmed ∈ DecoupledConsensusModel.Protocol.round_votes st.toProof a.toProof ∨
      (DecoupledConsensusModel.Protocol.round_votes st.toProof a.toProof).card = 2) ↔
      ¬ (Protocol.attestation_admissible (Config.toSpec E hc cfg) st a = true) := by
    rw [attestation_admissible_iff, not_not, toProof_round_votes]
    have hconf : a.toProof.confirmed =
        (Function.Embedding.optionMap BlockId.toProofEmb) a.confirmed := rfl
    rw [hconf, Finset.mem_map', Finset.card_map]
    rfl
  unfold DecoupledConsensusModel.Protocol.on_sg_vote
  simp only [hc1]
  simp only [Protocol.admit_attestation, Protocol.add_attestation, Id.run, pure, getElem_fun]
  split_ifs
  · simp only [Store.toProof]
    congr 1
    · funext u
      by_cases hu : u = (Protocol.sgVote a).toProof
      · subst hu; simp [toProof_sgVote]
      · have hu' : Protocol.SGVote.toSpec u ≠ Protocol.sgVote a := by
          intro h; apply hu; rw [← h, Protocol.SGVote.toProof_toSpec]
        simp [hu, hu', toProof_sgVote]
    · funext k
      by_cases hk : k = a.round
      · subst hk; simp
      · simp [hk]
  · rfl

/-- The record's member `admit_row`: `DecoupledConsensusModel.Protocol.NamedAdmission.admit_row hc`
    on the named images of `st` and `row` is the named image of the spec's
    `Protocol.admit_attestation` at `Config.toSpec E hc cfg`, for every `E` and `cfg`. -/
theorem toProof_admit_row (E : DecoupledConsensusModel.Env V)
    (hc : DecoupledConsensusModel.Protocol.HealConfig)
    (cfg : DecoupledConsensusModel.Protocol.HeightConfig) (st : Store V)
    (row : Attestation V) :
    DecoupledConsensusModel.Protocol.NamedAdmission.admit_row hc st.toProofNamed
        row.toProofNamed =
      (Protocol.admit_attestation (Config.toSpec E hc cfg) st row).toProofNamed := by
  unfold DecoupledConsensusModel.Protocol.NamedAdmission.admit_row
  simp only [Store.toProofNamed_core, Attestation.toProofNamed_erase, toProof_on_sg_vote E hc cfg,
    toProof_store_sg_pool, Attestation.toProofNamed_round]
  by_cases hadm : Protocol.attestation_admissible (Config.toSpec E hc cfg) st row = true
  · have hres : Protocol.admit_attestation (Config.toSpec E hc cfg) st row =
        Protocol.add_attestation st row := by
      simp only [Protocol.admit_attestation, Id.run, hadm, if_true, pure]
    have hnew : row.toProof ∉ (st.sg_pool row.round).image Attestation.toProof := by
      intro hmem
      obtain ⟨b, hb, hbrow⟩ := Finset.mem_image.mp hmem
      apply (attestation_admissible_iff _ st row).mp hadm
      refine Or.inr (Or.inr (Or.inl ?_))
      have hpool : row.toProof ∈
          DecoupledConsensusModel.Protocol.Store.sg_pool st.toProof row.toProof.round := by
        rw [show row.toProof.round = row.round from rfl, toProof_store_sg_pool]
        exact hmem
      have hup : (Function.Embedding.optionMap BlockId.toProofEmb) row.confirmed ∈
          DecoupledConsensusModel.Protocol.round_votes st.toProof row.toProof :=
        Finset.mem_image.mpr ⟨row.toProof, Finset.mem_filter.mpr ⟨hpool, rfl⟩, rfl⟩
      rw [toProof_round_votes] at hup
      exact (Finset.mem_map' _).mp hup
    have hatt : (Protocol.add_attestation st row).attestations =
        Function.update st.attestations row.round (st.attestations row.round ++ [row]) := rfl
    have hin : row.toProof ∈
        ((Protocol.add_attestation st row).sg_pool row.round).image Attestation.toProof := by
      apply Finset.mem_image_of_mem
      simp [Store.sg_pool, getElem_fun, hatt]
    rw [hres, if_pos ⟨hnew, hin⟩]
    simp only [Store.toProofNamed]
    congr 1
    funext r
    by_cases hr : r = row.round
    · subst hr; simp [hatt]
    · simp [hr, hatt]
  · have hres : Protocol.admit_attestation (Config.toSpec E hc cfg) st row = st := by
      simp only [Protocol.admit_attestation, Id.run, hadm, pure]
      rfl
    rw [hres, if_neg (fun h => h.1 h.2)]
    rfl

/-- The record's member `admit_rows`:
    `DecoupledConsensusModel.Protocol.NamedAdmission.admit_rows hc` on the named images of `st` and
    of the attestations of `rows` is the named image of the spec's `Protocol.admit_attestations` at
    `Config.toSpec E hc cfg`, for every `E` and `cfg`. -/
theorem toProof_admit_rows (E : DecoupledConsensusModel.Env V)
    (hc : DecoupledConsensusModel.Protocol.HealConfig)
    (cfg : DecoupledConsensusModel.Protocol.HeightConfig) (st : Store V)
    (rows : List (Attestation V)) :
    DecoupledConsensusModel.Protocol.NamedAdmission.admit_rows hc st.toProofNamed
        (rows.map Attestation.toProofNamed) =
      (Protocol.admit_attestations (Config.toSpec E hc cfg) st rows).toProofNamed := by
  simp only [DecoupledConsensusModel.Protocol.NamedAdmission.admit_rows,
    Protocol.admit_attestations, Id.run, List.forIn_pure_yield_eq_foldl]
  induction rows generalizing st with
  | nil => rfl
  | cons row rows ih =>
    simp only [List.map_cons, List.foldl_cons, toProof_admit_row E hc cfg, ih]

omit [Fintype V] in
/-- The record's member `ns_initial`: `DecoupledConsensusModel.Protocol.NamedStore.initial` is the
    named image of the spec's `Store.init`. -/
theorem toProof_ns_initial :
    (DecoupledConsensusModel.Protocol.NamedStore.initial :
        DecoupledConsensusModel.Protocol.NamedStore V) =
      (Store.init : Store V).toProofNamed := by
  simp only [DecoupledConsensusModel.Protocol.NamedStore.initial, Store.toProofNamed,
    ← toProof_store_init]
  congr 1

end Admission

end SpecRecord
