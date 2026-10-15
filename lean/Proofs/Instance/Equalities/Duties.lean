import Proofs.Instance.Objects
import Proofs.Instance.ObjectConstants
import Proofs.Instance.Equalities.Handlers
import Spec
import Model.Vocabulary

/-!
# Equalities for the proposal-duty reads

For each member of the duties family of the record that the spec fills with a routine of its own,
the `DecoupledConsensusModel` routine filling it, applied to the `toProof` images of the spec's
data, equals the image of the spec's routine at `Config.toSpec E hc cfg`. A block or an attestation
is mapped by its named image (`toProofNamed`), which keeps the root of a timeout vote.
-/

set_option autoImplicit false

namespace SpecRecord

open Spec

variable {V : Type} [DecidableEq V]

/-! ## The admission window and the attestations the store holds -/

section Window

variable [Fintype V]

/-- The record's member `inWindow`: round `r` is in the admission window of the image of `st` under
    `hc` exactly when it is in the spec's `Protocol.in_admission_window` of `st` at
    `Config.toSpec E hc cfg`, for every `E` and `cfg`. -/
theorem toProof_inWindow (E : DecoupledConsensusModel.Env V)
    (hc : DecoupledConsensusModel.Protocol.HealConfig)
    (cfg : DecoupledConsensusModel.Protocol.HeightConfig) (st : Store V) (r : Round) :
    DecoupledConsensusModel.Protocol.ProposalRows.inWindow hc st.toProof r =
      Protocol.in_admission_window (Config.toSpec E hc cfg) st r := by
  simp only [DecoupledConsensusModel.Protocol.ProposalRows.inWindow, Protocol.in_admission_window,
    Bool.decide_and]
  rfl

/-- The record's member `processedRows`: the attestations the named image of `st` holds are the
    images, in the same order, of the spec's `Protocol.all_attestations` of `st`, for every `E` and
    `cfg`. -/
theorem toProof_processedRows (E : DecoupledConsensusModel.Env V)
    (hc : DecoupledConsensusModel.Protocol.HealConfig)
    (cfg : DecoupledConsensusModel.Protocol.HeightConfig) (st : Store V) :
    DecoupledConsensusModel.Protocol.NamedProposalRows.processedRows hc st.toProofNamed =
      (Protocol.all_attestations (Config.toSpec E hc cfg) st).map
        Attestation.toProofNamed := by
  simp only [DecoupledConsensusModel.Protocol.NamedProposalRows.processedRows,
    Protocol.all_attestations, List.map_flatMap, Store.toProofNamed_core,
    Store.toProof_s]
  rfl

/-- The record's member `poolRows`: the attestations the named image of `st` holds in its admission
    window are the images, in order, of the spec's `Protocol.attestations_in_window` of `st`, for
    every `E` and `cfg`. -/
theorem toProof_poolRows (E : DecoupledConsensusModel.Env V)
    (hc : DecoupledConsensusModel.Protocol.HealConfig)
    (cfg : DecoupledConsensusModel.Protocol.HeightConfig) (st : Store V) :
    DecoupledConsensusModel.Protocol.NamedProposalRows.poolRows hc st.toProofNamed =
      (Protocol.attestations_in_window (Config.toSpec E hc cfg) st).map
        Attestation.toProofNamed := by
  simp only [DecoupledConsensusModel.Protocol.NamedProposalRows.poolRows,
    Protocol.attestations_in_window, toProof_processedRows E hc cfg, List.filter_map,
    Function.comp_def, Attestation.toProofNamed_round, Store.toProofNamed_core,
    toProof_inWindow E hc cfg]

end Window

/-! ## The attestations a proposal includes -/

omit [DecidableEq V] in
/-- The record's member `chainRows`: the attestations included in the named image of `B` and its
    ancestors are the images, in order, of the spec's `Protocol.attestations_on_chain B`. -/
theorem toProof_chainRows (B : Block V) :
    DecoupledConsensusModel.Protocol.NamedProposalRows.chainRows B.toProofNamed=
      (Protocol.attestations_on_chain B).map Attestation.toProofNamed := by
  induction B with
  | genesis => rfl
  | node p s r gv gs ats pr ih =>
    simp only [Block.toProofNamed, DecoupledConsensusModel.Protocol.NamedProposalRows.chainRows,
      Protocol.attestations_on_chain, ih, List.map_append]

/-- `DecoupledConsensusModel.Protocol.NamedProposalRows.capPerSigner` of the images of `atts` is the
    list of the images of the spec's `capPerSigner atts`. -/
private theorem toProof_capPerSigner (atts : List (Attestation V)) :
    DecoupledConsensusModel.Protocol.NamedProposalRows.capPerSigner
        (atts.map Attestation.toProofNamed) =
      (Protocol.capPerSigner atts).map Attestation.toProofNamed := by
  simp only [DecoupledConsensusModel.Protocol.NamedProposalRows.capPerSigner,
    Protocol.capPerSigner, Id.run, bind_pure, Bool.and_eq_true, decide_eq_true_eq]
  suffices h : ∀ init : List (Attestation V),
      List.foldl
        (fun acc row =>
          if (decide (row ∈ acc) || decide (2 ≤ (List.filter (fun a =>
              decide (a.val_index = row.val_index ∧ a.round = row.round)) acc).length)) = true
          then acc else acc ++ [row])
        (init.map Attestation.toProofNamed) (atts.map Attestation.toProofNamed) =
      List.map Attestation.toProofNamed (forIn (m := Id) atts init fun a s =>
        if a ∉ s ∧ (List.filter (fun b => decide (b.val_index = a.val_index) &&
            decide (b.round = a.round)) s).length < 2
        then pure (ForInStep.yield (s ++ [a])) else pure (ForInStep.yield s)) from h []
  intro init
  induction atts generalizing init with
  | nil => rfl
  | cons a t ih =>
    have hmem : (a.toProofNamed ∈ init.map Attestation.toProofNamed) ↔ a ∈ init :=
      List.mem_map_of_injective Attestation.toProofNamed_injective
    have hlen : (List.filter (fun b => decide (b.val_index = a.toProofNamed.val_index ∧
        b.round = a.toProofNamed.round)) (init.map Attestation.toProofNamed)).length =
        (List.filter (fun b => decide (b.val_index = a.val_index) && decide (b.round = a.round))
          init).length := by
      rw [List.filter_map, List.length_map]
      congr 1
      refine List.filter_congr ?_
      intro b _
      simp only [Function.comp_apply, Attestation.toProofNamed_val_index,
        Attestation.toProofNamed_round, Bool.decide_and]
      rfl
    rw [List.forIn_cons, List.map_cons, List.foldl_cons]
    by_cases h : a ∉ init ∧
        (List.filter (fun b => decide (b.val_index = a.val_index) && decide (b.round = a.round))
          init).length < 2
    · have h' : ¬ ((decide (a.toProofNamed ∈ init.map Attestation.toProofNamed) ||
          decide (2 ≤ (List.filter (fun b => decide (b.val_index = a.toProofNamed.val_index ∧
            b.round = a.toProofNamed.round)) (init.map Attestation.toProofNamed)).length)) = true) := by
        rw [hlen]
        simp only [Bool.or_eq_true, decide_eq_true_eq, hmem, not_or, not_le]
        exact h
      rw [if_neg h']
      simp only [if_pos h, pure_bind]
      rw [← ih, List.map_append]
      rfl
    · have h' : (decide (a.toProofNamed ∈ init.map Attestation.toProofNamed) ||
          decide (2 ≤ (List.filter (fun b => decide (b.val_index = a.toProofNamed.val_index ∧
            b.round = a.toProofNamed.round)) (init.map Attestation.toProofNamed)).length)) = true := by
        rw [hlen]
        simp only [Bool.or_eq_true, decide_eq_true_eq, hmem]
        by_contra hc
        simp only [not_or, not_le] at hc
        exact h hc
      rw [if_pos h']
      simp only [if_neg h, pure_bind]
      exact ih init

/-- The record's member `proposalRows`: the attestations a proposal on the named image of `parent`
    includes from the images of `rows` are the images, in order, of the spec's
    `Protocol.proposal_attestations parent rows`. -/
theorem toProof_proposalRows (parent : Block V) (rows : List (Attestation V)) :
    DecoupledConsensusModel.Protocol.NamedProposalRows.proposalRows parent.toProofNamed
        (rows.map Attestation.toProofNamed) =
      (Protocol.proposal_attestations parent rows).map Attestation.toProofNamed := by
  have hex : DecoupledConsensusModel.Protocol.NamedProposalRows.excludeOnChain parent.toProofNamed
      (rows.map Attestation.toProofNamed) =
      (Protocol.excludeOnChain parent rows).map Attestation.toProofNamed := by
    simp only [DecoupledConsensusModel.Protocol.NamedProposalRows.excludeOnChain,
      Protocol.excludeOnChain, toProof_chainRows, List.filter_map, Function.comp_def,
      List.mem_map_of_injective Attestation.toProofNamed_injective, decide_not]
  simp only [DecoupledConsensusModel.Protocol.NamedProposalRows.proposalRows,
    Protocol.proposal_attestations, hex, toProof_capPerSigner]

end SpecRecord
