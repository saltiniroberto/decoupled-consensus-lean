import Proofs.Instance.Objects
import Spec
import Model.Vocabulary

/-!
# Equalities for the chain-state routines

For each member of the chain-state family of the record, the `DecoupledConsensusModel` routine
filling it, applied to the `toProof` images of the spec's data, equals the image of the spec's
routine at the `toSpec` images of the parameters. A routine that reads only some of the parameters
has its lemma stated for every value of the others.
-/

set_option autoImplicit false

namespace SpecRecord

open Spec

variable {V : Type}

/-- The slot of a block's image is the block's slot. -/
private theorem block_toProof_slot (B : Block V) : B.toProof.slot = B.slot := by
  cases B <;> rfl

/-- The named image of an attestation carries the image of the finality pair `(h, r)`, the root
`r` mapped, exactly when the attestation carries `(h, r)`. -/
private theorem finality_pair_toProofNamed_eq (a : Attestation V) (h : Height) (r : BlockId) :
    a.toProofNamed.finality_pair = some ⟨h, r.toProof⟩ ↔ a.finality_pair = some ⟨h, r⟩ := by
  cases a with
  | mk v r c hp fp =>
    cases fp with
    | none => simp [Attestation.toProofNamed]
    | some p =>
      cases p
      simp [Attestation.toProofNamed, FinalityPair.toProof]

/-- The targeted reading of the named image of `p` at `h` and the image of `r` is the target vote at
    `h` for the image of `r` exactly when `p` is the target vote at `h` for `r`. -/
private theorem targeted_eq_target (p : HeightPair) (h : Height) (r : BlockId) :
    (if p.toProofNamed.matchesEntry h r.toProof then p.toProofNamed.erase else .empty) =
        DecoupledConsensusModel.HeightPair.target h r.toProof ↔ p = .vote h r false := by
  cases p with
  | empty => simp [HeightPair.toProofNamed, DecoupledConsensusModel.NamedHeightPair.matchesEntry]
  | vote h' r' timeout =>
    by_cases hc : h' = h ∧ r' = r <;> cases timeout <;>
      simp [HeightPair.toProofNamed, DecoupledConsensusModel.NamedHeightPair.matchesEntry,
        DecoupledConsensusModel.NamedHeightPair.erase, hc]

/-- The targeted reading of the named image of `p` at `h` and the image of `r` is the timeout vote
    at `h` exactly when `p` is the timeout vote at `h` for `r`. -/
private theorem targeted_eq_timeout (p : HeightPair) (h : Height) (r : BlockId) :
    (if p.toProofNamed.matchesEntry h r.toProof then p.toProofNamed.erase else .empty) =
        DecoupledConsensusModel.HeightPair.timeout h ↔ p = .vote h r true := by
  cases p with
  | empty => simp [HeightPair.toProofNamed, DecoupledConsensusModel.NamedHeightPair.matchesEntry]
  | vote h' r' timeout =>
    by_cases hc : h' = h ∧ r' = r <;> cases timeout <;>
      simp [HeightPair.toProofNamed, DecoupledConsensusModel.NamedHeightPair.matchesEntry,
        DecoupledConsensusModel.NamedHeightPair.erase, hc]

/-- The attestations of a block's named image are the block's attestations, each mapped by
`Attestation.toProofNamed`. -/
private theorem block_toProofNamed_attestations (B : Block V) :
    B.toProofNamed.attestations = B.attestations.map Attestation.toProofNamed := by
  cases B <;> rfl

/-! ## The initial chain state and the updates -/

/-- The record's member `cs_initial`: the `DecoupledConsensusModel` chain state of the genesis block
    is the image of the spec's `Protocol.ChainState.initial`. -/
theorem toProof_cs_initial :
    (DecoupledConsensusModel.Protocol.ChainState.initial :
        DecoupledConsensusModel.Protocol.ChainState V) =
      (Protocol.ChainState.initial : Protocol.ChainState V).toProof := rfl

/-! ## One attestation -/

section Attestation

variable [DecidableEq V]

/-- The `DecoupledConsensusModel` one-attestation step with the targeted reading, on the image of
    `σ` and the named image of `a`, is the image of the spec's `Protocol.process_attestation σ a`: a
    timeout vote is counted only when it names the block that entered the current height. -/
theorem toProof_process_attestation_with_targeted (σ : Protocol.ChainState V)
    (a : Attestation V) :
    DecoupledConsensusModel.Protocol.process_attestation_with
        (DecoupledConsensusModel.Protocol.TimeoutBinding.targeted V) σ.toProof a.toProofNamed =
      (Protocol.process_attestation σ a).toProof := by
  have hfp : (DecoupledConsensusModel.Protocol.TimeoutBinding.view
      (DecoupledConsensusModel.Protocol.TimeoutBinding.targeted V) σ.toProof
        a.toProofNamed).finality_pair = a.toProofNamed.finality_pair := rfl
  have hhp : (DecoupledConsensusModel.Protocol.TimeoutBinding.view
      (DecoupledConsensusModel.Protocol.TimeoutBinding.targeted V) σ.toProof
        a.toProofNamed).height_pair =
      (if a.height_pair.toProofNamed.matchesEntry σ.h σ.T_h.root.toProof then
        a.height_pair.toProofNamed.erase else .empty) := by
    simp only [DecoupledConsensusModel.Protocol.TimeoutBinding.view,
      DecoupledConsensusModel.Protocol.TimeoutBinding.targeted,
      DecoupledConsensusModel.Protocol.TimeoutBinding.targetedHeightPair,
      Protocol.ChainState.toProof_h, Protocol.ChainState.toProof_T_h, Block.toProof_root]
    rfl
  have hval : (DecoupledConsensusModel.Protocol.TimeoutBinding.view
      (DecoupledConsensusModel.Protocol.TimeoutBinding.targeted V) σ.toProof
        a.toProofNamed).val_index = a.val_index := rfl
  simp only [DecoupledConsensusModel.Protocol.process_attestation_with,
    DecoupledConsensusModel.Protocol.process_attestation, Protocol.process_attestation,
    Id.run, hfp, hhp, hval, Finset.union_singleton, Protocol.ChainState.toProof_h_F, Protocol.ChainState.toProof_h_j,
    Protocol.ChainState.toProof_J, Protocol.ChainState.toProof_h, Protocol.ChainState.toProof_T_h,
    Block.toProof_root, finality_pair_toProofNamed_eq, targeted_eq_target, targeted_eq_timeout,
    Bool.and_eq_true, decide_eq_true_eq]
  split_ifs <;> rfl

end Attestation

/-! ## The height events -/

section HeightEvents

variable [DecidableEq V] [Fintype V]

/-- The record's member `nonjustifiable`:
    `DecoupledConsensusModel.Protocol.nonjustifiable cfg h h_F` is the spec's
    `Protocol.nonjustifiable` at `Config.toSpec E hc cfg`, for every `E` and `hc`. -/
theorem toProof_nonjustifiable (E : DecoupledConsensusModel.Env V)
    (hc : DecoupledConsensusModel.Protocol.HealConfig)
    (cfg : DecoupledConsensusModel.Protocol.HeightConfig) (h h_F : Height) :
    DecoupledConsensusModel.Protocol.nonjustifiable cfg h h_F =
      Protocol.nonjustifiable (Config.toSpec E hc cfg) h h_F := rfl

/-- The record's member `advance_height`: `DecoupledConsensusModel.Protocol.advance_height cfg` of
    the image of `σ` is the image of the spec's `Protocol.advance_height` at
    `Config.toSpec E hc cfg`, for every `E` and `hc`. -/
theorem toProof_advance_height (E : DecoupledConsensusModel.Env V)
    (hc : DecoupledConsensusModel.Protocol.HealConfig)
    (cfg : DecoupledConsensusModel.Protocol.HeightConfig) (σ : Protocol.ChainState V) :
    DecoupledConsensusModel.Protocol.advance_height cfg σ.toProof =
      (Protocol.advance_height (Config.toSpec E hc cfg) σ).toProof := rfl

/-- The record's member `finalityReady`: `DecoupledConsensusModel.Protocol.finalityReady E` of the
    image of `σ` is the spec's `Protocol.finalityReady` at `Provisional.toSpec E`. -/
theorem toProof_finalityReady (E : DecoupledConsensusModel.Env V) (σ : Protocol.ChainState V) :
    DecoupledConsensusModel.Protocol.finalityReady E σ.toProof =
      Protocol.finalityReady (Provisional.toSpec E) σ := rfl

/-- The record's member `targetReady`: `DecoupledConsensusModel.Protocol.targetReady E` of the image
    of `σ` is the spec's `Protocol.targetReady` at `Provisional.toSpec E`. -/
theorem toProof_targetReady (E : DecoupledConsensusModel.Env V) (σ : Protocol.ChainState V) :
    DecoupledConsensusModel.Protocol.targetReady E σ.toProof =
      Protocol.targetReady (Provisional.toSpec E) σ := rfl

/-- The record's member `progReady`: `DecoupledConsensusModel.Protocol.progReady E cfg` of the image
    of `σ` is the spec's `Protocol.progReady` at `Config.toSpec E hc cfg` and
    `Provisional.toSpec E`, for every `hc`. -/
theorem toProof_progReady (E : DecoupledConsensusModel.Env V)
    (hc : DecoupledConsensusModel.Protocol.HealConfig)
    (cfg : DecoupledConsensusModel.Protocol.HeightConfig) (σ : Protocol.ChainState V) :
    DecoupledConsensusModel.Protocol.progReady E cfg σ.toProof =
      Protocol.progReady (Config.toSpec E hc cfg) (Provisional.toSpec E) σ := by
  simp only [DecoupledConsensusModel.Protocol.progReady, Protocol.progReady,
    Protocol.ChainState.toProof_T_h, Protocol.ChainState.toProof_s, block_toProof_slot]
  rfl

/-- The record's member `process_height_events`:
    `DecoupledConsensusModel.Protocol.process_height_events E cfg` of the image of `σ` is the image
    of the spec's `Protocol.process_height_events` at `Config.toSpec E hc cfg` and
    `Provisional.toSpec E`, for every `hc`. -/
theorem toProof_process_height_events (E : DecoupledConsensusModel.Env V)
    (hc : DecoupledConsensusModel.Protocol.HealConfig)
    (cfg : DecoupledConsensusModel.Protocol.HeightConfig) (σ : Protocol.ChainState V) :
    DecoupledConsensusModel.Protocol.process_height_events E cfg σ.toProof =
      (Protocol.process_height_events (Config.toSpec E hc cfg) (Provisional.toSpec E) σ).toProof := by
  have hfin : (if DecoupledConsensusModel.Protocol.finalityReady E σ.toProof then
        { σ.toProof with F := σ.toProof.J, h_F := σ.toProof.h_j } else σ.toProof) =
      (if Protocol.finalityReady (Provisional.toSpec E) σ then
        ({ σ with F := σ.J, h_F := σ.h_j } : Protocol.ChainState V) else σ).toProof := by
    rw [toProof_finalityReady]
    split <;> rfl
  simp only [DecoupledConsensusModel.Protocol.process_height_events,
    Protocol.process_height_events, Id.run, hfin, toProof_targetReady,
    toProof_progReady E hc cfg]
  split_ifs <;> rfl

end HeightEvents

/-! ## The chain state of a block -/

section Transition

variable [DecidableEq V]

/-- The `DecoupledConsensusModel` fold of the named images of `atts` from the image of `σ` is the
    image of the spec's fold of `atts` from `σ`. -/
private theorem toProof_foldl (σ : Protocol.ChainState V) (atts : List (Attestation V)) :
    (atts.map Attestation.toProofNamed).foldl
        (DecoupledConsensusModel.Protocol.process_attestation_with
          (DecoupledConsensusModel.Protocol.TimeoutBinding.targeted V)) σ.toProof =
      (atts.foldl Protocol.process_attestation σ).toProof := by
  induction atts generalizing σ with
  | nil => rfl
  | cons a atts ih =>
    simp only [List.map_cons, List.foldl_cons, toProof_process_attestation_with_targeted, ih]

/-- `DecoupledConsensusModel.Protocol.fold_rows` with the targeted reading, on the image of `σ`, the
    image of `B` and the named images of `atts`, is the image of the spec's
    `Protocol.process_attestations σ B atts`. -/
theorem toProof_fold_rows (σ : Protocol.ChainState V) (B : Block V)
    (atts : List (Attestation V)) :
    DecoupledConsensusModel.Protocol.fold_rows
        (DecoupledConsensusModel.Protocol.TimeoutBinding.targeted V) σ.toProof B.toProof
        (atts.map Attestation.toProofNamed) =
      (Protocol.process_attestations σ B atts).toProof := by
  have hs : { σ.toProof with s := B.toProof.slot } =
      ({ σ with s := B.slot } : Protocol.ChainState V).toProof := by
    rw [block_toProof_slot]
    rfl
  simp only [DecoupledConsensusModel.Protocol.fold_rows, Protocol.process_attestations, Id.run,
    List.forIn_pure_yield_eq_foldl, hs, toProof_foldl]
  rfl

variable [Fintype V]

/-- The record's member `named_transition`:
    `DecoupledConsensusModel.Protocol.named_transition E cfg` of the image of `σ` and the named
    image of `B` is the image of the spec's `Protocol.state_transition` at `Config.toSpec E hc cfg`
    and `Provisional.toSpec E`, for every `hc`. -/
theorem toProof_named_transition (E : DecoupledConsensusModel.Env V)
    (hc : DecoupledConsensusModel.Protocol.HealConfig)
    (cfg : DecoupledConsensusModel.Protocol.HeightConfig) (σ : Protocol.ChainState V)
    (B : Block V) :
    DecoupledConsensusModel.Protocol.named_transition E cfg σ.toProof B.toProofNamed =
      (Protocol.state_transition (Config.toSpec E hc cfg) (Provisional.toSpec E) σ B).toProof := by
  simp only [DecoupledConsensusModel.Protocol.named_transition,
    DecoupledConsensusModel.Protocol.transition_rows, Protocol.state_transition, Id.run,
    Block.toProofNamed_erase, block_toProofNamed_attestations, toProof_fold_rows,
    toProof_process_height_events E hc cfg]
  rfl

end Transition

end SpecRecord
