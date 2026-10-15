import Model.Record.ChainStateRunFacts
import Proofs.Claims.Spec2Claims.Claim13bModel_derive_named
import Proofs.Claims.Spec2Claims.Claim13bModel_AdvanceHeight
import Proofs.Claims.Spec2Claims.Claim13bModel_targetReady
import Proofs.Claims.Spec2Claims.Claim13bModel_conflictsWithFinality
import Proofs.Claims.Spec2Claims.Claim13bModel_e1Fields
import Proofs.Claims.Spec2Claims.Claim13bModel_e2Fields
import Proofs.Claims.Spec2Claims.Claim13bModel_Slashable
import Proofs.Claims.Spec2Claims.Claim13beRoute3_70b
import Proofs.Vocabulary.Protocol.ChainState.FinalityCertificates
import Proofs.Vocabulary.Protocol.ChainState.JustificationCertificates
import Proofs.Vocabulary.Protocol.ChainState.CheckpointHeights
import Proofs.Vocabulary.Protocol.ChainState.CheckpointAlgebra
import Proofs.Vocabulary.Protocol.ChainState.HeightProgressFixedRootRows
import Proofs.Vocabulary.Protocol.ChainState.HeightRegimeNamedBaseDeadline
import Proofs.Vocabulary.Generic.EvaluationStore

/-!
# The chain-state record's instance `vocabulary`

`vocabulary` fills `ChainStateModel` with the protocol's `ChainState` and its routines.
`vocabulary_facts` proves `ChainStateFacts` for it and `vocabulary_runFacts` proves
`ChainStateVocabularyRunFacts`.
-/

set_option autoImplicit false

/-- The simp set of equivalences between a definition that names a chain-state routine and the same
    definition stated over the record at the instance `vocabulary`. -/
register_simp_attr chain_state_vocabulary

namespace DecoupledConsensusModel.Sts.Record

open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Protocol (HeightConfig)

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The chain-state family given by the protocol's `ChainState`: each reader is its field and each
    operation the protocol's routine. -/
def vocabulary : ChainStateModel V where
  CS := Protocol.ChainState V
  h σ := σ.h
  T_h σ := σ.T_h
  nj σ := σ.nj
  J σ := σ.J
  h_j σ := σ.h_j
  F σ := σ.F
  h_F σ := σ.h_F
  progress σ := σ.progress
  target_participation σ := σ.target_participation
  Binding Row := Protocol.TimeoutBinding V Row
  targeted := Protocol.TimeoutBinding.targeted V
  process_attestation := Protocol.process_attestation
  process_attestation_with := Protocol.process_attestation_with
  fold_rows := Protocol.fold_rows
  process_height_events := Protocol.process_height_events
  finalityReady := Protocol.finalityReady
  targetReady := Protocol.targetReady
  progReady := Protocol.progReady
  named_transition := Protocol.named_transition
  derive_named := Protocol.derive_named
  conflictsWithFinality := Protocol.conflictsWithFinality
  e2Fields := Protocol.e2Fields
  Slashable := Protocol.Slashable

/-- The chain-state routines of `vocabulary` satisfy `ChainStateFacts`. -/
theorem vocabulary_facts : ChainStateFacts (vocabulary (V := V)) where
  derive_named_genesis_h := derive_named_genesis_h
  one_le_derive_named_h E cfg B := Protocol.one_le_derive_named_h E cfg B
  derive_height_mono := Proofs.NamedEntryHeight.derive_height_mono
  entry_eq_on_plateau := Proofs.NamedEntryHeight.entry_eq_on_plateau
  entry_ancestor_same_height := Proofs.NamedEntryHeight.entry_ancestor_same_height
  entry_geometry_ancestor := Proofs.NamedEntryHeight.entry_geometry_ancestor
  chainOrder_derive_named E cfg B :=
    ⟨(Proofs.NamedDerivationGeometry.chainOrder_derive_named E cfg B).heights_ordered,
      (Proofs.NamedDerivationGeometry.chainOrder_derive_named E cfg B).justified_below_height⟩
  derive_named_anchors_preceq := Proofs.NamedDerivationGeometry.derive_named_anchors_preceq
  justified_ancestor_height := Proofs.NamedCheckpointHeights.justified_ancestor_height
  namedJustification_selfTarget := Proofs.NamedCheckpointAlgebra.namedJustification_selfTarget
  namedFinalization_selfTarget_deadline E cfg B :=
    (priv% Proofs.Vocabulary.Protocol.ChainState.HeightRegimeNamedBaseDeadline
      DecoupledConsensusModel.Proofs.HealingSurface.namedFinalization_selfTarget_deadline) E cfg B
  namedJustification_entry_ancestor E cfg B :=
    (priv% Proofs.Vocabulary.Protocol.ChainState.HeightProgressFixedRootRows
      DecoupledConsensusModel.Proofs.HealingSurface.namedJustification_entry_ancestor) E cfg B
  justified_zero_is_genesis := Proofs.NamedJustificationCertificates.justified_zero_is_genesis
  finalized_zero_is_genesis := Proofs.NamedFinalityCertificates.finalized_zero_is_genesis
  finality_certificate := Proofs.NamedFinalityCertificates.finality_certificate
  height_crossing := Proofs.NamedFinalityCertificates.height_crossing
  derive_named_h_j_parent_le := derive_named_h_j_parent_le
  derive_named_h_j_step_cases := derive_named_h_j_step_cases
  derive_named_node_nj_of_h_eq := derive_named_node_nj_of_h_eq
  derive_named_checkpoint_entries := derive_named_checkpoint_entries
  derive_named_node_h_eq_succ_of_progressQuorum := derive_named_node_h_eq_succ_of_progressQuorum
  conflictsWithFinality_eq_false_of := conflictsWithFinality_eq_false_of
  e2Fields_eq_false_of := e2Fields_eq_false_of
  not_Slashable_of_fields left right hleft hright h2 :=
    (not_Slashable_iff left right).2
      (slashable_eq_false_of_fields left right (e1Fields_eq_false_of left right hleft hright) h2)

/-- The runs of the protocol satisfy `ChainStateVocabularyRunFacts` for `vocabulary`. -/
theorem vocabulary_runFacts : ChainStateVocabularyRunFacts (vocabulary (V := V)) where
  storeFinalizationOnChain_stateBefore := Proofs.Bridges.storeFinalizationOnChain_stateBefore
  storeFinalizationOnChain_stateBeforeTime :=
    Proofs.Bridges.storeFinalizationOnChain_stateBeforeTime
  justification_carrier_stateBefore :=
    Proofs.NamedJustificationCarrier.justification_carrier_stateBefore
  storeJustificationOnChain_stateBeforeTime :=
    Proofs.Bridges.storeJustificationOnChain_stateBeforeTime
  noHighJustifications_stateBeforeTime :=
    Proofs.NamedJustificationBound.noHighJustifications_stateBeforeTime
  heights_le_hMax_stateBefore := Proofs.NamedStoreBridge.heights_le_hMax_stateBefore
  derivedView_stateBefore_h S rho i v D hD :=
    congrArg Protocol.ChainState.h (Proofs.NamedStoreBridge.derivedView_stateBefore S rho i v D hD)
  action_witness S rho v r Cfg hCfg := by
    obtain ⟨C, hC, hCe, hσ, hW⟩ := Proofs.NamedActionSources.action_witness S rho v r Cfg hCfg
    exact ⟨C, hC, hCe, congrArg Protocol.ChainState.h hσ, congrArg Protocol.ChainState.T_h hσ,
      congrArg Protocol.ChainState.nj hσ, hW⟩
  derivedStateAgrees_actionStoreAtOn S _ Hs Xb _ hf v r D hD :=
    congrArg Protocol.ChainState.T_h (derivedStateAgrees_actionStoreAtOn S Hs Xb hf v r D hD)
  action_named_checkpointOn := action_named_checkpointOn
  honestHeightRow_confirmationWitnessOn := honestHeightRow_confirmationWitnessOn
  storeF_preceq_checkpoint_of_windowOn := storeF_preceq_checkpoint_of_windowOn

end DecoupledConsensusModel.Sts.Record
