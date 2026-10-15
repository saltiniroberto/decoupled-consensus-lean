import Proofs.Instance.Facts.ChainState
import Proofs.Instance.Facts.Handlers

/-!
# The chain-state facts about runs, over `Model.spec`'s own runs

The fields of `ChainStateRunFacts` at `Model.spec` that read the worlds the model's own runs
reach, proved from the store invariant `OwnRunsInv` carried along every fold of events from the
initial world, and the bundle `Model.spec_runFacts_cs`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace SpecRecord.ChainStateRunFacts

open DecoupledConsensusModel
open DecoupledConsensusModel.Sts
open DecoupledConsensusModel.Sts.Record
open DecoupledConsensusModel.Execution
open SpecRecord.HandlersRunFacts
open SpecRecord.NoRaise
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-- `OwnRunsInv S st`: some tree block of `st` has `st`'s justified block and justified height in
    its chain state, every tree block's chain state has a height at most `st`'s `h_max`, and the
    named image of `st` is coherent with its roots in the tree. -/
def OwnRunsInv (S : Setup V) (st : Spec.Store V) : Prop :=
  (priv% Proofs.Vocabulary.Protocol.Handlers.JustificationCarrier
    DecoupledConsensusModel.Proofs.NamedJustificationCarrier.CoreJustifier) st.toProof ∧
  (priv% Proofs.Vocabulary.Protocol.Handlers.NumericStore
    DecoupledConsensusModel.Proofs.NamedNumericStore.CoreBound) st.toProof ∧
  RootsInv S st

/-- Every store step into a store of distinct roots keeps `OwnRunsInv`, together with `StoreOk` and
    `RunStoreInv`. -/
theorem ownRunsInv_step (S : Setup V) (τ : Time) (a b : Spec.Store V)
    (hs : StoreSteps.StoreStep (Setup.toSpec S).C (Setup.toSpec S).P τ a b)
    (hd : DistinctRoots b.T) (h : StoreOk a ∧ SubtypeEqualities.RunStoreInv a ∧ OwnRunsInv S a) :
    StoreOk b ∧ SubtypeEqualities.RunStoreInv b ∧ OwnRunsInv S b := by
  obtain ⟨hb1, hb2⟩ := base_step hs hd ⟨h.1, h.2.1⟩
  refine ⟨hb1, hb2, ?_⟩
  have hj := h.2.2
  cases hs with
  | grades g => exact hj
  | clock => exact hj
  | confirm x y z => exact hj
  | vote u =>
    have h1 := (priv% Proofs.Vocabulary.Protocol.Handlers.JustificationCarrier
      DecoupledConsensusModel.Proofs.NamedJustificationCarrier.gf_justifier) S.E a.toProof
      u.toProof hj.1
    have h2 := ((priv% Proofs.Vocabulary.Protocol.Handlers.NumericStore
      DecoupledConsensusModel.Proofs.NamedNumericStore.gf_step) S.E a.toProof u.toProof).2 hj.2.1
    rw [toProof_on_goldfish_vote_checked] at h1 h2
    obtain ⟨x, y, e⟩ := StoreSteps.on_goldfish_vote_checked_writes (Setup.toSpec S).P a u
    refine ⟨h1, h2, ?_⟩
    rw [e]
    exact hj.2.2
  | attest row =>
    have h1 := (priv% Proofs.Vocabulary.Protocol.Handlers.JustificationCarrier
      DecoupledConsensusModel.Proofs.NamedJustificationCarrier.row_justifier) S.hc a.toProofNamed
      row.toProofNamed hj.1
    have h2 := ((priv% Proofs.Vocabulary.Protocol.Handlers.NumericStore
      DecoupledConsensusModel.Proofs.NamedNumericStore.row_step) S.hc a.toProofNamed
      row.toProofNamed).2 hj.2.1
    have h3 := Proofs.NamedStoreRoots.invariant_admit_row S.E S.hc S.cfg a.toProofNamed
      row.toProofNamed hj.2.2
    rw [toProof_admit_row S.E S.hc S.cfg] at h1 h2 h3
    exact ⟨h1, h2, h3⟩
  | block B =>
    rcases SubtypeEqualities.on_block_cases_of_ok _ _ hd with e | hroot
    · rw [e]
      exact hj
    · have h1 := (priv% Proofs.Vocabulary.Protocol.Handlers.JustificationCarrier
        DecoupledConsensusModel.Proofs.NamedJustificationCarrier.block_justifier) S a.toProofNamed
        B.toProofNamed hj.2.2.1 hj.1
      have h2 := ((priv% Proofs.Vocabulary.Protocol.Handlers.NumericStore
        DecoupledConsensusModel.Proofs.NamedNumericStore.block_step) S a.toProofNamed
        B.toProofNamed).2 hj.2.1
      have h3 := Proofs.NamedStoreRoots.invariant_on_block_with .alsoCarried S.E S.hc S.cfg
        a.toProofNamed B.toProofNamed hj.2.2
      rw [← image_on_block_step S h.1 h.2.1 B hroot] at h1 h2 h3
      exact ⟨h1, h2, h3⟩

/-- The initial store satisfies `OwnRunsInv`. -/
theorem ownRunsInv_init (S : Setup V) (v : V) :
    OwnRunsInv S (Spec.Store.init : Spec.Store V) := by
  have h1 := (priv% Proofs.Vocabulary.Protocol.Handlers.JustificationCarrier
    DecoupledConsensusModel.Proofs.NamedJustificationCarrier.initial_core_justifier) (V := V)
  have h2 := (priv% Proofs.Vocabulary.Protocol.Handlers.NumericStore
    DecoupledConsensusModel.Proofs.NamedNumericStore.initial_bound) v
  rw [show (NamedWorld.init v : NamedNodeState V).st = Protocol.NamedStore.initial from
    Proofs.ModelProperties.initial_st] at h2
  have h3 := Proofs.NamedStoreRoots.invariant_initial S.E S.cfg (V := V)
  rw [toProof_ns_initial] at h1 h2 h3
  exact ⟨h1, h2, h3⟩

/-- At `Model.spec`, `OwnRunsInv` holds at every validator of every world the events `es` lead
    to from the initial world. -/
theorem ownRunsInv_fold (S : Setup V) (es : List (Record.Event V)) (v₀ : V) :
    ∀ w ∈ es.foldlM (worldStepOf (Model.spec (V := V)) S)
        (fun u => (Model.spec (V := V)).initial S u),
      ∀ v, OwnRunsInv S (w v).val.st :=
  inv_fold S (OwnRunsInv S) (ownRunsInv_step S) (ownRunsInv_init S v₀) es

/-- From `OwnRunsInv`, some held named block derives the store's justified block and justified
    height. -/
theorem justification_of_inv (S : Setup V) (n : (Model.spec (V := V)).N)
    (h : OwnRunsInv S n.val.st) :
    ∃ D : NamedBlock V, D ∈ n.st.bodies ∧
      ((Model.spec (V := V)).derive_named S.E S.cfg D).J = n.st.core.J ∧
      ((Model.spec (V := V)).derive_named S.E S.cfg D).h_j = n.st.core.h_j := by
  obtain ⟨D, hD, hJ, hh⟩ := (priv% Proofs.Vocabulary.Protocol.Handlers.JustificationCarrier
    DecoupledConsensusModel.Proofs.NamedJustificationCarrier.named_justifier) S
    n.val.st.toProofNamed h.2.2.1 h.1
  refine ⟨D, hD, ?_, ?_⟩
  · show (Member.derive_named S.E S.cfg D).toProof.J = _
    rw [image_derive_named]
    exact hJ
  · show (Member.derive_named S.E S.cfg D).toProof.h_j = _
    rw [image_derive_named]
    exact hh

/-- From `OwnRunsInv`, every held named block's derived height is at most the store's `h_max`. -/
theorem heights_of_inv (S : Setup V) (n : (Model.spec (V := V)).N)
    (h : OwnRunsInv S n.val.st) :
    ∀ D ∈ n.st.bodies,
      ((Model.spec (V := V)).derive_named S.E S.cfg D).h ≤ n.st.core.h_max := by
  intro D hD
  have hb := (priv% Proofs.Vocabulary.Protocol.Handlers.NumericStore
    DecoupledConsensusModel.Proofs.NamedNumericStore.named_bound) S n.val.st.toProofNamed
    h.2.2.1 h.2.1 D hD
  show (Member.derive_named S.E S.cfg D).toProof.h ≤ _
  rw [image_derive_named]
  exact hb

/-- From `OwnRunsInv`, for every held named block, the height the store records at its erasure is
    its derived height. -/
theorem derivedView_h_of_inv (S : Setup V) (n : (Model.spec (V := V)).N)
    (h : OwnRunsInv S n.val.st) :
    ∀ D ∈ n.st.bodies,
      (n.st.core.σ D.erase).h = ((Model.spec (V := V)).derive_named S.E S.cfg D).h := by
  intro D hD
  have he := h.2.2.1.2.2.2.2 D hD
  show _ = (Member.derive_named S.E S.cfg D).toProof.h
  rw [image_derive_named, ← he]
  rfl

/-- At `Model.spec`, for every world `w` the run `rho` can reach before its `i`-th event, some
    body `C` that validator `v` holds in `w` has `v`'s store's justified block and justified height
    as its own. -/
theorem spec_justification_carrier_stateBefore_ownRuns : ∀ (S : Setup V)
    (rho : Record.Run V) (i : Nat) (v : V),
    ∀ w ∈ stateBeforeOf (Model.spec (V := V)) S rho i,
    ∃ C : NamedBlock V, C ∈ (w v).st.bodies ∧
      ((Model.spec (V := V)).derive_named S.E S.cfg C).J = (w v).st.core.J ∧
      ((Model.spec (V := V)).derive_named S.E S.cfg C).h_j = (w v).st.core.h_j := by
  intro S rho i v w hw
  exact justification_of_inv S (w v) (ownRunsInv_fold S (rho.events.take i) v w hw v)

/-- At `Model.spec`, for every world `w` the events of `rho` timed before `t` lead to from the
    initial world, some body `D` that validator `v` holds in `w` has `v`'s store's justified block
    and justified height as its own. -/
theorem spec_storeJustificationOnChain_stateBeforeTime_ownRuns : ∀ (S : Setup V)
    (rho : Record.Run V) (t : Time) (v : V),
    ∀ w ∈ (rho.events.filter (fun e => decide (e.time < t))).foldlM
        (worldStepOf (Model.spec (V := V)) S) (fun u => (Model.spec (V := V)).initial S u),
    ∃ D ∈ (w v).st.bodies,
      ((Model.spec (V := V)).derive_named S.E S.cfg D).J = (w v).st.core.J ∧
      ((Model.spec (V := V)).derive_named S.E S.cfg D).h_j = (w v).st.core.h_j := by
  intro S rho t v w hw
  obtain ⟨D, hD, hJ, hh⟩ := justification_of_inv S (w v) (ownRunsInv_fold S _ v w hw v)
  exact ⟨D, hD, hJ, hh⟩

/-- At `Model.spec`, for every world `w` the run `rho` can reach before its `i`-th event, every
    body validator `v` holds in `w` has a height at most `v`'s store's `h_max`. -/
theorem spec_heights_le_hMax_stateBefore_ownRuns : ∀ (S : Setup V) (rho : Record.Run V)
    (i : Nat) (v : V),
    ∀ w ∈ stateBeforeOf (Model.spec (V := V)) S rho i,
    ∀ D ∈ (w v).st.bodies,
      ((Model.spec (V := V)).derive_named S.E S.cfg D).h ≤ (w v).st.core.h_max := by
  intro S rho i v w hw
  exact heights_of_inv S (w v) (ownRunsInv_fold S (rho.events.take i) v w hw v)

/-- At `Model.spec`, for every world `w` the run `rho` can reach before its `i`-th event and
    every body `D` validator `v` holds in `w`, the height `v`'s store records for `D`'s erasure is
    the height of `D`'s chain state. -/
theorem spec_derivedView_stateBefore_h_ownRuns : ∀ (S : Setup V) (rho : Record.Run V)
    (i : Nat) (v : V),
    ∀ w ∈ stateBeforeOf (Model.spec (V := V)) S rho i,
    ∀ D ∈ (w v).st.bodies,
      ((w v).st.core.σ D.erase).h = ((Model.spec (V := V)).derive_named S.E S.cfg D).h := by
  intro S rho i v w hw
  exact derivedView_h_of_inv S (w v) (ownRunsInv_fold S (rho.events.take i) v w hw v)

end SpecRecord.ChainStateRunFacts

namespace DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-- `Model.spec` satisfies `ChainStateRunFacts`. -/
theorem Model.spec_runFacts_cs : ChainStateRunFacts (Model.spec (V := V)) where
  storeFinalizationOnChain_stateBefore := fun S rho i v w hw =>
    SpecRecord.HandlersRunFacts.spec_finalization_carrier_stateBefore S rho i v w hw
  storeFinalizationOnChain_stateBeforeTime := fun S rho t v w hw =>
    SpecRecord.HandlersRunFacts.spec_finalization_carrier_stateBeforeTime S rho t v w hw
  justification_carrier_stateBefore :=
    SpecRecord.ChainStateRunFacts.spec_justification_carrier_stateBefore_ownRuns
  storeJustificationOnChain_stateBeforeTime :=
    SpecRecord.ChainStateRunFacts.spec_storeJustificationOnChain_stateBeforeTime_ownRuns
  noHighJustifications_stateBeforeTime :=
    SpecRecord.HandlersRunFacts.spec_noHighJustifications_stateBeforeTime
  heights_le_hMax_stateBefore :=
    SpecRecord.ChainStateRunFacts.spec_heights_le_hMax_stateBefore_ownRuns
  derivedView_stateBefore_h :=
    SpecRecord.ChainStateRunFacts.spec_derivedView_stateBefore_h_ownRuns
  action_witness := SpecRecord.ChainStateRunFacts.spec_action_witness
  derivedStateAgrees_actionStoreAtOn :=
    SpecRecord.ChainStateRunFacts.spec_derivedStateAgrees_actionStoreAtOn
  action_named_checkpointOn := SpecRecord.ChainStateRunFacts.spec_action_named_checkpointOn
  honestHeightRow_confirmationWitnessOn :=
    SpecRecord.ChainStateRunFacts.spec_honestHeightRow_confirmationWitnessOn
  storeF_preceq_checkpoint_of_windowOn :=
    SpecRecord.ChainStateRunFacts.spec_storeF_preceq_checkpoint_of_windowOn

end DecoupledConsensusModel.Sts.Record
