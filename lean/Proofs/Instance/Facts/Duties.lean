import Proofs.Instance.Model
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Instance.Equalities.ContractImages
import Proofs.Instance.Facts.Handlers
import Proofs.Instance.Facts.Node

/-!
# The duties facts at `Model.specDraft`

The fields of `DutiesFacts` proved at `Model.specDraft`, one theorem `specDraft_<field>` per field,
by equating each member the fields read with the corresponding `Protocol` routine; and the bundle
`Model.specDraft_runFacts_duties` of `DutiesRunFacts`, which has no field.
-/

set_option autoImplicit false

namespace SpecDraftRecord.DutiesFacts

open DecoupledConsensusModel DecoupledConsensusModel.Execution DecoupledConsensusModel.Sts
open DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-- At `Model.specDraft`, `proposalRows` is `Protocol.NamedProposalRows.proposalRows`. -/
theorem proposalRows_eq (P : NamedBlock V) (rows : List (NamedAttestation V)) :
    (Model.specDraft (V := V)).proposalRows P rows =
      Protocol.NamedProposalRows.proposalRows P rows := by
  have h := toProof_proposalRows (Spec.Block.toSpecNamed P)
    (rows.map Spec.Attestation.toSpecNamed)
  simp only [List.map_map, Spec.Block.toProofNamed_toSpecNamed] at h
  rw [show (Spec.Attestation.toProofNamed ∘ Spec.Attestation.toSpecNamed :
      NamedAttestation V → NamedAttestation V) = id from
    funext Spec.Attestation.toProofNamed_toSpecNamed, List.map_id] at h
  rw [h]
  rfl

/-- At `Model.specDraft`, `chainRows` is `Protocol.NamedProposalRows.chainRows`. -/
theorem chainRows_eq (P : NamedBlock V) :
    (Model.specDraft (V := V)).chainRows P = Protocol.NamedProposalRows.chainRows P := by
  have h := toProof_chainRows (Spec.Block.toSpecNamed P)
  rw [Spec.Block.toProofNamed_toSpecNamed] at h
  rw [h]
  rfl

/-- At `Model.specDraftBase`, `processedRows` on the store `st` is
    `Protocol.NamedProposalRows.processedRows` on `st.toProofNamed`. -/
theorem processedRows_eq (hc : Protocol.HealConfig) (st : Spec.Store V) :
    (Model.specDraftBase (V := V)).processedRows hc st =
      Protocol.NamedProposalRows.processedRows hc st.toProofNamed := by
  rw [toProof_processedRows Member.unreadEnvForDuties hc unreadHeightConfig st]
  rfl

/-- At `Model.specDraftBase`, `poolRows` on the store `st` is `Protocol.NamedProposalRows.poolRows`
    on `st.toProofNamed`. -/
theorem poolRows_eq (hc : Protocol.HealConfig) (st : Spec.Store V) :
    (Model.specDraftBase (V := V)).poolRows hc st =
      Protocol.NamedProposalRows.poolRows hc st.toProofNamed := by
  rw [toProof_poolRows Member.unreadEnvForDuties hc unreadHeightConfig st]
  rfl

/-- At `Model.specDraft`, every attestation a proposal on `parent` includes from `rows` is one of
    `rows`, and is not already included on the chain of `parent`. -/
theorem specDraft_mem_proposalRows : ∀ (parent : DecoupledConsensusModel.NamedBlock V) (rows : List (DecoupledConsensusModel.NamedAttestation V)), ∀ row ∈ (Model.specDraft (V := V)).proposalRows parent rows, row ∈ rows ∧ row ∉ (Model.specDraft (V := V)).chainRows parent := by
  intro parent rows
  rw [proposalRows_eq, chainRows_eq]
  exact (Model.vocabulary_facts_duties (V := V)).mem_proposalRows parent rows

/-- At `Model.specDraft`, an attestation of `rows` not on the chain of `parent`, and the only one of
    `rows` by its validator for its round, is included in a proposal on `parent`. -/
theorem specDraft_mem_proposalRows_of_unique : ∀ (parent : DecoupledConsensusModel.NamedBlock V) (rows : List (DecoupledConsensusModel.NamedAttestation V)), ∀ row ∈ rows, row ∉ (Model.specDraft (V := V)).chainRows parent → (∀ b ∈ rows, b.val_index = row.val_index → b.round = row.round → b = row) → row ∈ (Model.specDraft (V := V)).proposalRows parent rows := by
  intro parent rows
  rw [proposalRows_eq, chainRows_eq]
  exact (Model.vocabulary_facts_duties (V := V)).mem_proposalRows_of_unique parent rows

/-- At `Model.specDraftBase`, a full attestation of `st` in the admission window is among the full
    attestations of `st` of every round up to the store's round. -/
theorem specDraftBase_mem_processedRows_of_mem_poolRows : ∀ (hc : DecoupledConsensusModel.Protocol.HealConfig) (st : (Model.specDraftBase (V := V)).NS) {a : DecoupledConsensusModel.NamedAttestation V}, a ∈ (Model.specDraftBase (V := V)).poolRows hc st → a ∈ (Model.specDraftBase (V := V)).processedRows hc st := by
  intro hc st a
  rw [poolRows_eq, processedRows_eq]
  exact (Model.vocabulary_facts_duties (V := V)).mem_processedRows_of_mem_poolRows hc st.toProofNamed

/-- At `Model.specDraft`, a full attestation of `st` in the admission window is among the full
    attestations of `st` of every round up to the store's round. -/
theorem specDraft_mem_processedRows_of_mem_poolRows : ∀ (hc : DecoupledConsensusModel.Protocol.HealConfig) (st : (Model.specDraft (V := V)).NS) {a : DecoupledConsensusModel.NamedAttestation V}, a ∈ (Model.specDraft (V := V)).poolRows hc st → a ∈ (Model.specDraft (V := V)).processedRows hc st :=
  fun hc st {a} => specDraftBase_mem_processedRows_of_mem_poolRows hc st.val (a := a)

/-- At `Model.specDraftBase`, round `r` is in the admission window of `st` exactly when it is at
    least the store's round minus `η_SG` and at most the store's round. -/
theorem specDraftBase_inWindow_eq_true_iff : ∀ (hc : Protocol.HealConfig) (st : (Model.specDraftBase (V := V)).S) (r : Round), (Model.specDraftBase (V := V)).inWindow hc st r = true ↔
    ((Model.specDraftBase (V := V)).round_of hc st.s) - hc.η_SG ≤ r ∧ r ≤ ((Model.specDraftBase (V := V)).round_of hc st.s) := by
  intro hc st r
  have h := (Model.vocabulary_facts_duties (V := V)).inWindow_eq_true_iff hc st.toProof r
  simp only [Model.vocabulary, Model.S.s, Protocol.HealConfig.round_of] at h
  simp only [Model.specDraftBase, Model.S.s, Member.round_of, Member.store_s]
  rw [Member.inWindow, ← toProof_inWindow]
  exact h

/-- At `Model.specDraft`, round `r` is in the admission window of `st` exactly when it is at least
    the store's round minus `η_SG` and at most the store's round. -/
theorem specDraft_inWindow_eq_true_iff : ∀ (hc : Protocol.HealConfig) (st : (Model.specDraft (V := V)).S) (r : Round), (Model.specDraft (V := V)).inWindow hc st r = true ↔
    ((Model.specDraft (V := V)).round_of hc st.s) - hc.η_SG ≤ r ∧ r ≤ ((Model.specDraft (V := V)).round_of hc st.s) :=
  fun hc st r => specDraftBase_inWindow_eq_true_iff hc st.val r

/-- At `Model.specDraftBase`, a full attestation `processedRows` lists for `st` is among the full
    attestations `st` holds for some round. -/
theorem specDraftBase_exists_sg_rows_of_mem_processedRows : ∀ (hc : Protocol.HealConfig) (st : (Model.specDraftBase (V := V)).NS) {a : NamedAttestation V} (h : a ∈ (Model.specDraftBase (V := V)).processedRows hc st), ∃ k : Round, a ∈ st.sg_rows k := by
  intro hc st a hmem
  rw [processedRows_eq] at hmem
  exact (Model.vocabulary_facts_duties (V := V)).exists_sg_rows_of_mem_processedRows hc
    st.toProofNamed hmem

/-- At `Model.specDraft`, a full attestation `processedRows` lists for `st` is among the full
    attestations `st` holds for some round. -/
theorem specDraft_exists_sg_rows_of_mem_processedRows : ∀ (hc : Protocol.HealConfig) (st : (Model.specDraft (V := V)).NS) {a : NamedAttestation V} (h : a ∈ (Model.specDraft (V := V)).processedRows hc st), ∃ k : Round, a ∈ st.sg_rows k :=
  fun hc st {a} h => specDraftBase_exists_sg_rows_of_mem_processedRows hc st.val (a := a) h

/-- At `Model.specDraftBase`, round `r` is in the admission window of `st` exactly when it is at
    least the store's round minus `η_SG` and at most the store's round. -/
theorem specDraftBase_inWindow_iff : ∀ (hc : Protocol.HealConfig) (st : (Model.specDraftBase (V := V)).S) (r : Round), (Model.specDraftBase (V := V)).inWindow hc st r = true ↔
    ((Model.specDraftBase (V := V)).round_of hc st.s) - hc.η_SG ≤ r ∧ r ≤ ((Model.specDraftBase (V := V)).round_of hc st.s) := by
  intro hc st r
  have h := (Model.vocabulary_facts_duties (V := V)).inWindow_iff hc st.toProof r
  simp only [Model.vocabulary, Model.S.s, Protocol.HealConfig.round_of] at h
  simp only [Model.specDraftBase, Model.S.s, Member.round_of, Member.store_s]
  rw [Member.inWindow, ← toProof_inWindow]
  exact h

/-- At `Model.specDraft`, round `r` is in the admission window of `st` exactly when it is at least
    the store's round minus `η_SG` and at most the store's round. -/
theorem specDraft_inWindow_iff : ∀ (hc : Protocol.HealConfig) (st : (Model.specDraft (V := V)).S) (r : Round), (Model.specDraft (V := V)).inWindow hc st r = true ↔
    ((Model.specDraft (V := V)).round_of hc st.s) - hc.η_SG ≤ r ∧ r ≤ ((Model.specDraft (V := V)).round_of hc st.s) :=
  fun hc st r => specDraftBase_inWindow_iff hc st.val r

/-- At `Model.specDraft`, the attestation `a` is among the chain rows of the named block `B` exactly
    when it is among the attestations of `B`'s named chain. -/
theorem specDraft_chainRows_iff_named_chain : ∀ (B : NamedBlock V) (a : NamedAttestation V),
    a ∈ (Model.specDraft (V := V)).chainRows B ↔ a ∈ Protocol.named_chain_attestations B := by
  intro B a
  rw [chainRows_eq]
  exact (Model.vocabulary_facts_duties (V := V)).chainRows_iff_named_chain B a

/-- The root of the proposal input `Protocol.proposal_input` builds is `X.new_root v` at the input's
    slot. -/
theorem proposal_input_root {C : Spec.Config} {X : Spec.External V} {v : V}
    {st : Spec.Store V} {i : Spec.Protocol.ProposalInput V}
    (h : Spec.Protocol.proposal_input C X v st = .ok i) :
    i.root = X.new_root v i.slot := by
  unfold Spec.Protocol.proposal_input at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h; rfl

/-- At `Model.specDraft`, the proposal input of a node carries the node's root of new blocks of its
    slot. -/
theorem specDraft_with_proposal_input_id_root : ∀ (contract : (Model.specDraft (V := V)).Contract)
    (E : DecoupledConsensusModel.Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig)
    (nd : DecoupledConsensusModel.Protocol.Node V) (st : (Model.specDraft (V := V)).HS)
    (P : Protocol.ProposalInput V)
    (hP : (Model.specDraft (V := V)).with_proposal_input contract E hc nd st id ⇢ P),
    P.root = nd.new_root P.slot := by
  intro contract E hc nd st P hP
  have h := (returns_successOutcomes _ _).1 hP
  revert h
  cases hi : Spec.Protocol.proposal_input
      (Spec.Config.toSpec E hc unreadHeightConfig) (Member.externalOfNode nd)
      nd.val_index { Spec.Store.ofImage st.val with saved_grades := fill (Spec.Protocol.advance_to_round
        (st.val.contractOfImage contract)
        ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.val.s)) } with
  | error e => intro h; cases h
  | ok i =>
    intro h
    cases h
    have e := proposal_input_root hi
    simp only [id, Spec.Protocol.ProposalInput.toProof_root,
      Spec.Protocol.ProposalInput.toProof_slot, e, Member.externalOfNode,
      Spec.BlockId.toProof_toSpec]

end SpecDraftRecord.DutiesFacts

namespace SpecDraftRecord.DutiesFacts

/-! ## The confirmation duty -/

open DecoupledConsensusModel DecoupledConsensusModel.Sts DecoupledConsensusModel.Sts.Record
open SpecDraftRecord.ContractImages
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-- At `Model.specDraft`, the finalized block of every outcome `st'` of the confirmation update is
    the finalized block of `st`. -/
theorem specDraft_update_confirmation_with_F :
    ∀ (contract : (Model.specDraft (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (st : (Model.specDraft (V := V)).S) (s : Slot) (st' : (Model.specDraft (V := V)).S), (Model.specDraft (V := V)).update_confirmation_with contract E hc st s ⇢ st' → st'.F = st.F := by
  intro contract E hc st s st' h
  obtain ⟨x1, x2, x3, he⟩ :=
    update_confirmation_with_shape ((returns_preimageOutcomes _ _ _).1 h)
  obtain ⟨v, hv⟩ := st'
  dsimp only at he
  subst he
  exact Spec.Store.toProof_blockOfImage _ _

/-- At `Model.specDraft`, the block tree of every outcome `st'` of the confirmation update is the
    block tree of `st`. -/
theorem specDraft_update_confirmation_with_T :
    ∀ (contract : (Model.specDraft (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (st : (Model.specDraft (V := V)).S) (s : Slot) (st' : (Model.specDraft (V := V)).S), (Model.specDraft (V := V)).update_confirmation_with contract E hc st s ⇢ st' → st'.T = st.T := by
  intro contract E hc st s st' h
  obtain ⟨x1, x2, x3, he⟩ :=
    update_confirmation_with_shape ((returns_preimageOutcomes _ _ _).1 h)
  obtain ⟨v, hv⟩ := st'
  dsimp only at he
  subst he
  rfl

/-- At `Model.specDraft`, for every outcome `st'` of the confirmation update and every slot, the
    Goldfish votes of that slot that `st'` has processed are those of `st`. -/
theorem specDraft_update_confirmation_with_pool :
    ∀ (contract : (Model.specDraft (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (st : (Model.specDraft (V := V)).S) (s : Slot) (st' : (Model.specDraft (V := V)).S), (Model.specDraft (V := V)).update_confirmation_with contract E hc st s ⇢ st' → ((Model.specDraft (V := V)).store_pool st') = ((Model.specDraft (V := V)).store_pool st) := by
  intro contract E hc st s st' h
  obtain ⟨x1, x2, x3, he⟩ :=
    update_confirmation_with_shape ((returns_preimageOutcomes _ _ _).1 h)
  obtain ⟨v, hv⟩ := st'
  dsimp only at he
  subst he
  rfl

/-- At `Model.specDraft`, the slot of every outcome `st'` of the confirmation update is the slot of
    `st`. -/
theorem specDraft_update_confirmation_with_s :
    ∀ (contract : (Model.specDraft (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (st : (Model.specDraft (V := V)).S) (s : Slot) (st' : (Model.specDraft (V := V)).S), (Model.specDraft (V := V)).update_confirmation_with contract E hc st s ⇢ st' → st'.s = st.s := by
  intro contract E hc st s st' h
  obtain ⟨x1, x2, x3, he⟩ :=
    update_confirmation_with_shape ((returns_preimageOutcomes _ _ _).1 h)
  obtain ⟨v, hv⟩ := st'
  dsimp only at he
  subst he
  rfl

/-- At `Model.specDraft`, every outcome `st'` of the confirmation update has the clock `t` of `st`. -/
theorem specDraft_update_confirmation_with_t :
    ∀ (contract : (Model.specDraft (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (st : (Model.specDraft (V := V)).S) (s : Slot) (st' : (Model.specDraft (V := V)).S), (Model.specDraft (V := V)).update_confirmation_with contract E hc st s ⇢ st' → st'.t = st.t := by
  intro contract E hc st s st' h
  obtain ⟨x1, x2, x3, he⟩ :=
    update_confirmation_with_shape ((returns_preimageOutcomes _ _ _).1 h)
  obtain ⟨v, hv⟩ := st'
  dsimp only at he
  subst he
  rfl

/-- At `Model.specDraft`, the Goldfish vote buckets of every outcome `st'` of the confirmation
    update are those of `st`. -/
theorem specDraft_update_confirmation_with_gf_votes :
    ∀ (contract : (Model.specDraft (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (st : (Model.specDraft (V := V)).S) (s : Slot) (st' : (Model.specDraft (V := V)).S), (Model.specDraft (V := V)).update_confirmation_with contract E hc st s ⇢ st' → st'.gf_votes = st.gf_votes := by
  intro contract E hc st s st' h
  obtain ⟨x1, x2, x3, he⟩ :=
    update_confirmation_with_shape ((returns_preimageOutcomes _ _ _).1 h)
  obtain ⟨v, hv⟩ := st'
  dsimp only at he
  subst he
  rfl

/-- At `Model.specDraft`, the stamps every outcome `st'` of the confirmation update gives Goldfish
    votes are those `st` gives them. -/
theorem specDraft_update_confirmation_with_timestamp_vote :
    ∀ (contract : (Model.specDraft (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (st : (Model.specDraft (V := V)).S) (s : Slot) (st' : (Model.specDraft (V := V)).S), (Model.specDraft (V := V)).update_confirmation_with contract E hc st s ⇢ st' → st'.timestamp_vote = st.timestamp_vote := by
  intro contract E hc st s st' h
  obtain ⟨x1, x2, x3, he⟩ :=
    update_confirmation_with_shape ((returns_preimageOutcomes _ _ _).1 h)
  obtain ⟨v, hv⟩ := st'
  dsimp only at he
  subst he
  rfl

/-- At `Model.specDraft`, every outcome `st'` of the confirmation update has the justified block `J`
    of `st`. -/
theorem specDraft_update_confirmation_with_toHealing_J :
    ∀ (contract : (Model.specDraft (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (st : (Model.specDraft (V := V)).S) (s : Slot) (st' : (Model.specDraft (V := V)).S), (Model.specDraft (V := V)).update_confirmation_with contract E hc st s ⇢ st' → ((Model.specDraft (V := V)).toHealing st').toFG.J = ((Model.specDraft (V := V)).toHealing st).toFG.J := by
  intro contract E hc st s st' h
  obtain ⟨x1, x2, x3, he⟩ :=
    update_confirmation_with_shape ((returns_preimageOutcomes _ _ _).1 h)
  obtain ⟨v, hv⟩ := st'
  dsimp only at he
  subst he
  exact Spec.Store.toProof_blockOfImage _ _

/-- At `Model.specDraft`, every outcome `st'` of the confirmation update has the justified height
    `h_j` of `st`. -/
theorem specDraft_update_confirmation_with_toHealing_h_j :
    ∀ (contract : (Model.specDraft (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (st : (Model.specDraft (V := V)).S) (s : Slot) (st' : (Model.specDraft (V := V)).S), (Model.specDraft (V := V)).update_confirmation_with contract E hc st s ⇢ st' → ((Model.specDraft (V := V)).toHealing st').toFG.h_j
    = ((Model.specDraft (V := V)).toHealing st).toFG.h_j := by
  intro contract E hc st s st' h
  obtain ⟨x1, x2, x3, he⟩ :=
    update_confirmation_with_shape ((returns_preimageOutcomes _ _ _).1 h)
  obtain ⟨v, hv⟩ := st'
  dsimp only at he
  subst he
  rfl

/-- At `Model.specDraft`, every outcome `st'` of the confirmation update has the height maximum
    `h_max` of `st`. -/
theorem specDraft_update_confirmation_with_toHealing_h_max :
    ∀ (contract : (Model.specDraft (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (st : (Model.specDraft (V := V)).S) (s : Slot) (st' : (Model.specDraft (V := V)).S), (Model.specDraft (V := V)).update_confirmation_with contract E hc st s ⇢ st' → ((Model.specDraft (V := V)).toHealing st').toFG.h_max
    = ((Model.specDraft (V := V)).toHealing st).toFG.h_max := by
  intro contract E hc st s st' h
  obtain ⟨x1, x2, x3, he⟩ :=
    update_confirmation_with_shape ((returns_preimageOutcomes _ _ _).1 h)
  obtain ⟨v, hv⟩ := st'
  dsimp only at he
  subst he
  rfl

/-- At `Model.specDraft`, every outcome `st'` of the confirmation update has the slot of `st`. -/
theorem specDraft_update_confirmation_with_toHealing_s :
    ∀ (contract : (Model.specDraft (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (st : (Model.specDraft (V := V)).S) (s : Slot) (st' : (Model.specDraft (V := V)).S), (Model.specDraft (V := V)).update_confirmation_with contract E hc st s ⇢ st' → ((Model.specDraft (V := V)).toHealing st').toFG.toSG.toGoldfishStore.s = ((Model.specDraft (V := V)).toHealing st).toFG.toSG.toGoldfishStore.s := by
  intro contract E hc st s st' h
  obtain ⟨x1, x2, x3, he⟩ :=
    update_confirmation_with_shape ((returns_preimageOutcomes _ _ _).1 h)
  obtain ⟨v, hv⟩ := st'
  dsimp only at he
  subst he
  simp only [Model.GS.s, Model.specDraft, Member.gs_s, Member.toHealing, Member.toFG, Member.toSG,
    Member.toGoldfishStore, Model.HS.toFG, Model.FGS.toSG, Model.SGS.toGoldfishStore, id_eq,
    toProof_gs_s, Spec.Store.toProof_s]
  rfl

/-- At `Model.specDraft`, the FG root of the healing view of every outcome `st'` of the confirmation
    update is that of `st`. -/
theorem specDraft_update_confirmation_with_toHealing_fg_root :
    ∀ (contract : (Model.specDraft (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (st : (Model.specDraft (V := V)).S) (s : Slot) (st' : (Model.specDraft (V := V)).S), (Model.specDraft (V := V)).update_confirmation_with contract E hc st s ⇢ st' → (Model.specDraft (V := V)).get_fg_root ((Model.specDraft (V := V)).toHealing st').toFG =
    (Model.specDraft (V := V)).get_fg_root ((Model.specDraft (V := V)).toHealing st).toFG := by
  intro contract E hc st s st' h
  obtain ⟨x1, x2, x3, he⟩ :=
    update_confirmation_with_shape ((returns_preimageOutcomes _ _ _).1 h)
  obtain ⟨v, hv⟩ := st'
  dsimp only at he
  subst he
  show (Spec.Protocol.get_fg_root (Spec.Store.ofImage
      { Spec.Store.ofImage st.val with live_confirmed := x1, latest_stable := x2, latest_confirmed := x3, saved_grades := contract })).toProof =
    (Spec.Protocol.get_fg_root (Spec.Store.ofImage st.val)).toProof
  congr 1
  apply ForkChoiceImages.get_fg_root_congr <;> simp [Spec.Store.ofImage_F, Spec.Store.ofImage_J, Spec.Store.blockOfImage]

/-- At `Model.specDraft`, the filtered tree of the healing view of every outcome `st'` of the
    confirmation update is that of `st`. -/
theorem specDraft_update_confirmation_with_toHealing_filtered :
    ∀ (contract : (Model.specDraft (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (st : (Model.specDraft (V := V)).S) (s : Slot) (st' : (Model.specDraft (V := V)).S), (Model.specDraft (V := V)).update_confirmation_with contract E hc st s ⇢ st' → (Model.specDraft (V := V)).get_filtered_block_tree
    ((Model.specDraft (V := V)).toHealing st').toFG =
    (Model.specDraft (V := V)).get_filtered_block_tree ((Model.specDraft (V := V)).toHealing st).toFG := by
  intro contract E hc st s st' h
  obtain ⟨x1, x2, x3, he⟩ :=
    update_confirmation_with_shape ((returns_preimageOutcomes _ _ _).1 h)
  obtain ⟨v, hv⟩ := st'
  dsimp only at he
  subst he
  show (Spec.Protocol.get_filtered_block_tree (Spec.Store.ofImage
      { Spec.Store.ofImage st.val with live_confirmed := x1, latest_stable := x2, latest_confirmed := x3, saved_grades := contract })).image
      Spec.Block.toProof =
    (Spec.Protocol.get_filtered_block_tree (Spec.Store.ofImage st.val)).image
      Spec.Block.toProof
  congr 1
  apply ForkChoiceImages.get_filtered_block_tree_congr <;> simp [Spec.Store.ofImage_F, Spec.Store.ofImage_J, Spec.Store.blockOfImage]

/-- At `Model.specDraft`, the bodies of every outcome `D` of the confirmation duty are the bodies of
    `st`. -/
theorem specDraft_named_update_confirmation_with_bodies :
    ∀ (contract : (Model.specDraft (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (st : (Model.specDraft (V := V)).NS) (s : Slot)
    (D : (Model.specDraft (V := V)).NS) (hD : (Model.specDraft (V := V)).duties_update_confirmation_with contract E hc st s ⇢ D), D.bodies = st.bodies := by
  intro contract E hc st s st' h
  obtain ⟨x1, x2, x3, he⟩ :=
    update_confirmation_with_shape ((returns_preimageOutcomes _ _ _).1 h)
  obtain ⟨v, hv⟩ := st'
  dsimp only at he
  subst he
  rfl

/-- At `Model.specDraft`, the bodies of every outcome `D` of the named confirmation duty on the
    named store `st` are the bodies of `st`. -/
theorem specDraft_namedDuties_update_confirmation_with_bodies :
    ∀ (contract : (Model.specDraft (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (st : (Model.specDraft (V := V)).NS) (s : Slot)
    (D : (Model.specDraft (V := V)).NS) (hD : (Model.specDraft (V := V)).duties_update_confirmation_with contract E hc st s ⇢ D), D.bodies = st.bodies := by
  intro contract E hc st s st' h
  obtain ⟨x1, x2, x3, he⟩ :=
    update_confirmation_with_shape ((returns_preimageOutcomes _ _ _).1 h)
  obtain ⟨v, hv⟩ := st'
  dsimp only at he
  subst he
  rfl

/-- At `Model.specDraft`, every outcome `D` of the confirmation duty at `st` for the slot `s` has
    the bodies and the SG rows of `st`. -/
theorem specDraft_confirmation_metadata :
    ∀ (gc : (Model.specDraft (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (st : (Model.specDraft (V := V)).NS) (s : Slot)
    (D : (Model.specDraft (V := V)).NS) (hD : (Model.specDraft (V := V)).duties_update_confirmation_with gc E hc st s ⇢ D),
    D.bodies = st.bodies ∧ D.sg_rows = st.sg_rows := by
  intro gc E hc st s D hD
  obtain ⟨x1, x2, x3, he⟩ :=
    update_confirmation_with_shape ((returns_preimageOutcomes _ _ _).1 hD)
  obtain ⟨v, hv⟩ := D
  dsimp only at he
  subst he
  exact ⟨rfl, rfl⟩

/-- At `Model.specDraft`, every outcome `D` of the confirmation duty at `st` for the slot `s` has
    the time `t` and the current slot of `st`'s core store. -/
theorem specDraft_named_confirmation_clock :
    ∀ (gc : (Model.specDraft (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (st : (Model.specDraft (V := V)).NS) (s : Slot)
    (D : (Model.specDraft (V := V)).NS) (hD : (Model.specDraft (V := V)).duties_update_confirmation_with gc E hc st s ⇢ D),
    D.core.t = st.core.t ∧ D.core.s = st.core.s := by
  intro gc E hc st s D hD
  obtain ⟨x1, x2, x3, he⟩ :=
    update_confirmation_with_shape ((returns_preimageOutcomes _ _ _).1 hD)
  obtain ⟨v, hv⟩ := D
  dsimp only at he
  subst he
  exact ⟨rfl, rfl⟩

/-- At `Model.specDraft`, for every outcome `D` of the named confirmation duty and every outcome `X`
    of the confirmation update of `st`'s core store, with the same contract, environment,
    configuration and slot, the core store of `D` is `X`. -/
theorem specDraft_named_update_confirmation_with_core :
    ∀ (contract : (Model.specDraft (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (st : (Model.specDraft (V := V)).NS) (s : Slot)
    (D : (Model.specDraft (V := V)).NS) (hD : (Model.specDraft (V := V)).duties_update_confirmation_with contract E hc st s ⇢ D)
    (X : (Model.specDraft (V := V)).S) (hX : (Model.specDraft (V := V)).update_confirmation_with contract E hc st.core s ⇢ X), D.core = X := by
  intro contract E hc st s D hD X hX
  have h1 := (returns_successOutcomes _ _).1 ((returns_preimageOutcomes _ _ _).1 hD)
  have h2 := (returns_successOutcomes _ _).1 ((returns_preimageOutcomes _ _ _).1 hX)
  exact Subtype.ext (Except.ok.inj (h1.symm.trans h2))

/-- At `Model.specDraft`, for every outcome `D` of the named confirmation update and every outcome
    `X` of the confirmation update of the core, the core of `D` is `X`. -/
theorem specDraft_namedDuties_update_confirmation_with_core :
    ∀ (contract : (Model.specDraft (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (st : (Model.specDraft (V := V)).NS) (s : Slot)
    (D : (Model.specDraft (V := V)).NS) (hD : (Model.specDraft (V := V)).duties_update_confirmation_with contract E hc st s ⇢ D)
    (X : (Model.specDraft (V := V)).S) (hX : (Model.specDraft (V := V)).update_confirmation_with contract E hc st.core s ⇢ X), D.core = X := by
  intro contract E hc st s D hD X hX
  have h1 := (returns_successOutcomes _ _).1 ((returns_preimageOutcomes _ _ _).1 hD)
  have h2 := (returns_successOutcomes _ _).1 ((returns_preimageOutcomes _ _ _).1 hX)
  exact Subtype.ext (Except.ok.inj (h1.symm.trans h2))

/-- At `Model.specDraft`, if `D` is an outcome of the confirmation duty of slot `s` run on `st` with
    the grade contract of the cache `c`, then `D` with `c` written into it is also an outcome of
    that duty. -/
theorem specDraft_duties_update_confirmation_with_store_with_cache_outcome :
    ∀ (c : (Model.specDraft (V := V)).Cache) (E : Env V)
    (hc : Protocol.HealConfig) (st : (Model.specDraft (V := V)).NS) (s : Slot) (D : (Model.specDraft (V := V)).NS),
    (Model.specDraft (V := V)).duties_update_confirmation_with ((Model.specDraft (V := V)).gradeContract c) E hc st s ⇢ D →
    (Model.specDraft (V := V)).duties_update_confirmation_with ((Model.specDraft (V := V)).gradeContract c) E hc st s ⇢ (Model.specDraft (V := V)).store_with_cache D c := by
  intro c E hc st s D hD
  obtain ⟨x1, x2, x3, he⟩ :=
    update_confirmation_with_shape ((returns_preimageOutcomes _ _ _).1 hD)
  obtain ⟨v, hv⟩ := D
  dsimp only at he
  subst he
  exact hD

end SpecDraftRecord.DutiesFacts

namespace SpecDraftRecord.DutiesFacts

/-! ## The proposal and the Goldfish vote duty -/

open DecoupledConsensusModel DecoupledConsensusModel.Sts DecoupledConsensusModel.Sts.Record
open SpecDraftRecord.ContractImages
open DecoupledConsensusModel.Protocol (HealConfig HeightConfig)
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-- At `Model.specDraft`, the attestation duty run with `gc` on `st` with the cache `c` written into
    it has the same outcomes as the attestation duty run with `gc` on `st`. -/
theorem specDraft_duties_attest_with_store_with_cache :
    ∀ (gc : (Model.specDraft (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig)
    (nd : Protocol.Node V) (st : (Model.specDraft (V := V)).NS) (c : (Model.specDraft (V := V)).Cache) (record : (Model.specDraft (V := V)).NR),
    (Model.specDraft (V := V)).duties_attest_with gc E hc nd ((Model.specDraft (V := V)).store_with_cache st c) record =
      (Model.specDraft (V := V)).duties_attest_with gc E hc nd st record := by
  intros
  rfl

/-- At `Model.specDraft`, the Goldfish vote duty run with `gc` on `st` with the cache `c` written
    into it has the same outcomes as the Goldfish vote duty run with `gc` on `st`. -/
theorem specDraft_duties_goldfish_vote_with_store_with_cache :
    ∀ (gc : (Model.specDraft (V := V)).Contract) (E : Env V)
    (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : (Model.specDraft (V := V)).NS) (c : (Model.specDraft (V := V)).Cache),
    (Model.specDraft (V := V)).duties_goldfish_vote_with gc E hc nd ((Model.specDraft (V := V)).store_with_cache st c) =
      (Model.specDraft (V := V)).duties_goldfish_vote_with gc E hc nd st := by
  intros
  rfl

/-- At `Model.specDraft`, the proposal run with `gc` on `st` with the cache `c` written into it has
    the same outcomes as the proposal run with `gc` on `st`. -/
theorem specDraft_proposal_with_store_with_cache :
    ∀ (gc : (Model.specDraft (V := V)).Contract) (src : Protocol.ProposalRowSource)
    (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : (Model.specDraft (V := V)).NS) (c : (Model.specDraft (V := V)).Cache),
    (Model.specDraft (V := V)).proposal_with gc src E hc nd ((Model.specDraft (V := V)).store_with_cache st c) = (Model.specDraft (V := V)).proposal_with gc src E hc nd st := by
  intros
  rfl

/-- At `Model.specDraft`, for every outcome `D` of the named Goldfish vote duty and every outcome
    `G` of the Goldfish vote duty on the named store's core store, the core store of `D`'s named
    store is `G`'s store. -/
theorem specDraft_namedDuties_goldfish_vote_with_fst_core :
    ∀ (contract : (Model.specDraft (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : (Model.specDraft (V := V)).NS)
    (D : (Model.specDraft (V := V)).NS × Option (GoldfishVote V)) (hD : (Model.specDraft (V := V)).duties_goldfish_vote_with contract E hc nd st ⇢ D)
    (G : (Model.specDraft (V := V)).S × Option (GoldfishVote V)) (hG : (Model.specDraft (V := V)).goldfish_vote_with contract E hc nd st.core ⇢ G),
    D.1.core = G.1 := by
  intro contract E hc nd st D hD G hG
  obtain ⟨o1, e1, f1⟩ := except_map_eq_ok
    ((returns_successOutcomes _ _).1 ((returns_preimageOutcomes _ _ _).1 hD))
  obtain ⟨o2, e2, f2⟩ := except_map_eq_ok
    ((returns_successOutcomes _ _).1 ((returns_preimageOutcomes _ _ _).1 hG))
  have e : o1 = o2 := Except.ok.inj (e1.symm.trans e2)
  subst e
  exact Subtype.ext ((congrArg Prod.fst f1).symm.trans (congrArg Prod.fst f2))

/-- At `Model.specDraft`, for every outcome `D` of the named Goldfish vote duty on the named store
    `st` and every outcome `G` of the Goldfish vote duty on the core store of `st`, the vote, if
    any, of `D` is the vote of `G`. -/
theorem specDraft_namedDuties_goldfish_vote_with_snd :
    ∀ (contract : (Model.specDraft (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : (Model.specDraft (V := V)).NS)
    (D : (Model.specDraft (V := V)).NS × Option (GoldfishVote V)) (hD : (Model.specDraft (V := V)).duties_goldfish_vote_with contract E hc nd st ⇢ D)
    (G : (Model.specDraft (V := V)).S × Option (GoldfishVote V)) (hG : (Model.specDraft (V := V)).goldfish_vote_with contract E hc nd st.core ⇢ G),
    D.2 = G.2 := by
  intro contract E hc nd st D hD G hG
  obtain ⟨o1, e1, f1⟩ := except_map_eq_ok
    ((returns_successOutcomes _ _).1 ((returns_preimageOutcomes _ _ _).1 hD))
  obtain ⟨o2, e2, f2⟩ := except_map_eq_ok
    ((returns_successOutcomes _ _).1 ((returns_preimageOutcomes _ _ _).1 hG))
  have e : o1 = o2 := Except.ok.inj (e1.symm.trans e2)
  subst e
  have h1 := congrArg Prod.snd f1
  have h2 := congrArg Prod.snd f2
  simp only [Prod.map_snd, id_eq] at h1 h2
  rw [← h1, ← h2, firstSentGoldfishVote_map]

/-- At `Model.specDraft`, the proposer of every outcome `P` of the proposal input built at `st` for
    the node `nd` is `nd`'s validator. -/
theorem specDraft_with_proposal_input_id_proposer :
    ∀ (contract : (Model.specDraft (V := V)).Contract) (E : DecoupledConsensusModel.Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig) (nd : DecoupledConsensusModel.Protocol.Node V) (st : (Model.specDraft (V := V)).HS)
    (P : Protocol.ProposalInput V) (hP : (Model.specDraft (V := V)).with_proposal_input contract E hc nd st id ⇢ P),
    P.proposer = nd.val_index := by
  intro contract E hc nd st P hP
  obtain ⟨i, hi, rfl⟩ := except_map_eq_ok ((returns_successOutcomes _ _).1 hP)
  obtain ⟨H, sv, hsv, hH, rfl⟩ := proposal_input_shape hi
  rfl

/-- At `Model.specDraft`, the slot of every outcome `P` of the proposal input built at `st` is
    `st`'s slot. -/
theorem specDraft_with_proposal_input_id_slot :
    ∀ (contract : (Model.specDraft (V := V)).Contract) (E : DecoupledConsensusModel.Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig) (nd : DecoupledConsensusModel.Protocol.Node V) (st : (Model.specDraft (V := V)).HS)
    (P : Protocol.ProposalInput V) (hP : (Model.specDraft (V := V)).with_proposal_input contract E hc nd st id ⇢ P),
    P.slot = st.toFG.toSG.toGoldfishStore.s := by
  intro contract E hc nd st P hP
  obtain ⟨i, hi, rfl⟩ := except_map_eq_ok ((returns_successOutcomes _ _).1 hP)
  obtain ⟨H, sv, hsv, hH, rfl⟩ := proposal_input_shape hi
  simp only [Model.GS.s, Model.S.s, Model.specDraft, Member.gs_s, Member.store_s, Member.toHealing,
    Member.toFG, Member.toSG, Member.toGoldfishStore, Model.HS.toFG, Model.FGS.toSG,
    Model.SGS.toGoldfishStore, id_eq, toProof_gs_s, Spec.Store.toProof_s]
  rfl

/-- At `Model.specDraft`, the Goldfish votes of every outcome `P` of the proposal input built at
    `st` are the proposer's view of `st`'s Goldfish votes at `st`'s slot. -/
theorem specDraft_with_proposal_input_id_gf_votes :
    ∀ (contract : (Model.specDraft (V := V)).Contract) (E : DecoupledConsensusModel.Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig) (nd : DecoupledConsensusModel.Protocol.Node V) (st : (Model.specDraft (V := V)).HS)
    (P : Protocol.ProposalInput V) (hP : (Model.specDraft (V := V)).with_proposal_input contract E hc nd st id ⇢ P),
    P.gf_votes = (Model.specDraft (V := V)).proposer_view st.toFG.toSG.toGoldfishStore st.toFG.toSG.toGoldfishStore.s := by
  intro contract E hc nd st P hP
  obtain ⟨i, hi, rfl⟩ := except_map_eq_ok ((returns_successOutcomes _ _).1 hP)
  obtain ⟨H, sv, hsv, hH, rfl⟩ := proposal_input_shape hi
  simp only [Model.GS.s, Model.S.s, Model.specDraft, Member.gs_s, Member.store_s, Member.toHealing,
    Member.toFG, Member.toSG, Member.toGoldfishStore, Model.HS.toFG, Model.FGS.toSG,
    Model.SGS.toGoldfishStore, id_eq, toProof_gs_s, Spec.Store.toProof_s]
  rfl

/-- At `Model.specDraft`, for every outcome `P` of the proposal input built at `st` and every
    outcome `L` of the proposer's view of `st`'s support votes at `st`'s slot, the support votes of
    `P` are `L`. -/
theorem specDraft_with_proposal_input_id_gf_support_votes :
    ∀ (contract : (Model.specDraft (V := V)).Contract) (E : DecoupledConsensusModel.Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig) (nd : DecoupledConsensusModel.Protocol.Node V) (st : (Model.specDraft (V := V)).HS)
    (P : Protocol.ProposalInput V) (hP : (Model.specDraft (V := V)).with_proposal_input contract E hc nd st id ⇢ P)
    (L : List (GoldfishVote V)) (hL : (Model.specDraft (V := V)).proposer_support_view st.toFG.toSG.toGoldfishStore st.toFG.toSG.toGoldfishStore.s ⇢ L),
    P.gf_support_votes = L := by
  intro contract E hc nd st P hP L hL
  obtain ⟨i, hi, rfl⟩ := except_map_eq_ok ((returns_successOutcomes _ _).1 hP)
  obtain ⟨H, sv, hsv, hH, rfl⟩ := proposal_input_shape hi
  simp only [Model.GS.s, Model.S.s, Model.specDraft, Member.gs_s, Member.store_s, Member.toHealing,
    Member.toFG, Member.toSG, Member.toGoldfishStore, Model.HS.toFG, Model.FGS.toSG,
    Model.SGS.toGoldfishStore, id_eq, toProof_gs_s, Spec.Store.toProof_s] at hL
  obtain ⟨sv', e', rfl⟩ := except_map_eq_ok ((returns_successOutcomes _ _).1 hL)
  have e : sv = sv' := Except.ok.inj (hsv.symm.trans e')
  subst e
  rfl

/-- At `Model.specDraft`, if an outcome `o` of the proposal under `contract` is the block `B` at
    `st`, then the slot of `B` is the slot of `st`'s core store. -/
theorem specDraft_ModelProperties_proposal_with_slot :
    ∀ (contract : (Model.specDraft (V := V)).Contract) (source : Protocol.ProposalRowSource) (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : (Model.specDraft (V := V)).NS) (B : NamedBlock V)
    (o : Option (NamedBlock V)) (ho : (Model.specDraft (V := V)).proposal_with contract source E hc nd st ⇢ o) (h : o = some B), B.slot = st.core.s := by
  intro contract source E hc nd st B o ho h
  subst h
  obtain ⟨B', hB', e⟩ := except_map_eq_ok ((returns_successOutcomes _ _).1 ho)
  obtain ⟨i, rows, hi, hrows, rfl⟩ := build_proposal_shape hB'
  obtain ⟨H, sv, hsv, hH, rfl⟩ := proposal_input_shape hi
  cases e
  simp only [Spec.Block.toProofNamed, DecoupledConsensusModel.NamedBlock.slot, DecoupledConsensusModel.NamedBlock.gf_votes, Model.GS.s, Model.S.s, Model.specDraft, Member.gs_s, Member.store_s, Member.toHealing,
    Member.toFG, Member.toSG, Member.toGoldfishStore, Model.HS.toFG, Model.FGS.toSG,
    Model.SGS.toGoldfishStore, id_eq, toProof_gs_s, Spec.Store.toProof_s]
  rfl

/-- At `Model.specDraft`, if an outcome `o` of the proposal under `contract`, with the row source
    `source`, is the block `B` at `st`, then the slot of `B` is the current slot of `st`'s core
    store. -/
theorem specDraft_Optimistic_proposal_with_slot :
    ∀ (contract : (Model.specDraft (V := V)).Contract) (source : Protocol.ProposalRowSource) (E : Env V) (hc : HealConfig) (nd : Protocol.Node V) (st : (Model.specDraft (V := V)).NS) {B : NamedBlock V}
    (o : Option (NamedBlock V)) (ho : (Model.specDraft (V := V)).proposal_with contract source E hc nd st ⇢ o) (hB : o = some B), B.slot = st.core.s := by
  intro contract source E hc nd st B o ho h
  subst h
  obtain ⟨B', hB', e⟩ := except_map_eq_ok ((returns_successOutcomes _ _).1 ho)
  obtain ⟨i, rows, hi, hrows, rfl⟩ := build_proposal_shape hB'
  obtain ⟨H, sv, hsv, hH, rfl⟩ := proposal_input_shape hi
  cases e
  simp only [Spec.Block.toProofNamed, DecoupledConsensusModel.NamedBlock.slot, DecoupledConsensusModel.NamedBlock.gf_votes, Model.GS.s, Model.S.s, Model.specDraft, Member.gs_s, Member.store_s, Member.toHealing,
    Member.toFG, Member.toSG, Member.toGoldfishStore, Model.HS.toFG, Model.FGS.toSG,
    Model.SGS.toGoldfishStore, id_eq, toProof_gs_s, Spec.Store.toProof_s]
  rfl

/-- At `Model.specDraft`, if an outcome `o` of the proposal under `contract`, with the row source
    `source`, is the block `B` at `st`, then the Goldfish votes of `B` are the Goldfish votes of the
    slot before `st`'s current slot that `st`'s core store has processed. -/
theorem specDraft_proposal_with_gf_votes :
    ∀ (contract : (Model.specDraft (V := V)).Contract) (source : Protocol.ProposalRowSource) (E : Env V) (hc : HealConfig) (nd : Protocol.Node V) (st : (Model.specDraft (V := V)).NS) {B : NamedBlock V}
    (o : Option (NamedBlock V)) (ho : (Model.specDraft (V := V)).proposal_with contract source E hc nd st ⇢ o) (hB : o = some B), B.gf_votes = st.core.gf_votes (st.core.s - 1) := by
  intro contract source E hc nd st B o ho h
  subst h
  obtain ⟨B', hB', e⟩ := except_map_eq_ok ((returns_successOutcomes _ _).1 ho)
  obtain ⟨i, rows, hi, hrows, rfl⟩ := build_proposal_shape hB'
  obtain ⟨H, sv, hsv, hH, rfl⟩ := proposal_input_shape hi
  cases e
  simp only [Spec.Block.toProofNamed, DecoupledConsensusModel.NamedBlock.slot, DecoupledConsensusModel.NamedBlock.gf_votes, Model.GS.s, Model.S.s, Model.specDraft, Member.gs_s, Member.store_s, Member.toHealing,
    Member.toFG, Member.toSG, Member.toGoldfishStore, Model.HS.toFG, Model.FGS.toSG,
    Model.SGS.toGoldfishStore, id_eq, toProof_gs_s, Spec.Store.toProof_s]
  rfl

/-- At `Model.specDraft`, if an outcome `o` of the proposal under `contract`, with the row source
    `source`, is the block `B` at the named store `st`, then every support vote included in `B` is
    among the Goldfish votes included in `B`. -/
theorem specDraft_proposal_with_gf_support_subset :
    ∀ (contract : (Model.specDraft (V := V)).Contract) (source : Protocol.ProposalRowSource) (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : (Model.specDraft (V := V)).NS) {B : NamedBlock V}
    (o : Option (NamedBlock V)) (ho : (Model.specDraft (V := V)).proposal_with contract source E hc nd st ⇢ o) (h : o = some B),
    ∀ u ∈ B.gf_support_votes, u ∈ B.gf_votes := by
  intro contract source E hc nd st B o ho h
  subst h
  obtain ⟨B', hB', e⟩ := except_map_eq_ok ((returns_successOutcomes _ _).1 ho)
  obtain ⟨i, rows, hi, hrows, rfl⟩ := build_proposal_shape hB'
  obtain ⟨H, sv, hsv, hH, rfl⟩ := proposal_input_shape hi
  cases e
  intro u hu
  simp only [Spec.Block.toProofNamed, DecoupledConsensusModel.NamedBlock.gf_support_votes,
    DecoupledConsensusModel.NamedBlock.gf_votes, List.mem_map] at hu ⊢
  obtain ⟨w, hw, rfl⟩ := hu
  exact ⟨w, list_filterM_subset _ _ _ hsv w hw, rfl⟩

/-- At `Model.specDraft`, every support vote included in the block `B` an outcome `o` of the
    proposal names is one of the Goldfish votes included in `B`. -/
theorem specDraft_proposal_with_support_subset :
    ∀ (contract : (Model.specDraft (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : (Model.specDraft (V := V)).NS) {B : NamedBlock V}
    (o : Option (NamedBlock V)) (ho : (Model.specDraft (V := V)).proposal_with contract .poolAndCarried E hc nd st ⇢ o) (hB : o = some B),
    ∀ u ∈ B.gf_support_votes, u ∈ B.gf_votes := by
  intro contract E hc nd st B o ho h
  subst h
  obtain ⟨B', hB', e⟩ := except_map_eq_ok ((returns_successOutcomes _ _).1 ho)
  obtain ⟨i, rows, hi, hrows, rfl⟩ := build_proposal_shape hB'
  obtain ⟨H, sv, hsv, hH, rfl⟩ := proposal_input_shape hi
  cases e
  intro u hu
  simp only [Spec.Block.toProofNamed, DecoupledConsensusModel.NamedBlock.gf_support_votes,
    DecoupledConsensusModel.NamedBlock.gf_votes, List.mem_map] at hu ⊢
  obtain ⟨w, hw, rfl⟩ := hu
  exact ⟨w, list_filterM_subset _ _ _ hsv w hw, rfl⟩

/-- At `Model.specDraft`, if the named store `st` satisfies the named-store root invariant at `E`
    and `cfg`, every outcome `o` of the proposal run with the grade contract of the cache `c`, the
    row source `source`, `E`, `hc` and the node `nd` on `st` is some named block. -/
theorem specDraft_proposal_with_gradeContract_isSome :
    ∀ (c : (Model.specDraft (V := V)).Cache) (source : DecoupledConsensusModel.Protocol.ProposalRowSource) (E : DecoupledConsensusModel.Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig) (cfg : DecoupledConsensusModel.Protocol.HeightConfig) (nd : DecoupledConsensusModel.Protocol.Node V) (st : (Model.specDraft (V := V)).NS), DecoupledConsensusModel.Sts.Restated.Vocabulary.Proofs.NamedStoreRoots.Invariant (Model.specDraft (V := V)) E cfg st → ∀ o : Option (NamedBlock V), (Model.specDraft (V := V)).proposal_with ((Model.specDraft (V := V)).gradeContract c) source E hc nd st ⇢ o → ∃ B, o = Option.some B := by
  intro c source E hc cfg nd st _ o ho
  obtain ⟨B', -, rfl⟩ := except_map_eq_ok ((returns_successOutcomes _ _).1 ho)
  exact ⟨_, rfl⟩

/-- At `Model.specDraft`, if an outcome `o` of the proposal under `gc`, with the row source
    `.poolAndCarried`, is no block at `st`, then every outcome `D` of the proposal duty is `st` and
    no block. -/
theorem specDraft_propose_none :
    ∀ (gc : (Model.specDraft (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (nd : Protocol.Node V) (st : (Model.specDraft (V := V)).NS)
    (o : Option (NamedBlock V)) (ho : (Model.specDraft (V := V)).proposal_with gc .poolAndCarried E hc nd st ⇢ o) (h : o = none)
    (D : (Model.specDraft (V := V)).NS × Option (NamedBlock V)) (hD : (Model.specDraft (V := V)).duties_propose_block_with gc E hc cfg nd st ⇢ D), D = (st, none) := by
  intro gc E hc cfg nd st o ho h D hD
  obtain ⟨B', -, rfl⟩ := except_map_eq_ok ((returns_successOutcomes _ _).1 ho)
  cases h

/-- At `Model.specDraft`, if an outcome `o` of the proposal the duty would make at `st` is absent,
    the store of every outcome `D` of the duty is `st`. -/
theorem specDraft_propose_block_with_fst_of_none :
    ∀ (contract : (Model.specDraft (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (nd : Protocol.Node V) (st : (Model.specDraft (V := V)).NS)
    (o : Option (NamedBlock V)) (ho : (Model.specDraft (V := V)).proposal_with contract .poolAndCarried E hc nd st ⇢ o) (h : o = none)
    (D : (Model.specDraft (V := V)).NS × Option (NamedBlock V)) (hD : (Model.specDraft (V := V)).duties_propose_block_with contract E hc cfg nd st ⇢ D), D.1 = st := by
  intro gc E hc cfg nd st o ho h D hD
  obtain ⟨B', -, rfl⟩ := except_map_eq_ok ((returns_successOutcomes _ _).1 ho)
  cases h

/-- At `Model.specDraft`, if an outcome `o` of the proposal under `contract` is the block `B` at
    `st`, then for every outcome `input` of the proposal input built at `st`'s healing view, `B` has
    a named parent `p`, and `p` erases to the parent of `input`. -/
theorem specDraft_proposal_with_parent? :
    ∀ (contract : (Model.specDraft (V := V)).Contract) (source : DecoupledConsensusModel.Protocol.ProposalRowSource) (E : DecoupledConsensusModel.Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig) (nd : DecoupledConsensusModel.Protocol.Node V) (st : (Model.specDraft (V := V)).NS) (B : DecoupledConsensusModel.NamedBlock V) (o : Option (DecoupledConsensusModel.NamedBlock V)), (Model.specDraft (V := V)).proposal_with contract source E hc nd st ⇢ o → o = Option.some B → ∀ input : Protocol.ProposalInput V, (Model.specDraft (V := V)).with_proposal_input contract E hc nd ((Model.specDraft (V := V)).toHealing st.core) id ⇢ input → ∃ p, B.parent? = Option.some p ∧ p.erase = input.parent := by
  intro contract source E hc nd st B o ho h input hinput
  subst h
  obtain ⟨B', hB', e⟩ := except_map_eq_ok ((returns_successOutcomes _ _).1 ho)
  obtain ⟨i, rows, hi, hrows, rfl⟩ := build_proposal_shape hB'
  obtain ⟨i', hi', rfl⟩ := except_map_eq_ok ((returns_successOutcomes _ _).1 hinput)
  have e' : i = i' := Except.ok.inj (hi.symm.trans hi')
  subst e'
  cases e
  exact ⟨_, rfl, Spec.Block.toProofNamed_erase _⟩

end SpecDraftRecord.DutiesFacts

namespace SpecDraftRecord.DutiesFacts

/-! ## The attestation duty -/

open DecoupledConsensusModel DecoupledConsensusModel.Sts DecoupledConsensusModel.Sts.Record
open SpecDraftRecord.ContractImages
open DecoupledConsensusModel.Protocol (HealConfig HeightConfig)
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-- At `Model.specDraft`, the validator of the row of every outcome `A` of the named round action at
    the store `st` is the validator of the node `nd`. -/
theorem specDraft_round_action_with_val_index :
    ∀ (contract : (Model.specDraft (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : (Model.specDraft (V := V)).HS) (record : (Model.specDraft (V := V)).NR)
    (A : (Model.specDraft (V := V)).NR × NamedAttestation V) (hA : (Model.specDraft (V := V)).round_action_with contract E hc nd st record ⇢ A),
    A.2.val_index = nd.val_index := by
  intro contract E hc nd st record A hA
  obtain ⟨p, hp, rfl⟩ := round_action_with_shape hA
  obtain ⟨i, -, hv, -, rfl⟩ := build_attestation_shape hp
  rw [← hv]
  rfl

/-- At `Model.specDraft`, the round of the row of every outcome `A` of the named round action at the
    store `st` is the round of `st`'s slot. -/
theorem specDraft_round_action_with_round :
    ∀ (contract : (Model.specDraft (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : (Model.specDraft (V := V)).HS) (record : (Model.specDraft (V := V)).NR)
    (A : (Model.specDraft (V := V)).NR × NamedAttestation V) (hA : (Model.specDraft (V := V)).round_action_with contract E hc nd st record ⇢ A),
    A.2.round = ((Model.specDraft (V := V)).round_of hc st.toFG.toSG.toGoldfishStore.s) := by
  intro contract E hc nd st record A hA
  obtain ⟨p, hp, rfl⟩ := round_action_with_shape hA
  obtain ⟨i, -, -, hr, rfl⟩ := build_attestation_shape hp
  simp only [Model.GS.s, Model.S.s, Model.specDraft, Member.gs_s, Member.store_s, Member.toHealing,
    Member.toFG, Member.toSG, Member.toGoldfishStore, Model.HS.toFG, Model.FGS.toSG,
    Model.SGS.toGoldfishStore, id_eq, toProof_gs_s, Spec.Store.toProof_s]
  exact hr

/-- At `Model.specDraft`, the named store of every outcome `D` of the attestation duty at `st` with
    the record `record` has the time `t` and the current slot `s` of `st`'s core store. -/
theorem specDraft_named_attest_clock :
    ∀ (gc : (Model.specDraft (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : (Model.specDraft (V := V)).NS) (record : (Model.specDraft (V := V)).NR)
    (D : (Model.specDraft (V := V)).NS × (Model.specDraft (V := V)).NR × NamedAttestation V) (hD : (Model.specDraft (V := V)).duties_attest_with gc E hc nd st record ⇢ D),
    D.1.core.t = st.core.t ∧ D.1.core.s = st.core.s := by
  intro gc E hc nd st record D hD
  obtain ⟨p, hp, hD'⟩ := duties_attest_with_shape ((returns_preimageOutcomes _ _ _).1 hD)
  have h1 : D.1.val = _ := congrArg (fun x => x.1) hD'
  obtain ⟨ht, hs, hl, hls, hlc⟩ := admit_attestation_frame
    (Spec.Config.toSpec E hc unreadHeightConfig) _ p.2
  refine ⟨?_, ?_⟩
  · show D.1.val.t = st.val.t
    rw [h1]
    exact ht
  · show D.1.val.s = st.val.s
    rw [h1]
    exact hs

/-- At `Model.specDraft`, the store of every outcome `D` of the attestation duty holds the
    `live_confirmed` of the store it was given. -/
theorem specDraft_Sts_attest_with_live_confirmed :
    ∀ (gc : (Model.specDraft (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : (Model.specDraft (V := V)).NS) (record : (Model.specDraft (V := V)).NR)
    (D : (Model.specDraft (V := V)).NS × (Model.specDraft (V := V)).NR × NamedAttestation V) (hD : (Model.specDraft (V := V)).duties_attest_with gc E hc nd st record ⇢ D),
    D.1.core.live_confirmed = st.core.live_confirmed := by
  intro gc E hc nd st record D hD
  obtain ⟨p, hp, hD'⟩ := duties_attest_with_shape ((returns_preimageOutcomes _ _ _).1 hD)
  have h1 : D.1.val = _ := congrArg (fun x => x.1) hD'
  obtain ⟨ht, hs, hl, hls, hlc⟩ := admit_attestation_frame
    (Spec.Config.toSpec E hc unreadHeightConfig) _ p.2
  show Member.store_live_confirmed D.1.val = Member.store_live_confirmed st.val
  rw [h1]
  simp only [Member.store_live_confirmed, Spec.Store.toProof_live_confirmed]
  rw [hl]
  exact Spec.Store.toProof_blockOfImage _ _

/-- At `Model.specDraft`, the store of every outcome `D` of the attestation duty holds the
    `latest_stable` and the `latest_confirmed` of the store it was given. -/
theorem specDraft_attest_with_records :
    ∀ (gc : (Model.specDraft (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : (Model.specDraft (V := V)).NS) (record : (Model.specDraft (V := V)).NR)
    (D : (Model.specDraft (V := V)).NS × (Model.specDraft (V := V)).NR × NamedAttestation V) (hD : (Model.specDraft (V := V)).duties_attest_with gc E hc nd st record ⇢ D),
    D.1.core.latest_stable = st.core.latest_stable ∧
    D.1.core.latest_confirmed = st.core.latest_confirmed := by
  intro gc E hc nd st record D hD
  obtain ⟨p, hp, hD'⟩ := duties_attest_with_shape ((returns_preimageOutcomes _ _ _).1 hD)
  have h1 : D.1.val = _ := congrArg (fun x => x.1) hD'
  obtain ⟨ht, hs, hl, hls, hlc⟩ := admit_attestation_frame
    (Spec.Config.toSpec E hc unreadHeightConfig) _ p.2
  refine ⟨?_, ?_⟩
  · show Member.store_latest_stable D.1.val = Member.store_latest_stable st.val
    rw [h1]
    simp only [Member.store_latest_stable, Spec.Store.toProof_latest_stable]
    rw [hls]
    exact Spec.Store.toProof_blockOfImage _ _
  · show Member.store_latest_confirmed D.1.val = Member.store_latest_confirmed st.val
    rw [h1]
    simp only [Member.store_latest_confirmed, Spec.Store.toProof_latest_confirmed]
    rw [hlc]
    exact Spec.Store.toProof_blockOfImage _ _

/-- At `Model.specDraft`, for every outcome `D` of the attestation duty at `st` with the record
    `record` and every outcome `A` of the named round action at `st`'s healing view with that
    record, the named row of `D` is the row of `A`. -/
theorem specDraft_attest_with_row :
    ∀ (contract : (Model.specDraft (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : (Model.specDraft (V := V)).NS) (record : (Model.specDraft (V := V)).NR)
    (D : (Model.specDraft (V := V)).NS × (Model.specDraft (V := V)).NR × NamedAttestation V) (hD : (Model.specDraft (V := V)).duties_attest_with contract E hc nd st record ⇢ D)
    (A : (Model.specDraft (V := V)).NR × NamedAttestation V) (hA : (Model.specDraft (V := V)).round_action_with contract E hc nd ((Model.specDraft (V := V)).toHealing st.core) record ⇢ A),
    D.2.2 = A.2 := by
  intro contract E hc nd st record D hD A hA
  obtain ⟨p, hp, hD'⟩ := duties_attest_with_shape ((returns_preimageOutcomes _ _ _).1 hD)
  obtain ⟨p', hp', rfl⟩ := round_action_with_shape hA
  have e : p = p' := Except.ok.inj (hp.symm.trans hp')
  subst e
  exact congrArg (fun x => x.2.2) hD'

end SpecDraftRecord.DutiesFacts

namespace SpecDraftRecord.DutiesFacts

/-! ## The proposal duty -/

open DecoupledConsensusModel DecoupledConsensusModel.Sts DecoupledConsensusModel.Sts.Record
open SpecDraftRecord.ContractImages
open DecoupledConsensusModel.Protocol (HealConfig HeightConfig Node)
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-- At `Model.specDraft`, if the block of an outcome `D` of the proposal duty at `st` is `B`, then
    the slot of `B` is the current slot of `st`'s core store. -/
theorem specDraft_propose_block_with_slot :
    ∀ (contract : (Model.specDraft (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (nd : Protocol.Node V) (st : (Model.specDraft (V := V)).NS) {B : NamedBlock V}
    (D : (Model.specDraft (V := V)).NS × Option (NamedBlock V)) (hD : (Model.specDraft (V := V)).duties_propose_block_with contract E hc cfg nd st ⇢ D)
    (hB : D.2 = some B), B.slot = st.core.s := by
  intro contract E hc cfg nd st B D hD hB
  obtain ⟨B', hB', hD'⟩ := duties_propose_block_with_shape ((returns_preimageOutcomes _ _ _).1 hD)
  have h2 : D.2 = some B'.toProofNamed := congrArg (fun x => x.2) hD'
  rw [h2] at hB
  cases hB
  obtain ⟨i, rows, hi, hrows, rfl⟩ := build_proposal_shape hB'
  obtain ⟨H, sv, hsv, hH, rfl⟩ := proposal_input_shape hi
  simp only [Spec.Block.toProofNamed, DecoupledConsensusModel.NamedBlock.slot, DecoupledConsensusModel.NamedBlock.proposer?, Model.GS.s, Model.S.s, Model.specDraft, Member.gs_s, Member.store_s, Member.toHealing,
    Member.toFG, Member.toSG, Member.toGoldfishStore, Model.HS.toFG, Model.FGS.toSG,
    Model.SGS.toGoldfishStore, id_eq, toProof_gs_s, Spec.Store.toProof_s]
  rfl

/-- At `Model.specDraft`, the block `B` of any outcome `D` of a validator's proposal duty carries
    that validator as its proposer. -/
theorem specDraft_proposer_of_propose_block_with :
    ∀ (gc : (Model.specDraft (V := V)).Contract) (E : Env V) (hc : HealConfig) (cfg : HeightConfig) (nd : Node V) (st : (Model.specDraft (V := V)).NS) (B : NamedBlock V)
    (D : (Model.specDraft (V := V)).NS × Option (NamedBlock V)) (hD : (Model.specDraft (V := V)).duties_propose_block_with gc E hc cfg nd st ⇢ D) (h : D.2 = some B),
    B.proposer? = some nd.val_index := by
  intro gc E hc cfg nd st B D hD h
  obtain ⟨B', hB', hD'⟩ := duties_propose_block_with_shape ((returns_preimageOutcomes _ _ _).1 hD)
  have h2 : D.2 = some B'.toProofNamed := congrArg (fun x => x.2) hD'
  rw [h2] at h
  cases h
  obtain ⟨i, rows, hi, hrows, rfl⟩ := build_proposal_shape hB'
  obtain ⟨H, sv, hsv, hH, rfl⟩ := proposal_input_shape hi
  simp only [Spec.Block.toProofNamed, DecoupledConsensusModel.NamedBlock.slot, DecoupledConsensusModel.NamedBlock.proposer?, Model.GS.s, Model.S.s, Model.specDraft, Member.gs_s, Member.store_s, Member.toHealing,
    Member.toFG, Member.toSG, Member.toGoldfishStore, Model.HS.toFG, Model.FGS.toSG,
    Model.SGS.toGoldfishStore, id_eq, toProof_gs_s, Spec.Store.toProof_s]

/-- At `Model.specDraft`, if an outcome `o` of the proposal `proposal_with` would make at `st`, with
    the row source `.poolAndCarried`, is the block `B`, then the block of every outcome `D` of the
    proposal duty at `st` is `B`. -/
theorem specDraft_propose_block_with_snd_of_some :
    ∀ (contract : (Model.specDraft (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (nd : Protocol.Node V) (st : (Model.specDraft (V := V)).NS) {B : NamedBlock V}
    (o : Option (NamedBlock V)) (ho : (Model.specDraft (V := V)).proposal_with contract .poolAndCarried E hc nd st ⇢ o) (h : o = some B)
    (D : (Model.specDraft (V := V)).NS × Option (NamedBlock V)) (hD : (Model.specDraft (V := V)).duties_propose_block_with contract E hc cfg nd st ⇢ D), D.2 = some B := by
  intro contract E hc cfg nd st B o ho h D hD
  subst h
  obtain ⟨B', hB', hD'⟩ := duties_propose_block_with_shape ((returns_preimageOutcomes _ _ _).1 hD)
  have h2 : D.2 = some B'.toProofNamed := congrArg (fun x => x.2) hD'
  obtain ⟨B'', hB'', e⟩ := except_map_eq_ok ((returns_successOutcomes _ _).1 ho)
  have e' : B' = B'' := Except.ok.inj (hB'.symm.trans hB'')
  subst e'
  rw [h2, e]

/-- At `Model.specDraft`, if an outcome `D` of the proposal duty under `contract` at the named store
    `st` proposes the block `B`, then every outcome `o` of `proposal_with`, with the row source
    `.poolAndCarried`, at `st` is `B`. -/
theorem specDraft_proposal_with_eq_of_propose_block_with_snd :
    ∀ (contract : (Model.specDraft (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (nd : Protocol.Node V) (st : (Model.specDraft (V := V)).NS) {B : NamedBlock V}
    (D : (Model.specDraft (V := V)).NS × Option (NamedBlock V)) (hD : (Model.specDraft (V := V)).duties_propose_block_with contract E hc cfg nd st ⇢ D) (h : D.2 = some B)
    (o : Option (NamedBlock V)) (ho : (Model.specDraft (V := V)).proposal_with contract .poolAndCarried E hc nd st ⇢ o), o = some B := by
  intro contract E hc cfg nd st B D hD h o ho
  obtain ⟨B', hB', hD'⟩ := duties_propose_block_with_shape ((returns_preimageOutcomes _ _ _).1 hD)
  have h2 : D.2 = some B'.toProofNamed := congrArg (fun x => x.2) hD'
  obtain ⟨B'', hB'', e⟩ := except_map_eq_ok ((returns_successOutcomes _ _).1 ho)
  have e' : B' = B'' := Except.ok.inj (hB'.symm.trans hB'')
  subst e'
  rw [← e, ← h2, h]

/-- At `Model.specDraft`, if an outcome `D` of the named proposal duty returned the block `B`, then
    every outcome `o` of `proposal_with` at the row source `.poolAndCarried` is `B` too. -/
theorem specDraft_proposal_with_of_propose_block_with :
    ∀ (contract : (Model.specDraft (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (nd : Protocol.Node V) (st : (Model.specDraft (V := V)).NS) {B : NamedBlock V}
    (D : (Model.specDraft (V := V)).NS × Option (NamedBlock V)) (hD : (Model.specDraft (V := V)).duties_propose_block_with contract E hc cfg nd st ⇢ D) (hB : D.2 = some B)
    (o : Option (NamedBlock V)) (ho : (Model.specDraft (V := V)).proposal_with contract .poolAndCarried E hc nd st ⇢ o), o = some B := by
  intro contract E hc cfg nd st B D hD h o ho
  obtain ⟨B', hB', hD'⟩ := duties_propose_block_with_shape ((returns_preimageOutcomes _ _ _).1 hD)
  have h2 : D.2 = some B'.toProofNamed := congrArg (fun x => x.2) hD'
  obtain ⟨B'', hB'', e⟩ := except_map_eq_ok ((returns_successOutcomes _ _).1 ho)
  have e' : B' = B'' := Except.ok.inj (hB'.symm.trans hB'')
  subst e'
  rw [← e, ← h2, h]

/-- At `Model.specDraft`, the named store of every outcome `D` of the proposal duty at `st` has the
    time `t` and the current slot `s` of `st`'s core store. -/
theorem specDraft_named_propose_clock :
    ∀ (gc : (Model.specDraft (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (cfg : HeightConfig) (nd : Protocol.Node V) (st : (Model.specDraft (V := V)).NS)
    (D : (Model.specDraft (V := V)).NS × Option (NamedBlock V)) (hD : (Model.specDraft (V := V)).duties_propose_block_with gc E hc cfg nd st ⇢ D),
    D.1.core.t = st.core.t ∧ D.1.core.s = st.core.s := by
  intro gc E hc cfg nd st D hD
  obtain ⟨B', hB', hD'⟩ := duties_propose_block_with_shape ((returns_preimageOutcomes _ _ _).1 hD)
  have h1 : D.1.val = _ := congrArg (fun x => x.1) hD'
  obtain ⟨ht, hs, -, hF⟩ := HandlersFacts.admitBlockCore_fields
    (Spec.Config.toSpec E hc cfg) (Spec.Provisional.toSpec E) _ B'
  refine ⟨?_, ?_⟩
  · show D.1.val.t = st.val.t
    rw [h1]
    exact (HandlersFacts.on_block_t _ _ _ _).trans ht
  · show D.1.val.s = st.val.s
    rw [h1]
    exact (HandlersFacts.on_block_s _ _ _ _).trans hs

/-- At `Model.specDraft`, the finalized block of `st`'s core store is an ancestor of, or equal to,
    the finalized block of the core store of the named store of every outcome `D` of the proposal
    duty at `st`. -/
theorem specDraft_propose_block_with_F :
    ∀ (gc : (Model.specDraft (V := V)).Contract) (E : Env V) (hc : HealConfig) (cfg : HeightConfig) (nd : Protocol.Node V) (st : (Model.specDraft (V := V)).NS)
    (D : (Model.specDraft (V := V)).NS × Option (NamedBlock V)) (hD : (Model.specDraft (V := V)).duties_propose_block_with gc E hc cfg nd st ⇢ D),
    Block.Preceq st.core.F D.1.core.F := by
  intro gc E hc cfg nd st D hD
  obtain ⟨B', hB', hD'⟩ := duties_propose_block_with_shape ((returns_preimageOutcomes _ _ _).1 hD)
  have h1 : D.1.val = _ := congrArg (fun x => x.1) hD'
  show Block.Preceq (Member.store_F st.val) (Member.store_F D.1.val)
  rw [h1]
  unfold Block.Preceq
  simp only [Member.store_F, Spec.Store.toProof_F]
  refine Spec.Block.toProof_preceq_of_ancestorEq _ _ ?_
  rw [HandlersFacts.on_block_F]
  conv_lhs => rw [← Spec.Store.ofImage_F_of_storeOk st.property]
  exact (HandlersFacts.admitBlockCore_fields (Spec.Config.toSpec E hc cfg)
    (Spec.Provisional.toSpec E)
    { Spec.Store.ofImage st.val with saved_grades := fill (Spec.Protocol.advance_to_round (st.val.contractOfImage gc) ((Spec.Config.toSpec E hc cfg).round_of st.val.s)) }
    B').2.2.2

end SpecDraftRecord.DutiesFacts

namespace SpecDraftRecord.DutiesFacts

/-! ## The Goldfish vote duty's store, and the pool across two duties -/

open DecoupledConsensusModel DecoupledConsensusModel.Sts DecoupledConsensusModel.Sts.Record
open SpecDraftRecord.ContractImages
open DecoupledConsensusModel.Protocol (HealConfig HeightConfig Node)
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-- At `Model.specDraft`, the named store of every outcome `D` of the Goldfish vote duty at `st` has
    the time `t` and the current slot `s` of `st`'s core store. -/
theorem specDraft_named_vote_clock :
    ∀ (gc : (Model.specDraft (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : (Model.specDraft (V := V)).NS)
    (D : (Model.specDraft (V := V)).NS × Option (GoldfishVote V)) (hD : (Model.specDraft (V := V)).duties_goldfish_vote_with gc E hc nd st ⇢ D),
    D.1.core.t = st.core.t ∧ D.1.core.s = st.core.s := by
  intro gc E hc nd st D hD
  obtain ⟨x, y, he⟩ := duties_goldfish_vote_with_shape ((returns_preimageOutcomes _ _ _).1 hD)
  obtain ⟨⟨v, hv⟩, o⟩ := D
  dsimp only [Prod.map] at he
  subst he
  exact ⟨rfl, rfl⟩

/-- At `Model.specDraft`, the named store of every outcome `D` of the Goldfish vote duty at `st` has
    the bodies and the SG rows of `st`. -/
theorem specDraft_goldfish_vote_metadata :
    ∀ (gc : (Model.specDraft (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : (Model.specDraft (V := V)).NS)
    (D : (Model.specDraft (V := V)).NS × Option (GoldfishVote V)) (hD : (Model.specDraft (V := V)).duties_goldfish_vote_with gc E hc nd st ⇢ D),
    D.1.bodies = st.bodies ∧ D.1.sg_rows = st.sg_rows := by
  intro gc E hc nd st D hD
  obtain ⟨x, y, he⟩ := duties_goldfish_vote_with_shape ((returns_preimageOutcomes _ _ _).1 hD)
  obtain ⟨⟨v, hv⟩, o⟩ := D
  dsimp only [Prod.map] at he
  subst he
  exact ⟨rfl, rfl⟩

/-- At `Model.specDraft`, the core store of the named store of every outcome `D` of the Goldfish
    vote duty at `st` has the SG votes `sg_votes` of `st`'s core store. -/
theorem specDraft_goldfish_vote_with_sg_votes :
    ∀ (contract : (Model.specDraft (V := V)).Contract) (E : Env V) (hc : HealConfig) (nd : Protocol.Node V) (st : (Model.specDraft (V := V)).NS)
    (D : (Model.specDraft (V := V)).NS × Option (GoldfishVote V)) (hD : (Model.specDraft (V := V)).duties_goldfish_vote_with contract E hc nd st ⇢ D),
    D.1.core.sg_votes = st.core.sg_votes := by
  intro contract E hc nd st D hD
  obtain ⟨x, y, he⟩ := duties_goldfish_vote_with_shape ((returns_preimageOutcomes _ _ _).1 hD)
  obtain ⟨⟨v, hv⟩, o⟩ := D
  dsimp only [Prod.map] at he
  subst he
  rfl

/-- At `Model.specDraft`, for every outcome `D` of the named Goldfish vote duty on `st`, the
    finalized block of the core store of `D`'s named store is the finalized block of `st`'s core
    store. -/
theorem specDraft_namedDuties_goldfish_vote_with_fst_core_F :
    ∀ (contract : (Model.specDraft (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : (Model.specDraft (V := V)).NS) (D : (Model.specDraft (V := V)).NS × Option (GoldfishVote V)), (Model.specDraft (V := V)).duties_goldfish_vote_with contract E hc nd st ⇢ D → D.1.core.F = st.core.F := by
  intro contract E hc nd st D hD
  obtain ⟨x, y, he⟩ := duties_goldfish_vote_with_shape ((returns_preimageOutcomes _ _ _).1 hD)
  obtain ⟨⟨v, hv⟩, o⟩ := D
  dsimp only [Prod.map] at he
  subst he
  exact Spec.Store.toProof_blockOfImage _ _

/-- At `Model.specDraft`, for every outcome `D` of the confirmation duty for slot `s` on `st`,
    `InsertsAt` at `c` holds from the core store of `st` to the core store of `D`. -/
theorem specDraft_insertsAt_named_confirmation :
    ∀ (E : Env V) (c : Int) (contract : (Model.specDraft (V := V)).Contract)
    (hc : Protocol.HealConfig) (st : (Model.specDraft (V := V)).NS) (s : Slot)
    (D : (Model.specDraft (V := V)).NS), (Model.specDraft (V := V)).duties_update_confirmation_with contract E hc st s ⇢ D →
    Restated.InsertsAt (Model.specDraft (V := V)) E c st.core D.core := by
  intro E c contract hc st s D hD hps hc'
  obtain ⟨x1, x2, x3, he⟩ :=
    update_confirmation_with_shape ((returns_preimageOutcomes _ _ _).1 hD)
  obtain ⟨v, hv⟩ := D
  dsimp only at he
  subst he
  exact ⟨⟨fun _ _ h => h, fun _ _ h => h⟩, ⟨hps.slot, hps.stamped, hps.pooled, hps.bounded⟩, hc', rfl,
    fun _ h1 h2 => absurd h2 h1⟩

/-- At `Model.specDraft`, for every outcome `D` of the attestation duty on `st` with the signing
    record `record`, `InsertsAt` at `c` holds from the core store of `st` to the core store of `D`'s
    named store. -/
theorem specDraft_insertsAt_named_attest :
    ∀ (E : Env V) (c : Int) (contract : (Model.specDraft (V := V)).Contract) (hc : Protocol.HealConfig)
    (nd : Protocol.Node V) (st : (Model.specDraft (V := V)).NS) (record : (Model.specDraft (V := V)).NR)
    (D : (Model.specDraft (V := V)).NS × (Model.specDraft (V := V)).NR × NamedAttestation V), (Model.specDraft (V := V)).duties_attest_with contract E hc nd st record ⇢ D →
    Restated.InsertsAt (Model.specDraft (V := V)) E c st.core D.1.core := by
  intro E c contract hc nd st record D hD hps hc'
  obtain ⟨p, hp, hD'⟩ := duties_attest_with_shape ((returns_preimageOutcomes _ _ _).1 hD)
  obtain ⟨⟨v, hv⟩, nr, a⟩ := D
  have h1 : v = _ := congrArg (fun x => x.1) hD'
  obtain ⟨x, y, hw⟩ := StoreSteps.admit_attestation_writes
    (Spec.Config.toSpec E hc unreadHeightConfig) _ p.2
  rw [hw] at h1
  subst h1
  exact ⟨⟨fun _ _ h => h, fun _ _ h => h⟩, ⟨hps.slot, hps.stamped, hps.pooled, hps.bounded⟩, hc', rfl,
    fun _ h1 h2 => absurd h2 h1⟩

end SpecDraftRecord.DutiesFacts

namespace SpecDraftRecord.DutiesFacts

/-! ## The grade-2 candidate and the finality-gadget source -/

open DecoupledConsensusModel DecoupledConsensusModel.Sts DecoupledConsensusModel.Sts.Record
open SpecDraftRecord.ContractImages
open DecoupledConsensusModel.Protocol (HealConfig HeightConfig Node GradeRead)
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-- At `Model.specDraft`, for every outcome `G` of the contract's grade read at `st` and `r` and
    every outcome `Q` of the grade-2 candidate under `contract` at `st` and `r`, `Q` is the grade-2
    candidate of `G`. -/
theorem specDraft_grade2_block_with_eq_read_Q2 :
    ∀ (contract : (Model.specDraft (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (st : (Model.specDraft (V := V)).HS) (r : Round)
    (G : GradeRead V) (hG : contract.read E hc st r ⇢ G)
    (Q : Option (Block V)) (hQ : (Model.specDraft (V := V)).grade2_block_with contract E hc st r ⇢ Q), Q = G.Q2 := by
  intro contract E hc st r G hG Q hQ
  obtain ⟨Q2, h1, rfl⟩ := grade2_block_with_shape (E := E) (hc := hc) hQ
  obtain ⟨Q2', h2, e⟩ := read_shape (E := E) (hc := hc) hG
  rw [e, Except.ok.inj (h1.symm.trans h2)]

/-- At `Model.specDraft`, if, for an outcome `A2` of the contract's grade-2 candidate for round `r`,
    an outcome `o` of the FG source computed at `A2` is some block `B`, then every outcome `G` of
    the contract's read for round `r` has some grade-2 candidate. -/
theorem specDraft_read_Q2_isSome_of_fg_source_with_grade2 :
    ∀ (contract : (Model.specDraft (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (st : (Model.specDraft (V := V)).HS) (r : Round) {B : Block V}
    (A2 : Option (Block V)) (hA2 : (Model.specDraft (V := V)).grade2_block_with contract E hc st r ⇢ A2)
    (o : Option (Block V)) (ho : (Model.specDraft (V := V)).fg_source_with contract E hc st r A2 ⇢ o) (h : o = some B)
    (G : GradeRead V) (hG : contract.read E hc st r ⇢ G), ∃ A, G.Q2 = some A := by
  intro contract E hc st r B A2 hA2 o ho h G hG
  subst h
  obtain ⟨Q2, h1, rfl⟩ := grade2_block_with_shape (E := E) (hc := hc) hA2
  obtain ⟨Q2', h2, e⟩ := read_shape (E := E) (hc := hc) hG
  rw [e, ← Except.ok.inj (h1.symm.trans h2)]
  rcases fg_source_with_shape (E := E) (hc := hc) ho with ⟨-, e'⟩ | ⟨q, hq, -⟩
  · cases e'
  · exact ⟨q, hq⟩

/-- At `Model.specDraft`, if an outcome `o` of the finality-gadget source is the block `Cfg`, then
    `Cfg` is an ancestor of the store's confirmed block, or it is the grade-2 candidate the caller
    supplied. -/
theorem specDraft_fg_source_cases :
    ∀ (contract : (Model.specDraft (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (st : (Model.specDraft (V := V)).HS) (r₁ : Round) {A_G2 : Option (Block V)} {Cfg : Block V}
    (o : Option (Block V)) (ho : (Model.specDraft (V := V)).fg_source_with contract E hc st r₁ A_G2 ⇢ o) (h : o = some Cfg),
    Block.Preceq Cfg st.toFG.toSG.toGoldfishStore.live_confirmed ∨ A_G2 = some Cfg := by
  intro contract E hc st r₁ A_G2 Cfg o ho h
  subst h
  rcases fg_source_with_shape (E := E) (hc := hc) ho with ⟨-, e'⟩ | ⟨q, rfl, e' | ⟨B, test, hB, e'⟩⟩
  · cases e'
  · cases e'
    exact Or.inr rfl
  · cases e'
    left
    show DecoupledConsensusModel.Block.Preceq B.toProof (Member.gs_live_confirmed st.val)
    rw [Member.gs_live_confirmed, toProof_gs_live_confirmed]
    unfold DecoupledConsensusModel.Block.Preceq
    have h2 := Spec.Block.toProof_preceq_of_ancestorEq _ _ (deepest_clear_between hB).2
    rwa [Spec.Store.ofImage_live_confirmed, Spec.Store.toProof_blockOfImage] at h2

/-- At `Model.specDraft`, if an outcome `o` of the finality-gadget source at the grade-2 candidate
    `A_G2` is `B`, then `A_G2` is some block `q`, and `q` is an ancestor of `B` or `B` itself. -/
theorem specDraft_fg_source_with_some :
    ∀ (contract : (Model.specDraft (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (st : (Model.specDraft (V := V)).HS) (r : Round) {A_G2 : Option (Block V)} {B : Block V}
    (o : Option (Block V)) (ho : (Model.specDraft (V := V)).fg_source_with contract E hc st r A_G2 ⇢ o) (h : o = some B),
    ∃ q : Block V, A_G2 = some q ∧ Block.Preceq q B := by
  intro contract E hc st r A_G2 B o ho h
  subst h
  rcases fg_source_with_shape (E := E) (hc := hc) ho with ⟨-, e'⟩ | ⟨q, rfl, e' | ⟨B', test, hB, e'⟩⟩
  · cases e'
  · cases e'
    refine ⟨B, rfl, ?_⟩
    unfold DecoupledConsensusModel.Block.Preceq
    exact DecoupledConsensusModel.Block.preceq_self _
  · cases e'
    refine ⟨q, rfl, ?_⟩
    have hq := Spec.Block.toProof_preceq_of_ancestorEq _ _ (deepest_clear_between hB).1
    rw [Spec.Store.toProof_blockOfImage] at hq
    unfold DecoupledConsensusModel.Block.Preceq
    exact hq

end SpecDraftRecord.DutiesFacts

namespace SpecDraftRecord.DutiesFacts

/-! ## The confirmed root of the attestation -/

open DecoupledConsensusModel DecoupledConsensusModel.Sts DecoupledConsensusModel.Sts.Record
open SpecDraftRecord.ContractImages
open DecoupledConsensusModel.Protocol (HealConfig HeightConfig Node GradeRead)
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-- At `Model.specDraft`, for every outcome `I` of the attestation input built at `st`, every
    outcome `A2` of the grade-2 block of `st`'s round, and every outcome `W` of the SG vote the
    contract selects at `st`'s round from `A2`, the confirmed root of `I` is the root of `W`. -/
theorem specDraft_with_attestation_input_id_confirmed :
    ∀ (contract : (Model.specDraft (V := V)).Contract) (E : DecoupledConsensusModel.Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig) (nd : DecoupledConsensusModel.Protocol.Node V) (st : (Model.specDraft (V := V)).HS)
    (I : Protocol.AttestationInput V) (hI : (Model.specDraft (V := V)).with_attestation_input contract E hc nd st id ⇢ I)
    (A2 : Option (Block V)) (hA2 : (Model.specDraft (V := V)).grade2_block_with contract E hc st (((Model.specDraft (V := V)).round_of hc st.toFG.toSG.toGoldfishStore.s)) ⇢ A2)
    (W : Block V) (hW : (Model.specDraft (V := V)).get_sg_vote_with contract E hc st (((Model.specDraft (V := V)).round_of hc st.toFG.toSG.toGoldfishStore.s)) A2 ⇢ W),
    I.confirmed = Option.some W.root := by
  intro contract E hc nd st I hI A2 hA2 W hW
  obtain ⟨i, hi, rfl⟩ := except_map_eq_ok ((returns_successOutcomes _ _).1 hI)
  obtain ⟨A_G2, W0, hA, hW0, hconf⟩ := attestation_input_confirmed hi
  obtain ⟨Q2, h1, rfl⟩ := grade2_block_with_shape (E := E) (hc := hc) hA2
  obtain ⟨W', hW', rfl⟩ := get_sg_vote_with_shape (E := E) (hc := hc) hW
  have hr : (Model.specDraft (V := V)).round_of hc st.toFG.toSG.toGoldfishStore.s =
      (Spec.Config.toSpec E hc unreadHeightConfig).round_of st.val.s := by
    simp only [Model.GS.s, Model.specDraft, Member.gs_s, Member.toHealing, Member.toFG, Member.toSG,
      Member.toGoldfishStore, Model.HS.toFG, Model.FGS.toSG, Model.SGS.toGoldfishStore, id_eq,
      toProof_gs_s, Spec.Store.toProof_s, Member.round_of]
    rfl
  rw [hr] at h1 hW'
  unfold Spec.Protocol.grade2_block_with at hA
  have e : Q2 = A_G2 := Except.ok.inj (h1.symm.trans hA)
  subst e
  have hroot := get_sg_vote_with_root_congr (map_toSpec_toProof_root Q2) hW' hW0
  show (Option.map Spec.BlockId.toProof i.confirmed) = some W'.toProof.root
  rw [hconf, Spec.Block.toProof_root, hroot]
  rfl

/-- At `Model.specDraft`, for every outcome `A` of the named round action at the store `st`, every
    outcome `A2` of the contract's grade-2 candidate at the round of `st`'s slot, and every outcome
    `W` of the SG vote the contract selects at `st` and that round with `A2`, the confirmed root of
    `A`'s row is the root of `W`. -/
theorem specDraft_round_action_with_confirmed :
    ∀ (contract : (Model.specDraft (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : (Model.specDraft (V := V)).HS) (record : (Model.specDraft (V := V)).NR)
    (A : (Model.specDraft (V := V)).NR × NamedAttestation V) (hA : (Model.specDraft (V := V)).round_action_with contract E hc nd st record ⇢ A)
    (A2 : Option (Block V)) (hA2 : (Model.specDraft (V := V)).grade2_block_with contract E hc st (((Model.specDraft (V := V)).round_of hc st.toFG.toSG.toGoldfishStore.s)) ⇢ A2)
    (W : Block V) (hW : (Model.specDraft (V := V)).get_sg_vote_with contract E hc st (((Model.specDraft (V := V)).round_of hc st.toFG.toSG.toGoldfishStore.s)) A2 ⇢ W),
    A.2.confirmed = some W.root := by
  intro contract E hc nd st record A hA A2 hA2 W hW
  obtain ⟨p, hp, rfl⟩ := round_action_with_shape hA
  obtain ⟨i, hi, -, -, rfl⟩ := build_attestation_shape hp
  obtain ⟨A_G2, W0, hA, hW0, hconf⟩ := attestation_input_confirmed hi
  obtain ⟨Q2, h1, rfl⟩ := grade2_block_with_shape (E := E) (hc := hc) hA2
  obtain ⟨W', hW', rfl⟩ := get_sg_vote_with_shape (E := E) (hc := hc) hW
  have hr : (Model.specDraft (V := V)).round_of hc st.toFG.toSG.toGoldfishStore.s =
      (Spec.Config.toSpec E hc unreadHeightConfig).round_of st.val.s := by
    simp only [Model.GS.s, Model.specDraft, Member.gs_s, Member.toHealing, Member.toFG, Member.toSG,
      Member.toGoldfishStore, Model.HS.toFG, Model.FGS.toSG, Model.SGS.toGoldfishStore, id_eq,
      toProof_gs_s, Spec.Store.toProof_s, Member.round_of]
    rfl
  rw [hr] at h1 hW'
  unfold Spec.Protocol.grade2_block_with at hA
  have e : Q2 = A_G2 := Except.ok.inj (h1.symm.trans hA)
  subst e
  have hroot := get_sg_vote_with_root_congr (map_toSpec_toProof_root Q2) hW' hW0
  show (Option.map Spec.BlockId.toProof i.confirmed) = some W'.toProof.root
  rw [hconf, Spec.Block.toProof_root, hroot]
  rfl

end SpecDraftRecord.DutiesFacts

namespace SpecDraftRecord.DutiesFacts

/-! ## The proposal input's parent -/

open DecoupledConsensusModel DecoupledConsensusModel.Sts DecoupledConsensusModel.Sts.Record
open SpecDraftRecord.ContractImages
open DecoupledConsensusModel.Protocol (HealConfig HeightConfig Node GradeRead)
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-- At `Model.specDraft`, for every outcome `P` of the proposal input built at `st`, every outcome
    `L` of the proposer's view of `st`'s support votes at `st`'s slot, and every outcome `H` of the
    head under `contract` at `st`, read with the proposer's view of `st`'s Goldfish votes and `L`
    for the slot before `st`'s slot, the parent of `P` is `H`. -/
theorem specDraft_with_proposal_input_id_parent :
    ∀ (contract : (Model.specDraft (V := V)).Contract) (E : DecoupledConsensusModel.Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig) (nd : DecoupledConsensusModel.Protocol.Node V) (st : (Model.specDraft (V := V)).HS)
    (P : Protocol.ProposalInput V) (hP : (Model.specDraft (V := V)).with_proposal_input contract E hc nd st id ⇢ P)
    (L : List (GoldfishVote V)) (hL : (Model.specDraft (V := V)).proposer_support_view st.toFG.toSG.toGoldfishStore st.toFG.toSG.toGoldfishStore.s ⇢ L)
    (H : Block V) (hH : (Model.specDraft (V := V)).get_head_with contract E hc st ((Model.specDraft (V := V)).proposer_view st.toFG.toSG.toGoldfishStore st.toFG.toSG.toGoldfishStore.s).toFinset L.toFinset (st.toFG.toSG.toGoldfishStore.s - 1) ⇢ H),
    P.parent = H := by
  intro contract E hc nd st P hP L hL H hH
  obtain ⟨i, hi, rfl⟩ := except_map_eq_ok ((returns_successOutcomes _ _).1 hP)
  obtain ⟨H', sv, hsv, hH', rfl⟩ := proposal_input_shape hi
  simp only [Model.GS.s, Model.S.s, Model.specDraft, Member.gs_s, Member.store_s, Member.toHealing,
    Member.toFG, Member.toSG, Member.toGoldfishStore, Model.HS.toFG, Model.FGS.toSG,
    Model.SGS.toGoldfishStore, id_eq, toProof_gs_s, Spec.Store.toProof_s] at hL hH
  obtain ⟨sv', e', rfl⟩ := except_map_eq_ok ((returns_successOutcomes _ _).1 hL)
  have e : sv = sv' := Except.ok.inj (hsv.symm.trans e')
  subst e
  have hH2 := (returns_successOutcomes _ _).1 hH
  obtain ⟨H'', hH'', rfl⟩ := except_map_eq_ok hH2
  rw [show (Member.proposer_view st.val st.val.s) =
      (Spec.Protocol.proposer_view st.val st.val.s).map Spec.GoldfishVote.toProof from rfl,
    map_voteToSpec_toFinset, map_voteToSpec_toFinset] at hH''
  have e2 : H' = H'' := Except.ok.inj (hH'.symm.trans hH'')
  subst e2
  rfl

end SpecDraftRecord.DutiesFacts

namespace SpecDraftRecord.DutiesFacts

/-! ## The attestations a proposal may include -/

open DecoupledConsensusModel DecoupledConsensusModel.Sts DecoupledConsensusModel.Sts.Record
open SpecDraftRecord.ContractImages
open DecoupledConsensusModel.Protocol (HealConfig HeightConfig Node GradeRead)
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-- At `Model.specDraft`, every named attestation of an outcome `L` of `select .poolAndCarried` at
    the named store `st` is among `st`'s pool rows or among every outcome `C` of `carriedRows` at
    `st`. -/
theorem specDraft_mem_select_poolAndCarried :
    ∀ (hc : Protocol.HealConfig) (st : (Model.specDraft (V := V)).NS) {a : NamedAttestation V}
    (L : List (NamedAttestation V)), (Model.specDraft (V := V)).select .poolAndCarried hc st ⇢ L →
    a ∈ L → ∀ C : List (NamedAttestation V), (Model.specDraft (V := V)).carriedRows hc st ⇢ C → a ∈ (Model.specDraft (V := V)).poolRows hc st ∨ a ∈ C := by
  intro hc st a L hL ha C hC
  obtain ⟨rows, hrows, rfl⟩ := except_map_eq_ok ((returns_successOutcomes _ _).1 hL)
  obtain ⟨car, hcar, rfl⟩ := except_map_eq_ok ((returns_successOutcomes _ _).1 hC)
  unfold Spec.Protocol.attestations_to_include at hrows
  obtain ⟨car', hcar', hrows⟩ := NoRaise.DRE.of_bind_ok hrows
  have e : car' = car := Except.ok.inj (hcar'.symm.trans hcar)
  subst e
  rw [← Except.ok.inj hrows, List.map_append, List.mem_append] at ha
  exact ha

/-- At `Model.specDraft`, a row among a store's processed rows whose round is in the store's row
    window is in every outcome `L` of the rows a proposal on that store selects, from either row
    source. -/
theorem specDraft_mem_select_of_processed_inWindow :
    ∀ (source : Protocol.ProposalRowSource) (hc : Protocol.HealConfig) (st : (Model.specDraft (V := V)).NS) {a : NamedAttestation V} (hproc : a ∈ (Model.specDraft (V := V)).processedRows hc st) (hw : (Model.specDraft (V := V)).inWindow hc st.core a.round = true)
    (L : List (NamedAttestation V)) (hL : (Model.specDraft (V := V)).select source hc st ⇢ L), a ∈ L := by
  intro source hc st a hproc hw L hL
  obtain ⟨rows, hrows, rfl⟩ := except_map_eq_ok ((returns_successOutcomes _ _).1 hL)
  unfold Spec.Protocol.attestations_to_include at hrows
  obtain ⟨car, -, hrows⟩ := NoRaise.DRE.of_bind_ok hrows
  rw [← Except.ok.inj hrows, List.map_append, List.mem_append]
  left
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hproc
  refine List.mem_map.mpr ⟨x, ?_, rfl⟩
  unfold Spec.Protocol.attestations_in_window
  exact List.mem_filter.mpr ⟨hx, hw⟩

end SpecDraftRecord.DutiesFacts

namespace SpecDraftRecord.DutiesFacts

/-! ## The attestation's height pair and source -/

open DecoupledConsensusModel DecoupledConsensusModel.Sts DecoupledConsensusModel.Sts.Record
open SpecDraftRecord.ContractImages
open DecoupledConsensusModel.Protocol (HealConfig HeightConfig Node GradeRead)
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-- The round of the slot of a healing store of `Model.specDraft` is the spec's round of the store's
    slot. -/
theorem round_of_toSpec (E : Env V) (hc : Protocol.HealConfig) (st : (Model.specDraft (V := V)).HS) :
    (Model.specDraft (V := V)).round_of hc st.toFG.toSG.toGoldfishStore.s =
      (Spec.Config.toSpec E hc unreadHeightConfig).round_of st.val.s := by
  simp only [Model.GS.s, Model.specDraft, Member.gs_s, Member.toHealing, Member.toFG, Member.toSG,
    Member.toGoldfishStore, Model.HS.toFG, Model.FGS.toSG, Model.SGS.toGoldfishStore, id_eq,
    toProof_gs_s, Spec.Store.toProof_s, Member.round_of]
  rfl

/-- At `Model.specDraft`, if the contract's read of the store's round offers no grade-2 candidate,
    the round action's attestation has the empty height pair. -/
theorem specDraft_round_action_with_height_pair_of_Q2_none :
    ∀ (contract : (Model.specDraft (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : (Model.specDraft (V := V)).HS) (record : (Model.specDraft (V := V)).NR) (G : GradeRead V) (hG : contract.read E hc st (((Model.specDraft (V := V)).round_of hc st.toFG.toSG.toGoldfishStore.s)) ⇢ G) (h : G.Q2 = none) (A : (Model.specDraft (V := V)).NR × NamedAttestation V) (hA : (Model.specDraft (V := V)).round_action_with contract E hc nd st record ⇢ A), A.2.height_pair = NamedHeightPair.empty := by
  intro contract E hc nd st record G hG h A hA
  obtain ⟨p, hp, rfl⟩ := round_action_with_shape hA
  obtain ⟨i, hi, -, -, rfl⟩ := build_attestation_shape hp
  obtain ⟨A_G2, src, hA2, hsrc, hf⟩ := attestation_input_fields hi
  obtain ⟨Q2, hQ2, hGQ⟩ := read_shape (E := E) (hc := hc) hG
  rw [round_of_toSpec E] at hQ2
  unfold Spec.Protocol.grade2_block_with at hA2
  have e : Q2 = A_G2 := Except.ok.inj (hQ2.symm.trans hA2)
  subst e
  rw [h] at hGQ
  have hQ : Q2 = none := Option.map_eq_none_iff.mp hGQ.symm
  subst hQ
  rw [fg_source_with_none] at hsrc
  cases Except.ok.inj hsrc
  show Spec.HeightPair.toProofNamed (Spec.Protocol.create _ i).2.height_pair = _
  rw [create_height_pair, hf]
  rfl

/-- At `Model.specDraft`, if the round action's attestation has the vote at `h` for `entry`, the
    attestation input's fields are `h`, `entry` and some flag. -/
theorem specDraft_round_action_names_source :
    ∀ (contract : (Model.specDraft (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : (Model.specDraft (V := V)).HS) (record : (Model.specDraft (V := V)).NR) (h : Height) (entry : BlockId) (timeout : Bool) (A : (Model.specDraft (V := V)).NR × NamedAttestation V) (hA : (Model.specDraft (V := V)).round_action_with contract E hc nd st record ⇢ A) (hp : A.2.height_pair = .vote h entry timeout) (I : Protocol.AttestationInput V) (hI : (Model.specDraft (V := V)).with_attestation_input contract E hc nd st id ⇢ I), ∃ nu, I.fields = some (h, entry, nu) := by
  intro contract E hc nd st record h entry timeout A hA hp I hI
  obtain ⟨p, hp', rfl⟩ := round_action_with_shape hA
  obtain ⟨i, hi, -, -, rfl⟩ := build_attestation_shape hp'
  obtain ⟨i', hi', rfl⟩ := except_map_eq_ok ((returns_successOutcomes _ _).1 hI)
  have e : i' = i := Except.ok.inj (hi'.symm.trans hi)
  subst e
  change Spec.HeightPair.toProofNamed (Spec.Protocol.create _ i').2.height_pair = _ at hp
  rw [create_height_pair] at hp
  generalize hq : Spec.Protocol.height_pair _ i'.fields _ = q at hp
  cases q with
  | empty => cases hp
  | vote h' T b =>
    simp only [Spec.HeightPair.toProofNamed, NamedHeightPair.vote.injEq] at hp
    obtain ⟨rfl, rfl, rfl⟩ := hp
    obtain ⟨ν, hν⟩ := height_pair_vote_fields hq
    refine ⟨ν, ?_⟩
    show i'.fields.map _ = _
    rw [hν]
    rfl

/-- At `Model.specDraft`, the round action's height pair is the encoding of the attestation input's
    fields with some height pair. -/
theorem specDraft_round_action_with_height_pair_input :
    ∀ (contract : (Model.specDraft (V := V)).Contract) (E : DecoupledConsensusModel.Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig) (nd : DecoupledConsensusModel.Protocol.Node V) (st : (Model.specDraft (V := V)).HS) (record : (Model.specDraft (V := V)).NR) (A : (Model.specDraft (V := V)).NR × NamedAttestation V) (hA : (Model.specDraft (V := V)).round_action_with contract E hc nd st record ⇢ A) (I : Protocol.AttestationInput V) (hI : (Model.specDraft (V := V)).with_attestation_input contract E hc nd st id ⇢ I), ∃ pair, A.2.height_pair = (Model.specDraft (V := V)).encodeHeight I.fields pair := by
  intro contract E hc nd st record A hA I hI
  obtain ⟨p, hp', rfl⟩ := round_action_with_shape hA
  obtain ⟨i, hi, -, -, rfl⟩ := build_attestation_shape hp'
  obtain ⟨i', hi', rfl⟩ := except_map_eq_ok ((returns_successOutcomes _ _).1 hI)
  have e : i' = i := Except.ok.inj (hi'.symm.trans hi)
  subst e
  show ∃ pair, Spec.HeightPair.toProofNamed (Spec.Protocol.create _ i').2.height_pair = _
  rw [create_height_pair]
  generalize hq : Spec.Protocol.height_pair _ i'.fields _ = q
  cases q with
  | empty =>
    refine ⟨.empty, ?_⟩
    show _ = Protocol.NamedRecord.encodeHeight (i'.fields.map _) _
    cases i'.fields <;> simp [Protocol.NamedRecord.encodeHeight, Spec.HeightPair.toProofNamed]
  | vote h' T b =>
    obtain ⟨ν, hν⟩ := height_pair_vote_fields hq
    cases b
    · refine ⟨.target h' T.toProof, ?_⟩
      show _ = Protocol.NamedRecord.encodeHeight (i'.fields.map _) _
      rw [hν]
      simp [Protocol.NamedRecord.encodeHeight, Spec.HeightPair.toProofNamed]
    · refine ⟨.timeout h', ?_⟩
      show _ = Protocol.NamedRecord.encodeHeight (i'.fields.map _) _
      rw [hν]
      simp [Protocol.NamedRecord.encodeHeight, Spec.HeightPair.toProofNamed]

/-- At `Model.specDraft`, under the confirmation-membership invariant, the finality-gadget source at
    the contract's grade-2 candidate is a block of the store's tree. -/
theorem specDraft_frame_fg_source_mem :
    ∀ (S : DecoupledConsensusModel.Execution.Setup V) (cache : (Model.specDraft (V := V)).Cache) (st : (Model.specDraft (V := V)).NS) (r : Round) (hinv : Restated.Vocabulary.Proofs.NamedConfirmationMembership.Invariant (Model.specDraft (V := V)) S.E S.cfg st) {raw : Block V} (A2 : Option (Block V)) (hA2 : (Model.specDraft (V := V)).grade2_block_with ((Model.specDraft (V := V)).gradeContract cache) S.E S.hc ((Model.specDraft (V := V)).toHealing st.core) r ⇢ A2) (o : Option (Block V)) (ho : (Model.specDraft (V := V)).fg_source_with ((Model.specDraft (V := V)).gradeContract cache) S.E S.hc ((Model.specDraft (V := V)).toHealing st.core) r A2 ⇢ o) (hs : o = some raw), raw ∈ st.core.T := by
  intro S cache st r hinv raw A2 hA2 o ho hs
  subst hs
  show raw ∈ st.val.T.image Spec.Block.toProof
  obtain ⟨Q2, hQ2, rfl⟩ := grade2_block_with_shape (E := S.E) (hc := S.hc) hA2
  have ho' : Returns (Member.fg_source_with cache S.E S.hc st.val r (Q2.map Spec.Block.toProof))
      (some raw) := ho
  unfold Member.fg_source_with at ho'
  obtain ⟨o', ho', e⟩ := except_map_eq_ok ((returns_successOutcomes _ _).1 ho')
  cases Q2 with
  | none =>
    rw [Option.map_none, Option.map_none, fg_source_with_none] at ho'
    cases Except.ok.inj ho'
    cases e
  | some Q =>
    have hQ' := GradesImages.filtered_subset _ (grade2Block_mem_filtered hQ2)
    have hQ : Q ∈ st.val.T := hQ'
    have hbl : st.val.blockOfImage Q.toProof = Q :=
      Spec.Store.blockOfImage_toProof_of_mem _ st.property.2.1 hQ
    rw [Option.map_some, Option.map_some, hbl] at ho'
    rcases draft_fg_source_some_cases ho' with rfl | ⟨G0, B, -, hB, rfl⟩
    · cases e
      exact Finset.mem_image_of_mem _ hQ
    · cases e
      have hlc : st.val.live_confirmed.toProof ∈ st.val.T.image Spec.Block.toProof :=
        hinv.2.1
      obtain ⟨X, hX, hXl⟩ := Finset.mem_image.mp hlc
      replace hXl : X.toProof = (Spec.Store.ofImage st.val).live_confirmed.toProof :=
        hXl.trans (Spec.Store.toProof_blockOfImage _ _).symm
      exact toProof_mem_image_of_mem_chain st.property.2.2.1 hX hXl (deepest_clear_mem_chain hB)

/-- At `Model.specDraft`, under the confirmation-membership invariant, the attestation input
    confirms the root of a block of the store's tree. -/
theorem specDraft_attestation_input_head_gradeContract :
    ∀ (c : (Model.specDraft (V := V)).Cache) (E : Env V) (hc : Protocol.HealConfig) (cfg : HeightConfig) (nd : Protocol.Node V) (st : (Model.specDraft (V := V)).NS) (h : Restated.Vocabulary.Proofs.NamedConfirmationMembership.Invariant (Model.specDraft (V := V)) E cfg st) (I : Protocol.AttestationInput V) (hI : (Model.specDraft (V := V)).with_attestation_input ((Model.specDraft (V := V)).gradeContract c) E hc nd ((Model.specDraft (V := V)).toHealing st.core) id ⇢ I), ∃ H ∈ st.core.T, I.confirmed = some H.root := by
  intro c E hc cfg nd st h I hI
  have hI' : Returns (Member.with_attestation_input c E hc nd st.val id) I := hI
  unfold Member.with_attestation_input at hI'
  obtain ⟨i, hi, rfl⟩ := except_map_eq_ok ((returns_successOutcomes _ _).1 hI')
  obtain ⟨A_G2, W, hA, hW, hconf⟩ := attestation_input_confirmed hi
  refine ⟨W.toProof, ?_, ?_⟩
  · show W.toProof ∈ st.val.T.image Spec.Block.toProof
    have hpar := st.property.2.2.1
    have hfilt : ∀ X, X ∈ Spec.Protocol.get_filtered_block_tree
        { Spec.Store.ofImage st.val with saved_grades := fill (Spec.Protocol.advance_to_round (st.val.contractOfImage c) ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.val.s)) } →
        X.toProof ∈ st.val.T.image Spec.Block.toProof :=
      fun X hX => by
        have h' := GradesImages.filtered_subset _ hX
        exact Finset.mem_image_of_mem _ h'
    have hroot : (Spec.Protocol.get_fg_root
        { Spec.Store.ofImage st.val with saved_grades := fill (Spec.Protocol.advance_to_round (st.val.contractOfImage c) ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.val.s)) }).toProof ∈
        st.val.T.image Spec.Block.toProof := by
      have e : (Spec.Protocol.get_fg_root
          { Spec.Store.ofImage st.val with saved_grades := fill (Spec.Protocol.advance_to_round (st.val.contractOfImage c) ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.val.s)) }).toProof =
          (Spec.Protocol.get_fg_root st.val).toProof :=
        Spec.Store.toProof_get_fg_root_ofImage st.val
      rw [e]
      unfold Spec.Protocol.get_fg_root
      simp only [Id.run, pure]
      split
      · exact h.1.2.2
      · exact Finset.mem_image_of_mem _ st.property.2.2.2
    unfold Spec.Protocol.get_sg_vote_with at hW
    obtain ⟨g, hg, hW⟩ := NoRaise.DRE.of_bind_ok hW
    rw [← Except.ok.inj hW]
    rcases currentSGVote_cases _ { g with Q2 := A_G2 } with ⟨B, hB, e⟩ | ⟨Q, hQ, e⟩ | e | e <;> rw [e]
    · have hlc : st.val.live_confirmed.toProof ∈ st.val.T.image Spec.Block.toProof := h.2.1
      obtain ⟨X, hX, hXl⟩ := Finset.mem_image.mp hlc
      replace hXl : X.toProof = (Spec.Store.ofImage st.val).live_confirmed.toProof :=
        hXl.trans (Spec.Store.toProof_blockOfImage _ _).symm
      exact toProof_mem_image_of_mem_chain hpar hX hXl (deepest_clear_mem_chain hB)
    · cases hQ
      unfold Spec.Protocol.grade2_block_with at hA
      exact hfilt _ (grade2Block_mem_filtered hA)
    · exact hroot
    · rcases round_grade_read_anchor_cases hg with e' | e'
      · show g.anchor.toProof ∈ _
        rw [e']
        exact hroot
      · exact hfilt _ e'
  · show i.confirmed.map Spec.BlockId.toProof = some W.toProof.root
    rw [hconf, Spec.Block.toProof_root]
    rfl

/-- At `Model.specDraft`, if no clear block of the live confirmed chain descends from the candidate
    `q`, the finality-gadget source at `q` is `q`. -/
theorem specDraft_fg_source_with_some_of_deepest_clear_none :
    ∀ (contract : (Model.specDraft (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (st : (Model.specDraft (V := V)).HS) (r : Round) {q : Block V} (G : GradeRead V) (hG : contract.read E hc st r ⇢ G) (h : (Model.specDraft (V := V)).deepest_clear (some q) st.toFG.toSG.toGoldfishStore.live_confirmed G.clear = none) (o : Option (Block V)) (ho : (Model.specDraft (V := V)).fg_source_with contract E hc st r (some q) ⇢ o), o = some q := by
  intro contract E hc st r q G hG h o ho
  have ho' : Returns (Member.fg_source_with contract E hc st.val r (some q)) o := ho
  unfold Member.fg_source_with at ho'
  obtain ⟨o', hx, rfl⟩ := except_map_eq_ok ((returns_successOutcomes _ _).1 ho')
  rw [Option.map_some] at hx
  rcases draft_fg_source_some_cases hx with rfl | ⟨G0, B, hg0, hB, rfl⟩
  · simp
  · exfalso
    have hG' : Returns (Member.read contract E hc st.val r) G := hG
    unfold Member.read at hG'
    obtain ⟨g, -, hGe⟩ := except_map_eq_ok ((returns_successOutcomes _ _).1 hG')
    obtain ⟨hBc, hBf, hBt⟩ := deepest_clear_spec hB
    have hcl : G.clear = Member.clear (Spec.Protocol.round_grades
        { Spec.Store.ofImage st.val with saved_grades := fill (Spec.Protocol.advance_to_round (st.val.contractOfImage contract) r) } r) := by
      rw [← hGe]
    rw [hcl] at h
    have hlc : (Spec.Store.ofImage st.val).live_confirmed.toProof = st.val.live_confirmed.toProof :=
      Spec.Store.toProof_blockOfImage _ _
    have h' : DecoupledConsensusModel.Protocol.deepest_clear (some q)
        (Spec.Store.ofImage st.val).live_confirmed.toProof
        (Member.clear (Spec.Protocol.round_grades
          { Spec.Store.ofImage st.val with saved_grades := fill (Spec.Protocol.advance_to_round (st.val.contractOfImage contract) r) } r)) = none := by
      change Member.deepest_clear (some q) (Member.gs_live_confirmed st.val) _ = none at h
      rw [Member.gs_live_confirmed, toProof_gs_live_confirmed] at h
      unfold Member.deepest_clear at h
      rw [Spec.Protocol.deepest_clear_toSpec] at h
      rw [hlc]
      exact h
    have hs := Proofs.HealingSurface.deepest_clear_isSome_of_mem (floor := some q)
      (C := (Spec.Store.ofImage st.val).live_confirmed.toProof) (B := B.toProof)
      (test := Member.clear (Spec.Protocol.round_grades
        { Spec.Store.ofImage st.val with saved_grades := fill (Spec.Protocol.advance_to_round (st.val.contractOfImage contract) r) } r))
      ?_ ?_ ?_
    · simp only [h', Option.isSome_none, Bool.false_eq_true] at hs
    · have := Spec.Block.toProof_preceq_of_ancestorEq _ _ hBf
      rw [Spec.Store.toProof_blockOfImage] at this
      exact this
    · rw [chain_of_toProof]
      exact List.mem_map_of_mem hBc
    · unfold Member.clear DecoupledConsensusModel.Protocol.clear
      simp only [Spec.RoundGrades.toProof, hg0, Spec.GradeResult.toProof]
      cases G0 with
      | none => rfl
      | some R =>
        simp only [Option.map_some]
        exact Spec.Block.toProof_compatible_of_compatible _ _ hBt

end SpecDraftRecord.DutiesFacts

namespace SpecDraftRecord.DutiesFacts

/-! ## The confirmation records -/

open DecoupledConsensusModel DecoupledConsensusModel.Sts DecoupledConsensusModel.Sts.Record
open SpecDraftRecord.ContractImages
open DecoupledConsensusModel.Protocol (HealConfig HeightConfig Node GradeRead)
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-- An outcome `D` of the named confirmation duty under `c` is `st` with the three confirmation
    records the spec's update computes and `c` as saved grades, and nothing else written. -/
theorem confirmation_out {c : Spec.SavedGrades V} {E : Env V} {hc : Protocol.HealConfig}
    {st D : Spec.Store V} {s : Slot}
    (h : Returns (Member.duties_update_confirmation_with c E hc st s) D) :
    ∃ out, Spec.Protocol.update_confirmation (Spec.Config.toSpec E hc unreadHeightConfig)
        { Spec.Store.ofImage st with saved_grades := fill (Spec.Protocol.advance_to_round (st.contractOfImage c) ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.s)) } s = .ok out ∧
      D = { Spec.Store.ofImage st with live_confirmed := out.live_confirmed, latest_stable := out.latest_stable, latest_confirmed := out.latest_confirmed, saved_grades := c } := by
  unfold Member.duties_update_confirmation_with at h
  rw [returns_successOutcomes] at h
  obtain ⟨out, hout, e⟩ := except_map_eq_ok h
  refine ⟨out, hout, ?_⟩
  rw [← e]
  exact congrArg (fun o : Spec.Store V => { o with saved_grades := c })
    (NoRaise.update_confirmation_writes_only_confirmation hout)

/-- At `Model.specDraft`, the named confirmation update keeps a coherent store coherent. -/
theorem specDraft_coherent_confirmation :
    ∀ (gc : (Model.specDraft (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (st : (Model.specDraft (V := V)).NS) (s : Slot), Restated.Vocabulary.Proofs.NamedStore.Coherent (Model.specDraft (V := V)) E cfg st → ∀ D : (Model.specDraft (V := V)).NS, (Model.specDraft (V := V)).duties_update_confirmation_with gc E hc st s ⇢ D → Restated.Vocabulary.Proofs.NamedStore.Coherent (Model.specDraft (V := V)) E cfg D := by
  intro gc E hc cfg st s h D hD
  obtain ⟨out, -, he⟩ := confirmation_out ((returns_preimageOutcomes _ _ _).1 hD)
  obtain ⟨v, hv⟩ := D
  dsimp only at he
  subst he
  exact h

/-- At `Model.specDraft`, the named confirmation duty keeps the confirmation-membership invariant. -/
theorem specDraft_invariant_update_gradeContract :
    ∀ (c : (Model.specDraft (V := V)).Cache) (E : Env V) (hc : Protocol.HealConfig) (cfg : HeightConfig) (st : (Model.specDraft (V := V)).NS) (s : Slot) (h : Restated.Vocabulary.Proofs.NamedConfirmationMembership.Invariant (Model.specDraft (V := V)) E cfg st) (D : (Model.specDraft (V := V)).NS) (hD : (Model.specDraft (V := V)).duties_update_confirmation_with ((Model.specDraft (V := V)).gradeContract c) E hc st s ⇢ D), Restated.Vocabulary.Proofs.NamedConfirmationMembership.Invariant (Model.specDraft (V := V)) E cfg D := by
  intro c E hc cfg st s h D hD
  obtain ⟨out, hout, he⟩ := confirmation_out ((returns_preimageOutcomes _ _ _).1 hD)
  obtain ⟨g1, g2, g3⟩ := update_confirmation_good hout
  have good : ∀ X, ConfirmationGood { Spec.Store.ofImage st.val with saved_grades := fill (Spec.Protocol.advance_to_round (st.val.contractOfImage c) ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.val.s)) } X →
      X.toProof ∈ st.val.T.image Spec.Block.toProof := by
    intro X hX
    rcases hX with hX | hX
    · rw [hX]
      have e : (Spec.Protocol.get_fg_root
          { Spec.Store.ofImage st.val with saved_grades := fill (Spec.Protocol.advance_to_round (st.val.contractOfImage c) ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.val.s)) }).toProof =
          (Spec.Protocol.get_fg_root st.val).toProof :=
        Spec.Store.toProof_get_fg_root_ofImage st.val
      rw [e]
      unfold Spec.Protocol.get_fg_root
      simp only [Id.run, pure]
      split
      · exact h.1.2.2
      · exact Finset.mem_image_of_mem _ st.property.2.2.2
    · have h' := GradesImages.filtered_subset _ hX
      exact Finset.mem_image_of_mem _ h'
  obtain ⟨v, hv⟩ := D
  dsimp only at he
  subst he
  refine ⟨⟨h.1.1, ?_, ?_⟩, ?_, ?_, ?_⟩
  · show (Spec.Store.ofImage st.val).F.toProof ∈ st.val.T.image Spec.Block.toProof
    rw [Spec.Store.ofImage_F, Spec.Store.toProof_blockOfImage]
    exact h.1.2.1
  · show (Spec.Store.ofImage st.val).J.toProof ∈ st.val.T.image Spec.Block.toProof
    rw [Spec.Store.ofImage_J, Spec.Store.toProof_blockOfImage]
    exact h.1.2.2
  · exact good _ g1
  · show out.latest_confirmed.toProof ∈ st.val.T.image Spec.Block.toProof
    rcases g3 with g | g | g
    · exact good _ g
    · rw [g]
      show (Spec.Store.ofImage st.val).latest_confirmed.toProof ∈ _
      rw [Spec.Store.ofImage_latest_confirmed, Spec.Store.toProof_blockOfImage]
      exact h.2.2.1
    · rw [g]
      show (Spec.Store.ofImage st.val).latest_stable.toProof ∈ _
      rw [Spec.Store.ofImage_latest_stable, Spec.Store.toProof_blockOfImage]
      exact h.2.2.2
  · show out.latest_stable.toProof ∈ st.val.T.image Spec.Block.toProof
    rcases g2 with g | g
    · exact good _ g
    · rw [g]
      show (Spec.Store.ofImage st.val).latest_stable.toProof ∈ _
      rw [Spec.Store.ofImage_latest_stable, Spec.Store.toProof_blockOfImage]
      exact h.2.2.2

/-- At `Model.specDraft`, if `get_fg_root` of the store is in the filtered tree, so is the live
    confirmed block of every outcome of the confirmation update. -/
theorem specDraft_update_confirmation_with_live_confirmed_mem_filtered :
    ∀ (contract : (Model.specDraft (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (st : (Model.specDraft (V := V)).S) (s : Slot), (Model.specDraft (V := V)).get_fg_root ((Model.specDraft (V := V)).toHealing st).toFG ∈ (Model.specDraft (V := V)).get_filtered_block_tree ((Model.specDraft (V := V)).toHealing st).toFG → ∀ R : Block V, (Model.specDraft (V := V)).get_sg_root_with contract E hc ((Model.specDraft (V := V)).toHealing st) ((Model.specDraft (V := V)).round_of hc st.s) ⇢ R → R ∈ (Model.specDraft (V := V)).get_filtered_block_tree ((Model.specDraft (V := V)).toHealing st).toFG → ∀ st' : (Model.specDraft (V := V)).S, (Model.specDraft (V := V)).update_confirmation_with contract E hc st s ⇢ st' → st'.live_confirmed ∈ (Model.specDraft (V := V)).get_filtered_block_tree ((Model.specDraft (V := V)).toHealing st).toFG := by
  intro contract E hc st s hfg R _ _ st' hst'
  obtain ⟨out, hout, he⟩ := confirmation_out ((returns_preimageOutcomes _ _ _).1 hst')
  obtain ⟨g1, -, -⟩ := update_confirmation_good hout
  obtain ⟨v, hv⟩ := st'
  dsimp only at he
  subst he
  show out.live_confirmed.toProof ∈ (Spec.Protocol.get_filtered_block_tree
      (Spec.Store.ofImage st.val)).image
    Spec.Block.toProof
  rcases g1 with g | g
  · rw [g]
    exact hfg
  · exact Finset.mem_image_of_mem _ g

end SpecDraftRecord.DutiesFacts

namespace SpecDraftRecord.DutiesFacts

/-! ## The proposal's rows -/

open DecoupledConsensusModel DecoupledConsensusModel.Sts DecoupledConsensusModel.Sts.Record
open SpecDraftRecord.ContractImages
open DecoupledConsensusModel.Protocol (HealConfig HeightConfig Node GradeRead)
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-- At `Model.specDraft`, if every bucket is the erasure of its named rows, the erasures of the
    processed rows are the buckets of rounds `0` to the store's round, in order. -/
theorem specDraft_processed_rows_erasure :
    ∀ (hc : Protocol.HealConfig) (st : (Model.specDraft (V := V)).NS), (∀ r, st.core.sg_votes r = (st.sg_rows r).map NamedAttestation.erase) → ((Model.specDraft (V := V)).processedRows hc st).map NamedAttestation.erase = (List.range (((Model.specDraft (V := V)).round_of hc st.core.s) + 1)).flatMap st.core.sg_votes := by
  intro hc st h
  have hr : (List.range (((Model.specDraft (V := V)).round_of hc st.core.s) + 1)).flatMap st.core.sg_votes =
      (List.range (((Model.specDraft (V := V)).round_of hc st.core.s) + 1)).flatMap
        (fun r => (st.sg_rows r).map NamedAttestation.erase) := by
    congr 1
    funext r
    exact h r
  rw [hr]
  show ((Spec.Protocol.all_attestations _ st.val).map Spec.Attestation.toProofNamed).map
    NamedAttestation.erase = _
  unfold Spec.Protocol.all_attestations
  rw [List.map_flatMap, List.map_flatMap]
  rfl

/-- At `Model.specDraft`, every ordered body is a body of the store. -/
theorem specDraft_ordered_bodies_mem :
    ∀ {st : (Model.specDraft (V := V)).NS} {B : DecoupledConsensusModel.NamedBlock V} (O : List (DecoupledConsensusModel.NamedBlock V)), (Model.specDraft (V := V)).orderedBodies st ⇢ O → B ∈ O → B ∈ st.bodies := by
  intro st B O hO hB
  have hO' : Returns (Member.orderedBodies st.val) O := hO
  unfold Member.orderedBodies at hO'
  obtain ⟨bodies, hb, rfl⟩ := except_map_eq_ok ((returns_successOutcomes _ _).1 hO')
  obtain ⟨B', hB', rfl⟩ := List.mem_map.mp hB
  exact Finset.mem_map_of_mem _ (sorted_blocks_mem hb B' hB')

/-- At `Model.specDraft`, every row the selector offers has a round at most the store's round. -/
theorem specDraft_selected_row_round_le :
    ∀ (hc : DecoupledConsensusModel.Protocol.HealConfig) (st : (Model.specDraft (V := V)).NS) {a : DecoupledConsensusModel.NamedAttestation V} (L : List (DecoupledConsensusModel.NamedAttestation V)), (Model.specDraft (V := V)).select .poolAndCarried hc st ⇢ L → a ∈ L → a.round ≤ (Model.specDraft (V := V)).round_of hc st.core.s := by
  intro hc st a L hL ha
  have hL' : Returns (Member.select .poolAndCarried hc st.val) L := hL
  unfold Member.select at hL'
  obtain ⟨rows, hrows, rfl⟩ := except_map_eq_ok ((returns_successOutcomes _ _).1 hL')
  obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ha
  exact attestations_to_include_round_le hrows a' ha'

/-- At `Model.specDraft`, a row is in `carriedRows` exactly when an eligible ordered body includes
    it and its round is in the store's window. -/
theorem specDraft_mem_carried_rows :
    ∀ (hc : DecoupledConsensusModel.Protocol.HealConfig) (st : (Model.specDraft (V := V)).NS) (row : DecoupledConsensusModel.NamedAttestation V) (C : List (DecoupledConsensusModel.NamedAttestation V)) (hC : (Model.specDraft (V := V)).carriedRows hc st ⇢ C) (O : List (DecoupledConsensusModel.NamedBlock V)) (hO : (Model.specDraft (V := V)).orderedBodies st ⇢ O), row ∈ C ↔ ∃ B ∈ O, (Model.specDraft (V := V)).eligibleBody hc st B = Bool.true ∧ row ∈ B.attestations ∧ (Model.specDraft (V := V)).inWindow hc st.core row.round = Bool.true := by
  intro hc st row C hC O hO
  have hC' : Returns (Member.carriedRows hc st.val) C := hC
  have hO' : Returns (Member.orderedBodies st.val) O := hO
  unfold Member.carriedRows at hC'
  unfold Member.orderedBodies at hO'
  obtain ⟨rows, hrows, rfl⟩ := except_map_eq_ok ((returns_successOutcomes _ _).1 hC')
  obtain ⟨bodies, hb, rfl⟩ := except_map_eq_ok ((returns_successOutcomes _ _).1 hO')
  obtain ⟨bodies', hb', rfl⟩ := included_attestations_in_window_ok hrows
  have e : bodies' = bodies := Except.ok.inj (hb'.symm.trans hb)
  subst e
  have hatt : ∀ B : Spec.Block V,
      B.toProofNamed.attestations = B.attestations.map Spec.Attestation.toProofNamed := by
    intro B; cases B <;> simp [Spec.Block.toProofNamed, Spec.Block.attestations, DecoupledConsensusModel.NamedBlock.attestations]
  constructor
  · intro hr
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    obtain ⟨B, hB, haB⟩ := List.mem_flatMap.mp ha
    split at haB
    · rename_i hmay
      obtain ⟨haB, hw⟩ := List.mem_filter.mp haB
      refine ⟨B.toProofNamed, List.mem_map_of_mem hB, ?_, ?_, hw⟩
      · show Spec.Protocol.may_repropose_attestations_of _ st.val
          (Spec.Block.toSpecNamed B.toProofNamed) = true
        rw [Spec.Block.toSpecNamed_toProofNamed]
        exact hmay
      · rw [hatt]
        exact List.mem_map_of_mem haB
    · cases haB
  · rintro ⟨B, hB, hmay, hrB, hw⟩
    obtain ⟨B', hB', rfl⟩ := List.mem_map.mp hB
    rw [hatt] at hrB
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hrB
    have hmay' : Spec.Protocol.may_repropose_attestations_of
        (Spec.Config.toSpec (Member.unreadEnvForDuties (V := V)) hc unreadHeightConfig) st.val B' = true := by
      have := hmay
      change Spec.Protocol.may_repropose_attestations_of _ st.val
        (Spec.Block.toSpecNamed B'.toProofNamed) = true at this
      rwa [Spec.Block.toSpecNamed_toProofNamed] at this
    refine List.mem_map_of_mem (List.mem_flatMap.mpr ⟨B', hB', ?_⟩)
    rw [if_pos hmay']
    exact List.mem_filter.mpr ⟨ha, hw⟩

/-- At `Model.specDraft`, a proposal the duty builds includes only attestations of its slot's round
    or earlier. -/
theorem specDraft_proposal_with_carried_admissible_inclG2 :
    ∀ (contract : (Model.specDraft (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : (Model.specDraft (V := V)).NS) {B : NamedBlock V} (o : Option (NamedBlock V)) (ho : (Model.specDraft (V := V)).proposal_with contract .poolAndCarried E hc nd st ⇢ o) (hB : o = some B), (Model.specDraft (V := V)).carried_attestations_admissible hc B.erase = true := by
  intro contract E hc nd st B o ho hB
  subst hB
  have ho' : Returns (Member.proposal_with contract .poolAndCarried E hc nd st.val) (some B) := ho
  unfold Member.proposal_with at ho'
  obtain ⟨Bd, hBd, e⟩ := except_map_eq_ok ((returns_successOutcomes _ _).1 ho')
  cases Option.some.inj e
  obtain ⟨i, rows, hi, hrows, rfl⟩ := build_proposal_shape hBd
  obtain ⟨H, sv, -, -, rfl⟩ := proposal_input_shape hi
  have hle := attestations_to_include_round_le hrows
  show Spec.Protocol.included_attestations_admissible _
    (Spec.Block.toSpec (Spec.Block.toProofNamed _).erase) = true
  rw [Spec.Block.toProofNamed_erase]
  unfold Spec.Protocol.included_attestations_admissible
  rw [List.all_eq_true]
  intro a ha
  simp only [Spec.Block.toProof, Spec.Block.toSpec, Spec.Block.attestations,
    List.map_map, List.mem_map, Function.comp] at ha
  obtain ⟨a', ha', rfl⟩ := ha
  have h1 := hle a' (List.mem_filter.mp (capPerSigner_subset _ a' ha')).1
  simp only [Spec.Attestation.toSpec, Spec.Attestation.toProof] at h1 ⊢
  exact decide_eq_true h1

end SpecDraftRecord.DutiesFacts

namespace SpecDraftRecord.DutiesFacts

/-! ## The fields that hold because the store is read through its tree -/

open DecoupledConsensusModel DecoupledConsensusModel.Sts DecoupledConsensusModel.Sts.Record
open SpecDraftRecord.ContractImages
open DecoupledConsensusModel.Protocol (HealConfig HeightConfig Node GradeRead)
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-- At `Model.specDraft`, the SG vote a duty computes for the round's own grade-2 candidate is the
    vote `currentSGVote` gives at the contract's grade read. -/
theorem specDraft_get_sg_vote_with_gradeContract_grade2 : ∀ (c : (Model.specDraft (V := V)).Cache) (E : Env V) (hc : Protocol.HealConfig) (st : (Model.specDraft (V := V)).HS) (r : Round)
    (A2 : Option (Block V)) (hA2 : (Model.specDraft (V := V)).grade2_block_with ((Model.specDraft (V := V)).gradeContract c) E hc st r ⇢ A2)
    (G : GradeRead V) (hG : ((Model.specDraft (V := V)).gradeContract c).read E hc st r ⇢ G)
    (W : Block V) (hW : (Model.specDraft (V := V)).get_sg_vote_with ((Model.specDraft (V := V)).gradeContract c) E hc st r A2 ⇢ W),
    W = (Model.specDraft (V := V)).currentSGVote st G := by
  intro c E hc st r A2 hA2 G hG W hW
  obtain ⟨Q2, h1, rfl⟩ := grade2_block_with_shape (E := E) (hc := hc) hA2
  obtain ⟨W', hW', rfl⟩ := get_sg_vote_with_shape (E := E) (hc := hc) hW
  have hG' : Returns (Member.read ((Model.specDraft (V := V)).gradeContract c) E hc st.val r) G := hG
  unfold Member.read at hG'
  obtain ⟨g, hg, rfl⟩ := except_map_eq_ok ((returns_successOutcomes _ _).1 hG')
  obtain ⟨-, -, -, -, hQ⟩ := round_grade_read_parts hg
  have eQ : Q2 = g.Q2 := Except.ok.inj (h1.symm.trans hQ)
  subst eQ
  unfold Spec.Protocol.get_sg_vote_with at hW'
  obtain ⟨g', hg', hW'⟩ := NoRaise.DRE.of_bind_ok hW'
  have eg : g' = g := Except.ok.inj (hg'.symm.trans hg)
  subst eg
  rw [← Except.ok.inj hW', currentSGVote_contractStore st _ r hg']
  show Member.currentSGVote st.val _ = Member.currentSGVote st.val _
  congr 1
  rw [Option.map_map, Option.map_map]
  simp [Function.comp_def, Spec.Block.toProof_toSpec]
  rfl

/-- At `Model.specDraft`, when the clearing walk from the grade read's anchor finds `B`, the duty's
    SG vote is `B`, whatever the candidate. -/
theorem specDraft_get_sg_vote_with_gradeContract_of_deepest_clear : ∀ (c : (Model.specDraft (V := V)).Cache) (E : Env V) (hc : Protocol.HealConfig) (st : (Model.specDraft (V := V)).HS) (r : Round) (A_G2 : Option (Block V)) {B : Block V}
    (G : GradeRead V) (hG : ((Model.specDraft (V := V)).gradeContract c).read E hc st r ⇢ G)
    (h : (Model.specDraft (V := V)).deepest_clear (some G.anchor) st.toFG.toSG.toGoldfishStore.live_confirmed G.clear = some B)
    (W : Block V) (hW : (Model.specDraft (V := V)).get_sg_vote_with ((Model.specDraft (V := V)).gradeContract c) E hc st r A_G2 ⇢ W), W = B := by
  intro c E hc st r A_G2 B G hG h W hW
  obtain ⟨W', hW', rfl⟩ := get_sg_vote_with_shape (E := E) (hc := hc) hW
  have hG' : Returns (Member.read ((Model.specDraft (V := V)).gradeContract c) E hc st.val r) G := hG
  unfold Member.read at hG'
  obtain ⟨g, hg, rfl⟩ := except_map_eq_ok ((returns_successOutcomes _ _).1 hG')
  unfold Spec.Protocol.get_sg_vote_with at hW'
  obtain ⟨g', hg', hW'⟩ := NoRaise.DRE.of_bind_ok hW'
  have eg : g' = g := Except.ok.inj (hg'.symm.trans hg)
  subst eg
  rw [← Except.ok.inj hW', currentSGVote_contractStore st _ r hg']
  apply GradesImages.member_currentSGVote_of_deepest_clear st
  have h' : Member.deepest_clear _ (Member.gs_live_confirmed st.val) _ = some B := h
  rw [member_deepest_clear_eq] at h'
  exact h'

/-- At `Model.specDraft`, when the clearing walk from `q` finds `W`, the finality-gadget source at
    `q` is `W`. -/
theorem specDraft_fg_source_with_some_of_deepest_clear : ∀ (contract : (Model.specDraft (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (st : (Model.specDraft (V := V)).HS) (r : Round) {q W : Block V}
    (G : GradeRead V) (hG : contract.read E hc st r ⇢ G)
    (h : (Model.specDraft (V := V)).deepest_clear (some q) st.toFG.toSG.toGoldfishStore.live_confirmed G.clear = some W)
    (o : Option (Block V)) (ho : (Model.specDraft (V := V)).fg_source_with contract E hc st r (some q) ⇢ o), o = some W := by
  intro contract E hc st r q W G hG h o ho
  have ho' : Returns (Member.fg_source_with contract E hc st.val r (some q)) o := ho
  unfold Member.fg_source_with at ho'
  obtain ⟨o', hx, rfl⟩ := except_map_eq_ok ((returns_successOutcomes _ _).1 ho')
  rw [Option.map_some] at hx
  have hG' : Returns (Member.read contract E hc st.val r) G := hG
  unfold Member.read at hG'
  obtain ⟨g, hg, rfl⟩ := except_map_eq_ok ((returns_successOutcomes _ _).1 hG')
  have h' : Member.deepest_clear _ (Member.gs_live_confirmed st.val) _ = some W := h
  rw [member_deepest_clear_eq] at h'
  unfold Spec.Protocol.fg_source_with at hx
  simp only [ne_eq, reduceCtorEq, not_false_eq_true, Option.value, Option.get_some] at hx
  obtain ⟨G0, hG0, hx⟩ := NoRaise.DRE.of_bind_ok hx
  have hg0 : (Spec.Protocol.round_grades (contractStore st.val contract r) r).g0 = .computed G0 := by
    revert hG0
    cases (Spec.Protocol.round_grades (contractStore st.val contract r) r).g0 with
    | pending => intro hG0; cases hG0
    | computed G => intro hG0; cases hG0; rfl
  have hdc := deepest_clear_blockOfImage_test st.val st.property.2.1 st.property.2.2.1 q
    st.val.live_confirmed.toProof (Spec.Protocol.G0_compatible G0)
    (Member.clear (Spec.Protocol.round_grades (contractStore st.val contract r) r))
    (fun B hB => contractStore_clear_fixed st contract r hB hg0)
  rw [h'] at hdc
  obtain ⟨B', hB', e⟩ := Option.map_eq_some_iff.mp hdc
  have hB'' : Spec.Protocol.deepest_clear (st.val.blockOfImage q)
      (contractStore st.val contract r).live_confirmed (Spec.Protocol.G0_compatible G0) =
        some B' := hB'
  split at hx
  · rename_i hne
    obtain ⟨B, hB⟩ := Option.ne_none_iff_exists'.mp hne
    have hB2 : Spec.Protocol.deepest_clear (st.val.blockOfImage q)
        (contractStore st.val contract r).live_confirmed (Spec.Protocol.G0_compatible G0) =
          some B := hB
    have eB : B = B' := Option.some.inj (hB2.symm.trans hB'')
    subst eB
    rw [← Except.ok.inj hx]
    simp [hB, e]
  · rename_i hne
    have hn : Spec.Protocol.deepest_clear (st.val.blockOfImage q)
        (contractStore st.val contract r).live_confirmed (Spec.Protocol.G0_compatible G0) =
          none := by simpa using hne
    rw [hn] at hB''
    cases hB''

/-- At `Model.specDraft`, the attestation duty confirms the root of the contract's SG vote at the
    store's round. -/
theorem specDraft_namedDuties_attest_with_confirmed : ∀ (contract : (Model.specDraft (V := V)).Contract) (E : DecoupledConsensusModel.Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig) (nd : DecoupledConsensusModel.Protocol.Node V) (st : (Model.specDraft (V := V)).NS) (record : (Model.specDraft (V := V)).NR)
    (D : (Model.specDraft (V := V)).NS × (Model.specDraft (V := V)).NR × NamedAttestation V) (hD : (Model.specDraft (V := V)).duties_attest_with contract E hc nd st record ⇢ D)
    (G : GradeRead V) (hG : contract.read E hc ((Model.specDraft (V := V)).toHealing st.core) ((Model.specDraft (V := V)).round_of hc ((Model.specDraft (V := V)).toHealing st.core).toFG.toSG.toGoldfishStore.s) ⇢ G),
    D.2.2.confirmed = Option.some (contract.sgVote ((Model.specDraft (V := V)).toHealing st.core) G).root := by
  intro contract E hc nd st record D hD G hG
  obtain ⟨p, hp, hD'⟩ := duties_attest_with_shape ((returns_preimageOutcomes _ _ _).1 hD)
  have h2 : D.2.2 = p.2.toProofNamed := congrArg (fun x => x.2.2) hD'
  obtain ⟨i, hi, -, -, hpi⟩ := build_attestation_shape hp
  rw [h2, hpi]
  obtain ⟨A_G2, W0, hA, hW0, hconf⟩ := attestation_input_confirmed hi
  have hG' : Returns (Member.read contract E hc st.val
      ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.val.s)) G := by
    rw [← round_of_toSpec E hc st]
    exact hG
  unfold Member.read at hG'
  obtain ⟨g, hg, rfl⟩ := except_map_eq_ok ((returns_successOutcomes _ _).1 hG')
  obtain ⟨-, -, -, -, hQ⟩ := round_grade_read_parts hg
  unfold Spec.Protocol.grade2_block_with at hA
  have eQ : A_G2 = g.Q2 := Except.ok.inj (hA.symm.trans hQ)
  subst eQ
  unfold Spec.Protocol.get_sg_vote_with at hW0
  obtain ⟨g', hg', hW0⟩ := NoRaise.DRE.of_bind_ok hW0
  have eg : g' = g := Except.ok.inj (hg'.symm.trans hg)
  subst eg
  have hW := currentSGVote_contractStore st contract _ hg' g'.Q2
  show i.confirmed.map Spec.BlockId.toProof =
    some (Member.currentSGVote st.val _).root
  rw [hconf, ← Except.ok.inj hW0, Option.map_some, ← Spec.Block.toProof_root]
  show some (Spec.Protocol.currentSGVote _ { g' with Q2 := g'.Q2 }).toProof.root = _
  rw [hW]
  rfl

/-- At `Model.specDraft`, the attestation input's height fields are read off the chain state of the
    finality-gadget source the members give. -/
theorem specDraft_with_attestation_input_id_fields : ∀ (contract : (Model.specDraft (V := V)).Contract) (E : DecoupledConsensusModel.Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig) (nd : DecoupledConsensusModel.Protocol.Node V) (st : (Model.specDraft (V := V)).HS)
    (I : Protocol.AttestationInput V) (hI : (Model.specDraft (V := V)).with_attestation_input contract E hc nd st id ⇢ I)
    (A2 : Option (Block V)) (hA2 : (Model.specDraft (V := V)).grade2_block_with contract E hc st (((Model.specDraft (V := V)).round_of hc st.toFG.toSG.toGoldfishStore.s)) ⇢ A2)
    (F : Option (Block V)) (hF : (Model.specDraft (V := V)).fg_source_with contract E hc st (((Model.specDraft (V := V)).round_of hc st.toFG.toSG.toGoldfishStore.s)) A2 ⇢ F),
    I.fields = Option.map (fun q ↦ ((st.toFG.σ q).h, (st.toFG.σ q).T_h.root, (st.toFG.σ q).nj)) F := by
  intro contract E hc nd st I hI A2 hA2 F hF
  obtain ⟨i, hi, rfl⟩ := except_map_eq_ok ((returns_successOutcomes _ _).1 hI)
  rw [round_of_toSpec E] at hA2 hF
  exact attestation_input_fields_image st hi hA2 hF

/-- At `Model.specDraft`, the round action's height pair is encoded from the chain state of the
    members' source and the height pair the signing record gives for it. -/
theorem specDraft_named_round_action_height_pair : ∀ (contract : (Model.specDraft (V := V)).Contract) (E : DecoupledConsensusModel.Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig) (nd : DecoupledConsensusModel.Protocol.Node V) (st : (Model.specDraft (V := V)).HS) (record : (Model.specDraft (V := V)).NR)
    (A : (Model.specDraft (V := V)).NR × NamedAttestation V) (hA : (Model.specDraft (V := V)).round_action_with contract E hc nd st record ⇢ A)
    (A2 : Option (Block V)) (hA2 : (Model.specDraft (V := V)).grade2_block_with contract E hc st ((Model.specDraft (V := V)).round_of hc st.s) ⇢ A2)
    (F : Option (Block V)) (hF : (Model.specDraft (V := V)).fg_source_with contract E hc st ((Model.specDraft (V := V)).round_of hc st.s) A2 ⇢ F),
    A.2.height_pair =
      (Model.specDraft (V := V)).encodeHeight (F.map
        (fun Q => ((st.σ Q).h, (st.σ Q).T_h.root, (st.σ Q).nj)))
        ((Model.specDraft (V := V)).height_pair record.legacy (F.map
          (fun Q => ((st.σ Q).h, (st.σ Q).T_h.root, (st.σ Q).nj))) A.2.finality_pair) := by
  intro contract E hc nd st record A hA A2 hA2 F hF
  obtain ⟨p, hp, rfl⟩ := round_action_with_shape hA
  obtain ⟨i, hi, -, -, rfl⟩ := build_attestation_shape hp
  have hA2' : Returns (Member.grade2_block_with contract E hc st.val
      ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.val.s)) A2 := by
    rw [← round_of_toSpec E hc st]; exact hA2
  have hF' : Returns (Member.fg_source_with contract E hc st.val
      ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.val.s) A2) F := by
    rw [← round_of_toSpec E hc st]; exact hF
  have hfi := attestation_input_fields_image st hi hA2' hF'
  show (Spec.Protocol.create record i).2.height_pair.toProofNamed =
    Protocol.NamedRecord.encodeHeight (F.map _) (Member.height_pair (Member.legacy record) (F.map _)
      ((Spec.Protocol.create record i).2.finality_pair.map Spec.FinalityPair.toProof))
  rw [create_height_pair, ← NodeFacts.encodeHeight_height_pair]
  change _ = Protocol.NamedRecord.encodeHeight (F.map (fun q => ((Member.fg_σ st.val q).toProof.h,
    (Member.fg_σ st.val q).toProof.T_h.root, (Member.fg_σ st.val q).toProof.nj))) _
  rw [← hfi]
  congr 1
  unfold Member.height_pair
  rw [← toProof_height_pair]
  have hrt : ∀ x : Option (Height × BlockId × Bool),
      (ChainStateToHandlers.fieldsToSpec x).map (fun f => (f.1, f.2.1.toProof, f.2.2)) = x := by
    rintro (_ | ⟨h, e, ν⟩) <;> rfl
  have hfp : ∀ y : Option Spec.FinalityPair,
      ((y.map Spec.FinalityPair.toProof).map Spec.FinalityPair.toSpec).map
        Spec.FinalityPair.toProof = y.map Spec.FinalityPair.toProof := by
    rintro (_ | p) <;> rfl
  rw [← toProof_height_pair, hrt, hfp, hfi]
  rfl

/-- At `Model.specDraft`, the round action's finality pair is the one the signing record gives for
    the head's justified height, justified root and finalized height. -/
theorem specDraft_round_action_finality_pair_eq : ∀ (contract : (Model.specDraft (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig)
    (nd : Protocol.Node V) (st : (Model.specDraft (V := V)).HS) (record : (Model.specDraft (V := V)).NR)
    (A : (Model.specDraft (V := V)).NR × NamedAttestation V) (hA : (Model.specDraft (V := V)).round_action_with contract E hc nd st record ⇢ A)
    (res : GoldfishVote V → Bool) (hres : ∀ u, (Model.specDraft (V := V)).resolved st.T u ⇢ res u)
    (H : Block V) (hH : (Model.specDraft (V := V)).get_head_with contract E hc st (st.toFG.toSG.toGoldfishStore.pool st.s)
      ((st.toFG.toSG.toGoldfishStore.pool st.s).filter (fun u => res u = true)) st.s ⇢ H),
    A.2.finality_pair =
      (Model.specDraft (V := V)).finality_pair record.legacy (st.σ H).h_j (st.σ H).J.root (st.σ H).h_F := by
  intro contract E hc nd st record A hA res hres H hH
  obtain ⟨p, hp, rfl⟩ := round_action_with_shape hA
  obtain ⟨i, hi, -, -, rfl⟩ := build_attestation_shape hp
  unfold Spec.Protocol.attestation_input at hi
  obtain ⟨A_G2, -, hi⟩ := NoRaise.DRE.of_bind_ok hi
  obtain ⟨⟨fields, h_j, J, h_F⟩, hf, hi⟩ := NoRaise.DRE.of_bind_ok hi
  obtain ⟨W, -, hi⟩ := NoRaise.DRE.of_bind_ok hi
  cases Except.ok.inj hi
  obtain ⟨S, H', hS, hH', e⟩ := get_fg_vote_with_parts hf
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl, rfl⟩ := e
  have hs : (st.s : Slot) = st.val.s := by
    simp only [Model.HS.s, Model.S.s, Model.GS.s, Model.specDraft, Member.gs_s, Member.store_s,
      Member.toHealing, Member.toFG, Member.toSG, Member.toGoldfishStore, Model.HS.toFG,
      Model.FGS.toSG, Model.SGS.toGoldfishStore, id_eq, toProof_gs_s, Spec.Store.toProof_s]
  rw [hs] at hH
  have hH2 := (returns_successOutcomes _ _).1 hH
  obtain ⟨H'', hH'', rfl⟩ := except_map_eq_ok hH2
  have ev : st.toFG.toSG.toGoldfishStore.pool st.val.s =
      (st.val.pool st.val.s).map Spec.GoldfishVote.toProofEmb := rfl
  rw [(contractStore_fields st.val contract _).1, contractStore_pool,
    (contractStore_fields st.val contract _).2.1] at hS
  rw [(contractStore_fields st.val contract _).1, contractStore_pool] at hH'
  have hT : st.T = st.val.T.image Spec.Block.toProof := by
    simp only [Model.HS.T, Model.GS.T, Model.specDraft, Member.gs_T, Member.toFG, Member.toSG,
      Member.toGoldfishStore, Model.HS.toFG, Model.FGS.toSG, Model.SGS.toGoldfishStore, id_eq,
      toProof_gs_T]
  have hres' : ∀ u, (Model.specDraft (V := V)).resolved (st.val.T.image Spec.Block.toProof) u ⇢ res u := by
    rw [← hT]; exact hres
  have hsup := support_filter_eq st st.val.s res hres' hS
  rw [ev, hsup, map_toProofEmb_voteToSpec] at hH''
  have eH : H'' = H' := Except.ok.inj (hH''.symm.trans hH')
  subst eH
  have hfix := get_head_with_contractStore_fixed st contract _ hH'
  show (Spec.Protocol.finality_pair record (st.val.σ H'').h_j (st.val.σ H'').J.root
      (st.val.σ H'').h_F).map Spec.FinalityPair.toProof =
    (Spec.Protocol.finality_pair (Member.legacy record)
      (st.val.σ (st.val.blockOfImage H''.toProof)).toProof.h_j
      (Spec.BlockId.toSpec (st.val.σ (st.val.blockOfImage H''.toProof)).toProof.J.root)
      (st.val.σ (st.val.blockOfImage H''.toProof)).toProof.h_F).map Spec.FinalityPair.toProof
  rw [hfix]
  simp [Spec.Protocol.ChainState.toProof, Spec.Block.toProof_root]
  rfl

/-- At `Model.specDraft`, when the record's target, timeout and lock at the head's justified height
    allow it and the head's finalized height is less than it, the round action names the head's
    justified pair. -/
theorem specDraft_namedRoundAction_finality_pair_of_record_guard : ∀ (contract : (Model.specDraft (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig)
    (nd : Protocol.Node V) (st : (Model.specDraft (V := V)).HS) (record : (Model.specDraft (V := V)).NR) {h : Height} {J : BlockId}
    (htarget : record.legacy.target h = none ∨ record.legacy.target h = some J)
    (htimeout : record.legacy.timeout h = false)
    (hlock : record.legacy.lock h = none ∨ record.legacy.lock h = some J)
    (A : (Model.specDraft (V := V)).NR × NamedAttestation V) (hA : (Model.specDraft (V := V)).round_action_with contract E hc nd st record ⇢ A)
    (res : GoldfishVote V → Bool) (hres : ∀ u, (Model.specDraft (V := V)).resolved st.T u ⇢ res u)
    (H : Block V) (hH : (Model.specDraft (V := V)).get_head_with contract E hc st (st.toFG.toSG.toGoldfishStore.pool st.s)
      ((st.toFG.toSG.toGoldfishStore.pool st.s).filter (fun u => res u = true)) st.s ⇢ H)
    (hhj : (st.σ H).h_j = h) (hJ : (st.σ H).J.root = J) (hF : (st.σ H).h_F < h),
    A.2.finality_pair = some ⟨h, J⟩ := by
  intro contract E hc nd st record h J htarget htimeout hlock A hA res hres H hH hhj hJ hF
  rw [specDraft_round_action_finality_pair_eq contract E hc nd st record A hA res hres H hH, hhj, hJ]
  show (Spec.Protocol.finality_pair (Member.legacy record) h (Spec.BlockId.toSpec J)
    _).map Spec.FinalityPair.toProof = _
  rw [← toProof_finality_pair, Spec.BlockId.toProof_toSpec]
  have hguard : ((Spec.SigningHistory.toProof (Member.legacy record)).legacy.target h = none ∨
      (Spec.SigningHistory.toProof (Member.legacy record)).legacy.target h = some J) ∧
      (Spec.SigningHistory.toProof (Member.legacy record)).legacy.timeout h = false ∧
      ((Spec.SigningHistory.toProof (Member.legacy record)).legacy.lock h = none ∨
        (Spec.SigningHistory.toProof (Member.legacy record)).legacy.lock h = some J) :=
    ⟨htarget, htimeout, hlock⟩
  simp only [DecoupledConsensusModel.Protocol.finality_pair, if_pos hF, if_pos hguard]

end SpecDraftRecord.DutiesFacts


namespace DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-- `Model.specDraft` satisfies `DutiesRunFacts`, which has no field. -/
theorem Model.specDraft_runFacts_duties : DutiesRunFacts (Model.specDraft (V := V)) where

end DecoupledConsensusModel.Sts.Record
