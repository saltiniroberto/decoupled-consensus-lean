import Proofs.Instance.Model
import Proofs.Instance.Facts.Handlers
import Proofs.Instance.Facts.Node
import Proofs.Instance.Equalities.ForkChoiceImages
import Proofs.Vocabulary.ModelVocabularyFacts

/-!
# Store-reading fields of the facts structures at `Model.spec`

Proofs of the fields of `StoreFacts` and `HandlersFacts` that read the store type, at the model
`Model.spec`, one theorem `spec_<x>` per field `<x>`. The store type is the subtype
`OkStore V`: stamped, of distinct roots, parent-closed and holding its finalized block.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## `StoreFacts`: the resolution times -/

namespace SpecRecord.StoreFacts

open DecoupledConsensusModel DecoupledConsensusModel.Execution DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

omit [Fintype V] [Inhabited V] in
/-- The resolution times of a store's image read as a Goldfish store are the resolution times of the
    image. -/
theorem gs_tau_image (st : Spec.Store V) :
    DecoupledConsensusModel.Protocol.GoldfishStore.tau
        st.toProof.toHealing.toFG.toSG.toGoldfishStore =
      DecoupledConsensusModel.Protocol.Store.tau st.toProof := by
  unfold DecoupledConsensusModel.Protocol.Store.toHealing
    DecoupledConsensusModel.Protocol.GoldfishStore.tau DecoupledConsensusModel.Protocol.Store.tau
  rfl

/-- The member `store_tau` of `Model.spec` at a store `st` of the instance has one outcome,
    `Protocol.Store.tau` of the store's image. -/
theorem spec_store_tau_eq (st : OkStore V) :
    (Model.spec (V := V)).store_tau st =
      (pure (DecoupledConsensusModel.Protocol.Store.tau st.val.toProof) :
        DC.NDRE (TimestampMap (GoldfishVote V))) := by
  obtain ⟨hst, hT, -, -⟩ := st.property
  have hval : ∀ u : GoldfishVote V,
      (st.val.timestamp_vote (Spec.GoldfishVote.toSpec u)).isSome →
        st.val.tau (Spec.GoldfishVote.toSpec u) =
          .ok (DecoupledConsensusModel.Protocol.Store.tau st.val.toProof u) := by
    intro u hu
    obtain ⟨o, ho⟩ := NoRaise.tau_ok hT hst.1 (Option.isSome_iff_ne_none.1 hu)
    rw [ho, ForkChoiceImages.tau_toProof_of_ok st _ ho, Spec.GoldfishVote.toProof_toSpec,
      gs_tau_image]
  have hnone : ∀ u : GoldfishVote V,
      st.val.timestamp_vote (Spec.GoldfishVote.toSpec u) = none →
        DecoupledConsensusModel.Protocol.Store.tau st.val.toProof u = none := by
    intro u hu
    have hu' : st.val.toProof.timestamp_vote u = none := hu
    unfold DecoupledConsensusModel.Protocol.Store.tau DecoupledConsensusModel.Protocol.resolution_time
    split
    · rfl
    · split
      · rw [hu']; cases st.val.toProof.timestamp_block _ <;> unfold DecoupledConsensusModel.occurrenceMax <;> rfl
      · rfl
  apply ExceptT.ext
  apply Set.ext
  intro x
  change x ∈ {x | ∃ f : TimestampMap (GoldfishVote V), _ ∧ _ ∧ x = .ok f} ↔ x = .ok _
  constructor
  · rintro ⟨f, h1, h2, rfl⟩
    congr 1
    funext u
    cases hu : st.val.timestamp_vote (Spec.GoldfishVote.toSpec u) with
    | none => rw [h2 u hu, hnone u hu]
    | some a =>
      have hs : (st.val.timestamp_vote (Spec.GoldfishVote.toSpec u)).isSome := by
        rw [hu]; rfl
      have := (h1 u hs).symm.trans (hval u hs)
      exact Except.ok.inj this
  · rintro rfl
    exact ⟨_, fun u hu => hval u hu, fun u hu => hnone u hu, rfl⟩

/-- An outcome `tm` of the resolution times of `Model.spec` at `st` is `Protocol.Store.tau` of
    the store's image. -/
theorem tm_eq_of_returns (st : OkStore V) {tm : TimestampMap (GoldfishVote V)}
    (htm : (Model.spec (V := V)).store_tau st ⇢ tm) :
    tm = DecoupledConsensusModel.Protocol.Store.tau st.val.toProof := by
  rw [spec_store_tau_eq] at htm
  exact (returns_pure _ _).1 htm

/-- The field `tau_eq_of_fields` of `StoreFacts` at `Model.spec`: two stores with the same
    block tree, the same block stamps and the same vote stamps have the same resolution times. -/
theorem spec_tau_eq_of_fields : ∀ {st st' : (Model.spec (V := V)).S} (hT : st.T = st'.T)
    (hb : st.timestamp_block = st'.timestamp_block)
    (hv : st.timestamp_vote = st'.timestamp_vote), st.tau = st'.tau := by
  intro st st' hT hb hv
  show (Model.spec (V := V)).store_tau st = (Model.spec (V := V)).store_tau st'
  rw [spec_store_tau_eq, spec_store_tau_eq]
  exact (Model.vocabulary_facts_store (V := V)).tau_eq_of_fields
    (st := st.val.toProof) (st' := st'.val.toProof) hT hb hv

/-- The field `store_with_t_s_timestamp_vote` of `StoreFacts` at `Model.spec`: writing the
    clock and the slot of a store keeps its vote stamps. -/
theorem spec_store_with_t_s_timestamp_vote : ∀ (st : (Model.spec (V := V)).S) (t : Time) (s : Slot),
    ((Model.spec (V := V)).store_with_t_s st t s).timestamp_vote = st.timestamp_vote :=
  fun _ _ _ => rfl

/-- The field `store_with_σ_T_timestamp_block_h_max` of `StoreFacts` at `Model.spec`: writing
    the chain states, the tree and the block stamps of a store keeps its largest seen height. -/
theorem spec_store_with_σ_T_timestamp_block_h_max : ∀ (st : (Model.spec (V := V)).S) (σ' : Block V → (Model.spec (V := V)).CS)
    (T' : Finset (Block V)) (τ' : TimestampMap (Block V)),
    ((Model.spec (V := V)).store_with_σ_T_timestamp_block st σ' T' τ').h_max = st.h_max := by
  intro st σ' T' τ'
  show Member.store_h_max (OkMember.store_with_σ_T_timestamp_block st σ' T' τ').val =
    Member.store_h_max st.val
  unfold OkMember.store_with_σ_T_timestamp_block
  split <;> rfl

/-- The field `store_with_σ_T_timestamp_block_J` of `StoreFacts` at `Model.spec`: writing the
    chain states, the tree and the block stamps of a store keeps its justified block. -/
theorem spec_store_with_σ_T_timestamp_block_J : ∀ (st : (Model.spec (V := V)).S) (σ' : Block V → (Model.spec (V := V)).CS) (T' : Finset (Block V))
    (τ' : TimestampMap (Block V)), ((Model.spec (V := V)).store_with_σ_T_timestamp_block st σ' T' τ').J = st.J := by
  intro st σ' T' τ'
  show Member.store_J (OkMember.store_with_σ_T_timestamp_block st σ' T' τ').val =
    Member.store_J st.val
  unfold OkMember.store_with_σ_T_timestamp_block
  split <;> rfl

/-- The field `store_with_σ_T_timestamp_block_h_j` of `StoreFacts` at `Model.spec`: writing the
    chain states, the tree and the block stamps of a store keeps its justified height. -/
theorem spec_store_with_σ_T_timestamp_block_h_j : ∀ (st : (Model.spec (V := V)).S) (σ' : Block V → (Model.spec (V := V)).CS)
    (T' : Finset (Block V)) (τ' : TimestampMap (Block V)),
    ((Model.spec (V := V)).store_with_σ_T_timestamp_block st σ' T' τ').h_j = st.h_j := by
  intro st σ' T' τ'
  show Member.store_h_j (OkMember.store_with_σ_T_timestamp_block st σ' T' τ').val =
    Member.store_h_j st.val
  unfold OkMember.store_with_σ_T_timestamp_block
  split <;> rfl

/-- The field `head_slot_le_of_tau` of `StoreFacts` at `Model.spec`: if the tree holds the head
    block `H` of the vote `u`, and `u` resolves before `Γ`, then `H`'s slot is at most `u`'s. -/
theorem spec_head_slot_le_of_tau : ∀ (st : (Model.spec (V := V)).S) {Γ : Time} {u : GoldfishVote V} {H : Block V}
    (hfind : Block.find? st.T u.head = some H)
    (tm : TimestampMap (GoldfishVote V)) (htm : st.tau ⇢ tm)
    (h : stampedBefore tm Γ u = true),
    H.slot ≤ u.slot := by
  intro st Γ u H hfind tm htm h
  obtain rfl := tm_eq_of_returns st htm
  exact (Model.vocabulary_facts_store (V := V)).head_slot_le_of_tau st.val.toProof hfind _
    ((returns_pure _ _).2 rfl) h

/-- The field `stampedBefore_block_of_tau` of `StoreFacts` at `Model.spec`: if the tree holds
    the head block `H` of the vote `u`, and `u` resolves before `Γ`, then `H` was received before
    `Γ`. -/
theorem spec_stampedBefore_block_of_tau : ∀ (st : (Model.spec (V := V)).S) {Γ : Time} {u : GoldfishVote V} {H : Block V}
    (hfind : Block.find? st.T u.head = some H)
    (tm : TimestampMap (GoldfishVote V)) (htm : st.tau ⇢ tm)
    (h : stampedBefore tm Γ u = true),
    stampedBefore st.timestamp_block Γ H = true := by
  intro st Γ u H hfind tm htm h
  obtain rfl := tm_eq_of_returns st htm
  exact (Model.vocabulary_facts_store (V := V)).stampedBefore_block_of_tau st.val.toProof hfind _
    ((returns_pure _ _).2 rfl) h

/-- The field `stampedBefore_store_tau_of` of `StoreFacts` at `Model.spec`: if the tree holds
    the head block `H` of the vote `u`, of a slot at most `u`'s, and both `u` and `H` were received
    before `Γ`, then `u` resolves before `Γ`. -/
theorem spec_stampedBefore_store_tau_of : ∀ (st : (Model.spec (V := V)).S) {Γ : Time} {u : GoldfishVote V} {H : Block V}
    (hfind : Block.find? st.T u.head = some H) (hslot : H.slot ≤ u.slot)
    (hv : stampedBefore st.timestamp_vote Γ u = true)
    (hH : stampedBefore st.timestamp_block Γ H = true)
    (tm : TimestampMap (GoldfishVote V)) (htm : st.tau ⇢ tm),
    stampedBefore tm Γ u = true := by
  intro st Γ u H hfind hslot hv hH tm htm
  obtain rfl := tm_eq_of_returns st htm
  exact (Model.vocabulary_facts_store (V := V)).stampedBefore_store_tau_of st.val.toProof hfind
    hslot hv hH _ ((returns_pure _ _).2 rfl)

/-- The field `stampedBefore_tau_of` of `StoreFacts` at `Model.spec`: if the tree of the
    Goldfish store `gs` holds the head block `H` of the vote `u`, of a slot at most `u`'s, and both
    `u` and `H` were received before `Γ`, then `u` resolves before `Γ`. -/
theorem spec_stampedBefore_tau_of : ∀ (gs : (Model.spec (V := V)).GS) {Γ : Time} {u : GoldfishVote V} {H : Block V}
    (hfind : Block.find? gs.T u.head = some H) (hslot : H.slot ≤ u.slot)
    (hv : stampedBefore gs.timestamp_vote Γ u = true)
    (hH : stampedBefore gs.timestamp_block Γ H = true)
    (tm : TimestampMap (GoldfishVote V)) (htm : gs.tau ⇢ tm),
    stampedBefore tm Γ u = true := by
  intro gs Γ u H hfind hslot hv hH tm htm
  have htm' := tm_eq_of_returns gs htm
  exact (Model.vocabulary_facts_store (V := V)).stampedBefore_tau_of
    gs.val.toProof.toHealing.toFG.toSG.toGoldfishStore hfind hslot hv hH _
    ((returns_pure _ _).2 (htm'.trans (gs_tau_image _).symm))

/-- The field `stampedBefore_vote_of_tau` of `StoreFacts` at `Model.spec`: a vote that resolves
    before `Γ` was received before `Γ`. -/
theorem spec_stampedBefore_vote_of_tau : ∀ (st : (Model.spec (V := V)).S) {Γ : Time} {u : GoldfishVote V}
    (tm : TimestampMap (GoldfishVote V)) (htm : st.tau ⇢ tm)
    (h : stampedBefore tm Γ u = true),
    stampedBefore st.timestamp_vote Γ u = true := by
  intro st Γ u tm htm h
  obtain rfl := tm_eq_of_returns st htm
  exact (Model.vocabulary_facts_store (V := V)).stampedBefore_vote_of_tau st.val.toProof _
    ((returns_pure _ _).2 rfl) h

/-- The field `tau_eq_max` of `StoreFacts` at `Model.spec`: if the tree holds the head block
    `X` of the vote `u`, of a slot at most `u`'s, the vote was received at `τ` and the block at `σ`,
    then `u` resolves at the later of the two. -/
theorem spec_tau_eq_max : ∀ (st : (Model.spec (V := V)).S) {u : GoldfishVote V} {X : Block V}
    (hX : Block.find? st.T u.head = some X) (hXs : X.slot ≤ u.slot) {τ σ : Stamp}
    (hτ : st.timestamp_vote u = some τ) (hσ : st.timestamp_block X = some σ)
    (tm : TimestampMap (GoldfishVote V)) (htm : st.tau ⇢ tm),
    tm u = some (max τ σ) := by
  intro st u X hX hXs τ σ hτ hσ tm htm
  obtain rfl := tm_eq_of_returns st htm
  exact (Model.vocabulary_facts_store (V := V)).tau_eq_max st.val.toProof hX hXs hτ hσ _
    ((returns_pure _ _).2 rfl)

/-- The field `tau_eq_max_gf` of `StoreFacts` at `Model.spec`: if the tree of the Goldfish
    store `gs` holds the head block `X` of the vote `u`, of a slot at most `u`'s, the vote was
    received at `τ` and the block at `σ`, then `u` resolves at the later of the two. -/
theorem spec_tau_eq_max_gf : ∀ (gs : (Model.spec (V := V)).GS) {u : GoldfishVote V} {X : Block V}
    (hX : Block.find? gs.T u.head = some X) (hXs : X.slot ≤ u.slot) {τ σ : Stamp}
    (hτ : gs.timestamp_vote u = some τ) (hσ : gs.timestamp_block X = some σ)
    (tm : TimestampMap (GoldfishVote V)) (htm : gs.tau ⇢ tm),
    tm u = some (max τ σ) := by
  intro gs u X hX hXs τ σ hτ hσ tm htm
  have htm' := tm_eq_of_returns gs htm
  exact (Model.vocabulary_facts_store (V := V)).tau_eq_max_gf
    gs.val.toProof.toHealing.toFG.toSG.toGoldfishStore hX hXs hτ hσ _
    ((returns_pure _ _).2 (htm'.trans (gs_tau_image _).symm))

end SpecRecord.StoreFacts

/-! ## `HandlersFacts`: the fields read off the store's members -/

namespace SpecRecord.HandlersFacts

open DecoupledConsensusModel
open DecoupledConsensusModel.Sts
open DecoupledConsensusModel.Sts.Record
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol (ChainState HeightConfig HealConfig HeightId)
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-- Unfolds the readers and members of `Model.spec` into reads of the images and rewrites each
    member with its `image_` lemma, in the goal and in every hypothesis. -/
local macro "unfold_spec" : tactic => `(tactic| simp only [Model.spec, Model.specBase, Model.S.t,
  Model.S.s, Model.S.T, Model.S.timestamp_block, Model.S.timestamp_vote, Model.S.timestamp_sg_vote,
  Model.S.σ, Model.S.gf_votes, Model.S.sg_votes, Model.S.F, Model.S.J, Model.S.h_j, Model.S.h_max,
  Model.S.live_confirmed, Model.S.latest_confirmed, Model.S.latest_stable, Model.NS.core,
  Model.NS.bodies, Model.NS.sg_rows, Model.N.st, Model.S.toHealing, Model.S.pool, Model.S.sg_pool,
  Model.NS.setClock, Model.NS.process_block_core, Model.NS.commitBlock,
  ChainStateModel.CS.h, ChainStateModel.CS.J, ChainStateModel.CS.h_j, ChainStateModel.CS.F,
  ChainStateModel.CS.h_F,
  Member.store_t, Member.store_s, Member.store_T, Member.store_timestamp_block,
  Member.store_timestamp_vote, Member.store_timestamp_sg_vote, Member.store_gf_votes,
  Member.store_sg_votes, Member.store_F, Member.store_J, Member.store_h_j, Member.store_h_max,
  Member.store_live_confirmed, Member.store_latest_confirmed, Member.store_latest_stable,
  Member.bodies, Member.sg_rows, Member.h, Member.J, Member.h_j, Member.F, Member.h_F,
  image_core, image_on_sg_vote, image_on_goldfish_vote_checked, image_on_goldfish_vote,
  image_admit_row, image_admit_rows,
  image_ns_setClock, image_ns_initial, image_store_pool, image_store_sg_pool, image_round_votes,
  image_sgVote, image_advance_confirmed, image_floor_on_stable,
  image_carried_attestations_admissible, image_round_of,
  image_admit_carried, image_equivocates] at *)

/-- The field `ns_with_core_core` of `HandlersFacts` at `Model.spec`: the store part of the
    named store `st` with its store part set to `c` is `c`. -/
theorem spec_ns_with_core_core : ∀ (st : (Model.spec (V := V)).NS) (c : (Model.spec (V := V)).S),
    ((Model.spec (V := V)).ns_with_core st c).core = c :=
  fun _ _ => rfl

/-- The field `on_block_checked_using_store_part` of `HandlersFacts` at `Model.spec`: setting a
    named store's store part to the result of the checked block handler, then reading the store part
    back, gives that result. -/
theorem spec_on_block_checked_using_store_part : ∀ (E : Env V) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) (before : (Model.spec (V := V)).NS) (B : NamedBlock V),
    ((Model.spec (V := V)).ns_with_core before
        ((Model.spec (V := V)).on_block_checked_using
          (fun current => (Model.spec (V := V)).on_block_using E current B.erase
            (fun ps => (Model.spec (V := V)).named_transition E cfg ps B)) hc before.core B.erase)).core =
      (Model.spec (V := V)).on_block_checked_using
        (fun current => (Model.spec (V := V)).on_block_using E current B.erase
          (fun ps => (Model.spec (V := V)).named_transition E cfg ps B)) hc before.core B.erase :=
  fun _ _ _ _ _ => rfl

/-- The field `setClock_core_eq_store_with_t_s` of `HandlersFacts` at `Model.spec`: setting the
    clock of the named store `st` to `t` writes the clock `t` and the slot `E.slotOf t` into its
    store part. -/
theorem spec_setClock_core_eq_store_with_t_s : ∀ (E : Env V) (st : (Model.spec (V := V)).NS) (t : Time),
    ((Model.spec (V := V)).ns_setClock E st t).core =
      (Model.spec (V := V)).store_with_t_s st.core t (E.slotOf t) := by
  intro E st t
  apply Subtype.ext
  show Member.ns_setClock E st.val t = Member.store_with_t_s st.val t (E.slotOf t)
  unfold Member.ns_setClock Member.store_with_t_s DecoupledConsensusModel.Env.slotOf
    DecoupledConsensusModel.slotOfTime
  rfl

/-- The field `coherent_clock` of `HandlersFacts` at `Model.spec`: setting the clock of a
    coherent named store keeps it coherent. -/
theorem spec_coherent_clock : ∀ (E : Env V) (cfg : Protocol.HeightConfig) (st : (Model.spec (V := V)).NS) (t : Time),
    Restated.Vocabulary.Proofs.NamedStore.Coherent (Model.spec (V := V)) E cfg st →
    Restated.Vocabulary.Proofs.NamedStore.Coherent (Model.spec (V := V)) E cfg ((Model.spec (V := V)).ns_setClock E st t) :=
  fun _ _ _ _ h => h

/-- The field `treeSlotBounded_init` of `HandlersFacts` at `Model.spec`: every block of the
    initial store's tree has a slot at most the initial store's slot. -/
theorem spec_treeSlotBounded_init : ∀ B : Block V, B ∈ ((Model.spec (V := V)).ns_initial : (Model.spec (V := V)).NS).core.T → B.slot ≤ ((Model.spec (V := V)).ns_initial : (Model.spec (V := V)).NS).core.s := by
  intro B hB
  unfold_spec
  exact (Model.vocabulary_facts_handlers (V := V)).treeSlotBounded_init B hB

/-- The field `goldfish_vote_with_T` of `HandlersFacts` at `Model.spec`: the Goldfish vote duty
    keeps the store's tree. -/
theorem spec_goldfish_vote_with_T : ∀ (contract : (Model.spec (V := V)).Contract) (E : Env V) (hc : HealConfig) (nd : Protocol.Node V) (st : (Model.spec (V := V)).S) (out : (Model.spec (V := V)).S × Option (GoldfishVote V)), (Model.spec (V := V)).goldfish_vote_with contract E hc nd st ⇢ out → out.1.T = st.T := by
  intro contract E hc nd st out hout
  replace hout : Returns (Member.goldfish_vote_with contract E hc nd st.val) (out.1.val, out.2) := hout
  unfold Member.goldfish_vote_with at hout
  rw [returns_successOutcomes] at hout
  obtain ⟨o, ho, e⟩ := ContractImages.except_map_eq_ok hout
  obtain ⟨x, y, hx⟩ := ContractImages.goldfish_vote_writes ho
  have e1 := congrArg Prod.fst e
  show out.1.val.toProof.T = st.val.toProof.T
  simp only at e1
  rw [← e1, hx]
  rfl

/-- The field `goldfish_vote_with_snd` of `HandlersFacts` at `Model.spec`: a vote the Goldfish
    vote duty sends is signed by the node's validator, at the store's slot. -/
theorem spec_goldfish_vote_with_snd : ∀ (contract : (Model.spec (V := V)).Contract) (E : Env V) (hc : HealConfig) (nd : Protocol.Node V) (st : (Model.spec (V := V)).S) {u : GoldfishVote V} (out : (Model.spec (V := V)).S × Option (GoldfishVote V)) (hout : (Model.spec (V := V)).goldfish_vote_with contract E hc nd st ⇢ out) (h : out.2 = some u), u.val_index = nd.val_index ∧ u.slot = st.s := by
  intro contract E hc nd st u out hout h
  replace hout : Returns (Member.goldfish_vote_with contract E hc nd st.val) (out.1.val, out.2) := hout
  unfold Member.goldfish_vote_with at hout
  rw [returns_successOutcomes] at hout
  obtain ⟨o, ho, e⟩ := ContractImages.except_map_eq_ok hout
  obtain ⟨_, _, _, _, _, _, _, _, hsent⟩ := ContractImages.goldfish_vote_sent ho
  have e2 := congrArg Prod.snd e
  simp only at e2
  rw [← e2] at h
  rcases hsent with ⟨-, hl⟩ | ⟨-, hl⟩
  · rw [hl] at h
    simp [ChainStateToHandlers.sentGoldfishVote, Spec.GoldfishVote.toProof] at h
    subst h
    exact ⟨rfl, rfl⟩
  · rw [hl] at h
    simp [ChainStateToHandlers.sentGoldfishVote] at h

/-- The field `blockStamps_init` of `HandlersFacts` at `Model.spec`: in the initial store every
    block of the tree is stamped, every stamped block is in the tree, and every stamp is at most the
    clock. -/
theorem spec_blockStamps_init : ((∀ B : Block V, B ∈ ((Model.spec (V := V)).ns_initial : (Model.spec (V := V)).NS).core.T → (((Model.spec (V := V)).ns_initial : (Model.spec (V := V)).NS).core.timestamp_block B).isSome = true) ∧
      (∀ B : Block V, (((Model.spec (V := V)).ns_initial : (Model.spec (V := V)).NS).core.timestamp_block B).isSome = true → B ∈ ((Model.spec (V := V)).ns_initial : (Model.spec (V := V)).NS).core.T) ∧
      (∀ (B : Block V) (c : Stamp), ((Model.spec (V := V)).ns_initial : (Model.spec (V := V)).NS).core.timestamp_block B = some c →
        c ≤ (((Model.spec (V := V)).ns_initial : (Model.spec (V := V)).NS).core.t : Stamp))) := by
  unfold_spec
  exact (Model.vocabulary_facts_handlers (V := V)).blockStamps_init

/-- The field `poolStamps_initial` of `HandlersFacts` at `Model.spec`: the initial store meets
    `PoolStamps`. -/
theorem spec_poolStamps_initial : Restated.Vocabulary.Protocol.PoolStamps (Model.spec (V := V)) ((Model.spec (V := V)).ns_initial : (Model.spec (V := V)).NS).core := by
  have h := (Model.vocabulary_facts_handlers (V := V)).poolStamps_initial
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k u hu
    unfold_spec
    exact h.slot k u hu
  · intro k u hu
    unfold_spec
    exact h.stamped k u hu
  · intro u hu
    unfold_spec
    exact h.pooled u hu
  · intro u c hu
    unfold_spec
    exact h.bounded u c hu

/-- If the store `st` of the instance meets `PoolStamps` at `Model.spec`, its image
    `st.val.toProof` meets `PoolStamps` at `Model.vocabulary`. -/
theorem poolStamps_image (st : (Model.spec (V := V)).S)
    (h : Restated.Vocabulary.Protocol.PoolStamps (Model.spec (V := V)) st) :
    Restated.Vocabulary.Protocol.PoolStamps (Model.vocabulary (V := V)) st.val.toProof :=
  ⟨h.slot, h.stamped, h.pooled, h.bounded⟩

/-- The field `on_goldfish_vote_beforeCutoff_or_equivocates` of `HandlersFacts` at
    `Model.spec`: a vote of the current or the previous slot, stored before the cutoff `Γ`
    passes, is in the pool before the cutoff, unless its validator equivocates there. -/
theorem spec_on_goldfish_vote_beforeCutoff_or_equivocates : ∀ (st : (Model.spec (V := V)).S) (u : GoldfishVote V) (Γ : Time),
    Restated.Vocabulary.Protocol.PoolStamps (Model.spec (V := V)) st →
    ¬ u.slot < st.s - 1 → ¬ st.s < u.slot → st.t < Γ →
    u ∈ _root_.DecoupledConsensusModel.beforeCutoff ((Model.spec (V := V)).on_goldfish_vote st u).timestamp_vote Γ
        ((Model.spec (V := V)).store_pool ((Model.spec (V := V)).on_goldfish_vote st u) u.slot) ∨
      (Model.spec (V := V)).equivocates
        (_root_.DecoupledConsensusModel.beforeCutoff ((Model.spec (V := V)).on_goldfish_vote st u).timestamp_vote Γ
          ((Model.spec (V := V)).store_pool ((Model.spec (V := V)).on_goldfish_vote st u) u.slot)) u.val_index = true := by
  intro st u Γ h h1 h2 h3
  have := (Model.vocabulary_facts_handlers (V := V)).on_goldfish_vote_beforeCutoff_or_equivocates
    st.val.toProof u Γ (poolStamps_image st h) h1 h2 h3
  unfold_spec
  exact this

/-- A named store of the instance that is `Coherent` at `Model.spec` has a named image that is
    `Coherent` at `Model.vocabulary`. -/
theorem coherent_image (E : Env V) (cfg : HeightConfig) (st : (Model.spec (V := V)).NS)
    (h : Restated.Vocabulary.Proofs.NamedStore.Coherent (Model.spec (V := V)) E cfg st) :
    Restated.Vocabulary.Proofs.NamedStore.Coherent (Model.vocabulary (V := V)) E cfg
      st.val.toProofNamed := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1, h2, h3, h4, fun B hB => ?_⟩
  show (Member.store_σ st.val B.erase).toProof = Protocol.derive_named E cfg B
  rw [← HandlersRunFacts.image_derive_named]
  exact congrArg Spec.Protocol.ChainState.toProof (h5 B hB)

/-- The field `sgArrival_rows_data` of `HandlersFacts` at `Model.spec`: if the clock and every
    row's stamp of a coherent named store are within `bound`, they still are after the list `rows`
    is admitted, and every row stays of its round. -/
theorem spec_sgArrival_rows_data : ∀ (S : Setup V) (bound : Time) (st : (Model.spec (V := V)).NS) (rows : List (NamedAttestation V)),
    Restated.Vocabulary.Proofs.NamedStore.Coherent (Model.spec (V := V)) S.E S.cfg st →
    (st.core.t ≤ bound ∧ ∀ k (a : NamedAttestation V), a ∈ st.sg_rows k →
      a.round = k ∧ ∃ stamp : Time, stamp ≤ bound ∧
        st.core.timestamp_sg_vote ((Model.spec (V := V)).sgVote a.erase) = some (stamp : Stamp)) →
    (((Model.spec (V := V)).admit_rows S.hc st rows).core.t ≤ bound ∧
      ∀ k (a : NamedAttestation V), a ∈ ((Model.spec (V := V)).admit_rows S.hc st rows).sg_rows k →
        a.round = k ∧ ∃ stamp : Time, stamp ≤ bound ∧
          ((Model.spec (V := V)).admit_rows S.hc st rows).core.timestamp_sg_vote ((Model.spec (V := V)).sgVote a.erase) = some (stamp : Stamp)) := by
  intro S bound st rows hcoh hdata
  have hcoh' := coherent_image S.E S.cfg st hcoh
  have := (Model.vocabulary_facts_handlers (V := V)).sgArrival_rows_data S bound st.val.toProofNamed
    rows hcoh'
  unfold_spec
  exact this hdata

/-- The field `NamedAdmission_coherent_admit_rows` of `HandlersFacts` at `Model.spec`:
    admitting a list of rows into a coherent named store keeps it coherent. -/
theorem spec_NamedAdmission_coherent_admit_rows : ∀ (E : Env V) (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (st : (Model.spec (V := V)).NS)
    (rows : List (NamedAttestation V)),
    Restated.Vocabulary.Proofs.NamedStore.Coherent (Model.spec (V := V)) E cfg st →
    Restated.Vocabulary.Proofs.NamedStore.Coherent (Model.spec (V := V)) E cfg ((Model.spec (V := V)).admit_rows hc st rows) := by
  intro E hc cfg st rows h
  obtain ⟨at', ts, he⟩ := SpecRecord.NodeFacts.admit_attestations_frame
    (Spec.Config.toSpec (ChainStateToHandlers.unreadEnv (V := V)) hc unreadHeightConfig) st.val
    (rows.map Spec.Attestation.toSpecNamed)
  obtain ⟨h1, h2, h3, -, h5⟩ := h
  set X := Member.admit_rows hc st.val rows with hX
  have hval : X = { st.val with attestations := at', timestamp_sg_vote := ts } := he
  have hb : Member.bodies X = Member.bodies st.val := by rw [hval]; rfl
  have hT : Member.store_T X = Member.store_T st.val := by rw [hval]; rfl
  have hσ : Member.store_σ X = Member.store_σ st.val := by rw [hval]; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show Member.store_T X = (Member.bodies X).image NamedBlock.erase
    rw [hT, hb]; exact h1
  · show ∀ A ∈ Member.bodies X, ∀ B ∈ Member.bodies X, A.erase = B.erase → A = B
    rw [hb]; exact h2
  · show NamedBlock.genesis ∈ Member.bodies X ∧ ∀ B ∈ Member.bodies X, B.parent ∈ Member.bodies X
    rw [hb]; exact h3
  · intro r
    show (X.attestations r).map Spec.Attestation.toProof =
      ((X.attestations r).map Spec.Attestation.toProofNamed).map NamedAttestation.erase
    rw [List.map_map, Spec.Attestation.erase_comp_toProofNamed]
  · show ∀ B ∈ Member.bodies X, Member.store_σ X B.erase = Member.derive_named E cfg B
    rw [hb, hσ]; exact h5

/-- The field `Sts_voter_filtered_block_tree_subset` of `HandlersFacts` at `Model.spec`: the
    voter's filtered tree is a subset of the store's tree. -/
theorem spec_Sts_voter_filtered_block_tree_subset : ∀ (E : Env V) (st : (Model.spec (V := V)).S) (s : Slot) (X : Finset (Block V)), (Model.spec (V := V)).voter_filtered_block_tree E st s ⇢ X → X ⊆ st.T := by
  intro E st s X hX
  replace hX : Returns (Member.voter_filtered_block_tree E st.val s) X := hX
  unfold Member.voter_filtered_block_tree at hX
  rw [returns_successOutcomes] at hX
  obtain ⟨T', hT', rfl⟩ := ContractImages.except_map_eq_ok hX
  exact Finset.image_subset_image
    (ContractImages.voter_filtered_block_tree_subset (st := Spec.Store.ofImage st.val) hT')

/-- The field `ModelProperties_voter_filtered_block_tree_subset` of `HandlersFacts` at
    `Model.spec`: the voter's filtered tree is a subset of the store's tree. -/
theorem spec_ModelProperties_voter_filtered_block_tree_subset : ∀ (E : Env V) (st : (Model.spec (V := V)).S) (s : Slot) (X : Finset (Block V)), (Model.spec (V := V)).voter_filtered_block_tree E st s ⇢ X → X ⊆ st.T :=
  spec_Sts_voter_filtered_block_tree_subset

/-- The field `update_confirmation_with_toHealing_F` of `HandlersFacts` at `Model.spec`: the
    confirmation update keeps the finalized block. -/
theorem spec_update_confirmation_with_toHealing_F : ∀ (contract : (Model.spec (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (st : (Model.spec (V := V)).S) (s : Slot) (st' : (Model.spec (V := V)).S), (Model.spec (V := V)).update_confirmation_with contract E hc st s ⇢ st' → ((Model.spec (V := V)).toHealing st').toFG.F = ((Model.spec (V := V)).toHealing st).toFG.F := by
  intro contract E hc st s st' h
  obtain ⟨x1, x2, x3, he⟩ := ContractImages.update_confirmation_with_shape
    (c := contract) (E := E) (hc := hc) (st := st.val) (st' := st'.val) (s := s) h
  show st'.val.F.toProof = st.val.F.toProof
  rw [he]
  show (Spec.Store.ofImage st.val).F.toProof = _
  rw [Spec.Store.ofImage_F, Spec.Store.toProof_blockOfImage]

/-- The field `update_confirmation_with_filtered` of `HandlersFacts` at `Model.spec`: the
    confirmation update keeps the filtered block tree. -/
theorem spec_update_confirmation_with_filtered : ∀ (contract : (Model.spec (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (st : (Model.spec (V := V)).S) (s : Slot)
    (st' : (Model.spec (V := V)).S), (Model.spec (V := V)).update_confirmation_with contract E hc st s ⇢ st' → (Model.spec (V := V)).get_filtered_block_tree
    ((Model.spec (V := V)).toHealing st').toFG
    = (Model.spec (V := V)).get_filtered_block_tree ((Model.spec (V := V)).toHealing st).toFG := by
  intro contract E hc st s st' h
  obtain ⟨x1, x2, x3, he⟩ := ContractImages.update_confirmation_with_shape
    (c := contract) (E := E) (hc := hc) (st := st.val) (st' := st'.val) (s := s) h
  show (Spec.Protocol.get_filtered_block_tree (Spec.Store.ofImage st'.val)).image
      Spec.Block.toProof =
    (Spec.Protocol.get_filtered_block_tree (Spec.Store.ofImage st.val)).image
      Spec.Block.toProof
  rw [ForkChoiceImages.get_filtered_block_tree_congr (a := Spec.Store.ofImage st'.val)
    (b := Spec.Store.ofImage st.val)] <;> rw [he] <;>
    simp only [Spec.Store.ofImage, Spec.Store.blockOfImage,
      Spec.Store.toProof_blockOfImageIn]

/-! ## The stable and confirmed blocks a store exposes, at the image -/

omit [Fintype V] [Inhabited V] in
/-- On a store of the instance, `Spec.Protocol.get_stable` of the store read through its tree is the
    block `st.val.blockOfImage` gives for `Protocol.get_stable` of the store's image. -/
theorem get_stable_ofImage (st : OkStore V) :
    Spec.Protocol.get_stable (Spec.Store.ofImage st.val) =
      st.val.blockOfImage (Protocol.get_stable st.val.toProof) := by
  obtain ⟨-, hT, hpar, -⟩ := st.property
  unfold Spec.Protocol.get_stable Protocol.get_stable
  simp only [Id.run, pure, Spec.Store.ofImage]
  rw [Spec.Store.blockOfImage_ancestorEq_of_distinctRoots _ hT hpar]
  show _ = st.val.blockOfImage
    (if Block.preceq st.val.F.toProof st.val.latest_stable.toProof then
      st.val.latest_stable.toProof else st.val.F.toProof)
  split <;> rfl

omit [Fintype V] [Inhabited V] in
/-- On a store of the instance, the member `get_stable` is `Protocol.get_stable` of the store's
    image. -/
theorem get_stable_image (st : OkStore V) :
    Member.get_stable st.val = Protocol.get_stable st.val.toProof := by
  unfold Member.get_stable
  rw [get_stable_ofImage, Spec.Store.toProof_blockOfImage]

omit [Fintype V] [Inhabited V] in
/-- On a store of the instance, the member `get_confirmed` is `Protocol.get_confirmed` of the
    store's image. -/
theorem get_confirmed_image (st : OkStore V) :
    Member.get_confirmed st.val = Protocol.get_confirmed st.val.toProof := by
  obtain ⟨-, hT, hpar, -⟩ := st.property
  unfold Member.get_confirmed Spec.Protocol.get_confirmed Protocol.get_confirmed
  rw [get_stable_ofImage]
  simp only [Id.run, pure, Spec.Store.ofImage]
  rw [Spec.Store.blockOfImage_ancestorEq_of_distinctRoots _ hT hpar]
  show _ = (if Block.preceq (Protocol.get_stable st.val.toProof) st.val.latest_confirmed.toProof then
      st.val.latest_confirmed.toProof else Protocol.get_stable st.val.toProof)
  split <;> rw [Spec.Store.toProof_blockOfImage]

/-- The field `get_stable_upper` of `HandlersFacts` at `Model.spec`: when `F` and the stable
    record are compatible, both are ancestors of the stable block, or the block itself. -/
theorem spec_get_stable_upper : ∀ (st : (Model.spec (V := V)).S) (h : Block.compatible st.F st.latest_stable = true), Block.Preceq st.F ((Model.spec (V := V)).get_stable st) ∧
    Block.Preceq st.latest_stable ((Model.spec (V := V)).get_stable st) := by
  intro st h
  show Block.Preceq _ (Member.get_stable st.val) ∧ Block.Preceq _ (Member.get_stable st.val)
  rw [get_stable_image]
  exact (Model.vocabulary_facts_handlers (V := V)).get_stable_upper st.val.toProof h

/-- The field `get_confirmed_upper` of `HandlersFacts` at `Model.spec`: when the stable block
    and the confirmation record are compatible, both are ancestors of the confirmed block, or the
    block itself. -/
theorem spec_get_confirmed_upper : ∀ (st : (Model.spec (V := V)).S) (h : Block.compatible ((Model.spec (V := V)).get_stable st) st.latest_confirmed = true), Block.Preceq ((Model.spec (V := V)).get_stable st) ((Model.spec (V := V)).get_confirmed st) ∧
    Block.Preceq st.latest_confirmed ((Model.spec (V := V)).get_confirmed st) := by
  intro st h
  show Block.Preceq (Member.get_stable st.val) (Member.get_confirmed st.val) ∧
    Block.Preceq _ (Member.get_confirmed st.val)
  replace h : Block.compatible (Member.get_stable st.val) _ = true := h
  rw [get_stable_image] at h ⊢
  rw [get_confirmed_image]
  exact (Model.vocabulary_facts_handlers (V := V)).get_confirmed_upper st.val.toProof h

/-- The field `get_stable_preceq_of_fields` of `HandlersFacts` at `Model.spec`: if `F` and the
    stable record of `old` are ancestors of those of `new` (or the same), and `new`'s two are
    compatible, then `old`'s stable block is an ancestor of `new`'s, or the same. -/
theorem spec_get_stable_preceq_of_fields : ∀ (old new : (Model.spec (V := V)).S) (hF : Block.Preceq old.F new.F) (hL : Block.Preceq old.latest_stable new.latest_stable) (hFL : Block.compatible new.F new.latest_stable = true), Block.Preceq ((Model.spec (V := V)).get_stable old) ((Model.spec (V := V)).get_stable new) := by
  intro old new hF hL hFL
  show Block.Preceq (Member.get_stable old.val) (Member.get_stable new.val)
  rw [get_stable_image, get_stable_image]
  exact (Model.vocabulary_facts_handlers (V := V)).get_stable_preceq_of_fields old.val.toProof
    new.val.toProof hF hL hFL

/-- The field `get_confirmed_preceq_of_fields` of `HandlersFacts` at `Model.spec`: if `F`, the
    stable record and the confirmation record of `old` are ancestors of those of `new` (or the
    same), and `new`'s are compatible as required, then `old`'s confirmed block is an ancestor of
    `new`'s, or the same. -/
theorem spec_get_confirmed_preceq_of_fields : ∀ (old new : (Model.spec (V := V)).S) (hF : Block.Preceq old.F new.F) (hL : Block.Preceq old.latest_stable new.latest_stable) (hC : Block.Preceq old.latest_confirmed new.latest_confirmed) (hFL : Block.compatible new.F new.latest_stable = true) (hSC : Block.compatible ((Model.spec (V := V)).get_stable new) new.latest_confirmed = true), Block.Preceq ((Model.spec (V := V)).get_confirmed old) ((Model.spec (V := V)).get_confirmed new) := by
  intro old new hF hL hC hFL hSC
  show Block.Preceq (Member.get_confirmed old.val) (Member.get_confirmed new.val)
  replace hSC : Block.compatible (Member.get_stable new.val) _ = true := hSC
  rw [get_stable_image] at hSC
  rw [get_confirmed_image, get_confirmed_image]
  exact (Model.vocabulary_facts_handlers (V := V)).get_confirmed_preceq_of_fields old.val.toProof
    new.val.toProof hF hL hC hFL hSC

/-- The field `preceq_get_stable_of_record` of `HandlersFacts` at `Model.spec`: a block that is
    an ancestor of the stable record and compatible with `F` is an ancestor of the stable block, or
    the block itself. -/
theorem spec_preceq_get_stable_of_record : ∀ (st : (Model.spec (V := V)).S) {P : Block V} (hL : Block.Preceq P st.latest_stable) (hF : Block.Compatible P st.F), Block.Preceq P ((Model.spec (V := V)).get_stable st) := by
  intro st P hL hF
  show Block.Preceq P (Member.get_stable st.val)
  rw [get_stable_image]
  exact (Model.vocabulary_facts_handlers (V := V)).preceq_get_stable_of_record st.val.toProof hL hF

/-! ## The block handler's refusals, at the image -/

omit [Inhabited V] in
omit [Inhabited V] in
omit [Inhabited V] in
omit [Inhabited V] in
omit [Inhabited V] in
omit [Inhabited V] in
omit [Inhabited V] in
omit [Inhabited V] in
omit [Inhabited V] in
omit [Inhabited V] in
omit [Inhabited V] in
omit [Inhabited V] in
omit [Inhabited V] in
omit [Inhabited V] in
omit [Inhabited V] in
/-- `Handlers.onBlockUsing` returns the store unchanged when one of its tests refuses the block `X`:
    a slot after the store's, `X` already held or its parent not held, the finalized block not an
    ancestor of `X`, a proposer other than its slot's, or a parent slot not before its slot. -/
theorem onBlockUsing_of_reject (P : Spec.Provisional V) (st : Spec.Store V)
    (X : Spec.Block V)
    (build : Spec.Protocol.ChainState V → Spec.Protocol.ChainState V)
    (h : (st.s < X.slot ∨ X ∈ st.T ∨ X.parent ∉ st.T) ∨ st.F.ancestorEq X = false ∨
      X.proposer? ≠ P.proposer X.slot ∨ ¬ (X.parent.slot < X.slot)) :
    Handlers.onBlockUsing P st X build = st := by
  unfold Handlers.onBlockUsing
  simp only [Id.run]
  rcases h with (h | h | h) | h | h | h <;> simp [h] <;> rfl


/-- The field `on_block_using_of_rejected` of `HandlersFacts` at `Model.spec`: a block `B` that
    one of the block handler's tests refuses leaves the store as it was. -/
theorem spec_on_block_using_of_rejected : ∀ (E : Env V) (st : (Model.spec (V := V)).S) (B : Block V) (build : (Model.spec (V := V)).CS → (Model.spec (V := V)).CS) (h : (st.s < B.slot ∨ B ∈ st.T ∨ B.parent ∉ st.T) ∨ (!Block.preceq st.F B) = true ∨
    B.proposer? ≠ some (E.proposer B.slot) ∨ ¬ (B.parent.slot < B.slot)), (Model.spec (V := V)).on_block_using E st B build = st := by
  intro E st B build h
  obtain ⟨-, hd, hpc, hF⟩ := st.property
  show OkMember.on_block_using E st B build = st
  unfold OkMember.on_block_using
  split
  · rfl
  apply Subtype.ext
  show Handlers.onBlockUsing (Spec.Provisional.toSpec E) st.val (st.val.blockOfImage B)
    build = st.val
  apply onBlockUsing_of_reject
  set X := st.val.blockOfImage B with hXdef
  have hXB : X.toProof = B := Spec.Store.toProof_blockOfImage _ _
  have hslotX : X.slot = B.slot := by rw [← hXB, SubtypeEqualities.toProof_slot]
  have hXpar : X.parent = st.val.blockOfImage B.parent :=
    (Spec.Store.blockOfImage_parent st.val hd.injOn_toProof hpc B).symm
  have hpslotX : X.parent.slot = B.parent.slot := by
    rw [hXpar, ← SubtypeEqualities.toProof_slot, Spec.Store.toProof_blockOfImage]
  have hpropX : X.proposer? = B.proposer? := by rw [← hXB, SubtypeEqualities.toProof_proposer?]
  rcases h with (h | h | h) | h | h | h
  · left; left
    rw [hslotX]; exact h
  · left; right; left
    obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.1 (show B ∈ st.val.T.image _ from h)
    rw [hXdef, Spec.Store.blockOfImage_toProof_of_mem st.val hd hY]
    exact hY
  · left; right; right
    intro hm
    apply h
    show B.parent ∈ st.val.T.image Spec.Block.toProof
    rw [← Spec.Store.toProof_blockOfImage st.val B.parent, ← hXpar]
    exact Finset.mem_image_of_mem _ hm
  · right; left
    have hF' : st.val.blockOfImage st.val.F.toProof = st.val.F :=
      Spec.Store.blockOfImage_toProof_of_mem st.val hd hF
    rw [← hF', hXdef, Spec.Store.blockOfImage_ancestorEq_of_distinctRoots _ hd hpc]
    replace h : (!Block.preceq st.val.F.toProof B) = true := h
    simpa using h
  · right; right; left
    rw [hpropX, hslotX]
    exact h
  · right; right; right
    rw [hpslotX, hslotX]
    exact h

/-- The field `checked_existing` of `HandlersFacts` at `Model.spec`: a block the store already
    holds leaves the store as it was. -/
theorem spec_checked_existing : ∀ (E : Env V) (hc : Protocol.HealConfig) (st : (Model.spec (V := V)).S) (B : Block V) (buildState : (Model.spec (V := V)).CS → (Model.spec (V := V)).CS) (hB : B ∈ st.T), (Model.spec (V := V)).on_block_checked_using
    (fun current => (Model.spec (V := V)).on_block_using E current B buildState) hc st B = st := by
  intro E hc st B buildState hB
  show OkMember.on_block_checked_using (fun current => OkMember.on_block_using E current B buildState) hc st B = st
  unfold OkMember.on_block_checked_using
  split
  · exact spec_on_block_using_of_rejected E st B buildState (Or.inl (Or.inr (Or.inl hB)))
  · rfl


/-! ## The voter's filtered tree, at the image -/

omit [Fintype V] [Inhabited V] in
/-- The member `get_fg_root` of a store of the spec is `Protocol.get_fg_root` of its image. -/
theorem get_fg_root_image (st : Spec.Store V) :
    Member.get_fg_root st = Protocol.get_fg_root st.toProof.toHealing.toFG := by
  unfold Member.get_fg_root
  rw [Spec.Store.toProof_get_fg_root_ofImage, SpecRecord.toProof_get_fg_root]

/-- At a store `st` of the instance, the member `voter_filtered_block_tree` of `Model.spec`
    equals that of `Model.vocabulary` at the store's image `st.val.toProof`. -/
theorem spec_voter_filtered_block_tree_eq (E : Env V) (st : OkStore V) (s : Slot) :
    (Model.spec (V := V)).voter_filtered_block_tree E st s =
      (Model.vocabulary (V := V)).voter_filtered_block_tree E st.val.toProof s := by
  obtain ⟨hst, -, -, -⟩ := st.property
  set C := Spec.Config.toSpec E unreadHealConfig unreadHeightConfig with hC
  obtain ⟨Q, hQ⟩ := NoRaise.voter_processed_block_tree_ok C hst s
  have hsub : Q ⊆ st.val.T := ForkChoiceImages.processed_subset_of_ok C st.val s hQ
  have hP : Q.image Spec.Block.toProof =
      Protocol.voter_processed_block_tree E st.val.toProof.toHealing.toFG.toSG.toGoldfishStore s := by
    have e := ForkChoiceImages.spec_voter_processed_block_tree_eq E st s
    have h1 : (Model.spec (V := V)).voter_processed_block_tree E st s ⇢
        Q.image Spec.Block.toProof := by
      show Returns (successOutcomes (Except.map (fun T => T.image Spec.Block.toProof)
        (Spec.Protocol.voter_processed_block_tree C st.val s))) _
      rw [hQ]
      exact (returns_pure _ _).2 rfl
    rw [e] at h1
    exact (returns_pure _ _).1 h1
  show successOutcomes ((Spec.Protocol.voter_filtered_block_tree C
      (Spec.Store.ofImage st.val) s).map
      (fun T => T.image Spec.Block.toProof)) = _
  rw [ForkChoiceImages.voter_filtered_block_tree_ofImage, hQ]
  show (pure ((Spec.Protocol.get_filtered_block_tree_from
    (Spec.Store.ofImage st.val) Q).image Spec.Block.toProof) :
      DC.NDRE (Finset (Block V))) = _
  have hm : Member.get_filtered_block_tree_from st.val (Q.image Spec.Block.toProof) =
      (Spec.Protocol.get_filtered_block_tree_from
        (Spec.Store.ofImage st.val) Q).image Spec.Block.toProof := by
    unfold Member.get_filtered_block_tree_from
    rw [ForkChoiceImages.image_map_blockOfImage_of_subset st hsub]
  rw [← hm, ForkChoiceImages.filtered_from_eq_vocabulary st, hP]
  show _ = (pure (Protocol.voter_filtered_block_tree E st.val.toProof s) : DC.NDRE _)
  unfold Protocol.voter_filtered_block_tree
  rfl

/-- The field `voter_filtered_block_tree_cases` of `HandlersFacts` at `Model.spec`: a block `C`
    of the voter's filtered tree is a block of the voter's processed tree `P`, `F` or a descendant
    of `F`, a block of `P` whose chain state has height at least `h_max − 1` or an ancestor of one,
    and the root `get_fg_root` or a descendant of it. -/
theorem spec_voter_filtered_block_tree_cases : ∀ (E : Env V) (st : (Model.spec (V := V)).S) (s : Slot) {C : Block V} (X : Finset (Block V)) (hX : (Model.spec (V := V)).voter_filtered_block_tree E st s ⇢ X) (hC : C ∈ X) (P : Finset (Block V)) (hP : (Model.spec (V := V)).voter_processed_block_tree E ((Model.spec (V := V)).toHealing st).toFG.toSG.toGoldfishStore s ⇢ P), C ∈ P ∧
    Block.Preceq st.F C ∧
    (∃ Y ∈ P,
    Block.Preceq C Y ∧ st.h_max - 1 ≤ (st.σ Y).h) ∧
    Block.Preceq ((Model.spec (V := V)).get_fg_root ((Model.spec (V := V)).toHealing st).toFG) C := by
  intro E st s C X hX hC P hP
  rw [spec_voter_filtered_block_tree_eq] at hX
  have hP' : (Model.vocabulary (V := V)).voter_processed_block_tree E
      st.val.toProof.toHealing.toFG.toSG.toGoldfishStore s ⇢ P := by
    rw [← ForkChoiceImages.spec_voter_processed_block_tree_eq]; exact hP
  have h := (Model.vocabulary_facts_handlers (V := V)).voter_filtered_block_tree_cases E
    st.val.toProof s X hX hC P hP'
  obtain ⟨h1, h2, ⟨Y, hY, h3, h4⟩, h5⟩ := h
  refine ⟨h1, h2, ⟨Y, hY, h3, ?_⟩, ?_⟩
  · show st.val.h_max - 1 ≤ (Member.store_σ st.val Y).toProof.h
    exact h4
  · show Block.Preceq (Member.get_fg_root st.val) C
    rw [get_fg_root_image]
    exact h5

/-- The field `mem_voter_filtered_block_tree_of_parts` of `HandlersFacts` at `Model.spec`: a
    block `C` of the voter's processed tree `P` that is `F` or a descendant of `F`, the root
    `get_fg_root` or a descendant of it, and an ancestor (or itself) of a block of `P` whose chain
    state has height at least `h_max − 1`, is in the voter's filtered tree. -/
theorem spec_mem_voter_filtered_block_tree_of_parts : ∀ (E : Env V) (st : (Model.spec (V := V)).S) (s : Slot) {C Y : Block V} (P : Finset (Block V)) (hP : (Model.spec (V := V)).voter_processed_block_tree E ((Model.spec (V := V)).toHealing st).toFG.toSG.toGoldfishStore s ⇢ P) (hC : C ∈ P) (hF : Block.Preceq st.F C) (hY : Y ∈ P) (hCY : Block.Preceq C Y) (hh : st.h_max - 1 ≤ (st.σ Y).h) (hroot : Block.Preceq ((Model.spec (V := V)).get_fg_root ((Model.spec (V := V)).toHealing st).toFG) C) (X : Finset (Block V)) (hX : (Model.spec (V := V)).voter_filtered_block_tree E st s ⇢ X), C ∈ X := by
  intro E st s C Y P hP hC hF hY hCY hh hroot X hX
  rw [spec_voter_filtered_block_tree_eq] at hX
  have hP' : (Model.vocabulary (V := V)).voter_processed_block_tree E
      st.val.toProof.toHealing.toFG.toSG.toGoldfishStore s ⇢ P := by
    rw [← ForkChoiceImages.spec_voter_processed_block_tree_eq]; exact hP
  exact (Model.vocabulary_facts_handlers (V := V)).mem_voter_filtered_block_tree_of_parts E
    st.val.toProof s P hP' hC hF hY hCY hh
    (by
      show Block.Preceq (Protocol.get_fg_root st.val.toProof.toHealing.toFG) C
      rw [← get_fg_root_image]; exact hroot) X hX


/-! ## The head in a tree, at the image -/

/-- The member `round_of` of `Model.spec` at the store's slot is the spec's round of that slot. -/
theorem round_of_store (E : Env V) (hc : Protocol.HealConfig) (st : OkStore V) :
    (Model.spec (V := V)).round_of hc (Member.store_s st.val) =
      (Spec.Config.toSpec E hc unreadHeightConfig).round_of st.val.s := by
  simp only [Model.spec, Member.round_of]
  rfl

/-- The field `get_head_in_tree_with_eq_layer` of `HandlersFacts` at `Model.spec`: the head in
    a tree read on the store is the head read on the store as a healing store. -/
theorem spec_get_head_in_tree_with_eq_layer : ∀ (contract : (Model.spec (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (st : (Model.spec (V := V)).S) (tree : Finset (Block V)) (votes support : Finset (GoldfishVote V)) (k : Slot)
    (X : Block V), (Model.spec (V := V)).get_head_in_tree_with contract E hc st tree votes support k ⇢ X ↔
    (Model.spec (V := V)).get_head_in_tree_with_layer contract E hc ((Model.spec (V := V)).toHealing st) tree votes support k ⇢ X :=
  fun _ _ _ _ _ _ _ _ _ => Iff.rfl

/-- The field `get_head_in_tree_with_eq_fork_choice` of `HandlersFacts` at `Model.spec`: for
    every outcome `R` of the SG root at the store's round, `X` is an outcome of the head in `tree`
    exactly when `X` is an outcome of the Goldfish fork choice from `R` through `tree`. -/
theorem spec_get_head_in_tree_with_eq_fork_choice : ∀ (contract : (Model.spec (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (st : (Model.spec (V := V)).S) (tree : Finset (Block V)) (votes support : Finset (GoldfishVote V)) (s : Slot)
    (R : Block V), (Model.spec (V := V)).get_sg_root_with contract E hc ((Model.spec (V := V)).toHealing st) ((Model.spec (V := V)).round_of hc st.s) ⇢ R →
    ∀ X : Block V, (Model.spec (V := V)).get_head_in_tree_with contract E hc st tree votes support s ⇢ X ↔
    (Model.spec (V := V)).goldfish_fork_choice E ((Model.spec (V := V)).toHealing st).toFG.σ ((Model.spec (V := V)).toHealing st).toFG.h_max st.T st.s
    R tree
    votes support s ⇢ X := by
  intro c E hc st tree votes support s R hR X
  have hR' : Returns (Member.get_sg_root_with c E hc st.val
      ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.val.s)) R := by
    rw [← round_of_store E hc st]; exact hR
  have e := ContractImages.member_get_head_in_tree_with_layer_eq st c E hc tree votes support s hR'
  rw [ForkChoiceImages.spec_goldfish_fork_choice_eq]
  show Returns (Member.get_head_in_tree_with_layer c E hc st.val tree votes support s) X ↔ _
  rw [e]
  rfl

/-- The field `get_sg_root_with_preceq_get_head_in_tree_with_store` of `HandlersFacts` at
    `Model.spec`: the SG root at the store's round is an ancestor of the head in any tree, or
    the head itself. -/
theorem spec_get_sg_root_with_preceq_get_head_in_tree_with_store : ∀ (contract : (Model.spec (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (st : (Model.spec (V := V)).S) (tree : Finset (Block V)) (votes support : Finset (GoldfishVote V)) (s : Slot)
    (R : Block V), (Model.spec (V := V)).get_sg_root_with contract E hc ((Model.spec (V := V)).toHealing st) ((Model.spec (V := V)).round_of hc st.s) ⇢ R →
    ∀ H : Block V, (Model.spec (V := V)).get_head_in_tree_with contract E hc st tree votes support s ⇢ H →
    Block.Preceq R H := by
  intro c E hc st tree votes support s R hR H hH
  have hR' : Returns (Member.get_sg_root_with c E hc st.val
      ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.val.s)) R := by
    rw [← round_of_store E hc st]; exact hR
  have e := ContractImages.member_get_head_in_tree_with_layer_eq st c E hc tree votes support s hR'
  replace hH : Returns (Member.get_head_in_tree_with_layer c E hc st.val tree votes support s) H := hH
  rw [e] at hH
  obtain rfl := (returns_pure _ _).1 hH
  unfold Protocol.goldfish_fork_choice
  exact Protocol.ghost_preceq _ _ _ _


/-! ## The block receipt's new bodies -/

omit [Inhabited V] in
/-- The spec's block receipt either admits the block `X`, and then its tree is the store's with `X`
    added, or returns the store unchanged. -/
theorem on_block_cases (C : Spec.Config) (P : Spec.Provisional V)
    (st : Spec.Store V) (X : Spec.Block V) :
    (Spec.Protocol.block_admissible C P st X = true ∧
        (Spec.Protocol.on_block C P st X).T = st.T ∪ {X}) ∨
      Spec.Protocol.on_block C P st X = st := by
  rw [Handlers.on_block_eq]
  by_cases h : Spec.Protocol.block_admissible C P st X = true
  · left
    refine ⟨h, ?_⟩
    rw [if_pos h, OkStore.admit_attestations_T]
    unfold Handlers.admitBlockCore
    rw [if_pos h, SubtypeEqualities.blockCore_T]
  · right
    rw [if_neg h]

omit [Inhabited V] in
/-- The spec's block receipt `Spec.Protocol.on_block` and `Handlers.admitBlockCore` give the same
    tree. -/
theorem on_block_T_eq_admitBlockCore_T (C : Spec.Config) (P : Spec.Provisional V)
    (st : Spec.Store V) (X : Spec.Block V) :
    (Spec.Protocol.on_block C P st X).T = (Handlers.admitBlockCore C P st X).T := by
  rw [Handlers.on_block_eq]
  by_cases h : Spec.Protocol.block_admissible C P st X = true
  · rw [if_pos h, OkStore.admit_attestations_T]
  · rw [if_neg h]
    unfold Handlers.admitBlockCore
    rw [if_neg h]

/-- The field `on_block_with_new_body` of `HandlersFacts` at `Model.spec`: a body the block
    receipt adds is the received block `B'`, and its erasure is then in the tree. -/
theorem spec_on_block_with_new_body : ∀ (adm : Protocol.CarriedAdmission) (S : Setup V) (before : (Model.spec (V := V)).NS) (B' C : NamedBlock V) (hpre : C ∉ before.bodies) (hpost : C ∈ ((Model.spec (V := V)).on_block_with adm S.E S.hc S.cfg before B').bodies), C = B' ∧
    C.erase ∈ ((Model.spec (V := V)).on_block_with adm S.E S.hc S.cfg before B').core.T := by
  intro adm S before B' C hpre hpost
  rcases ok_block_cases adm S.E S.hc S.cfg before B' with ⟨-, he, -⟩ | ⟨-, he, -⟩
  · rw [he] at hpost; exact absurd hpost hpre
  change C ∈ Member.bodies ((Model.spec (V := V)).on_block_with adm S.E S.hc S.cfg before B').val
    at hpost
  show C = B' ∧ C.erase ∈ Member.store_T
    ((Model.spec (V := V)).on_block_with adm S.E S.hc S.cfg before B').val
  rw [he] at hpost ⊢
  change C ∈ Member.bodies (Spec.Protocol.on_block
    (Spec.Config.toSpec S.E S.hc S.cfg) (Spec.Provisional.toSpec S.E) before.val
    (Spec.Block.toSpecNamed B')) at hpost
  show C = B' ∧ C.erase ∈ (Spec.Protocol.on_block
    (Spec.Config.toSpec S.E S.hc S.cfg) (Spec.Provisional.toSpec S.E) before.val
    (Spec.Block.toSpecNamed B')).T.image Spec.Block.toProof
  have hpre' : C ∉ before.val.T.map Spec.Block.toProofNamedEmb := hpre
  rcases on_block_cases (Spec.Config.toSpec S.E S.hc S.cfg)
      (Spec.Provisional.toSpec S.E) before.val (Spec.Block.toSpecNamed B')
    with ⟨-, hT⟩ | hst
  · unfold Member.bodies at hpost
    rw [hT] at hpost ⊢
    obtain ⟨Y, hY, rfl⟩ := Finset.mem_map.1 hpost
    rcases Finset.mem_union.1 hY with hY | hY
    · exact absurd (Finset.mem_map_of_mem _ hY) hpre'
    · rw [Finset.mem_singleton.1 hY]
      refine ⟨by simp, ?_⟩
      rw [Spec.Block.coe_toProofNamedEmb, Spec.Block.toProofNamed_erase]
      exact Finset.mem_image_of_mem _ (Finset.mem_union_right _ (Finset.mem_singleton_self _))
  · rw [hst] at hpost
    exact absurd hpost hpre'

/-- The field `new_body_guards` of `HandlersFacts` at `Model.spec`: a body `B` the block
    receipt adds has a slot not after the store's, its slot's proposer, a parent of an earlier slot,
    and included attestations that pass the round test. -/
theorem spec_new_body_guards : ∀ (E : Env V) (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig)
    (st : (Model.spec (V := V)).NS) (B : NamedBlock V), B ∉ st.bodies →
    B ∈ ((Model.spec (V := V)).on_block_with .alsoCarried E hc cfg st B).bodies →
    B.erase.slot ≤ st.core.s ∧ B.erase.proposer? = some (E.proposer B.erase.slot) ∧
      B.erase.parent.slot < B.erase.slot ∧ (Model.spec (V := V)).carried_attestations_admissible hc B.erase = true := by
  intro E hc cfg st B hpre hpost
  rcases ok_block_cases .alsoCarried E hc cfg st B with ⟨-, he, -⟩ | ⟨-, he, -⟩
  · rw [he] at hpost; exact absurd hpost hpre
  change B ∈ Member.bodies ((Model.spec (V := V)).on_block_with .alsoCarried E hc cfg st B).val
    at hpost
  rw [he] at hpost
  change B ∈ Member.bodies (Spec.Protocol.on_block
    (Spec.Config.toSpec E hc cfg) (Spec.Provisional.toSpec E) st.val
    (Spec.Block.toSpecNamed B)) at hpost
  have hpre' : B ∉ st.val.T.map Spec.Block.toProofNamedEmb := hpre
  set X := Spec.Block.toSpecNamed B with hXdef
  have hXB : X.toProofNamed = B := Spec.Block.toProofNamed_toSpecNamed B
  have hE : B.erase = X.toProof := by rw [← hXB, Spec.Block.toProofNamed_erase]
  rcases on_block_cases (Spec.Config.toSpec E hc cfg)
      (Spec.Provisional.toSpec E) st.val X with ⟨had, -⟩ | hst
  · obtain ⟨-, hinc, hslot, -, hprop, hps⟩ := (SubtypeEqualities.block_admissible_iff _ _ _ _).1 had
    rw [hE]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [SubtypeEqualities.toProof_slot]
      exact Nat.not_lt.1 hslot
    · rw [SubtypeEqualities.toProof_proposer?, SubtypeEqualities.toProof_slot]
      exact hprop
    · rw [SubtypeEqualities.toProof_parent, SubtypeEqualities.toProof_slot,
        SubtypeEqualities.toProof_slot]
      exact hps
    · show Member.carried_attestations_admissible hc X.toProof = true
      rw [image_carried_attestations_admissible, toProof_carried_attestations_admissible E hc cfg]
      exact hinc
  · rw [hst] at hpost
    exact absurd hpost hpre'

/-- The field `mem_on_block_with_bodies_of_mem_core` of `HandlersFacts` at `Model.spec`: every
    body after `ns_process_block_core` is a body after the whole block receipt `on_block_with`. -/
theorem spec_mem_on_block_with_bodies_of_mem_core : ∀ (admission : Protocol.CarriedAdmission) (E : Env V) (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (st : (Model.spec (V := V)).NS) (B : NamedBlock V) {D : NamedBlock V} (hD : D ∈ ((Model.spec (V := V)).ns_process_block_core E hc cfg st B).bodies), D ∈ ((Model.spec (V := V)).on_block_with admission E hc cfg st B).bodies := by
  intro admission E hc cfg st B D hD
  rcases ok_block_cases admission E hc cfg st B with ⟨-, he1, he2⟩ | ⟨-, he1, he2⟩
  · rw [he2] at hD; rw [he1]; exact hD
  change D ∈ Member.bodies ((Model.spec (V := V)).ns_process_block_core E hc cfg st B).val at hD
  show D ∈ Member.bodies ((Model.spec (V := V)).on_block_with admission E hc cfg st B).val
  rw [he2] at hD
  rw [he1]
  change D ∈ Member.bodies (Handlers.admitBlockCore (Spec.Config.toSpec E hc cfg)
    (Spec.Provisional.toSpec E) st.val (Spec.Block.toSpecNamed B)) at hD
  show D ∈ Member.bodies (Spec.Protocol.on_block (Spec.Config.toSpec E hc cfg)
    (Spec.Provisional.toSpec E) st.val (Spec.Block.toSpecNamed B))
  unfold Member.bodies at hD ⊢
  rw [on_block_T_eq_admitBlockCore_T]
  exact hD


omit [Inhabited V] in
/-- A Goldfish vote of slot `k` after the spec's checked admission of `v` was there before or is
    `v`. -/
theorem on_goldfish_vote_checked_gf_votes_mem (P : Spec.Provisional V)
    (S : Spec.Store V) (v : Spec.GoldfishVote V) (k : Slot)
    {y : Spec.GoldfishVote V}
    (h : y ∈ (Spec.Protocol.on_goldfish_vote_checked P S v).gf_votes k) :
    y ∈ S.gf_votes k ∨ y = v := by
  unfold Spec.Protocol.on_goldfish_vote_checked Spec.Protocol.on_goldfish_vote
    at h
  simp only [Id.run, pure] at h
  split_ifs at h <;> first
    | exact Or.inl h
    | (simp only [Function.update_apply] at h
       split_ifs at h with hk
       · rcases List.mem_append.1 h with h | h
         · rw [hk]; exact Or.inl h
         · exact Or.inr (List.mem_singleton.1 h)
       · exact Or.inl h)

omit [Inhabited V] in
/-- A Goldfish vote of slot `k` after the spec's checked admission of a list of votes was there
    before or is in the list. -/
theorem foldl_checked_gf_votes_mem (P : Spec.Provisional V)
    (votes : List (Spec.GoldfishVote V)) (S0 : Spec.Store V) (k : Slot)
    {y : Spec.GoldfishVote V}
    (h : y ∈ (votes.foldl (Spec.Protocol.on_goldfish_vote_checked P) S0).gf_votes k) :
    y ∈ S0.gf_votes k ∨ y ∈ votes := by
  induction votes generalizing S0 with
  | nil => exact Or.inl h
  | cons v vs ih =>
    rcases ih _ h with h1 | h1
    · rcases on_goldfish_vote_checked_gf_votes_mem P S0 v k h1 with h2 | h2
      · exact Or.inl h2
      · exact Or.inr (h2 ▸ List.mem_cons_self ..)
    · exact Or.inr (List.mem_cons_of_mem _ h1)

/-- The field `process_block_core_gf_votes_upper` of `HandlersFacts` at `Model.spec`: a
    Goldfish vote that `ns_process_block_core` adds is a vote the block `B` includes, and `B`'s
    erasure was not in the tree before and is in it after. -/
theorem spec_process_block_core_gf_votes_upper : ∀ (E : Env V) (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig)
    (st : (Model.spec (V := V)).NS) (B : NamedBlock V) (k : Slot) (y : GoldfishVote V),
    y ∈ ((Model.spec (V := V)).ns_process_block_core E hc cfg st B).core.gf_votes k →
      y ∈ st.core.gf_votes k ∨
        (y ∈ B.gf_votes ∧ B.erase ∉ st.core.T ∧
          B.erase ∈ ((Model.spec (V := V)).ns_process_block_core E hc cfg st B).core.T) := by
  intro E hc cfg st B k y hy
  rcases ok_block_cases .alsoCarried E hc cfg st B with ⟨-, -, he⟩ | ⟨hnh, -, he⟩
  · rw [he] at hy; exact Or.inl hy
  change y ∈ ((((Model.spec (V := V)).ns_process_block_core E hc cfg st B).val).gf_votes k).map
    Spec.GoldfishVote.toProof at hy
  show _ ∨ (_ ∧ _ ∧ B.erase ∈
    ((Model.spec (V := V)).ns_process_block_core E hc cfg st B).val.T.image
      Spec.Block.toProof)
  rw [he] at hy ⊢
  set X := Spec.Block.toSpecNamed B with hXdef
  have hXB : X.toProofNamed = B := Spec.Block.toProofNamed_toSpecNamed B
  have hE : B.erase = X.toProof := by rw [← hXB, Spec.Block.toProofNamed_erase]
  change y ∈ ((Handlers.admitBlockCore (Spec.Config.toSpec E hc cfg)
    (Spec.Provisional.toSpec E) st.val X).gf_votes k).map
      Spec.GoldfishVote.toProof at hy
  change _ ∨ (_ ∧ _ ∧ B.erase ∈ (Handlers.admitBlockCore (Spec.Config.toSpec E hc cfg)
    (Spec.Provisional.toSpec E) st.val X).T.image Spec.Block.toProof)
  unfold Handlers.admitBlockCore at hy ⊢
  by_cases had : Spec.Protocol.block_admissible (Spec.Config.toSpec E hc cfg)
      (Spec.Provisional.toSpec E) st.val X = true
  · rw [if_pos had] at hy ⊢
    rw [SubtypeEqualities.blockCore_T]
    rw [SubtypeEqualities.blockCore_eq] at hy
    obtain ⟨a, b, c, d, hW⟩ := OkStore.updateFinalityWith_shape
      (X.gf_votes.foldl (Spec.Protocol.on_goldfish_vote_checked
        (Spec.Provisional.toSpec E))
        { st.val with
          σ := Function.update st.val.σ X (Spec.Protocol.state_transition
            (Spec.Config.toSpec E hc cfg) (Spec.Provisional.toSpec E)
            (st.val.σ X.parent) X)
          T := st.val.T ∪ {X}
          timestamp_block := Function.update st.val.timestamp_block X (some (st.val.t : Stamp)) })
      ((X.gf_votes.foldl (Spec.Protocol.on_goldfish_vote_checked
        (Spec.Provisional.toSpec E))
        { st.val with
          σ := Function.update st.val.σ X (Spec.Protocol.state_transition
            (Spec.Config.toSpec E hc cfg) (Spec.Provisional.toSpec E)
            (st.val.σ X.parent) X)
          T := st.val.T ∪ {X}
          timestamp_block := Function.update st.val.timestamp_block X (some (st.val.t : Stamp)) }).σ X)
    rw [hW] at hy
    obtain ⟨y', hy', rfl⟩ := List.mem_map.1 hy
    rcases foldl_checked_gf_votes_mem _ _ _ k hy' with h1 | h1
    · exact Or.inl (List.mem_map_of_mem h1)
    · right
      obtain ⟨⟨hXT, -⟩, -⟩ := (SubtypeEqualities.block_admissible_iff _ _ _ _).1 had
      refine ⟨?_, ?_, ?_⟩
      · rw [← hXB, Spec.Block.toProofNamed_gf_votes]
        exact List.mem_map_of_mem h1
      · rw [hE]
        intro hm
        obtain ⟨Y, hY, hYX⟩ := Finset.mem_image.1 hm
        apply hXT
        by_cases hYe : Y = X
        · exact hYe ▸ hY
        · exfalso
          apply hnh
          refine ⟨Y, hY, hYe, ?_⟩
          have := congrArg DecoupledConsensusModel.Block.root hYX
          rwa [Spec.Block.toProof_root, Spec.Block.toProof_root,
            Spec.BlockId.toProof_inj] at this
      · rw [hE]
        exact Finset.mem_image_of_mem _ (Finset.mem_union_right _ (Finset.mem_singleton_self X))
  · rw [if_neg had] at hy
    exact Or.inl hy


/-! ## The finality update keeps the finalized block viable -/

omit [Fintype V] [Inhabited V] in
/-- What the spec's finality update with the chain state `σ` writes: the tree and the chain states
    are kept, `h_max` becomes `max st.h_max σ.h`, and the finalized block is kept or becomes `σ.F`,
    a block of the viable tree read with the new `h_max`. -/
theorem updateFinalityWith_F_cases (st : Spec.Store V)
    (σ : Spec.Protocol.ChainState V) :
    (Handlers.updateFinalityWith st σ).T = st.T ∧ (Handlers.updateFinalityWith st σ).σ = st.σ ∧
      (Handlers.updateFinalityWith st σ).h_max = max st.h_max σ.h ∧
      ((Handlers.updateFinalityWith st σ).F = st.F ∨
        ((Handlers.updateFinalityWith st σ).F = σ.F ∧
          σ.F ∈ Spec.Protocol.viable_tree st.σ st.F (max st.h_max σ.h) st.T)) := by
  unfold Handlers.updateFinalityWith
  simp only [Id.run, pure]
  split_ifs with h1 h2 <;> simp_all

omit [Fintype V] [Inhabited V] in
/-- On a store of the instance, the finality update from the chain state `σ` of the tree block `Y`,
    of which `F` is an ancestor, keeps `F` in the tree with a descendant of chain-state height at
    least `h_max − 1`. -/
theorem finalizedViable_updateFinalityWith (st : OkStore V)
    (σ : Spec.Protocol.ChainState V) {Y : Spec.Block V} (hY : Y ∈ st.val.T)
    (hσY : st.val.σ Y = σ) (hFB : Block.preceq st.val.F.toProof Y.toProof = true)
    (h1 : st.val.F.toProof ∈ st.val.T.image Spec.Block.toProof)
    (h2 : ∃ W ∈ st.val.T.image Spec.Block.toProof, Block.Preceq st.val.F.toProof W ∧
      st.val.h_max - 1 ≤ (st.val.σ (st.val.blockOfImage W)).h) :
    (Handlers.updateFinalityWith st.val σ).F.toProof ∈
        (Handlers.updateFinalityWith st.val σ).T.image Spec.Block.toProof ∧
      ∃ W ∈ (Handlers.updateFinalityWith st.val σ).T.image Spec.Block.toProof,
        Block.Preceq (Handlers.updateFinalityWith st.val σ).F.toProof W ∧
        (Handlers.updateFinalityWith st.val σ).h_max - 1 ≤
          ((Handlers.updateFinalityWith st.val σ).σ
            ((Handlers.updateFinalityWith st.val σ).blockOfImage W)).h := by
  obtain ⟨-, hd, hpc, -⟩ := st.property
  have hinj := hd.injOn_toProof
  obtain ⟨hT, hσ, hm, hF⟩ := updateFinalityWith_F_cases st.val σ
  have hbo : (Handlers.updateFinalityWith st.val σ).blockOfImage = st.val.blockOfImage := by
    funext W; unfold Spec.Store.blockOfImage; rw [hT]
  rw [hT, hσ, hm, hbo]
  have hYfix : st.val.blockOfImage Y.toProof = Y :=
    Spec.Store.blockOfImage_toProof_of_mem st.val hd hY
  rcases hF with hF | ⟨hF, hv⟩
  · rw [hF]
    refine ⟨h1, ?_⟩
    by_cases hle : st.val.h_max ≤ σ.h
    · refine ⟨Y.toProof, Finset.mem_image_of_mem _ hY,
        _root_.DecoupledConsensusModel.Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mp hFB, ?_⟩
      rw [hYfix, hσY, max_eq_right hle]
      exact Nat.sub_le _ _
    · obtain ⟨W, hW, hFW, hh⟩ := h2
      refine ⟨W, hW, hFW, ?_⟩
      rw [max_eq_left (le_of_lt (Nat.lt_of_not_le hle))]
      exact hh
  · rw [hF]
    simp only [Spec.Protocol.viable_tree, Spec.Protocol.finalized_descendants,
      Spec.Protocol.viable, Finset.mem_filter, decide_eq_true_eq] at hv
    obtain ⟨⟨hσF, -⟩, W, hW, hσW, hh⟩ := hv
    refine ⟨Finset.mem_image_of_mem _ hσF, W.toProof, Finset.mem_image_of_mem _ hW, ?_, ?_⟩
    · apply _root_.DecoupledConsensusModel.Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mp
      rw [Spec.Block.toProof_preceq_of_injOn st.val.T hinj hpc hσF hW]
      exact hσW
    · rw [Spec.Store.blockOfImage_toProof_of_mem st.val hd hW]
      exact hh

/-- The field `finalizedViable_update_finality` of `HandlersFacts` at `Model.spec`: if `F` is
    in the tree with a descendant of chain-state height at least `h_max − 1`, the finality update
    from the chain state of a tree block `B` of which `F` is an ancestor keeps that true. -/
theorem spec_finalizedViable_update_finality : ∀ (st : (Model.spec (V := V)).S) (σ : (Model.spec (V := V)).CS) {B : Block V}, B ∈ st.T → st.σ B = σ →
    Block.preceq st.F B = true →
    (st.F ∈ st.T ∧ ∃ W ∈ st.T, Block.Preceq st.F W ∧ st.h_max - 1 ≤ (st.σ W).h) →
    (((Model.spec (V := V)).update_finality st σ).F ∈ ((Model.spec (V := V)).update_finality st σ).T ∧
      ∃ W ∈ ((Model.spec (V := V)).update_finality st σ).T, Block.Preceq ((Model.spec (V := V)).update_finality st σ).F W ∧
        ((Model.spec (V := V)).update_finality st σ).h_max - 1 ≤ (((Model.spec (V := V)).update_finality st σ).σ W).h) := by
  intro st σ B hB hσB hFB h
  obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.1 (show B ∈ st.val.T.image _ from hB)
  have hσY : st.val.σ Y = σ := by
    have e : st.val.σ (st.val.blockOfImage Y.toProof) = σ := hσB
    rwa [Spec.Store.blockOfImage_toProof_of_mem st.val st.property.2.1 hY] at e
  exact finalizedViable_updateFinalityWith st σ hY hσY hFB h.1 h.2


/-! ## The confirmation update, read step by step -/

section Confirmation

omit [Inhabited V] in
/-- What an outcome of the spec's `update_confirmation` is made of: `early`, the slot-`s` pool votes
    that resolve before the Goldfish confirmation time; `late`, the pool's votes stamped before the
    confirmation time; `A`, the SG root; `H`, the walk's answer from `A` through the filtered tree;
    `hel`, the eligibility of `H`; `G`, the stable-record root of the store's round; and `S?`, the
    confirmation candidate. The three records are written from these. -/
theorem update_confirmation_trace {C : Spec.Config} {st st' : Spec.Store V} {s : Slot}
    (h : Spec.Protocol.update_confirmation C st s = .ok st') :
    ∃ (early late : Finset (Spec.GoldfishVote V)) (A H G : Spec.Block V) (hel : Bool)
      (S? : Option (Spec.Block V)),
      early = (st.pool s).filter (fun v => (match st.tau v with
        | .ok o => Spec.occurrenceBefore o (C.gf_confirmation_time s)
        | .error _ => false) = true) ∧
      Spec.beforeCutoff st.timestamp_vote (C.confirmation_time s) (st.pool s) = .ok late ∧
      Spec.Protocol.get_sg_root_with C st = .ok A ∧
      Spec.Protocol.ghost A (Spec.Protocol.get_filtered_block_tree st)
        (Spec.Protocol.raw_goldfish_score st.T
          (early.filter fun v => Spec.Protocol.no_second_vote_in late v = true)
          (early.filter fun v => Spec.Protocol.no_second_vote_in late v = true) s)
        (fun B => do
          let n ← Spec.Protocol.raw_goldfish_score st.T
            (early.filter fun v => Spec.Protocol.no_second_vote_in late v = true)
            (early.filter fun v => Spec.Protocol.no_second_vote_in late v = true) s B
          return decide (Spec.Protocol.raw_voters_count late < 2 * n)) = .ok H ∧
      (do
          let n ← Spec.Protocol.raw_goldfish_score st.T
            (early.filter fun v => Spec.Protocol.no_second_vote_in late v = true)
            (early.filter fun v => Spec.Protocol.no_second_vote_in late v = true) s H
          return decide (Spec.Protocol.raw_voters_count late < 2 * n) : DC.DRE Bool) = .ok hel ∧
      Spec.Protocol.round_stable_root st (C.round_of st.s) = .ok G ∧
      Spec.Protocol.confirmation_candidate C st = .ok S? ∧
      st'.live_confirmed = (if hel then H else Spec.Protocol.get_fg_root st) ∧
      st'.latest_stable = Spec.Protocol.advance_confirmed st.latest_stable G ∧
      st'.latest_confirmed = Spec.Protocol.floor_on_stable (Spec.Protocol.advance_confirmed st.latest_stable G)
        (if hel then Spec.Protocol.advance_confirmed st.latest_confirmed H else
          match S? with
          | some S => Spec.Protocol.advance_confirmed st.latest_confirmed S
          | none => st.latest_confirmed) st.latest_confirmed := by
  unfold Spec.Protocol.update_confirmation at h
  obtain ⟨early, he, h⟩ := NoRaise.DRE.of_bind_ok h
  obtain ⟨late, hl, h⟩ := NoRaise.DRE.of_bind_ok h
  dsimp only at h
  obtain ⟨A, hA, h⟩ := NoRaise.DRE.of_bind_ok h
  obtain ⟨H, hH, h⟩ := NoRaise.DRE.of_bind_ok h
  obtain ⟨hel, hhel, h⟩ := NoRaise.DRE.of_bind_ok h
  obtain ⟨G, hG, h⟩ := NoRaise.DRE.of_bind_ok h
  obtain ⟨S?, hS, h⟩ := NoRaise.DRE.of_bind_ok h
  refine ⟨early, late, A, H, G, hel, S?, ?_, hl, hA, hH, hhel, hG, hS, ?_⟩
  · refine ForkChoiceImages.filterM_eq_filter_of_ok _ _ (fun a b hp => ?_) _ _ he
    cases ht : st.tau a with
    | error e => rw [ht] at hp; cases hp
    | ok o =>
      rw [ht] at hp
      have hb := Except.ok.inj hp
      subst hb
      rfl
  · split_ifs at h with h1 h2 <;> simp only [pure, Except.pure, Except.ok.injEq] at h <;> subst h
    · simp [h1]
    · obtain ⟨S, rfl⟩ := Option.ne_none_iff_exists'.mp h2
      simp [h1, Option.value]
    · have h2' : S? = none := by simpa using h2
      subst h2'
      simp [h1]

end Confirmation


/-! ## The confirmation update at the image: the votes, the score and the walk -/

/-- The slot-`s` votes of the store's pool stamped before slot `s`'s confirmation time: the votes
    the confirmation update counts as late. -/
def ucLate (E : Env V) (st : Spec.Store V) (s : Slot) : Finset (GoldfishVote V) :=
  DecoupledConsensusModel.beforeCutoff (Member.store_timestamp_vote st) (Member.confirmation_time E s)
    (Member.store_pool st s)

/-- The support votes of the confirmation update of slot `s`: the pool's votes that resolve before
    the support cutoff, without those of a validator with a second vote in `ucLate`. -/
def ucSupport (E : Env V) (st : Spec.Store V) (s : Slot) : Finset (GoldfishVote V) :=
  (DecoupledConsensusModel.beforeCutoff (Protocol.Store.tau st.toProof) (Member.support_cutoff E s)
    (Member.store_pool st s)).filter
    (fun u => Member.no_second_vote_in (ucLate E st s) u = true)

/-- The Goldfish score of `B` over the support votes `ucSupport` of slot `s`. -/
def ucScore (E : Env V) (st : Spec.Store V) (s : Slot) (B : Block V) : ℕ :=
  Protocol.goldfish_score E (Member.store_T st) (ucSupport E st s) (ucSupport E st s) s B

/-- Whether the number of validators with a vote in `ucLate` is less than twice `ucScore` of `B`. -/
def ucEligible (E : Env V) (st : Spec.Store V) (s : Slot) (B : Block V) : Bool :=
  decide (Member.voters_count E (ucLate E st s) s < 2 * ucScore E st s B)

/-- On a store of the instance, `Store.tau` of a stamped vote `v` is `Protocol.Store.tau` of the
    store's image at `v`'s image. -/
theorem tau_eq_ok_of_stamped (st : OkStore V) {v : Spec.GoldfishVote V}
    (hv : st.val.timestamp_vote v ≠ none) :
    st.val.tau v = .ok (Protocol.Store.tau st.val.toProof v.toProof) := by
  obtain ⟨hst, hT, -, -⟩ := st.property
  obtain ⟨o, ho⟩ := NoRaise.tau_ok hT hst.1 hv
  rw [ho, ForkChoiceImages.tau_toProof_of_ok st _ ho, StoreFacts.gs_tau_image]

/-- On a store of the instance, the early votes of the spec's confirmation update, mapped to their
    images, are the votes of the image's pool that resolve before the support cutoff. -/
theorem early_map (st : OkStore V) (E : Env V) (hc : Protocol.HealConfig) (s : Slot) :
    ((st.val.pool s).filter (fun v => (match st.val.tau v with
        | .ok o => Spec.occurrenceBefore o
            ((Spec.Config.toSpec E hc unreadHeightConfig).gf_confirmation_time s)
        | .error _ => false) = true)).map Spec.GoldfishVote.toProofEmb =
      DecoupledConsensusModel.beforeCutoff (Protocol.Store.tau st.val.toProof)
        (Member.support_cutoff E s) (Member.store_pool st.val s) := by
  unfold DecoupledConsensusModel.beforeCutoff Member.store_pool
  rw [Finset.filter_map]
  congr 1
  apply Finset.filter_congr
  intro v hv
  rw [tau_eq_ok_of_stamped st (NoRaise.stamped_pool st.property.1 hv)]
  show Spec.occurrenceBefore (st.val.toProof.tau v.toProof) _ = true ↔
    DecoupledConsensusModel.stampedBefore st.val.toProof.tau _ v.toProof = true
  rw [Spec.stampedBefore_eq_occurrenceBefore]
  rfl

/-- On a store of the instance, the late votes of the spec's confirmation update are `ucLate` in the
    spec's vote type. -/
theorem late_eq (st : OkStore V) (E : Env V) (hc : Protocol.HealConfig) (s : Slot)
    {late : Finset (Spec.GoldfishVote V)}
    (h : Spec.beforeCutoff st.val.timestamp_vote
      ((Spec.Config.toSpec E hc unreadHeightConfig).confirmation_time s) (st.val.pool s)
        = .ok late) :
    late = (ucLate E st.val s).map ForkChoiceGrades.voteToSpecEmb := by
  rw [Spec.beforeCutoff_eq_ok _ _ _
    (fun v hv => NoRaise.stamped_pool st.property.1 hv)] at h
  have e := Except.ok.inj h
  subst e
  unfold ucLate Member.store_pool
  rw [show Member.store_timestamp_vote st.val =
      fun u => st.val.timestamp_vote (Spec.GoldfishVote.toSpec u) from rfl,
    ← ForkChoiceImages.beforeCutoff_map, ContractImages.map_toProofEmb_voteToSpec]
  rfl


/-- On a store of the instance whose late votes are `ucLate` in the spec's vote type, the support
    votes of the spec's confirmation update are `ucSupport` in that type. -/
theorem support_eq (st : OkStore V) (E : Env V) (hc : Protocol.HealConfig) (s : Slot)
    {late : Finset (Spec.GoldfishVote V)}
    (hl : late = (ucLate E st.val s).map ForkChoiceGrades.voteToSpecEmb) :
    ((st.val.pool s).filter (fun v => (match st.val.tau v with
        | .ok o => Spec.occurrenceBefore o
            ((Spec.Config.toSpec E hc unreadHeightConfig).gf_confirmation_time s)
        | .error _ => false) = true)).filter
        (fun v => Spec.Protocol.no_second_vote_in late v = true) =
      (ucSupport E st.val s).map ForkChoiceGrades.voteToSpecEmb := by
  have key : (((st.val.pool s).filter (fun v => (match st.val.tau v with
        | .ok o => Spec.occurrenceBefore o
            ((Spec.Config.toSpec E hc unreadHeightConfig).gf_confirmation_time s)
        | .error _ => false) = true)).filter
        (fun v => Spec.Protocol.no_second_vote_in late v = true)).map
          Spec.GoldfishVote.toProofEmb = ucSupport E st.val s := by
    unfold ucSupport
    rw [← early_map st E hc s, Finset.filter_map]
    congr 1
    apply Finset.filter_congr
    intro v _
    show _ ↔ Member.no_second_vote_in (ucLate E st.val s) v.toProof = true
    unfold Member.no_second_vote_in
    rw [← hl, Spec.GoldfishVote.toSpec_toProof]
  rw [← key, ContractImages.map_toProofEmb_voteToSpec]

/-- The spec's filtered tree of the contract store is the blocks `st.val.blockOfImage` gives for the
    member's filtered tree. -/
theorem filtered_contractStore (st : OkStore V) (c : Spec.SavedGrades V) (r : Round) :
    Spec.Protocol.get_filtered_block_tree (ContractImages.contractStore st.val c r) =
      (Member.get_filtered_block_tree st.val).map st.val.blockOfImageEmb := by
  have e : Spec.Protocol.get_filtered_block_tree (ContractImages.contractStore st.val c r) =
      Spec.Protocol.get_filtered_block_tree (Spec.Store.ofImage st.val) :=
    ForkChoiceImages.get_filtered_block_tree_congr rfl rfl rfl rfl rfl rfl
  rw [e]
  unfold Member.get_filtered_block_tree
  exact (ForkChoiceImages.image_map_blockOfImage_of_subset st
    (GradesImages.filtered_subset (Spec.Store.ofImage st.val))).symm

/-- On a store of the instance whose late and support votes are `ucLate` and `ucSupport` in the
    spec's type, the spec's eligibility test on the block standing for `C` answers `ucEligible C`,
    and its score answers `ucScore C`. -/
theorem score_elig_at (st : OkStore V) (E : Env V) (s : Slot) (T : Finset (Spec.Block V))
    (hTe : T = st.val.T) {late sup : Finset (Spec.GoldfishVote V)}
    (hl : late = (ucLate E st.val s).map ForkChoiceGrades.voteToSpecEmb)
    (hs : sup = (ucSupport E st.val s).map ForkChoiceGrades.voteToSpecEmb) :
    (∀ (C : Block V) (n : ℕ),
      Spec.Protocol.raw_goldfish_score T sup sup s (st.val.blockOfImageEmb C) = .ok n →
        n = ucScore E st.val s C) ∧
    (∀ (C : Block V) (b : Bool),
      (do
        let n ← Spec.Protocol.raw_goldfish_score T sup sup s (st.val.blockOfImageEmb C)
        return decide (Spec.Protocol.raw_voters_count late < 2 * n) : DC.DRE Bool) = .ok b →
        b = ucEligible E st.val s C) := by
  obtain ⟨-, hT, hpar, -⟩ := st.property
  have hinj := hT.injOn_toProof
  have hsc : ∀ (C : Block V) (n : ℕ),
      Spec.Protocol.raw_goldfish_score T sup sup s (st.val.blockOfImageEmb C) = .ok n →
        n = ucScore E st.val s C := by
    intro C n h
    rw [hTe, ContractImages.T_eq_map_blockOfImage st, hs] at h
    exact ForkChoiceImages.raw_goldfish_score_at st.val.blockOfImageEmb
      (Spec.Store.toProof_blockOfImage st.val)
      (Spec.Store.blockOfImage_ancestorEq st.val hinj hpar) E _ _ _ s C h
  refine ⟨hsc, fun C b h => ?_⟩
  cases hn : Spec.Protocol.raw_goldfish_score T sup sup s (st.val.blockOfImageEmb C) with
  | error e => rw [hn] at h; cases h
  | ok n =>
    rw [hn] at h
    have hb := Except.ok.inj h
    subst hb
    rw [hsc C n hn, hl]
    rfl

omit [Fintype V] in
/-- A block the confirmation update may write on the contract store stands for its image. -/
theorem good_fixed (st : OkStore V) (c : Spec.SavedGrades V) (r : Round)
    {X : Spec.Block V}
    (h : ContractImages.ConfirmationGood (ContractImages.contractStore st.val c r) X) :
    st.val.blockOfImage X.toProof = X := by
  rcases h with rfl | hm
  · have e : Spec.Protocol.get_fg_root (ContractImages.contractStore st.val c r) =
        Spec.Protocol.get_fg_root (Spec.Store.ofImage st.val) :=
      ForkChoiceImages.get_fg_root_congr rfl rfl rfl rfl
    rw [e, Spec.Store.get_fg_root_ofImage, Spec.Store.toProof_blockOfImage]
  · exact Spec.Store.blockOfImage_toProof_of_injOn st.val st.property.2.1.injOn_toProof
      (show X ∈ st.val.T from GradesImages.filtered_subset (ContractImages.contractStore st.val c r) hm)

omit [Fintype V] [Inhabited V] in
/-- The stable-record root that `round_stable_root` returns meets `ContractImages.ConfirmationGood`:
    it is the store's root or a block of the filtered tree. -/
theorem round_stable_root_good {st : Spec.Store V} {r : Spec.Round}
    {G : Spec.Block V} (h : Spec.Protocol.round_stable_root st r = .ok G) :
    ContractImages.ConfirmationGood st G := by
  unfold Spec.Protocol.round_stable_root at h
  obtain ⟨G2, -, h⟩ := NoRaise.DRE.of_bind_ok h
  rw [← Except.ok.inj h]
  unfold Spec.Protocol.stable_root
  simp only [Id.run, pure]
  split
  · rename_i hne
    obtain ⟨X, hX⟩ := Option.ne_none_iff_exists'.mp hne
    simp only [hX, Option.value]
    exact Or.inr (ContractImages.active_prefix_mem_filtered hX)
  · exact Or.inl rfl

omit [Fintype V] [Inhabited V] in
/-- The confirmation candidate that `confirmation_candidate` returns, when present, is a block of
    the filtered tree. -/
theorem confirmation_candidate_good {C : Spec.Config} {st : Spec.Store V}
    {S? : Option (Spec.Block V)}
    (h : Spec.Protocol.confirmation_candidate C st = .ok S?) {S : Spec.Block V}
    (hS : S? = some S) : ContractImages.ConfirmationGood st S := by
  unfold Spec.Protocol.confirmation_candidate at h
  obtain ⟨G2, -, h⟩ := NoRaise.DRE.of_bind_ok h
  rw [← Except.ok.inj h] at hS
  exact Or.inr (ContractImages.active_prefix_mem_filtered hS)

omit [Fintype V] [Inhabited V] in
/-- On a store of the instance, the spec's `advance_confirmed` on the blocks standing for `a` and
    `b` is the block standing for `Protocol.advance_confirmed a b`. -/
theorem advance_confirmed_ofImage (st : OkStore V) (a b : Block V) :
    Spec.Protocol.advance_confirmed (st.val.blockOfImage a) (st.val.blockOfImage b) =
      st.val.blockOfImage (Protocol.advance_confirmed a b) := by
  obtain ⟨-, hT, hpar, -⟩ := st.property
  unfold Spec.Protocol.advance_confirmed Protocol.advance_confirmed
  simp only [Id.run, pure]
  rw [Spec.Store.blockOfImage_ancestorEq_of_distinctRoots _ hT hpar]
  split <;> rfl

omit [Fintype V] [Inhabited V] in
/-- On a store of the instance, the spec's `floor_on_stable` on the blocks standing for `a`, `b` and
    `d` is the block standing for `Protocol.floor_on_stable` of them. -/
theorem floor_on_stable_ofImage (st : OkStore V) (a b d : Block V) :
    Spec.Protocol.floor_on_stable (st.val.blockOfImage a) (st.val.blockOfImage b)
        (st.val.blockOfImage d) =
      st.val.blockOfImage (Protocol.floor_on_stable a b d) := by
  obtain ⟨-, hT, hpar, -⟩ := st.property
  unfold Spec.Protocol.floor_on_stable Protocol.floor_on_stable
  simp only [Id.run, pure]
  rw [Spec.Store.blockOfImage_ancestorEq_of_distinctRoots _ hT hpar,
    Spec.Store.blockOfImage_ancestorEq_of_distinctRoots _ hT hpar]
  split_ifs <;> rfl


/-- At a store `st` of the instance, an outcome `st'` of the member `update_confirmation_with`
    writes, read at the image: as live confirmed, the walk's head `W` from the SG root `R` through
    the member's filtered tree with the score `ucScore` when `W` passes `ucEligible`, and the root
    `get_fg_root` otherwise; the stable record moved to the stable root `G` that `stableRoot`
    returns; and the confirmation record floored on the new stable record, from the record moved to
    `W` (when eligible) or to the candidate that `confirmationSG` returns, or the record as it was. -/
theorem update_confirmation_with_image (st : OkStore V) (c : Spec.SavedGrades V)
    (E : Env V) (hc : Protocol.HealConfig) (s : Slot) {st' : Spec.Store V}
    (h : Returns (Member.update_confirmation_with c E hc st.val s) st') {R : Block V}
    (hR : Returns (Member.get_sg_root_with c E hc st.val
      ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.val.s)) R) :
    ∃ (G : Block V) (S? : Option (Block V)),
      Returns (Member.stableRoot c E hc st.val
        ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.val.s)) (some G) ∧
      Returns (Member.confirmationSG c E hc st.val s) S? ∧
      st'.live_confirmed.toProof =
        (if ucEligible E st.val s (Protocol.ghost R (Member.get_filtered_block_tree st.val)
            (ucScore E st.val s) (ucEligible E st.val s)) then
          Protocol.ghost R (Member.get_filtered_block_tree st.val) (ucScore E st.val s)
            (ucEligible E st.val s)
        else Member.get_fg_root st.val) ∧
      st'.latest_stable.toProof = Protocol.advance_confirmed st.val.latest_stable.toProof G ∧
      st'.latest_confirmed.toProof =
        Protocol.floor_on_stable (Protocol.advance_confirmed st.val.latest_stable.toProof G)
          (if ucEligible E st.val s (Protocol.ghost R (Member.get_filtered_block_tree st.val)
              (ucScore E st.val s) (ucEligible E st.val s)) then
            Protocol.advance_confirmed st.val.latest_confirmed.toProof
              (Protocol.ghost R (Member.get_filtered_block_tree st.val) (ucScore E st.val s)
                (ucEligible E st.val s))
          else
            match S? with
            | some S => Protocol.advance_confirmed st.val.latest_confirmed.toProof S
            | none => st.val.latest_confirmed.toProof)
          st.val.latest_confirmed.toProof := by
  obtain ⟨-, hT, hpar, -⟩ := st.property
  have hinj := hT.injOn_toProof
  set C := Spec.Config.toSpec E hc unreadHeightConfig with hCdef
  set r := C.round_of st.val.s with hrdef
  unfold Member.update_confirmation_with at h
  rw [returns_successOutcomes] at h
  obtain ⟨out, hout, e⟩ := ContractImages.except_map_eq_ok h
  subst e
  obtain ⟨early, late, A, H, G, hel, S?, hearly, hl, hA, hH, hhel, hG, hS, hlive, hstab, hconf⟩ :=
    update_confirmation_trace hout
  have hl' := late_eq st E hc s hl
  have hsup : early.filter (fun v => Spec.Protocol.no_second_vote_in late v = true) =
      (ucSupport E st.val s).map ForkChoiceGrades.voteToSpecEmb := by
    rw [hearly]; exact support_eq st E hc s hl'
  -- the SG root
  obtain ⟨A', hA', rfl⟩ := ContractImages.get_sg_root_with_shape hR
  rw [ContractImages.get_sg_root_with_eq_anchor] at hA
  have hAA : A = A' := Except.ok.inj (hA.symm.trans hA')
  subst hAA
  have hAfix : st.val.blockOfImage A.toProof = A := ContractImages.contractStore_anchor_fixed st c r hA'
  -- the walk
  obtain ⟨hsc, hel'⟩ := score_elig_at st E s (ContractImages.contractStore st.val c r).T rfl hl'
    (sup := (ucSupport E st.val s).map ForkChoiceGrades.voteToSpecEmb) rfl
  rw [filtered_contractStore st c r, hsup] at hH
  rw [hsup] at hhel
  have hH' : Spec.Protocol.ghost (st.val.blockOfImageEmb A.toProof)
      ((Member.get_filtered_block_tree st.val).map st.val.blockOfImageEmb)
      (Spec.Protocol.raw_goldfish_score (ContractImages.contractStore st.val c r).T
        ((ucSupport E st.val s).map ForkChoiceGrades.voteToSpecEmb)
        ((ucSupport E st.val s).map ForkChoiceGrades.voteToSpecEmb) s)
      (fun B => do
        let n ← Spec.Protocol.raw_goldfish_score (ContractImages.contractStore st.val c r).T
          ((ucSupport E st.val s).map ForkChoiceGrades.voteToSpecEmb)
          ((ucSupport E st.val s).map ForkChoiceGrades.voteToSpecEmb) s B
        return decide (Spec.Protocol.raw_voters_count late < 2 * n)) = .ok H := by
    rw [Spec.Store.coe_blockOfImageEmb, hAfix]; exact hH
  have hHW := ForkChoiceImages.ghost_at st.val.blockOfImageEmb
    (Spec.Store.toProof_blockOfImage st.val)
    (ForkChoiceImages.parent?_iff_at st.val.blockOfImageEmb
      (Spec.Store.toProof_blockOfImage st.val)
      (fun B => (Spec.Store.blockOfImage_parent st.val hinj hpar B).symm))
    _ _ _ _ hsc hel' A.toProof (Member.get_filtered_block_tree st.val) hH'
  set W := Protocol.ghost A.toProof (Member.get_filtered_block_tree st.val) (ucScore E st.val s)
    (ucEligible E st.val s) with hWdef
  rw [hHW] at hhel
  have hhelW : hel = ucEligible E st.val s W := hel' W hel hhel
  have hGfix := good_fixed st c r (round_stable_root_good hG)
  refine ⟨G.toProof, S?.map Spec.Block.toProof, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Member.stableRoot
    rw [returns_successOutcomes]
    have hG' : Spec.Protocol.round_stable_root
        (ContractImages.contractStore st.val c r) r = .ok G := hG
    show Except.map _ (Spec.Protocol.round_stable_root
      (ContractImages.contractStore st.val c r) r) = _
    rw [hG']
    rfl
  · unfold Member.confirmationSG
    rw [returns_successOutcomes]
    have hS' : Spec.Protocol.confirmation_candidate C
        (ContractImages.contractStore st.val c r) = .ok S? := hS
    show Except.map _ (Spec.Protocol.confirmation_candidate C
      (ContractImages.contractStore st.val c r)) = _
    rw [hS']
    rfl
  · show out.live_confirmed.toProof = _
    rw [hlive, hhelW]
    split
    · rw [hHW]; exact Spec.Store.toProof_blockOfImage st.val W
    · unfold Member.get_fg_root
      congr 1
  · have hadv : Spec.Protocol.advance_confirmed
        (st.val.blockOfImage st.val.latest_stable.toProof) G =
        st.val.blockOfImage (Protocol.advance_confirmed st.val.latest_stable.toProof G.toProof) := by
      have := advance_confirmed_ofImage st st.val.latest_stable.toProof G.toProof
      rwa [hGfix] at this
    show out.latest_stable.toProof = _
    rw [hstab]
    show (Spec.Protocol.advance_confirmed
      (st.val.blockOfImage st.val.latest_stable.toProof) G).toProof = _
    rw [hadv, Spec.Store.toProof_blockOfImage]
  · have hadv : Spec.Protocol.advance_confirmed
        (st.val.blockOfImage st.val.latest_stable.toProof) G =
        st.val.blockOfImage (Protocol.advance_confirmed st.val.latest_stable.toProof G.toProof) := by
      have := advance_confirmed_ofImage st st.val.latest_stable.toProof G.toProof
      rwa [hGfix] at this
    show out.latest_confirmed.toProof = _
    rw [hconf, hhelW]
    split
    · show (Spec.Protocol.floor_on_stable
        (Spec.Protocol.advance_confirmed
          (st.val.blockOfImage st.val.latest_stable.toProof) G)
        (Spec.Protocol.advance_confirmed
          (st.val.blockOfImage st.val.latest_confirmed.toProof) H)
        (st.val.blockOfImage st.val.latest_confirmed.toProof)).toProof = _
      rw [hadv, hHW, Spec.Store.coe_blockOfImageEmb, advance_confirmed_ofImage,
        floor_on_stable_ofImage, Spec.Store.toProof_blockOfImage]
    · cases hS? : S? with
      | none =>
        show (Spec.Protocol.floor_on_stable
          (Spec.Protocol.advance_confirmed
            (st.val.blockOfImage st.val.latest_stable.toProof) G)
          (st.val.blockOfImage st.val.latest_confirmed.toProof)
          (st.val.blockOfImage st.val.latest_confirmed.toProof)).toProof = _
        rw [hadv, floor_on_stable_ofImage, Spec.Store.toProof_blockOfImage]
        rfl
      | some S =>
        have hSfix := good_fixed st c r (confirmation_candidate_good hS hS?)
        have hadvS : Spec.Protocol.advance_confirmed
            (st.val.blockOfImage st.val.latest_confirmed.toProof) S =
            st.val.blockOfImage
              (Protocol.advance_confirmed st.val.latest_confirmed.toProof S.toProof) := by
          have := advance_confirmed_ofImage st st.val.latest_confirmed.toProof S.toProof
          rwa [hSfix] at this
        show (Spec.Protocol.floor_on_stable
          (Spec.Protocol.advance_confirmed
            (st.val.blockOfImage st.val.latest_stable.toProof) G)
          (Spec.Protocol.advance_confirmed
            (st.val.blockOfImage st.val.latest_confirmed.toProof) S)
          (st.val.blockOfImage st.val.latest_confirmed.toProof)).toProof = _
        rw [hadv, hadvS, floor_on_stable_ofImage, Spec.Store.toProof_blockOfImage]
        rfl


/-! ## The confirmation update's fields -/

omit [Inhabited V] in
/-- An outcome of the member `update_confirmation_with` comes with an outcome of the member
    `get_sg_root_with` at the store's round. -/
theorem exists_sg_root_of_update (st : OkStore V) (c : Spec.SavedGrades V) (E : Env V)
    (hc : Protocol.HealConfig) (s : Slot) {st' : Spec.Store V}
    (h : Returns (Member.update_confirmation_with c E hc st.val s) st') :
    ∃ R, Returns (Member.get_sg_root_with c E hc st.val
      ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.val.s)) R := by
  unfold Member.update_confirmation_with at h
  rw [returns_successOutcomes] at h
  obtain ⟨out, hout, -⟩ := ContractImages.except_map_eq_ok h
  obtain ⟨-, -, A, -, -, -, -, -, -, hA, -⟩ := update_confirmation_trace hout
  rw [ContractImages.get_sg_root_with_eq_anchor] at hA
  refine ⟨A.toProof, ?_⟩
  unfold Member.get_sg_root_with
  rw [returns_successOutcomes]
  show Except.map _ (Spec.Protocol.anchor
    (ContractImages.contractStore st.val c
      ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.val.s)) _) = _
  have hA' : Spec.Protocol.anchor (ContractImages.contractStore st.val c
      ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.val.s))
      (Spec.Protocol.round_grades (ContractImages.contractStore st.val c
        ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.val.s))
        ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.val.s)).g1 = .ok A := hA
  rw [hA']
  rfl

omit [Inhabited V] in
/-- Two outcomes of the member `stableRoot` are equal. -/
theorem stableRoot_unique {c : Spec.SavedGrades V} {E : Env V} {hc : Protocol.HealConfig}
    {st : Spec.Store V} {r : Round} {x y : Option (Block V)}
    (hx : Returns (Member.stableRoot c E hc st r) x) (hy : Returns (Member.stableRoot c E hc st r) y) :
    x = y := by
  unfold Member.stableRoot at hx hy
  rw [returns_successOutcomes] at hx hy
  exact Except.ok.inj (hx.symm.trans hy)

/-- The field `update_confirmation_with_live_confirmed_walk_or_fgRoot` of `HandlersFacts` at
    `Model.spec`: the confirmation update records as live confirmed either the walk's head or
    the root `get_fg_root`. -/
theorem spec_update_confirmation_with_live_confirmed_walk_or_fgRoot : ∀ (contract : (Model.spec (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (st : (Model.spec (V := V)).S) (s : Slot)
    (tm : TimestampMap (GoldfishVote V)) (htm : st.tau ⇢ tm)
    (R : Block V) (hR : (Model.spec (V := V)).get_sg_root_with contract E hc st.toHealing ((Model.spec (V := V)).round_of hc st.s) ⇢ R)
    (score : Block V → ℕ)
    (hscore : ∀ B, (Model.spec (V := V)).goldfish_score E st.T
      ((_root_.DecoupledConsensusModel.beforeCutoff tm ((Model.spec (V := V)).support_cutoff E s) (st.pool s)).filter (fun u => (Model.spec (V := V)).no_second_vote_in (_root_.DecoupledConsensusModel.beforeCutoff st.timestamp_vote ((Model.spec (V := V)).confirmation_time E s) (st.pool s)) u = true))
      ((_root_.DecoupledConsensusModel.beforeCutoff tm ((Model.spec (V := V)).support_cutoff E s) (st.pool s)).filter (fun u => (Model.spec (V := V)).no_second_vote_in (_root_.DecoupledConsensusModel.beforeCutoff st.timestamp_vote ((Model.spec (V := V)).confirmation_time E s) (st.pool s)) u = true))
      s B ⇢ score B)
    (W : Block V) (hW : (Model.spec (V := V)).ghost R ((Model.spec (V := V)).get_filtered_block_tree st.toHealing.toFG) score
      (fun B => decide ((Model.spec (V := V)).voters_count E (_root_.DecoupledConsensusModel.beforeCutoff st.timestamp_vote ((Model.spec (V := V)).confirmation_time E s) (st.pool s)) s < 2 * score B)) ⇢ W)
    (st' : (Model.spec (V := V)).S) (hst' : (Model.spec (V := V)).update_confirmation_with contract E hc st s ⇢ st'),
    st'.live_confirmed = W ∨ st'.live_confirmed = (Model.spec (V := V)).get_fg_root ((Model.spec (V := V)).toHealing st).toFG := by
  intro contract E hc st s tm htm R hR score hscore W hW st' hst'
  obtain rfl := StoreFacts.tm_eq_of_returns st htm
  have hR' : Returns (Member.get_sg_root_with contract E hc st.val
      ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.val.s)) R := by
    rw [← round_of_store E hc st]; exact hR
  obtain rfl : score = ucScore E st.val s := funext fun B => by
    have h := hscore B
    rw [ForkChoiceImages.spec_goldfish_score_eq] at h
    exact (returns_pure _ _).1 h
  rw [ForkChoiceImages.spec_ghost_eq] at hW
  obtain rfl := (returns_pure _ _).1 hW
  obtain ⟨G, S?, -, -, hlive, -, -⟩ := update_confirmation_with_image st contract E hc s hst' hR'
  show st'.val.live_confirmed.toProof = _ ∨ st'.val.live_confirmed.toProof = Member.get_fg_root st.val
  rw [hlive]
  split
  · exact Or.inl rfl
  · exact Or.inr rfl


/-- The field `update_confirmation_with_live_confirmed_genuine_or_fgRoot` of `HandlersFacts` at
    `Model.spec`: the confirmation update records as live confirmed the walk's head when it
    passes the eligibility test, and the root `get_fg_root` otherwise. -/
theorem spec_update_confirmation_with_live_confirmed_genuine_or_fgRoot : ∀ (contract : (Model.spec (V := V)).Contract) (E : Env V)
    (hc : Protocol.HealConfig) (st : (Model.spec (V := V)).S) (s : Slot)
    (tm : TimestampMap (GoldfishVote V)) (htm : st.tau ⇢ tm)
    (R : Block V) (hR : (Model.spec (V := V)).get_sg_root_with contract E hc st.toHealing ((Model.spec (V := V)).round_of hc st.s) ⇢ R)
    (score : Block V → ℕ)
    (hscore : ∀ B, (Model.spec (V := V)).goldfish_score E st.T
      ((_root_.DecoupledConsensusModel.beforeCutoff tm ((Model.spec (V := V)).support_cutoff E s) (st.pool s)).filter (fun u => (Model.spec (V := V)).no_second_vote_in (_root_.DecoupledConsensusModel.beforeCutoff st.timestamp_vote ((Model.spec (V := V)).confirmation_time E s) (st.pool s)) u = true))
      ((_root_.DecoupledConsensusModel.beforeCutoff tm ((Model.spec (V := V)).support_cutoff E s) (st.pool s)).filter (fun u => (Model.spec (V := V)).no_second_vote_in (_root_.DecoupledConsensusModel.beforeCutoff st.timestamp_vote ((Model.spec (V := V)).confirmation_time E s) (st.pool s)) u = true))
      s B ⇢ score B)
    (W : Block V) (hW : (Model.spec (V := V)).ghost R ((Model.spec (V := V)).get_filtered_block_tree st.toHealing.toFG) score
      (fun B => decide ((Model.spec (V := V)).voters_count E (_root_.DecoupledConsensusModel.beforeCutoff st.timestamp_vote ((Model.spec (V := V)).confirmation_time E s) (st.pool s)) s < 2 * score B)) ⇢ W)
    (st' : (Model.spec (V := V)).S) (hst' : (Model.spec (V := V)).update_confirmation_with contract E hc st s ⇢ st'),
    (∃ C : Block V, st'.live_confirmed = C ∧
        decide ((Model.spec (V := V)).voters_count E (_root_.DecoupledConsensusModel.beforeCutoff st.timestamp_vote ((Model.spec (V := V)).confirmation_time E s) (st.pool s)) s < 2 * score W) = true) ∨
      st'.live_confirmed = (Model.spec (V := V)).get_fg_root ((Model.spec (V := V)).toHealing st).toFG := by
  intro contract E hc st s tm htm R hR score hscore W hW st' hst'
  obtain rfl := StoreFacts.tm_eq_of_returns st htm
  have hR' : Returns (Member.get_sg_root_with contract E hc st.val
      ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.val.s)) R := by
    rw [← round_of_store E hc st]; exact hR
  obtain rfl : score = ucScore E st.val s := funext fun B => by
    have h := hscore B
    rw [ForkChoiceImages.spec_goldfish_score_eq] at h
    exact (returns_pure _ _).1 h
  rw [ForkChoiceImages.spec_ghost_eq] at hW
  obtain rfl := (returns_pure _ _).1 hW
  obtain ⟨G, S?, -, -, hlive, -, -⟩ := update_confirmation_with_image st contract E hc s hst' hR'
  by_cases hE : ucEligible E st.val s (Protocol.ghost R (Member.get_filtered_block_tree st.val)
      (ucScore E st.val s) (ucEligible E st.val s)) = true
  · exact Or.inl ⟨_, rfl, hE⟩
  · right
    show st'.val.live_confirmed.toProof = Member.get_fg_root st.val
    rw [hlive, if_neg hE]


/-- The field `update_confirmation_with_live_confirmed_of_eligible` of `HandlersFacts` at
    `Model.spec`: when the walk's head passes the eligibility test, the confirmation update
    records it as live confirmed. -/
theorem spec_update_confirmation_with_live_confirmed_of_eligible : ∀ (contract : (Model.spec (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (st : (Model.spec (V := V)).S) (s : Slot)
    (tm : TimestampMap (GoldfishVote V)) (htm : st.tau ⇢ tm)
    (R : Block V) (hR : (Model.spec (V := V)).get_sg_root_with contract E hc st.toHealing ((Model.spec (V := V)).round_of hc st.s) ⇢ R)
    (score : Block V → ℕ)
    (hscore : ∀ B, (Model.spec (V := V)).goldfish_score E st.T
      ((_root_.DecoupledConsensusModel.beforeCutoff tm ((Model.spec (V := V)).support_cutoff E s) (st.pool s)).filter (fun u => (Model.spec (V := V)).no_second_vote_in (_root_.DecoupledConsensusModel.beforeCutoff st.timestamp_vote ((Model.spec (V := V)).confirmation_time E s) (st.pool s)) u = true))
      ((_root_.DecoupledConsensusModel.beforeCutoff tm ((Model.spec (V := V)).support_cutoff E s) (st.pool s)).filter (fun u => (Model.spec (V := V)).no_second_vote_in (_root_.DecoupledConsensusModel.beforeCutoff st.timestamp_vote ((Model.spec (V := V)).confirmation_time E s) (st.pool s)) u = true))
      s B ⇢ score B)
    (W : Block V) (hW : (Model.spec (V := V)).ghost R ((Model.spec (V := V)).get_filtered_block_tree st.toHealing.toFG) score
      (fun B => decide ((Model.spec (V := V)).voters_count E (_root_.DecoupledConsensusModel.beforeCutoff st.timestamp_vote ((Model.spec (V := V)).confirmation_time E s) (st.pool s)) s < 2 * score B)) ⇢ W),
    decide ((Model.spec (V := V)).voters_count E (_root_.DecoupledConsensusModel.beforeCutoff st.timestamp_vote ((Model.spec (V := V)).confirmation_time E s) (st.pool s)) s < 2 * score W) = true →
    ∀ (st' : (Model.spec (V := V)).S), (Model.spec (V := V)).update_confirmation_with contract E hc st s ⇢ st' →
    st'.live_confirmed = W := by
  intro contract E hc st s tm htm R hR score hscore W hW hE st' hst'
  obtain rfl := StoreFacts.tm_eq_of_returns st htm
  have hR' : Returns (Member.get_sg_root_with contract E hc st.val
      ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.val.s)) R := by
    rw [← round_of_store E hc st]; exact hR
  obtain rfl : score = ucScore E st.val s := funext fun B => by
    have h := hscore B
    rw [ForkChoiceImages.spec_goldfish_score_eq] at h
    exact (returns_pure _ _).1 h
  rw [ForkChoiceImages.spec_ghost_eq] at hW
  obtain rfl := (returns_pure _ _).1 hW
  replace hE : ucEligible E st.val s (Protocol.ghost R (Member.get_filtered_block_tree st.val) (ucScore E st.val s) (ucEligible E st.val s)) = true := hE
  obtain ⟨G, S?, -, -, hlive, -, -⟩ := update_confirmation_with_image st contract E hc s hst' hR'
  show st'.val.live_confirmed.toProof = _
  rw [hlive, if_pos hE]
  rfl


/-- The field `update_confirmation_with_latest_confirmed_cases` of `HandlersFacts` at
    `Model.spec`: the new confirmation record is the floor, on the new stable record, of the
    old record, of the old record moved to the eligible walk's head, or of the old record moved to
    the SG candidate. -/
theorem spec_update_confirmation_with_latest_confirmed_cases : ∀ (contract : (Model.spec (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (st : (Model.spec (V := V)).S) (s : Slot)
    (tm : TimestampMap (GoldfishVote V)) (htm : st.tau ⇢ tm)
    (R : Block V) (hR : (Model.spec (V := V)).get_sg_root_with contract E hc st.toHealing ((Model.spec (V := V)).round_of hc st.s) ⇢ R)
    (score : Block V → ℕ)
    (hscore : ∀ B, (Model.spec (V := V)).goldfish_score E st.T
      ((_root_.DecoupledConsensusModel.beforeCutoff tm ((Model.spec (V := V)).support_cutoff E s) (st.pool s)).filter (fun u => (Model.spec (V := V)).no_second_vote_in (_root_.DecoupledConsensusModel.beforeCutoff st.timestamp_vote ((Model.spec (V := V)).confirmation_time E s) (st.pool s)) u = true))
      ((_root_.DecoupledConsensusModel.beforeCutoff tm ((Model.spec (V := V)).support_cutoff E s) (st.pool s)).filter (fun u => (Model.spec (V := V)).no_second_vote_in (_root_.DecoupledConsensusModel.beforeCutoff st.timestamp_vote ((Model.spec (V := V)).confirmation_time E s) (st.pool s)) u = true))
      s B ⇢ score B)
    (W : Block V) (hW : (Model.spec (V := V)).ghost R ((Model.spec (V := V)).get_filtered_block_tree st.toHealing.toFG) score
      (fun B => decide ((Model.spec (V := V)).voters_count E (_root_.DecoupledConsensusModel.beforeCutoff st.timestamp_vote ((Model.spec (V := V)).confirmation_time E s) (st.pool s)) s < 2 * score B)) ⇢ W)
    (st' : (Model.spec (V := V)).S) (hst' : (Model.spec (V := V)).update_confirmation_with contract E hc st s ⇢ st'),
    ∃ cand : Block V,
      st'.latest_confirmed = (Model.spec (V := V)).floor_on_stable st'.latest_stable cand st.latest_confirmed ∧
      (cand = st.latest_confirmed ∨
        (decide ((Model.spec (V := V)).voters_count E (_root_.DecoupledConsensusModel.beforeCutoff st.timestamp_vote ((Model.spec (V := V)).confirmation_time E s) (st.pool s)) s < 2 * score W) = true ∧
          cand = (Model.spec (V := V)).advance_confirmed st.latest_confirmed W) ∨
        ∃ G : Block V, contract.confirmationSG E hc st.toHealing s ⇢ some G ∧
          cand = (Model.spec (V := V)).advance_confirmed st.latest_confirmed G) := by
  intro contract E hc st s tm htm R hR score hscore W hW st' hst'
  obtain rfl := StoreFacts.tm_eq_of_returns st htm
  have hR' : Returns (Member.get_sg_root_with contract E hc st.val
      ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.val.s)) R := by
    rw [← round_of_store E hc st]; exact hR
  obtain rfl : score = ucScore E st.val s := funext fun B => by
    have h := hscore B
    rw [ForkChoiceImages.spec_goldfish_score_eq] at h
    exact (returns_pure _ _).1 h
  rw [ForkChoiceImages.spec_ghost_eq] at hW
  obtain rfl := (returns_pure _ _).1 hW
  obtain ⟨G, S?, -, hS, -, hls, hlc⟩ := update_confirmation_with_image st contract E hc s hst' hR'
  by_cases hE : ucEligible E st.val s (Protocol.ghost R (Member.get_filtered_block_tree st.val)
      (ucScore E st.val s) (ucEligible E st.val s)) = true
  · refine ⟨Protocol.advance_confirmed st.val.latest_confirmed.toProof
      (Protocol.ghost R (Member.get_filtered_block_tree st.val) (ucScore E st.val s)
        (ucEligible E st.val s)), ?_, Or.inr (Or.inl ⟨hE, (image_advance_confirmed _ _).symm⟩)⟩
    show st'.val.latest_confirmed.toProof = Member.floor_on_stable st'.val.latest_stable.toProof
      (Protocol.advance_confirmed st.val.latest_confirmed.toProof (Protocol.ghost R (Member.get_filtered_block_tree st.val) (ucScore E st.val s) (ucEligible E st.val s)))
      st.val.latest_confirmed.toProof
    rw [image_floor_on_stable, hlc, hls, if_pos hE]
  · cases hS? : S? with
    | none =>
      refine ⟨st.val.latest_confirmed.toProof, ?_, Or.inl rfl⟩
      show st'.val.latest_confirmed.toProof = Member.floor_on_stable st'.val.latest_stable.toProof
        st.val.latest_confirmed.toProof st.val.latest_confirmed.toProof
      rw [image_floor_on_stable, hlc, hls, if_neg hE, hS?]
    | some S =>
      refine ⟨Protocol.advance_confirmed st.val.latest_confirmed.toProof S, ?_,
        Or.inr (Or.inr ⟨S, hS? ▸ hS, (image_advance_confirmed _ _).symm⟩)⟩
      show st'.val.latest_confirmed.toProof = Member.floor_on_stable st'.val.latest_stable.toProof
        (Protocol.advance_confirmed st.val.latest_confirmed.toProof S) st.val.latest_confirmed.toProof
      rw [image_floor_on_stable, hlc, hls, if_neg hE, hS?]


/-- The field `update_confirmation_with_latest_confirmed_of_eligible` of `HandlersFacts` at
    `Model.spec`: when the walk's head is eligible, the new confirmation record is the floor,
    on the new stable record, of the old record moved to that head. -/
theorem spec_update_confirmation_with_latest_confirmed_of_eligible : ∀ (contract : (Model.spec (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (st : (Model.spec (V := V)).S) (s : Slot)
    (tm : TimestampMap (GoldfishVote V)) (htm : st.tau ⇢ tm)
    (R : Block V) (hR : (Model.spec (V := V)).get_sg_root_with contract E hc st.toHealing ((Model.spec (V := V)).round_of hc st.s) ⇢ R)
    (score : Block V → ℕ)
    (hscore : ∀ B, (Model.spec (V := V)).goldfish_score E st.T
      ((_root_.DecoupledConsensusModel.beforeCutoff tm ((Model.spec (V := V)).support_cutoff E s) (st.pool s)).filter (fun u => (Model.spec (V := V)).no_second_vote_in (_root_.DecoupledConsensusModel.beforeCutoff st.timestamp_vote ((Model.spec (V := V)).confirmation_time E s) (st.pool s)) u = true))
      ((_root_.DecoupledConsensusModel.beforeCutoff tm ((Model.spec (V := V)).support_cutoff E s) (st.pool s)).filter (fun u => (Model.spec (V := V)).no_second_vote_in (_root_.DecoupledConsensusModel.beforeCutoff st.timestamp_vote ((Model.spec (V := V)).confirmation_time E s) (st.pool s)) u = true))
      s B ⇢ score B)
    (W : Block V) (hW : (Model.spec (V := V)).ghost R ((Model.spec (V := V)).get_filtered_block_tree st.toHealing.toFG) score
      (fun B => decide ((Model.spec (V := V)).voters_count E (_root_.DecoupledConsensusModel.beforeCutoff st.timestamp_vote ((Model.spec (V := V)).confirmation_time E s) (st.pool s)) s < 2 * score B)) ⇢ W),
    decide ((Model.spec (V := V)).voters_count E (_root_.DecoupledConsensusModel.beforeCutoff st.timestamp_vote ((Model.spec (V := V)).confirmation_time E s) (st.pool s)) s < 2 * score W) = true →
    ∀ (st' : (Model.spec (V := V)).S), (Model.spec (V := V)).update_confirmation_with contract E hc st s ⇢ st' →
    st'.latest_confirmed = (Model.spec (V := V)).floor_on_stable st'.latest_stable
      ((Model.spec (V := V)).advance_confirmed st.latest_confirmed W) st.latest_confirmed := by
  intro contract E hc st s tm htm R hR score hscore W hW hE st' hst'
  obtain rfl := StoreFacts.tm_eq_of_returns st htm
  have hR' : Returns (Member.get_sg_root_with contract E hc st.val
      ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.val.s)) R := by
    rw [← round_of_store E hc st]; exact hR
  obtain rfl : score = ucScore E st.val s := funext fun B => by
    have h := hscore B
    rw [ForkChoiceImages.spec_goldfish_score_eq] at h
    exact (returns_pure _ _).1 h
  rw [ForkChoiceImages.spec_ghost_eq] at hW
  obtain rfl := (returns_pure _ _).1 hW
  replace hE : ucEligible E st.val s (Protocol.ghost R (Member.get_filtered_block_tree st.val) (ucScore E st.val s) (ucEligible E st.val s)) = true := hE
  obtain ⟨G, S?, -, -, -, hls, hlc⟩ := update_confirmation_with_image st contract E hc s hst' hR'
  show st'.val.latest_confirmed.toProof = Member.floor_on_stable st'.val.latest_stable.toProof
    (Member.advance_confirmed st.val.latest_confirmed.toProof (Protocol.ghost R (Member.get_filtered_block_tree st.val) (ucScore E st.val s) (ucEligible E st.val s))) st.val.latest_confirmed.toProof
  rw [image_floor_on_stable, image_advance_confirmed, hlc, hls, if_pos hE]


/-- The field `update_confirmation_with_latest_stable_of_root` of `HandlersFacts` at
    `Model.spec`: the new stable record is the old one moved to the round's stable root. -/
theorem spec_update_confirmation_with_latest_stable_of_root : ∀ (contract : (Model.spec (V := V)).Contract) (E : Env V)
    (hc : Protocol.HealConfig) (st : (Model.spec (V := V)).S) (s : Slot) {G : Block V},
    ∀ x : Option (Block V), contract.stableRoot E hc st.toHealing ((Model.spec (V := V)).round_of hc st.s) ⇢ x →
    x = some G →
    ∀ st' : (Model.spec (V := V)).S, (Model.spec (V := V)).update_confirmation_with contract E hc st s ⇢ st' →
    st'.latest_stable =
      (Model.spec (V := V)).advance_confirmed st.latest_stable G := by
  intro contract E hc st s G x hx hxG st' hst'
  obtain ⟨R, hR'⟩ := exists_sg_root_of_update st contract E hc s hst'
  obtain ⟨G', S?, hG', -, -, hls, hlc⟩ := update_confirmation_with_image st contract E hc s hst' hR'
  have hx' : Returns (Member.stableRoot contract E hc st.val
      ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.val.s)) x := by
    rw [← round_of_store E hc st]; exact hx
  have e := stableRoot_unique hx' hG'
  rw [hxG] at e
  obtain rfl := Option.some.inj e
  show st'.val.latest_stable.toProof = Member.advance_confirmed st.val.latest_stable.toProof G
  rw [image_advance_confirmed, hls]


/-- The field `update_confirmation_with_keeps_stable_of_root_preceq` of `HandlersFacts` at
    `Model.spec`: when the round's stable root is an ancestor of the stable record, the update
    keeps the stable record, and the new confirmation record is a descendant of it. -/
theorem spec_update_confirmation_with_keeps_stable_of_root_preceq : ∀ (contract : (Model.spec (V := V)).Contract) (E : Env V)
    (hc : Protocol.HealConfig) (st : (Model.spec (V := V)).S) (s : Slot) {G : Block V},
    ∀ x : Option (Block V), contract.stableRoot E hc st.toHealing ((Model.spec (V := V)).round_of hc st.s) ⇢ x →
    x = some G →
    Block.Preceq G st.latest_stable →
    ∀ st' : (Model.spec (V := V)).S, (Model.spec (V := V)).update_confirmation_with contract E hc st s ⇢ st' →
    st'.latest_stable = st.latest_stable ∧
      Block.Preceq st.latest_stable st'.latest_confirmed := by
  intro contract E hc st s G x hx hxG hGo st' hst'
  obtain ⟨R, hR'⟩ := exists_sg_root_of_update st contract E hc s hst'
  obtain ⟨G', S?, hG', -, -, hls, hlc⟩ := update_confirmation_with_image st contract E hc s hst' hR'
  have hx' : Returns (Member.stableRoot contract E hc st.val
      ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.val.s)) x := by
    rw [← round_of_store E hc st]; exact hx
  have e := stableRoot_unique hx' hG'
  rw [hxG] at e
  obtain rfl := Option.some.inj e
  have hadv : Protocol.advance_confirmed st.val.latest_stable.toProof G =
      st.val.latest_stable.toProof :=
    _root_.DecoupledConsensusModel.Sts.advance_confirmed_of_preceq hGo
  have hstab : st'.val.latest_stable.toProof = st.val.latest_stable.toProof := by
    rw [hls, hadv]
  refine ⟨hstab, ?_⟩
  show Block.Preceq st.val.latest_stable.toProof st'.val.latest_confirmed.toProof
  rw [hlc, hadv]
  exact _root_.DecoupledConsensusModel.Sts.floor_on_stable_stable_preceq _ _ _


/-- The grade contract whose SG root is `R` at every store and round: its grade read has the anchor
    `R`, no grade-2 candidate, every block clear and no raw grade-2; its SG vote is `R`, and it
    offers no confirmation candidate and no stable root. -/
def anchorContract (R : Block V) : Protocol.GradeContract V where
  read := fun _ _ _ _ => ⟨R, none, fun _ => true, False, inferInstance⟩
  sgVote := fun _ _ => R
  confirmationSG := .optional (fun _ _ _ _ => none)
  stableRoot := fun _ _ _ _ => none

/-- At a store of the instance, `ucSupport` and `ucLate` are `Protocol.confVotes` and
    `Protocol.confLate` of the store's image. -/
theorem uc_conf (st : OkStore V) (E : Env V) (s : Slot) :
    ucSupport E st.val s = Protocol.confVotes E st.val.toProof s ∧
      ucLate E st.val s = Protocol.confLate E st.val.toProof s := by
  have hp : Member.store_pool st.val s = Protocol.Store.pool st.val.toProof s :=
    image_store_pool st.val s
  have hn : (Member.no_second_vote_in : Finset (GoldfishVote V) → GoldfishVote V → Bool) =
      Protocol.no_second_vote_in := ForkChoiceImages.spec_no_second_vote_in_eq
  have hl : ucLate E st.val s = Protocol.confLate E st.val.toProof s := by
    unfold ucLate Protocol.confLate Member.store_timestamp_vote Member.confirmation_time
    rw [hp, ← SpecRecord.toProof_confirmation_time]
  refine ⟨?_, hl⟩
  unfold ucSupport Protocol.confVotes Protocol.confEarly Member.support_cutoff
  rw [hl, hp, hn, ← SpecRecord.toProof_support_cutoff]

/-- At a store of the instance, `ucScore` is `Protocol.confScore` of the store's image. -/
theorem ucScore_eq_conf (st : OkStore V) (E : Env V) (s : Slot) :
    ucScore E st.val s = Protocol.confScore E st.val.toProof s := by
  funext B
  unfold ucScore Protocol.confScore
  rw [(uc_conf st E s).1]
  rfl

/-- At a store of the instance, `ucEligible` is `Protocol.confEligible` of the store's image. -/
theorem ucEligible_eq_conf (st : OkStore V) (E : Env V) (s : Slot) :
    ucEligible E st.val s = Protocol.confEligible E st.val.toProof s := by
  funext B
  have hv : (Member.voters_count : Env V → Finset (GoldfishVote V) → Slot → ℕ) =
      Protocol.voters_count := ForkChoiceImages.spec_voters_count_eq
  unfold ucEligible Protocol.confEligible Protocol.confCount
  rw [ucScore_eq_conf, (uc_conf st E s).2, hv]


/-- The field `live_confirmed_eq_with` of `HandlersFacts` at `Model.spec`: when the honest
    support of `B` is enough, the votes are valid, `B` is a descendant of the SG root and the path
    from the root to `B` is in the filtered tree, the confirmation update records `B` as live
    confirmed. -/
theorem spec_live_confirmed_eq_with : ∀ (contract : (Model.spec (V := V)).Contract) (E : Env V) (hc : HealConfig) (st : (Model.spec (V := V)).S) (s : Slot) (Hon : Finset V) (B : Block V) (tm : TimestampMap (GoldfishVote V)) (htm : st.tau ⇢ tm) (hsup : _root_.DecoupledConsensusModel.Protocol.HonestSupport E st.T ((_root_.DecoupledConsensusModel.beforeCutoff tm ((Model.spec (V := V)).support_cutoff E s) (st.pool s)).filter (fun u => (Model.spec (V := V)).no_second_vote_in (_root_.DecoupledConsensusModel.beforeCutoff st.timestamp_vote ((Model.spec (V := V)).confirmation_time E s) (st.pool s)) u = true)) s Hon B) (hvalid : _root_.DecoupledConsensusModel.Protocol.VoteSetValid E s (_root_.DecoupledConsensusModel.beforeCutoff st.timestamp_vote ((Model.spec (V := V)).confirmation_time E s) (st.pool s))) (R : Block V) (hR : (Model.spec (V := V)).get_sg_root_with contract E hc st.toHealing ((Model.spec (V := V)).round_of hc st.s) ⇢ R) (hpre : Block.Preceq R B) (hpath : ∀ C : Block V, Block.Preceq R C → C ≠ R → Block.Preceq C B → C ∈ (Model.spec (V := V)).get_filtered_block_tree st.toHealing.toFG) (st' : (Model.spec (V := V)).S) (hst' : (Model.spec (V := V)).update_confirmation_with contract E hc st s ⇢ st'), st'.live_confirmed = B := by
  intro contract E hc st s Hon B tm htm hsup hvalid R hR hpre hpath st' hst'
  obtain rfl := StoreFacts.tm_eq_of_returns st htm
  have hR' : Returns (Member.get_sg_root_with contract E hc st.val
      ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.val.s)) R := by
    rw [← round_of_store E hc st]; exact hR
  obtain ⟨hU, hL⟩ := uc_conf st E s
  have hanc : Protocol.confAnchorWith (anchorContract R) E hc st.val.toProof = R := by
    unfold Protocol.confAnchorWith Protocol.get_sg_root_with anchorContract
    rfl
  have hsup' : Protocol.HonestSupport E st.val.toProof.T (Protocol.confVotes E st.val.toProof s) s
      Hon B := by rw [← hU]; exact hsup
  have hvalid' : Protocol.VoteSetValid E s (Protocol.confLate E st.val.toProof s) := by
    rw [← hL]; exact hvalid
  have hpath' : ∀ C : Block V, Block.Preceq (Protocol.confAnchorWith (anchorContract R) E hc
      st.val.toProof) C → C ≠ Protocol.confAnchorWith (anchorContract R) E hc st.val.toProof →
      Block.Preceq C B → C ∈ Protocol.confTree st.val.toProof := by
    intro C h1 h2 h3
    rw [hanc] at h1 h2
    have h := hpath C h1 h2 h3
    show C ∈ Protocol.get_filtered_block_tree st.val.toProof.toHealing.toFG
    rw [← ForkChoiceImages.filtered_eq_vocabulary st]
    exact h
  obtain ⟨hwalk, helig⟩ := Protocol.confWalkWith_eq_of_support (anchorContract R) E hc
    st.val.toProof s Hon B hsup' hvalid' (by rw [hanc]; exact hpre) hpath'
  unfold Protocol.confWalkWith Protocol.confTree at hwalk
  rw [hanc] at hwalk
  obtain ⟨G, S?, -, -, hlive, -, -⟩ := update_confirmation_with_image st contract E hc s hst' hR'
  have hW : Protocol.ghost R (Member.get_filtered_block_tree st.val) (ucScore E st.val s)
      (ucEligible E st.val s) = B := by
    rw [ucScore_eq_conf, ucEligible_eq_conf, ForkChoiceImages.filtered_eq_vocabulary st]
    exact hwalk
  have hE : ucEligible E st.val s B = true := by rw [ucEligible_eq_conf]; exact helig
  show st'.val.live_confirmed.toProof = B
  rw [hlive, hW, if_pos hE]


/-! ## The Goldfish votes a received block includes -/

/-- Every Goldfish vote the store `S` holds, of any slot, has a stamp at most the store's clock. -/
def StampsLe (S : Spec.Store V) : Prop :=
  ∀ (k : Slot) (w : Spec.GoldfishVote V), w ∈ S.gf_votes k →
    ∃ c : Spec.Stamp, S.timestamp_vote w = some c ∧ c ≤ (S.t : Spec.Stamp)

omit [Inhabited V] in
/-- The spec's checked admission of one Goldfish vote keeps the clock, the slot and every held vote,
    and keeps every held vote stamped no later than the clock. -/
theorem checked_step (P : Spec.Provisional V) (S : Spec.Store V)
    (v : Spec.GoldfishVote V) :
    (Spec.Protocol.on_goldfish_vote_checked P S v).t = S.t ∧
      (Spec.Protocol.on_goldfish_vote_checked P S v).s = S.s ∧
      (∀ k w, w ∈ S.gf_votes k →
        w ∈ (Spec.Protocol.on_goldfish_vote_checked P S v).gf_votes k) ∧
      (StampsLe S → StampsLe (Spec.Protocol.on_goldfish_vote_checked P S v)) := by
  unfold Spec.Protocol.on_goldfish_vote_checked Spec.Protocol.on_goldfish_vote
  simp only [Id.run, pure]
  split_ifs <;> first | exact ⟨rfl, rfl, fun _ _ h => h, id⟩ | skip
  refine ⟨rfl, rfl, fun k w h => ?_, fun hS k w h => ?_⟩
  · show w ∈ Function.update S.gf_votes v.slot (S.gf_votes v.slot ++ [v]) k
    rw [Function.update_apply]
    split_ifs with hk
    · subst hk; exact List.mem_append_left _ h
    · exact h
  · change w ∈ Function.update S.gf_votes v.slot (S.gf_votes v.slot ++ [v]) k at h
    show ∃ c, Function.update S.timestamp_vote v (some (S.t : Spec.Stamp)) w = some c ∧
      c ≤ (S.t : Spec.Stamp)
    rw [Function.update_apply]
    by_cases hw : w = v
    · rw [if_pos hw]; exact ⟨_, rfl, le_refl _⟩
    · rw [if_neg hw]
      rw [Function.update_apply] at h
      split_ifs at h with hk
      · rcases List.mem_append.1 h with h | h
        · subst hk; exact hS _ w h
        · exact absurd (List.mem_singleton.1 h) hw
      · exact hS k w h

omit [Inhabited V] in
/-- After the spec's checked admission of the vote `v` of a committee member, of a slot not before
    the store's slot minus one and not after it, `v` is held in its slot's pool or its validator has
    two votes there. -/
theorem checked_self (P : Spec.Provisional V) (S : Spec.Store V)
    (v : Spec.GoldfishVote V) (hc : v.val_index ∈ P.committee v.slot)
    (h1 : ¬ v.slot < S.s - 1) (h2 : ¬ S.s < v.slot) :
    v ∈ (Spec.Protocol.on_goldfish_vote_checked P S v).pool v.slot ∨
      Spec.Protocol.equivocates
        ((Spec.Protocol.on_goldfish_vote_checked P S v).pool v.slot) v.val_index = true := by
  unfold Spec.Protocol.on_goldfish_vote_checked Spec.Protocol.on_goldfish_vote
  simp only [Id.run, pure]
  split_ifs with h3 h4
  · left
    simp only [Bool.or_eq_true, decide_eq_true_eq] at h3
    rcases h3 with (h3 | h3) | h3
    · exact absurd h3 h1
    · exact absurd h3 h2
    · exact List.mem_toFinset.2 h3
  · exact Or.inr h4
  · left
    show v ∈ (Function.update S.gf_votes v.slot (S.gf_votes v.slot ++ [v]) v.slot).toFinset
    rw [Function.update_apply, if_pos rfl]
    exact List.mem_toFinset.2 (List.mem_append_right _ (List.mem_singleton_self v))

omit [Fintype V] [Inhabited V] in
/-- A validator that equivocates in a vote set equivocates in every larger set. -/
theorem equivocates_mono {A B : Finset (Spec.GoldfishVote V)} (h : A ⊆ B) {v : V}
    (hA : Spec.Protocol.equivocates A v = true) :
    Spec.Protocol.equivocates B v = true := by
  unfold Spec.Protocol.equivocates Spec.Protocol.votes_by at hA ⊢
  simp only [decide_eq_true_eq] at hA ⊢
  exact le_trans hA (Finset.card_le_card (Finset.filter_subset_filter _ h))

omit [Inhabited V] in
/-- After the spec's checked admission of a list of Goldfish votes holding `v`, a vote of a
    committee member in the store's window, `v` is held in its slot's pool or its validator has two
    votes there; the clock and the slot are kept, and held votes stay stamped no later than the
    clock. -/
theorem fold_checked_self (P : Spec.Provisional V)
    (votes : List (Spec.GoldfishVote V)) (S0 : Spec.Store V)
    (v : Spec.GoldfishVote V) (hv : v ∈ votes) (hc : v.val_index ∈ P.committee v.slot)
    (h1 : ¬ v.slot < S0.s - 1) (h2 : ¬ S0.s < v.slot) (hS : StampsLe S0) :
    (votes.foldl (Spec.Protocol.on_goldfish_vote_checked P) S0).t = S0.t ∧
      StampsLe (votes.foldl (Spec.Protocol.on_goldfish_vote_checked P) S0) ∧
      (v ∈ (votes.foldl (Spec.Protocol.on_goldfish_vote_checked P) S0).pool v.slot ∨
        Spec.Protocol.equivocates
          ((votes.foldl (Spec.Protocol.on_goldfish_vote_checked P) S0).pool v.slot)
          v.val_index = true) := by
  have keep : ∀ (l : List (Spec.GoldfishVote V)) (S : Spec.Store V),
      (l.foldl (Spec.Protocol.on_goldfish_vote_checked P) S).t = S.t ∧
      (l.foldl (Spec.Protocol.on_goldfish_vote_checked P) S).s = S.s ∧
      (∀ k w, w ∈ S.gf_votes k →
        w ∈ (l.foldl (Spec.Protocol.on_goldfish_vote_checked P) S).gf_votes k) ∧
      (StampsLe S → StampsLe (l.foldl (Spec.Protocol.on_goldfish_vote_checked P) S)) := by
    intro l
    induction l with
    | nil => intro S; exact ⟨rfl, rfl, fun _ _ h => h, id⟩
    | cons w l ih =>
      intro S
      obtain ⟨ht, hs, hm, hst⟩ := checked_step P S w
      obtain ⟨ht', hs', hm', hst'⟩ := ih (Spec.Protocol.on_goldfish_vote_checked P S w)
      exact ⟨ht'.trans ht, hs'.trans hs, fun k w h => hm' k w (hm k w h), fun h => hst' (hst h)⟩
  refine ⟨(keep votes S0).1, (keep votes S0).2.2.2 hS, ?_⟩
  induction votes generalizing S0 with
  | nil => cases hv
  | cons w l ih =>
    simp only [List.foldl_cons]
    obtain ⟨-, hs, -, hst⟩ := checked_step P S0 w
    rcases List.mem_cons.1 hv with rfl | hv'
    · obtain ⟨-, -, hm, -⟩ := keep l (Spec.Protocol.on_goldfish_vote_checked P S0 v)
      have hsub : (Spec.Protocol.on_goldfish_vote_checked P S0 v).pool v.slot ⊆
          (l.foldl (Spec.Protocol.on_goldfish_vote_checked P)
            (Spec.Protocol.on_goldfish_vote_checked P S0 v)).pool v.slot := by
        intro w hw
        exact List.mem_toFinset.2 (hm _ _ (List.mem_toFinset.1 hw))
      rcases checked_self P S0 v hc h1 h2 with h | h
      · exact Or.inl (hsub h)
      · exact Or.inr (equivocates_mono hsub h)
    · exact ih _ hv' (by rw [hs]; exact h1) (by rw [hs]; exact h2) (hst hS)


/-- The field `block_carried_before_deadline_or_equivocates` of `HandlersFacts` at
    `Model.spec`: an in-window committee vote `u` that a newly received block `B` includes is,
    once `B` is received, in the pool before any later cutoff `Γ`, unless its validator equivocates
    there. -/
theorem spec_block_carried_before_deadline_or_equivocates : ∀ (S : Setup V) (st : (Model.spec (V := V)).NS)
    (B : NamedBlock V) (u : GoldfishVote V) (Γ : Time),
    Restated.Vocabulary.Protocol.PoolStamps (Model.spec (V := V)) st.core → B ∉ st.bodies →
    B ∈ ((Model.spec (V := V)).on_block_with .alsoCarried S.E S.hc S.cfg st B).bodies →
    u ∈ B.erase.gf_votes → u.val_index ∈ S.E.committee u.slot →
    ¬ u.slot < st.core.s - 1 → ¬ st.core.s < u.slot → st.core.t < Γ →
    u ∈ _root_.DecoupledConsensusModel.beforeCutoff
        ((Model.spec (V := V)).on_block_with .alsoCarried S.E S.hc S.cfg st B).core.timestamp_vote Γ
        ((Model.spec (V := V)).store_pool ((Model.spec (V := V)).on_block_with .alsoCarried S.E S.hc S.cfg st B).core u.slot) ∨
      (Model.spec (V := V)).equivocates
        (_root_.DecoupledConsensusModel.beforeCutoff
          ((Model.spec (V := V)).on_block_with .alsoCarried S.E S.hc S.cfg st B).core.timestamp_vote Γ
          ((Model.spec (V := V)).store_pool ((Model.spec (V := V)).on_block_with .alsoCarried S.E S.hc S.cfg st B).core u.slot))
        u.val_index = true := by
  intro S st B u Γ hstamps hpre hpost hu hcommittee hfresh hfuture hclock
  rcases ok_block_cases .alsoCarried S.E S.hc S.cfg st B with ⟨-, he, -⟩ | ⟨-, he, -⟩
  · rw [he] at hpost; exact absurd hpost hpre
  set C := Spec.Config.toSpec S.E S.hc S.cfg with hCdef
  set P := Spec.Provisional.toSpec S.E with hPdef
  set X := Spec.Block.toSpecNamed B with hXdef
  have hXB : X.toProofNamed = B := Spec.Block.toProofNamed_toSpecNamed B
  have hE : B.erase = X.toProof := by rw [← hXB, Spec.Block.toProofNamed_erase]
  set A := ((Model.spec (V := V)).on_block_with .alsoCarried S.E S.hc S.cfg st B).val with hAdef
  have hA : A = Spec.Protocol.on_block C P st.val X := he
  have hpost' : B ∈ Member.bodies A := hpost
  have hpre' : B ∉ st.val.T.map Spec.Block.toProofNamedEmb := hpre
  have had : Spec.Protocol.block_admissible C P st.val X = true := by
    rcases on_block_cases C P st.val X with ⟨had, -⟩ | hst
    · exact had
    · rw [hA, hst] at hpost'; exact absurd hpost' hpre'
  set S1 : Spec.Store V := { st.val with
    σ := Function.update st.val.σ X (Spec.Protocol.state_transition C P (st.val.σ X.parent) X)
    T := st.val.T ∪ {X}
    timestamp_block := Function.update st.val.timestamp_block X (some (st.val.t : Spec.Stamp)) }
    with hS1
  set Fo := X.gf_votes.foldl (Spec.Protocol.on_goldfish_vote_checked P) S1 with hFo
  have hAF : A.gf_votes = Fo.gf_votes ∧ A.timestamp_vote = Fo.timestamp_vote := by
    rw [hA, Handlers.on_block_eq, if_pos had]
    unfold Handlers.admitBlockCore
    rw [if_pos had, SubtypeEqualities.blockCore_eq]
    obtain ⟨a, b, c, d, hW⟩ := OkStore.updateFinalityWith_shape Fo (Fo.σ X)
    rw [hW]
    obtain ⟨at', ts, hat⟩ := SpecRecord.NodeFacts.admit_attestations_frame C
      { Fo with h_max := a, J := b, h_j := c, F := d } X.attestations
    rw [hat]
    exact ⟨rfl, rfl⟩
  rw [hE, SubtypeEqualities.toProof_gf_votes] at hu
  obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hu
  have hSt1 : StampsLe S1 := by
    intro k w hw
    have hw' : w.toProof ∈ st.core.gf_votes k := List.mem_map_of_mem hw
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 (hstamps.stamped k w.toProof hw')
    refine ⟨c, ?_, hstamps.bounded w.toProof c hc⟩
    have e : st.core.timestamp_vote w.toProof = st.val.timestamp_vote w := by
      show st.val.timestamp_vote (Spec.GoldfishVote.toSpec w.toProof) = _
      rw [Spec.GoldfishVote.toSpec_toProof]
    rw [← e]; exact hc
  obtain ⟨ht, hSt, hres⟩ := fold_checked_self P X.gf_votes S1 v hv
    (by simpa [hPdef] using hcommittee)
    (show ¬ v.slot < S1.s - 1 from hfresh) (show ¬ S1.s < v.slot from hfuture) hSt1
  have hpoolA : ∀ k, A.pool k = Fo.pool k := fun k => by
    unfold Spec.Store.pool; rw [hAF.1]
  have hcut : _root_.DecoupledConsensusModel.beforeCutoff
      ((Model.spec (V := V)).on_block_with .alsoCarried S.E S.hc S.cfg st B).core.timestamp_vote Γ
      ((Model.spec (V := V)).store_pool
        ((Model.spec (V := V)).on_block_with .alsoCarried S.E S.hc S.cfg st B).core v.slot) =
      (Fo.pool v.slot).map Spec.GoldfishVote.toProofEmb := by
    show _root_.DecoupledConsensusModel.beforeCutoff
      (fun w => A.timestamp_vote (Spec.GoldfishVote.toSpec w)) Γ
      ((A.pool v.slot).map Spec.GoldfishVote.toProofEmb) = _
    rw [← ForkChoiceImages.beforeCutoff_map, hpoolA, hAF.2]
    congr 1
    unfold DecoupledConsensusModel.beforeCutoff
    apply Finset.filter_true_of_mem
    intro w hw
    obtain ⟨c, hc, hle⟩ := hSt v.slot w (List.mem_toFinset.1 hw)
    unfold DecoupledConsensusModel.stampedBefore
    rw [hc]
    have hlt : (Fo.t : Spec.Stamp) < (Γ : Spec.Stamp) := by
      rw [ht]; exact WithBot.coe_lt_coe.2 hclock
    exact decide_eq_true (lt_of_le_of_lt hle hlt)
  show v.toProof ∈ _ ∨ Member.equivocates _ v.val_index = true
  have hs : v.toProof.slot = v.slot := rfl
  rw [hs, hcut]
  rcases hres with h | h
  · exact Or.inl (Finset.mem_map_of_mem _ h)
  · right
    unfold Member.equivocates
    have e : ((Fo.pool v.slot).map Spec.GoldfishVote.toProofEmb).map
        ChainStateToHandlers.goldfishVoteToSpecEmb = Fo.pool v.slot := by
      ext w; simp [ChainStateToHandlers.goldfishVoteToSpecEmb]
    rw [e]
    exact h


/-! ## The block handler's accepted case -/

omit [Fintype V] [Inhabited V] in
/-- Adding to a tree `T` of distinct roots the block standing for a block `B` that `T` does not
    image, when no tree block has its root, changes no block standing for an image. -/
theorem blockOfImageIn_insert_eq {T : Finset (Spec.Block V)} (hd : NoRaise.DistinctRoots T)
    {B : Block V} (hnew : B ∉ T.image Spec.Block.toProof)
    (hroot : ¬ RootHeldByOther T (Spec.Store.blockOfImageIn T B)) :
    ∀ C : Block V, Spec.Store.blockOfImageIn (T ∪ {Spec.Store.blockOfImageIn T B}) C =
      Spec.Store.blockOfImageIn T C := by
  set X := Spec.Store.blockOfImageIn T B with hXdef
  have hXB : X.toProof = B := Spec.Store.toProof_blockOfImageIn T B
  have hinj' := SubtypeEqualities.injOn_insert hd hroot
  let S : Spec.Store V := { Spec.Store.init with T := T }
  let S' : Spec.Store V := { Spec.Store.init with T := T ∪ {X} }
  intro C
  induction C with
  | genesis => rfl
  | node p s r votes support ats proposer ih =>
    by_cases hC : Block.node p s r votes support ats proposer ∈ T.image Spec.Block.toProof
    · obtain ⟨Y, hY, hYC⟩ := Finset.mem_image.1 hC
      rw [← hYC]
      have e1 : Spec.Store.blockOfImageIn T Y.toProof = Y :=
        Spec.Store.blockOfImage_toProof_of_injOn S
          (SubtypeEqualities.injOn_of_distinctRoots hd) hY
      have e2 : Spec.Store.blockOfImageIn (T ∪ {X}) Y.toProof = Y :=
        Spec.Store.blockOfImage_toProof_of_injOn S' hinj' (Finset.mem_union_left _ hY)
      rw [e1, e2]
    · by_cases hCB : Block.node p s r votes support ats proposer = B
      · rw [hCB]
        rw [← hXB]
        exact Spec.Store.blockOfImage_toProof_of_injOn S' hinj'
          (Finset.mem_union_right _ (Finset.mem_singleton_self X)) |>.trans
          (by rw [hXB])
      · have hn : ∀ U : Finset (Spec.Block V),
            (∀ Y ∈ U, Y.toProof ≠ Block.node p s r votes support ats proposer) →
            Spec.pickUnique? U
              (fun B' => decide (B'.toProof = Block.node p s r votes support ats proposer)) = none := by
          intro U hU
          unfold Spec.pickUnique?
          rw [dif_neg]
          rintro ⟨a, ⟨ha, hpa⟩, -⟩
          exact hU a ha (of_decide_eq_true hpa)
        have h1 : ∀ Y ∈ T, Y.toProof ≠ Block.node p s r votes support ats proposer :=
          fun Y hY h => hC (h ▸ Finset.mem_image_of_mem _ hY)
        have h2 : ∀ Y ∈ T ∪ {X}, Y.toProof ≠ Block.node p s r votes support ats proposer := by
          intro Y hY h
          rcases Finset.mem_union.1 hY with hY | hY
          · exact h1 Y hY h
          · rw [Finset.mem_singleton.1 hY, hXB] at h; exact hCB h.symm
        simp only [Spec.Store.blockOfImageIn, hn T h1, hn _ h2, Option.getD]
        rw [ih]

/-- The field `raw_eq_or_accepted` of `HandlersFacts` at `Model.spec`: the block handler either
    leaves the store as it was, or adds the new block `B`, a descendant of `F`, with its chain state
    built from its parent's, and then updates finality from that chain state. -/
theorem spec_raw_eq_or_accepted : ∀ (E : Env V) (st : (Model.spec (V := V)).S) (B : Block V) (build : (Model.spec (V := V)).CS → (Model.spec (V := V)).CS), (Model.spec (V := V)).on_block_using E st B build = st ∨
    ∃ u : (Model.spec (V := V)).S,
    u.T = insert B st.T ∧ u.F = st.F ∧ u.J = st.J ∧ u.h_j = st.h_j ∧
    u.h_max = st.h_max ∧
    u.σ = (fun C => if C = B then build (st.σ B.parent) else st.σ C) ∧
    (∀ σ, (Model.spec (V := V)).chainStateInTree st σ → (Model.spec (V := V)).chainStateInTree u σ) ∧
    B ∉ st.T ∧ Block.preceq st.F B = true ∧
    (Model.spec (V := V)).on_block_using E st B build = (Model.spec (V := V)).update_finality u (u.σ B) := by
  intro E st B build
  obtain ⟨hst, hd, hpc, hF⟩ := st.property
  by_cases hrej : (st.s < B.slot ∨ B ∈ st.T ∨ B.parent ∉ st.T) ∨ (!Block.preceq st.F B) = true ∨
      B.proposer? ≠ some (E.proposer B.slot) ∨ ¬ (B.parent.slot < B.slot)
  · exact Or.inl (spec_on_block_using_of_rejected E st B build hrej)
  set X := st.val.blockOfImage B with hXdef
  by_cases hheld : RootHeldByOther st.val.T X
  · left
    show OkMember.on_block_using E st B build = st
    unfold OkMember.on_block_using
    rw [dif_pos hheld]
  right
  simp only [not_or, not_not, Bool.not_eq_true', Bool.not_eq_false] at hrej
  obtain ⟨⟨hslot, hnew, hparB⟩, hFB, hprop, hps⟩ := hrej
  have hinj := hd.injOn_toProof
  have hXB : X.toProof = B := Spec.Store.toProof_blockOfImage _ _
  have hnew' : B ∉ st.val.T.image Spec.Block.toProof := hnew
  have hXT : X ∉ st.val.T := fun h => hnew' (hXB ▸ Finset.mem_image_of_mem _ h)
  have hXpar : X.parent = st.val.blockOfImage B.parent :=
    (Spec.Store.blockOfImage_parent st.val hinj hpc B).symm
  obtain ⟨Y, hY, hYp⟩ := Finset.mem_image.1 (show B.parent ∈ st.val.T.image _ from hparB)
  have hXparT : X.parent ∈ st.val.T := by
    rw [hXpar, ← hYp, Spec.Store.blockOfImage_toProof_of_mem st.val hd hY]; exact hY
  have hslotX : X.slot = B.slot := by rw [← hXB, SubtypeEqualities.toProof_slot]
  have hpslotX : X.parent.slot = B.parent.slot := by
    rw [hXpar, ← SubtypeEqualities.toProof_slot, Spec.Store.toProof_blockOfImage]
  have hpropX : X.proposer? = B.proposer? := by rw [← hXB, SubtypeEqualities.toProof_proposer?]
  have hFX : st.val.F.ancestorEq X = true := by
    have hF' : st.val.blockOfImage st.val.F.toProof = st.val.F :=
      Spec.Store.blockOfImage_toProof_of_mem st.val hd hF
    rw [← hF', hXdef, Spec.Store.blockOfImage_ancestorEq_of_distinctRoots _ hd hpc]
    exact hFB
  set P := Spec.Provisional.toSpec E with hPdef
  set S0 : Spec.Store V := { st.val with
    σ := Function.update st.val.σ X (build (st.val.σ X.parent))
    T := st.val.T ∪ {X}
    timestamp_block := Function.update st.val.timestamp_block X (some (st.val.t : Spec.Stamp)) }
    with hS0
  set Fo := X.gf_votes.foldl (Spec.Protocol.on_goldfish_vote_checked P) S0 with hFo
  have hok : NoRaise.StoreOk Fo :=
    OkStore.foldl_checked P _ (OkStore.insert ⟨hst, hd, hpc, hF⟩ hXparT hheld _ _)
  obtain ⟨x, y, hFoe⟩ := SubtypeEqualities.foldl_checked_shape P X.gf_votes S0
  have hFoT : Fo.T = st.val.T ∪ {X} := by rw [hFo, hFoe]
  have hbo : Fo.blockOfImage = st.val.blockOfImage := by
    funext C
    unfold Spec.Store.blockOfImage
    rw [hFoT]
    exact blockOfImageIn_insert_eq hd hnew' hheld C
  have hFoX : Fo.blockOfImage B = X := by rw [hbo]
  have hval : (OkMember.on_block_using E st B build).val =
      Handlers.updateFinalityWith Fo (Fo.σ X) := by
    rw [OkMember.on_block_using_val_of_not_held hheld]
    show Handlers.onBlockUsing P st.val X build = _
    have h1' : ¬ st.val.s < X.slot := by rw [hslotX]; exact hslot
    have hprop' : X.proposer? = P.proposer X.slot := by
      rw [hpropX, hprop, hslotX]; rfl
    have hps' : X.parent.slot < X.slot := by rw [hpslotX, hslotX]; exact hps
    unfold Handlers.onBlockUsing
    simp only [Id.run, h1', hXT, hXparT, hFX, hprop', hps', decide_false,
      Bool.or_false, not_true_eq_false, if_false, ne_eq, Bool.false_eq_true,
      List.forIn_pure_yield_eq_foldl]
    rfl
  refine ⟨⟨Fo, hok⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hnew, hFB, ?_⟩
  · show Fo.T.image Spec.Block.toProof = insert B (st.val.T.image Spec.Block.toProof)
    rw [hFoT, Finset.image_union, Finset.image_singleton, hXB, Finset.insert_eq, Finset.union_comm]
  · show Fo.F.toProof = st.val.F.toProof
    rw [hFo, hFoe]
  · show Fo.J.toProof = st.val.J.toProof
    rw [hFo, hFoe]
  · show Fo.h_j = st.val.h_j
    rw [hFo, hFoe]
  · show Fo.h_max = st.val.h_max
    rw [hFo, hFoe]
  · funext C
    show Fo.σ (Fo.blockOfImage C) = if C = B then build (st.val.σ (st.val.blockOfImage B.parent))
      else st.val.σ (st.val.blockOfImage C)
    have hσ : Fo.σ = Function.update st.val.σ X (build (st.val.σ X.parent)) := by rw [hFo, hFoe]
    rw [hσ, hbo]
    split_ifs with hC
    · subst hC
      rw [← hXdef, Function.update_self, hXpar]
    · have hne : st.val.blockOfImage C ≠ X := by
        intro h
        apply hC
        rw [← Spec.Store.toProof_blockOfImage st.val C, h, hXB]
      rw [Function.update_of_ne hne]
  ·
    intro σ hσ
    obtain ⟨h1, h2, h3⟩ := hσ
    have hsub : st.val.T ⊆ Fo.T := by
      rw [hFoT]
      exact Finset.subset_union_left
    have hJ : Fo.J = st.val.J := by rw [hFo, hFoe]
    exact ⟨hsub h1, hsub h2, by rw [hJ]; exact hsub h3⟩
  · apply Subtype.ext
    show (OkMember.on_block_using E st B build).val =
      Member.update_finality Fo (Fo.σ (Fo.blockOfImage B))
    rw [hval, hFoX]
    rfl

end SpecRecord.HandlersFacts
