import Proofs.Instance.Model
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Instance.Equalities.ForkChoiceImages
import Proofs.Instance.Equalities.ContractImages

/-!
# The fork-choice facts of `Model.spec`

The fields of `ForkChoiceFacts` proved at the model `Model.spec`, one theorem per field, and
the bundle `Model.spec_runFacts_forkChoice`.
-/

set_option autoImplicit false

namespace SpecRecord.ForkChoiceFacts

open DecoupledConsensusModel DecoupledConsensusModel.Execution DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

omit [Fintype V] [Inhabited V] in
/-- Mapping each block of `T` to its spec form and back gives `T`. -/
theorem map_blockToSpec_toProof (T : Finset (Block V)) :
    (T.map ForkChoiceGrades.blockToSpecEmb).image Spec.Block.toProof = T := by
  ext B
  simp [ForkChoiceGrades.blockToSpecEmb]

omit [DecidableEq V] [Fintype V] [Inhabited V] in
/-- Mapping each Goldfish vote of `T` to its spec form by `ForkChoiceGrades.voteToSpecEmb` and back
    gives `T`. -/
theorem map_voteToSpec_toProof (T : Finset (GoldfishVote V)) :
    (T.map ForkChoiceGrades.voteToSpecEmb).map Spec.GoldfishVote.toProofEmb = T := by
  ext u
  simp [ForkChoiceGrades.voteToSpecEmb]

omit [DecidableEq V] [Fintype V] [Inhabited V] in
/-- Mapping each Goldfish vote of `T` to its spec form by
    `ChainStateToHandlers.goldfishVoteToSpecEmb` and back gives `T`. -/
theorem map_goldfishVoteToSpec_toProof (T : Finset (GoldfishVote V)) :
    (T.map ChainStateToHandlers.goldfishVoteToSpecEmb).map
      Spec.GoldfishVote.toProofEmb = T := by
  ext u
  simp [ChainStateToHandlers.goldfishVoteToSpecEmb]

/-- The member `no_second_vote_in` of `Model.spec` is `Protocol.no_second_vote_in`. -/
theorem spec_no_second_vote_in_eq :
    (Model.spec (V := V)).no_second_vote_in =
      DecoupledConsensusModel.Protocol.no_second_vote_in := by
  funext late vote
  show Spec.Protocol.no_second_vote_in (late.map ForkChoiceGrades.voteToSpecEmb)
    (Spec.GoldfishVote.toSpec vote) = _
  rw [← toProof_no_second_vote_in, map_voteToSpec_toProof,
    Spec.GoldfishVote.toProof_toSpec]

/-- The member `voters_count` of `Model.spec` is `Protocol.voters_count`. -/
theorem spec_voters_count_eq :
    (Model.spec (V := V)).voters_count = DecoupledConsensusModel.Protocol.voters_count := by
  funext E votes s
  show Spec.Protocol.raw_voters_count (votes.map ForkChoiceGrades.voteToSpecEmb) = _
  rw [← toProof_voters_count E _ s, map_voteToSpec_toProof]

/-- The member `participates` of `Model.spec` is `Protocol.participates`. -/
theorem spec_participates_eq :
    (Model.spec (V := V)).participates = DecoupledConsensusModel.Protocol.participates := by
  funext votes v
  show Spec.Protocol.participates
    (votes.map ChainStateToHandlers.goldfishVoteToSpecEmb) v = _
  rw [← toProof_participates, map_goldfishVoteToSpec_toProof]

/-- The member `latest_window` of `Model.spec` is `Protocol.latest_window`. -/
theorem spec_latest_window_eq :
    (Model.spec (V := V)).latest_window = DecoupledConsensusModel.Protocol.latest_window := by
  funext η r
  exact (toProof_latest_window η r).symm

omit [DecidableEq V] [Fintype V] [Inhabited V] in
/-- Two blocks with the same spec form are the same block. -/
theorem blockToSpec_inj (A B : Block V) :
    Spec.Block.toSpec A = Spec.Block.toSpec B ↔ A = B :=
  ⟨fun h => by simpa using congrArg Spec.Block.toProof h, fun h => h ▸ rfl⟩

omit [Fintype V] [Inhabited V] in
/-- The spec form of `A` is an ancestor of the spec form of `B`, or equal to it, exactly when `A` is
    an ancestor of `B` or equal to it. -/
theorem toSpec_ancestorEq (A B : Block V) :
    (Spec.Block.toSpec A).ancestorEq (Spec.Block.toSpec B) =
      Block.preceq A B := by
  induction B with
  | genesis =>
      show (Spec.Block.toSpec A).ancestorEq Spec.Block.genesis = _
      rw [Spec.Block.ancestorEq, Block.preceq]
      have e : (Spec.Block.genesis : Spec.Block V) =
          Spec.Block.toSpec Block.genesis := rfl
      rw [e]
      simp only [blockToSpec_inj]
  | node p s r votes support ats proposer ih =>
      have e : Spec.Block.toSpec (Block.node p s r votes support ats proposer) =
          Spec.Block.node (Spec.Block.toSpec p) s
            (Spec.BlockId.toSpec r) (votes.map Spec.GoldfishVote.toSpec)
            (support.map Spec.GoldfishVote.toSpec)
            (ats.map Spec.Attestation.toSpec) proposer := rfl
      rw [e, Spec.Block.ancestorEq, ← e, Block.preceq, ih]
      simp only [blockToSpec_inj]

/-- The member `viable_tree` of `Model.spec` at a chain-state map `σ` is `Protocol.viable_tree`
    at the map `fun C => (σ C).toProof`. -/
theorem spec_viable_tree_eq (σ : Block V → Spec.Protocol.ChainState V)
    (F : Block V) (h_max : Height) (T : Finset (Block V)) :
    (Model.spec (V := V)).viable_tree σ F h_max T =
      DecoupledConsensusModel.Protocol.viable_tree (fun C => (σ C).toProof) F h_max T := by
  show (Spec.Protocol.viable_tree (fun C => σ C.toProof) (Spec.Block.toSpec F)
    h_max (T.map ForkChoiceGrades.blockToSpecEmb)).image Spec.Block.toProof = _
  ext B
  simp only [Spec.Protocol.viable_tree, Spec.Protocol.finalized_descendants,
    Spec.Protocol.viable, DecoupledConsensusModel.Protocol.viable_tree,
    DecoupledConsensusModel.Protocol.finalized_descendants, DecoupledConsensusModel.Protocol.viable,
    Finset.mem_image, Finset.mem_filter, Finset.mem_map, ForkChoiceGrades.blockToSpecEmb,
    Function.Embedding.coeFn_mk, Spec.Block.AncestorEq, Block.Preceq,
    Spec.Protocol.ChainState.toProof_h, decide_eq_true_eq]
  constructor
  · rintro ⟨D, ⟨⟨⟨A, hA, rfl⟩, hF⟩, W, ⟨W', hW', rfl⟩, hDW, hh⟩, rfl⟩
    rw [toSpec_ancestorEq] at hF hDW
    simp only [Spec.Block.toProof_toSpec] at hh ⊢
    exact ⟨⟨hA, hF⟩, W', hW', hDW, hh⟩
  · rintro ⟨⟨hB, hF⟩, W, hW, hBW, hh⟩
    refine ⟨Spec.Block.toSpec B, ⟨⟨⟨B, hB, rfl⟩, ?_⟩, Spec.Block.toSpec W,
      ⟨W, hW, rfl⟩, ?_, ?_⟩, Spec.Block.toProof_toSpec B⟩
    · rw [toSpec_ancestorEq]; exact hF
    · rw [toSpec_ancestorEq]; exact hBW
    · simpa using hh

/-- Unfolds the members of `Model.vocabulary` and `Model.spec` and rewrites every routine read at
    a `toProof` image of a spec store into the spec's routine. -/
local macro "sd_normalize" : tactic => `(tactic| simp only [Model.vocabulary, Model.spec, Model.specBase,
  DecoupledConsensusModel.Sts.Record.vocabulary,
  Model.S.F, Model.S.J, Model.S.h_j, Model.S.h_max, Model.S.T, Model.S.s, Model.S.t, Model.S.σ,
  Model.S.gf_votes, Model.S.sg_votes, Model.S.live_confirmed, Model.S.timestamp_block,
  Model.S.timestamp_vote, Model.S.toHealing, Model.S.pool, Model.S.sg_pool,
  Model.HS.toFG, Model.FGS.toSG, Model.SGS.toGoldfishStore,
  Model.FGS.F, Model.FGS.J, Model.FGS.h_j, Model.FGS.h_max, Model.FGS.σ,
  Model.GS.T, Model.GS.s, Model.GS.gf_votes, Model.GS.pool, Model.GS.live_confirmed,
  Model.GS.timestamp_block, Model.GS.timestamp_vote, ChainStateModel.CS.h,
  Member.toHealing, Member.toFG, Member.toSG, Member.toGoldfishStore, id_eq,
  Member.fg_F, Member.fg_J, Member.fg_h_j, Member.fg_h_max, Member.fg_σ, Member.h,
  Member.store_F, Member.store_J, Member.store_h_j, Member.store_h_max, Member.store_T,
  Member.store_s, Member.store_t, Member.store_σ, Member.store_gf_votes, Member.store_sg_votes,
  Member.store_live_confirmed, Member.store_timestamp_block, Member.store_timestamp_vote,
  Member.gs_T, Member.gs_s, Member.gs_gf_votes, Member.gs_live_confirmed,
  Member.gs_timestamp_block, Member.gs_timestamp_vote,
  Member.get_fg_root, Member.get_filtered_block_tree, Member.get_filtered_block_tree_from,
  toProof_fg_F, toProof_fg_J, toProof_fg_h_j, toProof_fg_h_max,
  toProof_gs_T, toProof_gs_s, toProof_gs_gf_votes, toProof_gs_live_confirmed,
  Spec.Store.toProof_get_fg_root_ofImage, toProof_get_fg_root, map_blockToSpec_toProof,
  DecoupledConsensusModel.Proofs.ModelProperties.toHealing_σ,
  Spec.Store.toProof_F, Spec.Store.toProof_J, Spec.Store.toProof_h_j,
  Spec.Store.toProof_h_max, Spec.Store.toProof_T, Spec.Store.toProof_s,
  Spec.Store.toProof_σ, Spec.Store.toProof_gf_votes,
  Spec.Protocol.ChainState.toProof_h] at *)

/-! ## `ForkChoiceFacts` -/

/-- The field `get_fg_root_toHealing_clock` of `ForkChoiceFacts` at `Model.spec`: setting the
    store's time and slot does not change the FG root of its healing view. -/
theorem spec_get_fg_root_toHealing_clock :
    ∀ (st : (Model.spec (V := V)).S) (t : Time) (s : Slot),
    (Model.spec (V := V)).get_fg_root ((Model.spec (V := V)).store_with_t_s st t s).toHealing.toFG = (Model.spec (V := V)).get_fg_root st.toHealing.toFG :=
  fun _ _ _ => rfl

/-- The field `get_filtered_block_tree_toHealing_clock` of `ForkChoiceFacts` at `Model.spec`:
    setting the store's time and slot does not change the filtered tree of its healing view. -/
theorem spec_get_filtered_block_tree_toHealing_clock :
    ∀ (st : (Model.spec (V := V)).S) (t : Time) (s : Slot),
    (Model.spec (V := V)).get_filtered_block_tree ((Model.spec (V := V)).store_with_t_s st t s).toHealing.toFG =
      (Model.spec (V := V)).get_filtered_block_tree st.toHealing.toFG :=
  fun _ _ _ => rfl

/-- The field `mem_viable_tree_iff` of `ForkChoiceFacts` at `Model.spec`: `B` is in the viable
    tree of `σ`, `F`, `h_max` and `T` exactly when `B` is in `T`, `F ⪯ B`, and some `W` in `T` with
    `B ⪯ W` has chain-state height at least `h_max - 1`. -/
theorem spec_mem_viable_tree_iff :
    ∀ (σ : Block V → (Model.spec (V := V)).CS) (F : Block V) (h_max : Height)
    (T : Finset (Block V)) (B : Block V),
    B ∈ (Model.spec (V := V)).viable_tree σ F h_max T ↔
      (B ∈ T ∧ Block.Preceq F B) ∧ ∃ W ∈ T, Block.Preceq B W ∧ h_max - 1 ≤ (σ W).h := by
  intro σ F h_max T B
  rw [spec_viable_tree_eq]
  exact (Model.vocabulary_facts_forkChoice (V := V)).mem_viable_tree_iff (fun C => (σ C).toProof) F h_max T B

/-- The field `get_fg_root_set_clock_slot` of `ForkChoiceFacts` at `Model.spec`: setting the
    store's time and slot does not change its FG root. -/
theorem spec_get_fg_root_set_clock_slot :
    ∀ (st : (Model.spec (V := V)).S) (t : Int) (s : Slot),
    (Model.spec (V := V)).get_fg_root ((Model.spec (V := V)).store_with_t_s st t s).toHealing.toFG = (Model.spec (V := V)).get_fg_root st.toHealing.toFG :=
  fun _ _ _ => rfl

/-- The field `get_filtered_block_tree_set_clock_slot` of `ForkChoiceFacts` at `Model.spec`:
    setting the store's time and slot does not change its filtered block tree. -/
theorem spec_get_filtered_block_tree_set_clock_slot :
    ∀ (st : (Model.spec (V := V)).S) (t : Int) (s : Slot),
    (Model.spec (V := V)).get_filtered_block_tree ((Model.spec (V := V)).store_with_t_s st t s).toHealing.toFG =
      (Model.spec (V := V)).get_filtered_block_tree st.toHealing.toFG :=
  fun _ _ _ => rfl

/-- The field `no_second_vote_in_eq_true_iff` of `ForkChoiceFacts` at `Model.spec`:
    `no_second_vote_in late vote` is `true` exactly when every vote of `late` is `vote` or has
    another signer. -/
theorem spec_no_second_vote_in_eq_true_iff :
    ∀ (late : Finset (GoldfishVote V)) (vote : GoldfishVote V),
    (Model.spec (V := V)).no_second_vote_in late vote = true ↔ ∀ u ∈ late, u = vote ∨ u.val_index ≠ vote.val_index := by
  intro late vote
  rw [spec_no_second_vote_in_eq]
  exact (Model.vocabulary_facts_forkChoice (V := V)).no_second_vote_in_eq_true_iff late vote

/-- The field `no_second_vote_in_of_forall` of `ForkChoiceFacts` at `Model.spec`: if every vote
    of `late` is `vote` or has another signer, then `no_second_vote_in late vote` is `true`. -/
theorem spec_no_second_vote_in_of_forall :
    ∀ {late : Finset (GoldfishVote V)} {vote : GoldfishVote V},
    (∀ u ∈ late, u = vote ∨ u.val_index ≠ vote.val_index) → (Model.spec (V := V)).no_second_vote_in late vote = true := by
  intro late vote h
  rw [spec_no_second_vote_in_eq]
  exact (Model.vocabulary_facts_forkChoice (V := V)).no_second_vote_in_of_forall h

/-- The field `proposer_view_set_clock_slot` of `ForkChoiceFacts` at `Model.spec`: setting the
    store's time and slot does not change its slot-`k` proposer view. -/
theorem spec_proposer_view_set_clock_slot :
    ∀ (st : (Model.spec (V := V)).S) (t : Int) (s k : Slot),
    (Model.spec (V := V)).proposer_view ((Model.spec (V := V)).store_with_t_s st t s).toHealing.toFG.toSG.toGoldfishStore k =
      (Model.spec (V := V)).proposer_view st.toHealing.toFG.toSG.toGoldfishStore k :=
  fun _ _ _ _ => rfl

/-- The field `get_fg_root_toHealing_eq_of_fields` of `ForkChoiceFacts` at `Model.specBase`:
    two stores with the same finalized block, justified block, justified height and height maximum
    have the same FG root. -/
theorem specBase_get_fg_root_toHealing_eq_of_fields :
    ∀ {st st' : (Model.specBase (V := V)).S} (hF : st.F = st'.F) (hJ : st.J = st'.J) (hhj : st.h_j = st'.h_j) (hmax : st.h_max = st'.h_max), (Model.specBase (V := V)).get_fg_root ((Model.specBase (V := V)).toHealing st).toFG = (Model.specBase (V := V)).get_fg_root ((Model.specBase (V := V)).toHealing st').toFG := by
  intro st st' hF hJ hhj hmax
  have := (Model.vocabulary_facts_forkChoice (V := V)).get_fg_root_toHealing_eq_of_fields (st := st.toProof) (st' := st'.toProof)
  sd_normalize
  exact this hF hJ hhj hmax

/-- The field `get_fg_root_toHealing_eq_of_fields` of `ForkChoiceFacts` at `Model.spec`: two
    stores with the same finalized block, justified block, justified height and height maximum have
    the same FG root. -/
theorem spec_get_fg_root_toHealing_eq_of_fields :
    ∀ {st st' : (Model.spec (V := V)).S} (hF : st.F = st'.F) (hJ : st.J = st'.J) (hhj : st.h_j = st'.h_j) (hmax : st.h_max = st'.h_max), (Model.spec (V := V)).get_fg_root ((Model.spec (V := V)).toHealing st).toFG = (Model.spec (V := V)).get_fg_root ((Model.spec (V := V)).toHealing st').toFG :=
  fun {st} {st'} hF hJ hhj hmax => specBase_get_fg_root_toHealing_eq_of_fields (st := st.val) (st' := st'.val) hF hJ hhj hmax

/-- The field `get_fg_root_toHealing_of_eq` of `ForkChoiceFacts` at `Model.specBase`: when the
    store's height maximum is its justified height plus one, its FG root is its justified block. -/
theorem specBase_get_fg_root_toHealing_of_eq :
    ∀ (st : (Model.specBase (V := V)).S) (h : st.h_max = st.h_j + 1), (Model.specBase (V := V)).get_fg_root ((Model.specBase (V := V)).toHealing st).toFG = st.J := by
  intro st h
  have := (Model.vocabulary_facts_forkChoice (V := V)).get_fg_root_toHealing_of_eq st.toProof
  sd_normalize
  exact this h

/-- The field `get_fg_root_toHealing_of_eq` of `ForkChoiceFacts` at `Model.spec`: when the
    store's height maximum is its justified height plus one, its FG root is its justified block. -/
theorem spec_get_fg_root_toHealing_of_eq :
    ∀ (st : (Model.spec (V := V)).S) (h : st.h_max = st.h_j + 1), (Model.spec (V := V)).get_fg_root ((Model.spec (V := V)).toHealing st).toFG = st.J :=
  fun st h => specBase_get_fg_root_toHealing_of_eq st.val h

/-- The field `get_fg_root_toHealing_of_ne` of `ForkChoiceFacts` at `Model.specBase`: when the
    store's height maximum is not its justified height plus one, its FG root is its finalized block. -/
theorem specBase_get_fg_root_toHealing_of_ne :
    ∀ (st : (Model.specBase (V := V)).S) (h : ¬ st.h_max = st.h_j + 1), (Model.specBase (V := V)).get_fg_root ((Model.specBase (V := V)).toHealing st).toFG = st.F := by
  intro st h
  have := (Model.vocabulary_facts_forkChoice (V := V)).get_fg_root_toHealing_of_ne st.toProof
  sd_normalize
  exact this h

/-- The field `get_fg_root_toHealing_of_ne` of `ForkChoiceFacts` at `Model.spec`: when the
    store's height maximum is not its justified height plus one, its FG root is its finalized block. -/
theorem spec_get_fg_root_toHealing_of_ne :
    ∀ (st : (Model.spec (V := V)).S) (h : ¬ st.h_max = st.h_j + 1), (Model.spec (V := V)).get_fg_root ((Model.spec (V := V)).toHealing st).toFG = st.F :=
  fun st h => specBase_get_fg_root_toHealing_of_ne st.val h

/-- The field `mem_latest_window` of `ForkChoiceFacts` at `Model.spec`: if `r − eta ≤ k` and
    `k < r`, then `k` is in `latest_window eta r`. -/
theorem spec_mem_latest_window :
    ∀ {eta r k : Round} (hlo : r - eta ≤ k) (hhi : k < r), k ∈ (Model.spec (V := V)).latest_window eta r := by
  intro eta r k hlo hhi
  rw [spec_latest_window_eq]
  exact (Model.vocabulary_facts_forkChoice (V := V)).mem_latest_window hlo hhi

/-- The field `window_bounds` of `ForkChoiceFacts` at `Model.spec`: a round `k` in
    `latest_window eta r` has `r − eta ≤ k` and `k < r`. -/
theorem spec_window_bounds :
    ∀ {eta r k : Nat} (hk : k ∈ (Model.spec (V := V)).latest_window eta r), r - eta ≤ k ∧ k < r := by
  intro eta r k hk
  rw [spec_latest_window_eq] at hk
  exact (Model.vocabulary_facts_forkChoice (V := V)).window_bounds hk

/-- The field `preceq_get_fg_root_of_F` of `ForkChoiceFacts` at `Model.specBase`: if the FG
    store's finalized block is an ancestor of its justified block or that block, it is an ancestor
    of its FG root or that root. -/
theorem specBase_preceq_get_fg_root_of_F :
    ∀ {st : (Model.specBase (V := V)).FGS} (hFJ : Block.preceq st.F st.J = true), Block.preceq st.F ((Model.specBase (V := V)).get_fg_root st) = true := by
  intro st hFJ
  have := (Model.vocabulary_facts_forkChoice (V := V)).preceq_get_fg_root_of_F (st := st.toProof.toHealing.toFG)
  sd_normalize
  exact this hFJ

/-- The field `preceq_get_fg_root_of_F` of `ForkChoiceFacts` at `Model.spec`: if the FG store's
    finalized block is an ancestor of its justified block or that block, it is an ancestor of its FG
    root or that root. -/
theorem spec_preceq_get_fg_root_of_F :
    ∀ {st : (Model.spec (V := V)).FGS} (hFJ : Block.preceq st.F st.J = true), Block.preceq st.F ((Model.spec (V := V)).get_fg_root st) = true :=
  fun {st} hFJ => specBase_preceq_get_fg_root_of_F (st := st.val) hFJ

/-- The field `pred_mem_latest_window` of `ForkChoiceFacts` at `Model.spec`: if `1 ≤ etaSG` and
    `0 < r`, then `r − 1` is in `latest_window etaSG r`. -/
theorem spec_pred_mem_latest_window :
    ∀ (etaSG r : Round) (heta : 1 ≤ etaSG) (hr : 0 < r), r - 1 ∈ (Model.spec (V := V)).latest_window etaSG r := by
  intro etaSG r heta hr
  rw [spec_latest_window_eq]
  exact (Model.vocabulary_facts_forkChoice (V := V)).pred_mem_latest_window etaSG r heta hr

/-- The field `voters_count_le_committee` of `ForkChoiceFacts` at `Model.spec`: for a vote set
    valid at slot `s`, the participant count is at most the size of slot `s`'s committee. -/
theorem spec_voters_count_le_committee :
    ∀ (E : Env V) (late : Finset (GoldfishVote V)) (s : Slot) (hvalid : Protocol.VoteSetValid E s late), (Model.spec (V := V)).voters_count E late s ≤ (E.committee s).card := by
  intro E late s hvalid
  rw [spec_voters_count_eq]
  exact (Model.vocabulary_facts_forkChoice (V := V)).voters_count_le_committee E late s hvalid

/-- The field `card_le_voters_count_of_participates` of `ForkChoiceFacts` at `Model.spec`: if
    every validator of `X` participates in `votes`, then `X` has at most as many members as the
    participant count of `votes`. -/
theorem spec_card_le_voters_count_of_participates :
    ∀ (E : Env V) (votes : Finset (GoldfishVote V)) (s : Slot) (X : Finset V) (h : ∀ x ∈ X, (Model.spec (V := V)).participates votes x = true), X.card ≤ (Model.spec (V := V)).voters_count E votes s := by
  intro E votes s X h
  rw [spec_participates_eq] at h
  rw [spec_voters_count_eq]
  exact (Model.vocabulary_facts_forkChoice (V := V)).card_le_voters_count_of_participates E votes s X h

/-- The field `fgRoot_compatible_ofJustifiedBranch` of `ForkChoiceFacts` at `Model.specBase`:
    the FG root of `stH` is compatible with `T` when the finalized block is an ancestor of `T` and,
    if `h_max = h_j + 1`, the justified block is compatible with `T`. -/
theorem specBase_fgRoot_compatible_ofJustifiedBranch :
    ∀ {stH : (Model.specBase (V := V)).HS} {T : Block V} (hF : Block.Preceq stH.toFG.F T) (hJ : stH.toFG.h_max = stH.toFG.h_j + 1 → Block.compatible stH.toFG.J T = true), Block.compatible ((Model.specBase (V := V)).get_fg_root stH.toFG) T = true := by
  intro stH T hF hJ
  have := (Model.vocabulary_facts_forkChoice (V := V)).fgRoot_compatible_ofJustifiedBranch (stH := stH.toProof.toHealing) (T := T)
  sd_normalize
  exact this hF hJ

/-- The field `fgRoot_compatible_ofJustifiedBranch` of `ForkChoiceFacts` at `Model.spec`: the
    FG root of `stH` is compatible with `T` when the finalized block is an ancestor of `T` and, if
    `h_max = h_j + 1`, the justified block is compatible with `T`. -/
theorem spec_fgRoot_compatible_ofJustifiedBranch :
    ∀ {stH : (Model.spec (V := V)).HS} {T : Block V} (hF : Block.Preceq stH.toFG.F T) (hJ : stH.toFG.h_max = stH.toFG.h_j + 1 → Block.compatible stH.toFG.J T = true), Block.compatible ((Model.spec (V := V)).get_fg_root stH.toFG) T = true :=
  fun {stH} {T} hF hJ => specBase_fgRoot_compatible_ofJustifiedBranch (stH := stH.val) (T := T) hF hJ

/-- The field `fgRoot_compatible_of_compatible` of `ForkChoiceFacts` at `Model.specBase`: the
    FG root of `stH` is compatible with `B` when the finalized block is and, if `h_max = h_j + 1`,
    the justified block is too. -/
theorem specBase_fgRoot_compatible_of_compatible :
    ∀ {stH : (Model.specBase (V := V)).HS} {B : Block V} (hF : Block.compatible stH.toFG.F B = true) (hJ : stH.toFG.h_max = stH.toFG.h_j + 1 → Block.compatible stH.toFG.J B = true), Block.compatible ((Model.specBase (V := V)).get_fg_root stH.toFG) B = true := by
  intro stH B hF hJ
  have := (Model.vocabulary_facts_forkChoice (V := V)).fgRoot_compatible_of_compatible (stH := stH.toProof.toHealing) (B := B)
  sd_normalize
  exact this hF hJ

/-- The field `fgRoot_compatible_of_compatible` of `ForkChoiceFacts` at `Model.spec`: the FG
    root of `stH` is compatible with `B` when the finalized block is and, if `h_max = h_j + 1`, the
    justified block is too. -/
theorem spec_fgRoot_compatible_of_compatible :
    ∀ {stH : (Model.spec (V := V)).HS} {B : Block V} (hF : Block.compatible stH.toFG.F B = true) (hJ : stH.toFG.h_max = stH.toFG.h_j + 1 → Block.compatible stH.toFG.J B = true), Block.compatible ((Model.spec (V := V)).get_fg_root stH.toFG) B = true :=
  fun {stH} {B} hF hJ => specBase_fgRoot_compatible_of_compatible (stH := stH.val) (B := B) hF hJ

/-- The field `fgRoot_preceq` of `ForkChoiceFacts` at `Model.specBase`: the FG root is an
    ancestor of `T` when the finalized and justified blocks both are. -/
theorem specBase_fgRoot_preceq :
    ∀ {stH : (Model.specBase (V := V)).HS} {T : Block V} (hF : Block.Preceq stH.toFG.F T) (hJ : Block.Preceq stH.toFG.J T), Block.Preceq ((Model.specBase (V := V)).get_fg_root stH.toFG) T := by
  intro stH T hF hJ
  have := (Model.vocabulary_facts_forkChoice (V := V)).fgRoot_preceq (stH := stH.toProof.toHealing) (T := T)
  sd_normalize
  exact this hF hJ

/-- The field `fgRoot_preceq` of `ForkChoiceFacts` at `Model.spec`: the FG root is an ancestor
    of `T` when the finalized and justified blocks both are. -/
theorem spec_fgRoot_preceq :
    ∀ {stH : (Model.spec (V := V)).HS} {T : Block V} (hF : Block.Preceq stH.toFG.F T) (hJ : Block.Preceq stH.toFG.J T), Block.Preceq ((Model.spec (V := V)).get_fg_root stH.toFG) T :=
  fun {stH} {T} hF hJ => specBase_fgRoot_preceq (stH := stH.val) (T := T) hF hJ

/-- The field `fgRoot_preceq_ofJustifiedBranch` of `ForkChoiceFacts` at `Model.specBase`: the
    FG root of `stH` is an ancestor of `T` when the finalized block is and, if `h_max = h_j + 1`,
    the justified block is too. -/
theorem specBase_fgRoot_preceq_ofJustifiedBranch :
    ∀ {stH : (Model.specBase (V := V)).HS} {T : Block V} (hF : Block.Preceq stH.toFG.F T) (hJ : stH.toFG.h_max = stH.toFG.h_j + 1 → Block.Preceq stH.toFG.J T), Block.Preceq ((Model.specBase (V := V)).get_fg_root stH.toFG) T := by
  intro stH T hF hJ
  have := (Model.vocabulary_facts_forkChoice (V := V)).fgRoot_preceq_ofJustifiedBranch (stH := stH.toProof.toHealing) (T := T)
  sd_normalize
  exact this hF hJ

/-- The field `fgRoot_preceq_ofJustifiedBranch` of `ForkChoiceFacts` at `Model.spec`: the FG
    root of `stH` is an ancestor of `T` when the finalized block is and, if `h_max = h_j + 1`, the
    justified block is too. -/
theorem spec_fgRoot_preceq_ofJustifiedBranch :
    ∀ {stH : (Model.spec (V := V)).HS} {T : Block V} (hF : Block.Preceq stH.toFG.F T) (hJ : stH.toFG.h_max = stH.toFG.h_j + 1 → Block.Preceq stH.toFG.J T), Block.Preceq ((Model.spec (V := V)).get_fg_root stH.toFG) T :=
  fun {stH} {T} hF hJ => specBase_fgRoot_preceq_ofJustifiedBranch (stH := stH.val) (T := T) hF hJ

/-- The field `finalized_preceq_get_fg_root` of `ForkChoiceFacts` at `Model.specBase`: if the
    store's finalized block is an ancestor of its justified block, it is an ancestor of its FG root. -/
theorem specBase_finalized_preceq_get_fg_root :
    ∀ (st : (Model.specBase (V := V)).S) (hFJ : Block.Preceq st.F st.J), Block.Preceq st.F ((Model.specBase (V := V)).get_fg_root ((Model.specBase (V := V)).toHealing st).toFG) := by
  intro st hFJ
  have := (Model.vocabulary_facts_forkChoice (V := V)).finalized_preceq_get_fg_root st.toProof
  sd_normalize
  exact this hFJ

/-- The field `finalized_preceq_get_fg_root` of `ForkChoiceFacts` at `Model.spec`: if the
    store's finalized block is an ancestor of its justified block, it is an ancestor of its FG root. -/
theorem spec_finalized_preceq_get_fg_root :
    ∀ (st : (Model.spec (V := V)).S) (hFJ : Block.Preceq st.F st.J), Block.Preceq st.F ((Model.spec (V := V)).get_fg_root ((Model.spec (V := V)).toHealing st).toFG) :=
  fun st hFJ => specBase_finalized_preceq_get_fg_root st.val hFJ

/-- The field `get_fg_root_eq_J_or_F` of `ForkChoiceFacts` at `Model.specBase`: a store's FG
    root is its justified block `J` or its finalized block `F`. -/
theorem specBase_get_fg_root_eq_J_or_F :
    ∀ (st : (Model.specBase (V := V)).S), (Model.specBase (V := V)).get_fg_root ((Model.specBase (V := V)).toHealing st).toFG = st.J ∨
    (Model.specBase (V := V)).get_fg_root ((Model.specBase (V := V)).toHealing st).toFG = st.F := by
  intro st
  have := (Model.vocabulary_facts_forkChoice (V := V)).get_fg_root_eq_J_or_F st.toProof
  sd_normalize
  exact this

/-- The field `get_fg_root_eq_J_or_F` of `ForkChoiceFacts` at `Model.spec`: a store's FG root
    is its justified block `J` or its finalized block `F`. -/
theorem spec_get_fg_root_eq_J_or_F :
    ∀ (st : (Model.spec (V := V)).S), (Model.spec (V := V)).get_fg_root ((Model.spec (V := V)).toHealing st).toFG = st.J ∨
    (Model.spec (V := V)).get_fg_root ((Model.spec (V := V)).toHealing st).toFG = st.F :=
  fun st => specBase_get_fg_root_eq_J_or_F st.val

/-- The field `mem_latest_window_ge` of `ForkChoiceFacts` at `Model.spec`: a round in
    `latest_window eta r` is at least `r − eta`. -/
theorem spec_mem_latest_window_ge :
    ∀ {eta r k : Round} (hk : k ∈ (Model.spec (V := V)).latest_window eta r), r - eta ≤ k := by
  intro eta r k hk
  rw [spec_latest_window_eq] at hk
  exact (Model.vocabulary_facts_forkChoice (V := V)).mem_latest_window_ge hk

/-- The field `mem_latest_window_lt` of `ForkChoiceFacts` at `Model.spec`: a round in
    `latest_window eta r` is less than `r`. -/
theorem spec_mem_latest_window_lt :
    ∀ {eta r k : Round} (hk : k ∈ (Model.spec (V := V)).latest_window eta r), k < r := by
  intro eta r k hk
  rw [spec_latest_window_eq] at hk
  exact (Model.vocabulary_facts_forkChoice (V := V)).mem_latest_window_lt hk

/-- The field `proposer_view_eq` of `ForkChoiceFacts` at `Model.specBase`: the slot-`s`
    proposer view of `gs` is `gs`'s list of slot-`(s − 1)` Goldfish votes. -/
theorem specBase_proposer_view_eq :
    ∀ (gs : (Model.specBase (V := V)).GS) (s : Slot), (Model.specBase (V := V)).proposer_view gs s = gs.gf_votes (s - 1) := by
  intro gs s
  have := (Model.vocabulary_facts_forkChoice (V := V)).proposer_view_eq gs.toProof.toHealing.toFG.toSG.toGoldfishStore s
  change DecoupledConsensusModel.Protocol.proposer_view
    gs.toProof.toHealing.toFG.toSG.toGoldfishStore s = _ at this
  rw [toProof_proposer_view] at this
  exact this

/-- The field `proposer_view_eq` of `ForkChoiceFacts` at `Model.spec`: the slot-`s` proposer
    view of `gs` is `gs`'s list of slot-`(s − 1)` Goldfish votes. -/
theorem spec_proposer_view_eq :
    ∀ (gs : (Model.spec (V := V)).GS) (s : Slot), (Model.spec (V := V)).proposer_view gs s = gs.gf_votes (s - 1) :=
  fun gs s => specBase_proposer_view_eq gs.val s

/-- The field `proposer_view_toFinset` of `ForkChoiceFacts` at `Model.specBase`: the votes of
    the slot-`s` proposer view of `gs` are `gs_pool gs (s − 1)`. -/
theorem specBase_proposer_view_toFinset :
    ∀ (gs : (Model.specBase (V := V)).GS) (s : Slot), ((Model.specBase (V := V)).proposer_view gs s).toFinset = ((Model.specBase (V := V)).gs_pool gs (s - 1)) := by
  intro gs s
  have := (Model.vocabulary_facts_forkChoice (V := V)).proposer_view_toFinset gs.toProof.toHealing.toFG.toSG.toGoldfishStore s
  change (DecoupledConsensusModel.Protocol.proposer_view
    gs.toProof.toHealing.toFG.toSG.toGoldfishStore s).toFinset =
    DecoupledConsensusModel.Protocol.GoldfishStore.pool
      gs.toProof.toHealing.toFG.toSG.toGoldfishStore (s - 1) at this
  rw [toProof_proposer_view, toProof_gs_pool] at this
  exact this

/-- The field `proposer_view_toFinset` of `ForkChoiceFacts` at `Model.spec`: the votes of the
    slot-`s` proposer view of `gs` are `gs_pool gs (s − 1)`. -/
theorem spec_proposer_view_toFinset :
    ∀ (gs : (Model.spec (V := V)).GS) (s : Slot), ((Model.spec (V := V)).proposer_view gs s).toFinset = ((Model.spec (V := V)).gs_pool gs (s - 1)) :=
  fun gs s => specBase_proposer_view_toFinset gs.val s

/-- The field `voters_count_eq_of_participates` of `ForkChoiceFacts` at `Model.spec`: two vote
    sets with the same participating validators have the same participant count, at any two slots. -/
theorem spec_voters_count_eq_of_participates :
    ∀ (E : Env V) {votes votes' : Finset (GoldfishVote V)} (s s' : Slot) (h : ∀ w : V, (Model.spec (V := V)).participates votes w = (Model.spec (V := V)).participates votes' w), (Model.spec (V := V)).voters_count E votes s = (Model.spec (V := V)).voters_count E votes' s' := by
  intro E votes votes' s s' h
  rw [spec_participates_eq] at h
  rw [spec_voters_count_eq]
  exact (Model.vocabulary_facts_forkChoice (V := V)).voters_count_eq_of_participates E s s' h

/-! ## The Goldfish fork choice, the walk and the supporters -/

/-- The field `goldfish_passes_cone` of `ForkChoiceFacts` at `Model.spec`: if an honest,
    non-equivocating majority of slot `k`'s committee has votes in `support ⊆ votes`, valid for slot
    `k`, whose heads resolve to descendants of `B`, `A` is an ancestor of `B`, and the blocks after
    `A` up to `B` are in `tree`, then every outcome of the Goldfish fork choice from `A` over `tree`
    is a descendant of `B`. -/
theorem spec_goldfish_passes_cone :
    ∀ (E : Env V) (σ : Block V → (Model.spec (V := V)).CS) (h_max : Height) (T tree : Finset (Block V)) (cur : Slot) (votes support : Finset (GoldfishVote V)) (k : Slot) (Hon : Finset V) {A B : Block V} (hmaj : (E.committee k).card < 2 * ((E.committee k) ∩ Hon).card) (hcounted : votes ⊆ votes) (hsub : support ⊆ votes) (hno : ∀ x ∈ E.committee k, x ∈ Hon → (Model.spec (V := V)).equivocates votes x = false) (hvote : ∀ x ∈ E.committee k, x ∈ Hon → ∃ u ∈ support, u.val_index = x ∧ u.slot = k ∧ ∃ X : Block V, Block.find? T u.head = some X ∧ X.slot ≤ u.slot ∧ Block.Preceq B X) (hvalid : Protocol.VoteSetValid E k votes) (hAB : Block.Preceq A B) (hpath : ∀ C : Block V, Block.Preceq A C → C ≠ A → Block.Preceq C B → C ∈ tree) (X : Block V) (hX : (Model.spec (V := V)).goldfish_fork_choice E σ h_max T cur A tree votes support k ⇢ X), Block.Preceq B X
    := by
  intro E σ h_max T tree cur votes support k Hon A B hmaj hcounted hsub hno hvote hvalid hAB hpath X hX
  rw [ForkChoiceImages.spec_equivocates_eq] at hno
  exact (Model.vocabulary_facts_forkChoice (V := V)).goldfish_passes_cone E (fun C => (σ C).toProof)
    h_max T tree cur votes support k Hon hmaj hcounted hsub hno hvote hvalid hAB hpath X
    (ForkChoiceImages.vocabulary_returns_of_spec_goldfish_fork_choice E σ h_max T cur A tree
      votes support k hX)

/-- The field `ghost_passes_cone` of `ForkChoiceFacts` at `Model.spec`: if
    `support ⊆ votes ⊆ late`, the late votes are valid for slot `s`, an honest, non-equivocating
    majority of slot `s`'s committee has votes in `support` whose heads resolve to descendants of
    `B`, `A` is an ancestor of `B`, and the blocks after `A` up to `B` are in `tree`, then every
    outcome of the walk `ghost` from `A`, scored by a choice of Goldfish scores and admitting blocks
    whose score is more than half of the late voters, is a descendant of `B`. -/
theorem spec_ghost_passes_cone :
    ∀ (E : Env V) (T tree : Finset (Block V)) (votes support late : Finset (GoldfishVote V)) (s : Slot) (Hon : Finset V) {A B : Block V} (hmaj : (E.committee s).card < 2 * ((E.committee s) ∩ Hon).card) (hcounted : votes ⊆ late) (hsub : support ⊆ votes) (hno : ∀ x ∈ E.committee s, x ∈ Hon → (Model.spec (V := V)).equivocates votes x = false) (hvote : ∀ x ∈ E.committee s, x ∈ Hon → ∃ u ∈ support, u.val_index = x ∧ u.slot = s ∧ ∃ X : Block V, Block.find? T u.head = some X ∧ X.slot ≤ u.slot ∧ Block.Preceq B X) (hvalid : Protocol.VoteSetValid E s late) (hAB : Block.Preceq A B) (hpath : ∀ C : Block V, Block.Preceq A C → C ≠ A → Block.Preceq C B → C ∈ tree) (score : Block V → ℕ) (hscore : ∀ C, (Model.spec (V := V)).goldfish_score E T votes support s C ⇢ score C) (X : Block V) (hX : (Model.spec (V := V)).ghost A tree score (fun C => decide ((Model.spec (V := V)).voters_count E late s < 2 * score C)) ⇢ X), Block.Preceq B X
    := by
  rw [ForkChoiceImages.spec_equivocates_eq, ForkChoiceImages.spec_goldfish_score_eq,
    ForkChoiceImages.spec_ghost_eq, ForkChoiceImages.spec_voters_count_eq]
  exact (Model.vocabulary_facts_forkChoice (V := V)).ghost_passes_cone

/-- The field `goldfish_passes_cone_count` of `ForkChoiceFacts` at `Model.spec`: if the voters
    of `votes` at slot `k` are fewer than twice the committee members in `Hon`, none of those
    equivocates, each has a vote in `support ⊆ votes` whose head resolves to a descendant of `B`,
    `A` is an ancestor of `B`, and the blocks after `A` up to `B` are in `tree`, then every outcome
    of the Goldfish fork choice from `A` over `tree` is a descendant of `B`. -/
theorem spec_goldfish_passes_cone_count :
    ∀ (E : Env V) (σ : Block V → (Model.spec (V := V)).CS) (h_max : Height) (T tree : Finset (Block V)) (cur : Slot) (votes support : Finset (GoldfishVote V)) (k : Slot) (Hon : Finset V) {A B : Block V} (hcount : (Model.spec (V := V)).voters_count E votes k < 2 * ((E.committee k) ∩ Hon).card) (hsub : support ⊆ votes) (hno : ∀ x ∈ E.committee k, x ∈ Hon → (Model.spec (V := V)).equivocates votes x = false) (hvote : ∀ x ∈ E.committee k, x ∈ Hon → ∃ u ∈ support, u.val_index = x ∧ u.slot = k ∧ ∃ X : Block V, Block.find? T u.head = some X ∧ X.slot ≤ u.slot ∧ Block.Preceq B X) (hAB : Block.Preceq A B) (hpath : ∀ C : Block V, Block.Preceq A C → C ≠ A → Block.Preceq C B → C ∈ tree) (X : Block V) (hX : (Model.spec (V := V)).goldfish_fork_choice E σ h_max T cur A tree votes support k ⇢ X), Block.Preceq B X
    := by
  intro E σ h_max T tree cur votes support k Hon A B hcount hsub hno hvote hAB hpath X hX
  rw [ForkChoiceImages.spec_equivocates_eq] at hno
  rw [spec_voters_count_eq] at hcount
  exact (Model.vocabulary_facts_forkChoice (V := V)).goldfish_passes_cone_count E (fun C => (σ C).toProof)
    h_max T tree cur votes support k Hon hcount hsub hno hvote hAB hpath X
    (ForkChoiceImages.vocabulary_returns_of_spec_goldfish_fork_choice E σ h_max T cur A tree
      votes support k hX)

/-- The field `ghost_passes_cone_count` of `ForkChoiceFacts` at `Model.spec`: if the voters of
    `late` at slot `s` are fewer than twice the committee members in `Hon`, `support ⊆ votes ⊆
    late`, none of those members equivocates, each has a vote in `support` whose head resolves to a
    descendant of `B`, `A` is an ancestor of `B`, and the blocks after `A` up to `B` are in `tree`,
    then every outcome of the walk `ghost` from `A`, scored by a choice of Goldfish scores and
    admitting blocks whose score is more than half of the late voters, is a descendant of `B`. -/
theorem spec_ghost_passes_cone_count :
    ∀ (E : Env V) (T tree : Finset (Block V)) (votes support late : Finset (GoldfishVote V)) (s : Slot) (Hon : Finset V) {A B : Block V} (hcount : (Model.spec (V := V)).voters_count E late s < 2 * ((E.committee s) ∩ Hon).card) (hcounted : votes ⊆ late) (hsub : support ⊆ votes) (hno : ∀ x ∈ E.committee s, x ∈ Hon → (Model.spec (V := V)).equivocates votes x = false) (hvote : ∀ x ∈ E.committee s, x ∈ Hon → ∃ u ∈ support, u.val_index = x ∧ u.slot = s ∧ ∃ X : Block V, Block.find? T u.head = some X ∧ X.slot ≤ u.slot ∧ Block.Preceq B X) (hAB : Block.Preceq A B) (hpath : ∀ C : Block V, Block.Preceq A C → C ≠ A → Block.Preceq C B → C ∈ tree) (score : Block V → ℕ) (hscore : ∀ C, (Model.spec (V := V)).goldfish_score E T votes support s C ⇢ score C) (X : Block V) (hX : (Model.spec (V := V)).ghost A tree score (fun C => decide ((Model.spec (V := V)).voters_count E late s < 2 * score C)) ⇢ X), Block.Preceq B X
    := by
  rw [ForkChoiceImages.spec_equivocates_eq, ForkChoiceImages.spec_goldfish_score_eq,
    ForkChoiceImages.spec_ghost_eq, ForkChoiceImages.spec_voters_count_eq]
  exact (Model.vocabulary_facts_forkChoice (V := V)).ghost_passes_cone_count

/-- The field `ConeSupport_eligible_count` of `ForkChoiceFacts` at `Model.spec`: if the voters
    of `late` at slot `s` are fewer than twice the committee members in `Hon`, `support ⊆ votes ⊆
    late`, none of those members equivocates, each has a vote in `support` whose head resolves to a
    block `tgt` admits, and `C` is an ancestor of every such block, then the late voters of slot `s`
    are fewer than twice every Goldfish score of `C`. -/
theorem spec_ConeSupport_eligible_count :
    ∀ (E : Env V) (T : Finset (Block V)) (votes support late : Finset (GoldfishVote V)) (s : Slot) (Hon : Finset V) (tgt : Block V → Prop) {C : Block V} (hcount : (Model.spec (V := V)).voters_count E late s < 2 * ((E.committee s) ∩ Hon).card) (hcounted : votes ⊆ late) (hsub : support ⊆ votes) (hno : ∀ x ∈ E.committee s, x ∈ Hon → (Model.spec (V := V)).equivocates votes x = false) (hvote : ∀ x ∈ E.committee s, x ∈ Hon → ∃ u ∈ support, u.val_index = x ∧ u.slot = s ∧ ∃ X : Block V, Block.find? T u.head = some X ∧ X.slot ≤ u.slot ∧ tgt X) (hC : ∀ X : Block V, tgt X → Block.preceq C X = true) (g : ℕ) (hg : (Model.spec (V := V)).goldfish_score E T votes support s C ⇢ g), (Model.spec (V := V)).voters_count E late s < 2 * g
    := by
  rw [ForkChoiceImages.spec_equivocates_eq, ForkChoiceImages.spec_goldfish_score_eq,
    ForkChoiceImages.spec_voters_count_eq]
  exact (Model.vocabulary_facts_forkChoice (V := V)).ConeSupport_eligible_count

/-- The field `voters_count_le_card_of_valIndex` of `ForkChoiceFacts` at `Model.spec`: if every
    vote of `votes` names a member of `X`, the participant count is at most the size of `X`. -/
theorem spec_voters_count_le_card_of_valIndex :
    ∀ (E : Env V) (votes : Finset (GoldfishVote V)) (s : Slot) (X : Finset V) (h : ∀ u ∈ votes, u.val_index ∈ X), (Model.spec (V := V)).voters_count E votes s ≤ X.card := by
  intro E votes s X h
  rw [spec_voters_count_eq]
  exact (Model.vocabulary_facts_forkChoice (V := V)).voters_count_le_card_of_valIndex E votes s X h

/-- The field `eligible_compatible` of `ForkChoiceFacts` at `Model.spec`: if each of two views
    counts its early votes with no second vote in its late votes, every vote one view counts is in
    the other's late votes or its validator equivocates there, the two trees resolve counted heads
    to the same block, and each view gives its block a Goldfish score more than half of its late
    voters, then the two blocks are ancestor-comparable. -/
theorem spec_eligible_compatible :
    ∀ {E : Env V} {Tv Tw : Finset (Block V)}
    {earlyv latev votesv earlyw latew votesw : Finset (GoldfishVote V)} {s : Slot}
    {C D : Block V}
    (hNv_early_late : earlyv ⊆ latev)
    (hNv_filtered : votesv = earlyv.filter (fun u => (Model.spec (V := V)).no_second_vote_in latev u = true))
    (hNw_early_late : earlyw ⊆ latew)
    (hNw_filtered : votesw = earlyw.filter (fun u => (Model.spec (V := V)).no_second_vote_in latew u = true))
    (hvw_transfer : ∀ u ∈ votesv, u ∈ latew ∨ (Model.spec (V := V)).equivocates latew u.val_index = true)
    (hvw_resolve : ∀ u ∈ votesv, ∀ B C : Block V,
      Block.find? Tv u.head = some B → Block.find? Tw u.head = some C → B = C)
    (hwv_transfer : ∀ u ∈ votesw, u ∈ latev ∨ (Model.spec (V := V)).equivocates latev u.val_index = true)
    (hwv_resolve : ∀ u ∈ votesw, ∀ B C : Block V,
      Block.find? Tw u.head = some B → Block.find? Tv u.head = some C → B = C)
    (gC : ℕ) (hgC : (Model.spec (V := V)).goldfish_score E Tv votesv votesv s C ⇢ gC)
    (hC : (Model.spec (V := V)).voters_count E latev s < 2 * gC)
    (gD : ℕ) (hgD : (Model.spec (V := V)).goldfish_score E Tw votesw votesw s D ⇢ gD)
    (hD : (Model.spec (V := V)).voters_count E latew s < 2 * gD),
    Block.compatible C D = true
    := by
  rw [ForkChoiceImages.spec_no_second_vote_in_eq, ForkChoiceImages.spec_equivocates_eq,
    ForkChoiceImages.spec_goldfish_score_eq, ForkChoiceImages.spec_voters_count_eq]
  exact (Model.vocabulary_facts_forkChoice (V := V)).eligible_compatible

/-- The field `confirmation_adoption` of `ForkChoiceFacts` at `Model.spec`: if the source
    counts its early votes with no second vote in its late votes, every source vote supporting `B`
    is a supporting target vote or its validator equivocates at the target, every target vote is a
    source late vote or its validator equivocates at the source, and `B`'s Goldfish score at the
    source is more than half of the source voters, then the source supporters of `B` are among the
    target supporters, which are more than half of the target voters. -/
theorem spec_confirmation_adoption :
    ∀ {E : Env V} {sourceTree targetTree : Finset (Block V)}
    {sourceEarly sourceLate sourceVotes targetVotes targetSupport : Finset (GoldfishVote V)}
    {s : Slot} {B : Block V}
    (hN_early_late : sourceEarly ⊆ sourceLate)
    (hN_filtered : sourceVotes = sourceEarly.filter (fun u => (Model.spec (V := V)).no_second_vote_in sourceLate u = true))
    (tS : GoldfishVote V → Bool) (htS : ∀ u, (Model.spec (V := V)).targets_under sourceTree B u ⇢ tS u)
    (tT : GoldfishVote V → Bool) (htT : ∀ u, (Model.spec (V := V)).targets_under targetTree B u ⇢ tT u)
    (hT_forward : ∀ u ∈ sourceVotes, tS u = true →
      (u ∈ targetSupport ∧ tT u = true) ∨
        (Model.spec (V := V)).equivocates targetVotes u.val_index = true)
    (hT_backward : ∀ u ∈ targetVotes, u ∈ sourceLate ∨ (Model.spec (V := V)).equivocates sourceLate u.val_index = true)
    (g : ℕ) (hg : (Model.spec (V := V)).goldfish_score E sourceTree sourceVotes sourceVotes s B ⇢ g)
    (heligible : (Model.spec (V := V)).voters_count E sourceLate s < 2 * g)
    (sS : Finset V) (hsS : (Model.spec (V := V)).raw_supporters sourceTree sourceVotes sourceVotes s B ⇢ sS)
    (sT : Finset V) (hsT : (Model.spec (V := V)).raw_supporters targetTree targetVotes targetSupport s B ⇢ sT),
    sS ⊆ sT ∧ (Model.spec (V := V)).voters_count E targetVotes s < 2 * sT.card
    := by
  rw [ForkChoiceImages.spec_no_second_vote_in_eq, ForkChoiceImages.spec_targets_under_eq,
    ForkChoiceImages.spec_equivocates_eq, ForkChoiceImages.spec_goldfish_score_eq,
    ForkChoiceImages.spec_voters_count_eq, ForkChoiceImages.spec_raw_supporters_eq]
  exact (Model.vocabulary_facts_forkChoice (V := V)).confirmation_adoption

/-- The field `goldfish_fork_choice_captures_supporter_majority` of `ForkChoiceFacts` at
    `Model.spec`: if `support ⊆ votes`, the supporters of `B` are more than half of the
    participant count, `A` and `B` are compatible, and, when `A ⪯ B`, the blocks after `A` up to `B`
    are in `tree`, then `B` is an ancestor of every outcome of the Goldfish fork choice from `A`, or
    that outcome itself. -/
theorem spec_goldfish_fork_choice_captures_supporter_majority :
    ∀ (E : Env V) (σ : Block V → (Model.spec (V := V)).CS)
    (h_max : Height) (T tree : Finset (Block V)) (cur : Slot)
    (votes support : Finset (GoldfishVote V)) (s : Slot) {A B : Block V}
    (hsub : support ⊆ votes)
    (sup : Finset V) (hsup : (Model.spec (V := V)).raw_supporters T votes support s B ⇢ sup)
    (hmajority : (Model.spec (V := V)).voters_count E votes s < 2 * sup.card)
    (hcompatible : Block.compatible A B = true)
    (hpath : Block.Preceq A B → ∀ C : Block V, Block.Preceq A C → C ≠ A → Block.Preceq C B → C ∈ tree)
    (X : Block V) (hX : (Model.spec (V := V)).goldfish_fork_choice E σ h_max T cur A tree votes support s ⇢ X),
    Block.Preceq B X
    := by
  intro E σ h_max T tree cur votes support s A B hsub sup hsup hmajority hcompatible hpath X hX
  rw [ForkChoiceImages.spec_raw_supporters_eq] at hsup
  rw [ForkChoiceImages.spec_voters_count_eq] at hmajority
  exact (Model.vocabulary_facts_forkChoice (V := V)).goldfish_fork_choice_captures_supporter_majority
    E (fun C => (σ C).toProof) h_max T tree cur votes support s hsub sup hsup hmajority hcompatible
    hpath X (ForkChoiceImages.vocabulary_returns_of_spec_goldfish_fork_choice E σ h_max T cur A
      tree votes support s hX)

/-- The field `mem_supporters_iff` of `ForkChoiceFacts` at `Model.spec`: for every outcome `R`
    of `raw_supporters T votes support_votes s B` and every choice `t` of outcomes of the supporter
    test `targets_under T B u`, `x` is in `R` exactly when `x` does not equivocate in `votes` and
    has a slot-`s` vote `u` in `support_votes` with `t u = true`. -/
theorem spec_mem_supporters_iff :
    ∀ {_E : Env V} {T : Finset (Block V)} {votes support_votes : Finset (GoldfishVote V)} {s : Slot} {B : Block V} {x : V} (R : Finset V) (hR : (Model.spec (V := V)).raw_supporters T votes support_votes s B ⇢ R) (t : GoldfishVote V → Bool) (ht : ∀ u, (Model.spec (V := V)).targets_under T B u ⇢ t u), x ∈ R ↔ (Model.spec (V := V)).equivocates votes x = false ∧ ∃ u ∈ (Model.spec (V := V)).votes_by support_votes x, u.slot = s ∧ t u = true
    := by
  rw [ForkChoiceImages.spec_raw_supporters_eq, ForkChoiceImages.spec_targets_under_eq,
    ForkChoiceImages.spec_equivocates_eq, ForkChoiceImages.spec_votes_by_eq]
  exact fun {_E} => (Model.vocabulary_facts_forkChoice (V := V)).mem_supporters_iff (_E := _E)

/-- The field `ghost_step_child` of `ForkChoiceFacts` at `Model.spec`: if one step of the walk
    from `H` returns `some C`, then `C` is in the tree, its parent is `H`, and it is eligible. -/
theorem spec_ghost_step_child :
    ∀ {tree : Finset (Block V)} {score : Block V → ℕ}
    {eligible : Block V → Bool} {H C : Block V} (o : Option (Block V)),
    (Model.spec (V := V)).ghost_step tree score eligible H ⇢ o → o = some C →
      C ∈ tree ∧ C.parent? = some H ∧ eligible C = true
    := by
  rw [ForkChoiceImages.spec_ghost_step_eq]
  exact (Model.vocabulary_facts_forkChoice (V := V)).ghost_step_child

/-- The field `ghost_transport_via_bridge_of_target_passes` of `ForkChoiceFacts` at
    `Model.spec`: suppose both trees have injective roots, the source walk from `sourceAnchor`
    ends at `H`, `sourceAnchor ⪯ bridge ⪯ H`, `targetAnchor ⪯ H` with the blocks after
    `targetAnchor` up to `H` in the target tree, `bridge` is an ancestor of the target walk's
    outcome `G'`, the source steps from `bridge` towards `H` land on target-eligible blocks of the
    target tree, every target-eligible child of a block between `bridge` and `H` is a
    source-eligible block of the source tree, and the two scores agree on both trees; then no child
    of `H` in the target tree is target-eligible, and `G'` is `H`. -/
theorem spec_ghost_transport_via_bridge_of_target_passes :
    ∀ {sourceTree targetTree : Finset (Block V)}
    {sourceScore targetScore : Block V → ℕ} {sourceEligible targetEligible : Block V → Bool}
    {sourceAnchor targetAnchor bridge H : Block V},
    DecoupledConsensusModel.Execution.RootInjectiveBelow sourceTree →
    DecoupledConsensusModel.Execution.RootInjectiveBelow targetTree →
    ∀ G : Block V, (Model.spec (V := V)).ghost sourceAnchor sourceTree sourceScore sourceEligible ⇢ G → G = H →
    Block.Preceq sourceAnchor bridge → Block.Preceq bridge H → Block.Preceq targetAnchor H →
    (∀ (C : Block V), Block.Preceq targetAnchor C → C ≠ targetAnchor → Block.Preceq C H →
      C ∈ targetTree) →
    ∀ G' : Block V, (Model.spec (V := V)).ghost targetAnchor targetTree targetScore targetEligible ⇢ G' →
    Block.Preceq bridge G' →
    ∀ step : Block V → Option (Block V),
    (∀ X, (Model.spec (V := V)).ghost_step sourceTree sourceScore sourceEligible X ⇢ step X) →
    (∀ (X C : Block V), Block.Preceq bridge X → Block.Preceq X H → X ≠ H →
      step X = some C → Block.Preceq C H →
      C ∈ targetTree ∧ targetEligible C = true) →
    (∀ (X C : Block V), Block.Preceq bridge X → Block.Preceq X H → C ∈ targetTree →
      C.parent? = some X → targetEligible C = true →
      C ∈ sourceTree ∧ sourceEligible C = true) →
    (∀ C ∈ sourceTree, C ∈ targetTree → targetScore C = sourceScore C) →
    (∀ C ∈ targetTree, C.parent? = some H → targetEligible C = false) ∧ G' = H
    := by
  rw [ForkChoiceImages.spec_ghost_eq, ForkChoiceImages.spec_ghost_step_eq]
  exact (Model.vocabulary_facts_forkChoice (V := V)).ghost_transport_via_bridge_of_target_passes

/-- The field `ghost_eq_of_compatible_anchor_and_terminal` of `ForkChoiceFacts` at
    `Model.spec`: if `A` and `B` are compatible, `B ⪯ G` whenever `A ⪯ B`, `A = B` whenever
    `B ⪯ A`, and no block of `tree` other than `B` descends from `B`, then the outcome `G` of the
    walk from `A` is `B`. -/
theorem spec_ghost_eq_of_compatible_anchor_and_terminal :
    ∀ {tree : Finset (Block V)} {score : Block V → Nat} {eligible : Block V → Bool} {A B : Block V} (G : Block V) (hG : (Model.spec (V := V)).ghost A tree score eligible ⇢ G) (hcompat : Block.compatible A B = true) (hforward : Block.Preceq A B →
    Block.Preceq B G) (hanchorTerminal : Block.Preceq B A → A = B) (htreeTerminal : ∀ X ∈ tree, Block.Preceq B X → X = B), G = B
    := by
  rw [ForkChoiceImages.spec_ghost_eq]
  exact (Model.vocabulary_facts_forkChoice (V := V)).ghost_eq_of_compatible_anchor_and_terminal

/-- The field `ghost_insert_eq` of `ForkChoiceFacts` at `Model.spec`: if the walk from `A` over
    `tree` ends at `H`, and `B` is an eligible child of `H` not in `tree`, with no eligible sibling
    and no child in `tree`, then the walk from `A` over `insert B tree` ends at `B`. -/
theorem spec_ghost_insert_eq :
    ∀ {tree : Finset (Block V)} {score : Block V → Nat} {eligible : Block V → Bool} {A B H : Block V} (hpar : B.parent? = some H) (helig : eligible B = true) (hnotin : B ∉ tree) (hstop : ∀ C ∈ tree, C.parent? = some H → eligible C = false) (hfresh : ∀ C ∈ tree, C.parent? ≠ some B) (G : Block V) (hG : (Model.spec (V := V)).ghost A tree score eligible ⇢ G) (hwalk : G = H) (G' : Block V) (hG' : (Model.spec (V := V)).ghost A (insert B tree) score eligible ⇢ G'), G' = B
    := by
  rw [ForkChoiceImages.spec_ghost_eq]
  exact (Model.vocabulary_facts_forkChoice (V := V)).ghost_insert_eq

/-- The field `goldfish_eligible_iff` of `ForkChoiceFacts` at `Model.spec`: an outcome of
    `goldfish_eligible` for `B` is `true` exactly when the chain-state height of `B`'s parent is
    less than `h_max − 1`, or the participant count is less than twice `B`'s Goldfish score, or
    `B`'s slot is `cur`. -/
theorem spec_goldfish_eligible_iff :
    ∀ (E : Env V) (σ : Block V → (Model.spec (V := V)).CS) (h_max : Height) (T : Finset (Block V)) (cur : Slot) (votes support_votes : Finset (GoldfishVote V)) (s : Slot) (B : Block V) (e : Bool) (he : (Model.spec (V := V)).goldfish_eligible E σ h_max T cur votes support_votes s B ⇢ e) (g : ℕ) (hg : (Model.spec (V := V)).goldfish_score E T votes support_votes s B ⇢ g), e = true ↔
    ((σ B.parent).h < h_max - 1 ∨
    (Model.spec (V := V)).voters_count E votes s <
    2 * g ∨
    B.slot = cur)
    := by
  intro E σ h_max T cur votes support_votes s B e he g hg
  rw [ForkChoiceImages.spec_goldfish_eligible_eq] at he
  rw [ForkChoiceImages.spec_goldfish_score_eq] at hg
  rw [ForkChoiceImages.spec_voters_count_eq]
  exact (Model.vocabulary_facts_forkChoice (V := V)).goldfish_eligible_iff E (fun C => (σ C).toProof)
    h_max T cur votes support_votes s B e he g hg

/-- The field `ghost_mem` of `ForkChoiceFacts` at `Model.spec`: every outcome of the walk from
    `anchor` over `tree` is `anchor` or a block of `tree`. -/
theorem spec_ghost_mem :
    ∀ (anchor : Block V) (tree : Finset (Block V)) (score : Block V → Nat) (eligible : Block V → Bool) (G : Block V), (Model.spec (V := V)).ghost anchor tree score eligible ⇢ G → G = anchor ∨
    G ∈ tree
    := by
  rw [ForkChoiceImages.spec_ghost_eq]
  exact (Model.vocabulary_facts_forkChoice (V := V)).ghost_mem

/-- The field `ghost_eligible` of `ForkChoiceFacts` at `Model.spec`: every outcome of the walk
    from `anchor` is `anchor` or a block that passes `eligible`. -/
theorem spec_ghost_eligible :
    ∀ (anchor : Block V) (tree : Finset (Block V)) (score : Block V → Nat) (eligible : Block V → Bool) (G : Block V), (Model.spec (V := V)).ghost anchor tree score eligible ⇢ G → G = anchor ∨
    eligible G = true
    := by
  rw [ForkChoiceImages.spec_ghost_eq]
  exact (Model.vocabulary_facts_forkChoice (V := V)).ghost_eligible

/-- The field `ghost_preceq` of `ForkChoiceFacts` at `Model.spec`: `anchor` is an ancestor of
    every outcome of the walk from `anchor`, or that outcome itself. -/
theorem spec_ghost_preceq :
    ∀ (anchor : Block V) (tree : Finset (Block V)) (score : Block V → Nat) (eligible : Block V → Bool) (G : Block V), (Model.spec (V := V)).ghost anchor tree score eligible ⇢ G → Block.Preceq anchor G
    := by
  rw [ForkChoiceImages.spec_ghost_eq]
  exact (Model.vocabulary_facts_forkChoice (V := V)).ghost_preceq

/-- The field `targets_under_iff` of `ForkChoiceFacts` at `Model.spec`: an outcome of the
    supporter test `targets_under T B u` is `true` exactly when `u`'s head resolves in `T` to a
    descendant of `B`, or `B` itself, whose slot is at most `u`'s slot. -/
theorem spec_targets_under_iff :
    ∀ {T : Finset (Block V)} {B : Block V} {u : GoldfishVote V} (b : Bool), (Model.spec (V := V)).targets_under T B u ⇢ b → (b = true ↔
    ∃ B', Block.find? T u.head = some B' ∧ B'.slot ≤ u.slot ∧
    Block.preceq B B' = true)
    := by
  rw [ForkChoiceImages.spec_targets_under_eq]
  exact (Model.vocabulary_facts_forkChoice (V := V)).targets_under_iff

/-- The field `goldfish_eligible_eq_false_of_parent_fork_choice` of `ForkChoiceFacts` at
    `Model.spec`: in a tree with injective roots, a block `C` of `tree` whose parent is an
    outcome of the Goldfish fork choice from `A` through `tree` fails `goldfish_eligible`. -/
theorem spec_goldfish_eligible_eq_false_of_parent_fork_choice :
    ∀ {E : Env V} {σ : Block V → (Model.spec (V := V)).CS} {h_max : Height} {T : Finset (Block V)} {cur : Slot} {A : Block V} {tree : Finset (Block V)} {votes support : Finset (GoldfishVote V)} {s : Slot} {C : Block V} (hroot : Execution.RootInjectiveBelow tree) (hC : C ∈ tree) (X : Block V) (hX : (Model.spec (V := V)).goldfish_fork_choice E σ h_max T cur A tree votes support s ⇢ X) (hparent : C.parent? =
    some X) (e : Bool) (he : (Model.spec (V := V)).goldfish_eligible E σ h_max T cur votes support s C ⇢ e), e = false
    := by
  intro E σ h_max T cur A tree votes support s C hroot hC X hX hparent e he
  rw [ForkChoiceImages.spec_goldfish_eligible_eq] at he
  exact (Model.vocabulary_facts_forkChoice (V := V)).goldfish_eligible_eq_false_of_parent_fork_choice
    hroot hC X (ForkChoiceImages.vocabulary_returns_of_spec_goldfish_fork_choice E σ h_max T cur A
      tree votes support s hX) hparent e he

/-- The field `goldfish_fork_choice_eq_child_of_pivot` of `ForkChoiceFacts` at `Model.spec`:
    the voter's Goldfish fork choice from `Av` through `Tv` ends at `B` when the proposer's ends at
    `P`, both start from ancestors of a block `Y ⪯ P`, the voter's outcome descends from `Y`, the
    two stores agree between `Y` and `P` (the hypotheses `hhP`, `hhV`, `hscore`, `hcount`, `hpathV`,
    `hchildV`), and `B` is the only block of slot `cur` in `Tv`, a child of `P` with no child in
    `Tv`. -/
theorem spec_goldfish_fork_choice_eq_child_of_pivot :
    ∀ (E : Env V) {σp σv : Block V → (Model.spec (V := V)).CS} {hp hv : Height} {TPs TVs Tp Tv : Finset (Block V)} {cur : Slot} {votesP supportP votesV supportV : Finset (GoldfishVote V)} {s' : Slot} {Ap Av Y P B : Block V} (hrootP : RootInjectiveBelow Tp) (hrootV : RootInjectiveBelow Tv) (GP : Block V) (hGP : (Model.spec (V := V)).goldfish_fork_choice E σp hp TPs cur Ap Tp votesP supportP s' ⇢ GP) (hsource : GP = P) (hApY : Block.Preceq Ap Y) (hAvY : Block.Preceq Av Y) (hYP : Block.Preceq Y P) (GV : Block V) (hGV : (Model.spec (V := V)).goldfish_fork_choice E σv hv TVs cur Av Tv votesV supportV s' ⇢ GV) (hpasses : Block.Preceq Y
    GV) (hhP : ∀ X, Block.Preceq Y X → Block.Preceq X P → hp - 1 ≤ (σp X).h) (hhV : ∀ X, Block.Preceq Y X → Block.Preceq X P → hv - 1 ≤ (σv X).h) (scV : Block V → ℕ) (hscV : ∀ C, (Model.spec (V := V)).goldfish_score E TVs votesV supportV s' C ⇢ scV C) (scP : Block V → ℕ) (hscP : ∀ C, (Model.spec (V := V)).goldfish_score E TPs votesP supportP s' C ⇢ scP C) (hscore : ∀ C, Block.Preceq Y C →
    scV C =
    scP C) (hcount : (Model.spec (V := V)).voters_count E votesV s' = (Model.spec (V := V)).voters_count E votesP s') (hpathV : ∀ C, Block.Preceq Y C → C ≠ Y → Block.Preceq C P → C ∈ Tv) (hchildV : ∀ X C, Block.Preceq Y X → Block.Preceq X P → C ∈ Tv → C.parent? = some X →
    C.slot ≠ cur → C ∈ Tp) (hBonly : ∀ C ∈ Tv, C.slot = cur → C = B) (hB : B ∈ Tv) (hBpar : B.parent? = some P) (hBslot : B.slot = cur) (hfresh : ∀ C ∈ Tv, C.parent? ≠ some B), GV = B
    := by
  intro E σp σv hp hv TPs TVs Tp Tv cur votesP supportP votesV supportV s' Ap Av Y P B hrootP hrootV
    GP hGP hsource hApY hAvY hYP GV hGV hpasses hhP hhV scV hscV scP hscP hscore hcount hpathV
    hchildV hBonly hB hBpar hBslot hfresh
  rw [ForkChoiceImages.spec_goldfish_score_eq] at hscV hscP
  rw [ForkChoiceImages.spec_voters_count_eq] at hcount
  exact (Model.vocabulary_facts_forkChoice (V := V)).goldfish_fork_choice_eq_child_of_pivot E
    (σp := fun C => (σp C).toProof) (σv := fun C => (σv C).toProof) hrootP hrootV GP
    (ForkChoiceImages.vocabulary_returns_of_spec_goldfish_fork_choice E σp hp TPs cur Ap Tp
      votesP supportP s' hGP) hsource hApY hAvY hYP GV
    (ForkChoiceImages.vocabulary_returns_of_spec_goldfish_fork_choice E σv hv TVs cur Av Tv
      votesV supportV s' hGV) hpasses hhP hhV scV hscV scP hscP hscore hcount hpathV hchildV
    hBonly hB hBpar hBslot hfresh

/-- The field `goldfish_score_eq_of_iff` of `ForkChoiceFacts` at `Model.spec`: if the same
    validators equivocate in `votes` and `votes'`, and each non-equivocating validator supports `C`
    in `support` exactly when it does in `support'`, then the Goldfish scores of `C` in the two
    settings are equal. -/
theorem spec_goldfish_score_eq_of_iff :
    ∀ (E : Env V) {T T' : Finset (Block V)} {votes support votes' support' : Finset (GoldfishVote V)} (s : Slot) (C : Block V) (heq : ∀ w : V, (Model.spec (V := V)).equivocates votes w = (Model.spec (V := V)).equivocates votes' w) (t : GoldfishVote V → Bool) (ht : ∀ u, (Model.spec (V := V)).targets_under T C u ⇢ t u) (t' : GoldfishVote V → Bool) (ht' : ∀ u, (Model.spec (V := V)).targets_under T' C u ⇢ t' u) (hsup : ∀ w : V, (Model.spec (V := V)).equivocates votes w = false →
    ((∃ u ∈ support, u.val_index = w ∧ u.slot = s ∧ t u = true) ↔
    (∃ u ∈ support', u.val_index = w ∧ u.slot = s ∧
    t' u = true))) (g : ℕ) (hg : (Model.spec (V := V)).goldfish_score E T votes support s C ⇢ g) (g' : ℕ) (hg' : (Model.spec (V := V)).goldfish_score E T' votes' support' s C ⇢ g'), g =
    g'
    := by
  rw [ForkChoiceImages.spec_equivocates_eq, ForkChoiceImages.spec_targets_under_eq,
    ForkChoiceImages.spec_goldfish_score_eq]
  exact (Model.vocabulary_facts_forkChoice (V := V)).goldfish_score_eq_of_iff

/-- The field `targets_under_eq_true_iff` of `ForkChoiceFacts` at `Model.spec`: an outcome of
    the supporter test `targets_under T B u` is `true` exactly when `u`'s head resolves in `T` to a
    block `X` with `B ⪯ X` whose slot is at most `u`'s slot. -/
theorem spec_targets_under_eq_true_iff :
    ∀ (T : Finset (Block V)) (B : Block V) (u : GoldfishVote V) (b : Bool) (hb : (Model.spec (V := V)).targets_under T B u ⇢ b), b = true ↔
    ∃ X, Block.find? T u.head = some X ∧ X.slot ≤ u.slot ∧ Block.Preceq B X
    := by
  rw [ForkChoiceImages.spec_targets_under_eq]
  exact (Model.vocabulary_facts_forkChoice (V := V)).targets_under_eq_true_iff

/-- The field `ConeSupport_eligible` of `ForkChoiceFacts` at `Model.spec`: if
    `support ⊆ votes ⊆ late`, the late votes are valid for slot `s`, an honest, non-equivocating
    majority of slot `s`'s committee has votes in `support` whose heads resolve to blocks `tgt`
    admits, and `C` is an ancestor of every such block, then the late voters of slot `s` are fewer
    than twice every Goldfish score of `C`. -/
theorem spec_ConeSupport_eligible :
    ∀ (E : Env V) (T : Finset (Block V)) (votes support late : Finset (GoldfishVote V)) (s : Slot) (Hon : Finset V) (tgt : Block V → Prop) {C : Block V} (hmaj : (E.committee s).card < 2 * ((E.committee s) ∩ Hon).card) (hcounted : votes ⊆ late) (hsub : support ⊆ votes) (hno : ∀ x ∈ E.committee s, x ∈ Hon → (Model.spec (V := V)).equivocates votes x = false) (hvote : ∀ x ∈ E.committee s, x ∈ Hon → ∃ u ∈ support, u.val_index = x ∧ u.slot = s ∧ ∃ X : Block V, Block.find? T u.head = some X ∧ X.slot ≤ u.slot ∧ tgt X) (hvalid : Protocol.VoteSetValid E s late) (hC : ∀ X : Block V, tgt X → Block.preceq C X = true) (g : ℕ) (hg : (Model.spec (V := V)).goldfish_score E T votes support s C ⇢ g), (Model.spec (V := V)).voters_count E late s < 2 * g
    := by
  rw [ForkChoiceImages.spec_equivocates_eq, ForkChoiceImages.spec_goldfish_score_eq,
    ForkChoiceImages.spec_voters_count_eq]
  exact (Model.vocabulary_facts_forkChoice (V := V)).ConeSupport_eligible

/-- The field `goldfish_score_le_of_Preceq` of `ForkChoiceFacts` at `Model.spec`: if `D ⪯ C`,
    the Goldfish score of `C` is at most that of `D`, over the same tree, votes and slot. -/
theorem spec_goldfish_score_le_of_Preceq :
    ∀ (E : Env V) (T : Finset (Block V))
    (votes support : Finset (GoldfishVote V)) (s : Slot) {C D : Block V},
    Block.Preceq D C →
    ∀ gC : ℕ, (Model.spec (V := V)).goldfish_score E T votes support s C ⇢ gC →
    ∀ gD : ℕ, (Model.spec (V := V)).goldfish_score E T votes support s D ⇢ gD →
    gC ≤ gD
    := by
  rw [ForkChoiceImages.spec_goldfish_score_eq]
  exact (Model.vocabulary_facts_forkChoice (V := V)).goldfish_score_le_of_Preceq

/-- The field `Numerator_score_eq_supporters` of `ForkChoiceFacts` at `Model.spec`: when
    `votes` is the votes of `early ⊆ late` with no second vote in `late`, the Goldfish score of `B`
    over `votes` is the number of supporters of `B` over `votes`. -/
theorem spec_Numerator_score_eq_supporters :
    ∀ (early late votes : Finset (GoldfishVote V)), early ⊆ late →
    votes = early.filter (fun u => (Model.spec (V := V)).no_second_vote_in late u = true) →
    ∀ (E : Env V) (T : Finset (Block V)) (s : Slot) (B : Block V) (sc : Nat),
    (Model.spec (V := V)).goldfish_score E T votes votes s B ⇢ sc →
    ∀ R : Finset V, (Model.spec (V := V)).raw_supporters T votes votes s B ⇢ R → sc = R.card
    := by
  rw [ForkChoiceImages.spec_no_second_vote_in_eq, ForkChoiceImages.spec_goldfish_score_eq,
    ForkChoiceImages.spec_raw_supporters_eq]
  exact (Model.vocabulary_facts_forkChoice (V := V)).Numerator_score_eq_supporters

/-! ## The filtered tree of a store -/

/-- The field `get_filtered_block_tree_from_subset` of `ForkChoiceFacts` at `Model.spec`: the
    filtered tree of `st` over `blocks` is a subset of `blocks`. -/
theorem spec_get_filtered_block_tree_from_subset :
    ∀ (st : (Model.spec (V := V)).FGS) (blocks : Finset (Block V)),
    (Model.spec (V := V)).get_filtered_block_tree_from st blocks ⊆ blocks
    := by
  intro st blocks B hB
  exact (Model.vocabulary_facts_forkChoice (V := V)).get_filtered_block_tree_from_subset
    st.val.toProof.toHealing.toFG blocks (ForkChoiceImages.filtered_from_subset_vocabulary st.val blocks hB)

/-- The field `mem_get_filtered_block_tree_from_parts` of `ForkChoiceFacts` at `Model.spec`: a
    block `B` of the filtered tree of `st` over `blocks` is in `blocks`, descends from `st`'s
    finalized block and FG root, and has a descendant in `blocks` of chain-state height at least
    `st.h_max − 1`. -/
theorem spec_mem_get_filtered_block_tree_from_parts :
    ∀ {st : (Model.spec (V := V)).FGS} {blocks : Finset (Block V)}
    {B : Block V}, B ∈ (Model.spec (V := V)).get_filtered_block_tree_from st blocks →
    B ∈ blocks ∧ Block.Preceq st.F B ∧ (∃ W ∈ blocks, Block.Preceq B W ∧ st.h_max - 1 ≤ (st.σ W).h) ∧
      Block.Preceq ((Model.spec (V := V)).get_fg_root st) B
    := by
  intro st blocks B hB
  have h := (Model.vocabulary_facts_forkChoice (V := V)).mem_get_filtered_block_tree_from_parts
    (st := st.val.toProof.toHealing.toFG) (ForkChoiceImages.filtered_from_subset_vocabulary st.val blocks hB)
  sd_normalize
  exact h

/-- The field `parts_of_mem_get_filtered_block_tree_from` of `ForkChoiceFacts` at `Model.spec`:
    a block `C` of the filtered tree of `st` over `blocks` is in `blocks`, descends from `st`'s
    finalized block and FG root, and has a descendant in `blocks` of chain-state height at least
    `st.h_max − 1`. -/
theorem spec_parts_of_mem_get_filtered_block_tree_from :
    ∀ {st : (Model.spec (V := V)).FGS} {blocks : Finset (Block V)}
    {C : Block V}, C ∈ (Model.spec (V := V)).get_filtered_block_tree_from st blocks →
    ((C ∈ blocks ∧ Block.Preceq st.F C) ∧ ∃ W ∈ blocks, Block.Preceq C W ∧ st.h_max - 1 ≤ (st.σ W).h) ∧
      Block.Preceq ((Model.spec (V := V)).get_fg_root st) C
    := by
  intro st blocks C hC
  have h := (Model.vocabulary_facts_forkChoice (V := V)).parts_of_mem_get_filtered_block_tree_from
    (st := st.val.toProof.toHealing.toFG) (ForkChoiceImages.filtered_from_subset_vocabulary st.val blocks hC)
  sd_normalize
  exact h

/-- The field `finalized_preceq_of_mem_get_filtered_block_tree` of `ForkChoiceFacts` at
    `Model.spec`: `st`'s finalized block is an ancestor of every block of its filtered tree, or
    that block itself. -/
theorem spec_finalized_preceq_of_mem_get_filtered_block_tree :
    ∀ {st : (Model.spec (V := V)).FGS} {B : Block V} (hB : B ∈ (Model.spec (V := V)).get_filtered_block_tree st), Block.Preceq st.F B
    := by
  intro st B hB
  have h := (Model.vocabulary_facts_forkChoice (V := V)).finalized_preceq_of_mem_get_filtered_block_tree
    (st := st.val.toProof.toHealing.toFG) (ForkChoiceImages.filtered_subset_vocabulary st hB)
  sd_normalize
  exact h

/-- The field `q10_filtered_F` of `ForkChoiceFacts` at `Model.spec`: `st`'s finalized block is
    an ancestor of every block of its filtered tree, or that block itself. -/
theorem spec_q10_filtered_F :
    ∀ {st : (Model.spec (V := V)).FGS} {B : Block V} (h : B ∈ (Model.spec (V := V)).get_filtered_block_tree st), Block.Preceq st.F B
    := by
  intro st B hB
  have h := (Model.vocabulary_facts_forkChoice (V := V)).q10_filtered_F
    (st := st.val.toProof.toHealing.toFG) (ForkChoiceImages.filtered_subset_vocabulary st hB)
  sd_normalize
  exact h

/-- The field `get_filtered_block_tree_subset` of `ForkChoiceFacts` at `Model.spec`: the
    filtered tree of `st` is a subset of `st`'s block tree. -/
theorem spec_get_filtered_block_tree_subset :
    ∀ (st : (Model.spec (V := V)).FGS), (Model.spec (V := V)).get_filtered_block_tree st ⊆ st.toSG.toGoldfishStore.T
    := by
  intro st B hB
  have h := (Model.vocabulary_facts_forkChoice (V := V)).get_filtered_block_tree_subset
    st.val.toProof.toHealing.toFG (ForkChoiceImages.filtered_subset_vocabulary st hB)
  sd_normalize
  exact h

/-- The field `preceq_get_fg_root_of_mem_filtered` of `ForkChoiceFacts` at `Model.spec`: `st`'s
    FG root is an ancestor of every block of its filtered tree, or that block itself. -/
theorem spec_preceq_get_fg_root_of_mem_filtered :
    ∀ {st : (Model.spec (V := V)).FGS} {B : Block V} (hB : B ∈ (Model.spec (V := V)).get_filtered_block_tree st), Block.preceq ((Model.spec (V := V)).get_fg_root st) B = true
    := by
  intro st B hB
  have h := (Model.vocabulary_facts_forkChoice (V := V)).preceq_get_fg_root_of_mem_filtered
    (st := st.val.toProof.toHealing.toFG) (ForkChoiceImages.filtered_subset_vocabulary st hB)
  sd_normalize
  exact h

/-- The field `parts_of_mem_get_filtered_block_tree` of `ForkChoiceFacts` at `Model.spec`: a
    block `C` of `st`'s filtered tree is in `st`'s tree, descends from `st`'s finalized block and FG
    root, and has a descendant in the tree of chain-state height at least `st.h_max − 1`. -/
theorem spec_parts_of_mem_get_filtered_block_tree :
    ∀ {st : (Model.spec (V := V)).FGS} {C : Block V} (h : C ∈ (Model.spec (V := V)).get_filtered_block_tree st), ((C ∈ st.toSG.toGoldfishStore.T ∧ Block.Preceq st.F C) ∧
    ∃ W, W ∈ st.toSG.toGoldfishStore.T ∧ Block.Preceq C W ∧ st.h_max - 1 ≤ (st.σ W).h) ∧
    Block.Preceq ((Model.spec (V := V)).get_fg_root st) C
    := by
  intro st C hC
  have h := (Model.vocabulary_facts_forkChoice (V := V)).parts_of_mem_get_filtered_block_tree
    (st := st.val.toProof.toHealing.toFG) (ForkChoiceImages.filtered_subset_vocabulary st hC)
  sd_normalize
  exact h

/-- The field `viable_witness_of_mem_get_filtered_block_tree` of `ForkChoiceFacts` at
    `Model.spec`: a block `B` of `st`'s filtered tree has a descendant `W` in `st`'s tree, or
    is one, with chain-state height at least `st.h_max − 1`. -/
theorem spec_viable_witness_of_mem_get_filtered_block_tree :
    ∀ {st : (Model.spec (V := V)).FGS} {B : Block V} (hB : B ∈ (Model.spec (V := V)).get_filtered_block_tree st), ∃ W ∈ st.toSG.toGoldfishStore.T, Block.Preceq B W ∧ st.h_max - 1 ≤ (st.σ W).h
    := by
  intro st B hB
  have h := (Model.vocabulary_facts_forkChoice (V := V)).viable_witness_of_mem_get_filtered_block_tree
    (st := st.val.toProof.toHealing.toFG) (ForkChoiceImages.filtered_subset_vocabulary st hB)
  sd_normalize
  exact h

/-- The field `mem_filtered_of_preceq` of `ForkChoiceFacts` at `Model.spec`: if `st.F ⪯ st.J`,
    `P` is in `st`'s filtered tree, and `R` is a block of `st`'s tree with `R ⪯ P` and FG root
    `⪯ R`, then `R` is in the filtered tree. -/
theorem spec_mem_filtered_of_preceq :
    ∀ {st : (Model.spec (V := V)).FGS} {P R : Block V} (hFJ : Block.preceq st.F st.J = true) (hP : P ∈ (Model.spec (V := V)).get_filtered_block_tree st) (hRT : R ∈ st.toSG.toGoldfishStore.T) (hRP : Block.preceq R P = true) (hroot : Block.preceq ((Model.spec (V := V)).get_fg_root st) R = true), R ∈ (Model.spec (V := V)).get_filtered_block_tree st
    := by
  intro st P R hFJ hP hRT hRP hroot
  have hP' := ForkChoiceImages.filtered_subset_vocabulary st hP
  have h := (Model.vocabulary_facts_forkChoice (V := V)).mem_filtered_of_preceq
    (st := st.val.toProof.toHealing.toFG) (by sd_normalize; exact hFJ) hP' (by sd_normalize; exact hRT)
    hRP (by sd_normalize; exact hroot)
  show R ∈ Member.get_filtered_block_tree st.val
  rw [ForkChoiceImages.filtered_eq_vocabulary st]
  exact h


/-! ### The views -/

/-- The field `mem_voter_view_of_carried` of `ForkChoiceFacts` at `Model.spec`: a
    slot-`(s − 1)` Goldfish vote included in a slot-`s` block of `gs`'s tree is in every outcome of
    the slot-`s` voter view of `gs`. -/
theorem spec_mem_voter_view_of_carried :
    ∀ (E : Env V) (gs : (Model.spec (V := V)).GS) (s : Slot) {u : GoldfishVote V} {X : Block V} (hX : X ∈ gs.T) (hXs : X.slot = s) (hu : u ∈ X.gf_votes) (hus : u.slot = s - 1) (Y : Finset (GoldfishVote V)) (hY : (Model.spec (V := V)).voter_view E gs s ⇢ Y), u ∈ Y
    := by
  intro E gs s u X hX hXs hu hus Y hY
  rw [ForkChoiceImages.spec_voter_view_eq] at hY
  exact (Model.vocabulary_facts_forkChoice (V := V)).mem_voter_view_of_carried E _ s hX hXs hu hus Y hY

/-- The field `carried_raw_subset_voter_view` of `ForkChoiceFacts` at `Model.spec`: if `B` is a
    slot-`s` block of `st`'s tree whose Goldfish votes are all of slot `B.slot − 1`, then those
    votes are in every outcome of the slot-`s` voter view of `st`. -/
theorem spec_carried_raw_subset_voter_view :
    ∀ (E : Env V) (st : (Model.spec (V := V)).GS) {s : Slot} {B : Block V} (hB : B ∈ st.T) (hBslot : B.slot = s) (hslots : ∀ u ∈ B.gf_votes, u.slot + 1 = B.slot) (Y : Finset (GoldfishVote V)) (hY : (Model.spec (V := V)).voter_view E st s ⇢ Y), B.gf_votes.toFinset ⊆ Y
    := by
  intro E st s B hB hBslot hslots Y hY
  rw [ForkChoiceImages.spec_voter_view_eq] at hY
  exact (Model.vocabulary_facts_forkChoice (V := V)).carried_raw_subset_voter_view E _ hB hBslot hslots Y hY

/-- The field `mem_voter_view_of_pool` of `ForkChoiceFacts` at `Model.spec`: a slot-`s`
    Goldfish vote of `gs`'s pool stamped before slot `s`'s view freeze is in every outcome of the
    slot-`(s + 1)` voter view of `gs`. -/
theorem spec_mem_voter_view_of_pool :
    ∀ (E : Env V) (gs : (Model.spec (V := V)).GS) (s : Slot) {u : GoldfishVote V},
    u ∈ gs.pool s → ∀ {τ : Stamp}, gs.timestamp_vote u = some τ →
    τ < (((Model.spec (V := V)).view_freeze E s : Int) : Stamp) →
    ∀ Y : Finset (GoldfishVote V), (Model.spec (V := V)).voter_view E gs (s + 1) ⇢ Y → u ∈ Y
    := by
  intro E gs s u hu τ hτ hlt Y hY
  rw [ForkChoiceImages.spec_voter_view_eq] at hY
  rw [ForkChoiceImages.spec_view_freeze_eq] at hlt
  change u ∈ (Model.spec (V := V)).gs_pool gs s at hu
  rw [ForkChoiceImages.spec_gs_pool_eq] at hu
  exact (Model.vocabulary_facts_forkChoice (V := V)).mem_voter_view_of_pool E _ s hu hτ hlt Y hY

/-- The field `voter_view_cases` of `ForkChoiceFacts` at `Model.spec`: a vote in an outcome of
    the slot-`s` voter view of `gs` is in `gs_pool gs (s − 1)` with a stamp strictly before slot
    `s − 1`'s view freeze, or is a slot-`(s − 1)` Goldfish vote included in a slot-`s` block of
    `gs`'s tree. -/
theorem spec_voter_view_cases :
    ∀ (E : Env V) (gs : (Model.spec (V := V)).GS) (s : Slot) {u : GoldfishVote V} (Y : Finset (GoldfishVote V)) (hY : (Model.spec (V := V)).voter_view E gs s ⇢ Y) (h : u ∈ Y), (u ∈ ((Model.spec (V := V)).gs_pool gs (s - 1)) ∧ ∃ τ : Stamp, gs.timestamp_vote u = some τ ∧
    τ < (((Model.spec (V := V)).view_freeze E (s - 1) : Int) : Stamp)) ∨
    ∃ X ∈ gs.T, X.slot = s ∧ u ∈ X.gf_votes ∧ u.slot = s - 1
    := by
  intro E gs s u Y hY h
  rw [ForkChoiceImages.spec_voter_view_eq] at hY
  rw [ForkChoiceImages.spec_view_freeze_eq, ForkChoiceImages.spec_gs_pool_eq]
  exact (Model.vocabulary_facts_forkChoice (V := V)).voter_view_cases E _ s Y hY h

/-- The field `voter_view_cases_beforeCutoff` of `ForkChoiceFacts` at `Model.spec`: a vote in
    an outcome of the slot-`s` voter view of `gs` is among the votes of `gs_pool gs (s − 1)` stamped
    before slot `s − 1`'s view freeze, or is a slot-`(s − 1)` Goldfish vote included in a slot-`s`
    block of `gs`'s tree. -/
theorem spec_voter_view_cases_beforeCutoff :
    ∀ (E : Env V) (gs : (Model.spec (V := V)).GS) (s : Slot) {u : GoldfishVote V} (Y : Finset (GoldfishVote V)) (hY : (Model.spec (V := V)).voter_view E gs s ⇢ Y) (h : u ∈ Y), u ∈ beforeCutoff gs.timestamp_vote ((Model.spec (V := V)).view_freeze E (s - 1)) (((Model.spec (V := V)).gs_pool gs (s - 1))) ∨
    ∃ X ∈ gs.T, X.slot = s ∧ u ∈ X.gf_votes ∧ u.slot = s - 1
    := by
  intro E gs s u Y hY h
  rw [ForkChoiceImages.spec_voter_view_eq] at hY
  rw [ForkChoiceImages.spec_view_freeze_eq, ForkChoiceImages.spec_gs_pool_eq]
  exact (Model.vocabulary_facts_forkChoice (V := V)).voter_view_cases_beforeCutoff E _ s Y hY h

/-- The field `voter_view_set_clock_slot` of `ForkChoiceFacts` at `Model.spec`: setting the
    store's time and slot does not change the outcomes of its slot-`k` voter view. -/
theorem spec_voter_view_set_clock_slot :
    ∀ (E : Env V) (st : (Model.spec (V := V)).S) (t : Int) (s k : Slot) (Y : Finset (GoldfishVote V)),
    (Model.spec (V := V)).voter_view E ((Model.spec (V := V)).store_with_t_s st t s).toHealing.toFG.toSG.toGoldfishStore k ⇢ Y ↔
      (Model.spec (V := V)).voter_view E st.toHealing.toFG.toSG.toGoldfishStore k ⇢ Y
    := by
  intro E st t s k Y
  rfl


/-- The field `mem_T_of_mem_voter_processed_block_tree` of `ForkChoiceFacts` at `Model.spec`:
    every block of an outcome of the voter's processed tree of `gs` is in `gs`'s tree. -/
theorem spec_mem_T_of_mem_voter_processed_block_tree :
    ∀ (E : Env V) (gs : (Model.spec (V := V)).GS) (s : Slot) {B : Block V} (P : Finset (Block V)) (hP : (Model.spec (V := V)).voter_processed_block_tree E gs s ⇢ P) (h : B ∈ P), B ∈ gs.T
    := by
  intro E gs s B P hP h
  rw [ForkChoiceImages.spec_voter_processed_block_tree_eq] at hP
  exact (Model.vocabulary_facts_forkChoice (V := V)).mem_T_of_mem_voter_processed_block_tree E _ s P hP h

/-- The field `mem_voter_processed_block_tree_of_proposal` of `ForkChoiceFacts` at
    `Model.spec`: an ancestor `B` in `gs`'s tree of a slot-`s` block `P` of `gs`'s tree is in
    every outcome of the voter's processed tree of `gs` at slot `s`. -/
theorem spec_mem_voter_processed_block_tree_of_proposal :
    ∀ (E : Env V) (gs : (Model.spec (V := V)).GS) (s : Slot) {B P : Block V} (hT : B ∈ gs.T) (hP : P ∈ gs.T) (hPs : P.slot = s) (hBP : Block.Preceq B P) (Q : Finset (Block V)) (hQ : (Model.spec (V := V)).voter_processed_block_tree E gs s ⇢ Q), B ∈ Q
    := by
  intro E gs s B P hT hP hPs hBP Q hQ
  rw [ForkChoiceImages.spec_voter_processed_block_tree_eq] at hQ
  exact (Model.vocabulary_facts_forkChoice (V := V)).mem_voter_processed_block_tree_of_proposal E _ s hT hP hPs hBP Q hQ

/-- The field `mem_voter_processed_block_tree_of_slot` of `ForkChoiceFacts` at `Model.spec`: a
    slot-`s` block of `gs`'s tree is in every outcome of the voter's processed tree of `gs` at slot
    `s`. -/
theorem spec_mem_voter_processed_block_tree_of_slot :
    ∀ (E : Env V) (gs : (Model.spec (V := V)).GS) (s : Slot) {B : Block V} (hB : B ∈ gs.T) (hs : B.slot = s) (Q : Finset (Block V)) (hQ : (Model.spec (V := V)).voter_processed_block_tree E gs s ⇢ Q), B ∈ Q
    := by
  intro E gs s B hB hs Q hQ
  rw [ForkChoiceImages.spec_voter_processed_block_tree_eq] at hQ
  exact (Model.vocabulary_facts_forkChoice (V := V)).mem_voter_processed_block_tree_of_slot E _ s hB hs Q hQ

/-- The field `mem_voter_processed_block_tree_of_stamped` of `ForkChoiceFacts` at `Model.spec`:
    a block of `gs`'s tree stamped before slot `s − 1`'s view freeze is in every outcome of the
    voter's processed tree of `gs` at slot `s`. -/
theorem spec_mem_voter_processed_block_tree_of_stamped :
    ∀ (E : Env V) (gs : (Model.spec (V := V)).GS) (s : Slot) {B : Block V} (hT : B ∈ gs.T) (hst : stampedBefore gs.timestamp_block ((Model.spec (V := V)).view_freeze E (s - 1)) B = true) (Q : Finset (Block V)) (hQ : (Model.spec (V := V)).voter_processed_block_tree E gs s ⇢ Q), B ∈ Q
    := by
  intro E gs s B hT hst Q hQ
  rw [ForkChoiceImages.spec_voter_processed_block_tree_eq] at hQ
  rw [ForkChoiceImages.spec_view_freeze_eq] at hst
  exact (Model.vocabulary_facts_forkChoice (V := V)).mem_voter_processed_block_tree_of_stamped E _ s hT hst Q hQ

/-- The field `voter_processed_block_tree_cases` of `ForkChoiceFacts` at `Model.spec`: a block
    `B` of an outcome of the voter's processed tree of `gs` at slot `s` is in `gs`'s tree, and was
    stamped before slot `s − 1`'s view freeze or is an ancestor of a slot-`s` block of the tree, or
    that block itself. -/
theorem spec_voter_processed_block_tree_cases :
    ∀ (E : Env V) (gs : (Model.spec (V := V)).GS) (s : Slot) {B : Block V} (Q : Finset (Block V)) (hQ : (Model.spec (V := V)).voter_processed_block_tree E gs s ⇢ Q) (h : B ∈ Q), B ∈ gs.T ∧
    (stampedBefore gs.timestamp_block ((Model.spec (V := V)).view_freeze E (s - 1)) B = true ∨
    ∃ P ∈ gs.T, P.slot = s ∧ Block.Preceq B P)
    := by
  intro E gs s B Q hQ h
  rw [ForkChoiceImages.spec_voter_processed_block_tree_eq] at hQ
  rw [ForkChoiceImages.spec_view_freeze_eq]
  exact (Model.vocabulary_facts_forkChoice (V := V)).voter_processed_block_tree_cases E _ s Q hQ h

/-- The field `mem_proposer_support_view_iff` of `ForkChoiceFacts` at `Model.spec`: a vote `u`
    is in an outcome of the slot-`s` proposer support view of `gs` exactly when it is among `gs`'s
    slot-`(s − 1)` Goldfish votes and its resolution test `resolved gs.T u` returns `true`. -/
theorem spec_mem_proposer_support_view_iff :
    ∀ (gs : (Model.spec (V := V)).GS) (s : Slot) (u : GoldfishVote V) (L : List (GoldfishVote V)) (hL : (Model.spec (V := V)).proposer_support_view gs s ⇢ L) (b : Bool) (hb : (Model.spec (V := V)).resolved gs.T u ⇢ b), u ∈ L ↔
    u ∈ gs.gf_votes (s - 1) ∧ b = true
    := by
  intro gs s u L hL b hb
  rw [ForkChoiceImages.spec_proposer_support_view_eq] at hL
  rw [ForkChoiceImages.spec_resolved_eq] at hb
  exact (Model.vocabulary_facts_forkChoice (V := V)).mem_proposer_support_view_iff _ s u L hL b hb

/-- The field `voter_support_view_subset` of `ForkChoiceFacts` at `Model.spec`: if every
    block's support votes are among its Goldfish votes, every outcome of the slot-`s` support voter
    view of `st` is a subset of every outcome of its slot-`s` voter view. -/
theorem spec_voter_support_view_subset :
    ∀ (E : Env V) (st : (Model.spec (V := V)).GS) (s : Slot) (hsub : ∀ B ∈ st.T, ∀ u ∈ B.gf_support_votes, u ∈ B.gf_votes) (Y : Finset (GoldfishVote V)) (hY : (Model.spec (V := V)).voter_support_view E st s ⇢ Y) (Z : Finset (GoldfishVote V)) (hZ : (Model.spec (V := V)).voter_view E st s ⇢ Z), Y ⊆ Z
    := by
  intro E st s hsub Y hY Z hZ
  rw [ForkChoiceImages.spec_voter_support_view_eq] at hY
  rw [ForkChoiceImages.spec_voter_view_eq] at hZ
  exact (Model.vocabulary_facts_forkChoice (V := V)).voter_support_view_subset E _ s hsub Y hY Z hZ

/-- The field `mem_voter_support_view_of_carried` of `ForkChoiceFacts` at `Model.spec`: a
    slot-`(s − 1)` support vote of a slot-`s` block of `gs`'s tree whose resolution test returns
    `true` is in every outcome of the slot-`s` support voter view of `gs`. -/
theorem spec_mem_voter_support_view_of_carried :
    ∀ (E : Env V) (gs : (Model.spec (V := V)).GS) (s : Slot) {u : GoldfishVote V} {X : Block V} (hX : X ∈ gs.T) (hXs : X.slot = s) (hu : u ∈ X.gf_support_votes) (b : Bool) (hb : (Model.spec (V := V)).resolved gs.T u ⇢ b) (hres : b = true) (hus : u.slot = s - 1) (Y : Finset (GoldfishVote V)) (hY : (Model.spec (V := V)).voter_support_view E gs s ⇢ Y), u ∈ Y
    := by
  intro E gs s u X hX hXs hu b hb hres hus Y hY
  rw [ForkChoiceImages.spec_voter_support_view_eq] at hY
  rw [ForkChoiceImages.spec_resolved_eq] at hb
  exact (Model.vocabulary_facts_forkChoice (V := V)).mem_voter_support_view_of_carried E _ s hX hXs hu b hb hres hus Y hY

/-- The field `voter_support_view_cases` of `ForkChoiceFacts` at `Model.spec`: a vote in an
    outcome of the slot-`s` support voter view of `gs` is either in `gs_pool gs (s − 1)`, with its
    head resolving in `gs`'s tree to a block of slot at most the vote's and both stamps strictly
    before slot `s − 1`'s view freeze, or a slot-`(s − 1)` support vote of a slot-`s` block of the
    tree whose resolution test returns `true`. -/
theorem spec_voter_support_view_cases :
    ∀ (E : Env V) (gs : (Model.spec (V := V)).GS) (s : Slot) {u : GoldfishVote V} (Y : Finset (GoldfishVote V)) (hY : (Model.spec (V := V)).voter_support_view E gs s ⇢ Y) (h : u ∈ Y) (b : Bool) (hb : (Model.spec (V := V)).resolved gs.T u ⇢ b), (u ∈ ((Model.spec (V := V)).gs_pool gs (s - 1)) ∧ ∃ X : Block V, Block.find? gs.T u.head = some X ∧
    X.slot ≤ u.slot ∧ ∃ τ σ : Stamp, gs.timestamp_vote u = some τ ∧
    gs.timestamp_block X = some σ ∧
    τ < (((Model.spec (V := V)).view_freeze E (s - 1) : Int) : Stamp) ∧
    σ < (((Model.spec (V := V)).view_freeze E (s - 1) : Int) : Stamp)) ∨
    ∃ X ∈ gs.T, X.slot = s ∧ u ∈ X.gf_support_votes ∧
    b = true ∧ u.slot = s - 1
    := by
  intro E gs s u Y hY h b hb
  rw [ForkChoiceImages.spec_voter_support_view_eq] at hY
  rw [ForkChoiceImages.spec_resolved_eq] at hb
  rw [ForkChoiceImages.spec_view_freeze_eq, ForkChoiceImages.spec_gs_pool_eq]
  exact (Model.vocabulary_facts_forkChoice (V := V)).voter_support_view_cases E _ s Y hY h b hb

/-- The field `Optimistic_mem_voter_support_view_of_pool` of `ForkChoiceFacts` at `Model.spec`:
    for every outcome `τ` of `gs_tau gst`, a vote of `gst`'s slot-`(s − 1)` pool stamped by `τ`
    before slot `s − 1`'s view freeze is in every outcome of the slot-`s` support voter view of
    `gst`. -/
theorem spec_Optimistic_mem_voter_support_view_of_pool :
    ∀ (E : Env V) (gst : (Model.spec (V := V)).GS) (s : Slot)
    {u : GoldfishVote V} (τ : TimestampMap (GoldfishVote V)), (Model.spec (V := V)).gs_tau gst ⇢ τ →
    u ∈ beforeCutoff τ ((Model.spec (V := V)).view_freeze E (s - 1)) ((Model.spec (V := V)).gs_pool gst (s - 1)) →
    ∀ Y : Finset (GoldfishVote V), (Model.spec (V := V)).voter_support_view E gst s ⇢ Y → u ∈ Y
    := by
  intro E gst s u τ hτ hu Y hY
  rw [ForkChoiceImages.spec_voter_support_view_eq] at hY
  obtain ⟨f, hf, -, hfx⟩ := hτ
  cases Except.ok.inj hfx
  rw [ForkChoiceImages.spec_view_freeze_eq, ForkChoiceImages.spec_gs_pool_eq] at hu
  refine (Model.vocabulary_facts_forkChoice (V := V)).Optimistic_mem_voter_support_view_of_pool E _ s
    (DecoupledConsensusModel.Protocol.GoldfishStore.tau
      gst.val.toProof.toHealing.toFG.toSG.toGoldfishStore) rfl ?_ Y hY
  unfold beforeCutoff at hu ⊢
  rw [Finset.mem_filter] at hu ⊢
  refine ⟨hu.1, ?_⟩
  have hpool := hu.1
  rw [← ForkChoiceImages.spec_gs_pool_eq] at hpool
  change u ∈ (gst.val.pool (s - 1)).map Spec.GoldfishVote.toProofEmb at hpool
  obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hpool
  obtain ⟨hst, hT, -, -⟩ := gst.property
  have hstw : (gst.val.timestamp_vote (Spec.GoldfishVote.toSpec w.toProof)).isSome := by
    rw [Spec.GoldfishVote.toSpec_toProof]
    exact Option.isSome_iff_ne_none.mpr (NoRaise.stamped_pool hst hw)
  have hfw := hf _ hstw
  rw [Spec.GoldfishVote.toSpec_toProof] at hfw
  have heq := ForkChoiceImages.tau_toProof_of_ok gst w hfw
  have h2 := hu.2
  unfold DecoupledConsensusModel.stampedBefore at h2 ⊢
  simp only [Spec.GoldfishVote.coe_toProofEmb] at h2 ⊢
  rw [← heq]
  exact h2

/-- The field `voter_candidate_tree_eq_protocol_voter_filtered_block_tree` of `ForkChoiceFacts` at
    `Model.spec`: for every outcome `P` of the voter's processed tree at `st`'s slot, the
    filtered tree of `st`'s FG view over `P` is every outcome of
    `voter_filtered_block_tree E st st.s`. -/
theorem spec_voter_candidate_tree_eq_protocol_voter_filtered_block_tree :
    ∀ (E : Env V) (st : (Model.spec (V := V)).S)
    (P : Finset (Block V)),
    (Model.spec (V := V)).voter_processed_block_tree E ((Model.spec (V := V)).toHealing st).toFG.toSG.toGoldfishStore ((Model.spec (V := V)).toHealing st).s ⇢ P →
    ∀ X : Finset (Block V), (Model.spec (V := V)).voter_filtered_block_tree E st st.s ⇢ X →
    (Model.spec (V := V)).get_filtered_block_tree_from ((Model.spec (V := V)).toHealing st).toFG P = X
    := by
  intro E st P hP X hX
  have hP' := (returns_successOutcomes _ _).mp hP
  have hX' := (returns_successOutcomes _ _).mp hX
  have hs : ((Model.spec (V := V)).toHealing st).s = st.s := by
    simp only [Model.HS.s, Model.S.s, Model.GS.s, Model.spec,
      Member.gs_s, Member.store_s, Member.toHealing, Member.toFG, Member.toSG,
      Member.toGoldfishStore, Model.HS.toFG, Model.FGS.toSG, Model.SGS.toGoldfishStore, id_eq,
      toProof_gs_s, Spec.Store.toProof_s]
  rw [hs] at hP'
  change Except.map _ (Spec.Protocol.voter_processed_block_tree
    (Spec.Config.toSpec E unreadHealConfig unreadHeightConfig) st.val st.s) = .ok P at hP'
  rw [ForkChoiceImages.voter_filtered_block_tree_ofImage] at hX'
  cases hq : Spec.Protocol.voter_processed_block_tree
      (Spec.Config.toSpec E unreadHealConfig unreadHeightConfig) st.val st.s with
  | error e => rw [hq] at hP'; cases hP'
  | ok Q =>
    rw [hq] at hP' hX'
    have hPQ : P = Q.image Spec.Block.toProof := (Except.ok.inj hP').symm
    have hXQ : X = (Spec.Protocol.get_filtered_block_tree_from
        (Spec.Store.ofImage st.val) Q).image Spec.Block.toProof :=
      (Except.ok.inj hX').symm
    change Member.get_filtered_block_tree_from st.val P = X
    rw [hPQ, hXQ]
    unfold Member.get_filtered_block_tree_from
    rw [ForkChoiceImages.image_map_blockOfImage_of_subset st
      (ForkChoiceImages.processed_subset_of_ok _ _ _ hq)]

/-- The field `voter_filtered_block_tree_subset_filtered` of `ForkChoiceFacts` at `Model.spec`:
    every outcome of `voter_filtered_block_tree E st st.s` is a subset of the filtered tree of
    `st`'s healing view. -/
theorem spec_voter_filtered_block_tree_subset_filtered :
    ∀ (E : Env V) (st : (Model.spec (V := V)).S) (X : Finset (Block V)),
    (Model.spec (V := V)).voter_filtered_block_tree E st st.s ⇢ X → X ⊆ (Model.spec (V := V)).get_filtered_block_tree ((Model.spec (V := V)).toHealing st).toFG
    := by
  intro E st X hX
  have hX' := (returns_successOutcomes _ _).mp hX
  rw [ForkChoiceImages.voter_filtered_block_tree_ofImage] at hX'
  cases hq : Spec.Protocol.voter_processed_block_tree
      (Spec.Config.toSpec E unreadHealConfig unreadHeightConfig) st.val st.s with
  | error e => rw [hq] at hX'; cases hX'
  | ok Q =>
    rw [hq] at hX'
    have hXQ : X = (Spec.Protocol.get_filtered_block_tree_from
        (Spec.Store.ofImage st.val) Q).image Spec.Block.toProof :=
      (Except.ok.inj hX').symm
    change X ⊆ Member.get_filtered_block_tree st.val
    rw [hXQ]
    exact Finset.image_subset_image (ForkChoiceImages.draft_filtered_from_mono
      (Spec.Store.ofImage st.val)
      (ForkChoiceImages.processed_subset_of_ok _ _ _ hq))

/-! ## Membership in the filtered tree, and the fork choice as a walk -/


/-- The field `mem_get_filtered_block_tree_of_parts` of `ForkChoiceFacts` at `Model.spec`: a
    block of the store's tree that descends from the finalized block and from the FG root, and has a
    descendant in the tree of chain-state height at least `h_max − 1`, is in the store's filtered
    tree. -/
theorem spec_mem_get_filtered_block_tree_of_parts : ∀ (st : (Model.spec (V := V)).HS) {C W : Block V} (hC : C ∈ st.toFG.toSG.toGoldfishStore.T) (hF : Block.Preceq st.toFG.F C) (hW : W ∈ st.toFG.toSG.toGoldfishStore.T) (hCW : Block.Preceq C W) (hh : st.toFG.h_max - 1 ≤ (st.toFG.σ W).h) (hroot : Block.Preceq ((Model.spec (V := V)).get_fg_root st.toFG) C), C ∈ (Model.spec (V := V)).get_filtered_block_tree st.toFG := by
  intro st C W hC hF hW hCW hh hroot
  have h := (Model.vocabulary_facts_forkChoice (V := V)).mem_get_filtered_block_tree_of_parts
    (st := st.val.toProof.toHealing) (by sd_normalize; exact hC) (by sd_normalize; exact hF)
    (by sd_normalize; exact hW) hCW (by sd_normalize; exact hh) (by sd_normalize; exact hroot)
  show C ∈ Member.get_filtered_block_tree st.val
  rw [ForkChoiceImages.filtered_eq_vocabulary st]
  exact h

/-- The field `canonicalConeSegment_mem_filtered_of_root_preceq` of `ForkChoiceFacts` at
    `Model.spec`: a block between a descendant of the FG root and a tree block of chain-state
    height at least `h_max − 1` is in the store's filtered tree. -/
theorem spec_canonicalConeSegment_mem_filtered_of_root_preceq : ∀ {st : (Model.spec (V := V)).S} (hpc : Block.genesis ∈ ((Model.spec (V := V)).toHealing st).toFG.toSG.toGoldfishStore.T ∧ ∀ B ∈ ((Model.spec (V := V)).toHealing st).toFG.toSG.toGoldfishStore.T, B.parent? = none ∨ B.parent ∈ ((Model.spec (V := V)).toHealing st).toFG.toSG.toGoldfishStore.T) (hFJ : Block.Preceq st.F st.J) {P W D : Block V} (hrootP : Block.Preceq ((Model.spec (V := V)).get_fg_root ((Model.spec (V := V)).toHealing st).toFG) P) (hWT : W ∈ st.T) (hheight : st.h_max - 1 ≤ (st.σ W).h) (hPD : Block.Preceq P D) (hDW : Block.Preceq D W), D ∈ (Model.spec (V := V)).get_filtered_block_tree ((Model.spec (V := V)).toHealing st).toFG := by
  intro st hpc hFJ P W D hrootP hWT hheight hPD hDW
  have h := (Model.vocabulary_facts_forkChoice (V := V)).canonicalConeSegment_mem_filtered_of_root_preceq
    (st := st.val.toProof) (by sd_normalize; exact hpc) (by sd_normalize; exact hFJ)
    (by sd_normalize; exact hrootP) (by sd_normalize; exact hWT) (by sd_normalize; exact hheight)
    hPD hDW
  show D ∈ Member.get_filtered_block_tree st.val
  rw [ForkChoiceImages.filtered_eq_vocabulary st]
  exact h

/-- The field `mem_get_filtered_block_tree_from_of_parts_explicit` of `ForkChoiceFacts` at
    `Model.spec`: a block of `blocks` that descends from the finalized block and from the FG
    root, and has a descendant in `blocks` of chain-state height at least `h_max − 1`, is in the
    filtered tree over `blocks`. -/
theorem spec_mem_get_filtered_block_tree_from_of_parts_explicit : ∀ (st : (Model.spec (V := V)).FGS) {blocks : Finset (Block V)}
    {C W : Block V}, C ∈ blocks → Block.Preceq st.F C → W ∈ blocks → Block.Preceq C W →
    st.h_max - 1 ≤ (st.σ W).h → Block.Preceq ((Model.spec (V := V)).get_fg_root st) C →
    C ∈ (Model.spec (V := V)).get_filtered_block_tree_from st blocks := by
  intro st blocks C W hC hF hW hCW hh hroot
  have h := (Model.vocabulary_facts_forkChoice (V := V)).mem_get_filtered_block_tree_from_of_parts_explicit
    st.val.toProof.toHealing.toFG hC (by sd_normalize; exact hF) hW hCW
    (by sd_normalize; exact hh) (by sd_normalize; exact hroot)
  show C ∈ Member.get_filtered_block_tree_from st.val blocks
  rw [ForkChoiceImages.filtered_from_eq_vocabulary st]
  exact h

/-- The field `goldfish_fork_choice_eq_ghost` of `ForkChoiceFacts` at `Model.spec`: for
    outcomes `score` and `elig` of the Goldfish score and test at every block, the Goldfish fork
    choice from `A` through `tree` returns `X` exactly when the walk scored by `score` and admitting
    by `elig` returns `X`. -/
theorem spec_goldfish_fork_choice_eq_ghost : ∀ (E : Env V) (σ : Block V → (Model.spec (V := V)).CS) (h_max : Height) (T : Finset (Block V)) (cur : Slot) (A : Block V) (tree : Finset (Block V)) (votes support : Finset (GoldfishVote V)) (s : Slot)
    (score : Block V → ℕ) (hscore : ∀ B, (Model.spec (V := V)).goldfish_score E T votes support s B ⇢ score B)
    (elig : Block V → Bool) (helig : ∀ B, (Model.spec (V := V)).goldfish_eligible E σ h_max T cur votes support s B ⇢ elig B)
    (X : Block V), (Model.spec (V := V)).goldfish_fork_choice E σ h_max T cur A tree votes support s ⇢ X ↔
    (Model.spec (V := V)).ghost A tree score elig ⇢ X := by
  intro E σ h_max T cur A tree votes support s score hscore elig helig X
  rw [ForkChoiceImages.spec_goldfish_fork_choice_eq, ForkChoiceImages.spec_ghost_eq]
  rw [ForkChoiceImages.spec_goldfish_score_eq] at hscore
  rw [ForkChoiceImages.spec_goldfish_eligible_eq] at helig
  exact (Model.vocabulary_facts_forkChoice (V := V)).goldfish_fork_choice_eq_ghost E
    (fun C => (σ C).toProof) h_max T cur A tree votes support s score hscore elig helig X

end SpecRecord.ForkChoiceFacts

namespace SpecRecord.ForkChoiceFacts

/-! ## The SG root and the heads under a contract -/

open DecoupledConsensusModel DecoupledConsensusModel.Sts DecoupledConsensusModel.Sts.Record
open DecoupledConsensusModel.Execution
open SpecRecord.ContractImages
open DecoupledConsensusModel.Protocol (HealConfig HeightConfig Node GradeRead)
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-- The field `get_sg_root_with_eq_read_anchor` of `ForkChoiceFacts` at `Model.spec`: every
    outcome of the SG root `get_sg_root_with contract E hc st r` is the anchor of every outcome of
    the grade read `contract.read E hc st r`. -/
theorem spec_get_sg_root_with_eq_read_anchor :
    ∀ (contract : (Model.spec (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (st : (Model.spec (V := V)).HS) (r : Round) (G : GradeRead V), contract.read E hc st r ⇢ G → ∀ R : Block V, (Model.spec (V := V)).get_sg_root_with contract E hc st r ⇢ R → R = G.anchor := by
  intro contract E hc st r G hG R hR
  obtain ⟨A, hA, rfl⟩ := get_sg_root_with_shape (E := E) (hc := hc) hR
  obtain ⟨A', hA', e⟩ := read_anchor_shape (E := E) (hc := hc) hG
  rw [e, Except.ok.inj (hA.symm.trans hA')]

/-- The field `fg_root_preceq_get_sg_root_with_frame` of `ForkChoiceFacts` at `Model.spec`:
    under the frame contract of a cache, the FG root of `st` is an ancestor of every outcome of the
    SG root at round `r`, or that outcome itself. -/
theorem spec_fg_root_preceq_get_sg_root_with_frame :
    ∀ (c : (Model.spec (V := V)).Cache) (E : Env V) (hc : Protocol.HealConfig) (st : (Model.spec (V := V)).HS) (r : Round) (R : Block V), (Model.spec (V := V)).get_sg_root_with ((Model.spec (V := V)).frameContract c) E hc st r ⇢ R → Block.Preceq ((Model.spec (V := V)).get_fg_root st.toFG) R := by
  intro c E hc st r R hR
  obtain ⟨A, hA, rfl⟩ := get_sg_root_with_shape (E := E) (hc := hc) hR
  show DecoupledConsensusModel.Block.Preceq
    (Spec.Protocol.get_fg_root (Spec.Store.ofImage st.val)).toProof A.toProof
  unfold DecoupledConsensusModel.Block.Preceq
  refine Spec.Block.toProof_preceq_of_ancestorEq _ _ ?_
  rcases anchor_cases hA with e | hm
  · rw [e]; exact ancestorEq_self _
  · exact fg_root_ancestorEq_of_mem_filtered hm

/-- The field `fg_root_Preceq_get_sg_root_with_gradeContract` of `ForkChoiceFacts` at
    `Model.spec`: under the grade contract of a cache, the FG root of `st` is an ancestor of
    every outcome of the SG root at round `r`, or that outcome itself. -/
theorem spec_fg_root_Preceq_get_sg_root_with_gradeContract :
    ∀ (c : (Model.spec (V := V)).Cache) (E : Env V) (hc : Protocol.HealConfig) (st : (Model.spec (V := V)).HS) (r : Round) (R : Block V), (Model.spec (V := V)).get_sg_root_with ((Model.spec (V := V)).gradeContract c) E hc st r ⇢ R → Block.Preceq ((Model.spec (V := V)).get_fg_root st.toFG) R := by
  intro c E hc st r R hR
  obtain ⟨A, hA, rfl⟩ := get_sg_root_with_shape (E := E) (hc := hc) hR
  show DecoupledConsensusModel.Block.Preceq
    (Spec.Protocol.get_fg_root (Spec.Store.ofImage st.val)).toProof A.toProof
  unfold DecoupledConsensusModel.Block.Preceq
  refine Spec.Block.toProof_preceq_of_ancestorEq _ _ ?_
  rcases anchor_cases hA with e | hm
  · rw [e]; exact ancestorEq_self _
  · exact fg_root_ancestorEq_of_mem_filtered hm

/-- The field `get_sg_root_with_gradeContract_mem_filtered` of `ForkChoiceFacts` at
    `Model.spec`: if the FG root of `st` is in `st`'s filtered tree, so is every outcome of the
    SG root under the grade contract of a cache. -/
theorem spec_get_sg_root_with_gradeContract_mem_filtered :
    ∀ (c : (Model.spec (V := V)).Cache) (E : Env V) (hc : Protocol.HealConfig) (st : (Model.spec (V := V)).HS) (r : Round) (hroot : (Model.spec (V := V)).get_fg_root st.toFG ∈ (Model.spec (V := V)).get_filtered_block_tree st.toFG) (R : Block V) (hR : (Model.spec (V := V)).get_sg_root_with ((Model.spec (V := V)).gradeContract c) E hc st r ⇢ R), R ∈
    (Model.spec (V := V)).get_filtered_block_tree st.toFG := by
  intro c E hc st r hroot R hR
  obtain ⟨A, hA, rfl⟩ := get_sg_root_with_shape (E := E) (hc := hc) hR
  rcases anchor_cases hA with e | hm
  · rw [e]; exact hroot
  · exact Finset.mem_image_of_mem _ hm

/-- The field `get_head_in_tree_with_layer_anchor_or_mem` of `ForkChoiceFacts` at `Model.spec`:
    every outcome of the head over `tree` under `contract` is the anchor of the grade read at the
    store's round, or a block of `tree`. -/
theorem spec_get_head_in_tree_with_layer_anchor_or_mem :
    ∀ (contract : (Model.spec (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (st : (Model.spec (V := V)).S) (tree : Finset (Block V)) (votes support : Finset (GoldfishVote V)) (k : Slot) (G : GradeRead V) (hG : contract.read E hc ((Model.spec (V := V)).toHealing st) ((Model.spec (V := V)).round_of hc st.s) ⇢ G) (X : Block V) (hX : (Model.spec (V := V)).get_head_in_tree_with_layer contract E hc ((Model.spec (V := V)).toHealing st) tree votes support k ⇢ X), X =
    G.anchor ∨
    X ∈
    tree := by
  intro contract E hc st tree votes support k G hG X hX
  obtain ⟨A, X', hA, hm, ha, rfl⟩ := get_head_in_tree_with_layer_shape hX
  obtain ⟨A', hA', e⟩ := read_anchor_shape (E := E) (hc := hc) hG
  have hr : (Model.spec (V := V)).round_of hc st.s =
      (Spec.Config.toSpec E hc unreadHeightConfig).round_of st.val.s := by
    simp only [Model.GS.s, Model.spec, Member.gs_s, Member.toHealing, Member.toFG, Member.toSG,
      Member.toGoldfishStore, Model.HS.toFG, Model.FGS.toSG, Model.SGS.toGoldfishStore, id_eq,
      toProof_gs_s, Spec.Store.toProof_s, Member.round_of]
    rfl
  rw [hr] at hA'
  have eA : A = A' := Except.ok.inj (hA.symm.trans hA')
  subst eA
  rcases hm with rfl | hm
  · exact Or.inl e.symm
  · right
    obtain ⟨B, hB, rfl⟩ := Finset.mem_map.mp hm
    show (st.val.blockOfImage B).toProof ∈ tree
    rw [Spec.Store.toProof_blockOfImage]
    exact hB

/-- The field `ModelProperties_get_head_in_tree_with_layer_mem` of `ForkChoiceFacts` at
    `Model.spec`: if a set `T` holds the anchor of the grade read at the store's round and
    every block of `tree`, it holds every outcome of the head over `tree`. -/
theorem spec_ModelProperties_get_head_in_tree_with_layer_mem :
    ∀ (contract : (Model.spec (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (st : (Model.spec (V := V)).HS) (tree : Finset (Block V)) (votes support : Finset (GoldfishVote V)) (k : Slot) {T : Finset (Block V)} (G : GradeRead V) (hG : contract.read E hc st (((Model.spec (V := V)).round_of hc st.toFG.toSG.toGoldfishStore.s)) ⇢ G) (hanchor : G.anchor ∈ T) (htree : tree ⊆ T) (X : Block V) (hX : (Model.spec (V := V)).get_head_in_tree_with_layer contract E hc st tree votes support k ⇢ X), X ∈ T := by
  intro contract E hc st tree votes support k T G hG hanchor htree X hX
  obtain ⟨A, X', hA, hm, ha, rfl⟩ := get_head_in_tree_with_layer_shape hX
  obtain ⟨A', hA', e⟩ := read_anchor_shape (E := E) (hc := hc) hG
  have hr : (Model.spec (V := V)).round_of hc st.toFG.toSG.toGoldfishStore.s =
      (Spec.Config.toSpec E hc unreadHeightConfig).round_of st.val.s := by
    simp only [Model.GS.s, Model.spec, Member.gs_s, Member.toHealing, Member.toFG, Member.toSG,
      Member.toGoldfishStore, Model.HS.toFG, Model.FGS.toSG, Model.SGS.toGoldfishStore, id_eq,
      toProof_gs_s, Spec.Store.toProof_s, Member.round_of]
    rfl
  rw [hr] at hA'
  have eA : A = A' := Except.ok.inj (hA.symm.trans hA')
  subst eA
  rcases hm with rfl | hm
  · rw [← e]; exact hanchor
  · obtain ⟨B, hB, rfl⟩ := Finset.mem_map.mp hm
    show (st.val.blockOfImage B).toProof ∈ T
    rw [Spec.Store.toProof_blockOfImage]
    exact htree hB

/-- The field `Sts_get_head_in_tree_with_layer_mem` of `ForkChoiceFacts` at `Model.spec`: if a
    set `T` holds an outcome of the SG root at the store's round and every block of `tree`, it holds
    every outcome of the head over `tree`. -/
theorem spec_Sts_get_head_in_tree_with_layer_mem :
    ∀ (contract : (Model.spec (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (st : (Model.spec (V := V)).HS) (tree : Finset (Block V)) (votes support : Finset (GoldfishVote V)) (k : Slot) {T : Finset (Block V)} (R : Block V) (hR : (Model.spec (V := V)).get_sg_root_with contract E hc st (((Model.spec (V := V)).round_of hc st.toFG.toSG.toGoldfishStore.s)) ⇢ R) (hA : R ∈ T) (htree : tree ⊆ T) (X : Block V) (hX : (Model.spec (V := V)).get_head_in_tree_with_layer contract E hc st tree votes support k ⇢ X), X ∈ T := by
  intro contract E hc st tree votes support k T R hR hanchor htree X hX
  obtain ⟨A, X', hA, hm, ha, rfl⟩ := get_head_in_tree_with_layer_shape hX
  obtain ⟨A', hA', e⟩ := get_sg_root_with_shape (E := E) (hc := hc) hR
  have hr : (Model.spec (V := V)).round_of hc st.toFG.toSG.toGoldfishStore.s =
      (Spec.Config.toSpec E hc unreadHeightConfig).round_of st.val.s := by
    simp only [Model.GS.s, Model.spec, Member.gs_s, Member.toHealing, Member.toFG, Member.toSG,
      Member.toGoldfishStore, Model.HS.toFG, Model.FGS.toSG, Model.SGS.toGoldfishStore, id_eq,
      toProof_gs_s, Spec.Store.toProof_s, Member.round_of]
    rfl
  rw [hr] at hA'
  have eA : A = A' := Except.ok.inj (hA.symm.trans hA')
  subst eA
  rcases hm with rfl | hm
  · rw [← e]; exact hanchor
  · obtain ⟨B, hB, rfl⟩ := Finset.mem_map.mp hm
    show (st.val.blockOfImage B).toProof ∈ T
    rw [Spec.Store.toProof_blockOfImage]
    exact htree hB

/-- The field `read_anchor_preceq_get_head_in_tree_with_layer` of `ForkChoiceFacts` at
    `Model.spec`: the anchor of the grade read at the store's round is an ancestor of every
    outcome of the head over any tree, or that outcome itself. -/
theorem spec_read_anchor_preceq_get_head_in_tree_with_layer :
    ∀ (contract : (Model.spec (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (st : (Model.spec (V := V)).HS) (tree : Finset (Block V)) (votes support : Finset (GoldfishVote V)) (k : Slot) (G : GradeRead V) (hG : contract.read E hc st (((Model.spec (V := V)).round_of hc st.toFG.toSG.toGoldfishStore.s)) ⇢ G) (X : Block V) (hX : (Model.spec (V := V)).get_head_in_tree_with_layer contract E hc st tree votes support k ⇢ X), Block.Preceq G.anchor X := by
  intro contract E hc st tree votes support k G hG X hX
  obtain ⟨A, X', hA, hm, ha, rfl⟩ := get_head_in_tree_with_layer_shape hX
  obtain ⟨A', hA', e⟩ := read_anchor_shape (E := E) (hc := hc) hG
  have hr : (Model.spec (V := V)).round_of hc st.toFG.toSG.toGoldfishStore.s =
      (Spec.Config.toSpec E hc unreadHeightConfig).round_of st.val.s := by
    simp only [Model.GS.s, Model.spec, Member.gs_s, Member.toHealing, Member.toFG, Member.toSG,
      Member.toGoldfishStore, Model.HS.toFG, Model.FGS.toSG, Model.SGS.toGoldfishStore, id_eq,
      toProof_gs_s, Spec.Store.toProof_s, Member.round_of]
    rfl
  rw [hr] at hA'
  have eA : A = A' := Except.ok.inj (hA.symm.trans hA')
  subst eA
  rw [e]
  unfold DecoupledConsensusModel.Block.Preceq
  exact Spec.Block.toProof_preceq_of_ancestorEq _ _ (ha A (ancestorEq_self A))

/-- The field `fgRoot_Preceq_get_head_in_tree_with_layer_gradeContract` of `ForkChoiceFacts` at
    `Model.spec`: under the grade contract of a cache, the FG root of `st` is an ancestor of
    every outcome of the head over any tree, or that outcome itself. -/
theorem spec_fgRoot_Preceq_get_head_in_tree_with_layer_gradeContract :
    ∀ (c : (Model.spec (V := V)).Cache) (E : Env V) (hc : Protocol.HealConfig) (st : (Model.spec (V := V)).HS) (tree : Finset (Block V)) (votes support : Finset (GoldfishVote V)) (k : Slot) (X : Block V), (Model.spec (V := V)).get_head_in_tree_with_layer ((Model.spec (V := V)).gradeContract c) E hc st tree votes
    support k ⇢ X → Block.Preceq ((Model.spec (V := V)).get_fg_root st.toFG) X := by
  intro c E hc st tree votes support k X hX
  obtain ⟨A, X', hA, hm, ha, rfl⟩ := get_head_in_tree_with_layer_shape hX
  show DecoupledConsensusModel.Block.Preceq
    (Spec.Protocol.get_fg_root (Spec.Store.ofImage st.val)).toProof X'.toProof
  unfold DecoupledConsensusModel.Block.Preceq
  refine Spec.Block.toProof_preceq_of_ancestorEq _ _ (ha _ ?_)
  rcases anchor_cases hA with e | hm'
  · rw [e]; exact ancestorEq_self _
  · exact fg_root_ancestorEq_of_mem_filtered hm'

/-- The field `get_head_with_mem_filtered` of `ForkChoiceFacts` at `Model.spec`: if an outcome
    of the SG root at `st`'s round is in `st`'s filtered tree, so is every outcome of the head
    `get_head_with`. -/
theorem spec_get_head_with_mem_filtered :
    ∀ (contract : (Model.spec (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (st : (Model.spec (V := V)).HS) (votes support : Finset (GoldfishVote V)) (k : Slot) (R : Block V) (hR : (Model.spec (V := V)).get_sg_root_with contract E hc st (((Model.spec (V := V)).round_of hc st.toFG.toSG.toGoldfishStore.s)) ⇢ R) (hanchor : R ∈
    (Model.spec (V := V)).get_filtered_block_tree st.toFG) (X : Block V) (hX : (Model.spec (V := V)).get_head_with contract E hc st votes support k ⇢ X), X ∈
    (Model.spec (V := V)).get_filtered_block_tree st.toFG := by
  intro contract E hc st votes support k R hR hanchor X hX
  obtain ⟨A, X', hA, hm, ha, rfl⟩ := get_head_with_shape hX
  obtain ⟨A', hA', e⟩ := get_sg_root_with_shape (E := E) (hc := hc) hR
  have hr : (Model.spec (V := V)).round_of hc st.toFG.toSG.toGoldfishStore.s =
      (Spec.Config.toSpec E hc unreadHeightConfig).round_of st.val.s := by
    simp only [Model.GS.s, Model.spec, Member.gs_s, Member.toHealing, Member.toFG, Member.toSG,
      Member.toGoldfishStore, Model.HS.toFG, Model.FGS.toSG, Model.SGS.toGoldfishStore, id_eq,
      toProof_gs_s, Spec.Store.toProof_s, Member.round_of]
    rfl
  rw [hr] at hA'
  have eA : A = A' := Except.ok.inj (hA.symm.trans hA')
  subst eA
  rcases hm with rfl | hm
  · rw [← e]; exact hanchor
  · exact Finset.mem_image_of_mem _ hm

/-- The field `get_head_with_gradeContract_mem` of `ForkChoiceFacts` at `Model.spec`: if the FG
    root of `st` is in `st`'s tree, so is every outcome of the head `get_head_with` under the grade
    contract of a cache. -/
theorem spec_get_head_with_gradeContract_mem :
    ∀ (c : (Model.spec (V := V)).Cache) (E : Env V) (hc : Protocol.HealConfig) (st : (Model.spec (V := V)).HS) (votes support : Finset (GoldfishVote V)) (k : Slot) (hroot : (Model.spec (V := V)).get_fg_root st.toFG ∈ st.toFG.toSG.toGoldfishStore.T) (X : Block V) (hX : (Model.spec (V := V)).get_head_with ((Model.spec (V := V)).gradeContract c) E hc st votes support k ⇢ X), X
    ∈ st.toFG.toSG.toGoldfishStore.T := by
  intro c E hc st votes support k hroot X hX
  obtain ⟨A, X', hA, hm, ha, rfl⟩ := get_head_with_shape hX
  rcases hm with rfl | hm
  · rcases anchor_cases hA with e | hm'
    · rw [e]; exact hroot
    · show X'.toProof ∈ Member.gs_T st.val
      rw [Member.gs_T, toProof_gs_T]
      have hsub := GradesImages.filtered_subset _ hm'
      exact Finset.mem_image_of_mem _ hsub
  · show X'.toProof ∈ Member.gs_T st.val
    rw [Member.gs_T, toProof_gs_T]
    have hsub := GradesImages.filtered_subset _ hm
    exact Finset.mem_image_of_mem _ hsub

/-- The field `NamedProposalParent_get_head_with_mem` of `ForkChoiceFacts` at `Model.spec`: if
    the anchor of an outcome of the grade read at the round of `st`'s slot is in `st`'s tree, so is
    every outcome of the head `get_head_with`. -/
theorem spec_NamedProposalParent_get_head_with_mem :
    ∀ (gc : (Model.spec (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (st : (Model.spec (V := V)).HS) (votes support : Finset (GoldfishVote V)) (k : Slot) (G : GradeRead V),
    gc.read E hc st ((Model.spec (V := V)).round_of hc st.toFG.toSG.toGoldfishStore.s) ⇢ G → G.anchor ∈ st.toFG.toSG.toGoldfishStore.T →
    ∀ X : Block V, (Model.spec (V := V)).get_head_with gc E hc st votes support k ⇢ X → X ∈ st.toFG.toSG.toGoldfishStore.T := by
  intro gc E hc st votes support k G hG hanchor X hX
  obtain ⟨A, X', hA, hm, ha, rfl⟩ := get_head_with_shape hX
  obtain ⟨A', hA', e⟩ := read_anchor_shape (E := E) (hc := hc) hG
  have hr : (Model.spec (V := V)).round_of hc st.toFG.toSG.toGoldfishStore.s =
      (Spec.Config.toSpec E hc unreadHeightConfig).round_of st.val.s := by
    simp only [Model.GS.s, Model.spec, Member.gs_s, Member.toHealing, Member.toFG, Member.toSG,
      Member.toGoldfishStore, Model.HS.toFG, Model.FGS.toSG, Model.SGS.toGoldfishStore, id_eq,
      toProof_gs_s, Spec.Store.toProof_s, Member.round_of]
    rfl
  rw [hr] at hA'
  have eA : A = A' := Except.ok.inj (hA.symm.trans hA')
  subst eA
  rcases hm with rfl | hm
  · rw [← e]; exact hanchor
  · show X'.toProof ∈ Member.gs_T st.val
    rw [Member.gs_T, toProof_gs_T]
    have hsub := GradesImages.filtered_subset _ hm
    exact Finset.mem_image_of_mem _ hsub

/-! ## The head as the Goldfish fork choice from the SG root -/

/-- The field `get_head_in_tree_split_with` of `ForkChoiceFacts` at `Model.spec`: for every
    outcome `R` of the SG root at the store's round, `X` is an outcome of the head in `tree` exactly
    when it is an outcome of the Goldfish fork choice from `R` through `tree`. -/
theorem spec_get_head_in_tree_split_with : ∀ (contract : (Model.spec (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (st : (Model.spec (V := V)).HS) (tree : Finset (Block V)) (votes support_votes : Finset (GoldfishVote V)) (k : Slot)
    (R : Block V), (Model.spec (V := V)).get_sg_root_with contract E hc st (((Model.spec (V := V)).round_of hc st.s)) ⇢ R →
    ∀ X : Block V, (Model.spec (V := V)).get_head_in_tree_with_layer contract E hc st tree votes support_votes k ⇢ X ↔
      (Model.spec (V := V)).goldfish_fork_choice E st.σ st.h_max st.T st.s R tree votes support_votes k ⇢ X := by
  intro c E hc st tree votes support k R hR X
  have hr : (Model.spec (V := V)).round_of hc st.s =
      (Spec.Config.toSpec E hc unreadHeightConfig).round_of st.val.s := by
    simp only [Model.HS.s, Model.GS.s, Model.spec, Member.gs_s, Member.toHealing, Member.toFG, Member.toSG,
      Member.toGoldfishStore, Model.HS.toFG, Model.FGS.toSG, Model.SGS.toGoldfishStore, id_eq,
      toProof_gs_s, Member.round_of]
    rfl
  have hR' : Returns (Member.get_sg_root_with c E hc st.val
      ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.val.s)) R := by
    rw [← hr]; exact hR
  have e := member_get_head_in_tree_with_layer_eq st c E hc tree votes support k hR'
  rw [ForkChoiceImages.spec_goldfish_fork_choice_eq]
  show Returns (Member.get_head_in_tree_with_layer c E hc st.val tree votes support k) X ↔ _
  rw [e]
  simp only [Model.vocabulary, returns_pure]
  have hT : st.T = st.val.T.image Spec.Block.toProof := by
    simp only [Model.HS.T, Model.GS.T, Model.spec, Member.gs_T, Member.toFG, Member.toSG,
      Member.toGoldfishStore, Model.HS.toFG, Model.FGS.toSG, Model.SGS.toGoldfishStore, id_eq,
      toProof_gs_T]
  have hσ : (fun C => Spec.Protocol.ChainState.toProof (st.σ C)) =
      (fun C => (st.val.σ (st.val.blockOfImage C)).toProof) := rfl
  have hm : st.h_max = st.val.h_max := rfl
  have hs : st.s = st.val.s := by
    simp only [Model.HS.s, Model.GS.s, Model.spec, Member.gs_s, Member.toFG, Member.toSG,
      Member.toGoldfishStore, Model.HS.toFG, Model.FGS.toSG, Model.SGS.toGoldfishStore, id_eq,
      toProof_gs_s]
  rw [hT, hσ, hm, hs]

/-- The field `goldfish_eligible_false_of_parent_head` of `ForkChoiceFacts` at `Model.spec`: in
    a tree with injective roots, a block of `tree` whose parent is the head fails
    `goldfish_eligible`. -/
theorem spec_goldfish_eligible_false_of_parent_head : ∀ (contract : (Model.spec (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (st : (Model.spec (V := V)).S) (tree : Finset (Block V)) (votes support : Finset (GoldfishVote V)) (k : Slot) {C : Block V} (hroot : Execution.RootInjectiveBelow tree) (hC : C ∈ tree) (X : Block V) (hX : (Model.spec (V := V)).get_head_in_tree_with_layer contract E hc ((Model.spec (V := V)).toHealing st) tree votes support k ⇢ X) (hparent : C.parent? = some
    X) (e : Bool) (he : (Model.spec (V := V)).goldfish_eligible E st.σ st.h_max st.T st.s votes support k C ⇢ e), e = false := by
  intro c E hc st tree votes support k C hroot hC X hX hparent e he
  obtain ⟨A, -, hA, -, -, -⟩ := get_head_in_tree_with_layer_shape hX
  have eX := member_get_head_in_tree_with_layer_eq_of_anchor st c E hc tree votes support k hA
  have hX' : Returns (Member.get_head_in_tree_with_layer c E hc st.val tree votes support k) X := hX
  rw [eX, returns_pure] at hX'
  subst hX'
  rw [ForkChoiceImages.spec_goldfish_eligible_eq] at he
  simp only [Model.vocabulary, returns_pure] at he
  have hT : st.T = st.val.T.image Spec.Block.toProof := by
    simp only [Model.S.T, Model.spec, Member.store_T, Spec.Store.toProof_T]
  have hs : st.s = st.val.s := by
    simp only [Model.S.s, Model.spec, Member.store_s, Spec.Store.toProof_s]
  have hm : st.h_max = st.val.h_max := by
    simp only [Model.S.h_max, Model.spec, Member.store_h_max, Spec.Store.toProof_h_max]
  have hσ : (fun C => Spec.Protocol.ChainState.toProof (st.σ C)) =
      (fun C => (st.val.σ (st.val.blockOfImage C)).toProof) := rfl
  rw [hT, hs, hm, hσ] at he
  rw [he]
  unfold Protocol.goldfish_fork_choice at hparent
  exact DecoupledConsensusModel.Proofs.HealingSurface.eligible_child_false_at_ghost_result hroot hC
    hparent

end SpecRecord.ForkChoiceFacts

namespace SpecRecord.ForkChoiceFacts

/-! ## The Goldfish vote duty's vote -/

open DecoupledConsensusModel DecoupledConsensusModel.Sts DecoupledConsensusModel.Sts.Record
open DecoupledConsensusModel.Execution
open SpecRecord.ContractImages
open DecoupledConsensusModel.Protocol (HealConfig HeightConfig Node GradeRead)
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-- The field `goldfish_vote_with_snd_of_mem_committee` of `ForkChoiceFacts` at `Model.spec`:
    if `nd`'s validator is in the committee of `st`'s slot `s`, the Goldfish vote duty at `st`
    returns the vote of `nd`'s validator at slot `s` for the root of the head computed over the
    voter's filtered tree and views for slot `s − 1`. -/
theorem spec_goldfish_vote_with_snd_of_mem_committee :
    ∀ (contract : (Model.spec (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : (Model.spec (V := V)).NS) (hcom : nd.val_index ∈ E.committee st.core.s)
    (D : (Model.spec (V := V)).NS × Option (GoldfishVote V)) (hD : (Model.spec (V := V)).duties_goldfish_vote_with contract E hc nd st ⇢ D)
    (tree : Finset (Block V)) (htree : (Model.spec (V := V)).voter_filtered_block_tree E st.core st.core.s ⇢ tree)
    (votes : Finset (GoldfishVote V)) (hvotes : (Model.spec (V := V)).voter_view E ((Model.spec (V := V)).toHealing st.core).toFG.toSG.toGoldfishStore st.core.s ⇢ votes)
    (support : Finset (GoldfishVote V)) (hsupport : (Model.spec (V := V)).voter_support_view E ((Model.spec (V := V)).toHealing st.core).toFG.toSG.toGoldfishStore st.core.s ⇢ support)
    (H : Block V) (hH : (Model.spec (V := V)).get_head_in_tree_with_layer contract E hc ((Model.spec (V := V)).toHealing st.core) tree votes support (st.core.s - 1) ⇢ H),
    D.2 = some ⟨nd.val_index, st.core.s, H.root⟩ := by
  intro contract E hc nd st hcom D hD tree htree votes hvotes support hsupport H hH
  have h := duties_goldfish_vote_with_snd_spec ((returns_preimageOutcomes _ _ _).1 hD) htree hvotes
    hsupport hH
  rw [if_pos (show nd.val_index ∈ E.committee st.val.s from hcom)] at h
  exact h

/-- The field `namedDuties_goldfish_vote_with_snd_eq_some` of `ForkChoiceFacts` at
    `Model.spec`: if the Goldfish vote duty of `nd` at `st` returns the vote `u`, then `nd`'s
    validator is in the committee of `st`'s slot `s`, and `u` is its slot-`s` vote for the root of
    the head computed over the voter's filtered tree and views for slot `s − 1`. -/
theorem spec_namedDuties_goldfish_vote_with_snd_eq_some :
    ∀ (contract : (Model.spec (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : (Model.spec (V := V)).NS) {u : GoldfishVote V}
    (D : (Model.spec (V := V)).NS × Option (GoldfishVote V)) (hD : (Model.spec (V := V)).duties_goldfish_vote_with contract E hc nd st ⇢ D) (h : D.2 = some u)
    (tree : Finset (Block V)) (htree : (Model.spec (V := V)).voter_filtered_block_tree E st.core st.core.s ⇢ tree)
    (votes : Finset (GoldfishVote V)) (hvotes : (Model.spec (V := V)).voter_view E ((Model.spec (V := V)).toHealing st.core).toFG.toSG.toGoldfishStore st.core.s ⇢ votes)
    (support : Finset (GoldfishVote V)) (hsupport : (Model.spec (V := V)).voter_support_view E ((Model.spec (V := V)).toHealing st.core).toFG.toSG.toGoldfishStore st.core.s ⇢ support)
    (H : Block V) (hH : (Model.spec (V := V)).get_head_in_tree_with_layer contract E hc ((Model.spec (V := V)).toHealing st.core) tree votes support (st.core.s - 1) ⇢ H),
    nd.val_index ∈ E.committee st.core.s ∧
    u = ⟨nd.val_index, st.core.s, H.root⟩ := by
  intro contract E hc nd st u D hD hu tree htree votes hvotes support hsupport H hH
  have h := duties_goldfish_vote_with_snd_spec ((returns_preimageOutcomes _ _ _).1 hD) htree hvotes
    hsupport hH
  change D.2 = _ at h
  rw [hu] at h
  by_cases hcom : nd.val_index ∈ E.committee st.val.s
  · rw [if_pos hcom] at h
    exact ⟨hcom, Option.some.inj h⟩
  · rw [if_neg hcom] at h
    cases h

/-- The field `namedDuties_goldfish_vote_with_snd_head` of `ForkChoiceFacts` at `Model.spec`:
    if the Goldfish vote duty at `st` signs the vote `u`, the head of `u` is the root of every
    outcome of the head computed over the voter's tree and views at `st`'s slot, from the slot
    before it. -/
theorem spec_namedDuties_goldfish_vote_with_snd_head :
    ∀ (contract : (Model.spec (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : (Model.spec (V := V)).NS) {u : GoldfishVote V}
    (D : (Model.spec (V := V)).NS × Option (GoldfishVote V)) (hD : (Model.spec (V := V)).duties_goldfish_vote_with contract E hc nd st ⇢ D) (h : D.2 = some u)
    (tree : Finset (Block V)) (htree : (Model.spec (V := V)).voter_filtered_block_tree E st.core st.core.s ⇢ tree)
    (votes : Finset (GoldfishVote V)) (hvotes : (Model.spec (V := V)).voter_view E ((Model.spec (V := V)).toHealing st.core).toFG.toSG.toGoldfishStore st.core.s ⇢ votes)
    (support : Finset (GoldfishVote V)) (hsupport : (Model.spec (V := V)).voter_support_view E ((Model.spec (V := V)).toHealing st.core).toFG.toSG.toGoldfishStore st.core.s ⇢ support)
    (H : Block V) (hH : (Model.spec (V := V)).get_head_in_tree_with_layer contract E hc ((Model.spec (V := V)).toHealing st.core) tree votes support (st.core.s - 1) ⇢ H),
    u.head = H.root := by
  intro contract E hc nd st u D hD hu tree htree votes hvotes support hsupport H hH
  have h := duties_goldfish_vote_with_snd_spec ((returns_preimageOutcomes _ _ _).1 hD) htree hvotes
    hsupport hH
  change D.2 = _ at h
  rw [hu] at h
  by_cases hcom : nd.val_index ∈ E.committee st.val.s
  · rw [if_pos hcom] at h
    rw [Option.some.inj h]
  · rw [if_neg hcom] at h
    cases h

end SpecRecord.ForkChoiceFacts

namespace DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-- `Model.spec` satisfies `ForkChoiceRunFacts`, a structure with no field. -/
theorem Model.spec_runFacts_forkChoice : ForkChoiceRunFacts (Model.spec (V := V)) where

end DecoupledConsensusModel.Sts.Record
