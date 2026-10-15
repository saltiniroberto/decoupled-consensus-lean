import Proofs.Instance.Model
import Proofs.Instance.NoRaise.Routines
import Model.Record.Wiring

/-!
# The `_nonempty` fields at `Model.specDraft`

A `_nonempty` field of the record's facts bundles says that a member has an outcome for every
argument. This file proves those fields at `Model.specDraft`, each as
`SpecDraftRecord.<Bundle>.specDraft_<field>`, mostly from the two clauses of `StoreOk` that every
store of the store type meets.
-/

set_option autoImplicit false

namespace SpecDraftRecord.NonEmpty

open DecoupledConsensusModel.Sts.Record
open SpecDraftRecord.NoRaise

variable {V : Type}

/-- A store of the store type is stamped: every block, Goldfish vote and attestation it holds has a
    stamp. -/
theorem stamped (st : OkStore V) : Stamped st.val := st.property.1

/-- No two blocks of the tree of a store of the store type share a root. -/
theorem roots (st : OkStore V) : DistinctRoots st.val.T := st.property.2.1

/-- When `r = .ok a`, the call `successOutcomes r` returns `a`. -/
theorem returns_of_ok {α : Type} {r : DC.DRE α} {a : α} (h : r = .ok a) :
    Returns (successOutcomes r) a :=
  (returns_successOutcomes r a).2 h

end SpecDraftRecord.NonEmpty

/-- `nonempty_of h` closes a goal `∃ x, m ⇢ x` where the member `m` unfolds to `successOutcomes r`,
    from `h : ∃ v, routine … = .ok v` whose left-hand side occurs in `r`. -/
macro "nonempty_of " h:term : tactic =>
  `(tactic| (apply Exists.intro; apply SpecDraftRecord.NonEmpty.returns_of_ok; rw [($h).choose_spec]; try rfl))

namespace SpecDraftRecord.StoreFacts

open DecoupledConsensusModel DecoupledConsensusModel.Sts.Record
open SpecDraftRecord.NonEmpty

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-- The field `resolved_nonempty` of `StoreFacts` at `Model.specDraft`: whether a Goldfish vote `u`
    is resolved on a tree `T` is always answered. -/
theorem specDraft_resolved_nonempty : ∀ (T : Finset (Block V)) (u : GoldfishVote V),
    ∃ b : Bool, (Model.specDraft (V := V)).resolved T u ⇢ b := by
  intro T u
  nonempty_of orVocabulary_ok _ _

/-- The field `tau_nonempty` of `StoreFacts` at `Model.specDraft`: every store of the store type has
    a Goldfish-vote timestamp map. -/
theorem specDraft_tau_nonempty : ∀ (st : (Model.specDraft (V := V)).S),
    ∃ tm : TimestampMap (GoldfishVote V), st.tau ⇢ tm := by
  intro st
  classical
  have hok : ∀ u : GoldfishVote V,
      (st.val.timestamp_vote (Spec.GoldfishVote.toSpec u)).isSome →
        ∃ o, st.val.tau (Spec.GoldfishVote.toSpec u) = .ok o := fun u h =>
    NoRaise.tau_ok (roots st) (stamped st).1 (Option.isSome_iff_ne_none.1 h)
  refine ⟨fun u => if h : (st.val.timestamp_vote (Spec.GoldfishVote.toSpec u)).isSome
    then (hok u h).choose else none, ?_⟩
  show ∃ f : TimestampMap (GoldfishVote V), _
  refine ⟨_, fun u h => ?_, fun u h => ?_, rfl⟩
  · rw [dif_pos h]
    exact (hok u h).choose_spec
  · have h' : ¬ (st.val.timestamp_vote (Spec.GoldfishVote.toSpec u)).isSome := by
      rw [h]; exact Bool.false_ne_true
    rw [dif_neg h']

end SpecDraftRecord.StoreFacts

namespace SpecDraftRecord.ForkChoiceFacts

open DecoupledConsensusModel DecoupledConsensusModel.Sts.Record
open SpecDraftRecord.NonEmpty

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-- The field `targets_under_nonempty` of `ForkChoiceFacts` at `Model.specDraft`: whether a Goldfish
    vote targets a descendant of `B` on a tree `T` is always answered. -/
theorem specDraft_targets_under_nonempty :
    ∀ (T : Finset (Block V)) (B : Block V) (u : GoldfishVote V),
      ∃ b, (Model.specDraft (V := V)).targets_under T B u ⇢ b := by
  intro T B u
  nonempty_of orVocabulary_ok _ _

/-- The field `goldfish_score_nonempty` of `ForkChoiceFacts` at `Model.specDraft`: the Goldfish
    score of a block on a tree is always answered. -/
theorem specDraft_goldfish_score_nonempty :
    ∀ (E : Env V) (T : Finset (Block V)) (votes support_votes : Finset (GoldfishVote V))
      (s : Slot) (B : Block V),
      ∃ g : ℕ, (Model.specDraft (V := V)).goldfish_score E T votes support_votes s B ⇢ g := by
  intro E T votes support_votes s B
  nonempty_of orVocabulary_ok _ _

/-- The field `voter_filtered_block_tree_nonempty` of `ForkChoiceFacts` at `Model.specDraft`: every
    store of the store type has a voter's filtered block tree at every slot. -/
theorem specDraft_voter_filtered_block_tree_nonempty :
    ∀ (E : Env V) (st : (Model.specDraft (V := V)).S) (s : Slot),
      ∃ T : Finset (Block V), (Model.specDraft (V := V)).voter_filtered_block_tree E st s ⇢ T := by
  intro E st s
  nonempty_of NoRaise.voter_filtered_block_tree_ok _
    (show SpecDraftRecord.NoRaise.Stamped (Spec.Store.ofImage st.val) from stamped st) s

/-- The field `voter_view_nonempty` of `ForkChoiceFacts` at `Model.specDraft`: every store of the
    store type has a voter's view at every slot. -/
theorem specDraft_voter_view_nonempty :
    ∀ (E : Env V) (gst : (Model.specDraft (V := V)).GS) (s : Slot),
      ∃ W : Finset (GoldfishVote V), (Model.specDraft (V := V)).voter_view E gst s ⇢ W := by
  intro E gst s
  nonempty_of NoRaise.voter_view_ok _ (stamped gst) s

/-- The field `voter_support_view_nonempty` of `ForkChoiceFacts` at `Model.specDraft`: every store
    of the store type has a voter's support view at every slot. -/
theorem specDraft_voter_support_view_nonempty :
    ∀ (E : Env V) (gst : (Model.specDraft (V := V)).GS) (s : Slot),
      ∃ U : Finset (GoldfishVote V), (Model.specDraft (V := V)).voter_support_view E gst s ⇢ U := by
  intro E gst s
  nonempty_of NoRaise.voter_support_view_ok _ (roots gst) (stamped gst) s

/-- The field `raw_supporters_nonempty` of `ForkChoiceFacts` at `Model.specDraft`: the supporters of
    a block on a tree are always answered. -/
theorem specDraft_raw_supporters_nonempty :
    ∀ (T : Finset (Block V)) (votes support_votes : Finset (GoldfishVote V)) (s : Slot)
      (B : Block V), ∃ sup : Finset V,
        (Model.specDraft (V := V)).raw_supporters T votes support_votes s B ⇢ sup := by
  intro T votes support_votes s B
  nonempty_of orVocabulary_ok _ _

/-- The field `proposer_support_view_nonempty` of `ForkChoiceFacts` at `Model.specDraft`: every
    store of the store type has a proposer's support view at every slot. -/
theorem specDraft_proposer_support_view_nonempty :
    ∀ (gs : (Model.specDraft (V := V)).GS) (s : Slot),
      ∃ L : List (GoldfishVote V), (Model.specDraft (V := V)).proposer_support_view gs s ⇢ L := by
  intro gs s
  nonempty_of NoRaise.proposer_support_view_ok (roots gs) s

/-- The field `goldfish_eligible_nonempty` of `ForkChoiceFacts` at `Model.specDraft`: whether a
    block is eligible for the Goldfish walk is always answered. -/
theorem specDraft_goldfish_eligible_nonempty :
    ∀ (E : Env V) (σ : Block V → (Model.specDraft (V := V)).CS) (h_max : Height)
      (T : Finset (Block V)) (cur : Slot) (votes support : Finset (GoldfishVote V)) (s : Slot)
      (B : Block V),
      ∃ b : Bool,
        (Model.specDraft (V := V)).goldfish_eligible E σ h_max T cur votes support s B ⇢ b := by
  intro E σ h_max T cur votes support s B
  nonempty_of orVocabulary_ok _ _

/-- The field `voter_processed_block_tree_nonempty` of `ForkChoiceFacts` at `Model.specDraft`: every
    store of the store type has a voter's processed block tree at every slot. -/
theorem specDraft_voter_processed_block_tree_nonempty :
    ∀ (E : Env V) (gs : (Model.specDraft (V := V)).GS) (s : Slot),
      ∃ P : Finset (Block V), (Model.specDraft (V := V)).voter_processed_block_tree E gs s ⇢ P := by
  intro E gs s
  nonempty_of NoRaise.voter_processed_block_tree_ok _ (stamped gs) s

/-- The field `ghost_nonempty` of `ForkChoiceFacts` at `Model.specDraft`: the GHOST walk from `A` on
    a tree always answers a block. -/
theorem specDraft_ghost_nonempty :
    ∀ (A : Block V) (tree : Finset (Block V)) (score : Block V → ℕ) (elig : Block V → Bool),
      ∃ X : Block V, (Model.specDraft (V := V)).ghost A tree score elig ⇢ X := by
  intro A tree score elig
  nonempty_of NoRaise.ghost_ok (score := fun C => pure (score C.toProof))
    (eligible := fun C => pure (elig C.toProof)) (fun _ => ⟨_, rfl⟩) (fun _ => ⟨_, rfl⟩) _ _

/-- The field `ghost_step_nonempty` of `ForkChoiceFacts` at `Model.specDraft`: one GHOST step from
    `H` on a tree always answers. -/
theorem specDraft_ghost_step_nonempty :
    ∀ (tree : Finset (Block V)) (score : Block V → ℕ) (eligible : Block V → Bool)
      (H : Block V), ∃ o : Option (Block V),
        (Model.specDraft (V := V)).ghost_step tree score eligible H ⇢ o := by
  intro tree score eligible H
  nonempty_of NoRaise.ghost_step_ok (score := fun C => pure (score C.toProof))
    (eligible := fun C => pure (eligible C.toProof)) (fun _ => ⟨_, rfl⟩) (fun _ => ⟨_, rfl⟩) _ _

end SpecDraftRecord.ForkChoiceFacts

namespace SpecDraftRecord.GradesFacts

open DecoupledConsensusModel DecoupledConsensusModel.Sts.Record
open SpecDraftRecord.NonEmpty

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-- The field `positive_nonempty` of `GradesFacts` at `Model.specDraft`: whether a validator's vote
    is positive for `B` is always answered. -/
theorem specDraft_positive_nonempty :
    ∀ (gv : (Model.specDraft (V := V)).GV) (F : Block V) (η r : Round) (early late : Time)
      (u : V) (B : Block V),
      ∃ p : Bool, (Model.specDraft (V := V)).positive gv F η r early late u B ⇢ p := by
  intro gv F η r early late u B
  nonempty_of NoRaise.positive_ok (roots gv) (stamped gv) _ η r early late u _

/-- The field `opposing_nonempty` of `GradesFacts` at `Model.specDraft`: whether a validator's vote
    opposes `B` is always answered. -/
theorem specDraft_opposing_nonempty :
    ∀ (gv : (Model.specDraft (V := V)).GV) (F : Block V) (η r : Round) (early late : Time)
      (u : V) (B : Block V),
      ∃ o : Bool, (Model.specDraft (V := V)).opposing gv F η r early late u B ⇢ o := by
  intro gv F η r early late u B
  nonempty_of NoRaise.opposing_ok (roots gv) (stamped gv) _ η r early late u _

/-- The field `rawView_nonempty` of `GradesFacts` at `Model.specDraft`: a validator's raw view of a
    round is always answered. -/
theorem specDraft_rawView_nonempty :
    ∀ (gv : (Model.specDraft (V := V)).GV) (η r : Round) (c : Time) (u : V),
      ∃ X : Finset (DecoupledConsensusModel.Protocol.Token (Option BlockId)),
        (Model.specDraft (V := V)).rawView gv η r c u ⇢ X := by
  intro gv η r c u
  nonempty_of NoRaise.rawView_ok (stamped gv) η r c u

/-- The field `readyView_nonempty` of `GradesFacts` at `Model.specDraft`: a validator's ready view
    of a round is always answered. -/
theorem specDraft_readyView_nonempty :
    ∀ (gv : (Model.specDraft (V := V)).GV) (F : Block V) (η r : Round) (c : Time) (u : V),
      ∃ X : Finset (DecoupledConsensusModel.Protocol.Token (Option BlockId)),
        (Model.specDraft (V := V)).readyView gv F η r c u ⇢ X := by
  intro gv F η r c u
  nonempty_of (NoRaise.readyView_post (roots gv) (stamped gv) _ η r c u).imp fun _ h => h.1

/-- The field `head_covers_nonempty` of `GradesFacts` at `Model.specDraft`: whether a head key
    covers `B` on a tree is always answered. -/
theorem specDraft_head_covers_nonempty :
    ∀ (T : Finset (Block V)) (B : Block V) (k : Option BlockId),
      ∃ b : Bool, (Model.specDraft (V := V)).head_covers T B k ⇢ b := by
  intro T B k
  nonempty_of orVocabulary_ok _ _

/-- The field `onPhaseTick_nonempty` of `GradesFacts` at `Model.specDraft`: the grade tick always
    answers new saved grades. -/
theorem specDraft_onPhaseTick_nonempty :
    ∀ (E : Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig)
      (st : (Model.specDraft (V := V)).HS) (t : Int) (c : (Model.specDraft (V := V)).Cache),
      ∃ c' : (Model.specDraft (V := V)).Cache,
        (Model.specDraft (V := V)).onPhaseTick E hc st t c ⇢ c' := by
  intro E hc st t c
  nonempty_of NoRaise.update_grades_ok _ _ (st := { st.val with saved_grades := c })
    (roots st) (stamped st) t

/-- The field `rawInputs_nonempty` of `GradesFacts` at `Model.specDraft`: a validator's raw SG
    inputs of a round are always answered. -/
theorem specDraft_rawInputs_nonempty :
    ∀ (gv : (Model.specDraft (V := V)).GV) (η r : Round) (c : Time) (u : V),
      ∃ Y : Finset (DecoupledConsensusModel.Protocol.SGVote V),
        (Model.specDraft (V := V)).rawInputs gv η r c u ⇢ Y := by
  intro gv η r c u
  nonempty_of NoRaise.rawInputs_ok (stamped gv) η r c u

/-- The field `anchor_nonempty` of `GradesFacts` at `Model.specDraft`: the anchor of a grade-1
    result is always answered. -/
theorem specDraft_anchor_nonempty :
    ∀ (E : Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig)
      (st : (Model.specDraft (V := V)).HS) (r : Round) (g1 : Option (Option (Block V))),
      ∃ a, (Model.specDraft (V := V)).anchor E hc st r g1 ⇢ a := by
  intro E hc st r g1
  nonempty_of NoRaise.anchor_ok (Spec.Store.ofImage st.val) (fillResult_ne_pending _)

/-- The field `grade2Block_nonempty` of `GradesFacts` at `Model.specDraft`: the grade-2 block of a
    round's grades is always answered. -/
theorem specDraft_grade2Block_nonempty :
    ∀ (st : (Model.specDraft (V := V)).HS) (frame : (Model.specDraft (V := V)).Frame),
      ∃ o : Option (Block V), (Model.specDraft (V := V)).grade2Block st frame ⇢ o := by
  intro st frame
  have h := roundComputed_fillRound (st.val.roundGradesOfImage frame)
  nonempty_of NoRaise.grade2Block_ok (Spec.Store.ofImage st.val) h.2.2 h.2.1 h.1

/-- The field `gradeBool_nonempty` of `GradesFacts` at `Model.specDraft`: whether a block passes the
    grade test is always answered. -/
theorem specDraft_gradeBool_nonempty :
    ∀ (E : Env V) (gv : (Model.specDraft (V := V)).GV) (F : Block V) (η r : Round)
      (early late : Time) (B : Block V),
      ∃ b : Bool, (Model.specDraft (V := V)).gradeBool E gv F η r early late B ⇢ b := by
  intro E gv F η r early late B
  nonempty_of NoRaise.gradeBool_ok _ (roots gv) (stamped gv) _ η r early late _

/-- The field `bodyReady_nonempty` of `GradesFacts` at `Model.specDraft`: whether an SG vote is
    ready is always answered. -/
theorem specDraft_bodyReady_nonempty :
    ∀ (gv : (Model.specDraft (V := V)).GV) (F : Block V) (c : Time)
      (u : DecoupledConsensusModel.Protocol.SGVote V),
      ∃ b : Bool, (Model.specDraft (V := V)).bodyReady gv F c u ⇢ b := by
  intro gv F c u
  nonempty_of (NoRaise.bodyReady_post (roots gv) (stamped gv).1 _ c _).imp fun _ h => h.1

/-- The field `interpretedInputs_nonempty` of `GradesFacts` at `Model.specDraft`: a validator's
    interpreted SG inputs of a round are always answered. -/
theorem specDraft_interpretedInputs_nonempty :
    ∀ (gv : (Model.specDraft (V := V)).GV) (F : Block V) (η r : Round) (c : Time) (u : V),
      ∃ Y : Finset (DecoupledConsensusModel.Protocol.SGVote V),
        (Model.specDraft (V := V)).interpretedInputs gv F η r c u ⇢ Y := by
  intro gv F η r c u
  nonempty_of (NoRaise.interpretedInputs_post (roots gv) (stamped gv) _ η r c u).imp fun _ h => h.1

/-- The field `freezeRoot_nonempty` of `GradesFacts` at `Model.specDraft`: the freeze root of a
    round is always answered. -/
theorem specDraft_freezeRoot_nonempty :
    ∀ (E : Env V) (gv : (Model.specDraft (V := V)).GV) (F : Block V) (η r : Round)
      (early late : Time),
      ∃ fr : Option (Block V), (Model.specDraft (V := V)).freezeRoot E gv F η r early late ⇢ fr := by
  intro E gv F η r early late
  nonempty_of NoRaise.freezeRoot_ok _ (roots gv) (stamped gv) _ η r early late

end SpecDraftRecord.GradesFacts

namespace SpecDraftRecord.DutiesFacts

open DecoupledConsensusModel DecoupledConsensusModel.Sts.Record
open SpecDraftRecord.NonEmpty

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-- The field `select_nonempty` of `DutiesFacts` at `Model.specDraft`: the attestations a proposal
    includes are always answered. -/
theorem specDraft_select_nonempty :
    ∀ (source : DecoupledConsensusModel.Protocol.ProposalRowSource)
      (hc : DecoupledConsensusModel.Protocol.HealConfig) (st : (Model.specDraft (V := V)).NS),
      ∃ L : List (NamedAttestation V), (Model.specDraft (V := V)).select source hc st ⇢ L := by
  intro source hc st
  nonempty_of NoRaise.attestations_to_include_ok _ (roots st)

/-- The field `carriedRows_nonempty` of `DutiesFacts` at `Model.specDraft`: the attestations the
    store's blocks include in the window are always answered. -/
theorem specDraft_carriedRows_nonempty :
    ∀ (hc : DecoupledConsensusModel.Protocol.HealConfig) (st : (Model.specDraft (V := V)).NS),
      ∃ C : List (NamedAttestation V), (Model.specDraft (V := V)).carriedRows hc st ⇢ C := by
  intro hc st
  nonempty_of NoRaise.included_attestations_in_window_ok _ (roots st)

/-- The field `orderedBodies_nonempty` of `DutiesFacts` at `Model.specDraft`: the store's blocks in
    order are always answered. -/
theorem specDraft_orderedBodies_nonempty :
    ∀ (st : (Model.specDraft (V := V)).NS),
      ∃ O : List (NamedBlock V), (Model.specDraft (V := V)).orderedBodies st ⇢ O := by
  intro st
  nonempty_of NoRaise.sorted_blocks_ok (roots st)

end SpecDraftRecord.DutiesFacts

/-! ## The contract-taking fields -/

namespace SpecDraftRecord.NonEmpty

open Spec SpecDraftRecord.NoRaise

variable {V : Type} [DecidableEq V]

/-- `alignedStore st c ρ`: `st` read through its tree, with its saved grades replaced by `c` read
    through the tree, brought to round `ρ`, and filled. -/
abbrev alignedStore (st : Store V) (c : SavedGrades V) (ρ : Round) : Store V :=
  { Store.ofImage st with saved_grades := fill (Protocol.advance_to_round (st.contractOfImage c) ρ) }

/-- At round `ρ`, the saved grades of `alignedStore st c ρ` hold computed results only. -/
theorem alignedStore_computed (st : Store V) (c : SavedGrades V) (ρ : Round) :
    RoundComputed (Protocol.saved_round_grades (alignedStore st c ρ).saved_grades ρ) :=
  fill_advance_ne_pending _ ρ

/-- `StoreOk` reads no saved grades: replacing them keeps `StoreOk`. -/
theorem storeOk_with_saved_grades {st : Store V} (h : StoreOk st) (c : SavedGrades V) :
    StoreOk { st with saved_grades := c } := h

variable [Fintype V]

/-- An answer of the confirmation update meets `StoreOk` when its input does. -/
theorem storeOk_update_confirmation {C : Config} {st st' : Store V} {s : Slot}
    (h : Protocol.update_confirmation C st s = .ok st') (hs : StoreOk st) : StoreOk st' := by
  rw [update_confirmation_eq h]
  exact hs

/-- An answer of the Goldfish vote duty meets `StoreOk` when its input does. -/
theorem storeOk_goldfish_vote {C : Config} {P : Provisional V} {v : V} {st : Store V}
    {l : List (NamedObject V)} {out : Store V × List (NamedObject V)}
    (h : (Protocol.goldfish_vote C P v st).run l = .ok out) (hs : StoreOk st) :
    StoreOk out.1 := by
  unfold Protocol.goldfish_vote at h
  dsimp only at h
  rw [DREB.run_bind_ok_iff] at h
  obtain ⟨_, _, -, h⟩ := h
  rw [DREB.run_bind_ok_iff] at h
  obtain ⟨_, _, -, h⟩ := h
  rw [DREB.run_bind_ok_iff] at h
  obtain ⟨_, _, -, h⟩ := h
  rw [DREB.run_bind_ok_iff] at h
  obtain ⟨H, _, -, h⟩ := h
  split_ifs at h
  · rw [DREB.run_bind_ok_iff] at h
    obtain ⟨_, _, -, h⟩ := h
    rw [DREB.pure_run_ok_iff] at h
    subst h
    exact OkStore.on_goldfish_vote_checked P hs _
  · rw [DREB.pure_run_ok_iff] at h
    subst h
    exact hs

/-- An answer of the attestation duty is the input store after `admit_attestation` of the
    attestation `build_attestation` built, with the signing history it returned, and the objects
    sent are those before followed by that attestation. -/
theorem attest_out {C : Config} {v : V} {st : Store V} {sh : SigningHistory}
    {l : List (NamedObject V)} {out : (Store V × SigningHistory) × List (NamedObject V)}
    (h : (Protocol.attest C v st sh).run l = .ok out) :
    ∃ p : SigningHistory × Attestation V,
      out = ((Protocol.admit_attestation C st p.2, p.1), l ++ [NamedObject.attest p.2]) := by
  unfold Protocol.attest at h
  dsimp only at h
  cases hb : Protocol.build_attestation C v st sh with
  | error e => rw [hb] at h; cases h
  | ok p =>
    rw [hb] at h
    have h2 : (Except.ok ((Protocol.admit_attestation C st p.2, p.1), l ++ [NamedObject.attest p.2]) :
        DC.DRE ((Store V × SigningHistory) × List (NamedObject V))) = Except.ok out := h
    cases h2
    exact ⟨p, rfl⟩

/-- An answer of the attestation duty meets `StoreOk` when its input does. -/
theorem storeOk_attest {C : Config} {v : V} {st : Store V} {sh : SigningHistory}
    {l : List (NamedObject V)} {out : (Store V × SigningHistory) × List (NamedObject V)}
    (h : (Protocol.attest C v st sh).run l = .ok out) (hs : StoreOk st) : StoreOk out.1.1 := by
  obtain ⟨p, rfl⟩ := attest_out h
  exact OkStore.admit_attestation C hs p.2

end SpecDraftRecord.NonEmpty

namespace SpecDraftRecord.ForkChoiceFacts

open DecoupledConsensusModel DecoupledConsensusModel.Sts.Record
open SpecDraftRecord.NonEmpty

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-- The field `get_sg_root_with_nonempty` of `ForkChoiceFacts` at `Model.specDraft`: the SG root of
    every round, under every contract, is answered. -/
theorem specDraft_get_sg_root_with_nonempty : ∀ (contract : (Model.specDraft (V := V)).Contract)
    (E : Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig)
    (st : (Model.specDraft (V := V)).HS) (r : Round),
    ∃ R : Block V, (Model.specDraft (V := V)).get_sg_root_with contract E hc st r ⇢ R := by
  intro contract E hc st r
  nonempty_of NoRaise.anchor_ok (alignedStore st.val contract r)
    (g1 := (Spec.Protocol.round_grades (alignedStore st.val contract r) r).g1)
    (NoRaise.round_grades_ne_pending (p := .g1) (alignedStore_computed st.val contract r).2.1)

/-- The field `get_head_with_nonempty` of `ForkChoiceFacts` at `Model.specDraft`: the head under
    every contract is answered. -/
theorem specDraft_get_head_with_nonempty : ∀ (contract : (Model.specDraft (V := V)).Contract)
    (E : Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig)
    (st : (Model.specDraft (V := V)).HS) (votes support : Finset (GoldfishVote V)) (k : Slot),
    ∃ X : Block V, (Model.specDraft (V := V)).get_head_with contract E hc st votes support k ⇢ X := by
  intro contract E hc st votes support k
  nonempty_of NoRaise.get_head_with_ok _
    (st := alignedStore st.val contract
      ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.val.s))
    (roots st) (alignedStore_computed _ _ _).2.1 _ _ _

/-- The field `get_head_in_tree_with_layer_nonempty` of `ForkChoiceFacts` at `Model.specDraft`: the
    head in every tree under every contract is answered. -/
theorem specDraft_get_head_in_tree_with_layer_nonempty :
    ∀ (contract : (Model.specDraft (V := V)).Contract) (E : Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig)
      (st : (Model.specDraft (V := V)).HS) (tree : Finset (Block V))
      (votes support_votes : Finset (GoldfishVote V)) (k : Slot),
      ∃ X : Block V, (Model.specDraft (V := V)).get_head_in_tree_with_layer contract E hc st tree
        votes support_votes k ⇢ X := by
  intro contract E hc st tree votes support_votes k
  nonempty_of NoRaise.get_head_in_tree_with_layer_ok _
    (st := alignedStore st.val contract
      ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.val.s))
    (roots st) (alignedStore_computed _ _ _).2.1 _ _ _ _

end SpecDraftRecord.ForkChoiceFacts

namespace SpecDraftRecord.GradesFacts

open DecoupledConsensusModel DecoupledConsensusModel.Sts.Record
open SpecDraftRecord.NonEmpty

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-- The field `read_nonempty` of `GradesFacts` at `Model.specDraft`: the grade read of every round,
    under every contract, is answered. -/
theorem specDraft_read_nonempty : ∀ (gc : (Model.specDraft (V := V)).Contract) (E : Env V)
    (hc : DecoupledConsensusModel.Protocol.HealConfig) (st : (Model.specDraft (V := V)).HS)
    (r : Round), ∃ G, gc.read E hc st r ⇢ G := by
  intro gc E hc st r
  have h := alignedStore_computed st.val gc r
  nonempty_of NoRaise.round_grade_read_ok (st := alignedStore st.val gc r) h.2.2 h.2.1 h.1

/-- The field `frameStableRoot_nonempty` of `GradesFacts` at `Model.specDraft`: the stable root of
    every round, from every cache, is answered. -/
theorem specDraft_frameStableRoot_nonempty : ∀ (c : (Model.specDraft (V := V)).Cache) (E : Env V)
    (hc : DecoupledConsensusModel.Protocol.HealConfig) (st : (Model.specDraft (V := V)).HS)
    (r : Round), ∃ x : Option (Block V), (Model.specDraft (V := V)).frameStableRoot c E hc st r ⇢ x := by
  intro c E hc st r
  nonempty_of NoRaise.round_stable_root_ok (st := alignedStore st.val c r)
    (alignedStore_computed st.val c r).2.2

/-- The field `localCovers_nonempty` of `GradesFacts` at `Model.specDraft`: whether a key covers `B`
    on a grade view is always answered. -/
theorem specDraft_localCovers_nonempty : ∀ (gv : (Model.specDraft (V := V)).GV)
    (k : Option BlockId) (B : Block V), ∃ b : Bool, (Model.specDraft (V := V)).localCovers gv k B ⇢ b := by
  intro gv k B
  nonempty_of orVocabulary_ok _ _

end SpecDraftRecord.GradesFacts

namespace SpecDraftRecord.DutiesFacts

open DecoupledConsensusModel DecoupledConsensusModel.Sts.Record
open SpecDraftRecord.NonEmpty

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-- The field `goldfish_vote_with_nonempty` of `DutiesFacts` at `Model.specDraft`: the Goldfish vote
    duty under every contract answers a store of the store type. -/
theorem specDraft_goldfish_vote_with_nonempty : ∀ (gc : (Model.specDraft (V := V)).Contract)
    (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V)
    (st : (Model.specDraft (V := V)).NS),
    ∃ D : (Model.specDraft (V := V)).NS × Option (GoldfishVote V),
      (Model.specDraft (V := V)).duties_goldfish_vote_with gc E hc nd st ⇢ D := by
  intro gc E hc nd st
  obtain ⟨out, hout⟩ := NoRaise.goldfish_vote_ok _ (Spec.Provisional.toSpec E)
    nd.val_index (st := alignedStore st.val gc
      ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.val.s))
    (roots st) (stamped st) (alignedStore_computed _ _ _).2.1 []
  exact ⟨(⟨{ out.1 with saved_grades := gc }, storeOk_with_saved_grades
      (storeOk_goldfish_vote hout (storeOk_with_saved_grades (Spec.Store.storeOk_ofImage st.property) _)) _⟩,
      (Member.firstSentGoldfishVote out.2).map Spec.GoldfishVote.toProof),
    (returns_preimageOutcomes _ _ _).2 (returns_of_ok (by rw [hout]; rfl))⟩

/-- The field `round_action_with_nonempty` of `DutiesFacts` at `Model.specDraft`: the attestation
    built under every contract is answered. -/
theorem specDraft_round_action_with_nonempty : ∀ (contract : (Model.specDraft (V := V)).Contract)
    (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V)
    (st : (Model.specDraft (V := V)).HS) (record : (Model.specDraft (V := V)).NR),
    ∃ A, (Model.specDraft (V := V)).round_action_with contract E hc nd st record ⇢ A := by
  intro contract E hc nd st record
  have h := alignedStore_computed st.val contract
    ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.val.s)
  nonempty_of NoRaise.build_attestation_ok _
    (st := alignedStore st.val contract
      ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.val.s)) nd.val_index (roots st) h.2.2 h.2.1 h.1 record

/-- The field `with_attestation_input_nonempty` of `DutiesFacts` at `Model.specDraft`: the
    attestation input under every contract is answered. -/
theorem specDraft_with_attestation_input_nonempty :
    ∀ (contract : (Model.specDraft (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig)
      (nd : Protocol.Node V) (st : (Model.specDraft (V := V)).HS),
      ∃ I : Protocol.AttestationInput V,
        (Model.specDraft (V := V)).with_attestation_input contract E hc nd st id ⇢ I := by
  intro contract E hc nd st
  have h := alignedStore_computed st.val contract
    ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.val.s)
  nonempty_of NoRaise.attestation_input_ok _
    (st := alignedStore st.val contract
      ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.val.s)) nd.val_index (roots st) h.2.2 h.2.1 h.1

open scoped DC in
/-- The field `attest_with_nonempty` of `DutiesFacts` at `Model.specDraft`: the attestation duty
    under every contract answers a store of the store type. -/
theorem specDraft_attest_with_nonempty : ∀ (contract : (Model.specDraft (V := V)).Contract)
    (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V)
    (st : (Model.specDraft (V := V)).NS) (record : (Model.specDraft (V := V)).NR),
    ∃ D, (Model.specDraft (V := V)).duties_attest_with contract E hc nd st record ⇢ D := by
  intro contract E hc nd st record
  have h := alignedStore_computed st.val contract
    ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.val.s)
  obtain ⟨out, hout⟩ := NoRaise.attest_ok _
    (st := alignedStore st.val contract
      ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.val.s)) nd.val_index (roots st) h.2.2 h.2.1 h.1 record []
  have hok := storeOk_attest hout (storeOk_with_saved_grades (Spec.Store.storeOk_ofImage st.property) _)
  obtain ⟨p, hp⟩ := attest_out hout
  have ha : Member.firstSentAttestation out.2 = some p.2 := by
    rw [hp]; rfl
  exact ⟨(⟨{ out.1.1 with saved_grades := contract }, storeOk_with_saved_grades hok _⟩, out.1.2,
      p.2.toProofNamed),
    (returns_preimageOutcomes _ _ _).2 (returns_of_ok (by
      rw [hout]
      simp only [NoRaise.DRE.bind_ok]
      rw [show (liftM (Member.firstSentAttestation out.2) :
          DC.DRE (Spec.Attestation V)) = .ok p.2 by rw [ha]; rfl]
      rfl))⟩

/-- The field `grade2_block_with_nonempty` of `DutiesFacts` at `Model.specDraft`: the grade-2 block
    of every round, under every contract, is answered. -/
theorem specDraft_grade2_block_with_nonempty : ∀ (contract : (Model.specDraft (V := V)).Contract)
    (E : Env V) (hc : Protocol.HealConfig) (st : (Model.specDraft (V := V)).HS) (r : Round),
    ∃ A2, (Model.specDraft (V := V)).grade2_block_with contract E hc st r ⇢ A2 := by
  intro contract E hc st r
  have h := alignedStore_computed st.val contract r
  nonempty_of NoRaise.grade2_block_with_ok (st := alignedStore st.val contract r) h.2.2 h.2.1 h.1

/-- The field `get_sg_vote_with_nonempty` of `DutiesFacts` at `Model.specDraft`: the SG vote of
    every round, under every contract, is answered. -/
theorem specDraft_get_sg_vote_with_nonempty : ∀ (contract : (Model.specDraft (V := V)).Contract)
    (E : Env V) (hc : Protocol.HealConfig) (st : (Model.specDraft (V := V)).HS) (r : Round)
    (A2 : Option (Block V)),
    ∃ W, (Model.specDraft (V := V)).get_sg_vote_with contract E hc st r A2 ⇢ W := by
  intro contract E hc st r A2
  have h := alignedStore_computed st.val contract r
  nonempty_of NoRaise.get_sg_vote_with_ok (st := alignedStore st.val contract r) h.2.2 h.2.1 h.1
    (A2.map Spec.Block.toSpec)

/-- The field `update_confirmation_with_nonempty` of `DutiesFacts` at `Model.specDraft`: the
    confirmation update under every contract answers a store of the store type. -/
theorem specDraft_update_confirmation_with_nonempty :
    ∀ (contract : (Model.specDraft (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig)
      (st : (Model.specDraft (V := V)).S) (s : Slot),
      ∃ X, (Model.specDraft (V := V)).update_confirmation_with contract E hc st s ⇢ X := by
  intro contract E hc st s
  have h := alignedStore_computed st.val contract
    ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.val.s)
  obtain ⟨out, hout⟩ := NoRaise.update_confirmation_ok _
    (st := alignedStore st.val contract
      ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.val.s)) (roots st) (stamped st) h.2.1 h.2.2 s
  exact ⟨⟨{ out with saved_grades := contract }, storeOk_with_saved_grades
      (storeOk_update_confirmation hout (storeOk_with_saved_grades (Spec.Store.storeOk_ofImage st.property) _)) _⟩,
    (returns_preimageOutcomes _ _ _).2 (returns_of_ok (by rw [hout]; rfl))⟩

/-- The field `with_proposal_input_nonempty` of `DutiesFacts` at `Model.specDraft`: the proposal
    input under every contract is answered. -/
theorem specDraft_with_proposal_input_nonempty :
    ∀ (contract : (Model.specDraft (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig)
      (nd : Protocol.Node V) (st : (Model.specDraft (V := V)).HS),
      ∃ P : Protocol.ProposalInput V,
        (Model.specDraft (V := V)).with_proposal_input contract E hc nd st id ⇢ P := by
  intro contract E hc nd st
  have h := alignedStore_computed st.val contract
    ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.val.s)
  nonempty_of NoRaise.proposal_input_ok _
    (st := alignedStore st.val contract
      ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.val.s)) (Member.externalOfNode nd) nd.val_index (roots st) h.2.1

/-- The field `proposal_with_nonempty` of `DutiesFacts` at `Model.specDraft`: the proposal under
    every contract is answered. -/
theorem specDraft_proposal_with_nonempty : ∀ (contract : (Model.specDraft (V := V)).Contract)
    (source : Protocol.ProposalRowSource) (E : Env V) (hc : Protocol.HealConfig)
    (nd : Protocol.Node V) (st : (Model.specDraft (V := V)).NS),
    ∃ o : Option (NamedBlock V),
      (Model.specDraft (V := V)).proposal_with contract source E hc nd st ⇢ o := by
  intro contract source E hc nd st
  have h := alignedStore_computed st.val contract
    ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.val.s)
  nonempty_of NoRaise.build_proposal_ok _
    (st := alignedStore st.val contract
      ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.val.s)) (Member.externalOfNode nd) nd.val_index (roots st) h.2.1

/-- The field `duties_update_confirmation_with_nonempty` of `DutiesFacts` at `Model.specDraft`: the
    named confirmation duty under every contract answers a store of the store type. -/
theorem specDraft_duties_update_confirmation_with_nonempty :
    ∀ (contract : (Model.specDraft (V := V)).Contract) (E : Env V)
      (hc : Protocol.HealConfig) (st : (Model.specDraft (V := V)).NS) (s : Slot),
      ∃ st' : (Model.specDraft (V := V)).NS,
        (Model.specDraft (V := V)).duties_update_confirmation_with contract E hc st s ⇢ st' := by
  intro contract E hc st s
  have h := alignedStore_computed st.val contract
    ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.val.s)
  obtain ⟨out, hout⟩ := NoRaise.update_confirmation_ok _
    (st := alignedStore st.val contract
      ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.val.s)) (roots st) (stamped st) h.2.1 h.2.2 s
  exact ⟨⟨{ out with saved_grades := contract }, storeOk_with_saved_grades
      (storeOk_update_confirmation hout (storeOk_with_saved_grades (Spec.Store.storeOk_ofImage st.property) _)) _⟩,
    (returns_preimageOutcomes _ _ _).2 (returns_of_ok (by rw [hout]; rfl))⟩

/-- The field `fg_source_with_nonempty` of `DutiesFacts` at `Model.specDraft`: the finality-gadget
    source of every round, under every contract, is answered. -/
theorem specDraft_fg_source_with_nonempty : ∀ (contract : (Model.specDraft (V := V)).Contract)
    (E : Env V) (hc : Protocol.HealConfig) (st : (Model.specDraft (V := V)).HS) (r : Round)
    (A2 : Option (Block V)),
    ∃ F, (Model.specDraft (V := V)).fg_source_with contract E hc st r A2 ⇢ F := by
  intro contract E hc st r A2
  nonempty_of NoRaise.fg_source_with_ok (st := alignedStore st.val contract r)
    (alignedStore_computed st.val contract r).1 (A2.map st.val.blockOfImage)

end SpecDraftRecord.DutiesFacts

namespace SpecDraftRecord.NodeFacts

open DecoupledConsensusModel DecoupledConsensusModel.Sts.Record DecoupledConsensusModel.Execution
open SpecDraftRecord.NonEmpty

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-- If no held named block other than a received block `B` has `B`'s root, then no block of the
    node's tree other than `B`'s spec form has it. -/
theorem not_objectRootHeldByOther (n : (Model.specDraft (V := V)).N) (o : NamedObject V)
    (hroot : ∀ B : NamedBlock V, o = NamedObject.block B →
      ∀ C ∈ n.st.bodies, C.root = B.root → C = B) :
    ¬ objectRootHeldByOther n.val.st.T o := by
  cases o with
  | block B =>
    rintro ⟨B', hB', hne, hr⟩
    apply hne
    have hC : Spec.Block.toProofNamed B' ∈ n.st.bodies :=
      Finset.mem_map_of_mem _ hB'
    have e := hroot B rfl _ hC (by
      rw [Spec.Block.toProofNamed_root, hr, ← Spec.Block.toProofNamed_root,
        Spec.Block.toProofNamed_toSpecNamed])
    rw [← e, Spec.Block.toSpecNamed_toProofNamed]
  | gfVote _ => exact id
  | attest _ => exact id

/-- The field `process_nonempty` of `NodeFacts` at `Model.specDraft`: receiving an object, other
    than a block whose root another held block has, always gives a node state. -/
theorem specDraft_process_nonempty : ∀ (S : Setup V) (n : (Model.specDraft (V := V)).N)
    (o : NamedObject V)
    -- if `o` is a block `B`, no block of `n`'s bodies has `B`'s root unless it is `B`
    (hroot : ∀ B : NamedBlock V, o = NamedObject.block B →
      ∀ C ∈ n.st.bodies, C.root = B.root → C = B),
    ∃ n' : (Model.specDraft (V := V)).N, (Model.specDraft (V := V)).process S n o ⇢ n' := by
  intro S n o hroot
  have h := OkStore.receipt_process S n.property (not_objectRootHeldByOther n o hroot)
  have hok : NoRaise.StoreOk (receiveNamedObject S n.val o).st := by
    cases o <;> exact h
  exact ⟨⟨receiveNamedObject S n.val o, hok⟩, (returns_pure _ _).2 rfl⟩

end SpecDraftRecord.NodeFacts
