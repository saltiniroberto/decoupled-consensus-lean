import Proofs.Instance.Equalities.Images
import Proofs.Instance.Equalities.Grades
import Proofs.Instance.StoreOk
import Proofs.Instance.Model
import Proofs.Instance.NoRaise.Routines
import Proofs.Vocabulary.ModelVocabulary

/-!
# The grade members of `Model.specDraft` and of `Model.vocabulary` at the image of a store

Each `specDraft_<m>_eq` says that the member `m` of `Model.specDraft` at a store `st : OkStore V`
equals the member `m` of `Model.vocabulary` at the grade view of the image,
`st.val.toProof.toHealing.gradeView`. Each rests on a lemma about the spec's routine alone: on a
store meeting `StoreOk` the routine answers, and its answer, mapped, is the value of the routine of
the same name in `DecoupledConsensusModel.Protocol`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace SpecDraftRecord.GradesImages

open Spec
open SpecDraftRecord.ForkChoiceGrades
open SpecDraftRecord.NoRaise (Stamped DistinctRoots ParentClosed StoreOk)
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The raising filter -/

omit [DecidableEq V] [Fintype V] in
/-- If, on every member of `s`, `p` answers `true` exactly where `q` holds, then a filter of `s` by
    `p` that answers `v` keeps the members of `s` where `q` holds. -/
theorem filterM_eq_filter {α : Type} [DecidableEq α] (p : α → DC.DRE Bool)
    (q : α → Prop) [DecidablePred q] (s : Finset α)
    (hpq : ∀ a ∈ s, ∀ b, p a = .ok b → (b = true ↔ q a)) (v : Finset α)
    (hv : s.filterM p = .ok v) : v = s.filter q := by
  classical
  have key : ∀ (t : Finset α), t ⊆ s → ∀ w, t.filterM p = .ok w → w = t.filter q := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro _ w hw
      simp only [Finset.filterM, Finset.fold_empty] at hw
      cases hw
      rfl
    | @insert a t ha ih =>
      intro hts w hw
      have hstep : (insert a t).filterM p =
          Finset.unionM (do if ← p a then return {a} else return ∅) (t.filterM p) := by
        simp only [Finset.filterM, Finset.fold_insert ha]
      rw [hstep] at hw
      cases hpa : p a with
      | error e => simp [Finset.unionM, hpa, bind, Except.bind] at hw
      | ok b =>
        cases hrest : t.filterM p with
        | error e =>
          cases b <;> simp [Finset.unionM, hpa, hrest, bind, Except.bind, pure, Except.pure] at hw
        | ok w' =>
          have hw' := ih (fun x hx => hts (Finset.mem_insert_of_mem hx)) w' hrest
          have hb := hpq a (hts (Finset.mem_insert_self a t)) b hpa
          rw [Finset.filter_insert]
          cases b
          · have hq : ¬ q a := fun h => by simpa using hb.mpr h
            simp [Finset.unionM, hpa, hrest, bind, Except.bind, pure, Except.pure] at hw
            subst hw
            simp [hq, hw']
          · have hq : q a := hb.mp rfl
            simp [Finset.unionM, hpa, hrest, bind, Except.bind, pure, Except.pure] at hw
            subst hw
            rw [if_pos hq, hw', Finset.insert_eq]
  exact key s (subset_refl s) v hv

/-! ## The inputs: `rawInputs` -/

/-- On a stamped store `st`, the spec's `rawInputs` answers the votes of `st`'s latest window whose
    validator is `v` and whose stamp is strictly before `t`. -/
theorem rawInputs_eq {st : Store V} (hst : Stamped st) (eta r : Round) (t : Time) (v : V) :
    Protocol.rawInputs st eta r t v = .ok ((st.sg_votes_in_window eta r).filter fun u =>
      u.val_index = v ∧ DecoupledConsensusModel.occurrenceBefore (st.timestamp_sg_vote u) t = true) := by
  obtain ⟨w, hw⟩ := NoRaise.rawInputs_ok hst eta r t v
  rw [hw]
  congr 1
  unfold Protocol.rawInputs at hw
  refine filterM_eq_filter _ _ _ (fun u hu b hb => ?_) w hw
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp (NoRaise.stamped_sg hst hu)
  simp only [ha] at hb
  have hb' := (Except.ok.inj hb).symm
  subst hb'
  simp [DecoupledConsensusModel.occurrenceBefore, ha]

/-- `DecoupledConsensusModel.Protocol.rawInputs` on the grade view of the image of `st` is the
    images of the votes of `st`'s latest window whose validator is `v` and whose stamp is before
    `t`. -/
theorem vocabulary_rawInputs_toProof (st : Store V) (eta r : Round) (t : Time) (v : V) :
    DecoupledConsensusModel.Protocol.rawInputs st.toProof.toHealing.gradeView eta r t v =
      ((st.sg_votes_in_window eta r).filter fun u => u.val_index = v ∧
        DecoupledConsensusModel.occurrenceBefore (st.timestamp_sg_vote u) t = true).map
        Protocol.SGVote.toProofEmb := by
  ext u
  unfold DecoupledConsensusModel.Protocol.rawInputs
  rw [Finset.mem_filter, Finset.mem_map]
  simp only [Finset.mem_filter, Finset.mem_biUnion, toProof_gv_sg_votes, Finset.mem_map,
    toProof_gv_timestamp_sg_vote, Store.sg_votes_in_window, Protocol.SGVote.coe_toProofEmb,
    toProof_latest_window]
  constructor
  · rintro ⟨⟨r', hr', a, ha, rfl⟩, hv, ht⟩
    exact ⟨a, ⟨⟨r', hr', ha⟩, hv, by simpa using ht⟩, rfl⟩
  · rintro ⟨a, ⟨⟨r', hr', ha⟩, hv, ht⟩, rfl⟩
    exact ⟨⟨r', hr', a, ha, rfl⟩, hv, by simpa using ht⟩

/-! ## The body test: `bodyReady` -/

/-- The grade view of the image of `st` stamps the block `B` as the image of `st` does. -/
theorem toProof_gv_timestamp_block (st : Store V) (B : DecoupledConsensusModel.Block V) :
    st.toProof.toHealing.gradeView.timestamp_block B = st.toProof.timestamp_block B := by
  unfold DecoupledConsensusModel.Protocol.HealingStore.gradeView
  dsimp only
  unfold DecoupledConsensusModel.Protocol.Store.toHealing
  dsimp only

/-- On a store meeting `StoreOk`, the spec's `bodyReady` at the block standing for `F` and the spec
    form of the vote `u` answers `DecoupledConsensusModel.Protocol.bodyReady` on the grade view of
    the image. -/
theorem bodyReady_eq {st : Store V} (hok : StoreOk st) (F : DecoupledConsensusModel.Block V)
    (t : Time) (u : DecoupledConsensusModel.Protocol.SGVote V) :
    Protocol.bodyReady st (st.blockOfImage F) t (Protocol.SGVote.toSpec u) =
      .ok (DecoupledConsensusModel.Protocol.bodyReady st.toProof.toHealing.gradeView F t u) := by
  obtain ⟨hst, hT, hpar, -⟩ := hok
  have hinj := hT.injOn_toProof
  unfold DecoupledConsensusModel.Protocol.bodyReady
  cases hc : u.confirmed with
  | none =>
    have hc' : (Protocol.SGVote.toSpec u).confirmed = none := by
      simp [Protocol.SGVote.toSpec, hc]
    simp only [Protocol.bodyReady, hc']
    rfl
  | some x =>
    have hc' : (Protocol.SGVote.toSpec u).confirmed = some (BlockId.toSpec x) := by
      simp [Protocol.SGVote.toSpec, hc]
    have hfind : DecoupledConsensusModel.Block.find? st.toProof.toHealing.gradeView.T x =
        (Block.find? st.T (BlockId.toSpec x)).map Block.toProof := by
      rw [toProof_gv_T]
      have h := Block.toProof_find?_of_injOn st.T hinj (BlockId.toSpec x)
      rwa [BlockId.toProof_toSpec] at h
    simp only [Protocol.bodyReady, hc', ne_eq, reduceCtorEq, not_false_eq_true, dite_true,
      Option.value, Option.get_some, NoRaise.blockWithRoot_eq hT, NoRaise.DRE.bind_ok, hfind]
    cases hf : Block.find? st.T (BlockId.toSpec x) with
    | none => rfl
    | some H =>
      obtain ⟨hHT, -⟩ := NoRaise.find?_mem hf
      obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp (hst.1 H hHT)
      have hts : st.toProof.toHealing.gradeView.timestamp_block H.toProof = some a := by
        rw [toProof_gv_timestamp_block, Store.toProof_timestamp_block_of_mem st hinj hHT, ha]
      simp only [reduceCtorEq, not_false_eq_true, dite_true, Option.get_some, Option.map_some,
        ha, DecoupledConsensusModel.stampedBefore, hts,
        Store.compatible_blockOfImage_of_mem st hinj hpar hHT F]
      rfl

/-! ## The ready inputs: `interpretedInputs` -/

/-- On a store meeting `StoreOk`, the spec's `interpretedInputs` at the block standing for `F`
    answers the raw inputs of `rawInputs_eq` that `DecoupledConsensusModel.Protocol.bodyReady` finds
    ready on the grade view of the image. -/
theorem interpretedInputs_eq {st : Store V} (hok : StoreOk st)
    (F : DecoupledConsensusModel.Block V) (eta r : Round) (t : Time) (v : V) :
    Protocol.interpretedInputs st (st.blockOfImage F) eta r t v = .ok
      ((((st.sg_votes_in_window eta r).filter fun u => u.val_index = v ∧
        DecoupledConsensusModel.occurrenceBefore (st.timestamp_sg_vote u) t = true)).filter
        fun u => DecoupledConsensusModel.Protocol.bodyReady st.toProof.toHealing.gradeView F t
          u.toProof = true) := by
  have hbody : ∀ u : Protocol.SGVote V, Protocol.bodyReady st (st.blockOfImage F) t u =
      .ok (DecoupledConsensusModel.Protocol.bodyReady st.toProof.toHealing.gradeView F t
        u.toProof) := fun u => by
    have h := bodyReady_eq hok F t u.toProof
    rwa [Protocol.SGVote.toSpec_toProof] at h
  unfold Protocol.interpretedInputs
  rw [rawInputs_eq hok.1, NoRaise.DRE.bind_ok]
  obtain ⟨w, hw⟩ := NoRaise.filterM_ok (fun u => Protocol.bodyReady st (st.blockOfImage F) t u)
    _ (fun u _ => ⟨_, hbody u⟩)
  have hw' := filterM_eq_filter _ _ _ (fun u _ b hb => by
    rw [hbody u] at hb
    cases Except.ok.inj hb
    exact Iff.rfl) w hw
  subst hw'
  exact hw

/-- `DecoupledConsensusModel.Protocol.interpretedInputs` on the grade view of the image of `st` is
    the images of the raw inputs of `rawInputs_eq` that `DecoupledConsensusModel.Protocol.bodyReady`
    finds ready. -/
theorem vocabulary_interpretedInputs_toProof (st : Store V) (F : DecoupledConsensusModel.Block V)
    (eta r : Round) (t : Time) (v : V) :
    DecoupledConsensusModel.Protocol.interpretedInputs st.toProof.toHealing.gradeView F eta r t v =
      (((st.sg_votes_in_window eta r).filter fun u => u.val_index = v ∧
        DecoupledConsensusModel.occurrenceBefore (st.timestamp_sg_vote u) t = true).filter
        fun u => DecoupledConsensusModel.Protocol.bodyReady st.toProof.toHealing.gradeView F t
          u.toProof = true).map Protocol.SGVote.toProofEmb := by
  unfold DecoupledConsensusModel.Protocol.interpretedInputs
  rw [vocabulary_rawInputs_toProof, Finset.filter_map]
  rfl

/-! ## The token views: `rawView` and `readyView` -/

/-- The tokens of the images of a set of SG votes are the images of their tokens. -/
theorem image_token_map (X : Finset (Protocol.SGVote V)) :
    (X.map Protocol.SGVote.toProofEmb).image DecoupledConsensusModel.Protocol.token =
      (X.image Protocol.token).map Protocol.Token.toProofEmb := by
  ext k
  simp only [Finset.mem_image, Finset.mem_map, Protocol.SGVote.coe_toProofEmb,
    Protocol.Token.coe_toProofEmb]
  constructor
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨_, ⟨u, hu, rfl⟩, (toProof_token u).symm⟩
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨_, ⟨u, hu, rfl⟩, toProof_token u⟩

/-- On a stamped store, the spec's `rawView` answers the tokens of the raw inputs of `rawInputs_eq`. -/
theorem rawView_eq {st : Store V} (hst : Stamped st) (eta r : Round) (t : Time) (v : V) :
    Protocol.rawView st eta r t v = .ok (((st.sg_votes_in_window eta r).filter fun u =>
      u.val_index = v ∧
        DecoupledConsensusModel.occurrenceBefore (st.timestamp_sg_vote u) t = true).image
      Protocol.token) := by
  unfold Protocol.rawView
  rw [rawInputs_eq hst]
  rfl

/-- On a store meeting `StoreOk`, the spec's `readyView` at the block standing for `F` answers the
    tokens of the ready inputs of `interpretedInputs_eq`. -/
theorem readyView_eq {st : Store V} (hok : StoreOk st) (F : DecoupledConsensusModel.Block V)
    (eta r : Round) (t : Time) (v : V) :
    Protocol.readyView st (st.blockOfImage F) eta r t v = .ok
      (((((st.sg_votes_in_window eta r).filter fun u => u.val_index = v ∧
        DecoupledConsensusModel.occurrenceBefore (st.timestamp_sg_vote u) t = true)).filter
        fun u => DecoupledConsensusModel.Protocol.bodyReady st.toProof.toHealing.gradeView F t
          u.toProof = true).image Protocol.token) := by
  unfold Protocol.readyView
  rw [interpretedInputs_eq hok]
  rfl

/-! ## The coverage test and the grade computation -/

/-- On a store whose tree has distinct roots and is parent-closed, where the spec's `head_covers` at
    the block standing for `B` answers `b`, `b` is `DecoupledConsensusModel.Protocol.head_covers` on
    the images of the tree, at `B` and the image of the key. -/
theorem head_covers_eq_of_ok {st : Store V} (hT : DistinctRoots st.T) (hpar : ParentClosed st.T)
    (B : DecoupledConsensusModel.Block V) (k : Option BlockId) (b : Bool)
    (h : Protocol.head_covers st.T (st.blockOfImage B) k = .ok b) :
    b = DecoupledConsensusModel.Protocol.head_covers (st.T.image Block.toProof) B
      (k.map BlockId.toProof) := by
  have hinj := hT.injOn_toProof
  cases k with
  | none =>
    have h' : (Except.ok false : DC.DRE Bool) = .ok b := h
    cases h'
    simp [DecoupledConsensusModel.Protocol.head_covers]
  | some x =>
    simp only [Protocol.head_covers, ne_eq, reduceCtorEq, not_false_eq_true, dite_true,
      Option.value, Option.get_some] at h
    cases hf : Block.find? st.T x with
    | none =>
      rw [hf] at h
      cases h
    | some H =>
      obtain ⟨hHT, -⟩ := NoRaise.find?_mem hf
      rw [hf] at h
      have h' : (Except.ok ((st.blockOfImage B).ancestorEq H) : DC.DRE Bool) = .ok b := h
      cases h'
      simp only [Option.map_some, DecoupledConsensusModel.Protocol.head_covers,
        Block.toProof_find?_of_injOn st.T hinj x, hf, Option.map_some]
      rw [Store.blockOfImage_ancestorEq_of_mem st hinj hpar B hHT]

/-- On a key that is empty or the root of a tree block (`hk`), the spec's `head_covers` at the block
    standing for `B` answers, and its answer is `DecoupledConsensusModel.Protocol.head_covers` on
    the images. -/
theorem head_covers_eq {st : Store V} (hT : DistinctRoots st.T) (hpar : ParentClosed st.T)
    (B : DecoupledConsensusModel.Block V) {k : Option BlockId}
    (hk : ∀ x, k = some x → ∃ H ∈ st.T, H.root = x) :
    Protocol.head_covers st.T (st.blockOfImage B) k =
      .ok (DecoupledConsensusModel.Protocol.head_covers (st.T.image Block.toProof) B
        (k.map BlockId.toProof)) := by
  obtain ⟨b, hb⟩ := NoRaise.head_covers_ok hT (st.blockOfImage B) hk
  rw [hb, head_covers_eq_of_ok hT hpar B k b hb]

/-- Where the spec's `readyView` answers `E` at the block standing for `F`,
    `DecoupledConsensusModel.Protocol.readyView` on the grade view of the image is the image of `E`. -/
theorem readyView_toProof {st : Store V} (hok : StoreOk st) (F : DecoupledConsensusModel.Block V)
    (eta r : Round) (t : Time) (v : V) {E : Finset (Protocol.Token (Option BlockId))}
    (hE : Protocol.readyView st (st.blockOfImage F) eta r t v = .ok E) :
    DecoupledConsensusModel.Protocol.readyView st.toProof.toHealing.gradeView F eta r t v =
      E.map Protocol.Token.toProofEmb := by
  rw [readyView_eq hok] at hE
  cases hE
  unfold DecoupledConsensusModel.Protocol.readyView
  rw [vocabulary_interpretedInputs_toProof, image_token_map]

/-- Where the spec's `rawView` answers `R`, `DecoupledConsensusModel.Protocol.rawView` on the grade
    view of the image is the image of `R`. -/
theorem rawView_toProof {st : Store V} (hst : Stamped st) (eta r : Round) (t : Time) (v : V)
    {R : Finset (Protocol.Token (Option BlockId))}
    (hR : Protocol.rawView st eta r t v = .ok R) :
    DecoupledConsensusModel.Protocol.rawView st.toProof.toHealing.gradeView eta r t v =
      R.map Protocol.Token.toProofEmb := by
  rw [rawView_eq hst] at hR
  cases hR
  unfold DecoupledConsensusModel.Protocol.rawView
  rw [vocabulary_rawInputs_toProof, image_token_map]

omit [DecidableEq V] [Fintype V] in
/-- The spec's support test on a set of covering keys `C` is the `DecoupledConsensusModel` support
    test on the mapped tokens with the cover relation `cov`, when on the keys of `E` and `L`
    membership in `C` is `cov` at the mapped key (`hC`). -/
theorem supports_map {β : Type} (C : Finset (Option BlockId))
    (cov : Option DecoupledConsensusModel.BlockId → β → Prop)
    (E L R : Finset (Protocol.Token (Option BlockId))) (B : β)
    (hC : ∀ x ∈ E ∪ L, x.key ∈ C ↔ cov (x.key.map BlockId.toProof) B) :
    Protocol.Supports C E L R ↔
      DecoupledConsensusModel.Protocol.Supports cov
        (E.map Protocol.Token.toProofEmb) (L.map Protocol.Token.toProofEmb)
        (R.map Protocol.Token.toProofEmb) B := by
  have hround : ∀ x : Protocol.Token (Option BlockId), x.toProof.round = x.round := fun _ => rfl
  have hk : ∀ x : Protocol.Token (Option BlockId), x.toProof.key = x.key.map BlockId.toProof :=
    fun _ => rfl
  unfold Protocol.Supports DecoupledConsensusModel.Protocol.Supports
  simp only [Finset.forall_mem_map, Protocol.Token.coe_toProofEmb]
  simp only [Finset.mem_map, Protocol.Token.coe_toProofEmb, toProof_CleanFrom,
    exists_exists_and_eq_and, hround, hk]
  constructor
  · rintro ⟨u, hu, h1, h2, h3, h4⟩
    refine ⟨u, hu, h1, (hC u (Finset.mem_union_left _ hu)).mp h2, h3, fun x hx hlt =>
      (hC x (Finset.mem_union_right _ hx)).mp (h4 x hx hlt)⟩
  · rintro ⟨u, hu, h1, h2, h3, h4⟩
    refine ⟨u, hu, h1, (hC u (Finset.mem_union_left _ hu)).mpr h2, h3, fun x hx hlt =>
      (hC x (Finset.mem_union_right _ hx)).mpr (h4 x hx hlt)⟩

omit [DecidableEq V] [Fintype V] in
/-- The spec's opposition test on a set of covering keys `C` is the `DecoupledConsensusModel`
    opposition test on the mapped tokens with the cover relation `cov`, when on the keys of `L`
    membership in `C` is `cov` at the mapped key (`hC`). -/
theorem opposes_map {β : Type} (C : Finset (Option BlockId))
    (cov : Option DecoupledConsensusModel.BlockId → β → Prop)
    (E L R : Finset (Protocol.Token (Option BlockId))) (B : β)
    (hC : ∀ x ∈ L, x.key ∈ C ↔ cov (x.key.map BlockId.toProof) B) :
    Protocol.Opposes C E L R ↔
      DecoupledConsensusModel.Protocol.Opposes cov
        (E.map Protocol.Token.toProofEmb) (L.map Protocol.Token.toProofEmb)
        (R.map Protocol.Token.toProofEmb) B := by
  have hkey : ∀ x y : Protocol.Token (Option BlockId),
      x.toProof.key = y.toProof.key ↔ x.key = y.key := fun x y =>
    (Option.map_injective BlockId.toProof_injective).eq_iff
  have hround : ∀ x : Protocol.Token (Option BlockId), x.toProof.round = x.round := fun _ => rfl
  have hk : ∀ x : Protocol.Token (Option BlockId), x.toProof.key = x.key.map BlockId.toProof :=
    fun _ => rfl
  unfold Protocol.Opposes DecoupledConsensusModel.Protocol.Opposes
  simp only [Finset.forall_mem_map, Protocol.Token.coe_toProofEmb]
  simp only [Finset.mem_map, Protocol.Token.coe_toProofEmb, exists_exists_and_eq_and, hround]
  constructor
  · rintro (⟨x, hx, h1, h2⟩ | ⟨x, hx, y, hy, h1, h2, h3⟩)
    · exact Or.inl ⟨x, hx, h1, fun h => h2 ((hC x hx).mpr h)⟩
    · exact Or.inr ⟨x, hx, y, hy, h1, h2, fun h => h3 ((hkey x y).mp h)⟩
  · rintro (⟨x, hx, h1, h2⟩ | ⟨x, hx, y, hy, h1, h2, h3⟩)
    · exact Or.inl ⟨x, hx, h1, fun h => h2 ((hC x hx).mp h)⟩
    · exact Or.inr ⟨x, hx, y, hy, h1, h2, fun h => h3 ((hkey x y).mpr h)⟩

/-- On a store meeting `StoreOk`, the spec's `positive` at the blocks standing for `F` and `B`
    answers `DecoupledConsensusModel.Protocol.positive` on the grade view of the image. -/
theorem positive_eq {st : Store V} (hok : StoreOk st) (F : DecoupledConsensusModel.Block V)
    (eta r : Round) (t_0 t_1 : Time) (v : V) (B : DecoupledConsensusModel.Block V) :
    Protocol.positive st (st.blockOfImage F) eta r t_0 t_1 v (st.blockOfImage B) =
      .ok (DecoupledConsensusModel.Protocol.positive st.toProof.toHealing.gradeView F eta r t_0 t_1
        v B) := by
  obtain ⟨hst, hT, hpar, hFT⟩ := hok
  obtain ⟨E, hE, hEk⟩ := NoRaise.readyView_post hT hst (st.blockOfImage F) eta r t_0 v
  obtain ⟨L, hL, hLk⟩ := NoRaise.readyView_post hT hst (st.blockOfImage F) eta r t_1 v
  obtain ⟨R, hR⟩ := NoRaise.rawView_ok hst eta r t_1 v
  have hkeys : ∀ k ∈ (E ∪ L).image (fun u => u.key), ∀ x, k = some x → ∃ H ∈ st.T, H.root = x := by
    intro k hk x hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hk
    exact (Finset.mem_union.mp hu).elim (fun h => hEk u h x hx) (fun h => hLk u h x hx)
  obtain ⟨w, hw⟩ := NoRaise.filterM_ok (fun k => Protocol.head_covers st.T (st.blockOfImage B) k)
    ((E ∪ L).image (fun u => u.key)) (fun k hk => ⟨_, head_covers_eq hT hpar B (hkeys k hk)⟩)
  have hw' := filterM_eq_filter _ (fun k => DecoupledConsensusModel.Protocol.head_covers
    (st.T.image Block.toProof) B (k.map BlockId.toProof) = true) _ (fun k _ b hb => by
      rw [head_covers_eq_of_ok hT hpar B k b hb]) w hw
  have hS : (E ∪ L).map' (fun u => u.key) = (E ∪ L).image (fun u => u.key) := rfl
  simp only [Protocol.positive, hE, hL, hR, NoRaise.DRE.bind_ok, hS, hw]
  unfold DecoupledConsensusModel.Protocol.positive
  rw [readyView_toProof ⟨hst, hT, hpar, hFT⟩ F eta r t_0 v hE,
    readyView_toProof ⟨hst, hT, hpar, hFT⟩ F eta r t_1 v hL, rawView_toProof hst eta r t_1 v hR]
  refine congrArg Except.ok (decide_eq_decide.mpr ?_)
  subst hw'
  refine supports_map _ _ E L R B (fun x hx => ?_)
  simp only [Finset.mem_filter, Finset.mem_image, DecoupledConsensusModel.Protocol.localCovers,
    toProof_gv_T]
  exact ⟨fun h => h.2, fun h => ⟨⟨x, hx, rfl⟩, h⟩⟩

/-- On a store meeting `StoreOk`, the spec's `opposing` at the blocks standing for `F` and `B`
    answers `DecoupledConsensusModel.Protocol.opposing` on the grade view of the image. -/
theorem opposing_eq {st : Store V} (hok : StoreOk st) (F : DecoupledConsensusModel.Block V)
    (eta r : Round) (t_0 t_1 : Time) (v : V) (B : DecoupledConsensusModel.Block V) :
    Protocol.opposing st (st.blockOfImage F) eta r t_0 t_1 v (st.blockOfImage B) =
      .ok (DecoupledConsensusModel.Protocol.opposing st.toProof.toHealing.gradeView F eta r t_0 t_1
        v B) := by
  obtain ⟨hst, hT, hpar, hFT⟩ := hok
  obtain ⟨E, hE, -⟩ := NoRaise.readyView_post hT hst (st.blockOfImage F) eta r t_0 v
  obtain ⟨L, hL, hLk⟩ := NoRaise.readyView_post hT hst (st.blockOfImage F) eta r t_1 v
  obtain ⟨R, hR⟩ := NoRaise.rawView_ok hst eta r t_1 v
  have hkeys : ∀ k ∈ L.image (fun u => u.key), ∀ x, k = some x → ∃ H ∈ st.T, H.root = x := by
    intro k hk x hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hk
    exact hLk u hu x hx
  obtain ⟨w, hw⟩ := NoRaise.filterM_ok (fun k => Protocol.head_covers st.T (st.blockOfImage B) k)
    (L.image (fun u => u.key)) (fun k hk => ⟨_, head_covers_eq hT hpar B (hkeys k hk)⟩)
  have hw' := filterM_eq_filter _ (fun k => DecoupledConsensusModel.Protocol.head_covers
    (st.T.image Block.toProof) B (k.map BlockId.toProof) = true) _ (fun k _ b hb => by
      rw [head_covers_eq_of_ok hT hpar B k b hb]) w hw
  have hS : L.map' (fun u => u.key) = L.image (fun u => u.key) := rfl
  simp only [Protocol.opposing, hE, hL, hR, NoRaise.DRE.bind_ok, hS, hw]
  unfold DecoupledConsensusModel.Protocol.opposing
  rw [readyView_toProof ⟨hst, hT, hpar, hFT⟩ F eta r t_0 v hE,
    readyView_toProof ⟨hst, hT, hpar, hFT⟩ F eta r t_1 v hL, rawView_toProof hst eta r t_1 v hR]
  refine congrArg Except.ok (decide_eq_decide.mpr ?_)
  subst hw'
  refine opposes_map _ _ E L R B (fun x hx => ?_)
  simp only [Finset.mem_filter, Finset.mem_image, DecoupledConsensusModel.Protocol.localCovers,
    toProof_gv_T]
  exact ⟨fun h => h.2, fun h => ⟨⟨x, hx, rfl⟩, h⟩⟩

/-- On a store meeting `StoreOk`, the spec's `gradeBool` at `Provisional.toSpec E` and at the blocks
    standing for `F` and `B` answers `DecoupledConsensusModel.Protocol.gradeBool` on the grade view
    of the image. -/
theorem gradeBool_eq {st : Store V} (hok : StoreOk st) (E : DecoupledConsensusModel.Env V)
    (F : DecoupledConsensusModel.Block V) (eta r : Round) (t_0 t_1 : Time)
    (B : DecoupledConsensusModel.Block V) :
    Protocol.gradeBool (Provisional.toSpec E) st (st.blockOfImage F) eta r t_0 t_1
        (st.blockOfImage B) =
      .ok (DecoupledConsensusModel.Protocol.gradeBool E st.toProof.toHealing.gradeView F eta r t_0
        t_1 B) := by
  obtain ⟨w₁, hw₁⟩ := NoRaise.filterM_ok
    (fun v => Protocol.opposing st (st.blockOfImage F) eta r t_0 t_1 v (st.blockOfImage B))
    Finset.univ (fun v _ => ⟨_, opposing_eq hok F eta r t_0 t_1 v B⟩)
  obtain ⟨w₂, hw₂⟩ := NoRaise.filterM_ok
    (fun v => Protocol.positive st (st.blockOfImage F) eta r t_0 t_1 v (st.blockOfImage B))
    Finset.univ (fun v _ => ⟨_, positive_eq hok F eta r t_0 t_1 v B⟩)
  have h₁ := filterM_eq_filter _ (fun v => DecoupledConsensusModel.Protocol.opposing
    st.toProof.toHealing.gradeView F eta r t_0 t_1 v B = true) _ (fun v _ b hb => by
      rw [opposing_eq hok] at hb
      cases Except.ok.inj hb
      exact Iff.rfl) w₁ hw₁
  have h₂ := filterM_eq_filter _ (fun v => DecoupledConsensusModel.Protocol.positive
    st.toProof.toHealing.gradeView F eta r t_0 t_1 v B = true) _ (fun v _ b hb => by
      rw [positive_eq hok] at hb
      cases Except.ok.inj hb
      exact Iff.rfl) w₂ hw₂
  simp only [Protocol.gradeBool, hw₁, hw₂, NoRaise.DRE.bind_ok]
  subst h₁ h₂
  unfold DecoupledConsensusModel.Protocol.gradeBool
  show (Except.ok _ : DC.DRE Bool) = _
  exact congrArg Except.ok (decide_eq_decide.mpr (by simp [Provisional.toSpec_weightOf]))

/-- On a store meeting `StoreOk`, the image of the spec's `freezeRoot` at the block standing for `F`
    is `DecoupledConsensusModel.Protocol.freezeRoot` on the grade view of the image. -/
theorem freezeRoot_eq {st : Store V} (hok : StoreOk st) (E : DecoupledConsensusModel.Env V)
    (F : DecoupledConsensusModel.Block V) (eta r : Round) (t_0 t_1 : Time) :
    Except.map (Option.map Block.toProof)
        (Protocol.freezeRoot (Provisional.toSpec E) st (st.blockOfImage F) eta r t_0 t_1) =
      .ok (DecoupledConsensusModel.Protocol.freezeRoot E st.toProof.toHealing.gradeView F eta r t_0
        t_1) := by
  have hinj := hok.2.1.injOn_toProof
  have hgb : ∀ B ∈ st.T, Protocol.gradeBool (Provisional.toSpec E) st (st.blockOfImage F) eta r
      t_0 t_1 B = .ok (DecoupledConsensusModel.Protocol.gradeBool E st.toProof.toHealing.gradeView
        F eta r t_0 t_1 B.toProof) := fun B hB => by
    have h := gradeBool_eq hok E F eta r t_0 t_1 B.toProof
    rwa [Store.blockOfImage_toProof_of_injOn st hinj hB] at h
  obtain ⟨w, hw⟩ := NoRaise.filterM_ok
    (fun B => Protocol.gradeBool (Provisional.toSpec E) st (st.blockOfImage F) eta r t_0 t_1 B)
    st.T (fun B hB => ⟨_, hgb B hB⟩)
  have hw' := filterM_eq_filter _ (fun B => DecoupledConsensusModel.Protocol.gradeBool E
    st.toProof.toHealing.gradeView F eta r t_0 t_1 B.toProof = true) _ (fun B hB b hb => by
      rw [hgb B hB] at hb
      cases Except.ok.inj hb
      exact Iff.rfl) w hw
  simp only [Protocol.freezeRoot, hw, NoRaise.DRE.bind_ok]
  subst hw'
  unfold DecoupledConsensusModel.Protocol.freezeRoot
  rw [toProof_gv_T, Finset.filter_image, Block.toProof_deepest?_of_injOn _
    (hinj.mono (fun B hB => Finset.mem_coe.mpr (Finset.mem_filter.mp hB).1))]
  rfl

/-! ## The anchor and the grade-2 candidate: `anchor`, `grade2Block` -/

omit [Fintype V] in
/-- Every block of `get_filtered_block_tree st` is a block of `st.T`. -/
theorem filtered_subset (st : Store V) : Protocol.get_filtered_block_tree st ⊆ st.T := by
  intro B hB
  simp only [Protocol.get_filtered_block_tree, Protocol.get_filtered_block_tree_from,
    Protocol.viable_tree, Protocol.finalized_descendants, Id.run, pure, Finset.mem_filter] at hB
  exact hB.1.1.1

/-!
## The grade reads through a contract: `read`, `confirmationSG`, `stableRoot` and their frame forms

A contract-taking member reads its saved grades through the tree, brought to the round it reads, and
filled.
-/

omit [Fintype V] in
/-- The loop of the spec's `deepest_compatible_ancestor`, started at the block standing for `g` and
    testing against the block standing for `F`, given at least `g.depth + 1` steps (`hl`), ends at
    the block standing for `DecoupledConsensusModel.Protocol.clipGrade g F`. -/
theorem dca_loop_blockOfImage (st : Store V)
    (hinj : Set.InjOn (Block.toProof (V := V)) (↑st.T : Set (Block V)))
    (hpar : ParentClosed st.T) (F : DecoupledConsensusModel.Block V) (l : List Nat)
    (g : DecoupledConsensusModel.Block V) (hl : g.depth + 1 ≤ l.length) :
    (forIn (m := Id) l ((none : Option (Block V)), st.blockOfImage g)
        fun _ (s : Option (Block V) × Block V) =>
        if s.2.compatible (st.blockOfImage F) = true then pure (ForInStep.done (some s.2, s.2))
        else pure (ForInStep.yield (none, s.2.parent))) =
      (some (st.blockOfImage (DecoupledConsensusModel.Protocol.clipGrade g F)),
        st.blockOfImage (DecoupledConsensusModel.Protocol.clipGrade g F)) := by
  induction l generalizing g with
  | nil => simp at hl
  | cons x l ih =>
    rw [List.forIn_cons]
    have hc := Store.blockOfImage_compatible st hinj hpar g F
    cases g with
    | genesis =>
      have hg : (st.blockOfImage .genesis : Block V) = .genesis := rfl
      have hgc : (st.blockOfImage (.genesis : DecoupledConsensusModel.Block V)).compatible
          (st.blockOfImage F) = true := by
        rw [hg]; simp [Block.compatible, Block.genesis_ancestorEq]
      simp only [hgc, if_true]
      rw [DecoupledConsensusModel.Protocol.clipGrade]
      rfl
    | node p s r votes support ats proposer =>
      rw [hc]
      by_cases h : DecoupledConsensusModel.Block.compatible
          (.node p s r votes support ats proposer) F = true
      · simp only [h, if_true]
        rw [DecoupledConsensusModel.Protocol.clipGrade, if_pos h]
        rfl
      · have hl' : p.depth + 1 ≤ l.length := by
          simp [DecoupledConsensusModel.Block.depth] at hl; omega
        have hp : (st.blockOfImage (.node p s r votes support ats proposer)).parent =
            st.blockOfImage p := by
          rw [← Store.blockOfImage_parent st hinj hpar]
          simp only [DecoupledConsensusModel.Block.parent]
        simp only [h, Bool.false_eq_true, if_false, hp]
        show forIn l (none, st.blockOfImage p) _ = _
        rw [ih p hl', DecoupledConsensusModel.Protocol.clipGrade, if_neg h]

omit [Fintype V] in
/-- The spec's deepest compatible ancestor of the block standing for `g`, against the block standing
    for `F`, is the block standing for `DecoupledConsensusModel.Protocol.clipGrade g F`. -/
theorem dca_blockOfImage (st : Store V)
    (hinj : Set.InjOn (Block.toProof (V := V)) (↑st.T : Set (Block V)))
    (hpar : ParentClosed st.T) (g F : DecoupledConsensusModel.Block V) :
    Protocol.deepest_compatible_ancestor (st.blockOfImage g) (st.blockOfImage F) =
      st.blockOfImage (DecoupledConsensusModel.Protocol.clipGrade g F) := by
  unfold Protocol.deepest_compatible_ancestor
  simp only [Id.run]
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  rw [dca_loop_blockOfImage st hinj hpar F _ g (by
    simp [Std.Legacy.Range.size, ← Block.toProof_depth, Store.toProof_blockOfImage])]
  rfl

/-- The frame `U` as round grades on the store `st`: each of its three results read through
    `gradeResultOfImage`. -/
def frameOfImage (st : Store V) (U : DecoupledConsensusModel.Protocol.Frame V) : RoundGrades V :=
  ⟨gradeResultOfImage st U.g0, gradeResultOfImage st U.g1, gradeResultOfImage st U.g2⟩

omit [Fintype V] in
/-- Filling the result standing for `u` gives `u`'s block read on `st`, or no block. -/
theorem fill_gradeResultOfImage (st : Store V) (u : Option (Option (DecoupledConsensusModel.Block V))) :
    fillResult (gradeResultOfImage st u) = .computed ((u.bind id).map st.blockOfImage) := by
  rcases u with _ | _ | X <;> rfl

omit [Fintype V] in
/-- Making the result `g` read through the tree compatible with the store's finalized block is
    reading through the tree the clip of the image of `g`. -/
theorem clip_resultOfImage (st : Store V)
    (hinj : Set.InjOn (Block.toProof (V := V)) (↑st.T : Set (Block V)))
    (hpar : ParentClosed st.T) (hF : st.F ∈ st.T) (g : GradeResult V) :
    Protocol.make_result_compatible_with st.F (st.resultOfImage g) =
      gradeResultOfImage st
        (DecoupledConsensusModel.Protocol.clipResult st.F.toProof g.toProof) := by
  rcases g with _ | _ | X
  · simp [Store.resultOfImage, gradeResultOfImage,
      DecoupledConsensusModel.Protocol.clipResult, Protocol.make_result_compatible_with, Id.run]
    rfl
  · simp [Store.resultOfImage, gradeResultOfImage,
      DecoupledConsensusModel.Protocol.clipResult, Protocol.make_result_compatible_with,
      GradeResult.block, Id.run]
    rfl
  · have hFb : st.blockOfImage st.F.toProof = st.F := Store.blockOfImage_toProof_of_injOn st hinj hF
    show GradeResult.computed (some (Protocol.deepest_compatible_ancestor
      (st.blockOfImage X.toProof) st.F)) = _
    conv_lhs => rw [← hFb]
    rw [dca_blockOfImage st hinj hpar]
    simp [gradeResultOfImage, DecoupledConsensusModel.Protocol.clipResult]

omit [Fintype V] in
/-- The image of the result standing for `u` is `u`. -/
@[simp] theorem toProof_gradeResultOfImage (st : Store V)
    (u : Option (Option (DecoupledConsensusModel.Block V))) :
    (gradeResultOfImage st u).toProof = u := by
  rcases u with _ | _ | X <;> simp [gradeResultOfImage]

omit [Fintype V] in
/-- The image of the round grades standing for the frame `U` is `U`. -/
@[simp] theorem toProof_frameOfImage (st : Store V) (U : DecoupledConsensusModel.Protocol.Frame V) :
    (frameOfImage st U).toProof = U := by
  rcases U with ⟨u0, u1, u2⟩
  simp [frameOfImage, RoundGrades.toProof]

omit [Fintype V] in
/-- The result standing for `u`, read through the tree, is unchanged. -/
theorem resultOfImage_gradeResultOfImage (st : Store V)
    (u : Option (Option (DecoupledConsensusModel.Block V))) :
    st.resultOfImage (gradeResultOfImage st u) = gradeResultOfImage st u := by
  rcases u with _ | _ | X <;> simp [gradeResultOfImage, Store.resultOfImage]

omit [Fintype V] in
/-- On a store whose tree meets `hinj`, `hpar` and `hF`, `Member.readFrame c st r` is
    `frameOfImage st` of `DecoupledConsensusModel.Protocol.readFrame` of `c.toProof` at round `r` on
    the image of `st`. -/
theorem readFrame_eq_frameOfImage (st : Store V)
    (hinj : Set.InjOn (Block.toProof (V := V)) (↑st.T : Set (Block V)))
    (hpar : ParentClosed st.T) (hF : st.F ∈ st.T) (c : SavedGrades V) (r : Round) :
    Member.readFrame c st r =
      frameOfImage st
        (DecoupledConsensusModel.Protocol.readFrame c.toProof st.toProof.toHealing r) := by
  show Protocol.make_round_grades_compatible_with st.F
      (Protocol.saved_round_grades (st.contractOfImage c) r) = _
  rw [Store.saved_round_grades_contractOfImage]
  unfold DecoupledConsensusModel.Protocol.readFrame
  rw [toProof_cacheAtRound]
  simp only [Protocol.make_round_grades_compatible_with, frameOfImage,
    Store.roundGradesOfImage, RoundGrades.toProof, DecoupledConsensusModel.Protocol.clipFrame,
    toProof_fg_F]
  rw [clip_resultOfImage st hinj hpar hF, clip_resultOfImage st hinj hpar hF,
    clip_resultOfImage st hinj hpar hF]

omit [Fintype V] in
/-- On a store whose tree meets `hinj`, `hpar` and `hF`, the image of the member `readFrame` is
    `DecoupledConsensusModel.Protocol.readFrame` of the images. -/
theorem toProof_readFrame_ofImage (st : Store V)
    (hinj : Set.InjOn (Block.toProof (V := V)) (↑st.T : Set (Block V)))
    (hpar : ParentClosed st.T) (hF : st.F ∈ st.T) (c : SavedGrades V) (r : Round) :
    (Member.readFrame c st r).toProof =
      DecoupledConsensusModel.Protocol.readFrame c.toProof st.toProof.toHealing r := by
  rw [readFrame_eq_frameOfImage st hinj hpar hF, toProof_frameOfImage]

omit [Fintype V] in
/-- The round grades standing for the frame `U`, read through the tree, are unchanged. -/
theorem roundGradesOfImage_frameOfImage (st : Store V)
    (U : DecoupledConsensusModel.Protocol.Frame V) :
    st.roundGradesOfImage (frameOfImage st U) = frameOfImage st U := by
  simp only [Store.roundGradesOfImage, frameOfImage, resultOfImage_gradeResultOfImage]

omit [Fintype V] in
/-- Filling, then making compatible with `F`, is making compatible with `F`, then filling. -/
theorem clip_fillResult (F : Block V) (g : GradeResult V) :
    Protocol.make_result_compatible_with F (fillResult g) =
      fillResult (Protocol.make_result_compatible_with F g) := by
  rcases g with _ | _ | X <;>
    simp [fillResult, Protocol.make_result_compatible_with, Id.run] <;> rfl

omit [Fintype V] in
/-- The round grades a contract-taking member reads of round `r` through `c` are the frame
    `readFrame c st r` with its pending results read as computed with no block. -/
theorem round_grades_eq_fillRound_readFrame (st : Store V) (c : SavedGrades V) (r : Round) :
    Protocol.round_grades
        { st with saved_grades := fill (Protocol.advance_to_round (st.contractOfImage c) r) } r =
      fillRound (Member.readFrame c st r) := by
  show Protocol.make_round_grades_compatible_with st.F
      (Protocol.saved_round_grades (fill (Protocol.advance_to_round (st.contractOfImage c) r)) r) =
    fillRound (Protocol.make_round_grades_compatible_with st.F
      (Protocol.saved_round_grades (st.contractOfImage c) r))
  rw [saved_round_grades_fill_advance]
  simp only [Protocol.make_round_grades_compatible_with, fillRound, clip_fillResult]

omit [Fintype V] in
/-- `round_grades_eq_fillRound_readFrame` on the store read through its tree, on a store meeting
    `StoreOk`. -/
theorem round_grades_ofImage_eq_fillRound_readFrame {st : Store V} (hok : StoreOk st)
    (c : SavedGrades V) (r : Round) :
    Protocol.round_grades
        { Store.ofImage st with
          saved_grades := fill (Protocol.advance_to_round (st.contractOfImage c) r) } r =
      fillRound (Member.readFrame c st r) := by
  show Protocol.make_round_grades_compatible_with (Store.ofImage st).F
      (Protocol.saved_round_grades (fill (Protocol.advance_to_round (st.contractOfImage c) r)) r) = _
  rw [Store.ofImage_F_of_storeOk hok]
  exact round_grades_eq_fillRound_readFrame st c r

omit [Fintype V] in
/-- On a store whose tree meets `hinj`, `hpar` and `hF`, each result of `readFrame c st r`, mapped
    and read again on `st`, is unchanged. -/
theorem gradeResultOfImage_readFrame (st : Store V)
    (hinj : Set.InjOn (Block.toProof (V := V)) (↑st.T : Set (Block V)))
    (hpar : ParentClosed st.T) (hF : st.F ∈ st.T) (c : SavedGrades V) (r : Round) :
    gradeResultOfImage st (Member.readFrame c st r).g0.toProof = (Member.readFrame c st r).g0 ∧
    gradeResultOfImage st (Member.readFrame c st r).g1.toProof = (Member.readFrame c st r).g1 ∧
    gradeResultOfImage st (Member.readFrame c st r).g2.toProof = (Member.readFrame c st r).g2 := by
  rw [readFrame_eq_frameOfImage st hinj hpar hF]
  simp only [frameOfImage, toProof_gradeResultOfImage, and_self]

end SpecDraftRecord.GradesImages

namespace SpecDraftRecord.GradesImages

open Spec
open SpecDraftRecord.ForkChoiceGrades
open DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-- The member `rawInputs` of `Model.specDraft` at a store `st` of the instance is the member
    `rawInputs` of `Model.vocabulary` at the grade view of the image of `st`. -/
theorem specDraft_rawInputs_eq (st : OkStore V) (eta r : Round) (t : Time) (v : V) :
    (Model.specDraft (V := V)).rawInputs st eta r t v =
      (Model.vocabulary (V := V)).rawInputs st.val.toProof.toHealing.gradeView eta r t v := by
  show successOutcomes (Except.map (fun votes => votes.map Protocol.SGVote.toProofEmb)
    (Protocol.rawInputs st.val eta r t v)) =
      pure (DecoupledConsensusModel.Protocol.rawInputs _ eta r t v)
  rw [rawInputs_eq st.property.1, vocabulary_rawInputs_toProof]
  rfl

/-- The member `bodyReady` of `Model.specDraft` at a store `st` of the instance is the member
    `bodyReady` of `Model.vocabulary` at the grade view of the image of `st`. -/
theorem specDraft_bodyReady_eq (st : OkStore V) (F : DecoupledConsensusModel.Block V) (t : Time)
    (u : DecoupledConsensusModel.Protocol.SGVote V) :
    (Model.specDraft (V := V)).bodyReady st F t u =
      (Model.vocabulary (V := V)).bodyReady st.val.toProof.toHealing.gradeView F t u := by
  show successOutcomes (Protocol.bodyReady st.val (st.val.blockOfImage F) t
    (Protocol.SGVote.toSpec u)) = pure (DecoupledConsensusModel.Protocol.bodyReady _ F t u)
  rw [bodyReady_eq st.property]
  rfl

/-- The member `interpretedInputs` of `Model.specDraft` at a store `st` of the instance is the
    member `interpretedInputs` of `Model.vocabulary` at the grade view of the image of `st`. -/
theorem specDraft_interpretedInputs_eq (st : OkStore V) (F : DecoupledConsensusModel.Block V)
    (eta r : Round) (t : Time) (v : V) :
    (Model.specDraft (V := V)).interpretedInputs st F eta r t v =
      (Model.vocabulary (V := V)).interpretedInputs st.val.toProof.toHealing.gradeView F eta r t v := by
  show successOutcomes (Except.map (fun votes => votes.map Protocol.SGVote.toProofEmb)
    (Protocol.interpretedInputs st.val (st.val.blockOfImage F) eta r t v)) =
      pure (DecoupledConsensusModel.Protocol.interpretedInputs _ F eta r t v)
  rw [interpretedInputs_eq st.property, vocabulary_interpretedInputs_toProof]
  rfl

/-- The member `rawView` of `Model.specDraft` at a store `st` of the instance is the member
    `rawView` of `Model.vocabulary` at the grade view of the image of `st`. -/
theorem specDraft_rawView_eq (st : OkStore V) (eta r : Round) (t : Time) (v : V) :
    (Model.specDraft (V := V)).rawView st eta r t v =
      (Model.vocabulary (V := V)).rawView st.val.toProof.toHealing.gradeView eta r t v := by
  have h1 : (Model.specDraft (V := V)).rawView st eta r t v =
      successOutcomes (Except.map (fun tokens => tokens.map Protocol.Token.toProofEmb)
        (Protocol.rawView st.val eta r t v)) := rfl
  have h2 : (Model.vocabulary (V := V)).rawView st.val.toProof.toHealing.gradeView eta r t v =
      pure (DecoupledConsensusModel.Protocol.rawView st.val.toProof.toHealing.gradeView eta r t
        v) := rfl
  rw [h1, h2, rawView_eq st.property.1]
  unfold DecoupledConsensusModel.Protocol.rawView
  rw [vocabulary_rawInputs_toProof, image_token_map]
  rfl

/-- The member `readyView` of `Model.specDraft` at a store `st` of the instance is the member
    `readyView` of `Model.vocabulary` at the grade view of the image of `st`. -/
theorem specDraft_readyView_eq (st : OkStore V) (F : DecoupledConsensusModel.Block V)
    (eta r : Round) (t : Time) (v : V) :
    (Model.specDraft (V := V)).readyView st F eta r t v =
      (Model.vocabulary (V := V)).readyView st.val.toProof.toHealing.gradeView F eta r t v := by
  have h1 : (Model.specDraft (V := V)).readyView st F eta r t v =
      successOutcomes (Except.map (fun tokens => tokens.map Protocol.Token.toProofEmb)
        (Protocol.readyView st.val (st.val.blockOfImage F) eta r t v)) := rfl
  have h2 : (Model.vocabulary (V := V)).readyView st.val.toProof.toHealing.gradeView F eta r t v =
      pure (DecoupledConsensusModel.Protocol.readyView st.val.toProof.toHealing.gradeView F eta r
        t v) := rfl
  rw [h1, h2, readyView_eq st.property]
  unfold DecoupledConsensusModel.Protocol.readyView
  rw [vocabulary_interpretedInputs_toProof, image_token_map]
  rfl

/-- The member `localCovers` of `Model.specDraft` at a store `st` of the instance is the member
    `localCovers` of `Model.vocabulary` at the grade view of the image of `st`, at every key. -/
theorem specDraft_localCovers_eq (st : OkStore V) (key : Option DecoupledConsensusModel.BlockId)
    (B : DecoupledConsensusModel.Block V) :
    (Model.specDraft (V := V)).localCovers st key B =
      (Model.vocabulary (V := V)).localCovers st.val.toProof.toHealing.gradeView key B := by
  obtain ⟨-, hT, hpar, -⟩ := st.property
  show successOutcomes (orVocabulary (Protocol.head_covers st.val.T (st.val.blockOfImage B)
    (key.map BlockId.toSpec)) (DecoupledConsensusModel.Protocol.localCovers _ key B)) =
      pure (DecoupledConsensusModel.Protocol.localCovers _ key B)
  cases h : Protocol.head_covers st.val.T (st.val.blockOfImage B) (key.map BlockId.toSpec) with
  | error e => rfl
  | ok b =>
    have hb := head_covers_eq_of_ok hT hpar B _ b h
    rw [Option.map_map, show BlockId.toProof ∘ BlockId.toSpec = id from
      funext BlockId.toProof_toSpec, Option.map_id] at hb
    dsimp only [id] at hb
    subst hb
    simp only [DecoupledConsensusModel.Protocol.localCovers, toProof_gv_T]
    rfl

/-- The member `positive` of `Model.specDraft` at a store `st` of the instance is the member
    `positive` of `Model.vocabulary` at the grade view of the image of `st`. -/
theorem specDraft_positive_eq (st : OkStore V) (F : DecoupledConsensusModel.Block V)
    (eta r : Round) (t_0 t_1 : Time) (v : V) (B : DecoupledConsensusModel.Block V) :
    (Model.specDraft (V := V)).positive st F eta r t_0 t_1 v B =
      (Model.vocabulary (V := V)).positive st.val.toProof.toHealing.gradeView F eta r t_0 t_1 v B := by
  show successOutcomes (Protocol.positive st.val (st.val.blockOfImage F) eta r t_0 t_1 v
    (st.val.blockOfImage B)) = pure (DecoupledConsensusModel.Protocol.positive _ F eta r t_0 t_1 v B)
  rw [positive_eq st.property]
  rfl

/-- The member `opposing` of `Model.specDraft` at a store `st` of the instance is the member
    `opposing` of `Model.vocabulary` at the grade view of the image of `st`. -/
theorem specDraft_opposing_eq (st : OkStore V) (F : DecoupledConsensusModel.Block V)
    (eta r : Round) (t_0 t_1 : Time) (v : V) (B : DecoupledConsensusModel.Block V) :
    (Model.specDraft (V := V)).opposing st F eta r t_0 t_1 v B =
      (Model.vocabulary (V := V)).opposing st.val.toProof.toHealing.gradeView F eta r t_0 t_1 v B := by
  show successOutcomes (Protocol.opposing st.val (st.val.blockOfImage F) eta r t_0 t_1 v
    (st.val.blockOfImage B)) = pure (DecoupledConsensusModel.Protocol.opposing _ F eta r t_0 t_1 v B)
  rw [opposing_eq st.property]
  rfl

/-- The member `gradeBool` of `Model.specDraft` at a store `st` of the instance is the member
    `gradeBool` of `Model.vocabulary` at the grade view of the image of `st`. -/
theorem specDraft_gradeBool_eq (E : DecoupledConsensusModel.Env V) (st : OkStore V)
    (F : DecoupledConsensusModel.Block V) (eta r : Round) (t_0 t_1 : Time)
    (B : DecoupledConsensusModel.Block V) :
    (Model.specDraft (V := V)).gradeBool E st F eta r t_0 t_1 B =
      (Model.vocabulary (V := V)).gradeBool E st.val.toProof.toHealing.gradeView F eta r t_0 t_1 B := by
  show successOutcomes (Protocol.gradeBool (Provisional.toSpec E) st.val (st.val.blockOfImage F)
    eta r t_0 t_1 (st.val.blockOfImage B)) =
      pure (DecoupledConsensusModel.Protocol.gradeBool E _ F eta r t_0 t_1 B)
  rw [gradeBool_eq st.property]
  rfl

/-- The member `freezeRoot` of `Model.specDraft` at a store `st` of the instance is the member
    `freezeRoot` of `Model.vocabulary` at the grade view of the image of `st`. -/
theorem specDraft_freezeRoot_eq (E : DecoupledConsensusModel.Env V) (st : OkStore V)
    (F : DecoupledConsensusModel.Block V) (eta r : Round) (t_0 t_1 : Time) :
    (Model.specDraft (V := V)).freezeRoot E st F eta r t_0 t_1 =
      (Model.vocabulary (V := V)).freezeRoot E st.val.toProof.toHealing.gradeView F eta r t_0 t_1 := by
  show successOutcomes (Except.map (Option.map Block.toProof)
    (Protocol.freezeRoot (Provisional.toSpec E) st.val (st.val.blockOfImage F) eta r t_0 t_1)) =
      pure (DecoupledConsensusModel.Protocol.freezeRoot E _ F eta r t_0 t_1)
  rw [freezeRoot_eq st.property]
  rfl

end SpecDraftRecord.GradesImages

namespace SpecDraftRecord.GradesImages

open Spec
open DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V]

/-- On a store of the instance, when `DecoupledConsensusModel.Protocol.deepest_clear` from the
    anchor of `grades` along the chain of the image of the store's confirmed block finds `D`, the
    member `currentSGVote` answers `D`. -/
theorem member_currentSGVote_of_deepest_clear (st : OkStore V)
    (grades : DecoupledConsensusModel.Protocol.GradeRead V) {D : DecoupledConsensusModel.Block V}
    (h : DecoupledConsensusModel.Protocol.deepest_clear (some grades.anchor)
      st.val.live_confirmed.toProof grades.clear = some D) :
    Member.currentSGVote st.val grades = D := by
  obtain ⟨-, hT, hpar, -⟩ := st.property
  have e := Protocol.deepest_clear_blockOfImage_image st.val hT.injOn_toProof hpar
    grades.anchor st.val.live_confirmed.toProof grades.clear
  rw [h] at e
  obtain ⟨D', hD', rfl⟩ := Option.map_eq_some_iff.mp e
  unfold Member.currentSGVote
  simp only [Protocol.currentSGVote, Id.run, ForkChoiceGrades.gradeReadOfImage]
  rw [show (Store.ofImage st.val).live_confirmed =
    st.val.blockOfImage st.val.live_confirmed.toProof from rfl]
  simp [hD', Option.value]
  rfl

end SpecDraftRecord.GradesImages
