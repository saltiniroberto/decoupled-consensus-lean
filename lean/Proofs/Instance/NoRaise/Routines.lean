import Proofs.Instance.NoRaise.Kit
import Proofs.Instance.NoRaise.Predicates

/-!
# The no-raise library over the spec

For each raising routine the tick reaches, a lemma `<routine>_ok` saying that the routine answers
under the conditions it needs: `DistinctRoots` for a lookup by root, `Stamped` (or one clause of it)
for a read of a stamp, and a saved grade result that is not `pending` for a read of the saved
grades. The four duties are `propose_block_ok`, `goldfish_vote_ok`, `update_confirmation_ok` and
`attest_ok`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Spec Spec.Protocol
open scoped DC
open DC (DRE)

namespace SpecDraftRecord.NoRaise

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Lookups by root -/

/-- Under distinct roots, at most one block of the tree has a given root. -/
theorem card_root_le_one {T : Finset (Block V)} (hT : DistinctRoots T) (r : BlockId) :
    ({B ∈ T | B.root = r}).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [Finset.mem_filter] at ha hb
  exact hT a ha.1 b hb.1 (ha.2.trans hb.2.symm)

/-- Under distinct roots, `blockWithRoot T r` answers `Block.find? T r`. -/
theorem blockWithRoot_eq {T : Finset (Block V)} (hT : DistinctRoots T) (r : BlockId) :
    blockWithRoot T r = .ok (Block.find? T r) := by
  simp only [blockWithRoot]
  rw [if_neg (by have := card_root_le_one hT r; omega)]
  rfl

/-- If `Block.find? T r` is `some H`, then `H` is in `T` and its root is `r`. -/
theorem find?_mem {T : Finset (Block V)} {r : BlockId} {H : Block V}
    (h : Block.find? T r = some H) : H ∈ T ∧ H.root = r := by
  unfold Block.find? pickUnique? at h
  split at h
  · rename_i hex
    rw [← Option.some.inj h]
    have := Finset.choose_spec _ _ hex
    exact ⟨this.1, by simpa using this.2⟩
  · cases h

/-- Under distinct roots, `Block.find? T H.root` is `some H` for every `H` in `T`. -/
theorem find?_of_mem {T : Finset (Block V)} (hT : DistinctRoots T) {H : Block V}
    (hH : H ∈ T) : Block.find? T H.root = some H := by
  have hex : ∃! a, a ∈ T ∧ (decide (a.root = H.root)) = true :=
    ⟨H, ⟨hH, by simp⟩, fun b hb => hT b hb.1 H hH (by simpa using hb.2)⟩
  unfold Block.find? pickUnique?
  rw [dif_pos hex]
  have := Finset.choose_spec _ _ hex
  exact congrArg some (hT _ this.1 H hH (by simpa using this.2))

/-- `resolved` answers under distinct roots. -/
theorem resolved_ok {T : Finset (Block V)} (hT : DistinctRoots T) (vote : GoldfishVote V) :
    ∃ b, resolved T vote = .ok b := by
  simp only [resolved, blockWithRoot_eq hT, DRE.bind_ok]
  split <;> exact ⟨_, rfl⟩

/-- `resolution_time` answers under distinct roots, when every block of the tree is stamped in `tb`
    and the vote is stamped in `tv`. -/
theorem resolution_time_ok {T : Finset (Block V)} (hT : DistinctRoots T)
    {tb : TimestampMap (Block V)} {tv : TimestampMap (GoldfishVote V)} {vote : GoldfishVote V}
    (htb : ∀ B ∈ T, tb B ≠ none) (htv : tv vote ≠ none) :
    ∃ o, resolution_time T tb tv vote = .ok o := by
  simp only [resolution_time, blockWithRoot_eq hT, DRE.bind_ok]
  cases hf : Block.find? T vote.head with
  | none => exact ⟨_, rfl⟩
  | some H =>
      obtain ⟨hHT, -⟩ := find?_mem hf
      obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp htv
      obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp (htb H hHT)
      simp only [ne_eq, reduceCtorEq, not_false_eq_true, dite_true]
      split
      · simp only [Option.value, Option.get_some, ha, hb]
        exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩

/-- `beforeCutoff` answers when every member of the set has a stamp. -/
theorem beforeCutoff_ok {α : Type} [DecidableEq α] {ts : TimestampMap α} (Γ : Time)
    {S : Finset α} (h : ∀ x ∈ S, ts x ≠ none) : ∃ v, beforeCutoff ts Γ S = .ok v := by
  refine filterM_ok _ _ fun x hx => ?_
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp (h x hx)
  simp only [ha]
  exact ⟨_, rfl⟩

/-- `Store.tau` answers when the tree has distinct roots, every block of it is stamped, and the vote
    is stamped. -/
theorem tau_ok {st : Store V} (hT : DistinctRoots st.T)
    (hb : ∀ B ∈ st.T, st.timestamp_block B ≠ none)
    {vote : GoldfishVote V} (hv : st.timestamp_vote vote ≠ none) :
    ∃ o, st.tau vote = .ok o :=
  resolution_time_ok hT hb hv

/-- On a stamped store, every Goldfish vote of `st.pool s` has a stamp. -/
theorem stamped_pool {st : Store V} (hst : Stamped st) {s : Slot} {u : GoldfishVote V}
    (hu : u ∈ st.pool s) : st.timestamp_vote u ≠ none :=
  hst.2.1 s u (List.mem_toFinset.mp hu)

/-! ## The views -/

/-- `voter_view` answers on a stamped store. -/
theorem voter_view_ok (C : Config) {st : Store V} (hst : Stamped st) (s : Slot) :
    ∃ v, voter_view C st s = .ok v := by
  unfold voter_view
  exact DRE.bind_ok_of (beforeCutoff_ok _ fun _ hx => stamped_pool hst hx) fun _ => ⟨_, rfl⟩

/-- `voter_support_view` answers on a stamped store whose tree has distinct roots. -/
theorem voter_support_view_ok (C : Config) {st : Store V} (hT : DistinctRoots st.T)
    (hst : Stamped st) (s : Slot) : ∃ v, voter_support_view C st s = .ok v := by
  simp only [voter_support_view]
  refine DRE.bind_ok_of (filterM_ok _ _ fun x hx => ?_)
    fun _ => DRE.bind_ok_of (filterM_ok _ _ fun x _ => ?_) fun _ => ⟨_, rfl⟩
  · exact DRE.bind_ok_of (tau_ok hT hst.1 (stamped_pool hst hx)) fun _ => ⟨_, rfl⟩
  · exact resolved_ok hT x

/-- `voter_processed_block_tree` answers on a stamped store. -/
theorem voter_processed_block_tree_ok (C : Config) {st : Store V} (hst : Stamped st)
    (s : Slot) : ∃ v, voter_processed_block_tree C st s = .ok v := by
  simp only [voter_processed_block_tree]
  refine filterM_ok _ _ fun B hB => ?_
  exact DRE.bind_ok_of (optionLift_ok (hst.1 B hB)) fun _ => ⟨_, rfl⟩

/-- `proposer_support_view` answers when the tree has distinct roots. -/
theorem proposer_support_view_ok {st : Store V} (hT : DistinctRoots st.T) (s : Slot) :
    ∃ v, proposer_support_view st s = .ok v :=
  List.filterM_ok _ _ fun vote _ => resolved_ok hT vote

/-! ## The Goldfish walk -/

/-- `targets_under` answers under distinct roots. -/
theorem targets_under_ok {T : Finset (Block V)} (hT : DistinctRoots T) (B : Block V)
    (vote : GoldfishVote V) : ∃ b, targets_under T B vote = .ok b := by
  simp only [targets_under, blockWithRoot_eq hT, DRE.bind_ok]
  split <;> exact ⟨_, rfl⟩

/-- `raw_supporters` answers under distinct roots. -/
theorem raw_supporters_ok {T : Finset (Block V)} (hT : DistinctRoots T)
    (votes support_votes : Finset (GoldfishVote V)) (s : Slot) (B : Block V) :
    ∃ v, raw_supporters T votes support_votes s B = .ok v := by
  unfold raw_supporters
  refine DRE.bind_ok_of (filterM_ok _ _ fun vote _ => ?_) fun _ => ⟨_, rfl⟩
  split
  · exact targets_under_ok hT B vote
  · exact ⟨_, rfl⟩

/-- `raw_goldfish_score` answers under distinct roots. -/
theorem raw_goldfish_score_ok {T : Finset (Block V)} (hT : DistinctRoots T)
    (votes support_votes : Finset (GoldfishVote V)) (s : Slot) (B : Block V) :
    ∃ n, raw_goldfish_score T votes support_votes s B = .ok n :=
  DRE.bind_ok_of (raw_supporters_ok hT votes support_votes s B) fun _ => ⟨_, rfl⟩

/-- `outranks` answers when the score answers on every block. -/
theorem outranks_ok {score : Block V → DRE Nat} (hs : ∀ B, ∃ n, score B = .ok n)
    (B C : Block V) : ∃ b, outranks score B C = .ok b :=
  DRE.bind_ok_of (hs B) fun _ => DRE.bind_ok_of (hs C) fun _ => ⟨_, rfl⟩

/-- `is_best_in` answers when the score answers on every block. -/
theorem is_best_in_ok {score : Block V → DRE Nat} (hs : ∀ B, ∃ n, score B = .ok n)
    (children : Finset (Block V)) (B : Block V) : ∃ b, is_best_in score children B = .ok b :=
  DRE.bind_ok_of (filterM_ok _ _ fun C _ => outranks_ok hs C B) fun _ => ⟨_, rfl⟩

/-- `argmax?` answers when the score answers on every block. -/
theorem argmax?_ok {score : Block V → DRE Nat} (hs : ∀ B, ∃ n, score B = .ok n)
    (children : Finset (Block V)) : ∃ o, argmax? score children = .ok o :=
  DRE.bind_ok_of (filterM_ok _ _ fun B _ => is_best_in_ok hs children B) fun _ => ⟨_, rfl⟩

/-- `ghost_children` answers when the eligibility test answers on every block. -/
theorem ghost_children_ok {eligible : Block V → DRE Bool}
    (he : ∀ B, ∃ b, eligible B = .ok b) (tree : Finset (Block V)) (H : Block V) :
    ∃ v, ghost_children tree eligible H = .ok v := by
  refine filterM_ok _ _ fun B _ => ?_
  split
  · exact he B
  · exact ⟨_, rfl⟩

/-- `ghost_step` answers when the score and the eligibility test answer on every block. -/
theorem ghost_step_ok {score : Block V → DRE Nat} {eligible : Block V → DRE Bool}
    (hs : ∀ B, ∃ n, score B = .ok n) (he : ∀ B, ∃ b, eligible B = .ok b)
    (tree : Finset (Block V)) (H : Block V) : ∃ o, ghost_step tree score eligible H = .ok o :=
  DRE.bind_ok_of (ghost_children_ok he tree H) fun c => argmax?_ok hs c

/-- `ghost_walk` answers when the score and the eligibility test answer on every block. -/
theorem ghost_walk_ok {score : Block V → DRE Nat} {eligible : Block V → DRE Bool}
    (hs : ∀ B, ∃ n, score B = .ok n) (he : ∀ B, ∃ b, eligible B = .ok b)
    (tree : Finset (Block V)) (n : Nat) (H : Block V) :
    ∃ B, ghost_walk tree score eligible n H = .ok B := by
  induction n generalizing H with
  | zero => exact ⟨H, rfl⟩
  | succ n ih =>
      simp only [ghost_walk]
      refine DRE.bind_ok_of (ghost_step_ok hs he tree H) fun o => ?_
      split
      · exact ih _
      · exact ⟨_, rfl⟩

/-- `ghost` answers when the score and the eligibility test answer on every block. -/
theorem ghost_ok {score : Block V → DRE Nat} {eligible : Block V → DRE Bool}
    (hs : ∀ B, ∃ n, score B = .ok n) (he : ∀ B, ∃ b, eligible B = .ok b)
    (anchor : Block V) (tree : Finset (Block V)) :
    ∃ B, ghost anchor tree score eligible = .ok B :=
  ghost_walk_ok hs he tree _ anchor

/-- `goldfish_eligible` answers under distinct roots. -/
theorem goldfish_eligible_ok {T : Finset (Block V)} (hT : DistinctRoots T)
    (σ : Block V → ChainState V) (h_max : Height) (cur : Slot)
    (votes support_votes : Finset (GoldfishVote V)) (s : Slot) (B : Block V) :
    ∃ b, goldfish_eligible σ h_max T cur votes support_votes s B = .ok b :=
  DRE.bind_ok_of (raw_goldfish_score_ok hT votes support_votes s B) fun _ => ⟨_, rfl⟩

/-- `goldfish_fork_choice` answers under distinct roots. -/
theorem goldfish_fork_choice_ok {T : Finset (Block V)} (hT : DistinctRoots T)
    (σ : Block V → ChainState V) (h_max : Height) (cur : Slot) (anchor : Block V)
    (tree : Finset (Block V)) (votes support_votes : Finset (GoldfishVote V)) (s : Slot) :
    ∃ B, goldfish_fork_choice σ h_max T cur anchor tree votes support_votes s = .ok B :=
  ghost_ok (fun B => raw_goldfish_score_ok hT votes support_votes s B)
    (fun B => goldfish_eligible_ok hT σ h_max cur votes support_votes s B) anchor tree

/-! ## The saved grade results -/

/-- A grade result read in `DRE` answers when it is not pending. -/
theorem gradeResult_ok {g : GradeResult V} (h : g ≠ .pending) :
    ∃ G, (g : DRE (Option (Block V))) = .ok G := by
  cases g with
  | pending => exact absurd rfl h
  | computed G => exact ⟨G, rfl⟩

/-- `make_result_compatible_with F` keeps a result that is not pending not pending. -/
theorem make_result_compatible_with_ne_pending (F : Block V) {g : GradeResult V}
    (h : g ≠ .pending) : make_result_compatible_with F g ≠ .pending := by
  cases g with
  | pending => exact absurd rfl h
  | computed G =>
      cases G <;> simp [make_result_compatible_with, GradeResult.block, Id.run]

/-- Taking a phase's result commutes with `make_round_grades_compatible_with F`. -/
theorem phaseResult_compatible (F : Block V) (g : RoundGrades V) (p : Phase) :
    phaseResult (make_round_grades_compatible_with F g) p =
      make_result_compatible_with F (phaseResult g p) := by
  cases p <;> rfl

/-- `Store.grade` answers for phase `p` when the saved result of phase `p` of the store's round is
    not pending. -/
theorem grade_ok (C : Config) {st : Store V} {p : Phase}
    (h : phaseResult (saved_round_grades st.saved_grades (C.round_of st.s)) p ≠ .pending) :
    ∃ G, st.grade C p = .ok G := by
  simp only [Store.grade]
  rw [phaseResult_compatible]
  exact gradeResult_ok (make_result_compatible_with_ne_pending _ h)

/-- `Store.G1` answers when the saved grade-1 result of the store's round is not pending. -/
theorem G1_ok (C : Config) {st : Store V}
    (h : (saved_round_grades st.saved_grades (C.round_of st.s)).g1 ≠ .pending) :
    ∃ G, st.G1 C = .ok G :=
  grade_ok C (p := .g1) h

/-- `Store.G2` answers when the saved grade-2 result of the store's round is not pending. -/
theorem G2_ok (C : Config) {st : Store V}
    (h : (saved_round_grades st.saved_grades (C.round_of st.s)).g2 ≠ .pending) :
    ∃ G, st.G2 C = .ok G :=
  grade_ok C (p := .g2) h

/-! ## The grade computation -/

/-- On a stamped store, every SG vote of `st.sg_votes_in_window eta r` has a stamp. -/
theorem stamped_sg {st : Store V} (hst : Stamped st) {eta r : Round} {u : SGVote V}
    (hu : u ∈ st.sg_votes_in_window eta r) : st.timestamp_sg_vote u ≠ none := by
  simp only [Store.sg_votes_in_window, Store.sg_votes, Store.sg_pool, Finset.map',
    Finset.mem_biUnion, Finset.mem_image] at hu
  obtain ⟨r', -, a, ha, rfl⟩ := hu
  exact hst.2.2 r' a (List.mem_toFinset.mp ha)

/-- `head_covers` answers under distinct roots, when `H` is empty or the root of a block of the
    tree. -/
theorem head_covers_ok {T : Finset (Block V)} (hT : DistinctRoots T) (B : Block V)
    {H : Option BlockId} (hH : ∀ x, H = some x → ∃ B' ∈ T, B'.root = x) :
    ∃ b, head_covers T B H = .ok b := by
  simp only [head_covers]
  cases hc : H with
  | none => exact ⟨false, rfl⟩
  | some x =>
      obtain ⟨B', hB'T, hB'r⟩ := hH x hc
      have hf : Block.find? T x = some B' := hB'r ▸ find?_of_mem hT hB'T
      simp only [ne_eq, reduceCtorEq, not_false_eq_true, dite_true, Option.value,
        Option.get_some, hf]
      exact ⟨_, rfl⟩

/-- `bodyReady` answers under distinct roots when every block of the tree is stamped; when it
    answers `true`, the vote's confirmed root, if any, is the root of a block of the tree. -/
theorem bodyReady_post {st : Store V} (hT : DistinctRoots st.T)
    (hb : ∀ B ∈ st.T, st.timestamp_block B ≠ none) (F : Block V) (t : Time) (u : SGVote V) :
    ∃ b, bodyReady st F t u = .ok b ∧
      (b = true → ∀ x, u.confirmed = some x → ∃ H ∈ st.T, H.root = x) := by
  simp only [bodyReady]
  cases hc : u.confirmed with
  | none => exact ⟨true, rfl, fun _ x hx => nomatch hx⟩
  | some x =>
      simp only [ne_eq, reduceCtorEq, not_false_eq_true, dite_true, Option.value,
        Option.get_some, blockWithRoot_eq hT, DRE.bind_ok]
      cases hf : Block.find? st.T x with
      | none => exact ⟨false, rfl, fun h => nomatch h⟩
      | some H =>
          obtain ⟨hHT, hHr⟩ := find?_mem hf
          obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp (hb H hHT)
          simp only [reduceCtorEq, not_false_eq_true, dite_true, Option.get_some, ha]
          exact ⟨_, rfl, fun _ y hy => ⟨H, hHT, hHr.trans (Option.some.inj hy)⟩⟩

/-- `rawInputs` answers on a stamped store. -/
theorem rawInputs_ok {st : Store V} (hst : Stamped st) (eta r : Round) (t : Time) (v : V) :
    ∃ w, rawInputs st eta r t v = .ok w := by
  unfold rawInputs
  exact filterM_ok _ _ fun u hu =>
    DRE.bind_ok_of (optionLift_ok (stamped_sg hst hu)) fun _ => ⟨_, rfl⟩

/-- `interpretedInputs` answers on a stamped store whose tree has distinct roots, and every vote it
    answers names a block of the tree or no block. -/
theorem interpretedInputs_post {st : Store V} (hT : DistinctRoots st.T) (hst : Stamped st)
    (F : Block V) (eta r : Round) (t : Time) (v : V) :
    ∃ w, interpretedInputs st F eta r t v = .ok w ∧
      ∀ u ∈ w, ∀ x, u.confirmed = some x → ∃ H ∈ st.T, H.root = x := by
  unfold interpretedInputs
  refine DRE.bind_ok_post (P := fun _ => True)
    ((rawInputs_ok hst eta r t v).imp fun _ h => ⟨h, trivial⟩) fun raw _ => ?_
  exact (filterM_post _ raw _ fun u _ => bodyReady_post hT hst.1 F t u).imp
    fun _ h => ⟨h.1, fun u hu => (h.2 u hu).2⟩

/-- `rawView` answers on a stamped store. -/
theorem rawView_ok {st : Store V} (hst : Stamped st) (eta r : Round) (t : Time) (v : V) :
    ∃ w, rawView st eta r t v = .ok w :=
  DRE.bind_ok_of (rawInputs_ok hst eta r t v) fun _ => ⟨_, rfl⟩

/-- `readyView` answers on a stamped store whose tree has distinct roots, and every token it answers
    has as key the root of a block of the tree, or no key. -/
theorem readyView_post {st : Store V} (hT : DistinctRoots st.T) (hst : Stamped st)
    (F : Block V) (eta r : Round) (t : Time) (v : V) :
    ∃ w, readyView st F eta r t v = .ok w ∧
      ∀ k ∈ w, ∀ x, k.key = some x → ∃ H ∈ st.T, H.root = x := by
  unfold readyView
  refine DRE.bind_ok_post (interpretedInputs_post hT hst F eta r t v) fun ready hready => ?_
  refine ⟨_, rfl, fun k hk x hx => ?_⟩
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hk
  exact hready u hu x hx

/-- `positive` answers on a stamped store whose tree has distinct roots. -/
theorem positive_ok {st : Store V} (hT : DistinctRoots st.T) (hst : Stamped st) (F : Block V)
    (eta r : Round) (t_0 t_1 : Time) (v : V) (B : Block V) :
    ∃ b, positive st F eta r t_0 t_1 v B = .ok b := by
  obtain ⟨E, hE, hEk⟩ := readyView_post hT hst F eta r t_0 v
  obtain ⟨L, hL, hLk⟩ := readyView_post hT hst F eta r t_1 v
  obtain ⟨R, hR⟩ := rawView_ok hst eta r t_1 v
  simp only [positive, hE, hL, hR, DRE.bind_ok]
  refine DRE.bind_ok_of (filterM_ok _ _ fun k hk => ?_) fun _ => ⟨_, rfl⟩
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hk
  exact head_covers_ok hT B fun x hx =>
    (Finset.mem_union.mp hu).elim (fun h => hEk u h x hx) (fun h => hLk u h x hx)

/-- `opposing` answers on a stamped store whose tree has distinct roots. -/
theorem opposing_ok {st : Store V} (hT : DistinctRoots st.T) (hst : Stamped st) (F : Block V)
    (eta r : Round) (t_0 t_1 : Time) (v : V) (B : Block V) :
    ∃ b, opposing st F eta r t_0 t_1 v B = .ok b := by
  obtain ⟨E, hE, -⟩ := readyView_post hT hst F eta r t_0 v
  obtain ⟨L, hL, hLk⟩ := readyView_post hT hst F eta r t_1 v
  obtain ⟨R, hR⟩ := rawView_ok hst eta r t_1 v
  simp only [opposing, hE, hL, hR, DRE.bind_ok]
  refine DRE.bind_ok_of (filterM_ok _ _ fun k hk => ?_) fun _ => ⟨_, rfl⟩
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hk
  exact head_covers_ok hT B fun x hx => hLk u hu x hx

/-- `gradeBool` answers on a stamped store whose tree has distinct roots. -/
theorem gradeBool_ok (P : Provisional V) {st : Store V} (hT : DistinctRoots st.T)
    (hst : Stamped st) (F : Block V) (eta r : Round) (t_0 t_1 : Time) (B : Block V) :
    ∃ b, gradeBool P st F eta r t_0 t_1 B = .ok b := by
  unfold gradeBool
  exact DRE.bind_ok_of (filterM_ok _ _ fun v _ => opposing_ok hT hst F eta r t_0 t_1 v B)
    fun _ => DRE.bind_ok_of (filterM_ok _ _ fun v _ => positive_ok hT hst F eta r t_0 t_1 v B)
      fun _ => ⟨_, rfl⟩

/-- `freezeRoot` answers on a stamped store whose tree has distinct roots. -/
theorem freezeRoot_ok (P : Provisional V) {st : Store V} (hT : DistinctRoots st.T)
    (hst : Stamped st) (F : Block V) (eta r : Round) (t_0 t_1 : Time) :
    ∃ G, freezeRoot P st F eta r t_0 t_1 = .ok G := by
  unfold freezeRoot
  exact DRE.bind_ok_of (filterM_ok _ _ fun B _ => gradeBool_ok P hT hst F eta r t_0 t_1 B)
    fun _ => ⟨_, rfl⟩

/-- `graded_block` answers on a stamped store whose tree has distinct roots. -/
theorem graded_block_ok (C : Config) (P : Provisional V) {st : Store V}
    (hT : DistinctRoots st.T) (hst : Stamped st) (r : Round) (t_0 t_1 : Time) :
    ∃ G, graded_block C P st r t_0 t_1 = .ok G :=
  freezeRoot_ok P hT hst st.F C.η_SG r t_0 t_1

/-- `update_grades` answers at any time `t` on a stamped store whose tree has distinct roots. -/
theorem update_grades_ok (C : Config) (P : Provisional V) {st : Store V}
    (hT : DistinctRoots st.T) (hst : Stamped st) (t : Time) :
    ∃ st', update_grades C P st t = .ok st' := by
  simp only [update_grades]
  repeat' (first
    | split
    | refine DRE.bind_ok_of (graded_block_ok C P ?_ ?_ _ _ _) fun _ => ?_)
  all_goals first | exact ⟨_, rfl⟩ | exact hT | exact hst

/-- `advance_to_round c r` is at round `r`. -/
theorem advance_to_round_round (c : SavedGrades V) (r : Round) :
    (advance_to_round c r).round = r := by
  unfold advance_to_round
  split_ifs with h1
  · exact h1.symm
  · rfl
  · rfl

/-- An answer `st'` of `update_grades` at `t` is `st` with only its saved grades written, and those
    are at the round of `t`'s slot. -/
theorem update_grades_writes_only_grades {C : Config} {P : Provisional V} {st st' : Store V}
    {t : Time} (h : update_grades C P st t = .ok st') :
    st' = { st with saved_grades := st'.saved_grades } ∧
      st'.saved_grades.round = C.round_of (C.slotOf t) := by
  simp only [update_grades] at h
  repeat' (first
    | (split_ifs at h)
    | (obtain ⟨_, -, h⟩ := DRE.of_bind_ok h; try dsimp only at h))
  all_goals
    have h' := h
    simp only [pure, Except.pure, Except.ok.injEq] at h'
    subst h'
    exact ⟨rfl, advance_to_round_round _ _⟩

/-! ## The grade readers -/

/-- The saved grades `c` read at their own round give `c.current`. -/
theorem saved_round_grades_of_round {c : SavedGrades V} {r : Round} (hr : c.round = r) :
    saved_round_grades c r = c.current := by
  subst hr
  simp [saved_round_grades]

/-- If the saved result of phase `p` of round `r` is not pending, neither is the one
    `round_grades st r` gives. -/
theorem round_grades_ne_pending {st : Store V} {r : Round} {p : Phase}
    (h : phaseResult (saved_round_grades st.saved_grades r) p ≠ .pending) :
    phaseResult (round_grades st r) p ≠ .pending := by
  rw [show round_grades st r =
      make_round_grades_compatible_with st.F (saved_round_grades st.saved_grades r) from rfl,
    phaseResult_compatible]
  exact make_result_compatible_with_ne_pending _ h

/-- `computed_grades` answers when the three results are computed. -/
theorem computed_grades_ok {g : RoundGrades V} (h2 : g.g2 ≠ .pending) (h1 : g.g1 ≠ .pending)
    (h0 : g.g0 ≠ .pending) : ∃ G, computed_grades g = .ok G :=
  DRE.bind_ok_of (gradeResult_ok h2) fun _ => DRE.bind_ok_of (gradeResult_ok h1)
    fun _ => DRE.bind_ok_of (gradeResult_ok h0) fun _ => ⟨_, rfl⟩

/-- `rawG2` answers when the grade-2 result is computed. -/
theorem rawG2_ok {g : RoundGrades V} (h2 : g.g2 ≠ .pending) : ∃ b, rawG2 g = .ok b :=
  DRE.bind_ok_of (gradeResult_ok h2) fun _ => ⟨_, rfl⟩

/-- `anchor` answers when the grade-1 result is computed. -/
theorem anchor_ok (st : Store V) {g1 : GradeResult V} (h1 : g1 ≠ .pending) :
    ∃ A, anchor st g1 = .ok A :=
  DRE.bind_ok_of (gradeResult_ok h1) fun _ => ⟨_, rfl⟩

/-- `grade2Block` answers when the three results are computed. -/
theorem grade2Block_ok (st : Store V) {g : RoundGrades V} (h2 : g.g2 ≠ .pending)
    (h1 : g.g1 ≠ .pending) (h0 : g.g0 ≠ .pending) : ∃ G, grade2Block st g = .ok G :=
  DRE.bind_ok_of (computed_grades_ok h2 h1 h0) fun _ => ⟨_, rfl⟩

/-- `confirmation_candidate` answers when the saved grade-2 result of the store's round is computed. -/
theorem confirmation_candidate_ok (C : Config) {st : Store V}
    (h2 : (saved_round_grades st.saved_grades (C.round_of st.s)).g2 ≠ .pending) :
    ∃ G, confirmation_candidate C st = .ok G :=
  DRE.bind_ok_of (G2_ok C h2) fun _ => ⟨_, rfl⟩

/-- `round_stable_root` answers when the saved grade-2 result of round `r` is computed. -/
theorem round_stable_root_ok {st : Store V} {r : Round}
    (h2 : (saved_round_grades st.saved_grades r).g2 ≠ .pending) :
    ∃ B, round_stable_root st r = .ok B := by
  unfold round_stable_root
  exact DRE.bind_ok_of (gradeResult_ok (round_grades_ne_pending (p := .g2) h2))
    fun _ => ⟨_, rfl⟩

/-- `round_grade_read` answers when the three saved results of round `r` are computed. -/
theorem round_grade_read_ok {st : Store V} {r : Round}
    (h2 : (saved_round_grades st.saved_grades r).g2 ≠ .pending)
    (h1 : (saved_round_grades st.saved_grades r).g1 ≠ .pending)
    (h0 : (saved_round_grades st.saved_grades r).g0 ≠ .pending) :
    ∃ G, round_grade_read st r = .ok G := by
  have h2' := round_grades_ne_pending (st := st) (p := .g2) h2
  have h1' := round_grades_ne_pending (st := st) (p := .g1) h1
  have h0' := round_grades_ne_pending (st := st) (p := .g0) h0
  unfold round_grade_read
  exact DRE.bind_ok_of (anchor_ok st h1') fun _ =>
    DRE.bind_ok_of (grade2Block_ok st h2' h1' h0') fun _ =>
      DRE.bind_ok_of (gradeResult_ok h0') fun _ =>
        DRE.bind_ok_of (rawG2_ok h2') fun _ => ⟨_, rfl⟩

/-! ## The head -/

/-- `get_sg_root_with` answers when the saved grade-1 result of the store's round is computed. -/
theorem get_sg_root_with_ok (C : Config) {st : Store V}
    (h1 : (saved_round_grades st.saved_grades (C.round_of st.s)).g1 ≠ .pending) :
    ∃ A, get_sg_root_with C st = .ok A := by
  unfold get_sg_root_with
  refine DRE.bind_ok_of (G1_ok C h1) fun _ => ?_
  dsimp only
  split <;> exact ⟨_, rfl⟩

/-- `get_head_in_tree_with_layer` answers when the store's tree has distinct roots and the saved
    grade-1 result of the store's round is computed. -/
theorem get_head_in_tree_with_layer_ok (C : Config) {st : Store V} (hT : DistinctRoots st.T)
    (h1 : (saved_round_grades st.saved_grades (C.round_of st.s)).g1 ≠ .pending)
    (tree : Finset (Block V)) (votes support_votes : Finset (GoldfishVote V)) (s : Slot) :
    ∃ H, get_head_in_tree_with_layer C st tree votes support_votes s = .ok H :=
  DRE.bind_ok_of (get_sg_root_with_ok C h1) fun A =>
    goldfish_fork_choice_ok hT st.σ st.h_max st.s A tree votes support_votes s

/-- `get_head_with` answers when the store's tree has distinct roots and the saved grade-1 result of
    the store's round is computed. -/
theorem get_head_with_ok (C : Config) {st : Store V} (hT : DistinctRoots st.T)
    (h1 : (saved_round_grades st.saved_grades (C.round_of st.s)).g1 ≠ .pending)
    (votes support_votes : Finset (GoldfishVote V)) (s : Slot) :
    ∃ H, get_head_with C st votes support_votes s = .ok H :=
  get_head_in_tree_with_layer_ok C hT h1 _ votes support_votes s

/-! ## The Goldfish vote and the confirmation -/

/-- `voter_filtered_block_tree` answers on a stamped store. -/
theorem voter_filtered_block_tree_ok (C : Config) {st : Store V} (hst : Stamped st)
    (s : Slot) : ∃ T, voter_filtered_block_tree C st s = .ok T :=
  DRE.bind_ok_of (voter_processed_block_tree_ok C hst s) fun _ => ⟨_, rfl⟩

/-- The Goldfish vote duty `goldfish_vote` answers, from any list of objects sent before it, on a
    stamped store whose tree has distinct roots and whose round's saved grade-1 result is computed. -/
theorem goldfish_vote_ok (C : Config) (P : Provisional V) (v : V) {st : Store V}
    (hT : DistinctRoots st.T) (hst : Stamped st)
    (h1 : (saved_round_grades st.saved_grades (C.round_of st.s)).g1 ≠ .pending)
    (l : List (NamedObject V)) :
    ∃ out, (goldfish_vote C P v st).run l = .ok out := by
  simp only [goldfish_vote]
  refine DREB.bind_ok_of (DREB.liftM_ok (voter_view_ok C hst _) l) fun _ l1 => ?_
  refine DREB.bind_ok_of (DREB.liftM_ok (voter_support_view_ok C hT hst _) l1) fun _ l2 => ?_
  refine DREB.bind_ok_of (DREB.liftM_ok (voter_filtered_block_tree_ok C hst _) l2)
    fun _ l3 => ?_
  refine DREB.bind_ok_of (DREB.liftM_ok (get_head_in_tree_with_layer_ok C hT h1 _ _ _ _) l3)
    fun _ l4 => ?_
  split
  · exact DREB.bind_ok_of (DREB.broadcast_ok _ l4) fun _ l5 => DREB.pure_ok _ l5
  · exact DREB.pure_ok _ l4

/-- The confirmation duty `update_confirmation` answers, for every slot, on a stamped store whose
    tree has distinct roots and whose round's saved grade-1 and grade-2 results are computed. -/
theorem update_confirmation_ok (C : Config) {st : Store V} (hT : DistinctRoots st.T)
    (hst : Stamped st)
    (h1 : (saved_round_grades st.saved_grades (C.round_of st.s)).g1 ≠ .pending)
    (h2 : (saved_round_grades st.saved_grades (C.round_of st.s)).g2 ≠ .pending) (s : Slot) :
    ∃ st', update_confirmation C st s = .ok st' := by
  simp only [update_confirmation]
  refine DRE.bind_ok_of (filterM_ok _ _ fun _ hv =>
    DRE.bind_ok_of (tau_ok hT hst.1 (stamped_pool hst hv)) fun _ => ⟨_, rfl⟩) fun _ => ?_
  refine DRE.bind_ok_of (beforeCutoff_ok _ fun _ hx => stamped_pool hst hx) fun _ => ?_
  refine DRE.bind_ok_of (get_sg_root_with_ok C h1) fun _ => ?_
  refine DRE.bind_ok_of (ghost_ok (fun B => raw_goldfish_score_ok hT _ _ _ B)
    (fun B => DRE.bind_ok_of (raw_goldfish_score_ok hT _ _ _ B) fun _ => ⟨_, rfl⟩) _ _)
    fun H => ?_
  refine DRE.bind_ok_of (DRE.bind_ok_of (raw_goldfish_score_ok hT _ _ _ H) fun _ => ⟨_, rfl⟩)
    fun _ => ?_
  refine DRE.bind_ok_of (round_stable_root_ok h2) fun _ => ?_
  refine DRE.bind_ok_of (confirmation_candidate_ok C h2) fun _ => ?_
  repeat' split
  all_goals exact ⟨_, rfl⟩

/-- An answer `st'` of `update_confirmation` is `st` with only `live_confirmed`, `latest_stable` and
    `latest_confirmed` written. -/
theorem update_confirmation_writes_only_confirmation {C : Config} {st st' : Store V}
    {s : Slot} (h : update_confirmation C st s = .ok st') :
    st' = { st with live_confirmed := st'.live_confirmed, latest_stable := st'.latest_stable,
                    latest_confirmed := st'.latest_confirmed } := by
  simp only [update_confirmation] at h
  repeat' (first
    | (split_ifs at h)
    | (obtain ⟨_, -, h⟩ := DRE.of_bind_ok h; try dsimp only at h))
  all_goals
    have h' := h
    simp only [pure, Except.pure, Except.ok.injEq] at h'
    subst h'
    rfl

/-! ## The attestation -/

/-- `grade2_block_with` answers when the three saved results of round `r` are computed. -/
theorem grade2_block_with_ok {st : Store V} {r : Round}
    (h2 : (saved_round_grades st.saved_grades r).g2 ≠ .pending)
    (h1 : (saved_round_grades st.saved_grades r).g1 ≠ .pending)
    (h0 : (saved_round_grades st.saved_grades r).g0 ≠ .pending) :
    ∃ G, grade2_block_with st r = .ok G :=
  grade2Block_ok st (round_grades_ne_pending (p := .g2) h2)
    (round_grades_ne_pending (p := .g1) h1) (round_grades_ne_pending (p := .g0) h0)

/-- `get_sg_vote_with` answers, for every grade-2 candidate, when the three saved results of round
    `r` are computed. -/
theorem get_sg_vote_with_ok {st : Store V} {r : Round}
    (h2 : (saved_round_grades st.saved_grades r).g2 ≠ .pending)
    (h1 : (saved_round_grades st.saved_grades r).g1 ≠ .pending)
    (h0 : (saved_round_grades st.saved_grades r).g0 ≠ .pending) (A_G2 : Option (Block V)) :
    ∃ B, get_sg_vote_with st r A_G2 = .ok B :=
  DRE.bind_ok_of (round_grade_read_ok h2 h1 h0) fun _ => ⟨_, rfl⟩

/-- `fg_source_with` answers, for every grade-2 candidate, when the saved grade-0 result of round
    `r` is computed. -/
theorem fg_source_with_ok {st : Store V} {r : Round}
    (h0 : (saved_round_grades st.saved_grades r).g0 ≠ .pending) (A_G2 : Option (Block V)) :
    ∃ B, fg_source_with st r A_G2 = .ok B := by
  simp only [fg_source_with]
  split
  · refine DRE.bind_ok_of (gradeResult_ok (round_grades_ne_pending (p := .g0) h0)) fun _ => ?_
    split <;> exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

/-- `get_fg_vote_with` answers, for every grade-2 candidate, when the store's tree has distinct
    roots, the saved grade-1 result of the store's round is computed, and the saved grade-0 result
    of round `r` is computed. -/
theorem get_fg_vote_with_ok (C : Config) {st : Store V} (hT : DistinctRoots st.T)
    (h1 : (saved_round_grades st.saved_grades (C.round_of st.s)).g1 ≠ .pending) {r : Round}
    (h0 : (saved_round_grades st.saved_grades r).g0 ≠ .pending) (A_G2 : Option (Block V)) :
    ∃ f, get_fg_vote_with C st r A_G2 = .ok f := by
  simp only [get_fg_vote_with]
  refine DRE.bind_ok_of (filterM_ok _ _ fun u _ => resolved_ok hT u) fun _ => ?_
  refine DRE.bind_ok_of (get_head_with_ok C hT h1 _ _ _) fun _ => ?_
  refine DRE.bind_ok_of (fg_source_with_ok h0 A_G2) fun _ => ?_
  split <;> exact ⟨_, rfl⟩

/-- `attestation_input` answers when the store's tree has distinct roots and the three saved results
    of the store's round are computed. -/
theorem attestation_input_ok (C : Config) (v : V) {st : Store V} (hT : DistinctRoots st.T)
    (h2 : (saved_round_grades st.saved_grades (C.round_of st.s)).g2 ≠ .pending)
    (h1 : (saved_round_grades st.saved_grades (C.round_of st.s)).g1 ≠ .pending)
    (h0 : (saved_round_grades st.saved_grades (C.round_of st.s)).g0 ≠ .pending) :
    ∃ i, attestation_input C v st = .ok i := by
  simp only [attestation_input]
  refine DRE.bind_ok_of (grade2_block_with_ok h2 h1 h0) fun A => ?_
  refine DRE.bind_ok_of (get_fg_vote_with_ok C hT h1 h0 A) fun p => ?_
  obtain ⟨_, _, _, _⟩ := p
  exact DRE.bind_ok_of (get_sg_vote_with_ok h2 h1 h0 A) fun _ => ⟨_, rfl⟩

/-- `build_attestation` answers when the store's tree has distinct roots and the three saved results
    of the store's round are computed. -/
theorem build_attestation_ok (C : Config) (v : V) {st : Store V} (hT : DistinctRoots st.T)
    (h2 : (saved_round_grades st.saved_grades (C.round_of st.s)).g2 ≠ .pending)
    (h1 : (saved_round_grades st.saved_grades (C.round_of st.s)).g1 ≠ .pending)
    (h0 : (saved_round_grades st.saved_grades (C.round_of st.s)).g0 ≠ .pending)
    (signingHistory : SigningHistory) :
    ∃ p, build_attestation C v st signingHistory = .ok p :=
  DRE.bind_ok_of (attestation_input_ok C v hT h2 h1 h0) fun _ => ⟨_, rfl⟩

/-- The attestation duty `attest` answers, from any list of objects sent before it, when the store's
    tree has distinct roots and the three saved results of the store's round are computed. -/
theorem attest_ok (C : Config) (v : V) {st : Store V} (hT : DistinctRoots st.T)
    (h2 : (saved_round_grades st.saved_grades (C.round_of st.s)).g2 ≠ .pending)
    (h1 : (saved_round_grades st.saved_grades (C.round_of st.s)).g1 ≠ .pending)
    (h0 : (saved_round_grades st.saved_grades (C.round_of st.s)).g0 ≠ .pending)
    (signingHistory : SigningHistory) (l : List (NamedObject V)) :
    ∃ out, (attest C v st signingHistory).run l = .ok out := by
  simp only [attest]
  refine DREB.bind_ok_of (DREB.liftM_ok (build_attestation_ok C v hT h2 h1 h0 _) l)
    fun _ l1 => ?_
  exact DREB.bind_ok_of (DREB.broadcast_ok _ l1) fun _ l2 => DREB.pure_ok _ l2

/-! ## The proposal -/

/-- `sorted_blocks` answers when the store's tree has distinct roots. -/
theorem sorted_blocks_ok {st : Store V} (hT : DistinctRoots st.T) :
    ∃ l, sorted_blocks st = .ok l := by
  unfold sorted_blocks
  refine List.mapM_ok _ _ fun root hroot => ?_
  unfold sorted_block_roots at hroot
  obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp ((Finset.mem_sort _).mp hroot)
  refine optionLift_ok ?_
  rw [show pickUnique? st.T (fun B' => decide (B'.root = B.root)) = Block.find? st.T B.root
    from rfl, find?_of_mem hT hB]
  exact Option.some_ne_none B

/-- `included_attestations_in_window` answers when the store's tree has distinct roots. -/
theorem included_attestations_in_window_ok (C : Config) {st : Store V}
    (hT : DistinctRoots st.T) : ∃ l, included_attestations_in_window C st = .ok l := by
  simp only [included_attestations_in_window]
  refine DRE.bind_ok_of (sorted_blocks_ok hT) fun _ => ?_
  exact DRE.bind_ok_of (List.forIn_ok _ _ _ fun _ _ => by split <;> exact ⟨_, rfl⟩)
    fun _ => ⟨_, rfl⟩

/-- `attestations_to_include` answers when the store's tree has distinct roots. -/
theorem attestations_to_include_ok (C : Config) {st : Store V} (hT : DistinctRoots st.T) :
    ∃ l, attestations_to_include C st = .ok l :=
  DRE.bind_ok_of (included_attestations_in_window_ok C hT) fun _ => ⟨_, rfl⟩

/-- `proposal_input` answers when the store's tree has distinct roots and the saved grade-1 result
    of the store's round is computed. -/
theorem proposal_input_ok (C : Config) (X : External V) (v : V) {st : Store V}
    (hT : DistinctRoots st.T)
    (h1 : (saved_round_grades st.saved_grades (C.round_of st.s)).g1 ≠ .pending) :
    ∃ i, proposal_input C X v st = .ok i := by
  simp only [proposal_input]
  exact DRE.bind_ok_of (proposer_support_view_ok hT _) fun _ =>
    DRE.bind_ok_of (get_head_with_ok C hT h1 _ _ _) fun _ => ⟨_, rfl⟩

/-- `build_proposal` answers when the store's tree has distinct roots and the saved grade-1 result
    of the store's round is computed. -/
theorem build_proposal_ok (C : Config) (X : External V) (v : V) {st : Store V}
    (hT : DistinctRoots st.T)
    (h1 : (saved_round_grades st.saved_grades (C.round_of st.s)).g1 ≠ .pending) :
    ∃ B, build_proposal C X v st = .ok B :=
  DRE.bind_ok_of (proposal_input_ok C X v hT h1) fun _ =>
    DRE.bind_ok_of (attestations_to_include_ok C hT) fun _ => ⟨_, rfl⟩

/-- The proposal duty `propose_block` answers, from any list of objects sent before it, when the
    store's tree has distinct roots and the saved grade-1 result of the store's round is computed. -/
theorem propose_block_ok (C : Config) (P : Provisional V) (X : External V) (v : V)
    {st : Store V} (hT : DistinctRoots st.T)
    (h1 : (saved_round_grades st.saved_grades (C.round_of st.s)).g1 ≠ .pending)
    (l : List (NamedObject V)) :
    ∃ out, (propose_block C P X v st).run l = .ok out := by
  simp only [propose_block]
  refine DREB.bind_ok_of (DREB.liftM_ok (build_proposal_ok C X v hT h1) l) fun _ l1 => ?_
  exact DREB.bind_ok_of (DREB.broadcast_ok _ l1) fun _ l2 => DREB.pure_ok _ l2

end SpecDraftRecord.NoRaise
