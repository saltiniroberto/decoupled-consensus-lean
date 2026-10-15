import Proofs.Instance.Equalities.Images
import Proofs.Instance.Equalities.ForkChoice
import Proofs.Instance.Equalities.Schedule
import Proofs.Instance.StoreOk
import Proofs.Instance.Model
import Proofs.Instance.NoRaise.Routines
import Proofs.Vocabulary.ModelVocabulary

/-!
# The fork-choice members of `Model.spec` and of `Model.vocabulary`

Each theorem compares one member of the fork-choice family of `Model.spec` with the same member
of `Model.vocabulary`, at the same arguments and, for a member that reads a store, at a store
`st : OkStore V` of the instance and its image. Some members are equal as functions; for the
Goldfish fork choice every outcome is the value of `Model.vocabulary`; the views agree at `OkStore V`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace SpecRecord.ForkChoiceImages

open Spec
open SpecRecord.ForkChoiceGrades
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Raising filters, unique picks and outcomes -/

omit [DecidableEq V] [Fintype V] in
/-- If `p` answers `true` exactly where `q` holds, wherever `p` answers, then a filter of `s` by `p`
    that answers keeps the members of `s` where `q` holds. -/
theorem filterM_eq_filter_of_ok {α : Type} [DecidableEq α] (p : α → DC.DRE Bool) (q : α → Prop)
    [DecidablePred q] (hpq : ∀ a b, p a = .ok b → (b = true ↔ q a)) :
    ∀ (s : Finset α) (v : Finset α), s.filterM p = .ok v → v = s.filter q := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro v hv
    simp only [Finset.filterM, Finset.fold_empty] at hv
    cases hv
    rfl
  | @insert a s ha ih =>
    intro v hv
    have hstep : (insert a s).filterM p =
        Finset.unionM (do if ← p a then return {a} else return ∅) (s.filterM p) := by
      simp only [Finset.filterM, Finset.fold_insert ha]
    rw [hstep] at hv
    cases hpa : p a with
    | error e => simp [Finset.unionM, hpa, bind, Except.bind] at hv
    | ok b =>
      cases hrest : s.filterM p with
      | error e =>
        cases b <;> simp [Finset.unionM, hpa, hrest, bind, Except.bind, pure, Except.pure] at hv
      | ok w =>
        have hw := ih w hrest
        have hb := hpq a b hpa
        rw [Finset.filter_insert]
        cases b
        · have hq : ¬ q a := fun h => by simpa using hb.mpr h
          simp [Finset.unionM, hpa, hrest, bind, Except.bind, pure, Except.pure] at hv
          subst hv
          simp [hq, hw]
        · have hq : q a := hb.mp rfl
          simp [Finset.unionM, hpa, hrest, bind, Except.bind, pure, Except.pure] at hv
          subst hv
          rw [if_pos hq, hw, Finset.insert_eq]

omit [DecidableEq V] [Fintype V] in
/-- `filterM_eq_filter_of_ok` with the agreement asked only on the members of `s`. -/
theorem filterM_eq_filter_of_ok_mem {α : Type} [DecidableEq α] (p : α → DC.DRE Bool)
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

/-- Picking the one member of `S.map e` that passes `p` is mapping by `e` the one member of `S` that
    passes `p ∘ e`. -/
theorem pickUnique?_map {α β : Type} [DecidableEq α] [DecidableEq β] (S : Finset α)
    (e : α ↪ β) (p : β → Bool) :
    pickUnique? (S.map e) p =
      (DecoupledConsensusModel.pickUnique? S (fun a => p (e a))).map e := by
  unfold pickUnique? DecoupledConsensusModel.pickUnique?
  by_cases h : ∃! a, a ∈ S ∧ p (e a) = true
  · have h' : ∃! b, b ∈ S.map e ∧ p b = true := by
      obtain ⟨a, ⟨haS, hpa⟩, hu⟩ := h
      refine ⟨e a, ⟨Finset.mem_map_of_mem e haS, hpa⟩, ?_⟩
      rintro b ⟨hb, hpb⟩
      obtain ⟨a', ha'S, rfl⟩ := Finset.mem_map.mp hb
      exact congrArg e (hu a' ⟨ha'S, hpb⟩)
    rw [dif_pos h', dif_pos h, Option.map_some]
    congr 1
    have hc := Finset.choose_spec (fun a => p (e a) = true) S h
    have hc' := Finset.choose_spec (fun b => p b = true) (S.map e) h'
    obtain ⟨a, ⟨haS, hpa⟩, hu⟩ := h
    obtain ⟨a', ha'S, he⟩ := Finset.mem_map.mp hc'.1
    rw [← he, hu a' ⟨ha'S, he ▸ hc'.2⟩, hu _ hc]
  · have h' : ¬ ∃! b, b ∈ S.map e ∧ p b = true := by
      rintro ⟨b, ⟨hb, hpb⟩, hu⟩
      obtain ⟨a, haS, rfl⟩ := Finset.mem_map.mp hb
      exact h ⟨a, ⟨haS, hpb⟩, fun a' ha' =>
        e.injective (hu (e a') ⟨Finset.mem_map_of_mem e ha'.1, ha'.2⟩)⟩
    rw [dif_neg h', dif_neg h, Option.map_none]

omit [DecidableEq V] [Fintype V] in
/-- The outcomes of an answer `a` are the one outcome `a`. -/
theorem successOutcomes_ok {α : Type} (a : α) : successOutcomes (.ok a : DC.DRE α) = pure a := rfl

omit [DecidableEq V] [Fintype V] in
/-- If `r`, wherever it answers, answers `a`, then `orVocabulary r a` has the one outcome `a`. -/
theorem successOutcomes_orVocabulary {α : Type} (r : DC.DRE α) (a : α)
    (h : ∀ b, r = .ok b → b = a) : successOutcomes (orVocabulary r a) = pure a := by
  cases hr : r with
  | ok b => rw [← h b hr]; rfl
  | error e => rfl

/-! ## Blocks and votes through `toSpec` -/

omit [DecidableEq V] [Fintype V] in
/-- The root of `Block.toSpec B` is `BlockId.toSpec` of `B`'s root. -/
theorem toSpec_root (B : DecoupledConsensusModel.Block V) :
    (Block.toSpec B).root = BlockId.toSpec B.root := by
  have h := Block.toProof_root (Block.toSpec B)
  rw [Block.toProof_toSpec] at h
  rw [h, BlockId.toSpec_toProof]

omit [DecidableEq V] [Fintype V] in
/-- The slot of `Block.toSpec B` is the slot of `B`. -/
theorem toSpec_slot (B : DecoupledConsensusModel.Block V) :
    (Block.toSpec B).slot = B.slot := by
  cases B <;> simp [Block.toSpec, Block.slot, DecoupledConsensusModel.Block.slot]

omit [DecidableEq V] [Fintype V] in
/-- The parent of `Block.toSpec B` is `Block.toSpec` of the parent of `B`. -/
theorem toSpec_parent (B : DecoupledConsensusModel.Block V) :
    (Block.toSpec B).parent = Block.toSpec B.parent := by
  cases B <;> simp [Block.toSpec, Block.parent, DecoupledConsensusModel.Block.parent]

omit [DecidableEq V] [Fintype V] in
/-- The optional parent of `Block.toSpec B` is `B`'s optional parent mapped by `Block.toSpec`. -/
theorem toSpec_parent? (B : DecoupledConsensusModel.Block V) :
    (Block.toSpec B).parent? = B.parent?.map Block.toSpec := by
  cases B <;> simp [Block.toSpec, Block.parent?, DecoupledConsensusModel.Block.parent?]

omit [DecidableEq V] [Fintype V] in
/-- `BlockId.toSpec` is injective. -/
theorem blockIdToSpec_inj {r r' : DecoupledConsensusModel.BlockId} :
    BlockId.toSpec r = BlockId.toSpec r' ↔ r = r' :=
  ⟨fun h => by simpa using congrArg BlockId.toProof h, fun h => h ▸ rfl⟩

/-- The spec's lookup by root in `T.map e`, for an embedding `e` whose function is `Block.toSpec`,
    is `DecoupledConsensusModel.Block.find? T r` mapped by `e`. -/
theorem find?_map (T : Finset (DecoupledConsensusModel.Block V))
    (e : DecoupledConsensusModel.Block V ↪ Block V) (he : ∀ B, e B = Block.toSpec B)
    (r : DecoupledConsensusModel.BlockId) :
    Block.find? (T.map e) (BlockId.toSpec r) =
      (DecoupledConsensusModel.Block.find? T r).map e := by
  unfold Block.find? DecoupledConsensusModel.Block.find?
  rw [pickUnique?_map]
  congr 2
  funext B
  rw [he, toSpec_root]
  simp only [blockIdToSpec_inj]

/-- If `blockWithRoot` answers `o` on `T.map e` and `BlockId.toSpec r`, then `o` is
    `DecoupledConsensusModel.Block.find? T r` mapped by `e`. -/
theorem blockWithRoot_map_of_ok (T : Finset (DecoupledConsensusModel.Block V))
    (e : DecoupledConsensusModel.Block V ↪ Block V) (he : ∀ B, e B = Block.toSpec B)
    (r : DecoupledConsensusModel.BlockId) {o : Option (Block V)}
    (h : blockWithRoot (T.map e) (BlockId.toSpec r) = .ok o) :
    o = (DecoupledConsensusModel.Block.find? T r).map e := by
  unfold blockWithRoot at h
  split at h
  · cases h
  · rw [← find?_map T e he r]
    exact (Except.ok.inj h).symm

/-! ## The members on plain sets -/

/-- Where the spec's `targets_under` answers on the `Block.toSpec` forms of a tree, a block and a
    vote, it answers `DecoupledConsensusModel.Protocol.targets_under`. -/
theorem targets_under_of_ok (T : Finset (DecoupledConsensusModel.Block V))
    (B : DecoupledConsensusModel.Block V) (vote : DecoupledConsensusModel.GoldfishVote V) {b : Bool}
    (h : Protocol.targets_under (T.map blockToSpecEmb) (Block.toSpec B) (GoldfishVote.toSpec vote) =
      .ok b) :
    b = DecoupledConsensusModel.Protocol.targets_under T B vote := by
  unfold Protocol.targets_under at h
  cases hb : blockWithRoot (T.map blockToSpecEmb) (GoldfishVote.toSpec vote).head with
  | error e => rw [hb] at h; cases h
  | ok o =>
    rw [hb] at h
    have ho := blockWithRoot_map_of_ok T blockToSpecEmb (fun _ => rfl) vote.head hb
    unfold DecoupledConsensusModel.Protocol.targets_under
    cases hf : DecoupledConsensusModel.Block.find? T vote.head with
    | none =>
      rw [hf] at ho
      subst ho
      exact (Except.ok.inj (h : (Except.ok false : DC.DRE Bool) = .ok b)).symm
    | some B' =>
      rw [hf] at ho
      subst ho
      have h' : (Except.ok (decide ((Block.toSpec B').slot ≤ (GoldfishVote.toSpec vote).slot) &&
          (Block.toSpec B).ancestorEq (Block.toSpec B')) : DC.DRE Bool) = .ok b := h
      rw [← Except.ok.inj h', Block.toSpec_ancestorEq, toSpec_slot]
      rfl

omit [DecidableEq V] [Fintype V] in
/-- Mapping a set of `DecoupledConsensusModel` votes to the spec's type and back gives the set. -/
theorem map_voteToSpec_map_toProof (votes : Finset (DecoupledConsensusModel.GoldfishVote V)) :
    (votes.map voteToSpecEmb).map GoldfishVote.toProofEmb = votes := by
  ext u
  simp [voteToSpecEmb]

omit [Fintype V] in
/-- `v` equivocates among the spec forms of `votes` exactly when it equivocates in `votes`. -/
theorem equivocates_map (votes : Finset (DecoupledConsensusModel.GoldfishVote V)) (v : V) :
    Protocol.equivocates (votes.map voteToSpecEmb) v =
      DecoupledConsensusModel.Protocol.equivocates votes v := by
  rw [← toProof_equivocates, map_voteToSpec_map_toProof]

/-- The equivocators among the spec forms of `votes` are those of `votes`. -/
theorem raw_equivocators_map (votes : Finset (DecoupledConsensusModel.GoldfishVote V)) :
    Protocol.raw_equivocators (votes.map voteToSpecEmb) =
      DecoupledConsensusModel.Protocol.raw_equivocators votes := by
  ext v
  simp [Protocol.raw_equivocators, DecoupledConsensusModel.Protocol.raw_equivocators,
    equivocates_map]

/-- The spec's count of voters on the spec forms of `votes` is
    `DecoupledConsensusModel.Protocol.raw_voters_count votes`. -/
theorem raw_voters_count_map (votes : Finset (DecoupledConsensusModel.GoldfishVote V)) :
    Protocol.raw_voters_count (votes.map voteToSpecEmb) =
      DecoupledConsensusModel.Protocol.raw_voters_count votes := by
  unfold Protocol.raw_voters_count DecoupledConsensusModel.Protocol.raw_voters_count
  congr 1
  ext v
  simp [Protocol.raw_participants, DecoupledConsensusModel.Protocol.raw_participants,
    ← toProof_participates, map_voteToSpec_map_toProof]

/-- Where the spec's `raw_supporters` answers on the spec forms of a tree, the votes, the support
    votes and a block, it answers `DecoupledConsensusModel.Protocol.raw_supporters`. -/
theorem raw_supporters_of_ok (T : Finset (DecoupledConsensusModel.Block V))
    (votes support_votes : Finset (DecoupledConsensusModel.GoldfishVote V)) (s : Slot)
    (B : DecoupledConsensusModel.Block V) {R : Finset V}
    (h : Protocol.raw_supporters (T.map blockToSpecEmb) (votes.map voteToSpecEmb)
      (support_votes.map voteToSpecEmb) s (Block.toSpec B) = .ok R) :
    R = DecoupledConsensusModel.Protocol.raw_supporters T votes support_votes s B := by
  unfold Protocol.raw_supporters at h
  cases hf : (support_votes.map voteToSpecEmb).filterM (fun vote => do
      if vote.slot = s then Protocol.targets_under (T.map blockToSpecEmb) (Block.toSpec B) vote
      else return false) with
  | error e => rw [hf] at h; cases h
  | ok w =>
    rw [hf] at h
    have hw := filterM_eq_filter_of_ok _
      (fun u : GoldfishVote V => u.slot = s ∧
        DecoupledConsensusModel.Protocol.targets_under T B u.toProof = true)
      (by
        intro a b hab
        by_cases hs : a.slot = s
        · rw [if_pos hs] at hab
          rw [← GoldfishVote.toSpec_toProof a] at hab
          rw [targets_under_of_ok T B a.toProof hab]
          simp [hs]
        · rw [if_neg hs] at hab
          cases hab
          simp [hs])
      _ w hf
    subst hw
    rw [← Except.ok.inj h]
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true,
      decide_eq_true_eq, equivocates_map, DecoupledConsensusModel.Protocol.raw_supporters,
      DecoupledConsensusModel.Protocol.votes_by, Finset.mem_map]
    constructor
    · rintro ⟨he, _, ⟨⟨a, ha, rfl⟩, hs, ht⟩, hv⟩
      exact ⟨he, a, ⟨ha, hv⟩, hs, by simpa [voteToSpecEmb] using ht⟩
    · rintro ⟨he, a, ⟨ha, hv⟩, hs, ht⟩
      exact ⟨he, voteToSpecEmb a, ⟨⟨a, ha, rfl⟩, hs, by simpa [voteToSpecEmb] using ht⟩, hv⟩

/-- Where the spec's `raw_goldfish_score` answers on the spec forms of a tree, the votes, the
    support votes and a block, it answers `DecoupledConsensusModel.Protocol.goldfish_score`, for
    every environment. -/
theorem raw_goldfish_score_of_ok (E : DecoupledConsensusModel.Env V)
    (T : Finset (DecoupledConsensusModel.Block V))
    (votes support_votes : Finset (DecoupledConsensusModel.GoldfishVote V)) (s : Slot)
    (B : DecoupledConsensusModel.Block V) {n : ℕ}
    (h : Protocol.raw_goldfish_score (T.map blockToSpecEmb) (votes.map voteToSpecEmb)
      (support_votes.map voteToSpecEmb) s (Block.toSpec B) = .ok n) :
    n = DecoupledConsensusModel.Protocol.goldfish_score E T votes support_votes s B := by
  unfold Protocol.raw_goldfish_score at h
  cases hr : Protocol.raw_supporters (T.map blockToSpecEmb) (votes.map voteToSpecEmb)
      (support_votes.map voteToSpecEmb) s (Block.toSpec B) with
  | error e => rw [hr] at h; cases h
  | ok R =>
    rw [hr] at h
    have hR := raw_supporters_of_ok T votes support_votes s B hr
    subst hR
    have h' : (Except.ok (|Protocol.raw_equivocators (votes.map voteToSpecEmb)| +
        |DecoupledConsensusModel.Protocol.raw_supporters T votes support_votes s B|) :
        DC.DRE ℕ) = .ok n := h
    rw [← Except.ok.inj h', raw_equivocators_map]
    simp only [DecoupledConsensusModel.Protocol.goldfish_score,
      DecoupledConsensusModel.Protocol.raw_goldfish_score]

/-- Where the spec's `goldfish_eligible` answers on the spec forms of a tree, the votes and a block,
    with the state map `σ`, it answers `DecoupledConsensusModel.Protocol.goldfish_eligible` at the
    state map `fun C => (σ C).toProof`. -/
theorem goldfish_eligible_of_ok (E : DecoupledConsensusModel.Env V)
    (σ : DecoupledConsensusModel.Block V → Protocol.ChainState V) (h_max : Height)
    (T : Finset (DecoupledConsensusModel.Block V)) (cur : Slot)
    (votes support_votes : Finset (DecoupledConsensusModel.GoldfishVote V)) (s : Slot)
    (B : DecoupledConsensusModel.Block V) {b : Bool}
    (h : Protocol.goldfish_eligible (fun C => σ C.toProof) h_max (T.map blockToSpecEmb) cur
      (votes.map voteToSpecEmb) (support_votes.map voteToSpecEmb) s (Block.toSpec B) = .ok b) :
    b = DecoupledConsensusModel.Protocol.goldfish_eligible E (fun C => (σ C).toProof) h_max T cur
      votes support_votes s B := by
  unfold Protocol.goldfish_eligible at h
  cases hr : Protocol.raw_goldfish_score (T.map blockToSpecEmb) (votes.map voteToSpecEmb)
      (support_votes.map voteToSpecEmb) s (Block.toSpec B) with
  | error e => rw [hr] at h; cases h
  | ok n =>
    rw [hr] at h
    have hn := raw_goldfish_score_of_ok E T votes support_votes s B hr
    subst hn
    have h' : (Except.ok (decide ((σ (Block.toSpec B).parent.toProof).h < h_max - 1) ||
        decide (Protocol.raw_voters_count (votes.map voteToSpecEmb) <
          2 * DecoupledConsensusModel.Protocol.goldfish_score E T votes support_votes s B) ||
        decide ((Block.toSpec B).slot = cur)) : DC.DRE Bool) = .ok b := h
    rw [← Except.ok.inj h', raw_voters_count_map, toSpec_parent, Block.toProof_toSpec, toSpec_slot]
    unfold DecoupledConsensusModel.Protocol.goldfish_eligible
      DecoupledConsensusModel.Protocol.voters_count
    rfl

/-!
## The walk

The spec's walk takes a score `sc` and a test `el` that may raise. The lemmas of this section assume
that, on the spec form of every block, `sc` and `el` answer `sc'` and `el'` wherever they answer,
and conclude that the spec's walk, wherever it answers, answers the spec form of the walk with `sc'`
and `el'`.
-/

omit [Fintype V] in
/-- `DecoupledConsensusModel.pickUnique?` of the members of `S` that pass `p`, with the test `true`,
    is its pick of `S` with the test `p`. -/
theorem vocabulary_pickUnique?_filter {α : Type} [DecidableEq α] (S : Finset α) (p : α → Bool) :
    DecoupledConsensusModel.pickUnique? (S.filter (fun a => p a = true)) (fun _ => true) =
      DecoupledConsensusModel.pickUnique? S p := by
  unfold DecoupledConsensusModel.pickUnique?
  have hiff : (∃! a, a ∈ S.filter (fun a => p a = true) ∧ (fun _ => true) a = true) ↔
      (∃! a, a ∈ S ∧ p a = true) := by
    simp [Finset.mem_filter]
  by_cases h : ∃! a, a ∈ S ∧ p a = true
  · have h' := hiff.mpr h
    rw [dif_pos h', dif_pos h]
    congr 1
    have hc := Finset.choose_spec _ _ h
    have hc' := Finset.choose_spec _ _ h'
    have ⟨a, _, hu⟩ := h
    exact (hu _ (by simpa using hc'.1)).trans (hu _ hc).symm
  · rw [dif_neg (fun h' => h (hiff.mp h')), dif_neg h]

section Walk

variable (sc : Block V → DC.DRE ℕ) (el : Block V → DC.DRE Bool)
  (sc' : DecoupledConsensusModel.Block V → ℕ) (el' : DecoupledConsensusModel.Block V → Bool)

omit [Fintype V] in
/-- Where the spec's `outranks` answers on the spec forms of two blocks, it answers the
    `DecoupledConsensusModel` one with the score `sc'`. -/
theorem outranks_of_ok (hsc : ∀ C n, sc (Block.toSpec C) = .ok n → n = sc' C)
    (B C : DecoupledConsensusModel.Block V) {b : Bool}
    (h : Protocol.outranks sc (Block.toSpec B) (Block.toSpec C) = .ok b) :
    b = DecoupledConsensusModel.Protocol.outranks sc' B C := by
  unfold Protocol.outranks at h
  cases hB : sc (Block.toSpec B) with
  | error e => rw [hB] at h; cases h
  | ok nB =>
    cases hC : sc (Block.toSpec C) with
    | error e => rw [hB, hC] at h; cases h
    | ok nC =>
      rw [hB, hC] at h
      have h' : (Except.ok (decide (nC < nB) || (decide (nC = nB) &&
          decide ((Block.toSpec C).root < (Block.toSpec B).root))) : DC.DRE Bool) = .ok b := h
      rw [← Except.ok.inj h', hsc B nB hB, hsc C nC hC, toSpec_root, toSpec_root]
      unfold DecoupledConsensusModel.Protocol.outranks
      have hlt : (BlockId.toSpec C.root < BlockId.toSpec B.root) ↔ C.root < B.root := by
        rw [← BlockId.toProof_lt, BlockId.toProof_toSpec, BlockId.toProof_toSpec]
      simp only [hlt]

/-- Where the spec's `is_best_in` answers on the spec forms of a set and a block, it answers the
    `DecoupledConsensusModel` one with the score `sc'`. -/
theorem is_best_in_of_ok (hsc : ∀ C n, sc (Block.toSpec C) = .ok n → n = sc' C)
    (S : Finset (DecoupledConsensusModel.Block V)) (B : DecoupledConsensusModel.Block V)
    {b : Bool} (h : Protocol.is_best_in sc (S.map blockToSpecEmb) (Block.toSpec B) = .ok b) :
    b = DecoupledConsensusModel.Protocol.is_best_in sc' S B := by
  unfold Protocol.is_best_in at h
  cases hf : (S.map blockToSpecEmb).filterM (fun C => Protocol.outranks sc C (Block.toSpec B)) with
  | error e => rw [hf] at h; cases h
  | ok w =>
    rw [hf] at h
    have hw := filterM_eq_filter_of_ok_mem _
      (fun C : Block V => DecoupledConsensusModel.Protocol.outranks sc' C.toProof B = true) _
      (by
        intro a ha b' hab
        obtain ⟨C, _, rfl⟩ := Finset.mem_map.mp ha
        rw [outranks_of_ok sc sc' hsc C B hab]
        simp [blockToSpecEmb])
      w hf
    subst hw
    have h' : (Except.ok (decide ((S.map blockToSpecEmb).filter (fun C : Block V =>
        DecoupledConsensusModel.Protocol.outranks sc' C.toProof B = true) = ∅)) :
        DC.DRE Bool) = .ok b := h
    rw [← Except.ok.inj h']
    unfold DecoupledConsensusModel.Protocol.is_best_in
    rw [Finset.filter_map]
    simp only [Finset.map_eq_empty, Finset.filter_eq_empty_iff, Function.comp_apply,
      blockToSpecEmb, Function.Embedding.coeFn_mk, Block.toProof_toSpec, Bool.not_eq_true]

/-- Where the spec's `argmax?` answers on the spec form of a set, it answers the spec form of the
    `DecoupledConsensusModel` one with the score `sc'`. -/
theorem argmax?_of_ok (hsc : ∀ C n, sc (Block.toSpec C) = .ok n → n = sc' C)
    (S : Finset (DecoupledConsensusModel.Block V)) {o : Option (Block V)}
    (h : Protocol.argmax? sc (S.map blockToSpecEmb) = .ok o) :
    o = (DecoupledConsensusModel.Protocol.argmax? sc' S).map blockToSpecEmb := by
  unfold Protocol.argmax? at h
  cases hf : (S.map blockToSpecEmb).filterM (Protocol.is_best_in sc (S.map blockToSpecEmb)) with
  | error e => rw [hf] at h; cases h
  | ok w =>
    rw [hf] at h
    have hw := filterM_eq_filter_of_ok_mem _
      (fun C : Block V => DecoupledConsensusModel.Protocol.is_best_in sc' S C.toProof = true) _
      (by
        intro a ha b' hab
        obtain ⟨C, _, rfl⟩ := Finset.mem_map.mp ha
        rw [is_best_in_of_ok sc sc' hsc S C hab]
        simp [blockToSpecEmb])
      w hf
    subst hw
    have h' : (Except.ok (pickUnique? ((S.map blockToSpecEmb).filter (fun C : Block V =>
        DecoupledConsensusModel.Protocol.is_best_in sc' S C.toProof = true)) (fun _ => true)) :
        DC.DRE (Option (Block V))) = .ok o := h
    rw [← Except.ok.inj h', Finset.filter_map, pickUnique?_map]
    unfold DecoupledConsensusModel.Protocol.argmax?
    have hfe : S.filter ((fun C : Block V =>
        DecoupledConsensusModel.Protocol.is_best_in sc' S C.toProof = true) ∘ blockToSpecEmb) =
        S.filter (fun C => DecoupledConsensusModel.Protocol.is_best_in sc' S C = true) :=
      Finset.filter_congr (fun C _ => by simp [blockToSpecEmb])
    rw [hfe]
    exact congrArg (Option.map _) (vocabulary_pickUnique?_filter S _)

/-- Where the spec's `ghost_children` answers on the spec forms of a tree and a block, it answers
    the spec forms of the `DecoupledConsensusModel` one with the test `el'`. -/
theorem ghost_children_of_ok (hel : ∀ C b, el (Block.toSpec C) = .ok b → b = el' C)
    (tree : Finset (DecoupledConsensusModel.Block V)) (H : DecoupledConsensusModel.Block V)
    {w : Finset (Block V)}
    (h : Protocol.ghost_children (tree.map blockToSpecEmb) el (Block.toSpec H) = .ok w) :
    w = (DecoupledConsensusModel.Protocol.ghost_children tree el' H).map blockToSpecEmb := by
  unfold Protocol.ghost_children at h
  have hw := filterM_eq_filter_of_ok_mem _
    (fun B : Block V => B.parent? = some (Block.toSpec H) ∧ el' B.toProof = true) _
    (by
      intro a ha b hab
      obtain ⟨C, _, rfl⟩ := Finset.mem_map.mp ha
      by_cases hp : (blockToSpecEmb C).parent? = some (Block.toSpec H)
      · rw [if_pos hp] at hab
        rw [hel C b hab]
        simp only [blockToSpecEmb, Function.Embedding.coeFn_mk] at hp ⊢
        simp [hp]
      · rw [if_neg hp] at hab
        cases hab
        simp [hp])
    w h
  rw [hw, Finset.filter_map]
  unfold DecoupledConsensusModel.Protocol.ghost_children
  congr 1
  ext C
  simp only [Finset.mem_filter, Function.comp_apply, blockToSpecEmb, Function.Embedding.coeFn_mk,
    Block.toProof_toSpec, toSpec_parent?, Option.map_eq_some_iff]
  constructor
  · rintro ⟨hC, ⟨P, hP, hPH⟩, he⟩
    exact ⟨hC, by rw [hP, Block.toSpec_injective hPH], he⟩
  · rintro ⟨hC, hP, he⟩
    exact ⟨hC, ⟨H, hP, rfl⟩, he⟩

/-- Where the spec's `ghost_step` answers on the spec forms of a tree and a block, it answers the
    spec form of the `DecoupledConsensusModel` step. -/
theorem ghost_step_of_ok (hsc : ∀ C n, sc (Block.toSpec C) = .ok n → n = sc' C)
    (hel : ∀ C b, el (Block.toSpec C) = .ok b → b = el' C)
    (tree : Finset (DecoupledConsensusModel.Block V)) (H : DecoupledConsensusModel.Block V)
    {o : Option (Block V)}
    (h : Protocol.ghost_step (tree.map blockToSpecEmb) sc el (Block.toSpec H) = .ok o) :
    o = (DecoupledConsensusModel.Protocol.ghost_step tree sc' el' H).map blockToSpecEmb := by
  unfold Protocol.ghost_step at h
  cases hc : Protocol.ghost_children (tree.map blockToSpecEmb) el (Block.toSpec H) with
  | error e => rw [hc] at h; cases h
  | ok w =>
    rw [hc] at h
    rw [ghost_children_of_ok el el' hel tree H hc] at h
    unfold DecoupledConsensusModel.Protocol.ghost_step
    exact argmax?_of_ok sc sc' hsc _ h

/-- Where the spec's walk of at most `n` steps answers on the spec forms of a tree and a block, it
    answers the spec form of the `DecoupledConsensusModel` walk. -/
theorem ghost_walk_of_ok (hsc : ∀ C n, sc (Block.toSpec C) = .ok n → n = sc' C)
    (hel : ∀ C b, el (Block.toSpec C) = .ok b → b = el' C)
    (tree : Finset (DecoupledConsensusModel.Block V)) (n : ℕ)
    (H : DecoupledConsensusModel.Block V) {X : Block V}
    (h : Protocol.ghost_walk (tree.map blockToSpecEmb) sc el n (Block.toSpec H) = .ok X) :
    X = Block.toSpec (DecoupledConsensusModel.Protocol.ghost_walk tree sc' el' n H) := by
  induction n generalizing H with
  | zero =>
    rw [DecoupledConsensusModel.Protocol.ghost_walk]
    exact (Except.ok.inj h).symm
  | succ n ih =>
    unfold Protocol.ghost_walk at h
    unfold DecoupledConsensusModel.Protocol.ghost_walk
    cases hs : Protocol.ghost_step (tree.map blockToSpecEmb) sc el (Block.toSpec H) with
    | error e => rw [hs] at h; cases h
    | ok o =>
      rw [hs] at h
      have ho := ghost_step_of_ok sc el sc' el' hsc hel tree H hs
      cases hu : DecoupledConsensusModel.Protocol.ghost_step tree sc' el' H with
      | none =>
        rw [hu] at ho
        subst ho
        exact (Except.ok.inj h).symm
      | some C =>
        rw [hu] at ho
        subst ho
        exact ih C h

/-- Where the spec's `ghost` answers on the spec forms of an anchor and a tree, it answers the spec
    form of the `DecoupledConsensusModel` walk. -/
theorem ghost_of_ok (hsc : ∀ C n, sc (Block.toSpec C) = .ok n → n = sc' C)
    (hel : ∀ C b, el (Block.toSpec C) = .ok b → b = el' C)
    (anchor : DecoupledConsensusModel.Block V) (tree : Finset (DecoupledConsensusModel.Block V))
    {X : Block V}
    (h : Protocol.ghost (Block.toSpec anchor) (tree.map blockToSpecEmb) sc el = .ok X) :
    X = Block.toSpec (DecoupledConsensusModel.Protocol.ghost anchor tree sc' el') := by
  unfold Protocol.ghost at h
  rw [Finset.card_map] at h
  unfold DecoupledConsensusModel.Protocol.ghost
  exact ghost_walk_of_ok sc el sc' el' hsc hel tree _ anchor h

end Walk

/-!
## The walk at an embedding that keeps images, parents and ancestry

The same facts for any embedding `φ` of `DecoupledConsensusModel` blocks into the spec's that sends
every block to a block with that image, keeps parents and keeps ancestry, such as
`Store.blockOfImageEmb` on a store of the instance.
-/

section WalkAt

variable (φ : DecoupledConsensusModel.Block V ↪ Block V)
  (hφ : ∀ B, (φ B).toProof = B)
  (hφp : ∀ C H, (φ C).parent? = some (φ H) ↔ C.parent? = some H)
  (sc : Block V → DC.DRE ℕ) (el : Block V → DC.DRE Bool)
  (sc' : DecoupledConsensusModel.Block V → ℕ) (el' : DecoupledConsensusModel.Block V → Bool)

omit [DecidableEq V] [Fintype V] in
include hφ in
/-- Where the spec's `outranks` answers on `φ B` and `φ C`, it answers the `DecoupledConsensusModel`
    one on `B` and `C`, when the score answers `sc'` on every `φ C` (`hsc`). -/
theorem outranks_at (hsc : ∀ C n, sc (φ C) = .ok n → n = sc' C)
    (B C : DecoupledConsensusModel.Block V) {b : Bool}
    (h : Protocol.outranks sc (φ B) (φ C) = .ok b) :
    b = DecoupledConsensusModel.Protocol.outranks sc' B C := by
  unfold Protocol.outranks at h
  cases hB : sc (φ B) with
  | error e => rw [hB] at h; cases h
  | ok nB =>
    cases hC : sc (φ C) with
    | error e => rw [hB, hC] at h; cases h
    | ok nC =>
      rw [hB, hC] at h
      have h' : (Except.ok (decide (nC < nB) || (decide (nC = nB) &&
          decide ((φ C).root < (φ B).root))) : DC.DRE Bool) = .ok b := h
      rw [← Except.ok.inj h', hsc B nB hB, hsc C nC hC]
      unfold DecoupledConsensusModel.Protocol.outranks
      have hlt : (φ C).root < (φ B).root ↔ C.root < B.root := by
        rw [← BlockId.toProof_lt, ← Block.toProof_root, ← Block.toProof_root, hφ, hφ]
      simp only [hlt]

omit [Fintype V] in
include hφ in
/-- Where the spec's `is_best_in` answers on `S.map φ` and `φ B`, it answers the
    `DecoupledConsensusModel` one on `S` and `B`. -/
theorem is_best_in_at (hsc : ∀ C n, sc (φ C) = .ok n → n = sc' C)
    (S : Finset (DecoupledConsensusModel.Block V)) (B : DecoupledConsensusModel.Block V)
    {b : Bool} (h : Protocol.is_best_in sc (S.map φ) (φ B) = .ok b) :
    b = DecoupledConsensusModel.Protocol.is_best_in sc' S B := by
  unfold Protocol.is_best_in at h
  cases hf : (S.map φ).filterM (fun C => Protocol.outranks sc C (φ B)) with
  | error e => rw [hf] at h; cases h
  | ok w =>
    rw [hf] at h
    have hw := filterM_eq_filter_of_ok_mem _
      (fun C : Block V => DecoupledConsensusModel.Protocol.outranks sc' C.toProof B = true) _
      (by
        intro a ha b' hab
        obtain ⟨C, _, rfl⟩ := Finset.mem_map.mp ha
        rw [outranks_at φ hφ sc sc' hsc C B hab]
        simp [hφ])
      w hf
    subst hw
    have h' : (Except.ok (decide ((S.map φ).filter (fun C : Block V =>
        DecoupledConsensusModel.Protocol.outranks sc' C.toProof B = true) = ∅)) :
        DC.DRE Bool) = .ok b := h
    rw [← Except.ok.inj h']
    unfold DecoupledConsensusModel.Protocol.is_best_in
    rw [Finset.filter_map]
    simp only [Finset.map_eq_empty, Finset.filter_eq_empty_iff, Function.comp_apply, hφ,
      Bool.not_eq_true]

omit [Fintype V] in
include hφ in
/-- Where the spec's `argmax?` answers on `S.map φ`, it answers the block `φ` sends the
    `DecoupledConsensusModel` `argmax?` on `S` to. -/
theorem argmax?_at (hsc : ∀ C n, sc (φ C) = .ok n → n = sc' C)
    (S : Finset (DecoupledConsensusModel.Block V)) {o : Option (Block V)}
    (h : Protocol.argmax? sc (S.map φ) = .ok o) :
    o = (DecoupledConsensusModel.Protocol.argmax? sc' S).map φ := by
  unfold Protocol.argmax? at h
  cases hf : (S.map φ).filterM (Protocol.is_best_in sc (S.map φ)) with
  | error e => rw [hf] at h; cases h
  | ok w =>
    rw [hf] at h
    have hw := filterM_eq_filter_of_ok_mem _
      (fun C : Block V => DecoupledConsensusModel.Protocol.is_best_in sc' S C.toProof = true) _
      (by
        intro a ha b' hab
        obtain ⟨C, _, rfl⟩ := Finset.mem_map.mp ha
        rw [is_best_in_at φ hφ sc sc' hsc S C hab]
        simp [hφ])
      w hf
    subst hw
    have h' : (Except.ok (pickUnique? ((S.map φ).filter (fun C : Block V =>
        DecoupledConsensusModel.Protocol.is_best_in sc' S C.toProof = true)) (fun _ => true)) :
        DC.DRE (Option (Block V))) = .ok o := h
    rw [← Except.ok.inj h', Finset.filter_map, pickUnique?_map]
    unfold DecoupledConsensusModel.Protocol.argmax?
    have hfe : S.filter ((fun C : Block V =>
        DecoupledConsensusModel.Protocol.is_best_in sc' S C.toProof = true) ∘ φ) =
        S.filter (fun C => DecoupledConsensusModel.Protocol.is_best_in sc' S C = true) :=
      Finset.filter_congr (fun C _ => by simp [hφ])
    rw [hfe]
    exact congrArg (Option.map _) (vocabulary_pickUnique?_filter S _)

omit [Fintype V] in
include hφ hφp in
/-- Where the spec's `ghost_children` of `φ H` in `tree.map φ` answers, it answers the image under
    `φ` of the `DecoupledConsensusModel` children of `H` in `tree`, when `φ` keeps parents and the
    test answers `el'` (`hel`). -/
theorem ghost_children_at (hel : ∀ C b, el (φ C) = .ok b → b = el' C)
    (tree : Finset (DecoupledConsensusModel.Block V)) (H : DecoupledConsensusModel.Block V)
    {w : Finset (Block V)}
    (h : Protocol.ghost_children (tree.map φ) el (φ H) = .ok w) :
    w = (DecoupledConsensusModel.Protocol.ghost_children tree el' H).map φ := by
  unfold Protocol.ghost_children at h
  have hw := filterM_eq_filter_of_ok_mem _
    (fun B : Block V => B.parent? = some (φ H) ∧ el' B.toProof = true) _
    (by
      intro a ha b hab
      obtain ⟨C, _, rfl⟩ := Finset.mem_map.mp ha
      by_cases hp : (φ C).parent? = some (φ H)
      · rw [if_pos hp] at hab
        rw [hel C b hab, hφ]
        simp [hp]
      · rw [if_neg hp] at hab
        cases hab
        simp [hp])
    w h
  rw [hw, Finset.filter_map]
  unfold DecoupledConsensusModel.Protocol.ghost_children
  congr 1
  ext C
  simp only [Finset.mem_filter, Function.comp_apply, hφ, hφp]

omit [Fintype V] in
include hφ hφp in
/-- Where one step of the spec's walk from `φ H` through `tree.map φ` answers, it answers the block
    `φ` sends the `DecoupledConsensusModel` step from `H` to. -/
theorem ghost_step_at (hsc : ∀ C n, sc (φ C) = .ok n → n = sc' C)
    (hel : ∀ C b, el (φ C) = .ok b → b = el' C)
    (tree : Finset (DecoupledConsensusModel.Block V)) (H : DecoupledConsensusModel.Block V)
    {o : Option (Block V)}
    (h : Protocol.ghost_step (tree.map φ) sc el (φ H) = .ok o) :
    o = (DecoupledConsensusModel.Protocol.ghost_step tree sc' el' H).map φ := by
  unfold Protocol.ghost_step at h
  cases hc : Protocol.ghost_children (tree.map φ) el (φ H) with
  | error e => rw [hc] at h; cases h
  | ok w =>
    rw [hc] at h
    rw [ghost_children_at φ hφ hφp el el' hel tree H hc] at h
    unfold DecoupledConsensusModel.Protocol.ghost_step
    exact argmax?_at φ hφ sc sc' hsc _ h

omit [Fintype V] in
include hφ hφp in
/-- Where the spec's walk of `n` steps from `φ H` answers, it answers the block `φ` sends the
    `DecoupledConsensusModel` walk of `n` steps from `H` to. -/
theorem ghost_walk_at (hsc : ∀ C n, sc (φ C) = .ok n → n = sc' C)
    (hel : ∀ C b, el (φ C) = .ok b → b = el' C)
    (tree : Finset (DecoupledConsensusModel.Block V)) (n : ℕ)
    (H : DecoupledConsensusModel.Block V) {X : Block V}
    (h : Protocol.ghost_walk (tree.map φ) sc el n (φ H) = .ok X) :
    X = φ (DecoupledConsensusModel.Protocol.ghost_walk tree sc' el' n H) := by
  induction n generalizing H with
  | zero =>
    rw [DecoupledConsensusModel.Protocol.ghost_walk]
    exact (Except.ok.inj h).symm
  | succ n ih =>
    unfold Protocol.ghost_walk at h
    unfold DecoupledConsensusModel.Protocol.ghost_walk
    cases hs : Protocol.ghost_step (tree.map φ) sc el (φ H) with
    | error e => rw [hs] at h; cases h
    | ok o =>
      rw [hs] at h
      have ho := ghost_step_at φ hφ hφp sc el sc' el' hsc hel tree H hs
      cases hu : DecoupledConsensusModel.Protocol.ghost_step tree sc' el' H with
      | none =>
        rw [hu] at ho
        subst ho
        exact (Except.ok.inj h).symm
      | some C =>
        rw [hu] at ho
        subst ho
        exact ih C h

omit [Fintype V] in
include hφ hφp in
/-- Where the spec's `ghost` from `φ anchor` through `tree.map φ` answers, it answers the block `φ`
    sends the `DecoupledConsensusModel` `ghost` from `anchor` through `tree` to. -/
theorem ghost_at (hsc : ∀ C n, sc (φ C) = .ok n → n = sc' C)
    (hel : ∀ C b, el (φ C) = .ok b → b = el' C)
    (anchor : DecoupledConsensusModel.Block V) (tree : Finset (DecoupledConsensusModel.Block V))
    {X : Block V}
    (h : Protocol.ghost (φ anchor) (tree.map φ) sc el = .ok X) :
    X = φ (DecoupledConsensusModel.Protocol.ghost anchor tree sc' el') := by
  unfold Protocol.ghost at h
  rw [Finset.card_map] at h
  unfold DecoupledConsensusModel.Protocol.ghost
  exact ghost_walk_at φ hφ hφp sc el sc' el' hsc hel tree _ anchor h

end WalkAt

section ScoresAt

variable (φ : DecoupledConsensusModel.Block V ↪ Block V)
  (hφ : ∀ B, (φ B).toProof = B)

omit [DecidableEq V] [Fintype V] in
include hφ in
/-- The root of `φ B` is `BlockId.toSpec` of `B`'s root. -/
theorem root_at (B : DecoupledConsensusModel.Block V) : (φ B).root = BlockId.toSpec B.root := by
  have h := Block.toProof_root (φ B)
  rw [hφ] at h
  rw [h, BlockId.toSpec_toProof]

omit [DecidableEq V] [Fintype V] in
include hφ in
/-- The slot of `φ B` is `B`'s slot. -/
theorem slot_at (B : DecoupledConsensusModel.Block V) : (φ B).slot = B.slot := by
  conv_rhs => rw [← hφ B]
  generalize φ B = X
  cases X <;> simp [Block.toProof, DecoupledConsensusModel.Block.slot, Block.slot]

omit [DecidableEq V] [Fintype V] in
include hφ in
/-- When `φ` keeps parents (`hpar`), the optional parent of `φ C` is `C`'s optional parent mapped by
    `φ`. -/
theorem parent?_at (hpar : ∀ B, (φ B).parent = φ B.parent) (C : DecoupledConsensusModel.Block V) :
    (φ C).parent? = C.parent?.map φ := by
  have h1 := hφ C
  have h2 := hpar C
  cases hC : φ C with
  | genesis =>
    rw [hC] at h1
    subst h1
    simp [Block.toProof, Block.parent?, DecoupledConsensusModel.Block.parent?]
  | node q s r v su a p =>
    rw [hC] at h1 h2
    subst h1
    simp only [Block.parent?, Block.toProof, DecoupledConsensusModel.Block.parent?,
      Option.map_some] at h2 ⊢
    simp only [Block.parent, DecoupledConsensusModel.Block.parent] at h2
    rw [h2, hφ]

omit [DecidableEq V] [Fintype V] in
include hφ in
/-- `φ C` is a child of `φ H` exactly when `C` is a child of `H`. -/
theorem parent?_iff_at (hpar : ∀ B, (φ B).parent = φ B.parent)
    (C H : DecoupledConsensusModel.Block V) :
    (φ C).parent? = some (φ H) ↔ C.parent? = some H := by
  rw [parent?_at φ hφ hpar]
  cases C.parent? with
  | none => simp
  | some P => simp [φ.injective.eq_iff]

omit [Fintype V] in
include hφ in
/-- Where the spec's `blockWithRoot` answers on `T.map φ` and `BlockId.toSpec r`, it answers
    `DecoupledConsensusModel.Block.find? T r` mapped by `φ`. -/
theorem blockWithRoot_at (T : Finset (DecoupledConsensusModel.Block V))
    (r : DecoupledConsensusModel.BlockId) {o : Option (Block V)}
    (h : blockWithRoot (T.map φ) (BlockId.toSpec r) = .ok o) :
    o = (DecoupledConsensusModel.Block.find? T r).map φ := by
  unfold blockWithRoot at h
  split at h
  · cases h
  · have hf : Block.find? (T.map φ) (BlockId.toSpec r) =
        (DecoupledConsensusModel.Block.find? T r).map φ := by
      unfold Block.find? DecoupledConsensusModel.Block.find?
      rw [pickUnique?_map]
      congr 2
      funext B
      simp only [root_at φ hφ, blockIdToSpec_inj]
    rw [← hf]
    exact (Except.ok.inj h).symm

omit [Fintype V] in
include hφ in
/-- Where the spec's `targets_under` answers on `T.map φ`, `φ B` and the spec form of a vote, it
    answers `DecoupledConsensusModel.Protocol.targets_under`, when `φ` keeps ancestry (`hanc`). -/
theorem targets_under_at
    (hanc : ∀ A B, (φ A).ancestorEq (φ B) = DecoupledConsensusModel.Block.preceq A B)
    (T : Finset (DecoupledConsensusModel.Block V))
    (B : DecoupledConsensusModel.Block V) (vote : DecoupledConsensusModel.GoldfishVote V) {b : Bool}
    (h : Protocol.targets_under (T.map φ) (φ B) (GoldfishVote.toSpec vote) = .ok b) :
    b = DecoupledConsensusModel.Protocol.targets_under T B vote := by
  unfold Protocol.targets_under at h
  cases hb : blockWithRoot (T.map φ) (GoldfishVote.toSpec vote).head with
  | error e => rw [hb] at h; cases h
  | ok o =>
    rw [hb] at h
    have ho := blockWithRoot_at φ hφ T vote.head hb
    unfold DecoupledConsensusModel.Protocol.targets_under
    cases hf : DecoupledConsensusModel.Block.find? T vote.head with
    | none =>
      rw [hf] at ho
      subst ho
      exact (Except.ok.inj (h : (Except.ok false : DC.DRE Bool) = .ok b)).symm
    | some B' =>
      rw [hf] at ho
      subst ho
      have h' : (Except.ok (decide ((φ B').slot ≤ (GoldfishVote.toSpec vote).slot) &&
          (φ B).ancestorEq (φ B')) : DC.DRE Bool) = .ok b := h
      rw [← Except.ok.inj h', hanc, slot_at φ hφ]
      rfl

include hφ in
/-- Where the spec's `raw_supporters` answers on `T.map φ`, it answers
    `DecoupledConsensusModel.Protocol.raw_supporters`. -/
theorem raw_supporters_at
    (hanc : ∀ A B, (φ A).ancestorEq (φ B) = DecoupledConsensusModel.Block.preceq A B)
    (T : Finset (DecoupledConsensusModel.Block V))
    (votes support_votes : Finset (DecoupledConsensusModel.GoldfishVote V)) (s : Slot)
    (B : DecoupledConsensusModel.Block V) {R : Finset V}
    (h : Protocol.raw_supporters (T.map φ) (votes.map voteToSpecEmb)
      (support_votes.map voteToSpecEmb) s (φ B) = .ok R) :
    R = DecoupledConsensusModel.Protocol.raw_supporters T votes support_votes s B := by
  unfold Protocol.raw_supporters at h
  cases hf : (support_votes.map voteToSpecEmb).filterM (fun vote => do
      if vote.slot = s then Protocol.targets_under (T.map φ) (φ B) vote
      else return false) with
  | error e => rw [hf] at h; cases h
  | ok w =>
    rw [hf] at h
    have hw := filterM_eq_filter_of_ok _
      (fun u : GoldfishVote V => u.slot = s ∧
        DecoupledConsensusModel.Protocol.targets_under T B u.toProof = true)
      (by
        intro a b hab
        by_cases hs : a.slot = s
        · rw [if_pos hs] at hab
          rw [← GoldfishVote.toSpec_toProof a] at hab
          rw [targets_under_at φ hφ hanc T B a.toProof hab]
          simp [hs]
        · rw [if_neg hs] at hab
          cases hab
          simp [hs])
      _ w hf
    subst hw
    rw [← Except.ok.inj h]
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Bool.and_eq_true,
      decide_eq_true_eq, equivocates_map, DecoupledConsensusModel.Protocol.raw_supporters,
      DecoupledConsensusModel.Protocol.votes_by, Finset.mem_map]
    constructor
    · rintro ⟨he, _, ⟨⟨a, ha, rfl⟩, hs, ht⟩, hv⟩
      exact ⟨he, a, ⟨ha, hv⟩, hs, by simpa [voteToSpecEmb] using ht⟩
    · rintro ⟨he, a, ⟨ha, hv⟩, hs, ht⟩
      exact ⟨he, voteToSpecEmb a, ⟨⟨a, ha, rfl⟩, hs, by simpa [voteToSpecEmb] using ht⟩, hv⟩

include hφ in
/-- Where the spec's `raw_goldfish_score` answers on `T.map φ`, it answers
    `DecoupledConsensusModel.Protocol.goldfish_score`, for every environment. -/
theorem raw_goldfish_score_at
    (hanc : ∀ A B, (φ A).ancestorEq (φ B) = DecoupledConsensusModel.Block.preceq A B)
    (E : DecoupledConsensusModel.Env V)
    (T : Finset (DecoupledConsensusModel.Block V))
    (votes support_votes : Finset (DecoupledConsensusModel.GoldfishVote V)) (s : Slot)
    (B : DecoupledConsensusModel.Block V) {n : ℕ}
    (h : Protocol.raw_goldfish_score (T.map φ) (votes.map voteToSpecEmb)
      (support_votes.map voteToSpecEmb) s (φ B) = .ok n) :
    n = DecoupledConsensusModel.Protocol.goldfish_score E T votes support_votes s B := by
  unfold Protocol.raw_goldfish_score at h
  cases hr : Protocol.raw_supporters (T.map φ) (votes.map voteToSpecEmb)
      (support_votes.map voteToSpecEmb) s (φ B) with
  | error e => rw [hr] at h; cases h
  | ok R =>
    rw [hr] at h
    have hR := raw_supporters_at φ hφ hanc T votes support_votes s B hr
    subst hR
    have h' : (Except.ok (|Protocol.raw_equivocators (votes.map voteToSpecEmb)| +
        |DecoupledConsensusModel.Protocol.raw_supporters T votes support_votes s B|) :
        DC.DRE ℕ) = .ok n := h
    rw [← Except.ok.inj h', raw_equivocators_map]
    simp only [DecoupledConsensusModel.Protocol.goldfish_score,
      DecoupledConsensusModel.Protocol.raw_goldfish_score]

include hφ in
/-- Where the spec's `goldfish_eligible` answers on `T.map φ` with the state map `σ`, it answers
    `DecoupledConsensusModel.Protocol.goldfish_eligible` at the state map
    `fun C => (σ (φ C)).toProof`, when `φ` keeps ancestry and parents. -/
theorem goldfish_eligible_at
    (hanc : ∀ A B, (φ A).ancestorEq (φ B) = DecoupledConsensusModel.Block.preceq A B)
    (hpar : ∀ B, (φ B).parent = φ B.parent)
    (E : DecoupledConsensusModel.Env V)
    (σ : Block V → Protocol.ChainState V) (h_max : Height)
    (T : Finset (DecoupledConsensusModel.Block V)) (cur : Slot)
    (votes support_votes : Finset (DecoupledConsensusModel.GoldfishVote V)) (s : Slot)
    (B : DecoupledConsensusModel.Block V) {b : Bool}
    (h : Protocol.goldfish_eligible σ h_max (T.map φ) cur
      (votes.map voteToSpecEmb) (support_votes.map voteToSpecEmb) s (φ B) = .ok b) :
    b = DecoupledConsensusModel.Protocol.goldfish_eligible E (fun C => (σ (φ C)).toProof) h_max T
      cur votes support_votes s B := by
  unfold Protocol.goldfish_eligible at h
  cases hr : Protocol.raw_goldfish_score (T.map φ) (votes.map voteToSpecEmb)
      (support_votes.map voteToSpecEmb) s (φ B) with
  | error e => rw [hr] at h; cases h
  | ok n =>
    rw [hr] at h
    have hn := raw_goldfish_score_at φ hφ hanc E T votes support_votes s B hr
    subst hn
    have h' : (Except.ok (decide ((σ (φ B).parent).h < h_max - 1) ||
        decide (Protocol.raw_voters_count (votes.map voteToSpecEmb) <
          2 * DecoupledConsensusModel.Protocol.goldfish_score E T votes support_votes s B) ||
        decide ((φ B).slot = cur)) : DC.DRE Bool) = .ok b := h
    rw [← Except.ok.inj h', raw_voters_count_map, hpar, slot_at φ hφ]
    unfold DecoupledConsensusModel.Protocol.goldfish_eligible
      DecoupledConsensusModel.Protocol.voters_count
    rfl

include hφ in
/-- Where the spec's Goldfish fork choice answers from `φ anchor` through `tree.map φ`, with the
    tree `T.map φ`, it answers the block `φ` sends
    `DecoupledConsensusModel.Protocol.goldfish_fork_choice` to, at the state map
    `fun C => (σ (φ C)).toProof`. -/
theorem goldfish_fork_choice_at
    (hanc : ∀ A B, (φ A).ancestorEq (φ B) = DecoupledConsensusModel.Block.preceq A B)
    (hpar : ∀ B, (φ B).parent = φ B.parent)
    (E : DecoupledConsensusModel.Env V)
    (σ : Block V → Protocol.ChainState V) (h_max : Height)
    (T : Finset (DecoupledConsensusModel.Block V)) (cur : Slot)
    (anchor : DecoupledConsensusModel.Block V) (tree : Finset (DecoupledConsensusModel.Block V))
    (votes support_votes : Finset (DecoupledConsensusModel.GoldfishVote V)) (s : Slot)
    {Y : Block V}
    (h : Protocol.goldfish_fork_choice σ h_max (T.map φ) cur (φ anchor) (tree.map φ)
      (votes.map voteToSpecEmb) (support_votes.map voteToSpecEmb) s = .ok Y) :
    Y = φ (DecoupledConsensusModel.Protocol.goldfish_fork_choice E (fun C => (σ (φ C)).toProof)
      h_max T cur anchor tree votes support_votes s) := by
  unfold Protocol.goldfish_fork_choice at h
  rw [ghost_at φ hφ (parent?_iff_at φ hφ hpar) _ _ _ _
    (fun C _ h => raw_goldfish_score_at φ hφ hanc E T votes support_votes s C h)
    (fun C _ h => goldfish_eligible_at φ hφ hanc hpar E σ h_max T cur votes support_votes s C h)
    anchor tree h]
  unfold DecoupledConsensusModel.Protocol.goldfish_fork_choice
  rfl

end ScoresAt

end SpecRecord.ForkChoiceImages

namespace SpecRecord.ForkChoiceImages

open Spec
open SpecRecord.ForkChoiceGrades
open DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-!
## The filtered tree at a store of the instance

The instance's filtered tree within a block set `blocks` is the spec's, computed within the blocks
standing for `blocks` on the store and mapped back. Its blocks are always in the
`DecoupledConsensusModel` filtered tree of the store's image; the converse holds on a store of the
instance.
-/

omit [Fintype V] in
/-- The tree of the healing view of a store's image is the set of the images of the store's blocks. -/
theorem image_T (st : Store V) : st.toProof.toHealing.T = st.T.image Block.toProof := by
  unfold DecoupledConsensusModel.Protocol.Store.toHealing
  rfl

omit [Fintype V] in
/-- The chain state of `B` in the healing view of a store's image is the image of the store's chain
    state of the block standing for `B`. -/
theorem image_σ (st : Store V) (B : DecoupledConsensusModel.Block V) :
    st.toProof.toHealing.σ B = (st.σ (st.blockOfImage B)).toProof := by
  unfold DecoupledConsensusModel.Protocol.Store.toHealing
  rfl

omit [Fintype V] in
/-- The spec's filtered tree within `blocks`, written out: the blocks of `viable_tree` within
    `blocks` that are descendants of the fgroot. -/
theorem draft_filtered_from_def (st : Store V) (blocks : Finset (Block V)) :
    Protocol.get_filtered_block_tree_from st blocks =
      {B ∈ Protocol.viable_tree st.σ st.F st.h_max blocks |
        (Protocol.get_fg_root st).ancestorEq B = true} := rfl

/-- Every block of the instance's filtered tree of `st` within `blocks` is in
    `DecoupledConsensusModel.Protocol.get_filtered_block_tree_from` of the store's image within
    `blocks`. -/
theorem filtered_from_subset_vocabulary (st : Store V)
    (blocks : Finset (DecoupledConsensusModel.Block V)) :
    Member.get_filtered_block_tree_from st blocks ⊆
      DecoupledConsensusModel.Protocol.get_filtered_block_tree_from st.toProof.toHealing.toFG
        blocks := by
  intro B hB
  simp only [Member.get_filtered_block_tree_from, Finset.mem_image] at hB
  obtain ⟨X, hX, rfl⟩ := hB
  rw [draft_filtered_from_def] at hX
  simp only [Protocol.viable_tree, Protocol.finalized_descendants, Protocol.viable,
    Finset.mem_filter, Finset.mem_map, Store.coe_blockOfImageEmb, decide_eq_true_eq] at hX
  obtain ⟨⟨⟨⟨X₀, hX₀, rfl⟩, hF⟩, W, ⟨W₀, hW₀, rfl⟩, hXW, hh⟩, hroot⟩ := hX
  unfold DecoupledConsensusModel.Protocol.get_filtered_block_tree_from
    DecoupledConsensusModel.Protocol.viable_tree DecoupledConsensusModel.Protocol.finalized_descendants
    DecoupledConsensusModel.Protocol.viable
  rw [toProof_get_fg_root]
  simp only [Finset.mem_filter, decide_eq_true_eq, Store.toProof_blockOfImage]
  have hF' := Block.toProof_preceq_of_ancestorEq _ _ hF
  have hXW' := Block.toProof_preceq_of_ancestorEq _ _ hXW
  have hroot' := Block.toProof_preceq_of_ancestorEq _ _ hroot
  rw [Store.toProof_blockOfImage] at hF' hroot' hXW'
  rw [Store.toProof_blockOfImage] at hXW'
  rw [Store.ofImage_F, Store.toProof_blockOfImage] at hF'
  rw [Store.toProof_get_fg_root_ofImage] at hroot'
  refine ⟨⟨⟨hX₀, ?_⟩, W₀, hW₀, ?_, ?_⟩, hroot'⟩
  · rw [toProof_fg_F]; exact hF'
  · unfold DecoupledConsensusModel.Block.Preceq; exact hXW'
  · rw [toProof_fg_h_max, image_σ]; exact hh

/-- On a store of the instance, the instance's filtered tree within `blocks` is
    `DecoupledConsensusModel.Protocol.get_filtered_block_tree_from` of the store's image within
    `blocks`. -/
theorem filtered_from_eq_vocabulary (st : OkStore V)
    (blocks : Finset (DecoupledConsensusModel.Block V)) :
    Member.get_filtered_block_tree_from st.val blocks =
      DecoupledConsensusModel.Protocol.get_filtered_block_tree_from
        st.val.toProof.toHealing.toFG blocks := by
  obtain ⟨-, hT, hpar, hFT⟩ := st.property
  have hinj := hT.injOn_toProof
  refine Finset.Subset.antisymm (filtered_from_subset_vocabulary st.val blocks) ?_
  intro B hB
  unfold DecoupledConsensusModel.Protocol.get_filtered_block_tree_from
    DecoupledConsensusModel.Protocol.viable_tree DecoupledConsensusModel.Protocol.finalized_descendants
    DecoupledConsensusModel.Protocol.viable at hB
  rw [toProof_get_fg_root] at hB
  simp only [Finset.mem_filter, decide_eq_true_eq] at hB
  obtain ⟨⟨⟨hBb, hF⟩, W₀, hW₀, hBW, hh⟩, hr⟩ := hB
  simp only [Member.get_filtered_block_tree_from, Finset.mem_image]
  refine ⟨st.val.blockOfImage B, ?_, Store.toProof_blockOfImage _ _⟩
  rw [draft_filtered_from_def]
  simp only [Protocol.viable_tree, Protocol.finalized_descendants, Protocol.viable,
    Finset.mem_filter, Finset.mem_map, Store.coe_blockOfImageEmb, decide_eq_true_eq]
  refine ⟨⟨⟨⟨B, hBb, rfl⟩, ?_⟩, st.val.blockOfImage W₀, ⟨W₀, hW₀, rfl⟩, ?_, ?_⟩, ?_⟩
  · rw [Store.ofImage_F, Store.blockOfImage_ancestorEq st.val hinj hpar]
    rw [toProof_fg_F] at hF; exact hF
  · show (st.val.blockOfImage B).ancestorEq (st.val.blockOfImage W₀) = true
    rw [Store.blockOfImage_ancestorEq st.val hinj hpar]
    unfold DecoupledConsensusModel.Block.Preceq at hBW; exact hBW
  · rw [toProof_fg_h_max, image_σ] at hh; exact hh
  · rw [Store.get_fg_root_ofImage, Store.blockOfImage_ancestorEq st.val hinj hpar]; exact hr

/-- On a store of the instance, the instance's filtered tree is its filtered tree within the images
    of the store's tree. -/
theorem filtered_eq_from_image (st : OkStore V) :
    Member.get_filtered_block_tree st.val =
      Member.get_filtered_block_tree_from st.val (st.val.T.image Block.toProof) := by
  obtain ⟨-, hT, -, -⟩ := st.property
  have hinj := hT.injOn_toProof
  have hmap : (st.val.T.image Block.toProof).map st.val.blockOfImageEmb = st.val.T := by
    ext X
    simp only [Finset.mem_map, Finset.mem_image, Store.coe_blockOfImageEmb]
    constructor
    · rintro ⟨_, ⟨Y, hY, rfl⟩, rfl⟩
      rw [Store.blockOfImage_toProof_of_injOn st.val hinj hY]; exact hY
    · intro hX
      exact ⟨X.toProof, ⟨X, hX, rfl⟩, Store.blockOfImage_toProof_of_injOn st.val hinj hX⟩
  simp only [Member.get_filtered_block_tree, Member.get_filtered_block_tree_from, hmap,
    Protocol.get_filtered_block_tree, Store.ofImage_T]

/-- On a store of the instance, every block of the instance's filtered tree is in
    `DecoupledConsensusModel.Protocol.get_filtered_block_tree` of the store's image. -/
theorem filtered_subset_vocabulary (st : OkStore V) :
    Member.get_filtered_block_tree st.val ⊆
      DecoupledConsensusModel.Protocol.get_filtered_block_tree st.val.toProof.toHealing.toFG := by
  rw [filtered_eq_from_image]
  unfold DecoupledConsensusModel.Protocol.get_filtered_block_tree
  rw [image_T]
  exact filtered_from_subset_vocabulary st.val (st.val.T.image Block.toProof)

/-- On a store of the instance, the instance's filtered tree is
    `DecoupledConsensusModel.Protocol.get_filtered_block_tree` of the store's image. -/
theorem filtered_eq_vocabulary (st : OkStore V) :
    Member.get_filtered_block_tree st.val =
      DecoupledConsensusModel.Protocol.get_filtered_block_tree st.val.toProof.toHealing.toFG := by
  rw [filtered_eq_from_image]
  unfold DecoupledConsensusModel.Protocol.get_filtered_block_tree
  rw [image_T]
  exact filtered_from_eq_vocabulary st (st.val.T.image Block.toProof)

/-!
## The views at a store of the instance

The image of a store as a Goldfish store is `st.toProof.toHealing.toFG.toSG.toGoldfishStore`; the
lemmas here read its fields back as the store's.
-/

omit [Fintype V] in
/-- The slot of the image of a block is the block's slot. -/
theorem toProof_slot (B : Block V) : B.toProof.slot = B.slot := by
  cases B <;> simp [Block.toProof, DecoupledConsensusModel.Block.slot, Block.slot]

omit [Fintype V] in
/-- The included Goldfish votes of the image of a block are the images of the block's. -/
theorem toProof_gf_votes (B : Block V) :
    B.toProof.gf_votes = B.gf_votes.map GoldfishVote.toProof := by
  cases B <;> simp [Block.toProof, DecoupledConsensusModel.Block.gf_votes, Block.gf_votes]

omit [Fintype V] in
/-- The included support votes of the image of a block are the images of the block's. -/
theorem toProof_gf_support_votes (B : Block V) :
    B.toProof.gf_support_votes = B.gf_support_votes.map GoldfishVote.toProof := by
  cases B <;> simp [Block.toProof, DecoupledConsensusModel.Block.gf_support_votes,
    Block.gf_support_votes]

omit [Fintype V] in
/-- The tree of the image of a store, as a Goldfish store, is the images of its blocks. -/
theorem image_gs_T (st : Store V) :
    st.toProof.toHealing.toFG.toSG.toGoldfishStore.T = st.T.image Block.toProof := by
  unfold DecoupledConsensusModel.Protocol.Store.toHealing
  rfl

omit [Fintype V] in
/-- The image of a store, as a Goldfish store, stamps a vote as the store stamps the vote's spec
    form. -/
theorem image_gs_timestamp_vote (st : Store V) (u : DecoupledConsensusModel.GoldfishVote V) :
    st.toProof.toHealing.toFG.toSG.toGoldfishStore.timestamp_vote u =
      st.timestamp_vote (GoldfishVote.toSpec u) := by
  unfold DecoupledConsensusModel.Protocol.Store.toHealing
  rfl

omit [Fintype V] in
/-- The image of a store, as a Goldfish store, stamps a block as the store stamps the block standing
    for it. -/
theorem image_gs_timestamp_block (st : Store V) (B : DecoupledConsensusModel.Block V) :
    st.toProof.toHealing.toFG.toSG.toGoldfishStore.timestamp_block B =
      st.timestamp_block (st.blockOfImage B) := by
  unfold DecoupledConsensusModel.Protocol.Store.toHealing
  rfl

omit [Fintype V] in
/-- The Goldfish votes of slot `s` of the image of a store, as a Goldfish store, are the images of
    the store's. -/
theorem image_gs_gf_votes (st : Store V) (s : Slot) :
    st.toProof.toHealing.toFG.toSG.toGoldfishStore.gf_votes s =
      (st.gf_votes s).map GoldfishVote.toProof := by
  unfold DecoupledConsensusModel.Protocol.Store.toHealing
  rfl

omit [Fintype V] in
/-- The pool of slot `s` of the image of a store, as a Goldfish store, is the image of the store's
    pool. -/
theorem image_gs_pool (st : Store V) (s : Slot) :
    DecoupledConsensusModel.Protocol.GoldfishStore.pool
        st.toProof.toHealing.toFG.toSG.toGoldfishStore s =
      (st.pool s).map GoldfishVote.toProofEmb :=
  toProof_gs_pool st s

omit [Fintype V] in
/-- `DecoupledConsensusModel.beforeCutoff` of the image of a vote set, read with the stamps of the
    spec forms, is the image of the cutoff of the set. -/
theorem beforeCutoff_map (ts : TimestampMap (GoldfishVote V)) (Γ : Time)
    (S : Finset (GoldfishVote V)) :
    (DecoupledConsensusModel.beforeCutoff ts Γ S).map GoldfishVote.toProofEmb =
      DecoupledConsensusModel.beforeCutoff (fun u => ts (GoldfishVote.toSpec u)) Γ
        (S.map GoldfishVote.toProofEmb) := by
  unfold DecoupledConsensusModel.beforeCutoff
  rw [Finset.filter_map]
  congr 2
  funext u
  simp [DecoupledConsensusModel.stampedBefore]

omit [Fintype V] in
/-- The image of the votes included in a store's slot-`s` blocks is the set of the votes included in
    the images of the slot-`s` blocks. -/
theorem included_votes_map (st : Store V) (s : Slot) :
    (st.included_votes s).map GoldfishVote.toProofEmb =
      ((st.T.image Block.toProof).filter (fun B => B.slot = s)).biUnion (fun B =>
        B.gf_votes.toFinset.filter (fun vote => vote.slot = s - 1)) := by
  ext u
  simp only [Store.included_votes, Finset.mem_map, Finset.mem_biUnion, Finset.mem_filter,
    Finset.mem_image, List.mem_toFinset, GoldfishVote.coe_toProofEmb]
  constructor
  · rintro ⟨v, ⟨B, ⟨hB, hBs⟩, hv, hvs⟩, rfl⟩
    refine ⟨B.toProof, ⟨⟨B, hB, rfl⟩, by rw [toProof_slot]; exact hBs⟩, ?_, hvs⟩
    rw [toProof_gf_votes]; exact List.mem_map_of_mem hv
  · rintro ⟨_, ⟨⟨B, hB, rfl⟩, hBs⟩, hu, hus⟩
    rw [toProof_gf_votes, List.mem_map] at hu
    obtain ⟨v, hv, rfl⟩ := hu
    exact ⟨v, ⟨B, ⟨hB, by rw [← toProof_slot]; exact hBs⟩, hv, hus⟩, rfl⟩

/-- The member `voter_view` of `Model.spec` at a store `st` of the instance is the member
    `voter_view` of `Model.vocabulary` at the store's image. -/
theorem spec_voter_view_eq (E : DecoupledConsensusModel.Env V) (st : OkStore V) (s : Slot) :
    (Model.spec (V := V)).voter_view E st s =
      (Model.vocabulary (V := V)).voter_view E st.val.toProof.toHealing.toFG.toSG.toGoldfishStore s := by
  obtain ⟨hst, -, -, -⟩ := st.property
  show successOutcomes (Except.map (fun votes => votes.map GoldfishVote.toProofEmb)
    (Protocol.voter_view (Config.toSpec E unreadHealConfig unreadHeightConfig) st.val s)) =
    pure (DecoupledConsensusModel.Protocol.voter_view E
      st.val.toProof.toHealing.toFG.toSG.toGoldfishStore s)
  unfold Protocol.voter_view
  rw [beforeCutoff_eq_ok _ _ _ (fun _ hx => NoRaise.stamped_pool hst hx)]
  show successOutcomes (.ok ((DecoupledConsensusModel.beforeCutoff st.val.timestamp_vote
    ((Config.toSpec E unreadHealConfig unreadHeightConfig).view_freeze (s - 1))
    (st.val.pool (s - 1)) ∪ st.val.included_votes s).map GoldfishVote.toProofEmb)) = _
  rw [successOutcomes_ok, Finset.map_union, beforeCutoff_map, included_votes_map]
  unfold DecoupledConsensusModel.Protocol.voter_view
  rw [image_gs_pool, image_gs_T, ← toProof_view_freeze E unreadHealConfig unreadHeightConfig]
  congr 3
  funext u
  rw [image_gs_timestamp_vote]

/-! ## Equal members -/

/-- The member `equivocates` of `Model.spec` equals that of `Model.vocabulary`. -/
theorem spec_equivocates_eq :
    (Model.spec (V := V)).equivocates = (Model.vocabulary (V := V)).equivocates := by
  funext votes v
  show Protocol.equivocates (votes.map ChainStateToHandlers.goldfishVoteToSpecEmb) v =
    DecoupledConsensusModel.Protocol.equivocates votes v
  rw [← toProof_equivocates]
  congr 1
  ext u
  simp [ChainStateToHandlers.goldfishVoteToSpecEmb]

/-- The member `votes_by` of `Model.spec` equals that of `Model.vocabulary`. -/
theorem spec_votes_by_eq :
    (Model.spec (V := V)).votes_by = (Model.vocabulary (V := V)).votes_by := by
  funext votes v
  show (Protocol.votes_by (votes.map ChainStateToHandlers.goldfishVoteToSpecEmb) v).map
    GoldfishVote.toProofEmb = DecoupledConsensusModel.Protocol.votes_by votes v
  rw [← toProof_votes_by]
  congr 1
  ext u
  simp [ChainStateToHandlers.goldfishVoteToSpecEmb]

/-- The member `voters_count` of `Model.spec` equals that of `Model.vocabulary`. -/
theorem spec_voters_count_eq :
    (Model.spec (V := V)).voters_count = (Model.vocabulary (V := V)).voters_count := by
  funext E votes s
  show Protocol.raw_voters_count (votes.map voteToSpecEmb) =
    DecoupledConsensusModel.Protocol.voters_count E votes s
  rw [raw_voters_count_map]
  unfold DecoupledConsensusModel.Protocol.voters_count
  rfl

/-- The member `no_second_vote_in` of `Model.spec` equals that of `Model.vocabulary`. -/
theorem spec_no_second_vote_in_eq :
    (Model.spec (V := V)).no_second_vote_in =
      (Model.vocabulary (V := V)).no_second_vote_in := by
  funext late vote
  show Protocol.no_second_vote_in (late.map voteToSpecEmb) (GoldfishVote.toSpec vote) =
    DecoupledConsensusModel.Protocol.no_second_vote_in late vote
  rw [← toProof_no_second_vote_in, map_voteToSpec_map_toProof, GoldfishVote.toProof_toSpec]

/-- The member `targets_under` of `Model.spec` equals that of `Model.vocabulary`. -/
theorem spec_targets_under_eq :
    (Model.spec (V := V)).targets_under = (Model.vocabulary (V := V)).targets_under := by
  funext T B vote
  exact successOutcomes_orVocabulary _ _ (fun _ h => targets_under_of_ok T B vote h)

/-- The member `raw_supporters` of `Model.spec` equals that of `Model.vocabulary`. -/
theorem spec_raw_supporters_eq :
    (Model.spec (V := V)).raw_supporters = (Model.vocabulary (V := V)).raw_supporters := by
  funext T votes support_votes s B
  exact successOutcomes_orVocabulary _ _
    (fun _ h => raw_supporters_of_ok T votes support_votes s B h)

/-- The member `goldfish_score` of `Model.spec` equals that of `Model.vocabulary`. -/
theorem spec_goldfish_score_eq :
    (Model.spec (V := V)).goldfish_score = (Model.vocabulary (V := V)).goldfish_score := by
  funext E T votes support_votes s B
  exact successOutcomes_orVocabulary _ _
    (fun _ h => raw_goldfish_score_of_ok E T votes support_votes s B h)

/-- The member `goldfish_eligible` of `Model.spec` at a map `σ` to the spec's chain states
    equals that of `Model.vocabulary` at the map `fun C => (σ C).toProof`. -/
theorem spec_goldfish_eligible_eq (E : DecoupledConsensusModel.Env V)
    (σ : DecoupledConsensusModel.Block V → Protocol.ChainState V) :
    (Model.spec (V := V)).goldfish_eligible E σ =
      (Model.vocabulary (V := V)).goldfish_eligible E (fun C => (σ C).toProof) := by
  funext h_max T cur votes support_votes s B
  exact successOutcomes_orVocabulary _ _
    (fun _ h => goldfish_eligible_of_ok E σ h_max T cur votes support_votes s B h)

/-- The member `ghost_step` of `Model.spec` equals that of `Model.vocabulary`. -/
theorem spec_ghost_step_eq :
    (Model.spec (V := V)).ghost_step = (Model.vocabulary (V := V)).ghost_step := by
  funext tree score eligible H
  obtain ⟨o, ho⟩ := NoRaise.ghost_step_ok
    (score := fun C : Block V => (pure (score C.toProof) : DC.DRE ℕ))
    (eligible := fun C : Block V => (pure (eligible C.toProof) : DC.DRE Bool))
    (fun _ => ⟨_, rfl⟩) (fun _ => ⟨_, rfl⟩) (tree.map blockToSpecEmb) (Block.toSpec H)
  have hv := ghost_step_of_ok _ _ score eligible
    (fun C _ h => (Except.ok.inj h).symm.trans (by rw [Block.toProof_toSpec]))
    (fun C _ h => (Except.ok.inj h).symm.trans (by rw [Block.toProof_toSpec])) tree H ho
  show successOutcomes (Except.map (Option.map Block.toProof)
    (Protocol.ghost_step (tree.map blockToSpecEmb) (fun C => pure (score C.toProof))
      (fun C => pure (eligible C.toProof)) (Block.toSpec H))) = _
  rw [ho, hv]
  show (pure ((Option.map Block.toProof (Option.map blockToSpecEmb
    (DecoupledConsensusModel.Protocol.ghost_step tree score eligible H)))) : DC.NDRE _) = _
  rw [Option.map_map]
  simp [blockToSpecEmb, Function.comp_def, Model.vocabulary]

/-- The member `ghost` of `Model.spec` equals that of `Model.vocabulary`. -/
theorem spec_ghost_eq :
    (Model.spec (V := V)).ghost = (Model.vocabulary (V := V)).ghost := by
  funext B tree score eligible
  obtain ⟨X, hX⟩ := NoRaise.ghost_ok
    (score := fun C : Block V => (pure (score C.toProof) : DC.DRE ℕ))
    (eligible := fun C : Block V => (pure (eligible C.toProof) : DC.DRE Bool))
    (fun _ => ⟨_, rfl⟩) (fun _ => ⟨_, rfl⟩) (Block.toSpec B) (tree.map blockToSpecEmb)
  have hv := ghost_of_ok _ _ score eligible
    (fun C _ h => (Except.ok.inj h).symm.trans (by rw [Block.toProof_toSpec]))
    (fun C _ h => (Except.ok.inj h).symm.trans (by rw [Block.toProof_toSpec])) B tree hX
  show successOutcomes (Except.map Block.toProof
    (Protocol.ghost (Block.toSpec B) (tree.map blockToSpecEmb) (fun C => pure (score C.toProof))
      (fun C => pure (eligible C.toProof)))) = _
  rw [hX, hv]
  show (pure (Block.toProof (Block.toSpec
    (DecoupledConsensusModel.Protocol.ghost B tree score eligible))) : DC.NDRE _) = _
  rw [Block.toProof_toSpec]
  rfl

/-- Every outcome of the member `goldfish_fork_choice` of `Model.spec` at a map `σ` to the
    spec's chain states is `DecoupledConsensusModel.Protocol.goldfish_fork_choice` at the map
    `fun C => (σ C).toProof`. -/
theorem spec_goldfish_fork_choice_of_returns (E : DecoupledConsensusModel.Env V)
    (σ : DecoupledConsensusModel.Block V → Protocol.ChainState V) (h_max : Height)
    (T : Finset (DecoupledConsensusModel.Block V)) (cur : Slot)
    (anchor : DecoupledConsensusModel.Block V) (tree : Finset (DecoupledConsensusModel.Block V))
    (votes support_votes : Finset (DecoupledConsensusModel.GoldfishVote V)) (s : Slot)
    {X : DecoupledConsensusModel.Block V}
    (hX : (Model.spec (V := V)).goldfish_fork_choice E σ h_max T cur anchor tree votes
      support_votes s ⇢ X) :
    X = DecoupledConsensusModel.Protocol.goldfish_fork_choice E (fun C => (σ C).toProof) h_max T
      cur anchor tree votes support_votes s := by
  change successOutcomes (orVocabulary (Except.map Block.toProof
    (Protocol.goldfish_fork_choice (fun C => σ C.toProof) h_max (T.map blockToSpecEmb) cur
      (Block.toSpec anchor) (tree.map blockToSpecEmb) (votes.map voteToSpecEmb)
      (support_votes.map voteToSpecEmb) s))
    (DecoupledConsensusModel.Protocol.goldfish_fork_choice E (fun C => (σ C).toProof) h_max T cur
      anchor tree votes support_votes s)) ⇢ X at hX
  rw [returns_successOutcomes] at hX
  cases hd : Protocol.goldfish_fork_choice (fun C => σ C.toProof) h_max (T.map blockToSpecEmb) cur
      (Block.toSpec anchor) (tree.map blockToSpecEmb) (votes.map voteToSpecEmb)
      (support_votes.map voteToSpecEmb) s with
  | error e =>
    rw [hd] at hX
    exact (Except.ok.inj hX).symm
  | ok Y =>
    rw [hd] at hX
    have hY := ghost_of_ok _ _ _ _
      (fun C _ h => raw_goldfish_score_of_ok E T votes support_votes s C h)
      (fun C _ h => goldfish_eligible_of_ok E σ h_max T cur votes support_votes s C h)
      anchor tree hd
    have hXY : Y.toProof = X := Except.ok.inj hX
    rw [← hXY, hY, Block.toProof_toSpec]
    unfold DecoupledConsensusModel.Protocol.goldfish_fork_choice
    rfl

/-- Every outcome of the member `goldfish_fork_choice` of `Model.spec` is an outcome of the
    same member of `Model.vocabulary` at the mapped chain states. -/
theorem vocabulary_returns_of_spec_goldfish_fork_choice (E : DecoupledConsensusModel.Env V)
    (σ : DecoupledConsensusModel.Block V → Protocol.ChainState V) (h_max : Height)
    (T : Finset (DecoupledConsensusModel.Block V)) (cur : Slot)
    (anchor : DecoupledConsensusModel.Block V) (tree : Finset (DecoupledConsensusModel.Block V))
    (votes support_votes : Finset (DecoupledConsensusModel.GoldfishVote V)) (s : Slot)
    {X : DecoupledConsensusModel.Block V}
    (hX : (Model.spec (V := V)).goldfish_fork_choice E σ h_max T cur anchor tree votes
      support_votes s ⇢ X) :
    (Model.vocabulary (V := V)).goldfish_fork_choice E (fun C => (σ C).toProof) h_max T cur anchor
      tree votes support_votes s ⇢ X := by
  rw [spec_goldfish_fork_choice_of_returns E σ h_max T cur anchor tree votes support_votes s
    hX]
  exact (returns_pure _ _).mpr rfl

/-- The member `goldfish_fork_choice` of `Model.spec` at a map `σ` to the spec's chain states
    equals that of `Model.vocabulary` at the map `fun C => (σ C).toProof`. -/
theorem spec_goldfish_fork_choice_eq (E : DecoupledConsensusModel.Env V)
    (σ : DecoupledConsensusModel.Block V → Protocol.ChainState V) :
    (Model.spec (V := V)).goldfish_fork_choice E σ =
      (Model.vocabulary (V := V)).goldfish_fork_choice E (fun C => (σ C).toProof) := by
  funext h_max T cur anchor tree votes support_votes s
  refine successOutcomes_orVocabulary _ _ (fun b hb => ?_)
  apply spec_goldfish_fork_choice_of_returns E σ h_max T cur anchor tree votes support_votes s
  show Returns (successOutcomes (orVocabulary _ _)) b
  rw [hb]
  exact (returns_successOutcomes _ _).2 rfl

/-! ## The support views, the processed tree and the voter's filtered tree -/

/-- The member `view_freeze` of `Model.spec` equals that of `Model.vocabulary`. -/
theorem spec_view_freeze_eq :
    (Model.spec (V := V)).view_freeze = (Model.vocabulary (V := V)).view_freeze := by
  funext E s
  exact (toProof_view_freeze E unreadHealConfig unreadHeightConfig s).symm

/-- The member `gs_pool` of `Model.spec` at a store of the instance is the member `gs_pool` of
    `Model.vocabulary` at the store's image. -/
theorem spec_gs_pool_eq (gs : OkStore V) (s : Slot) :
    (Model.spec (V := V)).gs_pool gs s =
      (Model.vocabulary (V := V)).gs_pool gs.val.toProof.toHealing.toFG.toSG.toGoldfishStore s :=
  (ForkChoiceImages.image_gs_pool gs.val s).symm


/-- Where the spec's `Protocol.resolved` answers on the spec forms of a tree and a vote, it answers
    `DecoupledConsensusModel.Protocol.resolved`. -/
theorem resolved_of_ok (T : Finset (DecoupledConsensusModel.Block V))
    (u : DecoupledConsensusModel.GoldfishVote V) {b : Bool}
    (h : Protocol.resolved (T.map ChainStateToHandlers.blockToSpecEmb) (GoldfishVote.toSpec u) =
      .ok b) :
    b = DecoupledConsensusModel.Protocol.resolved T u := by
  unfold Protocol.resolved at h
  cases hb : blockWithRoot (T.map ChainStateToHandlers.blockToSpecEmb) (GoldfishVote.toSpec u).head with
  | error e => rw [hb] at h; cases h
  | ok o =>
    rw [hb] at h
    have ho := blockWithRoot_map_of_ok T ChainStateToHandlers.blockToSpecEmb (fun _ => rfl) u.head hb
    unfold DecoupledConsensusModel.Protocol.resolved
    cases hf : DecoupledConsensusModel.Block.find? T u.head with
    | none =>
      rw [hf] at ho
      subst ho
      exact (Except.ok.inj (h : (Except.ok false : DC.DRE Bool) = .ok b)).symm
    | some B' =>
      rw [hf] at ho
      subst ho
      have h' : (Except.ok (decide ((Block.toSpec B').slot ≤ (GoldfishVote.toSpec u).slot)) :
          DC.DRE Bool) = .ok b := h
      rw [← Except.ok.inj h', toSpec_slot]
      rfl

/-- The member `resolved` of `Model.spec` equals that of `Model.vocabulary`. -/
theorem spec_resolved_eq :
    (Model.spec (V := V)).resolved = (Model.vocabulary (V := V)).resolved := by
  funext T u
  exact successOutcomes_orVocabulary _ _ (fun _ h => resolved_of_ok T u h)

/-- The member `voter_processed_block_tree` of `Model.spec` at a store `st` of the instance is
    the same member of `Model.vocabulary` at the store's image. -/
theorem spec_voter_processed_block_tree_eq (E : DecoupledConsensusModel.Env V)
    (st : OkStore V) (s : Slot) :
    (Model.spec (V := V)).voter_processed_block_tree E st s =
      (Model.vocabulary (V := V)).voter_processed_block_tree E
        st.val.toProof.toHealing.toFG.toSG.toGoldfishStore s := by
  obtain ⟨hst, hT, hpar, -⟩ := st.property
  have hinj := hT.injOn_toProof
  obtain ⟨v, hv⟩ := NoRaise.voter_processed_block_tree_ok
    (Config.toSpec E unreadHealConfig unreadHeightConfig) hst s
  show successOutcomes (Except.map (fun T => T.image Block.toProof)
    (Protocol.voter_processed_block_tree (Config.toSpec E unreadHealConfig unreadHeightConfig)
      st.val s)) = pure _
  rw [hv]
  show successOutcomes (.ok (v.image Block.toProof)) = _
  rw [successOutcomes_ok]
  congr 1
  simp only [Protocol.voter_processed_block_tree] at hv
  have hq := filterM_eq_filter_of_ok _
    (fun B => (∃ τ, (↑st : Store V).timestamp_block B = some τ ∧
        τ < (((Config.toSpec E unreadHealConfig unreadHeightConfig).view_freeze (s - 1) : Time) :
          Stamp)) ∨
      ∃ P ∈ (↑st : Store V).T, P.slot = s ∧ B.ancestorEq P = true)
    (fun B b h => ?_) _ _ hv
  · rw [hq]
    unfold DecoupledConsensusModel.Protocol.voter_processed_block_tree
    rw [image_gs_T, Finset.filter_image]
    congr 1
    apply Finset.filter_congr
    intro B hB
    have hts : (↑st : Store V).toProof.toHealing.toFG.toSG.toGoldfishStore.timestamp_block
        B.toProof = (↑st : Store V).timestamp_block B := by
      rw [image_gs_timestamp_block, Store.blockOfImage_toProof_of_injOn st.val hinj hB]
    unfold DecoupledConsensusModel.stampedBefore
    rw [hts, ← toProof_view_freeze E unreadHealConfig unreadHeightConfig]
    apply or_congr
    · cases (↑st : Store V).timestamp_block B <;> simp
    · constructor
      · rintro ⟨P, hP, hPs, hBP⟩
        refine ⟨P.toProof, Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hP, ?_⟩, ?_⟩
        · rw [toProof_slot]; exact hPs
        · rw [Block.toProof_preceq_of_injOn _ hinj hpar hB hP]; exact hBP
      · rintro ⟨P', hP', hBP⟩
        obtain ⟨hP'T, hP's⟩ := Finset.mem_filter.mp hP'
        obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hP'T
        refine ⟨P, hP, ?_, ?_⟩
        · rw [← toProof_slot]; exact hP's
        · rw [← Block.toProof_preceq_of_injOn _ hinj hpar hB hP]; exact hBP
  · cases ht : (↑st : Store V).timestamp_block B with
    | none =>
      simp only [ht, liftM, monadLift, MonadLift.monadLift, Option.elim] at h
      cases h
    | some τ =>
      simp only [ht, liftM, monadLift, MonadLift.monadLift, Option.elim] at h
      have h' := Except.ok.inj h
      subst h'
      simp [Finset.mem_filter, and_assoc]

omit [DecidableEq V] [Fintype V] [Inhabited V] in
/-- If `p` answers `q`'s value wherever it answers, a filter of the list `l` by `p` that answers
    keeps the members of `l` where `q` is `true`, in order. -/
theorem list_filterM_eq_filter_of_ok {α : Type} (p : α → DC.DRE Bool) (q : α → Bool)
    (hpq : ∀ a b, p a = .ok b → b = q a) (l v : List α) (h : l.filterM p = .ok v) :
    v = l.filter q := by
  have aux : ∀ (l acc v : List α), (List.filterAuxM p l acc : DC.DRE (List α)) = .ok v →
      v = (l.filter q).reverse ++ acc := by
    intro l
    induction l with
    | nil =>
      intro acc v h
      simp only [List.filterAuxM] at h
      cases h
      simp
    | cons a l ih =>
      intro acc v h
      cases hb : p a with
      | error e =>
        simp only [List.filterAuxM, hb] at h
        cases h
      | ok b =>
        simp only [List.filterAuxM, hb, NoRaise.DRE.bind_ok] at h
        rw [ih _ _ h]
        have hq := hpq a b hb
        subst hq
        cases hqa : q a <;> simp [hqa]
  simp only [List.filterM] at h
  cases ha : (List.filterAuxM p l [] : DC.DRE (List α)) with
  | error e => rw [ha] at h; cases h
  | ok w =>
    rw [ha, NoRaise.DRE.bind_ok] at h
    cases h
    rw [aux l [] w ha]
    simp

/-- On a tree with distinct roots, the spec's `Protocol.resolved` of a vote answers
    `DecoupledConsensusModel.Protocol.resolved` of the vote's image in the tree's images. -/
theorem resolved_toProof_of_ok {T : Finset (Block V)} (hT : NoRaise.DistinctRoots T)
    (vote : GoldfishVote V) {b : Bool} (h : Protocol.resolved T vote = .ok b) :
    b = DecoupledConsensusModel.Protocol.resolved (T.image Block.toProof) vote.toProof := by
  unfold Protocol.resolved at h
  rw [NoRaise.blockWithRoot_eq hT, NoRaise.DRE.bind_ok] at h
  unfold DecoupledConsensusModel.Protocol.resolved
  rw [show vote.toProof.head = vote.head.toProof from rfl,
    Block.toProof_find?_of_injOn T hT.injOn_toProof]
  cases hf : Block.find? T vote.head with
  | none =>
    rw [hf] at h
    exact (Except.ok.inj (h : (Except.ok false : DC.DRE Bool) = .ok b)).symm
  | some H =>
    rw [hf] at h
    have h' : (Except.ok (decide (H.slot ≤ vote.slot)) : DC.DRE Bool) = .ok b := h
    rw [← Except.ok.inj h']
    simp [GoldfishVote.toProof]

/-- The member `proposer_support_view` of `Model.spec` at a store `st` of the instance is the
    same member of `Model.vocabulary` at the store's image. -/
theorem spec_proposer_support_view_eq (st : OkStore V) (s : Slot) :
    (Model.spec (V := V)).proposer_support_view st s =
      (Model.vocabulary (V := V)).proposer_support_view
        st.val.toProof.toHealing.toFG.toSG.toGoldfishStore s := by
  obtain ⟨-, hT, -, -⟩ := st.property
  obtain ⟨v, hv⟩ := NoRaise.proposer_support_view_ok hT s
  show successOutcomes (Except.map (fun votes => votes.map GoldfishVote.toProof)
    (Protocol.proposer_support_view st.val s)) = pure _
  rw [hv]
  show successOutcomes (.ok (v.map GoldfishVote.toProof)) = _
  rw [successOutcomes_ok]
  congr 1
  unfold Protocol.proposer_support_view at hv
  rw [list_filterM_eq_filter_of_ok _ _ (fun vote b h => resolved_toProof_of_ok hT vote h) _ _ hv]
  unfold DecoupledConsensusModel.Protocol.proposer_support_view
  rw [image_gs_gf_votes, image_gs_T, List.filter_map]
  simp only [Function.comp_def, Bool.decide_eq_true]
  rfl

/-- Where the spec's resolution time `st.tau` of a vote answers at a store of the instance, it
    answers `DecoupledConsensusModel.Protocol.GoldfishStore.tau` of the vote's image at the store's
    image. -/
theorem tau_toProof_of_ok (st : OkStore V) (vote : GoldfishVote V) {o : Occurrence}
    (h : st.val.tau vote = .ok o) :
    o = DecoupledConsensusModel.Protocol.GoldfishStore.tau
      st.val.toProof.toHealing.toFG.toSG.toGoldfishStore vote.toProof := by
  obtain ⟨hst, hT, -, -⟩ := st.property
  have hinj := hT.injOn_toProof
  unfold Store.tau Protocol.resolution_time at h
  rw [NoRaise.blockWithRoot_eq hT, NoRaise.DRE.bind_ok] at h
  unfold DecoupledConsensusModel.Protocol.GoldfishStore.tau
    DecoupledConsensusModel.Protocol.resolution_time
  rw [image_gs_T, show vote.toProof.head = vote.head.toProof from rfl,
    Block.toProof_find?_of_injOn _ hinj]
  cases hf : Block.find? st.val.T vote.head with
  | none =>
    rw [hf] at h
    exact (Except.ok.inj h).symm
  | some H =>
    rw [hf] at h
    obtain ⟨hHT, -⟩ := NoRaise.find?_mem hf
    have hts : st.val.toProof.toHealing.toFG.toSG.toGoldfishStore.timestamp_block H.toProof =
        st.val.timestamp_block H := by
      rw [image_gs_timestamp_block, Store.blockOfImage_toProof_of_injOn st.val hinj hHT]
    simp only [Option.map_some]
    simp only [Option.value, Option.get_some] at h
    have htv : st.val.toProof.toHealing.toFG.toSG.toGoldfishStore.timestamp_vote vote.toProof =
        st.val.timestamp_vote vote := by
      rw [image_gs_timestamp_vote, GoldfishVote.toSpec_toProof]
    rw [toProof_slot, show vote.toProof.slot = vote.slot from rfl, hts, htv]
    by_cases hs : H.slot ≤ vote.slot
    · rw [if_pos hs]
      cases htv' : st.val.timestamp_vote vote <;> cases htb : st.val.timestamp_block H <;>
        simp [htv', htb, hs, liftM, monadLift, MonadLift.monadLift, Option.elim,
          NoRaise.DRE.bind_ok] at h ⊢
      all_goals first
        | (subst h; unfold DecoupledConsensusModel.occurrenceMax; rfl)
        | cases h
    · rw [if_neg hs]
      simp [hs] at h
      exact (Except.ok.inj h).symm

omit [DecidableEq V] [Fintype V] [Inhabited V] in
/-- If `x >>= f` answers `v`, then `x` answers some `a` and `f a` answers `v`. -/
theorem bind_eq_ok {α β : Type} {x : DC.DRE α} {f : α → DC.DRE β} {v : β}
    (h : x >>= f = .ok v) : ∃ a, x = .ok a ∧ f a = .ok v := by
  cases hx : x with
  | error e => rw [hx] at h; cases h
  | ok a => rw [hx] at h; exact ⟨a, rfl, h⟩

/-- The member `voter_support_view` of `Model.spec` at a store `st` of the instance is the same
    member of `Model.vocabulary` at the store's image. -/
theorem spec_voter_support_view_eq (E : DecoupledConsensusModel.Env V) (st : OkStore V)
    (s : Slot) :
    (Model.spec (V := V)).voter_support_view E st s =
      (Model.vocabulary (V := V)).voter_support_view E
        st.val.toProof.toHealing.toFG.toSG.toGoldfishStore s := by
  obtain ⟨hst, hT, hpar, -⟩ := st.property
  have hinj := hT.injOn_toProof
  obtain ⟨v, hv⟩ := NoRaise.voter_support_view_ok
    (Config.toSpec E unreadHealConfig unreadHeightConfig) hT hst s
  show successOutcomes (Except.map (fun votes => votes.map GoldfishVote.toProofEmb)
    (Protocol.voter_support_view (Config.toSpec E unreadHealConfig unreadHeightConfig)
      st.val s)) = pure _
  rw [hv]
  show successOutcomes (.ok (v.map GoldfishVote.toProofEmb)) = _
  rw [successOutcomes_ok]
  congr 1
  simp only [Protocol.voter_support_view] at hv
  obtain ⟨A, hA, hv⟩ := bind_eq_ok hv
  obtain ⟨B, hB, hv⟩ := bind_eq_ok hv
  have hvAB : v = A ∪ B := (Except.ok.inj hv).symm
  have hAq := filterM_eq_filter_of_ok _
    (fun vote => DecoupledConsensusModel.stampedBefore
      (DecoupledConsensusModel.Protocol.GoldfishStore.tau
        st.val.toProof.toHealing.toFG.toSG.toGoldfishStore)
      (DecoupledConsensusModel.Protocol.view_freeze E (s - 1)) vote.toProof = true)
    (fun vote b h => ?_) _ _ hA
  have hBq := filterM_eq_filter_of_ok _
    (fun vote => DecoupledConsensusModel.Protocol.resolved (st.val.T.image Block.toProof)
      vote.toProof = true)
    (fun vote b h => by rw [resolved_toProof_of_ok hT vote h]) _ _ hB
  · rw [hvAB, hAq, hBq, Finset.map_union]
    unfold DecoupledConsensusModel.Protocol.voter_support_view
    rw [image_gs_pool, image_gs_T]
    congr 1
    · unfold DecoupledConsensusModel.beforeCutoff
      rw [Finset.filter_map]
      rfl
    · ext u
      simp only [Store.included_support_votes, Finset.mem_map, Finset.mem_biUnion,
        Finset.mem_filter, Finset.mem_image, List.mem_toFinset, GoldfishVote.coe_toProofEmb]
      constructor
      · rintro ⟨w, ⟨⟨X, ⟨hX, hXs⟩, hw, hws⟩, hres⟩, rfl⟩
        refine ⟨X.toProof, ⟨⟨X, hX, rfl⟩, by rw [toProof_slot]; exact hXs⟩, ?_, hres, hws⟩
        rw [toProof_gf_support_votes]; exact List.mem_map_of_mem hw
      · rintro ⟨_, ⟨⟨X, hX, rfl⟩, hXs⟩, hu, hres, hus⟩
        rw [toProof_gf_support_votes, List.mem_map] at hu
        obtain ⟨w, hw, rfl⟩ := hu
        exact ⟨w, ⟨⟨X, ⟨hX, by rw [← toProof_slot]; exact hXs⟩, hw, hus⟩, hres⟩, rfl⟩
  · obtain ⟨o, ho, h⟩ := bind_eq_ok h
    have ho' := tau_toProof_of_ok st vote ho
    unfold DecoupledConsensusModel.stampedBefore
    rw [← ho', ← Except.ok.inj h, toProof_view_freeze E unreadHealConfig unreadHeightConfig]
    cases o with
    | none => simp [occurrenceBefore]
    | some x =>
      simp only [occurrenceBefore]
      simp
      exact Iff.rfl

omit [DecidableEq V] [Fintype V] [Inhabited V] in
/-- If `S.filterM p` answers `v`, every member of `v` is in `S`. -/
theorem filterM_subset_of_ok {α : Type} [DecidableEq α] (p : α → DC.DRE Bool) (S v : Finset α)
    (h : S.filterM p = .ok v) : v ⊆ S := by
  rw [filterM_eq_filter_of_ok p (fun a => p a = .ok true)
    (fun a b hb => by rw [hb]; exact ⟨fun h => by rw [h], fun h => Except.ok.inj h⟩) S v h]
  exact Finset.filter_subset _ _

omit [Fintype V] in
/-- Two stores that agree on `F`, `J`, `h_j` and `h_max` have the same fgroot. -/
theorem get_fg_root_congr {a b : Store V} (hF : a.F = b.F) (hJ : a.J = b.J)
    (hj : a.h_j = b.h_j) (hm : a.h_max = b.h_max) :
    Protocol.get_fg_root a = Protocol.get_fg_root b := by
  unfold Protocol.get_fg_root
  rw [hF, hJ, hj, hm]

omit [Fintype V] in
/-- Two stores that agree on `T`, `σ`, `F`, `J`, `h_j` and `h_max` have the same filtered tree. -/
theorem get_filtered_block_tree_congr {a b : Store V} (hT : a.T = b.T) (hσ : a.σ = b.σ)
    (hF : a.F = b.F) (hJ : a.J = b.J) (hj : a.h_j = b.h_j) (hm : a.h_max = b.h_max) :
    Protocol.get_filtered_block_tree a = Protocol.get_filtered_block_tree b := by
  simp only [Protocol.get_filtered_block_tree, draft_filtered_from_def,
    get_fg_root_congr hF hJ hj hm, hT, hσ, hF, hm]

/-- The spec's processed tree of the store read through its tree is the store's processed tree. -/
theorem voter_processed_block_tree_ofImage (C : Config) (st : Store V) (s : Slot) :
    Protocol.voter_processed_block_tree C (Store.ofImage st) s =
      Protocol.voter_processed_block_tree C st s := rfl

/-- The spec's voter's filtered tree of the store read through its tree is the filtered tree of that
    store within the store's processed tree. -/
theorem voter_filtered_block_tree_ofImage (C : Config) (st : Store V) (s : Slot) :
    Protocol.voter_filtered_block_tree C (Store.ofImage st) s =
      (Protocol.voter_processed_block_tree C st s).map
        (Protocol.get_filtered_block_tree_from (Store.ofImage st)) := by
  unfold Protocol.voter_filtered_block_tree
  rw [voter_processed_block_tree_ofImage]
  cases Protocol.voter_processed_block_tree C st s <;> rfl

/-- The spec's processed tree, where it answers, is a set of blocks of the store's tree. -/
theorem processed_subset_of_ok (C : Config) (st : Store V) (s : Slot) {Q : Finset (Block V)}
    (h : Protocol.voter_processed_block_tree C st s = .ok Q) : Q ⊆ st.T := by
  simp only [Protocol.voter_processed_block_tree] at h
  exact filterM_subset_of_ok _ _ _ h

/-- At a store of the instance, the blocks standing for the images of a set `Q` of tree blocks are
    `Q`. -/
theorem image_map_blockOfImage_of_subset (st : OkStore V) {Q : Finset (Block V)}
    (hQ : Q ⊆ st.val.T) : (Q.image Block.toProof).map st.val.blockOfImageEmb = Q := by
  obtain ⟨-, hT, -, -⟩ := st.property
  have hinj := hT.injOn_toProof
  ext X
  simp only [Finset.mem_map, Finset.mem_image, Store.coe_blockOfImageEmb]
  constructor
  · rintro ⟨_, ⟨Y, hY, rfl⟩, rfl⟩
    rw [Store.blockOfImage_toProof_of_injOn st.val hinj (hQ hY)]; exact hY
  · intro hX
    exact ⟨X.toProof, ⟨X, hX, rfl⟩, Store.blockOfImage_toProof_of_injOn st.val hinj (hQ hX)⟩

/-- If `Q ⊆ Q'`, the spec's filtered tree of `st` within `Q` is a subset of its filtered tree within
    `Q'`. -/
theorem draft_filtered_from_mono (st : Store V) {Q Q' : Finset (Block V)} (hQ : Q ⊆ Q') :
    Protocol.get_filtered_block_tree_from st Q ⊆ Protocol.get_filtered_block_tree_from st Q' := by
  intro B hB
  simp only [draft_filtered_from_def, Protocol.viable_tree, Protocol.finalized_descendants,
    Protocol.viable, Finset.mem_filter, decide_eq_true_eq] at hB ⊢
  obtain ⟨⟨⟨hBQ, hF⟩, W, hW, hBW, hh⟩, hr⟩ := hB
  exact ⟨⟨⟨hQ hBQ, hF⟩, W, hQ hW, hBW, hh⟩, hr⟩

end SpecRecord.ForkChoiceImages
