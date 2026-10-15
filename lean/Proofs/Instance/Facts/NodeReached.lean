import Proofs.Instance.Facts.GradesRun

/-!
# Node facts at reached node states of `Model.specDraft`

Proofs of fields of `NodeFacts` and `NodeRunFacts` at `Model.specDraft` that hold at node states (or
named stores) a run reaches: the cache fields, the stamp fields and the finality of the core call.
-/

set_option autoImplicit false

namespace SpecDraftRecord.NodeReached

open Spec
open scoped DC

variable {V : Type} [DecidableEq V]

/-! ## The image clip on a tree -/

/-- On a tree `T` that holds the parents of its blocks and `F`, and on which `Block.toProof` is
    injective, the loop of `clipBlockImage F.toProof` from a tree block `g`, given at least
    `g.depth + 1` steps, stops at the spec's deepest ancestor of `g` compatible with `F`. -/
theorem clipBlockImage_loop_mem (T : Finset (Block V))
    (hinj : Set.InjOn (Block.toProof (V := V)) (↑T : Set (Block V)))
    (hpar : ∀ B ∈ T, B.parent ∈ T) {F : Block V} (hF : F ∈ T)
    (l : List Nat) (g : Block V) (hg : g ∈ T) (hl : g.depth + 1 ≤ l.length) :
    (forIn (m := Id) l ((none : Option (Block V)), g)
        fun _ (s : Option (Block V) × Block V) =>
        if DecoupledConsensusModel.Block.compatible s.2.toProof F.toProof = true then
          pure (ForInStep.done (some s.2, s.2))
        else pure (ForInStep.yield (none, s.2.parent))) =
      (some (GradesLocal.clipBlock g F), GradesLocal.clipBlock g F) := by
  induction l generalizing g with
  | nil => simp at hl
  | cons x l ih =>
    rw [List.forIn_cons]
    have hc := Block.toProof_compatible_of_injOn T hinj hpar hg hF
    cases g with
    | genesis =>
      have hg' : (Block.genesis : Block V).compatible F = true := by
        simp [Block.compatible, GradesLocal.genesis_ancestorEq]
      simp only [hc, hg', if_true]
      rfl
    | node p s root gv gsv ats v =>
      by_cases h : (Block.node p s root gv gsv ats v).compatible F = true
      · simp only [hc, h, if_true]
        simp only [GradesLocal.clipBlock, h, if_true]
        rfl
      · have hl' : p.depth + 1 ≤ l.length := by
          simp [Block.depth] at hl; omega
        have hp : p ∈ T := hpar _ hg
        have hpar' : (Block.node p s root gv gsv ats v).parent = p := rfl
        simp only [hc, h, Bool.false_eq_true, if_false, hpar']
        show forIn l (none, p) _ = _
        rw [ih p hp hl']
        simp only [GradesLocal.clipBlock, h, Bool.false_eq_true, if_false]

/-- On a tree with the three conditions of `clipBlockImage_loop_mem`, the image clip of a tree block
    `g` at the image of `F` is the spec's deepest ancestor of `g` compatible with `F`. -/
theorem clipBlockImage_eq_dca (T : Finset (Block V))
    (hinj : Set.InjOn (Block.toProof (V := V)) (↑T : Set (Block V)))
    (hpar : ∀ B ∈ T, B.parent ∈ T) {F : Block V} (hF : F ∈ T) (g : Block V) (hg : g ∈ T) :
    clipBlockImage F.toProof g = Protocol.deepest_compatible_ancestor g F := by
  rw [GradesLocal.deepest_compatible_ancestor_eq]
  unfold clipBlockImage
  simp only [Id.run]
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  rw [clipBlockImage_loop_mem T hinj hpar hF _ g hg (by simp [Std.Legacy.Range.size])]
  rfl

/-- On a tree with the three conditions of `clipBlockImage_loop_mem`, the image clip of a grade
    result whose block, if any, is a tree block is the spec's clip. -/
theorem clipResultImage_eq_of_mem (T : Finset (Block V))
    (hinj : Set.InjOn (Block.toProof (V := V)) (↑T : Set (Block V)))
    (hpar : ∀ B ∈ T, B.parent ∈ T) {F : Block V} (hF : F ∈ T) (r : GradeResult V)
    (hr : ∀ G, r = .computed (some G) → G ∈ T) :
    clipResultImage F.toProof r = Protocol.make_result_compatible_with F r := by
  have hp : ∀ x : GradeResult V, (pure x : Id (GradeResult V)) = x := fun _ => rfl
  cases r with
  | pending => simp [Protocol.make_result_compatible_with, clipResultImage, Id.run, hp]
  | computed G =>
    cases G with
    | none => rfl
    | some G =>
      show GradeResult.computed (some (clipBlockImage F.toProof G)) =
        GradeResult.computed (some (Protocol.deepest_compatible_ancestor G F))
      rw [clipBlockImage_eq_dca T hinj hpar hF G (hr G rfl)]

/-- On a tree with distinct images that holds the parents of its blocks and `F`, the member
    `clipCache` at the image of `F` is the spec's clip at `F` on saved grades whose blocks are tree
    blocks. -/
theorem clipCache_eq_of_contractInTree [Fintype V] (T : Finset (Block V))
    (hinj : Set.InjOn (Block.toProof (V := V)) (↑T : Set (Block V)))
    (hpar : ∀ B ∈ T, B.parent ∈ T) {F : Block V} (hF : F ∈ T) (c : SavedGrades V)
    (hc : Store.ContractInTree T c) :
    Member.clipCache F.toProof c = Protocol.make_saved_grades_compatible_with F c := by
  obtain ⟨r, ⟨a0, a1, a2⟩, ⟨b0, b1, b2⟩⟩ := c
  have h := fun (fr : RoundGrades V) (hfr : fr ∈ [(⟨a0, a1, a2⟩ : RoundGrades V), ⟨b0, b1, b2⟩])
    (g : GradeResult V) (hg : g ∈ [fr.g0, fr.g1, fr.g2]) => hc fr hfr g hg
  simp only [Member.clipCache, Member.clipFrame, Protocol.make_saved_grades_compatible_with,
    Protocol.make_round_grades_compatible_with]
  rw [clipResultImage_eq_of_mem T hinj hpar hF a0 (h ⟨a0, a1, a2⟩ (by simp) _ (by simp)),
    clipResultImage_eq_of_mem T hinj hpar hF a1 (h ⟨a0, a1, a2⟩ (by simp) _ (by simp)),
    clipResultImage_eq_of_mem T hinj hpar hF a2 (h ⟨a0, a1, a2⟩ (by simp) _ (by simp)),
    clipResultImage_eq_of_mem T hinj hpar hF b0 (h ⟨b0, b1, b2⟩ (by simp) _ (by simp)),
    clipResultImage_eq_of_mem T hinj hpar hF b1 (h ⟨b0, b1, b2⟩ (by simp) _ (by simp)),
    clipResultImage_eq_of_mem T hinj hpar hF b2 (h ⟨b0, b1, b2⟩ (by simp) _ (by simp))]

omit [DecidableEq V] in
/-- Saved grades whose blocks are blocks of `T` have their blocks in every superset of `T`. -/
theorem contractInTree_mono {T T' : Finset (Block V)} (hT : T ⊆ T') {c : SavedGrades V}
    (hc : Store.ContractInTree T c) : Store.ContractInTree T' c :=
  fun fr hfr g hg G hG => hT (hc fr hfr g hg G hG)

omit [DecidableEq V] in
/-- Saved grades whose blocks are blocks of `T` satisfy the claim that each result's block is in
    `T`. -/
theorem claim_of_contractInTree [Fintype V] {T : Finset (Block V)} {c : SavedGrades V}
    (hc : Store.ContractInTree T c) :
    GradesRunFacts.CacheClaim c (fun _ _ G => ∀ g, G = some g → g ∈ T) := by
  have key : ∀ f ∈ [c.current, c.next], ∀ r,
      GradesRunFacts.FrameClaim r f (fun _ _ G => ∀ g, G = some g → g ∈ T) := by
    intro f hf r p G hG g hg
    subst hg
    cases p
    · simp only [GradesRunFacts.res, Protocol.phaseResult, Protocol.Phase.toSpec] at hG
      exact hc f hf f.g0 (by simp) g hG
    · simp only [GradesRunFacts.res, Protocol.phaseResult, Protocol.Phase.toSpec] at hG
      exact hc f hf f.g1 (by simp) g hG
    · simp only [GradesRunFacts.res, Protocol.phaseResult, Protocol.Phase.toSpec] at hG
      exact hc f hf f.g2 (by simp) g hG
  exact ⟨key _ (by simp) _, key _ (by simp) _⟩

/-! ## The block stamps read through the image -/

/-- `StampStep a b τ`: the store `b` has the tree and the block stamps of `a`, or `a`'s tree with
    one new block `Y` added and `a`'s stamps with `Y` stamped `τ`. -/
def StampStep (a b : Store V) (τ : Stamp) : Prop :=
  (b.T = a.T ∧ b.timestamp_block = a.timestamp_block) ∨
    ∃ Y, Y ∉ a.T ∧ b.T = a.T ∪ {Y} ∧
      b.timestamp_block = Function.update a.timestamp_block Y (some τ)

/-- A `StampStep` with a stamp `τ` at most `b`'s clock, from a store `a` that stamps no block
    outside its tree and whose image stamps are at most its clock, to a store `b` whose clock is at
    least `a`'s, keeps `a`'s tree images and image stamps; in `b` the images of tree blocks are
    exactly the stamped images, and every image stamp is at most the clock. -/
theorem stamp_step {a b : Store V} (ha : NoRaise.StoreOk a) (hb : NoRaise.StoreOk b)
    (hoff : ∀ X, X ∉ a.T → a.timestamp_block X = none)
    (hclock : ∀ (B : DecoupledConsensusModel.Block V) (c : Stamp),
      a.timestamp_block (a.blockOfImage B) = some c → c ≤ (a.t : Stamp))
    (hab : (a.t : Stamp) ≤ (b.t : Stamp)) {τ : Stamp} (hτ : τ ≤ (b.t : Stamp))
    (hstep : StampStep a b τ) :
    ((∀ B : DecoupledConsensusModel.Block V, B ∈ a.T.image Block.toProof →
        B ∈ b.T.image Block.toProof) ∧
      (∀ (B : DecoupledConsensusModel.Block V) (c : Stamp),
        a.timestamp_block (a.blockOfImage B) = some c →
        b.timestamp_block (b.blockOfImage B) = some c)) ∧
    ((∀ B : DecoupledConsensusModel.Block V, B ∈ b.T.image Block.toProof →
        (b.timestamp_block (b.blockOfImage B)).isSome = true) ∧
      (∀ B : DecoupledConsensusModel.Block V,
        (b.timestamp_block (b.blockOfImage B)).isSome = true → B ∈ b.T.image Block.toProof) ∧
      (∀ (B : DecoupledConsensusModel.Block V) (c : Stamp),
        b.timestamp_block (b.blockOfImage B) = some c → c ≤ (b.t : Stamp))) := by
  have hinja := SubtypeEqualities.injOn_of_distinctRoots ha.2.1
  have hinjb := SubtypeEqualities.injOn_of_distinctRoots hb.2.1
  have hsub : a.T ⊆ b.T := by
    rcases hstep with ⟨hT, -⟩ | ⟨Y, -, hT, -⟩
    · rw [hT]
    · rw [hT]; exact Finset.subset_union_left
  have hkeep : ∀ X ∈ a.T, b.timestamp_block X = a.timestamp_block X := by
    intro X hX
    rcases hstep with ⟨-, hts⟩ | ⟨Y, hY, -, hts⟩
    · rw [hts]
    · have hXY : X ≠ Y := fun h => hY (by rw [← h]; exact hX)
      rw [hts, Function.update_of_ne hXY]
  have hoffb : ∀ X, X ∉ b.T → b.timestamp_block X = none := by
    intro X hX
    rcases hstep with ⟨hT, hts⟩ | ⟨Y, hY, hT, hts⟩
    · rw [hts]; exact hoff X (by rw [← hT]; exact hX)
    · have hXY : X ≠ Y := fun h => hX (by rw [hT, h]; simp)
      rw [hts, Function.update_of_ne hXY]
      exact hoff X (fun h => hX (hsub h))
  have hstampa : ∀ X c, a.timestamp_block X = some c → X ∈ a.T := by
    intro X c h
    by_contra hX
    rw [hoff X hX] at h
    cases h
  refine ⟨⟨fun B hB => Finset.image_subset_image hsub hB, ?_⟩, ?_, ?_, ?_⟩
  · intro B c h
    have hX := hstampa _ _ h
    have e : (a.blockOfImage B).toProof = B := Store.toProof_blockOfImage a B
    rw [← e, Store.blockOfImage_toProof_of_injOn b hinjb (hsub hX), hkeep _ hX]
    rw [← e, Store.blockOfImage_toProof_of_injOn a hinja hX] at h
    exact h
  · intro B hB
    obtain ⟨X, hX, rfl⟩ := Finset.mem_image.mp hB
    rw [Store.blockOfImage_toProof_of_injOn b hinjb hX]
    exact Option.isSome_iff_ne_none.mpr (hb.1.1 X hX)
  · intro B hB
    have hmem : b.blockOfImage B ∈ b.T := by
      by_contra hX
      rw [hoffb _ hX] at hB
      cases hB
    rw [← Store.toProof_blockOfImage b B]
    exact Finset.mem_image_of_mem _ hmem
  · intro B c h
    rcases hstep with ⟨-, hts⟩ | ⟨Y, hY, -, hts⟩
    · rw [hts] at h
      have hX := hstampa _ _ h
      have e : (b.blockOfImage B).toProof = B := Store.toProof_blockOfImage b B
      have h' : a.timestamp_block (a.blockOfImage B) = some c := by
        rw [← e, Store.blockOfImage_toProof_of_injOn a hinja hX]; exact h
      exact (hclock B c h').trans hab
    · by_cases hXY : b.blockOfImage B = Y
      · rw [hXY, hts, Function.update_self] at h
        cases h
        exact hτ
      · rw [hts, Function.update_of_ne hXY] at h
        have hX := hstampa _ _ h
        have e : (b.blockOfImage B).toProof = B := Store.toProof_blockOfImage b B
        have h' : a.timestamp_block (a.blockOfImage B) = some c := by
          rw [← e, Store.blockOfImage_toProof_of_injOn a hinja hX]; exact h
        exact (hclock B c h').trans hab

end SpecDraftRecord.NodeReached

/-! ## The receipt and the tick at the instance: the tree grows -/

namespace SpecDraftRecord.NodeReached

open DecoupledConsensusModel DecoupledConsensusModel.Execution DecoupledConsensusModel.Sts
open DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-- The tick of `Model.specDraft` keeps every block of the node's tree. -/
theorem tick_T_subset (S : Setup V) (v : V) (n : (Model.specDraft (V := V)).N) (t : Time)
    (out : (Model.specDraft (V := V)).N × List (NamedObject V))
    (hout : (Model.specDraft (V := V)).tick S v n t ⇢ out) :
    n.val.st.T ⊆ out.1.val.st.T := by
  obtain ⟨sg, ⟨h, -⟩ | ⟨B, -, h⟩⟩ := NodeFacts.tick_shape S v n t out hout
  · rw [h.1]
  · rw [h.1]
    exact (NodeFacts.keeps_receipt_process S
      { n.val.st with saved_grades := sg, t := t, s := (Setup.toSpec S).C.slotOf t } (.block B)).2.2.1

/-- The node state the receipt of `o` returns at `Model.specDraft` has the store
    `make_grades_compatible_with_finalized` of the member `receipt_process` on `n`'s store. -/
theorem process_st (S : Setup V) (n : (Model.specDraft (V := V)).N) (o : NamedObject V)
    (n' : (Model.specDraft (V := V)).N) (hn' : (Model.specDraft (V := V)).process S n o ⇢ n') :
    n'.val.st = Spec.make_grades_compatible_with_finalized
      (Member.receipt_process S n.val.st o) := by
  rw [(NodeFacts.process_returns_iff S n.val n'.val o).mp hn', NodeFacts.receiveNamedObject_eq]

end SpecDraftRecord.NodeReached

/-! ## The cache fields -/

namespace DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

open DecoupledConsensusModel.Execution
open scoped DC
open SpecDraftRecord

/-- The field `process_cache_eq` of `NodeFacts` at `Model.specDraft`: at a reached node state, the
    cache after a receipt is the record's clip of the cache before at the new finalized block. -/
theorem _root_.SpecDraftRecord.NodeFacts.specDraft_process_cache_eq :
    ∀ (S : Setup V) (n : (Model.specDraft (V := V)).N) (o : NamedObject V) (n' : (Model.specDraft (V := V)).N)
      (hn' : (Model.specDraft (V := V)).process S n o ⇢ n') (hn : (Model.specDraft (V := V)).reachedNode n), n'.cache = (Model.specDraft (V := V)).clipCache n'.st.core.F n.cache := by
  intro S n o n' hn' hn
  obtain ⟨hinv, hconf, hcontract⟩ := reached_elim hn
  obtain ⟨-, hd, hpc, hF⟩ := n'.property
  have hst := NodeReached.process_st S n o n' hn'
  have hT : n.val.st.T ⊆ n'.val.st.T := by
    rw [hst]
    exact (NodeFacts.keeps_receipt_process S n.val.st o).2.2.1
  show n'.val.st.saved_grades = Member.clipCache n'.val.st.F.toProof n.val.st.saved_grades
  rw [NodeReached.clipCache_eq_of_contractInTree n'.val.st.T
    (SubtypeEqualities.injOn_of_distinctRoots hd) hpc hF _
    (NodeReached.contractInTree_mono hT hcontract), hst]
  show Spec.Protocol.make_saved_grades_compatible_with _
      (Member.receipt_process S n.val.st o).saved_grades = _
  rw [NodeFacts.receipt_process_saved_grades]
  rfl

/-- The field `namedNode_process_cache` of `NodeFacts` at `Model.specDraft`: at a reached node
    state, the cache after a receipt is the record's clip of the cache before at the new finalized
    block. -/
theorem _root_.SpecDraftRecord.NodeFacts.specDraft_namedNode_process_cache :
    ∀ (S : Setup V) (n : (Model.specDraft (V := V)).N) (o : NamedObject V) (n' : (Model.specDraft (V := V)).N)
      (hn' : (Model.specDraft (V := V)).process S n o ⇢ n') (hn : (Model.specDraft (V := V)).reachedNode n), n'.cache = (Model.specDraft (V := V)).clipCache n'.st.core.F n.cache := by
  intro S n o n' hn' hn
  exact SpecDraftRecord.NodeFacts.specDraft_process_cache_eq S n o n' hn' hn

/-- The field `tick_cache_eq` of `NodeFacts` at `Model.specDraft`: at a reached node state, the
    cache after a tick is the record's clip, at the tick's final finalized block, of the outcome `c`
    of the phase tick on the node's store and cache. -/
theorem _root_.SpecDraftRecord.NodeFacts.specDraft_tick_cache_eq :
    ∀ (S : Setup V) (v : V) (n : (Model.specDraft (V := V)).N) (t : Time)
      (out : (Model.specDraft (V := V)).N × List (NamedObject V)) (hout : (Model.specDraft (V := V)).tick S v n t ⇢ out)
      (c : (Model.specDraft (V := V)).Cache) (hcache : (Model.specDraft (V := V)).onPhaseTick S.E S.hc n.st.core.toHealing t n.cache ⇢ c)
      (hn : (Model.specDraft (V := V)).reachedNode n),
      out.1.cache = (Model.specDraft (V := V)).clipCache out.1.st.core.F c := by
  intro S v n t out hout c hcache hn
  obtain ⟨hinv, hconf, hcontract⟩ := reached_elim hn
  obtain ⟨S', hS', rfl, -⟩ := GradesFacts.sd_onPhaseTick_ok hcache
  have hout' : (Model.specDraftBase (V := V)).tick S v n.val t ⇢ (out.1.val, out.2) := hout
  obtain ⟨st0, h0, hsaved⟩ := GradesRunFacts.tick_saved hout'
  have e : Spec.Protocol.update_grades (Setup.toSpec S).C (Setup.toSpec S).P n.val.st t =
      .ok S' := hS'
  rw [h0] at e
  obtain ⟨⟩ := e
  obtain ⟨-, hd, hpc, hF⟩ := out.1.property
  have hmem := GradesRunFacts.contractInTree_of_claim
    (GradesRunFacts.memClaim_update_grades n.property h0
      (NodeReached.claim_of_contractInTree hcontract))
  show out.1.val.st.saved_grades = Member.clipCache out.1.val.st.F.toProof S'.saved_grades
  rw [NodeReached.clipCache_eq_of_contractInTree out.1.val.st.T
    (SubtypeEqualities.injOn_of_distinctRoots hd) hpc hF _
    (NodeReached.contractInTree_mono (NodeReached.tick_T_subset S v n t out hout) hmem)]
  exact hsaved

/-- The field `namedNode_tick_cache` of `NodeFacts` at `Model.specDraft`: at a reached node state,
    the cache after a tick is the record's clip, at the tick's final finalized block, of the outcome
    of the phase tick on the node's store and cache. -/
theorem _root_.SpecDraftRecord.NodeFacts.specDraft_namedNode_tick_cache :
    ∀ (S : Setup V) (v : V) (n : (Model.specDraft (V := V)).N) (t : Int)
      (out : (Model.specDraft (V := V)).N × List (NamedObject V)) (hout : (Model.specDraft (V := V)).tick S v n t ⇢ out)
      (c : (Model.specDraft (V := V)).Cache) (hcache : (Model.specDraft (V := V)).onPhaseTick S.E S.hc n.st.core.toHealing t n.cache ⇢ c)
      (hn : (Model.specDraft (V := V)).reachedNode n),
      out.1.cache
        = (Model.specDraft (V := V)).clipCache out.1.st.core.F c := by
  intro S v n t out hout c hcache hn
  exact SpecDraftRecord.NodeFacts.specDraft_tick_cache_eq S v n t out hout c hcache hn

/-- The field `process_node_of_store_id` of `NodeFacts` at `Model.specDraft`: at a reached node
    state, a receipt that keeps the store, at a node whose cache the record's clip keeps, returns
    the node state unchanged. -/
theorem _root_.SpecDraftRecord.NodeFacts.specDraft_process_node_of_store_id :
    ∀ (S : DecoupledConsensusModel.Execution.Setup V) (n : (Model.specDraft (V := V)).N) (o : DecoupledConsensusModel.Execution.NamedObject V), (Model.specDraft (V := V)).receipt_process S n.st o = n.st → (Model.specDraft (V := V)).clipCache n.st.core.F n.cache = n.cache → ∀ (n' : (Model.specDraft (V := V)).N), (Model.specDraft (V := V)).process S n o ⇢ n' → ∀ (hn : (Model.specDraft (V := V)).reachedNode n), n' = n := by
  intro S n o h₁ h₂ n' h₃ hn
  obtain ⟨hinv, hconf, hcontract⟩ := reached_elim hn
  obtain ⟨-, hd, hpc, hF⟩ := n.property
  obtain ⟨-, hd', -, -⟩ := n'.property
  have hst := NodeReached.process_st S n o n' h₃
  have hclip : Spec.Protocol.make_saved_grades_compatible_with n.val.st.F
      n.val.st.saved_grades = n.val.st.saved_grades := by
    rw [← NodeReached.clipCache_eq_of_contractInTree n.val.st.T
      (SubtypeEqualities.injOn_of_distinctRoots hd) hpc hF _ hcontract]
    exact h₂
  have hrec : Member.receipt_process S n.val.st o = n.val.st := by
    by_cases hr : objectRootHeldByOther n.val.st.T o
    · cases o with
      | gfVote _ => exact hr.elim
      | attest _ => exact hr.elim
      | block B =>
        obtain ⟨Y, hY, hne, hroot⟩ := hr
        have hrp : Member.receipt_process S n.val.st (.block B) =
            Spec.Protocol.on_block (Spec.Config.toSpec S.E S.hc S.cfg)
              (Spec.Provisional.toSpec S.E) n.val.st
              (Spec.Block.toSpecNamed B) := rfl
        by_cases hadm : Spec.Protocol.block_admissible
            (Spec.Config.toSpec S.E S.hc S.cfg) (Spec.Provisional.toSpec S.E)
            n.val.st (Spec.Block.toSpecNamed B) = true
        · exfalso
          have hX : Spec.Block.toSpecNamed B ∈
              (Member.receipt_process S n.val.st (.block B)).T := by
            rw [hrp, Handlers.on_block_eq, if_pos hadm]
            apply (NodeFacts.keeps_admit_attestations _ _ _).2.2.1
            have hcore : Handlers.admitBlockCore (Spec.Config.toSpec S.E S.hc S.cfg)
                (Spec.Provisional.toSpec S.E) n.val.st
                (Spec.Block.toSpecNamed B) =
                Handlers.blockCore (Spec.Config.toSpec S.E S.hc S.cfg)
                  (Spec.Provisional.toSpec S.E) n.val.st
                  (Spec.Block.toSpecNamed B) := if_pos hadm
            rw [hcore]
            exact (NodeFacts.blockCore_keeps _ _ _ _).2.2
          have hX' : Spec.Block.toSpecNamed B ∈ n'.val.st.T := by rw [hst]; exact hX
          have hY' : Y ∈ n'.val.st.T := by
            rw [hst]
            exact (NodeFacts.keeps_receipt_process S n.val.st (.block B)).2.2.1 hY
          exact hne (hd' Y hY' _ hX' hroot)
        · rw [hrp, Handlers.on_block_eq, if_neg hadm]
    · have hv := congrArg Subtype.val h₁
      have e : ((Model.specDraft (V := V)).receipt_process S n.st o).val =
          Member.receipt_process S n.val.st o := by
        show (OkMember.receipt_process S n.st o).val = _
        unfold OkMember.receipt_process
        rw [dif_neg (show ¬ objectRootHeldByOther n.st.val.T o from hr)]
        rfl
      rw [e] at hv
      exact hv
  apply Subtype.ext
  rw [(NodeFacts.process_returns_iff S n.val n'.val o).mp h₃]
  exact NodeFacts.process_node_of_store_id_aux S n.val o hrec hclip

/-! ## The stamp fields -/

/-- The field `blockStep_process` of `NodeRunFacts` at `Model.specDraft`: at a reached node state
    whose block stamps meet the three clauses (tree blocks stamped, stamped blocks in the tree,
    stamps at most the clock), a receipt keeps the tree and the old stamps, and its outcome meets
    the three clauses. -/
theorem _root_.SpecDraftRecord.NodeRunFacts.specDraft_blockStep_process :
    ∀ (S : Setup V) (n : (Model.specDraft (V := V)).N) (o : NamedObject V) (n' : (Model.specDraft (V := V)).N), (Model.specDraft (V := V)).process S n o ⇢ n' →
      ((∀ B : Block V, B ∈ n.st.core.T → (n.st.core.timestamp_block B).isSome = true) ∧
        (∀ B : Block V, (n.st.core.timestamp_block B).isSome = true → B ∈ n.st.core.T) ∧
        (∀ (B : Block V) (c : Stamp), n.st.core.timestamp_block B = some c →
          c ≤ (n.st.core.t : Stamp))) →
      ∀ (hn : (Model.specDraft (V := V)).reachedNode n),
      ((∀ B : Block V, B ∈ n.st.core.T → B ∈ n'.st.core.T) ∧
        (∀ (B : Block V) (c : Stamp), n.st.core.timestamp_block B = some c →
          n'.st.core.timestamp_block B = some c)) ∧
      ((∀ B : Block V, B ∈ n'.st.core.T → (n'.st.core.timestamp_block B).isSome = true) ∧
        (∀ B : Block V, (n'.st.core.timestamp_block B).isSome = true → B ∈ n'.st.core.T) ∧
        (∀ (B : Block V) (c : Stamp), n'.st.core.timestamp_block B = some c →
          c ≤ (n'.st.core.t : Stamp))) := by
  intro S n o n' h₁ h₂ hn
  obtain ⟨hinv, hconf, hcontract⟩ := reached_elim hn
  have hst := NodeReached.process_st S n o n' h₁
  have ht : n'.val.st.t = n.val.st.t := by
    rw [hst]
    exact (NodeFacts.keeps_receipt_process S n.val.st o).1
  have hstep : NodeReached.StampStep n.val.st n'.val.st (n.val.st.t : Spec.Stamp) := by
    rcases SubtypeEqualities.receipt_cases S n.val.st o with
      ⟨hT, -, hts, -⟩ | ⟨B, rfl, hadm, hT, -, hts, -⟩
    · left
      rw [hst]
      exact ⟨hT, hts⟩
    · right
      refine ⟨_, ((SubtypeEqualities.block_admissible_iff _ _ _ _).mp hadm).1.1, ?_, ?_⟩
      · rw [hst]; exact hT
      · rw [hst]; exact hts
  exact NodeReached.stamp_step (a := n.val.st) (b := n'.val.st) n.property n'.property (fun X hX => (hinv.2.2 X hX).2) h₂.2.2
    (le_of_eq (by rw [ht])) (le_of_eq (by rw [ht])) hstep

/-- The field `blockStep_tick` of `NodeRunFacts` at `Model.specDraft`: at a reached node state whose
    block stamps meet the three clauses (tree blocks stamped, stamped blocks in the tree, stamps at
    most the clock), a tick at a time `t` not before the node's clock keeps the tree and the old
    stamps, and its outcome meets the three clauses. -/
theorem _root_.SpecDraftRecord.NodeRunFacts.specDraft_blockStep_tick :
    ∀ (S : Setup V) (v : V) (n : (Model.specDraft (V := V)).N) (t : DecoupledConsensusModel.Time)
      (out : (Model.specDraft (V := V)).N × List (NamedObject V)), (Model.specDraft (V := V)).tick S v n t ⇢ out → n.st.core.t ≤ t →
      ((∀ B : Block V, B ∈ n.st.core.T → (n.st.core.timestamp_block B).isSome = true) ∧
        (∀ B : Block V, (n.st.core.timestamp_block B).isSome = true → B ∈ n.st.core.T) ∧
        (∀ (B : Block V) (c : Stamp), n.st.core.timestamp_block B = some c →
          c ≤ (n.st.core.t : Stamp))) →
      ∀ (hn : (Model.specDraft (V := V)).reachedNode n),
      ((∀ B : Block V, B ∈ n.st.core.T → B ∈ out.1.st.core.T) ∧
        (∀ (B : Block V) (c : Stamp), n.st.core.timestamp_block B = some c →
          out.1.st.core.timestamp_block B = some c)) ∧
      ((∀ B : Block V, B ∈ out.1.st.core.T → (out.1.st.core.timestamp_block B).isSome = true) ∧
        (∀ B : Block V, (out.1.st.core.timestamp_block B).isSome = true → B ∈ out.1.st.core.T) ∧
        (∀ (B : Block V) (c : Stamp), out.1.st.core.timestamp_block B = some c →
          c ≤ (out.1.st.core.t : Stamp))) := by
  intro S v n t out h₁ h₂ h₃ hn
  obtain ⟨hinv, hconf, hcontract⟩ := reached_elim hn
  have hoff : ∀ X, X ∉ n.val.st.T → n.val.st.timestamp_block X = none :=
    fun X hX => (hinv.2.2 X hX).2
  have hle : ((n.val.st.t : Time) : Spec.Stamp) ≤ ((t : Time) : Spec.Stamp) :=
    WithBot.coe_le_coe.mpr h₂
  obtain ⟨sg, ⟨h, -⟩ | ⟨B, -, h⟩⟩ := NodeFacts.tick_shape S v n t out h₁
  · obtain ⟨hT, hts, -, -, -, -, -, ht, -⟩ := h
    refine NodeReached.stamp_step (τ := ((t : Time) : Spec.Stamp))
      (a := n.val.st) (b := out.1.val.st) n.property
      out.1.property hoff h₃.2.2 ?_ ?_ (Or.inl ⟨hT, hts⟩)
    · rw [ht]; exact hle
    · rw [ht]
  · obtain ⟨hT, hts, -, -, -, -, -, ht, -⟩ := h
    have hk := NodeFacts.keeps_receipt_process S
      { n.val.st with saved_grades := sg, t := t, s := (Setup.toSpec S).C.slotOf t } (.block B)
    refine NodeReached.stamp_step (τ := ((t : Time) : Spec.Stamp))
      (a := n.val.st) (b := out.1.val.st) n.property
      out.1.property hoff h₃.2.2 ?_ ?_ ?_
    · rw [ht, hk.1]; exact hle
    · rw [ht, hk.1]
    · rcases SubtypeEqualities.receipt_cases S
        { n.val.st with saved_grades := sg, t := t, s := (Setup.toSpec S).C.slotOf t } (.block B)
        with ⟨hT', -, hts', -⟩ | ⟨B', -, hadm, hT', -, hts', -⟩
      · exact Or.inl ⟨hT.trans hT', hts.trans hts'⟩
      · exact Or.inr ⟨_, ((SubtypeEqualities.block_admissible_iff _ _ _ _).mp hadm).1.1,
          hT.trans hT', hts.trans hts'⟩

/-! ## The core call's finality -/

/-- The field `postCore_absorbs_finality` of `NodeFacts` at `Model.specDraft`: at a reached coherent
    named store `before`, under the field's conditions on the new block `B`, `B`'s derived finalized
    block is an ancestor of the finalized block of the store the core call leaves. -/
theorem _root_.SpecDraftRecord.NodeFacts.specDraft_postCore_absorbs_finality :
    ∀ (S : Setup V) (before : (Model.specDraft (V := V)).NS) (B : NamedBlock V),
      DecoupledConsensusModel.Sts.Restated.Vocabulary.Proofs.NamedStore.Coherent (Model.specDraft (V := V)) S.E S.cfg before →
      B.erase ∉ before.core.T →
      B.erase ∈ ((Model.specDraft (V := V)).postCore S before B).core.T →
      Block.Preceq before.core.F ((Model.specDraft (V := V)).derive_named S.E S.cfg B).F →
      (∀ A ∈ before.bodies,
        ((Model.specDraft (V := V)).derive_named S.E S.cfg A).J = ((Model.specDraft (V := V)).derive_named S.E S.cfg B).F →
        ((Model.specDraft (V := V)).derive_named S.E S.cfg A).h_j = ((Model.specDraft (V := V)).derive_named S.E S.cfg B).h_F →
        Block.Preceq ((Model.specDraft (V := V)).derive_named S.E S.cfg B).F before.core.J) →
      (∃ D ∈ before.bodies, ((Model.specDraft (V := V)).derive_named S.E S.cfg D).h = before.core.h_max) →
      (∀ D ∈ before.bodies,
        ((Model.specDraft (V := V)).derive_named S.E S.cfg B).h_F < ((Model.specDraft (V := V)).derive_named S.E S.cfg D).h →
        Block.Preceq ((Model.specDraft (V := V)).derive_named S.E S.cfg B).F D.erase) →
      ∀ (hn : (Model.specDraft (V := V)).reachedStore before),
      Block.Preceq ((Model.specDraft (V := V)).derive_named S.E S.cfg B).F ((Model.specDraft (V := V)).postCore S before B).core.F := by
  intro S before B h₁ h₂ h₃ h₄ h₅ h₆ h₇ hn
  obtain ⟨hinv, hconf, hcontract⟩ := reachedStore_elim hn
  by_cases hroot : RootHeldByOther before.val.T (Spec.Block.toSpecNamed B)
  · exfalso
    have e : (Model.specDraft (V := V)).postCore S before B = before := by
      show OkMember.postCore S before B = before
      unfold OkMember.postCore
      rw [dif_pos hroot]
    rw [e] at h₃
    exact h₂ h₃
  · have hval : ((Model.specDraft (V := V)).postCore S before B).val =
        Handlers.admitBlockCore (Spec.Config.toSpec S.E S.hc S.cfg)
          (Spec.Provisional.toSpec S.E) before.val
          (Spec.Block.toSpecNamed B) := by
      show (OkMember.postCore S before B).val = _
      unfold OkMember.postCore
      rw [dif_neg hroot]
      rfl
    have hpost : ((Model.specDraft (V := V)).postCore S before B).val.toProofNamed =
        DecoupledConsensusModel.Execution.NamedReceiptCalls.postCore S before.val.toProofNamed B := by
      rw [hval, SubtypeEqualities.toProofNamed_admitBlockCore S.E S.hc S.cfg before.property hinv
        _ hroot, Spec.Block.toProofNamed_toSpecNamed]
      unfold DecoupledConsensusModel.Execution.NamedReceiptCalls.postCore
      rfl
    have hD : ∀ A : NamedBlock V, Protocol.derive_named S.E S.cfg A =
        (Member.derive_named S.E S.cfg A).toProof := fun A =>
      (NodeFacts.toProof_derive_named S.E S.cfg A).symm
    have hco : DecoupledConsensusModel.Proofs.NamedStore.Coherent S.E S.cfg
        before.val.toProofNamed := by
      refine ⟨h₁.1, h₁.2.1, h₁.2.2.1, h₁.2.2.2.1, ?_⟩
      intro A hA
      have h := h₁.2.2.2.2 A hA
      change before.val.σ (before.val.blockOfImage A.erase) = Member.derive_named S.E S.cfg A at h
      rw [hD]
      show (before.val.σ (before.val.blockOfImage A.erase)).toProof = _
      rw [h]
    have key := DecoupledConsensusModel.Sts.postCore_absorbs_finality_r58a S
      before.val.toProofNamed B hco
    rw [← hpost] at key
    simp only [hD] at key
    exact key h₂ h₃ h₄ h₅ h₆ h₇

end DecoupledConsensusModel.Sts.Record
