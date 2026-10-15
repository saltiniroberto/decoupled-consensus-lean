import Proofs.Instance.Model
import Proofs.Instance.RunInvariant
import Proofs.Instance.Facts.Grades

/-!
# The image of the block receipt

The named image of the spec's block receipt `Member.on_block_with` is `NamedAdmission.on_block_with`
at the named image of the store, when the store meets `StoreOk` and `RunStoreInv` and no other tree
block has the received block's root (`image_on_block_with_of_not_held`). The file also proves the
lemmas this needs: the chain state of a new block, the image on a tree with distinct roots, the
finality update at the image, `RunStoreInv` along the store's writes, and the clips of the saved
grades.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace SpecRecord.SubtypeEqualities

open Spec
open SpecRecord.NoRaise
open scoped DC

variable {V : Type} [DecidableEq V]

/-! ## The chain state of a new block -/

/-- `process_attestation` keeps the blocks `T_h`, `J` and `F` of the chain state. -/
theorem process_attestation_blocks (σ : Protocol.ChainState V) (a : Attestation V) :
    (Protocol.process_attestation σ a).T_h = σ.T_h ∧ (Protocol.process_attestation σ a).J = σ.J ∧
      (Protocol.process_attestation σ a).F = σ.F := by
  unfold Protocol.process_attestation
  simp only [Id.run]
  split_ifs <;> exact ⟨rfl, rfl, rfl⟩

/-- Counting a list of attestations, in order, keeps the blocks `T_h`, `J` and `F` of the chain
    state. -/
theorem foldl_process_attestation_blocks (atts : List (Attestation V)) :
    ∀ σ : Protocol.ChainState V,
      (atts.foldl Protocol.process_attestation σ).T_h = σ.T_h ∧
        (atts.foldl Protocol.process_attestation σ).J = σ.J ∧
        (atts.foldl Protocol.process_attestation σ).F = σ.F := by
  induction atts with
  | nil => exact fun _ => ⟨rfl, rfl, rfl⟩
  | cons a atts ih =>
      intro σ
      obtain ⟨h1, h2, h3⟩ := ih (Protocol.process_attestation σ a)
      obtain ⟨k1, k2, k3⟩ := process_attestation_blocks σ a
      exact ⟨h1.trans k1, h2.trans k2, h3.trans k3⟩

/-- The chain state `state_transition C P σ B` of a new block `B` has latest block `B`; its block
    that entered its height is `σ.T_h` or `B`; its justified block is `σ.J` or `σ.T_h`; its
    finalized block is `σ.F` or `σ.J`. -/
theorem state_transition_blocks [Fintype V] (C : Config) (P : Provisional V)
    (σ : Protocol.ChainState V) (B : Block V) :
    (Protocol.state_transition C P σ B).L = B ∧
      ((Protocol.state_transition C P σ B).T_h = σ.T_h ∨
        (Protocol.state_transition C P σ B).T_h = B) ∧
      ((Protocol.state_transition C P σ B).J = σ.J ∨
        (Protocol.state_transition C P σ B).J = σ.T_h) ∧
      ((Protocol.state_transition C P σ B).F = σ.F ∨
        (Protocol.state_transition C P σ B).F = σ.J) := by
  simp only [Protocol.state_transition, Protocol.process_attestations, Id.run,
    List.forIn_pure_yield_eq_foldl, pure_bind]
  generalize hτ : List.foldl (fun b a => Protocol.process_attestation b a) { σ with s := B.slot }
    B.attestations = τ
  have hfold := foldl_process_attestation_blocks B.attestations { σ with s := B.slot }
  have hτ' : List.foldl Protocol.process_attestation { σ with s := B.slot } B.attestations = τ :=
    hτ
  rw [hτ'] at hfold
  obtain ⟨h1, h2, h3⟩ := hfold
  have hp : ∀ x : Protocol.ChainState V, (pure x : Id (Protocol.ChainState V)) = x := fun _ => rfl
  unfold Protocol.process_height_events
  simp only [Id.run, hp] at h1 h2 h3 ⊢
  split_ifs <;> simp [Protocol.advance_height, Id.run, hp, h1, h2, h3]

/-! ## Injectivity of the image on a tree -/

/-- `Block.toProof` is injective on a tree with distinct roots. -/
theorem injOn_of_distinctRoots {T : Finset (Block V)} (h : DistinctRoots T) :
    Set.InjOn (Block.toProof (V := V)) (↑T : Set (Block V)) := by
  intro B hB B' hB' e
  refine h B (Finset.mem_coe.mp hB) B' (Finset.mem_coe.mp hB') ?_
  have := congrArg DecoupledConsensusModel.Block.root e
  simpa only [Block.toProof_root, BlockId.toProof_inj] using this

/-- `Block.toProof` is injective on a tree with distinct roots extended by a block `X` whose root no
    other tree block has. -/
theorem injOn_insert {T : Finset (Block V)} (h : DistinctRoots T) {X : Block V}
    (hroot : ¬ RootHeldByOther T X) :
    Set.InjOn (Block.toProof (V := V)) (↑(T ∪ {X}) : Set (Block V)) := by
  have key : ∀ Y ∈ T, Y.toProof = X.toProof → Y = X := by
    intro Y hY e
    by_contra hne
    refine hroot ⟨Y, hY, hne, ?_⟩
    have := congrArg DecoupledConsensusModel.Block.root e
    simpa only [Block.toProof_root, BlockId.toProof_inj] using this
  intro B hB B' hB' e
  simp only [Finset.coe_union, Finset.coe_singleton, Set.mem_union, Set.mem_singleton_iff,
    Finset.mem_coe] at hB hB'
  rcases hB with hB | rfl <;> rcases hB' with hB' | rfl
  · exact injOn_of_distinctRoots h (Finset.mem_coe.mpr hB) (Finset.mem_coe.mpr hB') e
  · exact key B hB e
  · exact (key B' hB' e.symm).symm
  · rfl

/-- For a block `X` whose root no other block of `T` has,
    `X.toProof ∈ T.image Block.toProof ↔ X ∈ T`. -/
theorem toProof_mem_image_iff {T : Finset (Block V)} {X : Block V}
    (hroot : ¬ RootHeldByOther T X) : X.toProof ∈ T.image Block.toProof ↔ X ∈ T := by
  constructor
  · intro hm
    obtain ⟨Y, hY, e⟩ := Finset.mem_image.mp hm
    by_contra hX
    refine hroot ⟨Y, hY, fun h => hX (h ▸ hY), ?_⟩
    have := congrArg DecoupledConsensusModel.Block.root e
    simpa only [Block.toProof_root, BlockId.toProof_inj] using this
  · exact fun h => Finset.mem_image_of_mem _ h

/-! ## The reads of the image after a block is written -/

/-- For `C ≠ X.toProof`, when no other tree block has `X`'s root, the block standing for `C` in
    `st.T ∪ {X}` is either the block standing for `C` in `st.T` and a tree block, or neither of the
    two is in its tree. -/
theorem blockOfImageIn_insert_cases {st : Store V} (hd : DistinctRoots st.T) {X : Block V}
    (hroot : ¬ RootHeldByOther st.T X) (C : DecoupledConsensusModel.Block V)
    (hC : C ≠ X.toProof) :
    (Store.blockOfImageIn (st.T ∪ {X}) C = st.blockOfImage C ∧ st.blockOfImage C ∈ st.T) ∨
      (Store.blockOfImageIn (st.T ∪ {X}) C ∉ st.T ∪ {X} ∧ st.blockOfImage C ∉ st.T) := by
  by_cases hm : C ∈ st.T.image Block.toProof
  · obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.mp hm
    have e1 : st.blockOfImage Y.toProof = Y :=
      Store.blockOfImage_toProof_of_injOn st (injOn_of_distinctRoots hd) hY
    have e2 : Store.blockOfImageIn (st.T ∪ {X}) Y.toProof = Y :=
      Store.blockOfImage_toProof_of_injOn { st with T := st.T ∪ {X} } (injOn_insert hd hroot)
        (Finset.mem_union_left _ hY)
    exact Or.inl ⟨e2.trans e1.symm, by rw [e1]; exact hY⟩
  · refine Or.inr ⟨fun h => ?_, fun h => ?_⟩
    · rcases Finset.mem_union.mp h with h | h
      · exact hm (Store.toProof_blockOfImageIn (st.T ∪ {X}) C ▸ Finset.mem_image_of_mem _ h)
      · exact hC (by rw [← Finset.mem_singleton.mp h, Store.toProof_blockOfImageIn])
    · exact hm (Store.toProof_blockOfImage st C ▸ Finset.mem_image_of_mem _ h)

/-- When `st` has distinct roots, meets `OffTreeInitial`, and no other tree block has `X`'s root,
    the image of `st` with `X` written in (chain state `v`, in the tree, stamped at the store's
    clock) is the image of `st` with `X.toProof` written in the same way. -/
theorem toProof_write_block {st : Store V} (hd : DistinctRoots st.T) (hoff : OffTreeInitial st)
    {X : Block V} (hroot : ¬ RootHeldByOther st.T X) (v : Protocol.ChainState V) :
    ({ st.toProof with
        σ := fun C => if C = X.toProof then v.toProof else st.toProof.σ C
        T := insert X.toProof st.toProof.T
        timestamp_block := fun C =>
          if C = X.toProof then some (st.toProof.t : Stamp) else st.toProof.timestamp_block C } :
        DecoupledConsensusModel.Protocol.Store V) =
      ({ st with
          σ := Function.update st.σ X v
          T := st.T ∪ {X}
          timestamp_block := Function.update st.timestamp_block X (some (st.t : Stamp)) } :
        Store V).toProof := by
  have hXX : Store.blockOfImageIn (st.T ∪ {X}) X.toProof = X :=
    Store.blockOfImage_toProof_of_injOn { st with T := st.T ∪ {X} } (injOn_insert hd hroot)
      (Finset.mem_union_right _ (Finset.mem_singleton_self X))
  have hne : ∀ C, C ≠ X.toProof → Store.blockOfImageIn (st.T ∪ {X}) C ≠ X := by
    intro C hC h
    apply hC
    rw [← h, Store.toProof_blockOfImageIn]
  simp only [Store.toProof]
  congr 1
  · rw [Finset.image_union, Finset.image_singleton, Finset.insert_eq, Finset.union_comm]
  · funext C
    by_cases hC : C = X.toProof
    · subst hC
      simp only [if_true, Store.blockOfImage, hXX, Function.update_self]
    · simp only [hC, if_false]
      show st.timestamp_block (st.blockOfImage C) =
        Function.update st.timestamp_block X _ (Store.blockOfImageIn (st.T ∪ {X}) C)
      rw [Function.update_of_ne (hne C hC)]
      rcases blockOfImageIn_insert_cases hd hroot C hC with ⟨e, _⟩ | ⟨h1, h2⟩
      · rw [e]
      · rw [(hoff _ h2).2, (hoff _ fun h => h1 (Finset.mem_union_left _ h)).2]
  · funext C
    by_cases hC : C = X.toProof
    · subst hC
      simp only [if_true, Store.blockOfImage, hXX, Function.update_self]
    · simp only [hC, if_false]
      show (st.σ (st.blockOfImage C)).toProof =
        (Function.update st.σ X v (Store.blockOfImageIn (st.T ∪ {X}) C)).toProof
      rw [Function.update_of_ne (hne C hC)]
      rcases blockOfImageIn_insert_cases hd hroot C hC with ⟨e, _⟩ | ⟨h1, h2⟩
      · rw [e]
      · rw [(hoff _ h2).1, (hoff _ fun h => h1 (Finset.mem_union_left _ h)).1]

/-! ## The Goldfish votes a block includes -/

section Votes

variable [Fintype V]

/-- Admitting a list of Goldfish votes, in order, writes only the Goldfish votes and their stamps. -/
theorem foldl_checked_shape (P : Provisional V) (votes : List (GoldfishVote V)) (st : Store V) :
    ∃ x y, votes.foldl (Protocol.on_goldfish_vote_checked P) st =
      { st with gf_votes := x, timestamp_vote := y } := by
  induction votes generalizing st with
  | nil => exact ⟨_, _, rfl⟩
  | cons u votes ih =>
      obtain ⟨x, y, e⟩ : ∃ x y, Protocol.on_goldfish_vote_checked P st u =
          { st with gf_votes := x, timestamp_vote := y } := by
        unfold Protocol.on_goldfish_vote_checked Protocol.on_goldfish_vote
        simp only [Id.run, pure]
        split_ifs <;> exact ⟨_, _, rfl⟩
      obtain ⟨x', y', e'⟩ := ih (Protocol.on_goldfish_vote_checked P st u)
      rw [List.foldl_cons, e', e]
      exact ⟨x', y', rfl⟩

/-- Admitting the images of `votes`, in order, into the image of `st` gives the image of admitting
    `votes` into `st`, the committees read from `E`. -/
theorem toProof_foldl_checked (E : DecoupledConsensusModel.Env V)
    (votes : List (GoldfishVote V)) (st : Store V) :
    (votes.map GoldfishVote.toProof).foldl
        (DecoupledConsensusModel.Protocol.on_goldfish_vote_checked E) st.toProof =
      (votes.foldl (Protocol.on_goldfish_vote_checked (Provisional.toSpec E)) st).toProof := by
  induction votes generalizing st with
  | nil => rfl
  | cons vote votes ih =>
    simp only [List.map_cons, List.foldl_cons, toProof_on_goldfish_vote_checked, ih]

end Votes

/-! ## The finality update at the image -/

/-- When `Block.toProof` is injective on `st.T`, the tree is parent-closed and holds `st.F`, a tree
    block's image is in the viable tree of the image exactly when the block is in `st`'s viable
    tree. -/
theorem toProof_mem_viable_tree {st : Store V}
    (hinj : Set.InjOn (Block.toProof (V := V)) (↑st.T : Set (Block V)))
    (hpar : ParentClosed st.T) (hF : st.F ∈ st.T) {B : Block V} (hB : B ∈ st.T) (h : Height) :
    B.toProof ∈ DecoupledConsensusModel.Protocol.viable_tree st.toProof.σ st.F.toProof h
        (st.T.image Block.toProof) ↔
      B ∈ Protocol.viable_tree st.σ st.F h st.T := by
  simp only [DecoupledConsensusModel.Protocol.viable_tree,
    DecoupledConsensusModel.Protocol.finalized_descendants, DecoupledConsensusModel.Protocol.viable,
    Protocol.viable_tree, Protocol.finalized_descendants, Protocol.viable, Finset.mem_filter,
    decide_eq_true_eq, Finset.exists_mem_image]
  rw [Block.toProof_preceq_of_injOn st.T hinj hpar hF hB]
  have hw : ∀ W ∈ st.T, (DecoupledConsensusModel.Block.Preceq B.toProof W.toProof ∧
      h - 1 ≤ (st.toProof.σ W.toProof).h) ↔ (B.AncestorEq W ∧ h - 1 ≤ (st.σ W).h) := by
    intro W hW
    rw [Store.toProof_σ_of_mem st hinj hW, Protocol.ChainState.toProof_h]
    unfold DecoupledConsensusModel.Block.Preceq Block.AncestorEq
    rw [Block.toProof_preceq_of_injOn st.T hinj hpar hB hW]
  constructor
  · rintro ⟨⟨-, hFB⟩, W, hW, hW'⟩
    exact ⟨⟨hB, hFB⟩, W, hW, (hw W hW).mp hW'⟩
  · rintro ⟨⟨-, hFB⟩, W, hW, hW'⟩
    exact ⟨⟨Finset.mem_image_of_mem _ hB, hFB⟩, W, hW, (hw W hW).mpr hW'⟩

/-- When `Block.toProof` is injective on `st.T`, the tree is parent-closed and holds `st.F`, `st.J`,
    `σ.J` and `σ.F`, the finality update of the image of `st` from the image of `σ` is the image of
    `Handlers.updateFinalityWith st σ`. -/
theorem toProof_updateFinalityWith {st : Store V} (σ : Protocol.ChainState V)
    (hinj : Set.InjOn (Block.toProof (V := V)) (↑st.T : Set (Block V)))
    (hpar : ParentClosed st.T) (hF : st.F ∈ st.T) (hJ : st.J ∈ st.T) (hσJ : σ.J ∈ st.T)
    (hσF : σ.F ∈ st.T) :
    DecoupledConsensusModel.Protocol.update_finality st.toProof σ.toProof =
      (Handlers.updateFinalityWith st σ).toProof := by
  have e1 := Block.toProof_preceq_of_injOn st.T hinj hpar hF hσJ
  have e2 := Block.toProof_preceq_of_injOn st.T hinj hpar hσF hσJ
  have e3 := Block.toProof_preceq_of_injOn st.T hinj hpar hσF hJ
  have e4 := Block.toProof_preceq_of_injOn st.T hinj hpar hF hσF
  have e5 : (st.F.toProof = σ.F.toProof) ↔ st.F = σ.F :=
    ⟨fun h => hinj (Finset.mem_coe.mpr hF) (Finset.mem_coe.mpr hσF) h, fun h => by rw [h]⟩
  have ev := fun h => toProof_mem_viable_tree hinj hpar hF hσF h
  unfold DecoupledConsensusModel.Protocol.update_finality Handlers.updateFinalityWith
  simp only [Id.run, pure, Store.toProof_F, Store.toProof_J, Store.toProof_h_j,
    Store.toProof_h_max, Protocol.ChainState.toProof_J, Protocol.ChainState.toProof_h_j,
    Protocol.ChainState.toProof_F, Protocol.ChainState.toProof_h, Block.toProof_root,
    Protocol.heightId_mk_toProof_lt, e1, DecoupledConsensusModel.Block.prec, Block.ancestorStrict]
  by_cases c1 : (st.F.ancestorEq σ.J && decide ((st.h_j, st.J.root) <[lex] (σ.h_j, σ.J.root))) =
      true
  · simp only [c1, ↓reduceIte, e2, e4, e5, Store.toProof_T, ev]
    split_ifs <;> rfl
  · simp only [c1, ↓reduceIte, Bool.false_eq_true, e3, e4, e5, Store.toProof_T, ev]
    split_ifs <;> rfl

/-! ## The fields of a block's images -/

/-- The slot of a block's image is the block's slot. -/
theorem toProof_slot (X : Block V) : X.toProof.slot = X.slot := by cases X <;> simp [Block.toProof, Block.toProofNamed, Block.slot, Block.parent, Block.proposer?,
    Block.gf_votes, Block.attestations, DecoupledConsensusModel.Block.slot,
    DecoupledConsensusModel.Block.parent, DecoupledConsensusModel.Block.proposer?,
    DecoupledConsensusModel.Block.gf_votes, DecoupledConsensusModel.NamedBlock.parent,
    DecoupledConsensusModel.NamedBlock.attestations]

/-- The parent of a block's image is the image of the block's parent. -/
theorem toProof_parent (X : Block V) : X.toProof.parent = X.parent.toProof := by cases X <;> simp [Block.toProof, Block.toProofNamed, Block.slot, Block.parent, Block.proposer?,
    Block.gf_votes, Block.attestations, DecoupledConsensusModel.Block.slot,
    DecoupledConsensusModel.Block.parent, DecoupledConsensusModel.Block.proposer?,
    DecoupledConsensusModel.Block.gf_votes, DecoupledConsensusModel.NamedBlock.parent,
    DecoupledConsensusModel.NamedBlock.attestations]

/-- The parent of a block's named image is the named image of the block's parent. -/
theorem toProofNamed_parent (X : Block V) : X.toProofNamed.parent = X.parent.toProofNamed := by
  cases X <;> simp [Block.toProof, Block.toProofNamed, Block.slot, Block.parent, Block.proposer?,
    Block.gf_votes, Block.attestations, DecoupledConsensusModel.Block.slot,
    DecoupledConsensusModel.Block.parent, DecoupledConsensusModel.Block.proposer?,
    DecoupledConsensusModel.Block.gf_votes, DecoupledConsensusModel.NamedBlock.parent,
    DecoupledConsensusModel.NamedBlock.attestations]

/-- The proposer of a block's image is the block's proposer. -/
theorem toProof_proposer? (X : Block V) : X.toProof.proposer? = X.proposer? := by cases X <;> simp [Block.toProof, Block.toProofNamed, Block.slot, Block.parent, Block.proposer?,
    Block.gf_votes, Block.attestations, DecoupledConsensusModel.Block.slot,
    DecoupledConsensusModel.Block.parent, DecoupledConsensusModel.Block.proposer?,
    DecoupledConsensusModel.Block.gf_votes, DecoupledConsensusModel.NamedBlock.parent,
    DecoupledConsensusModel.NamedBlock.attestations]

/-- The Goldfish votes a block's image includes are the images of those the block includes. -/
theorem toProof_gf_votes (X : Block V) :
    X.toProof.gf_votes = X.gf_votes.map GoldfishVote.toProof := by
  cases X <;> simp [Block.toProof, Block.toProofNamed, Block.slot, Block.parent, Block.proposer?,
    Block.gf_votes, Block.attestations, DecoupledConsensusModel.Block.slot,
    DecoupledConsensusModel.Block.parent, DecoupledConsensusModel.Block.proposer?,
    DecoupledConsensusModel.Block.gf_votes, DecoupledConsensusModel.NamedBlock.parent,
    DecoupledConsensusModel.NamedBlock.attestations]

/-- The attestations a block's named image includes are the named images of those the block
includes. -/
theorem toProofNamed_attestations (X : Block V) :
    X.toProofNamed.attestations = X.attestations.map Attestation.toProofNamed := by
  cases X <;> simp [Block.toProof, Block.toProofNamed, Block.slot, Block.parent, Block.proposer?,
    Block.gf_votes, Block.attestations, DecoupledConsensusModel.Block.slot,
    DecoupledConsensusModel.Block.parent, DecoupledConsensusModel.Block.proposer?,
    DecoupledConsensusModel.Block.gf_votes, DecoupledConsensusModel.NamedBlock.parent,
    DecoupledConsensusModel.NamedBlock.attestations]

/-! ## The admission of a block, at the image -/

section Admission

variable [Fintype V]

/-- The store admits `X` exactly when `X` is not in the tree and its parent is, its attestations
    pass the round test, its slot is not later than the store's, the finalized block is an ancestor
    of it, its proposer is its slot's, and its parent's slot is earlier. -/
theorem block_admissible_iff (C : Config) (P : Provisional V) (st : Store V) (X : Block V) :
    Protocol.block_admissible C P st X = true ↔
      (X ∉ st.T ∧ X.parent ∈ st.T) ∧ Protocol.included_attestations_admissible C X = true ∧
        ¬ st.s < X.slot ∧ st.F.ancestorEq X = true ∧ X.proposer? = some (P.proposer X.slot) ∧
        X.parent.slot < X.slot := by
  unfold Protocol.block_admissible
  simp only [Id.run]
  split_ifs <;> first | rfl | (simp_all; done) | (simp_all; tauto)

/-- When `st` meets `StoreOk` and `RunStoreInv` and no other tree block has `X`'s root, the named
    image of `Handlers.admitBlockCore` at `X` is `NamedStore.process_block_core` at the named images
    of `st` and `X`. -/
theorem toProofNamed_admitBlockCore (E : DecoupledConsensusModel.Env V)
    (hc : DecoupledConsensusModel.Protocol.HealConfig)
    (cfg : DecoupledConsensusModel.Protocol.HeightConfig) {st : Store V} (hok : StoreOk st)
    (hinv : RunStoreInv st) (X : Block V) (hroot : ¬ RootHeldByOther st.T X) :
    (Handlers.admitBlockCore (Config.toSpec E hc cfg) (Provisional.toSpec E) st X).toProofNamed =
      DecoupledConsensusModel.Protocol.NamedStore.process_block_core E hc cfg st.toProofNamed
        X.toProofNamed := by
  obtain ⟨-, hd, hpc, hF⟩ := hok
  obtain ⟨hJ, hcs, hoff⟩ := hinv
  have hinjT := injOn_of_distinctRoots hd
  have hcommit : DecoupledConsensusModel.Protocol.NamedStore.commitBlock st.toProofNamed
      st.toProof X.toProofNamed = st.toProofNamed := by
    unfold DecoupledConsensusModel.Protocol.NamedStore.commitBlock
    simp only [Store.toProofNamed_core, Block.toProofNamed_erase]
    split_ifs with h
    · exact absurd h.2 h.1
    · rfl
  have hpar_named : X.toProofNamed.parent ∈ st.toProofNamed.bodies ↔ X.parent ∈ st.T := by
    rw [Store.toProofNamed_bodies, toProofNamed_parent, ← Block.coe_toProofNamedEmb,
      Finset.mem_map' Block.toProofNamedEmb]
  unfold Handlers.admitBlockCore DecoupledConsensusModel.Protocol.NamedStore.process_block_core
  simp only [hpar_named, Store.toProofNamed_core, Block.toProofNamed_erase]
  by_cases hadm : Protocol.block_admissible (Config.toSpec E hc cfg) (Provisional.toSpec E) st X
      = true
  · obtain ⟨⟨hX, hp⟩, hia, hs, hFX, hprop, hps⟩ :=
      (block_admissible_iff _ _ st X).mp hadm
    rw [if_pos hadm, if_neg (not_not.mpr hp)]
    have hpc' : ParentClosed (st.T ∪ {X}) := by
      intro Y hY
      rcases Finset.mem_union.mp hY with hY | hY
      · exact Finset.mem_union_left _ (hpc Y hY)
      · rw [Finset.mem_singleton.mp hY]
        exact Finset.mem_union_left _ hp
    have hinjX := injOn_insert hd hroot
    have hXmem : X ∈ st.T ∪ {X} := Finset.mem_union_right _ (Finset.mem_singleton_self X)
    have h1' : ¬ (st.toProof.s < X.toProof.slot ∨ X.toProof ∈ st.toProof.T ∨
        X.toProof.parent ∉ st.toProof.T) := by
      rw [Store.toProof_s, toProof_slot, Store.toProof_T, toProof_mem_image_iff hroot,
        toProof_parent]
      simp only [Finset.mem_image_of_mem _ hp, not_true_eq_false, or_false]
      rintro (h | h)
      · exact hs h
      · exact hX h
    have h2' : ¬ ((!DecoupledConsensusModel.Block.preceq st.toProof.F X.toProof) = true) := by
      rw [Store.toProof_F, Block.toProof_preceq_of_injOn (st.T ∪ {X}) hinjX hpc'
        (Finset.mem_union_left _ hF) hXmem, hFX]
      decide
    have h3' : ¬ (X.toProof.proposer? ≠ some (E.proposer X.toProof.slot)) := by
      rw [toProof_proposer?, toProof_slot]
      simpa [Provisional.toSpec] using hprop
    have h4' : ¬ ¬ (X.toProof.parent.slot < X.toProof.slot) := by
      rw [toProof_parent, toProof_slot, toProof_slot]
      exact not_not.mpr hps
    unfold DecoupledConsensusModel.Protocol.on_block_checked_using
    rw [toProof_carried_attestations_admissible E hc cfg, if_pos hia]
    unfold DecoupledConsensusModel.Protocol.on_block_using
    beta_reduce
    rw [if_neg h1', if_neg h2', if_neg h3', if_neg h4']
    set v := Protocol.state_transition (Config.toSpec E hc cfg) (Provisional.toSpec E)
      (st.σ X.parent) X with hv
    have hstate : DecoupledConsensusModel.Protocol.named_transition E cfg
        (st.toProof.σ X.toProof.parent) X.toProofNamed = v.toProof := by
      rw [toProof_parent, Store.toProof_σ_of_mem st hinjT hp, toProof_named_transition E hc cfg]
    simp only [hstate]
    rw [toProof_write_block hd hoff hroot v, toProof_gf_votes, toProof_foldl_checked]
    set st₁ : Store V := { st with
      σ := Function.update st.σ X v
      T := st.T ∪ {X}
      timestamp_block := Function.update st.timestamp_block X (some (st.t : Stamp)) } with hst₁
    obtain ⟨x, y, hst₂⟩ := foldl_checked_shape (Provisional.toSpec E) X.gf_votes st₁
    have hbc : Handlers.blockCore (Config.toSpec E hc cfg) (Provisional.toSpec E) st X =
        Handlers.updateFinalityWith
          (X.gf_votes.foldl (Protocol.on_goldfish_vote_checked (Provisional.toSpec E)) st₁)
          ((X.gf_votes.foldl (Protocol.on_goldfish_vote_checked (Provisional.toSpec E)) st₁).σ X) := by
      simp only [Handlers.blockCore, Id.run, List.forIn_pure_yield_eq_foldl]
      rfl
    rw [hbc, hst₂]
    have hσX : ({ st₁ with gf_votes := x, timestamp_vote := y } : Store V).σ X = v := by
      show Function.update st.σ X v X = v
      exact Function.update_self ..
    have hvb := state_transition_blocks (Config.toSpec E hc cfg) (Provisional.toSpec E)
      (st.σ X.parent) X
    obtain ⟨-, hcsL, hcsT, hcsJ, hcsF⟩ : True ∧ (st.σ X.parent).L ∈ st.T ∧
        (st.σ X.parent).T_h ∈ st.T ∧ (st.σ X.parent).J ∈ st.T ∧ (st.σ X.parent).F ∈ st.T :=
      ⟨trivial, hcs _ hp⟩
    have hvJ : v.J ∈ st.T ∪ {X} := by
      rcases hvb.2.2.1 with h | h <;> rw [h] <;> exact Finset.mem_union_left _ ‹_›
    have hvF : v.F ∈ st.T ∪ {X} := by
      rcases hvb.2.2.2 with h | h <;> rw [h] <;> exact Finset.mem_union_left _ ‹_›
    rw [Store.toProof_σ_of_mem _ hinjX hXmem, hσX,
      toProof_updateFinalityWith (st := { st₁ with gf_votes := x, timestamp_vote := y }) v hinjX
        hpc' (Finset.mem_union_left _ hF) (Finset.mem_union_left _ hJ) hvJ hvF]
    obtain ⟨a, b, c, d, hW⟩ :=
      OkStore.updateFinalityWith_shape ({ st₁ with gf_votes := x, timestamp_vote := y } : Store V) v
    rw [hW]
    unfold DecoupledConsensusModel.Protocol.NamedStore.commitBlock
    simp only [Store.toProofNamed_core, Block.toProofNamed_erase]
    rw [if_pos ⟨fun h => hX ((toProof_mem_image_iff hroot).mp h),
      Finset.mem_image_of_mem _ hXmem⟩]
    simp only [Store.toProofNamed]
    congr 1
    rw [Finset.map_union, Finset.map_singleton, Finset.insert_eq, Finset.union_comm]
    rfl
  · rw [if_neg hadm]
    split_ifs with hp
    · symm
      convert hcommit using 2
      unfold DecoupledConsensusModel.Protocol.on_block_checked_using
      rw [toProof_carried_attestations_admissible E hc cfg]
      split_ifs with hia
      · unfold DecoupledConsensusModel.Protocol.on_block_using
        have hp' : X.parent.toProof ∈ st.T.image Block.toProof :=
          Finset.mem_image_of_mem _ (hp)
        simp only [Store.toProof_s, toProof_slot, Store.toProof_T, toProof_mem_image_iff hroot,
          toProof_parent, hp', not_true_eq_false, or_false, toProof_proposer?, Store.toProof_F]
        by_cases hX : X ∈ st.T
        · simp [hX]
        · have hpc' : ParentClosed (st.T ∪ {X}) := by
            intro Y hY
            rcases Finset.mem_union.mp hY with hY | hY
            · exact Finset.mem_union_left _ (hpc Y hY)
            · rw [Finset.mem_singleton.mp hY]
              exact Finset.mem_union_left _ (hp)
          rw [Block.toProof_preceq_of_injOn (st.T ∪ {X}) (injOn_insert hd hroot) hpc'
            (Finset.mem_union_left _ hF) (Finset.mem_union_right _ (Finset.mem_singleton_self X))]
          rw [block_admissible_iff] at hadm
          split_ifs with h1 h2 h3 h4 <;> try rfl
          exfalso
          apply hadm
          refine ⟨⟨hX, hp⟩, hia, ?_, ?_, ?_, ?_⟩
          · exact fun h => h1 (Or.inl h)
          · simpa using h2
          · simpa [Provisional.toSpec] using h3
          · simpa [toProof_parent, toProof_slot] using h4
      · rfl
    · rfl

end Admission

/-! ## The block receipt -/

section Receipt

variable [Fintype V]

/-- `Handlers.blockCore C P st X` is the finality update, from `X`'s new chain state, of `st` with
    `X` written in (its chain state computed by `state_transition` from its parent's, `X` in the
    tree and stamped) and the Goldfish votes `X` includes admitted. -/
theorem blockCore_eq (C : Config) (P : Provisional V) (st : Store V) (X : Block V) :
    Handlers.blockCore C P st X =
      Handlers.updateFinalityWith
        (X.gf_votes.foldl (Protocol.on_goldfish_vote_checked P)
          { st with
            σ := Function.update st.σ X (Protocol.state_transition C P (st.σ X.parent) X)
            T := st.T ∪ {X}
            timestamp_block := Function.update st.timestamp_block X (some (st.t : Stamp)) })
        ((X.gf_votes.foldl (Protocol.on_goldfish_vote_checked P)
          { st with
            σ := Function.update st.σ X (Protocol.state_transition C P (st.σ X.parent) X)
            T := st.T ∪ {X}
            timestamp_block := Function.update st.timestamp_block X (some (st.t : Stamp)) }).σ X) := by
  simp only [Handlers.blockCore, Id.run, List.forIn_pure_yield_eq_foldl]
  rfl

/-- The tree of `Handlers.blockCore C P st X` is `st.T ∪ {X}`. -/
theorem blockCore_T (C : Config) (P : Provisional V) (st : Store V) (X : Block V) :
    (Handlers.blockCore C P st X).T = st.T ∪ {X} := by
  rw [blockCore_eq]
  obtain ⟨x, y, e⟩ := foldl_checked_shape P X.gf_votes
    { st with
      σ := Function.update st.σ X (Protocol.state_transition C P (st.σ X.parent) X)
      T := st.T ∪ {X}
      timestamp_block := Function.update st.timestamp_block X (some (st.t : Stamp)) }
  rw [e]
  obtain ⟨a, b, c, d, hW⟩ := OkStore.updateFinalityWith_shape
    ({ { st with
      σ := Function.update st.σ X (Protocol.state_transition C P (st.σ X.parent) X)
      T := st.T ∪ {X}
      timestamp_block := Function.update st.timestamp_block X (some (st.t : Stamp)) } with
      gf_votes := x, timestamp_vote := y } : Store V) (Function.update st.σ X
        (Protocol.state_transition C P (st.σ X.parent) X) X)
  rw [hW]

/-- When `st` meets `StoreOk` and `RunStoreInv` and no other tree block has the root of
    `Block.toSpecNamed B`, the named image of `Member.on_block_with` at `B` is
    `NamedAdmission.on_block_with` at the named image of `st` and `B`. -/
theorem image_on_block_with_of_not_held (adm : DecoupledConsensusModel.Protocol.CarriedAdmission)
    (E : DecoupledConsensusModel.Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig)
    (cfg : DecoupledConsensusModel.Protocol.HeightConfig) {st : Store V} (hok : StoreOk st)
    (hinv : RunStoreInv st) (B : DecoupledConsensusModel.NamedBlock V)
    (hroot : ¬ RootHeldByOther st.T (Block.toSpecNamed B)) :
    (Member.on_block_with adm E hc cfg st B).toProofNamed =
      DecoupledConsensusModel.Protocol.NamedAdmission.on_block_with adm E hc cfg st.toProofNamed
        B := by
  set X := Block.toSpecNamed B with hXdef
  have hB : X.toProofNamed = B := Block.toProofNamed_toSpecNamed B
  rw [← hB]
  unfold Member.on_block_with DecoupledConsensusModel.Protocol.NamedAdmission.on_block_with
    DecoupledConsensusModel.Protocol.NamedAdmission.admit_carried
  rw [← toProofNamed_admitBlockCore E hc cfg hok hinv X hroot, Handlers.on_block_eq,
    Block.toSpecNamed_toProofNamed]
  simp only [Store.toProofNamed_bodies, ← Block.coe_toProofNamedEmb,
    Finset.mem_map' Block.toProofNamedEmb]
  by_cases hadm : Protocol.block_admissible (Config.toSpec E hc cfg) (Provisional.toSpec E) st X
      = true
  · have hX := ((block_admissible_iff _ _ st X).mp hadm).1.1
    have hcore : Handlers.admitBlockCore (Config.toSpec E hc cfg) (Provisional.toSpec E) st X =
        Handlers.blockCore (Config.toSpec E hc cfg) (Provisional.toSpec E) st X := if_pos hadm
    rw [if_pos hadm, hcore, blockCore_T, if_pos ⟨hX, Finset.mem_union_right _
      (Finset.mem_singleton_self X)⟩, Block.coe_toProofNamedEmb, toProofNamed_attestations,
      toProof_admit_rows E hc cfg]
  · have hcore : Handlers.admitBlockCore (Config.toSpec E hc cfg) (Provisional.toSpec E) st X =
        st := if_neg hadm
    rw [if_neg hadm, hcore, if_neg (fun h => h.1 h.2)]

/-- If the tree after `on_block C P st B` has distinct roots, either the receipt left `st` unchanged
    or no other tree block of `st` had `B`'s root. -/
theorem on_block_cases_of_ok (C : Config) (P : Provisional V) {st : Store V} {B : Block V}
    (hok' : DistinctRoots (Protocol.on_block C P st B).T) :
    Protocol.on_block C P st B = st ∨ ¬ RootHeldByOther st.T B := by
  rw [Handlers.on_block_eq] at hok' ⊢
  by_cases hadm : Protocol.block_admissible C P st B = true
  · right
    rintro ⟨B', hB', hne, hr⟩
    rw [if_pos hadm, OkStore.admit_attestations_T] at hok'
    have hT : (Handlers.admitBlockCore C P st B).T = st.T ∪ {B} := by
      unfold Handlers.admitBlockCore
      rw [if_pos hadm, blockCore_T]
    rw [hT] at hok'
    exact hne (hok' B' (Finset.mem_union_left _ hB') B
      (Finset.mem_union_right _ (Finset.mem_singleton_self B)) hr)
  · left
    rw [if_neg hadm]

end Receipt

/-! ## `RunStoreInv` along the store's writes -/

/-- Admitting a list of attestations, in order, writes only the attestations and their stamps. -/
theorem admit_attestations_shape (C : Config) (st : Store V) (rows : List (Attestation V)) :
    ∃ x y, Protocol.admit_attestations C st rows =
      { st with attestations := x, timestamp_sg_vote := y } := by
  unfold Protocol.admit_attestations
  simp only [Id.run, List.forIn_pure_yield_eq_foldl]
  induction rows generalizing st with
  | nil => exact ⟨_, _, rfl⟩
  | cons a rows ih =>
      obtain ⟨x, y, e⟩ : ∃ x y, Protocol.admit_attestation C st a =
          { st with attestations := x, timestamp_sg_vote := y } := by
        unfold Protocol.admit_attestation Protocol.add_attestation
        simp only [Id.run, pure]
        split_ifs <;> exact ⟨_, _, rfl⟩
      obtain ⟨x', y', e'⟩ := ih (Protocol.admit_attestation C st a)
      simp only [List.foldl_cons] at e' ⊢
      rw [e', e]
      exact ⟨x', y', rfl⟩

/-- The initial store meets `RunStoreInv`. -/
theorem runStoreInv_init : RunStoreInv (Store.init : Store V) := by
  refine ⟨Finset.mem_singleton_self _, ?_, ?_⟩
  · intro B _
    simp [Store.init, Protocol.ChainState.initial]
  · intro B hB
    simp only [Store.init, Finset.mem_singleton] at hB
    simp [Store.init, hB]

/-- A write that keeps the tree, the chain states, the justified block and the block stamps keeps
    `RunStoreInv`. -/
theorem runStoreInv_of_frame {st st' : Store V} (h : RunStoreInv st) (hT : st'.T = st.T)
    (hσ : st'.σ = st.σ) (hJ : st'.J = st.J) (hτ : st'.timestamp_block = st.timestamp_block) :
    RunStoreInv st' := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨hT ▸ hJ ▸ h1, ?_, ?_⟩
  · intro B hB
    rw [hT] at hB ⊢
    rw [hσ]
    exact h2 B hB
  · intro B hB
    rw [hT] at hB
    rw [hσ, hτ]
    exact h3 B hB

/-- The block receipt `Protocol.on_block` keeps `RunStoreInv`. -/
theorem runStoreInv_on_block [Fintype V] (C : Config) (P : Provisional V) {st : Store V}
    (h : RunStoreInv st) (X : Block V) : RunStoreInv (Protocol.on_block C P st X) := by
  rw [Handlers.on_block_eq]
  by_cases hadm : Protocol.block_admissible C P st X = true
  · rw [if_pos hadm]
    obtain ⟨⟨hX, hp⟩, -⟩ := (block_admissible_iff C P st X).mp hadm
    have hcore : Handlers.admitBlockCore C P st X = Handlers.blockCore C P st X := if_pos hadm
    rw [hcore]
    obtain ⟨a, b, e⟩ := admit_attestations_shape C (Handlers.blockCore C P st X) X.attestations
    refine runStoreInv_of_frame ?_ (by rw [e]) (by rw [e]) (by rw [e]) (by rw [e])
    obtain ⟨hJ, hcs, hoff⟩ := h
    set v := Protocol.state_transition C P (st.σ X.parent) X with hv
    rw [blockCore_eq]
    obtain ⟨x, y, e2⟩ := foldl_checked_shape P X.gf_votes
      { st with
        σ := Function.update st.σ X v
        T := st.T ∪ {X}
        timestamp_block := Function.update st.timestamp_block X (some (st.t : Stamp)) }
    rw [e2]
    have hσX : Function.update st.σ X v X = v := Function.update_self ..
    obtain ⟨a', b', c', d', hW⟩ := OkStore.updateFinalityWith_shape
      ({ { st with
        σ := Function.update st.σ X v
        T := st.T ∪ {X}
        timestamp_block := Function.update st.timestamp_block X (some (st.t : Stamp)) } with
        gf_votes := x, timestamp_vote := y } : Store V) (Function.update st.σ X v X)
    have hJ' : (Handlers.updateFinalityWith
        ({ { st with
          σ := Function.update st.σ X v
          T := st.T ∪ {X}
          timestamp_block := Function.update st.timestamp_block X (some (st.t : Stamp)) } with
          gf_votes := x, timestamp_vote := y } : Store V) (Function.update st.σ X v X)).J = st.J ∨
        (Handlers.updateFinalityWith
        ({ { st with
          σ := Function.update st.σ X v
          T := st.T ∪ {X}
          timestamp_block := Function.update st.timestamp_block X (some (st.t : Stamp)) } with
          gf_votes := x, timestamp_vote := y } : Store V) (Function.update st.σ X v X)).J = v.J := by
      unfold Handlers.updateFinalityWith
      simp only [Id.run, pure, hσX]
      split_ifs <;> simp
    rw [hW] at hJ' ⊢
    obtain ⟨-, hvT, hvJ, hvF⟩ := state_transition_blocks C P (st.σ X.parent) X
    obtain ⟨hpL, hpT, hpJ, hpF⟩ := hcs _ hp
    have hXm : X ∈ st.T ∪ {X} := Finset.mem_union_right _ (Finset.mem_singleton_self X)
    simp only at hJ' ⊢
    refine ⟨?_, ?_, ?_⟩
    · rcases hJ' with e | e <;> rw [e]
      · exact Finset.mem_union_left _ hJ
      · rcases hvJ with e' | e' <;> rw [e'] <;> exact Finset.mem_union_left _ ‹_›
    · intro B hB
      dsimp only at hB ⊢
      by_cases hBX : B = X
      · subst hBX
        rw [hσX]
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [state_transition_blocks C P (st.σ B.parent) B |>.1]; exact hXm
        · rcases hvT with e' | e' <;> rw [e']
          · exact Finset.mem_union_left _ hpT
          · exact hXm
        · rcases hvJ with e' | e' <;> rw [e'] <;> exact Finset.mem_union_left _ ‹_›
        · rcases hvF with e' | e' <;> rw [e'] <;> exact Finset.mem_union_left _ ‹_›
      · have hBT : B ∈ st.T := by
          rcases Finset.mem_union.mp hB with h | h
          · exact h
          · exact absurd (Finset.mem_singleton.mp h) hBX
        rw [Function.update_of_ne hBX]
        obtain ⟨k1, k2, k3, k4⟩ := hcs B hBT
        exact ⟨Finset.mem_union_left _ k1, Finset.mem_union_left _ k2, Finset.mem_union_left _ k3,
          Finset.mem_union_left _ k4⟩
    · intro B hB
      dsimp only at hB ⊢
      have hBX : B ≠ X := fun h => hB (h ▸ hXm)
      have hBT : B ∉ st.T := fun h => hB (Finset.mem_union_left _ h)
      rw [Function.update_of_ne hBX, Function.update_of_ne hBX]
      exact hoff B hBT
  · rw [if_neg hadm]
    exact h

/-! ## The stamps the block core writes -/

/-- The block stamps of `Handlers.blockCore C P st X` are the store's, with `X` stamped at the
    store's clock. -/
theorem blockCore_timestamp_block [Fintype V] (C : Config) (P : Provisional V) (st : Store V)
    (X : Block V) :
    (Handlers.blockCore C P st X).timestamp_block =
      Function.update st.timestamp_block X (some (st.t : Stamp)) := by
  rw [blockCore_eq]
  obtain ⟨x, y, e⟩ := foldl_checked_shape P X.gf_votes
    { st with
      σ := Function.update st.σ X (Protocol.state_transition C P (st.σ X.parent) X)
      T := st.T ∪ {X}
      timestamp_block := Function.update st.timestamp_block X (some (st.t : Stamp)) }
  rw [e]
  obtain ⟨a, b, c, d, hW⟩ := OkStore.updateFinalityWith_shape
    ({ { st with
      σ := Function.update st.σ X (Protocol.state_transition C P (st.σ X.parent) X)
      T := st.T ∪ {X}
      timestamp_block := Function.update st.timestamp_block X (some (st.t : Stamp)) } with
      gf_votes := x, timestamp_vote := y } : Store V) (Function.update st.σ X
        (Protocol.state_transition C P (st.σ X.parent) X) X)
  rw [hW]

/-!
## The two clips of the saved grades

The receipt and the tick clip the saved grades at the finalized block `F`
(`make_saved_grades_compatible_with`); the member `clipCache` clips at the image of `F`. The lemmas
say that `clipCache` leaves grades already clipped at `F` unchanged.
-/

/-- `GradesLocal.clipBlock g F` is compatible with `F`. -/
theorem clipBlock_compatible (g F : Block V) :
    (GradesLocal.clipBlock g F).compatible F = true := by
  induction g with
  | genesis =>
      simp [GradesLocal.clipBlock, Block.compatible, GradesLocal.genesis_ancestorEq]
  | node p s r gv gsv ats v ih =>
      simp only [GradesLocal.clipBlock]
      split_ifs with h
      · exact h
      · exact ih

/-- `deepest_compatible_ancestor g F` is compatible with `F`. -/
theorem deepest_compatible_ancestor_compatible (g F : Block V) :
    (Protocol.deepest_compatible_ancestor g F).compatible F = true := by
  rw [GradesLocal.deepest_compatible_ancestor_eq]
  exact clipBlock_compatible g F

/-- `clipBlockImage` at `F.toProof` keeps a block compatible with `F`. -/
theorem clipBlockImage_of_compatible {F g : Block V} (h : g.compatible F = true) :
    clipBlockImage F.toProof g = g := by
  have hc := Block.toProof_compatible_of_compatible g F h
  unfold clipBlockImage
  simp only [Id.run]
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size]
  rw [show (g.depth + 1 - 0 + 1 - 1) / 1 = g.depth + 1 by omega, List.range'_succ, List.forIn_cons,
    if_pos hc]
  rfl

/-- `clipResultImage` at `F.toProof` keeps a grade result already clipped at `F`. -/
theorem clipResultImage_make_result (F : Block V) (r : GradeResult V) :
    clipResultImage F.toProof (Protocol.make_result_compatible_with F r) =
      Protocol.make_result_compatible_with F r := by
  have hp : ∀ x : GradeResult V, (pure x : Id (GradeResult V)) = x := fun _ => rfl
  cases r with
  | pending => simp [Protocol.make_result_compatible_with, clipResultImage, Id.run, hp]
  | computed G =>
    cases G with
    | none => rfl
    | some G =>
      show GradeResult.computed (some (clipBlockImage F.toProof
          (Protocol.deepest_compatible_ancestor G F))) =
        GradeResult.computed (some (Protocol.deepest_compatible_ancestor G F))
      rw [clipBlockImage_of_compatible (deepest_compatible_ancestor_compatible G F)]

/-- `Member.clipCache` at `F.toProof` keeps saved grades already clipped at `F`. -/
theorem clipCache_make_saved_grades_compatible_with [Fintype V] (F : Block V)
    (c : SavedGrades V) :
    Member.clipCache F.toProof (Protocol.make_saved_grades_compatible_with F c) =
      Protocol.make_saved_grades_compatible_with F c := by
  simp [Member.clipCache, Member.clipFrame, Protocol.make_saved_grades_compatible_with,
    Protocol.make_round_grades_compatible_with, clipResultImage_make_result]

/-! ## The fields the receipt writes -/

/-- `Handlers.updateFinalityWith st σ` sets `h_max` to `max st.h_max σ.h`; keeps the justified block
    and height, or sets them to `σ.J` and `σ.h_j` when `st.F` is an ancestor of `σ.J`; keeps the
    finalized block, or sets it to `σ.F` when `σ.F` is an ancestor of the justified block the update
    leaves. -/
theorem updateFinalityWith_vals (st : Store V) (σ : Protocol.ChainState V) :
    (Handlers.updateFinalityWith st σ).h_max = max st.h_max σ.h ∧
      (((Handlers.updateFinalityWith st σ).J = st.J ∧
          (Handlers.updateFinalityWith st σ).h_j = st.h_j) ∨
        ((Handlers.updateFinalityWith st σ).J = σ.J ∧
          (Handlers.updateFinalityWith st σ).h_j = σ.h_j ∧ st.F.ancestorEq σ.J = true)) ∧
      ((Handlers.updateFinalityWith st σ).F = st.F ∨
        ((Handlers.updateFinalityWith st σ).F = σ.F ∧
          σ.F.ancestorEq (Handlers.updateFinalityWith st σ).J = true)) := by
  unfold Handlers.updateFinalityWith
  simp only [Id.run, pure]
  split_ifs with h1 h2 h3 <;> simp_all

/-- A receipt of a named object either keeps the tree, the chain states, the block stamps, `h_max`,
    the justified block and height and the finalized block, or admits a block `B` whose spec form
    `X` joins the tree with the chain state `v` computed from its parent's and the stamp `st.t`,
    `h_max` becomes `max st.h_max v.h`, and the justified and finalized blocks move as
    `updateFinalityWith_vals` says. -/
theorem receipt_cases [Fintype V] [Inhabited V] (S : DecoupledConsensusModel.Execution.Setup V)
    (st : Store V) (o : DecoupledConsensusModel.Execution.NamedObject V) :
    ((Member.receipt_process S st o).T = st.T ∧ (Member.receipt_process S st o).σ = st.σ ∧
      (Member.receipt_process S st o).timestamp_block = st.timestamp_block ∧
      (Member.receipt_process S st o).h_max = st.h_max ∧
      (Member.receipt_process S st o).J = st.J ∧ (Member.receipt_process S st o).h_j = st.h_j ∧
      (Member.receipt_process S st o).F = st.F) ∨
    ∃ B, o = .block B ∧
      Protocol.block_admissible (Config.toSpec S.E S.hc S.cfg) (Provisional.toSpec S.E) st
        (Block.toSpecNamed B) = true ∧
      (Member.receipt_process S st o).T = st.T ∪ {Block.toSpecNamed B} ∧
      (Member.receipt_process S st o).σ = Function.update st.σ (Block.toSpecNamed B)
        (Protocol.state_transition (Config.toSpec S.E S.hc S.cfg) (Provisional.toSpec S.E)
          (st.σ (Block.toSpecNamed B).parent) (Block.toSpecNamed B)) ∧
      (Member.receipt_process S st o).timestamp_block =
        Function.update st.timestamp_block (Block.toSpecNamed B) (some (st.t : Stamp)) ∧
      (Member.receipt_process S st o).h_max = max st.h_max
        (Protocol.state_transition (Config.toSpec S.E S.hc S.cfg) (Provisional.toSpec S.E)
          (st.σ (Block.toSpecNamed B).parent) (Block.toSpecNamed B)).h ∧
      (((Member.receipt_process S st o).J = st.J ∧ (Member.receipt_process S st o).h_j = st.h_j) ∨
        ((Member.receipt_process S st o).J =
            (Protocol.state_transition (Config.toSpec S.E S.hc S.cfg) (Provisional.toSpec S.E)
              (st.σ (Block.toSpecNamed B).parent) (Block.toSpecNamed B)).J ∧
          (Member.receipt_process S st o).h_j =
            (Protocol.state_transition (Config.toSpec S.E S.hc S.cfg) (Provisional.toSpec S.E)
              (st.σ (Block.toSpecNamed B).parent) (Block.toSpecNamed B)).h_j ∧
          st.F.ancestorEq (Protocol.state_transition (Config.toSpec S.E S.hc S.cfg)
            (Provisional.toSpec S.E) (st.σ (Block.toSpecNamed B).parent) (Block.toSpecNamed B)).J
            = true)) ∧
      ((Member.receipt_process S st o).F = st.F ∨
        ((Member.receipt_process S st o).F =
            (Protocol.state_transition (Config.toSpec S.E S.hc S.cfg) (Provisional.toSpec S.E)
              (st.σ (Block.toSpecNamed B).parent) (Block.toSpecNamed B)).F ∧
          (Protocol.state_transition (Config.toSpec S.E S.hc S.cfg) (Provisional.toSpec S.E)
              (st.σ (Block.toSpecNamed B).parent) (Block.toSpecNamed B)).F.ancestorEq
            (Member.receipt_process S st o).J = true)) := by
  cases o with
  | gfVote u =>
    left
    obtain ⟨x, y, e⟩ := foldl_checked_shape (Provisional.toSpec S.E) [GoldfishVote.toSpec u] st
    have e' : Member.receipt_process S st (.gfVote u) = { st with gf_votes := x, timestamp_vote := y } :=
      e
    rw [e']
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | attest a =>
    left
    obtain ⟨x, y, e⟩ := admit_attestations_shape (Config.toSpec S.E S.hc S.cfg) st
      [Attestation.toSpecNamed a]
    have e' : Member.receipt_process S st (.attest a) =
        { st with attestations := x, timestamp_sg_vote := y } := by
      rw [← e]
      simp only [Protocol.admit_attestations, Id.run, List.forIn_pure_yield_eq_foldl,
        List.foldl_cons, List.foldl_nil]
      rfl
    rw [e']
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | block B =>
    have hrp : Member.receipt_process S st (.block B) =
        Protocol.on_block (Config.toSpec S.E S.hc S.cfg) (Provisional.toSpec S.E) st
          (Block.toSpecNamed B) := rfl
    rw [hrp, Handlers.on_block_eq]
    by_cases hadm : Protocol.block_admissible (Config.toSpec S.E S.hc S.cfg)
        (Provisional.toSpec S.E) st (Block.toSpecNamed B) = true
    · right
      refine ⟨B, rfl, hadm, ?_⟩
      rw [if_pos hadm]
      have hcore : Handlers.admitBlockCore (Config.toSpec S.E S.hc S.cfg) (Provisional.toSpec S.E)
          st (Block.toSpecNamed B) = Handlers.blockCore (Config.toSpec S.E S.hc S.cfg)
            (Provisional.toSpec S.E) st (Block.toSpecNamed B) := if_pos hadm
      rw [hcore]
      obtain ⟨x, y, e⟩ := admit_attestations_shape (Config.toSpec S.E S.hc S.cfg)
        (Handlers.blockCore (Config.toSpec S.E S.hc S.cfg) (Provisional.toSpec S.E) st
          (Block.toSpecNamed B)) (Block.toSpecNamed B).attestations
      rw [e]
      simp only
      rw [blockCore_eq]
      obtain ⟨x', y', e'⟩ := foldl_checked_shape (Provisional.toSpec S.E)
        (Block.toSpecNamed B).gf_votes
        { st with
          σ := Function.update st.σ (Block.toSpecNamed B)
            (Protocol.state_transition (Config.toSpec S.E S.hc S.cfg) (Provisional.toSpec S.E)
              (st.σ (Block.toSpecNamed B).parent) (Block.toSpecNamed B))
          T := st.T ∪ {Block.toSpecNamed B}
          timestamp_block := Function.update st.timestamp_block (Block.toSpecNamed B)
            (some (st.t : Stamp)) }
      rw [e']
      obtain ⟨v1, v2, v3⟩ := updateFinalityWith_vals
        ({ { st with
          σ := Function.update st.σ (Block.toSpecNamed B)
            (Protocol.state_transition (Config.toSpec S.E S.hc S.cfg) (Provisional.toSpec S.E)
              (st.σ (Block.toSpecNamed B).parent) (Block.toSpecNamed B))
          T := st.T ∪ {Block.toSpecNamed B}
          timestamp_block := Function.update st.timestamp_block (Block.toSpecNamed B)
            (some (st.t : Stamp)) } with gf_votes := x', timestamp_vote := y' } : Store V)
        (Function.update st.σ (Block.toSpecNamed B)
            (Protocol.state_transition (Config.toSpec S.E S.hc S.cfg) (Provisional.toSpec S.E)
              (st.σ (Block.toSpecNamed B).parent) (Block.toSpecNamed B)) (Block.toSpecNamed B))
      obtain ⟨a', b', c', d', hW⟩ := OkStore.updateFinalityWith_shape
        ({ { st with
          σ := Function.update st.σ (Block.toSpecNamed B)
            (Protocol.state_transition (Config.toSpec S.E S.hc S.cfg) (Provisional.toSpec S.E)
              (st.σ (Block.toSpecNamed B).parent) (Block.toSpecNamed B))
          T := st.T ∪ {Block.toSpecNamed B}
          timestamp_block := Function.update st.timestamp_block (Block.toSpecNamed B)
            (some (st.t : Stamp)) } with gf_votes := x', timestamp_vote := y' } : Store V)
        (Function.update st.σ (Block.toSpecNamed B)
            (Protocol.state_transition (Config.toSpec S.E S.hc S.cfg) (Provisional.toSpec S.E)
              (st.σ (Block.toSpecNamed B).parent) (Block.toSpecNamed B)) (Block.toSpecNamed B))
      rw [hW] at v1 v2 v3 ⊢
      simp only [Function.update_self] at v1 v2 v3 ⊢
      exact ⟨trivial, trivial, trivial, v1, v2, v3⟩
    · left
      rw [if_neg hadm]
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The height of the chain state of a new block is at most its parent's height plus one. -/
theorem state_transition_h_le_succ [Fintype V] (C : Config) (P : Provisional V)
    (σ : Protocol.ChainState V) (B : Block V) :
    (Protocol.state_transition C P σ B).h ≤ σ.h + 1 := by
  have hfold : ∀ (atts : List (Attestation V)) (τ : Protocol.ChainState V),
      (atts.foldl Protocol.process_attestation τ).h = τ.h := by
    intro atts
    induction atts with
    | nil => exact fun _ => rfl
    | cons a atts ih =>
        intro τ
        rw [List.foldl_cons, ih]
        unfold Protocol.process_attestation
        simp only [Id.run]
        split_ifs <;> rfl
  have hp : ∀ x : Protocol.ChainState V, (pure x : Id (Protocol.ChainState V)) = x := fun _ => rfl
  simp only [Protocol.state_transition, Protocol.process_attestations, Id.run,
    List.forIn_pure_yield_eq_foldl, pure_bind]
  generalize hτ : List.foldl (fun b a => Protocol.process_attestation b a) { σ with s := B.slot }
    B.attestations = τ
  have hτh : τ.h = σ.h := by
    rw [← hτ]
    exact hfold B.attestations { σ with s := B.slot }
  unfold Protocol.process_height_events
  simp only [Id.run, hp]
  split_ifs <;> simp [Protocol.advance_height, Id.run, hp, hτh]

end SpecRecord.SubtypeEqualities
