import Proofs.Instance.Objects
import Proofs.Instance.NoRaise.Predicates

/-!
# Ancestry at the blocks standing for images

A block `B` of `DecoupledConsensusModel.Block V` is read in the spec's type either as
`st.blockOfImage B`, the block standing for `B` on the store `st`, or as `Block.toSpec B`. Both
readings keep parents and ancestry. The file also defines the reading of saved grades and of a store
through the store's tree (`Store.contractOfImage`, `Store.ofImage`).
-/

set_option autoImplicit false

namespace SpecDraftRecord.NoRaise

open Spec

variable {V : Type}

/-- On a tree whose blocks have distinct roots, `Block.toProof` is injective. -/
theorem DistinctRoots.injOn_toProof {T : Finset (Block V)} (hT : DistinctRoots T) :
    Set.InjOn (Block.toProof (V := V)) (↑T : Set (Block V)) := by
  intro B hB B' hB' h
  refine hT B (Finset.mem_coe.mp hB) B' (Finset.mem_coe.mp hB') ?_
  have := congrArg DecoupledConsensusModel.Block.root h
  simpa only [Block.toProof_root, BlockId.toProof_inj] using this

end SpecDraftRecord.NoRaise

namespace Spec

open SpecDraftRecord.NoRaise (ParentClosed DistinctRoots)

variable {V : Type} [DecidableEq V]

/-! ## The block standing for an image keeps ancestry -/

namespace Store

/-- On a store whose tree is parent-closed and on which `Block.toProof` is injective, the block
    standing for the parent of `B` is the parent of the block standing for `B`. -/
theorem blockOfImage_parent (st : Store V)
    (hinj : Set.InjOn (Block.toProof (V := V)) (↑st.T : Set (Block V)))
    (hpar : ParentClosed st.T) (B : DecoupledConsensusModel.Block V) :
    st.blockOfImage B.parent = (st.blockOfImage B).parent := by
  cases B with
  | genesis => rfl
  | node p s r votes support ats proposer =>
      show blockOfImageIn st.T p = (blockOfImageIn st.T (.node p s r votes support ats proposer)).parent
      cases hpk : pickUnique? st.T
          (fun B' => decide (B'.toProof = .node p s r votes support ats proposer)) with
      | none =>
          simp only [blockOfImageIn, hpk, Option.getD, Block.parent]
      | some Z =>
          obtain ⟨hZ, himg⟩ := blockWithImage?_eq_some st hpk
          have hlhs : blockOfImageIn st.T (.node p s r votes support ats proposer) = Z := by
            simp only [blockOfImageIn, hpk, Option.getD]
          rw [hlhs]
          cases Z with
          | genesis => cases himg
          | node p' s' r' votes' support' ats' proposer' =>
              simp only [Block.toProof, DecoupledConsensusModel.Block.node.injEq] at himg
              rw [← himg.1]
              exact blockOfImage_toProof_of_injOn st hinj (hpar _ hZ)

/-- On a store whose tree is parent-closed and on which `Block.toProof` is injective, the block
    standing for `A` is an ancestor of, or equal to, the block standing for `B` exactly when `A` is
    an ancestor of, or equal to, `B`. -/
theorem blockOfImage_ancestorEq (st : Store V)
    (hinj : Set.InjOn (Block.toProof (V := V)) (↑st.T : Set (Block V)))
    (hpar : ParentClosed st.T) (A B : DecoupledConsensusModel.Block V) :
    (st.blockOfImage A).ancestorEq (st.blockOfImage B) = DecoupledConsensusModel.Block.preceq A B := by
  induction B with
  | genesis =>
      have hg : st.blockOfImage (DecoupledConsensusModel.Block.genesis : DecoupledConsensusModel.Block V)
          = .genesis := rfl
      have hA : st.blockOfImage A = .genesis ↔ A = .genesis := by
        constructor
        · intro h
          have := toProof_blockOfImage st A
          rw [h] at this
          exact this.symm
        · intro h
          subst h
          rfl
      rw [hg, Block.ancestorEq, DecoupledConsensusModel.Block.preceq]
      simp only [hA]
  | node p s r votes support ats proposer ih =>
      obtain ⟨q, s', r', votes', support', ats', proposer', hX⟩ :
          ∃ q s' r' votes' support' ats' proposer',
            st.blockOfImage (.node p s r votes support ats proposer) =
              .node q s' r' votes' support' ats' proposer' := by
        cases h : st.blockOfImage (.node p s r votes support ats proposer) with
        | genesis =>
            have := toProof_blockOfImage st (.node p s r votes support ats proposer)
            rw [h] at this
            cases this
        | node q s' r' votes' support' ats' proposer' =>
            exact ⟨q, s', r', votes', support', ats', proposer', rfl⟩
      have hq : q = st.blockOfImage p := by
        have := blockOfImage_parent st hinj hpar (.node p s r votes support ats proposer)
        rw [hX] at this
        exact this.symm
      rw [hX, Block.ancestorEq, ← hX, hq, ih, DecoupledConsensusModel.Block.preceq]
      simp only [(blockOfImage_injective st).eq_iff]

/-- `Store.blockOfImage_ancestorEq` with distinct roots (`DistinctRoots st.T`) in place of
    injectivity. -/
theorem blockOfImage_ancestorEq_of_distinctRoots (st : Store V) (hT : DistinctRoots st.T)
    (hpar : ParentClosed st.T) (A B : DecoupledConsensusModel.Block V) :
    (st.blockOfImage A).ancestorEq (st.blockOfImage B) = DecoupledConsensusModel.Block.preceq A B :=
  blockOfImage_ancestorEq st hT.injOn_toProof hpar A B

/-- A block `X` of the tree is an ancestor of, or equal to, the block standing for `B` exactly when
    the image of `X` is an ancestor of, or equal to, `B`. -/
theorem ancestorEq_blockOfImage_of_mem (st : Store V)
    (hinj : Set.InjOn (Block.toProof (V := V)) (↑st.T : Set (Block V)))
    (hpar : ParentClosed st.T) {X : Block V} (hX : X ∈ st.T)
    (B : DecoupledConsensusModel.Block V) :
    X.ancestorEq (st.blockOfImage B) = DecoupledConsensusModel.Block.preceq X.toProof B := by
  conv_lhs => rw [← blockOfImage_toProof_of_injOn st hinj hX]
  exact blockOfImage_ancestorEq st hinj hpar X.toProof B

/-- The block standing for `A` is an ancestor of, or equal to, a block `X` of the tree exactly when
    `A` is an ancestor of, or equal to, the image of `X`. -/
theorem blockOfImage_ancestorEq_of_mem (st : Store V)
    (hinj : Set.InjOn (Block.toProof (V := V)) (↑st.T : Set (Block V)))
    (hpar : ParentClosed st.T) (A : DecoupledConsensusModel.Block V) {X : Block V}
    (hX : X ∈ st.T) :
    (st.blockOfImage A).ancestorEq X = DecoupledConsensusModel.Block.preceq A X.toProof := by
  conv_lhs => rw [← blockOfImage_toProof_of_injOn st hinj hX]
  exact blockOfImage_ancestorEq st hinj hpar A X.toProof

/-- On a store whose tree is parent-closed and on which `Block.toProof` is injective, the blocks
    standing for `A` and `B` are compatible exactly when `A` and `B` are. -/
theorem blockOfImage_compatible (st : Store V)
    (hinj : Set.InjOn (Block.toProof (V := V)) (↑st.T : Set (Block V)))
    (hpar : ParentClosed st.T) (A B : DecoupledConsensusModel.Block V) :
    (st.blockOfImage A).compatible (st.blockOfImage B) = DecoupledConsensusModel.Block.compatible A B := by
  simp only [Block.compatible, DecoupledConsensusModel.Block.compatible,
    blockOfImage_ancestorEq st hinj hpar]

/-- A block `X` of the tree and the block standing for `B` are compatible exactly when the image of
    `X` and `B` are. -/
theorem compatible_blockOfImage_of_mem (st : Store V)
    (hinj : Set.InjOn (Block.toProof (V := V)) (↑st.T : Set (Block V)))
    (hpar : ParentClosed st.T) {X : Block V} (hX : X ∈ st.T)
    (B : DecoupledConsensusModel.Block V) :
    X.compatible (st.blockOfImage B) = DecoupledConsensusModel.Block.compatible X.toProof B := by
  conv_lhs => rw [← blockOfImage_toProof_of_injOn st hinj hX]
  exact blockOfImage_compatible st hinj hpar X.toProof B

end Store

/-! ## `Block.toSpec` keeps ancestry -/

namespace Block

omit [DecidableEq V] in
/-- `Block.toSpec` keeps the depth. -/
theorem toSpec_depth (B : DecoupledConsensusModel.Block V) : (Block.toSpec B).depth = B.depth := by
  rw [← Block.toProof_depth, Block.toProof_toSpec]

/-- The genesis block is an ancestor of, or equal to, every block. -/
theorem genesis_ancestorEq (B : Block V) : Block.ancestorEq .genesis B = true := by
  induction B with
  | genesis => simp [Block.ancestorEq]
  | node p s root gv gsv ats v ih => simp [Block.ancestorEq, ih]

/-- `Block.toSpec A` is an ancestor of, or equal to, `Block.toSpec B` exactly when `A` is an
    ancestor of, or equal to, `B`. -/
theorem toSpec_ancestorEq (A B : DecoupledConsensusModel.Block V) :
    (Block.toSpec A).ancestorEq (Block.toSpec B) = DecoupledConsensusModel.Block.preceq A B := by
  induction B with
  | genesis =>
      show (Block.toSpec A).ancestorEq Block.genesis = _
      rw [Block.ancestorEq, DecoupledConsensusModel.Block.preceq]
      have e : (Block.genesis : Block V) = Block.toSpec DecoupledConsensusModel.Block.genesis := rfl
      rw [e]
      simp only [Block.toSpec_injective.eq_iff]
  | node p s r votes support ats proposer ih =>
      have e : Block.toSpec (DecoupledConsensusModel.Block.node p s r votes support ats proposer) =
          Block.node (Block.toSpec p) s (BlockId.toSpec r) (votes.map GoldfishVote.toSpec)
            (support.map GoldfishVote.toSpec) (ats.map Attestation.toSpec) proposer := rfl
      rw [e, Block.ancestorEq, ← e, DecoupledConsensusModel.Block.preceq, ih]
      simp only [Block.toSpec_injective.eq_iff]

/-- The deepest block of `S.image Block.toSpec`, mapped back, is the deepest block of `S`. -/
theorem deepest?_image_toSpec (S : Finset (DecoupledConsensusModel.Block V)) :
    (Block.deepest? (S.image Block.toSpec)).map Block.toProof =
      DecoupledConsensusModel.Block.deepest? S := by
  have hinj : Set.InjOn (Block.toProof (V := V)) (↑(S.image Block.toSpec) : Set (Block V)) := by
    intro a ha b hb h
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at ha hb
    obtain ⟨a', _, rfl⟩ := ha
    obtain ⟨b', _, rfl⟩ := hb
    simp only [Block.toProof_toSpec] at h
    rw [h]
  have h := Block.toProof_deepest?_of_injOn _ hinj
  rw [Finset.image_image, Block.toProof_comp_toSpec, Finset.image_id] at h
  exact h.symm

end Block

/-! ## The routines on blocks, at the two readings -/

namespace Protocol

/-- On a store whose tree is parent-closed and on which `Block.toProof` is injective, the image of
    the spec's active prefix of the block standing for `root` in a subset `tree` of the store's tree
    is `DecoupledConsensusModel.Protocol.activePrefix` of `root` in the image of `tree`. -/
theorem activePrefix_blockOfImage (st : Store V)
    (hinj : Set.InjOn (Block.toProof (V := V)) (↑st.T : Set (Block V)))
    (hpar : ParentClosed st.T) {tree : Finset (Block V)} (htree : tree ⊆ st.T)
    (root : DecoupledConsensusModel.Block V) :
    (activePrefix tree (st.blockOfImage root)).map Block.toProof =
      DecoupledConsensusModel.Protocol.activePrefix (tree.image Block.toProof) root := by
  unfold activePrefix DecoupledConsensusModel.Protocol.activePrefix
  rw [Finset.filter_image]
  have hS : ({B ∈ tree | B.ancestorEq (st.blockOfImage root) = true} : Finset (Block V)) =
      tree.filter (fun B => DecoupledConsensusModel.Block.preceq B.toProof root = true) := by
    refine Finset.filter_congr (fun B hB => ?_)
    rw [Store.ancestorEq_blockOfImage_of_mem st hinj hpar (htree hB)]
  have hinj' : Set.InjOn (Block.toProof (V := V))
      (↑(tree.filter (fun B => DecoupledConsensusModel.Block.preceq B.toProof root = true)) :
        Set (Block V)) :=
    hinj.mono (fun B hB => Finset.mem_coe.mpr (htree (Finset.mem_filter.mp hB).1))
  rw [hS, Block.toProof_deepest?_of_injOn _ hinj']

omit [DecidableEq V] in
/-- The spec's `chain_up n (Block.toSpec B)` is `DecoupledConsensusModel.Protocol.chain_up n B`
    mapped by `Block.toSpec`. -/
theorem chain_up_toSpec (n : Nat) (B : DecoupledConsensusModel.Block V) :
    chain_up n (Block.toSpec B) =
      (DecoupledConsensusModel.Protocol.chain_up n B).map Block.toSpec := by
  induction n generalizing B with
  | zero => simp [DecoupledConsensusModel.Protocol.chain_up, chain_up]
  | succ n ih =>
    cases B with
    | genesis =>
      simp [DecoupledConsensusModel.Protocol.chain_up, chain_up, Block.toSpec,
        DecoupledConsensusModel.Block.parent?, Block.parent?, Id.run, pure]
    | node p s r votes support ats proposer =>
      simp [DecoupledConsensusModel.Protocol.chain_up, chain_up, Block.toSpec,
        DecoupledConsensusModel.Block.parent?, Block.parent?, Id.run, ih, Option.value, pure]

omit [DecidableEq V] in
/-- The spec's `chain_of (Block.toSpec B)` is `DecoupledConsensusModel.Protocol.chain_of B` mapped
    by `Block.toSpec`. -/
theorem chain_of_toSpec (B : DecoupledConsensusModel.Block V) :
    chain_of (Block.toSpec B) =
      (DecoupledConsensusModel.Protocol.chain_of B).map Block.toSpec := by
  rw [chain_of, Block.toSpec_depth, chain_up_toSpec, DecoupledConsensusModel.Protocol.chain_of]

omit [DecidableEq V] in
/-- `DecoupledConsensusModel.Protocol.chain_up n` of the image of `B` is the images, in order, of
    the spec's `chain_up n B`. -/
theorem chain_up_toProof (n : Nat) (B : Block V) :
    DecoupledConsensusModel.Protocol.chain_up n B.toProof = (chain_up n B).map Block.toProof := by
  induction n generalizing B with
  | zero => rfl
  | succ n ih =>
    cases B with
    | genesis => rfl
    | node p s r votes support ats proposer =>
      simp [DecoupledConsensusModel.Protocol.chain_up, chain_up, Block.toProof,
        DecoupledConsensusModel.Block.parent?, Block.parent?, Id.run, ih, Option.value, pure]

omit [DecidableEq V] in
/-- In a parent-closed set `T` holding `C`, every block of `chain_up n C` is in `T`. -/
theorem mem_of_mem_chain_up {T : Finset (Block V)} (hpar : ParentClosed T) (n : Nat)
    {C : Block V} (hC : C ∈ T) {B : Block V} (hB : B ∈ chain_up n C) : B ∈ T := by
  induction n generalizing C with
  | zero =>
      simp only [chain_up, List.mem_singleton] at hB
      rw [hB]; exact hC
  | succ n ih =>
    cases C with
    | genesis =>
      simp [chain_up, Block.parent?, Id.run, pure] at hB
      rw [hB]; exact hC
    | node p s r votes support ats proposer =>
      simp [chain_up, Block.parent?, Id.run, pure] at hB
      rcases hB with hB | hB
      · rw [hB]; exact hC
      · exact ih (hpar _ hC) hB

private theorem toFinset_map_eq_image {α β : Type} [DecidableEq α] [DecidableEq β] (f : α → β)
    (l : List α) : (l.map f).toFinset = l.toFinset.image f := by
  ext b
  simp

/-- The spec's `deepest_clear` at `floor` mapped by `Block.toSpec` (the genesis block when there is
    none), at `Block.toSpec C`, with the test read at the image, mapped back, is
    `DecoupledConsensusModel.Protocol.deepest_clear floor C test`. -/
theorem deepest_clear_toSpec (floor : Option (DecoupledConsensusModel.Block V))
    (C : DecoupledConsensusModel.Block V) (test : DecoupledConsensusModel.Block V → Bool) :
    (deepest_clear ((floor.map Block.toSpec).getD .genesis) (Block.toSpec C)
        (fun B => test B.toProof)).map Block.toProof =
      DecoupledConsensusModel.Protocol.deepest_clear floor C test := by
  unfold deepest_clear DecoupledConsensusModel.Protocol.deepest_clear
  rw [chain_of_toSpec, toFinset_map_eq_image, Finset.filter_image]
  have hS : ((DecoupledConsensusModel.Protocol.chain_of C).toFinset.filter
        (fun B => (((floor.map Block.toSpec).getD .genesis).ancestorEq (Block.toSpec B) &&
          test (Block.toSpec B).toProof) = true)) =
      (DecoupledConsensusModel.Protocol.chain_of C).toFinset.filter (fun B =>
        floor.elim true (fun anchor => DecoupledConsensusModel.Block.preceq anchor B) = true ∧
          test B = true) := by
    refine Finset.filter_congr (fun B _ => ?_)
    cases floor with
    | none => simp [Block.genesis_ancestorEq, Block.toProof_toSpec]
    | some A => simp [Block.toSpec_ancestorEq, Block.toProof_toSpec]
  rw [hS]
  exact Block.deepest?_image_toSpec _

/-- On a store whose tree is parent-closed and on which `Block.toProof` is injective, every block of
    `chain_up n (st.blockOfImage Y)` stands for its own image. -/
theorem chain_up_blockOfImage (st : Store V)
    (hinj : Set.InjOn (Block.toProof (V := V)) (↑st.T : Set (Block V)))
    (hpar : ParentClosed st.T) (n : Nat) (Y : DecoupledConsensusModel.Block V) :
    ∀ B ∈ chain_up n (st.blockOfImage Y), st.blockOfImage B.toProof = B := by
  induction n generalizing Y with
  | zero =>
      intro B hB
      simp only [chain_up, List.mem_singleton] at hB
      rw [hB, Store.toProof_blockOfImage]
  | succ n ih =>
      intro B hB
      have hY : st.blockOfImage (st.blockOfImage Y).toProof = st.blockOfImage Y := by
        rw [Store.toProof_blockOfImage]
      have hp := Store.blockOfImage_parent st hinj hpar Y
      generalize hX : st.blockOfImage Y = X at hB hY hp
      cases X with
      | genesis =>
        simp [chain_up, Block.parent?, Id.run, pure] at hB
        rw [hB]; exact hY
      | node p s r votes support ats proposer =>
        simp [chain_up, Block.parent?, Id.run, pure] at hB
        rcases hB with hB | hB
        · rw [hB]; exact hY
        · have hp' : p = st.blockOfImage Y.parent := by rw [hp]; rfl
          rw [hp'] at hB
          exact ih Y.parent B hB

/-- On a store whose tree is parent-closed and on which `Block.toProof` is injective, the spec's
    `deepest_clear` between the blocks standing for `A` and `Y`, with the test read at the image,
    mapped, is `DecoupledConsensusModel.Protocol.deepest_clear (some A) Y test`. -/
theorem deepest_clear_blockOfImage_image (st : Store V)
    (hinj : Set.InjOn (Block.toProof (V := V)) (↑st.T : Set (Block V)))
    (hpar : ParentClosed st.T) (A Y : DecoupledConsensusModel.Block V)
    (test : DecoupledConsensusModel.Block V → Bool) :
    (deepest_clear (st.blockOfImage A) (st.blockOfImage Y) (fun B => test B.toProof)).map
        Block.toProof =
      DecoupledConsensusModel.Protocol.deepest_clear (some A) Y test := by
  conv_rhs => rw [← Store.toProof_blockOfImage st Y]
  unfold deepest_clear DecoupledConsensusModel.Protocol.deepest_clear
  have hchain : DecoupledConsensusModel.Protocol.chain_of (st.blockOfImage Y).toProof =
      (chain_of (st.blockOfImage Y)).map Block.toProof := by
    rw [DecoupledConsensusModel.Protocol.chain_of, Block.toProof_depth, chain_up_toProof]
    rfl
  have hfix : ∀ B ∈ (chain_of (st.blockOfImage Y)).toFinset, st.blockOfImage B.toProof = B :=
    fun B hB => chain_up_blockOfImage st hinj hpar _ Y B (List.mem_toFinset.mp hB)
  rw [hchain, toFinset_map_eq_image, Finset.filter_image]
  have hS : ((chain_of (st.blockOfImage Y)).toFinset.filter
        (fun B => ((st.blockOfImage A).ancestorEq B && test B.toProof) = true)) =
      (chain_of (st.blockOfImage Y)).toFinset.filter (fun B =>
        (some A).elim true (fun anchor => DecoupledConsensusModel.Block.preceq anchor B.toProof)
          = true ∧ test B.toProof = true) := by
    refine Finset.filter_congr (fun B hB => ?_)
    conv_lhs => rw [← hfix B hB]
    rw [Store.blockOfImage_ancestorEq st hinj hpar A B.toProof]
    simp
  have hinj' : Set.InjOn (Block.toProof (V := V))
      (↑((chain_of (st.blockOfImage Y)).toFinset.filter (fun B =>
        (some A).elim true (fun anchor => DecoupledConsensusModel.Block.preceq anchor B.toProof)
          = true ∧ test B.toProof = true)) : Set (Block V)) := by
    intro B₁ h₁ B₂ h₂ e
    rw [← hfix B₁ (Finset.mem_filter.mp h₁).1, ← hfix B₂ (Finset.mem_filter.mp h₂).1, e]
  rw [hS, Block.toProof_deepest?_of_injOn _ hinj']

end Protocol

/-! ## Saved grades read through the tree -/

namespace Store

/-- The grade result `result` with its block, if it holds one, replaced by the block standing for
    its image on `st`. -/
def resultOfImage (st : Store V) : GradeResult V → GradeResult V
  | .pending => .pending
  | .computed G => .computed (G.map fun g => st.blockOfImage g.toProof)

/-- The round's grades `grades` with each of their three results passed to `st.resultOfImage`. -/
def roundGradesOfImage (st : Store V) (grades : RoundGrades V) : RoundGrades V :=
  ⟨st.resultOfImage grades.g0, st.resultOfImage grades.g1, st.resultOfImage grades.g2⟩

/-- The saved grades `c` with the grades of both their rounds passed to `st.roundGradesOfImage`, the
    round kept. -/
def contractOfImage (st : Store V) (c : SavedGrades V) : SavedGrades V :=
  ⟨c.round, st.roundGradesOfImage c.current, st.roundGradesOfImage c.next⟩

/-- Reading the saved grades through the tree keeps their round. -/
@[simp] theorem contractOfImage_round (st : Store V) (c : SavedGrades V) :
    (st.contractOfImage c).round = c.round := rfl

/-- Round grades with every result pending are unchanged by the reading through the tree. -/
@[simp] theorem roundGradesOfImage_pending (st : Store V) :
    st.roundGradesOfImage (Protocol.pending_round_grades (V := V)) =
      Protocol.pending_round_grades := rfl

/-- Every block a result of the saved grades `c` holds is a block of `T`. -/
def ContractInTree (T : Finset (Block V)) (c : SavedGrades V) : Prop :=
  ∀ fr ∈ [c.current, c.next], ∀ g ∈ [fr.g0, fr.g1, fr.g2], ∀ G, g = .computed (some G) → G ∈ T

/-- When `Block.toProof` is injective on `st.T` and the block `result` holds, if any, is a tree
    block, `st.resultOfImage result = result`. -/
theorem resultOfImage_of_inTree (st : Store V)
    (hinj : Set.InjOn (Block.toProof (V := V)) (↑st.T : Set (Block V))) {result : GradeResult V}
    (h : ∀ G, result = .computed (some G) → G ∈ st.T) : st.resultOfImage result = result := by
  cases result with
  | pending => rfl
  | computed G =>
    cases G with
    | none => rfl
    | some G => simp [resultOfImage, st.blockOfImage_toProof_of_injOn hinj (h G rfl)]

/-- When `Block.toProof` is injective on `st.T` and `ContractInTree st.T c`,
    `st.contractOfImage c = c`. -/
theorem contractOfImage_of_inTree (st : Store V)
    (hinj : Set.InjOn (Block.toProof (V := V)) (↑st.T : Set (Block V))) {c : SavedGrades V}
    (h : ContractInTree st.T c) : st.contractOfImage c = c := by
  obtain ⟨r, ⟨a0, a1, a2⟩, ⟨b0, b1, b2⟩⟩ := c
  have k (fr : RoundGrades V) (hfr : fr ∈ [⟨a0, a1, a2⟩, ⟨b0, b1, b2⟩]) (g : GradeResult V)
      (hg : g ∈ [fr.g0, fr.g1, fr.g2]) : st.resultOfImage g = g :=
    st.resultOfImage_of_inTree hinj (h fr hfr g hg)
  simp only [contractOfImage, roundGradesOfImage,
    k ⟨a0, a1, a2⟩ (by simp) a0 (by simp), k ⟨a0, a1, a2⟩ (by simp) a1 (by simp),
    k ⟨a0, a1, a2⟩ (by simp) a2 (by simp), k ⟨b0, b1, b2⟩ (by simp) b0 (by simp),
    k ⟨b0, b1, b2⟩ (by simp) b1 (by simp), k ⟨b0, b1, b2⟩ (by simp) b2 (by simp)]

/-- `contractOfImage_of_inTree` on a tree whose blocks have distinct roots. -/
theorem contractOfImage_of_distinctRoots (st : Store V) (hT : DistinctRoots st.T)
    {c : SavedGrades V} (h : ContractInTree st.T c) : st.contractOfImage c = c :=
  st.contractOfImage_of_inTree (SpecDraftRecord.NoRaise.DistinctRoots.injOn_toProof hT) h

/-- The grades of round `ρ` of `st.contractOfImage c` are the grades of round `ρ` of `c`, read
    through the tree. -/
theorem saved_round_grades_contractOfImage (st : Store V) (c : SavedGrades V) (ρ : Round) :
    Protocol.saved_round_grades (st.contractOfImage c) ρ =
      st.roundGradesOfImage (Protocol.saved_round_grades c ρ) := by
  unfold Protocol.saved_round_grades
  by_cases h0 : ρ = c.round
  · simp [h0, contractOfImage]
  · by_cases h1 : ρ = c.round + 1
    · simp [h1, contractOfImage]
    · simp [h0, h1, contractOfImage]

end Store

/-! ## The store read through its tree -/

namespace Store

/-- The store `st` with its five named blocks `F`, `J`, `live_confirmed`, `latest_confirmed` and
    `latest_stable` each replaced by the block standing for its image on the tree of `st`; every
    other field as it is. -/
def ofImage (st : Store V) : Store V :=
  { st with
    F := st.blockOfImage st.F.toProof
    J := st.blockOfImage st.J.toProof
    live_confirmed := st.blockOfImage st.live_confirmed.toProof
    latest_confirmed := st.blockOfImage st.latest_confirmed.toProof
    latest_stable := st.blockOfImage st.latest_stable.toProof }

/-- `Store.ofImage` keeps the tree. -/
@[simp] theorem ofImage_T (st : Store V) : (Store.ofImage st).T = st.T := rfl

/-- `Store.ofImage` keeps the saved grades. -/
@[simp] theorem ofImage_saved_grades (st : Store V) :
    (Store.ofImage st).saved_grades = st.saved_grades := rfl

/-- `(Store.ofImage st).blockOfImage = st.blockOfImage`: `blockOfImage` reads the tree only. -/
@[simp] theorem blockOfImage_ofImage (st : Store V) :
    (Store.ofImage st).blockOfImage = st.blockOfImage := rfl

/-- `(Store.ofImage st).contractOfImage c = st.contractOfImage c`: `contractOfImage` reads the tree
    only. -/
@[simp] theorem contractOfImage_ofImage (st : Store V) (c : SavedGrades V) :
    (Store.ofImage st).contractOfImage c = st.contractOfImage c := rfl

/-- `Store.ofImage` keeps the clock, the slot, the stamps, the chain states, the votes, the
    attestations, `h_j` and `h_max`. -/
@[simp] theorem ofImage_fields (st : Store V) :
    (Store.ofImage st).t = st.t ∧ (Store.ofImage st).s = st.s ∧
      (Store.ofImage st).timestamp_block = st.timestamp_block ∧
      (Store.ofImage st).timestamp_vote = st.timestamp_vote ∧
      (Store.ofImage st).timestamp_sg_vote = st.timestamp_sg_vote ∧
      (Store.ofImage st).σ = st.σ ∧ (Store.ofImage st).gf_votes = st.gf_votes ∧
      (Store.ofImage st).attestations = st.attestations ∧ (Store.ofImage st).h_j = st.h_j ∧
      (Store.ofImage st).h_max = st.h_max :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `(Store.ofImage st).F = st.blockOfImage st.F.toProof`. -/
theorem ofImage_F (st : Store V) : (Store.ofImage st).F = st.blockOfImage st.F.toProof := rfl

/-- `(Store.ofImage st).J = st.blockOfImage st.J.toProof`. -/
theorem ofImage_J (st : Store V) : (Store.ofImage st).J = st.blockOfImage st.J.toProof := rfl

/-- `(Store.ofImage st).live_confirmed = st.blockOfImage st.live_confirmed.toProof`. -/
theorem ofImage_live_confirmed (st : Store V) :
    (Store.ofImage st).live_confirmed = st.blockOfImage st.live_confirmed.toProof := rfl

/-- `(Store.ofImage st).latest_confirmed = st.blockOfImage st.latest_confirmed.toProof`. -/
theorem ofImage_latest_confirmed (st : Store V) :
    (Store.ofImage st).latest_confirmed = st.blockOfImage st.latest_confirmed.toProof := rfl

/-- `(Store.ofImage st).latest_stable = st.blockOfImage st.latest_stable.toProof`. -/
theorem ofImage_latest_stable (st : Store V) :
    (Store.ofImage st).latest_stable = st.blockOfImage st.latest_stable.toProof := rfl

/-- If the blocks of `st.T` have distinct roots and `st.F`, `st.J`, `st.live_confirmed`,
    `st.latest_confirmed` and `st.latest_stable` are blocks of `st.T`, then `Store.ofImage st = st`. -/
theorem ofImage_eq_self (st : Store V) (hT : DistinctRoots st.T) (hF : st.F ∈ st.T)
    (hJ : st.J ∈ st.T) (hl : st.live_confirmed ∈ st.T) (hc : st.latest_confirmed ∈ st.T)
    (hs : st.latest_stable ∈ st.T) : Store.ofImage st = st := by
  have hinj := SpecDraftRecord.NoRaise.DistinctRoots.injOn_toProof hT
  simp [Store.ofImage, st.blockOfImage_toProof_of_injOn hinj hF,
    st.blockOfImage_toProof_of_injOn hinj hJ, st.blockOfImage_toProof_of_injOn hinj hl,
    st.blockOfImage_toProof_of_injOn hinj hc, st.blockOfImage_toProof_of_injOn hinj hs]

/-- If `StoreOk st`, then `(Store.ofImage st).F = st.F`. -/
theorem ofImage_F_of_storeOk {st : Store V} (h : SpecDraftRecord.NoRaise.StoreOk st) :
    (Store.ofImage st).F = st.F :=
  st.blockOfImage_toProof_of_injOn
    (SpecDraftRecord.NoRaise.DistinctRoots.injOn_toProof h.2.1) h.2.2.2

/-- If `StoreOk st`, then `StoreOk (Store.ofImage st)`. -/
theorem storeOk_ofImage {st : Store V} (h : SpecDraftRecord.NoRaise.StoreOk st) :
    SpecDraftRecord.NoRaise.StoreOk (Store.ofImage st) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, h3, ?_⟩
  show st.blockOfImage st.F.toProof ∈ st.T
  rw [st.blockOfImage_toProof_of_injOn (SpecDraftRecord.NoRaise.DistinctRoots.injOn_toProof h2) h4]
  exact h4

/-- The fgroot of `Store.ofImage st` is the block standing for the image of the fgroot of `st`. -/
theorem get_fg_root_ofImage (st : Store V) :
    Protocol.get_fg_root (Store.ofImage st) =
      st.blockOfImage (Protocol.get_fg_root st).toProof := by
  unfold Protocol.get_fg_root
  simp only [Id.run, Store.ofImage]
  split_ifs <;> rfl

/-- The image of the fgroot of `Store.ofImage st` is the image of the fgroot of `st`. -/
theorem toProof_get_fg_root_ofImage (st : Store V) :
    (Protocol.get_fg_root (Store.ofImage st)).toProof = (Protocol.get_fg_root st).toProof := by
  rw [get_fg_root_ofImage, toProof_blockOfImage]

end Store

end Spec
