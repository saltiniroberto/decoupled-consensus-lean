module
public import Goldilocks.AC.Confirmation

@[expose] public section

/-!
# Ancestry over Goldilocks's blocks

The ancestry test `Block.ancestorEq` walks from a block to its parent until the genesis block.
This file proves that it is a tree order, with the depth facts the walk lemmas use:

- `ancestorEq_genesis_iff`, `ancestorEq_node_iff`: the two cases of `Block.ancestorEq`;
- `ancestorEq_refl`, `ancestorEq_trans`, `ancestorEq_compatible`, `ancestorEq_antisymm`: a block
  is an ancestor of itself, ancestry is transitive, two ancestors of one block are compatible, and
  two blocks each an ancestor of the other are equal; `genesis_ancestorEq`;
- depth: `depth_le_of_ancestorEq`, `eq_of_ancestorEq_of_depth`, `eq_of_ancestorEq_common`,
  `ancestorEq_of_parent?`, `depth_of_parent?`;
- children on the way to a block: `child_towards_unique`, `exists_child_towards`, `path_card`;
- compatibility: `compatible_iff`, `conflicts_iff`, `compatible_of_ancestorEq_compatible`,
  `conflicts_of_ancestorEq_conflicts`.
-/

set_option autoImplicit false

open scoped DC

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks

variable {V : Type} [DecidableEq V]

/-! ## The two cases, and the tree order -/

/-- A block is an ancestor of the genesis block, or the genesis block itself, exactly when it is
the genesis block.

The variables:
- `B`: the block tested. -/
theorem ancestorEq_genesis_iff (B : Block V) : B.AncestorEq Block.genesis ↔ B = Block.genesis := by
  simp [Block.AncestorEq, Block.ancestorEq]

/-- `B` is an ancestor of the block `C` with parent `p`, or `C` itself, exactly when `B` is `C`
or an ancestor of `p`, or `p` itself.

The variables:
- `B`: the block tested;
- `p`, `s`, `r`, `votes`, `support`, `ats`, `v`: the parent, slot, root, Goldfish votes, support
  votes, attestations and proposer of the block `C` it is tested against. -/
theorem ancestorEq_node_iff (B p : Block V) (s : Slot) (r : BlockId)
    (votes support : List (GoldfishVote V)) (ats : List (Attestation V)) (v : V) :
    B.AncestorEq (.node p s r votes support ats v) ↔
      B = .node p s r votes support ats v ∨ B.AncestorEq p := by
  simp [Block.AncestorEq, Block.ancestorEq]

/-- Every block is an ancestor of itself, or itself.

The variables:
- `B`: the block. -/
theorem ancestorEq_refl (B : Block V) : B.AncestorEq B := by
  cases B with
  | genesis => exact (ancestorEq_genesis_iff _).2 rfl
  | node p s r votes support ats v => exact (ancestorEq_node_iff _ _ _ _ _ _ _ _).2 (Or.inl rfl)

/-- An ancestor of an ancestor of a block is an ancestor of that block.

The variables:
- `B`, `B'`, `B''`: the three blocks, `B` an ancestor of `B'` and `B'` of `B''`. -/
theorem ancestorEq_trans {B B' B'' : Block V} (h : B.AncestorEq B') (h' : B'.AncestorEq B'') :
    B.AncestorEq B'' := by
  induction B'' with
  | genesis =>
      rw [ancestorEq_genesis_iff] at h' ⊢
      subst h'
      exact (ancestorEq_genesis_iff _).1 h
  | node p s r votes support ats v ih =>
      rw [ancestorEq_node_iff] at h' ⊢
      rcases h' with h' | h'
      · subst h'
        rw [← ancestorEq_node_iff]
        exact h
      · exact Or.inr (ih h')

/-- Two ancestors of one block are compatible: one of them is an ancestor of the other, or they
are equal.

The variables:
- `B`, `B'`: the two ancestors; `B''`: the block they are ancestors of. -/
theorem ancestorEq_compatible {B B' B'' : Block V} (h : B.AncestorEq B'')
    (h' : B'.AncestorEq B'') : B.AncestorEq B' ∨ B'.AncestorEq B := by
  induction B'' with
  | genesis =>
      rw [ancestorEq_genesis_iff] at h h'
      subst h h'
      exact Or.inl (ancestorEq_refl _)
  | node p s r votes support ats v ih =>
      rw [ancestorEq_node_iff] at h h'
      rcases h with h | h
      · subst h
        exact Or.inr ((ancestorEq_node_iff _ _ _ _ _ _ _ _).2 h')
      · rcases h' with h' | h'
        · subst h'
          exact Or.inl ((ancestorEq_node_iff _ _ _ _ _ _ _ _).2 (Or.inr h))
        · exact ih h h'

/-- The genesis block is an ancestor of every block, or the block itself.

The variables:
- `B`: the block. -/
theorem genesis_ancestorEq (B : Block V) : (Block.genesis : Block V).AncestorEq B := by
  induction B with
  | genesis => exact ancestorEq_refl _
  | node p s r votes support ats v ih =>
      exact (ancestorEq_node_iff _ _ _ _ _ _ _ _).2 (Or.inr ih)

/-! ## Depth -/

/-- An ancestor of a block has a depth at most the block's.

The variables:
- `B`, `C`: the two blocks, `B` an ancestor of `C` or `C` itself. -/
theorem depth_le_of_ancestorEq {B C : Block V} (h : B.AncestorEq C) : B.depth ≤ C.depth := by
  induction C with
  | genesis => rw [(ancestorEq_genesis_iff B).1 h]
  | node p s r votes support ats v ih =>
    rcases (ancestorEq_node_iff _ _ _ _ _ _ _ _).1 h with h | h
    · rw [h]
    · have := ih h
      simp only [Block.depth]
      omega

/-- An ancestor of a block whose depth is at least the block's is the block itself.

The variables:
- `B`, `C`: the two blocks, `B` an ancestor of `C` or `C` itself. -/
theorem eq_of_ancestorEq_of_depth {B C : Block V} (h : B.AncestorEq C)
    (hd : C.depth ≤ B.depth) : B = C := by
  cases C with
  | genesis => exact (ancestorEq_genesis_iff B).1 h
  | node p s r votes support ats v =>
    rcases (ancestorEq_node_iff _ _ _ _ _ _ _ _).1 h with h | h
    · exact h
    · have := depth_le_of_ancestorEq h
      simp only [Block.depth] at hd
      omega

/-- Two blocks each an ancestor of the other, or equal to it, are equal.

The variables:
- `X`, `Y`: the two blocks. -/
theorem ancestorEq_antisymm {X Y : Block V} (hXY : X.AncestorEq Y) (hYX : Y.AncestorEq X) :
    X = Y :=
  eq_of_ancestorEq_of_depth hXY (depth_le_of_ancestorEq hYX)

/-- Two ancestors of one block with the same depth are equal.

The variables:
- `B`, `B'`: the two ancestors; `C`: the block they are ancestors of. -/
theorem eq_of_ancestorEq_common {B B' C : Block V} (h : B.AncestorEq C) (h' : B'.AncestorEq C)
    (hd : B.depth = B'.depth) : B = B' := by
  rcases ancestorEq_compatible h h' with h'' | h''
  · exact eq_of_ancestorEq_of_depth h'' (by omega)
  · exact (eq_of_ancestorEq_of_depth h'' (by omega)).symm

/-- A block's parent is an ancestor of it.

The variables:
- `B`: the block; `H`: its parent. -/
theorem ancestorEq_of_parent? {B H : Block V} (h : B.parent? = some H) : H.AncestorEq B := by
  cases B with
  | genesis => simp [Block.parent?] at h
  | node p s r votes support ats v =>
    simp only [Block.parent?, Option.some.injEq] at h
    subst h
    exact (ancestorEq_node_iff _ _ _ _ _ _ _ _).2 (Or.inr (ancestorEq_refl _))

omit [DecidableEq V] in
/-- A child of a block is one deeper than the block.

The variables:
- `C`: the child; `H`: its parent. -/
theorem depth_of_parent? {C H : Block V} (h : C.parent? = some H) : C.depth = H.depth + 1 := by
  cases C with
  | genesis => simp [Block.parent?] at h
  | node p s r votes support ats v =>
    simp only [Block.parent?, Option.some.injEq] at h
    subst h
    rfl

/-! ## Children on the way to a block -/

/-- Two blocks with the same parent, each an ancestor of a block or that block, are equal.

The variables:
- `H`: the common parent; `C`, `D`: the two children; `B`: the block both are ancestors of. -/
theorem child_towards_unique {H C D B : Block V} (hC : C.parent? = some H)
    (hD : D.parent? = some H) (hCB : C.AncestorEq B) (hDB : D.AncestorEq B) : D = C :=
  eq_of_ancestorEq_common hDB hCB (by rw [depth_of_parent? hC, depth_of_parent? hD])

/-- A strict ancestor of a block has a child that is an ancestor of the block, or the block.

The variables:
- `H`: the ancestor; `B`: the block. -/
theorem exists_child_towards {H B : Block V} (hHB : H.AncestorEq B) (hne : H ≠ B) :
    ∃ C : Block V, C.parent? = some H ∧ C.AncestorEq B := by
  induction B with
  | genesis => exact absurd ((ancestorEq_genesis_iff H).1 hHB) hne
  | node p s r votes support ats v ih =>
    rcases (ancestorEq_node_iff _ _ _ _ _ _ _ _).1 hHB with h | h
    · exact absurd h hne
    · by_cases hp : H = p
      · subst hp
        exact ⟨_, rfl, ancestorEq_refl _⟩
      · obtain ⟨C, hC, hCp⟩ := ih h hp
        exact ⟨C, hC, ancestorEq_trans hCp
          (ancestorEq_of_parent? (B := .node p s r votes support ats v) rfl)⟩

/-- When every block after `A` on the way to `B` is in `tree`, `B` is at most `tree.card` deeper
than `A`: those blocks are distinct, one at each depth.

The variables:
- `A`: the block the path starts from; `B`: the block it ends at;
- `tree`: the set holding the blocks after `A` on the path. -/
theorem path_card {A B : Block V} {tree : Finset (Block V)} (hAB : A.AncestorEq B)
    -- every block after `A` on the way to `B`, `B` included, is in `tree`
    (hpath : ∀ P : Block V, A.AncestorEq P → P ≠ A → P.AncestorEq B → P ∈ tree) :
    B.depth ≤ A.depth + tree.card := by
  induction B generalizing tree with
  | genesis =>
    rw [(ancestorEq_genesis_iff A).1 hAB]
    omega
  | node p s r votes support ats v ih =>
    by_cases hA : A = .node p s r votes support ats v
    · rw [hA]
      omega
    · have hAp : A.AncestorEq p :=
        ((ancestorEq_node_iff _ _ _ _ _ _ _ _).1 hAB).resolve_left hA
      have hpB : p.AncestorEq (.node p s r votes support ats v) :=
        ancestorEq_of_parent? (B := .node p s r votes support ats v) rfl
      have hBmem : Block.node p s r votes support ats v ∈ tree :=
        hpath _ hAB (Ne.symm hA) (ancestorEq_refl _)
      have hrec := ih hAp (tree := tree.erase (.node p s r votes support ats v))
        (fun P hAP hPA hPp => by
          refine Finset.mem_erase.2 ⟨fun hPB => ?_, hpath P hAP hPA (ancestorEq_trans hPp hpB)⟩
          have := depth_le_of_ancestorEq hPp
          rw [hPB] at this
          simp only [Block.depth] at this
          omega)
      have hcard := Finset.card_erase_of_mem hBmem
      have hpos := Finset.card_pos.2 ⟨_, hBmem⟩
      simp only [Block.depth]
      omega

/-! ## Compatibility -/

/-- Two blocks are compatible exactly when one is an ancestor of the other, or they are equal.

The variables:
- `X`, `Y`: the two blocks. -/
theorem compatible_iff (X Y : Block V) :
    X.compatible Y = true ↔ X.AncestorEq Y ∨ Y.AncestorEq X := by
  simp only [Block.compatible, Block.AncestorEq, Bool.or_eq_true]

/-- Two blocks conflict exactly when they are not compatible.

The variables:
- `X`, `Y`: the two blocks. -/
theorem conflicts_iff (X Y : Block V) : X.conflicts Y = true ↔ ¬ X.compatible Y = true := by
  simp [Block.conflicts]

/-- An ancestor of a block compatible with `R` is compatible with `R`.

The variables:
- `X`: the ancestor; `Y`: the block compatible with `R`; `R`: the block. -/
theorem compatible_of_ancestorEq_compatible {X Y R : Block V} (hXY : X.AncestorEq Y)
    (hYR : Y.compatible R = true) : X.compatible R = true := by
  rw [compatible_iff] at hYR ⊢
  rcases hYR with hYR | hRY
  · exact Or.inl (ancestorEq_trans hXY hYR)
  · exact ancestorEq_compatible hXY hRY

/-- A block that conflicts with `R` conflicts with every descendant of `R`.

The variables:
- `R`: the block; `H`: the descendant of `R`, or `R`; `D`: the block that conflicts with `R`. -/
theorem conflicts_of_ancestorEq_conflicts {R H D : Block V} (hRH : R.AncestorEq H)
    (hD : D.conflicts R = true) : D.conflicts H = true := by
  rw [conflicts_iff] at hD ⊢
  intro hDH
  apply hD
  have hHD : H.compatible D = true := by
    rw [compatible_iff] at hDH ⊢
    exact hDH.symm
  have hRD := compatible_of_ancestorEq_compatible hRH hHD
  rw [compatible_iff] at hRD ⊢
  exact hRD.symm

end GoldilocksCorrectness.Proofs.Routines

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks

-- An index `x[i]` into an execution has the valid-index predicate `fun _ _ => True`; this rule,
-- local to the file, proves it at once.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- A tree closed under parents holds every ancestor of each of its blocks.

The variables:
- `T`: the tree; `B`: a block of it; `P'`: an ancestor of `B`, or `B`. -/
theorem ancestors_mem {T : Finset (Block V)}
    (hT : ∀ B ∈ T, B ≠ Block.genesis → B.parent ∈ T) {B P' : Block V} (hB : B ∈ T)
    (h : P'.AncestorEq B) : P' ∈ T := by
  induction B with
  | genesis =>
      rw [(ancestorEq_genesis_iff P').1 h]
      exact hB
  | node p s r votes support ats v ih =>
      rcases (ancestorEq_node_iff P' p s r votes support ats v).1 h with he | hp
      · rw [he]; exact hB
      · exact ih (hT _ hB (by intro he; cases he)) hp

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

omit [Fintype V] [RootOrder] in
/-- Two blocks that are ancestors-or-equal of two compatible blocks are compatible.

The variables:
- `X`, `Y`: the two blocks; `Cx`, `Cy`: the compatible blocks they are ancestors of, or equal to.

Read aloud: going back along two compatible chains keeps them compatible. -/
theorem compatible_of_ancestorEq_both {X Y Cx Cy : Block V} (hX : X.AncestorEq Cx)
    (hY : Y.AncestorEq Cy) (hC : Cx.compatible Cy = true) : X.compatible Y = true := by
  have h1 : X.compatible Cy = true := compatible_of_ancestorEq_compatible hX hC
  have h2 : Cy.compatible X = true := (compatible_iff _ _).2 ((compatible_iff _ _).1 h1).symm
  have h3 : Y.compatible X = true := compatible_of_ancestorEq_compatible hY h2
  exact (compatible_iff _ _).2 ((compatible_iff _ _).1 h3).symm

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

omit [Fintype V] [RootOrder] in
/-- Compatibility is symmetric.

The variables:
- `X`, `Y`: the two blocks. -/
theorem compatible_symm' {X Y : Block V} (h : X.compatible Y = true) : Y.compatible X = true :=
  (compatible_iff _ _).2 ((compatible_iff _ _).1 h).symm

omit [Fintype V] [RootOrder] in
/-- A block compatible with `X` is compatible with every ancestor of `X`, or `X`.

The variables:
- `E`: the block; `X`: the block it is compatible with; `Y`: an ancestor of `X`, or `X`.

Read aloud: going back along the chain of `X` keeps compatibility with `E`. -/
theorem compatible_of_compatible_ancestorEq {E X Y : Block V} (hE : E.compatible X = true)
    (hY : Y.AncestorEq X) : E.compatible Y = true :=
  compatible_symm' (compatible_of_ancestorEq_compatible hY (compatible_symm' hE))

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

omit [Fintype V] [RootOrder] in
/-- A block's parent is an ancestor of it, or it (the genesis block is its own parent).

The variables:
- `B`: the block. -/
theorem parent_ancestorEq_self (B : Block V) : B.parent.AncestorEq B := by
  cases B with
  | genesis => exact ancestorEq_refl _
  | node p s r votes support ats v => exact ancestorEq_of_parent? rfl

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

omit [Fintype V] [RootOrder] in
/-- A block's parent is an ancestor of it, or it (the genesis block is its own parent).

The variables:
- `B`: the block. -/
theorem parent_ancestorEq (B : Block V) : B.parent.AncestorEq B := by
  cases B with
  | genesis => exact ancestorEq_refl _
  | node p s r votes support ats v => exact ancestorEq_of_parent? rfl

end

end GoldilocksCorrectness.Proofs.Routines
