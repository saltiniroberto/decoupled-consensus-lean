module
public import GoldilocksCorrectness.Proofs.Routines.FGCaches
import all Goldilocks.FG.ChainState
import all Goldilocks.FG.State
import all Goldilocks.FG.ValidatorClient

@[expose] public section

/-!
# What the FG handlers do to the FG state

The theorems about the FG handlers of the spec, `fg_on_block`, `fg_on_attestation`,
`fg_on_attestations`, `update_finality` and `fg_attest`, one handler at a time: what each keeps
(`…_keeps`, `…_eq`, `…_pool`, `…_holds`), what each writes to the caches `h_max`, `h_j`, `J` and
`F` (`…_J_cases`, `…_F_cases`, `…_F`, `update_finality_h_max`, `…_h_j`, `…_F_descends`,
`…_F_reaches`), and the state-level conditions of
`GoldilocksCorrectness/Statements/Routines/FGStateDefs.lean` each preserves
(`…_finalizedAncestorJustified`, `…_heightCacheBounds`, `…_justification`, `…_justified`,
`…_caches`); and `head_height_floor_initial`, `head_height_floor` of the initial FG state.

They read the handlers alone: no node state, no execution.

Moved here unchanged from the execution pages.
-/

set_option autoImplicit false

open scoped DC
open DC (DRE)

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks

-- An index `x[i]` into an execution has the valid-index predicate `fun _ _ => True`; this rule,
-- local to the file, proves it at once.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

omit [Fintype V] in
/-- The finality update keeps the finalized block or writes `σ.F`.

The variables:
- `S`: the FG state; `σ`: the chain state it is updated from. -/
theorem update_finality_F_cases (S : FGState V) (σ : ChainState V) :
    (update_finality S σ).F = S.F ∨ (update_finality S σ).F = σ.F := by
  simp only [update_finality, Id.run]
  split
  · split
    · exact Or.inr rfl
    · exact Or.inl rfl
  · split
    · exact Or.inr rfl
    · exact Or.inl rfl

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

omit [Fintype V] in
/-- The finality update keeps the justified block or writes `σ.J`.

The variables:
- `S`: the FG state; `σ`: the chain state it is updated from. -/
theorem update_finality_J_cases (S : FGState V) (σ : ChainState V) :
    (update_finality S σ).J = S.J ∨ (update_finality S σ).J = σ.J := by
  simp only [update_finality, Id.run]
  split
  · split
    · exact Or.inr rfl
    · exact Or.inr rfl
  · split
    · exact Or.inl rfl
    · exact Or.inl rfl

omit [Fintype V] [RootOrder] in
/-- Receiving an attestation keeps the justified block.

The variables:
- `S`: the FG state; `a`: the attestation. -/
theorem fg_on_attestation_J (S : FGState V) (a : Attestation V) :
    (fg_on_attestation S a).J = S.J := by
  simp only [fg_on_attestation, Id.run]
  split <;> rfl

/-- Accepting a block keeps the justified block or writes the justified block of the chain state
computed for the block from its parent's.

The variables:
- `C`: the parameters; `S`: the FG state; `B`: the block. -/
theorem fg_on_block_J_cases (C : Config) (S : FGState V) (B : Block V) :
    (fg_on_block C S B).J = S.J ∨
      (fg_on_block C S B).J = (state_transition C (S.σ B.parent) B).J := by
  set S₁ : FGState V := { S with
    σ := Function.update S.σ B (state_transition C (S.σ B.parent) B)
    T := S.T ∪ {B} } with hS₁
  have hdef : fg_on_block C S B = forIn (m := Id) B.attestations
      (update_finality S₁ (S₁.σ B))
      (fun a X => Pure.pure (ForInStep.yield (fg_on_attestation X a))) := rfl
  have hfold := forIn_yield_inv B.attestations (update_finality S₁ (S₁.σ B))
    (fun X a => fg_on_attestation X a) (fun X => X.J = (update_finality S₁ (S₁.σ B)).J) rfl
    (fun X a _ hX => (fg_on_attestation_J X a).trans hX)
  rw [hdef, hfold]
  have hσ : S₁.σ B = state_transition C (S.σ B.parent) B := Function.update_self _ _ _
  rw [← hσ]
  exact update_finality_J_cases S₁ (S₁.σ B)

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- Receiving an attestation keeps the tree, the chain states and the finalized block: it writes
the pool of attestations only.

The variables:
- `S`: the FG state; `a`: the attestation. -/
theorem fg_on_attestation_keeps (S : FGState V) (a : Attestation V) :
    (fg_on_attestation S a).T = S.T ∧ (fg_on_attestation S a).σ = S.σ ∧
      (fg_on_attestation S a).F = S.F := by
  simp only [fg_on_attestation, Id.run]
  split <;> exact ⟨rfl, rfl, rfl⟩

omit [Fintype V] in
/-- Receiving the attestations of a list in order keeps the tree, the chain states and the
finalized block.

The variables:
- `l`: the attestations; `S`: the FG state. -/
theorem fg_on_attestations_keeps (l : List (Attestation V)) (S : FGState V) :
    (forIn (m := Id) l S (fun a X => Pure.pure (ForInStep.yield (fg_on_attestation X a)))).T =
        S.T ∧
      (forIn (m := Id) l S (fun a X => Pure.pure (ForInStep.yield (fg_on_attestation X a)))).σ =
        S.σ ∧
      (forIn (m := Id) l S (fun a X => Pure.pure (ForInStep.yield (fg_on_attestation X a)))).F =
        S.F :=
  forIn_yield_inv l S (fun X a => fg_on_attestation X a)
    (fun X => X.T = S.T ∧ X.σ = S.σ ∧ X.F = S.F) ⟨rfl, rfl, rfl⟩
    (fun X a _ hX => by
      obtain ⟨h1, h2, h3⟩ := fg_on_attestation_keeps X a
      exact ⟨h1.trans hX.1, h2.trans hX.2.1, h3.trans hX.2.2⟩)

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- Accepting a block keeps the finalized block or writes the finalized block of the chain state
computed for the block from its parent's.

The variables:
- `C`: the parameters; `S`: the FG state; `B`: the block. -/
theorem fg_on_block_F_cases (C : Config) (S : FGState V) (B : Block V) :
    (fg_on_block C S B).F = S.F ∨
      (fg_on_block C S B).F = (state_transition C (S.σ B.parent) B).F := by
  set S₁ : FGState V := { S with
    σ := Function.update S.σ B (state_transition C (S.σ B.parent) B)
    T := S.T ∪ {B} } with hS₁
  have hdef : fg_on_block C S B = forIn (m := Id) B.attestations
      (update_finality S₁ (S₁.σ B))
      (fun a X => Pure.pure (ForInStep.yield (fg_on_attestation X a))) := rfl
  rw [hdef, (fg_on_attestations_keeps B.attestations (update_finality S₁ (S₁.σ B))).2.2]
  have hσ : S₁.σ B = state_transition C (S.σ B.parent) B := Function.update_self _ _ _
  rw [← hσ]
  exact update_finality_F_cases S₁ (S₁.σ B)

end

section

open GoldilocksCorrectness.Statements.Routines (FinalizedAncestorJustified HeightCacheBounds)

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]

section

variable [RootOrder]

omit [Fintype V] in
/-- The finality update keeps the tree and the chain states, and moves the finalized block, if at
all, to an ancestor of a block of the tree, or a block of the tree.

The variables:
- `S`: the FG state; `σ`: the chain state it is updated from. -/
theorem update_finality_keeps (S : FGState V) (σ : ChainState V) :
    (update_finality S σ).T = S.T ∧ (update_finality S σ).σ = S.σ ∧
      ((update_finality S σ).F = S.F ∨
        ∃ B' ∈ S.T, (update_finality S σ).F.AncestorEq B') := by
  have key : ∀ S' : FGState V, has_viable_descendant S' σ.F = true → S'.T = S.T →
      ∃ B' ∈ S.T, σ.F.AncestorEq B' := by
    intro S' hv hT
    simp only [has_viable_descendant, decide_eq_true_eq] at hv
    obtain ⟨B', hB', hanc, -⟩ := hv
    exact ⟨B', hT ▸ hB', hanc⟩
  simp only [update_finality, Id.run]
  split
  · split
    · rename_i h
      simp only [Bool.and_eq_true] at h
      exact ⟨rfl, rfl, Or.inr (key _ h.2 rfl)⟩
    · exact ⟨rfl, rfl, Or.inl rfl⟩
  · split
    · rename_i h
      simp only [Bool.and_eq_true] at h
      exact ⟨rfl, rfl, Or.inr (key _ h.2 rfl)⟩
    · exact ⟨rfl, rfl, Or.inl rfl⟩

/-- Accepting the block `B` adds `B` to the tree, writes the chain state of `B` from its
parent's, and moves the finalized block, if at all, to an ancestor of a block of the new tree, or
a block of it.

The variables:
- `C`: the parameters; `S`: the FG state; `B`: the block. -/
theorem fg_on_block_eq (C : Config) (S : FGState V) (B : Block V) :
    (fg_on_block C S B).T = S.T ∪ {B} ∧
      (fg_on_block C S B).σ = Function.update S.σ B (state_transition C (S.σ B.parent) B) ∧
      ((fg_on_block C S B).F = S.F ∨ ∃ B' ∈ S.T ∪ {B}, (fg_on_block C S B).F.AncestorEq B') := by
  set S₁ : FGState V := { S with
    σ := Function.update S.σ B (state_transition C (S.σ B.parent) B)
    T := S.T ∪ {B} } with hS₁
  have hdef : fg_on_block C S B = forIn (m := Id) B.attestations
      (update_finality S₁ (S₁.σ B))
      (fun a X => Pure.pure (ForInStep.yield (fg_on_attestation X a))) := rfl
  rw [hdef]
  obtain ⟨h1, h2, h3⟩ := fg_on_attestations_keeps B.attestations (update_finality S₁ (S₁.σ B))
  obtain ⟨u1, u2, u3⟩ := update_finality_keeps S₁ (S₁.σ B)
  refine ⟨h1.trans u1, h2.trans u2, ?_⟩
  rw [h3]
  exact u3

omit [Fintype V] in
/-- The finality update keeps the pool of attestations.

The variables:
- `S`: the FG state; `σ`: the chain state it is updated from. -/
theorem update_finality_attestations (S : FGState V) (σ : ChainState V) :
    (update_finality S σ).attestations = S.attestations := by
  simp only [update_finality, Id.run]
  split <;> split <;> rfl

omit [Fintype V] [RootOrder] in
/-- Receiving an attestation keeps the justified block and the cache `h_max`.

The variables:
- `S`: the FG state; `a`: the attestation. -/
theorem fg_on_attestation_caches (S : FGState V) (a : Attestation V) :
    (fg_on_attestation S a).J = S.J ∧ (fg_on_attestation S a).h_max = S.h_max := by
  simp only [fg_on_attestation, Id.run]
  split <;> exact ⟨rfl, rfl⟩

omit [Fintype V] [RootOrder] in
/-- Receiving the attestations of a list in order keeps the justified block and the cache
`h_max`.

The variables:
- `l`: the attestations; `S`: the FG state. -/
theorem fg_on_attestations_caches (l : List (Attestation V)) (S : FGState V) :
    (forIn (m := Id) l S (fun a X => Pure.pure (ForInStep.yield (fg_on_attestation X a)))).J =
        S.J ∧
      (forIn (m := Id) l S
        (fun a X => Pure.pure (ForInStep.yield (fg_on_attestation X a)))).h_max = S.h_max :=
  forIn_yield_inv l S (fun X a => fg_on_attestation X a)
    (fun X => X.J = S.J ∧ X.h_max = S.h_max) ⟨rfl, rfl⟩
    (fun X a _ hX => by
      obtain ⟨h1, h2⟩ := fg_on_attestation_caches X a
      exact ⟨h1.trans hX.1, h2.trans hX.2⟩)

omit [Fintype V] in
/-- The finality update sets the cache `h_max` to the greater of itself and `σ.h`: its step 1,
which no later step writes.

The variables:
- `S`: the FG state; `σ`: the chain state it is updated from. -/
theorem update_finality_h_max (S : FGState V) (σ : ChainState V) :
    (update_finality S σ).h_max = max S.h_max σ.h := by
  simp only [update_finality, Id.run]
  split <;> split <;> rfl

omit [Fintype V] in
/-- The finality update keeps the finalized block the justified block or an ancestor of it. Its
step 2 writes `σ.J` as the justified block only when the finalized block is `σ.J` or an ancestor
of it; its step 3 writes `σ.F` as the finalized block only when `σ.F` is the justified block step
2 left or an ancestor of it.

The variables:
- `S`: the FG state; `σ`: the chain state it is updated from. -/
theorem update_finality_finalizedAncestorJustified (S : FGState V) (σ : ChainState V)
    -- the finalized block of `S` is the justified block of `S` or an ancestor of it
    (hS : FinalizedAncestorJustified S) :
    FinalizedAncestorJustified (update_finality S σ) := by
  unfold FinalizedAncestorJustified
  simp only [update_finality, Id.run]
  split
  · rename_i h1
    split
    · rename_i h2
      simp only [Bool.and_eq_true] at h2
      exact h2.1.2
    · simp only [Bool.and_eq_true] at h1
      exact h1.1
  · split
    · rename_i h2
      simp only [Bool.and_eq_true] at h2
      exact h2.1.2
    · exact hS

/-- Accepting a block keeps the finalized block the justified block or an ancestor of it.

The variables:
- `C`: the parameters; `S`: the FG state; `B`: the block. -/
theorem fg_on_block_finalizedAncestorJustified (C : Config) (S : FGState V) (B : Block V)
    -- the finalized block of `S` is the justified block of `S` or an ancestor of it
    (hS : FinalizedAncestorJustified S) :
    FinalizedAncestorJustified (fg_on_block C S B) := by
  set S₁ : FGState V := { S with
    σ := Function.update S.σ B (state_transition C (S.σ B.parent) B)
    T := S.T ∪ {B} } with hS₁
  have hdef : fg_on_block C S B = forIn (m := Id) B.attestations
      (update_finality S₁ (S₁.σ B))
      (fun a X => Pure.pure (ForInStep.yield (fg_on_attestation X a))) := rfl
  rw [hdef]
  obtain ⟨-, -, h3⟩ := fg_on_attestations_keeps B.attestations (update_finality S₁ (S₁.σ B))
  obtain ⟨h4, -⟩ := fg_on_attestations_caches B.attestations (update_finality S₁ (S₁.σ B))
  unfold FinalizedAncestorJustified
  rw [h3, h4]
  exact update_finality_finalizedAncestorJustified S₁ (S₁.σ B) hS

/-- Accepting a block keeps the cache `h_max` at least the chain-state height of every block of
the tree: the new block's chain state is written, then the finality update raises `h_max` to at
least its height; every other block keeps its chain state, and `h_max` does not decrease.

The variables:
- `C`: the parameters; `S`: the FG state; `B`: the block. -/
theorem fg_on_block_heightCacheBounds (C : Config) (S : FGState V) (B : Block V)
    -- no block of the tree of `S` has a chain-state height greater than `S.h_max`
    (hS : HeightCacheBounds S) :
    HeightCacheBounds (fg_on_block C S B) := by
  set S₁ : FGState V := { S with
    σ := Function.update S.σ B (state_transition C (S.σ B.parent) B)
    T := S.T ∪ {B} } with hS₁
  have hdef : fg_on_block C S B = forIn (m := Id) B.attestations
      (update_finality S₁ (S₁.σ B))
      (fun a X => Pure.pure (ForInStep.yield (fg_on_attestation X a))) := rfl
  rw [hdef]
  obtain ⟨h1, h2, -⟩ := fg_on_attestations_keeps B.attestations (update_finality S₁ (S₁.σ B))
  obtain ⟨-, h4⟩ := fg_on_attestations_caches B.attestations (update_finality S₁ (S₁.σ B))
  obtain ⟨u1, u2, -⟩ := update_finality_keeps S₁ (S₁.σ B)
  unfold HeightCacheBounds
  rw [h1, h2, h4, u1, u2, update_finality_h_max]
  intro B' hB'
  by_cases he : B' = B
  · rw [he]
    exact le_max_right _ _
  · have hB'' : B' ∈ S.T := by
      rcases Finset.mem_union.mp hB' with h | h
      · exact h
      · exact absurd (Finset.mem_singleton.mp h) he
    show (Function.update S.σ B (state_transition C (S.σ B.parent) B) B').h ≤
      max S.h_max (S₁.σ B).h
    rw [Function.update_of_ne he]
    exact le_trans (hS B' hB'') (le_max_left _ _)

omit [Fintype V] [RootOrder] in
/-- Receiving an attestation keeps the justification height.

The variables:
- `S`: the FG state; `a`: the attestation. -/
theorem fg_on_attestation_h_j (S : FGState V) (a : Attestation V) :
    (fg_on_attestation S a).h_j = S.h_j := by
  simp only [fg_on_attestation, Id.run]
  split <;> rfl

omit [Fintype V] [RootOrder] in
/-- Receiving the attestations of a list in order keeps the justification height.

The variables:
- `l`: the attestations; `S`: the FG state. -/
theorem fg_on_attestations_h_j (l : List (Attestation V)) (S : FGState V) :
    (forIn (m := Id) l S
      (fun a X => Pure.pure (ForInStep.yield (fg_on_attestation X a)))).h_j = S.h_j :=
  forIn_yield_inv l S (fun X a => fg_on_attestation X a) (fun X => X.h_j = S.h_j) rfl
    (fun X a _ hX => (fg_on_attestation_h_j X a).trans hX)

omit [Fintype V] in
/-- The finality update moves the finalized block, if at all, to a descendant of it.

The variables:
- `S`: the FG state; `σ`: the chain state it is updated from. -/
theorem update_finality_F_descends (S : FGState V) (σ : ChainState V) :
    S.F.AncestorEq (update_finality S σ).F := by
  simp only [update_finality, Id.run]
  split
  · split
    · rename_i h
      simp only [Bool.and_eq_true, Block.ancestorStrict] at h
      exact h.1.1.2
    · exact ancestorEq_refl _
  · split
    · rename_i h
      simp only [Bool.and_eq_true, Block.ancestorStrict] at h
      exact h.1.1.2
    · exact ancestorEq_refl _

omit [Fintype V] in
/-- The finality update keeps the justified block and the justification height, or writes `σ.J`
and `σ.h_j`; the new justification height is at least the old one, and at least `σ.h_j` when the
finalized block is `σ.J` or an ancestor of it.

The variables:
- `S`: the FG state; `σ`: the chain state it is updated from. -/
theorem update_finality_justification (S : FGState V) (σ : ChainState V) :
    S.h_j ≤ (update_finality S σ).h_j ∧
      (S.F.AncestorEq σ.J → σ.h_j ≤ (update_finality S σ).h_j) ∧
      (((update_finality S σ).J = S.J ∧ (update_finality S σ).h_j = S.h_j) ∨
        ((update_finality S σ).J = σ.J ∧ (update_finality S σ).h_j = σ.h_j)) := by
  simp only [update_finality, Id.run]
  split
  · rename_i h1
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h1
    have hle : S.h_j ≤ σ.h_j := by
      rcases h1.2 with h | ⟨h, -⟩
      · exact Nat.le_of_lt h
      · exact Nat.le_of_eq h
    split <;> exact ⟨hle, fun _ => le_rfl, Or.inr ⟨rfl, rfl⟩⟩
  · rename_i h1
    have hle : S.F.AncestorEq σ.J → σ.h_j ≤ S.h_j := by
      intro hF
      by_contra hlt
      apply h1
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
      exact ⟨hF, Or.inl (Nat.lt_of_not_le hlt)⟩
    split <;> exact ⟨le_rfl, hle, Or.inl ⟨rfl, rfl⟩⟩

/-- Accepting the block `B` moves the finalized block, if at all, to a descendant of it; keeps the
justified block and the justification height, or writes those of the chain state of `B`; and the
new justification height is at least the old one, and at least `B`'s when the finalized block is
`B`'s justified block or an ancestor of it.

The variables:
- `C`: the parameters; `S`: the FG state; `B`: the block. -/
theorem fg_on_block_justification (C : Config) (S : FGState V) (B : Block V) :
    S.F.AncestorEq (fg_on_block C S B).F ∧ S.h_j ≤ (fg_on_block C S B).h_j ∧
      (S.F.AncestorEq (state_transition C (S.σ B.parent) B).J →
        (state_transition C (S.σ B.parent) B).h_j ≤ (fg_on_block C S B).h_j) ∧
      (((fg_on_block C S B).J = S.J ∧ (fg_on_block C S B).h_j = S.h_j) ∨
        ((fg_on_block C S B).J = (state_transition C (S.σ B.parent) B).J ∧
          (fg_on_block C S B).h_j = (state_transition C (S.σ B.parent) B).h_j)) := by
  set S₁ : FGState V := { S with
    σ := Function.update S.σ B (state_transition C (S.σ B.parent) B)
    T := S.T ∪ {B} } with hS₁
  have hdef : fg_on_block C S B = forIn (m := Id) B.attestations
      (update_finality S₁ (S₁.σ B))
      (fun a X => Pure.pure (ForInStep.yield (fg_on_attestation X a))) := rfl
  have hσB : S₁.σ B = state_transition C (S.σ B.parent) B := Function.update_self _ _ _
  rw [hdef, (fg_on_attestations_keeps B.attestations (update_finality S₁ (S₁.σ B))).2.2,
    (fg_on_attestations_caches B.attestations (update_finality S₁ (S₁.σ B))).1,
    fg_on_attestations_h_j]
  rw [← hσB]
  exact ⟨update_finality_F_descends S₁ (S₁.σ B), update_finality_justification S₁ (S₁.σ B)⟩

end

end

end

section

open GoldilocksCorrectness.Statements.Routines (ChainStatesComputed FinalizedAncestorJustified
  JustificationCacheBounds JustifiedHeight JustifiedInTree)
open GoldilocksCorrectness.Statements.Routines (chainStateOf)

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]

section

variable [RootOrder]

/-- Accepting a new block `B`, whose parent is in the tree and of which the finalized block is an
ancestor, keeps `JustificationCacheBounds`, `JustifiedHeight` and `JustifiedInTree`, when the
chain states of the tree before and after are the blocks' own and the tree after is closed under
parents.

Why: the finality update keeps the justified block and its height, or writes `B`'s; `B`'s
justified block is on `B`'s chain, at its justification height when that is at least `1`, and the
genesis block otherwise (`chainStateOf_J_spec`). When the update keeps the cache although `B`'s
justification is greater, `B`'s justified block is not on the finalized block's chain, so it is an
ancestor of the finalized block, whose height is at most the justified block's.

The variables:
- `C`: the parameters; `S`: the FG state; `B`: the block. -/
theorem fg_on_block_justified (C : Config) (S : FGState V) (B : Block V)
    -- every non-genesis block of the new tree has its parent in the new tree
    (hcl' : ∀ B' ∈ (fg_on_block C S B).T, B' ≠ Block.genesis →
      B'.parent ∈ (fg_on_block C S B).T)
    (hCS : ChainStatesComputed C S) (hCS' : ChainStatesComputed C (fg_on_block C S B))
    -- `B` is new, its parent is in the tree, and the finalized block is `B` or an ancestor of it
    (hBT : B ∉ S.T) (hFB : S.F.AncestorEq B)
    (hFJ : FinalizedAncestorJustified S) (hJCB : JustificationCacheBounds S)
    (hJH : JustifiedHeight S) (hJIT : JustifiedInTree S) :
    JustificationCacheBounds (fg_on_block C S B) ∧ JustifiedHeight (fg_on_block C S B) ∧
      JustifiedInTree (fg_on_block C S B) := by
  obtain ⟨hT', hσ', -⟩ := fg_on_block_eq C S B
  obtain ⟨hF', hle, hσJ, hcases⟩ := fg_on_block_justification C S B
  have hBT' : B ∈ (fg_on_block C S B).T := by
    rw [hT']
    exact Finset.mem_union_right _ (Finset.mem_singleton_self B)
  -- the chain state written for `B` is `B`'s own
  have hσB : state_transition C (S.σ B.parent) B = chainStateOf C B := by
    have h := hCS' B hBT'
    rw [hσ', Function.update_self] at h
    exact h
  obtain ⟨hJB, hJ0, hJ1⟩ := chainStateOf_J_spec C B
  rw [hσB] at hσJ hcases
  have hold : ∀ B' ∈ S.T, (fg_on_block C S B).σ B' = S.σ B' := fun B' h => by
    rw [hσ', Function.update_of_ne (by rintro rfl; exact hBT h)]
  have hJmem : (chainStateOf C B).J ∈ (fg_on_block C S B).T := ancestors_mem hcl' hBT' hJB
  -- `B`'s justification height is at most the new cache
  have hBle : (chainStateOf C B).h_j ≤ (fg_on_block C S B).h_j := by
    by_cases hFJ' : S.F.AncestorEq (chainStateOf C B).J
    · exact hσJ hFJ'
    refine le_trans ?_ hle
    by_cases h0 : (chainStateOf C B).h_j = 0
    · rw [h0]
      exact Nat.zero_le _
    have h1 : 1 ≤ (chainStateOf C B).h_j := Nat.one_le_iff_ne_zero.mpr h0
    rcases ancestorEq_compatible hJB hFB with hJF | hFJ''
    · rcases hJH with hg | hh
      · exfalso
        apply hFJ'
        have hFg : S.F = Block.genesis := by
          have h' : S.F.AncestorEq S.J := hFJ
          rw [hg] at h'
          exact (ancestorEq_genesis_iff _).1 h'
        rw [hFg]
        exact genesis_ancestorEq _
      · rw [← hJ1 h1, ← hh, hCS _ hJIT]
        exact le_trans (chainStateOf_height_mono C hJF) (chainStateOf_height_mono C hFJ)
    · exact absurd hFJ'' hFJ'
  refine ⟨fun B' hB' hFB' => ?_, ?_, ?_⟩
  · have hFB'' : S.F.AncestorEq B' := ancestorEq_trans hF' hFB'
    by_cases he : B' = B
    · subst he
      rw [hσ', Function.update_self, hσB]
      exact hBle
    · have hB'S : B' ∈ S.T := by
        rw [hT'] at hB'
        rcases Finset.mem_union.mp hB' with h | h
        · exact h
        · exact absurd (Finset.mem_singleton.mp h) he
      rw [hold B' hB'S]
      exact le_trans (hJCB B' hB'S hFB'') hle
  · rcases hcases with ⟨hJ, hh⟩ | ⟨hJ, hh⟩
    · rcases hJH with hg | hh'
      · left
        rw [hJ]
        exact hg
      · right
        show ((fg_on_block C S B).σ (fg_on_block C S B).J).h = (fg_on_block C S B).h_j
        rw [hJ, hh, hold _ hJIT]
        exact hh'
    · by_cases h0 : (chainStateOf C B).h_j = 0
      · left
        rw [hJ]
        exact hJ0 h0
      · right
        show ((fg_on_block C S B).σ (fg_on_block C S B).J).h = (fg_on_block C S B).h_j
        rw [hJ, hh, hCS' _ hJmem]
        exact hJ1 (Nat.one_le_iff_ne_zero.mpr h0)
  · rcases hcases with ⟨hJ, -⟩ | ⟨hJ, -⟩
    · show (fg_on_block C S B).J ∈ (fg_on_block C S B).T
      rw [hJ, hT']
      exact Finset.mem_union_left _ hJIT
    · show (fg_on_block C S B).J ∈ (fg_on_block C S B).T
      rw [hJ]
      exact hJmem

omit [DecidableEq V] [Fintype V] [RootOrder] in
/-- `fg_attest` is `create_attestation` from the source's height and the root of the block that
took its chain into that height, and the head's justification height, justified root and
finalization height. -/
theorem fg_attest_eq (S : FGState V) (Λ : SigningHistory) (v : V) (source head : Block V) :
    fg_attest S Λ v source head = create_attestation Λ v (S.σ source).h (S.σ source).T_h.root
      (S.σ head).h_j (S.σ head).J.root (S.σ head).h_F := by rfl

end

end

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- Receiving the attestation `a` into the FG state `S` keeps its pool and holds `a`.

The variables:
- `S`: the FG state; `a`: the attestation. -/
theorem fg_on_attestation_pool (S : FGState V) (a : Attestation V) :
    (∀ a' ∈ S.attestations, a' ∈ (fg_on_attestation S a).attestations) ∧
      a ∈ (fg_on_attestation S a).attestations := by
  simp only [fg_on_attestation, Id.run]
  split
  · exact ⟨fun a' h => List.mem_append_left _ h,
      List.mem_append_right _ (List.mem_singleton_self a)⟩
  · rename_i h
    exact ⟨fun a' h' => h', Decidable.not_not.mp h⟩

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

omit [Fintype V] [RootOrder] in
/-- Receiving the attestations of a list in order puts each of them in the pool.

The variables:
- `l`: the attestations; `S`: the FG state. -/
theorem fg_on_attestations_holds (l : List (Attestation V)) (S : FGState V) :
    ∀ a ∈ l, a ∈ (forIn (m := Id) l S
      (fun a X => Pure.pure (ForInStep.yield (fg_on_attestation X a)))).attestations := by
  induction l generalizing S with
  | nil => intro a ha; cases ha
  | cons b l ih =>
      intro a ha
      rw [List.forIn_cons]
      rcases List.mem_cons.1 ha with rfl | ha
      · exact forIn_yield_inv l _ (fun X a => fg_on_attestation X a)
          (fun X => a ∈ X.attestations) (fg_on_attestation_pool S a).2
          (fun X a' _ hX => (fg_on_attestation_pool X a').1 a hX)
      · exact ih _ a ha

/-- Accepting a block puts each attestation it includes in the pool.

The variables:
- `C`: the parameters; `S`: the FG state; `B`: the block. -/
theorem fg_on_block_holds (C : Config) (S : FGState V) (B : Block V) :
    ∀ a ∈ B.attestations, a ∈ (fg_on_block C S B).attestations := by
  set S₁ : FGState V := { S with
    σ := Function.update S.σ B (state_transition C (S.σ B.parent) B)
    T := S.T ∪ {B} } with hS₁
  have hdef : fg_on_block C S B = forIn (m := Id) B.attestations
      (update_finality S₁ (S₁.σ B))
      (fun a X => Pure.pure (ForInStep.yield (fg_on_attestation X a))) := rfl
  rw [hdef]
  exact fg_on_attestations_holds B.attestations _

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]
variable [RootOrder]

/-- Accepting a block keeps the pool: the finality update keeps it, and the block's attestations
are received into it.

The variables:
- `C`: the parameters; `S`: the FG state; `B`: the block. -/
theorem fg_on_block_pool (C : Config) (S : FGState V) (B : Block V) :
    ∀ a ∈ S.attestations, a ∈ (fg_on_block C S B).attestations := by
  set S₁ : FGState V := { S with
    σ := Function.update S.σ B (state_transition C (S.σ B.parent) B)
    T := S.T ∪ {B} } with hS₁
  have hdef : fg_on_block C S B = forIn (m := Id) B.attestations
      (update_finality S₁ (S₁.σ B))
      (fun a X => Pure.pure (ForInStep.yield (fg_on_attestation X a))) := rfl
  intro a ha
  rw [hdef]
  refine forIn_yield_inv B.attestations _ (fun X a => fg_on_attestation X a)
    (fun X => a ∈ X.attestations) ?_ (fun X a' _ hX => (fg_on_attestation_pool X a').1 a hX)
  rw [update_finality_attestations]
  exact ha

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]

section

variable [RootOrder]

omit [Fintype V] in
/-- The finality update moves the finalized block, if at all, to a descendant: the old finalized
block is an ancestor of the new one, or the new one. It moves only to `σ.F`, and only when the old
finalized block is a strict ancestor of `σ.F`.

The variables:
- `S`: the FG state; `σ`: the chain state it is updated from. -/
theorem update_finality_F (S : FGState V) (σ : ChainState V) :
    S.F.AncestorEq (update_finality S σ).F := by
  simp only [update_finality, Id.run]
  split
  · split
    · rename_i h
      simp only [Bool.and_eq_true, Block.ancestorStrict] at h
      exact h.1.1.2
    · exact ancestorEq_refl _
  · split
    · rename_i h
      simp only [Bool.and_eq_true, Block.ancestorStrict] at h
      exact h.1.1.2
    · exact ancestorEq_refl _

/-- Accepting a block moves the finalized block, if at all, to a descendant.

The variables:
- `C`: the parameters; `S`: the FG state; `B`: the block. -/
theorem fg_on_block_F (C : Config) (S : FGState V) (B : Block V) :
    S.F.AncestorEq (fg_on_block C S B).F := by
  set S₁ : FGState V := { S with
    σ := Function.update S.σ B (state_transition C (S.σ B.parent) B)
    T := S.T ∪ {B} } with hS₁
  have hdef : fg_on_block C S B = forIn (m := Id) B.attestations
      (update_finality S₁ (S₁.σ B))
      (fun a X => Pure.pure (ForInStep.yield (fg_on_attestation X a))) := rfl
  rw [hdef, (fg_on_attestations_keeps B.attestations (update_finality S₁ (S₁.σ B))).2.2]
  exact update_finality_F S₁ (S₁.σ B)

end

end

section

open GoldilocksCorrectness.Statements.Routines (chainStateOf)

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

omit [Fintype V] in
/-- **Kit fact, the finality update reaches `σ.F`.** When `S.F` and `σ.F` are on one chain,
`σ.F` is an ancestor of `σ.J` or `σ.J`, `σ.F` is an ancestor of `S.J` or the update's
justification step fires, and some block of the tree that is `σ.F` or a descendant of it has a
height at least the updated `h_max`: the updated finalized block is `σ.F` or a descendant of it.

Why: when `σ.F` is an ancestor of `S.F` the finalized block only moves to descendants; otherwise
`S.F` is a strict ancestor of `σ.F`, and the three tests of step 3 pass. -/
theorem update_finality_F_reaches (S : FGState V) (σ : ChainState V)
    (hcomp : S.F.AncestorEq σ.F ∨ σ.F.AncestorEq S.F)
    (hσFJ : σ.F.AncestorEq σ.J)
    (hJ : σ.F.AncestorEq S.J ∨ S.h_j < σ.h_j)
    (hV : ∃ X ∈ S.T, σ.F.AncestorEq X ∧ max S.h_max σ.h ≤ (S.σ X).h) :
    σ.F.AncestorEq (update_finality S σ).F := by
  rcases hcomp with hle | hge
  swap
  · exact ancestorEq_trans hge (update_finality_F S σ)
  by_cases heq : S.F = σ.F
  · rw [← heq]; exact update_finality_F S σ
  obtain ⟨X, hX, hFX, hXh⟩ := hV
  have hstrict : S.F.ancestorStrict σ.F = true := by
    simp only [Block.ancestorStrict, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
    exact ⟨heq, hle⟩
  simp only [update_finality, Id.run]
  split
  · split
    · exact ancestorEq_refl _
    · rename_i h3
      exfalso
      apply h3
      simp only [Bool.and_eq_true]
      exact ⟨⟨hstrict, hσFJ⟩, has_viable_descendant_of _ σ.F X hX hFX hXh⟩
  · rename_i h2
    split
    · exact ancestorEq_refl _
    · rename_i h3
      exfalso
      apply h3
      have hFJ : σ.F.AncestorEq S.J := by
        rcases hJ with hJ | hJ
        · exact hJ
        · exfalso
          apply h2
          simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
          exact ⟨ancestorEq_trans hle hσFJ, Or.inl hJ⟩
      simp only [Bool.and_eq_true]
      exact ⟨⟨hstrict, hFJ⟩, has_viable_descendant_of _ σ.F X hX hFX hXh⟩

/-- **Kit fact, accepting `D` reaches `D`'s finalized block.** Accepting a block `D` not in the
tree, whose parent is in it and of which `S.F` is an ancestor, from an FG state `ReadyFor` `D`,
leaves a finalized block that is `D`'s or a descendant of it. -/
theorem fg_on_block_F_reaches (C : Config) (S : FGState V) (D : Block V)
    (hR : ReadyFor C D S) (hDT : D ∉ S.T) (hpar : D.parent ∈ S.T)
    (hFD : S.F.AncestorEq D) (hDg : D ≠ Block.genesis) :
    (chainStateOf C D).F.AncestorEq (fg_on_block C S D).F := by
  obtain ⟨hCS, hJ, hV⟩ := hR
  set S₁ : FGState V := { S with
    σ := Function.update S.σ D (state_transition C (S.σ D.parent) D)
    T := S.T ∪ {D} } with hS₁
  have hdef : fg_on_block C S D = forIn (m := Id) D.attestations
      (update_finality S₁ (S₁.σ D))
      (fun a X => Pure.pure (ForInStep.yield (fg_on_attestation X a))) := rfl
  have hst : state_transition C (S.σ D.parent) D = chainStateOf C D := by
    rw [hCS D.parent hpar]
    cases D with
    | genesis => exact absurd rfl hDg
    | node p s r votes support ats v => rfl
  have hσ₁ : S₁.σ D = chainStateOf C D := by
    rw [hS₁]
    show Function.update S.σ D (state_transition C (S.σ D.parent) D) D = _
    rw [Function.update_self, hst]
  rw [hdef, (fg_on_attestations_keeps D.attestations (update_finality S₁ (S₁.σ D))).2.2, hσ₁]
  have hFDD := chainStateOf_F_ancestorEq C D
  refine update_finality_F_reaches S₁ (chainStateOf C D) ?_
    (chainStateOf_F_ancestorEq_J C D) hJ ?_
  · rcases ancestorEq_compatible hFD hFDD with h | h
    · exact Or.inl h
    · exact Or.inr h
  · rcases hV with hle | ⟨X, hX, hFX, hXh⟩
    · refine ⟨D, Finset.mem_union_right _ (Finset.mem_singleton_self D), hFDD, ?_⟩
      rw [hσ₁]
      exact max_le hle le_rfl
    · refine ⟨X, Finset.mem_union_left _ hX, hFX, ?_⟩
      have hXD : X ≠ D := fun h => hDT (h ▸ hX)
      show max S.h_max (chainStateOf C D).h ≤
        (Function.update S.σ D (state_transition C (S.σ D.parent) D) X).h
      rw [Function.update_of_ne hXD, hCS X hX]
      exact hXh

end

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

omit [Fintype V] [RootOrder] in
/-- The initial FG state is not contested, and its `head_height_floor` (the least chain-state height a viable block may have) is `0`. -/
theorem head_height_floor_initial : head_height_floor (FGState.initial : FGState V) = 0 := by
  have hc : fg_contest (FGState.initial : FGState V) = false := by
    simp only [fg_contest, Id.run]
    split
    · rfl
    · refine decide_eq_false ?_
      rintro ⟨B, hB, -, -, hJ⟩
      have hB' : B = Block.genesis := Finset.mem_singleton.1 hB
      subst hB'
      exact hJ (genesis_ancestorEq _)
  simp only [head_height_floor, Id.run, hc]
  rfl

end

section

open Goldilocks

variable {V : Type}

/-- **The initial FG state, written out.** `FGState.initial` has the genesis block alone as its
tree, every chain state `ChainState.initial`, the genesis block as its finalized and its justified
block, the cached heights `h_j = 0` and `h_max = 1`, and no attestation. Added by the record
migration, step 1f, for the execution proofs that read a field of the initial node state.

Read aloud: the FG state starts with the genesis block alone, finalized and justified, and no
attestation. -/
theorem fgState_initial_eq :
    (FGState.initial : FGState V) =
      { T := {Block.genesis}, σ := fun _ => ChainState.initial, F := Block.genesis,
        J := Block.genesis, h_j := 0, h_max := 1, attestations := [] } := by rfl

end

end GoldilocksCorrectness.Proofs.Routines
