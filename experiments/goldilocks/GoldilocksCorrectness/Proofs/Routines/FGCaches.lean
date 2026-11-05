module
public import GoldilocksCorrectness.Proofs.Routines.DREPost
public import GoldilocksCorrectness.Proofs.Routines.FGStateReaders
import all Goldilocks.FG.ChainState
import all Goldilocks.FG.State

@[expose] public section

/-!
# The caches of the FG state after each handler, against the chain states

`CachesOnChainWith`, `CachesWitnessed` and `ReadyFor`, conditions relating the caches `h_max`,
`h_j`, `J` and `F` of an FG state to the chain states of the blocks of its tree, and what the FG
handlers do to them: `update_finality_cachesOnChainWith`, `fg_on_block_cachesOnChainWith`,
`fg_on_attestation_witness_keeps`, `has_viable_descendant_witness`, `update_finality_witness`,
`fg_on_block_witnessed`, `exists_viable_head_of_witnessed`.

They read the handlers and an FG state alone: no node state, no execution.

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

open GoldilocksCorrectness.Statements.Routines (IsEntry chainStateOf)

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- `CachesOnChainWith C H OnChain S`: the justification height `S.h_j` is greater than `H`; the
justified block `S.J` satisfies `OnChain`, is an entry block and has the chain-state height
`S.h_j`; the finalized block `S.F` is `S.J` or an ancestor of it.

The variables:
- `C`: the parameters; `H`: the threshold; `OnChain`: the set of blocks; `S`: the FG state. -/
def CachesOnChainWith (C : Config) (H : ℕ) (OnChain : Block V → Prop) (S : FGState V) : Prop :=
  H < S.h_j ∧ OnChain S.J ∧ IsEntry C S.J ∧ (chainStateOf C S.J).h = S.h_j ∧
    S.F.AncestorEq S.J

/-- **Kit fact, the finality update on a chain state.** When the caches of `S` satisfy
`CachesOnChainWith`, and the justified block of `σ` satisfies `OnChain`, is an entry block and
has its height at `σ.h_j` whenever `σ.h_j` is greater than `H`, the caches of the updated FG state
satisfy `CachesOnChainWith`.

Why: step 2 moves the justified block only to `σ.J`, at a justification height at least `S.h_j`,
so greater than `H`, and only when `S.F` is `σ.J` or an ancestor of it; step 3 moves the finalized
block only to `σ.F`, the justified block or an ancestor of it.

The variables:
- `C`: the parameters; `H`: the threshold; `OnChain`: the set of blocks; `S`: the FG state; `σ`:
  the chain state. -/
theorem update_finality_cachesOnChainWith (C : Config) (H : ℕ) (OnChain : Block V → Prop)
    (S : FGState V) (σ : ChainState V)
    -- the caches of `S` are on the set
    (hS : CachesOnChainWith C H OnChain S)
    -- the justified block of `σ` is on the set, an entry block at its height, when `σ.h_j > H`
    (hσ : H < σ.h_j →
      OnChain σ.J ∧ IsEntry C σ.J ∧ (chainStateOf C σ.J).h = σ.h_j) :
    CachesOnChainWith C H OnChain (update_finality S σ) := by
  obtain ⟨hH, hon, hent, hht, hFJ⟩ := hS
  simp only [update_finality, Id.run]
  split
  · rename_i h2
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h2
    have hlt : H < σ.h_j := by
      rcases h2.2 with h | ⟨h, -⟩
      · exact Nat.lt_trans hH h
      · exact h ▸ hH
    obtain ⟨h1, h3, h4⟩ := hσ hlt
    split
    · rename_i h5
      simp only [Bool.and_eq_true] at h5
      exact ⟨hlt, h1, h3, h4, h5.1.2⟩
    · exact ⟨hlt, h1, h3, h4, h2.1⟩
  · split
    · rename_i h5
      simp only [Bool.and_eq_true] at h5
      exact ⟨hH, hon, hent, hht, h5.1.2⟩
    · exact ⟨hH, hon, hent, hht, hFJ⟩

/-- **Kit fact, accepting a block.** When the caches of `S` satisfy `CachesOnChainWith`, and the
chain state computed for `B` from its parent's satisfies the hypothesis of
`update_finality_cachesOnChainWith`, the caches after accepting `B` satisfy `CachesOnChainWith`:
the attestations of `B` received after the update keep the caches.

The variables:
- `C`: the parameters; `H`: the threshold; `OnChain`: the set of blocks; `S`: the FG state; `B`:
  the block. -/
theorem fg_on_block_cachesOnChainWith (C : Config) (H : ℕ) (OnChain : Block V → Prop)
    (S : FGState V) (B : Block V)
    -- the caches of `S` are on the set
    (hS : CachesOnChainWith C H OnChain S)
    -- the justified block of the chain state computed for `B` is on the set when its
    -- justification height is greater than `H`
    (hσ : H < (state_transition C (S.σ B.parent) B).h_j →
      OnChain (state_transition C (S.σ B.parent) B).J ∧
        IsEntry C (state_transition C (S.σ B.parent) B).J ∧
        (chainStateOf C (state_transition C (S.σ B.parent) B).J).h =
          (state_transition C (S.σ B.parent) B).h_j) :
    CachesOnChainWith C H OnChain (fg_on_block C S B) := by
  set S₁ : FGState V := { S with
    σ := Function.update S.σ B (state_transition C (S.σ B.parent) B)
    T := S.T ∪ {B} } with hS₁
  have hdef : fg_on_block C S B = forIn (m := Id) B.attestations
      (update_finality S₁ (S₁.σ B))
      (fun a X => Pure.pure (ForInStep.yield (fg_on_attestation X a))) := rfl
  have hkeep : ∀ (X : FGState V) (a : Attestation V), (fg_on_attestation X a).J = X.J ∧
      (fg_on_attestation X a).h_j = X.h_j ∧ (fg_on_attestation X a).F = X.F := by
    intro X a
    simp only [fg_on_attestation, Id.run]
    split <;> exact ⟨rfl, rfl, rfl⟩
  have hfold := forIn_yield_inv B.attestations (update_finality S₁ (S₁.σ B))
    (fun X a => fg_on_attestation X a)
    (fun X => X.J = (update_finality S₁ (S₁.σ B)).J ∧
      X.h_j = (update_finality S₁ (S₁.σ B)).h_j ∧ X.F = (update_finality S₁ (S₁.σ B)).F)
    ⟨rfl, rfl, rfl⟩
    (fun X a _ hX => ⟨(hkeep X a).1.trans hX.1, (hkeep X a).2.1.trans hX.2.1,
      (hkeep X a).2.2.trans hX.2.2⟩)
  have hσ₁ : S₁.σ B = state_transition C (S.σ B.parent) B := Function.update_self _ _ _
  have hU := update_finality_cachesOnChainWith C H OnChain S₁ (S₁.σ B) hS (by rw [hσ₁]; exact hσ)
  rw [hdef]
  unfold CachesOnChainWith at hU ⊢
  rw [hfold.1, hfold.2.1, hfold.2.2]
  exact hU

end

end

section

open GoldilocksCorrectness.Statements.Routines (ChainStatesComputed)
open GoldilocksCorrectness.Statements.Routines (chainStateOf)

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- `ReadyFor C D S`: the chain states of `S`'s tree are the blocks' own; `D`'s finalized block is
an ancestor of `S.J` or `S.J`, or `S`'s justification height is less than `D`'s; and `S.h_max` is
at most `D`'s height, or some block of the tree that is `D`'s finalized block or a descendant of it
has a height at least the greater of `S.h_max` and `D`'s height.

The variables:
- `C`: the parameters; `D`: the block; `S`: the FG state. -/
def ReadyFor (C : Config) (D : Block V) (S : FGState V) : Prop :=
  ChainStatesComputed C S ∧
  ((chainStateOf C D).F.AncestorEq S.J ∨ S.h_j < (chainStateOf C D).h_j) ∧
  (S.h_max ≤ (chainStateOf C D).h ∨
    ∃ X ∈ S.T, (chainStateOf C D).F.AncestorEq X ∧
      max S.h_max (chainStateOf C D).h ≤ (chainStateOf C X).h)

end

end

section

open GoldilocksCorrectness.Statements.Routines (ChainStatesComputed)
open GoldilocksCorrectness.Statements.Routines (chainStateOf)

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- `CachesWitnessed C S`: the justified block and the justification height of the FG state `S`
are those of the chain state of a block of its tree; some block of its tree has the chain-state
height `S.h_max`; and some block of its tree, the finalized block or a descendant of it, has a
chain-state height at least `S.h_max − 1`.

The variables:
- `C`: the parameters; `S`: the FG state. -/
def CachesWitnessed (C : Config) (S : FGState V) : Prop :=
  (∃ D ∈ S.T, S.J = (chainStateOf C D).J ∧ S.h_j = (chainStateOf C D).h_j) ∧
  (∃ X ∈ S.T, (chainStateOf C X).h = S.h_max) ∧
  (∃ W ∈ S.T, S.F.AncestorEq W ∧ S.h_max - 1 ≤ (chainStateOf C W).h)

omit [Fintype V] [RootOrder] in
/-- Receiving an attestation into the FG state keeps the tree, the chain states, the justified
block, the caches and the finalized block. -/
theorem fg_on_attestation_witness_keeps (S : FGState V) (a : Attestation V) :
    (fg_on_attestation S a).T = S.T ∧ (fg_on_attestation S a).σ = S.σ ∧
      (fg_on_attestation S a).J = S.J ∧ (fg_on_attestation S a).h_j = S.h_j ∧
      (fg_on_attestation S a).h_max = S.h_max ∧ (fg_on_attestation S a).F = S.F := by
  simp only [fg_on_attestation, Id.run]
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

omit [Fintype V] [RootOrder] in
/-- A viable descendant reaches `h_max − 1`. -/
theorem has_viable_descendant_witness (S : FGState V) (F : Block V)
    (hv : has_viable_descendant S F = true) :
    ∃ B' ∈ S.T, F.AncestorEq B' ∧ S.h_max - 1 ≤ (S.σ B').h := by
  simp only [has_viable_descendant, decide_eq_true_eq] at hv
  obtain ⟨B', hB', hanc, hvi⟩ := hv
  simp only [is_viable, decide_eq_true_eq] at hvi
  have h1 : (S.h_max : ℕ) ≤ head_height_floor S + 1 := h_max_le_floor_add_one S
  have h2 : (head_height_floor S : ℕ) ≤ (S.σ B').h := hvi
  exact ⟨B', hB', hanc, Nat.sub_le_of_le_add (le_trans h1 (Nat.add_le_add_right h2 1))⟩

omit [Fintype V] in
/-- The finality update keeps the tree and the chain states, raises `h_max` to `σ.h` when it is
greater, keeps the justified block and its height or writes `σ`'s, and keeps the finalized block
or writes `σ.F`, which then has a descendant in the tree at a chain-state height at least the new
`h_max − 1`. -/
theorem update_finality_witness (S : FGState V) (σ : ChainState V) :
    (update_finality S σ).T = S.T ∧ (update_finality S σ).σ = S.σ ∧
      (update_finality S σ).h_max = max S.h_max σ.h ∧
      (((update_finality S σ).J = S.J ∧ (update_finality S σ).h_j = S.h_j) ∨
        ((update_finality S σ).J = σ.J ∧ (update_finality S σ).h_j = σ.h_j)) ∧
      ((update_finality S σ).F = S.F ∨ ((update_finality S σ).F = σ.F ∧
        ∃ B' ∈ S.T, σ.F.AncestorEq B' ∧ max S.h_max σ.h - 1 ≤ (S.σ B').h)) := by
  simp only [update_finality, Id.run]
  split
  · split
    · rename_i h1 h2
      simp only [Bool.and_eq_true] at h2
      exact ⟨rfl, rfl, rfl, Or.inr ⟨rfl, rfl⟩,
        Or.inr ⟨rfl, has_viable_descendant_witness _ _ h2.2⟩⟩
    · exact ⟨rfl, rfl, rfl, Or.inr ⟨rfl, rfl⟩, Or.inl rfl⟩
  · split
    · rename_i h1 h2
      simp only [Bool.and_eq_true] at h2
      exact ⟨rfl, rfl, rfl, Or.inl ⟨rfl, rfl⟩,
        Or.inr ⟨rfl, has_viable_descendant_witness _ _ h2.2⟩⟩
    · exact ⟨rfl, rfl, rfl, Or.inl ⟨rfl, rfl⟩, Or.inl rfl⟩

/-- Accepting a block keeps `CachesWitnessed`, when the chain states of the tree are the blocks'
own, the block's parent is in the tree, the finalized block is an ancestor of the block, and the
block is not the genesis block. -/
theorem fg_on_block_witnessed (C : Config) (S : FGState V) (B : Block V)
    (hCS : ChainStatesComputed C S) (hpar : B.parent ∈ S.T) (hFB : S.F.AncestorEq B)
    (hg : B ≠ Block.genesis) (hW : CachesWitnessed C S) :
    CachesWitnessed C (fg_on_block C S B) := by
  set S₁ : FGState V := { S with
    σ := Function.update S.σ B (state_transition C (S.σ B.parent) B)
    T := S.T ∪ {B} } with hS₁
  have hdef : fg_on_block C S B = forIn (m := Id) B.attestations
      (update_finality S₁ (S₁.σ B))
      (fun a X => Pure.pure (ForInStep.yield (fg_on_attestation X a))) := rfl
  have hfold := forIn_yield_inv B.attestations (update_finality S₁ (S₁.σ B))
    (fun X a => fg_on_attestation X a)
    (fun X => X.T = (update_finality S₁ (S₁.σ B)).T ∧ X.J = (update_finality S₁ (S₁.σ B)).J ∧
      X.h_j = (update_finality S₁ (S₁.σ B)).h_j ∧
      X.h_max = (update_finality S₁ (S₁.σ B)).h_max ∧ X.F = (update_finality S₁ (S₁.σ B)).F)
    ⟨rfl, rfl, rfl, rfl, rfl⟩
    (fun X a _ hX => by
      obtain ⟨h1, _h2, h3, h4, h5, h6⟩ := fg_on_attestation_witness_keeps X a
      exact ⟨h1.trans hX.1, h3.trans hX.2.1, h4.trans hX.2.2.1, h5.trans hX.2.2.2.1,
        h6.trans hX.2.2.2.2⟩)
  -- the chain state written for `B` is `B`'s own, and every chain state of the new tree is its
  -- block's own
  have hσB : S₁.σ B = chainStateOf C B := by
    show Function.update S.σ B (state_transition C (S.σ B.parent) B) B = chainStateOf C B
    rw [Function.update_self, hCS B.parent hpar]
    cases B with
    | genesis => exact absurd rfl hg
    | node p s r votes support ats v => rfl
  have hσ : ∀ Y ∈ S₁.T, S₁.σ Y = chainStateOf C Y := by
    intro Y hY
    by_cases hYB : Y = B
    · rw [hYB]
      exact hσB
    · show Function.update S.σ B (state_transition C (S.σ B.parent) B) Y = chainStateOf C Y
      rw [Function.update_of_ne hYB]
      have hY' : Y ∈ S.T := by
        rcases Finset.mem_union.1 hY with h | h
        · exact h
        · exact absurd (Finset.mem_singleton.1 h) hYB
      exact hCS Y hY'
  have hBT : B ∈ S₁.T := Finset.mem_union_right _ (Finset.mem_singleton_self B)
  have hsub : S.T ⊆ S₁.T := Finset.subset_union_left
  obtain ⟨u1, -, u3, u4, u5⟩ := update_finality_witness S₁ (S₁.σ B)
  rw [hσB] at u4 u5
  obtain ⟨⟨D, hD, hDJ, hDj⟩, ⟨X, hX, hXh⟩, ⟨W, hWT, hFW, hWh⟩⟩ := hW
  rw [hdef]
  unfold CachesWitnessed
  rw [hfold.1, hfold.2.1, hfold.2.2.1, hfold.2.2.2.1, hfold.2.2.2.2, u1, u3, hσB]
  refine ⟨?_, ?_, ?_⟩
  · rcases u4 with ⟨hJ, hj⟩ | ⟨hJ, hj⟩
    · exact ⟨D, hsub hD, hJ.trans hDJ, hj.trans hDj⟩
    · exact ⟨B, hBT, hJ, hj⟩
  · by_cases hle : (chainStateOf C B).h ≤ S.h_max
    · refine ⟨X, hsub hX, ?_⟩
      rw [hXh]
      exact (max_eq_left hle).symm
    · exact ⟨B, hBT, (max_eq_right (Nat.le_of_not_le hle)).symm⟩
  · rcases u5 with hF | ⟨hF, B', hB', hFB', hB'h⟩
    · rw [hF]
      by_cases hle : (chainStateOf C B).h ≤ S.h_max
      · refine ⟨W, hsub hWT, hFW, ?_⟩
        rw [max_eq_left hle]
        exact hWh
      · refine ⟨B, hBT, hFB, ?_⟩
        rw [max_eq_right (Nat.le_of_not_le hle)]
        exact Nat.sub_le _ _
    · rw [hF]
      refine ⟨B', hB', hFB', ?_⟩
      rw [← hσ B' hB']
      exact hB'h

end

end

section

open GoldilocksCorrectness.Statements.Routines (ChainStatesComputed)

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

omit [RootOrder] in
/-- An FG state whose chain states of its tree are the blocks' own, whose justified block is in its
tree, with the finalized block an ancestor of it, and which satisfies
`CachesWitnessed`, has a viable head: in box 3 the block that makes it contested; in box 2 the
justified block; otherwise a block on the finalized block's chain at a chain-state height at
least `h_max − 1`. -/
theorem exists_viable_head_of_witnessed (C : Config) (S : FGState V)
    (hCS : ChainStatesComputed C S) (hFJ : S.F.AncestorEq S.J)
    (hJT : S.J ∈ S.T) (hW : CachesWitnessed C S) :
    ∃ W : Block V, W ∈ (fg_to_ac S).viable_heads := by
  obtain ⟨⟨D, -, hDJ, hDj⟩, -, ⟨W, hWT, hFW, hWh⟩⟩ := hW
  have hfc : (fg_to_ac S).fc_root = get_fc_root S := rfl
  cases hc : fg_contest S with
  | true =>
      obtain ⟨-, hroot, hfloor⟩ :=
        GoldilocksCorrectness.Statements.Routines.frameShape_of_boxThree S hc
      have hc' := hc
      simp only [fg_contest, Id.run] at hc'
      split at hc'
      · exact absurd hc' Bool.false_ne_true
      · have hc'' : ∃ B ∈ S.T, S.F.ancestorEq B = true ∧ S.σ[B].h = S.h_max ∧
            ¬ S.J.ancestorEq B = true := of_decide_eq_true hc'
        obtain ⟨B, hBT, hFB, hBh, -⟩ := hc''
        refine ⟨B, (mem_viable_heads_iff S B).2 ⟨hBT, hFB, ?_, ?_⟩⟩
        · rw [hfc, hroot]
          exact hFB
        · rw [hfloor]
          exact le_of_eq hBh.symm
  | false =>
      by_cases hbox : S.h_max = S.h_j + 1
      · obtain ⟨hroot, hfloor⟩ :=
          GoldilocksCorrectness.Statements.Routines.frameShape_of_boxTwo S S.J ⟨hbox, hc, rfl⟩
        refine ⟨S.J, (mem_viable_heads_iff S S.J).2 ⟨hJT, hFJ, ?_, ?_⟩⟩
        · rw [hfc, hroot]
          exact ancestorEq_refl _
        · rw [hfloor, hCS S.J hJT, hbox, Nat.add_sub_cancel]
          rcases Nat.eq_zero_or_pos S.h_j with h0 | hpos
          · rw [h0]
            exact Nat.zero_le _
          · rw [hDJ, hDj]
            rw [hDj] at hpos
            exact le_of_eq ((chainStateOf_J_spec C D).2.2 hpos).symm
      · have hroot : get_fc_root S = S.F := by
          simp [get_fc_root, hbox]
        have hfloor : head_height_floor S = S.h_max - 1 := by
          simp [head_height_floor, hc]
        refine ⟨W, (mem_viable_heads_iff S W).2 ⟨hWT, hFW, ?_, ?_⟩⟩
        · rw [hfc, hroot]
          exact hFW
        · rw [hfloor, hCS W hWT]
          exact hWh

end

end

end GoldilocksCorrectness.Proofs.Routines
