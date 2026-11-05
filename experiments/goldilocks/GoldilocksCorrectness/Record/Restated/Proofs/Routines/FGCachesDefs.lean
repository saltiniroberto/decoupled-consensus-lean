module
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.FGStateDefs
public import GoldilocksCorrectness.Proofs.Routines.FGCaches

@[expose] public section

/-!
# The caches of a node on its chain, over a model

The definitions of `GoldilocksCorrectness/Proofs/Routines/FGCaches.lean` over a model `M`, each a
condition on a node state `n : M.N`: its justified block and justification height on a chain, a
block ready to be added, and the node's justification and greatest height witnessed by blocks of its
tree. They are on a page of their own, which imports no facts, because the facts of the FG-state
family name them.

At the spec's model `CachesOnChainWith` is the landed definition (the equation
`goldilocks_CachesOnChainWith`, in the simp set `record_goldilocks`); `ReadyFor` and
`CachesWitnessed` are the landed definitions when the node's cache `n.S.h_max` is `hMax` (and, for
`ReadyFor`, its chain states of its tree are the blocks' own).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Record
open GoldilocksCorrectness.Record.Statements.Routines (IsEntry ChainStatesComputed hMax
  chainStatesComputed)

variable {V : Type} [DecidableEq V] [Fintype V]

/-- `CachesOnChainWith M C H OnChain n`: the node's justification height `n.justifiedHeight` is
greater than `H`; its justified block `n.justified` satisfies `OnChain`, is the block that took its
chain into its height, and has the chain-state height `n.justifiedHeight`; and its finalized block
is the justified block or an ancestor of it.

The variables:
- `M`: the model;
- `C`: the parameters; `H`: the height; `OnChain`: the condition on blocks; `n`: the node state.

Read aloud: the node's justified block, justified at a height greater than `H`, satisfies `OnChain`,
entered its height, and has its finalized block on its chain. -/
def CachesOnChainWith (M : GoldilocksModel V) (C : Config) (H : ℕ) (OnChain : Block V → Prop)
    (n : M.N) : Prop :=
  H < n.justifiedHeight ∧ OnChain n.justified ∧ IsEntry M C n.justified ∧
    (M.chainStateOf C n.justified).h = n.justifiedHeight ∧
    n.finalized.AncestorEq n.justified

/-- `ReadyFor M C D n`: the node's chain states of its tree are the blocks' own; the finalized
block of `D`'s chain state is the node's justified block or an ancestor of it, or `D`'s
justification height is greater than the node's; and `hMax M C n` is at most `D`'s chain-state
height, or some block `X` of the tree that has the finalized block of `D`'s chain state as an
ancestor or is it has a chain-state height at least `hMax M C n` and at least `D`'s.

The variables:
- `M`: the model;
- `C`: the parameters; `D`: the block; `n`: the node state.

Read aloud: the node is ready for `D`: its justified block is on the chain of `D`'s finalized block
or `D` is justified higher, and its greatest chain-state height is at most `D`'s or is reached by a
block on the chain of `D`'s finalized block. -/
def ReadyFor (M : GoldilocksModel V) (C : Config) (D : Block V) (n : M.N) : Prop :=
  ChainStatesComputed M C n ∧
  ((M.chainStateOf C D).F.AncestorEq n.justified ∨ n.justifiedHeight < (M.chainStateOf C D).h_j) ∧
  (hMax M C n ≤ (M.chainStateOf C D).h ∨
    ∃ X ∈ n.tree, (M.chainStateOf C D).F.AncestorEq X ∧
      max (hMax M C n) (M.chainStateOf C D).h ≤ (M.chainStateOf C X).h)

/-- `CachesWitnessed M C n`: some block `D` of the tree `n.tree` has the node's justified block and
justification height in its chain state; some block of the tree has the chain-state height
`hMax M C n`; and some block `W` of the tree that is the finalized block or a descendant of it has a
chain-state height at least `hMax M C n − 1`.

The variables:
- `M`: the model;
- `C`: the parameters; `n`: the node state.

Read aloud: the node's justification and its greatest chain-state height are witnessed by blocks of
its tree. -/
def CachesWitnessed (M : GoldilocksModel V) (C : Config) (n : M.N) : Prop :=
  (∃ D ∈ n.tree, n.justified = (M.chainStateOf C D).J ∧
    n.justifiedHeight = (M.chainStateOf C D).h_j) ∧
  (∃ X ∈ n.tree, (M.chainStateOf C X).h = hMax M C n) ∧
  (∃ W ∈ n.tree, n.finalized.AncestorEq W ∧ hMax M C n - 1 ≤ (M.chainStateOf C W).h)

/-! ## At the spec's model -/

/-- At the spec's model, `CachesOnChainWith` is the landed definition.

The variables:
- `C`, `H`, `OnChain`, `n`: as in `CachesOnChainWith`, at the spec's model.

Read aloud: the spec's model has the landed `CachesOnChainWith`. -/
@[record_goldilocks]
theorem goldilocks_CachesOnChainWith (C : Config) (H : ℕ) (OnChain : Block V → Prop)
    (n : NodeState V) :
    GoldilocksCorrectness.Proofs.Routines.CachesOnChainWith C H OnChain n.S =
      CachesOnChainWith (Model.goldilocks (V := V)) C H OnChain n := rfl

/-- At the spec's model, `ReadyFor` is the landed definition when the node's chain states of its
tree are the blocks' own and its cache `n.S.h_max` is `hMax`.

The variables:
- `C`: the parameters; `D`: the block; `n`: the node state;
- `hσ`: the node's chain states of its tree are the blocks' own;
- `hH`: the node's cache of the greatest chain-state height is `hMax`.

Read aloud: under those two conditions, the spec's model has the landed `ReadyFor`. -/
theorem goldilocks_ReadyFor (C : Config) (D : Block V) (n : NodeState V)
    (hσ : GoldilocksCorrectness.Statements.Routines.ChainStatesComputed C n.S)
    (hH : n.S.h_max = hMax (Model.goldilocks (V := V)) C n) :
    GoldilocksCorrectness.Proofs.Routines.ReadyFor C D n.S ↔
      ReadyFor (Model.goldilocks (V := V)) C D n := by
  unfold GoldilocksCorrectness.Proofs.Routines.ReadyFor ReadyFor
  rw [hH]
  exact ⟨fun h => ⟨chainStatesComputed (Model.goldilocks (V := V)) C n, h.2⟩,
    fun h => ⟨hσ, h.2⟩⟩

/-- At the spec's model, `CachesWitnessed` is the landed definition when the node's cache
`n.S.h_max` is `hMax`.

The variables:
- `C`: the parameters; `n`: the node state;
- `hH`: the node's cache of the greatest chain-state height is `hMax`.

Read aloud: when the cache is the greatest chain-state height, the spec's model has the landed
`CachesWitnessed`. -/
theorem goldilocks_CachesWitnessed (C : Config) (n : NodeState V)
    (hH : n.S.h_max = hMax (Model.goldilocks (V := V)) C n) :
    GoldilocksCorrectness.Proofs.Routines.CachesWitnessed C n.S ↔
      CachesWitnessed (Model.goldilocks (V := V)) C n := by
  unfold GoldilocksCorrectness.Proofs.Routines.CachesWitnessed CachesWitnessed
  rw [hH]
  exact Iff.rfl

end GoldilocksCorrectness.Record.Proofs.Routines
