module
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.ChainStateDefs
public import GoldilocksCorrectness.Statements.Routines.FGStateDefs

@[expose] public section

/-!
# Conditions on a node's FG part, over a model

The definitions of `GoldilocksCorrectness/Statements/Routines/FGStateDefs.lean` over a model
`M`, each a condition on a node state `n : M.N` read through the record's node readers, and the
greatest chain-state height of the node's tree, `hMax M C n`, with the two theorems that bound it.

The record has no reader for the chain states a node holds for the blocks of its tree, nor for the
node's cache of the greatest chain-state height: a node's chain state of a block is the block's own,
`M.chainStateOf C B`, and the greatest height is `hMax M C n`. So `ChainStatesComputed M C n` and
`HeightCacheBounds M C n` hold of every node state (`chainStatesComputed`, `heightCacheBounds`), and
the conditions that read a chain state take the parameters `C`.

At the spec's model a condition that reads no chain state the node holds is the landed definition
(the equations `goldilocks_…`, in the simp set `record_goldilocks`); one that reads them is the
landed definition when the node's chain states are the blocks' own (the theorems
`goldilocks_AttestationsValid`, `goldilocks_JustificationCacheBounds`,
`goldilocks_JustifiedHeight`, each with that hypothesis).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Statements.Routines

open Goldilocks
open GoldilocksCorrectness.Record

variable {V : Type} [DecidableEq V] [Fintype V]

/-- `hMax M C n`: the greatest chain-state height of a block of the tree `n.tree`, or `0` for an
empty tree.

The variables:
- `M`: the model;
- `C`: the parameters; `n`: the node state.

Read aloud: the greatest chain-state height in `n`'s tree. -/
def hMax (M : GoldilocksModel V) (C : Config) (n : M.N) : Height :=
  n.tree.sup (fun B => (M.chainStateOf C B).h)

/-- `FinalizedFromChain M C n`: the finalized block `n.finalized` of the node state `n` is the
finalized block of the chain state `M.chainStateOf C B` of a block `B` of the tree `n.tree`.

The variables:
- `M`: the model;
- `C`: the parameters; `n`: the node state.

Read aloud: the node's finalized block is the finalized block of the chain state of a block of its
tree. -/
def FinalizedFromChain (M : GoldilocksModel V) (C : Config) (n : M.N) : Prop :=
  ∃ B ∈ n.tree, n.finalized = (M.chainStateOf C B).F

/-- `ChainStatesComputed M C n`: the chain state the node holds for each block of its tree is the
one computed from the block alone. The record reads a node's chain state of a block as the block's
own, `M.chainStateOf C B`, so the condition holds of every node state (`chainStatesComputed`).

The variables:
- `M`: the model;
- `C`: the parameters; `n`: the node state.

Read aloud: the node's chain states of its tree are the blocks' own. -/
def ChainStatesComputed (M : GoldilocksModel V) (C : Config) (n : M.N) : Prop :=
  ∀ B ∈ n.tree, M.chainStateOf C B = M.chainStateOf C B

/-- `AttestationsValid M C n`: every attestation a non-genesis block of the tree `n.tree` includes
is valid against the chain state `M.chainStateOf C B.parent` of the block's parent.

The variables:
- `M`: the model;
- `C`: the parameters; `n`: the node state.

Read aloud: every included attestation is valid against the parent's chain state. -/
def AttestationsValid (M : GoldilocksModel V) (C : Config) (n : M.N) : Prop :=
  ∀ B ∈ n.tree, B ≠ Block.genesis →
    ∀ a ∈ B.attestations, M.valid_attestation (M.chainStateOf C B.parent) a = true

/-- `FinalizedAncestorJustified M n`: the finalized block `n.finalized` of the node state `n` is
its justified block `n.justified` or an ancestor of it.

The variables:
- `M`: the model;
- `n`: the node state.

Read aloud: the finalized block is on the justified block's chain. -/
def FinalizedAncestorJustified (M : GoldilocksModel V) (n : M.N) : Prop :=
  n.finalized.AncestorEq n.justified

/-- `HeightCacheBounds M C n`: no block of the tree `n.tree` has a chain-state height greater than
`hMax M C n`. It holds of every node state (`heightCacheBounds`).

The variables:
- `M`: the model;
- `C`: the parameters; `n`: the node state.

Read aloud: `hMax M C n` is at least the chain-state height of every accepted block. -/
def HeightCacheBounds (M : GoldilocksModel V) (C : Config) (n : M.N) : Prop :=
  ∀ B ∈ n.tree, (M.chainStateOf C B).h ≤ hMax M C n

/-- `JustificationCacheBounds M C n`: no block `B` of the tree `n.tree` that is the finalized
block `n.finalized` or a descendant of it has a justification height `(M.chainStateOf C B).h_j`
greater than the node's justification height `n.justifiedHeight`.

The variables:
- `M`: the model;
- `C`: the parameters; `n`: the node state.

Read aloud: no accepted block on the finalized block's chain has a justification height greater
than the node's. -/
def JustificationCacheBounds (M : GoldilocksModel V) (C : Config) (n : M.N) : Prop :=
  ∀ B ∈ n.tree, n.finalized.AncestorEq B → (M.chainStateOf C B).h_j ≤ n.justifiedHeight

/-- `JustifiedHeight M C n`: the justified block `n.justified` of the node state `n` is the
genesis block, or its chain-state height `(M.chainStateOf C n.justified).h` is the node's
justification height `n.justifiedHeight`.

The variables:
- `M`: the model;
- `C`: the parameters; `n`: the node state.

Read aloud: the justified block's own chain-state height is the justification height, the genesis
block excepted. -/
def JustifiedHeight (M : GoldilocksModel V) (C : Config) (n : M.N) : Prop :=
  n.justified = Block.genesis ∨ (M.chainStateOf C n.justified).h = n.justifiedHeight

/-- `JustifiedInTree M n`: the justified block `n.justified` of the node state `n` is in its tree
`n.tree`.

The variables:
- `M`: the model;
- `n`: the node state.

Read aloud: the justified block is accepted. -/
def JustifiedInTree (M : GoldilocksModel V) (n : M.N) : Prop :=
  n.justified ∈ n.tree

/-- Every block of the tree `n.tree` has a chain-state height at most `hMax M C n`.

The variables:
- `M`: the model;
- `C`: the parameters; `n`: the node state; `B`: the block.

Read aloud: an accepted block's chain-state height is at most the greatest one. -/
theorem le_hMax (M : GoldilocksModel V) {C : Config} {n : M.N} {B : Block V} (hB : B ∈ n.tree) :
    (M.chainStateOf C B).h ≤ hMax M C n :=
  Finset.le_sup (f := fun B => (M.chainStateOf C B).h) hB

/-- A nonempty tree `n.tree` has a block whose chain-state height is `hMax M C n`.

The variables:
- `M`: the model;
- `C`: the parameters; `n`: the node state.

Read aloud: the greatest chain-state height of a nonempty tree is the height of one of its
blocks. -/
theorem exists_eq_hMax (M : GoldilocksModel V) {C : Config} {n : M.N} (h : n.tree.Nonempty) :
    ∃ B ∈ n.tree, (M.chainStateOf C B).h = hMax M C n := by
  obtain ⟨B, hB, hEq⟩ := Finset.exists_mem_eq_sup n.tree h (fun B => (M.chainStateOf C B).h)
  exact ⟨B, hB, hEq.symm⟩

/-- `ChainStatesComputed M C n` holds of every node state.

The variables:
- `M`: the model;
- `C`: the parameters; `n`: the node state.

Read aloud: over the record, a node's chain states are the blocks' own. -/
theorem chainStatesComputed (M : GoldilocksModel V) (C : Config) (n : M.N) :
    ChainStatesComputed M C n :=
  fun _ _ => rfl

/-- `HeightCacheBounds M C n` holds of every node state.

The variables:
- `M`: the model;
- `C`: the parameters; `n`: the node state.

Read aloud: over the record, every accepted block's chain-state height is at most `hMax M C n`. -/
theorem heightCacheBounds (M : GoldilocksModel V) (C : Config) (n : M.N) :
    HeightCacheBounds M C n :=
  fun _ hB => le_hMax M hB

/-! ## At the spec's model -/

/-- At the spec's model, `FinalizedFromChain` is the landed definition.

The variables:
- `C`, `n`: as in `FinalizedFromChain`, at the spec's model.

Read aloud: the spec's model has the landed `FinalizedFromChain`. -/
@[record_goldilocks]
theorem goldilocks_FinalizedFromChain (C : Config) (n : NodeState V) :
    GoldilocksCorrectness.Statements.Routines.FinalizedFromChain C n.S =
      FinalizedFromChain (Model.goldilocks (V := V)) C n := rfl

/-- At the spec's model, `FinalizedAncestorJustified` is the landed definition.

The variables:
- `n`: as in `FinalizedAncestorJustified`, at the spec's model.

Read aloud: the spec's model has the landed `FinalizedAncestorJustified`. -/
@[record_goldilocks]
theorem goldilocks_FinalizedAncestorJustified (n : NodeState V) :
    GoldilocksCorrectness.Statements.Routines.FinalizedAncestorJustified n.S =
      FinalizedAncestorJustified (Model.goldilocks (V := V)) n := rfl

/-- At the spec's model, `JustifiedInTree` is the landed definition.

The variables:
- `n`: as in `JustifiedInTree`, at the spec's model.

Read aloud: the spec's model has the landed `JustifiedInTree`. -/
@[record_goldilocks]
theorem goldilocks_JustifiedInTree (n : NodeState V) :
    GoldilocksCorrectness.Statements.Routines.JustifiedInTree n.S =
      JustifiedInTree (Model.goldilocks (V := V)) n := rfl

/-- At the spec's model, `AttestationsValid` is the landed definition when the node's chain
states of its tree are the blocks' own and every non-genesis block of its tree has its parent in the
tree.

The variables:
- `C`: the parameters; `n`: the node state;
- `hσ`: the node's chain states of its tree are the blocks' own;
- `hpar`: every non-genesis block of the tree has its parent in the tree.

Read aloud: under those two conditions, the spec's model has the landed `AttestationsValid`. -/
theorem goldilocks_AttestationsValid (C : Config) (n : NodeState V)
    (hσ : GoldilocksCorrectness.Statements.Routines.ChainStatesComputed C n.S)
    (hpar : ∀ B ∈ n.S.T, B ≠ Block.genesis → B.parent ∈ n.S.T) :
    GoldilocksCorrectness.Statements.Routines.AttestationsValid n.S ↔
      AttestationsValid (Model.goldilocks (V := V)) C n := by
  constructor
  · intro h B hB hg a ha
    have h1 := h B hB hg a ha
    rw [hσ B.parent (hpar B hB hg)] at h1
    exact h1
  · intro h B hB hg a ha
    show Goldilocks.valid_attestation (n.S.σ B.parent) a = true
    rw [hσ B.parent (hpar B hB hg)]
    exact h B hB hg a ha

/-- At the spec's model, `JustificationCacheBounds` is the landed definition when the node's chain
states of its tree are the blocks' own.

The variables:
- `C`: the parameters; `n`: the node state;
- `hσ`: the node's chain states of its tree are the blocks' own.

Read aloud: under that condition, the spec's model has the landed `JustificationCacheBounds`. -/
theorem goldilocks_JustificationCacheBounds (C : Config) (n : NodeState V)
    (hσ : GoldilocksCorrectness.Statements.Routines.ChainStatesComputed C n.S) :
    GoldilocksCorrectness.Statements.Routines.JustificationCacheBounds n.S ↔
      JustificationCacheBounds (Model.goldilocks (V := V)) C n := by
  constructor
  · intro h B hB hF
    have h1 := h B hB hF
    rw [hσ B hB] at h1
    exact h1
  · intro h B hB hF
    show (n.S.σ B).h_j ≤ n.S.h_j
    rw [hσ B hB]
    exact h B hB hF

/-- At the spec's model, `JustifiedHeight` is the landed definition when the node's chain states of
its tree are the blocks' own and its justified block is in its tree.

The variables:
- `C`: the parameters; `n`: the node state;
- `hσ`: the node's chain states of its tree are the blocks' own;
- `hJ`: the justified block is in the tree.

Read aloud: under those two conditions, the spec's model has the landed `JustifiedHeight`. -/
theorem goldilocks_JustifiedHeight (C : Config) (n : NodeState V)
    (hσ : GoldilocksCorrectness.Statements.Routines.ChainStatesComputed C n.S)
    (hJ : n.S.J ∈ n.S.T) :
    GoldilocksCorrectness.Statements.Routines.JustifiedHeight n.S ↔
      JustifiedHeight (Model.goldilocks (V := V)) C n := by
  show (n.S.J = Block.genesis ∨ (n.S.σ n.S.J).h = n.S.h_j) ↔ _
  rw [hσ n.S.J hJ]
  exact Iff.rfl

end GoldilocksCorrectness.Record.Statements.Routines
