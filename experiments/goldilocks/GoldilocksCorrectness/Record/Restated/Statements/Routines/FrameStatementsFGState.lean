module
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.FrameFGState
public import GoldilocksCorrectness.Statements.Routines.FrameStatements

@[expose] public section

/-!
# FrameStatementsFGState, over a model: Lemma 56 and its three cases

The node-state statements of `GoldilocksCorrectness/Statements/Routines/FrameStatements.lean` over a
model `M` whose facts `F` hold: Lemma 56, the frame of a node state of a given shape, and its three
cases. Each is stated for a node state `n` satisfying the model's node invariant
`M.nodeInv C P X n`, with `hMax M C n` for the stored greatest height and `M.chainStateOf C B` for
the stored chain state of a block. Lemma 56's statement about viability reads the blocks of `n`'s
tree: the record reads the chain state of a block of the tree only. Proved on
`Record/Restated/Proofs/Routines/FrameFGState.lean`.

The recovery section at the end of the page states each landed theorem again, as the landed
statement (`type_of%`) at the FG state `n.S` of a node state `n` satisfying the spec's model's node
invariant, and proves it from its record form at the spec's model `Model.goldilocks` and its facts
`goldilocksFacts`. Lemma 56 has no recovery here: the landed statement reads the viability of every
block, of the tree or not, and its record form takes the block in the tree (see
`Record/Restated/Proofs/Routines/FrameFGState.lean`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Statements.Routines

open Goldilocks
open GoldilocksCorrectness.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section

variable (M : GoldilocksModel V) (F : Facts M)
include M F

/-- **Lemma 56, the frame of a shape.** When the fgroot of `n` is `ρ` and its `head_height_floor`
is `φ`, the frame `M.fg_to_ac n` has the root `ρ`; a block of the tree is viable exactly when its
chain-state height is at least `φ`; and the viable heads are the blocks of `n`'s tree of which
`n.finalized` and `ρ` are ancestors (or which are `n.finalized`, `ρ`) and whose chain-state height
is at least `φ`.

Why: `fg_to_ac` writes the fgroot as the root and filters its viable heads by the root's ancestry
and `is_viable`, which compares the chain-state height with `head_height_floor`.

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the given values, the digest; `n`: the node state;
- `hI`: `n` satisfies the model's node invariant; `ρ`: the root; `φ`: the least height of a viable
  block.

Read aloud: the frame of a shape is rooted at `ρ`, and its viable heads are the accepted blocks on
`ρ`'s chain, from `ρ` on, whose chain-state height is at least `φ`. -/
theorem lem56_frame_of_shape (C : Config) (P : Provisional V) (X : External V) (n : M.N)
    -- `n` satisfies the model's node invariant
    (hI : M.nodeInv C P X n) (ρ : Block V) (φ : Height)
    -- `n`'s fgroot is `ρ` and its `head_height_floor` is `φ`
    (hShape : FrameShape M n ρ φ) :
    (M.fg_to_ac n).fc_root = ρ ∧
    (∀ B ∈ n.tree, M.is_viable n B = true ↔ φ ≤ (M.chainStateOf C B).h) ∧
    (∀ B : Block V, B ∈ (M.fg_to_ac n).viable_heads ↔
      B ∈ n.tree ∧ n.finalized.AncestorEq B ∧ ρ.AncestorEq B ∧ φ ≤ (M.chainStateOf C B).h) :=
  GoldilocksCorrectness.Record.Proofs.Routines.lem56_frame_of_shape M F C P X n hI ρ φ hShape

/-- **Lemma 56, box 1: not contested; root the finalized block, least viable height
`hMax M C n − 1`.** When `n.justifiedHeight + 1 < hMax M C n`, `n` is not contested, its fgroot is
its finalized block, and its `head_height_floor` is `hMax M C n − 1`.

Why: `fg_contest` answers false at its first test, since `hMax M C n ≠ n.justifiedHeight + 1`;
then `get_fc_root` and `head_height_floor` take their second branches.

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the given values, the digest; `n`: the node state;
- `hI`: `n` satisfies the model's node invariant.

Read aloud: in box 1 the fork choice is rooted at the finalized block and a block is viable from
height `hMax M C n − 1` on. -/
theorem frameShape_of_boxOne (C : Config) (P : Provisional V) (X : External V) (n : M.N)
    -- `n` satisfies the model's node invariant
    (hI : M.nodeInv C P X n)
    -- `n` is in box 1
    (h : BoxOne M C n) :
    M.fg_contest n = false ∧ FrameShape M n n.finalized (hMax M C n - 1) :=
  GoldilocksCorrectness.Record.Proofs.Routines.frameShape_of_boxOne M F C P X n hI h

/-- **Lemma 56, box 2: root `J₀`, least viable height `hMax M C n − 1`.** When
`hMax M C n = n.justifiedHeight + 1`, `n` is not contested and its justified block is `J₀`, its
fgroot is `J₀` and its `head_height_floor` is `hMax M C n − 1`.

Why: the condition of `get_fc_root` holds, and `head_height_floor` takes its second branch.

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the given values, the digest; `n`: the node state;
- `hI`: `n` satisfies the model's node invariant; `J₀`: the justified block.

Read aloud: in box 2 the fork choice is rooted at the justified block `J₀` and a block is viable
from height `hMax M C n − 1` on. -/
theorem frameShape_of_boxTwo (C : Config) (P : Provisional V) (X : External V) (n : M.N)
    -- `n` satisfies the model's node invariant
    (hI : M.nodeInv C P X n) (J₀ : Block V)
    -- `n` is in box 2 with the justified block `J₀`
    (h : BoxTwo M C n J₀) :
    FrameShape M n J₀ (hMax M C n - 1) :=
  GoldilocksCorrectness.Record.Proofs.Routines.frameShape_of_boxTwo M F C P X n hI J₀ h

/-- **Lemma 56, box 3: `hMax M C n = n.justifiedHeight + 1`; root the finalized block, least
viable height `hMax M C n`.** When `n` is contested, `hMax M C n = n.justifiedHeight + 1`, its
fgroot is its finalized block, and its `head_height_floor` is `hMax M C n`.

Why: `fg_contest` answers true only past its first test, which needs
`hMax M C n = n.justifiedHeight + 1`; the condition of `get_fc_root` fails on `fg_contest`, and
`head_height_floor` takes its first branch.

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the given values, the digest; `n`: the node state;
- `hI`: `n` satisfies the model's node invariant.

Read aloud: in box 3 the fork choice is rooted at the finalized block and a block is viable from
height `hMax M C n` on. -/
theorem frameShape_of_boxThree (C : Config) (P : Provisional V) (X : External V) (n : M.N)
    -- `n` satisfies the model's node invariant
    (hI : M.nodeInv C P X n)
    -- `n` is in box 3
    (h : BoxThree M n) :
    hMax M C n = n.justifiedHeight + 1 ∧ FrameShape M n n.finalized (hMax M C n) :=
  GoldilocksCorrectness.Record.Proofs.Routines.frameShape_of_boxThree M F C P X n hI h

end

/-! ## At the spec's model -/

/-- The landed `GoldilocksCorrectness.Statements.Routines.frameShape_of_boxOne`, recovered from its
record form at the spec's model, at the FG state `n.S` of every node state `n` satisfying the spec's
model's node invariant.

Read aloud: the landed `frameShape_of_boxOne` holds at the FG state of every node state satisfying
the invariant. -/
theorem frameShape_of_boxOne_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (C : Config) (P : Provisional V) (X : External V) (n : NodeState V),
      (Model.goldilocks (V := V)).nodeInv C P X n →
      type_of% (@GoldilocksCorrectness.Statements.Routines.frameShape_of_boxOne V _ n.S) := by
  intro C P X n hI h
  have h' := frameShape_of_boxOne Model.goldilocks goldilocksFacts C P X n hI
    ((goldilocks_BoxOne C n (hMax_goldilocks hI).symm).1 h)
  rw [hMax_goldilocks hI] at h'
  exact h'

/-- The landed `GoldilocksCorrectness.Statements.Routines.frameShape_of_boxTwo`, recovered from its
record form at the spec's model, at the FG state `n.S` of every node state `n` satisfying the spec's
model's node invariant.

Read aloud: the landed `frameShape_of_boxTwo` holds at the FG state of every node state satisfying
the invariant. -/
theorem frameShape_of_boxTwo_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (C : Config) (P : Provisional V) (X : External V) (n : NodeState V),
      (Model.goldilocks (V := V)).nodeInv C P X n →
      type_of% (@GoldilocksCorrectness.Statements.Routines.frameShape_of_boxTwo V _ n.S) := by
  intro C P X n hI J₀ h
  have h' := frameShape_of_boxTwo Model.goldilocks goldilocksFacts C P X n hI J₀
    ((goldilocks_BoxTwo C n J₀ (hMax_goldilocks hI).symm).1 h)
  rw [hMax_goldilocks hI] at h'
  exact h'

/-- The landed `GoldilocksCorrectness.Statements.Routines.frameShape_of_boxThree`, recovered from
its record form at the spec's model, at the FG state `n.S` of every node state `n` satisfying the
spec's model's node invariant.

Read aloud: the landed `frameShape_of_boxThree` holds at the FG state of every node state
satisfying the invariant. -/
theorem frameShape_of_boxThree_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (C : Config) (P : Provisional V) (X : External V) (n : NodeState V),
      (Model.goldilocks (V := V)).nodeInv C P X n →
      type_of% (@GoldilocksCorrectness.Statements.Routines.frameShape_of_boxThree V _ n.S) := by
  intro C P X n hI h
  have h' := frameShape_of_boxThree Model.goldilocks goldilocksFacts C P X n hI h
  rw [hMax_goldilocks hI] at h'
  exact h'

end GoldilocksCorrectness.Record.Statements.Routines
