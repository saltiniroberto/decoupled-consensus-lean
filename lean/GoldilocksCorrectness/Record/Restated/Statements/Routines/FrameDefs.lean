module
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.FGStateDefs
public import GoldilocksCorrectness.Statements.Routines.FrameDefs

@[expose] public section

/-!
# The fgroot and the three cases of Lemma 56, over a model

The definitions of `GoldilocksCorrectness/Statements/Routines/FrameDefs.lean` over a model `M`:
the node's fgroot and `head_height_floor` named, and the three cases of Lemma 56, each a condition
on a node state `n : M.N`. The node's greatest chain-state height is `hMax M C n`, so `BoxOne` and
`BoxTwo` take the parameters `C`.

At the spec's model `FrameShape` and `BoxThree` are the landed definitions (the equations
`goldilocks_FrameShape`, `goldilocks_BoxThree`, in the simp set `record_goldilocks`); `BoxOne` and
`BoxTwo` are the landed definitions when the node's cache `n.S.h_max` is `hMax` (the theorems
`goldilocks_BoxOne`, `goldilocks_BoxTwo`, with that hypothesis).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Statements.Routines

open Goldilocks
open GoldilocksCorrectness.Record

variable {V : Type} [DecidableEq V] [Fintype V]

/-- `FrameShape M n ρ φ`: the fgroot of the node state `n` is `ρ` and its `head_height_floor` is
`φ`.

The variables:
- `M`: the model;
- `n`: the node state; `ρ`: the block; `φ`: the height.

Read aloud: `n`'s fgroot is `ρ`, and the least chain-state height of a viable block of `n` is
`φ`. -/
def FrameShape (M : GoldilocksModel V) (n : M.N) (ρ : Block V) (φ : Height) : Prop :=
  M.get_fc_root n = ρ ∧ M.head_height_floor n = φ

/-- `BoxOne M C n`: the first case of Lemma 56: the node's justification height plus one is less
than `hMax M C n`.

The variables:
- `M`: the model;
- `C`: the parameters; `n`: the node state.

Read aloud: `n.justifiedHeight + 1 < hMax M C n`. -/
def BoxOne (M : GoldilocksModel V) (C : Config) (n : M.N) : Prop :=
  n.justifiedHeight + 1 < hMax M C n

/-- `BoxTwo M C n J₀`: the second case of Lemma 56: `hMax M C n` is the node's justification
height plus one, the node's FG state is not contested, and its justified block is `J₀`.

The variables:
- `M`: the model;
- `C`: the parameters; `n`: the node state.
- `J₀`: the block.

Read aloud: `hMax M C n = n.justifiedHeight + 1`, `n` is not contested, and `n.justified = J₀`. -/
def BoxTwo (M : GoldilocksModel V) (C : Config) (n : M.N) (J₀ : Block V) : Prop :=
  hMax M C n = n.justifiedHeight + 1 ∧ M.fg_contest n = false ∧ n.justified = J₀

/-- `BoxThree M n`: the third case of Lemma 56: the node's FG state is contested.

The variables:
- `M`: the model;
- `n`: the node state.

Read aloud: `n`'s FG state is contested. -/
def BoxThree (M : GoldilocksModel V) (n : M.N) : Prop :=
  M.fg_contest n = true

/-! ## At the spec's model -/

/-- At the spec's model, `FrameShape` is the landed definition.

The variables:
- `n`, `ρ`, `φ`: as in `FrameShape`, at the spec's model.

Read aloud: the spec's model has the landed `FrameShape`. -/
@[record_goldilocks]
theorem goldilocks_FrameShape (n : NodeState V) (ρ : Block V) (φ : Height) :
    GoldilocksCorrectness.Statements.Routines.FrameShape n.S ρ φ =
      FrameShape (Model.goldilocks (V := V)) n ρ φ := rfl

/-- At the spec's model, `BoxThree` is the landed definition.

The variables:
- `n`: as in `BoxThree`, at the spec's model.

Read aloud: the spec's model has the landed `BoxThree`. -/
@[record_goldilocks]
theorem goldilocks_BoxThree (n : NodeState V) :
    GoldilocksCorrectness.Statements.Routines.BoxThree n.S =
      BoxThree (Model.goldilocks (V := V)) n := rfl

/-- At the spec's model, `BoxOne` is the landed definition when the node's cache `n.S.h_max` is
`hMax`.

The variables:
- `C`: the parameters; `n`: the node state;
- `hH`: the node's cache of the greatest chain-state height is `hMax`.

Read aloud: when the cache is the greatest chain-state height, the spec's model has the landed
`BoxOne`. -/
theorem goldilocks_BoxOne (C : Config) (n : NodeState V)
    (hH : n.S.h_max = hMax (Model.goldilocks (V := V)) C n) :
    GoldilocksCorrectness.Statements.Routines.BoxOne n.S ↔
      BoxOne (Model.goldilocks (V := V)) C n := by
  show n.S.h_j + 1 < n.S.h_max ↔ _
  rw [hH]
  exact Iff.rfl

/-- At the spec's model, `BoxTwo` is the landed definition when the node's cache `n.S.h_max` is
`hMax`.

The variables:
- `C`: the parameters; `n`: the node state; `J₀`: the block;
- `hH`: the node's cache of the greatest chain-state height is `hMax`.

Read aloud: when the cache is the greatest chain-state height, the spec's model has the landed
`BoxTwo`. -/
theorem goldilocks_BoxTwo (C : Config) (n : NodeState V) (J₀ : Block V)
    (hH : n.S.h_max = hMax (Model.goldilocks (V := V)) C n) :
    GoldilocksCorrectness.Statements.Routines.BoxTwo n.S J₀ ↔
      BoxTwo (Model.goldilocks (V := V)) C n J₀ := by
  show (n.S.h_max = n.S.h_j + 1 ∧ _) ↔ _
  rw [hH]
  exact Iff.rfl

end GoldilocksCorrectness.Record.Statements.Routines
