module
public import Goldilocks.FG.State

@[expose] public section

/-!
# The vocabulary of the frame statements

The definitions the statements about the frame the finality gadget gives the available chain
read (`FrameStatements.lean`):

- `FrameShape S ρ φ`, the root of the fork choice and the least viable height of an FG state;
- `BoxOne S`, `BoxTwo S J₀`, `BoxThree S`: the three cases of the FG state's finality caches the
  height argument distinguishes: the justified height less than `h_max − 1`; `h_max = h_j + 1`
  with the state not contested and the justified block `J₀`; the state contested.
-/

set_option autoImplicit false

open scoped DC

namespace GoldilocksCorrectness.Statements.Routines

open Goldilocks

variable {V : Type} [DecidableEq V]

/-- `FrameShape S ρ φ`: the root of the fork choice of the FG state `S` is `ρ` and its least
viable height is `φ`.

The variables:
- `S`: the FG state; `ρ`: the root; `φ`: the value of `head_height_floor` (the least chain-state height a viable block may have).

Read aloud: the fork choice of `S` is rooted at `ρ`, and a block is viable at `S` exactly when its
height is at least `φ`.

 -/
def FrameShape (S : FGState V) (ρ : Block V) (φ : Height) : Prop :=
  get_fc_root S = ρ ∧ head_height_floor S = φ

/-- `BoxOne S`: the justified height of the FG state `S` is less than `h_max − 1`.

The variables:
- `S`: the FG state.

Read aloud: `S.h_j + 1 < S.h_max`.

 -/
def BoxOne (S : FGState V) : Prop := S.h_j + 1 < S.h_max

/-- `BoxTwo S J₀`: `h_max = h_j + 1`, the FG state `S` is not contested, and its justified block
is `J₀`.

The variables:
- `S`: the FG state; `J₀`: the justified block.

Read aloud: `S.h_max = S.h_j + 1`, `fg_contest S` is false, and `S.J = J₀`.

 -/
def BoxTwo (S : FGState V) (J₀ : Block V) : Prop :=
  S.h_max = S.h_j + 1 ∧ fg_contest S = false ∧ S.J = J₀

/-- `BoxThree S`: the FG state `S` is contested.

The variables:
- `S`: the FG state.

Read aloud: `fg_contest S` is true.

 -/
def BoxThree (S : FGState V) : Prop := fg_contest S = true

end GoldilocksCorrectness.Statements.Routines
