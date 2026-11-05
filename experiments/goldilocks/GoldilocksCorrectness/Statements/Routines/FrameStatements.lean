module
public import GoldilocksCorrectness.Proofs.Routines.Frame

@[expose] public section

/-!
# The statements about the frame of a shape, the three boxes, and the walk's end

The audited statements about the frame `fg_to_ac S` the finality gadget gives the available
chain, and about where the fork choice stops, proved in
`GoldilocksCorrectness/Proofs/Routines/Frame.lean`:

- Lemma 56, `lem56_frame_of_shape`: the frame of an FG state of shape `FrameShape S ρ φ` has the
  root `ρ`, its viable blocks are those of height at least `φ`, and its viable heads are the
  accepted blocks on `ρ`'s chain from `ρ` on, of height at least `φ`; the three readers
  `frameShape_of_boxOne`, `frameShape_of_boxTwo`, `frameShape_of_boxThree` give the shape of
  each box;
- Lemma 58, `lem58_walk_end_is_viable_head`: a head the fork choice answers inside the viable
  tree is a viable head.
-/

set_option autoImplicit false

open scoped DC

open DC (DRE)

namespace GoldilocksCorrectness.Statements.Routines

open Goldilocks

variable {V : Type} [DecidableEq V]

/-! ## Lemma 56 -/

/-- **Lemma 56, the frame of a shape.** When the root of the fork choice of `S` is `ρ` and its
`head_height_floor` (the least chain-state height a viable block may have) is `φ`, the frame `fg_to_ac S` has the root `ρ`; a block is viable exactly when its height
is at least `φ`; and the viable heads are the blocks of `S`'s tree of which `S.F` and `ρ` are
ancestors (or which are `S.F`, `ρ`) and whose height is at least `φ`.

Why: `fg_to_ac` writes `get_fc_root S` as the root and filters its viable heads by the root's
ancestry and `is_viable`, which compares the height with `head_height_floor S`.

The variables:
- `S`: the FG state; `ρ`: the root; `φ`: the value of `head_height_floor`.

Read aloud: the frame of a shape is rooted at `ρ`, and its viable heads are the accepted blocks
on `ρ`'s chain, from `ρ` on, that reach `head_height_floor` equal to `φ`.

 -/
theorem lem56_frame_of_shape (S : FGState V) (ρ : Block V) (φ : Height)
    (hShape : FrameShape S ρ φ) :
    (fg_to_ac S).fc_root = ρ ∧
    (∀ B : Block V, is_viable S B = true ↔ φ ≤ (S.σ B).h) ∧
    (∀ B : Block V, B ∈ (fg_to_ac S).viable_heads ↔
      B ∈ S.T ∧ S.F.AncestorEq B ∧ ρ.AncestorEq B ∧ φ ≤ (S.σ B).h) :=
  GoldilocksCorrectness.Proofs.Routines.lem56_frame_of_shape S ρ φ hShape

/-- **Lemma 56, box 1: not contested; root `F`, `head_height_floor` equal to `h_max − 1`.** When the justified height
of `S` is less than `h_max − 1`, `S` is not contested, the root of its fork choice is its
finalized block, and its `head_height_floor` is `h_max − 1`.

Why: `fg_contest` answers false at its first test, since `h_max ≠ h_j + 1`; then `get_fc_root`
and `head_height_floor` take their second branches.

The variables:
- `S`: the FG state.

Read aloud: in box 1 the fork choice is rooted at the finalized block and a block is viable from
height `h_max − 1` on.

 -/
theorem frameShape_of_boxOne (S : FGState V) (h : BoxOne S) :
    fg_contest S = false ∧ FrameShape S S.F (S.h_max - 1) :=
  GoldilocksCorrectness.Proofs.Routines.frameShape_of_boxOne S h

/-- **Lemma 56, box 2: root `J₀`, `head_height_floor` equal to `h_max − 1`.** When `h_max = h_j + 1`, `S` is not
contested and its justified block is `J₀`, the root of its fork choice is `J₀` and its `head_height_floor` is
`h_max − 1`.

Why: the condition of `get_fc_root` holds, and `head_height_floor` takes its second branch.

The variables:
- `S`: the FG state; `J₀`: the justified block.

Read aloud: in box 2 the fork choice is rooted at the justified block `J₀` and a block is viable
from height `h_max − 1` on.

 -/
theorem frameShape_of_boxTwo (S : FGState V) (J₀ : Block V) (h : BoxTwo S J₀) :
    FrameShape S J₀ (S.h_max - 1) :=
  GoldilocksCorrectness.Proofs.Routines.frameShape_of_boxTwo S J₀ h

/-- **Lemma 56, box 3: `h_max = h_j + 1`; root `F`, `head_height_floor` equal to `h_max`.** When `S` is contested,
`h_max = h_j + 1`, the root of its fork choice is its finalized block, and its `head_height_floor` is `h_max`.

Why: `fg_contest` answers true only past its first test, which needs `h_max = h_j + 1`; the
condition of `get_fc_root` fails on `fg_contest`, and `head_height_floor` takes its first
branch.

The variables:
- `S`: the FG state.

Read aloud: in box 3 the fork choice is rooted at the finalized block and a block is viable from
height `h_max` on.

 -/
theorem frameShape_of_boxThree (S : FGState V) (h : BoxThree S) :
    S.h_max = S.h_j + 1 ∧ FrameShape S S.F S.h_max :=
  GoldilocksCorrectness.Proofs.Routines.frameShape_of_boxThree S h

/-! ## Lemma 58 -/

variable [Fintype V] [RootOrder]

/-- **Lemma 58, the walk's end in the viable tree is a viable head.** When the head the fork
choice answers, `get_head C A Φ t votes support_votes s = .ok H`, is in the viable tree of
`Φ.tree`, no two blocks of `Φ.tree` share a root, and every block between two blocks of `Φ.tree`
is in `Φ.tree`, then `H` is a viable head of `Φ`.

Why: the walk's end has no step. If `H` were not a viable head, the viable head `W` of the tree
that `H` is an ancestor of would be a strict descendant of `H`; the child `D` of `H` towards `W` is
between `H` and `W`, so in `Φ.tree` and in the viable tree; it passes the eligibility test by its
first case (its parent `H` is not a viable head); and with distinct roots a non-empty set of
eligible children has a best member, so the step from `H` would answer a block.

The variables:
- `C`: the parameters; `A`: the AC state; `Φ`: the frame; `t`: the time;
- `votes`, `support_votes`: the votes and the support votes counted; `s`: their slot;
- `H`: the head.

Read aloud: the fork choice stops at a viable head whenever it stops inside the viable tree.

 -/
theorem lem58_walk_end_is_viable_head (C : Config) (A : ACState V) (Φ : Frame V) (t : Time)
    (votes support_votes : Finset (GoldfishVote V)) (s : Slot) (H : Block V)
    (hRoots : RootsNameBlocksIn Φ.tree)
    -- every block between two blocks of `Φ.tree` (an ancestor-or-self of the second that the
    -- first is an ancestor-or-self of) is in `Φ.tree`
    (hBetween : ∀ X ∈ Φ.tree, ∀ Y ∈ Φ.tree, ∀ Z : Block V, X.AncestorEq Z → Z.AncestorEq Y →
      Z ∈ Φ.tree)
    -- the fork choice answers the head `H`
    (hHead : get_head C A Φ t votes support_votes s = .ok H)
    -- `H` is in the viable tree of `Φ.tree`
    (hIn : H ∈ viable_tree Φ Φ.tree) :
    H ∈ Φ.viable_heads :=
  GoldilocksCorrectness.Proofs.Routines.lem58_walk_end_is_viable_head C A Φ t votes
    support_votes s H hRoots hBetween hHead hIn

end GoldilocksCorrectness.Statements.Routines
