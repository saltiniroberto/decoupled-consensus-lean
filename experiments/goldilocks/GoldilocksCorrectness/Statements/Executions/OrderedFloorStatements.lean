module
public import GoldilocksCorrectness.Proofs.Executions.OrderedFloors
public import GoldilocksCorrectness.Proofs.Executions.OrderedFloorVotes

@[expose] public section

/-!
# The `head_height_floor` values (the least chain-state height a viable block may have) ordered: the voter's least viable height at least the proposer's

The audited statements of the facts about two frames whose `head_height_floor` values are ordered, proved in
`GoldilocksCorrectness/Proofs/Executions/OrderedFloors.lean`:

- `lem59le_frame`: along the path from `X` to `B`'s parent, a block that is a viable head at the
  voter `w` is one at the proposer `p`, when `head_height_floor` at `w` is at least the one at `p`;
- `lem59le_boxOne`, `lem59le_boxTwo`, `lem59le_boxThree`: the box instances of Lemma 59 with the
  two `h_max` ordered, giving the two frame shapes and the order of their `head_height_floor` values.

Each of the four has an `_at` form with the reading times parameters (`t_p` and `t_w` for
`lem59le_frame_at`, `t_w` for the three boxes); the four are its instances at the start and the
vote time of slot `s + 1`.


-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff)

open GoldilocksCorrectness.Statements.Routines (chainStateOf)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Routines (FrameShape BoxOne BoxTwo BoxThree)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **The viable heads along the path, with ordered `head_height_floor` values.** When `p`'s frame before the time
`t_p` has the root `ρ_p` and `head_height_floor` equal to `φ`, `w`'s frame before the time `t_w` has the root `ρ_w`
and `head_height_floor` equal to `φ_w`, `φ` is at most `φ_w`, `p`'s tree before `t_p` holds `B`'s parent, and `ρ_p` is `X` or an ancestor of `X`: then every block that is `X` or a
descendant of `X`, `ρ_w` or a descendant of `ρ_w`, and `B`'s parent or an ancestor of it, and that
is a viable head at `w`, is a viable head at `p`.

This is the direction "a viable head at `w` is one at `p`" of `viable_heads_agree_of_floor_eq`,
with its equality of the two `head_height_floor` values replaced by `φ ≤ φ_w`. The other direction does not hold: a
block whose chain-state height is at least `φ` and less than `φ_w` is a viable head at `p` and not
at `w`.

Why: `p`'s tree holds the block, as an ancestor of `B`'s parent, or that parent; `w`'s holds it,
as a viable head; both hold for it its own chain state (Lemma 11); its height is at least `φ_w`,
so at least `φ`; `ρ_p` is an ancestor of it through `X`, and so is `p`'s finalized block
(Lemma 46); so it is a viable head at `p` (Lemma 56).

The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `t_p`, `t_w`: the times `p`'s and `w`'s states are read;
- `X`: the block the path starts from; `B`: the block whose parent `p` holds;
- `p`, `w`: the two validators;
- `ρ_p`, `ρ_w`: the roots of `p`'s and `w`'s fork choices; `φ`, `φ_w`: their `head_height_floor` values.

Read aloud: on the path from `X` to `B`'s parent past `w`'s root, a block viable at `w` is viable
at `p`, when `head_height_floor` at `w` is at least the one at `p`.

`lem59le_frame` is its instance at `t_p := slotStart S (s + 1)`, `t_w := voteTime S (s + 1)`. -/
theorem lem59le_frame_at (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (t_p t_w : ℕ) (X B : Block V) (p w : V)
    (ρ_p ρ_w : Block V) (φ φ_w : Height)
    -- `p`'s frame before `t_p` has the root `ρ_p` and `head_height_floor` equal to `φ`
    (hShapeP : FrameShape (stateBefore x t_p p).S ρ_p φ)
    -- `w`'s frame before `t_w` has the root `ρ_w` and `head_height_floor` equal to `φ_w`
    (hShapeW : FrameShape (stateBefore x t_w w).S ρ_w φ_w)
    -- `head_height_floor` at `p` is at most the one at `w`
    (hFloorLe : φ ≤ φ_w)
    -- `p`'s tree before `t_p` holds `B`'s parent
    (hParentHeld : B.parent ∈ (stateBefore x t_p p).S.T)
    -- `ρ_p` is `X` or an ancestor of `X`
    (hRXp : ρ_p.AncestorEq X) :
    ∀ Y : Block V, X.AncestorEq Y → ρ_w.AncestorEq Y → Y.AncestorEq B.parent →
      Y ∈ (fg_to_ac (stateBefore x t_w w).S).viable_heads →
      Y ∈ (fg_to_ac (stateBefore x t_p p).S).viable_heads :=
  GoldilocksCorrectness.Proofs.Executions.lem59le_frame_at S Sched x t_p t_w X B p w ρ_p ρ_w φ φ_w
    hShapeP hShapeW hFloorLe hParentHeld hRXp

/-- **The viable heads along the path, with ordered `head_height_floor` values.** When `p`'s frame before the start
`t₁` of slot `s + 1` has the root `ρ_p` and `head_height_floor` equal to `φ`, `w`'s frame before the vote time `t₃`
of slot `s + 1` has the root `ρ_w` and `head_height_floor` equal to `φ_w`, `φ` is at most `φ_w`, `p`'s tree before
`t₁` holds `B`'s parent, and `ρ_p` is `X` or an ancestor of `X`: then every block that is `X` or a
descendant of `X`, `ρ_w` or a descendant of `ρ_w`, and `B`'s parent or an ancestor of it, and that
is a viable head at `w`, is a viable head at `p`.

This is the direction "a viable head at `w` is one at `p`" of `viable_heads_agree_of_floor_eq`,
with its equality of the two `head_height_floor` values replaced by `φ ≤ φ_w`. The other direction does not hold: a
block whose chain-state height is at least `φ` and less than `φ_w` is a viable head at `p` and not
at `w`.

Why: `p`'s tree holds the block, as an ancestor of `B`'s parent, or that parent; `w`'s holds it,
as a viable head; both hold for it its own chain state (Lemma 11); its height is at least `φ_w`,
so at least `φ`; `ρ_p` is an ancestor of it through `X`, and so is `p`'s finalized block
(Lemma 46); so it is a viable head at `p` (Lemma 56).

The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution; `s`: the slot of the votes;
- `X`: the block the slot-`s` majority extends; `B`: the block `p` proposed at `t₁`;
- `p`: the proposer of slot `s + 1`; `w`: the voter of slot `s + 1`;
- `ρ_p`, `ρ_w`: the roots of `p`'s and `w`'s fork choices; `φ`, `φ_w`: their `head_height_floor` values.

Read aloud: on the path from `X` to `B`'s parent past `w`'s root, a block viable at `w` is viable
at `p`, when `head_height_floor` at `w` is at least the one at `p`.



It is the instance of `lem59le_frame_at` at `t_p := slotStart S (s + 1)`,
`t_w := voteTime S (s + 1)`. -/
theorem lem59le_frame (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s : ℕ) (X B : Block V) (p w : V)
    (ρ_p ρ_w : Block V) (φ φ_w : Height)
    -- `p`'s frame before `t₁` has the root `ρ_p` and `head_height_floor` equal to `φ`
    (hShapeP : FrameShape (stateBefore x (slotStart S (s + 1)) p).S ρ_p φ)
    -- `w`'s frame before `t₃` has the root `ρ_w` and `head_height_floor` equal to `φ_w`
    (hShapeW : FrameShape (stateBefore x (voteTime S (s + 1)) w).S ρ_w φ_w)
    -- `head_height_floor` at `p` is at most the one at `w`
    (hFloorLe : φ ≤ φ_w)
    -- `p`'s tree before `t₁` holds `B`'s parent
    (hParentHeld : B.parent ∈ (stateBefore x (slotStart S (s + 1)) p).S.T)
    -- `ρ_p` is `X` or an ancestor of `X`
    (hRXp : ρ_p.AncestorEq X) :
    ∀ Y : Block V, X.AncestorEq Y → ρ_w.AncestorEq Y → Y.AncestorEq B.parent →
      Y ∈ (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).viable_heads →
      Y ∈ (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).viable_heads :=
  lem59le_frame_at S Sched x (slotStart S (s + 1)) (voteTime S (s + 1)) X B p w ρ_p ρ_w φ φ_w
    hShapeP hShapeW hFloorLe hParentHeld hRXp

/-- **Lemma 59 in box 1, with ordered `h_max`.** When `p`'s state before the start `t₁` of slot
`s + 1` and `w`'s before the time `t_w` are both in box 1, `p`'s `h_max` is at
most `w`'s, `w`'s finalized block is `B` or an ancestor of `B`, `p` put `B` on the wire at its
tick at `t₁` with `B`'s parent in `p`'s viable tree, and some block of `p`'s tree on `p`'s
finalized block's chain, `X` or a descendant of `X`, has a chain-state height at least `p`'s
`h_max − 1`: then `p`'s frame has the root `p`'s finalized block and `head_height_floor` equal to `p`'s `h_max − 1`,
`w`'s has the root `w`'s finalized block and `head_height_floor` equal to `w`'s `h_max − 1`, the first `head_height_floor` value is at
most the second, and `B`'s chain-state height is at least the first.

Why: box 1 has the finalized block as its root and `h_max − 1` as its `head_height_floor` (Lemma 56); the
ordered `h_max` give ordered `head_height_floor` values; the honest proposal reaches `head_height_floor` at its proposer
(`proposal_viable`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the slot before the proposal's;
- `X`: the block every honest slot-`s` vote extends; `B`: the block `p` proposed;
- `p`: the proposer of slot `s + 1`; `w`: the voter of slot `s + 1`;
- `t_w`: the time `w`'s state is read.

Read aloud: in box 1 the `head_height_floor` values are `h_max − 1` at both states, ordered as the two `h_max`, and the
honest proposal reaches `p`'s.

`lem59le_boxOne` is its instance at `t_w := voteTime S (s + 1)`. -/
theorem lem59le_boxOne_at (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s t_w : ℕ) (X B : Block V) (p w : V)
    -- `p`'s state before `t₁` is in box 1
    (hBoxP : BoxOne (stateBefore x (slotStart S (s + 1)) p).S)
    -- `w`'s state before `t_w` is in box 1
    (hBoxW : BoxOne (stateBefore x t_w w).S)
    -- `p`'s `h_max` before `t₁` is at most `w`'s before `t_w`
    (hHmaxLe : (stateBefore x (slotStart S (s + 1)) p).S.h_max ≤
      (stateBefore x t_w w).S.h_max)
    -- `w`'s finalized block before `t_w` is `B` or an ancestor of `B`
    (hFw : (stateBefore x t_w w).S.F.AncestorEq B)
    -- `p`'s tick at `t₁` put `B` on the wire
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    -- `B`'s parent is in the viable tree of `p`'s frame before `t₁`
    (hParentIn : B.parent ∈ viable_tree (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S)
      (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).tree)
    -- some accepted block of `p` on its finalized block's chain, `X` or a descendant of `X`,
    -- has a chain-state height at least `p`'s `h_max − 1`
    (hHeadP : ∃ W ∈ (stateBefore x (slotStart S (s + 1)) p).S.T,
      X.AncestorEq W ∧ (stateBefore x (slotStart S (s + 1)) p).S.F.AncestorEq W ∧
        (stateBefore x (slotStart S (s + 1)) p).S.h_max - 1 ≤ (chainStateOf S.C W).h) :
    FrameShape (stateBefore x (slotStart S (s + 1)) p).S
        (stateBefore x (slotStart S (s + 1)) p).S.F
        ((stateBefore x (slotStart S (s + 1)) p).S.h_max - 1) ∧
      FrameShape (stateBefore x t_w w).S
        (stateBefore x t_w w).S.F
        ((stateBefore x t_w w).S.h_max - 1) ∧
      (stateBefore x (slotStart S (s + 1)) p).S.h_max - 1 ≤
        (stateBefore x t_w w).S.h_max - 1 ∧
      (stateBefore x t_w w).S.F.AncestorEq B ∧
      (∃ W ∈ (stateBefore x (slotStart S (s + 1)) p).S.T,
        X.AncestorEq W ∧ (stateBefore x (slotStart S (s + 1)) p).S.F.AncestorEq W ∧
          (stateBefore x (slotStart S (s + 1)) p).S.h_max - 1 ≤ (chainStateOf S.C W).h) ∧
      (stateBefore x (slotStart S (s + 1)) p).S.h_max - 1 ≤ (chainStateOf S.C B).h :=
  GoldilocksCorrectness.Proofs.Executions.lem59le_boxOne_at S Sched x s t_w X B p w hBoxP hBoxW
    hHmaxLe hFw hPropose hParentIn hHeadP

/-- **Lemma 59 in box 1, with ordered `h_max`.** When `p`'s state before the start `t₁` of slot
`s + 1` and `w`'s before the vote time `t₃` of slot `s + 1` are both in box 1, `p`'s `h_max` is at
most `w`'s, `w`'s finalized block is `B` or an ancestor of `B`, `p` put `B` on the wire at its
tick at `t₁` with `B`'s parent in `p`'s viable tree, and some block of `p`'s tree on `p`'s
finalized block's chain, `X` or a descendant of `X`, has a chain-state height at least `p`'s
`h_max − 1`: then `p`'s frame has the root `p`'s finalized block and `head_height_floor` equal to `p`'s `h_max − 1`,
`w`'s has the root `w`'s finalized block and `head_height_floor` equal to `w`'s `h_max − 1`, the first `head_height_floor` value is at
most the second, and `B`'s chain-state height is at least the first.

This is `lem59_boxOne` with its hypothesis "the two states have the same `h_max`" replaced by
"`p`'s `h_max` is at most `w`'s".

Why: box 1 has the finalized block as its root and `h_max − 1` as its `head_height_floor` (Lemma 56); the
ordered `h_max` give ordered `head_height_floor` values; the honest proposal reaches `head_height_floor` at its proposer
(`proposal_viable`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the slot before the proposal's;
- `X`: the block every honest slot-`s` vote extends; `B`: the block `p` proposed;
- `p`: the proposer of slot `s + 1`; `w`: the voter of slot `s + 1`.

Read aloud: in box 1 the `head_height_floor` values are `h_max − 1` at both states, ordered as the two `h_max`, and the
honest proposal reaches `p`'s.



It is the instance of `lem59le_boxOne_at` at `t_w := voteTime S (s + 1)`. -/
theorem lem59le_boxOne (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s : ℕ) (X B : Block V) (p w : V)
    -- `p`'s state before `t₁` is in box 1
    (hBoxP : BoxOne (stateBefore x (slotStart S (s + 1)) p).S)
    -- `w`'s state before `t₃` is in box 1
    (hBoxW : BoxOne (stateBefore x (voteTime S (s + 1)) w).S)
    -- `p`'s `h_max` before `t₁` is at most `w`'s before `t₃`
    (hHmaxLe : (stateBefore x (slotStart S (s + 1)) p).S.h_max ≤
      (stateBefore x (voteTime S (s + 1)) w).S.h_max)
    -- `w`'s finalized block before `t₃` is `B` or an ancestor of `B`
    (hFw : (stateBefore x (voteTime S (s + 1)) w).S.F.AncestorEq B)
    -- `p`'s tick at `t₁` put `B` on the wire
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    -- `B`'s parent is in the viable tree of `p`'s frame before `t₁`
    (hParentIn : B.parent ∈ viable_tree (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S)
      (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).tree)
    -- some accepted block of `p` on its finalized block's chain, `X` or a descendant of `X`,
    -- has a chain-state height at least `p`'s `h_max − 1`
    (hHeadP : ∃ W ∈ (stateBefore x (slotStart S (s + 1)) p).S.T,
      X.AncestorEq W ∧ (stateBefore x (slotStart S (s + 1)) p).S.F.AncestorEq W ∧
        (stateBefore x (slotStart S (s + 1)) p).S.h_max - 1 ≤ (chainStateOf S.C W).h) :
    FrameShape (stateBefore x (slotStart S (s + 1)) p).S
        (stateBefore x (slotStart S (s + 1)) p).S.F
        ((stateBefore x (slotStart S (s + 1)) p).S.h_max - 1) ∧
      FrameShape (stateBefore x (voteTime S (s + 1)) w).S
        (stateBefore x (voteTime S (s + 1)) w).S.F
        ((stateBefore x (voteTime S (s + 1)) w).S.h_max - 1) ∧
      (stateBefore x (slotStart S (s + 1)) p).S.h_max - 1 ≤
        (stateBefore x (voteTime S (s + 1)) w).S.h_max - 1 ∧
      (stateBefore x (voteTime S (s + 1)) w).S.F.AncestorEq B ∧
      (∃ W ∈ (stateBefore x (slotStart S (s + 1)) p).S.T,
        X.AncestorEq W ∧ (stateBefore x (slotStart S (s + 1)) p).S.F.AncestorEq W ∧
          (stateBefore x (slotStart S (s + 1)) p).S.h_max - 1 ≤ (chainStateOf S.C W).h) ∧
      (stateBefore x (slotStart S (s + 1)) p).S.h_max - 1 ≤ (chainStateOf S.C B).h :=
  lem59le_boxOne_at S Sched x s (voteTime S (s + 1)) X B p w hBoxP hBoxW hHmaxLe hFw hPropose
    hParentIn hHeadP

/-- **Lemma 59 in box 2, with the voter in box 2 or contested.** When `p`'s state before the start
`t₁` of slot `s + 1` is in box 2 with the justified block `J₀`, and `w`'s before the time `t_w` is in box 2 with `J₀`, other than the genesis block, or is contested with `p`'s
`h_max` and its finalized block `B` or an ancestor of `B`; and `p` put `B` on the wire at its tick
at `t₁` with `B`'s parent in `p`'s viable tree: then `p`'s frame has the root `J₀` and `head_height_floor` equal to
`p`'s `h_max − 1`, `w`'s frame has a root that is `B` or an ancestor of `B` and a `head_height_floor` value at least
`p`'s, `J₀` is `B`'s parent or an ancestor of it, and `B`'s chain-state height is at least
`head_height_floor` at `p`.

Why: box 2 has `J₀` as its root and `h_max − 1` as its `head_height_floor` (Lemma 56); when `w` is in box 2 with
`J₀`, the two `h_max` are `J₀`'s chain-state height plus one (Lemma 57), so the `head_height_floor` values are equal,
and `J₀` is an ancestor of `B` through `B`'s parent, which the viable tree places past the root;
when `w` is contested, its root is its finalized block and its `head_height_floor` its `h_max` (Lemma 56), which
is `p`'s; the honest proposal reaches `head_height_floor` at its proposer (`proposal_viable`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the slot before the proposal's;
- `B`: the block `p` proposed; `J₀`: the justified block;
- `p`: the proposer of slot `s + 1`; `w`: the voter of slot `s + 1`;
- `t_w`: the time `w`'s state is read.

Read aloud: with `p` in box 2, `head_height_floor` at the voter is the one at `p` when it is in box 2 with the same
justified block, and one more when it is contested with the same `h_max`; either way its root is
on `B`'s chain.

`lem59le_boxTwo` is its instance at `t_w := voteTime S (s + 1)`. -/
theorem lem59le_boxTwo_at (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s t_w : ℕ) (B J₀ : Block V) (p w : V)
    -- `p`'s state before `t₁` is in box 2 with the justified block `J₀`
    (hBoxP : BoxTwo (stateBefore x (slotStart S (s + 1)) p).S J₀)
    -- `w`'s state before `t_w` is in box 2 with `J₀`, and `J₀` is not the genesis block; or it is
    -- contested, with `p`'s `h_max`, and its finalized block is `B` or an ancestor of `B`
    (hBoxW : (BoxTwo (stateBefore x t_w w).S J₀ ∧ J₀ ≠ Block.genesis) ∨
      (BoxThree (stateBefore x t_w w).S ∧
        (stateBefore x (slotStart S (s + 1)) p).S.h_max =
          (stateBefore x t_w w).S.h_max ∧
        (stateBefore x t_w w).S.F.AncestorEq B))
    -- `p`'s tick at `t₁` put `B` on the wire
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    -- `B`'s parent is in the viable tree of `p`'s frame before `t₁`
    (hParentIn : B.parent ∈ viable_tree (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S)
      (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).tree) :
    FrameShape (stateBefore x (slotStart S (s + 1)) p).S J₀
        ((stateBefore x (slotStart S (s + 1)) p).S.h_max - 1) ∧
      (∃ ρ_w : Block V, ∃ φ_w : Height,
        FrameShape (stateBefore x t_w w).S ρ_w φ_w ∧
        (stateBefore x (slotStart S (s + 1)) p).S.h_max - 1 ≤ φ_w ∧ ρ_w.AncestorEq B) ∧
      J₀.AncestorEq B.parent ∧
      (stateBefore x (slotStart S (s + 1)) p).S.h_max - 1 ≤ (chainStateOf S.C B).h :=
  GoldilocksCorrectness.Proofs.Executions.lem59le_boxTwo_at S Sched x s t_w B J₀ p w hBoxP hBoxW
    hPropose hParentIn

/-- **Lemma 59 in box 2, with the voter in box 2 or contested.** When `p`'s state before the start
`t₁` of slot `s + 1` is in box 2 with the justified block `J₀`, and `w`'s before the vote time `t₃`
of slot `s + 1` is in box 2 with `J₀`, other than the genesis block, or is contested with `p`'s
`h_max` and its finalized block `B` or an ancestor of `B`; and `p` put `B` on the wire at its tick
at `t₁` with `B`'s parent in `p`'s viable tree: then `p`'s frame has the root `J₀` and `head_height_floor` equal to
`p`'s `h_max − 1`, `w`'s frame has a root that is `B` or an ancestor of `B` and a `head_height_floor` value at least
`p`'s, `J₀` is `B`'s parent or an ancestor of it, and `B`'s chain-state height is at least
`head_height_floor` at `p`.

This is `lem59_boxTwo` with `w`'s state allowed to be contested with `p`'s `h_max`, in which case
its `head_height_floor` is the one at `p` plus one.

Why: box 2 has `J₀` as its root and `h_max − 1` as its `head_height_floor` (Lemma 56); when `w` is in box 2 with
`J₀`, the two `h_max` are `J₀`'s chain-state height plus one (Lemma 57), so the `head_height_floor` values are equal,
and `J₀` is an ancestor of `B` through `B`'s parent, which the viable tree places past the root;
when `w` is contested, its root is its finalized block and its `head_height_floor` its `h_max` (Lemma 56), which
is `p`'s; the honest proposal reaches `head_height_floor` at its proposer (`proposal_viable`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the slot before the proposal's;
- `B`: the block `p` proposed; `J₀`: the justified block;
- `p`: the proposer of slot `s + 1`; `w`: the voter of slot `s + 1`.

Read aloud: with `p` in box 2, `head_height_floor` at the voter is the one at `p` when it is in box 2 with the same
justified block, and one more when it is contested with the same `h_max`; either way its root is
on `B`'s chain.



It is the instance of `lem59le_boxTwo_at` at `t_w := voteTime S (s + 1)`. -/
theorem lem59le_boxTwo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s : ℕ) (B J₀ : Block V) (p w : V)
    -- `p`'s state before `t₁` is in box 2 with the justified block `J₀`
    (hBoxP : BoxTwo (stateBefore x (slotStart S (s + 1)) p).S J₀)
    -- `w`'s state before `t₃` is in box 2 with `J₀`, and `J₀` is not the genesis block; or it is
    -- contested, with `p`'s `h_max`, and its finalized block is `B` or an ancestor of `B`
    (hBoxW : (BoxTwo (stateBefore x (voteTime S (s + 1)) w).S J₀ ∧ J₀ ≠ Block.genesis) ∨
      (BoxThree (stateBefore x (voteTime S (s + 1)) w).S ∧
        (stateBefore x (slotStart S (s + 1)) p).S.h_max =
          (stateBefore x (voteTime S (s + 1)) w).S.h_max ∧
        (stateBefore x (voteTime S (s + 1)) w).S.F.AncestorEq B))
    -- `p`'s tick at `t₁` put `B` on the wire
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    -- `B`'s parent is in the viable tree of `p`'s frame before `t₁`
    (hParentIn : B.parent ∈ viable_tree (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S)
      (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).tree) :
    FrameShape (stateBefore x (slotStart S (s + 1)) p).S J₀
        ((stateBefore x (slotStart S (s + 1)) p).S.h_max - 1) ∧
      (∃ ρ_w : Block V, ∃ φ_w : Height,
        FrameShape (stateBefore x (voteTime S (s + 1)) w).S ρ_w φ_w ∧
        (stateBefore x (slotStart S (s + 1)) p).S.h_max - 1 ≤ φ_w ∧ ρ_w.AncestorEq B) ∧
      J₀.AncestorEq B.parent ∧
      (stateBefore x (slotStart S (s + 1)) p).S.h_max - 1 ≤ (chainStateOf S.C B).h :=
  lem59le_boxTwo_at S Sched x s (voteTime S (s + 1)) B J₀ p w hBoxP hBoxW hPropose hParentIn

/-- **Lemma 59 in box 3, with ordered `h_max`.** When `p`'s state before the start `t₁` of slot
`s + 1` and `w`'s before the time `t_w` are both contested, `p`'s `h_max` is at
most `w`'s, `w`'s finalized block is `B` or an ancestor of `B`, and `p` put `B` on the wire at its
tick at `t₁` with `B`'s parent in `p`'s viable tree: then `p`'s frame has the root `p`'s finalized
block and `head_height_floor` equal to `p`'s `h_max`, `w`'s has the root `w`'s finalized block and `head_height_floor` equal to `w`'s
`h_max`, the first `head_height_floor` value is at most the second, and `B`'s chain-state height is at least the
first.

Why: box 3 has the finalized block as its root and `h_max` as its `head_height_floor` (Lemma 56); the honest
proposal reaches `head_height_floor` at its proposer (`proposal_viable`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the slot before the proposal's;
- `B`: the block `p` proposed;
- `p`: the proposer of slot `s + 1`; `w`: the voter of slot `s + 1`;
- `t_w`: the time `w`'s state is read.

Read aloud: in box 3 the `head_height_floor` values are the two `h_max`, ordered, and the honest proposal reaches
`p`'s.

`lem59le_boxThree` is its instance at `t_w := voteTime S (s + 1)`. -/
theorem lem59le_boxThree_at (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s t_w : ℕ) (B : Block V) (p w : V)
    -- `p`'s state before `t₁` is contested
    (hBoxP : BoxThree (stateBefore x (slotStart S (s + 1)) p).S)
    -- `w`'s state before `t_w` is contested
    (hBoxW : BoxThree (stateBefore x t_w w).S)
    -- `p`'s `h_max` before `t₁` is at most `w`'s before `t_w`
    (hHmaxLe : (stateBefore x (slotStart S (s + 1)) p).S.h_max ≤
      (stateBefore x t_w w).S.h_max)
    -- `w`'s finalized block before `t_w` is `B` or an ancestor of `B`
    (hFw : (stateBefore x t_w w).S.F.AncestorEq B)
    -- `p`'s tick at `t₁` put `B` on the wire
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    -- `B`'s parent is in the viable tree of `p`'s frame before `t₁`
    (hParentIn : B.parent ∈ viable_tree (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S)
      (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).tree) :
    FrameShape (stateBefore x (slotStart S (s + 1)) p).S
        (stateBefore x (slotStart S (s + 1)) p).S.F
        (stateBefore x (slotStart S (s + 1)) p).S.h_max ∧
      FrameShape (stateBefore x t_w w).S
        (stateBefore x t_w w).S.F
        (stateBefore x t_w w).S.h_max ∧
      (stateBefore x (slotStart S (s + 1)) p).S.h_max ≤
        (stateBefore x t_w w).S.h_max ∧
      (stateBefore x t_w w).S.F.AncestorEq B ∧
      (stateBefore x (slotStart S (s + 1)) p).S.h_max ≤ (chainStateOf S.C B).h :=
  GoldilocksCorrectness.Proofs.Executions.lem59le_boxThree_at S Sched x s t_w B p w hBoxP hBoxW
    hHmaxLe hFw hPropose hParentIn

/-- **Lemma 59 in box 3, with ordered `h_max`.** When `p`'s state before the start `t₁` of slot
`s + 1` and `w`'s before the vote time `t₃` of slot `s + 1` are both contested, `p`'s `h_max` is at
most `w`'s, `w`'s finalized block is `B` or an ancestor of `B`, and `p` put `B` on the wire at its
tick at `t₁` with `B`'s parent in `p`'s viable tree: then `p`'s frame has the root `p`'s finalized
block and `head_height_floor` equal to `p`'s `h_max`, `w`'s has the root `w`'s finalized block and `head_height_floor` equal to `w`'s
`h_max`, the first `head_height_floor` value is at most the second, and `B`'s chain-state height is at least the
first.

This is `lem59_boxThree` with its hypothesis "the two states have the same `h_max`" replaced by
"`p`'s `h_max` is at most `w`'s".

Why: box 3 has the finalized block as its root and `h_max` as its `head_height_floor` (Lemma 56); the honest
proposal reaches `head_height_floor` at its proposer (`proposal_viable`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the slot before the proposal's;
- `B`: the block `p` proposed;
- `p`: the proposer of slot `s + 1`; `w`: the voter of slot `s + 1`.

Read aloud: in box 3 the `head_height_floor` values are the two `h_max`, ordered, and the honest proposal reaches
`p`'s.



It is the instance of `lem59le_boxThree_at` at `t_w := voteTime S (s + 1)`. -/
theorem lem59le_boxThree (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s : ℕ) (B : Block V) (p w : V)
    -- `p`'s state before `t₁` is contested
    (hBoxP : BoxThree (stateBefore x (slotStart S (s + 1)) p).S)
    -- `w`'s state before `t₃` is contested
    (hBoxW : BoxThree (stateBefore x (voteTime S (s + 1)) w).S)
    -- `p`'s `h_max` before `t₁` is at most `w`'s before `t₃`
    (hHmaxLe : (stateBefore x (slotStart S (s + 1)) p).S.h_max ≤
      (stateBefore x (voteTime S (s + 1)) w).S.h_max)
    -- `w`'s finalized block before `t₃` is `B` or an ancestor of `B`
    (hFw : (stateBefore x (voteTime S (s + 1)) w).S.F.AncestorEq B)
    -- `p`'s tick at `t₁` put `B` on the wire
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    -- `B`'s parent is in the viable tree of `p`'s frame before `t₁`
    (hParentIn : B.parent ∈ viable_tree (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S)
      (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).tree) :
    FrameShape (stateBefore x (slotStart S (s + 1)) p).S
        (stateBefore x (slotStart S (s + 1)) p).S.F
        (stateBefore x (slotStart S (s + 1)) p).S.h_max ∧
      FrameShape (stateBefore x (voteTime S (s + 1)) w).S
        (stateBefore x (voteTime S (s + 1)) w).S.F
        (stateBefore x (voteTime S (s + 1)) w).S.h_max ∧
      (stateBefore x (slotStart S (s + 1)) p).S.h_max ≤
        (stateBefore x (voteTime S (s + 1)) w).S.h_max ∧
      (stateBefore x (voteTime S (s + 1)) w).S.F.AncestorEq B ∧
      (stateBefore x (slotStart S (s + 1)) p).S.h_max ≤ (chainStateOf S.C B).h :=
  lem59le_boxThree_at S Sched x s (voteTime S (s + 1)) B p w hBoxP hBoxW hHmaxLe hFw hPropose
    hParentIn

/-! ## Lemmas 20, 24 and 59 with `head_height_floor` at `p` at most at `w`

The audited statements of Lemmas 20, 24 and 59 when `head_height_floor` at the proposer `p` (its FG
state before the start `t₁` of slot `s + 1`) is at most `head_height_floor` at the voter `w` (its
FG state before the vote time `t₃` of slot `s + 1`), each with a hypothesis on `B`'s parent in place
of the same hypothesis on `B`, proved in
`GoldilocksCorrectness/Proofs/Executions/OrderedFloorVotes.lean`:

- `lem20le_goldfish_vote_names_honest_proposal`: along the path, a viable head at `w` is one at
  `p`, and `B`'s parent is a viable head at `w` when it is one at `p`;
- `lem24le_goldfish_vote_names_honest_proposal_composed`: `B`'s parent passes `w`'s viability
  test;
- `lem59le_goldfish_vote_names_honest_proposal_frame`: `head_height_floor` at `w` is at most the
  chain-state height of `B`'s parent.


-/

open GoldilocksCorrectness.Statements.Routines (expireLocks CountedVotes ProposalCountedVotes)

/-- **Lemma 20 with `head_height_floor` at `p` at most at `w`.** Under the hypotheses of Lemma 20
(`lem20_goldfish_vote_names_honest_proposal`) other than its agreement of the viable heads, and:
along the path from `X` to `B`'s parent, on the blocks that have the root of `w`'s fork choice as
an ancestor (or are that root), a viable head at `w` is a viable head at `p`; and `B`'s parent,
when the root of `w`'s fork choice is an ancestor of it (or it), is a viable head at `w` when it is
one at `p` — then `w`'s vote names `B`.

Why: as Lemma 20. From the shared block on, the two walks see the same scores; on a child of a
path block that is a viable head at `w`, the two eligibility tests agree; on a child of a path
block that is not a viable head at `w`, `w`'s test accepts it; so `w`'s test accepts every block
`p`'s accepts, and Lemma 9 with ordered tests (`lem9le_walk_ends_at_proposal_of_shared_block`)
ends `w`'s walk at `B`. At `B`'s parent, a child `w` accepts and `p` refuses would need `B`'s
parent viable at `p` and not at `w`, which the last hypothesis excludes.

The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s`: the slot of the votes;
- `Hs`: the honest voters of slot `s`; `H`: the block each voter's vote is for;
- `X`: the block every vote of `Hs` extends; `B`: the block `p` proposed at the start of slot
  `s + 1`;
- `p`: the proposer of slot `s + 1`; `w`: the voter of slot `s + 1`;
- `vote`: the Goldfish vote `w` sent at the vote time of slot `s + 1`.

Read aloud: Lemma 20 holds when, along the path from `X` to `B`'s parent past the root of `w`'s
fork choice, every viable head at `w` is one at `p`, and `B`'s parent, if a viable head at `p`, is
one at `w`.



Roots name blocks until `supportCutoff S s`: the bound of the two Lemma 12 calls at slot `s` the
proof passes the premise to, as Lemma 20's. -/
theorem lem20le_goldfish_vote_names_honest_proposal (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s : ℕ) (Hs : Finset V) (H : V → Block V)
    (X B : Block V) (p w : V) (vote : GoldfishVote V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S s))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    (hGST : GST ≤ voteTime S s)
    -- the slot-`s` votes of `Hs` for `X`
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ Sched.adv (voteTime S (s + 1) : Int) ∧
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      H u ∈ (stateBefore x (voteTime S s) u).S.T ∧ X.AncestorEq (H u))
    -- the validators with a vote among those `w`'s slot-`(s + 1)` vote counts are fewer than
    -- twice `Hs`
    (hVoters : ∀ votes_w support_w : Finset (GoldfishVote V),
      CountedVotes S.C (stateBefore x (voteTime S (s + 1)) w).A
        (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) (s + 1) votes_w support_w →
      voters_count votes_w < 2 * Hs.card)
    -- the proposer `p` and the voter `w` are awake and honest from the vote time of slot `s` to
    -- its support cutoff
    (hp : ∀ t : ℕ, voteTime S s ≤ t → t ≤ supportCutoff S s →
      p ∈ Sched.awake (t : Int) ∧ p ∉ Sched.adv (t : Int))
    (hw : ∀ t : ℕ, voteTime S s ≤ t → t ≤ supportCutoff S s →
      w ∈ Sched.awake (t : Int) ∧ w ∉ Sched.adv (t : Int))
    -- `p`'s tick at `t₁` put `B` on the wire
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    -- `w`'s tick at `t₃` put `vote` on the wire
    (hSend : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (s + 1)) ∧
      (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent)
    -- `w` holds `B` before its vote
    (hBw : B ∈ (stateBefore x (voteTime S (s + 1)) w).S.T)
    -- some block of `p`'s frame tree before `t₁` that is `X` or a descendant of `X` is a viable
    -- head
    (hF3p : ∃ W ∈ (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).tree,
      W ∈ (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).viable_heads ∧ X.AncestorEq W)
    -- `p`'s anchor is `X` or an ancestor of `X`
    (hApX : (get_anchor (stateBefore x (slotStart S (s + 1)) p).A
      (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S)
      ((slotStart S (s + 1) : ℕ) : Int)).AncestorEq X)
    -- every live lock entry `w`'s revocation leaves is on `B` or an ancestor of `B`
    (hLocksW : ∀ A' : ACState V,
      revoke_locks S.P (expireLocks (stateBefore x (voteTime S (s + 1)) w).A
        ((voteTime S (s + 1) : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
        ((voteTime S (s + 1) : ℕ) : Int) (s + 1) = .ok A' →
      ∀ e ∈ A'.lock_entries,
        is_live (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
          ((voteTime S (s + 1) : ℕ) : Int) e = true → e.B.AncestorEq B)
    -- `B` is a viable head at `w`
    (hBViable : B ∈ (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).viable_heads)
    -- along the path from `X` to `B`'s parent, on the blocks that have the root of `w`'s fork
    -- choice as an ancestor (or are that root), a viable head at `w` is one at `p`
    (hViableLe : ∀ Y : Block V, X.AncestorEq Y →
      (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).fc_root.AncestorEq Y →
      Y.AncestorEq B.parent →
      Y ∈ (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).viable_heads →
      Y ∈ (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).viable_heads)
    -- `B`'s parent, when the root of `w`'s fork choice is an ancestor of it (or it), is a viable
    -- head at `w` when it is one at `p`
    (hViableEnd : (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).fc_root.AncestorEq B.parent →
      B.parent ∈ (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).viable_heads →
      B.parent ∈ (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).viable_heads)
    -- the two validators count alike: the same score on every child of a block from `X` to
    -- `B`'s parent that has the root of `w`'s fork choice as an ancestor (or is that root), the
    -- same number of voters
    (hCount : ∀ votes_p support_p votes_w support_w : Finset (GoldfishVote V),
      ProposalCountedVotes (stateBefore x (slotStart S (s + 1)) p).A
        (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S) s votes_p support_p →
      CountedVotes S.C (stateBefore x (voteTime S (s + 1)) w).A
        (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) (s + 1) votes_w support_w →
      (∀ Y : Block V, X.AncestorEq Y →
        (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).fc_root.AncestorEq Y →
        Y.AncestorEq B.parent →
        ∀ D : Block V, D.parent? = some Y → ∃ n : ℕ,
          goldfish_score (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S) votes_p support_p s
            D = .ok n ∧
          goldfish_score (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) votes_w support_w s
            D = .ok n) ∧
      voters_count votes_p = voters_count votes_w)
    -- every child in `w`'s viable tree of a block from `X` to `B`'s parent that has the root of
    -- `w`'s fork choice as an ancestor (or is that root), other than `B`, that `w`'s eligibility
    -- test accepts, is in `p`'s viable tree
    (hChild : ∀ (vbt : Finset (Block V)) (votes_w support_w : Finset (GoldfishVote V)),
      voter_block_tree S.C (stateBefore x (voteTime S (s + 1)) w).A
        (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) (s + 1) = .ok vbt →
      CountedVotes S.C (stateBefore x (voteTime S (s + 1)) w).A
        (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) (s + 1) votes_w support_w →
      ∀ Y : Block V, X.AncestorEq Y →
        (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).fc_root.AncestorEq Y →
        Y.AncestorEq B.parent →
        ∀ D ∈ viable_tree (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) vbt,
          D.parent? = some Y → D ≠ B →
          goldfish_eligible S.C (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
            ((voteTime S (s + 1) : ℕ) : Int) votes_w support_w s D = .ok true →
          D ∈ viable_tree (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S)
            (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).tree) :
    vote.head = B.root :=
  GoldilocksCorrectness.Proofs.Executions.lem20le_goldfish_vote_names_honest_proposal S Sched x
    GST s Hs H X B p w vote hDiv hMono hSync hCatch hRoots hParent hOwner hGST hHs hVoters
    hp hw hPropose hSend hBw hF3p hApX hLocksW hBViable hViableLe hViableEnd hCount hChild

/-- **Lemma 24 with `head_height_floor` at `p` at most at `w`.** Under the hypotheses of Lemma 24
(`lem24_goldfish_vote_names_honest_proposal_composed`) other than "`B` passes `w`'s viability
test" and "`head_height_floor` at `p` equals `head_height_floor` at `w`", and: `B`'s parent passes
`w`'s viability test (`is_viable`: its chain-state height is at least `head_height_floor` at `w`);
and `head_height_floor` at `p` is at most `head_height_floor` at `w` — then `vote`'s head is the
root of `B`.

Why: as Lemma 24, with Lemma 20 in the form `lem20le_goldfish_vote_names_honest_proposal`. `w`
holds `B` (Lemmas 22a and 22) and so `B`'s parent; both have their own chain states (Lemma 11),
and heights grow along ancestry (Lemma 47 (d)), so `B` passes `w`'s viability test too and is a
viable head at `w`. Along the path, a viable head at `w` reaches `head_height_floor` at `w`, so at
`p`, and is one at `p`; `B`'s parent is a viable head at `w` whenever the root of `w`'s fork choice
is an ancestor of it.

The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s`: the slot of the votes;
- `Hs`: the honest voters of slot `s`; `H`: the block each voter's vote is for;
- `X`: the block every vote of `Hs` extends; `B`: the block `p` proposed at the start of slot
  `s + 1`;
- `p`: the proposer of slot `s + 1`; `w`: the voter of slot `s + 1`;
- `vote`: the Goldfish vote `w` sent at the vote time of slot `s + 1`.

Read aloud: Lemma 24 holds when `head_height_floor` at the voter is at least at the proposer, and
the proposal's parent passes the voter's viability test.



Roots name blocks until `voteTime S (s + 1)`: Lemma 22 and Lemma 23, which the proof calls, take
blocks as held up to `w`'s vote time of slot `s + 1`;
`lem20le_goldfish_vote_names_honest_proposal` and `child_mem_proposer_viable_tree` read earlier. -/
theorem lem24le_goldfish_vote_names_honest_proposal_composed (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s : ℕ) (Hs : Finset V) (H : V → Block V)
    (X B : Block V) (p w : V) (vote : GoldfishVote V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (voteTime S (s + 1)))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    (hGST : GST ≤ voteTime S s)
    -- the slot-`s` votes of `Hs` for `X`
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ Sched.adv (voteTime S (s + 1) : Int) ∧
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      H u ∈ (stateBefore x (voteTime S s) u).S.T ∧ X.AncestorEq (H u))
    -- the validators with a vote among those `w`'s slot-`(s + 1)` vote counts are fewer than
    -- twice `Hs`
    (hVoters : ∀ votes_w support_w : Finset (GoldfishVote V),
      CountedVotes S.C (stateBefore x (voteTime S (s + 1)) w).A
        (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) (s + 1) votes_w support_w →
      voters_count votes_w < 2 * Hs.card)
    -- `p` is awake and honest from the vote time of slot `s` to `t₁`
    (hp : ∀ t : ℕ, voteTime S s ≤ t → t ≤ slotStart S (s + 1) →
      p ∈ Sched.awake (t : Int) ∧ p ∉ Sched.adv (t : Int))
    -- `w` is awake and honest from the vote time of slot `s` to `t₃`
    (hw : ∀ t : ℕ, voteTime S s ≤ t → t ≤ voteTime S (s + 1) →
      w ∈ Sched.awake (t : Int) ∧ w ∉ Sched.adv (t : Int))
    -- `p`'s tick at `t₁` put `B` on the wire
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    -- `w`'s tick at `t₃` put `vote` on the wire
    (hSend : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (s + 1)) ∧
      (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent)
    -- `w`'s tree before `t₃` holds no slot-`(s + 1)` block other than `B`
    (hOnly : ∀ B' ∈ (stateBefore x (voteTime S (s + 1)) w).S.T, B'.slot = s + 1 → B' = B)
    -- no block of `p`'s tree before `t₁` has `B`'s root
    (hRootNew : ∀ B' ∈ (stateBefore x (slotStart S (s + 1)) p).S.T, B'.root ≠ B.root)
    -- some block of `p`'s frame tree before `t₁` that is `X` or a descendant of `X` is a viable
    -- head
    (hF3p : ∃ W ∈ (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).tree,
      W ∈ (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).viable_heads ∧ X.AncestorEq W)
    -- `p`'s anchor is `X` or an ancestor of `X`
    (hApX : (get_anchor (stateBefore x (slotStart S (s + 1)) p).A
      (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S)
      ((slotStart S (s + 1) : ℕ) : Int)).AncestorEq X)
    -- the root of `w`'s fork choice is `B` or an ancestor of `B`
    (hF2w : (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).fc_root.AncestorEq B)
    -- every live lock entry `w`'s revocation leaves is on `B` or an ancestor of `B`
    (hLocksW : ∀ A' : ACState V,
      revoke_locks S.P (expireLocks (stateBefore x (voteTime S (s + 1)) w).A
        ((voteTime S (s + 1) : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
        ((voteTime S (s + 1) : ℕ) : Int) (s + 1) = .ok A' →
      ∀ e ∈ A'.lock_entries,
        is_live (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
          ((voteTime S (s + 1) : ℕ) : Int) e = true → e.B.AncestorEq B)
    -- `B`'s parent passes `w`'s viability test
    (hParentViable : is_viable (stateBefore x (voteTime S (s + 1)) w).S B.parent = true)
    -- `head_height_floor` at `p` is at most `head_height_floor` at `w`
    (hFloorLe : head_height_floor (stateBefore x (slotStart S (s + 1)) p).S ≤
      head_height_floor (stateBefore x (voteTime S (s + 1)) w).S) :
    vote.head = B.root :=
  GoldilocksCorrectness.Proofs.Executions.lem24le_goldfish_vote_names_honest_proposal_composed S
    Sched x GST s Hs H X B p w vote hDiv hMono hSync hCatch hRoots hParent hOwner hGST hHs
    hVoters hp hw hPropose hSend hOnly hRootNew hF3p hApX hF2w hLocksW hParentViable hFloorLe

/-- **Lemma 59 with `head_height_floor` at `p` at most at `w`.** Under the hypotheses of Lemma 59
(`lem59_goldfish_vote_names_honest_proposal_frame`) with `w`'s frame shape at `φ_w` in place of
`φ`, and with "`B`'s chain-state height is at least `φ`" replaced by: `φ ≤ φ_w`, and `φ_w`
is at most the chain-state height of `B`'s parent — then `w`'s vote names `B`. Here `φ` is
`head_height_floor` at `p` and `φ_w` is `head_height_floor` at `w`, as the two frame shapes say.

Why: as Lemma 59, with Lemma 24 in the form `lem24le_goldfish_vote_names_honest_proposal_composed`.
`w` holds `B` (Lemmas 22a and 22) and so `B`'s parent, with its own chain state (Lemma 11), so
`B`'s parent passes `w`'s viability test (Lemma 56); the two frame shapes give the two
`head_height_floor` as `φ` and `φ_w`.

The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s`: the slot of the votes;
- `Hs`: the honest voters of slot `s`; `H`: the block each voter's vote is for;
- `X`: the block every vote of `Hs` extends; `B`: the block `p` proposed at the start of slot
  `s + 1`;
- `p`: the proposer of slot `s + 1`; `w`: the voter of slot `s + 1`;
- `vote`: the Goldfish vote `w` sent at the vote time of slot `s + 1`;
- `ρ_p`, `ρ_w`: the roots of `p`'s and `w`'s fork choices; `φ`, `φ_w`: `head_height_floor` at `p`
  and at `w`.

Read aloud: when `head_height_floor` at the voter is at least at the proposer and at most the
height of the proposal's parent, the voter's vote names the proposal.



Roots name blocks until `voteTime S (s + 1)`: Lemma 22 and
`lem24le_goldfish_vote_names_honest_proposal_composed`, which the proof calls, take blocks as
held up to `w`'s vote time of slot `s + 1`. -/
theorem lem59le_goldfish_vote_names_honest_proposal_frame (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s : ℕ) (Hs : Finset V) (H : V → Block V)
    (X B : Block V) (p w : V) (vote : GoldfishVote V) (ρ_p ρ_w : Block V) (φ φ_w : Height)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (voteTime S (s + 1)))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    (hGST : GST ≤ voteTime S s)
    -- the slot-`s` votes of `Hs` for `X`
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ Sched.adv (voteTime S (s + 1) : Int) ∧
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      H u ∈ (stateBefore x (voteTime S s) u).S.T ∧ X.AncestorEq (H u))
    -- the validators with a vote among those `w`'s slot-`(s + 1)` vote counts are fewer than
    -- twice `Hs`
    (hVoters : ∀ votes_w support_w : Finset (GoldfishVote V),
      CountedVotes S.C (stateBefore x (voteTime S (s + 1)) w).A
        (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) (s + 1) votes_w support_w →
      voters_count votes_w < 2 * Hs.card)
    -- `p` is awake and honest from the vote time of slot `s` to `t₁`
    (hp : ∀ t : ℕ, voteTime S s ≤ t → t ≤ slotStart S (s + 1) →
      p ∈ Sched.awake (t : Int) ∧ p ∉ Sched.adv (t : Int))
    -- `w` is awake and honest from the vote time of slot `s` to `t₃`
    (hw : ∀ t : ℕ, voteTime S s ≤ t → t ≤ voteTime S (s + 1) →
      w ∈ Sched.awake (t : Int) ∧ w ∉ Sched.adv (t : Int))
    -- `p`'s tick at `t₁` put `B` on the wire
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    -- `w`'s tick at `t₃` put `vote` on the wire
    (hSend : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (s + 1)) ∧
      (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent)
    -- `w`'s tree before `t₃` holds no slot-`(s + 1)` block other than `B`
    (hOnly : ∀ B' ∈ (stateBefore x (voteTime S (s + 1)) w).S.T, B'.slot = s + 1 → B' = B)
    -- no block of `p`'s tree before `t₁` has `B`'s root
    (hRootNew : ∀ B' ∈ (stateBefore x (slotStart S (s + 1)) p).S.T, B'.root ≠ B.root)
    -- `p`'s frame before `t₁` has the root `ρ_p` and `head_height_floor` `φ`
    (hShapeP : FrameShape (stateBefore x (slotStart S (s + 1)) p).S ρ_p φ)
    -- `w`'s frame before `t₃` has the root `ρ_w` and `head_height_floor` `φ_w`
    (hShapeW : FrameShape (stateBefore x (voteTime S (s + 1)) w).S ρ_w φ_w)
    -- `φ` is at most `φ_w`
    (hFloorLe : φ ≤ φ_w)
    -- some block of `p`'s tree that is `X` or a descendant of `X`, and `ρ_p` or a descendant of
    -- `ρ_p`, has a chain-state height at least `φ`
    (hHeadP : ∃ W ∈ (stateBefore x (slotStart S (s + 1)) p).S.T,
      X.AncestorEq W ∧ ρ_p.AncestorEq W ∧ φ ≤ (chainStateOf S.C W).h)
    -- `p`'s anchor is `X` or an ancestor of `X`
    (hApX : (get_anchor (stateBefore x (slotStart S (s + 1)) p).A
      (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S)
      ((slotStart S (s + 1) : ℕ) : Int)).AncestorEq X)
    -- `ρ_w` is `B` or an ancestor of `B`
    (hRootW : ρ_w.AncestorEq B)
    -- every live lock entry `w`'s revocation leaves is on `B` or an ancestor of `B`
    (hLocksW : ∀ A' : ACState V,
      revoke_locks S.P (expireLocks (stateBefore x (voteTime S (s + 1)) w).A
        ((voteTime S (s + 1) : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
        ((voteTime S (s + 1) : ℕ) : Int) (s + 1) = .ok A' →
      ∀ e ∈ A'.lock_entries,
        is_live (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
          ((voteTime S (s + 1) : ℕ) : Int) e = true → e.B.AncestorEq B)
    -- `φ_w` is at most the chain-state height of `B`'s parent
    (hParentHeight : φ_w ≤ (chainStateOf S.C B.parent).h) :
    vote.head = B.root :=
  GoldilocksCorrectness.Proofs.Executions.lem59le_goldfish_vote_names_honest_proposal_frame S Sched
    x GST s Hs H X B p w vote ρ_p ρ_w φ φ_w hDiv hMono hSync hCatch hRoots hParent hOwner
    hGST hHs hVoters hp hw hPropose hSend hOnly hRootNew hShapeP hShapeW hFloorLe hHeadP hApX
    hRootW hLocksW hParentHeight

end GoldilocksCorrectness.Statements.Executions
