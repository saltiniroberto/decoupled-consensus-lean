module
public import GoldilocksCorrectness.Proofs.Executions.Boxes

@[expose] public section

/-!
# The box instances of Lemmas 59 and 61

The audited statements of what each of the three boxes (`BoxOne`, `BoxTwo`, `BoxThree`) supplies
to Lemma 59 (`lem59_goldfish_vote_names_honest_proposal_frame`) and Lemma 61
(`lem61_honest_validator_attests_frame`, through its kit theorem `lem61_frame_hypotheses`), proved
in `GoldilocksCorrectness/Proofs/Executions/Boxes.lean`: `lem59_boxOne`, `lem59_boxTwo`,
`lem59_boxThree`, `lem61_boxOne`, `lem61_boxTwo`, `lem61_boxThree`. Each has an `_at` form with
the time `w`'s state is read (`t_w`, Lemma 59) or `v`'s (`t_v`, Lemma 61) a parameter; the six are
its instances at the vote time and the support cutoff of slot `s + 1`.


-/

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (slotStart voteTime supportCutoff)

open GoldilocksCorrectness.Statements.Routines (chainStateOf)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Routines (FrameShape BoxOne BoxTwo BoxThree)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-! ## Lemma 59 -/

/-- **Lemma 59 in box 1.** When `p`'s state before the start `t₁` of slot `s + 1` and `w`'s before
the time `t_w` are both in box 1 with one `h_max`, `w`'s finalized block is `B`
or an ancestor of `B`, `p` put `B` on the wire at its tick at `t₁` with `B`'s parent in `p`'s viable
tree, and some block of `p`'s tree on `p`'s finalized block's chain, `X` or a descendant of `X`,
has a chain-state height at least `p`'s `h_max − 1`: then the frame hypotheses of Lemma 59 hold
with the roots `p`'s and `w`'s finalized blocks and `head_height_floor` (the least chain-state height a viable block may have) equal to `p`'s `h_max − 1`.

Why: box 1 has the finalized block as its root and `h_max − 1` as its `head_height_floor` (Lemma 56), equal at
the two states by the one `h_max`; the honest proposal reaches `head_height_floor` at its proposer
(`proposal_viable`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the slot before the proposal's;
- `X`: the block every honest slot-`s` vote extends; `B`: the block `p` proposed;
- `p`: the proposer of slot `s + 1`; `w`: the voter of slot `s + 1`;
- `t_w`: the time `w`'s state is read.

Read aloud: in box 1, with one `h_max`, the `head_height_floor` values agree at `h_max − 1` and the honest proposal
reaches it; the root condition is the hypothesis on `w`'s finalized block.

`lem59_boxOne` is its instance at `t_w := voteTime S (s + 1)`. -/
theorem lem59_boxOne_at (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s t_w : ℕ) (X B : Block V) (p w : V)
    -- `p`'s state before `t₁` is in box 1
    (hBoxP : BoxOne (stateBefore x (slotStart S (s + 1)) p).S)
    -- `w`'s state before `t_w` is in box 1
    (hBoxW : BoxOne (stateBefore x t_w w).S)
    -- the two states have the same `h_max`
    (hHmax : (stateBefore x (slotStart S (s + 1)) p).S.h_max =
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
        ((stateBefore x (slotStart S (s + 1)) p).S.h_max - 1) ∧
      (stateBefore x t_w w).S.F.AncestorEq B ∧
      (∃ W ∈ (stateBefore x (slotStart S (s + 1)) p).S.T,
        X.AncestorEq W ∧ (stateBefore x (slotStart S (s + 1)) p).S.F.AncestorEq W ∧
          (stateBefore x (slotStart S (s + 1)) p).S.h_max - 1 ≤ (chainStateOf S.C W).h) ∧
      (stateBefore x (slotStart S (s + 1)) p).S.h_max - 1 ≤ (chainStateOf S.C B).h :=
  GoldilocksCorrectness.Proofs.Executions.lem59_boxOne_at S Sched x s t_w X B p w hBoxP hBoxW hHmax
    hFw hPropose hParentIn hHeadP

/-- **Lemma 59 in box 1.** When `p`'s state before the start `t₁` of slot `s + 1` and `w`'s before
the vote time `t₃` of slot `s + 1` are both in box 1 with one `h_max`, `w`'s finalized block is `B`
or an ancestor of `B`, `p` put `B` on the wire at its tick at `t₁` with `B`'s parent in `p`'s viable
tree, and some block of `p`'s tree on `p`'s finalized block's chain, `X` or a descendant of `X`,
has a chain-state height at least `p`'s `h_max − 1`: then the frame hypotheses of Lemma 59 hold
with the roots `p`'s and `w`'s finalized blocks and `head_height_floor` equal to `p`'s `h_max − 1`.

Why: box 1 has the finalized block as its root and `h_max − 1` as its `head_height_floor` (Lemma 56), equal at
the two states by the one `h_max`; the honest proposal reaches `head_height_floor` at its proposer
(`proposal_viable`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the slot before the proposal's;
- `X`: the block every honest slot-`s` vote extends; `B`: the block `p` proposed;
- `p`: the proposer of slot `s + 1`; `w`: the voter of slot `s + 1`.

Read aloud: in box 1, with one `h_max`, the `head_height_floor` values agree at `h_max − 1` and the honest proposal
reaches it; the root condition is the hypothesis on `w`'s finalized block.



It is the instance of `lem59_boxOne_at` at `t_w := voteTime S (s + 1)`. -/
theorem lem59_boxOne (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s : ℕ) (X B : Block V) (p w : V)
    -- `p`'s state before `t₁` is in box 1
    (hBoxP : BoxOne (stateBefore x (slotStart S (s + 1)) p).S)
    -- `w`'s state before `t₃` is in box 1
    (hBoxW : BoxOne (stateBefore x (voteTime S (s + 1)) w).S)
    -- the two states have the same `h_max`
    (hHmax : (stateBefore x (slotStart S (s + 1)) p).S.h_max =
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
        ((stateBefore x (slotStart S (s + 1)) p).S.h_max - 1) ∧
      (stateBefore x (voteTime S (s + 1)) w).S.F.AncestorEq B ∧
      (∃ W ∈ (stateBefore x (slotStart S (s + 1)) p).S.T,
        X.AncestorEq W ∧ (stateBefore x (slotStart S (s + 1)) p).S.F.AncestorEq W ∧
          (stateBefore x (slotStart S (s + 1)) p).S.h_max - 1 ≤ (chainStateOf S.C W).h) ∧
      (stateBefore x (slotStart S (s + 1)) p).S.h_max - 1 ≤ (chainStateOf S.C B).h :=
  lem59_boxOne_at S Sched x s (voteTime S (s + 1)) X B p w hBoxP hBoxW hHmax hFw hPropose hParentIn
    hHeadP

/-- **Lemma 59 in box 2.** When `p`'s state before the start `t₁` of slot `s + 1` and `w`'s before
the time `t_w` are both in box 2 with one justified block `J₀`, other than the
genesis block, and `p` put `B` on the wire at its tick at `t₁` with `B`'s parent in `p`'s viable
tree: then both frames have the root `J₀` and `head_height_floor` equal to `p`'s `h_max − 1`, `J₀` is `B`'s parent or
an ancestor of it, and `B`'s chain-state height is at least that `head_height_floor` value.

Why: box 2 has `J₀` as its root and `h_max − 1` as its `head_height_floor` (Lemma 56); at both states `h_max` is
`h_j + 1` and `h_j` is `J₀`'s chain-state height (Lemma 57), so the two `h_max` are equal; the
viable tree holds only descendants of the root; the honest proposal reaches `head_height_floor` at its proposer
(`proposal_viable`). With `J₀` the genesis block the two `h_j` can differ (`0` and `1`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the slot before the proposal's;
- `B`: the block `p` proposed; `J₀`: the justified block;
- `p`: the proposer of slot `s + 1`; `w`: the voter of slot `s + 1`;
- `t_w`: the time `w`'s state is read.

Read aloud: in box 2 the root condition is free and the equal `head_height_floor` values come from the one justified
block.

`lem59_boxTwo` is its instance at `t_w := voteTime S (s + 1)`. -/
theorem lem59_boxTwo_at (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s t_w : ℕ) (B J₀ : Block V) (p w : V)
    -- `p`'s state before `t₁` is in box 2 with the justified block `J₀`
    (hBoxP : BoxTwo (stateBefore x (slotStart S (s + 1)) p).S J₀)
    -- `w`'s state before `t_w` is in box 2 with the justified block `J₀`
    (hBoxW : BoxTwo (stateBefore x t_w w).S J₀)
    -- `J₀` is not the genesis block
    (hJ₀ : J₀ ≠ Block.genesis)
    -- `p`'s tick at `t₁` put `B` on the wire
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    -- `B`'s parent is in the viable tree of `p`'s frame before `t₁`
    (hParentIn : B.parent ∈ viable_tree (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S)
      (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).tree) :
    FrameShape (stateBefore x (slotStart S (s + 1)) p).S J₀
        ((stateBefore x (slotStart S (s + 1)) p).S.h_max - 1) ∧
      FrameShape (stateBefore x t_w w).S J₀
        ((stateBefore x (slotStart S (s + 1)) p).S.h_max - 1) ∧
      J₀.AncestorEq B.parent ∧
      (stateBefore x (slotStart S (s + 1)) p).S.h_max - 1 ≤ (chainStateOf S.C B).h :=
  GoldilocksCorrectness.Proofs.Executions.lem59_boxTwo_at S Sched x s t_w B J₀ p w hBoxP hBoxW hJ₀
    hPropose hParentIn

/-- **Lemma 59 in box 2.** When `p`'s state before the start `t₁` of slot `s + 1` and `w`'s before
the vote time `t₃` of slot `s + 1` are both in box 2 with one justified block `J₀`, other than the
genesis block, and `p` put `B` on the wire at its tick at `t₁` with `B`'s parent in `p`'s viable
tree: then both frames have the root `J₀` and `head_height_floor` equal to `p`'s `h_max − 1`, `J₀` is `B`'s parent or
an ancestor of it, and `B`'s chain-state height is at least that `head_height_floor` value.

Why: box 2 has `J₀` as its root and `h_max − 1` as its `head_height_floor` (Lemma 56); at both states `h_max` is
`h_j + 1` and `h_j` is `J₀`'s chain-state height (Lemma 57), so the two `h_max` are equal; the
viable tree holds only descendants of the root; the honest proposal reaches `head_height_floor` at its proposer
(`proposal_viable`). With `J₀` the genesis block the two `h_j` can differ (`0` and `1`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the slot before the proposal's;
- `B`: the block `p` proposed; `J₀`: the justified block;
- `p`: the proposer of slot `s + 1`; `w`: the voter of slot `s + 1`.

Read aloud: in box 2 the root condition is free and the equal `head_height_floor` values come from the one justified
block.



It is the instance of `lem59_boxTwo_at` at `t_w := voteTime S (s + 1)`. -/
theorem lem59_boxTwo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s : ℕ) (B J₀ : Block V) (p w : V)
    -- `p`'s state before `t₁` is in box 2 with the justified block `J₀`
    (hBoxP : BoxTwo (stateBefore x (slotStart S (s + 1)) p).S J₀)
    -- `w`'s state before `t₃` is in box 2 with the justified block `J₀`
    (hBoxW : BoxTwo (stateBefore x (voteTime S (s + 1)) w).S J₀)
    -- `J₀` is not the genesis block
    (hJ₀ : J₀ ≠ Block.genesis)
    -- `p`'s tick at `t₁` put `B` on the wire
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S (s + 1)) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    -- `B`'s parent is in the viable tree of `p`'s frame before `t₁`
    (hParentIn : B.parent ∈ viable_tree (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S)
      (fg_to_ac (stateBefore x (slotStart S (s + 1)) p).S).tree) :
    FrameShape (stateBefore x (slotStart S (s + 1)) p).S J₀
        ((stateBefore x (slotStart S (s + 1)) p).S.h_max - 1) ∧
      FrameShape (stateBefore x (voteTime S (s + 1)) w).S J₀
        ((stateBefore x (slotStart S (s + 1)) p).S.h_max - 1) ∧
      J₀.AncestorEq B.parent ∧
      (stateBefore x (slotStart S (s + 1)) p).S.h_max - 1 ≤ (chainStateOf S.C B).h :=
  lem59_boxTwo_at S Sched x s (voteTime S (s + 1)) B J₀ p w hBoxP hBoxW hJ₀ hPropose hParentIn

/-- **Lemma 59 in box 3.** When `p`'s state before the start `t₁` of slot `s + 1` and `w`'s before
the time `t_w` are both contested with one `h_max`, `w`'s finalized block is
`B` or an ancestor of `B`, and `p` put `B` on the wire at its tick at `t₁` with `B`'s parent in
`p`'s viable tree: then the frame hypotheses of Lemma 59 other than the block of `p`'s tree hold
with the roots `p`'s and `w`'s finalized blocks and `head_height_floor` equal to `p`'s `h_max`.

Why: box 3 has the finalized block as its root and `h_max` as its `head_height_floor` (Lemma 56), equal at the
two states by the one `h_max`; the honest proposal reaches `head_height_floor` at its proposer
(`proposal_viable`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the slot before the proposal's;
- `B`: the block `p` proposed;
- `p`: the proposer of slot `s + 1`; `w`: the voter of slot `s + 1`;
- `t_w`: the time `w`'s state is read.

Read aloud: in box 3, with one `h_max`, the `head_height_floor` values agree at `h_max` and the honest proposal reaches
it; the root condition is the hypothesis on `w`'s finalized block.

`lem59_boxThree` is its instance at `t_w := voteTime S (s + 1)`. -/
theorem lem59_boxThree_at (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s t_w : ℕ) (B : Block V) (p w : V)
    -- `p`'s state before `t₁` is contested
    (hBoxP : BoxThree (stateBefore x (slotStart S (s + 1)) p).S)
    -- `w`'s state before `t_w` is contested
    (hBoxW : BoxThree (stateBefore x t_w w).S)
    -- the two states have the same `h_max`
    (hHmax : (stateBefore x (slotStart S (s + 1)) p).S.h_max =
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
        (stateBefore x (slotStart S (s + 1)) p).S.h_max ∧
      (stateBefore x t_w w).S.F.AncestorEq B ∧
      (stateBefore x (slotStart S (s + 1)) p).S.h_max ≤ (chainStateOf S.C B).h :=
  GoldilocksCorrectness.Proofs.Executions.lem59_boxThree_at S Sched x s t_w B p w hBoxP hBoxW hHmax
    hFw hPropose hParentIn

/-- **Lemma 59 in box 3.** When `p`'s state before the start `t₁` of slot `s + 1` and `w`'s before
the vote time `t₃` of slot `s + 1` are both contested with one `h_max`, `w`'s finalized block is
`B` or an ancestor of `B`, and `p` put `B` on the wire at its tick at `t₁` with `B`'s parent in
`p`'s viable tree: then the frame hypotheses of Lemma 59 other than the block of `p`'s tree hold
with the roots `p`'s and `w`'s finalized blocks and `head_height_floor` equal to `p`'s `h_max`.

Why: box 3 has the finalized block as its root and `h_max` as its `head_height_floor` (Lemma 56), equal at the
two states by the one `h_max`; the honest proposal reaches `head_height_floor` at its proposer
(`proposal_viable`).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the slot before the proposal's;
- `B`: the block `p` proposed;
- `p`: the proposer of slot `s + 1`; `w`: the voter of slot `s + 1`.

Read aloud: in box 3, with one `h_max`, the `head_height_floor` values agree at `h_max` and the honest proposal reaches
it; the root condition is the hypothesis on `w`'s finalized block.



It is the instance of `lem59_boxThree_at` at `t_w := voteTime S (s + 1)`. -/
theorem lem59_boxThree (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s : ℕ) (B : Block V) (p w : V)
    -- `p`'s state before `t₁` is contested
    (hBoxP : BoxThree (stateBefore x (slotStart S (s + 1)) p).S)
    -- `w`'s state before `t₃` is contested
    (hBoxW : BoxThree (stateBefore x (voteTime S (s + 1)) w).S)
    -- the two states have the same `h_max`
    (hHmax : (stateBefore x (slotStart S (s + 1)) p).S.h_max =
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
        (stateBefore x (slotStart S (s + 1)) p).S.h_max ∧
      (stateBefore x (voteTime S (s + 1)) w).S.F.AncestorEq B ∧
      (stateBefore x (slotStart S (s + 1)) p).S.h_max ≤ (chainStateOf S.C B).h :=
  lem59_boxThree_at S Sched x s (voteTime S (s + 1)) B p w hBoxP hBoxW hHmax hFw hPropose hParentIn

/-! ## Lemma 61 -/

/-- **Lemma 61 in box 1.** When `v`'s state before the time `t_v` is in
box 1, its finalized block is `B` or an ancestor of `B`, `B`'s chain-state height `H` is at least
`h_max − 1`, and `B` is in `v`'s tree: then `B` is in `v`'s viable tree, and `v`'s record holds no
lock at `H`, or the lock on the root `T` of `B`'s `T_h` with every attestation it sent at `H`
naming `T`.

Why: box 1 has the root `F` and `head_height_floor` equal to `h_max − 1` (Lemma 56); the cache `h_j` is less than
`h_max − 1`, so less than `H`, and the record holds no lock at `H` (Lemma 57); the kit theorem
`lem61_frame_hypotheses` concludes.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t_v`: the time `v`'s state
  is read;
- `B`: the block; `v`: the validator.

Read aloud: in box 1 the record holds no lock at `B`'s height, because the cache `h_j` is less than
`head_height_floor` and `head_height_floor` is at most `B`'s height.

`lem61_boxOne` is its instance at `t_v := supportCutoff S (s + 1)`. -/
theorem lem61_boxOne_at (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (t_v : ℕ) (B : Block V) (v : V)
    -- `v`'s state before `t_v` is in box 1
    (hBox : BoxOne (stateBefore x t_v v).S)
    -- `v`'s finalized block before `t_v` is `B` or an ancestor of `B`
    (hFv : (stateBefore x t_v v).S.F.AncestorEq B)
    -- `B`'s chain-state height is at least `h_max − 1`
    (hBHeight : (stateBefore x t_v v).S.h_max - 1 ≤ (chainStateOf S.C B).h)
    -- `B` is in `v`'s tree before `t_v`
    (hBin : B ∈ (stateBefore x t_v v).S.T) :
    B ∈ viable_tree (fg_to_ac (stateBefore x t_v v).S)
        (fg_to_ac (stateBefore x t_v v).S).tree ∧
      ((stateBefore x t_v v).Λ.lock (chainStateOf S.C B).h = none ∨
        ((stateBefore x t_v v).Λ.lock (chainStateOf S.C B).h =
            some (chainStateOf S.C B).T_h.root ∧
          ∀ b ∈ (stateBefore x t_v v).Λ.sent,
            b.h = (chainStateOf S.C B).h → b.T = (chainStateOf S.C B).T_h.root)) :=
  GoldilocksCorrectness.Proofs.Executions.lem61_boxOne_at S Sched x t_v B v hBox hFv hBHeight hBin

/-- **Lemma 61 in box 1.** When `v`'s state before the support cutoff `a_r` of slot `s + 1` is in
box 1, its finalized block is `B` or an ancestor of `B`, `B`'s chain-state height `H` is at least
`h_max − 1`, and `B` is in `v`'s tree: then `B` is in `v`'s viable tree, and `v`'s record holds no
lock at `H`, or the lock on the root `T` of `B`'s `T_h` with every attestation it sent at `H`
naming `T`.

Why: box 1 has the root `F` and `head_height_floor` equal to `h_max − 1` (Lemma 56); the cache `h_j` is less than
`h_max − 1`, so less than `H`, and the record holds no lock at `H` (Lemma 57); the kit theorem
`lem61_frame_hypotheses` concludes.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the slot before the update's;
- `B`: the block; `v`: the validator.

Read aloud: in box 1 the record holds no lock at `B`'s height, because the cache `h_j` is less than
`head_height_floor` and `head_height_floor` is at most `B`'s height.



It is the instance of `lem61_boxOne_at` at `t_v := supportCutoff S (s + 1)`. -/
theorem lem61_boxOne (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (s : ℕ) (B : Block V) (v : V)
    -- `v`'s state before `a_r` is in box 1
    (hBox : BoxOne (stateBefore x (supportCutoff S (s + 1)) v).S)
    -- `v`'s finalized block before `a_r` is `B` or an ancestor of `B`
    (hFv : (stateBefore x (supportCutoff S (s + 1)) v).S.F.AncestorEq B)
    -- `B`'s chain-state height is at least `h_max − 1`
    (hBHeight : (stateBefore x (supportCutoff S (s + 1)) v).S.h_max - 1 ≤ (chainStateOf S.C B).h)
    -- `B` is in `v`'s tree before `a_r`
    (hBin : B ∈ (stateBefore x (supportCutoff S (s + 1)) v).S.T) :
    B ∈ viable_tree (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S)
        (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S).tree ∧
      ((stateBefore x (supportCutoff S (s + 1)) v).Λ.lock (chainStateOf S.C B).h = none ∨
        ((stateBefore x (supportCutoff S (s + 1)) v).Λ.lock (chainStateOf S.C B).h =
            some (chainStateOf S.C B).T_h.root ∧
          ∀ b ∈ (stateBefore x (supportCutoff S (s + 1)) v).Λ.sent,
            b.h = (chainStateOf S.C B).h → b.T = (chainStateOf S.C B).T_h.root)) :=
  lem61_boxOne_at S Sched x (supportCutoff S (s + 1)) B v hBox hFv hBHeight hBin

/-- **Lemma 61 in box 2.** When `v`'s state before the time `t_v` is in
box 2 with the justified block `J₀`, `J₀` is `B` or an ancestor of `B`, `B`'s chain-state height
`H` is at least `h_max − 1`, `v`'s lock at height `h_max − 1`, when set, is on the root `T` of
`B`'s `T_h`, and `B` is in `v`'s tree: then `B` is in `v`'s viable tree, and `v`'s record holds no
lock at `H`, or the lock on `T` with every attestation it sent at `H` naming `T`.

Why: box 2 has the root `J₀` and `head_height_floor` equal to `h_max − 1 = h_j` (Lemma 56); when `H` is greater than
`h_j` the record holds no lock at `H` (Lemma 57); when `H` is `h_j`, the lock at `H`, when set, is
`T` by the hypothesis on the lock; the kit theorem `lem61_frame_hypotheses` concludes.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t_v`: the time `v`'s state
  is read;
- `B`: the block; `J₀`: the justified block; `v`: the validator.

Read aloud: in box 2 the lock at `B`'s height, when `B` is at `h_max − 1`, is on the entry block of
`B`'s height, as the hypothesis on the lock says.

`lem61_boxTwo` is its instance at `t_v := supportCutoff S (s + 1)`. -/
theorem lem61_boxTwo_at (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (t_v : ℕ) (B J₀ : Block V) (v : V)
    -- `v`'s state before `t_v` is in box 2 with the justified block `J₀`
    (hBox : BoxTwo (stateBefore x t_v v).S J₀)
    -- `J₀` is `B` or an ancestor of `B`
    (hJB : J₀.AncestorEq B)
    -- `B`'s chain-state height is at least `h_max − 1`
    (hBHeight : (stateBefore x t_v v).S.h_max - 1 ≤ (chainStateOf S.C B).h)
    -- `v`'s lock at height `h_max − 1`, when set, is on the root of `B`'s `T_h`
    (hLockT : ∀ T' : BlockId,
      (stateBefore x t_v v).Λ.lock
        ((stateBefore x t_v v).S.h_max - 1) = some T' →
      T' = (chainStateOf S.C B).T_h.root)
    -- `B` is in `v`'s tree before `t_v`
    (hBin : B ∈ (stateBefore x t_v v).S.T) :
    B ∈ viable_tree (fg_to_ac (stateBefore x t_v v).S)
        (fg_to_ac (stateBefore x t_v v).S).tree ∧
      ((stateBefore x t_v v).Λ.lock (chainStateOf S.C B).h = none ∨
        ((stateBefore x t_v v).Λ.lock (chainStateOf S.C B).h =
            some (chainStateOf S.C B).T_h.root ∧
          ∀ b ∈ (stateBefore x t_v v).Λ.sent,
            b.h = (chainStateOf S.C B).h → b.T = (chainStateOf S.C B).T_h.root)) :=
  GoldilocksCorrectness.Proofs.Executions.lem61_boxTwo_at S Sched x t_v B J₀ v hBox hJB hBHeight
    hLockT hBin

/-- **Lemma 61 in box 2.** When `v`'s state before the support cutoff `a_r` of slot `s + 1` is in
box 2 with the justified block `J₀`, `J₀` is `B` or an ancestor of `B`, `B`'s chain-state height
`H` is at least `h_max − 1`, `v`'s lock at height `h_max − 1`, when set, is on the root `T` of
`B`'s `T_h`, and `B` is in `v`'s tree: then `B` is in `v`'s viable tree, and `v`'s record holds no
lock at `H`, or the lock on `T` with every attestation it sent at `H` naming `T`.

Why: box 2 has the root `J₀` and `head_height_floor` equal to `h_max − 1 = h_j` (Lemma 56); when `H` is greater than
`h_j` the record holds no lock at `H` (Lemma 57); when `H` is `h_j`, the lock at `H`, when set, is
`T` by the hypothesis on the lock; the kit theorem `lem61_frame_hypotheses` concludes.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the slot before the update's;
- `B`: the block; `J₀`: the justified block; `v`: the validator.

Read aloud: in box 2 the lock at `B`'s height, when `B` is at `h_max − 1`, is on the entry block of
`B`'s height, as the hypothesis on the lock says.



It is the instance of `lem61_boxTwo_at` at `t_v := supportCutoff S (s + 1)`. -/
theorem lem61_boxTwo (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (s : ℕ) (B J₀ : Block V) (v : V)
    -- `v`'s state before `a_r` is in box 2 with the justified block `J₀`
    (hBox : BoxTwo (stateBefore x (supportCutoff S (s + 1)) v).S J₀)
    -- `J₀` is `B` or an ancestor of `B`
    (hJB : J₀.AncestorEq B)
    -- `B`'s chain-state height is at least `h_max − 1`
    (hBHeight : (stateBefore x (supportCutoff S (s + 1)) v).S.h_max - 1 ≤ (chainStateOf S.C B).h)
    -- `v`'s lock at height `h_max − 1`, when set, is on the root of `B`'s `T_h`
    (hLockT : ∀ T' : BlockId,
      (stateBefore x (supportCutoff S (s + 1)) v).Λ.lock
        ((stateBefore x (supportCutoff S (s + 1)) v).S.h_max - 1) = some T' →
      T' = (chainStateOf S.C B).T_h.root)
    -- `B` is in `v`'s tree before `a_r`
    (hBin : B ∈ (stateBefore x (supportCutoff S (s + 1)) v).S.T) :
    B ∈ viable_tree (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S)
        (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S).tree ∧
      ((stateBefore x (supportCutoff S (s + 1)) v).Λ.lock (chainStateOf S.C B).h = none ∨
        ((stateBefore x (supportCutoff S (s + 1)) v).Λ.lock (chainStateOf S.C B).h =
            some (chainStateOf S.C B).T_h.root ∧
          ∀ b ∈ (stateBefore x (supportCutoff S (s + 1)) v).Λ.sent,
            b.h = (chainStateOf S.C B).h → b.T = (chainStateOf S.C B).T_h.root)) :=
  lem61_boxTwo_at S Sched x (supportCutoff S (s + 1)) B J₀ v hBox hJB hBHeight hLockT hBin

/-- **Lemma 61 in box 3.** When `v`'s state before the time `t_v` is
contested, its finalized block is `B` or an ancestor of `B`, `B`'s chain-state height `H` is at
least `h_max`, and `B` is in `v`'s tree: then `B` is in `v`'s viable tree, and `v`'s record holds no
lock at `H`, or the lock on the root `T` of `B`'s `T_h` with every attestation it sent at `H`
naming `T`.

Why: box 3 has the root `F`, `head_height_floor` equal to `h_max` and `h_max = h_j + 1` (Lemma 56); so `h_j` is less
than `H`, and the record holds no lock at `H` (Lemma 57); the kit theorem `lem61_frame_hypotheses`
concludes.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t_v`: the time `v`'s state
  is read;
- `B`: the block; `v`: the validator.

Read aloud: in box 3 the record holds no lock at `B`'s height, because the cache `h_j` is
`h_max − 1` and `B`'s height is at least `h_max`.

`lem61_boxThree` is its instance at `t_v := supportCutoff S (s + 1)`. -/
theorem lem61_boxThree_at (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (t_v : ℕ) (B : Block V) (v : V)
    -- `v`'s state before `t_v` is contested
    (hBox : BoxThree (stateBefore x t_v v).S)
    -- `v`'s finalized block before `t_v` is `B` or an ancestor of `B`
    (hFv : (stateBefore x t_v v).S.F.AncestorEq B)
    -- `B`'s chain-state height is at least `h_max`
    (hBHeight : (stateBefore x t_v v).S.h_max ≤ (chainStateOf S.C B).h)
    -- `B` is in `v`'s tree before `t_v`
    (hBin : B ∈ (stateBefore x t_v v).S.T) :
    B ∈ viable_tree (fg_to_ac (stateBefore x t_v v).S)
        (fg_to_ac (stateBefore x t_v v).S).tree ∧
      ((stateBefore x t_v v).Λ.lock (chainStateOf S.C B).h = none ∨
        ((stateBefore x t_v v).Λ.lock (chainStateOf S.C B).h =
            some (chainStateOf S.C B).T_h.root ∧
          ∀ b ∈ (stateBefore x t_v v).Λ.sent,
            b.h = (chainStateOf S.C B).h → b.T = (chainStateOf S.C B).T_h.root)) :=
  GoldilocksCorrectness.Proofs.Executions.lem61_boxThree_at S Sched x t_v B v hBox hFv hBHeight hBin

/-- **Lemma 61 in box 3.** When `v`'s state before the support cutoff `a_r` of slot `s + 1` is
contested, its finalized block is `B` or an ancestor of `B`, `B`'s chain-state height `H` is at
least `h_max`, and `B` is in `v`'s tree: then `B` is in `v`'s viable tree, and `v`'s record holds no
lock at `H`, or the lock on the root `T` of `B`'s `T_h` with every attestation it sent at `H`
naming `T`.

Why: box 3 has the root `F`, `head_height_floor` equal to `h_max` and `h_max = h_j + 1` (Lemma 56); so `h_j` is less
than `H`, and the record holds no lock at `H` (Lemma 57); the kit theorem `lem61_frame_hypotheses`
concludes.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the slot before the update's;
- `B`: the block; `v`: the validator.

Read aloud: in box 3 the record holds no lock at `B`'s height, because the cache `h_j` is
`h_max − 1` and `B`'s height is at least `h_max`.



It is the instance of `lem61_boxThree_at` at `t_v := supportCutoff S (s + 1)`. -/
theorem lem61_boxThree (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (s : ℕ) (B : Block V) (v : V)
    -- `v`'s state before `a_r` is contested
    (hBox : BoxThree (stateBefore x (supportCutoff S (s + 1)) v).S)
    -- `v`'s finalized block before `a_r` is `B` or an ancestor of `B`
    (hFv : (stateBefore x (supportCutoff S (s + 1)) v).S.F.AncestorEq B)
    -- `B`'s chain-state height is at least `h_max`
    (hBHeight : (stateBefore x (supportCutoff S (s + 1)) v).S.h_max ≤ (chainStateOf S.C B).h)
    -- `B` is in `v`'s tree before `a_r`
    (hBin : B ∈ (stateBefore x (supportCutoff S (s + 1)) v).S.T) :
    B ∈ viable_tree (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S)
        (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S).tree ∧
      ((stateBefore x (supportCutoff S (s + 1)) v).Λ.lock (chainStateOf S.C B).h = none ∨
        ((stateBefore x (supportCutoff S (s + 1)) v).Λ.lock (chainStateOf S.C B).h =
            some (chainStateOf S.C B).T_h.root ∧
          ∀ b ∈ (stateBefore x (supportCutoff S (s + 1)) v).Λ.sent,
            b.h = (chainStateOf S.C B).h → b.T = (chainStateOf S.C B).T_h.root)) :=
  lem61_boxThree_at S Sched x (supportCutoff S (s + 1)) B v hBox hFv hBHeight hBin

end GoldilocksCorrectness.Statements.Executions
