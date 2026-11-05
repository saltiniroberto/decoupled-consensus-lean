module
public import GoldilocksCorrectness.Proofs.Routines.ForkChoiceFacts

@[expose] public section

/-!
# Two statements about the end of the Goldfish fork choice

`vote_head_compatible_of_justified_past`: at an FG state `n` justified at least one height past a
block `B`, under the conditions it states, the end of the Goldfish fork choice from the anchor of
an AC state through a viable tree is compatible with `B`; `vote_head_descends_of_F`: that end is
`n.F` or a descendant of `n.F` when `n.F` is `n.J` or an ancestor of it. Proved in
`Proofs/Routines/ForkChoiceFacts.lean`.

Moved here unchanged from the execution pages.
-/

set_option autoImplicit false

open scoped DC
open DC (DRE)

namespace GoldilocksCorrectness.Statements.Routines

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]

/-- **The vote of a state justified past `B` does not conflict with `B`.** At an FG state `n`
whose chain states are computed, whose justified block is compatible with `B`, has the chain-state
height `n.h_j`, with `n.F` an ancestor of it or it, whose held blocks two heights past `B` descend
from `B`, with `n.h_j < n.h_max` and `h(B) + 1 ≤ n.h_j`: the end of the Goldfish fork choice from
the anchor of any AC state `A'` through the viable tree of any tree `vbt` (the form Lemma 14,
`lem14_tick_vote_walk`, gives a vote's head) is compatible with `B`.

Why: every viable head descends from `B` (three cases: contested, `h_max = h_j + 1`
not contested, otherwise); so every block of a viable tree is compatible with `B`; the
fork-choice root (`J` or `F`, `F ⪯ J`) is; the anchor is the root or a block of a viable tree;
the walk ends at the anchor or at a block of the tree walked.

The variables:
- `C`: the parameters; `n`: the FG state; `B`: the block; `A'`: the AC state the anchor is read
  from; `t`: the time; `vbt`: the voter tree; `votes`, `sv`: the votes and the support votes;
  `s`: the slot; `H`: the head.

Read aloud: at an FG state whose caches are compatible with `B`, whose held blocks two heights
past `B` descend from `B`, with `h_j < h_max` and `h_j ≥ h(B) + 1`, the head of any Goldfish vote
it computes is compatible with `B`. -/
theorem vote_head_compatible_of_justified_past [RootOrder] (C : Config) (n : FGState V)
    (B : Block V)
    -- the chain states of `n`'s tree are the blocks' own
    (hσ : ChainStatesComputed C n)
    -- `n`'s justified block is compatible with `B`
    (hJ : n.J.AncestorEq B ∨ B.AncestorEq n.J)
    -- `n`'s justified block has the chain-state height `n.h_j`
    (hJh : (chainStateOf C n.J).h = n.h_j)
    -- `n`'s finalized block is its justified block or an ancestor of it
    (hFJ : n.F.AncestorEq n.J)
    -- every block of `n`'s tree two heights past `B` descends from `B`
    (hTwo : ∀ D ∈ n.T, (chainStateOf C B).h + 2 ≤ (chainStateOf C D).h → B.AncestorEq D)
    -- `n`'s justification height is less than its greatest height
    (hjmax : n.h_j < n.h_max)
    -- `n` is justified past `B`
    (hSafe : (chainStateOf C B).h + 1 ≤ n.h_j)
    (A' : ACState V) (t : Time) (vbt : Finset (Block V)) (votes sv : Finset (GoldfishVote V))
    (s : Slot) (H : Block V)
    -- the fork choice ends at `H`
    (h : goldfish_fork_choice C (fg_to_ac n) t (get_anchor A' (fg_to_ac n) t)
      (viable_tree (fg_to_ac n) vbt) votes sv s = .ok H) :
    H.compatible B = true :=
  GoldilocksCorrectness.Proofs.Routines.vote_head_compatible_of_justified_past C n B hσ hJ hJh
    hFJ hTwo hjmax hSafe A' t vbt votes sv s H h

/-- **The head of a Goldfish vote descends from the voter's finalized block.** The end of the
Goldfish fork choice from the anchor of any AC state `A'` through the viable tree of any tree
`vbt` is `n.F` or a descendant of `n.F`, when `n.F` is `n.J` or an ancestor of it.

Why: the anchor is the root of the fork choice or a block of a viable tree, the walk ends at the
anchor or at a block of the viable tree it walks, every block of a viable tree descends from the
root of the fork choice, and that root is `n.J` or `n.F`.

The variables:
- `C`: the parameters; `n`: the FG state; `A'`: the AC state the anchor is read from; `t`: the
  time; `vbt`: the voter tree; `votes`, `sv`: the votes and the support votes; `s`: the slot;
  `H`: the head.

Read aloud: the head of a Goldfish vote is the voter's finalized block or a descendant of it. -/
theorem vote_head_descends_of_F [RootOrder] (C : Config) (n : FGState V) (A' : ACState V)
    (t : Time) (vbt : Finset (Block V)) (votes sv : Finset (GoldfishVote V)) (s : Slot)
    (H : Block V)
    -- `n`'s finalized block is its justified block or an ancestor of it
    (hFJ : n.F.AncestorEq n.J)
    -- the fork choice ends at `H`
    (h : goldfish_fork_choice C (fg_to_ac n) t (get_anchor A' (fg_to_ac n) t)
      (viable_tree (fg_to_ac n) vbt) votes sv s = .ok H) :
    n.F.AncestorEq H :=
  GoldilocksCorrectness.Proofs.Routines.vote_head_descends_of_F C n A' t vbt votes sv s H hFJ h

end

end GoldilocksCorrectness.Statements.Routines
