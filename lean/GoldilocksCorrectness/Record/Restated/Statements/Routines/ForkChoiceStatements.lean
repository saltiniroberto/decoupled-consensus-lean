module
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ForkChoiceFacts
public import GoldilocksCorrectness.Statements.Routines.ForkChoiceStatements

@[expose] public section

/-!
# ForkChoiceStatements, over a model: the head of a Goldfish vote

The statements of `GoldilocksCorrectness/Statements/Routines/ForkChoiceStatements.lean` over a model
`M` whose facts `F` hold: at a node state justified past `B`, the end of the Goldfish walk is
compatible with `B`; and the end of the Goldfish walk is the voter's finalized block or a
descendant of it. The Goldfish fork choice is not a member of the record: the walk is given by walk
steps of the library predicate `WalkStep` at the model's tie-break `M.tieBreak`, from a start that
is the fgroot or a block of the viable tree of the frame's tree (the landed statements start from
the anchor of any AC state, which is such a block). Proved on
`Record/Restated/Proofs/Routines/ForkChoiceFacts.lean`.

The recovery section at the end of the page states each landed theorem again, as the landed
statement (`type_of%`) at the FG state `n.S` of a node state `n` satisfying the spec's model's node
invariant, and proves it from its record form at the spec's model `Model.goldilocks` and its facts
`goldilocksFacts`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Statements.Routines

open Goldilocks
open GoldilocksCorrectness.Record
open GoldilocksCorrectness.Statements.Routines (WalkStep)

variable {V : Type} [DecidableEq V] [Fintype V]

section

variable (M : GoldilocksModel V) (F : Facts M)
include M F

/-- **The head of a Goldfish vote is compatible with `B` at a node justified past `B`.** The walk
from a start that is the fgroot or a block of the viable tree of the frame's tree, through the
viable tree of any tree `vbt`, with the Goldfish score and eligibility test, at the model's
tie-break, ends at a block compatible with `B`, when `n`'s justified block is compatible with `B`
and has the chain-state height `n.justifiedHeight`, `n.finalized` is an ancestor of `n.justified`
or it, the blocks of `n`'s tree two heights past `B` descend from `B`,
`n.justifiedHeight < hMax M C n` and `h(B) + 1 ≤ n.justifiedHeight`.

Why: every viable head descends from `B`, so every block of a viable tree, and the fgroot, are
compatible with `B`; the walk ends at its start or at a block of the viable tree it walks.

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the given values, the digest; `n`: the node state;
- `hI`: `n` satisfies the model's node invariant; `B`: the block; `A₀`: the start of the walk;
  `t`: the time; `vbt`: the voter tree; `votes`, `sv`: the votes and the support votes; `s`: the
  slot; `H`: the end of the walk.

Read aloud: at a node justified past `B` whose caches are compatible with `B`, the head of any
Goldfish vote it computes is compatible with `B`. -/
theorem vote_head_compatible_of_justified_past [RootOrder] (C : Config) (P : Provisional V)
    (X : External V) (n : M.N)
    -- `n` satisfies the model's node invariant
    (hI : M.nodeInv C P X n) (B : Block V)
    -- `n`'s justified block is compatible with `B`, at the height `n.justifiedHeight`
    (hJ : n.justified.AncestorEq B ∨ B.AncestorEq n.justified)
    (hJh : (M.chainStateOf C n.justified).h = n.justifiedHeight)
    -- `n`'s finalized block is its justified block or an ancestor of it
    (hFJ : n.finalized.AncestorEq n.justified)
    -- the blocks of `n`'s tree two heights past `B` descend from `B`
    (hTwo : ∀ D ∈ n.tree, (M.chainStateOf C B).h + 2 ≤ (M.chainStateOf C D).h → B.AncestorEq D)
    -- `n.justifiedHeight < hMax M C n` and `h(B) + 1 ≤ n.justifiedHeight`
    (hjmax : n.justifiedHeight < hMax M C n)
    (hSafe : (M.chainStateOf C B).h + 1 ≤ n.justifiedHeight)
    -- the start of the walk is the fgroot or a block of the viable tree of the frame's tree
    (A₀ : Block V)
    (hA₀ : A₀ = (M.fg_to_ac n).fc_root ∨ A₀ ∈ M.viable_tree (M.fg_to_ac n) (M.fg_to_ac n).tree)
    (t : Time) (vbt : Finset (Block V)) (votes sv : Finset (GoldfishVote V)) (s : Slot)
    (H : Block V)
    -- walk steps at the model's tie-break lead from `A₀` to `H`
    (h : Relation.ReflTransGen (@WalkStep V M.tieBreak (M.viable_tree (M.fg_to_ac n) vbt)
      (goldfish_score (M.fg_to_ac n) votes sv s) (goldfish_eligible C (M.fg_to_ac n) t votes sv s))
      A₀ H) :
    H.compatible B = true :=
  GoldilocksCorrectness.Record.Proofs.Routines.vote_head_compatible_of_justified_past M F C P X n
    hI B hJ hJh hFJ hTwo hjmax hSafe A₀ hA₀ t vbt votes sv s H h

/-- **The head of a Goldfish vote descends from the voter's finalized block.** The walk from a
start that is the fgroot or a block of the viable tree of the frame's tree, through the viable tree
of any tree `vbt`, with the Goldfish score and eligibility test, at the model's tie-break, ends at
`n.finalized` or a descendant of it, when `n.finalized` is an ancestor of `n.justified` or it.

Why: the walk ends at its start or at a block of the viable tree it walks; every block of a viable
tree is the fgroot or a descendant of it, and the fgroot is `n.justified` or `n.finalized`.

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the given values, the digest; `n`: the node state;
- `hI`: `n` satisfies the model's node invariant; `A₀`: the start of the walk; `t`: the time;
  `vbt`: the voter tree; `votes`, `sv`: the votes and the support votes; `s`: the slot; `H`: the
  head.

Read aloud: the head of a Goldfish vote is the voter's finalized block or a descendant of it. -/
theorem vote_head_descends_of_F [RootOrder] (C : Config) (P : Provisional V) (X : External V)
    (n : M.N)
    -- `n` satisfies the model's node invariant
    (hI : M.nodeInv C P X n)
    -- `n`'s finalized block is its justified block or an ancestor of it
    (hFJ : n.finalized.AncestorEq n.justified)
    -- the start of the walk is the fgroot or a block of the viable tree of the frame's tree
    (A₀ : Block V)
    (hA₀ : A₀ = (M.fg_to_ac n).fc_root ∨ A₀ ∈ M.viable_tree (M.fg_to_ac n) (M.fg_to_ac n).tree)
    (t : Time) (vbt : Finset (Block V)) (votes sv : Finset (GoldfishVote V)) (s : Slot)
    (H : Block V)
    -- walk steps at the model's tie-break lead from `A₀` to `H`
    (h : Relation.ReflTransGen (@WalkStep V M.tieBreak (M.viable_tree (M.fg_to_ac n) vbt)
      (goldfish_score (M.fg_to_ac n) votes sv s) (goldfish_eligible C (M.fg_to_ac n) t votes sv s))
      A₀ H) :
    n.finalized.AncestorEq H :=
  GoldilocksCorrectness.Record.Proofs.Routines.vote_head_descends_of_F M F C P X n hI hFJ A₀ hA₀ t
    vbt votes sv s H h

end

/-! ## At the spec's model -/

/-- The landed `GoldilocksCorrectness.Statements.Routines.vote_head_compatible_of_justified_past`,
recovered from its record form at the spec's model, at the FG state `n.S` of every node state `n`
satisfying the spec's model's node invariant: the landed walk starts from the anchor of any AC
state `A'`, the fgroot or a block of the viable tree (`get_anchor_cases_viable`), and its answer is
reached by walk steps at the Goldilocks tie-break (`walkSteps_of_ghost_eq_ok`).

Read aloud: the landed `vote_head_compatible_of_justified_past` holds at the FG state of every node
state satisfying the invariant. -/
theorem vote_head_compatible_of_justified_past_recovered {V : Type} [DecidableEq V] [Fintype V]
    [RootOrder] :
    ∀ (C : Config) (P : Provisional V) (X : External V) (n : NodeState V),
      (Model.goldilocks (V := V)).nodeInv C P X n →
      type_of% (@GoldilocksCorrectness.Statements.Routines.vote_head_compatible_of_justified_past V
        _ _ _ C n.S) := by
  intro C P X n hI B _ hJ hJh hFJ hTwo hjmax hSafe A' t vbt votes sv s H h
  rw [GoldilocksCorrectness.Proofs.Routines.goldfish_fork_choice_eq] at h
  exact vote_head_compatible_of_justified_past Model.goldilocks goldilocksFacts C P X n hI B hJ hJh
    hFJ hTwo (by rw [hMax_goldilocks hI]; exact hjmax) hSafe (get_anchor A' (fg_to_ac n.S) t)
    (GoldilocksCorrectness.Proofs.Routines.get_anchor_cases_viable A' (fg_to_ac n.S) t) t vbt
    votes sv s H (GoldilocksCorrectness.Proofs.Routines.walkSteps_of_ghost_eq_ok h)

/-- The landed `GoldilocksCorrectness.Statements.Routines.vote_head_descends_of_F`, recovered from
its record form at the spec's model, at the FG state `n.S` of every node state `n` satisfying the
spec's model's node invariant, as `vote_head_compatible_of_justified_past_recovered`.

Read aloud: the landed `vote_head_descends_of_F` holds at the FG state of every node state
satisfying the invariant. -/
theorem vote_head_descends_of_F_recovered {V : Type} [DecidableEq V] [Fintype V] [RootOrder] :
    ∀ (C : Config) (P : Provisional V) (X : External V) (n : NodeState V),
      (Model.goldilocks (V := V)).nodeInv C P X n →
      type_of% (@GoldilocksCorrectness.Statements.Routines.vote_head_descends_of_F V _ _ _ C
        n.S) := by
  intro C P X n hI A' t vbt votes sv s H hFJ h
  rw [GoldilocksCorrectness.Proofs.Routines.goldfish_fork_choice_eq] at h
  exact vote_head_descends_of_F Model.goldilocks goldilocksFacts C P X n hI hFJ
    (get_anchor A' (fg_to_ac n.S) t)
    (GoldilocksCorrectness.Proofs.Routines.get_anchor_cases_viable A' (fg_to_ac n.S) t) t vbt
    votes sv s H (GoldilocksCorrectness.Proofs.Routines.walkSteps_of_ghost_eq_ok h)

end GoldilocksCorrectness.Record.Statements.Routines
