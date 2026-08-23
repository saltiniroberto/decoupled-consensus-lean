import Spec.Consensus1.Store
import Spec.Consensus1.Nondet

/-!
# Figure 1 — the Goldfish score and the walk

Definition 2 and Figure 1: `goldfish_score`, `ghost`, `goldfish_eligible`,
`goldfish_fork_choice` and `get_head`. `ghost` is the draft's one building block — "throughout
this document, we use this as a building block" — and every later fork choice is the same
walk with a different score and gate.

The `-- line n` comments use Figure 1's own line numbering, in the draft as of 2026-08-22.

## The layers rename nothing, so the layers are namespaces

Figure 4 and Figure 7 each redefine `get_head`, and Figure 7 redefines `goldfish_eligible`
and `process_block`. The draft can do that because each section *replaces* the previous
reading; Lean cannot, so each layer's routine sits in its own namespace —
`Consensus1.Goldfish`, `Consensus1.SG`, `Consensus1.FG` — and the protocol is the last one. A
reader comparing against the draft reads one namespace at a time; a caller wanting "the" fork
choice wants `FG.getHead`.

`ghost` itself is not in a layer namespace: it is the shared building block, and no section
redefines it.

Everything that takes a store sits in `namespace Store`, and a name whose draft prefix the
layer namespace carried spells it itself there (`S.goldfishForkChoice`, `S.sgSupport`) —
so a caller writes `S.updateConfirmation k`, `S.goldfishForkChoice …`, `S.viable` (Roberto,
2026-08-23). The one exception is forced: names *two* layers claim — `get_head` (three),
`process_block` (two), `goldfish_eligible` (two) — cannot share one namespace, so the
protocol's readings bear the `Store` names (`S.getHead`, `S.goldfishEligible` are
Figure 7's) and the superseded readings keep `Goldfish`/`SG`.

## The arg-max step: the tie is a pick

Line 11 is `arg max score`, "ties by root order". The maximal-score children are a filter;
the tie is a **nondeterministic pick**, `←ᵖ` (Roberto, 2026-08-23, ending the chooser-class
line: `Selection`, then `TieBreak`, are gone). The draft never says what a root is or how one
is computed — Section 1 asks only that the tie-break be fixed — so nothing is assumed at all:
every resolution is among the outcomes, a root order being one of them, and "the walk does
not depend on the tie" is a provable singleton statement, not a precondition.

## The walk is `NDRE`

The tie-break picks and the eligibility condition may raise — Figure 7's reads `Σ.σ[B].h` —
so the walk carries `NDRE`, and its `eligible` parameter is `Block → ResultOrExcept Bool`:
the raising layer passes its condition directly (the deviation this closed is recorded in
`CONTEXT.md`), and the pure layers offer theirs with `pure`. Line 8 filters the children
through `Finset.filterM` at `ResultOrExcept`, whose fold instances exist; a per-child
condition in `NDRE` itself would not commute (a pick with no outcomes annihilates where an
error survives), which is why the parameter type is the raising monad, not the full stack.
One notation cost, measured: the figure's `H ← arg max` cannot use the plain arrow, which
the assignment macro claims for pure re-assignment, so the monadic bind is written
`H := (← bestChild …)`.

## The figure's `loop` gets a bound

The figure writes `loop … return H`, which terminates because each step moves to a child and
`tree` is finite. That argument is about the tree being a tree — parent-closed and acyclic —
which is an invariant of `Σ.T` rather than a fact about the `Finset` this routine takes. So
line 7's `loop` is written `for _ in [:|tree|]`: a descent through distinct blocks of
`tree` visits at most `|tree|` of them, so on anything that really is a tree the bound is
never reached and the `for` runs exactly the figure's `loop`.

What the bound costs is one reachable case the draft does not have: the iterations run out
with an eligible child still available, and the routine returns the block it stands on — the
same answer the figure gives when no child is eligible. `Analysis/` is where "the bound is
never reached on a real tree" belongs. The alternative — a well-founded recursion on the set
of strict descendants — needs the tree invariant in the *definition*, and `Spec/` is not the
place to assume it.

## The score counts equivocators for every block

Definition 2: an equivocator "counts for every block and stays among the participants, so it
can neither create nor block a descent". That is why line 2 collects them separately and line
4 adds both cardinalities: a validator with two votes is added to every block's score without
its target being read at all.
-/

set_option autoImplicit false

namespace Consensus1

variable {Validator : Type} [Roots]

/-! ## The shared walk -/

section Ghost
variable [DecidableEq Validator]

/-- Line 11's `arg max score`: the maximal-score members, the tie a genuine pick — every
    resolution among the outcomes, a root order being one. On empty `children` there are no
    outcomes at all, an answer `ghost`'s line 9 never asks for. -/
def bestChild (children : Finset (Block Validator)) (score : Block Validator → Nat) :
    NDR (Block Validator) := do
  let top := {B ∈ children | ∀ C ∈ children, score C ≤ score B}
  let W ←ᵖ top
  return W

/-- `ghost(anchor, tree, score, eligible)` (Figure 1, lines 5–11): descend from `anchor`
    through eligible children in `tree`, taking the highest score at each step, and stop
    where no child is eligible. The tie at each step is a pick; the eligibility condition
    may raise. See the module header on both, and on why `eligible` is `ResultOrExcept`
    rather than the full stack.

    The figure's `loop` is bounded by `|tree|`. -/
def ghost (anchor : Block Validator) (tree : Finset (Block Validator))
    (score : Block Validator → Nat) (eligible : Block Validator → ResultOrExcept Bool) :
    NDRE (Block Validator) := do
  let mut H := anchor                                          -- line 6
  for _ in [:|tree|] do                                        -- line 7: `loop`, bounded
    -- line 8: the eligible children of the block we stand on; the filter runs at
    -- `ResultOrExcept` — the ascription keeps the stack out of it — and lifts whole
    let children ← (({B ∈ tree | B.parent = ↑H}).filterM eligible :
      ResultOrExcept (Finset (Block Validator)))
    if children = ∅ then                                       -- line 9
      return H                                                 -- line 10
    -- line 11: `H ← arg max score`; the plain arrow is the assignment macro's, so the
    -- monadic bind is written through `:=`
    H := (← bestChild children score)
  return H  -- the bound is reached: not a figure line, see the module header

end Ghost

namespace Goldfish

/-! ## The Goldfish score and gate -/

section Score
variable [DecidableEq Validator] [Committees Validator]

/-- The validators of `K_s` that `votes` shows equivocating: two distinct votes by the same
    validator. Line 2 of `goldfish_score`, named because the score and the participant count
    both read it. -/
def equivocators (votes : Finset (GoldfishVote Validator)) (s : Nat) : Finset Validator :=
  {v ∈ Committees.K s |
    ∃ a ∈ votes, ∃ b ∈ votes, a.validator = v ∧ b.validator = v ∧ a ≠ b}

/-- `goldfish_score(votes, s, B)` (Figure 1, lines 1–4): every equivocator, plus every
    non-equivocating participant whose target descends from `B`.

    An equivocator is counted without its target being read — see the module header. -/
def score (votes : Finset (GoldfishVote Validator)) (s : Nat) (B : Block Validator) : Nat :=
  let eq := equivocators votes s
  -- line 3: `{v ∈ K_s \ equivocators : (v, s, B') ∈ votes with B ⪯ B'}`
  let supporters := {v ∈ Committees.K s \ eq |
    ∃ a ∈ votes, a.validator = v ∧ B ⪯ a.target}
  |eq| + |supporters|                                          -- line 4

/-- `voters_count = |{v ∈ K_s : votes holds a vote by v}|`: the participants `N_s(votes)` of
    Definition 2, as a count. Line 13 of `goldfish_eligible`, and line 5 of Figure 3's
    confirmation, which counts a *different* vote set against the same shape. -/
def votersCount (votes : Finset (GoldfishVote Validator)) (s : Nat) : Nat :=
  |{v ∈ Committees.K s | ∃ a ∈ votes, a.validator = v}|

/-- `goldfish_eligible(Σ, votes, s, B)` (Figure 1, lines 12–14): a strict majority of the
    participants support `B`, or `B` is a block of the current slot.

    The second disjunct is why a fresh proposal can be walked onto at all: "it only does not
    apply to proposals from the current slot, which cannot yet have votes". -/
def eligible (S : Store Validator) (votes : Finset (GoldfishVote Validator)) (s : Nat)
    (B : Block Validator) : Bool :=
  2 * score votes s B > votersCount votes s ∨ B.slot = S.s   -- line 14

end Score

end Goldfish

namespace Store

section Score
variable [DecidableEq Validator] [Committees Validator]

/-- `goldfish_fork_choice(Σ, anchor, tree, votes, s)` (Figure 1, lines 15–16): the shared
    walk, instantiated with the Goldfish score and eligibility condition. In `Store` with
    the draft's own prefix — the layer namespace no longer carries it. -/
def goldfishForkChoice (S : Store Validator) (anchor : Block Validator)
    (tree : Finset (Block Validator)) (votes : Finset (GoldfishVote Validator)) (s : Nat) :
    NDRE (Block Validator) :=
  -- line 16; the pure condition offered to the walk's raising slot with `pure`
  ghost anchor tree (Goldfish.score votes s) (fun B => pure (Goldfish.eligible S votes s B))

end Score

end Store

namespace Goldfish

section Score
variable [DecidableEq Validator] [Committees Validator]

/-- `get_head(Σ, votes, s)` (Figure 1, lines 17–18): the walk from genesis over the whole
    processed tree.

    This is the Goldfish layer's head. Figure 4 redefines it to start from the SG root, and
    Figure 7 again to start from the fork-choice root over the filtered tree; see the module
    header on the namespaces. -/
def getHead (S : Store Validator) (votes : Finset (GoldfishVote Validator)) (s : Nat) :
    NDRE (Block Validator) :=
  S.goldfishForkChoice .genesis S.T votes s                    -- line 18

end Score

end Goldfish

end Consensus1
