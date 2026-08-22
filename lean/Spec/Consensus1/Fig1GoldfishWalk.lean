import Spec.Consensus1.Store

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

## The arg-max step, and where the choice goes

Line 11 is `arg max score`, "ties by root order". The maximal-score children are a filter;
the tie-break is the ambient `TieBreak` class, an *unspecified* fixed choice (Roberto,
2026-08-22). The draft never says what a root is or how one is computed — Section 1 asks only
that the tie-break be fixed — so committing the Lean to `≤` on `B.root` claimed more than the
draft does, and a root order is one instance of the class.

A class is also what getting one block out of a `Finset` computably needs: `Finset.toList`
depends on `Classical.choice`, so a fold over it makes every caller `noncomputable` (measured
2026-08-21), and `Finset.min'` would want a `LinearOrder` on blocks, which the model has no
way to build — `Validator` carries no order.

## The walk raises

`TieBreak.pick` raises on the empty set instead of taking a nonemptiness proof (Roberto,
2026-08-22, replacing the proof-carrying `Selection.select`): no proof text at any call, and
the walk carries `ResultOrExcept` for it — and with the walk, every fork choice and duty that
runs one. Line 9 never hands `pick` an empty set, so the raise is unreachable in `ghost`;
that is a fact for `Analysis/`, not a hypothesis of the definition. One notation cost,
measured: the figure's `H ← arg max` cannot use the plain arrow, which the assignment macro
claims for pure re-assignment, so the monadic bind is written `H := (← bestChild …)`.

## The figure's `loop` gets a bound

The figure writes `loop … return H`, which terminates because each step moves to a child and
`tree` is finite. That argument is about the tree being a tree — parent-closed and acyclic —
which is an invariant of `Σ.T` rather than a fact about the `Finset` this routine takes. So
line 7's `loop` is written `for _ in [:tree.card]`: a descent through distinct blocks of
`tree` visits at most `tree.card` of them, so on anything that really is a tree the bound is
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

variable {Validator : Type}

/-! ## The shared walk -/

/-- The draft's tie-break: "ties use a fixed root order" (Section 1), assumed as an
    unspecified fixed choice rather than rendered — the draft never says what a root is or
    how one is computed, and a root order is one instance of this class.

    `pick s` is one member of `s`, or the failure on the empty set (Roberto, 2026-08-22).
    The subtype does most of the specifying: an `.ok` answer is a member by type, and on `∅`
    the failure is *forced* — `{B // B ∈ ∅}` has no inhabitants, so no total instance can
    answer `.ok` there. What the type cannot force is the converse, so `pick_ok` is a field:
    a nonempty set is never refused. A `Prop` field of a class is a definition component, not
    a `Spec/` theorem — the `Electorate.w_pos` precedent — and every instance owes its proof. -/
class TieBreak (Validator : Type) where
  /-- One member of `s`, or the failure on the empty set. -/
  pick : (s : Finset (Block Validator)) → ResultOrExcept {B // B ∈ s}
  /-- A nonempty set is never refused. -/
  pick_ok : ∀ s : Finset (Block Validator), s.Nonempty → ∃ B, pick s = .ok B

section Ghost
variable [DecidableEq Validator] [TieBreak Validator]

/-- Line 11's `arg max score`: the maximal-score members, the tie broken by the ambient
    `TieBreak.pick`. It raises exactly on empty `children` — the filter keeps a maximum
    whenever one exists, and `pick_ok` accepts anything nonempty — and `ghost`'s line 9
    never passes it an empty set. -/
def bestChild (children : Finset (Block Validator)) (score : Block Validator → Nat) :
    ResultOrExcept (Block Validator) := do
  let top := {B ∈ children | ∀ C ∈ children, score C ≤ score B}
  return (← TieBreak.pick top)

/-- `ghost(anchor, tree, score, eligible)` (Figure 1, lines 5–11): descend from `anchor`
    through eligible children in `tree`, taking the highest score at each step, and stop
    where no child is eligible. Ties are broken by the ambient `TieBreak`.

    The figure's `loop` is bounded by `tree.card`, and the result is `ResultOrExcept`
    because the tie-break raises — on a set line 9 keeps empty sets out of, so the raise is
    unreachable here. See the module header for both. -/
def ghost (anchor : Block Validator) (tree : Finset (Block Validator))
    (score : Block Validator → Nat) (eligible : Block Validator → Bool) :
    ResultOrExcept (Block Validator) := do
  let mut H := anchor                                          -- line 6
  for _ in [:tree.card] do                                     -- line 7: `loop`, bounded
    -- line 8: the eligible children of the block we stand on
    let children := {B ∈ tree | B.parent = ↑H ∧ eligible B}
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
variable [DecidableEq Validator] [Committees Validator] [TieBreak Validator]

/-- The validators of `K_s` that `votes` shows equivocating: two distinct votes by the same
    validator. Line 2 of `goldfish_score`, named because the score and the participant count
    both read it. -/
def equivocators (votes : Finset (GoldfishVote Validator)) (s : Nat) : Finset Validator :=
  {v ∈ (Committees.K s : Finset Validator) |
    ∃ a ∈ votes, ∃ b ∈ votes, a.validator = v ∧ b.validator = v ∧ a ≠ b}

/-- `goldfish_score(votes, s, B)` (Figure 1, lines 1–4): every equivocator, plus every
    non-equivocating participant whose target descends from `B`.

    An equivocator is counted without its target being read — see the module header. -/
def score (votes : Finset (GoldfishVote Validator)) (s : Nat) (B : Block Validator) : Nat :=
  let eq := equivocators votes s
  -- line 3: `{v ∈ K_s \ equivocators : (v, s, B') ∈ votes with B ⪯ B'}`
  let supporters := {v ∈ (Committees.K s : Finset Validator) \ eq |
    ∃ a ∈ votes, a.validator = v ∧ B ⪯ a.target}
  eq.card + supporters.card                                    -- line 4

/-- `voters_count = |{v ∈ K_s : votes holds a vote by v}|`: the participants `N_s(votes)` of
    Definition 2, as a count. Line 13 of `goldfish_eligible`, and line 5 of Figure 3's
    confirmation, which counts a *different* vote set against the same shape. -/
def votersCount (votes : Finset (GoldfishVote Validator)) (s : Nat) : Nat :=
  ({v ∈ (Committees.K s : Finset Validator) | ∃ a ∈ votes, a.validator = v}).card

/-- `goldfish_eligible(Σ, votes, s, B)` (Figure 1, lines 12–14): a strict majority of the
    participants support `B`, or `B` is a block of the current slot.

    The second disjunct is why a fresh proposal can be walked onto at all: "it only does not
    apply to proposals from the current slot, which cannot yet have votes". -/
def eligible (S : Store Validator) (votes : Finset (GoldfishVote Validator)) (s : Nat)
    (B : Block Validator) : Bool :=
  2 * score votes s B > votersCount votes s ∨ B.slot = S.s   -- line 14

/-- `goldfish_fork_choice(Σ, anchor, tree, votes, s)` (Figure 1, lines 15–16): the shared
    walk, instantiated with the Goldfish score and gate. -/
def forkChoice (S : Store Validator) (anchor : Block Validator)
    (tree : Finset (Block Validator)) (votes : Finset (GoldfishVote Validator)) (s : Nat) :
    ResultOrExcept (Block Validator) :=
  ghost anchor tree (score votes s) (eligible S votes s)       -- line 16

/-- `get_head(Σ, votes, s)` (Figure 1, lines 17–18): the walk from genesis over the whole
    processed tree.

    This is the Goldfish layer's head. Figure 4 redefines it to start from the SG root, and
    Figure 7 again to start from the fork-choice root over the filtered tree; see the module
    header on the namespaces. -/
def getHead (S : Store Validator) (votes : Finset (GoldfishVote Validator)) (s : Nat) :
    ResultOrExcept (Block Validator) :=
  forkChoice S .genesis S.T votes s                            -- line 18

end Score

end Goldfish

end Consensus1
