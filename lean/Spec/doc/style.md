# The remaining style rulings

One line per ruling, with a pointer to where the mechanics live. The two large ones —
nondeterminism and naming — have their own pages. The running list, with dates and
reasoning, is `CONTEXT.md`'s "The `Consensus1` style sheet".

## Reads and failure

- **Raise, never answer silently.** A map read whose key may be absent is a raising
  bracket: `S.σ[B]`, and the three timestamp fields via `TimeMap` (`Store.lean`). The raw
  `Option` stays reachable by applying the field directly.
- **Set operations over raising reads go through `filterM`/`imageM`** (`FinsetM.lean`), or
  the raising set-builder below.

## Notation (`Notation.lean`, `Nondet.lean`)

- Assignment arrows render the figures' `←`, including bare identifiers, two-level map
  writes, and the pair form.
- `|s|` is `Finset.card`. Cost: the `abs` bars are shadowed inside the namespace.
- `let y ← {x ∈ᴹ s | p}` is the raising set-builder — a filter whose condition may raise.
  It is a `doElem` macro, necessarily: a term-macro form loses the inner `←` to the outer
  `do` before the macro expands. Its expansion pins `DRE`, so it lifts whole
  inside `NDRE`.
- `let x ←ᵖ s` is the nondeterministic pick (see [nondeterminism.md](nondeterminism.md)).

## Spec bodies

- **No `match` and no `|` alternatives.** The dependent `if` idiom instead, binding `_`
  unless the hypothesis's name is used. A `for`-range bound is the tolerated recursion
  shape (`ghost`'s loop).
- **Absence is tested `x ≠ ⊥`, never `.isSome`**, and in a raising body the branch
  extracts by the lift: `let y ← x`, value or raise (the scoped
  `MonadLift Option DRE`, `Raise.lean`) — behind the `≠ ⊥` test the raise is
  unreachable. The store's map machinery keeps `.isSome` internally; the rule is about
  spec bodies. (An autoparam extraction for *pure* bodies, `Option.value`, is parked in
  `OldDefs.lean`.)
- **No `∣` (divides)**: write `% … = 0`.
- **What the protocol writes inline stays inline.** `voters_count` and the equivocator
  set are `let`s at each use site — locals, not definitions.
- **Explicit coercion where a `mut` read blocks insertion**: `B.parent = ↑H` — the `=`
  elaborator inserts no coercion around a mutable variable's read.

## Messages and duties

- **Messages are built by named `mk`**: `GoldfishVote.mk (validator := i) …`, and
  `Block.mk` likewise names its fields (Figure 2, line 25). `DutyResult` keeps the brace
  form `{ state := …, send := … }`.
- **Duties run in `NDREB`** (`Nondet.lean`): the outbox threaded over `NDRE`,
  `broadcast` the protocol's own verb, the store an explicit input and output — no caller
  ever unions sends, an earlier duty's broadcasts already sitting in the outbox when a
  later one runs. `DutyResult` survives only at the boundary: `NDREB.outcomes` is the
  outcome set the sts wiring and `Analysis/` consume a duty as. The tick still returns
  from each action branch directly (`Fig2.onTick`; the protocol's `Store.onTick` runs it
  and then the SG layer's added line, `Fig5SGDuty.lean`).
- **Scheduled routines carry their instant as an anonymous autoparam**, discharged by
  `solve_by_elim [And.left, And.right]`, so `Store.onTick`'s dependent `if`s satisfy them
  with no `have`s (`Fig2GoldfishDuties.lean` explains the tactic choice).

## The ambient environment

- **Classes, not type parameters**: `Electorate`, `Committees`, `Params`, `Roots` (the
  abstract `Root` type, its order, genesis's root), `RootComputation` (a block's root from
  its parent and slot), `SGSchedule` (the instants `a_r`). All in `Model.lean`.

## Comments and citations

- **Line comments cite the figure's own line numbers** (`-- line 25`).
- **Docstrings are self-contained and cite nothing** — every docstring says what its
  definition means on its own (correctness is the contract).

## Retired machinery

- **`OldDefs.lean` parks what lost its consumers** (the `for all`-era macros, the `ForIn`
  over `Finset`). Nothing under `Spec/` may import it; revive a definition by
  moving it out.
