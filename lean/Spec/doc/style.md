# The remaining style rulings

One line per ruling, with a pointer to where the mechanics live. The two large ones —
nondeterminism and naming — have their own pages. The running list, with dates and
reasoning, is `CONTEXT.md`'s "The `DC` style sheet".

## Reads and failure

- **Raise, never answer silently.** A map read whose key may be absent is a raising
  bracket: `S.σ[B]` (`Store.lean`). The stored votes carry their own times
  (`TimestampedVote`), so no rule reads a timestamp map any more — that bracket read is
  parked in `OldDefs.lean`. The raw `Option` stays reachable by applying the field
  directly.
- **Set operations over raising reads go through `filterM`/`imageM`** (`FinsetM.lean`), or
  the raising set-builder below.

## Notation (`Notation.lean`, `Nondet.lean`)

- Assignment arrows render the figures' `←`, including bare identifiers, two-level map
  writes, and the pair form. **`⇐` is the assignment whose right-hand side computes** —
  `Σ.sg_root[r] ⇐ get_sg_root(Σ, r)`, `H ⇐ bestChild …` — binding the value and supplying
  an `Option` field's wrapper by coercion, so the arrowhead is what says the step picks or
  raises. Three arrows: `←` re-assigns, `⇐` binds, `←ᵖ` picks.
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
- **`return`s do not alternate.** Read top to bottom, once the returned value changes it
  never changes back: each rejection returns the fallback in its own `if`, and the value
  the routine is about comes last (`get_round_root`, `09_Healing.lean`).
- **A set-builder condition over an `Option` entry is a named predicate** — the inline
  `∃ e ∈ Σ.head[k][i], …` loses the decidability search at `def` level (measured), so the
  condition gets a name and a keyed `Decidable` instance (`Store.headSupports`,
  `Store.equivBefore`, `09_Healing.lean`). Over a `Finset`, the inline `∃` stays
  (`04_SGForkChoice.lean`).
- **Absence is tested `x ≠ ⊥`, never `.isSome`**, and in a raising body the branch
  extracts by the lift: `let y ← x`, value or raise (the scoped
  `MonadLift Option DRE`, `Raise.lean`) — behind the `≠ ⊥` test the raise is
  unreachable. Every extraction in the spec is that lift; the site-checked alternative
  for a *pure* body, `Option.value`, is parked in `OldDefs.lean`. The store's map
  machinery keeps `.isSome` internally; the rule is about spec bodies.
- **No `∣` (divides)**: write `% … = 0`.
- **A projection is the image comprehension**: `{e.vote | e ∈ S.gfVotes s}`, and with
  a condition `{e.vote | e ∈ S.gfVotes s, e.time < c}` — Python's set comprehension
  (`Notation.lean`), expanding to `Finset.map'` (`FinsetM.lean`), `image` under the name
  a programmer expects. No bare `Finset.image` and no `biUnion` in spec bodies; the
  unprimed `Finset.map` takes an embedding and cannot project; the raising fold `imageM`
  is unaffected.
- **What the protocol writes inline stays inline.** `voters_count` and the equivocator
  set are `let`s at each use site — locals, not definitions.
- **Explicit coercion where a `mut` read blocks insertion**: `B.parent = ↑H` — the `=`
  elaborator inserts no coercion around a mutable variable's read.

## Signatures

- **Function-typed fields and parameters name their binders** —
  `head : (r : Int) → (i : Validator) → Option …`,
  `score : (B : Block Validator) → Nat` — so a docstring can name what it talks about.
  The pattern-matching accessors (`Block.parent` and kin) have no binder position and
  stay as they are.

## Messages and duties

- **Messages are built by named `mk`**: `GoldfishVote.mk (validator := i) …`, and
  `Block.mk` likewise names its fields (`Store.proposeBlock`). `DutyResult` keeps the brace
  form `{ state := …, send := … }`.
- **Duties run in `NDREB`** (`Nondet.lean`): the outbox threaded over `NDRE`,
  `broadcast` the protocol's own verb, the store an explicit input and output — no caller
  ever unions sends, an earlier duty's broadcasts already sitting in the outbox when a
  later one runs. `DutyResult` survives only at the boundary: `NDREB.outcomes` is the
  outcome set the sts wiring ([sts.md](sts.md)) and `Analysis/` consume a duty as. The tick still returns
  from each action branch directly (`Fig2.onTick`; the protocol's `Store.onTick` runs it
  and then the SG layer's added line, `05_SGDuty.lean`).
- **Scheduled routines carry their instant as an anonymous autoparam**, discharged by
  `solve_by_elim [And.left, And.right]`, so `Store.onTick`'s dependent `if`s satisfy them
  with no `have`s (`02_GoldfishDuties.lean` explains the tactic choice).

## The ambient environment

- **Classes, not type parameters**: `Electorate`, `Committees`, `Params`, `Roots` (the
  abstract `Root` type, its order, genesis's root), `RootComputation` (a block's root from
  its parent and slot), `SGSchedule` (the attestation times `sgfgVoting i r`, no formula
  fixed, bounded to `a_r ≤ sgfgVoting i r < roundStart (r + 1)`) — all in `Model.lean` —
  and `GoldfishWalk` (`Defs/GoldfishWalk.lean`), the anchor, the blocks and the
  eligibility condition that `get_head` takes from the layer, with exactly one instance,
  supplied by the layer whose readings are the protocol's.
  The SG vote time `a_r` is a definition in the class's own namespace, not a field —
  `SGSchedule.a r = roundStart r + 6Δ` — so the whole round schedule reads `SGSchedule.…`.

## Comments and citations

- **Line comments say what a statement does, not where it sits** — the rendered figure
  shows them as margin notes, and nothing numbers the lines.
- **Docstrings are self-contained and cite nothing** — every docstring says what its
  definition means on its own (correctness is the contract).

## Retired machinery

- **`OldDefs.lean` parks what lost its consumers** (the `for all`-era macros, the `ForIn`
  over `Finset`). Nothing under `Spec/` may import it; revive a definition by
  moving it out.
