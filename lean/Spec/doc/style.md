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
  `S ⇐ S.updateConfirmation (s − 1)`, `H ⇐ bestChild …` — binding the value and supplying
  an `Option` field's wrapper by coercion, so in the Lean the arrowhead is what says the step
  picks or raises. Three arrows: `←` re-assigns, `⇐` binds, `←ᵖ` picks. The distinction is
  Lean's: the extracted document writes `←` for both of the first two, as the draft does.
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
  the routine is about comes last (`process_block`, `07_FGStore.lean`). A figure whose own
  case cascade returns different answers case by case — `height_pair`,
  `08_FinalityVote.lean` — renders its cases in the figure's order; the ruling is about
  rejection-and-fallback shapes, not the protocol's case analyses.
- **A set-builder condition with nested bounded quantifiers is a named predicate** — an
  inline one loses the decidability search at `def` level (measured, on the old per-round
  `Option` maps), so the condition gets a name and a keyed `Decidable` instance
  (`Store.summarySupports`, `Store.equivBefore`, `09_Healing.lean`). Over a `Finset`, the
  inline `∃` stays (`04_SGForkChoice.lean`).
- **No existential quantifier over an `Option`.** Not `∃ x ∈ o, …`, not
  `∃ x, o = some x ∧ …`: test `o ≠ ⊥` and read the value through an extraction (the lift,
  the bracket, `Option.value`), or use the `∀`-bounded form where only a constraint on
  the value is meant.
- **Absence is tested `x ≠ ⊥`, never `.isSome`**, and in a raising body the branch
  extracts by the lift: `let y ← x`, value or raise (the scoped
  `MonadLift Option DRE`, `Raise.lean`) — behind the `≠ ⊥` test the raise is
  unreachable. Every extraction in a monadic body is that lift; a *pure* body extracts
  with the site-checked `Option.value` (`Raise.lean`) inside a dependent
  `if _ : x ≠ ⊥`. The store's map
  machinery keeps `.isSome` internally; the rule is about spec bodies.
- **No `∣` (divides)**: write `% … = 0`.
- **A projection is the image comprehension**: `{e.vote | e ∈ S.gfVotes s}`, and with
  a condition `{e.vote | e ∈ S.gfVotes s, e.time < c}` — Python's set comprehension
  (`Notation.lean`), expanding to `Finset.map'` (`FinsetM.lean`), `image` under the name
  a programmer expects. No bare `Finset.image` and no `biUnion` in spec bodies — a union
  the protocol needs is a vocabulary definition a spec body reads by name
  (`Store.allAttestations`, `Defs/Store.lean`); the
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
  from each action branch directly (`Store.goldfishOnTick`; `Store.onTick`,
  `11_Duties.lean`, runs it among its own lines).
- **Scheduled routines carry their instant as an anonymous autoparam**, discharged by
  `solve_by_elim [And.left, And.right]`, so `Store.onTick`'s dependent `if`s satisfy them
  with no `have`s (`11_Duties.lean` explains the tactic choice).

## The ambient environment

- **Classes, not type parameters**: `Electorate`, `Committees`, `Proposers`, `Params`,
  `BlockIds` (the abstract identifier type, its equality and its order — the lex
  comparison's tie-break, blocks carrying no root), `BlockIdentity` (the injective `id`),
  `SGSchedule` (the attestation times `sgfgVoting i r`, no formula
  fixed, bounded to `a_r ≤ sgfgVoting i r < roundStart (r + 1)`) — all in `Model.lean`.

- **A routine that inserts between another's lines is written out, from named halves.**
  The tick's lines interleave the slot's actions with the round's, so its two reusable
  halves are routines of their own — `set_clock`, which the tick begins with, and
  `goldfish_on_tick`, the slot's actions, which reads the clock rather than taking the
  time — and `Store.onTick` calls them with its own lines in place (`11_Duties.lean`).
  The draft prints `on_tick` whole; this is that, with the repeated halves named instead
  of copied.
  The round's fixed instant is a bare definition, not a field of that class —
  `heightDecisionTime r = roundStart r + 6Δ`, the protocol's `a_r` — because the formula is
  fixed and no instance may move it, and because taking `[Params]` alone lets a routine test
  it without carrying the class.

## Comments and citations

- **Line comments say what a statement does, not where it sits** — the rendered figure
  shows them as margin notes, and nothing numbers the lines.
- **Docstrings are self-contained and cite nothing** — every docstring says what its
  definition means on its own (correctness is the contract).

## Retired machinery

- **`OldDefs.lean` parks what lost its consumers** (the `for all`-era macros, the `ForIn`
  over `Finset`). Nothing under `Spec/` may import it; revive a definition by
  moving it out.
