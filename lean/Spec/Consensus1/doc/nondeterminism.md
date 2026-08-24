# Nondeterminism: `NDR`, `NDRE`, and the pick

## The problem

The draft's pseudocode makes choices it does not determine. `best_child` (Figure 1) breaks
a score tie arbitrarily. `propose_block` (Figure 2, line 25) writes a set of votes into a
block field that is a list, without saying in which order. A deterministic rendering would
have to invent a resolution for both — an assumption the draft does not make, and one every
theorem downstream would silently depend on.

`Spec/Consensus1/` renders these choices as genuine nondeterminism. A routine that makes a
choice returns the **set of all its possible outcomes**, one outcome per combination of
choices. No representative is ever picked, so no theorem can depend on one. "The choice
does not matter" stops being an assumption and becomes a provable statement: the outcome
set is a singleton.

## The two monads

`Nondet.lean` defines the vocabulary. Two reducible abbreviations:

```lean
abbrev NDR  (α : Type) := Set α                    -- choices only
abbrev NDRE (α : Type) := ExceptT Error Set α      -- choices and raising reads
```

In plain words: an `NDR α` value *is* the set of possible answers. An `NDRE α` value,
unwrapped with `.run`, is definitionally a `Set (DRE α)` — each element either
an answer or the failure, an error path cut short exactly as a plain `DRE`
computation would cut it. (`DRE α` is `Except Error α`, from `Raise.lean`: the
type of a computation that may raise instead of answering, used for reads like `S.σ[B]`
where the key may be absent.)

`do` notation works in both: Mathlib's `Set.monad` instance is opt-in, and `Nondet.lean`
activates it scoped.

## The four tiers

A routine takes the weakest type that fits what it does:

| It…                        | Return type        | Examples |
| -------------------------- | ------------------ | -------- |
| neither raises nor chooses | plain value        | `Store.processGoldfishVote`, `Store.sgVote` |
| raises, never chooses      | `DRE α` | `Store.viable`, `Store.processBlock` |
| chooses, never raises      | `NDR α`            | `bestChild` |
| both                       | `NDRE α`           | `ghost`, `Store.getHead` |

The duties sit one layer up: `DutyM α` (`Duty.lean`) is the broadcast outbox threaded
over `NDRE`, so a duty picks, raises, *and* broadcasts — see [style.md](style.md).

Inside a `do` block at a higher tier, a call at any lower tier binds with the ordinary `←`.
The lifts do the plumbing invisibly: core lifts `Set` into `NDRE`, and `Nondet.lean` adds
the one lift core does not ship, a bare `Except` value into `ExceptT` — so a raising read
spells the same in an `NDRE` routine as in a `DRE` one.

## The pick, `let x ←ᵖ s`

A nondeterministic choice wears its own arrow, so it never looks like an ordinary bind:

```lean
let W ←ᵖ top          -- best_child, line 4: any highest-scoring child
```

The right-hand side is anything `Pickable`: a `Set` or a `Finset`, so set-builders and
whole store fields pick directly. Semantics: the rest of the computation runs once per
element of `s`, and the routine's outcome set is the union over those runs.

A pick from the empty set has **no outcomes** — the branch contributes the empty set of
results. It is not a raise: an error is an outcome saying the protocol failed, while an
empty pick says this combination of choices does not occur.

## `listings`

`propose_block` must serialize a `Finset` of votes into a list. `listings s` is the set of
all duplicate-free lists whose elements are exactly `s` — written as a predicate, so no
list is ever built and none is ever preferred. The routine picks one:

```lean
let gfList ←ᵖ listings votes                       -- line 25: any order
```

## Consuming a result

There is deliberately no computable exit from `NDR`/`NDRE` — any function producing a
single answer would be exactly the arbitrary choice this vocabulary exists to avoid.
A result is consumed as a **relation**:

```lean
res ∈ (S.onTick i t p).outcomes
```

read: `res` is one possible outcome of the duty — a failure, or the store afterwards with
everything broadcast (`DutyM.outcomes`, `Duty.lean`, packaging a run started with an
empty outbox). This is the shape a state-transition-system step wants — the eventual
lean-sts wiring relates pre-state to post-state through that membership. Statements
*about all outcomes* are `Analysis/` matter, over the same set:

- "the exception never fires on a coherent store" is `.error ∉ (…).run`;
- "the walk does not depend on its picks" is `(…).run` a singleton.

## What this replaced

The architecture was adopted 2026-08-23 and dissolved four earlier constructions in one
motion (git history has each):

- the `TieBreak` class — the tie at `bestChild` is now a pick;
- `[LinearOrder (GoldfishVote Validator)]` and `toSortedList` — the carried list is now a
  picked listing;
- the `for all` macros — the two order-free loops are written as the sets they build
  (a `biUnion` for the view merge, a set-builder for `sg_support`);
- the rendering's one named deviation — `ghost`'s condition parameter is
  `Block Validator → DRE Bool`, so Figure 7's raising `goldfish_eligible`
  passes to it directly at line 29, and the pure layers offer their conditions with `pure`.

## Traps

Three measured traps, recorded in full in `Nondet.lean`'s header and at each site:

1. A `do` block's result type must **name the stack** (`NDR`/`NDRE`). Declared as bare
   `Set (DRE …)`, the elaborator picks the `Set` monad and every bind means the
   wrong thing.
2. A `filterM` inside an `NDRE` block must be ascribed to `DRE` and lifted
   whole. Elaborated at the stack itself, its fold needs a commutativity that is *false*
   there: a pick with no outcomes annihilates where an error survives. The `∈ᴹ`
   set-builder's expansion pins the monad for this reason.
3. A macro quotation's global names resolve when the macro is *declared*, not where it is
   used — `Notation.lean` imports `Raise.lean` so its expansions can name `DRE`.
