# experiments

Work that is not the specification. Each subdirectory is a copy of the spec that some
change is tried out on, so that `lean/Spec/` is never where a change is tried.

**Nothing here speaks for the protocol.** Read [`lean/Spec/`](../lean/Spec/) for what the
protocol is. A change made here reaches the spec only by being carried over deliberately.

Everything here is a `lean_lib` like any other, listed in
[`lakefile.toml`](../lakefile.toml) with `srcDir = "experiments"`, so `make dev` and
`make check` build it along with the rest and its warnings ride along with the spec's.

## `SpecM/` — the store threaded through a monad

A copy of `lean/Spec/`, taken on 2026-08-27 from the working tree at commit `c0ef96e`
together with the spec edits that were uncommitted at that moment. It differs from its
source only in the module names on its `import` lines, apart from the experiment itself;
the reader-facing pages under `lean/Spec/doc/` were not duplicated.

The question it is here to answer: what the spec reads like when a routine neither takes
the store as a parameter nor hands it back, the store threading through the monad instead.

Two monads carry it, both in [`SpecM/Defs/Store.lean`](SpecM/Defs/Store.lean):

- `DRES Validator α` — the store threaded through a routine that can also raise. Under
  the `abbrev` it is `Store → DRE (α × Store)`.
- `DRS Validator α` — the same threading for a routine that cannot fail, so a rule reading
  only store fields does not advertise a failure it cannot make. `raising` carries a `DRS`
  into a `DRES`.

The letter continues the effect inventory of `Defs/Raise.lean` and `Defs/Nondet.lean`: `S`
for the store, as `B` in `NDREB` is for the broadcasts.

### What is converted so far

[`SpecM/08_FinalityVote.lean`](SpecM/08_FinalityVote.lean), all three of its rules.
`heightVote` and `fgVote` are `DRES`, `finalityVote` is `DRS`. None names a store at its
signature, none returns one, and each returns its vote alone — so `VoteAndStore`, which
existed to name the two things a rule handed back, is gone from the file. Each rule reads
through one `let S ← get`, and the writes to the signing record are named routines
(`recordEmptyTarget`, `recordTarget`, `recordFinalityTarget`) so that no rule body says
`modify`.

A caller that holds a store runs a rule: `fgVote.run S`.

Everything else in `SpecM/` is still the copy as taken, in the store-in, store-out shape,
which is what makes the two readings comparable side by side.

`CONTEXT.md` at the repository root carries the decisions and the measurements behind
them — including what was tried and does not work.
