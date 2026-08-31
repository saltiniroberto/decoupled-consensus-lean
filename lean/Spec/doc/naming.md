# Naming: full names at each `def`, no namespace blocks

Every definition in `Spec/` carries its full name at its own `def`; the files
contain no `namespace` blocks. (The one `section` left is `Model.lean`'s `Electorate`,
which scopes section variables and says so where it opens.) The point: a definition read
mid-file tells the reader everything from its own first line, with no scrolling up to find
which block it sits in.

## The three name shapes

**`Store.foo`** — the routine takes a store. Putting it in the `Store` namespace is what
makes dot notation work at call sites: `S.getHead`, `S.processBlock`, `S.viable`. A name
moved under `Store` keeps the protocol's own prefix: `goldfish_fork_choice` is
`Store.goldfishForkChoice`, `sg_support` is `Store.sgSupport` — never a bare
`forkChoice` or `support`.

**`Fig<n>.foo`** — a superseded reading of a routine the protocol redefines incrementally.
The prefix says which figure's reading it is, and warns that a later figure replaces it.
**Currently the shape has no instances**: every routine is defined exactly once, the
assembled protocol's reading, because the spec renders the newer draft's one complete
figure set rather than a layer-by-layer build-up. The shape stands for any future
superseded reading; git history holds the last uses (`Fig1.goldfishEligible`,
`Fig2.processBlock`).

**A bare name** — everything defined exactly once that takes no store:
`ghost`'s tie-break `bestChild`, and `Λ`'s rules under `SigningHistory.…`, which is the
same dot-notation move as `Store.…` for the record's own takers. Since no namespace
supplies a prefix, a bare routine's own prefix is spelled in the name.

## What this replaced

The scheme is the third pass (Roberto, 2026-08-23); git history has the first two:

1. store-takers inside `namespace Store` blocks, everything else at top level;
2. layer namespaces `Goldfish`/`SG`/`FG` holding the superseded readings.

Both were dropped for the same reason: a namespace block makes a definition's full name
invisible at the definition, and the layer names (`Goldfish`, `SG`, `FG`) are coarser than
what a reader actually needs, which is *which figure* a superseded reading comes from.
