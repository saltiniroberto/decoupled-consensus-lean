# Naming: full names at each `def`, no namespace blocks

Every definition in `Spec/Consensus1/` carries its full name at its own `def`; the files
contain no `namespace` blocks. (The one `section` left is `Model.lean`'s `Electorate`,
which scopes section variables and says so where it opens.) The point: a definition read
mid-file tells the reader everything from its own first line, with no scrolling up to find
which block it sits in.

## The three name shapes

**`Store.foo`** — the routine takes a store. Putting it in the `Store` namespace is what
makes dot notation work at call sites: `S.getHead`, `S.processBlock`, `S.viable`. A name
moved under `Store` keeps the prefix the pdf gives it: the pdf's `goldfish_fork_choice` is
`Store.goldfishForkChoice`, its `sg_support` is `Store.sgSupport` — never a bare
`forkChoice` or `support`.

**`Fig<n>.foo`** — a superseded reading of a routine the draft redefines incrementally
(see the table below). The prefix says which figure's reading this is, and warns that a
later figure replaces it.

**A bare name** — everything the draft defines exactly once and that takes no store:
`ghost`, `bestChild`, `goldfishScore`. Since no namespace supplies a prefix, the pdf's own
prefix is spelled in the name: `goldfishScore`, not `score`.

## The incrementally-redefined routines

The draft defines three routines more than once, each later figure extending or replacing
the earlier reading. The rule: **the last reading is the protocol's, and it bears the plain
`Store` name**; the superseded readings are figure-named.

| pdf routine         | superseded readings          | the protocol's (Figure 7) |
| ------------------- | ---------------------------- | ------------------------- |
| `get_head`          | `Fig1.getHead`, `Fig4.getHead` | `Store.getHead`         |
| `process_block`     | `Fig2.processBlock`          | `Store.processBlock`      |
| `goldfish_eligible` | `Fig1.goldfishEligible`      | `Store.goldfishEligible`  |

So a caller who writes `S.getHead` gets the protocol's fork choice without thinking about
layers, and a reader who sees `Fig2.processBlock` inside `Store.proposeBlock` knows that
duty predates Figure 7's extension.

## What this replaced

The scheme is the third pass (Roberto, 2026-08-23); git history has the first two:

1. store-takers inside `namespace Store` blocks, everything else at top level;
2. layer namespaces `Goldfish`/`SG`/`FG` holding the superseded readings.

Both were dropped for the same reason: a namespace block makes a definition's full name
invisible at the definition, and the layer names (`Goldfish`, `SG`, `FG`) are coarser than
what a reader actually needs, which is *which figure* a superseded reading comes from.
