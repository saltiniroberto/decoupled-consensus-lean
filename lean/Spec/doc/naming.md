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

**`Fig<n>.foo`** — a superseded reading of a routine the protocol redefines incrementally
(see the table below). The prefix says which figure's reading this is, and warns that a
later figure replaces it.

**A bare name** — everything defined exactly once that takes no store:
`ghost`, `bestChild`, `goldfishScore`. Since no namespace supplies a prefix, the
routine's own prefix is spelled in the name: `goldfishScore`, not `score`.

## The incrementally-redefined routines

Four routines are defined more than once, a later figure extending or
replacing the earlier reading. The rule: **the last reading is the protocol's, and it bears
the plain `Store` name**; the superseded readings are figure-named.

| routine             | superseded readings            | the protocol's                      |
| ------------------- | ------------------------------ | ----------------------------------- |
| `get_head`          | `Fig1.getHead`, `Fig4.getHead` | `Store.getHead` (Figure 7)          |
| `process_block`     | `Fig2.processBlock`            | `Store.processBlock` (Figure 7)     |
| `goldfish_eligible` | `Fig1.goldfishEligible`        | `Store.goldfishEligible` (Figure 7) |
| `on_tick`           | `Fig2.onTick`                  | `Store.onTick` (`Fig5SGDuty.lean`)  |

`on_tick` is the one whose extension is rendered as a call rather than a rewrite: Section
3.4 says "`on_tick` gains one line", and `Store.onTick` is exactly that — it runs
`Fig2.onTick`, then the one line at `t = a_r`.

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
