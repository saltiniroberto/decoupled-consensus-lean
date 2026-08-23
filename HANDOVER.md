# Handover — 2026-08-23, at commit `ace0320`

Written before a compaction, mid-collaboration with Roberto on `Spec/Consensus1/`. It is a
snapshot, not a record: `CONTEXT.md` is the record, and where the two disagree, `CONTEXT.md`
is right. Delete this file once it has been read.

## Read these first, in this order

1. `CLAUDE.md` and `CLAUDE.local.md` — the rules. Watch the word-choice rules in the global
   file: never "gate" for a condition (Roberto corrected this live), never "guard",
   never "load-bearing".
2. `CONTEXT.md`, two places: **"The `Consensus1` style sheet — running list"** (every
   stylistic ruling, one per bullet) and the dated 2026-08-23 entries above it, especially
   **"The walk goes nondeterministic: `NDR`/`NDRE` adopted"**.
3. `lean/Spec/Consensus1/Nondet.lean` — the nondeterminism vocabulary, its header carries
   the design and the measured traps.

## Where the work stands

`main` at `ace0320`, working tree clean, ~230 commits ahead of `origin/main`. `lake build
Spec` green (834 jobs); `make nodecide orphans sorry cites` all pass (535 citations, 0
problems). The older subtrees (`Spec/Defs/`, `Spec/Consensus/` with `Validator.lean`) are
untouched all day, per standing instruction.

## What happened on 2026-08-23, in one paragraph each

**The nondeterminism adoption.** The parked `for all` question resolved by architecture:
`NDR α := Set α` (picks) and `NDRE α := ExceptT Error Set α` (picks + raising reads) in
`Nondet.lean`; the walk and every duty carry `NDRE`; picks wear their own arrow `←ᵖ`;
`TieBreak`, the `LinearOrder` on votes, the `for all` macros, and the one named deviation
all dissolved (`bestChild` picks its tie, `proposeBlock` picks a `listings` order, `ghost`'s
condition slot is `Block → ResultOrExcept Bool` so Figure 7's raising `goldfish_eligible`
passes directly). Consumption: compose by `←` inside a stack; at the boundary a duty is a
relation `res ∈ (f …).run` — the lean-sts step shape; no computable exit, deliberately.
Probes (kept): `scratch/SetMonadProbe.lean`, `scratch/SetExceptProbe.lean`.

**The naming scheme, three passes ending flat.** Store-takers in `Store` for dot notation →
prefixes restored on moved names (`Store.sgSupport`, `Store.goldfishForkChoice`) → final
form: **no namespace blocks at all**; every definition carries its full name at its own
`def`. `Store.…` for store-takers; `Fig<n>.…` for the superseded readings of the three
incrementally-redefined routines (`Fig1.getHead`, `Fig4.getHead`, `Fig2.processBlock`,
`Fig1.goldfishEligible` — the last reading of each is the protocol's: `S.getHead`,
`S.processBlock`, `S.goldfishEligible`); bare names for the once-defined (`ghost`,
`goldfishScore`). `Goldfish`/`SG`/`FG` no longer exist. Sections minimized to one
(`Model.lean`'s `Electorate`, with its reason stated).

**Smaller rulings, all on the style sheet**: what the pdf writes inline stays inline
(`equivocators`, `voters_count` are `let`s); messages built by named `mk`; instants as
autoparams with `solve_by_elim [And.left, And.right]` (no `have`s in `onTick`); `SGSchedule`
class for `a_r` and `on_tick`'s §3.4 line; `Roots` abstract type class; `RootComputation`
from parent and slot; `DutyResult` for every duty and `on_tick` (early return per branch);
`|s|` cardinality bars; `∈ᴹ` raising set-builder (`doElem`, expansion pins `ResultOrExcept`);
`TimeMap` raising timestamp reads; `latest` as `Finset.max`; unused macros parked in
`OldDefs.lean` (nothing may import it — revive by moving out).

## Pending: Roberto wants documentation

His last words before compacting: he needs to **document the above** — the day's design
(the nondeterminism architecture and the naming scheme), presumably as prose for humans,
"perhaps after the compact". Nothing has been started. The raw material is `CONTEXT.md`'s
2026-08-23 entries, the style sheet, `Nondet.lean`'s header, and the commit messages from
`f6bd570` (machinery) through `ace0320` (figure names). Ask him what form he wants — a
`docs/` page, a README section, a paper appendix — before writing.

## Other open items

- **No `Analysis/` for `Consensus1`.** The adoption reshaped the obligations: "the exception
  never fires" is `.error ∉ (…).run` on coherent stores; "the walk does not depend on its
  picks" is `.run` a singleton. The `coherence-invariant` branch is about the *older* store
  and does not transfer.
- **The sts wiring** consumes a duty as `res ∈ (….run)`; not started.
- `Next` items 1+ in `CONTEXT.md`: the older subtree where 2026-08-22 left it, `MAPPING.md`
  refresh on instruction, `README.md` before a push (a push is overdue — ~230 commits).

## Traps that will bite a fresh session (details in CONTEXT.md and at the sites)

- A `do` block's result type must *name* the stack (`NDR`/`NDRE`) or binds elaborate in the
  `Set` monad. A `filterM` inside an `NDRE` block needs a `ResultOrExcept` ascription —
  at the stack, `unionM` commutativity is *false* (empty pick annihilates, error survives).
- Quotation globals resolve at macro declaration (`Notation.lean` imports `Raise.lean` for
  exactly this). Bash heredocs containing `/--` or `/-` sequences are denied by the hook —
  patch scripts go in `scratch/` via the Write tool, run as `python3 scratch/x.py`.
- `Committees ?m` sticks only when nothing in the expression pins `Validator`; a `let` from
  an inlined def may need the deleted def's result-type ascription back
  (`scratch/AscriptionProbe.lean`).
- The `=` elaborator inserts no coercion around a `mut` read (`B.parent = ↑H` is explicit);
  field notation never coerces a subtype (`.val` or destructure `let ⟨B, hB⟩ ←`).
