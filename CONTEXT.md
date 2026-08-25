# Context

The durable, machine-independent record, kept by topic: each design decision with its
reason and the alternatives declined, the measured Lean facts, and the pointers to what
lives elsewhere. It is not a journal — `git log` holds the chronology — so an entry is
updated in place when its decision changes, and deleted when it becomes wrong. The other
half, anything needing this machine's paths, is `CONTEXT_LOCAL.md`, gitignored. Keep both
current as work happens.

## What this is

The Lean 4 specification of **Ethereum decoupled consensus**. `lean/Spec/` is the
protocol's source of truth; `extract/` renders it into a paper-shaped document
(`make extract` → `extract/out/dc.pdf`); `lean/Analysis/` states results against it. The
spec originated (2026-08-22 to 24) as a rendering of a human-controlled working draft,
`consensus-1.pdf`, not distributed with this repository; since 2026-08-24 the spec speaks
for itself (Roberto: "this is not anymore a formalization of consensus-1.pdf — it is the
formalization of Ethereum decoupled consensus").

Standing rules that fall out of that identity, all Roberto's:

- **Docstrings cite nothing and narrate no history.** No external document, no
  Definition/Section numbers, no figure-line citations, no was-X-until-Y notes,
  no attributions, no local-file names. History belongs here; local paths belong in
  `CONTEXT_LOCAL.md`. Layer language — availability, SG, finality — replaces section
  numbers. Two deliberate exceptions: "measured YYYY-MM-DD" stamps on Lean-behaviour
  facts (dated measurements, not spec history), and `Analysis/AccountableSafety.lean`'s
  pointer to the old proof ("a starting point, not a citation").
- **No PDF spec is ever committed**, and committed files name no local-only files.
  History before `4630c05` still carries the PDFs then tracked, the safety branch
  included.
- **`README.md` is a front door**: navigation only — identity, where the spec is with one
  code snippet, links to the guide / file map / design pages / `Analysis/`, the
  `extract/` and `deps/lean-sts` lines, Building. No protocol description, no history.

## What was removed, and where it lives

**The branch `pre-consensus1-purge` holds the last commit carrying everything removed on
2026-08-24** (Roberto: keep only what `Spec/` and the extractor need): two older
renderings — the `latex-specs` papers' (namespace `Decoupled`, with its `Analysis/`, the
citation checker, `MAPPING.md` and tooling) and `consensus.pdf`'s (namespace
`Consensus`) — plus this file's pre-purge decision trails. Treat everything from those
layers as **unverified** until re-checked here. The old accountable-safety proof is
there: `Analysis/Theorems.lean`, its Lemma 11 chain. `deps/lean-sts` remains the one
submodule.

Names to search history with (each renamed since; dated commits carry the old ones):
namespace `Consensus1` → `DC`; `ResultOrExcept` → `DRE`; `Fig<n><Name>.lean` files →
`XX_Name.lean`; `FinalityVote.lean` → `08_FinalityVote.lean`; `Duty.lean` → merged into
`Nondet.lean`; `DutyM` → `NDREB`; `SGSchedule` the class → `SGSchedule.a` the definition;
`firstLock`/`saveLock` → `finalityTarget`/`saveFinalityTarget`; layer namespaces
`Goldfish`/`SG`/`FG` → the full-name scheme.

Toolchain: pinned in `lean-toolchain` (Lean 4.32.2); Mathlib's rev in `lakefile.toml` and
the rev `deps/lean-sts` requires must both match it — bump all three together.

## The `DC` style sheet

Every stylistic call Roberto has made for this spec, in one place; the decision entries
below carry the reasoning, the docstrings at each point of use carry the mechanics.
Update this list when a new call lands.

- **Raise, never answer silently — and branch rather than assume.** Map reads are raising
  brackets (`Σ.σ[B]`, `Σ.timestamp[x]` via `TimeMap`), set operations that read them go
  through `filterM`/`imageM`, and the raw `Option` stays reachable by application. The
  walk and the duties carry `NDRE` (`Nondet.lean`): ties and list orders are picks
  (`←ᵖ`), every resolution among the outcomes. No deviation stands.
- **Pseudocode spelling, gaps closed in `Notation.lean` and `Nondet.lean`**: assignment
  arrows (incl. bare identifiers and the pair form), `|s|` for `Finset.card` (cost: the
  `abs` bars, shadowed in-namespace), the raising set-builder `let y ← {x ∈ᴹ s | p}` (a
  `doElem`, necessarily — the term-macro form loses the `←` to the outer `do`'s lift; its
  expansion pins `DRE` so it lifts whole inside `NDRE`), and the pick `let x ←ᵖ s`. The
  order-free loops are written as the sets they build (`biUnion`, the set-builder); a
  genuinely order-sensitive loop would use the `ForIn` parked in `OldDefs.lean`.
- **No `match` and no `|` alternatives in spec bodies** — the dependent-`if` idiom;
  recursion patterns like a `for`-range bound are the tolerated shape. **Absence is
  tested `x ≠ ⊥`, never `.isSome`**, and in a raising body extraction is the lift:
  `let y ← x` binds the value or raises (the scoped `MonadLift Option DRE`,
  `Raise.lean`; Roberto: "do that, also wherever applicable"). Behind a plain
  `if x ≠ ⊥` the raise is unreachable; the accepted cost, stated at the instance, is that
  dropping the test leaves compiling code that raises where a rule meant to fall through.
  The autoparam extraction that did check at the site, `Option.value`, is parked in
  `OldDefs.lean` (revived by a *pure* body that must extract). The store's map machinery
  keeps `.isSome` internally — the rule is about spec bodies. **No `∣` (divides)**: write
  `% … = 0`.
- **Messages are built by named `mk`** (`GoldfishVote.mk (validator := i) …`; `Block.mk`
  likewise, in `Store.proposeBlock`); `DutyResult` keeps the brace form
  `{ state := …, send := ∅ }`; `match` patterns untouched.
- **Full names at each `def`, no namespace blocks.** `Store.…` for whatever a store flows
  into, so dot notation works; `Fig<n>.…` for a superseded reading of an
  incrementally-redefined routine (`Fig1.getHead`, `Fig4.getHead`, `Fig2.processBlock`,
  `Fig1.goldfishEligible`, `Fig2.onTick` — the last reading of each is the protocol's and
  bears the plain `Store` name; `on_tick`'s is the SG layer's, rendered as a call); a
  bare name for everything defined once (`ghost`, `goldfishScore`, its prefix spelled
  since no namespace carries it). `voters_count` is a `let` at each of its three sites —
  a local, like the equivocator set, not a definition.
- **Scheduled routines carry their instant as an anonymous autoparam**
  (`… := by solve_by_elim [And.left, And.right]`); `on_tick` discharges them with
  dependent `if`s alone, no `have`s. The `if`s bind `_`, not a name — the tactic reads
  the anonymous hypothesis; a dependent `if` names its hypothesis only where the proof is
  used (`if hp :` at `07_FGStore.lean`'s `(B.parent).get hp`).
- **The ambient environment is classes**: `Electorate`, `Committees`, `Params`, `Roots`
  (abstract `Root`, its order, genesis's root), `RootComputation`, `SGSchedule`. All in
  `Model.lean`; the SG vote time is a definition in the class's namespace, not a field —
  `SGSchedule.a r = t_{rR} + 6Δ`.
- **Duties run in `NDREB`** (`Nondet.lean`): the outbox threaded over `NDRE`, `broadcast`
  the protocol's own verb, the store an explicit input and output — no caller unions
  sends. `DutyResult` survives at the boundary only, `NDREB.outcomes` being what the sts
  wiring and `Analysis/` consume; `on_tick` returns from each action branch directly.
- **Explicit coercion where a `mut` read blocks insertion**: `B.parent = ↑H`.
- **Function-typed fields and parameters name their binders** (Roberto, 2026-08-25:
  "always name the parameters so that it is easier to refer to them in the docstring") —
  `gfVotes : (k : Nat) → (i : Validator) → Option …`,
  `score : (B : Block Validator) → Nat`. The pattern-matching accessors (`Block.parent`
  and kin) have no binder position and stay as they are.
- **Line comments describe; nothing numbers lines.** A `--` comment says what a statement
  does and becomes the rendered figure's margin note (the `-- line n` coordinates are
  retired and deleted from the spec). Docstrings are self-contained and cite nothing.

## Decisions

Each entry: what stands, why, and what was declined. Dates are when the call was made.

### The model

- **`Root` is an abstract type carried by `class Roots`** (2026-08-23; it began as a
  `Nat`). `Root : Type`, `genesisRoot : Root` (every block has a root, and genesis is a
  block), `ord : LinearOrder Root` — the one thing read off a root, `update_finality`'s
  lex comparison `(h_j, J.root)`. `export Roots (Root)` gives the bare spelling. A class
  rather than a type parameter, confirmed after questioning: the two are logically
  interconvertible, so the choice is ergonomic — the class fixes type, order and genesis
  root together, and instance search makes one vocabulary per context silent; the
  parameter form wins only for statements mixing two root vocabularies, which nothing
  foresees, and explicit `@`-instances would still express one. Every inductive of the
  mutual family takes `[Roots]` — one parameter list per `mutual` block, so the two that
  never mention a root carry it anyway.
- **The proposer's root is assumed**: `class RootComputation`,
  `compute : Block Validator → Nat → Root`, from the block's parent and its slot
  (corrected from a first cut that read it from the proposer and the store). Nothing
  constrains a block's root to match the post-state it would compute — the block *claims*
  one, and validity is not this spec's question.
- **`a_r = t_{rR} + 6Δ`** (2026-08-24): each round's SG vote time is `6Δ` after the
  round's opening slot — `SGSchedule.a`, a definition in `Model.lean`. It was an assumed
  class ("a public parameter, no formula fixed") until Roberto fixed the formula; the
  `SGSchedule.a` spelling survived the change, so call sites stood. The instant coincides
  with `t_{rR+1} + 2Δ`, the tick at which the opening slot's confirmation is evaluated —
  the two actions compose, `sg_vote` voting the fresh `live_confirmed`. Open: with
  `R = 1` the instant lies outside round `r` and `on_tick`, dispatching on the current
  round, never fires `sg_vote`; `Params` requires only `R ≥ 1` (flagged, not ruled on).
- **The attestation times are assumed: `class SGSchedule`** (2026-08-25).
  `sgfgVoting : (i : Validator) → (r : Nat) → Int` is when validator `i` sends its
  attestation for round `r` — a public parameter with no formula fixed. Total on the
  validator set by being a function; the binders are named for documentation only. Two
  proof fields, both Roberto's, bound each time within its round:
  `sgfgVoting_ge : ∀ i r, SGSchedule.a r ≤ sgfgVoting i r` and
  `sgfgVoting_lt : ∀ i r, sgfgVoting i r < roundStart (r + 1)`. The window is
  `[roundStart r + 6Δ, roundStart r + 4ΔR)`, nonempty exactly when `R ≥ 2` — with
  `R = 1` the two fields contradict and the class has no instance; `Params` requires
  only `R ≥ 1` (flagged, not ruled on — it sharpens the `a_r` vs `R = 1` question
  under Next). `roundStart r = t_{rR}` is a definition next to `round`, and
  `SGSchedule.a` reads `roundStart r + 6Δ`. The class shares the namespace of the
  definition `SGSchedule.a` (Roberto: "combine it all under SGSchedule"), so the whole
  round schedule reads `SGSchedule.…`; a declaration and its namespace may share a name,
  and the build confirms no clash. Names are Roberto's after two same-day renames (it
  landed as `FGSchedule` with field `b`, then `SGFGVotingSchedule`); the constraint
  fields' `_ge`/`_lt` suffixes follow `Params`. Nothing consumes the class yet.
- **Block equality is decided by hand**: `deriving DecidableEq` does not reach a mutual
  family nested through `List` and `Option` (measured), so the `…Beq` functions and their
  `…Beq_iff` soundness theorems are written out — the one kind of proof a `Spec/` file
  may hold, with `Raise.lean`'s `Subsingleton Error`.
- **Timestamps are three maps**, one per object kind — Lean has no sum over them here.
  Each is `Option Int`, `none` standing for both "not processed" and genesis's `−∞`,
  which costs nothing: no rule reads a block's timestamp.
- **The wire objects are one `Message` sum** — one message type per protocol, the
  lean-sts convention — and **attestations travel on the wire**: `Message.attestation`
  exists so `Store.fgVote` can be a duty that broadcasts what it signs, and a block
  carries the attestations its proposer includes.

### The store

- **`gf_votes` stores one vote per slot and validator** (2026-08-25; Roberto:
  "implement the same logic used in `on_attestation` [the healing source's handler] to
  the gfVotes to reduce the size of the votes stored"). `Σ.gf_votes[k][i]` is the first
  slot-`k` vote processed from `i`; a later differing vote is never stored — it writes
  the equivocator record. Same day, all on Roberto's word: the entry is a `VoteTime` —
  vote and processing time together, `gfVoteTime` deleted — and the record is
  `gfEquiv : (k : Nat) → Finset Validator`, the per-slot set of caught equivocators
  (first a timed map, then a `Bool` map, then the set — each his revision).
  Consequences, checked read by read:
  - the stored entry carries its time, so an unstamped stored vote is unrepresentable:
    the freeze and both confirmation cutoffs are pure entry filters, no `∈ᴹ` and no
    raise (the `let mut … ←ᴹ` form of the raising builder lost its only use — kept);
  - `goldfish_score` gains a `marked` input — the record read as of the caller's run:
    the voter, the proposer, and confirmation (which cleans its votes and passes `∅`)
    all read `Σ.gf_equiv[k]` directly. The two-distinct-votes test stays beside it, for
    the block-carried votes in the voter's merged view, which the store never
    deduplicates. With the record untimed, the voter's equivocator set is no longer
    freeze-bounded — marks landed after `t_{s−1} + 3Δ` now count (Roberto's call,
    implicit in dropping the time); `update_confirmation`'s read is equivalent to the
    old late-cutoff one, an object processed exactly at a scheduled instant being
    processed after that instant's tick;
  - the vote-set rules consume `gf_votes_at(Σ, k)`, the stored entries of `K_k`
    collected as a `Finset`, and take the votes by `.image (·.vote)`. A stored vote from
    outside the committee is not collected, which no rule can observe — every score and
    count already filters by `K_k`. The one visible change is the intended one: a
    proposal now carries at most one vote per validator, and no out-of-committee votes.
  Declined: keeping the two-vote sets (the size was the point). `timeBefore`, briefly
  added for the timed record, went with the `Bool`.
- **A raising read wears brackets; a total map is a plain function.** `Σ.σ[B]` and
  `Σ.timestamp[x]` return `DRE` and raise on an unrecorded key — their map types
  (`StateMap`, `TimeMap`) are named because instances resolve on a type's head constant
  and a bare function type has none; the raw `Option` stays reachable by application, and
  `B ∈ σ` is the membership, `.isSome` internally. The total maps (`sg_votes`,
  `gf_equiv`, and the two-level `gf_votes`) are bare function types read by application —
  `VoteTable` and its bracket read existed until Roberto dropped them (2026-08-25: "not
  sure what it gives us"); the assignment macros still write with brackets, consulting no
  instance.
- **`E_F(Σ)` is not rendered** — no figure reads it, and a definition lands with its
  first consumer.
- **`Σ.H` and `Σ.i` are this spec's own store fields.** `Σ.H` is the durable signing
  record behind the finality-vote rules; `Σ.i` is the node's validator (2026-08-24:
  `fgVote` takes no identity parameter), fixed at `Store.gen`, written by nothing. Open:
  the other duties still take `i` as a parameter; whether they switch to `Σ.i` is
  undecided.
- **`DutyResult` is the boundary object**: `state` and `send`, the field names of
  lean-sts's `NodeStepResult` (whose `send` is a `Multiset` for framework-internal
  reasons this layer does not have). Built only by `NDREB.outcomes`; no duty returns one.

### Failure

- **One payload-free `Error`.** The error is a spec artifact — the protocol never fails —
  so detail in it helps nobody (the fact worth proving is that it never fires); one fixed
  error type keeps every `do` block in a single `ε`; and, decisive for the machinery,
  `Finset.filterM`/`imageM` need their fold commutative, whose failure-failure case needs
  the two failures *equal* — `Subsingleton Error`. A payload would make
  `Std.Commutative` false, not merely unproved.
- **`DRE α = Except Error α`, an `abbrev`** — it must be reducible (measured: instance
  synthesis does not unfold a `def`, so `Monad`/`MonadExcept` are not found and even
  `throw .error` fails). Named as the deterministic partner of `NDRE` — the effect
  inventory `DRE`/`NDR`/`NDRE`/`NDREB` — and an acronym because a bare `Result` would
  silently shadow core's `EStateM.Result`.
- **Extraction from `Option` is the lift**: the scoped `MonadLift Option DRE`, `let y ← x`
  binding the value or raising, behind a plain `if x ≠ ⊥`. Accepted cost at the instance:
  the safety is not checked at the site. The site-checked alternative, the `Option.value`
  autoparam, lost its consumers to the lift and is parked in `OldDefs.lean` for a pure
  body that must extract.

### Nondeterminism

- **`NDR α = Set α`, `NDRE α = ExceptT Error Set α`** (`Nondet.lean`; Mathlib's opt-in
  `Set.monad`, activated scoped). A pick wears its own arrow, `let x ←ᵖ s`, over
  `Pickable` (`Set` or `Finset`); a pick from the empty set has **no outcomes** — not a
  raise: an error says the protocol failed, an empty pick says this combination of
  choices does not occur. `listings s` is the set of duplicate-free orderings, a
  predicate — no list is built, none preferred.
- **There is deliberately no computable exit.** A result is consumed as a relation,
  `res ∈ (…).run` / `res ∈ (…).outcomes` — the sts step shape — and `Analysis/`
  statements quantify over the same sets: "the failure never fires on a coherent store"
  is `.error ∉ (…).run`, "the walk does not depend on its picks" is a singleton set.
- **What genuine nondeterminism replaced, and why the replaced forms existed** (all
  dissolved 2026-08-23):
  - *The tie-break.* Roberto did not want nonemptiness proofs inside `bestChild`; the
    routes weighed and declined: a total chooser with a junk value on `∅` (the Mathlib
    `n / 0 = 0` standard — the silent-answer pattern this spec rejects), a named lemma
    above the definition (relocates the proof, keeps it), a linear order on blocks
    assumed as a class (order-lifting plumbing). The interim answer was a raising
    `TieBreak` class; the pick dissolved it — every resolution among the outcomes, a
    root order being one.
  - *The carried list's order.* `propose_block` must serialize a `Finset` into the
    block's `List`; an assumed `[LinearOrder (GoldfishVote _)]` with a computable
    `Finset.sort` did it (inert protocol-wise); the picked `listings` dissolved it.
    Declined throughout: list-valued vote tables, which would make "at most two per
    validator" a property of a list and put `.toFinset` at every counting site.
  - *The `for all` macros.* The two order-free loops are the sets they build — the view
    merge one `biUnion`, `sg_support` its set-builder — and a `ForIn` over `Finset`
    (pick a listing, loop the list) is parked in `OldDefs.lean` for the first loop whose
    body is not order-free.
  - *The one deviation.* The walk's condition slot is `Block → DRE Bool`, so the finality
    layer's raising `goldfish_eligible` passes to `ghost` directly; the pure layers offer
    theirs with `pure`.

### Duties

- **`NDREB Validator α = StateT (Finset (Message Validator)) NDRE α`** — the outbox
  threaded over the nondeterministic-raising base; `broadcast` writes into it. Probed
  both ways before adoption (2026-08-24): store and outbox both ambient was **declined**
  (Roberto: the functions must keep their input `Store`; and, measured, an ambient store
  costs the instant autoparams — a precondition needs the store as a *term*); outbox-only
  was adopted. The name `DutyM` lasted an hour — the `-M` suffix here marks monadic
  variants of named pure operations, which a duty monad is not.
- **No `run` appears in `Spec/`.** A named `runDuty` was declined ("reads off compared to
  the paper"); `NDREB.outcomes` — the outcome set of a run started with an empty outbox —
  is the one boundary. The outbox sits *inside* the nondeterminism
  (`outbox → NDRE (α × outbox)`), so each outcome carries its own sends — necessary,
  a picking duty broadcasting differently per pick.
- **The handlers stay `Store → Store`**: the algorithms give them no broadcast line, and
  "an honest node relays every object it processes" is network behaviour, the wiring
  layer's to render.
- **Scheduled duties carry their instants as anonymous autoparams**, tactic
  `solve_by_elim [And.left, And.right]` (plain `assumption` first — the upgrade lets a
  caller's dependent `if` on a several-part condition discharge the instant with no
  `have`). A caller must still hold the fact as a hypothesis. `on_tick` discharges all of
  them from its own dependent `if`s: the clock is written just above the tests, so `S.t`
  reduces to `t` (the join-point fact below), and the confirmation branch tests the
  instant in the form `t_{s−1} + 6Δ` — equal to slot `s−1`'s `t + 6Δ` whenever `s > 0` —
  so no arithmetic is proved anywhere in `Spec/`.
- **`on_tick` is two readings**: `Fig2.onTick`, exactly the availability layer's lines,
  and `Store.onTick`, the protocol's — run `Fig2.onTick`, then at `t = a_r` run `sg_vote`
  on the result. The one incrementally-redefined routine whose extension is a call rather
  than a rewrite; `05_SGDuty.lean` imports `02_GoldfishDuties.lean` for it.

### The algorithms

- **`ghost` is the figure's own loop, bounded**: `for _ in [:|tree|]` — a descent through
  distinct blocks visits at most `|tree|` of them. The loop's real termination argument
  (the tree is a tree) is an invariant of `Σ.T`, not a fact about the `Finset` the
  routine takes, so the bound is visible instead. Cost: one reachable case the protocol
  does not have — the bound reached with an eligible child still available, answering the
  block it stands on; "never reached on a real tree" is `Analysis/` matter. Declined: a
  fuel recursion (looked nothing like a paper's loop) and a well-founded recursion (needs
  the tree invariant in the definition).
- **`nj` is a stored field of the chain state**, written on entry into a height and read
  by the justify event. Recomputing the test at the event would be a *different rule* —
  it would read the `h_F` of the justification's moment, not of the height's entry.
- **The view merge is the figure's `for` loop again** (2026-08-25, Roberto: "can we
  please have a for loop here as in consensus-1.pdf"). The nondeterministic `ForIn` over
  `Finset` moved out of `OldDefs.lean` into `Nondet.lean`: pick a listing, loop the
  list — every visitation order among the outcomes. The merge's body is an order-free
  union, so every listing converges to one store and the outcome set equals the old
  fold's. (The fold reading it replaced: `biUnion`, adopted when no `ForIn` existed —
  needed `Mathlib.Data.Finset.Lattice.Basic` and a result-type annotation. `OldDefs` also
  lost its parked `idx2Assign`, superseded by `Notation.lean`'s live `idxAssign2`.)
- **The finality-vote strategy** (`08_FinalityVote.lean`, imported 2026-08-23 from the
  first rendering's `Voting.lean`, on the branch): `SigningHistory` — the once-only
  per-height record, fields `signedEmptyTarget`/`firstTarget`/`finalityTarget` (Roberto
  asked for speaking names over the source's `τ`/`T`/`lock`) — with the five-case
  `heightVote` under the confirmed ceiling, `finalityVote` signing `(h_j, J)`, and
  `Store.fgVote` composing them finality-first, so the finality write is visible to the
  height rule's read. The rules are store rules returning `SigningResult` (`pair`,
  `state` — a named structure, not a product), the record write riding the returned
  store. **The crossing decisions, each one to revisit**: the pair encodings
  (`.timeout` → `emptyTarget`, `.commit` → `pair`); the four fork-choice inputs read from
  the store; the ceiling is `Σ.live_confirmed` and always exists (a block from genesis
  on — the source's nothing-confirmed case is unrepresentable); the context read raises
  off `Σ.σ[live_confirmed]` (the source degraded to an empty pair; no `process_slots`
  exists here, the stored state is read as it is); the context target is always a block;
  the two heights coincide, so the source's `hC ≥ k` conditions hold outright and are
  unwritten; `r = round Σ.s`; `head` stays explicit (producing it is the confirmation
  rule's concern); the source's `hasJC` input is dropped — justification is an on-chain
  fact here, the store's replayed chain its own evidence, no separate
  certificate-knowledge to model. A store-free `fgVote` layer between the rules and the
  wiring was folded away — it added only a name, and the name collided (the bare-name
  trap below).
- **The healing layer** (`09_Healing.lean`, imported 2026-08-25 from the earlier draft's
  Figures 4 and 5, on Roberto's word — the draft `consensus.pdf`, local; not
  `consensus-1.pdf`, whose Figures 4–5 are the SG files). The support scores and grades
  over the store's new per-round bookkeeping (`head`/`equiv`/`root_proposal`/`sg_root`,
  `Store.lean`), and the five round-root functions. The vocabulary landed with it:
  `m = ⌊W/2⌋ + 1` beside `q`, and the grade instants `Γ j r = roundStart r + jΔ` beside
  `roundStart` (both `Model.lean`, where the source's own model and schedule sections put
  them). The crossing decisions, each ruled on by Roberto 2026-08-25 (confirmed unless
  marked *to change*):
  - the per-round maps are `Int`-indexed: round `r` reads its round-`(r − 1)` entries and
    round `0` must find round `−1` empty, where a `Nat` index would truncate `0 − 1` to
    `0` — confirmed;
  - the head entry is a named structure, `deriving DecidableEq` — a plain structure, so
    the mutual-family deriving limit does not apply. It landed as `HeadEntry` (`H`, `t`)
    and became `VoteTime (α : Type)` (`vote`, `t`) on Roberto's word (2026-08-25), one
    entry type for the healing heads and the stored Goldfish votes;
  - "the deepest block in `G`" is a pick from `deepest G`, the `⪯`-maximal blocks; the
    one-chain claim that makes the pick a singleton is `Analysis/` matter, not assumed —
    confirmed;
  - the source's `C(Σ)` and `fork choice root(Σ)` are the existing
    `get_filtered_block_tree` and `fork_choice_root` (`07_FGStore.lean`) — the two
    documents define them the same way, so no new view was added — confirmed;
  - *to change*: `E_j` filters over `V` where the source ranges over the `equiv` map's
    domain (`E_j = {i ∈ Σ.equiv[r−1] : Σ.equiv[r−1][i] < Γ_j}`) — Roberto: render it as
    the source writes it. Open rendering question when executing: the map is a function,
    so its domain is not a `Finset` of the type; either the field becomes a finite map,
    or the domain set needs another spelling (`w(·)` takes a `Finset`);
  - `get_walk_root` reads the stored SG root as set (raising on absence) — semantics
    confirmed, but *to change* the spelling: Roberto wants the bracket read
    `S.sgRoot[r]`, which needs a named map type (or `GetElem` instance) the way
    `TimeMap`'s raising bracket is done;
  - `G0` is imported with the other grades though nothing reads it yet — confirmed, keep.
  Skipped, deliberately, each to land with its own figure: the writers (the source's
  `on_tick`/`on_attestation` lines and the `on_block` proposal-root registration), the
  block's proposal-root field, and the `action_root[·]` store field. The source's
  schedule requires `R ≥ 2` (`a_r + Δ ≤ t_{r+1} − Δ`); Roberto ruled 2026-08-25 that
  `Params` adopts it (pending, Next).

### Naming and layout

- **Full names at each `def`, no namespace blocks** (the scheme in the style sheet;
  layer namespaces `Goldfish`/`SG`/`FG` and a `namespace Store` pass preceded it, in git
  history). Open: the `Fig<n>.…` declaration prefixes survive the file renames, re-read
  as "the number of the file that defined the superseded reading"; renaming them is
  Roberto's call, not made.
- **The spec files are `XX_Name.lean`** (2026-08-24), `XX` the double-digit figure
  number, `08_FinalityVote.lean` closing the list — asked and picked over dependency
  order; `Defs/` stays unnumbered. Digit-leading module names need guillemets:
  `import Spec.«01_GoldfishWalk»`. The extractor derives `\label{fig:<stem>}`, so
  `[fig:…]` labels in `## Extract` prose follow the stems.
- **The namespace is `DC`** (2026-08-24), the layout `lean/Spec/` + `lean/Spec/Defs/`,
  the finality-vote file at the root (all Roberto's words). `DutyResult` sits in
  `Store.lean`; the duty monad sits in `Nondet.lean` (its own `Duty.lean` said nothing —
  merged; `Nondet` imports `Store`, acyclic).

### Accountable safety

Statements only (2026-08-24): `lean/Analysis/AccountableSafety.lean` holds `E1`, `E2`,
`IncludedOn`, `replay` (`state_transition` folded along the parent link — store-free,
what every coherent store's `Σ.σ[B]` equals), and `AccountableSafety` as a named `Prop`,
so nothing claims a proof and `make check` stays green; proving one later adds a
`theorem` beside it. **The adaptation decisions, each one to revisit**: totality deletes
the source's two `≠ invalid` hypotheses (every block replays, there is no invalid);
`replay` is defined here because the statement must be store-free; "conflicting" is
`¬ Compatible` (the source names no relation for it); the pair encodings are this spec's
(`.commit` → `FinalityPair.pair`, `.timeout` → `HeightPair.emptyTarget`); the height
binders the source itself called redundant are dropped — "for some height `h`" lives
inside E1 and E2's own pairs. The source statement and its proof: the branch,
`Analysis/Theorems.lean`, Lemma 11.

### The extractor

`extract/extract.py` renders the live `lean/Spec/` into `extract/out/dc.pdf`
(LuaLaTeX; `make extract`); its conventions live in `extract/README.md` and its module
docstring — this file records only the decisions:

- **Prose is opt-in, under the `## Extract` marker** (the keyword chosen over
  Draft/Document/PDF for naming the destination): a module header's marked section is
  the file's section prose, a figured `def`'s marked docstring section leads its figure.
- **A `def` is figured exactly when its docstring carries an `## Extract` section** (a
  bare heading counts). Declined: deriving figuredness from body shape (misclassifies
  symbol defs and the `Beq` helpers) and a root-module import list (authors order, not
  figuredness).
- **The spec drives the structure; nothing is hardcoded.** Files render in alphabetical
  path order, subdirectories first (so `Defs/Model` and `Defs/Store` open the document);
  routines in declaration order. The paper form of a routine derives from the Lean `def`
  (snake-cased name, explicit params, store as `Σ`); a docstring opening with a pure call
  span `` `name(args)` `` overrides — the way to hide params the paper's calls hide. Any
  `--` comment is its statement's margin note. `[eq:name]` in marked prose expands to the
  named declaration's docstring opening span, so a formula lives once, at its definition.
- **Not carried over from the source document**: its `E_F(Σ)` evidence-set display
  (nothing consumes it) and `Σ.timestamp(B_gen) = −∞` (not checked against the Lean).
- The frozen copies the extractor was developed against are records in `archive/`;
  nothing reads them.

### The doc pages

`lean/Spec/doc/`: `README.md` (the file map), `guide.md` (reading the spec without Lean —
first link on the front door), `nondeterminism.md`, `naming.md`, `style.md`, `sts.md`
(the duty boundary and `deps/lean-sts`; how the wiring will be written is deliberately
absent, per the one-step rule). They state the decisions for a reader; the reasoning
stays here. **This file is the record**: when a ruling changes, update the entry here and
then the page.

## Measured Lean facts

General Lean behaviour, each paid for once. The toolchain is 4.32.2; re-verify on bumps.

### What a hypothesis can reach past in a `do` block (2026-08-21)

A plain assignment leaves the mutated variable a `let` **with a value**, so `isDefEq`
walks back through the whole chain — a signature hypothesis about the resulting store
matches definitionally, and `assumption` finds it. Control flow that mutates and has a
**shared continuation** does not: the do-elaborator binds its result to a fresh opaque
binder, with no value.

| shape | store after it |
| --- | --- |
| `if c then (assign)` with a tail below | opaque — `__r✝ : Unit`, then a valueless store |
| `if c then (assign; return …)` with a fallthrough | then-branch concrete, fallthrough opaque |
| `if c then (assign; return …) else (return …)`, nothing after | both branches concrete |
| `for C in xs do (assign)` | opaque, always |

The rule is about the shared continuation, not about `if` or `for`. Consequences: a
mutating branch inline with a proof-carrying call after it is impossible, not awkward —
only *values* cross a join point, which is why an `Except` result works where a
hypothesis cannot; the diagnosis is not in the error (an unremarkable goal — the opacity
shows only as a context entry with no `:=`); and hoisting branches into named routines
works but duplicates the sequence in a `def`.

### Elaboration and instances

- `Subtype.val` coerces at expected-type positions (`return b`, `:=` onto a typed `mut`
  variable) but never at field access or into an application with an open implicit;
  `let ⟨B, hB⟩ ← e` destructures past the question. The `=` elaborator inserts no
  coercion around a `mut`-variable read — hence the explicit `B.parent = ↑H`.
- A reducibility-dependent abbreviation must be an `abbrev`: instance synthesis does not
  unfold a `def` (the `DRE` case).
- `deriving DecidableEq` does not reach a mutual family nested through `List`/`Option`.
- There is no computable loop over a `Finset` (no `ForIn`; `Finset.toList` needs
  `Classical.choice`); `Finset.fold` demands a commutative-associative operation, and
  supplying those instances is what it means for a monad to be usable over a set —
  `StateM` rightly cannot.
- Dot notation resolves fields in the type's *root* namespace only — a `DC.Option.value`
  is invisible to `x.value`, hence `_root_.` on such defs. Inside `def Store.fgVote`, the
  bare name `fgVote` resolves to the def itself.
- Digit-leading module names take guillemets: `import Spec.«01_GoldfishWalk»`.

### Set-builders over `Option` entries (2026-08-25)

- **An inline `∃ e ∈ (o : Option α), …` condition fails in a `def`-level set-builder**:
  the sep notation's `DecidablePred` synthesis dies on it inside a `def`, even though the
  identical goal synthesizes as an `example`'s stated type or through a `haveI` in the
  same body (measured, `scratch/HealingFilterProbe.lean`). Fix: name the condition as a
  `Prop` with a keyed `Decidable` instance — `Store.headSupports`, `Store.equivBefore`.
  Over a `Finset`, the inline `∃` works (`sgSupport`).
- **A `let`-bound set-builder over `Electorate.V` needs the instance pinned**:
  `{i ∈ Electorate.V (Validator := Validator) | …}`; unpinned, elaboration sticks on
  `Electorate ?m` (`W`'s definition set the spelling). `Committees.K` in the same
  position needs the same pin (the `marked` builders, `02_GoldfishDuties.lean`).
- **A `doElem` `macro_rules` whose pattern quotation is ambiguous never fires**
  (2026-08-25): the two-level write `σ.arr[i][j] ← e` declared as `scoped syntax` plus a
  separate `macro_rules` silently lost its expansion — the pattern also parses as core's
  pattern-bind, and every use site then errors "Invalid pattern". Declared as one
  `scoped macro` command (no pattern quotation) it works: `idxAssign2`,
  `Notation.lean`; measured on `scratch/IdxAssign2Probe.lean`.

### `do` blocks over `Set`

- A `do` block's result type must *name* the stack (`NDR`/`NDRE`): declared as bare
  `Set (DRE …)`, the elaborator picks the `Set` monad and every bind means the wrong
  thing.
- A `filterM` inside an `NDRE` block must be ascribed to `DRE` and lifted whole — at the
  stack itself its fold would need a `unionM` commutativity that is *false* there (a pick
  with no outcomes annihilates where an error survives). The `∈ᴹ` builder's expansion
  pins the monad for this reason.
- A macro quotation's global names resolve at *declaration* — `Notation.lean` imports
  `Raise.lean` so its expansions can name `DRE`. And a set-builder macro must be a
  `doElem`, not a term macro: the enclosing `do` lifts a user's `(← …)` out of a term
  before the macro expands, and the bound variable escapes its binder.

## Next

0. **The spec is the source of truth, complete over its seven figures plus the
   finality-vote rules and the healing functions, and everything builds** (`make check`
   green). Open, in order of readiness:
   - **Instructed by Roberto 2026-08-25, not yet executed** (his rulings on the healing
     import's crossing decisions — see the healing entry under Decisions):
     1. raise `Params.R_ge` to `2 ≤ R` (the healing source's schedule requires it; it
        also settles the `a_r`-outside-round-`r` pathology and `SGSchedule`'s
        inhabitation);
     2. respell `get_walk_root`'s read as the bracket `S.sgRoot[r]` (raising semantics
        confirmed; needs a named map type or `GetElem` instance);
     3. re-render `E_j` as the source writes it — over the `equiv` map's domain, not a
        filter of `V` (rendering question noted in the Decisions entry);
     4. rename the raising set-builder's `∈ᴹ` to `∈ᵉ` — `e` for exception (`Notation.lean`;
        the typing table in `doc/guide.md`, `doc/style.md`, `doc/nondeterminism.md` and
        the style sheet here mention the old spelling).
   - **the healing writers** (2026-08-25): `09_Healing.lean` holds the scores, grades and
     round-root functions, but the four store fields they read are written by no routine —
     the `on_tick`/`on_attestation` handler lines, the `on_block` proposal-root
     registration, the block's proposal-root field, and the `action_root[·]` field all
     await their figures (see the healing entry under Decisions).
   - **the sts wiring**: a step consumes a duty as `res ∈ (….outcomes)`; `deps/lean-sts`'s
     `StsMultisetLog` is the target, and the framework-layer audit (its `Execution.lean`
     and `Schedule.lean`) is owed before trusting it.
   - **`Analysis/` beyond the accountable-safety statement**: "the exception never fires"
     as `.error ∉ …` on coherent stores, "the walk does not depend on its picks" as a
     singleton outcome set. The old `coherence-invariant` branch predates this store and
     does not transfer.
   - **Open questions awaiting Roberto's call**: renaming the `Fig<n>.…` declaration
     prefixes; the duties taking `Σ.i` instead of an `i` parameter. (The `a_r` vs `R = 1`
     question is ruled: `R ≥ 2`, pending above.)
   - **The attestation schedule is stated but unconsumed** (2026-08-25): the class
     `SGSchedule` exists (see Decisions); no duty dispatches on `sgfgVoting i r` yet,
     and the formula is deferred on Roberto's word.
   - **`sg_votes` await the same storage treatment as `gf_votes`** (Roberto, 2026-08-25:
     "the head votes in the healing spec are the sgVotes", and the gf change came
     "first") — the healing `head[·]`/`equiv[·]` bookkeeping and the SG vote sets are to
     meet; how is not yet ruled.
1. **The extractor workstream** (`extract/`): conventions in `extract/README.md`; the
   spec drives the structure, all eight figure blocks render.
2. `README.md` is refreshed before a push, not per commit; a push is long overdue.
