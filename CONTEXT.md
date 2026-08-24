# Context

The durable, machine-independent record: decisions, revisions, what is proved, what
failed. The other half — anything needing this machine's paths — is `CONTEXT_LOCAL.md`,
gitignored. Keep both current as work happens; delete what becomes wrong.

## What this is

The Lean 4 specification of Ethereum decoupled consensus, as `lean/Spec/` — rendered
from the protocol's working draft, `consensus-1.pdf`, human-controlled and not
distributed with this repository — plus `extract/`, a script that renders the Lean back
into a paper-shaped document. No PDF spec is committed, and committed files do not name
local-only files (Roberto, 2026-08-24, all three: the identity is the protocol's
formalization; nothing in the tracked tree is a PDF — history before `4630c05` still
carries the ones then tracked, the safety branch included; and where local material
lives is `CONTEXT_LOCAL.md`'s to say).

**Two older renderings and their apparatus preceded this scope and were removed on
2026-08-24** (Roberto: keep only what `Spec/` and the extractor need): the
`latex-specs` papers' rendering (`Spec/Defs/` and the root figure files, namespace
`Decoupled`, with `Analysis/`, the citation checker, `MAPPING.md` and its tooling) and
`consensus.pdf`'s (`Spec/Consensus/`, namespace `Consensus`). **The branch
`pre-consensus1-purge` holds the last commit carrying all of it**, history included — the
entries below that cite removed files or their decision trails resolve there.
(`deps/lean-sts` remains the one submodule.)

Toolchain: pinned in `lean-toolchain` (Lean 4.32.2); Mathlib rev in `lakefile.toml` and
the rev `deps/lean-sts` requires must both match it — bump all three together.

## Inherited measured facts

One entry kept from the removed renderings' era, because this subtree's code cites it
(`on_tick`'s dependent-`if` discharge is built on it).

### What a hypothesis can reach past in a `do` block — 2026-08-21

Measured on the probe over four shapes, and the reason the assumptions had to go. A plain
assignment leaves the mutated variable a `let` **with a value**, so `isDefEq` walks back
through the whole chain of them, however long — a hypothesis stated in the signature about
the resulting store matches by definitional equality, and `assumption` finds it. Control flow
that mutates and has a **shared continuation** does not: the do-elaborator binds its result
to a fresh opaque binder, with no value.

| shape | store after it |
| --- | --- |
| `if c then (assign)` with a tail below | opaque — `__r✝ : Unit`, then a valueless store |
| `if c then (assign; return …)` with a fallthrough | then-branch concrete, fallthrough opaque |
| `if c then (assign; return …) else (return …)`, nothing after | both branches concrete |
| `for C in xs do (assign)` | opaque, always |

So the rule is about the shared continuation, not about `if` or `for`. Consequences:

- **A mutating branch inline with a proof-carrying call after it is impossible**, not merely
  awkward: inside the join point the store is a lambda-bound variable, nothing in scope
  relates it to what either branch built, and a `∀ S₂, …` hypothesis would need `assumption`
  to instantiate it, which it does not do. Only *values* cross a join point — which is why
  the `Except` result works and a hypothesis could not.
- The diagnosis is not in the error. It reports an unremarkable goal such as
  `⊢ S.t = actionTime r`; the opacity is visible only by reading the printed context for an
  entry with no `:=`.
- Two dead ends worth not repeating: hoisting the branch and the loop into named routines
  (`maybeJustify`, `acceptAll`) does work, but it forces the whole sequence to be duplicated
  in a `def` so the signature has a name for the final store; and `Reachable.coherent hpb hR`
  does not accept dot notation for the `Coherent` lemmas, its result unfolding to a `∀` first
  — write `Coherent.of_write_σ (hR.coherent hpb) …`.

## The `Consensus1` rendering — 2026-08-22 onward

### `consensus-1.pdf` is a *third* rendering — 2026-08-22 (then `Spec/Consensus1/`)

A newer variant of the draft arrived. It is a rewrite, not a revision: **block-only Goldfish**,
one store built up in three layers, and seven figures none of which matches the older draft's
six.

**It began beside the two older renderings, not in place of them** (Roberto's call, after
seeing the first attempt delete seven files; the coexistence ended with the 2026-08-24
purge). One mechanic from that era still shapes the tree: `FinsetM.lean`'s combinators
live in the root `Finset` namespace, where a second copy would collide, so this subtree
*imported* the second rendering's file — adding `Finset.imageM` on 2026-08-22, when
Roberto had the exception style carried through the set operations — until the purge
absorbed the combinators into this subtree's own `FinsetM.lean`.

**File layout.** `Model.lean` (Section 1's substrate and the wire objects), `Store.lean`
(Definition 1 plus the fields Sections 3.2 and 5.1 add), then `Fig<n>` per figure. The import
order is dependency order, not figure order: Figure 6's chain state is what `Σ.σ[·]` maps into,
and Figure 3's confirmation is what Figure 2's `on_tick` calls.

#### Decisions taken while rendering, each in a docstring at its line

- **`B.root` is a field of the abstract type `Root`** (Roberto, 2026-08-23; it began as a
  `Nat` with `0` at genesis, replacing the old `BlockHash` class). The entry below has the
  `Roots` class. Nothing constrains a block's root to match the post-state it would compute:
  the block *claims* one.
- **`nj` is a stored field of the chain state**, written by `advance_height` and read by the
  justify event. The older draft recomputed the test inline, which is a *different rule*: this
  one reads the `h_F` of the height's entry, not of the moment the justification fires.
- **`ghost` is the figure's own loop, bounded** (reshaped 2026-08-22 on Roberto's word — the
  first form, a fuel recursion `ghostFuel`, looked nothing like the figure). `Id.run do`,
  `let mut H := anchor`, and line 7's `loop` written `for _ in [:tree.card]`: the figure's
  `loop` terminates because the tree is a tree, which is an invariant of `Σ.T` and not a fact
  about the `Finset` the routine takes, so Lean gets the bound as a visible range instead. The
  cost is unchanged from the fuel form — one case the draft has not, the bound reached with an
  eligible child still available, which returns the block it stands on. A well-founded
  recursion would need the tree invariant *in the definition*.
- **The arg-max tie-break and line 25's `Finset` → `List` crossing each went through two
  designs before the nondeterminism adoption dissolved both** (entry below: the tie and the
  list order are picks). Two facts from those designs still hold: `Finset.toList` needs
  `Classical.choice`, so no computable route enumerates a `Finset` without an assumed
  order; and the alternative every form declined — list-valued vote tables — would make
  "at most two per validator" a property of a list and put `.toFinset` at every counting
  site (recorded in Figure 2's header).
- **Line 30's `for all B ∈ Σ.T` is a `Finset.fold`**, not a loop: no `ForIn` for `Finset`, and
  the body accumulates a *union*, which is commutative and associative — which is why the
  draft can write a loop over a set at all. Needed `Mathlib.Data.Finset.Lattice.Basic` in the
  import graph for the two instances, and the fold's result type annotated, or the instance
  search is stuck inside the `do` block.
- **Timestamps are three maps**, one per object kind, since Lean has no sum over them here.
  Each is `Option Int`, `none` standing for both "not processed" and the draft's
  `timestamp(B_gen) = −∞` — which costs nothing, no rule reading a block's timestamp.
- Absent for want of a consumer: Section 5.1's `E_F(Σ)`, and Section 3.4's `get_head`
  redirection — Section 5 redefines `get_head` again and its version is the protocol's.
  Section 4.1's E1/E2 slashing conditions sat in this list until 2026-08-24, when
  `Analysis/AccountableSafety.lean` rendered them. Section 3.4's `on_tick` line first sat
  here too, wrongly: Section 5 never touches `on_tick`, so the line is rendered — since
  2026-08-23 as its own reading, `Store.onTick` (entry below).

### The walk raises: `TieBreak.pick` — 2026-08-22, dissolved 2026-08-23

Roberto did not want the nonemptiness proofs inside `bestChild`. The routes weighed, each
declined for a stated reason: a total chooser with a junk value on `∅` (the Mathlib standard —
`n / 0 = 0` — but the silent-answer pattern this subtree already rejected once); a named
lemma above the definition (relocates the proof, keeps it); a linear order on blocks assumed
as a class (most faithful to "a fixed root order", but order-lifting plumbing). His call: the
chooser raises — a `TieBreak` class whose `pick` returned a member of the set or the
failure. The nondeterminism adoption (entry below) dissolved the class the next day: the
tie is a pick, and a pick from the empty set has no outcomes.

- **Subtype-coercion facts, measured**: the `Subtype.val`
  coercion fires at expected-type positions — `return b`, `return (← e)`, and `:=` onto a
  typed `mut` variable — but never at field access (`b.slot` fails) nor in an application
  whose implicit is still open (`Block.slot b` fails); `let ⟨B, hB⟩ ← e` destructures past
  the question entirely. Related, from the same sitting (commit
  `c2238d1`): the `=` elaborator does not insert a coercion around a `mut`-variable read —
  bare `B.parent = H` elaborates against a plain binder and fails against a `mut` one — so
  Figure 1's line 8 writes the coercion explicitly, `B.parent = ↑H`.

### The timed Goldfish routines carry their instants — 2026-08-23

Roberto: the functions supposed to run at specific times should say so by autoparam. The
`onSGFGVotingAction` precedent, retaken: `propose_block` requires `S.t = slotStart S.s`,
`goldfish_vote` requires `S.t = slotStart S.s + Δ`, `update_confirmation` requires
`S.t = slotStart s + 6Δ` — each an anonymous autoparam whose tactic is
`solve_by_elim [And.left, And.right]` (second pass, 2026-08-23; `by assumption` first): it
finds the instant even *inside a conjunction*, so a caller's dependent `if` on a
several-part condition discharges it with no `have`, and `on_tick`'s branches are pure
figure lines. A caller must still hold the fact as a hypothesis, named by `if h :` or
otherwise. `sg_vote` requires `S.t = SGSchedule.a (round
S.s)` (added 2026-08-23, second pass): its `a_r` is "a public parameter in this intermediate
protocol", which is exactly an ambient class — `SGSchedule` in `Model.lean`, the `Committees`
move — so the instant is stateable with no formula fixed. `on_tick` gained Section 3.4's
line, dispatching on it — inlined at first; later the same day the line became its own
reading, `Store.onTick` in `Fig5SGDuty.lean` (entry below), and the Figure 2 → Figure 5
import the inlining had forced flipped back. A correction from the same pass: Fig5's header
claim that Fig7 carried a final `on_tick` was wrong — Section 5 never touches `on_tick`.

`on_tick` discharges all three from its own tests: each `if` became dependent, and the
autoparam projects the tested instant out of the branch's conjunction, no `have` (the first
pass had one per branch) — the clock was written just above the
tests, so `S.t` reduces to `t` whatever the base, the join-point trick recorded on
2026-08-21. One line moved to make the third discharge a projection rather than a proof:
line 7 tests the figure's `t_s + 2Δ` in the form `t_{s−1} + 6Δ`, equal whenever `s > 0` —
the identity the 2026-08-22 docstring already stated — so no arithmetic is proved anywhere
in `Spec/`.

### Store-taking routines take the `Store.` prefix — 2026-08-23

Roberto: everything that takes a store should be in the `Store` namespace, for dot notation
— `S.updateConfirmation k`, `S.viable`, `S.processGoldfishVote vote`; the store need not be
the first parameter, dot notation filling the first `Store`-typed one. The layer-redefined
names were the exception (one namespace holds one `getHead`), first kept in layer
namespaces `Goldfish`/`SG`/`FG`; the third naming pass the same day replaced those with the
figure-named readings and full names at each `def` — the style sheet below carries the
scheme that stands.

### The duty result takes the framework's shape — 2026-08-23

Roberto: `propose_block` should return what an sts step wants, a state and the messages to
send. `Model.lean` gains `Message`, the three wire objects as one sum (`block`, `gfVote`,
`sgVote` — one message type per protocol, the lean-sts convention), and
`Fig2GoldfishDuties.lean` gains `DutyResult` with fields `state : Store Validator` and
`send : Finset (Message Validator)` — the field names of the framework's `NodeStepResult`,
whose `send` is a `Multiset` for framework-internal reasons this layer does not have.
All three duties return it — `propose_block` and `sg_vote` with their singleton sends,
`goldfish_vote` with `send := ∅` for a validator off the committee, its `Option` gone — and
`on_tick` does too, each action branch returning its duty's result directly (Roberto's
call; a union-accumulator form preceded it, and with it went `Message`'s only `DecidableEq`
consumer, so the deriving clause is gone again — the three instants are mutually exclusive,
distinct multiples of `Δ`). The 2026-08-22 note "the duties' broadcasts are dropped by
`on_tick`, the one place this rendering loses something" is repaired and void. The two
`process_*` handlers stay `Store → Store`: the figures give them no broadcast line, and
Section 1's "an honest node relays every object it processes" is network behaviour, the
wiring layer's to render. `DutyResult` sits in `Store.lean` because Figure 5 does not
import Figure 2.

### `Root` is abstract, and the proposer's root is assumed — 2026-08-23

Roberto's two calls, ending the root-as-`Nat` rendering.

- **A class, not a type parameter** — confirmed by Roberto 2026-08-23 after questioning it.
  The two are logically interconvertible (an instance binder is an implicit parameter, the
  class a bundle), so the choice is ergonomic: the class fixes type, order and genesis root
  *together*, unmixably, and instance search makes one vocabulary per context silent. The
  parameter form wins only for statements mixing two root vocabularies — a cross-instance
  simulation, say — which nothing foresees; if `Analysis/` ever wants one, explicit
  `@`-instances still express it.
- **`class Roots`** in `Model.lean` carries the abstract type: `Root : Type`,
  `genesisRoot : Root` (the draft says every block has a root, and genesis is a block), and
  `ord : LinearOrder Root` — the one thing this rendering still reads off a root,
  `update_finality`'s lex comparison `(h_j, J.root)`. `export Roots (Root)` gives the bare
  spelling, and a scoped instance surfaces the order.
- **Every inductive of the mutual family takes `[Roots]`**, `HeightPair` and `FinalityPair`
  included: Lean requires one parameter list across a `mutual` block, so the two that never
  mention a root carry the instance anyway. Everything downstream picks it up through one
  `variable {Validator : Type} [Roots]` per file. `blockBeq` compares roots by
  `decide (rt = rt')`, the `DecidableEq` coming from the order.
- **`class RootComputation`** in `Fig2GoldfishDuties.lean`:
  `compute : Block Validator → Nat → Root`, the assumed function computing the root a
  proposer writes from the block's parent and its slot (Roberto's correction; a first cut
  read it from the proposer and the store). `proposeBlock` and `onTick` lose their
  `root : Nat` parameter — line 25 writes `root := RootComputation.compute H s` — so the
  environment no longer threads a root through the tick. The draft calls the root the post-state root and defines the post-state only at
  Section 5, so the function is assumed, its answer unconstrained, exactly as a received
  block's claim is unchecked.

### The walk goes nondeterministic: `NDR`/`NDRE` adopted — 2026-08-23

Roberto: implement the scoped-out solution. This resolves the parked `for all` decision by
its fourth exit, measured on two probes
(kept). `Nondet.lean` is the machinery: `NDR α := Set α` (picks only, Mathlib's opt-in
`Set.monad` activated scoped), `NDRE α := ExceptT Error Set α` (picks and raising reads,
`Set (ResultOrExcept α)` under `.run`), the missing `Except`-into-`ExceptT` lift, the pick
`let x ←ᵖ s` over `Pickable` (`Set` or `Finset`), `listings` (a predicate, never an
enumeration), and a `ForIn` over `Finset` for any monad `Set` lifts into — pick a listing,
loop the list.

**What dissolved, all in one motion:**

- `TieBreak` — the tie at `bestChild` is `let W ←ᵖ top`: every resolution among the
  outcomes, a root order one of them; "the walk does not depend on the tie" becomes a
  provable singleton statement.
- `[LinearOrder (GoldfishVote Validator)]` and `toSortedList` — `propose_block`'s carried
  list is `let gfList ←ᵖ listings votes`, its order a genuine nondeterministic choice.
- **The one named deviation** — the walk had read Figure 7's height clause through the
  raw `Option`, its condition slot being pure — closed: the slot is
  `Block → ResultOrExcept Bool`, so the raising `goldfish_eligible` passes directly at
  line 29; the pure layers offer their conditions with `pure`.
- The `for all` macros and the `all` token — the two order-free loops are written as the
  sets they build: the view merge as one `biUnion` union, `sg_support` as the set-builder
  it always was.

**The tier map**: pure handlers stay pure (`sgVote` included); `viable`, `updateFinality`,
`FG.processBlock`, `goldfishEligible` keep plain `ResultOrExcept` (raising, no picks) and
lift into `NDRE` callers by `←`; the walk and everything that runs one — `bestChild`
(`NDR`), `ghost`, both `forkChoice`s, the three `getHead`s, `updateConfirmation`,
`proposeBlock`, `goldfishVote`, `onTick` — carry `NDRE`. `S.goldfishEligible` moved to
`Store` with `S.getHead`, their bare names being unique to the protocol layer.

**Consumption discipline**: inside a stack, compose by `←`; at the boundary a stack is a
relation, `res ∈ (f …).run` — the lean-sts step shape — and there is deliberately no
computable exit. What `Analysis/` owes changed shape with it: "the exception never fires"
is now `.error ∉ (…).run` on coherent stores, and "the walk does not depend on its picks"
is `(…).run` a singleton.

**Measured on the way** (the traps, each recorded at its site): a `do` block's result type
must *name* the stack or the binds elaborate in the `Set` monad; a `filterM` inside an
`NDRE` block must be ascribed to `ResultOrExcept` and lifted whole — at the stack itself its
fold would need `unionM` commutativity, which is *false* there, a pick with no outcomes
annihilating where an error survives (the `∈ᴹ` builder's expansion now pins the monad for
this reason); and a quotation's global names resolve at macro declaration, so `Notation.lean`
had to import `Raise.lean` before its expansion could name `ResultOrExcept`.

### `Spec/doc/` — reader-facing pages for the design — 2026-08-23

On Roberto's word ("perhaps in a doc folder under consensus-1 for now"): four markdown
pages under `lean/Spec/doc/` — `README.md` (index), `nondeterminism.md`
(`NDR`/`NDRE`, the pick, consumption as `res ∈ (…).run`), `naming.md` (the full-name
scheme, the `Fig<n>` table), `style.md` (the remaining rulings, one line each). They state
the decisions for a reader of the subtree; the decision trails stay here. **This file is
the record**: when a ruling changes, update the entry here and then the page. The "for
now" is Roberto's — the folder may move.

### `on_tick` splits into readings: `Fig2.onTick` and `Store.onTick` — 2026-08-23

Roberto: a general `on_tick` calling the sub-ticks, so Figure 2's looks like the paper.
`Fig2.onTick` is now exactly the figure's lines 1–8. `Store.onTick`, the protocol's, lives
in `Fig5SGDuty.lean` (whose header discusses Section 3.4) and renders "`on_tick` gains one
line" as the extension it states: run `Fig2.onTick`, then, at `t = a_r`, `sg_vote` on the
result's state — the clock is already written, so the dependent `if` hands `sg_vote` its
instant autoparam as Figure 2's own branches do. The fourth incrementally-redefined routine
under the naming scheme, and the only one whose extension is a call rather than a rewrite.

The import between Figures 2 and 5 flipped back with it: the Section 3.4 line was the only
thing Figure 2 took from Figure 5, so `Fig2GoldfishDuties.lean` dropped that import (and
its `[SGSchedule]` binder) and `Fig5SGDuty.lean` imports it instead.

Three refinements the same day, all Roberto's. The collision edge composes rather than
drops: on a schedule where `a_r` coincided with a Goldfish instant, `sg_vote` runs on that
duty's post-state and the return unions the two sends, so nothing is lost (on the draft's
own schedules the instants are distinct and the Goldfish send there is `∅`). The bound
result is `let res : DutyResult Validator ←` (briefly `S`, shadowing the store — Roberto
took the shadowing back), reads going through `res.state` — a `Coe (DutyResult → Store)`
would not shorten them, field notation never
inserting coercions (the `↑H` limit). And dependent `if`s bind no name when nothing uses
the hypothesis — `if _ : … then`, the autoparam tactic reading the anonymous hypothesis —
applied to all four tick branches. The send union is `Message`'s first equality consumer,
so `Message` now derives `DecidableEq`, exactly as its docstring had planned.

### Two parallel workstreams; `extract/` opened — 2026-08-23

Roberto: two things in parallel — (1) keep improving and expanding the `Consensus1`
definitions, in place; (2) a script that extracts, out of the Lean files, a document
similar to the source `consensus-1.pdf`. Stream 2 works against `extract/Consensus1-frozen/`,
a plain copy of `lean/Spec/` (frozen at `909b4f6`), so the live spec can keep
moving under stream 1; `extract/README.md` carries the rules (nothing imports the copy, no
build target reads it, refresh only on instruction). Roberto chose the target: LaTeX
compiled to PDF, figures plus prose. `extract/extract.py` is the v1 pipeline
(`python3 extract/extract.py`, output in the gitignored `extract/out/`): module headers →
section prose, docstring `(Figure N, lines a–b)` citations → figure membership and order,
`-- line n` comments → the pdf's line numbers, docstrings → note paragraphs; LuaLaTeX with
a DejaVu fallback carries the unicode, so there is no symbol-translation table. The open
part is the Lean-to-pseudocode rewriting: v1 prints lightly cleaned Lean, and the rewrite
rules are meant to accumulate in `clean_code_line`.

**v2 (2026-08-23) rewrites the figure bodies into the draft's own pseudocode style.**
Roberto's constraint: no rule fitted to the frozen files — every rule is keyed on Lean or
Mathlib surface syntax, or driven by tables harvested from the sources' conventions. The
harvested conventions: a docstring opening with a backticked paper form
(`` `Σ.gf_votes[k]` ``, `` `t_s = 4Δs` ``, `` `B_gen` ``) names that declaration's paper
symbol and access shape; the figure citation `name(args)` names a routine's paper signature,
and Lean params absent from it (the validator `i`, `isProposer`) stay hidden at call sites,
as the paper's own calls hide them; a structure whose field docstrings open `Σ.…` is the
paper's `Σ`, so the store-typed parameter renders `Σ`; "the tuple `(v, s, B)`" in a
structure's docstring makes its `.mk` a tuple; a constructor docstring's tuple template
(`` `(h, ⊥)` ``) renders anonymous-constructor equalities. Syntax-keyed rules: all binders
render `←`; dependent-`if` binders drop; top-level `∧`/`∨` become and/or, `∧` in a
set-builder becomes a comma; `X ← X ∪ {e}` becomes "add e to X"; `x := fun y => e` becomes
"define x(y) as e"; a `{state, send}` duty return becomes "broadcast m; call"; coercion and
`Option` noise strips (`↑`, ascriptions, `.toNat` (⌊⌋ over a division), `.toFinset`, `some`,
`pure`, `.get`, `.getD` — the last drops a default, the one lossy rule); `filterM`/`imageM`
fuse into set-builders, `biUnion` into a big union; `for _ in [:e]` is the figure's `loop`.
Typography follows the paper: bold keywords, small-caps routine names, italic variables,
sans field names, subscripts for `x_y` names, right-margin `▷` notes from the `-- line n`
comment text (dropped when they merely echo the rewritten code). Class fields without an
opening symbol fall back to namespace-stripped call form — `Committees.K s` renders `K(s)`,
not the draft's `K_s`, until the live spec's docstring opens with the symbol.

**v3 (2026-08-24): prose is opt-in, under the `## Extract` marker.** Roberto flipped the
default — instead of subtracting Lean-side commentary, only sections headed `## Extract`
(his keyword, chosen over Draft/Document/PDF for naming the destination without colliding
with "the draft") reach the PDF: a module header's marked section is the file's section
prose (`## Extract — X` titles it X), a figured routine's marked docstring section leads
its figure in, any other declaration's follows the figure. Unmarked prose — all of it, at
present — stays out, so the document is figures plus whatever has been deliberately
written for it. Marked prose and the figures' margin notes render in the draft's
typography: backticked spans go through the figure rewriter, falling back to mono exactly
when a span quotes Lean (binder keywords, `:=`, camelCase or Type-looking names).

**v5 (2026-08-24): the PDF becomes a real document, every number LaTeX's own.** On
Roberto's instruction ("apply your four moves", live spec untouched): definitions are
`amsthm` environments (`def:<slug>` labels), figures are captioned floats (`fig:<file
stem>` labels) rendered with `algorithmicx` — whose automatic line numbers replace the
draft's `-- line n` coordinates in the output, the comments staying as provenance and as
the margin notes' source; sections are numbered with a table of contents, their "Figure
N — " title prefixes stripped; the title page is stamped with the generating commit and
date. Prose never writes a generated number: `[fig:Name]`/`[def:slug]` forms resolve to
hyperlinked `\ref`s — the four hardcoded "Figure N" mentions in the frozen prose became
symbolic the same day.

**The frozen-copy discipline governed v1–v5 and ended the same day**: the extractor now
reads the live `lean/Spec/` (entry below), the `## Extract` sections' home is the live
spec itself, and the frozen copies moved to `archive/`, records nothing reads.

### `FinalityVote.lean`: the attestation-filling rules, imported from the first rendering — 2026-08-23

Roberto: the protocol determining finality votes, written by importing the logic from the
initial spec (`latex-specs` and the root `Spec` folder). `consensus-1.pdf` shapes the
attestation but never says how its pairs are filled; `lean/Spec/FinalityVote.lean`
carries the first rendering's voting strategy (`Spec/Defs/Voting.lean`) over:
`SigningHistory` (τ/T/lock per height, writes returned with the pair), `heightVote` (the
five-case current-height rule under the confirmed ceiling), `finalityVote` (sign
`(h_j, J)` when ahead, chained, certified, record-consistent; lock on first release), and
`Store.fgVote`, whose own body is the composition — finality first, so the lock write is
visible to the height rule's read. A store-free `fgVote` layer briefly sat between the
pair rules and the wiring, mirroring the first rendering's; Roberto had it folded — it
added nothing but a name, and the name collided: inside `def Store.fgVote` a bare `fgVote`
resolves to the def itself (measured — the fix while it existed was a qualified
`Consensus1.fgVote`). The crossing decisions, for review (they were the module header's
list until the 2026-08-24 de-referencing sweep, entry below; this is now the record):
subtree pair encodings (`.timeout` → `emptyTarget`, `.commit` → `pair`); all four
fork-choice fields from the store (`h_F` no longer explicit); `C = Σ.live_confirmed`;
context read raising off `Σ.σ[live_confirmed]` (the first rendering degraded to an empty
pair; no `process_slots` exists here so the stored state is read as is); `T = some σ.T_h`
(never `⊥` here, the fallback vanished); `r = round Σ.s`; `head` and `hasJC` still
explicit. One trap hit: inside `def Store.fgVote` the bare name `fgVote` resolves to the
def itself, so the pure rule is called as `Consensus1.fgVote`. No citations, per the
2026-08-19 pivot — the docstrings are self-contained and name `Spec/Defs/Voting.lean` as
the working source.

Second pass, same day (Roberto): the record moved into the store and the rules moved onto
it. `SigningHistory` and its writes live in their own `SigningHistory.lean`, imported by
`Store.lean` (third pass — a structure is closed, so the field line itself cannot leave
the store file; only the type could). Its fields carry speaking names,
`signedEmptyTarget`/`firstTarget`/`finalityTarget` (Roberto asked for better than the
first paper's `τ`/`T`/`lock`; "first" is the record's once-only discipline; the third was
`firstLock` until later on 2026-08-24, its write `saveLock` now `saveFinalityTarget`). The store gains the field `Σ.H`
(its docstring and the header table say it is not the draft's), `Store.gen` starts it
empty. `Store.heightVote` (raising — it does the `Σ.σ[live_confirmed]` read itself) and
`Store.finalityVote` read their inputs from the store and return the pair with the updated
store; `Store.fgVote` threads it — finality, then height, then the attestation. Two more
collapses fell out of store access, both on the crossing list: the ceiling always exists
(`live_confirmed` is a block from genesis on, so the first rendering's nothing-confirmed
case is unrepresentable), and the two heights are the same state's (`hC = k`), so the
`hC ≥ k` conditions hold outright and are unwritten. The explicit-`H` threading and the
qualified-call trap are history from the first pass. The pair rules return a named
structure, not a product (Roberto, 2026-08-24, the `DutyResult` move): `SigningResult`
(`pair`, `state`; the field was `signed` for a day). `Store.fgVote` itself returns a
`DutyResult` like every duty (Roberto, same day): the attestation travels as
`Message.attestation` — a constructor the draft does not have, the wire decision recorded
on it (the draft never says how attestations reach a proposer; the first specification's
attestation is a wire message, and the import keeps that answer). Two removals later on
2026-08-24, both Roberto's: `hasJC` is gone — in this draft justification is an on-chain
fact, the store's replayed chain being the evidence, so there is no separate
certificate-knowledge to model — and `fgVote` takes no
identity parameter: the store carries its node's validator as the new field `Σ.i`
(not the draft's; the draft's `ℓ` is ambient in its figures), fixed at `Store.gen`,
which now takes it. The other duties still take `i`; whether they switch to `Σ.i` is
open.

### `ResultOrExcept` is `DRE` — 2026-08-24

Roberto: `NDRE` is the nondeterministic result with exception, so the deterministic one
is `DRE`. The `Consensus1` abbrev renamed subtree-wide (code, docstrings, doc pages);
`Raise.lean`'s header carries the naming note, including the surviving reason the bare
name `Result` was never taken. **Only this subtree**: the second rendering's
`Consensus.ResultOrExcept` keeps its name, as does every dated entry below — they record
what was. Historical searches need both names.

### Duties go monadic: `DutyM` adopted — 2026-08-24

The trail: `DutyResult.withSend` (the tick's send union) prompted "any alternatives"; the
duty-monad option was probed twice — store and outbox both ambient, **declined**
(Roberto: the functions must keep their input `Store`; ambient identity also cost the
instant autoparams) — and outbox only, adopted ("ok"). The machinery landed in its own
`Duty.lean`, merged into `Nondet.lean` later on 2026-08-24 (entry below): `NDREB α
= StateT (Finset (Message _)) NDRE α` — nondeterministic result with exception and
broadcasts, the effect-inventory name continuing `DRE`/`NDRE` (Roberto; the first name,
`DutyM`, lasted an hour — the `-M` suffix here marks monadic variants of named pure
operations, which a duty monad is not) — plus `broadcast` and `NDREB.outcomes`. The named
`runDuty` of the probes does not exist — Roberto: it "reads off compared to the paper" —
its content folded into `outcomes`, the one boundary, so no `run` appears anywhere in
`Spec/` and the wiring will read `res ∈ (…).outcomes`.

What moved: the five duties (`proposeBlock`, `goldfishVote`, `sgVote`, `fgVote`, both
`onTick`s) are `… → NDREB (Store _)` — store in, store out, instant autoparams untouched
since the store stayed a term — with `broadcast` at the draft's own broadcast lines and
`return S.process… vote` closing each. The ticks compose by calling: Figure 2's sends
cross the `if` inside the outbox, so `withSend` lost its consumer and is parked in
`OldDefs.lean`; `sgVote` stopped being pure (`Id.run do` → the monad). `DutyResult` stays
in `Store.lean` as the boundary object nothing returns. The pair rules are untouched —
they broadcast nothing.

Measured on the way: the outbox sits *inside* the nondeterminism (`StateT` over `NDRE` =
`outbox → NDRE (α × outbox)`), so each outcome carries its own sends — necessary, a
picking duty broadcasting differently per pick; and the store-ambient variant's autoparam
loss is a general fact — a precondition needs the store as a *term*, which is the
recorded reason the store stays explicit.

### The `DC` style sheet — running list (named `Consensus1` until 2026-08-24)

Every stylistic call Roberto has made for this subtree, in one place; the dated entries
above carry the reasoning, the docstrings at each point of use carry the mechanics. Update
this list when a new call lands.

- **Raise, never answer silently — and since 2026-08-23, branch rather than assume.** Map
  reads are raising brackets (`Σ.σ[B]`, `Σ.timestamp[x]` via `TimeMap`), set operations that
  read them go through `filterM`/`imageM`, and the raw `Option` stays reachable by
  application. The walk and the duties carry `NDRE` (`Nondet.lean`): ties and list orders
  are picks (`←ᵖ`), every resolution among the outcomes. No deviation stands.
- **Pseudocode spelling, gaps closed in `Notation.lean` and `Nondet.lean`**: assignment
  arrows (incl. bare identifiers and two-level maps), `|s|` for `Finset.card` (cost: the
  `abs` bars, shadowed in-namespace), the raising set-builder `let y ← {x ∈ᴹ s | p}` (a
  `doElem`, necessarily — the term-macro form loses the `←` to the outer `do`'s lift; its
  expansion pins `DRE` so it lifts whole inside `NDRE`), and the pick
  `let x ←ᵖ s`. The `for all` productions are **retired** (2026-08-23, resolving the parked
  review): the order-free loops are written as the sets they build (`biUnion`, the
  set-builder), and a genuinely order-sensitive loop would use `Nondet.lean`'s `for` over a
  `Finset`. The `all` token is freed with them.
- **No `match` and no `|` alternatives in spec bodies** — the dependent-`if` idiom;
  recursion patterns like a `for`-range bound are the tolerated shape. **Absence is tested
  `x ≠ ⊥`, never `.isSome`** (Roberto, 2026-08-23), and in a raising body extraction is
  the lift: `let y ← x` binds the value or raises, via the scoped
  `MonadLift Option DRE` in `Raise.lean` (Roberto, 2026-08-24, "do that, also
  wherever applicable"). Behind a plain
  `if x ≠ ⊥` the raise is unreachable; the accepted cost, stated at the instance, is
  that dropping the test leaves compiling code that raises where a rule meant to fall
  through. The autoparam extraction that did check at the site, `Option.value`, lost its
  three consumers to the lift the same day and is parked in `OldDefs.lean` (revived by a
  *pure* body that must extract; its measured trap travels with it — dot notation
  resolves fields in the type's own namespace only, hence `_root_.`). The store's map
  machinery (`GetElem` instances, the `StateMap` membership) keeps `.isSome` internally —
  the rule is about spec bodies. **No `∣` (divides)**: write
  `% … = 0`.
- **Messages are built by named `mk`** (`GoldfishVote.mk (validator := i) …`); `Block.mk`
  likewise names its fields at Figure 2 line 25; `DutyResult` keeps the brace form
  `{ state := …, send := ∅ }`; `match` patterns untouched.
- **Full names at each `def`, no namespace blocks** (Roberto, 2026-08-23, third pass —
  layer namespaces `Goldfish`/`SG`/`FG` preceded it, git history has them). `Store.…` for
  whatever a store flows into, so dot notation works; `Fig<n>.…` for a superseded reading of
  an incrementally-redefined routine (`Fig1.getHead`, `Fig4.getHead`, `Fig2.processBlock`,
  `Fig1.goldfishEligible`, `Fig2.onTick` — the last reading of each is the protocol's and
  bears the plain `Store` name; `on_tick`'s is Section 3.4's, rendered as a call — entry
  above); a bare name for everything defined once (`ghost`, `goldfishScore`, its
  prefix spelled since no namespace carries it). `voters_count` is a `let` at each of its
  three sites, being a local in the pdf, like the equivocator set.
- **Scheduled routines carry their instant as an anonymous autoparam**
  (`… := by solve_by_elim [And.left, And.right]`); `on_tick` discharges them with
  dependent `if`s alone, no `have`s (second pass 2026-08-23; entry above). The `if`s bind
  `_`, not a name — the tactic reads the anonymous hypothesis; a dependent `if` names its
  hypothesis only where the proof is used (`if hp :` at Figure 7's `(B.parent).get hp`).
- **The ambient environment is classes**: `Electorate`, `Committees`, `Params`, `Roots`
  (abstract `Root`, its order, genesis's root), `RootComputation`, `SGSchedule`. Class over
  type parameter, confirmed 2026-08-23. Two former members dissolved into nondeterminism the
  same day: `TieBreak` (the tie is a pick) and `[LinearOrder (GoldfishVote Validator)]`
  (the carried list is a picked listing).
- **Duties run in `NDREB`** (`Nondet.lean`, 2026-08-24; entry above): the outbox threaded
  over `NDRE`, `broadcast` the protocol's own verb, the store an explicit input and output —
  no caller unions sends. `DutyResult` survives at the boundary only, `NDREB.outcomes`
  being what the sts wiring and `Analysis/` consume; `on_tick` returns from each action
  branch directly.
- **Explicit coercion where a `mut` read blocks insertion**: `B.parent = ↑H`.
- **Line comments cite the figure's own numbering**; docstrings are self-contained and cite
  nothing (the 2026-08-19 pivot).

### The spec moves up: `Spec/` and `Spec/Defs/` — 2026-08-24

With one rendering left, its `Consensus1/` directory level said nothing (Roberto: "the
spec should live under Spec"). The figure files now sit directly under `lean/Spec/`, and
the definition and vocabulary files under `lean/Spec/Defs/` — the first rendering's
layout, whose `Spec/Defs/` name returns. `doc/` moved up with them. Module names follow
(`Spec.Fig1GoldfishWalk`, `Spec.Defs.Model`); the namespace stays `Consensus1`. Path
mentions in the dated entries above were left as written — they describe the layout of
their day.

### Docstrings stop narrating their own history — 2026-08-24

The audit pass over the purge (Roberto: "purging the Lean docstrings of history about
changes"): attributions, was-X-until-Y notes, git-history and branch pointers, and probe
filenames left the `.lean` docstrings — this file is where that history lives. Two
provenance notes stayed then — `FinalityVote.lean` naming the source of its imported
strategy, and `OldDefs.lean` entries saying where each parked piece came from — and fell
in the same day's second, stricter sweep (entry below).

### Accountable safety: the statement imported — 2026-08-24

Roberto: import the accountable-safety theorem statements (only the statements) from the
first specification's analysis and adapt them. `lean/Analysis/AccountableSafety.lean`
(the `Analysis` lib returns to `lakefile.toml` for it): `E1`, `E2` over this rendering's
pair constructors, `IncludedOn`, `replay` (`state_transition` folded along the parent
link — store-free, what every coherent store's `Σ.σ[B]` equals), and `AccountableSafety`
as a named `Prop`, so nothing claims a proof and `make check` stays green. The adaptation
decisions, each one to revisit (they were the module header's bullet list until the
de-referencing sweep, entry below; this is now the record): totality deletes the source's
two `≠ invalid` hypotheses (every block replays to a state, there is no invalid);
`replay` is defined here because the statement must be store-free; "conflicting" is
`¬ Compatible` (the source defines *compatible*, `∼`, and names no relation for its
negation); the pair encodings are this rendering's (`.commit` → `FinalityPair.pair`,
`.timeout` → `HeightPair.emptyTarget`); and the height binders the source itself called
redundant are dropped — "for some height `h`" lives inside E1 and E2's own pairs. The
source statement and its proof live on the `pre-consensus1-purge` branch
(`Analysis/Theorems.lean`, its Lemma 11 chain).

### `doc/guide.md`: reading the spec without Lean — 2026-08-24

Roberto: a concise, human-written reading guide for people who know code and paper
pseudocode but not Lean, explaining only what is unfamiliar. `lean/Spec/doc/guide.md`:
the shape of a file, the effect scale read off return types (plain/`DRE`/`NDR`/`NDRE`/
`NDREB`), the pick and the outbox, and the small bumps (`⊥`, `Finset`, records, class
assumptions, instant autoparams). Linked first from `doc/README.md`.

### The extractor reads the live spec — 2026-08-24

Roberto: "the source should be the Spec folder". `extract/extract.py`'s `SRC` is now
`lean/Spec/`, read recursively (`Defs/` included); the frozen copies stay as records,
nothing reads them. Found in the same step: the live docstrings carry no
`(Figure N, lines a–b)` citations — those were extraction-side edits living only in
`Consensus1-frozen-2/` — so `CITE_RE` matches nothing, no routine is figured, and the
generated document is prose-only. The paper-form signature spans (`` `ghost(anchor,
tree, score, eligible)` ``) and the `-- line n` comments are still in the spec; what is
missing was the marker that a `def` is figured — settled the same day, entry below.

### The spec drives the extraction's structure; nothing is hardcoded — 2026-08-24

Roberto, five instructions in one sitting, all landed in `extract/extract.py` (its
module docstring's v5 note and `extract/README.md` carry the conventions):

- **Files render in alphabetical order** of their path under `lean/Spec/`; a file with
  nothing marked `## Extract` emits no section. `FILE_ORDER` is deleted. Today the
  alphabetical order reproduces the old hardcoded one exactly (`Defs/` sorts before
  `Fig*`; only Model, Store and the seven figure files carry marks).
- **A `def` is figured — rendered as pseudocode — when its own docstring carries an
  `## Extract` section** (a bare heading with no prose counts). The section's prose
  leads the figure in, as before. Alternatives considered and dropped: deriving
  figuredness from body shape (`do`/`let`) misclassifies `Q_target`-style symbol defs
  and the `Beq` helpers; a root-module import list authors order but not figuredness.
- **Routines render in declaration order** within their file; the `line_a` sort is gone.
- **The paper form derives from the Lean `def`**: name snake-cased from the Lean name's
  tail, signature from the explicit params in order, store-typed params as their
  structure's symbol. A docstring opening with a pure call span `` `name(args)` ``
  overrides — still the way to hide params (`on_tick(Σ, t)` hides `i`, `isProposer`).
- **Any `--` comment is the margin note** of the statement it trails or precedes; the
  `-- line n` convention is retired (a legacy `line n:` prefix is stripped while the
  sources still carry them). The join-to-numbered-predecessor peephole went with it.
- **The frozen copies moved to `archive/`** — kept as records, outside `extract/` so
  the extractor cannot reach them; nothing reads them.

Same day, on instruction ("add Extract to the files so the output prints all the
figures + the finality vote"): the 30 figured defs are marked — the 27 that carried
citations in the frozen copy (Fig5's `Store.onTick` stays unmarked, the draft giving it
as prose, "gains one line", not figure lines) plus `FinalityVote.lean`'s three rules
(`Store.heightVote`, `Store.finalityVote`, `Store.fgVote`, paper forms derived:
`height_vote(Σ)`, `finality_vote(Σ)`, `fg_vote(Σ, head)`). `dc.pdf` renders all eight
figure blocks; `make check` green. The marking script and the fixture are gitignored
under `extract/out/` (`_add_marks.py`, `_mark_test.py`, `_run_test.py`).

Later the same day, two prose conventions (Roberto: render the equation rows above the
draft's state-transition figure without duplicating strings): `[eq:name]` in
`## Extract` prose expands to the named declaration's docstring opening span — the
formula lives once, at the definition site; keyed by Lean name, unique Lean-name tail,
or unique harvested paper symbol — and a paragraph of nothing but backticked spans
and/or `[eq:…]` refs renders as a centered display line, items quad-separated.
Placement stays authored: the reference is written where the equation should appear.
Typography same day: symbol glyphs fall back to Latin Modern Math before DejaVu
(weight-matched, no more bold-looking `⪯`/`∈`), no space after a quantifier
(`∃a ∈ votes`, as math sets it), each figure's algorithm block boxed as the source
document boxes its figures, a numeral joined to a short symbol by thin space (`2W`),
a primed letter (`T'`) kept out of the mono fallback, and a bare argument-less mention
of a callable rendered as the name, not a padded call.

Evening, on instruction ("apply the above to the live spec so that it looks like the
source document as much as possible"): the `-- line N` comments are gone from the spec
(bare markers deleted, prefixed text kept, the header sentence describing the
convention deleted); files in a subdirectory render before the root files (the
numeric renames had pushed `Defs/Model` and `Defs/Store` after `08_` in a plain path
sort, and the document opens with substrate and store); and the marked prose was
brought up to the source document section by section — displays and `[eq:…]` refs
throughout, the slot-action schedule table, E1/E2, and the wire objects introduced
per layer (SG vote in `04_`, attestation in `06_`) instead of all in Model. The
document now tracks the source's five-section structure with matching definition
numbering (1 Store, 2 Goldfish score and walk, 3 Latest vote, 4 Chain state,
5 Viability).

The last coordinates left the same evening (Roberto: "we should not have Figure N;
makes no sense now"): module titles drop the `Figure N —` prefix (the extractor's
caption is now the section title, its prefix-strip rule deleted), every `Figure N` and
`line N` mention in docstrings, headers and `doc/` pages was reworded to layer
language, a Lean name, or a file name, and `style.md`'s line-comment rule now says
comments describe. The `Fig<n>` declaration names stay, re-read as "the number of the
file that defined the superseded reading" — renaming them (e.g. to nothing, or to file
names) is open, Roberto's call. Not carried over: the source's `E_F(Σ)` evidence-set display (nothing
in this document consumes it) and `Σ.timestamp(B_gen) = −∞` in the store's initial
values (not checked against the Lean).

### The identity is the protocol, and the spec speaks as the source of truth — 2026-08-24

Roberto, in sequence: "this is not anymore a formalization of consensus-1.pdf. It is the
formalization of Ethereum decoupled consensus"; then remove every reference to
`consensus-1.pdf` from the README and from all docstrings — "assume no knowledge of
consensus-1.pdf": the spec being the source of truth, Definition-number, Section-number
and figure-line citations of the pdf make no sense; and (twice, emphatic) docstrings
narrate no history at all — the history goes here. What fell in the sweep, beyond the
first audit's scope: `FinalityVote.lean`'s "what changed in the crossing" section (the
record is the 2026-08-23/24 entries above) and its two module-header pointers, inlined;
`AccountableSafety.lean`'s adaptation bullets (record above); `Spec.lean`'s history
paragraph; `OldDefs.lean`'s where-it-came-from narrations; `Model.lean`'s `Message`
first-specification paragraph, rewritten as what the constructor is for; every residual
"draft"/"pdf"/"previous rendering" token in `.lean` docstrings and the `doc/` pages
(`naming.md`'s table header was "pdf routine"; `Store.onTick`'s home is named as
`Fig5SGDuty.lean`, not a section number). Layer language — availability, SG, finality —
replaces section numbers. Two things deliberately kept: the "measured YYYY-MM-DD" stamps
on Lean-behavior facts (dated measurements, not spec history), and
`AccountableSafety.lean`'s pointer to the old proof on the `pre-consensus1-purge` branch
(a resource for whoever proves it here, marked "a starting point, not a citation").

### `README.md` is a front door — 2026-08-24

Roberto: someone landing on the repository should get where the spec is and be able to
jump to it at once, and should come away expecting it to be easy to read without the
README saying so. So the README is navigation only: the one-line identity, where the spec
lives with an `sgVote` snippet showing what the routines look like, links to the guide /
file map / design pages / `Analysis/`, the extractor line, and Building. Removed on his
instruction: the natural-language protocol description, the history section, every
`consensus-1.pdf` mention, every local-file mention. Per-file descriptions moved to
`doc/README.md`.

### `make extract` renders `extract/out/dc.pdf` — 2026-08-24

Roberto: the extractor's output is `dc.pdf`; a make target runs it and is documented in
the README's Building list. `extract/out/` is gitignored — no PDF is committed.

### `FinalityVote.lean` moves to the spec root — 2026-08-24

Roberto: "I want FinalityVote to be part of the root spec." `git mv` from `Spec/Defs/` to
`Spec/`, module `Spec.FinalityVote`; the doc file map lists it with the algorithm files.

### `Duty.lean` merges into `Nondet.lean` — 2026-08-24

Roberto: with the duty monad being nondeterminism machinery, the filename said nothing.
`NDREB`, `broadcast` and `NDREB.outcomes` moved into `Nondet.lean`, which gained
`import Spec.Defs.Store` (acyclic — nothing below `Store` imports `Nondet`) and a
duty-monad section in its header; `Duty.lean` is deleted, its importers (Fig2, Fig5,
`FinalityVote.lean`, `Spec.lean`) rewired, the doc pages updated.

### The spec files are numbered: `XX_Name.lean` — 2026-08-24

Roberto: rename the Lean spec files to `XXName`, `XX` a double-digit number, dropping the
`Fig` prefix; refined the same day to `XX_Name`. His picks, asked: `XX` keeps the figure
numbers (over dependency order), and `Defs/` stays untouched. So `Fig1GoldfishWalk.lean` →
`01_GoldfishWalk.lean` through `07_FGStore.lean`, and `FinalityVote.lean` →
`08_FinalityVote.lean`. Digit-leading module names need guillemets:
`import Spec.«01_GoldfishWalk»`. The `Fig<n>.…` declaration
prefixes are unchanged — the naming scheme still keys on the figure headers. Accepted
consequence, decided knowingly: the extractor renders files in alphabetical path order
and digits sort before `Defs/`, so the extracted document now opens with the eight
numbered files and puts the Model and Store sections last; if that order is wrong it is
the extractor's to fix. The `[fig:…]` labels in `## Extract` prose follow the stems
(`[fig:02_GoldfishDuties]`), since the extractor derives `\label{fig:<stem>}`.

### The namespace is `DC` — 2026-08-24

Roberto: rename the namespace `Consensus1` to `DC`. All declarations now live under
`DC` (`DC.Store.getHead`, …); the style sheet's heading follows, as do the doc pages and
`CLAUDE.md`'s pointer to it. Dated entries above keep `Consensus1`, the name of their
day — historical searches need both names, as with `ResultOrExcept`. The `a_r` schedule
kept its `SGSchedule.a` spelling when the class became a definition earlier the same day
(entry above is the class's era; the formula is `Model.lean`'s docstring).

### `doc/guide.md` gains the typing table — 2026-08-24

Roberto: write how to type the symbols people might not know (`←ᵖ`, `⪯`, …). A table of
the VS Code Lean abbreviations (`\l`, `\l\^p`, `\preceq`, `\bot`, …) with the hover tip,
in the guide before "Where to go deeper"; the guide itself de-drafted in the same pass —
it now speaks of paper pseudocode and the protocol, no external document.

## Next

0. **`consensus-1.pdf` is rendered as `Spec/`, and everything builds.** All
   seven figures are in; the nondeterministic architecture (2026-08-23), the duty monad
   `NDREB` (2026-08-24) and the imported finality-vote strategy are adopted. Open, in
   order of readiness:
   - **the sts wiring**: a step consumes a duty as `res ∈ (….outcomes)`; `deps/lean-sts`'s
     `StsMultisetLog` is the target, and the framework-layer audit (its `Execution.lean`
     and `Schedule.lean`) is owed before trusting it.
   - **`Analysis/` for this draft** (none exists): "the exception never fires" as
     `.error ∉ …` on coherent stores, "the walk does not depend on its picks" as a
     singleton outcome set. The `coherence-invariant` branch predates this store and does
     not transfer.
1. **The extractor workstream** (`extract/`): the conventions and rewrite rules are in
   `extract/README.md`; the input is the live `lean/Spec/` (2026-08-24), the spec
   drives the structure, and all eight figure blocks render (entry above).
2. `README.md` is refreshed before a push, not per commit; a push is long overdue.
