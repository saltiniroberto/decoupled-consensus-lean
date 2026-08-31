import Spec.Defs.Model
import Spec.Defs.Notation
import Spec.Defs.FinsetM
import Spec.Defs.Raise
import Spec.Defs.Nondet
import Spec.Defs.OldDefs
import Spec.Defs.SigningHistory
import Spec.«06_StateTransition»
import Spec.Defs.Store
import Spec.«01_GoldfishWalk»
import Spec.«02_GoldfishStore»
import Spec.«04_SGForkChoice»
import Spec.«05_SGDuty»
import Spec.«07_FGStore»
import Spec.«08_FinalityVote»
import Spec.«09_Healing»
import Spec.«10_AvailableConfirmation»
import Spec.«11_Duties»

/-!
# The specification

One import per file. **This library is the specification of Ethereum decoupled
consensus**, under namespace `DC`. The algorithm files sit directly under
`Spec/`, and everything they are written in terms of sits in `Spec/Defs/`. The protocol
is block-only Goldfish: one store built up in three layers — availability, SG, finality —
with `ghost` as a named building block, per-slot committees, block-carried Goldfish votes
as the only relay channel, timestamps on every object, and a relative-majority SG fork
choice.

**One definition per routine, in dependency order.** The protocol's layers build some
routines up — `get_head`, `process_block`, `goldfish_eligible`, `on_tick` — and what is
rendered here is the assembled definition of each, once. The earlier forms are not written
out: a reader auditing this spec is auditing the protocol, not its presentation.

That fixes the file order, and the file numbers follow it. A file may name only what an
earlier file defines, so the fork choice's tree comes before the duties that walk it
(`09_Healing.lean` before `11_Duties.lean`) and available confirmation sits between them.
The numbers skip `03`, which the confirmation file left when it moved to `10`.

Store-taking routines sit in `DC.Store` for dot notation; everything defined once and
store-free is bare (`ghost`, `goldfishScore`); there are no namespace blocks, every
definition carrying its full name at its own `def`.

`Spec/Defs/` holds the non-algorithm files: `Model.lean` (the substrate and the wire
objects), `Store.lean` (the store, with the fields each layer adds),
`SigningHistory.lean` (the signing record behind the finality-vote rules — see
`08_FinalityVote.lean`), `Notation.lean` (the assignment macros and the raising set-builder),
`Raise.lean` (the failure vocabulary: `Error` and `DRE`), `FinsetM.lean` (monadic filter
and image over a `Finset`), `Nondet.lean` (the nondeterminism vocabulary: `NDR`, `NDRE`,
the pick, and the duty monad `NDREB` with `broadcast`), `GoldfishWalk.lean` (the tree and
the eligibility condition that `get_head` takes from the layer) and `Tick.lean` (the
protocol's `on_tick`) — each one class with one instance, held by the layer whose reading is
the protocol's — and `OldDefs.lean`
(parked definitions kept compiling; nothing may import it). The import order is dependency
order rather than figure order: Figure 6's chain state is what the store's `Σ.σ[·]` maps
into, and Figure 3's confirmation is what Figure 2's `on_tick` calls.
-/
