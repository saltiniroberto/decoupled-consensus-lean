import Spec.Defs.Model
import Spec.Defs.Notation
import Spec.Defs.FinsetM
import Spec.Defs.Raise
import Spec.Defs.Nondet
import Spec.Defs.ForkChoice
import Spec.Defs.OldDefs
import Spec.Defs.SigningHistory
import Spec.«06_StateTransition»
import Spec.Defs.Store
import Spec.«01_GoldfishWalk»
import Spec.«03_AvailableConfirmation»
import Spec.«02_GoldfishDuties»
import Spec.«04_SGForkChoice»
import Spec.«05_SGDuty»
import Spec.«07_FGStore»
import Spec.«08_FinalityVote»
import Spec.«09_Healing»

/-!
# The specification

One import per file. **This library is the specification of Ethereum decoupled
consensus**, under namespace `DC`. The algorithm files sit directly under
`Spec/`, and everything they are written in terms of sits in `Spec/Defs/`. The protocol
is block-only Goldfish: one store built up in three layers — availability, SG, finality —
with `ghost` as a named building block, per-slot committees, block-carried Goldfish votes
as the only relay channel, timestamps on every object, and a relative-majority SG fork
choice.

**The layers define incrementally, and the old readings are figure-named.** Each layer
redefines `get_head`, and the finality layer redefines `process_block` and
`goldfish_eligible` as well; a paper-style presentation replaces a reading, and Lean
cannot. The last reading
of each is the protocol's and bears the plain `Store` name (`S.getHead`, `S.processBlock`,
`S.goldfishEligible`); each superseded reading is named by its figure — `Fig1.getHead`,
`Fig4.getHead`, `Fig2.processBlock`, `Fig1.goldfishEligible`. Store-taking routines sit in
`DC.Store` for dot notation; everything defined once is bare (`ghost`,
`goldfishScore`); there are no namespace blocks, every definition carrying its full name at
its own `def`.

`Spec/Defs/` holds the non-algorithm files: `Model.lean` (the substrate and the wire
objects), `Store.lean` (the store, with the fields each layer adds),
`SigningHistory.lean` (the signing record behind the finality-vote rules — see
`08_FinalityVote.lean`), `Notation.lean` (the assignment macros and the raising set-builder),
`Raise.lean` (the failure vocabulary: `Error` and `DRE`), `FinsetM.lean` (monadic filter
and image over a `Finset`), `Nondet.lean` (the nondeterminism vocabulary: `NDR`, `NDRE`,
the pick, and the duty monad `NDREB` with `broadcast`), `ForkChoice.lean` and
`GoldfishWalk.lean` (the classes the walk's redefined routines are reached through, one
instance each, held by the layer whose reading is the protocol's), and `OldDefs.lean`
(parked definitions kept compiling; nothing may import it). The import order is dependency
order rather than figure order: Figure 6's chain state is what the store's `Σ.σ[·]` maps
into, and Figure 3's confirmation is what Figure 2's `on_tick` calls.
-/
