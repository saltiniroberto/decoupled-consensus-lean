import SpecM.Defs.Model
import SpecM.Defs.Notation
import SpecM.Defs.FinsetM
import SpecM.Defs.Raise
import SpecM.Defs.Nondet
import SpecM.Defs.ForkChoice
import SpecM.Defs.OldDefs
import SpecM.Defs.SigningHistory
import SpecM.«06_StateTransition»
import SpecM.Defs.Store
import SpecM.«01_GoldfishWalk»
import SpecM.«03_AvailableConfirmation»
import SpecM.«02_GoldfishDuties»
import SpecM.«04_SGForkChoice»
import SpecM.«05_SGDuty»
import SpecM.«07_FGStore»
import SpecM.«08_FinalityVote»
import SpecM.«09_Healing»

/-!
# The specification — frozen copy

**This library is a copy of `Spec` as it stood on 2026-08-27**, taken so that the
experiment of threading the store through a monad has somewhere to happen. The source is
the working tree at commit `c0ef96e` ("BlockTree: a root and the blocks a walk may
descend", branch `healing`) together with the edits to `01_GoldfishWalk`,
`03_AvailableConfirmation`, `04_SGForkChoice`, `07_FGStore`, `08_FinalityVote`,
`09_Healing` and `Defs/Model` that were uncommitted at that moment; the commit that adds
this library is what records those bytes. `Spec` is the specification and stays as it is; nothing here is read as the protocol until it is carried
back. The copy differs from its source only in the module names on its `import` lines: the
files, the namespace `DC`, and every definition's name are the same. Only the Lean files
were copied: the reader-facing pages stay at `Spec/doc/`, unduplicated. Because the namespace
is shared, no file may import from both libraries.

The text below is the source library's, and describes what was copied.

## The specification

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
the pick, and the duty monad `NDREB` with `broadcast`), and `OldDefs.lean`
(parked definitions kept compiling; nothing may import it). The import order is dependency
order rather than figure order: Figure 6's chain state is what the store's `Σ.σ[·]` maps
into, and Figure 3's confirmation is what Figure 2's `on_tick` calls.
-/
