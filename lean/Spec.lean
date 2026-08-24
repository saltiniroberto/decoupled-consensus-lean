import Spec.Defs.Model
import Spec.Defs.Notation
import Spec.Defs.FinsetM
import Spec.Defs.Raise
import Spec.Defs.Nondet
import Spec.Defs.OldDefs
import Spec.Defs.SigningHistory
import Spec.Fig6StateTransition
import Spec.Defs.Store
import Spec.Defs.Duty
import Spec.Fig1GoldfishWalk
import Spec.Fig3AvailableConfirmation
import Spec.Fig2GoldfishDuties
import Spec.Fig4SGForkChoice
import Spec.Fig5SGDuty
import Spec.Fig7FGStore
import Spec.Defs.FinalityVote

/-!
# The specification

One import per file. **This library renders `consensus-1.pdf`** — the human-controlled
draft, kept locally at the repository root and never committed — under namespace
`Consensus1`, figure by figure from 2026-08-22. The figure files sit directly under
`Spec/`, and everything they are written in terms of sits in `Spec/Defs/`. The draft is
block-only Goldfish: one store built up in three layers, `ghost` as a named building
block, per-slot committees, block-carried Goldfish votes as the only relay channel,
timestamps on every object, and a relative-majority SG fork choice.

**The draft defines incrementally, and the old readings are figure-named.** Sections 2, 3
and 5 each redefine `get_head`, and Section 5 redefines `process_block` and
`goldfish_eligible` as well; a draft can replace a reading and Lean cannot. The last reading
of each is the protocol's and bears the plain `Store` name (`S.getHead`, `S.processBlock`,
`S.goldfishEligible`); each superseded reading is named by its figure — `Fig1.getHead`,
`Fig4.getHead`, `Fig2.processBlock`, `Fig1.goldfishEligible`. Store-taking routines sit in
`Consensus1.Store` for dot notation; everything defined once is bare (`ghost`,
`goldfishScore`); there are no namespace blocks, every definition carrying its full name at
its own `def`.

`Spec/Defs/` holds the non-figure files: `Model.lean` (Section 1's substrate and the
wire objects), `Store.lean` (Definition 1 and the fields Sections 3.2 and 5.1 add),
`SigningHistory.lean` (the signing record of the imported voting strategy — see
`FinalityVote.lean`), `Notation.lean` (the assignment macros and the raising set-builder),
`Raise.lean` (the failure vocabulary: `Error` and `DRE`), `FinsetM.lean` (monadic filter
and image over a `Finset`), `Nondet.lean` (the nondeterminism vocabulary: `NDR`, `NDRE`,
the pick), `Duty.lean` (the duty monad `NDREB` and `broadcast`), and `OldDefs.lean`
(parked definitions kept compiling; nothing may import it). The import order is dependency
order rather than figure order: Figure 6's chain state is what the store's `Σ.σ[·]` maps
into, and Figure 3's confirmation is what Figure 2's `on_tick` calls.

**Two older renderings preceded this one** — the `latex-specs` papers (namespace
`Decoupled`, with its `Analysis/` and citation apparatus) and `consensus.pdf` (namespace
`Consensus`) — and were removed on 2026-08-24, the repository narrowing to this rendering
and the PDF extractor under `extract/`. The branch `pre-consensus1-purge` holds the last
commit that carries them.
-/
