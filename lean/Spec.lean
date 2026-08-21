import Spec.Defs.Basic
import Spec.Defs.Notation
import Spec.Defs.Store
import Spec.Defs.Voting
import Spec.Fig2AttestationProcessing
import Spec.Fig1SlotReplay
import Spec.HftFig2Store
import Spec.Receive
import Spec.Protocol
import Spec.Consensus.Model
import Spec.Consensus.Notation
import Spec.Consensus.FinsetM
import Spec.Consensus.Raise
import Spec.Consensus.Fig1StateTransition
import Spec.Consensus.Fig2FinalityStore
import Spec.Consensus.Goldfish
import Spec.Consensus.Fig3Schedule
import Spec.Consensus.Fig4SupportScores
import Spec.Consensus.Fig5RoundRoots
import Spec.Consensus.Fig6TimedStore
import Spec.Consensus.Validator

/-!
# The specification

One import per file under `Spec/`. **One protocol**, assembled from two papers: the chain
layer from `height_filter_healing.tex`, the store layer from the companion paper
`full/height_filter_and_timeouts.tex` — the decision is recorded in `Spec/Defs/Store.lean`
and `CONTEXT.md`.

**A figure file's name says which paper it renders.** A figure of the healing paper is
`Fig<n><Subject>`; a figure of the companion paper is `HftFig<n><Subject>` — the same
`hft` that prefixes its citation labels — with `<n>` the printed figure number in its own
paper at the pinned revision. So `Fig2AttestationProcessing` is healing's Figure 2 and
`HftFig2Store` is the companion's.

Everything the figures are written in terms of sits one level down, in `Spec/Defs/`:
`Basic.lean` holds the healing paper's numbered definitions, `Store.lean` the companion
paper's, `Voting.lean` the healing paper's voting strategy (Definitions 12 and 47–50)
wired over the hybrid's store, and `Notation.lean` the assignment macros and no protocol
content. Each says so in its own docstring.

Two files render no figure: `Receive.lean`, the message-receipt wiring — a block message
is passed to `on_block` — and `Protocol.lean`, the node as a
`Framework.StsMultisetLog.Protocol` instance.

**`Spec/Consensus/` is a second, separate rendering**: the human-controlled draft
`consensus.pdf` at the repository root, built figure by figure from 2026-08-19 under
namespace `Consensus`. It shares nothing with the files above — not the base types, not
the notation — so the rendering of record stays frozen while the draft's is written.
`Model.lean` grows on demand as its figure files consume definitions;
`Fig<n><Subject>.lean` names the draft's own figure numbering.

Five of its files render no figure, and each says so in its own header: `Model.lean`, the
draft's Section 1 vocabulary; `Notation.lean`, the assignment macros; `FinsetM.lean`, a
filter over a `Finset` that propagates a monad's effect, general Lean machinery with no
protocol content; `Raise.lean`, the failure vocabulary — one payload-free `Error` and
`ResultOrExcept` — which every routine that can fail shares; and `Goldfish.lean`,
Definition 4's raw votes and the slot committees they are cast by. `FinsetM.lean` and
`Raise.lean` were carved out of `Fig2FinalityStore.lean` on 2026-08-21, so that a figure file
states what the draft says and nothing else.

Present from the old source: healing's Figures 1 (`alg:state-replay`) and 2 (`alg:attestation-processing`),
the companion's Figure 2 (`hft:alg:store`), and the vocabulary those three need. Healing's
Figure 3 (`alg:store`) is deliberately not rendered — the store above replaces it — and
its Figures 4 (`alg:fork-choice-state`) and 5 (`alg:recovery-action`) are absent, as is
everything its Section 6 onward defines.
-/
