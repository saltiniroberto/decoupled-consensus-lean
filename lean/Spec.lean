import Spec.Defs.Basic
import Spec.Defs.Notation
import Spec.Fig2AttestationProcessing
import Spec.Fig1SlotReplay
import Spec.Timeouts.Defs
import Spec.Timeouts.Fig2Store
import Spec.Timeouts.Receive

/-!
# The specification

One import per file under `Spec/`. The papers' figures, and the numbered definitions they
read.

**`Spec/` holds the figure translations and nothing else.** A file that renders one of the
healing paper's five algorithm figures is named `Fig<n><Subject>`, where `<n>` is the
figure's printed number at the pinned revision of the paper.

Everything the figures are written in terms of sits one level down, in `Spec/Defs/`:
`Basic.lean` holds the paper's numbered definitions, and `Notation.lean` holds the
assignment macros and no protocol content. Each says so in its own docstring.

**`Spec/Timeouts/` is the store layer**, and its contract is the companion paper
`full/height_filter_and_timeouts.tex` — cited with `hft:`-prefixed labels — rather than the
healing paper; `Spec/Timeouts/Defs.lean` records the decision. The same naming convention
applies inside it with that paper's figure numbers: `Fig2Store` renders its Figure 2
(`hft:alg:store`), `Defs` the numbered definitions that figure reads, and `Receive` the
message-receipt wiring, which renders no figure.

Present from the healing paper: Figure 1 (`alg:state-replay`) and Figure 2
(`alg:attestation-processing`), and the vocabulary in `Spec/Defs/Basic.lean` those two
need. Its Figure 3 (`alg:store`), Figure 4 (`alg:fork-choice-state`) and Figure 5
(`alg:recovery-action`) are absent — the store layer deliberately so, in favour of
`Spec/Timeouts/` — as is everything Section 6 onward defines.
-/
