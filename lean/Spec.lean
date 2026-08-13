import Spec.Defs.Basic
import Spec.Defs.Notation
import Spec.Fig2AttestationProcessing
import Spec.Fig1SlotReplay

/-!
# The specification

One import per file under `Spec/`. The paper's figures, and the numbered definitions they
read.

**`Spec/` holds the figure translations and nothing else.** A file that renders one of the
paper's five algorithm figures is named `Fig<n><Subject>`, where `<n>` is the figure's printed
number at the pinned revision of the paper. So listing `Spec/*.lean` is the list of figures
rendered so far.

Everything the figures are written in terms of sits one level down, in `Spec/Defs/`:
`Basic.lean` holds the paper's numbered definitions, and `Notation.lean` holds the assignment
macros and no protocol content. Each says so in its own docstring.

Present: Figure 1 (`alg:state-replay`) and Figure 2 (`alg:attestation-processing`), and the
vocabulary in `Spec/Defs/Basic.lean` those two need. Figure 3 (`alg:store`),
Figure 4 (`alg:fork-choice-state`) and Figure 5 (`alg:recovery-action`) are absent, as is
everything Section 6 onward defines.
-/
