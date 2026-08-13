import Spec.Basic
import Spec.Pseudocode
import Spec.Fig2AttestationProcessing
import Spec.Fig1SlotReplay

/-!
# The specification

One import per file under `Spec/`. The paper's figures, and the numbered
definitions they read.

A file that renders one of the paper's five algorithm figures is named `Fig<n><Subject>`,
where `<n>` is the figure's printed number at the pinned revision of the paper. A file that
renders no figure carries no such prefix: `Basic.lean` holds numbered definitions and
`Pseudocode.lean` holds notation, and each says so in its own docstring.

Present: Figure 1 (`alg:state-replay`) and Figure 2 (`alg:attestation-processing`), and the
vocabulary in `Basic.lean` those two need. Figure 3 (`alg:store`),
Figure 4 (`alg:fork-choice-state`) and Figure 5 (`alg:recovery-action`) are absent, as is
everything Section 6 onward defines.
-/
