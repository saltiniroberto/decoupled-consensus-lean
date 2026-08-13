import Analysis.Lemmas

/-!
# The analysis

One import per file under `Analysis/`. The paper's numbered results, stated and proved against
the specification in `Spec`.

Present: `Lemmas.lean`, holding the nine lemmas of Section 3 "Deterministic finality state
machine" and Section 4 "Accountable safety" — printed numbers 3 to 11. `Theorems.lean` and
`Corollaries.lean` are absent, as is everything Section 5 onward states.

**Nothing is proved yet.** Read `Analysis/Lemmas.lean`'s own docstring first: it explains why
some lemmas are a `theorem … := sorry` and others a `def … : Prop`, which turns on whether the
paper's sentence can be written in the vocabulary the specification currently has.
-/
