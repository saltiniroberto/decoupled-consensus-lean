import Analysis.Vocabulary
import Analysis.Proofs.Weights
import Analysis.Proofs.SlotClosure
import Analysis.Proofs.Ancestry
import Analysis.Proofs.Witnessed
import Analysis.Proofs.Certificates
import Analysis.Proofs.Freshness
import Analysis.Lemmas

/-!
# The analysis

One import per file under `Analysis/`. The paper's numbered results, stated and proved against
the specification in `Spec`.

Present: `Lemmas.lean`, the statements of record; `Vocabulary.lean`, the paper's definitions that
no figure reads and a statement needs; and `Proofs/`, which holds the arguments.
`Theorems.lean` and `Corollaries.lean` are absent.

**A statement in `Lemmas.lean` is proved by a one-line call into `Proofs/`**, so that a statement
can be read against the paper without a proof between it and the reader. `Lemmas.lean` also holds
no `variable` at section level: every declaration spells out its own binders.

Read `Analysis/Lemmas.lean`'s own docstring first. It lists every lemma of Sections 2 to 4 with
what each still waits on, and explains the one distinction that decides a statement's shape: a
missing *proof* is a `sorry` in `Proofs/`, while a statement that cannot yet be *written*, because
it names something the specification does not have, is a `def … : Prop` there instead.
-/
