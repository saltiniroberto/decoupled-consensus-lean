import Analysis.Vocabulary
import Analysis.Proofs.Weights
import Analysis.Proofs.SlotClosure
import Analysis.Proofs.Ancestry
import Analysis.Proofs.Determinism
import Analysis.Proofs.Witnessed
import Analysis.Proofs.Certificates
import Analysis.Proofs.Freshness
import Analysis.Proofs.ChainTarget
import Analysis.Proofs.Compression
import Analysis.Proofs.Provenance
import Analysis.Proofs.Finality
import Analysis.Proofs.Irreversibility
import Analysis.Proofs.StoreInvariants
import Analysis.Proofs.StoreProvenance
import Analysis.Proofs.StoreRecords
import Analysis.Proofs.Upgrade
import Analysis.Proofs.Viability
import Analysis.Lemmas
import Analysis.Theorems
import Analysis.HftTheorems

/-!
# The analysis

One import per file under `Analysis/`. The papers' numbered results, stated and proved against
the specification in `Spec`.

Present: `Lemmas.lean` and `Theorems.lean`, the healing paper's statements of record;
`HftTheorems.lean`, the companion paper's Section 3.1 theorems, stated and not yet proved —
each is a `sorry`; `Vocabulary.lean`, the papers' definitions that no figure reads and a
statement needs; and `Proofs/`, which holds the arguments. `Corollaries.lean` is absent.

**A statement in `Lemmas.lean` is proved by a one-line call into `Proofs/`**, so that a statement
can be read against the paper without a proof between it and the reader. `Lemmas.lean` also holds
no `variable` at section level: every declaration spells out its own binders.

Read `Analysis/Lemmas.lean`'s own docstring first. It lists every lemma of Sections 2 to 4 with
what each still waits on, and explains the one distinction that decides a statement's shape: a
missing *proof* is a `sorry` in `Proofs/`, while a statement that cannot yet be *written*, because
it names something the specification does not have, is a `def … : Prop` there instead.
-/
