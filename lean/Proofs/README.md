# `lean/Proofs/`: every proof

The library `Proofs` of `lakefile.toml` (`srcDir = "lean"`, module root `Proofs`), so the module
`Proofs.Instance.Model` is the file `lean/Proofs/Instance/Model.lean`. Every proof is here, whoever
wrote it; the definitions they are stated against are under `lean/Model/`. `lean/Spec/doc/PROVING.md`
explains how the pieces fit.

- `Vocabulary/`: the proofs about the vocabulary model of `lean/Model/Vocabulary/`; its internal
  library under `Vocabulary/Internal/`; and the vocabulary model as an instance of the record:
  `ModelVocabulary.lean`, `ModelVocabularyFacts.lean` (`Model.vocabulary_facts_*`) and
  `ChainStateVocabulary.lean`.
- `Claims/`: the claims. `Claims/Restated/` restates every theorem the end results need over an
  arbitrary `M : Record.Model V` with `facts : Record.Facts M`; its nine top-level theorems are the
  `…_holds` theorems (`constants_holds`, `claim13bf_holds`, `claimConfirmedAfterHealing_holds`,
  ...). `Claims/Spec2Claims/` holds the proofs typed over the vocabulary model that those restated
  pages and the vocabulary model's instance still use. The pages directly under `Claims/` (`ProcessedFlip.lean`, `RunAll.lean`,
  `ModelIrreducible.lean`, ...) are shared by both.
- `Instance/`: the spec's instance of the record: `Model.spec` (the record's members at the
  spec under `lean/Spec/`) and `Model.spec_facts : Facts Model.spec`
  (`Instance/Facts/Assembly.lean`). Many of its fields are transported from the vocabulary model's
  facts through theorems that a spec routine equals the vocabulary model's routine
  (`Instance/Equalities/`), which is why `Vocabulary/` is still needed.

The end results are not here: they are the library `EndResults`, which applies the nine `…_holds`
to `Model.spec_facts`. Its file `lean/EndResults.lean` holds `constants_holds` and the explicit
forms `…_holds_explicit`, and `lean/EndResults/ExistentialForms.lean` the forms `…_holds` and
`…_holds_perExecution`.

The pages hold only the declarations the end results reach. The Lean namespaces do not follow the
folders: they are `DecoupledConsensusModel` and others, namespaces such as
`DecoupledConsensusModel.Sts.Restated` for the claims, and `SpecRecord` and `Spec` for the
spec's instance.

Build: `lake build Proofs` (not a default target).
