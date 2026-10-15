# `lean/Model/`: the definitions the proofs are stated against

The library `Model` of `lakefile.toml` (`srcDir = "lean"`, module root `Model`), so the module
`Model.Record.Facts` is the file `lean/Model/Record/Facts.lean`. Every definition the proofs are
stated against is here, and every proof is under `lean/Proofs/` except the end results, the
library `EndResults` (`lean/EndResults.lean` and `lean/EndResults/`); the protocol itself is the
library `Spec`, under `lean/Spec/`. A file is placed by what it mostly is, and files are not
split, so many pages here import pages of `Proofs` (some proof pages declare definitions that
statements use); Lake resolves the modules across the two libraries.

- `Vocabulary/`: the vocabulary model, a second model of the protocol (objects, protocol,
  execution) that the claims were first proved over, and under `Vocabulary/Statements/` its
  statement library.
- `Record/`: the record. `Record/Model.lean` defines `Record.Model` (what a protocol model
  supplies), `Record/Facts.lean` defines `Record.Facts` (what such a model must prove), the
  `*Facts.lean` pages its facts bundles, `Record/Wiring.lean` the record's node under the sts
  framework, and `ChainState*.lean` the chain-state part of the record.
- `Conditions/`: the definitions the restated claims are stated with.
- `Sts/` and `Sts.lean`: the vocabulary model placed under the sts framework's `Protocol`, and the
  part of its statement layer over the framework's executions that the end results use (interface,
  constants, conditions, and the claim definitions typed over the vocabulary model under
  `Sts/Spec2Claims/`).

The pages hold only the declarations the end results reach. The Lean namespaces do not follow the
folders: they are `DecoupledConsensusModel` and namespaces under it such as
`DecoupledConsensusModel.Sts` and `DecoupledConsensusModel.Sts.Record`.

Build: `lake build Model` (not a default target).
