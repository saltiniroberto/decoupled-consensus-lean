# decoupled-consensus-lean

A Lean 4 specification of **Ethereum decoupled consensus**, and machine-checked proofs of its
safety and liveness properties after healing.

## The spec

The specification is the library `Spec`, under [`lean/Spec/`](lean/Spec/). It is one node of the
protocol, written as definitions only: its types (blocks, Goldfish votes, attestations with their
height pairs and finality pairs, chain states), its parameters, its store and the routines that
read and update it, and the node's tick. The routines are written to read like a paper's
pseudocode, and every definition carries a docstring that says what it means.

- [`lean/Spec/doc/README.md`](lean/Spec/doc/README.md): what the library holds, file by file.
- [`lean/Spec/doc/STYLE.md`](lean/Spec/doc/STYLE.md): the style the spec is written in, and its
  notation.
- [`lean/Spec/doc/DEPENDENCIES.md`](lean/Spec/doc/DEPENDENCIES.md): what each file imports.
- [`lean/Spec/doc/PROVING.md`](lean/Spec/doc/PROVING.md): how the spec is proved.

## The layout

The five libraries of [`lakefile.toml`](lakefile.toml), all with `srcDir = "lean"`:

| library | folder | what it holds |
| --- | --- | --- |
| `Spec` | `lean/Spec/`, `lean/Spec.lean` | the specification; no theorem |
| `Sts` | `lean/Sts.lean` | the spec's node placed under the transition-system framework's `Protocol` |
| `Model` | `lean/Model/` | the definitions the proofs are stated against: the vocabulary model (a second model of the protocol, which the claims were first proved over), the record `Model V` that a protocol model supplies and the facts it must prove, the conditions the claims are stated with |
| `Proofs` | `lean/Proofs/` | every proof but the end results: the proofs about the vocabulary model, the claims restated over the record, and the spec's instance of the record |
| `EndResults` | `lean/EndResults.lean`, `lean/EndResults/` | the end results: the claims' top-level theorems applied to the spec's instance of the record |

[`deps/lean-sts`](https://github.com/saltiniroberto/lean-sts) is the transition-system framework,
a git submodule. It handles what is not the protocol: delivery, who is asleep, who is corrupt.
[`extract/`](extract/README.md) renders the spec into a paper-shaped PDF (`make extract`).

## The end results

The library `EndResults` states nine theorems for the spec itself, in the Lean namespace
`EndResults`. Each applies a theorem proved over an arbitrary model of the record to the spec's
model `Model.spec` and its facts `Model.spec_facts`
(`lean/Proofs/Instance/Facts/Assembly.lean`). The file
[`lean/EndResults.lean`](lean/EndResults.lean) holds `EndResults.constants_holds` and, for each of
the other eight, its explicit form `…_holds_explicit`, which states the claim over every phase at
least as long as the healing length its proof picks, written out, with every hypothesis before the
colon:

| theorem | what it says |
| --- | --- |
| `EndResults.constants_holds` | the protocol's constants (the round period, the participation lag and window, the growth delay) are well formed |
| `EndResults.claim13bf_holds_explicit` | after healing, the finalized blocks of any two honest validators, at any two steps of an execution, are compatible |
| `EndResults.claimConfirmedAfterHealing_holds_explicit` | from one round after the healing phase's end, Goldfish confirmation agrees across honest active readers and only extends at each |
| `EndResults.claimConfirmedIncludedAfterHealing_holds_explicit` | after healing, a proposer honest through its slot's vote instant and awake before its proposal proposes a block, and that block enters the confirmed output of every honest active reader |
| `EndResults.claimConfirmedGrowsAfterHealing_holds_explicit` | after healing, if honest awake proposers recur, the confirmed output keeps growing |
| `EndResults.claimStableLiveAfterHealing_holds_explicit` | the same inclusion and growth for the stable output |
| `EndResults.claimFinalityLiveAfterHealing_holds_explicit` | after healing, finality includes every honest proposal within a deadline and keeps growing, for as long as the premises continue |
| `EndResults.claimStableThroughOneAsyncPeriod_holds_explicit` | the stable output survives one asynchronous period after healing |
| `EndResults.claimStableThroughOneAsyncPeriodCommonViewAgain_holds_explicit` | the same, with the common view of finalized descendants asked again after the asynchronous period |

The file [`lean/EndResults/ExistentialForms.lean`](lean/EndResults/ExistentialForms.lean)
holds, for each of the eight, the form `…_holds`, which states that there is a healing length
`tHeal`, and after it its per-execution form `…_holds_perExecution`, where the execution `x` and
its hypotheses come before the colon, so that `tHeal` is chosen for each execution.

Each theorem's statement gives its full hypotheses. Every one of them depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`.

All nine assume nothing beyond their statements' own premises. None of them assumes that
validators wake only at a round's action instant or fall asleep only right after one: the spec's
wake rule lets a validator perform a duty of a round only if it has been awake, without
interruption, since one delay before the first cutoff of the grade results that duty reads. The
spec's node placed under the transition-system framework (`lean/Sts.lean`) runs the node's tick at
every reading of the validator's clock.
[`lean/Spec/doc/PROVING.md`](lean/Spec/doc/PROVING.md) says how they are proved.

## Building

    make            # list the available targets
    make cache      # fetch prebuilt Mathlib artefacts -- do this before a first build
    make check      # the native_decide and sorry checks, then build Spec and Sts
    make proofs     # build all five libraries, capped (see below)
    make extract    # render the spec into a paper-shaped PDF (extract/out/dc.pdf)

`lake build` builds the default targets, `Spec` and `Sts`. The proofs are large: a full build of
the five libraries compiles about 1,600 modules, and one compile can take 3.5 GB of memory. Lake
runs as many compiles at once as there are cores, which can exhaust the memory of a laptop, so
`make proofs` runs

    LEAN_NUM_THREADS=2 nice -n 10 lake build Spec Sts Model Proofs EndResults

which kept the build at two compiles at a time. Measured on a 12-core machine with 32 GB free, it
took about 40 minutes, with Mathlib already fetched by `make cache`.

The toolchain is pinned in [`lean-toolchain`](lean-toolchain) (Lean 4.32.2); Mathlib's rev in
`lakefile.toml` and the rev the `deps/lean-sts` submodule requires must match it. Clone with
`--recurse-submodules`, or run `git submodule update --init` after cloning.

## License

See [`LICENSE`](LICENSE).
