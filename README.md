# Goldilocks on per-node clocks and real time: statements on runs (draft)

**Draft.** Work in progress, published as it stands for discussion. Statements and proofs may still
change, and some of the statements below are stated but not yet proved.

This branch carries one line of work of the
[decoupled-consensus-lean](https://github.com/saltiniroberto/decoupled-consensus-lean) project, taken
out of a larger development: the Goldilocks consensus protocol's correctness proved on a model in
which every node has its own clock, clocks drift within known bounds, and time is real-valued, plus
protocol-agnostic statements on the runs of a protocol and Goldilocks's claims that its runs meet them.

## What is here

| folder | library | what it is |
| --- | --- | --- |
| `lean/RStsVariant2/` | `RStsVariant2` | The execution framework. A configuration carries no time; an execution gives each configuration the real time it is entered. Each node's clock is moved only by an environment step of its own (`setClock`), every other node event runs the protocol at the stored clock value, and the conditions on executions (clock skew, delivery, catch-up after a restart, committee sleepiness) are predicates a statement takes as hypotheses. |
| `lean/Goldilocks/` | `Goldilocks` | The Goldilocks protocol's specification. |
| `lean/GoldilocksCorrectness/` | `GoldilocksCorrectness` | The correctness development: a model `M` of the protocol with the facts it satisfies, abstract traces with an activity and per-node clocks, and the statements proved on them (finality safety after healing, the confirmed tip after healing, finality liveness after healing, resilience to a period of asynchrony). |
| `lean/GoldilocksVariant/` | `GoldilocksVariant` | Goldilocks's node as a protocol of `RStsVariant2`, and the instance of the abstract-trace layer on its runs (the projection of a run to a trace, and the run facts and environment facts read back). |
| `lean/LARuns/Statements/` | `LARuns` | Seven statements on the runs of any protocol of `RStsVariant2`, seen only through its nodes' views and the messages on the wire. |
| `lean/LARuns/Goldilocks/` | `LARuns` | Goldilocks's claims that its runs satisfy those statements, and the bridges from the abstract-trace results. |
| `lean/GoldilocksSts.lean`, `lean/StsRefinement/`, `lean/Spec2/Defs/` | `GoldilocksSts`, `StsRefinement`, `Spec2` | Definitions the above import. |
| `deps/lean-sts` | (submodule) | The protocol-independent [sts framework](https://github.com/saltiniroberto/lean-sts). |

## Where the results are

- The statements on runs: `lean/LARuns/Statements/Statement1OnRuns.lean` to
  `Statement7OnRuns.lean` (finalized blocks compatible after healing; the confirmed tip after healing;
  finality liveness after healing; resilience of a proposed block to a period of asynchrony; finalized
  blocks on the confirmed chain; finality only extends; finalized blocks compatible unless slashable).
- Goldilocks's claims: `lean/LARuns/Goldilocks/Instance.lean`. Statements 5, 6 and 7 are
  proved for Goldilocks (`lean/LARuns/Goldilocks/Proofs567.lean`); statements 1 to 4 are
  stated, and their proofs are in progress (the bridges are in `Bridge.lean`).
- The abstract-trace statements, all proved: `lean/GoldilocksCorrectness/Record/Restated/Statements/Executions/`
  (`HealedTopStatements.lean`, `HealedFinalityLivenessStatements.lean`, `AsyncResilienceStatements.lean`).

No `sorry`, no `axiom` beyond Lean's and Mathlib's standard ones, no `native_decide`.

## Building

    git submodule update --init deps/lean-sts
    lake exe cache get
    lake build

Lean 4.32.2 and Mathlib `v4.32.2` (pinned in `lean-toolchain` and `lakefile.toml`).
