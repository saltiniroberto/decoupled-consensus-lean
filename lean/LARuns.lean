import LARuns.Trace
import LARuns.Environment
import LARuns.Statements.Statement4Defs
import LARuns.Statements.Statement1Defs
import LARuns.Statements.Statement2Defs
import LARuns.Statements.Statement3Defs
import LARuns.Readers
import LARuns.Bridge
import LARuns.Goldilocks.Defs
import LARuns.Statements.Statement1OnRuns
import LARuns.Statements.Statement2OnRuns
import LARuns.Statements.Statement3OnRuns
import LARuns.Statements.Statement4OnRuns
import LARuns.Statements.Statement5OnRuns
import LARuns.Statements.Statement6OnRuns
import LARuns.Statements.Statement7OnRuns
import LARuns.Goldilocks.Instance
import LARuns.Proofs
import LARuns.Goldilocks.Proofs
import LARuns.Goldilocks.Proofs567
import LARuns.Goldilocks.Bridge

/-!
# `LARuns`: the top statements over the runs of a protocol of `RStsVariant2`

`Statements/Statement1OnRuns` to `Statements/Statement4OnRuns`: the four top statements (finality
safety after healing, the confirmed tip after healing, finality liveness after healing, and the
confirmed tip through an asynchronous period), each over every run `π` of a protocol of the bare
framework whose observed run `τ` (the run with each node's local state replaced by its view) meets
the claim's extra conditions, the committees and proposer requirements read at `π`, every other
hypothesis and the conclusion on `τ`. `Statements/Statement5OnRuns` to
`Statements/Statement7OnRuns`: the three statements without healing premises (the finalized block
on the confirmed tip's chain, the finalized block only extends, and finalized blocks agree unless
there is slashable evidence), each over every run `π` whose observed run `τ`, without committees,
meets the claim's extra conditions, the conclusion on `τ`. `Goldilocks/Instance`: Goldilocks's claims in that shape, and
`Goldilocks/Defs`, what Goldilocks passes; every page specific to Goldilocks is under `Goldilocks/`.

The other pages define. Every theorem and example is on one of four proof pages: `Proofs`, the proofs
about the generic pages, `Goldilocks/Proofs`, the proofs about Goldilocks's pages,
`Goldilocks/Proofs567`, Goldilocks's claim for statement 5 proved over its runs, and
`Goldilocks/Bridge`, a run of Goldilocks's node read as observed and as a trace, premise by premise.

The defining pages: `Statement4Defs` (the healing-phase segment, the conclusions of statement 4,
the conditions every top statement takes and the readers the statements after healing share, on
the observed run), `Statement1Defs` to `Statement3Defs` (each statement's own conclusions),
`Readers` and `Bridge` (the classes `NodeViewOf` and `ProtocolCommittees`, how a node state and
a run are read, and a run read as a trace), `Trace` (the trace) and `Environment` (the readings that
Goldilocks's extra condition `RedeliveredAfterReleaseFromDelivery` reads). Every condition a statement takes is a
condition on executions of `RStsVariant2`.
-/
