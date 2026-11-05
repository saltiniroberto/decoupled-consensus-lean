module
public import GoldilocksCorrectness.Record.Wiring
public import GoldilocksCorrectness.Statements.Executions.WiringDefs
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.RunFactsDefs
public import GoldilocksCorrectness.Statements.AbstractTrace.DeliveryDefs
public import GoldilocksCorrectness.Statements.Executions.UnforgeabilityDefs

@[expose] public section

/-!
# WiringDefs, over a model

The recovery lines of `GoldilocksCorrectness/Statements/Executions/WiringDefs.lean`. The page's
node, its reactions and its reading lemmas are restated over a model on `Record/Wiring.lean`
(`protocolOf`, `reactionsOf`, `mem_reactionsOf_tick_iff`, `reactionsOf_tick_eq_empty_iff`,
`step_tick_iff`, `step_recv_iff`, `step_wake_iff`); each landed reading lemma is recovered here from
that page's form at the spec's model. The deterministic reaction `reaction`, `step_iff_eq_reaction`
and `DREBOutcomesOk.of_run_ok` read the spec's tick through its run, which the record has no member
for, and have no twin.
-/

