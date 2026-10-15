import Model.Record.Wiring

/-!
# The converse awake facts of the node routines

`NodeWakeFacts` holds two facts a model `M` provides about executions of its node routines: when an
honest validator, awake at the time `τ` of a tick step, has a node state that passes round `r`'s
grade-2 (or grade-1) awake test, the validator has been awake at every time from that round's
grade-2 (or grade-1) window start to `τ`. They are the converses of the fields `run_fact_g2_at` and
`run_fact_g1_at` of `NodeRunFacts` (`lean/Model/Record/NodeFacts.lean`).

The structure is the field `ndWake` of `Facts` (`lean/Model/Record/Facts.lean`); it is proved at the
spec's model as `Model.spec_wakeFacts` (`lean/Proofs/Instance/Facts/Assembly.lean`).
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

open DecoupledConsensusModel.Execution
open scoped DC

/-- The facts that read a node state's awake test back as a fact about the schedule: a validator
    whose node state passes round `r`'s awake test at a tick has been awake throughout the window the
    test names. -/
structure NodeWakeFacts (M : Model V) : Prop where
  /-- At a tick step `k` at time `τ`, if a validator not held by the adversary at any time up to `τ`
      and awake at `τ` has a node state, as its tick at `τ` reads it, that passes the grade-2 awake
      test of round `r`, then the validator was awake at every time from round `r`'s grade-2 window
      start to `τ`. The window start must be at or after time `0`, which excludes round `0`. -/
  run_fact_g2_sound_at : ∀ (S : Setup V) (Sched : Framework.StsMultisetLog.Schedule V)
      (x : Framework.StsMultisetLog.AtomicExec (protocolOf M S) Sched) (k τ : Nat) (r : Round) (v : V),
    x.lbl k = Framework.StsMultisetLog.AtomicAction.tickAllAwake τ →
    0 ≤ M.early S.E S.hc r .g2 - S.E.Δ →
    (∀ t' ≤ (τ : Int), v ∉ Sched.adv t') →
    v ∈ Sched.awake (τ : Int) →
    M.awake_for_grade2 (Setup.alwaysAwake S) v (wakeStage M Sched (τ : Int) x[k] v) r →
    v ∈ Sched.awakeThroughout (M.early S.E S.hc r .g2 - S.E.Δ) (τ : Int)
  /-- At a tick step `k` at time `τ`, if a validator not held by the adversary at any time up to `τ`
      and awake at `τ` has a node state, as its tick at `τ` reads it, that passes the grade-1 awake
      test of round `r`, then the validator was awake at every time from round `r`'s grade-1 window
      start to `τ`. The window start must be at or after time `0`. -/
  run_fact_g1_sound_at : ∀ (S : Setup V) (Sched : Framework.StsMultisetLog.Schedule V)
      (x : Framework.StsMultisetLog.AtomicExec (protocolOf M S) Sched) (k τ : Nat) (r : Round) (v : V),
    x.lbl k = Framework.StsMultisetLog.AtomicAction.tickAllAwake τ →
    0 ≤ M.early S.E S.hc r .g1 - S.E.Δ →
    (∀ t' ≤ (τ : Int), v ∉ Sched.adv t') →
    v ∈ Sched.awake (τ : Int) →
    M.awake_for_grade1 (Setup.alwaysAwake S) v (wakeStage M Sched (τ : Int) x[k] v) r →
    v ∈ Sched.awakeThroughout (M.early S.E S.hc r .g1 - S.E.Δ) (τ : Int)

end DecoupledConsensusModel.Sts.Record
