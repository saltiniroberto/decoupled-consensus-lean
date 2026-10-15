import Model.Record.ChainStateRunFacts
import Model.Record.ChainStateAddedFacts
import Model.Record.ScheduleFacts
import Model.Record.StoreFacts
import Model.Record.ForkChoiceFacts
import Model.Record.ValidatorClientFacts
import Model.Record.GradesFacts
import Model.Record.HandlersFacts
import Model.Record.DutiesFacts
import Model.Record.NodeFacts
import Model.Record.EvidenceFacts

/-!
# The facts a model satisfies

`Facts M` gathers, for a model `M : Model V`, the facts about each family's routines on every input
and the facts about its runs. A proof over the record takes one hypothesis `F : Facts M` and reads
the fact it calls as a field of a field (`F.cs.…`, `F.sto.…`).
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The facts a model satisfies: for each family, its facts on every input and its facts about runs,
    one field each. -/
structure Facts (M : Model V) : Prop where
  /-- The chain state's facts on every input, over `M`'s chain-state part. -/
  cs : ChainStateFacts M.toChainStateModel
  /-- The chain state's facts about runs, over `M`'s own runs. -/
  csRun : ChainStateRunFacts M
  /-- The chain state's further facts on every input, beyond `ChainStateFacts`. -/
  csAdded : ChainStateAddedFacts M
  /-- The chain state's further facts about runs, beyond `ChainStateRunFacts`. -/
  csAddedRun : ChainStateAddedRunFacts M
  /-- The schedule's facts on every input. -/
  sch : ScheduleFacts M
  /-- The schedule's facts about runs. -/
  schRun : ScheduleRunFacts M
  /-- The store's facts on every input. -/
  sto : StoreFacts M
  /-- The store's facts about runs. -/
  stoRun : StoreRunFacts M
  /-- The fork choice's facts on every input. -/
  fc : ForkChoiceFacts M
  /-- The fork choice's facts about runs. -/
  fcRun : ForkChoiceRunFacts M
  /-- The validator client's facts on every input. -/
  vc : ValidatorClientFacts M
  /-- The validator client's facts about runs. -/
  vcRun : ValidatorClientRunFacts M
  /-- The grades' facts on every input. -/
  gr : GradesFacts M
  /-- The grades' facts about runs. -/
  grRun : GradesRunFacts M
  /-- The handlers' facts on every input. -/
  hd : HandlersFacts M
  /-- The handlers' facts about runs. -/
  hdRun : HandlersRunFacts M
  /-- The facts of the duties and the tick on every input. -/
  dt : DutiesFacts M
  /-- The facts about runs of the duties and the tick. -/
  dtRun : DutiesRunFacts M
  /-- The node's facts on every input. -/
  nd : NodeFacts M
  /-- The node's facts about runs. -/
  ndRun : NodeRunFacts M
  /-- The evidence's facts on every input. -/
  ev : EvidenceFacts M
  /-- The evidence's facts about runs. -/
  evRun : EvidenceRunFacts M

/-! ## The node state a validator's tick stage reads -/

section WakeStage

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

variable {M : Model V}

/-- The node state `wakeStage` gives has the store of the node state before the step. -/
theorem wakeStage_st (facts : Facts M) (Sched : Schedule V) (t : Int)
    (c : Config V (NamedObject V) M.N) (v : V) :
    (wakeStage M Sched t c v).st = c[v].st.st := by
  unfold wakeStage; split
  · exact (facts.nd.wake_st_record _).1
  · rfl

/-- The node state `wakeStage` gives has the signing record of the node state before the step. -/
theorem wakeStage_record (facts : Facts M) (Sched : Schedule V) (t : Int)
    (c : Config V (NamedObject V) M.N) (v : V) :
    (wakeStage M Sched t c v).record = c[v].st.record := by
  unfold wakeStage; split
  · exact (facts.nd.wake_st_record _).2
  · rfl

/-- The node state `wakeStage` gives has the grade cache of the node state before the step. -/
theorem wakeStage_cache (facts : Facts M) (Sched : Schedule V) (t : Int)
    (c : Config V (NamedObject V) M.N) (v : V) :
    (wakeStage M Sched t c v).cache = c[v].st.cache := by
  unfold wakeStage; split
  · exact facts.nd.wake_cache _
  · rfl


/-- In every configuration `k` of an atomic execution `x`, every validator's node state satisfies
    `M.reachedNode`. -/
theorem reachedNode_sts (facts : Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocolOf M S) Sched) (k : Nat) (v : V) : M.reachedNode (x[k][v].st) :=
  inv_sts M S Sched x M.reachedNode (fun v => facts.nd.reachedNode_initial _ v)
    (fun n h => facts.nd.reachedNode_wake n h)
    (fun v n t out h hn => facts.nd.reachedNode_tick _ v n t out h hn)
    (fun n o n' h hn => facts.nd.reachedNode_process _ n o n' h hn) k v

/-- At a `tickAllAwake t` step from configuration `k`, the node state `v`'s tick stage reads is a
    reached node state. -/
theorem reachedNode_wakeStage (facts : Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocolOf M S) Sched) (k : Nat) (v : V) (t : Int) :
    M.reachedNode (wakeStage M Sched t x[k] v) := by
  unfold wakeStage; split
  · exact facts.nd.reachedNode_wake _ (reachedNode_sts facts S Sched x k v)
  · exact reachedNode_sts facts S Sched x k v

/-- In every configuration `k` of an atomic execution `x`, validator `v`'s node state runs as `v`. -/
theorem runs_as_sts (facts : Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocolOf M S) Sched) (k : Nat) (v : V) : M.runs_as (x[k][v].st) v := by
  obtain ⟨w, hw, heq⟩ := stateBeforeOf_runOfM M S Sched x facts.nd.wake_events_or_id v k
  rw [← heq]
  exact facts.ndRun.stateBeforeOf_runs_as (Setup.alwaysAwake S) _ _ w hw v

/-- At a `tickAllAwake t` step from configuration `k`, the node state `v`'s tick stage reads runs as
    `v`. -/
theorem runs_as_wakeStage (facts : Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocolOf M S) Sched) (k : Nat) (v : V) (t : Int) :
    M.runs_as (wakeStage M Sched t x[k] v) v := by
  unfold wakeStage; split
  · exact facts.nd.runs_as_wake _ v (runs_as_sts facts S Sched x k v)
  · exact runs_as_sts facts S Sched x k v

end WakeStage

section RunWorlds

open DecoupledConsensusModel.Execution
open scoped DC

variable {M : Model V}

/-- If every validator's node state in the world `w₁` is a reached node state, then so is every
    validator's node state in every world that folding `worldStepOf` over the events `es` from `w₁`
    can reach. -/
theorem reachedNode_foldlM_worldStepOf (facts : Facts M) (S : Setup V)
    (es : List (Record.Event V)) (w₁ : V → M.N) (h₁ : ∀ v, M.reachedNode (w₁ v)) :
    ∀ w₂ ∈ es.foldlM (worldStepOf M S) w₁, ∀ v, M.reachedNode (w₂ v) := by
  induction es generalizing w₁ with
  | nil =>
    intro w₂ hw v
    have hw' : w₂ = w₁ := hw
    subst hw'
    exact h₁ v
  | cons e es ih =>
    intro w₂ hw v
    rw [List.foldlM_cons, Set.bind_def] at hw
    obtain ⟨w', hw', hw₂⟩ := Set.mem_iUnion₂.mp hw
    refine ih w' ?_ w₂ hw₂ v
    cases e with
    | wake p t =>
      simp only [worldStepOf, Set.mem_singleton_iff] at hw'
      subst hw'
      intro u
      by_cases hu : u = p
      · subst hu
        rw [Function.update_self]
        exact facts.nd.reachedNode_wake _ (h₁ u)
      · rw [Function.update_of_ne hu]
        exact h₁ u
    | tick p t =>
      simp only [worldStepOf, Set.mem_setOf_eq] at hw'
      rcases hw' with ⟨out, hout, rfl⟩ | ⟨-, rfl⟩
      · intro u
        by_cases hu : u = p
        · subst hu
          rw [Function.update_self]
          exact facts.nd.reachedNode_tick S u (w₁ u) t out hout (h₁ u)
        · rw [Function.update_of_ne hu]
          exact h₁ u
      · exact h₁
    | deliver p o t =>
      simp only [worldStepOf, Set.mem_setOf_eq] at hw'
      rcases hw' with ⟨n', hn', rfl⟩ | ⟨-, rfl⟩
      · intro u
        by_cases hu : u = p
        · subst hu
          rw [Function.update_self]
          exact facts.nd.reachedNode_process S (w₁ u) o n' hn' (h₁ u)
        · rw [Function.update_of_ne hu]
          exact h₁ u
      · exact h₁

/-- For every world `w` that the events of `rho` timed before `t` lead to from the world of initial
    node states, every validator's node state in `w` is a reached node state. -/
theorem reachedNode_stateBeforeTime (facts : Facts M) (S : Setup V) (rho : Record.Run V)
    (t : DecoupledConsensusModel.Time) :
    ∀ w ∈ (rho.events.filter (fun e => decide (e.time < t))).foldlM (worldStepOf M S)
        (fun v => M.initial S v), ∀ v, M.reachedNode (w v) :=
  reachedNode_foldlM_worldStepOf facts S _ _ (fun v => facts.nd.reachedNode_initial S v)

end RunWorlds

end DecoupledConsensusModel.Sts.Record
