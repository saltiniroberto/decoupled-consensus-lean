import Proofs.Vocabulary.Internal.ModelVocabulary.Execution.NamedRun
import Proofs.Vocabulary.Execution.Runtime
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Record.Wiring
import Proofs.Vocabulary.ModelVocabularyFacts

/-!
# Run reads and emissions

The worlds a run can reach, the objects a tick can send, one path of a run, and the emission and
processing relations read along a path, over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Execution.NamedRun

/-- The set of worlds that can hold after all the events of `rho`, starting from the world where
    every validator `v` holds `M.initial S v`. -/
def Vocabulary.Execution.NamedRun.final (M : Record.Model V) (S : Setup V) (rho : Record.Run V) :
    DC.NDR (V → M.N) :=
  rho.events.foldlM (Record.worldStepOf M S) (fun v => M.initial S v)

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Execution.NamedRun

/-- The set of the lists of objects `v`'s tick at `t` can send, from `v`'s node state in any world
    that can hold before the `i`-th event of `rho`. -/
def Vocabulary.Execution.NamedRun.emittedAt (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (i : Nat) (v : V) (t : Time) :
    DC.NDR (List (NamedObject V)) :=
  { l | ∃ w ∈ Record.stateBeforeOf M S rho i, ∃ out : M.N × List (NamedObject V),
      M.tick S v (w v) t ⇢ out ∧ l = out.2 }

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Execution.NamedRun

/-- `W` is one path of the run `rho`: for every `i`, `W i` is a world that can hold before the
    `i`-th event, and `W (i + 1)` is a world that event can lead to from `W i` (`W i` itself when
    `rho` has no `i`-th event). -/
def Vocabulary.Execution.NamedRun.OnePath (M : Record.Model V) (S : Setup V) (rho : Record.Run V)
    (W : Nat → V → M.N) : Prop :=
  ∀ i : Nat, W i ∈ Record.stateBeforeOf M S rho i ∧
    W (i + 1) ∈ ((rho.events.drop i).take (i + 1 - i)).foldlM (Record.worldStepOf M S) (W i)

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Execution.NamedRun

/-- Some event `i` of `rho` is `v`'s tick at `t`, and some outcome of that tick from `v`'s node
    state in `W i` has `v`'s node state in `W (i + 1)` as its node state and sends `o`. -/
def Vocabulary.Execution.NamedRun.emitsAlong (M : Record.Model V) (S : Setup V) (rho : Record.Run V)
    (W : Nat → V → M.N) (v : V) (o : NamedObject V) (t : Time) : Prop :=
  ∃ i : Nat, rho.events[i]? = some (.tick v t) ∧
    ∃ out : M.N × List (NamedObject V), M.tick S v (W i v) t ⇢ out ∧ W (i + 1) v = out.1 ∧
      o ∈ out.2

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Execution.NamedRun

/-- `v`'s tick at `t` sends `o` along the path `W` of `rho`; it is `emitsAlong`. -/
def Vocabulary.Execution.NamedRun.emits (M : Record.Model V) (S : Setup V) (rho : Record.Run V)
    (W : Nat → V → M.N) (v : V) (o : NamedObject V) (t : Time) : Prop :=
  Restated.Vocabulary.Execution.NamedRun.emitsAlong M S rho W v o t

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Execution.NamedRun

/-- Along the path `W` of `rho`, `v`'s tick at `t` sends `o`, or some event of `rho` is the delivery
    of `o` to `v` at `t`. -/
def Vocabulary.Execution.NamedRun.processes (M : Record.Model V) (S : Setup V) (rho : Record.Run V)
    (W : Nat → V → M.N) (v : V) (o : NamedObject V) (t : Time) : Prop :=
  Restated.Vocabulary.Execution.NamedRun.emitsAlong M S rho W v o t ∨
    ∃ i : Nat, rho.events[i]? = some (.deliver v o t)

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Execution.NamedRun

/-- The `i`-th event of `rho` is a tick of `v` at some `t` and `o` is in every list of objects that
    tick can send, or it is a delivery of `o` to `v`. -/
def Vocabulary.Execution.NamedRun.processesAtIndex (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (i : Nat) (v : V)
    (o : NamedObject V) : Prop :=
  (∃ t : Time, rho.events[i]? = some (.tick v t) ∧
      ∀ l ∈ Restated.Vocabulary.Execution.NamedRun.emittedAt M S rho i v t, o ∈ l) ∨
    ∃ t : Time, rho.events[i]? = some (.deliver v o t)

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Execution.NamedRun

/-- At the model `Record.Model.vocabulary`, `Restated.Vocabulary.Execution.NamedRun.final` is the
    singleton of `DecoupledConsensusModel.Execution.NamedRun.final`. -/
@[record_vocabulary]
theorem Vocabulary.Execution.NamedRun.final_vocabulary_eq (S : Setup V) (rho : NamedRun V) :
    Restated.Vocabulary.Execution.NamedRun.final (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) =
      {_root_.DecoupledConsensusModel.Execution.NamedRun.final (V := V) S rho} :=
  Record.foldlM_worldStepOf_vocabulary S rho.events NamedWorld.init

/-- At the model `Record.Model.vocabulary`, `Restated.Vocabulary.Execution.NamedRun.emittedAt` is the
    singleton of `DecoupledConsensusModel.Execution.NamedRun.emittedAt`. -/
@[record_vocabulary]
theorem Vocabulary.Execution.NamedRun.emittedAt_vocabulary_eq (S : Setup V) (rho : NamedRun V) (i : Nat) (v : V) (t : Time) :
    Restated.Vocabulary.Execution.NamedRun.emittedAt (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) i v t =
      {_root_.DecoupledConsensusModel.Execution.NamedRun.emittedAt (V := V) S rho i v t} := by
  ext l
  have hr : ∀ out, Record.Model.vocabulary.tick S v (NamedRun.stateBefore S rho i v) t ⇢ out ↔
      out = NamedNode.tick S v (NamedRun.stateBefore S rho i v) t :=
    fun out => Record.returns_pure _ out
  constructor
  · rintro ⟨w, hw, out, hout, rfl⟩
    rw [Record.stateBeforeOf_vocabulary] at hw
    cases hw
    rw [(hr out).1 hout]
    rfl
  · intro hl
    cases hl
    refine ⟨NamedRun.stateBefore S rho i, ?_, _, (hr _).2 rfl, rfl⟩
    rw [Record.stateBeforeOf_vocabulary]
    rfl

/-- `DecoupledConsensusModel.Execution.NamedRun.emits` holds exactly when
    `Restated.Vocabulary.Execution.NamedRun.emitsAlong` holds at the model `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Execution.NamedRun.emitsAlong_vocabulary_eq (S : Setup V) (rho : NamedRun V) (v : V) (o : NamedObject V) (t : Time) :
    _root_.DecoupledConsensusModel.Execution.NamedRun.emits (V := V) S rho v o t ↔
      Restated.Vocabulary.Execution.NamedRun.emitsAlong (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun i => NamedRun.stateBefore S rho i) v o t := by
  refine exists_congr fun i => ⟨fun ⟨hi, ho⟩ =>
      ⟨(Record.Event.map_ofVocabulary_getElem?_tick _ _ _ _).2 hi, _, (Record.returns_pure _ _).2 rfl,
      _root_.DecoupledConsensusModel.Proofs.NamedRuntime.stateBefore_tick S rho hi, ho⟩,
    fun ⟨hi, out, hout, _, ho⟩ => ⟨(Record.Event.map_ofVocabulary_getElem?_tick _ _ _ _).1 hi, ?_⟩⟩
  rw [(Record.returns_pure _ out).1 hout] at ho
  exact ho

/-- `DecoupledConsensusModel.Execution.NamedRun.emits` holds exactly when
    `Restated.Vocabulary.Execution.NamedRun.emits` holds at the model `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Execution.NamedRun.emits_vocabulary_eq (S : Setup V) (rho : NamedRun V) (v : V) (o : NamedObject V) (t : Time) :
    _root_.DecoupledConsensusModel.Execution.NamedRun.emits (V := V) S rho v o t ↔
      Restated.Vocabulary.Execution.NamedRun.emits (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun i => NamedRun.stateBefore S rho i) v o t :=
  Vocabulary.Execution.NamedRun.emitsAlong_vocabulary_eq S rho v o t

/-- `DecoupledConsensusModel.Execution.NamedRun.processes` holds exactly when
    `Restated.Vocabulary.Execution.NamedRun.processes` holds at the model `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Execution.NamedRun.processes_vocabulary_eq (S : Setup V) (rho : NamedRun V) (v : V) (o : NamedObject V) (t : Time) :
    _root_.DecoupledConsensusModel.Execution.NamedRun.processes (V := V) S rho v o t ↔
      Restated.Vocabulary.Execution.NamedRun.processes (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun i => NamedRun.stateBefore S rho i) v o t :=
  or_congr (Vocabulary.Execution.NamedRun.emitsAlong_vocabulary_eq S rho v o t)
    (exists_congr fun i => (Record.Event.map_ofVocabulary_getElem?_deliver _ _ _ _ _).symm)

/-- `DecoupledConsensusModel.Execution.NamedRun.processesAtIndex` holds exactly when
    `Restated.Vocabulary.Execution.NamedRun.processesAtIndex` holds at the model
    `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Execution.NamedRun.processesAtIndex_vocabulary_eq (S : Setup V) (rho : NamedRun V) (i : Nat) (v : V) (o : NamedObject V) :
    _root_.DecoupledConsensusModel.Execution.NamedRun.processesAtIndex (V := V) S rho i v o ↔ Restated.Vocabulary.Execution.NamedRun.processesAtIndex (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) i v o := by
  refine or_congr (exists_congr fun t => and_congr ?_ ?_)
    (exists_congr fun t => (Record.Event.map_ofVocabulary_getElem?_deliver _ _ _ _ _).symm)
  · exact (Record.Event.map_ofVocabulary_getElem?_tick _ _ _ _).symm
  rw [Vocabulary.Execution.NamedRun.emittedAt_vocabulary_eq]
  exact ⟨fun h l hl => by cases hl; exact h, fun h => h _ rfl⟩

end

end DecoupledConsensusModel.Sts.Restated
