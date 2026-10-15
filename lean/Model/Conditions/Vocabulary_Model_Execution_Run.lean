import Model.Vocabulary.Execution.Run
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.RunVocabulary
import Model.Record.Wiring
import Proofs.Vocabulary.ModelVocabularyFacts

/-!
# Run states, stores and blocks

The worlds and stores a run can reach before or at a time, the blocks of a run read along a path, a
validator's confirmation reads, and root collision freedom, over a model `M : Record.Model V`.
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

/-- The set of worlds that can hold after the events of `rho` whose time is before `t`, starting
    from the world where every validator `v` holds `M.initial S v`. -/
def Vocabulary.Execution.NamedRun.stateBeforeTime (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (t : Time) :
    DC.NDR (V → M.N) :=
  (rho.events.filter (fun e => decide (e.time < t))).foldlM (Record.worldStepOf M S) (fun v => M.initial S v)

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Execution.NamedRun

/-- The set of worlds that can hold after the events of `rho` whose time is at most `t`, starting
    from the world where every validator `v` holds `M.initial S v`. -/
def Vocabulary.Execution.NamedRun.readAt (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (t : Time) :
    DC.NDR (V → M.N) :=
  (rho.events.filter (fun e => decide (e.time ≤ t))).foldlM (Record.worldStepOf M S) (fun v => M.initial S v)

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Execution.NamedRun

/-- `B` is a block object of `rho`, or for some honest `v` and some index `i`, `B` is among `v`'s
    stored bodies in the world `W i`. -/
def Vocabulary.Execution.NamedRun.directBlockInRun (M : Record.Model V) (S : Setup V) (rho : Record.Run V)
    (W : Nat → V → M.N) (B : NamedBlock V) : Prop :=
  NamedObject.block B ∈ objects rho ∨
    ∃ v ∈ rho.honest, ∃ i : Nat, B ∈ (W i v).st.bodies

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Execution.NamedRun

/-- `A ⪯ B` for some block `B` with `directBlockInRun M S rho W B`. -/
def Vocabulary.Execution.NamedRun.blockInRun (M : Record.Model V) (S : Setup V) (rho : Record.Run V)
    (W : Nat → V → M.N) (A : NamedBlock V) : Prop :=
  ∃ B : NamedBlock V, Restated.Vocabulary.Execution.NamedRun.directBlockInRun M S rho W B ∧ NamedBlock.Preceq A B

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Execution.NamedActionReads
open DecoupledConsensusModel.Protocol

/-- The set of `v`'s confirmation reads at time `t`: for every world `w` that can hold before `t`
    and every outcome `c` of `M.onPhaseTick` on `v`'s cache, the node state with `v`'s store with
    its clock set to `t`, `v`'s signing record, and the cache `c`. -/
def Vocabulary.Execution.NamedActionReads.confirmationReadAt (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (v : V) (t : Time) :
    DC.NDR M.N :=
  { n | ∃ w ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t, ∃ c : M.Cache,
      M.onPhaseTick S.E S.hc (w v).st.core.toHealing t (w v).cache ⇢ c ∧
      n = M.mkNode (M.ns_setClock S.E (w v).st t) (w v).record c }

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Execution.Run

/-- The set of `v`'s stores in every world that can hold after the events of `rho` whose time is at
    most `t`. -/
def Vocabulary.Execution.Run.storeAt (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (v : V) (t : Time) : DC.NDR M.NS :=
  (fun w => (w v).st) '' Restated.Vocabulary.Execution.NamedRun.readAt M S rho t

end

section
open DecoupledConsensusModel.Execution

/-- Equal roots identify the ancestors of the blocks of `rho` read along the path `W`. -/
structure Vocabulary.Execution.NamedRootCollisionFree (M : Record.Model V) (S : Setup V) (rho : Record.Run V)
    (W : Nat → V → M.N) : Prop where
  root_injective : ∀ B C : NamedBlock V,
    Restated.Vocabulary.Execution.NamedRun.blockInRun M S rho W B → Restated.Vocabulary.Execution.NamedRun.blockInRun M S rho W C →
    ∀ A D : NamedBlock V,
      (NamedBlock.Preceq A B ∨ NamedBlock.Preceq A C) →
      (NamedBlock.Preceq D B ∨ NamedBlock.Preceq D C) → A.root = D.root → A = D

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Execution.NamedRun
open DecoupledConsensusModel.Execution.NamedActionReads
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Execution.Run

/-- At the model `Record.Model.vocabulary`, `Restated.Vocabulary.Execution.NamedRun.stateBeforeTime` is
    the singleton of `DecoupledConsensusModel.Execution.NamedRun.stateBeforeTime`. -/
@[record_vocabulary]
theorem Vocabulary.Execution.NamedRun.stateBeforeTime_vocabulary_eq (S : Setup V) (rho : NamedRun V) (t : Time) :
    Restated.Vocabulary.Execution.NamedRun.stateBeforeTime (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) t =
      {_root_.DecoupledConsensusModel.Execution.NamedRun.stateBeforeTime (V := V) S rho t} := by
  have h := Record.stateBeforeTime_vocabulary_erase S (Record.Run.ofVocabulary rho) t
  rwa [Record.Run.toVocabulary_ofVocabulary] at h

/-- At the model `Record.Model.vocabulary`, `Restated.Vocabulary.Execution.NamedRun.readAt` is the
    singleton of `DecoupledConsensusModel.Execution.NamedRun.readAt`. -/
@[record_vocabulary]
theorem Vocabulary.Execution.NamedRun.readAt_vocabulary_eq (S : Setup V) (rho : NamedRun V) (t : Time) :
    Restated.Vocabulary.Execution.NamedRun.readAt (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) t =
      {_root_.DecoupledConsensusModel.Execution.NamedRun.readAt (V := V) S rho t} := by
  rw [Restated.Vocabulary.Execution.NamedRun.readAt, Record.Run.ofVocabulary_events, List.filter_map]
  simp only [Function.comp_def, Record.Event.ofVocabulary_time]
  exact Record.foldlM_worldStepOf_vocabulary S _ NamedWorld.init

/-- `DecoupledConsensusModel.Execution.NamedRun.directBlockInRun` holds exactly when
    `Restated.Vocabulary.Execution.NamedRun.directBlockInRun` holds at the model
    `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Execution.NamedRun.directBlockInRun_vocabulary_eq (S : Setup V) (rho : NamedRun V) (B : NamedBlock V) :
    _root_.DecoupledConsensusModel.Execution.NamedRun.directBlockInRun (V := V) S rho B ↔
      Restated.Vocabulary.Execution.NamedRun.directBlockInRun (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun i => _root_.DecoupledConsensusModel.Execution.NamedRun.stateBefore S rho i) B := by
  simp only [Restated.Vocabulary.Execution.NamedRun.directBlockInRun, Restated.objects_ofVocabulary,
    Record.Run.ofVocabulary_honest]
  exact Iff.rfl

/-- `DecoupledConsensusModel.Execution.NamedRun.blockInRun` holds exactly when
    `Restated.Vocabulary.Execution.NamedRun.blockInRun` holds at the model `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Execution.NamedRun.blockInRun_vocabulary_eq (S : Setup V) (rho : NamedRun V) (A : NamedBlock V) :
    _root_.DecoupledConsensusModel.Execution.NamedRun.blockInRun (V := V) S rho A ↔
      Restated.Vocabulary.Execution.NamedRun.blockInRun (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun i => _root_.DecoupledConsensusModel.Execution.NamedRun.stateBefore S rho i) A := by
  simp only [_root_.DecoupledConsensusModel.Execution.NamedRun.blockInRun,
    Restated.Vocabulary.Execution.NamedRun.blockInRun, directBlockInRun_vocabulary_eq]

/-- At the model `Record.Model.vocabulary`,
    `Restated.Vocabulary.Execution.NamedActionReads.confirmationReadAt` is the singleton of
    `DecoupledConsensusModel.Execution.NamedActionReads.confirmationReadAt`. -/
@[record_vocabulary]
theorem Vocabulary.Execution.NamedActionReads.confirmationReadAt_vocabulary_eq (S : Setup V) (rho : NamedRun V) (v : V) (t : Time) :
    Restated.Vocabulary.Execution.NamedActionReads.confirmationReadAt (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) v t =
      {_root_.DecoupledConsensusModel.Execution.NamedActionReads.confirmationReadAt (V := V) S rho v t} := by
  ext n
  rw [Restated.Vocabulary.Execution.NamedActionReads.confirmationReadAt,
    Vocabulary.Execution.NamedRun.stateBeforeTime_vocabulary_eq]
  constructor
  · rintro ⟨w, hw, c, hc, rfl⟩
    obtain rfl : w = _ := hw
    obtain rfl := (Record.returns_pure _ _).1 hc
    show _ = _
    unfold _root_.DecoupledConsensusModel.Execution.NamedActionReads.confirmationReadAt
      _root_.DecoupledConsensusModel.Execution.NamedActionReads.confirmationReadFrom
      _root_.DecoupledConsensusModel.Execution.NamedActionReads.preparedCache
    simp only [Record.Model.vocabulary, Record.Model.N.st, Record.Model.N.record, Record.Model.N.cache,
      Record.Model.NS.core, Record.Model.S.toHealing]
  · intro hn
    obtain rfl : n = _ := hn
    refine ⟨_root_.DecoupledConsensusModel.Execution.NamedRun.stateBeforeTime S rho t, rfl, _,
      (Record.returns_pure _ _).2 rfl, ?_⟩
    unfold _root_.DecoupledConsensusModel.Execution.NamedActionReads.confirmationReadAt
      _root_.DecoupledConsensusModel.Execution.NamedActionReads.confirmationReadFrom
      _root_.DecoupledConsensusModel.Execution.NamedActionReads.preparedCache
    simp only [Record.Model.vocabulary, Record.Model.N.st, Record.Model.N.record, Record.Model.N.cache,
      Record.Model.NS.core, Record.Model.S.toHealing]

/-- At the model `Record.Model.vocabulary`, `Restated.Vocabulary.Execution.Run.storeAt` is the singleton
    of `DecoupledConsensusModel.Execution.Run.storeAt`. -/
@[record_vocabulary]
theorem Vocabulary.Execution.Run.storeAt_vocabulary_eq (S : Setup V) (rho : Run V) (v : V) (t : Time) :
    Restated.Vocabulary.Execution.Run.storeAt (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) v t =
      {_root_.DecoupledConsensusModel.Execution.Run.storeAt (V := V) S rho v t} := by
  rw [Restated.Vocabulary.Execution.Run.storeAt, Vocabulary.Execution.NamedRun.readAt_vocabulary_eq]
  exact Set.image_singleton

/-- `DecoupledConsensusModel.Execution.NamedRootCollisionFree` holds exactly when
    `Restated.Vocabulary.Execution.NamedRootCollisionFree` holds at the model `Record.Model.vocabulary`. -/
@[record_vocabulary]
theorem Vocabulary.Execution.NamedRootCollisionFree_vocabulary_eq (S : Setup V) (rho : NamedRun V) :
    _root_.DecoupledConsensusModel.Execution.NamedRootCollisionFree (V := V) S rho ↔
      Restated.Vocabulary.Execution.NamedRootCollisionFree (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho)
        (fun i => _root_.DecoupledConsensusModel.Execution.NamedRun.stateBefore S rho i) := by
  constructor
  · rintro ⟨h⟩
    exact ⟨fun B C hB hC => h B C ((Vocabulary.Execution.NamedRun.blockInRun_vocabulary_eq S rho B).2 hB)
      ((Vocabulary.Execution.NamedRun.blockInRun_vocabulary_eq S rho C).2 hC)⟩
  · rintro ⟨h⟩
    exact ⟨fun B C hB hC => h B C ((Vocabulary.Execution.NamedRun.blockInRun_vocabulary_eq S rho B).1 hB)
      ((Vocabulary.Execution.NamedRun.blockInRun_vocabulary_eq S rho C).1 hC)⟩

end

end DecoupledConsensusModel.Sts.Restated
