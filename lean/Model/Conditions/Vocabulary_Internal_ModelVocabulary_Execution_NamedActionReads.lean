import Proofs.Vocabulary.Internal.ModelVocabulary.Execution.NamedActionReads
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring

/-!
# Action reads

The node states a validator can hold at a round's action time after the confirmation duty, as sets
over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Execution.NamedActionReads
open DecoupledConsensusModel.Protocol

/-- The set of node states after the confirmation duty at round `r`'s action time, starting from the
    node state `before`: its clock set to that time, its cache an outcome of `M.onPhaseTick`, and
    its store an outcome of the confirmation duty. -/
def Vocabulary.Execution.NamedActionReads.actionReadFrom (M : Record.Model V) (S : Setup V) (before : M.N) (r : Round) :
    DC.NDR M.N :=
  let t := (Restated.Vocabulary.Execution.Setup.a M S r)
  { n | ∃ c : M.Cache, M.onPhaseTick S.E S.hc before.st.core.toHealing t before.cache ⇢ c ∧
      ∃ st : M.NS, M.duties_update_confirmation_with
        (M.gradeContract c) S.E S.hc (M.ns_setClock S.E before.st t) (S.E.slotOf t - 1) ⇢ st ∧
      n = M.mkNode st before.record c }

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Execution.NamedActionReads
open DecoupledConsensusModel.Protocol

/-- The set of node states in `actionReadFrom M S (w v) r` for some world `w` that can hold before
    round `r`'s action time. -/
def Vocabulary.Execution.NamedActionReads.actionReadAt (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (v : V) (r : Round) :
    DC.NDR M.N :=
  { n | ∃ w ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho
      (Restated.Vocabulary.Execution.Setup.a M S r),
      n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (w v) r }

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Execution.NamedActionReads
open DecoupledConsensusModel.Protocol

/-- At the model `Record.Model.vocabulary`,
    `Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom` is the singleton of
    `DecoupledConsensusModel.Execution.NamedActionReads.actionReadFrom`. -/
@[record_vocabulary]
theorem Vocabulary.Execution.NamedActionReads.actionReadFrom_vocabulary_eq (S : Setup V) (before : NamedNodeState V) (r : Round) :
    Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom (V := V) Record.Model.vocabulary S before r =
      {_root_.DecoupledConsensusModel.Execution.NamedActionReads.actionReadFrom (V := V) S before r} := by
  ext n
  constructor
  · rintro ⟨c, hc, st, hst, rfl⟩
    obtain rfl := (Record.returns_pure _ _).1 hc
    obtain rfl := (Record.returns_pure _ _).1 hst
    show _ = _
    unfold _root_.DecoupledConsensusModel.Execution.NamedActionReads.actionReadFrom
      _root_.DecoupledConsensusModel.Execution.NamedActionReads.confirmationReadFrom
      _root_.DecoupledConsensusModel.Execution.NamedActionReads.preparedCache
    simp only [Record.Model.vocabulary, Record.Model.N.st, Record.Model.N.record, Record.Model.N.cache,
      Record.Model.NS.core, Record.Model.S.toHealing]
  · intro hn
    obtain rfl : n = _ := hn
    refine ⟨_, (Record.returns_pure _ _).2 rfl, _, (Record.returns_pure _ _).2 rfl, ?_⟩
    unfold _root_.DecoupledConsensusModel.Execution.NamedActionReads.actionReadFrom
      _root_.DecoupledConsensusModel.Execution.NamedActionReads.confirmationReadFrom
      _root_.DecoupledConsensusModel.Execution.NamedActionReads.preparedCache
    simp only [Record.Model.vocabulary, Record.Model.N.st, Record.Model.N.record, Record.Model.N.cache,
      Record.Model.NS.core, Record.Model.S.toHealing]

/-- At the model `Record.Model.vocabulary`,
    `Restated.Vocabulary.Execution.NamedActionReads.actionReadAt` is the singleton of
    `DecoupledConsensusModel.Execution.NamedActionReads.actionReadAt`. -/
@[record_vocabulary]
theorem Vocabulary.Execution.NamedActionReads.actionReadAt_vocabulary_eq (S : Setup V) (rho : NamedRun V) (v : V) (r : Round) :
    Restated.Vocabulary.Execution.NamedActionReads.actionReadAt (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) v r =
      {_root_.DecoupledConsensusModel.Execution.NamedActionReads.actionReadAt (V := V) S rho v r} := by
  ext n
  rw [Restated.Vocabulary.Execution.NamedActionReads.actionReadAt,
    Vocabulary.Execution.NamedRun.stateBeforeTime_vocabulary_eq]
  constructor
  · rintro ⟨w, hw, hn⟩
    obtain rfl : w = _ := hw
    rw [Vocabulary.Execution.NamedActionReads.actionReadFrom_vocabulary_eq] at hn
    exact hn
  · intro hn
    exact ⟨_, rfl, by rw [Vocabulary.Execution.NamedActionReads.actionReadFrom_vocabulary_eq]; exact hn⟩

end

end DecoupledConsensusModel.Sts.Restated
