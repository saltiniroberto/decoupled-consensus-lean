import Proofs.Vocabulary.Internal.Definitions.NamedExecutionQueries
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_FinalityGadget_Crossing
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Record.Wiring

/-!
# Committee pools over a run

The committee-pools invariant on core stores, on worlds, on the steps between worlds and along a
run, stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record DC

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Execution

/-- The committee-pools invariant `CommitteePools` of the core store `st`. -/
abbrev Vocabulary.Execution.CorePools (M : Record.Model V) (S : Setup V) (st : M.S) : Prop :=
  Restated.Vocabulary.Protocol.CommitteePools M S.E st

end

section
open DecoupledConsensusModel.Execution

/-- Every validator's core store in the world `w` satisfies `CorePools`. -/
def Vocabulary.Execution.NamedWorldCommitteePools (M : Record.Model V) (S : Setup V) (w : (V → M.N)) : Prop :=
  ∀ v : V, Restated.Vocabulary.Execution.CorePools M S (w v).st.core

end

section
open DecoupledConsensusModel.Execution

/-- In the world where every validator `v` holds `M.initial S v`, every validator's core store
    satisfies `CorePools`. -/
def Vocabulary.Execution.NamedWorldInitPoolsQuery (M : Record.Model V) (S : Setup V) : Prop :=
  Restated.Vocabulary.Execution.NamedWorldCommitteePools M S (fun v => M.initial S v)

end

section
open DecoupledConsensusModel.Execution

/-- For every world `w`, event `e` and world `w'` that `e` can lead to from `w`, if every
    validator's core store in `w` satisfies `CorePools`, so does every validator's core store in
    `w'`. -/
def Vocabulary.Execution.NamedWorldStepPoolsQuery (M : Record.Model V) (S : Setup V) : Prop :=
  ∀ (w : (V → M.N)) (e : Record.Event V), ∀ w' ∈ Record.worldStepOf M S w e,
    Restated.Vocabulary.Execution.NamedWorldCommitteePools M S w → Restated.Vocabulary.Execution.NamedWorldCommitteePools M S w'

end

section
open DecoupledConsensusModel.Execution

/-- Every validator's core store satisfies `CorePools` in every world that can hold before the
    `i`-th event of `rho`, at time `t`, before time `t`, and at the end of `rho`. -/
def Vocabulary.Execution.NamedRunPoolsQuery (M : Record.Model V) (S : Setup V) (rho : Record.Run V) : Prop :=
  (∀ (i : Nat), ∀ w ∈ Record.stateBeforeOf M S rho i, ∀ (v : V), Restated.Vocabulary.Execution.CorePools M S (w v).st.core) ∧
  (∀ (t : Time), ∀ w ∈ Restated.Vocabulary.Execution.NamedRun.readAt M S rho t, ∀ (v : V), Restated.Vocabulary.Execution.CorePools M S (w v).st.core) ∧
  (∀ (t : Time), ∀ w ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t, ∀ (v : V), Restated.Vocabulary.Execution.CorePools M S (w v).st.core) ∧
  (∀ w ∈ Restated.Vocabulary.Execution.NamedRun.final M S rho, ∀ v : V, Restated.Vocabulary.Execution.CorePools M S (w v).st.core)

end

end DecoupledConsensusModel.Sts.Restated
