import Proofs.Vocabulary.Protocol.Handlers.JustificationCarrier
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Vocabulary.Protocol.Schedule.NamedTick
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring

/-!
# A body for the store's justification

In every world of a run, a validator's store holds a body whose derived justification is the store's
own, stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open Execution

/-- Some block of the tree of `n`'s core store has a chain state whose justification and
    justification height are the store's own. -/
private def CoreJustifier' (n : M.N) : Prop :=
  ∃ D ∈ n.st.core.T, (n.st.core.σ D).J = n.st.core.J ∧ (n.st.core.σ D).h_j = n.st.core.h_j

/-- `n`'s named store satisfies the confirmation-membership invariant, its signing record the tick
    record invariant, and its core store `CoreJustifier'`. -/
private def Carried' (S : Setup V) (n : M.N) : Prop :=
  (Restated.Vocabulary.Proofs.NamedConfirmationMembership.Invariant M S.E S.cfg n.st ∧
    Restated.Vocabulary.Proofs.NamedTickRecord.Invariant M n.record) ∧ CoreJustifier' n

private theorem step_carried' (facts : Record.Facts M) (S : Setup V) (w : V → M.N)
    (e : Record.Event V) (h : ∀ u, Carried' S (w u)) :
    ∀ w' ∈ Record.worldStepOf M S w e, ∀ u, Carried' S (w' u) := by
  intro w' hw' u
  cases e with
  | wake x t =>
    have hw'' : w' = Function.update w x (M.wake (w x)) := hw'
    subst hw''
    by_cases hu : u = x
    · subst u
      rw [Function.update_self]
      unfold Carried' CoreJustifier'
      rw [(facts.nd.wake_st_record _).1, (facts.nd.wake_st_record _).2]
      exact h x
    · rw [Function.update_of_ne hu]
      exact h u
  | tick x t =>
    simp only [Record.worldStepOf, Set.mem_setOf_eq] at hw'
    rcases hw' with ⟨out, hout, rfl⟩ | ⟨-, rfl⟩
    · by_cases hu : u = x
      · subst u
        rw [Function.update_self]
        exact ⟨⟨facts.nd.confirmation_invariant_tick S x (w x) t (h x).1.1 out hout,
            facts.nd.record_invariant_tick S x (w x) t (h x).1.2 out hout⟩,
          facts.nd.tick_core_justifier S x (w x) t out hout (h x).1.1.1.1 (h x).2⟩
      · rw [Function.update_of_ne hu]
        exact h u
    · exact h u
  | deliver x o t =>
    simp only [Record.worldStepOf, Set.mem_setOf_eq] at hw'
    rcases hw' with ⟨n', hn', rfl⟩ | ⟨-, rfl⟩
    · by_cases hu : u = x
      · subst u
        rw [Function.update_self]
        exact ⟨facts.nd.invariants_process S (w x) o (h x).1.1 (h x).1.2 n' hn',
          facts.nd.process_core_justifier S (w x) o n' hn' (h x).1.1.1.1 (h x).2⟩
      · rw [Function.update_of_ne hu]
        exact h u
    · exact h u

private theorem fold_carried' (facts : Record.Facts M) (S : Setup V) :
    ∀ (l : List (Record.Event V)) (w : V → M.N), (∀ u, Carried' S (w u)) →
      ∀ w₂ ∈ l.foldlM (Record.worldStepOf M S) w, ∀ u, Carried' S (w₂ u) := by
  intro l
  induction l with
  | nil =>
    intro w h w₂ hw₂
    obtain rfl := Set.mem_singleton_iff.mp hw₂
    exact h
  | cons e l ih =>
    intro w h w₂ hw₂
    rw [List.foldlM_cons, Set.bind_def] at hw₂
    obtain ⟨w', hw', hw₂'⟩ := Set.mem_iUnion₂.mp hw₂
    exact ih w' (step_carried' facts S w e h w' hw') w₂ hw₂'

private theorem initial_carried' (facts : Record.Facts M) (S : Setup V) (v : V) :
    Carried' S (M.initial S v) := by
  refine ⟨facts.nd.initial_invariants S v, ?_⟩
  unfold CoreJustifier'
  rw [facts.nd.initial_st S v]
  exact facts.hd.initial_core_justifier

private theorem named_justifier' (S : Setup V) (n : M.N)
    (hco : Restated.Vocabulary.Proofs.NamedStore.Coherent M S.E S.cfg n.st) (h : CoreJustifier' n) :
    ∃ D : NamedBlock V, D ∈ n.st.bodies ∧ (M.derive_named S.E S.cfg D).J = n.st.core.J ∧
      (M.derive_named S.E S.cfg D).h_j = n.st.core.h_j := by
  obtain ⟨raw, hraw, hF, hh⟩ := h
  rw [hco.1] at hraw
  obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hraw
  rw [hco.2.2.2.2 D hD] at hF hh
  exact ⟨D, hD, hF, hh⟩

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedJustificationCarrier
open Execution Protocol

/-- In every world before time `t` in `rho`, `v`'s store holds a body whose derived justification
    and justification height are those of `v`'s core store. -/
theorem Vocabulary.Proofs.NamedJustificationCarrier.justification_carrier_stateBeforeTime (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (t : Time) (v : V) : ∀ w₁ ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t,
    ∃ D : NamedBlock V, D ∈ (w₁ v).st.bodies ∧
      (M.derive_named S.E S.cfg D).J = (w₁ v).st.core.J ∧
      (M.derive_named S.E S.cfg D).h_j = (w₁ v).st.core.h_j := fun w₁ hw₁ =>
  named_justifier' S _
    (Restated.Vocabulary.Proofs.NamedRuntime.stateBeforeTime_invariants facts S rho t v w₁ hw₁).1.1.1
    (fold_carried' facts S _ (fun u => M.initial S u) (fun u => initial_carried' facts S u)
      w₁ hw₁ v).2

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedJustificationCarrier
open Execution Protocol

/-- In every world before the `i`-th event of `rho`, `v`'s store holds a body whose derived
    justification and justification height are those of `v`'s core store. -/
theorem Vocabulary.Proofs.NamedJustificationCarrier.justification_carrier_stateBefore (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (i : Nat) (v : V) : ∀ w₁ ∈ Record.stateBeforeOf M S rho i,
    ∃ D : NamedBlock V, D ∈ (w₁ v).st.bodies ∧
      (M.derive_named S.E S.cfg D).J = (w₁ v).st.core.J ∧
      (M.derive_named S.E S.cfg D).h_j = (w₁ v).st.core.h_j := fun w₁ hw₁ =>
  named_justifier' S _
    (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho i v w₁ hw₁).1.1.1
    (fold_carried' facts S (rho.events.take i) (fun u => M.initial S u)
      (fun u => initial_carried' facts S u) w₁ hw₁ v).2

end

end DecoupledConsensusModel.Sts.Restated
