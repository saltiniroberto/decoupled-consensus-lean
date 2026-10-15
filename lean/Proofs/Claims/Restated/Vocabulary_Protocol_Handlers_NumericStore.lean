import Proofs.Vocabulary.Protocol.Handlers.NumericStore
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_HMaxMonotone
import Proofs.Vocabulary.Protocol.Schedule.NamedTick
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_NumericStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring

/-!
# Body heights are bounded by the height maximum

In every world of a run, every body a validator's store holds has derived height at most the store's
`h_max`, and `h_max` never decreases, stated over a model `M : Record.Model V`.
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

/-- Every block of the tree of `n`'s core store has a chain-state height at most that store's
    `h_max`. -/
private def CoreBound' (n : M.N) : Prop :=
  ∀ B ∈ n.st.core.T, (n.st.core.σ B).h ≤ n.st.core.h_max

private theorem initial_bound' (facts : Record.Facts M) (S : Setup V) (v : V) :
    CoreBound' (M.initial S v) := by
  intro B _
  rw [facts.nd.initial_st]
  exact facts.hd.initial_core_σ_h_le_h_max B

private theorem step_bound' (facts : Record.Facts M) (S : Setup V) (w : V → M.N)
    (e : Record.Event V) (h : ∀ u, CoreBound' (w u)) :
    ∀ w' ∈ Record.worldStepOf M S w e, ∀ u, CoreBound' (w' u) := by
  intro w' hw' u
  cases e with
  | wake x t =>
    simp only [Record.worldStepOf, Set.mem_singleton_iff] at hw'
    subst hw'
    by_cases hu : u = x
    · subst u
      intro B hB
      rw [Function.update_self, (facts.nd.wake_st_record (w x)).1] at hB ⊢
      exact h x B hB
    · rw [Function.update_of_ne hu]
      exact h u
  | tick x t =>
    simp only [Record.worldStepOf, Set.mem_setOf_eq] at hw'
    rcases hw' with ⟨out, hout, rfl⟩ | ⟨-, rfl⟩
    · by_cases hu : u = x
      · subst u
        rw [Function.update_self]
        exact facts.nd.tick_core_bound S x (w x) t out hout (h x)
      · rw [Function.update_of_ne hu]
        exact h u
    · exact h u
  | deliver x o t =>
    simp only [Record.worldStepOf, Set.mem_setOf_eq] at hw'
    rcases hw' with ⟨n', hn', rfl⟩ | ⟨-, rfl⟩
    · by_cases hu : u = x
      · subst u
        rw [Function.update_self]
        exact facts.nd.process_core_bound S (w x) o n' hn' (h x)
      · rw [Function.update_of_ne hu]
        exact h u
    · exact h u

private theorem fold_bound' (facts : Record.Facts M) (S : Setup V) :
    ∀ (l : List (Record.Event V)) (w : V → M.N), (∀ u, CoreBound' (w u)) →
      ∀ w₂ ∈ l.foldlM (Record.worldStepOf M S) w, ∀ u, CoreBound' (w₂ u) := by
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
    exact ih w' (step_bound' facts S w e h w' hw') w₂ hw₂'

private theorem named_bound' (S : Setup V) (n : M.N)
    (hco : Restated.Vocabulary.Proofs.NamedStore.Coherent M S.E S.cfg n.st) (h : CoreBound' n) :
    Restated.Vocabulary.Proofs.NamedNumericStore.HeightsBounded M S n.st := by
  intro B hB
  have hmem : B.erase ∈ n.st.core.T := by
    rw [hco.1]
    exact Finset.mem_image_of_mem NamedBlock.erase hB
  have hb := h B.erase hmem
  rw [hco.2.2.2.2 B hB] at hb
  exact hb

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedNumericStore
open Execution Protocol

/-- In every world before the `i`-th event of `rho`, every body `v`'s store holds has a derived
    height at most the store's `h_max`. -/
theorem Vocabulary.Proofs.NamedNumericStore.heights_bounded_stateBefore (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (i : Nat) (v : V) : ∀ w₁ ∈ Record.stateBeforeOf M S rho i,
    Restated.Vocabulary.Proofs.NamedNumericStore.HeightsBounded M S (w₁ v).st := fun w₁ hw₁ =>
  named_bound' S _
    (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho i v w₁ hw₁).1.1.1
    (fold_bound' facts S (rho.events.take i) (fun u => M.initial S u)
      (fun u => initial_bound' facts S u) w₁ hw₁ v)

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedNumericStore
open Execution Protocol

/-- In every world before time `t` in `rho`, every body `v`'s store holds has a derived height at
    most the store's `h_max`. -/
theorem Vocabulary.Proofs.NamedNumericStore.heights_bounded_stateBeforeTime (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (t : Time) (v : V) : ∀ w₁ ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t,
    Restated.Vocabulary.Proofs.NamedNumericStore.HeightsBounded M S (w₁ v).st := fun w₁ hw₁ =>
  named_bound' S _
    (Restated.Vocabulary.Proofs.NamedRuntime.stateBeforeTime_invariants facts S rho t v w₁ hw₁).1.1.1
    (fold_bound' facts S _ (fun u => M.initial S u) (fun u => initial_bound' facts S u) w₁ hw₁ v)

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedNumericStore
open Execution Protocol

/-- In every world after the events up to time `t` in `rho`, every body `v`'s store holds has a
    derived height at most the store's `h_max`. -/
theorem Vocabulary.Proofs.NamedNumericStore.heights_bounded_readAt (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (t : Time) (v : V) : ∀ w₁ ∈ Restated.Vocabulary.Execution.NamedRun.readAt M S rho t,
    Restated.Vocabulary.Proofs.NamedNumericStore.HeightsBounded M S (w₁ v).st := fun w₁ hw₁ =>
  named_bound' S _
    (Restated.Vocabulary.Proofs.NamedRuntime.readAt_invariants facts S rho t v w₁ hw₁).1.1.1
    (fold_bound' facts S _ (fun u => M.initial S u) (fun u => initial_bound' facts S u) w₁ hw₁ v)

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedNumericStore
open Execution Protocol

/-- For `i ≤ j`, every world `w₁` before the `i`-th event of `rho` and every world `w₂` the events
    `i` to `j - 1` can lead to from `w₁`, the `h_max` of `v`'s store in `w₁` is at most the one in
    `w₂`. -/
theorem Vocabulary.Proofs.NamedNumericStore.stateBefore_hmax_mono (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (v : V)
    {i j : Nat} (hij : i ≤ j) : ∀ w₁ ∈ Record.stateBeforeOf M S rho i,
    ∀ w₂ ∈ ((rho.events.drop i).take (j - i)).foldlM (Record.worldStepOf M S) w₁,
    (w₁ v).st.core.h_max ≤
      (w₂ v).st.core.h_max :=
  Restated.Vocabulary.Proofs.HealingSurface.stateBefore_hMax_mono facts S rho v hij

end

end DecoupledConsensusModel.Sts.Restated
