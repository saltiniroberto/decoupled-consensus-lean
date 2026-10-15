import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_NumericStore
import Model.Conditions.Claim13bStepKitStore
import Model.Conditions.Vocabulary_Execution_Runtime
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_NumericStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bStepKitStore

/-!
# Event lists and height bounds of a store

A validator's event list only grows, the projected run of a later step contains the earlier node
state, and every store's chain-state heights are bounded by its `h_max`, which never decreases,
stated over a model `M : Record.Model V` and its facts `facts : Record.Facts M`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For `i ≤ j`, `v`'s event list for the first `i` steps is a prefix of its list for the first `j`
    steps. -/
theorem vevents_prefix (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V) {i j : Nat} (hij : i ≤ j) :
    Record.veventsOf M S Sched x v i <+: Record.veventsOf M S Sched x v j := by
  induction j, hij using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ j hij ih =>
      refine ih.trans ?_
      rw [show Record.veventsOf M S Sched x v (j + 1)
            = Record.veventsOf M S Sched x v j ++ Record.actionEventsOf M S Sched v (x[j].time : Int) (x.lbl j) from rfl]
      exact List.prefix_append _ _

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For `i ≤ j`, the first `(veventsOf … i).length` events of `v`'s list for `j` steps are its list
    for `i` steps. -/
theorem take_vevents (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V) {i j : Nat} (hij : i ≤ j) :
    (Record.veventsOf M S Sched x v j).take (Record.veventsOf M S Sched x v i).length = Record.veventsOf M S Sched x v i :=
  (List.prefix_iff_eq_take.mp (Restated.vevents_prefix facts S Sched x v hij)).symm

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For `i ≤ j`, some world the run of `v`'s events of the first `j` steps reaches at the end of its
    events of the first `i` steps holds, at `v`, `v`'s node state after `i` steps. -/
theorem stateBefore_runOf_of_le (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V)
    {i j : Nat} (hij : i ≤ j) :
    ∃ w ∈ Record.stateBeforeOf M (Setup.alwaysAwake S) (Record.runOfM M S Sched x v j)
        (Record.veventsOf M S Sched x v i).length, w v = x[i][v].st := by
  unfold Record.stateBeforeOf
  show ∃ w ∈ ((Record.veventsOf M S Sched x v j).take (Record.veventsOf M S Sched x v i).length).foldlM
      (Record.worldStepOf M (Setup.alwaysAwake S)) (fun v' => M.initial (Setup.alwaysAwake S) v'),
      w v = x[i][v].st
  rw [Restated.take_vevents facts S Sched x v hij]
  exact Record.fold_veventsOf M S Sched x facts.nd.wake_events_or_id v i

/-- For `i ≤ j` and a world `w₁` holding `v`'s node state after `i` steps, the events `v`
    contributes in steps `i` to `j` can lead from `w₁` to a world holding `v`'s node state after `j`
    steps. -/
private theorem fold_veventsOf_drop (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V)
    {i j : Nat} (hij : i ≤ j)
    (w₁ : V → M.N) (hw₁ : w₁ v = x[i][v].st) :
    ∃ w₂ ∈ ((Record.veventsOf M S Sched x v j).drop (Record.veventsOf M S Sched x v i).length).foldlM
        (Record.worldStepOf M (Setup.alwaysAwake S)) w₁, w₂ v = x[j][v].st := by
  induction j, hij using Nat.le_induction with
  | base =>
      rw [List.drop_length]
      exact ⟨w₁, Set.mem_singleton _, hw₁⟩
  | succ j hij ih =>
      obtain ⟨w₂, hw₂, hw₂v⟩ := ih
      obtain ⟨w₃, hw₃, hw₃v⟩ := Record.fold_actionEventsOf M S Sched x facts.nd.wake_events_or_id v j w₂ hw₂v
      refine ⟨w₃, ?_, hw₃v⟩
      have hlen : (Record.veventsOf M S Sched x v i).length ≤ (Record.veventsOf M S Sched x v j).length :=
        (Restated.vevents_prefix facts S Sched x v hij).length_le
      rw [show Record.veventsOf M S Sched x v (j + 1)
            = Record.veventsOf M S Sched x v j ++ Record.actionEventsOf M S Sched v (x[j].time : Int) (x.lbl j)
          from rfl, List.drop_append_of_le_length hlen, List.foldlM_append, Set.bind_def]
      exact Set.mem_biUnion hw₂ hw₃

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- After any number of steps, every body a validator's store holds replays to a chain state whose
    height is at most the store's `h_max`. -/
theorem heights_le_hMax_sts (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (i : Nat) (v : V) :
    ∀ D ∈ (x[i][v].st).st.bodies,
      (M.derive_named S.E S.cfg D).h ≤ (x[i][v].st).st.core.h_max := by
  obtain ⟨w, hw, hwv⟩ := Record.stateBeforeOf_runOfM M S Sched x facts.nd.wake_events_or_id v i
  have h := Restated.Vocabulary.Proofs.NamedNumericStore.heights_bounded_stateBefore facts
    (Setup.alwaysAwake S) (Record.runOfM M S Sched x v i) (Record.veventsOf M S Sched x v i).length v
    w hw
  rw [hwv] at h
  exact h

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- After any number of steps, every block in a validator's tree has chain-state height at most the
    store's `h_max`. -/
theorem treeHeightsLeHMax_sts (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (i : Nat) (v : V) :
    ∀ B ∈ (x[i][v].st).st.core.T,
      ((x[i][v].st).st.core.σ B).h ≤ (x[i][v].st).st.core.h_max := by
  obtain ⟨w, hw, hwv⟩ := Record.stateBeforeOf_runOfM M S Sched x facts.nd.wake_events_or_id v i
  have hinv := Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts
    (Setup.alwaysAwake S) (Record.runOfM M S Sched x v i) (Record.veventsOf M S Sched x v i).length v
    w hw
  rw [hwv] at hinv
  have hco : Restated.Vocabulary.Proofs.NamedStore.Coherent M (Setup.alwaysAwake S).E (Setup.alwaysAwake S).cfg
      (x[i][v].st).st := hinv.1.1.1
  intro B hB
  rw [hco.1] at hB
  obtain ⟨D, hD, hDB⟩ := Finset.mem_image.mp hB
  subst hDB
  rw [hco.2.2.2.2 D hD]
  exact Restated.heights_le_hMax_sts facts S Sched x i v D hD

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For `i ≤ j`, `v`'s `h_max` after `i` steps is at most its `h_max` after `j` steps. -/
theorem h_max_mono_sts (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V)
    {i j : Nat} (hij : i ≤ j) :
    (x[i][v].st).st.core.h_max ≤ (x[j][v].st).st.core.h_max := by
  have hlen : (Record.veventsOf M S Sched x v i).length ≤ (Record.veventsOf M S Sched x v j).length :=
    (Restated.vevents_prefix facts S Sched x v hij).length_le
  obtain ⟨w₁, hw₁, hw₁v⟩ := Restated.stateBefore_runOf_of_le facts S Sched x v hij
  obtain ⟨w₂, hw₂, hw₂v⟩ := fold_veventsOf_drop facts S Sched x v hij w₁ hw₁v
  have hw₂' : w₂ ∈ (((Record.runOfM M S Sched x v j).events.drop
      (Record.veventsOf M S Sched x v i).length).take
      ((Record.veventsOf M S Sched x v j).length - (Record.veventsOf M S Sched x v i).length)).foldlM
      (Record.worldStepOf M (Setup.alwaysAwake S)) w₁ := by
    show w₂ ∈ (((Record.veventsOf M S Sched x v j).drop
      (Record.veventsOf M S Sched x v i).length).take _).foldlM _ w₁
    rw [List.take_of_length_le (by simp)]
    exact hw₂
  have h := Restated.Vocabulary.Proofs.NamedNumericStore.stateBefore_hmax_mono facts
    (Setup.alwaysAwake S) (Record.runOfM M S Sched x v j) v hlen w₁ hw₁ w₂ hw₂'
  rw [hw₁v, hw₂v] at h
  exact h

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- In a grade view whose pools are indexed by the attestations' own rounds, every token of every
    outcome of the raw view a round-`r` grade reads carries a round of the expiry window
    `M.latest_window eta r`. -/
theorem rawView_round_mem_window (facts : Record.Facts M) {gv : M.GV}
    (hidx : Restated.SGVotesRoundIndexed M gv) (eta r : Round) (cutoff : Int) (v : V) :
    ∀ X, M.rawView gv eta r cutoff v ⇢ X → ∀ tok ∈ X,
      tok.round ∈ M.latest_window eta r := by
  intro X hX tok htok
  obtain ⟨Y, hY⟩ := facts.gr.rawInputs_nonempty gv eta r cutoff v
  obtain ⟨u, hu, htu⟩ := facts.gr.exists_rawInputs_of_mem_rawView X hX htok Y hY
  obtain ⟨⟨k, hk, huk⟩, _, _⟩ := facts.gr.rawInputs_mem_window gv eta r cutoff v Y hY hu
  have hround : u.round = k := hidx k u huk
  rw [← htu, facts.gr.token_round, hround]
  exact hk

end

end DecoupledConsensusModel.Sts.Restated
