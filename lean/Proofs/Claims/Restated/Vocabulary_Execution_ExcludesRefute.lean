import Proofs.Vocabulary.Execution.ExcludesRefute
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Model.Conditions.RunVocabulary
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Record.Wiring

/-!
# Compatibility at a later read refutes exclusion

Theorems over a model `M : Record.Model V` and its facts `facts : Record.Facts M`, each comparing
two worlds of one run, the later reached from the earlier by the events between them: a finalized
block compatible with a block at the later world was compatible with it at the earlier one, and the
finalized block at the earlier world is an ancestor of the one at the later world.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel
open Execution

/-- If `A` is an ancestor of `C` and `C` is compatible with `B`, then `A` is compatible with `B`. -/
private theorem er_compatible_of_preceq_of_compatible {A C B : Block V}
    (hAC : Block.Preceq A C) (hCB : Block.compatible C B = true) :
    Block.compatible A B = true := by
  have hAC' : Block.preceq A C = true := ModelProperties.preceq_eq_true_iff_Preceq.mpr hAC
  simp only [Block.compatible, Bool.or_eq_true] at hCB ⊢
  rcases hCB with hCB | hBC
  · exact Or.inl (Block.preceq_trans hAC' hCB)
  · simpa only [Block.compatible, Bool.or_eq_true] using
      (Block.compatible_of_preceq_common hAC' hBC)

/-- For `i ≤ j`, a world reached by the events `i` to `j - 1` of `rho` from a world that can hold
    before the `i`-th event can hold before the `j`-th event. -/
private theorem er_mem_stateBeforeOf_of_path (S : Setup V) (rho : Record.Run V) {i j : Nat}
    (hij : i ≤ j) {w₁ w₂ : V → M.N} (hw₁ : w₁ ∈ Record.stateBeforeOf M S rho i)
    (hw₂ : w₂ ∈ ((rho.events.drop i).take (j - i)).foldlM (Record.worldStepOf M S) w₁) :
    w₂ ∈ Record.stateBeforeOf M S rho j := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  rw [Nat.add_sub_cancel_left] at hw₂
  unfold Record.stateBeforeOf
  rw [List.take_add, List.foldlM_append, Set.bind_def]
  exact Set.mem_iUnion₂.mpr ⟨w₁, hw₁, hw₂⟩

/-- If the worlds before time `d` are the worlds before event `n`, with `n ≤ j`, then for every
    world `w₁` before time `d` and every world `w₂` the events `n` to `j - 1` lead to from `w₁`, if
    the finalized block of `w`'s store in `w₂` is compatible with `B`, so is the finalized block of
    `w`'s store in `w₁`. -/
theorem Vocabulary.Proofs.not_excludes_of_compatible_later (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) {w : V} {B : NamedBlock V}
    {d : Time} {j : Nat} {n : Nat}
    (hn : Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho d =
      Record.stateBeforeOf M S rho n) (hnj : n ≤ j) :
    ∀ w₁ ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho d,
    ∀ w₂ ∈ ((rho.events.drop n).take (j - n)).foldlM (Record.worldStepOf M S) w₁,
      Block.compatible (w₂ w).st.core.F B.erase = true →
      Block.compatible (w₁ w).st.core.F B.erase = true := by
  intro w₁ hw₁ w₂ hw₂ hcompat
  rw [hn] at hw₁
  have hmono := Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_F_mono facts S rho w hnj
    w₁ hw₁ w₂ hw₂
  exact er_compatible_of_preceq_of_compatible hmono hcompat

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel
open Execution

/-- In a run sorted by key, the worlds before time `t` are the worlds before event `n`, where `n` is
    the number of events of the run whose time is before `t`. -/
theorem Vocabulary.Proofs.stateBeforeTime_eq_stateBefore_filter_length (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key)) (t : Time) :
    Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t =
      Record.stateBeforeOf M S rho
        (rho.events.filter (fun e => decide (e.time < t))).length := by
  let p : Record.Event V → Bool := fun e => decide (e.time < t)
  have hpref : rho.events.filter p <+: rho.events := by
    rw [Proofs.Bridges.filter_eq_takeWhile_of_pairwise
      (fun e f hk hf => by
        simp only [p, decide_eq_true_eq] at hf ⊢
        exact (Restated.time_le_of_key_le hk).trans_lt hf) _ hsorted]
    exact List.takeWhile_prefix p
  have hpre : rho.events.filter p =
      rho.events.take (rho.events.filter p).length :=
    List.prefix_iff_eq_take.mp hpref
  change (rho.events.filter p).foldlM (Record.worldStepOf M S) (fun v => M.initial S v) =
    (rho.events.take (rho.events.filter p).length).foldlM
      (Record.worldStepOf M S) (fun v => M.initial S v)
  exact congrArg (fun events => events.foldlM (Record.worldStepOf M S) (fun v => M.initial S v)) hpre

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel
open Execution

/-- In a run sorted by key, with `d ≤ read`, for every world `w₁` before time `d` and every world
    `w₂` the events from the first at or after `d` to the last before `read` lead to from `w₁`, the
    finalized block of `w`'s store in `w₁` is an ancestor of the one in `w₂`. -/
theorem Vocabulary.Proofs.stateBeforeTime_F_mono_of_le (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key))
    {w : V} {d read : Time} (hdr : d ≤ read) :
    ∀ w₁ ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho d,
    ∀ w₂ ∈ ((rho.events.drop (rho.events.filter (fun e => decide (e.time < d))).length).take
        ((rho.events.filter (fun e => decide (e.time < read))).length -
          (rho.events.filter (fun e => decide (e.time < d))).length)).foldlM
        (Record.worldStepOf M S) w₁,
    Block.Preceq (w₁ w).st.core.F (w₂ w).st.core.F := by
  intro w₁ hw₁
  have hnd := Restated.Vocabulary.Proofs.stateBeforeTime_eq_stateBefore_filter_length facts S rho hsorted d
  have hlen := Restated.strict_filter_length_mono rho hdr
  rw [hnd] at hw₁
  exact Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_F_mono facts S rho w hlen w₁ hw₁

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel
open Execution

/-- In a run sorted by key, with `i` at most the number of events before time `d`, for every world
    `w₁` before event `i` and every world `w₂` the events from `i` to the last before `d` lead to
    from `w₁`, the finalized block of `w`'s store in `w₁` is an ancestor of the one in `w₂`. -/
theorem Vocabulary.Proofs.stateBefore_F_preceq_stateBeforeTime_of_prefix (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key))
    {w : V} {d : Time} {i : Nat}
    (hi : i ≤ (rho.events.filter (fun e => decide (e.time < d))).length) :
    ∀ w₁ ∈ Record.stateBeforeOf M S rho i,
    ∀ w₂ ∈ ((rho.events.drop i).take
        ((rho.events.filter (fun e => decide (e.time < d))).length - i)).foldlM
        (Record.worldStepOf M S) w₁,
    Block.Preceq (w₁ w).st.core.F (w₂ w).st.core.F :=
  Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_F_mono facts S rho w hi

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel
open Execution

/-- In a run sorted by key, with `i` at most the number of events before time `d`, for every world
    `w₁` before event `i` and every world `w₂` the events from `i` to the last before `d` lead to
    from `w₁`, if the FG root of `w`'s store in `w₂` is an ancestor of `B`, then the finalized block
    of `w`'s store in `w₁` is an ancestor of `B`. -/
theorem Vocabulary.Proofs.finalized_preceq_at_prefix_of_storeBeforeRoot_preceq (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key))
    {w : V} {B : Block V} {d : Time}
    {i : Nat} (hi : i ≤
      (rho.events.filter (fun e => decide (e.time < d))).length) :
    ∀ w₁ ∈ Record.stateBeforeOf M S rho i,
    ∀ w₂ ∈ ((rho.events.drop i).take
        ((rho.events.filter (fun e => decide (e.time < d))).length - i)).foldlM
        (Record.worldStepOf M S) w₁,
    Block.Preceq (M.get_fg_root (M.toHealing (w₂ w).st.core).toFG) B →
    Block.Preceq (w₁ w).st.core.F B := by
  intro w₁ hw₁ w₂ hw₂ hroot
  have hmono := Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_F_mono facts S rho w hi
    w₁ hw₁ w₂ hw₂
  have hw₂t : w₂ ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho d := by
    rw [Restated.Vocabulary.Proofs.stateBeforeTime_eq_stateBefore_filter_length facts S rho hsorted d]
    exact er_mem_stateBeforeOf_of_path S rho hi hw₁ hw₂
  have hFJ := Restated.Vocabulary.Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime facts
    S rho d w w₂ hw₂t
  have hFJ' : Block.preceq
      (M.toHealing (w₂ w).st.core).toFG.F
      (M.toHealing (w₂ w).st.core).toFG.J = true := by
    rw [facts.sto.ModelProperties_toHealing_F, facts.sto.ModelProperties_toHealing_J,
      ModelProperties.preceq_eq_true_iff_Preceq]
    exact hFJ
  have hFroot := facts.fc.preceq_get_fg_root_of_F
    (st := (M.toHealing (w₂ w).st.core).toFG) hFJ'
  rw [ModelProperties.preceq_eq_true_iff_Preceq, facts.sto.ModelProperties_toHealing_F] at hFroot
  have hFtime : Block.Preceq (w₂ w).st.core.F B :=
    ModelProperties.Preceq_trans hFroot hroot
  exact ModelProperties.Preceq_trans hmono hFtime

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel
open Execution

/-- In a run sorted by key, with `d ≤ read`, for every world `w₁` before time `d` and every world
    `w₂` the events from the first at or after `d` to the last before `read` lead to from `w₁`, if
    the finalized block of `w`'s store in `w₂` is compatible with `B`, so is the finalized block of
    `w`'s store in `w₁`. -/
theorem Vocabulary.Proofs.not_excludes_of_compatible_later_time (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key))
    {w : V} {B : NamedBlock V} {d read : Time} (hdr : d ≤ read) :
    ∀ w₁ ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho d,
    ∀ w₂ ∈ ((rho.events.drop (rho.events.filter (fun e => decide (e.time < d))).length).take
        ((rho.events.filter (fun e => decide (e.time < read))).length -
          (rho.events.filter (fun e => decide (e.time < d))).length)).foldlM
        (Record.worldStepOf M S) w₁,
      Block.compatible (w₂ w).st.core.F B.erase = true →
      Block.compatible (w₁ w).st.core.F B.erase = true :=
  Restated.Vocabulary.Proofs.not_excludes_of_compatible_later facts S rho
    (Restated.Vocabulary.Proofs.stateBeforeTime_eq_stateBefore_filter_length facts S rho hsorted d)
    (Restated.strict_filter_length_mono rho hdr)

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel
open Execution

/-- In a run sorted by key, with `d ≤ read`, for every world `w₁` before time `d` and every world
    `w₂` the events from the first at or after `d` to the last before `read` lead to from `w₁`, if
    the finalized block of `w`'s store in `w₂` is an ancestor of `B`, then the finalized block of
    `w`'s store in `w₁` is compatible with `B`. -/
theorem Vocabulary.Proofs.not_excludes_of_F_preceq_later_time (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key))
    {w : V} {B : NamedBlock V} {d read : Time} (hdr : d ≤ read) :
    ∀ w₁ ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho d,
    ∀ w₂ ∈ ((rho.events.drop (rho.events.filter (fun e => decide (e.time < d))).length).take
        ((rho.events.filter (fun e => decide (e.time < read))).length -
          (rho.events.filter (fun e => decide (e.time < d))).length)).foldlM
        (Record.worldStepOf M S) w₁,
      Block.Preceq (w₂ w).st.core.F B.erase →
      Block.compatible (w₁ w).st.core.F B.erase = true := by
  intro w₁ hw₁ w₂ hw₂ hF
  exact Restated.Vocabulary.Proofs.not_excludes_of_compatible_later_time facts S rho hsorted hdr
    w₁ hw₁ w₂ hw₂ (ModelProperties.compatible_eq_true_of_Preceq hF)

end

end DecoupledConsensusModel.Sts.Restated
