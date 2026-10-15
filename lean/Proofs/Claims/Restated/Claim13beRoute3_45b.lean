import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13beRoute3_45
import Proofs.Claims.Restated.Vocabulary_Execution_BridgesCore
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_Blocks
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.RunVocabulary
import Model.Conditions.Vocabulary_Execution_Runtime
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Event
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedReceiptCalls
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Node
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Objects
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Protocol_ChainState_AlignedRoundLemmas
import Model.Conditions.Vocabulary_Protocol_Handlers_Blocks
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_45b

/-!
# Block stamps, block carry and admission along the bundle's path

Facts about the blocks of a validator's core store read along the path `W` the bundle
`AdmissibleFieldsOn` is read along: the store clock against event instants, the block-stamp bundle,
blocks kept with their stamps from one prefix to a later one, admission before a cutoff, and run
blocks behind core-tree blocks. Stated over a model `M : Record.Model V` and its facts
`facts : Record.Facts M`.
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
open DecoupledConsensusModel.Execution

omit [DecidableEq V] [Fintype V] in
/-- When the event at index `i` of `rho` is `e`, the events from index `i` to index `i` of `rho` are
    the list `[e]`. -/
private theorem drop_take_succ₄₅b {rho : Record.Run V} {i : Nat} {e : Record.Event V}
    (hi : rho.events[i]? = some e) : (rho.events.drop i).take (i + 1 - i) = [e] := by
  rw [Nat.add_sub_cancel_left, List.take_one, List.head?_drop, hi]
  rfl

omit [DecidableEq V] [Fintype V] in
/-- When `rho` has no event at index `i`, the events from index `i` to index `i` of `rho` are the
    empty list. -/
private theorem drop_take_succ_none₄₅b {rho : Record.Run V} {i : Nat}
    (hi : rho.events[i]? = none) : (rho.events.drop i).take (i + 1 - i) = [] := by
  rw [List.getElem?_eq_none_iff] at hi
  rw [List.drop_eq_nil_of_le hi]
  exact List.take_nil

omit [DecidableEq V] [Fintype V] in
/-- For `m ≤ j ≤ n`, the elements `m` to `n - 1` of a list are the elements `m` to `j - 1` followed
    by the elements `j` to `n - 1`. -/
private theorem slice_split₄₅b {α : Type} (l : List α) {m j n : Nat} (hmj : m ≤ j) (hjn : j ≤ n) :
    (l.drop m).take (n - m) = (l.drop m).take (j - m) ++ (l.drop j).take (n - j) := by
  have h : n - m = (j - m) + (n - j) := by omega
  rw [h, List.take_add, List.drop_drop, Nat.add_sub_cancel' hmj]

/-- The worlds the one-event list `[e]` leads to from `w` are the worlds
    `Record.worldStepOf M S w e`. -/
private theorem mem_foldlM_singleton₄₅b (S : Setup V) (w w₂ : V → M.N) (e : Record.Event V) :
    w₂ ∈ [e].foldlM (Record.worldStepOf M S) w ↔ w₂ ∈ Record.worldStepOf M S w e := by
  rw [List.foldlM_cons, Set.bind_def]
  constructor
  · intro h
    obtain ⟨w', hw', h2⟩ := Set.mem_iUnion₂.mp h
    obtain rfl := Set.mem_singleton_iff.mp h2
    exact hw'
  · intro h
    exact Set.mem_iUnion₂.mpr ⟨w₂, h, Set.mem_singleton w₂⟩

/-- A world the events `l₁ ++ l₂` lead to from `w` is one the events `l₂` lead to from a world the
    events `l₁` lead to from `w`, and conversely. -/
private theorem mem_foldlM_append₄₅b (S : Setup V) (l₁ l₂ : List (Record.Event V)) (w w₂ : V → M.N) :
    w₂ ∈ (l₁ ++ l₂).foldlM (Record.worldStepOf M S) w ↔
      ∃ w' ∈ l₁.foldlM (Record.worldStepOf M S) w,
        w₂ ∈ l₂.foldlM (Record.worldStepOf M S) w' := by
  rw [List.foldlM_append, Set.bind_def]
  constructor
  · intro h
    obtain ⟨w', hw', h2⟩ := Set.mem_iUnion₂.mp h
    exact ⟨w', hw', h2⟩
  · rintro ⟨w', hw', h2⟩
    exact Set.mem_iUnion₂.mpr ⟨w', hw', h2⟩

/-- For `i ≤ j`, a world `w₂` can hold before the `j`-th event of `rho` exactly when it is reached,
    by the events `i` to `j - 1` of `rho`, from a world that can hold before the `i`-th event. -/
private theorem mem_stateBeforeOf_split₄₅b (S : Setup V) (rho : Record.Run V) {i j : Nat}
    (hij : i ≤ j) (w₂ : V → M.N) :
    w₂ ∈ Record.stateBeforeOf M S rho j ↔
      ∃ w₁ ∈ Record.stateBeforeOf M S rho i,
        w₂ ∈ ((rho.events.drop i).take (j - i)).foldlM (Record.worldStepOf M S) w₁ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  unfold Record.stateBeforeOf
  rw [Nat.add_sub_cancel_left, List.take_add, List.foldlM_append, Set.bind_def]
  constructor
  · intro h
    obtain ⟨w₁, hw₁, h2⟩ := Set.mem_iUnion₂.mp h
    exact ⟨w₁, hw₁, h2⟩
  · rintro ⟨w₁, hw₁, h2⟩
    exact Set.mem_iUnion₂.mpr ⟨w₁, hw₁, h2⟩

/-- For `m ≤ j ≤ n`, a world the events `m` to `n - 1` of `rho` lead to from `w` is one the events
    `j` to `n - 1` lead to from a world the events `m` to `j - 1` lead to from `w`, and conversely. -/
private theorem mem_slice_split₄₅b (S : Setup V) (rho : Record.Run V) {m j n : Nat} (hmj : m ≤ j)
    (hjn : j ≤ n) (w w₂ : V → M.N) :
    w₂ ∈ ((rho.events.drop m).take (n - m)).foldlM (Record.worldStepOf M S) w ↔
      ∃ w' ∈ ((rho.events.drop m).take (j - m)).foldlM (Record.worldStepOf M S) w,
        w₂ ∈ ((rho.events.drop j).take (n - j)).foldlM (Record.worldStepOf M S) w' := by
  rw [slice_split₄₅b rho.events hmj hjn]
  exact mem_foldlM_append₄₅b S _ _ w w₂

/-- If `w₂` is reached from `w` by the events from index `n` to index `n` of `rho`, then either
    `rho` has no event at index `n` and `w₂` is `w`, or the `n`-th event is some `e` and `w₂` is one
    of the worlds `e` can lead to from `w`. -/
private theorem step_cases₄₅b (S : Setup V) (rho : Record.Run V) (n : Nat) (w w₂ : V → M.N)
    (h : w₂ ∈ ((rho.events.drop n).take (n + 1 - n)).foldlM (Record.worldStepOf M S) w) :
    (rho.events[n]? = none ∧ w₂ = w) ∨
      ∃ e, rho.events[n]? = some e ∧ w₂ ∈ Record.worldStepOf M S w e := by
  rcases hev : rho.events[n]? with _ | e
  · rw [drop_take_succ_none₄₅b hev] at h
    exact Or.inl ⟨rfl, Set.mem_singleton_iff.mp h⟩
  · rw [drop_take_succ₄₅b hev, mem_foldlM_singleton₄₅b] at h
    exact Or.inr ⟨e, rfl, h⟩

/-- For every path `W` of `rho`, `W (m + k)` is among the worlds the events `m` to `m + k - 1` of
    `rho` lead to from `W m`. -/
private theorem onePath_reach₄₅b {S : Setup V} {rho : Record.Run V}
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (m : Nat) :
    ∀ k : Nat, W (m + k) ∈ ((rho.events.drop m).take k).foldlM (Record.worldStepOf M S) (W m) := by
  intro k
  induction k with
  | zero => exact Set.mem_singleton _
  | succ k ih =>
    have hstep := (hW (m + k)).2
    rw [Nat.add_sub_cancel_left] at hstep
    rw [List.take_add, List.foldlM_append, Set.bind_def, List.drop_drop]
    refine Set.mem_iUnion₂.mpr ⟨W (m + k), ih, ?_⟩
    rw [← Nat.add_assoc]
    exact hstep

/-- For every path `W` of `rho` and `m ≤ n`, `W n` is among the worlds the events `m` to `n - 1` of
    `rho` lead to from `W m`. -/
private theorem onePath_reach_le₄₅b {S : Setup V} {rho : Record.Run V}
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    {m n : Nat} (hmn : m ≤ n) :
    W n ∈ ((rho.events.drop m).take (n - m)).foldlM (Record.worldStepOf M S) (W m) := by
  have h := onePath_reach₄₅b W hW m (n - m)
  rwa [Nat.add_sub_of_le hmn] at h

/-- For every path `W` of `rho`, if the event at index `n` is `e`, then `W (n + 1)` is one of the
    worlds `e` can lead to from `W n`. -/
private theorem onePath_step₄₅b {S : Setup V} {rho : Record.Run V}
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    {n : Nat} {e : Record.Event V} (he : rho.events[n]? = some e) :
    W (n + 1) ∈ Record.worldStepOf M S (W n) e := by
  have h := (hW n).2
  rw [drop_take_succ₄₅b he, mem_foldlM_singleton₄₅b] at h
  exact h

/-- If `w₂` is a world the event `e` can lead to from `w`, and the clock of `v`'s core store in `w`
    is at most the instant of `e`, then so is the clock of `v`'s core store in `w₂`. -/
private theorem step_clock₄₅b (facts : Record.Facts M) (S : Setup V) (v : V) (w w₂ : V → M.N)
    (e : Record.Event V) (hw₂ : w₂ ∈ Record.worldStepOf M S w e)
    (h : (w v).st.core.t ≤ e.time) : (w₂ v).st.core.t ≤ e.time := by
  cases e with
  | wake u t =>
    simp only [Record.worldStepOf, Set.mem_singleton_iff] at hw₂
    subst hw₂
    by_cases hv : v = u
    · subst hv
      rw [Function.update_self, (facts.nd.wake_st_record _).1]
      exact h
    · rw [Function.update_of_ne hv]
      exact h
  | tick u t =>
    simp only [Record.worldStepOf, Set.mem_setOf_eq] at hw₂
    rcases hw₂ with ⟨out, hout, rfl⟩ | ⟨-, rfl⟩
    · by_cases hv : v = u
      · subst hv
        rw [Function.update_self, (facts.nd.tick_clock S v (w v) t out hout).1]
        exact le_refl t
      · rw [Function.update_of_ne hv]
        exact h
    · exact h
  | deliver u o t =>
    simp only [Record.worldStepOf, Set.mem_setOf_eq] at hw₂
    rcases hw₂ with ⟨n', hn', rfl⟩ | ⟨-, rfl⟩
    · by_cases hv : v = u
      · subst hv
        rw [Function.update_self, (facts.nd.process_clock S (w v) o n' hn').1]
        exact h
      · rw [Function.update_of_ne hv]
        exact h
    · exact h

/-- If `w₂` is a world the event `e` can lead to from `w`, and the clock of `v`'s core store in `w`
    is at most the instant of `e` when `e` is a tick of `v`, then `v`'s core store goes from `w` to
    `w₂` by a block step. -/
private theorem step_block₄₅b (facts : Record.Facts M) (S : Setup V) (v : V) (w w₂ : V → M.N)
    (e : Record.Event V) (hw₂ : w₂ ∈ Record.worldStepOf M S w e)
    (hclock : ∀ t, e = .tick v t → (w v).st.core.t ≤ t) (hn : M.reachedNode (w v) := by trivial) :
    Restated.Vocabulary.Protocol.BlockStep M (w v).st.core (w₂ v).st.core := by
  cases e with
  | wake u t =>
    simp only [Record.worldStepOf, Set.mem_singleton_iff] at hw₂
    subst hw₂
    by_cases hv : v = u
    · subst hv
      rw [Function.update_self, (facts.nd.wake_st_record _).1]
      exact Restated.Vocabulary.Protocol.BlockStep.refl' facts _
    · rw [Function.update_of_ne hv]
      exact Restated.Vocabulary.Protocol.BlockStep.refl' facts _
  | tick u t =>
    simp only [Record.worldStepOf, Set.mem_setOf_eq] at hw₂
    rcases hw₂ with ⟨out, hout, rfl⟩ | ⟨-, rfl⟩
    · by_cases hv : v = u
      · subst hv
        rw [Function.update_self]
        intro h
        obtain ⟨⟨hmem, hstamp⟩, hs₁, hs₂, hs₃⟩ :=
          facts.ndRun.blockStep_tick S v (w v) t out hout (hclock t rfl)
            ⟨h.stamped, h.stored, h.bounded⟩
        exact ⟨⟨hmem, hstamp⟩, ⟨hs₁, hs₂, hs₃⟩⟩
      · rw [Function.update_of_ne hv]
        exact Restated.Vocabulary.Protocol.BlockStep.refl' facts _
    · exact Restated.Vocabulary.Protocol.BlockStep.refl' facts _
  | deliver u o t =>
    simp only [Record.worldStepOf, Set.mem_setOf_eq] at hw₂
    rcases hw₂ with ⟨n', hn', rfl⟩ | ⟨-, rfl⟩
    · by_cases hv : v = u
      · subst hv
        rw [Function.update_self]
        intro h
        obtain ⟨⟨hmem, hstamp⟩, hs₁, hs₂, hs₃⟩ :=
          facts.ndRun.blockStep_process S (w v) o n' hn' ⟨h.stamped, h.stored, h.bounded⟩
        exact ⟨⟨hmem, hstamp⟩, ⟨hs₁, hs₂, hs₃⟩⟩
      · rw [Function.update_of_ne hv]
        exact Restated.Vocabulary.Protocol.BlockStep.refl' facts _
    · exact Restated.Vocabulary.Protocol.BlockStep.refl' facts _

/-- Along a path `W` of `rho`, the named bodies `u` holds in `W i` contain genesis and the parent of
    each of them. -/
private theorem namedParentClosed_W₄₅b (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    (i : Nat) (u : V) :
    Restated.Vocabulary.Proofs.NamedStore.NamedParentClosed M (W i u).st :=
  (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho i u (W i)
    (hW i).1).1.1.1.2.2.1

/-- If the named bodies of `st` contain the parent of each of them, every named ancestor of a body
    of `st` is a body of `st`. -/
private theorem ancestor_body_mem₄₅b {st : M.NS}
    (hpc : Restated.Vocabulary.Proofs.NamedStore.NamedParentClosed M st) {A B : NamedBlock V}
    (hB : B ∈ st.bodies) (hAB : NamedBlock.Preceq A B) : A ∈ st.bodies := by
  revert hB hAB
  induction B with
  | genesis =>
    intro hB hAB
    simp only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] at hAB
    exact hAB ▸ hB
  | node parent s root votes support rows proposer ih =>
    intro hB hAB
    simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
      decide_eq_true_eq] at hAB
    rcases hAB with rfl | hparent
    · exact hB
    · have hp := hpc.2 _ hB
      rw [Proofs.ModelProperties.named_parent_node] at hp
      exact ih hp (by simp only [NamedBlock.Preceq]; exact hparent)

/-- Along a path `W` of `rho`, a named body `X` that `v` holds in `W i` and that includes the row
    `row` was processed by `v` at some instant, along `W`. -/
private theorem processes_of_mem_bodies₄₅b (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (v : V) (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    (i : Nat) {X : NamedBlock V} (hX : X ∈ (W i v).st.bodies)
    {row : NamedAttestation V} (hrow : row ∈ X.attestations) :
    ∃ t : Time, Restated.Vocabulary.Execution.NamedRun.processes M S rho W v (Object.block X) t := by
  rcases Restated.Vocabulary.Proofs.Bridges.processes_block_of_mem_T facts S rho v W hW i X hX with
    rfl | ⟨j, e, -, -, hproc⟩
  · rw [Proofs.ModelProperties.attestations_genesis] at hrow
    exact absurd hrow (by simp)
  · exact ⟨e.time, hproc⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- For the path `W` the bundle `AdmissibleFieldsOn` is read along, the core clock of `v`'s store in
    `W n` is at most the instant of the event at index `n`. -/
theorem block_store_time_le_event_timeOn (facts : Record.Facts M) (S : Setup V) {ρ : Record.Run V} (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S ρ W Hs Xb lo)
    {n : Nat} {e : Record.Event V}
    (he : ρ.events[n]? = some e) (v : V) :
    (W n v).st.core.t ≤ e.time :=
  Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_clock_le_event facts S ρ hf.sorted he
    (hf.in_horizon _ (List.mem_of_getElem? he)).1 v (W n) (hf.onePath n).1

/-- For the path `W` the bundle `AdmissibleFieldsOn` is read along, the core clock of `v`'s store in
    `W (n + 1)` is at most the instant of the event at index `n`. -/
theorem block_store_time_after_event_leOn (facts : Record.Facts M) (S : Setup V) {ρ : Record.Run V} (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S ρ W Hs Xb lo)
    {n : Nat} {e : Record.Event V}
    (he : ρ.events[n]? = some e) (v : V) :
    (W (n + 1) v).st.core.t ≤ e.time :=
  step_clock₄₅b facts S v (W n) (W (n + 1)) e (onePath_step₄₅b hf.onePath he)
    (Restated.block_store_time_le_event_timeOn facts S Hs Xb hf he v)

/-- Under the bundle `AdmissibleFieldsOn`, in every world before every event, `v`'s core store
    carries the block-stamp bundle. -/
private theorem blockStamps_all₄₅b (facts : Record.Facts M) (S : Setup V) {ρ : Record.Run V}
    {Hs : Int → Finset V} {Xb : Finset V} {lo : Int} {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S ρ W Hs Xb lo) (v : V) :
    ∀ n : Nat, ∀ w₁ ∈ Record.stateBeforeOf M S ρ n,
      Restated.Vocabulary.Protocol.BlockStamps M (w₁ v).st.core := by
  intro n
  induction n with
  | zero =>
    intro w₁ hw₁
    rw [Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_zero facts] at hw₁
    obtain rfl := Set.mem_singleton_iff.mp hw₁
    show Restated.Vocabulary.Protocol.BlockStamps M (M.initial S v : M.N).st.core
    rw [facts.nd.initial_st]
    obtain ⟨hs₁, hs₂, hs₃⟩ := facts.hd.blockStamps_init
    exact ⟨hs₁, hs₂, hs₃⟩
  | succ n ih =>
    intro w₁ hw₁
    obtain ⟨w, hw, hw₁'⟩ := (mem_stateBeforeOf_split₄₅b S ρ (Nat.le_succ n) w₁).mp hw₁
    rcases step_cases₄₅b S ρ n w w₁ hw₁' with ⟨-, hww⟩ | ⟨e, hev, hstep⟩
    · rw [hww]
      exact ih w hw
    · refine (step_block₄₅b facts S v w w₁ e hstep ?_
        (facts.ndRun.stateBeforeOf_reachedNode S ρ n w hw v) (ih w hw)).2
      intro t ht
      subst ht
      exact Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_clock_le_event facts S ρ hf.sorted hev
        (hf.in_horizon _ (List.mem_of_getElem? hev)).1 v w hw

/-- Under the bundle `AdmissibleFieldsOn`, for `m ≤ n`, every world `w₁` before event `m` and every
    world `w₂` the events `m` to `n - 1` lead to from `w₁`, a block in `v`'s core tree in `w₁` is in
    `v`'s core tree in `w₂`, with the stamp it had. -/
private theorem block_carry_all₄₅b (facts : Record.Facts M) (S : Setup V) {ρ : Record.Run V}
    {Hs : Int → Finset V} {Xb : Finset V} {lo : Int} {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S ρ W Hs Xb lo)
    (v : V) {m : Nat} : ∀ w₁ ∈ Record.stateBeforeOf M S ρ m, ∀ n : Nat, m ≤ n →
      ∀ w₂ ∈ ((ρ.events.drop m).take (n - m)).foldlM (Record.worldStepOf M S) w₁,
      Restated.Vocabulary.Protocol.BlockCarry M (w₁ v).st.core (w₂ v).st.core := by
  intro w₁ hw₁ n
  induction n with
  | zero =>
    intro hle w₂ hw₂
    rw [Nat.zero_sub, List.take_zero] at hw₂
    obtain rfl := Set.mem_singleton_iff.mp hw₂
    exact ⟨fun _ h => h, fun _ _ h => h⟩
  | succ n ih =>
    intro hle w₂ hw₂
    rcases Nat.lt_or_ge m (n + 1) with hlt | hge
    · have hmn : m ≤ n := Nat.lt_succ_iff.mp hlt
      obtain ⟨w', hw', hw₂'⟩ := (mem_slice_split₄₅b S ρ hmn (Nat.le_succ n) w₁ w₂).mp hw₂
      have hc1 := ih hmn w' hw'
      have hw'mem : w' ∈ Record.stateBeforeOf M S ρ n :=
        (mem_stateBeforeOf_split₄₅b S ρ hmn w').mpr ⟨w₁, hw₁, hw'⟩
      have hc2 : Restated.Vocabulary.Protocol.BlockCarry M (w' v).st.core (w₂ v).st.core := by
        rcases step_cases₄₅b S ρ n w' w₂ hw₂' with ⟨-, rfl⟩ | ⟨e, hev, hstep⟩
        · exact ⟨fun _ h => h, fun _ _ h => h⟩
        · refine (step_block₄₅b facts S v w' w₂ e hstep ?_
            (facts.ndRun.stateBeforeOf_reachedNode S ρ n w' hw'mem v)
            (blockStamps_all₄₅b facts S hf v n w' hw'mem)).1
          intro t ht
          subst ht
          exact Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_clock_le_event facts S ρ hf.sorted
            hev (hf.in_horizon _ (List.mem_of_getElem? hev)).1 v w' hw'mem
      exact ⟨fun B hB => hc2.mem B (hc1.mem B hB), fun B c hc => hc2.stamp B c (hc1.stamp B c hc)⟩
    · have hmn : m = n + 1 := Nat.le_antisymm hle hge
      subst hmn
      rw [Nat.sub_self, List.take_zero] at hw₂
      obtain rfl := Set.mem_singleton_iff.mp hw₂
      exact ⟨fun _ h => h, fun _ _ h => h⟩

/-- For the path `W` the bundle `AdmissibleFieldsOn` is read along and every `n`, `v`'s core store
    in `W n` carries the block-stamp bundle. -/
theorem blockStamps_stateBeforeOn (facts : Record.Facts M) (S : Setup V) {ρ : Record.Run V} (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S ρ W Hs Xb lo)
    (v : V) : ∀ n : Nat,
      Restated.Vocabulary.Protocol.BlockStamps M (W n v).st.core := fun n =>
  blockStamps_all₄₅b facts S hf v n (W n) (hf.onePath n).1

/-- For the path `W` the bundle `AdmissibleFieldsOn` is read along and `m ≤ n`, a block in `v`'s
    core tree in `W m` is in `v`'s core tree in `W n`, with the stamp it had. -/
theorem block_carryOn (facts : Record.Facts M) (S : Setup V) {ρ : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V)
    {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S ρ W Hs Xb lo)
    (v : V) {m : Nat} : ∀ n : Nat, m ≤ n →
      Restated.Vocabulary.Protocol.BlockCarry M (W m v).st.core (W n v).st.core := fun n hmn =>
  block_carry_all₄₅b facts S hf v (W m) (hf.onePath m).1 n hmn (W n)
    (onePath_reach_le₄₅b hf.onePath hmn)

/-- If `v` admitted `B` before `Γ` along the path `W` the bundle `AdmissibleFieldsOn` is read along,
    then `B` is in the tree of `v`'s core store in `W (strictEventIndex ρ Γ)` and stamped there
    before `Γ`. -/
theorem admittedBefore_mem_and_stampOn (facts : Record.Facts M) (S : Setup V) {ρ : Record.Run V} (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S ρ W Hs Xb lo)
    {v : V} {B : Block V} {Γ : Time}
    (hadmit : Restated.Vocabulary.Protocol.AdmittedBefore M S ρ W v B Γ) :
    B ∈ (W (strictEventIndex ρ Γ) v).st.core.T ∧
      stampedBefore (W (strictEventIndex ρ Γ) v).st.core.timestamp_block Γ B = true := by
  have hW := hf.onePath
  obtain ⟨C, hCB, i, t, hacc, hlt⟩ := hadmit
  subst hCB
  obtain ⟨⟨hidx, e, he, -, het⟩, hpre, hpost⟩ := hacc
  have hpreB : C ∉ (W i v).st.bodies := by
    simpa only [Restated.Vocabulary.Execution.Object.processed, decide_eq_false_iff_not] using hpre
  have hpostB : C ∈ (W (i + 1) v).st.bodies := by
    simpa only [Restated.Vocabulary.Execution.Object.processed, decide_eq_true_eq] using hpost
  have hstepW : W (i + 1) ∈ Record.worldStepOf M S (W i) e := by
    have h := (hW i).2
    rw [drop_take_succ₄₅b he, mem_foldlM_singleton₄₅b] at h
    exact h
  have hidx' : Restated.Vocabulary.Execution.NamedRun.processesAtIndexAlong M S ρ W i v
      (Object.block C) := hidx
  obtain ⟨c, hc, hct⟩ : ∃ c : Stamp,
      (W (i + 1) v).st.core.timestamp_block C.erase = some c ∧ c ≤ (t : Stamp) := by
    rcases hidx' with ⟨t', htick, out, hout, hWout, -⟩ | ⟨t', hdeliver⟩
    · rw [htick] at he
      have hee := Option.some.inj he
      subst hee
      have ht' : t' = t := het
      subst ht'
      rw [hWout] at hpostB ⊢
      exact ⟨(t' : Stamp), facts.nd.node_tick_body_stamp S v (W i v) t' out hout C hpreB hpostB,
        le_refl _⟩
    · have hclk := Restated.block_store_time_le_event_timeOn facts S Hs Xb hf hdeliver v
      rw [hdeliver] at he
      have hee := Option.some.inj he
      subst hee
      have ht' : t' = t := het
      subst ht'
      simp only [Record.worldStepOf, Set.mem_setOf_eq] at hstepW
      rcases hstepW with ⟨n', hn', hWeq⟩ | ⟨-, hWeq⟩
      · have hv : W (i + 1) v = n' := by rw [hWeq, Function.update_self]
        rw [hv] at hpostB ⊢
        exact ⟨(((W i v).st.core.t : Int) : Stamp),
          facts.nd.node_process_body_stamp S (W i v) _ n' hn' C hpreB hpostB,
          WithBot.coe_le_coe.mpr hclk⟩
      · rw [hWeq] at hpostB
        exact absurd hpostB hpreB
  have hiN : i < strictEventIndex ρ Γ := by
    by_contra hnot
    have hNle : (ρ.events.filter (fun x => decide (x.time < Γ))).length ≤ i :=
      Nat.le_of_not_gt hnot
    have hΓe : Γ ≤ e.time :=
      Restated.le_time_of_index_geOn facts S Hs Xb hf (t := Γ) (j := i) (e := e) hNle he
    rw [het] at hΓe
    exact (not_le_of_gt hlt) hΓe
  have hcarry := Restated.block_carryOn facts S Hs Xb hf v (m := i + 1)
    (strictEventIndex ρ Γ) (Nat.succ_le_of_lt hiN)
  have hsource := Restated.blockStamps_stateBeforeOn facts S Hs Xb hf v (i + 1)
  have hmemT : C.erase ∈ (W (i + 1) v).st.core.T := hsource.stored C.erase (by rw [hc]; rfl)
  have hcfinal := hcarry.stamp C.erase c hc
  have hcΓ : c < (Γ : Stamp) := lt_of_le_of_lt hct (WithBot.coe_lt_coe.mpr hlt)
  exact ⟨hcarry.mem C.erase hmemT, stampedBefore_of_lt hcfinal hcΓ⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead
local macro "sb% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Vocabulary.Protocol.Handlers.StoreBridge)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.NamedStoreBridge ++ n.getId)))

/-- For every path `W` of `rho`, if `v ∈ Xb` has `B` in its core tree in `W i`, some run block read
    through `Xb` along `W` erases to `B`. -/
theorem runBlock_of_mem_core_TOn (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    (Xb : Finset V) {v : V}
    (hv : v ∈ Xb) (i : Nat) {B : Block V} (hB : B ∈ (W i v).st.core.T) :
    ∃ D : NamedBlock V, D.erase = B ∧ Restated.RunBlockOn M S rho W Xb D := by
  obtain ⟨D, hD, hDB⟩ :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore facts S rho i v (W i)
      (hW i).1 hB
  exact ⟨D, hDB, Restated.runBlock_of_stateBefore_memOn facts S W Xb hv hD⟩

/-- For the path `W` the bundle `AdmissibleFieldsOn` is read along, if `v ∈ Xb` has `B` in its core
    tree in `W (strictEventIndex rho t)`, some run block read through `Xb` along `W` erases to `B`. -/
theorem runBlock_of_mem_core_T_stateBeforeTimeOn (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    (Hs : Int → Finset V) (Xb : Finset V) {lo : Int} {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} (hv : v ∈ Xb) (t : Time)
    {B : Block V} (hB : B ∈ (W (strictEventIndex rho t) v).st.core.T) :
    ∃ D : NamedBlock V, D.erase = B ∧ Restated.RunBlockOn M S rho W Xb D :=
  Restated.runBlock_of_mem_core_TOn facts S rho W hf.onePath Xb hv _ hB

/-- If `B` is a run block read through `Xb` along the path `W` the bundle `AdmissibleFieldsOn` is
    read along, `X ⪯ B` and `X` includes the row `row`, then some validator processed `X` along `W`
    at some instant. -/
theorem processes_of_runBlockOn (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {B : NamedBlock V} (hB : Restated.RunBlockOn M S rho W Xb B)
    {X : NamedBlock V} (hXB : NamedBlock.Preceq X B)
    {row : NamedAttestation V} (hrow : row ∈ X.attestations) :
    ∃ (u : V) (t : Time), Restated.Vocabulary.Execution.Run.processes M S rho W u (Object.block X) t := by
  have hW := hf.onePath
  obtain ⟨C, hC, hBC⟩ := hB
  have hXC : NamedBlock.Preceq X C := (sb% preceq_trans) hXB hBC
  rcases hC with hobj | ⟨w, -, i, hmem⟩
  · obtain ⟨i, u, t, hev⟩ := Restated.exists_deliver_of_mem_objects rho hobj
    rcases (sb% preceq_cases) hXC with rfl | hparent
    · exact ⟨u, t, Or.inr ⟨i, hev⟩⟩
    · have hpar : C.parent ∈ (W i u).st.bodies := hf.deps i u (Object.block C) t hev C rfl
      have hXmem : X ∈ (W i u).st.bodies :=
        ancestor_body_mem₄₅b (namedParentClosed_W₄₅b facts S rho W hW i u) hpar hparent
      obtain ⟨t', hproc⟩ := processes_of_mem_bodies₄₅b facts S rho u W hW i hXmem hrow
      exact ⟨u, t', hproc⟩
  · have hXmem : X ∈ (W i w).st.bodies :=
      ancestor_body_mem₄₅b (namedParentClosed_W₄₅b facts S rho W hW i w) hmem hXC
    obtain ⟨t', hproc⟩ := processes_of_mem_bodies₄₅b facts S rho w W hW i hXmem hrow
    exact ⟨w, t', hproc⟩

/-- If the family shrinks as time grows and `B` is a run block read through `Xb` along the path `W`
    the bundle `AdmissibleFieldsOn` is read along, every attestation on `B`'s chain signed by a
    member of the set for the horizon was emitted by its signer along `W`. -/
theorem carriedByHonest_of_runBlockOn (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    {B : NamedBlock V} (hB : Restated.RunBlockOn M S rho W Xb B) :
    Restated.Vocabulary.Proofs.AlignedRoundLemmas.CarriedByHonest M S rho W (Hs rho.horizon)
      (M.chain_attestations B.erase) := by
  intro a ha hah
  obtain ⟨X, hXB, row, hrow, rfl⟩ := facts.ev.named_mem_chain_attestations_of_erase B ha
  obtain ⟨u, t, hproc⟩ := Restated.processes_of_runBlockOn facts S Hs Xb hf hB hXB hrow
  have hthor : t ≤ rho.horizon := by
    rcases hproc with ⟨i, hi, -⟩ | ⟨i, hi⟩
    · exact (hf.in_horizon _ (List.mem_of_getElem? hi)).2
    · exact (hf.in_horizon _ (List.mem_of_getElem? hi)).2
  obtain ⟨t', -, hem⟩ := hf.carried_attest u X t hproc row hrow
    (hHs _ _ hthor (by rw [← namedAttestation_erase_val_index row]; exact hah))
  exact ⟨row, t', rfl, by rw [namedAttestation_erase_val_index]; exact hem⟩

end

end DecoupledConsensusModel.Sts.Restated
