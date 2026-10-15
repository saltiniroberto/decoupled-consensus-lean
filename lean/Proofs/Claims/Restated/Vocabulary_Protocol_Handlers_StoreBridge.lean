import Proofs.Vocabulary.Protocol.Handlers.StoreBridge
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Execution_BridgesCore
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_MaximumCarrier
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_NumericStore
import Proofs.Vocabulary.Protocol.Schedule.NamedTick
import Model.Conditions.Vocabulary_Execution_Runtime
import Model.Conditions.Vocabulary_Internal_Invariants
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ValidatorVoteSafety
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Protocol_ChainState_AlignedRoundLemmas
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreBridge
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_Schedule_Alignment
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring

/-!
# Store invariants along a run

Facts that hold of a validator's store in every world of a run: the finalized and justified blocks
are in the tree, the tree is parent-closed and made of named bodies, the finalized block is an
ancestor of the justified block, heights are bounded by `h_max` and `h_max` is attained by a body,
the store's slot is its clock's slot, and facts about its attestation rows, stated over a model
`M : Record.Model V`.
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
open DecoupledConsensusModel.Proofs.NamedStoreBridge
open Internal
open Execution

private theorem coherent_of_inv' {S : Setup V} {n : M.N}
    (h : Restated.Vocabulary.Proofs.NamedRuntime.NodeInvariant M S n) :
    Restated.Vocabulary.Proofs.NamedStore.Coherent M S.E S.cfg n.st := h.1.1.1

private theorem treeView_of_inv' {S : Setup V} {n : M.N}
    (h : Restated.Vocabulary.Proofs.NamedRuntime.NodeInvariant M S n) :
    n.st.core.T = n.st.bodies.image NamedBlock.erase := (coherent_of_inv' h).1

private theorem namedParentClosed_of_inv' {S : Setup V} {n : M.N}
    (h : Restated.Vocabulary.Proofs.NamedRuntime.NodeInvariant M S n) :
    Restated.Vocabulary.Proofs.NamedStore.NamedParentClosed M n.st :=
  (coherent_of_inv' h).2.2.1

private theorem exists_named_of_inv' {S : Setup V} {n : M.N}
    (h : Restated.Vocabulary.Proofs.NamedRuntime.NodeInvariant M S n) {B : Block V}
    (hB : B ∈ n.st.core.T) : ∃ D ∈ n.st.bodies, D.erase = B := by
  rw [treeView_of_inv' h] at hB
  obtain ⟨D, hD, hDB⟩ := Finset.mem_image.mp hB
  exact ⟨D, hD, hDB⟩

private theorem parentClosed_of_inv' (facts : Record.Facts M) {S : Setup V} {n : M.N}
    (h : Restated.Vocabulary.Proofs.NamedRuntime.NodeInvariant M S n) :
    Restated.Vocabulary.Internal.ParentClosed M n.st.core := by
  have hTree := treeView_of_inv' h
  have hpc := namedParentClosed_of_inv' h
  unfold Restated.Vocabulary.Internal.ParentClosed Record.Model.GS.parent_closed
  rw [facts.sto.toHealing_T]
  constructor
  · rw [hTree, ← Proofs.ModelProperties.erase_genesis]
    exact Finset.mem_image_of_mem NamedBlock.erase hpc.1
  · intro B hB
    refine Or.inr ?_
    rw [hTree] at hB ⊢
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hB
    rw [Proofs.NamedWire.erase_parent]
    exact Finset.mem_image_of_mem NamedBlock.erase (hpc.2 D hD)

private theorem ancestor_body_mem' {st : M.NS}
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

private theorem processes_of_mem_bodies' (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (v : V) (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    (i : Nat) {X : NamedBlock V} (hX : X ∈ (W i v).st.bodies)
    {row : NamedAttestation V} (hrow : row ∈ X.attestations) :
    ∃ t : Time, Restated.Vocabulary.Execution.NamedRun.processes M S rho W v (Object.block X) t := by
  rcases Restated.Vocabulary.Proofs.Bridges.processes_block_of_mem_T facts S rho v W hW i X hX with
    rfl | ⟨j, e, -, -, hproc⟩
  · rw [Proofs.ModelProperties.attestations_genesis] at hrow
    exact absurd hrow (by simp)
  · exact ⟨e.time, hproc⟩

/-- If a wake, every tick outcome and every receipt outcome keep the node-state predicate `P`, then
    from a world where every validator satisfies `P`, every world the events `l` can lead to has
    every validator satisfying `P`. -/
private theorem fold_pred' (S : Setup V) (P : M.N → Prop)
    (hwake : ∀ n : M.N, P n → P (M.wake n))
    (htick : ∀ (v : V) (n : M.N) (t : Time) (out : M.N × List (NamedObject V)),
      P n → M.tick S v n t ⇢ out → P out.1)
    (hproc : ∀ (n : M.N) (o : NamedObject V) (n' : M.N), P n → M.process S n o ⇢ n' → P n') :
    ∀ (l : List (Record.Event V)) (w : V → M.N), (∀ v, P (w v)) →
      ∀ w₂ ∈ l.foldlM (Record.worldStepOf M S) w, ∀ v, P (w₂ v) := by
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
    refine ih w' ?_ w₂ hw₂'
    intro v
    cases e with
    | wake u t =>
      simp only [Record.worldStepOf, Set.mem_singleton_iff] at hw'
      subst hw'
      by_cases hv : v = u
      · subst hv
        rw [Function.update_self]
        exact hwake (w v) (h v)
      · rw [Function.update_of_ne hv]
        exact h v
    | tick u t =>
      simp only [Record.worldStepOf, Set.mem_setOf_eq] at hw'
      rcases hw' with ⟨out, hout, rfl⟩ | ⟨-, rfl⟩
      · by_cases hv : v = u
        · subst hv
          rw [Function.update_self]
          exact htick v (w v) t out (h v) hout
        · rw [Function.update_of_ne hv]
          exact h v
      · exact h v
    | deliver u o t =>
      simp only [Record.worldStepOf, Set.mem_setOf_eq] at hw'
      rcases hw' with ⟨n', hn', rfl⟩ | ⟨-, rfl⟩
      · by_cases hv : v = u
        · subst hv
          rw [Function.update_self]
          exact hproc (w v) o n' (h v) hn'
        · rw [Function.update_of_ne hv]
          exact h v
      · exact h v

private theorem slotOfClock_fold' (facts : Record.Facts M) (S : Setup V)
    (l : List (Record.Event V)) :
    ∀ w₂ ∈ l.foldlM (Record.worldStepOf M S) (fun v => M.initial S v), ∀ v,
      Restated.Vocabulary.Proofs.Optimistic.SlotOfClock M S.E (w₂ v).st.core :=
  fold_pred' S (fun n => Restated.Vocabulary.Proofs.Optimistic.SlotOfClock M S.E n.st.core)
    (fun n h => by simpa only [(facts.nd.wake_st_record n).1] using h)
    (fun v n t out h hout => by
      unfold Restated.Vocabulary.Proofs.Optimistic.SlotOfClock
      rw [(facts.nd.tick_clock S v n t out hout).1]
      exact (facts.nd.tick_clock S v n t out hout).2)
    (fun n o n' h hn' => by
      unfold Restated.Vocabulary.Proofs.Optimistic.SlotOfClock at h ⊢
      rw [(facts.nd.process_clock S n o n' hn').1, (facts.nd.process_clock S n o n' hn').2]
      exact h)
    l (fun v => M.initial S v)
    (fun _ => by
      unfold Restated.Vocabulary.Proofs.Optimistic.SlotOfClock
      rw [facts.nd.initial_st, facts.hd.initial_core_s, facts.hd.initial_core_t,
        Proofs.ModelProperties.slotOf_zero])

private theorem order_fold' (facts : Record.Facts M) (S : Setup V)
    (l : List (Record.Event V)) :
    ∀ w₂ ∈ l.foldlM (Record.worldStepOf M S) (fun v => M.initial S v), ∀ v,
      Block.Preceq (w₂ v).st.core.F (w₂ v).st.core.J :=
  fold_pred' S (fun n => Block.Preceq n.st.core.F n.st.core.J)
    (fun n h => by simpa only [(facts.nd.wake_st_record n).1] using h)
    (fun v n t out h hout => facts.nd.frozen_tick_preceq S v n t h out hout)
    (fun n o n' h hn' => facts.nd.frozen_process_preceq S n o h n' hn')
    l (fun v => M.initial S v)
    (fun v => by
      show Block.Preceq (M.initial S v : M.N).st.core.F (M.initial S v : M.N).st.core.J
      rw [facts.nd.initial_st, facts.hd.initial_core_F, facts.hd.initial_core_J]
      exact Proofs.ModelProperties.Preceq_self (Block.genesis : Block V))

/-- In every world before the `i`-th event of `rho`, the finalized block of `v`'s store is in its
    tree. -/
theorem Vocabulary.Proofs.NamedStoreBridge.finalizedInTree_stateBefore (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (i : Nat) (v : V) : ∀ w₁ ∈ Record.stateBeforeOf M S rho i,
    ((w₁ v)).st.core.F ∈ ((w₁ v)).st.core.T := fun w₁ hw₁ =>
  (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho i v w₁ hw₁).1.1.2.1

/-- In every world after the events of `rho` before time `t`, the finalized block of `v`'s store is
    in its tree. -/
theorem Vocabulary.Proofs.NamedStoreBridge.finalizedInTree_stateBeforeTime (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (t : Time) (v : V) : ∀ w₁ ∈ Restated.Vocabulary.Execution.Run.stateBeforeTime M S rho t,
    ((w₁ v)).st.core.F ∈ ((w₁ v)).st.core.T := fun w₁ hw₁ =>
  (Restated.Vocabulary.Proofs.NamedRuntime.stateBeforeTime_invariants facts S rho t v w₁ hw₁).1.1.2.1

/-- In every world after the events of `rho` before time `t`, the justified block of `v`'s store is
    in its tree. -/
theorem Vocabulary.Proofs.NamedStoreBridge.justifiedInTree_stateBeforeTime (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (t : Time) (v : V) : ∀ w₁ ∈ Restated.Vocabulary.Execution.Run.stateBeforeTime M S rho t,
    ((w₁ v)).st.core.J ∈ ((w₁ v)).st.core.T := fun w₁ hw₁ =>
  (Restated.Vocabulary.Proofs.NamedRuntime.stateBeforeTime_invariants facts S rho t v w₁ hw₁).1.1.2.2

/-- In every world before the `i`-th event of `rho`, every block of the tree of `v`'s store is the
    erasure of a named body `v`'s store holds. -/
theorem Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (i : Nat) (v : V) :
    ∀ w₁ ∈ Record.stateBeforeOf M S rho i, ∀ {B : Block V}, B ∈ (w₁ v).st.core.T →
    ∃ D ∈ (w₁ v).st.bodies, D.erase = B := fun w₁ hw₁ _ hB =>
  exists_named_of_inv' (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho i v w₁ hw₁) hB

/-- In every world after the events of `rho` before time `t`, every block of the tree of `v`'s store
    is the erasure of a named body `v`'s store holds. -/
theorem Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (t : Time) (v : V) :
    ∀ w₁ ∈ Restated.Vocabulary.Execution.Run.stateBeforeTime M S rho t, ∀ {B : Block V},
    B ∈ (w₁ v).st.core.T → ∃ D ∈ (w₁ v).st.bodies, D.erase = B := fun w₁ hw₁ _ hB =>
  exists_named_of_inv' (Restated.Vocabulary.Proofs.NamedRuntime.stateBeforeTime_invariants facts S rho t v w₁ hw₁) hB

/-- In every world after the events of `rho` at or before time `t`, every block of the tree of `v`'s
    store is the erasure of a named body `v`'s store holds. -/
theorem Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_readAt (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (t : Time) (v : V) :
    ∀ w₁ ∈ Restated.Vocabulary.Execution.Run.readAt M S rho t, ∀ {B : Block V},
    B ∈ (w₁ v).st.core.T → ∃ D ∈ (w₁ v).st.bodies, D.erase = B := fun w₁ hw₁ _ hB =>
  exists_named_of_inv' (Restated.Vocabulary.Proofs.NamedRuntime.readAt_invariants facts S rho t v w₁ hw₁) hB

/-- In every world of `rho` at time `t`, every block of the tree of `v`'s store is the erasure of a
    named body `v`'s store holds. -/
theorem Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateAt (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (t : Time) (v : V) :
    ∀ w₁ ∈ Restated.Vocabulary.Execution.Run.stateAt M S rho t, ∀ {B : Block V},
    B ∈ (w₁ v).st.core.T → ∃ D ∈ (w₁ v).st.bodies, D.erase = B :=
  Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_readAt facts S rho t v

/-- In every world before the `i`-th event of `rho`, the tree of `v`'s store is parent closed. -/
theorem Vocabulary.Proofs.NamedStoreBridge.parentClosed_stateBefore (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (i : Nat) (v : V) : ∀ w₁ ∈ Record.stateBeforeOf M S rho i,
    Restated.Vocabulary.Internal.ParentClosed M ((w₁ v)).st.core := fun w₁ hw₁ =>
  parentClosed_of_inv' facts (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho i v w₁ hw₁)

/-- In every world after the events of `rho` before time `t`, the tree of `v`'s store is parent
    closed. -/
theorem Vocabulary.Proofs.NamedStoreBridge.parentClosed_stateBeforeTime (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (t : Time) (v : V) : ∀ w₁ ∈ Restated.Vocabulary.Execution.Run.stateBeforeTime M S rho t,
    Restated.Vocabulary.Internal.ParentClosed M ((w₁ v)).st.core := fun w₁ hw₁ =>
  parentClosed_of_inv' facts (Restated.Vocabulary.Proofs.NamedRuntime.stateBeforeTime_invariants facts S rho t v w₁ hw₁)

/-- In every world after the events of `rho` at or before time `t`, the tree of `v`'s store is
    parent closed. -/
theorem Vocabulary.Proofs.NamedStoreBridge.parentClosed_readAt (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (t : Time) (v : V) :
    ∀ w₁ ∈ Restated.Vocabulary.Execution.Run.readAt M S rho t,
    Restated.Vocabulary.Internal.ParentClosed M (w₁ v).st.core := fun w₁ hw₁ =>
  parentClosed_of_inv' facts (Restated.Vocabulary.Proofs.NamedRuntime.readAt_invariants facts S rho t v w₁ hw₁)

/-- In every world of `rho` at time `t`, the tree of `v`'s store is parent closed. -/
theorem Vocabulary.Proofs.NamedStoreBridge.parentClosed_stateAt (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (t : Time) (v : V) :
    ∀ w₁ ∈ Restated.Vocabulary.Execution.Run.stateAt M S rho t,
    Restated.Vocabulary.Internal.ParentClosed M (w₁ v).st.core :=
  Restated.Vocabulary.Proofs.NamedStoreBridge.parentClosed_readAt facts S rho t v

/-- For every path `W` of `rho` along which carried attestations are authentic, every attestation of
    `v`'s store in `W i` that names an honest validator is the erasure of a row that validator
    emits, along `W`, at some time. -/
theorem Vocabulary.Proofs.NamedStoreBridge.carriedByHonest_of_stateBefore (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    (auth : Restated.Vocabulary.Internal.AttestationAuthenticity M S rho W) (v : V) (i : Nat) :
    Restated.Vocabulary.Proofs.AlignedRoundLemmas.CarriedByHonest M S rho W rho.honest
      (M.store_attestations (W i v).st.core) := by
  intro a ha hah
  have hinv := Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho i v (W i)
    (hW i).1
  obtain ⟨B, hB, haB⟩ := (facts.ev.mem_store_attestations_iff _ a).mp ha
  obtain ⟨D, hD, rfl⟩ := exists_named_of_inv' hinv hB
  obtain ⟨X, hXD, row, hrow, rfl⟩ := facts.ev.named_mem_chain_attestations_of_erase D haB
  have hX : X ∈ (W i v).st.bodies := ancestor_body_mem' (namedParentClosed_of_inv' hinv) hD hXD
  obtain ⟨t, hproc⟩ := processes_of_mem_bodies' facts S rho v W hW i hX hrow
  rw [Proofs.ModelProperties.erase_val_index] at hah ⊢
  obtain ⟨t', -, hem⟩ := auth.carriedAttest v X t hproc row hrow hah
  exact ⟨row, t', rfl, hem⟩

/-- In every world before the `i`-th event of `rho`, every row `v`'s store holds in bucket `r` names
    round `r`. -/
theorem Vocabulary.Proofs.NamedStoreBridge.sgRowRounds_stateBefore (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (i : Nat) (v : V) : ∀ w₁ ∈ Record.stateBeforeOf M S rho i,
    Restated.Vocabulary.Proofs.NamedStoreBridge.SgRowRounds M ((w₁ v)).st := fun w₁ hw₁ r row hrow =>
  facts.stoRun.row_round_stateBefore S rho i v r row w₁ hw₁ hrow

/-- In every world after the events of `rho` before time `t`, every row `v`'s store holds in bucket
    `r` names round `r`. -/
theorem Vocabulary.Proofs.NamedStoreBridge.sgRowRounds_stateBeforeTime (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (t : Time) (v : V) : ∀ w₁ ∈ Restated.Vocabulary.Execution.Run.stateBeforeTime M S rho t,
    Restated.Vocabulary.Proofs.NamedStoreBridge.SgRowRounds M ((w₁ v)).st := fun w₁ hw₁ =>
  facts.hdRun.sgRowRounds_stateBeforeTime S rho t v w₁ hw₁

/-- In every world before the `i`-th event of `rho`, every attestation `v`'s store holds in its
    attestation set of round `r` names round `r`. -/
theorem Vocabulary.Proofs.NamedStoreBridge.sgRounds_stateBefore (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (i : Nat) (v : V) : ∀ w₁ ∈ Record.stateBeforeOf M S rho i,
    Restated.Vocabulary.Proofs.Optimistic.SgRounds M ((w₁ v)).st.core := by
  intro w₁ hw₁ r a ha
  have hp := (coherent_of_inv' (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho i v w₁ hw₁)).2.2.2.1
  rw [hp r, List.mem_map] at ha
  obtain ⟨row, hrow, rfl⟩ := ha
  rw [Proofs.ModelProperties.erase_round]
  exact Restated.Vocabulary.Proofs.NamedStoreBridge.sgRowRounds_stateBefore facts S rho i v w₁ hw₁ r row hrow

/-- In every world before the `i`-th event of `rho`, the slot of `v`'s store is the slot of its
    clock. -/
theorem Vocabulary.Proofs.NamedStoreBridge.slotOfClock_stateBefore (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (i : Nat) (v : V) : ∀ w₁ ∈ Record.stateBeforeOf M S rho i,
    Restated.Vocabulary.Proofs.Optimistic.SlotOfClock M S.E ((w₁ v)).st.core := fun w₁ hw₁ =>
  slotOfClock_fold' facts S (rho.events.take i) w₁ hw₁ v

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedStoreBridge
open Internal
open Execution
open Protocol (ChainState derive_named)

/-- In every world before the `i`-th event of `rho`, the finalized block of `v`'s store is an
    ancestor of, or is, its justified block. -/
theorem Vocabulary.Proofs.NamedStoreBridge.finalized_preceq_justified_stateBefore (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (i : Nat) (v : V) : ∀ w₁ ∈ Record.stateBeforeOf M S rho i,
    Block.Preceq ((w₁ v)).st.core.F ((w₁ v)).st.core.J := fun w₁ hw₁ =>
  order_fold' facts S (rho.events.take i) w₁ hw₁ v

/-- In every world after the events of `rho` before time `t`, the finalized block of `v`'s store is
    an ancestor of, or is, its justified block. -/
theorem Vocabulary.Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (t : Time) (v : V) : ∀ w₁ ∈ Restated.Vocabulary.Execution.Run.stateBeforeTime M S rho t,
    Block.Preceq ((w₁ v)).st.core.F ((w₁ v)).st.core.J := fun w₁ hw₁ =>
  order_fold' facts S _ w₁ hw₁ v

/-- In every world before the `i`-th event of `rho`, some named body `v`'s store holds has the
    height of its derived chain state equal to the store's `h_max`. -/
theorem Vocabulary.Proofs.NamedStoreBridge.maximum_carrier_stateBefore (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (i : Nat) (v : V) :
    ∀ w₁ ∈ Record.stateBeforeOf M S rho i, ∃ D ∈ (w₁ v).st.bodies,
      (M.derive_named S.E S.cfg D).h = (w₁ v).st.core.h_max :=
  Restated.Vocabulary.Proofs.NamedMaximumCarrier.maximum_carrier_stateBefore facts S rho i v

/-- In every world after the events of `rho` before time `t`, some named body `v`'s store holds has
    the height of its derived chain state equal to the store's `h_max`. -/
theorem Vocabulary.Proofs.NamedStoreBridge.maximum_carrier_stateBeforeTime (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (t : Time) (v : V) :
    ∀ w₁ ∈ Restated.Vocabulary.Execution.Run.stateBeforeTime M S rho t, ∃ D ∈ (w₁ v).st.bodies,
      (M.derive_named S.E S.cfg D).h = (w₁ v).st.core.h_max :=
  Restated.Vocabulary.Proofs.NamedMaximumCarrier.maximum_carrier_stateBeforeTime facts S rho t v

/-- In every world before the `i`-th event of `rho`, every named body `v`'s store holds has a
    derived height at most the store's `h_max`. -/
theorem Vocabulary.Proofs.NamedStoreBridge.heights_le_hMax_stateBefore (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (i : Nat) (v : V) :
    ∀ w₁ ∈ Record.stateBeforeOf M S rho i, ∀ D ∈ (w₁ v).st.bodies,
      (M.derive_named S.E S.cfg D).h ≤ (w₁ v).st.core.h_max :=
  Restated.Vocabulary.Proofs.NamedNumericStore.heights_bounded_stateBefore facts S rho i v

/-- In every world after the events of `rho` before time `t`, every named body `v`'s store holds has
    a derived height at most the store's `h_max`. -/
theorem Vocabulary.Proofs.NamedStoreBridge.heights_le_hMax_stateBeforeTime (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (t : Time) (v : V) :
    ∀ w₁ ∈ Restated.Vocabulary.Execution.Run.stateBeforeTime M S rho t, ∀ D ∈ (w₁ v).st.bodies,
      (M.derive_named S.E S.cfg D).h ≤ (w₁ v).st.core.h_max :=
  Restated.Vocabulary.Proofs.NamedNumericStore.heights_bounded_stateBeforeTime facts S rho t v

/-- In every world after the events of `rho` at or before time `t`, every named body `v`'s store
    holds has a derived height at most the store's `h_max`. -/
theorem Vocabulary.Proofs.NamedStoreBridge.heights_le_hMax_readAt (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (t : Time) (v : V) :
    ∀ w₁ ∈ Restated.Vocabulary.Execution.Run.readAt M S rho t, ∀ D ∈ (w₁ v).st.bodies,
      (M.derive_named S.E S.cfg D).h ≤ (w₁ v).st.core.h_max :=
  Restated.Vocabulary.Proofs.NamedNumericStore.heights_bounded_readAt facts S rho t v

/-- In every world of `rho` at time `t`, every named body `v`'s store holds has a derived height at
    most the store's `h_max`. -/
theorem Vocabulary.Proofs.NamedStoreBridge.heights_le_hMax_stateAt (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (t : Time) (v : V) :
    ∀ w₁ ∈ Restated.Vocabulary.Execution.Run.stateAt M S rho t, ∀ D ∈ (w₁ v).st.bodies,
      (M.derive_named S.E S.cfg D).h ≤ (w₁ v).st.core.h_max :=
  Restated.Vocabulary.Proofs.NamedStoreBridge.heights_le_hMax_readAt facts S rho t v

/-- In every world before the `i`-th event of `rho`, the chain state `v`'s store holds for the
    erasure of each named body it holds is that body's derived chain state. -/
theorem Vocabulary.Proofs.NamedStoreBridge.derivedView_stateBefore (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (i : Nat) (v : V) :
    ∀ w₁ ∈ Record.stateBeforeOf M S rho i, ∀ D ∈ (w₁ v).st.bodies,
      (w₁ v).st.core.σ D.erase = M.derive_named S.E S.cfg D := fun w₁ hw₁ =>
  (coherent_of_inv' (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho i v w₁ hw₁)).2.2.2.2

/-- In every world after the events of `rho` before time `t`, the chain state `v`'s store holds for
    the erasure of each named body it holds is that body's derived chain state. -/
theorem Vocabulary.Proofs.NamedStoreBridge.derivedView_stateBeforeTime (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (t : Time) (v : V) :
    ∀ w₁ ∈ Restated.Vocabulary.Execution.Run.stateBeforeTime M S rho t, ∀ D ∈ (w₁ v).st.bodies,
      (w₁ v).st.core.σ D.erase = M.derive_named S.E S.cfg D := fun w₁ hw₁ =>
  (coherent_of_inv' (Restated.Vocabulary.Proofs.NamedRuntime.stateBeforeTime_invariants facts S rho t v w₁ hw₁)).2.2.2.2

end

end DecoupledConsensusModel.Sts.Restated
