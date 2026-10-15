import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13beRoute3_45
import Proofs.Claims.Restated.Claim13beRoute3_45b
import Proofs.Claims.Restated.Claim13beRoute3_46
import Proofs.Claims.Restated.Claim13beRoute3_47
import Proofs.Claims.Restated.Claim13beRoute3_47b
import Proofs.Claims.Restated.Claim13beRoute3_48
import Proofs.Claims.Restated.Claim13beRoute3_48b
import Proofs.Claims.Restated.Claim13beRoute3_49
import Proofs.Claims.Restated.Claim13beRoute3_49b
import Proofs.Claims.Restated.Claim13beRoute3_51
import Proofs.Claims.Restated.Vocabulary_Execution_Acceptance
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Claims.Restated.Vocabulary_Execution_StoreFinalityCore
import Proofs.Claims.Restated.Vocabulary_Protocol_ChainState_JustificationCertificates
import Proofs.Claims.Restated.Vocabulary_Protocol_ChainState_ProposalBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Evidence_ProvenanceBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_OpeningActiveCarrier
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_ProposalSnapshotBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_GradeFormsProducers
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_AcceptanceTiming
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_BlockAdmission
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_FinalityMonotoneCore
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_JustificationBound
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_Action
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_SlotInduction
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_42c
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.RunVocabulary
import Model.Conditions.Vocabulary_Internal_Definitions_NamedDerived
import Model.Conditions.Vocabulary_Internal_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_Definitions_NamedLifecycle
import Model.Conditions.Vocabulary_Internal_Definitions_NamedProposalPivot
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGradeQueries
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGrades
import Model.Conditions.Vocabulary_Internal_Definitions_TickReads
import Model.Conditions.Vocabulary_Internal_Internal_GradeReads
import Model.Conditions.Vocabulary_Internal_Invariants
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ProposalSourcesInternal
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedReceiptCalls
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Objects
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_Internal_StoreFinality
import Model.Conditions.Vocabulary_ModelVocabulary_Healing_Schedule
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Proofs.Vocabulary.Protocol.ChainState.Chain
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Protocol_Evidence_ProvenanceBridge
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Agreement
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_ProposalSnapshotBridge
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_SGOpeningFrozenSuffix
import Proofs.Vocabulary.Protocol.ForkChoice.Views.ProposalCore
import Model.Conditions.Vocabulary_Protocol_Grades_LegacyVocabulary
import Model.Conditions.Vocabulary_Protocol_Handlers_Blocks
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Conditions.Vocabulary_Statements_Instantiation_Proposals
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_25

/-!
# Duty stores of a slot along a path of the run

Theorems about the proposal duty store and the vote duty store of a slot, the action attestations,
and the height progress of the stores, read along the path `W` of a run satisfying
`AdmissibleFieldsOn`, over a model `M : Record.Model V` and its facts. A store strictly before an
instant `t` is the store in `W (strictEventIndex rho t)`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

open scoped DC

/-! ### Helpers about paths, reads and stores -/

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Proofs.HealingSurface

/-- In a run sorted by key, the worlds strictly before `t` are the worlds before the event of index
    `strictEventIndex rho t`. -/
private theorem stateBeforeTime_eq_strict₅₂ (S : Setup V) (rho : Record.Run V)
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f)) (t : Time) :
    Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t =
      Record.stateBeforeOf M S rho (strictEventIndex rho t) := by
  have hpre : rho.events.filter (fun e => decide (e.time < t)) =
      rho.events.take (rho.events.filter (fun e => decide (e.time < t))).length := by
    refine List.prefix_iff_eq_take.mp ?_
    rw [DecoupledConsensusModel.Proofs.Bridges.filter_eq_takeWhile_of_pairwise
      (R := fun e f => Record.Event.key e ≤ Record.Event.key f) ?_ _ hsorted]
    · exact List.takeWhile_prefix _
    · intro e f hk hf
      simp only [decide_eq_true_eq] at hf ⊢
      exact lt_of_le_of_lt (Restated.time_le_of_key_le hk) hf
  show (rho.events.filter (fun e => decide (e.time < t))).foldlM (Record.worldStepOf M S)
      (fun v => M.initial S v) =
    (rho.events.take (rho.events.filter (fun e => decide (e.time < t))).length).foldlM
      (Record.worldStepOf M S) (fun v => M.initial S v)
  rw [← hpre]

/-- In a run sorted by key, the world `W (strictEventIndex rho t)` of a path `W` is a world strictly
    before `t`. -/
private theorem mem_stateBeforeTime_along₅₂ {S : Setup V} {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (t : Time) :
    W (strictEventIndex rho t) ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t := by
  rw [stateBeforeTime_eq_strict₅₂ S rho hsorted]
  exact (hW _).1

omit [DecidableEq V] [Fintype V] in
/-- In a run sorted by key, an event among the first `strictEventIndex rho t` events is at a time
    before `t`. -/
private theorem time_lt_of_lt_strict₅₂ {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {j : Nat} {e : Record.Event V} (he : rho.events[j]? = some e) {t : Time}
    (hj : j < strictEventIndex rho t) : e.time < t := by
  have hpre : rho.events.filter (fun f => decide (f.time < t)) =
      rho.events.take (rho.events.filter (fun f => decide (f.time < t))).length := by
    refine List.prefix_iff_eq_take.mp ?_
    rw [DecoupledConsensusModel.Proofs.Bridges.filter_eq_takeWhile_of_pairwise
      (R := fun e f => Record.Event.key e ≤ Record.Event.key f) ?_ _ hsorted]
    · exact List.takeWhile_prefix _
    · intro e' f hk hf
      simp only [decide_eq_true_eq] at hf ⊢
      exact lt_of_le_of_lt (Restated.time_le_of_key_le hk) hf
  have hj' : j < (rho.events.filter (fun f => decide (f.time < t))).length := hj
  have hmem : e ∈ rho.events.filter (fun f => decide (f.time < t)) := by
    rw [hpre]
    exact List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hj']; exact he)
  simpa only [decide_eq_true_eq] using (List.mem_filter.mp hmem).2

/-- Along a path `W` of `rho`, `W (m + k)` is among the worlds the events `m` to `m + k - 1` lead to
    from `W m`. -/
private theorem onePath_reach₅₂ {S : Setup V} {rho : Record.Run V}
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

/-- Along a path `W` of `rho`, for `m ≤ n`, `W n` is among the worlds the events `m` to `n - 1` lead
    to from `W m`. -/
private theorem onePath_slice₅₂ {S : Setup V} {rho : Record.Run V}
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) {m n : Nat}
    (hmn : m ≤ n) :
    W n ∈ ((rho.events.drop m).take (n - m)).foldlM (Record.worldStepOf M S) (W m) := by
  have h := onePath_reach₅₂ W hW m (n - m)
  rwa [Nat.add_sub_of_le hmn] at h

/-- The node state built from the proposer's node state in `W` strictly before slot `s`'s proposal
    time, with its clock set to that time and an outcome of `M.onPhaseTick` as cache, is one of the
    reads `proposerReadAt M S rho s`. -/
private theorem mem_proposerReadAt_along₅₂ {S : Setup V} {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (s : Slot)
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core.toHealing
      (M.proposal_time S.E s)
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).cache ⇢ c) :
    M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
        (M.proposal_time S.E s))
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record c ∈
      Restated.Vocabulary.Statements.Instantiation.proposerReadAt M S rho s :=
  ⟨_, mem_stateBeforeTime_along₅₂ hsorted hW _, c, hc, rfl⟩

/-- The store `tickStore` stages at `t` from `n`'s core store is the core store of `n`'s store with
    its clock set to `t`. -/
private theorem tickStore_eq₅₂ (facts : Record.Facts M) (S : Setup V) (n : M.N) (t : Time) :
    Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core t = (M.ns_setClock S.E n.st t).core := by
  rw [Restated.Vocabulary.Proofs.Optimistic.tickStore, facts.hd.setClock_core_eq_store_with_t_s]

private theorem read_core₅₂ (facts : Record.Facts M) (S : Setup V) (n : M.N) (t : Time) :
    (M.ns_setClock S.E n.st t).core = Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core t :=
  (tickStore_eq₅₂ facts S n t).symm

/-- A block of the filtered block tree of a store is a descendant of the store's finalized block. -/
private theorem F_preceq_of_mem_filtered₅₂ (facts : Record.Facts M) (st : M.S) {C : Block V}
    (hC : C ∈ M.get_filtered_block_tree (M.toHealing st).toFG) : Block.Preceq st.F C := by
  have h := facts.fc.finalized_preceq_of_mem_get_filtered_block_tree hC
  rwa [facts.sto.Sts_toHealing_F] at h

/-- The store `tickStore` stages from `n`'s core store has the tree, chain states, finalized and
    justified blocks, height maximum and block stamps of `n`'s core store. -/
private theorem tickStore_parts₅₂ (facts : Record.Facts M) (S : Setup V) (n : M.N) (t : Time) :
    (Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core t).T = n.st.core.T ∧
    (Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core t).σ = n.st.core.σ ∧
    (Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core t).F = n.st.core.F ∧
    (Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core t).J = n.st.core.J ∧
    (Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core t).h_max = n.st.core.h_max ∧
    (Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core t).timestamp_block =
      n.st.core.timestamp_block := by
  rw [tickStore_eq₅₂ facts]
  exact ⟨facts.hd.Sts_setClock_core_T _ _ _, facts.hd.Sts_setClock_core_σ _ _ _,
    facts.hd.setClock_core_F _ _ _, facts.hd.setClock_core_J _ _ _,
    facts.hd.setClock_core_h_max _ _ _, facts.hd.setClock_core_timestamp_block _ _ _⟩

/-- The core store of `n`'s store with its clock set to slot `s`'s vote time is the vote staging of
    `n`'s core store for `s`. -/
private theorem voteRead_core₅₂ (facts : Record.Facts M) (S : Setup V) (n : M.N) (s : Slot) :
    (M.ns_setClock S.E n.st (M.vote_time S.E s)).core =
      Restated.Vocabulary.Proofs.Optimistic.voteStore M S n.st.core s :=
  read_core₅₂ facts S n _

/-- The slot of the store `tickStore` stages at `t` is the slot of `t`. -/
private theorem tickStore_s₅₂ (facts : Record.Facts M) (S : Setup V) (n : M.N) (t : Time) :
    (Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core t).s = S.E.slotOf t := by
  rw [tickStore_eq₅₂ facts, facts.hd.Sts_setClock_core_s]

/-- In a run sorted by key, every block other than genesis of the tree of `v`'s core store in
    `W (strictEventIndex rho t)` has its parent in that tree. -/
private theorem closed_along₅₂ (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    (t : Time) (v : V) :
    ∀ B ∈ (W (strictEventIndex rho t) v).st.core.T,
      B.parent? = none ∨ B.parent ∈ (W (strictEventIndex rho t) v).st.core.T := by
  have hpc := Restated.Vocabulary.Proofs.NamedStoreBridge.parentClosed_stateBeforeTime facts S rho t v
    _ (mem_stateBeforeTime_along₅₂ hsorted hW t)
  unfold Restated.Vocabulary.Internal.ParentClosed Record.Model.GS.parent_closed at hpc
  rw [facts.sto.toHealing_gs_T] at hpc
  exact hpc.2

/-- In a run sorted by key, an ancestor of a block of the tree of `v`'s core store in
    `W (strictEventIndex rho t)` is in that tree. -/
private theorem mem_of_preceq_along₅₂ (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    (t : Time) (v : V) {X Y : Block V} (hY : Y ∈ (W (strictEventIndex rho t) v).st.core.T)
    (hXY : Block.Preceq X Y) : X ∈ (W (strictEventIndex rho t) v).st.core.T :=
  DecoupledConsensusModel.Proofs.Records.mem_of_preceq (closed_along₅₂ facts S hsorted hW t v) X Y hY
    (DecoupledConsensusModel.Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mpr hXY)

/-- Along a path `W`, for `j ≤ n`, `v`'s finalized block in `W j` is an ancestor of its finalized
    block in `W n`. -/
private theorem F_mono_along₅₂ (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (v : V)
    {j n : Nat} (hjn : j ≤ n) : Block.Preceq (W j v).st.core.F (W n v).st.core.F :=
  Restated.Vocabulary.Protocol.stateBefore_F_mono facts S rho v hjn (W j) (hW j).1 (W n)
    (onePath_slice₅₂ W hW hjn)

/-- The slot of the vote staging of a store for slot `s` is `s`. -/
private theorem voteStore_s₅₂ (facts : Record.Facts M) (S : Setup V) (n : M.N) (s : Slot) :
    (Restated.Vocabulary.Proofs.Optimistic.voteStore M S n.st.core s).s = s := by
  rw [Restated.Vocabulary.Proofs.Optimistic.voteStore, tickStore_s₅₂ facts, facts.sch.slotOf_vote_time]

/-- The slot of the store `tickStore` stages at slot `s`'s proposal time is `s`. -/
private theorem proposalStore_s₅₂ (facts : Record.Facts M) (S : Setup V) (n : M.N) (s : Slot) :
    (Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core (M.proposal_time S.E s)).s = s := by
  rw [tickStore_s₅₂ facts, facts.sch.slotOf_proposal_time]

omit [DecidableEq V] [Fintype V] in
private theorem le_sub_of_add_le₅₂ {a b c : Int} (h : a + c ≤ b) : a ≤ b - c := by
  omega

omit [DecidableEq V] [Fintype V] in
/-- For `Δ > 0`, if `a` and `b` are multiples of `Δ` and `a < b`, then `a + Δ ≤ b`. -/
private theorem add_delta_le_of_lt_emod₅₂ {Δ a b : Int} (hΔ : 0 < Δ) (ha : a % Δ = 0)
    (hb : b % Δ = 0) (hab : a < b) : a + Δ ≤ b := by
  obtain ⟨k, rfl⟩ := Int.dvd_of_emod_eq_zero ha
  obtain ⟨l, rfl⟩ := Int.dvd_of_emod_eq_zero hb
  have hkl : k < l := by
    by_contra h
    have h' : l ≤ k := not_lt.mp h
    have : Δ * l ≤ Δ * k := Int.mul_le_mul_of_nonneg_left h' (le_of_lt hΔ)
    omega
  have h1 : k + 1 ≤ l := hkl
  have h2 : Δ * (k + 1) ≤ Δ * l := Int.mul_le_mul_of_nonneg_left h1 (le_of_lt hΔ)
  rw [Int.mul_add, Int.mul_one] at h2
  exact h2

/-- One delay after slot `s`'s proposal time is at or before its vote time. -/
private theorem proposal_add_delta_le_vote₅₂ (facts : Record.Facts M) (S : Setup V) (s : Slot) :
    M.proposal_time S.E s + S.E.Δ ≤ M.vote_time S.E s :=
  add_delta_le_of_lt_emod₅₂ S.E.Δ_pos (facts.sch.proposal_time_emod_delta_inclX S.E s)
    (facts.sch.vote_time_emod_delta S s) (facts.sch.proposal_time_lt_vote_time S.E s)

/-- Slot `s`'s vote time is before its support cutoff. -/
private theorem vote_time_lt_support_cutoff₅₂ (facts : Record.Facts M) (S : Setup V) (s : Slot) :
    M.vote_time S.E s < M.support_cutoff S.E s := by
  rcases lt_or_gt_of_ne (facts.sch.support_cutoff_ne_vote_time S.E s) with h | h
  · exfalso
    have h1 := facts.sch.support_cutoff_lt_vote_time_imp_lt_proposal_time S.E h
    have h2 := facts.sch.proposal_time_slotOf_le S.E (le_of_lt (facts.sch.support_cutoff_pos S s))
    rw [facts.sch.slotOf_support_cutoff] at h2
    exact absurd h1 (not_lt.mpr h2)
  · exact h

/-- For `0 < s`: one delay after the view freeze of slot `s − 1` is at or before slot `s`'s proposal
    time, slot `s − 1`'s proposal time is at or before its view freeze, and that view freeze is at
    or before slot `s`'s vote time. -/
private theorem freeze_facts₅₂ (facts : Record.Facts M) (S : Setup V) {s : Slot} (hs : 0 < s) :
    M.view_freeze S.E (s - 1) + S.E.Δ ≤ M.proposal_time S.E s ∧
    M.proposal_time S.E (s - 1) ≤ M.view_freeze S.E (s - 1) ∧
    M.view_freeze S.E (s - 1) ≤ M.vote_time S.E s := by
  have hpred : s - 1 + 1 = s := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hs))
  have hhop : M.view_freeze S.E (s - 1) + S.E.Δ ≤ M.proposal_time S.E s := by
    have h := facts.sch.view_freeze_add_delta_le_proposal_time_succ S.E (s - 1)
    rwa [hpred] at h
  refine ⟨hhop, ?_, ?_⟩
  · exact le_of_lt (lt_trans (lt_trans (facts.sch.proposal_time_lt_vote_time S.E (s - 1))
      (vote_time_lt_support_cutoff₅₂ facts S (s - 1)))
      (facts.sch.Optimistic_support_cutoff_lt_view_freeze S.E (s - 1)))
  · have hlt : M.view_freeze S.E (s - 1) < M.proposal_time S.E s :=
      lt_of_lt_of_le (Int.lt_add_of_pos_right _ S.E.Δ_pos) hhop
    exact le_of_lt (lt_trans hlt (facts.sch.proposal_time_lt_vote_time S.E s))

/-- A block `C` of the tree of `st` that is a descendant of `st`'s finalized block and FG root, with
    a descendant `Y` in the tree of chain-state height at least `st.h_max − 1`, is in the filtered
    block tree of `st`. -/
private theorem mem_filtered_of_parts₅₂ (facts : Record.Facts M) (st : M.S) {C Y : Block V}
    (hC : C ∈ st.T) (hF : Block.Preceq st.F C) (hY : Y ∈ st.T) (hCY : Block.Preceq C Y)
    (hh : st.h_max - 1 ≤ (st.σ Y).h)
    (hroot : Block.Preceq (M.get_fg_root (M.toHealing st).toFG) C) :
    C ∈ M.get_filtered_block_tree (M.toHealing st).toFG :=
  facts.fc.mem_get_filtered_block_tree_of_parts (M.toHealing st)
    (by rw [facts.sto.toHealing_T]; exact hC) (by rw [facts.sto.Sts_toHealing_F]; exact hF)
    (by rw [facts.sto.toHealing_T]; exact hY) hCY
    (by rw [facts.sto.Sts_toHealing_h_max, facts.sto.Sts_toHealing_σ]; exact hh) hroot

/-- If the proposal computed on a proposer's read `n` can be `P`, the parent of `P`'s erasure is the
    parent of every outcome of the proposal input of `n`. -/
private theorem proposal_erase_parent₅₂ (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    (s : Slot) {n : M.N} (hn : n ∈ Restated.Vocabulary.Statements.Instantiation.proposerReadAt M S rho s)
    {P : NamedBlock V}
    (hP : M.proposal_with (M.gradeContract n.cache) Protocol.ProposalRowSource.poolAndCarried S.E S.hc
      (S.node (S.E.proposer s)) n.st ⇢ some P)
    (input : Protocol.ProposalInput V)
    (hinput : Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract n.cache)
      S.E S.hc (S.node (S.E.proposer s)) (M.toHealing n.st.core) ⇢ input) :
    P.erase.parent? = some input.parent := by
  obtain ⟨p, hp, hpe⟩ :=
    Restated.Vocabulary.Proofs.HealingSurface.proposedBlockAt_parent facts S rho s n hn hP input hinput
  rw [DecoupledConsensusModel.Proofs.NamedWire.erase_parent_optional, hp, Option.map_some, hpe]

/-- If every body of a named store has its parent among the bodies, every named ancestor of a body
    is a body. -/
private theorem ancestor_body_mem₅₂ {st : M.NS}
    (hpc : Restated.Vocabulary.Proofs.NamedStore.NamedParentClosed M st)
    {A B : NamedBlock V} (hB : B ∈ st.bodies) (hAB : NamedBlock.Preceq A B) : A ∈ st.bodies := by
  revert hB hAB
  induction B with
  | genesis =>
      intro hB hAB
      simp only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] at hAB
      exact hAB ▸ hB
  | node parent slot root votes support rows proposer ih =>
      intro hB hAB
      simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hAB
      rcases hAB with rfl | hparent
      · exact hB
      · have hp := hpc.2 _ hB
        simp only [NamedBlock.parent] at hp
        exact ih hp (by simpa only [NamedBlock.Preceq] using hparent)

/-- In a world strictly before `t`, the chain-state height grows along the tree of `w`'s core store:
    if `A ⪯ B` are both in the tree, the height of `A` is at most that of `B`. -/
private theorem sigma_height_mono₅₂ (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    (t : Time) (w : V) (x : V → M.N)
    (hx : x ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t)
    {A B : Block V} (hA : A ∈ (x w).st.core.T) (hB : B ∈ (x w).st.core.T)
    (hAB : Block.Preceq A B) : ((x w).st.core.σ A).h ≤ ((x w).st.core.σ B).h := by
  have hcoh : Restated.Vocabulary.Proofs.NamedStore.Coherent M S.E S.cfg (x w).st :=
    (Restated.Vocabulary.Proofs.NamedRuntime.stateBeforeTime_invariants facts S rho t w x hx).1.1.1
  obtain ⟨An, hAn, hAerase⟩ :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime facts S rho t w x hx hA
  obtain ⟨Bn, hBn, hBerase⟩ :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime facts S rho t w x hx hB
  have hABn : Block.Preceq An.erase Bn.erase := by rw [hAerase, hBerase]; exact hAB
  obtain ⟨An', hAn'B, hAn'e⟩ := DecoupledConsensusModel.Proofs.NamedAncestry.erased_ancestor_lift Bn hABn
  have hAn'mem : An' ∈ (x w).st.bodies := ancestor_body_mem₅₂ hcoh.2.2.1 hBn hAn'B
  have hEq : An' = An := hcoh.2.1 An' hAn'mem An hAn hAn'e
  calc ((x w).st.core.σ A).h
      = (M.derive_named S.E S.cfg An).h := by
        rw [← hAerase]
        exact congrArg (fun y => y.h)
          (Restated.Vocabulary.Proofs.NamedStoreBridge.derivedView_stateBeforeTime facts S rho t w x hx An hAn)
    _ = (M.derive_named S.E S.cfg An').h := by rw [hEq]
    _ ≤ (M.derive_named S.E S.cfg Bn).h := facts.cs.derive_height_mono S.E S.cfg hAn'B
    _ = ((x w).st.core.σ B).h := by
        rw [← hBerase]
        exact (congrArg (fun y => y.h)
          (Restated.Vocabulary.Proofs.NamedStoreBridge.derivedView_stateBeforeTime facts S rho t w x hx Bn
            hBn)).symm

/-- If `B` is in the filtered block tree of the proposer's staged store at slot `s`'s proposal time,
    and `C` is a descendant of that store's FG root and an ancestor of `B`, then `C` is in that
    filtered block tree. -/
private theorem path_of_candidate₅₂ (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (s : Slot)
    {B C : Block V}
    (hB : B ∈ M.get_filtered_block_tree (M.toHealing (M.ns_setClock S.E
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
      (M.proposal_time S.E s)).core).toFG)
    (hrootC : Block.Preceq (M.get_fg_root (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core
      (M.proposal_time S.E s))).toFG) C)
    (hCB : Block.Preceq C B) :
    C ∈ M.get_filtered_block_tree (M.toHealing (M.ns_setClock S.E
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
      (M.proposal_time S.E s)).core).toFG := by
  rw [read_core₅₂ facts] at hB ⊢
  obtain ⟨hTeq, -, hFeq, hJeq, -, -⟩ := tickStore_parts₅₂ facts S
    (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)) (M.proposal_time S.E s)
  have hFJ0 := Restated.Vocabulary.Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
    facts S rho (M.proposal_time S.E s) (S.E.proposer s) _ (mem_stateBeforeTime_along₅₂ hsorted hW _)
  have hBT : B ∈ (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core.T := by
    have h := facts.fc.get_filtered_block_tree_subset _ hB
    rw [facts.sto.toHealing_T, hTeq] at h
    exact h
  have hCT := mem_of_preceq_along₅₂ facts S hsorted hW _ _ hBT hCB
  refine facts.fc.mem_filtered_of_preceq ?_ hB ?_
    (DecoupledConsensusModel.Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mpr hCB)
    (DecoupledConsensusModel.Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mpr hrootC)
  · rw [facts.sto.Sts_toHealing_F, facts.sto.Sts_toHealing_J, hFeq, hJeq]
    exact DecoupledConsensusModel.Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mpr hFJ0
  · rw [facts.sto.toHealing_T, hTeq]
    exact hCT

/-- Under `CandidateScorePreservingViewExtension` for `C`, the source and target raw views count the
    same voters at every slot, and every outcome of the Goldfish score of `C` over the source equals
    every outcome over the target. -/
private theorem view_ext_eqs₅₂ (facts : Record.Facts M) (E : Env V)
    {sT tT : Finset (Block V)} {sR sS tR tS : Finset (GoldfishVote V)} {C : Block V}
    (h : Restated.Vocabulary.Protocol.CandidateScorePreservingViewExtension M sT tT sR sS tR tS C)
    (k : Slot) :
    M.voters_count E sR k = M.voters_count E tR k ∧
      ∀ g : Nat, M.goldfish_score E sT sR sS k C ⇢ g →
      ∀ g' : Nat, M.goldfish_score E tT tR tS k C ⇢ g' → g = g' := by
  have heq : ∀ w : V, M.equivocates sR w = M.equivocates tR w := by
    intro w
    cases hs : M.equivocates sR w with
    | true => exact (facts.sch.equivocates_mono_of_subset h.raw_subset hs).symm
    | false =>
        cases ht : M.equivocates tR w with
        | false => rfl
        | true =>
            exfalso
            obtain ⟨u, hu, u', hu', hne, huw, hu'w⟩ :=
              (facts.sch.equivocates_eq_true_iff tR w).mp ht
            by_cases hus : u ∈ sR
            · by_cases hu's : u' ∈ sR
              · have : M.equivocates sR w = true :=
                  (facts.sch.equivocates_eq_true_iff sR w).mpr
                    ⟨u, hus, u', hu's, hne, huw, hu'w⟩
                rw [hs] at this; exact Bool.false_ne_true this
              · have := h.raw_extra_equiv u' hu' hu's
                rw [hu'w, hs] at this; exact Bool.false_ne_true this
            · have := h.raw_extra_equiv u hu hus
              rw [huw, hs] at this; exact Bool.false_ne_true this
  refine ⟨?_, ?_⟩
  · apply facts.fc.voters_count_eq_of_participates E k k
    intro w
    cases hs : M.participates sR w with
    | true =>
        obtain ⟨u, hu, huw⟩ := (facts.sch.participates_eq_true_iff sR w).mp hs
        exact ((facts.sch.participates_eq_true_iff tR w).mpr ⟨u, h.raw_subset hu, huw⟩).symm
    | false =>
        cases ht : M.participates tR w with
        | false => rfl
        | true =>
            exfalso
            obtain ⟨u, hu, huw⟩ := (facts.sch.participates_eq_true_iff tR w).mp ht
            by_cases hus : u ∈ sR
            · have := (facts.sch.participates_eq_true_iff sR w).mpr ⟨u, hus, huw⟩
              rw [hs] at this; exact Bool.false_ne_true this
            · have h1 := h.raw_extra_equiv u hu hus
              rw [huw] at h1
              have := facts.sch.participates_of_equivocates h1
              rw [hs] at this; exact Bool.false_ne_true this
  · intro g hg g' hg'
    choose t ht using fun u => facts.fc.targets_under_nonempty sT C u
    choose t' ht' using fun u => facts.fc.targets_under_nonempty tT C u
    refine facts.fc.goldfish_score_eq_of_iff E k C heq t ht t' ht' ?_ g hg g' hg'
    intro w hclean
    have hcleanT : M.equivocates tR w = false := by rw [← heq w]; exact hclean
    constructor
    · rintro ⟨u, hu, huw, hus, htu⟩
      rcases h.forward u hu (t u) (ht u) htu with ⟨hreach, hall⟩ | hequiv
      · exact ⟨u, hreach, huw, hus, hall _ (ht' u)⟩
      · rw [huw, hcleanT] at hequiv; exact absurd hequiv Bool.false_ne_true
    · rintro ⟨u, hu, huw, hus, htu⟩
      rcases h.backward u hu (t' u) (ht' u) htu with ⟨hreach, hall⟩ | hequiv
      · exact ⟨u, hreach, huw, hus, hall _ (ht u)⟩
      · rw [huw, hclean] at hequiv; exact absurd hequiv Bool.false_ne_true

/-- If `m` can return `a`, then `f <$> m` can return `f a`. -/
private theorem returns_map_intro₅₂ {α β : Type} (f : α → β) (m : DC.NDRE α) (a : α)
    (h : m ⇢ a) : (f <$> m) ⇢ f a := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image]
  exact ⟨_, h, rfl⟩

/-- If every anchor the node state `n` can give at round `r` is an ancestor of `pivot`, then the FG
    root of `n`'s core store is an ancestor of `pivot`. -/
private theorem fgRoot_preceq_of_anchors₅₂ (facts : Record.Facts M) (S : Setup V) (n : M.N)
    (r : Round) {pivot : Block V}
    (h : ∀ A, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n r ⇢ A → Block.Preceq A pivot) :
    Block.Preceq (M.get_fg_root (M.toHealing n.st.core).toFG) pivot := by
  obtain ⟨G, hG⟩ := facts.gr.read_nonempty (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core) r
  have hA : Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n r ⇢ G.anchor :=
    returns_map_intro₅₂ (fun g : Protocol.GradeRead V => g.anchor)
      (Restated.Vocabulary.Internal.PhaseGrades.nodeRead M S n r) G hG
  exact DecoupledConsensusModel.Proofs.ModelProperties.Preceq_trans
    (Restated.Vocabulary.Proofs.w4_fgRoot_preceq_nodeAnchor facts S n r G.anchor hA) (h _ hA)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation

/-- Two run blocks read through `Xb` with the same erasure are equal. -/
theorem frozenSuffix_runBlock_uniqueOn (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} {Hs : Int → Finset V} {Xb : Finset V} {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {A B : NamedBlock V} (hA : Restated.RunBlockOn M S rho W Xb A)
    (hB : Restated.RunBlockOn M S rho W Xb B)
    (herase : A.erase = B.erase) : A = B :=
  hf.rootCollisionFree.root_injective
    A B hA hB A B (Or.inl (Proofs.NamedAncestry.named_self A))
      (Or.inr (Proofs.NamedAncestry.named_self B))
      (by rw [← Proofs.NamedWire.erase_root A, ← Proofs.NamedWire.erase_root B, herase])

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation

/-- If `p, w ∈ Xb` and `C` is in the tree of `p`'s core store in `W (strictEventIndex rho tp)` and
    of `w`'s core store in `W (strictEventIndex rho tw)`, the two stores give `C` the same chain
    state. -/
theorem frozenSuffix_sigma_eqOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {p w : V} (hp : p ∈ Xb) (hw : w ∈ Xb) (tp tw : Time)
    {C : Block V}
    (hCp : C ∈ (W (strictEventIndex rho tp) p).st.core.T)
    (hCw : C ∈ (W (strictEventIndex rho tw) w).st.core.T) :
    (W (strictEventIndex rho tp) p).st.core.σ C = (W (strictEventIndex rho tw) w).st.core.σ C := by
  have hmp := mem_stateBeforeTime_along₅₂ hf.sorted hf.onePath tp
  have hmw := mem_stateBeforeTime_along₅₂ hf.sorted hf.onePath tw
  obtain ⟨Dp, hDpmem, hDpe⟩ :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime facts S rho tp p
      _ hmp hCp
  obtain ⟨Dw, hDwmem, hDwe⟩ :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime facts S rho tw w
      _ hmw hCw
  have hRp : Restated.RunBlockOn M S rho W Xb Dp :=
    Restated.runBlock_of_stateBefore_memOn facts S W Xb hp hDpmem
  have hRw : Restated.RunBlockOn M S rho W Xb Dw :=
    Restated.runBlock_of_stateBefore_memOn facts S W Xb hw hDwmem
  have heq : Dp = Dw :=
    Restated.frozenSuffix_runBlock_uniqueOn facts hf hRp hRw (hDpe.trans hDwe.symm)
  calc (W (strictEventIndex rho tp) p).st.core.σ C
      = M.derive_named S.E S.cfg Dp := by
        rw [← hDpe]
        exact Restated.Vocabulary.Proofs.NamedStoreBridge.derivedView_stateBeforeTime facts S rho tp p
          _ hmp Dp hDpmem
    _ = M.derive_named S.E S.cfg Dw := by rw [heq]
    _ = (W (strictEventIndex rho tw) w).st.core.σ C := by
        rw [← hDwe]
        exact (Restated.Vocabulary.Proofs.NamedStoreBridge.derivedView_stateBeforeTime facts S rho tw w
          _ hmw Dw hDwmem).symm

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation

/-- If the proposer of `s` and `v` are in `Xb` and `C` is in the tree of both the proposal duty
    store of slot `s` and `v`'s vote duty store, read along `W`, the two stores give `C` the same
    chain state. -/
theorem frozenSuffix_sigma_source_targetOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {s : Slot} (hprop : S.E.proposer s ∈ Xb)
    {v : V} (hv : v ∈ Xb) {C : Block V}
    (hCsource : C ∈ (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core
      (M.proposal_time S.E s)).T)
    (hCtarget : C ∈ (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
      (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core s).T) :
    (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core
        (M.proposal_time S.E s)).σ C =
      (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core s).σ C := by
  rw [Restated.Vocabulary.Proofs.Optimistic.voteStore, tickStore_eq₅₂ facts,
    tickStore_eq₅₂ facts, facts.hd.Sts_setClock_core_σ, facts.hd.Sts_setClock_core_σ]
  rw [Restated.Vocabulary.Proofs.Optimistic.voteStore, tickStore_eq₅₂ facts,
    facts.hd.Sts_setClock_core_T] at hCtarget
  rw [tickStore_eq₅₂ facts, facts.hd.Sts_setClock_core_T] at hCsource
  exact Restated.frozenSuffix_sigma_eqOn facts S Hs Xb hf hprop hv (M.proposal_time S.E s)
    (M.vote_time S.E s) hCsource hCtarget

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation

/-- If the proposal computed on the proposer's read at slot `s` can be `P`, `P`'s erasure is in an
    outcome `T` of `v`'s voter filtered block tree, and `D` is an ancestor of `P`'s erasure and a
    descendant of the finalized block and FG root of `v`'s vote staging, then `D` is in `T`. -/
theorem voterCandidate_on_proposalSegmentOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (_hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {s : Slot} {v : V} {D : Block V} {P : NamedBlock V}
    (cp : M.Cache)
    (hcp : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core.toHealing
      (M.proposal_time S.E s) (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).cache
      ⇢ cp)
    (hP : M.proposal_with
      (M.gradeContract (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
          (M.proposal_time S.E s))
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record cp).cache)
      .poolAndCarried S.E S.hc (S.node (S.E.proposer s))
      (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
          (M.proposal_time S.E s))
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record cp).st ⇢ some P)
    (T : Finset (Block V))
    (hT : M.voter_filtered_block_tree S.E
      (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st (M.vote_time S.E s)).core
      (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st
        (M.vote_time S.E s)).core.s ⇢ T)
    (hproposal : P.erase ∈ T)
    (hDP : Block.Preceq D P.erase)
    (hFD : Block.Preceq (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
      (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core s).F D)
    (hrootD : Block.Preceq
      (M.get_fg_root (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core s)).toFG) D) :
    D ∈ T := by
  rw [voteRead_core₅₂ facts] at hT
  obtain ⟨hTeq, -, -, -, -, -⟩ :=
    tickStore_parts₅₂ facts S (W (strictEventIndex rho (M.vote_time S.E s)) v) (M.vote_time S.E s)
  set target := Restated.Vocabulary.Proofs.Optimistic.voteStore M S
    (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core s with htarget
  obtain ⟨Q, hQ⟩ := facts.fc.voter_processed_block_tree_nonempty S.E
    (M.toHealing target).toFG.toSG.toGoldfishStore target.s
  obtain ⟨hPprocessed, _hFP, ⟨Y, hYprocessed, hPY, hheight⟩, _hrootP⟩ :=
    facts.hd.voter_filtered_block_tree_cases S.E target target.s T hT hproposal Q hQ
  have hPT : P.erase ∈ target.T := by
    have h' := facts.fc.mem_T_of_mem_voter_processed_block_tree _ _ _ Q hQ hPprocessed
    rwa [facts.sto.toHealing_gs_T] at h'
  have hDT : D ∈ target.T := by
    have hPT' : P.erase ∈ (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core.T := by
      rw [← hTeq]; exact hPT
    rw [htarget, Restated.Vocabulary.Proofs.Optimistic.voteStore, hTeq]
    exact mem_of_preceq_along₅₂ facts S _hf.sorted _hf.onePath _ v hPT' hDP
  have hslot : P.erase.slot = target.s := by
    rw [Proofs.NamedWire.erase_slot,
      Restated.Vocabulary.Proofs.HealingSurface.proposedBlockAt_slot facts S rho s _
        ⟨_, mem_proposerReadAt_along₅₂ _hf.sorted _hf.onePath s cp hcp, hP⟩ rfl,
      htarget, Restated.Vocabulary.Proofs.Optimistic.voteStore, tickStore_s₅₂ facts,
      facts.sch.slotOf_vote_time]
  have hDprocessed : D ∈ Q :=
    facts.fc.mem_voter_processed_block_tree_of_proposal _ _ _
      (by rw [facts.sto.toHealing_gs_T]; exact hDT) (by rw [facts.sto.toHealing_gs_T]; exact hPT)
      hslot hDP Q hQ
  exact facts.hd.mem_voter_filtered_block_tree_of_parts S.E target target.s Q hQ hDprocessed hFD
    hYprocessed (preceq_trans_Preceq hDP hPY) hheight hrootD T hT

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation

/-- If the proposal computed on the proposer's read at slot `s` can be `P`, `P`'s erasure is in an
    outcome `T` of `v`'s voter filtered block tree, `A` is in the filtered block tree of `v`'s vote
    staging, and `A ⪯ D ⪯` `P`'s erasure, then `D` is in `T`. -/
theorem voterCandidate_above_fullPivotOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {s : Slot} {v : V} {A D : Block V} {P : NamedBlock V}
    (cp : M.Cache)
    (hcp : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core.toHealing
      (M.proposal_time S.E s) (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).cache
      ⇢ cp)
    (hP : M.proposal_with
      (M.gradeContract (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
          (M.proposal_time S.E s))
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record cp).cache)
      .poolAndCarried S.E S.hc (S.node (S.E.proposer s))
      (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
          (M.proposal_time S.E s))
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record cp).st ⇢ some P)
    (T : Finset (Block V))
    (hT : M.voter_filtered_block_tree S.E
      (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st (M.vote_time S.E s)).core
      (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st
        (M.vote_time S.E s)).core.s ⇢ T)
    (hproposal : P.erase ∈ T)
    (hA : A ∈ M.get_filtered_block_tree
      (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core s)).toFG)
    (hAD : Block.Preceq A D)
    (hDP : Block.Preceq D P.erase) :
    D ∈ T := by
  obtain ⟨-, -, hFeq, hJeq, -, -⟩ :=
    tickStore_parts₅₂ facts S (W (strictEventIndex rho (M.vote_time S.E s)) v) (M.vote_time S.E s)
  have hFJ0 := Restated.Vocabulary.Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
    facts S rho (M.vote_time S.E s) v _ (mem_stateBeforeTime_along₅₂ hf.sorted hf.onePath _)
  rw [← hFeq, ← hJeq] at hFJ0
  let target := Restated.Vocabulary.Proofs.Optimistic.voteStore M S
    (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core s
  have hFJ : Block.Preceq target.F target.J := hFJ0
  have hrootA : Block.Preceq
      (M.get_fg_root (M.toHealing target).toFG) A :=
    preceq_eq_true_iff_Preceq.mp (facts.fc.preceq_get_fg_root_of_mem_filtered hA)
  have hFA : Block.Preceq target.F A :=
    preceq_trans_Preceq
      (Restated.Vocabulary.Proofs.StoreFinality.finalized_preceq_fgRoot facts (preceq_eq_true_iff_Preceq.mpr hFJ))
      hrootA
  exact Restated.voterCandidate_on_proposalSegmentOn facts S Hs Xb hf cp hcp hP T hT hproposal hDP
    (preceq_trans_Preceq hFA hAD) (preceq_trans_Preceq hrootA hAD)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation

/-- For `0 < s`, if the proposal at slot `s` can be `P` with `P`'s erasure in an outcome of `v`'s
    voter filtered block tree, and `Z` is in an outcome of `v`'s voter processed tree but is not an
    ancestor of `P`'s erasure, then `v`'s vote staging stamped `Z` before `view_freeze (s − 1)`. -/
theorem stampedBefore_of_voterProcessed_not_proposalAncestorOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    {s : Slot} (hs : 0 < s)
    (hprop : S.E.proposer s ∈ Hs (M.vote_time S.E s))
    {v : V} {Z : Block V} {P : NamedBlock V}
    (cp : M.Cache)
    (hcp : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core.toHealing
      (M.proposal_time S.E s) (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).cache
      ⇢ cp)
    (hP : M.proposal_with
      (M.gradeContract (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
          (M.proposal_time S.E s))
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record cp).cache)
      .poolAndCarried S.E S.hc (S.node (S.E.proposer s))
      (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
          (M.proposal_time S.E s))
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record cp).st ⇢ some P)
    (T : Finset (Block V))
    (hT : M.voter_filtered_block_tree S.E
      (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st (M.vote_time S.E s)).core
      (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st
        (M.vote_time S.E s)).core.s ⇢ T)
    (hproposal : P.erase ∈ T)
    (Q : Finset (Block V))
    (hQ : M.voter_processed_block_tree S.E
      (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core s)).toFG.toSG.toGoldfishStore
      (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core s)).s ⇢ Q)
    (hZprocessed : Z ∈ Q)
    (hnot : ¬ Block.Preceq Z P.erase) :
    stampedBefore
      (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core s).timestamp_block
      (M.view_freeze S.E (s - 1)) Z = true := by
  have htargetSlot : (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
      (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core s).s = s := by
    rw [Restated.Vocabulary.Proofs.Optimistic.voteStore, tickStore_s₅₂ facts, facts.sch.slotOf_vote_time]
  obtain ⟨hTeq, -, -, -, -, -⟩ :=
    tickStore_parts₅₂ facts S (W (strictEventIndex rho (M.vote_time S.E s)) v) (M.vote_time S.E s)
  rcases (facts.fc.voter_processed_block_tree_cases _ _ _ Q hQ hZprocessed).2 with
    hstamp | ⟨Q, hQT, hQs, hZQ⟩
  · rw [facts.sto.toHealing_gs_timestamp_block, Record.Model.HS.s, facts.sto.toHealing_s,
      htargetSlot] at hstamp
    exact hstamp
  · have hproposalT : P.erase ∈ (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core.T := by
      have h' := facts.hd.Sts_voter_filtered_block_tree_subset _ _ _ T hT hproposal
      rw [voteRead_core₅₂ facts, Restated.Vocabulary.Proofs.Optimistic.voteStore, hTeq] at h'
      exact h'
    have hQprefix : Q ∈ (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core.T := by
      have h' := hQT
      rw [facts.sto.toHealing_gs_T, Restated.Vocabulary.Proofs.Optimistic.voteStore, hTeq] at h'
      exact h'
    have hPslot : P.erase.slot = s := by
      rw [Proofs.NamedWire.erase_slot]
      exact Restated.Vocabulary.Proofs.HealingSurface.proposedBlockAt_slot facts S rho s _
        ⟨_, mem_proposerReadAt_along₅₂ hf.sorted hf.onePath s cp hcp, hP⟩ rfl
    have hTn : ∀ (j : Nat) (e : Record.Event V), j < strictEventIndex rho (M.vote_time S.E s) →
        rho.events[j]? = some e → e.time ≤ M.vote_time S.E s :=
      fun j e hj he => le_of_lt (time_lt_of_lt_strict₅₂ hf.sorted he hj)
    have hQeq : Q = P.erase :=
      Restated.unique_slot_block_in_store_beforeOn facts S Hs Xb hf hHs hs hprop hTn hTn
        hQprefix hproposalT
        (by rw [hQs, Record.Model.HS.s, facts.sto.toHealing_s, htargetSlot])
        hPslot
    exact False.elim (hnot (by rw [← hQeq]; exact hZQ))

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation

/-- If `Z`'s erasure is a descendant of the FG root of the proposal duty store of slot `s`, then for
    every `i` up to the number of events before `proposal_time s`, the proposer's finalized block in
    `W i` is an ancestor of `Z`'s erasure. -/
theorem sourceAnchor_finalizedBelowAtDeliveriesOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {s : Slot} {Z : NamedBlock V}
    (hroot : Block.Preceq
      (M.get_fg_root (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core
        (M.proposal_time S.E s))).toFG) Z.erase) :
    ∀ i : Nat, i ≤ (rho.events.filter (fun e => decide (e.time < M.proposal_time S.E s))).length →
      Block.Preceq (W i (S.E.proposer s)).st.core.F Z.erase := by
  obtain ⟨-, -, hFeq, hJeq, -, -⟩ := tickStore_parts₅₂ facts S
    (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)) (M.proposal_time S.E s)
  have hFJ0 := Restated.Vocabulary.Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
    facts S rho (M.proposal_time S.E s) (S.E.proposer s) _
    (mem_stateBeforeTime_along₅₂ hf.sorted hf.onePath _)
  rw [← hFeq, ← hJeq] at hFJ0
  have hFZ := preceq_trans_Preceq
    (Restated.Vocabulary.Proofs.StoreFinality.finalized_preceq_fgRoot facts
      (preceq_eq_true_iff_Preceq.mpr hFJ0)) hroot
  rw [hFeq] at hFZ
  intro i hi
  exact preceq_trans_Preceq (F_mono_along₅₂ facts S hf.onePath (S.E.proposer s) hi) hFZ

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation

/-- For `0 < s` and `lo ≤ proposal_time (s − 1)`, if `Z` is a body of `v`'s store before
    `vote_time s`, stamped before `view_freeze (s − 1)` and a descendant of the FG root of the
    proposal duty store of slot `s`, then `Z`'s erasure is in that proposal duty store. -/
theorem stampedVoterBlock_mem_proposerDuty_afterGSTOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {s : Slot} (hs : 0 < s)
    (hpost : lo ≤ M.proposal_time S.E (s - 1))
    (hprop : S.E.proposer s ∈ Hs (M.proposal_time S.E s))
    {v : V} (hv : v ∈ Hs (M.vote_time S.E s))
    (hhor : M.proposal_time S.E s ≤ rho.horizon)
    {Z : NamedBlock V}
    (hZbody : Z ∈ (W (strictEventIndex rho (M.vote_time S.E s)) v).st.bodies)
    (hstamp : stampedBefore
      (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core s).timestamp_block
      (M.view_freeze S.E (s - 1)) Z.erase = true)
    (hroot : Block.Preceq
      (M.get_fg_root (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core
        (M.proposal_time S.E s))).toFG) Z.erase) :
    Z.erase ∈ (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core
      (M.proposal_time S.E s)).T := by
  rw [(tickStore_parts₅₂ facts S _ _).1]
  by_cases hgen : Z = NamedBlock.genesis
  · subst hgen
    have hvisible := Restated.genesis_mem_and_stamp_storeBeforeTimeOn facts S Hs Xb hf
      (S.E.proposer s) (M.proposal_time S.E s) (M.proposal_time S.E s)
    rw [erase_named_genesis]
    exact hvisible.1
  · have hZn := hZbody
    have hstampn : stampedBefore
        (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core.timestamp_block
        (M.view_freeze S.E (s - 1)) Z.erase = true := by
      rw [← (tickStore_parts₅₂ facts S _ (M.vote_time S.E s)).2.2.2.2.2]
      exact hstamp
    have hprocessed : Restated.Vocabulary.Execution.Object.processed M
        (W (strictEventIndex rho (M.vote_time S.E s)) v).st (NamedObject.block Z) = true := by
      simpa only [Restated.Vocabulary.Execution.Object.processed, decide_eq_true_eq] using hZn
    obtain ⟨hfreezeHop, hpropFreeze, hfreezeVote⟩ := freeze_facts₅₂ facts S hs
    have hpostFreeze : lo ≤ M.view_freeze S.E (s - 1) := hpost.trans hpropFreeze
    rcases Restated.Vocabulary.Protocol.acceptsAt_block_of_processed facts S rho v W hf.onePath
        (strictEventIndex rho (M.vote_time S.E s)) Z hprocessed with
      hgen' | ⟨i, hi, t, hacc⟩
    · exact False.elim (hgen hgen')
    · have ht : t < M.view_freeze S.E (s - 1) :=
        Restated.acceptsAt_block_lt_of_stamp_before_coreOn facts S Hs Xb hf hacc
          (Nat.succ_le_of_lt hi)
          (Restated.Vocabulary.Protocol.publicTime_view_freeze facts S (s - 1)) (hHs _ _ hfreezeVote hv)
          hpostFreeze hstampn
      have hZpos : 0 < Z.slot := by
        rw [← Proofs.NamedWire.erase_slot]
        exact Nat.zero_lt_of_lt
          (Restated.Vocabulary.Protocol.parent_slot_lt_of_acceptsAt_block facts S W hf.onePath hacc)
      have hvmax : v ∈ Hs (max t lo) :=
        hHs _ _ (le_trans (max_le (le_of_lt ht) hpostFreeze) hfreezeVote) hv
      have hadmit : Restated.Vocabulary.Protocol.AdmittedBefore M S rho W (S.E.proposer s) Z.erase
          (M.proposal_time S.E s) :=
        Restated.block_admittedBefore_of_accepted_after_cutoff_coreOn facts
          S Hs Xb hf hHs hHsXb hvmax hprop hZpos hacc
            (lt_of_lt_of_le ht (le_sub_of_add_le₅₂ hfreezeHop))
            (hpostFreeze.trans (le_sub_of_add_le₅₂ hfreezeHop)) (Int.sub_add_cancel _ _) hhor
            (Restated.sourceAnchor_finalizedBelowAtDeliveriesOn facts S Hs Xb hf hroot)
      have hvisible := Restated.admittedBefore_mem_and_stamp_atOn facts S Hs Xb hf hadmit (le_refl _)
      exact hvisible.1

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation

/-- For `0 < s` and `lo ≤ proposal_time (s − 1)`, if the proposal at slot `s` can be `P`, the pivot
    is a descendant of the proposer's FG root and an ancestor of `X`, and the viability condition
    holds, then every child `C` of `X` in `v`'s target walk tree is in the filtered block tree of
    the proposer's staged store. -/
theorem targetChild_mem_sourceTree_of_frozenProposalOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {s : Slot} (hs : 0 < s)
    (hpost : lo ≤ M.proposal_time S.E (s - 1))
    (hprop : S.E.proposer s ∈ Hs (M.vote_time S.E s))
    {v : V} (hv : v ∈ Hs (M.vote_time S.E s))
    (hhor : M.proposal_time S.E s ≤ rho.horizon)
    {pivot X C : Block V} {P : NamedBlock V}
    (cp : M.Cache)
    (hcp : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core.toHealing
      (M.proposal_time S.E s) (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).cache
      ⇢ cp)
    (hP : M.proposal_with
      (M.gradeContract (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
          (M.proposal_time S.E s))
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record cp).cache)
      .poolAndCarried S.E S.hc (S.node (S.E.proposer s))
      (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
          (M.proposal_time S.E s))
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record cp).st ⇢ some P)
    (hsourceRoot : Block.Preceq
      (M.get_fg_root (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core
        (M.proposal_time S.E s))).toFG) pivot)
    (T : Finset (Block V))
    (hT : M.voter_filtered_block_tree S.E
      (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st (M.vote_time S.E s)).core
      (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st
        (M.vote_time S.E s)).core.s ⇢ T)
    (hproposal : P.erase ∈ T)
    (hviability :
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
          (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core
          (M.proposal_time S.E s)).h_max - 1 ≤
          (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
            (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core s).h_max - 1 ∨
        (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
          (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core
          (M.proposal_time S.E s)).h_max - 1 ≤
          ((Restated.Vocabulary.Proofs.Optimistic.tickStore M S
            (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core
            (M.proposal_time S.E s)).σ pivot).h)
    (hpivotX : Block.Preceq pivot X)
    (hCtarget : C ∈ T.erase P.erase)
    (hparent : C.parent? = some X) :
    C ∈ M.get_filtered_block_tree (M.toHealing (M.ns_setClock S.E
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
      (M.proposal_time S.E s)).core).toFG := by
  have hW := hf.onePath
  have hpmem := mem_stateBeforeTime_along₅₂ hf.sorted hW (M.proposal_time S.E s)
  have hvmem := mem_stateBeforeTime_along₅₂ hf.sorted hW (M.vote_time S.E s)
  have hn := mem_proposerReadAt_along₅₂ hf.sorted hW s cp hcp
  have hT0 := hT
  rw [voteRead_core₅₂ facts] at hT
  obtain ⟨Qv, hQv⟩ := facts.fc.voter_processed_block_tree_nonempty S.E
    (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
      (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core s)).toFG.toSG.toGoldfishStore
    (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
      (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core s).s
  obtain ⟨hTs, hσs, hFs, hJs, -, -⟩ := tickStore_parts₅₂ facts S
    (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)) (M.proposal_time S.E s)
  obtain ⟨hTt, -, -, -, -, -⟩ := tickStore_parts₅₂ facts S
    (W (strictEventIndex rho (M.vote_time S.E s)) v) (M.vote_time S.E s)
  have hpropProposal : S.E.proposer s ∈ Hs (M.proposal_time S.E s) :=
    hHs _ _ (le_of_lt (facts.sch.proposal_time_lt_vote_time S.E s)) hprop
  have hCne : C ≠ P.erase := (Finset.mem_erase.mp hCtarget).1
  have hCfrozen := (Finset.mem_erase.mp hCtarget).2
  have hXC : Block.Preceq X C := preceq_eq_true_iff_Preceq.mp (Protocol.preceq_of_parent? hparent)
  have hrootC := preceq_trans_Preceq hsourceRoot (preceq_trans_Preceq hpivotX hXC)
  by_cases hCP : Block.Preceq C P.erase
  · obtain ⟨input, hinput⟩ := facts.dt.with_proposal_input_nonempty
      (M.gradeContract (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
          (M.proposal_time S.E s))
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record cp).cache)
      S.E S.hc (S.node (S.E.proposer s))
      (M.toHealing (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
          (M.proposal_time S.E s))
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record cp).st.core)
    have hCH := preceq_eq_true_iff_Preceq.mp (Proofs.Optimistic.preceq_parent_of_ne
      (proposal_erase_parent₅₂ facts S s hn hP input hinput) (preceq_eq_true_iff_Preceq.mpr hCP) hCne)
    have hparentMem := Restated.Vocabulary.Proofs.HealingSurface.selectedOpeningProposedParent_mem_filtered
      facts S s _ hn input hinput
    rw [facts.nd.mkNode_st] at hparentMem
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at hparentMem
    exact path_of_candidate₅₂ facts S hf.sorted hW s hparentMem hrootC hCH
  · obtain ⟨hCprocessed, _hFC, ⟨Y, hYprocessed, hCY, hheightTarget⟩, _hrootC⟩ :=
      facts.hd.voter_filtered_block_tree_cases S.E _ _ T hT hCfrozen Qv hQv
    have hslotH : (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core s)).s =
        (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core s).s := by
      rw [Record.Model.HS.s, facts.sto.toHealing_s]
    have hQv' : M.voter_processed_block_tree S.E
        (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core s)).toFG.toSG.toGoldfishStore
        (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core s)).s ⇢ Qv := by
      rw [hslotH]; exact hQv
    have hYT : Y ∈ (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core.T := by
      have h' := facts.fc.mem_T_of_mem_voter_processed_block_tree _ _ _ Qv hQv hYprocessed
      rw [facts.sto.toHealing_gs_T, Restated.Vocabulary.Proofs.Optimistic.voteStore, hTt] at h'
      exact h'
    have hCT : C ∈ (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core.T := by
      have h' := facts.fc.mem_T_of_mem_voter_processed_block_tree _ _ _ Qv hQv hCprocessed
      rw [facts.sto.toHealing_gs_T, Restated.Vocabulary.Proofs.Optimistic.voteStore, hTt] at h'
      exact h'
    have hYnot : ¬ Block.Preceq Y P.erase := fun hYP => hCP (preceq_trans_Preceq hCY hYP)
    have hCstamp := Restated.stampedBefore_of_voterProcessed_not_proposalAncestorOn facts
      S Hs Xb hf hHs hs hprop cp hcp hP T hT0 hproposal Qv hQv' hCprocessed hCP
    have hYstamp := Restated.stampedBefore_of_voterProcessed_not_proposalAncestorOn facts
      S Hs Xb hf hHs hs hprop cp hcp hP T hT0 hproposal Qv hQv' hYprocessed hYnot
    obtain ⟨Cn, hCnbody, hCnerase⟩ :=
      Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime facts S rho
        (M.vote_time S.E s) v _ hvmem hCT
    obtain ⟨Yn, hYnbody, hYnerase⟩ :=
      Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime facts S rho
        (M.vote_time S.E s) v _ hvmem hYT
    have hrootY := preceq_trans_Preceq hrootC hCY
    have hCTsource : C ∈ (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core.T := by
      have hmem := Restated.stampedVoterBlock_mem_proposerDuty_afterGSTOn facts
        S Hs Xb hf hHs hHsXb hs hpost hpropProposal hv hhor hCnbody
          (by rw [hCnerase]; exact hCstamp)
          (by rw [hCnerase]; exact hrootC)
      rwa [hCnerase, hTs] at hmem
    have hYTsource : Y ∈ (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core.T := by
      have hmem := Restated.stampedVoterBlock_mem_proposerDuty_afterGSTOn facts
        S Hs Xb hf hHs hHsXb hs hpost hpropProposal hv hhor hYnbody
          (by rw [hYnerase]; exact hYstamp)
          (by rw [hYnerase]; exact hrootY)
      rwa [hYnerase, hTs] at hmem
    have hFJ0 := Restated.Vocabulary.Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
      facts S rho (M.proposal_time S.E s) (S.E.proposer s) _ hpmem
    have hFJ : Block.Preceq
        (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
          (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core
          (M.proposal_time S.E s)).F
        (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
          (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core
          (M.proposal_time S.E s)).J := by
      rw [hFs, hJs]; exact hFJ0
    have hFC := preceq_trans_Preceq (facts.fc.finalized_preceq_get_fg_root _ hFJ) hrootC
    rw [read_core₅₂ facts]
    rcases hviability with hthreshold | hpivotFloor
    · have hheight : (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
            (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core
            (M.proposal_time S.E s)).h_max - 1 ≤
          ((Restated.Vocabulary.Proofs.Optimistic.tickStore M S
            (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core
            (M.proposal_time S.E s)).σ Y).h := by
        refine le_trans hthreshold (le_trans hheightTarget (le_of_eq ?_))
        rw [Restated.frozenSuffix_sigma_source_targetOn facts S Hs Xb hf (hHsXb _ hprop) (hHsXb _ hv)
          (by rw [hTs]; exact hYTsource)
          (by rw [Restated.Vocabulary.Proofs.Optimistic.voteStore, hTt]; exact hYT)]
      exact mem_filtered_of_parts₅₂ facts _ (by rw [hTs]; exact hCTsource) hFC
        (by rw [hTs]; exact hYTsource) hCY hheight hrootC
    · have hpivotC := preceq_trans_Preceq hpivotX hXC
      have hpivotSource := mem_of_preceq_along₅₂ facts S hf.sorted hW _ _ hCTsource hpivotC
      have hheight : (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
            (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core
            (M.proposal_time S.E s)).h_max - 1 ≤
          ((Restated.Vocabulary.Proofs.Optimistic.tickStore M S
            (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core
            (M.proposal_time S.E s)).σ C).h := by
        refine le_trans hpivotFloor ?_
        rw [hσs]
        exact sigma_height_mono₅₂ facts S (M.proposal_time S.E s) (S.E.proposer s) _ hpmem
          hpivotSource hCTsource hpivotC
      exact mem_filtered_of_parts₅₂ facts _ (by rw [hTs]; exact hCTsource) hFC
        (by rw [hTs]; exact hCTsource) (Proofs.ModelProperties.Preceq_self C) hheight hrootC

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation

/-- For `0 < s` and `lo ≤ proposal_time (s − 1)`, if the proposal at slot `s` can be `P`, the core
    inputs and the candidate score bridge hold, and either the two duty stores have the same `h_max`
    or the pivot is in both stores' viability bands, then the proposal suffix transfers in both
    directions between the proposer's read and `v`'s read. -/
theorem namedProposalPivotSuffixTransfer_of_core_of_scoreBridgeOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {s : Slot} (hs : 0 < s)
    (hpost : lo ≤ M.proposal_time S.E (s - 1))
    (hprop : S.E.proposer s ∈ Hs (M.vote_time S.E s))
    {v : V} (hv : v ∈ Hs (M.vote_time S.E s))
    (hvoteHor : M.vote_time S.E s ≤ rho.horizon)
    {pivot : Block V} {P : NamedBlock V}
    (cp : M.Cache)
    (hcp : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core.toHealing
      (M.proposal_time S.E s) (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).cache
      ⇢ cp)
    (hP : M.proposal_with
      (M.gradeContract (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
          (M.proposal_time S.E s))
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record cp).cache)
      .poolAndCarried S.E S.hc (S.node (S.E.proposer s))
      (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
          (M.proposal_time S.E s))
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record cp).st ⇢ some P)
    (cv : M.Cache)
    (hcv : M.onPhaseTick S.E S.hc (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core.toHealing
      (M.vote_time S.E s) (W (strictEventIndex rho (M.vote_time S.E s)) v).cache ⇢ cv)
    (h : Restated.Vocabulary.Proofs.HealingSurface.NamedFrozenProposalSuffixCoreInputs M S rho s pivot v P
      (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
          (M.proposal_time S.E s))
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record cp)
      (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st
        (M.vote_time S.E s)) (W (strictEventIndex rho (M.vote_time S.E s)) v).record cv))
    (hbridge : Restated.Vocabulary.Proofs.HealingSurface.NamedProposalCandidateScoreBridge M S rho s v P
      (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
          (M.proposal_time S.E s))
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record cp)
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core
        (M.proposal_time S.E s))
      (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core s))
    (hfrontier :
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
          (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core
          (M.proposal_time S.E s)).h_max =
          (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
            (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core s).h_max ∨
        ((Restated.Vocabulary.Proofs.Optimistic.tickStore M S
            (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core
            (M.proposal_time S.E s)).h_max - 1 ≤
            ((Restated.Vocabulary.Proofs.Optimistic.tickStore M S
              (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core
              (M.proposal_time S.E s)).σ pivot).h ∧
          (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
            (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core s).h_max - 1 ≤
            ((Restated.Vocabulary.Proofs.Optimistic.voteStore M S
              (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core s).σ pivot).h)) :
    Restated.Vocabulary.Proofs.HealingSurface.NamedProposalPivotSuffixTransfer M S rho s pivot v P
      (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
          (M.proposal_time S.E s))
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record cp)
      (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st
        (M.vote_time S.E s)) (W (strictEventIndex rho (M.vote_time S.E s)) v).record cv) := by
  have hW := hf.onePath
  have hpmem := mem_stateBeforeTime_along₅₂ hf.sorted hW (M.proposal_time S.E s)
  have hvmem := mem_stateBeforeTime_along₅₂ hf.sorted hW (M.vote_time S.E s)
  have hn := mem_proposerReadAt_along₅₂ hf.sorted hW s cp hcp
  obtain ⟨hTs, hσs, -, -, -, -⟩ := tickStore_parts₅₂ facts S
    (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)) (M.proposal_time S.E s)
  obtain ⟨hTt0, hσt0, -, -, -, -⟩ := tickStore_parts₅₂ facts S
    (W (strictEventIndex rho (M.vote_time S.E s)) v) (M.vote_time S.E s)
  have hTt : (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
      (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core s).T =
      (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core.T := hTt0
  have hσt : (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
      (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core s).σ =
      (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core.σ := hσt0
  have hpropXb : S.E.proposer s ∈ Xb := hHsXb _ hprop
  have hvXb : v ∈ Xb := hHsXb _ hv
  have hcandT : ∀ T : Finset (Block V), M.voter_filtered_block_tree S.E
      (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st (M.vote_time S.E s)).core
      (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st
        (M.vote_time S.E s)).core.s ⇢ T → P.erase ∈ T := by
    intro T hT
    have hc := h.proposalCandidate T
    rw [facts.nd.mkNode_st] at hc
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at hc
    exact hc hT
  obtain ⟨T0, hT0⟩ := facts.fc.voter_filtered_block_tree_nonempty S.E
    (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st (M.vote_time S.E s)).core
    (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st (M.vote_time S.E s)).core.s
  have hproposalT : P.erase ∈ (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core.T := by
    have h' := facts.hd.Sts_voter_filtered_block_tree_subset _ _ _ T0 hT0 (hcandT T0 hT0)
    rw [voteRead_core₅₂ facts, hTt] at h'
    exact h'
  have hproposalHor : M.proposal_time S.E s ≤ rho.horizon :=
    le_trans (le_of_lt (facts.sch.proposal_time_lt_vote_time S.E s)) hvoteHor
  have hsourceSlot := proposalStore_s₅₂ facts S
    (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)) s
  have htargetSlot := voteStore_s₅₂ facts S (W (strictEventIndex rho (M.vote_time S.E s)) v) s
  have hrawOf : ∀ input : Protocol.ProposalInput V,
      Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
          (M.proposal_time S.E s))
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record cp).cache)
        S.E S.hc (S.node (S.E.proposer s)) (M.toHealing (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
          (M.proposal_time S.E s))
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record cp).st.core) ⇢ input →
      P.erase.gf_votes.toFinset =
        (M.proposer_view (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
            (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core
            (M.proposal_time S.E s))).toFG.toSG.toGoldfishStore
          (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
            (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core
            (M.proposal_time S.E s)).s).toFinset := by
    intro input hinput
    rw [Proofs.NamedWire.erase_goldfish_votes,
      Restated.Vocabulary.Protocol.proposedBlock_gf_votes facts S rho s _ hn hP input hinput,
      facts.dt.with_proposal_input_id_gf_votes _ _ _ _ _ input hinput, facts.sto.toHealing_s,
      facts.nd.mkNode_st]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    try rw [read_core₅₂ facts]
  have hsupportOf : ∀ input : Protocol.ProposalInput V,
      Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
          (M.proposal_time S.E s))
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record cp).cache)
        S.E S.hc (S.node (S.E.proposer s)) (M.toHealing (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
          (M.proposal_time S.E s))
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record cp).st.core) ⇢ input →
      ∀ psv : List (GoldfishVote V),
      M.proposer_support_view (M.toHealing (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
          (M.proposal_time S.E s))
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record cp).st.core
        ).toFG.toSG.toGoldfishStore (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
          (M.proposal_time S.E s))
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record cp).st.core.s ⇢ psv →
      P.erase.gf_support_votes.toFinset = psv.toFinset := by
    intro input hinput psv hpsv
    rw [Proofs.NamedWire.erase_goldfish_support,
      Restated.Vocabulary.Protocol.proposedBlock_gf_support_votes facts S rho s _ hn hP input hinput,
      facts.dt.with_proposal_input_id_gf_support_votes _ _ _ _ _ input hinput psv
        (by rw [facts.sto.toHealing_s]; exact hpsv)]
  have hTn : ∀ (j : Nat) (e : Record.Event V), j < strictEventIndex rho (M.vote_time S.E s) →
      rho.events[j]? = some e → e.time ≤ M.vote_time S.E s :=
    fun j e hj he => le_of_lt (time_lt_of_lt_strict₅₂ hf.sorted he hj)
  have hPslot : P.erase.slot = s := by
    rw [Proofs.NamedWire.erase_slot]
    exact Restated.Vocabulary.Proofs.HealingSurface.proposedBlockAt_slot facts S rho s _ ⟨_, hn, hP⟩ rfl
  refine { persist := ?_, reflect := ?_ }
  · intro input hinput psv hpsv srcScore hsrcScore srcEligible hsrcElig T hT vv hvv vsv hvsv
    dsimp only
    intro X C hpivotX _hXparent _hXne hstep hCparent
    have hraw := hrawOf input hinput
    have hsupp := hsupportOf input hinput psv hpsv
    have hpar := proposal_erase_parent₅₂ facts S s hn hP input hinput
    have hparentP := preceq_eq_true_iff_Preceq.mp (Protocol.preceq_of_parent? hpar)
    have hchild := facts.fc.ghost_step_child (some C) hstep rfl
    have hparent : C.parent? = some X := hchild.2.1
    have hXC : Block.Preceq X C :=
      preceq_eq_true_iff_Preceq.mp (Protocol.preceq_of_parent? hparent)
    have hCP : Block.Preceq C P.erase := preceq_trans_Preceq hCparent hparentP
    have hT' := hT
    rw [facts.nd.mkNode_st] at hT'
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at hT'
    have hpivotTarget := h.pivotTarget
    rw [facts.nd.mkNode_st] at hpivotTarget
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at hpivotTarget
    try rw [voteRead_core₅₂ facts] at hpivotTarget
    have hCtargetFrozen := Restated.voterCandidate_above_fullPivotOn facts S Hs Xb hf cp hcp hP T hT'
      (hcandT T hT') hpivotTarget (preceq_trans_Preceq hpivotX hXC) hCP
    have hCne : C ≠ P.erase := by
      intro heq
      have hproposalParent : Block.Preceq P.erase input.parent := by
        rw [← heq]; exact hCparent
      have heq' := Proofs.ModelProperties.Preceq_antisymm hproposalParent hparentP
      have hpar' := hpar
      rw [heq'] at hpar'
      have hdepth := Protocol.depth_of_parent? hpar'
      omega
    have hCsourceN := hchild.1
    have hCsource := hchild.1
    rw [facts.nd.mkNode_st] at hCsource
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at hCsource
    try rw [read_core₅₂ facts] at hCsource
    have hTv := hT'
    rw [voteRead_core₅₂ facts] at hTv
    have hCfullTarget := facts.fc.voter_filtered_block_tree_subset_filtered S.E _ T hTv hCtargetFrozen
    rw [facts.nd.mkNode_st] at hsrcScore hsrcElig
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at hsrcScore hsrcElig
    try rw [read_core₅₂ facts] at hsrcScore hsrcElig
    rw [facts.nd.mkNode_st] at hvv hvsv
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at hvv hvsv
    try rw [voteRead_core₅₂ facts] at hvv hvsv
    have hsourceT : C ∈ (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core.T := by
      have h' := facts.fc.get_filtered_block_tree_subset _ hCsource
      rw [facts.sto.toHealing_T, hTs] at h'
      exact h'
    have htargetT : C ∈ (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core.T := by
      have h' := facts.fc.get_filtered_block_tree_subset _ hCfullTarget
      rw [facts.sto.toHealing_T, hTt] at h'
      exact h'
    have hsourceParentT := mem_of_preceq_along₅₂ facts S hf.sorted hW _ _ hsourceT
      (preceq_eq_true_iff_Preceq.mp (preceq_parent C))
    have htargetParentT := mem_of_preceq_along₅₂ facts S hf.sorted hW _ _ htargetT
      (preceq_eq_true_iff_Preceq.mp (preceq_parent C))
    have hnotCurrent : C.slot ≠ (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core
        (M.proposal_time S.E s)).s := by
      rw [hsourceSlot]
      exact Nat.ne_of_lt (Restated.block_slot_lt_of_mem_before_proposalOn facts S Hs Xb hf hs hsourceT)
    have heligSource := (facts.fc.goldfish_eligible_iff _ _ _ _ _ _ _ _ C (srcEligible C)
      (hsrcElig C) (srcScore C) (hsrcScore C)).mp hchild.2.2
    refine ⟨Finset.mem_erase.mpr ⟨hCne, hCtargetFrozen⟩, ?_⟩
    rw [facts.nd.mkNode_st]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    try rw [voteRead_core₅₂ facts]
    intro b hb
    obtain ⟨g', hg'⟩ := facts.fc.goldfish_score_nonempty S.E
      (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core s).T vv vsv
      ((Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core s).s - 1) C
    rw [facts.fc.goldfish_eligible_iff _ _ _ _ _ _ _ _ C b hb g' hg']
    rcases heligSource with hlow | hmajority | hcurrent
    · rcases hfrontier with hmaxEq | hband
      · refine Or.inl (lt_of_eq_of_lt ?_ (lt_of_lt_of_eq hlow (by rw [hmaxEq])))
        rw [Restated.frozenSuffix_sigma_source_targetOn facts S Hs Xb hf hpropXb hvXb
          (by rw [hTs]; exact hsourceParentT) (by rw [hTt]; exact htargetParentT)]
      · have hpivotParent : Block.Preceq pivot C.parent := by
          rw [parent_eq_of_parent? hparent]
          exact hpivotX
        have hpivotSource := mem_of_preceq_along₅₂ facts S hf.sorted hW _ _ hsourceParentT hpivotParent
        have hmono := sigma_height_mono₅₂ facts S (M.proposal_time S.E s) (S.E.proposer s) _ hpmem
          hpivotSource hsourceParentT hpivotParent
        have hb := hband.1
        rw [hσs] at hb hlow
        exact False.elim ((not_lt_of_ge (le_trans hb hmono)) hlow)
    · right
      left
      have hvv' := hvv
      have hvsv' := hvsv
      rw [htargetSlot] at hvv' hvsv'
      obtain ⟨hcount, hscore⟩ := view_ext_eqs₅₂ facts S.E
        (hbridge C hCsourceN hCfullTarget vv hvv' vsv hvsv') (s - 1)
      have hs1 := hsrcScore C
      rw [← hraw, ← hsupp, hsourceSlot] at hs1
      rw [← hraw, hsourceSlot] at hmajority
      rw [htargetSlot] at hg'
      rw [htargetSlot, ← hcount, ← hscore _ hs1 _ hg']
      exact hmajority
    · exact False.elim (hnotCurrent hcurrent)
  · intro input hinput psv hpsv T hT vv hvv vsv hvsv
    dsimp only
    intro X C hpivotX _hXparent hCtarget hparent heligible
    have hraw := hrawOf input hinput
    have hsupp := hsupportOf input hinput psv hpsv
    have hT' := hT
    rw [facts.nd.mkNode_st] at hT'
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at hT'
    have hroot0 := fgRoot_preceq_of_anchors₅₂ facts S _ _ h.sourceAnchor
    rw [facts.nd.mkNode_st] at hroot0
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at hroot0
    try rw [read_core₅₂ facts] at hroot0
    have hCsource0 := Restated.targetChild_mem_sourceTree_of_frozenProposalOn facts
      S Hs Xb hf hHs hHsXb hs hpost hprop hv hproposalHor cp hcp hP hroot0 T hT' (hcandT T hT')
        (by
          rcases hfrontier with hmaxEq | hband
          · exact Or.inl (by rw [hmaxEq])
          · exact Or.inr hband.1)
        hpivotX hCtarget hparent
    have hCsourceN : C ∈ M.get_filtered_block_tree (M.toHealing (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
          (M.proposal_time S.E s))
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record cp).st.core).toFG := by
      rw [facts.nd.mkNode_st]
      try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
      exact hCsource0
    have hCsource := hCsource0
    rw [read_core₅₂ facts] at hCsource
    have hCne : C ≠ P.erase := (Finset.mem_erase.mp hCtarget).1
    have hCfrozen := (Finset.mem_erase.mp hCtarget).2
    have hTv := hT'
    rw [voteRead_core₅₂ facts] at hTv
    have hCfullTarget := facts.fc.voter_filtered_block_tree_subset_filtered S.E _ T hTv hCfrozen
    rw [facts.nd.mkNode_st] at heligible hvv hvsv
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at heligible hvv hvsv
    try rw [voteRead_core₅₂ facts] at heligible hvv hvsv
    have hsourceT : C ∈ (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core.T := by
      have h' := facts.fc.get_filtered_block_tree_subset _ hCsource
      rw [facts.sto.toHealing_T, hTs] at h'
      exact h'
    have htargetT : C ∈ (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core.T := by
      have h' := facts.fc.get_filtered_block_tree_subset _ hCfullTarget
      rw [facts.sto.toHealing_T, hTt] at h'
      exact h'
    have hsourceParentT := mem_of_preceq_along₅₂ facts S hf.sorted hW _ _ hsourceT
      (preceq_eq_true_iff_Preceq.mp (preceq_parent C))
    have htargetParentT := mem_of_preceq_along₅₂ facts S hf.sorted hW _ _ htargetT
      (preceq_eq_true_iff_Preceq.mp (preceq_parent C))
    have hnotCurrent : C.slot ≠ (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core s).s := by
      intro hcur
      rw [htargetSlot] at hcur
      exact hCne (Restated.unique_slot_block_in_store_beforeOn facts S Hs Xb hf hHs hs hprop hTn hTn
        htargetT hproposalT hcur hPslot)
    obtain ⟨g', hg'⟩ := facts.fc.goldfish_score_nonempty S.E
      (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core s).T vv vsv
      ((Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core s).s - 1) C
    have heligTarget := (facts.fc.goldfish_eligible_iff _ _ _ _ _ _ _ _ C true heligible g' hg').mp rfl
    refine ⟨hCsourceN, ?_⟩
    rw [facts.nd.mkNode_st]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    try rw [read_core₅₂ facts]
    intro b hb
    obtain ⟨g, hg⟩ := facts.fc.goldfish_score_nonempty S.E
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core
        (M.proposal_time S.E s)).T
      (M.proposer_view (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
          (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core
          (M.proposal_time S.E s))).toFG.toSG.toGoldfishStore
        (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
          (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core
          (M.proposal_time S.E s)).s).toFinset psv.toFinset
      ((Restated.Vocabulary.Proofs.Optimistic.tickStore M S
          (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core
          (M.proposal_time S.E s)).s - 1) C
    rw [facts.fc.goldfish_eligible_iff _ _ _ _ _ _ _ _ C b hb g hg]
    rcases heligTarget with hlow | hmajority | hcurrent
    · rcases hfrontier with hmaxEq | hband
      · refine Or.inl (lt_of_eq_of_lt ?_ (lt_of_lt_of_eq hlow (by rw [hmaxEq])))
        rw [Restated.frozenSuffix_sigma_source_targetOn facts S Hs Xb hf hpropXb hvXb
          (by rw [hTs]; exact hsourceParentT) (by rw [hTt]; exact htargetParentT)]
      · have hpivotParent : Block.Preceq pivot C.parent := by
          rw [parent_eq_of_parent? hparent]
          exact hpivotX
        have hpivotTarget := mem_of_preceq_along₅₂ facts S hf.sorted hW _ _ htargetParentT hpivotParent
        have hmono := sigma_height_mono₅₂ facts S (M.vote_time S.E s) v _ hvmem
          hpivotTarget htargetParentT hpivotParent
        have hb := hband.2
        rw [hσt] at hb hlow
        exact False.elim ((not_lt_of_ge (le_trans hb hmono)) hlow)
    · right
      left
      have hvv' := hvv
      have hvsv' := hvsv
      rw [htargetSlot] at hvv' hvsv'
      obtain ⟨hcount, hscore⟩ := view_ext_eqs₅₂ facts S.E
        (hbridge C hCsourceN hCfullTarget vv hvv' vsv hvsv') (s - 1)
      rw [htargetSlot] at hmajority hg'
      rw [← hraw, ← hsupp, hsourceSlot] at hg
      rw [← hraw, hsourceSlot, hcount, hscore _ hg _ hg']
      exact hmajority
    · exact False.elim (hnotCurrent hcurrent)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation

/-- Two run blocks read through `Xb` with the same root are equal. -/
theorem frozenSuffix_runBlock_unique_of_rootOn (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} {Hs : Int → Finset V} {Xb : Finset V} {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {A B : NamedBlock V} (hA : Restated.RunBlockOn M S rho W Xb A)
    (hB : Restated.RunBlockOn M S rho W Xb B)
    (hroot : A.root = B.root) : A = B :=
  hf.rootCollisionFree.root_injective
    A B hA hB A B (Or.inl (Proofs.NamedAncestry.named_self A))
      (Or.inr (Proofs.NamedAncestry.named_self B)) hroot

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation

/-- If `w ∈ Xb`, some store resolves `u`'s head to `H`, and `H` is in the tree of `w`'s core store
    in `W (strictEventIndex rho t)`, then that store resolves `u`'s head to `H`. -/
theorem frozenSuffix_find_of_find_and_memOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {w : V} (hw : w ∈ Xb) (t : Time)
    {source : M.S} {u : GoldfishVote V} {H : Block V}
    (hfind : Block.find? source.T u.head = some H)
    (hHmem : H ∈ (W (strictEventIndex rho t) w).st.core.T) :
    Block.find? (W (strictEventIndex rho t) w).st.core.T u.head = some H := by
  have hHroot : H.root = u.head := Proofs.HealingLemmas.find?_root hfind
  rw [← hHroot]
  refine Proofs.Optimistic.find?_eq_some_of_unique hHmem ?_
  intro Y hY hrootEq
  obtain ⟨Yn, hYe, hYrun⟩ :=
    Restated.runBlock_of_mem_core_T_stateBeforeTimeOn facts S Hs Xb hf hw t hY
  obtain ⟨Hn, hHe, hHrun⟩ :=
    Restated.runBlock_of_mem_core_T_stateBeforeTimeOn facts S Hs Xb hf hw t hHmem
  have hr : Yn.root = Hn.root := by
    rw [← Proofs.NamedWire.erase_root Yn, ← Proofs.NamedWire.erase_root Hn, hYe, hHe]
    exact hrootEq
  have heq : Yn = Hn := Restated.frozenSuffix_runBlock_unique_of_rootOn facts hf hYrun hHrun hr
  rw [← hYe, ← hHe, heq]

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation

/-- If the proposer of `s` and `v` are in `Xb`, and the proposal duty store of slot `s` and `v`'s
    vote duty store resolve `u`'s head to `H` and `K`, then `H = K`. -/
theorem frozenSuffix_resolved_blocks_eqOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {s : Slot} (hprop : S.E.proposer s ∈ Xb)
    {v : V} (hv : v ∈ Xb) {u : GoldfishVote V} {H K : Block V}
    (hH : Block.find? (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core
      (M.proposal_time S.E s)).T u.head = some H)
    (hK : Block.find? (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
      (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core s).T u.head = some K) :
    H = K := by
  have hHmem := Proofs.HealingLemmas.find?_mem hH
  rw [(tickStore_parts₅₂ facts S _ _).1] at hHmem
  have hKmem := Proofs.HealingLemmas.find?_mem hK
  rw [Restated.Vocabulary.Proofs.Optimistic.voteStore, (tickStore_parts₅₂ facts S _ _).1] at hKmem
  obtain ⟨Hn, hHe, hHrun⟩ :=
    Restated.runBlock_of_mem_core_T_stateBeforeTimeOn facts S Hs Xb hf hprop
      (M.proposal_time S.E s) hHmem
  obtain ⟨Kn, hKe, hKrun⟩ :=
    Restated.runBlock_of_mem_core_T_stateBeforeTimeOn facts S Hs Xb hf hv
      (M.vote_time S.E s) hKmem
  have hroot : Hn.root = Kn.root := by
    rw [← Proofs.NamedWire.erase_root Hn, ← Proofs.NamedWire.erase_root Kn, hHe, hKe]
    exact (Proofs.HealingLemmas.find?_root hH).trans (Proofs.HealingLemmas.find?_root hK).symm
  have heq : Hn = Kn := Restated.frozenSuffix_runBlock_unique_of_rootOn facts hf hHrun hKrun hroot
  rw [← hHe, ← hKe, heq]

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation

/-- Every outcome of `v`'s voter support view of slot `s` is a subset of every outcome of its voter
    view of `s`, both read on `v`'s vote duty store. -/
theorem frozenSuffix_voterSupport_subset_voterViewOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo) (v : V) (s : Slot) :
    ∀ Y : Finset (GoldfishVote V), M.voter_support_view S.E
        (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core s)).toFG.toSG.toGoldfishStore s ⇢ Y →
    ∀ Z : Finset (GoldfishVote V), M.voter_view S.E
        (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core s)).toFG.toSG.toGoldfishStore s ⇢ Z →
    Y ⊆ Z := by
  intro Y hY Z hZ
  refine facts.fc.voter_support_view_subset S.E _ s ?_ Y hY Z hZ
  intro B hB
  refine Restated.carried_support_subset_of_mem_T_coreOn facts S Hs Xb hf v
    (strictEventIndex rho (M.vote_time S.E s)) ?_
  rw [facts.sto.toHealing_gs_T, Restated.Vocabulary.Proofs.Optimistic.voteStore,
    (tickStore_parts₅₂ facts S _ _).1] at hB
  exact hB

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation

/-- If the finalized block of `w`'s core store in `W (strictEventIndex rho t)` is an ancestor of `C`
    and `C` of `H`'s erasure, then for every `i` up to the number of events before `t`, `w`'s
    finalized block in `W i` is an ancestor of `H`'s erasure. -/
theorem frozenSuffix_finalizedBelowAtDeliveries_of_preceqOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {w : V} {t : Time} {C : Block V} {H : NamedBlock V}
    (hFC : Block.Preceq (W (strictEventIndex rho t) w).st.core.F C)
    (hCH : Block.Preceq C H.erase) :
    ∀ i : Nat, i ≤ (rho.events.filter (fun e => decide (e.time < t))).length →
      Block.Preceq (W i w).st.core.F H.erase := by
  intro i hi
  exact preceq_trans_Preceq (F_mono_along₅₂ facts S hf.onePath w hi)
    (preceq_trans_Preceq hFC hCH)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation

/-- For `lo ≤ proposal_time (s − 1)`, if `C` is in the filtered block tree of `v`'s vote staging,
    the proposal duty store of slot `s` resolves `u`'s head to `H`, and `C` is an ancestor of `H`,
    then `v`'s vote staging resolves `u`'s head to `H` and stamped `H` before `vote_time s`. -/
theorem frozenSuffix_proposalTarget_visibleAtVoteOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {s : Slot}
    (hpost : lo ≤ M.proposal_time S.E (s - 1))
    (hprop : S.E.proposer s ∈ Hs (M.proposal_time S.E s))
    {v : V} (hv : v ∈ Hs (M.vote_time S.E s))
    (hhor : M.vote_time S.E s ≤ rho.horizon)
    {C : Block V}
    (hC : C ∈ M.get_filtered_block_tree
      (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core s)).toFG)
    {u : GoldfishVote V} {H : Block V}
    (hfind : Block.find? (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core
      (M.proposal_time S.E s)).T u.head = some H)
    (hCH : Block.Preceq C H) :
    Block.find? (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core s).T u.head = some H ∧
      stampedBefore (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core s).timestamp_block
        (M.vote_time S.E s) H = true := by
  have hW := hf.onePath
  have hpmem := mem_stateBeforeTime_along₅₂ hf.sorted hW (M.proposal_time S.E s)
  have hvXb : v ∈ Xb := hHsXb _ hv
  obtain ⟨hTs, -, -, -, -, -⟩ := tickStore_parts₅₂ facts S
    (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)) (M.proposal_time S.E s)
  obtain ⟨hTt, -, hFt, -, -, hTBt⟩ := tickStore_parts₅₂ facts S
    (W (strictEventIndex rho (M.vote_time S.E s)) v) (M.vote_time S.E s)
  have hFC : Block.Preceq (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core.F C := by
    rw [← hFt]
    exact F_preceq_of_mem_filtered₅₂ facts _ hC
  rw [Restated.Vocabulary.Proofs.Optimistic.voteStore, hTt, hTBt]
  have hHsource : H ∈ (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core.T := by
    have h' := Proofs.HealingLemmas.find?_mem hfind
    rwa [hTs] at h'
  obtain ⟨Hn, hHnbody, hHne⟩ :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime facts S rho
      (M.proposal_time S.E s) (S.E.proposer s) _ hpmem hHsource
  have hprocessed : Restated.Vocabulary.Execution.Object.processed M
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
        (NamedObject.block Hn) = true := by
    simpa only [Restated.Vocabulary.Execution.Object.processed, decide_eq_true_eq] using hHnbody
  rcases Restated.Vocabulary.Protocol.acceptsAt_block_of_processed facts S rho (S.E.proposer s) W hW
      (strictEventIndex rho (M.proposal_time S.E s)) Hn hprocessed with hgen | ⟨i, hi, t, hacc⟩
  · have hHgen : H = Block.genesis := by rw [← hHne, hgen, erase_named_genesis]
    have hvisible := Restated.genesis_mem_and_stamp_storeBeforeTimeOn facts S Hs Xb hf v
      (M.vote_time S.E s) (M.vote_time S.E s)
    refine ⟨?_, ?_⟩
    · exact Restated.frozenSuffix_find_of_find_and_memOn facts S Hs Xb hf hvXb
        (M.vote_time S.E s) hfind (by rw [hHgen]; exact hvisible.1)
    · rw [hHgen]; exact hvisible.2
  · obtain ⟨-, e, he, -, het⟩ := hacc.1
    have ht : t < M.proposal_time S.E s := by
      rw [← het]
      exact time_lt_of_lt_strict₅₂ hf.sorted he hi
    have hpostS : lo ≤ M.proposal_time S.E s :=
      hpost.trans (facts.sch.proposal_time_mono S.E (Nat.sub_le s 1))
    have hpropVote := proposal_add_delta_le_vote₅₂ facts S s
    have hFhist := Restated.frozenSuffix_finalizedBelowAtDeliveries_of_preceqOn facts S Hs Xb hf
      (w := v) (t := M.vote_time S.E s) hFC (by rw [hHne]; exact hCH)
    have hHpos : 0 < Hn.slot := by
      rw [← Proofs.NamedWire.erase_slot]
      exact Nat.zero_lt_of_lt
        (Restated.Vocabulary.Protocol.parent_slot_lt_of_acceptsAt_block facts S W hW hacc)
    have hpmax : S.E.proposer s ∈ Hs (max t lo) :=
      hHs _ _ (max_le (le_of_lt ht) hpostS) hprop
    have hadmit : Restated.Vocabulary.Protocol.AdmittedBefore M S rho W v Hn.erase
        (M.vote_time S.E s) :=
      Restated.block_admittedBefore_of_accepted_after_cutoff_coreOn facts
        S Hs Xb hf hHs hHsXb hpmax hv hHpos hacc
          (lt_of_lt_of_le ht (le_sub_of_add_le₅₂ hpropVote))
          (hpostS.trans (le_sub_of_add_le₅₂ hpropVote)) (Int.sub_add_cancel _ _) hhor hFhist
    have hvisible := Restated.admittedBefore_mem_and_stamp_atOn facts S Hs Xb hf hadmit (le_refl _)
    rw [hHne] at hvisible
    exact ⟨Restated.frozenSuffix_find_of_find_and_memOn facts S Hs Xb hf hvXb
      (M.vote_time S.E s) hfind hvisible.1, hvisible.2⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation

/-- For `0 < s` and `lo ≤ proposal_time (s − 1)`, if `C` is in the filtered block tree of the
    proposal duty store of slot `s`, `v`'s vote staging resolves `u`'s head to `H` and stamped `H`
    before `view_freeze (s − 1)`, and `C` is an ancestor of `H`, then the proposal duty store
    resolves `u`'s head to `H`. -/
theorem frozenSuffix_voterTarget_visibleAtProposalOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {s : Slot} (hs : 0 < s)
    (hpost : lo ≤ M.proposal_time S.E (s - 1))
    (hprop : S.E.proposer s ∈ Hs (M.proposal_time S.E s))
    {v : V} (hv : v ∈ Hs (M.vote_time S.E s))
    (hhor : M.proposal_time S.E s ≤ rho.horizon)
    {C : Block V}
    (hC : C ∈ M.get_filtered_block_tree
      (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core
        (M.proposal_time S.E s))).toFG)
    {u : GoldfishVote V} {H : Block V}
    (hfind : Block.find? (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
      (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core s).T u.head = some H)
    (hHstamp : stampedBefore
      (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core s).timestamp_block
      (M.view_freeze S.E (s - 1)) H = true)
    (hCH : Block.Preceq C H) :
    Block.find? (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core
      (M.proposal_time S.E s)).T u.head = some H := by
  have hW := hf.onePath
  have hvmem := mem_stateBeforeTime_along₅₂ hf.sorted hW (M.vote_time S.E s)
  have hpropXb : S.E.proposer s ∈ Xb := hHsXb _ hprop
  obtain ⟨hTs, -, hFs, -, -, -⟩ := tickStore_parts₅₂ facts S
    (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)) (M.proposal_time S.E s)
  obtain ⟨hTt, -, -, -, -, hTBt⟩ := tickStore_parts₅₂ facts S
    (W (strictEventIndex rho (M.vote_time S.E s)) v) (M.vote_time S.E s)
  have hFC : Block.Preceq
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core.F C := by
    rw [← hFs]
    exact F_preceq_of_mem_filtered₅₂ facts _ hC
  rw [hTs]
  have hHtarget : H ∈ (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core.T := by
    have h' := Proofs.HealingLemmas.find?_mem hfind
    rwa [Restated.Vocabulary.Proofs.Optimistic.voteStore, hTt] at h'
  obtain ⟨Hn, hHnbody, hHne⟩ :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime facts S rho
      (M.vote_time S.E s) v _ hvmem hHtarget
  have hstampn : stampedBefore (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core.timestamp_block
      (M.view_freeze S.E (s - 1)) Hn.erase = true := by
    rw [hHne, ← hTBt]
    exact hHstamp
  have hprocessed : Restated.Vocabulary.Execution.Object.processed M
      (W (strictEventIndex rho (M.vote_time S.E s)) v).st (NamedObject.block Hn) = true := by
    simpa only [Restated.Vocabulary.Execution.Object.processed, decide_eq_true_eq] using hHnbody
  obtain ⟨hfreezeHop, hpropFreeze, hfreezeVote⟩ := freeze_facts₅₂ facts S hs
  have hpostFreeze : lo ≤ M.view_freeze S.E (s - 1) := hpost.trans hpropFreeze
  have hfind' : Block.find? (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core.T u.head =
      some H := by
    rw [← hTt]; exact hfind
  rcases Restated.Vocabulary.Protocol.acceptsAt_block_of_processed facts S rho v W hW
      (strictEventIndex rho (M.vote_time S.E s)) Hn hprocessed with hgen | ⟨i, hi, t, hacc⟩
  · have hHgen : H = Block.genesis := by rw [← hHne, hgen, erase_named_genesis]
    have hvisible := Restated.genesis_mem_and_stamp_storeBeforeTimeOn facts S Hs Xb hf
      (S.E.proposer s) (M.proposal_time S.E s) (M.proposal_time S.E s)
    exact Restated.frozenSuffix_find_of_find_and_memOn facts S Hs Xb hf hpropXb
      (M.proposal_time S.E s) hfind' (by rw [hHgen]; exact hvisible.1)
  · have ht : t < M.view_freeze S.E (s - 1) :=
      Restated.acceptsAt_block_lt_of_stamp_before_coreOn facts S Hs Xb hf hacc
        (Nat.succ_le_of_lt hi)
        (Restated.Vocabulary.Protocol.publicTime_view_freeze facts S (s - 1)) (hHs _ _ hfreezeVote hv)
        hpostFreeze hstampn
    have hFhist := Restated.frozenSuffix_finalizedBelowAtDeliveries_of_preceqOn facts S Hs Xb hf
      (w := S.E.proposer s) (t := M.proposal_time S.E s) hFC
        (by rw [hHne]; exact hCH)
    have hHpos : 0 < Hn.slot := by
      rw [← Proofs.NamedWire.erase_slot]
      exact Nat.zero_lt_of_lt
        (Restated.Vocabulary.Protocol.parent_slot_lt_of_acceptsAt_block facts S W hW hacc)
    have hvmax : v ∈ Hs (max t lo) :=
      hHs _ _ (le_trans (max_le (le_of_lt ht) hpostFreeze) hfreezeVote) hv
    have hadmit : Restated.Vocabulary.Protocol.AdmittedBefore M S rho W (S.E.proposer s) Hn.erase
        (M.proposal_time S.E s) :=
      Restated.block_admittedBefore_of_accepted_after_cutoff_coreOn facts
        S Hs Xb hf hHs hHsXb hvmax hprop hHpos hacc
          (lt_of_lt_of_le ht (le_sub_of_add_le₅₂ hfreezeHop))
          (hpostFreeze.trans (le_sub_of_add_le₅₂ hfreezeHop)) (Int.sub_add_cancel _ _) hhor hFhist
    have hvisible := Restated.admittedBefore_mem_and_stamp_atOn facts S Hs Xb hf hadmit (le_refl _)
    rw [hHne] at hvisible
    exact Restated.frozenSuffix_find_of_find_and_memOn facts S Hs Xb hf hpropXb
      (M.proposal_time S.E s) hfind' hvisible.1

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation

/-- The candidate score bridge: for `0 < s` and `lo ≤ proposal_time (s − 1)`, if the proposal at
    slot `s` can be `P` and `P`'s erasure is in the filtered block tree of `v`'s vote staging, then
    `NamedProposalCandidateScoreBridge` holds at the proposer's read and the two duty stores. -/
theorem namedProposalCandidateScoreBridge_afterGST_coreOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {s : Slot} (hs : 0 < s)
    (hpost : lo ≤ M.proposal_time S.E (s - 1))
    (hprop : S.E.proposer s ∈ Hs (M.vote_time S.E s))
    {v : V} (hv : v ∈ Hs (M.vote_time S.E s))
    (hhor : M.vote_time S.E s ≤ rho.horizon)
    {P : NamedBlock V}
    (cp : M.Cache)
    (hcp : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core.toHealing
      (M.proposal_time S.E s) (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).cache
      ⇢ cp)
    (hP : M.proposal_with
      (M.gradeContract (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
          (M.proposal_time S.E s))
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record cp).cache)
      .poolAndCarried S.E S.hc (S.node (S.E.proposer s))
      (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
          (M.proposal_time S.E s))
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record cp).st ⇢ some P)
    (hproposal : P.erase ∈ M.get_filtered_block_tree
      (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core s)).toFG) :
    Restated.Vocabulary.Proofs.HealingSurface.NamedProposalCandidateScoreBridge M S rho s v P
      (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
          (M.proposal_time S.E s))
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record cp)
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core
        (M.proposal_time S.E s))
      (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core s) := by
  have hW := hf.onePath
  have hn := mem_proposerReadAt_along₅₂ hf.sorted hW s cp hcp
  obtain ⟨hTt0, -, -, -, -, -⟩ := tickStore_parts₅₂ facts S
    (W (strictEventIndex rho (M.vote_time S.E s)) v) (M.vote_time S.E s)
  have hTt : (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
      (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core s).T =
      (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core.T := hTt0
  have hpropProposal : S.E.proposer s ∈ Hs (M.proposal_time S.E s) :=
    hHs _ _ (le_of_lt (facts.sch.proposal_time_lt_vote_time S.E s)) hprop
  have hproposalHor : M.proposal_time S.E s ≤ rho.horizon :=
    le_trans (le_of_lt (facts.sch.proposal_time_lt_vote_time S.E s)) hhor
  obtain ⟨cv, hcv⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc
    (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core.toHealing (M.vote_time S.E s)
    (W (strictEventIndex rho (M.vote_time S.E s)) v).cache
  have hrawExtra := Restated.voter_raw_extra_equivocates_proposal_afterGST_coreOn facts
    S Hs Xb hf hHs hs hpost hprop hv hproposalHor cp hcp hP cv hcv
    (by rw [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [voteRead_core₅₂ facts]; exact hproposal)
  rw [facts.nd.mkNode_st] at hrawExtra
  try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at hrawExtra
  rw [voteRead_core₅₂ facts] at hrawExtra
  have hBvoteH := facts.fc.get_filtered_block_tree_subset _ hproposal
  have hBvote : P.erase ∈ (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core.T := by
    have h' := hBvoteH
    rw [facts.sto.toHealing_T, hTt] at h'
    exact h'
  have hPslot : P.erase.slot = s := by
    rw [Proofs.NamedWire.erase_slot]
    exact Restated.Vocabulary.Proofs.HealingSurface.proposedBlockAt_slot facts S rho s _ ⟨_, hn, hP⟩ rfl
  have hsourceSlot := proposalStore_s₅₂ facts S
    (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)) s
  obtain ⟨input, hinput⟩ := facts.dt.with_proposal_input_nonempty
    (M.gradeContract (M.mkNode
      (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
        (M.proposal_time S.E s))
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record cp).cache)
    S.E S.hc (S.node (S.E.proposer s))
    (M.toHealing (M.mkNode
      (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
        (M.proposal_time S.E s))
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record cp).st.core)
  obtain ⟨psv, hpsv⟩ := facts.fc.proposer_support_view_nonempty
    (M.toHealing (M.mkNode
      (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
        (M.proposal_time S.E s))
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record cp).st.core
      ).toFG.toSG.toGoldfishStore
    (M.mkNode
      (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
        (M.proposal_time S.E s))
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record cp).st.core.s
  have hraw : P.erase.gf_votes.toFinset =
      (M.proposer_view (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
          (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core
          (M.proposal_time S.E s))).toFG.toSG.toGoldfishStore
        (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
          (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core
          (M.proposal_time S.E s)).s).toFinset := by
    rw [Proofs.NamedWire.erase_goldfish_votes,
      Restated.Vocabulary.Protocol.proposedBlock_gf_votes facts S rho s _ hn hP input hinput,
      facts.dt.with_proposal_input_id_gf_votes _ _ _ _ _ input hinput, facts.sto.toHealing_s,
      facts.nd.mkNode_st]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    try rw [read_core₅₂ facts]
  have hsupport : P.erase.gf_support_votes.toFinset = psv.toFinset := by
    rw [Proofs.NamedWire.erase_goldfish_support,
      Restated.Vocabulary.Protocol.proposedBlock_gf_support_votes facts S rho s _ hn hP input hinput,
      facts.dt.with_proposal_input_id_gf_support_votes _ _ _ _ _ input hinput psv
        (by rw [facts.sto.toHealing_s]; exact hpsv)]
  have hpsvT : M.proposer_support_view (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
          (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core
          (M.proposal_time S.E s))).toFG.toSG.toGoldfishStore
        (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
          (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core
          (M.proposal_time S.E s)).s ⇢ psv := by
    simpa only [facts.nd.mkNode_st, read_core₅₂ facts, facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] using hpsv
  have hvalid := Restated.proposerDutyStore_proposer_view_valid_coreOn facts S Hs Xb hf s
  have hslots : ∀ u ∈ P.erase.gf_votes, u.slot + 1 = P.erase.slot := by
    intro u hu
    have hmem : u ∈ (M.proposer_view (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
          (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core
          (M.proposal_time S.E s))).toFG.toSG.toGoldfishStore
        (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
          (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core
          (M.proposal_time S.E s)).s).toFinset := by
      rw [← hraw]
      exact List.mem_toFinset.mpr hu
    have hslot := (hvalid u hmem).1
    rw [hsourceSlot] at hslot
    rw [hPslot, hslot]
    exact Nat.succ_pred_eq_of_pos hs
  have hTn : ∀ (j : Nat) (e : Record.Event V), j < strictEventIndex rho (M.vote_time S.E s) →
      rho.events[j]? = some e → e.time ≤ M.vote_time S.E s :=
    fun j e hj he => le_of_lt (time_lt_of_lt_strict₅₂ hf.sorted he hj)
  intro C hCsource hCtarget Y hY Z hZ
  have hCsrc := hCsource
  rw [facts.nd.mkNode_st] at hCsrc
  try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at hCsrc
  try rw [read_core₅₂ facts] at hCsrc
  refine
    { raw_subset := facts.fc.carried_raw_subset_voter_view S.E _ hBvoteH hPslot hslots Y hY
      raw_extra_equiv := hrawExtra Y hY
      forward := ?_
      backward := ?_ }
  · intro u hu b hb htrue
    obtain ⟨H, hfindSource, hHslot, hCH⟩ := (facts.fc.targets_under_iff b hb).mp htrue
    have hvis := Restated.frozenSuffix_proposalTarget_visibleAtVoteOn facts
      S Hs Xb hf hHs hHsXb hpost hpropProposal hv hhor hCtarget hfindSource
      (preceq_eq_true_iff_Preceq.mp hCH)
    obtain ⟨rb, hrb⟩ := facts.sto.resolved_nonempty (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core s).T u
    have hrbt : rb = true := (facts.sto.resolved_eq_true_iff _ u rb hrb).mpr ⟨H, hvis.1, hHslot⟩
    subst hrbt
    have hresolved : M.resolved (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core s)).toFG.toSG.toGoldfishStore.T
        u ⇢ true := by
      rw [facts.sto.toHealing_T]
      exact hrb
    have huslot : u.slot + 1 = P.erase.slot :=
      hslots u (Restated.carried_support_subset_of_mem_T_coreOn facts S Hs Xb hf v
        (strictEventIndex rho (M.vote_time S.E s)) hBvote u (List.mem_toFinset.mp hu))
    exact Or.inl ⟨Restated.Vocabulary.Protocol.mem_voter_support_view_of_carried facts S.E
      _ hBvoteH hPslot (List.mem_toFinset.mp hu) hresolved huslot Z hZ,
      fun b' hb' => (facts.fc.targets_under_iff b' hb').mpr ⟨H, hvis.1, hHslot, hCH⟩⟩
  · intro u hu b hb htrue
    have huRaw := Restated.frozenSuffix_voterSupport_subset_voterViewOn facts S Hs Xb hf v s Z hZ Y hY hu
    obtain ⟨rb, hrb⟩ := facts.sto.resolved_nonempty (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core s)).toFG.toSG.toGoldfishStore.T u
    obtain ⟨rs, hrs⟩ := facts.sto.resolved_nonempty (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
          (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core
          (M.proposal_time S.E s)).T u
    have hrs' : M.resolved (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
          (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core
          (M.proposal_time S.E s))).toFG.toSG.toGoldfishStore.T u ⇢ rs := by
      rw [facts.sto.toHealing_T]; exact hrs
    rcases facts.fc.voter_support_view_cases S.E _ _ Z hZ hu rb hrb with
      ⟨_hpool, X0, hfind0, -, -, σ0, -, hσ0, -, hσlt⟩ | ⟨B, hBT, hBs, huB, -, -⟩
    · by_cases huSource : u ∈ P.erase.gf_votes.toFinset
      · obtain ⟨K, hfindTarget, hKslot, hCK⟩ := (facts.fc.targets_under_iff b hb).mp htrue
        have hX0K : X0 = K := by
          rw [facts.sto.toHealing_gs_T, hfindTarget] at hfind0
          exact (Option.some.inj hfind0).symm
        have hKstamp : stampedBefore
            (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
              (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core s).timestamp_block
            (M.view_freeze S.E (s - 1)) K = true := by
          rw [facts.sto.toHealing_gs_timestamp_block, hX0K] at hσ0
          exact stampedBefore_of_lt hσ0 hσlt
        have hfindSource := Restated.frozenSuffix_voterTarget_visibleAtProposalOn facts
          S Hs Xb hf hHs hHsXb hs hpost hpropProposal hv hproposalHor hCsrc hfindTarget
          hKstamp (preceq_eq_true_iff_Preceq.mp hCK)
        have huSourceList : u ∈ (M.proposer_view
            (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
              (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core
              (M.proposal_time S.E s))).toFG.toSG.toGoldfishStore
            (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
              (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core
              (M.proposal_time S.E s)).s) := by
          have hmem := huSource
          rw [hraw] at hmem
          exact List.mem_toFinset.mp hmem
        have huSupport : u ∈ P.erase.gf_support_votes.toFinset := by
          rw [hsupport, List.mem_toFinset, facts.fc.mem_proposer_support_view_iff _ _ u psv hpsvT rs hrs']
          rw [facts.fc.proposer_view_eq] at huSourceList
          refine ⟨huSourceList, ?_⟩
          exact (facts.sto.resolved_eq_true_iff _ u rs hrs).mpr ⟨K, hfindSource, hKslot⟩
        exact Or.inl ⟨huSupport,
          fun b' hb' => (facts.fc.targets_under_iff b' hb').mpr ⟨K, hfindSource, hKslot, hCK⟩⟩
      · exact Or.inr (hrawExtra Y hY u huRaw huSource)
    · have hBprefix' : B ∈ (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core.T := by
        rw [facts.sto.toHealing_gs_T, hTt] at hBT
        exact hBT
      have hBeq : B = P.erase :=
        Restated.unique_slot_block_in_store_beforeOn facts S Hs Xb hf hHs hs hprop hTn hTn
          hBprefix' hBvote hBs hPslot
      subst hBeq
      have huSource : u ∈ P.erase.gf_support_votes.toFinset := List.mem_toFinset.mpr huB
      obtain ⟨K, hfindTarget, hKslot, hCK⟩ := (facts.fc.targets_under_iff b hb).mp htrue
      have hmem := huSource
      rw [hsupport, List.mem_toFinset, facts.fc.mem_proposer_support_view_iff _ _ u psv hpsvT rs hrs']
        at hmem
      obtain ⟨H, hfindSource, -⟩ := (facts.sto.resolved_eq_true_iff _ u rs hrs).mp hmem.2
      have hHK : H = K :=
        Restated.frozenSuffix_resolved_blocks_eqOn facts S Hs Xb hf (hHsXb _ hprop) (hHsXb _ hv)
          hfindSource hfindTarget
      have hHslot : H.slot ≤ u.slot := by
        simpa only [← hHK] using hKslot
      have hHC : C.preceq H = true := by
        simpa only [← hHK] using hCK
      exact Or.inl ⟨huSource,
        fun b' hb' => (facts.fc.targets_under_iff b' hb').mpr ⟨H, hfindSource, hHslot, hHC⟩⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation

/-- The candidate score bridge `namedProposalCandidateScoreBridge_afterGST_coreOn`, under the same
    hypotheses. -/
theorem namedProposalCandidateScoreBridge_afterGSTOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {s : Slot} (hs : 0 < s)
    (hpost : lo ≤ M.proposal_time S.E (s - 1))
    (hprop : S.E.proposer s ∈ Hs (M.vote_time S.E s))
    {v : V} (hv : v ∈ Hs (M.vote_time S.E s))
    (hhor : M.vote_time S.E s ≤ rho.horizon)
    {P : NamedBlock V}
    (cp : M.Cache)
    (hcp : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core.toHealing
      (M.proposal_time S.E s) (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).cache
      ⇢ cp)
    (hP : M.proposal_with
      (M.gradeContract (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
          (M.proposal_time S.E s))
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record cp).cache)
      .poolAndCarried S.E S.hc (S.node (S.E.proposer s))
      (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
          (M.proposal_time S.E s))
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record cp).st ⇢ some P)
    (hproposal : P.erase ∈ M.get_filtered_block_tree
      (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core s)).toFG) :
    Restated.Vocabulary.Proofs.HealingSurface.NamedProposalCandidateScoreBridge M S rho s v P
      (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
          (M.proposal_time S.E s))
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record cp)
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core
        (M.proposal_time S.E s))
      (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core s) :=
  Restated.namedProposalCandidateScoreBridge_afterGST_coreOn facts
    S Hs Xb hf hHs hHsXb hs hpost hprop hv hhor cp hcp hP hproposal

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation

/-- For `0 < s` and `lo ≤ proposal_time (s − 1)`, if the proposal at slot `s` can be `P` and the
    frozen suffix inputs hold, then the proposal suffix transfers in both directions between the
    proposer's read and `v`'s read. -/
theorem namedProposalPivotSuffixTransfer_of_frozenProposalNoRiseOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {s : Slot} (hs : 0 < s)
    (hpost : lo ≤ M.proposal_time S.E (s - 1))
    (hprop : S.E.proposer s ∈ Hs (M.vote_time S.E s))
    {v : V} (hv : v ∈ Hs (M.vote_time S.E s))
    (hvoteHor : M.vote_time S.E s ≤ rho.horizon)
    {pivot : Block V} {P : NamedBlock V}
    (cp : M.Cache)
    (hcp : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core.toHealing
      (M.proposal_time S.E s) (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).cache
      ⇢ cp)
    (hP : M.proposal_with
      (M.gradeContract (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
          (M.proposal_time S.E s))
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record cp).cache)
      .poolAndCarried S.E S.hc (S.node (S.E.proposer s))
      (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
          (M.proposal_time S.E s))
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record cp).st ⇢ some P)
    (cv : M.Cache)
    (hcv : M.onPhaseTick S.E S.hc (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core.toHealing
      (M.vote_time S.E s) (W (strictEventIndex rho (M.vote_time S.E s)) v).cache ⇢ cv)
    (h : Restated.Vocabulary.Proofs.HealingSurface.NamedFrozenProposalSuffixInputs M S rho s pivot v P
      (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
          (M.proposal_time S.E s))
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record cp)
      (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st
        (M.vote_time S.E s)) (W (strictEventIndex rho (M.vote_time S.E s)) v).record cv)) :
    Restated.Vocabulary.Proofs.HealingSurface.NamedProposalPivotSuffixTransfer M S rho s pivot v P
      (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
          (M.proposal_time S.E s))
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record cp)
      (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st
        (M.vote_time S.E s)) (W (strictEventIndex rho (M.vote_time S.E s)) v).record cv) := by
  obtain ⟨T0, hT0⟩ := facts.fc.voter_filtered_block_tree_nonempty S.E
    (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st
      (M.vote_time S.E s)) (W (strictEventIndex rho (M.vote_time S.E s)) v).record cv).st.core
    (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st
      (M.vote_time S.E s)) (W (strictEventIndex rho (M.vote_time S.E s)) v).record cv).st.core.s
  have hPT := h.proposalCandidate T0 hT0
  rw [facts.nd.mkNode_st] at hT0
  try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at hT0
  rw [voteRead_core₅₂ facts] at hT0
  have hsame := h.sameHMax
  rw [facts.nd.mkNode_st] at hsame
  try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at hsame
  rw [facts.nd.mkNode_st] at hsame
  try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at hsame
  rw [voteRead_core₅₂ facts, read_core₅₂ facts] at hsame
  exact Restated.namedProposalPivotSuffixTransfer_of_core_of_scoreBridgeOn facts
    S Hs Xb hf hHs hHsXb hs hpost hprop hv hvoteHor cp hcp hP cv hcv
      h.toNamedFrozenProposalSuffixCoreInputs
      (Restated.namedProposalCandidateScoreBridge_afterGSTOn facts S Hs Xb hf hHs hHsXb hs
        hpost hprop hv hvoteHor cp hcp hP
        (facts.fc.voter_filtered_block_tree_subset_filtered S.E _ T0 hT0 hPT))
      (Or.inl hsame)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open Proofs.HealingLemmas

/-- If `v` is in the set for `S.a r`, awake at `r`, `lo ≤ S.a r`, and `v`'s tick at `S.a r` has an
    outcome, then `v` emits along `W` at `S.a r`, for every node state of its action read and every
    outcome of the attestation duty, an attestation whose SG projection is `⟨v, r, some B.root⟩` for
    every block `B` the SG selector can pick. -/
theorem honest_emits_actionAttestationAt_of_awakeOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} (r : Round) (hv : v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)))
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ rho.horizon) (hA : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick v (Restated.Vocabulary.Execution.Setup.a M S r)) → M.awake_for_grade2 S v (W j v) r)
    (hgat : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S r))
    (hneTick : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick v (Restated.Vocabulary.Execution.Setup.a M S r)) →
      ∃ out : M.N × List (NamedObject V), M.tick S v (W j v) (Restated.Vocabulary.Execution.Setup.a M S r) ⇢ out) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r,
      let gc := M.gradeContract n.cache
      let st := M.toHealing n.st.core
      let k := M.round_of S.hc st.s
      ∀ D, M.duties_attest_with gc S.E S.hc (S.node v) n.st n.record ⇢ D →
        Restated.Vocabulary.Execution.Run.emits M S rho W v (Object.attest D.2.2)
            (Restated.Vocabulary.Execution.Setup.a M S r) ∧
          ∀ A2, M.grade2_block_with gc S.E S.hc st k ⇢ A2 →
          ∀ B, M.get_sg_vote_with gc S.E S.hc st k A2 ⇢ B →
            M.sgVote D.2.2.erase = (⟨v, r, some B.root⟩ : Protocol.SGVote V) := by
  intro n hn gc st k D hD
  exact ⟨Restated.honest_emits_exact_actionAttestationAt_of_awakeOn facts S Hs Xb hf r hv hA hhor
      hgat hneTick n hn D hD,
    Restated.Vocabulary.Proofs.HealingSurface.sgVote_actionAttestationAt facts S rho v r _
      (mem_stateBeforeTime_along₅₂ hf.sorted hf.onePath _) n hn D hD⟩

end

/-! ### Helpers about event indices and paths -/

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Proofs.HealingSurface
open scoped DC

omit [DecidableEq V] [Fintype V] in
/-- In a run sorted by key, an event among the first `strictEventIndex rho t` events is at a time
    before `t`. -/
private theorem time_lt_of_lt_strict₅₂b {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {j : Nat} {e : Record.Event V} (he : rho.events[j]? = some e) {t : Time}
    (hj : j < strictEventIndex rho t) : e.time < t := by
  have hpre : rho.events.filter (fun f => decide (f.time < t)) =
      rho.events.take (rho.events.filter (fun f => decide (f.time < t))).length := by
    refine List.prefix_iff_eq_take.mp ?_
    rw [DecoupledConsensusModel.Proofs.Bridges.filter_eq_takeWhile_of_pairwise
      (R := fun e f => Record.Event.key e ≤ Record.Event.key f) ?_ _ hsorted]
    · exact List.takeWhile_prefix _
    · intro e' f hk hf
      simp only [decide_eq_true_eq] at hf ⊢
      exact lt_of_le_of_lt (Restated.time_le_of_key_le hk) hf
  have hj' : j < (rho.events.filter (fun f => decide (f.time < t))).length := hj
  have hmem : e ∈ rho.events.filter (fun f => decide (f.time < t)) := by
    rw [hpre]
    exact List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hj']; exact he)
  simpa only [decide_eq_true_eq] using (List.mem_filter.mp hmem).2

omit [DecidableEq V] [Fintype V] in
/-- In a run sorted by key, an event at index `j` with a time before `t` is among the first
    `strictEventIndex rho t` events. -/
private theorem lt_strict_of_time_lt₅₂b {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {j : Nat} {e : Record.Event V} (he : rho.events[j]? = some e) {t : Time} (ht : e.time < t) :
    j < strictEventIndex rho t := by
  by_contra hnot
  exact absurd ht (not_lt.mpr
    (Restated.le_time_of_index_ge_of_sorted hsorted
      (Nat.le_of_not_gt hnot) he))

/-- Along a path `W` of `rho`, `W (m + k)` is among the worlds the events `m` to `m + k - 1` lead to
    from `W m`. -/
private theorem onePath_reach₅₂b {S : Setup V} {rho : Record.Run V}
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

/-- Along a path `W` of `rho`, for `m ≤ n`, `W n` is among the worlds the events `m` to `n - 1` lead
    to from `W m`. -/
private theorem onePath_slice₅₂b {S : Setup V} {rho : Record.Run V}
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) {m n : Nat}
    (hmn : m ≤ n) :
    W n ∈ ((rho.events.drop m).take (n - m)).foldlM (Record.worldStepOf M S) (W m) := by
  have h := onePath_reach₅₂b W hW m (n - m)
  rwa [Nat.add_sub_of_le hmn] at h

/-- In a run sorted by key, the worlds strictly before `t` are the worlds before the event of index
    `strictEventIndex rho t`. -/
private theorem stateBeforeTime_eq_strict₅₂b (S : Setup V) (rho : Record.Run V)
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f)) (t : Time) :
    Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t =
      Record.stateBeforeOf M S rho (strictEventIndex rho t) :=
  stateBeforeTime_eq_strict₅₂ S rho hsorted t

/-- In a run sorted by key, the world `W (strictEventIndex rho t)` of a path `W` is a world strictly
    before `t`. -/
private theorem mem_stateBeforeTime_path₅₂b (S : Setup V) (rho : Record.Run V)
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (t : Time) :
    W (strictEventIndex rho t) ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t := by
  rw [stateBeforeTime_eq_strict₅₂b S rho hsorted t]
  exact (hW _).1

/-- In a run sorted by key, every node state of `v`'s round-`r` action read on its node state in
    `W (strictEventIndex rho (S.a r))` is one of `v`'s action stores of `r`. -/
private theorem mem_actionStoreAt_path₅₂b (S : Setup V) (rho : Record.Run V)
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (v : V)
    (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r,
      n ∈ Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt M S rho v r :=
  fun _ hn => ⟨_, mem_stateBeforeTime_path₅₂b S rho hsorted W hW _, hn⟩

omit [DecidableEq V] [Fintype V] in
/-- The strict event index of `t + 1` is the inclusive event index of `t`. -/
private theorem strict_succ_eq_inclusive₅₂b (rho : Record.Run V) (t : Time) :
    strictEventIndex rho (t + 1) = inclusiveEventIndex rho t := by
  unfold strictEventIndex inclusiveEventIndex
  congr 1
  apply List.filter_congr
  intro e _
  simp only [Int.lt_add_one_iff]

/-- Every node state `n` of the round-`r` action read from `before` has the store
    `M.store_with_cache st n.cache` for some `st` whose core store is an outcome of the confirmation
    update on `before`'s core store with its clock set to `S.a r`. -/
private theorem actionReadFrom_core₅₂b (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      ∃ st : M.NS, n.st = M.store_with_cache st n.cache ∧
      M.update_confirmation_with (M.gradeContract n.cache) S.E S.hc
        (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r)).core
        (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1) ⇢ st.core := by
  rintro _ ⟨c, -, st, hst, rfl⟩
  obtain ⟨X, hX⟩ := facts.dt.update_confirmation_with_nonempty (M.gradeContract c) S.E S.hc
    (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r)).core
    (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1)
  refine ⟨st, by rw [facts.nd.mkNode_st, facts.nd.mkNode_cache], ?_⟩
  rw [facts.nd.mkNode_cache, facts.dt.named_update_confirmation_with_core _ _ _ _ _ st hst X hX]
  exact hX

/-- Every node state of the round-`r` action read from `before` has the height maximum of `before`'s
    core store. -/
private theorem actionReadFrom_h_max₅₂b (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      n.st.core.h_max = before.st.core.h_max := by
  intro n hn
  obtain ⟨st₀, hst₀, hX₀⟩ := actionReadFrom_core₅₂b facts S before r n hn
  rw [hst₀, facts.nd.store_with_cache_core_h_max,
    ← facts.sto.Sts_toHealing_h_max,
    facts.dt.update_confirmation_with_toHealing_h_max _ _ _ _ _ _ hX₀,
    facts.hd.setClock_toHealing_h_max]

/-- Every node state of the round-`r` action read from `before` has the justified height of
    `before`'s core store. -/
private theorem actionReadFrom_h_j₅₂b (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      n.st.core.h_j = before.st.core.h_j := by
  intro n hn
  obtain ⟨st₀, hst₀, hX₀⟩ := actionReadFrom_core₅₂b facts S before r n hn
  rw [hst₀, facts.nd.store_with_cache_core_h_j,
    ← facts.sto.toHealing_h_j,
    facts.dt.update_confirmation_with_toHealing_h_j _ _ _ _ _ _ hX₀,
    facts.hd.setClock_toHealing_h_j]

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open Proofs.HealingLemmas

/-- If `v` is in the set for `S.a r`, awake at `r`, `lo ≤ S.a r`, and `v`'s tick at `S.a r` has an
    outcome, then `v` emits along `W` at `S.a r`, for every node state of its action read and every
    outcome of the attestation duty, an attestation whose SG projection is `⟨v, r, some B.root⟩` for
    every block `B` the SG selector can pick. -/
theorem honest_emits_actionAttestationAtOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} (r : Round) (hv : v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)))
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ rho.horizon) (hpost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S r))
    (hA : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick v (Restated.Vocabulary.Execution.Setup.a M S r)) → M.awake_for_grade2 S v (W j v) r)
    (hneTick : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick v (Restated.Vocabulary.Execution.Setup.a M S r)) →
      ∃ out : M.N × List (NamedObject V), M.tick S v (W j v) (Restated.Vocabulary.Execution.Setup.a M S r) ⇢ out) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r,
      let gc := M.gradeContract n.cache
      let st := M.toHealing n.st.core
      let k := M.round_of S.hc st.s
      ∀ D, M.duties_attest_with gc S.E S.hc (S.node v) n.st n.record ⇢ D →
        Restated.Vocabulary.Execution.Run.emits M S rho W v (Object.attest D.2.2)
            (Restated.Vocabulary.Execution.Setup.a M S r) ∧
          ∀ A2, M.grade2_block_with gc S.E S.hc st k ⇢ A2 →
          ∀ B, M.get_sg_vote_with gc S.E S.hc st k A2 ⇢ B →
            M.sgVote D.2.2.erase = (⟨v, r, some B.root⟩ : Protocol.SGVote V) :=
  Restated.honest_emits_actionAttestationAt_of_awakeOn facts S Hs Xb hf r hv hhor hA hpost hneTick

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open Proofs.HealingLemmas

/-- If `v` and `w` are in the set for `S.a r + Δ`, `lo ≤ S.a r`, and `v` is awake at `r`, then for
    every attestation `a` that `v`'s action can compute at `S.a r`, some event `j` before
    `S.a r + Δ` leaves `a` among the round-`r` SG rows of `w`'s store in `W (j + 1)`. -/
theorem actionAttestationAt_rows_before_deltaOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    {v w : V} (r : Round) (hv : v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ)) (hw : w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ))
    (hpost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S r))
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ ≤ rho.horizon) (hA : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick v (Restated.Vocabulary.Execution.Setup.a M S r)) → M.awake_for_grade2 S v (W j v) r) :
    ∀ a ∈ Restated.actionAttestationFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) v r,
    ∃ j : Nat, ∃ e : Record.Event V,
      rho.events[j]? = some e ∧ e.time < (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ ∧
        a ∈ (W (j + 1) w).st.sg_rows r := by
  intro a ha
  obtain ⟨n, hn, ns, rec, hD⟩ := ha
  have hΔ : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ := le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)
  have haHor : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ rho.horizon := le_trans hΔ hhor
  have hva : v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)) := hHs _ _ hΔ hv
  have hwa : w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)) := hHs _ _ hΔ hw
  obtain ⟨A2, hA2⟩ := facts.dt.grade2_block_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s)
  obtain ⟨B, hB⟩ := facts.dt.get_sg_vote_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s) A2
  obtain ⟨hval, haround, -⟩ := Restated.Vocabulary.Proofs.HealingSurface.actionAttestationAt_shape facts
    S rho v r n (mem_actionStoreAt_path₅₂b S rho hf.sorted W hf.onePath v r n hn) _ hD A2 hA2 B hB
  have hval' : a.val_index = v := hval
  have haround' : a.round = r := haround
  have hemit : Restated.Vocabulary.Execution.Run.emits M S rho W v (Object.attest a)
      (Restated.Vocabulary.Execution.Setup.a M S r) :=
    Restated.honest_emits_exact_actionAttestationAtOn facts S Hs Xb hf r hva haHor hpost hA
      (fun j hj => hf.tick_outcome j _ _ hj) n hn _ hD
  have hemit' : Restated.Vocabulary.Execution.NamedRun.emits M S rho W a.val_index
      (.attest a) ((Restated.Vocabulary.Execution.Setup.a M S a.round)) := by
    rw [hval', haround']; exact hemit
  obtain ⟨t', hcausal, hlt, j, hcall⟩ :=
    hf.broadcast v (Object.attest a) ((Restated.Vocabulary.Execution.Setup.a M S r)) hva hemit w hw
      hpost hhor (fun _ h => by cases h)
  have hvalt : a.val_index ∈ Hs t' := by
    rw [hval']; exact hHs _ _ (le_of_lt hlt) hv
  have hrow := Restated.honest_row_after_callOn facts S rho Hs Xb hf hHs hvalt hemit' hcall
    (by rw [haround']; exact hcausal) (by rw [haround']; exact hlt)
    (by rw [haround']; exact hwa) (by rw [haround']; exact hpost)
  obtain ⟨-, e, he, -, het⟩ := hcall
  refine ⟨j, e, he, ?_, by rwa [haround'] at hrow⟩
  rw [show Record.Event.time e = t' from het]
  exact hlt

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open Proofs.HealingLemmas

/-- If `v` and `w` are in the set for `S.a r + Δ`, `lo ≤ S.a r`, and `v` is awake at `r`, then for
    every block `B` the SG selector can pick in `v`'s action read, some event `j` before `S.a r + Δ`
    leaves the SG vote `⟨v, r, some B.root⟩` in the round-`r` SG pool of `w`'s store in `W (j + 1)`. -/
theorem actionSGVote_pooled_before_deltaOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    {v w : V} (r : Round) (hv : v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ)) (hw : w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ))
    (hpost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S r))
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ ≤ rho.horizon) (hA : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick v (Restated.Vocabulary.Execution.Setup.a M S r)) → M.awake_for_grade2 S v (W j v) r) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r,
      let gc := M.gradeContract n.cache
      let st := M.toHealing n.st.core
      let k := M.round_of S.hc st.s
      ∀ A2, M.grade2_block_with gc S.E S.hc st k ⇢ A2 →
      ∀ B, M.get_sg_vote_with gc S.E S.hc st k A2 ⇢ B →
      ∃ j : Nat, ∃ e : Record.Event V,
        rho.events[j]? = some e ∧ e.time < (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ ∧
          (⟨v, r, some B.root⟩ : Protocol.SGVote V) ∈ (W (j + 1) w).st.toHealing.sg_votes r := by
  intro n hn gc st k A2 hA2 B hB
  obtain ⟨D, hD⟩ := facts.dt.attest_with_nonempty gc S.E S.hc (S.node v) n.st n.record
  obtain ⟨j, e, he, het, hrow⟩ :=
    Restated.actionAttestationAt_rows_before_deltaOn facts S Hs Xb hf hHs r hv hw hpost hhor hA
      D.2.2 ⟨n, hn, D.1, D.2.1, hD⟩
  refine ⟨j, e, he, het, ?_⟩
  obtain ⟨-, haround, -⟩ := Restated.Vocabulary.Proofs.HealingSurface.actionAttestationAt_shape facts
    S rho v r n (mem_actionStoreAt_path₅₂b S rho hf.sorted W hf.onePath v r n hn) D hD A2 hA2 B hB
  have hown : D.2.2 ∈ (W (j + 1) w).st.sg_rows D.2.2.round := by
    rw [haround]; exact hrow
  have hpool := facts.sto.pool_view_mem (W (j + 1) w).st
    (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho (j + 1) w _
      (hf.onePath (j + 1)).1).1.1.1.2.2.2.1 _ hown
  rw [haround] at hpool
  have himg := Finset.mem_image_of_mem M.sgVote hpool
  have hvote := Restated.Vocabulary.Proofs.HealingSurface.sgVote_actionAttestationAt facts S rho v r _
    (mem_stateBeforeTime_path₅₂b S rho hf.sorted W hf.onePath _) n hn D hD A2 hA2 B hB
  rw [hvote] at himg
  change _ ∈ (M.toHealing (W (j + 1) w).st.core).toFG.toSG.sg_votes r
  rw [facts.sto.Sts_toHealing_sg_votes]
  exact himg

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open Proofs.HealingLemmas

/-- If `v` and `w` are in the set for `S.a r + Δ`, `lo ≤ S.a r`, and `v` is awake at `r`, then for
    every block `B` the SG selector can pick in `v`'s action read, the vote `⟨v, r, some B.root⟩` is
    among `v`'s votes of the round-`(r + 1)` grade batch of `w`'s store in
    `W (strictEventIndex rho (S.a (r + 1)))`. -/
theorem actionSGVote_mem_next_round_batchOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    {v w : V} (r : Round) (hv : v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ)) (hw : w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ))
    (hpost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S r))
    (hcut : Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (r + 1) ≤ rho.horizon)
    (hA : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick v (Restated.Vocabulary.Execution.Setup.a M S r)) → M.awake_for_grade2 S v (W j v) r) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r,
      let gc := M.gradeContract n.cache
      let st := M.toHealing n.st.core
      let k := M.round_of S.hc st.s
      ∀ A2, M.grade2_block_with gc S.E S.hc st k ⇢ A2 →
      ∀ B, M.get_sg_vote_with gc S.E S.hc st k A2 ⇢ B →
      (⟨v, r, some B.root⟩ : Protocol.SGVote V) ∈ Protocol.sg_votes_by
        (Restated.Vocabulary.Protocol.round_batch M
          (M.gradeView (M.toHealing
            (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (r + 1))) w).st.core))
          (r + 1)) v := by
  intro n hn gc st k A2 hA2 B hB
  have hdeadline : (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ ≤ rho.horizon :=
    le_trans (facts.gr.action_add_delta_le_next_Γ_neg1 S r) hcut
  obtain ⟨j, e, hj, hjt, hpool⟩ :=
    Restated.actionSGVote_pooled_before_deltaOn facts S Hs Xb hf hHs r hv hw hpost hdeadline hA
      n hn A2 hA2 B hB
  have hbefore : e.time < (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) :=
    lt_of_lt_of_le hjt (le_trans (facts.gr.action_add_delta_le_next_Γ_neg1 S r)
      (le_of_lt (Restated.Vocabulary.Proofs.HealingSurface.next_Γ_neg1_lt_action facts S r)))
  have hread := Restated.sgVote_mem_stateBeforeTime_of_postOn facts S Hs Xb hf hj hbefore hpool
  have hr1 : r + 1 ≠ 0 := by
    simpa only [Nat.succ_eq_add_one] using Nat.succ_ne_zero r
  apply Finset.mem_filter.mpr
  constructor
  · rw [Restated.Vocabulary.Protocol.round_batch, if_neg hr1, Nat.add_sub_cancel,
      facts.gr.gradeView_sg_votes, ← facts.sto.Sts_toHealing_sg_votes]
    exact hread
  · rfl

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open Proofs.HealingLemmas

/-- If event `j` is before `t` and `u` is in the round-`k` SG pool of `w`'s store in `W (j + 1)`,
    then `w`'s store in `W (strictEventIndex rho t)` gives `u` the same stamp. -/
theorem timestamp_sg_vote_stateBeforeTime_of_postOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {w : V} {j : Nat} {e : Record.Event V} {t : Time} {k : Round}
    {u : Protocol.SGVote V}
    (hj : rho.events[j]? = some e) (hjt : e.time < t)
    (hu : u ∈ (W (j + 1) w).st.toHealing.sg_votes k) :
    (W (strictEventIndex rho t) w).st.timestamp_sg_vote u =
      (W (j + 1) w).st.timestamp_sg_vote u := by
  have hjN : j + 1 ≤ strictEventIndex rho t :=
    Nat.succ_le_of_lt (lt_strict_of_time_lt₅₂b hf.sorted hj hjt)
  exact Restated.Vocabulary.Proofs.HealingSurface.GradeDeliveryRun.stateBefore_timestamp_sg_vote_carry
    facts S rho w (i := j + 1) (W (j + 1)) (hf.onePath (j + 1)).1 _ hjN hu _
    (onePath_slice₅₂b W hf.onePath hjN)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open Proofs.HealingLemmas

/-- If `a` is among the SG rows of `v`'s store in `W (i + 1)` and event `i` is before `Gamma`, then
    that store stamps `a`'s projection before `Gamma`. -/
theorem timestamp_sg_vote_before_of_mem_post_eventOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} {i : Nat} {e : Record.Event V} {a : NamedAttestation V}
    {Gamma : Time} (hi : rho.events[i]? = some e)
    (ha : a ∈ (W (i + 1) v).st.sg_rows a.round)
    (heGamma : e.time < Gamma) :
    occurrenceBefore
      ((W (i + 1) v).st.timestamp_sg_vote
        (M.sgVote a.erase)) Gamma = true := by
  obtain ⟨-, stamp, hle, heq⟩ :=
    Restated.held_row_own_and_stamp_at_eventOn facts S rho Hs Xb hf hi v a.round a
      (W (i + 1)) (hf.onePath (i + 1)).1 ha
  have heq' : (W (i + 1) v).st.timestamp_sg_vote
      (M.sgVote a.erase) = some (stamp : Stamp) := heq
  have hlt : stamp < Gamma := lt_of_le_of_lt hle heGamma
  rw [heq']
  exact (occurrenceBefore_some_iff (stamp : Stamp) Gamma).mpr (WithBot.coe_lt_coe.mpr hlt)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open Proofs.HealingLemmas

/-- If event `j` is before `Gamma ≤ read` and `u` is in the round-`k` SG pool of `w`'s store in
    `W (j + 1)` with a stamp before `Gamma`, then `u` is in that pool of `w`'s store in
    `W (strictEventIndex rho read)` with a stamp before `Gamma`. -/
theorem projected_vote_mem_stamp_at_readOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {w : V} {j : Nat} {e : Record.Event V} {read Gamma : Time} {k : Round}
    {u : Protocol.SGVote V}
    (hj : rho.events[j]? = some e) (heGamma : e.time < Gamma)
    (hGammaRead : Gamma ≤ read)
    (hu : u ∈ (W (j + 1) w).st.toHealing.sg_votes k)
    (hut : occurrenceBefore
      ((W (j + 1) w).st.timestamp_sg_vote u) Gamma = true) :
    u ∈ (W (strictEventIndex rho read) w).st.toHealing.sg_votes k ∧
      occurrenceBefore
        ((W (strictEventIndex rho read) w).st.timestamp_sg_vote u) Gamma = true := by
  have heRead : e.time < read := lt_of_lt_of_le heGamma hGammaRead
  constructor
  · exact Restated.sgVote_mem_stateBeforeTime_of_postOn facts S Hs Xb hf hj heRead hu
  · have hcarry := Restated.timestamp_sg_vote_stateBeforeTime_of_postOn facts S Hs Xb hf hj heRead hu
    rwa [hcarry]

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open Proofs.HealingLemmas

/-- If `v` and `w` are in the set for `S.a r + Δ`, `lo ≤ S.a r`, and `v` is awake at `r`, then for
    every block `B` the SG selector can pick in `v`'s action read, the grade view of `w`'s store in
    `W (strictEventIndex rho (S.a (r + 1)))` stamps `⟨v, r, some B.root⟩` before round `r + 1`'s
    earliest grade cutoff. -/
theorem actionSGVote_stamp_before_next_Γ_neg1On (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    {v w : V} (r : Round) (hv : v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ)) (hw : w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ))
    (hpost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S r))
    (hcut : Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (r + 1) ≤ rho.horizon)
    (hA : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick v (Restated.Vocabulary.Execution.Setup.a M S r)) → M.awake_for_grade2 S v (W j v) r) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r,
      let gc := M.gradeContract n.cache
      let st := M.toHealing n.st.core
      let k := M.round_of S.hc st.s
      ∀ A2, M.grade2_block_with gc S.E S.hc st k ⇢ A2 →
      ∀ B, M.get_sg_vote_with gc S.E S.hc st k A2 ⇢ B →
      occurrenceBefore
        ((M.gradeView (M.toHealing
            (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (r + 1))) w).st.core)).timestamp_sg_vote
          (⟨v, r, some B.root⟩ : Protocol.SGVote V))
        (Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (r + 1)) = true := by
  intro n hn gc st k A2 hA2 B hB
  have hdeadline : (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ ≤ rho.horizon :=
    le_trans (facts.gr.action_add_delta_le_next_Γ_neg1 S r) hcut
  obtain ⟨D, hD⟩ := facts.dt.attest_with_nonempty gc S.E S.hc (S.node v) n.st n.record
  obtain ⟨j, e, hj, heDelta, hrow⟩ :=
    Restated.actionAttestationAt_rows_before_deltaOn facts S Hs Xb hf hHs r hv hw hpost
      hdeadline hA D.2.2 ⟨n, hn, D.1, D.2.1, hD⟩
  obtain ⟨-, haround, -⟩ := Restated.Vocabulary.Proofs.HealingSurface.actionAttestationAt_shape facts
    S rho v r n (mem_actionStoreAt_path₅₂b S rho hf.sorted W hf.onePath v r n hn) D hD A2 hA2 B hB
  have ha' : D.2.2 ∈ (W (j + 1) w).st.sg_rows D.2.2.round := by
    rw [haround]; exact hrow
  have heCut : e.time < Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (r + 1) :=
    lt_of_lt_of_le heDelta (facts.gr.action_add_delta_le_next_Γ_neg1 S r)
  have hut := Restated.timestamp_sg_vote_before_of_mem_post_eventOn facts S Hs Xb hf hj ha' heCut
  have hvote := Restated.Vocabulary.Proofs.HealingSurface.sgVote_actionAttestationAt facts S rho v r _
    (mem_stateBeforeTime_path₅₂b S rho hf.sorted W hf.onePath _) n hn D hD A2 hA2 B hB
  have hu : M.sgVote D.2.2.erase ∈ (W (j + 1) w).st.toHealing.sg_votes r := by
    have hpool := facts.sto.pool_view_mem (W (j + 1) w).st
      (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho (j + 1) w _
        (hf.onePath (j + 1)).1).1.1.1.2.2.2.1 _ ha'
    rw [haround] at hpool
    have himg := Finset.mem_image_of_mem M.sgVote hpool
    change _ ∈ (M.toHealing (W (j + 1) w).st.core).toFG.toSG.sg_votes r
    rw [facts.sto.Sts_toHealing_sg_votes]
    exact himg
  have hread : Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (r + 1) ≤
      (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) :=
    le_of_lt (Restated.Vocabulary.Proofs.HealingSurface.next_Γ_neg1_lt_action facts S r)
  have hpostRead := Restated.projected_vote_mem_stamp_at_readOn facts S Hs Xb hf hj heCut hread hu hut
  rw [facts.gr.gradeView_timestamp_sg_vote, ← hvote]
  exact hpostRead.2

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open Proofs.HealingLemmas

/-- If `P` is an ancestor of every round-`r` action carrier, `t_GST ≤ S.a r`, `P` is in the filtered
    tree of every reader of round `r + 1` and of every grade-2 domain reader of `r + 1`, every
    member of the set for `S.a r + Δ` is awake at `r`, and `lo ≤ S.a r`, then `CleanActionReadForOn`
    holds of the worlds `fun t => W (strictEventIndex rho t)`. -/
theorem cleanActionReadFor_of_actionCarriersCover_and_next_activeOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {r : Round} {P : Block V}
    (hcover : Restated.ActionCarriersCoverOn M S rho Hs r P
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r))))
    (hpost : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S r))
    (hcut : Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (r + 1) ≤ rho.horizon)
    (hactive : ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))),
      P ∈ M.get_filtered_block_tree
        (M.toHealing
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (r + 1))) w).st.core).toFG)
    (hactive_domain : ∀ w ∈ Hs (M.domain S.E S.hc (r + 1) Phase.g2),
      P ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
        (W (strictEventIndex rho (M.domain S.E S.hc (r + 1) Phase.g2)) w))
    (hA : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick v (Restated.Vocabulary.Execution.Setup.a M S r)) → M.awake_for_grade2 S v (W j v) r)
    (hlo : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S r)) :
    Restated.CleanActionReadForOn M S rho Hs r (fun t => W (strictEventIndex rho t)) P := by
  refine ⟨hpost, hcut, hactive, hactive_domain, ?_⟩
  intro w hw v hvD
  dsimp only
  intro n hn g hg B hB
  have hv : v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)) :=
    hHs _ _ (le_of_lt (lt_add_of_pos_right _ S.E.Δ_pos)) hvD
  have hrelayRead : (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ ≤
      (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) :=
    le_trans (facts.gr.action_add_delta_le_next_Γ_neg1 S r)
      (le_of_lt (Restated.Vocabulary.Proofs.HealingSurface.next_Γ_neg1_lt_action facts S r))
  have hPB : Block.Preceq P B := hcover v hv n hn g hg B hB
  have hBsource : B ∈ (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).st.core.T :=
    Restated.Vocabulary.Proofs.HealingSurface.actionSGBlockAt_mem_storeBeforeTime facts S rho v r _
      (mem_stateBeforeTime_path₅₂b S rho hf.sorted W hf.onePath _) n hn g hg B hB
  have hvisible : B ∈
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (r + 1))) w).st.T ∧
      stampedBefore
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (r + 1))) w).st.timestamp_block
        (Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (r + 1)) B = true := by
    rcases Restated.block_eq_genesis_or_acceptsBefore_of_mem_storeBeforeTimeOn facts
        S Hs Xb hf v ((Restated.Vocabulary.Execution.Setup.a M S r)) hBsource with
      hgen | ⟨D, i, t, hDerase, hacc, ht⟩
    · rw [hgen]
      exact Restated.genesis_mem_and_stamp_storeBeforeTimeOn facts S Hs Xb hf w
        ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) _
    · have hHpos : 0 < D.slot := by
        have hslot := Restated.Vocabulary.Protocol.parent_slot_lt_of_acceptsAt_block facts S W
          hf.onePath hacc
        rw [Proofs.NamedWire.erase_slot] at hslot
        exact Nat.zero_lt_of_lt hslot
      have hPD : Block.Preceq P D.erase := by rw [hDerase]; exact hPB
      have hFP : Block.Preceq
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (r + 1))) w).st.core.F P := by
        have h := facts.fc.finalized_preceq_of_mem_get_filtered_block_tree (hactive w hw)
        rw [facts.sto.ModelProperties_toHealing_F] at h
        exact h
      have hFhist : ∀ j : Nat,
          j ≤ (rho.events.filter (fun e => decide (e.time <
            (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ))).length →
            Block.Preceq (W j w).st.core.F D.erase := by
        intro j hj
        exact Restated.frozenSuffix_finalizedBelowAtDeliveries_of_preceqOn facts S Hs Xb hf hFP hPD
          j (le_trans hj (strictEventIndex_mono rho hrelayRead))
      have hrelayHor : (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ ≤ rho.horizon :=
        le_trans (facts.gr.action_add_delta_le_next_Γ_neg1 S r) hcut
      have hvmax : v ∈ Hs (max t lo) := hHs _ _ (max_le (le_of_lt ht) hlo) hv
      obtain ⟨C, hCerase, j, t', hacc', ht'⟩ := Restated.block_admittedBefore_of_accepted_after_cutoffOn
        facts S Hs Xb hf hHs hHsXb hvmax (hHs _ _ hrelayRead hw) hHpos hacc ht hlo rfl hrelayHor
        hFhist
      have hadmitNext : Restated.Vocabulary.Protocol.AdmittedBefore M S rho W w B
          (Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (r + 1)) :=
        ⟨C, by rw [hCerase]; exact hDerase, j, t', hacc',
          lt_of_lt_of_le ht' (facts.gr.action_add_delta_le_next_Γ_neg1 S r)⟩
      exact Restated.admittedBefore_mem_and_stamp_atOn facts S Hs Xb hf hadmitNext
        (le_of_lt (Restated.Vocabulary.Proofs.HealingSurface.next_Γ_neg1_lt_action facts S r))
  have hvoteStamp := Restated.actionSGVote_stamp_before_next_Γ_neg1On facts S Hs Xb hf hHs r
    hvD (hHs _ _ hrelayRead hw) hlo hcut (hA v hvD) n hn g hg B hB
  obtain ⟨Bn, hBnErase, hBrun⟩ :=
    Restated.runBlock_of_mem_core_T_stateBeforeTimeOn facts S Hs Xb hf (hHsXb _ hw)
      ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) hvisible.1
  have hfind : Block.find?
      (M.gradeView (M.toHealing
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (r + 1))) w).st.core)).T
        B.root = some B := by
    apply Proofs.Optimistic.find?_eq_some_of_unique
    · rw [facts.gr.Sts_gradeView_T]
      exact hvisible.1
    · intro Y hY hroot
      rw [facts.gr.Sts_gradeView_T] at hY
      obtain ⟨Yn, hYnErase, hYrun⟩ :=
        Restated.runBlock_of_mem_core_T_stateBeforeTimeOn facts S Hs Xb hf (hHsXb _ hw)
          ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) hY
      have hrootN : Yn.root = Bn.root :=
        (Proofs.NamedWire.erase_root Yn).symm.trans
          (((congrArg Block.root hYnErase).trans hroot).trans
            (congrArg Block.root hBnErase.symm) |>.trans (Proofs.NamedWire.erase_root Bn))
      have hYB := hf.rootCollisionFree.root_injective
        Yn Bn hYrun hBrun Yn Bn
        (Or.inl (Proofs.NamedAncestry.named_self Yn))
        (Or.inr (Proofs.NamedAncestry.named_self Bn)) hrootN
      rw [← hYnErase, hYB]
      exact hBnErase
  have hblock : occurrenceBefore
      ((M.gradeView (M.toHealing
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (r + 1))) w).st.core)).timestamp_block B)
      (Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (r + 1)) = true := by
    have h2 := hvisible.2
    rw [stampedBefore_eq_occurrenceBefore] at h2
    rw [facts.gr.gradeView_timestamp_block]
    exact h2
  constructor
  · simp only [Protocol.sg_resolution_time, hfind]
    exact occurrenceBefore_max hvoteStamp hblock
  · intro b hb
    exact facts.gr.head_covers_of_find hfind hPB b hb

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open Proofs.HealingLemmas

/-- If `F` is an ancestor of the FG root of every round-`r` action store of every member of
    `Hs (S.a r)`, then for every world before `S.a r`, `F` is an ancestor of every round-`r` action
    carrier of those members computed from it. -/
theorem actionCarriersCover_of_fgRootFloorOn (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (Hs : Int → Finset V) {r : Round} {F : Block V}
    (hfloor : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)),
      ∀ n ∈ Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt M S rho v r,
        Block.Preceq F (M.get_fg_root (M.toHealing n.st.core).toFG)) :
    ∀ wd ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho
        (Restated.Vocabulary.Execution.Setup.a M S r),
      Restated.ActionCarriersCoverOn M S rho Hs r F wd := by
  intro wd hwd v hv n hnwd A2 hA2 A hA
  exact preceq_trans_Preceq (hfloor v hv n ⟨wd, hwd, hnwd⟩)
    (Restated.Vocabulary.Proofs.HealingSurface.actionFGRoot_preceq_actionSGBlockAt facts S rho v r
      wd hwd n hnwd A2 hA2 A hA)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation

/-- If `w ∈ Xb` holds `D` in its store in `W (strictEventIndex rho read)`, then `D` is a run block
    read through `Xb` along `W`. -/
theorem runBlockOf_of_stateBeforeTime_memOn_HeightProgressSeedRegime (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {w : V} (hw : w ∈ Xb) (read : Time)
    {D : NamedBlock V} (hD : D ∈ (W (strictEventIndex rho read) w).st.bodies) :
    Restated.RunBlockOn M S rho W Xb D :=
  Restated.runBlock_of_stateBefore_memOn facts S W Xb hw hD

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation

/-- Two run blocks read through `Xb` along `W` with the same erasure are equal. -/
theorem runBlock_unique_of_erase_eqOn_HeightProgressSeedRegime (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} {Hs : Int → Finset V} {Xb : Finset V} {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {A D : NamedBlock V} (hA : Restated.RunBlockOn M S rho W Xb A) (hD : Restated.RunBlockOn M S rho W Xb D)
    (herase : A.erase = D.erase) : A = D :=
  hf.rootCollisionFree.root_injective A D hA hD A D
    (Or.inl (Proofs.NamedAncestry.named_self A)) (Or.inr (Proofs.NamedAncestry.named_self D))
    (by rw [← Proofs.NamedWire.erase_root A, ← Proofs.NamedWire.erase_root D, herase])

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation

/-- Under the hypotheses of `frontierBlock_filtered_of_gateOffOn`, the finalized block of `w`'s core
    store in `W (strictEventIndex rho read)` is an ancestor of `X`, `X`'s chain-state height is at
    least that store's `h_max` minus one, and the store's FG root is an ancestor of `X`. -/
private theorem frontierBlock_parts₅₂b (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hsb : Restated.SlashableBoundOn M S rho W Xb)
    {w : V} (hw : w ∈ Xb) {read : Time}
    {X : Block V} {Xn : NamedBlock V} {Mh : Height}
    (hX : X ∈ (W (strictEventIndex rho read) w).st.T)
    (hXerase : Xn.erase = X) (hXrun : Restated.RunBlockOn M S rho W Xb Xn)
    (hXh : Mh - 1 ≤ (M.derive_named S.E S.cfg Xn).h)
    (hfrontier : (W (strictEventIndex rho read) w).st.h_max = Mh)
    (hgateOff : (W (strictEventIndex rho read) w).st.h_j + 2 ≤ Mh) :
    Block.Preceq (W (strictEventIndex rho read) w).st.core.F X ∧
      (W (strictEventIndex rho read) w).st.core.h_max - 1 ≤
        ((W (strictEventIndex rho read) w).st.core.σ X).h ∧
      Block.Preceq (M.get_fg_root (M.toHealing (W (strictEventIndex rho read) w).st.core).toFG) X := by
  have hmem := mem_stateBeforeTime_path₅₂b S rho hf.sorted W hf.onePath read
  set wd := W (strictEventIndex rho read) with hwd
  have hX' : X ∈ (wd w).st.core.T := hX
  have hfrontier' : (wd w).st.core.h_max = Mh := hfrontier
  have hgateOff' : (wd w).st.core.h_j + 2 ≤ Mh := hgateOff
  have hnoHigh :=
    Restated.Vocabulary.Proofs.NamedJustificationBound.noHighJustifications_stateBeforeTime facts S rho
      read w wd hmem
  obtain ⟨Dst, hDstMem, hDstF, -⟩ :=
    Restated.Vocabulary.Proofs.Bridges.storeFinalizationOnChain_stateBeforeTime facts S rho read w wd
      hmem
  have hDrun : Restated.RunBlockOn M S rho W Xb Dst :=
    Restated.runBlockOf_of_stateBeforeTime_memOn_HeightProgressSeedRegime facts S Hs Xb hf hw read
      hDstMem
  have hhjlt : (wd w).st.core.h_j < Mh - 1 := by
    rw [Nat.lt_sub_iff_add_lt]
    exact Nat.lt_of_succ_le (by simpa only [Nat.add_assoc] using hgateOff')
  have hcrossed : (M.derive_named S.E S.cfg Dst).h_F <
      (M.derive_named S.E S.cfg Xn).h := by
    calc
      (M.derive_named S.E S.cfg Dst).h_F ≤
          (M.derive_named S.E S.cfg Dst).h_j :=
        (facts.cs.chainOrder_derive_named S.E S.cfg Dst).heights_ordered
      _ ≤ (wd w).st.core.h_j := hnoHigh Dst hDstMem
      _ < Mh - 1 := hhjlt
      _ ≤ (M.derive_named S.E S.cfg Xn).h := hXh
  have hFX : Block.Preceq (wd w).st.core.F X := by
    have hpre := Restated.finalized_preceq_of_height_ltOn facts
      S rho W Xb Xn Dst hsb hf.rootCollisionFree hXrun hDrun hcrossed
    rw [hXerase] at hpre
    simp only [hDstF] at hpre
    exact hpre
  have hgate : ¬ (wd w).st.core.h_max = (wd w).st.core.h_j + 1 := by
    apply Nat.ne_of_gt
    rw [hfrontier']
    exact Nat.lt_of_succ_le (by simpa only [Nat.add_assoc] using hgateOff')
  have hroot : M.get_fg_root (M.toHealing (wd w).st.core).toFG = (wd w).st.core.F :=
    facts.fc.get_fg_root_toHealing_of_ne (wd w).st.core hgate
  obtain ⟨D', hD'mem, hD'erase⟩ :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime facts S rho read w
      wd hmem hX'
  have hD'run : Restated.RunBlockOn M S rho W Xb D' :=
    Restated.runBlockOf_of_stateBeforeTime_memOn_HeightProgressSeedRegime facts S Hs Xb hf hw read
      hD'mem
  have hDeq : D' = Xn :=
    Restated.runBlock_unique_of_erase_eqOn_HeightProgressSeedRegime facts hf hD'run hXrun
      (hD'erase.trans hXerase.symm)
  have hview :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.derivedView_stateBeforeTime facts S rho read w wd hmem
      D' hD'mem
  rw [hD'erase, hDeq] at hview
  refine ⟨hFX, ?_, by rw [hroot]; exact hFX⟩
  rw [hview, hfrontier']
  exact hXh

/-- If `w ∈ Xb` holds `X` in its store in `W (strictEventIndex rho read)`, `X` erases a run block of
    height at least `Mh − 1`, `1 ≤ Mh`, that store's `h_max` is `Mh` and its `h_j + 2 ≤ Mh`, then
    `X` is in that store's filtered tree. -/
theorem frontierBlock_filtered_of_gateOffOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hsb : Restated.SlashableBoundOn M S rho W Xb)
    {w : V} (hw : w ∈ Xb) {read : Time} (hread : read ≤ rho.horizon)
    {X : Block V} {Xn : NamedBlock V} {Mh : Height}
    (hX : X ∈ (W (strictEventIndex rho read) w).st.T)
    (hXerase : Xn.erase = X) (hXrun : Restated.RunBlockOn M S rho W Xb Xn)
    (hXh : Mh - 1 ≤ (M.derive_named S.E S.cfg Xn).h) (hM : 1 ≤ Mh)
    (hfrontier : (W (strictEventIndex rho read) w).st.h_max = Mh)
    (hgateOff : (W (strictEventIndex rho read) w).st.h_j + 2 ≤ Mh) :
    X ∈ M.get_filtered_block_tree
      (M.toHealing (W (strictEventIndex rho read) w).st.core).toFG := by
  obtain ⟨hFX, hh, hrootX⟩ := frontierBlock_parts₅₂b facts S Hs Xb hf hsb hw hX hXerase hXrun hXh
    hfrontier hgateOff
  have hX' : X ∈ (W (strictEventIndex rho read) w).st.core.T := hX
  exact facts.fc.mem_get_filtered_block_tree_of_parts _
    (by rw [facts.sto.toHealing_T]; exact hX')
    (by rw [facts.sto.ModelProperties_toHealing_F]; exact hFX)
    (by rw [facts.sto.toHealing_T]; exact hX') (Proofs.ModelProperties.Preceq_self _)
    (by rw [facts.sto.ModelProperties_toHealing_h_max, facts.sto.ModelProperties_toHealing_σ]; exact hh)
    hrootX

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation

/-- If `w ∈ Xb` holds `D` in its store in `W (strictEventIndex rho read)`, `D` erases a run block of
    height at least `Mh − 1`, `C ⪯ D`, `1 ≤ Mh`, that store's `h_max` is `Mh` and its
    `h_j + 2 ≤ Mh`, and `C` is a descendant of that store's FG root, then `C` is in that store's
    filtered tree. -/
theorem frontierAncestor_filtered_of_gateOffOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hsb : Restated.SlashableBoundOn M S rho W Xb)
    {w : V} (hw : w ∈ Xb) {read : Time} (hread : read ≤ rho.horizon)
    {C D : Block V} {Dn : NamedBlock V} {Mh : Height}
    (hD : D ∈ (W (strictEventIndex rho read) w).st.T)
    (hDerase : Dn.erase = D) (hDrun : Restated.RunBlockOn M S rho W Xb Dn)
    (hCD : Block.Preceq C D)
    (hDh : Mh - 1 ≤ (M.derive_named S.E S.cfg Dn).h) (hM : 1 ≤ Mh)
    (hfrontier : (W (strictEventIndex rho read) w).st.h_max = Mh)
    (hgateOff : (W (strictEventIndex rho read) w).st.h_j + 2 ≤ Mh)
    (hrootC : Block.Preceq
      (M.get_fg_root
        (M.toHealing (W (strictEventIndex rho read) w).st.core).toFG) C) :
    C ∈ M.get_filtered_block_tree
      (M.toHealing (W (strictEventIndex rho read) w).st.core).toFG := by
  have hmem := mem_stateBeforeTime_path₅₂b S rho hf.sorted W hf.onePath read
  let st := (W (strictEventIndex rho read) w).st
  have hCT : C ∈ st.core.T :=
    Restated.ancestor_mem_storeBeforeTimeOn facts S Hs Xb hf hD hCD
  have hFJ : Block.Preceq st.core.F st.core.J :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime facts S rho
      read w _ hmem
  have hDfiltered : D ∈ M.get_filtered_block_tree
      (M.toHealing st.core).toFG :=
    Restated.frontierBlock_filtered_of_gateOffOn facts S Hs Xb hf hsb hw hread hD hDerase hDrun
      hDh hM hfrontier hgateOff
  exact facts.fc.mem_filtered_of_preceq
    (by rw [facts.sto.Sts_toHealing_F, facts.sto.Sts_toHealing_J]; exact preceq_eq_true_iff_Preceq.mpr hFJ)
    hDfiltered (by rw [facts.sto.toHealing_gs_T]; exact hCT) (preceq_eq_true_iff_Preceq.mpr hCD)
    (preceq_eq_true_iff_Preceq.mpr hrootC)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation

/-- If `w ∈ Xb`, some body of `w`'s store in `W (strictEventIndex rho read)` is a run block read
    through `Xb` that justifies the store's justified block at its justified height. -/
theorem justificationCarrierAtStrictRead_l1On (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {w : V} (hw : w ∈ Xb) (read : Time) :
    let st := (W (strictEventIndex rho read) w).st
    ∃ C : NamedBlock V,
      C ∈ st.bodies ∧ Restated.RunBlockOn M S rho W Xb C ∧
        Restated.Vocabulary.Internal.NamedJustifiedAt M S.E S.cfg C st.J st.h_j := by
  have hmem := mem_stateBeforeTime_path₅₂b S rho hf.sorted W hf.onePath read
  obtain ⟨C, hC, hJ, hhj⟩ :=
    Restated.Vocabulary.Proofs.Bridges.storeJustificationOnChain_stateBeforeTime facts S rho read w _
      hmem
  have hCrun : Restated.RunBlockOn M S rho W Xb C :=
    Restated.runBlockOf_of_stateBeforeTime_memOn_HeightProgressSeedRegime facts S Hs Xb hf hw read hC
  exact ⟨C, hC, hCrun, ⟨hJ, hhj⟩⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation

/-- If `C` is a run block read through `Xb` along `W` that justifies `J` at height `h ≠ 0`, then a
    certificate read through `Xb` along `W` exists for `h` and `J`'s root. -/
theorem certificate_of_justifiedRunBlock_l1On (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} {W : Nat → V → M.N} (Xb : Finset V)
    {C : NamedBlock V} {J : Block V} {h : Height}
    (hCrun : Restated.RunBlockOn M S rho W Xb C)
    (hjust : Restated.Vocabulary.Internal.NamedJustifiedAt M S.E S.cfg C J h)
    (hne : h ≠ 0) : Restated.CertificateOn M S rho W Xb h J.root := by
  have hderivedNe : (M.derive_named S.E S.cfg C).h_j ≠ 0 := by
    rw [hjust.2]
    exact hne
  obtain ⟨J', hJ'D, hJ'earse, Q, hQ, hsign⟩ :=
    Restated.Vocabulary.Proofs.NamedJustificationCertificates.justification_certificate facts S.E S.cfg C hderivedNe
  have hJroot : J'.root = J.root := by
    rw [← Proofs.NamedWire.erase_root J', hJ'earse, hjust.1]
  refine ⟨Q, (isQuorum_iff_q_le S.E Q).mp hQ, ?_⟩
  intro i hi
  obtain ⟨carrier, a, hcarrier, ha, hav, hpair⟩ := hsign i hi
  have hcarrierRun : Restated.RunBlockOn M S rho W Xb carrier :=
    Restated.blockInRun_of_ancestorOn facts S rho W Xb hCrun hcarrier
  refine ⟨a,
    Or.inr ⟨carrier, hcarrierRun,
      (priv% Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.HeightProgressSeedRegime
        DecoupledConsensusModel.Proofs.HealingSurface.mem_named_chain_attestations_own_l1) ha⟩,
    hav, ?_⟩
  rw [hpair, hjust.2, hJroot]

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation

/-- If `w ∈ Xb`, the justified block of `w`'s store in `W (strictEventIndex rho read)` erases a run
    block read through `Xb` along `W`. -/
theorem runBlockOf_justified_atStrictRead_l1On (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {w : V} (hw : w ∈ Xb) (read : Time) :
    Restated.RunBlockOfOn M S rho W Xb (W (strictEventIndex rho read) w).st.J := by
  have hmem := mem_stateBeforeTime_path₅₂b S rho hf.sorted W hf.onePath read
  have hJmem := Restated.Vocabulary.Proofs.NamedStoreBridge.justifiedInTree_stateBeforeTime facts S rho
    read w _ hmem
  obtain ⟨D, hD, hDe⟩ :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime facts S rho read w
      _ hmem hJmem
  exact ⟨D, hDe, Restated.runBlockOf_of_stateBeforeTime_memOn_HeightProgressSeedRegime facts S Hs Xb hf hw
    read hD⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation

/-- Round `start`'s action time plus one plus one delay is at most round `start + 1`'s action time. -/
theorem action_add_one_add_delta_le_next_action_l52 (facts : Record.Facts M) (S : Setup V) (start : Round) :
    (Restated.Vocabulary.Execution.Setup.a M S start) + 1 + S.E.Δ ≤ (Restated.Vocabulary.Execution.Setup.a M S (start + 1)) := by
  show M.a S.hc S.E.Δ start + 1 + S.E.Δ ≤ M.a S.hc S.E.Δ (start + 1)
  rw [facts.gr.a_add_rounds S start 1]
  have hDelta : (1 : Time) ≤ S.E.Δ :=
    Int.add_one_le_iff.mpr S.E.Δ_pos
  have hDnonneg : (0 : Time) ≤ S.E.Δ := le_of_lt S.E.Δ_pos
  have hR : (2 : Time) ≤ (S.hc.R : Nat) := by
    exact_mod_cast S.hc.R_ge_two
  have hcoef : (0 : Time) ≤ 4 * S.E.Δ :=
    Int.mul_nonneg (by norm_num) hDnonneg
  have hscale : 4 * S.E.Δ * 2 ≤ 4 * S.E.Δ * (S.hc.R : Nat) :=
    Int.mul_le_mul_of_nonneg_left hR hcoef
  have hsmall : (1 : Time) + S.E.Δ ≤ 4 * S.E.Δ * (S.hc.R : Nat) := by
    calc
      (1 : Time) + S.E.Δ ≤ 2 * S.E.Δ := by
        simpa [two_mul] using Int.add_le_add_right hDelta S.E.Δ
      _ ≤ 4 * S.E.Δ * 2 := by
        have htwo := Int.mul_le_mul_of_nonneg_right
          (show (2 : Time) ≤ 8 by decide) hDnonneg
        simpa only [show (8 : Time) * S.E.Δ = 4 * S.E.Δ * 2 by ring] using htwo
      _ ≤ 4 * S.E.Δ * (S.hc.R : Nat) := hscale
  simpa only [Nat.cast_one, mul_one, Int.add_assoc] using
    Int.add_le_add_left hsmall (M.a S.hc S.E.Δ start)

end

/-! ### Height progress -/

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation

/-- Two run blocks read through `Xb` along `W` with the same erasure are equal. -/
theorem runBlock_unique_of_erase_eqOn_RawHeightProgress (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} {Hs : Int → Finset V} {Xb : Finset V} {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {A D : NamedBlock V} (hA : Restated.RunBlockOn M S rho W Xb A)
    (hD : Restated.RunBlockOn M S rho W Xb D)
    (herase : A.erase = D.erase) : A = D :=
  hf.rootCollisionFree.root_injective A D hA hD A D
    (Or.inl (Proofs.NamedAncestry.named_self A)) (Or.inr (Proofs.NamedAncestry.named_self D))
    (by rw [← Proofs.NamedWire.erase_root A, ← Proofs.NamedWire.erase_root D, herase])

/-- If `D` is a run block at height `H`, `w ∈ Xb`, `i` is at most the number of events before
    `cutoff`, and the `h_max` of `w`'s store in `W (strictEventIndex rho cutoff)` is at most `H`,
    then the finalized block of `w`'s store in `W i` is an ancestor of `D`'s erasure. -/
theorem exactHeightCarrier_finalizedBelowAtPrefixOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hsb : Restated.SlashableBoundOn M S rho W Xb)
    {H : Height} {D : NamedBlock V}
    (hcarrierRun : Restated.RunBlockOn M S rho W Xb D)
    (hcarrierHeight : (M.derive_named S.E S.cfg D).h = H)
    {w : V} (hw : w ∈ Xb)
    {i : Nat} {cutoff : Time}
    (hi : i ≤ (rho.events.filter
      (fun e => decide (e.time < cutoff))).length)
    (hcap : (W (strictEventIndex rho cutoff) w).st.core.h_max ≤ H) :
    Block.Preceq (W i w).st.core.F D.erase := by
  have hiN : i ≤ strictEventIndex rho cutoff := hi
  have hpreCap : (W i w).st.core.h_max ≤ H :=
    (Restated.Vocabulary.Proofs.HealingSurface.stateBefore_hMax_mono facts S rho w hiN (W i)
      (hf.onePath i).1 _ (onePath_slice₅₂b W hf.onePath hiN)).trans hcap
  obtain ⟨C, hC, hCF, hCheight⟩ :=
    Restated.Vocabulary.Proofs.Bridges.storeFinalizationOnChain_stateBefore facts S rho i w (W i)
      (hf.onePath i).1
  have hCrun : Restated.RunBlockOn M S rho W Xb C :=
    Restated.runBlock_of_stateBefore_memOn facts S W Xb hw hC
  have hcrossed : (M.derive_named S.E S.cfg C).h_F <
      (M.derive_named S.E S.cfg D).h := by
    calc
      (M.derive_named S.E S.cfg C).h_F < (W i w).st.core.h_max := hCheight
      _ ≤ H := hpreCap
      _ = (M.derive_named S.E S.cfg D).h := hcarrierHeight.symm
  have hpreceq := Restated.finalized_preceq_of_height_ltOn facts
    S rho W Xb D C hsb hf.rootCollisionFree hcarrierRun hCrun hcrossed
  simpa only [hCF] using hpreceq

/-- If the holder carries `carrier` at height `H` at `t`, `lo ≤ t`, `t + 1 + Δ ≤ read ≤ horizon`,
    `w` is in the set for `t + 1 + Δ`, and the `h_max` of `w`'s store in
    `W (strictEventIndex rho read)` is at most `H`, then `carrier` is in the tree of that store. -/
theorem HonestHMaxCarrierAtOn.visibleAtReader_after_oneDelay_of_localCap (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hsb : Restated.SlashableBoundOn M S rho W Xb)
    {t read : Time} {H : Height} {holder : V} {carrier : Block V}
    (hcarrier : Restated.HonestHMaxCarrierAtOn M S rho W Hs Xb t
      (W (inclusiveEventIndex rho t)) H holder carrier)
    (hpost : lo ≤ t)
    (hdelay : t + 1 + S.E.Δ ≤ read)
    (hreadHor : read ≤ rho.horizon)
    {w : V} (hw : w ∈ Hs (t + 1 + S.E.Δ))
    (hcap : (W (strictEventIndex rho read) w).st.core.h_max ≤ H) :
    carrier ∈ (W (strictEventIndex rho read) w).st.core.T := by
  obtain ⟨D, hDerase, hDrun, hDheight⟩ := hcarrier.namedWitness
  have hsourceN : carrier ∈ (W (strictEventIndex rho (t + 1)) holder).st.core.T := by
    rw [strict_succ_eq_inclusive₅₂b rho t]
    exact hcarrier.processed
  rcases Restated.Vocabulary.Protocol.acceptsAt_block_of_processed_erased facts S rho holder W
      hf.onePath _ hsourceN with
    hgen | ⟨D', hD'erase, i, hi, ta, hacc⟩
  · rw [hgen]
    exact (Restated.genesis_mem_and_stamp_storeBeforeTimeOn facts S Hs Xb hf w read read).1
  · have hD'body : D' ∈ (W (i + 1) holder).st.bodies := of_decide_eq_true hacc.2.2
    have hD'run : Restated.RunBlockOn M S rho W Xb D' :=
      Restated.runBlock_of_stateBefore_memOn facts S W Xb (hHsXb _ hcarrier.holderHonest) hD'body
    have hEq : D' = D :=
      Restated.runBlock_unique_of_erase_eqOn_RawHeightProgress facts hf hD'run hDrun
        (hD'erase.trans hDerase.symm)
    have hD'height : (M.derive_named S.E S.cfg D').h = H := by
      rw [hEq]; exact hDheight
    have hta : ta < t + 1 := by
      obtain ⟨_, ⟨e, he, _, het⟩⟩ := hacc.1
      rw [← het]
      exact time_lt_of_lt_strict₅₂b hf.sorted he hi
    have hD'pos : 0 < D'.slot := by
      have hslot := Restated.Vocabulary.Protocol.parent_slot_lt_of_acceptsAt_block facts S W
        hf.onePath hacc
      rw [Proofs.NamedWire.erase_slot] at hslot
      exact Nat.zero_lt_of_lt hslot
    have hrelayHor : t + 1 + S.E.Δ ≤ rho.horizon := hdelay.trans hreadHor
    have hFhist : ∀ j : Nat,
        j ≤ (rho.events.filter (fun e => decide (e.time < t + 1 + S.E.Δ))).length →
          Block.Preceq (W j w).st.core.F D'.erase := by
      intro j hj
      exact Restated.exactHeightCarrier_finalizedBelowAtPrefixOn facts S Hs Xb hf hsb hD'run
        hD'height (hHsXb _ hw)
        (hj.trans (Restated.strict_filter_length_mono rho hdelay)) hcap
    have htat : ta ≤ t := Int.lt_add_one_iff.mp hta
    have hholderMax : holder ∈ Hs (max ta lo) :=
      hHs _ _ (max_le htat hpost) hcarrier.holderHonest
    have hadmit : Restated.Vocabulary.Protocol.AdmittedBefore M S rho W w D'.erase
        (t + 1 + S.E.Δ) :=
      Restated.block_admittedBefore_of_accepted_after_cutoffOn facts
        S Hs Xb hf hHs hHsXb hholderMax hw hD'pos hacc hta
          (hpost.trans (le_of_lt (lt_add_one t))) rfl hrelayHor hFhist
    have hvisible := Restated.admittedBefore_mem_and_stamp_atOn facts S Hs Xb hf hadmit hdelay
    rw [← hD'erase]
    exact hvisible.1

/-- If the holder carries `carrier` at height `H` at `t`, `lo ≤ t`, `t + 1 + Δ ≤ read ≤ horizon`,
    and the largest `h_max` over the set for `read` at `read` is at most `H`, then every member of
    that set holds `carrier` in its store in `W (strictEventIndex rho read)`. -/
theorem HonestHMaxCarrierAtOn.visibleToAll_after_oneDelay_of_noRise (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hsb : Restated.SlashableBoundOn M S rho W Xb)
    {t read : Time} {H : Height} {holder : V} {carrier : Block V}
    (hcarrier : Restated.HonestHMaxCarrierAtOn M S rho W Hs Xb t
      (W (inclusiveEventIndex rho t)) H holder carrier)
    (hpost : lo ≤ t)
    (hdelay : t + 1 + S.E.Δ ≤ read)
    (hreadHor : read ≤ rho.horizon)
    (hcap : ((Hs read).sup fun u => (W (inclusiveEventIndex rho read) u).st.core.h_max) ≤ H) :
    ∀ w ∈ Hs read,
      carrier ∈ (W (strictEventIndex rho read) w).st.core.T := by
  intro w hw
  exact hcarrier.visibleAtReader_after_oneDelay_of_localCap facts S Hs Xb hf hHs hHsXb hsb
    hpost hdelay hreadHor (hHs _ _ hdelay hw)
    (((Restated.storeBeforeTime_hMax_le_storeAtOn facts S Hs Xb hf w read).trans
      (Finset.le_sup (f := fun u => (W (inclusiveEventIndex rho read) u).st.core.h_max) hw)).trans
      hcap)

/-- If the holder carries `carrier` at height `H` at `t`, `lo ≤ t`, and
    `t + 1 + Δ ≤ read ≤ horizon`, then every member of the set for `t + 1 + Δ` has `h_max` at least
    `H` in its store in `W (strictEventIndex rho read)`. -/
theorem HonestHMaxCarrierAtOn.localFrontier_ge_after_oneDelay (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hsb : Restated.SlashableBoundOn M S rho W Xb)
    {t read : Time} {H : Height} {holder : V} {carrier : Block V}
    (hcarrier : Restated.HonestHMaxCarrierAtOn M S rho W Hs Xb t
      (W (inclusiveEventIndex rho t)) H holder carrier)
    (hpost : lo ≤ t)
    (hdelay : t + 1 + S.E.Δ ≤ read)
    (hreadHor : read ≤ rho.horizon) :
    ∀ w ∈ Hs (t + 1 + S.E.Δ), H ≤ (W (strictEventIndex rho read) w).st.core.h_max := by
  intro w hw
  have hwXb : w ∈ Xb := hHsXb _ hw
  by_cases hbound : H ≤ (W (strictEventIndex rho read) w).st.core.h_max
  · exact hbound
  have hmem := hcarrier.visibleAtReader_after_oneDelay_of_localCap facts S Hs Xb hf hHs hHsXb hsb
    hpost hdelay hreadHor hw (Nat.le_of_lt (Nat.lt_of_not_ge hbound))
  have hworld := mem_stateBeforeTime_path₅₂b S rho hf.sorted W hf.onePath read
  obtain ⟨D, hDmem, hDerase⟩ :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime facts S rho read w
      _ hworld hmem
  have hDrun : Restated.RunBlockOn M S rho W Xb D :=
    Restated.runBlock_of_stateBefore_memOn facts S W Xb hwXb hDmem
  obtain ⟨Dcarrier, hDcarrierErase, hDcarrierRun, hDcarrierHeight⟩ :=
    hcarrier.namedWitness
  have hEqCarrier : D = Dcarrier :=
    Restated.runBlock_unique_of_erase_eqOn_RawHeightProgress facts hf hDrun hDcarrierRun
      (hDerase.trans hDcarrierErase.symm)
  have hheight : (M.derive_named S.E S.cfg D).h = H := by
    rw [hEqCarrier]; exact hDcarrierHeight
  have hmax := Restated.Vocabulary.Proofs.NamedStoreBridge.heights_le_hMax_stateBeforeTime facts S rho
    read w _ hworld D hDmem
  rw [hheight] at hmax
  exact absurd hmax hbound

/-- If the holder carries `carrier` at height `H` at `t`, `lo ≤ t`, `t + 1 + Δ ≤ read ≤ horizon`,
    and the largest `h_max` over the set for `read` at `read` is at most `H`, then every member of
    that set holds `carrier` in its store in `W (strictEventIndex rho read)`, whose `h_max` is
    exactly `H`. -/
theorem HonestHMaxCarrierAtOn.visibleWithExactFrontier_after_oneDelay_of_noRise
    (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hsb : Restated.SlashableBoundOn M S rho W Xb)
    {t read : Time} {H : Height} {holder : V} {carrier : Block V}
    (hcarrier : Restated.HonestHMaxCarrierAtOn M S rho W Hs Xb t
      (W (inclusiveEventIndex rho t)) H holder carrier)
    (hpost : lo ≤ t)
    (hdelay : t + 1 + S.E.Δ ≤ read)
    (hreadHor : read ≤ rho.horizon)
    (hcap : ((Hs read).sup fun u => (W (inclusiveEventIndex rho read) u).st.core.h_max) ≤ H) :
    ∀ w ∈ Hs read,
      carrier ∈ (W (strictEventIndex rho read) w).st.core.T ∧
        (W (strictEventIndex rho read) w).st.core.h_max = H := by
  intro w hw
  have hmem := hcarrier.visibleToAll_after_oneDelay_of_noRise
    facts S Hs Xb hf hHs hHsXb hsb hpost hdelay hreadHor hcap w hw
  refine ⟨hmem, ?_⟩
  have hlower := hcarrier.localFrontier_ge_after_oneDelay facts S Hs Xb hf hHs hHsXb hsb
    hpost hdelay hreadHor w (hHs _ _ hdelay hw)
  have hupper : (W (strictEventIndex rho read) w).st.core.h_max ≤ H :=
    ((Restated.storeBeforeTime_hMax_le_storeAtOn facts S Hs Xb hf w read).trans
      (Finset.le_sup (f := fun u => (W (inclusiveEventIndex rho read) u).st.core.h_max) hw)).trans
      hcap
  exact Nat.le_antisymm hupper hlower

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation

/-- If the largest `h_max` over the set for `S.a start` at `S.a start` is `Mh`, `lo ≤ S.a start`,
    the largest over the set for `S.a (start + 1)` at that time is at most `Mh`, and `2 ≤ Mh`, then
    either some member of the set for `S.a (start + 1)` reads a fixed-height justification root at
    height `Mh` there, or every member has `h_j + 2 ≤ Mh` and `h_max = Mh` before `S.a (start + 1)`. -/
theorem frontierRegime_after_oneDelayOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hfb : Execution.BelowOneThird S (Hs rho.horizon))
    (hsb : Restated.SlashableBoundOn M S rho W Xb)
    {start : Round} {Mh : Height}
    (hM : ((Hs (Restated.Vocabulary.Execution.Setup.a M S start)).sup fun u =>
      (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S start)) u).st.core.h_max) = Mh)
    (hpost : lo ≤ Restated.Vocabulary.Execution.Setup.a M S start)
    (hcap : ((Hs (Restated.Vocabulary.Execution.Setup.a M S (start + 1))).sup fun u =>
      (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (start + 1))) u).st.core.h_max) ≤ Mh)
    (hhor : Restated.Vocabulary.Execution.Setup.a M S (start + 1) ≤ rho.horizon) (h2 : 2 ≤ Mh) :
    (∃ u ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S (start + 1)),
      Restated.FixedHeightJustificationRootAtReadOn M S rho W Hs Xb Mh u
        (Restated.Vocabulary.Execution.Setup.a M S (start + 1))
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (start + 1))))) ∨
    (∀ w ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S (start + 1)),
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (start + 1))) w).st.core.h_j
          + 2 ≤ Mh ∧
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (start + 1))) w).st.core.h_max
          = Mh) := by
  set read := Restated.Vocabulary.Execution.Setup.a M S (start + 1) with hread
  set n := inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S start) with hn
  have hpred : Mh - 1 + 1 = Mh :=
    Nat.sub_add_cancel ((by decide : 1 ≤ 2).trans h2)
  have hprefixSucc : ((Hs (Restated.Vocabulary.Execution.Setup.a M S start)).sup fun u =>
      (W n u).st.core.h_max) = Mh - 1 + 1 := by
    rw [hpred]; exact hM
  obtain ⟨holder, hholder, carrier, hcarrierMem, hcarrierRun, hcarrierHeight⟩ :=
    Restated.exists_honest_exactHMaxCarrierAtPrefixOn facts S Hs Xb
      (Hs (Restated.Vocabulary.Execution.Setup.a M S start)) hf (hHsXb _) n (Mh - 1) hprefixSucc
  have hcoh := (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho n holder
    (W n) (hf.onePath n).1).1.1.1
  have hcarrierT : carrier.erase ∈ (W n holder).st.core.T := by
    rw [hcoh.1]
    exact Finset.mem_image_of_mem _ hcarrierMem
  have hcarrier : Restated.HonestHMaxCarrierAtOn M S rho W Hs Xb
      (Restated.Vocabulary.Execution.Setup.a M S start) (W n) Mh holder carrier.erase :=
    { holderHonest := hholder
      processed := hcarrierT
      namedWitness := ⟨carrier, rfl, hcarrierRun, by rw [hcarrierHeight, hpred]⟩ }
  have hrelayStep : Restated.Vocabulary.Execution.Setup.a M S start + 1 + S.E.Δ ≤ read :=
    Restated.action_add_one_add_delta_le_next_action_l52 facts S start
  have hexact : ∀ w ∈ Hs read, (W (strictEventIndex rho read) w).st.core.h_max = Mh := by
    intro w hw
    exact (hcarrier.visibleWithExactFrontier_after_oneDelay_of_noRise
      facts S Hs Xb hf hHs hHsXb hsb hpost hrelayStep hhor hcap w hw).2
  by_cases hgate : ∃ u ∈ Hs read, (W (strictEventIndex rho read) u).st.core.h_j = Mh - 1
  · rcases hgate with ⟨u, hu, hju⟩
    left
    refine ⟨u, hu, ?_⟩
    obtain ⟨C, hC, hCrun, hjust⟩ :=
      Restated.justificationCarrierAtStrictRead_l1On facts S Hs Xb hf (hHsXb _ hu) read
    have hjust' : Restated.Vocabulary.Internal.NamedJustifiedAt M S.E S.cfg C
        (W (strictEventIndex rho read) u).st.J (Mh - 1) := by
      rw [← hju]; exact hjust
    have hMsubPos : 0 < Mh - 1 :=
      Nat.sub_pos_iff_lt.mpr ((by decide : 1 < 2).trans_le h2)
    have hcert : Restated.CertificateOn M S rho W Xb (Mh - 1)
        (W (strictEventIndex rho read) u).st.J.root :=
      Restated.certificate_of_justifiedRunBlock_l1On facts S Xb hCrun hjust'
        (Nat.ne_of_gt hMsubPos)
    refine
      { readerHonest := hu
        readInHorizon := hhor
        carrierExists := ⟨C, hC, hCrun, hjust⟩
        targetHeightPositive := hMsubPos
        fixedTarget :=
          { frontier := hexact u hu
            justificationHeight := hju
            gate := by rw [hexact u hu, hju, hpred]
            certificate := hcert
            uniqueAtHeight := ?_
            targetBlock := Restated.runBlockOf_justified_atStrictRead_l1On facts S Hs Xb hf
              (hHsXb _ hu) read } }
    intro T hT
    exact Restated.certificateTarget_uniqueOn facts S Hs Xb hf hHs hfb (Mh - 1) T
      (W (strictEventIndex rho read) u).st.J.root hT hcert
  · right
    intro w hw
    have hbelow : (W (strictEventIndex rho read) w).st.core.h_j < Mh := by
      have hbelow' := Restated.Vocabulary.Proofs.NamedJustificationBound.justificationBelowMax_stateBeforeTime
        facts S rho read w _ (mem_stateBeforeTime_path₅₂b S rho hf.sorted W hf.onePath read)
      have hbelow'' : (W (strictEventIndex rho read) w).st.core.h_j <
          (W (strictEventIndex rho read) w).st.core.h_max := by
        simpa only [Restated.Vocabulary.Internal.JustificationBelowMax] using hbelow'
      rw [← hexact w hw]; exact hbelow''
    have hne : (W (strictEventIndex rho read) w).st.core.h_j ≠ Mh - 1 := by
      intro heq
      exact hgate ⟨w, hw, heq⟩
    refine ⟨?_, hexact w hw⟩
    have hlt : (W (strictEventIndex rho read) w).st.core.h_j < Mh - 1 :=
      lt_of_le_of_ne (Nat.le_pred_of_lt hbelow) hne
    have hstep := Nat.add_le_add_right (Nat.succ_le_of_lt hlt) 1
    rw [hpred] at hstep
    exact hstep

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation

/-- The form of `frontierRegime_after_oneDelayOn` over a window `[lo, hi]` with
    `S.a start + 1 + Δ ≤ lo`: either some member of the set for `hi` reads a fixed-height
    justification root at height `Mh` at some `read` in the window, or at every `read` in the window
    every member has `h_j + 2 ≤ Mh` and `h_max = Mh`. -/
theorem frontierRegime_window_after_oneDelayOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo₀ : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo₀)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hfb : Execution.BelowOneThird S (Hs rho.horizon))
    (hsb : Restated.SlashableBoundOn M S rho W Xb)
    {start : Round} {Mh : Height} {lo hi : Time}
    (hM : ((Hs (Restated.Vocabulary.Execution.Setup.a M S start)).sup fun u =>
      (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S start)) u).st.core.h_max) = Mh)
    (hpost : lo₀ ≤ Restated.Vocabulary.Execution.Setup.a M S start)
    (hrelay : Restated.Vocabulary.Execution.Setup.a M S start + 1 + S.E.Δ ≤ lo)
    (hcap : ((Hs hi).sup fun u => (W (inclusiveEventIndex rho hi) u).st.core.h_max) ≤ Mh)
    (hhor : hi ≤ rho.horizon) (h2 : 2 ≤ Mh) :
    (∃ u ∈ Hs hi, ∃ read : Time, lo ≤ read ∧ read ≤ hi ∧
      Restated.FixedHeightJustificationRootAtReadOn M S rho W Hs Xb Mh u read
        (W (strictEventIndex rho read))) ∨
    (∀ read : Time, lo ≤ read → read ≤ hi → ∀ w ∈ Hs hi,
      (W (strictEventIndex rho read) w).st.core.h_j + 2 ≤ Mh ∧
        (W (strictEventIndex rho read) w).st.core.h_max = Mh) := by
  set n := inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S start) with hn
  have hpred : Mh - 1 + 1 = Mh :=
    Nat.sub_add_cancel ((by decide : 1 ≤ 2).trans h2)
  have hprefixSucc : ((Hs (Restated.Vocabulary.Execution.Setup.a M S start)).sup fun u =>
      (W n u).st.core.h_max) = Mh - 1 + 1 := by
    rw [hpred]; exact hM
  obtain ⟨holder, hholder, carrier, hcarrierMem, hcarrierRun, hcarrierHeight⟩ :=
    Restated.exists_honest_exactHMaxCarrierAtPrefixOn facts S Hs Xb
      (Hs (Restated.Vocabulary.Execution.Setup.a M S start)) hf (hHsXb _) n (Mh - 1) hprefixSucc
  have hcoh := (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho n holder
    (W n) (hf.onePath n).1).1.1.1
  have hcarrierT : carrier.erase ∈ (W n holder).st.core.T := by
    rw [hcoh.1]
    exact Finset.mem_image_of_mem _ hcarrierMem
  have hcarrier : Restated.HonestHMaxCarrierAtOn M S rho W Hs Xb
      (Restated.Vocabulary.Execution.Setup.a M S start) (W n) Mh holder carrier.erase :=
    { holderHonest := hholder
      processed := hcarrierT
      namedWitness := ⟨carrier, rfl, hcarrierRun, by rw [hcarrierHeight, hpred]⟩ }
  have hexact : ∀ read : Time, lo ≤ read → read ≤ hi → ∀ w ∈ Hs hi,
      (W (strictEventIndex rho read) w).st.core.h_max = Mh := by
    intro read hlo hhi w hw
    have hreadHor : read ≤ rho.horizon := hhi.trans hhor
    have hdelay : Restated.Vocabulary.Execution.Setup.a M S start + 1 + S.E.Δ ≤ read :=
      hrelay.trans hlo
    have hupper : (W (strictEventIndex rho read) w).st.core.h_max ≤ Mh := by
      have hmono := Restated.honestHMaxAt_monoOn facts S Hs Xb (Hs hi) hf hhi
      have hloc := Finset.le_sup (f := fun u => (W (inclusiveEventIndex rho read) u).st.core.h_max) hw
      exact ((Restated.storeBeforeTime_hMax_le_storeAtOn facts S Hs Xb hf w read).trans
        (hloc.trans hmono)).trans hcap
    have hwDelay : w ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S start + 1 + S.E.Δ) :=
      hHs _ _ (hdelay.trans hhi) hw
    have hlower := hcarrier.localFrontier_ge_after_oneDelay facts S Hs Xb hf hHs hHsXb hsb
      hpost hdelay hreadHor w hwDelay
    exact Nat.le_antisymm hupper hlower
  by_cases hgate : ∃ u ∈ Hs hi, ∃ read : Time, lo ≤ read ∧ read ≤ hi ∧
      (W (strictEventIndex rho read) u).st.core.h_j = Mh - 1
  · rcases hgate with ⟨u, hu, read, hlo, hhi, hju⟩
    left
    refine ⟨u, hu, read, hlo, hhi, ?_⟩
    obtain ⟨C, hC, hCrun, hjust⟩ :=
      Restated.justificationCarrierAtStrictRead_l1On facts S Hs Xb hf (hHsXb _ hu) read
    have hjust' : Restated.Vocabulary.Internal.NamedJustifiedAt M S.E S.cfg C
        (W (strictEventIndex rho read) u).st.J (Mh - 1) := by
      rw [← hju]; exact hjust
    have hMsubPos : 0 < Mh - 1 :=
      Nat.sub_pos_iff_lt.mpr ((by decide : 1 < 2).trans_le h2)
    have hcert : Restated.CertificateOn M S rho W Xb (Mh - 1)
        (W (strictEventIndex rho read) u).st.J.root :=
      Restated.certificate_of_justifiedRunBlock_l1On facts S Xb hCrun hjust'
        (Nat.ne_of_gt hMsubPos)
    refine
      { readerHonest := hHs _ _ hhi hu
        readInHorizon := hhi.trans hhor
        carrierExists := ⟨C, hC, hCrun, hjust⟩
        targetHeightPositive := hMsubPos
        fixedTarget :=
          { frontier := hexact read hlo hhi u hu
            justificationHeight := hju
            gate := by rw [hexact read hlo hhi u hu, hju, hpred]
            certificate := hcert
            uniqueAtHeight := ?_
            targetBlock := Restated.runBlockOf_justified_atStrictRead_l1On facts S Hs Xb hf
              (hHsXb _ hu) read } }
    intro T hT
    exact Restated.certificateTarget_uniqueOn facts S Hs Xb hf hHs hfb (Mh - 1) T
      (W (strictEventIndex rho read) u).st.J.root hT hcert
  · right
    intro read hlo hhi w hw
    have hbelow : (W (strictEventIndex rho read) w).st.core.h_j < Mh := by
      have hbelow' := Restated.Vocabulary.Proofs.NamedJustificationBound.justificationBelowMax_stateBeforeTime
        facts S rho read w _ (mem_stateBeforeTime_path₅₂b S rho hf.sorted W hf.onePath read)
      have hbelow'' : (W (strictEventIndex rho read) w).st.core.h_j <
          (W (strictEventIndex rho read) w).st.core.h_max := by
        simpa only [Restated.Vocabulary.Internal.JustificationBelowMax] using hbelow'
      rw [← hexact read hlo hhi w hw]; exact hbelow''
    have hne : (W (strictEventIndex rho read) w).st.core.h_j ≠ Mh - 1 := by
      intro heq
      exact hgate ⟨w, hw, read, hlo, hhi, heq⟩
    refine ⟨?_, hexact read hlo hhi w hw⟩
    have hlt : (W (strictEventIndex rho read) w).st.core.h_j < Mh - 1 :=
      lt_of_le_of_ne (Nat.le_pred_of_lt hbelow) hne
    have hstep := Nat.add_le_add_right (Nat.succ_le_of_lt hlt) 1
    rw [hpred] at hstep
    exact hstep

end

end DecoupledConsensusModel.Sts.Restated
