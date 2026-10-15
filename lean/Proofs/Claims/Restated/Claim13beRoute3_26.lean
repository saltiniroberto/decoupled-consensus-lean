import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.RunAll
import Proofs.Claims.Restated.Vocabulary_Execution_Acceptance
import Proofs.Claims.Restated.Vocabulary_Execution_BodyRetention
import Proofs.Claims.Restated.Vocabulary_Execution_ReceiptCalls
import Proofs.Claims.Restated.Vocabulary_Execution_ReceiptCallsBase
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Claims.Restated.Vocabulary_Protocol_Duties_Proposals_Actions
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_Admission
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_BlockStamp
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_Blocks
import Proofs.Vocabulary.Protocol.Handlers.Invariants
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_RelayGuards
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Proofs.Vocabulary.Protocol.Schedule.NamedTick
import Model.Conditions.RunAll
import Model.Conditions.Sts_Conditions
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedReceiptCalls
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Healing_Action
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_Schedule_Alignment
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_25
import Proofs.Claims.Spec2Claims.Claim13beRoute3_26

/-!
# Acceptance, handling and block stamps along a path of the run

A block is accepted no earlier than its slot's proposal time, a handled block that descends from the
receiver's finalized block is held, acceptances behind held blocks come before a cutoff, held bodies
are stamped before the current time, and deliveries in the run built from an execution find their
dependencies. Stated over a model `M : Record.Model V`.
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

/-- If `w₁` can hold before the `(n + 1)`-th event of `rho`, then some world `w₀` that can hold
    before the `n`-th event leads to `w₁` by the `n`-th event. -/
private theorem stateBeforeOf_succ_split (S : Setup V) (rho : Record.Run V) (n : Nat)
    (w₁ : V → M.N) (hw₁ : w₁ ∈ Record.stateBeforeOf M S rho (n + 1)) :
    ∃ w₀ ∈ Record.stateBeforeOf M S rho n,
      w₁ ∈ ((rho.events.drop n).take (n + 1 - n)).foldlM (Record.worldStepOf M S) w₀ := by
  unfold Record.stateBeforeOf at hw₁ ⊢
  rw [Nat.add_sub_cancel_left]
  rw [List.take_add, List.foldlM_append, Set.bind_def] at hw₁
  obtain ⟨w₀, hw₀, h2⟩ := Set.mem_iUnion₂.mp hw₁
  exact ⟨w₀, hw₀, h2⟩

/-- If the `n`-th event of `rho` is `u`'s wake at `t`, and `w₁` is reached from `w₀` by that event,
    then `v`'s store in `w₁` is `v`'s store in `w₀`. -/
private theorem wake_step_st₂₆ (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    {n : Nat} {u : V} {t : Time} (he : rho.events[n]? = some (.wake u t)) (w₀ w₁ : V → M.N)
    (hstep : w₁ ∈ ((rho.events.drop n).take (n + 1 - n)).foldlM (Record.worldStepOf M S) w₀)
    (v : V) : (w₁ v).st = (w₀ v).st := by
  have hl : (rho.events.drop n).take (n + 1 - n) = [.wake u t] := by
    rw [Nat.add_sub_cancel_left, List.take_one, List.head?_drop, he]
    rfl
  rw [hl, List.foldlM_cons, Set.bind_def] at hstep
  obtain ⟨w', hw', h2⟩ := Set.mem_iUnion₂.mp hstep
  obtain rfl := Set.mem_singleton_iff.mp h2
  have hw'' : w₁ = Function.update w₀ u (M.wake (w₀ u)) := hw'
  subst hw''
  by_cases hv : v = u
  · subst hv
    rw [Function.update_self]
    exact (facts.nd.wake_st_record _).1
  · rw [Function.update_of_ne hv]

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedRelayGuards
set_option autoImplicit false
open Execution

/-- In a run sorted by key and inside its horizon, for every path `W` of the run, a block accepted
    along `W` is accepted at or after the proposal time of its slot. -/
theorem Vocabulary.Proofs.NamedRelayGuards.proposal_time_le_acceptance_of_fields (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    (hin : ∀ e ∈ rho.events, 0 ≤ e.time ∧ e.time ≤ rho.horizon)
    {i : Nat} {v : V} {B : NamedBlock V} {ta : Time}
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    (hacc : Restated.Vocabulary.Execution.NamedRun.acceptsAt M S rho W i v (.block B) ta) :
    M.proposal_time S.E B.erase.slot ≤ ta := by
  have _hr_0 : M.reachedNode (W i v) := facts.ndRun.stateBeforeOf_reachedNode S rho i (W i) (hW i).1 v
  have _hv_0 : M.runs_as (W i v) v := facts.ndRun.stateBeforeOf_runs_as S rho i (W i) (hW i).1 v
  have _hr_1 : M.reachedNode (W (i + 1) v) := facts.ndRun.stateBeforeOf_reachedNode S rho (i + 1) (W (i + 1)) (hW (i + 1)).1 v
  have _hv_1 : M.runs_as (W (i + 1) v) v := facts.ndRun.stateBeforeOf_runs_as S rho (i + 1) (W (i + 1)) (hW (i + 1)).1 v
  obtain ⟨⟨hproc, e, he, -, het⟩, hpre', hpost'⟩ := hacc
  have hpre : B ∉ (W i v).st.bodies := by
    simpa only [Restated.Vocabulary.Execution.Object.processed, decide_eq_false_iff_not] using hpre'
  have hpost : B ∈ (W (i + 1) v).st.bodies := by
    simpa only [Restated.Vocabulary.Execution.Object.processed, decide_eq_true_eq] using hpost'
  rcases hproc with ⟨t, htick, out, hout, hw, -⟩ | ⟨t, hdel⟩
  · obtain rfl : e = .tick v t := Option.some.inj (he.symm.trans htick)
    have ht : t = ta := het
    subst ht
    have hnonneg : 0 ≤ t := (hin _ (List.mem_of_getElem? htick)).1
    rw [hw] at hpost
    -- the tick sent `B`, so `B` is its proposal
    have hsent := facts.nd.tick_new_body_origin S v (W i v) t out hout B hpre hpost
    obtain ⟨-, hD⟩ := facts.nd.block_mem_on_tick_emit S v (W i v) t out hout hsent
    obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc (W i v).st.core.toHealing t
      (W i v).cache
    obtain ⟨D, hDD⟩ := facts.dt.propose_block_with_nonempty S v (W i v) t out hout
      (facts.nd.block_mem_on_tick_emit S v (W i v) t out hout hsent).1.1 (facts.nd.block_mem_on_tick_emit S v (W i v) t out hout hsent).1.2.1
      (facts.nd.block_mem_on_tick_emit S v (W i v) t out hout hsent).1.2.2
      (facts.nd.block_mem_on_tick_emit_awake S v (W i v) t out hout hsent) c hc
    have hslot := facts.dt.propose_block_with_slot _ _ _ _ _ _ D hDD (hD c hc D hDD)
    rw [facts.hd.Sts_setClock_core_s] at hslot
    have hslot' : B.erase.slot ≤ S.E.slotOf t := by
      rw [Proofs.NamedWire.erase_slot, hslot]
    exact (facts.sch.proposal_time_mono S.E hslot').trans
      (facts.sch.proposal_time_slotOf_le S.E hnonneg)
  · obtain rfl : e = .deliver v (.block B) t := Option.some.inj (he.symm.trans hdel)
    have ht : t = ta := het
    subst ht
    have hnonneg : 0 ≤ t := (hin _ (List.mem_of_getElem? hdel)).1
    rcases Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_deliver facts S rho hdel (W i) (hW i).1
        (W (i + 1)) (hW i).2 with hproc | ⟨-, hsame⟩
    · rw [facts.nd.process_st S (W i v) _ (W (i + 1) v) hproc,
        facts.nd.make_grades_compatible_with_finalized_bodies, facts.nd.process_block] at hpost
      have hslot := (facts.hd.new_body_guards S.E S.hc S.cfg _ B hpre hpost).1
      have htime : (W i v).st.core.t ≤ t :=
        Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_clock_le_event facts S rho hsorted hdel
          hnonneg v (W i) (hW i).1
      have hs : Restated.Vocabulary.Proofs.Optimistic.SlotOfClock M S.E (W i v).st.core :=
        Restated.Vocabulary.Proofs.NamedStoreBridge.slotOfClock_stateBefore facts S rho i v (W i) (hW i).1
      unfold Restated.Vocabulary.Proofs.Optimistic.SlotOfClock at hs
      have hclock0 : 0 ≤ (W i v).st.core.t := by
        have h := Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_clock_mono facts S rho hsorted
          (fun e he => (hin e he).1) v (Nat.zero_le i) (fun v' => M.initial S v')
          (by rw [Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_zero facts]; exact Set.mem_singleton _)
          (W i) (by simpa only [List.drop_zero, Nat.sub_zero, Record.stateBeforeOf] using (hW i).1)
        exact (le_of_eq (facts.nd.initial_clock_eq_zero S v).symm).trans h
      have hslot' : B.erase.slot ≤ S.E.slotOf (W i v).st.core.t := by
        rw [← hs]; exact hslot
      exact (facts.sch.proposal_time_mono S.E hslot').trans
        ((facts.sch.proposal_time_slotOf_le S.E hclock0).trans htime)
    · rw [hsame] at hpost
      exact absurd hpost hpre

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedRelayGuards
set_option autoImplicit false
open Execution

/-- For every path `W` of the run: if every delivered block's parent is among the receiver's bodies
    in the world of `W` before the delivery, an honest source accepted `B` at index `i`, an honest
    receiver handles `B` at index `j`, the receiver's finalized block in `W j` is an ancestor of
    `B`, and a delivery there finds the receiver's slot in `W j` at least `B`'s, then the receiver
    holds `B` in `W (j + 1)`. -/
theorem Vocabulary.Proofs.NamedRelayGuards.handled_block_held_of_finalized_prefix_of_fields (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (W : Nat → V → M.N)
    (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    (hdeps : ∀ (i : Nat) (v : V) (o : NamedObject V) (t : Time),
      rho.events[i]? = some (.deliver v o t) →
        ∀ C : NamedBlock V, o = .block C → C.parent ∈ (W i v).st.bodies)
    (roots : Restated.Vocabulary.Execution.NamedRootCollisionFree M S rho W)
    {i j : Nat} {source receiver : V} {B : NamedBlock V} {ta td : Time}
    (hsource : source ∈ rho.honest) (hreceiver : receiver ∈ rho.honest)
    (hacc : Restated.Vocabulary.Execution.NamedRun.acceptsAt M S rho W i source (.block B) ta)
    (hcall : Restated.Vocabulary.Execution.NamedRun.actualHandlesAt M S rho W j receiver (.block B) td)
    (hrecv : rho.events[j]? = some (.deliver receiver (.block B) td) →
      B.erase.slot ≤ (W j receiver).st.core.s)
    (hF : Block.Preceq (W j receiver).st.core.F B.erase) :
    B ∈ (W (j + 1) receiver).st.bodies := by
  have _hr_0 : M.reachedNode (W j receiver) := facts.ndRun.stateBeforeOf_reachedNode S rho j (W j) (hW j).1 receiver
  have _hv_0 : M.runs_as (W j receiver) receiver := facts.ndRun.stateBeforeOf_runs_as S rho j (W j) (hW j).1 receiver
  have _hr_1 : M.reachedNode (W (i + 1) source) := facts.ndRun.stateBeforeOf_reachedNode S rho (i + 1) (W (i + 1)) (hW (i + 1)).1 source
  have _hv_1 : M.runs_as (W (i + 1) source) source := facts.ndRun.stateBeforeOf_runs_as S rho (i + 1) (W (i + 1)) (hW (i + 1)).1 source
  have _hr_2 : M.reachedNode (W (j + 1) receiver) := facts.ndRun.stateBeforeOf_reachedNode S rho (j + 1) (W (j + 1)) (hW (j + 1)).1 receiver
  have _hv_2 : M.runs_as (W (j + 1) receiver) receiver := facts.ndRun.stateBeforeOf_runs_as S rho (j + 1) (W (j + 1)) (hW (j + 1)).1 receiver
  by_cases hheld : B ∈ (W j receiver).st.bodies
  · exact Restated.Vocabulary.Proofs.NamedBodyRetention.stateBefore_bodies_mono facts S rho receiver
      (Nat.le_succ j) (W j) (hW j).1 (W (j + 1)) (hW j).2 hheld
  have haccepted : B ∈ (W (i + 1) source).st.bodies := by
    simpa only [Restated.Vocabulary.Execution.Object.processed, decide_eq_true_eq] using hacc.2.2
  have hscope := Restated.Vocabulary.Proofs.NamedRuntime.blockInRun_of_direct facts S rho W hW
    (Restated.Vocabulary.Proofs.NamedRuntime.directBlock_of_prefix facts S rho W hW hsource (i + 1)
      haccepted)
  have hcoh := (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho j receiver
    (W j) (hW j).1).1.1.1
  -- an alias of `B` in the receiver's tree is a held body with `B`'s root, so `B` itself by the
  -- root-collision hypothesis
  have hfresh : B.erase ∉ (W j receiver).st.core.T := by
    intro hgeom
    rw [hcoh.1] at hgeom
    obtain ⟨C, hC, he⟩ := Finset.mem_image.mp hgeom
    have hCscope := Restated.Vocabulary.Proofs.NamedRuntime.blockInRun_of_direct facts S rho W hW
      (Restated.Vocabulary.Proofs.NamedRuntime.directBlock_of_prefix facts S rho W hW hreceiver j hC)
    have hroot : C.root = B.root :=
      (Proofs.NamedWire.erase_root C).symm.trans
        ((congrArg Block.root he).trans (Proofs.NamedWire.erase_root B))
    have hCB : C = B := roots.root_injective C B hCscope hscope C B
      (Or.inl (Proofs.NamedAncestry.named_self C)) (Or.inr (Proofs.NamedAncestry.named_self B))
      hroot
    exact hheld (by simpa only [hCB] using hC)
  obtain ⟨hproposer, hparent, hcarried⟩ :=
    Restated.Vocabulary.Proofs.NamedRelayGuards.accepted_block_static_guards facts S rho W hW hacc
  have hinsert : ∀ st0 : M.NS, st0.core.T = (W j receiver).st.core.T →
      st0.core.F = (W j receiver).st.core.F → B.parent ∈ st0.bodies →
      B.parent ∈ (W j receiver).st.bodies → B.erase.slot ≤ st0.core.s → M.reachedStore st0 →
      B ∈ (M.on_block_with .alsoCarried S.E S.hc S.cfg st0 B).bodies := by
    intro st0 hT hF0 hp hpW hslot _hrs0
    rw [facts.hd.on_block_with_bodies_eq S .alsoCarried st0 B,
      facts.hd.process_block_core_bodies_eq_commit S.E S.hc S.cfg hp]
    refine facts.hd.mem_commitBlock_bodies_of_fresh S.E S.hc S.cfg rfl ⟨by rw [hT]; exact hfresh, ?_⟩
    rw [facts.hd.sameCore_T (facts.hd.process_block_core_of_parent_mem S.E S.hc S.cfg hp),
      facts.hd.commit_core _ _ B (facts.hd.on_block_checked_using_store_part S.E S.hc S.cfg st0 B)]
    have hparentTree : B.erase.parent ∈ st0.core.T := by
      rw [Proofs.NamedWire.erase_parent, hT, hcoh.1]
      exact Finset.mem_image_of_mem NamedBlock.erase hpW
    rw [facts.hd.on_block_checked_using_of_admissible _ S.hc st0.core hcarried]
    exact facts.hd.mem_T_on_block_using S.E st0.core B.erase _ hslot (by rw [hT]; exact hfresh)
      hparentTree (Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mpr (by rw [hF0]; exact hF))
      hproposer hparent (facts.sto.rootFresh_of_distinct _ _ (fun C hC hr => by
        -- a tree block with `B.erase`'s root is the erasure of a held body of the receiver, which
        -- the root-collision hypothesis makes `B`
        rw [hT, hcoh.1] at hC
        obtain ⟨D, hD, hDe⟩ := Finset.mem_image.mp hC
        have hDB : D = B :=
          roots.root_injective D B
            (Restated.Vocabulary.Proofs.NamedRuntime.blockInRun_of_direct facts S rho W hW
              (Restated.Vocabulary.Proofs.NamedRuntime.directBlock_of_prefix facts S rho W hW
                hreceiver j hD))
            hscope D B (Or.inl (Proofs.NamedAncestry.named_self D))
            (Or.inr (Proofs.NamedAncestry.named_self B))
            (by rw [← Proofs.NamedWire.erase_root D, hDe, hr, Proofs.NamedWire.erase_root B])
        rw [← hDe, hDB]))
  obtain ⟨hidx, e, he, -, het⟩ := hcall
  rcases hidx with ⟨t, htick, out, hout, hw1, hB⟩ | ⟨t, hdel⟩
  · -- the handle is the receiver's own proposal at its tick
    have hemit := (facts.nd.block_mem_on_tick_emit S receiver (W j receiver) t out hout hB).1
    obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc (W j receiver).st.core.toHealing t
      (W j receiver).cache
    obtain ⟨D, hDD⟩ := facts.dt.propose_block_with_nonempty S receiver (W j receiver) t out hout
      (facts.nd.block_mem_on_tick_emit S receiver (W j receiver) t out hout hB).1.1 (facts.nd.block_mem_on_tick_emit S receiver (W j receiver) t out hout hB).1.2.1
      (facts.nd.block_mem_on_tick_emit S receiver (W j receiver) t out hout hB).1.2.2
      (facts.nd.block_mem_on_tick_emit_awake S receiver (W j receiver) t out hout hB) c hc
    have heq := Restated.Vocabulary.Proofs.NamedReceiptCallsBase.self_proposal_call facts S rho htick
      (W j) (hW j).1 out hout hB c hc D hDD
    have hsnd : D.2 = some B := by rw [heq]
    obtain ⟨o, ho⟩ := facts.dt.proposal_with_nonempty (M.frameContract c) .poolAndCarried S.E S.hc
      (S.node receiver) (M.ns_setClock S.E (W j receiver).st t)
    have hprop : M.proposal_with (M.frameContract c) .poolAndCarried S.E S.hc (S.node receiver)
        (M.ns_setClock S.E (W j receiver).st t) ⇢ some B :=
      facts.dt.proposal_with_of_propose_block_with _ _ _ _ _ _ D hDD hsnd o ho ▸ ho
    obtain ⟨input, hinput⟩ := facts.dt.with_proposal_input_nonempty (M.frameContract c) S.E S.hc
      (S.node receiver) (M.toHealing (M.ns_setClock S.E (W j receiver).st t).core)
    obtain ⟨L, hL⟩ := facts.dt.select_nonempty .poolAndCarried S.hc
      (M.ns_setClock S.E (W j receiver).st t)
    have _hrs : M.reachedStore (M.ns_setClock S.E (W j receiver).st t) :=
      facts.sto.reachedStore_setClock S.E _ t (facts.nd.reachedStore_of_node _ _hr_0)
    have hpay := Restated.Vocabulary.Proofs.NamedActions.proposal_payload facts _ .poolAndCarried
      S.E S.hc (S.node receiver) _ B hprop input hinput L hL
    have hpW : B.parent ∈ (W j receiver).st.bodies := by
      rw [← facts.hd.ModelProperties_setClock_bodies S.E _ t]
      exact hpay.1
    have hbodies := ((facts.nd.tick_bodies_and_coreT_from_proposal S receiver (W j receiver) t out
      hout).1 ⟨hemit.1, hemit.2.1, by rw [S.node_val_index]; exact hemit.2.2,
        facts.nd.block_mem_on_tick_emit_awake S receiver (W j receiver) t out hout hB⟩ c hc D hDD).1
    rw [hw1, hbodies, heq]
    simp only [facts.nd.store_with_cache_bodies]
    refine hinsert _ (facts.hd.ModelProperties_setClock_core_T S.E _ t)
      (facts.hd.setClock_core_F S.E _ t) hpay.1 hpW ?_ _hrs
    rw [Proofs.NamedWire.erase_slot, facts.dt.propose_block_with_slot _ _ _ _ _ _ D hDD hsnd]
  · -- the handle is a delivery of `B` to the receiver
    obtain rfl : e = .deliver receiver (.block B) t := Option.some.inj (he.symm.trans hdel)
    have ht : t = td := het
    subst ht
    rcases Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_deliver facts S rho hdel (W j) (hW j).1
        (W (j + 1)) (hW j).2 with hproc | ⟨hnone, -⟩
    · rw [facts.nd.process_st S (W j receiver) _ (W (j + 1) receiver) hproc,
        facts.nd.make_grades_compatible_with_finalized_bodies, facts.nd.process_block]
      have hpW : B.parent ∈ (W j receiver).st.bodies := hdeps j receiver (.block B) t hdel B rfl
      exact hinsert _ rfl rfl hpW hpW (hrecv hdel) (facts.nd.reachedStore_of_node _ _hr_0)
    · obtain ⟨n', hn'⟩ := facts.nd.process_nonempty S (W j receiver) (.block B) (fun B' hB' C hC hr => by
        have hBB : B = B' := NamedObject.block.inj hB'
        rw [← hBB] at hr ⊢
        exact roots.root_injective C B
          (Restated.Vocabulary.Proofs.NamedRuntime.blockInRun_of_direct facts S rho W hW
            (Restated.Vocabulary.Proofs.NamedRuntime.directBlock_of_prefix facts S rho W hW hreceiver j hC))
          hscope C B (Or.inl (Proofs.NamedAncestry.named_self C))
          (Or.inr (Proofs.NamedAncestry.named_self B)) hr)
      exact absurd hn' (hnone n')

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
set_option autoImplicit false
open Internal
open Execution

/-- For every path `W` of the run, a block of positive slot that `w`'s store in `W` holds right
    after an event before `GammaOut` was accepted by `w`, along `W`, at a time before `GammaOut`. -/
theorem Vocabulary.Proofs.HealingSurface.acceptsAt_before_of_processed_after_event (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {w : V} {B : NamedBlock V} (hBpos : 0 < B.slot) {n : Nat} {e : Record.Event V}
    {GammaOut : Time} (he : rho.events[n]? = some e) (het : e.time < GammaOut)
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    (hproc : Restated.Vocabulary.Execution.Object.processed M (W (n + 1) w).st (.block B) = true) :
    ∃ j : Nat, ∃ t' : Time, Restated.Vocabulary.Execution.NamedRun.acceptsAt M S rho W j w (.block B) t' ∧ t' < GammaOut := by
  rcases Restated.Vocabulary.Protocol.acceptsAt_block_of_processed facts S rho w W hW (n + 1) B hproc with
    hgen | ⟨j, hj, t', hacc'⟩
  · exact False.elim ((Nat.ne_of_gt hBpos) (by rw [hgen]; exact Sts.named_genesis_slot))
  · obtain ⟨-, e', he', -, ht'⟩ := hacc'.1
    have ht'le : t' ≤ e.time := by
      rw [← ht']
      rcases (Nat.le_of_lt_succ hj).lt_or_eq with hlt | rfl
      · obtain ⟨hjl, hjg⟩ := List.getElem?_eq_some_iff.mp he'
        obtain ⟨hnl, hng⟩ := List.getElem?_eq_some_iff.mp he
        have hk := (List.pairwise_iff_getElem.mp hsorted) j n hjl hnl hlt
        rw [hjg, hng] at hk
        exact Restated.time_le_of_key_le hk
      · rw [Option.some.inj (he'.symm.trans he)]
    exact ⟨j, t', hacc', lt_of_le_of_lt ht'le het⟩

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedBlockStamp
set_option autoImplicit false
open Execution

/-- In a run sorted by key and inside its horizon, if every event before index `n` is before
    `bound`, then in every world before index `n`, every body a validator's store holds has a block
    stamp before `bound`. -/
theorem Vocabulary.Proofs.NamedBlockStamp.timedBodies_prefix_of_fields (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    (hin : ∀ e ∈ rho.events, 0 ≤ e.time ∧ e.time ≤ rho.horizon)
    (bound : Time) (n : Nat)
    (hearly : ∀ k e, k < n → rho.events[k]? = some e → e.time < bound)
    (reader : V) : ∀ w₁ ∈ Record.stateBeforeOf M S rho n,
    ∀ B : NamedBlock V, B ∈ (w₁ reader).st.bodies →
      ∃ stamp : Stamp, stamp < (bound : Stamp) ∧
        (w₁ reader).st.core.timestamp_block B.erase = some stamp := by
  induction n with
  | zero =>
      intro w₁ hw₁ B hB
      have hgen : B = NamedBlock.genesis :=
        facts.ndRun.stateBefore_zero_body_eq_genesis S rho reader w₁ hw₁ hB
      subst B
      have hw : w₁ = fun v' => M.initial S v' := hw₁
      subst hw
      refine ⟨⊥, WithBot.bot_lt_coe bound, ?_⟩
      rw [Sts.erase_named_genesis]
      exact facts.nd.initial_timestamp_genesis S reader
  | succ n ih =>
      have hold := ih (fun k e hk he => hearly k e (Nat.lt_succ_of_lt hk) he)
      intro w₁ hw₁ B hB
      obtain ⟨w₀, hw₀, hstep⟩ := stateBeforeOf_succ_split S rho n w₁ hw₁
      by_cases hpre : B ∈ (w₀ reader).st.bodies
      · obtain ⟨stamp, hs, heq⟩ := hold w₀ hw₀ B hpre
        refine ⟨stamp, hs, ?_⟩
        exact (Restated.Vocabulary.Proofs.NamedBlockStamp.stateBefore_body_stamp_mono facts S rho reader
          (Nat.le_succ n) w₀ hw₀ hpre w₁ hstep).2.trans heq
      · cases he : rho.events[n]? with
        | none =>
            have hlen : rho.events.length ≤ n := List.getElem?_eq_none_iff.mp he
            rw [List.drop_eq_nil_of_le hlen, List.take_nil, List.foldlM_nil] at hstep
            have hsame : w₁ = w₀ := hstep
            rw [hsame] at hB
            exact absurd hB hpre
        | some e =>
            have htime : e.time < bound := hearly n e (Nat.lt_succ_self n) he
            by_cases hnode : reader = e.node
            · cases e with
              | wake v eventTime =>
                  rw [wake_step_st₂₆ facts S rho he w₀ w₁ hstep reader] at hB
                  exact absurd hB hpre
              | tick v eventTime =>
                  change reader = v at hnode
                  subst v
                  rcases Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_tick facts S rho he w₀ hw₀ w₁
                      hstep with ⟨out, hout, hw⟩ | ⟨-, hsame⟩
                  · rw [hw] at hB ⊢
                    refine ⟨(eventTime : Stamp), ?_, ?_⟩
                    · exact_mod_cast htime
                    · exact facts.nd.node_tick_body_stamp S reader (w₀ reader) eventTime out hout B
                        hpre hB
                  · rw [hsame] at hB
                    exact absurd hB hpre
              | deliver v o eventTime =>
                  change reader = v at hnode
                  subst v
                  rcases Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_deliver facts S rho he w₀ hw₀ w₁
                      hstep with hproc | ⟨-, hsame⟩
                  · have hclock : (w₀ reader).st.core.t ≤ eventTime :=
                      Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_clock_le_event facts S rho hsorted
                        he (hin _ (List.mem_of_getElem? he)).1 reader w₀ hw₀
                    refine ⟨(((w₀ reader).st.core.t : Int) : Stamp), ?_, ?_⟩
                    · exact_mod_cast hclock.trans_lt htime
                    · exact facts.nd.node_process_body_stamp S (w₀ reader) o (w₁ reader) hproc B hpre hB
                  · rw [hsame] at hB
                    exact absurd hB hpre
            · have hsame := Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_other facts S rho he reader
                hnode w₀ hw₀ w₁ hstep
              rw [hsame] at hB
              exact absurd hB hpre

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedBlockStamp
set_option autoImplicit false
open Execution

/-- In a run sorted by key and inside its horizon, in every world strictly before `t`, every body
    the reader's store holds has its block stamp strictly before `t`. -/
theorem Vocabulary.Proofs.NamedBlockStamp.held_body_stampedBefore_stateBeforeTime_of_fields (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    (hin : ∀ e ∈ rho.events, 0 ≤ e.time ∧ e.time ≤ rho.horizon)
    (reader : V) (t : Time) (B : NamedBlock V) :
    ∀ w₁ ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t,
    B ∈ (w₁ reader).st.bodies →
    stampedBefore
      (w₁ reader).st.core.timestamp_block
      t B.erase = true := by
  intro w₁ hw₁ hB
  obtain ⟨n, hread, hearly⟩ :=
    Restated.Vocabulary.Proofs.NamedRuntime.stateBeforeTime_eq_prefix facts S rho hsorted t
  rw [hread] at hw₁
  obtain ⟨stamp, hlt, hstamp⟩ :=
    Restated.Vocabulary.Proofs.NamedBlockStamp.timedBodies_prefix_of_fields facts S rho hsorted hin t n hearly
      reader w₁ hw₁ B hB
  exact Sts.stampedBefore_of_lt hstamp hlt

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If the execution delivers only blocks whose parent the receiver holds, then every delivery of a
    block `C` in the run of the first `n` steps, whatever honest set is declared, finds `C`'s parent
    among the receiver's bodies, along the path `x` follows. -/
theorem deps_runAll_withHonest (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V)
    (H : Finset V) (n : Nat)
    (hdel : Restated.DeliveryWellFormed M S x) :
    ∀ (i : Nat) (w : V) (o : NamedObject V) (t : Int),
      ({ Restated.runAll M S Sched x v n with honest := H } : Record.Run V).events[i]? =
        some (.deliver w o t) →
      ∀ C : NamedBlock V, o = .block C →
        C.parent ∈ (Restated.runAllPath M S Sched x v n i w).st.bodies := by
  intro i w o t hi C hC
  have hev : (Restated.runEvents M S Sched x n)[i]? = some (Record.Event.deliver w o t) := hi
  obtain ⟨k, -, hmemk, hcases⟩ := Restated.runAllPath_at_event facts S Sched x v n i hev
  obtain ⟨m, hlbl, hmsg, -⟩ := Restated.deliver_of_mem_actionEventsOf hmemk
  have hdeps := hdel.deps k w m hlbl C (hmsg.trans hC)
  rcases hcases with ⟨t', he', -, -⟩ | ⟨t', he', -, -⟩ | ⟨o', t', -, hb, -⟩
  · cases he'
  · cases he'
  · have hb' : Restated.runAllPath M S Sched x v n i w = x[k][w].st := hb
    rw [hb']
    exact hdeps

end

end DecoupledConsensusModel.Sts.Restated
