import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13beRoute3_45
import Proofs.Claims.Restated.Claim13beRoute3_46
import Proofs.Claims.Restated.Claim13beRoute3_47b
import Proofs.Claims.Restated.Claim13beRoute3_50
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Claims.Restated.Vocabulary_Protocol_ChainState_ProposalBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Duties_Proposals_Actions
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_TickBridges
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.RunVocabulary
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ProposalSourcesInternal
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedReceiptCalls
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Healing_Action
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Proofs.Vocabulary.Protocol.ForkChoice.Views.ProposalCore
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Internal_Definitions_TickReads
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreBridge
import Model.Conditions.Vocabulary_Statements_Instantiation_Proposals
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_25

/-!
# Proposals along a path

Theorems over a model `M : Record.Model V` and its facts about the slot-`s` proposer's read, its
proposal and the rows it selects, read along the path `W` of the bundle `AdmissibleFieldsOn`. The
proposer's read is the store of its node state in the world strictly before the proposal instant,
with its clock set to that instant and an outcome of its cache update.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Proofs.HealingSurface

omit [DecidableEq V] [Fintype V] in
/-- In a run sorted by key, every event before index `strictEventIndex rho t` is strictly before
    `t`. -/
private theorem time_lt_of_lt_strict₅₀b {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f)) (t : Time) :
    ∀ (j : Nat) (e : Record.Event V), j < strictEventIndex rho t → rho.events[j]? = some e →
      e.time < t := by
  intro j e hj he
  by_contra hnot
  have hle : t ≤ e.time := le_of_not_gt hnot
  have hlen : (rho.events.filter (fun e => decide (e.time < t))).length ≤ j := by
    have hpre : rho.events.filter (fun e => decide (e.time < t)) =
        rho.events.take (rho.events.filter (fun e => decide (e.time < t))).length := by
      refine List.prefix_iff_eq_take.mp ?_
      rw [DecoupledConsensusModel.Proofs.Bridges.filter_eq_takeWhile_of_pairwise
        (R := fun e f => Record.Event.key e ≤ Record.Event.key f) ?_ _ hsorted]
      · exact List.takeWhile_prefix _
      · intro e f hk hf
        simp only [decide_eq_true_eq] at hf ⊢
        exact lt_of_le_of_lt (Restated.time_le_of_key_le hk) hf
    by_contra hlt
    have hlt' : j < (rho.events.filter (fun e => decide (e.time < t))).length :=
      Nat.lt_of_not_ge hlt
    have hmem : e ∈ rho.events.filter (fun e => decide (e.time < t)) := by
      rw [hpre]
      exact List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hlt']; exact he)
    have hp := (List.mem_filter.mp hmem).2
    simp only [decide_eq_true_eq] at hp
    exact absurd hp (not_lt.mpr hle)
  exact absurd hj (not_lt.mpr hlen)

/-- The world `W (strictEventIndex rho t)` of the bundle's path is a world strictly before `t`. -/
private theorem mem_stateBeforeTime_strict₅₀b (facts : Record.Facts M) (S : Setup V)
    {rho : Record.Run V} {Hs : Int → Finset V} {Xb : Finset V} {lo : Int} {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo) (t : Time) :
    W (strictEventIndex rho t) ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t := by
  rw [Restated.stateBeforeTime_eq_stateBefore_strictEventIndexOn facts S Hs Xb hf t]
  exact (hf.onePath _).1

/-- For every outcome `c` of the cache update at slot `s`'s proposal instant on the proposer's node
    state along `W`, the node state built from its store with the clock set, its signing record and
    `c` is one of `proposerReadAt M S rho s`. -/
private theorem proposerRead_mem₅₀b (facts : Record.Facts M) (S : Setup V)
    {rho : Record.Run V} {Hs : Int → Finset V} {Xb : Finset V} {lo : Int} {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo) (s : Slot) (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core.toHealing
      (M.proposal_time S.E s)
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).cache ⇢ c) :
    M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
        (M.proposal_time S.E s))
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record c ∈
      Restated.Vocabulary.Statements.Instantiation.proposerReadAt M S rho s :=
  ⟨W (strictEventIndex rho (M.proposal_time S.E s)),
    mem_stateBeforeTime_strict₅₀b facts S hf _, c, hc, rfl⟩

/-- For every outcome `c` of the cache update at slot `s`'s proposal instant on the proposer's node
    state along `W`, every outcome of the proposal duty run with `c`'s grade contract is one of
    `proposedBlockAt M S rho s`. -/
private theorem proposedBlockAt_mem₅₀b (facts : Record.Facts M) (S : Setup V)
    {rho : Record.Run V} {Hs : Int → Finset V} {Xb : Finset V} {lo : Int} {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo) (s : Slot) (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core.toHealing
      (M.proposal_time S.E s)
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).cache ⇢ c)
    {o : Option (NamedBlock V)}
    (ho : M.proposal_with (M.gradeContract c)
      Protocol.ProposalRowSource.poolAndCarried S.E S.hc (S.node (S.E.proposer s))
      (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
        (M.proposal_time S.E s)) ⇢ o) :
    o ∈ Restated.Vocabulary.Statements.Instantiation.proposedBlockAt M S rho s :=
  ⟨_, proposerRead_mem₅₀b facts S hf s c hc,
    by rw [facts.nd.mkNode_cache, facts.nd.mkNode_st, facts.dt.proposal_with_store_with_cache]; exact ho⟩

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

/-- On the path `W` of the bundle, if `0 < s`, slot `s`'s proposer is in the set for `s`'s
    confirmation instant, `lo ≤ proposal_time s ≤ horizon`, and the proposer's tick at the proposal
    instant has an outcome and passes the grade-1 awake test, then every outcome of the proposal
    duty is `some B` for a block `B` of slot `s`, and the proposer emits `B` at the proposal
    instant. -/
theorem proposedBlockAt_emits_of_honestOn (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    (Hs : Int → Finset V) (Xb : Finset V) {lo : Int} {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    (s : Slot) (hs : 0 < s)
    (hprop : S.E.proposer s ∈ Hs (M.confirmation_time S.E s))
    (hhor : M.proposal_time S.E s ≤ rho.horizon)
    (hgat : lo ≤ M.proposal_time S.E s)
    (hneTick : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick (S.E.proposer s) (M.proposal_time S.E s)) →
      ∃ out : M.N × List (NamedObject V), M.tick S (S.E.proposer s) (W j (S.E.proposer s)) (M.proposal_time S.E s) ⇢ out)
    (hrun : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick (S.E.proposer s) (M.proposal_time S.E s)) →
      M.awake_for_grade1 S (S.E.proposer s) (W j (S.E.proposer s)) (M.round_of S.hc s)) :
    ∀ c : M.Cache, M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core.toHealing
        (M.proposal_time S.E s)
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).cache ⇢ c →
    ∀ o : Option (NamedBlock V), M.proposal_with (M.gradeContract c)
        Protocol.ProposalRowSource.poolAndCarried S.E S.hc (S.node (S.E.proposer s))
        (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
          (M.proposal_time S.E s)) ⇢ o →
    ∃ B : NamedBlock V, o = some B ∧ B.slot = s ∧
      Restated.Vocabulary.Execution.NamedRun.emits M S rho W (S.E.proposer s) (.block B)
        (M.proposal_time S.E s) := by
  intro c hc o ho
  obtain ⟨B, rfl⟩ := Restated.Vocabulary.Proofs.HealingSurface.proposedBlockAt_isSome facts S rho s o
    (proposedBlockAt_mem₅₀b facts S hf s c hc ho)
  obtain ⟨hslot, hemit⟩ :=
    Restated.proposalTickOn facts S Hs Xb hf hHs s hs hprop hhor hgat hneTick hrun c hc ho
  exact ⟨B, rfl, hslot, hemit⟩

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

/-- Under the hypotheses of `proposedBlockAt_emits_of_honestOn`, if the proposal duty with an
    outcome `c` of the cache update can return `some B` and admitting `B` into the proposer's read
    keeps it, then at some index `i` the proposer ticks at the proposal instant and holds `B` in
    `W (i + 1)`. -/
theorem proposedBlockAt_mem_bodies_after_tickOn (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    (Hs : Int → Finset V) (Xb : Finset V) {lo : Int} {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    (s : Slot) (hs : 0 < s)
    (hprop : S.E.proposer s ∈ Hs (M.confirmation_time S.E s))
    (hhor : M.proposal_time S.E s ≤ rho.horizon)
    (hgat : lo ≤ M.proposal_time S.E s)
    (hneTick : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick (S.E.proposer s) (M.proposal_time S.E s)) →
      ∃ out : M.N × List (NamedObject V), M.tick S (S.E.proposer s) (W j (S.E.proposer s)) (M.proposal_time S.E s) ⇢ out)
    (hrun : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick (S.E.proposer s) (M.proposal_time S.E s)) →
      M.awake_for_grade1 S (S.E.proposer s) (W j (S.E.proposer s)) (M.round_of S.hc s))
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core.toHealing
      (M.proposal_time S.E s)
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).cache ⇢ c)
    {B : NamedBlock V}
    (hB : M.proposal_with (M.gradeContract c)
      Protocol.ProposalRowSource.poolAndCarried S.E S.hc (S.node (S.E.proposer s))
      (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
        (M.proposal_time S.E s)) ⇢ some B)
    (hadmit : B ∈ (M.on_block_with .alsoCarried S.E S.hc S.cfg
      (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
        (M.proposal_time S.E s)) B).bodies) :
    ∃ i : Nat, rho.events[i]? =
        some (.tick (S.E.proposer s) (M.proposal_time S.E s)) ∧
      B ∈ (W (i + 1) (S.E.proposer s)).st.bodies := by
  have _hr_0 : M.reachedNode (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)) := facts.ndRun.stateBeforeOf_reachedNode S rho (strictEventIndex rho (M.proposal_time S.E s)) (W (strictEventIndex rho (M.proposal_time S.E s))) (hf.onePath (strictEventIndex rho (M.proposal_time S.E s))).1 (S.E.proposer s)
  have _hv_0 : M.runs_as (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)) (S.E.proposer s) := facts.ndRun.stateBeforeOf_runs_as S rho (strictEventIndex rho (M.proposal_time S.E s)) (W (strictEventIndex rho (M.proposal_time S.E s))) (hf.onePath (strictEventIndex rho (M.proposal_time S.E s))).1 (S.E.proposer s)
  obtain ⟨-, i, hi, out, hout, hW1, hsend⟩ :=
    Restated.proposalTickOn facts S Hs Xb hf hHs s hs hprop hhor hgat hneTick hrun c hc hB
  refine ⟨i, hi, ?_⟩
  have hst := Restated.stateBefore_tick_eq_stateBeforeTimeOn facts S Hs Xb hf hi
  have hnst : (W i (S.E.proposer s)).st =
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st := by
    rcases hst with hst | hst
    · rw [hst]
    · rw [hst, (facts.nd.wake_st_record _).1]
  have hncache : (W i (S.E.proposer s)).cache =
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).cache := by
    rcases hst with hst | hst
    · rw [hst]
    · rw [hst, facts.nd.wake_cache]
  obtain ⟨c', hc'⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc
    (W i (S.E.proposer s)).st.core.toHealing
    (M.proposal_time S.E s)
    (W i (S.E.proposer s)).cache
  have _hr_i := facts.ndRun.stateBeforeOf_reachedNode S rho i (W i) (hf.onePath i).1 (S.E.proposer s)
  have _hv_i := facts.ndRun.stateBeforeOf_runs_as S rho i (W i) (hf.onePath i).1 (S.E.proposer s)
  obtain ⟨D, hD⟩ := facts.dt.propose_block_with_nonempty S (S.E.proposer s) (W i (S.E.proposer s))
    (M.proposal_time S.E s) out hout
    (facts.nd.block_mem_on_tick_emit S _ _ _ out hout hsend).1.1
    (facts.nd.block_mem_on_tick_emit S _ _ _ out hout hsend).1.2.1
    (facts.nd.block_mem_on_tick_emit S _ _ _ out hout hsend).1.2.2
    (facts.nd.block_mem_on_tick_emit_awake S _ _ _ out hout hsend) c' hc'
  have hD2 : D.2 = some B :=
    (facts.nd.block_mem_on_tick_emit S _ _ _ out hout hsend).2 c' hc' D hD
  have _hr_s1 := facts.sto.reachedStore_setClock S.E _ (M.proposal_time S.E s) (facts.nd.reachedStore_of_node _ (facts.ndRun.stateBeforeOf_reachedNode S rho i (W i) (hf.onePath i).1 (S.E.proposer s)))
  have hDeq := facts.dt.propose_block_with_eq_of_snd _ _ _ _ _ _ D hD hD2
  have hdue : 0 < S.E.slotOf (M.proposal_time S.E s) ∧
      M.proposal_time S.E s = M.proposal_time S.E (S.E.slotOf (M.proposal_time S.E s)) ∧
      S.E.proposer (S.E.slotOf (M.proposal_time S.E s)) = (S.node (S.E.proposer s)).val_index := by
    rw [facts.sch.slotOf_proposal_time]
    exact ⟨hs, rfl, (S.node_val_index (S.E.proposer s)).symm⟩
  have hbod := ((facts.nd.tick_bodies_and_coreT_from_proposal S _ _ _ out hout).1
    ⟨hdue.1, hdue.2.1, hdue.2.2, facts.nd.block_mem_on_tick_emit_awake S _ _ _ out hout hsend⟩
    c' hc' D hD).1
  rw [hW1, hbod, hDeq, hnst]
  simp only [facts.nd.store_with_cache_bodies]
  exact hadmit

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

/-- Under the hypotheses of `proposedBlockAt_mem_bodies_after_tickOn`, the proposal `B` is a run
    block read through `Xb` along `W`. -/
theorem proposedBlockAt_blockInRunOn (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    (Hs : Int → Finset V) (Xb : Finset V) {lo : Int} {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (s : Slot) (hs : 0 < s)
    (hprop : S.E.proposer s ∈ Hs (M.confirmation_time S.E s))
    (hhor : M.proposal_time S.E s ≤ rho.horizon)
    (hgat : lo ≤ M.proposal_time S.E s)
    (hneTick : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick (S.E.proposer s) (M.proposal_time S.E s)) →
      ∃ out : M.N × List (NamedObject V), M.tick S (S.E.proposer s) (W j (S.E.proposer s)) (M.proposal_time S.E s) ⇢ out)
    (hrun : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick (S.E.proposer s) (M.proposal_time S.E s)) →
      M.awake_for_grade1 S (S.E.proposer s) (W j (S.E.proposer s)) (M.round_of S.hc s))
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core.toHealing
      (M.proposal_time S.E s)
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).cache ⇢ c)
    {B : NamedBlock V}
    (hB : M.proposal_with (M.gradeContract c)
      Protocol.ProposalRowSource.poolAndCarried S.E S.hc (S.node (S.E.proposer s))
      (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
        (M.proposal_time S.E s)) ⇢ some B)
    (hadmit : B ∈ (M.on_block_with .alsoCarried S.E S.hc S.cfg
      (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
        (M.proposal_time S.E s)) B).bodies) :
    Restated.blockInRunOn M S rho W Xb B := by
  obtain ⟨i, -, hmem⟩ :=
    Restated.proposedBlockAt_mem_bodies_after_tickOn facts S Hs Xb hf hHs s hs hprop hhor hgat
      hneTick hrun c hc hB hadmit
  exact Restated.runBlock_of_stateBefore_memOn facts S W Xb (hHsXb _ hprop) hmem

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

/-- On the path `W` of the bundle, if `a` is in an outcome of the rows the slot-`s` proposer selects
    at its read and `a`'s signer is in the set for the proposal instant, the signer emitted `a` at
    `a`'s action instant. -/
theorem honest_selected_row_emissionOn (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    (Hs : Int → Finset V) (Xb : Finset V) {lo : Int} {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    (s : Slot) {a : NamedAttestation V} (L : List (NamedAttestation V))
    (hL : M.select .poolAndCarried S.hc
      (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
        (M.proposal_time S.E s)) ⇢ L)
    (ha : a ∈ L)
    (hhon : a.val_index ∈ Hs (M.proposal_time S.E s)) :
    Restated.Vocabulary.Execution.Run.emits M S rho W a.val_index (.attest a)
      (Restated.Vocabulary.Execution.Setup.a M S a.round) := by
  have hT : ∀ (j : Nat) (e : Record.Event V), j < strictEventIndex rho (M.proposal_time S.E s) →
      rho.events[j]? = some e → e.time ≤ M.proposal_time S.E s :=
    fun j e hj he => (time_lt_of_lt_strict₅₀b hf.sorted _ j e hj he).le
  obtain ⟨C, hC⟩ := facts.dt.carriedRows_nonempty S.hc
    (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
      (M.proposal_time S.E s))
  rcases facts.dt.mem_select_poolAndCarried S.hc _ L hL ha C hC with hpool | hcarried
  · have hprocessed := facts.dt.mem_processedRows_of_mem_poolRows S.hc _ hpool
    obtain ⟨k, hak⟩ := facts.dt.exists_sg_rows_of_mem_processedRows S.hc _ hprocessed
    rw [facts.hd.setClock_sg_rows] at hak
    have har : a.round = k :=
      Restated.Vocabulary.Proofs.NamedStoreBridge.sgRowRounds_stateBeforeTime facts S rho
        (M.proposal_time S.E s) (S.E.proposer s) _ (mem_stateBeforeTime_strict₅₀b facts S hf _)
        k a hak
    have haN : a ∈ (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.sg_rows
        a.round := by
      rw [har]
      exact hak
    obtain ⟨_, _, _, _, _, hem⟩ :=
      Restated.heldArePastEmissions_of_admissibleCoreOn facts S Hs Xb hf hHs _ (S.E.proposer s)
        hT haN hhon
    exact hem
  · obtain ⟨O, hO⟩ := facts.dt.orderedBodies_nonempty
      (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
        (M.proposal_time S.E s))
    obtain ⟨B, hB, _, hrow, _⟩ := (facts.dt.mem_carried_rows S.hc _ a C hC O hO).mp hcarried
    have hbody := facts.dt.ordered_bodies_mem O hO hB
    rw [facts.hd.ModelProperties_setClock_bodies] at hbody
    obtain ⟨_, _, _, _, _, hem⟩ :=
      Restated.honest_held_ancestor_row_emissionOn facts S rho Hs Xb hf hHs _
        (S.E.proposer s) hT hbody (Proofs.NamedAncestry.named_self B) hrow hhon
    exact hem

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

/-- On the path `W` of the bundle, if `a` and `b` are in one outcome of the rows the slot-`s`
    proposer selects at its read, `a`'s signer is in the set for the proposal instant, and `b` has
    `a`'s signer and round, then `b = a`. -/
theorem honest_selected_row_uniqueOn (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    (Hs : Int → Finset V) (Xb : Finset V) {lo : Int} {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    (s : Slot)
    {a b : NamedAttestation V} (L : List (NamedAttestation V))
    (hL : M.select .poolAndCarried S.hc
      (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
        (M.proposal_time S.E s)) ⇢ L)
    (ha : a ∈ L) (hb : b ∈ L)
    (hhon : a.val_index ∈ Hs (M.proposal_time S.E s))
    (hval : b.val_index = a.val_index) (hround : b.round = a.round) :
    b = a := by
  have hbHon : b.val_index ∈ Hs (M.proposal_time S.E s) := by
    simpa only [hval] using hhon
  have hbe := Restated.honest_selected_row_emissionOn facts S Hs Xb hf hHs s L hL hb hbHon
  have hae := Restated.honest_selected_row_emissionOn facts S Hs Xb hf hHs s L hL ha hhon
  have hbe' : Restated.Vocabulary.Execution.NamedRun.emits M S rho W a.val_index (.attest b)
      (Restated.Vocabulary.Execution.Setup.a M S b.round) := by
    simpa only [hval] using hbe
  exact Restated.emitted_same_round_uniqueOn facts S rho Hs Xb hf hbe' hae hround

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

/-- On the path `W` of the bundle, if `0 < s` and the proposal duty at the slot-`s` proposer's read
    can return `some B`, then `B`'s erasure is not in that read's tree. -/
theorem proposedBlockErased_fresh_at_tickOn (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    (Hs : Int → Finset V) (Xb : Finset V) {lo : Int} {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (s : Slot) (hs : 0 < s)
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core.toHealing
      (M.proposal_time S.E s)
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).cache ⇢ c)
    {B : NamedBlock V}
    (hB : M.proposal_with (M.gradeContract c)
      Protocol.ProposalRowSource.poolAndCarried S.E S.hc (S.node (S.E.proposer s))
      (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
        (M.proposal_time S.E s)) ⇢ some B) :
    B.erase ∉ (M.ns_setClock S.E
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
      (M.proposal_time S.E s)).core.T := by
  intro hmem
  rw [facts.hd.Sts_setClock_core_T] at hmem
  have hlt := Restated.block_slot_lt_of_mem_beforeTime_of_le_proposalOn facts
    S Hs Xb hf hs (le_refl (M.proposal_time S.E s)) hmem
  rw [Proofs.NamedWire.erase_slot,
    Restated.Vocabulary.Proofs.HealingSurface.proposedBlockAt_slot facts S rho s _
      (proposedBlockAt_mem₅₀b facts S hf s c hc hB) rfl] at hlt
  exact Nat.lt_irrefl s hlt

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

/-- On the path `W` of the bundle, if `0 < s` and the proposal duty at the slot-`s` proposer's read
    can return `some B`, then admitting `B` into that read's store keeps `B` among its bodies. -/
theorem proposedBlockAt_admitOn (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    (Hs : Int → Finset V) (Xb : Finset V) {lo : Int} {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (s : Slot) (hs : 0 < s) {j : Nat}
    (hj : rho.events[j]? = some (Record.Event.tick (S.E.proposer s) (M.proposal_time S.E s)))
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core.toHealing
      (M.proposal_time S.E s)
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).cache ⇢ c)
    {B : NamedBlock V}
    (hB : M.proposal_with (M.gradeContract c)
      Protocol.ProposalRowSource.poolAndCarried S.E S.hc (S.node (S.E.proposer s))
      (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
        (M.proposal_time S.E s)) ⇢ some B) :
    B ∈ (M.on_block_with .alsoCarried S.E S.hc S.cfg
      (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
        (M.proposal_time S.E s)) B).bodies := by
  have _hr_0 : M.reachedNode (W j (S.E.proposer s)) := facts.ndRun.stateBeforeOf_reachedNode S rho j (W j) (hf.onePath j).1 (S.E.proposer s)
  have hn := proposerRead_mem₅₀b facts S hf s c hc
  have hst := facts.nd.mkNode_st
    (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
      (M.proposal_time S.E s))
    (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record c
  have hcache := facts.nd.mkNode_cache
    (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
      (M.proposal_time S.E s))
    (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record c
  have _hrW : M.reachedNode (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)) :=
    facts.ndRun.stateBeforeOf_reachedNode S rho _ (W _) (hf.onePath _).1 (S.E.proposer s)
  have _hrsC : M.reachedStore (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st (M.proposal_time S.E s)) :=
    facts.sto.reachedStore_setClock _ _ _ (facts.nd.reachedStore_of_node _ _hrW)
  have _hrs := facts.nd.reachedStore_of_node _
    (facts.nd.reachedNode_confirmationRead S.E S.hc _ _ c hc _hrW)
  generalize M.mkNode
    (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
      (M.proposal_time S.E s))
    (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record c = n at hn hst hcache _hrs
  have hcoreT : n.st.core.T = (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st (M.proposal_time S.E s)).core.T := by
    rw [hst, facts.nd.store_with_cache_core_T]
  have hcoreS : n.st.core.s = (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st (M.proposal_time S.E s)).core.s := by
    rw [hst, facts.nd.store_with_cache_core_s]
  have hcoreF : n.st.core.F = (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st (M.proposal_time S.E s)).core.F := by
    rw [hst, facts.nd.store_with_cache_core_F]
  have hB' : M.proposal_with (M.gradeContract n.cache)
      Protocol.ProposalRowSource.poolAndCarried S.E S.hc (S.node (S.E.proposer s)) n.st ⇢ some B := by
    rw [hst, hcache, facts.dt.proposal_with_store_with_cache]
    exact hB
  have hpB : some B ∈ Restated.Vocabulary.Statements.Instantiation.proposedBlockAt M S rho s :=
    ⟨n, hn, hB'⟩
  obtain ⟨input, hinput⟩ := facts.dt.with_proposal_input_nonempty (M.gradeContract n.cache) S.E S.hc
    (S.node (S.E.proposer s)) (M.toHealing n.st.core)
  obtain ⟨L, hL⟩ := facts.dt.select_nonempty .poolAndCarried S.hc n.st
  have hpay := Restated.Vocabulary.Proofs.NamedActions.proposal_payload facts _ .poolAndCarried
    S.E S.hc (S.node (S.E.proposer s)) _ B hB' input hinput L hL
  have hstore : B.erase.slot = n.st.core.s := by
    rw [Proofs.NamedWire.erase_slot, hpay.2.2.1]
    exact (facts.dt.with_proposal_input_id_slot _ _ _ _ _ input hinput).trans
      (facts.sto.toHealing_s _)
  have hsslot : B.erase.slot = s := by
    rw [Proofs.NamedWire.erase_slot]
    exact Restated.Vocabulary.Proofs.HealingSurface.proposedBlockAt_slot facts S rho s _ hpB rfl
  have hpar := Restated.Vocabulary.Proofs.HealingSurface.proposedBlockErased_parent facts S rho s n hn
    hB' input hinput
  have hfresh : B.erase ∉ n.st.core.T := by
    rw [hcoreT]
    exact Restated.proposedBlockErased_fresh_at_tickOn facts S Hs Xb hf s hs c hc hB
  have hparentTree : B.erase.parent ∈ n.st.core.T := by
    rw [hpar]
    exact Restated.Vocabulary.Proofs.HealingSurface.proposedParent_mem facts S rho s n hn input hinput
  have hparent : B.erase.parent.slot < B.erase.slot := by
    rw [hsslot]
    have h := hparentTree
    rw [hcoreT, facts.hd.Sts_setClock_core_T] at h
    exact Restated.block_slot_lt_of_mem_beforeTime_of_le_proposalOn facts S Hs Xb hf hs
      (le_refl (M.proposal_time S.E s)) h
  have hparentPreceq : Block.Preceq B.erase.parent B.erase := by
    by_cases hg : B.erase = Block.genesis
    · rw [hg, Proofs.ModelProperties.parent_genesis]
      exact Proofs.ModelProperties.Preceq_self _
    · exact Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mp
        (Protocol.preceq_of_parent? (parent?_eq_some_parent_of_ne_genesis hg))
  have hF : Block.Preceq n.st.core.F B.erase :=
    Proofs.ModelProperties.Preceq_trans
      (by
        rw [hpar]
        exact Restated.Vocabulary.Proofs.HealingSurface.finalized_preceq_proposedParent facts S rho s
          n hn input hinput)
      hparentPreceq
  have hproposer : B.erase.proposer? = some (S.E.proposer B.erase.slot) := by
    rw [Proofs.NamedWire.erase_proposer, hsslot]
    exact Restated.Vocabulary.Proofs.HealingSurface.proposedBlockAt_proposer facts S rho s _ hpB rfl
  have hparentBodies : B.parent ∈ (M.ns_setClock S.E
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
      (M.proposal_time S.E s)).bodies := by
    have h := hpay.1
    rw [hst, facts.nd.store_with_cache_bodies] at h
    exact h
  have hBroot : B.erase.root = (S.node (S.E.proposer s)).new_root s := by
    rw [Proofs.NamedWire.erase_root, hpay.2.2.2.1,
      facts.dt.with_proposal_input_id_root _ _ _ _ _ input hinput, ← hpay.2.2.1,
      ← Proofs.NamedWire.erase_slot, hsslot]
  have hroot : ∀ C ∈ (M.ns_setClock S.E
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
      (M.proposal_time S.E s)).core.T, C.root = B.erase.root → C = B.erase := by
    intro C hC hr
    exfalso
    rw [facts.hd.Sts_setClock_core_T] at hC
    have hcoh := (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho
      (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)
      (W (strictEventIndex rho (M.proposal_time S.E s)))
      (hf.onePath _).1).1.1.1
    rw [hcoh.1] at hC
    obtain ⟨D, hD, hDe⟩ := Finset.mem_image.mp hC
    have hDj : D ∈ (W j (S.E.proposer s)).st.bodies := by
      rcases Restated.stateBefore_tick_eq_stateBeforeTimeOn facts S Hs Xb hf hj with h | h
      · rw [h]; exact hD
      · rw [h, (facts.nd.wake_st_record _).1]; exact hD
    exact hf.rootCollisionFree.honest_roots_new s j hj D hDj
      (by rw [← Proofs.NamedWire.erase_root D, hDe, hr, hBroot])
  rw [hcoreT] at hparentTree hfresh
  rw [hcoreS] at hstore
  rw [hcoreF] at hF
  exact Restated.Vocabulary.Proofs.HealingSurface.mem_bodies_on_block_with facts S.E S.hc S.cfg _ B
    hparentBodies hfresh
    (Restated.Vocabulary.Proofs.HealingSurface.erased_handler_inserts facts S _ B hparentTree hfresh
      (le_of_eq hstore) hF hproposer hparent
      (Restated.Vocabulary.Proofs.HealingSurface.proposedBlockErased_carried_admissible facts S rho s
        _ hpB rfl) (facts.sto.rootFresh_of_distinct _ _ hroot))

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

/-- Under the hypotheses of `proposedBlockAt_emits_of_honestOn`, if the proposal duty at the
    slot-`s` proposer's read, with an outcome `c` of the cache update, can return `some B`, then `B`
    is a run block read through `Xb` along `W`. -/
theorem proposedBlockAt_blockInRun_of_admissibleOn (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    (Hs : Int → Finset V) (Xb : Finset V) {lo : Int} {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (s : Slot) (hs : 0 < s)
    (hprop : S.E.proposer s ∈ Hs (M.confirmation_time S.E s))
    (hhor : M.proposal_time S.E s ≤ rho.horizon)
    (hgat : lo ≤ M.proposal_time S.E s)
    (hneTick : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick (S.E.proposer s) (M.proposal_time S.E s)) →
      ∃ out : M.N × List (NamedObject V), M.tick S (S.E.proposer s) (W j (S.E.proposer s)) (M.proposal_time S.E s) ⇢ out)
    (hrun : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick (S.E.proposer s) (M.proposal_time S.E s)) →
      M.awake_for_grade1 S (S.E.proposer s) (W j (S.E.proposer s)) (M.round_of S.hc s))
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core.toHealing
      (M.proposal_time S.E s)
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).cache ⇢ c)
    {B : NamedBlock V}
    (hB : M.proposal_with (M.gradeContract c)
      Protocol.ProposalRowSource.poolAndCarried S.E S.hc (S.node (S.E.proposer s))
      (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
        (M.proposal_time S.E s)) ⇢ some B) :
    Restated.blockInRunOn M S rho W Xb B := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp (hf.tick_total _ hgat _
    (hHs _ _ (facts.sch.proposal_time_le_confirmation_time S.E s) hprop)
    (Restated.Vocabulary.Proofs.Optimistic.publicTime_proposal_time facts S s) hhor)
  exact Restated.proposedBlockAt_blockInRunOn facts S Hs Xb hf hHs hHsXb s hs hprop hhor hgat hneTick
    hrun c hc hB (Restated.proposedBlockAt_admitOn facts S Hs Xb hf s hs hj c hc hB)

end

/-! ## Action bodies and confirmation witnesses -/

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- On the path `W` of the bundle, if `v ∈ Xb`, `n` is a node state of `v`'s round-`r` action read,
    and `D` is a body of `n`'s store, then `D` is a run block read through `Xb`. -/
theorem actionBody_runBlock_coreOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} (hv : v ∈ Xb) {r : Round} {n : M.N}
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r)
    {D : NamedBlock V} (hD : D ∈ n.st.bodies) :
    Restated.RunBlockOn M S rho W Xb D :=
  Restated.actionBody_runBlockOn facts S Hs Xb hf hv hn hD

/-- On the path `W` of the bundle, if `v ∈ Xb`, `n` is a node state of `v`'s round-`r` action read,
    and `D` is a body of `n`'s store, then some body `K` of `n`'s store erases to `D`'s entry, has
    `D`'s named height, is an ancestor of `D`, and is a run block read through `Xb`. -/
theorem action_named_checkpoint_coreOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} (hv : v ∈ Xb) {r : Round} {n : M.N}
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r)
    {D : NamedBlock V} (hD : D ∈ n.st.bodies) :
    ∃ K : NamedBlock V,
      K ∈ n.st.bodies ∧
      K.erase = (M.derive_named S.E S.cfg D).T_h ∧
      (M.derive_named S.E S.cfg K).h = (M.derive_named S.E S.cfg D).h ∧
      NamedBlock.Preceq K D ∧
      Restated.RunBlockOn M S rho W Xb K :=
  Restated.action_named_checkpointOn facts S Hs Xb hf hv hn hD

/-- On the path `W` of the bundle, if `a`'s signer, a member of `Xb`, emits `a` at `ta` with a
    height pair naming `h`, then for every node state `nr` of the signer's round action read and
    every outcome `o` of `nr`'s action FG source, there are bodies `D` and `K` of `nr` with
    `o = some D.erase`, both of named height `h`, `K` erasing to `D`'s entry and `K ⪯ D`, the FG
    confirmation witness of `nr` can return `K`'s entry, and `a`'s height pair targets `K`'s root at
    `h` or is the timeout at `h`. -/
theorem honestHeightRow_confirmationWitness_coreOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {a : NamedAttestation V} {ta : Time} {h : Height}
    (haHon : a.val_index ∈ Xb)
    (hemit : Restated.Vocabulary.Execution.NamedRun.emits M S rho W a.val_index (Object.attest a) ta)
    (hh : a.height_pair.erase.height? = some h) :
    ∀ nr ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round)) a.val_index)
      a.round,
    ∀ o, Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S nr ⇢ o →
    ∃ D K : NamedBlock V,
      Restated.Vocabulary.Proofs.HealingSurface.fgConfirmationWitness M S nr ⇢
        some (M.derive_named S.E S.cfg K).T_h ∧
      D ∈ nr.st.bodies ∧
      o = some D.erase ∧
      (M.derive_named S.E S.cfg D).h = h ∧
      K ∈ nr.st.bodies ∧
      K.erase = (M.derive_named S.E S.cfg D).T_h ∧
      (M.derive_named S.E S.cfg K).h = h ∧
      Block.Preceq K.erase D.erase ∧
      (a.height_pair.erase = HeightPair.target h K.erase.root ∨
        a.height_pair.erase = HeightPair.timeout h) :=
  Restated.honestHeightRow_confirmationWitnessOn facts S Hs Xb hf haHon hemit hh

end

/-! ## The FG root's witnesses -/

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- In a parent-closed named store, every named ancestor of a held body is held. -/
private theorem namedAncestor_mem₅₀c {st : M.NS}
    (hpc : Restated.Vocabulary.Proofs.NamedStore.NamedParentClosed M st) {A B : NamedBlock V}
    (hB : B ∈ st.bodies) (hAB : NamedBlock.Preceq A B) : A ∈ st.bodies := by
  revert hB hAB
  induction B with
  | genesis =>
      intro hB hAB
      simp only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] at hAB
      exact hAB ▸ hB
  | node p s r gv gsv ats proposer ih =>
      intro hB hAB
      simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hAB
      rcases hAB with rfl | hparent
      · exact hB
      · exact ih (by simpa only [NamedBlock.parent] using hpc.2 _ hB)
          (by unfold NamedBlock.Preceq; exact hparent)

/-- Every node state the round-`r` action read from `before` can give holds `before`'s bodies. -/
private theorem actionReadFrom_bodies₅₀c (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      n.st.bodies = before.st.bodies := by
  rintro _ ⟨c, -, st, hst, rfl⟩
  rw [facts.nd.mkNode_st, facts.nd.store_with_cache_bodies,
    facts.dt.named_update_confirmation_with_bodies _ _ _ _ _ st hst,
    facts.hd.ModelProperties_setClock_bodies]

/-- In a parent-closed named store, for every held body `C`, some held body has `C`'s finalized
    block as its justified block. -/
private theorem finalized_justificationSource₅₀c (facts : Record.Facts M) (E : Env V)
    (cfg : HeightConfig) {st : M.NS}
    (hpc : Restated.Vocabulary.Proofs.NamedStore.NamedParentClosed M st) :
    ∀ C : NamedBlock V, C ∈ st.bodies →
      ∃ D ∈ st.bodies, (M.derive_named E cfg D).J = (M.derive_named E cfg C).F := by
  intro C
  induction C with
  | genesis =>
      intro hC
      refine ⟨.genesis, hC, ?_⟩
      rw [facts.csAdded.derive_named_genesis_F]
      exact facts.cs.justified_zero_is_genesis E cfg _
        (facts.csAdded.ModelProperties_derive_named_genesis_h_j E cfg)
  | node p s r gv gsv ats proposer ih =>
      intro hC
      have hp : p ∈ st.bodies := by simpa only [NamedBlock.parent] using hpc.2 _ hC
      rcases facts.csAdded.derive_named_F_cases E cfg
          (B := NamedBlock.node p s r gv gsv ats proposer) (by intro h; cases h) with h | h
      all_goals simp only [NamedBlock.parent] at h
      · obtain ⟨D, hD, hDJ⟩ := ih hp
        exact ⟨D, hD, hDJ.trans h.symm⟩
      · exact ⟨p, hp, h.symm⟩

/-- On the path `W` of the bundle, some body of `v`'s store in the world strictly before `time` has
    that store's FG root as its justified block. -/
theorem fgRoot_justificationSource_at_readOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo) (v : V)
    (time : Time) :
    ∃ D ∈ (W (strictEventIndex rho time) v).st.bodies,
      (M.derive_named S.E S.cfg D).J =
        M.get_fg_root (M.toHealing (W (strictEventIndex rho time) v).st.core).toFG := by
  have hmem := (hf.onePath (strictEventIndex rho time)).1
  have hpc : Restated.Vocabulary.Proofs.NamedStore.NamedParentClosed M
      (W (strictEventIndex rho time) v).st :=
    (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho _ v _
      hmem).1.1.1.2.2.1
  obtain ⟨J, hJ, hJstate, -⟩ :=
    facts.csRun.justification_carrier_stateBefore S rho _ v _ hmem
  obtain ⟨F, hF, hFstate, -⟩ :=
    facts.csRun.storeFinalizationOnChain_stateBefore S rho _ v _ hmem
  by_cases hgate : (W (strictEventIndex rho time) v).st.core.h_max =
      (W (strictEventIndex rho time) v).st.core.h_j + 1
  · rw [facts.fc.get_fg_root_toHealing_of_eq _ hgate]
    exact ⟨J, hJ, hJstate⟩
  · rw [facts.fc.get_fg_root_toHealing_of_ne _ hgate]
    obtain ⟨D, hD, hDJ⟩ := finalized_justificationSource₅₀c facts S.E S.cfg hpc F hF
    exact ⟨D, hD, hDJ.trans hFstate⟩

/-- On the path `W` of the bundle, if `v ∈ Xb`, `time ≤ horizon` and `C` is a body of `v`'s store in
    the world strictly before `time`, then `C`'s justified block is genesis, or some signer in the
    set for `time` emitted before `time` an attestation targeting it, and for every node state of
    that signer's round action read and every outcome of its action FG source, its FG confirmation
    witness can return `C`'s justified block. -/
theorem processedJustification_confirmationWitnessOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hmajority : HonestWeightMajorityOn S rho Hs)
    {v : V} (hv : v ∈ Xb) {time : Time} (hthor : time ≤ rho.horizon) {C : NamedBlock V}
    (hC : C ∈ (W (strictEventIndex rho time) v).st.bodies) :
    (M.derive_named S.E S.cfg C).J = Block.genesis ∨
      ∃ (a : NamedAttestation V) (ta : Time),
        a.val_index ∈ Hs time ∧
        Restated.Vocabulary.Execution.NamedRun.emits M S rho W a.val_index (Object.attest a) ta ∧
        ta < time ∧
        a.height_pair.erase = HeightPair.target
          (M.derive_named S.E S.cfg C).h_j
          (M.derive_named S.E S.cfg C).J.root ∧
        ∀ nr ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round)) a.val_index)
          a.round,
        ∀ o, Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S nr ⇢ o →
          Restated.Vocabulary.Proofs.HealingSurface.fgConfirmationWitness M S nr ⇢
            some (M.derive_named S.E S.cfg C).J := by
  by_cases hz : (M.derive_named S.E S.cfg C).h_j = 0
  · exact Or.inl (facts.cs.justified_zero_is_genesis S.E S.cfg C hz)
  obtain ⟨Jcert, hJcert, hJcertErase, Q, hQ, hwit⟩ :=
    Restated.Vocabulary.Proofs.NamedJustificationCertificates.justification_certificate facts
      S.E S.cfg C hz
  have hJcertRoot : Jcert.root = (M.derive_named S.E S.cfg C).J.root := by
    simpa only [Proofs.NamedWire.erase_root] using congrArg Block.root hJcertErase
  obtain ⟨i, hiQ, hiHon⟩ :=
    Protocol.HonestWeightMajority.exists_honest_member_of_quorum (hmajority time hthor) hQ
  obtain ⟨carrier, a, hcarrier, ha, hai, hap⟩ := hwit i hiQ
  have haHon : a.val_index ∈ Hs time := by
    rw [hai]
    exact hiHon
  have hpc : Restated.Vocabulary.Proofs.NamedStore.NamedParentClosed M
      (W (strictEventIndex rho time) v).st :=
    (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho _ v _
      (hf.onePath _).1).1.1.1.2.2.1
  have hcarrierBody : carrier ∈ (W (strictEventIndex rho time) v).st.bodies :=
    namedAncestor_mem₅₀c hpc hC hcarrier
  have hJcertBody : Jcert ∈ (W (strictEventIndex rho time) v).st.bodies :=
    namedAncestor_mem₅₀c hpc hC hJcert
  rcases Restated.Vocabulary.Proofs.Bridges.processes_block_of_mem_T facts S rho v W hf.onePath _
      carrier hcarrierBody with hgen | ⟨j, e, hj, hje, hproc⟩
  · rw [hgen, named_genesis_attestations] at ha
    simp at ha
  · have hetime : e.time < time := time_lt_of_lt_strict₅₀b hf.sorted time j e hj hje
    obtain ⟨hround, hemit⟩ := Restated.carriedArePastEmissions_of_processesOn facts
      S rho Hs Xb hf hproc ha (hHs _ _ hetime.le haHon)
    have hta : (Restated.Vocabulary.Execution.Setup.a M S a.round) < time :=
      lt_of_le_of_lt hround hetime
    have hheight : a.height_pair.erase.height? =
        some (M.derive_named S.E S.cfg C).h_j := by
      rw [hap, namedHeightPair_erase_vote_height?]
    have haXb : a.val_index ∈ Xb := hHsXb _ haHon
    have hpair : a.height_pair.erase = HeightPair.target
        (M.derive_named S.E S.cfg C).h_j
        (M.derive_named S.E S.cfg C).J.root := by
      rw [hap, namedHeightPair_erase_vote_false, hJcertRoot]
    refine Or.inr ⟨a, (Restated.Vocabulary.Execution.Setup.a M S a.round), haHon, hemit, hta,
      hpair, ?_⟩
    intro nr hnr o ho
    obtain ⟨D, K, hfg, hD, hsource, hDheight, hK, hKentry, hKheight, hKpre, hrow⟩ :=
      Restated.honestHeightRow_confirmationWitness_coreOn facts S Hs Xb hf haXb hemit hheight
        nr hnr o ho
    have hbodies := actionReadFrom_bodies₅₀c facts S _ _ nr hnr
    have hDpre := hD
    have hKpreTime := hK
    rw [hbodies] at hDpre hKpreTime
    have hcohAction := (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho
      _ a.val_index _ (hf.onePath (strictEventIndex rho
        (Restated.Vocabulary.Execution.Setup.a M S a.round))).1).1.1.1
    obtain ⟨K', hK'D, hK'erase⟩ := Proofs.NamedAncestry.erased_ancestor_lift D hKpre
    have hK'body := namedAncestor_mem₅₀c hcohAction.2.2.1 hDpre hK'D
    have hK'eq : K' = K := hcohAction.2.1 K' hK'body K hKpreTime hK'erase
    have hKpreNamed : NamedBlock.Preceq K D := by
      rw [← hK'eq]
      exact hK'D
    have hKtarget : (M.derive_named S.E S.cfg K).T_h = K.erase := by
      have hKDheight : (M.derive_named S.E S.cfg K).h = (M.derive_named S.E S.cfg D).h :=
        hKheight.trans hDheight.symm
      exact (facts.cs.entry_eq_on_plateau S.E S.cfg hKpreNamed hKDheight).trans hKentry.symm
    have hroot : K.erase.root = (M.derive_named S.E S.cfg C).J.root := by
      rcases hrow with htarget | htimeout
      · have hEq := htarget.symm.trans hpair
        have hEq' : True ∧ K.erase.root = (M.derive_named S.E S.cfg C).J.root := by
          simpa only [HeightPair.target.injEq] using hEq
        exact hEq'.2
      · rw [hap, namedHeightPair_erase_vote_false] at htimeout
        simp at htimeout
    have hKrun : Restated.RunBlockOn M S rho W Xb K :=
      Restated.actionBody_runBlock_coreOn facts S Hs Xb hf haXb hnr hK
    have hJrun : Restated.RunBlockOn M S rho W Xb Jcert :=
      Restated.runBlock_of_stateBefore_memOn facts S W Xb hv hJcertBody
    have hroots : K.root = Jcert.root := by
      calc
        K.root = K.erase.root := (Proofs.NamedWire.erase_root K).symm
        _ = (M.derive_named S.E S.cfg C).J.root := hroot
        _ = Jcert.root := hJcertRoot.symm
    have hEq : K = Jcert :=
      hf.rootCollisionFree.root_injective K Jcert
        hKrun hJrun K Jcert (Or.inl (Proofs.NamedAncestry.named_self K))
        (Or.inr (Proofs.NamedAncestry.named_self Jcert)) hroots
    have hW : (M.derive_named S.E S.cfg K).T_h = (M.derive_named S.E S.cfg C).J :=
      hKtarget.trans (hEq ▸ hJcertErase)
    exact hW ▸ hfg

/-- On the path `W` of the bundle, if `v ∈ Xb` and `time ≤ horizon`, the FG root `R` of `v`'s store
    in the world strictly before `time` is genesis, or it is the justified block of a body of that
    store, some signer in the set for `time` emitted before `time` an attestation targeting it, and
    the FG confirmation witness of every node state of that signer's round action read can return
    `R`. -/
theorem fgRoot_confirmationWitness_at_readOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hmajority : HonestWeightMajorityOn S rho Hs)
    {v : V} (hv : v ∈ Xb) (time : Time) (hthor : time ≤ rho.horizon) :
    let R := M.get_fg_root (M.toHealing (W (strictEventIndex rho time) v).st.core).toFG
    R = Block.genesis ∨ ∃ (C : NamedBlock V),
      C ∈ (W (strictEventIndex rho time) v).st.bodies ∧
      (M.derive_named S.E S.cfg C).J = R ∧
      ∃ (a : NamedAttestation V) (ta : Time),
      a.val_index ∈ Hs time ∧
      Restated.Vocabulary.Execution.NamedRun.emits M S rho W a.val_index (Object.attest a) ta ∧
      ta < time ∧
      a.height_pair.erase = HeightPair.target
        (M.derive_named S.E S.cfg C).h_j
        (M.derive_named S.E S.cfg C).J.root ∧
      ∀ nr ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round)) a.val_index)
        a.round,
      ∀ o, Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S nr ⇢ o →
        Restated.Vocabulary.Proofs.HealingSurface.fgConfirmationWitness M S nr ⇢ some R := by
  intro R
  obtain ⟨C, hC, hJ⟩ := Restated.fgRoot_justificationSource_at_readOn facts S Hs Xb hf v time
  rcases Restated.processedJustification_confirmationWitnessOn facts S Hs Xb hf hHs hHsXb
      hmajority hv hthor hC with
      hgen | ⟨a, ta, haHon, hemit, hta, hpair, hwitness⟩
  · exact Or.inl (hJ.symm.trans hgen)
  · exact Or.inr ⟨C, hC, hJ, a, ta, haHon, hemit, hta, hpair,
      fun nr hnr o ho => by
        have hw := hwitness nr hnr o ho
        rw [hJ] at hw
        exact hw⟩

/-- On the path `W` of the bundle, if every confirmation witness of an action at a round `r ≥ cut`
    before `time`, by a validator in the set for that action's instant, is compatible with `B`, and
    every earlier target explaining the FG root of `v`'s store strictly before `time`, emitted
    before round `cut`, makes that root compatible with `B`, then the root is compatible with `B`. -/
theorem fgRoot_compatible_of_bootstrap_and_recentActions_at_readOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hmajority : HonestWeightMajorityOn S rho Hs)
    {v : V} (hv : v ∈ Xb) {time : Time} (hthor : time ≤ rho.horizon) {cut : Round}
    {B : Block V}
    (hrecent : ∀ r, cut ≤ r → (Restated.Vocabulary.Execution.Setup.a M S r) < time →
      ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)), ∀ T,
      (∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) w) r,
        ∀ o, Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n ⇢ o →
          Restated.Vocabulary.Proofs.HealingSurface.fgConfirmationWitness M S n ⇢ some T) →
        Block.compatible B T = true)
    (hbootstrap : ∀ (C : NamedBlock V) (a : NamedAttestation V) (ta : Time),
      let R := M.get_fg_root (M.toHealing (W (strictEventIndex rho time) v).st.core).toFG
      C ∈ (W (strictEventIndex rho time) v).st.bodies →
      (M.derive_named S.E S.cfg C).J = R →
      a.val_index ∈ Hs ta →
      Restated.Vocabulary.Execution.NamedRun.emits M S rho W a.val_index (Object.attest a) ta →
      ta < time → a.round < cut →
      a.height_pair.erase = HeightPair.target
        (M.derive_named S.E S.cfg C).h_j
        (M.derive_named S.E S.cfg C).J.root →
      (∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round)) a.val_index)
          a.round,
        ∀ o, Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n ⇢ o →
          Restated.Vocabulary.Proofs.HealingSurface.fgConfirmationWitness M S n ⇢ some R) →
        Block.compatible B R = true) :
    Block.compatible
      (M.get_fg_root (M.toHealing (W (strictEventIndex rho time) v).st.core).toFG) B = true := by
  rcases Restated.fgRoot_confirmationWitness_at_readOn facts S Hs Xb hf hHs hHsXb hmajority hv
      time hthor with
      hgen | ⟨C, hC, hJ, a, ta, ha, hemit, ht, hpair, hT⟩
  · rw [hgen]
    exact compatible_of_cases (Or.inl (preceq_eq_true_iff_Preceq.mp (Protocol.preceq_genesis _)))
  · suffices h : Block.compatible B
        (M.get_fg_root (M.toHealing (W (strictEventIndex rho time) v).st.core).toFG) = true by
      exact compatible_of_cases (compatible_cases h).symm
    by_cases hboot : a.round < cut
    · exact hbootstrap C a ta hC hJ (hHs _ _ ht.le ha) hemit ht hboot hpair hT
    · have htime :=
        (Restated.Vocabulary.Proofs.Optimistic.emits_attest_shape facts S W hf.onePath hemit).2
      have hltime : (Restated.Vocabulary.Execution.Setup.a M S a.round) < time := by
        simpa only [htime] using ht
      exact hrecent a.round (Nat.le_of_not_gt hboot) hltime
        a.val_index (hHs _ _ hltime.le ha) _ hT

end

end DecoupledConsensusModel.Sts.Restated
