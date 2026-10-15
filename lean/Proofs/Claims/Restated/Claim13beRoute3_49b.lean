import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13beRoute3_45
import Proofs.Claims.Restated.Claim13beRoute3_46
import Proofs.Claims.Restated.Claim13beRoute3_48
import Proofs.Claims.Restated.Claim13beRoute3_49
import Proofs.Claims.Restated.Vocabulary_Execution_EmissionShape
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Claims.Restated.Vocabulary_Generic_EvaluationStore
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_ValidatorClient_Schedule
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.RunVocabulary
import Model.Conditions.Vocabulary_Internal_Definitions_TickReads
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedReceiptCalls
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_Store
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Proofs.Vocabulary.Protocol.ForkChoice.Views.ProposalCore
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Protocol_Grades_Main
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_Handlers_TickBridges
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring

/-!
# SG pools, confirmation stores and height maxima along a path of the run

Theorems about attestations in the SG pool, the confirmation store, the proposer's processed
attestations and the largest `h_max` over a set at an event prefix, stated over a model
`M : Record.Model V` along the path `W` of the bundle `AdmissibleFieldsOn`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

open scoped DC

/-! ## Helpers about event indices, paths and tick stores -/

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Proofs.HealingSurface

omit [DecidableEq V] [Fintype V] in
/-- In a run sorted by key, an event at index `j` with a time before `t` is among the first
    `strictEventIndex rho t` events. -/
private theorem lt_strict_of_time_lt₄₉b {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {j : Nat} {e : Record.Event V} (he : rho.events[j]? = some e) {t : Time} (ht : e.time < t) :
    j < strictEventIndex rho t := by
  by_contra hnot
  exact absurd ht (not_lt.mpr
    (Restated.le_time_of_index_ge_of_sorted hsorted
      (Nat.le_of_not_gt hnot) he))

/-- For every path `W` of `rho`, `W (m + k)` is among the worlds the events `m` to `m + k - 1` lead
    to from `W m`. -/
private theorem onePath_reach₄₉b {S : Setup V} {rho : Record.Run V}
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

/-- For every path `W` of `rho` and `m ≤ n`, `W n` is among the worlds the events `m` to `n - 1`
    lead to from `W m`. -/
private theorem onePath_slice₄₉b {S : Setup V} {rho : Record.Run V}
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) {m n : Nat}
    (hmn : m ≤ n) :
    W n ∈ ((rho.events.drop m).take (n - m)).foldlM (Record.worldStepOf M S) (W m) := by
  have h := onePath_reach₄₉b W hW m (n - m)
  rwa [Nat.add_sub_of_le hmn] at h

/-- In a run sorted by key, the worlds strictly before the instant `t` are the worlds before the
    event of index `strictEventIndex rho t`. -/
private theorem stateBeforeTime_eq_strict₄₉b (S : Setup V) (rho : Record.Run V)
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

/-- In a run sorted by key, along every path `W` of `rho`, the world `W (strictEventIndex rho t)` is
    a world strictly before the instant `t`. -/
private theorem mem_stateBeforeTime_path₄₉b (S : Setup V) (rho : Record.Run V)
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (t : Time) :
    W (strictEventIndex rho t) ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t := by
  rw [stateBeforeTime_eq_strict₄₉b S rho hsorted t]
  exact (hW _).1

/-- The store a tick at `t` hands its first duty, staged from `n`'s core store, has the tree of
    `n`'s core store. -/
private theorem tickStore_T₄₉b (facts : Record.Facts M) (S : Setup V) (n : M.N) (t : Time) :
    (Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core t).T = n.st.core.T := by
  rw [Restated.Vocabulary.Proofs.Optimistic.tickStore,
    ← facts.hd.setClock_core_eq_store_with_t_s S.E n.st t, facts.hd.Sts_setClock_core_T]

/-- The store a tick at `t` hands its first duty, staged from `n`'s core store, has the SG votes of
    `n`'s core store. -/
private theorem tickStore_sg_votes₄₉b (facts : Record.Facts M) (S : Setup V) (n : M.N)
    (t : Time) :
    (Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core t).sg_votes = n.st.core.sg_votes := by
  rw [Restated.Vocabulary.Proofs.Optimistic.tickStore,
    ← facts.hd.setClock_core_eq_store_with_t_s S.E n.st t, facts.hd.setClock_core_sg_votes]

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

/-- Along the path `W` of the bundle, if event `j` is `e`, `e` happens before `t`, and `w`'s SG pool
    of `k` in `W (j + 1)` holds `a`, then `w`'s SG pool of `k` in `W (strictEventIndex rho t)` holds
    `a`. -/
theorem attest_mem_stateBeforeTime_of_postOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {w : V} {j : Nat} {e : Record.Event V} {t : Time} {k : Round}
    {a : CombinedAttestation V}
    (hj : rho.events[j]? = some e) (hjt : e.time < t)
    (ha : a ∈ (W (j + 1) w).st.sg_pool k) :
    a ∈ (W (strictEventIndex rho t) w).st.sg_pool k := by
  have hjN : j < strictEventIndex rho t := lt_strict_of_time_lt₄₉b hf.sorted hj hjt
  exact Restated.Vocabulary.Proofs.HealingLemmas.stateBefore_sg_pool_subset facts S rho w k
    (i := j + 1) (W (j + 1)) (hf.onePath (j + 1)).1 _ (Nat.succ_le_of_lt hjN) _
    (onePath_slice₄₉b W hf.onePath (Nat.succ_le_of_lt hjN)) ha

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

/-- If `v ∈ Xb` and `B`'s erasure is in the confirmation tree of `v`'s confirmation store of `s`,
    staged from the world of `W` strictly before `confirmation_time s`, then looking up `B`'s root
    in that store's tree finds `B`'s erasure. -/
theorem confFind_of_candidateOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {s : Slot} {v : V} (hv : v ∈ Xb) {B : NamedBlock V}
    (hB : B.erase ∈ Restated.Vocabulary.Protocol.confTree M
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core
        (M.confirmation_time S.E s))) :
    Block.find? (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core
        (M.confirmation_time S.E s)).T B.erase.root = some B.erase := by
  set t := M.confirmation_time S.E s with ht
  set n := strictEventIndex rho t with hn
  have hmem := mem_stateBeforeTime_path₄₉b S rho hf.sorted W hf.onePath t
  rw [tickStore_T₄₉b facts]
  have hBT : B.erase ∈ (W n v).st.core.T := by
    have h := facts.fc.get_filtered_block_tree_subset
      (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M S (W n v).st.core t)).toFG hB
    rw [facts.sto.toHealing_gs_T, tickStore_T₄₉b facts] at h
    exact h
  have hcoh : Restated.Vocabulary.Proofs.NamedStore.Coherent M S.E S.cfg (W n v).st :=
    (Restated.Vocabulary.Proofs.NamedRuntime.stateBeforeTime_invariants facts S rho t v (W n)
      hmem).1.1.1
  have hrun : ∀ C ∈ (W n v).st.bodies, Restated.RunBlockOn M S rho W Xb C :=
    fun C hC => Restated.runBlock_of_stateBefore_memOn facts S W Xb hv (i := n) hC
  have hinj := Restated.rootInjectiveBelow_of_runBlocksOn facts S W Xb hf.rootCollisionFree hrun
  rw [← hcoh.1] at hinj
  exact Proofs.Optimistic.find?_eq_some_of_unique hBT (fun X hX hroot =>
    RootInjectiveBelow.eq_of_root_eq hinj hX (preceq_eq_true_iff_Preceq.mp (Block.preceq_self X))
      hBT (preceq_eq_true_iff_Preceq.mp (Block.preceq_self B.erase)) hroot)

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

/-- Along the path `W` of the bundle, if every tick has an outcome, the author of `a` and the
    proposer of `s` are in `Hs (t + Δ)`, the author emits `a` at `t ≥ lo`,
    `t + Δ ≤ proposal_time s`, and `proposal_time s` is inside the horizon, then `a`'s erasure is
    among the processed attestations of the proposer's duty store of `s`, staged from the world of
    `W` strictly before `proposal_time s`. -/
theorem honestAttestation_mem_processedAtProposal_after_gstOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    {s : Slot}
    (hhor : M.proposal_time S.E s ≤ rho.horizon)
    {a : NamedAttestation V} {t : Time}
    (haHon : a.val_index ∈ Hs (t + S.E.Δ))
    (hprop : S.E.proposer s ∈ Hs (t + S.E.Δ))
    (hemit : Restated.Vocabulary.Execution.NamedRun.emits M S rho W a.val_index (Object.attest a) t)
    (hpost : lo ≤ t)
    (hdelay : t + S.E.Δ ≤ M.proposal_time S.E s) :
    let duty := Restated.Vocabulary.Proofs.Optimistic.tickStore M S
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st.core
      (M.proposal_time S.E s)
    a.erase ∈ duty.processed_attestations S.hc := by
  intro duty
  set p := S.E.proposer s with hp
  set tp := M.proposal_time S.E s with htp
  have hW := hf.onePath
  have hlt : t < tp := lt_of_lt_of_le (Int.lt_add_of_pos_right _ S.E.Δ_pos) hdelay
  have htShape := (Restated.Vocabulary.Proofs.Optimistic.emits_attest_shape facts S W hW hemit).2
  have hemitAction : Restated.Vocabulary.Execution.NamedRun.emits M S rho W a.val_index
      (Object.attest a) (Restated.Vocabulary.Execution.Setup.a M S a.round) := by
    rw [← htShape]; exact hemit
  have hgat : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S a.round) := by
    rw [← htShape]; exact hpost
  have htΔ : t ≤ t + S.E.Δ := le_of_lt (Int.lt_add_of_pos_right _ S.E.Δ_pos)
  have haA : a.val_index ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S a.round)) := by
    rw [← htShape]; exact hHs _ _ htΔ haHon
  have haT : a.val_index ∈ Hs t := hHs _ _ htΔ haHon
  obtain ⟨i, hi, hem⟩ := id hemit
  have hselfRow : a ∈ (W (i + 1) a.val_index).st.sg_rows a.round := by
    have hcall : Restated.Vocabulary.Execution.NamedRun.actualHandlesAt M S rho W i a.val_index
        (Object.attest a) (Restated.Vocabulary.Execution.Setup.a M S a.round) := by
      rw [← htShape]
      exact ⟨Or.inl (Or.inl ⟨t, hi, hem⟩), ⟨Record.Event.tick a.val_index t, hi, rfl, rfl⟩⟩
    exact Restated.honest_row_after_callOn facts S rho Hs Xb hf hHs haA hemitAction hcall
      (le_refl _) (lt_add_of_pos_right _ S.E.Δ_pos) haA hgat
  have hselfPool : a.erase ∈ (W (i + 1) a.val_index).st.sg_pool a.round :=
    facts.sto.pool_view_mem _
      (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho (i + 1) a.val_index
        (W (i + 1)) (hW (i + 1)).1).1.1.1.2.2.2.1
      a hselfRow
  have hpHon : p ∈ Hs (t + S.E.Δ) := hprop
  have hpA : p ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S a.round)) := by
    rw [← htShape]; exact hHs _ _ htΔ hpHon
  have haRead : a.erase ∈ (W (strictEventIndex rho tp) p).st.sg_pool a.round := by
    by_cases hsame : p = a.val_index
    · have hreadSelf := Restated.attest_mem_stateBeforeTime_of_postOn facts S Hs Xb hf hi
        (by simpa only [Record.Event.time] using hlt) hselfPool
      rw [hsame]
      exact hreadSelf
    · obtain ⟨td, htaTd, htd, j', hcall⟩ :=
        hf.broadcast a.val_index (Object.attest a) t haT hemit p hpHon hpost
          (hdelay.trans hhor) (fun _ h => by cases h)
      have hlo : (Restated.Vocabulary.Execution.Setup.a M S a.round) ≤ td := by
        rw [← htShape]
        exact htaTd
      have hhi : td < (Restated.Vocabulary.Execution.Setup.a M S a.round) + S.E.Δ := by
        rw [← htShape]
        exact htd
      have hrow : a ∈ (W (j' + 1) p).st.sg_rows a.round :=
        Restated.honest_row_after_callOn facts S rho Hs Xb hf hHs
          (hHs _ _ (le_of_lt htd) haHon) hemitAction hcall hlo hhi hpA hgat
      have hpool : a.erase ∈ (W (j' + 1) p).st.sg_pool a.round :=
        facts.sto.pool_view_mem _
          (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho (j' + 1) p
            (W (j' + 1)) (hW (j' + 1)).1).1.1.1.2.2.2.1
          a hrow
      obtain ⟨-, e', he', -, hte'⟩ := hcall
      have htdlt : td < tp := lt_of_lt_of_le htd hdelay
      exact Restated.attest_mem_stateBeforeTime_of_postOn facts S Hs Xb hf he'
        (by have h : e'.time < tp := hte' ▸ htdlt; exact h) hpool
  have haDuty : a.erase ∈ M.store_sg_pool duty a.round := by
    rw [facts.sto.Sts_mem_sg_pool_iff, tickStore_sg_votes₄₉b facts, ← facts.sto.Sts_mem_sg_pool_iff]
    exact haRead
  have hround : a.round ≤ (M.round_of S.hc duty.s) := by
    have hltAction : (Restated.Vocabulary.Execution.Setup.a M S a.round) < M.proposal_time S.E s := by
      rw [← htShape]
      exact hlt
    have hr := Restated.Vocabulary.Protocol.action_round_le_of_lt_proposal facts S
      (r := a.round) (s := s) hltAction
    have hs : duty.s = s := by
      show (Restated.Vocabulary.Proofs.Optimistic.tickStore M S _ tp).s = s
      rw [Restated.Vocabulary.Proofs.Optimistic.tickStore, facts.sto.store_with_t_s_s,
        facts.sch.slotOf_proposal_time]
    rw [hs]
    exact hr
  rw [← namedAttestation_erase_round a] at haDuty hround
  exact Restated.Vocabulary.Protocol.mem_processed_attestations_of_pool facts
    S.hc duty haDuty hround

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
open DecoupledConsensusModel.Protocol (derive_named)

/-- For every world `w` after `n` events, if the largest `h_max` over `X` in `w` is `H + 1`, then
    some member of `X` has `h_max` exactly `H + 1` in `w`. -/
theorem exists_honest_localHMax_eq_of_honestHMaxBeforeIndex_eq_succOn (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (X : Finset V) (n : Nat) (H : Height) :
    ∀ w ∈ Record.stateBeforeOf M S rho n,
      (X.sup fun u => (w u).st.h_max) = H + 1 → ∃ v ∈ X, (w v).st.h_max = H + 1 := by
  intro w hw heq
  have hlt : H < X.sup fun u => (w u).st.h_max := by
    rw [heq]
    exact Nat.lt_succ_self H
  obtain ⟨v, hv, hlocal⟩ :=
    Restated.exists_honest_localHMax_gt_of_lt_honestHMaxBeforeIndexOn facts S rho X n H w hw hlt
  have hupper :=
    (Restated.localHMax_le_honestHMaxBeforeIndexOn facts S rho X n hv w hw).trans_eq heq
  have hlower : H + 1 ≤ (w v).st.h_max :=
    Nat.succ_le_iff.mpr hlocal
  exact ⟨v, hv, Nat.le_antisymm hupper hlower⟩

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
open DecoupledConsensusModel.Protocol (derive_named)

/-- If `X ⊆ Xb` and the largest `h_max` over `X` in `W n` is `H + 1`, then some member of `X` holds,
    in `W n`, a body that is a run block read through `Xb` along `W` with derived height `H + 1`. -/
theorem exists_honest_exactHMaxCarrierAtPrefixOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) (X : Finset V) {lo : Int}
    {W : Nat → V → M.N} (_hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo) (hXXb : X ⊆ Xb)
    (n : Nat) (H : Height)
    (heq : (X.sup fun u => (W n u).st.h_max) = H + 1) :
    ∃ v ∈ X, ∃ carrier : NamedBlock V,
      carrier ∈ (W n v).st.bodies ∧
      Restated.RunBlockOn M S rho W Xb carrier ∧
      (M.derive_named S.E S.cfg carrier).h = H + 1 := by
  obtain ⟨v, hv, hlocal⟩ :=
    Restated.exists_honest_localHMax_eq_of_honestHMaxBeforeIndex_eq_succOn facts S rho X n H (W n)
      (_hf.onePath n).1 heq
  obtain ⟨carrier, hcarrier, hcarrierHeight⟩ :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.maximum_carrier_stateBefore facts S rho n v (W n)
      (_hf.onePath n).1
  exact ⟨v, hv, carrier, hcarrier,
    Restated.runBlock_of_stateBefore_memOn facts S W Xb (hXXb hv) hcarrier,
    hcarrierHeight.trans hlocal⟩

end

/-! ## Height crossings at an event prefix -/

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- If the named bodies of `st` contain the parent of each of them, every named ancestor of a body
    of `st` is a body of `st`. -/
private theorem ancestor_body_mem₄₉w {st : M.NS}
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

/-- Along the path `W` of the bundle, if `X ⊆ Xb`, `1 ≤ blocked`, and the largest `h_max` over `X`
    in `W n` is `blocked + 2`, then some member of `X` holds in `W n` a carrier at derived height
    `blocked + 2` and an ancestor of it at derived height `blocked`, both run blocks read through
    `Xb` along `W`. -/
theorem prefixHeightCrossingWitness_of_frontier_eqOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) (X : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo) (hXXb : X ⊆ Xb)
    {n : Nat} {blocked : Height} (hblocked : 1 ≤ blocked)
    (heq : (X.sup fun u => (W n u).st.h_max) = (blocked + 1) + 1) :
    Restated.PrefixHeightCrossingWitnessOn M S rho W X Xb n blocked := by
  obtain ⟨v, hv, carrier, hcarrier, hcarrierRun, hcarrierHeight⟩ :=
    Restated.exists_honest_exactHMaxCarrierAtPrefixOn facts S Hs Xb X hf hXXb n (blocked + 1) heq
  have hlt : blocked < (M.derive_named S.E S.cfg carrier).h := by
    rw [hcarrierHeight]
    exact Nat.lt_succ_of_lt (Nat.lt_succ_self blocked)
  obtain ⟨anchor, hanchorCarrier, hanchorHeight, -⟩ :=
    facts.cs.height_crossing S.E S.cfg carrier blocked hblocked hlt
  have hpc : Restated.Vocabulary.Proofs.NamedStore.NamedParentClosed M (W n v).st :=
    (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho n v (W n)
      (hf.onePath n).1).1.1.1.2.2.1
  have hanchor : anchor ∈ (W n v).st.bodies := ancestor_body_mem₄₉w hpc hcarrier hanchorCarrier
  exact ⟨v, hv, carrier, anchor, hcarrier, hanchor, hcarrierRun,
    Restated.runBlock_of_stateBefore_memOn facts S W Xb (hXXb hv) hanchor,
    hanchorCarrier, hanchorHeight, by
      simpa only [Nat.add_assoc] using hcarrierHeight⟩

/-- Along the path `W` of the bundle, if every set of the family at an instant `t ≥ 0` is inside `X`
    and the largest `h_max` over `X` in `W start` is less than `H`, then for every tick before index
    `start` of a validator in the set for the tick's instant, the outcome of that tick along `W`
    sends no attestation whose height pair names `H`. -/
theorem noLocalHeightPairBefore_of_frontier_ltOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) (X : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hX : ∀ t : Int, 0 ≤ t → Hs t ⊆ X)
    {start : Nat} {H : Height}
    (hbound : (X.sup fun x => (W start x).st.h_max) < H) :
    ∀ {i : Nat} {v : V} {t : Time} {a : NamedAttestation V},
      i < start → v ∈ Hs t → rho.events[i]? = some (Record.Event.tick v t) →
        ∀ out : M.N × List (NamedObject V), M.tick S v (W i v) t ⇢ out → W (i + 1) v = out.1 →
          Object.attest a ∈ out.2 → a.height_pair.erase.height? ≠ some H := by
  intro i v t a hi hv hevent out hout hstep hmem hrow
  have ht0 : 0 ≤ t := by
    simpa only [Record.Event.time] using (hf.in_horizon _ (List.mem_of_getElem? hevent)).1
  exact (Nat.not_le_of_gt hbound)
    (Restated.honestEmittedHeight_le_honestHMaxBeforeIndexOn facts S Hs Xb X hf (hX t ht0 hv)
      hevent ⟨out, hout, hstep, hmem⟩ hi hrow)

end

end DecoupledConsensusModel.Sts.Restated
