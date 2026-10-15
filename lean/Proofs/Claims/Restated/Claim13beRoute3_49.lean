import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13beRoute3_45
import Proofs.Claims.Restated.Claim13beRoute3_45b
import Proofs.Claims.Restated.Claim13beRoute3_46
import Proofs.Claims.Restated.Claim13beRoute3_47
import Proofs.Claims.Restated.Claim13beRoute3_47b
import Proofs.Claims.Restated.Claim13beRoute3_48
import Proofs.Claims.Restated.Vocabulary_Execution_BridgesCore
import Proofs.Claims.Restated.Vocabulary_Execution_EmissionShape
import Proofs.Claims.Restated.Vocabulary_Execution_ReceiptCallsBase
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Claims.Restated.Vocabulary_Protocol_ChainState_ProposalBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Duties_Inputs_ActionSources
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_ProposalSnapshotBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_ProposalParent
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_GoldfishVotePool
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_Pool
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreRoots
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_TickBridges
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_AdoptionTransport
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_Alignment
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_SlotInduction
import Proofs.Claims.Restated.Vocabulary_Protocol_ValidatorClient_BlockEmission
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.RunVocabulary
import Model.Conditions.Vocabulary_Internal_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_Definitions_TickReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedHeadReads
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedReceiptCalls
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Node
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Objects
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_FinalityGadget_Crossing
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Agreement
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Confirmation
import Proofs.Vocabulary.Protocol.ForkChoice.Views.ProposalCore
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Protocol_Grades_Main
import Model.Conditions.Vocabulary_Protocol_Handlers_Blocks
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_Pool
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_Handlers_TickBridges
import Model.Conditions.Vocabulary_Protocol_Schedule_Alignment
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Conditions.Vocabulary_Statements_Instantiation_Proposals
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_25

/-!
# Emitted heights, vote relay and proposal reads along a path of the run

Theorems about emitted heights, broadcast and relay of Goldfish votes, the settling of votes in
pools, vote-duty and proposal reads, and cone support from confirmation votes, stated over a model
`M : Record.Model V` along the path `W` of the bundle `AdmissibleFieldsOn`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

/-! ## Helpers -/

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-- Slot `s`'s vote instant is before its support cutoff. -/
private theorem vote_time_lt_support_cutoff₄₉ (facts : Record.Facts M) (S : Setup V) (s : Slot) :
    M.vote_time S.E s < M.support_cutoff S.E s := by
  rcases lt_or_gt_of_ne (facts.sch.support_cutoff_ne_vote_time S.E s) with h | h
  · exfalso
    have h1 := facts.sch.support_cutoff_lt_vote_time_imp_lt_proposal_time S.E h
    have h2 := facts.sch.proposal_time_slotOf_le S.E (le_of_lt (facts.sch.support_cutoff_pos S s))
    rw [facts.sch.slotOf_support_cutoff] at h2
    exact absurd h1 (not_lt.mpr h2)
  · exact h

omit [DecidableEq V] [Fintype V] in
/-- For `Δ > 0`, if `a` and `b` are multiples of `Δ` and `a < b`, then `a + Δ ≤ b`. -/
private theorem add_delta_le_of_lt_emod₄₉ {Δ a b : Int} (hΔ : 0 < Δ) (ha : a % Δ = 0)
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

/-- A slot's support cutoff plus one delay is at most the slot's view freeze. -/
private theorem support_cutoff_add_delta_le_view_freeze₄₉ (facts : Record.Facts M) (S : Setup V)
    (s : Slot) : M.support_cutoff S.E s + S.E.Δ ≤ M.view_freeze S.E s := by
  obtain ⟨k, hk⟩ := (facts.sch.publicTime_iff S (M.view_freeze S.E s)).mpr
    ⟨s, Or.inr (Or.inr (Or.inr rfl))⟩
  have hb : M.view_freeze S.E s % S.E.Δ = 0 := by
    rw [hk]
    exact Int.mul_emod_left _ _
  exact add_delta_le_of_lt_emod₄₉ S.E.Δ_pos (facts.sch.support_cutoff_emod_delta S s) hb
    (facts.sch.Optimistic_support_cutoff_lt_view_freeze S.E s)

/-- A slot's vote instant plus one delay is at most the slot's support cutoff. -/
private theorem vote_time_add_delta_le_support_cutoff₄₉ (facts : Record.Facts M) (S : Setup V)
    (s : Slot) : M.vote_time S.E s + S.E.Δ ≤ M.support_cutoff S.E s :=
  add_delta_le_of_lt_emod₄₉ S.E.Δ_pos (facts.sch.vote_time_emod_delta S s)
    (facts.sch.support_cutoff_emod_delta S s) (vote_time_lt_support_cutoff₄₉ facts S s)

/-- The store a tick at `t` hands its first duty, staged from `n`'s core store, has the tree of
    `n`'s core store. -/
private theorem tickStore_T₄₉ (facts : Record.Facts M) {S : Setup V} (n : M.N) (t : Time) :
    (Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core t).T = n.st.core.T := by
  rw [Restated.Vocabulary.Proofs.Optimistic.tickStore,
    ← facts.hd.setClock_core_eq_store_with_t_s S.E n.st t, facts.hd.Sts_setClock_core_T]

/-- If every vote of `votesv` is in `latew` or shows its author equivocating there, and no two
    blocks of the union of `Tv` and `Tw` share a root, then `CrossView` holds of the two trees and
    the two vote sets. -/
private theorem crossView_of_rootInjective₄₉ {Tv Tw : Finset (Block V)}
    {votesv latew : Finset (GoldfishVote V)}
    (transfer : ∀ u ∈ votesv, u ∈ latew ∨ M.equivocates latew u.val_index = true)
    (root_injective : RootInjectiveBelow (Tv ∪ Tw)) :
    Restated.Vocabulary.Protocol.CrossView M Tv Tw votesv latew :=
  ⟨transfer, (DecoupledConsensusModel.Protocol.CrossView.of_rootInjective (votesv := votesv)
    (latew := votesv) (fun u hu => Or.inl hu) root_injective).resolve⟩

/-- A slot's support cutoff plus one delay is before the slot's confirmation instant. -/
private theorem support_cutoff_add_delta_lt_confirmation₄₉ (facts : Record.Facts M) (S : Setup V)
    (s : Slot) : M.support_cutoff S.E s + S.E.Δ < M.confirmation_time S.E s := by
  have h1 := facts.sch.Optimistic_support_cutoff_lt_view_freeze S.E s
  have h2 := facts.sch.view_freeze_add_delta_lt_confirmation_time S.E s
  linarith only [h1, h2]

/-- Setting the clock of a named store to an instant no earlier than its clock keeps `PoolStamps`. -/
private theorem poolStamps_setClock₄₉ (facts : Record.Facts M) (E : Env V) (st : M.NS) {t : Time}
    (hle : st.core.t ≤ t) (hps : Restated.Vocabulary.Protocol.PoolStamps M st.core) :
    Restated.Vocabulary.Protocol.PoolStamps M (M.ns_setClock E st t).core := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k u' hu'
    rw [facts.hd.setClock_core_gf_votes] at hu'
    exact hps.slot k u' hu'
  · intro k u' hu'
    rw [facts.hd.setClock_core_gf_votes] at hu'
    rw [facts.hd.setClock_core_timestamp_vote]
    exact hps.stamped k u' hu'
  · intro u' hu'
    rw [facts.hd.setClock_core_timestamp_vote] at hu'
    rw [facts.hd.setClock_core_gf_votes]
    exact hps.pooled u' hu'
  · intro u' c hc
    rw [facts.hd.setClock_core_timestamp_vote] at hc
    rw [facts.hd.Sts_setClock_core_t]
    exact le_trans (hps.bounded u' c hc) (WithBot.coe_le_coe.mpr hle)

/-- If the pool of `st'` carries that of `st` (`PoolCarry`), every vote of slot `k` stamped before
    `Γ` in `st` is stamped before `Γ` in `st'`. -/
private theorem beforeCutoff_subset_of_poolCarry₄₉ (facts : Record.Facts M) {st st' : M.S}
    (h : Restated.Vocabulary.Protocol.PoolCarry M st st') (k : Slot) (Γ : Time) :
    ∀ x ∈ beforeCutoff st.timestamp_vote Γ (M.store_pool st k),
      x ∈ beforeCutoff st'.timestamp_vote Γ (M.store_pool st' k) := by
  intro x hx
  rw [mem_beforeCutoff_iff] at hx ⊢
  obtain ⟨hp, hs⟩ := hx
  obtain ⟨σ, hσ, hlt⟩ := exists_stamp_of_stampedBefore hs
  exact ⟨(facts.sto.mem_store_pool_iff _ _ _).mpr (h.mem k x ((facts.sto.mem_store_pool_iff _ _ _).mp hp)),
    stampedBefore_of_lt (h.stamp x σ hσ) hlt⟩

/-- Every node state the round-`r` action read can yield from `before` holds the bodies `before`
    holds. -/
private theorem actionReadFrom_bodies₄₉ (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ nr ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      nr.st.bodies = before.st.bodies := by
  rintro _ ⟨c, -, st, hst, rfl⟩
  rw [facts.nd.mkNode_st, facts.nd.store_with_cache_bodies,
    facts.dt.named_update_confirmation_with_bodies _ _ _ _ _ st hst,
    facts.hd.ModelProperties_setClock_bodies]

/-- For every node state `before` and round `r`, some node state is in
    `actionReadFrom M S before r`. -/
private theorem actionReadFrom_nonempty₄₉ (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∃ n, n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r := by
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc before.st.core.toHealing
    (Restated.Vocabulary.Execution.Setup.a M S r) before.cache
  obtain ⟨st, hst⟩ := facts.dt.duties_update_confirmation_with_nonempty (M.gradeContract c) S.E S.hc
    (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r))
    (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1)
  exact ⟨_, c, hc, st, hst, rfl⟩

open scoped DC in
/-- `m >>= k` can return `b` exactly when `m` can return some `a` and `k a` can return `b`. -/
private theorem returns_bind_iff₄₉ {α β : Type} (m : DC.NDRE α) (k : α → DC.NDRE β)
    (b : β) : (m >>= k) ⇢ b ↔ ∃ a, m ⇢ a ∧ k a ⇢ b := by
  unfold Record.Returns
  simp only [ExceptT.run_bind, Set.bind_def]
  constructor
  · intro h
    obtain ⟨e, he, hb⟩ := Set.mem_iUnion₂.mp h
    cases e with
    | ok a => exact ⟨a, he, hb⟩
    | error err => simp at hb
  · rintro ⟨a, ha, hb⟩
    exact Set.mem_iUnion₂.mpr ⟨_, ha, hb⟩

open scoped DC in
/-- If `f <$> m` can return `b`, then `m` can return some `a` with `f a = b`. -/
private theorem returns_map_elim₄₉ {α β : Type} (f : α → β) (m : DC.NDRE α) (b : β)
    (h : (f <$> m) ⇢ b) : ∃ a, m ⇢ a ∧ f a = b := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image] at h
  obtain ⟨e, he, hb⟩ := h
  cases e with
  | ok a => exact ⟨a, he, by simpa [Except.map] using hb⟩
  | error err => simp [Except.map] at hb

/-- For every node state `n`, the finality-gadget source read at `n` can return some value. -/
private theorem actionFGSource_nonempty₄₉ (facts : Record.Facts M) (S : Setup V)
    (n : M.N) : ∃ o, Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n ⇢ o := by
  obtain ⟨A2, hA2⟩ := facts.dt.grade2_block_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s)
  obtain ⟨o, ho⟩ := facts.dt.fg_source_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s) A2
  exact ⟨o, (returns_bind_iff₄₉ _ _ _).2 ⟨A2, hA2, ho⟩⟩

/-- For the path `W` of the bundle, the world `W (strictEventIndex rho t)` is one of the worlds
    strictly before `t`. -/
private theorem path_mem_stateBeforeTime₄₉ (facts : Record.Facts M) (S : Setup V)
    {rho : Record.Run V}
    (Hs : Int → Finset V) (Xb : Finset V) {lo : Int} {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo) (t : Time) :
    W (strictEventIndex rho t) ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t := by
  have h := Restated.stateBeforeTime_eq_takeOn facts S Hs Xb hf t
  have hmem := (hf.onePath (strictEventIndex rho t)).1
  unfold strictEventIndex at hmem
  show W _ ∈ Restated.Vocabulary.Execution.Run.stateBeforeTime M S rho t
  rw [h]
  exact hmem

omit [DecidableEq V] [Fintype V] in
/-- In a run sorted by key, every event before the index `strictEventIndex rho t` is strictly before
    the instant `t`. -/
private theorem time_lt_of_lt_strict₄₉ {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f)) (t : Time) :
    ∀ (j : Nat) (e : Record.Event V), j < strictEventIndex rho t → rho.events[j]? = some e →
      e.time < t := by
  intro j e hj he
  have hpre : rho.events.filter (fun e => decide (e.time < t)) =
      rho.events.take (rho.events.filter (fun e => decide (e.time < t))).length := by
    refine List.prefix_iff_eq_take.mp ?_
    rw [DecoupledConsensusModel.Proofs.Bridges.filter_eq_takeWhile_of_pairwise
      (R := fun e f => Record.Event.key e ≤ Record.Event.key f) ?_ _ hsorted]
    · exact List.takeWhile_prefix _
    · intro e f hk hf
      simp only [decide_eq_true_eq] at hf ⊢
      exact lt_of_le_of_lt (Restated.time_le_of_key_le hk) hf
  have hj' : j < (rho.events.filter (fun e => decide (e.time < t))).length := hj
  have hmem : e ∈ rho.events.filter (fun e => decide (e.time < t)) := by
    rw [hpre]
    exact List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hj']; exact he)
  have hp := (List.mem_filter.mp hmem).2
  simpa only [decide_eq_true_eq] using hp

/-- If the erasure of `B` is not in the tree of `st` and is in the tree of the store the core call
    on `B` returns on `st`, then `B` is among that store's named blocks. -/
private theorem core_new_body₄₉ (facts : Record.Facts M) (S : Setup V) (st : M.NS)
    (B : NamedBlock V) (hnew : B.erase ∉ st.core.T)
    (hpost : B.erase ∈ (M.postCore S st B).core.T) :
    B ∈ (M.postCore S st B).bodies := by
  rw [facts.nd.postCore_eq_process_block_core] at hpost ⊢
  by_cases hp : B.parent ∈ st.bodies
  · rw [facts.hd.process_block_core_bodies_eq_commit S.E S.hc S.cfg hp]
    exact facts.hd.mem_commitBlock_bodies_of_fresh S.E S.hc S.cfg rfl ⟨hnew, hpost⟩
  · rw [facts.hd.process_block_core_of_parent_not_mem S.E S.hc S.cfg hp] at hpost
    exact False.elim (hnew hpost)

/-- If the erasure of `B` is not in the tree of `st` and is in the tree of the store the core call
    on `B` returns on `st`, then `B` is among the named blocks of the store the block call on `B`
    returns on `st`. -/
private theorem on_block_new_body₄₉ (facts : Record.Facts M) (S : Setup V) (st : M.NS)
    (B : NamedBlock V) (hnew : B.erase ∉ st.core.T)
    (hpost : B.erase ∈ (M.postCore S st B).core.T) :
    B ∈ (M.on_block_with .alsoCarried S.E S.hc S.cfg st B).bodies := by
  have hheld := core_new_body₄₉ facts S st B hnew hpost
  by_cases hc : B ∉ st.bodies ∧ B ∈ (M.postCore S st B).bodies
  · rw [facts.nd.on_block_with_eq_admit_rows_postCore S st B hc.1 hc.2,
      (facts.hd.admit_rows_bodies_and_core_T S.hc _ _).1]
    exact hheld
  · rw [facts.nd.on_block_with_eq_postCore_of_not_new S st B hc]
    exact hheld

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

/-- Along the path `W` of the bundle, if `v` emits `a` at `t` and `a`'s height pair names the height
    `h`, then `h` is at most the `h_max` of `v`'s store in `W (strictEventIndex rho t)`. -/
theorem honestEmittedHeight_le_localHMaxBeforeTimeOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} {a : NamedAttestation V} {t : Time} {h : Height}
    (hemit : Restated.Vocabulary.Execution.Run.emits M S rho W v (Object.attest a) t)
    (hh : a.height_pair.erase.height? = some h) :
    h ≤ (W (strictEventIndex rho t) v).st.h_max := by
  have ht : t = (Restated.Vocabulary.Execution.Setup.a M S a.round) :=
    (Restated.Vocabulary.Proofs.Optimistic.emits_attest_shape facts S W hf.onePath hemit).2
  subst ht
  obtain ⟨i, hi, out, hout, -, hrow⟩ := hemit
  have hmemN := path_mem_stateBeforeTime₄₉ facts S Hs Xb hf
    (Restated.Vocabulary.Execution.Setup.a M S a.round)
  obtain ⟨n, hn⟩ := actionReadFrom_nonempty₄₉ facts S
    (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round)) v) a.round
  obtain ⟨D, hD⟩ := facts.dt.attest_with_nonempty (M.gradeContract n.cache) S.E S.hc (S.node v)
    n.st n.record
  rcases Restated.action_emissionOn facts S rho Hs Xb hf i v a.round hi out hout n hn D hD with
    ⟨-, hout2⟩ | ⟨-, hout2⟩
  · rw [hout2] at hrow
    simp only [List.mem_singleton, NamedObject.attest.injEq] at hrow
    obtain ⟨entry, timeout, hvote⟩ :=
      (priv% Proofs.Vocabulary.Objects.EmittedHeightBound
        DecoupledConsensusModel.Proofs.HealingSurface.heightPair_vote_of_height) hh
    rw [hrow] at hvote
    have hnmem : n ∈ Restated.Vocabulary.Proofs.HealingSurface.actionReadAt M S rho v a.round :=
      ⟨_, hmemN, hn⟩
    obtain ⟨o, ho⟩ := actionFGSource_nonempty₄₉ facts S n
    obtain ⟨Cfg, rfl, hheight, -⟩ :=
      Restated.Vocabulary.Proofs.NamedActionSources.action_source facts S rho v a.round n hnmem
        h entry timeout D hD hvote o ho
    obtain ⟨C, hCmem, -, hCderiv, -⟩ :=
      Restated.Vocabulary.Proofs.NamedActionSources.action_witness facts S rho v a.round n hnmem
        Cfg ho
    rw [hCderiv] at hheight
    rw [actionReadFrom_bodies₄₉ facts S _ _ n hn] at hCmem
    have hbound :=
      Restated.Vocabulary.Proofs.NamedStoreBridge.heights_le_hMax_stateBeforeTime facts S rho
        (Restated.Vocabulary.Execution.Setup.a M S a.round) v _ hmemN C hCmem
    rw [hheight] at hbound
    exact hbound
  · rw [hout2] at hrow
    simp only [List.not_mem_nil] at hrow

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

/-- Along the path `W` of the bundle, if `v ∈ X` emits `a` at `u ≤ t` and `a`'s height pair names
    `h`, then `h` is at most the largest `h_max` over `X` in the world `W (strictEventIndex rho t)`. -/
theorem honestEmittedHeight_le_honestHMaxBeforeTimeOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) (X : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} (hv : v ∈ X) {a : NamedAttestation V}
    {u t : Time} {h : Height}
    (hemit : Restated.Vocabulary.Execution.Run.emits M S rho W v (Object.attest a) u)
    (hh : a.height_pair.erase.height? = some h) (hut : u ≤ t) :
    h ≤ X.sup fun x => (W (strictEventIndex rho t) x).st.h_max := by
  have hlocal := (Restated.honestEmittedHeight_le_localHMaxBeforeTimeOn facts S Hs Xb hf hemit hh).trans
    (Restated.storeBeforeTime_hMax_monoOn facts S Hs Xb hf v hut)
  exact hlocal.trans (Restated.localHMax_le_honestHMaxBeforeIndexOn facts S rho X _ hv
    (W (strictEventIndex rho t)) (hf.onePath _).1)

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

/-- Along the path `W` of the bundle, genesis is in the tree of `v`'s store in
    `W (strictEventIndex rho Gamma)`, stamped before any `cutoff`. -/
theorem genesis_mem_and_stamp_storeBeforeTimeOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (v : V) (Gamma cutoff : Time) :
    Block.genesis ∈ (W (strictEventIndex rho Gamma) v).st.T ∧
      stampedBefore (W (strictEventIndex rho Gamma) v).st.timestamp_block
        cutoff Block.genesis = true := by
  have hcarry : Restated.Vocabulary.Protocol.BlockCarry M (W 0 v).st.core
      (W (strictEventIndex rho Gamma) v).st.core :=
    Restated.block_carryOn facts S Hs Xb hf v _ (Nat.zero_le _)
  have hW0 : W 0 = fun u => M.initial S u := (hf.onePath 0).1
  have hmem0 : Block.genesis ∈ (W 0 v).st.core.T := by
    rw [hW0]
    have hT : (M.initial S v).st.core.T = {Block.genesis} := by
      rw [facts.nd.initial_st, facts.hd.initial_core_T]
    show Block.genesis ∈ (M.initial S v).st.core.T
    rw [hT]
    exact Finset.mem_singleton_self _
  have hstamp0 : (W 0 v).st.core.timestamp_block Block.genesis = some ⊥ := by
    rw [hW0]
    exact facts.nd.initial_timestamp_genesis S v
  refine ⟨hcarry.mem Block.genesis hmem0, ?_⟩
  exact stampedBefore_of_lt (hcarry.stamp Block.genesis ⊥ hstamp0) (WithBot.bot_lt_coe cutoff)

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

/-- Along the path `W` of the bundle, if `v` admitted `B` before `Gamma` and `Gamma ≤ Gamma'`, then
    `B` is in the tree of `v`'s store in `W (strictEventIndex rho Gamma')`, stamped before `Gamma`. -/
theorem admittedBefore_mem_and_stamp_atOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} {B : Block V} {Gamma Gamma' : Time}
    (hadmit : Restated.Vocabulary.Protocol.AdmittedBefore M S rho W v B Gamma) (hle : Gamma ≤ Gamma') :
    B ∈ (W (strictEventIndex rho Gamma') v).st.T ∧
      stampedBefore (W (strictEventIndex rho Gamma') v).st.timestamp_block Gamma B = true := by
  have hW := hf.onePath
  obtain ⟨C, hCerase, i, t, hacc, hlt⟩ := hadmit
  obtain ⟨_, ⟨e, he, _, het⟩⟩ := hacc.1
  have hpostBodies : C ∈ (W (i + 1) v).st.bodies := of_decide_eq_true hacc.2.2
  have hcoh := (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho (i + 1) v
    (W (i + 1)) (hW (i + 1)).1).1.1.1
  have hpost : B ∈ (W (i + 1) v).st.core.T := by
    rw [hcoh.1, ← hCerase]
    exact Finset.mem_image_of_mem NamedBlock.erase hpostBodies
  let N := strictEventIndex rho Gamma'
  have hiN : i < N := by
    by_contra hnot
    have hNle : N ≤ i := Nat.le_of_not_gt hnot
    have hGamma'e : Gamma' ≤ e.time :=
      Restated.le_time_of_index_geOn facts S Hs Xb hf (t := Gamma') (j := i) (e := e) hNle he
    rw [het] at hGamma'e
    exact (not_le_of_gt (lt_of_lt_of_le hlt hle)) hGamma'e
  have hcarry : Restated.Vocabulary.Protocol.BlockCarry M (W (i + 1) v).st.core (W N v).st.core :=
    Restated.block_carryOn facts S Hs Xb hf v N (Nat.succ_le_of_lt hiN)
  have hsource : Restated.Vocabulary.Protocol.BlockStamps M (W (i + 1) v).st.core :=
    Restated.blockStamps_stateBeforeOn facts S Hs Xb hf v (i + 1)
  obtain ⟨c, hc⟩ : ∃ c : Stamp, (W (i + 1) v).st.core.timestamp_block B = some c :=
    Option.isSome_iff_exists.mp (hsource.stamped B hpost)
  have hcfinal : (W N v).st.core.timestamp_block B = some c :=
    hcarry.stamp B c hc
  have hclock : (W (i + 1) v).st.core.t ≤ t := by
    have ht := Restated.block_store_time_after_event_leOn facts S Hs Xb hf he v
    simpa only [het] using ht
  have hcGamma : c < (Gamma : Stamp) :=
    lt_of_le_of_lt
      (le_trans (hsource.bounded B c hc) (WithBot.coe_le_coe.mpr hclock))
      (WithBot.coe_lt_coe.mpr hlt)
  exact ⟨hcarry.mem B hpost, stampedBefore_of_lt hcfinal hcGamma⟩

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

/-- Along the path `W` of the bundle, if `v ∈ Hs t` emits `o` at `t ≥ lo`, `w ∈ Hs (t + Δ)`, `t + Δ`
    is inside the horizon and, when `o` is a block `B`, the finalized block of `w`'s store in
    `W (strictEventIndex rho (t + Δ))` is compatible with `B`'s erasure, then `w` handles `o` at
    some instant of `[t, t + Δ)`. -/
theorem broadcast_after_gstOn (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V)
    {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v w : V} {o : Object V} {t : Time}
    (hv : v ∈ Hs t) (hw : w ∈ Hs (t + S.E.Δ)) (hpost : lo ≤ t)
    (hemit : Restated.Vocabulary.Execution.Run.emits M S rho W v o t) (hhor : t + S.E.Δ ≤ rho.horizon)
    (hguard : ∀ B : NamedBlock V, o = .block B →
      Block.compatible (W (strictEventIndex rho (t + S.E.Δ)) w).st.core.F B.erase = true) :
    ∃ t', t ≤ t' ∧ t' < t + S.E.Δ ∧
      ∃ j : Nat, Restated.Vocabulary.Execution.NamedRun.actualHandlesAt M S rho W j w o t' :=
  hf.broadcast v o t hv hemit w hw hpost hhor hguard

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

/-- Along the path `W` of the bundle, if `v ∈ Hs t` accepts the Goldfish vote `u` at `t ≥ lo` at
    index `i`, `w ∈ Hs (t + Δ)` has not processed `u` in `W (i + 1)` and `t + Δ` is inside the
    horizon, then `w` handles `u` at some instant of `[t, t + Δ)`. -/
theorem relay_gf_vote_after_gst_coreOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v w : V} {i : Nat} {u : GoldfishVote V} {t : Time}
    (hv : v ∈ Hs t) (hw : w ∈ Hs (t + S.E.Δ)) (hpost : lo ≤ t)
    (hacc : Restated.Vocabulary.Execution.NamedRun.acceptsAt M S rho W i v (Object.gfVote u) t)
    (hunaccepted : Restated.Vocabulary.Execution.Object.processed M (W (i + 1) w).st
      (Object.gfVote u) = false)
    (hhor : t + S.E.Δ ≤ rho.horizon) :
    ∃ t', t ≤ t' ∧ t' < t + S.E.Δ ∧
      ∃ j : Nat, Restated.Vocabulary.Execution.NamedRun.actualHandlesAt M S rho W j w (Object.gfVote u) t' :=
  hf.relay_gf_vote_handled v i u t hv hacc hpost w hw hunaccepted hhor

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

/-- The conclusion of `relay_gf_vote_after_gst_coreOn`, from its hypotheses gathered in one premise
    structure. -/
theorem relay_gf_vote_after_gstOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v w : V} {i : Nat} {u : GoldfishVote V} {t : Time}
    (hv : v ∈ Hs t) (hw : w ∈ Hs (t + S.E.Δ)) (hpost : lo ≤ t)
    (hacc : Restated.Vocabulary.Execution.NamedRun.acceptsAt M S rho W i v (Object.gfVote u) t)
    (hunaccepted : Restated.Vocabulary.Execution.Object.processed M (W (i + 1) w).st
      (Object.gfVote u) = false)
    (hhor : t + S.E.Δ ≤ rho.horizon) :
    ∃ t', t ≤ t' ∧ t' < t + S.E.Δ ∧
      ∃ j : Nat, Restated.Vocabulary.Execution.NamedRun.actualHandlesAt M S rho W j w (Object.gfVote u) t' :=
  Restated.relay_gf_vote_after_gst_coreOn facts S Hs Xb hf hv hw hpost hacc hunaccepted hhor

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

/-- If event `j` is `f`, every event at an index `k < j` happens no later than `f`. -/
theorem time_le_of_index_lt_eventOn (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {j : Nat} {f : Record.Event V} (hj : rho.events[j]? = some f) :
    ∀ (k : Nat) (e : Record.Event V), k < j → rho.events[k]? = some e → e.time ≤ f.time := by
  intro k e hkj he
  exact Restated.time_le_of_key_le (Restated.key_le_of_index_ltOn facts S Hs Xb hf hkj he hj)

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

/-- Along the path `W` of the bundle, if `w` actually handles the vote `u` of slot `s > 0` at `t`
    with `vote_time s ≤ t < support_cutoff s` and `t < Gamma`, and `u`'s author and `w` are in
    `Hs t`, then for some event `i` before `Gamma`, `w`'s pool of slot `u.slot` in `W (i + 1)`, cut
    at `Gamma`, holds `u` or shows `u`'s author equivocating. -/
theorem actual_gfVote_settled_before_deadlineOn_RecoveryOpeningFrontierRunBlock (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    {j : Nat} {w : V} {u : GoldfishVote V} {s : Slot} {t Gamma : Time}
    (hactual : Restated.Vocabulary.Execution.NamedRun.actualHandlesAt M S rho W j w (Object.gfVote u) t)
    (hs : 0 < s) (hus : u.slot = s) (hval : u.val_index ∈ Hs t)
    (hw : w ∈ Hs t) (hgat : lo ≤ M.vote_time S.E s)
    (hlo : M.vote_time S.E s ≤ t)
    (hcut : t < M.support_cutoff S.E s) (hdeadline : t < Gamma) :
    ∃ i : Nat, ∃ e : Record.Event V, rho.events[i]? = some e ∧ e.time < Gamma ∧
      (u ∈ beforeCutoff
          (W (i + 1) w).st.core.timestamp_vote Gamma
          (M.store_pool (W (i + 1) w).st.core u.slot) ∨
        M.equivocates
          (beforeCutoff
            (W (i + 1) w).st.core.timestamp_vote Gamma
            (M.store_pool (W (i + 1) w).st.core u.slot))
          u.val_index = true) := by
  have _hr_0 : M.reachedNode (W j w) := facts.ndRun.stateBeforeOf_reachedNode S rho j (W j) (hf.onePath j).1 w
  have _hv_0 : M.runs_as (W j w) w := facts.ndRun.stateBeforeOf_runs_as S rho j (W j) (hf.onePath j).1 w
  have _hr_1 : M.reachedNode (W (j + 1) w) := facts.ndRun.stateBeforeOf_reachedNode S rho (j + 1) (W (j + 1)) (hf.onePath (j + 1)).1 w
  have _hv_1 : M.runs_as (W (j + 1) w) w := facts.ndRun.stateBeforeOf_runs_as S rho (j + 1) (W (j + 1)) (hf.onePath (j + 1)).1 w
  have hW := hf.onePath
  have hwVote : w ∈ Hs (M.vote_time S.E s) := hHs _ _ hlo hw
  obtain ⟨hindex, e, he, hnode, htime⟩ := hactual
  rcases hindex with (⟨t', htick', out, hout, hWout, hem⟩ | ⟨t', hdeliver⟩) |
      ⟨B, j', before, hcall⟩
  · have heq : Record.Event.tick w t' = e := Option.some.inj (htick'.symm.trans he)
    have htt : t' = t := (congrArg Record.Event.time heq).trans htime
    subst t'
    have hemit : Restated.Vocabulary.Execution.NamedRun.emits M S rho W w (Object.gfVote u) t :=
      ⟨j, htick', out, hout, hWout, hem⟩
    obtain ⟨hs', ht', -, hus'⟩ := Restated.Vocabulary.Proofs.Optimistic.emits_gfVote_shape facts S W hemit (fun i => facts.ndRun.stateBeforeOf_reachedNode S rho i (W i) (hf.onePath i).1 _) (fun i => facts.ndRun.stateBeforeOf_runs_as S rho i (W i) (hf.onePath i).1 _)
    have hslot : S.E.slotOf t = s := by rw [← hus', hus]
    have htVote : t = M.vote_time S.E s := by
      simpa only [hslot] using ht'
    have hemitVote : Restated.Vocabulary.Execution.NamedRun.emits M S rho W w (Object.gfVote u)
        (M.vote_time S.E s) := by
      simpa only [htVote] using hemit
    have hvalVote : u.val_index ∈ Hs (M.vote_time S.E s) := hHs _ _ hlo hval
    obtain ⟨i, hi, hmem, c, hc, hle⟩ :=
      Restated.mem_pool_of_emitsOn facts S Hs Xb hf hHs hs hemitVote hus hvalVote
    refine ⟨i, _, hi, ?_, ?_⟩
    · simpa only [Record.Event.time, htVote, Record.Event.time] using hdeadline
    · apply Or.inl
      rw [mem_beforeCutoff_iff]
      refine ⟨?_, ?_⟩
      · rw [hus]
        exact (facts.sto.mem_store_pool_iff _ _ _).2 hmem
      · have htime' : M.vote_time S.E s < Gamma := by
          rw [← htVote]
          exact hdeadline
        exact stampedBefore_of_lt hc (lt_of_le_of_lt hle (WithBot.coe_lt_coe.mpr htime'))
  · have heq : Record.Event.deliver w (Object.gfVote u) t' = e :=
      Option.some.inj (hdeliver.symm.trans he)
    have htt : t' = t := (congrArg Record.Event.time heq).trans htime
    subst t'
    have hcommittee : u.val_index ∈ S.E.committee u.slot :=
      (hf.wire j w (Object.gfVote u) t hdeliver).2 u rfl
    have hslot : (W j w).st.core.s = s :=
      Restated.delivery_store_slotOn facts S Hs Xb hf hwVote hgat hdeliver hlo hcut
    have hfresh : ¬ u.slot < (W j w).st.core.s - 1 := by
      rw [hslot, hus]
      exact Nat.not_lt.mpr (Nat.sub_le s 1)
    have hfuture : ¬ (W j w).st.core.s < u.slot := by
      rw [hslot, hus]
      exact Nat.lt_irrefl s
    have hequiv := Restated.pool_no_honest_equivocationOn facts S Hs Xb hf hHs w j (T := t)
      (fun k e' hk he' => by
        simpa only [Record.Event.time, Record.Event.time] using
          Restated.time_le_of_index_lt_eventOn facts S Hs Xb hf hdeliver k e' hk he')
      u.slot hval
    have hstamps : Restated.Vocabulary.Protocol.PoolStamps M (W j w).st.core :=
      Restated.poolStamps_stateBeforeOn facts S Hs Xb hf w j
    have hpost : (W (j + 1) w).st = M.make_grades_compatible_with_finalized
        (M.receipt_process S (W j w).st (Object.gfVote u)) :=
      Restated.Vocabulary.Proofs.NamedReceiptCallsBase.delivery_result facts S rho hdeliver (W j) (hW j).1
        (facts.nd.process_nonempty S (W j w) _ (fun _ h => by cases h)) (W (j + 1)) (hW j).2
    have hcoreEq : (M.receipt_process S (W j w).st (Object.gfVote u)).core =
        M.on_goldfish_vote (W j w).st.core u := by
      rw [facts.nd.process_gfVote, facts.hd.ns_with_core_core]
      exact facts.hd.on_goldfish_vote_checked_of_mem_committee S.E _ u hcommittee
    have hsettled :
        u ∈ (W (j + 1) w).st.core.gf_votes u.slot ∧
          ∃ c : Stamp, (W (j + 1) w).st.core.timestamp_vote u = some c ∧
            c ≤ ((W j w).st.core.t : Stamp) := by
      obtain ⟨hmem, c, hc, hle⟩ := Restated.Vocabulary.Protocol.mem_and_stamp_of_process facts
        (W j w).st.core u hstamps hfresh hfuture hequiv
      rw [hpost, facts.nd.make_grades_compatible_with_finalized_core_gf_votes,
        facts.nd.make_grades_compatible_with_finalized_core_timestamp_vote, hcoreEq]
      exact ⟨hmem, c, hc, hle⟩
    have hprele : (W j w).st.core.t ≤ t :=
      Restated.store_time_le_event_timeOn facts S Hs Xb hf hdeliver w
    refine ⟨j, _, hdeliver, ?_, ?_⟩
    · simpa only [Record.Event.time, Record.Event.time] using hdeadline
    · apply Or.inl
      rw [mem_beforeCutoff_iff]
      refine ⟨?_, ?_⟩
      · exact (facts.sto.mem_store_pool_iff _ _ _).2 hsettled.1
      · obtain ⟨c, hc, hle⟩ := hsettled.2
        exact stampedBefore_of_lt hc (lt_of_le_of_lt hle
          (WithBot.coe_lt_coe.mpr (lt_of_le_of_lt hprele hdeadline)))
  · obtain ⟨hblock, hnew, hcore, huindex⟩ := hcall
    have huB : u ∈ B.gf_votes := List.mem_of_getElem? huindex
    have huErase : u ∈ B.erase.gf_votes := by
      rwa [Proofs.NamedWire.erase_goldfish_votes]
    rcases hblock with
        ⟨t', hdeliver, hbefore⟩ | ⟨t', htick', ⟨out, hout, hWout, hBem⟩, hbefore⟩
    · have heq : Record.Event.deliver w (Object.block B) t' = e :=
        Option.some.inj (hdeliver.symm.trans he)
      have htt : t' = t := (congrArg Record.Event.time heq).trans htime
      subst t'
      subst hbefore
      have hpreBodies : B ∉ (W j w).st.bodies := by
        intro hB
        apply hnew
        have hcoh := (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho j w
          (W j) (hW j).1).1.1.1
        rw [hcoh.1]
        exact Finset.mem_image_of_mem NamedBlock.erase hB
      have hpostBodies := on_block_new_body₄₉ facts S (W j w).st B hnew hcore
      have hstamps : Restated.Vocabulary.Protocol.PoolStamps M (W j w).st.core :=
        Restated.poolStamps_stateBeforeOn facts S Hs Xb hf w j
      have hclock0 : M.vote_time S.E s ≤ (W j w).st.core.t := by
        refine Restated.tick_le_store_timeOn facts S Hs Xb hf hdeliver ?_ hlo
        exact hf.tick_total _ hgat w hwVote (Restated.Vocabulary.Proofs.Optimistic.publicTime_vote_time facts S s)
          (le_trans hlo (hf.in_horizon _ (List.mem_of_getElem? hdeliver)).2)
      have hclockUp : (W j w).st.core.t ≤ t :=
        Restated.store_time_le_event_timeOn facts S Hs Xb hf hdeliver w
      have hslot : (W j w).st.core.s = s := by
        have hsc := Restated.Vocabulary.Proofs.NamedStoreBridge.slotOfClock_stateBefore facts S rho j w
          (W j) (hW j).1
        unfold Restated.Vocabulary.Proofs.Optimistic.SlotOfClock at hsc
        rw [hsc]
        exact facts.sch.slotOf_of_between S.E s hclock0
          (lt_of_le_of_lt hclockUp hcut)
      have hfresh : ¬ u.slot < (W j w).st.core.s - 1 := by
        rw [hus, hslot]
        exact Nat.not_lt.mpr (Nat.sub_le s 1)
      have hfuture : ¬ (W j w).st.core.s < u.slot := by
        rw [hslot, hus]
        exact Nat.lt_irrefl s
      have hcommittee : u.val_index ∈ S.E.committee u.slot :=
        (hf.wire _ w (Object.block B) t hdeliver).1 B rfl |>.2.2 u huB
      have hlocal := Restated.Vocabulary.Proofs.Optimistic.block_carried_before_deadline_or_equivocates facts
        S (W j w).st B u Gamma hstamps hpreBodies hpostBodies huErase hcommittee
        hfresh hfuture (lt_of_le_of_lt hclockUp hdeadline)
      have hfinalEq : (W (j + 1) w).st = M.make_grades_compatible_with_finalized
          (M.on_block_with .alsoCarried S.E S.hc S.cfg (W j w).st B) := by
        rw [Restated.Vocabulary.Proofs.NamedReceiptCallsBase.delivery_result facts S rho hdeliver (W j) (hW j).1
            (hf.receipt_outcome _ _ _ _ hdeliver) (W (j + 1)) (hW j).2,
          facts.nd.process_block]
      have hpoolEq : M.store_pool (W (j + 1) w).st.core u.slot =
          M.store_pool (M.on_block_with .alsoCarried S.E S.hc S.cfg (W j w).st B).core u.slot := by
        rw [hfinalEq]
        exact congrFun (facts.nd.make_grades_compatible_with_finalized_core_pool _) u.slot
      have hstampEq : (W (j + 1) w).st.core.timestamp_vote =
          (M.on_block_with .alsoCarried S.E S.hc S.cfg (W j w).st B).core.timestamp_vote := by
        rw [hfinalEq, facts.nd.make_grades_compatible_with_finalized_core_timestamp_vote]
      refine ⟨j, _, he, ?_, ?_⟩
      · simpa only [htime] using hdeadline
      · rw [hpoolEq, hstampEq]
        exact hlocal
    · have heq : Record.Event.tick w t' = e := Option.some.inj (htick'.symm.trans he)
      have htt : t' = t := (congrArg Record.Event.time heq).trans htime
      subst t'
      subst hbefore
      obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc (W j w).st.core.toHealing t
        (W j w).cache
      have _hr_p := facts.ndRun.stateBeforeOf_reachedNode S rho j (W j) (hW j).1 w
      have _hv_p := facts.ndRun.stateBeforeOf_runs_as S rho j (W j) (hW j).1 w
      obtain ⟨D, hD⟩ := facts.dt.propose_block_with_nonempty S w (W j w) t out hout
        (facts.nd.block_mem_on_tick_emit S w (W j w) t out hout hBem).1.1
        (facts.nd.block_mem_on_tick_emit S w (W j w) t out hout hBem).1.2.1
        (facts.nd.block_mem_on_tick_emit S w (W j w) t out hout hBem).1.2.2
        (facts.nd.block_mem_on_tick_emit_awake S w (W j w) t out hout hBem) c hc
      have hproposal : D.2 = some B := by
        rw [Restated.Vocabulary.Proofs.NamedReceiptCallsBase.self_proposal_call facts S rho htick' (W j)
          (hW j).1 out hout hBem c hc D hD]
      obtain ⟨o, ho⟩ := facts.dt.proposal_with_nonempty (M.frameContract c) .poolAndCarried S.E S.hc
        (S.node w) (M.ns_setClock S.E (W j w).st t)
      have hgf' : B.gf_votes = (M.ns_setClock S.E (W j w).st t).core.gf_votes
          ((M.ns_setClock S.E (W j w).st t).core.s - 1) :=
        facts.dt.proposal_with_gf_votes _ .poolAndCarried S.E S.hc (S.node w) _ o ho
          (facts.dt.proposal_with_eq_of_propose_block_with_snd _ _ _ _ _ _ D hD hproposal o ho)
      have hslot : (M.ns_setClock S.E (W j w).st t).core.s = s := by
        rw [facts.hd.Sts_setClock_core_s]
        exact facts.sch.slotOf_of_between S.E s hlo hcut
      have hstamps : Restated.Vocabulary.Protocol.PoolStamps M (M.ns_setClock S.E (W j w).st t).core := by
        have hrawStamps := Restated.poolStamps_stateBeforeOn facts S Hs Xb hf w j
        have htle : (W j w).st.core.t ≤ t :=
          Restated.store_time_le_event_timeOn facts S Hs Xb hf htick' w
        exact poolStamps_setClock₄₉ facts S.E _ htle hrawStamps
      have huPool : u ∈ (M.ns_setClock S.E (W j w).st t).core.gf_votes
          ((M.ns_setClock S.E (W j w).st t).core.s - 1) := by
        rw [← hgf']
        exact List.mem_of_getElem? huindex
      have huslot := hstamps.slot _ u huPool
      have hbad : s = s - 1 := by simpa [hus, hslot] using huslot
      have hltNat : s - 1 < s := Nat.sub_lt (Nat.zero_lt_of_lt hs) (by decide)
      exact False.elim ((Nat.ne_of_lt hltNat) hbad.symm)

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

/-- Along the path `W` of the bundle, if `w`, in `Hs t`, actually handles the vote `u` of slot `s`
    at `t` with `proposal_time s ≤ t < view_freeze s` and `t < Gamma`, then for some event `i`
    before `Gamma`, `w`'s pool of slot `u.slot` in `W (i + 1)`, cut at `Gamma`, holds `u` or shows
    `u`'s author equivocating. -/
theorem actual_gfVote_settled_before_view_freezeOn_RecoveryOpeningFrontierRunBlock (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    {j : Nat} {w : V} {u : GoldfishVote V} {s : Slot} {t Gamma : Time}
    (hactual : Restated.Vocabulary.Execution.NamedRun.actualHandlesAt M S rho W j w (Object.gfVote u) t)
    (hus : u.slot = s) (hw : w ∈ Hs t) (hgat : lo ≤ M.proposal_time S.E s)
    (hlo : M.proposal_time S.E s ≤ t)
    (hhi : t < M.view_freeze S.E s) (hdeadline : t < Gamma) :
    ∃ i : Nat, ∃ e : Record.Event V, rho.events[i]? = some e ∧ e.time < Gamma ∧
      (u ∈ beforeCutoff
          (W (i + 1) w).st.core.timestamp_vote Gamma
          (M.store_pool (W (i + 1) w).st.core u.slot) ∨
        M.equivocates
          (beforeCutoff
            (W (i + 1) w).st.core.timestamp_vote Gamma
            (M.store_pool (W (i + 1) w).st.core u.slot))
          u.val_index = true) := by
  have _hr_0 : M.reachedNode (W j w) := facts.ndRun.stateBeforeOf_reachedNode S rho j (W j) (hf.onePath j).1 w
  have _hv_0 : M.runs_as (W j w) w := facts.ndRun.stateBeforeOf_runs_as S rho j (W j) (hf.onePath j).1 w
  have _hr_1 : M.reachedNode (W (j + 1) w) := facts.ndRun.stateBeforeOf_reachedNode S rho (j + 1) (W (j + 1)) (hf.onePath (j + 1)).1 w
  have _hv_1 : M.runs_as (W (j + 1) w) w := facts.ndRun.stateBeforeOf_runs_as S rho (j + 1) (W (j + 1)) (hf.onePath (j + 1)).1 w
  have hW := hf.onePath
  have hwProp : w ∈ Hs (M.proposal_time S.E s) := hHs _ _ hlo hw
  have hactual0 := hactual
  obtain ⟨hindex, e, he, hnode, htime⟩ := hactual
  rcases hindex with (⟨t', htick', out, hout, hWout, hem⟩ | ⟨t', hdeliver⟩) |
      ⟨B, jrow, before, hcall⟩
  · have heq : Record.Event.tick w t' = e := Option.some.inj (htick'.symm.trans he)
    have htt : t' = t := (congrArg Record.Event.time heq).trans htime
    subst t'
    have hemit : Restated.Vocabulary.Execution.NamedRun.emits M S rho W w (Object.gfVote u) t :=
      ⟨j, htick', out, hout, hWout, hem⟩
    obtain ⟨hs', ht', hval, hus'⟩ := Restated.Vocabulary.Proofs.Optimistic.emits_gfVote_shape facts S W hemit (fun i => facts.ndRun.stateBeforeOf_reachedNode S rho i (W i) (hf.onePath i).1 _) (fun i => facts.ndRun.stateBeforeOf_runs_as S rho i (W i) (hf.onePath i).1 _)
    have hslot : S.E.slotOf t = s := by rw [← hus', hus]
    have htVote : t = M.vote_time S.E s := by
      simpa only [hslot] using ht'
    have hcut : t < M.support_cutoff S.E s := by
      rw [htVote]
      exact vote_time_lt_support_cutoff₄₉ facts S s
    have hgatVote : lo ≤ M.vote_time S.E (S.E.slotOf t) := by
      rw [← ht']
      exact le_trans hgat hlo
    exact Restated.actual_gfVote_settled_before_deadlineOn_RecoveryOpeningFrontierRunBlock facts
      S Hs Xb hf hHs (s := S.E.slotOf t) hactual0 hs' hus'
      (by rw [hval]; exact hw) hw hgatVote (le_of_eq ht'.symm)
      (by simpa only [hslot] using hcut) hdeadline
  · have heq : Record.Event.deliver w (Object.gfVote u) t' = e :=
      Option.some.inj (hdeliver.symm.trans he)
    have htt : t' = t := (congrArg Record.Event.time heq).trans htime
    subst t'
    have hslot : (W j w).st.core.s = s :=
      Restated.delivery_store_slot_before_freezeOn facts S Hs Xb hf hwProp hgat hdeliver hlo hhi
    have hcommittee : u.val_index ∈ S.E.committee u.slot :=
      (hf.wire j w (Object.gfVote u) t hdeliver).2 u rfl
    have hstamps := Restated.poolStamps_stateBeforeOn facts S Hs Xb hf w j
    have hfresh : ¬ u.slot < (W j w).st.core.s - 1 := by
      rw [hslot, hus]
      exact Nat.not_lt.mpr (Nat.sub_le s 1)
    have hfuture : ¬ (W j w).st.core.s < u.slot := by
      rw [hslot, hus]
      exact Nat.lt_irrefl s
    have hclock : (W j w).st.core.t < Gamma :=
      lt_of_le_of_lt (Restated.store_time_le_event_timeOn facts S Hs Xb hf hdeliver w) hdeadline
    have hlocal := Restated.Vocabulary.Protocol.on_goldfish_vote_checked_beforeCutoff_or_equivocates facts
      S.E (W j w).st.core u Gamma hcommittee hstamps
      hfresh hfuture hclock
    have hpost : (W (j + 1) w).st = M.make_grades_compatible_with_finalized
        (M.receipt_process S (W j w).st (Object.gfVote u)) :=
      Restated.Vocabulary.Proofs.NamedReceiptCallsBase.delivery_result facts S rho hdeliver (W j) (hW j).1
        (facts.nd.process_nonempty S (W j w) _ (fun _ h => by cases h)) (W (j + 1)) (hW j).2
    have hcoreEq : (M.receipt_process S (W j w).st (Object.gfVote u)).core =
        M.on_goldfish_vote_checked S.E (W j w).st.core u := by
      rw [facts.nd.process_gfVote, facts.hd.ns_with_core_core]
    have hpoolEq : M.store_pool (W (j + 1) w).st.core u.slot =
        M.store_pool (M.on_goldfish_vote_checked S.E (W j w).st.core u) u.slot := by
      rw [hpost, ← hcoreEq]
      exact congrFun (facts.nd.make_grades_compatible_with_finalized_core_pool _) u.slot
    have hstampEq : (W (j + 1) w).st.core.timestamp_vote =
        (M.on_goldfish_vote_checked S.E (W j w).st.core u).timestamp_vote := by
      rw [hpost, facts.nd.make_grades_compatible_with_finalized_core_timestamp_vote, hcoreEq]
    refine ⟨j, _, hdeliver, ?_, ?_⟩
    · simpa only [Record.Event.time, Record.Event.time] using hdeadline
    · rw [hpoolEq, hstampEq]
      exact hlocal
  · obtain ⟨hblock, hnew, hcore, huindex⟩ := hcall
    have huB : u ∈ B.gf_votes := List.mem_of_getElem? huindex
    have huErase : u ∈ B.erase.gf_votes := by
      rwa [Proofs.NamedWire.erase_goldfish_votes]
    rcases hblock with
        ⟨t', hdeliver, hbefore⟩ | ⟨t', htick', ⟨out, hout, hWout, hBem⟩, hbefore⟩
    · have heq : Record.Event.deliver w (Object.block B) t' = e :=
        Option.some.inj (hdeliver.symm.trans he)
      have htt : t' = t := (congrArg Record.Event.time heq).trans htime
      subst t'
      subst hbefore
      have hpreBodies : B ∉ (W j w).st.bodies := by
        intro hB
        apply hnew
        have hcoh := (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho j w
          (W j) (hW j).1).1.1.1
        rw [hcoh.1]
        exact Finset.mem_image_of_mem NamedBlock.erase hB
      have hpostBodies := on_block_new_body₄₉ facts S (W j w).st B hnew hcore
      have hstamps : Restated.Vocabulary.Protocol.PoolStamps M (W j w).st.core :=
        Restated.poolStamps_stateBeforeOn facts S Hs Xb hf w j
      have hslot : (W j w).st.core.s = s :=
        Restated.delivery_store_slot_before_freezeOn facts S Hs Xb hf hwProp hgat hdeliver hlo hhi
      have hfresh : ¬ u.slot < (W j w).st.core.s - 1 := by
        rw [hus, hslot]
        exact Nat.not_lt.mpr (Nat.sub_le s 1)
      have hfuture : ¬ (W j w).st.core.s < u.slot := by
        rw [hslot, hus]
        exact Nat.lt_irrefl s
      have hcommittee : u.val_index ∈ S.E.committee u.slot :=
        (hf.wire _ w (Object.block B) t hdeliver).1 B rfl |>.2.2 u huB
      have hclock : (W j w).st.core.t < Gamma :=
        lt_of_le_of_lt (Restated.store_time_le_event_timeOn facts S Hs Xb hf hdeliver w) hdeadline
      have hlocal := Restated.Vocabulary.Proofs.Optimistic.block_carried_before_deadline_or_equivocates facts
        S (W j w).st B u Gamma hstamps hpreBodies hpostBodies huErase hcommittee
        hfresh hfuture hclock
      have hfinalEq : (W (j + 1) w).st = M.make_grades_compatible_with_finalized
          (M.on_block_with .alsoCarried S.E S.hc S.cfg (W j w).st B) := by
        rw [Restated.Vocabulary.Proofs.NamedReceiptCallsBase.delivery_result facts S rho hdeliver (W j) (hW j).1
            (hf.receipt_outcome _ _ _ _ hdeliver) (W (j + 1)) (hW j).2,
          facts.nd.process_block]
      have hpoolEq : M.store_pool (W (j + 1) w).st.core u.slot =
          M.store_pool (M.on_block_with .alsoCarried S.E S.hc S.cfg (W j w).st B).core u.slot := by
        rw [hfinalEq]
        exact congrFun (facts.nd.make_grades_compatible_with_finalized_core_pool _) u.slot
      have hstampEq : (W (j + 1) w).st.core.timestamp_vote =
          (M.on_block_with .alsoCarried S.E S.hc S.cfg (W j w).st B).core.timestamp_vote := by
        rw [hfinalEq, facts.nd.make_grades_compatible_with_finalized_core_timestamp_vote]
      refine ⟨j, _, he, ?_, ?_⟩
      · simpa only [htime] using hdeadline
      · rw [hpoolEq, hstampEq]
        exact hlocal
    · have heq : Record.Event.tick w t' = e := Option.some.inj (htick'.symm.trans he)
      have htt : t' = t := (congrArg Record.Event.time heq).trans htime
      subst t'
      subst hbefore
      obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc (W j w).st.core.toHealing t
        (W j w).cache
      have _hr_p := facts.ndRun.stateBeforeOf_reachedNode S rho j (W j) (hW j).1 w
      have _hv_p := facts.ndRun.stateBeforeOf_runs_as S rho j (W j) (hW j).1 w
      obtain ⟨D, hD⟩ := facts.dt.propose_block_with_nonempty S w (W j w) t out hout
        (facts.nd.block_mem_on_tick_emit S w (W j w) t out hout hBem).1.1
        (facts.nd.block_mem_on_tick_emit S w (W j w) t out hout hBem).1.2.1
        (facts.nd.block_mem_on_tick_emit S w (W j w) t out hout hBem).1.2.2
        (facts.nd.block_mem_on_tick_emit_awake S w (W j w) t out hout hBem) c hc
      have hcallEq := Restated.Vocabulary.Proofs.NamedReceiptCallsBase.self_proposal_call facts S rho htick'
        (W j) (hW j).1 out hout hBem c hc D hD
      have hproposal : D.2 = some B := by rw [hcallEq]
      have hshape := Restated.Vocabulary.Proofs.HealingSurface.block_mem_on_tick_emit facts S w
        (W j w) t out hout hBem
      have hguard := hshape.1
      obtain ⟨o, ho⟩ := facts.dt.proposal_with_nonempty (M.frameContract c) .poolAndCarried S.E S.hc
        (S.node w) (M.ns_setClock S.E (W j w).st t)
      have hgf : B.gf_votes = (M.ns_setClock S.E (W j w).st t).core.gf_votes
          ((M.ns_setClock S.E (W j w).st t).core.s - 1) :=
        facts.dt.proposal_with_gf_votes _ .poolAndCarried S.E S.hc (S.node w) _ o ho
          (facts.dt.proposal_with_eq_of_propose_block_with_snd _ _ _ _ _ _ D hD hproposal o ho)
      have htle : (W j w).st.core.t ≤ t :=
        Restated.store_time_le_event_timeOn facts S Hs Xb hf htick' w
      have hstamps : Restated.Vocabulary.Protocol.PoolStamps M (M.ns_setClock S.E (W j w).st t).core :=
        poolStamps_setClock₄₉ facts S.E _ htle (Restated.poolStamps_stateBeforeOn facts S Hs Xb hf w j)
      have huPool : u ∈ (M.ns_setClock S.E (W j w).st t).core.gf_votes
          ((M.ns_setClock S.E (W j w).st t).core.s - 1) := by
        rw [← hgf]
        exact List.mem_of_getElem? huindex
      have hslot : (M.ns_setClock S.E (W j w).st t).core.s = s + 1 := by
        have hslotTime : (M.ns_setClock S.E (W j w).st t).core.s = S.E.slotOf t :=
          facts.hd.Sts_setClock_core_s _ _ _
        have hspos : 0 < (M.ns_setClock S.E (W j w).st t).core.s := by
          rw [hslotTime]
          exact hguard.1
        have hs' : s = (M.ns_setClock S.E (W j w).st t).core.s - 1 := by
          simpa only [hus] using hstamps.slot _ u huPool
        calc
          (M.ns_setClock S.E (W j w).st t).core.s
              = ((M.ns_setClock S.E (W j w).st t).core.s - 1) + 1 :=
            (Nat.sub_add_cancel (Nat.succ_le_of_lt hspos)).symm
          _ = s + 1 := by rw [← hs']
      have hcommittee : u.val_index ∈ S.E.committee u.slot := by
        have huPool' : u ∈ (W j w).st.core.gf_votes
            ((M.ns_setClock S.E (W j w).st t).core.s - 1) := by
          rw [← facts.hd.setClock_core_gf_votes S.E _ t]
          exact huPool
        have hcommittee' := Restated.Vocabulary.Protocol.CommitteePools.stateBefore facts S rho w j
          (W j) (hW j).1 _ u huPool'
        have hs' := hstamps.slot _ u huPool
        simpa only [hs'] using hcommittee'
      have hfresh : ¬ u.slot < (M.ns_setClock S.E (W j w).st t).core.s - 1 := by
        rw [hus, hslot]
        rw [Nat.add_sub_cancel]
        exact Nat.lt_irrefl s
      have hfuture : ¬ (M.ns_setClock S.E (W j w).st t).core.s < u.slot := by
        rw [hslot, hus]
        exact Nat.not_lt.mpr (Nat.le_add_right s 1)
      have hclock : (M.ns_setClock S.E (W j w).st t).core.t < Gamma := by
        rw [facts.hd.Sts_setClock_core_t]
        exact hdeadline
      have hpostBodies := on_block_new_body₄₉ facts S _ B hnew hcore
      have hlocal := Restated.Vocabulary.Proofs.Optimistic.block_carried_before_deadline_or_equivocates facts
        S (M.ns_setClock S.E (W j w).st t) B u Gamma hstamps (by
          intro hB
          apply hnew
          have hcoh := (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho j w
            (W j) (hW j).1).1.1.1
          rw [facts.hd.Sts_setClock_bodies] at hB
          rw [facts.hd.Sts_setClock_core_T, hcoh.1]
          exact Finset.mem_image_of_mem NamedBlock.erase hB) hpostBodies huErase
        hcommittee hfresh hfuture hclock
      let final := M.on_block_with .alsoCarried S.E S.hc S.cfg (M.ns_setClock S.E (W j w).st t) B
      have hfinalFields :
          (W (j + 1) w).st.core.gf_votes = final.core.gf_votes ∧
          (W (j + 1) w).st.core.timestamp_vote = final.core.timestamp_vote := by
        have hguard' : 0 < S.E.slotOf t ∧
            t = M.proposal_time S.E (S.E.slotOf t) ∧
            S.E.proposer (S.E.slotOf t) = (S.node w).val_index := by
          simpa only [S.node_val_index] using hguard
        have hfields := Restated.Vocabulary.Proofs.Optimistic.tick_fields_from_proposal facts S w
          (W j w) t out hout hguard'
          (facts.nd.block_mem_on_tick_emit_awake S w (W j w) t out hout hBem) c hc D hD
        rw [hcallEq] at hfields
        simp only [facts.nd.store_with_cache_core_gf_votes,
          facts.nd.store_with_cache_core_timestamp_vote] at hfields
        rw [hWout]
        exact hfields
      refine ⟨j, _, he, ?_, ?_⟩
      · simpa only [htime] using hdeadline
      · have hpoolEq : ∀ k : Slot,
            (M.store_pool (W (j + 1) w).st.core k) = (M.store_pool final.core k) := by
          intro k
          ext x
          rw [facts.sto.mem_store_pool_iff, facts.sto.mem_store_pool_iff, hfinalFields.1]
        rw [hpoolEq, hfinalFields.2]
        exact hlocal

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

/-- Along the path `W` of the bundle, if `lo ≤ proposal_time s`, `w ∈ Hs t` actually handles the
    vote `u` of slot `s` at `t` with `proposal_time s ≤ t < view_freeze s`, and `view_freeze s` is
    inside the horizon, then `w`'s slot-`(s + 1)` vote-duty store, cut at `view_freeze s`, holds `u`
    in its pool of `s` or shows `u`'s author equivocating there. -/
theorem gfVote_processes_settled_at_voteDuty_after_gstOn_RecoveryOpeningFrontierRunBlock (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    {w : V} {u : GoldfishVote V} {s : Slot} {t : Time} {j : Nat}
    (hpost : lo ≤ M.proposal_time S.E s)
    (hproc : Restated.Vocabulary.Execution.NamedRun.actualHandlesAt M S rho W j w (Object.gfVote u) t)
    (hw : w ∈ Hs t)
    (hus : u.slot = s)
    (hlo : M.proposal_time S.E s ≤ t)
    (hhi : t < M.view_freeze S.E s)
    (_hhor : M.view_freeze S.E s ≤ rho.horizon) :
    u ∈ beforeCutoff
          (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
            (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1)).timestamp_vote
          (M.view_freeze S.E s)
          (M.store_pool (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
            (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1)) s) ∨
      M.equivocates
        (beforeCutoff
          (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
            (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1)).timestamp_vote
          (M.view_freeze S.E s)
          (M.store_pool (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
            (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1)) s))
        u.val_index = true := by
  obtain ⟨i, e, he, htime, hsettled⟩ :=
    Restated.actual_gfVote_settled_before_view_freezeOn_RecoveryOpeningFrontierRunBlock facts S Hs Xb hf
      hHs hproc hus hw hpost hlo hhi hhi
  let Gamma := M.vote_time S.E (s + 1)
  let N := strictEventIndex rho Gamma
  have hiN : i < N := by
    by_contra hnot
    have hNle : N ≤ i := Nat.le_of_not_gt hnot
    have hGammae : Gamma ≤ e.time :=
      Restated.le_time_of_index_geOn facts S Hs Xb hf
        (t := Gamma) (j := i) (e := e) hNle he
    have hfreezeSucc : M.view_freeze S.E s < Gamma :=
      facts.sch.view_freeze_lt_vote_time_succ S.E s
    exact (not_le_of_gt (lt_trans htime hfreezeSucc)) hGammae
  have hcarry : Restated.Vocabulary.Protocol.PoolCarry M (W (i + 1) w).st.core (W N w).st.core :=
    Restated.pool_carryOn facts S Hs Xb hf w N (Nat.succ_le_of_lt hiN)
  have hpoolN : M.store_pool (Restated.Vocabulary.Proofs.Optimistic.voteStore M S (W N w).st.core (s + 1)) s =
      M.store_pool (W N w).st.core s :=
    facts.sto.pool_set_clock_slot _ _ _ s
  have htsN : (Restated.Vocabulary.Proofs.Optimistic.voteStore M S (W N w).st.core (s + 1)).timestamp_vote =
      (W N w).st.core.timestamp_vote :=
    facts.sto.store_with_t_s_timestamp_vote _ _ _
  show u ∈ beforeCutoff
        (Restated.Vocabulary.Proofs.Optimistic.voteStore M S (W N w).st.core (s + 1)).timestamp_vote
        (M.view_freeze S.E s)
        (M.store_pool (Restated.Vocabulary.Proofs.Optimistic.voteStore M S (W N w).st.core (s + 1)) s) ∨
      M.equivocates
        (beforeCutoff
          (Restated.Vocabulary.Proofs.Optimistic.voteStore M S (W N w).st.core (s + 1)).timestamp_vote
          (M.view_freeze S.E s)
          (M.store_pool (Restated.Vocabulary.Proofs.Optimistic.voteStore M S (W N w).st.core (s + 1)) s))
        u.val_index = true
  rw [hpoolN, htsN]
  rw [hus] at hsettled
  rcases hsettled with hmem | hequiv
  · exact Or.inl (beforeCutoff_subset_of_poolCarry₄₉ facts hcarry s (M.view_freeze S.E s) u hmem)
  · apply Or.inr
    apply facts.sch.equivocates_mono _ u.val_index hequiv
    intro x hx
    exact beforeCutoff_subset_of_poolCarry₄₉ facts hcarry s (M.view_freeze S.E s) x hx

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

/-- Along the path `W` of the bundle, if `lo ≤ proposal_time s`, `v ∈ Hs t` accepts the vote `u` of
    slot `s` at `t` with `proposal_time s ≤ t < support_cutoff s`, `w ∈ Hs (t + Δ)`, and
    `view_freeze s` is inside the horizon, then `w`'s slot-`(s + 1)` vote-duty store, cut at
    `view_freeze s`, holds `u` in its pool of `s` or shows `u`'s author equivocating there. -/
theorem accepted_gfVote_forward_settled_at_voteDuty_after_gstOn_RecoveryOpeningFrontierRunBlock (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    {v w : V} {i : Nat} {u : GoldfishVote V} {s : Slot} {t : Time}
    (hpost : lo ≤ M.proposal_time S.E s)
    (hacc : Restated.Vocabulary.Execution.NamedRun.acceptsAt M S rho W i v (Object.gfVote u) t)
    (hv : v ∈ Hs t) (hw : w ∈ Hs (t + S.E.Δ))
    (hus : u.slot = s)
    (hlo : M.proposal_time S.E s ≤ t)
    (hhi : t < M.support_cutoff S.E s)
    (hhor : M.view_freeze S.E s ≤ rho.horizon) :
    u ∈ beforeCutoff
          (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
            (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1)).timestamp_vote
          (M.view_freeze S.E s)
          (M.store_pool (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
            (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1)) s) ∨
      M.equivocates
        (beforeCutoff
          (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
            (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1)).timestamp_vote
          (M.view_freeze S.E s)
          (M.store_pool (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
            (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1)) s))
        u.val_index = true := by
  have hfreeze : t + S.E.Δ < M.view_freeze S.E s :=
    lt_of_lt_of_le (Int.add_lt_add_right hhi S.E.Δ) (support_cutoff_add_delta_le_view_freeze₄₉ facts S s)
  by_cases halready : Restated.Vocabulary.Execution.Object.processed M
      (W (i + 1) w).st (Object.gfVote u) = true
  · obtain ⟨e, he, -, het⟩ := hacc.1.2
    apply Or.inl
    apply Restated.gfVote_processed_after_event_at_voteDutyOn facts S Hs Xb hf he hus halready
    simpa only [het] using
      lt_trans hhi (facts.sch.Optimistic_support_cutoff_lt_view_freeze S.E s)
  · have hunaccepted : Restated.Vocabulary.Execution.Object.processed M (W (i + 1) w).st
        (Object.gfVote u) = false :=
      Bool.eq_false_of_not_eq_true halready
    have hrelayHor : t + S.E.Δ ≤ rho.horizon := le_trans (le_of_lt hfreeze) hhor
    have hpostAcceptance : lo ≤ t := le_trans hpost hlo
    obtain ⟨t', hcausal, hdeadline, j, hproc⟩ :=
      Restated.relay_gf_vote_after_gstOn facts S Hs Xb hf hv hw hpostAcceptance hacc
        hunaccepted hrelayHor
    have hbeforeFreeze : t' < M.view_freeze S.E s := lt_trans hdeadline hfreeze
    exact Restated.gfVote_processes_settled_at_voteDuty_after_gstOn_RecoveryOpeningFrontierRunBlock facts
      S Hs Xb hf hHs hpost hproc (hHs _ _ (le_of_lt hdeadline) hw) hus
      (le_trans hlo hcausal) hbeforeFreeze hhor

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

/-- Along the path `W` of the bundle, if `lo ≤ proposal_time s`, `v` and `w` are in
    `Hs (confirmation_time s)` and that instant is inside the horizon, then for every outcome `X` of
    `v`'s confirmation votes of `s`, each vote `u` of `X` is in `w`'s late confirmation set of `s`
    or shows `u`'s author equivocating there. -/
theorem confVote_transfer_after_gstOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    {v w : V} {s : Slot}
    (hv : v ∈ Hs (M.confirmation_time S.E s))
    (hw : w ∈ Hs (M.confirmation_time S.E s))
    (hpost : lo ≤ M.proposal_time S.E s)
    (hhor : M.confirmation_time S.E s ≤ rho.horizon) :
    ∀ X, Restated.Vocabulary.Protocol.confVotes M S.E
        (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
          (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core (M.confirmation_time S.E s)) s ⇢ X →
    ∀ u ∈ X,
      u ∈ Restated.Vocabulary.Protocol.confLate M S.E
          (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
            (W (strictEventIndex rho (M.confirmation_time S.E s)) w).st.core (M.confirmation_time S.E s)) s ∨
        M.equivocates
          (Restated.Vocabulary.Protocol.confLate M S.E
            (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
              (W (strictEventIndex rho (M.confirmation_time S.E s)) w).st.core (M.confirmation_time S.E s)) s)
          u.val_index = true := by
  intro X hX u hu
  have hvote : M.proposal_time S.E s < M.vote_time S.E s :=
    facts.sch.proposal_time_lt_vote_time S.E s
  have hcut : M.vote_time S.E s < M.support_cutoff S.E s := vote_time_lt_support_cutoff₄₉ facts S s
  have hcutConf : M.support_cutoff S.E s < M.confirmation_time S.E s :=
    lt_trans (facts.sch.Optimistic_support_cutoff_lt_view_freeze S.E s)
      (facts.sch.view_freeze_lt_confirmation_time S.E s)
  obtain ⟨i, t, hacc, hus, hlo, hhi⟩ :=
    Restated.confirmationVotesAcceptedInWindow_of_admissibleOn facts S Hs Xb hf s
      (hHs _ _ (le_of_lt hcutConf) hv) (le_trans hpost (le_of_lt (hvote.trans hcut))) X hX u hu
  have hfreezeHor : M.view_freeze S.E s ≤ rho.horizon :=
    le_trans (le_of_lt (facts.sch.view_freeze_lt_confirmation_time S.E s)) hhor
  have htΔ : t + S.E.Δ ≤ M.confirmation_time S.E s :=
    le_of_lt (lt_trans (Int.add_lt_add_right hhi S.E.Δ) (support_cutoff_add_delta_lt_confirmation₄₉ facts S s))
  have hvt : v ∈ Hs t := hHs _ _ (le_of_lt (lt_trans hhi hcutConf)) hv
  have hwt : w ∈ Hs (t + S.E.Δ) := hHs _ _ htΔ hw
  have hsettled :=
    Restated.accepted_gfVote_forward_settled_at_voteDuty_after_gstOn_RecoveryOpeningFrontierRunBlock facts
      S Hs Xb hf hHs hpost hacc hvt hwt hus hlo hhi hfreezeHor
  have hsub := Restated.voteDutyFrozen_subset_confLateOn facts S Hs Xb hf w s
  rcases hsettled with hmem | hequiv
  · exact Or.inl (hsub hmem)
  · exact Or.inr (facts.sch.equivocates_mono hsub u.val_index hequiv)

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

/-- Along the path `W` of the bundle, if `lo ≤ proposal_time s`, `v` and `w` are in
    `Hs (confirmation_time s)` and that instant is inside the horizon, then every outcome of `v`'s
    confirmation votes of `s` crosses into `w`'s tree and late set of `s`, and every outcome of
    `w`'s into `v`'s. -/
theorem opening_frontier_crossViews_confStore_after_gstOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {v w : V} {s : Slot}
    (hv : v ∈ Hs (M.confirmation_time S.E s))
    (hw : w ∈ Hs (M.confirmation_time S.E s))
    (hpost : lo ≤ M.proposal_time S.E s)
    (hhor : M.confirmation_time S.E s ≤ rho.horizon) :
    (∀ X, Restated.Vocabulary.Protocol.confVotes M S.E
          (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
            (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core (M.confirmation_time S.E s)) s ⇢ X →
      Restated.Vocabulary.Protocol.CrossView M
        (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
          (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core (M.confirmation_time S.E s)).T
        (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
          (W (strictEventIndex rho (M.confirmation_time S.E s)) w).st.core (M.confirmation_time S.E s)).T
        X
        (Restated.Vocabulary.Protocol.confLate M S.E
          (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
            (W (strictEventIndex rho (M.confirmation_time S.E s)) w).st.core (M.confirmation_time S.E s)) s)) ∧
    (∀ Y, Restated.Vocabulary.Protocol.confVotes M S.E
          (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
            (W (strictEventIndex rho (M.confirmation_time S.E s)) w).st.core (M.confirmation_time S.E s)) s ⇢ Y →
      Restated.Vocabulary.Protocol.CrossView M
        (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
          (W (strictEventIndex rho (M.confirmation_time S.E s)) w).st.core (M.confirmation_time S.E s)).T
        (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
          (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core (M.confirmation_time S.E s)).T
        Y
        (Restated.Vocabulary.Protocol.confLate M S.E
          (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
            (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core (M.confirmation_time S.E s)) s)) := by
  have hW := hf.onePath
  have hvX : v ∈ Xb := hHsXb _ hv
  have hwX : w ∈ Xb := hHsXb _ hw
  have hmono := priv% Proofs.Vocabulary.Protocol.Schedule.RecoveryOpeningFrontierRunBlock
    DecoupledConsensusModel.Protocol.recovery_rootInjectiveBelow_mono
  have hinj : ∀ (x y : V), x ∈ Xb → y ∈ Xb →
      RootInjectiveBelow ((W (strictEventIndex rho (M.confirmation_time S.E s)) x).st.core.T ∪
        (W (strictEventIndex rho (M.confirmation_time S.E s)) y).st.core.T) := by
    intro x y hx hy
    have hri := Restated.rootInjectiveBelow_stateBefore_unionOn facts S W Xb hf.rootCollisionFree hx hy
      (strictEventIndex rho (M.confirmation_time S.E s)) (strictEventIndex rho (M.confirmation_time S.E s))
    refine hmono (Finset.subset_iff.mpr fun B hB => ?_) hri
    rcases Finset.mem_union.mp hB with hB | hB
    · obtain ⟨D, hD, hDe⟩ :=
        Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore facts S rho _ x
          (W _) (hW _).1 hB
      exact Finset.mem_image.mpr ⟨D, Finset.mem_union_left _ hD, hDe⟩
    · obtain ⟨D, hD, hDe⟩ :=
        Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore facts S rho _ y
          (W _) (hW _).1 hB
      exact Finset.mem_image.mpr ⟨D, Finset.mem_union_right _ hD, hDe⟩
  rw [tickStore_T₄₉ facts, tickStore_T₄₉ facts]
  exact ⟨fun X hX => crossView_of_rootInjective₄₉
      (Restated.confVote_transfer_after_gstOn facts S Hs Xb hf hHs hv hw hpost hhor X hX)
      (hinj _ _ hvX hwX),
    fun Y hY => crossView_of_rootInjective₄₉
      (Restated.confVote_transfer_after_gstOn facts S Hs Xb hf hHs hw hv hpost hhor Y hY)
      (hinj _ _ hwX hvX)⟩

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

/-- If event `j` is `f`, every event at an index `k < j + 1` happens no later than `f`. -/
theorem time_le_of_index_lt_succ_eventOn (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {j : Nat} {f : Record.Event V} (hj : rho.events[j]? = some f) :
    ∀ (k : Nat) (e : Record.Event V), k < j + 1 → rho.events[k]? = some e → e.time ≤ f.time := by
  intro k e hk he
  rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | heq
  · exact Restated.time_le_of_index_lt_eventOn facts S Hs Xb hf hj k e hlt he
  · subst heq
    rw [hj] at he
    cases he
    exact le_refl _

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

/-- The vote instant of a slot is before its support cutoff. -/
theorem vote_time_lt_support_cutoff_l49 (facts : Record.Facts M) (S : Setup V) (s : Slot) :
    M.vote_time S.E s < M.support_cutoff S.E s :=
  vote_time_lt_support_cutoff₄₉ facts S s

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

/-- Along the path `W` of the bundle, if `lo ≤ vote_time s`, `v` emits the vote `u` of slot `s > 0`
    at `vote_time s`, `v` and `w` are in `Hs (support_cutoff s)`, and `support_cutoff s` is inside
    the horizon, then for some event `j` before `support_cutoff s`, `w`'s pool of `s` in `W (j + 1)`
    holds `u` with a stamp before `support_cutoff s`. -/
theorem canonicalSuffixGfVotePooledBeforeFreeze_coreOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    {v : V} {s : Slot} (hv : v ∈ Hs (M.support_cutoff S.E s)) (hs : 0 < s)
    {u : GoldfishVote V}
    (hpost : lo ≤ M.vote_time S.E s)
    (hemit : Restated.Vocabulary.Execution.NamedRun.emits M S rho W v (Object.gfVote u)
      (M.vote_time S.E s))
    (hus : u.slot = s) {w : V} (hw : w ∈ Hs (M.support_cutoff S.E s))
    (hhor : M.support_cutoff S.E s ≤ rho.horizon) :
    ∃ (j : Nat) (e : Record.Event V), rho.events[j]? = some e ∧
      e.time < M.support_cutoff S.E s ∧
      u ∈ (W (j + 1) w).st.core.gf_votes s ∧
      ∃ c : Stamp,
        (W (j + 1) w).st.core.timestamp_vote u = some c ∧
          c < (M.support_cutoff S.E s : Stamp) := by
  have hW := hf.onePath
  have hvtCut := le_of_lt (vote_time_lt_support_cutoff₄₉ facts S s)
  have hvdCut := vote_time_add_delta_le_support_cutoff₄₉ facts S s
  obtain ⟨-, -, hvalv, -⟩ := Restated.Vocabulary.Proofs.Optimistic.emits_gfVote_shape facts S W hemit (fun i => facts.ndRun.stateBeforeOf_reachedNode S rho i (W i) (hf.onePath i).1 _) (fun i => facts.ndRun.stateBeforeOf_runs_as S rho i (W i) (hf.onePath i).1 _)
  have hval : u.val_index ∈ Hs (M.support_cutoff S.E s) := by rw [hvalv]; exact hv
  have hvVote : v ∈ Hs (M.vote_time S.E s) := hHs _ _ hvtCut hv
  have hwVote : w ∈ Hs (M.vote_time S.E s) := hHs _ _ hvtCut hw
  obtain ⟨t', hloRelay, hlt0, hactual⟩ :=
    Restated.broadcast_after_gstOn facts S Hs Xb hf hvVote
      (hHs _ _ hvdCut hw) hpost hemit
      (le_trans hvdCut hhor) (fun B hB => by cases hB)
  have hlt : t' < M.support_cutoff S.E s := lt_of_lt_of_le hlt0 hvdCut
  have hvalt' : u.val_index ∈ Hs t' := hHs _ _ (le_of_lt hlt) hval
  obtain ⟨j, hactual⟩ := hactual
  obtain ⟨hindex, e, he, hnode, htime⟩ := hactual
  rcases hindex with
      (⟨t'', htick', out, hout, hWout, hem⟩ | ⟨t'', hdeliver⟩) |
        ⟨B, j', before, hcall⟩
  · have heq : Record.Event.tick w t'' = e := Option.some.inj (htick'.symm.trans he)
    have htt : t'' = t' := (congrArg Record.Event.time heq).trans htime
    subst t''
    have hemit' : Restated.Vocabulary.Execution.NamedRun.emits M S rho W w (Object.gfVote u) t' :=
      ⟨j, htick', out, hout, hWout, hem⟩
    obtain ⟨hs', ht', -, hus'⟩ := Restated.Vocabulary.Proofs.Optimistic.emits_gfVote_shape facts S W hemit' (fun i => facts.ndRun.stateBeforeOf_reachedNode S rho i (W i) (hf.onePath i).1 _) (fun i => facts.ndRun.stateBeforeOf_runs_as S rho i (W i) (hf.onePath i).1 _)
    have hslot : S.E.slotOf t' = s := by rw [← hus', hus]
    have ht'vote : t' = M.vote_time S.E s := by
      simpa only [hslot] using ht'
    have hemitVote : Restated.Vocabulary.Execution.NamedRun.emits M S rho W w (Object.gfVote u)
        (M.vote_time S.E s) := by
      simpa only [ht'vote] using hemit'
    obtain ⟨i, hi, hmem, c, hc, hle⟩ :=
      Restated.mem_pool_of_emits_coreOn facts S Hs Xb hf hHs hs hemitVote hus (hHs _ _ hvtCut hval)
    refine ⟨i, _, hi, ?_, hmem, c, hc, ?_⟩
    · simpa only [ht'vote, Record.Event.time] using hlt
    · exact lt_of_le_of_lt hle (WithBot.coe_lt_coe.mpr (vote_time_lt_support_cutoff₄₉ facts S s))
  · have heq : Record.Event.deliver w (Object.gfVote u) t'' = e :=
      Option.some.inj (hdeliver.symm.trans he)
    have htt : t'' = t' := (congrArg Record.Event.time heq).trans htime
    subst t''
    have hlo : M.vote_time S.E s ≤ t' := hloRelay
    have hslot : (W j w).st.core.s = s :=
      Restated.delivery_store_slot_coreOn facts S Hs Xb hf hwVote hpost hdeliver hlo hlt
    have hcommittee : u.val_index ∈ S.E.committee u.slot :=
      (hf.wire j w (Object.gfVote u) t' hdeliver).2 u rfl
    have hstamps := Restated.poolStamps_stateBeforeOn facts S Hs Xb hf w j
    have hfresh : ¬ u.slot < (W j w).st.core.s - 1 := by
      rw [hslot, hus]
      exact Nat.not_lt.mpr (Nat.sub_le s 1)
    have hfuture : ¬ (W j w).st.core.s < u.slot := by
      rw [hslot, hus]
      exact Nat.lt_irrefl s
    have hequiv := Restated.pool_no_honest_equivocation_of_coreOn facts S Hs Xb hf hHs w j (T := t')
      (fun k e' hk he' => by
        simpa only [Record.Event.time, Record.Event.time] using
          Restated.time_le_of_index_lt_eventOn facts S Hs Xb hf hdeliver k e' hk he')
      u.slot hvalt'
    obtain ⟨hmem, c, hc, hle⟩ := Restated.Vocabulary.Protocol.mem_and_stamp_of_process facts
      (W j w).st.core u hstamps hfresh hfuture hequiv
    have hpost : (W (j + 1) w).st = M.make_grades_compatible_with_finalized
        (M.receipt_process S (W j w).st (Object.gfVote u)) :=
      Restated.Vocabulary.Proofs.NamedReceiptCallsBase.delivery_result facts S rho hdeliver (W j) (hW j).1
        (facts.nd.process_nonempty S (W j w) _ (fun _ h => by cases h)) (W (j + 1)) (hW j).2
    have hcoreEq : (M.receipt_process S (W j w).st (Object.gfVote u)).core =
        M.on_goldfish_vote (W j w).st.core u := by
      rw [facts.nd.process_gfVote, facts.hd.ns_with_core_core]
      exact facts.hd.on_goldfish_vote_checked_of_mem_committee S.E _ u hcommittee
    refine ⟨j, _, hdeliver, by simpa [Record.Event.time, Record.Event.time] using hlt, ?_, c, ?_, ?_⟩
    · rw [hpost, facts.nd.make_grades_compatible_with_finalized_core_gf_votes, hcoreEq]
      simpa only [hus] using hmem
    · rw [hpost, facts.nd.make_grades_compatible_with_finalized_core_timestamp_vote, hcoreEq]
      exact hc
    · have hup : (W j w).st.core.t ≤ t' :=
        Restated.store_time_le_event_timeOn facts S Hs Xb hf hdeliver w
      exact lt_of_le_of_lt hle (WithBot.coe_lt_coe.mpr (lt_of_le_of_lt hup hlt))
  · obtain ⟨hblock, hnew, hcore, huindex⟩ := hcall
    have huB : u ∈ B.gf_votes := List.mem_of_getElem? huindex
    have huErase : u ∈ B.erase.gf_votes := by
      rwa [Proofs.NamedWire.erase_goldfish_votes]
    rcases hblock with
        ⟨t'', hdeliver, hbefore⟩ | ⟨t'', htick', ⟨out, hout, hWout, hBem⟩, hbefore⟩
    · have heq : Record.Event.deliver w (Object.block B) t'' = e :=
        Option.some.inj (hdeliver.symm.trans he)
      have htt : t'' = t' := (congrArg Record.Event.time heq).trans htime
      subst t''
      subst hbefore
      have hpreBodies : B ∉ (W j w).st.bodies := by
        intro hB
        apply hnew
        have hcoh := (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho j w
          (W j) (hW j).1).1.1.1
        rw [hcoh.1]
        exact Finset.mem_image_of_mem NamedBlock.erase hB
      have hpostBodies := on_block_new_body₄₉ facts S (W j w).st B hnew hcore
      have hstamps : Restated.Vocabulary.Protocol.PoolStamps M (W j w).st.core :=
        Restated.poolStamps_stateBeforeOn facts S Hs Xb hf w j
      have hclock0 : M.vote_time S.E s ≤ (W j w).st.core.t := by
        refine Restated.tick_le_store_timeOn facts S Hs Xb hf hdeliver ?_ hloRelay
        exact hf.tick_total _ hpost w hwVote (Restated.Vocabulary.Proofs.Optimistic.publicTime_vote_time facts S s)
          (le_trans hloRelay
            (hf.in_horizon _ (List.mem_of_getElem? hdeliver)).2)
      have hclockUp : (W j w).st.core.t ≤ t' :=
        Restated.store_time_le_event_timeOn facts S Hs Xb hf hdeliver w
      have hslot : (W j w).st.core.s = s := by
        have hsc := Restated.Vocabulary.Proofs.NamedStoreBridge.slotOfClock_stateBefore facts S rho j w
          (W j) (hW j).1
        unfold Restated.Vocabulary.Proofs.Optimistic.SlotOfClock at hsc
        rw [hsc]
        exact facts.sch.slotOf_of_between S.E s hclock0
          (lt_of_le_of_lt hclockUp hlt)
      have hfresh : ¬ u.slot < (W j w).st.core.s - 1 := by
        rw [hus, hslot]
        exact Nat.not_lt.mpr (Nat.sub_le s 1)
      have hfuture : ¬ (W j w).st.core.s < u.slot := by
        rw [hslot, hus]
        exact Nat.lt_irrefl s
      have hcommittee : u.val_index ∈ S.E.committee u.slot :=
        (hf.wire _ w (Object.block B) t' hdeliver).1 B rfl |>.2.2 u huB
      have hlocal := Restated.Vocabulary.Proofs.Optimistic.block_carried_before_deadline_or_equivocates facts
        S (W j w).st B u (M.support_cutoff S.E s) hstamps hpreBodies hpostBodies
        huErase hcommittee hfresh hfuture (lt_of_le_of_lt hclockUp hlt)
      let final := M.on_block_with .alsoCarried S.E S.hc S.cfg (W j w).st B
      have hfinalEq : (W (j + 1) w).st = M.make_grades_compatible_with_finalized final := by
        rw [Restated.Vocabulary.Proofs.NamedReceiptCallsBase.delivery_result facts S rho hdeliver (W j) (hW j).1
            (hf.receipt_outcome _ _ _ _ hdeliver) (W (j + 1)) (hW j).2,
          facts.nd.process_block]
      have hgfEq : (W (j + 1) w).st.core.gf_votes = final.core.gf_votes := by
        rw [hfinalEq, facts.nd.make_grades_compatible_with_finalized_core_gf_votes]
      have hstampEq : (W (j + 1) w).st.core.timestamp_vote = final.core.timestamp_vote := by
        rw [hfinalEq, facts.nd.make_grades_compatible_with_finalized_core_timestamp_vote]
      have hpoolEq : ∀ k : Slot,
          M.store_pool (W (j + 1) w).st.core k = M.store_pool final.core k := by
        intro k
        rw [hfinalEq]
        exact congrFun (facts.nd.make_grades_compatible_with_finalized_core_pool _) k
      have hlocal' :
          u ∈ beforeCutoff final.core.timestamp_vote
              (M.support_cutoff S.E s) ((M.store_pool final.core u.slot)) ∨
            M.equivocates
              (beforeCutoff final.core.timestamp_vote
                (M.support_cutoff S.E s) ((M.store_pool final.core u.slot)))
              u.val_index = true := by
        simpa only [final] using hlocal
      rcases hlocal' with hlocal | hequiv
      · rw [mem_beforeCutoff_iff] at hlocal
        have hpool := hlocal.1
        obtain ⟨c, hc, hc'⟩ := exists_stamp_of_stampedBefore hlocal.2
        have hpool' : u ∈ final.core.gf_votes u.slot := (facts.sto.mem_store_pool_iff _ _ _).1 hpool
        refine ⟨_, _, he, ?_, ?_, c, ?_, hc'⟩
        · simpa [htime] using hlt
        · rw [hgfEq]
          simpa only [hus] using hpool'
        · rw [hstampEq]
          exact hc
      · have hfull : M.equivocates
            ((M.store_pool final.core u.slot))
            u.val_index = true :=
          facts.sch.equivocates_mono (by
            intro x hx
            exact ((mem_beforeCutoff_iff _ _ _ _).1 hx).1) u.val_index hequiv
        have hno := Restated.pool_no_honest_equivocation_of_coreOn facts S Hs Xb hf hHs w (j + 1) (T := t')
          (fun k e' hk he' => by
            simpa only [Record.Event.time, Record.Event.time] using
              Restated.time_le_of_index_lt_succ_eventOn facts S Hs Xb hf hdeliver k e' hk he')
          s hvalt'
        have hno' : M.equivocates ((M.store_pool final.core u.slot)) u.val_index = false := by
          rw [← hpoolEq, hus]
          exact hno
        rw [hno'] at hfull
        simp at hfull
    · have heq : Record.Event.tick w t'' = e := Option.some.inj (htick'.symm.trans he)
      have htt : t'' = t' := (congrArg Record.Event.time heq).trans htime
      subst t''
      subst hbefore
      obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc (W j w).st.core.toHealing t'
        (W j w).cache
      have _hr_p := facts.ndRun.stateBeforeOf_reachedNode S rho j (W j) (hW j).1 w
      have _hv_p := facts.ndRun.stateBeforeOf_runs_as S rho j (W j) (hW j).1 w
      obtain ⟨D, hD⟩ := facts.dt.propose_block_with_nonempty S w (W j w) t' out hout
        (facts.nd.block_mem_on_tick_emit S w (W j w) t' out hout hBem).1.1
        (facts.nd.block_mem_on_tick_emit S w (W j w) t' out hout hBem).1.2.1
        (facts.nd.block_mem_on_tick_emit S w (W j w) t' out hout hBem).1.2.2
        (facts.nd.block_mem_on_tick_emit_awake S w (W j w) t' out hout hBem) c hc
      have hproposal : D.2 = some B := by
        rw [Restated.Vocabulary.Proofs.NamedReceiptCallsBase.self_proposal_call facts S rho htick' (W j)
          (hW j).1 out hout hBem c hc D hD]
      obtain ⟨o, ho⟩ := facts.dt.proposal_with_nonempty (M.frameContract c) .poolAndCarried S.E S.hc
        (S.node w) (M.ns_setClock S.E (W j w).st t')
      have hgf' : B.gf_votes = (M.ns_setClock S.E (W j w).st t').core.gf_votes
          ((M.ns_setClock S.E (W j w).st t').core.s - 1) :=
        facts.dt.proposal_with_gf_votes _ .poolAndCarried S.E S.hc (S.node w) _ o ho
          (facts.dt.proposal_with_eq_of_propose_block_with_snd _ _ _ _ _ _ D hD hproposal o ho)
      have hslot : (M.ns_setClock S.E (W j w).st t').core.s = s := by
        rw [facts.hd.Sts_setClock_core_s]
        exact facts.sch.slotOf_of_between S.E s hloRelay hlt
      have hstamps : Restated.Vocabulary.Protocol.PoolStamps M (M.ns_setClock S.E (W j w).st t').core := by
        have htle : (W j w).st.core.t ≤ t' :=
          Restated.store_time_le_event_timeOn facts S Hs Xb hf htick' w
        exact poolStamps_setClock₄₉ facts S.E _ htle (Restated.poolStamps_stateBeforeOn facts S Hs Xb hf w j)
      have huPool : u ∈ (M.ns_setClock S.E (W j w).st t').core.gf_votes
          ((M.ns_setClock S.E (W j w).st t').core.s - 1) := by
        rw [← hgf']
        exact List.mem_of_getElem? huindex
      have huslot := hstamps.slot _ u huPool
      have hbad : s = s - 1 := by simpa [hus, hslot] using huslot
      have hltNat : s - 1 < s := Nat.sub_lt (Nat.zero_lt_of_lt hs) (by decide)
      exact False.elim ((Nat.ne_of_lt hltNat) hbad.symm)

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

/-- Along the path `W` of the bundle, if `lo ≤ vote_time s`, `v` emits the vote `u` of slot `s > 0`
    at `vote_time s`, `v` and `w` are in `Hs (support_cutoff s)`, and `support_cutoff s` is inside
    the horizon and at most `Gamma` and `Gamma'`, then `u` is in the pool of `s` of `w`'s core store
    in `W (strictEventIndex rho Gamma)`, stamped before `Gamma'`. -/
theorem canonicalSuffixGfVoteInCutoffView_coreOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    {v : V} {s : Slot} (hv : v ∈ Hs (M.support_cutoff S.E s)) (hs : 0 < s)
    {u : GoldfishVote V}
    (hpost : lo ≤ M.vote_time S.E s)
    (hemit : Restated.Vocabulary.Execution.NamedRun.emits M S rho W v (Object.gfVote u)
      (M.vote_time S.E s))
    (hus : u.slot = s) {w : V} (hw : w ∈ Hs (M.support_cutoff S.E s))
    (Gamma Gamma' : Time)
    (hGamma : M.support_cutoff S.E s ≤ Gamma)
    (hGamma' : M.support_cutoff S.E s ≤ Gamma')
    (hhor : M.support_cutoff S.E s ≤ rho.horizon) :
    u ∈ beforeCutoff (W (strictEventIndex rho Gamma) w).st.core.timestamp_vote Gamma'
      (M.store_pool (W (strictEventIndex rho Gamma) w).st.core s) := by
  obtain ⟨j, e, hj, hjt, hmem, c, hc, hlt⟩ :=
    Restated.canonicalSuffixGfVotePooledBeforeFreeze_coreOn facts S Hs Xb hf hHs hv hs hpost
      hemit hus hw hhor
  have hjN : j < strictEventIndex rho Gamma := by
    by_contra hcon
    have hGe : Gamma ≤ e.time :=
      Restated.le_time_of_index_geOn facts S Hs Xb hf (t := Gamma) (j := j) (e := e)
        (Nat.le_of_not_lt hcon) hj
    exact absurd (lt_of_lt_of_le hjt hGamma) (not_lt_of_ge hGe)
  have hcarry : Restated.Vocabulary.Protocol.PoolCarry M (W (j + 1) w).st.core
      (W (strictEventIndex rho Gamma) w).st.core :=
    Restated.pool_carryOn facts S Hs Xb hf w _ hjN
  rw [mem_beforeCutoff_iff]
  refine ⟨?_, ?_⟩
  · exact (facts.sto.mem_store_pool_iff _ _ _).mpr (hcarry.mem s u hmem)
  exact stampedBefore_of_lt (hcarry.stamp u c hc) (lt_of_lt_of_le hlt (by exact_mod_cast hGamma'))

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

/-- Along the path `W` of the bundle, if `lo ≤ vote_time s`, `confirmation_time s` is inside the
    horizon, `v ∈ Hs (support_cutoff s)`, the author of the vote `u` of slot `s > 0` is in
    `Hs (confirmation_time s)` and emitted `u` at `vote_time s`, and `u`'s head arrives in `v`'s
    confirmation store before `support_cutoff s`, then `u` is in every outcome of the confirmation
    votes of that store. -/
theorem canonicalSuffixHonestVoteCountedOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {s : Slot} (hs : 0 < s)
    (hpost : lo ≤ M.vote_time S.E s)
    (hhor : M.confirmation_time S.E s ≤ rho.horizon)
    (v : V) (hv : v ∈ Hs (M.support_cutoff S.E s))
    (u : GoldfishVote V) (hus : u.slot = s)
    (hval : u.val_index ∈ Hs (M.confirmation_time S.E s))
    (hemit : Restated.Vocabulary.Execution.Run.emits M S rho W u.val_index (Object.gfVote u)
      (M.vote_time S.E s))
    (harr : Proofs.Optimistic.HeadArrivesBefore
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core (M.confirmation_time S.E s)).T
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core
          (M.confirmation_time S.E s)).timestamp_block
      (M.support_cutoff S.E s) u) :
    ∀ cv, Restated.Vocabulary.Protocol.confVotes M S.E
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core (M.confirmation_time S.E s)) s ⇢ cv →
      u ∈ cv := by
  intro cv hcv
  have hle : M.support_cutoff S.E s ≤
      M.confirmation_time S.E s :=
    facts.sch.Sts_support_cutoff_le_confirmation_time S.E s
  let n := strictEventIndex rho (M.confirmation_time S.E s)
  have hnT := time_lt_of_lt_strict₄₉ hf.sorted (M.confirmation_time S.E s)
  obtain ⟨H, hfind, hH⟩ := harr
  have hHmem : H ∈ (W n v).st.core.T := by
    rw [← tickStore_T₄₉ facts (S := S) (W n v) (M.confirmation_time S.E s)]
    exact Proofs.HealingLemmas.find?_mem hfind
  have hslot : H.slot ≤ u.slot :=
    Restated.emitted_vote_head_slot_le_of_store_memOn facts S Hs Xb hf
      (hHsXb _ hval) (hHsXb _ hv) hemit hus hHmem (Proofs.HealingLemmas.find?_root hfind)
  have hrecv0 := Restated.canonicalSuffixGfVoteInCutoffView_coreOn facts S Hs Xb hf hHs
    (hHs _ _ hle hval) hs hpost hemit hus hv _ _ hle (le_refl _) (le_trans hle hhor)
  have hconfPool : M.store_pool (Restated.Vocabulary.Proofs.Optimistic.tickStore M S (W n v).st.core
      (M.confirmation_time S.E s)) s = M.store_pool (W n v).st.core s :=
    facts.sto.pool_set_clock_slot _ _ _ s
  have hconfTs : (Restated.Vocabulary.Proofs.Optimistic.tickStore M S (W n v).st.core
      (M.confirmation_time S.E s)).timestamp_vote = (W n v).st.core.timestamp_vote :=
    facts.sto.store_with_t_s_timestamp_vote _ _ _
  have hrecv : u ∈ beforeCutoff
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S (W n v).st.core
        (M.confirmation_time S.E s)).timestamp_vote
      (M.support_cutoff S.E s)
      (M.store_pool (Restated.Vocabulary.Proofs.Optimistic.tickStore M S (W n v).st.core
        (M.confirmation_time S.E s)) s) := by
    rw [hconfPool, hconfTs]
    exact hrecv0
  obtain ⟨e, he, rfl⟩ := returns_map_elim₄₉ _ _ _ hcv
  obtain ⟨τ, hτ, rfl⟩ := returns_map_elim₄₉ _ _ _ he
  have hearly : u ∈ beforeCutoff τ (M.support_cutoff S.E s)
      (M.store_pool (Restated.Vocabulary.Proofs.Optimistic.tickStore M S (W n v).st.core
        (M.confirmation_time S.E s)) s) := by
    have hr := (mem_beforeCutoff_iff _ _ _ _).1 hrecv
    rw [mem_beforeCutoff_iff]
    exact ⟨hr.1, facts.sto.stampedBefore_store_tau_of _ hfind hslot hr.2 hH τ hτ⟩
  rw [Finset.mem_filter]
  refine ⟨hearly, ?_⟩
  rw [facts.fc.no_second_vote_in_eq_true_iff]
  intro x hx
  by_cases hxv : x.val_index = u.val_index
  · refine Or.inl ?_
    have hxpool' : x ∈ (M.store_pool (W n v).st.core s) := by
      rw [← hconfPool]
      exact ((mem_beforeCutoff_iff _ _ _ _).1 hx).1
    have hupool' : u ∈ (M.store_pool (W n v).st.core s) := by
      rw [← hconfPool]
      exact ((mem_beforeCutoff_iff _ _ _ _).1 hrecv).1
    have hno := Restated.pool_no_honest_equivocationOn facts S Hs Xb hf hHs v n
      (T := M.confirmation_time S.E s)
      (fun k e hk he => le_of_lt (hnT k e hk he)) s hval
    by_contra hne
    have hboth := (facts.sch.equivocates_eq_true_iff _ _).2 ⟨x, hxpool', u, hupool', hne, hxv, rfl⟩
    rw [hno] at hboth
    exact Bool.false_ne_true hboth
  · exact Or.inr hxv

end

/-! ## Helpers of the second half -/

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Proofs.HealingSurface
open scoped DC

/-- The vote `u` is visible to `w` in `W n`: it is in some slot's pool of `w`'s core store there, or
    is included in a block of that store's tree. -/
private def canonicalVoteVisible₄₉b (W : Nat → V → M.N) (w : V) (n : Nat)
    (u : GoldfishVote V) : Prop :=
  (∃ k : Slot, u ∈ (W n w).st.core.gf_votes k) ∨ ∃ B ∈ (W n w).st.core.T, u ∈ B.gf_votes

/-- In a run sorted by key, the world `W (strictEventIndex rho t)` of a path `W` of the run is a
    world strictly before the instant `t`. -/
private theorem mem_stateBeforeTime_along₄₉b {S : Setup V} {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (t : Time) :
    W (strictEventIndex rho t) ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t := by
  have hpre : rho.events.filter (fun e => decide (e.time < t)) =
      rho.events.take (rho.events.filter (fun e => decide (e.time < t))).length := by
    refine List.prefix_iff_eq_take.mp ?_
    rw [DecoupledConsensusModel.Proofs.Bridges.filter_eq_takeWhile_of_pairwise
      (R := fun e f => Record.Event.key e ≤ Record.Event.key f) ?_ _ hsorted]
    · exact List.takeWhile_prefix _
    · intro e f hk hf
      simp only [decide_eq_true_eq] at hf ⊢
      exact lt_of_le_of_lt (Restated.time_le_of_key_le hk) hf
  show W (strictEventIndex rho t) ∈
    (rho.events.filter (fun e => decide (e.time < t))).foldlM (Record.worldStepOf M S)
      (fun v => M.initial S v)
  rw [hpre]
  exact (hW _).1

omit [DecidableEq V] [Fintype V] in
/-- In a run sorted by key, every event before the index `strictEventIndex rho t` is strictly before
    the instant `t`. -/
private theorem time_lt_of_lt_strict₄₉b {rho : Record.Run V}
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

/-- If `n` satisfies the node invariant, then for every cache `c`, with `m` the confirmation read
    staged from `n` at `t`, every head the Goldfish vote duty can compute on `m` is in the tree of
    `n`'s core store. -/
private theorem voteDutyHead_mem₄₉b (facts : Record.Facts M) (S : Setup V) (n : M.N)
    (hinvPre : Restated.Vocabulary.Proofs.NamedRuntime.NodeInvariant M S n) (t : Time) (c : M.Cache) :
    let m := M.mkNode (M.ns_setClock S.E n.st t) n.record c
    ∀ T, M.voter_filtered_block_tree S.E m.st.core m.st.core.s ⇢ T →
    ∀ L L' H, M.get_head_in_tree_with_layer (M.gradeContract m.cache) S.E S.hc
        (M.toHealing m.st.core) T L L' (m.st.core.s - 1) ⇢ H →
    H ∈ n.st.core.T := by
  intro m T hT L L' H hH
  have hmst : m.st = M.store_with_cache (M.ns_setClock S.E n.st t) _ := facts.nd.mkNode_st _ _ _
  have hmc : m.cache = c := facts.nd.mkNode_cache _ _ _
  rw [hmst] at hT hH
  try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at hT hH
  rw [hmc] at hH
  have hinv : Restated.Vocabulary.Proofs.NamedConfirmationMembership.Invariant M S.E S.cfg
      (M.ns_setClock S.E n.st t) :=
    facts.hd.invariant_clock S.E S.cfg _ _ hinvPre.1
  have hroot : M.get_fg_root (M.toHealing (M.ns_setClock S.E n.st t).core).toFG ∈
      (M.ns_setClock S.E n.st t).core.T :=
    Restated.Vocabulary.Proofs.NamedStoreRoots.fg_root_mem facts _ hinv.1.2
  obtain ⟨R, hR⟩ := facts.gr.anchor_nonempty S.E S.hc (M.toHealing (M.ns_setClock S.E n.st t).core)
    (M.round_of S.hc (M.toHealing (M.ns_setClock S.E n.st t).core).toFG.toSG.toGoldfishStore.s)
    (M.readFrame c (M.toHealing (M.ns_setClock S.E n.st t).core)
      (M.round_of S.hc (M.toHealing (M.ns_setClock S.E n.st t).core).toFG.toSG.toGoldfishStore.s)).g1
  have hRT : R ∈ (M.ns_setClock S.E n.st t).core.T := by
    have h := Restated.Vocabulary.Proofs.NamedProposalParent.frame_anchor_mem facts S.E S.hc
      (M.toHealing (M.ns_setClock S.E n.st t).core) _ _
      (by rw [Record.Model.HS.T, facts.sto.toHealing_gs_T]; exact hroot) R hR
    rw [Record.Model.HS.T, facts.sto.toHealing_gs_T] at h
    exact h
  have hR' := (facts.nd.gradeContract_sgRoot_eq_frameAnchor c S.E S.hc _ _ R).2 hR
  have hHmem := facts.fc.Sts_get_head_in_tree_with_layer_mem (M.gradeContract c) S.E S.hc
    (M.toHealing (M.ns_setClock S.E n.st t).core) T L L' _ R hR' hRT
    (facts.hd.Sts_voter_filtered_block_tree_subset S.E _ _ T hT) H hH
  rw [facts.hd.Sts_setClock_core_T] at hHmem
  exact hHmem

/-- The store a tick at `t` hands its first duty, staged from `n`'s core store, has the tree of
    `n`'s core store. -/
private theorem tickStore_T₄₉b (facts : Record.Facts M) {S : Setup V} (n : M.N) (t : Time) :
    (Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core t).T = n.st.core.T := by
  rw [Restated.Vocabulary.Proofs.Optimistic.tickStore,
    ← facts.hd.setClock_core_eq_store_with_t_s S.E n.st t, facts.hd.Sts_setClock_core_T]

/-- The store a tick at `t` hands its first duty, staged from `n`'s core store, has the block stamps
    of `n`'s core store. -/
private theorem tickStore_timestamp_block₄₉b (facts : Record.Facts M) {S : Setup V} (n : M.N)
    (t : Time) :
    (Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core t).timestamp_block =
      n.st.core.timestamp_block := by
  rw [Restated.Vocabulary.Proofs.Optimistic.tickStore,
    ← facts.hd.setClock_core_eq_store_with_t_s S.E n.st t, facts.hd.setClock_core_timestamp_block]

omit [DecidableEq V] [Fintype V] in
/-- If `stampedBefore ts Γ x` holds, `ts` gives `x` a stamp `τ` with `τ < Γ`. -/
private theorem stamp_of_stampedBefore₄₉b {α : Type} {ts : TimestampMap α} {Γ : Time} {x : α}
    (h : stampedBefore ts Γ x = true) : ∃ τ : Stamp, ts x = some τ ∧ τ < (Γ : Stamp) := by
  unfold stampedBefore at h
  cases hx : ts x with
  | none => rw [hx] at h; exact absurd h Bool.false_ne_true
  | some τ => rw [hx] at h; exact ⟨τ, rfl, of_decide_eq_true h⟩

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

/-- For every cache `c`, the confirmation read staged from `n` at `t` with the cache `c` has, at
    every slot `k`, the vote pool of `n`'s core store. -/
private theorem confirmationRead_pool₄₉b (facts : Record.Facts M) (S : Setup V) (n : M.N)
    (t : Time) (c : M.Cache) (k : Slot) :
    M.store_pool (M.mkNode (M.ns_setClock S.E n.st t) n.record c).st.core k =
      M.store_pool n.st.core k := by
  rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [facts.hd.Sts_setClock_core_pool]

/-- If `B`'s erasure is not in the tree of `before`'s core store and is in the tree of the core
    store `M.postCore S before B` returns, then `B` is among the named blocks of the store the block
    handler returns on `before` and `B`. -/
private theorem carried_block_body_of_core₄₉b (facts : Record.Facts M) (S : Setup V)
    (before : M.NS) (B : NamedBlock V)
    (hnew : B.erase ∉ before.core.T) (hpost : B.erase ∈ (M.postCore S before B).core.T) :
    B ∈ (M.on_block_with .alsoCarried S.E S.hc S.cfg before B).bodies := by
  rw [facts.nd.postCore_eq_process_block_core] at hpost
  by_cases hp : B.parent ∈ before.bodies
  · have hmem : B ∈ (M.ns_process_block_core S.E S.hc S.cfg before B).bodies := by
      rw [facts.hd.process_block_core_bodies_eq_commit S.E S.hc S.cfg hp]
      exact facts.hd.mem_commitBlock_bodies_of_fresh S.E S.hc S.cfg rfl ⟨hnew, hpost⟩
    exact facts.hd.mem_on_block_with_bodies_of_mem_core .alsoCarried S.E S.hc S.cfg before B hmem
  · rw [facts.hd.process_block_core_of_parent_not_mem S.E S.hc S.cfg hp] at hpost
    exact absurd hpost hnew

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

/-- Along the path `W` of the bundle, if `lo ≤ vote_time s`, `support_cutoff s` is inside the
    horizon, `x` and `w` are in `Hs (support_cutoff s)`, `x` emitted the vote `u` of slot `s > 0` at
    `vote_time s`, `gst` carries the votes and vote stamps of `w`'s core store in
    `W (strictEventIndex rho Gamma)` for some `Gamma ≥ support_cutoff s`, every block `u`'s head
    finds in `gst`'s tree is from a slot at most `u.slot`, and `u`'s head arrives in `gst` before
    `support_cutoff s`, then `u` is in every outcome of `gst`'s voter support view of slot `s + 1`. -/
theorem canonicalSuffixHonestVoteMemVoterSupport_coreOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    {s : Slot} (hs : 0 < s)
    (hpost : lo ≤ M.vote_time S.E s)
    (hhor : M.support_cutoff S.E s ≤ rho.horizon)
    {x : V} (hx : x ∈ Hs (M.support_cutoff S.E s)) {u : GoldfishVote V}
    (hus : u.slot = s)
    (hemit : (Restated.Vocabulary.Execution.Run.emits M S rho W x (Object.gfVote u))
      (M.vote_time S.E s))
    {w : V} (hw : w ∈ Hs (M.support_cutoff S.E s)) {Gamma : Time}
    (hGamma : M.support_cutoff S.E s ≤ Gamma)
    {gst : M.GS}
    (hgf : gst.gf_votes = (W (strictEventIndex rho Gamma) w).st.core.gf_votes)
    (hts : gst.timestamp_vote = (W (strictEventIndex rho Gamma) w).st.core.timestamp_vote)
    (hheads : ∀ H, Block.find? gst.T u.head = some H → H.slot ≤ u.slot)
    (harr : Proofs.Optimistic.HeadArrivesBefore gst.T gst.timestamp_block
      (M.support_cutoff S.E s) u) :
    ∀ Y : Finset (GoldfishVote V), M.voter_support_view S.E gst (s + 1) ⇢ Y → u ∈ Y := by
  intro Y hY
  have h := Restated.canonicalSuffixGfVoteInCutoffView_coreOn facts
    S Hs Xb hf hHs hx hs hpost hemit hus hw Gamma (M.view_freeze S.E s)
      hGamma
      (le_of_lt (facts.sch.Optimistic_support_cutoff_lt_view_freeze S.E s)) hhor
  have hpool : (M.gs_pool gst s) = M.store_pool (W (strictEventIndex rho Gamma) w).st.core s := by
    ext y
    rw [facts.sto.mem_goldfishStore_pool_iff, facts.sto.mem_store_pool_iff, hgf]
  obtain ⟨H, hfind, hH⟩ := harr
  rw [mem_beforeCutoff_iff] at h
  have hu : u ∈ M.gs_pool gst s := by
    rw [hpool]
    exact h.1
  have hv : stampedBefore gst.timestamp_vote (M.view_freeze S.E s) u = true := by
    rw [hts]
    exact h.2
  have hb : stampedBefore gst.timestamp_block (M.view_freeze S.E s) H = true := by
    rw [stampedBefore_eq_occurrenceBefore] at hH ⊢
    exact occurrenceBefore_mono
      (le_of_lt (facts.sch.Optimistic_support_cutoff_lt_view_freeze S.E s)) hH
  obtain ⟨τ, hτ, hτlt⟩ := stamp_of_stampedBefore₄₉b hv
  obtain ⟨σ, hσ, hσlt⟩ := stamp_of_stampedBefore₄₉b hb
  exact facts.sch.mem_voter_support_view_of_pool S.E gst s hu hτ hτlt hfind (hheads H hfind)
    hσ hσlt Y hY

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

/-- Along the path `W` of the bundle, if every event before index `n` happens by `T`, the vote `u`
    is in some slot's pool of `w`'s core store in `W n` or is included in a block of that store's
    tree, and `u`'s author is in `Hs T`, then `u`'s author emitted `u` at some instant. -/
theorem canonicalEmitsOfVoteVisible_coreOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    (w : V) (n : Nat) {T : Time}
    (hT : ∀ (j : Nat) (e : Record.Event V), j < n → rho.events[j]? = some e → e.time ≤ T)
    {u : GoldfishVote V}
    (hu : canonicalVoteVisible₄₉b W w n u)
    (hx : u.val_index ∈ Hs T) :
    ∃ t : Time, Restated.Vocabulary.Execution.NamedRun.emits M S rho W u.val_index (Object.gfVote u) t := by
  rcases hu with ⟨k, hk⟩ | ⟨B, hB, hmem⟩
  · exact Restated.named_emits_of_voteVisibleOn facts S Hs Xb hf hHs w n hT (Or.inl ⟨k, hk⟩) hx
  · obtain ⟨B', hB', hB'eq⟩ :=
      Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore facts S rho n w
        (W n) (hf.onePath n).1 hB
    have hmem' : u ∈ B'.gf_votes := by
      rw [← Proofs.NamedWire.erase_goldfish_votes, hB'eq]
      exact hmem
    exact Restated.named_emits_of_voteVisibleOn facts S Hs Xb hf hHs w n hT
      (Or.inr ⟨B', hB', hmem'⟩) hx

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

/-- Along the path `W` of the bundle, if every event before index `n` happens by `T`, and `u₁` and
    `u₂` are visible in `w`'s core store in `W n`, have the same author in `Hs T` and the same slot,
    then `u₁ = u₂`. -/
theorem canonicalVoteVisibleUnique_coreOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    (w : V) (n : Nat) {T : Time}
    (hT : ∀ (j : Nat) (e : Record.Event V), j < n → rho.events[j]? = some e → e.time ≤ T)
    {u₁ u₂ : GoldfishVote V}
    (h₁ : canonicalVoteVisible₄₉b W w n u₁)
    (h₂ : canonicalVoteVisible₄₉b W w n u₂)
    (hx : u₁.val_index ∈ Hs T)
    (hval : u₂.val_index = u₁.val_index)
    (hslot : u₁.slot = u₂.slot) : u₁ = u₂ := by
  obtain ⟨t₁, he₁⟩ := Restated.canonicalEmitsOfVoteVisible_coreOn facts S Hs Xb hf hHs w n hT h₁ hx
  obtain ⟨t₂, he₂⟩ := Restated.canonicalEmitsOfVoteVisible_coreOn facts S Hs Xb hf hHs w n hT h₂ (by
    rw [hval]
    exact hx)
  rw [hval] at he₂
  exact Restated.emits_gfVote_uniqueOn facts S Hs Xb hf he₁ he₂ hslot

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

/-- Along the path `W` of the bundle, if every event before index `n` happens by `T` and `gst`'s
    votes and tree are among those of `w`'s core store in `W n`, then for `x` in `Hs T`, every slot
    `s` and every outcome `L` of `gst`'s voter view of `s`, `L` does not show `x` equivocating. -/
theorem canonicalVoterViewNoHonestEquivocation_coreOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    (w : V) (n : Nat) {T : Time}
    (hT : ∀ (j : Nat) (e : Record.Event V), j < n → rho.events[j]? = some e → e.time ≤ T)
    (gst : M.GS)
    (hgf : ∀ (k : Slot) (u : GoldfishVote V), u ∈ gst.gf_votes k →
      u ∈ (W n w).st.core.gf_votes k)
    (hTree : ∀ B ∈ gst.T, B ∈ (W n w).st.core.T)
    {x : V} (hx : x ∈ Hs T) (s : Slot) :
    ∀ L : Finset (GoldfishVote V), M.voter_view S.E gst s ⇢ L → M.equivocates L x = false := by
  intro L hL
  have hview : ∀ u ∈ L,
      canonicalVoteVisible₄₉b W w n u ∧ u.slot = s - 1 := by
    intro u hu
    rcases facts.fc.voter_view_cases_beforeCutoff S.E gst s L hL hu with
      hu | ⟨B, hB, -, hmem, hus⟩
    · have hu1 : u ∈ gst.gf_votes (s - 1) :=
        (facts.sto.mem_goldfishStore_pool_iff gst (s - 1) u).1
          ((mem_beforeCutoff_iff _ _ _ _).1 hu).1
      have hmem := hgf (s - 1) u hu1
      exact ⟨Or.inl ⟨s - 1, hmem⟩,
        (Restated.poolStamps_stateBeforeOn facts S Hs Xb hf w n).slot _ u hmem⟩
    · have hBT : B ∈ (W n w).st.core.T := hTree B hB
      exact ⟨Or.inr ⟨B, hBT, hmem⟩, hus⟩
  apply facts.sch.equivocates_eq_false_of_card_le_one
  refine Finset.card_le_one.mpr ?_
  intro u₁ hu₁ u₂ hu₂
  rw [facts.sch.mem_votes_by_iff] at hu₁ hu₂
  obtain ⟨hv₁, hs₁⟩ := hview u₁ hu₁.1
  obtain ⟨hv₂, hs₂⟩ := hview u₂ hu₂.1
  exact Restated.canonicalVoteVisibleUnique_coreOn facts S Hs Xb hf hHs w n hT hv₁ hv₂
    (by rw [hu₁.2]; exact hx)
    (by rw [hu₂.2, hu₁.2]) (by rw [hs₁, hs₂])

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

/-- Along the path `W` of the bundle, under `HonestCommitteesOn`, if `lo ≤ vote_time s`,
    `support_cutoff s` is inside the horizon, every member of slot `s`'s committee in
    `Hs (vote_time s)` voted for a run block of the cone `tgt`, `w ∈ Hs (support_cutoff s)`,
    `support_cutoff s ≤ Gamma ≤ confirmation_time s`, `gst` carries the votes, vote stamps and tree
    of `w`'s core store in `W (strictEventIndex rho Gamma)`, and the heads picked from slot `s`'s
    committee resolve in `gst`, then every outcome of `gst`'s voter view of slot `s + 1` with every
    outcome of its support view gives cone support for `tgt` at `s`, counted over
    `Hs (confirmation_time s)`. -/
theorem canonicalSuffixConeSupportVoterView_coreOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    {s : Slot} (hs : 0 < s)
    (hpost : lo ≤ M.vote_time S.E s)
    (hhor : M.support_cutoff S.E s ≤ rho.horizon)
    {tgt : Block V → Prop}
    (hnames : Restated.NamedHonestVotesConeOn M S rho W Hs Xb s tgt)
    {w : V} (hw : w ∈ Hs (M.support_cutoff S.E s)) {Gamma : Time}
    (hGamma : M.support_cutoff S.E s ≤ Gamma)
    (hGammaConf : Gamma ≤ M.confirmation_time S.E s)
    {gst : M.GS}
    (hgf : gst.gf_votes = (W (strictEventIndex rho Gamma) w).st.core.gf_votes)
    (hts : gst.timestamp_vote = (W (strictEventIndex rho Gamma) w).st.core.timestamp_vote)
    (hT : gst.T = (W (strictEventIndex rho Gamma) w).st.core.T)
    (hres : Restated.HeadsResolveInOn M S rho W Hs Xb s gst.T gst.timestamp_block) :
    ∀ L : Finset (GoldfishVote V), M.voter_view S.E gst (s + 1) ⇢ L →
    ∀ L' : Finset (GoldfishVote V), M.voter_support_view S.E gst (s + 1) ⇢ L' →
    Restated.Vocabulary.Proofs.Optimistic.ConeSupport M S.E gst.T L L' L s
      (Hs (M.confirmation_time S.E s)) tgt := by
  intro L hL L' hL'
  have hcutConf : M.support_cutoff S.E s ≤ M.confirmation_time S.E s :=
    facts.sch.Sts_support_cutoff_le_confirmation_time S.E s
  have hvoteConf : M.vote_time S.E s ≤ M.confirmation_time S.E s :=
    le_trans (le_of_lt (Restated.vote_time_lt_support_cutoff_l49 facts S s)) hcutConf
  have hnT := time_lt_of_lt_strict₄₉b hf.sorted Gamma
  refine Restated.Vocabulary.Proofs.Optimistic.coneSupport_of_named_votes facts (hcom s) (subset_refl _)
    (facts.fc.voter_support_view_subset S.E gst (s + 1) ?_ L' hL' L hL) ?_ ?_
  · intro B hB
    refine Restated.carried_support_subset_of_mem_T_coreOn facts S Hs Xb hf w
      (strictEventIndex rho Gamma) ?_
    rw [← hT]
    exact hB
  · intro y _ hyHonest
    refine Restated.canonicalVoterViewNoHonestEquivocation_coreOn facts
      S Hs Xb hf hHs w (strictEventIndex rho Gamma) (T := Gamma)
      (fun k e hk he => le_of_lt (hnT k e hk he))
      gst ?_ ?_ (hHs _ _ hGammaConf hyHonest) (s + 1) L hL
    · intro k y' hy'
      rw [← hgf]
      exact hy'
    · intro B hB
      rw [← hT]
      exact hB
  · intro y hyCommittee hyHonest
    obtain ⟨X, htgt, hrun, hemit⟩ := hnames y (hHs _ _ hvoteConf hyHonest) hyCommittee
    have hhead : Restated.HonestHeadOn M S rho W Hs Xb s X.erase :=
      ⟨y, hyHonest, hyCommittee, ⟨X, rfl, hrun⟩, hemit⟩
    obtain ⟨hfind, hstamp⟩ := hres X.erase hhead
    have hheads : ∀ H, Block.find? gst.T X.erase.root = some H → H.slot ≤ s := by
      intro H hfindH
      have hHmem : H ∈ (W (strictEventIndex rho Gamma) w).st.core.T := by
        rw [← hT]
        exact Proofs.HealingLemmas.find?_mem hfindH
      exact Restated.emitted_vote_head_slot_le_of_store_memOn facts S Hs Xb hf
        (hHsXb _ hyHonest) (hHsXb _ hw) hemit rfl hHmem
        (Proofs.HealingLemmas.find?_root hfindH)
    exact ⟨X.erase, htgt, hheads X.erase hfind,
      Restated.canonicalSuffixHonestVoteMemVoterSupport_coreOn facts
        S Hs Xb hf hHs hs hpost hhor (hHs _ _ hcutConf hyHonest) rfl hemit hw hGamma hgf hts
          hheads
          ⟨X.erase, hfind, hstamp⟩ L' hL',
      hfind⟩

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

/-- The conclusion of `canonicalSuffixConeSupportVoterView_coreOn`, from its hypotheses gathered in
    one premise structure. -/
theorem canonicalSuffixConeSupportVoterViewOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    {s : Slot} (hs : 0 < s)
    (hpost : lo ≤ M.vote_time S.E s)
    (hhor : M.support_cutoff S.E s ≤ rho.horizon)
    {tgt : Block V → Prop}
    (hnames : Restated.NamedHonestVotesConeOn M S rho W Hs Xb s tgt)
    {w : V} (hw : w ∈ Hs (M.support_cutoff S.E s)) {Gamma : Time}
    (hGamma : M.support_cutoff S.E s ≤ Gamma)
    (hGammaConf : Gamma ≤ M.confirmation_time S.E s)
    {gst : M.GS}
    (hgf : gst.gf_votes = (W (strictEventIndex rho Gamma) w).st.core.gf_votes)
    (hts : gst.timestamp_vote = (W (strictEventIndex rho Gamma) w).st.core.timestamp_vote)
    (hT : gst.T = (W (strictEventIndex rho Gamma) w).st.core.T)
    (hres : Restated.HeadsResolveInOn M S rho W Hs Xb s gst.T gst.timestamp_block) :
    ∀ L : Finset (GoldfishVote V), M.voter_view S.E gst (s + 1) ⇢ L →
    ∀ L' : Finset (GoldfishVote V), M.voter_support_view S.E gst (s + 1) ⇢ L' →
    Restated.Vocabulary.Proofs.Optimistic.ConeSupport M S.E gst.T L L' L s
      (Hs (M.confirmation_time S.E s)) tgt :=
  Restated.canonicalSuffixConeSupportVoterView_coreOn facts S Hs Xb hf hHs hHsXb hcom hs hpost hhor hnames
    hw hGamma hGammaConf hgf hts hT hres

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
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- Along the path `W` of the bundle, for `w ∈ Xb`, every slot `d` and every outcome `c` of the
    phase tick on `w`'s node state in `W (strictEventIndex rho (vote_time d))`, with `n` the read
    staged from that node state with `c`, every head the vote duty can compute on `n` is the erasure
    of a named block in the tree of `n`'s core store that is a run block read through `Xb` along
    `W`. -/
theorem voterHead_runBlock_for_voteDutyReadOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {w : V} (hw : w ∈ Xb) (d : Slot) :
    ∀ c : M.Cache, M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core.toHealing
        (M.vote_time S.E d) (W (strictEventIndex rho (M.vote_time S.E d)) w).cache ⇢ c →
    let n := M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) w).st
      (M.vote_time S.E d)) (W (strictEventIndex rho (M.vote_time S.E d)) w).record c
    ∀ T, M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T →
    ∀ L, M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
    ∀ L', M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore
        n.st.core.s ⇢ L' →
    ∀ Hd, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
        T L L' (n.st.core.s - 1) ⇢ Hd →
    ∃ H : NamedBlock V, H.erase = Hd ∧
      H.erase ∈ n.st.core.T ∧
      Restated.blockInRunOn M S rho W Xb H := by
  intro c hc n T hT L hL L' hL' Hd hHd
  have hinv := Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho
    (strictEventIndex rho (M.vote_time S.E d)) w _ (hf.onePath _).1
  have hHpre := voteDutyHead_mem₄₉b facts S _ hinv (M.vote_time S.E d) c T hT L L' Hd hHd
  obtain ⟨H', hH'erase, hHrun⟩ :=
    Restated.runBlock_of_mem_core_T_stateBeforeTimeOn facts S Hs Xb hf hw
      (M.vote_time S.E d) hHpre
  refine ⟨H', hH'erase, ?_, hHrun⟩
  have hnst : n.st = M.store_with_cache (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) w).st (M.vote_time S.E d)) _ := facts.nd.mkNode_st _ _ _
  rw [hH'erase, hnst]
  try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
  rw [facts.hd.Sts_setClock_core_T]
  exact hHpre

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
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- Along the path `W` of the bundle, if `x ∈ Xb` emitted, at slot `s`'s vote instant, the vote
    whose head is the run block `C` read through `Xb`, then for every outcome `c` of the phase tick
    on `x`'s node state in `W (strictEventIndex rho (vote_time s))`, `C`'s erasure is in the tree of
    the read staged from that node state with `c`. -/
theorem emittedHead_mem_voteDutyStoreOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {x : V} (hx : x ∈ Xb) {s : Slot} {C : NamedBlock V}
    (hCrun : Restated.blockInRunOn M S rho W Xb C)
    (hemit : Restated.Vocabulary.Execution.NamedRun.emits M S rho W x
      (.gfVote ⟨x, s, C.erase.root⟩) (M.vote_time S.E s)) :
    ∀ c : M.Cache, M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E s)) x).st.core.toHealing
        (M.vote_time S.E s) (W (strictEventIndex rho (M.vote_time S.E s)) x).cache ⇢ c →
    C.erase ∈ (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) x).st
      (M.vote_time S.E s)) (W (strictEventIndex rho (M.vote_time S.E s)) x).record c).st.core.T := by
  intro c hc
  set n := M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) x).st
    (M.vote_time S.E s)) (W (strictEventIndex rho (M.vote_time S.E s)) x).record c with hn
  obtain ⟨T, hT⟩ := facts.fc.voter_filtered_block_tree_nonempty S.E n.st.core n.st.core.s
  obtain ⟨L, hL⟩ := facts.fc.voter_view_nonempty S.E
    (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s
  obtain ⟨L', hL'⟩ := facts.fc.voter_support_view_nonempty S.E
    (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s
  obtain ⟨Hd, hHd⟩ := facts.fc.get_head_in_tree_with_layer_nonempty (M.gradeContract n.cache) S.E
    S.hc (M.toHealing n.st.core) T L L' (n.st.core.s - 1)
  have hroot : (⟨x, s, C.erase.root⟩ : GoldfishVote V).head = Hd.root :=
    Restated.emitted_vote_head_eq_voterHeadAtOn facts S Hs Xb hf hemit c hc T hT L hL L' hL' Hd hHd
  obtain ⟨H, hHerase, hHmem, hHrun⟩ :=
    Restated.voterHead_runBlock_for_voteDutyReadOn facts S Hs Xb hf hx s c hc T hT L hL L' hL'
      Hd hHd
  have hrootNamed : H.root = C.root := by
    rw [← Proofs.NamedWire.erase_root H, ← Proofs.NamedWire.erase_root C, hHerase]
    exact hroot.symm
  have hHC : H = C :=
    hf.rootCollisionFree.root_injective H C
      hHrun hCrun H C (Or.inl (Proofs.NamedAncestry.named_self H))
      (Or.inr (Proofs.NamedAncestry.named_self C)) hrootNamed
  simpa only [hHC] using hHmem

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
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- Along the path `W` of the bundle, if `v ∈ Xb`, `support_cutoff s ≤ Gamma`, and every picked head
    of slot `s` is genesis or admitted by `v` before `support_cutoff s`, then every picked head is
    found by its root in the tree of `v`'s core store in `W (strictEventIndex rho Gamma)` and
    stamped there before `support_cutoff s`. -/
theorem headsResolveIn_storeBeforeTime_of_availableBefore_at_coreOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} (hv : v ∈ Xb) (s : Slot) {Gamma : Time}
    (hcut : M.support_cutoff S.E s ≤ Gamma)
    (havailable : Restated.HonestHeadsAvailableBeforeOn M S rho W Hs Xb s v
      (M.support_cutoff S.E s)) :
    Restated.HeadsResolveInOn M S rho W Hs Xb s
      (W (strictEventIndex rho Gamma) v).st.core.T
      (W (strictEventIndex rho Gamma) v).st.core.timestamp_block := by
  let cutoff := M.support_cutoff S.E s
  have htransport : ∀ X : Block V, Restated.HonestHeadOn M S rho W Hs Xb s X →
      X ∈ (W (strictEventIndex rho Gamma) v).st.core.T ∧
        stampedBefore (W (strictEventIndex rho Gamma) v).st.core.timestamp_block cutoff X = true := by
    intro X hX
    rcases havailable X hX with rfl | hadmit
    · exact Restated.genesis_mem_and_stamp_storeBeforeTimeOn facts S Hs Xb hf v Gamma cutoff
    · exact Restated.admittedBefore_mem_and_stamp_atOn facts S Hs Xb hf hadmit hcut
  have hrun : ∀ X : Block V, X ∈ (W (strictEventIndex rho Gamma) v).st.core.T →
      ∃ C : NamedBlock V, C.erase = X ∧ Restated.RunBlockOn M S rho W Xb C :=
    fun X hX => Restated.runBlock_of_mem_core_T_stateBeforeTimeOn facts S Hs Xb hf hv Gamma hX
  apply Restated.headsResolveIn_ofOn facts S rho W Hs Xb s
  · intro X hX
    exact (htransport X hX).1
  · intro X Y hX hY hroot
    obtain ⟨CX, hCX, hCXrun⟩ := hrun X hX
    obtain ⟨CY, hCY, hCYrun⟩ := hrun Y hY
    have hrootNamed : CX.root = CY.root := by
      rw [← Proofs.NamedWire.erase_root CX, ← Proofs.NamedWire.erase_root CY, hCX, hCY]
      exact hroot
    have hCXY : CX = CY :=
      hf.rootCollisionFree.root_injective CX CY hCXrun hCYrun CX CY
        (Or.inl (Proofs.NamedAncestry.named_self CX))
        (Or.inr (Proofs.NamedAncestry.named_self CY)) hrootNamed
    rw [← hCX, ← hCY, hCXY]
  · intro X hX
    exact (htransport X hX).2

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
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- The conclusion of `headsResolveIn_storeBeforeTime_of_availableBefore_at_coreOn`, from its
    hypotheses gathered in one premise structure. -/
theorem headsResolveIn_storeBeforeTime_of_availableBefore_atOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} (hv : v ∈ Xb) (s : Slot) {Gamma : Time}
    (hcut : M.support_cutoff S.E s ≤ Gamma)
    (havailable : Restated.HonestHeadsAvailableBeforeOn M S rho W Hs Xb s v
      (M.support_cutoff S.E s)) :
    Restated.HeadsResolveInOn M S rho W Hs Xb s
      (W (strictEventIndex rho Gamma) v).st.core.T
      (W (strictEventIndex rho Gamma) v).st.core.timestamp_block :=
  Restated.headsResolveIn_storeBeforeTime_of_availableBefore_at_coreOn facts S Hs Xb hf hv s hcut havailable

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
open DecoupledConsensusModel.Internal.NamedRecoveryRead

/-- Along the path `W` of the bundle, if `v ∈ Xb` and every picked head of slot `s` is genesis or
    admitted by `v` before `support_cutoff s`, then every picked head is found by its root in `v`'s
    confirmation store of `s`, staged from `W (strictEventIndex rho (confirmation_time s))`, and
    stamped there before `support_cutoff s`. -/
theorem headsResolveIn_confStore_of_availableBeforeOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} (hv : v ∈ Xb) (s : Slot)
    (havailable : Restated.HonestHeadsAvailableBeforeOn M S rho W Hs Xb s v
      (M.support_cutoff S.E s)) :
    Restated.HeadsResolveInOn M S rho W Hs Xb s
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core
        (M.confirmation_time S.E s)).T
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core
        (M.confirmation_time S.E s)).timestamp_block := by
  have h := Restated.headsResolveIn_storeBeforeTime_of_availableBefore_atOn facts
    S Hs Xb hf hv s (facts.sch.Sts_support_cutoff_le_confirmation_time S.E s) havailable
  rw [tickStore_T₄₉b facts, tickStore_timestamp_block₄₉b facts]
  exact h

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

/-- Along the path `W` of the bundle, under `HonestCommitteesOn`, if `lo ≤ vote_time s`,
    `confirmation_time s` is inside the horizon, every member of slot `s`'s committee in
    `Hs (vote_time s)` voted for a run block of the cone `tgt`, `v ∈ Hs (support_cutoff s)`, and the
    picked heads resolve in `v`'s confirmation store of `s`, then every outcome of that store's
    confirmation votes gives cone support for `tgt` at `s`, counted over `Hs (confirmation_time s)`. -/
theorem coneSupport_confVotes_after_gstOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    {s : Slot} (hs : 0 < s)
    (hpost : lo ≤ M.vote_time S.E s)
    (hhor : M.confirmation_time S.E s ≤ rho.horizon)
    {tgt : Block V → Prop}
    (hnames : Restated.NamedHonestVotesConeOn M S rho W Hs Xb s tgt)
    {v : V} (hv : v ∈ Hs (M.support_cutoff S.E s))
    (hres : Restated.HeadsResolveInOn M S rho W Hs Xb s
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core
        (M.confirmation_time S.E s)).T
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core
        (M.confirmation_time S.E s)).timestamp_block) :
    ∀ cv : Finset (GoldfishVote V), Restated.Vocabulary.Protocol.confVotes M S.E
        (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
          (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core
          (M.confirmation_time S.E s)) s ⇢ cv →
    Restated.Vocabulary.Proofs.Optimistic.ConeSupport M S.E
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core
        (M.confirmation_time S.E s)).T
      cv cv
      (Restated.Vocabulary.Protocol.confLate M S.E
        (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
          (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core
          (M.confirmation_time S.E s)) s)
      s (Hs (M.confirmation_time S.E s)) tgt := by
  intro cv hcv
  have hmem : Restated.Vocabulary.Proofs.Optimistic.tickStore M S
      (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core
      (M.confirmation_time S.E s) ∈ Restated.Vocabulary.Proofs.Optimistic.confStore M S rho v s :=
    ⟨(W (strictEventIndex rho (M.confirmation_time S.E s)) v).st,
      ⟨W (strictEventIndex rho (M.confirmation_time S.E s)),
        mem_stateBeforeTime_along₄₉b hf.sorted hf.onePath _, rfl⟩, rfl⟩
  apply Restated.coneSupport_confVotesOn facts S rho W Hs Xb hcom hHs hnames v _ hmem cv hcv
  · intro u hus hval hemit harr
    exact Restated.canonicalSuffixHonestVoteCountedOn facts S Hs Xb hf hHs hHsXb hs hpost hhor v hv u hus hval
      hemit harr cv hcv
  · exact hres

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
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Statements.Instantiation

/-- Along the path `W` of the bundle, if the proposer of `s + 1` is in `Hs (proposal_time s)`,
    `lo ≤ proposal_time s`, and it is delivered the vote `u` of slot `s` at
    `t ∈ [proposal_time s, proposal_time (s + 1))`, then for every outcome `c` of the phase tick on
    the proposer's node state in `W (strictEventIndex rho (proposal_time (s + 1)))`, the read staged
    from that node state with `c` holds `u` in its pool of `s` or shows `u`'s author equivocating
    there. -/
theorem gfVote_delivery_settled_at_proposalDutyOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {s : Slot} (hprop : S.E.proposer (s + 1) ∈ Hs (M.proposal_time S.E s))
    (hgat : lo ≤ M.proposal_time S.E s)
    {i : Nat} {u : GoldfishVote V} {t : Time}
    (hi : rho.events[i]? = some
      (Record.Event.deliver (S.E.proposer (s + 1)) (Object.gfVote u) t))
    (hus : u.slot = s)
    (hlo : M.proposal_time S.E s ≤ t)
    (hhi : t < M.proposal_time S.E (s + 1)) :
    ∀ c : M.Cache, M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.proposal_time S.E (s + 1))) (S.E.proposer (s + 1))).st.core.toHealing
        (M.proposal_time S.E (s + 1))
        (W (strictEventIndex rho (M.proposal_time S.E (s + 1))) (S.E.proposer (s + 1))).cache ⇢ c →
    let n := M.mkNode
      (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E (s + 1))) (S.E.proposer (s + 1))).st
        (M.proposal_time S.E (s + 1)))
      (W (strictEventIndex rho (M.proposal_time S.E (s + 1))) (S.E.proposer (s + 1))).record c
    u ∈ M.store_pool n.st.core s ∨ M.equivocates (M.store_pool n.st.core s) u.val_index = true := by
  intro c hc n
  have hW := hf.onePath
  let pre := (W i (S.E.proposer (s + 1))).st.core
  have hpreTime : pre.t ≤ t :=
    Restated.store_time_le_event_timeOn facts S Hs Xb hf hi (S.E.proposer (s + 1))
  have hclock0 : M.proposal_time S.E s ≤ pre.t :=
    Restated.tick_le_store_timeOn facts S Hs Xb hf hi
      (hf.tick_total _ hgat (S.E.proposer (s + 1)) hprop
        (Restated.Vocabulary.Proofs.Optimistic.publicTime_proposal_time facts S s)
        (le_trans hlo (hf.in_horizon _ (List.mem_of_getElem? hi)).2))
      hlo
  have hslot : pre.s = s := by
    have hslot' := Restated.Vocabulary.Proofs.NamedStoreBridge.slotOfClock_stateBefore facts
      S rho i (S.E.proposer (s + 1)) (W i) (hW i).1
    unfold Restated.Vocabulary.Proofs.Optimistic.SlotOfClock at hslot'
    show (W i (S.E.proposer (s + 1))).st.core.s = s
    rw [hslot']
    exact facts.sch.slotOf_of_proposal_before_next_proposal S.E s hclock0
      (lt_of_le_of_lt hpreTime hhi)
  have hclock : pre.t < M.proposal_time S.E (s + 1) :=
    lt_of_le_of_lt hpreTime hhi
  have hcommittee : u.val_index ∈ S.E.committee u.slot :=
    (hf.wire i (S.E.proposer (s + 1)) (Object.gfVote u) t hi).2 u rfl
  have hlocal := Restated.Vocabulary.Protocol.on_goldfish_vote_checked_beforeCutoff_or_equivocates facts
    S.E pre u (M.proposal_time S.E (s + 1)) hcommittee
    (Restated.poolStamps_stateBeforeOn facts S Hs Xb hf (S.E.proposer (s + 1)) i)
    (by rw [hus, hslot]; exact Nat.not_lt.mpr (Nat.sub_le s 1))
    (by rw [hus, hslot]; exact lt_irrefl s)
    hclock
  have hpostSt : (W (i + 1) (S.E.proposer (s + 1))).st =
      M.make_grades_compatible_with_finalized
        (M.ns_with_core (W i (S.E.proposer (s + 1))).st (M.on_goldfish_vote_checked S.E pre u)) := by
    rw [Restated.Vocabulary.Proofs.NamedReceiptCallsBase.delivery_result facts S rho hi (W i) (hW i).1
      (facts.nd.process_nonempty S (W i (S.E.proposer (s + 1))) _ (fun _ h => by cases h)) (W (i + 1)) (hW i).2,
      facts.nd.process_gfVote]
  have hpostTs : (W (i + 1) (S.E.proposer (s + 1))).st.core.timestamp_vote =
      (M.on_goldfish_vote_checked S.E pre u).timestamp_vote := by
    rw [hpostSt, facts.nd.make_grades_compatible_with_finalized_core_timestamp_vote,
      facts.hd.ns_with_core_core]
  have hpostPool : ∀ k : Slot, M.store_pool (W (i + 1) (S.E.proposer (s + 1))).st.core k =
      M.store_pool (M.on_goldfish_vote_checked S.E pre u) k := by
    intro k
    have h := congrFun (facts.nd.make_grades_compatible_with_finalized_core_pool
      (M.ns_with_core (W i (S.E.proposer (s + 1))).st (M.on_goldfish_vote_checked S.E pre u))) k
    rw [facts.hd.ns_with_core_core, ← hpostSt] at h
    exact h
  let Gamma := M.proposal_time S.E (s + 1)
  let N := strictEventIndex rho Gamma
  have hiN : i < N := lt_strict_of_time_lt₄₉b hf.sorted hi hhi
  have hcarry : Restated.Vocabulary.Protocol.PoolCarry M
      (W (i + 1) (S.E.proposer (s + 1))).st.core (W N (S.E.proposer (s + 1))).st.core :=
    Restated.pool_carryOn facts S Hs Xb hf (S.E.proposer (s + 1)) N (Nat.succ_le_of_lt hiN)
  have hpool : M.store_pool (W N (S.E.proposer (s + 1))).st.core s ⊆ M.store_pool n.st.core s := by
    rw [confirmationRead_pool₄₉b facts]
  rw [← hpostTs, ← hpostPool, hus] at hlocal
  have hsub : beforeCutoff (W (i + 1) (S.E.proposer (s + 1))).st.core.timestamp_vote Gamma
      (M.store_pool (W (i + 1) (S.E.proposer (s + 1))).st.core s) ⊆ M.store_pool n.st.core s := by
    intro x hx
    exact hpool ((mem_beforeCutoff_iff _ _ _ _).1
      (Restated.Vocabulary.Protocol.beforeCutoff_subset_of_poolCarry facts hcarry s Gamma hx)).1
  rcases hlocal with hmem | hequiv
  · exact Or.inl (hsub hmem)
  · exact Or.inr (facts.sch.equivocates_mono hsub u.val_index hequiv)

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
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Statements.Instantiation

/-- Along the path `W` of the bundle, if `lo ≤ proposal_time s`, the proposer of `s + 1` is in
    `Hs (support_cutoff s)` and processes the vote `u` of slot `s` at
    `t ∈ [proposal_time s, proposal_time (s + 1))`, and `proposal_time (s + 1)` is inside the
    horizon, then for every outcome `c` of the phase tick on the proposer's node state in
    `W (strictEventIndex rho (proposal_time (s + 1)))`, the read staged from it with `c` holds `u`
    in its pool of `s` or shows `u`'s author equivocating there. -/
theorem gfVote_processes_settled_at_nextProposer_afterGST_coreOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    {u : GoldfishVote V} {s : Slot} {t : Time}
    (hpost : lo ≤ M.proposal_time S.E s)
    (hprop : S.E.proposer (s + 1) ∈ Hs (M.support_cutoff S.E s))
    (hproc : Restated.Vocabulary.Execution.NamedRun.processes M S rho W (S.E.proposer (s + 1))
      (Object.gfVote u) t)
    (hus : u.slot = s)
    (hlo : M.proposal_time S.E s ≤ t)
    (hhi : t < M.proposal_time S.E (s + 1))
    (hhor : M.proposal_time S.E (s + 1) ≤ rho.horizon) :
    ∀ c : M.Cache, M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.proposal_time S.E (s + 1))) (S.E.proposer (s + 1))).st.core.toHealing
        (M.proposal_time S.E (s + 1))
        (W (strictEventIndex rho (M.proposal_time S.E (s + 1))) (S.E.proposer (s + 1))).cache ⇢ c →
    let n := M.mkNode
      (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E (s + 1))) (S.E.proposer (s + 1))).st
        (M.proposal_time S.E (s + 1)))
      (W (strictEventIndex rho (M.proposal_time S.E (s + 1))) (S.E.proposer (s + 1))).record c
    u ∈ M.store_pool n.st.core s ∨ M.equivocates (M.store_pool n.st.core s) u.val_index = true := by
  intro c hc n
  have hpropVote : M.proposal_time S.E s < M.vote_time S.E s :=
    facts.sch.proposal_time_lt_vote_time S.E s
  have hvoteCut := Restated.vote_time_lt_support_cutoff_l49 facts S s
  rcases hproc with hemit | ⟨i, hi⟩
  · apply Or.inl
    obtain ⟨hs, ht, -, hus'⟩ := Restated.Vocabulary.Proofs.Optimistic.emits_gfVote_shape facts S W hemit (fun i => facts.ndRun.stateBeforeOf_reachedNode S rho i (W i) (hf.onePath i).1 _) (fun i => facts.ndRun.stateBeforeOf_runs_as S rho i (W i) (hf.onePath i).1 _)
    have hslot : S.E.slotOf t = s := by rw [← hus', hus]
    have ht' : t = M.vote_time S.E s := by
      simpa only [hslot] using ht
    have hemit' : (Restated.Vocabulary.Execution.Run.emits M S rho W (S.E.proposer (s + 1))
        (Object.gfVote u)) (M.vote_time S.E s) := by
      rw [← ht']
      exact hemit
    have hpostVote : lo ≤ M.vote_time S.E s :=
      le_trans hpost (le_of_lt hpropVote)
    have hcut := facts.sch.support_cutoff_le_proposal_time_succ S.E s
    have hrecv := Restated.canonicalSuffixGfVoteInCutoffView_coreOn facts
      S Hs Xb hf hHs hprop (by simpa only [hslot] using hs) hpostVote hemit' hus hprop
      (M.proposal_time S.E (s + 1))
      (M.proposal_time S.E (s + 1)) hcut hcut
      (le_trans hcut hhor)
    rw [confirmationRead_pool₄₉b facts]
    exact ((mem_beforeCutoff_iff _ _ _ _).mp hrecv).1
  · exact Restated.gfVote_delivery_settled_at_proposalDutyOn facts S Hs Xb hf
      (hHs _ _ (le_of_lt (hpropVote.trans hvoteCut)) hprop) hpost hi hus hlo hhi c hc

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
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Statements.Instantiation

/-- Along the path `W` of the bundle, if event `i` is `e`, `e` happens before
    `proposal_time (s + 1)`, and the proposer of `s + 1` has processed `u` in `W (i + 1)`, then for
    every outcome `c` of the phase tick on the proposer's node state in
    `W (strictEventIndex rho (proposal_time (s + 1)))`, `u` is in the pool of `s` of the read staged
    from it with `c`. -/
theorem gfVote_processed_after_event_at_proposalDutyOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {i : Nat} {e : Record.Event V} {u : GoldfishVote V} {s : Slot}
    (he : rho.events[i]? = some e) (hus : u.slot = s)
    (hprocessed : Restated.Vocabulary.Execution.Object.processed M
      (W (i + 1) (S.E.proposer (s + 1))).st (Object.gfVote u) = true)
    (hearly : e.time < M.proposal_time S.E (s + 1)) :
    ∀ c : M.Cache, M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.proposal_time S.E (s + 1))) (S.E.proposer (s + 1))).st.core.toHealing
        (M.proposal_time S.E (s + 1))
        (W (strictEventIndex rho (M.proposal_time S.E (s + 1))) (S.E.proposer (s + 1))).cache ⇢ c →
    let n := M.mkNode
      (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E (s + 1))) (S.E.proposer (s + 1))).st
        (M.proposal_time S.E (s + 1)))
      (W (strictEventIndex rho (M.proposal_time S.E (s + 1))) (S.E.proposer (s + 1))).record c
    u ∈ M.store_pool n.st.core s := by
  intro c hc n
  have h := Restated.gfVote_processed_after_event_at_proposerDuty_coreOn facts S Hs Xb hf he hus
    hprocessed hearly
  rw [Restated.Vocabulary.Proofs.Optimistic.tickStore,
    ← facts.hd.setClock_core_eq_store_with_t_s] at h
  rewrite [show n.st = M.store_with_cache (M.ns_setClock S.E
      (W (strictEventIndex rho (M.proposal_time S.E (s + 1))) (S.E.proposer (s + 1))).st
      (M.proposal_time S.E (s + 1))) c from facts.nd.mkNode_st _ _ _]
  simp only [facts.nd.store_with_cache_store_pool]
  exact h

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
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Statements.Instantiation

/-- Along the path `W` of the bundle, if event `k` is `e`, `e` happens before
    `proposal_time (s + 1)` and `m ≤ k + 1`, then for every outcome `c` of the phase tick on the
    proposer's node state in `W (strictEventIndex rho (proposal_time (s + 1)))`, the pool of `s` of
    the proposer of `s + 1` in `W m` is contained in the pool of `s` of the read staged from it with
    `c`. -/
theorem proposalDutyPool_of_prefixOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo) {s : Slot} {k m : Nat}
    {e : Record.Event V} (he : rho.events[k]? = some e)
    (hearly : e.time < M.proposal_time S.E (s + 1))
    (hm : m ≤ k + 1) :
    ∀ c : M.Cache, M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.proposal_time S.E (s + 1))) (S.E.proposer (s + 1))).st.core.toHealing
        (M.proposal_time S.E (s + 1))
        (W (strictEventIndex rho (M.proposal_time S.E (s + 1))) (S.E.proposer (s + 1))).cache ⇢ c →
    let n := M.mkNode
      (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E (s + 1))) (S.E.proposer (s + 1))).st
        (M.proposal_time S.E (s + 1)))
      (W (strictEventIndex rho (M.proposal_time S.E (s + 1))) (S.E.proposer (s + 1))).record c
    M.store_pool (W m (S.E.proposer (s + 1))).st.core s ⊆ M.store_pool n.st.core s := by
  intro c hc n
  let Gamma := M.proposal_time S.E (s + 1)
  let N := strictEventIndex rho Gamma
  have hkN : k < N := lt_strict_of_time_lt₄₉b hf.sorted he hearly
  have hcarry : Restated.Vocabulary.Protocol.PoolCarry M
      (W m (S.E.proposer (s + 1))).st.core (W N (S.E.proposer (s + 1))).st.core :=
    Restated.pool_carryOn facts S Hs Xb hf
      (S.E.proposer (s + 1)) N (le_trans hm (Nat.succ_le_of_lt hkN))
  intro x hx
  rw [confirmationRead_pool₄₉b facts]
  rw [facts.sto.mem_store_pool_iff] at hx ⊢
  exact hcarry.mem s x hx

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
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Statements.Instantiation

/-- Along the path `W` of the bundle, if `w` is in `Hs (proposal_time s)`, `lo ≤ proposal_time s`,
    and `w` is delivered `o` at `t ∈ [proposal_time s, proposal_time (s + 1))` at index `i`, then
    `w`'s core store in `W i` is at slot `s`. -/
theorem delivery_store_slot_before_next_proposalOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {w : V} {s : Slot} (hw : w ∈ Hs (M.proposal_time S.E s))
    (hgat : lo ≤ M.proposal_time S.E s)
    {i : Nat} {o : Object V} {t : Time}
    (hi : rho.events[i]? = some (Record.Event.deliver w o t))
    (hlo : M.proposal_time S.E s ≤ t)
    (hhi : t < M.proposal_time S.E (s + 1)) :
    (W i w).st.core.s = s := by
  have hpreTime : (W i w).st.core.t ≤ t :=
    Restated.store_time_le_event_timeOn facts S Hs Xb hf hi w
  have hclock0 : M.proposal_time S.E s ≤ (W i w).st.core.t :=
    Restated.tick_le_store_timeOn facts S Hs Xb hf hi
      (hf.tick_total _ hgat w hw (Restated.Vocabulary.Proofs.Optimistic.publicTime_proposal_time facts S s)
        (le_trans hlo (hf.in_horizon _ (List.mem_of_getElem? hi)).2))
      hlo
  have hslot := Restated.Vocabulary.Proofs.NamedStoreBridge.slotOfClock_stateBefore facts S rho i w
    (W i) (hf.onePath i).1
  unfold Restated.Vocabulary.Proofs.Optimistic.SlotOfClock at hslot
  rw [hslot]
  exact facts.sch.slotOf_of_proposal_before_next_proposal S.E s hclock0
    (lt_of_le_of_lt hpreTime hhi)

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
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Statements.Instantiation

/-- Along the path `W` of the bundle, if `lo ≤ proposal_time s`, the proposer of `s + 1` is in
    `Hs (support_cutoff s)` and actually handles the vote `u` of slot `s` at
    `t ∈ [proposal_time s, proposal_time (s + 1))`, and `proposal_time (s + 1)` is inside the
    horizon, then for every outcome `c` of the phase tick on the proposer's node state in
    `W (strictEventIndex rho (proposal_time (s + 1)))`, the read staged from it with `c` holds `u`
    in its pool of `s` or shows `u`'s author equivocating there. -/
theorem actual_gfVote_settled_at_proposalDutyOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    {s : Slot} (hpost : lo ≤ M.proposal_time S.E s)
    (hprop : S.E.proposer (s + 1) ∈ Hs (M.support_cutoff S.E s))
    {j : Nat} {u : GoldfishVote V} {t : Time}
    (hactual : Restated.Vocabulary.Execution.NamedRun.actualHandlesAt M S rho W j (S.E.proposer (s + 1))
      (Object.gfVote u) t)
    (hus : u.slot = s)
    (hlo : M.proposal_time S.E s ≤ t)
    (hhi : t < M.proposal_time S.E (s + 1))
    (hhor : M.proposal_time S.E (s + 1) ≤ rho.horizon) :
    ∀ c : M.Cache, M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.proposal_time S.E (s + 1))) (S.E.proposer (s + 1))).st.core.toHealing
        (M.proposal_time S.E (s + 1))
        (W (strictEventIndex rho (M.proposal_time S.E (s + 1))) (S.E.proposer (s + 1))).cache ⇢ c →
    let n := M.mkNode
      (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E (s + 1))) (S.E.proposer (s + 1))).st
        (M.proposal_time S.E (s + 1)))
      (W (strictEventIndex rho (M.proposal_time S.E (s + 1))) (S.E.proposer (s + 1))).record c
    u ∈ M.store_pool n.st.core s ∨ M.equivocates (M.store_pool n.st.core s) u.val_index = true := by
  intro c hc n
  have hW := hf.onePath
  have hpropCut : M.proposal_time S.E s ≤ M.support_cutoff S.E s :=
    le_of_lt ((facts.sch.proposal_time_lt_vote_time S.E s).trans
      (Restated.vote_time_lt_support_cutoff_l49 facts S s))
  obtain ⟨hidx, e, he, -, htime⟩ := hactual
  have hearly : e.time < M.proposal_time S.E (s + 1) := by
    rw [htime]; exact hhi
  rcases hidx with (⟨t', hj, out, hout, hWout, hem⟩ | ⟨t', hj⟩) | ⟨B, jrow, before, hcall⟩
  · have heq : Record.Event.tick (S.E.proposer (s + 1)) t' = e :=
      Option.some.inj (hj.symm.trans he)
    have htt : t' = t := (congrArg Record.Event.time heq).trans htime
    subst t'
    exact Restated.gfVote_processes_settled_at_nextProposer_afterGST_coreOn facts
      S Hs Xb hf hHs hpost hprop (Or.inl ⟨j, hj, out, hout, hWout, hem⟩) hus hlo hhi hhor c hc
  · have heq : Record.Event.deliver (S.E.proposer (s + 1)) (Object.gfVote u) t' = e :=
      Option.some.inj (hj.symm.trans he)
    have htt : t' = t := (congrArg Record.Event.time heq).trans htime
    subst t'
    exact Restated.gfVote_processes_settled_at_nextProposer_afterGST_coreOn facts
      S Hs Xb hf hHs hpost hprop (Or.inr ⟨j, hj⟩) hus hlo hhi hhor c hc
  · obtain ⟨hblock, hnew, hcore, huindex⟩ := hcall
    have huErase : u ∈ B.erase.gf_votes := by
      rw [Proofs.NamedWire.erase_goldfish_votes]
      exact List.mem_of_getElem? huindex
    rcases hblock with ⟨t', hdeliver, hbefore⟩ | ⟨t', htick', ⟨out, hout, hWout, hBemit⟩, hbefore⟩
    · have heq : Record.Event.deliver (S.E.proposer (s + 1)) (Object.block B) t' = e :=
        Option.some.inj (hdeliver.symm.trans he)
      have htt : t' = t := (congrArg Record.Event.time heq).trans htime
      subst t'
      have hpreBodies : B ∉ before.bodies := by
        intro hB
        apply hnew
        have hcoh := (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho j
          (S.E.proposer (s + 1)) (W j) (hW j).1).1.1.1
        have hB' : B ∈ (W j (S.E.proposer (s + 1))).st.bodies := by
          rw [← hbefore]
          exact hB
        rw [hbefore, hcoh.1]
        exact Finset.mem_image_of_mem NamedBlock.erase hB'
      have hpostBodies := carried_block_body_of_core₄₉b facts S before B hnew hcore
      have hstamps : Restated.Vocabulary.Protocol.PoolStamps M before.core := by
        rw [hbefore]
        exact Restated.poolStamps_stateBeforeOn facts S Hs Xb hf (S.E.proposer (s + 1)) j
      have hslotStore : before.core.s = s := by
        rw [hbefore]
        exact Restated.delivery_store_slot_before_next_proposalOn facts S Hs Xb hf
          (hHs _ _ hpropCut hprop) hpost hdeliver hlo hhi
      have hfresh : ¬ u.slot < before.core.s - 1 := by
        rw [hus, hslotStore]
        exact Nat.not_lt.mpr (Nat.sub_le s 1)
      have hfuture : ¬ before.core.s < u.slot := by
        rw [hslotStore, hus]
        exact Nat.lt_irrefl s
      have hcommittee : u.val_index ∈ S.E.committee u.slot :=
        ((hf.wire j (S.E.proposer (s + 1)) (Object.block B) t hdeliver).1 B rfl).2.2 u
          (List.mem_of_getElem? huindex)
      have hclock : before.core.t < M.proposal_time S.E (s + 1) := by
        have hle : before.core.t ≤ t := by
          rw [hbefore]
          exact Restated.store_time_le_event_timeOn facts S Hs Xb hf hdeliver (S.E.proposer (s + 1))
        exact lt_of_le_of_lt hle hhi
      have hlocal := Restated.Vocabulary.Proofs.Optimistic.block_carried_before_deadline_or_equivocates facts
        S before B u (M.proposal_time S.E (s + 1)) hstamps hpreBodies
        hpostBodies huErase hcommittee hfresh hfuture hclock
      have hfinalEq : (W (j + 1) (S.E.proposer (s + 1))).st =
          M.make_grades_compatible_with_finalized
            (M.on_block_with .alsoCarried S.E S.hc S.cfg before B) := by
        rw [Restated.Vocabulary.Proofs.NamedReceiptCallsBase.delivery_result facts S rho hdeliver (W j)
          (hW j).1 (hf.receipt_outcome _ _ _ _ hdeliver) (W (j + 1)) (hW j).2,
          facts.nd.process_block, ← hbefore]
      have hfinalTs : (W (j + 1) (S.E.proposer (s + 1))).st.core.timestamp_vote =
          (M.on_block_with .alsoCarried S.E S.hc S.cfg before B).core.timestamp_vote := by
        rw [hfinalEq, facts.nd.make_grades_compatible_with_finalized_core_timestamp_vote]
      have hfinalPool : ∀ k : Slot, M.store_pool (W (j + 1) (S.E.proposer (s + 1))).st.core k =
          M.store_pool (M.on_block_with .alsoCarried S.E S.hc S.cfg before B).core k := by
        intro k
        have h := congrFun (facts.nd.make_grades_compatible_with_finalized_core_pool
          (M.on_block_with .alsoCarried S.E S.hc S.cfg before B)) k
        rw [← hfinalEq] at h
        exact h
      have hlocal' : u ∈ beforeCutoff
          (W (j + 1) (S.E.proposer (s + 1))).st.core.timestamp_vote
          (M.proposal_time S.E (s + 1))
          (M.store_pool (W (j + 1) (S.E.proposer (s + 1))).st.core u.slot) ∨
          M.equivocates
            (beforeCutoff
              (W (j + 1) (S.E.proposer (s + 1))).st.core.timestamp_vote
              (M.proposal_time S.E (s + 1))
              (M.store_pool (W (j + 1) (S.E.proposer (s + 1))).st.core u.slot))
            u.val_index = true := by
        rw [hfinalTs, hfinalPool]
        exact hlocal
      rw [hus] at hlocal'
      have hsub : (beforeCutoff
          (W (j + 1) (S.E.proposer (s + 1))).st.core.timestamp_vote
          (M.proposal_time S.E (s + 1))
          (M.store_pool (W (j + 1) (S.E.proposer (s + 1))).st.core s)) ⊆
          M.store_pool n.st.core s := by
        intro x hx
        exact Restated.proposalDutyPool_of_prefixOn facts S Hs Xb hf he hearly (le_refl (j + 1)) c hc
          ((mem_beforeCutoff_iff _ _ _ _).1 hx).1
      rcases hlocal' with hmem | hequiv
      · exact Or.inl (hsub hmem)
      · exact Or.inr (facts.sch.equivocates_mono hsub u.val_index hequiv)
    · have heq : Record.Event.tick (S.E.proposer (s + 1)) t' = e :=
        Option.some.inj (htick'.symm.trans he)
      have htt : t' = t := (congrArg Record.Event.time heq).trans htime
      subst t'
      have hstamps : Restated.Vocabulary.Protocol.PoolStamps M before.core := by
        rw [hbefore]
        have hrawStamps := Restated.poolStamps_stateBeforeOn facts S Hs Xb hf (S.E.proposer (s + 1)) j
        have htle : (W j (S.E.proposer (s + 1))).st.core.t ≤ t :=
          Restated.store_time_le_event_timeOn facts S Hs Xb hf htick' (S.E.proposer (s + 1))
        exact poolStamps_setClock₄₉ facts S.E _ htle hrawStamps
      have hcallEq := Restated.Vocabulary.Proofs.NamedReceiptCallsBase.self_proposal_call facts S rho
        htick' (W j) (hW j).1 out hout hBemit
      obtain ⟨c', hc'⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc
        (W j (S.E.proposer (s + 1))).st.core.toHealing t (W j (S.E.proposer (s + 1))).cache
      have _hr_p := facts.ndRun.stateBeforeOf_reachedNode S rho j (W j) (hW j).1 (S.E.proposer (s + 1))
      have _hv_p := facts.ndRun.stateBeforeOf_runs_as S rho j (W j) (hW j).1 (S.E.proposer (s + 1))
      obtain ⟨D, hD⟩ := facts.dt.propose_block_with_nonempty S (S.E.proposer (s + 1)) (W j (S.E.proposer (s + 1))) t out hout
        (facts.nd.block_mem_on_tick_emit S (S.E.proposer (s + 1)) (W j (S.E.proposer (s + 1))) t out hout hBemit).1.1
        (facts.nd.block_mem_on_tick_emit S (S.E.proposer (s + 1)) (W j (S.E.proposer (s + 1))) t out hout hBemit).1.2.1
        (facts.nd.block_mem_on_tick_emit S (S.E.proposer (s + 1)) (W j (S.E.proposer (s + 1))) t out hout hBemit).1.2.2
        (facts.nd.block_mem_on_tick_emit_awake S (S.E.proposer (s + 1)) (W j (S.E.proposer (s + 1))) t out hout hBemit) c' hc'
      have hDeq := hcallEq c' hc' D hD
      obtain ⟨o, ho⟩ := facts.dt.proposal_with_nonempty (M.frameContract c') .poolAndCarried S.E
        S.hc (S.node (S.E.proposer (s + 1))) (M.ns_setClock S.E (W j (S.E.proposer (s + 1))).st t)
      have hgf : B.gf_votes = before.core.gf_votes (before.core.s - 1) := by
        rw [hbefore]
        exact facts.dt.proposal_with_gf_votes _ .poolAndCarried
          S.E S.hc (S.node (S.E.proposer (s + 1))) _ o ho
          (facts.dt.proposal_with_eq_of_propose_block_with_snd _ _ _ _ _ _ D hD
            (by rw [hDeq]) o ho)
      have huPool : u ∈ before.core.gf_votes (before.core.s - 1) := by
        rw [← hgf]
        exact List.mem_of_getElem? huindex
      have huslot := hstamps.slot (before.core.s - 1) u huPool
      apply Or.inl
      refine Restated.proposalDutyPool_of_prefixOn facts S Hs Xb hf he hearly
        (le_of_lt (Nat.lt_succ_self j)) c hc ?_
      have hmemPool : u ∈ before.core.gf_votes s := by
        rw [← hus, huslot]
        exact huPool
      rw [facts.sto.mem_store_pool_iff]
      rw [hbefore, facts.hd.setClock_core_gf_votes] at hmemPool
      exact hmemPool

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
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Statements.Instantiation

/-- Along the path `W` of the bundle, if `v ∈ Hs t` accepts the vote `u` of slot `s` at
    `t ∈ [proposal_time s, view_freeze s)`, `lo ≤ proposal_time s`, the proposer of `s + 1` is in
    `Hs (proposal_time (s + 1))`, and that instant is inside the horizon, then for every outcome `c`
    of the phase tick on the proposer's node state in
    `W (strictEventIndex rho (proposal_time (s + 1)))`, the read staged from it with `c` holds `u`
    in its pool of `s` or shows `u`'s author equivocating there. -/
theorem accepted_gfVote_settled_at_nextProposer_afterGST_coreOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    {v : V}
    {s : Slot}
    (hpost : lo ≤ M.proposal_time S.E s)
    (hprop : S.E.proposer (s + 1) ∈ Hs (M.proposal_time S.E (s + 1)))
    {i : Nat} {u : GoldfishVote V} {t : Time}
    (hv : v ∈ Hs t)
    (hacc : Restated.Vocabulary.Execution.NamedRun.acceptsAt M S rho W i v (Object.gfVote u) t)
    (hus : u.slot = s)
    (hlo : M.proposal_time S.E s ≤ t)
    (hhi : t < M.view_freeze S.E s)
    (hhor : M.proposal_time S.E (s + 1) ≤ rho.horizon) :
    ∀ c : M.Cache, M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.proposal_time S.E (s + 1))) (S.E.proposer (s + 1))).st.core.toHealing
        (M.proposal_time S.E (s + 1))
        (W (strictEventIndex rho (M.proposal_time S.E (s + 1))) (S.E.proposer (s + 1))).cache ⇢ c →
    let n := M.mkNode
      (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E (s + 1))) (S.E.proposer (s + 1))).st
        (M.proposal_time S.E (s + 1)))
      (W (strictEventIndex rho (M.proposal_time S.E (s + 1))) (S.E.proposer (s + 1))).record c
    u ∈ M.store_pool n.st.core s ∨ M.equivocates (M.store_pool n.st.core s) u.val_index = true := by
  intro c hc n
  have hcutNext : M.support_cutoff S.E s ≤ M.proposal_time S.E (s + 1) :=
    facts.sch.support_cutoff_le_proposal_time_succ S.E s
  have hfreezeNext : M.view_freeze S.E s + S.E.Δ ≤ M.proposal_time S.E (s + 1) :=
    facts.sch.view_freeze_add_delta_le_proposal_time_succ S.E s
  by_cases halready : Restated.Vocabulary.Execution.Object.processed M
      (W (i + 1) (S.E.proposer (s + 1))).st (Object.gfVote u) = true
  · obtain ⟨e, he, -, het⟩ := hacc.1.2
    apply Or.inl
    exact Restated.gfVote_processed_after_event_at_proposalDutyOn facts S Hs Xb hf he hus halready
      (lt_of_le_of_lt (le_of_eq het) (lt_of_lt_of_le hhi
        (le_trans (le_of_lt (Int.lt_add_of_pos_right _ S.E.Δ_pos)) hfreezeNext))) c hc
  · have hunaccepted : Restated.Vocabulary.Execution.Object.processed M
        (W (i + 1) (S.E.proposer (s + 1))).st (Object.gfVote u) = false :=
      Bool.eq_false_of_not_eq_true halready
    have hrelayLe : t + S.E.Δ ≤ M.proposal_time S.E (s + 1) :=
      le_trans (Int.add_le_add_right (le_of_lt hhi) S.E.Δ) hfreezeNext
    have hrelayHor : t + S.E.Δ ≤ rho.horizon := le_trans hrelayLe hhor
    have hpostAcceptance : lo ≤ t := le_trans hpost hlo
    obtain ⟨t', hcausal, hdeadline, j, hactual⟩ :=
      Restated.relay_gf_vote_after_gst_coreOn facts S Hs Xb hf hv (hHs _ _ hrelayLe hprop) hpostAcceptance
        hacc hunaccepted hrelayHor
    have hbeforeProposal : t' < M.proposal_time S.E (s + 1) := lt_of_lt_of_le hdeadline hrelayLe
    exact Restated.actual_gfVote_settled_at_proposalDutyOn facts S Hs Xb hf hHs hpost
      (hHs _ _ hcutNext hprop) hactual hus
      (le_trans hlo hcausal) hbeforeProposal hhor c hc

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
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Statements.Instantiation

/-- Along the path `W` of the bundle, if `0 < s`, `lo ≤ proposal_time (s − 1)`, the proposer of `s`
    and `v` are in `Hs (vote_time s)`, `proposal_time s` is inside the horizon, `P` is a block the
    proposal duty can return on the proposer's read of `s`, and `P`'s erasure is in the filtered
    tree of `v`'s vote-duty read of `s`, then every vote of every outcome of that read's voter view
    of `s` that `P` does not include shows its author equivocating among `P`'s votes. -/
theorem voter_raw_extra_equivocates_proposal_afterGST_coreOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    {s : Slot} (hs : 0 < s)
    (hpost : lo ≤ M.proposal_time S.E (s - 1))
    (hprop : S.E.proposer s ∈ Hs (M.vote_time S.E s))
    {v : V} (hv : v ∈ Hs (M.vote_time S.E s))
    (hhor : M.proposal_time S.E s ≤ rho.horizon)
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
    (cv : M.Cache)
    (hcv : M.onPhaseTick S.E S.hc (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core.toHealing
      (M.vote_time S.E s) (W (strictEventIndex rho (M.vote_time S.E s)) v).cache ⇢ cv)
    (hcandidate : P.erase ∈ M.get_filtered_block_tree
      (M.toHealing (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st
        (M.vote_time S.E s)) (W (strictEventIndex rho (M.vote_time S.E s)) v).record cv).st.core).toFG) :
    ∀ L : Finset (GoldfishVote V), M.voter_view S.E
        (M.toHealing (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st
          (M.vote_time S.E s)) (W (strictEventIndex rho (M.vote_time S.E s)) v).record cv).st.core
          ).toFG.toSG.toGoldfishStore s ⇢ L →
    ∀ u ∈ L,
      u ∉ P.erase.gf_votes.toFinset →
        M.equivocates P.erase.gf_votes.toFinset u.val_index = true := by
  intro L hL u hu hnot
  have hW := hf.onePath
  have hnp : M.mkNode
      (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
        (M.proposal_time S.E s))
      (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record cp ∈
      Restated.Vocabulary.Statements.Instantiation.proposerReadAt M S rho s :=
    ⟨W (strictEventIndex rho (M.proposal_time S.E s)), mem_stateBeforeTime_along₄₉b hf.sorted hW _,
      cp, hcp, rfl⟩
  have hpredSucc : s - 1 + 1 = s :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hs))
  have hpropVote : M.proposal_time S.E s ≤ M.vote_time S.E s :=
    le_of_lt (facts.sch.proposal_time_lt_vote_time S.E s)
  have hfreezeVote : M.view_freeze S.E (s - 1) ≤ M.vote_time S.E s := by
    have h := facts.sch.view_freeze_lt_vote_time_succ S.E (s - 1)
    rw [hpredSucc] at h
    exact le_of_lt h
  rcases facts.fc.voter_view_cases S.E _ s L hL hu with ⟨hpool, τ, hτ, hτlt⟩ | ⟨C, hCT, hCs, huC, -⟩
  · have hreceipt' : u ∈ beforeCutoff
        (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E ((s - 1) + 1))) v).st.core ((s - 1) + 1)).timestamp_vote
        (M.view_freeze S.E (s - 1))
        (M.store_pool (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E ((s - 1) + 1))) v).st.core ((s - 1) + 1)) (s - 1)) := by
      rw [facts.sto.toHealing_gs_pool, confirmationRead_pool₄₉b facts] at hpool
      rewrite [facts.sto.toHealing_gs_timestamp_vote, facts.nd.mkNode_st] at hτ; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at hτ; rw [facts.hd.setClock_core_timestamp_vote] at hτ
      rw [hpredSucc, Restated.Vocabulary.Proofs.Optimistic.voteStore,
        Restated.Vocabulary.Proofs.Optimistic.tickStore, facts.sto.store_with_t_s_timestamp_vote,
        mem_beforeCutoff_iff]
      refine ⟨?_, stampedBefore_of_lt hτ hτlt⟩
      show u ∈ (M.store_with_t_s (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core
        (M.vote_time S.E s) (S.E.slotOf (M.vote_time S.E s))).pool (s - 1)
      rw [facts.sto.pool_set_clock_slot]
      exact hpool
    have hΓlo : lo ≤ M.view_freeze S.E (s - 1) :=
      le_trans hpost (le_of_lt
        (((facts.sch.proposal_time_lt_vote_time S.E (s - 1)).trans
          (Restated.vote_time_lt_support_cutoff_l49 facts S (s - 1))).trans
          (facts.sch.Optimistic_support_cutoff_lt_view_freeze S.E (s - 1))))
    obtain ⟨i, t, hacc, hus, hlo, hhi⟩ :=
      Restated.targetReceiptVotesAcceptedInWindow_of_admissibleOn_WeakExecution facts
        S Hs Xb hf (s - 1) (hHs _ _ hfreezeVote hv) hΓlo u hreceipt'
    have hprop' : S.E.proposer ((s - 1) + 1) ∈ Hs (M.proposal_time S.E ((s - 1) + 1)) := by
      rw [hpredSucc]
      exact hHs _ _ hpropVote hprop
    have hvt : v ∈ Hs t := hHs _ _ (le_trans (le_of_lt hhi) hfreezeVote) hv
    have hsettled0 := Restated.accepted_gfVote_settled_at_nextProposer_afterGST_coreOn facts
      (s := s - 1) S Hs Xb hf hHs hpost hprop' hvt hacc hus hlo hhi
        (by simpa only [hpredSucc] using hhor)
    rw [hpredSucc] at hsettled0
    have hsettled := hsettled0 cp hcp
    dsimp only at hsettled
    have hslotP : (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
          (M.proposal_time S.E s))
        (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record cp).st.core.s = s := by
      rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [facts.hd.Sts_setClock_core_s, facts.sch.slotOf_proposal_time]
    have hraw : P.erase.gf_votes.toFinset =
        M.store_pool (M.mkNode
          (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
            (M.proposal_time S.E s))
          (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record cp).st.core
          (s - 1) := by
      rw [Proofs.NamedWire.erase_goldfish_votes,
        Restated.Vocabulary.Protocol.proposedBlock_raw_eq_proposer_pool facts S rho s _ hnp hP, hslotP]
    rcases hsettled with hmem | hequiv
    · exact False.elim (hnot (by rw [hraw]; exact hmem))
    · rw [hraw]
      exact hequiv
  · have hTv : (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st
        (M.vote_time S.E s)) (W (strictEventIndex rho (M.vote_time S.E s)) v).record cv).st.core.T =
        (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core.T := by
      rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [facts.hd.Sts_setClock_core_T]
    have hPprefix : P.erase ∈ (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core.T := by
      have h := facts.fc.get_filtered_block_tree_subset _ hcandidate
      rw [facts.sto.toHealing_T, hTv] at h
      exact h
    have hCprefix : C ∈ (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core.T := by
      rw [facts.sto.toHealing_gs_T, hTv] at hCT
      exact hCT
    have hTn : ∀ (j : Nat) (e : Record.Event V), j < strictEventIndex rho (M.vote_time S.E s) →
        rho.events[j]? = some e → e.time ≤ M.vote_time S.E s :=
      fun j e hj he => le_of_lt (time_lt_of_lt_strict₄₉b hf.sorted _ j e hj he)
    have hCP : C = P.erase := Restated.unique_slot_block_in_store_beforeOn facts S Hs Xb hf hHs hs hprop
      hTn hTn hCprefix hPprefix
      hCs
      (by rw [Proofs.NamedWire.erase_slot]
          exact Restated.Vocabulary.Proofs.HealingSurface.proposedBlockAt_slot facts S rho s (some P)
            ⟨_, hnp, hP⟩ rfl)
    subst C
    exact False.elim (hnot (List.mem_toFinset.2 huC))

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
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Statements.Instantiation

/-- The conclusion of `voter_raw_extra_equivocates_proposal_afterGST_coreOn`, from its hypotheses
    gathered in one premise structure. -/
theorem voter_raw_extra_equivocates_proposal_afterGSTOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    {s : Slot} (hs : 0 < s)
    (hpost : lo ≤ M.proposal_time S.E (s - 1))
    (hprop : S.E.proposer s ∈ Hs (M.vote_time S.E s))
    {v : V} (hv : v ∈ Hs (M.vote_time S.E s))
    (hhor : M.proposal_time S.E s ≤ rho.horizon)
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
    (cv : M.Cache)
    (hcv : M.onPhaseTick S.E S.hc (W (strictEventIndex rho (M.vote_time S.E s)) v).st.core.toHealing
      (M.vote_time S.E s) (W (strictEventIndex rho (M.vote_time S.E s)) v).cache ⇢ cv)
    (hcandidate : P.erase ∈ M.get_filtered_block_tree
      (M.toHealing (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st
        (M.vote_time S.E s)) (W (strictEventIndex rho (M.vote_time S.E s)) v).record cv).st.core).toFG) :
    ∀ L : Finset (GoldfishVote V), M.voter_view S.E
        (M.toHealing (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) v).st
          (M.vote_time S.E s)) (W (strictEventIndex rho (M.vote_time S.E s)) v).record cv).st.core
          ).toFG.toSG.toGoldfishStore s ⇢ L →
    ∀ u ∈ L,
      u ∉ P.erase.gf_votes.toFinset →
        M.equivocates P.erase.gf_votes.toFinset u.val_index = true :=
  Restated.voter_raw_extra_equivocates_proposal_afterGST_coreOn facts
    S Hs Xb hf hHs hs hpost hprop hv hhor cp hcp hP cv hcv hcandidate

end

/-! ## Emitted heights at an event prefix -/

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

open scoped DC in
/-- For every path `W` of `rho`, `W (m + k)` is among the worlds the events `m` to `m + k - 1` lead
    to from `W m`. -/
private theorem onePath_reach₄₉w {S : Setup V} {rho : Record.Run V}
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

open scoped DC in
/-- For every path `W` of `rho` and `m ≤ n`, `W n` is among the worlds the events `m` to `n - 1`
    lead to from `W m`. -/
private theorem onePath_slice₄₉w {S : Setup V} {rho : Record.Run V}
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    {m n : Nat} (hmn : m ≤ n) :
    W n ∈ ((rho.events.drop m).take (n - m)).foldlM (Record.worldStepOf M S) (W m) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [Nat.add_sub_cancel_left]
  exact onePath_reach₄₉w W hW m k

/-- Along the path `W` of the bundle, if the `i`-th event is `v`'s tick at `t`, `i < n`, the outcome
    of that tick along `W` sends an attestation `a`, and `a`'s height pair names `h`, then `h` is at
    most the `h_max` of `v`'s store in `W n`. -/
theorem attestationHeight_le_stateBeforeIndexOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {i n : Nat} {v : V} {t : Time} {a : NamedAttestation V} {h : Height}
    (hi : rho.events[i]? = some (.tick v t))
    (hmem : ∃ out : M.N × List (NamedObject V),
      M.tick S v (W i v) t ⇢ out ∧ W (i + 1) v = out.1 ∧ Object.attest a ∈ out.2)
    (hin : i < n)
    (hh : a.height_pair.erase.height? = some h) :
    h ≤ (W n v).st.h_max := by
  have hemit : Restated.Vocabulary.Execution.Run.emits M S rho W v (Object.attest a) t :=
    ⟨i, hi, hmem⟩
  have hlocal := Restated.honestEmittedHeight_le_localHMaxBeforeTimeOn facts S Hs Xb hf hemit hh
  have ht : t = Restated.Vocabulary.Execution.Setup.a M S a.round :=
    (Restated.Vocabulary.Proofs.Optimistic.emits_attest_shape facts S W hf.onePath hemit).2
  subst ht
  have heq := Restated.action_read_indexOn facts S rho Hs Xb hf i v a.round hi
  have hlocal' : h ≤ (W i v).st.h_max := by
    rcases heq with heq | heq
    · rw [heq]; exact hlocal
    · rw [heq, (facts.nd.wake_st_record _).1]; exact hlocal
  exact hlocal'.trans
    (Restated.Vocabulary.Proofs.HealingSurface.stateBefore_hMax_mono facts S rho v
      (Nat.le_of_lt hin) (W i) (hf.onePath i).1 (W n)
      (onePath_slice₄₉w W hf.onePath (Nat.le_of_lt hin)))

/-- Along the path `W` of the bundle, if `v ∈ X`, the `i`-th event is `v`'s tick at `t`, `i < n`,
    the outcome of that tick along `W` sends an attestation `a`, and `a`'s height pair names `h`,
    then `h` is at most the largest `h_max` over `X` in `W n`. -/
theorem honestEmittedHeight_le_honestHMaxBeforeIndexOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) (X : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {i n : Nat} {v : V} (hv : v ∈ X)
    {t : Time} {a : NamedAttestation V} {h : Height}
    (hi : rho.events[i]? = some (.tick v t))
    (hmem : ∃ out : M.N × List (NamedObject V),
      M.tick S v (W i v) t ⇢ out ∧ W (i + 1) v = out.1 ∧ Object.attest a ∈ out.2)
    (hin : i < n)
    (hh : a.height_pair.erase.height? = some h) :
    h ≤ X.sup fun x => (W n x).st.h_max :=
  (attestationHeight_le_stateBeforeIndexOn facts S Hs Xb hf hi hmem hin hh).trans
    (Restated.localHMax_le_honestHMaxBeforeIndexOn facts S rho X n hv (W n) (hf.onePath n).1)

end

end DecoupledConsensusModel.Sts.Restated
