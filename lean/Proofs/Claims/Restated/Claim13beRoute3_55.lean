import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13beRoute3_45
import Proofs.Claims.Restated.Claim13beRoute3_45b
import Proofs.Claims.Restated.Claim13beRoute3_46
import Proofs.Claims.Restated.Claim13beRoute3_47
import Proofs.Claims.Restated.Claim13beRoute3_49
import Proofs.Claims.Restated.Claim13beRoute3_51
import Proofs.Claims.Restated.Claim13beRoute3_53
import Proofs.Claims.Restated.Claim13beRoute3_54
import Proofs.Claims.Restated.Claim13beRoute3_54b
import Proofs.Claims.Restated.Vocabulary_Execution_Acceptance
import Proofs.Claims.Restated.Vocabulary_Execution_ExcludesRefute
import Proofs.Claims.Restated.Vocabulary_Execution_HealthyLocalFacts
import Proofs.Claims.Restated.Vocabulary_Execution_ReceiptCallsBase
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Claims.Restated.Vocabulary_Protocol_Evidence_ProvenanceBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_Agreement
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_Confirmation
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_RecoveryProposalConfirmationRead
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_GradeFormsProducers
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_ProposalParent
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_AcceptanceTiming
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_BlockAdmission
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_GoldfishVotePool
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_HMaxMonotone
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_JustificationBound
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreRoots
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_TickBridges
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_AdoptionTransport
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_Alignment
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_SlotInduction
import Proofs.Claims.Restated.Vocabulary_Protocol_ValidatorClient_BlockEmission
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_42c
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.Claim13beRoute3_54b
import Model.Conditions.RunVocabulary
import Model.Conditions.Vocabulary_Internal_Definitions_NamedDerived
import Model.Conditions.Vocabulary_Internal_Definitions_NamedLifecycle
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGradeQueries
import Model.Conditions.Vocabulary_Internal_Definitions_TickReads
import Model.Conditions.Vocabulary_Internal_Internal_GradeReads
import Model.Conditions.Vocabulary_Internal_Invariants
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
import Model.Conditions.Vocabulary_ModelVocabulary_Goldfish_ForkChoice
import Model.Conditions.Vocabulary_ModelVocabulary_Healing_Schedule
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_Evidence_ProvenanceBridge
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Adoption
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Agreement
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Confirmation
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_FinalityFilterRetention
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Model.Conditions.Vocabulary_Protocol_Grades_Main
import Model.Conditions.Vocabulary_Protocol_Grades_ProposalLifecycleCore
import Model.Conditions.Vocabulary_Protocol_Handlers_Blocks
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_Pool
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_Handlers_TickBridges
import Proofs.Vocabulary.Protocol.Schedule.RecoveryHandoffCore
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Conditions.Vocabulary_Statements_Instantiation_Proposals
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_25
import Proofs.Claims.Spec2Claims.Claim13beRoute3_55

/-!
# Goldfish vote settlement, vote adoption and confirmation supporters along one path

Theorems over a model `M : Record.Model V` with facts `facts : Record.Facts M`, read along the path
`W` of the bundle `AdmissibleFieldsOn`: Goldfish votes emitted from `lo` on are pooled and settled
in the confirmation and vote-duty stores, a block confirmed at slot `s` is carried into the vote of
slot `s + 1`, and a confirmed block has a committee supporter in `Hs`. The file also bounds the
proposer's `h_max` at its proposal and closes the active exact-height opening case.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

omit [DecidableEq V] [Fintype V] in
/-- For `Δ > 0`, if `a` and `b` are multiples of `Δ` and `a < b`, then `a + Δ ≤ b`. -/
private theorem add_delta_le_of_lt_emod₅₅ {Δ a b : Int} (hΔ : 0 < Δ) (ha : a % Δ = 0)
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

/-- A slot's vote time plus one delay is at most the slot's support cutoff. -/
private theorem vote_time_add_delta_le_support_cutoff₅₅ (facts : Record.Facts M) (S : Setup V)
    (s : Slot) : M.vote_time S.E s + S.E.Δ ≤ M.support_cutoff S.E s :=
  add_delta_le_of_lt_emod₅₅ S.E.Δ_pos (facts.sch.vote_time_emod_delta S s)
    (facts.sch.support_cutoff_emod_delta S s) (Restated.vote_time_lt_support_cutoff_l49 facts S s)

omit [DecidableEq V] [Fintype V] in
/-- In a run sorted by key, an event at index `j` with a time before `t` is among the first
    `strictEventIndex rho t` events. -/
private theorem lt_strict_of_time_lt₅₅ {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {j : Nat} {e : Record.Event V} (he : rho.events[j]? = some e) {t : Time} (ht : e.time < t) :
    j < strictEventIndex rho t := by
  by_contra hnot
  exact absurd ht (not_lt.mpr
    (Restated.le_time_of_index_ge_of_sorted hsorted
      (Nat.le_of_not_gt hnot) he))

/-- The late confirmation set of slot `s` of `st` staged to `s`'s confirmation time is the set of
    votes of `st`'s pool of `s` stamped before that time. -/
private theorem confLate_tickStore₅₅ (facts : Record.Facts M) (S : Setup V) (st : M.S) (s : Slot) :
    Restated.Vocabulary.Protocol.confLate M S.E
        (Restated.Vocabulary.Proofs.Optimistic.tickStore M S st (M.confirmation_time S.E s)) s =
      beforeCutoff st.timestamp_vote (M.confirmation_time S.E s) (M.store_pool st s) := by
  rw [Restated.Vocabulary.Protocol.confLate, Restated.Vocabulary.Proofs.Optimistic.tickStore,
    facts.sto.store_with_t_s_timestamp_vote]
  exact congrArg _ (facts.sto.pool_set_clock_slot st (M.confirmation_time S.E s) _ s)

/-- If the erasure of `B` is not in the tree of `st` and is in the tree of the store the core call
    on `B` returns, then `B` is among that store's named blocks. -/
private theorem core_new_body₅₅ (facts : Record.Facts M) (S : Setup V) (st : M.NS)
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
    on `B` returns, then `B` is among the named blocks of the store the block call on `B` returns. -/
private theorem on_block_new_body₅₅ (facts : Record.Facts M) (S : Setup V) (st : M.NS)
    (B : NamedBlock V) (hnew : B.erase ∉ st.core.T)
    (hpost : B.erase ∈ (M.postCore S st B).core.T) :
    B ∈ (M.on_block_with .alsoCarried S.E S.hc S.cfg st B).bodies := by
  have hheld := core_new_body₅₅ facts S st B hnew hpost
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
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- Under the bundle along `W`, if every event before index `n` is at a time at most `T`, `u` is in
    a slot's list of `w`'s store in `W n` or is included in a body that store holds, and `u`'s
    sender is in `Hs T`, then that sender emitted `u` along `W`. -/
theorem core_emits_of_voteVisibleOn (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int} {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    (w : V) (n : Nat) {T : Time}
    (hT : ∀ (j : Nat) (e : Record.Event V), j < n → rho.events[j]? = some e → e.time ≤ T)
    {u : GoldfishVote V}
    (hu : (∃ k : Slot, u ∈ (W n w).st.core.gf_votes k) ∨ ∃ B ∈ (W n w).st.bodies, u ∈ B.gf_votes)
    (hx : u.val_index ∈ Hs T) :
    ∃ t : Time, Restated.Vocabulary.Execution.NamedRun.emits M S rho W u.val_index (Object.gfVote u) t :=
  Restated.named_emits_of_voteVisibleOn facts S Hs Xb hf hHs w n hT hu hx

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- Under the bundle along `W`, if every event before index `n` is at a time at most `T`, `u` is in
    `w`'s slot-`k` list in `W n`, and `u`'s sender is in `Hs T`, then that sender emitted `u` along
    `W`. -/
theorem honestVote_emitted_of_mem_pool_stateBeforeOn (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    (Hs : Int → Finset V) (Xb : Finset V) {lo : Int} {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    (w : V) (n : Nat) (k : Slot) {T : Time}
    (hT : ∀ (j : Nat) (e : Record.Event V), j < n → rho.events[j]? = some e → e.time ≤ T)
    {u : GoldfishVote V}
    (hmem : u ∈ (W n w).st.gf_votes k)
    (hx : u.val_index ∈ Hs T) :
    ∃ t : Time, Restated.Vocabulary.Execution.NamedRun.emits M S rho W u.val_index (Object.gfVote u) t :=
  Restated.core_emits_of_voteVisibleOn facts S Hs Xb hf hHs w n hT (Or.inl ⟨k, hmem⟩) hx

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- Under the bundle along `W`, if every event before index `n` is at a time at most `T` and
    `x ∈ Hs T`, then `x` does not equivocate in the slot-`k` pool of `w`'s store in `W n`. -/
theorem core_pool_no_honest_equivocationOn (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    (Hs : Int → Finset V) (Xb : Finset V) {lo : Int} {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    (w : V) (n : Nat) {T : Time}
    (hT : ∀ (j : Nat) (e : Record.Event V), j < n → rho.events[j]? = some e → e.time ≤ T)
    (k : Slot) {x : V} (hx : x ∈ Hs T) :
    M.equivocates (M.store_pool (W n w).st.core k) x = false :=
  Restated.pool_no_honest_equivocation_of_coreOn facts S Hs Xb hf hHs w n hT k hx

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- Under the bundle along `W`, if `w` handles the vote `u` of slot `s > 0` at `t` with
    `vote_time s ≤ t < support_cutoff s` and `t < Gamma`, and `u`'s author and `w` are in `Hs t`,
    then for some event `i` before `Gamma`, `w`'s pool of slot `u.slot` in `W (i + 1)`, cut at
    `Gamma`, holds `u` or shows `u`'s author equivocating. -/
theorem actual_gfVote_settled_before_deadlineOn_RecoveryHandoffCore (facts : Record.Facts M)
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
          u.val_index = true) :=
  Restated.actual_gfVote_settled_before_deadlineOn_RecoveryOpeningFrontierRunBlock facts S Hs Xb hf hHs
    hactual hs hus hval hw hgat hlo hcut hdeadline

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- Under the bundle along `W`, if `w ∈ Hs t` handles the vote `u` of slot `s` at `t` with
    `proposal_time s ≤ t < view_freeze s` and `t < Gamma`, then for some event `i` before `Gamma`,
    `w`'s pool of slot `u.slot` in `W (i + 1)`, cut at `Gamma`, holds `u` or shows `u`'s author
    equivocating. -/
theorem actual_gfVote_settled_before_view_freezeOn_RecoveryHandoffCore (facts : Record.Facts M)
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
          u.val_index = true) :=
  Restated.actual_gfVote_settled_before_view_freezeOn_RecoveryOpeningFrontierRunBlock facts S Hs Xb hf hHs
    hactual hus hw hgat hlo hhi hdeadline

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- Under the bundle along `W`, if `v` and `w` are in `Hs (support_cutoff s)`, `v` emits the vote
    `u` of slot `s > 0` at `vote_time s`, and `w` handles `u` at a time in
    `[vote_time s, support_cutoff s)`, then for some event `j` before `support_cutoff s`, `u` is in
    `w`'s slot-`s` list in `W (j + 1)` with a stamp before `support_cutoff s`. -/
theorem gfVote_pooled_before_freeze_of_broadcastOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    {v : V} {s : Slot} (hv : v ∈ Hs (M.support_cutoff S.E s)) (hs : 0 < s)
    {u : GoldfishVote V}
    (hemit : Restated.Vocabulary.Execution.NamedRun.emits M S rho W v (Object.gfVote u)
      (M.vote_time S.E s))
    (hus : u.slot = s) {w : V} (hw : w ∈ Hs (M.support_cutoff S.E s))
    (hreceive : ∃ t', M.vote_time S.E s ≤ t' ∧
      t' < M.support_cutoff S.E s ∧
      ∃ j : Nat, Restated.Vocabulary.Execution.NamedRun.actualHandlesAt M S rho W j w (Object.gfVote u) t')
    (hgat : lo ≤ M.vote_time S.E s) :
    ∃ (j : Nat) (e : Record.Event V), rho.events[j]? = some e ∧
      e.time < M.support_cutoff S.E s ∧
      u ∈ (W (j + 1) w).st.core.gf_votes s ∧
      ∃ c : Stamp,
        (W (j + 1) w).st.core.timestamp_vote u = some c ∧
          c < (M.support_cutoff S.E s : Stamp) := by
  obtain ⟨-, -, hvalv, -⟩ := Restated.Vocabulary.Proofs.Optimistic.emits_gfVote_shape facts S W hemit (fun i => facts.ndRun.stateBeforeOf_reachedNode S rho i (W i) (hf.onePath i).1 _) (fun i => facts.ndRun.stateBeforeOf_runs_as S rho i (W i) (hf.onePath i).1 _)
  have hval : u.val_index ∈ Hs (M.support_cutoff S.E s) := by
    rw [hvalv]
    exact hv
  obtain ⟨t', hlo, hhi, j, hactual⟩ := hreceive
  obtain ⟨i, e, he, hearly, hsettled⟩ :=
    Restated.actual_gfVote_settled_before_deadlineOn_RecoveryHandoffCore facts S Hs Xb hf hHs hactual
      hs hus (hHs _ _ hhi.le hval) (hHs _ _ hhi.le hw) hgat hlo hhi hhi
  rcases hsettled with hmem | hequiv
  · rw [mem_beforeCutoff_iff] at hmem
    obtain ⟨hpool, hstamp⟩ := hmem
    obtain ⟨c, hc, hc'⟩ := exists_stamp_of_stampedBefore hstamp
    refine ⟨i, e, he, hearly, ?_, c, hc, hc'⟩
    rw [hus] at hpool
    exact (facts.sto.mem_store_pool_iff _ _ _).mp hpool
  · have hfull : M.equivocates
        (M.store_pool (W (i + 1) w).st.core u.slot)
        u.val_index = true :=
      facts.sch.equivocates_mono (by
        intro x hx
        exact ((mem_beforeCutoff_iff _ _ _ _).mp hx).1) u.val_index hequiv
    have hno := Restated.core_pool_no_honest_equivocationOn facts S Hs Xb hf hHs w (i + 1)
      (T := M.support_cutoff S.E s)
      (fun k e' hk he' =>
        le_of_lt (lt_of_le_of_lt (Restated.time_le_of_index_lt_succ_eventOn facts S Hs Xb hf he k e' hk he')
          hearly))
      u.slot hval
    rw [hno] at hfull
    simp at hfull

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- Under the bundle along `W`, if `v` and `w` are in `Hs (support_cutoff s)`, `lo ≤ vote_time s`,
    `v` emits the vote `u` of slot `s > 0` at `vote_time s`, and `support_cutoff s` is inside the
    horizon, then for some event `j` before `support_cutoff s`, `u` is in `w`'s slot-`s` list in
    `W (j + 1)` with a stamp before `support_cutoff s`. -/
theorem gfVote_pooled_before_freeze_after_gstOn (facts : Record.Facts M)
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
  have hvdCut := vote_time_add_delta_le_support_cutoff₅₅ facts S s
  have hvtCut := le_of_lt (Restated.vote_time_lt_support_cutoff_l49 facts S s)
  apply Restated.gfVote_pooled_before_freeze_of_broadcastOn facts S Hs Xb hf hHs hv hs hemit hus hw _
    hpost
  obtain ⟨t', hlo, hhi, j, hactual⟩ :=
    Restated.broadcast_after_gstOn facts S Hs Xb hf (hHs _ _ hvtCut hv) (hHs _ _ hvdCut hw) hpost hemit
      (le_trans hvdCut hhor) (fun B hB => by cases hB)
  exact ⟨t', hlo, lt_of_lt_of_le hhi hvdCut, j, hactual⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- Under the bundle along `W`, if `v` and `w` are in `Hs (support_cutoff s)`, `lo ≤ vote_time s`,
    `v` emits the vote `u` of slot `s > 0` at `vote_time s`, and `support_cutoff s` is inside the
    horizon and at most `Gamma` and `Gamma'`, then `u` is in the slot-`s` pool of `w`'s store in
    `W (strictEventIndex rho Gamma)`, cut at `Gamma'`. -/
theorem gfVote_in_cutoff_view_after_gstOn (facts : Record.Facts M)
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
    u ∈ beforeCutoff (W (strictEventIndex rho Gamma) w).st.timestamp_vote Gamma'
      ((W (strictEventIndex rho Gamma) w).st.pool s) := by
  obtain ⟨j, e, hj, hjt, hmem, c, hc, hlt⟩ :=
    Restated.gfVote_pooled_before_freeze_after_gstOn facts S Hs Xb hf hHs hv hs hpost hemit hus hw
      hhor
  have hjN : j < strictEventIndex rho Gamma :=
    lt_strict_of_time_lt₅₅ hf.sorted hj (lt_of_lt_of_le hjt hGamma)
  have hcarry : Restated.Vocabulary.Protocol.PoolCarry M (W (j + 1) w).st.core
      (W (strictEventIndex rho Gamma) w).st.core :=
    Restated.pool_carryOn facts S Hs Xb hf w _ hjN
  show u ∈ beforeCutoff (W (strictEventIndex rho Gamma) w).st.core.timestamp_vote Gamma'
      (M.store_pool (W (strictEventIndex rho Gamma) w).st.core s)
  rw [mem_beforeCutoff_iff]
  refine ⟨?_, ?_⟩
  · exact (facts.sto.mem_store_pool_iff _ _ _).mpr (hcarry.mem s u hmem)
  exact stampedBefore_of_lt (hcarry.stamp u c hc)
    (lt_of_lt_of_le hlt (by exact_mod_cast hGamma'))

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- Under the bundle along `W`, if `lo ≤ proposal_time s`, `v ∈ Hs t` accepts the vote `u` of slot
    `s` at `t` with `proposal_time s ≤ t < support_cutoff s`, `w ∈ Hs (t + Δ)`, and `view_freeze s`
    is inside the horizon, then `w`'s vote-duty store of slot `s + 1`, cut at `view_freeze s`, holds
    `u` in its pool of `s` or shows `u`'s author equivocating there. -/
theorem accepted_gfVote_forward_settled_at_voteDuty_after_gstOn_RecoveryHandoffCore (facts : Record.Facts M)
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
        u.val_index = true :=
  Restated.accepted_gfVote_forward_settled_at_voteDuty_after_gstOn_RecoveryOpeningFrontierRunBlock facts
    S Hs Xb hf hHs hpost hacc hv hw hus hlo hhi hhor

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- Under the bundle along `W`, if `lo ≤ proposal_time s`, `w ∈ Hs t` handles the vote `u` of slot
    `s` at `t` with `proposal_time s ≤ t < confirmation_time s`, and `confirmation_time s` is inside
    the horizon, then `u` is in the late confirmation set of `s` of `w`'s confirmation store, or
    `u`'s author equivocates there. -/
theorem actual_gfVote_settled_at_confStore_after_gstOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    {j : Nat} {w : V} {u : GoldfishVote V} {s : Slot} {t : Time}
    (hpost : lo ≤ M.proposal_time S.E s)
    (hactual : Restated.Vocabulary.Execution.NamedRun.actualHandlesAt M S rho W j w (Object.gfVote u) t)
    (hus : u.slot = s) (hw : w ∈ Hs t)
    (hlo : M.proposal_time S.E s ≤ t)
    (hhi : t < M.confirmation_time S.E s)
    (_hhor : M.confirmation_time S.E s ≤ rho.horizon) :
    u ∈ Restated.Vocabulary.Protocol.confLate M S.E
        (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
          (W (strictEventIndex rho (M.confirmation_time S.E s)) w).st.core (M.confirmation_time S.E s)) s ∨
      M.equivocates
        (Restated.Vocabulary.Protocol.confLate M S.E
          (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
            (W (strictEventIndex rho (M.confirmation_time S.E s)) w).st.core (M.confirmation_time S.E s)) s)
        u.val_index = true := by
  have _hr_0 : M.reachedNode (W j w) := facts.ndRun.stateBeforeOf_reachedNode S rho j (W j) (hf.onePath j).1 w
  have _hv_0 : M.runs_as (W j w) w := facts.ndRun.stateBeforeOf_runs_as S rho j (W j) (hf.onePath j).1 w
  have _hr_1 : M.reachedNode (W (j + 1) w) := facts.ndRun.stateBeforeOf_reachedNode S rho (j + 1) (W (j + 1)) (hf.onePath (j + 1)).1 w
  have _hv_1 : M.runs_as (W (j + 1) w) w := facts.ndRun.stateBeforeOf_runs_as S rho (j + 1) (W (j + 1)) (hf.onePath (j + 1)).1 w
  have hW := hf.onePath
  let Gamma := M.confirmation_time S.E s
  let N := strictEventIndex rho Gamma
  have hwProp : w ∈ Hs (M.proposal_time S.E s) := hHs _ _ hlo hw
  have carry_to_conf :
      ∀ (i : Nat) (e : Record.Event V),
        rho.events[i]? = some e → e.time < Gamma →
        (u ∈ beforeCutoff
            (W (i + 1) w).st.core.timestamp_vote Gamma
            (M.store_pool (W (i + 1) w).st.core u.slot) ∨
          M.equivocates
            (beforeCutoff
              (W (i + 1) w).st.core.timestamp_vote Gamma
              (M.store_pool (W (i + 1) w).st.core u.slot))
            u.val_index = true) →
        u ∈ Restated.Vocabulary.Protocol.confLate M S.E
            (Restated.Vocabulary.Proofs.Optimistic.tickStore M S (W N w).st.core Gamma) s ∨
          M.equivocates
            (Restated.Vocabulary.Protocol.confLate M S.E
              (Restated.Vocabulary.Proofs.Optimistic.tickStore M S (W N w).st.core Gamma) s)
            u.val_index = true := by
    intro i e hi hetime hlocal
    have hiN : i < N := lt_strict_of_time_lt₅₅ hf.sorted hi hetime
    have hcarry : Restated.Vocabulary.Protocol.PoolCarry M (W (i + 1) w).st.core (W N w).st.core :=
      Restated.pool_carryOn facts S Hs Xb hf w N (Nat.succ_le_of_lt hiN)
    rw [confLate_tickStore₅₅ facts S]
    rw [hus] at hlocal
    rcases hlocal with hmem | hequiv
    · exact Or.inl (Restated.Vocabulary.Protocol.beforeCutoff_subset_of_poolCarry facts hcarry s Gamma hmem)
    · exact Or.inr (facts.sch.equivocates_mono
        (Restated.Vocabulary.Protocol.beforeCutoff_subset_of_poolCarry facts hcarry s Gamma) u.val_index hequiv)
  by_cases hfreeze : t < M.view_freeze S.E s
  · obtain ⟨i, e, hi, hetime, hlocal⟩ :=
      Restated.actual_gfVote_settled_before_view_freezeOn_RecoveryHandoffCore facts S Hs Xb hf hHs
        hactual hus hw hpost hlo hfreeze hhi
    exact carry_to_conf i e hi hetime hlocal
  · obtain ⟨hindex, e, he, hnode, htime⟩ := hactual
    rcases hindex with (⟨t', htick', out, hout, hWout, hem⟩ | ⟨t', hdeliver⟩) |
        ⟨B, j', before, hcall⟩
    · have heq : Record.Event.tick w t' = e := Option.some.inj (htick'.symm.trans he)
      have htt : t' = t := (congrArg Record.Event.time heq).trans htime
      subst t'
      have hemit : Restated.Vocabulary.Execution.NamedRun.emits M S rho W w (Object.gfVote u) t :=
        ⟨j, htick', out, hout, hWout, hem⟩
      obtain ⟨-, ht', -, hus'⟩ := Restated.Vocabulary.Proofs.Optimistic.emits_gfVote_shape facts S W hemit (fun i => facts.ndRun.stateBeforeOf_reachedNode S rho i (W i) (hf.onePath i).1 _) (fun i => facts.ndRun.stateBeforeOf_runs_as S rho i (W i) (hf.onePath i).1 _)
      have hslot : S.E.slotOf t = s := by rw [← hus', hus]
      have htVote : t = M.vote_time S.E s := by
        simpa only [hslot] using ht'
      exact absurd (by
        rw [htVote]
        exact lt_trans (Restated.vote_time_lt_support_cutoff_l49 facts S s)
          (facts.sch.Optimistic_support_cutoff_lt_view_freeze S.E s)) hfreeze
    · have heq : Record.Event.deliver w (Object.gfVote u) t' = e :=
        Option.some.inj (hdeliver.symm.trans he)
      have htt : t' = t := (congrArg Record.Event.time heq).trans htime
      subst t'
      exact Restated.gfVote_delivery_settled_at_confStoreOn facts S Hs Xb hf hwProp hpost hdeliver hus
        hlo hhi
    · obtain ⟨hblock, hnew, hcore, huindex⟩ := hcall
      have huB : u ∈ B.gf_votes := List.mem_of_getElem? huindex
      have huErase : u ∈ B.erase.gf_votes := by
        rwa [Proofs.NamedWire.erase_goldfish_votes]
      rcases hblock with
          ⟨t', hdeliver, hbefore⟩ | ⟨t', htick', ⟨out, hout, hWout, hBemit⟩, hbefore⟩
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
        have hpostBodies := on_block_new_body₅₅ facts S (W j w).st B hnew hcore
        have hstamps : Restated.Vocabulary.Protocol.PoolStamps M (W j w).st.core :=
          Restated.poolStamps_stateBeforeOn facts S Hs Xb hf w j
        have hslot : (W j w).st.core.s = s ∨ (W j w).st.core.s = s + 1 :=
          Restated.delivery_store_slot_before_confirmationOn facts S Hs Xb hf hwProp hpost hdeliver
            hlo hhi
        have hfresh : ¬ u.slot < (W j w).st.core.s - 1 := by
          rcases hslot with hs | hs
          · rw [hus, hs]
            exact Nat.not_lt.mpr (Nat.sub_le s 1)
          · rw [hus, hs, Nat.add_sub_cancel]
            exact Nat.lt_irrefl s
        have hfuture : ¬ (W j w).st.core.s < u.slot := by
          rcases hslot with hs | hs
          · rw [hus, hs]
            exact Nat.lt_irrefl s
          · rw [hus, hs]
            exact Nat.not_lt.mpr (Nat.le_add_right s 1)
        have hcommittee : u.val_index ∈ S.E.committee u.slot :=
          (hf.wire _ w (Object.block B) t hdeliver).1 B rfl |>.2.2 u huB
        have hclock : (W j w).st.core.t < Gamma :=
          lt_of_le_of_lt (Restated.store_time_le_event_timeOn facts S Hs Xb hf hdeliver w) hhi
        have hlocal := Restated.Vocabulary.Proofs.Optimistic.block_carried_before_deadline_or_equivocates facts
          S (W j w).st B u Gamma hstamps hpreBodies hpostBodies huErase hcommittee
          hfresh hfuture hclock
        let final := M.on_block_with .alsoCarried S.E S.hc S.cfg (W j w).st B
        have hfinalEq : (W (j + 1) w).st = M.make_grades_compatible_with_finalized final := by
          rw [Restated.Vocabulary.Proofs.NamedReceiptCallsBase.delivery_result facts S rho hdeliver (W j) (hW j).1
              (hf.receipt_outcome _ _ _ _ hdeliver) (W (j + 1)) (hW j).2,
            facts.nd.process_block]
        have hstampEq : (W (j + 1) w).st.core.timestamp_vote = final.core.timestamp_vote := by
          rw [hfinalEq, facts.nd.make_grades_compatible_with_finalized_core_timestamp_vote]
        have hpoolEq : ∀ k : Slot,
            M.store_pool (W (j + 1) w).st.core k = M.store_pool final.core k := by
          intro k
          rw [hfinalEq]
          exact congrFun (facts.nd.make_grades_compatible_with_finalized_core_pool _) k
        have hlocal' : u ∈ beforeCutoff
            (W (j + 1) w).st.core.timestamp_vote Gamma
            (M.store_pool (W (j + 1) w).st.core u.slot) ∨
            M.equivocates
              (beforeCutoff
                (W (j + 1) w).st.core.timestamp_vote Gamma
                (M.store_pool (W (j + 1) w).st.core u.slot))
              u.val_index = true := by
          rw [hstampEq, hpoolEq]
          exact hlocal
        exact carry_to_conf j e he (by simpa only [htime] using hhi) hlocal'
      · have heq : Record.Event.tick w t' = e :=
          Option.some.inj (htick'.symm.trans he)
        have htt : t' = t := (congrArg Record.Event.time heq).trans htime
        subst t'
        subst hbefore
        -- The proposal's votes are the votes of `w`'s pool before the tick.
        have hcallEq := Restated.Vocabulary.Proofs.NamedReceiptCallsBase.self_proposal_call facts S rho
          htick' (W j) (hW j).1 out hout hBemit
        obtain ⟨c', hc'⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc (W j w).st.core.toHealing t
          (W j w).cache
        have _hr_p := facts.ndRun.stateBeforeOf_reachedNode S rho j (W j) (hW j).1 w
        have _hv_p := facts.ndRun.stateBeforeOf_runs_as S rho j (W j) (hW j).1 w
        obtain ⟨D, hD⟩ := facts.dt.propose_block_with_nonempty S w (W j w) t out hout
          (facts.nd.block_mem_on_tick_emit S w (W j w) t out hout hBemit).1.1
          (facts.nd.block_mem_on_tick_emit S w (W j w) t out hout hBemit).1.2.1
          (facts.nd.block_mem_on_tick_emit S w (W j w) t out hout hBemit).1.2.2
          (facts.nd.block_mem_on_tick_emit_awake S w (W j w) t out hout hBemit) c' hc'
        have hDeq := hcallEq c' hc' D hD
        obtain ⟨o, ho⟩ := facts.dt.proposal_with_nonempty (M.frameContract c') .poolAndCarried S.E
          S.hc (S.node w) (M.ns_setClock S.E (W j w).st t)
        have hgf : B.gf_votes = (M.ns_setClock S.E (W j w).st t).core.gf_votes
            ((M.ns_setClock S.E (W j w).st t).core.s - 1) :=
          facts.dt.proposal_with_gf_votes _ .poolAndCarried S.E S.hc (S.node w) _ o ho
            (facts.dt.proposal_with_eq_of_propose_block_with_snd _ _ _ _ _ _ D hD
              (by rw [hDeq]) o ho)
        rw [facts.hd.setClock_core_gf_votes] at hgf
        have hstamps := Restated.poolStamps_stateBeforeOn facts S Hs Xb hf w j
        have huPool0 : u ∈ (W j w).st.core.gf_votes ((M.ns_setClock S.E (W j w).st t).core.s - 1) := by
          rw [← hgf]
          exact huB
        have huPool : u ∈ (W j w).st.core.gf_votes s := by
          have hslotIdx := hstamps.slot _ u huPool0
          rw [← hus, hslotIdx]
          exact huPool0
        obtain ⟨c, hc⟩ : ∃ c : Stamp, (W j w).st.core.timestamp_vote u = some c :=
          Option.isSome_iff_exists.mp (hstamps.stamped s u huPool)
        have hclock : (W j w).st.core.t ≤ t :=
          Restated.store_time_le_event_timeOn facts S Hs Xb hf htick' w
        have hcGamma : c < (Gamma : Stamp) :=
          lt_of_le_of_lt (hstamps.bounded u c hc) (WithBot.coe_lt_coe.mpr (lt_of_le_of_lt hclock hhi))
        have hjN : j < N := lt_strict_of_time_lt₅₅ hf.sorted he (by simpa only [htime] using hhi)
        have hcarry : Restated.Vocabulary.Protocol.PoolCarry M (W j w).st.core (W N w).st.core :=
          Restated.pool_carryOn facts S Hs Xb hf w N (le_of_lt hjN)
        apply Or.inl
        rw [confLate_tickStore₅₅ facts S, mem_beforeCutoff_iff, facts.sto.mem_store_pool_iff]
        exact ⟨hcarry.mem s u huPool, stampedBefore_of_lt (hcarry.stamp u c hc) hcGamma⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- `actual_gfVote_settled_at_confStore_after_gstOn`, for a vote `w` processes. -/
theorem gfVote_processes_settled_at_confStore_after_gstOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    {w : V} {u : GoldfishVote V} {s : Slot} {t : Time} {j : Nat}
    (hw : w ∈ Hs t)
    (hpost : lo ≤ M.proposal_time S.E s)
    (hproc : Restated.Vocabulary.Execution.NamedRun.actualHandlesAt M S rho W j w (Object.gfVote u) t)
    (hus : u.slot = s)
    (hlo : M.proposal_time S.E s ≤ t)
    (hhi : t < M.confirmation_time S.E s)
    (hhor : M.confirmation_time S.E s ≤ rho.horizon) :
    u ∈ Restated.Vocabulary.Protocol.confLate M S.E
        (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
          (W (strictEventIndex rho (M.confirmation_time S.E s)) w).st.core (M.confirmation_time S.E s)) s ∨
      M.equivocates
        (Restated.Vocabulary.Protocol.confLate M S.E
          (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
            (W (strictEventIndex rho (M.confirmation_time S.E s)) w).st.core (M.confirmation_time S.E s)) s)
        u.val_index = true :=
  Restated.actual_gfVote_settled_at_confStore_after_gstOn facts S Hs Xb hf hHs hpost hproc hus hw hlo
    hhi hhor

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- Under the bundle along `W`, if `lo ≤ proposal_time s`, `w ∈ Hs t` accepts the vote `u` of slot
    `s` at `t` with `proposal_time s ≤ t < vote_time (s + 1)`, `v ∈ Hs (t + Δ)`, and
    `confirmation_time s` is inside the horizon, then `u` is in the late confirmation set of `s` of
    `v`'s confirmation store, or `u`'s author equivocates there. -/
theorem accepted_gfVote_backward_settled_at_confStore_after_gstOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    {v w : V} {i : Nat} {u : GoldfishVote V} {s : Slot} {t : Time}
    (hv : v ∈ Hs (t + S.E.Δ)) (hw : w ∈ Hs t)
    (hpost : lo ≤ M.proposal_time S.E s)
    (hacc : Restated.Vocabulary.Execution.NamedRun.acceptsAt M S rho W i w (Object.gfVote u) t)
    (hus : u.slot = s)
    (hlo : M.proposal_time S.E s ≤ t)
    (hhi : t < M.vote_time S.E (s + 1))
    (hhor : M.confirmation_time S.E s ≤ rho.horizon) :
    u ∈ Restated.Vocabulary.Protocol.confLate M S.E
        (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
          (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core (M.confirmation_time S.E s)) s ∨
      M.equivocates
        (Restated.Vocabulary.Protocol.confLate M S.E
          (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
            (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core (M.confirmation_time S.E s)) s)
        u.val_index = true := by
  have hrelayLe : t + S.E.Δ ≤ M.confirmation_time S.E s :=
    le_trans (Int.add_le_add_right hhi.le S.E.Δ)
      (facts.sch.vote_time_succ_add_delta_le_confirmation_time S.E s)
  have hvoteConf : M.vote_time S.E (s + 1) < M.confirmation_time S.E s :=
    lt_of_lt_of_le (Int.lt_add_of_pos_right _ S.E.Δ_pos)
      (facts.sch.vote_time_succ_add_delta_le_confirmation_time S.E s)
  by_cases halready :
      Restated.Vocabulary.Execution.Object.processed M (W (i + 1) v).st (Object.gfVote u) = true
  · obtain ⟨e, he, -, het⟩ := hacc.1.2
    have hmem : u ∈ (W (i + 1) v).st.core.gf_votes s := by
      have h1 : u ∈ (W (i + 1) v).st.core.gf_votes u.slot := by
        simpa only [Restated.Vocabulary.Execution.Object.processed, decide_eq_true_eq] using halready
      rw [hus] at h1
      exact h1
    have hstamps := Restated.poolStamps_stateBeforeOn facts S Hs Xb hf v (i + 1)
    obtain ⟨c, hc⟩ : ∃ c : Stamp, (W (i + 1) v).st.core.timestamp_vote u = some c :=
      Option.isSome_iff_exists.mp (hstamps.stamped s u hmem)
    have hclock : (W (i + 1) v).st.core.t ≤ e.time :=
      Restated.block_store_time_after_event_leOn facts S Hs Xb hf he v
    have hetConf : e.time < M.confirmation_time S.E s := by
      rw [het]
      exact lt_trans hhi hvoteConf
    have hcConf : c < (M.confirmation_time S.E s : Stamp) :=
      lt_of_le_of_lt (hstamps.bounded u c hc)
        (WithBot.coe_lt_coe.mpr (lt_of_le_of_lt hclock hetConf))
    have hiN : i < strictEventIndex rho (M.confirmation_time S.E s) :=
      lt_strict_of_time_lt₅₅ hf.sorted he hetConf
    have hcarry : Restated.Vocabulary.Protocol.PoolCarry M (W (i + 1) v).st.core
        (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core :=
      Restated.pool_carryOn facts S Hs Xb hf v _ (Nat.succ_le_of_lt hiN)
    apply Or.inl
    rw [confLate_tickStore₅₅ facts S, mem_beforeCutoff_iff, facts.sto.mem_store_pool_iff]
    exact ⟨hcarry.mem s u hmem, stampedBefore_of_lt (hcarry.stamp u c hc) hcConf⟩
  · have hunaccepted :
        Restated.Vocabulary.Execution.Object.processed M (W (i + 1) v).st (Object.gfVote u) = false :=
      Bool.eq_false_of_not_eq_true halready
    have hrelayHor : t + S.E.Δ ≤ rho.horizon := le_trans hrelayLe hhor
    have hpostAcceptance : lo ≤ t := le_trans hpost hlo
    obtain ⟨t', hcausal, hdeadline, j', hproc⟩ :=
      Restated.relay_gf_vote_after_gstOn facts S Hs Xb hf hw hv hpostAcceptance hacc
        hunaccepted hrelayHor
    have hbeforeConf : t' < M.confirmation_time S.E s := lt_of_lt_of_le hdeadline hrelayLe
    exact Restated.gfVote_processes_settled_at_confStore_after_gstOn facts
      S Hs Xb hf hHs (hHs _ _ hdeadline.le hv) hpost hproc hus (le_trans hlo hcausal)
      hbeforeConf hhor

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- Under the bundle along `W`, if `v ∈ Hs (confirmation_time s)`, `w ∈ Hs (vote_time (s + 1))`,
    `lo ≤ proposal_time s`, and `confirmation_time s` is inside the horizon, then every vote `u` of
    the pool of `s` of `w`'s vote-duty store is in the late confirmation set of `s` of `v`'s
    confirmation store, or `u`'s author equivocates there. -/
theorem targetPoolVote_settledAtSource_after_gstOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    {v w : V} {s : Slot}
    (hv : v ∈ Hs (M.confirmation_time S.E s))
    (hw : w ∈ Hs (M.vote_time S.E (s + 1)))
    (hpost : lo ≤ M.proposal_time S.E s)
    (hhor : M.confirmation_time S.E s ≤ rho.horizon)
    {u : GoldfishVote V}
    (hu : u ∈ M.store_pool (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1)) s) :
    u ∈ Restated.Vocabulary.Protocol.confLate M S.E
        (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
          (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core (M.confirmation_time S.E s)) s ∨
      M.equivocates
        (Restated.Vocabulary.Protocol.confLate M S.E
          (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
            (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core (M.confirmation_time S.E s)) s)
        u.val_index = true := by
  obtain ⟨i, t, hacc, hus, hlo, hhi⟩ :=
    Restated.targetPoolVoteAcceptedBeforeVoteOn facts S Hs Xb hf hu
  have hvt : v ∈ Hs (t + S.E.Δ) :=
    hHs _ _ (le_trans (Int.add_le_add_right hhi.le S.E.Δ)
      (facts.sch.vote_time_succ_add_delta_le_confirmation_time S.E s)) hv
  exact Restated.accepted_gfVote_backward_settled_at_confStore_after_gstOn facts
    S Hs Xb hf hHs hvt (hHs _ _ hhi.le hw) hpost hacc hus hlo hhi hhor

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- Under the hypotheses of `targetPoolVote_settledAtSource_after_gstOn`, a validator that
    equivocates in the pool of `s` of `w`'s vote-duty store equivocates in the late confirmation set
    of `s` of `v`'s confirmation store. -/
theorem targetPoolEquivocates_settledAtSource_after_gstOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    {v w : V} {s : Slot}
    (hv : v ∈ Hs (M.confirmation_time S.E s))
    (hw : w ∈ Hs (M.vote_time S.E (s + 1)))
    (hpost : lo ≤ M.proposal_time S.E s)
    (hhor : M.confirmation_time S.E s ≤ rho.horizon) {x : V}
    (hequiv : M.equivocates
      (M.store_pool (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1)) s) x = true) :
    M.equivocates
      (Restated.Vocabulary.Protocol.confLate M S.E
        (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
          (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core (M.confirmation_time S.E s)) s)
      x = true := by
  by_cases hsource : M.equivocates
      (Restated.Vocabulary.Protocol.confLate M S.E
        (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
          (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core (M.confirmation_time S.E s)) s)
      x = true
  · exact hsource
  have hsub :
      M.votes_by
          (M.store_pool (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
            (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1)) s) x ⊆
        M.votes_by
          (Restated.Vocabulary.Protocol.confLate M S.E
            (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
              (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core (M.confirmation_time S.E s)) s)
          x := by
    intro u hu
    rw [facts.sch.mem_votes_by_iff] at hu ⊢
    refine ⟨?_, hu.2⟩
    rcases Restated.targetPoolVote_settledAtSource_after_gstOn facts
        S Hs Xb hf hHs hv hw hpost hhor hu.1 with hmem | hequivSource
    · exact hmem
    · rw [hu.2] at hequivSource
      exact False.elim (hsource hequivSource)
  obtain ⟨u, hu, u', hu', hne, hux, hu'x⟩ := (facts.sch.equivocates_eq_true_iff _ x).mp hequiv
  have h1 := hsub ((facts.sch.mem_votes_by_iff _ x u).mpr ⟨hu, hux⟩)
  have h2 := hsub ((facts.sch.mem_votes_by_iff _ x u').mpr ⟨hu', hu'x⟩)
  rw [facts.sch.mem_votes_by_iff] at h1 h2
  exact (facts.sch.equivocates_eq_true_iff _ x).mpr ⟨u, h1.1, u', h2.1, hne, hux, hu'x⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- Under the hypotheses of `targetPoolVote_settledAtSource_after_gstOn`, every vote of every
    outcome of the slot-`(s + 1)` voter view of `w`'s vote-duty store is in the late confirmation
    set of `s` of `v`'s confirmation store, or its author equivocates there. -/
theorem targetRawVote_settledAtSource_after_gstOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    {v w : V} {s : Slot}
    (hv : v ∈ Hs (M.confirmation_time S.E s))
    (hw : w ∈ Hs (M.vote_time S.E (s + 1)))
    (hpost : lo ≤ M.proposal_time S.E s)
    (hhor : M.confirmation_time S.E s ≤ rho.horizon) :
    ∀ Y, M.voter_view S.E
        (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1))).toFG.toSG.toGoldfishStore
          (s + 1) ⇢ Y →
    ∀ u ∈ Y,
      u ∈ Restated.Vocabulary.Protocol.confLate M S.E
          (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
            (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core (M.confirmation_time S.E s)) s ∨
        M.equivocates
          (Restated.Vocabulary.Protocol.confLate M S.E
            (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
              (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core (M.confirmation_time S.E s)) s)
          u.val_index = true := by
  have hΔ := S.E.Δ_pos
  have hwFreeze : w ∈ Hs (M.view_freeze S.E s) :=
    hHs _ _ (facts.sch.view_freeze_lt_vote_time_succ S.E s).le hw
  have hwNext : w ∈ Hs (M.proposal_time S.E (s + 1)) :=
    hHs _ _ (facts.sch.proposal_time_lt_vote_time S.E (s + 1)).le hw
  have hloFreeze : lo ≤ M.view_freeze S.E s :=
    le_trans hpost (le_of_lt
      (((facts.sch.proposal_time_lt_vote_time S.E s).trans
        (Restated.vote_time_lt_support_cutoff_l49 facts S s)).trans
        (facts.sch.Optimistic_support_cutoff_lt_view_freeze S.E s)))
  have hloNext : lo ≤ M.proposal_time S.E (s + 1) :=
    hpost.trans (facts.sch.proposal_time_mono S.E (Nat.le_succ s))
  intro Y hY u hu
  rcases facts.fc.voter_view_cases_beforeCutoff S.E _ _ Y hY hu with hreceipt | ⟨B, hBT, hBs, huList, hus0⟩
  · rw [Nat.add_sub_cancel, facts.sto.toHealing_gs_timestamp_vote, facts.sto.toHealing_gs_pool] at hreceipt
    obtain ⟨i, t, hacc, hus, hlo, hhi⟩ :=
      Restated.targetReceiptVotesAcceptedInWindow_of_admissibleOn_Protocol facts S Hs Xb hf s
        hwFreeze hloFreeze u hreceipt
    have hhi' : t < M.vote_time S.E (s + 1) :=
      lt_trans hhi (facts.sch.view_freeze_lt_vote_time_succ S.E s)
    have hvt : v ∈ Hs (t + S.E.Δ) :=
      hHs _ _ (le_trans (Int.add_le_add_right hhi'.le S.E.Δ)
        (facts.sch.vote_time_succ_add_delta_le_confirmation_time S.E s)) hv
    exact Restated.accepted_gfVote_backward_settled_at_confStore_after_gstOn facts
      S Hs Xb hf hHs hvt (hHs _ _ hhi'.le hw) hpost hacc hus hlo hhi' hhor
  · have hus : u.slot = s := by
      simpa only [Nat.add_sub_cancel] using hus0
    rw [facts.sto.toHealing_gs_T] at hBT
    rcases Restated.targetCarrierVote_settledInPoolOn facts
        S Hs Xb hf hwNext hloNext hBT hBs huList hus with hpool | hequiv
    · exact Restated.targetPoolVote_settledAtSource_after_gstOn facts
        S Hs Xb hf hHs hv hw hpost hhor hpool
    · exact Or.inr
        (Restated.targetPoolEquivocates_settledAtSource_after_gstOn facts
          S Hs Xb hf hHs hv hw hpost hhor hequiv)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open scoped DC

/-- The store `tickStore` stages from `n`'s core store at `t` has the tree of `n`'s core store. -/
private theorem tickStore_T₅₅b (facts : Record.Facts M) {S : Setup V} (n : M.N) (t : Time) :
    (Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core t).T = n.st.core.T := by
  rw [Restated.Vocabulary.Proofs.Optimistic.tickStore,
    ← facts.hd.setClock_core_eq_store_with_t_s S.E n.st t, facts.hd.Sts_setClock_core_T]

/-- The store `tickStore` stages from `n`'s core store at `t` has the block stamps of `n`'s core
    store. -/
private theorem tickStore_timestamp_block₅₅b (facts : Record.Facts M) {S : Setup V} (n : M.N)
    (t : Time) :
    (Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core t).timestamp_block =
      n.st.core.timestamp_block := by
  rw [Restated.Vocabulary.Proofs.Optimistic.tickStore,
    ← facts.hd.setClock_core_eq_store_with_t_s S.E n.st t, facts.hd.setClock_core_timestamp_block]

/-- A slot's support cutoff plus one delay is at most the slot's view freeze. -/
private theorem support_cutoff_add_delta_le_view_freeze₅₅b (facts : Record.Facts M) (S : Setup V)
    (s : Slot) : M.support_cutoff S.E s + S.E.Δ ≤ M.view_freeze S.E s := by
  obtain ⟨k, hk⟩ := (facts.sch.publicTime_iff S (M.view_freeze S.E s)).mpr
    ⟨s, Or.inr (Or.inr (Or.inr rfl))⟩
  have hb : M.view_freeze S.E s % S.E.Δ = 0 := by
    rw [hk]
    exact Int.mul_emod_left _ _
  exact add_delta_le_of_lt_emod₅₅ S.E.Δ_pos (facts.sch.support_cutoff_emod_delta S s) hb
    (facts.sch.Optimistic_support_cutoff_lt_view_freeze S.E s)

/-- If `f <$> m` can return `b`, then `m` can return some `a` with `f a = b`. -/
private theorem returns_map_elim₅₅b {α β : Type} (f : α → β) (m : DC.NDRE α) (b : β)
    (h : (f <$> m) ⇢ b) : ∃ a, m ⇢ a ∧ f a = b := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image] at h
  obtain ⟨e, he, hb⟩ := h
  cases e with
  | ok a => exact ⟨a, he, by simpa [Except.map] using hb⟩
  | error err => simp [Except.map] at hb

/-- For a path `W` of `rho`, `W (m + k)` is among the worlds the events `m` to `m + k - 1` of `rho`
    lead to from `W m`. -/
private theorem onePath_reach₅₅b {S : Setup V} {rho : Record.Run V}
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

/-- For a path `W` of `rho` and `m ≤ n`, `W n` is among the worlds the events `m` to `n - 1` of
    `rho` lead to from `W m`. -/
private theorem onePath_slice₅₅b {S : Setup V} {rho : Record.Run V}
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) {m n : Nat}
    (hmn : m ≤ n) :
    W n ∈ ((rho.events.drop m).take (n - m)).foldlM (Record.worldStepOf M S) (W m) := by
  have h := onePath_reach₅₅b W hW m (n - m)
  rwa [Nat.add_sub_of_le hmn] at h

omit [DecidableEq V] [Fintype V] in
/-- In a run sorted by key, an event among the first `strictEventIndex rho t` events has a time
    before `t`. -/
private theorem time_lt_of_lt_strict₅₅b {rho : Record.Run V}
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

/-- In a run sorted by key, the worlds strictly before `t` are the worlds before the event at index
    `strictEventIndex rho t`. -/
private theorem stateBeforeTime_eq_strict₅₅b (S : Setup V) (rho : Record.Run V)
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

/-- In a run sorted by key, the world of a path `W` before the event at index
    `strictEventIndex rho t` is a world strictly before `t`. -/
private theorem mem_stateBeforeTime_along₅₅b {S : Setup V} {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (t : Time) :
    W (strictEventIndex rho t) ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t := by
  rw [stateBeforeTime_eq_strict₅₅b S rho hsorted]
  exact (hW _).1

/-- If the named store `st` satisfies the confirmation-membership invariant, so does `st` with the
    cache `c` written into it. -/
private theorem invariant_store_with_cache₅₅b (facts : Record.Facts M) (E : Env V)
    (cfg : DecoupledConsensusModel.Protocol.HeightConfig) (st : M.NS) (c : M.Cache)
    (h : Restated.Vocabulary.Proofs.NamedConfirmationMembership.Invariant M E cfg st) :
    Restated.Vocabulary.Proofs.NamedConfirmationMembership.Invariant M E cfg
      (M.store_with_cache st c) := by
  simp only [Restated.Vocabulary.Proofs.NamedConfirmationMembership.Invariant,
    Restated.Vocabulary.Proofs.NamedStoreRoots.Invariant, Restated.Vocabulary.Proofs.NamedStore.Coherent,
    Restated.Vocabulary.Proofs.NamedStore.TreeView, Restated.Vocabulary.Proofs.NamedStore.ErasureUnique,
    Restated.Vocabulary.Proofs.NamedStore.NamedParentClosed, Restated.Vocabulary.Proofs.NamedStore.PoolView,
    Restated.Vocabulary.Proofs.NamedStore.DerivedView, Restated.Vocabulary.Proofs.NamedStoreRoots.RootsInTree,
    Restated.Vocabulary.Proofs.NamedConfirmationMembership.Confirmed,
    facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView, facts.nd.store_with_cache_bodies,
    facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_sg_votes,
    facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau,
    facts.nd.store_with_cache_core_attestations] at h ⊢
  exact h

/-- In a named store whose bodies are parent-closed, every ancestor of a body is a body. -/
private theorem ancestor_body_mem₅₅b {st : M.NS}
    (hpc : Restated.Vocabulary.Proofs.NamedStore.NamedParentClosed M st)
    {A B : NamedBlock V} (hB : B ∈ st.bodies)
    (hAB : NamedBlock.Preceq A B) : A ∈ st.bodies := by
  induction B with
  | genesis =>
      simp only [NamedBlock.Preceq, NamedBlock.preceq,
        decide_eq_true_eq] at hAB
      exact hAB ▸ hB
  | node parent slot root votes support rows proposer ih =>
      simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hAB
      rcases hAB with rfl | hparent
      · exact hB
      · have hP : parent ∈ st.bodies := by
          simpa only [NamedBlock.parent] using hpc.2 _ hB
        exact ih hP (by simpa only [NamedBlock.Preceq] using hparent)

/-- In a world `wd` strictly before `read`, a body `R` of `w`'s store other than genesis whose
    erasure is the store's FG root has derived height less than the store's `h_max`. -/
private theorem selectedFGRoot_deriveHeight_lt_hMax₅₅b (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (w : V) (read : Time) (wd : V → M.N)
    (hwd : wd ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho read)
    {R : NamedBlock V}
    (hRmem : R ∈ (wd w).st.bodies)
    (hroot : R.erase = M.get_fg_root (M.toHealing (wd w).st.core).toFG)
    (hne : R ≠ NamedBlock.genesis) :
    (M.derive_named S.E S.cfg R).h < (wd w).st.core.h_max := by
  have hco : Restated.Vocabulary.Proofs.NamedStore.Coherent M S.E S.cfg (wd w).st :=
    (Restated.Vocabulary.Proofs.NamedRuntime.stateBeforeTime_invariants facts S rho read w wd hwd).1.1.1
  have hbelow : (wd w).st.core.h_j < (wd w).st.core.h_max :=
    Restated.Vocabulary.Proofs.NamedJustificationBound.justificationBelowMax_stateBeforeTime facts
      S rho read w wd hwd
  by_cases hgate : (wd w).st.core.h_max = (wd w).st.core.h_j + 1
  · have hRJ : R.erase = (wd w).st.core.J :=
      hroot.trans (facts.fc.get_fg_root_toHealing_of_eq _ hgate)
    obtain ⟨C, hCmem, hCJ, hChj⟩ :=
      Restated.Vocabulary.Proofs.Bridges.storeJustificationOnChain_stateBeforeTime facts S rho read w
        wd hwd
    rcases facts.cs.justified_ancestor_height S.E S.cfg C with hz | ⟨J, hJC, hJerase, hJheight⟩
    · have hJgen : (wd w).st.core.J = Block.genesis := by
        rw [← hCJ]
        exact facts.cs.justified_zero_is_genesis S.E S.cfg C hz
      have hRgen : R = NamedBlock.genesis :=
        (priv% Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SGTargetCanonicality
          DecoupledConsensusModel.Proofs.HealingSurface.rootLock_named_genesis_of_erase_genesis)
          (hRJ.trans hJgen)
      exact (hne hRgen).elim
    · have hJmem : J ∈ (wd w).st.bodies :=
        ancestor_body_mem₅₅b hco.2.2.1 hCmem hJC
      have hRJerase : R.erase = J.erase :=
        hRJ.trans (hJerase.trans hCJ).symm
      have hRJnamed : R = J := hco.2.1 R hRmem J hJmem hRJerase
      calc
        (M.derive_named S.E S.cfg R).h =
            (M.derive_named S.E S.cfg J).h := by rw [hRJnamed]
        _ = (M.derive_named S.E S.cfg C).h_j := hJheight
        _ = (wd w).st.core.h_j := hChj
        _ < (wd w).st.core.h_max := hbelow
  · have hRF : R.erase = (wd w).st.core.F :=
      hroot.trans (facts.fc.get_fg_root_toHealing_of_ne _ hgate)
    obtain ⟨C, hCmem, hCF, hCFbelow⟩ :=
      Restated.Vocabulary.Proofs.Bridges.storeFinalizationOnChain_stateBeforeTime facts S rho read w
        wd hwd
    rcases facts.csAdded.finalized_ancestor_height S.E S.cfg C with hz | ⟨F, hFC, hFerase, hFheight⟩
    · have hFgen : (wd w).st.core.F = Block.genesis := by
        rw [← hCF]
        exact facts.cs.finalized_zero_is_genesis S.E S.cfg C hz
      have hRgen : R = NamedBlock.genesis :=
        (priv% Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SGTargetCanonicality
          DecoupledConsensusModel.Proofs.HealingSurface.rootLock_named_genesis_of_erase_genesis)
          (hRF.trans hFgen)
      exact (hne hRgen).elim
    · have hFmem : F ∈ (wd w).st.bodies :=
        ancestor_body_mem₅₅b hco.2.2.1 hCmem hFC
      have hRFerase : R.erase = F.erase :=
        hRF.trans (hFerase.trans hCF).symm
      have hRFnamed : R = F := hco.2.1 R hRmem F hFmem hRFerase
      calc
        (M.derive_named S.E S.cfg R).h =
            (M.derive_named S.E S.cfg F).h := by rw [hRFnamed]
        _ = (M.derive_named S.E S.cfg C).h_F := hFheight
        _ < (wd w).st.core.h_max := hCFbelow

/-- `m >>= k` can return `b` exactly when `m` can return some `a` from which `k a` can return `b`. -/
private theorem returns_bind_iff₅₅b {α β : Type} (m : DC.NDRE α) (k : α → DC.NDRE β) (b : β) :
    (m >>= k) ⇢ b ↔ ∃ a, m ⇢ a ∧ k a ⇢ b := by
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

/-- The healing view of the vote-duty store of slot `s + 1` staged from `n`'s core store has slot
    `s + 1`. -/
private theorem voteStore_hs_s₅₅b (facts : Record.Facts M) (S : Setup V) (n : M.N) (s : Slot) :
    (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S n.st.core (s + 1))).s = s + 1 := by
  show (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S n.st.core
    (s + 1))).toFG.toSG.toGoldfishStore.s = s + 1
  rw [facts.sto.toHealing_gs_s]
  show (Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core (M.vote_time S.E (s + 1))).s = s + 1
  rw [Restated.Vocabulary.Proofs.Optimistic.tickStore,
    ← facts.hd.setClock_core_eq_store_with_t_s S.E n.st, facts.hd.Sts_setClock_core_s,
    facts.sch.slotOf_vote_time]

/-- If `m` can return `a`, then `f <$> m` can return `f a`. -/
private theorem returns_map_intro₅₅b {α β : Type} (f : α → β) (m : DC.NDRE α) (a : α)
    (h : m ⇢ a) : (f <$> m) ⇢ f a := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image]
  exact ⟨_, h, rfl⟩

/-- If `B` satisfies `GenuineConfirmation` for `st` at slot `s`, then for some outcome of the early
    confirmation votes and some choice of Goldfish scores, those votes are an outcome of the
    confirmation votes and the count of the late voters is less than twice the score of `B`. -/
private theorem genuine_eligible₅₅b (facts : Record.Facts M) {contract : M.Contract} {E : Env V}
    {hc : Protocol.HealConfig} {st : M.S} {s : Slot} {B : Block V}
    (hB : Restated.Vocabulary.Protocol.GenuineConfirmation M (contract := contract) E hc st s B) :
    ∃ (early : Finset (GoldfishVote V)) (sc : Block V → Nat),
      Restated.Vocabulary.Protocol.confEarly M E st s ⇢ early ∧
      Restated.Vocabulary.Protocol.confVotes M E st s ⇢
        early.filter (fun x => M.no_second_vote_in (Restated.Vocabulary.Protocol.confLate M E st s) x = true) ∧
      (∀ B', M.goldfish_score E st.T
        (early.filter (fun x => M.no_second_vote_in (Restated.Vocabulary.Protocol.confLate M E st s) x = true))
        (early.filter (fun x => M.no_second_vote_in (Restated.Vocabulary.Protocol.confLate M E st s) x = true))
        s B' ⇢ sc B') ∧
      M.voters_count E (Restated.Vocabulary.Protocol.confLate M E st s) s < 2 * sc B := by
  obtain ⟨tm, htm⟩ := facts.sto.tau_nonempty st
  obtain ⟨R, hR⟩ := facts.fc.get_sg_root_with_nonempty contract E hc st.toHealing
    (M.round_of hc st.s)
  have hearly : Restated.Vocabulary.Protocol.confEarly M E st s ⇢
      beforeCutoff tm (M.support_cutoff E s) (st.pool s) :=
    returns_map_intro₅₅b _ _ _ htm
  have hu := returns_map_intro₅₅b
    (fun e => e.filter (fun x => M.no_second_vote_in (Restated.Vocabulary.Protocol.confLate M E st s) x = true))
    _ _ hearly
  choose sc hsc using fun B' => facts.fc.goldfish_score_nonempty E st.T
    ((beforeCutoff tm (M.support_cutoff E s) (st.pool s)).filter
      (fun x => M.no_second_vote_in (Restated.Vocabulary.Protocol.confLate M E st s) x = true))
    ((beforeCutoff tm (M.support_cutoff E s) (st.pool s)).filter
      (fun x => M.no_second_vote_in (Restated.Vocabulary.Protocol.confLate M E st s) x = true)) s B'
  obtain ⟨H, hH⟩ := facts.fc.ghost_nonempty R (Restated.Vocabulary.Protocol.confTree M st) sc
    (fun B' => decide (Restated.Vocabulary.Protocol.confCount M E st s < 2 * sc B'))
  have helig := hB.genuine R hR _ hu sc hsc H hH
  obtain ⟨st', hst'⟩ := facts.dt.update_confirmation_with_nonempty contract E hc st s
  have hW := facts.hd.update_confirmation_with_live_confirmed_of_eligible contract E hc st s tm htm
    R hR sc hsc H hH helig st' hst'
  have hBH : B = H := (hB.selected st' hst').symm.trans hW
  subst hBH
  exact ⟨_, sc, hearly, hu, hsc, of_decide_eq_true helig⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- Under the bundle along `W`, if `v ∈ Hs (support_cutoff s)`, `w ∈ Hs (view_freeze s)`,
    `lo ≤ proposal_time s`, `confirmation_time s` is inside the horizon, `w`'s vote-duty FG root of
    slot `s + 1` is an ancestor of `B`, `u` is in an outcome `cv` of the confirmation votes of `s`
    of `v`'s confirmation store with its head resolving there to a descendant `H` of `B`, then `u`'s
    head resolves to `H` in `w`'s vote-duty store, `H` is stamped there before `view_freeze s`, and
    `H` is genesis or `w` admitted it before `view_freeze s`. -/
theorem supportingTarget_visibleAtVoteDuty_after_gstOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {v w : V} {s : Slot}
    (hv : v ∈ Hs (M.support_cutoff S.E s))
    (hw : w ∈ Hs (M.view_freeze S.E s))
    (hpost : lo ≤ M.proposal_time S.E s)
    (hhor : M.confirmation_time S.E s ≤ rho.horizon)
    {B : Block V}
    (hroot : Block.Preceq
      (M.get_fg_root
        (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1))).toFG) B)
    {cv : Finset (GoldfishVote V)}
    (hcv : Restated.Vocabulary.Protocol.confVotes M S.E
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core (M.confirmation_time S.E s)) s ⇢ cv)
    {u : GoldfishVote V} (hu : u ∈ cv)
    {H : Block V}
    (hfind : Block.find? (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
      (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core (M.confirmation_time S.E s)).T
        u.head = some H)
    (hBH : Block.Preceq B H) :
    Block.find? (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1)).T u.head = some H ∧
      stampedBefore
        (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1)).timestamp_block
        (M.view_freeze S.E s) H = true ∧
      (H = Block.genesis ∨
        Restated.Vocabulary.Protocol.AdmittedBefore M S rho W w H (M.view_freeze S.E s)) := by
  have hΔ := S.E.Δ_pos
  have hloCut : lo ≤ M.support_cutoff S.E s :=
    hpost.trans ((facts.sch.proposal_time_lt_vote_time S.E s).trans
      (Restated.vote_time_lt_support_cutoff_l49 facts S s)).le
  have hvoteT : (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1)).T =
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.T :=
    tickStore_T₅₅b facts _ _
  have hvoteStamp : (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1)).timestamp_block =
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.timestamp_block :=
    tickStore_timestamp_block₅₅b facts _ _
  by_cases hgen : H = Block.genesis
  · subst H
    have hvisible := Restated.genesis_mem_and_stamp_storeBeforeTimeOn facts S Hs Xb hf w
      (M.vote_time S.E (s + 1)) (M.view_freeze S.E s)
    have hmem : Block.genesis ∈ (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1)).T := by
      rw [hvoteT]
      exact hvisible.1
    refine ⟨Restated.find_voteDutyStore_of_source_find_and_memOn facts S Hs Xb hf (hHsXb _ hw) hfind hmem,
      ?_, Or.inl rfl⟩
    rw [hvoteStamp]
    exact hvisible.2
  · set n := strictEventIndex rho (M.confirmation_time S.E s) with hn_def
    have hHsource : H ∈ (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W n v).st.core (M.confirmation_time S.E s)).T :=
      Proofs.HealingLemmas.find?_mem hfind
    obtain ⟨e, he, hce⟩ := returns_map_elim₅₅b _ _ _ hcv
    obtain ⟨τ, hτ, hτe⟩ := returns_map_elim₅₅b _ _ _ he
    have hearly : u ∈ beforeCutoff τ (M.support_cutoff S.E s)
        ((Restated.Vocabulary.Proofs.Optimistic.tickStore M S (W n v).st.core
          (M.confirmation_time S.E s)).pool s) := by
      rw [hτe]
      rw [← hce, Finset.mem_filter] at hu
      exact hu.1
    have hresolved : stampedBefore τ (M.support_cutoff S.E s) u = true :=
      ((mem_beforeCutoff_iff _ _ _ _).mp hearly).2
    have hHstamp : stampedBefore
        (Restated.Vocabulary.Proofs.Optimistic.tickStore M S (W n v).st.core
          (M.confirmation_time S.E s)).timestamp_block
        (M.support_cutoff S.E s) H = true :=
      facts.sto.stampedBefore_block_of_tau _ hfind τ hτ hresolved
    have hHn : H ∈ (W n v).st.core.T := by
      rw [tickStore_T₅₅b facts] at hHsource
      exact hHsource
    obtain ⟨C, hCmem, hCerase⟩ :=
      Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore facts S rho n v
        (W n) (hf.onePath n).1 hHn
    have hprocessed : Restated.Vocabulary.Execution.Object.processed M (W n v).st (Object.block C) = true := by
      show decide (C ∈ (W n v).st.bodies) = true
      exact decide_eq_true hCmem
    obtain hgen' | ⟨i, hin, t, hacc⟩ :=
      Restated.Vocabulary.Protocol.acceptsAt_block_of_processed facts S rho v W hf.onePath n C hprocessed
    · exact False.elim (hgen (by rw [← hCerase, hgen']; exact erase_named_genesis))
    · have hstampn : stampedBefore (W n v).st.core.timestamp_block
          (M.support_cutoff S.E s) C.erase = true := by
        rw [tickStore_timestamp_block₅₅b facts, ← hCerase] at hHstamp
        exact hHstamp
      have htSupport : t < M.support_cutoff S.E s :=
        Restated.acceptsAt_block_lt_of_stamp_beforeOn facts S Hs Xb hf hacc (Nat.succ_le_of_lt hin)
          (Restated.Vocabulary.Protocol.publicTime_support_cutoff facts S s) hv hloCut hstampn
      have hCposErase : 0 < C.erase.slot :=
        Nat.zero_lt_of_lt (Restated.Vocabulary.Protocol.parent_slot_lt_of_acceptsAt_block facts S W
          hf.onePath hacc)
      have hCpos : 0 < C.slot := by
        simpa only [Proofs.NamedWire.erase_slot] using hCposErase
      have hBH' : Block.Preceq B C.erase := by
        simpa only [hCerase] using hBH
      have hfreezeHor : M.view_freeze S.E s ≤ rho.horizon := by
        apply le_trans _ hhor
        exact le_of_lt (lt_trans
          (Int.lt_add_of_pos_right _ S.E.Δ_pos)
          (facts.sch.view_freeze_add_delta_lt_confirmation_time S.E s))
      have hvMax : v ∈ Hs (max t lo) := hHs _ _ (max_le htSupport.le hloCut) hv
      have hsvf := support_cutoff_add_delta_le_view_freeze₅₅b facts S s
      have hcutIn : M.support_cutoff S.E s ≤ M.view_freeze S.E s - S.E.Δ :=
        le_sub_iff_add_le.mpr hsvf
      have hadmitC : Restated.Vocabulary.Protocol.AdmittedBefore M S rho W w C.erase
          (M.view_freeze S.E s) := by
        apply Restated.block_admittedBefore_of_accepted_after_cutoffOn facts
          S Hs Xb hf hHs hHsXb hvMax hw hCpos hacc (htSupport.trans_le hcutIn) (hloCut.trans hcutIn)
            (sub_add_cancel _ _) hfreezeHor
        intro j hj
        have hjVote : j ≤ (rho.events.filter
            (fun e => decide (e.time < M.vote_time S.E (s + 1)))).length :=
          hj.trans (Restated.strict_filter_length_mono rho
            (le_of_lt (facts.sch.view_freeze_lt_vote_time_succ S.E s)))
        have hroot' : Block.Preceq
            (M.get_fg_root
              (M.toHealing (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core).toFG) B :=
          (congrArg (fun X => Block.Preceq X B) (facts.fc.get_fg_root_set_clock_slot
            (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core
            (M.vote_time S.E (s + 1))
            (S.E.slotOf (M.vote_time S.E (s + 1))))).mp hroot
        exact preceq_trans_Preceq
          (Restated.Vocabulary.Proofs.finalized_preceq_at_prefix_of_storeBeforeRoot_preceq facts
            S rho hf.sorted hjVote (W j) (hf.onePath j).1
            (W (strictEventIndex rho (M.vote_time S.E (s + 1))))
            (onePath_slice₅₅b W hf.onePath hjVote) hroot') hBH'
      have hvisible := Restated.admittedBefore_mem_and_stamp_atOn facts S Hs Xb hf hadmitC
          (le_of_lt (facts.sch.view_freeze_lt_vote_time_succ S.E s))
      have hmem : H ∈ (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1)).T := by
        rw [hvoteT, ← hCerase]
        exact hvisible.1
      refine ⟨Restated.find_voteDutyStore_of_source_find_and_memOn facts S Hs Xb hf (hHsXb _ hw) hfind hmem,
        ?_, Or.inr (by rw [← hCerase]; exact hadmitC)⟩
      rw [hvoteStamp, ← hCerase]
      exact hvisible.2

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- Under the bundle along `W`, if `v ∈ Hs (confirmation_time s)`, `w ∈ Hs (vote_time (s + 1))`,
    `lo ≤ proposal_time s`, `confirmation_time s` is inside the horizon, and `w`'s vote-duty FG root
    of slot `s + 1` is an ancestor of `B`, then `AdoptionTransport` for `B` holds from `v`'s
    confirmation store of `s` to `w`'s vote-duty store of `s + 1`, for every outcome of the
    confirmation votes, the voter view and the support view. -/
theorem adoptionTransport_B_after_gstOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {v w : V} {s : Slot}
    (hv : v ∈ Hs (M.confirmation_time S.E s))
    (hw : w ∈ Hs (M.vote_time S.E (s + 1)))
    (hpost : lo ≤ M.proposal_time S.E s)
    (hhor : M.confirmation_time S.E s ≤ rho.horizon)
    {B : Block V}
    (hroot : Block.Preceq
      (M.get_fg_root
        (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1))).toFG) B) :
    ∀ cv, Restated.Vocabulary.Protocol.confVotes M S.E
        (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
          (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core (M.confirmation_time S.E s)) s ⇢ cv →
    ∀ Y, M.voter_view S.E
        (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1))).toFG.toSG.toGoldfishStore
          (s + 1) ⇢ Y →
    ∀ U, M.voter_support_view S.E
        (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1))).toFG.toSG.toGoldfishStore
          (s + 1) ⇢ U →
    Restated.Vocabulary.Protocol.AdoptionTransport M
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core (M.confirmation_time S.E s)).T
      (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1)).T
      cv
      (Restated.Vocabulary.Protocol.confLate M S.E
        (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
          (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core (M.confirmation_time S.E s)) s)
      Y U B := by
  intro cv hcv Y hY U hU
  have hΔ := S.E.Δ_pos
  have hvCut : v ∈ Hs (M.support_cutoff S.E s) :=
    hHs _ _ (facts.sch.Protocol_support_cutoff_le_confirmation_time S.E s) hv
  have hwFreeze : w ∈ Hs (M.view_freeze S.E s) :=
    hHs _ _ (facts.sch.view_freeze_lt_vote_time_succ S.E s).le hw
  have hloCut : lo ≤ M.support_cutoff S.E s :=
    hpost.trans ((facts.sch.proposal_time_lt_vote_time S.E s).trans
      (Restated.vote_time_lt_support_cutoff_l49 facts S s)).le
  refine ⟨?_, Restated.targetRawVote_settledAtSource_after_gstOn facts S Hs Xb hf hHs hv hw hpost
    hhor Y hY⟩
  intro u hu b hb hbtrue
  obtain ⟨H, hfind, hBH⟩ := (facts.fc.targets_under_iff b hb).mp hbtrue
  obtain ⟨i, t, hacc, hus, hlo, hhi⟩ :=
    Restated.confirmationVotesAcceptedInWindow_of_admissibleOn facts S Hs Xb hf s hvCut
      hloCut cv hcv u hu
  have hfreezeHor : M.view_freeze S.E s ≤ rho.horizon := by
    apply le_trans _ hhor
    exact le_of_lt (lt_trans
      (Int.lt_add_of_pos_right _ S.E.Δ_pos)
      (facts.sch.view_freeze_add_delta_lt_confirmation_time S.E s))
  have hvt : v ∈ Hs t := hHs _ _ hhi.le hvCut
  have hwt : w ∈ Hs (t + S.E.Δ) := by
    refine hHs _ _ ?_ hw
    have h1 := support_cutoff_add_delta_le_view_freeze₅₅b facts S s
    have h2 := facts.sch.view_freeze_lt_vote_time_succ S.E s
    linarith
  have hsettled := Restated.accepted_gfVote_forward_settled_at_voteDuty_after_gstOn_RecoveryHandoffCore facts
    S Hs Xb hf hHs hpost hacc hvt hwt hus hlo hhi hfreezeHor
  have hvisible := Restated.supportingTarget_visibleAtVoteDuty_after_gstOn facts
    S Hs Xb hf hHs hHsXb hvCut hwFreeze hpost hhor hroot hcv hu hfind
    (preceq_eq_true_iff_Preceq.mp hBH.2)
  rcases Restated.Vocabulary.Protocol.settled_before_freeze_in_voter_pair facts S.E
      (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1)) s
      hvisible.1 hvisible.2.1 hBH.1 hsettled U hU Y hY with hsupport | hequiv
  · refine Or.inl ⟨hsupport, ?_⟩
    intro b' hb'
    exact (facts.fc.targets_under_iff b' hb').mpr ⟨H, hvisible.1, hBH.1, hBH.2⟩
  · exact Or.inr hequiv

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- Under the bundle along `W`, if `v ∈ Hs (support_cutoff s)`, `w ∈ Hs (view_freeze s)`,
    `lo ≤ proposal_time s`, `confirmation_time s` is inside the horizon, `B` satisfies
    `GenuineConfirmation` at `v`'s confirmation store of `s`, and `w`'s vote-duty FG root of slot
    `s + 1` is an ancestor of `B`, then `B` is in every outcome of `w`'s voter-processed block tree
    at its vote-duty store. -/
theorem voterProcessedTarget_of_genuineConfirmation_after_gstOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {v w : V} {s : Slot}
    (hv : v ∈ Hs (M.support_cutoff S.E s))
    (hw : w ∈ Hs (M.view_freeze S.E s))
    (hpost : lo ≤ M.proposal_time S.E s)
    (hhor : M.confirmation_time S.E s ≤ rho.horizon)
    {B : Block V}
    {contract : M.Contract}
    (hgenuine : Restated.Vocabulary.Protocol.GenuineConfirmation M (contract := contract) S.E S.hc
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core (M.confirmation_time S.E s)) s B)
    (hroot : Block.Preceq
      (M.get_fg_root
        (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1))).toFG) B) :
    ∀ Q, M.voter_processed_block_tree S.E
      (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1))).toFG.toSG.toGoldfishStore
      (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1))).s ⇢ Q → B ∈ Q := by
  intro Q hQ
  have hΔ := S.E.Δ_pos
  have hloFreeze : lo ≤ M.view_freeze S.E s :=
    le_trans hpost (le_of_lt
      (((facts.sch.proposal_time_lt_vote_time S.E s).trans
        (Restated.vote_time_lt_support_cutoff_l49 facts S s)).trans
        (facts.sch.Optimistic_support_cutoff_lt_view_freeze S.E s)))
  set cs := Restated.Vocabulary.Proofs.Optimistic.tickStore M S
    (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core (M.confirmation_time S.E s)
    with hcs
  set dW := W (strictEventIndex rho (M.vote_time S.E (s + 1))) with hdW
  obtain ⟨early, sc, hearly, hcvq, hsc, helig⟩ := genuine_eligible₅₅b facts hgenuine
  obtain ⟨τ, hτ, hτe⟩ := returns_map_elim₅₅b _ _ _ hearly
  have hel : early ⊆ Restated.Vocabulary.Protocol.confLate M S.E cs s := by
    intro u hu
    rw [← hτe, mem_beforeCutoff_iff] at hu
    have h1 := facts.sto.stampedBefore_vote_of_tau cs τ hτ hu.2
    exact Protocol.beforeCutoff_mono _ (facts.sch.Protocol_support_cutoff_le_confirmation_time S.E s) _
      ((mem_beforeCutoff_iff _ _ _ _).mpr ⟨hu.1, h1⟩)
  have hpos : 0 < sc B := by
    have h := helig
    omega
  obtain ⟨R, hR⟩ := facts.fc.raw_supporters_nonempty cs.T
    (early.filter (fun x => M.no_second_vote_in (Restated.Vocabulary.Protocol.confLate M S.E cs s) x = true))
    (early.filter (fun x => M.no_second_vote_in (Restated.Vocabulary.Protocol.confLate M S.E cs s) x = true))
    s B
  have hscR : sc B = R.card :=
    facts.fc.Numerator_score_eq_supporters early (Restated.Vocabulary.Protocol.confLate M S.E cs s) _
      hel rfl S.E cs.T s B (sc B) (hsc B) R hR
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (hscR ▸ hpos)
  choose tu htu using fun u => facts.fc.targets_under_nonempty cs.T B u
  rw [facts.fc.mem_supporters_iff (_E := S.E) R hR tu htu] at hx
  obtain ⟨-, u, huBy, -, htargets⟩ := hx
  rw [facts.sch.mem_votes_by_iff] at huBy
  obtain ⟨H, hfind, hBH⟩ := (facts.fc.targets_under_iff (tu u) (htu u)).mp htargets
  have hvisible := Restated.supportingTarget_visibleAtVoteDuty_after_gstOn facts
    S Hs Xb hf hHs hHsXb hv hw hpost hhor hroot hcvq huBy.1 hfind
      (preceq_eq_true_iff_Preceq.mp hBH.2)
  have hvoteT : (Restated.Vocabulary.Proofs.Optimistic.voteStore M S (dW w).st.core (s + 1)).T =
      (dW w).st.core.T :=
    tickStore_T₅₅b facts _ _
  have hvoteStamp : (Restated.Vocabulary.Proofs.Optimistic.voteStore M S (dW w).st.core (s + 1)).timestamp_block =
      (dW w).st.core.timestamp_block :=
    tickStore_timestamp_block₅₅b facts _ _
  have hslot : (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S (dW w).st.core (s + 1))).s =
      s + 1 := by
    show (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S (dW w).st.core
      (s + 1))).toFG.toSG.toGoldfishStore.s = s + 1
    rw [facts.sto.toHealing_gs_s]
    show (Restated.Vocabulary.Proofs.Optimistic.tickStore M S (dW w).st.core (M.vote_time S.E (s + 1))).s = s + 1
    rw [Restated.Vocabulary.Proofs.Optimistic.tickStore,
      ← facts.hd.setClock_core_eq_store_with_t_s S.E (dW w).st, facts.hd.Sts_setClock_core_s,
      facts.sch.slotOf_vote_time]
  have hHmem : H ∈ (Restated.Vocabulary.Proofs.Optimistic.voteStore M S (dW w).st.core (s + 1)).T :=
    Proofs.HealingLemmas.find?_mem hvisible.1
  have hHn : H ∈ (dW w).st.core.T := by
    rw [hvoteT] at hHmem
    exact hHmem
  rw [hslot] at hQ
  obtain hgen | ⟨C, hCerase, i, hin, t, hacc⟩ :=
    Restated.Vocabulary.Protocol.acceptsAt_block_of_processed_erased facts S rho w W hf.onePath
      (strictEventIndex rho (M.vote_time S.E (s + 1))) hHn
  · have hBgen : B = Block.genesis :=
      Block.preceq_antisymm (hgen ▸ hBH.2) (Protocol.preceq_genesis B)
    subst B
    have hgenesis := Restated.genesis_mem_and_stamp_storeBeforeTimeOn facts S Hs Xb hf w
        (M.vote_time S.E (s + 1))
        (M.view_freeze S.E s)
    refine facts.fc.mem_voter_processed_block_tree_of_stamped S.E _ _ ?_ ?_ Q hQ
    · rw [facts.sto.toHealing_gs_T, hvoteT]
      exact hgenesis.1
    · rw [Nat.add_sub_cancel, facts.sto.toHealing_gs_timestamp_block, hvoteStamp]
      exact hgenesis.2
  · have hstampC : stampedBefore (dW w).st.core.timestamp_block (M.view_freeze S.E s) C.erase = true := by
      have h := hvisible.2.1
      rw [hvoteStamp, ← hCerase] at h
      exact h
    have htFreeze : t < M.view_freeze S.E s :=
      Restated.acceptsAt_block_lt_of_stamp_beforeOn facts S Hs Xb hf hacc (Nat.succ_le_of_lt hin)
          (Restated.Vocabulary.Protocol.publicTime_view_freeze facts S s) hw hloFreeze hstampC
    have hvisibleB := Restated.admittedBefore_ancestor_mem_and_stamp_atOn facts S Hs Xb hf
      (show Restated.Vocabulary.Protocol.AdmittedBefore M S rho W w H
        (M.view_freeze S.E s) from
          ⟨C, hCerase, i, t, hacc, htFreeze⟩)
      (preceq_eq_true_iff_Preceq.mp hBH.2) (le_of_lt (facts.sch.view_freeze_lt_vote_time_succ S.E s))
    refine facts.fc.mem_voter_processed_block_tree_of_stamped S.E _ _ ?_ ?_ Q hQ
    · rw [facts.sto.toHealing_gs_T, hvoteT]
      exact hvisibleB.1
    · rw [Nat.add_sub_cancel, facts.sto.toHealing_gs_timestamp_block, hvoteStamp]
      exact hvisibleB.2

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- Under the bundle along `W`, if `w ∈ Hs (view_freeze s)`, `lo ≤ view_freeze s`, and `B` is in an
    outcome of the voter candidate tree of `w`'s vote-duty store of slot `s + 1`, then every
    ancestor of `B` is in every outcome of that store's voter-processed block tree. -/
theorem recoveryHandoff_processedPath_of_frozenCandidateOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {w : V} {s : Slot} (hw : w ∈ Hs (M.view_freeze S.E s)) {B : Block V}
    {K : Finset (Block V)}
    (hK : Restated.Vocabulary.Proofs.Optimistic.voter_candidate_tree M S.E
      (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1))) ⇢ K)
    (hB : B ∈ K)
    (hgat : lo ≤ M.view_freeze S.E s) :
    ∀ C : Block V, Block.Preceq C B →
    ∀ Q, M.voter_processed_block_tree S.E
      (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1))).toFG.toSG.toGoldfishStore
      (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1))).s ⇢ Q → C ∈ Q := by
  set n := strictEventIndex rho (M.vote_time S.E (s + 1)) with hn_def
  have hvoteT : (Restated.Vocabulary.Proofs.Optimistic.voteStore M S (W n w).st.core (s + 1)).T =
      (W n w).st.core.T :=
    tickStore_T₅₅b facts _ _
  have hvoteStamp : (Restated.Vocabulary.Proofs.Optimistic.voteStore M S (W n w).st.core (s + 1)).timestamp_block =
      (W n w).st.core.timestamp_block :=
    tickStore_timestamp_block₅₅b facts _ _
  have hslot := voteStore_hs_s₅₅b facts S (W n w) s
  unfold Restated.Vocabulary.Proofs.Optimistic.voter_candidate_tree at hK
  obtain ⟨P0, hP0, hKP⟩ := (returns_bind_iff₅₅b _ _ _).mp hK
  have hKeq := (Record.returns_pure _ _).1 hKP
  rw [hKeq] at hB
  have hBdata := facts.fc.parts_of_mem_get_filtered_block_tree_from hB
  have hBprocessed : B ∈ P0 := hBdata.1.1.1
  have hpc : Restated.Vocabulary.Internal.ParentClosed M (W n w).st.core :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.parentClosed_stateBefore facts S rho n w (W n)
      (hf.onePath n).1
  intro C hCB Q hQ
  rw [hslot] at hP0 hQ
  obtain ⟨hBT, hBcase⟩ := facts.fc.voter_processed_block_tree_cases S.E _ _ P0 hP0 hBprocessed
  rw [facts.sto.toHealing_gs_T, hvoteT] at hBT
  rcases hBcase with hstamp | ⟨P, hP, hPs, hBP⟩
  · rw [Nat.add_sub_cancel, facts.sto.toHealing_gs_timestamp_block, hvoteStamp] at hstamp
    rcases Restated.Vocabulary.Protocol.acceptsAt_block_of_processed_erased facts S rho w W hf.onePath n hBT with
      hgen | ⟨D, hDB, i, hin, t, hacc⟩
    · have hCgen : C = Block.genesis :=
        Block.preceq_antisymm (preceq_eq_true_iff_Preceq.mpr (hgen ▸ hCB))
          (Protocol.preceq_genesis C)
      subst C
      have hgenesis := Restated.genesis_mem_and_stamp_storeBeforeTimeOn facts S Hs Xb hf w
        (M.vote_time S.E (s + 1))
        (M.view_freeze S.E s)
      refine facts.fc.mem_voter_processed_block_tree_of_stamped S.E _ _ ?_ ?_ Q hQ
      · rw [facts.sto.toHealing_gs_T, hvoteT]
        exact hgenesis.1
      · rw [Nat.add_sub_cancel, facts.sto.toHealing_gs_timestamp_block, hvoteStamp]
        exact hgenesis.2
    · have hstampD : stampedBefore (W n w).st.core.timestamp_block
          (M.view_freeze S.E s) D.erase = true := by
        rw [hDB]
        exact hstamp
      have htFreeze : t < M.view_freeze S.E s :=
        Restated.acceptsAt_block_lt_of_stamp_beforeOn facts S Hs Xb hf hacc (Nat.succ_le_of_lt hin)
          (Restated.Vocabulary.Protocol.publicTime_view_freeze facts S s) hw hgat hstampD
      have hvisibleC := Restated.admittedBefore_ancestor_mem_and_stamp_atOn facts S Hs Xb hf
        (show Restated.Vocabulary.Protocol.AdmittedBefore M S rho W w B
          (M.view_freeze S.E s) from ⟨D, hDB, i, t, hacc, htFreeze⟩)
        hCB (le_of_lt (facts.sch.view_freeze_lt_vote_time_succ S.E s))
      refine facts.fc.mem_voter_processed_block_tree_of_stamped S.E _ _ ?_ ?_ Q hQ
      · rw [facts.sto.toHealing_gs_T, hvoteT]
        exact hvisibleC.1
      · rw [Nat.add_sub_cancel, facts.sto.toHealing_gs_timestamp_block, hvoteStamp]
        exact hvisibleC.2
  · have hPTn : P ∈ (W n w).st.core.T := by
      have h := hP
      rw [facts.sto.toHealing_gs_T, hvoteT] at h
      exact h
    have hCP : Block.Preceq C P := preceq_trans_Preceq hCB hBP
    unfold Restated.Vocabulary.Internal.ParentClosed Record.Model.GS.parent_closed at hpc
    rw [facts.sto.toHealing_gs_T] at hpc
    have hCTn : C ∈ (W n w).st.core.T :=
      Proofs.Records.mem_of_preceq hpc.2 C P hPTn (preceq_eq_true_iff_Preceq.mpr hCP)
    refine facts.fc.mem_voter_processed_block_tree_of_proposal S.E _ _ ?_ hP hPs hCP Q hQ
    rw [facts.sto.toHealing_gs_T, hvoteT]
    exact hCTn

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- An outcome of the voter candidate tree of a store with a cache written in is an outcome of the
    voter candidate tree of the store itself. -/
private theorem voter_candidate_tree_swc₅₅ (facts : Record.Facts M) (E : Env V) (st : M.NS)
    (c : M.Cache) (K : Finset (Block V))
    (hK : Restated.Vocabulary.Proofs.Optimistic.voter_candidate_tree M E
      (M.toHealing (M.store_with_cache st c).core) ⇢ K) :
    Restated.Vocabulary.Proofs.Optimistic.voter_candidate_tree M E (M.toHealing st.core) ⇢ K := by
  unfold Restated.Vocabulary.Proofs.Optimistic.voter_candidate_tree at hK ⊢
  obtain ⟨P0, hP0, hKP⟩ := (returns_bind_iff₅₅b _ _ _).mp hK
  have hKeq := (Record.returns_pure _ _).1 hKP
  have hP0' : M.voter_processed_block_tree E (M.toHealing st.core).toFG.toSG.toGoldfishStore
      (M.toHealing st.core).s ⇢ P0 := by
    have h := hP0
    simp only [Record.Model.HS.s, facts.sto.toHealing_gs_s, facts.nd.store_with_cache_core_s,
      facts.nd.store_with_cache_voter_processed_block_tree] at h ⊢
    exact h
  refine (returns_bind_iff₅₅b _ _ _).mpr ⟨P0, hP0', (Record.returns_pure _ _).2 ?_⟩
  obtain ⟨X, hX⟩ := facts.fc.voter_filtered_block_tree_nonempty E st.core st.core.s
  have hX' : M.voter_filtered_block_tree E (M.store_with_cache st c).core
      (M.store_with_cache st c).core.s ⇢ X := by
    rw [facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_voter_filtered_block_tree]
    exact hX
  have e1 := facts.fc.voter_candidate_tree_eq_protocol_voter_filtered_block_tree E st.core P0 hP0' X hX
  have e2 := facts.fc.voter_candidate_tree_eq_protocol_voter_filtered_block_tree E _ P0 hP0 X hX'
  rw [e1, ← e2]
  first
  | exact hKeq
  | exact hKeq.symm

/-- Under the bundle along `W`, if `w ∈ Hs (view_freeze s)`, `lo ≤ view_freeze s`, and `B` is in an
    outcome `K` of the voter candidate tree of `w`'s node state staged at `vote_time (s + 1)` with
    the cache outcome `c`, then for every outcome `R` of that node state's SG root, every block
    descending from `R`, other than `R`, and an ancestor of `B` is in `K`. -/
theorem recoveryHandoff_namedVotePath_of_frozenCandidateOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {w : V} {s : Slot} (hw : w ∈ Hs (M.view_freeze S.E s))
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.toHealing
      (M.vote_time S.E (s + 1))
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache ⇢ c)
    {B : Block V} {K : Finset (Block V)}
    (hK : Restated.Vocabulary.Proofs.Optimistic.voter_candidate_tree M S.E
      (M.toHealing (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
          (M.vote_time S.E (s + 1)))
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c).st.core) ⇢ K)
    (hB : B ∈ K)
    (hgat : lo ≤ M.view_freeze S.E s) :
    ∀ R : Block V, M.get_sg_root_with
        (M.gradeContract (M.mkNode
          (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
            (M.vote_time S.E (s + 1)))
          (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c).cache)
        S.E S.hc
        (M.toHealing (M.mkNode
          (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
            (M.vote_time S.E (s + 1)))
          (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c).st.core)
        (M.round_of S.hc (M.mkNode
          (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
            (M.vote_time S.E (s + 1)))
          (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c).st.core.s) ⇢ R →
    ∀ C : Block V, Block.Preceq R C → C ≠ R → Block.Preceq C B → C ∈ K := by
  set i := strictEventIndex rho (M.vote_time S.E (s + 1)) with hi_def
  set n := M.mkNode (M.ns_setClock S.E (W i w).st (M.vote_time S.E (s + 1))) (W i w).record c
    with hn_def
  have hnst : n.st = M.store_with_cache (M.ns_setClock S.E (W i w).st (M.vote_time S.E (s + 1))) c := by
    rw [hn_def, facts.nd.mkNode_st]
  have hcoreV : (M.ns_setClock S.E (W i w).st (M.vote_time S.E (s + 1))).core =
      Restated.Vocabulary.Proofs.Optimistic.voteStore M S (W i w).st.core (s + 1) := by
    rw [Restated.Vocabulary.Proofs.Optimistic.voteStore, Restated.Vocabulary.Proofs.Optimistic.tickStore,
      facts.hd.setClock_core_eq_store_with_t_s]
  have hstT : n.st.core.T = (W i w).st.core.T := by
    rw [hnst, facts.nd.store_with_cache_core_T, facts.hd.Sts_setClock_core_T]
  have hFJ : Block.Preceq n.st.core.F n.st.core.J := by
    rw [hnst, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.hd.setClock_core_F,
      facts.hd.setClock_core_J]
    exact Restated.Vocabulary.Proofs.NamedStoreBridge.finalized_preceq_justified_stateBefore facts S rho
      i w (W i) (hf.onePath i).1
  have hpc := Restated.Vocabulary.Proofs.NamedStoreBridge.parentClosed_stateBefore facts S rho i w (W i)
    (hf.onePath i).1
  unfold Restated.Vocabulary.Internal.ParentClosed Record.Model.GS.parent_closed at hpc
  rw [facts.sto.toHealing_gs_T] at hpc
  have hK' := hK
  unfold Restated.Vocabulary.Proofs.Optimistic.voter_candidate_tree at hK'
  obtain ⟨P0, hP0, hKP⟩ := (returns_bind_iff₅₅b _ _ _).mp hK'
  have hKeq := (Record.returns_pure _ _).1 hKP
  have hBdata := facts.fc.parts_of_mem_get_filtered_block_tree_from (hKeq ▸ hB)
  obtain ⟨Wb, hWbP, hBWb, hheight⟩ := hBdata.1.2
  have hBT : B ∈ n.st.core.T := by
    have h := (facts.fc.voter_processed_block_tree_cases S.E _ _ P0 hP0 hBdata.1.1.1).1
    rw [facts.sto.toHealing_gs_T] at h
    exact h
  have hWbT : Wb ∈ n.st.core.T := by
    have h := (facts.fc.voter_processed_block_tree_cases S.E _ _ P0 hP0 hWbP).1
    rw [facts.sto.toHealing_gs_T] at h
    exact h
  have hBfiltered : B ∈ M.get_filtered_block_tree (M.toHealing n.st.core).toFG := by
    refine facts.fc.mem_get_filtered_block_tree_of_parts (M.toHealing n.st.core) ?_ hBdata.1.1.2 ?_ hBWb
      hheight hBdata.2
    · rw [facts.sto.toHealing_gs_T]; exact hBT
    · rw [facts.sto.toHealing_gs_T]; exact hWbT
  have hKV : Restated.Vocabulary.Proofs.Optimistic.voter_candidate_tree M S.E
      (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S (W i w).st.core (s + 1))) ⇢ K := by
    have h := hK
    rw [hnst] at h
    have h2 := voter_candidate_tree_swc₅₅ facts S.E _ c K h
    rw [hcoreV] at h2
    exact h2
  have hprocessed := Restated.recoveryHandoff_processedPath_of_frozenCandidateOn facts
    S Hs Xb hf hw hKV hB hgat
  intro R hR C hAC _ hCB
  have hCT : C ∈ n.st.core.T := by
    rw [hstT]
    rw [hstT] at hBT
    exact Proofs.Records.mem_of_preceq hpc.2 C B hBT (preceq_eq_true_iff_Preceq.mpr hCB)
  have hroot : Block.Preceq (M.get_fg_root (M.toHealing n.st.core).toFG) R :=
    facts.fc.fg_root_Preceq_get_sg_root_with_gradeContract n.cache S.E S.hc _ _ R hR
  have hCfiltered : C ∈ M.get_filtered_block_tree (M.toHealing n.st.core).toFG := by
    have hFJ' : Block.preceq (M.toHealing n.st.core).toFG.F (M.toHealing n.st.core).toFG.J = true := by
      rw [facts.sto.Sts_toHealing_F, facts.sto.Sts_toHealing_J]
      exact preceq_eq_true_iff_Preceq.mpr hFJ
    have hCT' : C ∈ (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.T := by
      rw [facts.sto.toHealing_gs_T]
      exact hCT
    exact facts.fc.mem_filtered_of_preceq hFJ' hBfiltered hCT'
      (preceq_eq_true_iff_Preceq.mpr hCB)
      (preceq_eq_true_iff_Preceq.mpr (preceq_trans_Preceq hroot hAC))
  have hP0V : M.voter_processed_block_tree S.E
      (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S (W i w).st.core (s + 1))).toFG.toSG.toGoldfishStore
      (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S (W i w).st.core (s + 1))).s ⇢ P0 := by
    rw [← hcoreV]
    have h := hP0
    rw [hnst] at h
    simp only [Record.Model.HS.s, facts.sto.toHealing_gs_s, facts.nd.store_with_cache_core_s,
      facts.nd.store_with_cache_voter_processed_block_tree] at h ⊢
    exact h
  have hCprocessed : C ∈ P0 := hprocessed C hCB P0 hP0V
  have hCdata := facts.fc.parts_of_mem_get_filtered_block_tree hCfiltered
  rw [hKeq]
  exact facts.fc.mem_get_filtered_block_tree_from_of_parts_explicit _ hCprocessed hCdata.1.1.2 hWbP
    (preceq_trans_Preceq hCB hBWb) hheight hCdata.2

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- Under the bundle along `W`, let `n` be `w`'s node state staged at `vote_time (s + 1)` with the
    cache outcome `c`. If `v ∈ Hs (confirmation_time s)`, `w ∈ Hs (vote_time (s + 1))`,
    `lo ≤ proposal_time s`, `confirmation_time s` is inside the horizon, `w`'s ticks at
    `vote_time (s + 1)` pass the grade-1 awake test, and `B` is in an outcome of `n`'s voter
    candidate tree and descends from `n`'s FG root and from every outcome of its SG root, then the
    confirmation votes of `v`'s confirmation store satisfy `AdoptionTransport` into `n`'s tree, the
    blocks between the SG root and `B` are in `n`'s filtered voter tree, `n`'s in-tree head is a run
    block through `Xb`, and `w` emits its Goldfish vote along `W` at `vote_time (s + 1)`. -/
theorem nextVoteAdoption_of_recovery_after_gstOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {v w : V} {s : Slot}
    (hv : v ∈ Hs (M.confirmation_time S.E s))
    (hw : w ∈ Hs (M.vote_time S.E (s + 1)))
    (hpost : lo ≤ M.proposal_time S.E s)
    (hhor : M.confirmation_time S.E s ≤ rho.horizon)
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.toHealing
      (M.vote_time S.E (s + 1))
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache ⇢ c)
    {B : Block V}
    (hroot : Block.Preceq
      (M.get_fg_root
        (M.toHealing (M.mkNode
          (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
            (M.vote_time S.E (s + 1)))
          (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c).st.core).toFG) B)
    (hanchor : ∀ R : Block V, M.get_sg_root_with
        (M.gradeContract (M.mkNode
          (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
            (M.vote_time S.E (s + 1)))
          (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c).cache)
        S.E S.hc
        (M.toHealing (M.mkNode
          (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
            (M.vote_time S.E (s + 1)))
          (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c).st.core)
        (M.round_of S.hc (M.mkNode
          (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
            (M.vote_time S.E (s + 1)))
          (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c).st.core.s) ⇢ R →
      Block.Preceq R B)
    {K : Finset (Block V)}
    (hK : Restated.Vocabulary.Proofs.Optimistic.voter_candidate_tree M S.E
      (M.toHealing (M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
          (M.vote_time S.E (s + 1)))
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c).st.core) ⇢ K)
    (hcandidate : B ∈ K)
    (hrun : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick w (M.vote_time S.E (s + 1))) →
      M.awake_for_grade1 S w (W j w) (M.round_of S.hc (s + 1))) :
    let n := M.mkNode
      (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
        (M.vote_time S.E (s + 1)))
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c
    let cw := Restated.Vocabulary.Proofs.Optimistic.tickStore M S
      (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core (M.confirmation_time S.E s)
    (∀ votes : Finset (GoldfishVote V), Restated.Vocabulary.Protocol.confVotes M S.E cw s ⇢ votes →
      ∀ L : Finset (GoldfishVote V),
        M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
      ∀ L' : Finset (GoldfishVote V),
        M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
      Restated.Vocabulary.Protocol.AdoptionTransport M cw.T n.st.core.T votes
        (Restated.Vocabulary.Protocol.confLate M S.E cw s) L L' B) ∧
    (∀ L : Finset (GoldfishVote V),
        M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
      ∀ L' : Finset (GoldfishVote V),
        M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
      L' ⊆ L) ∧
    (∀ R : Block V, M.get_sg_root_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
        (M.round_of S.hc n.st.core.s) ⇢ R →
      R.compatible B = true) ∧
    (∀ R : Block V, M.get_sg_root_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
        (M.round_of S.hc n.st.core.s) ⇢ R →
      R ⪯ B →
        ∀ C : Block V, R ⪯ C → C ≠ R → C ⪯ B →
          ∀ T : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T →
            C ∈ T) ∧
    (∀ T : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T →
      ∀ L : Finset (GoldfishVote V),
        M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
      ∀ L' : Finset (GoldfishVote V),
        M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
      ∀ H : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
          (M.toHealing n.st.core) T L L' (n.st.core.s - 1) ⇢ H →
      ∃ C : NamedBlock V, C.erase = H ∧ Restated.RunBlockOn M S rho W Xb C) ∧
    (∀ u : GoldfishVote V,
      ∀ D : M.NS × Option (GoldfishVote V),
        M.duties_goldfish_vote_with (M.gradeContract n.cache) S.E S.hc (S.node w) n.st ⇢ D →
      D.2 = some u →
        Restated.Vocabulary.Execution.Run.emits M S rho W w (Object.gfVote u) (M.vote_time S.E (s + 1))) := by
  intro n cw
  set i := strictEventIndex rho (M.vote_time S.E (s + 1)) with hi_def
  have hΔ := S.E.Δ_pos
  have hwFreeze : w ∈ Hs (M.view_freeze S.E s) :=
    hHs _ _ (facts.sch.view_freeze_lt_vote_time_succ S.E s).le hw
  have hloFreeze : lo ≤ M.view_freeze S.E s :=
    le_trans hpost (le_of_lt
      (((facts.sch.proposal_time_lt_vote_time S.E s).trans
        (Restated.vote_time_lt_support_cutoff_l49 facts S s)).trans
        (facts.sch.Optimistic_support_cutoff_lt_view_freeze S.E s)))
  have hloVote : lo ≤ M.vote_time S.E (s + 1) :=
    hpost.trans ((facts.sch.proposal_time_lt_vote_time S.E s).le.trans
      (facts.sch.vote_time_mono S.E (Nat.le_succ s)))
  have hvoteHor : M.vote_time S.E (s + 1) ≤ rho.horizon := by
    have h := facts.sch.vote_time_succ_add_delta_le_confirmation_time S.E s
    linarith
  have hnst₀ : n.st = M.store_with_cache (M.ns_setClock S.E (W i w).st (M.vote_time S.E (s + 1))) c :=
    facts.nd.mkNode_st _ _ _
  have hnst : n.st = M.store_with_cache (M.ns_setClock S.E (W i w).st (M.vote_time S.E (s + 1))) _ := facts.nd.mkNode_st _ _ _
  have hcache : n.cache = c := facts.nd.mkNode_cache _ _ _
  have hcoreV : (M.ns_setClock S.E (W i w).st (M.vote_time S.E (s + 1))).core =
      Restated.Vocabulary.Proofs.Optimistic.voteStore M S (W i w).st.core (s + 1) := by
    rw [Restated.Vocabulary.Proofs.Optimistic.voteStore, Restated.Vocabulary.Proofs.Optimistic.tickStore,
      facts.hd.setClock_core_eq_store_with_t_s]
  have hslotS : n.st.core.s = s + 1 := by
    rw [hnst]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    rw [facts.hd.Sts_setClock_core_s, facts.sch.slotOf_vote_time]
  have hstT : n.st.core.T = (W i w).st.core.T := by
    rw [hnst]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    rw [facts.hd.Sts_setClock_core_T]
  have hrootV : Block.Preceq
      (M.get_fg_root (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W i w).st.core (s + 1))).toFG) B := by
    have h := hroot
    rw [hnst₀, facts.nd.store_with_cache_get_fg_root, hcoreV] at h
    exact h
  have hK' := hK
  unfold Restated.Vocabulary.Proofs.Optimistic.voter_candidate_tree at hK'
  obtain ⟨P0, hP0, hKP⟩ := (returns_bind_iff₅₅b _ _ _).mp hK'
  have hKeq := (Record.returns_pure _ _).1 hKP
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro votes hvotes L hL L' hL'
    rw [hslotS] at hL hL'
    rw [hnst₀] at hL hL' ⊢
    simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at hL hL' ⊢
    rw [hcoreV] at hL hL' ⊢
    exact Restated.adoptionTransport_B_after_gstOn facts S Hs Xb hf hHs hHsXb hv hw hpost hhor
      hrootV votes hvotes L hL L' hL'
  · intro L hL L' hL'
    refine facts.fc.voter_support_view_subset S.E _ _ ?_ L' hL' L hL
    intro C hC
    rw [facts.sto.toHealing_gs_T, hstT] at hC
    exact Restated.carried_support_subset_of_mem_TOn facts S Hs Xb hf w i hC
  · intro R hR
    exact Proofs.ModelProperties.compatible_eq_true_of_Preceq (hanchor R hR)
  · intro R hR _ C hAC hCne hCB T hT
    have hCK := Restated.recoveryHandoff_namedVotePath_of_frozenCandidateOn facts
      S Hs Xb hf hwFreeze c hc hK hcandidate hloFreeze R hR C hAC hCne hCB
    rw [← facts.fc.voter_candidate_tree_eq_protocol_voter_filtered_block_tree S.E n.st.core P0 hP0 T hT,
      ← hKeq]
    exact hCK
  · intro T hT L hL L' hL' H hH
    have hTsub : T ⊆ n.st.core.T := by
      rw [← facts.fc.voter_candidate_tree_eq_protocol_voter_filtered_block_tree S.E n.st.core P0 hP0 T hT]
      intro C hC
      have h := facts.fc.mem_T_of_mem_voter_processed_block_tree S.E _ _ P0 hP0
        (facts.fc.get_filtered_block_tree_from_subset _ _ hC)
      rw [facts.sto.toHealing_gs_T] at h
      exact h
    have hinvPre := (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho i w
      (W i) (hf.onePath i).1).1
    have hinv0 := facts.hd.invariant_clock S.E S.cfg (W i w).st (M.vote_time S.E (s + 1)) hinvPre
    have hinv : Restated.Vocabulary.Proofs.NamedConfirmationMembership.Invariant M S.E S.cfg n.st := by
      rw [hnst₀]
      exact invariant_store_with_cache₅₅b facts S.E S.cfg _ c hinv0
    have hrootMem : M.get_fg_root (M.toHealing n.st.core).toFG ∈ n.st.core.T :=
      Restated.Vocabulary.Proofs.NamedStoreRoots.fg_root_mem facts n.st hinv.1.2
    obtain ⟨R, hR⟩ := facts.fc.get_sg_root_with_nonempty (M.gradeContract n.cache) S.E S.hc
      (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.s)
    have hRmem : R ∈ n.st.core.T := by
      have h := Restated.Vocabulary.Proofs.NamedProposalParent.frame_anchor_mem facts S.E S.hc
        (M.toHealing n.st.core) _ _
        (by
          show M.get_fg_root (M.toHealing n.st.core).toFG ∈
            (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.T
          rw [facts.sto.toHealing_gs_T]
          exact hrootMem) R
        ((facts.nd.gradeContract_sgRoot_eq_frameAnchor _ _ _ _ _ _).mp hR)
      have h' : R ∈ (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.T := h
      rw [facts.sto.toHealing_gs_T] at h'
      exact h'
    have hHmem := facts.fc.Sts_get_head_in_tree_with_layer_mem _ S.E S.hc _ T L L' _ R hR hRmem hTsub
      H hH
    rw [hstT] at hHmem
    exact Restated.runBlock_of_mem_core_T_stateBeforeTimeOn facts S Hs Xb hf (hHsXb _ hw)
      (M.vote_time S.E (s + 1)) hHmem
  · intro u D hD hu
    rw [hcache, hnst₀, facts.dt.duties_goldfish_vote_with_store_with_cache] at hD
    apply Restated.emits_of_on_tick_emitOn facts S Hs Xb hf hw
      (Restated.Vocabulary.Proofs.Optimistic.publicTime_vote_time facts S (s + 1)) hloVote hvoteHor
      (fun j hj => hf.tick_outcome j _ _ hj)
    intro j hj
    have haw := hrun j hj
    rcases Restated.stateBefore_tick_eq_stateBeforeTimeOn facts S Hs Xb hf hj with hj' | hj'
    · rw [hj'] at haw ⊢
      have _hr_s1 := facts.ndRun.stateBeforeOf_reachedNode S rho i (W i) (hf.onePath i).1 w
      have _hv_s2 := facts.ndRun.stateBeforeOf_runs_as S rho i (W i) (hf.onePath i).1 w
      exact Restated.Vocabulary.Proofs.Optimistic.on_tick_emit_vote_mem facts S w (W i w) (s + 1)
        (Nat.zero_lt_succ s) c hc D hD hu haw
    · rw [hj'] at haw ⊢
      have hst' := (facts.nd.wake_st_record (W i w)).1
      have hca' := facts.nd.wake_cache (W i w)
      have _hr_s3 := facts.nd.reachedNode_wake _ (facts.ndRun.stateBeforeOf_reachedNode S rho i (W i) (hf.onePath i).1 w)
      have _hv_s4 := facts.nd.runs_as_wake _ w (facts.ndRun.stateBeforeOf_runs_as S rho i (W i) (hf.onePath i).1 w)
      exact Restated.Vocabulary.Proofs.Optimistic.on_tick_emit_vote_mem facts S w (M.wake (W i w))
        (s + 1) (Nat.zero_lt_succ s) c (by rw [hst', hca']; exact hc) D (by rw [hst']; exact hD) hu
        haw

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Proofs.Optimistic

/-- Under the bundle along `W`, if `w ∈ Hs (vote_time d)`, `0 < d`, `w` is on `d`'s committee,
    `vote_time d` is inside the horizon, `lo ≤ vote_time d`, and `w`'s ticks at `vote_time d` pass
    the grade-1 awake test, then `w` emits along `W` at `vote_time d` the Goldfish vote of slot `d`
    for every head the in-tree head computation can return at `w`'s node state staged at
    `vote_time d` with the cache outcome `c`. -/
theorem voterHead_emits_of_coreOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {w : V} {d : Slot} (hw : w ∈ Hs (M.vote_time S.E d)) (hd : 0 < d)
    (hwCommittee : w ∈ S.E.committee d)
    (hhor : M.vote_time S.E d ≤ rho.horizon)
    (hgat : lo ≤ M.vote_time S.E d)
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core.toHealing
      (M.vote_time S.E d)
      (W (strictEventIndex rho (M.vote_time S.E d)) w).cache ⇢ c)
    (hrun : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick w (M.vote_time S.E d)) →
      M.awake_for_grade1 S w (W j w) (M.round_of S.hc d)) :
    let n := M.mkNode
      (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) w).st (M.vote_time S.E d))
      (W (strictEventIndex rho (M.vote_time S.E d)) w).record c
    ∀ T : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T →
    ∀ L : Finset (GoldfishVote V),
      M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
    ∀ L' : Finset (GoldfishVote V),
      M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
    ∀ H : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
        (M.toHealing n.st.core) T L L' (n.st.core.s - 1) ⇢ H →
      Restated.Vocabulary.Execution.Run.emits M S rho W w
        (Object.gfVote ⟨w, d, H.root⟩)
        (M.vote_time S.E d) := by
  intro n T hT L hL L' hL' H hH
  set i := strictEventIndex rho (M.vote_time S.E d) with hi_def
  have hnst₀ : n.st = M.store_with_cache (M.ns_setClock S.E (W i w).st (M.vote_time S.E d)) c :=
    facts.nd.mkNode_st _ _ _
  have hnst : n.st = M.store_with_cache (M.ns_setClock S.E (W i w).st (M.vote_time S.E d)) _ := facts.nd.mkNode_st _ _ _
  have hcache : n.cache = c := facts.nd.mkNode_cache _ _ _
  have hslot : n.st.core.s = d := by
    rw [hnst]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    rw [facts.hd.Sts_setClock_core_s, facts.sch.slotOf_vote_time]
  obtain ⟨D, hD⟩ := facts.dt.goldfish_vote_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (S.node w) n.st
  have hout : D.2 = some ⟨(S.node w).val_index, n.st.core.s, H.root⟩ :=
    facts.fc.goldfish_vote_with_snd_of_mem_committee _ S.E S.hc (S.node w) n.st
      (by rw [S.node_val_index, hslot]; exact hwCommittee) D hD T hT L hL L' hL' H hH
  rw [S.node_val_index, hslot] at hout
  rw [hcache, hnst₀, facts.dt.duties_goldfish_vote_with_store_with_cache] at hD
  have ho : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick w (M.vote_time S.E d)) →
      ∀ out ∈ Restated.Vocabulary.Execution.on_tick_emit M S w (W j w) (M.vote_time S.E d),
        Object.gfVote ⟨w, d, H.root⟩ ∈ out.2 := by
    intro j hj
    have haw := hrun j hj
    rcases Restated.stateBefore_tick_eq_stateBeforeTimeOn facts S Hs Xb hf hj with hj' | hj'
    · rw [hj'] at haw ⊢
      have _hr_s5 := facts.ndRun.stateBeforeOf_reachedNode S rho i (W i) (hf.onePath i).1 w
      have _hv_s6 := facts.ndRun.stateBeforeOf_runs_as S rho i (W i) (hf.onePath i).1 w
      exact Restated.Vocabulary.Proofs.Optimistic.on_tick_emit_vote_mem facts S w (W i w) d hd c hc
        D hD hout haw
    · rw [hj'] at haw ⊢
      have hst' := (facts.nd.wake_st_record (W i w)).1
      have hca' := facts.nd.wake_cache (W i w)
      have _hr_s7 := facts.nd.reachedNode_wake _ (facts.ndRun.stateBeforeOf_reachedNode S rho i (W i) (hf.onePath i).1 w)
      have _hv_s8 := facts.nd.runs_as_wake _ w (facts.ndRun.stateBeforeOf_runs_as S rho i (W i) (hf.onePath i).1 w)
      exact Restated.Vocabulary.Proofs.Optimistic.on_tick_emit_vote_mem facts S w (M.wake (W i w)) d
        hd c (by rw [hst', hca']; exact hc) D (by rw [hst']; exact hD) hout haw
  exact Restated.emits_of_on_tick_emitOn facts S Hs Xb hf hw
    (Restated.Vocabulary.Proofs.Optimistic.publicTime_vote_time facts S d) hgat hhor
    (fun j hj => hf.tick_outcome j _ _ hj) ho

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Proofs.Optimistic

/-- Under the bundle along `W`, if `w ∈ Xb`, every head the in-tree head computation can return at
    `w`'s node state staged at `vote_time d` is the erasure of a run block read through `Xb` along
    `W`. -/
theorem voterHead_runBlock_of_coreOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {w : V} (hw : w ∈ Xb) (d : Slot)
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core.toHealing
      (M.vote_time S.E d)
      (W (strictEventIndex rho (M.vote_time S.E d)) w).cache ⇢ c) :
    let n := M.mkNode
      (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) w).st (M.vote_time S.E d))
      (W (strictEventIndex rho (M.vote_time S.E d)) w).record c
    ∀ T : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T →
    ∀ L : Finset (GoldfishVote V),
      M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
    ∀ L' : Finset (GoldfishVote V),
      M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
    ∀ Hd : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
        (M.toHealing n.st.core) T L L' (n.st.core.s - 1) ⇢ Hd →
    ∃ H : NamedBlock V, H.erase = Hd ∧ Restated.blockInRunOn M S rho W Xb H := by
  intro n T hT L hL L' hL' Hd hHd
  set i := strictEventIndex rho (M.vote_time S.E d) with hi_def
  have hnst₀ : n.st = M.store_with_cache (M.ns_setClock S.E (W i w).st (M.vote_time S.E d)) c :=
    facts.nd.mkNode_st _ _ _
  have hnst : n.st = M.store_with_cache (M.ns_setClock S.E (W i w).st (M.vote_time S.E d)) _ := facts.nd.mkNode_st _ _ _
  have hstT : n.st.core.T = (W i w).st.core.T := by
    rw [hnst]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    rw [facts.hd.Sts_setClock_core_T]
  have hinvPre := (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho i w
    (W i) (hf.onePath i).1).1
  have hinv0 := facts.hd.invariant_clock S.E S.cfg (W i w).st (M.vote_time S.E d) hinvPre
  have hinv : Restated.Vocabulary.Proofs.NamedConfirmationMembership.Invariant M S.E S.cfg n.st := by
    rw [hnst₀]
    exact invariant_store_with_cache₅₅b facts S.E S.cfg _ c hinv0
  have hrootMem : M.get_fg_root (M.toHealing n.st.core).toFG ∈ n.st.core.T :=
    Restated.Vocabulary.Proofs.NamedStoreRoots.fg_root_mem facts n.st hinv.1.2
  obtain ⟨R, hR⟩ := facts.fc.get_sg_root_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.s)
  have hRmem : R ∈ n.st.core.T := by
    have h := Restated.Vocabulary.Proofs.NamedProposalParent.frame_anchor_mem facts S.E S.hc
      (M.toHealing n.st.core) _ _
      (by
        show M.get_fg_root (M.toHealing n.st.core).toFG ∈
          (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.T
        rw [facts.sto.toHealing_gs_T]
        exact hrootMem) R
      ((facts.nd.gradeContract_sgRoot_eq_frameAnchor _ _ _ _ _ _).mp hR)
    have h' : R ∈ (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.T := h
    rw [facts.sto.toHealing_gs_T] at h'
    exact h'
  have hHmem := facts.fc.Sts_get_head_in_tree_with_layer_mem _ S.E S.hc _ T L L' _ R hR hRmem
    (facts.hd.Sts_voter_filtered_block_tree_subset S.E n.st.core n.st.core.s T hT) Hd hHd
  rw [hstT] at hHmem
  exact Restated.runBlock_of_mem_core_T_stateBeforeTimeOn facts S Hs Xb hf hw (M.vote_time S.E d) hHmem

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Proofs.Optimistic

/-- Under the bundle along `W` with `HonestCommitteesOn`, if `v ∈ Xb`, `0 < s`,
    `confirmation_time s` is inside the horizon, `B` satisfies `GenuineConfirmationWith` at `v`'s
    confirmation store of `s` under the cache outcome `cv`, every member of `s`'s committee in
    `Hs (confirmation_time s)` has its head vote in that store's late confirmation set,
    `lo ≤ vote_time s`, and those members' ticks at `vote_time s` pass the grade-1 awake test, then
    some such member has `B` as an ancestor of every head its vote-duty node state can compute. -/
theorem genuineConfirmation_exists_honestVoteSupporter_of_receiptsOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    {v : V} (hv : v ∈ Xb) {s : Slot} (hs : 0 < s) {B : Block V}
    (hhor : M.confirmation_time S.E s ≤ rho.horizon)
    (cv : M.Cache)
    (hcv : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core.toHealing
      (M.confirmation_time S.E s)
      (W (strictEventIndex rho (M.confirmation_time S.E s)) v).cache ⇢ cv)
    (hgenuine : Restated.Vocabulary.Protocol.GenuineConfirmationWith M (M.gradeContract cv)
      S.E S.hc (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core (M.confirmation_time S.E s)) s B)
    (hreceipt : ∀ x ∈ S.E.committee s, x ∈ Hs (M.confirmation_time S.E s) →
      ∀ c : M.Cache, M.onPhaseTick S.E S.hc
          (W (strictEventIndex rho (M.vote_time S.E s)) x).st.core.toHealing
          (M.vote_time S.E s)
          (W (strictEventIndex rho (M.vote_time S.E s)) x).cache ⇢ c →
      let n := M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) x).st (M.vote_time S.E s))
        (W (strictEventIndex rho (M.vote_time S.E s)) x).record c
      ∀ T : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T →
      ∀ L : Finset (GoldfishVote V),
        M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
      ∀ L' : Finset (GoldfishVote V),
        M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
      ∀ H : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
          (M.toHealing n.st.core) T L L' (n.st.core.s - 1) ⇢ H →
        (⟨x, s, H.root⟩ : GoldfishVote V) ∈
          Restated.Vocabulary.Protocol.confLate M S.E (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
            (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core (M.confirmation_time S.E s)) s)
    (hgat : lo ≤ M.vote_time S.E s)
    (hrun : ∀ x ∈ S.E.committee s, x ∈ Hs (M.confirmation_time S.E s) →
      ∀ j : Nat, rho.events[j]? = some (Record.Event.tick x (M.vote_time S.E s)) →
        M.awake_for_grade1 S x (W j x) (M.round_of S.hc s)) :
    ∃ x ∈ Hs (M.confirmation_time S.E s), x ∈ S.E.committee s ∧
      ∀ c : M.Cache, M.onPhaseTick S.E S.hc
          (W (strictEventIndex rho (M.vote_time S.E s)) x).st.core.toHealing
          (M.vote_time S.E s)
          (W (strictEventIndex rho (M.vote_time S.E s)) x).cache ⇢ c →
      let n := M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) x).st (M.vote_time S.E s))
        (W (strictEventIndex rho (M.vote_time S.E s)) x).record c
      ∀ T : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T →
      ∀ L : Finset (GoldfishVote V),
        M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
      ∀ L' : Finset (GoldfishVote V),
        M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
      ∀ H : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
          (M.toHealing n.st.core) T L L' (n.st.core.s - 1) ⇢ H →
        Block.Preceq B H := by
  set j := strictEventIndex rho (M.confirmation_time S.E s) with hj_def
  set i := strictEventIndex rho (M.vote_time S.E s) with hi_def
  set cw := Restated.Vocabulary.Proofs.Optimistic.tickStore M S (W j v).st.core
    (M.confirmation_time S.E s) with hcw
  set late := Restated.Vocabulary.Protocol.confLate M S.E cw s with hlate
  have hvoteHor : M.vote_time S.E s ≤ rho.horizon :=
    (facts.sch.Protocol_vote_time_le_confirmation_time S.E s).trans hhor
  have hgenuine' : Restated.Vocabulary.Protocol.GenuineConfirmation M (contract := M.gradeContract cv)
      S.E S.hc cw s B :=
    ⟨hgenuine.selected, hgenuine.genuine⟩
  obtain ⟨early, sc, hearly, hcvq, hsc, helig⟩ := genuine_eligible₅₅b facts hgenuine'
  obtain ⟨τ, hτ, hτe⟩ := returns_map_elim₅₅b _ _ _ hearly
  have hel : early ⊆ late := by
    intro u hu
    rw [← hτe, mem_beforeCutoff_iff] at hu
    have h1 := facts.sto.stampedBefore_vote_of_tau cw τ hτ hu.2
    exact Protocol.beforeCutoff_mono _ (facts.sch.Protocol_support_cutoff_le_confirmation_time S.E s) _
      ((mem_beforeCutoff_iff _ _ _ _).mpr ⟨hu.1, h1⟩)
  obtain ⟨R, hR⟩ := facts.fc.raw_supporters_nonempty cw.T
    (early.filter (fun x => M.no_second_vote_in late x = true))
    (early.filter (fun x => M.no_second_vote_in late x = true)) s B
  have hscR : sc B = R.card :=
    facts.fc.Numerator_score_eq_supporters early late _ hel rfl S.E cw.T s B (sc B) (hsc B) R hR
  choose tu htu using fun u => facts.fc.targets_under_nonempty cw.T B u
  have hrepresented : ∀ x ∈ (S.E.committee s) ∩ Hs (M.confirmation_time S.E s),
      M.participates late x = true := by
    intro x hx
    obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc (W i x).st.core.toHealing
      (M.vote_time S.E s) (W i x).cache
    let n := M.mkNode (M.ns_setClock S.E (W i x).st (M.vote_time S.E s)) (W i x).record c
    obtain ⟨T, hT⟩ := facts.fc.voter_filtered_block_tree_nonempty S.E n.st.core n.st.core.s
    obtain ⟨L, hL⟩ := facts.fc.voter_view_nonempty S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore
      n.st.core.s
    obtain ⟨L', hL'⟩ := facts.fc.voter_support_view_nonempty S.E
      (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s
    obtain ⟨H, hH⟩ := facts.fc.get_head_in_tree_with_layer_nonempty (M.gradeContract n.cache) S.E S.hc
      (M.toHealing n.st.core) T L L' (n.st.core.s - 1)
    have hraw := hreceipt x (Finset.mem_inter.mp hx).1 (Finset.mem_inter.mp hx).2 c hc T hT L hL L' hL'
      H hH
    exact (facts.sch.participates_eq_true_iff late x).mpr ⟨_, hraw, rfl⟩
  have hvalid : Protocol.VoteSetValid S.E s late := by
    rw [hlate, hcw, confLate_tickStore₅₅ facts]
    have h := Restated.voteSetValid_confLate_stateBeforeTimeOn facts S Hs Xb hf v
      (M.confirmation_time S.E s) s
    rw [Restated.Vocabulary.Protocol.confLate] at h
    exact h
  have hsupportRep : ∀ x ∈ R, M.participates late x = true := by
    intro x hx
    obtain ⟨-, u, hu, -, -⟩ := (facts.fc.mem_supporters_iff (_E := S.E) R hR tu htu).mp hx
    obtain ⟨hu1, hu2⟩ := (facts.sch.mem_votes_by_iff _ _ _).mp hu
    exact (facts.sch.participates_eq_true_iff late x).mpr
      ⟨u, hel (Finset.mem_filter.mp hu1).1, hu2⟩
  have hex : ∃ x ∈ Hs (M.confirmation_time S.E s), x ∈ R := by
    by_contra hnone
    have hdisjoint : Disjoint ((S.E.committee s) ∩ Hs (M.confirmation_time S.E s)) R := by
      apply Finset.disjoint_left.mpr
      intro x hx hsupp
      exact hnone ⟨x, (Finset.mem_inter.mp hx).2, hsupp⟩
    have hsum : ((S.E.committee s) ∩ Hs (M.confirmation_time S.E s)).card +
        R.card ≤ M.voters_count S.E late s := by
      rw [← Finset.card_union_of_disjoint hdisjoint]
      apply facts.fc.card_le_voters_count_of_participates
      intro x hx
      rcases Finset.mem_union.mp hx with h | h
      · exact hrepresented x h
      · exact hsupportRep x h
    have hcount : M.voters_count S.E late s ≤ (S.E.committee s).card :=
      facts.fc.voters_count_le_committee S.E late s hvalid
    have hmajority := hcom s
    have helig' : M.voters_count S.E late s < 2 * R.card := hscR ▸ helig
    omega
  obtain ⟨x, hxHon, hxSupport⟩ := hex
  obtain ⟨_, u, hu, hus, htargets⟩ := (facts.fc.mem_supporters_iff (_E := S.E) R hR tu htu).mp hxSupport
  have huval : u.val_index = x := ((facts.sch.mem_votes_by_iff _ _ _).mp hu).2
  have hul : u ∈ late := hel (Finset.mem_filter.mp ((facts.sch.mem_votes_by_iff _ _ _).mp hu).1).1
  have hxCommittee : x ∈ S.E.committee s := huval ▸ (hvalid u hul).2
  obtain ⟨H0, hfind, hBH⟩ := (facts.fc.targets_under_iff (tu u) (htu u)).mp htargets
  have hpool : u ∈ (W j v).st.gf_votes s := by
    have hul' := hul
    rw [hlate, hcw, confLate_tickStore₅₅ facts, mem_beforeCutoff_iff, facts.sto.mem_store_pool_iff] at hul'
    exact hul'.1
  have hTj : ∀ (j' : Nat) (e : Record.Event V), j' < j → rho.events[j']? = some e →
      e.time ≤ M.confirmation_time S.E s :=
    fun j' e hj' he => le_of_lt (time_lt_of_lt_strict₅₅b hf.sorted he hj')
  obtain ⟨tu', huemit⟩ := Restated.honestVote_emitted_of_mem_pool_stateBeforeOn facts
    S Hs Xb hf hHs v j s hTj hpool (by rw [huval]; exact hxHon)
  rw [huval] at huemit
  have hxVote : x ∈ Hs (M.vote_time S.E s) :=
    hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E s) hxHon
  have hH0T : H0 ∈ (W j v).st.core.T := by
    have h := Proofs.HealingLemmas.find?_mem hfind
    rw [hcw, tickStore_T₅₅b facts] at h
    exact h
  obtain ⟨D, hDerase, hDrun⟩ :=
    Restated.runBlock_of_mem_core_T_stateBeforeTimeOn facts S Hs Xb hf hv
      (M.confirmation_time S.E s) hH0T
  refine ⟨x, hxHon, hxCommittee, ?_⟩
  intro c hc n T hT L hL L' hL' H hH
  have hxemit := Restated.voterHead_emits_of_coreOn facts S Hs Xb hf hxVote hs hxCommittee
    hvoteHor hgat c hc (hrun x hxCommittee hxHon) T hT L hL L' hL' H hH
  have huEq : u = ⟨x, s, H.root⟩ :=
    Restated.emits_gfVote_uniqueOn facts S Hs Xb hf huemit hxemit hus
  have hroot : H0.root = H.root := by
    have h := Proofs.HealingLemmas.find?_root hfind
    simpa only [huEq] using h
  obtain ⟨X, hXerase, hXrun⟩ := Restated.voterHead_runBlock_of_coreOn facts S Hs Xb hf
    (hHsXb _ hxHon) s c hc T hT L hL L' hL' H hH
  have hrootNamed : D.root = X.root := by
    rw [← Proofs.NamedWire.erase_root D, ← Proofs.NamedWire.erase_root X, hDerase, hXerase]
    exact hroot
  have hDX : D = X := hf.rootCollisionFree.root_injective
    D X hDrun hXrun D X (Or.inl (Proofs.NamedAncestry.named_self D))
      (Or.inr (Proofs.NamedAncestry.named_self X)) hrootNamed
  calc
    Block.Preceq B H0 := preceq_eq_true_iff_Preceq.mp hBH.2
    _ = H := by rw [← hDerase, hDX, hXerase]

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Proofs.Optimistic

/-- Under the bundle along `W` with `HonestCommitteesOn`, if `v ∈ Hs (support_cutoff s)`, `0 < s`,
    `lo ≤ vote_time s`, `confirmation_time s` is inside the horizon, the ticks at `vote_time s` of
    the members of `s`'s committee in `Hs (confirmation_time s)` pass the grade-1 awake test, and
    `B` satisfies `GenuineConfirmationWith` at `v`'s confirmation store of `s` under the cache
    outcome `cv`, then some such member has `B` as an ancestor of every head its vote-duty node
    state can compute. -/
theorem genuineConfirmation_exists_honestVoteSupporter_after_gstOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    {v : V} {s : Slot} (hv : v ∈ Hs (M.support_cutoff S.E s)) (hs : 0 < s)
    {B : Block V}
    (hpost : lo ≤ M.vote_time S.E s)
    (hhor : M.confirmation_time S.E s ≤ rho.horizon)
    (cv : M.Cache)
    (hcv : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core.toHealing
      (M.confirmation_time S.E s)
      (W (strictEventIndex rho (M.confirmation_time S.E s)) v).cache ⇢ cv)
    (hgenuine : Restated.Vocabulary.Protocol.GenuineConfirmationWith M (M.gradeContract cv)
      S.E S.hc (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core (M.confirmation_time S.E s)) s B)
    (hrun : ∀ x ∈ S.E.committee s, x ∈ Hs (M.confirmation_time S.E s) →
      ∀ j : Nat, rho.events[j]? = some (Record.Event.tick x (M.vote_time S.E s)) →
        M.awake_for_grade1 S x (W j x) (M.round_of S.hc s)) :
    ∃ x ∈ Hs (M.confirmation_time S.E s), x ∈ S.E.committee s ∧
      ∀ c : M.Cache, M.onPhaseTick S.E S.hc
          (W (strictEventIndex rho (M.vote_time S.E s)) x).st.core.toHealing
          (M.vote_time S.E s)
          (W (strictEventIndex rho (M.vote_time S.E s)) x).cache ⇢ c →
      let n := M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) x).st (M.vote_time S.E s))
        (W (strictEventIndex rho (M.vote_time S.E s)) x).record c
      ∀ T : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T →
      ∀ L : Finset (GoldfishVote V),
        M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
      ∀ L' : Finset (GoldfishVote V),
        M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
      ∀ H : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
          (M.toHealing n.st.core) T L L' (n.st.core.s - 1) ⇢ H →
        Block.Preceq B H := by
  refine Restated.genuineConfirmation_exists_honestVoteSupporter_of_receiptsOn facts
    S Hs Xb hf hHs hHsXb hcom (hHsXb _ hv) hs hhor cv hcv hgenuine ?_ hpost hrun
  intro x hx hxHon c hc n T hT L hL L' hL' H hH
  have hvoteHor : M.vote_time S.E s ≤ rho.horizon :=
    (facts.sch.Protocol_vote_time_le_confirmation_time S.E s).trans hhor
  have hcut := facts.sch.Sts_support_cutoff_le_confirmation_time S.E s
  have hemit := Restated.voterHead_emits_of_coreOn facts S Hs Xb hf
    (hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E s) hxHon) hs hx hvoteHor hpost
    c hc (hrun x hx hxHon) T hT L hL L' hL' H hH
  have h := Restated.gfVote_in_cutoff_view_after_gstOn facts S Hs Xb hf hHs (hHs _ _ hcut hxHon) hs
    hpost hemit rfl hv _ _ hcut hcut (hcut.trans hhor)
  rw [confLate_tickStore₅₅ facts]
  exact h

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Proofs.HealingLemmas

/-- `cleanActionReadFor_of_actionCarriersCover_and_next_activeOn` with its carrier cover read in the
    world of `W` before `S.a r`. -/
private theorem cleanActionReadFor_of_coverAlong₅₅b (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {r : Round} {P : Block V}
    (hcover : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)),
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r,
      ∀ g, M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ g →
      ∀ B, M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc (M.toHealing n.st.core).s) g ⇢ B →
        Block.Preceq P B)
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
      (mem_stateBeforeTime_along₅₅b hf.sorted hf.onePath _) n hn g hg B hB
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

/-- Under the bundle along `W`, if the validators outside `Hs` weigh less than a third, `w`'s store
    before `read` has a fixed-height justification root at `H`, `S.E.t_GST ≤ read ≤ S.a r`, carrier
    rounds recur with gap `gap` from `t₀ ≤ read` to the horizon, `S.a (r + 4 + gap)` is inside the
    horizon, `lo ≤ read`, and the members of `Hs (S.a k + Δ)` are awake at every round `k`, then
    either the largest `h_max` over `Hs (S.a (r + 4 + gap))` exceeds `H`, or some carrier round `q`
    with `r + 3 ≤ q ≤ r + 3 + gap` gives `w`'s justified block the named grade of round `q − 1` in
    the world of `W`. -/
theorem fixedHeightJustificationRoot_boundedGradeFormsAt_of_proposerRecurrence_of_faultBoundOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hfb : BelowOneThirdOn S rho Hs)
    {H : Height} {w : V} {read : Time}
    (h : Restated.FixedHeightJustificationRootAtReadOn M S rho W Hs Xb H w read
      (W (strictEventIndex rho read)))
    {r gap : Round} {t₀ : Int}
    (hpost : S.E.t_GST ≤ read) (hreadAction : read ≤ (Restated.Vocabulary.Execution.Setup.a M S r))
    (hrecurrence : Restated.MultiProposerRecurrenceOn M S Hs gap t₀ rho.horizon)
    (hendHor : (Restated.Vocabulary.Execution.Setup.a M S (r + 4 + gap)) ≤ rho.horizon)
    (hlo : lo ≤ read) (ht₀ : t₀ ≤ read)
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    H < ((Hs (Restated.Vocabulary.Execution.Setup.a M S (r + 4 + gap))).sup fun v =>
        (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (r + 4 + gap))) v).st.core.h_max) ∨
      ∃ q : Round,
        r + 3 ≤ q ∧ q ≤ r + 3 + gap ∧
          Restated.ProposerCarrierAtOn M S Hs q ∧
            ∀ v ∈ Hs (M.domain S.E S.hc (q - 1) .g2),
              (W (strictEventIndex rho read) w).st.J ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
                  (W (strictEventIndex rho (M.domain S.E S.hc (q - 1) .g2)) v) ∧
                ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
                  (W (strictEventIndex rho (M.domain S.E S.hc (q - 1) .g2)) v).st (q - 1) .g2
                    (W (strictEventIndex rho read) w).st.J ⇢ b →
                  b = true := by
  set J := (W (strictEventIndex rho read) w).st.J with hJ_def
  by_cases hrise : H < ((Hs (Restated.Vocabulary.Execution.Setup.a M S (r + 4 + gap))).sup fun v =>
      (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (r + 4 + gap))) v).st.core.h_max)
  · exact Or.inl hrise
  · right
    have hcapEnd : ((Hs (Restated.Vocabulary.Execution.Setup.a M S (r + 4 + gap))).sup fun v =>
        (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (r + 4 + gap))) v).st.core.h_max)
          ≤ H :=
      Nat.le_of_not_gt hrise
    have hmajority : HonestWeightMajorityOn S rho Hs :=
      honestWeightMajorityOn_of_belowOneThirdOn hfb
    have hneEnd : (Hs ((Restated.Vocabulary.Execution.Setup.a M S (r + 4 + gap)))).Nonempty :=
      nonempty_of_honestWeightMajority_l54 (hmajority _ hendHor)
    have hsetCap : ∀ target : Time, (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) ≤ target →
        target + S.E.Δ < (Restated.Vocabulary.Execution.Setup.a M S (r + 4 + gap)) →
        ((Hs target).sup fun v => (W (inclusiveEventIndex rho target) v).st.core.h_max) ≤ H := by
      intro target hlow hhigh
      have hloTarget : lo ≤ target :=
        hlo.trans (hreadAction.trans ((Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.le_succ r)).trans hlow))
      exact (Restated.honestHMaxAtOn_le_of_relay_l56 facts S Hs Xb hf hHs hHsXb hloTarget hhigh hendHor
        hneEnd).trans hcapEnd
    have hrlt : r < r + 3 := Nat.lt_add_of_pos_right (by decide : 0 < 3)
    have hwindowEnd : r + 3 + gap ≤ r + 4 + gap :=
      Nat.add_le_add_right (Nat.add_le_add_left (by decide : 3 ≤ 4) r) gap
    obtain ⟨q, hqlo, hqhi, hcarrier⟩ := hrecurrence (r + 3)
      (ht₀.trans (hreadAction.trans
        ((Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans
          (Restated.Vocabulary.Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt facts S
            hrlt))))
      ((Restated.Vocabulary.Proofs.HealingLemmas.openingProposal_window_le_action facts S (r + 3) gap).trans
        ((Restated.Vocabulary.Proofs.Assembly.a_mono facts S hwindowEnd).trans hendHor))
    have hqlo' : r + 1 + 2 ≤ q := by
      simpa only [Nat.add_assoc] using hqlo
    have hqTwo : 2 ≤ q :=
      (Nat.le_add_left 2 (r + 1)).trans hqlo'
    have hqActionLower : r + 1 ≤ q - 2 :=
      Nat.le_sub_of_add_le hqlo'
    have hqActionBase : r ≤ q - 2 :=
      (Nat.le_succ r).trans hqActionLower
    have hqActionSucc : q - 2 ≤ q - 1 :=
      Nat.sub_le_sub_left (by decide : 1 ≤ 2) q
    have hbaseEnd : r + 3 ≤ r + 4 :=
      Nat.add_le_add_left (Nat.le_succ 3) r
    have hqEnd : q ≤ r + 4 + gap :=
      hqhi.trans (Nat.add_le_add_right hbaseEnd gap)
    have hqActionEnd : q - 2 ≤ r + 4 + gap :=
      (Nat.sub_le q 2).trans hqEnd
    have hqNextEnd : q - 1 ≤ r + 4 + gap :=
      (Nat.sub_le q 1).trans hqEnd
    have hqPred : q - 2 + 1 = q - 1 := by
      have hqEq : q - 2 + 2 = q := Nat.sub_add_cancel hqTwo
      rw [← hqEq]
      simp
    have hactionMono : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 2)) :=
      Restated.Vocabulary.Proofs.Assembly.a_mono facts S hqActionBase
    have hreadActionAt : read ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 2)) :=
      hreadAction.trans hactionMono
    have hdelayAction : read + S.E.Δ ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 2)) := by
      calc
        read + S.E.Δ ≤ (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ :=
          Int.add_le_add_right hreadAction S.E.Δ
        _ ≤ Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (r + 1) :=
          facts.gr.action_add_delta_le_next_Γ_neg1 S r
        _ ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) :=
          le_of_lt (Restated.Vocabulary.Proofs.HealingSurface.next_Γ_neg1_lt_action facts S r)
        _ ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 2)) := Restated.Vocabulary.Proofs.Assembly.a_mono facts S hqActionLower
    have hpostAction : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 2)) :=
      hpost.trans hreadActionAt
    have hloAction : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 2)) :=
      hlo.trans hreadActionAt
    have hactionEnd : (Restated.Vocabulary.Execution.Setup.a M S (q - 2)) ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 4 + gap)) :=
      Restated.Vocabulary.Proofs.Assembly.a_mono facts S hqActionEnd
    have hactionHor : (Restated.Vocabulary.Execution.Setup.a M S (q - 2)) ≤ rho.horizon :=
      hactionEnd.trans hendHor
    have hr1Action : (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 2)) :=
      Restated.Vocabulary.Proofs.Assembly.a_mono facts S hqActionLower
    have hcapAction := hsetCap _ hr1Action (Restated.action_add_delta_lt_action_of_lt_l67 facts S
        (lt_of_lt_of_le (Nat.sub_lt (lt_of_lt_of_le (by decide : 0 < 2) hqTwo) (by decide)) hqEnd))
    have hnextEnd : (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 4 + gap)) :=
      Restated.Vocabulary.Proofs.Assembly.a_mono facts S hqNextEnd
    have hnextHor : (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) ≤ rho.horizon :=
      hnextEnd.trans hendHor
    have hr1Next : (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) :=
      hr1Action.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hqActionSucc)
    have hcapNext := hsetCap _ hr1Next (Restated.action_add_delta_lt_action_of_lt_l67 facts S
        (lt_of_lt_of_le (Nat.sub_lt (lt_of_lt_of_le (by decide : 0 < 2) hqTwo) (by decide)) hqEnd))
    have hdelayNext : read + S.E.Δ ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) :=
      hdelayAction.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hqActionSucc)
    have hcutRaw : Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ ((q - 2) + 1) ≤ rho.horizon :=
      (le_of_lt (Restated.Vocabulary.Proofs.HealingSurface.next_Γ_neg1_lt_action facts S (q - 2))).trans
        (by rw [hqPred]; exact hnextHor)
    have hrootEq {p : V} {target : Time} (hp : p ∈ Hs target)
        (hdelay : read + S.E.Δ ≤ target)
        (hhor : target ≤ rho.horizon)
        (hcap : ((Hs target).sup fun v => (W (inclusiveEventIndex rho target) v).st.core.h_max) ≤ H) :
        M.get_fg_root (M.toHealing (W (strictEventIndex rho target) p).st.core).toFG = J := by
      have hlocalCap : (W (strictEventIndex rho target) p).st.h_max ≤ H :=
        ((Restated.storeBeforeTime_hMax_le_storeAtOn facts S Hs Xb hf p target).trans
          (Finset.le_sup (f := fun v => (W (inclusiveEventIndex rho target) v).st.core.h_max) hp)).trans hcap
      obtain ⟨carrier, hcarrierAt, _hcarrierRun, hcarrierJust, hcarrierTarget⟩ :=
        Restated.fixedHeightJustificationRootCarrier_exists_mem_laterRead_of_oneDelay_of_noRiseOn facts
          S Hs Xb hf hHs hHsXb hf.slashableBound h hp hlo hdelay hhor hcap
      exact
        Restated.fixedHeightJustificationRoot_laterFGRoot_eq_target_of_carrier_mem_of_hMax_leOn facts
          S Hs Xb hf h (hHsXb _ hp) hcarrierAt hcarrierJust hcarrierTarget hlocalCap
    have hcoverW : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 2))),
        ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 2))) v) (q - 2),
        ∀ g, M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
            (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ g →
        ∀ B, M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
            (M.round_of S.hc (M.toHealing n.st.core).s) g ⇢ B →
          Block.Preceq J B := by
      intro v hv n hn g hg B hB
      have hwd := mem_stateBeforeTime_along₅₅b hf.sorted hf.onePath
        (Restated.Vocabulary.Execution.Setup.a M S (q - 2))
      have hroot := hrootEq hv hdelayAction hactionHor hcapAction
      have h1 := Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt_fgRoot_eq_storeBeforeTime facts
        S rho v (q - 2) _ hwd n hn
      have h2 := Restated.Vocabulary.Proofs.HealingSurface.actionFGRoot_preceq_actionSGBlockAt facts
        S rho v (q - 2) _ hwd n hn g hg B hB
      rw [h1, hroot] at h2
      exact h2
    have hactiveRaw : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S ((q - 2) + 1))),
        J ∈ M.get_filtered_block_tree
          (M.toHealing
            (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S ((q - 2) + 1))) v).st.core).toFG := by
      intro v hv
      rw [hqPred] at hv ⊢
      rw [← hrootEq hv hdelayNext hnextHor hcapNext]
      exact Restated.Vocabulary.Proofs.HealingSurface.named_fgRoot_mem_filtered_stateBeforeTime facts
        S rho _ v _ (mem_stateBeforeTime_along₅₅b hf.sorted hf.onePath _)
    let domainRead := M.domain S.E S.hc (q - 1) .g2
    have hdomainAction : domainRead ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 1)) :=
      facts.gr.domain_le_a S (q - 1) .g2
    have hdomainEnd : domainRead ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 4 + gap)) :=
      hdomainAction.trans hnextEnd
    have hdomainHor : domainRead ≤ rho.horizon :=
      hdomainEnd.trans hendHor
    have hdelayDomain : read + S.E.Δ ≤ domainRead := by
      have hnext := facts.gr.action_add_delta_le_next_Γ_neg1 S (q - 2)
      rw [facts.gr.gammaNeg1_eq_domain_g2_succ S (q - 2)] at hnext
      exact hdelayAction.trans
        ((le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans
          (by simpa only [domainRead, hqPred] using hnext))
    have hr1Domain : (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) ≤ domainRead := by
      have hnext := facts.gr.action_add_delta_le_next_Γ_neg1 S (q - 2)
      rw [facts.gr.gammaNeg1_eq_domain_g2_succ S (q - 2)] at hnext
      exact hr1Action.trans
        ((le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans
          (by simpa only [domainRead, hqPred] using hnext))
    have hdomainCap := hsetCap _ hr1Domain
        (lt_of_lt_of_le (Restated.domain_add_delta_lt_action_l56 facts S (q - 1) .g2) hnextEnd)
    have hactiveDomainRaw : ∀ v ∈ Hs (M.domain S.E S.hc ((q - 2) + 1) .g2),
        J ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
          (W (strictEventIndex rho (M.domain S.E S.hc ((q - 2) + 1) .g2)) v) := by
      intro v hv
      rw [hqPred] at hv ⊢
      show J ∈ M.get_filtered_block_tree
        (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc (q - 1) .g2)) v).st.core).toFG
      rw [← hrootEq hv hdelayDomain hdomainHor hdomainCap]
      exact Restated.Vocabulary.Proofs.HealingSurface.named_fgRoot_mem_filtered_stateBeforeTime facts
        S rho _ v _ (mem_stateBeforeTime_along₅₅b hf.sorted hf.onePath _)
    have hne : (Hs ((Restated.Vocabulary.Execution.Setup.a M S ((q - 2) + 1)))).Nonempty :=
      nonempty_of_honestWeightMajority_l54 (hmajority _ (by rw [hqPred]; exact hnextHor))
    have hAq := hA (q - 2)
      (Restated.lo_le_early_g2_sub_delta_of_action_lt facts S (hlo.trans hreadAction) hqActionLower)
    have hclean := cleanActionReadFor_of_coverAlong₅₅b facts S Hs Xb hf hHs hHsXb hcoverW
      hpostAction hcutRaw hactiveRaw hactiveDomainRaw hAq hloAction
    have hformsRaw := Restated.namedGradeFormsAt_of_cleanActionReadOn facts S Hs Xb hf hHs hHsXb
      hmajority hclean hne hloAction hAq
    rw [hqPred] at hformsRaw
    exact ⟨q, hqlo, hqhi, hcarrier, hformsRaw⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation

/-- Under the bundle along `W`, if the proposer of round `q`'s opening slot is in `Hs (S.a q)`, `lo`
    is at most that slot's proposal time, `S.a q ≤ endpoint ≤ rho.horizon`, and `Hs endpoint` is not
    empty, then `ProposerProposalStoreBelowFrontierOn` holds: the proposer's `h_max` at its proposal
    time is at most the largest `h_max` over `Hs endpoint`. -/
theorem proposerProposalStoreBelowFrontierOn_of_relay (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {q : Round} {endpoint : Time}
    (hp : S.E.proposer ((M.opening_slot S.hc q)) ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)))
    (hlo : lo ≤ M.proposal_time S.E ((M.opening_slot S.hc q)))
    (hactionEnd : (Restated.Vocabulary.Execution.Setup.a M S q) ≤ endpoint) (hendHor : endpoint ≤ rho.horizon)
    (hne : (Hs endpoint).Nonempty) :
    Restated.ProposerProposalStoreBelowFrontierOn M S rho Hs q endpoint
      (W (inclusiveEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q))))
      (W (inclusiveEventIndex rho endpoint)) := by
  set s := (M.opening_slot S.hc q) with hsdef
  set p := S.E.proposer s with hpdef
  set read := M.proposal_time S.E s with hreaddef
  have hΔ := S.E.Δ_pos
  have hconf : M.confirmation_time S.E s = Restated.Vocabulary.Execution.Setup.a M S q :=
    Restated.Vocabulary.Proofs.HealingSurface.opening_confirmation_time_eq_action facts S q
  have hreadAction : read ≤ Restated.Vocabulary.Execution.Setup.a M S q := by
    rw [← hconf]
    exact facts.sch.proposal_time_le_confirmation_time S.E s
  have hreadDelta : read + S.E.Δ < Restated.Vocabulary.Execution.Setup.a M S q := by
    rw [← hconf]
    have h1 := facts.sch.proposal_time_lt_vote_time S.E s
    have h2 := facts.sch.vote_time_add_delta_le_confirmation_time S s
    linarith
  obtain ⟨w, hw⟩ := hne
  have hwXb : w ∈ Xb := hHsXb _ hw
  have hpXb : p ∈ Xb := hHsXb _ hp
  unfold Restated.ProposerProposalStoreBelowFrontierOn
  set n := inclusiveEventIndex rho read with hn_def
  set ke := inclusiveEventIndex rho endpoint with hke_def
  suffices hgoal : (W n p).st.core.h_max ≤ (W ke w).st.core.h_max by
    exact hgoal.trans (Finset.le_sup (f := fun v => (W ke v).st.core.h_max) hw)
  obtain ⟨D, hDmem, hDh⟩ := Restated.Vocabulary.Proofs.NamedStoreBridge.maximum_carrier_stateBefore facts
    S rho n p (W n) (hf.onePath n).1
  rw [← hDh]
  have hprocessed : Restated.Vocabulary.Execution.Object.processed M (W n p).st (Object.block D) = true := by
    show decide (D ∈ (W n p).st.bodies) = true
    exact decide_eq_true hDmem
  rcases Restated.Vocabulary.Protocol.acceptsAt_block_of_processed facts S rho p W hf.onePath n D hprocessed with
    hgen | ⟨i, hin, t, hacc⟩
  ·
    have hpc := Restated.Vocabulary.Proofs.NamedStoreBridge.parentClosed_stateBefore facts S rho ke w (W ke)
      (hf.onePath ke).1
    unfold Restated.Vocabulary.Internal.ParentClosed Record.Model.GS.parent_closed at hpc
    rw [facts.sto.toHealing_gs_T] at hpc
    obtain ⟨G, hG, hGerase⟩ :=
      Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore facts S rho ke w (W ke)
        (hf.onePath ke).1 hpc.1
    have hbound := Restated.Vocabulary.Proofs.NamedStoreBridge.heights_le_hMax_stateBefore facts S rho ke w
      (W ke) (hf.onePath ke).1 G hG
    have hGgen : G = NamedBlock.genesis := eq_named_genesis_of_erase_eq_genesis hGerase
    rw [hgen]
    rw [hGgen] at hbound
    exact hbound
  · obtain ⟨-, e, he, -, het⟩ := hacc.1
    have hetime : e.time ≤ read := by
      have htrue := Restated.filter_true_of_index_ltOn facts S Hs Xb hf
        (fun f : Record.Event V => decide (f.time ≤ read))
        (fun e₁ f₁ hkey hf₁ => by
          simp only [decide_eq_true_eq] at hf₁ ⊢
          exact le_trans (Restated.time_le_of_key_le hkey) hf₁) hin he
      simpa only [decide_eq_true_eq] using htrue
    have htRead : t ≤ read := by rw [← het]; exact hetime
    have hDrun : Restated.RunBlockOn M S rho W Xb D :=
      Restated.runBlock_of_stateBefore_memOn facts S W Xb hpXb hDmem
    have hDpos : 0 < D.slot := by
      have h' := Restated.Vocabulary.Protocol.parent_slot_lt_of_acceptsAt_block facts S W hf.onePath hacc
      rw [Proofs.NamedWire.erase_slot] at h'
      exact Nat.zero_lt_of_lt h'
    have hpMax : p ∈ Hs (max t lo) :=
      hHs _ _ (max_le (htRead.trans hreadAction) (hlo.trans hreadAction)) hp
    set N := strictEventIndex rho endpoint with hN_def
    by_cases hcase : (M.derive_named S.E S.cfg D).h ≤ (W N w).st.core.h_max
    · exact hcase.trans (Restated.storeBeforeTime_hMax_le_storeAtOn facts S Hs Xb hf w endpoint)
    · exfalso
      have hlt : (W N w).st.core.h_max < (M.derive_named S.E S.cfg D).h := Nat.lt_of_not_ge hcase
      have hFhist : ∀ j : Nat,
          j ≤ (rho.events.filter (fun e => decide (e.time < endpoint))).length →
            Block.Preceq (W j w).st.core.F D.erase := by
        intro j hj
        have hpreCap : (W j w).st.core.h_max ≤ (W N w).st.core.h_max :=
          Restated.Vocabulary.Proofs.HealingSurface.stateBefore_hMax_mono facts S rho w hj (W j)
            (hf.onePath j).1 (W N) (onePath_slice₅₅b W hf.onePath hj)
        obtain ⟨Dst, hDstMem, hDstF, hDstBound⟩ :=
          Restated.Vocabulary.Proofs.Bridges.storeFinalizationOnChain_stateBefore facts S rho j w (W j)
            (hf.onePath j).1
        have hDstRun : Restated.RunBlockOn M S rho W Xb Dst :=
          Restated.runBlock_of_stateBefore_memOn facts S W Xb hwXb hDstMem
        have hcrossed : (M.derive_named S.E S.cfg Dst).h_F <
            (M.derive_named S.E S.cfg D).h :=
          lt_of_lt_of_le (hDstBound.trans_le hpreCap) (le_of_lt hlt)
        have hpreceq := Restated.finalized_preceq_of_height_ltOn facts S rho W Xb D Dst hf.slashableBound
          hf.rootCollisionFree hDrun hDstRun hcrossed
        rwa [hDstF] at hpreceq
      have htIn : t < endpoint - S.E.Δ := by
        apply (lt_sub_iff_add_lt).2
        linarith
      have hgst : lo ≤ endpoint - S.E.Δ := by
        apply (le_sub_iff_add_le).2
        linarith
      have hadmit : Restated.Vocabulary.Protocol.AdmittedBefore M S rho W w D.erase endpoint :=
        Restated.block_admittedBefore_of_accepted_after_cutoffOn facts S Hs Xb hf hHs hHsXb hpMax hw hDpos
          hacc htIn hgst (sub_add_cancel endpoint S.E.Δ) hendHor hFhist
      have hmemErased : D.erase ∈ (W N w).st.core.T :=
        (Restated.admittedBefore_mem_and_stampOn facts S Hs Xb hf hadmit).1
      have hbody : D ∈ (W N w).st.bodies :=
        Restated.namedMem_of_erasedMem_stateBeforeTimeOn facts S Hs Xb hf hwXb hDrun hmemErased
      have hle := Restated.Vocabulary.Proofs.NamedStoreBridge.heights_le_hMax_stateBefore facts S rho N w
        (W N) (hf.onePath N).1 D hbody
      exact absurd hle (not_le.mpr hlt)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation

/-- Under the bundle along `W`, `ActiveExactHeightProposalRootCarrierAtOn` for round `q` at
    `endpoint` and `ProposerProposalStoreBelowFrontierOn` cannot both hold. -/
theorem activeExactHeightProposalRootCarrierAt_falseOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {H : Height} {q : Round} {endpoint : Time}
    {source root : NamedBlock V} {c : M.Cache}
    (h : Restated.ActiveExactHeightProposalRootCarrierAtOn M
      S rho W (fun t => W (strictEventIndex rho t)) (W (inclusiveEventIndex rho endpoint))
      Hs Xb H q endpoint source root c)
    (hpropFrontier : Restated.ProposerProposalStoreBelowFrontierOn M S rho Hs q endpoint
      (W (inclusiveEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q))))
      (W (inclusiveEventIndex rho endpoint))) :
    False := by
  set s := M.opening_slot S.hc q with hs_def
  set p := S.E.proposer s with hp_def
  set read := M.proposal_time S.E s with hread_def
  set i := strictEventIndex rho read with hi_def
  have hwd : W i ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho read :=
    mem_stateBeforeTime_along₅₅b hf.sorted hf.onePath read
  have hrootNe : root ≠ NamedBlock.genesis := by
    intro hroot
    subst root
    have hstrict := prec_iff_ne_Preceq.mp h.sourceStrictRoot
    rw [erase_named_genesis] at hstrict
    exact hstrict.1 (eq_genesis_of_Preceq_genesis hstrict.2)
  have hrootEq : root.erase = M.get_fg_root (M.toHealing (W i p).st.core).toFG := by
    have h1 := h.root_eq
    rewrite [facts.nd.mkNode_st] at h1; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at h1; rw [facts.hd.setClock_core_eq_store_with_t_s] at h1
    rw [h1]
    exact facts.fc.get_fg_root_set_clock_slot _ _ _
  have hrootBelow : (M.derive_named S.E S.cfg root).h < (W i p).st.core.h_max :=
    selectedFGRoot_deriveHeight_lt_hMax₅₅b facts S rho p read (W i) hwd h.rootProcessed hrootEq hrootNe
  have hpreCap : (W i p).st.core.h_max ≤ H :=
    (Restated.storeBeforeTime_hMax_le_storeAtOn facts S Hs Xb hf p read).trans
      (hpropFrontier.trans h.endpointCap)
  have hlt : H < H := by
    calc
      H = (M.derive_named S.E S.cfg root).h :=
        h.rootExactHeight.symm
      _ < (W i p).st.core.h_max := hrootBelow
      _ ≤ H := hpreCap
  exact (lt_irrefl H hlt)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation

/-- Under the hypotheses of `activeExactHeightOpeningLifecycle_or_hMaxRiseOn` other than
    `ProposerProposalStoreBelowFrontierOn`, either the largest `h_max` over `Hs endpoint` exceeds
    `H`, or the proposer's store before its proposal time shows fixed-height root interference, with
    `proposal_time ≤ S.a q ≤ endpoint ≤ rho.horizon`. -/
theorem activeExactHeightOpening_fixedInterference_or_hMaxRiseOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hfb : BelowOneThirdOn S rho Hs)
    {H : Height} {q : Round} {source : NamedBlock V} {endpoint : Time}
    (hq : 0 < q)
    (hcarrier : Restated.ProposerCarrierAtOn M S Hs q)
    (hformsPrev : ∀ v ∈ Hs (M.domain S.E S.hc (q - 1) .g2),
      source.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
          (W (strictEventIndex rho (M.domain S.E S.hc (q - 1) .g2)) v) ∧
        ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
          (W (strictEventIndex rho (M.domain S.E S.hc (q - 1) .g2)) v).st (q - 1) .g2 source.erase ⇢ b →
            b = true)
    (hwindowPrev : ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1))),
      source.erase ∈ M.get_filtered_block_tree (M.toHealing
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) w).st.core).toFG)
    (hdomainWindow : ∀ w ∈ Hs (M.domain S.E S.hc q .g2),
      source.erase ∈ M.get_filtered_block_tree (M.toHealing
        (W (strictEventIndex rho (M.domain S.E S.hc q .g2)) w).st.core).toFG)
    (hsourceRun : Restated.RunBlockOn M S rho W Xb source)
    (hsourceHeight :
      (M.derive_named S.E S.cfg source).h = H)
    (hpostPrev : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 1)))
    {B : NamedBlock V}
    (hmature : ∀ P : NamedBlock V, NamedBlock.parent? B = some P →
      (M.derive_named S.E S.cfg P).T_h.slot + S.cfg.timeoutDelay ≤ M.opening_slot S.hc q)
    (hactiveAtAction : ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)),
      source.erase ∈ M.get_filtered_block_tree
        (M.toHealing (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) w).st.core).toFG)
    (hactionEnd : (Restated.Vocabulary.Execution.Setup.a M S q) ≤ endpoint)
    (hendHor : endpoint ≤ rho.horizon)
    (hlo : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (q - 1)))
    (hloOpen : lo ≤ M.opening S.E S.hc (q - 1 - S.hc.η_SG))
    (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q - 1)) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S (q - 1))) → M.awake_for_grade2 S u (W j u) (q - 1))
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
        (S.E.proposer (M.opening_slot S.hc q))).st.core.toHealing
      (M.proposal_time S.E (M.opening_slot S.hc q))
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
        (S.E.proposer (M.opening_slot S.hc q))).cache ⇢ c)
    (hB : M.proposal_with (M.gradeContract c)
      Protocol.ProposalRowSource.poolAndCarried S.E S.hc
      (S.node (S.E.proposer (M.opening_slot S.hc q)))
      (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
          (S.E.proposer (M.opening_slot S.hc q))).st
        (M.proposal_time S.E (M.opening_slot S.hc q))) ⇢ some B) :
    H < ((Hs endpoint).sup fun v => (W (inclusiveEventIndex rho endpoint) v).st.core.h_max) ∨
      (Restated.FixedHeightRootInterferenceAtReadOn M S rho W Hs Xb H
          (S.E.proposer ((M.opening_slot S.hc q)))
          (M.proposal_time S.E ((M.opening_slot S.hc q)))
          (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q))))
          source.erase ∧
        M.proposal_time S.E ((M.opening_slot S.hc q)) ≤ (Restated.Vocabulary.Execution.Setup.a M S q) ∧
        (Restated.Vocabulary.Execution.Setup.a M S q) ≤ endpoint ∧ endpoint ≤ rho.horizon) := by
  have hpropConf : S.E.proposer ((M.opening_slot S.hc q)) ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)) := by
    have h0 := hcarrier 0 (by decide)
    simpa only [Nat.add_zero, Restated.Vocabulary.Proofs.HealingSurface.opening_confirmation_time_eq_action facts S q] using h0
  have hqpred : q - 1 < q := Nat.sub_lt hq (by decide)
  have hloRead : lo ≤ M.proposal_time S.E ((M.opening_slot S.hc q)) :=
    hlo.trans ((Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans
      (Restated.Vocabulary.Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt facts S hqpred))
  have hne : (Hs endpoint).Nonempty :=
    nonempty_of_honestWeightMajority_l54
      (honestWeightMajorityOn_of_belowOneThirdOn hfb endpoint hendHor)
  have hpropFrontier := Restated.proposerProposalStoreBelowFrontierOn_of_relay facts S Hs Xb hf hHs
    hHsXb hpropConf hloRead hactionEnd hendHor hne
  rcases Restated.activeExactHeightOpeningLifecycle_or_hMaxRiseOn facts
      S Hs Xb hf hHs hHsXb hfb hq hcarrier hformsPrev hwindowPrev hdomainWindow
        hsourceRun hsourceHeight hpostPrev hmature hactiveAtAction
        hactionEnd hendHor hlo hloOpen hA hpropFrontier c hc hB with
    hrise | hfixed | ⟨root, hroot⟩
  · exact Or.inl hrise
  · exact Or.inr hfixed
  · exact False.elim
      (Restated.activeExactHeightProposalRootCarrierAt_falseOn facts S Hs Xb hf hroot hpropFrontier)

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Statements.Instantiation

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Proofs.Optimistic

/-- Under the bundle along `W` with `HonestCommitteesOn`, if `v ∈ Hs (support_cutoff s)`, `0 < s`,
    `lo ≤ vote_time s`, `confirmation_time s` is inside the horizon, the ticks at `vote_time s` of
    the members of `s`'s committee in `Hs (confirmation_time s)` pass the grade-1 awake test, `B`
    satisfies `GenuineConfirmationWith` at `v`'s confirmation store of `s` under the cache outcome
    `cv`, and each such member's vote-duty node state can compute a head descending from `C`, then
    `C` and `B` are compatible. -/
theorem genuineConfirmation_compatible_of_priorProtectedHeadsOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    {v : V} {s : Slot} (hv : v ∈ Hs (M.support_cutoff S.E s)) (hs : 0 < s)
    {B C : Block V}
    (hpost : lo ≤ M.vote_time S.E s)
    (hhor : M.confirmation_time S.E s ≤ rho.horizon)
    (cv : M.Cache)
    (hcv : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core.toHealing
      (M.confirmation_time S.E s)
      (W (strictEventIndex rho (M.confirmation_time S.E s)) v).cache ⇢ cv)
    (hgenuine : Restated.Vocabulary.Protocol.GenuineConfirmationWith M (M.gradeContract cv)
      S.E S.hc (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.confirmation_time S.E s)) v).st.core (M.confirmation_time S.E s)) s B)
    (hprotected : ∀ x ∈ Hs (M.confirmation_time S.E s), x ∈ S.E.committee s →
      ∃ c : M.Cache, M.onPhaseTick S.E S.hc
          (W (strictEventIndex rho (M.vote_time S.E s)) x).st.core.toHealing
          (M.vote_time S.E s)
          (W (strictEventIndex rho (M.vote_time S.E s)) x).cache ⇢ c ∧
      let n := M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) x).st (M.vote_time S.E s))
        (W (strictEventIndex rho (M.vote_time S.E s)) x).record c
      ∃ T : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T ∧
      ∃ L : Finset (GoldfishVote V),
        M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L ∧
      ∃ L' : Finset (GoldfishVote V),
        M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' ∧
      ∃ H : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
          (M.toHealing n.st.core) T L L' (n.st.core.s - 1) ⇢ H ∧
        Block.Preceq C H)
    (hrun : ∀ x ∈ S.E.committee s, x ∈ Hs (M.confirmation_time S.E s) →
      ∀ j : Nat, rho.events[j]? = some (Record.Event.tick x (M.vote_time S.E s)) →
        M.awake_for_grade1 S x (W j x) (M.round_of S.hc s)) :
    Block.compatible C B = true := by
  obtain ⟨x, hxHon, hxCommittee, hBX⟩ :=
    Restated.genuineConfirmation_exists_honestVoteSupporter_after_gstOn facts S Hs Xb hf hHs
      hHsXb hcom hv hs hpost hhor cv hcv hgenuine hrun
  obtain ⟨c, hc, T, hT, L, hL, L', hL', H, hH, hCH⟩ := hprotected x hxHon hxCommittee
  exact compatible_of_preceq_common_Preceq hCH (hBX c hc T hT L hL L' hL' H hH)

end

end DecoupledConsensusModel.Sts.Restated
