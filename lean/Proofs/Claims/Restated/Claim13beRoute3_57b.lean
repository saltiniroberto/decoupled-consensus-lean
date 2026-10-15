import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13beRoute3_45
import Proofs.Claims.Restated.Claim13beRoute3_47b
import Proofs.Claims.Restated.Claim13beRoute3_49
import Proofs.Claims.Restated.Claim13beRoute3_50b
import Proofs.Claims.Restated.Claim13beRoute3_51
import Proofs.Claims.Restated.Claim13beRoute3_52
import Proofs.Claims.Restated.Claim13beRoute3_52b
import Proofs.Claims.Restated.Claim13beRoute3_53
import Proofs.Claims.Restated.Claim13beRoute3_56
import Proofs.Claims.Restated.Vocabulary_Execution_ExcludesRefute
import Proofs.Claims.Restated.Vocabulary_Execution_HealthyLocalFacts
import Proofs.Claims.Restated.Vocabulary_ModelVocabulary_Healing_Schedule
import Proofs.Claims.Restated.Vocabulary_Protocol_ChainState_ProposalBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_SlotInduction
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_42c
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.RunVocabulary
import Model.Conditions.Vocabulary_Internal_Definitions_NamedDerived
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGradeQueries
import Model.Conditions.Vocabulary_Internal_Internal_GradeReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedReceiptCalls
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_ModelVocabulary_Healing_Schedule
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_Handlers_Blocks
import Model.Conditions.Vocabulary_Statements_Instantiation_Proposals
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_25
import Proofs.Claims.Spec2Claims.Claim13beRoute3_57b

/-!
# Vote names, opening proposals and the checkpoint of a height window

Theorems over a model `M : Record.Model V` and its facts `facts : Record.Facts M`, read along the
path `W` that the bundle `AdmissibleFieldsOn` binds: honest vote names from vote stores, an opening
proposal reaching the next round's readers, and the checkpoint of a height window.
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
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation

/-- Under the bundle along `W`, if `0 < s`, `vote_time s` is inside the horizon and at or after
    `lo`, every committee member of `s` in the set for `vote_time s` has a vote store, staged from
    `W`'s world before `vote_time s`, whose walk extends to `P`, and each such member's node state
    before its tick at `vote_time s` passes the grade-1 awake test of `s`'s round, then every such
    member emitted at `vote_time s`, along `W`, the vote naming `P`'s erasure. -/
theorem namedHonestVotesName_of_namedVoteStoresExtendOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {s : Slot} (hs : 0 < s)
    (hvoteHor : M.vote_time S.E s ≤ rho.horizon)
    {P : NamedBlock V}
    (hstores : Restated.VoteStoresExtendOn M S rho Hs s
      (W (strictEventIndex rho (M.vote_time S.E s))) P)
    (hgat : lo ≤ M.vote_time S.E s)
    (hrun : ∀ v ∈ Hs (M.vote_time S.E s), v ∈ S.E.committee s →
      ∀ j : Nat, rho.events[j]? = some (Record.Event.tick v (M.vote_time S.E s)) →
        M.awake_for_grade1 S v (W j v) (M.round_of S.hc s)) :
    Restated.NamedHonestVotesNameOn M S rho W Hs s P.erase :=
  Restated.honestVotesName_of_voteStoresExtendOn facts S Hs Xb hf hs hvoteHor hgat hstores
    (fun _ _ _ j hj => hf.tick_outcome j _ _ hj) hrun

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

/-- If `s ≤ opening_slot (q + 1)`, then `proposal_time s + Δ < S.a (q + 1)`. -/
theorem proposal_add_delta_lt_next_action_l57 (facts : Record.Facts M) (S : Setup V) (q : Round) {s : Slot}
    (hs : s ≤ (M.opening_slot S.hc (q + 1))) :
    M.proposal_time S.E s + S.E.Δ < (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) := by
  have hmono : M.proposal_time S.E s ≤
      M.proposal_time S.E ((M.opening_slot S.hc (q + 1))) :=
    facts.sch.proposal_time_mono S.E hs
  have ha : (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) =
      M.confirmation_time S.E ((M.opening_slot S.hc (q + 1))) := by
    rw [Restated.Vocabulary.Execution.Setup.a, Restated.Vocabulary.Protocol.a_eq_confirmation_time facts]
  have hpv := facts.sch.proposal_time_lt_vote_time S.E ((M.opening_slot S.hc (q + 1)))
  have hvc := facts.sch.vote_time_add_delta_le_confirmation_time S ((M.opening_slot S.hc (q + 1)))
  rw [ha]
  linarith

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

/-- The next round's grade-2 domain is one delay before the next opening slot's proposal instant:
    `domain (q + 1) .g2 + Δ = proposal_time (opening_slot (q + 1))`. -/
theorem domain_g2_succ_add_delta_l57 (facts : Record.Facts M) (S : Setup V) (q : Round) :
    M.domain S.E S.hc (q + 1) .g2 + S.E.Δ =
      M.proposal_time S.E ((M.opening_slot S.hc (q + 1))) := by
  have h1 := facts.gr.gammaNeg1_eq_domain_g2_succ S q
  have h2 := facts.sch.Γ_0_eq_proposal_time S.hc S.E (q + 1)
  rw [← h1, ← h2]
  ring

end

/-! ## Helpers along a path -/

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Proofs.HealingSurface
open scoped DC

/-- In a run sorted by key, the worlds strictly before the instant `t` are the worlds before the
    event whose index is `strictEventIndex rho t`. -/
private theorem stateBeforeTime_eq_strict₅₇b (S : Setup V) (rho : Record.Run V)
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

/-- In a run sorted by key, the world of a path `W` before the event whose index is
    `strictEventIndex rho t` is a world strictly before the instant `t`. -/
private theorem mem_stateBeforeTime_along₅₇b {S : Setup V} {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (t : Time) :
    W (strictEventIndex rho t) ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t := by
  rw [stateBeforeTime_eq_strict₅₇b S rho hsorted]
  exact (hW _).1

/-- For every path `W` of `rho`, `W (m + k)` is among the worlds the events `m` to `m + k - 1` of
    `rho` lead to from `W m`. -/
private theorem onePath_reach₅₇b {S : Setup V} {rho : Record.Run V}
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
private theorem onePath_slice₅₇b {S : Setup V} {rho : Record.Run V}
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) {m n : Nat}
    (hmn : m ≤ n) :
    W n ∈ ((rho.events.drop m).take (n - m)).foldlM (Record.worldStepOf M S) (W m) := by
  have h := onePath_reach₅₇b W hW m (n - m)
  rwa [Nat.add_sub_of_le hmn] at h

open scoped DC in
/-- Every outcome of slot `s`'s proposal duty, run on the proposer's node state in
    `W (strictEventIndex rho (proposal_time s))` with the grade contract of a cache-update outcome
    `c`, is one of the values `proposedBlockAt M S rho s`. -/
private theorem proposedBlockAt_mem₅₇b (facts : Record.Facts M) (S : Setup V)
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
  ⟨M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).st
      (M.proposal_time S.E s))
    (W (strictEventIndex rho (M.proposal_time S.E s)) (S.E.proposer s)).record c,
    ⟨W (strictEventIndex rho (M.proposal_time S.E s)),
      mem_stateBeforeTime_along₅₇b hf.sorted hf.onePath _, c, hc, rfl⟩,
    by rw [facts.nd.mkNode_cache, facts.nd.mkNode_st, facts.dt.proposal_with_store_with_cache]; exact ho⟩

omit [DecidableEq V] [Fintype V] in
/-- For `Δ > 0`, if `a` and `b` are multiples of `Δ` and `a < b`, then `a + Δ ≤ b`. -/
private theorem add_delta_le_of_lt_emod₅₇b {Δ a b : Int} (hΔ : 0 < Δ) (ha : a % Δ = 0)
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

/-- A slot's vote instant is at most the slot's support cutoff minus one delay. -/
private theorem vote_time_le_support_cutoff_sub₅₇b (facts : Record.Facts M) (S : Setup V)
    (s : Slot) : M.vote_time S.E s ≤ M.support_cutoff S.E s - S.E.Δ :=
  le_sub_iff_add_le.mpr (add_delta_le_of_lt_emod₅₇b S.E.Δ_pos (facts.sch.vote_time_emod_delta S s)
    (facts.sch.support_cutoff_emod_delta S s) (Restated.vote_time_lt_support_cutoff_l49 facts S s))

/-- Every node state the round-`r` action read computed from `before` can give holds the bodies
    `before` holds. -/
private theorem actionReadFrom_bodies₅₇b (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ nr ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      nr.st.bodies = before.st.bodies := by
  rintro _ ⟨c, -, st, hst, rfl⟩
  rw [facts.nd.mkNode_st, facts.nd.store_with_cache_bodies,
    facts.dt.named_update_confirmation_with_bodies _ _ _ _ _ st hst,
    facts.hd.ModelProperties_setClock_bodies]

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
open DecoupledConsensusModel.Proofs.Optimistic

/-- Under the bundle along `W` and `BelowOneThirdOn`, if `w`'s store in `W`'s world before `read` is
    a fixed-height justification root at `H`, `lo ≤ read ≤ S.a r`, `r + 3 ≤ q ≤ r + 3 + gap`, the
    proposers of `q`'s first three opening slots are each in the set for their confirmation instant,
    `P` is a proposal of the first slot's proposer, `w`'s justified block there is an ancestor of
    `P`'s erasure, and `S.a (r + 4 + gap)` is inside the horizon, then either the largest `h_max`
    over the family at `S.a (r + 4 + gap)` exceeds `H`, or `P`'s erasure is in the filtered tree of
    every member of the set for `S.a (q + 1)` at its round-`(q + 1)` store and of every member of
    the set for the next round's grade-2 domain at its node state there. -/
theorem fixedHeightJustificationRoot_namedOpeningProposal_nextActive_or_hMaxRiseOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hfb : BelowOneThirdOn S rho Hs)
    {H : Height} {w : V} {read : Time}
    (hfix : Restated.FixedHeightJustificationRootAtReadOn M S rho W Hs Xb H w read
      (W (strictEventIndex rho read)))
    {r gap q : Round}
    (hpost : lo ≤ read)
    (hreadAction : read ≤ (Restated.Vocabulary.Execution.Setup.a M S r))
    (hqlo : r + 3 ≤ q)
    (hqhi : q ≤ r + 3 + gap)
    (hcarrier : Restated.ProposerCarrierAtOn M S Hs q)
    (cp : M.Cache)
    (hcp : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
        (S.E.proposer (M.opening_slot S.hc q))).st.core.toHealing
      (M.proposal_time S.E (M.opening_slot S.hc q))
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
        (S.E.proposer (M.opening_slot S.hc q))).cache ⇢ cp)
    {P : NamedBlock V}
    (hP : M.proposal_with (M.gradeContract cp)
      Protocol.ProposalRowSource.poolAndCarried S.E S.hc (S.node (S.E.proposer (M.opening_slot S.hc q)))
      (M.ns_setClock S.E (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q)))
        (S.E.proposer (M.opening_slot S.hc q))).st
        (M.proposal_time S.E (M.opening_slot S.hc q))) ⇢ some P)
    (hJP : Block.Preceq (W (strictEventIndex rho read) w).st.J P.erase)
    (hendHor : (Restated.Vocabulary.Execution.Setup.a M S (r + 4 + gap)) ≤ rho.horizon) :
    H < ((Hs (Restated.Vocabulary.Execution.Setup.a M S (r + 4 + gap))).sup fun u =>
        (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (r + 4 + gap))) u).st.core.h_max) ∨
      (∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q + 1))),
        P.erase ∈ M.get_filtered_block_tree
          (M.toHealing (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q + 1))) v).st.core).toFG) ∧
      (∀ v ∈ Hs (M.domain S.E S.hc (q + 1) .g2),
        P.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
          (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g2)) v)) := by
  -- The opening proposer passes the grade-1 awake test at its proposal tick.
  have hrun : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick (S.E.proposer (M.opening_slot S.hc q))
        (M.proposal_time S.E (M.opening_slot S.hc q))) →
      M.awake_for_grade1 S (S.E.proposer (M.opening_slot S.hc q))
        (W j (S.E.proposer (M.opening_slot S.hc q))) (M.round_of S.hc (M.opening_slot S.hc q)) := by
    have hwin : lo ≤ M.early S.E S.hc (M.round_of S.hc (M.opening_slot S.hc q)) .g1 - S.E.Δ := by
      rw [facts.gr.round_of_opening_slot_eq S.hc q]
      have h1 := facts.gr.action_delta_le_early S S.hc.R_ge_three
        (Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide : 0 < 3)) hqlo)
      have h2 := facts.gr.early_g2_add_delta_le_early_g1 S q
      have h3 : lo ≤ M.a S.hc S.E.Δ r := hpost.trans hreadAction
      have h4 : 0 < S.E.Δ := S.E.Δ_pos
      linarith
    intro j hj
    exact hf.awake_g1 _ _ j _ (Or.inl rfl) hj
      (hHs _ _ (facts.sch.proposal_time_le_confirmation_time S.E _) (hcarrier 0 (by decide))) hwin
  let s0 : Slot := (M.opening_slot S.hc q)
  let s1 : Slot := s0 + 1
  let s2 : Slot := s1 + 1
  have hrq : r < q :=
    (Nat.lt_succ_self r).trans_le
      ((Nat.add_le_add_left (by decide : 1 ≤ 3) r).trans hqlo)
  have hqpos : 0 < q := (Nat.zero_le r).trans_lt hrq
  have hqEnd : q + 1 ≤ r + 4 + gap := by
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      Nat.add_le_add_right hqhi 1
  have hs0pos : 0 < s0 := by
    exact facts.gr.opening_slot_pos_of_round_pos S.hc hqpos
  have hs01 : s0 ≤ s1 := by simpa only [s1] using Nat.le_succ s0
  have hs12 : s1 ≤ s2 := by simpa only [s2] using Nat.le_succ s1
  have hs02 : s0 ≤ s2 := hs01.trans hs12
  have hs2Next : s2 ≤ (M.opening_slot S.hc (q + 1)) := by
    have hslots : (M.opening_slot S.hc q) + 2 ≤
        (M.opening_slot S.hc (q + 1)) := by
      rw [facts.gr.opening_slot_succ_eq]
      exact Nat.add_le_add_left S.hc.R_ge_two _
    simpa only [s2, s1, s0, Nat.add_assoc] using hslots
  have hs1Next : s1 ≤ (M.opening_slot S.hc (q + 1)) := hs12.trans hs2Next
  have hs0Next : s0 ≤ (M.opening_slot S.hc (q + 1)) := hs02.trans hs2Next
  have hproposalOpenNextAction :
      M.proposal_time S.E ((M.opening_slot S.hc (q + 1))) ≤
        (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) := by
    rw [Restated.Vocabulary.Execution.Setup.a, Restated.Vocabulary.Protocol.a_eq_confirmation_time facts]
    exact facts.sch.proposal_time_le_confirmation_time S.E _
  have hsupportOpenNextAction :
      M.support_cutoff S.E ((M.opening_slot S.hc (q + 1))) ≤
        (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) := by
    rw [Restated.Vocabulary.Execution.Setup.a, Restated.Vocabulary.Protocol.a_eq_confirmation_time facts]
    exact facts.sch.Protocol_support_cutoff_le_confirmation_time S.E _
  have hproposal0Action : M.proposal_time S.E s0 ≤ (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) :=
    (facts.sch.proposal_time_mono S.E hs0Next).trans hproposalOpenNextAction
  have hproposal1Action : M.proposal_time S.E s1 ≤ (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) :=
    (facts.sch.proposal_time_mono S.E hs1Next).trans hproposalOpenNextAction
  have hproposal2Action : M.proposal_time S.E s2 ≤ (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) :=
    (facts.sch.proposal_time_mono S.E hs2Next).trans hproposalOpenNextAction
  have hsupport2Action : M.support_cutoff S.E s2 ≤ (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) :=
    (Restated.Vocabulary.Proofs.Optimistic.support_cutoff_mono facts S.E hs2Next).trans hsupportOpenNextAction
  have hactionNextEnd : (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 4 + gap)) :=
    Restated.Vocabulary.Proofs.Assembly.a_mono facts S hqEnd
  have hnextHor : (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) ≤ rho.horizon := hactionNextEnd.trans hendHor
  have hproposal0Hor : M.proposal_time S.E s0 ≤ rho.horizon :=
    hproposal0Action.trans hnextHor
  have hproposal1Hor : M.proposal_time S.E s1 ≤ rho.horizon :=
    hproposal1Action.trans hnextHor
  have hproposal2Hor : M.proposal_time S.E s2 ≤ rho.horizon :=
    hproposal2Action.trans hnextHor
  have hsupport01 : M.support_cutoff S.E s0 ≤
      M.proposal_time S.E s1 := by
    simpa only [s1] using
      facts.sch.support_cutoff_le_proposal_time_succ S.E s0
  have hsupport12 : M.support_cutoff S.E s1 ≤
      M.proposal_time S.E s2 := by
    simpa only [s2] using
      facts.sch.support_cutoff_le_proposal_time_succ S.E s1
  have hsupport0Hor : M.support_cutoff S.E s0 ≤ rho.horizon :=
    hsupport01.trans hproposal1Hor
  have hsupport1Hor : M.support_cutoff S.E s1 ≤ rho.horizon :=
    hsupport12.trans hproposal2Hor
  have hsupport2Hor : M.support_cutoff S.E s2 ≤ rho.horizon :=
    hsupport2Action.trans hnextHor
  have hactionDelay : (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ ≤ M.proposal_time S.E s0 := by
    simpa only [s0] using
      (Restated.Vocabulary.Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt facts S hrq)
  have hreadDelay0 : read + S.E.Δ ≤ M.proposal_time S.E s0 :=
    (Int.add_le_add_right hreadAction S.E.Δ).trans hactionDelay
  have hreadDelay1 : read + S.E.Δ ≤ M.proposal_time S.E s1 :=
    hreadDelay0.trans (facts.sch.proposal_time_mono S.E hs01)
  have hreadDelay2 : read + S.E.Δ ≤ M.proposal_time S.E s2 :=
    hreadDelay0.trans (facts.sch.proposal_time_mono S.E hs02)
  have hreadDelayNext : read + S.E.Δ ≤ (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) :=
    hreadDelay0.trans hproposal0Action
  have hpostProposal0 : lo ≤ M.proposal_time S.E s0 :=
    (hpost.trans (Int.le_add_of_nonneg_right (le_of_lt S.E.Δ_pos))).trans
      hreadDelay0
  have hpostProposal1 : lo ≤ M.proposal_time S.E s1 :=
    hpostProposal0.trans (facts.sch.proposal_time_mono S.E hs01)
  have hpostVote0 : lo ≤ M.vote_time S.E s0 :=
    hpostProposal0.trans
      (le_of_lt (facts.sch.proposal_time_lt_vote_time S.E s0))
  have hpostVote1 : lo ≤ M.vote_time S.E s1 :=
    hpostVote0.trans (facts.sch.vote_time_mono_slots S.E hs01)
  have hpostVote2 : lo ≤ M.vote_time S.E s2 :=
    hpostVote1.trans (facts.sch.vote_time_mono_slots S.E hs12)
  have hprop0 : S.E.proposer s0 ∈ Hs (M.confirmation_time S.E s0) := by
    simpa only [s0, Nat.add_zero] using hcarrier 0 (by decide)
  have hprop1 : S.E.proposer s1 ∈ Hs (M.confirmation_time S.E s1) := by
    simpa only [s1, s0] using hcarrier 1 (by decide)
  have hprop2 : S.E.proposer s2 ∈ Hs (M.confirmation_time S.E s2) := by
    simpa only [s2, s1, s0, Nat.add_assoc] using hcarrier 2 (by decide)
  have hPslot : 0 < P.slot := by
    rw [Restated.Vocabulary.Proofs.HealingSurface.proposedBlockAt_slot facts S rho ((M.opening_slot S.hc q))
      (some P) (proposedBlockAt_mem₅₇b facts S hf _ cp hcp hP) rfl]
    simpa only [s0] using hs0pos
  have hPrun : Restated.RunBlockOn M S rho W Xb P :=
    Restated.proposedBlockAt_blockInRun_of_admissibleOn facts S Hs Xb hf hHs hHsXb
      ((M.opening_slot S.hc q)) (by simpa only [s0] using hs0pos)
      (by simpa only [s0] using hprop0)
      (by simpa only [s0] using hproposal0Hor)
      (by simpa only [s0] using hpostProposal0) (fun j hj => hf.tick_outcome j _ _ hj) hrun cp hcp hP
  obtain ⟨Jn, hJnErase, hJnRun, hJnHeight⟩ :=
    Restated.fixedRoot_namedTarget_of_fixedRootOn facts S Hs Xb hfix
  obtain ⟨Jp, hJpP, hJpErase⟩ := Proofs.NamedAncestry.erased_ancestor_lift P hJP
  have hJpRun : Restated.RunBlockOn M S rho W Xb Jp :=
    Restated.blockInRun_of_ancestorOn facts S rho W Xb hPrun hJpP
  have hJpEq : Jp = Jn := by
    apply hf.rootCollisionFree.root_injective Jp Jn hJpRun hJnRun Jp Jn
      (Or.inl (Proofs.NamedAncestry.named_self Jp))
      (Or.inr (Proofs.NamedAncestry.named_self Jn))
    rw [← Proofs.NamedWire.erase_root Jp, ← Proofs.NamedWire.erase_root Jn,
      hJpErase, hJnErase]
  have hPheight : H - 1 ≤ (M.derive_named S.E S.cfg P).h := by
    rw [← hJnHeight, ← hJpEq]
    exact facts.cs.derive_height_mono S.E S.cfg hJpP
  by_cases hrise : H < ((Hs (Restated.Vocabulary.Execution.Setup.a M S (r + 4 + gap))).sup fun u =>
      (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (r + 4 + gap))) u).st.core.h_max)
  · exact Or.inl hrise
  right
  have hcapEnd : ((Hs (Restated.Vocabulary.Execution.Setup.a M S (r + 4 + gap))).sup fun u =>
      (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (r + 4 + gap))) u).st.core.h_max) ≤ H :=
    Nat.le_of_not_gt hrise
  have hne : ∀ u : Time, u ≤ rho.horizon → (Hs u).Nonempty := fun u hu =>
    nonempty_of_honestWeightMajority_l54
      (AlignedRoundLemmas.honestWeightMajority_of_belowOneThird (hfb u hu))
  have hloNext : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) :=
    (hpost.trans (Int.le_add_of_nonneg_right (le_of_lt S.E.Δ_pos))).trans hreadDelayNext
  have hcapNext : ((Hs (Restated.Vocabulary.Execution.Setup.a M S (q + 1))).sup fun u =>
      (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (q + 1))) u).st.core.h_max) ≤ H := by
    rcases eq_or_lt_of_le hqEnd with heq | hlt
    · rw [heq]
      exact hcapEnd
    · have hstep := Restated.action_add_one_add_delta_le_next_action_l52 facts S (q + 1)
      have hmono : (Restated.Vocabulary.Execution.Setup.a M S (q + 1 + 1)) ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 4 + gap)) := Restated.Vocabulary.Proofs.Assembly.a_mono facts S hlt
      exact (Restated.honestHMaxAtOn_le_of_relay_l56 facts S Hs Xb hf hHs hHsXb hloNext
        (by linarith) hendHor (hne _ hendHor)).trans hcapEnd
  have hcapBefore : ∀ t : Time, lo ≤ t → t + S.E.Δ < (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) →
      ((Hs t).sup fun u => (W (inclusiveEventIndex rho t) u).st.core.h_max) ≤ H := fun t hlot ht =>
    (Restated.honestHMaxAtOn_le_of_relay_l56 facts S Hs Xb hf hHs hHsXb hlot ht hnextHor
      (hne _ hnextHor)).trans hcapNext
  have hcap1 : ((Hs (M.proposal_time S.E s1)).sup fun u =>
      (W (inclusiveEventIndex rho (M.proposal_time S.E s1)) u).st.core.h_max) ≤ H :=
    hcapBefore _ hpostProposal1 (Restated.proposal_add_delta_lt_next_action_l57 facts S q hs1Next)
  have hcap2 : ((Hs (M.proposal_time S.E s2)).sup fun u =>
      (W (inclusiveEventIndex rho (M.proposal_time S.E s2)) u).st.core.h_max) ≤ H :=
    hcapBefore _ (hpostProposal1.trans (facts.sch.proposal_time_mono S.E hs12))
      (Restated.proposal_add_delta_lt_next_action_l57 facts S q hs2Next)
  have hsb : Restated.SlashableBoundOn M S rho W Xb := hf.slashableBound
  have hp1target : S.E.proposer s1 ∈ Hs (M.proposal_time S.E s1) :=
    hHs _ _ (facts.sch.proposal_time_le_confirmation_time S.E s1) hprop1
  have hp2target : S.E.proposer s2 ∈ Hs (M.proposal_time S.E s2) :=
    hHs _ _ (facts.sch.proposal_time_le_confirmation_time S.E s2) hprop2
  obtain ⟨hroot1, -⟩ :=
    Restated.fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRiseOn facts
      S Hs Xb hf hHs hHsXb hsb hfix hp1target hpost hreadDelay1 hproposal1Hor hcap1
  obtain ⟨hroot2, -⟩ :=
    Restated.fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRiseOn facts
      S Hs Xb hf hHs hHsXb hsb hfix hp2target hpost hreadDelay2 hproposal2Hor hcap2
  have hroot1P : Block.Preceq
      (M.get_fg_root (M.toHealing
        (W (strictEventIndex rho (M.proposal_time S.E s1)) (S.E.proposer s1)).st.core).toFG) P.erase := by
    unfold Record.Model.NS.toHealing at hroot1
    rw [hroot1]
    exact hJP
  have hroot2P : Block.Preceq
      (M.get_fg_root (M.toHealing
        (W (strictEventIndex rho (M.proposal_time S.E s2)) (S.E.proposer s2)).st.core).toFG) P.erase := by
    unfold Record.Model.NS.toHealing at hroot2
    rw [hroot2]
    exact hJP
  obtain ⟨i0, hacc0⟩ := Restated.acceptsAt_proposedBlockOn facts S Hs Xb hf hHs
    (by simpa only [s0] using hs0pos) (by simpa only [s0] using hprop0)
      (by simpa only [s0] using hproposal0Hor)
      (by simpa only [s0] using hpostProposal0) (fun j hj => hf.tick_outcome j _ _ hj) hrun cp hcp hP
  have hFhist1 : ∀ j : Nat,
      j ≤ (rho.events.filter (fun e => decide (e.time < M.support_cutoff S.E s0))).length →
        Block.Preceq (W j (S.E.proposer s1)).st.core.F P.erase := by
    intro j hj
    have hj' : j ≤ strictEventIndex rho (M.proposal_time S.E s1) :=
      hj.trans (strict_filter_length_mono rho hsupport01)
    exact Restated.Vocabulary.Proofs.finalized_preceq_at_prefix_of_storeBeforeRoot_preceq facts S rho
      hf.sorted (w := S.E.proposer s1) hj' (W j) (hf.onePath j).1 _
      (onePath_slice₅₇b W hf.onePath hj') hroot1P
  have hp0max : S.E.proposer s0 ∈ Hs (max (M.proposal_time S.E s0) lo) := by
    rw [max_eq_left hpostProposal0]
    exact hHs _ _ (facts.sch.proposal_time_le_confirmation_time S.E s0) hprop0
  have hp1cut : S.E.proposer s1 ∈ Hs (M.support_cutoff S.E s0) :=
    hHs _ _ (hsupport01.trans (facts.sch.proposal_time_le_confirmation_time S.E s1)) hprop1
  have hadmit1 : Restated.Vocabulary.Protocol.AdmittedBefore M S rho W (S.E.proposer s1) P.erase
      (M.support_cutoff S.E s0) :=
    Restated.block_admittedBefore_of_accepted_after_cutoffOn facts
      S Hs Xb hf hHs hHsXb hp0max hp1cut hPslot hacc0
        ((facts.sch.proposal_time_lt_vote_time S.E s0).trans_le
          (vote_time_le_support_cutoff_sub₅₇b facts S s0))
        (hpostVote0.trans (vote_time_le_support_cutoff_sub₅₇b facts S s0))
        (Int.sub_add_cancel _ _) hsupport0Hor hFhist1
  obtain ⟨P1, hP1erase, i1, t1, hacc1, ht1⟩ := hadmit1
  have hP1slot : 0 < P1.slot := by
    rw [← Proofs.NamedWire.erase_slot P1, hP1erase, Proofs.NamedWire.erase_slot P]
    exact hPslot
  have ht1In : t1 < M.vote_time S.E s1 :=
    ht1.trans_le (by simpa only [s1] using
      facts.sch.support_cutoff_le_vote_time_succ S.E s0)
  have hFhist2 : ∀ j : Nat,
      j ≤ (rho.events.filter (fun e => decide (e.time < M.support_cutoff S.E s1))).length →
        Block.Preceq (W j (S.E.proposer s2)).st.core.F P1.erase := by
    intro j hj
    have hroot2P1 : Block.Preceq
        (M.get_fg_root (M.toHealing
          (W (strictEventIndex rho (M.proposal_time S.E s2)) (S.E.proposer s2)).st.core).toFG)
        P1.erase := by
      simpa only [hP1erase] using hroot2P
    have hj' : j ≤ strictEventIndex rho (M.proposal_time S.E s2) :=
      hj.trans (strict_filter_length_mono rho hsupport12)
    exact Restated.Vocabulary.Proofs.finalized_preceq_at_prefix_of_storeBeforeRoot_preceq facts S rho
      hf.sorted (w := S.E.proposer s2) hj' (W j) (hf.onePath j).1 _
      (onePath_slice₅₇b W hf.onePath hj') hroot2P1
  have hp1max : S.E.proposer s1 ∈ Hs (max t1 lo) :=
    hHs _ _ ((max_le (le_of_lt ht1In) hpostVote1).trans
      (facts.sch.Protocol_vote_time_le_confirmation_time S.E s1)) hprop1
  have hp2cut : S.E.proposer s2 ∈ Hs (M.support_cutoff S.E s1) :=
    hHs _ _ (hsupport12.trans (facts.sch.proposal_time_le_confirmation_time S.E s2)) hprop2
  have hadmit2 : Restated.Vocabulary.Protocol.AdmittedBefore M S rho W (S.E.proposer s2) P1.erase
      (M.support_cutoff S.E s1) :=
    Restated.block_admittedBefore_of_accepted_after_cutoffOn facts
      S Hs Xb hf hHs hHsXb hp1max hp2cut hP1slot hacc1
        (ht1In.trans_le (vote_time_le_support_cutoff_sub₅₇b facts S s1))
        (hpostVote1.trans (vote_time_le_support_cutoff_sub₅₇b facts S s1))
        (Int.sub_add_cancel _ _) hsupport1Hor hFhist2
  obtain ⟨P2, hP2erase, i2, t2, hacc2, ht2⟩ := hadmit2
  have hP2slot : 0 < P2.slot := by
    rw [← Proofs.NamedWire.erase_slot P2, hP2erase, hP1erase,
      Proofs.NamedWire.erase_slot P]
    exact hPslot
  have ht2In : t2 < M.vote_time S.E s2 :=
    ht2.trans_le (by simpa only [s2] using
      facts.sch.support_cutoff_le_vote_time_succ S.E s1)
  have hp2max : S.E.proposer s2 ∈ Hs (max t2 lo) :=
    hHs _ _ ((max_le (le_of_lt ht2In) hpostVote2).trans
      (facts.sch.Protocol_vote_time_le_confirmation_time S.E s2)) hprop2
  have hfilteredAt : ∀ (target : Time), read + S.E.Δ ≤ target →
      M.support_cutoff S.E s2 ≤ target → target ≤ rho.horizon →
      ((Hs target).sup fun u => (W (inclusiveEventIndex rho target) u).st.core.h_max) ≤ H →
      ∀ v ∈ Hs target,
        P.erase ∈ M.get_filtered_block_tree
          (M.toHealing (W (strictEventIndex rho target) v).st.core).toFG := by
    intro target hdelay hsupport htargetHor hcap v hv
    obtain ⟨hroot, hmax⟩ :=
      Restated.fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRiseOn facts
        S Hs Xb hf hHs hHsXb hsb hfix hv hpost hdelay htargetHor hcap
    have hrootP : Block.Preceq
        (M.get_fg_root (M.toHealing (W (strictEventIndex rho target) v).st.core).toFG) P.erase := by
      unfold Record.Model.NS.toHealing at hroot
      rw [hroot]
      exact hJP
    have hFhist : ∀ j : Nat,
        j ≤ (rho.events.filter (fun e => decide (e.time < M.support_cutoff S.E s2))).length →
          Block.Preceq (W j v).st.core.F P2.erase := by
      intro j hj
      have hrootP2 : Block.Preceq
          (M.get_fg_root (M.toHealing (W (strictEventIndex rho target) v).st.core).toFG) P2.erase := by
        simpa only [hP2erase, hP1erase] using hrootP
      have hj' : j ≤ strictEventIndex rho target :=
        hj.trans (strict_filter_length_mono rho hsupport)
      exact Restated.Vocabulary.Proofs.finalized_preceq_at_prefix_of_storeBeforeRoot_preceq facts S rho
        hf.sorted (w := v) hj' (W j) (hf.onePath j).1 _
        (onePath_slice₅₇b W hf.onePath hj') hrootP2
    have hvcut : v ∈ Hs (M.support_cutoff S.E s2) := hHs _ _ hsupport hv
    have hadmitRaw : Restated.Vocabulary.Protocol.AdmittedBefore M S rho W v P2.erase
        (M.support_cutoff S.E s2) :=
      Restated.block_admittedBefore_of_accepted_after_cutoffOn facts
        S Hs Xb hf hHs hHsXb hp2max hvcut hP2slot hacc2
          (ht2In.trans_le (vote_time_le_support_cutoff_sub₅₇b facts S s2))
          (hpostVote2.trans (vote_time_le_support_cutoff_sub₅₇b facts S s2))
          (Int.sub_add_cancel _ _) hsupport2Hor hFhist
    have hadmit : Restated.Vocabulary.Protocol.AdmittedBefore M S rho W v P.erase
        (M.support_cutoff S.E s2) := by
      simpa only [hP2erase, hP1erase] using hadmitRaw
    have hprocessed : P.erase ∈ (W (strictEventIndex rho target) v).st.core.T :=
      (Restated.admittedBefore_mem_and_stamp_atOn facts S Hs Xb hf hadmit hsupport).1
    exact Restated.fixedRootGrade_mem_filtered_of_exactRootOn facts S Hs Xb hf (hHsXb _ hv) hPrun
      hprocessed hJP hPheight hroot hmax
  refine ⟨?_, ?_⟩
  · intro v hv
    exact hfilteredAt ((Restated.Vocabulary.Execution.Setup.a M S (q + 1))) hreadDelayNext hsupport2Action
      hnextHor hcapNext v hv
  · let target := M.domain S.E S.hc (q + 1) .g2
    have htargetAction : target ≤ (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) :=
      facts.gr.domain_le_a S (q + 1) .g2
    have htargetHor : target ≤ rho.horizon := htargetAction.trans hnextHor
    have hsupportTarget : M.support_cutoff S.E s2 ≤ target := by
      have hs2succ : s2 + 1 ≤ (M.opening_slot S.hc (q + 1)) := by
        have hR := S.hc.R_ge_three
        have hslots := facts.gr.opening_slot_succ_eq S.hc q
        show (M.opening_slot S.hc q) + 1 + 1 + 1 ≤ _
        rw [hslots]
        exact Nat.add_le_add_left hR _
      have h1 := facts.sch.Sts_support_cutoff_lt_view_freeze S.E s2
      have h2 := facts.sch.view_freeze_add_delta_le_proposal_time_succ S.E s2
      have h3 := facts.sch.proposal_time_mono S.E hs2succ
      have h4 := Restated.domain_g2_succ_add_delta_l57 facts S q
      simp only [target]
      linarith
    have hdelayTarget : read + S.E.Δ ≤ target :=
      hreadDelay0.trans ((facts.sch.proposal_time_mono S.E hs02).trans
        ((le_of_lt (facts.sch.proposal_time_lt_vote_time S.E s2)).trans
          ((Int.le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans
            ((le_sub_iff_add_le.mp (vote_time_le_support_cutoff_sub₅₇b facts S s2)).trans
              hsupportTarget))))
    have hloTarget : lo ≤ target :=
      (hpost.trans (Int.le_add_of_nonneg_right (le_of_lt S.E.Δ_pos))).trans hdelayTarget
    have htargetGap : target + S.E.Δ < (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) := by
      have h1 := Restated.domain_g2_succ_add_delta_l57 facts S q
      have h2 := Restated.proposal_add_delta_lt_next_action_l57 facts S q (le_refl ((M.opening_slot S.hc (q + 1))))
      have hΔ := S.E.Δ_pos
      simp only [target]
      linarith
    have hcapTarget : ((Hs target).sup fun u => (W (inclusiveEventIndex rho target) u).st.core.h_max) ≤ H :=
      hcapBefore target hloTarget htargetGap
    intro v hv
    simpa only [Restated.Vocabulary.Internal.PhaseGrades.filteredTree, target] using
      hfilteredAt target hdelayTarget hsupportTarget htargetHor hcapTarget v hv

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

/-- For every validator `v` and round `r`, every node state of `v`'s round-`r` action read computed
    from `W`'s world before `S.a r` holds, for every body `D` of its store, the stored view of `D`'s
    named derivation. -/
theorem derivedStateAgrees_actionStoreAtOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (v : V) (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r,
      Restated.Vocabulary.Internal.NamedDerivedStateAgrees M S.E S.cfg n.st := by
  intro n hn D hD
  rw [actionReadFrom_bodies₅₇b facts S _ r n hn] at hD
  have hview := Restated.Vocabulary.Proofs.NamedStoreBridge.derivedView_stateBeforeTime facts
    S rho ((Restated.Vocabulary.Execution.Setup.a M S r)) v _
    (mem_stateBeforeTime_along₅₇b hf.sorted hf.onePath _) D hD
  obtain ⟨c, -, st, hst, rfl⟩ := hn
  obtain ⟨X, hX⟩ := facts.dt.update_confirmation_with_nonempty (M.gradeContract c) S.E S.hc
    (M.ns_setClock S.E (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).st
      (Restated.Vocabulary.Execution.Setup.a M S r)).core
    (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1)
  rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [facts.dt.named_update_confirmation_with_core _ _ _ _ _ st hst X hX,
    facts.dt.update_confirmation_with_σ _ _ _ _ _ X hX, facts.hd.ModelProperties_setClock_core_σ]
  exact hview

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel.Proofs.Optimistic

end

/-! ## The checkpoint of a height window -/

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open scoped DC

/-- The round-`r` action read computed from `before` can give some node state. -/
private theorem actionReadFrom_nonempty₅₇c (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∃ n, n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r := by
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc before.st.core.toHealing
    (Restated.Vocabulary.Execution.Setup.a M S r) before.cache
  obtain ⟨st, hst⟩ := facts.dt.duties_update_confirmation_with_nonempty (M.gradeContract c) S.E S.hc
    (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r))
    (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1)
  exact ⟨_, c, hc, st, hst, rfl⟩

omit [DecidableEq V] [Fintype V] in
/-- `m >>= k` can return `b` exactly when `m` can return some `a` and `k a` can return `b`. -/
private theorem returns_bind_iff₅₇c {α β : Type} (m : DC.NDRE α) (k : α → DC.NDRE β)
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

/-- For every node state `n`, the action FG source read at `n` can return some value. -/
private theorem actionFGSource_nonempty₅₇c (facts : Record.Facts M) (S : Setup V)
    (n : M.N) : ∃ o, Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n ⇢ o := by
  obtain ⟨A2, hA2⟩ := facts.dt.grade2_block_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s)
  obtain ⟨o, ho⟩ := facts.dt.fg_source_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s) A2
  exact ⟨o, (returns_bind_iff₅₇c _ _ _).2 ⟨A2, hA2, ho⟩⟩

/-- If `v ∈ Xb`, `n` is a node state of `v`'s round-`r` action read computed from the world of `W`
    strictly before `S.a r`, and `D` is a body of `n`'s store, then `D` is a run block read through
    `Xb` along `W`. -/
theorem actionBody_runBlock_heightRegimeOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} (hv : v ∈ Xb) {r : Round} {n : M.N}
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r)
    {D : NamedBlock V} (hD : D ∈ n.st.bodies) :
    Restated.RunBlockOn M S rho W Xb D :=
  Restated.actionBody_runBlockOn facts S Hs Xb hf hv hn hD

/-- On the path `W` the bundle is read along, if the validators outside the set for the horizon
    weigh less than a third, `v ∈ Xb`, `T` is a run block read through `Xb` along `W`, `k ≠ 0`,
    every height-`k` row emitted along `W` by a signer in the set for the horizon has `some T.erase`
    as every outcome of its action's confirmation witness, and `v`'s justified height in `W n` is
    `k`, then `v`'s justified block there is `T.erase`. -/
theorem storeJustified_eq_of_honestWitnessesOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hbelow : Execution.BelowOneThird S (Hs rho.horizon))
    {v : V} (hv : v ∈ Xb) {n : Nat} {k : Height} {T : NamedBlock V}
    (hTrun : Restated.RunBlockOn M S rho W Xb T) (hk : k ≠ 0)
    (hwit : ∀ (b : NamedAttestation V) (tb : Time), b.val_index ∈ Hs rho.horizon →
      Restated.Vocabulary.Execution.NamedRun.emits M S rho W b.val_index (Object.attest b) tb →
      b.height_pair.erase.height? = some k →
      ∀ nr ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S b.round)) b.val_index)
        b.round,
      ∀ o, Restated.Vocabulary.Proofs.HealingSurface.fgConfirmationWitness M S nr ⇢ o →
        o = some T.erase)
    (hhj : (W n v).st.core.h_j = k) :
    (W n v).st.core.J = T.erase := by
  have hmajority := AlignedRoundLemmas.honestWeightMajority_of_belowOneThird hbelow
  obtain ⟨C, hC, hCJ, hhjC⟩ :=
    Restated.Vocabulary.Proofs.Bridges.storeJustificationOnChain_stateBefore facts S rho n v
      (W n) (hf.onePath n).1
  have hCrun : Restated.RunBlockOn M S rho W Xb C :=
    Restated.runBlock_of_stateBefore_memOn facts S W Xb hv hC
  have hhjC' : (M.derive_named S.E S.cfg C).h_j = k := hhjC.trans hhj
  obtain ⟨J, hJC, hJerase, Q, hQ, hwitQ⟩ :=
    Restated.Vocabulary.Proofs.NamedJustificationCertificates.justification_certificate facts S.E S.cfg C
      (by rw [hhjC']; exact hk)
  obtain ⟨i, hiQ, hiHon⟩ :=
    Protocol.HonestWeightMajority.exists_honest_member_of_quorum hmajority hQ
  obtain ⟨carrier, a, hcarrier, ha, hai, hap⟩ := hwitQ i hiQ
  have haHon : a.val_index ∈ Hs rho.horizon := by rw [hai]; exact hiHon
  have haChain : a.erase ∈ M.chain_attestations C.erase :=
    facts.ev.erase_mem_chain_attestations C carrier hcarrier a ha
  obtain ⟨b, tb, hba, hemit⟩ :=
    Restated.carriedByHonest_of_runBlockOn facts S Hs Xb hf hHs hCrun a.erase haChain
      (by rw [namedAttestation_erase_val_index]; exact haHon)
  have hbHon : b.val_index ∈ Hs rho.horizon := by
    have hvb : b.val_index = a.val_index := by
      have h := congrArg CombinedAttestation.val_index hba
      rwa [namedAttestation_erase_val_index, namedAttestation_erase_val_index] at h
    rw [hvb]
    exact haHon
  have hpairEq : b.height_pair.erase = a.height_pair.erase := by
    have h := congrArg CombinedAttestation.height_pair hba
    rwa [namedAttestation_erase_height_pair, namedAttestation_erase_height_pair] at h
  have hbrow : b.height_pair.erase.height? = some k := by
    rw [hpairEq, hap, hhjC']
    exact namedHeightPair_erase_vote_height? k J.root false
  have hva : a.erase.val_index = b.val_index :=
    (congrArg CombinedAttestation.val_index hba.symm).trans (namedAttestation_erase_val_index b)
  rw [hva] at hemit
  obtain ⟨nr, hnr⟩ := actionReadFrom_nonempty₅₇c facts S
    (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S b.round)) b.val_index) b.round
  obtain ⟨o', ho'⟩ := actionFGSource_nonempty₅₇c facts S nr
  obtain ⟨D, K, hK, hD, hsource, hDheight, hKmem, hKentry, hKheight, hKD, hshape⟩ :=
    Restated.honestHeightRow_confirmationWitnessOn facts S Hs Xb hf (hHsXb _ hbHon) hemit hbrow
      nr hnr o' ho'
  have hKT : (M.derive_named S.E S.cfg K).T_h = T.erase :=
    Option.some.inj (hwit b tb hbHon hemit hbrow nr hnr _ hK)
  have hJroot : J.root = K.erase.root := by
    have hpair : a.height_pair.erase = HeightPair.target k J.erase.root := by
      rw [hap, hhjC', namedHeightPair_erase_vote_false, Proofs.NamedWire.erase_root]
    rcases hshape with htarget | htimeout
    · have htarget' : HeightPair.target k J.erase.root =
          HeightPair.target k K.erase.root := by
        calc
          HeightPair.target k J.erase.root = a.height_pair.erase := hpair.symm
          _ = b.height_pair.erase := hpairEq.symm
          _ = HeightPair.target k K.erase.root := htarget
      exact (Proofs.NamedWire.erase_root J).symm.trans (HeightPair.target.inj htarget').2
    · rw [hpairEq, hpair] at htimeout
      cases htimeout
  have hDrun : Restated.RunBlockOn M S rho W Xb D :=
    Restated.actionBody_runBlock_heightRegimeOn facts S Hs Xb hf (hHsXb _ hbHon) hnr hD
  have hKrun : Restated.RunBlockOn M S rho W Xb K :=
    Restated.actionBody_runBlock_heightRegimeOn facts S Hs Xb hf (hHsXb _ hbHon) hnr hKmem
  obtain ⟨K', hK'D, hK'entry⟩ :=
    Proofs.NamedAncestry.erased_ancestor_lift D hKD
  have hK'run : Restated.RunBlockOn M S rho W Xb K' :=
    Restated.blockInRun_of_ancestorOn facts S rho W Xb hDrun hK'D
  have hK'eq : K' = K := by
    apply hf.rootCollisionFree.root_injective K' K hK'run hKrun K' K
      (Or.inl (Proofs.NamedAncestry.named_self K'))
      (Or.inr (Proofs.NamedAncestry.named_self K))
    rw [← Proofs.NamedWire.erase_root K', hK'entry, Proofs.NamedWire.erase_root]
  have hKtarget : (M.derive_named S.E S.cfg K).T_h = K.erase := by
    have hplateau : (M.derive_named S.E S.cfg K).T_h =
        (M.derive_named S.E S.cfg D).T_h := by
      rw [← hK'eq]
      exact facts.cs.entry_eq_on_plateau S.E S.cfg hK'D
        ((hK'eq ▸ hKheight).trans hDheight.symm)
    exact hplateau.trans hKentry.symm
  have hTroot : T.root = K.root := by
    calc
      T.root = T.erase.root := (Proofs.NamedWire.erase_root T).symm
      _ = (M.derive_named S.E S.cfg K).T_h.root :=
        (congrArg Block.root hKT).symm
      _ = K.erase.root := congrArg Block.root hKtarget
      _ = K.root := Proofs.NamedWire.erase_root K
  have hJroot' : J.root = K.root := hJroot.trans (Proofs.NamedWire.erase_root K)
  have hJrun : Restated.RunBlockOn M S rho W Xb J :=
    Restated.blockInRun_of_ancestorOn facts S rho W Xb hCrun hJC
  have hJK : J = T := by
    apply hf.rootCollisionFree.root_injective J T hJrun hTrun J T
      (Or.inl (Proofs.NamedAncestry.named_self J))
      (Or.inr (Proofs.NamedAncestry.named_self T))
    exact hJroot'.trans hTroot.symm
  rw [← hCJ, ← hJerase, hJK]

/-- On the path `W` the bundle is read along, if the validators outside the set for the horizon
    weigh less than a third, `v ∈ Xb`, `T` is a run block read through `Xb` along `W` of height
    `k ≥ 2`, every height-`k` row emitted along `W` by a signer in the set for the horizon has
    `some T.erase` as every outcome of its action's confirmation witness, and `v`'s `h_max` in `W n`
    is at most `k + 1`, then `v`'s finalized block there is an ancestor of `T.erase`. -/
theorem storeF_preceq_checkpoint_of_windowOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hbelow : Execution.BelowOneThird S (Hs rho.horizon))
    {v : V} (hv : v ∈ Xb) {n : Nat} {k : Height} {T : NamedBlock V}
    (hTrun : Restated.RunBlockOn M S rho W Xb T)
    (hTh : (M.derive_named S.E S.cfg T).h = k) (hk : 2 ≤ k)
    (hwit : ∀ (b : NamedAttestation V) (tb : Time), b.val_index ∈ Hs rho.horizon →
      Restated.Vocabulary.Execution.NamedRun.emits M S rho W b.val_index (Object.attest b) tb →
      b.height_pair.erase.height? = some k →
      ∀ nr ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S b.round)) b.val_index)
        b.round,
      ∀ o, Restated.Vocabulary.Proofs.HealingSurface.fgConfirmationWitness M S nr ⇢ o →
        o = some T.erase)
    (hwin : (W n v).st.core.h_max ≤ k + 1) :
    Block.Preceq (W n v).st.core.F T.erase := by
  have hWn := (hf.onePath n).1
  have hsb : Restated.SlashableBoundOn M S rho W Xb := hf.slashableBound
  obtain ⟨C, hC, hF, hFheight⟩ :=
    Restated.Vocabulary.Proofs.Bridges.storeFinalizationOnChain_stateBefore facts S rho n v (W n) hWn
  have hCrun : Restated.RunBlockOn M S rho W Xb C :=
    Restated.runBlock_of_stateBefore_memOn facts S W Xb hv hC
  have hFle : (M.derive_named S.E S.cfg C).h_F ≤ k :=
    Nat.le_of_lt_succ (hFheight.trans_le hwin)
  rcases lt_or_eq_of_le hFle with hFlt | hFeq
  · have hpre : Block.Preceq (M.derive_named S.E S.cfg C).F T.erase :=
      Restated.finalized_preceq_of_height_ltOn facts S rho W Xb T C hsb
        hf.rootCollisionFree hTrun hCrun
        (by rw [hTh]; exact hFlt)
    rw [hF] at hpre
    exact hpre
  · have hFJ : Block.Preceq (W n v).st.core.F (W n v).st.core.J :=
      Restated.Vocabulary.Proofs.NamedStoreBridge.finalized_preceq_justified_stateBefore facts S rho n v
        (W n) hWn
    obtain ⟨C', hC', hJ, hhj'⟩ :=
      Restated.Vocabulary.Proofs.NamedJustificationCarrier.justification_carrier_stateBefore facts S rho n v
        (W n) hWn
    have hC'run : Restated.RunBlockOn M S rho W Xb C' :=
      Restated.runBlock_of_stateBefore_memOn facts S W Xb hv hC'
    have hFnonzero : (M.derive_named S.E S.cfg C).h_F ≠ 0 := by
      intro hzero
      exact (Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hk))
        (hFeq.symm.trans hzero)
    obtain ⟨Fn, hFnC, hFnErase, hFnHeight⟩ :=
      (facts.csAdded.finalized_ancestor_height S.E S.cfg C).resolve_left hFnonzero
    have hFnState : Fn.erase = (W n v).st.core.F := hFnErase.trans hF
    have hFnrun : Restated.RunBlockOn M S rho W Xb Fn :=
      Restated.blockInRun_of_ancestorOn facts S rho W Xb hCrun hFnC
    rcases facts.cs.justified_ancestor_height S.E S.cfg C' with
      hJzero | ⟨Jn, hJnC', hJnErase, hJnHeight⟩
    · exfalso
      have hJgen : (W n v).st.core.J = Block.genesis := by
        rw [← hJ]
        exact facts.cs.justified_zero_is_genesis S.E S.cfg C' hJzero
      have hFgen : (W n v).st.core.F = Block.genesis :=
        Block.preceq_antisymm (by rw [hJgen] at hFJ; exact preceq_eq_true_iff_Preceq.mpr hFJ)
          (Protocol.preceq_genesis _)
      have hFnGen : Fn = NamedBlock.genesis :=
        (priv% Proofs.Vocabulary.Objects.HeightRegimeStep
          DecoupledConsensusModel.Proofs.HealingSurface.namedGenesis_of_erase_genesis)
          (hFnState.trans hFgen)
      have hFnHeight' : (M.derive_named S.E S.cfg Fn).h = k :=
        hFnHeight.trans hFeq
      rw [hFnGen, facts.cs.derive_named_genesis_h] at hFnHeight'
      exact absurd hFnHeight'
        (Nat.ne_of_lt (lt_of_lt_of_le (by decide : 1 < 2) hk))
    have hJnState : Jn.erase = (W n v).st.core.J := hJnErase.trans hJ
    have hJnrun : Restated.RunBlockOn M S rho W Xb Jn :=
      Restated.blockInRun_of_ancestorOn facts S rho W Xb hC'run hJnC'
    have hFJ' : Block.Preceq (W n v).st.core.F Jn.erase := by
      rw [hJnState]
      exact hFJ
    obtain ⟨F'n, hF'nJn, hF'nErase⟩ :=
      Proofs.NamedAncestry.erased_ancestor_lift Jn hFJ'
    have hF'nrun : Restated.RunBlockOn M S rho W Xb F'n :=
      Restated.blockInRun_of_ancestorOn facts S rho W Xb hJnrun hF'nJn
    have hF'nFn : F'n = Fn := by
      apply hf.rootCollisionFree.root_injective F'n Fn hF'nrun hFnrun F'n Fn
        (Or.inl (Proofs.NamedAncestry.named_self F'n))
        (Or.inr (Proofs.NamedAncestry.named_self Fn))
      rw [← Proofs.NamedWire.erase_root F'n, hF'nErase, hFnState.symm,
        Proofs.NamedWire.erase_root]
    have hFnHeight' : (M.derive_named S.E S.cfg Fn).h = k := hFnHeight.trans hFeq
    have hJnHeight' : (M.derive_named S.E S.cfg Jn).h = (W n v).st.core.h_j :=
      hJnHeight.trans hhj'
    have hjge : k ≤ (W n v).st.core.h_j := by
      rw [← hFnHeight', ← hJnHeight']
      rw [← hF'nFn]
      exact facts.cs.derive_height_mono S.E S.cfg hF'nJn
    have hjlt : (W n v).st.core.h_j < (W n v).st.core.h_max :=
      Restated.Vocabulary.Proofs.NamedJustificationBound.justificationBelowMax_stateBefore facts S rho n v
        (W n) hWn
    have hjeq : (W n v).st.core.h_j = k :=
      Nat.le_antisymm (Nat.le_of_lt_succ (hjlt.trans_le hwin)) hjge
    have hJT := Restated.storeJustified_eq_of_honestWitnessesOn facts S Hs Xb hf hHs hHsXb hbelow hv
      hTrun (Nat.ne_of_gt (lt_of_lt_of_le (by decide) hk)) hwit hjeq
    rw [hJT] at hFJ
    exact hFJ

/-- If the largest `h_max` over `X` in the worlds of `W` before `first'` is at most `blocked + 2`,
    then for `v ∈ X` and `n ≤ first' − 1`, `v`'s `h_max` in `W n` is at most `blocked + 2`. -/
theorem window_of_nextCrossingOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} {W : Nat → V → M.N} (X : Finset V) {blocked : Height}
    {first' : Nat}
    (hfirst' : Restated.HeightWindowAtOn M S rho W X (blocked + 1 + 1) first')
    {v : V} (hv : v ∈ X) {n : Nat} (hn : n ≤ first' - 1) :
    (W n v).st.core.h_max ≤ blocked + 1 + 1 :=
  (Finset.le_sup (f := fun u => (W n u).st.h_max) hv).trans
    (hfirst'.before n (Nat.lt_of_le_pred hfirst'.positive hn))

omit [DecidableEq V] [Fintype V] in
/-- If `f <$> m` can return `b`, then `m` can return some `a` with `f a = b`. -/
private theorem returns_map_elim₅₇c {α β : Type} (f : α → β) (m : DC.NDRE α) (b : β)
    (h : (f <$> m) ⇢ b) : ∃ a, m ⇢ a ∧ f a = b := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image] at h
  obtain ⟨e, he, hb⟩ := h
  cases e with
  | ok a => exact ⟨a, he, by simpa [Except.map] using hb⟩
  | error err => simp [Except.map] at hb

omit [DecidableEq V] [Fintype V] in
/-- If `m` can return `a`, then `f <$> m` can return `f a`. -/
private theorem returns_map_intro₅₇c {α β : Type} (f : α → β) (m : DC.NDRE α) (a : α)
    (h : m ⇢ a) : (f <$> m) ⇢ f a := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image]
  exact ⟨_, h, rfl⟩

/-- Every node state the round-`r` action read computed from `before` can give holds `before`'s
    bodies. -/
private theorem actionReadFrom_bodies₅₇c (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      n.st.bodies = before.st.bodies := by
  rintro _ ⟨c, -, st, hst, rfl⟩
  rw [facts.nd.mkNode_st, facts.nd.store_with_cache_bodies,
    facts.dt.named_update_confirmation_with_bodies _ _ _ _ _ st hst,
    facts.hd.ModelProperties_setClock_bodies]

/-- Every action instant is at or after instant `0`. -/
private theorem a_nonneg₅₇c (facts : Record.Facts M) (S : Setup V) (r : Round) :
    0 ≤ Restated.Vocabulary.Execution.Setup.a M S r := by
  show 0 ≤ M.a S.hc S.E.Δ r
  rw [facts.sch.a_eq_confirmation_time]
  exact le_trans (facts.sch.Optimistic_proposal_time_nonneg S.E _)
    (facts.sch.proposal_time_le_confirmation_time S.E _)

/-- The number of events strictly before the seed attestation's action instant is less than `stop`. -/
private theorem actionPrefix_lt₅₇c (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} {Hs : Int → Finset V} {Xb : Finset V} {lo : Int}
    {W : Nat → V → M.N} {Wt : Time → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {start stop : Nat} {blocked : Height} {i : Nat}
    {a : NamedAttestation V} {ta : Time} {Cfg : NamedBlock V} {T : Block V}
    (hseed : Restated.PrefixFGSelectorConeAtOn M S rho W Wt Hs Xb start stop blocked i a ta Cfg T) :
    strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round) < stop := by
  have hle : strictEventIndex rho ta ≤ i := by
    by_contra hnot
    have hlt : i < strictEventIndex rho ta := Nat.lt_of_not_ge hnot
    unfold strictEventIndex at hlt
    have hmem : Record.Event.tick a.val_index ta ∈
        rho.events.filter (fun e => decide (e.time < ta)) := by
      rw [Restated.filter_eq_takeOn facts S Hs Xb hf _ (Restated.downward_lt ta)]
      exact List.mem_of_getElem? (by
        rw [List.getElem?_take_of_lt hlt]
        exact hseed.exactTick)
    have himpossible := (List.mem_filter.mp hmem).2
    simp only [decide_eq_true_eq, Record.Event.time] at himpossible
    exact lt_irrefl ta himpossible
  rw [hseed.actionTime_eq] at hle
  exact hle.trans_lt hseed.indexLtStop

/-- On the path `W` the bundle is read along, under the committee majority and `BelowOneThirdOn`,
    from the seed cone at height `blocked + 1` with its window and the frame at `blocked`: if
    `a.round` is minimal among height-`(blocked + 1)` rows, `1 ≤ blocked`, `first'` bounds the
    window at `blocked + 2`, `Tnext` is a run block of height `blocked + 1` erasing to `Cfg`'s
    entry, same-round rows of signers in the set for the horizon have `some Tnext.erase` as every
    outcome of their witness, and every block a later round's FG confirmation witness can return is
    compatible with `Tnext.erase`, then the named frame holds along `W` at height `blocked + 1` up
    to `first' − 1`, with `Tnext` as the previous checkpoint and `a.round + 1` as the round bound. -/
theorem PrefixFGSelectorConeAtOn.heightRegimeFrame_succ_of_frameN (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} (Hs : Int → Finset V) (Xb X : Finset V) {lo : Int}
    {W : Nat → V → M.N} {Wt : Time → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hX : ∀ t : Int, 0 ≤ t → Hs t ⊆ X) (hXXb : X ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hbelow : BelowOneThirdOn S rho Hs)
    {start first : Nat} {blocked : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg : NamedBlock V} {T0 : Block V}
    (hseed : Restated.PrefixFGSelectorConeAtOn M S rho W Wt Hs Xb start first blocked i a ta Cfg T0)
    (hfirst : Restated.HeightWindowAtOn M S rho W X (blocked + 1) first)
    {Tprev : NamedBlock V} {c0 : Round}
    (hframe : Restated.NamedHeightRegimeFrameOn M S rho W Wt Hs X Xb blocked (first - 1) Tprev c0)
    (hc0 : c0 ≤ a.round)
    (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho a.round)
    (hpostPrev : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (a.round - 1)))
    (hminimal : ∀ (b : NamedAttestation V) (tb : Time),
      b.val_index ∈ Hs tb →
      Restated.Vocabulary.Execution.NamedRun.emits M S rho W b.val_index (Object.attest b) tb →
      b.height_pair.erase.height? = some (blocked + 1) → a.round ≤ b.round)
    (hblocked : 1 ≤ blocked)
    {first' : Nat} (hfirst' : Restated.HeightWindowAtOn M S rho W X (blocked + 1 + 1) first')
    {Tnext : NamedBlock V}
    (hTnextCfg : NamedBlock.Preceq Tnext Cfg)
    (hTnextRun : Restated.RunBlockOn M S rho W Xb Tnext)
    (hTnextErase : Tnext.erase =
      (M.derive_named S.E S.cfg Cfg).T_h)
    (hTnextHeight :
      (M.derive_named S.E S.cfg Tnext).h = blocked + 1)
    (hsameRound : ∀ {b : NamedAttestation V} {tb : Time},
      b.val_index ∈ Hs rho.horizon →
      Restated.Vocabulary.Execution.NamedRun.emits M S rho W b.val_index (Object.attest b) tb →
      b.height_pair.erase.height? = some (blocked + 1) →
      a.round = b.round →
      ∀ nr ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S b.round)) b.val_index)
        b.round,
      ∀ o, Restated.Vocabulary.Proofs.HealingSurface.fgConfirmationWitness M S nr ⇢ o →
        o = some Tnext.erase)
    (hcompatLater : ∀ {r : Round}, a.round + 1 ≤ r →
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ rho.horizon →
      ∀ {w : V}, w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)) →
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) w) r,
      ∀ {B : Block V},
      Restated.Vocabulary.Proofs.HealingSurface.fgConfirmationWitness M S n ⇢ some B →
      Block.compatible B Tnext.erase = true) :
    Restated.NamedHeightRegimeFrameOn M S rho W (fun t => W (strictEventIndex rho t)) Hs X Xb
      (blocked + 1) (first' - 1) Tnext (a.round + 1) := by
  have hbelowHor : Execution.BelowOneThird S (Hs rho.horizon) := hbelow _ le_rfl
  have hwit : ∀ (b : NamedAttestation V) (tb : Time),
      b.val_index ∈ Hs rho.horizon →
      Restated.Vocabulary.Execution.NamedRun.emits M S rho W b.val_index (Object.attest b) tb →
      b.height_pair.erase.height? = some (blocked + 1) →
      ∀ nr ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S b.round)) b.val_index)
        b.round,
      ∀ o, Restated.Vocabulary.Proofs.HealingSurface.fgConfirmationWitness M S nr ⇢ o →
        o = some Tnext.erase := by
    intro b tb hb hemit hrow nr hnr o ho
    have htbHor : tb ≤ rho.horizon := by
      obtain ⟨k, hk, _⟩ := hemit
      have hin := (hf.in_horizon
        (Record.Event.tick b.val_index tb) (List.mem_of_getElem? hk)).2
      simpa only [Record.Event.time, Record.Event.time] using hin
    have hbtb : b.val_index ∈ Hs tb := hHs _ _ htbHor hb
    rcases eq_or_lt_of_le (hminimal b tb hbtb hemit hrow) with heq | hlt
    · exact hsameRound hb hemit hrow heq nr hnr o ho
    · unfold Restated.Vocabulary.Proofs.HealingSurface.fgConfirmationWitness at ho
      obtain ⟨o', ho', rfl⟩ := returns_map_elim₅₇c _ _ _ ho
      obtain ⟨D, K, hW, hDmem, hsource, hDheight, hKmem, hKerase, hKheight, hKD, _hshape⟩ :=
        Restated.honestHeightRow_confirmationWitnessOn facts S Hs Xb hf (hHsXb _ hb) hemit hrow
          nr hnr o' ho'
      have htime : tb = (Restated.Vocabulary.Execution.Setup.a M S b.round) :=
        (Restated.Vocabulary.Proofs.Optimistic.emits_attest_shape facts S W hf.onePath hemit).2
      have hhor : (Restated.Vocabulary.Execution.Setup.a M S b.round) ≤ rho.horizon := by
        rw [← htime]
        exact htbHor
      have hKfixed : (M.derive_named S.E S.cfg K).T_h = K.erase := by
        have hDrun := Restated.actionBody_runBlock_heightRegimeOn facts S Hs Xb hf (hHsXb _ hb) hnr hDmem
        have hKrun := Restated.actionBody_runBlock_heightRegimeOn facts S Hs Xb hf (hHsXb _ hb) hnr hKmem
        have hKDnamed := Restated.namedPreceq_of_runBlock_erase_preceqOn facts Hs Xb hf hKrun hDrun hKD
        exact (facts.cs.entry_eq_on_plateau S.E S.cfg hKDnamed
          (hKheight.trans hDheight.symm)).trans hKerase.symm
      have hW' : Restated.Vocabulary.Proofs.HealingSurface.fgConfirmationWitness M S nr ⇢
          some (M.derive_named S.E S.cfg D).T_h := by
        rw [hKfixed, hKerase] at hW
        exact hW
      have hbAct : b.val_index ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S b.round)) := by
        rw [← htime]
        exact hbtb
      have hcompat := hcompatLater hlt hhor hbAct nr hnr hW'
      have hDT := (hseed.laterFGWitness_eq_or_extends_checkpoint_of_frameN facts Hs Xb X
        hf hcom hbelow hfirst hframe hc0 ready hpostPrev hminimal
        hTnextCfg hTnextRun hTnextErase hTnextHeight hlt hhor (hHsXb _ hb) hnr hDmem
        hW' hcompat).1 hDheight
      rw [hsource, Option.map_some,
        Restated.derivedStateAgrees_actionStoreAtOn facts S Hs Xb hf b.val_index b.round nr hnr D hDmem,
        hDT]
  have hk2 : 2 ≤ blocked + 1 := Nat.succ_le_succ hblocked
  have hFT : ∀ v ∈ X, ∀ n : Nat, n ≤ first' - 1 →
      Block.Preceq (W n v).st.core.F Tnext.erase :=
    fun v hv n hn => Restated.storeF_preceq_checkpoint_of_windowOn facts
      S Hs Xb hf hHs hHsXb hbelowHor (hXXb hv) hTnextRun hTnextHeight hk2 hwit
        (Restated.window_of_nextCrossingOn facts S X hfirst' hv hn)
  refine {
    floor := ?_
    prevRun := hTnextRun
    prevHeight := hTnextHeight.le
    rootBelow := ?_
    sourceAbove := ?_ }
  · intro v hv n hn X' _ _ hTX
    exact preceq_trans_Preceq (hFT v hv n hn) (Proofs.NamedWire.erase_preceq hTX)
  · intro v hv n hn Q hQ hQh hTQ
    have hWn := (hf.onePath n).1
    have hQle : blocked + 1 + 1 ≤ (W n v).st.core.h_max := by
      have hbound := Restated.Vocabulary.Proofs.NamedStoreBridge.heights_le_hMax_stateBefore facts
        S rho n v (W n) hWn Q hQ
      rw [hQh] at hbound
      exact hbound
    have hmax : (W n v).st.core.h_max = blocked + 1 + 1 :=
      Nat.le_antisymm (Restated.window_of_nextCrossingOn facts S X hfirst' hv hn) hQle
    by_cases hgate : (W n v).st.core.h_max = (W n v).st.core.h_j + 1
    · have hroot : M.get_fg_root (M.toHealing (W n v).st.core).toFG = (W n v).st.core.J :=
        facts.fc.get_fg_root_toHealing_of_eq _ hgate
      have hhj : (W n v).st.core.h_j = blocked + 1 := by
        rw [hmax] at hgate
        exact (Nat.add_right_cancel hgate).symm
      rw [hroot, Restated.storeJustified_eq_of_honestWitnessesOn facts S Hs Xb hf hHs hHsXb hbelowHor
        (hXXb hv) hTnextRun (Nat.ne_of_gt (lt_of_lt_of_le (by decide) hk2)) hwit hhj]
      exact Proofs.NamedWire.erase_preceq hTQ
    · have hroot : M.get_fg_root (M.toHealing (W n v).st.core).toFG = (W n v).st.core.F :=
        facts.fc.get_fg_root_toHealing_of_ne _ hgate
      rw [hroot]
      exact preceq_trans_Preceq (hFT v hv n hn) (Proofs.NamedWire.erase_preceq hTQ)
  · intro p r hpAct hr hhor n hn B hBmem hsource hBh
    have hn' : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) p) r := hn
    have hp : p ∈ X := hX _ (a_nonneg₅₇c facts S r) hpAct
    have hrgt : a.round + 1 ≤ r := by
      by_contra hnot
      have hle : r ≤ a.round := Nat.le_of_lt_succ (Nat.lt_of_not_le hnot)
      have hBpre : B ∈
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) p).st.bodies := by
        rw [← actionReadFrom_bodies₅₇c facts S _ r n hn']
        exact hBmem
      have hmaxB : blocked + 1 + 1 ≤
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) p).st.core.h_max := by
        have hbound := Restated.Vocabulary.Proofs.NamedStoreBridge.heights_le_hMax_stateBefore facts
          S rho (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) p _
          (hf.onePath _).1 B hBpre
        rw [hBh] at hbound
        exact hbound
      have hfrontier :
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) p).st.core.h_max ≤
            blocked + 1 :=
        (Finset.le_sup (f := fun u =>
            (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) u).st.h_max) hp).trans
          (hfirst.before _
            ((Restated.strict_filter_length_mono rho
              (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hle)).trans_lt
              (actionPrefix_lt₅₇c facts hf hseed)))
      exact Nat.not_succ_le_self (blocked + 1) (hmaxB.trans hfrontier)
    have hW : Restated.Vocabulary.Proofs.HealingSurface.fgConfirmationWitness M S n ⇢
        some (M.derive_named S.E S.cfg B).T_h := by
      have h := returns_map_intro₅₇c
        (fun o : Option (Block V) => o.map (fun Cfg => (n.st.core.σ Cfg).T_h)) _ _ hsource
      rw [Option.map_some,
        Restated.derivedStateAgrees_actionStoreAtOn facts S Hs Xb hf p r n hn' B hBmem] at h
      exact h
    have hcompat := hcompatLater hrgt hhor hpAct n hn' hW
    have htarget :=
      (hseed.laterFGWitness_eq_or_extends_checkpoint_of_frameN facts Hs Xb X
        hf hcom hbelow hfirst hframe hc0 ready hpostPrev hminimal
        hTnextCfg hTnextRun hTnextErase hTnextHeight hrgt hhor (hXXb hp) hn' hBmem
        hW hcompat).2 (by rw [hBh]; exact Nat.le_succ (blocked + 1))
    obtain ⟨K, _hKmem, hKerase, _hKheight, hKB, hKrun⟩ :=
      Restated.action_named_checkpointOn facts S Hs Xb hf (hXXb hp) hn' hBmem
    rw [← hKerase] at htarget
    have hTnextK := Restated.namedPreceq_of_runBlock_erase_preceqOn facts Hs Xb hf hTnextRun hKrun htarget
    have hBrun := Restated.actionBody_runBlock_heightRegimeOn facts S Hs Xb hf (hXXb hp) hn' hBmem
    apply Restated.namedPreceq_of_runBlock_erase_preceqOn facts Hs Xb hf hTnextRun hBrun
    exact preceq_trans_Preceq (Proofs.NamedWire.erase_preceq hTnextK)
      (Proofs.NamedWire.erase_preceq hKB)

end

end DecoupledConsensusModel.Sts.Restated
