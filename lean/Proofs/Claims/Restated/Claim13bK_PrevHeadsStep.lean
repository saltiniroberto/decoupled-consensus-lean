import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bInvariantActive
import Proofs.Claims.Restated.Claim13bK_ConeAnchor
import Proofs.Claims.Restated.Claim13bK_ConeChain
import Proofs.Claims.Restated.Claim13bK_ConeSlots
import Proofs.Claims.Restated.Claim13bK_ConfirmedOld
import Proofs.Claims.Restated.Claim13bK_FgJustified
import Proofs.Claims.Restated.Claim13bK_FinBeforeTick
import Proofs.Claims.Restated.Claim13bK_Frame
import Proofs.Claims.Restated.Claim13bK_FrameNew
import Proofs.Claims.Restated.Claim13bK_FreshAttestersW
import Proofs.Claims.Restated.Claim13bK_GradeLate
import Proofs.Claims.Restated.Claim13bK_GradeOld
import Proofs.Claims.Restated.Claim13bK_GradeOldHeads
import Proofs.Claims.Restated.Claim13bK_HeadsNewAnchor
import Proofs.Claims.Restated.Claim13bK_HolderMargins
import Proofs.Claims.Restated.Claim13bKit
import Proofs.Claims.Restated.Claim13bPhaseSleepiness
import Proofs.Claims.Restated.Claim13bStepActionF
import Proofs.Claims.Restated.Claim13bStepAssembly
import Proofs.Claims.Restated.Claim13bStepCone
import Proofs.Claims.Restated.Claim13bStepConeIter
import Proofs.Claims.Restated.Claim13bStepFin
import Proofs.Claims.Restated.Claim13bStepGrade
import Proofs.Claims.Restated.Claim13bStepKitConfirm
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bStepKitTick
import Proofs.Claims.Restated.Claim13bStepPairwise
import Proofs.Claims.Restated.Claim13bStepRoots
import Proofs.Claims.Restated.Claim13bStepSG
import Proofs.Claims.Restated.Claim13bStepSGMove
import Proofs.Claims.Restated.Claim13bW_Schedule
import Proofs.Claims.Restated.Claim13beRoute3_2
import Proofs.Claims.Restated.CommonViewOfFinalizedDescendantsFacts
import Proofs.Claims.Restated.Projection
import Proofs.Claims.Restated.Vocabulary_Execution_HealthyLocalFacts
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActive
import Model.Conditions.Claim13bInvariantActiveJoint
import Model.Conditions.Claim13bInvariantActiveTop
import Model.Conditions.Claim13bK_ConeAnchor
import Model.Conditions.Claim13bK_ConeSlots
import Model.Conditions.Claim13bK_FgJustified
import Model.Conditions.Claim13bK_FinBeforeTick
import Model.Conditions.Claim13bK_FreshAttestersW
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13bStepAssembly
import Model.Conditions.Claim13bStepCone
import Model.Conditions.Claim13bStepConeIter
import Model.Conditions.Claim13bStepKitTick
import Model.Conditions.Claim13bStepSG
import Model.Conditions.Claim13beRoute3_5
import Model.Conditions.Claim13beRoute3_7
import Model.Conditions.CommonViewOfFinalizedDescendantsFacts
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_Grades_Main
import Model.Conditions.Vocabulary_Statements_Instantiation_RoundTimes
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bK_PrevHeadsStep
import Proofs.Claims.Restated.WakeWindow
import Proofs.Claims.Restated.Claim13bK_ConeAnchorRecv
import Proofs.Claims.Restated.Claim13bK_GradeLateRecv
import Proofs.Claims.Restated.Claim13bK_PrevHeadsStepRecv
import Proofs.Claims.Restated.Claim13bInvariantGrade1RuleFacts

/-!
# Round SG blocks and the heads of the next opening slot

After the phase, every round-`r` SG block of an honest active attester of round `r` is an ancestor
of every head voted at round `(r + 1)`'s opening slot, with the facts on heads, grades and anchors
this uses, stated over a model `M : Record.Model V` and its facts `facts : Record.Facts M`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

/-! ## Helpers -/

section
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

private theorem three_le_of_sum_nat_s2 (a b c d e f : Nat) (h : a + b + c + d + 2 + e ≤ f)
    (he : 1 ≤ e) : a + 1 + 1 + 1 ≤ f := by omega

/-- The successors of the slots of one round are the round's later slots and the next round's
    opening slot. -/
private theorem slot_succ_cases_s2 (a R s : Nat) (h0 : a ≤ s) (h1 : s ≤ a + R - 1)
    (hR : 3 ≤ R) : (1 ≤ s + 1 - a ∧ s + 1 - a < R ∧ s + 1 = a + (s + 1 - a)) ∨ s + 1 = a + R := by
  omega

private theorem pred_facts_s2 (a R b : Nat) (hb : b = a + R) (hR : 3 ≤ R) :
    b - 1 + 1 = b ∧ a + 1 ≤ b - 1 := by omega

private theorem succ_le_of_le_pred_s2 (s b a : Nat) (h : s ≤ b - 1) (ha : a + 1 ≤ b - 1) :
    s + 1 ≤ b := by omega

private theorem pos_of_sum_nat_s2 (a b c d e f : Nat) (h : a + b + c + d + 2 + e ≤ f) :
    0 < f := by omega

private theorem pos_of_succ_le_s2 (a b : Nat) (h : a + 1 ≤ b) : 0 < b := by omega

/-- A slot's confirmation instant is five delays after its vote instant. -/
private theorem vote_time_add_five_delta_phs (facts : Record.Facts M) (E : Env V) (s : Slot) :
    M.vote_time E s + 5 * E.Δ = M.confirmation_time E s := by
  have h1 := facts.sch.slotStart_add_delta_eq_vote_time E s
  have h2 := facts.sch.slotStart_add_six_delta_eq_confirmation_time E s
  linarith

/-- A round opens at the start of its opening slot. -/
private theorem opening_eq_slotStart_phs (facts : Record.Facts M) (S : Setup V) (r : Round) :
    M.opening S.E S.hc r = slotStart S.E.Δ (M.opening_slot S.hc r) :=
  (facts.gr.opening_eq_proposal_time S.E S.hc r).trans
    (facts.sch.Γ_0_eq_proposal_time S.hc S.E r).symm

/-- A round's action instant is six delays after its opening. -/
private theorem action_eq_opening_add_phs (facts : Record.Facts M) (S : Setup V) (r : Round) :
    Restated.Vocabulary.Execution.Setup.a M S r = M.opening S.E S.hc r + 6 * S.E.Δ := by
  have h1 : Restated.Vocabulary.Execution.Setup.a M S r
      = M.confirmation_time S.E (M.opening_slot S.hc r) :=
    facts.sch.a_eq_confirmation_time S.hc S.E r
  have h2 := facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E (M.opening_slot S.hc r)
  rw [h1, opening_eq_slotStart_phs facts S r]
  linarith

/-- Round zero opens at time zero. -/
private theorem opening_zero_phs (facts : Record.Facts M) (S : Setup V) :
    M.opening S.E S.hc 0 = 0 := by
  rw [opening_eq_slotStart_phs facts S 0, facts.gr.opening_slot_zero_mk S.hc]
  simp [slotStart]

/-- A round opens at or before its action instant. -/
private theorem opening_le_action_phs (facts : Record.Facts M) (S : Setup V) (r : Round) :
    M.opening S.E S.hc r ≤ Restated.Vocabulary.Execution.Setup.a M S r := by
  have h := action_eq_opening_add_phs facts S r
  have hd := S.E.Δ_pos
  linarith

/-- The action instant of round `ρ` is at or before the opening of round `ρ + 1`. -/
private theorem action_le_opening_succ_phs (facts : Record.Facts M) (S : Setup V) (ρ : Round) :
    (Restated.Vocabulary.Execution.Setup.a M S ρ) ≤ M.opening S.E S.hc (ρ + 1) := by
  have h1 := facts.gr.action_delta_le_early S S.hc.R_ge_three (Nat.lt_succ_self ρ)
  have h2 := facts.gr.early_g2_le_opening S (ρ + 1)
  have hd := S.E.Δ_pos
  show M.a S.hc S.E.Δ _ ≤ _
  linarith

/-- For every slot `s`, `slotStart s + 2Δ ≤ support_cutoff s`. -/
private theorem slotStart_add_two_delta_le_support_cutoff_phs (facts : Record.Facts M)
    (S : Setup V) (s : Slot) :
    slotStart S.E.Δ s + 2 * S.E.Δ ≤ M.support_cutoff S.E s := by
  have hd := S.E.Δ_pos
  have hvt := facts.sch.slotStart_add_delta_eq_vote_time S.E s
  have hp0 : slotStart S.E.Δ s ≤ M.proposal_time S.E s :=
    slotStart_le_of_le_slotOf S (facts.sch.Sts_proposal_time_nonneg S s)
      (le_of_eq (facts.sch.slotOf_proposal_time S.E s).symm)
  have hpv := facts.sch.proposal_time_lt_vote_time S.E s
  have hc0 : slotStart S.E.Δ s ≤ M.support_cutoff S.E s :=
    slotStart_le_of_le_slotOf S (le_of_lt (facts.sch.support_cutoff_pos S s))
      (le_of_eq (facts.sch.slotOf_support_cutoff S.E s).symm)
  have hcp := facts.sch.support_cutoff_ne_proposal_time S.E s
  have hcv := facts.sch.support_cutoff_ne_vote_time S.E s
  obtain ⟨a, ha⟩ := Int.dvd_of_emod_eq_zero (slotStart_emod_delta S s)
  obtain ⟨b, hb⟩ := Int.dvd_of_emod_eq_zero (facts.sch.proposal_time_emod_delta_inclX S.E s)
  obtain ⟨c, hc⟩ := Int.dvd_of_emod_eq_zero (facts.sch.support_cutoff_emod_delta S s)
  rw [ha, hb] at hp0
  rw [← hvt, ha, hb] at hpv
  rw [ha, hc] at hc0
  rw [hc, hb] at hcp
  rw [← hvt, hc, ha] at hcv
  rw [ha, hc]
  have hab : a ≤ b := le_of_mul_le_mul_left hp0 hd
  have hba : b < a + 1 :=
    lt_of_mul_lt_mul_left (by rw [mul_add, mul_one]; exact hpv) (le_of_lt hd)
  have hbeq : b = a := by omega
  subst hbeq
  have hac : b ≤ c := le_of_mul_le_mul_left hc0 hd
  have hc1 : c ≠ b := fun h => hcp (by rw [h])
  have hc2 : c ≠ b + 1 := fun h => hcv (by rw [h, mul_add, mul_one])
  have hc3 : b + 2 ≤ c := by omega
  nlinarith

/-- For every slot `s`, `support_cutoff s + Δ ≤ view_freeze s`. -/
private theorem support_cutoff_add_delta_le_view_freeze_phs (facts : Record.Facts M)
    (S : Setup V) (s : Slot) :
    M.support_cutoff S.E s + S.E.Δ ≤ M.view_freeze S.E s := by
  have hd := S.E.Δ_pos
  obtain ⟨k, hk⟩ := (facts.sch.publicTime_iff S (M.view_freeze S.E s)).mpr
    ⟨s, Or.inr (Or.inr (Or.inr rfl))⟩
  obtain ⟨c, hc⟩ := Int.dvd_of_emod_eq_zero (facts.sch.support_cutoff_emod_delta S s)
  have hlt := facts.sch.Sts_support_cutoff_lt_view_freeze S.E s
  rw [hk, hc] at hlt
  rw [hk, hc]
  have hck : c < (k : Int) := by
    by_contra hcon
    have h1 := mul_le_mul_of_nonneg_left (not_lt.mp hcon) (le_of_lt hd)
    rw [mul_comm] at h1
    linarith
  have hck1 : c + 1 ≤ (k : Int) := hck
  have h2 : S.E.Δ * (c + 1) ≤ S.E.Δ * (k : Int) :=
    mul_le_mul_of_nonneg_left hck1 (le_of_lt hd)
  rw [mul_add, mul_one] at h2
  rw [mul_comm (k : Int)]
  linarith

/-- The joint invariant at round `r`, step `n` and anchor `T` gives
    `AfterPhaseInvariantOverActiveSetsTop` at `r`, `n` and `T`. -/
private theorem joint_toTop_phs {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (Record.protocolOf M S) Sched} {r : Round} {n n_W : Nat} {T : NamedBlock V}
    (h : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x r n n_W T) :
    Restated.AfterPhaseInvariantOverActiveSetsTop M S Sched x r n T :=
  { tick := h.tick
    inPlay := h.inPlay
    anchorEntry := h.anchorEntry
    band := h.band
    sg := h.sg
    sgPairwise := h.sgPairwise
    heads := h.heads
    fin := h.fin
    grade1 := h.grade1
    grade1Performers := h.grade1Performers
    heightCeiling := h.heightCeiling
    targetsTop := h.targetsTop }

open scoped DC in
/-- If `m` can return `a`, then `f <$> m` can return `f a`. -/
private theorem returns_map_intro_phs {α β : Type} (f : α → β) (m : DC.NDRE α) (a : α)
    (h : m ⇢ a) : (f <$> m) ⇢ f a := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image]
  exact ⟨_, h, rfl⟩

open scoped DC in
/-- `m >>= k` can return `b` exactly when `m` can return some `a` from which `k a` can return `b`. -/
private theorem returns_bind_iff_phs {α β : Type} (m : DC.NDRE α) (k : α → DC.NDRE β) (b : β) :
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

open scoped DC in
/-- The lift of the set `s` can return `a` exactly when `a` is a member of `s`. -/
private theorem returns_lift_iff_phs {α : Type} (s : Set α) (a : α) :
    (ExceptT.lift s : DC.NDRE α) ⇢ a ↔ a ∈ s := by
  unfold Record.Returns
  simp only [ExceptT.run_lift, Set.fmap_eq_image, Set.mem_image]
  constructor
  · rintro ⟨a', ha', he⟩
    cases he
    exact ha'
  · intro h
    exact ⟨a, h, rfl⟩

/-- At every store some block is an outcome of `gfHeadWith`. -/
private theorem gfHeadWith_nonempty_phs (facts : Record.Facts M) (contract : M.Contract)
    (E : Env V) (hc : Protocol.HealConfig) (st : M.S) :
    ∃ H, Restated.gfHeadWith M contract E hc st ⇢ H := by
  obtain ⟨T, hT⟩ := facts.fc.voter_filtered_block_tree_nonempty E st st.s
  obtain ⟨W, hW⟩ := facts.fc.voter_view_nonempty E (M.toHealing st).toFG.toSG.toGoldfishStore st.s
  obtain ⟨U, hU⟩ :=
    facts.fc.voter_support_view_nonempty E (M.toHealing st).toFG.toSG.toGoldfishStore st.s
  obtain ⟨H, hH⟩ := facts.fc.get_head_in_tree_with_layer_nonempty contract E hc (M.toHealing st)
    T W U (st.s - 1)
  refine ⟨H, ?_⟩
  unfold Restated.gfHeadWith
  exact (returns_bind_iff_phs _ _ _).2 ⟨T, hT, (returns_bind_iff_phs _ _ _).2
    ⟨W, hW, (returns_bind_iff_phs _ _ _).2 ⟨U, hU,
      (facts.hd.get_head_in_tree_with_eq_layer _ _ _ _ _ _ _ _ _).2 hH⟩⟩⟩

/-- From every node state, some block is an outcome of `gfHeadFrom` at slot `s`. -/
private theorem gfHeadFrom_nonempty_phs (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (s : Slot) : ∃ H, Restated.gfHeadFrom M S before s ⇢ H := by
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc before.st.core.toHealing
    (M.vote_time S.E s) before.cache
  have hn : Restated.voteReadOf M S before s ⇢
      M.mkNode (M.ns_setClock S.E before.st (M.vote_time S.E s)) before.record c :=
    returns_map_intro_phs _ _ _ hc
  obtain ⟨H, hH⟩ := gfHeadWith_nonempty_phs facts (M.gradeContract
    (M.mkNode (M.ns_setClock S.E before.st (M.vote_time S.E s)) before.record c).cache) S.E S.hc
    (M.mkNode (M.ns_setClock S.E before.st (M.vote_time S.E s)) before.record c).st.core
  refine ⟨H, ?_⟩
  unfold Restated.gfHeadFrom
  exact (returns_bind_iff_phs _ _ _).2 ⟨_, hn, hH⟩

/-- The round-`r` action read computed from `before` gives some node state. -/
private theorem actionReadFrom_nonempty_phs (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∃ n, n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r := by
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc (M.toHealing before.st.core)
    (Restated.Vocabulary.Execution.Setup.a M S r) before.cache
  obtain ⟨st, hst⟩ := facts.dt.duties_update_confirmation_with_nonempty (M.gradeContract c) S.E
    S.hc (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r))
    (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1)
  exact ⟨_, c, hc, st, hst, rfl⟩

/-- The frame grade read of every cache at every healing store and round has an outcome. -/
private theorem frameGradeRead_nonempty_phs (facts : Record.Facts M) (c : M.Cache) (E : Env V)
    (hc : Protocol.HealConfig) (st : M.HS) (r : Round) :
    ∃ g, M.frameGradeRead c E hc st r ⇢ g := by
  obtain ⟨g, hg⟩ := facts.gr.read_nonempty (M.gradeContract c) E hc st r
  exact ⟨g, (facts.nd.gradeContract_read c E hc st r g).1 hg⟩

/-- Stamping the clock of a store does not change which blocks pass the confirmation eligibility
    test for slot `s`. -/
private theorem confEligible_setClock_phs (facts : Record.Facts M) (E : Env V) (st : M.NS)
    (t : Int) (s : Slot) :
    Restated.Vocabulary.Protocol.confEligible M E (M.ns_setClock E st t).core s
      = Restated.Vocabulary.Protocol.confEligible M E st.core s := by
  have htau : (M.ns_setClock E st t).core.tau = st.core.tau :=
    facts.sto.tau_eq_of_fields (facts.hd.Sts_setClock_core_T E st t)
      (facts.hd.setClock_core_timestamp_block E st t) (facts.hd.setClock_core_timestamp_vote E st t)
  have hpool : (M.ns_setClock E st t).core.pool s = st.core.pool s :=
    facts.hd.Sts_setClock_core_pool E st t s
  unfold Restated.Vocabulary.Protocol.confEligible
    Restated.Vocabulary.Protocol.confCount Restated.Vocabulary.Protocol.confVotes
    Restated.Vocabulary.Protocol.confEarly Restated.Vocabulary.Protocol.confLate
  rw [htau, hpool, facts.hd.setClock_core_timestamp_vote, facts.hd.Sts_setClock_core_T]

/-- For every store `hs` the round-`r₁` action read gives from `before`, the block `hs` holds as
    confirmed either passes some outcome of the confirmation eligibility test of `before`'s store,
    or is the fork-choice root of `before`'s store stamped with the action instant. -/
private theorem actionHealingStore_live_confirmed_cases_phs (facts : Record.Facts M)
    (S : Setup V) (before : M.N) (r₁ : Round) (hs : M.HS)
    (hhs : hs ∈ Restated.actionHealingStore M S before r₁) :
    (∃ el : Block V → Bool, Restated.Vocabulary.Protocol.confEligible M S.E before.st.core
        (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r₁) - 1) ⇢ el ∧
        el hs.live_confirmed = true) ∨
      hs.live_confirmed
        = Restated.Vocabulary.Protocol.confRoot M
            (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core := by
  classical
  obtain ⟨c, hc, X, hX, st₀, hst₀, rfl⟩ := Restated.actionHealingStore_eq facts S before r₁ hs hhs
  obtain ⟨hF₀, hJ₀, hhj₀, hhm₀, hlc₀, hT₀, hs₀, hσ₀⟩ :=
    Restated.HS_fields_store_with_cache facts c hst₀
  simp only [hF₀, hJ₀, hhj₀, hhm₀, hlc₀, hT₀, hs₀, hσ₀] at *
  rw [Record.Model.HS.live_confirmed, facts.sto.toHealing_live_confirmed]
  by_cases hroot : X.live_confirmed = Restated.Vocabulary.Protocol.confRoot M
      (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core
  · exact Or.inr hroot
  · left
    obtain ⟨tm, htm⟩ := facts.sto.tau_nonempty
      (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core
    obtain ⟨R, hR⟩ := facts.fc.get_sg_root_with_nonempty (M.gradeContract c) S.E S.hc
      (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core.toHealing
      (M.round_of S.hc
        (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core.s)
    obtain ⟨score, hscore⟩ : ∃ score : Block V → ℕ, ∀ B, M.goldfish_score S.E
        (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core.T
        ((beforeCutoff tm (M.support_cutoff S.E (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r₁) - 1))
          ((M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core.pool
            (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r₁) - 1))).filter
          (fun u => M.no_second_vote_in (Restated.Vocabulary.Protocol.confLate M S.E
            (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core
            (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r₁) - 1)) u = true))
        ((beforeCutoff tm (M.support_cutoff S.E (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r₁) - 1))
          ((M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core.pool
            (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r₁) - 1))).filter
          (fun u => M.no_second_vote_in (Restated.Vocabulary.Protocol.confLate M S.E
            (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core
            (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r₁) - 1)) u = true))
        (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r₁) - 1) B ⇢ score B :=
      ⟨fun B => (facts.fc.goldfish_score_nonempty _ _ _ _ _ B).choose,
        fun B => (facts.fc.goldfish_score_nonempty _ _ _ _ _ B).choose_spec⟩
    obtain ⟨W, hW⟩ := facts.fc.ghost_nonempty R
      (M.get_filtered_block_tree
        (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core.toHealing.toFG)
      score
      (fun B => decide (Restated.Vocabulary.Protocol.confCount M S.E
        (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core
        (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r₁) - 1) < 2 * score B))
    have hwalk := facts.hd.update_confirmation_with_live_confirmed_walk_or_fgRoot
      (M.gradeContract c) S.E S.hc
      (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core
      (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r₁) - 1) tm htm R hR score hscore W hW X hX
    have hgen := facts.hd.update_confirmation_with_live_confirmed_genuine_or_fgRoot
      (M.gradeContract c) S.E S.hc
      (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core
      (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r₁) - 1) tm htm R hR score hscore W hW X hX
    rcases hwalk with hwalk | hfg
    · rcases hgen with ⟨-, -, hel⟩ | hfg
      · refine ⟨fun B => decide (Restated.Vocabulary.Protocol.confCount M S.E
          (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core
          (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r₁) - 1) < 2 * score B), ?_, ?_⟩
        · rw [← confEligible_setClock_phs facts S.E before.st
            (Restated.Vocabulary.Execution.Setup.a M S r₁)]
          refine (returns_bind_iff_phs _ _ _).2 ⟨_, returns_map_intro_phs _ _ _
            (returns_map_intro_phs _ _ _ htm), ?_⟩
          refine (returns_bind_iff_phs _ _ _).2 ⟨score, (returns_lift_iff_phs _ _).2 hscore, ?_⟩
          exact (Record.returns_pure _ _).2 rfl
        · rw [hwalk]
          exact hel
      · exact absurd hfg hroot
    · exact absurd hfg hroot

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If every honest active member of slot `s`'s committee votes for a descendant of `B`, it votes
    for a descendant of every ancestor `X` of `B`. -/
theorem headsBelow_mono (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    {X B : Block V} {s : Slot} (hXB : Block.Preceq X B) (h : Restated.HeadsBelow M S Sched x B s) :
    Restated.HeadsBelow M S Sched x X s :=
  fun v m hv hm G hG => preceq_trans_Preceq hXB (h v m hv hm G hG)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If every honest active member of slot `s`'s committee votes for a descendant of `A` and for a
    descendant of `B`, and slot `s` has such a member `w`, then `A` and `B` lie on one chain. -/
theorem compatible_of_headsBelow_common (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {A B : Block V} {s : Slot}
    (hA : Restated.HeadsBelow M S Sched x A s) (hB : Restated.HeadsBelow M S Sched x B s) {w : V}
    (hw : w ∈ Restated.HonSlot M S Sched s) {m : Nat} (hm : Restated.tickStepAt M x m (M.vote_time S.E s)) :
    Block.compatible A B = true := by
  obtain ⟨G, hG⟩ := gfHeadFrom_nonempty_phs facts S (x[m][w].st) s
  exact compatible_of_preceq_common_Preceq (hA w m hw hm G hG) (hB w m hw hm G hG)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- For every node state `n` of the round-`r₁` action read from `before` and every grade read `g` of
    `n`'s frame, the block the SG walk returns at `n`'s healing store under `g` is an ancestor of
    that store's confirmed block, an ancestor of the grade-1 or of the grade-2 root `n`'s frame
    offers, or that store's fork-choice root. -/
theorem sgVote_directed_cases (facts : Record.Facts M) (S : Setup V) (before : M.N) (r₁ : Round)
    (n : M.N)
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
      before r₁)
    (g : Protocol.GradeRead V)
    (hg : M.frameGradeRead n.cache S.E S.hc (M.toHealing n.st.core) r₁ ⇢ g) :
    Block.Preceq (M.currentSGVote (M.toHealing n.st.core) g) (M.toHealing n.st.core).live_confirmed ∨
      (∃ root : Block V, (M.readFrame n.cache (M.toHealing n.st.core) r₁).g1 = some (some root) ∧
        Block.Preceq (M.currentSGVote (M.toHealing n.st.core) g) root) ∨
      (∃ root : Block V, (M.readFrame n.cache (M.toHealing n.st.core) r₁).g2 = some (some root) ∧
        Block.Preceq (M.currentSGVote (M.toHealing n.st.core) g) root) ∨
      M.currentSGVote (M.toHealing n.st.core) g = M.get_fg_root (M.toHealing n.st.core).toFG := by
  rcases Restated.sgVote_source facts (stH := M.toHealing n.st.core) (grades := g) with
    h | (hQ | hA) | h
  · exact Or.inl h
  ·
    obtain ⟨o, ho⟩ := facts.gr.grade2Block_nonempty (M.toHealing n.st.core)
      (M.readFrame n.cache (M.toHealing n.st.core) r₁)
    have hgo := facts.nd.ModelProperties_gradeContract_read_Q2 n.cache S.E S.hc
      (M.toHealing n.st.core) r₁ g ((facts.nd.gradeContract_read _ _ _ _ _ g).2 hg) o ho
    obtain ⟨root, hroot, hpre⟩ := facts.gr.grade2Block_preceq_root o ho (hgo.symm.trans hQ)
    exact Or.inr (Or.inr (Or.inl ⟨root, hroot, hpre⟩))
  ·
    obtain ⟨A, hA'⟩ := facts.gr.anchor_nonempty S.E S.hc (M.toHealing n.st.core) r₁
      (M.readFrame n.cache (M.toHealing n.st.core) r₁).g1
    have hvA : M.currentSGVote (M.toHealing n.st.core) g = A :=
      hA.trans (facts.gr.frameGradeRead_anchor n.cache S.E S.hc _ r₁ g hg A hA')
    rcases facts.gr.Sts_anchor_cases S (M.toHealing n.st.core) r₁ _ A hA' with
      hfg | ⟨root, hroot, hpre⟩
    · exact Or.inr (Or.inr (Or.inr (hvA.trans hfg)))
    · exact Or.inr (Or.inl ⟨root, hroot, by rw [hvA]; exact hpre⟩)
  · exact Or.inr (Or.inr (Or.inr h))

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If `v_1` is honest through step `n + 1`, `n` being the round-`r₁` tick step, its round-`r₁`
    attestation is in the sent log `x[n + 1].sent`, and `C` is a body of `v_1`'s store with the root
    that attestation names as confirmed, then `C`'s erasure is the block the SG walk returns at
    every node state and grade read of `v_1`'s round-`r₁` action read. -/
theorem freshSG_erase_eq_sgVote (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {r₁ : Round} {n : Nat} (hn : Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S r₁))) {v_1 : V}
    (hv_1 : Restated.HonestThrough M Sched x (n + 1) v_1) {a : NamedAttestation V}
    (ha : a.round = r₁) (hav : a.val_index = v_1)
    (hsent : (⟨v_1, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n + 1].sent)
    {C : NamedBlock V} (hC : C ∈ (x[n + 1][v_1].st).st.bodies) (hconf : a.confirmed = some C.root) :
    ∀ m ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (x[n][v_1].st) r₁,
      ∀ g : Protocol.GradeRead V,
        M.frameGradeRead m.cache S.E S.hc (M.toHealing m.st.core) r₁ ⇢ g →
        C.erase = M.currentSGVote (M.toHealing m.st.core) g := by
  have _hr_0 : M.reachedNode (x[n][v_1].st) := Record.reachedNode_sts facts S Sched x n v_1
  have _hr_1 : M.reachedNode (Record.wakeStage M Sched ((Restated.Vocabulary.Execution.Setup.a M S r₁)) x[n] v_1) := Record.reachedNode_wakeStage facts S Sched x n v_1 ((Restated.Vocabulary.Execution.Setup.a M S r₁))
  intro m hm g hg
  have hvh : HonestThroughTime Sched (x[n + 1].time : Int) v_1 := fun t ht => hv_1 t ht
  obtain ⟨-, k, -, htick, -, out, hout, hemit⟩ :=
    Restated.attest_round_of_sent facts S Sched x hvh hexec.toUnforgeability hav le_rfl hsent
  rw [ha] at htick hout
  have hkn : k = n := Restated.tickStepAt_unique facts x htick hn
  rw [hkn] at hout
  obtain ⟨D, hD⟩ := facts.dt.attest_with_nonempty (M.gradeContract m.cache)
    (Setup.alwaysAwake S).E (Setup.alwaysAwake S).hc ((Setup.alwaysAwake S).node v_1) m.st m.record
  have hmemA : D.2.2 ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][v_1].st) v_1 r₁ :=
    ⟨m, hm, D.1, D.2.1, hD⟩
  have hA : Restated.actionAttestationFrom M (Setup.alwaysAwake S)
      (Record.wakeStage M Sched ((Restated.Vocabulary.Execution.Setup.a M S r₁)) x[n] v_1) v_1 r₁ =
      Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][v_1].st) v_1 r₁ := by
    simp only [Restated.actionAttestationFrom,
      Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom, Record.wakeStage_st facts,
      Record.wakeStage_record facts, Record.wakeStage_cache facts]
  have _hv_s1 := Record.runs_as_wakeStage facts S Sched x (n) v_1 (Restated.Vocabulary.Execution.Setup.a M S r₁)
  have haeq : a = D.2.2 :=
    Restated.attest_of_tick_eq facts S v_1 _ r₁ hout hemit _ (by rw [hA]; exact hmemA)
  rw [haeq] at hconf
  have h := (Restated.attest_confirmed_eq_sgVote facts S (x[n][v_1].st) v_1 r₁ m hm D hD g hg).symm.trans
    hconf
  have hroot : C.root = (M.currentSGVote (M.toHealing m.st.core) g).root := (Option.some_inj.mp h).symm
  have hvn : Restated.HonestThrough M Sched x n v_1 := fun t ht =>
    hv_1 t (le_trans ht (Restated.time_mono_int facts S Sched x (Nat.le_succ n)))
  obtain ⟨D', hD', hDe⟩ := Restated.exists_inLog_erase_actionSGVote facts S Sched x hvn r₁ m hm g hg
  have hDroot : C.root = D'.root := by
    rw [hroot, ← hDe, Proofs.NamedWire.erase_root]
  rw [Restated.erase_eq_of_root_eq_inLog facts S Sched x hexec (Restated.blockInLog_of_mem_bodies facts S Sched hv_1 hC) hD'
    hDroot, hDe]

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- For every round `r` at or after the switch round, round `r` opens at least `8RΔ` after `tGAT`. -/
theorem tGAT_add_two_rounds_le_opening (facts : Record.Facts M) (S : Setup V) (tGAT tE : Int)
    (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    {r : Round} (hr : Restated.switchRound M S tE ≤ r) :
    tGAT + 8 * (S.hc.R : Int) * S.E.Δ ≤ M.opening S.E S.hc r := by
  have hd := S.E.Δ_pos
  have hbig := le_trans (Restated.switchRound_ge_of_healingLengthη facts S tGAT tE gap hgst hlen) hr
  have hsw : Restated.Vocabulary.Statements.Instantiation.roundAt M S tGAT + 1 + 1 + 1 ≤ r :=
    three_le_of_sum_nat_s2 _ _ _ _ _ _ hbig S.hc.η_SG_ge_one
  have h1 : tGAT ≤ M.opening S.E S.hc (Restated.Vocabulary.Statements.Instantiation.roundAt M S tGAT + 1) :=
    le_trans (Restated.Vocabulary.Statements.roundAt_spec facts S tGAT)
      (action_le_opening_succ_phs facts S (Restated.Vocabulary.Statements.Instantiation.roundAt M S tGAT))
  have h2 := facts.gr.Sts_opening_mono S hsw
  have e1 : ∀ k : Round, M.opening S.E S.hc (k + 1)
      = M.opening S.E S.hc k + 4 * (S.hc.R : Int) * S.E.Δ := by
    intro k
    rw [facts.gr.opening_add S.E S.hc k 1]
    push_cast; ring
  rw [e1, e1] at h2
  linarith

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If round `r` is at or after the switch round, there is an instant `t'` at or before `tE` and at
    or before the start of round `r`'s opening slot, at least one delay after `tGAT`, from which the
    committee majority holds. -/
theorem exists_cone_cutoff_at_opening (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (tE : Int)
    (hmono : Sched.MonotoneCorruption)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hcs : Restated.committeeSleepinessW M S Sched tE)
    {r : Round} (hr : Restated.switchRound M S tE ≤ r) :
    ∃ t' : Int, t' ≤ tE ∧ t' ≤ slotStart S.E.Δ ((M.opening_slot S.hc r)) ∧
      tGAT + S.E.Δ ≤ t' ∧ Restated.committeeSleepinessW M S Sched t' := by
  have hd := S.E.Δ_pos
  have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
  have hop : tGAT + (4 * (S.hc.R : Int) + 7) * S.E.Δ ≤ slotStart S.E.Δ ((M.opening_slot S.hc r)) := by
    have h0 := Restated.tGAT_add_two_rounds_le_opening facts S tGAT tE gap hgst hlen hr
    rw [opening_eq_slotStart_phs facts S r] at h0
    have h7 : 7 * S.E.Δ ≤ 4 * (S.hc.R : Int) * S.E.Δ := by nlinarith
    nlinarith
  by_cases h : tE ≤ slotStart S.E.Δ ((M.opening_slot S.hc r))
  · exact ⟨tE, le_rfl, h, Restated.delta_le_of_healingLengthη facts S hlen, hcs⟩
  ·
    have htG : (0 : Int) ≤ tGAT := le_trans S.E.t_GST_nonneg hgst
    have hpos2 : 2 ≤ ((M.opening_slot S.hc r) : Nat) := by
      have h0 := Restated.tGAT_add_two_rounds_le_opening facts S tGAT tE gap hgst hlen hr
      cases r with
      | zero => exfalso; rw [opening_zero_phs facts S] at h0; nlinarith
      | succ r0 =>
        rw [facts.gr.opening_slot_succ]
        exact le_trans (le_trans (by decide) S.hc.R_ge_three) (Nat.le_add_left _ _)
    have hs1 : (M.opening_slot S.hc r) - 1 + 1 = (M.opening_slot S.hc r) :=
      Nat.sub_add_cancel (le_trans (by decide) hpos2)
    have hpos' : 1 ≤ (M.opening_slot S.hc r) - 1 := Nat.le_sub_of_add_le hpos2
    have hprev : slotStart S.E.Δ ((M.opening_slot S.hc r) - 1)
        = slotStart S.E.Δ ((M.opening_slot S.hc r)) - 4 * S.E.Δ := by
      have e := slotStart_succ S.E.Δ ((M.opening_slot S.hc r) - 1)
      rw [hs1] at e
      linarith
    have hwv : wVote S = 4 * (S.hc.R : Int) * S.E.Δ + 2 * S.E.Δ := by unfold wVote; ring
    have hwin : tGAT + wVote S ≤ slotStart S.E.Δ ((M.opening_slot S.hc r) - 1) + S.E.Δ := by
      rw [hprev, hwv]; nlinarith
    have hmaj := Restated.committeeSleepinessW_of_phase facts S Sched hmono hcom hcs hphase hpos' hwin
    rw [hs1] at hmaj
    refine ⟨slotStart S.E.Δ ((M.opening_slot S.hc r)), le_of_lt (not_le.mp h), le_rfl, ?_, hmaj⟩
    nlinarith

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If the joint invariant holds at round `r + 1` and every round-`r` SG block of a member of
    `HonRound S Sched r` lies on one chain with `X`, then at every slot of round `r + 1` after its
    opening slot, every grade-1 root of the vote read of every honest active committee member lies
    on one chain with `X`. -/
theorem voteGradeOneCompatible_later_ofPrevSG (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hmono : Sched.MonotoneCorruption)
    {r : Round} {n n_W : Nat} {T : NamedBlock V}
    (hJ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x (r + 1) n n_W T)
    {n_prev : Nat} (hnp : Restated.tickStepAt M x n_prev ((Restated.Vocabulary.Execution.Setup.a M S r))) {X : Block V}
    (hPG : ∀ v_2 ∈ Restated.HonRound M S Sched r, ∀ a : NamedAttestation V,
      a.round = r → a.val_index = v_2 →
      (⟨v_2, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n_prev + 1].sent →
      ∀ G : NamedBlock V, G ∈ (x[n_prev + 1][v_2].st).st.bodies → a.confirmed = some G.root →
      Block.compatible G.erase X = true)
    {s : Slot} {j : Nat} (hj1 : 1 ≤ j) (hjR : j < S.hc.R)
    (hsj : s + 1 = (M.opening_slot S.hc (r + 1)) + j) :
    Restated.VoteGradeOneCompatible M S x X s := by
  intro v mr hv hmr nr hnr root hroot
  obtain ⟨m, B, hm, hB, hpre⟩ := Restated.voteFrame_g1_provenance facts S Sched x hmr v root hnr hroot
  have hround : (M.round_of S.hc (s + 1)) = r + 1 := by
    rw [hsj]; exact facts.gr.round_of_opening_slot_add S.hc (r + 1) hjR
  rw [hround] at hm hB
  have hv' : v ∈ Restated.HonSlot M S Sched ((M.opening_slot S.hc (r + 1)) + j) := by rw [← hsj]; exact hv
  have hvP : v ∈ Restated.grade1PerformersW M S Sched (r + 1) :=
    Finset.mem_sdiff.2
      (Restated.awakeThroughout_grade1_window_of_mem_honSlot facts S Sched hmono hjR hv')
  obtain ⟨b, hb⟩ := facts.gr.gradeBool_nonempty S.E (M.gradeView (M.toHealing (x[m][v].st).st.core))
    (x[m][v].st).st.core.F S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) .g1)
    (M.late S.E S.hc (r + 1) .g1) B
  obtain ⟨v_2, hv_2, a, ha, hai, hsent, G, hG, hconf, hBG⟩ :=
    hJ.gradedUnderPrevSGPerformers n_prev hnp v hvP m hm B b hb
      (hB b hb)
  exact Protocol.compatible_of_preceq_of_compatible (preceq_trans_Preceq hpre hBG)
    (hPG v_2 hv_2 a ha hai hsent G hG hconf)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If every round-`r` SG block of a member of `HonRound S Sched r` lies on one chain with `X`, then
    at round `(r + 1)`'s opening slot, every grade-1 root of the vote read of every honest active
    committee member lies on one chain with `X`. -/
theorem voteGradeOneCompatible_opening_ofSG (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (hsync : Restated.SynchronyFromWake M S x) (hmult : AwakeAtMultiples S Sched)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE) (hcs : Restated.committeeSleepinessW M S Sched tE)
    {r : Round} {n : Nat} {T : NamedBlock V}
    (hr : Restated.switchRound M S tE ≤ r) (hinv : Restated.AfterPhaseInvariantOverActiveSetsTop M S Sched x r n T)
    (hcross : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepFinalizedCrossingUnderAnchor M S Sched x r n'' T)
    {X : Block V}
    (hSG : ∀ v_1 ∈ Restated.HonRound M S Sched r, ∀ a : NamedAttestation V,
      a.round = r → a.val_index = v_1 →
      (⟨v_1, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n + 1].sent →
      ∀ G : NamedBlock V, G ∈ (x[n + 1][v_1].st).st.bodies → a.confirmed = some G.root →
      Block.compatible G.erase X = true)
    {s : Slot} (hs : s + 1 = (M.opening_slot S.hc (r + 1))) :
    Restated.VoteGradeOneCompatible M S x X s := by
  intro v mr hv hmr nr hnr root hroot
  have hd := S.E.Δ_pos
  have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
  have hsucc := facts.gr.action_succ_eq_add_rounds S r
  obtain ⟨m, B, hm, hB, hpre⟩ := Restated.voteFrame_g1_provenance facts S Sched x hmr v root hnr hroot
  have hround : (M.round_of S.hc (s + 1)) = r + 1 := by
    rw [hs]
    have h := facts.gr.round_of_opening_slot_add S.hc (r + 1) (j := 0)
      (lt_of_lt_of_le (by decide) S.hc.R_ge_three)
    simpa using h
  rw [hround] at hm hB
  have hvt : M.vote_time S.E (s + 1) = (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) - 5 * S.E.Δ := by
    rw [hs]
    have h := Restated.vote_time_opening_slot_add facts S (r + 1) 0
    simpa using h
  have hdom5 : M.domain S.E S.hc (r + 1) .g1 + 5 * S.E.Δ
      ≤ Restated.Vocabulary.Execution.Setup.a M S (r + 1) :=
    facts.gr.domain_add_five_delta_le_action S (r + 1) .g1
  have hdom : M.domain S.E S.hc (r + 1) .g1 ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) := facts.gr.domain_le_action S (r + 1) .g1
  have hwin : v ∈ Sched.awakeThroughout (M.vote_time S.E (s + 1) - wVote S)
      (M.vote_time S.E (s + 1)) := by
    rw [← facts.sch.slotStart_add_delta_eq_vote_time S.E (s + 1)]; exact ((Restated.mem_HonSlot facts).mp hv).1
  have hwv : wVote S = 4 * (S.hc.R : Int) * S.E.Δ + 2 * S.E.Δ := by unfold wVote; ring
  have hawT : v ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S r)) (M.domain S.E S.hc (r + 1) .g1) :=
    awakeThroughout_mono Sched hwin (by rw [hvt, hwv, hsucc]; linarith)
      (by rw [hvt]; linarith)
  have hvS : v ∉ Sched.adv (M.domain S.E S.hc (r + 1) .g1) := by
    intro hin
    refine ((Restated.mem_HonSlot facts).mp hv).2.2 (hmono _ _ ?_ hin)
    have e : M.confirmation_time S.E (s + 1)
        = M.vote_time S.E (s + 1) + 5 * S.E.Δ := by
      exact (vote_time_add_five_delta_phs facts S.E (s + 1)).symm
    rw [e, hvt]; linarith
  obtain ⟨b, hb⟩ := facts.gr.gradeBool_nonempty S.E (M.gradeView (M.toHealing (x[m][v].st).st.core))
    (x[m][v].st).st.core.F S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) .g1)
    (M.late S.E S.hc (r + 1) .g1) B
  have hd1 : (1 : Int) ≤ S.E.Δ := S.E.Δ_pos
  have hlo := facts.gr.action_delta_le_early S S.hc.R_ge_three (Nat.lt_succ_self r)
  have h21 := facts.gr.early_g2_add_delta_le_early_g1 S (r + 1)
  have he0 := facts.gr.early_g1_add_delta_le_early_g0 S (r + 1)
  have hl0 := facts.gr.early_le_late S.E S.hc (r + 1) .g0
  have hl1 := facts.gr.late_g0_add_delta_le_late_g1 S (r + 1)
  have ht₀ : Restated.Vocabulary.Execution.Setup.a M S r ≤ M.late S.E S.hc (r + 1) .g1 - 1 - 2 * S.E.Δ := by
    show M.a S.hc S.E.Δ r ≤ _
    linarith
  have hrecv := Restated.receives_of_awake_from_action facts S Sched x hsync .g1
    (Restated.gst_le_action_of_switchRound_le facts S tGAT tE gap hgst hlen hr) hawT
    (le_of_lt (Restated.action_delta_lt_domain_succ facts S r .g1))
  obtain ⟨v_1, hv_1, a, ha, hai, hsent, G, hG, hconf, hBG⟩ :=
    Restated.graded_preceq_freshSG_at_awakeReader_recv facts S Sched x tE hexec hmono htd hsync hmult tGAT
      gap hgst hlen hcv hthird hphase hrsW hcs hr hinv hcross hdom _ ht₀ hawT hrecv hvS hm B (hB b hb ▸ hb)
  exact Protocol.compatible_of_preceq_of_compatible (preceq_trans_Preceq hpre hBG)
    (hSG v_1 hv_1 a ha hai hsent G hG hconf)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If every justified block an honest validator holds, from round `r`'s second slot up to the step
    after the round-`(r + 1)` tick, is an ancestor of `T`, then at every slot from round `r`'s
    second slot whose vote instant is before `S.a (r + 1)`, every honest active committee member
    holds, before its vote tick, a finalized block and a justified block that are ancestors of `T`. -/
theorem voteFinJust_preceq_at_later_slots (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE)
    {r : Round} {n : Nat} {T : NamedBlock V}
    (hr : Restated.switchRound M S tE ≤ r) (hinv : Restated.AfterPhaseInvariantOverActiveSetsTop M S Sched x r n T)
    (hcross : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepFinalizedCrossingUnderAnchor M S Sched x r n'' T)
    {n' : Nat} (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    (hJT : ∀ (v : V) (n₁ : Nat),
      M.vote_time S.E ((M.opening_slot S.hc r) + 1) - 1 ≤ (x[n₁].time : Int) →
      n₁ ≤ n' + 1 → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J T.erase)
    {s : Slot} (hlo : M.vote_time S.E ((M.opening_slot S.hc r) + 1)
      ≤ M.vote_time S.E (s + 1))
    (hhi : M.vote_time S.E (s + 1) < (Restated.Vocabulary.Execution.Setup.a M S (r + 1))) :
    ∀ (v : V) (mr : Nat), v ∈ Restated.HonSlot M S Sched (s + 1) →
      Restated.tickStepAt M x mr (M.vote_time S.E (s + 1)) →
      Block.Preceq (x[mr][v].st).st.core.F T.erase ∧
        Block.Preceq (x[mr][v].st).st.core.J T.erase := by
  intro v mr hv hmr
  have hd := S.E.Δ_pos
  obtain ⟨-, hmr0⟩ := Restated.tickStepAt_time facts x hmr
  have hmrn' : mr ≤ n' := Restated.le_tick_of_time_lt_action facts S Sched x hn' (by linarith)
  have hct : (x[mr].time : Int) ≤ M.confirmation_time S.E (s + 1) := by
    have e : M.confirmation_time S.E (s + 1) = M.vote_time S.E (s + 1) + 5 * S.E.Δ :=
      (vote_time_add_five_delta_phs facts S.E (s + 1)).symm
    linarith
  have hvh : Restated.HonestThrough M Sched x mr v := Restated.honestThrough_of_mem_HonSlot facts S Sched x hmono hv hct
  exact ⟨Restated.fin_old_anchor_before_succ_tick_of_hypotheses facts (hcross := hcross) S Sched x tE hexec
      hmono tGAT gap hgst hlen hthird hphase hrsW hr hinv hn' v mr hmrn' hvh,
    hJT v mr (by linarith) (Nat.le_succ_of_le hmrn') hvh⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If every honest active member of slot `(s + 1)`'s committee holds, before its vote tick, a
    finalized block and a justified block that are ancestors of `T`, and `T` is an ancestor of `X`,
    then both blocks lie on one chain with `X`. -/
theorem voteFinJustCompatible_of_preceq (facts : Record.Facts M) (S : Setup V) {Sched : Schedule V}
    (x : AtomicExec (Record.protocolOf M S) Sched) {T X : Block V} {s : Slot}
    (hFJ : ∀ (v : V) (mr : Nat), v ∈ Restated.HonSlot M S Sched (s + 1) →
      Restated.tickStepAt M x mr (M.vote_time S.E (s + 1)) →
      Block.Preceq (x[mr][v].st).st.core.F T ∧ Block.Preceq (x[mr][v].st).st.core.J T)
    (hTX : Block.Preceq T X) : Restated.VoteFinJustCompatible M S x X s := by
  intro v mr hv hmr
  obtain ⟨hF, hJ⟩ := hFJ v mr hv hmr
  exact ⟨compatible_of_preceq_common_Preceq (preceq_trans_Preceq hF hTX) (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _)),
    fun _ => compatible_of_preceq_common_Preceq (preceq_trans_Preceq hJ hTX) (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _))⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- From an eligible confirmation at slot `s_c`: for every slot `s` from `s_c` to round `(r + 1)`'s
    opening slot, every block strictly between an honest active reader's SG root and `X` is in that
    reader's slot-`(s + 1)` voter tree. -/
theorem coneAnchorChainInTree_of_eligibleConfirmation_later (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (hsync : Restated.SynchronyFromWake M S x) (hmult : AwakeAtMultiples S Sched)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE) (hcs : Restated.committeeSleepinessW M S Sched tE)
    {r : Round} {n : Nat} {T : NamedBlock V}
    (hr : Restated.switchRound M S tE ≤ r) (hinv : Restated.AfterPhaseInvariantOverActiveSetsTop M S Sched x r n T)
    (hcross : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepFinalizedCrossingUnderAnchor M S Sched x r n'' T)
    {s_c : Slot} {nq : Nat} {q : V} {H X : Block V}
    (hqaw : q ∈ Sched.awakeThroughout (slotStart S.E.Δ s_c - S.E.Δ)
      (M.confirmation_time S.E s_c))
    (hqh : HonestThroughTime Sched (M.confirmation_time S.E s_c) q)
    (el : Block V → Bool)
    (hel' : Restated.Vocabulary.Protocol.confEligible M S.E (x[nq][q].st).st.core s_c ⇢ el)
    (hel : el H = true)
    (hXH : Block.Preceq X H) (hTX : Block.Preceq T.erase X)
    (hlo : tGAT ≤ slotStart S.E.Δ s_c)
    {s : Slot} (hss : s_c ≤ s) (hj : s + 1 ≤ (M.opening_slot S.hc (r + 1)) + 1) :
    Restated.ConeAnchorChainInTree M S x X s := by
  obtain ⟨nc, Xn, hnc, hXn, hqnc, hHXn⟩ :=
    Restated.supporterHead_held_before_cut facts S Sched x htd hqaw hqh el hel' hel
      (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›)
  have hd := S.E.Δ_pos
  have hncself := (Restated.tickStepAt_time facts x hnc).2
  have hsc := slotStart_add_two_delta_le_support_cutoff_phs facts S s_c
  have hscm := facts.sch.support_cutoff_mono S.E hss
  have hvf := support_cutoff_add_delta_le_view_freeze_phs facts S s
  exact Restated.coneAnchorChainInTree_of_heldDescendant facts S Sched x tE hexec hmono htd hsync hmult tGAT gap
    hgst hlen hcv hthird hphase hrsW hcs hr hinv hcross hXn hqnc (by linarith)
    (preceq_trans_Preceq hXH hHXn) hTX (by linarith) hj (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- For every slot `s` from round `(r + 1)`'s opening slot to the slot before round `(r + 2)`'s
    opening slot, `ConeAnchorCompatible S x X s` holds: the SG root of every honest active reader
    lies on one chain with `X`. -/
theorem coneAnchorCompatible_roundSlots_ofSG (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (hsync : Restated.SynchronyFromWake M S x) (hmult : AwakeAtMultiples S Sched)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE) (hcs : Restated.committeeSleepinessW M S Sched tE)
    {r : Round} {n n_W : Nat} {T : NamedBlock V}
    (hr : Restated.switchRound M S tE ≤ r + 1)
    (hJ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x (r + 1) n n_W T)
    {n' : Nat} (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1 + 1))))
    (hcross : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1 + 1))) →
      Restated.StepFinalizedCrossingUnderAnchor M S Sched x (r + 1) n'' T)
    (hJT : ∀ (v : V) (n₁ : Nat),
      M.vote_time S.E ((M.opening_slot S.hc (r + 1)) + 1) - 1 ≤ (x[n₁].time : Int) →
      n₁ ≤ n' + 1 → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J T.erase)
    {n_prev : Nat} (hnp : Restated.tickStepAt M x n_prev ((Restated.Vocabulary.Execution.Setup.a M S r)))
    {X : Block V} (hTX : Block.Preceq T.erase X)
    (hSG : ∀ v_1 ∈ Restated.HonRound M S Sched (r + 1), ∀ a : NamedAttestation V,
      a.round = r + 1 → a.val_index = v_1 →
      (⟨v_1, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n + 1].sent →
      ∀ G : NamedBlock V, G ∈ (x[n + 1][v_1].st).st.bodies → a.confirmed = some G.root →
      Block.compatible G.erase X = true)
    (hPG : ∀ v_2 ∈ Restated.HonRound M S Sched r, ∀ a : NamedAttestation V,
      a.round = r → a.val_index = v_2 →
      (⟨v_2, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n_prev + 1].sent →
      ∀ G : NamedBlock V, G ∈ (x[n_prev + 1][v_2].st).st.bodies → a.confirmed = some G.root →
      Block.compatible G.erase X = true) :
    ∀ s : Slot, (M.opening_slot S.hc (r + 1)) ≤ s →
      s ≤ (M.opening_slot S.hc (r + 1 + 1)) - 1 → Restated.ConeAnchorCompatible M S x X s := by
  have hinv := joint_toTop_phs hJ
  have hd := S.E.Δ_pos
  have hR3 : 3 ≤ S.hc.R := S.hc.R_ge_three
  have hosucc := facts.gr.opening_slot_succ S.hc (r + 1)
  obtain ⟨hs1, hle1⟩ := pred_facts_s2 _ _ _ hosucc hR3
  have hvtO : M.vote_time S.E ((M.opening_slot S.hc (r + 1 + 1)))
      = (Restated.Vocabulary.Execution.Setup.a M S (r + 1 + 1)) - 5 * S.E.Δ := by
    have h := Restated.vote_time_opening_slot_add facts S (r + 1 + 1) 0
    simpa using h
  intro s h0 h1
  have h1' : s ≤ (M.opening_slot S.hc (r + 1)) + S.hc.R - 1 := by rw [← hosucc]; exact h1
  have hsle : s + 1 ≤ (M.opening_slot S.hc (r + 1 + 1)) := succ_le_of_le_pred_s2 _ _ _ h1 hle1
  have hvlo : M.vote_time S.E ((M.opening_slot S.hc (r + 1)) + 1)
      ≤ M.vote_time S.E (s + 1) := by
    exact facts.sch.vote_time_mono S.E (Nat.succ_le_succ h0)
  have hvhi : M.vote_time S.E (s + 1) < (Restated.Vocabulary.Execution.Setup.a M S (r + 1 + 1)) := by
    have hm : M.vote_time S.E (s + 1)
        ≤ M.vote_time S.E ((M.opening_slot S.hc (r + 1 + 1))) := by
      exact facts.sch.vote_time_mono S.E hsle
    rw [hvtO] at hm; linarith
  have hFJ := Restated.voteFinJust_preceq_at_later_slots facts S Sched x tE hexec hmono tGAT gap hgst hlen
    hthird hphase hrsW hr hinv hcross hn' hJT hvlo hvhi
  refine Restated.coneAnchorCompatible_of_voteReads facts S x ?_ (Restated.voteFinJustCompatible_of_preceq facts S x hFJ hTX)
  rcases slot_succ_cases_s2 _ _ _ h0 h1' hR3 with ⟨hj1, hjR, hsj⟩ | hsO
  · exact Restated.voteGradeOneCompatible_later_ofPrevSG facts S Sched x hmono hJ hnp hPG hj1 hjR hsj
  · exact Restated.voteGradeOneCompatible_opening_ofSG facts S Sched x tE hexec hmono htd hsync hmult tGAT gap
      hgst hlen hcv hthird hphase hrsW hcs hr hinv hcross hSG (by rw [hsO, hosucc])

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If the joint invariant holds at round `r + 1` with anchor `T`, `X` is a descendant of `T` that
    lies on one chain with every SG block of rounds `r` and `r + 1`, `X`'s chain from every reader's
    SG root is in that reader's voter tree from round `(r + 1)`'s second slot to round `(r + 2)`'s
    opening slot, and every honest active member of slot `s₀`'s committee votes for a descendant of
    `X`, with `s₀` round `(r + 1)`'s first or second slot, then every honest active member of round
    `(r + 2)`'s opening slot's committee votes there for a descendant of `X`. -/
theorem headsBelow_nextOpening_of_base (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (hsync : Restated.SynchronyFromWake M S x) (hmult : AwakeAtMultiples S Sched)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE) (hcs : Restated.committeeSleepinessW M S Sched tE)
    {r : Round} {n n_W : Nat} {T : NamedBlock V}
    (hr : Restated.switchRound M S tE ≤ r + 1)
    (hJ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x (r + 1) n n_W T)
    {n' : Nat} (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1 + 1))))
    (hcross : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1 + 1))) →
      Restated.StepFinalizedCrossingUnderAnchor M S Sched x (r + 1) n'' T)
    (hJT : ∀ (v : V) (n₁ : Nat),
      M.vote_time S.E ((M.opening_slot S.hc (r + 1)) + 1) - 1 ≤ (x[n₁].time : Int) →
      n₁ ≤ n' + 1 → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J T.erase)
    {n_prev : Nat} (hnp : Restated.tickStepAt M x n_prev ((Restated.Vocabulary.Execution.Setup.a M S r)))
    {X : Block V} (hTX : Block.Preceq T.erase X)
    (hSG : ∀ v_1 ∈ Restated.HonRound M S Sched (r + 1), ∀ a : NamedAttestation V,
      a.round = r + 1 → a.val_index = v_1 →
      (⟨v_1, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n + 1].sent →
      ∀ G : NamedBlock V, G ∈ (x[n + 1][v_1].st).st.bodies → a.confirmed = some G.root →
      Block.compatible G.erase X = true)
    (hPG : ∀ v_2 ∈ Restated.HonRound M S Sched r, ∀ a : NamedAttestation V,
      a.round = r → a.val_index = v_2 →
      (⟨v_2, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n_prev + 1].sent →
      ∀ G : NamedBlock V, G ∈ (x[n_prev + 1][v_2].st).st.bodies → a.confirmed = some G.root →
      Block.compatible G.erase X = true)
    (hpath : ∀ s : Slot, (M.opening_slot S.hc (r + 1)) ≤ s →
      s + 1 ≤ (M.opening_slot S.hc (r + 1 + 1)) → Restated.ConeAnchorChainInTree M S x X s)
    {s₀ : Slot} (hs₀ : s₀ = (M.opening_slot S.hc (r + 1)) ∨ s₀ = (M.opening_slot S.hc (r + 1)) + 1)
    (hbase : Restated.HeadsBelow M S Sched x X s₀) :
    Restated.HeadsBelow M S Sched x X ((M.opening_slot S.hc (r + 1 + 1))) := by
  have hinv := joint_toTop_phs hJ
  have hd := S.E.Δ_pos
  have hd1 : (1 : Int) ≤ S.E.Δ := hd
  have hR3 : 3 ≤ S.hc.R := S.hc.R_ge_three
  have hosucc := facts.gr.opening_slot_succ S.hc (r + 1)
  obtain ⟨hs1, hle1⟩ := pred_facts_s2 _ _ _ hosucc hR3
  obtain ⟨t', ht'E, ht's, ht'len, hcs'⟩ :=
    Restated.exists_cone_cutoff_at_opening facts S Sched tE hmono hcom tGAT gap hgst hlen hphase hcs hr
  have hfin := Restated.fin_old_anchor_before_succ_tick_of_hypotheses facts (hcross := hcross) S Sched x tE hexec
    hmono tGAT gap hgst hlen hthird hphase hrsW hr hinv hn'
  have hunder := Restated.deliveredDescendant_mono facts S Sched x
    (Restated.deliveredDescendantUnderFinalized_anchor facts S Sched x hn' hfin tGAT) hTX
  have hunderS := Restated.finalizedPreceqAtSteps_mono facts S Sched x
    (Restated.finalizedPreceqAtSteps_anchor facts S Sched x hn' hfin tGAT) hTX
  have hct2 : M.confirmation_time S.E ((M.opening_slot S.hc (r + 1 + 1))) = (Restated.Vocabulary.Execution.Setup.a M S (r + 1 + 1)) :=
    Restated.confirmation_time_opening_slot facts S (r + 1 + 1)
  have hsR : M.support_cutoff S.E ((M.opening_slot S.hc (r + 1 + 1)) - 1)
      ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1 + 1)) - 1 := by
    have e1 := facts.sch.support_cutoff_le_vote_time_succ S.E ((M.opening_slot S.hc (r + 1 + 1)) - 1)
    rw [hs1] at e1
    have e2 := facts.sch.slotStart_add_delta_eq_vote_time S.E ((M.opening_slot S.hc (r + 1 + 1)))
    have e3 : M.confirmation_time S.E ((M.opening_slot S.hc (r + 1 + 1))) = slotStart S.E.Δ ((M.opening_slot S.hc (r + 1 + 1))) + 6 * S.E.Δ :=
      (facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E ((M.opening_slot S.hc (r + 1 + 1)))).symm
    rw [hct2] at e3
    linarith
  have hAB := Restated.coneAnchorCompatible_roundSlots_ofSG facts S Sched x tE hexec hmono htd hsync hmult
    tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr hJ hn' hcross hJT hnp hTX hSG hPG
  have hpath' : ∀ s : Slot, (M.opening_slot S.hc (r + 1)) ≤ s →
      s ≤ (M.opening_slot S.hc (r + 1 + 1)) - 1 → Restated.ConeAnchorChainInTree M S x X s := by
    intro s h0 h1
    have hsle : s + 1 ≤ (M.opening_slot S.hc (r + 1 + 1)) := succ_le_of_le_pred_s2 _ _ _ h1 hle1
    exact hpath s h0 hsle
  have hopos : 0 < (M.opening_slot S.hc (r + 1)) := facts.gr.opening_slot_pos S (Nat.succ_pos r)
  have hsE : ∀ s : Slot, (M.opening_slot S.hc (r + 1)) ≤ s → t' ≤ slotStart S.E.Δ s :=
    fun s hs => le_trans ht's (slotStart_mono S hs)
  rcases hs₀ with rfl | rfl
  · have hrange := Restated.headsBelow_range_afterPhase (hr1 := Restated.one_le_round_of_of_opening_slot_le facts S (r := r + 1) (Nat.le_add_left 1 r) le_rfl) facts S Sched x hexec hsync hmult htd hmono hgst hcv
      (fun t h1 h2 => hphase t h1 (le_trans h2 ht'E))
      (fun t h => hthird t (le_trans h ht'E)) hcs' ht'len hunder hunderS
      (s₀ := (M.opening_slot S.hc (r + 1))) (s₁ := (M.opening_slot S.hc (r + 1 + 1)) - 1)
      hopos (hsE _ le_rfl) hsR hAB hpath' hbase
      (fun s _ _ m hm q hq => Restated.tick_outcome_of_tickStepAt facts S Sched x
        hexec.idealization.root_injective hexec.honestRootsNew hmono hm (facts.sch.vote_time_emod_delta S _)
        (Finset.mem_sdiff.2 ⟨Restated.awake_of_mem_HonSlot facts S Sched _ hq, fun h =>
          ((Restated.mem_HonSlot facts).mp hq).2.2
            (hmono _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E s) h)⟩)) (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›)
    exact hrange _ (by rw [hosucc]; exact Nat.le_add_right _ _) (le_of_eq hs1.symm)
  · have hrange := Restated.headsBelow_range_afterPhase (hr1 := Restated.one_le_round_of_of_opening_slot_le facts S (r := r + 1) (Nat.le_add_left 1 r) (Nat.le_succ _)) facts S Sched x hexec hsync hmult htd hmono hgst hcv
      (fun t h1 h2 => hphase t h1 (le_trans h2 ht'E))
      (fun t h => hthird t (le_trans h ht'E)) hcs' ht'len hunder hunderS
      (s₀ := (M.opening_slot S.hc (r + 1)) + 1) (s₁ := (M.opening_slot S.hc (r + 1 + 1)) - 1)
      (Nat.succ_pos _) (hsE _ (Nat.le_succ _)) hsR
      (fun s h0 h1 => hAB s (le_trans (Nat.le_succ _) h0) h1)
      (fun s h0 h1 => hpath' s (le_trans (Nat.le_succ _) h0) h1) hbase
      (fun s _ _ m hm q hq => Restated.tick_outcome_of_tickStepAt facts S Sched x
        hexec.idealization.root_injective hexec.honestRootsNew hmono hm (facts.sch.vote_time_emod_delta S _)
        (Finset.mem_sdiff.2 ⟨Restated.awake_of_mem_HonSlot facts S Sched _ hq, fun h =>
          ((Restated.mem_HonSlot facts).mp hq).2.2
            (hmono _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E s) h)⟩)) (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›)
    exact hrange _ (by rw [hosucc]; exact Nat.add_le_add_left (le_trans (by decide) hR3) _)
      (le_of_eq hs1.symm)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If `X` is a descendant of the anchor and an ancestor of the block a member of
    `HonRound S Sched r` names as confirmed in its round-`r` attestation, and `X` lies on one chain
    with every round-`(r + 1)` SG block, then every honest active member of round `(r + 2)`'s
    opening slot's committee votes there for a descendant of `X`. -/
theorem prevHeads_case_graded (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (hsync : Restated.SynchronyFromWake M S x) (hmult : AwakeAtMultiples S Sched)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE) (hcs : Restated.committeeSleepinessW M S Sched tE)
    {r : Round} {n n_W : Nat} {T : NamedBlock V}
    (hr : Restated.switchRound M S tE ≤ r + 1)
    (hJ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x (r + 1) n n_W T)
    {n' : Nat} (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1 + 1))))
    (hcross : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1 + 1))) →
      Restated.StepFinalizedCrossingUnderAnchor M S Sched x (r + 1) n'' T)
    (hJT : ∀ (v : V) (n₁ : Nat),
      M.vote_time S.E ((M.opening_slot S.hc (r + 1)) + 1) - 1 ≤ (x[n₁].time : Int) →
      n₁ ≤ n' + 1 → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J T.erase)
    {n_prev : Nat} (hnp : Restated.tickStepAt M x n_prev ((Restated.Vocabulary.Execution.Setup.a M S r)))
    {X : Block V} (hTX : Block.Preceq T.erase X)
    (hSG : ∀ v_1 ∈ Restated.HonRound M S Sched (r + 1), ∀ a : NamedAttestation V,
      a.round = r + 1 → a.val_index = v_1 →
      (⟨v_1, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n + 1].sent →
      ∀ G : NamedBlock V, G ∈ (x[n + 1][v_1].st).st.bodies → a.confirmed = some G.root →
      Block.compatible G.erase X = true)
    {v_2 : V} (hv_2 : v_2 ∈ Restated.HonRound M S Sched r) {a₂ : NamedAttestation V}
    (ha₂ : a₂.round = r) (hav₂ : a₂.val_index = v_2)
    (hsent₂ : (⟨v_2, NamedObject.attest a₂⟩ : SignedMsg V (NamedObject V)) ∈ x[n_prev + 1].sent)
    {G₀ : NamedBlock V} (hG₀ : G₀ ∈ (x[n_prev + 1][v_2].st).st.bodies)
    (hconf₂ : a₂.confirmed = some G₀.root) (hXG : Block.Preceq X G₀.erase) :
    Restated.HeadsBelow M S Sched x X ((M.opening_slot S.hc (r + 1 + 1))) := by
  have hinv := joint_toTop_phs hJ
  have hd := S.E.Δ_pos
  have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
  have hRd : 12 * S.E.Δ ≤ 4 * (S.hc.R : Int) * S.E.Δ := by nlinarith
  have hG0heads : Restated.HeadsBelow M S Sched x G₀.erase ((M.opening_slot S.hc (r + 1))) :=
    hJ.prevHeads n_prev hnp v_2 hv_2 a₂ ha₂ hav₂ hsent₂ G₀ hG₀ hconf₂
  have hbase := Restated.headsBelow_mono facts S Sched x hXG hG0heads
  obtain ⟨t', -, ht's, -, hcs'⟩ :=
    Restated.exists_cone_cutoff_at_opening facts S Sched tE hmono hcom tGAT gap hgst hlen hphase hcs hr
  have hmaj := Restated.majority_of_committeeSleepinessW facts S Sched hcs' (s := (M.opening_slot S.hc (r + 1)))
    (le_trans ht's (slotStart_mono S (Nat.le_succ _)))
  obtain ⟨w₀, hw₀⟩ : ((S.E.committee ((M.opening_slot S.hc (r + 1)))) ∩
      Restated.HonSlot M S Sched ((M.opening_slot S.hc (r + 1)))).Nonempty := by
    rw [Finset.inter_eq_right.2 (Restated.HonSlot_subset_committee facts S Sched _), ← Finset.card_pos]; omega
  have hw₀H := (Finset.mem_inter.mp hw₀).2
  obtain ⟨m₀, hm₀⟩ :=
    Restated.exists_tickStepAt facts x htd (facts.sch.vote_time_pos S (facts.gr.opening_slot_pos S (Nat.succ_pos r)))
  have hPG : ∀ v_3 ∈ Restated.HonRound M S Sched r, ∀ a₃ : NamedAttestation V,
      a₃.round = r → a₃.val_index = v_3 →
      (⟨v_3, NamedObject.attest a₃⟩ : SignedMsg V (NamedObject V)) ∈ x[n_prev + 1].sent →
      ∀ G : NamedBlock V, G ∈ (x[n_prev + 1][v_3].st).st.bodies → a₃.confirmed = some G.root →
      Block.compatible G.erase X = true :=
    fun v_3 hv_3 a₃ ha₃ hav₃ hsent₃ G hG hconf₃ =>
      compatible_of_compatible_of_preceq
        (Restated.compatible_of_headsBelow_common facts S Sched x
          (hJ.prevHeads n_prev hnp v_3 hv_3 a₃ ha₃ hav₃ hsent₃ G hG hconf₃) hG0heads hw₀H hm₀)
        hXG
  obtain ⟨hnp1, -⟩ := Restated.tickStepAt_time facts x hnp
  have hv_2A : v_2 ∉ Sched.adv ((Restated.Vocabulary.Execution.Setup.a M S r)) := (Finset.mem_sdiff.1 hv_2).2
  have hv_2h : Restated.HonestThrough M Sched x (n_prev + 1) v_2 := fun t ht hin =>
    hv_2A (hmono t _ (by rw [← hnp1]; exact ht) hin)
  have hopen := Restated.tGAT_add_two_rounds_le_opening facts S tGAT tE gap hgst hlen hr
  have hsucc := facts.gr.action_succ_eq_add_rounds S r
  have hA1 : (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) = M.opening S.E S.hc (r + 1) + 6 * S.E.Δ :=
      action_eq_opening_add_phs facts S (r + 1)
  have htGr : tGAT ≤ (x[n_prev + 1].time : Int) := by rw [hnp1]; linarith
  have hpath : ∀ s : Slot, (M.opening_slot S.hc (r + 1)) ≤ s →
      s + 1 ≤ (M.opening_slot S.hc (r + 1 + 1)) → Restated.ConeAnchorChainInTree M S x X s := by
    intro s h0 h1
    have hmo := slotStart_mono S h0
    -- `slotStart s + 3Δ ≤ view_freeze s`
    have hvf1 := slotStart_add_two_delta_le_support_cutoff_phs facts S s
    have hvf2 := support_cutoff_add_delta_le_view_freeze_phs facts S s
    have hco := Restated.confirmation_time_opening_slot facts S (r + 1)
    have hsc := facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E ((M.opening_slot S.hc (r + 1)))
    exact Restated.coneAnchorChainInTree_of_heldDescendant facts S Sched x tE hexec hmono htd hsync hmult tGAT
      gap hgst hlen hcv hthird hphase hrsW hcs hr hinv hcross hG₀ hv_2h htGr hXG hTX
      (by clear hA1 hopen; rw [hnp1]; linarith) (Nat.le_succ_of_le h1) (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›)
  exact Restated.headsBelow_nextOpening_of_base facts S Sched x tE hexec hmono htd hsync hmult hcom tGAT gap
    hgst hlen hcv hthird hphase hrsW hcs hr hJ hn' hcross hJT hnp hTX hSG hPG hpath
    (Or.inl rfl) hbase

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Every round at or after the switch round is positive. -/
theorem round_pos_of_switch (facts : Record.Facts M) (S : Setup V) (tGAT tE : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    {r : Round} (hr : Restated.switchRound M S tE ≤ r) : 0 < r :=
  pos_of_sum_nat_s2 _ _ _ _ _ _
    (le_trans (Restated.switchRound_ge_of_healingLengthη facts S tGAT tE gap hgst hlen) hr)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If round `r` is at or after the switch round and the joint invariant holds at round `r` with
    anchor `T`, then every round-`r` SG block of a member of `HonRound S Sched r`, named as
    confirmed by its round-`r` attestation, is an ancestor of every head voted at round `(r + 1)`'s
    opening slot. -/
theorem prevHeads_succ_afterPhase (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (hsync : Restated.SynchronyFromWake M S x) (hmult : AwakeAtMultiples S Sched)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE) (hcs : Restated.committeeSleepinessW M S Sched tE)
    {r : Round} {n n_W : Nat} {T : NamedBlock V}
    (hr : Restated.switchRound M S tE ≤ r)
    (hJ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x r n n_W T)
    {n' : Nat} (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    (hcross : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepFinalizedCrossingUnderAnchor M S Sched x r n'' T)
    (hJT : ∀ (v : V) (n₁ : Nat),
      M.vote_time S.E ((M.opening_slot S.hc r) + 1) - 1 ≤ (x[n₁].time : Int) →
      n₁ ≤ n' + 1 → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J T.erase) :
    ∀ v_1 ∈ Restated.HonRound M S Sched r, ∀ a : NamedAttestation V, a.round = r → a.val_index = v_1 →
      (⟨v_1, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n + 1].sent →
      ∀ C : NamedBlock V, C ∈ (x[n + 1][v_1].st).st.bodies → a.confirmed = some C.root →
      Restated.HeadsBelow M S Sched x C.erase ((M.opening_slot S.hc (r + 1))) := by
  obtain ⟨r₀, rfl⟩ : ∃ r₀ : Round, r = r₀ + 1 :=
    ⟨r - 1, (Nat.succ_pred_eq_of_pos (Restated.round_pos_of_switch facts S tGAT tE gap hgst hlen hr)).symm⟩
  intro v_1 hv_1 a ha hav hsent C hC hconf
  have hinv := joint_toTop_phs hJ
  have hn := hinv.tick
  obtain ⟨n_prev, hnp0⟩ := hJ.prevTick
  have hnp : Restated.tickStepAt M x n_prev ((Restated.Vocabulary.Execution.Setup.a M S r₀)) := hnp0
  have hd := S.E.Δ_pos
  have hd1 : (1 : Int) ≤ S.E.Δ := hd
  have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
  have hRd : 12 * S.E.Δ ≤ 4 * (S.hc.R : Int) * S.E.Δ := by nlinarith
  obtain ⟨hn1, hn0⟩ := Restated.tickStepAt_time facts x hn
  have hv_1A : v_1 ∉ Sched.adv ((Restated.Vocabulary.Execution.Setup.a M S (r₀ + 1))) := (Finset.mem_sdiff.1 hv_1).2
  have hv_1n1 : Restated.HonestThrough M Sched x (n + 1) v_1 := fun t ht hin =>
    hv_1A (hmono t _ (by rw [← hn1]; exact ht) hin)
  have hv_1n : Restated.HonestThrough M Sched x n v_1 := fun t ht =>
    hv_1n1 t (le_trans ht (Restated.time_mono_int facts S Sched x (Nat.le_succ n)))
  have hfin := Restated.fin_old_anchor_before_succ_tick_of_hypotheses facts (hcross := hcross) S Sched x tE hexec
    hmono tGAT gap hgst hlen hthird hphase hrsW hr hinv hn'
  have hnn' : n ≤ n' := Restated.tick_le_of_round_le facts S Sched x hn hn' (Nat.le_succ _)
  have hvt1 : M.vote_time S.E ((M.opening_slot S.hc (r₀ + 1)) + 1) = (Restated.Vocabulary.Execution.Setup.a M S (r₀ + 1)) - S.E.Δ := by
    have h := Restated.vote_time_opening_slot_add facts S (r₀ + 1) 1
    rw [h]; push_cast; ring
  have hJn : Block.Preceq (x[n][v_1].st).st.core.J T.erase :=
    hJT v_1 n (by rw [hvt1]; linarith) (Nat.le_succ_of_le hnn') hv_1n
  have hFn : Block.Preceq (x[n][v_1].st).st.core.F T.erase := hfin v_1 n hnn' hv_1n
  have hjust : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r₀ + 1 + 1))) →
      Restated.StepJustifiedRootUnderAnchor M S Sched x (r₀ + 1) n n'' T := by
    intro n'' hn'' v n₁ h1 h2 hvh _ _
    have heq : n'' = n' := Restated.tickStepAt_unique facts x hn'' hn'
    subst heq
    have htm := Restated.time_mono_int facts S Sched x h1
    exact hJT v n₁ (by rw [hvt1]; linarith) (Nat.le_succ_of_le h2) hvh
  have hTheads := Restated.headsBelow_succ_opening_slot_at_anchor facts S Sched x tE hexec hmono htd hsync hmult
    hcom tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr hinv hcross hjust hn'
    (fun s _ _ m hm q hq => Restated.tick_outcome_of_tickStepAt facts S Sched x
        hexec.idealization.root_injective hexec.honestRootsNew hmono hm (facts.sch.vote_time_emod_delta S _)
        (Finset.mem_sdiff.2 ⟨Restated.awake_of_mem_HonSlot facts S Sched _ hq, fun h =>
          ((Restated.mem_HonSlot facts).mp hq).2.2
            (hmono _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E s) h)⟩)) (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›)
    (fun v_2 hv_2 => Restated.tick_outcome_of_tickStepAt facts S Sched x
      hexec.idealization.root_injective hexec.honestRootsNew hmono hn (Restated.action_emod_delta facts S _)
      (Finset.mem_sdiff.2 ⟨Restated.awake_action_of_mem_honRound facts hv_2, (Finset.mem_sdiff.1 hv_2).2⟩))
  have hdone : Block.Preceq C.erase T.erase →
      Restated.HeadsBelow M S Sched x C.erase ((M.opening_slot S.hc (r₀ + 1 + 1))) :=
    fun h => Restated.headsBelow_mono facts S Sched x h hTheads
  have hsg := hinv.sg v_1 hv_1 a ha hav hsent C hC hconf
  rcases compatible_cases hsg with hCT | hTC
  · exact hdone hCT
  obtain ⟨nr, hnr⟩ := actionReadFrom_nonempty_phs facts (Setup.alwaysAwake S) (x[n][v_1].st) (r₀ + 1)
  obtain ⟨g, hg⟩ := frameGradeRead_nonempty_phs facts nr.cache S.E S.hc (M.toHealing nr.st.core)
    (r₀ + 1)
  have hhs : M.toHealing nr.st.core ∈ Restated.actionHealingStore M S (x[n][v_1].st) (r₀ + 1) :=
    ⟨nr, hnr, rfl⟩
  have hfr : M.readFrame nr.cache (M.toHealing nr.st.core) (r₀ + 1)
      ∈ Restated.actionFrame M S (x[n][v_1].st) (r₀ + 1) := ⟨nr, hnr, rfl⟩
  have hCeq := Restated.freshSG_erase_eq_sgVote facts S Sched x hexec hn hv_1n1 ha hav hsent hC
    hconf nr hnr g hg
  have hFa : Block.Preceq (M.toHealing nr.st.core).F T.erase := by
    rw [Restated.actionHealingStore_F facts S _ _ _ hhs]; exact hFn
  have hJa : Block.Preceq (M.toHealing nr.st.core).J T.erase := by
    rw [Restated.actionHealingStore_J facts S _ _ _ hhs]; exact hJn
  have hSG : ∀ v' ∈ Restated.HonRound M S Sched (r₀ + 1), ∀ a' : NamedAttestation V,
      a'.round = r₀ + 1 → a'.val_index = v' →
      (⟨v', NamedObject.attest a'⟩ : SignedMsg V (NamedObject V)) ∈ x[n + 1].sent →
      ∀ G : NamedBlock V, G ∈ (x[n + 1][v'].st).st.bodies → a'.confirmed = some G.root →
      Block.compatible G.erase C.erase = true :=
    fun v' hv' a' ha' hav' hsent' G hG hconf' =>
      hinv.sgPairwise v' hv' v_1 hv_1 a' a ha' hav' hsent' ha hav hsent G C hG hconf' hC hconf
  have hopen := Restated.tGAT_add_two_rounds_le_opening facts S tGAT tE gap hgst hlen hr
  have hlo : tGAT ≤ slotStart S.E.Δ ((M.opening_slot S.hc (r₀ + 1))) := by
    rw [← opening_eq_slotStart_phs facts S]; nlinarith
  have hosucc := facts.gr.opening_slot_succ S.hc (r₀ + 1)
  have hjslot : ∀ s : Slot, s + 1 ≤ (M.opening_slot S.hc (r₀ + 1 + 1)) →
      s + 1 ≤ (M.opening_slot S.hc (r₀ + 1 + 1)) + 1 := fun s h => Nat.le_succ_of_le h
  rcases Restated.sgVote_directed_cases facts S (x[n][v_1].st) (r₀ + 1) nr hnr g hg with
      hL | ⟨root, hroot, hpre⟩ | ⟨root, hroot, hpre⟩ | hfg
  · -- case 2: `C` is an ancestor of `v_1`'s confirmed block
    rw [← hCeq] at hL
    have hct : M.confirmation_time S.E ((M.opening_slot S.hc (r₀ + 1))) = (Restated.Vocabulary.Execution.Setup.a M S (r₀ + 1)) :=
      Restated.confirmation_time_opening_slot facts S (r₀ + 1)
    have hnc : Restated.tickStepAt M x n (M.confirmation_time S.E ((M.opening_slot S.hc (r₀ + 1)))) := by
      rw [hct]; exact hn
    have hqaw := Restated.honRound_awakeThroughout_confirmation facts S Sched (r₀ + 1) hv_1
    have hqh : HonestThroughTime Sched
        (M.confirmation_time S.E ((M.opening_slot S.hc (r₀ + 1)))) v_1 :=
      fun t' ht' hin => hv_1A (hmono _ _ (by rw [← hct]; exact ht') hin)
    have hPG : ∀ v_2 ∈ Restated.HonRound M S Sched r₀, ∀ a₂ : NamedAttestation V,
        a₂.round = r₀ → a₂.val_index = v_2 →
        (⟨v_2, NamedObject.attest a₂⟩ : SignedMsg V (NamedObject V)) ∈ x[n_prev + 1].sent →
        ∀ G : NamedBlock V, G ∈ (x[n_prev + 1][v_2].st).st.bodies → a₂.confirmed = some G.root →
        Block.compatible G.erase C.erase = true :=
      fun v_2 hv_2 a₂ ha₂ hav₂ hsent₂ G hG hconf₂ =>
        compatible_of_compatible_of_preceq
          (hJ.prevConfirmed n_prev hnp v_1 hv_1 v_2 hv_2 a₂ ha₂ hav₂ hsent₂ G hG hconf₂ _ hhs) hL
    have hcases := actionHealingStore_live_confirmed_cases_phs facts S (x[n][v_1].st) (r₀ + 1) _ hhs
    rw [Restated.slotOf_a_sub_one facts S (r₀ + 1)] at hcases
    rcases hcases with ⟨el, hel', hel⟩ | hroot
    · have hpath : ∀ s : Slot, (M.opening_slot S.hc (r₀ + 1)) ≤ s →
          s + 1 ≤ (M.opening_slot S.hc (r₀ + 1 + 1)) → Restated.ConeAnchorChainInTree M S x C.erase s :=
        fun s h0 h1 => Restated.coneAnchorChainInTree_of_eligibleConfirmation_later facts S Sched x tE hexec
          hmono htd hsync hmult tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr hinv hcross hqaw
          hqh el hel' hel hL hTC hlo h0 (hjslot s h1)
      have hAB := Restated.coneAnchorCompatible_roundSlots_ofSG facts S Sched x tE hexec hmono htd hsync hmult
        tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr hJ hn' hcross hJT hnp hTC hSG hPG
      have hopos : 0 < (M.opening_slot S.hc (r₀ + 1)) := facts.gr.opening_slot_pos S (Nat.succ_pos r₀)
      have hsR : M.view_freeze S.E ((M.opening_slot S.hc (r₀ + 1))) ≤ (Restated.Vocabulary.Execution.Setup.a M S (r₀ + 1 + 1)) - 1 := by
        have hsucc := facts.gr.action_succ_eq_add_rounds S (r₀ + 1)
        have e1 := facts.sch.view_freeze_lt_vote_time_succ S.E ((M.opening_slot S.hc (r₀ + 1)))
        have e3 := facts.sch.slotStart_add_delta_eq_vote_time S.E ((M.opening_slot S.hc (r₀ + 1)) + 1)
        have e4 := slotStart_succ S.E.Δ ((M.opening_slot S.hc (r₀ + 1)))
        have e2 : M.confirmation_time S.E ((M.opening_slot S.hc (r₀ + 1)))
            = slotStart S.E.Δ ((M.opening_slot S.hc (r₀ + 1))) + 6 * S.E.Δ := (facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E _).symm
        rw [hct] at e2
        rw [hsucc]; linarith
      have hle0 : (M.opening_slot S.hc (r₀ + 1)) ≤ (M.opening_slot S.hc (r₀ + 1 + 1)) - 1 := by
        rw [hosucc]
        exact Nat.le_sub_of_add_le (Nat.add_le_add_left (le_trans (by decide) S.hc.R_ge_three) _)
      have hle1' : (M.opening_slot S.hc (r₀ + 1)) + 1 ≤ (M.opening_slot S.hc (r₀ + 1 + 1)) := by
        rw [hosucc]; exact Nat.add_le_add_left (le_trans (by decide) S.hc.R_ge_three) _
      have hbase := Restated.headsBelow_succ_of_eligible_afterPhase facts S Sched x hexec hsync hmult htd hmono
        (tR := (Restated.Vocabulary.Execution.Setup.a M S (r₀ + 1 + 1)) - 1) hgst hcv hphase hthird hcs
        (Restated.delta_le_of_healingLengthη facts S hlen)
        (Restated.deliveredDescendantUnderFinalized_anchor facts S Sched x hn' hfin tGAT)
        (Restated.finalizedPreceqAtSteps_anchor facts S Sched x hn' hfin tGAT) hTC hL hopos hlo hsR
        hnc hqaw hqh el hel' hel (hAB _ le_rfl hle0) (hpath _ le_rfl hle1')
        (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›) (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›)
      exact Restated.headsBelow_nextOpening_of_base facts S Sched x tE hexec hmono htd hsync hmult hcom tGAT gap
        hgst hlen hcv hthird hphase hrsW hcs hr hJ hn' hcross hJT hnp hTC hSG hPG hpath
        (Or.inr rfl) hbase
    · rw [hroot] at hL
      have hroot' := Restated.confRoot_setClock_preceq_ofAction facts S (x[n][v_1].st) r₀ _ hhs hFa
        (fun _ => hJa)
      rw [hct] at hroot'
      exact hdone (preceq_trans_Preceq hL hroot')
  · -- case 3: `C` is an ancestor of a grade-1 root of the action frame
    rw [← hCeq] at hpre
    obtain ⟨m, B, hm, hB, hrootB⟩ :=
      Restated.actionFrame_g1_provenance facts S Sched x hn v_1 root _ hfr hroot
    obtain ⟨b, hb⟩ := facts.gr.gradeBool_nonempty S.E (M.gradeView (M.toHealing (x[m][v_1].st).st.core))
      (x[m][v_1].st).st.core.F S.hc.η_SG (r₀ + 1) (M.early S.E S.hc (r₀ + 1) .g1)
      (M.late S.E S.hc (r₀ + 1) .g1) B
    obtain ⟨v_2, hv_2, a₂, ha₂, hav₂, hsent₂, G₀, hG₀, hconf₂, hBG⟩ :=
      hJ.gradedUnderPrevSGPerformers n_prev hnp v_1 (Restated.mem_grade1PerformersW_of_honRound facts S Sched hmono hv_1) m hm B
        b hb (hB b hb)
    exact Restated.prevHeads_case_graded facts S Sched x tE hexec hmono htd hsync hmult hcom tGAT gap hgst hlen
      hcv hthird hphase hrsW hcs hr hJ hn' hcross hJT hnp hTC hSG hv_2 ha₂ hav₂ hsent₂
      hG₀ hconf₂ (preceq_trans_Preceq hpre (preceq_trans_Preceq hrootB hBG))
  · -- case 3: `C` is an ancestor of a grade-2 root of the action frame
    rw [← hCeq] at hpre
    obtain ⟨m, B, hm, hB, hrootB⟩ :=
      Restated.actionFrame_g2_provenance facts S Sched x hn v_1 root _ hfr hroot
    obtain ⟨b, hb⟩ := facts.gr.gradeBool_nonempty S.E (M.gradeView (M.toHealing (x[m][v_1].st).st.core))
      (x[m][v_1].st).st.core.F S.hc.η_SG (r₀ + 1) (M.early S.E S.hc (r₀ + 1) .g2)
      (M.late S.E S.hc (r₀ + 1) .g2) B
    obtain ⟨v_2, hv_2, a₂, ha₂, hav₂, hsent₂, G₀, hG₀, hconf₂, hBG⟩ :=
      hJ.gradedUnderPrevSG n_prev hnp v_1 hv_1 .g2 (by decide) (facts.gr.domain_le_action S (r₀ + 1) .g2) m hm B
        b hb (hB b hb)
    exact Restated.prevHeads_case_graded facts S Sched x tE hexec hmono htd hsync hmult hcom tGAT gap hgst hlen
      hcv hthird hphase hrsW hcs hr hJ hn' hcross hJT hnp hTC hSG hv_2 ha₂ hav₂ hsent₂
      hG₀ hconf₂ (preceq_trans_Preceq hpre (preceq_trans_Preceq hrootB hBG))
  · -- case 1: `C` is the fork-choice root of the action read
    rw [← hCeq] at hfg
    refine hdone ?_
    rw [hfg]
    exact facts.fc.fgRoot_preceq hFa hJa

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- `prevHeads_succ_afterPhase` for a round strictly after the switch round, with the justified
    blocks bounded from the switch step on: every round-`r` SG block of an honest active attester of
    round `r` is an ancestor of every head voted at round `(r + 1)`'s opening slot. -/
theorem prevHeads_succ_afterPhase_ofAfterSwitch (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (hsync : Restated.SynchronyFromWake M S x) (hmult : AwakeAtMultiples S Sched)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE) (hcs : Restated.committeeSleepinessW M S Sched tE)
    {n_W : Nat} (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    {r : Round} {n : Nat} {T : NamedBlock V}
    (hr : Restated.switchRound M S tE + 1 ≤ r)
    (hJ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x r n n_W T)
    {n' : Nat} (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    (hcross : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepFinalizedCrossingUnderAnchor M S Sched x r n'' T)
    (hJTW : ∀ (v : V) (n₁ : Nat), n_W ≤ n₁ → n₁ ≤ n' + 1 → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J T.erase) :
    ∀ v_1 ∈ Restated.HonRound M S Sched r, ∀ a : NamedAttestation V, a.round = r → a.val_index = v_1 →
      (⟨v_1, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n + 1].sent →
      ∀ C : NamedBlock V, C ∈ (x[n + 1][v_1].st).st.bodies → a.confirmed = some C.root →
      Restated.HeadsBelow M S Sched x C.erase ((M.opening_slot S.hc (r + 1))) := by
  obtain ⟨r₀, rfl⟩ : ∃ r₀ : Round, r = r₀ + 1 :=
    ⟨r - 1, (Nat.succ_pred_eq_of_pos (pos_of_succ_le_s2 _ _ hr)).symm⟩
  have hrW : Restated.switchRound M S tE ≤ r₀ := Nat.le_of_succ_le_succ hr
  refine Restated.prevHeads_succ_afterPhase facts S Sched x tE hexec hmono htd hsync hmult hcom tGAT gap hgst hlen
    hcv hthird hphase hrsW hcs (le_trans hrW (Nat.le_succ r₀)) hJ hn' hcross ?_
  intro v n₁ hlo hhi hvh
  refine hJTW v n₁ ?_ hhi hvh
  have hd := S.E.Δ_pos
  have hvt1 : M.vote_time S.E ((M.opening_slot S.hc (r₀ + 1)) + 1) = (Restated.Vocabulary.Execution.Setup.a M S (r₀ + 1)) - S.E.Δ := by
    have h := Restated.vote_time_opening_slot_add facts S (r₀ + 1) 1
    rw [h]; push_cast; ring
  have hsucc := facts.gr.action_succ_eq_add_rounds S r₀
  have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
  have hmonoA := Restated.action_mono facts S hrW
  obtain ⟨hnW1, -⟩ := Restated.tickStepAt_time facts x hnW
  by_contra hcon
  have hle : n₁ ≤ n_W + 1 := Nat.le_succ_of_le (Nat.le_of_lt (Nat.lt_of_not_le hcon))
  have ht := Restated.time_mono_int facts S Sched x hle
  rw [hnW1] at ht
  rw [hvt1] at hlo
  have hd1 : (1 : Int) ≤ S.E.Δ := hd
  have hRd : 12 * S.E.Δ ≤ 4 * (S.hc.R : Int) * S.E.Δ := by nlinarith
  linarith

end

end DecoupledConsensusModel.Sts.Restated
