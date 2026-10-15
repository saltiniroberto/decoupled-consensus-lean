import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bInvariantActive
import Proofs.Claims.Restated.Claim13bK_ConeAnchor
import Proofs.Claims.Restated.Claim13bK_ConeSlots
import Proofs.Claims.Restated.Claim13bK_ConfirmedNew
import Proofs.Claims.Restated.Claim13bK_ConfirmedSettle
import Proofs.Claims.Restated.Claim13bK_FgJustified
import Proofs.Claims.Restated.Claim13bK_FinBeforeTick
import Proofs.Claims.Restated.Claim13bK_Frame
import Proofs.Claims.Restated.Claim13bK_FrameNew
import Proofs.Claims.Restated.Claim13bK_GradeOldHeads
import Proofs.Claims.Restated.Claim13bK_HeadsNewAnchor
import Proofs.Claims.Restated.Claim13bK_HeadsNewAnchorJoint
import Proofs.Claims.Restated.Claim13bK_HolderMargins
import Proofs.Claims.Restated.Claim13bK_LiveConfirmedSlots
import Proofs.Claims.Restated.Claim13bK_PrevHeadsStep
import Proofs.Claims.Restated.Claim13bStepActionF
import Proofs.Claims.Restated.Claim13bStepCone
import Proofs.Claims.Restated.Claim13bStepConeIter
import Proofs.Claims.Restated.Claim13bStepFin
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bW_Schedule
import Proofs.Claims.Restated.Claim13beRoute3_3
import Proofs.Claims.Restated.Claim13beRoute3_82
import Proofs.Claims.Restated.CommonViewOfFinalizedDescendantsFacts
import Proofs.Claims.Restated.Vocabulary_Execution_HealthyLocalFacts
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActive
import Model.Conditions.Claim13bInvariantActiveJoint
import Model.Conditions.Claim13bInvariantActiveSinceW
import Model.Conditions.Claim13bInvariantActiveTop
import Model.Conditions.Claim13bK_ConeAnchor
import Model.Conditions.Claim13bK_ConeSlots
import Model.Conditions.Claim13bK_ConfirmedSettle
import Model.Conditions.Claim13bK_FinBeforeTick
import Model.Conditions.Claim13bK_LiveConfirmedSlots
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13bStepCone
import Model.Conditions.Claim13bStepConeIter
import Model.Conditions.Claim13bStepSG
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_5
import Model.Conditions.Claim13beRoute3_7
import Model.Conditions.Claim13beRoute3_74
import Model.Conditions.Claim13beRoute3_83
import Model.Conditions.CommonViewOfFinalizedDescendantsFacts
import Model.Conditions.RunAll
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13bd
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Sts_Spec2Claims_Claim13bf
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_Grades_Main
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bK_HeadsPersist
import Proofs.Claims.Restated.Claim13bInvariantGrade1RuleFacts

/-!
# Persistence of the honest heads across rounds

After the phase, the descendants of the round anchor that the honest heads of a slot descend from
stay ancestors of every later honest head, round after round, stated over a model
`M : Record.Model V` and its facts `facts : Record.Facts M`.
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

/-- The successors of the slots from a round's opening slot to the next round's opening slot are the
    round's later slots and the next round's first two slots. -/
private theorem succ_slot_cases_hp (a R s : Nat) (h0 : a ≤ s) (h1 : s ≤ a + R) :
    (∃ j : Nat, 1 ≤ j ∧ j < R ∧ s + 1 = a + j) ∨ (∃ j : Nat, j ≤ 1 ∧ s + 1 = a + R + j) := by
  by_cases h : s + 1 < a + R
  · exact Or.inl ⟨s + 1 - a, by omega, by omega, by omega⟩
  · exact Or.inr ⟨s + 1 - (a + R), by omega, by omega⟩

/-- A round opens at the start of its opening slot. -/
private theorem opening_eq_slotStart_hp (facts : Record.Facts M) (S : Setup V) (r : Round) :
    M.opening S.E S.hc r = slotStart S.E.Δ (M.opening_slot S.hc r) :=
  (facts.gr.opening_eq_proposal_time S.E S.hc r).trans
    (facts.sch.Γ_0_eq_proposal_time S.hc S.E r).symm

/-- A round's action instant is six delays after its opening. -/
private theorem action_eq_opening_add_hp (facts : Record.Facts M) (S : Setup V) (r : Round) :
    Restated.Vocabulary.Execution.Setup.a M S r = M.opening S.E S.hc r + 6 * S.E.Δ := by
  have h1 : Restated.Vocabulary.Execution.Setup.a M S r
      = M.confirmation_time S.E (M.opening_slot S.hc r) :=
    facts.sch.a_eq_confirmation_time S.hc S.E r
  have h2 := facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E (M.opening_slot S.hc r)
  rw [h1, opening_eq_slotStart_hp facts S r]
  linarith

/-- For every slot `s`, `slotStart s + 2Δ ≤ support_cutoff s`. -/
private theorem slotStart_add_two_delta_le_support_cutoff_hp (facts : Record.Facts M)
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
private theorem support_cutoff_add_delta_le_view_freeze_hp (facts : Record.Facts M)
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

/-- The joint invariant at round `r`, step `n`, switch step `n_W` and anchor `T` gives
    `AfterPhaseInvariantOverActiveSetsTop` at `r`, `n` and `T`. -/
private theorem joint_toTop_hp {S : Setup V} {Sched : Schedule V}
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
private theorem returns_map_intro_hp {α β : Type} (f : α → β) (m : DC.NDRE α) (a : α)
    (h : m ⇢ a) : (f <$> m) ⇢ f a := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image]
  exact ⟨_, h, rfl⟩

open scoped DC in
/-- `m >>= k` can return `b` exactly when `m` can return some `a` from which `k a` can return `b`. -/
private theorem returns_bind_iff_hp {α β : Type} (m : DC.NDRE α) (k : α → DC.NDRE β) (b : β) :
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
private theorem returns_lift_iff_hp {α : Type} (s : Set α) (a : α) :
    (ExceptT.lift s : DC.NDRE α) ⇢ a ↔ a ∈ s := by
  unfold Record.Returns
  simp only [ExceptT.run_lift, Set.fmap_eq_image, Set.mem_image]
  constructor
  · rintro ⟨a', ha', he⟩
    cases he
    exact ha'
  · intro h
    exact ⟨a, h, rfl⟩

/-- The slot-`s` eligibility test of every store has an outcome. -/
private theorem confEligible_nonempty_hp (facts : Record.Facts M) (E : Env V) (st : M.S)
    (s : Slot) : ∃ el : Block V → Bool, Restated.Vocabulary.Protocol.confEligible M E st s ⇢ el := by
  obtain ⟨tm, htm⟩ := facts.sto.tau_nonempty st
  have hvv : Restated.Vocabulary.Protocol.confVotes M E st s ⇢
      (beforeCutoff tm (M.support_cutoff E s) (st.pool s)).filter
        (fun u => M.no_second_vote_in (Restated.Vocabulary.Protocol.confLate M E st s) u = true) :=
    returns_map_intro_hp _ _ _ (returns_map_intro_hp _ _ _ htm)
  obtain ⟨sc, hsc⟩ : ∃ sc : Block V → Nat, ∀ B, M.goldfish_score E st.T
      ((beforeCutoff tm (M.support_cutoff E s) (st.pool s)).filter
        (fun u => M.no_second_vote_in (Restated.Vocabulary.Protocol.confLate M E st s) u = true))
      ((beforeCutoff tm (M.support_cutoff E s) (st.pool s)).filter
        (fun u => M.no_second_vote_in (Restated.Vocabulary.Protocol.confLate M E st s) u = true))
      s B ⇢ sc B :=
    ⟨fun B => (facts.fc.goldfish_score_nonempty _ _ _ _ _ B).choose,
      fun B => (facts.fc.goldfish_score_nonempty _ _ _ _ _ B).choose_spec⟩
  refine ⟨fun B => decide (Restated.Vocabulary.Protocol.confCount M E st s < 2 * sc B), ?_⟩
  unfold Restated.Vocabulary.Protocol.confEligible
  refine (returns_bind_iff_hp _ _ _).2 ⟨_, hvv, ?_⟩
  refine (returns_bind_iff_hp _ _ _).2 ⟨sc, (returns_lift_iff_hp _ _).2 hsc, ?_⟩
  exact (Record.returns_pure _ _).2 rfl

/-- The round-`r` action read computed from `before` gives some node state. -/
private theorem actionReadFrom_nonempty_hp (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∃ n, n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r := by
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc (M.toHealing before.st.core)
    (Restated.Vocabulary.Execution.Setup.a M S r) before.cache
  obtain ⟨st, hst⟩ := facts.dt.duties_update_confirmation_with_nonempty (M.gradeContract c) S.E
    S.hc (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r))
    (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1)
  exact ⟨_, c, hc, st, hst, rfl⟩

/-- The frame grade read of every cache at every healing store and round has an outcome. -/
private theorem frameGradeRead_nonempty_hp (facts : Record.Facts M) (c : M.Cache) (E : Env V)
    (hc : Protocol.HealConfig) (st : M.HS) (r : Round) :
    ∃ g, M.frameGradeRead c E hc st r ⇢ g := by
  obtain ⟨g, hg⟩ := facts.gr.read_nonempty (M.gradeContract c) E hc st r
  exact ⟨g, (facts.nd.gradeContract_read c E hc st r g).1 hg⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If the committee majority `committeeSleepinessW` holds from `t'`, `t'` is at or before the start
    of slot `s + 1`, slot `s` is positive, and every honest active member of slot `s`'s committee
    votes there for a descendant of `A` and for a descendant of `B`, then `A` and `B` lie on one
    chain. -/
theorem compatible_of_headsBelow_after (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (htd : Restated.TimeDiverges M x) {t' : Int}
    (hcs' : Restated.committeeSleepinessW M S Sched t') {s : Slot} (hs : 0 < s)
    (ht' : t' ≤ slotStart S.E.Δ (s + 1)) {A B : Block V}
    (hA : Restated.HeadsBelow M S Sched x A s) (hB : Restated.HeadsBelow M S Sched x B s) :
    Block.compatible A B = true := by
  have hmaj := Restated.majority_of_committeeSleepinessW facts S Sched hcs' (s := s) ht'
  obtain ⟨w₀, hw₀⟩ : ((S.E.committee s) ∩ Restated.HonSlot M S Sched s).Nonempty := by
    rw [Finset.inter_eq_right.2 (Restated.HonSlot_subset_committee facts S Sched _), ← Finset.card_pos]; omega
  obtain ⟨m₀, hm₀⟩ := Restated.exists_tickStepAt facts x htd (facts.sch.vote_time_pos S hs)
  exact Restated.compatible_of_headsBelow_common facts S Sched x hA hB (Finset.mem_inter.mp hw₀).2 hm₀

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If the joint invariant holds at round `r + 1` with anchor `T`, `T` is an ancestor of `Y`, and
    `Y` lies on one chain with the honest round-`r` SG blocks that are descendants of `T` and with
    every honest round-`(r + 1)` SG block, then `ConeAnchorCompatible S x Y s` holds at every slot
    `s` from round `(r + 1)`'s opening slot to round `(r + 2)`'s opening slot. -/
theorem coneAnchorCompatible_roundSlots_above (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
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
    {Y : Block V} (hTY : Block.Preceq T.erase Y)
    (hGY : ∀ v_2 ∈ Restated.HonRound M S Sched r, ∀ a : NamedAttestation V,
      a.round = r → a.val_index = v_2 →
      (⟨v_2, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n_prev + 1].sent →
      ∀ G : NamedBlock V, G ∈ (x[n_prev + 1][v_2].st).st.bodies → a.confirmed = some G.root →
      Block.Preceq T.erase G.erase → Block.compatible G.erase Y = true)
    (hCY : ∀ v_1 ∈ Restated.HonRound M S Sched (r + 1), ∀ a : NamedAttestation V,
      a.round = r + 1 → a.val_index = v_1 →
      (⟨v_1, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n + 1].sent →
      ∀ C : NamedBlock V, C ∈ (x[n + 1][v_1].st).st.bodies → a.confirmed = some C.root →
      Block.compatible C.erase Y = true)
    (hrecvR : Restated.NextRoundReceipts M S Sched x (r + 1)) :
    ∀ s : Slot, (M.opening_slot S.hc (r + 1)) ≤ s → s ≤ (M.opening_slot S.hc (r + 1 + 1)) →
      Restated.ConeAnchorCompatible M S x Y s := by
  have hinv := joint_toTop_hp hJ
  have hd := S.E.Δ_pos
  have hR3 : 3 ≤ S.hc.R := S.hc.R_ge_three
  have hosucc := facts.gr.opening_slot_succ S.hc (r + 1)
  intro s h0 h1
  have hvlo : M.vote_time S.E ((M.opening_slot S.hc (r + 1)) + 1)
      ≤ M.vote_time S.E (s + 1) :=
    facts.sch.vote_time_mono S.E (Nat.succ_le_succ h0)
  have hvhi : M.vote_time S.E (s + 1) < (Restated.Vocabulary.Execution.Setup.a M S (r + 1 + 1)) := by
    have hm : M.vote_time S.E (s + 1)
        ≤ M.vote_time S.E ((M.opening_slot S.hc (r + 1 + 1)) + 1) :=
      facts.sch.vote_time_mono S.E (Nat.succ_le_succ h1)
    have e := Restated.vote_time_opening_slot_add facts S (r + 1 + 1) 1
    push_cast at e
    rw [e] at hm; linarith
  have hFJ := Restated.voteFinJust_preceq_at_later_slots facts S Sched x tE hexec hmono tGAT gap hgst hlen
    hthird hphase hrsW hr hinv hcross hn' hJT hvlo hvhi
  refine Restated.coneAnchorCompatible_of_voteReads facts S x ?_ (Restated.voteFinJustCompatible_of_preceq facts S x hFJ hTY)
  rw [hosucc] at h1
  rcases succ_slot_cases_hp _ _ _ h0 h1 with ⟨j, hj1, hjR, hsj⟩ | ⟨j, hj1, hsj⟩
  · intro v mr hv hmr nd hnd root hroot
    obtain ⟨m, B, hm, hB, hpre⟩ :=
      Restated.voteFrame_g1_provenance facts S Sched x hmr v root hnd hroot
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
      hJ.gradedUnderPrevSGPerformers n_prev hnp v hvP m hm B
        b hb (hB b hb)
    have hBT := hinv.grade1Performers v hvP m hm B b hb (hB b hb)
    rcases compatible_cases hBT with hBT | hTB
    · exact compatible_of_preceq_c2b
        (preceq_trans_Preceq hpre (preceq_trans_Preceq hBT hTY))
    · exact Protocol.compatible_of_preceq_of_compatible (preceq_trans_Preceq hpre hBG)
        (hGY v_2 hv_2 a ha hai hsent G hG hconf (preceq_trans_Preceq hTB hBG))
  · have hsj' : s + 1 = (M.opening_slot S.hc (r + 1 + 1)) + j := by rw [hosucc]; exact hsj
    exact Restated.voteGradeOneCompatible_of_gradedCompatible_rule facts S Sched x hmono (r := r + 1) (D := Y)
      (Restated.graded_compatible_of_sgCompatible (hrecvR := hrecvR) facts S Sched x tE hexec hmono htd hsync hmult tGAT gap hgst
        hlen hcv hthird hphase hrsW hcs hr hinv hcross (preceq_eq_true_iff_Preceq.mp (Block.preceq_self Y)) hCY
        )
      (j := j) (by omega) hsj'

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If `AfterPhaseInvariantOverActiveSetsTop` holds at round `r + 1` with anchor `T`, `T` is an
    ancestor of `Y`, the two anchor facts hold at `Y`, and every honest active member of slot `s₀`'s
    committee votes for a descendant of `Y`, then the same holds at every slot from `s₀` to round
    `(r + 2)`'s second slot. -/
theorem headsBelow_roundRange_above (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
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
    {r : Round} {n : Nat} {T : NamedBlock V}
    (hr : Restated.switchRound M S tE ≤ r + 1)
    (hinv : Restated.AfterPhaseInvariantOverActiveSetsTop M S Sched x (r + 1) n T)
    {n' : Nat} (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1 + 1))))
    (hcross : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1 + 1))) →
      Restated.StepFinalizedCrossingUnderAnchor M S Sched x (r + 1) n'' T)
    {Y : Block V} (hTY : Block.Preceq T.erase Y)
    (hAB : ∀ s : Slot, (M.opening_slot S.hc (r + 1)) ≤ s → s ≤ (M.opening_slot S.hc (r + 1 + 1)) →
      Restated.ConeAnchorCompatible M S x Y s)
    {s₀ : Slot}
    (hpath : ∀ s : Slot, s₀ ≤ s → s ≤ (M.opening_slot S.hc (r + 1 + 1)) →
      Restated.ConeAnchorChainInTree M S x Y s)
    (hs0 : (M.opening_slot S.hc (r + 1)) ≤ s₀)
    (hbase : Restated.HeadsBelow M S Sched x Y s₀) :
    ∀ s : Slot, s₀ ≤ s → s ≤ (M.opening_slot S.hc (r + 1 + 1)) + 1 → Restated.HeadsBelow M S Sched x Y s := by
  have hd := S.E.Δ_pos
  have hd1 : (1 : Int) ≤ S.E.Δ := hd
  obtain ⟨t', ht'E, ht's, ht'len, hcs'⟩ :=
    Restated.exists_cone_cutoff_at_opening facts S Sched tE hmono hcom tGAT gap hgst hlen hphase hcs hr
  have hfin := Restated.fin_old_anchor_before_succ_tick_of_hypotheses facts (hcross := hcross) S Sched x tE hexec
    hmono tGAT gap hgst hlen hthird hphase hrsW hr hinv hn'
  have hunder := Restated.deliveredDescendant_mono facts S Sched x
    (Restated.deliveredDescendantUnderFinalized_anchor facts S Sched x hn' hfin tGAT) hTY
  have hunderS := Restated.finalizedPreceqAtSteps_mono facts S Sched x
    (Restated.finalizedPreceqAtSteps_anchor facts S Sched x hn' hfin tGAT) hTY
  have hsR : M.support_cutoff S.E ((M.opening_slot S.hc (r + 1 + 1)))
      ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1 + 1)) - 1 := by
    have e1 := facts.sch.support_cutoff_le_vote_time_succ S.E ((M.opening_slot S.hc (r + 1 + 1)))
    have e2 := Restated.vote_time_opening_slot_add facts S (r + 1 + 1) 1
    push_cast at e2
    rw [e2] at e1; linarith
  have hopos : 0 < (M.opening_slot S.hc (r + 1)) := facts.gr.opening_slot_pos S (Nat.succ_pos r)
  exact Restated.headsBelow_range_afterPhase (hr1 := Restated.one_le_round_of_of_opening_slot_le facts S (r := r + 1) (Nat.le_add_left 1 r) hs0) facts S Sched x hexec hsync hmult htd hmono hgst hcv
    (fun t h1 h2 => hphase t h1 (le_trans h2 ht'E))
    (fun t h => hthird t (le_trans h ht'E)) hcs' ht'len hunder hunderS
    (s₀ := s₀) (s₁ := (M.opening_slot S.hc (r + 1 + 1)))
    (lt_of_lt_of_le hopos hs0) (le_trans ht's (slotStart_mono S hs0)) hsR
    (fun s h0 h1 => hAB s (le_trans hs0 h0) h1) hpath hbase
    (fun s _ _ m hm q hq => Restated.tick_outcome_of_tickStepAt facts S Sched x
      hexec.idealization.root_injective hexec.honestRootsNew hmono hm (facts.sch.vote_time_emod_delta S _)
      (Finset.mem_sdiff.2 ⟨Restated.awake_of_mem_HonSlot facts S Sched _ hq, fun h =>
        ((Restated.mem_HonSlot facts).mp hq).2.2
          (hmono _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E s) h)⟩))
    (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- At the round-`(r + 1)` tick, every member of `HonRound S Sched (r + 1)` is honest through the
    tick's successor and holds a finalized block and a justified block that are ancestors of the
    anchor `T`. -/
theorem honRound_finJust_at_tick (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (hmono : Sched.MonotoneCorruption)
    {r : Round} {n : Nat} {T : NamedBlock V}
    (hinv : Restated.AfterPhaseInvariantOverActiveSetsTop M S Sched x (r + 1) n T)
    {n' : Nat} (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1 + 1))))
    (hJT : ∀ (v : V) (n₁ : Nat),
      M.vote_time S.E ((M.opening_slot S.hc (r + 1)) + 1) - 1 ≤ (x[n₁].time : Int) →
      n₁ ≤ n' + 1 → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J T.erase) :
    ∀ q ∈ Restated.HonRound M S Sched (r + 1), Restated.HonestThrough M Sched x (n + 1) q ∧
      Block.Preceq (x[n][q].st).st.core.F T.erase ∧
      Block.Preceq (x[n][q].st).st.core.J T.erase := by
  intro q hq
  have hn := hinv.tick
  have hd := S.E.Δ_pos
  obtain ⟨hn1, hn0⟩ := Restated.tickStepAt_time facts x hn
  have hqA : q ∉ Sched.adv ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) := (Finset.mem_sdiff.1 hq).2
  have hqn1 : Restated.HonestThrough M Sched x (n + 1) q := fun t ht hin =>
    hqA (hmono t _ (by rw [← hn1]; exact ht) hin)
  have hqn : Restated.HonestThrough M Sched x n q := fun t ht =>
    hqn1 t (le_trans ht (Restated.time_mono_int facts S Sched x (Nat.le_succ n)))
  have hnn' : n ≤ n' := Restated.tick_le_of_round_le facts S Sched x hn hn' (Nat.le_succ _)
  have hvt1 : M.vote_time S.E ((M.opening_slot S.hc (r + 1)) + 1) = (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) - S.E.Δ := by
    have h := Restated.vote_time_opening_slot_add facts S (r + 1) 1
    rw [h]; push_cast; ring
  exact ⟨hqn1, hinv.fin q n (Nat.le_succ n) hqn,
    hJT q n (by rw [hvt1]; linarith) (Nat.le_succ_of_le hnn') hqn⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If every member of `HonRound S Sched (r + 1)` holds finalized and justified blocks that are
    ancestors of `T`, `T` is an ancestor of `Y`, and every block passing such a member's eligibility
    test at round `(r + 1)`'s opening slot lies on one chain with `Y`, then the confirmed block of
    every store such a member's round-`(r + 1)` action read can give lies on one chain with `Y`. -/
theorem liveConfirmed_compatible_of_eligible (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {r : Round} {n : Nat} {T : NamedBlock V}
    (hn : Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    (hFJ : ∀ q ∈ Restated.HonRound M S Sched (r + 1), Restated.HonestThrough M Sched x (n + 1) q ∧
      Block.Preceq (x[n][q].st).st.core.F T.erase ∧ Block.Preceq (x[n][q].st).st.core.J T.erase)
    {Y : Block V} (hTY : Block.Preceq T.erase Y)
    (hEl : ∀ q ∈ Restated.HonRound M S Sched (r + 1), ∀ el : Block V → Bool,
      Restated.Vocabulary.Protocol.confEligible M S.E (x[n][q].st).st.core ((M.opening_slot S.hc (r + 1))) ⇢ el →
      ∀ H : Block V, el H = true → Block.compatible H Y = true) :
    ∀ q ∈ Restated.HonRound M S Sched (r + 1),
      ∀ hs ∈ Restated.actionHealingStore M S (x[n][q].st) (r + 1),
        Block.compatible hs.live_confirmed Y = true := by
  intro q hq hs hhs
  rcases Restated.live_confirmed_cases_honRound facts S Sched x hn hq hs hhs with ⟨H, hel, heq⟩ | heq
  ·
    obtain ⟨el, hel'⟩ := confEligible_nonempty_hp facts S.E (x[n][q].st).st.core
      ((M.opening_slot S.hc (r + 1)))
    rw [heq]; exact hEl q hq el hel' H (hel el hel')
  · rw [heq]
    exact compatible_of_preceq_c2b (preceq_trans_Preceq
      (facts.fc.fgRoot_preceq_ofJustifiedBranch
        (stH := (M.toHealing (Restated.confStoreAt M S (x[n][q].st) ((M.opening_slot S.hc (r + 1))))))
        (by rw [Restated.confStoreAt, facts.hd.setClock_toHealing_F]; exact (hFJ q hq).2.1)
        (fun _ => by rw [Restated.confStoreAt, facts.hd.setClock_toHealing_J]; exact (hFJ q hq).2.2)) hTY)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If `T` is an ancestor of `Y`, and `Y` lies on one chain with every honest round-`r` SG block and
    with every confirmed block of the honest round-`(r + 1)` action reads, then every
    round-`(r + 1)` SG block of a member of `HonRound S Sched (r + 1)` lies on one chain with `Y`. -/
theorem roundSG_compatible_of_parts (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {r : Round} {n n_W : Nat} {T : NamedBlock V}
    (hJ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x (r + 1) n n_W T)
    {n_prev : Nat} (hnp : Restated.tickStepAt M x n_prev ((Restated.Vocabulary.Execution.Setup.a M S r)))
    (hFJ : ∀ q ∈ Restated.HonRound M S Sched (r + 1), Restated.HonestThrough M Sched x (n + 1) q ∧
      Block.Preceq (x[n][q].st).st.core.F T.erase ∧ Block.Preceq (x[n][q].st).st.core.J T.erase)
    {Y : Block V} (hTY : Block.Preceq T.erase Y)
    (hGY : ∀ v_2 ∈ Restated.HonRound M S Sched r, ∀ a : NamedAttestation V,
      a.round = r → a.val_index = v_2 →
      (⟨v_2, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n_prev + 1].sent →
      ∀ G : NamedBlock V, G ∈ (x[n_prev + 1][v_2].st).st.bodies → a.confirmed = some G.root →
      Block.compatible G.erase Y = true)
    (hLY : ∀ q ∈ Restated.HonRound M S Sched (r + 1),
      ∀ hs ∈ Restated.actionHealingStore M S (x[n][q].st) (r + 1),
        Block.compatible hs.live_confirmed Y = true)
    (hmono : Sched.MonotoneCorruption) :
    ∀ v_1 ∈ Restated.HonRound M S Sched (r + 1), ∀ a : NamedAttestation V,
      a.round = r + 1 → a.val_index = v_1 →
      (⟨v_1, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n + 1].sent →
      ∀ C : NamedBlock V, C ∈ (x[n + 1][v_1].st).st.bodies → a.confirmed = some C.root →
      Block.compatible C.erase Y = true := by
  intro v_1 hv_1 a ha hav hsent C hC hconf
  have hn := (joint_toTop_hp hJ).tick
  obtain ⟨hv_1n1, hFn, hJn⟩ := hFJ v_1 hv_1
  obtain ⟨nr, hnr⟩ := actionReadFrom_nonempty_hp facts (Setup.alwaysAwake S) (x[n][v_1].st) (r + 1)
  obtain ⟨g, hg⟩ := frameGradeRead_nonempty_hp facts nr.cache S.E S.hc (M.toHealing nr.st.core)
    (r + 1)
  have hhs : M.toHealing nr.st.core ∈ Restated.actionHealingStore M S (x[n][v_1].st) (r + 1) :=
    ⟨nr, hnr, rfl⟩
  have hfr : M.readFrame nr.cache (M.toHealing nr.st.core) (r + 1)
      ∈ Restated.actionFrame M S (x[n][v_1].st) (r + 1) := ⟨nr, hnr, rfl⟩
  have hCeq := Restated.freshSG_erase_eq_sgVote facts S Sched x hexec hn hv_1n1 ha hav hsent hC
    hconf nr hnr g hg
  have hFa : Block.Preceq (M.toHealing nr.st.core).F T.erase := by
    rw [Restated.actionHealingStore_F facts S _ _ _ hhs]; exact hFn
  have hJa : Block.Preceq (M.toHealing nr.st.core).J T.erase := by
    rw [Restated.actionHealingStore_J facts S _ _ _ hhs]; exact hJn
  rcases Restated.sgVote_directed_cases facts S (x[n][v_1].st) (r + 1) nr hnr g hg with
      hL | ⟨root, hroot, hpre⟩ | ⟨root, hroot, hpre⟩ | hfg
  · rw [← hCeq] at hL
    exact Protocol.compatible_of_preceq_of_compatible hL (hLY v_1 hv_1 _ hhs)
  · rw [← hCeq] at hpre
    obtain ⟨m, B, hm, hB, hrootB⟩ :=
      Restated.actionFrame_g1_provenance facts S Sched x hn v_1 root _ hfr hroot
    obtain ⟨b, hb⟩ := facts.gr.gradeBool_nonempty S.E (M.gradeView (M.toHealing (x[m][v_1].st).st.core))
      (x[m][v_1].st).st.core.F S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) .g1)
      (M.late S.E S.hc (r + 1) .g1) B
    obtain ⟨v_2, hv_2, a₂, ha₂, hav₂, hsent₂, G₀, hG₀, hconf₂, hBG⟩ :=
      hJ.gradedUnderPrevSGPerformers n_prev hnp v_1 (Restated.mem_grade1PerformersW_of_honRound facts S Sched hmono hv_1) m hm B
        b hb (hB b hb)
    exact Protocol.compatible_of_preceq_of_compatible
      (preceq_trans_Preceq hpre (preceq_trans_Preceq hrootB hBG))
      (hGY v_2 hv_2 a₂ ha₂ hav₂ hsent₂ G₀ hG₀ hconf₂)
  · rw [← hCeq] at hpre
    obtain ⟨m, B, hm, hB, hrootB⟩ :=
      Restated.actionFrame_g2_provenance facts S Sched x hn v_1 root _ hfr hroot
    obtain ⟨b, hb⟩ := facts.gr.gradeBool_nonempty S.E (M.gradeView (M.toHealing (x[m][v_1].st).st.core))
      (x[m][v_1].st).st.core.F S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) .g2)
      (M.late S.E S.hc (r + 1) .g2) B
    obtain ⟨v_2, hv_2, a₂, ha₂, hav₂, hsent₂, G₀, hG₀, hconf₂, hBG⟩ :=
      hJ.gradedUnderPrevSG n_prev hnp v_1 hv_1 .g2 (by decide) (facts.gr.domain_le_action S (r + 1) .g2) m hm B
        b hb (hB b hb)
    exact Protocol.compatible_of_preceq_of_compatible
      (preceq_trans_Preceq hpre (preceq_trans_Preceq hrootB hBG))
      (hGY v_2 hv_2 a₂ ha₂ hav₂ hsent₂ G₀ hG₀ hconf₂)
  · rw [← hCeq] at hfg
    rw [hfg]
    exact compatible_of_preceq_c2b (preceq_trans_Preceq (facts.fc.fgRoot_preceq hFa hJa) hTY)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- A round-`r` SG block `G₀` named as confirmed by an honest round-`r` attestation, and a
    descendant of the round-`(r + 1)` anchor `T`, is an ancestor of the vote of every honest active
    committee member at every slot from round `(r + 1)`'s opening slot to round `(r + 2)`'s second
    slot. -/
theorem prevSG_headsBelow_roundRange (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
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
    {v_2 : V} (hv_2 : v_2 ∈ Restated.HonRound M S Sched r) {a₂ : NamedAttestation V}
    (ha₂ : a₂.round = r) (hav₂ : a₂.val_index = v_2)
    (hsent₂ : (⟨v_2, NamedObject.attest a₂⟩ : SignedMsg V (NamedObject V)) ∈ x[n_prev + 1].sent)
    {G₀ : NamedBlock V} (hG₀ : G₀ ∈ (x[n_prev + 1][v_2].st).st.bodies)
    (hconf₂ : a₂.confirmed = some G₀.root) (hTG : Block.Preceq T.erase G₀.erase)
    (hrecvR : Restated.NextRoundReceipts M S Sched x (r + 1)) :
    ∀ s : Slot, (M.opening_slot S.hc (r + 1)) ≤ s → s ≤ (M.opening_slot S.hc (r + 1 + 1)) + 1 →
      Restated.HeadsBelow M S Sched x G₀.erase s := by
  have hinv := joint_toTop_hp hJ
  have hd := S.E.Δ_pos
  have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
  have hRd : 12 * S.E.Δ ≤ 4 * (S.hc.R : Int) * S.E.Δ := by nlinarith
  have hG0heads : Restated.HeadsBelow M S Sched x G₀.erase ((M.opening_slot S.hc (r + 1))) :=
    hJ.prevHeads n_prev hnp v_2 hv_2 a₂ ha₂ hav₂ hsent₂ G₀ hG₀ hconf₂
  obtain ⟨t', -, ht's, -, hcs'⟩ :=
    Restated.exists_cone_cutoff_at_opening facts S Sched tE hmono hcom tGAT gap hgst hlen hphase hcs hr
  have hopos : 0 < (M.opening_slot S.hc (r + 1)) := facts.gr.opening_slot_pos S (Nat.succ_pos r)
  have hGall : ∀ v_3 ∈ Restated.HonRound M S Sched r, ∀ a₃ : NamedAttestation V,
      a₃.round = r → a₃.val_index = v_3 →
      (⟨v_3, NamedObject.attest a₃⟩ : SignedMsg V (NamedObject V)) ∈ x[n_prev + 1].sent →
      ∀ G : NamedBlock V, G ∈ (x[n_prev + 1][v_3].st).st.bodies → a₃.confirmed = some G.root →
      Block.compatible G.erase G₀.erase = true :=
    fun v_3 hv_3 a₃ ha₃ hav₃ hsent₃ G hG hconf₃ =>
      Restated.compatible_of_headsBelow_after facts S Sched x htd hcs' hopos
        (le_trans ht's (slotStart_mono S (Nat.le_succ _)))
        (hJ.prevHeads n_prev hnp v_3 hv_3 a₃ ha₃ hav₃ hsent₃ G hG hconf₃) hG0heads
  have hFJ := Restated.honRound_finJust_at_tick facts S Sched x hmono hinv hn' hJT
  have hLY : ∀ q ∈ Restated.HonRound M S Sched (r + 1),
      ∀ hs ∈ Restated.actionHealingStore M S (x[n][q].st) (r + 1),
        Block.compatible hs.live_confirmed G₀.erase = true :=
    fun q hq hs hhs => Protocol.compatible_comm
      (hJ.prevConfirmed n_prev hnp q hq v_2 hv_2 a₂ ha₂ hav₂ hsent₂ G₀ hG₀ hconf₂ hs hhs)
  have hCY := Restated.roundSG_compatible_of_parts (hmono := hmono) facts S Sched x hexec hJ hnp hFJ hTG hGall hLY
  have hAB := Restated.coneAnchorCompatible_roundSlots_above (hrecvR := hrecvR) facts S Sched x tE hexec hmono htd hsync hmult
    tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr hJ hn' hcross hJT hnp hTG
    (fun v_3 hv_3 a₃ ha₃ hav₃ hsent₃ G hG hconf₃ _ =>
      hGall v_3 hv_3 a₃ ha₃ hav₃ hsent₃ G hG hconf₃) hCY
  obtain ⟨hnp1, -⟩ := Restated.tickStepAt_time facts x hnp
  have hv_2A : v_2 ∉ Sched.adv ((Restated.Vocabulary.Execution.Setup.a M S r)) := (Finset.mem_sdiff.1 hv_2).2
  have hv_2h : Restated.HonestThrough M Sched x (n_prev + 1) v_2 := fun t ht hin =>
    hv_2A (hmono t _ (by rw [← hnp1]; exact ht) hin)
  have hopen := Restated.tGAT_add_two_rounds_le_opening facts S tGAT tE gap hgst hlen hr
  have hsucc := facts.gr.action_succ_eq_add_rounds S r
  have hA1 : (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) = M.opening S.E S.hc (r + 1) + 6 * S.E.Δ :=
    action_eq_opening_add_hp facts S (r + 1)
  have htGr : tGAT ≤ (x[n_prev + 1].time : Int) := by rw [hnp1]; linarith
  have hpath : ∀ s : Slot, (M.opening_slot S.hc (r + 1)) ≤ s → s ≤ (M.opening_slot S.hc (r + 1 + 1)) →
      Restated.ConeAnchorChainInTree M S x G₀.erase s := by
    intro s h0 h1
    have hmo := slotStart_mono S h0
    have hvf1 := slotStart_add_two_delta_le_support_cutoff_hp facts S s
    have hvf2 := support_cutoff_add_delta_le_view_freeze_hp facts S s
    have hco := Restated.confirmation_time_opening_slot facts S (r + 1)
    have hsc := facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E ((M.opening_slot S.hc (r + 1)))
    exact Restated.coneAnchorChainInTree_of_heldDescendant facts S Sched x tE hexec hmono htd hsync hmult tGAT
      gap hgst hlen hcv hthird hphase hrsW hcs hr hinv hcross hG₀ hv_2h htGr
      (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _)) hTG
      (by clear hA1 hopen; rw [hnp1]; linarith) (Nat.succ_le_succ h1) (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›)
  exact Restated.headsBelow_roundRange_above facts S Sched x tE hexec hmono htd hsync hmult hcom tGAT gap hgst
    hlen hcv hthird hphase hrsW hcs hr hinv hn' hcross hTG hAB hpath le_rfl hG0heads

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- A block `H₁` that a member `v_1` of `HonRound S Sched (r + 1)` confirms at its action read,
    passing its eligibility test, and that is a descendant of the round-`(r + 1)` anchor `T`, is an
    ancestor of the vote of every honest active committee member at every slot from round
    `(r + 1)`'s second slot to round `(r + 2)`'s second slot. -/
theorem confirmed_headsBelow_roundRange (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
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
    {v_1 : V} (hv_1 : v_1 ∈ Restated.HonRound M S Sched (r + 1)) {H₁ : Block V}
    (el : Block V → Bool)
    (hel' : Restated.Vocabulary.Protocol.confEligible M S.E (x[n][v_1].st).st.core
      ((M.opening_slot S.hc (r + 1))) ⇢ el)
    (hel : el H₁ = true)
    (hsv : M.HS) (hhsv : hsv ∈ Restated.actionHealingStore M S (x[n][v_1].st) (r + 1))
    (hlc : hsv.live_confirmed = H₁)
    (hTH : Block.Preceq T.erase H₁)
    (hrecvR : Restated.NextRoundReceipts M S Sched x (r + 1)) :
    ∀ s : Slot, (M.opening_slot S.hc (r + 1)) + 1 ≤ s → s ≤ (M.opening_slot S.hc (r + 1 + 1)) + 1 →
      Restated.HeadsBelow M S Sched x H₁ s := by
  have hinv := joint_toTop_hp hJ
  have hn := hinv.tick
  have hd := S.E.Δ_pos
  have hd1 : (1 : Int) ≤ S.E.Δ := hd
  have hR3 : 3 ≤ S.hc.R := S.hc.R_ge_three
  have hct : M.confirmation_time S.E ((M.opening_slot S.hc (r + 1))) = (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) :=
    Restated.confirmation_time_opening_slot facts S (r + 1)
  have hnc : Restated.tickStepAt M x n (M.confirmation_time S.E ((M.opening_slot S.hc (r + 1)))) := by
    rw [hct]; exact hn
  have hhon : ∀ q ∈ Restated.HonRound M S Sched (r + 1),
      HonestThroughTime Sched (M.confirmation_time S.E ((M.opening_slot S.hc (r + 1)))) q :=
    fun q hq t' ht' hin => (Finset.mem_sdiff.1 hq).2 (hmono _ _ (le_trans ht' (le_of_eq hct)) hin)
  have hopos : 0 < (M.opening_slot S.hc (r + 1)) := facts.gr.opening_slot_pos S (Nat.succ_pos r)
  have hopen := Restated.tGAT_add_two_rounds_le_opening facts S tGAT tE gap hgst hlen hr
  have hlo : tGAT ≤ slotStart S.E.Δ ((M.opening_slot S.hc (r + 1))) := by
    rw [← opening_eq_slotStart_hp facts S]; nlinarith
  have hGall : ∀ v_2 ∈ Restated.HonRound M S Sched r, ∀ a₂ : NamedAttestation V,
      a₂.round = r → a₂.val_index = v_2 →
      (⟨v_2, NamedObject.attest a₂⟩ : SignedMsg V (NamedObject V)) ∈ x[n_prev + 1].sent →
      ∀ G : NamedBlock V, G ∈ (x[n_prev + 1][v_2].st).st.bodies → a₂.confirmed = some G.root →
      Block.compatible G.erase H₁ = true := by
    intro v_2 hv_2 a₂ ha₂ hav₂ hsent₂ G hG hconf₂
    rw [← hlc]
    exact hJ.prevConfirmed n_prev hnp v_1 hv_1 v_2 hv_2 a₂ ha₂ hav₂ hsent₂ G hG hconf₂ hsv hhsv
  have hFJ := Restated.honRound_finJust_at_tick facts S Sched x hmono hinv hn' hJT
  have hEl : ∀ q ∈ Restated.HonRound M S Sched (r + 1), ∀ elq : Block V → Bool,
      Restated.Vocabulary.Protocol.confEligible M S.E (x[n][q].st).st.core ((M.opening_slot S.hc (r + 1))) ⇢ elq →
      ∀ H' : Block V, elq H' = true → Block.compatible H' H₁ = true :=
    fun q hq elq helq H' hH' => Restated.sameSlot_eligible_compatible_afterPhase facts S Sched x hexec hsync
      htd hopos
      (le_trans hgst hlo) hnc (Restated.honRound_awakeThroughout_confirmation facts S Sched (r + 1) hq)
      (hhon q hq) (Restated.honRound_awakeThroughout_confirmation facts S Sched (r + 1) hv_1) (hhon v_1 hv_1)
      helq hH' hel' hel (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›) (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›)
  have hLY := Restated.liveConfirmed_compatible_of_eligible facts S Sched x hn hFJ hTH hEl
  have hCY := Restated.roundSG_compatible_of_parts (hmono := hmono) facts S Sched x hexec hJ hnp hFJ hTH hGall hLY
  have hAB := Restated.coneAnchorCompatible_roundSlots_above (hrecvR := hrecvR) facts S Sched x tE hexec hmono htd hsync hmult
    tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr hJ hn' hcross hJT hnp hTH
    (fun v_2 hv_2 a₂ ha₂ hav₂ hsent₂ G hG hconf₂ _ =>
      hGall v_2 hv_2 a₂ ha₂ hav₂ hsent₂ G hG hconf₂) hCY
  have hpath : ∀ s : Slot, (M.opening_slot S.hc (r + 1)) ≤ s → s ≤ (M.opening_slot S.hc (r + 1 + 1)) →
      Restated.ConeAnchorChainInTree M S x H₁ s :=
    fun s h0 h1 => Restated.coneAnchorChainInTree_of_eligibleConfirmation_later facts S Sched x tE hexec hmono
      htd hsync hmult tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr hinv hcross
      (Restated.honRound_awakeThroughout_confirmation facts S Sched (r + 1) hv_1) (hhon v_1 hv_1) el hel' hel
      (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _)) hTH hlo h0 (Nat.succ_le_succ h1)
  have hfin := Restated.fin_old_anchor_before_succ_tick_of_hypotheses facts (hcross := hcross) S Sched x tE hexec
    hmono tGAT gap hgst hlen hthird hphase hrsW hr hinv hn'
  have hsucc := facts.gr.action_succ_eq_add_rounds S (r + 1)
  have hsR : M.view_freeze S.E ((M.opening_slot S.hc (r + 1))) ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1 + 1)) - 1 := by
    have e1 := facts.sch.view_freeze_lt_vote_time_succ S.E ((M.opening_slot S.hc (r + 1)))
    have e3 := facts.sch.slotStart_add_delta_eq_vote_time S.E ((M.opening_slot S.hc (r + 1)) + 1)
    have e4 := slotStart_succ S.E.Δ ((M.opening_slot S.hc (r + 1)))
    have e2 : M.confirmation_time S.E ((M.opening_slot S.hc (r + 1)))
        = slotStart S.E.Δ ((M.opening_slot S.hc (r + 1))) + 6 * S.E.Δ := (facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E _).symm
    rw [hct] at e2
    rw [hsucc]; nlinarith
  have hle : (M.opening_slot S.hc (r + 1)) ≤ (M.opening_slot S.hc (r + 1 + 1)) := by
    rw [facts.gr.opening_slot_succ S.hc (r + 1)]; exact Nat.le_add_right _ _
  have hbase := Restated.headsBelow_succ_of_eligible_afterPhase facts S Sched x hexec hsync hmult htd hmono
    (tR := (Restated.Vocabulary.Execution.Setup.a M S (r + 1 + 1)) - 1) hgst hcv hphase hthird hcs (Restated.delta_le_of_healingLengthη facts S hlen)
    (Restated.deliveredDescendantUnderFinalized_anchor facts S Sched x hn' hfin tGAT)
    (Restated.finalizedPreceqAtSteps_anchor facts S Sched x hn' hfin tGAT) hTH (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _))
    hopos hlo hsR hnc (Restated.honRound_awakeThroughout_confirmation facts S Sched (r + 1) hv_1)
    (hhon v_1 hv_1) el hel' hel (hAB _ le_rfl hle) (hpath _ le_rfl hle)
    (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›) (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›)
  exact Restated.headsBelow_roundRange_above facts S Sched x tE hexec hmono htd hsync hmult hcom tGAT gap hgst
    hlen hcv hthird hphase hrsW hcs hr hinv hn' hcross hTH hAB (s₀ := (M.opening_slot S.hc (r + 1)) + 1)
    (fun s h0 h1 => hpath s (le_trans (Nat.le_succ _) h0) h1) (Nat.le_succ _) hbase

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Every block that an honest round-`(r + 1)` attestation names as confirmed is an ancestor of the
    round-`(r + 1)` anchor `T`, or of the vote of every honest active committee member at every slot
    from round `(r + 1)`'s second slot to round `(r + 2)`'s second slot. -/
theorem roundSG_preceq_anchor_or_headsBelow (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
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
    (hrecvR : Restated.NextRoundReceipts M S Sched x (r + 1)) :
    ∀ v_1 ∈ Restated.HonRound M S Sched (r + 1), ∀ a : NamedAttestation V,
      a.round = r + 1 → a.val_index = v_1 →
      (⟨v_1, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n + 1].sent →
      ∀ C : NamedBlock V, C ∈ (x[n + 1][v_1].st).st.bodies → a.confirmed = some C.root →
      Block.Preceq C.erase T.erase ∨
        ∀ s : Slot, (M.opening_slot S.hc (r + 1)) + 1 ≤ s → s ≤ (M.opening_slot S.hc (r + 1 + 1)) + 1 →
          Restated.HeadsBelow M S Sched x C.erase s := by
  intro v_1 hv_1 a ha hav hsent C hC hconf
  have hinv := joint_toTop_hp hJ
  have hn := hinv.tick
  have hFJ := Restated.honRound_finJust_at_tick facts S Sched x hmono hinv hn' hJT
  obtain ⟨hv_1n1, hFn, hJn⟩ := hFJ v_1 hv_1
  have hsg := hinv.sg v_1 hv_1 a ha hav hsent C hC hconf
  rcases compatible_cases hsg with hCT | hTC
  · exact Or.inl hCT
  obtain ⟨nr, hnr⟩ := actionReadFrom_nonempty_hp facts (Setup.alwaysAwake S) (x[n][v_1].st) (r + 1)
  obtain ⟨g, hg⟩ := frameGradeRead_nonempty_hp facts nr.cache S.E S.hc (M.toHealing nr.st.core)
    (r + 1)
  have hhs : M.toHealing nr.st.core ∈ Restated.actionHealingStore M S (x[n][v_1].st) (r + 1) :=
    ⟨nr, hnr, rfl⟩
  have hfr : M.readFrame nr.cache (M.toHealing nr.st.core) (r + 1)
      ∈ Restated.actionFrame M S (x[n][v_1].st) (r + 1) := ⟨nr, hnr, rfl⟩
  have hCeq := Restated.freshSG_erase_eq_sgVote facts S Sched x hexec hn hv_1n1 ha hav hsent hC
    hconf nr hnr g hg
  have hFa : Block.Preceq (M.toHealing nr.st.core).F T.erase := by
    rw [Restated.actionHealingStore_F facts S _ _ _ hhs]; exact hFn
  have hJa : Block.Preceq (M.toHealing nr.st.core).J T.erase := by
    rw [Restated.actionHealingStore_J facts S _ _ _ hhs]; exact hJn
  rcases Restated.sgVote_directed_cases facts S (x[n][v_1].st) (r + 1) nr hnr g hg with
      hL | ⟨root, hroot, hpre⟩ | ⟨root, hroot, hpre⟩ | hfg
  · rw [← hCeq] at hL
    rcases Restated.live_confirmed_cases_honRound facts S Sched x hn hv_1 _ hhs with
      ⟨H, hel, heq⟩ | heq
    ·
      obtain ⟨el, hel'⟩ := confEligible_nonempty_hp facts S.E (x[n][v_1].st).st.core
        ((M.opening_slot S.hc (r + 1)))
      rw [heq] at hL
      refine Or.inr (fun s h0 h1 => Restated.headsBelow_mono facts S Sched x hL ?_)
      exact Restated.confirmed_headsBelow_roundRange (hrecvR := hrecvR) facts S Sched x tE hexec hmono htd hsync hmult hcom
        tGAT gap
        hgst hlen hcv hthird hphase hrsW hcs hr hJ hn' hcross hJT hnp hv_1 el hel' (hel el hel')
        _ hhs heq (preceq_trans_Preceq hTC hL) s h0 h1
    · rw [heq] at hL
      exact Or.inl (preceq_trans_Preceq hL (facts.fc.fgRoot_preceq_ofJustifiedBranch
        (stH := (M.toHealing (Restated.confStoreAt M S (x[n][v_1].st) ((M.opening_slot S.hc (r + 1))))))
        (by rw [Restated.confStoreAt, facts.hd.setClock_toHealing_F]; exact hFn)
        (fun _ => by rw [Restated.confStoreAt, facts.hd.setClock_toHealing_J]; exact hJn)))
  · rw [← hCeq] at hpre
    obtain ⟨m, B, hm, hB, hrootB⟩ :=
      Restated.actionFrame_g1_provenance facts S Sched x hn v_1 root _ hfr hroot
    obtain ⟨b, hb⟩ := facts.gr.gradeBool_nonempty S.E (M.gradeView (M.toHealing (x[m][v_1].st).st.core))
      (x[m][v_1].st).st.core.F S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) .g1)
      (M.late S.E S.hc (r + 1) .g1) B
    obtain ⟨v_2, hv_2, a₂, ha₂, hav₂, hsent₂, G₀, hG₀, hconf₂, hBG⟩ :=
      hJ.gradedUnderPrevSGPerformers n_prev hnp v_1 (Restated.mem_grade1PerformersW_of_honRound facts S Sched hmono hv_1) m hm B
        b hb (hB b hb)
    have hCG := preceq_trans_Preceq hpre (preceq_trans_Preceq hrootB hBG)
    refine Or.inr (fun s h0 h1 => Restated.headsBelow_mono facts S Sched x hCG ?_)
    exact Restated.prevSG_headsBelow_roundRange (hrecvR := hrecvR) facts S Sched x tE hexec hmono htd hsync hmult hcom tGAT gap hgst
      hlen hcv hthird hphase hrsW hcs hr hJ hn' hcross hJT hnp hv_2 ha₂ hav₂ hsent₂ hG₀
      hconf₂ (preceq_trans_Preceq hTC hCG) s (le_trans (Nat.le_succ _) h0) h1
  · rw [← hCeq] at hpre
    obtain ⟨m, B, hm, hB, hrootB⟩ :=
      Restated.actionFrame_g2_provenance facts S Sched x hn v_1 root _ hfr hroot
    obtain ⟨b, hb⟩ := facts.gr.gradeBool_nonempty S.E (M.gradeView (M.toHealing (x[m][v_1].st).st.core))
      (x[m][v_1].st).st.core.F S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) .g2)
      (M.late S.E S.hc (r + 1) .g2) B
    obtain ⟨v_2, hv_2, a₂, ha₂, hav₂, hsent₂, G₀, hG₀, hconf₂, hBG⟩ :=
      hJ.gradedUnderPrevSG n_prev hnp v_1 hv_1 .g2 (by decide) (facts.gr.domain_le_action S (r + 1) .g2) m hm B
        b hb (hB b hb)
    have hCG := preceq_trans_Preceq hpre (preceq_trans_Preceq hrootB hBG)
    refine Or.inr (fun s h0 h1 => Restated.headsBelow_mono facts S Sched x hCG ?_)
    exact Restated.prevSG_headsBelow_roundRange (hrecvR := hrecvR) facts S Sched x tE hexec hmono htd hsync hmult hcom tGAT gap hgst
      hlen hcv hthird hphase hrsW hcs hr hJ hn' hcross hJT hnp hv_2 ha₂ hav₂ hsent₂ hG₀
      hconf₂ (preceq_trans_Preceq hTC hCG) s (le_trans (Nat.le_succ _) h0) h1
  · rw [← hCeq] at hfg
    refine Or.inl ?_
    rw [hfg]
    exact facts.fc.fgRoot_preceq hFa hJa

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If every honest active member of the committee of a slot `s` of round `r + 1` votes for a
    descendant `Y` of the anchor `T`, and some outcome of slot `s`'s eligibility test of an honest
    reader `q`'s store passes `H`, then `H` and `Y` lie on one chain. -/
theorem eligible_compatible_of_heads_round (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
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
    {r : Round} {n : Nat} {T : NamedBlock V}
    (hr : Restated.switchRound M S tE ≤ r + 1)
    (hinv : Restated.AfterPhaseInvariantOverActiveSetsTop M S Sched x (r + 1) n T)
    {n' : Nat} (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1 + 1))))
    (hcross : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1 + 1))) →
      Restated.StepFinalizedCrossingUnderAnchor M S Sched x (r + 1) n'' T)
    {s : Slot} (hs0 : (M.opening_slot S.hc (r + 1)) ≤ s) (hs1 : s ≤ (M.opening_slot S.hc (r + 1 + 1)))
    {Y : Block V} (hTY : Block.Preceq T.erase Y) (hY : Restated.HeadsBelow M S Sched x Y s)
    {m : Nat} (hm : Restated.tickStepAt M x m (M.confirmation_time S.E s)) {q : V}
    (hqaw : q ∈ Sched.awakeThroughout (slotStart S.E.Δ s - S.E.Δ)
      (M.confirmation_time S.E s))
    (hqh : HonestThroughTime Sched (M.confirmation_time S.E s) q)
    {H : Block V} (el : Block V → Bool)
    (hel' : Restated.Vocabulary.Protocol.confEligible M S.E (x[m][q].st).st.core s ⇢ el)
    (hel : el H = true) :
    Block.compatible H Y = true := by
  have hd := S.E.Δ_pos
  have hd1 : (1 : Int) ≤ S.E.Δ := hd
  have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
  obtain ⟨t', ht'E, ht's, ht'len, hcs'⟩ :=
    Restated.exists_cone_cutoff_at_opening facts S Sched tE hmono hcom tGAT gap hgst hlen hphase hcs hr
  have hfin := Restated.fin_old_anchor_before_succ_tick_of_hypotheses facts (hcross := hcross) S Sched x tE hexec
    hmono tGAT gap hgst hlen hthird hphase hrsW hr hinv hn'
  have hopos : 0 < (M.opening_slot S.hc (r + 1)) := facts.gr.opening_slot_pos S (Nat.succ_pos r)
  have hopen := Restated.tGAT_add_two_rounds_le_opening facts S tGAT tE gap hgst hlen hr
  have hslo : tGAT ≤ slotStart S.E.Δ s := by
    have hmo := slotStart_mono S hs0
    rw [← opening_eq_slotStart_hp facts S] at hmo
    nlinarith
  have hsR : M.support_cutoff S.E s ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1 + 1)) - 1 := by
    have e1 := facts.sch.support_cutoff_le_vote_time_succ S.E s
    have e2 : M.vote_time S.E (s + 1)
        ≤ M.vote_time S.E ((M.opening_slot S.hc (r + 1 + 1)) + 1) :=
      facts.sch.vote_time_mono S.E (Nat.succ_le_succ hs1)
    have e3 := Restated.vote_time_opening_slot_add facts S (r + 1 + 1) 1
    push_cast at e3
    rw [e3] at e2; linarith
  exact Restated.eligible_compatible_of_cone facts S Sched x hexec hsync hmult htd hmono hgst hcv
    (fun t h1 h2 => hphase t h1 (le_trans h2 ht'E)) (fun t h => hthird t (le_trans h ht'E))
    hcs' ht'len (Restated.deliveredDescendant_mono facts S Sched x
      (Restated.deliveredDescendantUnderFinalized_anchor facts S Sched x hn' hfin tGAT) hTY)
      (Restated.finalizedPreceqAtSteps_mono facts S Sched x
      (Restated.finalizedPreceqAtSteps_anchor facts S Sched x hn' hfin tGAT) hTY)
    (lt_of_lt_of_le hopos hs0) hslo
    (le_trans ht's (slotStart_mono S (Nat.le_succ_of_le hs0))) hsR hY hm hqaw hqh hel' hel
    (Restated.one_le_round_of_of_opening_slot_le facts S (r := r + 1) (Nat.le_add_left 1 r) hs0)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If `T` is an ancestor of `B` and every honest active member of the committee of a slot `s` from
    round `(r + 1)`'s second slot to round `(r + 2)`'s second slot votes for a descendant of `B`,
    then the same holds at every slot from `s` to round `(r + 2)`'s second slot. -/
theorem headsBelow_roundStep (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
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
    {B : Block V} (hTB : Block.Preceq T.erase B)
    {s : Slot} (hs0 : (M.opening_slot S.hc (r + 1)) + 1 ≤ s)
    (hs1 : s ≤ (M.opening_slot S.hc (r + 1 + 1)) + 1)
    (hbase : Restated.HeadsBelow M S Sched x B s)
    (hrecvR : Restated.NextRoundReceipts M S Sched x (r + 1)) :
    ∀ s' : Slot, s ≤ s' → s' ≤ (M.opening_slot S.hc (r + 1 + 1)) + 1 →
      Restated.HeadsBelow M S Sched x B s' := by
  have hinv := joint_toTop_hp hJ
  have hd := S.E.Δ_pos
  have hd1 : (1 : Int) ≤ S.E.Δ := hd
  by_cases hlast : s = (M.opening_slot S.hc (r + 1 + 1)) + 1
  · intro s' h0 h1
    have : s' = s := le_antisymm (by rw [hlast]; exact h1) h0
    rw [this]; exact hbase
  have hs1' : s ≤ (M.opening_slot S.hc (r + 1 + 1)) := Nat.le_of_lt_succ (lt_of_le_of_ne hs1 hlast)
  have hs0' : (M.opening_slot S.hc (r + 1)) ≤ s := le_trans (Nat.le_succ _) hs0
  obtain ⟨t', -, ht's, -, hcs'⟩ :=
    Restated.exists_cone_cutoff_at_opening facts S Sched tE hmono hcom tGAT gap hgst hlen hphase hcs hr
  have hopos : 0 < (M.opening_slot S.hc (r + 1)) := facts.gr.opening_slot_pos S (Nat.succ_pos r)
  have hspos : 0 < s := lt_of_lt_of_le hopos hs0'
  have ht's1 : t' ≤ slotStart S.E.Δ (s + 1) := le_trans ht's (slotStart_mono S (Nat.le_succ_of_le hs0'))
  have hcommon : ∀ Y : Block V, Restated.HeadsBelow M S Sched x Y s → Block.compatible Y B = true :=
    fun Y hY => Restated.compatible_of_headsBelow_after facts S Sched x htd hcs' hspos ht's1 hY hbase
  have hGY : ∀ v_2 ∈ Restated.HonRound M S Sched r, ∀ a : NamedAttestation V,
      a.round = r → a.val_index = v_2 →
      (⟨v_2, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n_prev + 1].sent →
      ∀ G : NamedBlock V, G ∈ (x[n_prev + 1][v_2].st).st.bodies → a.confirmed = some G.root →
      Block.Preceq T.erase G.erase → Block.compatible G.erase B = true :=
    fun v_2 hv_2 a ha hav hsent G hG hconf hTG => hcommon _
      (Restated.prevSG_headsBelow_roundRange (hrecvR := hrecvR) facts S Sched x tE hexec hmono htd hsync hmult hcom tGAT gap hgst
        hlen hcv hthird hphase hrsW hcs hr hJ hn' hcross hJT hnp hv_2 ha hav hsent hG hconf
        hTG s hs0' hs1)
  have hCY : ∀ v_1 ∈ Restated.HonRound M S Sched (r + 1), ∀ a : NamedAttestation V,
      a.round = r + 1 → a.val_index = v_1 →
      (⟨v_1, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n + 1].sent →
      ∀ C : NamedBlock V, C ∈ (x[n + 1][v_1].st).st.bodies → a.confirmed = some C.root →
      Block.compatible C.erase B = true := by
    intro v_1 hv_1 a ha hav hsent C hC hconf
    rcases Restated.roundSG_preceq_anchor_or_headsBelow (hrecvR := hrecvR) facts S Sched x tE hexec hmono htd hsync hmult hcom tGAT
        gap hgst hlen hcv hthird hphase hrsW hcs hr hJ hn' hcross hJT hnp v_1 hv_1 a ha hav
        hsent C hC hconf with hCT | hCh
    · exact compatible_of_preceq_c2b (preceq_trans_Preceq hCT hTB)
    · exact hcommon _ (hCh s hs0 hs1)
  have hAB := Restated.coneAnchorCompatible_roundSlots_above (hrecvR := hrecvR) facts S Sched x tE hexec hmono htd hsync hmult
    tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr hJ hn' hcross hJT hnp hTB hGY hCY
  have hmaj := Restated.majority_of_committeeSleepinessW facts S Sched hcs' (s := s) ht's1
  obtain ⟨w, hw₀⟩ : ((S.E.committee s) ∩ Restated.HonSlot M S Sched s).Nonempty := by
    rw [Finset.inter_eq_right.2 (Restated.HonSlot_subset_committee facts S Sched _), ← Finset.card_pos]; omega
  have hwH := (Finset.mem_inter.mp hw₀).2
  obtain ⟨mw, hmw⟩ := Restated.exists_tickStepAt facts x htd (facts.sch.vote_time_pos S hspos)
  obtain ⟨-, hmw0⟩ := Restated.tickStepAt_time facts x hmw
  have hvt : M.vote_time S.E s = slotStart S.E.Δ s + S.E.Δ := (facts.sch.slotStart_add_delta_eq_vote_time S.E s).symm
  obtain ⟨Hd, hHd⟩ := (priv% Proofs.Claims.Restated.Claim13bK_ConeSlots
    DecoupledConsensusModel.Sts.Restated.gfHeadFrom_nonempty_cs) facts S (x[mw][w].st) s
  obtain ⟨D, hD, hDe⟩ := Restated.exists_named_of_mem_tree facts S Sched x mw w
    (Restated.gfHeadFrom_mem_tree facts S Sched x mw w s Hd hHd)
  have hBD : Block.Preceq B D.erase := by rw [hDe]; exact hbase w mw hwH hmw Hd hHd
  have hwh : Restated.HonestThrough M Sched x mw w := Restated.honestThrough_of_mem_HonSlot facts S Sched x hmono hwH
    (by
      rw [← facts.sch.slotStart_add_six_delta_eq_confirmation_time]
      rw [hvt] at hmw0; linarith)
  have hopen := Restated.tGAT_add_two_rounds_le_opening facts S tGAT tE gap hgst hlen hr
  have htGm : tGAT ≤ (x[mw].time : Int) := by
    have := slotStart_mono S hs0'
    rw [← opening_eq_slotStart_hp facts S (r + 1)] at this
    rw [hvt] at hmw0; nlinarith
  have hpath : ∀ s' : Slot, s ≤ s' → s' ≤ (M.opening_slot S.hc (r + 1 + 1)) →
      Restated.ConeAnchorChainInTree M S x B s' := by
    intro s' h0 h1
    have hmo := slotStart_mono S h0
    have hvf1 := slotStart_add_two_delta_le_support_cutoff_hp facts S s'
    have hvf2 := support_cutoff_add_delta_le_view_freeze_hp facts S s'
    exact Restated.coneAnchorChainInTree_of_heldDescendant facts S Sched x tE hexec hmono htd hsync hmult tGAT
      gap hgst hlen hcv hthird hphase hrsW hcs hr hinv hcross hD hwh htGm hBD hTB
      (by rw [hvt] at hmw0; linarith) (Nat.succ_le_succ h1) (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›)
  exact Restated.headsBelow_roundRange_above facts S Sched x tE hexec hmono htd hsync hmult hcom tGAT gap hgst
    hlen hcv hthird hphase hrsW hcs hr hinv hn' hcross hTB hAB hpath hs0' hbase

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If some outcome of slot `s`'s eligibility test of an honest reader `q`'s store passes `H`, for a
    slot `s` of round `r + 1` after its opening slot, and `T` is an ancestor of `H`, then every
    honest active member of slot `(s + 1)`'s committee votes for a descendant of `H`. -/
theorem headsBelow_succ_of_eligible_round (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
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
    {s : Slot} (hs0 : (M.opening_slot S.hc (r + 1)) + 1 ≤ s)
    (hs1 : s ≤ (M.opening_slot S.hc (r + 1 + 1)))
    {m : Nat} (hm : Restated.tickStepAt M x m (M.confirmation_time S.E s)) {q : V}
    (hqaw : q ∈ Sched.awakeThroughout (slotStart S.E.Δ s - S.E.Δ)
      (M.confirmation_time S.E s))
    (hqh : HonestThroughTime Sched (M.confirmation_time S.E s) q)
    {H : Block V} (el : Block V → Bool)
    (hel' : Restated.Vocabulary.Protocol.confEligible M S.E (x[m][q].st).st.core s ⇢ el)
    (hel : el H = true)
    (hTH : Block.Preceq T.erase H)
    (hrecvR : Restated.NextRoundReceipts M S Sched x (r + 1)) :
    Restated.HeadsBelow M S Sched x H (s + 1) := by
  have hinv := joint_toTop_hp hJ
  have hd := S.E.Δ_pos
  have hd1 : (1 : Int) ≤ S.E.Δ := hd
  have hs0' : (M.opening_slot S.hc (r + 1)) ≤ s := le_trans (Nat.le_succ _) hs0
  have hcount : ∀ Y : Block V, Block.Preceq T.erase Y → Restated.HeadsBelow M S Sched x Y s →
      Block.compatible Y H = true := fun Y hTY hY =>
    Protocol.compatible_comm (Restated.eligible_compatible_of_heads_round facts S Sched x tE hexec hmono htd
      hsync hmult hcom tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr hinv hn' hcross hs0' hs1
      hTY hY hm hqaw hqh el hel' hel)
  have hGY : ∀ v_2 ∈ Restated.HonRound M S Sched r, ∀ a : NamedAttestation V,
      a.round = r → a.val_index = v_2 →
      (⟨v_2, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n_prev + 1].sent →
      ∀ G : NamedBlock V, G ∈ (x[n_prev + 1][v_2].st).st.bodies → a.confirmed = some G.root →
      Block.Preceq T.erase G.erase → Block.compatible G.erase H = true :=
    fun v_2 hv_2 a ha hav hsent G hG hconf hTG => hcount _ hTG
      (Restated.prevSG_headsBelow_roundRange (hrecvR := hrecvR) facts S Sched x tE hexec hmono htd hsync hmult hcom tGAT gap hgst
        hlen hcv hthird hphase hrsW hcs hr hJ hn' hcross hJT hnp hv_2 ha hav hsent hG hconf
        hTG s hs0' (Nat.le_succ_of_le hs1))
  have hCY : ∀ v_1 ∈ Restated.HonRound M S Sched (r + 1), ∀ a : NamedAttestation V,
      a.round = r + 1 → a.val_index = v_1 →
      (⟨v_1, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n + 1].sent →
      ∀ C : NamedBlock V, C ∈ (x[n + 1][v_1].st).st.bodies → a.confirmed = some C.root →
      Block.compatible C.erase H = true := by
    intro v_1 hv_1 a ha hav hsent C hC hconf
    have hsg := hinv.sg v_1 hv_1 a ha hav hsent C hC hconf
    rcases Restated.roundSG_preceq_anchor_or_headsBelow (hrecvR := hrecvR) facts S Sched x tE hexec hmono htd hsync hmult hcom tGAT
        gap hgst hlen hcv hthird hphase hrsW hcs hr hJ hn' hcross hJT hnp v_1 hv_1 a ha hav
        hsent C hC hconf with hCT | hCh
    · exact compatible_of_preceq_c2b (preceq_trans_Preceq hCT hTH)
    · rcases compatible_cases hsg with hCT | hTC
      · exact compatible_of_preceq_c2b (preceq_trans_Preceq hCT hTH)
      · exact hcount _ hTC (hCh s hs0 (Nat.le_succ_of_le hs1))
  have hAB := Restated.coneAnchorCompatible_roundSlots_above (hrecvR := hrecvR) facts S Sched x tE hexec hmono htd hsync hmult
    tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr hJ hn' hcross hJT hnp hTH hGY hCY
  have hopen := Restated.tGAT_add_two_rounds_le_opening facts S tGAT tE gap hgst hlen hr
  have hslo : tGAT ≤ slotStart S.E.Δ s := by
    have := slotStart_mono S hs0'
    rw [← opening_eq_slotStart_hp facts S (r + 1)] at this; nlinarith
  have hpath := Restated.coneAnchorChainInTree_of_eligibleConfirmation facts S Sched x tE hexec hmono htd hsync
    hmult tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr hinv hcross hqaw hqh el hel' hel
    (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _)) hTH hslo (Nat.succ_le_succ hs1)
    (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›) (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›)
  have hfin := Restated.fin_old_anchor_before_succ_tick_of_hypotheses facts (hcross := hcross) S Sched x tE hexec
    hmono tGAT gap hgst hlen hthird hphase hrsW hr hinv hn'
  have hsR : M.view_freeze S.E s ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1 + 1)) - 1 := by
    have e1 := facts.sch.view_freeze_lt_vote_time_succ S.E s
    have e1' := facts.sch.slotStart_add_delta_eq_vote_time S.E (s + 1)
    have e3 := slotStart_succ S.E.Δ s
    have e2 : (Restated.Vocabulary.Execution.Setup.a M S (r + 1 + 1)) = slotStart S.E.Δ ((M.opening_slot S.hc (r + 1 + 1))) + 6 * S.E.Δ := by
      rw [← Restated.confirmation_time_opening_slot facts S (r + 1 + 1)]; exact (facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E _).symm
    rw [e2]; linarith [slotStart_mono S hs1]
  have hopos : 0 < (M.opening_slot S.hc (r + 1)) := facts.gr.opening_slot_pos S (Nat.succ_pos r)
  exact Restated.headsBelow_succ_of_eligible_afterPhase facts S Sched x hexec hsync hmult htd hmono
    (tR := (Restated.Vocabulary.Execution.Setup.a M S (r + 1 + 1)) - 1) hgst hcv hphase hthird hcs (Restated.delta_le_of_healingLengthη facts S hlen)
    (Restated.deliveredDescendantUnderFinalized_anchor facts S Sched x hn' hfin tGAT)
    (Restated.finalizedPreceqAtSteps_anchor facts S Sched x hn' hfin tGAT) hTH (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _))
    (lt_of_lt_of_le hopos hs0') hslo hsR hm hqaw hqh el hel' hel (hAB s hs0' hs1) hpath
    (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›) (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- From the step before round `r`'s second slot's vote instant up to the step after the
    round-`(r + 1)` tick, the justified block of every validator honest through that step is an
    ancestor of the round-`r` anchor `T`. -/
theorem justified_fromSecondSlot_ofJoint (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hsync : Restated.SynchronyFromWake M S x)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE)
    (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    (hprev : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.BasePreviousRoundSGCompatibleWithAnchorAtRound M S Sched x v r N
        (Restated.runAllPath M S Sched x v N) T)
    (hclear : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round) (n₀ : Nat),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S r)) →
      Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T)
    (hB' : Restated.BaseJustifiedHighAtSwitchRoundW M S Sched x tGAT tE gap)
    {n_W : Nat} (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    {T_W : NamedBlock V} (hAW : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.switchRound M S tE) T_W)
    (hJswitch : ∀ (v : V) (n₁ : Nat),
      M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) - 1
        ≤ (x[n₁].time : Int) →
      n₁ ≤ n_W → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J T_W.erase)
    {r : Round} {n : Nat} {T : NamedBlock V}
    (hr : Restated.switchRound M S tE ≤ r) (hTW : Block.Preceq T_W.erase T.erase)
    (hJ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x r n n_W T)
    {n' : Nat} (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1)))) :
    ∀ (v : V) (n₁ : Nat),
      M.vote_time S.E ((M.opening_slot S.hc r) + 1) - 1 ≤ (x[n₁].time : Int) →
      n₁ ≤ n' + 1 → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J T.erase := by
  intro v n₁ hlo hhi hvh
  by_cases hle : n_W ≤ n₁
  · exact Restated.justified_preceq_anchor_ofJoint facts S Sched x tE hexec hmono htd tGAT gap hgst hlen hsync
      hthird hphase hrsW hmult hcv hcom hrec hprev hclear hB' hnW hAW hr hTW hJ hn' v n₁ hle hhi
      hvh
  have hlt : n₁ ≤ n_W := Nat.le_of_lt (Nat.lt_of_not_le hle)
  by_cases hrW : r = Restated.switchRound M S tE
  · rw [hrW] at hlo
    exact preceq_trans_Preceq (hJswitch v n₁ hlo hlt hvh) hTW
  · exfalso
    have hr1 : Restated.switchRound M S tE + 1 ≤ r := Nat.lt_of_le_of_ne hr (Ne.symm hrW)
    have hd := S.E.Δ_pos
    have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
    have hRd : 12 * S.E.Δ ≤ 4 * (S.hc.R : Int) * S.E.Δ := by nlinarith
    have hvt1 : M.vote_time S.E ((M.opening_slot S.hc r) + 1) = (Restated.Vocabulary.Execution.Setup.a M S r) - S.E.Δ := by
      have h := Restated.vote_time_opening_slot_add facts S r 1
      rw [h]; push_cast; ring
    have hsucc := facts.gr.action_succ_eq_add_rounds S (Restated.switchRound M S tE)
    have hmonoA := Restated.action_mono facts S hr1
    obtain ⟨-, hnW0⟩ := Restated.tickStepAt_time facts x hnW
    have ht := Restated.time_mono_int facts S Sched x hlt
    rw [hvt1] at hlo
    linarith

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If every honest active member of the committee of a slot `s` of round `r + 1` votes for a
    descendant of a descendant `B` of the anchor, then the same holds at every slot from `s` to
    round `(r + 1 + k + 1)`'s second slot. -/
theorem headsBelow_persist_rounds (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (hcatch : Restated.CatchUpOnWake M S x)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hsync : Restated.SynchronyFromWake M S x)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE)
    (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hcs : Restated.committeeSleepinessW M S Sched tE)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    (hprev : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.BasePreviousRoundSGCompatibleWithAnchorAtRound M S Sched x v r N
        (Restated.runAllPath M S Sched x v N) T)
    (hclear : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round) (n₀ : Nat),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S r)) →
      Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T)
    (hB' : Restated.BaseJustifiedHighAtSwitchRoundW M S Sched x tGAT tE gap)
    {n_W : Nat} (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    {T_W : NamedBlock V} (hAW : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.switchRound M S tE) T_W)
    (hJswitch : ∀ (v : V) (n₁ : Nat),
      M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) - 1
        ≤ (x[n₁].time : Int) →
      n₁ ≤ n_W → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J T_W.erase)
    {B : Block V} :
    ∀ (k : Nat) (r : Round) (n : Nat) (T : NamedBlock V),
      Restated.switchRound M S tE ≤ r + 1 → Block.Preceq T_W.erase T.erase →
      Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x (r + 1) n n_W T →
      Block.Preceq T.erase B →
      ∀ s : Slot, (M.opening_slot S.hc (r + 1)) + 1 ≤ s → s ≤ (M.opening_slot S.hc (r + 1 + 1)) + 1 →
      Restated.HeadsBelow M S Sched x B s →
      ∀ s' : Slot, s ≤ s' → s' ≤ (M.opening_slot S.hc (r + 1 + k + 1)) + 1 →
        Restated.HeadsBelow M S Sched x B s' := by
  intro k
  induction k with
  | zero =>
    intro r n T hr hTW hJ hTB s hs0 hs1 hbase s' h0 h1
    obtain ⟨n', hn'⟩ := Restated.tick_field_at_succ facts S Sched x htd (r + 1)
    obtain ⟨n_prev, hnp0⟩ := hJ.prevTick
    have hnp : Restated.tickStepAt M x n_prev ((Restated.Vocabulary.Execution.Setup.a M S r)) := hnp0
    have hJT := Restated.justified_fromSecondSlot_ofJoint facts S Sched x tE hexec hmono htd tGAT gap hgst hlen
      hsync hthird hphase hrsW hmult hcv hcom hrec hprev hclear hB' hnW hAW hJswitch hr hTW hJ hn'
    have hcross : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1 + 1))) →
        Restated.StepFinalizedCrossingUnderAnchor M S Sched x (r + 1) n'' T :=
      fun n'' h => Restated.stepFinalizedCrossingUnderAnchor_of_afterSwitch facts S Sched x hr hnW hJ.toAfterPhaseInvariantOverActiveSetsSince
        (Restated.justified_preceq_anchor_ofJoint facts S Sched x tE hexec hmono htd tGAT gap hgst hlen hsync
          hthird hphase hrsW hmult hcv hcom hrec hprev hclear hB' hnW hAW hr hTW hJ h)
    exact Restated.headsBelow_roundStep (hrecvR := Restated.nextRoundReceipts_of_catchUp facts S Sched x hsync hcatch
        (Restated.gst_le_action_of_switchRound_le facts S tGAT tE gap hgst hlen
          (by first | assumption | exact le_trans hr (Nat.le_succ _) | exact le_trans hr (Nat.le_add_right _ _) | exact Nat.le_succ_of_le hr | omega))) facts S Sched x tE hexec hmono htd hsync hmult hcom tGAT gap hgst hlen
      hcv hthird hphase hrsW hcs hr hJ hn' hcross hJT hnp hTB hs0 hs1 hbase s' h0 h1
  | succ k ih =>
    intro r n T hr hTW hJ hTB s hs0 hs1 hbase s' h0 h1
    obtain ⟨n', hn'⟩ := Restated.tick_field_at_succ facts S Sched x htd (r + 1)
    obtain ⟨n_prev, hnp0⟩ := hJ.prevTick
    have hnp : Restated.tickStepAt M x n_prev ((Restated.Vocabulary.Execution.Setup.a M S r)) := hnp0
    have hJT := Restated.justified_fromSecondSlot_ofJoint facts S Sched x tE hexec hmono htd tGAT gap hgst hlen
      hsync hthird hphase hrsW hmult hcv hcom hrec hprev hclear hB' hnW hAW hJswitch hr hTW hJ hn'
    have hcross : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1 + 1))) →
        Restated.StepFinalizedCrossingUnderAnchor M S Sched x (r + 1) n'' T :=
      fun n'' h => Restated.stepFinalizedCrossingUnderAnchor_of_afterSwitch facts S Sched x hr hnW hJ.toAfterPhaseInvariantOverActiveSetsSince
        (Restated.justified_preceq_anchor_ofJoint facts S Sched x tE hexec hmono htd tGAT gap hgst hlen hsync
          hthird hphase hrsW hmult hcv hcom hrec hprev hclear hB' hnW hAW hr hTW hJ h)
    have hstep := Restated.headsBelow_roundStep (hrecvR := Restated.nextRoundReceipts_of_catchUp facts S Sched x hsync hcatch
        (Restated.gst_le_action_of_switchRound_le facts S tGAT tE gap hgst hlen
          (by first | assumption | exact le_trans hr (Nat.le_succ _) | exact le_trans hr (Nat.le_add_right _ _) | exact Nat.le_succ_of_le hr | omega))) facts S Sched x tE hexec hmono htd hsync hmult hcom tGAT gap hgst
      hlen hcv hthird hphase hrsW hcs hr hJ hn' hcross hJT hnp hTB hs0 hs1 hbase
    by_cases hle : s' ≤ (M.opening_slot S.hc (r + 1 + 1)) + 1
    · exact hstep s' h0 hle
    have hlt : (M.opening_slot S.hc (r + 1 + 1)) + 1 + 1 ≤ s' := Nat.lt_of_not_le hle
    obtain ⟨n_1, T_1, hJ1, hW1, h2⟩ := Restated.exists_anchor_chain_secondSlot facts S Sched x tE hexec hmono htd
      hcatch tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hrec hprev hclear
      hB' hnW hAW hJswitch hr hTW hJ 1
    have hT1 : Restated.HeadsBelow M S Sched x T_1.erase ((M.opening_slot S.hc (r + 1 + 1)) + 1) :=
      h2 (Nat.succ_pos 0)
    have hB2 : Restated.HeadsBelow M S Sched x B ((M.opening_slot S.hc (r + 1 + 1)) + 1) := hstep _ hs1 le_rfl
    have hr2 : Restated.switchRound M S tE ≤ r + 1 + 1 := le_trans hr (Nat.le_succ _)
    obtain ⟨t', -, ht's, -, hcs'⟩ :=
      Restated.exists_cone_cutoff_at_opening facts S Sched tE hmono hcom tGAT gap hgst hlen hphase hcs hr2
    have hpos : 0 < (M.opening_slot S.hc (r + 1 + 1)) + 1 := Nat.succ_pos _
    have hcomp := Restated.compatible_of_headsBelow_after facts S Sched x htd hcs' hpos
      (le_trans ht's (slotStart_mono S (Nat.le_succ_of_le (Nat.le_succ _)))) hT1 hB2
    rcases compatible_cases hcomp with hT1B | hBT1
    · have e : r + 1 + (k + 1) + 1 = r + 1 + 1 + k + 1 := by ring
      rw [e] at h1
      exact ih (r + 1) n_1 T_1 hr2 hW1 hJ1 hT1B _ le_rfl (Nat.succ_le_succ
        (by rw [facts.gr.opening_slot_succ S.hc (r + 1 + 1)]; exact Nat.le_add_right _ _)) hB2 s' (Nat.le_of_succ_le hlt) h1
    · have hanc := Restated.anchor_ancestorOfHonestHeadsFrom facts S Sched x tE hexec hmono htd hcatch tGAT gap
        hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hrec hprev hclear hB' hnW hAW
        hJswitch hr2 hW1 hJ1
      exact Restated.headsBelow_mono facts S Sched x hBT1 (hanc s' hlt)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- After the phase, a block `B` on one chain with the round-`r` anchor `T`, such that every honest
    active member of the committee of a slot `s` of round `r` from its second slot votes for a
    descendant of `B`, stays an ancestor of every honest vote at every slot from `s` on. -/
theorem ancestorOfHonestHeadsFrom_of_compatible_anchor (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (hcatch : Restated.CatchUpOnWake M S x)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hsync : Restated.SynchronyFromWake M S x)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE)
    (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hcs : Restated.committeeSleepinessW M S Sched tE)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    (hprev : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.BasePreviousRoundSGCompatibleWithAnchorAtRound M S Sched x v r N
        (Restated.runAllPath M S Sched x v N) T)
    (hclear : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round) (n₀ : Nat),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S r)) →
      Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T)
    (hB' : Restated.BaseJustifiedHighAtSwitchRoundW M S Sched x tGAT tE gap)
    {n_W : Nat} (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    {T_W : NamedBlock V} (hAW : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.switchRound M S tE) T_W)
    (hJswitch : ∀ (v : V) (n₁ : Nat),
      M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) - 1
        ≤ (x[n₁].time : Int) →
      n₁ ≤ n_W → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J T_W.erase)
    {r : Round} {n : Nat} {T : NamedBlock V}
    (hr : Restated.switchRound M S tE ≤ r) (hTW : Block.Preceq T_W.erase T.erase)
    (hJ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x r n n_W T)
    {s : Slot} (hs0 : (M.opening_slot S.hc r) + 1 ≤ s) (hs1 : s ≤ (M.opening_slot S.hc (r + 1)) + 1)
    {B : Block V} (hBT : Block.compatible B T.erase = true)
    (hB : Restated.HeadsBelow M S Sched x B s) :
    Restated.AncestorOfHonestHeadsFrom M S Sched x B s := by
  obtain ⟨r₀, rfl⟩ : ∃ r₀ : Round, r = r₀ + 1 :=
    ⟨r - 1, (Nat.succ_pred_eq_of_pos (Restated.round_pos_of_switch facts S tGAT tE gap hgst hlen hr)).symm⟩
  rcases compatible_cases hBT with hBT | hTB
  · intro s' hs'
    by_cases heq : s' = s
    · rw [heq]; exact hB
    have hlt : s < s' := lt_of_le_of_ne hs' (Ne.symm heq)
    have h2 : (M.opening_slot S.hc (r₀ + 1)) + 2 ≤ s' := Nat.succ_le_of_lt (lt_of_le_of_lt hs0 hlt)
    exact Restated.headsBelow_mono facts S Sched x hBT
      (Restated.anchor_ancestorOfHonestHeadsFrom facts S Sched x tE hexec hmono htd hcatch tGAT gap hgst hlen
        hsync hthird hphase hrsW hmult hcv hcs hcom hrec hprev hclear hB' hnW hAW hJswitch
        hr hTW hJ s' h2)
  · intro s' hs'
    exact Restated.headsBelow_persist_rounds facts S Sched x tE hexec hmono htd hcatch tGAT gap hgst hlen hsync
      hthird hphase hrsW hmult hcv hcs hcom hrec hprev hclear hB' hnW hAW hJswitch s' r₀ n T
      hr hTW hJ hTB s hs0 hs1 hB s' hs' (Nat.le_succ_of_le (facts.gr.le_opening_slot_far S.hc r₀ s'))

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- A block `G₀` that an honest round-`r` attestation names as confirmed, and that is a descendant
    of the round-`(r + 1)` anchor `T`, is an ancestor of the vote of every honest active committee
    member at every slot from round `(r + 1)`'s opening slot on. -/
theorem prevSG_ancestorOfHonestHeadsFrom (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (hcatch : Restated.CatchUpOnWake M S x)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hsync : Restated.SynchronyFromWake M S x)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE)
    (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hcs : Restated.committeeSleepinessW M S Sched tE)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    (hprev : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.BasePreviousRoundSGCompatibleWithAnchorAtRound M S Sched x v r N
        (Restated.runAllPath M S Sched x v N) T)
    (hclear : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round) (n₀ : Nat),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S r)) →
      Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T)
    (hB' : Restated.BaseJustifiedHighAtSwitchRoundW M S Sched x tGAT tE gap)
    {n_W : Nat} (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    {T_W : NamedBlock V} (hAW : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.switchRound M S tE) T_W)
    (hJswitch : ∀ (v : V) (n₁ : Nat),
      M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) - 1
        ≤ (x[n₁].time : Int) →
      n₁ ≤ n_W → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J T_W.erase)
    {r : Round} {n : Nat} {T : NamedBlock V}
    (hr : Restated.switchRound M S tE ≤ r + 1) (hTW : Block.Preceq T_W.erase T.erase)
    (hJ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x (r + 1) n n_W T)
    {n_prev : Nat} (hnp : Restated.tickStepAt M x n_prev ((Restated.Vocabulary.Execution.Setup.a M S r)))
    {v_2 : V} (hv_2 : v_2 ∈ Restated.HonRound M S Sched r) {a₂ : NamedAttestation V}
    (ha₂ : a₂.round = r) (hav₂ : a₂.val_index = v_2)
    (hsent₂ : (⟨v_2, NamedObject.attest a₂⟩ : SignedMsg V (NamedObject V)) ∈ x[n_prev + 1].sent)
    {G₀ : NamedBlock V} (hG₀ : G₀ ∈ (x[n_prev + 1][v_2].st).st.bodies)
    (hconf₂ : a₂.confirmed = some G₀.root) (hTG : Block.Preceq T.erase G₀.erase) :
    Restated.AncestorOfHonestHeadsFrom M S Sched x G₀.erase ((M.opening_slot S.hc (r + 1))) := by
  obtain ⟨n', hn'⟩ := Restated.tick_field_at_succ facts S Sched x htd (r + 1)
  have hJT := Restated.justified_fromSecondSlot_ofJoint facts S Sched x tE hexec hmono htd tGAT gap hgst hlen
    hsync hthird hphase hrsW hmult hcv hcom hrec hprev hclear hB' hnW hAW hJswitch hr hTW hJ hn'
  have hcross : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1 + 1))) →
      Restated.StepFinalizedCrossingUnderAnchor M S Sched x (r + 1) n'' T :=
    fun n'' h => Restated.stepFinalizedCrossingUnderAnchor_of_afterSwitch facts S Sched x hr hnW hJ.toAfterPhaseInvariantOverActiveSetsSince
      (Restated.justified_preceq_anchor_ofJoint facts S Sched x tE hexec hmono htd tGAT gap hgst hlen hsync
        hthird hphase hrsW hmult hcv hcom hrec hprev hclear hB' hnW hAW hr hTW hJ h)
  have hrange := Restated.prevSG_headsBelow_roundRange (hrecvR := Restated.nextRoundReceipts_of_catchUp facts S Sched x hsync hcatch
        (Restated.gst_le_action_of_switchRound_le facts S tGAT tE gap hgst hlen
          (by first | assumption | exact le_trans hr (Nat.le_succ _) | exact le_trans hr (Nat.le_add_right _ _) | exact Nat.le_succ_of_le hr | omega))) facts S Sched x tE hexec hmono htd hsync hmult hcom tGAT
    gap hgst hlen hcv hthird hphase hrsW hcs hr hJ hn' hcross hJT hnp hv_2 ha₂ hav₂ hsent₂
    hG₀ hconf₂ hTG
  have hle2 : (M.opening_slot S.hc (r + 1)) + 1 ≤ (M.opening_slot S.hc (r + 1 + 1)) + 1 := by
    rw [facts.gr.opening_slot_succ S.hc (r + 1)]
    exact Nat.succ_le_succ (Nat.le_add_right _ _)
  have hfrom := Restated.ancestorOfHonestHeadsFrom_of_compatible_anchor facts S Sched x tE hexec hmono htd hcatch
    tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hrec hprev hclear hB'
    hnW hAW hJswitch hr hTW hJ (s := (M.opening_slot S.hc (r + 1)) + 1) le_rfl hle2
    (Protocol.compatible_comm (compatible_of_preceq_c2b hTG))
    (hrange _ (Nat.le_succ _) hle2)
  intro s' hs'
  by_cases heq : s' = (M.opening_slot S.hc (r + 1))
  · rw [heq]
    exact hrange _ le_rfl (le_trans (Nat.le_succ _) hle2)
  · exact hfrom s' (Nat.succ_le_of_lt (lt_of_le_of_ne hs' (Ne.symm heq)))

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Every block `B` that a member of `HonRound S Sched (r + 1)` can grade at least 1 for round
    `r + 1` is an ancestor of the vote of every honest active committee member at every slot from
    round `(r + 1)`'s third slot on. -/
theorem graded_ancestorOfHonestHeadsFrom (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (hcatch : Restated.CatchUpOnWake M S x)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hsync : Restated.SynchronyFromWake M S x)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE)
    (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hcs : Restated.committeeSleepinessW M S Sched tE)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    (hprev : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.BasePreviousRoundSGCompatibleWithAnchorAtRound M S Sched x v r N
        (Restated.runAllPath M S Sched x v N) T)
    (hclear : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round) (n₀ : Nat),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S r)) →
      Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T)
    (hB' : Restated.BaseJustifiedHighAtSwitchRoundW M S Sched x tGAT tE gap)
    {n_W : Nat} (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    {T_W : NamedBlock V} (hAW : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.switchRound M S tE) T_W)
    (hJswitch : ∀ (v : V) (n₁ : Nat),
      M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) - 1
        ≤ (x[n₁].time : Int) →
      n₁ ≤ n_W → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J T_W.erase)
    {r : Round} {n : Nat} {T : NamedBlock V}
    (hr : Restated.switchRound M S tE ≤ r + 1) (hTW : Block.Preceq T_W.erase T.erase)
    (hJ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x (r + 1) n n_W T)
    {v : V} (hv : v ∈ Restated.HonRound M S Sched (r + 1)) (p : Protocol.Phase)
    (hp : M.domain S.E S.hc (r + 1) p ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)))
    {m : Nat} (hm : Restated.stepBeforeInstant M x m (M.domain S.E S.hc (r + 1) p))
    {B : Block V}
    (hB : M.gradeBool S.E (M.gradeView (M.toHealing (x[m][v].st).st.core))
      (x[m][v].st).st.core.F S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) p)
      (M.late S.E S.hc (r + 1) p) B ⇢ true) :
    Restated.AncestorOfHonestHeadsFrom M S Sched x B ((M.opening_slot S.hc (r + 1)) + 2) := by
  have hpv : v ∈ Restated.grade1PerformersW M S Sched (r + 1) :=
    Restated.mem_grade1PerformersW_of_honRound facts S Sched hmono hv
  have hBT : Block.compatible B T.erase = true := by
    by_cases hpg : p = Protocol.Phase.g1
    · subst hpg; exact (joint_toTop_hp hJ).grade1Performers v hpv m hm B true hB rfl
    · exact (joint_toTop_hp hJ).grade1 v hv p hpg hp m hm B true hB rfl
  rcases compatible_cases hBT with hBT | hTB
  · exact Restated.ancestorOfHonestHeadsFrom_of_preceq facts S Sched x hBT
      (Restated.anchor_ancestorOfHonestHeadsFrom facts S Sched x tE hexec hmono htd hcatch tGAT gap hgst hlen
        hsync hthird hphase hrsW hmult hcv hcs hcom hrec hprev hclear hB' hnW hAW hJswitch
        hr hTW hJ)
  · obtain ⟨n_prev, hnp0⟩ := hJ.prevTick
    have hnp : Restated.tickStepAt M x n_prev ((Restated.Vocabulary.Execution.Setup.a M S r)) := hnp0
    have hGr : ∃ v_1 ∈ Restated.HonRound M S Sched (r + 1 - 1), ∃ a : NamedAttestation V,
        a.round = r + 1 - 1 ∧ a.val_index = v_1 ∧
        (⟨v_1, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n_prev + 1].sent ∧
        ∃ C : NamedBlock V, C ∈ (x[n_prev + 1][v_1].st).st.bodies ∧ a.confirmed = some C.root ∧
          Block.Preceq B C.erase := by
      by_cases hpg : p = Protocol.Phase.g1
      · subst hpg; exact hJ.gradedUnderPrevSGPerformers n_prev hnp v hpv m hm B true hB rfl
      · exact hJ.gradedUnderPrevSG n_prev hnp v hv p hpg hp m hm B true hB rfl
    obtain ⟨v_2, hv_2, a₂, ha₂, hav₂, hsent₂, G₀, hG₀, hconf₂, hBG⟩ := hGr
    exact Restated.ancestorOfHonestHeadsFrom_of_preceq facts S Sched x hBG
      (Restated.ancestorOfHonestHeadsFrom_mono facts S Sched x (Nat.le_add_right _ _)
        (Restated.prevSG_ancestorOfHonestHeadsFrom facts S Sched x tE hexec hmono htd hcatch tGAT gap hgst hlen
          hsync hthird hphase hrsW hmult hcv hcs hcom hrec hprev hclear hB' hnW hAW hJswitch
          hr hTW hJ hnp hv_2 ha₂ hav₂ hsent₂ hG₀ hconf₂ (preceq_trans_Preceq hTB hBG)))

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- `EligibleDescendantOfAnchorPersists` holds on the premises of
    `afterPhaseJointRound_of_premises`. -/
theorem eligibleDescendantOfAnchorPersists_ofJoint (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (hcatch : Restated.CatchUpOnWake M S x)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hsync : Restated.SynchronyFromWake M S x)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE)
    (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hcs : Restated.committeeSleepinessW M S Sched tE)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    (hprev : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.BasePreviousRoundSGCompatibleWithAnchorAtRound M S Sched x v r N
        (Restated.runAllPath M S Sched x v N) T)
    (hclear : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round) (n₀ : Nat),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S r)) →
      Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T)
    (hB' : Restated.BaseJustifiedHighAtSwitchRoundW M S Sched x tGAT tE gap)
    {n_W : Nat} (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    {T_W : NamedBlock V} (hAW : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.switchRound M S tE) T_W)
    (hJswitch : ∀ (v : V) (n₁ : Nat),
      M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) - 1
        ≤ (x[n₁].time : Int) →
      n₁ ≤ n_W → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J T_W.erase) :
    Restated.EligibleDescendantOfAnchorPersists M S Sched x tE n_W T_W := by
  intro r n T hr hTW hJ s _ hs0 hs1 m hm v hvaw hvh H el hel' hel hTH
  obtain ⟨r₀, rfl⟩ : ∃ r₀ : Round, r = r₀ + 1 :=
    ⟨r - 1, (Nat.succ_pred_eq_of_pos (Restated.round_pos_of_switch facts S tGAT tE gap hgst hlen hr)).symm⟩
  obtain ⟨n', hn'⟩ := Restated.tick_field_at_succ facts S Sched x htd (r₀ + 1)
  obtain ⟨n_prev, hnp0⟩ := hJ.prevTick
  have hnp : Restated.tickStepAt M x n_prev ((Restated.Vocabulary.Execution.Setup.a M S r₀)) := hnp0
  have hJT := Restated.justified_fromSecondSlot_ofJoint facts S Sched x tE hexec hmono htd tGAT gap hgst hlen
    hsync hthird hphase hrsW hmult hcv hcom hrec hprev hclear hB' hnW hAW hJswitch hr hTW hJ hn'
  have hcross : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r₀ + 1 + 1))) →
      Restated.StepFinalizedCrossingUnderAnchor M S Sched x (r₀ + 1) n'' T :=
    fun n'' h => Restated.stepFinalizedCrossingUnderAnchor_of_afterSwitch facts S Sched x hr hnW hJ.toAfterPhaseInvariantOverActiveSetsSince
      (Restated.justified_preceq_anchor_ofJoint facts S Sched x tE hexec hmono htd tGAT gap hgst hlen hsync
        hthird hphase hrsW hmult hcv hcom hrec hprev hclear hB' hnW hAW hr hTW hJ h)
  have hsucc := Restated.headsBelow_succ_of_eligible_round (hrecvR := Restated.nextRoundReceipts_of_catchUp facts S Sched x hsync hcatch
        (Restated.gst_le_action_of_switchRound_le facts S tGAT tE gap hgst hlen
          (by first | assumption | exact le_trans hr (Nat.le_succ _) | exact le_trans hr (Nat.le_add_right _ _) | exact Nat.le_succ_of_le hr | omega))) facts S Sched x tE hexec hmono htd hsync hmult hcom
    tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr hJ hn' hcross hJT hnp hs0 hs1 hm hvaw
    hvh el hel' hel hTH
  exact Restated.ancestorOfHonestHeadsFrom_of_compatible_anchor facts S Sched x tE hexec hmono htd hcatch tGAT
    gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hrec hprev hclear hB' hnW hAW
    hJswitch hr hTW hJ (Nat.le_succ_of_le hs0) (Nat.succ_le_succ hs1)
    (Protocol.compatible_comm (compatible_of_preceq_c2b hTH)) hsucc

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- After the phase, the `live_confirmed` that an honest reader's confirmation tick writes at a slot
    `s` from `o_{r₀} + 2` on is an ancestor of the vote of every honest active committee member at
    every slot from `s + 1` on. -/
theorem live_confirmed_ancestorOfHonestHeadsFrom_ofJoint (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (hcatch : Restated.CatchUpOnWake M S x)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hsync : Restated.SynchronyFromWake M S x)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE)
    (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hcs : Restated.committeeSleepinessW M S Sched tE)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    (hprev : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.BasePreviousRoundSGCompatibleWithAnchorAtRound M S Sched x v r N
        (Restated.runAllPath M S Sched x v N) T)
    (hclear : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round) (n₀ : Nat),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S r)) →
      Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T)
    (hB' : Restated.BaseJustifiedHighAtSwitchRoundW M S Sched x tGAT tE gap)
    {n_W : Nat} (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    {T_W : NamedBlock V} (hAW : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.switchRound M S tE) T_W)
    (hJswitch : ∀ (v : V) (n₁ : Nat),
      M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) - 1
        ≤ (x[n₁].time : Int) →
      n₁ ≤ n_W → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J T_W.erase)
    {r₀ : Round} {n₀ : Nat} {T₀ : NamedBlock V}
    (hr₀ : Restated.switchRound M S tE ≤ r₀) (hTW₀ : Block.Preceq T_W.erase T₀.erase)
    (hJ₀ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x r₀ n₀ n_W T₀)
    {s : Slot} (hs0 : (M.opening_slot S.hc r₀) + 2 ≤ s)
    {m : Nat} (hm : Restated.tickStepAt M x m (M.confirmation_time S.E s)) {v : V}
    (hvaw : v ∈ Sched.awakeThroughout (slotStart S.E.Δ s - S.E.Δ)
      (M.confirmation_time S.E s))
    (hvh : HonestThroughTime Sched (M.confirmation_time S.E s) v)
    (hrun : M.awake_for_grade2 (Setup.alwaysAwake S) v
      (Record.wakeStage M Sched (M.confirmation_time S.E s) x[m] v) (M.round_of S.hc (s + 1))) :
    Restated.AncestorOfHonestHeadsFrom M S Sched x (x[m + 1][v].st).st.core.live_confirmed (s + 1) :=
  Restated.live_confirmed_ancestorOfHonestHeadsFrom facts S Sched x tE hexec hmono htd hcatch tGAT gap hgst hlen
    hsync hthird hphase hrsW hmult hcv hcs hcom hrec hprev hclear hB' hnW hAW hJswitch hr₀
    hTW₀ hJ₀
    (Restated.eligibleDescendantOfAnchorPersists_ofJoint facts S Sched x tE hexec hmono htd hcatch tGAT gap hgst
      hlen hsync hthird hphase hrsW hmult hcv hcs hcom hrec hprev hclear hB' hnW hAW
      hJswitch)
    hs0 hm hvaw hvh hrun

end

section
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation

local macro "p83% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_83)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

end

end DecoupledConsensusModel.Sts.Restated
