import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bK_ConfirmedAgree
import Proofs.Claims.Restated.Claim13bK_ConfirmedRecord
import Proofs.Claims.Restated.Claim13bK_ConfirmedRecordReaders
import Proofs.Claims.Restated.Claim13bK_ConfirmedSettle
import Proofs.Claims.Restated.Claim13bK_HeadsPersist
import Proofs.Claims.Restated.Claim13bK_LiveConfirmedSlots
import Proofs.Claims.Restated.Claim13bK_PrevHeadsStep
import Proofs.Claims.Restated.Claim13bSGCompatible
import Proofs.Claims.Restated.Claim13bStepConeIter
import Proofs.Claims.Restated.Claim13bStepKitConfirm
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bStepKitRelay
import Proofs.Claims.Restated.Claim13bW_Schedule
import Proofs.Claims.Restated.Claim13beRoute3_15
import Proofs.Claims.Restated.ProcessedFlip
import Proofs.Claims.Restated.Redelivery
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_NamedNode
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActive
import Model.Conditions.Claim13bInvariantActiveJoint
import Model.Conditions.Claim13bInvariantActiveSinceW
import Model.Conditions.Claim13bK_ConfirmedRecord
import Model.Conditions.Claim13bK_ConfirmedSettle
import Model.Conditions.Claim13bK_ConfirmedWake
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13bStepCone
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_74
import Model.Conditions.Claim13beRoute3_83
import Model.Conditions.RunAll
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13bd
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Sts_Spec2Claims_Claim13bf
import Model.Conditions.Sts_Spec2Claims_ClaimConfirmedAfterHealing
import Model.Conditions.Sts_VocabularyAssumptions
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Vocabulary.Protocol.Grades
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Protocol_Grades_Main
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bK_ConfirmedWake

/-!
# Confirmed records of a validator that sleeps and wakes

That the stable and confirmed records of an honest validator stay ancestors of every honest head
after the tick at `S.a (rW + 1)`, also across sleep and wake: the store clock, the votes and
eligibility of a slot slept through, the awake provenance of phase results, and the reduction of
`RecordsSettledAtActionTicks` and `ConfirmedMonotoneAfterHealing` to `RecordsSettledAtSettleTick`.
Stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

local macro "p83% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_83)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "pCR% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13bK_ConfirmedRecord)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "pW% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13bK_ConfirmedStrongRoundWindow)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

/-! ## Helpers -/

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog

open scoped DC in
/-- If `f <$> m` can return `b`, then `m` can return some `a` with `f a = b`. -/
private theorem returns_map_elim_cw {α β : Type} (f : α → β) (m : DC.NDRE α) (b : β)
    (h : (f <$> m) ⇢ b) : ∃ a, m ⇢ a ∧ f a = b := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image] at h
  obtain ⟨e, he, hb⟩ := h
  cases e with
  | ok a => exact ⟨a, he, by simpa [Except.map] using hb⟩
  | error err => simp [Except.map] at hb

open scoped DC in
/-- If `m` can return `a`, then `f <$> m` can return `f a`. -/
private theorem returns_map_intro_cw {α β : Type} (f : α → β) (m : DC.NDRE α) (a : α)
    (h : m ⇢ a) : (f <$> m) ⇢ f a := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image]
  exact ⟨_, h, rfl⟩

open scoped DC in
/-- `m >>= k` can return `b` exactly when `m` can return some `a` from which `k a` can return `b`. -/
private theorem returns_bind_iff_cw {α β : Type} (m : DC.NDRE α) (k : α → DC.NDRE β) (b : β) :
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
private theorem returns_lift_iff_cw {α : Type} (s : Set α) (a : α) :
    (ExceptT.lift s : DC.NDRE α) ⇢ a ↔ a ∈ s := by
  unfold Record.Returns
  simp only [ExceptT.run_lift, Set.fmap_eq_image, Set.mem_image]
  constructor
  · rintro ⟨a', ha', he⟩
    cases he
    exact ha'
  · intro h
    exact ⟨a, h, rfl⟩

/-- After the tick at `τ` at step `k`, either `w` is awake at `τ` and its store clock is `τ`, or its
    store clock is the one it had before step `k`. -/
private theorem clock_succ_of_tick_awake_cw (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (w : V) {k τ : Nat}
    (hl : x.lbl k = AtomicAction.tickAllAwake τ) :
    (w ∈ Sched.awake (τ : Int) ∧ (x[k + 1][w].st).st.core.t = (τ : Int)) ∨
      (x[k + 1][w].st).st.core.t = (x[k][w].st).st.core.t := by
  have hs : AtomicStep (Record.protocolOf M S) Sched (x.lbl k) x[k] x[k + 1] := x.step k
  rw [hl] at hs
  obtain ⟨-, w', tk, hwake, htick, hc⟩ := hs
  by_cases hv : w ∈ Sched.awake (τ : Int) \ Sched.adv (τ : Int)
  · have hwst : ((w' w).state).st = (x[k][w].st).st := by
      have hww := hwake w
      unfold TickAllAwakeWake at hww
      by_cases he : w ∈ entrants Sched τ
      · rw [if_pos he] at hww
        rw [Record.protocolOf_step_wake M S hww]
        exact (facts.nd.wake_st_record _).1
      · rw [if_neg he] at hww
        rw [hww]
    have hx1 : x[k + 1][w].st = (tk w).state := by
      have h2 : x[k + 1][w] = (tickAllAwakeUpdate Sched τ x[k] w' tk)[w] := by rw [hc]
      rw [h2, tickAllAwakeUpdate_getElem_react hv]
    rcases Record.protocolOf_step_tick M S (htick w hv) with ⟨-, out₁, hout, hst⟩ | ⟨-, hst⟩
    · refine Or.inl ⟨(Finset.mem_sdiff.1 hv).1, ?_⟩
      rw [hx1, hst]
      exact (facts.nd.tick_clock (Setup.alwaysAwake S) w _ (τ : Int) out₁ hout).1
    · refine Or.inr ?_
      rw [hx1, hst, hwst]
  · refine Or.inr ?_
    have h2 : x[k + 1][w] = (tickAllAwakeUpdate Sched τ x[k] w' tk)[w] := by rw [hc]
    rw [h2, tickAllAwakeUpdate_getElem_st_of_not_react hv]

/-- The support cutoff of slot `0` is at most `6 * Δ`, and the support cutoff of slot `s + 1` is
    `4 * Δ * (s + 1) + 2 * Δ`. -/
private theorem support_cutoff_closed_cw (facts : Record.Facts M) (E : Env V) :
    M.support_cutoff E 0 ≤ 6 * E.Δ ∧
      ∀ s : Slot, M.support_cutoff E (s + 1) = 4 * E.Δ * ((s + 1 : Nat) : Int) + 2 * E.Δ := by
  refine ⟨?_, fun s => ?_⟩
  · have h := facts.sch.Sts_support_cutoff_le_confirmation_time E 0
    rw [(pCR% confirmation_time_closed_cr) facts] at h
    simpa using h
  · rw [← facts.sch.confirmation_time_eq_support_cutoff_succ E s,
      (pCR% confirmation_time_closed_cr) facts]
    push_cast
    ring

/-- Setting the clock of a store does not change which blocks pass the confirmation eligibility test
    for slot `s`. -/
private theorem confEligible_setClock_cw (facts : Record.Facts M) (E : Env V) (st : M.NS)
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

/-- For every outcome `D` of the confirmation update of `st` at slot `s` under `contract`, there is
    a block `cand` such that `D`'s `latest_confirmed` is `floor_on_stable` of `D`'s `latest_stable`,
    `cand` and `st`'s `latest_confirmed`, and `cand` is `st`'s `latest_confirmed`; or some outcome
    `el` of `st`'s slot-`s` eligibility test has `el D.live_confirmed = true` and `cand` is
    `advance_confirmed` of `st`'s `latest_confirmed` with `D`'s `live_confirmed`; or `cand` is
    `advance_confirmed` of it with a block `G` that the contract's SG candidate selection at `st`
    and `s` can return as `some G`. -/
private theorem update_confirmation_with_latest_confirmed_eligible_cw (facts : Record.Facts M)
    (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (st : M.S) (s : Slot)
    (D : M.S) (hD : M.update_confirmation_with contract E hc st s ⇢ D) :
    ∃ cand : Block V,
      D.latest_confirmed = M.floor_on_stable D.latest_stable cand st.latest_confirmed ∧
      (cand = st.latest_confirmed ∨
        (∃ el : Block V → Bool, Restated.Vocabulary.Protocol.confEligible M E st s ⇢ el ∧
          el D.live_confirmed = true ∧
          cand = M.advance_confirmed st.latest_confirmed D.live_confirmed) ∨
        ∃ G : Block V, contract.confirmationSG E hc st.toHealing s ⇢ some G ∧
          cand = M.advance_confirmed st.latest_confirmed G) := by
  classical
  obtain ⟨tm, htm⟩ := facts.sto.tau_nonempty st
  obtain ⟨R, hR⟩ := facts.fc.get_sg_root_with_nonempty contract E hc st.toHealing
    (M.round_of hc st.s)
  obtain ⟨score, hscore⟩ : ∃ score : Block V → ℕ, ∀ B, M.goldfish_score E st.T
      ((beforeCutoff tm (M.support_cutoff E s) (st.pool s)).filter (fun u =>
        M.no_second_vote_in (beforeCutoff st.timestamp_vote (M.confirmation_time E s)
          (st.pool s)) u = true))
      ((beforeCutoff tm (M.support_cutoff E s) (st.pool s)).filter (fun u =>
        M.no_second_vote_in (beforeCutoff st.timestamp_vote (M.confirmation_time E s)
          (st.pool s)) u = true))
      s B ⇢ score B :=
    ⟨fun B => (facts.fc.goldfish_score_nonempty _ _ _ _ _ B).choose,
      fun B => (facts.fc.goldfish_score_nonempty _ _ _ _ _ B).choose_spec⟩
  obtain ⟨W, hW⟩ := facts.fc.ghost_nonempty R (M.get_filtered_block_tree st.toHealing.toFG) score
    (fun B => decide (M.voters_count E (beforeCutoff st.timestamp_vote (M.confirmation_time E s)
      (st.pool s)) s < 2 * score B))
  obtain ⟨cand, hfl, hcases⟩ := facts.hd.update_confirmation_with_latest_confirmed_cases
    contract E hc st s tm htm R hR score hscore W hW D hD
  refine ⟨cand, hfl, ?_⟩
  rcases hcases with h | ⟨hel, h⟩ | h
  · exact Or.inl h
  · right; left
    have hlive := facts.hd.update_confirmation_with_live_confirmed_of_eligible contract E hc st s
      tm htm R hR score hscore W hW hel D hD
    have hvv : Restated.Vocabulary.Protocol.confVotes M E st s ⇢
        (beforeCutoff tm (M.support_cutoff E s) (st.pool s)).filter
          (fun u => M.no_second_vote_in (Restated.Vocabulary.Protocol.confLate M E st s) u = true) :=
      returns_map_intro_cw _ _ _ (returns_map_intro_cw _ _ _ htm)
    refine ⟨fun B => decide (Restated.Vocabulary.Protocol.confCount M E st s < 2 * score B), ?_, ?_, ?_⟩
    · exact (returns_bind_iff_cw _ _ _).2 ⟨_, hvv, (returns_bind_iff_cw _ _ _).2
        ⟨score, (returns_lift_iff_cw _ _).2 hscore, (Record.returns_pure _ _).2 rfl⟩⟩
    · rw [hlive]; exact hel
    · rw [hlive]; exact h
  · exact Or.inr (Or.inr h)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog

/-- After any number of steps, a validator's store clock is `0` or a time at which the schedule has
    that validator awake. -/
theorem clock_eq_zero_or_awake (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V) (k : Nat) :
    (x[k][v].st).st.core.t = 0 ∨ v ∈ Sched.awake (x[k][v].st).st.core.t := by
  induction k with
  | zero =>
      left
      have h1 := Restated.clock_le_time_sts facts S Sched x 0 v
      have h2 := Restated.clock_nonneg_sts facts S Sched x 0 v
      have h3 : x[0].time = 0 := x.init.1
      rw [h3] at h1
      exact le_antisymm (by exact_mod_cast h1) h2
  | succ k ih =>
      cases hl : x.lbl k with
      | tickAllAwake τ =>
          rcases clock_succ_of_tick_awake_cw facts S Sched x v hl with ⟨haw, hst⟩ | hst
          · right
            rw [hst]
            exact haw
          · rw [hst]; exact ih
      | deliver p m =>
          by_cases hp : p = v
          · subst hp
            rcases Restated.st_succ_of_deliver facts S Sched x hl with h | ⟨-, h⟩
            · rw [(facts.nd.process_clock (Setup.alwaysAwake S) (x[k][p].st) m.msg _ h).1]
              exact ih
            · rw [h]; exact ih
          · rw [Restated.getElem_succ_of_deliver_ne facts S Sched x hl hp]; exact ih
      | custom _ ev => exact ev.elim
      | adversarial p m =>
          rw [Restated.getElem_succ_of_adversarial facts S Sched x hl]; exact ih
      | forward p m =>
          rw [Restated.getElem_succ_of_forward facts S Sched x hl]; exact ih

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog

/-- If slot `s` starts at a positive time and `v` is asleep at every time from `slotStart s` to
    before slot `s`'s support cutoff, then after any number of steps no outcome of the votes `v`'s
    store counts at slot `s`'s confirmation has a member. -/
theorem confVotes_eq_empty_of_asleep (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (v : V) (m : Nat) {s : Slot}
    (hpos : 0 < slotStart S.E.Δ s)
    (hasleep : ∀ t : Int, slotStart S.E.Δ s ≤ t → t < M.support_cutoff S.E s →
      v ∉ Sched.awake t) :
    ∀ votes : Finset (GoldfishVote V),
      Restated.Vocabulary.Protocol.confVotes M S.E (x[m][v].st).st.core s ⇢ votes →
      ∀ u : GoldfishVote V, u ∉ votes := by
  intro votes hvotes u hu
  obtain ⟨e, he, rfl⟩ := returns_map_elim_cw _ _ _ hvotes
  obtain ⟨tm, htm, rfl⟩ := returns_map_elim_cw _ _ _ he
  have hearly := (mem_beforeCutoff_iff _ _ _ _).mp (Finset.mem_filter.mp hu).1
  have hpool : u ∈ (M.store_pool (x[m][v].st).st.core s) := hearly.1
  have hslot : u.slot = s := Restated.slot_of_mem_pool_sts facts S Sched x m v hpool
  rw [← hslot] at hpool
  obtain ⟨i, him, -, h0, h1⟩ := Restated.accepts_of_mem_pool facts S Sched x hpool
  obtain ⟨hst, hge, -⟩ := Restated.stamp_eq_clock_of_flip_gfVote facts S Sched x h0 h1
  have hst' := Restated.stamp_mono_sts facts S Sched x v (Nat.succ_le_of_lt him) hst
  obtain ⟨τ, hτ, hτlt⟩ :=
    exists_stamp_of_stampedBefore (facts.sto.stampedBefore_vote_of_tau _ tm htm hearly.2)
  have hτeq : τ = (((x[i + 1][v].st).st.core.t : Int) : Stamp) :=
    Option.some_inj.mp (hτ.symm.trans hst')
  rw [hτeq] at hτlt
  have hlt : (x[i + 1][v].st).st.core.t < M.support_cutoff S.E s :=
    WithBot.coe_lt_coe.mp hτlt
  rw [hslot] at hge
  rcases Restated.clock_eq_zero_or_awake facts S Sched x v (i + 1) with h | h
  · rw [h] at hge; exact absurd hge (not_le.mpr hpos)
  · exact hasleep _ hge hlt h

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog

/-- Under the hypotheses of `confVotes_eq_empty_of_asleep`, after any number of steps every outcome
    `el` of `v`'s slot-`s` eligibility test has `el H = false`, for every block `H`. -/
theorem confEligible_false_of_asleep (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (v : V) (m : Nat) {s : Slot}
    (hpos : 0 < slotStart S.E.Δ s)
    (hasleep : ∀ t : Int, slotStart S.E.Δ s ≤ t → t < M.support_cutoff S.E s →
      v ∉ Sched.awake t)
    (H : Block V) : ∀ el : Block V → Bool,
      Restated.Vocabulary.Protocol.confEligible M S.E (x[m][v].st).st.core s ⇢ el →
      el H = false := by
  classical
  intro el hel
  obtain ⟨u, hu, hel⟩ := (returns_bind_iff_cw _ _ _).1 hel
  obtain ⟨sc, hsc, hel⟩ := (returns_bind_iff_cw _ _ _).1 hel
  have hsc' : ∀ B, M.goldfish_score S.E (x[m][v].st).st.core.T u u s B ⇢ sc B :=
    (returns_lift_iff_cw _ _).1 hsc
  obtain rfl := (Record.returns_pure _ _).1 hel
  have hemp : u = ∅ := Finset.eq_empty_of_forall_notMem
    (Restated.confVotes_eq_empty_of_asleep facts S Sched x v m hpos hasleep u hu)
  subst hemp
  obtain ⟨R, hR⟩ := facts.fc.raw_supporters_nonempty (x[m][v].st).st.core.T
    (∅ : Finset (GoldfishVote V)) ∅ s H
  have hcard := facts.fc.Numerator_score_eq_supporters (∅ : Finset (GoldfishVote V))
    (∅ : Finset (GoldfishVote V)) ∅ (Finset.Subset.refl _) (Finset.filter_empty _).symm S.E
    (x[m][v].st).st.core.T s H (sc H) (hsc' H) R hR
  have hR0 : R = ∅ := by
    refine Finset.eq_empty_of_forall_notMem (fun y hy => ?_)
    obtain ⟨-, u', hu', -⟩ := (facts.fc.mem_supporters_iff (_E := S.E) R hR
      (fun u => (facts.fc.targets_under_nonempty (x[m][v].st).st.core.T H u).choose)
      (fun u => (facts.fc.targets_under_nonempty (x[m][v].st).st.core.T H u).choose_spec)).1 hy
    exact absurd ((facts.sch.mem_votes_by_iff _ _ _).1 hu').1 (Finset.notMem_empty _)
  rw [hR0, Finset.card_empty] at hcard
  show decide (_ < 2 * sc H) = false
  rw [hcard]
  exact decide_eq_false (by omega)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog

/-- If every phase result of `c` was written while `v` was awake at its domain time, the same holds
    of `c` clipped to any block. -/
theorem framePhaseAwakeProvenance_clipCache (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) {v : V}
    {c : M.Cache} (F : Block V) (h : Restated.FramePhaseAwakeProvenance M S Sched v c) :
    Restated.FramePhaseAwakeProvenance M S Sched v (M.clipCache F c) := by
  intro r₁ p root hr
  obtain ⟨root₀, h₀, -⟩ := facts.gr.phaseResult_clipCache hr
  exact h r₁ p root₀ h₀

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog

/-- If every phase result of `c` was written while `v` was awake at its domain time, and `v` is
    awake at `t`, the same holds of every cache a phase tick at `t` can leave. -/
theorem framePhaseAwakeProvenance_onPhaseTick (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) {v : V}
    (st : M.HS) {t : Int} (c : M.Cache)
    (haw : v ∈ Sched.awake t) (h : Restated.FramePhaseAwakeProvenance M S Sched v c) :
    ∀ c' : M.Cache, M.onPhaseTick S.E S.hc st t c ⇢ c' →
      Restated.FramePhaseAwakeProvenance M S Sched v c' := by
  intro c' hc' r₁ p root hr
  rcases facts.gr.phaseResult_onPhaseTick S.E S.hc st t c c' hc' hr
      (fun B => (facts.gr.gradeBool_nonempty S.E (M.gradeView st) st.toFG.F S.hc.η_SG r₁
        (M.early S.E S.hc r₁ p) (M.late S.E S.hc r₁ p) B).choose)
      (fun B => (facts.gr.gradeBool_nonempty S.E (M.gradeView st) st.toFG.F S.hc.η_SG r₁
        (M.early S.E S.hc r₁ p) (M.late S.E S.hc r₁ p) B).choose_spec) with
    ⟨root₀, h₀, -⟩ | ⟨ht, -⟩
  · exact h r₁ p root₀ h₀
  · rw [← ht]; exact haw

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog

/-- At every step, every phase result `v`'s cache holds for a round and a phase was written while
    `v` was awake at that phase's domain time. -/
theorem framePhaseAwakeProvenance_sts (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (v : V) (k : Nat) :
    Restated.FramePhaseAwakeProvenance M S Sched v (x[k][v].st).cache := by
  induction k with
  | zero =>
      intro r₁ p root hr
      rw [Record.st_zero M S Sched x v] at hr
      exact absurd hr (facts.nd.initial_cache_phaseResult_ne (Setup.alwaysAwake S) v r₁ p root)
  | succ k ih =>
      cases hl : x.lbl k with
      | tickAllAwake τ =>
          rcases Restated.st_succ_of_tick facts S Sched x v hl with
            ⟨haw, -, out₁, hout, hst⟩ | hst
          · obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc
              (x[k][v].st).st.core.toHealing (τ : Int) (x[k][v].st).cache
            have _hr_s1 := Record.reachedNode_wakeStage facts S Sched x (k) v (↑τ)
            have hcw := Restated.Vocabulary.Proofs.NamedNode.tick_cache_eq facts _ v _ _ out₁ hout c
              (by rw [Record.wakeStage_st facts, Record.wakeStage_cache facts]; exact hc)
            rw [hst, hcw]
            exact Restated.framePhaseAwakeProvenance_clipCache facts S Sched _
              (Restated.framePhaseAwakeProvenance_onPhaseTick facts S Sched _ _
                (Finset.mem_sdiff.1 haw).1 ih c hc)
          · rw [hst, Record.wakeStage_cache facts]; exact ih
      | deliver p m =>
          by_cases hp : p = v
          · subst hp
            rcases Restated.st_succ_of_deliver facts S Sched x hl with hproc | ⟨-, hst⟩
            · have _hr_s2 := Record.reachedNode_sts facts S Sched x (k) p
              rw [facts.nd.process_cache_eq _ _ _ _ hproc]
              exact Restated.framePhaseAwakeProvenance_clipCache facts S Sched _ ih
            · rw [hst]; exact ih
          · rw [Restated.getElem_succ_of_deliver_ne facts S Sched x hl hp]; exact ih
      | custom _ ev => exact ev.elim
      | adversarial p m =>
          rw [Restated.getElem_succ_of_adversarial facts S Sched x hl]; exact ih
      | forward p m =>
          rw [Restated.getElem_succ_of_forward facts S Sched x hl]; exact ih

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog

/-- If the round `r'` of slot `s + 1` is positive, then `S.a (r' − 1)` is at or before
    `slotStart s − Δ`. -/
theorem action_pred_round_of_succ_le (facts : Record.Facts M) (S : Setup V) (s : Slot)
    (hpos : 0 < (M.round_of S.hc (s + 1))) :
    (Restated.Vocabulary.Execution.Setup.a M S ((M.round_of S.hc (s + 1)) - 1)) ≤ slotStart S.E.Δ s - S.E.Δ := by
  have hd := S.E.Δ_pos
  obtain ⟨r₁, hr₁⟩ : ∃ r₁ : Round, (M.round_of S.hc (s + 1)) = r₁ + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
  have hlo := facts.gr.opening_slot_round_of_le_slot S.hc (s + 1)
  rw [hr₁, (pCR% opening_slot_closed_cr) facts, Nat.succ_mul] at hlo
  have hR3 := S.hc.R_ge_three
  have hN : r₁ * S.hc.R + 2 ≤ s := nat_add_two_le_of_add_le_succ hlo hR3
  have hI : ((r₁ * S.hc.R : Nat) : Int) + 2 ≤ (s : Int) := by exact_mod_cast hN
  push_cast at hI
  rw [hr₁, Nat.add_sub_cancel, (pCR% action_closed_cr) facts, slotStart_closed]
  nlinarith

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog

/-- Slot `s`'s confirmation time is strictly before `S.a (r' + 1)`, for the round `r'` of slot
    `s + 1`. -/
theorem confirmation_time_lt_action_round_of_succ (facts : Record.Facts M) (S : Setup V) (s : Slot) :
    M.confirmation_time S.E s < (Restated.Vocabulary.Execution.Setup.a M S ((M.round_of S.hc (s + 1)) + 1)) := by
  have hd := S.E.Δ_pos
  have hhi := facts.gr.lt_opening_slot_round_of_succ S.hc (s + 1)
  rw [(pCR% opening_slot_closed_cr) facts] at hhi
  have hI : (s : Int) + 1 < ((((M.round_of S.hc (s + 1)) + 1) * S.hc.R : Nat) : Int) := by
    exact_mod_cast hhi
  push_cast at hI
  rw [(pCR% confirmation_time_closed_cr) facts, (pCR% action_closed_cr) facts]
  push_cast
  nlinarith

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog

/-- If `slotStart s − Δ < S.a r`, then slot `s`'s support cutoff is at or before `S.a r`. -/
theorem support_cutoff_le_action_of_lt (facts : Record.Facts M) (S : Setup V) {s : Slot} {r : Round}
    (h : slotStart S.E.Δ s - S.E.Δ < (Restated.Vocabulary.Execution.Setup.a M S r)) :
    M.support_cutoff S.E s ≤ (Restated.Vocabulary.Execution.Setup.a M S r) := by
  have hd := S.E.Δ_pos
  rw [slotStart_closed, (pCR% action_closed_cr) facts] at h
  rw [(pCR% action_closed_cr) facts]
  have hkey : (s : Int) ≤ (S.hc.R : Int) * (r : Int) + 1 := by
    by_contra hc
    push Not at hc
    have h2 : (S.hc.R : Int) * (r : Int) + 2 ≤ (s : Int) := hc
    nlinarith
  obtain ⟨h0, hsucc⟩ := support_cutoff_closed_cw facts S.E
  cases s with
  | zero =>
      have hR : (0 : Int) ≤ (S.hc.R : Int) * (r : Int) :=
        mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
      nlinarith
  | succ s' =>
      rw [hsucc s']
      nlinarith

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog

/-- On the premises of `afterPhaseJointRound_of_premises`, with the joint invariant at a round `r₀`
    at or after the switch round, if slot `s` is at or after `o_{r₀} + 2`, `m` is the tick step at
    slot `s`'s confirmation time, and `v` is awake at that time, asleep at the grade-2 domain time
    of the round `r'` of `s + 1`, and honest through the confirmation time, then every stable root
    `G` of `v`'s grade contract at that tick is an ancestor of every honest head from slot `s + 3`
    on. -/
theorem stableRoot_ancestorOfHonestHeadsFrom_ofAsleepDomain (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (hcatch : Restated.CatchUpOnWake M S x) (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (hsync : Restated.SynchronyFromWake M S x) (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight) (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t) (hrsW : Restated.roundSleepinessW M S Sched tE) (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT) (hcs : Restated.committeeSleepinessW M S Sched tE) (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched)) (hw : Restated.WakesAtActionInstants M S Sched) (hs : Restated.SleepsAfterActionInstants M S Sched) (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap) (hprev : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
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
        (Restated.runAllPath M S Sched x v N) T) (hclear : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
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
      Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T) (hB' : Restated.BaseJustifiedHighAtSwitchRoundW M S Sched x tGAT tE gap) {n_W : Nat} (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)))) {T_W : NamedBlock V} (hAW : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.switchRound M S tE) T_W) (hJswitch : ∀ (v : V) (n₁ : Nat),
      M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) - 1
        ≤ (x[n₁].time : Int) →
      n₁ ≤ n_W → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J T_W.erase)
    {r₀ : Round} {n₀ : Nat} {T₀ : NamedBlock V}
    (hr₀ : Restated.switchRound M S tE ≤ r₀) (hTW₀ : Block.Preceq T_W.erase T₀.erase)
    (hJ₀ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x r₀ n₀ n_W T₀)
    {s : Slot} (hs0 : (M.opening_slot S.hc r₀) + 2 ≤ s)
    {m : Nat} (hm : Restated.tickStepAt M x m (M.confirmation_time S.E s)) {v : V}
    (haw : v ∈ Sched.awake (M.confirmation_time S.E s))
    (hasl : v ∉ Sched.awake (M.domain S.E S.hc ((M.round_of S.hc (s + 1))) .g2))
    (hvh : HonestThroughTime Sched (M.confirmation_time S.E s) v)
    {G : Block V} {c : M.Cache}
    (hc : M.onPhaseTick S.E S.hc (M.toHealing (x[m][v].st).st.core)
        (M.confirmation_time S.E s) (x[m][v].st).cache ⇢ c)
    (hG : (M.gradeContract c).stableRoot S.E S.hc
          (M.toHealing (M.ns_setClock S.E (x[m][v].st).st
            (M.confirmation_time S.E s)).core)
          ((M.round_of S.hc) (M.ns_setClock S.E (x[m][v].st).st
            (M.confirmation_time S.E s)).core.s) ⇢ some G) :
    Restated.AncestorOfHonestHeadsFrom M S Sched x G (s + 3) := by
  have hslot : (M.ns_setClock S.E (x[m][v].st).st
      (M.confirmation_time S.E s)).core.s = s + 1 := by
    rw [facts.hd.Sts_setClock_core_s]; exact facts.sch.Optimistic_slotOf_confirmation_time S.E s
  have hG := (facts.nd.gradeContract_stableRoot _ _ _ _ _ _).1 hG
  rw [hslot] at hG
  rcases facts.gr.frameStableRoot_cases _ _ _ _ _ _ hG rfl with hroot | ⟨root, hg2, -⟩
  · -- the first case of `frameStableRoot_cases`
    obtain ⟨hm1, hm0⟩ := Restated.tickStepAt_time facts x hm
    have hvm : Restated.HonestThrough M Sched x m v := fun t ht => hvh t (by linarith)
    have hrs0 := facts.gr.opening_slot_round_of_le_slot S.hc s
    have hrs1 := facts.gr.lt_opening_slot_round_of_succ S.hc s
    have hrr : r₀ ≤ (M.round_of S.hc s) := by
      by_contra hcon
      exact nat_lt_absurd_c3 hs0 hrs1
        (facts.gr.opening_slot_mono S (Nat.succ_le_of_lt (Nat.lt_of_not_le hcon)))
    obtain ⟨n, T, hJ, -, hTW⟩ := Restated.anchor_at_later_round facts S Sched x tE hexec hmono htd hcatch
      tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec hprev hclear hB'
      hnW hAW hJswitch hr₀ hTW₀ hJ₀ hrr
    have hr : Restated.switchRound M S tE ≤ (M.round_of S.hc s) := le_trans hr₀ hrr
    have hroot' : Block.Preceq (Restated.Vocabulary.Protocol.confRoot M (Restated.confStoreAt M S (x[m][v].st) s)) T.erase :=
      Restated.confRoot_preceq_anchor_atSlot facts S Sched x tE hexec hmono htd tGAT gap hgst hlen hsync hthird
        hphase hrsW hmult hcv hcom hrec hprev hclear hB' hnW hAW hr hTW hJ hrs0
        (Nat.le_of_lt hrs1) hm hvm
    have hGT : Block.Preceq G T.erase := by rw [hroot]; exact hroot'
    have hanc := Restated.anchor_ancestorOfHonestHeadsFrom facts S Sched x tE hexec hmono htd hcatch tGAT gap
      hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec hprev hclear hB' hnW hAW
      hJswitch hr hTW hJ
    exact Restated.ancestorOfHonestHeadsFrom_mono facts S Sched x (nat_le_add3_c3 hrs0)
      (Restated.ancestorOfHonestHeadsFrom_of_preceq facts S Sched x hGT hanc)
  · -- no grade-2 entry: it would have been written while `v` was awake at the domain instant
    exfalso
    obtain ⟨root₀, hc0, -⟩ := facts.gr.readFrame_g2_provenance _ _ _ hg2
    have hprov := Restated.framePhaseAwakeProvenance_onPhaseTick facts S Sched
      (M.toHealing (x[m][v].st).st.core) (x[m][v].st).cache haw
      (Restated.framePhaseAwakeProvenance_sts facts S Sched x v m) c hc
    exact hasl (hprov _ .g2 root₀ hc0)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog

/-- If `m` is the tick step at slot `s`'s confirmation time, `v` is awake there and not held, its
    tick has an outcome and passes the grade-2 awake test of the round of `s + 1`, every stable root
    `G` that `v` can use at the tick is an ancestor of every honest head from slot `s + 3` on, `v`'s
    `live_confirmed` after the tick is an ancestor of every honest head from slot `s + 1` on
    whenever some outcome of its slot-`s` eligibility test accepts a block, and `v`'s
    `latest_stable` and `latest_confirmed` after `m` steps are ancestors of every honest head from
    slot `s + 3` on, then so are they after `m + 1` steps. -/
theorem records_after_confirmation_tick_of_inputs (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {s : Slot}
    {m : Nat} (hm : Restated.tickStepAt M x m (M.confirmation_time S.E s)) {v : V}
    (haw : v ∈ Sched.awake (M.confirmation_time S.E s) \
      Sched.adv (M.confirmation_time S.E s))
    (hroot : ∀ c : M.Cache, M.onPhaseTick S.E S.hc (M.toHealing (x[m][v].st).st.core)
        (M.confirmation_time S.E s) (x[m][v].st).cache ⇢ c →
      ∀ G : Block V,
      (M.gradeContract c).stableRoot S.E S.hc
          (M.toHealing (M.ns_setClock S.E (x[m][v].st).st
            (M.confirmation_time S.E s)).core)
          ((M.round_of S.hc) (M.ns_setClock S.E (x[m][v].st).st
            (M.confirmation_time S.E s)).core.s) ⇢ some G →
      Restated.AncestorOfHonestHeadsFrom M S Sched x G (s + 3))
    (hlive : ∀ (H : Block V) (el : Block V → Bool),
      Restated.Vocabulary.Protocol.confEligible M S.E (x[m][v].st).st.core s ⇢ el → el H = true →
      Restated.AncestorOfHonestHeadsFrom M S Sched x (x[m + 1][v].st).st.core.live_confirmed (s + 1))
    (hL : Restated.AncestorOfHonestHeadsFrom M S Sched x (x[m][v].st).st.core.latest_stable (s + 3))
    (hC : Restated.AncestorOfHonestHeadsFrom M S Sched x (x[m][v].st).st.core.latest_confirmed (s + 3))
    (hneTick : ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched (M.confirmation_time S.E s) x[m] v) (M.confirmation_time S.E s) ⇢ out)
    -- The node state `v`'s tick reads passes the grade-2 awake test of the round of `s + 1`.
    (hrun : M.awake_for_grade2 (Setup.alwaysAwake S) v
      (Record.wakeStage M Sched (M.confirmation_time S.E s) x[m] v) (M.round_of S.hc (s + 1))) :
    Restated.AncestorOfHonestHeadsFrom M S Sched x (x[m + 1][v].st).st.core.latest_stable (s + 3) ∧
      Restated.AncestorOfHonestHeadsFrom M S Sched x (x[m + 1][v].st).st.core.latest_confirmed (s + 3) := by
  -- one outcome of the cache update and one of the stable root under its grade contract
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc (M.toHealing (x[m][v].st).st.core)
    (M.confirmation_time S.E s) (x[m][v].st).cache
  obtain ⟨o, ho'⟩ := facts.gr.frameStableRoot_nonempty c S.E S.hc
    (M.toHealing (M.ns_setClock S.E (x[m][v].st).st (M.confirmation_time S.E s)).core)
    ((M.round_of S.hc) (M.ns_setClock S.E (x[m][v].st).st (M.confirmation_time S.E s)).core.s)
  have ho := (facts.nd.gradeContract_stableRoot _ _ _ _ _ o).2 ho'
  obtain ⟨G, rfl, hstab, hconf⟩ := Restated.records_after_confirmation_tick facts S Sched x
    hm haw hneTick hrun c hc o ho
  have hGP := hroot c hc G ho
  have hnewstab : Restated.AncestorOfHonestHeadsFrom M S Sched x
      (M.advance_confirmed (x[m][v].st).st.core.latest_stable G) (s + 3) :=
    Restated.ancestorOfHonestHeadsFrom_advance_confirmed facts S Sched x hGP (fun _ => hL)
  refine ⟨by rw [hstab]; exact hnewstab, ?_⟩
  -- the confirmation record: one outcome of the confirmation update, and the candidate it writes
  obtain ⟨D, hD⟩ := facts.dt.update_confirmation_with_nonempty (M.gradeContract c) S.E S.hc
    (M.ns_setClock S.E (x[m][v].st).st (M.confirmation_time S.E s)).core s
  obtain ⟨cand, hfl, hcases⟩ := update_confirmation_with_latest_confirmed_eligible_cw facts
    (M.gradeContract c) S.E S.hc _ s D hD
  have hDstab : D.latest_stable = M.advance_confirmed (x[m][v].st).st.core.latest_stable G := by
    rw [facts.hd.update_confirmation_with_latest_stable_of_root _ _ _ _ _ (some G) ho rfl D hD,
      facts.hd.setClock_core_latest_stable]
  rw [facts.hd.setClock_core_latest_confirmed] at hfl hcases
  rw [hconf D hD, hfl, hDstab]
  refine Restated.ancestorOfHonestHeadsFrom_floor_on_stable facts S Sched x hnewstab (fun _ => ?_)
    (fun _ => hC)
  rcases hcases with hcand | ⟨el, hel, helD, hcand⟩ | ⟨G', hsel, hcand⟩
  · rw [hcand]; exact hC
  · -- the eligible walk result is the `live_confirmed` written at the tick
    rw [confEligible_setClock_cw facts S.E (x[m][v].st).st (M.confirmation_time S.E s)] at hel
    have hJ1 := hlive D.live_confirmed el hel helD
    rw [(pW% live_confirmed_after_confirmation_tick_outcome_csw) facts S Sched x hm haw
      hneTick hrun c hc D hD] at hJ1
    rw [hcand]
    exact Restated.ancestorOfHonestHeadsFrom_advance_confirmed facts S Sched x
      (Restated.ancestorOfHonestHeadsFrom_mono facts S Sched x (Nat.le_add_right _ 2) hJ1) (fun _ => hC)
  · -- the select candidate is the stable root
    have hGG : G = G' := Option.some.inj
      ((pW% confirmationSG_stableRoot_csw) facts c S.E S.hc _ s hsel (some G) ho)
    subst hGG
    rw [hcand]
    exact Restated.ancestorOfHonestHeadsFrom_advance_confirmed facts S Sched x hGP (fun _ => hC)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog

/-- If `S.E.t_GST ≤ tGAT`, the phase `[tGAT, tE]` is at least `healingLengthη S gap` long, every
    validator the adversary does not hold at a time of the phase is awake then, and validators fall
    asleep only right after action times, then a validator the adversary holds at no time up to
    `S.a (rW + 1)` is a member of `HonRound S Sched (rW + 1)`. -/
theorem honRound_switch_succ_of_honest (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (tE tGAT : Int)
    (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hs : Restated.SleepsAfterActionInstants M S Sched) {v : V}
    (hv : HonestThroughTime Sched ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE + 1))) v) :
    v ∈ Restated.HonRound M S Sched (Restated.switchRound M S tE + 1) := by
  have hd := S.E.Δ_pos
  set rW := Restated.switchRound M S tE with hrW
  obtain ⟨hwin, hWE⟩ := Restated.switchRound_window_in_phase facts S tGAT tE gap hgst hlen
  have hrW0 : 0 < rW := Restated.round_pos_of_switch facts S tGAT tE gap hgst hlen le_rfl
  have hspec := Restated.switchRound_spec facts S tE (Nat.pos_iff_ne_zero.mp hrW0)
  have hWa : 0 ≤ wAttest S := by
    have h := Restated.wAttest_eq_action_succ_sub facts S rW
    have h2 := Restated.action_mono facts S (Nat.le_succ rW)
    linarith
  have hlt : (Restated.Vocabulary.Execution.Setup.a M S rW) < tE := by
    rw [(pCR% confirmation_time_closed_cr) facts, (pCR% opening_slot_closed_cr) facts] at hspec
    rw [(pCR% action_closed_cr) facts]
    push_cast at hspec
    nlinarith
  have hsucc := facts.gr.action_succ_eq_add_rounds S rW
  have hR3 : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
  have hgap : (1 : Int) ≤ 4 * (S.hc.R : Int) * S.E.Δ := by nlinarith
  have haw1 : v ∈ Sched.awake ((Restated.Vocabulary.Execution.Setup.a M S rW) + 1) :=
    hphase ((Restated.Vocabulary.Execution.Setup.a M S rW) + 1) (by linarith) (by linarith) v (hv _ (by linarith))
  refine Finset.mem_sdiff.2 ⟨?_, hv _ le_rfl⟩
  show v ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S (rW + 1)) - wAttest S) ((Restated.Vocabulary.Execution.Setup.a M S (rW + 1)))
  rw [Restated.wAttest_eq_action_succ_sub facts]
  refine mem_awakeThroughout_of_forall Sched ?_
  intro t h0 h1
  by_cases hte : t ≤ (Restated.Vocabulary.Execution.Setup.a M S rW) + 1
  · exact hphase t (by linarith) (by linarith) v (hv t h1)
  · exact Restated.awake_forward_to_action facts S Sched hs (by linarith) haw1 t (by linarith) h1

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog

/-- On the premises of `afterPhaseJointRound_of_premises`, with the joint invariant at the switch
    round, if `RecordsSettledAtSettleTick` holds and `n_b` is the tick step at `S.a (rW + 1)`, then
    for every step `k ≥ n_b + 1` and every `v` honest through the configuration after `k` steps,
    `v`'s `latest_stable` and `latest_confirmed` after `k` steps are ancestors of every honest head
    from slot `slot(x[k].time) + 2` on. -/
theorem records_ancestorOfHonestHeads_after_settleTick (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (hcatch : Restated.CatchUpOnWake M S x) (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (hsync : Restated.SynchronyFromWake M S x) (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight) (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t) (hrsW : Restated.roundSleepinessW M S Sched tE) (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT) (hcs : Restated.committeeSleepinessW M S Sched tE) (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched)) (hw : Restated.WakesAtActionInstants M S Sched) (hs : Restated.SleepsAfterActionInstants M S Sched) (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap) (hprev : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
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
        (Restated.runAllPath M S Sched x v N) T) (hclear : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
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
      Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T) (hB' : Restated.BaseJustifiedHighAtSwitchRoundW M S Sched x tGAT tE gap) {n_W : Nat} (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)))) {T_W : NamedBlock V} (hAW : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.switchRound M S tE) T_W) (hJswitch : ∀ (v : V) (n₁ : Nat),
      M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) - 1
        ≤ (x[n₁].time : Int) →
      n₁ ≤ n_W → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J T_W.erase)
    {n₀ : Nat} {T₀ : NamedBlock V} (hTW₀ : Block.Preceq T_W.erase T₀.erase)
    (hJ₀ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x (Restated.switchRound M S tE) n₀ n_W T₀)
    (hsettle : Restated.RecordsSettledAtSettleTick M S Sched x tE)
    {n_b : Nat} (hn_b : Restated.tickStepAt M x n_b ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE + 1)))) (v : V) :
    ∀ k : Nat, n_b + 1 ≤ k → Restated.HonestThrough M Sched x k v →
      Restated.RecordsAncestorOfHonestHeads M S Sched x v k := by
  have hd := S.E.Δ_pos
  obtain ⟨hnb1, hnb0⟩ := Restated.tickStepAt_time facts x hn_b
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    intro hv
    have hHon : v ∈ Restated.HonRound M S Sched (Restated.switchRound M S tE + 1) :=
      Restated.honRound_switch_succ_of_honest facts S Sched tE tGAT gap hgst hlen hphase hs
        (fun t ht => hv t (by rw [hnb1]; exact ht))
    exact hsettle _ n_b v le_rfl hn_b hHon rfl
  | succ k hkn ih =>
    intro hv
    have hvk : Restated.HonestThrough M Sched x k v := fun t ht =>
      hv t (le_trans ht (Restated.time_mono_int facts S Sched x (Nat.le_succ k)))
    have ihk := ih hvk
    rcases Restated.records_succ_cases facts S Sched x v k with ⟨h1, h2⟩ | ⟨s, hm, haw⟩
    · have hsl : S.E.slotOf (x[k].time : Int) + 2 ≤ S.E.slotOf (x[k + 1].time : Int) + 2 :=
        Nat.add_le_add_right (slotOf_mono_sts S (Restated.time_mono_int facts S Sched x (Nat.le_succ k))) 2
      unfold Restated.RecordsAncestorOfHonestHeads
      rw [h1, h2]
      exact ⟨Restated.ancestorOfHonestHeadsFrom_mono facts S Sched x hsl ihk.1,
        Restated.ancestorOfHonestHeadsFrom_mono facts S Sched x hsl ihk.2⟩
    · obtain ⟨hn1, hn0⟩ := Restated.tickStepAt_time facts x hm
      have hslot : S.E.slotOf (x[k + 1].time : Int) = s + 1 := by
        rw [hn1]; exact facts.sch.Optimistic_slotOf_confirmation_time S.E s
      have hbk : (x[n_b + 1].time : Int) ≤ (x[k].time : Int) := Restated.time_mono_int facts S Sched x hkn
      have htc : (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE + 1)) < M.confirmation_time S.E s := by
        rw [hnb1] at hbk; linarith
      have hvh' : HonestThroughTime Sched (M.confirmation_time S.E s) v :=
        fun t ht => hv t (by rw [hn1]; exact ht)
      obtain ⟨hs1, hrr, -, ha1, -⟩ :=
        Restated.confirmation_tick_arith facts S (Nat.succ_pos _) htc
      have hs0 : (M.opening_slot S.hc (Restated.switchRound M S tE)) + 2 ≤ s := by
        have h1 := facts.gr.opening_slot_succ S.hc (Restated.switchRound M S tE)
        rw [h1] at hs1
        exact nat_add_two_le_c3 le_rfl hs1 S.hc.R_ge_three
      have hL : Restated.AncestorOfHonestHeadsFrom M S Sched x (x[k][v].st).st.core.latest_stable (s + 3) :=
        Restated.ancestorOfHonestHeadsFrom_mono facts S Sched x (Nat.add_le_add_right
          (by rw [← facts.sch.Optimistic_slotOf_confirmation_time S.E s]
              exact slotOf_mono_sts S (by linarith)) 2) ihk.1
      have hC : Restated.AncestorOfHonestHeadsFrom M S Sched x (x[k][v].st).st.core.latest_confirmed
          (s + 3) :=
        Restated.ancestorOfHonestHeadsFrom_mono facts S Sched x (Nat.add_le_add_right
          (by rw [← facts.sch.Optimistic_slotOf_confirmation_time S.E s]
              exact slotOf_mono_sts S (by linarith)) 2) ihk.2
      have hawtc : v ∈ Sched.awake (M.confirmation_time S.E s) := (Finset.mem_sdiff.1 haw).1
      set r' := (M.round_of S.hc (s + 1)) with hr'
      have hr'0 : 0 < r' := lt_of_lt_of_le (Nat.succ_pos _) hrr
      obtain ⟨r₁, hr₁⟩ : ∃ r₁ : Round, r' = r₁ + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hr'0).symm⟩
      have hpred : (Restated.Vocabulary.Execution.Setup.a M S r₁) ≤ slotStart S.E.Δ s - S.E.Δ := by
        have h := Restated.action_pred_round_of_succ_le facts S s hr'0
        rw [← hr', hr₁, Nat.add_sub_cancel] at h
        exact h
      have hres : Restated.AncestorOfHonestHeadsFrom M S Sched x (x[k + 1][v].st).st.core.latest_stable
            (s + 3) ∧
          Restated.AncestorOfHonestHeadsFrom M S Sched x (x[k + 1][v].st).st.core.latest_confirmed
            (s + 3) := by
        -- split on the grade-2 awake test of the round of `s + 1`; when it fails, the tick keeps
        -- both records
        have hdvd : M.confirmation_time S.E s % S.E.Δ = 0 := by
          rw [facts.sch.confirmation_time_eq_support_cutoff_succ]
          exact facts.sch.support_cutoff_emod_delta S (s + 1)
        by_cases hrun : M.awake_for_grade2 (Setup.alwaysAwake S) v
            (Record.wakeStage M Sched (M.confirmation_time S.E s) x[k] v) (M.round_of S.hc (s + 1))
        swap
        · obtain ⟨t', hlbl, ht'⟩ := id hm
          have hdvd' : (t' : Int) % S.E.Δ = 0 := by rw [ht']; exact hdvd
          have haw' : v ∈ Sched.awake (t' : Int) \ Sched.adv (t' : Int) := by rw [ht']; exact haw
          rcases Restated.st_succ_of_tick_awake facts S Sched x v hlbl haw' hdvd' with
            ⟨out, hout, hst⟩ | ⟨-, hst⟩
          · rw [ht'] at hout
            obtain ⟨hCk, hLk⟩ :=
              facts.nd.tick_records_frame_of_not_awake_for_grade2 S v _ s out hout hrun
            rw [hst, hLk, hCk, Record.wakeStage_st facts]
            exact ⟨hL, hC⟩
          · rw [hst, Record.wakeStage_st facts]
            exact ⟨hL, hC⟩
        by_cases hA : v ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S (r' - 1))) (M.confirmation_time S.E s)
        · -- awake since the round before
          have hvaw : v ∈ Sched.awakeThroughout (slotStart S.E.Δ s - S.E.Δ)
              (M.confirmation_time S.E s) := by
            refine awakeThroughout_mono Sched hA ?_ le_rfl
            rw [hr₁, Nat.add_sub_cancel]; exact hpred
          exact Restated.records_after_confirmation_tick_ancestorOfHonestHeadsFrom_ofAwake facts S Sched x tE
            hexec hmono htd hcatch tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom
            hw hs hrec hprev hclear hB' hnW hAW hJswitch le_rfl hTW₀ hJ₀ hs0 hrr hm hvaw hA hvh'
            hL hC
        · -- woke at `S.a r'`
          have ha1' : (Restated.Vocabulary.Execution.Setup.a M S r₁) < M.confirmation_time S.E s := by
            rw [hr₁, Nat.add_sub_cancel] at ha1; exact ha1
          have hlo0 : (Restated.Vocabulary.Execution.Setup.a M S 0) ≤ M.confirmation_time S.E s :=
            le_trans (Restated.action_mono facts S (Nat.zero_le _)) (le_of_lt ha1')
          obtain ⟨r_a, hra0, hra1⟩ := Restated.exists_action_round facts S hlo0
          have hup := Restated.confirmation_time_lt_action_round_of_succ facts S s
          rw [← hr', hr₁] at hup
          have hra_lo : r₁ < r_a + 1 := Restated.round_lt_of_action_lt facts S (lt_trans ha1' hra1)
          have hra_hi : r_a < r₁ + 1 + 1 := Restated.round_lt_of_action_lt facts S (lt_of_le_of_lt hra0 hup)
          have hback := Restated.awake_since_action facts S Sched hw hra0 hra1 hawtc
          have hra : r_a = r₁ + 1 := by
            by_contra hne
            have hra' : r_a = r₁ :=
              le_antisymm (Nat.le_of_lt_succ (lt_of_le_of_ne (Nat.le_of_lt_succ hra_hi) hne))
                (Nat.le_of_lt_succ hra_lo)
            apply hA
            rw [hr₁, Nat.add_sub_cancel]
            refine mem_awakeThroughout_of_forall Sched ?_
            intro t h0 h1
            exact hback t (by rw [hra']; exact h0) h1
          rw [hra] at hback hra0
          -- asleep at the time before `S.a r'`
          have hsucc := facts.gr.action_succ_eq_add_rounds S r₁
          have hR3 : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
          have hgap : (1 : Int) ≤ 4 * (S.hc.R : Int) * S.E.Δ := by nlinarith
          have hwake : v ∉ Sched.awake ((Restated.Vocabulary.Execution.Setup.a M S (r₁ + 1)) - 1) := by
            intro hawk
            have hb2 := Restated.awake_since_action facts S Sched hw (r := r₁) (t := (Restated.Vocabulary.Execution.Setup.a M S (r₁ + 1)) - 1)
              (by linarith) (by linarith) hawk
            apply hA
            rw [hr₁, Nat.add_sub_cancel]
            refine mem_awakeThroughout_of_forall Sched ?_
            intro t h0 h1
            by_cases ht : t ≤ (Restated.Vocabulary.Execution.Setup.a M S (r₁ + 1)) - 1
            · exact hb2 t h0 ht
            · exact hback t (by linarith) h1
          have hasl : v ∉ Sched.awake (M.domain S.E S.hc r' .g2) := by
            rw [hr₁]; exact Restated.asleep_at_domain facts S Sched hs hwake .g2
          have hroot : ∀ c : M.Cache, M.onPhaseTick S.E S.hc (M.toHealing (x[k][v].st).st.core)
                (M.confirmation_time S.E s) (x[k][v].st).cache ⇢ c →
              ∀ G : Block V,
              (M.gradeContract c).stableRoot S.E S.hc
                  (M.toHealing (M.ns_setClock S.E (x[k][v].st).st
                    (M.confirmation_time S.E s)).core)
                  ((M.round_of S.hc) (M.ns_setClock S.E (x[k][v].st).st
                    (M.confirmation_time S.E s)).core.s) ⇢ some G →
              Restated.AncestorOfHonestHeadsFrom M S Sched x G (s + 3) := fun c hc G hG =>
            Restated.stableRoot_ancestorOfHonestHeadsFrom_ofAsleepDomain facts S Sched x tE hexec hmono htd
              hcatch tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec
              hprev hclear hB' hnW hAW hJswitch le_rfl hTW₀ hJ₀ hs0 hm hawtc hasl hvh' hc hG
          have hlive : ∀ (H : Block V) (el : Block V → Bool),
              Restated.Vocabulary.Protocol.confEligible M S.E (x[k][v].st).st.core s ⇢ el →
              el H = true →
              Restated.AncestorOfHonestHeadsFrom M S Sched x (x[k + 1][v].st).st.core.live_confirmed
                (s + 1) := by
            intro H el hel hH
            by_cases hstart : (Restated.Vocabulary.Execution.Setup.a M S (r₁ + 1)) ≤ slotStart S.E.Δ s - S.E.Δ
            · have hvaw : v ∈ Sched.awakeThroughout (slotStart S.E.Δ s - S.E.Δ)
                  (M.confirmation_time S.E s) :=
                mem_awakeThroughout_of_forall Sched (fun t h0 h1 => hback t (by linarith) h1)
              exact Restated.live_confirmed_ancestorOfHonestHeadsFrom_ofJoint facts S Sched x tE hexec hmono htd
                hcatch tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec
                hprev hclear hB' hnW hAW hJswitch le_rfl hTW₀ hJ₀ hs0 hm hvaw hvh' hrun
            · exfalso
              have hcut := Restated.support_cutoff_le_action_of_lt facts S (not_le.mp hstart)
              have hpos : 0 < slotStart S.E.Δ s := by
                have h2 : (2 : Int) ≤ (s : Int) := by exact_mod_cast le_trans (Nat.le_add_left 2 _) hs0
                rw [slotStart_closed]; nlinarith
              have hasleep : ∀ t : Int, slotStart S.E.Δ s ≤ t →
                  t < M.support_cutoff S.E s → v ∉ Sched.awake t := by
                intro t h0 h1 hawt
                exact hwake (Restated.awake_forward_to_action facts S Sched hs (r := r₁) (by linarith) hawt
                  ((Restated.Vocabulary.Execution.Setup.a M S (r₁ + 1)) - 1) (by linarith) (by linarith))
              rw [Restated.confEligible_false_of_asleep facts S Sched x v k hpos hasleep H el
                hel] at hH
              exact Bool.false_ne_true hH
          exact Restated.records_after_confirmation_tick_of_inputs facts S Sched x hm haw hroot
            hlive hL hC (Restated.tick_outcome_of_tickStepAt facts S Sched x
              hexec.idealization.root_injective hexec.honestRootsNew hmono hm hdvd haw) hrun
      unfold Restated.RecordsAncestorOfHonestHeads
      rw [hslot]
      exact hres

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog

/-- On the premises of `afterPhaseJointRound_of_premises`, with the joint invariant at the switch
    round, `RecordsSettledAtSettleTick S Sched x tE` gives
    `RecordsSettledAtActionTicks S Sched x tE`. -/
theorem recordsSettledAtActionTicks_of_settleTick (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (hcatch : Restated.CatchUpOnWake M S x) (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (hsync : Restated.SynchronyFromWake M S x) (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight) (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t) (hrsW : Restated.roundSleepinessW M S Sched tE) (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT) (hcs : Restated.committeeSleepinessW M S Sched tE) (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched)) (hw : Restated.WakesAtActionInstants M S Sched) (hs : Restated.SleepsAfterActionInstants M S Sched) (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap) (hprev : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
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
        (Restated.runAllPath M S Sched x v N) T) (hclear : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
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
      Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T) (hB' : Restated.BaseJustifiedHighAtSwitchRoundW M S Sched x tGAT tE gap) {n_W : Nat} (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)))) {T_W : NamedBlock V} (hAW : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.switchRound M S tE) T_W) (hJswitch : ∀ (v : V) (n₁ : Nat),
      M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) - 1
        ≤ (x[n₁].time : Int) →
      n₁ ≤ n_W → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J T_W.erase)
    {n₀ : Nat} {T₀ : NamedBlock V} (hTW₀ : Block.Preceq T_W.erase T₀.erase)
    (hJ₀ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x (Restated.switchRound M S tE) n₀ n_W T₀)
    (hsettle : Restated.RecordsSettledAtSettleTick M S Sched x tE) :
    Restated.RecordsSettledAtActionTicks M S Sched x tE := by
  intro r n v hr hn hv _
  obtain ⟨n_b, hn_b⟩ := Restated.tick_field_at_succ facts S Sched x htd (Restated.switchRound M S tE)
  obtain ⟨hnb1, hnb0⟩ := Restated.tickStepAt_time facts x hn_b
  obtain ⟨hn1, hn0⟩ := Restated.tickStepAt_time facts x hn
  have hmono' := Restated.action_mono facts S hr
  refine Restated.records_ancestorOfHonestHeads_after_settleTick facts S Sched x tE hexec hmono htd hcatch tGAT
    gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec hprev hclear hB' hnW hAW
    hJswitch hTW₀ hJ₀ hsettle hn_b v (n + 1) ?_ ?_
  · by_contra hcon
    have := Restated.time_mono_int facts S Sched x (Nat.le_of_lt_succ (Nat.lt_of_not_le hcon))
    linarith
  · intro t ht hadv
    rw [hn1] at ht
    exact (Finset.mem_sdiff.1 hv).2 (hmono t ((Restated.Vocabulary.Execution.Setup.a M S r)) ht hadv)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog

/-- On the premises of `afterPhaseJointRound_of_premises`, with the joint invariant at the switch
    round, `RecordsSettledAtSettleTick` gives `ConfirmedMonotoneAfterHealing S Sched x tE`. -/
theorem confirmedMonotoneAfterHealing_of_settle (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (hcatch : Restated.CatchUpOnWake M S x) (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (hsync : Restated.SynchronyFromWake M S x) (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight) (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t) (hrsW : Restated.roundSleepinessW M S Sched tE) (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT) (hcs : Restated.committeeSleepinessW M S Sched tE) (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched)) (hw : Restated.WakesAtActionInstants M S Sched) (hs : Restated.SleepsAfterActionInstants M S Sched) (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap) (hprev : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
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
        (Restated.runAllPath M S Sched x v N) T) (hclear : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
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
      Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T) (hB' : Restated.BaseJustifiedHighAtSwitchRoundW M S Sched x tGAT tE gap) {n_W : Nat} (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)))) {T_W : NamedBlock V} (hAW : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.switchRound M S tE) T_W) (hJswitch : ∀ (v : V) (n₁ : Nat),
      M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) - 1
        ≤ (x[n₁].time : Int) →
      n₁ ≤ n_W → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J T_W.erase)
    {n₀ : Nat} {T₀ : NamedBlock V} (hTW₀ : Block.Preceq T_W.erase T₀.erase)
    (hJ₀ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x (Restated.switchRound M S tE) n₀ n_W T₀)
    (hsettle : Restated.RecordsSettledAtSettleTick M S Sched x tE) :
    Restated.ConfirmedMonotoneAfterHealing M S Sched x tE := by
  intro v i j hij hvj hti _ _
  obtain ⟨n_b, hn_b⟩ := Restated.tick_field_at_succ facts S Sched x htd (Restated.switchRound M S tE)
  obtain ⟨hnb1, hnb0⟩ := Restated.tickStepAt_time facts x hn_b
  have hts : (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE + 1)) ≤ (x[i].time : Int) := hti
  have hki : n_b + 1 ≤ i := by
    by_contra hcon
    have := Restated.time_mono_int facts S Sched x (Nat.le_of_lt_succ (Nat.lt_of_not_le hcon))
    linarith
  have hvk : ∀ k : Nat, k ≤ j → Restated.HonestThrough M Sched x k v := fun k hkj t' h =>
    hvj t' (le_trans h (Restated.time_mono_int facts S Sched x hkj))
  have hts' : (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)) ≤ (x[i].time : Int) :=
    le_trans (Restated.action_mono facts S (Nat.le_succ _)) hts
  refine Restated.get_confirmed_preceq_of_records_along facts S Sched x htd hcs v hij (fun k hik hkj => ?_)
    (fun k hik hkj => ?_) (facts.ndRun.tick_outcome_sts S Sched x hexec.idealization.root_injective hexec.honestRootsNew)
  · exact Restated.records_ancestorOfHonestHeads_after_settleTick facts S Sched x tE hexec hmono htd hcatch tGAT
      gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec hprev hclear hB' hnW
      hAW hJswitch hTW₀ hJ₀ hsettle hn_b v k (le_trans hki hik) (hvk k hkj)
  · exact Restated.finalized_ancestorOfHonestHeadsFrom facts S Sched x tE hexec hmono htd hcatch tGAT gap hgst
      hlen hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec hprev hclear hB' hnW hAW
      hJswitch le_rfl hTW₀ hJ₀ (le_trans hts' (Restated.time_mono_int facts S Sched x (le_of_lt hik)))
      (hvk k hkj)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog

end

end DecoupledConsensusModel.Sts.Restated
