import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bInvariantActive
import Proofs.Claims.Restated.Claim13bK_ConeHeadsUpTo
import Proofs.Claims.Restated.Claim13bK_ConeSlots
import Proofs.Claims.Restated.Claim13bStepCone
import Proofs.Claims.Restated.Claim13bStepConeIter
import Proofs.Claims.Restated.Claim13bStepConeIterUpTo
import Proofs.Claims.Restated.Claim13bStepConeUpTo
import Proofs.Claims.Restated.Claim13bStepGrade
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13beRoute3_3
import Proofs.Claims.Restated.Claim13beRoute3_7
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActive
import Model.Conditions.Claim13bK_ConeSlots
import Model.Conditions.Claim13bStepCone
import Model.Conditions.Claim13bStepConeIter
import Model.Conditions.Claim13bStepSG
import Model.Conditions.Claim13beRoute3_5
import Model.Conditions.Claim13beRoute3_7
import Model.Conditions.ClaimAsyncK_DeliveryUpTo
import Model.Conditions.CommonViewOfFinalizedDescendantsFacts
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_Grades_Main
import Model.Record.Wiring
import Proofs.Claims.Restated.WakeWindow

/-!
# Honest heads after the phase, with synchrony up to a cutoff

The slot-to-slot induction on honest heads after the phase and the compatibility of an honest
attester's confirmed block at the round's action read, with synchrony assumed only up to the support
cutoff of the last slot used, stated over a model `M : Record.Model V` and its facts.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Execution

/-- For a positive slot `s`, `support_cutoff s = slotStart s + 2Δ`. -/
private theorem support_cutoff_eq_of_pos (facts : Record.Facts M) (E : Env V) {s : Slot}
    (hs : 0 < s) : M.support_cutoff E s = slotStart E.Δ s + 2 * E.Δ := by
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, (Nat.succ_pred_eq_of_pos hs).symm⟩
  rw [← facts.sch.confirmation_time_eq_support_cutoff_succ,
    ← facts.sch.slotStart_add_six_delta_eq_confirmation_time, slotStart_succ]
  ring

open scoped DC in
/-- If `f <$> m` can return `b`, then `m` can return some `a` with `f a = b`. -/
private theorem returns_map_elim_csu {α β : Type} (f : α → β) (m : DC.NDRE α) (b : β)
    (h : (f <$> m) ⇢ b) : ∃ a, m ⇢ a ∧ f a = b := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image] at h
  obtain ⟨e, he, hb⟩ := h
  cases e with
  | ok a => exact ⟨a, he, by simpa [Except.map] using hb⟩
  | error err => simp [Except.map] at hb

open scoped DC in
/-- If `m` can return `a`, then `f <$> m` can return `f a`. -/
private theorem returns_map_intro_csu {α β : Type} (f : α → β) (m : DC.NDRE α) (a : α)
    (h : m ⇢ a) : (f <$> m) ⇢ f a := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image]
  exact ⟨_, h, rfl⟩

open scoped DC in
/-- `m >>= k` can return `b` exactly when `m` can return some `a` from which `k a` can return `b`. -/
private theorem returns_bind_iff_csu {α β : Type} (m : DC.NDRE α) (k : α → DC.NDRE β) (b : β) :
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

/-- Every outcome of the vote read of `before` at slot `s` is made of `before`'s store with its
    clock set to slot `s`'s vote instant, `before`'s signing record, and an outcome of the phase
    tick at that instant on `before`'s cache. -/
private theorem voteReadOf_cases_csu (S : Setup V) (before : M.N) (s : Slot) {n : M.N}
    (hn : Restated.voteReadOf M S before s ⇢ n) :
    ∃ c : M.Cache, M.onPhaseTick S.E S.hc before.st.core.toHealing (M.vote_time S.E s)
        before.cache ⇢ c ∧
      n = M.mkNode (M.ns_setClock S.E before.st (M.vote_time S.E s)) before.record c := by
  obtain ⟨c, hc, hcn⟩ := returns_map_elim_csu _ _ _ hn
  exact ⟨c, hc, hcn.symm⟩

/-- Every outcome of `gfHeadWith` at `st` is an outcome of `M.get_head_in_tree_with` over an outcome
    of `st`'s voter tree and outcomes of its two voter views. -/
private theorem gfHeadWith_cases_csu (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig)
    (st : M.S) {H : Block V} (hH : Restated.gfHeadWith M contract E hc st ⇢ H) :
    ∃ T, Restated.voteTreeOf M E st ⇢ T ∧ ∃ W, Restated.voteViewOf M E st ⇢ W ∧
      ∃ U, Restated.voteSupportViewOf M E st ⇢ U ∧
        M.get_head_in_tree_with contract E hc st T W U (st.s - 1) ⇢ H := by
  unfold Restated.gfHeadWith at hH
  obtain ⟨T, hT, hH⟩ := (returns_bind_iff_csu _ _ _).1 hH
  obtain ⟨W, hW, hH⟩ := (returns_bind_iff_csu _ _ _).1 hH
  obtain ⟨U, hU, hH⟩ := (returns_bind_iff_csu _ _ _).1 hH
  exact ⟨T, hT, W, hW, U, hU, hH⟩

/-- At every store `st`, `gfHeadWith` has an outcome. -/
private theorem gfHeadWith_nonempty_csu (facts : Record.Facts M) (contract : M.Contract) (E : Env V)
    (hc : Protocol.HealConfig) (st : M.S) : ∃ H, Restated.gfHeadWith M contract E hc st ⇢ H := by
  obtain ⟨T, hT⟩ := facts.fc.voter_filtered_block_tree_nonempty E st st.s
  obtain ⟨W, hW⟩ := facts.fc.voter_view_nonempty E (M.toHealing st).toFG.toSG.toGoldfishStore st.s
  obtain ⟨U, hU⟩ :=
    facts.fc.voter_support_view_nonempty E (M.toHealing st).toFG.toSG.toGoldfishStore st.s
  obtain ⟨H, hH⟩ := facts.fc.get_head_in_tree_with_layer_nonempty contract E hc (M.toHealing st)
    T W U (st.s - 1)
  refine ⟨H, ?_⟩
  unfold Restated.gfHeadWith
  exact (returns_bind_iff_csu _ _ _).2 ⟨T, hT, (returns_bind_iff_csu _ _ _).2
    ⟨W, hW, (returns_bind_iff_csu _ _ _).2 ⟨U, hU,
      (facts.hd.get_head_in_tree_with_eq_layer _ _ _ _ _ _ _ _ _).2 hH⟩⟩⟩

/-- From every node state `before`, `gfHeadFrom` has an outcome at slot `s`. -/
private theorem gfHeadFrom_nonempty_csu (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (s : Slot) : ∃ H, Restated.gfHeadFrom M S before s ⇢ H := by
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc before.st.core.toHealing
    (M.vote_time S.E s) before.cache
  have hn : Restated.voteReadOf M S before s ⇢
      M.mkNode (M.ns_setClock S.E before.st (M.vote_time S.E s)) before.record c :=
    returns_map_intro_csu _ _ _ hc
  obtain ⟨H, hH⟩ := gfHeadWith_nonempty_csu facts (M.gradeContract
    (M.mkNode (M.ns_setClock S.E before.st (M.vote_time S.E s)) before.record c).cache) S.E S.hc
    (M.mkNode (M.ns_setClock S.E before.st (M.vote_time S.E s)) before.record c).st.core
  refine ⟨H, ?_⟩
  unfold Restated.gfHeadFrom
  exact (returns_bind_iff_csu _ _ _).2 ⟨_, hn, hH⟩

/-- From every node state `before`, `gfVoteFrom` has an outcome. -/
private theorem gfVoteFrom_nonempty_csu (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (v : V) (s : Slot) : ∃ u, Restated.gfVoteFrom M S before v s ⇢ u := by
  obtain ⟨H, hH⟩ := gfHeadFrom_nonempty_csu facts S before s
  exact ⟨_, returns_map_intro_csu (fun H : Block V => (⟨v, s, H.root⟩ : GoldfishVote V)) _ H hH⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- A validator awake throughout slot `s`'s vote window is awake from one delay before the grade-1
    early cutoff of `s`'s round to `s`'s vote instant. -/
private theorem grade1_window_of_activeAtW_csu (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) {s : Slot} {q : V} (hq : q ∈ activeAtW S Sched s) :
    q ∈ Sched.awakeThroughout (M.early S.E S.hc (M.round_of S.hc s) .g1 - S.E.Δ)
      (M.vote_time S.E s) := by
  have hΔ := S.E.Δ_pos
  have hg1 := facts.gr.early_g2_add_delta_le_early_g1 S (M.round_of S.hc s)
  have hg2 := facts.gr.early_g2_eq S (M.round_of S.hc s)
  have ha := facts.sch.a_eq_confirmation_time S.hc S.E (M.round_of S.hc s)
  have hconf := facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E
    (M.opening_slot S.hc (M.round_of S.hc s))
  have hvote := facts.sch.slotStart_add_delta_eq_vote_time S.E s
  have hlt := facts.gr.lt_opening_slot_round_of_succ S.hc s
  rw [facts.gr.opening_slot_succ S.hc (M.round_of S.hc s)] at hlt
  have hsle : ((s : Nat) : Int) ≤ ((M.opening_slot S.hc (M.round_of S.hc s) : Nat) : Int) +
      ((S.hc.R : Nat) : Int) - 1 := by
    have h1 : s + 1 ≤ M.opening_slot S.hc (M.round_of S.hc s) + S.hc.R := hlt
    have h2 : ((s + 1 : Nat) : Int) ≤
        ((M.opening_slot S.hc (M.round_of S.hc s) + S.hc.R : Nat) : Int) := by
      exact_mod_cast h1
    push_cast at h2
    linarith
  have hmul := mul_le_mul_of_nonneg_left hsle (by linarith : (0 : Int) ≤ 4 * S.E.Δ)
  have hss : slotStart S.E.Δ s ≤ slotStart S.E.Δ (M.opening_slot S.hc (M.round_of S.hc s)) +
      4 * S.E.Δ * ((S.hc.R : Nat) : Int) - 4 * S.E.Δ := by
    unfold slotStart; linarith
  simp only [activeAtW, wVote, Schedule.awakeThroughout, Finset.mem_inf, Finset.mem_Icc] at hq ⊢
  intro i hi
  apply hq i
  constructor
  · have hRΔ : (4 * ((S.hc.R : Nat) : Int) + 2) * S.E.Δ =
        4 * S.E.Δ * ((S.hc.R : Nat) : Int) + 2 * S.E.Δ := by ring
    rw [hRΔ]
    linarith [hi.1]
  · linarith [hi.2]

/-- If step `m` is the tick at slot `s`'s vote instant, `q` is awake throughout slot `s`'s vote
    window and `q` is not held by the adversary up to that instant, then `q`'s node state at step
    `m` passes the grade-1 awake test of `s`'s round. -/
private theorem grade1_at_vote_tick_csu (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) {m : Nat} {s : Slot}
    (hm : Restated.tickStepAt M x m (M.vote_time S.E s)) {q : V} (hq : q ∈ activeAtW S Sched s)
    (hhon : ∀ t' ≤ M.vote_time S.E s, q ∉ Sched.adv t') :
    M.awake_for_grade1 (Setup.alwaysAwake S) q
      (Record.wakeStage M Sched (M.vote_time S.E s) x[m] q) (M.round_of S.hc s) := by
  obtain ⟨τ, hlbl, hτ⟩ := hm
  have h := Restated.run_fact_g1 facts S Sched x m τ s q hlbl (Or.inr hτ)
    (by rw [hτ]; exact grade1_window_of_activeAtW_csu facts S Sched hq) (by rw [hτ]; exact hhon)
  rw [hτ] at h
  exact h

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- With synchrony up to slot `s`'s support cutoff: if GST is at or before slot `s`'s start, the
    reading step `mr` lies between slot `s`'s support cutoff and its confirmation instant, `v` is
    not held by the adversary at `mr` and is awake from slot `s`'s start to its support cutoff, and
    the ticks named by `hneTickVote` and `hneTick` have an outcome, then every vote naming an honest
    active member of slot `s`'s committee, in every merged view slot `(s + 1)`'s vote duty can build
    at `v`'s store, is among `v`'s slot-`s` Goldfish votes in the store field `core.pool`. -/
theorem mem_pool_of_mem_voteView_afterPhase_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {s : Slot}
    (hsync : Restated.SynchronyFromWakeBefore M S x (M.support_cutoff S.E s)) (htd : Restated.TimeDiverges M x)
    (hmono : Sched.MonotoneCorruption)
    (hs : 0 < s) (hgst : S.E.t_GST ≤ slotStart S.E.Δ s)
    {m mr : Nat} (hm : Restated.tickStepAt M x m (M.vote_time S.E s))
    (hmr : M.support_cutoff S.E s ≤ (x[mr].time : Int))
    (hmrc : (x[mr].time : Int) ≤ M.confirmation_time S.E s)
    {v : V} (hv : v ∉ Sched.adv (x[mr].time : Int))
    (hawT : v ∈ Sched.awakeThroughout (slotStart S.E.Δ s) (M.support_cutoff S.E s))
    (hneTickVote : ∀ v' ∈ Restated.HonSlot M S Sched s, ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) v' (Record.wakeStage M Sched (M.vote_time S.E s) x[m] v') (M.vote_time S.E s) ⇢ out)
    (hneTick : ∀ n : Nat, Restated.tickStepAt M x n (slotStart S.E.Δ s) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched (slotStart S.E.Δ s) x[n] v) (slotStart S.E.Δ s) ⇢ out) :
    ∀ v' ∈ Restated.HonSlot M S Sched s,
      ∀ Y, Restated.voteViewOf M S.E (Restated.voteStoreAt M S (x[mr][v].st) (s + 1)) ⇢ Y →
      ∀ u ∈ Y, u.val_index = v' → u ∈ (M.store_pool (x[mr][v].st).st.core s) := by
  intro v' hv' Y hY u hu hidx
  have hcomm : v' ∈ S.E.committee s := ((Restated.mem_HonSlot facts).mp hv').2.1
  have hv'h : Restated.HonestThrough M Sched x mr v' :=
    Restated.honestThrough_of_mem_HonSlot facts S Sched x hmono hv' hmrc
  have hsc : M.support_cutoff S.E s = slotStart S.E.Δ s + 2 * S.E.Δ :=
    support_cutoff_eq_of_pos facts S.E hs
  have hwh : v ∉ Sched.adv (slotStart S.E.Δ s) := by
    intro hmem
    refine hv (hmono _ _ ?_ hmem)
    rw [hsc] at hmr
    linarith [S.E.Δ_pos]
  have hY' : M.voter_view S.E
      (M.toHealing (Restated.voteStoreAt M S (x[mr][v].st) (s + 1))).toFG.toSG.toGoldfishStore
      (s + 1) ⇢ Y := by
    have h := hY
    simp only [Restated.voteViewOf, Restated.voteStoreAt_slot facts S (x[mr][v].st) (s + 1)] at h
    exact h
  rcases facts.fc.voter_view_cases _ _ _ Y hY' hu with hu | hu
  · have hu1 := hu.1
    rw [facts.sto.toHealing_gs_pool, Nat.add_sub_cancel, Restated.voteStoreAt,
      facts.hd.Sts_setClock_core_pool] at hu1
    exact hu1
  · obtain ⟨Bl, hBlT0, -, huv, huslot⟩ := hu
    rw [Nat.add_sub_cancel] at huslot
    have hBlT : Bl ∈ (x[mr][v].st).st.core.T := by
      rw [facts.sto.toHealing_gs_T, Restated.voteStoreAt, facts.hd.Sts_setClock_core_T] at hBlT0
      exact hBlT0
    obtain ⟨D, hD, hDe⟩ := Restated.exists_named_of_mem_tree facts S Sched x mr v hBlT
    have huD : u ∈ D.gf_votes := by
      rw [← Proofs.NamedWire.erase_goldfish_votes, hDe]; exact huv
    have hne : D ≠ NamedBlock.genesis := by
      intro hcon
      rw [hcon] at huD
      exact absurd huD (by rw [named_genesis_gf_votes]; simp)
    obtain ⟨j, sm, hjm, hsm, hmsg⟩ := Restated.carried_vote_envelope facts S Sched x mr v hne hD
    have hhon : Restated.HonestThrough M Sched x j v' := fun t ht =>
      hv'h t (le_trans ht (Restated.time_mono_int facts S Sched x hjm))
    have hauthor : NamedObject.author (NamedObject.gfVote u) = some v' := by
      rw [author_gfVote, hidx]
    have hsent : (⟨v', NamedObject.gfVote u⟩ : SignedMsg V (NamedObject V)) ∈ x[j].sent :=
      hexec.carried j sm (NamedObject.gfVote u) v' hsm
        (by rw [hmsg]; exact Or.inl ⟨u, huD, rfl⟩) hauthor hhon
    obtain ⟨-, -, -, k, -, hk, -, hueq⟩ :=
      Restated.gfVote_slot_of_sent facts S Sched x (tB := (x[mr].time : Int)) hv'h
        hexec.toUnforgeability hidx (Restated.time_mono_int facts S Sched x hjm) hsent
    rw [huslot] at hk hueq
    rw [Restated.tickStepAt_unique facts x hk hm] at hueq
    obtain ⟨u', hu'⟩ := gfVoteFrom_nonempty_csu facts S (x[m][v'].st) v' s
    rw [hueq u' hu']
    exact (Restated.fresh_vote_in_pool_upTo facts S Sched x hexec hsync htd hs hgst hm
      (Restated.awake_of_mem_HonSlot facts S Sched s hv') hcomm hv'h hmr hawT hwh
      (hneTickVote v' hv') hneTick
      (grade1_at_vote_tick_csu facts S Sched x hm ((Restated.mem_HonSlot facts).mp hv').1
        (fun t ht hmem => ((Restated.mem_HonSlot facts).mp hv').2.2 (hmono t _
          (le_trans ht (facts.sch.Sts_vote_time_le_confirmation_time S s)) hmem))) u' hu').1

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- One step of the slot-to-slot induction, with synchrony up to slot `s`'s support cutoff: if every
    honest active member of slot `s`'s committee votes for a descendant of `B`,
    `ConeSlotHypothesesCompatibleAt` holds at slot `s`, and the ticks named by `hneTickVote` and
    `hneTick` have an outcome, then every honest active member of slot `(s + 1)`'s committee votes
    for a descendant of `B`. -/
theorem headsBelow_succ_ofCompatible_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {s : Slot}
    (hsync : Restated.SynchronyFromWakeBefore M S x (M.support_cutoff S.E s)) (htd : Restated.TimeDiverges M x)
    (hmono : Sched.MonotoneCorruption) {tE : Int}
    (hcs : Restated.committeeSleepinessW M S Sched tE)
    (hs : 0 < s) (hanchor : tE ≤ slotStart S.E.Δ (s + 1))
    (hgst : S.E.t_GST ≤ slotStart S.E.Δ s) {B : Block V}
    (hhyp : Restated.ConeSlotHypothesesCompatibleAt M S Sched x B s) (hprev : Restated.HeadsBelow M S Sched x B s)
    (hneTickVote : ∀ m : Nat, Restated.tickStepAt M x m (M.vote_time S.E s) →
      ∀ q ∈ Restated.HonSlot M S Sched s, ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) q (Record.wakeStage M Sched (M.vote_time S.E s) x[m] q) (M.vote_time S.E s) ⇢ out)
    (hneTick : ∀ v ∈ Restated.HonSlot M S Sched (s + 1), ∀ n : Nat,
      Restated.tickStepAt M x n (slotStart S.E.Δ s) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched (slotStart S.E.Δ s) x[n] v) (slotStart S.E.Δ s) ⇢ out) :
    Restated.HeadsBelow M S Sched x B (s + 1) := by
  intro v mr hv hmr' G hG
  obtain ⟨m, hm⟩ := Restated.exists_tickStepAt facts x htd (facts.sch.vote_time_pos S hs)
  obtain ⟨hawT, hres, hideal, hinlog, hcarried, hviewPool, hvalid, hcompat, hpath⟩ :=
    hhyp v m mr hv hm hmr'
  unfold Restated.gfHeadFrom at hG
  obtain ⟨n, hn, hG⟩ := (returns_bind_iff_csu _ _ _).1 hG
  have hGn := hG
  obtain ⟨T, hT, W, hW, U, hU, hGh⟩ := gfHeadWith_cases_csu _ _ _ _ hG
  obtain ⟨c, -, hneq⟩ := voteReadOf_cases_csu S (x[mr][v].st) (s + 1) hn
  have hcore : n.st = M.store_with_cache (M.ns_setClock S.E (x[mr][v].st).st (M.vote_time S.E (s + 1))) c := by
    rw [hneq, facts.nd.mkNode_st]
  rw [hcore] at hT hW hU hGh
  simp only [Restated.voteTreeOf, Restated.voteViewOf, Restated.voteSupportViewOf, facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at hT hW hU hGh
  change Restated.voteTreeOf M S.E (Restated.voteStoreAt M S (x[mr][v].st) (s + 1)) ⇢ T at hT
  change Restated.voteViewOf M S.E (Restated.voteStoreAt M S (x[mr][v].st) (s + 1)) ⇢ W at hW
  change Restated.voteSupportViewOf M S.E (Restated.voteStoreAt M S (x[mr][v].st) (s + 1)) ⇢ U at hU
  change M.get_head_in_tree_with (M.gradeContract n.cache) S.E S.hc (Restated.voteStoreAt M S (x[mr][v].st) (s + 1)) T W U ((Restated.voteStoreAt M S (x[mr][v].st) (s + 1)).s - 1) ⇢ _ at hGh
  obtain ⟨A, hA⟩ := facts.fc.get_sg_root_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (Restated.voteStoreAt M S (x[mr][v].st) (s + 1)).toHealing
    (M.round_of S.hc (Restated.voteStoreAt M S (x[mr][v].st) (s + 1)).s)
  rcases compatible_cases (hcompat n hn A hA) with hAB | hBA
  · have hd := S.E.Δ_pos
    have hd1 : (1 : Int) ≤ S.E.Δ := by
      simpa only [zero_add] using Int.add_one_le_iff.mpr hd
    obtain ⟨-, hself⟩ := Restated.tickStepAt_time facts x hmr'
    have hvt : M.vote_time S.E (s + 1) = slotStart S.E.Δ s + 5 * S.E.Δ := by
      rw [← facts.sch.slotStart_add_delta_eq_vote_time, slotStart_succ]
      ring
    rw [hvt] at hself
    have hmrle : M.support_cutoff S.E s ≤ (x[mr].time : Int) := by
      rw [support_cutoff_eq_of_pos facts S.E hs]
      linarith
    have hmrc : (x[mr].time : Int) ≤ M.confirmation_time S.E s := by
      rw [← facts.sch.slotStart_add_six_delta_eq_confirmation_time]
      linarith
    have hwh : v ∉ Sched.adv (slotStart S.E.Δ s) := by
      intro hmem
      refine ((Restated.mem_HonSlot facts).mp hv).2.2 (hmono _ _ ?_ hmem)
      rw [← facts.sch.slotStart_add_six_delta_eq_confirmation_time, slotStart_succ]
      linarith
    have hcone := Restated.coneHeads_of_headsBelow facts S Sched x hprev hm hres hideal hinlog
    exact Restated.gf_hop_upTo facts S Sched x hexec hsync htd hmono hcs hs hanchor hgst hm hmrle hmrc
      hawT hwh
      (fun q hq => by
        obtain ⟨H, hH⟩ := gfHeadFrom_nonempty_csu facts S (x[m][q].st) s
        exact ⟨H, hH, hcone q hq H hH⟩)
      hcarried n hn T hT W hW U hU A hA (fun q hq => hviewPool q hq W hW) (hvalid W hW) hAB
      (fun C h1 h2 h3 => hpath n hn A hA C h1 h2 h3 T hT) (hneTickVote m hm) (hneTick v hv) G hGh
  · exact preceq_trans_Preceq hBA
      (Restated.voteAnchor_preceq_gfHeadFrom facts S (x[mr][v].st) (s + 1) n hn A hA G hGn)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- With synchrony up to slot `s`'s support cutoff: if slot `s` is positive, starts at or after `tE`
    and has its support cutoff at or before `tR`, every honest active member of slot `s`'s committee
    votes for a descendant of `B`, `ConeAnchorCompatible` and `ConeAnchorChainInTree` hold at slot
    `s`, and the ticks named by `hneTickVote` and `hneTick` have an outcome, then
    `ConeSlotHypothesesCompatibleAt S Sched x B s` holds. -/
theorem coneSlotHypotheses_afterPhase_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {s : Slot}
    (hsync : Restated.SynchronyFromWakeBefore M S x (M.support_cutoff S.E s))
    (hmult : AwakeAtMultiples S Sched) (htd : Restated.TimeDiverges M x)
    (hmono : Sched.MonotoneCorruption) {tGAT tE tR : Int} (hgst : S.E.t_GST ≤ tGAT)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcs : Restated.committeeSleepinessW M S Sched tE) (hlen : tGAT + S.E.Δ ≤ tE)
    {B : Block V} (hunder : Restated.DeliveredDescendantUnderFinalizedInPhase M S x tGAT tR B)
    (hunderS : Restated.FinalizedPreceqAtStepsInPhase M S x tGAT tR B)
    (hs : 0 < s) (hsE : tE ≤ slotStart S.E.Δ s)
    (hsR : M.support_cutoff S.E s ≤ tR)
    (hAB : Restated.ConeAnchorCompatible M S x B s) (hpath : Restated.ConeAnchorChainInTree M S x B s)
    (hbelow : Restated.HeadsBelow M S Sched x B s)
    (hneTickVote : ∀ m : Nat, Restated.tickStepAt M x m (M.vote_time S.E s) →
      ∀ q ∈ Restated.HonSlot M S Sched s, ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) q (Record.wakeStage M Sched (M.vote_time S.E s) x[m] q) (M.vote_time S.E s) ⇢ out)
    (hneTick : ∀ v ∈ Restated.HonSlot M S Sched (s + 1), ∀ (n' : Nat) (t' : Int),
      Restated.tickStepAt M x n' t' → t' % S.E.Δ = 0 → v ∈ Sched.awake t' \ Sched.adv t' → t' < M.vote_time S.E (s + 1) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched t' x[n'] v) t' ⇢ out) :
    Restated.ConeSlotHypothesesCompatibleAt M S Sched x B s := by
  intro v m mr hv hm hmr'
  have hd := S.E.Δ_pos
  have hd1 : (1 : Int) ≤ S.E.Δ := by
    simpa only [zero_add] using Int.add_one_le_iff.mpr hd
  have hslo : tGAT ≤ slotStart S.E.Δ s := by linarith
  have hgsts : S.E.t_GST ≤ slotStart S.E.Δ s := le_trans hgst hslo
  have hvt : M.vote_time S.E (s + 1) = slotStart S.E.Δ s + 5 * S.E.Δ := by
    have h1 := slotStart_succ S.E.Δ s
    have h2 := facts.sch.slotStart_add_delta_eq_vote_time S.E (s + 1)
    linarith
  have hsc : M.support_cutoff S.E s = slotStart S.E.Δ s + 2 * S.E.Δ :=
      support_cutoff_eq_of_pos facts S.E hs
  have hct : M.confirmation_time S.E s = slotStart S.E.Δ s + 6 * S.E.Δ :=
      (facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E s).symm
  have hct1 : M.confirmation_time S.E (s + 1) = slotStart S.E.Δ s + 10 * S.E.Δ := by
    have h1 := slotStart_succ S.E.Δ s
    have h2 := facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E (s + 1)
    linarith
  obtain ⟨-, hmrself⟩ := Restated.tickStepAt_time facts x hmr'
  rw [hvt] at hmrself
  obtain ⟨-, hmself⟩ := Restated.tickStepAt_time facts x hm
  rw [← facts.sch.slotStart_add_delta_eq_vote_time S.E s] at hmself
  have hmrlo : M.support_cutoff S.E s ≤ (x[mr].time : Int) := by rw [hsc]; linarith
  have hmrc : (x[mr].time : Int) ≤ M.confirmation_time S.E s := by rw [hct]; linarith
  have hmrc1 : (x[mr].time : Int) ≤ M.confirmation_time S.E (s + 1) := by
    rw [hct1]; linarith
  have hmc : (x[m].time : Int) ≤ M.confirmation_time S.E s := by rw [hct]; linarith
  have hvh : Restated.HonestThrough M Sched x mr v :=
    Restated.honestThrough_of_mem_HonSlot facts S Sched x hmono hv hmrc1
  have hvadv : v ∉ Sched.adv (x[mr].time : Int) := hvh _ (le_refl _)
  have hawT := Restated.awakeThroughout_support_of_mem_HonSlot_succ facts S Sched hv
  exact ⟨hawT,
    Restated.headsResolve_afterPhase_upTo facts S Sched x hexec hsync hmult htd hmono hgst hcv hawake hthird hcs hlen
      hunder hunderS hm hmrlo hslo hsR hvadv hawT hbelow
      (fun n' t' h1 hΔ hq h2 => hneTick v hv n' t' h1 hΔ hq (by rw [hvt]; linarith)),
    Restated.treeIdealizes_phase facts S Sched x hexec hvh,
    Restated.headsInPlay_phase facts S Sched x hmono hmc,
    fun Bl hBl => (Restated.treeBlock_carried_ok facts S Sched x hexec mr v hBl).1,
    Restated.mem_pool_of_mem_voteView_afterPhase_upTo facts S Sched x hexec hsync htd hmono hs hgsts hm hmrlo hmrc
      hvadv hawT (hneTickVote m hm) (fun n hn => hneTick v hv n _ hn (slotStart_emod_delta S s)
        (Finset.mem_sdiff.2 ⟨mem_awake_of_awakeThroughout Sched hawT le_rfl (by linarith), hvh _ (by linarith)⟩)
        (by rw [hvt]; linarith)),
    Restated.voteSetValid_phase facts S Sched x hexec,
    hAB v mr hv hmr',
    hpath v mr hv hmr'⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- With synchrony up to slot `s₁`'s support cutoff: if slot `s₀` is positive and starts at or after
    `tE`, slot `s₁`'s support cutoff is at or before `tR`, `ConeAnchorCompatible` and
    `ConeAnchorChainInTree` hold at every slot from `s₀` to `s₁`, the ticks named by `hneTickVote`
    and `hneTick` have an outcome, and every honest active member of slot `s₀`'s committee votes for
    a descendant of `B`, then the same holds at every slot from `s₀` to `s₁ + 1`. -/
theorem headsBelow_range_afterPhase_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {s₀ s₁ : Slot}
    (hsync : Restated.SynchronyFromWakeBefore M S x (M.support_cutoff S.E s₁))
    (hmult : AwakeAtMultiples S Sched) (htd : Restated.TimeDiverges M x)
    (hmono : Sched.MonotoneCorruption) {tGAT tE tR : Int} (hgst : S.E.t_GST ≤ tGAT)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcs : Restated.committeeSleepinessW M S Sched tE) (hlen : tGAT + S.E.Δ ≤ tE)
    {B : Block V} (hunder : Restated.DeliveredDescendantUnderFinalizedInPhase M S x tGAT tR B)
    (hunderS : Restated.FinalizedPreceqAtStepsInPhase M S x tGAT tR B)
    (hs₀ : 0 < s₀) (hsE : tE ≤ slotStart S.E.Δ s₀)
    (hsR : M.support_cutoff S.E s₁ ≤ tR)
    (hAB : ∀ s : Slot, s₀ ≤ s → s ≤ s₁ → Restated.ConeAnchorCompatible M S x B s)
    (hpath : ∀ s : Slot, s₀ ≤ s → s ≤ s₁ → Restated.ConeAnchorChainInTree M S x B s)
    (hbase : Restated.HeadsBelow M S Sched x B s₀)
    (hneTickVote : ∀ s : Slot, s₀ ≤ s → s ≤ s₁ →
      ∀ m : Nat, Restated.tickStepAt M x m (M.vote_time S.E s) →
      ∀ q ∈ Restated.HonSlot M S Sched s, ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) q (Record.wakeStage M Sched (M.vote_time S.E s) x[m] q) (M.vote_time S.E s) ⇢ out)
    (hneTick : ∀ s : Slot, s₀ ≤ s → s ≤ s₁ →
      ∀ v ∈ Restated.HonSlot M S Sched (s + 1), ∀ (n' : Nat) (t' : Int),
      Restated.tickStepAt M x n' t' → t' % S.E.Δ = 0 → v ∈ Sched.awake t' \ Sched.adv t' → t' < M.vote_time S.E (s + 1) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched t' x[n'] v) t' ⇢ out) :
    ∀ s : Slot, s₀ ≤ s → s ≤ s₁ + 1 → Restated.HeadsBelow M S Sched x B s := by
  have hd := S.E.Δ_pos
  -- synchrony up to slot `s₁`'s support cutoff gives synchrony up to the support cutoff of every
  -- slot `s ≤ s₁`
  have hsyncAt : ∀ s : Slot, s ≤ s₁ →
      Restated.SynchronyFromWakeBefore M S x (M.support_cutoff S.E s) := fun s hss1 =>
    fun k w' sm hsend hle haw =>
      hsync k w' sm hsend (le_trans hle (facts.sch.support_cutoff_mono S.E hss1)) haw
  have hbundle : ∀ s : Slot, s₀ ≤ s → s ≤ s₁ → Restated.HeadsBelow M S Sched x B s →
      Restated.ConeSlotHypothesesCompatibleAt M S Sched x B s := by
    intro s hs0s hss1 hbelow
    have hmo := slotStart_mono S hs0s
    have hsRs : M.support_cutoff S.E s ≤ tR :=
      le_trans (facts.sch.support_cutoff_mono S.E hss1) hsR
    exact Restated.coneSlotHypotheses_afterPhase_upTo facts S Sched x hexec
      (hsyncAt s hss1) hmult htd hmono hgst hcv hawake
      hthird hcs hlen hunder hunderS (lt_of_lt_of_le hs₀ hs0s) (le_trans hsE hmo) hsRs
      (hAB s hs0s hss1) (hpath s hs0s hss1) hbelow (hneTickVote s hs0s hss1) (hneTick s hs0s hss1)
  have hlo : tGAT ≤ slotStart S.E.Δ s₀ := by linarith
  intro s hs
  induction s, hs using Nat.le_induction with
  | base => intro _; exact hbase
  | succ s hles ih =>
      intro hsh
      have hsle : s ≤ s₁ := Nat.le_of_succ_le_succ hsh
      have hprev : Restated.HeadsBelow M S Sched x B s := ih (Nat.le_succ_of_le hsle)
      have hvt : M.vote_time S.E (s + 1) = slotStart S.E.Δ s + 5 * S.E.Δ := by
        have h1 := slotStart_succ S.E.Δ s
        have h2 := facts.sch.slotStart_add_delta_eq_vote_time S.E (s + 1)
        linarith
      exact Restated.headsBelow_succ_ofCompatible_upTo facts S Sched x hexec
        (hsyncAt s hsle) htd hmono hcs
        (lt_of_lt_of_le hs₀ hles)
        (le_trans hsE (slotStart_mono S (Nat.le_succ_of_le hles)))
        (le_trans (le_trans hgst hlo) (slotStart_mono S hles))
        (hbundle s hles hsle hprev) hprev (hneTickVote s hles hsle)
        (fun v hv n hn => hneTick s hles hsle v hv n _ hn (slotStart_emod_delta S s)
          (Finset.mem_sdiff.2 ⟨mem_awake_of_awakeThroughout Sched
              (Restated.awakeThroughout_support_of_mem_HonSlot_succ facts S Sched hv) le_rfl
              (by rw [support_cutoff_eq_of_pos facts S.E (lt_of_lt_of_le hs₀ hles)]; linarith),
            fun hin => ((Restated.mem_HonSlot facts).mp hv).2.2 (hmono _ _
              (by have h1 := slotStart_succ S.E.Δ s
                  have h2 := facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E (s + 1)
                  linarith) hin)⟩)
          (by rw [hvt]; linarith))

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- With synchrony up to the support cutoff of round `r + 1`'s opening slot: if that slot starts at
    or after `tE` and has its support cutoff at or before `tR`, `n` is the tick step at
    `S.a (r + 1)`, `v` is in `HonRound S Sched (r + 1)`, every honest active member of the opening
    slot's committee votes for a descendant of `T`'s erasure, the anchor `A` read under the phase
    tick's outcome `c` satisfies `hAB` and `hpath`, and the ticks named by `hneTickVote` and
    `hneTick` have an outcome, then every store `hs` round `(r + 1)`'s action can read from `v`'s
    node state at step `n` and satisfying `hF` and `hJ` has its confirmed block compatible with
    `T`'s erasure. -/
theorem live_confirmed_compatible_at_action_afterPhase_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {r : Round}
    (hsync : Restated.SynchronyFromWakeBefore M S x (M.support_cutoff S.E ((M.opening_slot S.hc (r + 1)))))
    (hmult : AwakeAtMultiples S Sched) (htd : Restated.TimeDiverges M x)
    (hmono : Sched.MonotoneCorruption) {tGAT tE tR : Int} (hgst : S.E.t_GST ≤ tGAT)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcs : Restated.committeeSleepinessW M S Sched tE) (hlen : tGAT + S.E.Δ ≤ tE)
    {n : Nat} {v : V} {T : NamedBlock V}
    (hunder : Restated.DeliveredDescendantUnderFinalizedInPhase M S x tGAT tR T.erase)
    (hunderS : Restated.FinalizedPreceqAtStepsInPhase M S x tGAT tR T.erase)
    (hsE : tE ≤ slotStart S.E.Δ ((M.opening_slot S.hc (r + 1))))
    (hsR : M.support_cutoff S.E ((M.opening_slot S.hc (r + 1))) ≤ tR)
    (hn : Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    (hv : v ∈ Restated.HonRound M S Sched (r + 1))
    (hprev : Restated.HeadsBelow M S Sched x T.erase ((M.opening_slot S.hc (r + 1))))
    (c : M.Cache) (hc : M.onPhaseTick S.E S.hc (M.toHealing (x[n][v].st).st.core)
      (M.confirmation_time S.E ((M.opening_slot S.hc (r + 1)))) (x[n][v].st).cache ⇢ c)
    (A : Block V) (hA : Restated.Vocabulary.Protocol.confAnchorWith M (M.gradeContract c) S.E S.hc
      (Restated.confStoreAt M S (x[n][v].st) ((M.opening_slot S.hc (r + 1)))) ⇢ A)
    (hAB : Block.Preceq A T.erase)
    (hpath : ∀ C : Block V, Block.Preceq A C → C ≠ A → Block.Preceq C T.erase →
      C ∈ Restated.Vocabulary.Protocol.confTree M (Restated.confStoreAt M S (x[n][v].st) ((M.opening_slot S.hc (r + 1)))))
    (hs : M.HS) (hhs : hs ∈ Restated.actionHealingStore M S (x[n][v].st) (r + 1))
    (hF : Block.Preceq hs.F T.erase)
    (hJ : hs.h_max = hs.h_j + 1 → Block.compatible hs.J T.erase = true)
    (hneTickVote : ∀ m : Nat, Restated.tickStepAt M x m (M.vote_time S.E ((M.opening_slot S.hc (r + 1)))) →
      ∀ q ∈ Restated.HonSlot M S Sched ((M.opening_slot S.hc (r + 1))), ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) q (Record.wakeStage M Sched (M.vote_time S.E ((M.opening_slot S.hc (r + 1)))) x[m] q) (M.vote_time S.E ((M.opening_slot S.hc (r + 1)))) ⇢ out)
    (hneTick : ∀ (n' : Nat) (t' : Int), Restated.tickStepAt M x n' t' → t' % S.E.Δ = 0 → v ∈ Sched.awake t' \ Sched.adv t' →
      t' ≤ M.confirmation_time S.E ((M.opening_slot S.hc (r + 1))) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched t' x[n'] v) t' ⇢ out) :
    Block.compatible hs.live_confirmed T.erase = true := by
  have hd := S.E.Δ_pos
  have hd1 : (1 : Int) ≤ S.E.Δ := by
    simpa only [zero_add] using Int.add_one_le_iff.mpr hd
  have hct : M.confirmation_time S.E ((M.opening_slot S.hc (r + 1))) = (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) :=
    Restated.confirmation_time_opening_slot facts S (r + 1)
  have hct' : M.confirmation_time S.E ((M.opening_slot S.hc (r + 1))) = slotStart S.E.Δ ((M.opening_slot S.hc (r + 1))) + 6 * S.E.Δ :=
      (facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E ((M.opening_slot S.hc (r + 1)))).symm
  have hsc : M.support_cutoff S.E ((M.opening_slot S.hc (r + 1))) ≤ slotStart S.E.Δ ((M.opening_slot S.hc (r + 1))) + 5 * S.E.Δ := by
    have h1 := facts.sch.support_cutoff_le_vote_time_succ S.E ((M.opening_slot S.hc (r + 1)))
    have h2 := facts.sch.slotStart_add_delta_eq_vote_time S.E ((M.opening_slot S.hc (r + 1)) + 1)
    have h3 := slotStart_succ S.E.Δ ((M.opening_slot S.hc (r + 1)))
    linarith
  have hslo : tGAT ≤ slotStart S.E.Δ ((M.opening_slot S.hc (r + 1))) := by linarith
  have hgsts : S.E.t_GST ≤ slotStart S.E.Δ ((M.opening_slot S.hc (r + 1))) := le_trans hgst hslo
  have hanchor : tE ≤ slotStart S.E.Δ ((M.opening_slot S.hc (r + 1)) + 1) :=
    le_trans hsE (slotStart_mono S (Nat.le_succ _))
  have hawRound := Restated.honRound_awakeThroughout_confirmation facts S Sched (r + 1) hv
  have hawTc : v ∈ Sched.awakeThroughout (slotStart S.E.Δ ((M.opening_slot S.hc (r + 1))))
      (M.confirmation_time S.E ((M.opening_slot S.hc (r + 1)))) :=
    awakeThroughout_mono Sched hawRound (by linarith) le_rfl
  have hwaw : v ∈ Sched.awakeThroughout (slotStart S.E.Δ ((M.opening_slot S.hc (r + 1))))
      (M.support_cutoff S.E ((M.opening_slot S.hc (r + 1)))) :=
    awakeThroughout_mono Sched hawTc le_rfl (by rw [hct']; linarith)
  have hvadvA : v ∉ Sched.adv ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) := (Finset.mem_sdiff.1 hv).2
  have hvh : HonestThroughTime Sched
      (M.confirmation_time S.E ((M.opening_slot S.hc (r + 1)))) v := by
    intro t' ht' hmem
    exact hvadvA (hmono _ _ (by rw [← hct]; exact ht') hmem)
  obtain ⟨-, hnself⟩ := Restated.tickStepAt_time facts x hn
  have hn6 : (x[n].time : Int) + 1 = slotStart S.E.Δ ((M.opening_slot S.hc (r + 1))) + 6 * S.E.Δ := by
    rw [← hct', hct]; exact hnself
  have hnc : (x[n].time : Int) ≤ M.confirmation_time S.E ((M.opening_slot S.hc (r + 1))) := by
    rw [hct']; linarith
  have hnlo : M.support_cutoff S.E ((M.opening_slot S.hc (r + 1))) ≤ (x[n].time : Int) := by
    linarith
  have hvn : Restated.HonestThrough M Sched x n v := fun t' ht' => hvh t' (le_trans ht' hnc)
  have hvnadv : v ∉ Sched.adv (x[n].time : Int) := hvn _ (le_refl _)
  have hres : ∀ m : Nat,
      Restated.tickStepAt M x m (M.vote_time S.E ((M.opening_slot S.hc (r + 1)))) →
      Restated.HeadsResolve M S Sched x v m n ((M.opening_slot S.hc (r + 1))) := fun m hm =>
    Restated.headsResolve_afterPhase_upTo facts S Sched x hexec hsync hmult htd hmono hgst hcv hawake hthird hcs
      hlen hunder hunderS hm hnlo hslo hsR hvnadv hwaw hprev
      (fun n' t' h1 hΔ hq h2 => hneTick n' t' h1 hΔ hq (by rw [hct']; linarith))
  have hinlog : ∀ m : Nat,
      Restated.tickStepAt M x m (M.vote_time S.E ((M.opening_slot S.hc (r + 1)))) →
      ∀ v' ∈ Restated.HonSlot M S Sched ((M.opening_slot S.hc (r + 1))), ∀ G : Block V,
        Restated.gfHeadFrom M S (x[m][v'].st) ((M.opening_slot S.hc (r + 1))) ⇢ G →
        ∃ H : NamedBlock V, Restated.blockInLog M S Sched x H ∧ H.erase = G := by
    intro m hm
    obtain ⟨-, hmself⟩ := Restated.tickStepAt_time facts x hm
    have hvt : M.vote_time S.E ((M.opening_slot S.hc (r + 1))) = slotStart S.E.Δ ((M.opening_slot S.hc (r + 1))) + S.E.Δ :=
      (facts.sch.slotStart_add_delta_eq_vote_time S.E ((M.opening_slot S.hc (r + 1)))).symm
    rw [hvt] at hmself
    exact Restated.headsInPlay_phase facts S Sched x hmono (by rw [hct']; linarith)
  exact Restated.live_confirmed_compatible_at_action_upTo facts S Sched x hexec hsync htd hmono hcs hanchor hgsts hn
    hawTc hvh hprev hres (Restated.treeIdealizes_phase facts S Sched x hexec hvn) hinlog
    (Restated.voteSetValid_conf facts S Sched x n v ((M.opening_slot S.hc (r + 1))))
    c hc A hA hAB hpath hs hhs hF hJ
    hneTickVote
    (fun n' hn' => hneTick n' _ hn' (slotStart_emod_delta S (M.opening_slot S.hc (r + 1)))
      (Finset.mem_sdiff.2 ⟨mem_awake_of_awakeThroughout Sched hawTc le_rfl (by rw [hct']; linarith),
        hvh _ (by rw [hct']; linarith)⟩) (by rw [hct']; linarith))
    (hneTick n _ (by rw [hct]; exact hn) (by rw [hct]; exact Restated.action_emod_delta facts S (r + 1))
      (Finset.mem_sdiff.2 ⟨mem_awake_of_awakeThroughout Sched hawTc (by rw [hct']; linarith) le_rfl,
        hvh _ le_rfl⟩) le_rfl)
    -- the grade-2 awake test at `v`'s confirmation tick
    (by
      have hround : M.round_of S.hc (M.opening_slot S.hc (r + 1) + 1) = r + 1 :=
        facts.gr.round_of_opening_slot_add S.hc (r + 1)
          (lt_of_lt_of_le (by norm_num) S.hc.R_ge_three)
      rw [hround, hct]
      obtain ⟨τ, hlbl, hτ⟩ := hn
      refine Restated.run_fact_g2 facts S Sched x n τ (r + 1) v hlbl hτ ?_ (by
        rw [hτ]
        intro t ht
        exact hvh t (by rw [hct]; exact ht))
      have hw := (Finset.mem_sdiff.1 hv).1
      have h12 := twelve_delta_le_wAttest S
      simp only [Restated.activeRoundW, Schedule.awakeThroughout, Finset.mem_inf,
        Finset.mem_Icc] at hw ⊢
      rw [facts.gr.early_g2_eq S (r + 1)]
      intro t ht
      exact hw t ⟨by linarith [ht.1], ht.2⟩)

end

end DecoupledConsensusModel.Sts.Restated
