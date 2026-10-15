import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bStepCone
import Proofs.Claims.Restated.Claim13bStepKitConfirm
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bStepKitRelay
import Proofs.Claims.Restated.Claim13bSyncViewUpTo
import Proofs.Claims.Restated.RunAll
import Proofs.Claims.Restated.VocabularyAssumptionsLemmas
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_SlotInduction
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bStepCone
import Model.Conditions.ClaimAsyncK_DeliveryUpTo
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Agreement
import Model.Conditions.Vocabulary_Protocol_Grades_Main
import Model.Record.Wiring
import Proofs.Claims.Restated.WakeWindow

/-!
# The cone of support, with synchrony up to a cutoff

The Goldfish votes of a slot reach a receiver's pool before the slot's support cutoff, give a cone
of support for a block in its voter and confirmation views, and so fix the head and the confirmed
block that follow, assuming synchrony only up to the slot's support cutoff. Stated over a model
`M : Record.Model V` and its facts `facts : Record.Facts M`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

/-! ## Helpers on outcome sets -/

section
open DecoupledConsensusModel.Execution

open scoped DC in
/-- An outcome of `f <$> m` is `f a` for an outcome `a` of `m`. -/
private theorem returns_map_elim_cone {α β : Type} (f : α → β) (m : DC.NDRE α) (b : β)
    (h : (f <$> m) ⇢ b) : ∃ a, m ⇢ a ∧ f a = b := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image] at h
  obtain ⟨e, he, hb⟩ := h
  cases e with
  | ok a => exact ⟨a, he, by simpa [Except.map] using hb⟩
  | error err => simp [Except.map] at hb

open scoped DC in
/-- If `m` can return `a`, then `f <$> m` can return `f a`. -/
private theorem returns_map_intro_cone {α β : Type} (f : α → β) (m : DC.NDRE α) (a : α)
    (h : m ⇢ a) : (f <$> m) ⇢ f a := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image]
  exact ⟨_, h, rfl⟩

/-- Every outcome of `confVotes` at slot `s` is, for an outcome `tm` of `st`'s resolution times, the
    slot-`s` pool filtered by `tm` against the support cutoff and then by the absence of a second
    vote of the same signer in the late set. -/
private theorem confVotes_cases (E : Env V) (st : M.S) (s : Slot) {e : Finset (GoldfishVote V)}
    (he : Restated.Vocabulary.Protocol.confVotes M E st s ⇢ e) :
    ∃ tm, st.tau ⇢ tm ∧
      e = (beforeCutoff tm (M.support_cutoff E s) (st.pool s)).filter
        (fun u => M.no_second_vote_in (Restated.Vocabulary.Protocol.confLate M E st s) u = true) := by
  obtain ⟨e', he', rfl⟩ := returns_map_elim_cone _ _ _ he
  obtain ⟨tm, htm, rfl⟩ := returns_map_elim_cone _ _ _ he'
  exact ⟨tm, htm, rfl⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For `0 < s`, slot `s`'s support cutoff is two delays after the slot's start. -/
private theorem support_cutoff_eq_of_pos (facts : Record.Facts M) (E : Env V) {s : Slot}
    (hs : 0 < s) : M.support_cutoff E s = slotStart E.Δ s + 2 * E.Δ := by
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, (Nat.succ_pred_eq_of_pos hs).symm⟩
  rw [← facts.sch.confirmation_time_eq_support_cutoff_succ,
    ← facts.sch.slotStart_add_six_delta_eq_confirmation_time, slotStart_succ]
  ring

/-- A Goldfish vote of `q` that slot `s`'s vote tick at step `m` added to the sent log is an honest
    send at step `m`, when `q` is honest through a step at or after the slot's support cutoff. -/
private theorem gfVote_honestSend_at_tick (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) {s : Slot} (hs : 0 < s)
    {m : Nat} (hm : Restated.tickStepAt M x m (M.vote_time S.E s))
    {q : V} {u : GoldfishVote V} (_huslot : u.slot = s)
    (hsent : (⟨q, NamedObject.gfVote u⟩ : SignedMsg V (NamedObject V))
      ∈ x[m + 1].sent - x[m].sent)
    {mr : Nat} (hqh : Restated.HonestThrough M Sched x mr q)
    (hmr : M.support_cutoff S.E s ≤ (x[mr].time : Int)) :
    Restated.HonestSendAt M S x m (⟨q, NamedObject.gfVote u⟩ : SignedMsg V (NamedObject V)) := by
  have hd := S.E.Δ_pos
  have hvt : M.vote_time S.E s = slotStart S.E.Δ s + S.E.Δ :=
    (facts.sch.slotStart_add_delta_eq_vote_time S.E s).symm
  have hsc : M.support_cutoff S.E s = slotStart S.E.Δ s + 2 * S.E.Δ :=
    support_cutoff_eq_of_pos facts S.E hs
  have hmtime : (x[m].time : Int) + 1 = M.vote_time S.E s := (Restated.tickStepAt_time facts x hm).2
  have hmle : (x[m].time : Int) ≤ (x[mr].time : Int) := by
    have h1 : (x[m].time : Int) = slotStart S.E.Δ s + S.E.Δ - 1 := by
      rw [hvt] at hmtime; linarith
    have h2 : slotStart S.E.Δ s + 2 * S.E.Δ ≤ (x[mr].time : Int) := by rw [← hsc]; exact hmr
    linarith
  have hqm : Restated.HonestThrough M Sched x m q := fun t ht => hqh t (le_trans ht hmle)
  exact And.intro hsent (hqm _ (le_refl _))

/-- A Goldfish vote honestly sent at the step before slot `s`'s vote instant is delivered to a
    receiver `w` awake from the slot's start to its support cutoff, at a step strictly before that
    cutoff and before step `mr`, when synchrony from wake holds up to that cutoff. -/
private theorem gfVote_delivery_step_upTo (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) {s : Slot}
    (hsync : Restated.SynchronyFromWakeBefore M S x (M.support_cutoff S.E s))
    (hs : 0 < s) (hgst : S.E.t_GST ≤ slotStart S.E.Δ s)
    {q w : V} {u : GoldfishVote V} {i : Nat}
    (hsend : Restated.HonestSendAt M S x i (⟨q, NamedObject.gfVote u⟩ : SignedMsg V (NamedObject V)))
    (hitime : (x[i].time : Int) + 1 = M.vote_time S.E s)
    {mr : Nat} (hmr : M.support_cutoff S.E s ≤ (x[mr].time : Int))
    (hawT : w ∈ Sched.awakeThroughout (slotStart S.E.Δ s) (M.support_cutoff S.E s)) :
    ∃ k : Nat, k + 1 ≤ mr ∧ (x[k].time : Int) < M.support_cutoff S.E s ∧
      x.lbl k = AtomicAction.deliver w ⟨q, NamedObject.gfVote u⟩ := by
  have hd := S.E.Δ_pos
  have hvt : M.vote_time S.E s = slotStart S.E.Δ s + S.E.Δ :=
    (facts.sch.slotStart_add_delta_eq_vote_time S.E s).symm
  have hsc : M.support_cutoff S.E s = slotStart S.E.Δ s + 2 * S.E.Δ :=
    support_cutoff_eq_of_pos facts S.E hs
  have hit : (x[i].time : Int) = slotStart S.E.Δ s + S.E.Δ - 1 := by
    rw [hvt] at hitime; linarith
  have hmax : max (x[i].time : Int) S.E.t_GST = (x[i].time : Int) :=
    max_eq_left (by rw [hit]; linarith)
  have hwin : w ∈ Sched.awakeThroughout (x[i].time : Int)
      (max (x[i].time : Int) S.E.t_GST + S.E.Δ) := by
    refine awakeThroughout_mono Sched hawT ?_ ?_
    · rw [hit]; linarith
    · rw [hmax, hit, hsc]; linarith
  have hb : max (x[i].time : Int) S.E.t_GST + S.E.Δ ≤ M.support_cutoff S.E s := by
    rw [hmax, hit, hsc]; linarith
  have hsync' : Restated.SynchronyFromWakeBefore M S x
      (max (x[i].time : Int) S.E.t_GST + S.E.Δ) :=
    fun k' w' sm' hs' hle haw => hsync k' w' sm' hs' (le_trans hle hb) haw
  obtain ⟨k, -, hlbl, -, hlt⟩ := Restated.synchronyFromWake_from_step_upTo facts S hsync' hsend hwin
  rw [hmax, hit] at hlt
  have hkcut : (x[k].time : Int) < M.support_cutoff S.E s := by rw [hsc]; linarith
  refine ⟨k, ?_, hkcut, hlbl⟩
  by_contra hcon
  have hmrk : mr ≤ k := by omega
  have h := Restated.time_mono_int facts S Sched x hmrk
  linarith

/-- If step `k` delivers `q`'s slot-`s` vote `u` to `w` strictly before the slot's support cutoff
    and before step `mr`, then `w`'s store at step `mr` holds `u` in its slot-`s` pool with a stamp
    strictly before the cutoff; the second half of `fresh_vote_in_pool_upTo`. -/
private theorem fresh_vote_after_delivery (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (htd : Restated.TimeDiverges M x) {s : Slot} (hs : 0 < s) {q w : V} {u : GoldfishVote V}
    (huslot : u.slot = s) (huidx : u.val_index = q) (hcomm : q ∈ S.E.committee s) {k mr : Nat}
    (hlbl : x.lbl k = AtomicAction.deliver w ⟨q, NamedObject.gfVote u⟩) (hk1mr : k + 1 ≤ mr)
    (hkstrict : (x[k].time : Int) < M.support_cutoff S.E s)
    (hqh : Restated.HonestThrough M Sched x mr q)
    (hawT : w ∈ Sched.awakeThroughout (slotStart S.E.Δ s) (M.support_cutoff S.E s))
    (hwh : w ∉ Sched.adv (slotStart S.E.Δ s))
    (hneTick : ∀ n : Nat, Restated.tickStepAt M x n (slotStart S.E.Δ s) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) w (Record.wakeStage M Sched (slotStart S.E.Δ s) x[n] w) (slotStart S.E.Δ s) ⇢ out) :
    u ∈ (M.store_pool (x[mr][w].st).st.core s) ∧
      ∃ τ : Stamp, (x[mr][w].st).st.core.timestamp_vote u = some τ ∧
        τ < ((M.support_cutoff S.E s : Int) : Stamp) := by
  have hd := S.E.Δ_pos
  have hvt : M.vote_time S.E s = slotStart S.E.Δ s + S.E.Δ :=
    (facts.sch.slotStart_add_delta_eq_vote_time S.E s).symm
  have hsc : M.support_cutoff S.E s = slotStart S.E.Δ s + 2 * S.E.Δ :=
    support_cutoff_eq_of_pos facts S.E hs
  have hkmr : k ≤ mr := by omega
  have hqk : Restated.HonestThrough M Sched x k q := fun t ht =>
    hqh t (le_trans ht (Restated.time_mono_int facts S Sched x hkmr))
  have hsentk : (⟨q, NamedObject.gfVote u⟩ : SignedMsg V (NamedObject V)) ∈ x[k].sent :=
    (Restated.sent_of_deliver facts S Sched x hlbl).1
  obtain ⟨-, -, -, k_0, hk_0k, htick_0, -, -⟩ :=
    Restated.gfVote_slot_of_sent facts S Sched x (tB := (x[k].time : Int)) hqk hexec.toUnforgeability huidx
      (le_refl _) hsentk
  have hlo : slotStart S.E.Δ s ≤ (x[k].time : Int) := by
    have h1 : (x[k_0 + 1].time : Int) = M.vote_time S.E u.slot :=
      (Restated.tickStepAt_time facts x htick_0).1
    have h2 : (x[k_0 + 1].time : Int) ≤ (x[k].time : Int) :=
      Restated.time_mono_int facts S Sched x (Nat.succ_le_of_lt hk_0k)
    rw [h1, huslot, hvt] at h2
    linarith
  have hhi : (x[k].time : Int) < slotStart S.E.Δ (u.slot + 2) := by
    rw [huslot]
    have hexp : slotStart S.E.Δ (s + 2) = slotStart S.E.Δ s + 8 * S.E.Δ := by
      rw [slotStart_add]
      push_cast; ring
    rw [hexp]
    rw [hsc] at hkstrict
    linarith
  have hawTk : w ∈ Sched.awakeThroughout (slotStart S.E.Δ u.slot) (x[k].time : Int) := by
    rw [huslot]
    exact awakeThroughout_shrink Sched hawT (le_of_lt hkstrict)
  have hwin := Restated.gf_window_of_awakeThroughout facts S Sched x htd k w u hawTk
    (by rw [huslot]; exact hwh) (by rw [huslot]; exact hlo) (by rw [huslot]; exact hs) hhi
    (by rw [huslot]; exact hneTick)
  have hcommu : u.val_index ∈ S.E.committee u.slot := by rw [huidx, huslot]; exact hcomm
  have hstampAt : ∀ n : Nat, (x[n][w].st).st.core.t ≤ (x[k].time : Int) →
      u ∈ (M.store_pool (x[n][w].st).st.core u.slot) → n ≤ mr →
      (u ∈ (M.store_pool (x[mr][w].st).st.core s) ∧
        ∃ τ : Stamp, (x[mr][w].st).st.core.timestamp_vote u = some τ ∧
          τ < ((M.support_cutoff S.E s : Int) : Stamp)) := by
    intro n hclk hmem hnmr
    obtain ⟨τ, hτ, hb⟩ := Restated.stamp_le_clock_gfVote facts S Sched x n w hmem
    refine ⟨by rw [← huslot]; exact Restated.mem_pool_mono_sts facts S Sched x w hnmr hmem, τ,
      Restated.stamp_mono_sts facts S Sched x w hnmr hτ, ?_⟩
    refine lt_of_le_of_lt (le_trans hb (WithBot.coe_le_coe.mpr hclk)) ?_
    exact WithBot.coe_lt_coe.mpr hkstrict
  have hdt : x[k + 1].time = x[k].time := Restated.deliver_time facts S Sched x hlbl
  rcases Restated.gfVote_recorded_of_deliver facts S Sched x hlbl hwin hcommu
      (facts.nd.process_nonempty _ _ _ (fun _ h => by cases h)) with hmk | heq | ⟨hm1, hst1⟩
  · exact hstampAt k (Restated.clock_le_time_sts facts S Sched x k w) hmk hkmr
  · have hne := Restated.no_equiv_of_honest facts S Sched x hexec (w := w) hqk u.slot
    rw [huidx] at heq
    exact Bool.noConfusion (heq.symm.trans hne)
  · have hclk1 : (x[k + 1][w].st).st.core.t ≤ (x[k].time : Int) := by
      have h1 : (x[k + 1][w].st).st.core.t ≤ (x[k + 1].time : Int) :=
        Restated.clock_le_time_sts facts S Sched x (k + 1) w
      rw [hdt] at h1
      exact h1
    exact hstampAt (k + 1) hclk1 hm1 hk1mr

/-- `fresh_vote_in_pool` with synchrony assumed only up to slot `s`'s support cutoff: `w`'s store at
    step `mr` holds every slot-`s` vote `gfVoteFrom` names for `q` in its slot-`s` pool, with a
    stamp strictly before the cutoff. -/
theorem fresh_vote_in_pool_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {s : Slot}
    (hsync : Restated.SynchronyFromWakeBefore M S x (M.support_cutoff S.E s)) (htd : Restated.TimeDiverges M x)
    (hs : 0 < s) (hgst : S.E.t_GST ≤ slotStart S.E.Δ s)
    {m : Nat} (hm : Restated.tickStepAt M x m (M.vote_time S.E s))
    {q : V} (hqaw : q ∈ Sched.awake (M.vote_time S.E s)) (hcomm : q ∈ S.E.committee s)
    {w : V} {mr : Nat} (hqh : Restated.HonestThrough M Sched x mr q)
    (hmr : M.support_cutoff S.E s ≤ (x[mr].time : Int))
    (hawT : w ∈ Sched.awakeThroughout (slotStart S.E.Δ s) (M.support_cutoff S.E s))
    (hwh : w ∉ Sched.adv (slotStart S.E.Δ s))
    (hneTickVote : ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) q (Record.wakeStage M Sched (M.vote_time S.E s) x[m] q) (M.vote_time S.E s) ⇢ out)
    (hneTick : ∀ n : Nat, Restated.tickStepAt M x n (slotStart S.E.Δ s) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) w (Record.wakeStage M Sched (slotStart S.E.Δ s) x[n] w) (slotStart S.E.Δ s) ⇢ out)
    (hrun : M.awake_for_grade1 (Setup.alwaysAwake S) q
      (Record.wakeStage M Sched (M.vote_time S.E s) x[m] q) (M.round_of S.hc s)) :
    ∀ u, Restated.gfVoteFrom M S (x[m][q].st) q s ⇢ u →
      u ∈ (M.store_pool (x[mr][w].st).st.core s) ∧
        ∃ τ : Stamp, (x[mr][w].st).st.core.timestamp_vote u = some τ ∧
          τ < ((M.support_cutoff S.E s : Int) : Stamp) := by
  have _hr_0 : M.reachedNode (x[m][q].st) := Record.reachedNode_sts facts S Sched x m q
  have _hr_1 : M.reachedNode (Record.wakeStage M Sched (M.vote_time S.E s) x[m] q) := Record.reachedNode_wakeStage facts S Sched x m q (M.vote_time S.E s)
  intro u hu
  have hd := S.E.Δ_pos
  have hvt : M.vote_time S.E s = slotStart S.E.Δ s + S.E.Δ :=
    (facts.sch.slotStart_add_delta_eq_vote_time S.E s).symm
  have hsc : M.support_cutoff S.E s = slotStart S.E.Δ s + 2 * S.E.Δ :=
    support_cutoff_eq_of_pos facts S.E hs
  have huslot : u.slot = s := Restated.gfVoteFrom_slot facts S (x[m][q].st) q s u hu
  have huidx : u.val_index = q := Restated.gfVoteFrom_val_index facts S (x[m][q].st) q s u hu
  have hsent : (⟨q, NamedObject.gfVote u⟩ :
        SignedMsg V (NamedObject V)) ∈ x[m + 1].sent - x[m].sent := by
    obtain ⟨t', hlbl_m, ht'⟩ := id hm
    have hqv : q ∈ Sched.awake (M.vote_time S.E s) \ Sched.adv (M.vote_time S.E s) :=
      Finset.mem_sdiff.2 ⟨hqaw, hqh _ (by rw [hvt]; rw [hsc] at hmr; linarith)⟩
    refine Restated.mem_sent_diff_of_tick facts S Sched x hlbl_m (by rw [ht']; exact hqv)
      (by rw [ht']; exact facts.sch.vote_time_emod_delta S s) ?_ (by rw [ht']; exact hneTickVote)
    rw [ht']
    have hvf : Restated.gfVoteFrom M S (Record.wakeStage M Sched (M.vote_time S.E s) x[m] q) q s =
        Restated.gfVoteFrom M S (x[m][q].st) q s := by
      simp only [Restated.gfVoteFrom, Restated.gfHeadFrom, Restated.voteReadOf,
        Record.wakeStage_st facts, Record.wakeStage_record facts, Record.wakeStage_cache facts]
    have _hr_g := Record.reachedNode_wakeStage facts S Sched x m q (M.vote_time S.E s)
    have _hv_g := Record.runs_as_wakeStage facts S Sched x m q (M.vote_time S.E s)
    exact fun out hout => Restated.namedTick_emits_gfVote facts S q _ s hs hcomm hrun out
      hout u (by rw [hvf]; exact hu)
  obtain ⟨k, hk1mr, hkstrict, hlbl⟩ :=
    gfVote_delivery_step_upTo facts S Sched x hsync hs hgst
      (gfVote_honestSend_at_tick facts S Sched x hs hm huslot hsent hqh hmr)
      (Restated.tickStepAt_time facts x hm).2 hmr hawT
  exact fresh_vote_after_delivery facts S Sched x hexec htd hs huslot huidx hcomm hlbl hk1mr
    hkstrict hqh hawT hwh hneTick

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If `before` holds the vote `⟨q, s, X.root⟩` in its slot-`s` pool and the block `X`, of slot at
    most `s`, both stamped before slot `s`'s support cutoff, then the vote is in every outcome of
    the slot-`(s + 1)` support view of the store slot `s + 1`'s vote duty reads. -/
private theorem vote_mem_support_view_cone (facts : Record.Facts M) (S : Setup V) (before : M.N)
    {s : Slot} {q : V} {X : Block V} {τ σ : Stamp}
    (hpool : (⟨q, s, X.root⟩ : GoldfishVote V) ∈ M.store_pool before.st.core s)
    (hτ : before.st.core.timestamp_vote ⟨q, s, X.root⟩ = some τ)
    (hτlt : τ < ((M.support_cutoff S.E s : Int) : Stamp))
    (hfind : Block.find? before.st.core.T X.root = some X) (hXs : X.slot ≤ s)
    (hσ : before.st.core.timestamp_block X = some σ)
    (hσlt : σ < ((M.support_cutoff S.E s : Int) : Stamp))
    (U : Finset (GoldfishVote V)) (hU : M.voter_support_view S.E
      (M.toHealing (Restated.voteStoreAt M S before (s + 1))).toFG.toSG.toGoldfishStore (s + 1) ⇢ U) :
    (⟨q, s, X.root⟩ : GoldfishVote V) ∈ U := by
  have hgT : (M.toHealing (Restated.voteStoreAt M S before (s + 1))).toFG.toSG.toGoldfishStore.T
      = before.st.core.T := by
    rw [facts.sto.toHealing_gs_T, Restated.voteStoreAt, facts.hd.Sts_setClock_core_T]
  have hgP : M.gs_pool (M.toHealing (Restated.voteStoreAt M S before (s + 1))).toFG.toSG.toGoldfishStore s
      = M.store_pool before.st.core s := by
    rw [facts.sto.toHealing_gs_pool, Restated.voteStoreAt, facts.hd.Sts_setClock_core_pool]
  have hgV :
      (M.toHealing (Restated.voteStoreAt M S before (s + 1))).toFG.toSG.toGoldfishStore.timestamp_vote
        = before.st.core.timestamp_vote := by
    rw [facts.sto.toHealing_gs_timestamp_vote, Restated.voteStoreAt,
      facts.hd.setClock_core_timestamp_vote]
  have hgB :
      (M.toHealing (Restated.voteStoreAt M S before (s + 1))).toFG.toSG.toGoldfishStore.timestamp_block
        = before.st.core.timestamp_block := by
    rw [facts.sto.toHealing_gs_timestamp_block, Restated.voteStoreAt,
      facts.hd.setClock_core_timestamp_block]
  have hvfr : ((M.support_cutoff S.E s : Int) : Stamp) < ((M.view_freeze S.E s : Int) : Stamp) :=
    WithBot.coe_lt_coe.mpr (facts.sch.Sts_support_cutoff_lt_view_freeze S.E s)
  rw [← hgP] at hpool
  rw [← hgV] at hτ
  rw [← hgT] at hfind
  rw [← hgB] at hσ
  exact facts.sch.mem_voter_support_view_of_pool S.E _ s hpool hτ (lt_trans hτlt hvfr) hfind hXs
    hσ (lt_trans hσlt hvfr) U hU

/-- A validator awake throughout slot `s`'s vote window is awake from one delay before the grade-1
    early cutoff of `s`'s round to `s`'s vote instant. -/
private theorem grade1_window_of_activeAtW_cone (facts : Record.Facts M) (S : Setup V)
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

/-- If step `m` is the tick at slot `s`'s vote instant, and `q` is awake throughout slot `s`'s vote
    window and not held by the adversary up to that instant, then the node state `q`'s tick at step
    `m` reads passes the grade-1 awake test of `s`'s round. -/
private theorem grade1_at_vote_tick_cone (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) {m : Nat} {s : Slot}
    (hm : Restated.tickStepAt M x m (M.vote_time S.E s)) {q : V} (hq : q ∈ activeAtW S Sched s)
    (hhon : ∀ t' ≤ M.vote_time S.E s, q ∉ Sched.adv t') :
    M.awake_for_grade1 (Setup.alwaysAwake S) q
      (Record.wakeStage M Sched (M.vote_time S.E s) x[m] q) (M.round_of S.hc s) := by
  obtain ⟨τ, hlbl, hτ⟩ := hm
  have h := Restated.run_fact_g1 facts S Sched x m τ s q hlbl (Or.inr hτ)
    (by rw [hτ]; exact grade1_window_of_activeAtW_cone facts S Sched hq) (by rw [hτ]; exact hhon)
  rw [hτ] at h
  exact h

/-- `coneSupport_at_slot` with synchrony assumed only up to slot `s`'s support cutoff: `w`'s
    slot-`(s + 1)` voter views carry a cone of support for the descendants of `B` at slot `s`. -/
theorem coneSupport_at_slot_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {s : Slot}
    (hsync : Restated.SynchronyFromWakeBefore M S x (M.support_cutoff S.E s)) (htd : Restated.TimeDiverges M x)
    (hmono : Sched.MonotoneCorruption) {tE : Int}
    (hcs : Restated.committeeSleepinessW M S Sched tE)
    (hs : 0 < s) (hanchor : tE ≤ slotStart S.E.Δ (s + 1))
    (hgst : S.E.t_GST ≤ slotStart S.E.Δ s)
    {m : Nat} (hm : Restated.tickStepAt M x m (M.vote_time S.E s))
    {w : V} {mr : Nat}
    (hmr : M.support_cutoff S.E s ≤ (x[mr].time : Int))
    (hmrc : (x[mr].time : Int) ≤ M.confirmation_time S.E s)
    (hawT : w ∈ Sched.awakeThroughout (slotStart S.E.Δ s) (M.support_cutoff S.E s))
    (hwh : w ∉ Sched.adv (slotStart S.E.Δ s))
    {B : Block V}
    (hheads : ∀ q ∈ Restated.HonSlot M S Sched s, ∃ H : Block V,
      Restated.gfHeadFrom M S (x[m][q].st) s ⇢ H ∧ ∃ X : Block V,
      X.root = H.root ∧ Block.Preceq B X ∧ X.slot ≤ s ∧
        Block.find? (x[mr][w].st).st.core.T X.root = some X ∧
        ∃ σ : Stamp, (x[mr][w].st).st.core.timestamp_block X = some σ ∧
          σ < ((M.support_cutoff S.E s : Int) : Stamp))
    (hcarried : ∀ Bl ∈ (x[mr][w].st).st.core.T,
      ∀ u ∈ Bl.gf_support_votes, u ∈ Bl.gf_votes)
    (W : Finset (GoldfishVote V))
    (hW : Restated.voteViewOf M S.E (Restated.voteStoreAt M S (x[mr][w].st) (s + 1)) ⇢ W)
    (hviewPool : ∀ q ∈ Restated.HonSlot M S Sched s,
      ∀ u ∈ W, u.val_index = q → u ∈ (M.store_pool (x[mr][w].st).st.core s))
    (hneTickVote : ∀ q ∈ Restated.HonSlot M S Sched s, ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) q (Record.wakeStage M Sched (M.vote_time S.E s) x[m] q) (M.vote_time S.E s) ⇢ out)
    (hneTick : ∀ n : Nat, Restated.tickStepAt M x n (slotStart S.E.Δ s) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) w (Record.wakeStage M Sched (slotStart S.E.Δ s) x[n] w) (slotStart S.E.Δ s) ⇢ out) :
    ∀ U, Restated.voteSupportViewOf M S.E (Restated.voteStoreAt M S (x[mr][w].st) (s + 1)) ⇢ U →
      Restated.Vocabulary.Proofs.Optimistic.ConeSupport M S.E
        (Restated.voteStoreAt M S (x[mr][w].st) (s + 1)).T W U W
        ((Restated.voteStoreAt M S (x[mr][w].st) (s + 1)).s - 1) (Restated.HonSlot M S Sched s)
        (fun X => Block.Preceq B X) := by
  intro U hU
  have hT : (Restated.voteStoreAt M S (x[mr][w].st) (s + 1)).T = (x[mr][w].st).st.core.T := by
    rw [Restated.voteStoreAt, facts.hd.Sts_setClock_core_T]
  have hgT : (M.toHealing (Restated.voteStoreAt M S (x[mr][w].st) (s + 1))).toFG.toSG.toGoldfishStore.T
      = (x[mr][w].st).st.core.T := by
    rw [facts.sto.toHealing_gs_T, hT]
  have hsc : (Restated.voteStoreAt M S (x[mr][w].st) (s + 1)).s - 1 = s := by
    simp only [Restated.voteStoreAt_slot facts S (x[mr][w].st) (s + 1), Nat.add_sub_cancel]
  rw [hsc]
  have hW' : M.voter_view S.E
      (M.toHealing (Restated.voteStoreAt M S (x[mr][w].st) (s + 1))).toFG.toSG.toGoldfishStore
      (s + 1) ⇢ W := by
    have h := hW
    simp only [Restated.voteViewOf, Restated.voteStoreAt_slot facts S (x[mr][w].st) (s + 1)] at h
    exact h
  have hU' : M.voter_support_view S.E
      (M.toHealing (Restated.voteStoreAt M S (x[mr][w].st) (s + 1))).toFG.toSG.toGoldfishStore
      (s + 1) ⇢ U := by
    have h := hU
    simp only [Restated.voteSupportViewOf, Restated.voteStoreAt_slot facts S (x[mr][w].st) (s + 1)]
      at h
    exact h
  refine Restated.Vocabulary.Proofs.Optimistic.coneSupport_of_named_votes facts
    (Restated.majority_of_committeeSleepinessW facts S Sched hcs hanchor) (Finset.Subset.refl _)
    (facts.fc.voter_support_view_subset S.E _ (s + 1) (by rw [hgT]; exact hcarried) U hU' W hW')
    ?_ ?_
  · intro q _ hqH
    exact Restated.no_equiv_of_subset_pool facts S Sched x hexec
      (Restated.honestThrough_of_mem_HonSlot facts S Sched x hmono hqH hmrc) (w := w) (s := s)
      (hviewPool q hqH)
  · intro q _ hqH
    obtain ⟨H, hH, X, hXroot, hBX, hXs, hfind, σ, hσ, hσlt⟩ := hheads q hqH
    have hu : Restated.gfVoteFrom M S (x[m][q].st) q s ⇢ (⟨q, s, X.root⟩ : GoldfishVote V) := by
      rw [hXroot]
      exact returns_map_intro_cone (fun H : Block V => (⟨q, s, H.root⟩ : GoldfishVote V)) _ H hH
    obtain ⟨hpool, τ, hτ, hτlt⟩ :=
      Restated.fresh_vote_in_pool_upTo facts S Sched x hexec hsync htd hs hgst hm
        (Restated.awake_of_mem_HonSlot facts S Sched s hqH) ((Restated.mem_HonSlot facts).mp hqH).2.1
        (Restated.honestThrough_of_mem_HonSlot facts S Sched x hmono hqH hmrc) hmr hawT hwh
        (hneTickVote q hqH) hneTick
        (grade1_at_vote_tick_cone facts S Sched x hm ((Restated.mem_HonSlot facts).mp hqH).1
          (fun t ht hmem => ((Restated.mem_HonSlot facts).mp hqH).2.2 (hmono t _
            (le_trans ht (facts.sch.Sts_vote_time_le_confirmation_time S s)) hmem))) _ hu
    exact ⟨X, hBX, hXs,
      vote_mem_support_view_cone facts S (x[mr][w].st) hpool hτ hτlt hfind hXs hσ hσlt U hU',
      by rw [hT]; exact hfind⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- `gf_hop` with synchrony assumed only up to slot `s`'s support cutoff: every head `w`'s
    slot-`(s + 1)` vote duty selects along the given outcomes is a descendant of `B`. -/
theorem gf_hop_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {s : Slot}
    (hsync : Restated.SynchronyFromWakeBefore M S x (M.support_cutoff S.E s)) (htd : Restated.TimeDiverges M x)
    (hmono : Sched.MonotoneCorruption) {tE : Int}
    (hcs : Restated.committeeSleepinessW M S Sched tE)
    (hs : 0 < s) (hanchor : tE ≤ slotStart S.E.Δ (s + 1))
    (hgst : S.E.t_GST ≤ slotStart S.E.Δ s)
    {m : Nat} (hm : Restated.tickStepAt M x m (M.vote_time S.E s))
    {w : V} {mr : Nat}
    (hmr : M.support_cutoff S.E s ≤ (x[mr].time : Int))
    (hmrc : (x[mr].time : Int) ≤ M.confirmation_time S.E s)
    (hawT : w ∈ Sched.awakeThroughout (slotStart S.E.Δ s) (M.support_cutoff S.E s))
    (hwh : w ∉ Sched.adv (slotStart S.E.Δ s))
    {B : Block V}
    (hheads : ∀ q ∈ Restated.HonSlot M S Sched s, ∃ H : Block V,
      Restated.gfHeadFrom M S (x[m][q].st) s ⇢ H ∧ ∃ X : Block V,
      X.root = H.root ∧ Block.Preceq B X ∧ X.slot ≤ s ∧
        Block.find? (x[mr][w].st).st.core.T X.root = some X ∧
        ∃ σ : Stamp, (x[mr][w].st).st.core.timestamp_block X = some σ ∧
          σ < ((M.support_cutoff S.E s : Int) : Stamp))
    (hcarried : ∀ Bl ∈ (x[mr][w].st).st.core.T,
      ∀ u ∈ Bl.gf_support_votes, u ∈ Bl.gf_votes)
    (n : M.N) (hn : Restated.voteReadOf M S (x[mr][w].st) (s + 1) ⇢ n)
    (T : Finset (Block V))
    (hT : Restated.voteTreeOf M S.E (Restated.voteStoreAt M S (x[mr][w].st) (s + 1)) ⇢ T)
    (W : Finset (GoldfishVote V))
    (hW : Restated.voteViewOf M S.E (Restated.voteStoreAt M S (x[mr][w].st) (s + 1)) ⇢ W)
    (U : Finset (GoldfishVote V))
    (hU : Restated.voteSupportViewOf M S.E (Restated.voteStoreAt M S (x[mr][w].st) (s + 1)) ⇢ U)
    (A : Block V)
    (hA : Restated.voteAnchorOf M (M.gradeContract n.cache) S.E S.hc
      (Restated.voteStoreAt M S (x[mr][w].st) (s + 1)) ⇢ A)
    (hviewPool : ∀ q ∈ Restated.HonSlot M S Sched s,
      ∀ u ∈ W, u.val_index = q → u ∈ (M.store_pool (x[mr][w].st).st.core s))
    (hvalid : Protocol.VoteSetValid S.E ((Restated.voteStoreAt M S (x[mr][w].st) (s + 1)).s - 1) W)
    (hAB : Block.Preceq A B)
    (hpath : ∀ C : Block V, Block.Preceq A C → C ≠ A → Block.Preceq C B → C ∈ T)
    (hneTickVote : ∀ q ∈ Restated.HonSlot M S Sched s, ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) q (Record.wakeStage M Sched (M.vote_time S.E s) x[m] q) (M.vote_time S.E s) ⇢ out)
    (hneTick : ∀ n : Nat, Restated.tickStepAt M x n (slotStart S.E.Δ s) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) w (Record.wakeStage M Sched (slotStart S.E.Δ s) x[n] w) (slotStart S.E.Δ s) ⇢ out) :
    ∀ H, M.get_head_in_tree_with (M.gradeContract n.cache) S.E S.hc
        (Restated.voteStoreAt M S (x[mr][w].st) (s + 1)) T W U
        ((Restated.voteStoreAt M S (x[mr][w].st) (s + 1)).s - 1) ⇢ H →
      Block.Preceq B H :=
  Restated.head_preceq_of_cone facts (M.gradeContract n.cache)
    S.E S.hc (Restated.voteStoreAt M S (x[mr][w].st) (s + 1)) T hT W hW U hU A hA
    (Restated.coneSupport_at_slot_upTo facts S Sched x hexec hsync htd hmono hcs hs hanchor
      hgst hm hmr hmrc hawT hwh hheads hcarried W hW hviewPool hneTickVote hneTick U hU)
    hvalid hAB hpath

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Every outcome of `confVotes` at slot `s` is inside the store's slot-`s` pool. -/
private theorem confVotes_subset_pool_cone (E : Env V) (st : M.S) (s : Slot) :
    ∀ e, Restated.Vocabulary.Protocol.confVotes M E st s ⇢ e → e ⊆ M.store_pool st s := by
  intro e he u hu
  obtain ⟨e', he', rfl⟩ := returns_map_elim_cone _ _ _ he
  obtain ⟨tm, -, rfl⟩ := returns_map_elim_cone _ _ _ he'
  rw [Finset.mem_filter, mem_beforeCutoff_iff] at hu
  exact hu.1.1

/-- `coneSupport_at_confirmation` with synchrony assumed only up to slot `s`'s support cutoff: `w`'s
    slot-`s` confirmation views carry, for every outcome of its confirmation votes, a cone of
    support for the descendants of `B` at slot `s`. -/
theorem coneSupport_at_confirmation_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {s : Slot}
    (hsync : Restated.SynchronyFromWakeBefore M S x (M.support_cutoff S.E s)) (htd : Restated.TimeDiverges M x)
    (hmono : Sched.MonotoneCorruption) {tE : Int}
    (hcs : Restated.committeeSleepinessW M S Sched tE)
    (hs : 0 < s) (hanchor : tE ≤ slotStart S.E.Δ (s + 1))
    (hgst : S.E.t_GST ≤ slotStart S.E.Δ s)
    {m : Nat} (hm : Restated.tickStepAt M x m (M.vote_time S.E s))
    {w : V} {mr : Nat}
    (hmr : M.support_cutoff S.E s ≤ (x[mr].time : Int))
    (hmrc : (x[mr].time : Int) ≤ M.confirmation_time S.E s)
    (hawT : w ∈ Sched.awakeThroughout (slotStart S.E.Δ s) (M.support_cutoff S.E s))
    (hwh : w ∉ Sched.adv (slotStart S.E.Δ s))
    {B : Block V}
    (hheads : ∀ q ∈ Restated.HonSlot M S Sched s, ∃ H : Block V,
      Restated.gfHeadFrom M S (x[m][q].st) s ⇢ H ∧ ∃ X : Block V,
      X.root = H.root ∧ Block.Preceq B X ∧ X.slot ≤ s ∧
        Block.find? (x[mr][w].st).st.core.T X.root = some X ∧
        ∃ σ : Stamp, (x[mr][w].st).st.core.timestamp_block X = some σ ∧
          σ < ((M.support_cutoff S.E s : Int) : Stamp))
    (hneTickVote : ∀ q ∈ Restated.HonSlot M S Sched s, ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) q (Record.wakeStage M Sched (M.vote_time S.E s) x[m] q) (M.vote_time S.E s) ⇢ out)
    (hneTick : ∀ n : Nat, Restated.tickStepAt M x n (slotStart S.E.Δ s) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) w (Record.wakeStage M Sched (slotStart S.E.Δ s) x[n] w) (slotStart S.E.Δ s) ⇢ out) :
    ∀ e, Restated.Vocabulary.Protocol.confVotes M S.E (Restated.confStoreAt M S (x[mr][w].st) s) s ⇢ e →
      Restated.Vocabulary.Proofs.Optimistic.ConeSupport M S.E
        (Restated.confStoreAt M S (x[mr][w].st) s).T e e
        (Restated.Vocabulary.Protocol.confLate M S.E (Restated.confStoreAt M S (x[mr][w].st) s) s)
        s (Restated.HonSlot M S Sched s) (fun X => Block.Preceq B X) := by
  intro e he
  refine Restated.Vocabulary.Proofs.Optimistic.coneSupport_of_named_votes facts
    (Restated.majority_of_committeeSleepinessW facts S Sched hcs hanchor)
    (Restated.confVotes_subset_confLate facts S.E _ s e he) (Finset.Subset.refl _) ?_ ?_
  · intro q _ hqH
    refine Restated.no_equiv_of_subset_pool facts S Sched x hexec
      (Restated.honestThrough_of_mem_HonSlot facts S Sched x hmono hqH hmrc) (w := w) (s := s) ?_
    intro u hu _
    rw [← facts.hd.Sts_setClock_core_pool S.E (x[mr][w].st).st (M.confirmation_time S.E s) s]
    exact confVotes_subset_pool_cone S.E _ s e he hu
  · intro q _ hqH
    obtain ⟨H, hH, X, hXroot, hBX, hXs, hfind, σ, hσ, hσlt⟩ := hheads q hqH
    have hu : Restated.gfVoteFrom M S (x[m][q].st) q s ⇢ (⟨q, s, X.root⟩ : GoldfishVote V) := by
      rw [hXroot]
      exact returns_map_intro_cone (fun H : Block V => (⟨q, s, H.root⟩ : GoldfishVote V)) _ H hH
    obtain ⟨hpoolX, τ, hτ, hτlt⟩ :=
      Restated.fresh_vote_in_pool_upTo facts S Sched x hexec hsync htd hs hgst hm
        (Restated.awake_of_mem_HonSlot facts S Sched s hqH) ((Restated.mem_HonSlot facts).mp hqH).2.1
        (Restated.honestThrough_of_mem_HonSlot facts S Sched x hmono hqH hmrc) hmr hawT hwh
        (hneTickVote q hqH) hneTick
        (grade1_at_vote_tick_cone facts S Sched x hm ((Restated.mem_HonSlot facts).mp hqH).1
          (fun t ht hmem => ((Restated.mem_HonSlot facts).mp hqH).2.2 (hmono t _
            (le_trans ht (facts.sch.Sts_vote_time_le_confirmation_time S s)) hmem))) _ hu
    have hfind' : Block.find? (Restated.confStoreAt M S (x[mr][w].st) s).T X.root = some X := by
      rw [Restated.confStoreAt, facts.hd.Sts_setClock_core_T]
      exact hfind
    have hpool' : (⟨q, s, X.root⟩ : GoldfishVote V) ∈
        (M.store_pool (Restated.confStoreAt M S (x[mr][w].st) s) s) := by
      rw [Restated.confStoreAt, facts.hd.Sts_setClock_core_pool]
      exact hpoolX
    have hτ' : (Restated.confStoreAt M S (x[mr][w].st) s).timestamp_vote ⟨q, s, X.root⟩
        = some τ := by
      rw [Restated.confStoreAt, facts.hd.setClock_core_timestamp_vote]
      exact hτ
    have hσ' : (Restated.confStoreAt M S (x[mr][w].st) s).timestamp_block X = some σ := by
      rw [Restated.confStoreAt, facts.hd.setClock_core_timestamp_block]
      exact hσ
    refine ⟨X, hBX, hXs, ?_, hfind'⟩
    refine Restated.mem_confVotes_of facts S.E _ (u := ⟨q, s, X.root⟩) hpool'
      hτ' hτlt hfind' hXs hσ' hσlt ?_ e he
    intro u' hu' hidx
    have hu'' : u' ∈ (M.store_pool (x[mr][w].st).st.core s) := by
      rw [← facts.hd.Sts_setClock_core_pool S.E (x[mr][w].st).st (M.confirmation_time S.E s) s]
      exact hu'
    exact Restated.gfVote_unique_of_honest facts S Sched x hexec
      (Restated.honestThrough_of_mem_HonSlot facts S Sched x hmono hqH hmrc) (s := s) hu'' hpoolX
      hidx rfl

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- `confirmed_hop` with synchrony assumed only up to slot `s`'s support cutoff: every head of `w`'s
    slot-`s` confirmation walk from `A` is a descendant of `B`. -/
theorem confirmed_hop_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {s : Slot}
    (hsync : Restated.SynchronyFromWakeBefore M S x (M.support_cutoff S.E s)) (htd : Restated.TimeDiverges M x)
    (hmono : Sched.MonotoneCorruption) {tE : Int}
    (hcs : Restated.committeeSleepinessW M S Sched tE)
    (hs : 0 < s) (hanchor : tE ≤ slotStart S.E.Δ (s + 1))
    (hgst : S.E.t_GST ≤ slotStart S.E.Δ s)
    {m : Nat} (hm : Restated.tickStepAt M x m (M.vote_time S.E s))
    {w : V} {mr : Nat}
    (hmr : M.support_cutoff S.E s ≤ (x[mr].time : Int))
    (hmrc : (x[mr].time : Int) ≤ M.confirmation_time S.E s)
    (hawT : w ∈ Sched.awakeThroughout (slotStart S.E.Δ s) (M.support_cutoff S.E s))
    (hwh : w ∉ Sched.adv (slotStart S.E.Δ s))
    {B : Block V}
    (hheads : ∀ q ∈ Restated.HonSlot M S Sched s, ∃ H : Block V,
      Restated.gfHeadFrom M S (x[m][q].st) s ⇢ H ∧ ∃ X : Block V,
      X.root = H.root ∧ Block.Preceq B X ∧ X.slot ≤ s ∧
        Block.find? (x[mr][w].st).st.core.T X.root = some X ∧
        ∃ σ : Stamp, (x[mr][w].st).st.core.timestamp_block X = some σ ∧
          σ < ((M.support_cutoff S.E s : Int) : Stamp))
    (contract : M.Contract)
    (hvalid : Protocol.VoteSetValid S.E s
      (Restated.Vocabulary.Protocol.confLate M S.E (Restated.confStoreAt M S (x[mr][w].st) s) s))
    (A : Block V)
    (hA : Restated.Vocabulary.Protocol.confAnchorWith M contract S.E S.hc
      (Restated.confStoreAt M S (x[mr][w].st) s) ⇢ A)
    (hAB : Block.Preceq A B)
    (hpath : ∀ C : Block V, Block.Preceq A C → C ≠ A →
      Block.Preceq C B → C ∈ Restated.Vocabulary.Protocol.confTree M (Restated.confStoreAt M S (x[mr][w].st) s))
    (hneTickVote : ∀ q ∈ Restated.HonSlot M S Sched s, ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) q (Record.wakeStage M Sched (M.vote_time S.E s) x[m] q) (M.vote_time S.E s) ⇢ out)
    (hneTick : ∀ n : Nat, Restated.tickStepAt M x n (slotStart S.E.Δ s) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) w (Record.wakeStage M Sched (slotStart S.E.Δ s) x[n] w) (slotStart S.E.Δ s) ⇢ out) :
    ∀ e, Restated.Vocabulary.Protocol.confVotes M S.E (Restated.confStoreAt M S (x[mr][w].st) s) s ⇢ e →
      ∀ sc : Block V → ℕ, (∀ C, M.goldfish_score S.E (Restated.confStoreAt M S (x[mr][w].st) s).T
          e e s C ⇢ sc C) →
      ∀ X, M.ghost A (Restated.Vocabulary.Protocol.confTree M (Restated.confStoreAt M S (x[mr][w].st) s))
          sc (fun C => decide (Restated.Vocabulary.Protocol.confCount M S.E
            (Restated.confStoreAt M S (x[mr][w].st) s) s < 2 * sc C)) ⇢ X →
        Block.Preceq B X := by
  intro e he sc hsc X hX
  have hsup := Restated.coneSupport_at_confirmation_upTo facts S Sched x hexec hsync htd hmono
    hcs hs hanchor hgst hm hmr hmrc hawT hwh hheads hneTickVote hneTick e he
  exact facts.fc.ghost_passes_cone S.E (Restated.confStoreAt M S (x[mr][w].st) s).T
    (Restated.Vocabulary.Protocol.confTree M (Restated.confStoreAt M S (x[mr][w].st) s)) e e
    (Restated.Vocabulary.Protocol.confLate M S.E (Restated.confStoreAt M S (x[mr][w].st) s) s) s
    (Restated.HonSlot M S Sched s)
    hsup.majority hsup.counted hsup.sub hsup.no_equiv hsup.vote hvalid hAB hpath sc hsc X hX

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If step `n` is the tick at slot `s`'s confirmation instant, `w` is awake and not held by the
    adversary there, `w`'s tick at step `n` has an outcome, and the node state it reads passes the
    grade-2 awake test of slot `s + 1`'s round, then after the step `w`'s `live_confirmed` is the
    head `W` of the confirmation walk from `A` along the given outcomes, or the FG root of its
    clock-stamped store. -/
private theorem live_confirmed_after_confirmation_tick_cases (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    {n : Nat} {s : Slot} (hn : Restated.tickStepAt M x n (M.confirmation_time S.E s)) {w : V}
    (haw : w ∈ Sched.awake (M.confirmation_time S.E s) \ Sched.adv (M.confirmation_time S.E s))
    (hneTickConf : ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) w (Record.wakeStage M Sched (M.confirmation_time S.E s) x[n] w) (M.confirmation_time S.E s) ⇢ out)
    (hrun : M.awake_for_grade2 (Setup.alwaysAwake S) w
      (Record.wakeStage M Sched (M.confirmation_time S.E s) x[n] w) (M.round_of S.hc (s + 1)))
    (c : M.Cache) (hc : M.onPhaseTick S.E S.hc (M.toHealing (x[n][w].st).st.core)
      (M.confirmation_time S.E s) (x[n][w].st).cache ⇢ c)
    (A : Block V) (hA : Restated.Vocabulary.Protocol.confAnchorWith M (M.gradeContract c) S.E S.hc
      (Restated.confStoreAt M S (x[n][w].st) s) ⇢ A)
    (e : Finset (GoldfishVote V))
    (he : Restated.Vocabulary.Protocol.confVotes M S.E (Restated.confStoreAt M S (x[n][w].st) s) s ⇢ e)
    (sc : Block V → ℕ)
    (hsc : ∀ C, M.goldfish_score S.E (Restated.confStoreAt M S (x[n][w].st) s).T e e s C ⇢ sc C)
    (W : Block V)
    (hW : M.ghost A (Restated.Vocabulary.Protocol.confTree M (Restated.confStoreAt M S (x[n][w].st) s))
      sc (fun C => decide (Restated.Vocabulary.Protocol.confCount M S.E
        (Restated.confStoreAt M S (x[n][w].st) s) s < 2 * sc C)) ⇢ W) :
    (x[n + 1][w].st).st.core.live_confirmed = W ∨
      (x[n + 1][w].st).st.core.live_confirmed
        = Restated.Vocabulary.Protocol.confRoot M (Restated.confStoreAt M S (x[n][w].st) s) := by
  have _hr_0 : M.reachedNode (x[n][w].st) := Record.reachedNode_sts facts S Sched x n w
  have _hr_1 : M.reachedNode (Record.wakeStage M Sched (M.support_cutoff S.E (s + 1)) x[n] w) := Record.reachedNode_wakeStage facts S Sched x n w (M.support_cutoff S.E (s + 1))
  obtain ⟨t', hlbl, ht'⟩ := id hn
  have hct := facts.sch.confirmation_time_eq_support_cutoff_succ S.E s
  have hdvd : (t' : Int) % S.E.Δ = 0 := by
    rw [ht', hct]
    exact facts.sch.support_cutoff_emod_delta S (s + 1)
  have haw' : w ∈ Sched.awake (t' : Int) \ Sched.adv (t' : Int) := by rw [ht']; exact haw
  rcases Restated.st_succ_of_tick_awake facts S Sched x w hlbl haw' hdvd with
    ⟨out₁, hout, hst⟩ | ⟨hno, -⟩
  · rw [hst]
    rw [ht', hct] at hout
    rw [hct] at hc
    obtain ⟨D, hD⟩ := facts.dt.duties_update_confirmation_with_nonempty (M.gradeContract c) S.E
      S.hc (M.ns_setClock S.E (x[n][w].st).st (M.support_cutoff S.E (s + 1))) (s + 1 - 1)
    obtain ⟨X, hX⟩ := facts.dt.update_confirmation_with_nonempty (M.gradeContract c) S.E S.hc
      (M.ns_setClock S.E (x[n][w].st).st (M.support_cutoff S.E (s + 1))).core (s + 1 - 1)
    have hc' : M.onPhaseTick S.E S.hc
        (Record.wakeStage M Sched (M.support_cutoff S.E (s + 1)) x[n] w).st.core.toHealing
        (M.support_cutoff S.E (s + 1))
        (Record.wakeStage M Sched (M.support_cutoff S.E (s + 1)) x[n] w).cache ⇢ c := by
      rw [Record.wakeStage_st facts, Record.wakeStage_cache facts]; exact hc
    have hD' : M.duties_update_confirmation_with (M.gradeContract c) S.E S.hc
        (M.ns_setClock S.E (Record.wakeStage M Sched (M.support_cutoff S.E (s + 1)) x[n] w).st
          (M.support_cutoff S.E (s + 1))) (s + 1 - 1) ⇢ D := by
      rw [Record.wakeStage_st facts]; exact hD
    rw [hct] at hrun
    rw [facts.nd.on_tick_emit_confirmation_of_outcomes (Setup.alwaysAwake S) w _
        (s + 1) (Nat.succ_pos s) out₁ hout c hc' D hD' hrun,
      facts.dt.named_update_confirmation_with_core _ _ _ _ _ D hD X hX]
    rw [Nat.add_sub_cancel] at hX
    obtain ⟨tm, htm, rfl⟩ := confVotes_cases S.E _ s he
    have hconf : Restated.confStoreAt M S (x[n][w].st) s
        = (M.ns_setClock S.E (x[n][w].st).st (M.support_cutoff S.E (s + 1))).core := by
      rw [Restated.confStoreAt, hct]
    rw [hconf] at hA htm hsc hW ⊢
    exact facts.hd.update_confirmation_with_live_confirmed_walk_or_fgRoot _ _ _ _ _ tm htm A hA
      sc hsc W hW X hX
  · obtain ⟨o, ho⟩ := hneTickConf
    rw [← ht'] at ho
    exact absurd ho (hno o)

/-- `live_confirmed_cases_of_cone` with synchrony assumed only up to slot `s`'s support cutoff:
    right after the tick at slot `s`'s confirmation instant, `w` holds as its `live_confirmed`
    either a descendant of `B` or the FG root of its own clock-stamped store. -/
theorem live_confirmed_cases_of_cone_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {s : Slot}
    (hsync : Restated.SynchronyFromWakeBefore M S x (M.support_cutoff S.E s)) (htd : Restated.TimeDiverges M x)
    (hmono : Sched.MonotoneCorruption) {tE : Int}
    (hcs : Restated.committeeSleepinessW M S Sched tE)
    (hs : 0 < s) (hanchor : tE ≤ slotStart S.E.Δ (s + 1))
    (hgst : S.E.t_GST ≤ slotStart S.E.Δ s)
    {m : Nat} (hm : Restated.tickStepAt M x m (M.vote_time S.E s))
    {w : V} {n : Nat} (hn : Restated.tickStepAt M x n (M.confirmation_time S.E s))
    (hawTc : w ∈ Sched.awakeThroughout (slotStart S.E.Δ s) (M.confirmation_time S.E s))
    (hwh : HonestThroughTime Sched (M.confirmation_time S.E s) w)
    {B : Block V}
    (hheads : ∀ q ∈ Restated.HonSlot M S Sched s, ∃ H : Block V,
      Restated.gfHeadFrom M S (x[m][q].st) s ⇢ H ∧ ∃ X : Block V,
      X.root = H.root ∧ Block.Preceq B X ∧ X.slot ≤ s ∧
        Block.find? (x[n][w].st).st.core.T X.root = some X ∧
        ∃ σ : Stamp, (x[n][w].st).st.core.timestamp_block X = some σ ∧
          σ < ((M.support_cutoff S.E s : Int) : Stamp))
    (hvalid : Protocol.VoteSetValid S.E s
      (Restated.Vocabulary.Protocol.confLate M S.E (Restated.confStoreAt M S (x[n][w].st) s) s))
    (c : M.Cache) (hc : M.onPhaseTick S.E S.hc (M.toHealing (x[n][w].st).st.core)
      (M.confirmation_time S.E s) (x[n][w].st).cache ⇢ c)
    (A : Block V) (hA : Restated.Vocabulary.Protocol.confAnchorWith M (M.gradeContract c) S.E S.hc
      (Restated.confStoreAt M S (x[n][w].st) s) ⇢ A)
    (hAB : Block.Preceq A B)
    (hpath : ∀ C : Block V, Block.Preceq A C → C ≠ A →
      Block.Preceq C B → C ∈ Restated.Vocabulary.Protocol.confTree M (Restated.confStoreAt M S (x[n][w].st) s))
    (hneTickVote : ∀ q ∈ Restated.HonSlot M S Sched s, ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) q (Record.wakeStage M Sched (M.vote_time S.E s) x[m] q) (M.vote_time S.E s) ⇢ out)
    (hneTick : ∀ n' : Nat, Restated.tickStepAt M x n' (slotStart S.E.Δ s) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) w (Record.wakeStage M Sched (slotStart S.E.Δ s) x[n'] w) (slotStart S.E.Δ s) ⇢ out)
    (hneTickConf : ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) w (Record.wakeStage M Sched (M.confirmation_time S.E s) x[n] w) (M.confirmation_time S.E s) ⇢ out)
    (hrun : M.awake_for_grade2 (Setup.alwaysAwake S) w
      (Record.wakeStage M Sched (M.confirmation_time S.E s) x[n] w) (M.round_of S.hc (s + 1))) :
    Block.Preceq B (x[n + 1][w].st).st.core.live_confirmed ∨
      (x[n + 1][w].st).st.core.live_confirmed
        = Restated.Vocabulary.Protocol.confRoot M (Restated.confStoreAt M S (x[n][w].st) s) := by
  have hd := S.E.Δ_pos
  have hsc : M.support_cutoff S.E s = slotStart S.E.Δ s + 2 * S.E.Δ :=
    support_cutoff_eq_of_pos facts S.E hs
  have hct : M.confirmation_time S.E s = slotStart S.E.Δ s + 6 * S.E.Δ :=
    (facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E s).symm
  obtain ⟨hnsucc, hnself⟩ := Restated.tickStepAt_time facts x hn
  have hd1 : (1 : Int) ≤ S.E.Δ := Int.add_one_le_iff.mpr hd
  have hmr : M.support_cutoff S.E s ≤ (x[n].time : Int) := by
    rw [hsc]; rw [hct] at hnself; linarith
  have hmrc : (x[n].time : Int) ≤ M.confirmation_time S.E s := by
    rw [hct]; rw [hct] at hnself; linarith
  have hawT : w ∈ Sched.awakeThroughout (slotStart S.E.Δ s) (M.support_cutoff S.E s) :=
    awakeThroughout_shrink Sched hawTc
      (facts.sch.Sts_support_cutoff_le_confirmation_time S.E s)
  have haw : w ∈ Sched.awake (M.confirmation_time S.E s) :=
    mem_awake_of_awakeThroughout Sched hawTc (by rw [hct]; linarith) (le_refl _)
  obtain ⟨tm, htm⟩ := facts.sto.tau_nonempty (Restated.confStoreAt M S (x[n][w].st) s)
  obtain ⟨e, he⟩ : ∃ e, Restated.Vocabulary.Protocol.confVotes M S.E
      (Restated.confStoreAt M S (x[n][w].st) s) s ⇢ e :=
    ⟨_, returns_map_intro_cone _ _ _ (returns_map_intro_cone _ _ _ htm)⟩
  obtain ⟨sc, hsc⟩ : ∃ sc : Block V → ℕ, ∀ C,
      M.goldfish_score S.E (Restated.confStoreAt M S (x[n][w].st) s).T e e s C ⇢ sc C :=
    ⟨fun C => Classical.choose (facts.fc.goldfish_score_nonempty S.E _ e e s C),
      fun C => Classical.choose_spec (facts.fc.goldfish_score_nonempty S.E _ e e s C)⟩
  obtain ⟨W, hW⟩ := facts.fc.ghost_nonempty A
    (Restated.Vocabulary.Protocol.confTree M (Restated.confStoreAt M S (x[n][w].st) s)) sc
    (fun C => decide (Restated.Vocabulary.Protocol.confCount M S.E
      (Restated.confStoreAt M S (x[n][w].st) s) s < 2 * sc C))
  have hlc := live_confirmed_after_confirmation_tick_cases facts S Sched x hn
    (Finset.mem_sdiff.2 ⟨haw, hwh _ (le_refl _)⟩) hneTickConf hrun c hc A hA e he sc hsc W hW
  have hhop := Restated.confirmed_hop_upTo facts S Sched x hexec hsync htd hmono hcs hs hanchor
    hgst hm hmr hmrc hawT (hwh _ (by rw [hct]; linarith)) hheads (M.gradeContract c) hvalid A hA
    hAB hpath hneTickVote hneTick e he sc hsc W hW
  rcases hlc with hl | hl
  · exact Or.inl (by rw [hl]; exact hhop)
  · exact Or.inr hl

end

end DecoupledConsensusModel.Sts.Restated
