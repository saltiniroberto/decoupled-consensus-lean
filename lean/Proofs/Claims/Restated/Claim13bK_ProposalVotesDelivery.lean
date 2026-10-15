import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.ReceiptOutcome
import Proofs.Claims.Restated.Claim13b
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bK_ConeCover
import Proofs.Claims.Restated.Claim13bK_ConeHeads
import Proofs.Claims.Restated.Claim13bK_CrossTransport
import Proofs.Claims.Restated.Claim13bK_GradeOldHeads
import Proofs.Claims.Restated.Claim13bK_ProposalVotesPivot
import Proofs.Claims.Restated.Claim13bK_ProposalVotesScores
import Proofs.Claims.Restated.Claim13bK_WindowProposalSent
import Proofs.Claims.Restated.Claim13bRelay
import Proofs.Claims.Restated.Claim13bStepCone
import Proofs.Claims.Restated.Claim13bStepKitConfirm
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bStepKitRecord
import Proofs.Claims.Restated.Claim13bStepKitRelay
import Proofs.Claims.Restated.Claim13beRoute3_3
import Proofs.Claims.Restated.Claim13beRoute3_4
import Proofs.Claims.Restated.Claim13beRoute3_5
import Proofs.Claims.Restated.Claim13beRoute3_6
import Proofs.Claims.Restated.ProcessIdempotent
import Proofs.Claims.Restated.ProcessedFlip
import Proofs.Claims.Restated.Projection
import Proofs.Claims.Restated.RunAll
import Proofs.Claims.Restated.VocabularyAssumptionsLemmas
import Proofs.Claims.Restated.Vocabulary_Protocol_Duties_Proposals_Actions
import Proofs.Claims.Restated.Vocabulary_Protocol_ValidatorClient_BlockEmission
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActiveJoint
import Model.Conditions.Claim13bInvariantActiveSinceW
import Model.Conditions.Claim13bK_ProposalVotesDelivery
import Model.Conditions.Claim13bK_ProposalVotesPivot
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13bStepAssembly
import Model.Conditions.Claim13bStepCone
import Model.Conditions.Claim13bStepConeIter
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_5
import Model.Conditions.Claim13beRoute3_74
import Model.Conditions.Claim13beRoute3_83
import Model.Conditions.CommonViewOfFinalizedDescendantsFacts
import Model.Conditions.ProcessedFlip
import Model.Conditions.RunAll
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13bd
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Sts_Spec2Claims_Claim13bf
import Model.Conditions.Sts_VocabularyAssumptions
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Healing_Action
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bK_ProposalVotesDelivery
import Proofs.Claims.Restated.Claim13bK_ProposalVotesDeliveryRule

/-!
# Delivery of votes and blocks to a proposal

The previous slot's honest votes and their heads reach the store a proposer reads at its proposal
instant, with the delivery and pool facts this uses, stated over a model `M : Record.Model V` and
its facts `facts : Record.Facts M`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

local macro "pCW% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13bK_ConfirmedWake)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "pSC% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13bStepCone)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If slot `s` is at or after the opening slot of a round `r ≥ 1`, its proposer is not held by the
    adversary up to `s`'s vote instant, is awake at `s`'s proposal instant and sends a block `B'` at
    its tick there, then the proposer was awake at every time from two delays before the proposal
    instant to it: the tick that sent the block passed the grade-1 awake test. -/
theorem proposer_window_before_proposal (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {r : Round} (hr : 1 ≤ r) {s : Slot}
    (hslot : M.opening_slot S.hc r ≤ s)
    (hprop : HonestThroughTime Sched (M.vote_time S.E s) (S.E.proposer s))
    (hawp : S.E.proposer s ∈ Sched.awake (M.proposal_time S.E s))
    {k : Nat} (hk : Restated.tickStepAt M x k (M.proposal_time S.E s)) {B' : NamedBlock V}
    (hemit : ∃ out : M.N × List (NamedObject V), M.tick (Setup.alwaysAwake S) (S.E.proposer s)
        (Record.wakeStage M Sched (M.proposal_time S.E s) x[k] (S.E.proposer s))
        (M.proposal_time S.E s) ⇢ out ∧ NamedObject.block B' ∈ out.2) :
    S.E.proposer s ∈ Sched.awakeThroughout (M.proposal_time S.E s - 2 * S.E.Δ)
      (M.proposal_time S.E s) := by
  obtain ⟨τ, hl, hτ⟩ := hk
  obtain ⟨out, hout, hB⟩ := hemit
  have hpv := (facts.sch.proposal_time_lt_vote_time S.E s).le
  exact Restated.awakeThroughout_before_proposal_rule facts S Sched x hl hτ
    (fun t ht => hprop t (le_trans ht (by rw [hτ]; exact hpv))) (by rw [hτ]; exact hawp)
    (Restated.early_g1_sub_delta_nonneg_cone facts S
      (Restated.one_le_round_of_of_opening_slot_le facts S hr hslot))
    (by rw [hτ]; exact hout) hB

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The opening slot of round `r` is `r * R`. -/
private theorem opening_slot_closed_pvd (facts : Record.Facts M) (hc : Protocol.HealConfig)
    (r : Round) : M.opening_slot hc r = r * hc.R := by
  have h := facts.gr.opening_slot_add_mk hc 0 r
  rw [Nat.zero_add, facts.gr.opening_slot_zero_mk, Nat.zero_add] at h
  exact h

/-- The confirmation instant of slot `s` is `4 * Δ * s + 6 * Δ`. -/
private theorem confirmation_time_closed_pvd (facts : Record.Facts M) (E : Env V) (s : Slot) :
    M.confirmation_time E s = 4 * E.Δ * (s : Int) + 6 * E.Δ := by
  rw [← facts.sch.slotStart_add_six_delta_eq_confirmation_time E s, slotStart_closed]

/-- The action instant of round `r` is `4 * Δ * R * r + 6 * Δ`. -/
private theorem action_closed_pvd (facts : Record.Facts M) (S : Setup V) (r : Round) :
    (Restated.Vocabulary.Execution.Setup.a M S r) =
      4 * S.E.Δ * (S.hc.R : Int) * (r : Int) + 6 * S.E.Δ := by
  show M.a S.hc S.E.Δ r = _
  rw [facts.sch.a_eq_confirmation_time S.hc S.E r, confirmation_time_closed_pvd facts,
    opening_slot_closed_pvd facts]
  push_cast
  ring

/-- The opening instant of round `r` is `4 * Δ` times round `r`'s opening slot. -/
private theorem opening_closed_pvd (facts : Record.Facts M) (S : Setup V) (r : Round) :
    M.opening S.E S.hc r = 4 * S.E.Δ * (((M.opening_slot S.hc r) : Nat) : Int) := by
  rw [facts.gr.opening_eq_proposal_time S.E S.hc r, Restated.proposal_time_closed_g1 facts S]

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If `t_GST ≤ a₀`, `w` is awake at every instant of `[a₀, a₀ + 2Δ]`, and an honest validator sent
    `sm` at step `k` at an instant before `a₀ + Δ`, then some step after `k`, at an instant at or
    after the send's and strictly before `a₀ + 2Δ`, delivers `sm` to `w`. -/
theorem delivered_of_awakeThroughout_ofCatchUp (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (hsync : Restated.SynchronyFromWake M S x)
    (hcatch : Restated.CatchUpOnWake M S x) {a₀ : Int} (hgst : S.E.t_GST ≤ a₀) {w : V}
    (hwaw : w ∈ Sched.awakeThroughout a₀ (a₀ + 2 * S.E.Δ))
    {k : Nat} {sm : SignedMsg V (NamedObject V)} (hsend : Restated.HonestSendAt M S x k sm)
    (hbefore : (x[k].time : Int) < a₀ + S.E.Δ) :
    ∃ d : Nat, k < d ∧ x.lbl d = AtomicAction.deliver w sm ∧
      (x[k].time : Int) ≤ (x[d].time : Int) ∧ (x[d].time : Int) < a₀ + 2 * S.E.Δ := by
  classical
  have hΔ : (0 : Int) < (S.E.Δ : Int) := S.E.Δ_pos
  have hawake : ∀ t : Int, a₀ ≤ t → t ≤ a₀ + 2 * S.E.Δ → w ∈ Sched.awake t :=
    fun t h0 h1 => mem_awake_of_awakeThroughout Sched hwaw h0 h1
  obtain ⟨T, hTdef⟩ : ∃ T : Int, T = (x[k + 1].time : Int) := ⟨_, rfl⟩
  have hT : (x[k].time : Int) ≤ T ∧ T ≤ (x[k].time : Int) + 1 := by
    rcases atomic_time_stepwise x k with h | h <;> omega
  obtain ⟨N, hN⟩ : ∃ N : Nat, N = (a₀ - T).toNat := ⟨_, rfl⟩
  by_cases hex : ∃ j : Nat, j ≤ N ∧ w ∉ Sched.awake (T + j)
  · -- Case 2: the latest instant of `[T, a₀]` at which `w` is asleep
    let P : Nat → Prop := fun j => w ∉ Sched.awake (T + j)
    obtain ⟨j₀, hj₀N, hj₀⟩ := hex
    obtain ⟨m, hm⟩ : ∃ m : Nat, m = Nat.findGreatest P N := ⟨_, rfl⟩
    have hmN : m ≤ N := hm ▸ Nat.findGreatest_le N
    have hPm : P m := hm ▸ Nat.findGreatest_spec hj₀N hj₀
    have hmax : ∀ j : Nat, m < j → j ≤ N → w ∈ Sched.awake (T + j) := by
      intro j hj hjN
      have := Nat.findGreatest_is_greatest (hm ▸ hj) hjN
      simpa [P] using this
    have hslt : T + m < a₀ := by
      by_contra hcon
      exact hPm (hawake (T + m) (by omega) (by omega))
    have hmN' : m + 1 ≤ N := by omega
    have hwake : w ∈ Sched.awake (T + ((m + 1 : Nat) : Int)) := hmax (m + 1) (by omega) hmN'
    have hasleep : w ∉ Sched.awake (T + ((m + 1 : Nat) : Int) - 1) := by
      have he : T + ((m + 1 : Nat) : Int) - 1 = T + (m : Int) := by push_cast; ring
      rw [he]; exact hPm
    have hwin : w ∈ Sched.awakeThroughout (T + ((m + 1 : Nat) : Int))
        (max (T + ((m + 1 : Nat) : Int)) S.E.t_GST + S.E.Δ) := by
      refine mem_awakeThroughout_of_forall Sched (fun t h0 h1 => ?_)
      have hmx : max (T + ((m + 1 : Nat) : Int)) S.E.t_GST ≤ a₀ :=
        max_le (by omega) hgst
      by_cases ht : t ≤ a₀
      · have hj : T + (((t - T).toNat : Nat) : Int) = t := by omega
        rw [← hj]
        exact hmax _ (by omega) (by omega)
      · exact hawake t (by omega) (by omega)
    have htk : (x[k].time : Int) < T + ((m + 1 : Nat) : Int) := by omega
    obtain ⟨d, hkd, hl, hlo, hhi⟩ := hcatch k w sm _ hsend htk hwake hasleep hwin
    have hmx : max (T + ((m + 1 : Nat) : Int)) S.E.t_GST ≤ a₀ := max_le (by omega) hgst
    exact ⟨d, hkd, hl, by omega, by omega⟩
  · -- Case 1: `w` is awake at every instant of `[T, a₀]`
    have hmx : max (x[k].time : Int) S.E.t_GST < a₀ + S.E.Δ :=
      max_lt hbefore (lt_of_le_of_lt hgst (by omega))
    have hwin : w ∈ Sched.awakeThroughout T (max (x[k].time : Int) S.E.t_GST + S.E.Δ) := by
      refine mem_awakeThroughout_of_forall Sched (fun t h0 h1 => ?_)
      by_cases ht : t ≤ a₀
      · have hj : T + (((t - T).toNat : Nat) : Int) = t := by omega
        rw [← hj]
        by_contra hna
        exact hex ⟨(t - T).toNat, by omega, hna⟩
      · exact hawake t (by omega) (by omega)
    rw [hTdef] at hwin
    obtain ⟨d, hkd, hl, hlo, hhi⟩ := hsync k w sm hsend hwin
    exact ⟨d, hkd, hl, hlo, by omega⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If step `k` is the sts tick at `t` and step `d` delivers a message at an instant strictly before
    `t`, then `d < k`. -/
theorem deliver_lt_tick_g2 (facts : Record.Facts M) {S : Setup V} {Sched : Schedule V} (x : AtomicExec (Record.protocolOf M S) Sched)
    {k d : Nat} {t : Int} (hk : Restated.tickStepAt M x k t) {w : V} {sm : SignedMsg V (NamedObject V)}
    (hl : x.lbl d = AtomicAction.deliver w sm) (hdt : (x[d].time : Int) < t) : d < k := by
  obtain ⟨hk1, -⟩ := Restated.tickStepAt_time facts x hk
  rcases lt_trichotomy d k with h | h | h
  · exact h
  · exfalso
    obtain ⟨t', hl', -⟩ := hk
    rw [h, hl'] at hl
    cases hl
  · exfalso
    have hle : (x[k + 1].time : Int) ≤ (x[d].time : Int) :=
      Restated.time_mono_int facts S Sched x (Nat.succ_le_of_lt h)
    linarith

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If `s ≥ 2`, `t_GST` is at or before two delays before slot `s`'s proposal instant, `v` is awake
    from then to that instant and honest through it, and `v'` is in `HonSlot S Sched (s − 1)`, then
    every vote `v'` casts at slot `s − 1` is in `v`'s slot-`(s − 1)` pool at the tick step of slot
    `s`'s proposal instant. -/
theorem prevVote_in_pool_at_proposal (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hsync : Restated.SynchronyFromWake M S x) (hcatch : Restated.CatchUpOnWake M S x)
    (hmult : AwakeAtMultiples S Sched) (htd : Restated.TimeDiverges M x) (hmono : Sched.MonotoneCorruption)
    {s : Slot} (hs : 2 ≤ s)
    (hgst : S.E.t_GST ≤ M.proposal_time S.E s - 2 * S.E.Δ)
    {v : V}
    (hvaw : v ∈ Sched.awakeThroughout (M.proposal_time S.E s - 2 * S.E.Δ)
      (M.proposal_time S.E s))
    (hvh : HonestThroughTime Sched (M.proposal_time S.E s) v)
    {k : Nat} (hk : Restated.tickStepAt M x k (M.proposal_time S.E s))
    {m : Nat} (hm : Restated.tickStepAt M x m (M.vote_time S.E (s - 1)))
    {v' : V} (hv' : v' ∈ Restated.HonSlot M S Sched (s - 1)) :
    ∀ u, Restated.gfVoteFrom M S (x[m][v'].st) v' (s - 1) ⇢ u →
      u ∈ (M.store_pool (x[k][v].st).st.core (s - 1)) := by
  have _hr_0 : M.reachedNode (x[k][v].st) := Record.reachedNode_sts facts S Sched x k v
  have _hr_1 : M.reachedNode (Record.wakeStage M Sched (M.vote_time S.E (s - 1)) x[m] v') := Record.reachedNode_wakeStage facts S Sched x m v' (M.vote_time S.E (s - 1))
  intro u hu_out
  have hd := S.E.Δ_pos
  have hd1 : (1 : Int) ≤ S.E.Δ := by
    simpa only [zero_add] using Int.add_one_le_iff.mpr S.E.Δ_pos
  have hs1 : ((s - 1 : Nat) : Int) = (s : Int) - 1 := nat_sub_one_cast_g2 (le_trans (by decide) hs)
  have hts := Restated.proposal_time_closed_g1 facts S s
  have hvt := Restated.vote_time_closed_g1 facts S (s - 1)
  have hct := confirmation_time_closed_pvd facts S.E (s - 1)
  rw [hs1] at hvt hct
  obtain ⟨hm1, hm0⟩ := Restated.tickStepAt_time facts x hm
  obtain ⟨hk1, hk0⟩ := Restated.tickStepAt_time facts x hk
  have huslot : u.slot = s - 1 := Restated.gfVoteFrom_slot facts S _ v' (s - 1) u hu_out
  have huidx : u.val_index = v' := Restated.gfVoteFrom_val_index facts S _ v' (s - 1) u hu_out
  have hcomm : v' ∈ S.E.committee (s - 1) := ((Restated.mem_HonSlot facts).mp hv').2.1
  have hqaw : v' ∈ Sched.awake (M.vote_time S.E (s - 1)) :=
    Restated.awake_of_mem_HonSlot facts S Sched (s - 1) hv'
  have hqadv : v' ∉ Sched.adv (M.vote_time S.E (s - 1)) := fun hin =>
    ((Restated.mem_HonSlot facts).mp hv').2.2 (hmono _ _ (Restated.vote_time_le_confirmation_time_g1 facts S (s - 1)) hin)
  have hqm : Restated.HonestThrough M Sched x m v' :=
    Restated.honestThrough_of_mem_HonSlot facts S Sched x hmono hv' (by rw [hct]; linarith)
  have hneTickm := Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew
    hmono hm (facts.sch.vote_time_emod_delta S (s - 1)) (Finset.mem_sdiff.2 ⟨hqaw, hqadv⟩)
  have hrun1 : M.awake_for_grade1 (Setup.alwaysAwake S) v'
      (Record.wakeStage M Sched (M.vote_time S.E (s - 1)) x[m] v') (M.round_of S.hc (s - 1)) :=
    (pSC% grade1_at_vote_tick_cone) facts S Sched x hm ((Restated.mem_HonSlot facts).mp hv').1
      (fun t' ht' hin => ((Restated.mem_HonSlot facts).mp hv').2.2
        (hmono _ _ (ht'.trans (Restated.vote_time_le_confirmation_time_g1 facts S (s - 1))) hin))
  have hsent : (⟨v', NamedObject.gfVote u⟩ : SignedMsg V (NamedObject V))
      ∈ x[m + 1].sent - x[m].sent := by
    obtain ⟨t', hlbl_m, ht'⟩ := id hm
    refine Restated.mem_sent_diff_of_tick facts S Sched x hlbl_m
      (by rw [ht']; exact Finset.mem_sdiff.2 ⟨hqaw, hqadv⟩)
      ?_ (by rw [ht']; exact hneTickm)
    rw [ht']
    have _hr_g := Record.reachedNode_wakeStage facts S Sched x m v' (M.vote_time S.E (s - 1))
    have _hv_g := Record.runs_as_wakeStage facts S Sched x m v' (M.vote_time S.E (s - 1))
    exact fun out hout => Restated.namedTick_emits_gfVote facts S v' _ (s - 1)
      (nat_pos_sub_one_g2 hs) hcomm hrun1 out hout u
      (by rw [Restated.gfVoteFrom_wakeStage facts]; exact hu_out)
  have hsend : Restated.HonestSendAt M S x m (⟨v', NamedObject.gfVote u⟩ : SignedMsg V (NamedObject V)) :=
    And.intro hsent (hqm _ (le_refl _))
  have hvaw' : v ∈ Sched.awakeThroughout (M.proposal_time S.E s - 2 * S.E.Δ)
      (M.proposal_time S.E s - 2 * S.E.Δ + 2 * S.E.Δ) := by
    have e : M.proposal_time S.E s - 2 * S.E.Δ + 2 * S.E.Δ
        = M.proposal_time S.E s := by ring
    rw [e]; exact hvaw
  obtain ⟨d, hmd, hlbl, hlo, hhi⟩ :=
    Restated.delivered_of_awakeThroughout_ofCatchUp facts S Sched x hsync hcatch hgst hvaw' hsend
      (by linarith)
  have hhi' : (x[d].time : Int) < M.proposal_time S.E s := by linarith
  have hdk : d < k := Restated.deliver_lt_tick_g2 facts x hk hlbl hhi'
  have hvd : Restated.HonestThrough M Sched x d v := fun t ht => hvh t (by linarith)
  have hqd : Restated.HonestThrough M Sched x d v' :=
    Restated.honestThrough_of_mem_HonSlot facts S Sched x hmono hv' (by rw [hct]; linarith)
  have hstart : slotStart S.E.Δ (s - 1) ≤ (x[d].time : Int) := by
    rw [slotStart_closed, hs1]; linarith
  have hge : s - 1 ≤ (x[d][v].st).st.core.s :=
    Restated.slot_ge_of_awake_of_slotStart facts S Sched x hmult htd hstart (Restated.sent_of_deliver facts S Sched x hlbl).2
      hvd (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›)
  have hle : (x[d][v].st).st.core.s < s := by
    rw [Restated.slotOfClock_sts facts S Sched x d v]
    refine Nat.lt_of_le_of_lt (slotOf_mono_sts S (Restated.clock_le_time_sts facts S Sched x d v)) ?_
    refine slotOf_lt_of_lt_slotStart S (Int.natCast_nonneg _) ?_
    rw [slotStart_closed]; rw [hts] at hhi'; exact hhi'
  have hwin : ¬ (u.slot < (x[d][v].st).st.core.s - 1 ∨ (x[d][v].st).st.core.s < u.slot) := by
    rw [huslot]; exact nat_window_g2 hge hle
  have hcommu : u.val_index ∈ S.E.committee u.slot := by rw [huidx, huslot]; exact hcomm
  have hfin : u ∈ (M.store_pool (x[k][v].st).st.core u.slot) := by
    rcases Restated.gfVote_recorded_of_deliver facts S Sched x hlbl hwin hcommu
        (facts.nd.process_nonempty _ _ _ (fun _ h => by cases h)) with h0 | heq | ⟨h1, -⟩
    · exact Restated.mem_pool_mono_sts facts S Sched x v (le_of_lt hdk) h0
    · exfalso
      rw [huidx, huslot, Restated.no_equiv_of_honest facts S Sched x hexec hqd (s - 1)] at heq
      exact Bool.false_ne_true heq
    · exact Restated.mem_pool_mono_sts facts S Sched x v hdk h1
  rw [huslot] at hfin
  exact hfin

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If an honest validator sends the named block `B` at step `k`, at or after GST and `tGAT'`, `t`
    is at least a delay after the send and at or before `tR`, step `mr` is the sts tick at `t`, and
    the reader `v` is awake throughout `[x[k].time, x[k].time + Δ]` and not held at step `mr`'s
    instant, then `B`'s erasure is in `v`'s tree after `mr` steps, stamped strictly before `t`. -/
theorem block_in_tree_of_honestSend_window_atTick (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hsync : Restated.SynchronyFromWake M S x) (hmult : AwakeAtMultiples S Sched) (htd : Restated.TimeDiverges M x)
    (hmono : Sched.MonotoneCorruption) {tGAT' tR : Int}
    {C : Block V} (hunder : Restated.DeliveredDescendantUnderFinalizedInPhase M S x tGAT' tR C)
    {k mr n : Nat} {v_0 v v' : V} {B : NamedBlock V} {t : Int}
    (hsend : Restated.HonestSendAt M S x k (⟨v_0, NamedObject.block B⟩ : SignedMsg V (NamedObject V)))
    (hgst : S.E.t_GST ≤ (x[k].time : Int)) (hklo : tGAT' ≤ (x[k].time : Int))
    (hmem : B.erase ∈ (x[n][v'].st).st.core.T) (hgen : B ≠ NamedBlock.genesis)
    (hCB : Block.Preceq C B.erase)
    (hnk : (x[n].time : Int) ≤ (x[k + 1].time : Int))
    (hdl : (x[k].time : Int) + S.E.Δ ≤ t)
    (hΓR : t ≤ tR) (hmr : Restated.tickStepAt M x mr t)
    (hw : v ∉ Sched.adv (x[mr].time : Int))
    (hwin : v ∈ Sched.awakeThroughout (x[k].time : Int) ((x[k].time : Int) + S.E.Δ)) :
    B.erase ∈ (x[mr][v].st).st.core.T ∧
      ∃ σ : Stamp, (x[mr][v].st).st.core.timestamp_block B.erase = some σ ∧
        σ < (t : Stamp) := by
  have hd := S.E.Δ_pos
  have hmax : max (x[k].time : Int) S.E.t_GST = (x[k].time : Int) := max_eq_left hgst
  obtain ⟨d, hkd, hdlt, hdlbl⟩ := Restated.deliver_of_honestSendAt facts S Sched x hsync
    (D := t) hsend (by rw [hmax]; exact hdl) (by rw [hmax]; exact hwin)
  have hkd1 : k + 1 ≤ d := hkd
  have hk1d : (x[k + 1].time : Int) ≤ (x[d].time : Int) := Restated.time_mono_int facts S Sched x hkd1
  have hkd' : (x[k].time : Int) ≤ (x[d].time : Int) :=
    le_trans (Restated.time_mono_int facts S Sched x (Nat.le_succ k)) hk1d
  have hdmr : d < mr := Restated.deliver_lt_tick_g2 facts x hmr hdlbl hdlt
  have hdmr' : (x[d].time : Int) ≤ (x[mr].time : Int) := Restated.time_mono_int facts S Sched x (le_of_lt hdmr)
  have hwh : Restated.HonestThrough M Sched x d v := by
    intro t' ht' hin
    exact hw (hmono t' _ (le_trans ht' hdmr') hin)
  have hbody : B ∈ (x[d + 1][v].st).st.bodies :=
    Restated.block_admitted_of_deliver_afterPhase facts S Sched x hexec hmult htd hunder hdlbl hwh hmem hgen
      hCB (le_trans hnk hk1d) (le_trans hklo hkd') (le_trans (le_of_lt hdlt) hΓR)
      (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›)
  have hdtime : (x[d + 1].time : Int) = (x[d].time : Int) := by
    exact_mod_cast congrArg (fun m : Nat => (m : Int)) (Restated.deliver_time facts S Sched x hdlbl)
  have hbodymr : B ∈ (x[mr][v].st).st.bodies :=
    of_decide_eq_true (Restated.processed_mono facts S Sched x v (NamedObject.block B) hdmr
      (decide_eq_true hbody))
  refine ⟨?_, ?_⟩
  · rw [Restated.bodies_image_eq_T facts S Sched x mr v]
    exact Finset.mem_image_of_mem NamedBlock.erase hbodymr
  · have hmemTd : B.erase ∈ (x[d + 1][v].st).st.core.T := by
      rw [Restated.bodies_image_eq_T facts S Sched x (d + 1) v]
      exact Finset.mem_image_of_mem NamedBlock.erase hbody
    obtain ⟨σ, hσ, hσlt⟩ :=
      Restated.block_stamp_lt_of_time facts S Sched x (d + 1) v hmemTd (by rw [hdtime]; exact hdlt)
    exact ⟨σ, Restated.block_stamp_carry facts S Sched x hdmr v hσ, hσlt⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- After GST, if an honest validator sent the named block `B` at step `k`, `t` is at least a delay
    after the send and at or before `tR`, step `mr` is the sts tick at `t`, and the reader `v` is
    awake throughout `[t − 2Δ, t]` and not held at step `mr`'s instant, then `B`'s erasure is in
    `v`'s tree after `mr` steps, stamped strictly before `t`. -/
theorem block_in_tree_of_honestSend_atTick (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hsync : Restated.SynchronyFromWake M S x) (hmult : AwakeAtMultiples S Sched) (htd : Restated.TimeDiverges M x)
    (hmono : Sched.MonotoneCorruption) {tR : Int} {t : Int}
    {C : Block V} (hunder : Restated.DeliveredDescendantUnderFinalizedInPhase M S x (t - 2 * S.E.Δ) tR C)
    {k mr n : Nat} {v_0 v v' : V} {B : NamedBlock V}
    (hsend : Restated.HonestSendAt M S x k (⟨v_0, NamedObject.block B⟩ : SignedMsg V (NamedObject V)))
    (hgst : S.E.t_GST ≤ (x[k].time : Int))
    (hcover : ∀ t' : Int, (x[k].time : Int) ≤ t' → HonestAwakeCover S Sched t')
    (hmem : B.erase ∈ (x[n][v'].st).st.core.T) (hgen : B ≠ NamedBlock.genesis)
    (hCB : Block.Preceq C B.erase)
    (hnk : (x[n].time : Int) ≤ (x[k + 1].time : Int))
    (hdl : (x[k].time : Int) + S.E.Δ ≤ t)
    (hΓR : t ≤ tR) (hmr : Restated.tickStepAt M x mr t)
    (hw : v ∉ Sched.adv (x[mr].time : Int))
    (hwaw : v ∈ Sched.awakeThroughout (t - 2 * S.E.Δ) t) :
    B.erase ∈ (x[mr][v].st).st.core.T ∧
      ∃ σ : Stamp, (x[mr][v].st).st.core.timestamp_block B.erase = some σ ∧
        σ < (t : Stamp) := by
  have hd := S.E.Δ_pos
  by_cases hcase : t - 2 * S.E.Δ ≤ (x[k].time : Int)
  · exact Restated.block_in_tree_of_honestSend_window_atTick facts S Sched x hexec hsync hmult htd hmono hunder
      hsend hgst hcase hmem hgen hCB hnk hdl hΓR hmr hw
      (awakeThroughout_mono Sched hwaw hcase hdl)
  · have hlt : (x[k].time : Int) < t - 2 * S.E.Δ := not_le.mp hcase
    obtain ⟨k', v'', hs', h1, h2⟩ :=
      Restated.honestSend_recurs facts S Sched x hsync htd hsend hgst hcover
        (fun _ _ _ hl =>
          Restated.receipt_outcome_of_deliver_mono facts S Sched x hexec.idealization hmono hl)
        (t - 2 * S.E.Δ) (le_of_lt hlt)
    have hkk : k < k' := by
      by_contra hcon
      have hle : k' ≤ k := not_lt.mp hcon
      have := Restated.time_mono_int facts S Sched x hle
      linarith
    have hk1 : (x[k + 1].time : Int) ≤ (x[k' + 1].time : Int) :=
      Restated.time_mono_int facts S Sched x (Nat.succ_le_succ (le_of_lt hkk))
    have hkt : (x[k].time : Int) ≤ (x[k'].time : Int) := Restated.time_mono_int facts S Sched x (le_of_lt hkk)
    exact Restated.block_in_tree_of_honestSend_window_atTick facts S Sched x hexec hsync hmult htd hmono hunder
      hs' (le_trans hgst hkt) h1 hmem hgen hCB (le_trans hnk hk1)
      (by linarith) hΓR hmr hw (awakeThroughout_mono Sched hwaw h1 (by linarith))

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If an honest validator holds the named block `B` at step `m`, at an instant at or after `tGAT`,
    `t` is more than a delay after that instant and at or before `tR`, step `mr` is the sts tick at
    `t`, and the reader `v` is awake throughout `[t − 2Δ, t]` and not held at step `mr`'s instant,
    then `B`'s erasure is in `v`'s tree after `mr` steps, stamped strictly before `t`. -/
theorem block_in_tree_of_holder_atTick (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hsync : Restated.SynchronyFromWake M S x)
    (hmult : AwakeAtMultiples S Sched) (htd : Restated.TimeDiverges M x)
    (hmono : Sched.MonotoneCorruption) {tGAT tE tR : Int}
    (hgst : S.E.t_GST ≤ tGAT)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcs : Restated.committeeSleepinessW M S Sched tE) (hlen : tGAT + S.E.Δ ≤ tE) {t : Int}
    {C : Block V} (hunder : Restated.DeliveredDescendantUnderFinalizedInPhase M S x (t - 2 * S.E.Δ) tR C)
    (hunderS : Restated.FinalizedPreceqAtStepsInPhase M S x (t - 2 * S.E.Δ) tR C)
    {m mr : Nat} {v' v : V} {B : NamedBlock V}
    (hB : B ∈ (x[m][v'].st).st.bodies)
    (hq : Restated.HonestThrough M Sched x m v')
    (hCB : Block.Preceq C B.erase)
    (hlo : tGAT ≤ (x[m].time : Int))
    (hdeadline : (x[m].time : Int) + S.E.Δ < t)
    (hgap : tGAT + S.E.Δ + 1 < t)
    (hΓR : t ≤ tR) (hmr : Restated.tickStepAt M x mr t)
    (hw : v ∉ Sched.adv (x[mr].time : Int))
    (hwaw : v ∈ Sched.awakeThroughout (t - 2 * S.E.Δ) t) :
    B.erase ∈ (x[mr][v].st).st.core.T ∧
      ∃ σ : Stamp, (x[mr][v].st).st.core.timestamp_block B.erase = some σ ∧
        σ < (t : Stamp) := by
  classical
  have hd := S.E.Δ_pos
  obtain ⟨hmr1, hmr0⟩ := Restated.tickStepAt_time facts x hmr
  have hcov : ∀ t' : Int, tGAT ≤ t' → HonestAwakeCover S Sched t' := fun t' ht' =>
    Restated.honestAwakeCover_of_premises facts S Sched hmono hgst hthird hawake hcs ht'
  have hFst : ∀ d : Nat, (x[d].time : Int) = tGAT + S.E.Δ → Restated.HonestThrough M Sched x d v →
      Block.compatible (x[d][v].st).st.core.F B.erase = true ∨ B ∈ (x[d][v].st).st.bodies := by
    intro d hdt' _
    have hdmr : d ≤ mr := by
      by_contra hcon
      have hle : mr ≤ d := by omega
      have := Restated.time_mono_int facts S Sched x hle
      linarith
    have hvmr : Restated.HonestThrough M Sched x mr v := fun t' ht hin => hw (hmono t' _ ht hin)
    have h : Block.Preceq (x[d][v].st).st.core.F B.erase :=
      preceq_trans_Preceq (preceq_trans_Preceq (Restated.F_mono facts S Sched x v hdmr)
        (hunderS mr v hvmr (by linarith) (by linarith))) hCB
    exact Or.inl (compatible_of_cases (Or.inl h))
  have hviaCV : ∀ (n : Nat), B ∈ (x[n][v'].st).st.bodies → (x[n].time : Int) ≤ tGAT →
      HonestThroughTime Sched tGAT v' →
      B.erase ∈ (x[mr][v].st).st.core.T ∧
        ∃ σ : Stamp, (x[mr][v].st).st.core.timestamp_block B.erase = some σ ∧
          σ < (t : Stamp) := by
    intro n hBn hn hqT
    obtain ⟨hT, σ, hσ, hσlt⟩ := Restated.block_in_tree_of_narrowedCommonView_afterPhase facts S Sched x hexec
      htd hmono hcv
      hawake hlen (t := t - 1) hBn hqT hn (by linarith) (by linarith) hw hFst
    refine ⟨hT, σ, hσ, lt_trans hσlt ?_⟩
    exact WithBot.coe_lt_coe.mpr (by linarith)
  by_cases hgen : B = NamedBlock.genesis
  · subst hgen
    have hgb : (NamedBlock.genesis : NamedBlock V) ∈ (x[mr][v].st).st.bodies :=
      ((Restated.nodeInvariant_sts facts S Sched x mr v).1.1.1.2.2.1).1
    have hT : (NamedBlock.genesis : NamedBlock V).erase ∈ (x[mr][v].st).st.core.T := by
      rw [Restated.bodies_image_eq_T facts S Sched x mr v]
      exact Finset.mem_image_of_mem NamedBlock.erase hgb
    exact ⟨hT, Restated.block_stamp_lt_of_time facts S Sched x mr v hT (by linarith)⟩
  have h0 : Restated.Vocabulary.Execution.Object.processed M (x[0][v'].st).st
      (NamedObject.block B) = false := by
    rw [Record.st_zero M S Sched x v']
    simp only [Restated.Vocabulary.Execution.Object.processed, facts.nd.initial_st,
      facts.hd.initial_bodies, Finset.mem_singleton]
    exact decide_eq_false hgen
  obtain ⟨i, him, hf0, hf1⟩ :=
    Restated.exists_flip_of_processed facts S Sched x v' (NamedObject.block B) h0
      (decide_eq_true hB)
  have hbodyi : B ∈ (x[i + 1][v'].st).st.bodies := of_decide_eq_true hf1
  have hmemi : B.erase ∈ (x[i + 1][v'].st).st.core.T := by
    rw [Restated.bodies_image_eq_T facts S Sched x (i + 1) v']
    exact Finset.mem_image_of_mem NamedBlock.erase hbodyi
  have hqT : HonestThroughTime Sched tGAT v' := fun t' ht => hq t' (le_trans ht hlo)
  have himt : (x[i].time : Int) ≤ (x[m].time : Int) := Restated.time_mono_int facts S Sched x (le_of_lt him)
  have hqi : Restated.HonestThrough M Sched x i v' := fun t' ht => hq t' (le_trans ht himt)
  rcases Restated.flip_step_cases facts S Sched x hf0 hf1 with
    ⟨sm, hlbl, -, -, hpay⟩ | ⟨τ, hlbl, haw, out₁, hout₁, hst₁, hem⟩
  · -- `B` was delivered to the holder at step `i`
    rcases hpay with hmsg | ⟨Bl, -, hcc⟩
    · obtain ⟨u, o⟩ := sm
      have hmsg' : o = NamedObject.block B := hmsg
      subst hmsg'
      have hdt : (x[i + 1].time : Int) = (x[i].time : Int) := by
        exact_mod_cast congrArg (fun j : Nat => (j : Int)) (Restated.deliver_time facts S Sched x hlbl)
      by_cases hearly : (x[i].time : Int) ≤ tGAT
      · exact hviaCV (i + 1) hbodyi (by rw [hdt]; exact hearly) hqT
      · have hlate : tGAT ≤ (x[i].time : Int) := le_of_lt (not_le.mp hearly)
        obtain ⟨k, hkt, hsend⟩ := Restated.block_onWire_of_deliver_phase facts S Sched x hlbl hqi
          (Restated.sent_of_deliver facts S Sched x hlbl).2
          (Restated.receipt_outcome_of_flip facts S Sched x hlbl hf0 hf1)
        have hnk : (x[i + 1].time : Int) ≤ (x[k + 1].time : Int) := by
          rw [hdt, ← hkt]
          exact Restated.time_mono_int facts S Sched x (Nat.le_succ k)
        have hklo : tGAT ≤ (x[k].time : Int) := by rw [hkt]; exact hlate
        exact Restated.block_in_tree_of_honestSend_atTick facts S Sched x hexec hsync hmult htd hmono
          hunder hsend (le_trans hgst hklo) (fun t' ht' => hcov t' (le_trans hklo ht'))
          hmemi hgen hCB hnk (by rw [hkt]; linarith) hΓR hmr hw hwaw
    · exact hcc.elim
  · -- the holder's own tick at step `i` emitted `B`
    rcases hem with hemit | ⟨Bl, -, hcc⟩
    · obtain ⟨hτ, hτ'⟩ := Restated.tickAllAwake_time facts S Sched x hlbl
      have hdt : (x[i + 1].time : Int) = (x[i].time : Int) + 1 := by
        have h1 : (x[i].time : Int) + 1 = (τ : Int) := by exact_mod_cast hτ
        have h2 : (x[i + 1].time : Int) = (τ : Int) := by exact_mod_cast hτ'
        linarith
      by_cases hearly : (x[i].time : Int) < tGAT
      · exact hviaCV (i + 1) hbodyi (by rw [hdt]; linarith) hqT
      · have hlate : tGAT ≤ (x[i].time : Int) := not_lt.mp hearly
        have hsend := Restated.block_honestSend_at_tick facts S Sched x hqi hlbl haw
          ⟨out₁, hout₁, hst₁, hemit⟩
        exact Restated.block_in_tree_of_honestSend_atTick facts S Sched x hexec hsync hmult htd hmono
          hunder hsend (le_trans hgst hlate) (fun t' ht' => hcov t' (le_trans hlate ht'))
          hmemi hgen hCB (le_refl _) (by linarith) hΓR hmr hw hwaw
    · exact hcc.elim

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- The store slot `s`'s proposal duty reads has, for every slot `s'`, the pool of the node's own
    store. -/
theorem proposalStoreAt_pool (facts : Record.Facts M) (S : Setup V) (before : M.N) (s s' : Slot) :
    (M.store_pool (Restated.proposalStoreAt M S before s) s') = (M.store_pool before.st.core s') := by
  rw [Restated.proposalStoreAt, facts.hd.Sts_setClock_core_pool]

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- The store slot `s`'s proposal duty reads has the block tree of the node's own store. -/
theorem proposalStoreAt_T (facts : Record.Facts M) (S : Setup V) (before : M.N) (s : Slot) :
    (Restated.proposalStoreAt M S before s).T = before.st.core.T := by
  rw [Restated.proposalStoreAt, facts.hd.Sts_setClock_core_T]

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- The store slot `s`'s proposal duty reads has the block stamps of the node's own store. -/
theorem proposalStoreAt_timestamp_block (facts : Record.Facts M) (S : Setup V) (before : M.N) (s : Slot) :
    (Restated.proposalStoreAt M S before s).timestamp_block = before.st.core.timestamp_block := by
  rw [Restated.proposalStoreAt, facts.hd.setClock_core_timestamp_block]

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If step `n_W` is the sts tick at `t_W ≤ lo`, and every validator honest through a step from
    `n_W` on with instant at or before `hi` holds a finalized block that is an ancestor of `C`, then
    at every delivery of a descendant of `C` to an honest validator at an instant of `[lo, hi]`, the
    receiver's finalized block is an ancestor of the delivered block. -/
theorem deliveredUnderFinalized_of_finBound (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {n_W : Nat} {t_W lo hi : Int}
    (hnW : Restated.tickStepAt M x n_W t_W) (hlo : t_W ≤ lo) {C : Block V}
    (hF : ∀ (v : V) (n₁ : Nat), n_W ≤ n₁ → (x[n₁].time : Int) ≤ hi →
      Restated.HonestThrough M Sched x n₁ v → Block.Preceq (x[n₁][v].st).st.core.F C) :
    Restated.DeliveredDescendantUnderFinalizedInPhase M S x lo hi C := by
  intro d v v' B _ hvh hdlo hdhi hCB
  have hWd : n_W ≤ d := by
    by_contra hcon
    have hle : d ≤ n_W := by omega
    have h1 := Restated.time_mono_int facts S Sched x hle
    have h2 := (Restated.tickStepAt_time facts x hnW).2
    linarith
  exact preceq_eq_true_iff_Preceq.mpr (preceq_trans_Preceq (hF v d hWd hdhi hvh) hCB)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If step `n_W` is the sts tick at `t_W ≤ lo`, and every validator honest through a step from
    `n_W` on with instant at or before `hi` holds a finalized block that is an ancestor of `C`, then
    `FinalizedPreceqAtStepsInPhase` holds on `[lo, hi]`. -/
theorem finalizedPreceqAtSteps_of_finBound (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {n_W : Nat} {t_W lo hi : Int}
    (hnW : Restated.tickStepAt M x n_W t_W) (hlo : t_W ≤ lo) {C : Block V}
    (hF : ∀ (v : V) (n₁ : Nat), n_W ≤ n₁ → (x[n₁].time : Int) ≤ hi →
      Restated.HonestThrough M Sched x n₁ v → Block.Preceq (x[n₁][v].st).st.core.F C) :
    Restated.FinalizedPreceqAtStepsInPhase M S x lo hi C := by
  intro d v hvh hdlo hdhi
  have hWd : n_W ≤ d := by
    by_contra hcon
    have hle : d ≤ n_W := by omega
    have h1 := Restated.time_mono_int facts S Sched x hle
    have h2 := (Restated.tickStepAt_time facts x hnW).2
    linarith
  exact hF v d hWd hdhi hvh

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- For a slot `s` at or after the opening slot of the round after the switch round, `tGAT + 12Δ`
    and the switch round's action instant plus `4Δ` are at or before slot `s`'s proposal instant. -/
theorem tGAT_le_proposal_time_g2 (facts : Record.Facts M) (S : Setup V) (tGAT tE : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) {s : Slot}
    (hslot : (M.opening_slot S.hc (Restated.switchRound M S tE + 1)) ≤ s) :
    tGAT + 12 * S.E.Δ ≤ M.proposal_time S.E s ∧
      (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)) + 4 * S.E.Δ ≤ M.proposal_time S.E s := by
  have hd := S.E.Δ_pos
  have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
  have h1 := Restated.tGAT_le_switchOpening facts S tGAT tE gap hgst hlen
  have h2 := Restated.opening_le_proposal_time_g1 facts S hslot
  have h3 := opening_closed_pvd facts S (Restated.switchRound M S tE + 1)
  have h4 := opening_closed_pvd facts S (Restated.switchRound M S tE)
  have h5 : Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)
      = M.opening S.E S.hc (Restated.switchRound M S tE) + 6 * S.E.Δ := by
    rw [action_closed_pvd facts S, h4, opening_slot_closed_pvd facts]
    push_cast
    ring
  have h6 : Restated.switchOpening M S tE = M.opening S.E S.hc (Restated.switchRound M S tE) := rfl
  rw [opening_slot_closed_pvd facts] at h3 h4
  push_cast at h3 h4
  have hstep : M.opening S.E S.hc (Restated.switchRound M S tE + 1)
      = M.opening S.E S.hc (Restated.switchRound M S tE) + 4 * S.E.Δ * (S.hc.R : Int) := by
    rw [h3, h4]; ring
  have hRΔ : 12 * S.E.Δ ≤ 4 * S.E.Δ * (S.hc.R : Int) := by nlinarith
  constructor <;> linarith

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Under the joint invariant at the switch round, for a slot `s` at or after the opening slot of
    the round after the switch round and a validator `v` awake at `s`'s proposal instant and honest
    through it, every vote a member of `HonSlot S Sched (s − 1)` casts at slot `s − 1` is in the
    slot-`(s − 1)` pool of the store `v`'s proposal read holds, and that vote's head is in that
    store's tree, found by `Block.find?` at its root, of a slot at most `s − 1` and stamped strictly
    before `s`'s proposal instant. -/
theorem prevVotes_at_proposalStore (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (hcatch : Restated.CatchUpOnWake M S x)
    (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (hsync : Restated.SynchronyFromWake M S x) (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight) (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t) (hrsW : Restated.roundSleepinessW M S Sched tE) (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT) (hcs : Restated.committeeSleepinessW M S Sched tE) (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched)) (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap) (hprev : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
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
    {s : Slot} (hslot : (M.opening_slot S.hc (Restated.switchRound M S tE + 1)) ≤ s)
    {v : V} (haw : v ∈ Sched.awake (M.proposal_time S.E s))
    (hvh : HonestThroughTime Sched (M.proposal_time S.E s) v)
    {k : Nat} (hk : Restated.tickStepAt M x k (M.proposal_time S.E s))
    (hwinv : v ∈ Sched.awakeThroughout (M.proposal_time S.E s - 2 * S.E.Δ) (M.proposal_time S.E s))
    {m : Nat} (hm : Restated.tickStepAt M x m (M.vote_time S.E (s - 1)))
    {v' : V} (hv' : v' ∈ Restated.HonSlot M S Sched (s - 1)) :
    ∀ u, Restated.gfVoteFrom M S (x[m][v'].st) v' (s - 1) ⇢ u →
    ∀ H, Restated.gfHeadFrom M S (x[m][v'].st) (s - 1) ⇢ H →
      u ∈ (M.store_pool (Restated.proposalStoreAt M S (x[k][v].st) s) (s - 1)) ∧
      Block.find? (Restated.proposalStoreAt M S (x[k][v].st) s).T H.root = some H ∧
      H.slot ≤ s - 1 ∧
      ∃ σ : Stamp, (Restated.proposalStoreAt M S (x[k][v].st) s).timestamp_block H = some σ ∧
        σ < ((M.proposal_time S.E s : Int) : Stamp) := by
  intro u hu_out H hH_out
  have hd := S.E.Δ_pos
  have hd1 : (1 : Int) ≤ S.E.Δ := by
    simpa only [zero_add] using Int.add_one_le_iff.mpr S.E.Δ_pos
  have hR3 := S.hc.R_ge_three
  obtain ⟨hGt, hAt⟩ := Restated.tGAT_le_proposal_time_g2 facts S tGAT tE gap hgst hlen hslot
  have hs2 : 2 ≤ s := by
    have h := opening_slot_closed_pvd facts S.hc (Restated.switchRound M S tE + 1)
    have hle : S.hc.R ≤ (Restated.switchRound M S tE + 1) * S.hc.R :=
      Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
    rw [h] at hslot
    exact le_trans (le_trans (by decide) hR3) (le_trans hle hslot)
  have hts := Restated.proposal_time_closed_g1 facts S s
  have hs1 : ((s - 1 : Nat) : Int) = (s : Int) - 1 :=
    nat_sub_one_cast_g2 (le_trans (by decide) hs2)
  have hvt := Restated.vote_time_closed_g1 facts S (s - 1)
  have hct := confirmation_time_closed_pvd facts S.E (s - 1)
  rw [hs1] at hvt hct
  obtain ⟨hm1, hm0⟩ := Restated.tickStepAt_time facts x hm
  obtain ⟨hk1, hk0⟩ := Restated.tickStepAt_time facts x hk
  have hvaw := hwinv
  have hpool := Restated.prevVote_in_pool_at_proposal facts S Sched x hexec hsync hcatch hmult htd hmono hs2
    (by linarith) hvaw hvh hk hm hv' u hu_out
  rw [← Restated.proposalStoreAt_pool facts S (x[k][v].st) s (s - 1)] at hpool
  obtain ⟨T, -, hH, -, hFJ⟩ := Restated.exists_anchor_atSlot facts S Sched x tE hexec hmono htd hcatch tGAT gap
    hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hrec hprev hclear hB' hnW hAW
    hJswitch hTW₀ hJ₀ hslot
  have hunder : Restated.DeliveredDescendantUnderFinalizedInPhase M S x
      (M.proposal_time S.E s - 2 * S.E.Δ) (M.proposal_time S.E s) T.erase :=
    Restated.deliveredUnderFinalized_of_finBound facts S Sched x hnW (by linarith)
      (fun v₁ n₁ hW h1 hh => (hFJ v₁ n₁ hW (le_trans h1 (Restated.proposal_time_le_vote_time_g1 facts S s))
        hh).1)
  have hunderS : Restated.FinalizedPreceqAtStepsInPhase M S x
      (M.proposal_time S.E s - 2 * S.E.Δ) (M.proposal_time S.E s) T.erase :=
    Restated.finalizedPreceqAtSteps_of_finBound facts S Sched x hnW (by linarith)
      (fun v₁ n₁ hW h1 hh => (hFJ v₁ n₁ hW (le_trans h1 (Restated.proposal_time_le_vote_time_g1 facts S s))
        hh).1)
  obtain ⟨D, hD, hDe⟩ :=
    Restated.exists_named_of_mem_tree facts S Sched x m v'
      (Restated.gfHeadFrom_mem_tree facts S Sched x m v' (s - 1) H hH_out)
  have hTD : Block.Preceq T.erase D.erase := by rw [hDe]; exact hH v' m hv' hm H hH_out
  have hqm : Restated.HonestThrough M Sched x m v' :=
    Restated.honestThrough_of_mem_HonSlot facts S Sched x hmono hv' (by rw [hct]; linarith)
  have hvk : Restated.HonestThrough M Sched x k v := fun t ht => hvh t (by linarith)
  obtain ⟨hmemT, σ, hσ, hσlt⟩ :=
    Restated.block_in_tree_of_holder_atTick facts S Sched x hexec hsync hmult htd hmono hgst hcv hphase hthird
      hcs (Restated.delta_le_of_healingLengthη facts S hlen) hunder hunderS hD hqm hTD (by linarith) (by linarith)
      (by linarith) le_rfl hk (hvk _ le_rfl) hvaw
  rw [hDe] at hmemT hσ
  refine ⟨hpool, ?_, Restated.headSlot_le_of_tickStepAt facts S Sched x hm v' H hH_out, σ, ?_, hσlt⟩
  · rw [Restated.proposalStoreAt_T facts]
    exact Restated.find_of_mem_tree_honest facts S Sched x hexec hvk hmemT
  · rw [Restated.proposalStoreAt_timestamp_block facts]
    exact hσ

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If `w` holds `u` in its pool after `m` steps with a stamp strictly before the multiple `c` of
    `Δ`, step `n` is the sts tick at `c`, `w` is awake and not held at `c`, and `w`'s tick at step
    `n` has an outcome, then `u` entered `w`'s pool at a step `i` with `i < m` and `i + 1 ≤ n`,
    `u`'s slot starts at or before `w`'s clock after that step, and `u`'s signer is in the committee
    of `u`'s slot. -/
theorem gfVote_entered_before_cut (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    {m n : Nat} {c : Int} {w : V} {u : GoldfishVote V}
    (hu : u ∈ (M.store_pool (x[m][w].st).st.core u.slot)) {τ : Stamp}
    (hτ : (x[m][w].st).st.core.timestamp_vote u = some τ) (hτc : τ < (c : Stamp))
    (hn : Restated.tickStepAt M x n c) (haw : w ∈ Sched.awake c \ Sched.adv c) (hdvd : c % S.E.Δ = 0)
    (hne : ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) w (Record.wakeStage M Sched c x[n] w) c ⇢ out) :
    ∃ i : Nat, i < m ∧ i + 1 ≤ n ∧ u ∉ (M.store_pool (x[i][w].st).st.core u.slot) ∧
      u ∈ (M.store_pool (x[i + 1][w].st).st.core u.slot) ∧
      slotStart S.E.Δ u.slot ≤ (x[i + 1][w].st).st.core.t ∧
      u.val_index ∈ S.E.committee u.slot := by
  obtain ⟨i, him, -, h0, h1⟩ := Restated.accepts_of_mem_pool facts S Sched x hu
  obtain ⟨hst1, hfloor, hcomm⟩ := Restated.stamp_eq_clock_of_flip_gfVote facts S Sched x h0 h1
  have hcarry := Restated.stamp_mono_sts facts S Sched x w (Nat.succ_le_of_lt him) hst1
  rw [hτ] at hcarry
  have hlt : (x[i + 1][w].st).st.core.t < c := by
    have h := Option.some.inj hcarry
    rw [h] at hτc
    exact WithBot.coe_lt_coe.mp hτc
  refine ⟨i, him, ?_, h0, h1, hfloor, hcomm⟩
  by_contra hcon
  have hni : n < i + 1 := by omega
  exact absurd (Restated.clock_ge_of_tick_lt facts S Sched x hn haw hdvd hne hni)
    (not_le.mpr hlt)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If `u` enters `w`'s pool at step `i`, the configuration after `i + 1` steps is strictly before
    the multiple `c` of `Δ`, GST is at or before `x[i].time`, and some validator is awake for the
    delay from `x[i].time` on and not held at its end, then some validator honestly sends `u` at a
    step `k ≥ i`, at an instant strictly before `c`. -/
theorem gfVote_honestSend_of_entry (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hsync : Restated.SynchronyFromWake M S x)
    (hmono : Sched.MonotoneCorruption)
    -- every delivery has an outcome from the node state the receiver holds before it
    (hreceipt : ∀ (j : Nat) (w : V) (sm : SignedMsg V (NamedObject V)),
      x.lbl j = AtomicAction.deliver w sm →
      ∃ n' : M.N, M.process (Setup.alwaysAwake S) (x[j][w].st) sm.msg ⇢ n')
    {i : Nat} {w : V} {u : GoldfishVote V}
    (h0 : u ∉ (M.store_pool (x[i][w].st).st.core u.slot))
    (h1 : u ∈ (M.store_pool (x[i + 1][w].st).st.core u.slot)) {c : Int}
    (hlt : (x[i + 1].time : Int) < c) (hcdvd : c % S.E.Δ = 0)
    (hgst : S.E.t_GST ≤ (x[i].time : Int))
    (hcover : HonestAwakeCover S Sched (x[i].time : Int)) :
    ∃ k : Nat, ∃ w' : V,
      Restated.HonestSendAt M S x k (⟨w', NamedObject.gfVote u⟩ : SignedMsg V (NamedObject V)) ∧
      i ≤ k ∧ (x[k].time : Int) < c := by
  have hd := S.E.Δ_pos
  have hf0 : Restated.Vocabulary.Execution.Object.processed M (x[i][w].st).st
      (NamedObject.gfVote u) = false :=
    decide_eq_false (fun h => h0 ((facts.sto.mem_store_pool_iff _ _ _).2 h))
  have hf1 : Restated.Vocabulary.Execution.Object.processed M (x[i + 1][w].st).st
      (NamedObject.gfVote u) = true :=
    decide_eq_true ((facts.sto.mem_store_pool_iff _ _ _).1 h1)
  have hii1 : (x[i].time : Int) ≤ (x[i + 1].time : Int) := Restated.time_mono_int facts S Sched x (Nat.le_succ i)
  rcases Restated.flip_step_cases facts S Sched x hf0 hf1 with
    ⟨sm, hlbl, -, -, hpay⟩ | ⟨τ, hlbl, haw, out₁, hout₁, hst₁, hem⟩
  · -- a delivery to `w`: its re-send
    refine ⟨i, w, Restated.honestSendAt_of_deliver_relay facts S Sched x hlbl ?_
      (Restated.receipt_outcome_of_flip facts S Sched x hlbl hf0 hf1), le_refl _, lt_of_le_of_lt hii1 hlt⟩
    rw [mem_relayedObjects_iff]
    rcases hpay with hmsg | ⟨Bl, hmsg, hcc⟩
    · exact Or.inl hmsg.symm
    · rw [hmsg]
      exact Or.inr (Restated.carries_of_carriedCall facts (Setup.alwaysAwake S) _ Bl hcc)
  · obtain ⟨hτ, hτ'⟩ := Restated.tickAllAwake_time facts S Sched x hlbl
    have hτi : (x[i].time : Int) + 1 = (τ : Int) := by exact_mod_cast hτ
    have hτi' : (x[i + 1].time : Int) = (τ : Int) := by exact_mod_cast hτ'
    have hwadv : w ∉ Sched.adv (x[i].time : Int) := fun hin =>
      (Finset.mem_sdiff.1 haw).2 (hmono _ _ (by omega) hin)
    rcases hem with hemit | ⟨Bl, hmem, hcc⟩
    · -- `w`'s own tick emitted the vote
      exact ⟨i, w, ⟨Restated.mem_sent_diff_of_tick_of_state facts S Sched x hlbl haw
          (facts.nd.tick_send_eq_of_state (Setup.alwaysAwake S) w _ (τ : Int))
          hout₁ hst₁ hemit, hwadv⟩, le_refl _,
        lt_of_le_of_lt hii1 hlt⟩
    · -- `w`'s own tick emitted a block that includes the vote, which the cover validator re-sends
      have hsendB : Restated.HonestSendAt M S x i
          (⟨w, NamedObject.block Bl⟩ : SignedMsg V (NamedObject V)) :=
        ⟨Restated.mem_sent_diff_of_tick_of_state facts S Sched x hlbl haw
          (facts.nd.tick_send_eq_of_state (Setup.alwaysAwake S) w _ (τ : Int))
          hout₁ hst₁ hmem, hwadv⟩
      obtain ⟨w', hw'aw, -⟩ := hcover
      have hmax : max (x[i].time : Int) S.E.t_GST = (x[i].time : Int) := max_eq_left hgst
      obtain ⟨d, hid', hdlt, hdlbl⟩ := Restated.deliver_of_honestSendAt facts S Sched x hsync
        (D := (x[i].time : Int) + S.E.Δ) hsendB (by rw [hmax]) (by rw [hmax]; exact hw'aw)
      have hrel : NamedObject.gfVote u ∈ relayedObjects (NamedObject.block Bl) := by
        rw [mem_relayedObjects_iff]
        exact Or.inr (Restated.carries_of_carriedCall facts (Setup.alwaysAwake S) _ Bl hcc)
      -- `w`'s tick sent the block `Bl`, so `τ` is a proposal instant, a multiple of `S.E.Δ`
      have hdvd : (τ : Int) % S.E.Δ = 0 := by
        have _hr : M.reachedNode (Record.wakeStage M Sched (τ : Int) x[i] w) :=
          Record.reachedNode_wakeStage facts S Sched x i w τ
        have _hv : M.runs_as (Record.wakeStage M Sched (τ : Int) x[i] w) w :=
          Record.runs_as_wakeStage facts S Sched x i w τ
        rw [(facts.nd.block_mem_on_tick_emit (Setup.alwaysAwake S) w _ _ out₁ hout₁ hmem).1.2.1]
        exact facts.sch.proposal_time_emod_delta_inclX S.E _
      have hτc : (τ : Int) + S.E.Δ ≤ c := by
        have hτlt : (τ : Int) < c := by rw [← hτi']; exact hlt
        obtain ⟨q₁, hq₁⟩ : ∃ q₁, (τ : Int) = S.E.Δ * q₁ :=
          ⟨(τ : Int) / S.E.Δ, (Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero hdvd)).symm⟩
        obtain ⟨q₂, hq₂⟩ : ∃ q₂, c = S.E.Δ * q₂ :=
          ⟨c / S.E.Δ, (Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero hcdvd)).symm⟩
        rw [hq₁, hq₂] at hτlt ⊢
        have hq : q₁ < q₂ := lt_of_mul_lt_mul_left hτlt (le_of_lt hd)
        nlinarith
      exact ⟨d, w', Restated.honestSendAt_of_deliver_relay facts S Sched x hdlbl hrel
        (hreceipt _ _ _ hdlbl), le_of_lt hid', by linarith⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- The votes `w` pools for slot `s` after `k` steps are among those it pools after `m` steps, for
    `k ≤ m`. -/
theorem pool_subset_of_le_g2 (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (w : V) {k m : Nat} (hkm : k ≤ m) (s : Slot) :
    (M.store_pool (x[k][w].st).st.core s) ⊆ (M.store_pool (x[m][w].st).st.core s) := by
  intro y hy
  have hys : y.slot = s := Restated.slot_of_mem_pool_sts facts S Sched x k w hy
  rw [← hys] at hy ⊢
  exact Restated.mem_pool_mono_sts facts S Sched x w hkm hy

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If step `d` delivers a message to `w`, `w` is honest through `d`, and `d`'s instant is at or
    after slot `s − 1`'s start and strictly before slot `s`'s, then `w`'s store slot after `d` steps
    is `s − 1`. -/
theorem storeSlot_at_delivery_g2 (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hmult : AwakeAtMultiples S Sched) (htd : Restated.TimeDiverges M x)
    {d : Nat} {w : V} {sm : SignedMsg V (NamedObject V)}
    (hl : x.lbl d = AtomicAction.deliver w sm) (hwh : Restated.HonestThrough M Sched x d w) {s : Slot}
    (hlo : slotStart S.E.Δ (s - 1) ≤ (x[d].time : Int))
    (hhi : (x[d].time : Int) < slotStart S.E.Δ s)
    (hnr : ∀ (k τ : Nat) (u : V), x.lbl k = AtomicAction.tickAllAwake τ →
      (τ : Int) % S.E.Δ = 0 → u ∈ Sched.awake (τ : Int) \ Sched.adv (τ : Int) →
      (∀ t' ≤ (τ : Int), u ∉ Sched.adv t') →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) u (Record.wakeStage M Sched (τ : Int) x[k] u) (τ : Int) ⇢ out) :
    s - 1 ≤ (x[d][w].st).st.core.s ∧ (x[d][w].st).st.core.s < s := by
  refine ⟨Restated.slot_ge_of_awake_of_slotStart facts S Sched x hmult htd hlo (Restated.sent_of_deliver facts S Sched x hl).2
    hwh (fun n' t' hn' hΔ hq _ hhi' => by
      obtain ⟨τ, hl, rfl⟩ := hn'
      exact hnr n' τ w hl hΔ hq (fun t ht => hwh t (le_trans ht hhi'))), ?_⟩
  rw [Restated.slotOfClock_sts facts S Sched x d w]
  refine Nat.lt_of_le_of_lt (slotOf_mono_sts S (Restated.clock_le_time_sts facts S Sched x d w)) ?_
  exact slotOf_lt_of_lt_slotStart S (Int.natCast_nonneg _) hhi

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If `v` is awake throughout two delays before slot `s`'s proposal instant and honest through it,
    and `v'`, awake and not held one delay before that instant, holds `u` in its slot-`(s − 1)` pool
    with a stamp strictly before that instant, then at the tick of slot `s`'s proposal instant `u`
    is in `v`'s slot-`(s − 1)` pool or `u`'s signer equivocates in that pool. -/
theorem pooledVote_at_proposal (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hsync : Restated.SynchronyFromWake M S x) (hcatch : Restated.CatchUpOnWake M S x)
    (hmult : AwakeAtMultiples S Sched) (htd : Restated.TimeDiverges M x) (hmono : Sched.MonotoneCorruption)
    -- every delivery has an outcome from the node state the receiver holds before it
    (hreceipt : ∀ (j : Nat) (w : V) (sm : SignedMsg V (NamedObject V)),
      x.lbl j = AtomicAction.deliver w sm →
      ∃ n' : M.N, M.process (Setup.alwaysAwake S) (x[j][w].st) sm.msg ⇢ n')
    {s : Slot} (hs : 1 ≤ s)
    (hgst : S.E.t_GST ≤ slotStart S.E.Δ (s - 1) - 1)
    (hcover : ∀ t : Int, slotStart S.E.Δ (s - 1) - 1 ≤ t → HonestAwakeCover S Sched t)
    {v : V}
    (hvaw : v ∈ Sched.awakeThroughout (M.proposal_time S.E s - 2 * S.E.Δ)
      (M.proposal_time S.E s))
    (hvh : HonestThroughTime Sched (M.proposal_time S.E s) v)
    {k : Nat} (hk : Restated.tickStepAt M x k (M.proposal_time S.E s))
    {nc : Nat} (hnc : Restated.tickStepAt M x nc (M.proposal_time S.E s - S.E.Δ))
    {v' : V} (hv'c : v' ∈ Sched.awake (M.proposal_time S.E s - S.E.Δ) \
      Sched.adv (M.proposal_time S.E s - S.E.Δ))
    {m : Nat} {u : GoldfishVote V} (hu : u ∈ (M.store_pool (x[m][v'].st).st.core (s - 1))) {τ : Stamp}
    (hτ : (x[m][v'].st).st.core.timestamp_vote u = some τ)
    (hτc : τ < ((M.proposal_time S.E s - S.E.Δ : Int) : Stamp))
    (hnr : ∀ (k τ : Nat) (u : V), x.lbl k = AtomicAction.tickAllAwake τ →
      (τ : Int) % S.E.Δ = 0 → u ∈ Sched.awake (τ : Int) \ Sched.adv (τ : Int) →
      (∀ t' ≤ (τ : Int), u ∉ Sched.adv t') →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) u (Record.wakeStage M Sched (τ : Int) x[k] u) (τ : Int) ⇢ out) :
    u ∈ (M.store_pool (x[k][v].st).st.core (s - 1)) ∨
      M.equivocates ((M.store_pool (x[k][v].st).st.core (s - 1))) u.val_index = true := by
  have hd := S.E.Δ_pos
  have hts := Restated.proposal_time_closed_g1 facts S s
  have hs1 : ((s - 1 : Nat) : Int) = (s : Int) - 1 := nat_sub_one_cast_g2 hs
  have hss : slotStart S.E.Δ (s - 1) = M.proposal_time S.E s - 4 * S.E.Δ := by
    rw [slotStart_closed, hs1, hts]; ring
  have hss' : slotStart S.E.Δ s = M.proposal_time S.E s := by
    rw [slotStart_closed, hts]
  have hus : u.slot = s - 1 := Restated.slot_of_mem_pool_sts facts S Sched x m v' hu
  rw [← hus] at hu
  have hdvd : (M.proposal_time S.E s - S.E.Δ) % S.E.Δ = 0 := by
    have h : M.proposal_time S.E s - S.E.Δ = S.E.Δ * (4 * (s : Int) - 1) := by
      rw [hts]; ring
    rw [h]; exact Int.mul_emod_right _ _
  obtain ⟨i, -, hin, h0, h1, hfloor, hcomm⟩ :=
    Restated.gfVote_entered_before_cut facts S Sched x hu hτ hτc hnc hv'c hdvd
      (by
        obtain ⟨τc, hlc, hτc'⟩ := hnc
        rw [← hτc']
        exact hnr nc τc v' hlc (by rw [hτc']; exact hdvd) (by rw [hτc']; exact hv'c)
          (by rw [hτc']; exact Restated.honest_upTo_of_mono hmono hv'c))
  rw [hus] at hfloor
  obtain ⟨hnc1, hnc0⟩ := Restated.tickStepAt_time facts x hnc
  have hi1 : (x[i + 1].time : Int) ≤ (x[nc].time : Int) := Restated.time_mono_int facts S Sched x hin
  have hclk : (x[i + 1][v'].st).st.core.t ≤ (x[i + 1].time : Int) :=
    Restated.clock_le_time_sts facts S Sched x (i + 1) v'
  have hstep : (x[i + 1].time : Int) ≤ (x[i].time : Int) + 1 := by
    rcases atomic_time_stepwise x i with h | h <;> omega
  have hlo_i : slotStart S.E.Δ (s - 1) - 1 ≤ (x[i].time : Int) := by linarith
  obtain ⟨k', w', hsend, hik', hk'c⟩ :=
    Restated.gfVote_honestSend_of_entry facts S Sched x hsync hmono hreceipt h0 h1 (by linarith) hdvd
      (le_trans hgst hlo_i) (hcover _ hlo_i)
  have hvaw' : v ∈ Sched.awakeThroughout (M.proposal_time S.E s - 2 * S.E.Δ)
      (M.proposal_time S.E s - 2 * S.E.Δ + 2 * S.E.Δ) := by
    have e : M.proposal_time S.E s - 2 * S.E.Δ + 2 * S.E.Δ
        = M.proposal_time S.E s := by ring
    rw [e]; exact hvaw
  obtain ⟨d, hk'd, hlbl, -, hdhi⟩ :=
    Restated.delivered_of_awakeThroughout_ofCatchUp facts S Sched x hsync hcatch (by linarith) hvaw' hsend
      (by linarith)
  have hdhi' : (x[d].time : Int) < M.proposal_time S.E s := by linarith
  have hdk : d < k := Restated.deliver_lt_tick_g2 facts x hk hlbl hdhi'
  have hvd : Restated.HonestThrough M Sched x d v := fun t ht => hvh t (by linarith)
  have hk'1 : (x[i + 1].time : Int) ≤ (x[k' + 1].time : Int) :=
    Restated.time_mono_int facts S Sched x (Nat.succ_le_succ hik')
  have hk'd' : (x[k' + 1].time : Int) ≤ (x[d].time : Int) := Restated.time_mono_int facts S Sched x hk'd
  obtain ⟨hge, hlt⟩ := Restated.storeSlot_at_delivery_g2 facts S Sched x hmult htd hlbl hvd (s := s)
    (by linarith) (by rw [hss']; exact hdhi') hnr
  have hwin : ¬ (u.slot < (x[d][v].st).st.core.s - 1 ∨ (x[d][v].st).st.core.s < u.slot) := by
    rw [hus]; exact nat_window_g2 hge hlt
  rcases Restated.gfVote_recorded_of_deliver facts S Sched x hlbl hwin hcomm
      (facts.nd.process_nonempty _ _ _ (fun _ h => by cases h)) with hmem | heq | ⟨hrec, -⟩
  · left
    have h := Restated.mem_pool_mono_sts facts S Sched x v (le_of_lt hdk) hmem
    rw [hus] at h; exact h
  · right
    rw [hus] at heq
    exact facts.sch.equivocates_mono_of_subset (Restated.pool_subset_of_le_g2 facts S Sched x v (le_of_lt hdk) _) heq
  · left
    have h := Restated.mem_pool_mono_sts facts S Sched x v hdk hrec
    rw [hus] at h; exact h

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- A member of `HonSlot S Sched s` is awake at every instant from one delay before slot `s`'s
    proposal instant to its vote instant. -/
theorem honSlot_awake_around (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) {s : Slot} {v : V} (hvs : v ∈ Restated.HonSlot M S Sched s) :
    v ∈ Sched.awakeThroughout (M.proposal_time S.E s - S.E.Δ) (M.vote_time S.E s) := by
  have h := ((Restated.mem_HonSlot facts).mp hvs).1
  simp only [activeAtW, wVote] at h
  have hd := S.E.Δ_pos
  have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
  have hts := Restated.proposal_time_closed_g1 facts S s
  have hvt := Restated.vote_time_closed_g1 facts S s
  refine awakeThroughout_mono Sched h ?_ ?_
  · rw [hts, slotStart_closed]; nlinarith
  · rw [hvt, slotStart_closed]

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- `FinalizedBelowUpTo` at `C` gives it at every descendant of `C`. -/
theorem finalizedBelowUpTo_mono (facts : Record.Facts M) {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (Record.protocolOf M S) Sched} {n_W : Nat} {t : Int} {C C' : Block V}
    (h : Restated.FinalizedBelowUpTo M S Sched x n_W t C) (hCC' : Block.Preceq C C') :
    Restated.FinalizedBelowUpTo M S Sched x n_W t C' :=
  fun v n₁ hW h1 hh => preceq_trans_Preceq (h v n₁ hW h1 hh) hCC'

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If step `n_W` is the sts tick at `t_W ≤ lo` and `FinalizedBelowUpTo` holds at `C` from `n_W` up
    to `hi`, then at every delivery of a descendant of `C` to an honest validator at an instant of
    `[lo, hi]`, the receiver's finalized block is an ancestor of the delivered block. -/
theorem deliveredUnderFinalized_of_below (facts : Record.Facts M) {S : Setup V} {Sched : Schedule V}
    (x : AtomicExec (Record.protocolOf M S) Sched) {n_W : Nat} {t_W lo hi : Int}
    (hnW : Restated.tickStepAt M x n_W t_W) (hlo : t_W ≤ lo) {C : Block V}
    (hF : Restated.FinalizedBelowUpTo M S Sched x n_W hi C) :
    Restated.DeliveredDescendantUnderFinalizedInPhase M S x lo hi C :=
  Restated.deliveredUnderFinalized_of_finBound facts S Sched x hnW hlo hF

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If step `n_W` is the sts tick at `t_W ≤ lo` and `FinalizedBelowUpTo` holds at `C` from `n_W` up
    to `hi`, then at every step whose instant lies in `[lo, hi]` every honest validator holds a
    finalized block that is an ancestor of `C`. -/
theorem finalizedPreceqAtSteps_of_below (facts : Record.Facts M) {S : Setup V} {Sched : Schedule V}
    (x : AtomicExec (Record.protocolOf M S) Sched) {n_W : Nat} {t_W lo hi : Int}
    (hnW : Restated.tickStepAt M x n_W t_W) (hlo : t_W ≤ lo) {C : Block V}
    (hF : Restated.FinalizedBelowUpTo M S Sched x n_W hi C) :
    Restated.FinalizedPreceqAtStepsInPhase M S x lo hi C :=
  Restated.finalizedPreceqAtSteps_of_finBound facts S Sched x hnW hlo hF

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- The store slot `s`'s proposal duty reads stands at slot `s`. -/
theorem proposalStoreAt_s (facts : Record.Facts M) (S : Setup V) (before : M.N) (s : Slot) :
    (Restated.proposalStoreAt M S before s).s = s := by
  rw [Restated.proposalStoreAt, facts.hd.Sts_setClock_core_s]
  exact facts.sch.slotOf_proposal_time S.E s

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If `n` is a node state of the proposal read of slot `s` and the proposal duty, run by `v` on
    `n`, can return a pair whose block is `B`, then `B` is of slot `s`, carries the proposer's raw
    view as Goldfish votes and every outcome of its support view as support votes, has as parent
    every head the composed head computes there, held among the node's bodies before the tick, has
    proposer `v`, and its included rows pass the receiver's round test. -/
theorem proposalDuty_fields (facts : Record.Facts M) (S : Setup V) (before : M.N) (s : Slot) (v : V)
    {B : NamedBlock V}
    {n : M.N} (hn : Restated.proposalReadOf M S before s ⇢ n)
    {D : M.NS × Option (NamedBlock V)}
    (hD : M.duties_propose_block_with (M.gradeContract n.cache) S.E S.hc S.cfg
        ((Setup.alwaysAwake S).node v) (M.ns_setClock S.E before.st (M.proposal_time S.E s)) ⇢ D)
    (hduty : D.2 = some B) (hreach : M.reachedNode before := by trivial) :
    B.erase.slot = s ∧
      B.erase.gf_votes =
        M.proposer_view (M.toHealing (Restated.proposalStoreAt M S before s)).toFG.toSG.toGoldfishStore s ∧
      (∀ L : List (GoldfishVote V), M.proposer_support_view
        (M.toHealing (Restated.proposalStoreAt M S before s)).toFG.toSG.toGoldfishStore s ⇢ L →
        B.erase.gf_support_votes = L) ∧
      (∀ U : Finset (GoldfishVote V), Restated.proposerSupportOf M S before s ⇢ U →
        ∀ P : Block V, M.get_head_with (M.gradeContract n.cache) S.E S.hc
          (M.toHealing (Restated.proposalStoreAt M S before s))
          (Restated.proposerVotesOf M S before s) U (s - 1) ⇢ P →
        B.erase.parent = P) ∧
      B.parent ∈ before.st.bodies ∧
      B.erase.proposer? = some v ∧
      M.carried_attestations_admissible S.hc B.erase = true := by
  obtain ⟨c, hc, rfl⟩ := (pCW% returns_map_elim_cw) _ _ n hn
  rewrite [facts.nd.mkNode_cache] at hD
  rw [facts.nd.mkNode_cache]
  obtain ⟨o, ho⟩ := facts.dt.proposal_with_nonempty (M.gradeContract c) .poolAndCarried S.E S.hc
    ((Setup.alwaysAwake S).node v) (M.ns_setClock S.E before.st (M.proposal_time S.E s))
  have _hr_s0 := facts.sto.reachedStore_setClock S.E _ (M.proposal_time S.E s)
    (facts.nd.reachedStore_of_node _ hreach)
  have hpw := facts.dt.proposal_with_eq_of_propose_block_with_snd _ _ _ _ _ _ D hD hduty o ho
  obtain ⟨input, hinput⟩ := facts.dt.with_proposal_input_nonempty (M.gradeContract c) S.E S.hc
    ((Setup.alwaysAwake S).node v)
    (M.toHealing (M.ns_setClock S.E before.st (M.proposal_time S.E s)).core)
  obtain ⟨L0, hL0⟩ := facts.dt.select_nonempty .poolAndCarried S.hc
    (M.ns_setClock S.E before.st (M.proposal_time S.E s))
  obtain ⟨hpm, hpe, hsl, -, hgv, hgs, -, hpr⟩ :=
    facts.dt.proposal_payload _ .poolAndCarried S.E S.hc _ _ B o ho hpw input hinput L0 hL0
  have e : Restated.proposalStoreAt M S before s
      = (M.ns_setClock S.E before.st (M.proposal_time S.E s)).core := rfl
  have hs : (M.toHealing (M.ns_setClock S.E before.st (M.proposal_time S.E s)).core).toFG.toSG.toGoldfishStore.s
      = s := by
    rw [facts.sto.toHealing_slot, ← e]; exact Restated.proposalStoreAt_s facts S before s
  have hisl := facts.dt.with_proposal_input_id_slot _ _ _ _ _ input hinput
  have hipr := facts.dt.with_proposal_input_id_proposer _ _ _ _ _ input hinput
  have higv := facts.dt.with_proposal_input_id_gf_votes _ _ _ _ _ input hinput
  rw [hs] at hisl higv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_,
    facts.dt.proposal_with_carried_admissible_inclG2 _ _ _ _ _ o ho hpw⟩
  · rw [Proofs.NamedWire.erase_slot, hsl, hisl]
  · rw [Proofs.NamedWire.erase_goldfish_votes, hgv, higv, e]
  · intro L hL
    rw [Proofs.NamedWire.erase_goldfish_support, hgs]
    refine facts.dt.with_proposal_input_id_gf_support_votes _ _ _ _ _ input hinput L ?_
    rw [hs, ← e]; exact hL
  · intro U hU P hP
    obtain ⟨L, hL, rfl⟩ := (pCW% returns_map_elim_cw) _ _ U hU
    rw [Proofs.NamedWire.erase_parent, hpe]
    refine facts.dt.with_proposal_input_id_parent _ _ _ _ _ input hinput L
      (by rw [hs, ← e]; exact hL) P ?_
    rw [hs, ← e]; exact hP
  · rw [facts.hd.Sts_setClock_bodies] at hpm
    exact hpm
  · rw [Proofs.NamedWire.erase_proposer, hpr, hipr, (Setup.alwaysAwake S).node_val_index v]

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- In an sts execution with unforgeable signatures, if `s`'s proposer is honest through the instant
    of `x[i]` and `proposedBlockAtStep S x i s B` holds, then some step `k < i` is the tick at slot
    `s`'s proposal instant, and some outcome of the proposer's tick there sends a named block `B'`
    with erasure `B` that the proposal duty returns at every node state of the proposal read. -/
theorem sentProposal_duty (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hunf : Restated.Unforgeability M S x) {i : Nat} {s : Slot} {B : Block V}
    (hprop : HonestThroughTime Sched (x[i].time : Int) (S.E.proposer s))
    (hB : Restated.proposedBlockAtStep M S x i s B) :
    ∃ k < i, Restated.tickStepAt M x k (M.proposal_time S.E s) ∧ ∃ B' : NamedBlock V,
      B'.erase = B ∧
      (∃ out : M.N × List (NamedObject V), M.tick (Setup.alwaysAwake S) (S.E.proposer s)
        (Record.wakeStage M Sched (M.proposal_time S.E s) x[k] (S.E.proposer s))
        (M.proposal_time S.E s) ⇢ out ∧ NamedObject.block B' ∈ out.2) ∧
      ∀ n : M.N, Restated.proposalReadOf M S (x[k][S.E.proposer s].st) s ⇢ n →
      ∀ D : M.NS × Option (NamedBlock V),
        M.duties_propose_block_with (M.gradeContract n.cache) S.E S.hc S.cfg
          ((Setup.alwaysAwake S).node (S.E.proposer s)) (M.ns_setClock S.E (x[k][S.E.proposer s].st).st (M.proposal_time S.E s)) ⇢ D →
        D.2 = some B' := by
  obtain ⟨k, hki, B', hBe, -, hk, t, -, ht, out, hout, hmem⟩ :=
    Restated.signedProposal_tick_g1 facts S Sched x hunf hprop hB
  rw [ht] at hout
  refine ⟨k, hki, hk, B', hBe, ⟨out, hout, hmem⟩, ?_⟩
  intro n hn D hD
  obtain ⟨c, hc, rfl⟩ := (pCW% returns_map_elim_cw) _ _ n hn
  rewrite [facts.nd.mkNode_cache] at hD
  rw [facts.nd.gradeContract_eq_frameContract] at hD
  have _hr_s1 := Record.reachedNode_wakeStage facts S Sched x (k) (S.E.proposer s) (M.proposal_time S.E s)
  have _hv_s2 := Record.runs_as_wakeStage facts S Sched x (k) (S.E.proposer s) (M.proposal_time S.E s)
  exact (facts.nd.block_mem_on_tick_emit (Setup.alwaysAwake S) _ _ _ out hout hmem).2 c
    (by rw [Record.wakeStage_st facts, Record.wakeStage_cache facts]; exact hc) D
    (by rw [Record.wakeStage_st facts]; exact hD)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If `s`'s proposer is honest through `vote_time s` and awake at slot `s`'s proposal instant, its
    tick there sends the named block `B'` its proposal duty returns, `FinalizedBelowUpTo` holds at
    an ancestor `C` of `B'` up to `vote_time s`, and `v` is in `HonSlot S Sched s`, then `B'`'s
    erasure is in `v`'s tree at the tick step of `vote_time s`. -/
theorem proposal_in_voterTree (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hsync : Restated.SynchronyFromWake M S x) (hmult : AwakeAtMultiples S Sched) (htd : Restated.TimeDiverges M x)
    (hmono : Sched.MonotoneCorruption) {s : Slot}
    (hprop : HonestThroughTime Sched (M.vote_time S.E s) (S.E.proposer s))
    (hawp : S.E.proposer s ∈ Sched.awake (M.proposal_time S.E s))
    {k : Nat} (hk : Restated.tickStepAt M x k (M.proposal_time S.E s))
    (hgst : S.E.t_GST ≤ M.proposal_time S.E s - 1)
    {B' : NamedBlock V}
    (hemit : ∃ out : M.N × List (NamedObject V), M.tick (Setup.alwaysAwake S) (S.E.proposer s)
        (Record.wakeStage M Sched (M.proposal_time S.E s) x[k] (S.E.proposer s))
        (M.proposal_time S.E s) ⇢ out ∧ NamedObject.block B' ∈ out.2)
    {n : M.N} (hn : Restated.proposalReadOf M S (x[k][S.E.proposer s].st) s ⇢ n)
    {D : M.NS × Option (NamedBlock V)}
    (hD : M.duties_propose_block_with (M.gradeContract n.cache)
        S.E S.hc S.cfg ((Setup.alwaysAwake S).node (S.E.proposer s)) (M.ns_setClock S.E (x[k][S.E.proposer s].st).st (M.proposal_time S.E s)) ⇢ D)
    (hduty : D.2 = some B')
    {n_W : Nat} {t_W : Int} (hnW : Restated.tickStepAt M x n_W t_W)
    (htW : t_W ≤ M.proposal_time S.E s)
    {C : Block V} (hF : Restated.FinalizedBelowUpTo M S Sched x n_W (M.vote_time S.E s) C)
    (hCB : Block.Preceq C B'.erase)
    {v : V} (hv : v ∈ Restated.HonSlot M S Sched s)
    {mr : Nat} (hmr : Restated.tickStepAt M x mr (M.vote_time S.E s)) :
    B'.erase ∈ (x[mr][v].st).st.core.T := by
  have _hr_0 : M.reachedNode (x[k][S.E.proposer s].st) := Record.reachedNode_sts facts S Sched x k (S.E.proposer s)
  have _hv_0 : M.runs_as (x[k][S.E.proposer s].st) (S.E.proposer s) := Record.runs_as_sts facts S Sched x k (S.E.proposer s)
  have _hr_1 : M.reachedNode (x[mr][v].st) := Record.reachedNode_sts facts S Sched x mr v
  have _hv_1 : M.runs_as (x[mr][v].st) v := Record.runs_as_sts facts S Sched x mr v
  have _hr_2 : M.reachedNode (Record.wakeStage M Sched (M.proposal_time S.E s) x[k] (S.E.proposer s)) := Record.reachedNode_wakeStage facts S Sched x k (S.E.proposer s) (M.proposal_time S.E s)
  have _hv_2 : M.runs_as (Record.wakeStage M Sched (M.proposal_time S.E s) x[k] (S.E.proposer s)) (S.E.proposer s) := Record.runs_as_wakeStage facts S Sched x k (S.E.proposer s) (M.proposal_time S.E s)
  have hd := S.E.Δ_pos
  have hd1 : (1 : Int) ≤ S.E.Δ := by
    simpa only [zero_add] using Int.add_one_le_iff.mpr S.E.Δ_pos
  have hts := Restated.proposal_time_closed_g1 facts S s
  have hvt := Restated.vote_time_closed_g1 facts S s
  have hct := confirmation_time_closed_pvd facts S.E s
  obtain ⟨hk1, hk0⟩ := Restated.tickStepAt_time facts x hk
  have hfields := Restated.proposalDuty_fields facts S (x[k][S.E.proposer s].st) s
    (S.E.proposer s) hn hD hduty
  have hall : ∀ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) (S.E.proposer s)
        (Record.wakeStage M Sched (M.proposal_time S.E s) x[k] (S.E.proposer s))
        (M.proposal_time S.E s) ⇢ out → NamedObject.block B' ∈ out.2 := by
    obtain ⟨out₀, hout₀, hmem₀⟩ := hemit
    have hpos : 0 < s := by
      have h := (facts.nd.block_mem_on_tick_emit (Setup.alwaysAwake S) (S.E.proposer s)
        _ (M.proposal_time S.E s) out₀ hout₀ hmem₀).1.1
      rw [show (Setup.alwaysAwake S).E.slotOf (M.proposal_time S.E s) = s from
        facts.sch.slotOf_proposal_time S.E s] at h
      exact h
    obtain ⟨c, hc, rfl⟩ := (pCW% returns_map_elim_cw) _ _ n hn
    rewrite [facts.nd.mkNode_cache] at hD
    have hD'B := hduty
    have hrunP := facts.nd.block_mem_on_tick_emit_awake (Setup.alwaysAwake S) (S.E.proposer s) _
      (M.proposal_time S.E s) out₀ hout₀ hmem₀
    rw [show (Setup.alwaysAwake S).E.slotOf (M.proposal_time S.E s) = s from
      facts.sch.slotOf_proposal_time S.E s] at hrunP
    exact fun out hout => facts.nd.on_tick_emit_proposal_mem_of_outcomes (Setup.alwaysAwake S)
      (S.E.proposer s) _ s hpos
      ((Setup.alwaysAwake S).node_val_index (S.E.proposer s)).symm c
      (by rw [Record.wakeStage_st facts, Record.wakeStage_cache facts]; exact hc) D
      (by rw [Record.wakeStage_st facts]; exact hD) hD'B out hout hrunP
  obtain ⟨t', hl, ht'⟩ := id hk
  set p := S.E.proposer s with hp_def
  have hpv : M.proposal_time S.E s ≤ M.vote_time S.E s :=
    Restated.proposal_time_le_vote_time_g1 facts S s
  have hpk : Restated.HonestThrough M Sched x k p := fun t ht => hprop t (by linarith)
  have hawp' : p ∈ Sched.awake (t' : Int) \ Sched.adv (t' : Int) := by
    rw [ht']; exact Finset.mem_sdiff.2 ⟨hawp, hprop _ hpv⟩
  have hdvd : (t' : Int) % S.E.Δ = 0 := by
    rw [ht', hts]
    have h : 4 * S.E.Δ * (s : Int) = S.E.Δ * (4 * (s : Int)) := by ring
    rw [h]; exact Int.mul_emod_right _ _
  have hsend : Restated.HonestSendAt M S x k
      (⟨p, NamedObject.block B'⟩ : SignedMsg V (NamedObject V)) :=
    And.intro
      (Restated.mem_sent_diff_of_tick facts S Sched x hl hawp'
        (by rw [ht']; exact hall) (by rw [ht']; exact hemit.imp fun _ h => h.1))
      (hpk _ (le_refl _))
  have hmax : max (x[k].time : Int) S.E.t_GST = (x[k].time : Int) := max_eq_left (by linarith)
  have hvaw := Restated.honSlot_awake_around facts S Sched hv
  obtain ⟨d, hkd, hdlt, hdlbl⟩ := Restated.deliver_of_honestSendAt facts S Sched x hsync
    (D := M.vote_time S.E s) hsend (by rw [hmax]; linarith)
    (by rw [hmax]; exact awakeThroughout_mono Sched hvaw (by linarith) (by linarith))
  have hdmr : d < mr := Restated.deliver_lt_tick_g2 facts x hmr hdlbl hdlt
  have hvd : Restated.HonestThrough M Sched x d v :=
    Restated.honestThrough_of_mem_HonSlot facts S Sched x hmono hv (by rw [hct]; rw [hvt] at hdlt; linarith)
  have hk1d : (x[k + 1].time : Int) ≤ (x[d].time : Int) := Restated.time_mono_int facts S Sched x hkd
  obtain ⟨hfs, -, -, -, hfpm, hfpr, hfadm⟩ := hfields
  have hslot : B'.erase.slot ≤ (x[d][v].st).st.core.s := by
    rw [hfs]
    refine Restated.slot_ge_of_awake_of_slotStart facts S Sched x hmult htd ?_ (Restated.sent_of_deliver facts S Sched x hdlbl).2
      hvd (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›)
    rw [slotStart_closed, ← hts]; linarith
  have hWd : n_W ≤ d := by
    by_contra hcon
    have hle : d ≤ n_W := by omega
    have h1 := Restated.time_mono_int facts S Sched x hle
    have h2 := (Restated.tickStepAt_time facts x hnW).2
    linarith
  have hfin : Block.preceq (x[d][v].st).st.core.F B'.erase = true :=
    preceq_eq_true_iff_Preceq.mpr (preceq_trans_Preceq (hF v d hWd (le_of_lt hdlt) hvd) hCB)
  have hprop' : B'.erase.proposer? = some (S.E.proposer B'.erase.slot) := by
    rw [hfs]; exact hfpr
  have hpslot : B'.erase.parent.slot < B'.erase.slot := by
    rw [Proofs.NamedWire.erase_parent, hfs]
    have hmemT : B'.parent.erase ∈ (x[k][p].st).st.core.T := by
      rw [Restated.bodies_image_eq_T facts S Sched x k p]
      exact Finset.mem_image_of_mem NamedBlock.erase hfpm
    have h1 := Restated.slotStart_le_time_of_mem_tree facts S Sched x k p hmemT
    refine slot_lt_of_slotStart_lt_g2 S ?_
    rw [slotStart_closed (s := s), ← hts]; linarith
  have hbody : B' ∈ (x[d + 1][v].st).st.bodies :=
    Restated.block_admitted_of_deliver facts S Sched x hexec hdlbl hvd hslot hfin hprop' hpslot hfadm
  have hbodymr : B' ∈ (x[mr][v].st).st.bodies :=
    of_decide_eq_true (Restated.processed_mono facts S Sched x v (NamedObject.block B') hdmr
      (decide_eq_true hbody))
  rw [Restated.bodies_image_eq_T facts S Sched x mr v]
  exact Finset.mem_image_of_mem NamedBlock.erase hbodymr

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If `w` holds the named block `B`, not genesis, after `m` steps, and `B`'s proposer `q` is honest
    through step `m`, then the sent log at some step at or before `m` holds `q`'s own signed message
    for `B`. -/
theorem signed_of_mem_bodies_g2 (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {m : Nat} {w q : V} (hq : Restated.HonestThrough M Sched x m q) {B : NamedBlock V}
    (hB : B ∈ (x[m][w].st).st.bodies) (hgen : B ≠ NamedBlock.genesis)
    (hauth : B.proposer? = some q) :
    ∃ j : Nat, j ≤ m ∧
      (⟨q, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[j].sent := by
  have hauthor : NamedObject.author (NamedObject.block B) = some q := by
    rw [author_block]; exact hauth
  have h0 : Restated.Vocabulary.Execution.Object.processed M (x[0][w].st).st
      (NamedObject.block B) = false := by
    simp only [Restated.Vocabulary.Execution.Object.processed, decide_eq_false_iff_not]
    rw [Record.st_zero M S Sched x w, facts.nd.initial_st, facts.hd.initial_bodies,
      Finset.mem_singleton]
    exact hgen
  have hm1 : Restated.Vocabulary.Execution.Object.processed M (x[m][w].st).st
      (NamedObject.block B) = true := by
    simp only [Restated.Vocabulary.Execution.Object.processed, decide_eq_true_eq]
    exact hB
  obtain ⟨i, him, hf0, hf1⟩ :=
    Restated.exists_flip_of_processed facts S Sched x w (NamedObject.block B) h0 hm1
  rcases Restated.flip_step_cases facts S Sched x hf0 hf1 with
    ⟨sm, hlbl, -, -, hpay⟩ | ⟨τ, hlbl, haw, hem⟩
  · rcases hpay with hmsg | ⟨Bl, -, hcc⟩
    · have hsm : sm ∈ x[i].sent := (Restated.sent_of_deliver facts S Sched x hlbl).1
      have hhon : Restated.HonestThrough M Sched x i q := fun t ht =>
        hq t (le_trans ht (Restated.time_mono_int facts S Sched x (le_of_lt him)))
      have hres := hexec.unforgeable i sm q hsm (by rw [hmsg]; exact hauthor) hhon
      rw [hmsg] at hres
      exact ⟨i, le_of_lt him, hres⟩
    · exact hcc.elim
  · obtain ⟨out₁, hout₁, hst₁, hem⟩ := hem
    rcases hem with hmem | ⟨Bl, -, hcc⟩
    · have hhon : Restated.HonestThrough M Sched x (i + 1) q := fun t ht =>
        hq t (le_trans ht (Restated.time_mono_int facts S Sched x (Nat.succ_le_of_lt him)))
      have hsent := Restated.mem_sent_of_tick_of_state facts S Sched x hlbl haw
        (facts.nd.tick_send_eq_of_state (Setup.alwaysAwake S) w _ (τ : Int))
        hout₁ hst₁ hmem
      exact ⟨i + 1, Nat.succ_le_of_lt him,
        hexec.unforgeable (i + 1) ⟨w, NamedObject.block B⟩ q hsent hauthor hhon⟩
    · exact hcc.elim

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If `s > 0`, `proposedBlockAtStep S x i s B` holds at a step at or before `t`, `s`'s proposer is
    honest through `t`, and `X` is a block of slot `s` in a validator's tree after a step at or
    before `t`, then `X = B`. -/
theorem tree_slot_eq_sentProposal (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {s : Slot} (hs : 0 < s) {i : Nat} {B : Block V} (hB : Restated.proposedBlockAtStep M S x i s B)
    {t : Int} (hit : (x[i].time : Int) ≤ t) (hprop : HonestThroughTime Sched t (S.E.proposer s))
    {m : Nat} {v : V} (hmt : (x[m].time : Int) ≤ t)
    {X : Block V} (hX : X ∈ (x[m][v].st).st.core.T) (hXs : X.slot = s) : X = B := by
  have hne : X ≠ Block.genesis := by
    intro h
    rw [h, genesis_slot_inclG2] at hXs
    exact absurd hXs (Nat.ne_of_lt hs)
  obtain ⟨hpr, -, -⟩ := Restated.treeBlockShaped_sts facts S Sched x m v X hX hne
  obtain ⟨Xn, hXn, hXe⟩ := Restated.exists_named_of_mem_tree facts S Sched x m v hX
  have hXns : Xn.slot = s := by rw [← Proofs.NamedWire.erase_slot, hXe, hXs]
  have hXnpr : Xn.proposer? = some (S.E.proposer s) := by
    rw [← Proofs.NamedWire.erase_proposer, hXe, hpr, hXs]
  have hXngen : Xn ≠ NamedBlock.genesis := by
    intro h
    apply hne
    rw [← hXe, h]
    exact erase_named_genesis
  have hpm : Restated.HonestThrough M Sched x m (S.E.proposer s) := fun t' ht' => hprop t' (le_trans ht' hmt)
  obtain ⟨j, hjm, hsent⟩ := Restated.signed_of_mem_bodies_g2 facts S Sched x hexec hpm hXn hXngen hXnpr
  have hXB : Restated.proposedBlockAtStep M S x j s X := ⟨Xn, hsent, hXe, hXns, hXnpr⟩
  exact Restated.proposedBlockAtStep_unique_g1 facts S Sched x hexec.toUnforgeability
    (fun t' ht' => hprop t' (le_trans ht' (le_trans (Restated.time_mono_int facts S Sched x hjm) hmt)))
    (fun t' ht' => hprop t' (le_trans ht' hit)) hXB hB

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- The store slot `s`'s vote duty reads has the block tree of the node's own store. -/
theorem voteStoreAt_T (facts : Record.Facts M) (S : Setup V) (before : M.N) (s : Slot) :
    (Restated.voteStoreAt M S before s).T = before.st.core.T := by
  rw [Restated.voteStoreAt, facts.hd.Sts_setClock_core_T]

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- The store slot `s`'s vote duty reads has, for every slot `s'`, the pool of the node's own store. -/
theorem voteStoreAt_pool (facts : Record.Facts M) (S : Setup V) (before : M.N) (s s' : Slot) :
    (M.store_pool (Restated.voteStoreAt M S before s) s') = (M.store_pool before.st.core s') := by
  rw [Restated.voteStoreAt, facts.hd.Sts_setClock_core_pool]

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- The store slot `s`'s vote duty reads has the vote stamps of the node's own store. -/
theorem voteStoreAt_timestamp_vote (facts : Record.Facts M) (S : Setup V) (before : M.N) (s : Slot) :
    (Restated.voteStoreAt M S before s).timestamp_vote = before.st.core.timestamp_vote := by
  rw [Restated.voteStoreAt, facts.hd.setClock_core_timestamp_vote]

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- The store slot `s`'s vote duty reads has the block stamps of the node's own store. -/
theorem voteStoreAt_timestamp_block (facts : Record.Facts M) (S : Setup V) (before : M.N) (s : Slot) :
    (Restated.voteStoreAt M S before s).timestamp_block = before.st.core.timestamp_block := by
  rw [Restated.voteStoreAt, facts.hd.setClock_core_timestamp_block]

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- The store slot `s`'s proposal duty reads has, for every slot `s'`, the Goldfish votes of the
    node's own store. -/
theorem proposalStoreAt_gf_votes (facts : Record.Facts M) (S : Setup V) (before : M.N) (s s' : Slot) :
    (Restated.proposalStoreAt M S before s).gf_votes s' = before.st.core.gf_votes s' := by
  rw [Restated.proposalStoreAt, facts.hd.setClock_core_gf_votes]

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- `proposerVotesOf` at the proposal read of slot `s` is the node's slot-`(s − 1)` pool. -/
theorem proposerVotesOf_eq (facts : Record.Facts M) (S : Setup V) (before : M.N) (s : Slot) :
    Restated.proposerVotesOf M S before s = (M.store_pool before.st.core (s - 1)) := by
  rw [Restated.proposerVotesOf, facts.fc.proposer_view_toFinset, facts.sto.toHealing_gs_pool,
    Restated.proposalStoreAt_pool facts S before s]

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- A vote of an outcome of `proposerSupportOf` at slot `s` is in the node's slot-`(s − 1)` pool,
    and every outcome of its resolution test in the node's tree is `true`. -/
theorem mem_proposerSupportOf (facts : Record.Facts M) (S : Setup V) (before : M.N) (s : Slot)
    {U : Finset (GoldfishVote V)} (hU : Restated.proposerSupportOf M S before s ⇢ U)
    {u : GoldfishVote V} (hu : u ∈ U) :
    u ∈ (M.store_pool before.st.core (s - 1)) ∧
      ∀ b : Bool, M.resolved before.st.core.T u ⇢ b → b = true := by
  rw [Restated.proposerSupportOf] at hU
  obtain ⟨L, hL, rfl⟩ := (pCW% returns_map_elim_cw) _ _ U hU
  rw [List.mem_toFinset] at hu
  have key : ∀ b : Bool, M.resolved before.st.core.T u ⇢ b →
      u ∈ (M.store_pool before.st.core (s - 1)) ∧ b = true := by
    intro b hb
    have hb' : M.resolved
        (M.toHealing (Restated.proposalStoreAt M S before s)).toFG.toSG.toGoldfishStore.T u ⇢ b := by
      rw [facts.sto.toHealing_gs_T, Restated.proposalStoreAt_T facts S before s]; exact hb
    have h := (facts.fc.mem_proposer_support_view_iff _ s u L hL b hb').1 hu
    rw [facts.sto.toHealing_gs_gf_votes, Restated.proposalStoreAt_gf_votes facts S before s] at h
    exact ⟨(facts.sto.mem_store_pool_iff _ _ _).2 h.1, h.2⟩
  obtain ⟨b₀, hb₀⟩ := facts.sto.resolved_nonempty before.st.core.T u
  exact ⟨(key b₀ hb₀).1, fun b hb => (key b hb).2⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- A vote in the node's slot-`(s − 1)` pool whose resolution test in the node's tree can return
    `true` is in every outcome of `proposerSupportOf` at slot `s`. -/
theorem mem_proposerSupportOf_of (facts : Record.Facts M) (S : Setup V) (before : M.N) (s : Slot)
    {u : GoldfishVote V} (hu : u ∈ (M.store_pool before.st.core (s - 1)))
    (hres : M.resolved before.st.core.T u ⇢ true) :
    ∀ U : Finset (GoldfishVote V), Restated.proposerSupportOf M S before s ⇢ U → u ∈ U := by
  intro U hU
  rw [Restated.proposerSupportOf] at hU
  obtain ⟨L, hL, rfl⟩ := (pCW% returns_map_elim_cw) _ _ U hU
  rw [List.mem_toFinset]
  have hb' : M.resolved
      (M.toHealing (Restated.proposalStoreAt M S before s)).toFG.toSG.toGoldfishStore.T u ⇢ true := by
    rw [facts.sto.toHealing_gs_T, Restated.proposalStoreAt_T facts S before s]; exact hres
  refine (facts.fc.mem_proposer_support_view_iff _ s u L hL true hb').2 ⟨?_, rfl⟩
  rw [facts.sto.toHealing_gs_gf_votes, Restated.proposalStoreAt_gf_votes facts S before s]
  exact (facts.sto.mem_store_pool_iff _ _ _).1 hu

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- A vote of an outcome of `v`'s slot-`s` raw view at the vote read is in the node's slot-`(s − 1)`
    pool with a stamp strictly before slot `s − 1`'s view freeze, or is a slot-`(s − 1)` vote
    included in a slot-`s` block of the node's tree. -/
theorem voteViewOf_cases (facts : Record.Facts M) (S : Setup V) (before : M.N) (s : Slot)
    {Y : Finset (GoldfishVote V)}
    (hY : Restated.voteViewOf M S.E (Restated.voteStoreAt M S before s) ⇢ Y)
    {u : GoldfishVote V} (hu : u ∈ Y) :
    (u ∈ (M.store_pool before.st.core (s - 1)) ∧ ∃ τ : Stamp, before.st.core.timestamp_vote u = some τ ∧
        τ < ((M.view_freeze S.E (s - 1) : Int) : Stamp)) ∨
      ∃ X ∈ before.st.core.T, X.slot = s ∧ u ∈ X.gf_votes ∧ u.slot = s - 1 := by
  rw [Restated.voteViewOf, Restated.voteStoreAt_slot facts S before s] at hY
  have h := facts.fc.voter_view_cases S.E _ s Y hY hu
  rw [facts.sto.toHealing_gs_pool, facts.sto.toHealing_gs_timestamp_vote, facts.sto.toHealing_gs_T,
    Restated.voteStoreAt_pool facts S before s, Restated.voteStoreAt_timestamp_vote facts S before s,
    Restated.voteStoreAt_T facts S before s] at h
  exact h

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- A slot-`(s − 1)` vote included in a slot-`s` block of the node's tree is in every outcome of the
    slot-`s` raw view of its vote read. -/
theorem mem_voteViewOf_of_carried (facts : Record.Facts M) (S : Setup V) (before : M.N) (s : Slot)
    {u : GoldfishVote V} {X : Block V} (hX : X ∈ before.st.core.T) (hXs : X.slot = s)
    (hu : u ∈ X.gf_votes) (hus : u.slot = s - 1) :
    ∀ Y : Finset (GoldfishVote V),
      Restated.voteViewOf M S.E (Restated.voteStoreAt M S before s) ⇢ Y → u ∈ Y := by
  intro Y hY
  rw [Restated.voteViewOf, Restated.voteStoreAt_slot facts S before s] at hY
  refine facts.fc.mem_voter_view_of_carried S.E _ s ?_ hXs hu hus Y hY
  rw [facts.sto.toHealing_gs_T, Restated.voteStoreAt_T facts S before s]; exact hX

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- For a vote of an outcome of `v`'s slot-`s` support view at the vote read, and every outcome `b`
    of its resolution test: the vote is in the node's slot-`(s − 1)` pool, with its head resolving
    to a block of a slot at most the vote's and both stamps strictly before slot `s − 1`'s view
    freeze; or it is a slot-`(s − 1)` vote of the support list of a slot-`s` block of the node's
    tree, and `b` is `true`. -/
theorem voteSupportViewOf_cases (facts : Record.Facts M) (S : Setup V) (before : M.N) (s : Slot)
    {Y : Finset (GoldfishVote V)}
    (hY : Restated.voteSupportViewOf M S.E (Restated.voteStoreAt M S before s) ⇢ Y)
    {u : GoldfishVote V} (hu : u ∈ Y) :
    ∀ b : Bool, M.resolved before.st.core.T u ⇢ b →
    (u ∈ (M.store_pool before.st.core (s - 1)) ∧ ∃ X : Block V, Block.find? before.st.core.T u.head = some X ∧
        X.slot ≤ u.slot ∧ ∃ τ σ : Stamp, before.st.core.timestamp_vote u = some τ ∧
          before.st.core.timestamp_block X = some σ ∧
          τ < ((M.view_freeze S.E (s - 1) : Int) : Stamp) ∧
          σ < ((M.view_freeze S.E (s - 1) : Int) : Stamp)) ∨
      ∃ X ∈ before.st.core.T, X.slot = s ∧ u ∈ X.gf_support_votes ∧
        b = true ∧ u.slot = s - 1 := by
  intro b hb
  rw [Restated.voteSupportViewOf, Restated.voteStoreAt_slot facts S before s] at hY
  have hb' : M.resolved
      (M.toHealing (Restated.voteStoreAt M S before s)).toFG.toSG.toGoldfishStore.T u ⇢ b := by
    rw [facts.sto.toHealing_gs_T, Restated.voteStoreAt_T facts S before s]; exact hb
  have h := facts.fc.voter_support_view_cases S.E _ s Y hY hu b hb'
  rw [facts.sto.toHealing_gs_pool, facts.sto.toHealing_gs_timestamp_vote, facts.sto.toHealing_gs_timestamp_block,
    facts.sto.toHealing_gs_T, Restated.voteStoreAt_pool facts S before s,
    Restated.voteStoreAt_timestamp_vote facts S before s,
    Restated.voteStoreAt_timestamp_block facts S before s,
    Restated.voteStoreAt_T facts S before s] at h
  exact h

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- A slot-`(s − 1)` vote of the support list of a slot-`s` block of the node's tree, whose
    resolution test can return `true`, is in every outcome of the slot-`s` support view of its vote
    read. -/
theorem mem_voteSupportViewOf_of_carried (facts : Record.Facts M) (S : Setup V) (before : M.N) (s : Slot)
    {u : GoldfishVote V} {X : Block V} (hX : X ∈ before.st.core.T) (hXs : X.slot = s)
    (hu : u ∈ X.gf_support_votes) (hres : M.resolved before.st.core.T u ⇢ true)
    (hus : u.slot = s - 1) :
    ∀ Y : Finset (GoldfishVote V),
      Restated.voteSupportViewOf M S.E (Restated.voteStoreAt M S before s) ⇢ Y → u ∈ Y := by
  intro Y hY
  rw [Restated.voteSupportViewOf, Restated.voteStoreAt_slot facts S before s] at hY
  refine facts.fc.mem_voter_support_view_of_carried S.E _ s ?_ hXs hu true ?_ rfl hus Y hY
  · rw [facts.sto.toHealing_gs_T, Restated.voteStoreAt_T facts S before s]; exact hX
  · rw [facts.sto.toHealing_gs_T, Restated.voteStoreAt_T facts S before s]; exact hres

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- For every descendant `C` of `Y` and every validator `w` that does not equivocate in `votesP`,
    `w` holds a slot-`s` vote in `supportV` that supports `C` exactly when it holds one in
    `supportP` that supports `C`. -/
theorem supporter_iff_of_proposalViews_eqv (facts : Record.Facts M) {Tp Tv : Finset (Block V)}
    {votesP supportP supportV : Finset (GoldfishVote V)} {s : Slot} {Y C : Block V}
    (hsupPV : ∀ u ∈ supportP, (∃ X, Block.find? Tp u.head = some X ∧ Block.Preceq Y X) →
      u ∈ supportV)
    (hsupVP : ∀ u ∈ supportV, (∃ X, Block.find? Tv u.head = some X ∧ Block.Preceq Y X) →
      u ∈ supportP ∨ M.equivocates votesP u.val_index = true)
    (hfind : ∀ u ∈ supportP, ∀ X, Block.Preceq Y X →
      (Block.find? Tp u.head = some X ↔ Block.find? Tv u.head = some X))
    (hYC : Block.Preceq Y C)
    (tv : GoldfishVote V → Bool) (htv : ∀ u, M.targets_under Tv C u ⇢ tv u)
    (tp : GoldfishVote V → Bool) (htp : ∀ u, M.targets_under Tp C u ⇢ tp u)
    (w : V) (hw : M.equivocates votesP w = false) :
    (∃ u ∈ supportV, u.val_index = w ∧ u.slot = s ∧ tv u = true) ↔
      (∃ u ∈ supportP, u.val_index = w ∧ u.slot = s ∧ tp u = true) := by
  constructor
  · rintro ⟨u, hu, huw, hus, ht⟩
    obtain ⟨X, hX, hXs, hCX⟩ := (facts.fc.targets_under_eq_true_iff Tv C u (tv u) (htv u)).1 ht
    have hYX : Block.Preceq Y X := Proofs.ModelProperties.Preceq_trans hYC hCX
    rcases hsupVP u hu ⟨X, hX, hYX⟩ with huP | huE
    · have hXp : Block.find? Tp u.head = some X := (hfind u huP X hYX).2 hX
      exact ⟨u, huP, huw, hus,
        (facts.fc.targets_under_eq_true_iff Tp C u (tp u) (htp u)).2 ⟨X, hXp, hXs, hCX⟩⟩
    · rw [huw, hw] at huE
      exact absurd huE (by decide)
  · rintro ⟨u, hu, huw, hus, ht⟩
    obtain ⟨X, hX, hXs, hCX⟩ := (facts.fc.targets_under_eq_true_iff Tp C u (tp u) (htp u)).1 ht
    have hYX : Block.Preceq Y X := Proofs.ModelProperties.Preceq_trans hYC hCX
    have huV : u ∈ supportV := hsupPV u hu ⟨X, hX, hYX⟩
    have hXv : Block.find? Tv u.head = some X := (hfind u hu X hYX).1 hX
    exact ⟨u, huV, huw, hus,
      (facts.fc.targets_under_eq_true_iff Tv C u (tv u) (htv u)).2 ⟨X, hXv, hXs, hCX⟩⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If the voter's and the proposer's raw and support views agree up to signers that equivocate at
    the proposer, and the two stores resolve each support vote of the proposer to the same
    descendant of `Y`, then for every descendant `C` of `Y` the Goldfish scores at the two stores
    are equal, and so are the two participant counts. -/
theorem score_eq_of_proposalViews_eqv (facts : Record.Facts M) {E : Env V} {Tp Tv : Finset (Block V)}
    {votesP supportP votesV supportV : Finset (GoldfishVote V)} {s : Slot} {Y C : Block V}
    (hraw : ∀ u ∈ votesV, u ∈ votesP ∨ M.equivocates votesP u.val_index = true)
    (hsub : votesP ⊆ votesV)
    (hsupPV : ∀ u ∈ supportP, (∃ X, Block.find? Tp u.head = some X ∧ Block.Preceq Y X) →
      u ∈ supportV)
    (hsupVP : ∀ u ∈ supportV, (∃ X, Block.find? Tv u.head = some X ∧ Block.Preceq Y X) →
      u ∈ supportP ∨ M.equivocates votesP u.val_index = true)
    (hfind : ∀ u ∈ supportP, ∀ X, Block.Preceq Y X →
      (Block.find? Tp u.head = some X ↔ Block.find? Tv u.head = some X))
    (hYC : Block.Preceq Y C) :
    (∀ g : ℕ, M.goldfish_score E Tv votesV supportV s C ⇢ g →
        ∀ g' : ℕ, M.goldfish_score E Tp votesP supportP s C ⇢ g' → g = g') ∧
      M.voters_count E votesV s = M.voters_count E votesP s := by
  refine ⟨?_, facts.fc.voters_count_eq_of_participates E s s
    (Restated.participates_eq_of_proposalViews facts hraw hsub)⟩
  intro g hg g' hg'
  let tv : GoldfishVote V → Bool := fun u =>
    Classical.choose (facts.fc.targets_under_nonempty Tv C u)
  have htv : ∀ u, M.targets_under Tv C u ⇢ tv u := fun u =>
    Classical.choose_spec (facts.fc.targets_under_nonempty Tv C u)
  let tp : GoldfishVote V → Bool := fun u =>
    Classical.choose (facts.fc.targets_under_nonempty Tp C u)
  have htp : ∀ u, M.targets_under Tp C u ⇢ tp u := fun u =>
    Classical.choose_spec (facts.fc.targets_under_nonempty Tp C u)
  exact facts.fc.goldfish_score_eq_of_iff E s C
    (Restated.equivocates_eq_of_proposalViews facts hraw hsub) tv htv tp htp
    (fun w hw => Restated.supporter_iff_of_proposalViews_eqv facts hsupPV hsupVP hfind hYC
      tv htv tp htp w
      (by rw [← Restated.equivocates_eq_of_proposalViews facts hraw hsub w]; exact hw))
    g hg g' hg'

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- In an sts execution with unforgeable signatures, if `s`'s proposer is honest through the instant
    of `x[i]` and `proposedBlockAtStep S x i s B` holds, then the proposer is awake at slot `s`'s
    proposal instant. -/
theorem sentProposal_awake (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hunf : Restated.Unforgeability M S x) {i : Nat} {s : Slot} {B : Block V}
    (hprop : HonestThroughTime Sched (x[i].time : Int) (S.E.proposer s))
    (hB : Restated.proposedBlockAtStep M S x i s B) :
    S.E.proposer s ∈ Sched.awake (M.proposal_time S.E s) := by
  obtain ⟨B', hmem, -, hBslot, hauth⟩ := hB
  have hauthor : NamedObject.author (NamedObject.block B') = some (S.E.proposer s) := by
    rw [author_block]; exact hauth
  obtain ⟨k, hki, t, hl, haw, out, hout, hemit⟩ :=
    Restated.tick_of_honest_signed_upTo facts S Sched x (S.E.proposer s) (.block B')
      (x[i].time : Int) hprop hunf hauthor i le_rfl hmem
  obtain ⟨W, hW, hemi⟩ :=
    Restated.emits_runAll_of_tick facts S Sched x (S.E.proposer s) hki hl haw hout hemit
  have ht : (t : Int) = M.proposal_time S.E s := by
    rw [(Restated.Vocabulary.Proofs.HealingSurface.emits_block_shape facts (Setup.alwaysAwake S) _
      W hW hemi).2.1, hBslot]
    rfl
  rw [← ht]
  exact (Finset.mem_sdiff.1 haw).1

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- `FinalizedBelowUpTo` up to `t` gives it up to every `t' ≤ t`. -/
theorem finalizedBelowUpTo_le (facts : Record.Facts M) {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (Record.protocolOf M S) Sched} {n_W : Nat} {t t' : Int} {C : Block V}
    (h : Restated.FinalizedBelowUpTo M S Sched x n_W t C) (htt : t' ≤ t) :
    Restated.FinalizedBelowUpTo M S Sched x n_W t' C :=
  fun v n₁ hW h1 hh => h v n₁ hW (le_trans h1 htt) hh

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If `s`'s proposer is awake and not held at slot `s`'s proposal instant, some outcome of its tick
    there emits the named block `B'`, and the proposal duty can return a result naming `B'`, then
    `proposedBlockAtStep S x (k + 1) s B'.erase` holds, `k` being that tick's step. -/
theorem proposedBlockAtStep_of_emit (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {s : Slot}
    (hawp : S.E.proposer s ∈ Sched.awake (M.proposal_time S.E s) \
      Sched.adv (M.proposal_time S.E s))
    {k : Nat} (hk : Restated.tickStepAt M x k (M.proposal_time S.E s)) {B' : NamedBlock V}
    (hemit : ∃ out : M.N × List (NamedObject V), M.tick (Setup.alwaysAwake S) (S.E.proposer s)
        (Record.wakeStage M Sched (M.proposal_time S.E s) x[k] (S.E.proposer s))
        (M.proposal_time S.E s) ⇢ out ∧ NamedObject.block B' ∈ out.2)
    {n : M.N} (hn : Restated.proposalReadOf M S (x[k][S.E.proposer s].st) s ⇢ n)
    {D : M.NS × Option (NamedBlock V)}
    (hD : M.duties_propose_block_with (M.gradeContract n.cache)
        S.E S.hc S.cfg ((Setup.alwaysAwake S).node (S.E.proposer s)) (M.ns_setClock S.E (x[k][S.E.proposer s].st).st (M.proposal_time S.E s)) ⇢ D)
    (hduty : D.2 = some B') :
    Restated.proposedBlockAtStep M S x (k + 1) s B'.erase := by
  have _hr_0 : M.reachedNode (x[k][S.E.proposer s].st) := Record.reachedNode_sts facts S Sched x k (S.E.proposer s)
  have _hv_0 : M.runs_as (x[k][S.E.proposer s].st) (S.E.proposer s) := Record.runs_as_sts facts S Sched x k (S.E.proposer s)
  obtain ⟨t', hl, ht'⟩ := hk
  have hts := Restated.proposal_time_closed_g1 facts S s
  have hdvd : (t' : Int) % S.E.Δ = 0 := by
    rw [ht', hts]
    have h : 4 * S.E.Δ * (s : Int) = S.E.Δ * (4 * (s : Int)) := by ring
    rw [h]; exact Int.mul_emod_right _ _
  have hawp' : S.E.proposer s ∈ Sched.awake (t' : Int) \ Sched.adv (t' : Int) := by
    rw [ht']; exact hawp
  obtain ⟨hfs, -, -, -, -, hfpr, -⟩ := Restated.proposalDuty_fields facts S (x[k][S.E.proposer s].st) s _ hn hD hduty
  obtain ⟨out₀, hout₀, hmem₀⟩ := hemit
  have hpos : 0 < s := by
    have _hr_s3 := Record.reachedNode_wakeStage facts S Sched x (k) (S.E.proposer s) (M.proposal_time S.E s)
    have _hv_s4 := Record.runs_as_wakeStage facts S Sched x (k) (S.E.proposer s) (M.proposal_time S.E s)
    have h := (facts.nd.block_mem_on_tick_emit (Setup.alwaysAwake S) (S.E.proposer s)
      _ (M.proposal_time S.E s) out₀ hout₀ hmem₀).1.1
    rw [show (Setup.alwaysAwake S).E.slotOf (M.proposal_time S.E s) = s from
      facts.sch.slotOf_proposal_time S.E s] at h
    exact h
  have hall : ∀ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) (S.E.proposer s)
        (Record.wakeStage M Sched (t' : Int) x[k] (S.E.proposer s)) (t' : Int) ⇢ out →
        NamedObject.block B' ∈ out.2 := by
    rw [ht']
    obtain ⟨c, hc, rfl⟩ := (pCW% returns_map_elim_cw) _ _ n hn
    rewrite [facts.nd.mkNode_cache] at hD
    have hD'B := hduty
    have hrunP := facts.nd.block_mem_on_tick_emit_awake (Setup.alwaysAwake S) (S.E.proposer s) _
      (M.proposal_time S.E s) out₀ hout₀ hmem₀
    rw [show (Setup.alwaysAwake S).E.slotOf (M.proposal_time S.E s) = s from
      facts.sch.slotOf_proposal_time S.E s] at hrunP
    have _hr_w2 := Record.reachedNode_wakeStage facts S Sched x k (S.E.proposer s) (M.proposal_time S.E s)
    have _hv_w2 := Record.runs_as_wakeStage facts S Sched x k (S.E.proposer s) (M.proposal_time S.E s)
    exact fun out hout => facts.nd.on_tick_emit_proposal_mem_of_outcomes (Setup.alwaysAwake S)
      (S.E.proposer s) _ s hpos
      ((Setup.alwaysAwake S).node_val_index (S.E.proposer s)).symm c
      (by rw [Record.wakeStage_st facts, Record.wakeStage_cache facts]; exact hc) D
      (by rw [Record.wakeStage_st facts]; exact hD) hD'B out hout hrunP
  refine ⟨B', Restated.mem_sent_of_tick facts S Sched x hl hawp' hall
    ⟨out₀, by rw [ht']; exact hout₀⟩, rfl, ?_, ?_⟩
  · rw [← Proofs.NamedWire.erase_slot]; exact hfs
  · rw [← Proofs.NamedWire.erase_proposer]; exact hfpr

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- A slot at or after the opening slot of the round after the switch round is at least `2`. -/
theorem two_le_slot_g2 (facts : Record.Facts M) (S : Setup V) (tE : Int) {s : Slot}
    (hslot : (M.opening_slot S.hc (Restated.switchRound M S tE + 1)) ≤ s) : 2 ≤ s := by
  have hR3 := S.hc.R_ge_three
  have h := opening_slot_closed_pvd facts S.hc (Restated.switchRound M S tE + 1)
  have hle : S.hc.R ≤ (Restated.switchRound M S tE + 1) * S.hc.R :=
    Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  rw [h] at hslot
  exact le_trans (le_trans (by decide) hR3) (le_trans hle hslot)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
set_option linter.unusedSectionVars false

/-- For a slot `s` at or after the opening slot of the round after the switch round whose proposer
    is honest through `vote_time s`, and a member `v` of `HonSlot S Sched s`, if
    `FinalizedBelowUpTo` holds at `Y` up to `vote_time s`, then every descendant of `Y` in the
    proposer's tree at its proposal tick is in `v`'s tree at its vote tick. -/
theorem proposalBlock_in_voterTree (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (hcatch : Restated.CatchUpOnWake M S x) (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (hsync : Restated.SynchronyFromWake M S x) (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight) (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t) (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT) (hcs : Restated.committeeSleepinessW M S Sched tE) {n_W : Nat} (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)))) {s : Slot}
    (hslot : (M.opening_slot S.hc (Restated.switchRound M S tE + 1)) ≤ s)
    (hprop : HonestThroughTime Sched (M.vote_time S.E s) (S.E.proposer s))
    {k : Nat} (hk : Restated.tickStepAt M x k (M.proposal_time S.E s))
    {v : V} (hv : v ∈ Restated.HonSlot M S Sched s) {mr : Nat}
    (hmr : Restated.tickStepAt M x mr (M.vote_time S.E s))
    {Y : Block V} (hFY : Restated.FinalizedBelowUpTo M S Sched x n_W (M.vote_time S.E s) Y)
    {X : Block V} (hX : X ∈ (x[k][S.E.proposer s].st).st.core.T) (hYX : Block.Preceq Y X) :
    X ∈ (x[mr][v].st).st.core.T := by
  have hd := S.E.Δ_pos
  have hd1 : (1 : Int) ≤ S.E.Δ := by
    simpa only [zero_add] using Int.add_one_le_iff.mpr S.E.Δ_pos
  obtain ⟨hGt, hAt⟩ := Restated.tGAT_le_proposal_time_g2 facts S tGAT tE gap hgst hlen hslot
  have hts := Restated.proposal_time_closed_g1 facts S s
  have hvt := Restated.vote_time_closed_g1 facts S s
  have hct := confirmation_time_closed_pvd facts S.E s
  obtain ⟨hk1, hk0⟩ := Restated.tickStepAt_time facts x hk
  obtain ⟨hmr1, hmr0⟩ := Restated.tickStepAt_time facts x hmr
  obtain ⟨Xn, hXn, hXe⟩ := Restated.exists_named_of_mem_tree facts S Sched x k (S.E.proposer s) hX
  have hpk : Restated.HonestThrough M Sched x k (S.E.proposer s) := fun t ht => hprop t (by linarith)
  have hunder : Restated.DeliveredDescendantUnderFinalizedInPhase M S x
      (M.vote_time S.E s - 2 * S.E.Δ) (M.vote_time S.E s) Y :=
    Restated.deliveredUnderFinalized_of_below facts x hnW (by linarith) hFY
  have hunderS : Restated.FinalizedPreceqAtStepsInPhase M S x
      (M.vote_time S.E s - 2 * S.E.Δ) (M.vote_time S.E s) Y :=
    Restated.finalizedPreceqAtSteps_of_below facts x hnW (by linarith) hFY
  have hwaw : v ∈ Sched.awakeThroughout (M.vote_time S.E s - 2 * S.E.Δ)
      (M.vote_time S.E s) := by
    have e : M.vote_time S.E s - 2 * S.E.Δ = M.proposal_time S.E s - S.E.Δ := by
      rw [hvt, hts]; ring
    rw [e]; exact Restated.honSlot_awake_around facts S Sched hv
  have hvmr : v ∉ Sched.adv (x[mr].time : Int) :=
    Restated.honestThrough_of_mem_HonSlot facts S Sched x hmono hv (by rw [hct]; linarith) _ le_rfl
  obtain ⟨hT, -⟩ := Restated.block_in_tree_of_holder_atTick facts S Sched x hexec hsync hmult htd hmono hgst hcv
    hphase hthird hcs (Restated.delta_le_of_healingLengthη facts S hlen) (t := M.vote_time S.E s) hunder
    hunderS
    hXn hpk (by rw [hXe]; exact hYX) (by linarith) (by linarith) (by linarith) le_rfl hmr hvmr
    hwaw
  rw [hXe] at hT
  exact hT

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
set_option linter.unusedSectionVars false

/-- For a slot `s` at or after the opening slot of the round after the switch round whose proposer
    is honest through `vote_time s` and awake at `s`'s proposal instant, and a member `v` of
    `HonSlot S Sched s`, if `FinalizedBelowUpTo` holds at `Y` up to `vote_time s`, then every
    descendant of `Y` in `v`'s tree at its vote tick, stamped strictly before one delay before `s`'s
    proposal instant, is in the proposer's tree at its proposal tick. -/
theorem voterBlock_in_proposalTree (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (hcatch : Restated.CatchUpOnWake M S x) (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (hsync : Restated.SynchronyFromWake M S x) (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight) (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t) (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT) (hcs : Restated.committeeSleepinessW M S Sched tE) {n_W : Nat} (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)))) {s : Slot}
    (hslot : (M.opening_slot S.hc (Restated.switchRound M S tE + 1)) ≤ s)
    (hprop : HonestThroughTime Sched (M.vote_time S.E s) (S.E.proposer s))
    (hawp : S.E.proposer s ∈ Sched.awake (M.proposal_time S.E s))
    {k : Nat} (hk : Restated.tickStepAt M x k (M.proposal_time S.E s))
    (hwinp : S.E.proposer s ∈ Sched.awakeThroughout (M.proposal_time S.E s - 2 * S.E.Δ)
      (M.proposal_time S.E s))
    {v : V} (hv : v ∈ Restated.HonSlot M S Sched s) {mr : Nat}
    {Y : Block V} (hFY : Restated.FinalizedBelowUpTo M S Sched x n_W (M.vote_time S.E s) Y)
    {X : Block V} (hX : X ∈ (x[mr][v].st).st.core.T) {σ : Stamp}
    (hσ : (x[mr][v].st).st.core.timestamp_block X = some σ)
    (hσc : σ < ((M.proposal_time S.E s - S.E.Δ : Int) : Stamp)) (hYX : Block.Preceq Y X) :
    X ∈ (x[k][S.E.proposer s].st).st.core.T := by
  have hd := S.E.Δ_pos
  have hd1 : (1 : Int) ≤ S.E.Δ := by
    simpa only [zero_add] using Int.add_one_le_iff.mpr S.E.Δ_pos
  obtain ⟨hGt, hAt⟩ := Restated.tGAT_le_proposal_time_g2 facts S tGAT tE gap hgst hlen hslot
  have hts := Restated.proposal_time_closed_g1 facts S s
  have hct := confirmation_time_closed_pvd facts S.E s
  have hpv := Restated.proposal_time_le_vote_time_g1 facts S s
  obtain ⟨hk1, hk0⟩ := Restated.tickStepAt_time facts x hk
  have hpos : (0 : Int) < M.proposal_time S.E s - S.E.Δ := by
    have h0 : (0 : Int) ≤ tGAT := le_trans S.E.t_GST_nonneg hgst
    linarith
  obtain ⟨nc, hnc⟩ := Restated.exists_tickStepAt facts x htd hpos
  obtain ⟨hnc1, hnc0⟩ := Restated.tickStepAt_time facts x hnc
  have hdvd : (M.proposal_time S.E s - S.E.Δ) % S.E.Δ = 0 := by
    have h : M.proposal_time S.E s - S.E.Δ = S.E.Δ * (4 * (s : Int) - 1) := by
      rw [hts]; ring
    rw [h]; exact Int.mul_emod_right _ _
  have hvaw := Restated.honSlot_awake_around facts S Sched hv
  have hvc : v ∈ Sched.awake (M.proposal_time S.E s - S.E.Δ) \
      Sched.adv (M.proposal_time S.E s - S.E.Δ) := by
    refine Finset.mem_sdiff.2 ⟨mem_awake_of_awakeThroughout Sched hvaw le_rfl (by linarith), ?_⟩
    intro hin
    exact ((Restated.mem_HonSlot facts).mp hv).2.2 (hmono _ _ (by rw [hct]; linarith) hin)
  obtain ⟨Xn, hXn, hXe⟩ := Restated.exists_named_of_mem_tree facts S Sched x mr v hX
  have hσ' : (x[mr][v].st).st.core.timestamp_block Xn.erase = some σ := by rw [hXe]; exact hσ
  have hXnc : Xn ∈ (x[nc][v].st).st.bodies := Restated.body_held_before_cut facts S Sched x hXn hσ' hσc hnc hvc hdvd
      (Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono hnc hdvd hvc)
  have hvnc : Restated.HonestThrough M Sched x nc v :=
    Restated.honestThrough_of_mem_HonSlot facts S Sched x hmono hv (by rw [hct]; linarith)
  have hunder : Restated.DeliveredDescendantUnderFinalizedInPhase M S x
      (M.proposal_time S.E s - 2 * S.E.Δ) (M.proposal_time S.E s) Y :=
    Restated.deliveredUnderFinalized_of_below facts x hnW (by linarith) (Restated.finalizedBelowUpTo_le facts hFY hpv)
  have hunderS : Restated.FinalizedPreceqAtStepsInPhase M S x
      (M.proposal_time S.E s - 2 * S.E.Δ) (M.proposal_time S.E s) Y :=
    Restated.finalizedPreceqAtSteps_of_below facts x hnW (by linarith) (Restated.finalizedBelowUpTo_le facts hFY hpv)
  have hpadv : S.E.proposer s ∉ Sched.adv (x[k].time : Int) := hprop _ (by linarith)
  obtain ⟨hT, -⟩ := Restated.block_in_tree_of_holder_atTick facts S Sched x hexec hsync hmult htd hmono hgst hcv
    hphase hthird hcs (Restated.delta_le_of_healingLengthη facts S hlen) (t := M.proposal_time S.E s)
    hunder hunderS hXnc hvnc (by rw [hXe]; exact hYX) (by linarith) (by linarith) (by linarith)
    le_rfl hk
    hpadv hwinp
  rw [hXe] at hT
  exact hT

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
set_option linter.unusedSectionVars false

/-- For a slot `s` at or after the opening slot of the round after the switch round whose proposer,
    honest and awake, emits the named block `B'` its proposal duty returns, and a member `v` of
    `HonSlot S Sched s`, if `FinalizedBelowUpTo` holds at an ancestor `Y` of `B'` up to
    `vote_time s`, then `B'`'s erasure is in `v`'s tree at its vote tick and is the only block of
    slot `s` there. -/
theorem proposal_in_voterTree_unique (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (hcatch : Restated.CatchUpOnWake M S x) (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (hsync : Restated.SynchronyFromWake M S x) (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight) (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t) (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT) (hcs : Restated.committeeSleepinessW M S Sched tE) {n_W : Nat} (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)))) {s : Slot}
    (hslot : (M.opening_slot S.hc (Restated.switchRound M S tE + 1)) ≤ s)
    (hprop : HonestThroughTime Sched (M.vote_time S.E s) (S.E.proposer s))
    (hawp : S.E.proposer s ∈ Sched.awake (M.proposal_time S.E s))
    {k : Nat} (hk : Restated.tickStepAt M x k (M.proposal_time S.E s))
    {B' : NamedBlock V}
    (hemit : ∃ out : M.N × List (NamedObject V), M.tick (Setup.alwaysAwake S) (S.E.proposer s)
        (Record.wakeStage M Sched (M.proposal_time S.E s) x[k] (S.E.proposer s))
        (M.proposal_time S.E s) ⇢ out ∧ NamedObject.block B' ∈ out.2)
    {n : M.N} (hn : Restated.proposalReadOf M S (x[k][S.E.proposer s].st) s ⇢ n)
    {D : M.NS × Option (NamedBlock V)}
    (hD : M.duties_propose_block_with (M.gradeContract n.cache)
        S.E S.hc S.cfg ((Setup.alwaysAwake S).node (S.E.proposer s)) (M.ns_setClock S.E (x[k][S.E.proposer s].st).st (M.proposal_time S.E s)) ⇢ D)
    (hduty : D.2 = some B')
    {v : V} (hv : v ∈ Restated.HonSlot M S Sched s) {mr : Nat}
    (hmr : Restated.tickStepAt M x mr (M.vote_time S.E s))
    {Y : Block V} (hFY : Restated.FinalizedBelowUpTo M S Sched x n_W (M.vote_time S.E s) Y)
    (hYB : Block.Preceq Y B'.erase) :
    B'.erase ∈ (x[mr][v].st).st.core.T ∧
      ∀ X ∈ (x[mr][v].st).st.core.T, X.slot = s → X = B'.erase := by
  have hd := S.E.Δ_pos
  have hd1 : (1 : Int) ≤ S.E.Δ := by
    simpa only [zero_add] using Int.add_one_le_iff.mpr S.E.Δ_pos
  obtain ⟨hGt, hAt⟩ := Restated.tGAT_le_proposal_time_g2 facts S tGAT tE gap hgst hlen hslot
  have hpv := Restated.proposal_time_le_vote_time_g1 facts S s
  have hs2 := Restated.two_le_slot_g2 facts S tE hslot
  obtain ⟨hk1, hk0⟩ := Restated.tickStepAt_time facts x hk
  obtain ⟨hmr1, hmr0⟩ := Restated.tickStepAt_time facts x hmr
  refine ⟨Restated.proposal_in_voterTree facts S Sched x hexec hsync hmult htd hmono hprop hawp hk
    (by linarith) hemit hn hD hduty hnW (by linarith) hFY hYB hv hmr, ?_⟩
  intro X hX hXs
  have hB := Restated.proposedBlockAtStep_of_emit facts S Sched x
    (Finset.mem_sdiff.2 ⟨hawp, hprop _ hpv⟩) hk hemit hn hD hduty
  exact Restated.tree_slot_eq_sentProposal facts S Sched x hexec (lt_of_lt_of_le (by decide) hs2) hB
    (t := M.vote_time S.E s)
    (by linarith) hprop (by linarith) hX hXs

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
set_option linter.unusedSectionVars false

/-- Under the hypotheses of `proposal_in_voterTree_unique`, the proposer's raw view at its proposal
    read is a subset of every outcome of `v`'s raw view at its vote read. -/
theorem proposerVotes_subset_voterView (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (hcatch : Restated.CatchUpOnWake M S x) (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (hsync : Restated.SynchronyFromWake M S x) (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight) (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t) (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT) (hcs : Restated.committeeSleepinessW M S Sched tE) {n_W : Nat} (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)))) {s : Slot}
    (hslot : (M.opening_slot S.hc (Restated.switchRound M S tE + 1)) ≤ s)
    (hprop : HonestThroughTime Sched (M.vote_time S.E s) (S.E.proposer s))
    (hawp : S.E.proposer s ∈ Sched.awake (M.proposal_time S.E s))
    {k : Nat} (hk : Restated.tickStepAt M x k (M.proposal_time S.E s))
    {B' : NamedBlock V}
    (hemit : ∃ out : M.N × List (NamedObject V), M.tick (Setup.alwaysAwake S) (S.E.proposer s)
        (Record.wakeStage M Sched (M.proposal_time S.E s) x[k] (S.E.proposer s))
        (M.proposal_time S.E s) ⇢ out ∧ NamedObject.block B' ∈ out.2)
    {n : M.N} (hn : Restated.proposalReadOf M S (x[k][S.E.proposer s].st) s ⇢ n)
    {D : M.NS × Option (NamedBlock V)}
    (hD : M.duties_propose_block_with (M.gradeContract n.cache)
        S.E S.hc S.cfg ((Setup.alwaysAwake S).node (S.E.proposer s)) (M.ns_setClock S.E (x[k][S.E.proposer s].st).st (M.proposal_time S.E s)) ⇢ D)
    (hduty : D.2 = some B')
    {v : V} (hv : v ∈ Restated.HonSlot M S Sched s) {mr : Nat}
    (hmr : Restated.tickStepAt M x mr (M.vote_time S.E s))
    {Y : Block V} (hFY : Restated.FinalizedBelowUpTo M S Sched x n_W (M.vote_time S.E s) Y)
    (hYB : Block.Preceq Y B'.erase) :
    ∀ Wv : Finset (GoldfishVote V),
      Restated.voteViewOf M S.E (Restated.voteStoreAt M S (x[mr][v].st) s) ⇢ Wv →
      Restated.proposerVotesOf M S (x[k][S.E.proposer s].st) s ⊆ Wv := by
  have _hr_0 : M.reachedNode (x[k][S.E.proposer s].st) := Record.reachedNode_sts facts S Sched x k (S.E.proposer s)
  have _hr_1 : M.reachedNode (x[mr][v].st) := Record.reachedNode_sts facts S Sched x mr v
  obtain ⟨hBv, -⟩ := Restated.proposal_in_voterTree_unique facts S Sched x tE hexec hmono htd hcatch tGAT gap hgst
    hlen hsync hthird hphase hmult hcv hcs hnW hslot hprop hawp hk hemit hn hD hduty hv hmr hFY hYB
  obtain ⟨hfs, hfgv, -, -, -, -, -⟩ := Restated.proposalDuty_fields facts S (x[k][S.E.proposer s].st) s _ hn hD hduty
  intro Wv hWv u hu
  have hpool : u ∈ (M.store_pool (x[k][S.E.proposer s].st).st.core (s - 1)) := by
    rw [← Restated.proposerVotesOf_eq facts S]; exact hu
  have hus : u.slot = s - 1 := Restated.slot_of_mem_pool_sts facts S Sched x k _ hpool
  have hgv : u ∈ B'.erase.gf_votes := by
    rw [hfgv]; rw [Restated.proposerVotesOf, List.mem_toFinset] at hu; exact hu
  exact Restated.mem_voteViewOf_of_carried facts S (x[mr][v].st) s hBv hfs hgv hus Wv hWv

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
set_option linter.unusedSectionVars false

/-- Under the hypotheses of `proposal_in_voterTree_unique`, every vote of `v`'s raw view at its vote
    read is in the proposer's raw view at its proposal read, or its signer equivocates there. -/
theorem voterView_raw_at_proposal (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (hcatch : Restated.CatchUpOnWake M S x) (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (hsync : Restated.SynchronyFromWake M S x) (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight) (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t) (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT) (hcs : Restated.committeeSleepinessW M S Sched tE) {n_W : Nat} (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)))) {s : Slot}
    (hslot : (M.opening_slot S.hc (Restated.switchRound M S tE + 1)) ≤ s)
    (hprop : HonestThroughTime Sched (M.vote_time S.E s) (S.E.proposer s))
    (hawp : S.E.proposer s ∈ Sched.awake (M.proposal_time S.E s))
    {k : Nat} (hk : Restated.tickStepAt M x k (M.proposal_time S.E s))
    {B' : NamedBlock V}
    (hemit : ∃ out : M.N × List (NamedObject V), M.tick (Setup.alwaysAwake S) (S.E.proposer s)
        (Record.wakeStage M Sched (M.proposal_time S.E s) x[k] (S.E.proposer s))
        (M.proposal_time S.E s) ⇢ out ∧ NamedObject.block B' ∈ out.2)
    {n : M.N} (hn : Restated.proposalReadOf M S (x[k][S.E.proposer s].st) s ⇢ n)
    {D : M.NS × Option (NamedBlock V)}
    (hD : M.duties_propose_block_with (M.gradeContract n.cache)
        S.E S.hc S.cfg ((Setup.alwaysAwake S).node (S.E.proposer s)) (M.ns_setClock S.E (x[k][S.E.proposer s].st).st (M.proposal_time S.E s)) ⇢ D)
    (hduty : D.2 = some B')
    {v : V} (hv : v ∈ Restated.HonSlot M S Sched s) {mr : Nat}
    (hmr : Restated.tickStepAt M x mr (M.vote_time S.E s))
    {Y : Block V} (hFY : Restated.FinalizedBelowUpTo M S Sched x n_W (M.vote_time S.E s) Y)
    (hYB : Block.Preceq Y B'.erase) :
    ∀ Wv : Finset (GoldfishVote V),
      Restated.voteViewOf M S.E (Restated.voteStoreAt M S (x[mr][v].st) s) ⇢ Wv →
    ∀ u ∈ Wv,
      u ∈ Restated.proposerVotesOf M S (x[k][S.E.proposer s].st) s ∨
        M.equivocates (Restated.proposerVotesOf M S (x[k][S.E.proposer s].st) s) u.val_index = true := by
  have hwinp := Restated.proposer_window_before_proposal facts S Sched x (r := Restated.switchRound M S tE + 1)
      (Nat.le_add_left 1 _) hslot hprop hawp hk hemit
  have _hr_0 : M.reachedNode (x[k][S.E.proposer s].st) := Record.reachedNode_sts facts S Sched x k (S.E.proposer s)
  have _hr_1 : M.reachedNode (x[mr][v].st) := Record.reachedNode_sts facts S Sched x mr v
  have hd := S.E.Δ_pos
  have hd1 : (1 : Int) ≤ S.E.Δ := by
    simpa only [zero_add] using Int.add_one_le_iff.mpr S.E.Δ_pos
  obtain ⟨hGt, hAt⟩ := Restated.tGAT_le_proposal_time_g2 facts S tGAT tE gap hgst hlen hslot
  have hs2 := Restated.two_le_slot_g2 facts S tE hslot
  have hts := Restated.proposal_time_closed_g1 facts S s
  have hct := confirmation_time_closed_pvd facts S.E s
  have hpv := Restated.proposal_time_le_vote_time_g1 facts S s
  have hs1 : ((s - 1 : Nat) : Int) = (s : Int) - 1 := nat_sub_one_cast_g2 (le_trans (by decide) hs2)
  obtain ⟨-, hUnique⟩ := Restated.proposal_in_voterTree_unique facts S Sched x tE hexec hmono htd hcatch tGAT gap
    hgst hlen hsync hthird hphase hmult hcv hcs hnW hslot hprop hawp hk hemit hn hD hduty hv hmr hFY
    hYB
  obtain ⟨-, hfgv, -, -, -, -, -⟩ := Restated.proposalDuty_fields facts S (x[k][S.E.proposer s].st) s _ hn hD hduty
  intro Wv hWv u hu
  rcases Restated.voteViewOf_cases facts S (x[mr][v].st) s hWv hu with ⟨hpool, τ, hτ, hτc⟩ | ⟨X, hX, hXs, hux, -⟩
  · -- the pool case
    have hpos : (0 : Int) < M.proposal_time S.E s - S.E.Δ := by
      have h0 : (0 : Int) ≤ tGAT := le_trans S.E.t_GST_nonneg hgst
      linarith
    obtain ⟨nc, hnc⟩ := Restated.exists_tickStepAt facts x htd hpos
    have hvaw := Restated.honSlot_awake_around facts S Sched hv
    have hvc : v ∈ Sched.awake (M.proposal_time S.E s - S.E.Δ) \
        Sched.adv (M.proposal_time S.E s - S.E.Δ) := by
      refine Finset.mem_sdiff.2 ⟨mem_awake_of_awakeThroughout Sched hvaw le_rfl (by linarith), ?_⟩
      intro hin
      exact ((Restated.mem_HonSlot facts).mp hv).2.2 (hmono _ _ (by rw [hct]; linarith) hin)
    have hss : slotStart S.E.Δ (s - 1) = M.proposal_time S.E s - 4 * S.E.Δ := by
      rw [slotStart_closed, hs1, hts]; ring
    have hτc' : τ < ((M.proposal_time S.E s - S.E.Δ : Int) : Stamp) := by
      have e : M.view_freeze S.E (s - 1) = M.proposal_time S.E s - S.E.Δ := by
        rw [(facts.sch.slot_instants_l55 S.E (s - 1)).2.2.1, Restated.proposal_time_closed_g1 facts S (s - 1),
        hs1, hts]; ring
      rw [← e]; exact hτc
    rw [Restated.proposerVotesOf_eq facts S]
    exact Restated.pooledVote_at_proposal facts S Sched x hsync hcatch hmult htd hmono
      (fun _ _ _ hl =>
          Restated.receipt_outcome_of_deliver_mono facts S Sched x hexec.idealization hmono hl)
      (le_trans (by decide) hs2) (by rw [hss]; linarith)
      (fun t ht => Restated.honestAwakeCover_of_premises facts S Sched hmono hgst hthird hphase hcs
        (by rw [hss] at ht; linarith))
      hwinp (fun t ht => hprop t (by linarith)) hk
      hnc hvc hpool hτ hτc' (fun k τ u hl _ => facts.ndRun.tick_outcome_sts S Sched x hexec.idealization.root_injective hexec.honestRootsNew k τ u hl)
  · -- the included case: the block is the proposal
    have hXB := hUnique X hX hXs
    rw [hXB, hfgv] at hux
    left
    rw [Restated.proposerVotesOf, List.mem_toFinset]
    exact hux

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
set_option linter.unusedSectionVars false

/-- For every vote `u` of the proposer's support view and every descendant `X` of `Y`, the proposal
    read's tree resolves `u`'s head to `X` exactly when the vote read's tree does. -/
theorem supportFind_agree_at_views (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (hcatch : Restated.CatchUpOnWake M S x) (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (hsync : Restated.SynchronyFromWake M S x) (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight) (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t) (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT) (hcs : Restated.committeeSleepinessW M S Sched tE) {n_W : Nat} (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)))) {s : Slot}
    (hslot : (M.opening_slot S.hc (Restated.switchRound M S tE + 1)) ≤ s)
    (hprop : HonestThroughTime Sched (M.vote_time S.E s) (S.E.proposer s))
    {k : Nat} (hk : Restated.tickStepAt M x k (M.proposal_time S.E s))
    {v : V} (hv : v ∈ Restated.HonSlot M S Sched s) {mr : Nat}
    (hmr : Restated.tickStepAt M x mr (M.vote_time S.E s))
    {Y : Block V} (hFY : Restated.FinalizedBelowUpTo M S Sched x n_W (M.vote_time S.E s) Y) :
    ∀ Up : Finset (GoldfishVote V), Restated.proposerSupportOf M S (x[k][S.E.proposer s].st) s ⇢ Up →
    ∀ u ∈ Up, ∀ X, Block.Preceq Y X →
      (Block.find? (Restated.proposalStoreAt M S (x[k][S.E.proposer s].st) s).T u.head = some X ↔
        Block.find? (Restated.voteStoreAt M S (x[mr][v].st) s).T u.head = some X) := by
  have hd := S.E.Δ_pos
  have hct := confirmation_time_closed_pvd facts S.E s
  have hpv := Restated.proposal_time_le_vote_time_g1 facts S s
  have hvc := Restated.vote_time_le_confirmation_time_g1 facts S s
  obtain ⟨hk1, hk0⟩ := Restated.tickStepAt_time facts x hk
  obtain ⟨hmr1, hmr0⟩ := Restated.tickStepAt_time facts x hmr
  have hpk : Restated.HonestThrough M Sched x k (S.E.proposer s) := fun t ht => hprop t (by linarith)
  have hvmr : Restated.HonestThrough M Sched x mr v :=
    Restated.honestThrough_of_mem_HonSlot facts S Sched x hmono hv (by linarith)
  intro Up hUp u hu X hYX
  rw [Restated.proposalStoreAt_T facts, Restated.voteStoreAt_T facts]
  constructor
  · intro hX
    have hXT := Proofs.HealingLemmas.find?_mem hX
    have hXr := Proofs.HealingLemmas.find?_root hX
    have hXv := Restated.proposalBlock_in_voterTree facts S Sched x tE hexec hmono htd hcatch tGAT gap hgst hlen
      hsync hthird hphase hmult hcv hcs hnW hslot hprop hk hv hmr hFY hXT hYX
    rw [← hXr]
    exact Restated.find_of_mem_tree_honest facts S Sched x hexec hvmr hXv
  · intro hX
    obtain ⟨-, hres⟩ := Restated.mem_proposerSupportOf facts S _ s hUp hu
    obtain ⟨b₀, hb₀⟩ := facts.sto.resolved_nonempty (x[k][S.E.proposer s].st).st.core.T u
    obtain ⟨X'', hX'', -⟩ := (facts.sto.resolved_eq_true_iff _ u b₀ hb₀).1 (hres b₀ hb₀)
    have heq := Restated.find_agree_sts facts S Sched x hexec hpk hvmr hX'' hX
    rw [heq] at hX''
    exact hX''

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
set_option linter.unusedSectionVars false

/-- Under the hypotheses of `proposal_in_voterTree_unique`, every vote of the proposer's support
    view whose head the proposal read's tree resolves to a descendant of `Y` is in every outcome of
    `v`'s support view at its vote read. -/
theorem proposerSupport_in_voterSupport (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (hcatch : Restated.CatchUpOnWake M S x) (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (hsync : Restated.SynchronyFromWake M S x) (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight) (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t) (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT) (hcs : Restated.committeeSleepinessW M S Sched tE) {n_W : Nat} (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)))) {s : Slot}
    (hslot : (M.opening_slot S.hc (Restated.switchRound M S tE + 1)) ≤ s)
    (hprop : HonestThroughTime Sched (M.vote_time S.E s) (S.E.proposer s))
    (hawp : S.E.proposer s ∈ Sched.awake (M.proposal_time S.E s))
    {k : Nat} (hk : Restated.tickStepAt M x k (M.proposal_time S.E s))
    {B' : NamedBlock V}
    (hemit : ∃ out : M.N × List (NamedObject V), M.tick (Setup.alwaysAwake S) (S.E.proposer s)
        (Record.wakeStage M Sched (M.proposal_time S.E s) x[k] (S.E.proposer s))
        (M.proposal_time S.E s) ⇢ out ∧ NamedObject.block B' ∈ out.2)
    {n : M.N} (hn : Restated.proposalReadOf M S (x[k][S.E.proposer s].st) s ⇢ n)
    {D : M.NS × Option (NamedBlock V)}
    (hD : M.duties_propose_block_with (M.gradeContract n.cache)
        S.E S.hc S.cfg ((Setup.alwaysAwake S).node (S.E.proposer s)) (M.ns_setClock S.E (x[k][S.E.proposer s].st).st (M.proposal_time S.E s)) ⇢ D)
    (hduty : D.2 = some B')
    {v : V} (hv : v ∈ Restated.HonSlot M S Sched s) {mr : Nat}
    (hmr : Restated.tickStepAt M x mr (M.vote_time S.E s))
    {Y : Block V} (hFY : Restated.FinalizedBelowUpTo M S Sched x n_W (M.vote_time S.E s) Y)
    (hYB : Block.Preceq Y B'.erase) :
    ∀ Up : Finset (GoldfishVote V), Restated.proposerSupportOf M S (x[k][S.E.proposer s].st) s ⇢ Up →
    ∀ Uv : Finset (GoldfishVote V),
      Restated.voteSupportViewOf M S.E (Restated.voteStoreAt M S (x[mr][v].st) s) ⇢ Uv →
    ∀ u ∈ Up,
      (∃ X, Block.find? (Restated.proposalStoreAt M S (x[k][S.E.proposer s].st) s).T u.head = some X ∧
        Block.Preceq Y X) →
      u ∈ Uv := by
  have _hr_0 : M.reachedNode (x[k][S.E.proposer s].st) := Record.reachedNode_sts facts S Sched x k (S.E.proposer s)
  have _hr_1 : M.reachedNode (x[mr][v].st) := Record.reachedNode_sts facts S Sched x mr v
  obtain ⟨hBv, -⟩ := Restated.proposal_in_voterTree_unique facts S Sched x tE hexec hmono htd hcatch tGAT gap hgst
    hlen hsync hthird hphase hmult hcv hcs hnW hslot hprop hawp hk hemit hn hD hduty hv hmr hFY hYB
  obtain ⟨hfs, -, hfgs, -, -, -, -⟩ := Restated.proposalDuty_fields facts S (x[k][S.E.proposer s].st) s _ hn hD hduty
  have hagree := Restated.supportFind_agree_at_views facts S Sched x tE hexec hmono htd hcatch tGAT gap hgst hlen
    hsync hthird hphase hmult hcv hcs hnW hslot hprop hk hv hmr hFY
  intro Up hUp Uv hUv u hu ⟨X, hX, hYX⟩
  obtain ⟨hpool, hres⟩ := Restated.mem_proposerSupportOf facts S _ s hUp hu
  have hus : u.slot = s - 1 := Restated.slot_of_mem_pool_sts facts S Sched x k _ hpool
  have hXv := (hagree Up hUp u hu X hYX).1 hX
  rw [Restated.voteStoreAt_T facts] at hXv
  obtain ⟨b₀, hb₀⟩ := facts.sto.resolved_nonempty (x[k][S.E.proposer s].st).st.core.T u
  obtain ⟨X'', hX'', hX''s⟩ := (facts.sto.resolved_eq_true_iff _ u b₀ hb₀).1 (hres b₀ hb₀)
  rw [Restated.proposalStoreAt_T facts] at hX
  have hXX : X'' = X := Option.some.inj (hX''.symm.trans hX)
  rw [hXX] at hX''s
  have hsup : u ∈ B'.erase.gf_support_votes := by
    rw [Restated.proposerSupportOf] at hUp
    obtain ⟨L, hL, rfl⟩ := (pCW% returns_map_elim_cw) _ _ Up hUp
    rw [hfgs L hL]; exact List.mem_toFinset.1 hu
  obtain ⟨b₁, hb₁⟩ := facts.sto.resolved_nonempty (x[mr][v].st).st.core.T u
  have hb₁t : b₁ = true := (facts.sto.resolved_eq_true_iff _ u b₁ hb₁).2 ⟨X, hXv, hX''s⟩
  rw [hb₁t] at hb₁
  exact Restated.mem_voteSupportViewOf_of_carried facts S (x[mr][v].st) s hBv hfs hsup hb₁ hus Uv hUv

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
set_option linter.unusedSectionVars false

/-- Under the hypotheses of `proposal_in_voterTree_unique`, every vote of `v`'s support view whose
    head the vote read's tree resolves to a descendant of `Y` is in every outcome of the proposer's
    support view, or its signer equivocates in the proposer's raw view. -/
theorem voterSupport_at_proposal (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (hcatch : Restated.CatchUpOnWake M S x) (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (hsync : Restated.SynchronyFromWake M S x) (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight) (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t) (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT) (hcs : Restated.committeeSleepinessW M S Sched tE) {n_W : Nat} (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)))) {s : Slot}
    (hslot : (M.opening_slot S.hc (Restated.switchRound M S tE + 1)) ≤ s)
    (hprop : HonestThroughTime Sched (M.vote_time S.E s) (S.E.proposer s))
    (hawp : S.E.proposer s ∈ Sched.awake (M.proposal_time S.E s))
    {k : Nat} (hk : Restated.tickStepAt M x k (M.proposal_time S.E s))
    {B' : NamedBlock V}
    (hemit : ∃ out : M.N × List (NamedObject V), M.tick (Setup.alwaysAwake S) (S.E.proposer s)
        (Record.wakeStage M Sched (M.proposal_time S.E s) x[k] (S.E.proposer s))
        (M.proposal_time S.E s) ⇢ out ∧ NamedObject.block B' ∈ out.2)
    {n : M.N} (hn : Restated.proposalReadOf M S (x[k][S.E.proposer s].st) s ⇢ n)
    {D : M.NS × Option (NamedBlock V)}
    (hD : M.duties_propose_block_with (M.gradeContract n.cache)
        S.E S.hc S.cfg ((Setup.alwaysAwake S).node (S.E.proposer s)) (M.ns_setClock S.E (x[k][S.E.proposer s].st).st (M.proposal_time S.E s)) ⇢ D)
    (hduty : D.2 = some B')
    {v : V} (hv : v ∈ Restated.HonSlot M S Sched s) {mr : Nat}
    (hmr : Restated.tickStepAt M x mr (M.vote_time S.E s))
    {Y : Block V} (hFY : Restated.FinalizedBelowUpTo M S Sched x n_W (M.vote_time S.E s) Y)
    (hYB : Block.Preceq Y B'.erase) :
    ∀ Uv : Finset (GoldfishVote V),
      Restated.voteSupportViewOf M S.E (Restated.voteStoreAt M S (x[mr][v].st) s) ⇢ Uv →
    ∀ Up : Finset (GoldfishVote V), Restated.proposerSupportOf M S (x[k][S.E.proposer s].st) s ⇢ Up →
    ∀ u ∈ Uv,
      (∃ X, Block.find? (Restated.voteStoreAt M S (x[mr][v].st) s).T u.head = some X ∧ Block.Preceq Y X) →
      u ∈ Up ∨
        M.equivocates (Restated.proposerVotesOf M S (x[k][S.E.proposer s].st) s) u.val_index = true := by
  have hwinp := Restated.proposer_window_before_proposal facts S Sched x (r := Restated.switchRound M S tE + 1)
      (Nat.le_add_left 1 _) hslot hprop hawp hk hemit
  have _hr_0 : M.reachedNode (x[k][S.E.proposer s].st) := Record.reachedNode_sts facts S Sched x k (S.E.proposer s)
  have _hr_1 : M.reachedNode (x[mr][v].st) := Record.reachedNode_sts facts S Sched x mr v
  have hd := S.E.Δ_pos
  have hd1 : (1 : Int) ≤ S.E.Δ := by
    simpa only [zero_add] using Int.add_one_le_iff.mpr S.E.Δ_pos
  obtain ⟨hGt, hAt⟩ := Restated.tGAT_le_proposal_time_g2 facts S tGAT tE gap hgst hlen hslot
  have hs2 := Restated.two_le_slot_g2 facts S tE hslot
  have hts := Restated.proposal_time_closed_g1 facts S s
  have hct := confirmation_time_closed_pvd facts S.E s
  have hpv := Restated.proposal_time_le_vote_time_g1 facts S s
  have hs1 : ((s - 1 : Nat) : Int) = (s : Int) - 1 := nat_sub_one_cast_g2 (le_trans (by decide) hs2)
  obtain ⟨hk1, hk0⟩ := Restated.tickStepAt_time facts x hk
  obtain ⟨-, hUnique⟩ := Restated.proposal_in_voterTree_unique facts S Sched x tE hexec hmono htd hcatch tGAT gap
    hgst hlen hsync hthird hphase hmult hcv hcs hnW hslot hprop hawp hk hemit hn hD hduty hv hmr hFY
    hYB
  obtain ⟨-, -, hfgs, -, -, -, -⟩ := Restated.proposalDuty_fields facts S (x[k][S.E.proposer s].st) s _ hn hD hduty
  have hpk : Restated.HonestThrough M Sched x k (S.E.proposer s) := fun t ht => hprop t (by linarith)
  intro Uv hUv Up hUp u hu ⟨X, hX, hYX⟩
  rw [Restated.voteStoreAt_T facts] at hX
  obtain ⟨b₀, hb₀⟩ := facts.sto.resolved_nonempty (x[mr][v].st).st.core.T u
  rcases Restated.voteSupportViewOf_cases facts S (x[mr][v].st) s hUv hu b₀ hb₀ with
    ⟨hpool, X', hX', hX's, τ, σ, hτ, hσ, hτc, hσc⟩ | ⟨X', hX', hX's, hsup, -, -⟩
  · -- the pool case
    have hXX : X' = X := Option.some.inj (hX'.symm.trans hX)
    rw [hXX] at hX's hσ
    have e : M.view_freeze S.E (s - 1) = M.proposal_time S.E s - S.E.Δ := by
      rw [(facts.sch.slot_instants_l55 S.E (s - 1)).2.2.1, Restated.proposal_time_closed_g1 facts S (s - 1),
        hs1, hts]; ring
    rw [e] at hτc hσc
    have hss : slotStart S.E.Δ (s - 1) = M.proposal_time S.E s - 4 * S.E.Δ := by
      rw [slotStart_closed, hs1, hts]; ring
    have hpos : (0 : Int) < M.proposal_time S.E s - S.E.Δ := by
      have h0 : (0 : Int) ≤ tGAT := le_trans S.E.t_GST_nonneg hgst
      linarith
    obtain ⟨nc, hnc⟩ := Restated.exists_tickStepAt facts x htd hpos
    have hvaw := Restated.honSlot_awake_around facts S Sched hv
    have hvc : v ∈ Sched.awake (M.proposal_time S.E s - S.E.Δ) \
        Sched.adv (M.proposal_time S.E s - S.E.Δ) := by
      refine Finset.mem_sdiff.2 ⟨mem_awake_of_awakeThroughout Sched hvaw le_rfl (by linarith), ?_⟩
      intro hin
      exact ((Restated.mem_HonSlot facts).mp hv).2.2 (hmono _ _ (by rw [hct]; linarith) hin)
    rcases Restated.pooledVote_at_proposal facts S Sched x hsync hcatch hmult htd hmono
      (fun _ _ _ hl =>
          Restated.receipt_outcome_of_deliver_mono facts S Sched x hexec.idealization hmono hl)
        (le_trans (by decide) hs2) (by rw [hss]; linarith)
        (fun t ht => Restated.honestAwakeCover_of_premises facts S Sched hmono hgst hthird hphase hcs
          (by rw [hss] at ht; linarith))
        hwinp (fun t ht => hprop t (by linarith)) hk
        hnc hvc hpool hτ hτc (fun k τ u hl _ => facts.ndRun.tick_outcome_sts S Sched x hexec.idealization.root_injective hexec.honestRootsNew k τ u hl) with hin | heqv
    · left
      have hXT := Proofs.HealingLemmas.find?_mem hX
      have hXr := Proofs.HealingLemmas.find?_root hX
      have hXp := Restated.voterBlock_in_proposalTree facts S Sched x tE hexec hmono htd hcatch tGAT gap hgst hlen
        hsync hthird hphase hmult hcv hcs hnW hslot hprop hawp hk hwinp hv hFY hXT hσ hσc hYX
      have hfp := Restated.find_of_mem_tree_honest facts S Sched x hexec hpk hXp
      rw [hXr] at hfp
      obtain ⟨b₁, hb₁⟩ := facts.sto.resolved_nonempty (x[k][S.E.proposer s].st).st.core.T u
      have hb₁t : b₁ = true := (facts.sto.resolved_eq_true_iff _ u b₁ hb₁).2 ⟨X, hfp, hX's⟩
      rw [hb₁t] at hb₁
      exact Restated.mem_proposerSupportOf_of facts S _ s hin hb₁ Up hUp
    · right
      rw [Restated.proposerVotesOf_eq facts S]; exact heqv
  · -- the included case: the block is the proposal
    have hXB := hUnique X' hX' hX's
    rw [hXB] at hsup
    left
    rw [Restated.proposerSupportOf] at hUp
    obtain ⟨L, hL, rfl⟩ := (pCW% returns_map_elim_cw) _ _ Up hUp
    rw [List.mem_toFinset, ← hfgs L hL]
    exact hsup

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
set_option linter.unusedSectionVars false

/-- Under the hypotheses of `proposal_in_voterTree_unique`, every descendant `C` of `Y` has the same
    Goldfish score over the slot-`(s − 1)` votes at `v`'s vote read as at the proposer's proposal
    read, and the two participant counts are equal. -/
theorem score_eq_at_proposal_and_vote (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (hcatch : Restated.CatchUpOnWake M S x) (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (hsync : Restated.SynchronyFromWake M S x) (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight) (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t) (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT) (hcs : Restated.committeeSleepinessW M S Sched tE) {n_W : Nat} (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)))) {s : Slot}
    (hslot : (M.opening_slot S.hc (Restated.switchRound M S tE + 1)) ≤ s)
    (hprop : HonestThroughTime Sched (M.vote_time S.E s) (S.E.proposer s))
    (hawp : S.E.proposer s ∈ Sched.awake (M.proposal_time S.E s))
    {k : Nat} (hk : Restated.tickStepAt M x k (M.proposal_time S.E s))
    {B' : NamedBlock V}
    (hemit : ∃ out : M.N × List (NamedObject V), M.tick (Setup.alwaysAwake S) (S.E.proposer s)
        (Record.wakeStage M Sched (M.proposal_time S.E s) x[k] (S.E.proposer s))
        (M.proposal_time S.E s) ⇢ out ∧ NamedObject.block B' ∈ out.2)
    {n : M.N} (hn : Restated.proposalReadOf M S (x[k][S.E.proposer s].st) s ⇢ n)
    {D : M.NS × Option (NamedBlock V)}
    (hD : M.duties_propose_block_with (M.gradeContract n.cache)
        S.E S.hc S.cfg ((Setup.alwaysAwake S).node (S.E.proposer s)) (M.ns_setClock S.E (x[k][S.E.proposer s].st).st (M.proposal_time S.E s)) ⇢ D)
    (hduty : D.2 = some B')
    {v : V} (hv : v ∈ Restated.HonSlot M S Sched s) {mr : Nat}
    (hmr : Restated.tickStepAt M x mr (M.vote_time S.E s))
    {Y : Block V} (hFY : Restated.FinalizedBelowUpTo M S Sched x n_W (M.vote_time S.E s) Y)
    (hYB : Block.Preceq Y B'.erase) {C : Block V} (hYC : Block.Preceq Y C) :
    ∀ Wv : Finset (GoldfishVote V),
      Restated.voteViewOf M S.E (Restated.voteStoreAt M S (x[mr][v].st) s) ⇢ Wv →
    ∀ Uv : Finset (GoldfishVote V),
      Restated.voteSupportViewOf M S.E (Restated.voteStoreAt M S (x[mr][v].st) s) ⇢ Uv →
    ∀ Up : Finset (GoldfishVote V), Restated.proposerSupportOf M S (x[k][S.E.proposer s].st) s ⇢ Up →
    (∀ g : ℕ, M.goldfish_score S.E (Restated.voteStoreAt M S (x[mr][v].st) s).T Wv Uv (s - 1) C ⇢ g →
      ∀ g' : ℕ, M.goldfish_score S.E (Restated.proposalStoreAt M S (x[k][S.E.proposer s].st) s).T
        (Restated.proposerVotesOf M S (x[k][S.E.proposer s].st) s) Up (s - 1) C ⇢ g' → g = g') ∧
    M.voters_count S.E Wv (s - 1) =
      M.voters_count S.E (Restated.proposerVotesOf M S (x[k][S.E.proposer s].st) s) (s - 1) :=
  fun Wv hWv Uv hUv Up hUp =>
  Restated.score_eq_of_proposalViews_eqv facts
    (Restated.voterView_raw_at_proposal facts S Sched x tE hexec hmono htd hcatch tGAT gap hgst hlen hsync hthird
      hphase hmult hcv hcs hnW hslot hprop hawp hk hemit hn hD hduty hv hmr hFY hYB Wv hWv)
    (Restated.proposerVotes_subset_voterView facts S Sched x tE hexec hmono htd hcatch tGAT gap hgst hlen hsync
      hthird hphase hmult hcv hcs hnW hslot hprop hawp hk hemit hn hD hduty hv hmr hFY hYB Wv hWv)
    (Restated.proposerSupport_in_voterSupport facts S Sched x tE hexec hmono htd hcatch tGAT gap hgst hlen hsync
      hthird hphase hmult hcv hcs hnW hslot hprop hawp hk hemit hn hD hduty hv hmr hFY hYB Up hUp Uv hUv)
    (Restated.voterSupport_at_proposal facts S Sched x tE hexec hmono htd hcatch tGAT gap hgst hlen hsync hthird
      hphase hmult hcv hcs hnW hslot hprop hawp hk hemit hn hD hduty hv hmr hFY hYB Uv hUv Up hUp)
    (Restated.supportFind_agree_at_views facts S Sched x tE hexec hmono htd hcatch tGAT gap hgst hlen hsync
      hthird hphase hmult hcv hcs hnW hslot hprop hk hv hmr hFY Up hUp)
    hYC

end

section
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

local macro "p83pvd% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_83)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

end

end DecoupledConsensusModel.Sts.Restated
