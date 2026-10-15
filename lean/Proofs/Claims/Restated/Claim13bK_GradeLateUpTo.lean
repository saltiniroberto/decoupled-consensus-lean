import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bK_FreshAttestersW
import Proofs.Claims.Restated.Claim13bK_GradeLate
import Proofs.Claims.Restated.Claim13bStepGrade
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bStepKitDeliveryUpTo
import Proofs.Claims.Restated.Claim13bStepKitRecord
import Proofs.Claims.Restated.Claim13bStepKitTick
import Proofs.Claims.Restated.RunAll
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bK_FreshAttestersW
import Model.Conditions.Claim13bStepGrade
import Model.Conditions.Claim13bStepKitTick
import Model.Conditions.ClaimAsyncK_DeliveryUpTo
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring
import Proofs.Claims.Restated.WakeWindow

/-!
# Grades read at the late cutoff, with synchrony up to one delay after the action instant

Theorems on the round-`r` attestations of the members of `freshAttestersW`, with synchrony assumed
only up to `S.a r + Δ`: their tokens are in a receiver's views at round `r + 1`, a member opposes a
block that is an ancestor of none of its SG blocks, and a block graded at least 1 at round `r + 1`
is an ancestor of some member's round-`r` SG block.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- From any node state `before`, validator `v`'s round-`r` action can compute some attestation. -/
private theorem actionAttestationFrom_nonemptyLate (facts : Record.Facts M) (S : Setup V)
    (before : M.N) (v : V) (r : Round) :
    ∃ a, a ∈ Restated.actionAttestationFrom M S before v r := by
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc before.st.core.toHealing
    (Restated.Vocabulary.Execution.Setup.a M S r) before.cache
  obtain ⟨st, hst⟩ := facts.dt.duties_update_confirmation_with_nonempty (M.gradeContract c) S.E S.hc
    (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r))
    (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1)
  obtain ⟨D, hD⟩ := facts.dt.attest_with_nonempty (M.gradeContract (M.mkNode st before.record c).cache)
    S.E S.hc (S.node v) (M.mkNode st before.record c).st (M.mkNode st before.record c).record
  exact ⟨D.2.2, M.mkNode st before.record c, ⟨c, hc, st, hst, rfl⟩, D.1, D.2.1, hD⟩

/-- If `v`'s tick at round `r`'s action instant from `st` has an outcome and `st` passes the grade-2
    awake test of round `r`, any two attestations `v`'s round-`r` action can compute from `st` are
    equal. -/
private theorem actionAttestationFrom_uniqueLate (facts : Record.Facts M) (S : Setup V) (v : V)
    (st : M.N) (r : Round)
    (hne : ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) v st (Restated.Vocabulary.Execution.Setup.a M S r) ⇢ out)
    (hrun : M.awake_for_grade2 (Setup.alwaysAwake S) v st r)
    {a a' : NamedAttestation V}
    (ha : a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) st v r)
    (ha' : a' ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) st v r) (hn : M.reachedNode st := by trivial)
    (hv : M.runs_as st v := by trivial) : a = a' := by
  obtain ⟨out, hout⟩ := hne
  have h1 := Restated.namedTick_emits_only_attest facts S v st r hrun out hout a ha
  have h2 := Restated.namedTick_emits_only_attest facts S v st r hrun out hout a' ha'
  rw [h1] at h2
  simpa using h2

/-- The attestations `v`'s round-`r` action can compute from the wake stage at `t` of configuration
    `c` are those it can compute from `v`'s node state in `c`. -/
private theorem actionAttestationFrom_wakeStageLate (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (t : Int) (c : Config V (NamedObject V) M.N) (v : V) (r : Round) :
    Restated.actionAttestationFrom M S (Record.wakeStage M Sched t c v) v r =
      Restated.actionAttestationFrom M S (c[v].st) v r := by
  unfold Restated.actionAttestationFrom Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom
  rw [Record.wakeStage_st facts, Record.wakeStage_cache facts, Record.wakeStage_record facts]

/-- A member `v_1` of `freshAttestersW S Sched x r m` not held by the adversary up to round `r`'s
    action instant passes, at the tick step `n` at that instant, the grade-2 awake test of round
    `r`. -/
private theorem awake_for_grade2_of_mem_freshAttestersWLate (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    {r : Round} {n m : Nat} {v_1 : V}
    (hn : Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S r)))
    (hq : v_1 ∈ Restated.freshAttestersW M S Sched x r m)
    (hhon : ∀ t' ≤ Restated.Vocabulary.Execution.Setup.a M S r, v_1 ∉ Sched.adv t') :
    M.awake_for_grade2 (Setup.alwaysAwake S) v_1
      (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S r) x[n] v_1) r := by
  obtain ⟨τ, hlbl, hτ⟩ := id hn
  have hact : v_1 ∈ Restated.activeRoundW M S Sched r := ((Restated.mem_freshAttestersW facts).mp hq).1
  have hwin : v_1 ∈ Sched.awakeThroughout (M.early S.E S.hc r .g2 - S.E.Δ) (M.a S.hc S.E.Δ r) := by
    simp only [Restated.activeRoundW, Schedule.awakeThroughout, Finset.mem_inf,
      Finset.mem_Icc] at hact ⊢
    rw [facts.gr.early_g2_eq S r]
    intro t ht
    refine hact t ⟨?_, ht.2⟩
    have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
    have hΔ : 0 < S.E.Δ := S.E.Δ_pos
    simp only [wAttest]
    nlinarith [ht.1]
  exact Restated.run_fact_g2 facts S Sched x n τ r v_1 hlbl hτ hwin (by rw [hτ]; exact hhon)

/-- If step `n` is the tick step at `S.a r` and `v_1`'s tick there has an outcome and passes the
    grade-2 awake test of round `r`, then every attestation `v_1`'s round-`r` action can compute at
    step `n` was sent honestly at step `n`. -/
private theorem fresh_attest_honestSendLate (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    {r : Round} {n : Nat}
    (hn : Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S r)))
    {m : Nat} {v_1 : V} (hq : v_1 ∈ Restated.freshAttesters M S Sched x r m)
    (hnm : (x[n].time : Int) ≤ (x[m].time : Int))
    (hqr : v_1 ∉ Sched.adv ((Restated.Vocabulary.Execution.Setup.a M S r)))
    (hne : ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) v_1 (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S r) x[n] v_1)
        (Restated.Vocabulary.Execution.Setup.a M S r) ⇢ out)
    (hrun : M.awake_for_grade2 (Setup.alwaysAwake S) v_1
      (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S r) x[n] v_1) r) :
    ∀ a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][v_1].st) v_1 r,
    Restated.HonestSendAt M S x n (⟨v_1, NamedObject.attest a⟩
      : SignedMsg V (NamedObject V)) := by
  intro a ha
  obtain ⟨t', hlbl, ht'⟩ := id hn
  have hsent1 : (⟨v_1, NamedObject.attest a⟩
      : SignedMsg V (NamedObject V)) ∈ x[n + 1].sent - x[n].sent := by
    refine Restated.mem_sent_diff_of_tick facts S Sched x hlbl
      (by rw [ht']; exact Finset.mem_sdiff.2 ⟨Restated.awake_of_mem_freshAttesters facts hq, hqr⟩)
      (by rw [ht']; exact Restated.action_emod_delta facts S r) ?_ ?_
    · rw [ht']
      intro out hout
      have _hr_s1 := Record.reachedNode_wakeStage facts S Sched x (n) v_1 (Restated.Vocabulary.Execution.Setup.a M S r)
      have _hv_s2 := Record.runs_as_wakeStage facts S Sched x (n) v_1 (Restated.Vocabulary.Execution.Setup.a M S r)
      exact Restated.namedTick_emits_attest facts S v_1 _ r hrun out hout a
        (by rw [actionAttestationFrom_wakeStageLate facts]; exact ha)
    · rw [ht']
      exact hne
  have hqn : HonestThroughTime Sched (x[n].time : Int) v_1 := fun t ht =>
    Restated.honestThrough_of_mem_freshAttesters facts hq t (le_trans ht hnm)
  exact And.intro hsent1 (hqn (x[n].time : Int) (le_refl _))

/-- Whether or not `v_0` already held the sender's head when the attestation was delivered at step
    `k`, at step `m` the attestation's SG-vote projection is in the pool of its round of `v_0`'s
    grade view, with a stamp at or before `x[k].time`. -/
private theorem fresh_token_pooled_stampedLate (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    {k m : Nat} {v_0 : V}
    {a : NamedAttestation V} (hkm : k ≤ m) (hk1m : k + 1 ≤ m)
    (hcase : a.erase.confirmed ∈ M.round_votes (x[k][v_0].st).st.core a.erase ∨
      (a ∈ (x[k + 1][v_0].st).st.sg_rows a.round ∧
        (x[k + 1][v_0].st).st.core.timestamp_sg_vote (M.sgVote a.erase)
          = some (((x[k][v_0].st).st.core.t : Stamp)))) :
    M.sgVote a.erase ∈ (M.gradeView (M.toHealing (x[m][v_0].st).st.core)).sg_votes a.round ∧
      ∃ stamp : Int, stamp ≤ (x[k].time : Int) ∧
        (x[m][v_0].st).st.core.timestamp_sg_vote (M.sgVote a.erase)
          = some ((stamp : Stamp)) := by
  have ha_eround : a.erase.round = a.round := namedAttestation_erase_round a
  rcases hcase with hheld | ⟨h1, hstamp⟩
  · obtain ⟨c, hcpool, hcidx, hcconf⟩ :=
      (Restated.Vocabulary.Proofs.Optimistic.mem_round_votes facts).mp hheld
    have hpv := Restated.poolView_sts facts S Sched x k v_0 a.erase.round
    have hclist := (facts.sto.Sts_mem_sg_pool_iff _ _ c).mp hcpool
    rw [hpv] at hclist
    obtain ⟨B, hB, hBc⟩ := List.mem_map.mp hclist
    obtain ⟨hBround, stamp, hstampLe, hts⟩ :=
      (Restated.sgRowData_sts facts S Sched x k v_0).2 a.erase.round B hB
    have hBmem : B ∈ (x[k][v_0].st).st.sg_rows B.round := by rw [hBround]; exact hB
    have hsg : M.sgVote B.erase = M.sgVote a.erase := by
      rw [hBc]
      have hcround : c.round = a.erase.round := by
        rw [← hBc]; exact (namedAttestation_erase_round B).trans hBround
      exact facts.sto.sgVote_eq_of_fields hcidx hcround hcconf
    obtain ⟨hmem_m, hts_m⟩ := Restated.sgRow_stamp_mono_sts facts S Sched x v_0 hkm hBmem
    refine ⟨?_, stamp, hstampLe, ?_⟩
    · have hpool := Restated.sgRow_erase_mem_pool_sts facts S Sched x m v_0 B hmem_m
      rw [hBround, ha_eround] at hpool
      rw [← hsg, facts.gr.gradeView_sg_votes]
      exact Finset.mem_image_of_mem M.sgVote hpool
    · rw [← hsg, hts_m, hts]
  · obtain ⟨hmem_m, hts_m⟩ := Restated.sgRow_stamp_mono_sts facts S Sched x v_0 hk1m h1
    refine ⟨?_, (x[k][v_0].st).st.core.t, Restated.clock_le_time_sts facts S Sched x k v_0, ?_⟩
    · have hpool := Restated.sgRow_erase_mem_pool_sts facts S Sched x m v_0 a hmem_m
      rw [facts.gr.gradeView_sg_votes]
      exact Finset.mem_image_of_mem M.sgVote hpool
    · rw [hts_m, hstamp]

/-- With synchrony up to `S.a r + Δ`: if step `n` is the tick step at round `r`'s action instant,
    GST is at or before it, `m` is the last step before a phase instant of round `r + 1`, `v_0` is
    awake from `S.a r` to step `m` and not held at `S.a r`, and the ticks of `v_0` and `v_1` at step
    `n` have an outcome, then for every member `v_1` of `freshAttestersW S Sched x r m`, the SG-vote
    projection of every attestation `v_1`'s round-`r` action can compute is in every outcome of the
    raw inputs `v_0`'s grade view offers for round `r + 1` at the G2 early cutoff under `v_1`'s
    name. -/
theorem fresh_token_in_viewLate_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    {r : Round} (hsync : Restated.SynchronyFromWakeBefore M S x ((Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ)) (htd : Restated.TimeDiverges M x)
    (hunf : Restated.Unforgeability M S x)
    {n : Nat} (hn : Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S r))) (hgst : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S r))
    {m : Nat} {v_0 : V} {p : Protocol.Phase}
    (hm : Restated.stepBeforeInstant M x m (M.domain S.E S.hc (r + 1) p))
    (hawT : v_0 ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S r)) (x[m].time : Int))
    (hwh : v_0 ∉ Sched.adv ((Restated.Vocabulary.Execution.Setup.a M S r)))
    (hexp : (M.round_of S.hc (S.E.slotOf (x[m].time : Int))) ≤ r + S.hc.η_SG)
    (hroom : ∀ k : Nat, k < m → ∀ v_1 ∈ Restated.freshAttestersW M S Sched x r m,
      ∀ a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][v_1].st) v_1 r,
      x.lbl k = AtomicAction.deliver v_0 ⟨v_1, NamedObject.attest a⟩ →
      (M.round_votes (x[k][v_0].st).st.core a.erase).card ≠ 2)
    {v_1 : V} (hq : v_1 ∈ Restated.freshAttestersW M S Sched x r m)
    (hneTick : ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) v_0 (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S r) x[n] v_0)
        (Restated.Vocabulary.Execution.Setup.a M S r) ⇢ out)
    (hneAtt : ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) v_1 (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S r) x[n] v_1)
        (Restated.Vocabulary.Execution.Setup.a M S r) ⇢ out) :
    ∀ a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][v_1].st) v_1 r,
    ∀ X, M.rawInputs (M.gradeView (M.toHealing (x[m][v_0].st).st.core)) S.hc.η_SG (r + 1)
          (M.early S.E S.hc (r + 1) .g2) v_1 ⇢ X →
      M.sgVote a.erase ∈ X := by
  intro a ha X hX
  have hqW := hq
  have hq : v_1 ∈ Restated.freshAttesters M S Sched x r m := Restated.freshAttestersW_subset_freshAttesters facts S Sched x r m hq
  have ha_round : a.round = r :=
    Restated.actionAttestationFrom_round facts (Setup.alwaysAwake S) _ v_1 r a ha
  have ha_idx : a.val_index = v_1 :=
    Restated.actionAttestationFrom_val_index facts (Setup.alwaysAwake S) _ v_1 r a ha
  have hntime : (x[n].time : Int) = (Restated.Vocabulary.Execution.Setup.a M S r) - 1 := by
    have h := (Restated.tickStepAt_time facts x hn).2
    linarith only [h]
  have hpos : 0 < (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ := by
    linarith only [Restated.action_pos facts S r, S.E.Δ_pos]
  obtain ⟨k_1, hk_1⟩ := Restated.exists_tickStepAt facts x htd hpos
  obtain ⟨hk_1succ, hk_1self⟩ := Restated.tickStepAt_time facts x hk_1
  have hk_1m : k_1 < m := by
    by_contra hcon
    have h := hm.2 k_1 (Nat.le_of_not_lt hcon)
    rw [hk_1succ] at h
    exact absurd h (not_le_of_gt (Restated.action_delta_lt_domain_succ facts S r p))
  have hjm : k_1 + 1 ≤ m := Nat.succ_le_of_lt hk_1m
  have hjtime : (x[k_1 + 1].time : Int) ≤ (x[m].time : Int) := Restated.time_mono_int facts S Sched x hjm
  have hdpos := S.E.Δ_pos
  have hstart : (x[n].time : Int) ≤ (Restated.Vocabulary.Execution.Setup.a M S r) := by rw [hntime]; exact sub_le_self _ zero_le_one
  have hmaxle : max (x[n].time : Int) S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S r) := max_le hstart hgst
  have hlate : max (x[n].time : Int) S.E.t_GST + S.E.Δ ≤ (x[k_1 + 1].time : Int) := by
    rw [hk_1succ]; linarith only [hmaxle]
  have hnm : (x[n].time : Int) ≤ (x[m].time : Int) := by
    refine le_trans hstart (le_trans ?_ hjtime)
    rw [hk_1succ]; linarith only [hdpos]
  have haw : AtomicAwake x (k_1 + 1) v_0 := by
    refine mem_awake_of_awakeThroughout Sched hawT ?_ hjtime
    rw [hk_1succ]; linarith only [hdpos]
  have hwaw : v_0 ∈ Sched.awakeThroughout (x[n + 1].time : Int)
      (max (x[n].time : Int) S.E.t_GST + S.E.Δ) :=
    Restated.receiverWindowA_of_tick facts S x hn hgst
      (le_trans (by rw [hk_1succ]) hjtime) hawT
  have hv : HonestThroughTime Sched (x[k_1 + 1].time : Int) v_1 := fun t ht =>
    Restated.honestThrough_of_mem_freshAttesters facts hq t (le_trans ht hjtime)
  have hawT' : v_0 ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S a.round)) (x[k_1 + 1].time : Int) := by
    rw [ha_round]
    exact awakeThroughout_mono Sched hawT le_rfl hjtime
  have hsend : Restated.HonestSendAt M S x n (⟨v_1, NamedObject.attest a⟩
      : SignedMsg V (NamedObject V)) :=
    fresh_attest_honestSendLate facts S Sched x hn hq hnm
      (Restated.honestThrough_of_mem_freshAttesters facts hq _
        (le_trans (by rw [hk_1succ]; linarith only [hdpos]) hjtime)) hneAtt
      (awake_for_grade2_of_mem_freshAttestersWLate facts S Sched x hn hqW (fun t ht =>
        Restated.honestThrough_of_mem_freshAttesters facts hq t
          (le_trans ht (le_trans (by rw [hk_1succ]; linarith only [hdpos]) hjtime)))) a ha
  have hexp' : (M.round_of S.hc (S.E.slotOf (x[k_1 + 1].time : Int))) ≤ a.round + S.hc.η_SG := by
    rw [ha_round]
    exact le_trans (facts.gr.round_of_mono_sts S.hc (slotOf_mono_sts S hjtime)) hexp
  have hroom' : ∀ k : Nat, k < k_1 + 1 →
      x.lbl k = AtomicAction.deliver v_0 ⟨v_1, NamedObject.attest a⟩ →
      (M.round_votes (x[k][v_0].st).st.core a.erase).card ≠ 2 := by
    intro k hk hlbl
    exact hroom k (lt_of_lt_of_le hk hjm) v_1 hqW a ha hlbl
  have hsync' : Restated.SynchronyFromWakeBefore M S x
      (max (x[n].time : Int) S.E.t_GST + S.E.Δ) :=
    fun k w' sm hs hle haw' => hsync k w' sm hs (le_trans hle (by linarith only [hmaxle])) haw'
  obtain ⟨k, hkj, hlbl, hcase⟩ :=
    Restated.attest_recorded_of_honestSend_awake_succ_upTo facts S Sched x
      hsync' hsend hlate haw hwaw hv hunf ha_idx
      hawT'
      (by rw [ha_round]; exact hwh) hexp' hroom'
      (fun n' hn' => by
        rw [ha_round] at hn' ⊢
        rw [Restated.tickStepAt_unique facts x hn' hn]
        exact hneTick)
      (fun k _ _ => facts.nd.process_nonempty _ _ _ (fun _ h => by cases h))
  have hkm : k ≤ m := le_trans (le_of_lt hkj) hjm
  have hk1m : k + 1 ≤ m := le_trans (Nat.succ_le_of_lt hkj) hjm
  have hkt : (x[k].time : Int) ≤ (x[k_1].time : Int) :=
    Restated.time_mono_int facts S Sched x (Nat.le_of_lt_succ hkj)
  have hkstrict : (x[k].time : Int) < (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ := by
    linarith only [hkt, hk_1self]
  have hcut : (x[k].time : Int) < M.early S.E S.hc (r + 1) .g2 :=
    lt_of_lt_of_le hkstrict (Restated.action_delta_le_early_succ facts S r)
  have hkey := fresh_token_pooled_stampedLate facts S Sched x hkm hk1m
    (hcase.imp id (fun h => ⟨h.1, h.2.2⟩))
  rw [ha_round] at hkey
  obtain ⟨hmem, stamp, hstampLe, hts⟩ := hkey
  refine facts.gr.mem_rawInputs_of_stamp _ _ _ r _ _ (Restated.mem_latest_window_self_succ facts S r) hmem ?_ ?_
    (lt_of_le_of_lt hstampLe hcut) X hX
  · rw [facts.sto.sgVote_val]
    exact ha_idx
  · rw [facts.gr.gradeView_timestamp_sg_vote]
    exact hts

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Under the hypotheses of `fresh_token_in_viewLate_upTo`, if the block each member's attestation
    names resolves in `v_0`'s tree, stamped before the phase's late cutoff and compatible with
    `v_0`'s finalized block, then the token of every attestation `v_1`'s round-`r` action can
    compute is in every outcome of the tokens `v_0`'s grade view counts as evidence-ready for round
    `r + 1` at the phase's late cutoff under `v_1`'s name. -/
theorem fresh_token_readyLate_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    {r : Round} (hsync : Restated.SynchronyFromWakeBefore M S x ((Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ)) (htd : Restated.TimeDiverges M x)
    (hunf : Restated.Unforgeability M S x)
    {n : Nat} (hn : Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S r))) (hgst : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S r))
    {m : Nat} {v_0 : V} {p : Protocol.Phase}
    (hm : Restated.stepBeforeInstant M x m (M.domain S.E S.hc (r + 1) p))
    (hawT : v_0 ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S r)) (x[m].time : Int))
    (hwh : v_0 ∉ Sched.adv ((Restated.Vocabulary.Execution.Setup.a M S r)))
    (hexp : (M.round_of S.hc (S.E.slotOf (x[m].time : Int))) ≤ r + S.hc.η_SG)
    (hroom : ∀ k : Nat, k < m → ∀ v_1 ∈ Restated.freshAttestersW M S Sched x r m,
      ∀ a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][v_1].st) v_1 r,
      x.lbl k = AtomicAction.deliver v_0 ⟨v_1, NamedObject.attest a⟩ →
      (M.round_votes (x[k][v_0].st).st.core a.erase).card ≠ 2)
    (hheads : ∀ v_1 ∈ Restated.freshAttestersW M S Sched x r m,
      ∀ a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][v_1].st) v_1 r,
      ∀ C : NamedBlock V, C ∈ (x[n + 1][v_1].st).st.bodies →
      a.confirmed = some C.root →
      Block.find? (x[m][v_0].st).st.core.T C.root = some C.erase ∧
      stampedBefore (x[m][v_0].st).st.core.timestamp_block
        (M.late S.E S.hc (r + 1) p) C.erase = true ∧
      Block.compatible C.erase (x[m][v_0].st).st.core.F = true)
    (hhead_mem : ∀ v_1 ∈ Restated.freshAttestersW M S Sched x r m,
      ∀ a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][v_1].st) v_1 r,
      ∀ root : BlockId, a.confirmed = some root →
      ∃ C : NamedBlock V, C ∈ (x[n + 1][v_1].st).st.bodies ∧ C.root = root)
    {v_1 : V} (hq : v_1 ∈ Restated.freshAttestersW M S Sched x r m)
    (hneTick : ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) v_0 (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S r) x[n] v_0)
        (Restated.Vocabulary.Execution.Setup.a M S r) ⇢ out)
    (hneAtt : ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) v_1 (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S r) x[n] v_1)
        (Restated.Vocabulary.Execution.Setup.a M S r) ⇢ out) :
    ∀ a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][v_1].st) v_1 r,
    ∀ Y, M.readyView (M.gradeView (M.toHealing (x[m][v_0].st).st.core))
          (x[m][v_0].st).st.core.F S.hc.η_SG (r + 1)
          (M.late S.E S.hc (r + 1) p) v_1 ⇢ Y →
      M.token (M.sgVote a.erase) ∈ Y := by
  intro a ha Y hY
  obtain ⟨X, hX⟩ := facts.gr.rawInputs_nonempty (M.gradeView (M.toHealing (x[m][v_0].st).st.core))
    S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) .g2) v_1
  obtain ⟨X', hX'⟩ := facts.gr.rawInputs_nonempty (M.gradeView (M.toHealing (x[m][v_0].st).st.core))
    S.hc.η_SG (r + 1) (M.late S.E S.hc (r + 1) p) v_1
  have hraw2 := Restated.fresh_token_in_viewLate_upTo facts S Sched x hsync htd hunf hn hgst hm
    hawT hwh hexp hroom hq hneTick hneAtt a ha X hX
  have hraw := facts.gr.rawInputs_mono
    (M.gradeView (M.toHealing (x[m][v_0].st).st.core)) S.hc.η_SG (r + 1)
    (le_trans (Restated.early_g2_le_early facts S (r + 1) p)
      (facts.gr.early_le_late S.E S.hc (r + 1) p)) v_1 X hX X' hX' hraw2
  have hconf : (M.sgVote a.erase).confirmed = a.confirmed := facts.sto.sgVote_confirmed a
  obtain ⟨b, hb⟩ := facts.gr.bodyReady_nonempty (M.gradeView (M.toHealing (x[m][v_0].st).st.core))
    (x[m][v_0].st).st.core.F (M.late S.E S.hc (r + 1) p) (M.sgVote a.erase)
  have hready : b = true := by
    cases hc : a.confirmed with
    | none => exact facts.gr.bodyReady_of_no_head _ _ _ _ (hconf.trans hc) b hb
    | some root =>
        obtain ⟨C, hCbody, hCroot⟩ := hhead_mem v_1 hq a ha root hc
        obtain ⟨hfind, hstamped, hcompat⟩ := hheads v_1 hq a ha C hCbody (by rw [hc, hCroot])
        refine facts.gr.bodyReady_of_head _ _ _ _ (hconf.trans hc) ?_
          (by rw [facts.gr.gradeView_timestamp_block]; exact hstamped) hcompat b hb
        rw [← hCroot, facts.gr.Sts_gradeView_T]; exact hfind
  exact facts.gr.token_mem_readyView _ _ _ _ _ _ X' hX' hraw b hb hready Y hY

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If `B` is an ancestor of no body of `v_1` after step `n` that `a` names, and that body resolves
    in `v_0`'s tree, then no outcome of the test whether the head `a` names covers `B` in `v_0`'s
    grade view is `true`. -/
private theorem fresh_not_headCoversLate (facts : Record.Facts M) {S : Setup V}
    {Sched : Schedule V} (x : AtomicExec (Record.protocolOf M S) Sched) {n m : Nat} {v_0 v_1 : V}
    {a : NamedAttestation V}
    (hfind : ∀ C : NamedBlock V, C ∈ (x[n + 1][v_1].st).st.bodies →
      a.confirmed = some C.root →
      Block.find? (x[m][v_0].st).st.core.T C.root = some C.erase)
    (hhead_mem : ∀ root : BlockId, a.confirmed = some root →
      ∃ C : NamedBlock V, C ∈ (x[n + 1][v_1].st).st.bodies ∧ C.root = root)
    {B : Block V}
    (hnot : ∀ C : NamedBlock V, C ∈ (x[n + 1][v_1].st).st.bodies →
      a.confirmed = some C.root → ¬ Block.Preceq B C.erase) :
    ∀ b, M.head_covers (M.gradeView (M.toHealing (x[m][v_0].st).st.core)).T B a.confirmed ⇢ b →
      ¬ b = true := by
  intro b hb hcover
  obtain ⟨root, head, hkey, hfindh, -, hpreceq⟩ :=
    facts.gr.exists_head_of_head_covers b hb hcover
  obtain ⟨C, hCbody, hCroot⟩ := hhead_mem root hkey
  have hconfC : a.confirmed = some C.root := by rw [hkey, hCroot]
  have hfindC' : Block.find? (x[m][v_0].st).st.core.T root = some C.erase := by
    rw [← hCroot]; exact hfind C hCbody hconfC
  rw [facts.gr.Sts_gradeView_T] at hfindh
  have hhead : head = C.erase := Option.some.inj (hfindh.symm.trans hfindC')
  exact hnot C hCbody hconfC (by rw [← hhead]; exact preceq_eq_true_iff_Preceq.1 hpreceq)

/-- Under the hypotheses of `fresh_token_readyLate_upTo`, if `B` is an ancestor of none of the
    bodies of `v_1` after the round's tick that its round-`r` attestations name, then no outcome of
    the test whether `v_1` is a positive supporter of `B` at `v_0`'s store is `true`. -/
theorem fresh_not_positiveLate_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {r : Round} (hsync : Restated.SynchronyFromWakeBefore M S x ((Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ)) (htd : Restated.TimeDiverges M x)
    {n : Nat} (hn : Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S r))) (hgst : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S r))
    {m : Nat} {v_0 : V} {p : Protocol.Phase}
    (hm : Restated.stepBeforeInstant M x m (M.domain S.E S.hc (r + 1) p))
    (hawT : v_0 ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S r)) (x[m].time : Int))
    (hwh : v_0 ∉ Sched.adv ((Restated.Vocabulary.Execution.Setup.a M S r)))
    (hexp : (M.round_of S.hc (S.E.slotOf (x[m].time : Int))) ≤ r + S.hc.η_SG)
    (hroom : ∀ k : Nat, k < m → ∀ v_1 ∈ Restated.freshAttestersW M S Sched x r m,
      ∀ a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][v_1].st) v_1 r,
      x.lbl k = AtomicAction.deliver v_0 ⟨v_1, NamedObject.attest a⟩ →
      (M.round_votes (x[k][v_0].st).st.core a.erase).card ≠ 2)
    (hheads : ∀ v_1 ∈ Restated.freshAttestersW M S Sched x r m,
      ∀ a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][v_1].st) v_1 r,
      ∀ C : NamedBlock V, C ∈ (x[n + 1][v_1].st).st.bodies →
      a.confirmed = some C.root →
      Block.find? (x[m][v_0].st).st.core.T C.root = some C.erase ∧
      stampedBefore (x[m][v_0].st).st.core.timestamp_block
        (M.late S.E S.hc (r + 1) p) C.erase = true ∧
      Block.compatible C.erase (x[m][v_0].st).st.core.F = true)
    (hhead_mem : ∀ v_1 ∈ Restated.freshAttestersW M S Sched x r m,
      ∀ a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][v_1].st) v_1 r,
      ∀ root : BlockId, a.confirmed = some root →
      ∃ C : NamedBlock V, C ∈ (x[n + 1][v_1].st).st.bodies ∧ C.root = root)
    {B : Block V} {v_1 : V} (hq : v_1 ∈ Restated.freshAttestersW M S Sched x r m)
    (hnot : ∀ a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][v_1].st) v_1 r,
      ∀ C : NamedBlock V, C ∈ (x[n + 1][v_1].st).st.bodies →
      a.confirmed = some C.root → ¬ Block.Preceq B C.erase)
    (hneTick : ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) v_0 (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S r) x[n] v_0)
        (Restated.Vocabulary.Execution.Setup.a M S r) ⇢ out)
    (hneAtt : ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) v_1 (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S r) x[n] v_1)
        (Restated.Vocabulary.Execution.Setup.a M S r) ⇢ out) :
    ∀ b, M.positive (M.gradeView (M.toHealing (x[m][v_0].st).st.core)) (x[m][v_0].st).st.core.F
        S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) p)
        (M.late S.E S.hc (r + 1) p) v_1 B ⇢ b → ¬ b = true := by
  intro b hb hpos
  obtain ⟨a, ha⟩ := actionAttestationFrom_nonemptyLate facts (Setup.alwaysAwake S) (x[n][v_1].st) v_1 r
  obtain ⟨Re, hRe⟩ := facts.gr.readyView_nonempty (M.gradeView (M.toHealing (x[m][v_0].st).st.core))
    (x[m][v_0].st).st.core.F S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) p) v_1
  obtain ⟨Rl, hRl⟩ := facts.gr.readyView_nonempty (M.gradeView (M.toHealing (x[m][v_0].st).st.core))
    (x[m][v_0].st).st.core.F S.hc.η_SG (r + 1) (M.late S.E S.hc (r + 1) p) v_1
  obtain ⟨Wl, hWl⟩ := facts.gr.rawView_nonempty (M.gradeView (M.toHealing (x[m][v_0].st).st.core))
    S.hc.η_SG (r + 1) (M.late S.E S.hc (r + 1) p) v_1
  obtain ⟨We, hWe⟩ := facts.gr.rawView_nonempty (M.gradeView (M.toHealing (x[m][v_0].st).st.core))
    S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) p) v_1
  have hcovf : ∀ k, M.head_covers (M.gradeView (M.toHealing (x[m][v_0].st).st.core)).T B k ⇢
      (fun k => (facts.gr.head_covers_nonempty
        (M.gradeView (M.toHealing (x[m][v_0].st).st.core)).T B k).choose) k :=
    fun k => (facts.gr.head_covers_nonempty
      (M.gradeView (M.toHealing (x[m][v_0].st).st.core)).T B k).choose_spec
  obtain ⟨tok, htok, -, hcover, -, hnewer⟩ := facts.gr.conditions_of_positive _ _ _ _ _ _ _ _ b hb
    hpos Re hRe Rl hRl Wl hWl _ hcovf
  have hnc := fresh_not_headCoversLate facts x (m := m) (v_0 := v_0)
    (fun C hC hc => (hheads v_1 hq a ha C hC hc).1) (hhead_mem v_1 hq a ha) (hnot a ha)
  have hown := Restated.fresh_token_readyLate_upTo facts S Sched x hsync htd
    hexec.toUnforgeability hn hgst hm hawT hwh hexp hroom hheads hhead_mem hq hneTick hneAtt a ha
    Rl hRl
  have hownround : (M.token (M.sgVote a.erase)).round = r := by
    rw [facts.gr.token_round, facts.sto.sgVote_round_eq_round, namedAttestation_erase_round]
    exact Restated.actionAttestationFrom_round facts (Setup.alwaysAwake S) _ v_1 r a ha
  have htokW : tok ∈ We := facts.gr.readyView_subset_rawView _ _ _ _ _ _ Re hRe We hWe htok
  have hhigh : tok.round ≤ r :=
    Restated.rawView_round_le facts S Sched x m v_0 r (M.early S.E S.hc (r + 1) p) v_1 We hWe tok htokW
  rcases Nat.lt_or_eq_of_le hhigh with hlt | htokround
  ·
    have hcov := hnewer _ hown (by rw [hownround]; exact hlt)
    rw [facts.gr.token_key, facts.sto.sgVote_confirmed] at hcov
    exact hnc _ (hcovf a.confirmed) hcov
  ·
    obtain ⟨R, hR⟩ := facts.gr.rawInputs_nonempty (M.gradeView (M.toHealing (x[m][v_0].st).st.core))
      S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) p) v_1
    obtain ⟨y, hyraw, hytok⟩ := facts.gr.exists_rawInputs_of_mem_rawView We hWe htokW R hR
    obtain ⟨⟨k, -, hyk⟩, hyidx, -⟩ := facts.gr.rawInputs_mem_window _ _ _ _ _ R hR hyraw
    have hykround : y.round = k := Restated.sgVotesRoundIndexed_sts facts S Sched x m v_0 k y hyk
    have hyround : y.round = r := by rw [← htokround, ← hytok, facts.gr.token_round]
    have hymem : y ∈ (M.gradeView (M.toHealing (x[m][v_0].st).st.core)).sg_votes y.round := by
      rw [hykround]; exact hyk
    obtain ⟨n', htick', -, hyeq⟩ := Restated.token_of_honest_sender facts S Sched x hexec
      (Restated.honestThrough_of_mem_freshAttestersW facts hq) hymem hyidx
    rw [hyround] at htick' hyeq
    have hnn : n' = n := Restated.tickStepAt_unique facts x htick' hn
    rw [hnn] at hyeq
    have hkey : tok.key = a.confirmed := by
      rw [← hytok, hyeq a ha, facts.gr.token_key, facts.sto.sgVote_confirmed]
    exact hnc _ (hcovf a.confirmed) (by rw [← hkey]; exact hcover)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Under the hypotheses of `fresh_token_readyLate_upTo`, if `B` is an ancestor of none of the
    bodies of `v_1` after the round's tick that its round-`r` attestations name, then every outcome
    of the test whether `v_1` is an opposer of `B` at `v_0`'s store is `true`. -/
theorem fresh_opposesLate_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    {r : Round} (hsync : Restated.SynchronyFromWakeBefore M S x ((Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ)) (htd : Restated.TimeDiverges M x) (hunf : Restated.Unforgeability M S x)
    {n : Nat} (hn : Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S r))) (hgst : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S r))
    {m : Nat} {v_0 : V} {p : Protocol.Phase}
    (hm : Restated.stepBeforeInstant M x m (M.domain S.E S.hc (r + 1) p))
    (hawT : v_0 ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S r)) (x[m].time : Int))
    (hwh : v_0 ∉ Sched.adv ((Restated.Vocabulary.Execution.Setup.a M S r)))
    (hexp : (M.round_of S.hc (S.E.slotOf (x[m].time : Int))) ≤ r + S.hc.η_SG)
    (hroom : ∀ k : Nat, k < m → ∀ v_1 ∈ Restated.freshAttestersW M S Sched x r m,
      ∀ a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][v_1].st) v_1 r,
      x.lbl k = AtomicAction.deliver v_0 ⟨v_1, NamedObject.attest a⟩ →
      (M.round_votes (x[k][v_0].st).st.core a.erase).card ≠ 2)
    (hheads : ∀ v_1 ∈ Restated.freshAttestersW M S Sched x r m,
      ∀ a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][v_1].st) v_1 r,
      ∀ C : NamedBlock V, C ∈ (x[n + 1][v_1].st).st.bodies →
      a.confirmed = some C.root →
      Block.find? (x[m][v_0].st).st.core.T C.root = some C.erase ∧
      stampedBefore (x[m][v_0].st).st.core.timestamp_block
        (M.late S.E S.hc (r + 1) p) C.erase = true ∧
      Block.compatible C.erase (x[m][v_0].st).st.core.F = true)
    (hhead_mem : ∀ v_1 ∈ Restated.freshAttestersW M S Sched x r m,
      ∀ a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][v_1].st) v_1 r,
      ∀ root : BlockId, a.confirmed = some root →
      ∃ C : NamedBlock V, C ∈ (x[n + 1][v_1].st).st.bodies ∧ C.root = root)
    {B : Block V} {v_1 : V} (hq : v_1 ∈ Restated.freshAttestersW M S Sched x r m)
    (hnot : ∀ a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][v_1].st) v_1 r,
      ∀ C : NamedBlock V, C ∈ (x[n + 1][v_1].st).st.bodies →
      a.confirmed = some C.root → ¬ Block.Preceq B C.erase)
    (hneTick : ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) v_0 (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S r) x[n] v_0)
        (Restated.Vocabulary.Execution.Setup.a M S r) ⇢ out)
    (hneAtt : ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) v_1 (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S r) x[n] v_1)
        (Restated.Vocabulary.Execution.Setup.a M S r) ⇢ out) :
    ∀ o, M.opposing (M.gradeView (M.toHealing (x[m][v_0].st).st.core)) (x[m][v_0].st).st.core.F
      S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) p)
      (M.late S.E S.hc (r + 1) p) v_1 B ⇢ o → o = true := by
  intro o ho
  obtain ⟨a, ha⟩ := actionAttestationFrom_nonemptyLate facts (Setup.alwaysAwake S) (x[n][v_1].st) v_1 r
  obtain ⟨Re, hRe⟩ := facts.gr.readyView_nonempty (M.gradeView (M.toHealing (x[m][v_0].st).st.core))
    (x[m][v_0].st).st.core.F S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) p) v_1
  obtain ⟨Rl, hRl⟩ := facts.gr.readyView_nonempty (M.gradeView (M.toHealing (x[m][v_0].st).st.core))
    (x[m][v_0].st).st.core.F S.hc.η_SG (r + 1) (M.late S.E S.hc (r + 1) p) v_1
  obtain ⟨We, hWe⟩ := facts.gr.rawView_nonempty (M.gradeView (M.toHealing (x[m][v_0].st).st.core))
    S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) p) v_1
  have hown := Restated.fresh_token_readyLate_upTo facts S Sched x hsync htd hunf hn hgst hm
    hawT hwh hexp hroom hheads hhead_mem hq hneTick hneAtt a ha Rl hRl
  have hownround : (M.token (M.sgVote a.erase)).round = r := by
    rw [facts.gr.token_round, facts.sto.sgVote_round_eq_round, namedAttestation_erase_round]
    exact Restated.actionAttestationFrom_round facts (Setup.alwaysAwake S) _ v_1 r a ha
  have hk : (M.token (M.sgVote a.erase)).key = a.confirmed := by
    rw [facts.gr.token_key, facts.sto.sgVote_confirmed]
  obtain ⟨b, hb⟩ := facts.gr.head_covers_nonempty
    (M.gradeView (M.toHealing (x[m][v_0].st).st.core)).T B (M.token (M.sgVote a.erase)).key
  refine facts.gr.opposing_of_late_not_covers _ _ _ _ _ _ _ _ Rl hRl hown Re hRe ?_ b hb ?_ o ho
  · intro y hy
    rw [hownround]
    exact Restated.rawView_round_le facts S Sched x m v_0 r (M.early S.E S.hc (r + 1) p) v_1 We hWe y
      (facts.gr.readyView_subset_rawView _ _ _ _ _ _ Re hRe We hWe hy)
  · rw [hk] at hb
    exact fresh_not_headCoversLate facts x (m := m) (v_0 := v_0)
      (fun C hC hc => (hheads v_1 hq a ha C hC hc).1) (hhead_mem v_1 hq a ha) (hnot a ha) b hb

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Under the hypotheses of `fresh_token_readyLate_upTo`, if the validators holding a late raw
    token, other than the members of `freshAttestersW S Sched x r m`, weigh strictly less than those
    members, and `v_0`'s store can grade `B` at least 1 for round `r + 1` at the phase, then `B` is
    an ancestor of a body `C` of some member `v_1` after the round's tick, named by every
    attestation `v_1`'s round-`r` action can compute. -/
theorem graded_preceq_freshSG_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {r : Round} (hsync : Restated.SynchronyFromWakeBefore M S x ((Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ)) (htd : Restated.TimeDiverges M x)
    {n : Nat} (hn : Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S r))) (hgst : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S r))
    {m : Nat} {v_0 : V} {p : Protocol.Phase}
    (hm : Restated.stepBeforeInstant M x m (M.domain S.E S.hc (r + 1) p))
    (hawT : v_0 ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S r)) (x[m].time : Int))
    (hwh : v_0 ∉ Sched.adv ((Restated.Vocabulary.Execution.Setup.a M S r)))
    (hexp : (M.round_of S.hc (S.E.slotOf (x[m].time : Int))) ≤ r + S.hc.η_SG)
    (hroom : ∀ k : Nat, k < m → ∀ v_1 ∈ Restated.freshAttestersW M S Sched x r m,
      ∀ a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][v_1].st) v_1 r,
      x.lbl k = AtomicAction.deliver v_0 ⟨v_1, NamedObject.attest a⟩ →
      (M.round_votes (x[k][v_0].st).st.core a.erase).card ≠ 2)
    (hheads : ∀ v_1 ∈ Restated.freshAttestersW M S Sched x r m,
      ∀ a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][v_1].st) v_1 r,
      ∀ C : NamedBlock V, C ∈ (x[n + 1][v_1].st).st.bodies →
      a.confirmed = some C.root →
      Block.find? (x[m][v_0].st).st.core.T C.root = some C.erase ∧
      stampedBefore (x[m][v_0].st).st.core.timestamp_block
        (M.late S.E S.hc (r + 1) p) C.erase = true ∧
      Block.compatible C.erase (x[m][v_0].st).st.core.F = true)
    (hhead_mem : ∀ v_1 ∈ Restated.freshAttestersW M S Sched x r m,
      ∀ a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][v_1].st) v_1 r,
      ∀ root : BlockId, a.confirmed = some root →
      ∃ C : NamedBlock V, C ∈ (x[n + 1][v_1].st).st.bodies ∧ C.root = root)
    (hhalf : ∀ raw : V → Finset (Protocol.Token (Option BlockId)),
      (∀ u, M.rawView (M.gradeView (M.toHealing (x[m][v_0].st).st.core)) S.hc.η_SG (r + 1)
        (M.late S.E S.hc (r + 1) p) u ⇢ raw u) →
      S.E.electorate.weightOf
        ((Finset.univ.filter (fun v_1 => (raw v_1).Nonempty))
          \ Restated.freshAttestersW M S Sched x r m)
      < S.E.electorate.weightOf (Restated.freshAttestersW M S Sched x r m))
    (B : Block V)
    (hgrade : M.gradeBool S.E (M.gradeView (M.toHealing (x[m][v_0].st).st.core))
      (x[m][v_0].st).st.core.F S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) p)
      (M.late S.E S.hc (r + 1) p) B ⇢ true)
    (hneTick : ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) v_0 (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S r) x[n] v_0)
        (Restated.Vocabulary.Execution.Setup.a M S r) ⇢ out)
    (hneAtt : ∀ v_1 ∈ Restated.freshAttestersW M S Sched x r m,
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) v_1 (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S r) x[n] v_1)
          (Restated.Vocabulary.Execution.Setup.a M S r) ⇢ out) :
    ∃ v_1 ∈ Restated.freshAttestersW M S Sched x r m, ∃ C : NamedBlock V,
      C ∈ (x[n + 1][v_1].st).st.bodies ∧
      (∀ a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][v_1].st) v_1 r,
        a.confirmed = some C.root) ∧
      Block.Preceq B C.erase := by
  have _hr_0 : M.reachedNode (x[m][v_0].st) := Record.reachedNode_sts facts S Sched x m v_0
  classical
  by_contra hcon
  have hnot : ∀ v_1 ∈ Restated.freshAttestersW M S Sched x r m,
      ∀ a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][v_1].st) v_1 r,
      ∀ C : NamedBlock V, C ∈ (x[n + 1][v_1].st).st.bodies →
      a.confirmed = some C.root → ¬ Block.Preceq B C.erase := by
    intro v_1 hv_1 a ha C hC hc hBC
    refine hcon ⟨v_1, hv_1, C, hC, fun a' ha' => ?_, hBC⟩
    have _hr_s3 := Record.reachedNode_wakeStage facts S Sched x (n) v_1 (Restated.Vocabulary.Execution.Setup.a M S r)
    have _hv_s3 := Record.runs_as_wakeStage facts S Sched x (n) v_1 (Restated.Vocabulary.Execution.Setup.a M S r)
    have hu := actionAttestationFrom_uniqueLate facts S v_1 _ r (hneAtt v_1 hv_1)
      (awake_for_grade2_of_mem_freshAttestersWLate facts S Sched x hn hv_1 (fun t ht =>
        Restated.honestThrough_of_mem_freshAttestersW facts hv_1 t
          (le_trans ht (Restated.action_le_time_of_stepBefore facts S Sched x htd hm))))
      (by rw [actionAttestationFrom_wakeStageLate facts]; exact ha')
      (by rw [actionAttestationFrom_wakeStageLate facts]; exact ha)
    rw [hu]
    exact hc
  have hposf : ∀ u, M.positive (M.gradeView (M.toHealing (x[m][v_0].st).st.core))
      (x[m][v_0].st).st.core.F S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) p)
      (M.late S.E S.hc (r + 1) p) u B ⇢
      (fun u => (facts.gr.positive_nonempty (M.gradeView (M.toHealing (x[m][v_0].st).st.core))
        (x[m][v_0].st).st.core.F S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) p)
        (M.late S.E S.hc (r + 1) p) u B).choose) u :=
    fun u => (facts.gr.positive_nonempty _ _ _ _ _ _ u B).choose_spec
  have hoppf : ∀ u, M.opposing (M.gradeView (M.toHealing (x[m][v_0].st).st.core))
      (x[m][v_0].st).st.core.F S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) p)
      (M.late S.E S.hc (r + 1) p) u B ⇢
      (fun u => (facts.gr.opposing_nonempty (M.gradeView (M.toHealing (x[m][v_0].st).st.core))
        (x[m][v_0].st).st.core.F S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) p)
        (M.late S.E S.hc (r + 1) p) u B).choose) u :=
    fun u => (facts.gr.opposing_nonempty _ _ _ _ _ _ u B).choose_spec
  have hrawf : ∀ u, M.rawView (M.gradeView (M.toHealing (x[m][v_0].st).st.core)) S.hc.η_SG (r + 1)
      (M.late S.E S.hc (r + 1) p) u ⇢
      (fun u => (facts.gr.rawView_nonempty (M.gradeView (M.toHealing (x[m][v_0].st).st.core))
        S.hc.η_SG (r + 1) (M.late S.E S.hc (r + 1) p) u).choose) u :=
    fun u => (facts.gr.rawView_nonempty _ _ _ _ u).choose_spec
  set pos := fun u => (facts.gr.positive_nonempty (M.gradeView (M.toHealing (x[m][v_0].st).st.core))
    (x[m][v_0].st).st.core.F S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) p)
    (M.late S.E S.hc (r + 1) p) u B).choose with hpos_def
  set opp := fun u => (facts.gr.opposing_nonempty (M.gradeView (M.toHealing (x[m][v_0].st).st.core))
    (x[m][v_0].st).st.core.F S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) p)
    (M.late S.E S.hc (r + 1) p) u B).choose with hopp_def
  set raw := fun u => (facts.gr.rawView_nonempty (M.gradeView (M.toHealing (x[m][v_0].st).st.core))
    S.hc.η_SG (r + 1) (M.late S.E S.hc (r + 1) p) u).choose with hraw_def
  have hopp : Restated.freshAttestersW M S Sched x r m ⊆ Finset.univ.filter
      (fun v => opp v = true) := by
    intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ v,
      Restated.fresh_opposesLate_upTo facts S Sched x hsync htd hexec.toUnforgeability hn hgst
        hm hawT hwh hexp hroom hheads hhead_mem hv (hnot v hv) hneTick (hneAtt v hv) (opp v)
        (hoppf v)⟩
  have hposS : Finset.univ.filter (fun v => pos v = true)
      ⊆ (Finset.univ.filter (fun v_1 => (raw v_1).Nonempty))
          \ Restated.freshAttestersW M S Sched x r m := by
    intro v hv
    have hpv : pos v = true := (Finset.mem_filter.mp hv).2
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ v, ?_⟩, ?_⟩
    · obtain ⟨Re, hRe⟩ := facts.gr.readyView_nonempty (M.gradeView (M.toHealing (x[m][v_0].st).st.core))
        (x[m][v_0].st).st.core.F S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) p) v
      obtain ⟨Rl, hRl⟩ := facts.gr.readyView_nonempty (M.gradeView (M.toHealing (x[m][v_0].st).st.core))
        (x[m][v_0].st).st.core.F S.hc.η_SG (r + 1) (M.late S.E S.hc (r + 1) p) v
      obtain ⟨We, hWe⟩ := facts.gr.rawView_nonempty (M.gradeView (M.toHealing (x[m][v_0].st).st.core))
        S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) p) v
      obtain ⟨tok, htok, -⟩ := facts.gr.conditions_of_positive _ _ _ _ _ _ _ _ (pos v) (hposf v)
        hpv Re hRe Rl hRl (raw v) (hrawf v) _
        (fun k => (facts.gr.head_covers_nonempty
          (M.gradeView (M.toHealing (x[m][v_0].st).st.core)).T B k).choose_spec)
      refine ⟨tok, ?_⟩
      exact facts.gr.rawView_mono _ _ _
        (facts.gr.early_le_late S.E S.hc (r + 1) p) v We hWe (raw v) (hrawf v)
        (facts.gr.readyView_subset_rawView _ _ _ _ _ _ Re hRe We hWe htok)
    · intro hfresh
      exact Restated.fresh_not_positiveLate_upTo facts S Sched x hexec hsync htd hn hgst hm
        hawT hwh hexp hroom hheads hhead_mem hfresh (hnot v hfresh) hneTick (hneAtt v hfresh)
        (pos v) (hposf v) hpv
  have h_1 := S.E.electorate.weightOf_mono hopp
  have h_2 := S.E.electorate.weightOf_mono hposS
  have h_3 := hhalf raw hrawf
  have hfalse := facts.gr.gradeBool_eq_false_of_weight_le _ _ _ _ _ _ _ _ pos hposf opp hoppf
    (by omega) true hgrade
  exact absurd hfalse (by decide)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If every round-`r` SG block of a member of `H` is compatible with the anchor, every member of
    `freshAttestersW S Sched x r m` is in `H`, and the hypotheses of `graded_preceq_freshSG_upTo`
    hold, then every block `v_0`'s store can grade at least 1 for round `r + 1` at that phase is
    compatible with the anchor. -/
theorem grade1_of_sg_prevLate_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {r : Round} (hsync : Restated.SynchronyFromWakeBefore M S x ((Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ)) (htd : Restated.TimeDiverges M x)
    {n : Nat} {T : NamedBlock V} (hn : Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S r)))
    (hgst : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S r)) (H : Finset V)
    (hsg : ∀ v ∈ H, ∀ a : NamedAttestation V,
      a.round = r → a.val_index = v →
      (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n + 1].sent →
      ∀ C : NamedBlock V, C ∈ (x[n + 1][v].st).st.bodies → a.confirmed = some C.root →
      Block.compatible C.erase T.erase = true)
    {m : Nat} {v_0 : V} {p : Protocol.Phase}
    (hm : Restated.stepBeforeInstant M x m (M.domain S.E S.hc (r + 1) p))
    (hfreshH : Restated.freshAttestersW M S Sched x r m ⊆ H)
    (hawT : v_0 ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S r)) (x[m].time : Int))
    (hwh : v_0 ∉ Sched.adv ((Restated.Vocabulary.Execution.Setup.a M S r)))
    (hexp : (M.round_of S.hc (S.E.slotOf (x[m].time : Int))) ≤ r + S.hc.η_SG)
    (hroom : ∀ k : Nat, k < m → ∀ v_1 ∈ Restated.freshAttestersW M S Sched x r m,
      ∀ a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][v_1].st) v_1 r,
      x.lbl k = AtomicAction.deliver v_0 ⟨v_1, NamedObject.attest a⟩ →
      (M.round_votes (x[k][v_0].st).st.core a.erase).card ≠ 2)
    (hheads : ∀ v_1 ∈ Restated.freshAttestersW M S Sched x r m,
      ∀ a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][v_1].st) v_1 r,
      ∀ C : NamedBlock V, C ∈ (x[n + 1][v_1].st).st.bodies →
      a.confirmed = some C.root →
      Block.find? (x[m][v_0].st).st.core.T C.root = some C.erase ∧
      stampedBefore (x[m][v_0].st).st.core.timestamp_block
        (M.late S.E S.hc (r + 1) p) C.erase = true ∧
      Block.compatible C.erase (x[m][v_0].st).st.core.F = true)
    (hhead_mem : ∀ v_1 ∈ Restated.freshAttestersW M S Sched x r m,
      ∀ a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][v_1].st) v_1 r,
      ∀ root : BlockId, a.confirmed = some root →
      ∃ C : NamedBlock V, C ∈ (x[n + 1][v_1].st).st.bodies ∧ C.root = root)
    (hhalf : ∀ raw : V → Finset (Protocol.Token (Option BlockId)),
      (∀ u, M.rawView (M.gradeView (M.toHealing (x[m][v_0].st).st.core)) S.hc.η_SG (r + 1)
        (M.late S.E S.hc (r + 1) p) u ⇢ raw u) →
      S.E.electorate.weightOf
        ((Finset.univ.filter (fun v_1 => (raw v_1).Nonempty))
          \ Restated.freshAttestersW M S Sched x r m)
      < S.E.electorate.weightOf (Restated.freshAttestersW M S Sched x r m))
    (B : Block V)
    (hgrade : M.gradeBool S.E (M.gradeView (M.toHealing (x[m][v_0].st).st.core))
      (x[m][v_0].st).st.core.F S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) p)
      (M.late S.E S.hc (r + 1) p) B ⇢ true)
    (hneTick : ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) v_0 (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S r) x[n] v_0)
        (Restated.Vocabulary.Execution.Setup.a M S r) ⇢ out)
    (hneAtt : ∀ v_1 ∈ Restated.freshAttestersW M S Sched x r m,
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) v_1 (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S r) x[n] v_1)
          (Restated.Vocabulary.Execution.Setup.a M S r) ⇢ out) :
    Block.compatible B T.erase = true := by
  obtain ⟨v_1, hv_1, C, hC, hconf, hBC⟩ := Restated.graded_preceq_freshSG_upTo facts S Sched x
    hexec hsync htd hn hgst hm hawT hwh hexp hroom hheads hhead_mem hhalf B hgrade hneTick hneAtt
  obtain ⟨a, ha⟩ := actionAttestationFrom_nonemptyLate facts (Setup.alwaysAwake S) (x[n][v_1].st) v_1 r
  have hqr : v_1 ∉ Sched.adv ((Restated.Vocabulary.Execution.Setup.a M S r)) :=
    Restated.honestThrough_of_mem_freshAttestersW facts hv_1 _ (Restated.action_le_time_of_stepBefore facts S Sched x htd hm)
  have hsent := Restated.fresh_attests facts S Sched x hn
    (Restated.freshAttestersW_subset_freshAttesters facts S Sched x r m hv_1) hqr (hneAtt v_1 hv_1)
    (awake_for_grade2_of_mem_freshAttestersWLate facts S Sched x hn hv_1 (fun t ht =>
      Restated.honestThrough_of_mem_freshAttestersW facts hv_1 t
        (le_trans ht (Restated.action_le_time_of_stepBefore facts S Sched x htd hm)))) a ha
  have hcompat : Block.compatible C.erase T.erase = true :=
    hsg v_1 (hfreshH hv_1) a (Restated.actionAttestationFrom_round facts (Setup.alwaysAwake S) _ v_1 r a ha)
      (Restated.actionAttestationFrom_val_index facts (Setup.alwaysAwake S) _ v_1 r a ha) hsent C hC
      (hconf a ha)
  exact Protocol.compatible_of_preceq_of_compatible hBC hcompat

end

end DecoupledConsensusModel.Sts.Restated
