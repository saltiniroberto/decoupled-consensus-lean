import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bK_FreshAttestersW
import Proofs.Claims.Restated.Claim13bK_GradeForCatchUp
import Proofs.Claims.Restated.Claim13bK_GradeOld
import Proofs.Claims.Restated.Claim13bK_GradeOldHeads
import Proofs.Claims.Restated.Claim13bK_StableRootFor
import Proofs.Claims.Restated.Claim13bStepGrade
import Proofs.Claims.Restated.Claim13bStepKit
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bStepKitTick
import Proofs.Claims.Restated.Claim13bStepSG
import Proofs.Claims.Restated.Claim13bSyncView
import Proofs.Claims.Restated.Claim13bW_FrameAsleep
import Proofs.Claims.Restated.Claim13beRoute3_3
import Proofs.Claims.Restated.ClaimAsyncK_Attest
import Proofs.Claims.Restated.ClaimAsyncK_Defs
import Proofs.Claims.Restated.ClaimAsyncK_GradeFor
import Proofs.Claims.Restated.ClaimAsyncK_NoConflictingQuorum
import Proofs.Claims.Restated.ClaimAsyncK_PeriodInduction
import Proofs.Claims.Restated.ClaimAsyncK_StableRecord
import Proofs.Claims.Restated.ClaimAsyncK_TokensHeld
import Proofs.Claims.Restated.CommonViewOfFinalizedDescendantsFacts
import Proofs.Claims.Restated.ProcessIdempotent
import Proofs.Claims.Restated.ProcessedFlip
import Proofs.Claims.Restated.Projection
import Proofs.Claims.Restated.TickOutcomeHonest
import Proofs.Claims.Restated.VocabularyAssumptionsLemmas
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bK_FreshAttestersW
import Model.Conditions.Claim13bK_GradeOldHeads
import Model.Conditions.Claim13bStepKitTick
import Model.Conditions.Claim13bStepSG
import Model.Conditions.ClaimAsyncK_AfterPeriod
import Model.Conditions.ClaimAsyncK_Defs
import Model.Conditions.ClaimAsyncK_Handover
import Model.Conditions.ClaimAsyncK_PeriodInduction
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Sts_Spec2Claims_ClaimStableThroughAsyncPeriod
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.ClaimAsyncK_AfterPeriod
import Proofs.Claims.Restated.Claim13bW_ScheduleRule

/-!
# Delivery and grading around an asynchronous period

Over a model `M : Record.Model V`, under the delivery premises around an asynchronous period
`[b₀, b₁)`: honest messages reach a receiver awake throughout an interval, honest attestations and
blocks are held by the reader before a deadline, and the resulting ready tokens and grades at the
rounds of the expiry window.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

local macro "pGF% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13bK_GradeFor)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "pPI% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.ClaimAsyncK_PeriodInduction)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Under the delivery premises around the asynchronous period `[b₀, b₁)` with `b₀ ≤ b₁`, if an
    honest validator puts `sm` on the wire at step `k` with `x[k].time < t_a`, the deadline of `t_a`
    is at or before `D`, and `w` is awake at every instant of `[t_a, D]`, then `sm` is delivered to
    `w` at a step `d` after `k`, at an instant at or after `x[k].time` and strictly before `D`. -/
theorem deliver_by_outside (facts : Record.Facts M) (S : Setup V) {Sched : Schedule V}
    (x : AtomicExec (Record.protocolOf M S) Sched) {b₀ b₁ : Int} (hb : b₀ ≤ b₁)
    (hsync : Restated.SynchronyFromWakeOutside M S x b₀ b₁) (hcatch : Restated.CatchUpOnWakeOutside M S x b₀ b₁)
    {k : Nat} {sm : SignedMsg V (NamedObject V)} (hs : Restated.HonestSendAt M S x k sm)
    {w : V} {t_a D : Int} (hkt : (x[k].time : Int) < t_a)
    (hD : deadlineOutside S b₀ b₁ t_a ≤ D)
    (hw : w ∈ Sched.awakeThroughout t_a D) :
    ∃ d : Nat, k < d ∧ x.lbl d = AtomicAction.deliver w sm ∧
      (x[k].time : Int) ≤ (x[d].time : Int) ∧ (x[d].time : Int) < D := by
  classical
  have hd := S.E.Δ_pos
  have hle := le_deadlineOutside S b₀ b₁ t_a
  by_cases hA : w ∈ Sched.awakeThroughout (x[k + 1].time : Int) t_a
  · have hdl := deadlineOutside_mono S hb (le_of_lt hkt)
    have hwin : w ∈ Sched.awakeThroughout (x[k + 1].time : Int)
        (deadlineOutside S b₀ b₁ (x[k].time : Int)) := by
      refine mem_awakeThroughout_of_forall Sched (fun t h0 h1 => ?_)
      by_cases ht : t ≤ t_a
      · exact mem_awake_of_mem_awakeThroughout Sched hA h0 ht
      · exact mem_awake_of_mem_awakeThroughout Sched hw (by linarith) (by linarith)
    obtain ⟨d, hkd, hlbl, hlo, hlt⟩ := hsync k w sm hs hwin
    exact ⟨d, hkd, hlbl, hlo, by linarith⟩
  ·
    let A : Finset Int := (Finset.Icc (x[k + 1].time : Int) t_a).filter
      (fun t => w ∉ Sched.awake t)
    have hne : A.Nonempty := by
      by_contra hempty
      apply hA
      refine mem_awakeThroughout_of_forall Sched (fun t h0 h1 => ?_)
      by_contra hnot
      exact hempty ⟨t, Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨h0, h1⟩, hnot⟩⟩
    set t' := A.max' hne with ht'
    have ht'mem : t' ∈ A := Finset.max'_mem A hne
    obtain ⟨ht'Icc, ht'asleep⟩ := Finset.mem_filter.1 ht'mem
    obtain ⟨ht'lo, ht'hi⟩ := Finset.mem_Icc.1 ht'Icc
    have hwa : w ∈ Sched.awake t_a :=
      mem_awake_of_mem_awakeThroughout Sched hw le_rfl (by linarith)
    have ht'lt : t' < t_a := by
      rcases lt_or_eq_of_le ht'hi with h | h
      · exact h
      · exact absurd (h ▸ hwa) ht'asleep
    have hawake_after : ∀ t : Int, t' + 1 ≤ t → t ≤ D → w ∈ Sched.awake t := by
      intro t h0 h1
      by_cases hta : t ≤ t_a
      · by_contra hnot
        have htA : t ∈ A :=
          Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨by linarith, hta⟩, hnot⟩
        have := Finset.le_max' A t htA
        rw [← ht'] at this
        linarith
      · exact mem_awake_of_mem_awakeThroughout Sched hw (by linarith) h1
    have hdl := deadlineOutside_mono S hb (show t' + 1 ≤ t_a by linarith)
    have hwthr : w ∈ Sched.awakeThroughout (t' + 1) (deadlineOutside S b₀ b₁ (t' + 1)) :=
      mem_awakeThroughout_of_forall Sched (fun t h0 h1 => hawake_after t h0 (by linarith))
    have hkt' : (x[k].time : Int) < t' + 1 := by
      have := Restated.time_mono_int facts S Sched x (Nat.le_succ k)
      linarith
    have hprev : w ∉ Sched.awake (t' + 1 - 1) := by
      rw [add_sub_cancel_right]; exact ht'asleep
    obtain ⟨d, hkd, hlbl, hdlo, hdhi⟩ :=
      hcatch k w sm (t' + 1) hs hkt' (hawake_after (t' + 1) le_rfl (by linarith)) hprev hwthr
    exact ⟨d, hkd, hlbl, by linarith, by linarith⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- On an execution whose clock diverges, whose validators wake only at whole multiples of `Δ`, and
    in which every such tick of an awake validator not held has an outcome: if `w` is awake at step
    `k`'s instant and honest through `k`, and `t₀` is a positive whole multiple of `Δ` at or before
    `x[k].time`, then `w`'s store clock after `k` steps is at or after `t₀`. -/
theorem clock_ge_of_awake_sts (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (htd : Restated.TimeDiverges M x) (hmult : AwakeAtMultiples S Sched)
    {k : Nat} {w : V} (hwk : w ∈ Sched.awake (x[k].time : Int))
    (hhon : Restated.HonestThrough M Sched x k w) {t₀ : Int} (ht₀ : 0 < t₀) (hdvd : t₀ % S.E.Δ = 0)
    (hle : t₀ ≤ (x[k].time : Int))
    (hnr : ∀ (k τ : Nat) (u : V), x.lbl k = AtomicAction.tickAllAwake τ →
      (τ : Int) % S.E.Δ = 0 → u ∈ Sched.awake (τ : Int) \ Sched.adv (τ : Int) →
      (∀ t' ≤ (τ : Int), u ∉ Sched.adv t') →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) u (Record.wakeStage M Sched (τ : Int) x[k] u) (τ : Int) ⇢ out) :
    t₀ ≤ (x[k][w].st).st.core.t := by
  classical
  by_cases hA : w ∈ Sched.awakeThroughout t₀ (x[k].time : Int)
  · obtain ⟨n, hn⟩ := Restated.exists_tickStepAt facts x htd ht₀
    obtain ⟨-, hn0⟩ := Restated.tickStepAt_time facts x hn
    have hnk : n < k := Restated.lt_of_time_lt facts S Sched x (by linarith)
    have haw : w ∈ Sched.awake t₀ \ Sched.adv t₀ :=
      Finset.mem_sdiff.2 ⟨mem_awake_of_mem_awakeThroughout Sched hA le_rfl hle, hhon _ hle⟩
    exact Restated.clock_ge_of_tickStepAt_awake_sts facts S Sched x hn haw
      (by
        obtain ⟨τ, hl, hτ⟩ := id hn
        rw [← hτ] at haw hdvd ⊢
        exact hnr n τ w hl hdvd haw (fun t' ht' => hhon t' (by rw [hτ] at ht'; linarith)))
      (Nat.succ_le_of_lt hnk)
  · let A : Finset Int := (Finset.Icc t₀ (x[k].time : Int)).filter
      (fun t => w ∉ Sched.awake t)
    have hne : A.Nonempty := by
      by_contra hempty
      apply hA
      refine mem_awakeThroughout_of_forall Sched (fun t h0 h1 => ?_)
      by_contra hnot
      exact hempty ⟨t, Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨h0, h1⟩, hnot⟩⟩
    set t' := A.max' hne with ht'
    have ht'mem : t' ∈ A := Finset.max'_mem A hne
    obtain ⟨ht'Icc, ht'asleep⟩ := Finset.mem_filter.1 ht'mem
    obtain ⟨ht'lo, ht'hi⟩ := Finset.mem_Icc.1 ht'Icc
    have ht'lt : t' < (x[k].time : Int) := by
      rcases lt_or_eq_of_le ht'hi with h | h
      · exact h
      · exact absurd (h ▸ hwk) ht'asleep
    have hwake : w ∈ Sched.awake (t' + 1) := by
      by_contra hnot
      have htA : t' + 1 ∈ A :=
        Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨by linarith, by linarith⟩, hnot⟩
      have := Finset.le_max' A (t' + 1) htA
      rw [← ht'] at this
      linarith
    have hprev : w ∉ Sched.awake (t' + 1 - 1) := by
      rw [add_sub_cancel_right]; exact ht'asleep
    have hdvd' := hmult (t' + 1) w hwake hprev
    obtain ⟨n, hn⟩ := Restated.exists_tickStepAt facts x htd (show 0 < t' + 1 by linarith)
    obtain ⟨-, hn0⟩ := Restated.tickStepAt_time facts x hn
    have hnk : n < k := Restated.lt_of_time_lt facts S Sched x (by linarith)
    have haw : w ∈ Sched.awake (t' + 1) \ Sched.adv (t' + 1) :=
      Finset.mem_sdiff.2 ⟨hwake, hhon _ (by linarith)⟩
    have := Restated.clock_ge_of_tickStepAt_awake_sts facts S Sched x hn haw
      (by
        obtain ⟨τ, hl, hτ⟩ := id hn
        rw [← hτ] at haw hdvd' ⊢
        exact hnr n τ w hl hdvd' haw (fun t'' ht'' => hhon t'' (by rw [hτ] at ht''; linarith)))
      (Nat.succ_le_of_lt hnk)
    linarith

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- On an execution whose clock diverges, whose validators wake only at whole multiples of `Δ`, and
    in which every such tick of an awake validator not held has an outcome: if `a` names its signer
    `v`, `v` is not held at any instant up to `x[j].time`, the receiver `w` is honest through `j`,
    and the round of `x[j].time`'s slot is at most `a.round + η_SG`, then at every step before `j`
    that delivers `⟨v, a⟩` to `w`, the receiving store tests `a` neither as stale nor as a future
    round. -/
theorem window_of_awake_at_delivery (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (htd : Restated.TimeDiverges M x) (hmult : AwakeAtMultiples S Sched)
    {j : Nat} {v w : V} {a : NamedAttestation V}
    (hv : HonestThroughTime Sched (x[j].time : Int) v)
    (hunf : Restated.Unforgeability M S x) (hidx : a.val_index = v)
    (hwj : Restated.HonestThrough M Sched x j w)
    (hexp : (M.round_of S.hc (S.E.slotOf (x[j].time : Int))) ≤ a.round + S.hc.η_SG)
    (hnr : ∀ (k τ : Nat) (u : V), x.lbl k = AtomicAction.tickAllAwake τ →
      (τ : Int) % S.E.Δ = 0 → u ∈ Sched.awake (τ : Int) \ Sched.adv (τ : Int) →
      (∀ t' ≤ (τ : Int), u ∉ Sched.adv t') →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) u (Record.wakeStage M Sched (τ : Int) x[k] u) (τ : Int) ⇢ out) :
    ∀ k : Nat, k < j →
      x.lbl k = AtomicAction.deliver w ⟨v, NamedObject.attest a⟩ →
      ¬ (a.round < (M.round_of S.hc (x[k][w].st).st.core.s) - S.hc.η_SG ∨
         (M.round_of S.hc (x[k][w].st).st.core.s) < a.round) := by
  intro k hkj hlbl
  have hkt : (x[k].time : Int) ≤ (x[j].time : Int) := Restated.time_mono_int facts S Sched x (le_of_lt hkj)
  have hvk : HonestThroughTime Sched (x[k].time : Int) v :=
    fun t ht => hv t (le_trans ht hkt)
  obtain ⟨-, -, -, -, -, hact⟩ := Restated.deliver_attest_after_action facts S Sched x hvk hunf hidx hlbl
  have hwk : w ∈ Sched.awake (x[k].time : Int) := (Restated.sent_of_deliver facts S Sched x hlbl).2
  have hclock : (Restated.Vocabulary.Execution.Setup.a M S a.round) ≤ (x[k][w].st).st.core.t :=
    Restated.clock_ge_of_awake_sts facts S Sched x htd hmult hwk (Restated.honestThrough_of_time_le facts hwj hkt)
      (Restated.action_pos facts S a.round) (Restated.action_emod_delta facts S a.round) hact hnr
  have hge : a.round ≤ (M.round_of S.hc (x[k][w].st).st.core.s) :=
    Restated.receiver_round_ge_of_clock_ge facts S Sched x k w a.round hclock
  have hle : (M.round_of S.hc (x[k][w].st).st.core.s) ≤ a.round + S.hc.η_SG :=
    le_trans (Restated.receiver_round_le_of_time_le facts S Sched x k w hkt) hexp
  have hsub : (M.round_of S.hc (x[k][w].st).st.core.s) - S.hc.η_SG ≤ a.round :=
    Nat.sub_le_iff_le_add.mpr hle
  rintro (h | h)
  · exact absurd h (Nat.not_lt.mpr hsub)
  · exact absurd h (Nat.not_lt.mpr hge)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Under the delivery premises around `[b₀, b₁)` with `b₀ ≤ b₁`, if `n` is the tick step at
    `S.a ρ₀`, `S.a ρ₀ ≤ t_a`, the deadline of `t_a` is at or before `D ≤ S.a (ρ₀ + η_SG)`, `v_1` is
    an honest member of `attestersAt S Sched ρ₀` through a step `m` with `D ≤ x[m].time`, and `w`
    is honest through `m` and awake throughout `[t_a, D]`, then for every attestation `a` of `v_1`'s
    round-`ρ₀` action read, `w`'s grade view after `m` steps holds the SG-vote projection of `a` for
    round `ρ₀`, stamped strictly before `D`. -/
theorem token_held_by_outside (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {b₀ b₁ : Int} (hb : b₀ ≤ b₁) (hsync : Restated.SynchronyFromWakeOutside M S x b₀ b₁)
    (hcatch : Restated.CatchUpOnWakeOutside M S x b₀ b₁) (hmult : AwakeAtMultiples S Sched)
    (htd : Restated.TimeDiverges M x) {ρ₀ n m : Nat} (hn : Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S ρ₀))) {t_a D : Int}
    (hta : (Restated.Vocabulary.Execution.Setup.a M S ρ₀) ≤ t_a) (hD : deadlineOutside S b₀ b₁ t_a ≤ D)
    (hDexp : D ≤ (Restated.Vocabulary.Execution.Setup.a M S (ρ₀ + S.hc.η_SG)))
    {v_1 w : V} (hv_1 : v_1 ∈ Restated.attestersAt M S Sched ρ₀) (hv_1m : Restated.HonestThrough M Sched x m v_1)
    (hm : D ≤ (x[m].time : Int))
    (hw : w ∈ Sched.awakeThroughout t_a D) (hwm : Restated.HonestThrough M Sched x m w) :
    ∀ a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][v_1].st) v_1 ρ₀,
    M.sgVote a.erase
        ∈ (M.gradeView (M.toHealing (x[m][w].st).st.core)).sg_votes ρ₀ ∧
      ∃ stamp : Int, stamp < D ∧
        (M.gradeView (M.toHealing (x[m][w].st).st.core)).timestamp_sg_vote (M.sgVote a.erase)
          = some ((stamp : Stamp)) := by
  intro a ha
  have ha_round : a.round = ρ₀ :=
    Restated.actionAttestationFrom_round facts (Setup.alwaysAwake S) _ v_1 ρ₀ a ha
  have ha_idx : a.val_index = v_1 :=
    Restated.actionAttestationFrom_val_index facts (Setup.alwaysAwake S) _ v_1 ρ₀ a ha
  have hd := S.E.Δ_pos
  have hle := le_deadlineOutside S b₀ b₁ t_a
  obtain ⟨hn1, hn0⟩ := Restated.tickStepAt_time facts x hn
  have hsend := Restated.attest_honestSend_of_attestersAt facts S Sched x hn hv_1 hv_1m (by linarith) (fun k τ u hl _ => facts.ndRun.tick_outcome_sts S Sched x hexec.idealization.root_injective hexec.honestRootsNew k τ u hl) a ha
  obtain ⟨d, hnd, hlbl, -, hdlt⟩ :=
    Restated.deliver_by_outside facts S x hb hsync hcatch hsend (by linarith) hD hw
  have hdm : d < m := Restated.lt_of_time_lt facts S Sched x (by linarith)
  have hd1m : d + 1 ≤ m := Nat.succ_le_of_lt hdm
  have hdtime : (x[d + 1].time : Int) = (x[d].time : Int) := by
    exact_mod_cast congrArg (fun j : Nat => (j : Int)) (Restated.deliver_time facts S Sched x hlbl)
  have hd1le : (x[d + 1].time : Int) ≤ (x[m].time : Int) := Restated.time_mono_int facts S Sched x hd1m
  have hview : (⟨v_1, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[d + 1][w].view :=
    Restated.mem_view_succ_of_deliver facts S Sched x hlbl
  have haw : AtomicAwake x (d + 1) w := by
    have h := (Restated.sent_of_deliver facts S Sched x hlbl).2
    show w ∈ Sched.awake ((x[d + 1].time : Nat) : Int)
    rw [hdtime]; exact h
  have hv : HonestThroughTime Sched (x[d + 1].time : Int) v_1 := fun t ht =>
    hv_1m t (le_trans ht hd1le)
  have hexp : (M.round_of S.hc (S.E.slotOf (x[d + 1].time : Int))) ≤ a.round + S.hc.η_SG := by
    rw [ha_round, ← Restated.round_of_slotOf_action facts S (ρ₀ + S.hc.η_SG)]
    exact Restated.roundAt_mono_sr facts S (by rw [hdtime]; linarith)
  have hwin := Restated.window_of_awake_at_delivery facts S Sched x htd hmult hv hexec.toUnforgeability ha_idx
    (Restated.honestThrough_of_time_le facts hwm hd1le) hexp (fun k τ u hl _ => facts.ndRun.tick_outcome_sts S Sched x hexec.idealization.root_injective hexec.honestRootsNew k τ u hl)
  have hroom : ∀ k : Nat, k < d + 1 →
      x.lbl k = AtomicAction.deliver w ⟨v_1, NamedObject.attest a⟩ →
      (M.round_votes (x[k][w].st).st.core a.erase).card ≠ 2 := by
    intro k hk _
    have hkm : k ≤ m := le_trans (Nat.le_of_lt_succ hk) (le_of_lt hdm)
    exact Restated.hroom_of_fresh facts S Sched x hexec hn
      (fun t ht => hv_1m t (le_trans ht (Restated.time_mono_int facts S Sched x hkm))) a ha
  obtain ⟨k, hkj, -, hcase⟩ := Restated.attest_recorded_of_mem_view facts S Sched x hview haw hwin hroom
    (fun k _ _ => facts.nd.process_nonempty _ _ _ (fun _ h => by cases h))
  have hk1m : k + 1 ≤ m := le_trans (Nat.succ_le_of_lt hkj) hd1m
  have hkt : (x[k].time : Int) ≤ (x[d].time : Int) :=
    Restated.time_mono_int facts S Sched x (Nat.le_of_lt_succ hkj)
  have hkey := Restated.token_pooled_stamped_of_record facts S Sched x hk1m
    (hcase.imp id (fun h => ⟨h.1, h.2.2⟩))
  rw [ha_round] at hkey
  obtain ⟨hmem, stamp, hstampLe, hts⟩ := hkey
  exact ⟨hmem, stamp, by linarith, by rw [facts.gr.gradeView_timestamp_sg_vote]; exact hts⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Under the delivery premises around `[b₀, b₁)` with `b₀ ≤ b₁`, if `n` is the tick step at
    `S.a ρ₀`, `S.a ρ₀ ≤ t_a`, the deadline of `t_a` is at or before `D`, `v_1` is honest through
    `n + 1` and holds the named block `C` among its bodies there, `w` is honest through a step `m`
    with `D ≤ x[m].time` and awake throughout `[t_a, D]`, and `w` admits `C` at every delivery at or
    before `D`, then `C`'s erasure is in `w`'s tree after `m` steps, stamped strictly before `D`. -/
theorem block_held_by_outside (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {b₀ b₁ : Int} (hb : b₀ ≤ b₁) (hsync : Restated.SynchronyFromWakeOutside M S x b₀ b₁)
    (hcatch : Restated.CatchUpOnWakeOutside M S x b₀ b₁) (hmult : AwakeAtMultiples S Sched)
    (htd : Restated.TimeDiverges M x) {ρ₀ n m : Nat} (hn : Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S ρ₀))) {t_a D : Int}
    (hta : (Restated.Vocabulary.Execution.Setup.a M S ρ₀) ≤ t_a) (hD : deadlineOutside S b₀ b₁ t_a ≤ D)
    {v_1 : V} (hv_1 : Restated.HonestThrough M Sched x (n + 1) v_1) {C : NamedBlock V}
    (hC : C ∈ (x[n + 1][v_1].st).st.bodies) {w : V}
    (hm : D ≤ (x[m].time : Int))
    (hw : w ∈ Sched.awakeThroughout t_a D) (hwm : Restated.HonestThrough M Sched x m w)
    (hadm : Restated.ReaderAdmitsInPhase M S Sched x 0 D w C) :
    C.erase ∈ (x[m][w].st).st.core.T ∧
      ∃ σ : Stamp, (x[m][w].st).st.core.timestamp_block C.erase = some σ ∧
        σ < ((D : Int) : Stamp) := by
  classical
  have hd := S.E.Δ_pos
  obtain ⟨hn1, hn0⟩ := Restated.tickStepAt_time facts x hn
  by_cases hgen : C = NamedBlock.genesis
  · subst hgen
    have hgb : (NamedBlock.genesis : NamedBlock V) ∈ (x[m][w].st).st.bodies :=
      ((Restated.nodeInvariant_sts facts S Sched x m w).1.1.1.2.2.1).1
    refine ⟨?_, ⊥, ?_, WithBot.bot_lt_coe _⟩
    · rw [Restated.bodies_image_eq_T facts S Sched x m w]
      exact Finset.mem_image_of_mem NamedBlock.erase hgb
    · refine Restated.block_stamp_carry facts S Sched x (Nat.zero_le m) w ?_
      have hge : (NamedBlock.genesis : NamedBlock V).erase = Block.genesis := erase_named_genesis
      rw [Record.st_zero M S Sched x w, hge]
      exact facts.nd.initial_timestamp_genesis _ _
  obtain ⟨i, k, v_0, him, hmemi, -, hkt, hnk, -, hsend⟩ :=
    Restated.honestSend_of_holder facts S Sched x hC hv_1 hgen
  have hin : (x[i].time : Int) ≤ (x[n].time : Int) :=
    Restated.time_mono_int facts S Sched x (Nat.le_of_lt_succ him)
  obtain ⟨d, hkd, hdlbl, -, hdlt⟩ :=
    Restated.deliver_by_outside facts S x hb hsync hcatch hsend (show (x[k].time : Int) < t_a by linarith) hD hw
  have hdlo : (x[i + 1].time : Int) ≤ (x[d].time : Int) :=
    le_trans hnk (Restated.time_mono_int facts S Sched x (Nat.succ_le_of_lt hkd))
  have hdm : d < m := Restated.lt_of_time_lt facts S Sched x (by linarith)
  have hwh : Restated.HonestThrough M Sched x d w := fun t ht =>
    hwm t (le_trans ht (Restated.time_mono_int facts S Sched x (le_of_lt hdm)))
  have hbody : C ∈ (x[d + 1][w].st).st.bodies :=
    Restated.block_admitted_of_deliver_ofAdmits facts S Sched x hexec hmult htd hadm hdlbl hwh hmemi hgen
      hdlo (Int.natCast_nonneg _) (le_of_lt hdlt)
      (fun n' t' hn' hΔ hq _ hhi' => Restated.tick_outcome_of_tickStepAt_honest facts S Sched x
        hexec.idealization.root_injective hexec.honestRootsNew hn' hΔ hq (fun t'' ht'' => hwh t'' (le_trans ht'' hhi')))
  have hdtime : (x[d + 1].time : Int) = (x[d].time : Int) := by
    exact_mod_cast congrArg (fun j : Nat => (j : Int)) (Restated.deliver_time facts S Sched x hdlbl)
  have hdm1 : d + 1 ≤ m := Nat.succ_le_of_lt hdm
  have hbodym : C ∈ (x[m][w].st).st.bodies :=
    of_decide_eq_true (Restated.processed_mono facts S Sched x w (NamedObject.block C) hdm1
      (decide_eq_true hbody))
  refine ⟨?_, ?_⟩
  · rw [Restated.bodies_image_eq_T facts S Sched x m w]
    exact Finset.mem_image_of_mem NamedBlock.erase hbodym
  · have hmemTd : C.erase ∈ (x[d + 1][w].st).st.core.T := by
      rw [Restated.bodies_image_eq_T facts S Sched x (d + 1) w]
      exact Finset.mem_image_of_mem NamedBlock.erase hbody
    obtain ⟨σ, hσ, hσlt⟩ :=
      Restated.block_stamp_lt_of_time facts S Sched x (d + 1) w (Γ := D) hmemTd
        (by rw [hdtime]; exact hdlt)
    exact ⟨σ, Restated.block_stamp_carry facts S Sched x hdm1 w hσ, hσlt⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- On the premises of `block_held_by_outside` for every body of `v_1` after the tick named by an
    attestation of `v_1`'s round-`ρ₀` action read, if such an attestation `a` names the root `root`,
    then some body `C` of `v_1` after the tick has the root `root`, `w`'s tree after `m` steps
    resolves `root` to `C.erase`, and that block is stamped there before every cutoff at or after
    `D`. -/
theorem attested_block_resolves_by_outside (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {b₀ b₁ : Int} (hb : b₀ ≤ b₁) (hsync : Restated.SynchronyFromWakeOutside M S x b₀ b₁)
    (hcatch : Restated.CatchUpOnWakeOutside M S x b₀ b₁) (hmult : AwakeAtMultiples S Sched)
    (htd : Restated.TimeDiverges M x) {ρ₀ n m : Nat} (hn : Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S ρ₀))) {t_a D : Int}
    (hta : (Restated.Vocabulary.Execution.Setup.a M S ρ₀) ≤ t_a) (hD : deadlineOutside S b₀ b₁ t_a ≤ D)
    {v_1 : V} (hv_1m : Restated.HonestThrough M Sched x m v_1) {w : V}
    (hm : D ≤ (x[m].time : Int))
    (hw : w ∈ Sched.awakeThroughout t_a D) (hwm : Restated.HonestThrough M Sched x m w)
    (hadm : ∀ C : NamedBlock V, C ∈ (x[n + 1][v_1].st).st.bodies →
      ∀ a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][v_1].st) v_1 ρ₀,
      a.confirmed = some C.root →
      Restated.ReaderAdmitsInPhase M S Sched x 0 D w C)
    (a : NamedAttestation V)
    (ha : a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][v_1].st) v_1 ρ₀)
    (root : BlockId) (hroot : a.confirmed = some root) :
    ∃ C : NamedBlock V, C ∈ (x[n + 1][v_1].st).st.bodies ∧ C.root = root ∧
      Block.find? (x[m][w].st).st.core.T root = some C.erase ∧
      ∀ c : Int, D ≤ c →
        stampedBefore (x[m][w].st).st.core.timestamp_block c C.erase = true := by
  have hd := S.E.Δ_pos
  have hle := le_deadlineOutside S b₀ b₁ t_a
  have hn1 := (Restated.tickStepAt_time facts x hn).1
  have hv_1n : Restated.HonestThrough M Sched x (n + 1) v_1 := fun t ht =>
    hv_1m t (le_trans ht (by rw [hn1]; linarith))
  obtain ⟨C, hC, hCroot⟩ := Restated.hhead_mem_of_tick facts S Sched x n ρ₀ v_1 a ha root hroot
  obtain ⟨hmem, σ, hσ, hσlt⟩ :=
    Restated.block_held_by_outside facts S Sched x hexec hb hsync hcatch hmult htd hn hta hD hv_1n hC hm hw
      hwm (hadm C hC a ha (by rw [hroot, hCroot]))
  refine ⟨C, hC, hCroot, ?_, fun c hc => stampedBefore_of_lt hσ
    (lt_of_lt_of_le hσlt (WithBot.coe_le_coe.mpr hc))⟩
  rw [← hCroot, ← Proofs.NamedWire.erase_root]
  exact Restated.find_of_mem_tree_honest facts S Sched x hexec hwm hmem

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- On the premises of `token_held_by_outside` and `attested_block_resolves_by_outside`, if every
    body of `v_1` named by an attestation of its round-`ρ₀` action read is compatible with `w`'s
    finalized block after `m` steps, then for every round `q` with `ρ₀ + 1 ≤ q ≤ ρ₀ + η_SG` and
    every phase `p` whose early cutoff is at or after `D`, every outcome of `v_1`'s ready view of
    `w`'s round-`q` grade at that cutoff has a token of round at least `ρ₀`. -/
theorem exists_ready_token_ge_by_outside (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {b₀ b₁ : Int} (hb : b₀ ≤ b₁) (hsync : Restated.SynchronyFromWakeOutside M S x b₀ b₁)
    (hcatch : Restated.CatchUpOnWakeOutside M S x b₀ b₁) (hmult : AwakeAtMultiples S Sched)
    (htd : Restated.TimeDiverges M x) {ρ₀ n m : Nat} (hn : Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S ρ₀))) {t_a D : Int}
    (hta : (Restated.Vocabulary.Execution.Setup.a M S ρ₀) ≤ t_a) (hD : deadlineOutside S b₀ b₁ t_a ≤ D)
    (hDexp : D ≤ (Restated.Vocabulary.Execution.Setup.a M S (ρ₀ + S.hc.η_SG)))
    {v_1 w : V} (hv_1 : v_1 ∈ Restated.attestersAt M S Sched ρ₀) (hv_1m : Restated.HonestThrough M Sched x m v_1)
    (hm : D ≤ (x[m].time : Int))
    (hw : w ∈ Sched.awakeThroughout t_a D) (hwm : Restated.HonestThrough M Sched x m w)
    (hadm : ∀ C : NamedBlock V, C ∈ (x[n + 1][v_1].st).st.bodies →
      ∀ a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][v_1].st) v_1 ρ₀,
      a.confirmed = some C.root →
      Restated.ReaderAdmitsInPhase M S Sched x 0 D w C)
    (hcompat : ∀ C : NamedBlock V, C ∈ (x[n + 1][v_1].st).st.bodies →
      ∀ a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][v_1].st) v_1 ρ₀,
      a.confirmed = some C.root →
      Block.compatible C.erase (x[m][w].st).st.core.F = true)
    {q : Nat} (hq₁ : ρ₀ + 1 ≤ q) (hq₂ : q ≤ ρ₀ + S.hc.η_SG) (p : Protocol.Phase)
    (hc : D ≤ M.early S.E S.hc q p) :
    ∀ Re, M.readyView (M.gradeView (M.toHealing (x[m][w].st).st.core))
        (x[m][w].st).st.core.F S.hc.η_SG q (M.early S.E S.hc q p) v_1 ⇢ Re →
      ∃ tok ∈ Re, ρ₀ ≤ tok.round := by
  intro Re hRe
  obtain ⟨a, ha⟩ := (pGF% actionAttestationFrom_nonempty_gf) facts (Setup.alwaysAwake S)
    (x[n][v_1].st) v_1 ρ₀
  have ha_round : a.round = ρ₀ :=
    Restated.actionAttestationFrom_round facts (Setup.alwaysAwake S) _ v_1 ρ₀ a ha
  have ha_idx : a.val_index = v_1 :=
    Restated.actionAttestationFrom_val_index facts (Setup.alwaysAwake S) _ v_1 ρ₀ a ha
  obtain ⟨hmem, stamp, hlt, hts⟩ :=
    Restated.token_held_by_outside facts S Sched x hexec hb hsync hcatch hmult htd hn hta hD hDexp hv_1 hv_1m hm
      hw hwm a ha
  obtain ⟨X, hX⟩ := facts.gr.rawInputs_nonempty (M.gradeView (M.toHealing (x[m][w].st).st.core))
    S.hc.η_SG q (M.early S.E S.hc q p) v_1
  obtain ⟨b, hbr⟩ := facts.gr.bodyReady_nonempty (M.gradeView (M.toHealing (x[m][w].st).st.core))
    (x[m][w].st).st.core.F (M.early S.E S.hc q p) (M.sgVote a.erase)
  have hlo : q - S.hc.η_SG ≤ ρ₀ := by omega
  have hhi : ρ₀ < q := by omega
  have hwin : ρ₀ ∈ M.latest_window S.hc.η_SG q :=
    facts.fc.mem_latest_window hlo hhi
  have hraw := facts.gr.mem_rawInputs_of_stamp _ S.hc.η_SG q ρ₀ (M.early S.E S.hc q p) v_1 hwin
    hmem ((facts.sto.sgVote_val _).trans ha_idx) hts
    (lt_of_lt_of_le hlt hc) X hX
  have hready : b = true := by
    have hconf : (M.sgVote a.erase).confirmed = a.confirmed := facts.sto.sgVote_confirmed a
    cases hcase : a.confirmed with
    | none => exact facts.gr.bodyReady_of_no_head _ _ _ _ (hconf.trans hcase) b hbr
    | some root =>
        obtain ⟨C, hC, hCroot, hfind, hstamp⟩ :=
          Restated.attested_block_resolves_by_outside facts S Sched x hexec hb hsync hcatch hmult htd hn hta hD
            hv_1m hm hw hwm hadm a ha root hcase
        have hfind' : Block.find? (M.gradeView (M.toHealing (x[m][w].st).st.core)).T root
            = some C.erase := by
          rw [facts.gr.Sts_gradeView_T]
          exact hfind
        have hstamp' : stampedBefore (M.gradeView (M.toHealing (x[m][w].st).st.core)).timestamp_block
            (M.early S.E S.hc q p) C.erase = true := by
          rw [facts.gr.gradeView_timestamp_block]
          exact hstamp _ hc
        exact facts.gr.bodyReady_of_head _ _ _ _ (hconf.trans hcase) hfind' hstamp'
          (hcompat C hC a ha (by rw [hcase, hCroot])) b hbr
  refine ⟨_, facts.gr.token_mem_readyView _ _ _ _ _ _ X hX hraw b hbr hready Re hRe, ?_⟩
  rw [facts.gr.token_round, facts.sto.sgVote_round]
  exact le_of_eq ha_round.symm

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If `ρ ≥ 1` and `m` is the last step before round `ρ`'s phase-`p` domain instant, then
    `Protocol.early S.E S.hc ρ .g2 ≤ x[m].time`. -/
theorem early_le_time_of_stepBefore (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (htd : Restated.TimeDiverges M x) {ρ : Nat} (hρ : 1 ≤ ρ)
    {p : Protocol.Phase} {m : Nat}
    (hm : Restated.stepBeforeInstant M x m (M.domain S.E S.hc ρ p)) :
    M.early S.E S.hc ρ .g2 ≤ (x[m].time : Int) := by
  have h1 := Restated.time_of_stepBefore_domain facts S Sched x htd hρ hm
  have h2 := facts.gr.early_g2_lt_domain S ρ p
  have h3 : M.early S.E S.hc ρ .g2 < (x[m].time : Int) + 1 := by rw [h1]; exact h2
  exact Int.lt_add_one_iff.mp h3

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If `t_GST ≤ S.a r`, the asynchronous period `[b₀, b₁)` starts at least one delay after
    `S.a (r + 1)` and ends at least one delay before `early (r + η_SG + 1) .g2`, then the deadline
    of the instant `S.a (r + η_SG)` around that period is at or before `early (r + η_SG + 1) .g2`. -/
theorem deadline_le_early_expiry (facts : Record.Facts M) (S : Setup V) {r : Nat} {b₀ b₁ : Int}
    (hgst : S.E.t_GST ≤ (M.a S.hc S.E.Δ r)) (hb₀ : Restated.periodAfterRound M S r b₀) (hb : b₀ ≤ b₁)
    (hb₁ : Restated.periodBeforeExpiry M S r b₁) :
    deadlineOutside S b₀ b₁ ((Restated.Vocabulary.Execution.Setup.a M S (r + S.hc.η_SG))) ≤
      M.early S.E S.hc (r + S.hc.η_SG + 1) .g2 := by
  have hd := S.E.Δ_pos
  have h1 := Restated.early_g2_eq_healA facts S (r + S.hc.η_SG + 1)
  have h2 := Restated.healA_succ facts S (r + S.hc.η_SG)
  have h3 := twelve_delta_le_wAttest_kit S
  have h4 : (M.a S.hc S.E.Δ r) ≤ (M.a S.hc S.E.Δ (r + S.hc.η_SG)) := Restated.healA_mono facts S (by omega)
  have h5 : (M.a S.hc S.E.Δ r) ≤ (M.a S.hc S.E.Δ (r + 1)) := Restated.healA_mono facts S (by omega)
  unfold Restated.periodBeforeExpiry at hb₁
  unfold Restated.periodAfterRound at hb₀
  have hmax : max ((Restated.Vocabulary.Execution.Setup.a M S (r + S.hc.η_SG))) S.E.t_GST = (Restated.Vocabulary.Execution.Setup.a M S (r + S.hc.η_SG)) :=
    max_eq_left (le_trans hgst h4)
  unfold deadlineOutside
  split_ifs
  · rw [hmax]; show (M.a S.hc S.E.Δ (r + S.hc.η_SG)) + S.E.Δ ≤ _; linarith
  · have hm : max ((Restated.Vocabulary.Execution.Setup.a M S (r + S.hc.η_SG))) (max b₁ S.E.t_GST) + S.E.Δ ≤
        M.early S.E S.hc (r + S.hc.η_SG + 1) .g2 := by
      have hA : (Restated.Vocabulary.Execution.Setup.a M S (r + S.hc.η_SG)) + S.E.Δ ≤ M.early S.E S.hc (r + S.hc.η_SG + 1) .g2 := by
        show (M.a S.hc S.E.Δ (r + S.hc.η_SG)) + S.E.Δ ≤ _; linarith
      have hB : b₁ + S.E.Δ ≤ M.early S.E S.hc (r + S.hc.η_SG + 1) .g2 := hb₁
      have hG : S.E.t_GST + S.E.Δ ≤ M.early S.E S.hc (r + S.hc.η_SG + 1) .g2 := by
        linarith
      rcases max_cases ((Restated.Vocabulary.Execution.Setup.a M S (r + S.hc.η_SG))) (max b₁ S.E.t_GST) with ⟨h, -⟩ | ⟨h, -⟩
      · rw [h]; exact hA
      · rw [h]
        rcases max_cases b₁ S.E.t_GST with ⟨h', -⟩ | ⟨h', -⟩
        · rw [h']; exact hB
        · rw [h']; exact hG
    exact hm

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- For a round `ρ` from `r + 2` to `r + η_SG + 1`, `m` the last step before one of its phase-domain
    instants, and `u` honest through `m` and awake throughout `[t_a, D]`, with `S.a (r + 1) ≤ t_a`,
    the deadline of `t_a` at or before `D ≤ early ρ .g2`, and `u`'s finalized block an ancestor of
    `P` at a later step: if `Restated.StableHandover` holds for `P` at round `r`,
    `RoundAttestsAbove` holds at every round from `r + 2` to `ρ − 1`, and the participation and
    delivery premises hold, then every outcome of the grade test of `P` for round `ρ` at that phase
    on `u`'s store after `m` steps is `true`. -/
theorem graded_expiry_of_rounds (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {b₀ b₁ : Int} (hb : b₀ ≤ b₁) (hsync : Restated.SynchronyFromWakeOutside M S x b₀ b₁)
    (hcatch : Restated.CatchUpOnWakeOutside M S x b₀ b₁) (hmult : AwakeAtMultiples S Sched)
    (htd : Restated.TimeDiverges M x) (hmono : Sched.MonotoneCorruption) {r : Nat} {P : Block V}
    (hP : Restated.StableHandover M S Sched x r P) (hfix : Restated.fixedRoundSleepinessCountedW M S Sched r)
    {ρ : Nat} (hρ₁ : r + 2 ≤ ρ) (hρ₂ : ρ ≤ r + S.hc.η_SG + 1) (hη : S.hc.η_SG ≤ r)
    (hR : ∀ q : Nat, r + 2 ≤ q → q < ρ → Restated.RoundAttestsAbove M S Sched x r P q)
    {t_a D : Int} (hta : (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) ≤ t_a) (hD : deadlineOutside S b₀ b₁ t_a ≤ D)
    (hDe : D ≤ M.early S.E S.hc ρ .g2)
    {p : Protocol.Phase} {m : Nat} (hm : Restated.stepBeforeInstant M x m (M.domain S.E S.hc ρ p))
    {u : V} (hu : u ∈ Sched.awakeThroughout t_a D) (hum : Restated.HonestThrough M Sched x m u)
    {k : Nat} (hmk : (x[m].time : Int) < (x[k].time : Int))
    (hFk : Block.Preceq (x[k][u].st).st.core.F P) :
    ∀ g : Bool, M.gradeBool S.E (M.gradeView (M.toHealing (x[m][u].st).st.core))
        (x[m][u].st).st.core.F S.hc.η_SG ρ (M.early S.E S.hc ρ p) (M.late S.E S.hc ρ p) P ⇢ g →
      g = true := by
  intro g hg
  have hd := S.E.Δ_pos
  obtain ⟨n₁, hn₁⟩ := Restated.exists_tickStepAt facts x htd (Restated.action_pos facts S (r + 1))
  obtain ⟨hn₁1, -⟩ := Restated.tickStepAt_time facts x hn₁
  have hDm : D ≤ (x[m].time : Int) :=
    le_trans hDe (Restated.early_le_time_of_stepBefore facts S Sched x htd (by omega) hm)
  have hDexp : D ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1 + S.hc.η_SG)) := by
    have h1 := Restated.early_g2_eq_healA facts S ρ
    have h2 : (M.a S.hc S.E.Δ ρ) ≤ (M.a S.hc S.E.Δ (r + 1 + S.hc.η_SG)) := Restated.healA_mono facts S (by omega)
    show D ≤ (M.a S.hc S.E.Δ (r + 1 + S.hc.η_SG))
    linarith
  have hFd : ∀ d : Nat, (x[d].time : Int) < (x[k].time : Int) →
      Block.Preceq (x[d][u].st).st.core.F P := fun d hd' =>
    preceq_trans_Preceq (Restated.F_mono facts S Sched x u (le_of_lt (Restated.lt_of_time_lt facts S Sched x hd'))) hFk
  choose Re hRe using fun v_1 : V => facts.gr.readyView_nonempty
    (M.gradeView (M.toHealing (x[m][u].st).st.core)) (x[m][u].st).st.core.F S.hc.η_SG ρ
    (M.early S.E S.hc ρ p) v_1
  choose Wl hWl using fun v_1 : V => facts.gr.rawView_nonempty
    (M.gradeView (M.toHealing (x[m][u].st).st.core)) S.hc.η_SG ρ (M.late S.E S.hc ρ p) v_1
  refine Restated.gradeBool_period_of_tokens_resolved facts S Sched x hexec htd hmono hfix (by omega)
    hρ₂ hη hm Re hRe ?_ Wl hWl ?_ g hg
  ·
    intro v_1 hv_1
    have hv_1c := (Finset.mem_sdiff.1 hv_1).1
    have hv_1A := hv_1c
    have hv_1W := Restated.attestersAt_of_activeRoundW facts S Sched (Restated.activeRoundWThroughNext_subset_activeRoundW_succ facts S Sched r hv_1A)
    have hv_1m := Restated.honestThrough_of_mem_countedAt facts S Sched x htd hmono (by omega) hm hv_1
    have hv_1n : Restated.HonestThrough M Sched x (n₁ + 1) v_1 := by
      have hle := le_deadlineOutside S b₀ b₁ t_a
      exact Restated.honestThrough_of_time_le facts hv_1m (by rw [hn₁1]; linarith)
    have hcov := hP.covers (r + 1) (Or.inr rfl) n₁ hn₁ v_1 hv_1W hv_1n
    exact Restated.exists_ready_token_ge_by_outside facts S Sched x hexec hb hsync hcatch hmult htd hn₁ hta hD
      hDexp hv_1W hv_1m hDm hu hum
      (fun C hC a ha hconf d v_0 _ _ _ hdle => Or.inl
        (preceq_eq_true_iff_Preceq.mpr
          (preceq_trans_Preceq (hFd d (by linarith)) (hcov C hC a ha hconf))))
      (fun C hC a ha hconf => compatible_of_cases
        (Or.inr (preceq_trans_Preceq (hFd m hmk) (hcov C hC a ha hconf))))
      (q := ρ) (by omega) (by omega) p (le_trans hDe (Restated.early_g2_le_early facts S ρ p))
      (Re v_1) (hRe v_1)
  ·
    intro v_1 hv_1 tok htok hq
    have hv_1c := (Finset.mem_sdiff.1 hv_1).1
    have hv_1A := hv_1c
    have hv_1m := Restated.honestThrough_of_mem_countedAt facts S Sched x htd hmono (by omega) hm hv_1
    obtain ⟨hlt, n', hn', hawk, hkey⟩ :=
      Restated.rawView_token_facts facts S Sched x hexec hv_1m (hWl v_1) htok
    obtain ⟨hn'1, -⟩ := Restated.tickStepAt_time facts x hn'
    have hSq : (Restated.Vocabulary.Execution.Setup.a M S tok.round) + S.E.Δ ≤ (x[m].time : Int) :=
      Restated.action_delta_le_time_of_stepBefore facts S Sched x htd (show tok.round + 1 ≤ ρ by omega) hm
    have hv_1n : Restated.HonestThrough M Sched x (n' + 1) v_1 :=
      Restated.honestThrough_of_time_le facts hv_1m (by rw [hn'1]; linarith)
    obtain ⟨a, ha, root, hconf⟩ :=
      (pPI% exists_attestation_confirmed_pi) facts S (x[n'][v_1].st) v_1 tok.round
    refine ⟨root, (hkey a ha).trans hconf, fun B hB => ?_⟩
    have hcov : ∀ C : NamedBlock V, C ∈ (x[n' + 1][v_1].st).st.bodies →
        ∀ a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n'][v_1].st) v_1 tok.round,
        a.confirmed = some C.root →
        Block.Preceq P C.erase := by
      by_cases hr1 : tok.round = r + 1
      · have hv_1W := Restated.attestersAt_of_activeRoundW facts S Sched (Restated.activeRoundWThroughNext_subset_activeRoundW_succ facts S Sched r hv_1A)
        rw [hr1] at hn' ⊢
        exact hP.covers (r + 1) (Or.inr rfl) n' hn' v_1 hv_1W hv_1n
      · have hq2 : r + 2 ≤ tok.round := by omega
        have hawT : v_1 ∈ Sched.awakeThroughout
            (M.early S.E S.hc tok.round .g2 - S.E.Δ) ((Restated.Vocabulary.Execution.Setup.a M S tok.round)) :=
          Restated.rawView_token_attestersAt facts S Sched x hexec hv_1m (hWl v_1) htok (by omega)
        exact fun C hC a' ha' hconf' =>
          (hR tok.round hq2 hlt n' hn' v_1 hv_1A hv_1n hawT a' ha').1 C hC hconf'
    exact Restated.preceq_of_find_attested facts S Sched x hexec hv_1n hcov a ha hconf hum hB

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- For a round `q` whose action instant is at or after `b₁` and GST, `m` the last step before one
    of round `q + 1`'s phase-domain instants, and `u` honest through `m`, awake throughout
    `[t_a, t_a + Δ]` with `S.a q ≤ t_a` and `t_a + Δ ≤ early (q + 1) g2`, with its finalized block an ancestor of `P` at a later step: if
    round-level sleepiness holds from round `q + 1`'s opening at the latest, `RoundAttestsAll` holds
    at `q`, and the delivery premises hold around `[b₀, b₁)`, then every outcome of the grade test
    of `P` for round `q + 1` at that phase on `u`'s store after `m` steps is `true`. -/
theorem graded_after_of_round (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {b₀ b₁ : Int} (hb : b₀ ≤ b₁) (hsync : Restated.SynchronyFromWakeOutside M S x b₀ b₁)
    (hcatch : Restated.CatchUpOnWakeOutside M S x b₀ b₁) (hmult : AwakeAtMultiples S Sched)
    (htd : Restated.TimeDiverges M x) (hmono : Sched.MonotoneCorruption) {tE : Int}
    (hrs : Restated.roundSleepinessW M S Sched tE) {q : Nat}
    (htE : tE ≤ M.opening S.E S.hc (q + 1)) (hη : S.hc.η_SG ≤ q)
    (hgq : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S q)) (hbq : b₁ ≤ (Restated.Vocabulary.Execution.Setup.a M S q)) {P : Block V}
    (hRq : Restated.RoundAttestsAll M S Sched x P q)
    {p : Protocol.Phase} {m : Nat}
    (hm : Restated.stepBeforeInstant M x m (M.domain S.E S.hc (q + 1) p))
    {u : V} {t_a : Int} (hta : (Restated.Vocabulary.Execution.Setup.a M S q) ≤ t_a)
    (htaE : t_a + S.E.Δ ≤ M.early S.E S.hc (q + 1) .g2)
    (hu : u ∈ Sched.awakeThroughout t_a (t_a + S.E.Δ))
    (hum : Restated.HonestThrough M Sched x m u)
    {k : Nat} (hmk : (x[m].time : Int) < (x[k].time : Int))
    (hFk : Block.Preceq (x[k][u].st).st.core.F P) :
    ∀ g : Bool, M.gradeBool S.E (M.gradeView (M.toHealing (x[m][u].st).st.core))
        (x[m][u].st).st.core.F S.hc.η_SG (q + 1) (M.early S.E S.hc (q + 1) p)
        (M.late S.E S.hc (q + 1) p) P ⇢ g → g = true := by
  intro g hg
  have hd := S.E.Δ_pos
  have hη1 := S.hc.η_SG_ge_one
  obtain ⟨n, hn⟩ := Restated.exists_tickStepAt facts x htd (Restated.action_pos facts S q)
  obtain ⟨hn1, -⟩ := Restated.tickStepAt_time facts x hn
  have hmt : t_a + S.E.Δ ≤ (x[m].time : Int) :=
    le_trans htaE (Restated.early_le_time_of_stepBefore facts S Sched x htd (Nat.le_add_left 1 q) hm)
  have hD : deadlineOutside S b₀ b₁ t_a ≤ t_a + S.E.Δ :=
    deadline_le_of_after S (le_trans hgq hta) (le_trans hbq hta)
  have hDexp : t_a + S.E.Δ ≤ (Restated.Vocabulary.Execution.Setup.a M S (q + S.hc.η_SG)) := by
    have h1 := Restated.early_g2_eq_healA facts S (q + 1)
    have h3 : (M.a S.hc S.E.Δ (q + 1)) ≤ (M.a S.hc S.E.Δ (q + S.hc.η_SG)) :=
      Restated.healA_mono facts S (Nat.add_le_add_left hη1 q)
    have h4 : t_a + S.E.Δ ≤ M.a S.hc S.E.Δ (q + 1) - 11 * S.E.Δ := by rw [← h1]; exact htaE
    show t_a + S.E.Δ ≤ (M.a S.hc S.E.Δ (q + S.hc.η_SG))
    linarith
  have hFd : ∀ d : Nat, (x[d].time : Int) < (x[k].time : Int) →
      Block.Preceq (x[d][u].st).st.core.F P := fun d hd' =>
    preceq_trans_Preceq (Restated.F_mono facts S Sched x u (le_of_lt (Restated.lt_of_time_lt facts S Sched x hd'))) hFk
  have hmember : ∀ v_1 ∈ Restated.freshAttestersW M S Sched x q m,
      v_1 ∈ Restated.attestersAt M S Sched q ∧ Restated.HonestThrough M Sched x m v_1 ∧
      Restated.HonestThrough M Sched x (n + 1) v_1 ∧
      ∀ C : NamedBlock V, C ∈ (x[n + 1][v_1].st).st.bodies →
        ∀ a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][v_1].st) v_1 q,
        a.confirmed = some C.root →
        Block.Preceq P C.erase := by
    intro v_1 hv_1
    obtain ⟨hv_1W, hv_1m⟩ := (Restated.mem_freshAttestersW facts).mp hv_1
    have hv_1n : Restated.HonestThrough M Sched x (n + 1) v_1 :=
      Restated.honestThrough_of_time_le facts hv_1m (by rw [hn1]; linarith)
    exact ⟨hv_1W, hv_1m, hv_1n, fun C hC a ha hconf => (hRq n hn v_1 hv_1W hv_1n a ha).1 C hC hconf⟩
  have hadm : ∀ v_1 ∈ Restated.freshAttestersW M S Sched x q m,
      ∀ C : NamedBlock V, C ∈ (x[n + 1][v_1].st).st.bodies →
        ∀ a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][v_1].st) v_1 q,
        a.confirmed = some C.root →
        Restated.ReaderAdmitsInPhase M S Sched x 0 (t_a + S.E.Δ) u C := by
    intro v_1 hv_1 C hC a ha hconf d v_0 _ _ _ hdle
    exact Or.inl (preceq_eq_true_iff_Preceq.mpr (preceq_trans_Preceq (hFd d (by linarith))
      ((hmember v_1 hv_1).2.2.2 C hC a ha hconf)))
  choose Re hRe using fun v_1 : V => facts.gr.readyView_nonempty
    (M.gradeView (M.toHealing (x[m][u].st).st.core)) (x[m][u].st).st.core.F S.hc.η_SG (q + 1)
    (M.early S.E S.hc (q + 1) p) v_1
  choose Wl hWl using fun v_1 : V => facts.gr.rawView_nonempty
    (M.gradeView (M.toHealing (x[m][u].st).st.core)) S.hc.η_SG (q + 1)
    (M.late S.E S.hc (q + 1) p) v_1
  refine (Restated.gradeBool_base_of_tokens facts S Sched x hexec htd hmono hrs htE hη hm
    Re hRe ?_ Wl hWl ?_).1 g hg
  · intro v_1 hv_1
    obtain ⟨hv_1W, hv_1m, -, hcov⟩ := hmember v_1 hv_1
    exact Restated.exists_ready_token_ge_by_outside facts S Sched x hexec hb hsync hcatch hmult htd hn hta hD
      hDexp hv_1W hv_1m hmt hu hum (hadm v_1 hv_1)
      (fun C hC a ha hconf => compatible_of_cases
        (Or.inr (preceq_trans_Preceq (hFd m hmk) (hcov C hC a ha hconf))))
      (q := q + 1) le_rfl (Nat.add_le_add_left hη1 q) p
      (le_trans htaE (Restated.early_g2_le_early facts S (q + 1) p)) (Re v_1) (hRe v_1)
  · intro v_1 hv_1 tok htok hq
    obtain ⟨-, hv_1m, -, hcov⟩ := hmember v_1 hv_1
    have hle := Restated.rawView_round_le facts S Sched x m u q _ v_1 (Wl v_1) (hWl v_1) tok htok
    have hround : tok.round = q := le_antisymm hle hq
    obtain ⟨n', hn', hkey⟩ :=
      Restated.rawView_key_of_honest_at facts S Sched x hexec hv_1m (hWl v_1) htok hround
    have hnn : n' = n := Restated.tickStepAt_unique facts x hn' hn
    rw [hnn] at hkey
    obtain ⟨a, ha, root, hconf⟩ := (pPI% exists_attestation_confirmed_pi) facts S (x[n][v_1].st) v_1 q
    obtain ⟨C, hC, hCroot, hfind, -⟩ :=
      Restated.attested_block_resolves_by_outside facts S Sched x hexec hb hsync hcatch hmult htd hn hta hD
        hv_1m hmt hu hum (hadm v_1 hv_1) a ha root hconf
    refine ⟨root, C.erase, (hkey a ha).trans hconf, ?_, hcov C hC a ha (by rw [hconf, hCroot])⟩
    rw [facts.gr.Sts_gradeView_T]
    exact hfind

end

-- Folded in from the former module `ClaimAsyncK_AfterPeriodRule.lean` (wake switch, lane S).
/-!
# Height votes classified after the asynchronous period, under the awake-test rule

The lemma of `ClaimAsyncK_AfterPeriod.lean` that classifies every honest height vote in the sent
log after the hand-over, with the activity of a sender read off the attestation it sent. Stated
over a model `M : Record.Model V`, its facts `facts : Record.Facts M`, whose field `ndWake` holds the converse awake facts.
-/


section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Let `n₁` be the tick step at `S.a (r + 1)` and `k ≥ n₁ + 1` a step. If `Restated.StableHandover`
    holds for `P` at round `r`, `RoundAttestsAbove` holds at every round from `r + 2` to `r + η_SG`,
    and `RoundAttestsAll` at every round from `r + η_SG + 1` whose action instant is at or before
    `x[k].time`, then `VotesClassified S Sched x r P n₁ k` holds: every height vote in the sent log
    after `k` steps whose signer is honest through `k` is classified. -/
theorem votesClassified_upToSafe_rule (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {r : Nat} {P : Block V} (hP : Restated.StableHandover M S Sched x r P)
    {n₁ : Nat} (hn₁ : Restated.tickStepAt M x n₁ ((Restated.Vocabulary.Execution.Setup.a M S (r + 1)))) {k : Nat} (hk : n₁ + 1 ≤ k)
    (hR : ∀ q : Nat, r + 2 ≤ q → q ≤ r + S.hc.η_SG → Restated.RoundAttestsAbove M S Sched x r P q)
    (hA : ∀ q : Nat, r + S.hc.η_SG + 1 ≤ q → (Restated.Vocabulary.Execution.Setup.a M S q) ≤ (x[k].time : Int) →
      Restated.RoundAttestsAll M S Sched x P q) :
    Restated.VotesClassified M S Sched x r P n₁ k := by
  intro u a h root tmo hu ha hsent hpair
  obtain ⟨-, k', hk'k, htick, hawk, out, hout, hemit⟩ :=
    Restated.attest_round_of_sent facts S Sched x (tB := (x[k].time : Int)) hu hexec.toUnforgeability ha
      le_rfl hsent
  have _hr_s1 := Record.reachedNode_wakeStage facts S Sched x (k') u (Restated.Vocabulary.Execution.Setup.a M S a.round)
  have _hv_s2 := Record.runs_as_wakeStage facts S Sched x (k') u (Restated.Vocabulary.Execution.Setup.a M S a.round)
  have haeq := Restated.attest_of_tick_eq facts S u _ a.round hout hemit
  rw [Restated.actionAttestationFrom_wakeStage facts (Setup.alwaysAwake S) Sched _ x[k'] u a.round]
    at haeq
  have hamem : a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[k'][u].st) u a.round := by
    obtain ⟨a', ha'⟩ := (pGF% actionAttestationFrom_nonempty_gf) facts (Setup.alwaysAwake S)
      (x[k'][u].st) u a.round
    have haa := haeq a' ha'
    rw [← haa] at ha'
    exact ha'
  obtain ⟨hk'1, hk'0⟩ := Restated.tickStepAt_time facts x htick
  obtain ⟨hn₁1, -⟩ := Restated.tickStepAt_time facts x hn₁
  have hSq : (Restated.Vocabulary.Execution.Setup.a M S a.round) ≤ (x[k].time : Int) := by
    rw [← hk'1]; exact Restated.time_mono_int facts S Sched x hk'k
  have huk' : Restated.HonestThrough M Sched x (k' + 1) u :=
    Restated.honestThrough_of_time_le facts hu (Restated.time_mono_int facts S Sched x hk'k)
  by_cases hq : a.round ≤ r + 1
  ·
    have hk'n : k' + 1 ≤ n₁ + 1 := by
      by_contra hcon
      have h1 := Restated.time_mono_int facts S Sched x (show n₁ + 1 ≤ k' by omega)
      have h2 := Restated.healA_mono facts S hq
      have h3 : (Restated.Vocabulary.Execution.Setup.a M S a.round) ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) := h2
      linarith
    have hrunk : M.awake_for_grade2 (Setup.alwaysAwake S) u
        (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S a.round) x[k'] u) a.round := by
      by_contra hno
      have h0 := facts.nd.tick_at_action_asleep (Setup.alwaysAwake S) u _ a.round out hout hno
      rw [h0] at hemit
      exact List.not_mem_nil hemit
    have hemit' := Restated.attest_emitted_at_tick_from facts S Sched x htick hawk ⟨out, hout⟩ hrunk a hamem
    have hsent' := Restated.mem_sent_of_le facts x hk'n hemit'
    have hun : Restated.HonestThrough M Sched x (n₁ + 1) u :=
      Restated.honestThrough_of_time_le facts hu (Restated.time_mono_int facts S Sched x hk)
    exact Restated.votesClassified_of_handover facts S Sched x r P hP hn₁ u a h root tmo hun ha hsent' hpair
  · have hq' : r + 2 ≤ a.round := Nat.succ_le_of_lt (Nat.lt_of_not_le hq)
    have huW : u ∈ Restated.attestersAt M S Sched a.round := (Finset.mem_sdiff.1
      (Restated.honRound_of_attestation_sent facts S Sched x htick
        (Restated.early_g2_sub_delta_nonneg facts S (r := a.round) (Nat.le_trans (Nat.le_add_left 1 (r + 1)) hq')) hawk
        (fun t ht => Restated.honestThrough_of_time_le facts hu
          (Restated.time_mono_int facts S Sched x hk'k) t (by rw [hk'1]; exact ht))
        hout hemit rfl)).1
    by_cases hq2 : a.round ≤ r + S.hc.η_SG
    ·
      by_cases hin : u ∈ Restated.activeRoundWThroughNext M S Sched r
      · left
        have hawT : u ∈ Sched.awakeThroughout (M.early S.E S.hc a.round .g2 - S.E.Δ)
            ((Restated.Vocabulary.Execution.Setup.a M S a.round)) := by
          exact huW
        exact (hR a.round hq' hq2 k' htick u hin huk' hawT a hamem).2 h root tmo hpair
      · right; right
        unfold Restated.activeOutsideFixedIn
        exact Finset.mem_sdiff.2 ⟨Finset.mem_biUnion.2
          ⟨a.round, Finset.mem_Icc.2 ⟨hq', hq2⟩, huW⟩, hin⟩
    ·
      left
      have hq3 : r + S.hc.η_SG + 1 ≤ a.round := Nat.succ_le_of_lt (Nat.lt_of_not_le hq2)
      exact (hA a.round hq3 hSq k' htick u huW huk' a hamem).2 h root tmo hpair

end


section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- For a round `ρ` from `r + η_SG + 1` whose action instant is at or before `tSafe`, under the
    premises of the asynchronous period `[b₀, b₁)` and after it, if `RoundAttestsAbove` holds at
    every round from `r + 2` to `r + η_SG` and `RoundAttestsAll` at every round from `r + η_SG + 1`
    to `ρ − 1`, then `RoundAttestsAll` holds at `ρ`. -/
theorem roundAttestsAll_step (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {b₀ b₁ tSafe : Int} (hb : b₀ ≤ b₁) (hsync : Restated.SynchronyFromWakeOutside M S x b₀ b₁)
    (hcatch : Restated.CatchUpOnWakeOutside M S x b₀ b₁) (hmult : AwakeAtMultiples S Sched)
    (htd : Restated.TimeDiverges M x) (hmono : Sched.MonotoneCorruption) {tE : Int}
    (hrs : Restated.roundSleepinessW M S Sched tE) {r : Nat} {P : Block V}
    (hP : Restated.StableHandover M S Sched x r P) (hfix : Restated.fixedRoundSleepinessCountedW M S Sched r)
    (hlt : Restated.longTermConditionUpToW M S Sched r tSafe)
    (htE : tE ≤ M.opening S.E S.hc r) (hgst : S.E.t_GST ≤ (M.a S.hc S.E.Δ r)) (hη : S.hc.η_SG ≤ r)
    (hb₀ : Restated.periodAfterRound M S r b₀) (hb₁ : Restated.periodBeforeExpiry M S r b₁)
    (hR : ∀ q : Nat, r + 2 ≤ q → q ≤ r + S.hc.η_SG → Restated.RoundAttestsAbove M S Sched x r P q)
    {ρ : Nat} (hρ₁ : r + S.hc.η_SG + 1 ≤ ρ) (hρs : (Restated.Vocabulary.Execution.Setup.a M S ρ) ≤ tSafe)
    (hA : ∀ q : Nat, r + S.hc.η_SG + 1 ≤ q → q < ρ → Restated.RoundAttestsAll M S Sched x P q) :
    Restated.RoundAttestsAll M S Sched x P ρ := by
  intro n hn u hu hun a ha
  obtain ⟨nr, hnr, ns, rec, hD⟩ := ha
  have hd := S.E.Δ_pos
  have hη1 : (1 : Nat) ≤ S.hc.η_SG := S.hc.η_SG_ge_one
  obtain ⟨n₁, hn₁⟩ := Restated.exists_tickStepAt facts x htd (Restated.action_pos facts S (r + 1))
  obtain ⟨hn₁1, -⟩ := Restated.tickStepAt_time facts x hn₁
  obtain ⟨hnt1, hnt0⟩ := Restated.tickStepAt_time facts x hn
  have hρa : (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) < (Restated.Vocabulary.Execution.Setup.a M S ρ) := by
    have h1 := Restated.healA_succ facts S (r + 1)
    have h2 := twelve_delta_le_wAttest_kit S
    have h3 : (Restated.Vocabulary.Execution.Setup.a M S (r + 1 + 1)) ≤ (Restated.Vocabulary.Execution.Setup.a M S ρ) := Restated.healA_mono facts S (by omega)
    have h4 : (Restated.Vocabulary.Execution.Setup.a M S (r + 1 + 1)) = (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) + wAttest S := h1
    linarith
  have hk : n₁ + 1 ≤ n := by
    by_contra hcon
    have h1 := Restated.time_mono_int facts S Sched x (show n + 1 ≤ n₁ + 1 by omega)
    linarith
  have hvc := Restated.votesClassified_upToSafe_rule facts S Sched x hexec hP hn₁ hk hR
    (fun q hq hSq => hA q hq (by
      by_contra hcon
      have := Restated.healA_mono facts S (Nat.le_of_not_lt hcon)
      have h' : (Restated.Vocabulary.Execution.Setup.a M S ρ) ≤ (Restated.Vocabulary.Execution.Setup.a M S q) := this
      linarith))
  have hltn := Restated.longTermConditionUpToW_mono facts S Sched r hmono (show (x[n].time : Int) ≤ tSafe by
    linarith) hlt
  have hun' : Restated.HonestThrough M Sched x n u :=
    Restated.honestThrough_of_time_le facts hun (Restated.time_mono_int facts S Sched x (Nat.le_succ n))
  have hawT : u ∈ Sched.awakeThroughout (M.early S.E S.hc ρ .g2 - S.E.Δ) ((Restated.Vocabulary.Execution.Setup.a M S ρ)) :=
    hu
  obtain ⟨hFc, -⟩ := Restated.honest_roots_of_classified facts S Sched x hexec hmono hvc hltn hk hun'
  by_cases hPF : Block.Preceq P (x[n][u].st).st.core.F
  · have hPr := preceq_trans_Preceq hPF (Restated.F_preceq_fgRoot_sts facts S Sched x n u)
    exact ⟨fun C hC hconf =>
        Restated.attest_covers_of_fgRoot facts S Sched x hexec hun hPr nr hnr (ns, rec, a) hD C hC hconf,
      fun h root tmo hvote C hC hCroot =>
        Restated.attest_heightPair_compatible_of_fgRoot facts S Sched x hexec hn hun hPr nr hnr
          (ns, rec, a) hD h root tmo hvote C hC hCroot⟩
  · have hFP : Block.Preceq (x[n][u].st).st.core.F P :=
    (compatible_cases (compatible_iff_Compatible.mp hFc)).resolve_left hPF
    have hb₀' : (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) + S.E.Δ ≤ b₀ := hb₀
    have hgst₁ : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) := le_trans hgst (Restated.healA_mono facts S (Nat.le_succ r))
    have hρq : ρ - 1 + 1 = ρ := by omega
    have hdlAll : ∀ p : Protocol.Phase,
        M.domain S.E S.hc ρ p < (Restated.Vocabulary.Execution.Setup.a M S ρ) := by
      intro p
      have h := (Restated.domain_facts_att facts S (ρ - 1) p).2.2.2.2
      rw [hρq] at h
      exact h
    have hgr : ∀ (p : Protocol.Phase) (m : Nat),
        Restated.stepBeforeInstant M x m (M.domain S.E S.hc ρ p) →
        M.gradeBool S.E (M.gradeView (M.toHealing (x[m][u].st).st.core))
          (x[m][u].st).st.core.F S.hc.η_SG ρ (M.early S.E S.hc ρ p)
          (M.late S.E S.hc ρ p) P ⇢ true := by
      intro p m hm
      have hmd := Restated.time_of_stepBefore_domain facts S Sched x htd (show 1 ≤ ρ by omega) hm
      have hdl := hdlAll p
      have hmn : (x[m].time : Int) < (x[n].time : Int) := by linarith
      have hum : Restated.HonestThrough M Sched x m u := Restated.honestThrough_of_time_le facts hun' (le_of_lt hmn)
      obtain ⟨g, hg⟩ := facts.gr.gradeBool_nonempty S.E
        (M.gradeView (M.toHealing (x[m][u].st).st.core)) (x[m][u].st).st.core.F S.hc.η_SG ρ
        (M.early S.E S.hc ρ p) (M.late S.E S.hc ρ p) P
      suffices hgt : g = true by rw [hgt] at hg; exact hg
      clear hρq hdlAll hdl
      obtain ⟨q, rfl⟩ : ∃ q : Nat, ρ = q + 1 := ⟨ρ - 1, by omega⟩
      have hsucc := Restated.healA_succ facts S q
      by_cases hqe : q = r + S.hc.η_SG
      ·
        subst hqe
        have h1 := Restated.early_g2_eq_healA facts S (r + S.hc.η_SG + 1)
        have hs1 := Restated.healA_succ facts S (r + S.hc.η_SG)
        have h12 := twelve_delta_le_wAttest_kit S
        have hb₁' : b₁ + S.E.Δ ≤ M.early S.E S.hc (r + S.hc.η_SG + 1) .g2 := hb₁
        have hra : (M.a S.hc S.E.Δ (r + 1)) ≤ (M.a S.hc S.E.Δ (r + S.hc.η_SG)) :=
          Restated.healA_mono facts S (by omega)
        have hra0 : (M.a S.hc S.E.Δ r) ≤ (M.a S.hc S.E.Δ (r + 1)) := Restated.healA_mono facts S (Nat.le_succ r)
        have hgst₀ : S.E.t_GST ≤ (M.a S.hc S.E.Δ r) := hgst
        have hta : (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) ≤ M.early S.E S.hc (r + S.hc.η_SG + 1) .g2 - S.E.Δ := by
          show (M.a S.hc S.E.Δ (r + 1)) ≤ _
          rw [h1]; linarith
        have hDl : deadlineOutside S b₀ b₁ (M.early S.E S.hc (r + S.hc.η_SG + 1) .g2 - S.E.Δ)
            ≤ M.early S.E S.hc (r + S.hc.η_SG + 1) .g2 - S.E.Δ + S.E.Δ :=
          deadline_le_of_after S (by rw [h1]; linarith) (by linarith)
        have hu' : u ∈ Sched.awakeThroughout (M.early S.E S.hc (r + S.hc.η_SG + 1) .g2 - S.E.Δ)
            (M.early S.E S.hc (r + S.hc.η_SG + 1) .g2 - S.E.Δ + S.E.Δ) :=
          awakeThroughout_sub Sched le_rfl
            (by show _ ≤ M.a S.hc S.E.Δ (r + S.hc.η_SG + 1); rw [h1]; linarith) hu
        exact Restated.graded_expiry_of_rounds (hη := by first | exact hη | exact le_trans hη (Nat.le_succ _) | exact le_trans hη (Nat.le_add_right _ _) | exact le_trans hη (by omega)) facts S Sched x hexec hb hsync hcatch hmult htd hmono hP hfix
          (by omega) le_rfl (fun q' h1 h2 => hR q' h1 (by omega)) hta hDl (le_of_eq (by ring)) hm hu' hum hmn
          hFP g hg
      ·
        have hq1 : r + S.hc.η_SG + 1 ≤ q := by omega
        have hopen : tE ≤ M.opening S.E S.hc (q + 1) :=
          le_trans htE (facts.gr.Sts_opening_mono S (show r ≤ q + 1 by omega))
        have hrq : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (Restated.Vocabulary.Execution.Setup.a M S q) := Restated.healA_mono facts S (show r ≤ q by omega)
        have hgq : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S q) := le_trans hgst hrq
        have hbq : b₁ ≤ (Restated.Vocabulary.Execution.Setup.a M S q) := by
          have h1 := Restated.lt_action_of_periodBeforeExpiry facts S hb₁
          have h2 : (Restated.Vocabulary.Execution.Setup.a M S (r + S.hc.η_SG + 1)) ≤ (Restated.Vocabulary.Execution.Setup.a M S q) := Restated.healA_mono facts S hq1
          linarith
        have he1 := Restated.early_g2_eq_healA facts S (q + 1)
        have hs1 := Restated.healA_succ facts S q
        have h12 := twelve_delta_le_wAttest_kit S
        have htaq : (Restated.Vocabulary.Execution.Setup.a M S q) ≤ M.early S.E S.hc (q + 1) .g2 - S.E.Δ := by
          show (M.a S.hc S.E.Δ q) ≤ _
          rw [he1]; linarith
        have hu' : u ∈ Sched.awakeThroughout (M.early S.E S.hc (q + 1) .g2 - S.E.Δ)
            (M.early S.E S.hc (q + 1) .g2 - S.E.Δ + S.E.Δ) :=
          awakeThroughout_sub Sched le_rfl
            (by show _ ≤ M.a S.hc S.E.Δ (q + 1); rw [he1]; linarith) hu
        have hηq : S.hc.η_SG ≤ q := Nat.le_trans hη (by omega)
        exact Restated.graded_after_of_round (hη := hηq) facts S Sched x hexec hb hsync hcatch hmult htd hmono hrs hopen hgq
          hbq (hA q hq1 (Nat.lt_succ_self q)) hm htaq (le_of_eq (by ring)) hu' hum hmn hFP g hg
    obtain ⟨hdpos, -⟩ := Restated.domain_facts_att facts S (ρ - 1) .g2
    rw [hρq] at hdpos
    obtain ⟨m₂, hm₂⟩ := Restated.exists_tickStepAt facts x htd hdpos
    have hm₂B := Restated.stepBeforeInstant_of_tickStepAt facts x hm₂
    have hg2 := hgr .g2 m₂ hm₂B
    obtain ⟨H, hH, hPH⟩ :=
      facts.gr.Sts_exists_mem_T_preceq_of_gradeBool _ _ _ _ _ _ _ _ true hg2 rfl
    have hPT : P ∈ (x[m₂][u].st).st.core.T := Restated.mem_T_of_preceq_sts facts S Sched x m₂ u
      (by rw [← facts.gr.Sts_gradeView_T]; exact hH) hPH
    obtain ⟨Pn, hPn, hPe⟩ := Restated.exists_named_of_mem_tree facts S Sched x m₂ u hPT
    have hm₂n : m₂ ≤ n := by
      have hmd := Restated.time_of_stepBefore_domain facts S Sched x htd (show 1 ≤ ρ by omega) hm₂B
      have hdl := hdlAll .g2
      exact le_of_lt (Restated.lt_of_time_lt facts S Sched x (by linarith))
    have hPnn : Pn ∈ (x[n][u].st).st.bodies :=
      of_decide_eq_true (Restated.processed_mono facts S Sched x u (NamedObject.block Pn) hm₂n
        (decide_eq_true hPn))
    have hroot := Restated.mem_filtered_or_root_of_classified facts S Sched x hexec hmono hvc hltn hk hun' hPnn
      hPe
    have hρ0 : 0 < ρ := by omega
    exact ⟨fun C hC hconf =>
        Restated.attest_covers_of_graded facts S Sched x hexec htd hρ0 hn hawT hun hgr hFc hroot
          nr hnr (ns, rec, a) hD C hC hconf,
      fun h root tmo hvote C hC hCroot =>
        Restated.attest_heightPair_compatible_of_graded facts S Sched x hexec htd hρ0 hn hawT hun hgr hFc
          hroot nr hnr (ns, rec, a) hD h root tmo hvote C hC hCroot⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- In an execution whose delivery is suspended on `[b₀, b₁)`, with round-level sleepiness from
    round `r`'s opening, GST at or before `S.a r`, the period between the delivery and the expiry of
    round `r + 1`'s attestations, the participation premise, the long-term condition at `tSafe`, and
    `Restated.StableHandover` for `P` at round `r`: `RoundAttestsAll` holds at every round `ρ` from
    `r + η_SG + 1` whose action instant is at or before `tSafe`. -/
theorem roundAttestsAll_afterPeriod (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE b₀ b₁ tSafe : Int) (r : Nat) (P : Block V)
    (hmono : Sched.MonotoneCorruption)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hsync : Restated.SynchronyFromWakeOutside M S x b₀ b₁)
    (hmult : AwakeAtMultiples S Sched)
    (hcatch : Restated.CatchUpOnWakeOutside M S x b₀ b₁)
    (htd : Restated.TimeDiverges M x)
    (hrs : Restated.roundSleepinessW M S Sched tE) (htE : tE ≤ M.opening S.E S.hc r)
    (hgst : S.E.t_GST ≤ (M.a S.hc S.E.Δ r)) (hη : S.hc.η_SG ≤ r)
    (hb₀ : Restated.periodAfterRound M S r b₀) (hb : b₀ ≤ b₁) (hb₁ : Restated.periodBeforeExpiry M S r b₁)
    (hfix : Restated.fixedRoundSleepinessCountedW M S Sched r)
    (hlt : Restated.longTermConditionUpToW M S Sched r tSafe)
    (hP : Restated.StableHandover M S Sched x r P) :
    ∀ ρ : Nat, r + S.hc.η_SG + 1 ≤ ρ → (M.a S.hc S.E.Δ ρ) ≤ tSafe →
      Restated.RoundAttestsAll M S Sched x P ρ := by
  intro ρ
  induction ρ using Nat.strong_induction_on with
  | _ ρ ih =>
      intro h1 h2
      have hsafe : (Restated.Vocabulary.Execution.Setup.a M S (r + S.hc.η_SG + 1)) ≤ tSafe := le_trans (Restated.healA_mono facts S h1) h2
      have hR := Restated.roundAttestsAbove_all (hη := by first | exact hη | exact le_trans hη (Nat.le_succ _) | exact le_trans hη (Nat.le_add_right _ _) | exact le_trans hη (by omega)) facts S Sched x hexec hsync hcatch hmult htd
        hmono hP hfix (Restated.longTermConditionUpToW_mono facts S Sched r hmono hsafe hlt)
        (le_trans hgst (Restated.healA_mono facts S (Nat.le_succ r))) hb₀
      exact Restated.roundAttestsAll_step (hη := by first | exact hη | exact le_trans hη (Nat.le_succ _) | exact le_trans hη (Nat.le_add_right _ _) | exact le_trans hη (by omega)) facts S Sched x hexec hb hsync hcatch hmult htd hmono
        hrs hP hfix hlt htE hgst hb₀ hb₁ hR h1 h2
        (fun q hq hqρ => ih q hqρ hq (le_trans (Restated.healA_mono facts S (le_of_lt hqρ)) h2))

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- On the premises of `roundAttestsAll_afterPeriod` and `S.a (r + η_SG + 1) ≤ tSafe`, with `n₁` the
    tick step at `S.a (r + 1)`: at every step `k` from `n₁ + 1` whose instant is at or before
    `tSafe`, every honest store's finalized and justified blocks are ancestors or descendants of
    `P`. -/
theorem honestRoots_upToSafe (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE b₀ b₁ tSafe : Int) (r : Nat) (P : Block V)
    (hmono : Sched.MonotoneCorruption)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hsync : Restated.SynchronyFromWakeOutside M S x b₀ b₁)
    (hmult : AwakeAtMultiples S Sched)
    (hcatch : Restated.CatchUpOnWakeOutside M S x b₀ b₁)
    (htd : Restated.TimeDiverges M x)
    (hrs : Restated.roundSleepinessW M S Sched tE) (htE : tE ≤ M.opening S.E S.hc r)
    (hgst : S.E.t_GST ≤ (M.a S.hc S.E.Δ r)) (hη : S.hc.η_SG ≤ r)
    (hb₀ : Restated.periodAfterRound M S r b₀) (hb : b₀ ≤ b₁) (hb₁ : Restated.periodBeforeExpiry M S r b₁)
    (hfix : Restated.fixedRoundSleepinessCountedW M S Sched r)
    (hlt : Restated.longTermConditionUpToW M S Sched r tSafe)
    (hsafe : (M.a S.hc S.E.Δ (r + S.hc.η_SG + 1)) ≤ tSafe)
    (hP : Restated.StableHandover M S Sched x r P)
    {n₁ : Nat} (hn₁ : Restated.tickStepAt M x n₁ ((Restated.Vocabulary.Execution.Setup.a M S (r + 1)))) :
    ∀ k : Nat, n₁ + 1 ≤ k → (x[k].time : Int) ≤ tSafe →
      ∀ w : V, Restated.HonestThrough M Sched x k w →
        Block.Compatible P (x[k][w].st).st.core.F ∧ Block.Compatible P (x[k][w].st).st.core.J := by
  intro k hk hkt w hw
  have hR := Restated.roundAttestsAbove_all (hη := by first | exact hη | exact le_trans hη (Nat.le_succ _) | exact le_trans hη (Nat.le_add_right _ _) | exact le_trans hη (by omega)) facts S Sched x hexec hsync hcatch hmult htd
    hmono hP hfix (Restated.longTermConditionUpToW_mono facts S Sched r hmono hsafe hlt)
    (le_trans hgst (Restated.healA_mono facts S (Nat.le_succ r))) hb₀
  have hA := Restated.roundAttestsAll_afterPeriod (hη := by first | exact hη | exact le_trans hη (Nat.le_succ _) | exact le_trans hη (Nat.le_add_right _ _) | exact le_trans hη (by omega)) facts S Sched x tE b₀ b₁ tSafe r P hmono hexec hsync hmult
     hcatch htd hrs htE hgst hb₀ hb hb₁ hfix hlt hP
  have hvc := Restated.votesClassified_upToSafe_rule facts S Sched x hexec hP hn₁ hk hR
    (fun q hq hSq => hA q hq (le_trans hSq hkt))
  exact Restated.honest_roots_of_classified facts S Sched x hexec hmono hvc
    (Restated.longTermConditionUpToW_mono facts S Sched r hmono hkt hlt) hk hw

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Let step `k` be the tick at slot `s`'s confirmation instant, in round `q + 1`, and `w` awake and
    not held at round `q + 1`'s grade-2 domain instant, with every tick of `w` at that instant
    having an outcome. If the grade test of `P` for round `q + 1` can return `true` on `w`'s store
    at the last step before that instant, and `w`'s finalized block after `k` steps is an ancestor
    of `P` and its justified block is on one chain with `P`, then for every outcome `c` of `w`'s
    cache update at the tick, every stable root the grade contract of `c` can return is on one chain
    with `P`. -/
theorem stableRoot_compatible_of_graded (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (htd : Restated.TimeDiverges M x) {P : Block V} {w : V} {k : Nat}
    {s : Slot} (hks : Restated.tickStepAt M x k (M.confirmation_time S.E s)) {q : Nat}
    (hq : (M.round_of S.hc (S.E.slotOf (M.confirmation_time S.E s))) = q + 1)
    (hu : w ∈ Sched.awake (M.domain S.E S.hc (q + 1) .g2) \
      Sched.adv (M.domain S.E S.hc (q + 1) .g2))
    (hgr : ∀ m : Nat, Restated.stepBeforeInstant M x m (M.domain S.E S.hc (q + 1) .g2) →
      M.gradeBool S.E (M.gradeView (M.toHealing (x[m][w].st).st.core))
        (x[m][w].st).st.core.F S.hc.η_SG (q + 1) (M.early S.E S.hc (q + 1) .g2)
        (M.late S.E S.hc (q + 1) .g2) P ⇢ true)
    (hFk : Block.Preceq (x[k][w].st).st.core.F P)
    (hJk : Block.Compatible P (x[k][w].st).st.core.J)
    (hne : ∀ m : Nat, Restated.tickStepAt M x m (M.domain S.E S.hc (q + 1) .g2) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) w (Record.wakeStage M Sched (M.domain S.E S.hc (q + 1) .g2) x[m] w)
          (M.domain S.E S.hc (q + 1) .g2) ⇢ out) :
    ∀ c : M.Cache, M.onPhaseTick S.E S.hc (M.toHealing (x[k][w].st).st.core)
        (M.confirmation_time S.E s) (x[k][w].st).cache ⇢ c →
    ∀ G : Block V,
      (M.gradeContract c).stableRoot S.E S.hc
          (M.toHealing (M.ns_setClock S.E (x[k][w].st).st
            (M.confirmation_time S.E s)).core)
          ((M.round_of S.hc) (M.ns_setClock S.E (x[k][w].st).st
            (M.confirmation_time S.E s)).core.s) ⇢ some G →
      Block.Compatible P G := by
  intro c hc G hG
  obtain ⟨hk1, -⟩ := Restated.tickStepAt_time facts x hks
  rw [facts.hd.Sts_setClock_core_s, hq] at hG
  obtain ⟨hdpos, hdvd, hdρ, -, -⟩ := Restated.domain_facts_att facts S q .g2
  have hτpos : (0 : Int) ≤ M.confirmation_time S.E s := by
    rw [← hk1]; exact Int.natCast_nonneg _
  have hdτ : M.domain S.E S.hc (q + 1) .g2 < M.confirmation_time S.E s := by
    by_contra hcon
    have hle : M.confirmation_time S.E s
        < slotStart S.E.Δ ((M.opening_slot S.hc (q + 1))) := by
      have hdom := facts.gr.gammaNeg1_eq_domain_g2_succ S q
      have hcon' := not_lt.mp hcon
      linarith [S.E.Δ_pos]
    have hsl := slotOf_lt_of_lt_slotStart S hτpos hle
    have hro := Restated.round_of_le_of_lt_opening_slot_sr facts S hsl
    rw [hq] at hro
    exact Nat.not_succ_le_self q hro
  have hPF : ∀ j : Nat, j ≤ k → Block.compatible P (x[j][w].st).st.core.F = true :=
    fun j hj => compatible_of_cases (Or.inr (preceq_trans_Preceq (Restated.F_mono facts S Sched x w hj) hFk))
  have hst : Block.compatible P (M.toHealing (M.ns_setClock S.E (x[k][w].st).st
      (M.confirmation_time S.E s)).core).toFG.F = true := by
    rw [facts.hd.setClock_toHealing_F]; exact hPF k le_rfl
  obtain ⟨e, he, hPe⟩ := Restated.tickFrame_phase_preceq_of_graded facts S Sched x htd hdpos hdvd hdρ hks hq
    hdτ hu hgr hPF _ hst hne c hc
  rw [facts.gr.Sts_phaseResult_g2] at he
  have hfg : Block.Compatible P (M.get_fg_root (M.toHealing (M.ns_setClock S.E
      (x[k][w].st).st (M.confirmation_time S.E s)).core).toFG) := by
    rcases facts.fc.get_fg_root_eq_J_or_F (M.ns_setClock S.E (x[k][w].st).st
        (M.confirmation_time S.E s)).core with h | h
    · rw [h, facts.hd.setClock_core_J]; exact hJk
    · rw [h, facts.hd.setClock_core_F]; exact compatible_iff_Compatible.mpr (hPF k le_rfl)
  exact Restated.stableRoot_compatible_of_frame facts c S.E S.hc _ (q + 1) he hPe hfg hG

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Let step `k` be the tick at slot `s`'s confirmation instant, strictly after `S.a (r + 1)` and at
    or before `tSafe`, and `w` a member of `activeRoundWThroughNext S Sched r` honest through
    `k + 1` and awake from `S.a r − wAttest S` to that instant, whose finalized block after `k`
    steps is an ancestor of `P` and whose justified block is on one chain with `P`. Under the
    premises of the period and after it, for every outcome `c` of `w`'s cache update at the tick,
    every stable root the grade contract of `c` can return is on one chain with `P`. -/
theorem stableRoot_compatible_upToSafe (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {b₀ b₁ tSafe : Int} (hb : b₀ ≤ b₁) (hsync : Restated.SynchronyFromWakeOutside M S x b₀ b₁)
    (hcatch : Restated.CatchUpOnWakeOutside M S x b₀ b₁) (hmult : AwakeAtMultiples S Sched)
    (htd : Restated.TimeDiverges M x) (hmono : Sched.MonotoneCorruption) {tE : Int}
    (hrs : Restated.roundSleepinessW M S Sched tE) {r : Nat} {P : Block V}
    (hP : Restated.StableHandover M S Sched x r P) (hfix : Restated.fixedRoundSleepinessCountedW M S Sched r)
    (htE : tE ≤ M.opening S.E S.hc r) (hgst : S.E.t_GST ≤ (M.a S.hc S.E.Δ r)) (hη : S.hc.η_SG ≤ r)
    (hb₀ : Restated.periodAfterRound M S r b₀) (hb₁ : Restated.periodBeforeExpiry M S r b₁)
    (hR : ∀ q : Nat, r + 2 ≤ q → q ≤ r + S.hc.η_SG → Restated.RoundAttestsAbove M S Sched x r P q)
    (hA : ∀ q : Nat, r + S.hc.η_SG + 1 ≤ q → (Restated.Vocabulary.Execution.Setup.a M S q) ≤ tSafe → Restated.RoundAttestsAll M S Sched x P q)
    {w : V} (hwA : w ∈ Restated.activeRoundWThroughNext M S Sched r) {k : Nat} {s : Slot}
    (hks : Restated.tickStepAt M x k (M.confirmation_time S.E s))
    (hwr : w ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S r) - wAttest S) (x[k + 1].time : Int))
    (hwk : Restated.HonestThrough M Sched x (k + 1) w)
    (hτ₁ : (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) < M.confirmation_time S.E s)
    (hτ₂ : M.confirmation_time S.E s ≤ tSafe)
    (hFk : Block.Preceq (x[k][w].st).st.core.F P)
    (hJk : Block.Compatible P (x[k][w].st).st.core.J) :
    ∀ c : M.Cache, M.onPhaseTick S.E S.hc (M.toHealing (x[k][w].st).st.core)
        (M.confirmation_time S.E s) (x[k][w].st).cache ⇢ c →
    ∀ G : Block V,
      (M.gradeContract c).stableRoot S.E S.hc
          (M.toHealing (M.ns_setClock S.E (x[k][w].st).st
            (M.confirmation_time S.E s)).core)
          ((M.round_of S.hc) (M.ns_setClock S.E (x[k][w].st).st
            (M.confirmation_time S.E s)).core.s) ⇢ some G →
      Block.Compatible P G := by
  have hd := S.E.Δ_pos
  obtain ⟨hk1, hk0⟩ := Restated.tickStepAt_time facts x hks
  have hρ'₁ : r + 1 ≤ (M.round_of S.hc (S.E.slotOf (M.confirmation_time S.E s))) := by
    rw [← Restated.round_of_slotOf_action facts S (r + 1)]
    exact Restated.roundAt_mono_sr facts S (le_of_lt hτ₁)
  obtain ⟨q, hq⟩ : ∃ q : Nat,
      (M.round_of S.hc (S.E.slotOf (M.confirmation_time S.E s))) = q + 1 :=
    ⟨(M.round_of S.hc (S.E.slotOf (M.confirmation_time S.E s))) - 1,
      (Nat.sub_add_cancel (le_trans (Nat.succ_le_succ (Nat.zero_le r)) hρ'₁)).symm⟩
  rw [hq] at hρ'₁
  obtain ⟨hdpos, hdvd, hdρ, hdlo, hdhi⟩ := Restated.domain_facts_att facts S q .g2
  have hτpos : (0 : Int) ≤ M.confirmation_time S.E s := by
    rw [← hk1]; exact Int.natCast_nonneg _
  have hdτ : M.domain S.E S.hc (q + 1) .g2 < M.confirmation_time S.E s := by
    by_contra hcon
    have hle : M.confirmation_time S.E s
        < slotStart S.E.Δ ((M.opening_slot S.hc (q + 1))) := by
      have hdom := facts.gr.gammaNeg1_eq_domain_g2_succ S q
      have hcon' := not_lt.mp hcon
      linarith
    have hsl := slotOf_lt_of_lt_slotStart S hτpos hle
    have hro := Restated.round_of_le_of_lt_opening_slot_sr facts S hsl
    rw [hq] at hro
    exact Nat.not_succ_le_self q hro
  have hearly := Restated.early_g2_eq_healA facts S (q + 1)
  have hsucc := Restated.healA_succ facts S q
  have hW12 := twelve_delta_le_wAttest_kit S
  have hrq : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (Restated.Vocabulary.Execution.Setup.a M S q) := Restated.healA_mono facts S (by omega)
  have hdlo' : (Restated.Vocabulary.Execution.Setup.a M S r) - wAttest S ≤ M.domain S.E S.hc (q + 1) .g2 := by
    have h1 : (M.a S.hc S.E.Δ (q + 1)) = (M.a S.hc S.E.Δ q) + wAttest S := hsucc
    have h2 : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (M.a S.hc S.E.Δ q) := hrq
    have h3 : M.early S.E S.hc (q + 1) .g2 - S.E.Δ ≤
        M.domain S.E S.hc (q + 1) .g2 := hdlo
    rw [hearly] at h3
    have h4 : 0 ≤ wAttest S := by linarith
    linarith
  have hdk : M.domain S.E S.hc (q + 1) .g2 ≤ (x[k + 1].time : Int) := by
    rw [hk1]; exact le_of_lt hdτ
  have hu : w ∈ Sched.awake (M.domain S.E S.hc (q + 1) .g2) \
      Sched.adv (M.domain S.E S.hc (q + 1) .g2) :=
    Finset.mem_sdiff.2 ⟨mem_awake_of_awakeThroughout Sched hwr hdlo' hdk, hwk _ hdk⟩
  refine Restated.stableRoot_compatible_of_graded facts S Sched x htd hks hq hu ?_ hFk hJk
    (fun m hm => Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew
      hmono hm hdvd hu)
  intro m hm
  have hmd := Restated.time_of_stepBefore_domain facts S Sched x htd (Nat.succ_pos q) hm
  have hmk : (x[m].time : Int) < (x[k].time : Int) := by linarith
  have hwm : Restated.HonestThrough M Sched x m w := Restated.honestThrough_of_time_le facts hwk (by linarith)
  obtain ⟨g, hg⟩ := facts.gr.gradeBool_nonempty S.E
    (M.gradeView (M.toHealing (x[m][w].st).st.core)) (x[m][w].st).st.core.F S.hc.η_SG (q + 1)
    (M.early S.E S.hc (q + 1) .g2) (M.late S.E S.hc (q + 1) .g2) P
  suffices hgt : g = true by rw [hgt] at hg; exact hg
  have hgst₁ : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) := le_trans hgst (Restated.healA_mono facts S (Nat.le_succ r))
  have hb₀' : (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) + S.E.Δ ≤ b₀ := hb₀
  by_cases hq0 : q = r
  · subst hq0
    have hra : (Restated.Vocabulary.Execution.Setup.a M S q) ≤ (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) := Restated.healA_mono facts S (Nat.le_succ q)
    have hb₀r : (Restated.Vocabulary.Execution.Setup.a M S q) + S.E.Δ ≤ b₀ := by linarith
    have hw : w ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S q)) (x[m].time : Int) :=
      awakeThroughout_sub Sched (by linarith) (by linarith) hwr
    exact Restated.graded_base_reader (hη := by first | exact hη | exact le_trans hη (Nat.le_succ _) | exact le_trans hη (Nat.le_add_right _ _) | exact le_trans hη (by omega)) facts S Sched x hexec hsync hcatch hmult htd hmono hrs hP
      (le_trans htE (facts.gr.Sts_opening_mono S (Nat.le_succ q))) hgst hb₀r hm hw hwm hmk hFk g hg
  · by_cases hqη : q ≤ r + S.hc.η_SG
    · exact Restated.graded_period_of_rounds (hη := by first | exact hη | exact le_trans hη (Nat.le_succ _) | exact le_trans hη (Nat.le_add_right _ _) | exact le_trans hη (by omega)) facts S Sched x hexec hsync hcatch hmult htd hmono hP hfix hgst₁
        hb₀' (ρ := q + 1) (by omega) (by omega)
        (fun q' h1 h2 => hR q' h1 (by omega)) hm hwA hwm hmk hFk g hg
    · have hq1 : r + S.hc.η_SG + 1 ≤ q := by omega
      have hopen : tE ≤ M.opening S.E S.hc (q + 1) :=
        le_trans htE (facts.gr.Sts_opening_mono S (show r ≤ q + 1 by omega))
      have hgq : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S q) := le_trans hgst hrq
      have hbq : b₁ ≤ (Restated.Vocabulary.Execution.Setup.a M S q) := by
        have h1 := Restated.lt_action_of_periodBeforeExpiry facts S hb₁
        have h2 : (Restated.Vocabulary.Execution.Setup.a M S (r + S.hc.η_SG + 1)) ≤ (Restated.Vocabulary.Execution.Setup.a M S q) := Restated.healA_mono facts S hq1
        linarith
      have hqd : (Restated.Vocabulary.Execution.Setup.a M S q) + S.E.Δ ≤ M.domain S.E S.hc (q + 1) .g2 := by
        have := Restated.action_delta_le_early_succ_kit facts S q
        linarith [facts.gr.early_g2_lt_domain S (q + 1) .g2]
      have hqs : (Restated.Vocabulary.Execution.Setup.a M S q) ≤ tSafe := by linarith
      have hu' : w ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S q)) ((Restated.Vocabulary.Execution.Setup.a M S q) + S.E.Δ) :=
        awakeThroughout_sub Sched (by linarith) (by linarith) hwr
      have hηq : S.hc.η_SG ≤ q := Nat.le_trans hη (by omega)
      exact Restated.graded_after_of_round (hη := hηq) facts S Sched x hexec hb hsync hcatch hmult htd hmono hrs hopen hgq
        hbq (hA q hq1 hqs) hm le_rfl (Restated.action_delta_le_early_succ_kit facts S q) hu' hwm hmk hFk g hg

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Under the premises of the period and after it, with `S.a (r + η_SG + 1) ≤ tSafe` and `n₁` the
    tick step at `S.a (r + 1)`: if `w` is honest through a step `j` with
    `S.a (r + 1) + Δ ≤ x[j].time ≤ tSafe` and awake from `S.a r − wAttest S` to `x[j].time`, then at
    every step `k` from `n₁ + 1` to `j`, `P` is an ancestor of `w`'s finalized block or of its
    stable record. -/
theorem reader_upToSafe (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE b₀ b₁ tSafe : Int) (r : Nat) (P : Block V)
    (hmono : Sched.MonotoneCorruption)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hsync : Restated.SynchronyFromWakeOutside M S x b₀ b₁)
    (hmult : AwakeAtMultiples S Sched)
    (hcatch : Restated.CatchUpOnWakeOutside M S x b₀ b₁)
    (htd : Restated.TimeDiverges M x)
    (hrs : Restated.roundSleepinessW M S Sched tE) (htE : tE ≤ M.opening S.E S.hc r)
    (hgst : S.E.t_GST ≤ (M.a S.hc S.E.Δ r)) (hη : S.hc.η_SG ≤ r)
    (hb₀ : Restated.periodAfterRound M S r b₀) (hb : b₀ ≤ b₁) (hb₁ : Restated.periodBeforeExpiry M S r b₁)
    (hfix : Restated.fixedRoundSleepinessCountedW M S Sched r)
    (hlt : Restated.longTermConditionUpToW M S Sched r tSafe)
    (hsafe : (M.a S.hc S.E.Δ (r + S.hc.η_SG + 1)) ≤ tSafe)
    (hP : Restated.StableHandover M S Sched x r P)
    {n₁ : Nat} (hn₁ : Restated.tickStepAt M x n₁ ((Restated.Vocabulary.Execution.Setup.a M S (r + 1)))) {w : V} {j : Nat}
    (hwj : Restated.HonestThrough M Sched x j w)
    (hwr : w ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S r) - wAttest S) (x[j].time : Int))
    (hjA : (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) + S.E.Δ ≤ (x[j].time : Int))
    (hjt : (x[j].time : Int) ≤ tSafe) :
    ∀ k : Nat, n₁ + 1 ≤ k → k ≤ j →
      Block.Preceq P (x[k][w].st).st.core.F ∨
        Block.Preceq P (x[k][w].st).st.core.latest_stable := by
  have hd := S.E.Δ_pos
  obtain ⟨hn1, hn0⟩ := Restated.tickStepAt_time facts x hn₁
  have hra : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) := Restated.healA_mono facts S (Nat.le_succ r)
  have hb₀' : (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) + S.E.Δ ≤ b₀ := hb₀
  have hb₀r : (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ ≤ b₀ := by linarith
  have hwA : w ∈ Restated.activeRoundWThroughNext M S Sched r :=
    Restated.mem_activeRoundWThroughNext_of_reader facts S Sched hwr hjA
  have hlt₁ := Restated.longTermConditionUpToW_mono facts S Sched r hmono hsafe hlt
  have hR := Restated.roundAttestsAbove_all (hη := by first | exact hη | exact le_trans hη (Nat.le_succ _) | exact le_trans hη (Nat.le_add_right _ _) | exact le_trans hη (by omega)) facts S Sched x hexec hsync hcatch hmult htd
    hmono hP hfix hlt₁ (le_trans hgst hra) hb₀
  have hA := Restated.roundAttestsAll_afterPeriod (hη := by first | exact hη | exact le_trans hη (Nat.le_succ _) | exact le_trans hη (Nat.le_add_right _ _) | exact le_trans hη (by omega)) facts S Sched x tE b₀ b₁ tSafe r P hmono hexec hsync hmult
     hcatch htd hrs htE hgst hb₀ hb hb₁ hfix hlt hP
  have htE' : tE ≤ M.opening S.E S.hc (r + 1) :=
    le_trans htE (facts.gr.Sts_opening_mono S (Nat.le_succ r))
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
      intro hj
      exact Restated.reader_base (hη := by first | exact hη | exact le_trans hη (Nat.le_succ _) | exact le_trans hη (Nat.le_add_right _ _) | exact le_trans hη (by omega)) facts S Sched x hexec hsync hcatch hmult htd hmono hrs hP hlt₁ htE' hgst hb₀r
        hn₁ (awakeThroughout_sub Sched le_rfl (by linarith) hwr)
        (Restated.honestThrough_of_time_le facts hwj (Restated.time_mono_int facts S Sched x hj))
  | succ k hk ih =>
      intro hkj
      have hkj' : k ≤ j := Nat.le_of_succ_le hkj
      rcases ih hkj' with hF | hrec
      · exact Or.inl (preceq_trans_Preceq hF (Restated.F_mono facts S Sched x w (Nat.le_succ k)))
      · by_cases hPF : Block.Preceq P (x[k][w].st).st.core.F
        · exact Or.inl (preceq_trans_Preceq hPF (Restated.F_mono facts S Sched x w (Nat.le_succ k)))
        · right
          have hkt1 : (x[k + 1].time : Int) ≤ (x[j].time : Int) := Restated.time_mono_int facts S Sched x hkj
          have hkt0 : (x[k].time : Int) ≤ (x[k + 1].time : Int) :=
            Restated.time_mono_int facts S Sched x (Nat.le_succ k)
          have hkt : (x[k].time : Int) ≤ tSafe := by linarith
          have hvc := Restated.votesClassified_upToSafe_rule facts S Sched x hexec hP hn₁ hk hR
            (fun q hq hSq => hA q hq (le_trans hSq hkt))
          have hltk := Restated.longTermConditionUpToW_mono facts S Sched r hmono hkt hlt
          have hwk : Restated.HonestThrough M Sched x k w := Restated.honestThrough_of_time_le facts hwj (by linarith)
          obtain ⟨hFc, hJc⟩ := Restated.honest_roots_of_classified facts S Sched x hexec hmono hvc hltk hk hwk
          have hFP : Block.Preceq (x[k][w].st).st.core.F P :=
            (compatible_cases (compatible_iff_Compatible.mp hFc)).resolve_left hPF
          refine Restated.preceq_latest_stable_succ facts S Sched x w k hrec
            (fun s hks _ c hc G hG => ?_) (fun k τ u hl _ => facts.ndRun.tick_outcome_sts S Sched x hexec.idealization.root_injective hexec.honestRootsNew k τ u hl)
          obtain ⟨hk1, hk0⟩ := Restated.tickStepAt_time facts x hks
          have hnk : (x[n₁ + 1].time : Int) ≤ (x[k].time : Int) := Restated.time_mono_int facts S Sched x hk
          exact Restated.stableRoot_compatible_upToSafe (hη := by first | exact hη | exact le_trans hη (Nat.le_succ _) | exact le_trans hη (Nat.le_add_right _ _) | exact le_trans hη (by omega)) facts S Sched x hexec hb hsync hcatch hmult htd hmono
            hrs hP hfix htE hgst hb₀ hb₁ hR hA hwA hks
            (awakeThroughout_sub Sched le_rfl hkt1 hwr)
            (Restated.honestThrough_of_time_le facts hwj hkt1) (by linarith) (by linarith) hFP hJc
            c hc G hG

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- In an execution whose delivery is suspended on `[b₀, b₁)`, with round-level sleepiness from
    round `r`'s opening, GST at or before `S.a r`, the period between the delivery and the expiry of
    round `r + 1`'s attestations, the participation premise, the long-term condition at `tSafe`, and
    `Restated.StableHandover` for `P` at round `r`: every validator honest through a step `j` with
    `S.a (r + η_SG + 1) ≤ x[j].time ≤ tSafe`, awake from `S.a r − wAttest S` to `x[j].time`, has `P`
    as an ancestor of its stable output after `j` steps, or equal to it. -/
theorem stablePersists_untilSafe_ofHandover (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE b₀ b₁ tSafe : Int) (r : Nat) (P : Block V)
    (hmono : Sched.MonotoneCorruption)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hsync : Restated.SynchronyFromWakeOutside M S x b₀ b₁)
    (hmult : AwakeAtMultiples S Sched)
    (hcatch : Restated.CatchUpOnWakeOutside M S x b₀ b₁)
    (htd : Restated.TimeDiverges M x)
    (hrs : Restated.roundSleepinessW M S Sched tE) (htE : tE ≤ M.opening S.E S.hc r)
    (hgst : S.E.t_GST ≤ (M.a S.hc S.E.Δ r)) (hη : S.hc.η_SG ≤ r)
    (hb₀ : Restated.periodAfterRound M S r b₀) (hb : b₀ ≤ b₁) (hb₁ : Restated.periodBeforeExpiry M S r b₁)
    (hfix : Restated.fixedRoundSleepinessCountedW M S Sched r)
    (hlt : Restated.longTermConditionUpToW M S Sched r tSafe)
    (hP : Restated.StableHandover M S Sched x r P) :
    ∀ (w : V) (j : Nat), Restated.HonestThrough M Sched x j w →
      (M.a S.hc S.E.Δ (r + S.hc.η_SG + 1)) ≤ (x[j].time : Int) → (x[j].time : Int) ≤ tSafe →
      w ∈ Sched.awakeThroughout ((M.a S.hc S.E.Δ r) - wAttest S) (x[j].time : Int) →
      Block.Preceq P (M.get_stable (x[j][w].st).st.core) := by
  intro w j hwj hjlo hjt hwr
  have hd := S.E.Δ_pos
  have hη1 : (1 : Nat) ≤ S.hc.η_SG := S.hc.η_SG_ge_one
  have hsafe : (M.a S.hc S.E.Δ (r + S.hc.η_SG + 1)) ≤ tSafe := le_trans hjlo hjt
  have hjA : (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) + S.E.Δ ≤ (x[j].time : Int) := by
    have h1 := Restated.healA_succ facts S (r + 1)
    have h2 := twelve_delta_le_wAttest_kit S
    have h3 : (M.a S.hc S.E.Δ (r + 1 + 1)) ≤ (M.a S.hc S.E.Δ (r + S.hc.η_SG + 1)) :=
      Restated.healA_mono facts S (by omega)
    show (M.a S.hc S.E.Δ (r + 1)) + S.E.Δ ≤ _
    linarith
  obtain ⟨n₁, hn₁⟩ := Restated.exists_tickStepAt facts x htd (Restated.action_pos facts S (r + 1))
  obtain ⟨hn1, hn0⟩ := Restated.tickStepAt_time facts x hn₁
  have hjn : n₁ + 1 ≤ j := Restated.lt_of_time_lt facts S Sched x (by linarith)
  rcases Restated.reader_upToSafe (hη := by first | exact hη | exact le_trans hη (Nat.le_succ _) | exact le_trans hη (Nat.le_add_right _ _) | exact le_trans hη (by omega)) facts S Sched x tE b₀ b₁ tSafe r P hmono hexec hsync hmult
      hcatch htd hrs htE hgst hb₀ hb hb₁ hfix hlt hsafe hP hn₁ hwj hwr hjA hjt j hjn le_rfl
    with hF | hrec
  · exact preceq_trans_Preceq hF (facts.hd.finalized_preceq_get_stable _)
  · obtain ⟨hFc, -⟩ := Restated.honestRoots_upToSafe (hη := by first | exact hη | exact le_trans hη (Nat.le_succ _) | exact le_trans hη (Nat.le_add_right _ _) | exact le_trans hη (by omega)) facts S Sched x tE b₀ b₁ tSafe r P hmono hexec hsync hmult
       hcatch htd hrs htE hgst hb₀ hb hb₁ hfix hlt hsafe hP hn₁ j hjn hjt w hwj
    exact facts.hd.preceq_get_stable_of_record _ hrec hFc

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- `honestRoots_upToSafe` at the round `r + 1`, with the long-term condition replaced by
    `outsideAttestersUnderThird S Sched (r + 1)` and the adversary under a third up to `tSafe`: if
    `S.a (r + η_SG + 2) ≤ tSafe` and `n₁` is the tick step at `S.a (r + 2)`, then at every step from
    `n₁ + 1` whose instant is at or before `tSafe`, every honest store's finalized and justified
    blocks are ancestors or descendants of `P`. -/
theorem honestRoots_upToSafe_atPage (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE b₀ b₁ tSafe : Int) (r : Nat) (P : Block V)
    (hmono : Sched.MonotoneCorruption)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hsync : Restated.SynchronyFromWakeOutside M S x b₀ b₁)
    (hmult : AwakeAtMultiples S Sched)
    (hcatch : Restated.CatchUpOnWakeOutside M S x b₀ b₁)
    (htd : Restated.TimeDiverges M x)
    (hrs : Restated.roundSleepinessW M S Sched tE) (htE : tE ≤ M.opening S.E S.hc (r + 1))
    (hgst : S.E.t_GST ≤ (M.a S.hc S.E.Δ (r + 1))) (hη : S.hc.η_SG ≤ r)
    (hb₀ : Restated.periodAfterRound M S (r + 1) b₀) (hb : b₀ ≤ b₁)
    (hb₁ : Restated.periodBeforeExpiry M S (r + 1) b₁)
    (hfix : Restated.fixedRoundSleepinessCountedW M S Sched (r + 1))
    (hout : Restated.outsideAttestersUnderThird M S Sched (r + 1))
    (hadv : ∀ t : Int, t ≤ tSafe →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hsafe : (M.a S.hc S.E.Δ (r + S.hc.η_SG + 2)) ≤ tSafe)
    (hP : Restated.StableHandover M S Sched x (r + 1) P)
    {n₁ : Nat} (hn₁ : Restated.tickStepAt M x n₁ ((Restated.Vocabulary.Execution.Setup.a M S (r + 2)))) :
    ∀ k : Nat, n₁ + 1 ≤ k → (x[k].time : Int) ≤ tSafe →
      ∀ w : V, Restated.HonestThrough M Sched x k w →
        Block.Compatible P (x[k][w].st).st.core.F ∧ Block.Compatible P (x[k][w].st).st.core.J := by
  have heq : r + 1 + S.hc.η_SG + 1 = r + S.hc.η_SG + 2 := by
    rw [Nat.add_right_comm r 1 S.hc.η_SG]
  have hlt : Restated.longTermConditionUpToW M S Sched (r + 1) tSafe :=
    Restated.longTermConditionUpToW_of_thirds facts S Sched (r + 1) tSafe tSafe le_rfl hadv hout
  exact Restated.honestRoots_upToSafe (hη := by first | exact hη | exact le_trans hη (Nat.le_succ _) | exact le_trans hη (Nat.le_add_right _ _) | exact le_trans hη (by omega)) facts S Sched x tE b₀ b₁ tSafe (r + 1) P hmono hexec hsync hmult
    hcatch htd hrs htE hgst hb₀ hb hb₁ hfix hlt (by rw [heq]; exact hsafe) hP hn₁

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- `stablePersists_untilSafe_ofHandover` at the round `r + 1`, with the long-term condition
    replaced by the bound on the attesters outside `activeRoundWThroughNext S Sched (r + 1)` and the
    adversary under a third up to `tSafe`: every validator honest through a step `j` with
    `S.a (r + η_SG + 2) ≤ x[j].time ≤ tSafe`, awake from `S.a (r + 1) − wAttest S` to `x[j].time`,
    has `P` as an ancestor of its stable output after `j` steps, or equal to it. -/
theorem stablePersists_untilSafe_atPage (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE b₀ b₁ tSafe : Int) (r : Nat) (P : Block V)
    (hmono : Sched.MonotoneCorruption)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hsync : Restated.SynchronyFromWakeOutside M S x b₀ b₁)
    (hmult : AwakeAtMultiples S Sched)
    (hcatch : Restated.CatchUpOnWakeOutside M S x b₀ b₁)
    (htd : Restated.TimeDiverges M x)
    (hrs : Restated.roundSleepinessW M S Sched tE) (htE : tE ≤ M.opening S.E S.hc (r + 1))
    (hgst : S.E.t_GST ≤ (M.a S.hc S.E.Δ (r + 1))) (hη : S.hc.η_SG ≤ r)
    (hb₀ : Restated.periodAfterRound M S (r + 1) b₀) (hb : b₀ ≤ b₁)
    (hb₁ : Restated.periodBeforeExpiry M S (r + 1) b₁)
    (hfix : Restated.fixedRoundSleepinessCountedW M S Sched (r + 1))
    (hout : Restated.outsideAttestersUnderThird M S Sched (r + 1))
    (hadv : ∀ t : Int, t ≤ tSafe →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hP : Restated.StableHandover M S Sched x (r + 1) P) :
    ∀ (w : V) (j : Nat), Restated.HonestThrough M Sched x j w →
      (M.a S.hc S.E.Δ (r + S.hc.η_SG + 2)) ≤ (x[j].time : Int) → (x[j].time : Int) ≤ tSafe →
      w ∈ Sched.awakeThroughout ((M.a S.hc S.E.Δ (r + 1)) - wAttest S) (x[j].time : Int) →
      Block.Preceq P (M.get_stable (x[j][w].st).st.core) := by
  have heq : r + 1 + S.hc.η_SG + 1 = r + S.hc.η_SG + 2 := by
    rw [Nat.add_right_comm r 1 S.hc.η_SG]
  have hlt : Restated.longTermConditionUpToW M S Sched (r + 1) tSafe :=
    Restated.longTermConditionUpToW_of_thirds facts S Sched (r + 1) tSafe tSafe le_rfl hadv hout
  intro w j hwj hjlo hjt hwr
  exact Restated.stablePersists_untilSafe_ofHandover (hη := by first | exact hη | exact le_trans hη (Nat.le_succ _) | exact le_trans hη (Nat.le_add_right _ _) | exact le_trans hη (by omega)) facts S Sched x tE b₀ b₁ tSafe (r + 1) P hmono hexec hsync
    hmult hcatch htd hrs htE hgst hb₀ hb hb₁ hfix hlt hP w j hwj
    (by rw [heq]; exact hjlo) hjt hwr

end

end DecoupledConsensusModel.Sts.Restated
