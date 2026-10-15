import Proofs.Claims.Restated.Claim13bW_ReceiptRule
import Model.Conditions.ClaimAsyncK_DeliveryUpTo
import Model.Conditions.Sts_Spec2Claims_ClaimStableThroughAsyncPeriod

/-!
# Catch-up on wake up to a bound, and the receipts it gives

`CatchUpOnWakeBefore M S x b₀`: catch-up on wake for the wakes whose deadline
`max t_w S.E.t_GST + S.E.Δ` is at most `b₀`, the companion of `SynchronyFromWakeBefore`. Under both, a
member of `HonRound (r + 1)` receives round `r`'s honest attestations before round `r + 1`'s grade-2
first cutoff when that cutoff is at most `b₀` and GST is at or before `S.a r`. Both forms come from
the asynchrony page's `SynchronyFromWakeOutside` and `CatchUpOnWakeOutside`. Stated over a model
`M : Record.Model V`.
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

/-- Catch-up on wake for the wakes whose deadline `max t_w S.E.t_GST + S.E.Δ` is at most `b₀`: a
    validator `w` that wakes at `t_w`, after an honest message was sent at step `k`, and stays awake
    through that deadline, receives the message from `t_w` on, strictly before the deadline. -/
def CatchUpOnWakeBefore (M : Record.Model V) (S : Setup V) {Sched : Schedule V}
    (x : AtomicExec (Record.protocolOf M S) Sched) (b₀ : Int) : Prop :=
  ∀ (k : Nat) (w : V) (sm : SignedMsg V (NamedObject V)) (t_w : Int),
    Restated.HonestSendAt M S x k sm →
    (x[k].time : Int) < t_w →
    w ∈ Sched.awake t_w → w ∉ Sched.awake (t_w - 1) →
    max t_w S.E.t_GST + S.E.Δ ≤ b₀ →
    w ∈ Sched.awakeThroughout t_w (max t_w S.E.t_GST + S.E.Δ) →
    ∃ d : Nat, k < d ∧ x.lbl d = AtomicAction.deliver w sm ∧
      t_w ≤ (x[d].time : Int) ∧ (x[d].time : Int) < max t_w S.E.t_GST + S.E.Δ

/-- A smaller bound keeps catch-up. -/
theorem CatchUpOnWakeBefore.mono {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (Record.protocolOf M S) Sched} {b b' : Int} (hb : b ≤ b')
    (h : CatchUpOnWakeBefore M S x b') : CatchUpOnWakeBefore M S x b :=
  fun k w sm t_w hsend hk hwa hws hle haw => h k w sm t_w hsend hk hwa hws (le_trans hle hb) haw

/-- A smaller bound keeps catch-up (the argument order of `SynchronyFromWakeBefore.monoU`). -/
theorem CatchUpOnWakeBefore.monoU {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (Record.protocolOf M S) Sched} {b b' : Int}
    (h : CatchUpOnWakeBefore M S x b') (facts : Record.Facts M) (hb : b ≤ b') :
    CatchUpOnWakeBefore M S x b :=
  CatchUpOnWakeBefore.mono hb h

/-- Under synchrony and catch-up up to `b₀`, an honest message sent at step `k` at or before `t₀`,
    with GST at or before `t₀` and `t₀ + Δ ≤ b₀`, is delivered strictly before `t₀ + Δ` to a
    validator awake at every time of `[t₀, t₀ + Δ]`. -/
theorem delivered_before_of_honestSend_awakeFrom_before (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) {b₀ : Int}
    (hsync : Restated.SynchronyFromWakeBefore M S x b₀) (hcatch : CatchUpOnWakeBefore M S x b₀)
    {k : Nat} {w : V} {sm : SignedMsg V (NamedObject V)} {t₀ : Int}
    (hsend : Restated.HonestSendAt M S x k sm) (hk : (x[k].time : Int) ≤ t₀) (hgst : S.E.t_GST ≤ t₀)
    (hb : t₀ + S.E.Δ ≤ b₀)
    (haw : w ∈ Sched.awakeThroughout t₀ (t₀ + S.E.Δ)) :
    ∃ d : Nat, k < d ∧ x.lbl d = AtomicAction.deliver w sm ∧ (x[d].time : Int) < t₀ + S.E.Δ := by
  have hΔ : (0 : Int) < S.E.Δ := S.E.Δ_pos
  have hmk : max (x[k].time : Int) S.E.t_GST ≤ t₀ := max_le hk hgst
  by_cases hA : w ∈ Sched.awakeThroughout (x[k + 1].time : Int) (max (x[k].time : Int) S.E.t_GST + S.E.Δ)
  · obtain ⟨d, hkd, hl, -, hlt⟩ := hsync k w sm hsend (by linarith) hA
    exact ⟨d, hkd, hl, by linarith⟩
  · have hu : ∃ u : Int, (x[k + 1].time : Int) ≤ u ∧ u ≤ max (x[k].time : Int) S.E.t_GST + S.E.Δ ∧
        w ∉ Sched.awake u := by
      by_contra hno
      push Not at hno
      exact hA (mem_awakeThroughout_of_forall Sched fun t h0 h1 => hno t h0 h1)
    obtain ⟨u, hu0, hu1, hu⟩ := hu
    have hut : u < t₀ := by
      by_contra hge
      push Not at hge
      exact hu (mem_awake_of_awakeThroughout Sched haw hge (by linarith))
    obtain ⟨t_w, hutw, htw, hwa, hws, hthr⟩ := exists_last_entrance Sched hut (by linarith) hu haw
    have hstep : (x[k].time : Int) ≤ (x[k + 1].time : Int) := by
      exact_mod_cast Record.time_mono M S Sched x (Nat.le_succ k)
    have hkt : (x[k].time : Int) < t_w := by omega
    have hmw : max t_w S.E.t_GST + S.E.Δ ≤ t₀ + S.E.Δ := by
      have : max t_w S.E.t_GST ≤ t₀ := max_le htw hgst
      linarith
    have hthr' : w ∈ Sched.awakeThroughout t_w (max t_w S.E.t_GST + S.E.Δ) :=
      awakeThroughout_mono Sched hthr le_rfl hmw
    obtain ⟨d, hkd, hl, -, hlt⟩ := hcatch k w sm t_w hsend hkt hwa hws (le_trans hmw hb) hthr'
    exact ⟨d, hkd, hl, by linarith⟩

/-- Under synchrony and catch-up up to `b₀`, a validator awake at every time of `[t₀, t₀ + Δ]`, with
    `S.a r ≤ t₀`, GST at or before `t₀` and `t₀ + Δ ≤ b₀`, receives round `r`'s honest attestations
    strictly before `t₀ + Δ`. -/
theorem receives_of_awakeFrom_before (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {b₀ : Int}
    (hsync : Restated.SynchronyFromWakeBefore M S x b₀) (hcatch : CatchUpOnWakeBefore M S x b₀)
    {r : Round} {v : V} {t₀ : Int} (ht₀ : Restated.Vocabulary.Execution.Setup.a M S r ≤ t₀)
    (hgst : S.E.t_GST ≤ t₀) (hb : t₀ + S.E.Δ ≤ b₀)
    (haw : v ∈ Sched.awakeThroughout t₀ (t₀ + S.E.Δ)) :
    ReceivesRoundAttestationsBefore M S Sched x r v (t₀ + S.E.Δ) := by
  intro k w a hk hsend _ _
  have hkt : (x[k].time : Int) ≤ t₀ := by
    have := (Restated.tickStepAt_time facts x hk).2
    linarith
  exact delivered_before_of_honestSend_awakeFrom_before facts S Sched x hsync hcatch hsend hkt hgst hb haw

/-- Under synchrony and catch-up up to `b₀`, with GST at or before `S.a r` and round `r + 1`'s
    grade-2 first cutoff at most `b₀`, `NextRoundReceipts` holds at round `r`. -/
theorem nextRoundReceipts_of_before (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {b₀ : Int}
    (hsync : Restated.SynchronyFromWakeBefore M S x b₀) (hcatch : CatchUpOnWakeBefore M S x b₀)
    {r : Round} (hgst : S.E.t_GST ≤ Restated.Vocabulary.Execution.Setup.a M S r)
    (hb : M.early S.E S.hc (r + 1) .g1 ≤ b₀) :
    NextRoundReceipts M S Sched x r := by
  have h21 := facts.gr.early_g2_add_delta_le_early_g1 S (r + 1)
  refine ⟨fun v hv => ?_, fun v hv => ?_⟩
  swap
  · intro k w a hk hsend _ _
    obtain ⟨h1, h2⟩ := Restated.action_le_early_g1_succ_sub_delta_rr facts S r
    have hd := S.E.Δ_pos
    have hw := (Finset.mem_sdiff.1 hv).1
    have hkt : (x[k].time : Int) ≤ M.early S.E S.hc (r + 1) .g1 - S.E.Δ := by
      have := (Restated.tickStepAt_time facts x hk).2
      linarith
    have e : M.early S.E S.hc (r + 1) .g1 - S.E.Δ + S.E.Δ = M.early S.E S.hc (r + 1) .g1 := by ring
    have h := delivered_before_of_honestSend_awakeFrom_before facts S Sched x hsync hcatch hsend hkt
      (by linarith) (by rw [e]; exact hb) (by rw [e]; exact awakeThroughout_mono Sched hw le_rfl h2)
    rw [e] at h
    exact h
  intro k w a hk hsend _ _
  have hle := Restated.action_delta_le_early_succ facts S r
  have hd := S.E.Δ_pos
  have hwin := Restated.awakeThroughout_early_g2_of_honRound_succ facts S Sched hv
  have hkt : (x[k].time : Int) ≤ M.early S.E S.hc (r + 1) .g2 - S.E.Δ := by
    have := (Restated.tickStepAt_time facts x hk).2
    linarith
  have e : M.early S.E S.hc (r + 1) .g2 - S.E.Δ + S.E.Δ = M.early S.E S.hc (r + 1) .g2 := by ring
  have h := delivered_before_of_honestSend_awakeFrom_before facts S Sched x hsync hcatch hsend hkt
    (by linarith) (by rw [e]; linarith) hwin
  rw [e] at h
  exact h

/-- Round `r`'s grade-1 first cutoff is at or before its action instant. -/
theorem early_g1_le_action_rb (facts : Record.Facts M) (S : Setup V) (r : Round) :
    M.early S.E S.hc r .g1 ≤ Restated.Vocabulary.Execution.Setup.a M S r := by
  have he := facts.gr.early_g1_eq S r
  have hd := S.E.Δ_pos
  show _ ≤ M.a S.hc S.E.Δ r
  linarith

/-- Round `r`'s grade-2 first cutoff is at or before its action instant. -/
theorem early_g2_le_action_rb (facts : Record.Facts M) (S : Setup V) (r : Round) :
    M.early S.E S.hc r .g2 ≤ Restated.Vocabulary.Execution.Setup.a M S r := by
  have he := facts.gr.early_g2_eq S r
  have hd := S.E.Δ_pos
  show _ ≤ M.a S.hc S.E.Δ r
  linarith

/-- Synchrony and catch-up outside `[b₀, b₁)` give catch-up up to `b₀`. -/
theorem catchUpOnWakeBefore_of_outside (S : Setup V) {Sched : Schedule V}
    {x : AtomicExec (Record.protocolOf M S) Sched} {b₀ b₁ : Int}
    (hcatch : Restated.CatchUpOnWakeOutside M S x b₀ b₁) : CatchUpOnWakeBefore M S x b₀ := by
  intro k w sm t_w hsend hk hwa hws hle haw
  have hd : deadlineOutside S b₀ b₁ t_w = max t_w S.E.t_GST + S.E.Δ := by
    unfold deadlineOutside; rw [if_pos hle]
  have h := hcatch k w sm t_w hsend hk hwa hws (by rw [hd]; exact haw)
  rw [hd] at h
  exact h

end

end DecoupledConsensusModel.Sts.Restated
