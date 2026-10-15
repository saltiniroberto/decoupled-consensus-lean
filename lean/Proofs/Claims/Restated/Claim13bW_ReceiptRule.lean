import Proofs.Claims.Restated.Claim13bW_Receipt
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bStepGrade
import Model.Conditions.Claim13bInvariantActive
import Model.Conditions.Claim13bInvariantGrade1Rule

/-!
# Receipt of a round's attestations before a bound

`ReceivesRoundAttestationsBefore M S Sched x r v bound`: every attestation of round `r` an honest
validator sends at round `r`'s action tick reaches `v` strictly before `bound`. Then the ways it is
supplied: by synchrony or catch-up for a receiver awake from some `t₀ ≥ S.a r` through the deadline
of `t₀`, by synchrony alone for a receiver awake from `S.a r`, and inside a healing phase for a
member of `HonRound (r + 1)`, over a model `M : Record.Model V`.
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

/-- Every attestation `a` of round `r` that a validator `w` not held at the step's time sends at
    the tick step `k` of round `r`'s action instant, naming `w`, is delivered to `v` at a step `d`
    after `k` whose time is strictly before `bound`. -/
def ReceivesRoundAttestationsBefore (M : Record.Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (r : Round) (v : V) (bound : Int) : Prop :=
  ∀ (k : Nat) (w : V) (a : NamedAttestation V),
    Restated.tickStepAt M x k (Restated.Vocabulary.Execution.Setup.a M S r) →
    Restated.HonestSendAt M S x k (⟨w, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) →
    a.round = r → a.val_index = w →
    ∃ d : Nat, k < d ∧ x.lbl d = AtomicAction.deliver v ⟨w, NamedObject.attest a⟩ ∧
      (x[d].time : Int) < bound

/-- A larger bound keeps the receipt. -/
theorem ReceivesRoundAttestationsBefore.mono {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (Record.protocolOf M S) Sched} {r : Round} {v : V} {bound bound' : Int}
    (h : ReceivesRoundAttestationsBefore M S Sched x r v bound) (hle : bound ≤ bound') :
    ReceivesRoundAttestationsBefore M S Sched x r v bound' := by
  intro k w a hk hs hr hi
  obtain ⟨d, hkd, hl, hlt⟩ := h k w a hk hs hr hi
  exact ⟨d, hkd, hl, lt_of_lt_of_le hlt hle⟩

/-- Under synchrony and catch-up with a monotone `deadline`: a validator `v` awake at every time of
    `[t₀, deadline t₀]`, with `S.a r ≤ t₀ ≤ deadline t₀`, receives round `r`'s honest attestations
    strictly before `deadline t₀`. -/
theorem receivesRoundAttestationsBefore_of_awakeFrom_by (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (deadline : Int → Int)
    (hsync : Restated.SynchronyFromWakeBy M S x deadline)
    (hcatch : Restated.CatchUpOnWakeBy M S x deadline)
    (hmono : ∀ t t', t ≤ t' → deadline t ≤ deadline t')
    {r : Round} {v : V} {t₀ : Int}
    (ht₀ : Restated.Vocabulary.Execution.Setup.a M S r ≤ t₀) (hdl : t₀ ≤ deadline t₀)
    (haw : v ∈ Sched.awakeThroughout t₀ (deadline t₀)) :
    ReceivesRoundAttestationsBefore M S Sched x r v (deadline t₀) := by
  intro k w a hk hsend _ _
  have hkt : (x[k].time : Int) ≤ t₀ := by
    have := (Restated.tickStepAt_time facts x hk).2
    linarith
  exact delivered_before_of_honestSend_awakeFrom facts S Sched x deadline hsync hcatch hmono hsend
    hkt hdl haw

/-- The healing form: under `SynchronyFromWake` and `CatchUpOnWake`, a validator `v` awake at every
    time of `[t₀, t₀ + Δ]`, with `S.a r ≤ t₀` and GST at or before `t₀`, receives round `r`'s honest
    attestations strictly before `t₀ + Δ`. -/
theorem receivesRoundAttestationsBefore_of_awakeFrom (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hsync : Restated.SynchronyFromWake M S x) (hcatch : Restated.CatchUpOnWake M S x)
    {r : Round} {v : V} {t₀ : Int}
    (ht₀ : Restated.Vocabulary.Execution.Setup.a M S r ≤ t₀) (hgst : S.E.t_GST ≤ t₀)
    (haw : v ∈ Sched.awakeThroughout t₀ (t₀ + S.E.Δ)) :
    ReceivesRoundAttestationsBefore M S Sched x r v (t₀ + S.E.Δ) := by
  intro k w a hk hsend _ _
  have hkt : (x[k].time : Int) ≤ t₀ := by
    have := (Restated.tickStepAt_time facts x hk).2
    linarith
  exact delivered_before_of_honestSend_awakeFrom_healing facts S Sched x hsync hcatch hsend hkt hgst
    haw

/-- The form of the asynchrony pages: with synchrony and catch-up suspended on `[b₀, b₁)`, a
    validator `v` awake at every time of `[t₀, deadlineOutside S b₀ b₁ t₀]`, with `S.a r ≤ t₀`,
    receives round `r`'s honest attestations strictly before `deadlineOutside S b₀ b₁ t₀`. -/
theorem receivesRoundAttestationsBefore_of_awakeFrom_outside (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) {b₀ b₁ : Int}
    (hsync : Restated.SynchronyFromWakeOutside M S x b₀ b₁)
    (hcatch : Restated.CatchUpOnWakeOutside M S x b₀ b₁)
    {r : Round} {v : V} {t₀ : Int}
    (ht₀ : Restated.Vocabulary.Execution.Setup.a M S r ≤ t₀)
    (haw : v ∈ Sched.awakeThroughout t₀ (deadlineOutside S b₀ b₁ t₀)) :
    ReceivesRoundAttestationsBefore M S Sched x r v (deadlineOutside S b₀ b₁ t₀) :=
  receivesRoundAttestationsBefore_of_awakeFrom_by facts S Sched x (deadlineOutside S b₀ b₁) hsync
    hcatch (fun _ _ h => deadlineOutside_monotone S b₀ b₁ h) ht₀ (self_le_deadlineOutside S b₀ b₁ t₀) haw

/-- Synchrony alone: under `SynchronyFromWakeBy` with a `deadline`, a validator `v` awake at every
    time of `[S.a r, deadline (S.a r − 1)]` receives round `r`'s honest attestations strictly
    before `deadline (S.a r − 1)`, the deadline of the sends of round `r`'s action tick. -/
theorem receivesRoundAttestationsBefore_of_sync_by (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (deadline : Int → Int)
    (hsync : Restated.SynchronyFromWakeBy M S x deadline) {r : Round} {v : V}
    (haw : v ∈ Sched.awakeThroughout (Restated.Vocabulary.Execution.Setup.a M S r)
      (deadline (Restated.Vocabulary.Execution.Setup.a M S r - 1))) :
    ReceivesRoundAttestationsBefore M S Sched x r v
      (deadline (Restated.Vocabulary.Execution.Setup.a M S r - 1)) := by
  intro k w a hk hsend _ _
  obtain ⟨h1, h0⟩ := Restated.tickStepAt_time facts x hk
  have hk0 : (x[k].time : Int) = Restated.Vocabulary.Execution.Setup.a M S r - 1 := by linarith
  have haw' : v ∈ Sched.awakeThroughout (x[k + 1].time : Int) (deadline (x[k].time : Int)) := by
    rw [h1, hk0]; exact haw
  obtain ⟨d, hkd, hl, -, hlt⟩ := hsync k v _ hsend haw'
  exact ⟨d, hkd, hl, by rw [← hk0]; exact hlt⟩

/-- Synchrony alone, the healing form: under `SynchronyFromWake`, with GST at or before `S.a r`, a
    validator `v` awake at every time of `[S.a r, S.a r + Δ]` receives round `r`'s honest
    attestations strictly before `S.a r + Δ`. -/
theorem receivesRoundAttestationsBefore_of_sync (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hsync : Restated.SynchronyFromWake M S x) {r : Round} {v : V}
    (hgst : S.E.t_GST ≤ Restated.Vocabulary.Execution.Setup.a M S r)
    (haw : v ∈ Sched.awakeThroughout (Restated.Vocabulary.Execution.Setup.a M S r)
      (Restated.Vocabulary.Execution.Setup.a M S r + S.E.Δ)) :
    ReceivesRoundAttestationsBefore M S Sched x r v
      (Restated.Vocabulary.Execution.Setup.a M S r + S.E.Δ) := by
  have hle : max (Restated.Vocabulary.Execution.Setup.a M S r - 1) S.E.t_GST + S.E.Δ ≤
      Restated.Vocabulary.Execution.Setup.a M S r + S.E.Δ := by
    have : max (Restated.Vocabulary.Execution.Setup.a M S r - 1) S.E.t_GST ≤
        Restated.Vocabulary.Execution.Setup.a M S r := max_le (by linarith) hgst
    linarith
  refine ReceivesRoundAttestationsBefore.mono
    (receivesRoundAttestationsBefore_of_sync_by facts S Sched x (fun t => max t S.E.t_GST + S.E.Δ)
      hsync (awakeThroughout_mono Sched haw le_rfl hle)) hle

/-- A validator awake from one delay before the grade-2 first cutoff of the round of slot `s + 1` to
    slot `s`'s confirmation instant is awake from one delay before slot `s`'s start to that instant:
    the round of `s + 1` opens at or before slot `s + 1`. -/
theorem slotWindow_of_grade2Window (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    {s : Slot} {v : V}
    (h : v ∈ Sched.awakeThroughout (M.early S.E S.hc (M.round_of S.hc (s + 1)) .g2 - S.E.Δ)
      (M.confirmation_time S.E s)) :
    v ∈ Sched.awakeThroughout (slotStart S.E.Δ s - S.E.Δ) (M.confirmation_time S.E s) := by
  refine awakeThroughout_mono Sched h ?_ le_rfl
  have he := facts.gr.early_g2_eq S (M.round_of S.hc (s + 1))
  have ha := facts.sch.a_eq_confirmation_time S.hc S.E (M.round_of S.hc (s + 1))
  have hct := facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E
    (M.opening_slot S.hc (M.round_of S.hc (s + 1)))
  have ho := facts.gr.opening_slot_round_of_le_slot S.hc (s + 1)
  have hoI : ((M.opening_slot S.hc (M.round_of S.hc (s + 1)) : Nat) : Int) ≤ (s : Int) + 1 := by
    exact_mod_cast ho
  have hd := S.E.Δ_pos
  have hmul := mul_le_mul_of_nonneg_left hoI (by linarith : (0 : Int) ≤ 4 * S.E.Δ)
  rw [he, ha, ← hct, slotStart_closed, slotStart_closed]
  nlinarith

/-- Round `r`'s grade-1 window start is at or before its grade-1 late cutoff less `1 + 2Δ`. -/
theorem early_g1_sub_delta_le_late_g1_sub_rr (facts : Record.Facts M) (S : Setup V) (r : Round) :
    M.early S.E S.hc r .g1 - S.E.Δ ≤ M.late S.E S.hc r .g1 - 1 - 2 * S.E.Δ := by
  have h1 := facts.gr.early_g1_add_delta_le_early_g0 S r
  have h2 := facts.gr.late_g0_add_delta_le_late_g1 S r
  have h3 := facts.gr.early_le_late S.E S.hc r .g0
  have h4 : (0 : Int) + 1 ≤ S.E.Δ := Int.add_one_le_of_lt S.E.Δ_pos
  linarith

/-- Round `r`'s action instant is at or before round `r + 1`'s grade-1 late cutoff less `1 + 2Δ`. -/
theorem action_le_late_g1_succ_sub (facts : Record.Facts M) (S : Setup V) (r : Round) :
    Restated.Vocabulary.Execution.Setup.a M S r ≤ M.late S.E S.hc (r + 1) .g1 - 1 - 2 * S.E.Δ := by
  have hd1 : (1 : Int) ≤ S.E.Δ := S.E.Δ_pos
  have hlo := facts.gr.action_delta_le_early S S.hc.R_ge_three (Nat.lt_succ_self r)
  have h21 := facts.gr.early_g2_add_delta_le_early_g1 S (r + 1)
  have he0 := facts.gr.early_g1_add_delta_le_early_g0 S (r + 1)
  have hl0 := facts.gr.early_le_late S.E S.hc (r + 1) .g0
  have hl1 := facts.gr.late_g0_add_delta_le_late_g1 S (r + 1)
  show M.a S.hc S.E.Δ r ≤ _
  linarith

/-- Synchrony alone, to a later cutoff: under `SynchronyFromWake`, with GST at or before `S.a r`, a
    validator `v` awake from `S.a r` to a time `t₁` at or after `S.a r + Δ` receives round `r`'s
    honest attestations strictly before round `r + 1`'s first cutoff of phase `p`. -/
theorem receives_of_awake_from_action (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (hsync : Restated.SynchronyFromWake M S x)
    {r : Round} {v : V} {t₁ : Int} (p : Protocol.Phase)
    (hgst : S.E.t_GST ≤ Restated.Vocabulary.Execution.Setup.a M S r)
    (haw : v ∈ Sched.awakeThroughout (Restated.Vocabulary.Execution.Setup.a M S r) t₁)
    (ht₁ : Restated.Vocabulary.Execution.Setup.a M S r + S.E.Δ ≤ t₁) :
    ReceivesRoundAttestationsBefore M S Sched x r v (M.early S.E S.hc (r + 1) p) :=
  (receivesRoundAttestationsBefore_of_sync facts S Sched x hsync hgst
    (awakeThroughout_mono Sched haw le_rfl ht₁)).mono
    (le_trans (Restated.action_delta_le_early_succ facts S r) (Restated.early_g2_le_early facts S (r + 1) p))

/-- Inside a healing phase, synchrony alone: with every validator not held at a time of
    `[tGAT, tE]` awake at that time, corruption only growing, `tGAT ≤ S.a r`,
    `S.a (r + 1) ≤ tE` and GST at or before `S.a r`, a member `v` of `HonRound (r + 1)` receives
    round `r`'s honest attestations strictly before `S.a r + Δ`. -/
theorem receivesRoundAttestationsBefore_of_phase (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hsync : Restated.SynchronyFromWake M S x) (hmono : Sched.MonotoneCorruption)
    {tGAT tE : Int}
    -- Every validator not held by the adversary at a time of `[tGAT, tE]` is awake at that time.
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    {r : Round} {v : V} (hv : v ∈ Restated.HonRound M S Sched (r + 1))
    (hlo : tGAT ≤ Restated.Vocabulary.Execution.Setup.a M S r)
    (hhi : Restated.Vocabulary.Execution.Setup.a M S (r + 1) ≤ tE)
    (hgst : S.E.t_GST ≤ Restated.Vocabulary.Execution.Setup.a M S r) :
    ReceivesRoundAttestationsBefore M S Sched x r v
      (Restated.Vocabulary.Execution.Setup.a M S r + S.E.Δ) := by
  have hvS : v ∉ Sched.adv (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) :=
    (Finset.mem_sdiff.1 hv).2
  have hup : Restated.Vocabulary.Execution.Setup.a M S r + S.E.Δ ≤
      Restated.Vocabulary.Execution.Setup.a M S (r + 1) :=
    le_of_lt (lt_of_lt_of_le (Restated.action_delta_lt_domain_succ facts S r .g2)
      (facts.gr.domain_le_a S (r + 1) .g2))
  refine receivesRoundAttestationsBefore_of_sync facts S Sched x hsync hgst ?_
  refine mem_awakeThroughout_of_forall Sched ?_
  intro t h0 h1
  exact hphase t (le_trans hlo h0) (le_trans (le_trans h1 hup) hhi) v
    (fun h => hvS (hmono t _ (le_trans h1 hup) h))

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Every member of `HonRound (r + 1)` receives every attestation of round `r` an honest validator
    sends at round `r`'s action tick strictly before round `r + 1`'s grade-2 first cutoff, and every
    grade-1 performer of round `r + 1` receives them strictly before round `r + 1`'s grade-1 first
    cutoff. -/
def NextRoundReceipts (M : Record.Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (r : Round) : Prop :=
  (∀ v ∈ Restated.HonRound M S Sched (r + 1),
    ReceivesRoundAttestationsBefore M S Sched x r v (M.early S.E S.hc (r + 1) .g2)) ∧
  (∀ v ∈ Restated.grade1PerformersW M S Sched (r + 1),
    ReceivesRoundAttestationsBefore M S Sched x r v (M.early S.E S.hc (r + 1) .g1))

/-- From `NextRoundReceipts` at round `r`, a member of `HonRound (r + 1)` receives round `r`'s
    honest attestations strictly before round `r + 1`'s first cutoff of any phase. -/
theorem NextRoundReceipts.at (facts : Record.Facts M) {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (Record.protocolOf M S) Sched} {r : Round}
    (h : NextRoundReceipts M S Sched x r) {v : V} (hv : v ∈ Restated.HonRound M S Sched (r + 1))
    (p : Protocol.Phase) :
    ReceivesRoundAttestationsBefore M S Sched x r v (M.early S.E S.hc (r + 1) p) :=
  (h.1 v hv).mono (Restated.early_g2_le_early facts S (r + 1) p)

/-- From `NextRoundReceipts` at round `r`, a grade-1 performer of round `r + 1` receives round `r`'s
    honest attestations strictly before round `r + 1`'s grade-1 first cutoff. -/
theorem NextRoundReceipts.perf {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (Record.protocolOf M S) Sched} {r : Round}
    (h : NextRoundReceipts M S Sched x r) {v : V} (hv : v ∈ Restated.grade1PerformersW M S Sched (r + 1)) :
    ReceivesRoundAttestationsBefore M S Sched x r v (M.early S.E S.hc (r + 1) .g1) :=
  h.2 v hv

/-- Round `r`'s action instant is at or before one delay before round `r + 1`'s grade-1 first
    cutoff, and that cutoff is at or before round `r + 1`'s grade-1 domain instant. -/
theorem action_le_early_g1_succ_sub_delta_rr (facts : Record.Facts M) (S : Setup V) (r : Round) :
    Restated.Vocabulary.Execution.Setup.a M S r + S.E.Δ ≤ M.early S.E S.hc (r + 1) .g1 - S.E.Δ ∧
      M.early S.E S.hc (r + 1) .g1 ≤ M.domain S.E S.hc (r + 1) .g1 := by
  have hlo := facts.gr.action_delta_le_early S S.hc.R_ge_three (Nat.lt_succ_self r)
  have h21 := facts.gr.early_g2_add_delta_le_early_g1 S (r + 1)
  have hed := facts.gr.early_g1_le_domain_g1 S (r + 1)
  exact ⟨by show M.a S.hc S.E.Δ r + _ ≤ _; linarith, hed⟩

/-- A member of `HonRound (r + 1)` is awake at every time from one delay before round `r + 1`'s
    grade-2 first cutoff to that cutoff. -/
theorem awakeThroughout_early_g2_of_honRound_succ (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) {r : Round} {v : V} (hv : v ∈ Restated.HonRound M S Sched (r + 1)) :
    v ∈ Sched.awakeThroughout (M.early S.E S.hc (r + 1) .g2 - S.E.Δ)
      (M.early S.E S.hc (r + 1) .g2 - S.E.Δ + S.E.Δ) := by
  have hA : v ∈ Sched.awakeThroughout (M.early S.E S.hc (r + 1) .g2 - S.E.Δ)
      (M.a S.hc S.E.Δ (r + 1)) := (Finset.mem_sdiff.1 hv).1
  have he := facts.gr.early_g2_eq S (r + 1)
  have hd := S.E.Δ_pos
  exact awakeThroughout_mono Sched hA le_rfl (by linarith)

/-- Under `SynchronyFromWake` and `CatchUpOnWake`, with GST at or before round `r`'s action instant,
    `NextRoundReceipts` holds at round `r`: a member of `HonRound (r + 1)` is awake from one delay
    before round `r + 1`'s grade-2 first cutoff, at or after round `r`'s action instant, and catches
    up within one delay. -/
theorem nextRoundReceipts_of_catchUp (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hsync : Restated.SynchronyFromWake M S x) (hcatch : Restated.CatchUpOnWake M S x)
    {r : Round} (hgst : S.E.t_GST ≤ Restated.Vocabulary.Execution.Setup.a M S r) :
    NextRoundReceipts M S Sched x r := by
  refine ⟨fun v hv => ?_, fun v hv => ?_⟩
  · have hle := Restated.action_delta_le_early_succ facts S r
    have hd := S.E.Δ_pos
    have h := receivesRoundAttestationsBefore_of_awakeFrom facts S Sched x hsync hcatch
      (r := r) (t₀ := M.early S.E S.hc (r + 1) .g2 - S.E.Δ) (by linarith) (by linarith)
      (awakeThroughout_early_g2_of_honRound_succ facts S Sched hv)
    have he : M.early S.E S.hc (r + 1) .g2 - S.E.Δ + S.E.Δ = M.early S.E S.hc (r + 1) .g2 := by ring
    rw [he] at h
    exact h
  · obtain ⟨h1, h2⟩ := action_le_early_g1_succ_sub_delta_rr facts S r
    have hd := S.E.Δ_pos
    have hw := (Finset.mem_sdiff.1 hv).1
    have h := receivesRoundAttestationsBefore_of_awakeFrom facts S Sched x hsync hcatch
      (r := r) (t₀ := M.early S.E S.hc (r + 1) .g1 - S.E.Δ) (by linarith) (by linarith)
      (awakeThroughout_mono Sched hw le_rfl (by linarith))
    have he : M.early S.E S.hc (r + 1) .g1 - S.E.Δ + S.E.Δ = M.early S.E S.hc (r + 1) .g1 := by ring
    rw [he] at h
    exact h

/-- Inside a phase that reaches round `r + 1`'s action instant: with every validator not held at a
    time of `[tGAT, tHi]` awake at that time, corruption only growing, `tGAT ≤ S.a r`,
    `S.a (r + 1) ≤ tHi` and GST at or before `S.a r`, `NextRoundReceipts` holds at round `r`. -/
theorem nextRoundReceipts_of_phase (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hsync : Restated.SynchronyFromWake M S x) (hmono : Sched.MonotoneCorruption)
    {tGAT tHi : Int}
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tHi → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    {r : Round} (hlo : tGAT ≤ Restated.Vocabulary.Execution.Setup.a M S r)
    (hhi : Restated.Vocabulary.Execution.Setup.a M S (r + 1) ≤ tHi)
    (hgst : S.E.t_GST ≤ Restated.Vocabulary.Execution.Setup.a M S r) :
    NextRoundReceipts M S Sched x r := by
  refine ⟨fun v hv => (receivesRoundAttestationsBefore_of_phase facts S Sched x hsync hmono hphase hv
    hlo hhi hgst).mono (Restated.action_delta_le_early_succ facts S r), fun v hv => ?_⟩
  obtain ⟨h1, h2⟩ := action_le_early_g1_succ_sub_delta_rr facts S r
  have hd := S.E.Δ_pos
  have hdom := facts.gr.domain_le_action S (r + 1) .g1
  have hvS := (Finset.mem_sdiff.1 hv).2
  refine (receivesRoundAttestationsBefore_of_sync facts S Sched x hsync hgst ?_).mono (by linarith)
  refine mem_awakeThroughout_of_forall Sched ?_
  intro t h0 h3
  exact hphase t (le_trans hlo h0) (by linarith) v
    (fun h => hvS (hmono t _ (by linarith) h))

/-- Outside an asynchronous period `[b₀, b₁)`: with synchrony and catch-up suspended only on that
    period, GST at or before round `r`'s action instant and round `r + 1`'s grade-2 first cutoff at
    or before `b₀`, `NextRoundReceipts` holds at round `r`. -/
theorem nextRoundReceipts_of_outside (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {b₀ b₁ : Int}
    (hsync : Restated.SynchronyFromWakeOutside M S x b₀ b₁)
    (hcatch : Restated.CatchUpOnWakeOutside M S x b₀ b₁)
    {r : Round} (hgst : S.E.t_GST ≤ Restated.Vocabulary.Execution.Setup.a M S r)
    (hb : M.early S.E S.hc (r + 1) .g1 ≤ b₀) :
    NextRoundReceipts M S Sched x r := by
  have h21 := facts.gr.early_g2_add_delta_le_early_g1 S (r + 1)
  refine ⟨fun v hv => ?_, fun v hv => ?_⟩
  swap
  · obtain ⟨h1, h2⟩ := action_le_early_g1_succ_sub_delta_rr facts S r
    have hd := S.E.Δ_pos
    have hdl : deadlineOutside S b₀ b₁ (M.early S.E S.hc (r + 1) .g1 - S.E.Δ) =
        M.early S.E S.hc (r + 1) .g1 := by
      have hmax : max (M.early S.E S.hc (r + 1) .g1 - S.E.Δ) S.E.t_GST =
          M.early S.E S.hc (r + 1) .g1 - S.E.Δ := max_eq_left (by linarith)
      unfold deadlineOutside
      rw [hmax, if_pos (by linarith)]
      ring
    have hw := (Finset.mem_sdiff.1 hv).1
    have h := receivesRoundAttestationsBefore_of_awakeFrom_outside facts S Sched x hsync hcatch
      (r := r) (t₀ := M.early S.E S.hc (r + 1) .g1 - S.E.Δ) (by linarith)
      (by rw [hdl]; exact awakeThroughout_mono Sched hw le_rfl h2)
    rw [hdl] at h
    exact h
  have hle := Restated.action_delta_le_early_succ facts S r
  have hd := S.E.Δ_pos
  have hdl : deadlineOutside S b₀ b₁ (M.early S.E S.hc (r + 1) .g2 - S.E.Δ) =
      M.early S.E S.hc (r + 1) .g2 := by
    have hmax : max (M.early S.E S.hc (r + 1) .g2 - S.E.Δ) S.E.t_GST =
        M.early S.E S.hc (r + 1) .g2 - S.E.Δ := max_eq_left (by linarith)
    unfold deadlineOutside
    rw [hmax, if_pos (by linarith)]
    ring
  have hA := awakeThroughout_early_g2_of_honRound_succ facts S Sched hv
  have he : M.early S.E S.hc (r + 1) .g2 - S.E.Δ + S.E.Δ = M.early S.E S.hc (r + 1) .g2 := by ring
  rw [he] at hA
  have h := receivesRoundAttestationsBefore_of_awakeFrom_outside facts S Sched x hsync hcatch
    (r := r) (t₀ := M.early S.E S.hc (r + 1) .g2 - S.E.Δ) (by linarith) (by rw [hdl]; exact hA)
  rw [hdl] at h
  exact h

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Every late cutoff of round `r` is at or after `9Δ` before round `r`'s action instant. -/
theorem action_sub_nine_delta_le_late (facts : Record.Facts M) (S : Setup V) (r : Round)
    (p : Protocol.Phase) :
    M.a S.hc S.E.Δ r - 9 * S.E.Δ ≤ M.late S.E S.hc r p := by
  have he := facts.gr.early_g2_eq S r
  have h1 := facts.gr.early_g2_add_delta_le_early_g1 S r
  have h2 := facts.gr.early_g1_add_delta_le_early_g0 S r
  have h3 := facts.gr.early_le_late S.E S.hc r .g0
  have h4 := facts.gr.late_g0_add_delta_le_late_g1 S r
  have h5 := facts.gr.late_g1_add_delta_le_late_g2 S r
  have hd := S.E.Δ_pos
  cases p <;> linarith

/-- A member of `HonRound (r + 1)` is awake at every time of
    `[late (r + 1) p − 1 − 2Δ, late (r + 1) p − 1]`, for every phase `p`. -/
theorem awakeThroughout_late_of_honRound_succ (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) {r : Round} {v : V} (hv : v ∈ Restated.HonRound M S Sched (r + 1))
    (p : Protocol.Phase) :
    v ∈ Sched.awakeThroughout (M.late S.E S.hc (r + 1) p - 1 - 2 * S.E.Δ)
      (M.late S.E S.hc (r + 1) p - 1) := by
  have hA : v ∈ Sched.awakeThroughout (M.early S.E S.hc (r + 1) .g2 - S.E.Δ)
      (M.a S.hc S.E.Δ (r + 1)) := (Finset.mem_sdiff.1 hv).1
  have he := facts.gr.early_g2_eq S (r + 1)
  have hl := action_sub_nine_delta_le_late facts S (r + 1) p
  have hld := facts.gr.late_le_domain S (r + 1) p
  have hda := facts.gr.domain_le_a S (r + 1) p
  have hd : (1 : Int) ≤ S.E.Δ := S.E.Δ_pos
  exact awakeThroughout_mono Sched hA (by linarith) (by linarith)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- A member of `HonRound r` is awake at every time from round `r`'s grade-2 window start to
    round `r`'s action instant. -/
theorem awakeThroughout_of_mem_honRound (facts : Record.Facts M) {S : Setup V}
    {Sched : Schedule V} {r : Round} {v : V} (hv : v ∈ Restated.HonRound M S Sched r) :
    v ∈ Sched.awakeThroughout (M.early S.E S.hc r .g2 - S.E.Δ)
      (Restated.Vocabulary.Execution.Setup.a M S r) :=
  (Finset.mem_sdiff.1 hv).1

/-- A member of `HonRound r` is awake at round `r`'s action instant. -/
theorem awake_action_of_mem_honRound (facts : Record.Facts M) {S : Setup V}
    {Sched : Schedule V} {r : Round} {v : V} (hv : v ∈ Restated.HonRound M S Sched r) :
    v ∈ Sched.awake (Restated.Vocabulary.Execution.Setup.a M S r) := by
  have he := facts.gr.early_g2_eq S r
  have hd := S.E.Δ_pos
  have he' : M.early S.E S.hc r .g2 - S.E.Δ ≤ Restated.Vocabulary.Execution.Setup.a M S r := by
    show _ ≤ M.a S.hc S.E.Δ r
    linarith
  exact mem_awake_of_awakeThroughout Sched (awakeThroughout_of_mem_honRound facts hv) he' le_rfl

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- A member of `HonRound (r + 1)` is awake at every time from two delays and one before round
    `r + 1`'s late cutoff of a phase `p` to `p`'s domain instant, when that instant is at or before
    round `r + 1`'s action instant. -/
theorem awakeThroughout_late_domain_of_honRound_succ (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) {r : Round} {v : V} (hv : v ∈ Restated.HonRound M S Sched (r + 1))
    {p : Protocol.Phase}
    (hdom : M.domain S.E S.hc (r + 1) p ≤ Restated.Vocabulary.Execution.Setup.a M S (r + 1)) :
    v ∈ Sched.awakeThroughout (M.late S.E S.hc (r + 1) p - 1 - 2 * S.E.Δ)
      (M.domain S.E S.hc (r + 1) p) := by
  have he := facts.gr.early_g2_eq S (r + 1)
  have hl := action_sub_nine_delta_le_late facts S (r + 1) p
  have hd : (1 : Int) ≤ S.E.Δ := S.E.Δ_pos
  have hlo : M.early S.E S.hc (r + 1) .g2 - S.E.Δ ≤ M.late S.E S.hc (r + 1) p - 1 - 2 * S.E.Δ := by
    linarith
  exact awakeThroughout_mono Sched (awakeThroughout_of_mem_honRound facts hv) hlo hdom

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- A member of `HonRound r` is awake at every time of `[t, t']` for
    `S.a r − 12Δ ≤ t` and `t' ≤ S.a r`. -/
theorem awakeThroughout_sub_of_mem_honRound (facts : Record.Facts M) {S : Setup V}
    {Sched : Schedule V} {r : Round} {v : V} (hv : v ∈ Restated.HonRound M S Sched r) {t t' : Int}
    (hlo : Restated.Vocabulary.Execution.Setup.a M S r - 12 * S.E.Δ ≤ t)
    (hhi : t' ≤ Restated.Vocabulary.Execution.Setup.a M S r) :
    v ∈ Sched.awakeThroughout t t' := by
  have he := facts.gr.early_g2_eq S r
  have hlo' : M.early S.E S.hc r .g2 - S.E.Δ ≤ t := by
    have : M.a S.hc S.E.Δ r - 12 * S.E.Δ ≤ t := hlo
    linarith
  exact awakeThroughout_mono Sched (awakeThroughout_of_mem_honRound facts hv) hlo' hhi

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- From round `1` on, round `r`'s grade-2 window start, `S.a r − 12Δ`, is at or after time `0`. -/
theorem early_g2_sub_delta_nonneg_rr (facts : Record.Facts M) (S : Setup V) {r : Round}
    (hr : 1 ≤ r) : 0 ≤ M.early S.E S.hc r .g2 - S.E.Δ := by
  have he := facts.gr.early_g2_eq S r
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, (Nat.sub_add_cancel hr).symm⟩
  have hsucc := facts.gr.healA_succ_round S.hc S.E.Δ r'
  have ha0 : M.a S.hc S.E.Δ r' = M.confirmation_time S.E (M.opening_slot S.hc r') :=
    facts.sch.a_eq_confirmation_time S.hc S.E r'
  have hct := facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E (M.opening_slot S.hc r')
  have hss : 0 ≤ slotStart S.E.Δ (M.opening_slot S.hc r') := by
    rw [slotStart_closed]; have := S.E.Δ_pos; positivity
  have hd := S.E.Δ_pos
  have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
  have hRd : 12 * S.E.Δ ≤ 4 * S.E.Δ * (S.hc.R : Int) := by nlinarith
  rw [he, hsucc, ha0, ← hct]
  linarith

end

end DecoupledConsensusModel.Sts.Restated
