import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bStepKitRecord
import Proofs.Claims.Restated.Claim13bStepKitTick
import Proofs.Claims.Restated.Claim13bSyncView
import Proofs.Claims.Restated.ProcessedFlip
import Proofs.Claims.Restated.Projection
import Proofs.Claims.Restated.Redelivery
import Proofs.Claims.Restated.RunAll
import Proofs.Claims.Restated.SynchronyH
import Proofs.Claims.Restated.VocabularyAssumptionsLemmas
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_SGArrival
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bStepKitDelivery

/-!
# Clocks, deliveries and recorded attestations

How a store's clock follows real time, what a tick and a delivery step do to a validator's node
state, and when an attestation in a receiver's view is recorded in its store with the stamp of its
own clock, stated over a model `M : Record.Model V` and its facts `facts : Record.Facts M`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For `i ≤ j`, the time after `i` steps, read as an `Int`, is at most the time after `j` steps. -/
theorem time_mono_int (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {i j : Nat} (hij : i ≤ j) :
    (x[i].time : Int) ≤ (x[j].time : Int) := by
  exact_mod_cast Restated.time_mono facts S Sched x hij

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- After the tick at `τ` at step `k`, validator `w`'s store clock is `τ` or its store clock before
    step `k`. -/
private theorem clock_succ_of_tick (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (w : V) {k τ : Nat}
    (hl : x.lbl k = AtomicAction.tickAllAwake τ) :
    (x[k + 1][w].st).st.core.t = (τ : Int) ∨
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
    · refine Or.inl ?_
      rw [hx1, hst]
      exact (facts.nd.tick_clock (Setup.alwaysAwake S) w _ (τ : Int) out₁ hout).1
    · refine Or.inr ?_
      rw [hx1, hst, hwst]
  · refine Or.inr ?_
    have h2 : x[k + 1][w] = (tickAllAwakeUpdate Sched τ x[k] w' tk)[w] := by rw [hc]
    rw [h2, tickAllAwakeUpdate_getElem_st_of_not_react hv]

/-- After any number of steps, every validator's store clock is at or before the real time of that
    configuration. -/
theorem clock_le_time_sts (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (i : Nat) (w : V) :
    (x[i][w].st).st.core.t ≤ (x[i].time : Int) := by
  induction i with
  | zero =>
      have hst : x[0][w].st = M.initial (Setup.alwaysAwake S) w := Record.st_zero M S Sched x w
      have ht : x[0].time = 0 := x.init.1
      have h0 : (M.initial (Setup.alwaysAwake S) w).st.core.t = (0 : Int) :=
        facts.nd.initial_clock_eq_zero _ _
      rw [hst, ht, h0]
      norm_num
  | succ i ih =>
      have hmono : (x[i].time : Int) ≤ (x[i + 1].time : Int) :=
        Restated.time_mono_int facts S Sched x (Nat.le_succ i)
      cases hl : x.lbl i with
      | tickAllAwake τ =>
          obtain ⟨-, httime⟩ := Restated.tickAllAwake_time facts S Sched x hl
          rcases clock_succ_of_tick facts S Sched x w hl with hst | hst
          · refine le_of_eq ?_
            rw [hst, httime]
          · rw [hst]; exact le_trans ih hmono
      | deliver p m =>
          have htime : x[i + 1].time = x[i].time := Restated.deliver_time facts S Sched x hl
          by_cases hp : p = w
          · subst hp
            rcases Restated.st_succ_of_deliver facts S Sched x hl with h | ⟨-, h⟩
            · rw [(facts.nd.process_clock (Setup.alwaysAwake S) (x[i][p].st) m.msg _ h).1, htime]
              exact ih
            · rw [h, htime]
              exact ih
          · rw [Restated.getElem_succ_of_deliver_ne facts S Sched x hl hp, htime]
            exact ih
      | custom p ev => exact ev.elim
      | adversarial p m =>
          rw [Restated.getElem_succ_of_adversarial facts S Sched x hl, Restated.adversarial_time facts S Sched x hl]
          exact ih
      | forward p m =>
          rw [Restated.getElem_succ_of_forward facts S Sched x hl, Restated.forward_time facts S Sched x hl]
          exact ih

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- A validator's store clock after `i + 1` steps is at or after its clock after `i` steps. -/
theorem clock_mono_step (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (i : Nat) (w : V) :
    (x[i][w].st).st.core.t ≤ (x[i + 1][w].st).st.core.t := by
  cases hl : x.lbl i with
  | tickAllAwake τ =>
      obtain ⟨hten, -⟩ := Restated.tickAllAwake_time facts S Sched x hl
      rcases clock_succ_of_tick facts S Sched x w hl with h2 | hst
      · have h3 : (x[i].time : Int) + 1 = (τ : Int) := by exact_mod_cast hten
        have h4 := Restated.clock_le_time_sts facts S Sched x i w
        rw [h2]
        linarith
      · exact le_of_eq hst.symm
  | deliver p m =>
      by_cases hp : p = w
      · subst hp
        refine le_of_eq ?_
        rcases Restated.st_succ_of_deliver facts S Sched x hl with h | ⟨-, h⟩
        · rw [(facts.nd.process_clock (Setup.alwaysAwake S) (x[i][p].st) m.msg _ h).1]
        · rw [h]
      · exact le_of_eq (by rw [Restated.getElem_succ_of_deliver_ne facts S Sched x hl hp])
  | custom p ev => exact ev.elim
  | adversarial p m => exact le_of_eq (by rw [Restated.getElem_succ_of_adversarial facts S Sched x hl])
  | forward p m => exact le_of_eq (by rw [Restated.getElem_succ_of_forward facts S Sched x hl])

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For `i ≤ j`, a validator's store clock after `j` steps is at or after its clock after `i` steps. -/
theorem clock_mono_sts (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (w : V) {i j : Nat} (hij : i ≤ j) :
    (x[i][w].st).st.core.t ≤ (x[j][w].st).st.core.t := by
  induction j, hij using Nat.le_induction with
  | base => exact le_refl _
  | succ m hm ih => exact le_trans ih (Restated.clock_mono_step facts S Sched x m w)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- After the tick at a multiple `τ` of `Δ`, a validator awake and not held by the adversary at `τ`
    holds the node state of an outcome of its tick from `Record.wakeStage M Sched τ x[k] w`, or that
    tick has no outcome and it holds that wake-stage node state. -/
theorem st_succ_of_tick_awake (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (w : V) {k τ : Nat}
    (hl : x.lbl k = AtomicAction.tickAllAwake τ)
    (haw : w ∈ Sched.awake (τ : Int) \ Sched.adv (τ : Int))
    (hdvd : (τ : Int) % S.E.Δ = 0) :
    (∃ out₁ : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) w (Record.wakeStage M Sched (τ : Int) x[k] w) (τ : Int) ⇢ out₁ ∧ x[k + 1][w].st = out₁.1) ∨
      ((∀ out₁ : M.N × List (NamedObject V),
          ¬ M.tick (Setup.alwaysAwake S) w (Record.wakeStage M Sched (τ : Int) x[k] w) (τ : Int) ⇢ out₁) ∧
        x[k + 1][w].st = Record.wakeStage M Sched (τ : Int) x[k] w) := by
  have hs : AtomicStep (Record.protocolOf M S) Sched (x.lbl k) x[k] x[k + 1] := x.step k
  rw [hl] at hs
  obtain ⟨-, w', tk, hwake, htick, hc⟩ := hs
  have hwst : (w' w).state = Record.wakeStage M Sched (τ : Int) x[k] w :=
    Record.wakeStage_of_TickAllAwakeWake M S Sched (hwake w)
  have hx1 : x[k + 1][w].st = (tk w).state := by
    have h2 : x[k + 1][w] = (tickAllAwakeUpdate Sched τ x[k] w' tk)[w] := by rw [hc]
    rw [h2, tickAllAwakeUpdate_getElem_react haw]
  have htk := Record.protocolOf_step_tick M S (htick w haw)
  rw [hwst] at htk
  rcases htk with ⟨-, out₁, hout, hst⟩ | ⟨hno, hst⟩
  · exact Or.inl ⟨out₁, hout, by rw [hx1, hst]⟩
  · exact Or.inr ⟨hno.resolve_left (fun h => h hdvd), by rw [hx1, hst]⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- After the tick at a multiple `τ` of `Δ`, a validator awake and not held by the adversary at `τ`,
    whose tick there has an outcome, has store clock `τ`. -/
theorem clock_eq_of_tick_awake_sts (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {k τ : Nat} {w : V}
    (hl : x.lbl k = AtomicAction.tickAllAwake τ)
    (haw : w ∈ Sched.awake (τ : Int) \ Sched.adv (τ : Int))
    (hdvd : (τ : Int) % S.E.Δ = 0)
    (hne : ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) w (Record.wakeStage M Sched (τ : Int) x[k] w) (τ : Int) ⇢ out) :
    (x[k + 1][w].st).st.core.t = (τ : Int) := by
  rcases Restated.st_succ_of_tick_awake facts S Sched x w hl haw hdvd with
    ⟨out₁, hout, hst⟩ | ⟨hno, -⟩
  · rw [hst]
    exact (facts.nd.tick_clock (Setup.alwaysAwake S) w _ (τ : Int) out₁ hout).1
  · obtain ⟨out, hout⟩ := hne
    exact absurd hout (hno out)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If step `n` is the tick at a multiple `t` of `Δ` and `w` is awake and not held by the adversary
    at `t`, with a tick there that has an outcome, then `w`'s store clock is at or after `t` at
    every step from `n + 1` on. -/
theorem clock_ge_of_tickStepAt_awake_sts (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {n : Nat} {t : Int} {w : V}
    (hn : Restated.tickStepAt M x n t) (haw : w ∈ Sched.awake t \ Sched.adv t) (hdvd : t % S.E.Δ = 0)
    (hne : ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) w (Record.wakeStage M Sched t x[n] w) t ⇢ out)
    {m : Nat} (hm : n + 1 ≤ m) : t ≤ (x[m][w].st).st.core.t := by
  obtain ⟨t', hlbl, ht'⟩ := hn
  subst ht'
  rw [← Restated.clock_eq_of_tick_awake_sts facts S Sched x hlbl haw hdvd hne]
  exact Restated.clock_mono_sts facts S Sched x w hm

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- A store whose clock is at or after round `r`'s action instant has a round at or after `r`. -/
theorem receiver_round_ge_of_clock_ge (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (i : Nat) (w : V) (r : Round)
    (h : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[i][w].st).st.core.t) :
    r ≤ (M.round_of S.hc (x[i][w].st).st.core.s) := by
  rw [Restated.receiver_round_at_step facts S Sched x i w, ← Restated.round_of_slotOf_action facts S r]
  exact facts.gr.round_of_mono_sts S.hc (slotOf_mono_sts S h)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- A store read at a step whose time is at or before `t` has a round at or before the round of
    `t`'s slot. -/
theorem receiver_round_le_of_time_le (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (i : Nat) (w : V) {t : Int}
    (h : (x[i].time : Int) ≤ t) :
    (M.round_of S.hc (x[i][w].st).st.core.s) ≤ (M.round_of S.hc (S.E.slotOf t)) := by
  rw [Restated.receiver_round_at_step facts S Sched x i w]
  exact facts.gr.round_of_mono_sts S.hc
    (slotOf_mono_sts S (le_trans (Restated.clock_le_time_sts facts S Sched x i w) h))

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- A step that delivers `sm` to `w` happens at a configuration whose sent log already holds `sm`
    and at which `w` is awake. -/
theorem sent_of_deliver (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {k : Nat} {w : V}
    {sm : SignedMsg V (NamedObject V)}
    (hl : x.lbl k = AtomicAction.deliver w sm) :
    sm ∈ x[k].sent ∧ AtomicAwake x k w := by
  have hs : AtomicStep (Record.protocolOf M S) Sched (x.lbl k) x[k] x[k + 1] := x.step k
  rw [hl] at hs
  exact ⟨hs.1.1, hs.1.2.1⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- When step `k` delivers `sm` to `w` and `w`'s receipt of it has an outcome, every object `w`
    relays from it is an honest send of `⟨w, o⟩` at step `k`. -/
theorem honestSendAt_of_deliver_relay (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {k : Nat} {w : V}
    {sm : SignedMsg V (NamedObject V)} {o : NamedObject V}
    (hl : x.lbl k = AtomicAction.deliver w sm) (ho : o ∈ relayedObjects sm.msg)
    (hne : ∃ n' : M.N, M.process (Setup.alwaysAwake S) (x[k][w].st) sm.msg ⇢ n') :
    Restated.HonestSendAt M S x k (⟨w, o⟩ : SignedMsg V (NamedObject V)) := by
  have hs : AtomicStep (Record.protocolOf M S) Sched (x.lbl k) x[k] x[k + 1] := x.step k
  rw [hl] at hs
  exact ⟨Restated.mem_sent_diff_of_deliver facts S Sched x hl ho hne, AtomicStep.deliver_not_adv hs⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If step `k` delivers `⟨v, .attest a⟩` to `w`, `a` names `v`, and `v` is honest through the time
    of step `k`, then `v` was awake and not held by the adversary at the action instant of `a`'s
    round, some step `n < k` is the tick at that instant, and that instant is at or before the time
    of step `k`. -/
theorem deliver_attest_after_action (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    {k : Nat} {v w : V} {a : NamedAttestation V}
    (hv : HonestThroughTime Sched (x[k].time : Int) v)
    (hunf : Restated.Unforgeability M S x) (hidx : a.val_index = v)
    (hl : x.lbl k = AtomicAction.deliver w ⟨v, NamedObject.attest a⟩) :
    a.val_index = v ∧ v ∈ Sched.awake ((Restated.Vocabulary.Execution.Setup.a M S a.round)) \ Sched.adv ((Restated.Vocabulary.Execution.Setup.a M S a.round)) ∧
      ∃ n < k, Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S a.round)) ∧ (Restated.Vocabulary.Execution.Setup.a M S a.round) ≤ (x[k].time : Int) := by
  obtain ⟨hsent, -⟩ := Restated.sent_of_deliver facts S Sched x hl
  obtain ⟨hidx, n, hnk, htick, hawn, -⟩ :=
    Restated.attest_round_of_sent facts S Sched x hv hunf hidx (le_refl ((x[k].time : Nat) : Int)) hsent
  refine ⟨hidx, hawn, n, hnk, htick, ?_⟩
  have h1 : (x[n + 1].time : Int) = (Restated.Vocabulary.Execution.Setup.a M S a.round) := (Restated.tickStepAt_time facts x htick).1
  rw [← h1]
  exact Restated.time_mono_int facts S Sched x (Nat.succ_le_of_lt hnk)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If `⟨v, .attest a⟩` is in `w`'s view at step `j`, then some step `k < j` delivered it to `w`,
    and either `w` already held that sender's head for `a`'s round there, or `a` is in `w`'s bucket
    for `a.round` after step `k` and at step `j`, and `w`'s stamp for the SG vote of `a` is its
    store clock at step `k`. The hypotheses `hwin` and `hroom` say that each such delivery passes
    the window and the two-heads tests, and `hne` that the receipt there has an outcome. -/
theorem attest_recorded_of_mem_view (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    {j : Nat} {v w : V} {a : NamedAttestation V}
    (hview : (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[j][w].view)
    (haw : AtomicAwake x j w)
    (hwin : ∀ k : Nat, k < j →
      x.lbl k = AtomicAction.deliver w ⟨v, NamedObject.attest a⟩ →
      ¬ (a.round < (M.round_of S.hc (x[k][w].st).st.core.s) - S.hc.η_SG ∨
         (M.round_of S.hc (x[k][w].st).st.core.s) < a.round))
    (hroom : ∀ k : Nat, k < j →
      x.lbl k = AtomicAction.deliver w ⟨v, NamedObject.attest a⟩ →
      (M.round_votes (x[k][w].st).st.core a.erase).card ≠ 2)
    (hne : ∀ k : Nat, k < j →
      x.lbl k = AtomicAction.deliver w ⟨v, NamedObject.attest a⟩ →
      ∃ n' : M.N, M.process (Setup.alwaysAwake S) (x[k][w].st) (NamedObject.attest a) ⇢ n') :
    ∃ k : Nat, k < j ∧ x.lbl k = AtomicAction.deliver w ⟨v, NamedObject.attest a⟩ ∧
      (a.erase.confirmed ∈ M.round_votes (x[k][w].st).st.core a.erase ∨
        (a ∈ (x[k + 1][w].st).st.sg_rows a.round ∧
          a ∈ (x[j][w].st).st.sg_rows a.round ∧
          (x[k + 1][w].st).st.core.timestamp_sg_vote (M.sgVote a.erase)
            = some (((x[k][w].st).st.core.t : Stamp)))) := by
  obtain ⟨k, hkj, hlbl⟩ := Restated.deliver_of_mem_view facts S Sched x j hview
  refine ⟨k, hkj, hlbl, ?_⟩
  by_cases hnew : a.erase.confirmed ∈ M.round_votes (x[k][w].st).st.core a.erase
  · exact Or.inl hnew
  · refine Or.inr ?_
    have hproc : M.process (Setup.alwaysAwake S) (x[k][w].st) (NamedObject.attest a)
        ⇢ x[k + 1][w].st := by
      rcases Restated.st_succ_of_deliver facts S Sched x hlbl with h | ⟨hno, -⟩
      · exact h
      · obtain ⟨n', hn'⟩ := hne k hkj hlbl
        exact absurd hn' (hno n')
    have hst : (x[k + 1][w].st).st
        = M.make_grades_compatible_with_finalized (M.admit_row S.hc (x[k][w].st).st a) := by
      rw [facts.nd.process_st (Setup.alwaysAwake S) _ _ _ hproc]
      exact congrArg M.make_grades_compatible_with_finalized (facts.nd.process_attest _ _ a)
    have h1 : a ∈ (x[k + 1][w].st).st.sg_rows a.round := by
      rw [hst, facts.nd.make_grades_compatible_with_finalized_sg_rows]
      exact Restated.on_sg_vote_records facts S.hc (x[k][w].st).st a (hwin k hkj hlbl) hnew (hroom k hkj hlbl)
    have h2 : a ∈ (x[j][w].st).st.sg_rows a.round := by
      have hp : Restated.Vocabulary.Execution.Object.processed M (x[k + 1][w].st).st
          (NamedObject.attest a) = true := by
        simpa only [Restated.Vocabulary.Execution.Object.processed, decide_eq_true_eq] using h1
      simpa only [Restated.Vocabulary.Execution.Object.processed, decide_eq_true_eq] using
        Restated.processed_mono facts S Sched x w (NamedObject.attest a) (Nat.succ_le_of_lt hkj) hp
    refine ⟨h1, h2, ?_⟩
    have hcond : ¬ (a.erase.round < (M.round_of S.hc (x[k][w].st).st.core.s) - S.hc.η_SG ∨
        (M.round_of S.hc (x[k][w].st).st.core.s) < a.erase.round ∨
        a.erase.confirmed ∈ M.round_votes (x[k][w].st).st.core a.erase ∨
        (M.round_votes (x[k][w].st).st.core a.erase).card = 2) := by
      rintro (h | h | h | h)
      · rw [Proofs.ModelProperties.erase_round] at h
        exact hwin k hkj hlbl (Or.inl h)
      · rw [Proofs.ModelProperties.erase_round] at h
        exact hwin k hkj hlbl (Or.inr h)
      · exact hnew h
      · exact hroom k hkj hlbl h
    have hcore : M.sameCore (M.admit_row S.hc (x[k][w].st).st a).core
        (M.on_sg_vote S.hc (x[k][w].st).st.core a.erase) :=
      facts.hd.NamedAdmission_admit_row_core S.hc (x[k][w].st).st a
    have hafter : (M.on_sg_vote S.hc (x[k][w].st).st.core a.erase).timestamp_sg_vote
        (M.sgVote a.erase) = some (((x[k][w].st).st.core.t : Stamp)) :=
      facts.hd.on_sg_vote_timestamp_of_admitted S.hc (x[k][w].st).st.core a.erase hcond
    rw [hst, facts.nd.make_grades_compatible_with_finalized_core_timestamp_sg_vote,
      facts.hd.sameCore_timestamp_sg_vote hcore, hafter]

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For an honest send of `⟨v, .attest a⟩` at step `k_0`, under `SynchronyFromWake`, if step `j` is
    at or after the send's deadline and `w` is awake at step `j` and from the time the message is on
    the wire through the deadline, then the conclusion of `attest_recorded_of_mem_view` holds. -/
theorem attest_recorded_of_honestSend_succ (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (hsync : Restated.SynchronyFromWake M S x)
    {k_0 j : Nat} {v w : V} {a : NamedAttestation V}
    (hsend : Restated.HonestSendAt M S x k_0 (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)))
    (hlate : max (x[k_0].time : Int) S.E.t_GST + S.E.Δ ≤ (x[j].time : Int))
    (haw : AtomicAwake x j w)
    (hwaw : w ∈ Sched.awakeThroughout (x[k_0 + 1].time : Int)
      (max (x[k_0].time : Int) S.E.t_GST + S.E.Δ))
    (hwin : ∀ k : Nat, k < j →
      x.lbl k = AtomicAction.deliver w ⟨v, NamedObject.attest a⟩ →
      ¬ (a.round < (M.round_of S.hc (x[k][w].st).st.core.s) - S.hc.η_SG ∨
         (M.round_of S.hc (x[k][w].st).st.core.s) < a.round))
    (hroom : ∀ k : Nat, k < j →
      x.lbl k = AtomicAction.deliver w ⟨v, NamedObject.attest a⟩ →
      (M.round_votes (x[k][w].st).st.core a.erase).card ≠ 2)
    (hne : ∀ k : Nat, k < j →
      x.lbl k = AtomicAction.deliver w ⟨v, NamedObject.attest a⟩ →
      ∃ n' : M.N, M.process (Setup.alwaysAwake S) (x[k][w].st) (NamedObject.attest a) ⇢ n') :
    ∃ k : Nat, k < j ∧ x.lbl k = AtomicAction.deliver w ⟨v, NamedObject.attest a⟩ ∧
      (a.erase.confirmed ∈ M.round_votes (x[k][w].st).st.core a.erase ∨
        (a ∈ (x[k + 1][w].st).st.sg_rows a.round ∧
          a ∈ (x[j][w].st).st.sg_rows a.round ∧
          (x[k + 1][w].st).st.core.timestamp_sg_vote (M.sgVote a.erase)
            = some (((x[k][w].st).st.core.t : Stamp)))) :=
  Restated.attest_recorded_of_mem_view facts S Sched x
    (Restated.synchronyFromWakeView_of_deliver_succ facts S Sched x hsync hsend hwaw hlate) haw hwin hroom
    hne

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For `m ≤ m'`, validator `w`'s events over the first `m'` steps are its events over the first `m`
    steps followed by more events. -/
theorem vevents_append_of_le (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (w : V) {m m' : Nat} (hmm : m ≤ m') :
    ∃ l : List (Record.Event V), Record.veventsOf M S Sched x w m' = Record.veventsOf M S Sched x w m ++ l := by
  induction m', hmm using Nat.le_induction with
  | base => exact ⟨[], by rw [List.append_nil]⟩
  | succ n hn ih =>
      obtain ⟨l, hl⟩ := ih
      refine ⟨l ++ Record.actionEventsOf M S Sched w (x[n].time : Int) (x.lbl n), ?_⟩
      have hstep : Record.veventsOf M S Sched x w (n + 1)
          = Record.veventsOf M S Sched x w n ++ Record.actionEventsOf M S Sched w (x[n].time : Int) (x.lbl n) := rfl
      rw [hstep, hl, List.append_assoc]

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For `m ≤ m'`, `w`'s events over the first `m` steps are no more than its events over the first
    `m'` steps. -/
theorem length_vevents_mono (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (w : V) {m m' : Nat} (hmm : m ≤ m') :
    (Record.veventsOf M S Sched x w m).length ≤ (Record.veventsOf M S Sched x w m').length := by
  obtain ⟨l, hl⟩ := Restated.vevents_append_of_le facts S Sched x w hmm
  rw [hl, List.length_append]
  exact Nat.le_add_right _ _

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For `m ≤ m'`, some world reached by the first `(veventsOf … m).length` events of `w`'s run over
    the first `m'` steps holds, at `w`, `w`'s node state after `m` steps. -/
theorem stateBefore_runOf_le (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (w : V)
    {m m' : Nat} (hmm : m ≤ m') :
    ∃ W ∈ Record.stateBeforeOf M (Setup.alwaysAwake S) (Record.runOfM M S Sched x w m')
        (Record.veventsOf M S Sched x w m).length, W w = x[m][w].st := by
  obtain ⟨l, hl⟩ := Restated.vevents_append_of_le facts S Sched x w hmm
  have hfold : Record.stateBeforeOf M (Setup.alwaysAwake S) (Record.runOfM M S Sched x w m')
      (Record.veventsOf M S Sched x w m).length
      = (Record.veventsOf M S Sched x w m).foldlM (Record.worldStepOf M (Setup.alwaysAwake S))
          (fun v' => M.initial (Setup.alwaysAwake S) v') := by
    show ((Record.veventsOf M S Sched x w m').take (Record.veventsOf M S Sched x w m).length).foldlM
      (Record.worldStepOf M (Setup.alwaysAwake S)) (fun v' => M.initial (Setup.alwaysAwake S) v') = _
    rw [hl]
    simp
  rw [hfold]
  exact Record.fold_veventsOf M S Sched x facts.nd.wake_events_or_id w m

/-- For `m ≤ m'` and a world `W` holding `w`'s node state after `m` steps, the events `w`
    contributes in steps `m` to `m' - 1` can lead from `W` to a world holding `w`'s node state after
    `m'` steps. -/
private theorem fold_drop_veventsOf (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (w : V)
    {m m' : Nat} (hmm : m ≤ m')
    (W : V → M.N) (hW : W w = x[m][w].st) :
    ∃ W' ∈ ((Record.veventsOf M S Sched x w m').drop
        (Record.veventsOf M S Sched x w m).length).foldlM
        (Record.worldStepOf M (Setup.alwaysAwake S)) W, W' w = x[m'][w].st := by
  induction m', hmm using Nat.le_induction with
  | base =>
      rw [List.drop_length]
      exact ⟨W, Set.mem_singleton W, hW⟩
  | succ n hn ih =>
      obtain ⟨W₁, hW₁, hW₁w⟩ := ih
      obtain ⟨W₂, hW₂, hW₂w⟩ := Record.fold_actionEventsOf M S Sched x facts.nd.wake_events_or_id w n W₁ hW₁w
      refine ⟨W₂, ?_, hW₂w⟩
      have hlen : (Record.veventsOf M S Sched x w m).length
          ≤ (Record.veventsOf M S Sched x w n).length :=
        Restated.length_vevents_mono facts S Sched x w hn
      rw [show Record.veventsOf M S Sched x w (n + 1)
            = Record.veventsOf M S Sched x w n ++ Record.actionEventsOf M S Sched w (x[n].time : Int) (x.lbl n)
          from rfl, List.drop_append_of_le_length hlen, List.foldlM_append, Set.bind_def]
      exact Set.mem_biUnion hW₁ hW₂

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If `w`'s store after `m` steps holds the attestation `a` in the bucket of its round, then for
    every `m' ≥ m` it still holds `a` there, with the same stamp for the SG vote of `a`. -/
theorem sgRow_stamp_mono_sts (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (w : V)
    {m m' : Nat} (hmm : m ≤ m')
    {a : NamedAttestation V} (ha : a ∈ (x[m][w].st).st.sg_rows a.round) :
    a ∈ (x[m'][w].st).st.sg_rows a.round ∧
      (x[m'][w].st).st.core.timestamp_sg_vote (M.sgVote a.erase)
        = (x[m][w].st).st.core.timestamp_sg_vote (M.sgVote a.erase) := by
  obtain ⟨W₁, hW₁, hW₁w⟩ := Restated.stateBefore_runOf_le facts S Sched x w hmm
  obtain ⟨W₂, hW₂, hW₂w⟩ := fold_drop_veventsOf facts S Sched x w hmm W₁ hW₁w
  have ha' : a ∈ (W₁ w).st.sg_rows a.round := by rw [hW₁w]; exact ha
  have hW₂' : W₂ ∈ (((Record.runOfM M S Sched x w m').events.drop
      (Record.veventsOf M S Sched x w m).length).take
      ((Record.veventsOf M S Sched x w m').length - (Record.veventsOf M S Sched x w m).length)).foldlM
      (Record.worldStepOf M (Setup.alwaysAwake S)) W₁ := by
    show W₂ ∈ (((Record.veventsOf M S Sched x w m').drop
      (Record.veventsOf M S Sched x w m).length).take
      ((Record.veventsOf M S Sched x w m').length - (Record.veventsOf M S Sched x w m).length)).foldlM
      (Record.worldStepOf M (Setup.alwaysAwake S)) W₁
    rw [List.take_of_length_le (by rw [List.length_drop])]
    exact hW₂
  have h := Restated.Vocabulary.Proofs.NamedSGArrival.stateBefore_sg_row_stamp_mono facts (Setup.alwaysAwake S)
    (Record.runOfM M S Sched x w m') w (Restated.length_vevents_mono facts S Sched x w hmm) W₁ hW₁ ha'
    W₂ hW₂'
  rw [hW₁w, hW₂w] at h
  exact h

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If `w` is awake from the action instant of `a`'s round to the time of step `j` and not held by
    the adversary at that instant, `a` names `v`, `v` is honest through the time of step `j`, and
    the round of that time's slot is at most `a.round + η_SG`, then no delivery of `⟨v, .attest a⟩`
    to `w` before step `j` finds `a` stale or of a future round. The hypothesis `hneTick` says that
    `w`'s tick at the action instant of `a`'s round has an outcome. -/
theorem window_of_awakeThroughout (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    {j : Nat} {v w : V} {a : NamedAttestation V}
    (hv : HonestThroughTime Sched (x[j].time : Int) v)
    (hunf : Restated.Unforgeability M S x) (hidx : a.val_index = v)
    (hawT : w ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S a.round)) (x[j].time : Int))
    (hwh : w ∉ Sched.adv ((Restated.Vocabulary.Execution.Setup.a M S a.round)))
    (hexp : (M.round_of S.hc (S.E.slotOf (x[j].time : Int))) ≤ a.round + S.hc.η_SG)
    (hneTick : ∀ n : Nat, Restated.tickStepAt M x n (Restated.Vocabulary.Execution.Setup.a M S a.round) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) w (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S a.round) x[n] w) (Restated.Vocabulary.Execution.Setup.a M S a.round) ⇢ out) :
    ∀ k : Nat, k < j →
      x.lbl k = AtomicAction.deliver w ⟨v, NamedObject.attest a⟩ →
      ¬ (a.round < (M.round_of S.hc (x[k][w].st).st.core.s) - S.hc.η_SG ∨
         (M.round_of S.hc (x[k][w].st).st.core.s) < a.round) := by
  intro k hkj hlbl
  have hkt : (x[k].time : Int) ≤ (x[j].time : Int) := Restated.time_mono_int facts S Sched x (le_of_lt hkj)
  have hvk : HonestThroughTime Sched (x[k].time : Int) v :=
    fun t ht => hv t (le_trans ht hkt)
  obtain ⟨-, -, n, hnk, htick, hact⟩ := Restated.deliver_attest_after_action facts S Sched x hvk hunf hidx hlbl
  have hawa : w ∈ Sched.awake ((Restated.Vocabulary.Execution.Setup.a M S a.round)) :=
    mem_awake_of_awakeThroughout Sched hawT (le_refl _) (le_trans hact hkt)
  have hclock : (Restated.Vocabulary.Execution.Setup.a M S a.round) ≤ (x[k][w].st).st.core.t :=
    Restated.clock_ge_of_tickStepAt_awake_sts facts S Sched x htick (Finset.mem_sdiff.2 ⟨hawa, hwh⟩)
      (Restated.action_emod_delta facts S a.round) (hneTick n htick)
      (Nat.succ_le_of_lt hnk)
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

/-- `attest_recorded_of_mem_view` with the window test discharged by `window_of_awakeThroughout`. -/
theorem attest_recorded_of_mem_view_awake (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    {j : Nat} {v w : V} {a : NamedAttestation V}
    (hview : (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[j][w].view)
    (haw : AtomicAwake x j w)
    (hv : HonestThroughTime Sched (x[j].time : Int) v)
    (hunf : Restated.Unforgeability M S x) (hidx : a.val_index = v)
    (hawT : w ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S a.round)) (x[j].time : Int))
    (hwh : w ∉ Sched.adv ((Restated.Vocabulary.Execution.Setup.a M S a.round)))
    (hexp : (M.round_of S.hc (S.E.slotOf (x[j].time : Int))) ≤ a.round + S.hc.η_SG)
    (hroom : ∀ k : Nat, k < j →
      x.lbl k = AtomicAction.deliver w ⟨v, NamedObject.attest a⟩ →
      (M.round_votes (x[k][w].st).st.core a.erase).card ≠ 2)
    (hneTick : ∀ n : Nat, Restated.tickStepAt M x n (Restated.Vocabulary.Execution.Setup.a M S a.round) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) w (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S a.round) x[n] w) (Restated.Vocabulary.Execution.Setup.a M S a.round) ⇢ out)
    (hne : ∀ k : Nat, k < j →
      x.lbl k = AtomicAction.deliver w ⟨v, NamedObject.attest a⟩ →
      ∃ n' : M.N, M.process (Setup.alwaysAwake S) (x[k][w].st) (NamedObject.attest a) ⇢ n') :
    ∃ k : Nat, k < j ∧ x.lbl k = AtomicAction.deliver w ⟨v, NamedObject.attest a⟩ ∧
      (a.erase.confirmed ∈ M.round_votes (x[k][w].st).st.core a.erase ∨
        (a ∈ (x[k + 1][w].st).st.sg_rows a.round ∧
          a ∈ (x[j][w].st).st.sg_rows a.round ∧
          (x[k + 1][w].st).st.core.timestamp_sg_vote (M.sgVote a.erase)
            = some (((x[k][w].st).st.core.t : Stamp)))) :=
  Restated.attest_recorded_of_mem_view facts S Sched x hview haw
    (Restated.window_of_awakeThroughout facts S Sched x hv hunf hidx hawT hwh hexp hneTick) hroom hne

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For an honest send of `⟨v, .attest a⟩` at step `k_0`, under `SynchronyFromWake`, with `w` awake
    from the time the message is on the wire through its deadline, the conclusion of
    `attest_recorded_of_mem_view_awake` holds. -/
theorem attest_recorded_of_honestSend_awake_succ (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hsync : Restated.SynchronyFromWake M S x)
    {k_0 j : Nat} {v w : V} {a : NamedAttestation V}
    (hsend : Restated.HonestSendAt M S x k_0 (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)))
    (hlate : max (x[k_0].time : Int) S.E.t_GST + S.E.Δ ≤ (x[j].time : Int))
    (haw : AtomicAwake x j w)
    (hwaw : w ∈ Sched.awakeThroughout (x[k_0 + 1].time : Int)
      (max (x[k_0].time : Int) S.E.t_GST + S.E.Δ))
    (hv : HonestThroughTime Sched (x[j].time : Int) v)
    (hunf : Restated.Unforgeability M S x) (hidx : a.val_index = v)
    (hawT : w ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S a.round)) (x[j].time : Int))
    (hwh : w ∉ Sched.adv ((Restated.Vocabulary.Execution.Setup.a M S a.round)))
    (hexp : (M.round_of S.hc (S.E.slotOf (x[j].time : Int))) ≤ a.round + S.hc.η_SG)
    (hroom : ∀ k : Nat, k < j →
      x.lbl k = AtomicAction.deliver w ⟨v, NamedObject.attest a⟩ →
      (M.round_votes (x[k][w].st).st.core a.erase).card ≠ 2)
    (hneTick : ∀ n : Nat, Restated.tickStepAt M x n (Restated.Vocabulary.Execution.Setup.a M S a.round) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) w (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S a.round) x[n] w) (Restated.Vocabulary.Execution.Setup.a M S a.round) ⇢ out)
    (hne : ∀ k : Nat, k < j →
      x.lbl k = AtomicAction.deliver w ⟨v, NamedObject.attest a⟩ →
      ∃ n' : M.N, M.process (Setup.alwaysAwake S) (x[k][w].st) (NamedObject.attest a) ⇢ n') :
    ∃ k : Nat, k < j ∧ x.lbl k = AtomicAction.deliver w ⟨v, NamedObject.attest a⟩ ∧
      (a.erase.confirmed ∈ M.round_votes (x[k][w].st).st.core a.erase ∨
        (a ∈ (x[k + 1][w].st).st.sg_rows a.round ∧
          a ∈ (x[j][w].st).st.sg_rows a.round ∧
          (x[k + 1][w].st).st.core.timestamp_sg_vote (M.sgVote a.erase)
            = some (((x[k][w].st).st.core.t : Stamp)))) :=
  Restated.attest_recorded_of_honestSend_succ facts S Sched x hsync hsend hlate haw hwaw
    (Restated.window_of_awakeThroughout facts S Sched x hv hunf hidx hawT hwh hexp hneTick) hroom hne

end

end DecoupledConsensusModel.Sts.Restated
