import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.ReceiptOutcome
import Proofs.Claims.Restated.Claim13bRelayUpTo
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bStepKitRelay
import Proofs.Claims.Restated.Claim13beRoute3_23
import Proofs.Claims.Restated.ProcessedFlip
import Proofs.Claims.Restated.RunAll
import Proofs.Claims.Restated.VocabularyAssumptionsLemmas
import Model.Conditions.Claim13bStepKitRelayUpTo
import Model.Conditions.ClaimAsyncK_DeliveryUpTo
import Model.Conditions.ProcessedFlip
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Record.Wiring

/-!
# Relaying Goldfish votes, with synchrony up to a cutoff

The relay obligation for Goldfish votes up to a deadline, and its consequence for a receiver's pool,
assuming synchrony only up to that deadline, stated over a model `M : Record.Model V` and its facts
`facts : Record.Facts M`.
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

/-- `GfVoteRelayAtAcceptBefore` up to `b'` gives it up to every `b ≤ b'`. -/
theorem GfVoteRelayAtAcceptBefore.mono {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (Record.protocolOf M S) Sched} {b b' : Int} (hb : b ≤ b')
    (h : Restated.GfVoteRelayAtAcceptBefore M S x b') : Restated.GfVoteRelayAtAcceptBefore M S x b :=
  fun i v w u hle => h i v w u (le_trans hle hb)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- `SynchronyFromWakeBefore` up to `b` gives `GfVoteRelayAtAcceptBefore` up to `b`. -/
theorem gfVoteRelayAtAcceptBefore_of_sync (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {b : Int}
    (hsync : Restated.SynchronyFromWakeBefore M S x b) :
    Restated.GfVoteRelayAtAcceptBefore M S x b := by
  intro i v w u hb h0 h1 hvh _hawi hwaw
  have hf0 : Restated.Vocabulary.Execution.Object.processed M (x[i][v].st).st
      (NamedObject.gfVote u) = false :=
    decide_eq_false (fun h => h0 ((facts.sto.mem_store_pool_iff _ _ _).2 h))
  have hf1 : Restated.Vocabulary.Execution.Object.processed M (x[i + 1][v].st).st
      (NamedObject.gfVote u) = true :=
    decide_eq_true ((facts.sto.mem_store_pool_iff _ _ _).1 h1)
  have hti : (x[i].time : Int) ≤ (x[i + 1].time : Int) := by
    exact_mod_cast Restated.time_mono facts S Sched x (Nat.le_succ i)
  have hwin : w ∈ Sched.awakeThroughout (x[i].time : Int)
      (max (x[i].time : Int) S.E.t_GST + S.E.Δ) :=
    awakeThroughout_shrink Sched hwaw
      (by have := max_le_max hti (le_refl S.E.t_GST); linarith)
  have hsend : Restated.HonestSendAt M S x i
      (⟨v, NamedObject.gfVote u⟩ : SignedMsg V (NamedObject V)) := by
    rcases Restated.flip_step_cases facts S Sched x hf0 hf1 with
      ⟨m, hl, -, -, hcase⟩ | ⟨τ, hl, haw, hdvd, out₁, hout, hst, hcase⟩
    · have ho : NamedObject.gfVote u ∈ relayedObjects m.msg := by
        rw [mem_relayedObjects_iff]
        rcases hcase with heq | ⟨B, hB, hcc⟩
        · exact Or.inl heq.symm
        · rw [hB]; exact Or.inr (Restated.carries_of_carriedCall facts _ _ B hcc)
      exact Restated.honestSendAt_of_deliver_relay facts S Sched x hl ho
        (Restated.receipt_outcome_of_flip facts S Sched x hl hf0 hf1)
    · rcases hcase with hmem | ⟨B, hem, hcc⟩
      · exact ⟨Restated.mem_sent_diff_of_tick_of_state facts S Sched x hl haw hdvd
          (fun o₁ o₂ h₁ h₂ h12 =>
            facts.nd.tick_send_eq_of_state (Setup.alwaysAwake S) v _ _ o₁ o₂ h₁ h₂ h12)
          hout hst hmem,
          hvh (x[i].time : Int) (le_refl _)⟩
      · exfalso
        obtain ⟨⟨j, hj⟩, -, -⟩ := hcc
        exact h0 (Restated.mem_pool_of_mem_tick_block facts S Sched x i v (τ : Int) out₁ hout
          hem (List.mem_of_getElem? hj))
  have hsync' : Restated.SynchronyFromWakeBefore M S x
      (max (x[i].time : Int) S.E.t_GST + S.E.Δ) :=
    fun k w' sm hs hle haw => hsync k w' sm hs
      (le_trans hle (by have := max_le_max hti (le_refl S.E.t_GST); linarith)) haw
  exact Restated.relay_of_honestSendAt_from_upTo facts S Sched x hsync'
    (le_refl i) hti hsend rfl hwin

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- `gfVote_in_pool_of_accepts` with the relay obligation assumed only up to the deadline
    `max x[i + 1].time t_GST + Δ`. -/
theorem gfVote_in_pool_of_accepts_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) {i : Nat} {v w : V} {u : GoldfishVote V}
    (hrelay : Restated.GfVoteRelayAtAcceptBefore M S x (max (x[i + 1].time : Int) S.E.t_GST + S.E.Δ))
    (htd : Restated.TimeDiverges M x)
    (h0 : u ∉ (M.store_pool (x[i][v].st).st.core u.slot))
    (h1 : u ∈ (M.store_pool (x[i + 1][v].st).st.core u.slot))
    (hvh : Restated.HonestThrough M Sched x i v)
    (hawi : AtomicAwake x i w) (hcomm : u.val_index ∈ S.E.committee u.slot)
    (hpos : 0 < u.slot)
    (hlo : slotStart S.E.Δ u.slot ≤ (x[i + 1].time : Int))
    (hawT : w ∈ Sched.awakeThroughout (slotStart S.E.Δ u.slot - 1)
      (max (x[i + 1].time : Int) S.E.t_GST + S.E.Δ))
    (hwh : w ∉ Sched.adv (slotStart S.E.Δ u.slot))
    (hhi : max (x[i + 1].time : Int) S.E.t_GST + S.E.Δ ≤ slotStart S.E.Δ (u.slot + 2))
    (hneTick : ∀ n : Nat, Restated.tickStepAt M x n (slotStart S.E.Δ u.slot) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) w (Record.wakeStage M Sched (slotStart S.E.Δ u.slot) x[n] w) (slotStart S.E.Δ u.slot) ⇢ out) :
    ∃ k : Nat, (x[i + 1].time : Int) ≤ (x[k].time : Int) ∧
      (x[k].time : Int) < max (x[i + 1].time : Int) S.E.t_GST + S.E.Δ ∧
      ((u ∈ (M.store_pool (x[k + 1][w].st).st.core u.slot) ∧
          ∃ τ : Stamp, (x[k + 1][w].st).st.core.timestamp_vote u = some τ ∧
            τ ≤ ((x[k].time : Int) : Stamp)) ∨
        M.equivocates ((M.store_pool (x[k][w].st).st.core u.slot)) u.val_index = true) := by
  have hloi : slotStart S.E.Δ u.slot - 1 ≤ (x[i].time : Int) := by
    have := Restated.time_succ_le facts S Sched x i
    linarith
  obtain ⟨k, m, hk0, hk1, hlbl, hmsg⟩ :=
    hrelay i v w u (le_refl _) h0 h1 hvh hawi
      (awakeThroughout_shrink_left Sched hawT hloi)
  refine ⟨k, hk0, hk1, ?_⟩
  have hm_eq : (⟨m.sender, NamedObject.gfVote u⟩ : SignedMsg V (NamedObject V)) = m := by
    rw [← hmsg]
  have hlbl' : x.lbl k = AtomicAction.deliver w ⟨m.sender, NamedObject.gfVote u⟩ := by
    rw [hlbl, hm_eq]
  have hlok : slotStart S.E.Δ u.slot ≤ (x[k].time : Int) := le_trans hlo hk0
  have hhik : (x[k].time : Int) < slotStart S.E.Δ (u.slot + 2) := lt_of_lt_of_le hk1 hhi
  have hawTk : w ∈ Sched.awakeThroughout (slotStart S.E.Δ u.slot) (x[k].time : Int) :=
    awakeThroughout_shrink Sched (awakeThroughout_shrink_left Sched hawT (by linarith))
      (le_of_lt hk1)
  have hwin := Restated.gf_window_of_awakeThroughout facts S Sched x htd k w u hawTk hwh hlok hpos hhik
    hneTick
  have hstamp : ∀ _hmem : u ∈ (M.store_pool (x[k + 1][w].st).st.core u.slot),
      ∃ τ : Stamp, (x[k + 1][w].st).st.core.timestamp_vote u = some τ ∧
        τ ≤ ((x[k].time : Int) : Stamp) := by
    intro hmem
    obtain ⟨τ, hτ, hb⟩ := Restated.stamp_le_clock_gfVote facts S Sched x (k + 1) w hmem
    refine ⟨τ, hτ, le_trans hb ?_⟩
    have h1 : (x[k + 1][w].st).st.core.t ≤ (x[k + 1].time : Int) :=
      Restated.clock_le_time_sts facts S Sched x (k + 1) w
    have h2 : x[k + 1].time = x[k].time := Restated.deliver_time facts S Sched x hlbl'
    have h3 : (x[k + 1][w].st).st.core.t ≤ (x[k].time : Int) := by
      rw [← h2]; exact h1
    exact WithBot.coe_le_coe.mpr h3
  rcases Restated.gfVote_recorded_of_deliver facts S Sched x hlbl' hwin hcomm
      (facts.nd.process_nonempty _ _ _ (fun _ h => by cases h)) with hmk | heq | ⟨hm1, -⟩
  · refine Or.inl ?_
    have hk1mem : u ∈ (M.store_pool (x[k + 1][w].st).st.core u.slot) := by
      have h := Restated.processed_mono_step facts S Sched x w (NamedObject.gfVote u) k
        (decide_eq_true ((facts.sto.mem_store_pool_iff _ _ _).1 hmk))
      simp only [Restated.Vocabulary.Execution.Object.processed, decide_eq_true_eq] at h
      exact (facts.sto.mem_store_pool_iff _ _ _).2 h
    exact ⟨hk1mem, hstamp hk1mem⟩
  · exact Or.inr heq
  · exact Or.inl ⟨hm1, hstamp hm1⟩

end

end DecoupledConsensusModel.Sts.Restated
