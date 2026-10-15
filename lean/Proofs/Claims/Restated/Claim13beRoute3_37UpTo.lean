import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.ReceiptOutcome
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bStepKitRelay
import Proofs.Claims.Restated.Claim13bSyncViewUpTo
import Proofs.Claims.Restated.Claim13beRoute3_23
import Proofs.Claims.Restated.ProcessedFlip
import Proofs.Claims.Restated.RunAll
import Model.Conditions.ClaimAsyncK_DeliveryUpTo
import Model.Conditions.ProcessedFlip
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Record.Wiring

/-!
# Recorded Goldfish votes are delivered, with synchrony up to the deadline

A Goldfish vote an honest store records inside the phase is delivered to every validator not held at
the deadline, with synchrony assumed only up to that deadline. Stated over a model
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
open DecoupledConsensusModel.Protocol

/-- Under `SynchronyFromWakeBefore` up to the deadline (one delay after the later of `x[i + 1].time`
    and `t_GST`): if a Goldfish vote `u` enters `v`'s pool of `u`'s slot at step `i`, `v` is honest
    through that step, the step starts inside the phase, the deadline is inside the phase, and the
    adversary does not hold `w` at the deadline, then some step at or after `x[i + 1].time` and
    strictly before the deadline delivers to `w` the message `⟨v, u⟩`. -/
theorem gfVote_delivered_of_recorded_phase_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {i : Nat}
    (hsync : Restated.SynchronyFromWakeBefore M S x (max (x[i + 1].time : Int) S.E.t_GST + S.E.Δ))
    (hmono : Sched.MonotoneCorruption) {tGAT tE : Int}
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    {v w : V} {u : GoldfishVote V}
    (h0 : u ∉ (M.store_pool (x[i][v].st).st.core u.slot))
    (h1 : u ∈ (M.store_pool (x[i + 1][v].st).st.core u.slot))
    (hvh : Restated.HonestThrough M Sched x i v) (hi : tGAT ≤ (x[i].time : Int))
    (hdead : max (x[i + 1].time : Int) S.E.t_GST + S.E.Δ ≤ tE)
    (hw : w ∉ Sched.adv (max (x[i + 1].time : Int) S.E.t_GST + S.E.Δ)) :
    ∃ d : Nat, (x[i + 1].time : Int) ≤ (x[d].time : Int) ∧
      (x[d].time : Int) < max (x[i + 1].time : Int) S.E.t_GST + S.E.Δ ∧
      x.lbl d = AtomicAction.deliver w ⟨v, NamedObject.gfVote u⟩ := by
  have hf0 : Restated.Vocabulary.Execution.Object.processed M (x[i][v].st).st
      (NamedObject.gfVote u) = false :=
    decide_eq_false (fun h => h0 ((facts.sto.mem_store_pool_iff _ _ _).2 h))
  have hf1 : Restated.Vocabulary.Execution.Object.processed M (x[i + 1][v].st).st
      (NamedObject.gfVote u) = true :=
    decide_eq_true ((facts.sto.mem_store_pool_iff _ _ _).1 h1)
  have hti : (x[i].time : Int) ≤ (x[i + 1].time : Int) := by
    exact_mod_cast Restated.time_mono facts S Sched x (Nat.le_succ i)
  have hmax : max (x[i].time : Int) S.E.t_GST ≤ max (x[i + 1].time : Int) S.E.t_GST :=
    max_le_max hti (le_refl _)
  have hwin : w ∈ Sched.awakeThroughout (x[i].time : Int)
      (max (x[i].time : Int) S.E.t_GST + S.E.Δ) :=
    awakeThroughout_shrink Sched (awakeThroughout_phase Sched hawake hmono hi hdead hw)
      (by linarith)
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
  -- `hsync` at the earlier deadline `max x[i].time t_GST + Δ`
  have hsync' : Restated.SynchronyFromWakeBefore M S x
      (max (x[i].time : Int) S.E.t_GST + S.E.Δ) :=
    fun k w' sm hs hle haw => hsync k w' sm hs (le_trans hle (by linarith)) haw
  obtain ⟨d, hkd, hlbl, -, hlt⟩ := Restated.synchronyFromWake_from_step_upTo facts S hsync' hsend hwin
  refine ⟨d, ?_, by linarith, hlbl⟩
  exact_mod_cast Restated.time_mono facts S Sched x (show i + 1 ≤ d by omega)

end

end DecoupledConsensusModel.Sts.Restated
