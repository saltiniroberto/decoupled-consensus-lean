import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bSyncView
import Proofs.Claims.Restated.RunAll
import Model.Conditions.ClaimAsyncK_DeliveryUpTo
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Record.Wiring

/-!
# Synchrony up to the send's deadline

The delivery and view forms of synchrony from wake, with synchrony assumed only up to the deadline
of the send, stated over a model `M : Record.Model V`.
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

/-- Under `SynchronyFromWakeBefore` up to the deadline `max x[k].time t_GST + Δ`, whatever an honest
    validator puts on the wire at step `k` is delivered, at a step after `k` and strictly before
    that deadline, to every validator awake at every time from `x[k].time` through it. -/
theorem synchronyFromWake_from_step_upTo (facts : Record.Facts M) (S : Setup V) {Sched : Schedule V}
    {x : AtomicExec (Record.protocolOf M S) Sched} {k : Nat}
    (hsync : Restated.SynchronyFromWakeBefore M S x (max (x[k].time : Int) S.E.t_GST + S.E.Δ))
    {w : V} {sm : SignedMsg V (NamedObject V)}
    (hsend : Restated.HonestSendAt M S x k sm)
    (haw : w ∈ Sched.awakeThroughout (x[k].time : Int)
      (max (x[k].time : Int) S.E.t_GST + S.E.Δ)) :
    ∃ d : Nat, k < d ∧ x.lbl d = AtomicAction.deliver w sm ∧
      (x[k].time : Int) ≤ (x[d].time : Int) ∧
      (x[d].time : Int) < max (x[k].time : Int) S.E.t_GST + S.E.Δ :=
  hsync k w sm hsend le_rfl (Restated.awakeThroughout_succ_of_step facts S haw)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Under `SynchronyFromWakeBefore` up to the deadline `max x[k].time t_GST + Δ`, a message an
    honest validator put on the wire at step `k` is in the view of every validator awake at every
    time from `x[k + 1].time` through that deadline, at every step whose time is at or after it. -/
theorem synchronyFromWakeView_of_deliver_succ_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {k j : Nat}
    (hsync : Restated.SynchronyFromWakeBefore M S x (max (x[k].time : Int) S.E.t_GST + S.E.Δ))
    {w : V} {sm : SignedMsg V (NamedObject V)}
    (hsend : Restated.HonestSendAt M S x k sm)
    (haw : w ∈ Sched.awakeThroughout (x[k + 1].time : Int)
      (max (x[k].time : Int) S.E.t_GST + S.E.Δ))
    (hj : max (x[k].time : Int) S.E.t_GST + S.E.Δ ≤ (x[j].time : Int)) :
    sm ∈ x[j][w].view := by
  obtain ⟨d, hkd, hlbl, -, hlt⟩ := hsync k w sm hsend le_rfl haw
  have hdj : d < j := by
    by_contra hcon
    have hle : (x[j].time : Int) ≤ (x[d].time : Int) := by
      exact_mod_cast Restated.time_mono facts S Sched x (Nat.le_of_not_lt hcon)
    linarith
  exact Restated.mem_view_mono facts S Sched x (Nat.succ_le_of_lt hdj)
    (Restated.mem_view_succ_of_deliver facts S Sched x hlbl)

end

end DecoupledConsensusModel.Sts.Restated
