module
public import Model.Sts.Spec2Claims.Claim13be

@[expose] public section

/-!
# Catch-up on wake

The premise `CatchUpOnWake`: a validator that wakes is delivered, within a delay of its wake, what
honest validators sent before it.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Catch-up on wake: a message an honest validator sent at step `k` before `w`'s wake instant `t_w`
    is delivered to `w` at a step after `k`, at or after `t_w` and strictly before
    `max t_w S.E.t_GST + S.E.Δ`, provided `w` stays awake throughout until then. -/
def CatchUpOnWake (S : Setup V) {Sched : Schedule V}
    (x : AtomicExec (protocol S) Sched) : Prop :=
  ∀ (k : Nat) (w : V) (sm : SignedMsg V (NamedObject V)) (t_w : Int),
    HonestSendAt S x k sm →
    (x[k].time : Int) < t_w →
    w ∈ Sched.awake t_w → w ∉ Sched.awake (t_w - 1) →
    w ∈ Sched.awakeThroughout t_w (max t_w S.E.t_GST + S.E.Δ) →
    ∃ d : Nat, k < d ∧ x.lbl d = AtomicAction.deliver w sm ∧
      t_w ≤ (x[d].time : Int) ∧ (x[d].time : Int) < max t_w S.E.t_GST + S.E.Δ

end DecoupledConsensusModel.Sts
