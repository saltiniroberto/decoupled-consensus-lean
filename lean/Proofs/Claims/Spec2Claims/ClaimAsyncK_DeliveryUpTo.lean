import Model.Sts.Spec2Claims.ClaimStableThroughAsyncPeriod
import Proofs.Claims.Spec2Claims.Claim13bStepConeIter

/-!
# Synchrony from wake up to a bound

The premise `SynchronyFromWakeBefore`: delivery promised only for an honest send whose deadline is
at or before a bound.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Synchrony from wake, promised only up to the bound `b₀`: for an honest send at step `k` whose
    deadline `max (x[k].time) S.E.t_GST + S.E.Δ` is at most `b₀`, every validator awake throughout
    from `x[k + 1].time` to that deadline is delivered the message at a later step, at a time at or
    after the send's and strictly before the deadline. -/
def SynchronyFromWakeBefore (S : Setup V) {Sched : Schedule V}
    (x : AtomicExec (protocol S) Sched) (b₀ : Int) : Prop :=
  ∀ (k : Nat) (w : V) (sm : SignedMsg V (NamedObject V)),
    HonestSendAt S x k sm →
    max (x[k].time : Int) S.E.t_GST + S.E.Δ ≤ b₀ →
    w ∈ Sched.awakeThroughout (x[k + 1].time : Int)
      (max (x[k].time : Int) S.E.t_GST + S.E.Δ) →
    ∃ d : Nat, k < d ∧ x.lbl d = AtomicAction.deliver w sm ∧
      (x[k].time : Int) ≤ (x[d].time : Int) ∧
      (x[d].time : Int) < max (x[k].time : Int) S.E.t_GST + S.E.Δ

end DecoupledConsensusModel.Sts
