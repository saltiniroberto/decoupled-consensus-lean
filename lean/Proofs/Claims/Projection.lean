module
public import StsMultisetLog.Analysis.AtomicLemmas
public import Proofs.Vocabulary.Protocol.Handlers.FinalizationBridge
public import Model.Sts.Conditions
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Proofs.Vocabulary.Execution.Runtime
public import Proofs.Vocabulary.Execution.Wire
public import Proofs.Vocabulary.Objects.Ancestry
public import Proofs.Claims.ModelIrreducible
public import Proofs.Claims.Spec2Claims.Claim13bModel_Preceq
public import Proofs.Claims.Spec2Claims.Claim13bModel_NamedBlock_Preceq
public import Proofs.Claims.Spec2Claims.Claim13bModel_RootInjectiveBelow

@[expose] public section

/-!
# The events one validator contributes to its run

Defines `actionEvents`, the events a validator contributes to its own run for one sts action, and
relates the wiring's tick condition to `PublicTime`.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The events one validator contributes -/

/-- The events validator `v` contributes to its own run when the sts execution takes the atomic
    action `a` from a configuration whose real time is `now`: one tick event at a `tickAllAwake t`
    step when `v` is awake at `t`, is not in `Sched.adv t`, and `t` is a whole multiple of `S.E.Δ`;
    one delivery event at a delivery to `v`; nothing otherwise. -/
def actionEvents (S : Setup V) (Sched : Schedule V) (v : V) (now : Int) :
    AtomicAction V (NamedObject V) Empty → List (NamedEvent V)
  | .tickAllAwake t =>
      if v ∈ Sched.awake (t : Int) \ Sched.adv (t : Int) ∧ (t : Int) % S.E.Δ = 0
        then [Generic.Event.tick v (t : Int)] else []
  | .deliver p m => if p = v then [Generic.Event.deliver v m.msg now] else []
  | .custom _ ev => ev.elim
  | .adversarial _ _ => []
  | .forward _ _ => []

/-- For a natural reading `t`, `(t : Int) % S.E.Δ = 0` holds exactly when `PublicTime S t`: `t`
    leaves no remainder on division by `S.E.Δ` exactly when it is a whole number of `S.E.Δ`s. -/
theorem emod_eq_zero_iff_publicTime (S : Setup V) (t : Nat) :
    (t : Int) % S.E.Δ = 0 ↔ PublicTime S (t : Int) := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := Int.dvd_of_emod_eq_zero h
    have hc0 : 0 ≤ c := by
      by_contra hneg
      have hcneg : c < 0 := Int.not_le.1 hneg
      have : (t : Int) < 0 := by
        rw [hc]
        exact mul_neg_of_pos_of_neg S.E.Δ_pos hcneg
      exact absurd this (Int.not_lt.2 (Int.natCast_nonneg t))
    refine ⟨c.toNat, ?_⟩
    rw [hc, Int.toNat_of_nonneg hc0, mul_comm]
  · rintro ⟨k, hk⟩
    rw [hk]
    exact Int.mul_emod_left _ _

end DecoupledConsensusModel.Sts
