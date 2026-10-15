import Proofs.Claims.Spec2Claims.Claim13bK_ConfirmedRecord
import Proofs.Claims.Spec2Claims.Claim13bModel_advance_confirmed
import Proofs.Claims.Spec2Claims.Claim13bModel_floor_on_stable
import Proofs.Claims.Spec2Claims.Claim13bModel_get_stable
import Proofs.Claims.Spec2Claims.Claim13bModel_get_confirmed
import Proofs.Claims.Spec2Claims.Claim13bModel_Preceq

/-!
# Monotonicity of the confirmed output

The store-level fact that `get_confirmed` only moves to a descendant when `F` and the two records
`latest_stable` and `latest_confirmed` do and the new store's parts lie on one chain, with the slot
arithmetic it uses.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

open Framework.StsMultisetLog

/-! ## Slot arithmetic -/

/-- For `Δ > 0`, `t` is at or before the start of slot `s_0 + s_1 + t.toNat + 2`. -/
theorem le_slotStart_of_toNat (Δ : Int) (hΔ : 0 < Δ) (t : Int) (s_0 s_1 : Nat) :
    t ≤ slotStart Δ (s_0 + s_1 + t.toNat + 1 + 1) := by
  rw [slotStart_closed]
  have h1 : t ≤ (t.toNat : Int) := Int.self_le_toNat t
  have h2 : (0 : Int) ≤ (s_0 : Int) + (s_1 : Int) + (t.toNat : Int) + 2 := by positivity
  push_cast
  nlinarith

/-- `a ≤ a + b + c + 1`, over `Nat`. -/
theorem nat_le_sum_left_c4 (a b c : Nat) : a ≤ a + b + c + 1 := by omega

/-- `b ≤ a + b + c + 1`, over `Nat`. -/
theorem nat_le_sum_right_c4 (a b c : Nat) : b ≤ a + b + c + 1 := by omega

/-! ## The confirmed output only extends -/

omit [Fintype V] in
/-- If `A` and `B` lie on one chain, and `B` is `A` or is not an ancestor of `A`, then `A` is an
    ancestor of `B`. -/
theorem preceq_of_compatible_of_eq_or_not_preceq {A B : Block V}
    (hc : Block.compatible A B = true) (h : B = A ∨ ¬ Block.Preceq B A) :
    Block.Preceq A B := by
  rcases h with h | h
  · rw [h]; exact Proofs.ModelProperties.Preceq_self A
  · rcases compatible_cases hc with h1 | h1
    · exact h1
    · exact absurd h1 h

omit [Fintype V] in
/-- If the old store's `F`, `latest_stable` and `latest_confirmed` are ancestors of the new store's,
    the new `F` and `latest_stable` lie on one chain, and the new `get_stable` and
    `latest_confirmed` lie on one chain, then the old `get_confirmed` is an ancestor of the new one. -/
theorem get_confirmed_preceq_of_fields (old new : Protocol.Store V)
    (hF : Block.Preceq old.F new.F)
    (hL : Block.Preceq old.latest_stable new.latest_stable)
    (hC : Block.Preceq old.latest_confirmed new.latest_confirmed)
    (hFL : Block.compatible new.F new.latest_stable = true)
    (hSC : Block.compatible (Protocol.get_stable new) new.latest_confirmed = true) :
    Block.Preceq (Protocol.get_confirmed old) (Protocol.get_confirmed new) := by
  obtain ⟨hFS, hLS⟩ := get_stable_upper new hFL
  obtain ⟨hSO, hCO⟩ := get_confirmed_upper new hSC
  rcases get_confirmed_eq_or old with h | h
  · rw [h]; exact Proofs.ModelProperties.Preceq_trans hC hCO
  · rw [h]
    rcases get_stable_eq_or old with h' | h'
    · rw [h']; exact Proofs.ModelProperties.Preceq_trans hL (Proofs.ModelProperties.Preceq_trans hLS hSO)
    · rw [h']; exact Proofs.ModelProperties.Preceq_trans hF (Proofs.ModelProperties.Preceq_trans hFS hSO)

section Premises

variable (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched) (tE : Int)
    (hexec : ExecutionValid S Sched (interface S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : TimeDiverges x)
    (hcatch : CatchUpOnWake S x)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + healingLengthη S gap ≤ tE)
    (hsync : SynchronyFromWake S x)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : roundSleepinessW S Sched tE)
    (hmult : AwakeAtMultiples S Sched) (hcv : CommonViewOfFinalizedDescendantsAt S Sched x tGAT)
    (hcs : committeeSleepinessW S Sched tE)
    (hcom : HonestCommittees S Sched (interface S Sched))
    (hrec : strongOpeningsRecurFrom S Sched tGAT tE gap)
    (hprev : ∀ r : Round, rebasedDeadlineRoundW S tGAT gap ≤ r → r ≤ switchRound S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round),
      S.a r ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      NamedHeightRegimeRunOn (Setup.alwaysAwake S)
        ({ runAll S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Run V)
        (notHeldAt Sched) Finset.univ Finset.univ
        (roundAt S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → BasePreviousRoundSGCompatibleWithAnchorAtRound S Sched x v r N T)
    (hclear : ∀ r : Round, rebasedDeadlineRoundW S tGAT gap ≤ r → r ≤ switchRound S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round) (n₀ : Nat),
      S.a r ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      NamedHeightRegimeRunOn (Setup.alwaysAwake S)
        ({ runAll S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Run V)
        (notHeldAt Sched) Finset.univ Finset.univ
        (roundAt S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → tickStepAt x n₀ (S.a r) →
      BaseClearFGSourceCompatibleWithAnchorAtRound S Sched x r n₀ T)
    (hB' : BaseJustifiedHighAtSwitchRoundW S Sched x tGAT tE gap)
    {n_W : Nat} (hnW : tickStepAt x n_W (S.a (switchRound S tE)))
    {T_W : NamedBlock V} (hAW : AnchorAtRound S Sched x tGAT tE (switchRound S tE) T_W)
    (hJswitch : ∀ (v : V) (n₁ : Nat),
      Protocol.vote_time S.E (S.hc.opening_slot (switchRound S tE) + 1) - 1
        ≤ (x[n₁].time : Int) →
      n₁ ≤ n_W → HonestThrough Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J T_W.erase)

include hexec hmono htd hcatch hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hrec
  hprev hclear hB' hnW hAW hJswitch

end Premises

end DecoupledConsensusModel.Sts
