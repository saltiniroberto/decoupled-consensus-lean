import Proofs.Claims.Spec2Claims.Claim13bK_ConfirmedWake
import Proofs.Claims.Spec2Claims.Claim13bK_JointBase
import Proofs.Claims.Spec2Claims.Claim13bModel_setClock_inclG1
import Proofs.Claims.Spec2Claims.Claim13bModel_gradeContract_inclG1
import Proofs.Claims.Spec2Claims.Claim13bModel_readFrame_incl
import Proofs.Claims.Spec2Claims.Claim13bModel_proposal_time_inclG1
import Proofs.Claims.Spec2Claims.Claim13bModel_confirmationReadFrom
import Proofs.Claims.Spec2Claims.Claim13bModel_opening

/-!
# Slot and round arithmetic over `Nat`

Arithmetic facts over `Nat` about slots relative to a round's opening slot.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- An index into an sts execution is always valid, so `get_elem_tactic` is answered by
    `True.intro`. -/
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-! ## Arithmetic over `Nat` -/

/-- If `0 < a` and `a + 1 ≤ r`, then `r = r₂ + 1 + 1` for some `r₂`. -/
theorem nat_exists_add_two_g1 {a r : Nat} (ha : 0 < a) (hr : a + 1 ≤ r) :
    ∃ r₂ : Nat, r = r₂ + 1 + 1 :=
  ⟨r - 2, by omega⟩

/-- If `3 ≤ R`, then `a + 2 ≤ a + R + 1`. -/
theorem nat_add_two_le_add_succ_g1 {a R : Nat} (h : 3 ≤ R) : a + 2 ≤ a + R + 1 := by
  omega

/-- If `o + 2 ≤ s`, then `o + 2 ≤ s − 1` or `s − 1 = o + 1`. -/
theorem nat_pred_cases_g1 {o s : Nat} (h : o + 2 ≤ s) : o + 2 ≤ s - 1 ∨ s - 1 = o + 1 := by
  omega

/-- If `s < o'`, then `s − 1 ≤ o' + 1`. -/
theorem nat_pred_le_g1 {s o' : Nat} (h : s < o') : s - 1 ≤ o' + 1 := by
  omega

/-- If `s < o'`, then `s ≤ o' + 1`. -/
theorem nat_le_succ_of_lt_g1 {s o' : Nat} (h : s < o') : s ≤ o' + 1 := by
  omega

/-- If `3 ≤ R`, `o + R ≤ s` and not `o + R + 2 ≤ s`, then `o + 2 ≤ s − 1`, `s − 1 ≤ o + R + 1` and
    `s ≤ o + R + 1`. -/
theorem nat_firstSlots_g1 {o R s : Nat} (h3 : 3 ≤ R) (hlo : o + R ≤ s) (hhi : ¬ o + R + 2 ≤ s) :
    o + 2 ≤ s - 1 ∧ s - 1 ≤ o + R + 1 ∧ s ≤ o + R + 1 := by
  omega

/-- If `3 ≤ R` and `o + R ≤ s`, then `o + 2 ≤ s − 1`. -/
theorem nat_prev_round_third_le_pred_g1 {o R s : Nat} (h3 : 3 ≤ R) (hlo : o + R ≤ s) :
    o + 2 ≤ s - 1 := by
  omega

/-- If `a ≤ r`, then `0 < r − a` or `r = a`. -/
theorem nat_sub_pos_or_eq_g1 {a r : Nat} (h : a ≤ r) : 0 < r - a ∨ r = a := by
  omega

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
    (hw : WakesAtActionInstants S Sched) (hs : SleepsAfterActionInstants S Sched)
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

include hexec hmono htd hcatch hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec
  hprev hclear hB' hnW hAW hJswitch

end Premises

section Premises2

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
    (hw : WakesAtActionInstants S Sched) (hs : SleepsAfterActionInstants S Sched)
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

include hexec hmono htd hcatch hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec
  hprev hclear hB' hnW hAW hJswitch

end Premises2

end DecoupledConsensusModel.Sts
