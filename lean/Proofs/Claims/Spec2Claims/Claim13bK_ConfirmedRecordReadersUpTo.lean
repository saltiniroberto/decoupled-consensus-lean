import Proofs.Claims.Spec2Claims.Claim13bK_ConfirmedRecordUpTo
import Proofs.Claims.Spec2Claims.Claim13bModel_domain
import Proofs.Claims.Spec2Claims.Claim13bModel_Preceq

/-!
# A slot bound over `Nat`

One arithmetic fact: `3 ≤ R` gives `a + 2 ≤ a + R`.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution
variable {V : Type} [DecidableEq V] [Fintype V]
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Over `Nat`, `3 ≤ R` gives `a + 2 ≤ a + R`. -/
theorem nat_add_two_le_add_8b {a R : Nat} (h : 3 ≤ R) : a + 2 ≤ a + R := by omega

section Premises

variable (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched) (tE : Int)
    (hexec : ExecutionValid S Sched (interface S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : TimeDiverges x)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + healingLengthη S gap ≤ tE)
    {b₀ : Int} (hsync : SynchronyFromWakeBefore S x b₀)
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

include hexec hmono htd hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec
  hprev hclear hB' hnW hAW hJswitch

end Premises

end DecoupledConsensusModel.Sts
