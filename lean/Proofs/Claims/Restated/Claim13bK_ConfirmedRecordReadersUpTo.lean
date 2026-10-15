import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bK_ConfirmedRecord
import Proofs.Claims.Restated.Claim13bK_ConfirmedRecordUpTo
import Proofs.Claims.Restated.Claim13bK_ConfirmedSettle
import Proofs.Claims.Restated.Claim13bK_ConfirmedSettleUpTo
import Proofs.Claims.Restated.Claim13bK_ConfirmedStrongRoundWindow
import Proofs.Claims.Restated.Claim13bK_Frame
import Proofs.Claims.Restated.Claim13bK_HeadsPersistUpTo
import Proofs.Claims.Restated.Claim13bK_LiveConfirmedSlotsUpTo
import Proofs.Claims.Restated.Claim13bK_PrevHeadsStep
import Proofs.Claims.Restated.Claim13bK_PrevHeadsStepUpTo
import Proofs.Claims.Restated.Claim13bStepConeIter
import Proofs.Claims.Restated.Claim13bStepKitConfirm
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bW_Schedule
import Proofs.Claims.Restated.Claim13beRoute3_82
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActive
import Model.Conditions.Claim13bInvariantActiveJoint
import Model.Conditions.Claim13bInvariantActiveSinceW
import Model.Conditions.Claim13bInvariantActiveTop
import Model.Conditions.Claim13bK_ConfirmedRecordUpTo
import Model.Conditions.Claim13bK_FinBeforeTick
import Model.Conditions.Claim13bK_Frame
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13bStepCone
import Model.Conditions.Claim13bStepConeIter
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_74
import Model.Conditions.Claim13beRoute3_83
import Model.Conditions.ClaimAsyncK_DeliveryUpTo
import Model.Conditions.RunAll
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13bd
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Sts_Spec2Claims_ClaimConfirmedAfterHealing
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Vocabulary.Protocol.Grades
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Protocol_Grades_Main
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bK_ConfirmedRecordReadersUpTo

/-!
# Confirmed records at readers given by their awake window, up to a slot

The stable root, the two records and the confirmed output of a validator given by its awake window,
as ancestors of the honest heads of the slots up to `sEnd`, with synchrony assumed only up to a
bound `b₀`. Stated over a model `M : Record.Model V` and its facts.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

local macro "p83% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_83)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "pHP% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13bK_HeadsPersist)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "pCR% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13bK_ConfirmedRecord)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "pW% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13bK_ConfirmedStrongRoundWindow)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog

/-- Synchrony from wake up to `b'` gives synchrony from wake up to every `b ≤ b'`. -/
private theorem SynchronyFromWakeBefore.monoU {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (Record.protocolOf M S) Sched} {b b' : Int}
    (hs : Restated.SynchronyFromWakeBefore M S x b') (facts : Record.Facts M) (hb : b ≤ b') :
    Restated.SynchronyFromWakeBefore M S x b :=
  fun k w sm hsend hle haw => hs k w sm hsend (le_trans hle hb) haw

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Round `r`'s opening slot plus two is at or before round `r + 1`'s opening slot. -/
theorem opening_slot_add_two_le_succ (facts : Record.Facts M) (S : Setup V) (r : Round) :
    (M.opening_slot S.hc r) + 2 ≤ (M.opening_slot S.hc (r + 1)) := by
  rw [facts.gr.opening_slot_succ]; exact nat_add_two_le_add_8b S.hc.R_ge_three

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Under its premises on the execution and the phase ending at `tE`, with synchrony up to `b₀`
    where `max tE (S.a (round_of (sEnd − 2) + 1)) ≤ b₀`: if round `r` is at or after the switch
    round, `T_W` is an ancestor of `T`, the joint invariant holds at round `r` with anchor `T` and
    at round `r + 1`, `v` is awake from `S.a r` to the domain instant of a round-`(r + 1)` phase `p`
    and not held by the adversary there, `m` is the step before that instant, and the grade test of
    phase `p` at `v`'s store after `m` steps can return `true` for `B`, then `B` is an ancestor of
    every honest head of the slots from round `r + 1`'s opening slot to `sEnd`. -/
theorem graded_ancestorOfHonestHeadsFrom_at_awakeReader_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) {b₀ : Int} (hsync : Restated.SynchronyFromWakeBefore M S x b₀) (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight) (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t) (hrsW : Restated.roundSleepinessW M S Sched tE) (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT) (hcs : Restated.committeeSleepinessW M S Sched tE) (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched)) (hw : Restated.WakesAtActionInstants M S Sched) (hs : Restated.SleepsAfterActionInstants M S Sched) (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap) (hprev : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.BasePreviousRoundSGCompatibleWithAnchorAtRound M S Sched x v r N
        (Restated.runAllPath M S Sched x v N) T) (hclear : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round) (n₀ : Nat),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S r)) →
      Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T) (hB' : Restated.BaseJustifiedHighAtSwitchRoundW M S Sched x tGAT tE gap) {n_W : Nat} (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)))) {T_W : NamedBlock V} (hAW : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.switchRound M S tE) T_W) (hJswitch : ∀ (v : V) (n₁ : Nat),
      M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) - 1
        ≤ (x[n₁].time : Int) →
      n₁ ≤ n_W → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J T_W.erase) {sEnd : Slot}
    {r : Round} {n n₁ : Nat} {T T₁ : NamedBlock V}
    (hr : Restated.switchRound M S tE ≤ r) (hTW : Block.Preceq T_W.erase T.erase)
    (hJ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x r n n_W T)
    (hJ₁ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x (r + 1) n₁ n_W T₁)
    {v : V} {p : Protocol.Phase}
    (hawT : v ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S r)) (M.domain S.E S.hc (r + 1) p))
    (hvS : v ∉ Sched.adv (M.domain S.E S.hc (r + 1) p))
    {m : Nat} (hm : Restated.stepBeforeInstant M x m (M.domain S.E S.hc (r + 1) p))
    {B : Block V}
    (hB : M.gradeBool S.E (M.gradeView (M.toHealing (x[m][v].st).st.core))
      (x[m][v].st).st.core.F S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) p)
      (M.late S.E S.hc (r + 1) p) B ⇢ true)
    (hb₀ : max tE ((Restated.Vocabulary.Execution.Setup.a M S ((M.round_of S.hc (sEnd - 2)) + 1))) ≤ b₀) :
    Restated.AncestorOfHonestHeadsFromTo M S Sched x B ((M.opening_slot S.hc (r + 1))) sEnd := by
  by_cases hE : (M.opening_slot S.hc (r + 1)) ≤ sEnd
  swap
  · exact Restated.ancestorOfHonestHeadsFromTo_of_lt facts S Sched x (Nat.lt_of_not_le hE)
  have hsE : Restated.SynchronyFromWakeBefore M S x tE := hsync.monoU facts (le_trans (le_max_left _ _) hb₀)
  have hRr : r ≤ (M.round_of S.hc (sEnd - 2)) :=
    facts.gr.le_round_of_sub_two S.hc (le_trans (Restated.opening_slot_add_two_le_succ facts S r) hE)
  have hA1 : (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) ≤ b₀ :=
    le_trans (Restated.action_mono facts S (Nat.succ_le_succ hRr)) (le_trans (le_max_right _ _) hb₀)
  have hTop := (pHP% joint_toTop_hp) hJ
  have hcross : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepFinalizedCrossingUnderAnchor M S Sched x r n'' T :=
    fun n'' h => Restated.stepFinalizedCrossingUnderAnchor_of_afterSwitch facts S Sched x hr hnW
      hJ.toAfterPhaseInvariantOverActiveSetsSince
      (Restated.justified_preceq_anchor_ofJoint_upTo facts S Sched x tE hexec hmono htd tGAT gap hgst hlen hsE
        hthird hphase hrsW hmult hcv hcom hrec hprev hclear hB' hnW hAW hr hTW hJ h)
  obtain ⟨v_1, hv_1, a, har, hai, has, C, hC, hac, hBC⟩ :=
    Restated.graded_preceq_freshSG_at_awakeReader_upTo facts S Sched x tE hexec hmono htd
      (r := r) (hsync.monoU facts hA1) hmult tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr hTop hcross
      (facts.gr.domain_le_action S (r + 1) p) hawT hvS hm B hB
  have hCT : Block.compatible C.erase T.erase = true :=
    hTop.sg v_1 hv_1 a har hai has C hC hac
  have hPH := hJ₁.prevHeads
  simp only [Nat.add_sub_cancel] at hPH
  have hCheads : Restated.HeadsBelow M S Sched x C.erase ((M.opening_slot S.hc (r + 1))) :=
    hPH n hTop.tick v_1 hv_1 a har hai has C hC hac
  have hs0 : (M.opening_slot S.hc r) + 1 ≤ (M.opening_slot S.hc (r + 1)) := by
    rw [facts.gr.opening_slot_succ]
    exact Nat.add_le_add_left (le_trans (by decide : 1 ≤ 3) S.hc.R_ge_three) _
  have hCP := Restated.ancestorOfHonestHeadsFrom_of_compatible_anchor_upTo facts S Sched x tE hexec hmono htd
    tGAT gap hgst hlen (hsync.monoU facts hb₀) hthird hphase hrsW hmult hcv hcs hcom hw hs hrec hprev
    hclear hB' hnW hAW hJswitch hr hTW hJ hs0 (Nat.le_succ _) hCT hCheads
  exact Restated.ancestorOfHonestHeadsFrom_of_preceq_upTo facts S Sched x hBC hCP

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Under its premises on the execution and the phase ending at `tE`, with synchrony up to `b₀`
    where `max tE (S.a (round_of (sEnd − 2) + 1)) ≤ b₀`, and the joint invariant at a round `r₀` at
    or after the switch round for an anchor that is `T_W` or a descendant of it: if slot `s` is at
    least two after round `r₀`'s opening slot, the round `r'` of `s + 1` is after `r₀`, `m` is the
    tick step at slot `s`'s confirmation instant, `v` is awake from `S.a (r' − 1)` to that instant
    and honest through it, `c` is an outcome of `v`'s phase tick there, and `some G` is an outcome
    of the stable root of `c`'s grade contract at the clock-stamped store's round, then `G` is an
    ancestor of every honest head of the slots from `s + 3` to `sEnd`. -/
theorem stableRoot_ancestorOfHonestHeadsFrom_ofAwake_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) {b₀ : Int} (hsync : Restated.SynchronyFromWakeBefore M S x b₀) (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight) (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t) (hrsW : Restated.roundSleepinessW M S Sched tE) (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT) (hcs : Restated.committeeSleepinessW M S Sched tE) (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched)) (hw : Restated.WakesAtActionInstants M S Sched) (hs : Restated.SleepsAfterActionInstants M S Sched) (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap) (hprev : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.BasePreviousRoundSGCompatibleWithAnchorAtRound M S Sched x v r N
        (Restated.runAllPath M S Sched x v N) T) (hclear : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round) (n₀ : Nat),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S r)) →
      Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T) (hB' : Restated.BaseJustifiedHighAtSwitchRoundW M S Sched x tGAT tE gap) {n_W : Nat} (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)))) {T_W : NamedBlock V} (hAW : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.switchRound M S tE) T_W) (hJswitch : ∀ (v : V) (n₁ : Nat),
      M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) - 1
        ≤ (x[n₁].time : Int) →
      n₁ ≤ n_W → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J T_W.erase) {sEnd : Slot}
    {r₀ : Round} {n₀ : Nat} {T₀ : NamedBlock V}
    (hr₀ : Restated.switchRound M S tE ≤ r₀) (hTW₀ : Block.Preceq T_W.erase T₀.erase)
    (hJ₀ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x r₀ n₀ n_W T₀)
    {s : Slot} (hs0 : (M.opening_slot S.hc r₀) + 2 ≤ s)
    (hr1 : r₀ + 1 ≤ (M.round_of S.hc (s + 1)))
    {m : Nat} (hm : Restated.tickStepAt M x m (M.confirmation_time S.E s)) {v : V}
    (hvA : v ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S ((M.round_of S.hc (s + 1)) - 1)))
      (M.confirmation_time S.E s))
    (hvh : HonestThroughTime Sched (M.confirmation_time S.E s) v)
    {G : Block V} {c : M.Cache}
    (hc : M.onPhaseTick S.E S.hc (M.toHealing (x[m][v].st).st.core)
        (M.confirmation_time S.E s) (x[m][v].st).cache ⇢ c)
    (hG : (M.gradeContract c).stableRoot S.E S.hc
          (M.toHealing (M.ns_setClock S.E (x[m][v].st).st
            (M.confirmation_time S.E s)).core)
          ((M.round_of S.hc) (M.ns_setClock S.E (x[m][v].st).st
            (M.confirmation_time S.E s)).core.s) ⇢ some G)
    (hb₀ : max tE ((Restated.Vocabulary.Execution.Setup.a M S ((M.round_of S.hc (sEnd - 2)) + 1))) ≤ b₀) :
    Restated.AncestorOfHonestHeadsFromTo M S Sched x G (s + 3) sEnd := by
  by_cases hE : s + 3 ≤ sEnd
  swap
  · exact Restated.ancestorOfHonestHeadsFromTo_of_lt facts S Sched x (Nat.lt_of_not_le hE)
  have hsE : Restated.SynchronyFromWakeBefore M S x tE := hsync.monoU facts (le_trans (le_max_left _ _) hb₀)
  have hR0 : (M.round_of S.hc s) ≤ (M.round_of S.hc (sEnd - 2)) :=
    Restated.round_of_le_round_of_sub_two facts S (le_trans (Nat.le_succ _) hE)
  have hR1 : (M.round_of S.hc (s + 1)) ≤ (M.round_of S.hc (sEnd - 2)) :=
    Restated.round_of_le_round_of_sub_two facts S hE
  have hd := S.E.Δ_pos
  have hslot : (M.ns_setClock S.E (x[m][v].st).st
      (M.confirmation_time S.E s)).core.s = s + 1 := by
    rw [facts.hd.Sts_setClock_core_s]; exact facts.sch.Optimistic_slotOf_confirmation_time S.E s
  have hG := (facts.nd.gradeContract_stableRoot _ _ _ _ _ _).1 hG
  rw [hslot] at hG
  rcases facts.gr.frameStableRoot_cases _ _ _ _ _ _ hG rfl with hroot | ⟨root, hg2, hGroot⟩
  · -- the fork-choice root
    obtain ⟨hm1, hm0⟩ := Restated.tickStepAt_time facts x hm
    have hvm : Restated.HonestThrough M Sched x m v := fun t ht => hvh t (by linarith)
    have hrs0 := facts.gr.opening_slot_round_of_le_slot S.hc s
    have hrs1 := facts.gr.lt_opening_slot_round_of_succ S.hc s
    have hrr : r₀ ≤ (M.round_of S.hc s) := by
      by_contra hcon
      exact nat_lt_absurd_c3 hs0 hrs1
        (facts.gr.opening_slot_mono S (Nat.succ_le_of_lt (Nat.lt_of_not_le hcon)))
    obtain ⟨n, T, hJ, -, hTW⟩ := Restated.anchor_at_later_round_upTo facts S Sched x tE hexec hmono htd
      tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec hprev hclear hB'
      hnW hAW hJswitch hr₀ hTW₀ hJ₀ hrr (le_trans (Restated.anchorBound_le_headsBound facts S tE hR0) hb₀)
    have hr : Restated.switchRound M S tE ≤ (M.round_of S.hc s) := le_trans hr₀ hrr
    have hroot' : Block.Preceq (Restated.Vocabulary.Protocol.confRoot M (Restated.confStoreAt M S (x[m][v].st) s)) T.erase :=
      Restated.confRoot_preceq_anchor_atSlot_upTo facts S Sched x tE hexec hmono htd tGAT gap hgst hlen hsE
        hthird hphase hrsW hmult hcv hcom hrec hprev hclear hB' hnW hAW hr hTW hJ hrs0
        (Nat.le_of_lt hrs1) hm hvm
    have hGT : Block.Preceq G T.erase := by rw [hroot]; exact hroot'
    have hanc := Restated.anchor_ancestorOfHonestHeadsFrom_upTo facts S Sched x tE hexec hmono htd tGAT gap
      hgst hlen (hsync.monoU facts hb₀) hthird hphase hrsW hmult hcv hcs hcom hw hs hrec hprev hclear
      hB' hnW hAW hJswitch hr hTW hJ
    exact Restated.ancestorOfHonestHeadsFrom_mono_upTo facts S Sched x (nat_le_add3_c3 hrs0)
      (Restated.ancestorOfHonestHeadsFrom_of_preceq_upTo facts S Sched x hGT hanc)
  · -- an ancestor of the grade-2 entry of the round's frame, graded at an awake reader
    obtain ⟨root₀, hc0, hroot0⟩ := facts.gr.readFrame_g2_provenance _ _ _ hg2
    have hprov := Restated.framePhaseProvenance_onPhaseTick facts S hm
      (Restated.framePhaseProvenance_sts facts S Sched x v m) c hc
    obtain ⟨m', B, hm', hB, hroot0B⟩ := hprov _ .g2 root₀ hc0
    have hrs0 := facts.gr.opening_slot_round_of_le_slot S.hc (s + 1)
    have hr₀0 : 0 < r₀ := Restated.round_pos_of_switch facts S tGAT tE gap hgst hlen hr₀
    have hlt : (Restated.Vocabulary.Execution.Setup.a M S r₀) < M.confirmation_time S.E s := by
      rw [(pCR% action_closed_cr) facts, (pCR% confirmation_time_closed_cr) facts]
      have h1 : (((M.opening_slot S.hc r₀) : Nat) : Int) + 2 ≤ ((s : Nat) : Int) := by
        exact_mod_cast hs0
      rw [(pCR% opening_slot_closed_cr) facts] at h1
      push_cast at h1
      nlinarith
    obtain ⟨-, -, -, -, ha2⟩ := Restated.confirmation_tick_arith facts S hr₀0 hlt
    have hdom5 := facts.gr.domain_add_five_delta_le_action S ((M.round_of S.hc (s + 1))) .g2
    have hdomtc : M.domain S.E S.hc ((M.round_of S.hc (s + 1))) .g2
        ≤ M.confirmation_time S.E s := by linarith
    obtain ⟨r₁, hr₁⟩ : ∃ r₁ : Round, (M.round_of S.hc (s + 1)) = r₁ + 1 :=
      ⟨_, (Nat.succ_pred_eq_of_pos (Nat.lt_of_lt_of_le (Nat.succ_pos r₀) hr1)).symm⟩
    rw [hr₁] at hB hm' hr1 hrs0 hvA hdomtc hR1
    simp only [Nat.add_sub_cancel] at hvA
    have hrr₁ : r₀ ≤ r₁ := Nat.le_of_succ_le_succ hr1
    obtain ⟨n, T, hJ, -, hTW⟩ := Restated.anchor_at_later_round_upTo facts S Sched x tE hexec hmono htd
      tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec hprev hclear hB'
      hnW hAW hJswitch hr₀ hTW₀ hJ₀ hrr₁
      (le_trans (Restated.anchorBound_le_headsBound facts S tE (le_trans (Nat.le_succ r₁) hR1)) hb₀)
    obtain ⟨n₁, T₁, hJ₁, -, -⟩ := Restated.anchor_at_later_round_upTo facts S Sched x tE hexec hmono htd
      tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec hprev hclear hB'
      hnW hAW hJswitch hr₀ hTW₀ hJ₀ (Nat.le_succ_of_le hrr₁)
      (le_trans (Restated.anchorBound_le_headsBound facts S tE hR1) hb₀)
    have hawT : v ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S r₁)) (M.domain S.E S.hc (r₁ + 1) .g2) :=
      awakeThroughout_mono Sched hvA le_rfl hdomtc
    obtain ⟨b, hb⟩ := facts.gr.gradeBool_nonempty S.E
      (M.gradeView (M.toHealing (x[m'][v].st).st.core)) (x[m'][v].st).st.core.F S.hc.η_SG
      (r₁ + 1) (M.early S.E S.hc (r₁ + 1) .g2) (M.late S.E S.hc (r₁ + 1) .g2) B
    have hBt : M.gradeBool S.E (M.gradeView (M.toHealing (x[m'][v].st).st.core))
        (x[m'][v].st).st.core.F S.hc.η_SG (r₁ + 1) (M.early S.E S.hc (r₁ + 1) .g2)
        (M.late S.E S.hc (r₁ + 1) .g2) B ⇢ true := hB b hb ▸ hb
    have hBP := Restated.graded_ancestorOfHonestHeadsFrom_at_awakeReader_upTo facts S Sched x tE hexec hmono htd
      tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec hprev
      hclear hB' hnW hAW hJswitch (le_trans hr₀ hrr₁) hTW hJ hJ₁ hawT (hvh _ hdomtc) hm' hBt hb₀
    exact Restated.ancestorOfHonestHeadsFrom_mono_upTo facts S Sched x
      (le_trans hrs0 (Nat.add_le_add_left (by decide : 1 ≤ 3) s))
      (Restated.ancestorOfHonestHeadsFrom_of_preceq_upTo facts S Sched x
        (preceq_trans_Preceq hGroot (preceq_trans_Preceq hroot0 hroot0B)) hBP)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Under its premises on the execution and the phase ending at `tE`, with synchrony up to `b₀`
    where `max tE (S.a (round_of (sEnd − 2) + 1)) ≤ b₀`, and the joint invariant at a round `r₀` at
    or after the switch round for an anchor that is `T_W` or a descendant of it: if slot `s` is at
    least two after round `r₀`'s opening slot, the round `r'` of `s + 1` is after `r₀`, `m` is the
    tick step at slot `s`'s confirmation instant, `v` is awake from one delay before slot `s`'s
    start and from `S.a (r' − 1)` to that instant and honest through it, and `v`'s `latest_stable`
    and `latest_confirmed` after `m` steps are ancestors of every honest head of the slots from
    `s + 3` to `sEnd`, then so are they after `m + 1` steps. -/
theorem records_after_confirmation_tick_ancestorOfHonestHeadsFrom_ofAwake_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) {b₀ : Int} (hsync : Restated.SynchronyFromWakeBefore M S x b₀) (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight) (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t) (hrsW : Restated.roundSleepinessW M S Sched tE) (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT) (hcs : Restated.committeeSleepinessW M S Sched tE) (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched)) (hw : Restated.WakesAtActionInstants M S Sched) (hs : Restated.SleepsAfterActionInstants M S Sched) (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap) (hprev : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.BasePreviousRoundSGCompatibleWithAnchorAtRound M S Sched x v r N
        (Restated.runAllPath M S Sched x v N) T) (hclear : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round) (n₀ : Nat),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S r)) →
      Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T) (hB' : Restated.BaseJustifiedHighAtSwitchRoundW M S Sched x tGAT tE gap) {n_W : Nat} (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)))) {T_W : NamedBlock V} (hAW : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.switchRound M S tE) T_W) (hJswitch : ∀ (v : V) (n₁ : Nat),
      M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) - 1
        ≤ (x[n₁].time : Int) →
      n₁ ≤ n_W → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J T_W.erase) {sEnd : Slot}
    {r₀ : Round} {n₀ : Nat} {T₀ : NamedBlock V}
    (hr₀ : Restated.switchRound M S tE ≤ r₀) (hTW₀ : Block.Preceq T_W.erase T₀.erase)
    (hJ₀ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x r₀ n₀ n_W T₀)
    {s : Slot} (hs0 : (M.opening_slot S.hc r₀) + 2 ≤ s)
    (hr1 : r₀ + 1 ≤ (M.round_of S.hc (s + 1)))
    {m : Nat} (hm : Restated.tickStepAt M x m (M.confirmation_time S.E s)) {v : V}
    (hvaw : v ∈ Sched.awakeThroughout (slotStart S.E.Δ s - S.E.Δ)
      (M.confirmation_time S.E s))
    (hvA : v ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S ((M.round_of S.hc (s + 1)) - 1)))
      (M.confirmation_time S.E s))
    (hvh : HonestThroughTime Sched (M.confirmation_time S.E s) v)
    (hL : Restated.AncestorOfHonestHeadsFromTo M S Sched x (x[m][v].st).st.core.latest_stable (s + 3) sEnd)
    (hC : Restated.AncestorOfHonestHeadsFromTo M S Sched x (x[m][v].st).st.core.latest_confirmed (s + 3)
      sEnd)
    (hb₀ : max tE ((Restated.Vocabulary.Execution.Setup.a M S ((M.round_of S.hc (sEnd - 2)) + 1))) ≤ b₀) :
    Restated.AncestorOfHonestHeadsFromTo M S Sched x (x[m + 1][v].st).st.core.latest_stable (s + 3) sEnd ∧
      Restated.AncestorOfHonestHeadsFromTo M S Sched x (x[m + 1][v].st).st.core.latest_confirmed (s + 3)
        sEnd := by
  have hd := S.E.Δ_pos
  have haw : v ∈ Sched.awake (M.confirmation_time S.E s) \
      Sched.adv (M.confirmation_time S.E s) :=
    Finset.mem_sdiff.2 ⟨mem_awake_of_awakeThroughout Sched hvaw
      (by rw [slotStart_closed, (pCR% confirmation_time_closed_cr) facts]; linarith) le_rfl,
      hvh _ le_rfl⟩
  have hdvd : M.confirmation_time S.E s % S.E.Δ = 0 := by
    rw [facts.sch.confirmation_time_eq_support_cutoff_succ]
    exact facts.sch.support_cutoff_emod_delta S (s + 1)
  have hneTick := Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew
    hmono hm hdvd haw
  -- the grade-2 awake test of slot `s + 1`'s round at the confirmation tick
  have hrun : M.awake_for_grade2 (Setup.alwaysAwake S) v
      (Record.wakeStage M Sched (M.confirmation_time S.E s) x[m] v) (M.round_of S.hc (s + 1)) := by
    obtain ⟨τ, hlbl, hτ⟩ := id hm
    have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
    have hr'0 : 0 < M.round_of S.hc (s + 1) := lt_of_lt_of_le (Nat.succ_pos r₀) hr1
    have hlo := facts.gr.opening_slot_round_of_le_slot S.hc (s + 1)
    rw [(pCR% opening_slot_closed_cr) facts] at hlo
    have hloI : ((M.round_of S.hc (s + 1) : Nat) : Int) * (S.hc.R : Int) ≤ (s : Int) + 1 := by
      exact_mod_cast hlo
    have hea := facts.gr.early_g2_eq S (M.round_of S.hc (s + 1))
    have ha : M.a S.hc S.E.Δ (M.round_of S.hc (s + 1))
        = 4 * S.E.Δ * (S.hc.R : Int) * ((M.round_of S.hc (s + 1) : Nat) : Int) + 6 * S.E.Δ :=
      (pCR% action_closed_cr) facts S _
    have ha' : Restated.Vocabulary.Execution.Setup.a M S (M.round_of S.hc (s + 1) - 1)
        = 4 * S.E.Δ * (S.hc.R : Int) * (((M.round_of S.hc (s + 1) - 1 : Nat)) : Int) + 6 * S.E.Δ :=
      (pCR% action_closed_cr) facts S _
    have hsub : (((M.round_of S.hc (s + 1) - 1 : Nat)) : Int)
        = ((M.round_of S.hc (s + 1) : Nat) : Int) - 1 := by
      push_cast [Nat.cast_sub hr'0]; ring
    rw [hsub] at ha'
    have hcs := (pCR% confirmation_time_closed_cr) facts S.E s
    have hp1 : 0 ≤ S.E.Δ * ((s : Int) + 1 - ((M.round_of S.hc (s + 1) : Nat) : Int) * (S.hc.R : Int)) :=
      mul_nonneg (le_of_lt hd) (by linarith)
    have hp2 : 0 ≤ S.E.Δ * ((S.hc.R : Int) - 3) := mul_nonneg (le_of_lt hd) (by linarith)
    have hw : v ∈ Sched.awakeThroughout (M.early S.E S.hc (M.round_of S.hc (s + 1)) .g2 - S.E.Δ)
        (M.confirmation_time S.E s) :=
      awakeThroughout_mono Sched hvA (by rw [hea, ha, ha']; nlinarith) le_rfl
    rw [← hτ] at hw ⊢
    refine facts.ndRun.run_fact_g2_at S Sched x m τ _ v hlbl ?_ hw (fun t ht => hvh t (by rw [← hτ]; exact ht))
    rw [hea, ha, hτ, hcs]
    nlinarith
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc (M.toHealing (x[m][v].st).st.core)
    (M.confirmation_time S.E s) (x[m][v].st).cache
  obtain ⟨o, ho'⟩ := facts.gr.frameStableRoot_nonempty c S.E S.hc
    (M.toHealing (M.ns_setClock S.E (x[m][v].st).st (M.confirmation_time S.E s)).core)
    ((M.round_of S.hc) (M.ns_setClock S.E (x[m][v].st).st (M.confirmation_time S.E s)).core.s)
  have ho := (facts.nd.gradeContract_stableRoot _ _ _ _ _ o).2 ho'
  obtain ⟨G, rfl, hstab, hconf⟩ := Restated.records_after_confirmation_tick facts S Sched x
    hm haw hneTick hrun c hc o ho
  have hGP : Restated.AncestorOfHonestHeadsFromTo M S Sched x G (s + 3) sEnd :=
    Restated.stableRoot_ancestorOfHonestHeadsFrom_ofAwake_upTo facts S Sched x tE hexec hmono htd tGAT gap
      hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec hprev hclear hB' hnW hAW
      hJswitch hr₀ hTW₀ hJ₀ hs0 hr1 hm hvA hvh hc ho hb₀
  have hnewstab : Restated.AncestorOfHonestHeadsFromTo M S Sched x
      (M.advance_confirmed (x[m][v].st).st.core.latest_stable G) (s + 3) sEnd :=
    Restated.ancestorOfHonestHeadsFrom_advance_confirmed_upTo facts S Sched x hGP (fun _ => hL)
  refine ⟨by rw [hstab]; exact hnewstab, ?_⟩
  obtain ⟨D, hD⟩ := facts.dt.update_confirmation_with_nonempty (M.gradeContract c) S.E S.hc
    (M.ns_setClock S.E (x[m][v].st).st (M.confirmation_time S.E s)).core s
  obtain ⟨cand, hfl, hcases⟩ := (pW% update_confirmation_with_latest_confirmed_candidate_csw) facts
    (M.gradeContract c) S.E S.hc _ s D hD
  have hDstab : D.latest_stable = M.advance_confirmed (x[m][v].st).st.core.latest_stable G := by
    rw [facts.hd.update_confirmation_with_latest_stable_of_root _ _ _ _ _ (some G) ho rfl D hD,
      facts.hd.setClock_core_latest_stable]
  rw [facts.hd.setClock_core_latest_confirmed] at hfl hcases
  rw [hconf D hD, hfl, hDstab]
  refine Restated.ancestorOfHonestHeadsFrom_floor_on_stable_upTo facts S Sched x hnewstab (fun _ => ?_)
    (fun _ => hC)
  rcases hcases with hcand | hcand | ⟨G', hsel, hcand⟩
  · rw [hcand]; exact hC
  · -- the eligible walk result is the `live_confirmed` written at the tick
    have hJ1 := Restated.live_confirmed_ancestorOfHonestHeadsFrom_ofJoint_upTo facts S Sched x tE hexec hmono
      htd tGAT gap hgst hlen (hsync.monoU facts hb₀) hthird hphase hrsW hmult hcv hcs hcom hw hs hrec
      hprev hclear hB' hnW hAW hJswitch hr₀ hTW₀ hJ₀ hs0 hm hvaw hvh hrun
    rw [(pW% live_confirmed_after_confirmation_tick_outcome_csw) facts S Sched x hm haw
      hneTick hrun c hc D hD] at hJ1
    rw [hcand]
    exact Restated.ancestorOfHonestHeadsFrom_advance_confirmed_upTo facts S Sched x
      (Restated.ancestorOfHonestHeadsFrom_mono_upTo facts S Sched x (Nat.le_add_right _ 2) hJ1) (fun _ => hC)
  · -- the select candidate is the stable root
    have hGG : G = G' := Option.some.inj
      ((pW% confirmationSG_stableRoot_csw) facts c S.E S.hc _ s hsel (some G) ho)
    subst hGG
    rw [hcand]
    exact Restated.ancestorOfHonestHeadsFrom_advance_confirmed_upTo facts S Sched x hGP
      (fun _ => hC)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Under its premises on the execution and the phase ending at `tE`, with synchrony up to `b₀`
    where `max tE (S.a (round_of (sEnd − 2) + 1)) ≤ b₀`, and the joint invariant at a round `r₀` at
    or after the switch round for an anchor that is `T_W` or a descendant of it: if `r₀ < r_b`, step
    `k₀`'s time is at or after `S.a r_b`, `v`'s two records satisfy `RecordsAncestorOfHonestHeadsTo`
    up to `sEnd` after `k₀` steps, `k₀ ≤ N`, `v` is awake from `S.a (r_b − 1)` to every slot
    confirmation instant after `x[k₀].time` and at or before `x[N].time`, and `v` is honest through
    step `N`, then `v`'s two records satisfy `RecordsAncestorOfHonestHeadsTo` up to `sEnd` after `N`
    steps. -/
theorem records_ancestorOfHonestHeads_of_base_honestThrough_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) {b₀ : Int} (hsync : Restated.SynchronyFromWakeBefore M S x b₀) (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight) (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t) (hrsW : Restated.roundSleepinessW M S Sched tE) (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT) (hcs : Restated.committeeSleepinessW M S Sched tE) (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched)) (hw : Restated.WakesAtActionInstants M S Sched) (hs : Restated.SleepsAfterActionInstants M S Sched) (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap) (hprev : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.BasePreviousRoundSGCompatibleWithAnchorAtRound M S Sched x v r N
        (Restated.runAllPath M S Sched x v N) T) (hclear : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round) (n₀ : Nat),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S r)) →
      Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T) (hB' : Restated.BaseJustifiedHighAtSwitchRoundW M S Sched x tGAT tE gap) {n_W : Nat} (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)))) {T_W : NamedBlock V} (hAW : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.switchRound M S tE) T_W) (hJswitch : ∀ (v : V) (n₁ : Nat),
      M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) - 1
        ≤ (x[n₁].time : Int) →
      n₁ ≤ n_W → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J T_W.erase) {sEnd : Slot}
    {r₀ : Round} {n₀ : Nat} {T₀ : NamedBlock V}
    (hr₀ : Restated.switchRound M S tE ≤ r₀) (hTW₀ : Block.Preceq T_W.erase T₀.erase)
    (hJ₀ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x r₀ n₀ n_W T₀)
    {r_b : Round} (hrb : r₀ + 1 ≤ r_b) {k₀ : Nat} (hk₀ : (Restated.Vocabulary.Execution.Setup.a M S r_b) ≤ (x[k₀].time : Int))
    {v : V} (hbase : Restated.RecordsAncestorOfHonestHeadsTo M S Sched x v k₀ sEnd)
    {N : Nat} (hkN : k₀ ≤ N)
    (hwin : ∀ s : Slot, (x[k₀].time : Int) < M.confirmation_time S.E s →
      M.confirmation_time S.E s ≤ (x[N].time : Int) →
      v ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S (r_b - 1))) (M.confirmation_time S.E s))
    (hvh : Restated.HonestThrough M Sched x N v)
    (hb₀ : max tE ((Restated.Vocabulary.Execution.Setup.a M S ((M.round_of S.hc (sEnd - 2)) + 1))) ≤ b₀) :
    Restated.RecordsAncestorOfHonestHeadsTo M S Sched x v N sEnd := by
  have hd := S.E.Δ_pos
  have hrb0 : 0 < r_b := Nat.lt_of_lt_of_le (Nat.succ_pos r₀) hrb
  suffices key : ∀ n : Nat, k₀ ≤ n → n ≤ N → Restated.RecordsAncestorOfHonestHeadsTo M S Sched x v n sEnd
    from key N hkN le_rfl
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => intro _; exact hbase
  | succ n hkn ih =>
    intro hnN
    have ihn := ih (Nat.le_of_succ_le hnN)
    rcases Restated.records_succ_cases facts S Sched x v n with ⟨h1, h2⟩ | ⟨s, hm, haw⟩
    · have hsl : S.E.slotOf (x[n].time : Int) + 2 ≤ S.E.slotOf (x[n + 1].time : Int) + 2 :=
        Nat.add_le_add_right (slotOf_mono_sts S (Restated.time_mono_int facts S Sched x (Nat.le_succ n))) 2
      unfold Restated.RecordsAncestorOfHonestHeadsTo
      rw [h1, h2]
      exact ⟨Restated.ancestorOfHonestHeadsFrom_mono_upTo facts S Sched x hsl ihn.1,
        Restated.ancestorOfHonestHeadsFrom_mono_upTo facts S Sched x hsl ihn.2⟩
    · obtain ⟨hn1, hn0⟩ := Restated.tickStepAt_time facts x hm
      have hslot : S.E.slotOf (x[n + 1].time : Int) = s + 1 := by
        rw [hn1]; exact facts.sch.Optimistic_slotOf_confirmation_time S.E s
      have htk : (x[k₀].time : Int) < M.confirmation_time S.E s := by
        have := Restated.time_mono_int facts S Sched x hkn; linarith
      have htN : M.confirmation_time S.E s ≤ (x[N].time : Int) := by
        rw [← hn1]; exact Restated.time_mono_int facts S Sched x hnN
      obtain ⟨hs1, hrr, hwinlo, -, -⟩ :=
        Restated.confirmation_tick_arith facts S hrb0 (lt_of_le_of_lt hk₀ htk)
      have hs0 : (M.opening_slot S.hc r₀) + 2 ≤ s := by
        have h1 := facts.gr.opening_slot_mono S hrb
        rw [facts.gr.opening_slot_succ] at h1
        exact nat_add_two_le_c3 h1 hs1 S.hc.R_ge_three
      have hwin' := hwin s htk htN
      have hvaw : v ∈ Sched.awakeThroughout (slotStart S.E.Δ s - S.E.Δ)
          (M.confirmation_time S.E s) := awakeThroughout_mono Sched hwin' hwinlo le_rfl
      have hvA : v ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S ((M.round_of S.hc (s + 1)) - 1)))
          (M.confirmation_time S.E s) :=
        awakeThroughout_mono Sched hwin' (Restated.action_mono facts S (Nat.sub_le_sub_right hrr 1)) le_rfl
      have hvh' : HonestThroughTime Sched (M.confirmation_time S.E s) v :=
        fun t ht => hvh t (le_trans ht htN)
      have hL : Restated.AncestorOfHonestHeadsFromTo M S Sched x (x[n][v].st).st.core.latest_stable (s + 3)
          sEnd :=
        Restated.ancestorOfHonestHeadsFrom_mono_upTo facts S Sched x (Nat.add_le_add_right
          (by rw [← facts.sch.Optimistic_slotOf_confirmation_time S.E s]
              exact slotOf_mono_sts S (by linarith)) 2) ihn.1
      have hC : Restated.AncestorOfHonestHeadsFromTo M S Sched x (x[n][v].st).st.core.latest_confirmed
          (s + 3) sEnd :=
        Restated.ancestorOfHonestHeadsFrom_mono_upTo facts S Sched x (Nat.add_le_add_right
          (by rw [← facts.sch.Optimistic_slotOf_confirmation_time S.E s]
              exact slotOf_mono_sts S (by linarith)) 2) ihn.2
      have hres := Restated.records_after_confirmation_tick_ancestorOfHonestHeadsFrom_ofAwake_upTo facts S Sched
        x tE hexec hmono htd tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hw
        hs hrec hprev hclear hB' hnW hAW hJswitch hr₀ hTW₀ hJ₀ hs0 (le_trans hrb hrr) hm hvaw hvA
        hvh' hL hC hb₀
      unfold Restated.RecordsAncestorOfHonestHeadsTo
      rw [hslot]
      exact hres

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Under its premises on the execution and the phase ending at `tE`, with synchrony up to `b₀`
    where `max tE (S.a (round_of (sEnd − 2) + 1)) ≤ b₀`, the joint invariant at the switch round for
    an anchor that is `T_W` or a descendant of it, and `RecordsSettledAtActionTicksTo` up to `sEnd`:
    if `v` is honest through step `i`, `x[i].time` is at or after `confirmedSettleTime S tE`, and
    `v` is in `activeAtW` at the slot of `x[i].time`, then `v`'s two records after `i` steps satisfy
    `RecordsAncestorOfHonestHeadsTo` up to `sEnd`, and its `get_confirmed` is an ancestor of every
    honest head of the slots from `slot(x[i].time) + 2` to `sEnd`. -/
theorem records_ancestorOfHonestHeads_of_settle_honestThrough_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) {b₀ : Int} (hsync : Restated.SynchronyFromWakeBefore M S x b₀) (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight) (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t) (hrsW : Restated.roundSleepinessW M S Sched tE) (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT) (hcs : Restated.committeeSleepinessW M S Sched tE) (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched)) (hw : Restated.WakesAtActionInstants M S Sched) (hs : Restated.SleepsAfterActionInstants M S Sched) (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap) (hprev : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.BasePreviousRoundSGCompatibleWithAnchorAtRound M S Sched x v r N
        (Restated.runAllPath M S Sched x v N) T) (hclear : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round) (n₀ : Nat),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S r)) →
      Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T) (hB' : Restated.BaseJustifiedHighAtSwitchRoundW M S Sched x tGAT tE gap) {n_W : Nat} (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)))) {T_W : NamedBlock V} (hAW : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.switchRound M S tE) T_W) (hJswitch : ∀ (v : V) (n₁ : Nat),
      M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) - 1
        ≤ (x[n₁].time : Int) →
      n₁ ≤ n_W → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J T_W.erase) {sEnd : Slot}
    {n₀ : Nat} {T₀ : NamedBlock V} (hTW₀ : Block.Preceq T_W.erase T₀.erase)
    (hJ₀ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x (Restated.switchRound M S tE) n₀ n_W T₀)
    (hsettle : Restated.RecordsSettledAtActionTicksTo M S Sched x tE sEnd)
    {i : Nat} {v : V}
    (hvi : Restated.HonestThrough M Sched x i v)
    (hti : Restated.confirmedSettleTime M S tE ≤ (x[i].time : Int))
    (hva : v ∈ activeAtW S Sched (S.E.slotOf (x[i].time : Int)))
    (hb₀ : max tE ((Restated.Vocabulary.Execution.Setup.a M S ((M.round_of S.hc (sEnd - 2)) + 1))) ≤ b₀) :
    Restated.RecordsAncestorOfHonestHeadsTo M S Sched x v i sEnd ∧
      Restated.AncestorOfHonestHeadsFromTo M S Sched x (M.get_confirmed (x[i][v].st).st.core)
        (S.E.slotOf (x[i].time : Int) + 2) sEnd := by
  have hd := S.E.Δ_pos
  have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
  set t : Int := (x[i].time : Int) with ht
  set s_i : Slot := S.E.slotOf t with hs_i
  set rW := Restated.switchRound M S tE with hrW
  have ht0 : 0 ≤ t := Int.natCast_nonneg _
  have hts : (Restated.Vocabulary.Execution.Setup.a M S (rW + 1)) ≤ t := hti
  have hrW0 : 0 < rW := Restated.round_pos_of_switch facts S tGAT tE gap hgst hlen le_rfl
  have hss0 : slotStart S.E.Δ s_i ≤ t := slotStart_le_of_le_slotOf S ht0 le_rfl
  have hss1 : t < slotStart S.E.Δ (s_i + 1) := (slotStart_succ_slotOf_bounds S ht0).1
  rw [slotStart_closed] at hss0 hss1
  have hwv : wVote S = (4 * (S.hc.R : Int) + 2) * S.E.Δ := rfl
  have hva' : v ∈ Sched.awakeThroughout (slotStart S.E.Δ s_i + S.E.Δ - wVote S)
      (slotStart S.E.Δ s_i + S.E.Δ) := hva
  rw [slotStart_closed, hwv] at hva'
  push_cast at hss1
  have hsi : (S.hc.R : Int) * ((rW : Int) + 1) + 1 ≤ (s_i : Int) := by
    have h1 : 4 * S.E.Δ * ((S.hc.R : Int) * ((rW : Int) + 1) + 1)
        < 4 * S.E.Δ * ((s_i : Int) + 1) := by
      have := (pCR% action_closed_cr) facts S (rW + 1)
      push_cast at this
      linarith
    exact int_le_of_four_mul_lt _ _ _ hd h1
  have hrW1 : (1 : Int) ≤ (rW : Int) := by exact_mod_cast hrW0
  have hsi2 : 2 * (S.hc.R : Int) + 1 ≤ (s_i : Int) := by
    have := mul_nonneg (by linarith : (0 : Int) ≤ (S.hc.R : Int))
      (by linarith : (0 : Int) ≤ (rW : Int) - 1)
    nlinarith
  have hpR : 0 ≤ S.E.Δ * ((S.hc.R : Int) - 3) := mul_nonneg (le_of_lt hd) (by linarith)
  have hpsi : 0 ≤ S.E.Δ * ((s_i : Int) - 2 * (S.hc.R : Int) - 1) :=
    mul_nonneg (le_of_lt hd) (by linarith)
  have hpsi' : 0 ≤ S.E.Δ * ((s_i : Int) - (S.hc.R : Int) * ((rW : Int) + 1) - 1) :=
    mul_nonneg (le_of_lt hd) (by linarith)
  have hw0vt : 4 * S.E.Δ * (s_i : Int) + S.E.Δ - (4 * (S.hc.R : Int) + 2) * S.E.Δ
      ≤ 4 * S.E.Δ * (s_i : Int) + S.E.Δ := by
    have := mul_nonneg (by linarith : (0 : Int) ≤ 4 * (S.hc.R : Int) + 2) (le_of_lt hd)
    linarith
  have hw0 : (Restated.Vocabulary.Execution.Setup.a M S 0) ≤ 4 * S.E.Δ * (s_i : Int) + S.E.Δ - (4 * (S.hc.R : Int) + 2) * S.E.Δ := by
    rw [(pCR% action_closed_cr) facts]
    push_cast
    linarith
  obtain ⟨r_a, ha0, ha1⟩ := Restated.exists_action_round facts S hw0
  have hWa : v ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S r_a)) (4 * S.E.Δ * (s_i : Int) + S.E.Δ) :=
    Restated.awakeThroughout_from_action facts S Sched hw ha0 ha1 hw0vt hva'
  obtain ⟨r_c, hc0, hc1⟩ := Restated.exists_action_round facts S (t := 4 * S.E.Δ * (s_i : Int) + S.E.Δ)
    (le_trans hw0 hw0vt)
  have hc0' : (Restated.Vocabulary.Execution.Setup.a M S r_c) < 4 * S.E.Δ * (s_i : Int) + S.E.Δ := by
    rcases lt_or_eq_of_le hc0 with h | h
    · exact h
    · exact (Restated.action_ne_vote_instant facts S r_c s_i (by rw [slotStart_closed]; exact h)).elim
  have hvt : v ∈ Sched.awake (4 * S.E.Δ * (s_i : Int) + S.E.Δ) :=
    mem_awake_of_awakeThroughout Sched hWa (le_trans ha0 hw0vt) le_rfl
  have hWe : v ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S r_a)) ((Restated.Vocabulary.Execution.Setup.a M S (r_c + 1))) := by
    refine mem_awakeThroughout_of_forall Sched ?_
    intro t' h0 h1
    by_cases hle : t' ≤ 4 * S.E.Δ * (s_i : Int) + S.E.Δ
    · exact mem_awake_of_awakeThroughout Sched hWa h0 hle
    · exact Restated.awake_forward_to_action facts S Sched hs hc0' hvt t' (by linarith) h1
  have hrac : r_a ≤ r_c :=
    Nat.le_of_lt_succ (Restated.round_lt_of_action_lt facts S (lt_of_le_of_lt (le_trans ha0 hw0vt) hc1))
  have hWc : rW ≤ r_c := by
    have h1 : (Restated.Vocabulary.Execution.Setup.a M S rW) < (Restated.Vocabulary.Execution.Setup.a M S (r_c + 1)) := by
      refine lt_of_le_of_lt ?_ hc1
      rw [(pCR% action_closed_cr) facts]
      linarith
    exact Nat.le_of_lt_succ (Restated.round_lt_of_action_lt facts S h1)
  have hce : ∀ s : Slot, M.confirmation_time S.E s ≤ t →
      M.confirmation_time S.E s ≤ (Restated.Vocabulary.Execution.Setup.a M S (r_c + 1)) := by
    intro s hs'
    have hc1' := hc1
    rw [(pCR% action_closed_cr) facts] at hc1' ⊢
    push_cast at hc1' ⊢
    rw [(pCR% confirmation_time_closed_cr) facts] at hs' ⊢
    have h1 : (s : Int) + 1 ≤ (s_i : Int) := by
      refine int_le_of_four_mul_lt _ _ _ hd ?_
      linarith
    have h2 : (s_i : Int) ≤ (S.hc.R : Int) * ((r_c : Int) + 1) + 1 := by
      refine int_le_of_four_mul_lt _ _ _ hd ?_
      linarith
    have := mul_nonneg (le_of_lt hd)
      (by linarith : (0 : Int) ≤ (S.hc.R : Int) * ((r_c : Int) + 1) - (s : Int))
    linarith
  obtain ⟨r_w, hrw, hWw, hdisj⟩ := Restated.awake_stretch_start facts S Sched hw rW r_a hWe
  have hRr : ∀ r : Round, (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) - wAttest S = (Restated.Vocabulary.Execution.Setup.a M S r) := Restated.wAttest_eq_action_succ_sub facts S
  by_cases hcase : r_w ≤ rW
  · -- the base round is the round after the switch round
    have hWb : v ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S rW)) ((Restated.Vocabulary.Execution.Setup.a M S (r_c + 1))) :=
      awakeThroughout_mono Sched hWw (Restated.action_mono facts S hcase) le_rfl
    obtain ⟨n_b, hn_b⟩ := Restated.tick_field_at_succ facts S Sched x htd rW
    obtain ⟨hnb1, hnb0⟩ := Restated.tickStepAt_time facts x hn_b
    have hHon : v ∈ Restated.HonRound M S Sched (rW + 1) := by
      refine Finset.mem_sdiff.2 ⟨?_, fun hadv => hvi _ (by linarith) hadv⟩
      show v ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S (rW + 1)) - wAttest S) ((Restated.Vocabulary.Execution.Setup.a M S (rW + 1)))
      rw [hRr]
      exact awakeThroughout_mono Sched hWb le_rfl (Restated.action_mono facts S (Nat.succ_le_succ hWc))
    have hbase := hsettle (rW + 1) n_b v le_rfl hn_b hHon (Or.inl rfl)
    have hki : n_b + 1 ≤ i := by
      by_contra hcon
      have := Restated.time_mono_int facts S Sched x (Nat.le_of_lt_succ (Nat.lt_of_not_le hcon))
      linarith
    have hrec' := Restated.records_ancestorOfHonestHeads_of_base_honestThrough_upTo facts S Sched x tE hexec
      hmono htd tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec hprev
      hclear hB' hnW hAW hJswitch le_rfl hTW₀ hJ₀ (r_b := rW + 1) le_rfl (by rw [hnb1]) hbase hki
      (fun s _ hs2 => by
        rw [Nat.add_sub_cancel]
        exact awakeThroughout_mono Sched hWb le_rfl (hce s hs2)) hvi hb₀
    exact ⟨hrec', (Restated.outputs_ancestorOfHonestHeads_of_records_upTo facts S Sched x tE hexec hmono htd
      tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec hprev hclear hB'
      hnW hAW hJswitch le_rfl hTW₀ hJ₀ (le_trans (Restated.action_mono facts S (Nat.le_succ rW)) hts) hvi
      hrec' hb₀).2⟩
  · -- the base round is the round after the reader's last wake
    have hwc : r_w + 1 ≤ r_c + 1 := Nat.succ_le_succ (le_trans hrw hrac)
    obtain ⟨n_b, hn_b⟩ := Restated.tick_field_at_succ facts S Sched x htd r_w
    obtain ⟨hnb1, hnb0⟩ := Restated.tickStepAt_time facts x hn_b
    have hat : (Restated.Vocabulary.Execution.Setup.a M S (r_w + 1)) ≤ t := by
      have h1 := Restated.action_mono facts S (Nat.succ_le_succ hrw)
      have h2 := facts.gr.action_succ_eq_add_rounds S r_a
      linarith
    have hHon : v ∈ Restated.HonRound M S Sched (r_w + 1) := by
      refine Finset.mem_sdiff.2 ⟨?_, fun hadv => hvi _ hat hadv⟩
      show v ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S (r_w + 1)) - wAttest S) ((Restated.Vocabulary.Execution.Setup.a M S (r_w + 1)))
      rw [hRr]
      exact awakeThroughout_mono Sched hWw le_rfl (Restated.action_mono facts S hwc)
    have hasleep : v ∉ Sched.awake ((Restated.Vocabulary.Execution.Setup.a M S (r_w + 1 - 1)) - 1) := by
      rw [Nat.add_sub_cancel]
      rcases hdisj with h | h
      · exact absurd h hcase
      · exact h
    have hbase := hsettle (r_w + 1) n_b v (Nat.succ_le_succ (le_of_lt (Nat.lt_of_not_le hcase)))
      hn_b hHon (Or.inr hasleep)
    have hki : n_b + 1 ≤ i := by
      by_contra hcon
      have := Restated.time_mono_int facts S Sched x (Nat.le_of_lt_succ (Nat.lt_of_not_le hcon))
      linarith
    have hrec' := Restated.records_ancestorOfHonestHeads_of_base_honestThrough_upTo facts S Sched x tE hexec
      hmono htd tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec hprev
      hclear hB' hnW hAW hJswitch le_rfl hTW₀ hJ₀ (r_b := r_w + 1)
      (Nat.succ_le_succ (le_of_lt (Nat.lt_of_not_le hcase))) (by rw [hnb1]) hbase hki
      (fun s _ hs2 => by
        rw [Nat.add_sub_cancel]
        exact awakeThroughout_mono Sched hWw le_rfl (hce s hs2)) hvi hb₀
    exact ⟨hrec', (Restated.outputs_ancestorOfHonestHeads_of_records_upTo facts S Sched x tE hexec hmono htd
      tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec hprev hclear hB'
      hnW hAW hJswitch le_rfl hTW₀ hJ₀ (le_trans (Restated.action_mono facts S (Nat.le_succ rW)) hts) hvi
      hrec' hb₀).2⟩

end

end DecoupledConsensusModel.Sts.Restated
