import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bK_ConfirmedRecord
import Proofs.Claims.Restated.Claim13bK_ConfirmedSettle
import Proofs.Claims.Restated.Claim13bK_ConfirmedStrongRoundWindow
import Proofs.Claims.Restated.Claim13bK_Frame
import Proofs.Claims.Restated.Claim13bK_HeadsPersist
import Proofs.Claims.Restated.Claim13bK_LiveConfirmedSlots
import Proofs.Claims.Restated.Claim13bK_PrevHeadsStep
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
import Model.Conditions.Claim13bK_ConfirmedRecord
import Model.Conditions.Claim13bK_ConfirmedSettle
import Model.Conditions.Claim13bK_FinBeforeTick
import Model.Conditions.Claim13bK_Frame
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13bStepCone
import Model.Conditions.Claim13bStepConeIter
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_74
import Model.Conditions.Claim13beRoute3_83
import Model.Conditions.RunAll
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13bd
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Sts_Spec2Claims_Claim13bf
import Model.Conditions.Sts_Spec2Claims_ClaimConfirmedAfterHealing
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Vocabulary.Protocol.Grades
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Protocol_Grades_Main
import Model.Record.Wiring
import Proofs.Claims.Restated.Claim13bK_PrevHeadsStepRecv

/-!
# Records of readers awake from t₀, from a receipt

`graded_ancestorOfHonestHeadsFrom_at_awakeReader`, `stableRoot_ancestorOfHonestHeadsFrom_ofAwake` and
`records_after_confirmation_tick_ancestorOfHonestHeadsFrom_ofAwake` of
`Claim13bK_ConfirmedRecordReaders.lean` with the reader awake from some `t₀` at or before the
grade's late cutoff less `2 * Δ + 1` in place of an action instant, its receipt of the previous
round's honest attestations before the grade's first cutoff, and, for the confirmation tick, the
grade-2 awake test that tick passed as a hypothesis.
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
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- Under its premises on the execution and the phase ending at `tE`, if round `r` is at or after
    the switch round, `T_W` is an ancestor of `T`, the joint invariant holds at round `r` with
    anchor `T` and at round `r + 1`, `v` is awake from `t₀` to the domain instant of a
    round-`(r + 1)` phase `p`, with `t₀` at or before `p`'s late cutoff less `2 * Δ + 1`, receives
    round `r`'s honest attestations before `p`'s first cutoff, and is not held by the adversary there, `m` is the step before that
    instant, and the grade test of phase `p` at `v`'s store after `m` steps can return `true` for
    `B`, then every honest active committee member of every slot from round `r + 1`'s opening slot
    on votes for a descendant of `B`. -/
theorem graded_ancestorOfHonestHeadsFrom_at_awakeReader_recv (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (hcatch : Restated.CatchUpOnWake M S x) (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (hsync : Restated.SynchronyFromWake M S x) (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight) (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t) (hrsW : Restated.roundSleepinessW M S Sched tE) (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT) (hcs : Restated.committeeSleepinessW M S Sched tE) (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched)) (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap) (hprev : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
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
      Block.Preceq (x[n₁][v].st).st.core.J T_W.erase)
    {r : Round} {n n₁ : Nat} {T T₁ : NamedBlock V}
    (hr : Restated.switchRound M S tE ≤ r) (hTW : Block.Preceq T_W.erase T.erase)
    (hJ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x r n n_W T)
    (hJ₁ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x (r + 1) n₁ n_W T₁)
    {v : V} {p : Protocol.Phase}
    (t₀ : Int) (ht₀ : t₀ ≤ M.late S.E S.hc (r + 1) p - 1 - 2 * S.E.Δ)
    (hawT : v ∈ Sched.awakeThroughout t₀ (M.domain S.E S.hc (r + 1) p))
    (hrecv : Restated.ReceivesRoundAttestationsBefore M S Sched x r v (M.early S.E S.hc (r + 1) p))
    (hvS : v ∉ Sched.adv (M.domain S.E S.hc (r + 1) p))
    {m : Nat} (hm : Restated.stepBeforeInstant M x m (M.domain S.E S.hc (r + 1) p))
    {B : Block V}
    (hB : M.gradeBool S.E (M.gradeView (M.toHealing (x[m][v].st).st.core))
      (x[m][v].st).st.core.F S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) p)
      (M.late S.E S.hc (r + 1) p) B ⇢ true) :
    Restated.AncestorOfHonestHeadsFrom M S Sched x B ((M.opening_slot S.hc (r + 1))) := by
  have hTop := (pHP% joint_toTop_hp) hJ
  have hcross : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepFinalizedCrossingUnderAnchor M S Sched x r n'' T :=
    fun n'' h => Restated.stepFinalizedCrossingUnderAnchor_of_afterSwitch facts S Sched x hr hnW
      hJ.toAfterPhaseInvariantOverActiveSetsSince
      (Restated.justified_preceq_anchor_ofJoint facts S Sched x tE hexec hmono htd tGAT gap hgst hlen hsync
        hthird hphase hrsW hmult hcv hcom hrec hprev hclear hB' hnW hAW hr hTW hJ h)
  obtain ⟨v_1, hv_1, a, har, hai, has, C, hC, hac, hBC⟩ :=
    Restated.graded_preceq_freshSG_at_awakeReader_recv facts S Sched x tE hexec hmono htd hsync
      hmult tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr hTop hcross
      (facts.gr.domain_le_action S (r + 1) p) t₀ ht₀ hawT hrecv hvS hm B hB
  have hCT : Block.compatible C.erase T.erase = true :=
    hTop.sg v_1 hv_1 a har hai has C hC hac
  have hPH := hJ₁.prevHeads
  simp only [Nat.add_sub_cancel] at hPH
  have hCheads : Restated.HeadsBelow M S Sched x C.erase ((M.opening_slot S.hc (r + 1))) :=
    hPH n hTop.tick v_1 hv_1 a har hai has C hC hac
  have hs0 : (M.opening_slot S.hc r) + 1 ≤ (M.opening_slot S.hc (r + 1)) := by
    rw [facts.gr.opening_slot_succ]
    exact Nat.add_le_add_left (le_trans (by decide : 1 ≤ 3) S.hc.R_ge_three) _
  have hCP := Restated.ancestorOfHonestHeadsFrom_of_compatible_anchor facts S Sched x tE hexec hmono htd hcatch
    tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hrec hprev hclear hB'
    hnW hAW hJswitch hr hTW hJ hs0 (Nat.le_succ _) hCT hCheads
  exact Restated.ancestorOfHonestHeadsFrom_of_preceq facts S Sched x hBC hCP

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- Under its premises on the execution and the phase ending at `tE`, with the joint invariant at a
    round `r₀` at or after the switch round for an anchor that is `T_W` or a descendant of it: if
    slot `s` is at least two after round `r₀`'s opening slot, the round `r'` of `s + 1` is after
    `r₀`, `m` is the tick step at slot `s`'s confirmation instant, `v` is awake from `t₀` to that
    instant, with `t₀` at or before round `r'`'s grade-2 late cutoff less `2 * Δ + 1`, receives round
    `r' − 1`'s honest attestations before round `r'`'s grade-2 first cutoff and is honest through
    that instant, `c` is an outcome of `v`'s phase tick there, and `some G`
    is an outcome of the stable root of `c`'s grade contract at the clock-stamped store's round,
    then `G` is an ancestor of every honest head from slot `s + 3` on. -/
theorem stableRoot_ancestorOfHonestHeadsFrom_ofAwake_recv (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (hcatch : Restated.CatchUpOnWake M S x) (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (hsync : Restated.SynchronyFromWake M S x) (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight) (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t) (hrsW : Restated.roundSleepinessW M S Sched tE) (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT) (hcs : Restated.committeeSleepinessW M S Sched tE) (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched)) (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap) (hprev : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
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
      Block.Preceq (x[n₁][v].st).st.core.J T_W.erase)
    {r₀ : Round} {n₀ : Nat} {T₀ : NamedBlock V}
    (hr₀ : Restated.switchRound M S tE ≤ r₀) (hTW₀ : Block.Preceq T_W.erase T₀.erase)
    (hJ₀ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x r₀ n₀ n_W T₀)
    {s : Slot} (hs0 : (M.opening_slot S.hc r₀) + 2 ≤ s)
    (hr1 : r₀ + 1 ≤ (M.round_of S.hc (s + 1)))
    {m : Nat} (hm : Restated.tickStepAt M x m (M.confirmation_time S.E s)) {v : V}
    (t₀ : Int) (ht₀ : t₀ ≤ M.late S.E S.hc (M.round_of S.hc (s + 1)) .g2 - 1 - 2 * S.E.Δ)
    (hvA : v ∈ Sched.awakeThroughout t₀ (M.confirmation_time S.E s))
    (hrecv : Restated.ReceivesRoundAttestationsBefore M S Sched x ((M.round_of S.hc (s + 1)) - 1) v
      (M.early S.E S.hc (M.round_of S.hc (s + 1)) .g2))
    (hvh : HonestThroughTime Sched (M.confirmation_time S.E s) v)
    {G : Block V} {c : M.Cache}
    (hc : M.onPhaseTick S.E S.hc (M.toHealing (x[m][v].st).st.core)
        (M.confirmation_time S.E s) (x[m][v].st).cache ⇢ c)
    (hG : (M.gradeContract c).stableRoot S.E S.hc
          (M.toHealing (M.ns_setClock S.E (x[m][v].st).st
            (M.confirmation_time S.E s)).core)
          ((M.round_of S.hc) (M.ns_setClock S.E (x[m][v].st).st
            (M.confirmation_time S.E s)).core.s) ⇢ some G) :
    Restated.AncestorOfHonestHeadsFrom M S Sched x G (s + 3) := by
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
    obtain ⟨n, T, hJ, -, hTW⟩ := Restated.anchor_at_later_round facts S Sched x tE hexec hmono htd hcatch
      tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hrec hprev hclear hB'
      hnW hAW hJswitch hr₀ hTW₀ hJ₀ hrr
    have hr : Restated.switchRound M S tE ≤ (M.round_of S.hc s) := le_trans hr₀ hrr
    have hroot' : Block.Preceq (Restated.Vocabulary.Protocol.confRoot M (Restated.confStoreAt M S (x[m][v].st) s)) T.erase :=
      Restated.confRoot_preceq_anchor_atSlot facts S Sched x tE hexec hmono htd tGAT gap hgst hlen hsync hthird
        hphase hrsW hmult hcv hcom hrec hprev hclear hB' hnW hAW hr hTW hJ hrs0
        (Nat.le_of_lt hrs1) hm hvm
    have hGT : Block.Preceq G T.erase := by rw [hroot]; exact hroot'
    have hanc := Restated.anchor_ancestorOfHonestHeadsFrom facts S Sched x tE hexec hmono htd hcatch tGAT gap
      hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hrec hprev hclear hB' hnW hAW
      hJswitch hr hTW hJ
    exact Restated.ancestorOfHonestHeadsFrom_mono facts S Sched x (nat_le_add3_c3 hrs0)
      (Restated.ancestorOfHonestHeadsFrom_of_preceq facts S Sched x hGT hanc)
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
    rw [hr₁] at hB hm' hr1 hrs0 hdomtc ht₀ hrecv
    simp only [Nat.add_sub_cancel] at hrecv
    have hrr₁ : r₀ ≤ r₁ := Nat.le_of_succ_le_succ hr1
    obtain ⟨n, T, hJ, -, hTW⟩ := Restated.anchor_at_later_round facts S Sched x tE hexec hmono htd hcatch
      tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hrec hprev hclear hB'
      hnW hAW hJswitch hr₀ hTW₀ hJ₀ hrr₁
    obtain ⟨n₁, T₁, hJ₁, -, -⟩ := Restated.anchor_at_later_round facts S Sched x tE hexec hmono htd hcatch
      tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hrec hprev hclear hB'
      hnW hAW hJswitch hr₀ hTW₀ hJ₀ (Nat.le_succ_of_le hrr₁)
    have hawT : v ∈ Sched.awakeThroughout t₀ (M.domain S.E S.hc (r₁ + 1) .g2) :=
      awakeThroughout_mono Sched hvA le_rfl hdomtc
    obtain ⟨b, hb⟩ := facts.gr.gradeBool_nonempty S.E
      (M.gradeView (M.toHealing (x[m'][v].st).st.core)) (x[m'][v].st).st.core.F S.hc.η_SG
      (r₁ + 1) (M.early S.E S.hc (r₁ + 1) .g2) (M.late S.E S.hc (r₁ + 1) .g2) B
    have hBt : M.gradeBool S.E (M.gradeView (M.toHealing (x[m'][v].st).st.core))
        (x[m'][v].st).st.core.F S.hc.η_SG (r₁ + 1) (M.early S.E S.hc (r₁ + 1) .g2)
        (M.late S.E S.hc (r₁ + 1) .g2) B ⇢ true := hB b hb ▸ hb
    have hBP := Restated.graded_ancestorOfHonestHeadsFrom_at_awakeReader_recv facts S Sched x tE hexec hmono htd
      hcatch tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hrec hprev
      hclear hB' hnW hAW hJswitch (le_trans hr₀ hrr₁) hTW hJ hJ₁ t₀ ht₀ hawT hrecv (hvh _ hdomtc) hm' hBt
    exact Restated.ancestorOfHonestHeadsFrom_mono facts S Sched x
      (le_trans hrs0 (Nat.add_le_add_left (by decide : 1 ≤ 3) s))
      (Restated.ancestorOfHonestHeadsFrom_of_preceq facts S Sched x
        (preceq_trans_Preceq hGroot (preceq_trans_Preceq hroot0 hroot0B)) hBP)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- Under its premises on the execution and the phase ending at `tE`, with the joint invariant at a
    round `r₀` at or after the switch round for an anchor that is `T_W` or a descendant of it: if
    slot `s` is at least two after round `r₀`'s opening slot, the round `r'` of `s + 1` is after
    `r₀`, `m` is the tick step at slot `s`'s confirmation instant, `v` is awake from one delay
    before slot `s`'s start and from `t₀` to that instant, with `t₀` at or before round `r'`'s
    grade-2 late cutoff less `2 * Δ + 1`, receives round `r' − 1`'s honest attestations before round
    `r'`'s grade-2 first cutoff, is honest through that instant and passes there the grade-2 awake
    test of round `r'`, and `v`'s
    `latest_stable` and `latest_confirmed` after `m` steps are ancestors of every honest head from
    slot `s + 3` on, then so are they after `m + 1` steps. -/
theorem records_after_confirmation_tick_ancestorOfHonestHeadsFrom_ofAwake_recv (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (hcatch : Restated.CatchUpOnWake M S x) (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (hsync : Restated.SynchronyFromWake M S x) (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight) (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t) (hrsW : Restated.roundSleepinessW M S Sched tE) (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT) (hcs : Restated.committeeSleepinessW M S Sched tE) (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched)) (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap) (hprev : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
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
      Block.Preceq (x[n₁][v].st).st.core.J T_W.erase)
    {r₀ : Round} {n₀ : Nat} {T₀ : NamedBlock V}
    (hr₀ : Restated.switchRound M S tE ≤ r₀) (hTW₀ : Block.Preceq T_W.erase T₀.erase)
    (hJ₀ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x r₀ n₀ n_W T₀)
    {s : Slot} (hs0 : (M.opening_slot S.hc r₀) + 2 ≤ s)
    (hr1 : r₀ + 1 ≤ (M.round_of S.hc (s + 1)))
    {m : Nat} (hm : Restated.tickStepAt M x m (M.confirmation_time S.E s)) {v : V}
    (hvaw : v ∈ Sched.awakeThroughout (slotStart S.E.Δ s - S.E.Δ)
      (M.confirmation_time S.E s))
    (t₀ : Int) (ht₀ : t₀ ≤ M.late S.E S.hc (M.round_of S.hc (s + 1)) .g2 - 1 - 2 * S.E.Δ)
    (hvA : v ∈ Sched.awakeThroughout t₀ (M.confirmation_time S.E s))
    (hrecv : Restated.ReceivesRoundAttestationsBefore M S Sched x ((M.round_of S.hc (s + 1)) - 1) v
      (M.early S.E S.hc (M.round_of S.hc (s + 1)) .g2))
    (hvh : HonestThroughTime Sched (M.confirmation_time S.E s) v)
    -- `v` passed the grade-2 awake test of round `round_of (s + 1)` at its tick at slot `s`'s
    -- confirmation instant.
    (hrun : M.awake_for_grade2 (Setup.alwaysAwake S) v
      (Record.wakeStage M Sched (M.confirmation_time S.E s) x[m] v) (M.round_of S.hc (s + 1)))
    (hL : Restated.AncestorOfHonestHeadsFrom M S Sched x (x[m][v].st).st.core.latest_stable (s + 3))
    (hC : Restated.AncestorOfHonestHeadsFrom M S Sched x (x[m][v].st).st.core.latest_confirmed (s + 3)) :
    Restated.AncestorOfHonestHeadsFrom M S Sched x (x[m + 1][v].st).st.core.latest_stable (s + 3) ∧
      Restated.AncestorOfHonestHeadsFrom M S Sched x (x[m + 1][v].st).st.core.latest_confirmed (s + 3) := by
  have hd := S.E.Δ_pos
  have haw : v ∈ Sched.awake (M.confirmation_time S.E s) \
      Sched.adv (M.confirmation_time S.E s) :=
    Finset.mem_sdiff.2 ⟨mem_awake_of_awakeThroughout Sched hvaw
      (by rw [slotStart_closed, (pCR% confirmation_time_closed_cr) facts]; linarith) le_rfl,
      hvh _ le_rfl⟩
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc (M.toHealing (x[m][v].st).st.core)
    (M.confirmation_time S.E s) (x[m][v].st).cache
  obtain ⟨o, ho'⟩ := facts.gr.frameStableRoot_nonempty c S.E S.hc
    (M.toHealing (M.ns_setClock S.E (x[m][v].st).st (M.confirmation_time S.E s)).core)
    ((M.round_of S.hc) (M.ns_setClock S.E (x[m][v].st).st (M.confirmation_time S.E s)).core.s)
  have ho := (facts.nd.gradeContract_stableRoot _ _ _ _ _ o).2 ho'
  have hdvd : M.confirmation_time S.E s % S.E.Δ = 0 := by
    rw [facts.sch.confirmation_time_eq_support_cutoff_succ]
    exact facts.sch.support_cutoff_emod_delta S (s + 1)
  have hneTick := Restated.tick_outcome_of_tickStepAt facts S Sched x
    hexec.idealization.root_injective hexec.honestRootsNew hmono hm hdvd haw
  obtain ⟨G, rfl, hstab, hconf⟩ := Restated.records_after_confirmation_tick facts S Sched x
    hm haw hneTick hrun c hc o ho
  have hGP : Restated.AncestorOfHonestHeadsFrom M S Sched x G (s + 3) :=
    Restated.stableRoot_ancestorOfHonestHeadsFrom_ofAwake_recv facts S Sched x tE hexec hmono htd hcatch tGAT gap
      hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hrec hprev hclear hB' hnW hAW
      hJswitch hr₀ hTW₀ hJ₀ hs0 hr1 hm t₀ ht₀ hvA hrecv hvh hc ho
  have hnewstab : Restated.AncestorOfHonestHeadsFrom M S Sched x
      (M.advance_confirmed (x[m][v].st).st.core.latest_stable G) (s + 3) :=
    Restated.ancestorOfHonestHeadsFrom_advance_confirmed facts S Sched x hGP (fun _ => hL)
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
  refine Restated.ancestorOfHonestHeadsFrom_floor_on_stable facts S Sched x hnewstab (fun _ => ?_)
    (fun _ => hC)
  rcases hcases with hcand | hcand | ⟨G', hsel, hcand⟩
  · rw [hcand]; exact hC
  · -- the eligible walk result is the `live_confirmed` written at the tick
    have hJ1 := Restated.live_confirmed_ancestorOfHonestHeadsFrom_ofJoint facts S Sched x tE hexec hmono htd
      hcatch tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hrec hprev
      hclear hB' hnW hAW hJswitch hr₀ hTW₀ hJ₀ hs0 hm hvaw hvh hrun
    rw [(pW% live_confirmed_after_confirmation_tick_outcome_csw) facts S Sched x hm haw
      hneTick hrun c hc D hD] at hJ1
    rw [hcand]
    exact Restated.ancestorOfHonestHeadsFrom_advance_confirmed facts S Sched x
      (Restated.ancestorOfHonestHeadsFrom_mono facts S Sched x (Nat.le_add_right _ 2) hJ1) (fun _ => hC)
  · -- the select candidate is the stable root
    have hGG : G = G' := Option.some.inj
      ((pW% confirmationSG_stableRoot_csw) facts c S.E S.hc _ s hsel (some G) ho)
    subst hGG
    rw [hcand]
    exact Restated.ancestorOfHonestHeadsFrom_advance_confirmed facts S Sched x hGP (fun _ => hC)

end

end DecoupledConsensusModel.Sts.Restated
