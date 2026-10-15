import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bK_ConfirmedRecord
import Proofs.Claims.Restated.Claim13bK_ConfirmedRecordUpTo
import Proofs.Claims.Restated.Claim13bK_ConfirmedSettle
import Proofs.Claims.Restated.Claim13bK_ConfirmedSettleUpTo
import Proofs.Claims.Restated.Claim13bK_ConfirmedStrongRoundWindow
import Proofs.Claims.Restated.Claim13bK_HeadsPersistUpTo
import Proofs.Claims.Restated.Claim13bStepKitConfirm
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActive
import Model.Conditions.Claim13bInvariantActiveJoint
import Model.Conditions.Claim13bInvariantActiveSinceW
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
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
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Vocabulary.Protocol.Grades
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Protocol_Grades_Main
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bK_ConfirmedRecordUpTo
import Proofs.Claims.Spec2Claims.Claim13bModel_Preceq
import Proofs.Claims.Restated.Claim13bW_ReceiptBefore

/-!
# Confirmation ticks in the window of a strong round, up to a slot

What a confirmation tick writes to a validator's stable and confirmed records, and the conditions
under which both records stay ancestors of every honest head over the slots up to `sEnd`, with
synchrony assumed only up to a bound `b₀`. Stated over a model `M : Record.Model V`.
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
local macro "pW% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13bK_ConfirmedStrongRoundWindow)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog

/-- If `SynchronyFromWakeBefore` holds up to `b'` and `b ≤ b'`, it holds up to `b`. -/
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

/-- With synchrony up to `b₀ ≥ max tE (S.a (S.hc.round_of (sEnd - 2) + 1))`, on the premises of
    `afterPhaseJointRound_of_premises`, with the joint invariant at a round `r₀` at or after the
    switch round, if slot `s` is at or after `o_{r₀} + 2`, `m` is the tick step at slot `s`'s
    confirmation time, and `v` is awake, honest and a member of `HonRound S Sched r'` for the round
    `r'` of `s + 1`, then every stable root outcome `o` at that tick is `some G` for a block `G`
    that is an ancestor of every honest head from slot `s + 3` to `sEnd`, `v`'s new `latest_stable`
    is `advance_confirmed` of the old one with `G`, and `v`'s new `latest_confirmed` is
    `floor_on_stable` of the new `latest_stable`, a candidate and the old `latest_confirmed`, the
    candidate being the old `latest_confirmed` or `advance_confirmed` of it with a block that is an
    ancestor of every honest head from slot `s + 3` to `sEnd`. -/
theorem records_after_confirmation_tick_values_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) {b₀ : Int} (hsync : Restated.SynchronyFromWakeBefore M S x b₀) (hcatchB : Restated.CatchUpOnWakeBefore M S x b₀) (hthird : ∀ t : Int, t ≤ tE →
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
      Block.Preceq (x[n₁][v].st).st.core.J T_W.erase) {sEnd : Slot}
    {r₀ : Round} {n₀ : Nat} {T₀ : NamedBlock V}
    (hr₀ : Restated.switchRound M S tE ≤ r₀) (hTW₀ : Block.Preceq T_W.erase T₀.erase)
    (hJ₀ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x r₀ n₀ n_W T₀)
    {s : Slot} (hs0 : (M.opening_slot S.hc r₀) + 2 ≤ s)
    {m : Nat} (hm : Restated.tickStepAt M x m (M.confirmation_time S.E s)) {v : V}
    (hvaw : v ∈ Sched.awakeThroughout (slotStart S.E.Δ s - S.E.Δ)
      (M.confirmation_time S.E s))
    (hvh : HonestThroughTime Sched (M.confirmation_time S.E s) v)
    (hvR : v ∈ Restated.HonRound M S Sched ((M.round_of S.hc (s + 1))))
    -- `v`'s tick at step `m` passes the grade-2 awake test of slot `s + 1`'s round.
    (hrun : M.awake_for_grade2 (Setup.alwaysAwake S) v
      (Record.wakeStage M Sched (M.confirmation_time S.E s) x[m] v) (M.round_of S.hc (s + 1)))
    (hb₀ : max tE ((Restated.Vocabulary.Execution.Setup.a M S ((M.round_of S.hc (sEnd - 2)) + 1))) ≤ b₀) :
    ∀ c : M.Cache, M.onPhaseTick S.E S.hc (M.toHealing (x[m][v].st).st.core)
        (M.confirmation_time S.E s) (x[m][v].st).cache ⇢ c →
    ∀ o : Option (Block V), (M.gradeContract c).stableRoot S.E S.hc
          (M.toHealing (M.ns_setClock S.E (x[m][v].st).st
            (M.confirmation_time S.E s)).core)
          ((M.round_of S.hc) (M.ns_setClock S.E (x[m][v].st).st
            (M.confirmation_time S.E s)).core.s) ⇢ o →
    ∃ G : Block V, o = some G ∧
      Restated.AncestorOfHonestHeadsFromTo M S Sched x G (s + 3) sEnd ∧
      (x[m + 1][v].st).st.core.latest_stable
        = M.advance_confirmed (x[m][v].st).st.core.latest_stable G ∧
      ∃ cand : Block V,
        (x[m + 1][v].st).st.core.latest_confirmed
          = M.floor_on_stable (x[m + 1][v].st).st.core.latest_stable cand
              (x[m][v].st).st.core.latest_confirmed ∧
        (cand = (x[m][v].st).st.core.latest_confirmed ∨
          ∃ Y : Block V, Restated.AncestorOfHonestHeadsFromTo M S Sched x Y (s + 3) sEnd ∧
            cand = M.advance_confirmed (x[m][v].st).st.core.latest_confirmed Y) := by
  intro c hc o ho
  have hd := S.E.Δ_pos
  have haw : v ∈ Sched.awake (M.confirmation_time S.E s) \
      Sched.adv (M.confirmation_time S.E s) :=
    Finset.mem_sdiff.2 ⟨mem_awake_of_awakeThroughout Sched hvaw
      (by rw [slotStart_closed, (pW% confirmation_time_closed_csw) facts]; linarith) le_rfl,
      hvh _ le_rfl⟩
  have hdvd : M.confirmation_time S.E s % S.E.Δ = 0 := by
    rw [facts.sch.confirmation_time_eq_support_cutoff_succ]
    exact facts.sch.support_cutoff_emod_delta S (s + 1)
  have hneTick := Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew
    hmono hm hdvd haw
  obtain ⟨G, rfl, hstab, hconf⟩ := Restated.records_after_confirmation_tick facts S Sched x
    hm haw hneTick hrun c hc o ho
  have hroot : Restated.AncestorOfHonestHeadsFromTo M S Sched x G (s + 3) sEnd :=
    Restated.stableRoot_ancestorOfHonestHeadsFrom_upTo (hcatchB := hcatchB) facts S Sched x tE hexec hmono htd tGAT gap hgst hlen
      hsync hthird hphase hrsW hmult hcv hcs hcom hrec hprev hclear hB' hnW hAW hJswitch
      hr₀ hTW₀ hJ₀ hs0 hm hvR hvh hc ho hb₀
  refine ⟨G, rfl, hroot, hstab, ?_⟩
  -- one outcome of the confirmation update, and the candidate it writes
  obtain ⟨D, hD⟩ := facts.dt.update_confirmation_with_nonempty (M.gradeContract c) S.E S.hc
    (M.ns_setClock S.E (x[m][v].st).st (M.confirmation_time S.E s)).core s
  obtain ⟨cand, hfl, hcases⟩ := (pW% update_confirmation_with_latest_confirmed_candidate_csw) facts
    (M.gradeContract c) S.E S.hc _ s D hD
  have hDstab : D.latest_stable = (x[m + 1][v].st).st.core.latest_stable := by
    rw [facts.hd.update_confirmation_with_latest_stable_of_root _ _ _ _ _ (some G) ho rfl D hD,
      facts.hd.setClock_core_latest_stable, hstab]
  rw [facts.hd.setClock_core_latest_confirmed] at hfl hcases
  refine ⟨cand, ?_, ?_⟩
  · rw [hconf D hD, hfl, hDstab]
  rcases hcases with hcand | hcand | ⟨G', hsel, hcand⟩
  · exact Or.inl hcand
  · -- the eligible walk result is the `live_confirmed` written at the tick
    right
    have hJ1 := Restated.live_confirmed_ancestorOfHonestHeadsFrom_ofJoint_upTo (hcatchB := (hcatchB.monoU facts hb₀)) facts S Sched x tE hexec hmono htd
      tGAT gap hgst hlen (hsync.monoU facts hb₀) hthird hphase hrsW hmult hcv hcs hcom hrec hprev
      hclear hB' hnW hAW hJswitch hr₀ hTW₀ hJ₀ hs0 hm hvaw hvh hrun
    rw [(pW% live_confirmed_after_confirmation_tick_outcome_csw) facts S Sched x hm haw
      hneTick hrun c hc D hD] at hJ1
    exact ⟨D.live_confirmed,
      Restated.ancestorOfHonestHeadsFrom_mono_upTo facts S Sched x (Nat.le_add_right _ 2) hJ1, hcand⟩
  · -- the select candidate is the stable root
    right
    have hGG : G = G' := Option.some.inj
      ((pW% confirmationSG_stableRoot_csw) facts c S.E S.hc _ s hsel (some G) ho)
    subst hGG
    exact ⟨G, hroot, hcand⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- On the premises of `records_after_confirmation_tick_values_upTo`, for a property `Q` of blocks
    that every ancestor of every honest head from slot `s₀ ≥ s + 3` to `sEnd` has, if `v`'s
    `latest_stable` and `latest_confirmed` after `m` steps have `Q`, so do they after `m + 1` steps. -/
theorem records_after_confirmation_tick_keep_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) {b₀ : Int} (hsync : Restated.SynchronyFromWakeBefore M S x b₀) (hcatchB : Restated.CatchUpOnWakeBefore M S x b₀) (hthird : ∀ t : Int, t ≤ tE →
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
      Block.Preceq (x[n₁][v].st).st.core.J T_W.erase) {sEnd : Slot}
    {r₀ : Round} {n₀ : Nat} {T₀ : NamedBlock V}
    (hr₀ : Restated.switchRound M S tE ≤ r₀) (hTW₀ : Block.Preceq T_W.erase T₀.erase)
    (hJ₀ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x r₀ n₀ n_W T₀)
    {s : Slot} (hs0 : (M.opening_slot S.hc r₀) + 2 ≤ s)
    {m : Nat} (hm : Restated.tickStepAt M x m (M.confirmation_time S.E s)) {v : V}
    (hvaw : v ∈ Sched.awakeThroughout (slotStart S.E.Δ s - S.E.Δ)
      (M.confirmation_time S.E s))
    (hvh : HonestThroughTime Sched (M.confirmation_time S.E s) v)
    (hvR : v ∈ Restated.HonRound M S Sched ((M.round_of S.hc (s + 1))))
    -- `v`'s tick at step `m` passes the grade-2 awake test of slot `s + 1`'s round.
    (hrun : M.awake_for_grade2 (Setup.alwaysAwake S) v
      (Record.wakeStage M Sched (M.confirmation_time S.E s) x[m] v) (M.round_of S.hc (s + 1)))
    {s₀ : Slot} (hss₀ : s + 3 ≤ s₀) (Q : Block V → Prop)
    (hQ : ∀ B : Block V, Restated.AncestorOfHonestHeadsFromTo M S Sched x B s₀ sEnd → Q B)
    (hS : Q (x[m][v].st).st.core.latest_stable) (hC : Q (x[m][v].st).st.core.latest_confirmed)
    (hb₀ : max tE ((Restated.Vocabulary.Execution.Setup.a M S ((M.round_of S.hc (sEnd - 2)) + 1))) ≤ b₀) :
    Q (x[m + 1][v].st).st.core.latest_stable ∧ Q (x[m + 1][v].st).st.core.latest_confirmed := by
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc (M.toHealing (x[m][v].st).st.core)
    (M.confirmation_time S.E s) (x[m][v].st).cache
  obtain ⟨o, ho'⟩ := facts.gr.frameStableRoot_nonempty c S.E S.hc
    (M.toHealing (M.ns_setClock S.E (x[m][v].st).st (M.confirmation_time S.E s)).core)
    ((M.round_of S.hc) (M.ns_setClock S.E (x[m][v].st).st (M.confirmation_time S.E s)).core.s)
  have ho := (facts.nd.gradeContract_stableRoot _ _ _ _ _ o).2 ho'
  obtain ⟨G, -, hGP, hstab, cand, hconf, hcand⟩ :=
    Restated.records_after_confirmation_tick_values_upTo (hcatchB := hcatchB) facts S Sched x tE hexec hmono htd tGAT gap hgst hlen
      hsync hthird hphase hrsW hmult hcv hcs hcom
      hrec hprev hclear hB' hnW hAW hJswitch hr₀ hTW₀ hJ₀ hs0 hm hvaw hvh hvR hrun hb₀ c hc o ho
  have hgood : ∀ B : Block V, Restated.AncestorOfHonestHeadsFromTo M S Sched x B (s + 3) sEnd → Q B :=
    fun B hB => hQ B (Restated.ancestorOfHonestHeadsFrom_mono_upTo facts S Sched x hss₀ hB)
  have hnewS : Q (x[m + 1][v].st).st.core.latest_stable := by
    rw [hstab]
    rcases facts.hd.advance_confirmed_values (x[m][v].st).st.core.latest_stable G with ⟨-, he⟩ | he
    · rw [he]; exact hS
    · rw [he]; exact hgood G hGP
  have hQcand : Q cand := by
    rcases hcand with h | ⟨Y, hY, h⟩
    · rw [h]; exact hC
    · rw [h]
      rcases facts.hd.advance_confirmed_values (x[m][v].st).st.core.latest_confirmed Y with ⟨-, he⟩ | he
      · rw [he]; exact hC
      · rw [he]; exact hgood Y hY
  refine ⟨hnewS, ?_⟩
  rw [hconf]
  rcases facts.hd.floor_on_stable_values (x[m + 1][v].st).st.core.latest_stable cand
      (x[m][v].st).st.core.latest_confirmed with ⟨-, he⟩ | ⟨-, he⟩ | he
  · rw [he]; exact hQcand
  · rw [he]; exact hC
  · rw [he]; exact hnewS

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- On the premises of `records_after_confirmation_tick_values_upTo`, for a set `X` of blocks and a
    slot `s₀ ≥ s + 3`, call a block new when no member of `X` is a descendant of it or equal to it.
    If every stable root `v` can use at the tick is new, and each of `v`'s two records after `m`
    steps is an ancestor of every honest head from `s₀` to `sEnd` whenever it is new, then `v`'s
    `latest_stable` and `latest_confirmed` after `m + 1` steps are ancestors of every honest head
    from `s₀` to `sEnd`. -/
theorem records_after_confirmation_tick_of_new_root_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) {b₀ : Int} (hsync : Restated.SynchronyFromWakeBefore M S x b₀) (hcatchB : Restated.CatchUpOnWakeBefore M S x b₀) (hthird : ∀ t : Int, t ≤ tE →
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
      Block.Preceq (x[n₁][v].st).st.core.J T_W.erase) {sEnd : Slot}
    {r₀ : Round} {n₀ : Nat} {T₀ : NamedBlock V}
    (hr₀ : Restated.switchRound M S tE ≤ r₀) (hTW₀ : Block.Preceq T_W.erase T₀.erase)
    (hJ₀ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x r₀ n₀ n_W T₀)
    {s : Slot} (hs0 : (M.opening_slot S.hc r₀) + 2 ≤ s)
    {m : Nat} (hm : Restated.tickStepAt M x m (M.confirmation_time S.E s)) {v : V}
    (hvaw : v ∈ Sched.awakeThroughout (slotStart S.E.Δ s - S.E.Δ)
      (M.confirmation_time S.E s))
    (hvh : HonestThroughTime Sched (M.confirmation_time S.E s) v)
    (hvR : v ∈ Restated.HonRound M S Sched ((M.round_of S.hc (s + 1))))
    -- `v`'s tick at step `m` passes the grade-2 awake test of slot `s + 1`'s round.
    (hrun : M.awake_for_grade2 (Setup.alwaysAwake S) v
      (Record.wakeStage M Sched (M.confirmation_time S.E s) x[m] v) (M.round_of S.hc (s + 1)))
    {s₀ : Slot} (hss₀ : s + 3 ≤ s₀) (X : Finset (Block V))
    (hnew : ∀ c : M.Cache, M.onPhaseTick S.E S.hc (M.toHealing (x[m][v].st).st.core)
        (M.confirmation_time S.E s) (x[m][v].st).cache ⇢ c →
      ∀ G : Block V, (M.gradeContract c).stableRoot S.E S.hc
          (M.toHealing (M.ns_setClock S.E (x[m][v].st).st
            (M.confirmation_time S.E s)).core)
          ((M.round_of S.hc) (M.ns_setClock S.E (x[m][v].st).st
            (M.confirmation_time S.E s)).core.s) ⇢ some G →
      ∀ Y ∈ X, ¬ Block.Preceq G Y)
    (hS : (∀ Y ∈ X, ¬ Block.Preceq (x[m][v].st).st.core.latest_stable Y) →
      Restated.AncestorOfHonestHeadsFromTo M S Sched x (x[m][v].st).st.core.latest_stable s₀ sEnd)
    (hC : (∀ Y ∈ X, ¬ Block.Preceq (x[m][v].st).st.core.latest_confirmed Y) →
      Restated.AncestorOfHonestHeadsFromTo M S Sched x (x[m][v].st).st.core.latest_confirmed s₀ sEnd)
    (hb₀ : max tE ((Restated.Vocabulary.Execution.Setup.a M S ((M.round_of S.hc (sEnd - 2)) + 1))) ≤ b₀) :
    Restated.AncestorOfHonestHeadsFromTo M S Sched x (x[m + 1][v].st).st.core.latest_stable s₀ sEnd ∧
      Restated.AncestorOfHonestHeadsFromTo M S Sched x (x[m + 1][v].st).st.core.latest_confirmed s₀ sEnd := by
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc (M.toHealing (x[m][v].st).st.core)
    (M.confirmation_time S.E s) (x[m][v].st).cache
  obtain ⟨o, ho'⟩ := facts.gr.frameStableRoot_nonempty c S.E S.hc
    (M.toHealing (M.ns_setClock S.E (x[m][v].st).st (M.confirmation_time S.E s)).core)
    ((M.round_of S.hc) (M.ns_setClock S.E (x[m][v].st).st (M.confirmation_time S.E s)).core.s)
  have ho := (facts.nd.gradeContract_stableRoot _ _ _ _ _ o).2 ho'
  obtain ⟨G, rfl, hGP, hstab, cand, hconf, hcand⟩ :=
    Restated.records_after_confirmation_tick_values_upTo (hcatchB := hcatchB) facts S Sched x tE hexec hmono htd tGAT gap hgst hlen
      hsync hthird hphase hrsW hmult hcv hcs hcom
      hrec hprev hclear hB' hnW hAW hJswitch hr₀ hTW₀ hJ₀ hs0 hm hvaw hvh hvR hrun hb₀ c hc o ho
  -- a descendant of a new block is new
  have hup : ∀ A B : Block V, Block.Preceq A B → (∀ Y ∈ X, ¬ Block.Preceq A Y) →
      ∀ Y ∈ X, ¬ Block.Preceq B Y :=
    fun A B hAB hA Y hY hBY => hA Y hY (preceq_trans_Preceq hAB hBY)
  have hGnew := hnew c hc G ho
  have hGgood := Restated.ancestorOfHonestHeadsFrom_mono_upTo facts S Sched x hss₀ hGP
  -- the new stable record: new and `Good`
  have hnewS : (∀ Y ∈ X, ¬ Block.Preceq (x[m + 1][v].st).st.core.latest_stable Y) ∧
      Restated.AncestorOfHonestHeadsFromTo M S Sched x (x[m + 1][v].st).st.core.latest_stable s₀ sEnd := by
    rw [hstab]
    rcases facts.hd.advance_confirmed_values (x[m][v].st).st.core.latest_stable G with ⟨hGo, he⟩ | he
    · rw [he]
      have hon := hup G _ hGo hGnew
      exact ⟨hon, hS hon⟩
    · rw [he]; exact ⟨hGnew, hGgood⟩
  refine ⟨hnewS.2, ?_⟩
  -- the candidate, when new, is `Good`
  have hcandP : (∀ Y ∈ X, ¬ Block.Preceq cand Y) →
      Restated.AncestorOfHonestHeadsFromTo M S Sched x cand s₀ sEnd := by
    intro hcn
    rcases hcand with h | ⟨Y', hY', h⟩
    · rw [h] at hcn ⊢; exact hC hcn
    · rw [h] at hcn ⊢
      rcases facts.hd.advance_confirmed_values (x[m][v].st).st.core.latest_confirmed Y' with ⟨-, he⟩ | he
      · rw [he] at hcn ⊢; exact hC hcn
      · rw [he]; exact Restated.ancestorOfHonestHeadsFrom_mono_upTo facts S Sched x hss₀ hY'
  rw [hconf]
  rcases facts.hd.floor_on_stable_values (x[m + 1][v].st).st.core.latest_stable cand
      (x[m][v].st).st.core.latest_confirmed with ⟨hsc, he⟩ | ⟨hso, he⟩ | he
  · rw [he]; exact hcandP (hup _ _ hsc hnewS.1)
  · rw [he]; exact hC (hup _ _ hso hnewS.1)
  · rw [he]; exact hnewS.2

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- With synchrony up to `b₀ ≥ max tE (S.a (S.hc.round_of (sEnd - 2) + 1))`, on the premises of
    `afterPhaseJointRound_of_premises`, with the joint invariant at a round `r₀` at or after the
    switch round, if the configuration after `k₀ ≤ n` steps is after the confirmation time of slot
    `o_{r₀} + 1`, `n` is the tick step at slot `s_f`'s confirmation time, `v` is awake, honest and
    an honest active attester around every confirmation time after step `k₀` and at or before
    `s_f`'s, `v` passes the grade-2 awake test at each of those ticks, and no stable root `v` can
    use at the tick at `n` is an ancestor of, or equal to, a block of `v`'s tree after `k₀` steps,
    then `v`'s `latest_stable` and `latest_confirmed` after `n + 1` steps are ancestors of every
    honest head from slot `s_f + 3` to `sEnd`. -/
theorem records_good_of_new_root_window_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) {b₀ : Int} (hsync : Restated.SynchronyFromWakeBefore M S x b₀) (hcatchB : Restated.CatchUpOnWakeBefore M S x b₀) (hthird : ∀ t : Int, t ≤ tE →
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
      Block.Preceq (x[n₁][v].st).st.core.J T_W.erase) {sEnd : Slot}
    {r₀ : Round} {n₀ : Nat} {T₀ : NamedBlock V}
    (hr₀ : Restated.switchRound M S tE ≤ r₀) (hTW₀ : Block.Preceq T_W.erase T₀.erase)
    (hJ₀ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x r₀ n₀ n_W T₀)
    {v : V} {k₀ n : Nat} {s_f : Slot} (hk₀n : k₀ ≤ n)
    (hk₀ : M.confirmation_time S.E ((M.opening_slot S.hc r₀) + 1) ≤ (x[k₀].time : Int))
    (hn : Restated.tickStepAt M x n (M.confirmation_time S.E s_f))
    (hreader : ∀ s : Slot, (x[k₀].time : Int) < M.confirmation_time S.E s →
      M.confirmation_time S.E s ≤ M.confirmation_time S.E s_f →
      v ∈ Sched.awakeThroughout (slotStart S.E.Δ s - S.E.Δ) (M.confirmation_time S.E s) ∧
        HonestThroughTime Sched (M.confirmation_time S.E s) v ∧
        v ∈ Restated.HonRound M S Sched ((M.round_of S.hc (s + 1))))
    -- At every confirmation tick of the window, `v`'s node state passes the grade-2 awake test of
    -- the round of the next slot.
    (hrun : ∀ s : Slot, (x[k₀].time : Int) < M.confirmation_time S.E s →
      M.confirmation_time S.E s ≤ M.confirmation_time S.E s_f →
      ∀ m : Nat, Restated.tickStepAt M x m (M.confirmation_time S.E s) →
      M.awake_for_grade2 (Setup.alwaysAwake S) v
        (Record.wakeStage M Sched (M.confirmation_time S.E s) x[m] v) (M.round_of S.hc (s + 1)))
    (hnew : ∀ c : M.Cache, M.onPhaseTick S.E S.hc (M.toHealing (x[n][v].st).st.core)
        (M.confirmation_time S.E s_f) (x[n][v].st).cache ⇢ c →
      ∀ G : Block V, (M.gradeContract c).stableRoot S.E S.hc
          (M.toHealing (M.ns_setClock S.E (x[n][v].st).st
            (M.confirmation_time S.E s_f)).core)
          ((M.round_of S.hc) (M.ns_setClock S.E (x[n][v].st).st
            (M.confirmation_time S.E s_f)).core.s) ⇢ some G →
      ∀ Y ∈ (x[k₀][v].st).st.core.T, ¬ Block.Preceq G Y)
    (hb₀ : max tE ((Restated.Vocabulary.Execution.Setup.a M S ((M.round_of S.hc (sEnd - 2)) + 1))) ≤ b₀) :
    Restated.AncestorOfHonestHeadsFromTo M S Sched x (x[n + 1][v].st).st.core.latest_stable (s_f + 3) sEnd ∧
      Restated.AncestorOfHonestHeadsFromTo M S Sched x (x[n + 1][v].st).st.core.latest_confirmed (s_f + 3)
        sEnd := by
  have hd := S.E.Δ_pos
  set X : Finset (Block V) := (x[k₀][v].st).st.core.T with hX
  set Q : Block V → Prop := fun B =>
    (∀ Y ∈ X, ¬ Block.Preceq B Y) → Restated.AncestorOfHonestHeadsFromTo M S Sched x B (s_f + 3) sEnd
    with hQdef
  obtain ⟨hn1, hn0⟩ := Restated.tickStepAt_time facts x hn
  -- a confirmation tick at a step in `[k₀, n)` lies in the window
  have hwin : ∀ m : Nat, k₀ ≤ m → m < n → ∀ s : Slot,
      Restated.tickStepAt M x m (M.confirmation_time S.E s) →
      (M.opening_slot S.hc r₀) + 2 ≤ s ∧ s + 3 ≤ s_f + 3 ∧
        (x[k₀].time : Int) < M.confirmation_time S.E s ∧
        M.confirmation_time S.E s ≤ M.confirmation_time S.E s_f := by
    intro m hkm hmn s hm
    obtain ⟨hm1, hm0⟩ := Restated.tickStepAt_time facts x hm
    have h1 := Restated.time_mono_int facts S Sched x hkm
    have h2 := Restated.time_mono_int facts S Sched x (Nat.succ_le_of_lt hmn)
    have hlo : M.confirmation_time S.E ((M.opening_slot S.hc r₀) + 1)
        < M.confirmation_time S.E s := by linarith
    have hhi : M.confirmation_time S.E s < M.confirmation_time S.E s_f := by
      linarith
    exact ⟨Restated.slot_lt_of_confirmation_time_lt facts S hlo,
      Nat.add_le_add_right (Nat.le_of_lt (Restated.slot_lt_of_confirmation_time_lt facts S hhi)) 3,
      by linarith, le_of_lt hhi⟩
  -- the invariant along the window
  have key : ∀ m : Nat, k₀ ≤ m → m ≤ n →
      Q (x[m][v].st).st.core.latest_stable ∧ Q (x[m][v].st).st.core.latest_confirmed := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base =>
      intro _
      obtain ⟨hmS, hmC⟩ := Restated.records_mem_tree_sts facts S Sched x v k₀
      exact ⟨fun h => absurd (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _)) (h _ hmS),
        fun h => absurd (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _)) (h _ hmC)⟩
    | succ m hkm ih =>
      intro hmn
      obtain ⟨ihS, ihC⟩ := ih (Nat.le_of_succ_le hmn)
      rcases Restated.records_succ_cases facts S Sched x v m with ⟨h1, h2⟩ | ⟨s, hm, -⟩
      · rw [h1, h2]; exact ⟨ihS, ihC⟩
      · obtain ⟨hs0, hss, hlo, hhi⟩ := hwin m hkm (Nat.lt_of_succ_le hmn) s hm
        obtain ⟨hvaw, hvh, hvR⟩ := hreader s hlo hhi
        exact Restated.records_after_confirmation_tick_keep_upTo (hcatchB := hcatchB) facts S Sched x tE hexec hmono htd tGAT gap
          hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hrec hprev hclear hB' hnW
          hAW hJswitch hr₀ hTW₀ hJ₀ hs0 hm hvaw hvh hvR (hrun s hlo hhi m hm) hss Q
          (fun B hB _ => hB) ihS ihC hb₀
  obtain ⟨hQS, hQC⟩ := key n hk₀n le_rfl
  -- the last tick
  have hs0f : (M.opening_slot S.hc r₀) + 2 ≤ s_f := by
    have h1 := Restated.time_mono_int facts S Sched x hk₀n
    have hlo : M.confirmation_time S.E ((M.opening_slot S.hc r₀) + 1)
        < M.confirmation_time S.E s_f := by linarith
    exact Restated.slot_lt_of_confirmation_time_lt facts S hlo
  have hlof : (x[k₀].time : Int) < M.confirmation_time S.E s_f := by
    have h1 := Restated.time_mono_int facts S Sched x hk₀n
    linarith
  obtain ⟨hvaw, hvh, hvR⟩ := hreader s_f hlof le_rfl
  exact Restated.records_after_confirmation_tick_of_new_root_upTo (hcatchB := hcatchB) facts S Sched x tE hexec hmono htd tGAT gap
    hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hrec hprev hclear hB' hnW hAW
    hJswitch hr₀ hTW₀ hJ₀ hs0f hn hvaw hvh hvR (hrun s_f hlof le_rfl n hn) le_rfl X hnew hQS hQC hb₀

end

end DecoupledConsensusModel.Sts.Restated
