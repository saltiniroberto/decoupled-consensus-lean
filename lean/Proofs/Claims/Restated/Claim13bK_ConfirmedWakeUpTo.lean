import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bK_ConfirmedRecord
import Proofs.Claims.Restated.Claim13bK_ConfirmedRecordReadersUpTo
import Proofs.Claims.Restated.Claim13bK_ConfirmedRecordUpTo
import Proofs.Claims.Restated.Claim13bK_ConfirmedSettle
import Proofs.Claims.Restated.Claim13bK_ConfirmedSettleUpTo
import Proofs.Claims.Restated.Claim13bK_ConfirmedWake
import Proofs.Claims.Restated.Claim13bK_HeadsPersistUpTo
import Proofs.Claims.Restated.Claim13bK_LiveConfirmedSlotsUpTo
import Proofs.Claims.Restated.Claim13bK_PrevHeadsStep
import Proofs.Claims.Restated.Claim13bStepConeIter
import Proofs.Claims.Restated.Claim13bStepKitConfirm
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bW_Schedule
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActive
import Model.Conditions.Claim13bInvariantActiveJoint
import Model.Conditions.Claim13bInvariantActiveSinceW
import Model.Conditions.Claim13bK_ConfirmedRecordUpTo
import Model.Conditions.Claim13bK_ConfirmedWake
import Model.Conditions.Claim13bK_ConfirmedWakeUpTo
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13bStepCone
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
import Proofs.Claims.Restated.Claim13bW_ReceiptBefore

/-!
# Confirmed records of a validator that sleeps and wakes, up to a slot

That the stable and confirmed records of an honest validator stay ancestors of every honest head
over the slots up to `sEnd` after the tick at `S.a (rW + 1)`, with synchrony assumed only up to a
bound `b₀`, and the reduction of the action-tick settle fact to the settle-tick one. Stated over a
model `M : Record.Model V`.
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
local macro "pCW% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13bK_ConfirmedWake)
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
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If `m` is the tick step at slot `s`'s confirmation time, `v` is awake there and not held, its
    tick has an outcome and passes the grade-2 awake test of the round of `s + 1`, every stable root
    `G` that `v` can use at the tick is an ancestor of every honest head from slot `s + 3` to
    `sEnd`, `v`'s `live_confirmed` after the tick is an ancestor of every honest head from slot
    `s + 1` to `sEnd` whenever some outcome of its slot-`s` eligibility test accepts a block, and
    `v`'s `latest_stable` and `latest_confirmed` after `m` steps are ancestors of every honest head
    from slot `s + 3` to `sEnd`, then so are they after `m + 1` steps. -/
theorem records_after_confirmation_tick_of_inputs_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {s sEnd : Slot}
    {m : Nat} (hm : Restated.tickStepAt M x m (M.confirmation_time S.E s)) {v : V}
    (haw : v ∈ Sched.awake (M.confirmation_time S.E s) \
      Sched.adv (M.confirmation_time S.E s))
    (hroot : ∀ c : M.Cache, M.onPhaseTick S.E S.hc (M.toHealing (x[m][v].st).st.core)
        (M.confirmation_time S.E s) (x[m][v].st).cache ⇢ c →
      ∀ G : Block V,
      (M.gradeContract c).stableRoot S.E S.hc
          (M.toHealing (M.ns_setClock S.E (x[m][v].st).st
            (M.confirmation_time S.E s)).core)
          ((M.round_of S.hc) (M.ns_setClock S.E (x[m][v].st).st
            (M.confirmation_time S.E s)).core.s) ⇢ some G →
      Restated.AncestorOfHonestHeadsFromTo M S Sched x G (s + 3) sEnd)
    (hlive : ∀ (H : Block V) (el : Block V → Bool),
      Restated.Vocabulary.Protocol.confEligible M S.E (x[m][v].st).st.core s ⇢ el → el H = true →
      Restated.AncestorOfHonestHeadsFromTo M S Sched x (x[m + 1][v].st).st.core.live_confirmed (s + 1)
        sEnd)
    (hL : Restated.AncestorOfHonestHeadsFromTo M S Sched x (x[m][v].st).st.core.latest_stable (s + 3) sEnd)
    (hC : Restated.AncestorOfHonestHeadsFromTo M S Sched x (x[m][v].st).st.core.latest_confirmed (s + 3)
      sEnd)
    (hneTick : ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched (M.confirmation_time S.E s) x[m] v) (M.confirmation_time S.E s) ⇢ out)
    -- The node state `v`'s tick reads passes the grade-2 awake test of the round of `s + 1`.
    (hrun : M.awake_for_grade2 (Setup.alwaysAwake S) v
      (Record.wakeStage M Sched (M.confirmation_time S.E s) x[m] v) (M.round_of S.hc (s + 1))) :
    Restated.AncestorOfHonestHeadsFromTo M S Sched x (x[m + 1][v].st).st.core.latest_stable (s + 3) sEnd ∧
      Restated.AncestorOfHonestHeadsFromTo M S Sched x (x[m + 1][v].st).st.core.latest_confirmed (s + 3)
        sEnd := by
  -- one outcome of the cache update and one of the stable root under its grade contract
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc (M.toHealing (x[m][v].st).st.core)
    (M.confirmation_time S.E s) (x[m][v].st).cache
  obtain ⟨o, ho'⟩ := facts.gr.frameStableRoot_nonempty c S.E S.hc
    (M.toHealing (M.ns_setClock S.E (x[m][v].st).st (M.confirmation_time S.E s)).core)
    ((M.round_of S.hc) (M.ns_setClock S.E (x[m][v].st).st (M.confirmation_time S.E s)).core.s)
  have ho := (facts.nd.gradeContract_stableRoot _ _ _ _ _ o).2 ho'
  obtain ⟨G, rfl, hstab, hconf⟩ := Restated.records_after_confirmation_tick facts S Sched x
    hm haw hneTick hrun c hc o ho
  have hGP := hroot c hc G ho
  have hnewstab : Restated.AncestorOfHonestHeadsFromTo M S Sched x
      (M.advance_confirmed (x[m][v].st).st.core.latest_stable G) (s + 3) sEnd :=
    Restated.ancestorOfHonestHeadsFrom_advance_confirmed_upTo facts S Sched x hGP (fun _ => hL)
  refine ⟨by rw [hstab]; exact hnewstab, ?_⟩
  -- the confirmation record: one outcome of the confirmation update, and the candidate it writes
  obtain ⟨D, hD⟩ := facts.dt.update_confirmation_with_nonempty (M.gradeContract c) S.E S.hc
    (M.ns_setClock S.E (x[m][v].st).st (M.confirmation_time S.E s)).core s
  obtain ⟨cand, hfl, hcases⟩ := (pCW% update_confirmation_with_latest_confirmed_eligible_cw) facts
    (M.gradeContract c) S.E S.hc _ s D hD
  have hDstab : D.latest_stable = M.advance_confirmed (x[m][v].st).st.core.latest_stable G := by
    rw [facts.hd.update_confirmation_with_latest_stable_of_root _ _ _ _ _ (some G) ho rfl D hD,
      facts.hd.setClock_core_latest_stable]
  rw [facts.hd.setClock_core_latest_confirmed] at hfl hcases
  rw [hconf D hD, hfl, hDstab]
  refine Restated.ancestorOfHonestHeadsFrom_floor_on_stable_upTo facts S Sched x hnewstab (fun _ => ?_)
    (fun _ => hC)
  rcases hcases with hcand | ⟨el, hel, helD, hcand⟩ | ⟨G', hsel, hcand⟩
  · rw [hcand]; exact hC
  · -- the eligible walk result is the `live_confirmed` written at the tick
    rw [(pCW% confEligible_setClock_cw) facts S.E (x[m][v].st).st (M.confirmation_time S.E s)] at hel
    have hJ1 := hlive D.live_confirmed el hel helD
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
    exact Restated.ancestorOfHonestHeadsFrom_advance_confirmed_upTo facts S Sched x hGP (fun _ => hC)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- `RecordsSettledAtSettleTickTo S Sched x tE sEnd` and `sEnd' ≤ sEnd` give
    `RecordsSettledAtSettleTickTo S Sched x tE sEnd'`. -/
theorem RecordsSettledAtSettleTickTo.mono_end (facts : Record.Facts M) {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (Record.protocolOf M S) Sched} {tE : Int} {sEnd sEnd' : Slot}
    (hle : sEnd' ≤ sEnd) (h : Restated.RecordsSettledAtSettleTickTo M S Sched x tE sEnd) :
    Restated.RecordsSettledAtSettleTickTo M S Sched x tE sEnd' :=
  fun r n v h1 h2 h3 h4 => (h r n v h1 h2 h3 h4).mono_end facts hle

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- With synchrony up to `b₀ ≥ max tE (S.a (S.hc.round_of (sEnd - 2) + 1))`, on the premises of
    `afterPhaseJointRound_of_premises`, with the joint invariant at a round `r₀` at or after the
    switch round, if slot `s` is at or after `o_{r₀} + 2`, `m` is the tick step at slot `s`'s
    confirmation time, `v` is awake at that time, asleep at the grade-2 domain time of the round
    `r'` of `s + 1`, and honest through the confirmation time, `c` is an outcome of `v`'s cache
    update at the tick and the stable root of `c`'s grade contract can return `some G`, then `G` is
    an ancestor of every honest head from slot `s + 3` to `sEnd`. -/
theorem stableRoot_ancestorOfHonestHeadsFrom_ofAsleepDomain_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) {b₀ : Int} (hsync : Restated.SynchronyFromWakeBefore M S x b₀) (hcatchB : Restated.CatchUpOnWakeBefore M S x b₀) (hthird : ∀ t : Int, t ≤ tE →
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
    (haw : v ∈ Sched.awake (M.confirmation_time S.E s))
    (hasl : v ∉ Sched.awake (M.domain S.E S.hc ((M.round_of S.hc (s + 1))) .g2))
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
  have hsE_c : Restated.CatchUpOnWakeBefore M S x tE := hcatchB.monoU facts (le_trans (le_max_left _ _) hb₀)
  have hR0 : (M.round_of S.hc s) ≤ (M.round_of S.hc (sEnd - 2)) :=
    Restated.round_of_le_round_of_sub_two facts S (le_trans (Nat.le_succ _) hE)
  have hslot : (M.ns_setClock S.E (x[m][v].st).st
      (M.confirmation_time S.E s)).core.s = s + 1 := by
    rw [facts.hd.Sts_setClock_core_s]; exact facts.sch.Optimistic_slotOf_confirmation_time S.E s
  have hG := (facts.nd.gradeContract_stableRoot _ _ _ _ _ _).1 hG
  rw [hslot] at hG
  rcases facts.gr.frameStableRoot_cases _ _ _ _ _ _ hG rfl with hroot | ⟨root, hg2, -⟩
  · -- the first case of `frameStableRoot_cases`
    obtain ⟨hm1, hm0⟩ := Restated.tickStepAt_time facts x hm
    have hvm : Restated.HonestThrough M Sched x m v := fun t ht => hvh t (by linarith)
    have hrs0 := facts.gr.opening_slot_round_of_le_slot S.hc s
    have hrs1 := facts.gr.lt_opening_slot_round_of_succ S.hc s
    have hrr : r₀ ≤ (M.round_of S.hc s) := by
      by_contra hcon
      exact nat_lt_absurd_c3 hs0 hrs1
        (facts.gr.opening_slot_mono S (Nat.succ_le_of_lt (Nat.lt_of_not_le hcon)))
    obtain ⟨n, T, hJ, -, hTW⟩ := Restated.anchor_at_later_round_upTo (hcatchB := hcatchB) facts S Sched x tE hexec hmono htd
      tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hrec hprev hclear hB'
      hnW hAW hJswitch hr₀ hTW₀ hJ₀ hrr (le_trans (Restated.anchorBound_le_headsBound facts S tE hR0) hb₀)
    have hr : Restated.switchRound M S tE ≤ (M.round_of S.hc s) := le_trans hr₀ hrr
    have hroot' : Block.Preceq (Restated.Vocabulary.Protocol.confRoot M (Restated.confStoreAt M S (x[m][v].st) s)) T.erase :=
      Restated.confRoot_preceq_anchor_atSlot_upTo facts S Sched x tE hexec hmono htd tGAT gap hgst hlen hsE
        hthird hphase hrsW hmult hcv hcom hrec hprev hclear hB' hnW hAW hr hTW hJ hrs0
        (Nat.le_of_lt hrs1) hm hvm
    have hGT : Block.Preceq G T.erase := by rw [hroot]; exact hroot'
    have hanc := Restated.anchor_ancestorOfHonestHeadsFrom_upTo (hcatchB := (hcatchB.monoU facts hb₀)) facts S Sched x tE hexec hmono htd tGAT gap
      hgst hlen (hsync.monoU facts hb₀) hthird hphase hrsW hmult hcv hcs hcom hrec hprev hclear
      hB' hnW hAW hJswitch hr hTW hJ
    exact Restated.ancestorOfHonestHeadsFrom_mono_upTo facts S Sched x (nat_le_add3_c3 hrs0)
      (Restated.ancestorOfHonestHeadsFrom_of_preceq_upTo facts S Sched x hGT hanc)
  · -- no grade-2 entry: it would have been written while `v` was awake at the domain instant
    exfalso
    obtain ⟨root₀, hc0, -⟩ := facts.gr.readFrame_g2_provenance _ _ _ hg2
    have hprov := Restated.framePhaseAwakeProvenance_onPhaseTick facts S Sched
      (M.toHealing (x[m][v].st).st.core) (x[m][v].st).cache haw
      (Restated.framePhaseAwakeProvenance_sts facts S Sched x v m) c hc
    exact hasl (hprov _ .g2 root₀ hc0)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- With synchrony up to `b₀ ≥ max tE (S.a (S.hc.round_of (sEnd - 2) + 1))`, on the premises of
    `afterPhaseJointRound_of_premises`, with the joint invariant at the switch round, if
    `RecordsSettledAtSettleTickTo` holds at `sEnd` and `n_b` is the tick step at `S.a (rW + 1)`,
    then for every step `k ≥ n_b + 1` and every `v` honest through the configuration after `k`
    steps, `v`'s `latest_stable` and `latest_confirmed` after `k` steps are ancestors of every
    honest head from slot `slot(x[k].time) + 2` to `sEnd`. -/
theorem records_ancestorOfHonestHeads_after_settleTick_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) {b₀ : Int} (hsync : Restated.SynchronyFromWakeBefore M S x b₀) (hcatchB : Restated.CatchUpOnWakeBefore M S x b₀) (hthird : ∀ t : Int, t ≤ tE →
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
    {n₀ : Nat} {T₀ : NamedBlock V} (hTW₀ : Block.Preceq T_W.erase T₀.erase)
    (hJ₀ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x (Restated.switchRound M S tE) n₀ n_W T₀)
    (hsettle : Restated.RecordsSettledAtSettleTickTo M S Sched x tE sEnd)
    {n_b : Nat} (hn_b : Restated.tickStepAt M x n_b ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE + 1)))) (v : V)
    (hb₀ : max tE ((Restated.Vocabulary.Execution.Setup.a M S ((M.round_of S.hc (sEnd - 2)) + 1))) ≤ b₀) :
    ∀ k : Nat, n_b + 1 ≤ k → Restated.HonestThrough M Sched x k v →
      Restated.RecordsAncestorOfHonestHeadsTo M S Sched x v k sEnd := by
  have hd := S.E.Δ_pos
  obtain ⟨hnb1, hnb0⟩ := Restated.tickStepAt_time facts x hn_b
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    intro hv
    exact hsettle _ n_b v le_rfl hn_b (hv _ (by rw [hnb1])) rfl
  | succ k hkn ih =>
    intro hv
    have hvk : Restated.HonestThrough M Sched x k v := fun t ht =>
      hv t (le_trans ht (Restated.time_mono_int facts S Sched x (Nat.le_succ k)))
    have ihk := ih hvk
    rcases Restated.records_succ_cases facts S Sched x v k with ⟨h1, h2⟩ | ⟨s, hm, haw⟩
    · have hsl : S.E.slotOf (x[k].time : Int) + 2 ≤ S.E.slotOf (x[k + 1].time : Int) + 2 :=
        Nat.add_le_add_right (slotOf_mono_sts S (Restated.time_mono_int facts S Sched x (Nat.le_succ k))) 2
      unfold Restated.RecordsAncestorOfHonestHeadsTo
      rw [h1, h2]
      exact ⟨Restated.ancestorOfHonestHeadsFrom_mono_upTo facts S Sched x hsl ihk.1,
        Restated.ancestorOfHonestHeadsFrom_mono_upTo facts S Sched x hsl ihk.2⟩
    · obtain ⟨hn1, hn0⟩ := Restated.tickStepAt_time facts x hm
      have hslot : S.E.slotOf (x[k + 1].time : Int) = s + 1 := by
        rw [hn1]; exact facts.sch.Optimistic_slotOf_confirmation_time S.E s
      have hbk : (x[n_b + 1].time : Int) ≤ (x[k].time : Int) := Restated.time_mono_int facts S Sched x hkn
      have htc : (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE + 1)) < M.confirmation_time S.E s := by
        rw [hnb1] at hbk; linarith
      have hvh' : HonestThroughTime Sched (M.confirmation_time S.E s) v :=
        fun t ht => hv t (by rw [hn1]; exact ht)
      obtain ⟨hs1, hrr, -, ha1, -⟩ :=
        Restated.confirmation_tick_arith facts S (Nat.succ_pos _) htc
      have hs0 : (M.opening_slot S.hc (Restated.switchRound M S tE)) + 2 ≤ s := by
        have h1 := facts.gr.opening_slot_succ S.hc (Restated.switchRound M S tE)
        rw [h1] at hs1
        exact nat_add_two_le_c3 le_rfl hs1 S.hc.R_ge_three
      have hL : Restated.AncestorOfHonestHeadsFromTo M S Sched x (x[k][v].st).st.core.latest_stable (s + 3)
          sEnd :=
        Restated.ancestorOfHonestHeadsFrom_mono_upTo facts S Sched x (Nat.add_le_add_right
          (by rw [← facts.sch.Optimistic_slotOf_confirmation_time S.E s]
              exact slotOf_mono_sts S (by linarith)) 2) ihk.1
      have hC : Restated.AncestorOfHonestHeadsFromTo M S Sched x (x[k][v].st).st.core.latest_confirmed
          (s + 3) sEnd :=
        Restated.ancestorOfHonestHeadsFrom_mono_upTo facts S Sched x (Nat.add_le_add_right
          (by rw [← facts.sch.Optimistic_slotOf_confirmation_time S.E s]
              exact slotOf_mono_sts S (by linarith)) 2) ihk.2
      have hawtc : v ∈ Sched.awake (M.confirmation_time S.E s) := (Finset.mem_sdiff.1 haw).1
      set r' := (M.round_of S.hc (s + 1)) with hr'
      have hr'0 : 0 < r' := lt_of_lt_of_le (Nat.succ_pos _) hrr
      obtain ⟨r₁, hr₁⟩ : ∃ r₁ : Round, r' = r₁ + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hr'0).symm⟩
      have hpred : (Restated.Vocabulary.Execution.Setup.a M S r₁) ≤ slotStart S.E.Δ s - S.E.Δ := by
        have h := Restated.action_pred_round_of_succ_le facts S s hr'0
        rw [← hr', hr₁, Nat.add_sub_cancel] at h
        exact h
      have hres : Restated.AncestorOfHonestHeadsFromTo M S Sched x (x[k + 1][v].st).st.core.latest_stable
            (s + 3) sEnd ∧
          Restated.AncestorOfHonestHeadsFromTo M S Sched x (x[k + 1][v].st).st.core.latest_confirmed
            (s + 3) sEnd := by
        -- split on the grade-2 awake test of the round of `s + 1`; when it fails, the tick keeps
        -- both records
        have hdvd : M.confirmation_time S.E s % S.E.Δ = 0 := by
          rw [facts.sch.confirmation_time_eq_support_cutoff_succ]
          exact facts.sch.support_cutoff_emod_delta S (s + 1)
        by_cases hrun : M.awake_for_grade2 (Setup.alwaysAwake S) v
            (Record.wakeStage M Sched (M.confirmation_time S.E s) x[k] v) (M.round_of S.hc (s + 1))
        swap
        · obtain ⟨t', hlbl, ht'⟩ := id hm
          have hdvd' : (t' : Int) % S.E.Δ = 0 := by rw [ht']; exact hdvd
          have haw' : v ∈ Sched.awake (t' : Int) \ Sched.adv (t' : Int) := by rw [ht']; exact haw
          rcases Restated.st_succ_of_tick_awake facts S Sched x v hlbl haw' with
            ⟨out, hout, hst⟩ | ⟨-, hst⟩
          · rw [ht'] at hout
            obtain ⟨hCk, hLk⟩ :=
              facts.nd.tick_records_frame_of_not_awake_for_grade2 S v _ s out hout hrun
            rw [hst, hLk, hCk, Record.wakeStage_st facts]
            exact ⟨hL, hC⟩
          · rw [hst, Record.wakeStage_st facts]
            exact ⟨hL, hC⟩
        by_cases hsE : s + 3 ≤ sEnd
        swap
        · exact ⟨fun s' h1 h2 => absurd (le_trans h1 h2) hsE, fun s' h1 h2 => absurd (le_trans h1 h2) hsE⟩
        obtain ⟨t', hlbl, ht'⟩ := id hm
        have hrun' : M.awake_for_grade2 (Setup.alwaysAwake S) v
            (Record.wakeStage M Sched (t' : Int) x[k] v) r' := by rw [ht']; exact hrun
        have hwin := facts.ndWake.run_fact_g2_sound_at S Sched x k t' r' v hlbl
          (Restated.early_g2_sub_delta_nonneg facts S hr'0)
          (fun t'' h => hvh' t'' (by rw [← ht']; exact h)) (by rw [ht']; exact hawtc) hrun'
        rw [ht'] at hwin
        have he := facts.gr.early_g2_eq S r'
        have hl9 := Restated.action_sub_nine_delta_le_late facts S r' .g2
        have hd1 : (1 : Int) ≤ S.E.Δ := hd
        obtain ⟨-, -, -, -, hup'⟩ := Restated.confirmation_tick_arith facts S (Nat.succ_pos _) htc
        have hup : M.a S.hc S.E.Δ r' ≤ M.confirmation_time S.E s + 4 * S.E.Δ := hup'
        have hct6 := facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E s
        have hvaw : v ∈ Sched.awakeThroughout (slotStart S.E.Δ s - S.E.Δ)
            (M.confirmation_time S.E s) := by
          refine awakeThroughout_mono Sched hwin ?_ le_rfl
          rw [he]; linarith
        have hrW : Restated.switchRound M S tE ≤ r₁ := by
          have h := hrr; rw [hr₁] at h; exact Nat.le_of_succ_le_succ h
        -- round `r'` acts at or before `b₀`: its slot `s + 1` is at most `sEnd − 2`
        have hrb : M.early S.E S.hc r' .g2 ≤ b₀ := by
          have hss : s + 1 ≤ sEnd - 2 := Nat.le_sub_of_add_le hsE
          have hro : r' ≤ M.round_of S.hc (sEnd - 2) := facts.gr.round_of_mono_sts S.hc hss
          have hA := Restated.action_mono facts S (Nat.le_succ_of_le hro)
          exact le_trans (Restated.early_g2_le_action_rb facts S r')
            (le_trans hA (le_trans (le_max_right _ _) hb₀))
        have hrecv : Restated.ReceivesRoundAttestationsBefore M S Sched x (r' - 1) v
            (M.early S.E S.hc r' .g2) := by
          have hS := facts.gr.action_delta_le_early S S.hc.R_ge_three (Nat.lt_succ_self r₁)
          have hG := Restated.gst_le_action_of_switchRound_le facts S tGAT tE gap hgst hlen hrW
          rw [hr₁, Nat.add_sub_cancel]
          rw [hr₁] at hwin he hrb
          have e : M.early S.E S.hc (r₁ + 1) .g2 - S.E.Δ + S.E.Δ = M.early S.E S.hc (r₁ + 1) .g2 := by
            ring
          have h := Restated.receives_of_awakeFrom_before facts S Sched x hsync hcatchB
            (r := r₁) (t₀ := M.early S.E S.hc (r₁ + 1) .g2 - S.E.Δ)
            (by show M.a S.hc S.E.Δ r₁ ≤ _; linarith) (by linarith) (by rw [e]; exact hrb)
            (awakeThroughout_mono Sched hwin le_rfl (by rw [hr₁] at hup; linarith))
          rw [e] at h
          exact h
        exact Restated.records_after_confirmation_tick_ancestorOfHonestHeadsFrom_ofAwake_upTo_recv
          (hcatchB := hcatchB) facts S Sched x tE hexec hmono htd tGAT gap hgst hlen hsync hthird hphase
          hrsW hmult hcv hcs hcom hrec hprev hclear hB' hnW hAW hJswitch le_rfl hTW₀ hJ₀ hs0 hrr hm hvaw
          (M.early S.E S.hc r' .g2 - S.E.Δ) (by rw [he]; linarith) hwin hrecv hvh' hrun hL hC hb₀
      unfold Restated.RecordsAncestorOfHonestHeadsTo
      rw [hslot]
      exact hres

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- With synchrony up to `b₀ ≥ max tE (S.a (S.hc.round_of (sEnd - 2) + 1))`, on the premises of
    `afterPhaseJointRound_of_premises`, with the joint invariant at the switch round, the settle
    fact at the settle tick over the slots up to `sEnd` gives the settle fact at the action ticks
    over the same slots. -/
theorem recordsSettledAtActionTicks_of_settleTick_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) {b₀ : Int} (hsync : Restated.SynchronyFromWakeBefore M S x b₀) (hcatchB : Restated.CatchUpOnWakeBefore M S x b₀) (hthird : ∀ t : Int, t ≤ tE →
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
    {n₀ : Nat} {T₀ : NamedBlock V} (hTW₀ : Block.Preceq T_W.erase T₀.erase)
    (hJ₀ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x (Restated.switchRound M S tE) n₀ n_W T₀)
    (hsettle : Restated.RecordsSettledAtSettleTickTo M S Sched x tE sEnd)
    (hb₀ : max tE ((Restated.Vocabulary.Execution.Setup.a M S ((M.round_of S.hc (sEnd - 2)) + 1))) ≤ b₀) :
    Restated.RecordsSettledAtActionTicksTo M S Sched x tE sEnd := by
  intro r n v hr hn hv _
  obtain ⟨n_b, hn_b⟩ := Restated.tick_field_at_succ facts S Sched x htd (Restated.switchRound M S tE)
  obtain ⟨hnb1, hnb0⟩ := Restated.tickStepAt_time facts x hn_b
  obtain ⟨hn1, hn0⟩ := Restated.tickStepAt_time facts x hn
  have hmono' := Restated.action_mono facts S hr
  refine Restated.records_ancestorOfHonestHeads_after_settleTick_upTo (hcatchB := hcatchB) facts S Sched x tE hexec hmono htd tGAT
    gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hrec hprev hclear hB' hnW hAW
    hJswitch hTW₀ hJ₀ hsettle hn_b v hb₀ (n + 1) ?_ ?_
  · by_contra hcon
    have := Restated.time_mono_int facts S Sched x (Nat.le_of_lt_succ (Nat.lt_of_not_le hcon))
    linarith
  · intro t ht hadv
    rw [hn1] at ht
    exact (Finset.mem_sdiff.1 hv).2 (hmono t ((Restated.Vocabulary.Execution.Setup.a M S r)) ht hadv)

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
theorem records_ancestorOfHonestHeads_of_settle_honestThrough_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) {b₀ : Int} (hsync : Restated.SynchronyFromWakeBefore M S x b₀) (hcatchB : Restated.CatchUpOnWakeBefore M S x b₀) (hthird : ∀ t : Int, t ≤ tE →
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
    {n₀ : Nat} {T₀ : NamedBlock V} (hTW₀ : Block.Preceq T_W.erase T₀.erase)
    (hJ₀ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x (Restated.switchRound M S tE) n₀ n_W T₀)
    (hsettle : Restated.RecordsSettledAtSettleTickTo M S Sched x tE sEnd)
    {i : Nat} {v : V}
    (hvi : Restated.HonestThrough M Sched x i v)
    (hti : Restated.confirmedSettleTime M S tE ≤ (x[i].time : Int))
    (hva : v ∈ activeAtW S Sched (S.E.slotOf (x[i].time : Int)))
    (hb₀ : max tE ((Restated.Vocabulary.Execution.Setup.a M S ((M.round_of S.hc (sEnd - 2)) + 1))) ≤ b₀) :
    Restated.RecordsAncestorOfHonestHeadsTo M S Sched x v i sEnd ∧
      Restated.AncestorOfHonestHeadsFromTo M S Sched x (M.get_confirmed (x[i][v].st).st.core)
        (S.E.slotOf (x[i].time : Int) + 2) sEnd := by
  have hd := S.E.Δ_pos
  obtain ⟨n_b, hn_b⟩ := Restated.tick_field_at_succ facts S Sched x htd (Restated.switchRound M S tE)
  obtain ⟨hnb1, hnb0⟩ := Restated.tickStepAt_time facts x hn_b
  have hts : (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE + 1)) ≤ (x[i].time : Int) := hti
  have hki : n_b + 1 ≤ i := by
    by_contra hcon
    have := Restated.time_mono_int facts S Sched x (Nat.le_of_lt_succ (Nat.lt_of_not_le hcon))
    linarith
  have hrec' := Restated.records_ancestorOfHonestHeads_after_settleTick_upTo (hcatchB := hcatchB) facts S Sched x tE hexec
    hmono htd tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hrec hprev hclear hB' hnW
    hAW hJswitch hTW₀ hJ₀ hsettle hn_b v hb₀ i hki hvi
  exact ⟨hrec', (Restated.outputs_ancestorOfHonestHeads_of_records_upTo (hcatchB := hcatchB) facts S Sched x tE hexec hmono htd
    tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hrec hprev hclear hB'
    hnW hAW hJswitch le_rfl hTW₀ hJ₀
    (le_trans (Restated.action_mono facts S (Nat.le_succ (Restated.switchRound M S tE))) hts) hvi
    hrec' hb₀).2⟩

end

end DecoupledConsensusModel.Sts.Restated
