import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bInvariantActiveSince
import Proofs.Claims.Restated.Claim13bInvariantActiveSinceW
import Proofs.Claims.Restated.Claim13bInvariantActiveSinceWUpTo
import Proofs.Claims.Restated.Claim13bK_ConfirmedRecordReadersUpTo
import Proofs.Claims.Restated.Claim13bK_ConfirmedRecordUpTo
import Proofs.Claims.Restated.Claim13bK_ConfirmedSettleUpTo
import Proofs.Claims.Restated.Claim13bK_HeadsPersist
import Proofs.Claims.Restated.Claim13bK_InclusionAnchorTreeUpTo
import Proofs.Claims.Restated.Claim13bK_LiveConfirmedSlotsUpTo
import Proofs.Claims.Restated.Claim13bStepGrade
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bW_Schedule
import Proofs.Claims.Restated.Claim13beRoute3_76
import Proofs.Claims.Restated.Claim13beRoute3_82
import Proofs.Claims.Restated.Claim13beRoute3_83UpTo
import Proofs.Claims.Restated.Claim13beRoute3_85fUpTo
import Proofs.Claims.Restated.Claim13beRoute3_88UpTo
import Proofs.Claims.Restated.Claim13beRoute3_91UpTo
import Proofs.Claims.Restated.ClaimAsyncK_AfterFacts
import Proofs.Claims.Restated.ClaimAsyncK_HandoverCovers
import Proofs.Claims.Restated.ClaimAsyncK_HandoverRoots
import Proofs.Claims.Restated.ClaimConfirmedAfterHealingKit
import Proofs.Claims.Restated.ClaimConfirmedAfterHealingKitFullUpTo
import Proofs.Claims.Restated.ClaimConfirmedAfterHealingKitUpTo
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActiveJoint
import Model.Conditions.Claim13bInvariantActiveSince
import Model.Conditions.Claim13bInvariantActiveSinceW
import Model.Conditions.Claim13bK_ConfirmedRecordUpTo
import Model.Conditions.Claim13bK_ConfirmedWakeUpTo
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13bStepConeIter
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_72
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
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.ClaimAsyncK_HandoverRootsUpTo

/-!
# The fields `roots` and `entries` of the hand-over

Theorems over a model `M : Record.Model V` with facts `facts : Record.Facts M`: on the healing
premises with synchrony up to a bound, blocks of an honest stable output are ancestors of later
honest heads, the anchors of later rounds, and the fields `roots` and `entries` of
`Restated.StableHandover`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog

/-- The opening slot of round `r` is `r * R`. -/
private theorem opening_slot_closed_hr (facts : Record.Facts M) (hc : Protocol.HealConfig)
    (r : Round) : M.opening_slot hc r = r * hc.R := by
  have h := facts.gr.opening_slot_add_mk hc 0 r
  rw [Nat.zero_add, facts.gr.opening_slot_zero_mk, Nat.zero_add] at h
  exact h

/-- The action instant of round `r` is `4 * Δ * R * r + 6 * Δ`. -/
private theorem action_closed_hr (facts : Record.Facts M) (S : Setup V) (r : Round) :
    (Restated.Vocabulary.Execution.Setup.a M S r) =
      4 * S.E.Δ * (S.hc.R : Int) * (r : Int) + 6 * S.E.Δ := by
  show M.a S.hc S.E.Δ r = _
  rw [facts.sch.a_eq_confirmation_time S.hc S.E r,
    ← facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E _, slotStart_closed,
    opening_slot_closed_hr facts]
  push_cast
  ring

/-- If `o_ρ ≤ o_{r+1} + 1 ≤ o_{ρ+1}`, then `ρ = r + 1`. -/
private theorem eq_succ_of_opening_slot_bounds_hr (facts : Record.Facts M) (hc : Protocol.HealConfig)
    {r ρ : Round} (h0 : M.opening_slot hc ρ ≤ M.opening_slot hc (r + 1) + 1)
    (h1 : M.opening_slot hc (r + 1) + 1 ≤ M.opening_slot hc (ρ + 1)) : ρ = r + 1 := by
  rw [opening_slot_closed_hr facts, opening_slot_closed_hr facts] at h0 h1
  exact nat_eq_succ_of_mul_bounds_l9 r ρ hc.R hc.R_ge_three h0 h1

/-- `SynchronyFromWakeBefore.mono` with the synchrony hypothesis first. -/
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

/-- The round of the slot one before round `ρ + 1`'s opening slot is `ρ`:
    `round_of (o_{ρ+1} + 1 − 2) = ρ`. -/
theorem round_of_opening_succ_add_one_sub_two (facts : Record.Facts M) (hc : Protocol.HealConfig) (ρ : Round) :
    (M.round_of hc ((M.opening_slot hc (ρ + 1)) + 1 - 2)) = ρ := by
  have hR := hc.R_ge_three
  rw [nat_add_one_sub_two_l9 _ _ _ (facts.gr.opening_slot_succ hc ρ) hR]
  exact facts.gr.round_of_opening_slot_add hc ρ (by omega)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog

/-- The round of the slot after round `ρ + 1`'s opening slot is `ρ + 1`. -/
theorem round_of_opening_succ_add_one (facts : Record.Facts M) (hc : Protocol.HealConfig) (ρ : Round) :
    (M.round_of hc ((M.opening_slot hc (ρ + 1)) + 1)) = ρ + 1 :=
  facts.gr.round_of_opening_slot_add hc (ρ + 1) (by have := hc.R_ge_three; omega)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog

/-- If `confirmedSettleTime S tE ≤ t ≤ S.a r`, then `tE` is at or before the start of slot
    `o_{r+1} + 2`. -/
theorem phaseEnd_le_slotStart_of_read (facts : Record.Facts M) (S : Setup V) {tE t : Int} {r : Nat}
    (h0 : Restated.confirmedSettleTime M S tE ≤ t) (h1 : t ≤ (M.a S.hc S.E.Δ r)) :
    tE ≤ slotStart S.E.Δ ((M.opening_slot S.hc (r + 1)) + 1 + 1) := by
  have h8 := Restated.tAwakeEnd_lt_confirmedSettleTime_add facts S tE
  have ha := action_closed_hr facts S r
  have hd := S.E.Δ_pos
  have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
  have h1' : t ≤ (Restated.Vocabulary.Execution.Setup.a M S r) := h1
  rw [slotStart_closed, opening_slot_closed_hr facts]
  push_cast
  nlinarith

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog

/-- Under `committeeSleepinessW` from `tE`, on an execution whose time diverges, if every honest
    active committee member of every slot from `s_0` to `sEnd` votes for a descendant of `A`, and of
    every slot from `s_1` to `sEnd` for a descendant of `B`, and `s` is a positive slot from `s_0`
    and `s_1` to `sEnd` whose successor starts at or after `tE`, then `A` and `B` lie on one chain. -/
theorem compatible_of_ancestorOfHonestHeadsFromTo_at (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (htd : Restated.TimeDiverges M x) {tE : Int}
    (hcs : Restated.committeeSleepinessW M S Sched tE) {A B : Block V} {s_0 s_1 sEnd s : Slot}
    (hs : 0 < s) (ht : tE ≤ slotStart S.E.Δ (s + 1)) (h0 : s_0 ≤ s) (h1 : s_1 ≤ s)
    (hsE : s ≤ sEnd)
    (hA : Restated.AncestorOfHonestHeadsFromTo M S Sched x A s_0 sEnd)
    (hB : Restated.AncestorOfHonestHeadsFromTo M S Sched x B s_1 sEnd) :
    Block.compatible A B = true :=
  Restated.compatible_of_headsBelow_after facts S Sched x htd hcs hs ht (hA s h0 hsE) (hB s h1 hsE)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- On the healing premises, with synchrony only up to
    `max tE (S.a (S.hc.round_of (sEnd - 2) + 1))`: if `v` is honest through step `T`, the time after
    `T` steps is at or after `confirmedSettleTime S tE`, `v` is awake throughout the vote window of
    that time's slot, and `P` is an ancestor of `v`'s stable output there, then every honest active
    committee member of every slot from `slot(x[T].time) + 2` to `sEnd` votes for a descendant of
    `P`. -/
theorem ancestorOfHonestHeadsFrom_of_preceq_get_stable_of_settleTick_upTo (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tGAT tE : Int) (gap : Nat)
    (hgap : gap + 2 ≤ S.cfg.K)
    (hlen : tGAT + (Restated.healingLengthη M S gap + (Restated.constants M S).period) ≤ tE)
    (hgst : S.E.t_GST ≤ tGAT) (hmono : Sched.MonotoneCorruption)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {sEnd : Slot}
    (hsync : Restated.SynchronyFromWakeBefore M S x (max tE ((Restated.Vocabulary.Execution.Setup.a M S ((M.round_of S.hc (sEnd - 2)) + 1)))))
    (hmult : AwakeAtMultiples S Sched)
    (hwakes : Restated.WakesAtActionInstants M S Sched) (hsleeps : Restated.SleepsAfterActionInstants M S Sched)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (htd : Restated.TimeDiverges M x)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    (hsl : sleepinessW S Sched tE) (hrs : Restated.roundSleepinessW M S Sched tE)
    (hcs : Restated.committeeSleepinessW M S Sched tE)
    (hsettle : Restated.RecordsSettledAtSettleTickTo M S Sched x tE sEnd)
    (T : Nat) (hT : Restated.confirmedSettleTime M S tE ≤ (x[T].time : Int))
    (v : V) (hvT : Restated.HonestThrough M Sched x T v)
    (hva : v ∈ activeAtW S Sched (S.E.slotOf (x[T].time : Int)))
    (P : Block V) (hP : Block.Preceq P (M.get_stable (x[T][v].st).st.core)) :
    Restated.AncestorOfHonestHeadsFromTo M S Sched x P (S.E.slotOf (x[T].time : Int) + 2) sEnd := by
  have hsE := hsync.monoU facts (le_max_left _ _)
  have hlen' : tGAT + Restated.healingLengthη M S gap ≤ tE := Restated.healingLength_le_of_kit_l76 facts S hlen
  have hlow := Restated.hlow_of_premises_l85f_upTo facts S Sched x tGAT tE gap hgap hlen hgst hmono hexec hsE hmult
    hwakes hsleeps hcv htd hcom hthird hawake hrec hsl hrs hcs
  have hprev := Restated.basePreviousRoundSGCompatibleWithAnchor_atRound_upTo facts S Sched x tGAT tE gap hlen hgst
    hmono hexec hsE hmult hcv hcom hthird hawake hrec
  have hclear : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
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
      Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T :=
    fun r hrD' hrW => Restated.baseClearFGSource_atRound_of_premises_upTo facts S Sched x tGAT tE gap hgst hmono
      hexec hsE hmult hcv hcom hthird hawake r
      ((Restated.deadlineRoundW_le_rebased facts S tGAT gap).trans hrD') hrW
  have hB' := Restated.baseJustifiedHighAtSwitchRoundW_of_hlow facts S Sched x tGAT tE gap hlow
  obtain ⟨n_W, T_W, hnW, hAW, hJswitch, hbase⟩ := Restated.afterPhaseJointSwitchRound_of_premises_upTo facts S Sched
    x tGAT tE gap hgap hlen hgst hmono hexec hsE hmult hwakes hsleeps hcv htd hcom hthird
    hawake hrec hsl hrs hcs hlow
  have hA := Restated.recordsSettledAtActionTicks_of_joint_upTo facts S Sched x tGAT tE gap hgap hlen hgst hmono hexec
    hsync hmult hwakes hsleeps hcv htd hcom hthird hawake hrec hsl hrs hcs hsettle
  have hrecs := (Restated.records_ancestorOfHonestHeads_of_settle_honestThrough_upTo facts S Sched x tE hexec hmono htd
    tGAT gap hgst hlen' hsync hthird hawake hrs hmult hcv hcs hcom hwakes hsleeps hrec hprev
    hclear hB' hnW hAW hJswitch
    (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _)) hbase hA hvT hT hva le_rfl).1
  have hk : (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)) ≤ (x[T].time : Int) :=
    le_trans (Restated.action_mono facts S (Nat.le_succ _)) hT
  have hS := (Restated.outputs_ancestorOfHonestHeads_of_records_upTo facts S Sched x tE hexec hmono htd tGAT gap
    hgst hlen' hsync hthird hawake hrs hmult hcv hcs hcom hwakes hsleeps hrec hprev hclear hB' hnW
    hAW hJswitch le_rfl
    (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _)) hbase hk hvT hrecs le_rfl).1
  exact Restated.ancestorOfHonestHeadsFrom_of_preceq_upTo facts S Sched x hP hS

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- On the healing premises, with synchrony only up to
    `max tE (max (S.a ρEnd + S.E.Δ) (S.a (S.hc.round_of (sEnd - 2) + 1)))`, there is a tick step
    `n_W` at the switch round's action instant such that at every round `ρ` from the switch round to
    `ρEnd` the joint invariant holds with some tick step `n`, switch step `n_W` and anchor `T`;
    every justified block of a validator honest through its step, at any step from `n_W` to one
    after the round-`(ρ + 1)` tick step, is an ancestor of `T`; and every honest active committee
    member of every slot from `o_ρ + 2` to `sEnd` votes for a descendant of `T`. -/
theorem anchorFacts_of_settleTick_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tGAT tE : Int) (gap : Nat)
    (hgap : gap + 2 ≤ S.cfg.K)
    (hlen : tGAT + (Restated.healingLengthη M S gap + (Restated.constants M S).period) ≤ tE)
    (hgst : S.E.t_GST ≤ tGAT) (hmono : Sched.MonotoneCorruption)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {ρEnd : Round} {sEnd : Slot}
    (hsync : Restated.SynchronyFromWakeBefore M S x
      (max tE (max ((Restated.Vocabulary.Execution.Setup.a M S ρEnd) + S.E.Δ) ((Restated.Vocabulary.Execution.Setup.a M S ((M.round_of S.hc (sEnd - 2)) + 1))))))
    (hmult : AwakeAtMultiples S Sched)
    (hwakes : Restated.WakesAtActionInstants M S Sched) (hsleeps : Restated.SleepsAfterActionInstants M S Sched)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (htd : Restated.TimeDiverges M x)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    (hsl : sleepinessW S Sched tE) (hrs : Restated.roundSleepinessW M S Sched tE)
    (hcs : Restated.committeeSleepinessW M S Sched tE)
    (hsettle : Restated.RecordsSettledAtSettleTickTo M S Sched x tE sEnd) :
    ∃ n_W : Nat, Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))) ∧
      ∀ ρ : Nat, Restated.switchRound M S tE ≤ ρ → ρ ≤ ρEnd →
        ∃ (n : Nat) (T : NamedBlock V),
          Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x ρ n n_W T ∧
          (∀ n' : Nat, Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (ρ + 1))) →
            ∀ (w : V) (n₁ : Nat), n_W ≤ n₁ → n₁ ≤ n' + 1 → Restated.HonestThrough M Sched x n₁ w →
              Block.Preceq (x[n₁][w].st).st.core.J T.erase) ∧
          Restated.AncestorOfHonestHeadsFromTo M S Sched x T.erase ((M.opening_slot S.hc ρ) + 2) sEnd := by
  have hsE := hsync.monoU facts (le_max_left _ _)
  have hlen' : tGAT + Restated.healingLengthη M S gap ≤ tE := Restated.healingLength_le_of_kit_l76 facts S hlen
  have hlow := Restated.hlow_of_premises_l85f_upTo facts S Sched x tGAT tE gap hgap hlen hgst hmono hexec hsE hmult
    hwakes hsleeps hcv htd hcom hthird hawake hrec hsl hrs hcs
  have hprev := Restated.basePreviousRoundSGCompatibleWithAnchor_atRound_upTo facts S Sched x tGAT tE gap hlen hgst
    hmono hexec hsE hmult hcv hcom hthird hawake hrec
  have hclear : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
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
      Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T :=
    fun r hrD' hrW => Restated.baseClearFGSource_atRound_of_premises_upTo facts S Sched x tGAT tE gap hgst hmono
      hexec hsE hmult hcv hcom hthird hawake r
      ((Restated.deadlineRoundW_le_rebased facts S tGAT gap).trans hrD') hrW
  have hB' := Restated.baseJustifiedHighAtSwitchRoundW_of_hlow facts S Sched x tGAT tE gap hlow
  obtain ⟨n_W, T_W, hnW, hAW, hJswitch, hbase⟩ := Restated.afterPhaseJointSwitchRound_of_premises_upTo facts S Sched
    x tGAT tE gap hgap hlen hgst hmono hexec hsE hmult hwakes hsleeps hcv htd hcom hthird
    hawake hrec hsl hrs hcs hlow
  refine ⟨n_W, hnW, fun ρ hρ hρE => ?_⟩
  obtain ⟨n, T, hJ, -, hTW⟩ := Restated.anchor_at_later_round_upTo facts S Sched x tE hexec hmono htd
    tGAT gap hgst hlen' hsync hthird hawake hrs hmult hcv hcs hcom hwakes hsleeps hrec hprev hclear
    hB' hnW hAW hJswitch le_rfl (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _)) hbase hρ
    (max_le_max le_rfl (le_trans (by have := Restated.action_mono facts S hρE; linarith) (le_max_left _ _)))
  refine ⟨n, T, hJ, fun n' hn' => ?_, ?_⟩
  · exact Restated.justified_preceq_anchor_ofJoint_upTo facts S Sched x tE hexec hmono htd tGAT gap hgst hlen' hsE
      hthird hawake hrs hmult hcv hcom hrec hprev hclear hB' hnW hAW hρ hTW hJ hn'
  · exact Restated.anchor_ancestorOfHonestHeadsFrom_upTo facts S Sched x tE hexec hmono htd tGAT gap hgst hlen'
      (hsync.monoU facts (max_le_max le_rfl (le_max_right _ _))) hthird hawake hrs hmult hcv hcs hcom
      hwakes hsleeps hrec hprev hclear hB' hnW hAW hJswitch hρ hTW hJ

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- On the healing premises, with synchrony only up to `b₀ ≥ max tE (S.a (r + 1))`, for a validator
    `v` honest through a step `T` whose time is between `confirmedSettleTime S tE` and `S.a r`,
    awake throughout the vote window of its slot, and a block `P` that is an ancestor of `v`'s
    stable output there: right after the tick at `S.a (r + 1)`, every validator `w` honest through
    that step holds a finalized block and a justified block that are each an ancestor or a
    descendant of `P`. -/
theorem stableHandover_roots_of_settleTick_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tGAT tE : Int) (gap : Nat)
    (hgap : gap + 2 ≤ S.cfg.K)
    (hlen : tGAT + (Restated.healingLengthη M S gap + (Restated.constants M S).period) ≤ tE)
    (hgst : S.E.t_GST ≤ tGAT) (hmono : Sched.MonotoneCorruption)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {b₀ : Int} (hsync : Restated.SynchronyFromWakeBefore M S x b₀) (hmult : AwakeAtMultiples S Sched)
    (hwakes : Restated.WakesAtActionInstants M S Sched) (hsleeps : Restated.SleepsAfterActionInstants M S Sched)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (htd : Restated.TimeDiverges M x)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    (hsl : sleepinessW S Sched tE) (hrs : Restated.roundSleepinessW M S Sched tE)
    (hcs : Restated.committeeSleepinessW M S Sched tE)
    {sEnd : Slot} (hsettle : Restated.RecordsSettledAtSettleTickTo M S Sched x tE sEnd)
    (r : Nat) (T : Nat) (hT : Restated.confirmedSettleTime M S tE ≤ (x[T].time : Int))
    (hTr : (x[T].time : Int) ≤ (M.a S.hc S.E.Δ r))
    (v : V) (hvT : Restated.HonestThrough M Sched x T v)
    (hva : v ∈ activeAtW S Sched (S.E.slotOf (x[T].time : Int)))
    (P : Block V) (hP : Block.Preceq P (M.get_stable (x[T][v].st).st.core))
    (hsEnd : (M.opening_slot S.hc (r + 1)) + 1 ≤ sEnd) (hb₀ : max tE ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) ≤ b₀) :
    ∀ n : Nat, Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      ∀ w : V, Restated.HonestThrough M Sched x (n + 1) w →
        Block.Compatible P (x[n + 1][w].st).st.core.F ∧
        Block.Compatible P (x[n + 1][w].st).st.core.J := by
  have hR := Restated.round_of_opening_succ_add_one_sub_two facts S.hc r
  have hPh := Restated.ancestorOfHonestHeadsFrom_of_preceq_get_stable_of_settleTick_upTo facts S Sched x tGAT tE gap
    hgap hlen hgst hmono hexec (sEnd := (M.opening_slot S.hc (r + 1)) + 1)
    (hsync.monoU facts (by rw [hR]; exact hb₀)) hmult hwakes hsleeps hcv htd hcom hthird hawake hrec
    hsl hrs hcs (hsettle.mono_end facts hsEnd) T hT v hvT hva P hP
  have hrW := Restated.switchRound_lt_of_settle_le_action facts S hT hTr
  have hra := Restated.action_add_delta_le_succ facts S r
  obtain ⟨n_W, hnW, hfacts⟩ := Restated.anchorFacts_of_settleTick_upTo facts S Sched x tGAT tE gap hgap hlen hgst hmono
    hexec (ρEnd := r) (sEnd := (M.opening_slot S.hc (r + 1)) + 1)
    (hsync.monoU facts (by
      rw [hR]
      exact max_le (le_trans (le_max_left _ _) hb₀)
        (max_le (le_trans hra (le_trans (le_max_right _ _) hb₀))
          (le_trans (le_max_right _ _) hb₀))))
    hmult hwakes hsleeps hcv htd hcom hthird hawake hrec hsl hrs hcs (hsettle.mono_end facts hsEnd)
  obtain ⟨_, Tr, -, hJT, hanc⟩ := hfacts r (le_of_lt hrW) le_rfl
  intro n hn w hw
  have hWn : n_W ≤ n + 1 := by
    by_contra hcon
    have h1 := Restated.time_mono_int facts S Sched x (Nat.le_of_lt (Nat.lt_of_not_le hcon))
    rw [(Restated.tickStepAt_time facts x hn).1] at h1
    have h2 := (Restated.tickStepAt_time facts x hnW).2
    have h3 := Restated.action_mono facts S (Nat.le_succ_of_le (le_of_lt hrW))
    linarith
  have hJ := hJT n hn w (n + 1) hWn le_rfl hw
  have hJh := Restated.ancestorOfHonestHeadsFrom_of_preceq_upTo facts S Sched x hJ hanc
  have hFh := Restated.ancestorOfHonestHeadsFrom_of_preceq_upTo facts S Sched x
    (preceq_trans_Preceq (Restated.finalized_preceq_justified_sts facts S Sched x (n + 1) w) hJ) hanc
  have hsP : S.E.slotOf (x[T].time : Int) + 2 ≤ (M.opening_slot S.hc (r + 1)) + 1 :=
    Nat.le_succ_of_le (Restated.slotOf_add_two_le_opening_of_le_action facts S hTr le_rfl)
  have hsT : (M.opening_slot S.hc r) + 2 ≤ (M.opening_slot S.hc (r + 1)) + 1 :=
    nat_add_two_le_l9 _ _ _ _ (facts.gr.opening_slot_succ S.hc r) le_rfl S.hc.R_ge_three
  have ht := Restated.phaseEnd_le_slotStart_of_read facts S hT hTr
  exact ⟨compatible_iff_Compatible.mpr (Restated.compatible_of_ancestorOfHonestHeadsFromTo_at facts S Sched x
      htd hcs (Nat.succ_pos _) ht hsP hsT le_rfl hPh hFh),
    compatible_iff_Compatible.mpr (Restated.compatible_of_ancestorOfHonestHeadsFromTo_at facts S Sched x
      htd hcs (Nat.succ_pos _) ht hsP hsT le_rfl hPh hJh)⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- On the premises of `stableHandover_roots_of_settleTick_upTo`, with synchrony only up to
    `b₀ ≥ max tE (S.a (r + 1) + S.E.Δ)`: if `u` is honest through the step after the tick at
    `S.a (r + 1)`, the sent log right after that tick holds `u`'s attestation `a` whose height pair
    is a vote for height `h` bound to the root `root`, and that attestation was not in the sent log
    at the switch round's tick step, then every block on the wire whose root is `root` is an
    ancestor or a descendant of `P`. -/
theorem stableHandover_entries_sinceSwitch_of_settleTick_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tGAT tE : Int) (gap : Nat)
    (hgap : gap + 2 ≤ S.cfg.K)
    (hlen : tGAT + (Restated.healingLengthη M S gap + (Restated.constants M S).period) ≤ tE)
    (hgst : S.E.t_GST ≤ tGAT) (hmono : Sched.MonotoneCorruption)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {b₀ : Int} (hsync : Restated.SynchronyFromWakeBefore M S x b₀) (hmult : AwakeAtMultiples S Sched)
    (hwakes : Restated.WakesAtActionInstants M S Sched) (hsleeps : Restated.SleepsAfterActionInstants M S Sched)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (htd : Restated.TimeDiverges M x)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    (hsl : sleepinessW S Sched tE) (hrs : Restated.roundSleepinessW M S Sched tE)
    (hcs : Restated.committeeSleepinessW M S Sched tE)
    {sEnd : Slot} (hsettle : Restated.RecordsSettledAtSettleTickTo M S Sched x tE sEnd)
    (r : Nat) (T : Nat) (hT : Restated.confirmedSettleTime M S tE ≤ (x[T].time : Int))
    (hTr : (x[T].time : Int) ≤ (M.a S.hc S.E.Δ r))
    (v : V) (hvT : Restated.HonestThrough M Sched x T v)
    (hva : v ∈ activeAtW S Sched (S.E.slotOf (x[T].time : Int)))
    (P : Block V) (hP : Block.Preceq P (M.get_stable (x[T][v].st).st.core))
    (hsEnd : (M.opening_slot S.hc (r + 1)) + 1 ≤ sEnd)
    (hb₀ : max tE ((Restated.Vocabulary.Execution.Setup.a M S (r + 1)) + S.E.Δ) ≤ b₀) :
    ∀ n_W : Nat, Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))) →
    ∀ n : Nat, Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
    ∀ (u : V) (a : NamedAttestation V) (h : Height) (root : BlockId) (tmo : Bool),
    Restated.HonestThrough M Sched x (n + 1) u → a.val_index = u →
    (⟨u, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n + 1].sent →
    (⟨u, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∉ x[n_W].sent →
    a.height_pair = NamedHeightPair.vote h root tmo →
    ∀ C : NamedBlock V, Restated.blockInLog M S Sched x C → C.root = root →
      Block.Compatible P C.erase := by
  have hsE : Restated.SynchronyFromWakeBefore M S x tE := hsync.monoU facts (le_trans (le_max_left _ _) hb₀)
  have hR := Restated.round_of_opening_succ_add_one_sub_two facts S.hc r
  have hR1 := Restated.round_of_opening_succ_add_one facts S.hc r
  have hra := Restated.action_add_delta_le_succ facts S r
  have hd := S.E.Δ_pos
  have hPh := Restated.ancestorOfHonestHeadsFrom_of_preceq_get_stable_of_settleTick_upTo facts S Sched x tGAT tE gap
    hgap hlen hgst hmono hexec (sEnd := (M.opening_slot S.hc (r + 1)) + 1)
    (hsync.monoU facts (by
      rw [hR]
      exact le_trans (max_le_max le_rfl (by linarith)) hb₀))
    hmult hwakes hsleeps hcv htd hcom hthird hawake hrec
    hsl hrs hcs (hsettle.mono_end facts hsEnd) T hT v hvT hva P hP
  have hrW := Restated.switchRound_lt_of_settle_le_action facts S hT hTr
  have hlen' : tGAT + Restated.healingLengthη M S gap ≤ tE := Restated.healingLength_le_of_kit_l76 facts S hlen
  have hlow := Restated.hlow_of_premises_l85f_upTo facts S Sched x tGAT tE gap hgap hlen hgst hmono hexec hsE hmult
    hwakes hsleeps hcv htd hcom hthird hawake hrec hsl hrs hcs
  have hprev := Restated.basePreviousRoundSGCompatibleWithAnchor_atRound_upTo facts S Sched x tGAT tE gap hlen hgst
    hmono hexec hsE hmult hcv hcom hthird hawake hrec
  have hclear : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
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
      Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T :=
    fun r hrD' hrW => Restated.baseClearFGSource_atRound_of_premises_upTo facts S Sched x tGAT tE gap hgst hmono
      hexec hsE hmult hcv hcom hthird hawake r
      ((Restated.deadlineRoundW_le_rebased facts S tGAT gap).trans hrD') hrW
  have hB' := Restated.baseJustifiedHighAtSwitchRoundW_of_hlow facts S Sched x tGAT tE gap hlow
  obtain ⟨n_W₀, T_W, hnW₀, hAW, hJswitch, hbase⟩ := Restated.afterPhaseJointSwitchRound_of_premises_upTo facts S
    Sched x tGAT tE gap hgap hlen hgst hmono hexec hsE hmult hwakes hsleeps hcv htd hcom hthird
    hawake hrec hsl hrs hcs hlow
  have hs1 : (M.opening_slot S.hc (Restated.switchRound M S tE + 1)) ≤ (M.opening_slot S.hc (r + 1)) + 1 :=
    Nat.le_succ_of_le (facts.gr.opening_slot_mono S (Nat.succ_le_succ (le_of_lt hrW)))
  obtain ⟨r₁, n₂, T', -, -, hJ', hs0', hs1', hT'⟩ := Restated.exists_joint_anchor_headsBelow_atSlot_upTo facts S
    Sched x tE hexec hmono htd tGAT gap hgst hlen' hsync hthird hawake hrs hmult hcv hcs hcom hwakes
    hsleeps hrec hprev hclear hB' hnW₀ hAW hJswitch
    (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _)) hbase hs1
    (by
      rw [hR, hR1]
      exact max_le (le_trans (le_max_left _ _) hb₀)
        (max_le (le_trans (by linarith) (le_trans (le_max_right _ _) hb₀))
          (le_trans (le_max_right _ _) hb₀)))
  obtain rfl := eq_succ_of_opening_slot_bounds_hr facts S.hc hs0' hs1'
  intro n_W hnW n hn u a h root tmo hu hau hsent hnot hpair C hC hroot
  obtain rfl := Restated.tickStepAt_unique facts x hnW hnW₀
  obtain rfl := Restated.tickStepAt_unique facts x hJ'.tick hn
  have hceil := hJ'.heightCeiling u (n₂ + 1) a h root tmo le_rfl hu hau hsent hpair
  have hCT := hJ'.targetsSince u (n₂ + 1) a h root tmo le_rfl hu hau hsent hnot hpair hceil C hC
    hroot
  have hTh : Restated.AncestorOfHonestHeadsFromTo M S Sched x T'.erase ((M.opening_slot S.hc (r + 1)) + 1)
      ((M.opening_slot S.hc (r + 1)) + 1) := fun s' h1 h2 => by
    rw [le_antisymm h2 h1]; exact hT'
  have hsP : S.E.slotOf (x[T].time : Int) + 2 ≤ (M.opening_slot S.hc (r + 1)) + 1 :=
    Nat.le_succ_of_le (Restated.slotOf_add_two_le_opening_of_le_action facts S hTr le_rfl)
  exact compatible_iff_Compatible.mpr
    (Restated.compatible_of_ancestorOfHonestHeadsFromTo_at facts S Sched x htd hcs (Nat.succ_pos _)
      (Restated.phaseEnd_le_slotStart_of_read facts S hT hTr) hsP le_rfl le_rfl hPh
      (Restated.ancestorOfHonestHeadsFrom_of_preceq_upTo facts S Sched x hCT hTh))

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- On the premises of `stableHandover_roots_of_settleTick_upTo`, with synchrony only up to
    `b₀ ≥ max tE (S.a (r + 1) + S.E.Δ)`: if `u` is honest through the step after the tick at
    `S.a (r + 1)` and the sent log right after that tick holds `u`'s attestation `a` whose height
    pair is a vote for height `h` bound to the root `root`, then every block on the wire whose root
    is `root` is an ancestor or a descendant of `P`, or `h` is less than the justified height every
    validator honest through that step holds after it. -/
theorem stableHandover_entries_of_settleTick_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tGAT tE : Int) (gap : Nat)
    (hgap : gap + 2 ≤ S.cfg.K)
    (hlen : tGAT + (Restated.healingLengthη M S gap + (Restated.constants M S).period) ≤ tE)
    (hgst : S.E.t_GST ≤ tGAT) (hmono : Sched.MonotoneCorruption)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {b₀ : Int} (hsync : Restated.SynchronyFromWakeBefore M S x b₀) (hmult : AwakeAtMultiples S Sched)
    (hwakes : Restated.WakesAtActionInstants M S Sched) (hsleeps : Restated.SleepsAfterActionInstants M S Sched)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (htd : Restated.TimeDiverges M x)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    (hsl : sleepinessW S Sched tE) (hrs : Restated.roundSleepinessW M S Sched tE)
    (hcs : Restated.committeeSleepinessW M S Sched tE)
    {sEnd : Slot} (hsettle : Restated.RecordsSettledAtSettleTickTo M S Sched x tE sEnd)
    (r : Nat) (T : Nat) (hT : Restated.confirmedSettleTime M S tE ≤ (x[T].time : Int))
    (hTr : (x[T].time : Int) ≤ (M.a S.hc S.E.Δ r))
    (v : V) (hvT : Restated.HonestThrough M Sched x T v)
    (hva : v ∈ activeAtW S Sched (S.E.slotOf (x[T].time : Int)))
    (P : Block V) (hP : Block.Preceq P (M.get_stable (x[T][v].st).st.core))
    (hsEnd : (M.opening_slot S.hc (r + 1)) + 1 ≤ sEnd)
    (hb₀ : max tE ((Restated.Vocabulary.Execution.Setup.a M S (r + 1)) + S.E.Δ) ≤ b₀) :
    ∀ n : Nat, Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      ∀ (u : V) (a : NamedAttestation V) (h : Height) (root : BlockId) (tmo : Bool),
      Restated.HonestThrough M Sched x (n + 1) u → a.val_index = u →
      (⟨u, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n + 1].sent →
      a.height_pair = NamedHeightPair.vote h root tmo →
      ∀ C : NamedBlock V, Restated.blockInLog M S Sched x C → C.root = root →
        Block.Compatible P C.erase ∨
          ∀ w : V, Restated.HonestThrough M Sched x (n + 1) w → h < (x[n + 1][w].st).st.core.h_j := by
  have hlen' : tGAT + Restated.healingLengthη M S gap ≤ tE := Restated.healingLength_le_of_kit_l76 facts S hlen
  have hsE : Restated.SynchronyFromWakeBefore M S x tE := hsync.monoU facts (le_trans (le_max_left _ _) hb₀)
  have hR := Restated.round_of_opening_succ_add_one_sub_two facts S.hc r
  have hd := S.E.Δ_pos
  have hbR : max tE ((Restated.Vocabulary.Execution.Setup.a M S ((M.round_of S.hc ((M.opening_slot S.hc (r + 1)) + 1 - 2)) + 1))) ≤ b₀ := by
    rw [hR]; exact le_trans (max_le_max le_rfl (by linarith)) hb₀
  have hPh := Restated.ancestorOfHonestHeadsFrom_of_preceq_get_stable_of_settleTick_upTo facts S Sched x tGAT tE gap
    hgap hlen hgst hmono hexec (sEnd := (M.opening_slot S.hc (r + 1)) + 1) (hsync.monoU facts hbR) hmult
    hwakes hsleeps hcv htd hcom hthird hawake hrec
    hsl hrs hcs (hsettle.mono_end facts hsEnd) T hT v hvT hva P hP
  have hrW := Restated.switchRound_lt_of_settle_le_action facts S hT hTr
  have hlow := Restated.hlow_of_premises_l85f_upTo facts S Sched x tGAT tE gap hgap hlen hgst hmono hexec hsE hmult
    hwakes hsleeps hcv htd hcom hthird hawake hrec hsl hrs hcs
  have hprev := Restated.basePreviousRoundSGCompatibleWithAnchor_atRound_upTo facts S Sched x tGAT tE gap hlen hgst
    hmono hexec hsE hmult hcv hcom hthird hawake hrec
  have hclear : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
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
      Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T :=
    fun r hrD' hrW => Restated.baseClearFGSource_atRound_of_premises_upTo facts S Sched x tGAT tE gap hgst hmono
      hexec hsE hmult hcv hcom hthird hawake r
      ((Restated.deadlineRoundW_le_rebased facts S tGAT gap).trans hrD') hrW
  have hB' := Restated.baseJustifiedHighAtSwitchRoundW_of_hlow facts S Sched x tGAT tE gap hlow
  obtain ⟨n_W, T_W, hnW, hAW, hJswitch, hbase⟩ := Restated.afterPhaseJointSwitchRound_of_premises_upTo facts S Sched
    x tGAT tE gap hgap hlen hgst hmono hexec hsE hmult hwakes hsleeps hcv htd hcom hthird
    hawake hrec hsl hrs hcs hlow
  obtain ⟨v₀, -⟩ := exists_not_adv_l76 S Sched (hthird tE le_rfl)
  have hrDW' : Restated.rebasedDeadlineRoundW M S tGAT gap ≤ Restated.switchRound M S tE :=
    Restated.rebasedDeadlineRoundW_le_switchRound facts S tGAT tE gap (Restated.runAll M S Sched x v₀ 0) hgst hlen'
  obtain ⟨T_D', hAD'⟩ := Restated.exists_anchorAtRound_upTo facts S Sched x hsE hmono hawake hgst hcv hexec hmult
    hthird hcom hrec hlen' htd (Restated.deadlineRoundW_le_rebased facts S tGAT gap) hrDW'
  have hWh := Restated.anchor_ancestorOfHonestHeadsFrom_upTo facts S Sched x tE hexec hmono htd tGAT gap hgst
    hlen' (sEnd := (M.opening_slot S.hc (r + 1)) + 1) (hsync.monoU facts hbR) hthird hawake hrs hmult hcv hcs
    hcom hwakes hsleeps hrec hprev hclear hB' hnW hAW
    hJswitch le_rfl (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _)) hbase
  have hsP : S.E.slotOf (x[T].time : Int) + 2 ≤ (M.opening_slot S.hc (r + 1)) + 1 :=
    Nat.le_succ_of_le (Restated.slotOf_add_two_le_opening_of_le_action facts S hTr le_rfl)
  have hsW : (M.opening_slot S.hc (Restated.switchRound M S tE)) + 2 ≤ (M.opening_slot S.hc (r + 1)) + 1 := by
    exact nat_add_two_le_l9 _ _ _ _ (facts.gr.opening_slot_succ S.hc r)
      (facts.gr.opening_slot_mono S (le_of_lt hrW)) S.hc.R_ge_three
  intro n hn u a h root tmo hu hau hsent hpair C hC hroot
  have hWn : n_W ≤ n + 1 := by
    by_contra hcon
    have h1 := Restated.time_mono_int facts S Sched x (Nat.le_of_lt (Nat.lt_of_not_le hcon))
    rw [(Restated.tickStepAt_time facts x hn).1] at h1
    have h2 := (Restated.tickStepAt_time facts x hnW).2
    have h3 := Restated.action_mono facts S (Nat.le_succ_of_le (le_of_lt hrW))
    linarith
  have hthrough : ∀ w : V, Restated.HonestThrough M Sched x (n + 1) w → Restated.HonestThrough M Sched x n_W w :=
    fun w hw t ht => hw t (ht.trans (Restated.time_mono_int facts S Sched x hWn))
  by_cases hin : (⟨u, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n_W].sent
  · by_cases hhi : (M.derive_named S.E S.cfg T_D').h ≤ h
    · -- case 2: an older vote at a height at least `h(T_D')`
      left
      have hCW := Restated.honestVotes_onAnchorChain_since_roundW_upTo facts S Sched x hsE hmono hawake hgst hcv
        hexec hmult hthird hcom hrec hlen' htd (Restated.deadlineRoundW_le_rebased facts S tGAT gap) hrDW'
        (fun ρ hρ hρW => hprev ρ hρ hρW) (fun ρ hρ hρW => hclear ρ hρ hρW) hAD' hAW hnW
        u n_W a h root tmo (Nat.le_succ _) (hthrough u hu) hau hin hpair hhi C hC hroot
      exact compatible_iff_Compatible.mpr
        (Restated.compatible_of_ancestorOfHonestHeadsFromTo_at facts S Sched x htd hcs (Nat.succ_pos _)
          (Restated.phaseEnd_le_slotStart_of_read facts S hT hTr) hsP hsW le_rfl hPh
          (Restated.ancestorOfHonestHeadsFrom_of_preceq_upTo facts S Sched x hCW hWh))
    · -- case 3: an older vote at a height less than `h(T_D')`
      right
      intro w hw
      have hlo : (M.derive_named S.E S.cfg T_D').h ≤ (x[n_W][w].st).st.core.h_j :=
        hB' T_D' hAD' n_W hnW w (hthrough w hw)
      have hmo := Restated.h_j_mono_sts facts S Sched x w hWn
      have hlt : h < (M.derive_named S.E S.cfg T_D').h := Nat.lt_of_not_le hhi
      exact lt_of_lt_of_le hlt (le_trans hlo hmo)
  · -- case 1: a vote absent from the sent log at the switch round's tick step
    left
    exact Restated.stableHandover_entries_sinceSwitch_of_settleTick_upTo facts S Sched x tGAT tE gap hgap hlen hgst
      hmono hexec hsync hmult hwakes hsleeps hcv htd hcom hthird hawake hrec hsl hrs hcs
      hsettle r T hT hTr v hvT hva P hP hsEnd hb₀ n_W hnW n hn u a h root tmo hu hau hsent hin
      hpair C hC hroot

end

end DecoupledConsensusModel.Sts.Restated
