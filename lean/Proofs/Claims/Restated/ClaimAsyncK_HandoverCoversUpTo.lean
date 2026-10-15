import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariantActiveSinceW
import Proofs.Claims.Restated.Claim13bK_AttestedDescendantUpTo
import Proofs.Claims.Restated.Claim13bW_Schedule
import Proofs.Claims.Restated.Claim13beRoute3_76
import Proofs.Claims.Restated.Claim13beRoute3_85fUpTo
import Proofs.Claims.Restated.Claim13beRoute3_88UpTo
import Proofs.Claims.Restated.Claim13beRoute3_91UpTo
import Proofs.Claims.Restated.ClaimAsyncK_HandoverCovers
import Proofs.Claims.Restated.ClaimAsyncK_HandoverRoots
import Proofs.Claims.Restated.ClaimAsyncK_HandoverRootsUpTo
import Proofs.Claims.Restated.ClaimConfirmedAfterHealingKit
import Proofs.Claims.Restated.ClaimConfirmedAfterHealingKitUpTo
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActiveJoint
import Model.Conditions.Claim13bInvariantActiveSinceW
import Model.Conditions.Claim13bK_ConfirmedWakeUpTo
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13bStepConeIter
import Model.Conditions.Claim13bStepKitTick
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
import Proofs.Claims.Spec2Claims.ClaimAsyncK_HandoverCoversUpTo

/-!
# The field `covers` of the hand-over

Theorems over a model `M : Record.Model V` with facts `facts : Record.Facts M`, leading to the field
`covers` of `Restated.StableHandover` at round `r + 1` (`stableHandover_covers_of_settleTick_upTo`),
with synchrony assumed only up to a bound `b₀`.
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

/-- The round of the slot two before round `ρ + 1`'s opening slot is `ρ`:
    `round_of (o_{ρ+1} − 2) = ρ`. -/
theorem round_of_opening_succ_sub_two (facts : Record.Facts M) (hc : Protocol.HealConfig) (ρ : Round) :
    (M.round_of hc ((M.opening_slot hc (ρ + 1)) - 2)) = ρ := by
  have hR := hc.R_ge_three
  rw [nat_sub_two_l9 _ _ _ (facts.gr.opening_slot_succ hc ρ) hR]
  exact facts.gr.round_of_opening_slot_add hc ρ (by omega)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- On the healing premises, with synchrony only up to `b₀ ≥ max tE (S.a (r + 2) + S.E.Δ)`: for a
    validator `v` honest through a step `T` whose time is between `confirmedSettleTime S tE` and
    `S.a r`, awake throughout the vote window of its slot, and a block `P` that is an ancestor of
    `v`'s stable output there, every round-`(r + 1)` or round-`(r + 2)` attestation computed at that
    round's tick by a validator awake throughout the round's attester window and honest through the
    step after the tick names a block of that validator's tree after the tick that is `P` or a
    descendant of `P`. -/
theorem stableHandover_covers_of_settleTick_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
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
    (hsEnd : (M.opening_slot S.hc (r + 2)) ≤ sEnd)
    (hb₀ : max tE ((Restated.Vocabulary.Execution.Setup.a M S (r + 2)) + S.E.Δ) ≤ b₀) :
    ∀ ρ : Nat, (ρ = r + 1 ∨ ρ = r + 2) → ∀ n : Nat, Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S ρ)) →
      ∀ u ∈ Restated.activeRoundW M S Sched ρ, Restated.HonestThrough M Sched x (n + 1) u →
      ∀ C : NamedBlock V, C ∈ (x[n + 1][u].st).st.bodies →
      ∀ a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][u].st) u ρ,
        a.confirmed = some C.root →
        Block.Preceq P C.erase := by
  have hsE : Restated.SynchronyFromWakeBefore M S x tE := hsync.monoU facts (le_trans (le_max_left _ _) hb₀)
  have hd := S.E.Δ_pos
  have hRc : (M.round_of S.hc ((M.opening_slot S.hc (r + 2)) - 2)) = r + 1 :=
    Restated.round_of_opening_succ_sub_two facts S.hc (r + 1)
  have hPh := Restated.ancestorOfHonestHeadsFrom_of_preceq_get_stable_of_settleTick_upTo facts S Sched x tGAT tE gap
    hgap hlen hgst hmono hexec (sEnd := (M.opening_slot S.hc (r + 2)))
    (hsync.monoU facts (by rw [hRc]; exact le_trans (max_le_max le_rfl (by linarith)) hb₀))
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
  obtain ⟨n_W, T_W, hnW, hAW, hJswitch, hbase⟩ := Restated.afterPhaseJointSwitchRound_of_premises_upTo facts S Sched
    x tGAT tE gap hgap hlen hgst hmono hexec hsE hmult hwakes hsleeps hcv htd hcom hthird
    hawake hrec hsl hrs hcs hlow
  intro ρ hρ n hn u hu hvh C hC a ha hconf
  have hρr : r + 1 ≤ ρ := by
    rcases hρ with h | h
    · exact le_of_eq h.symm
    · rw [h]; exact Nat.le_succ _
  have hq : Restated.switchRound M S tE + 2 ≤ ρ := le_trans (Nat.succ_le_succ hrW) hρr
  have hρ2 : ρ ≤ r + 2 := by
    rcases hρ with h | h
    · rw [h]; exact Nat.le_succ _
    · exact le_of_eq h
  have hX : Restated.HeadsBelow M S Sched x P ((M.opening_slot S.hc ρ)) :=
    hPh _ (Restated.slotOf_add_two_le_opening_of_le_action facts S hTr hρr) (facts.gr.opening_slot_mono S hρ2)
  exact Restated.attested_descendant_of_headsBelow_covers_upTo facts S Sched x tE hexec hmono htd tGAT gap hgst
    hlen' hsync hthird hawake hrs hmult hcv hcs hcom hwakes hsleeps hrec hprev hclear hB' hnW hAW
    hJswitch (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _)) hbase hq hX hn hu hvh hC a ha hconf
    (le_trans (max_le_max le_rfl (by have := Restated.action_mono facts S hρ2; linarith)) hb₀)

end

end DecoupledConsensusModel.Sts.Restated
