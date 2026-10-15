import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bHandover
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bInvariantActiveSinceW
import Proofs.Claims.Restated.Claim13bK_ConfirmedSettleEarlier
import Proofs.Claims.Restated.Claim13bK_ConfirmedStrongRound
import Proofs.Claims.Restated.Claim13bK_ConfirmedStrongRoundWindow
import Proofs.Claims.Restated.Claim13bSGCompatible
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bStepKitTick
import Proofs.Claims.Restated.Claim13bW_Schedule
import Proofs.Claims.Restated.Claim13beRoute3_58
import Proofs.Claims.Restated.Claim13beRoute3_76
import Proofs.Claims.Restated.Claim13beRoute3_85f
import Proofs.Claims.Restated.Claim13beRoute3_88
import Proofs.Claims.Restated.Claim13beRoute3_91
import Proofs.Claims.Restated.ClaimConfirmedAfterHealingKit
import Proofs.Claims.Restated.Constants
import Model.Conditions.Claim13bHandover
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActive
import Model.Conditions.Claim13bInvariantActiveJoint
import Model.Conditions.Claim13bInvariantActiveSinceW
import Model.Conditions.Claim13bK_ConfirmedRecord
import Model.Conditions.Claim13bK_ConfirmedSettle
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_72
import Model.Conditions.Claim13beRoute3_74
import Model.Conditions.Claim13beRoute3_83
import Model.Conditions.RunAll
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13bd
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Sts_Spec2Claims_Claim13bf
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bK_ConfirmedStrongRoundSettle

/-!
# The settle fact at a strong round

Timing facts about opening slots, confirmation times and action times, and the theorem that at a
round `c` with honest opening proposers at `c` and `c − 1` the stable and confirmed records of
honest attesters settle on honest heads, stated over a model `M : Record.Model V`.
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
private theorem opening_slot_closed_srs (facts : Record.Facts M) (hc : Protocol.HealConfig)
    (r : Round) : M.opening_slot hc r = r * hc.R := by
  have h := facts.gr.opening_slot_add_mk hc 0 r
  rw [Nat.zero_add, facts.gr.opening_slot_zero_mk, Nat.zero_add] at h
  exact h

/-- The confirmation time of slot `s` is `4 * Δ * s + 6 * Δ`. -/
private theorem confirmation_time_closed_srs (facts : Record.Facts M) (E : Env V) (s : Slot) :
    M.confirmation_time E s = 4 * E.Δ * (s : Int) + 6 * E.Δ := by
  rw [← facts.sch.slotStart_add_six_delta_eq_confirmation_time E s, slotStart_closed]

/-- The action time of round `r` is `4 * Δ * R * r + 6 * Δ`. -/
private theorem action_closed_srs (facts : Record.Facts M) (S : Setup V) (r : Round) :
    (Restated.Vocabulary.Execution.Setup.a M S r) =
      4 * S.E.Δ * (S.hc.R : Int) * (r : Int) + 6 * S.E.Δ := by
  show M.a S.hc S.E.Δ r = _
  rw [facts.sch.a_eq_confirmation_time S.hc S.E r, confirmation_time_closed_srs facts,
    opening_slot_closed_srs facts]
  push_cast
  ring

/-- The opening time of round `r` is `4 * Δ` times round `r`'s opening slot. -/
private theorem opening_closed_srs (facts : Record.Facts M) (S : Setup V) (r : Round) :
    M.opening S.E S.hc r = 4 * S.E.Δ * (((M.opening_slot S.hc r) : Nat) : Int) := by
  rw [facts.gr.opening_eq_proposal_time S.E S.hc r]
  have h1 := (facts.sch.slot_instants_l55 S.E (M.opening_slot S.hc r)).2.2.2.2.2
  have h2 := confirmation_time_closed_srs facts S.E (M.opening_slot S.hc r)
  linarith

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation
open Framework.StsMultisetLog
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If slot `s`'s confirmation time is at or before slot `s'`'s, then `s ≤ s'`. -/
theorem slot_le_of_confirmation_time_le (facts : Record.Facts M) (S : Setup V) {s s' : Slot}
    (h : M.confirmation_time S.E s ≤ M.confirmation_time S.E s') : s ≤ s' := by
  have hd := S.E.Δ_pos
  rw [confirmation_time_closed_srs facts, confirmation_time_closed_srs facts] at h
  have h' : 4 * S.E.Δ * (s : Int) ≤ 4 * S.E.Δ * (s' : Int) := by linarith
  have := le_of_mul_le_mul_left h' (by linarith)
  exact_mod_cast this

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation
open Framework.StsMultisetLog
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- The switch round of the confirmation time of round `r`'s third slot is `r`:
    `switchRound S (tc (o_r + 2)) = r`. -/
theorem switchRound_confirmation_third (facts : Record.Facts M) (S : Setup V) (r : Round) :
    Restated.switchRound M S (M.confirmation_time S.E ((M.opening_slot S.hc r) + 2)) = r := by
  refine le_antisymm ?_ (Restated.switchRound_max facts S _ le_rfl)
  by_cases h0 : Restated.switchRound M S (M.confirmation_time S.E ((M.opening_slot S.hc r) + 2)) = 0
  · rw [h0]; exact Nat.zero_le _
  · have hspec := Restated.switchRound_spec facts S _ h0
    have hsl := Restated.slot_le_of_confirmation_time_le facts S hspec
    have hR : 0 < S.hc.R := lt_of_lt_of_le (by decide) S.hc.R_ge_three
    generalize Restated.switchRound M S (M.confirmation_time S.E ((M.opening_slot S.hc r) + 2)) = k
      at hsl ⊢
    rw [opening_slot_closed_srs facts, opening_slot_closed_srs facts] at hsl
    exact Nat.le_of_mul_le_mul_right (Nat.le_of_add_le_add_right hsl) hR

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation
open Framework.StsMultisetLog
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- One period is at most the healing length: `period ≤ healingLengthη S gap`. -/
theorem period_le_healingLengthη (facts : Record.Facts M) (S : Setup V) (gap : Nat) :
    (Restated.constants M S).period ≤ Restated.healingLengthη M S gap := by
  have hper : (0 : Int) < (Restated.constants M S).period := (Restated.constants_holds facts S).period_pos
  have hη : (1 : Int) ≤ (S.hc.η_SG : Int) := by exact_mod_cast S.hc.η_SG_ge_one
  have hb := Restated.healingLength_nonneg facts S gap
  show (Restated.constants M S).period ≤ Restated.healingLength M S gap + (S.hc.η_SG : Int) * (Restated.constants M S).period
  nlinarith

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation
open Framework.StsMultisetLog
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- The times of the settle argument, in order: for a round `c ≥ 2`, with `tE₁ = tc (o_{c − 2} + 2)`
    and `tE' = tc (o_{c − 1} + 2)`, `tE₁ < tE' ≤ S.a c`; the confirmation time of `o_{c − 2} + 1` is
    before the opening of round `c − 1`, which is before `S.a c`; and if
    `tGAT + (healingLengthη + period) ≤ tE₁`, then the opening of round `c − 1` less seven delays
    and `S.a (c − 1) − wAttest` are both at or after `tGAT`, and `tGAT + 8RΔ ≤ tE₁`. -/
theorem settle_instants (facts : Record.Facts M) (S : Setup V) {c : Round} (hc2 : 2 ≤ c) (tGAT : Int) (gap : Nat) :
    M.confirmation_time S.E ((M.opening_slot S.hc (c - 2)) + 2)
        < M.confirmation_time S.E ((M.opening_slot S.hc (c - 1)) + 2) ∧
      M.confirmation_time S.E ((M.opening_slot S.hc (c - 1)) + 2) ≤ (Restated.Vocabulary.Execution.Setup.a M S c) ∧
      M.confirmation_time S.E ((M.opening_slot S.hc (c - 2)) + 1)
        ≤ M.opening S.E S.hc (c - 1) - 1 ∧
      M.opening S.E S.hc (c - 1) < (Restated.Vocabulary.Execution.Setup.a M S c) ∧
      (tGAT + (Restated.healingLengthη M S gap + (Restated.constants M S).period)
          ≤ M.confirmation_time S.E ((M.opening_slot S.hc (c - 2)) + 2) →
        tGAT ≤ M.opening S.E S.hc (c - 1) - 7 * S.E.Δ ∧
        tGAT ≤ (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) - wAttest S ∧
        tGAT + 8 * (S.hc.R : Int) * S.E.Δ
          ≤ M.confirmation_time S.E ((M.opening_slot S.hc (c - 2)) + 2)) := by
  have hd : (1 : Int) ≤ S.E.Δ := S.E.Δ_pos
  have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
  obtain ⟨c₀, rfl⟩ : ∃ c₀, c = c₀ + 2 := ⟨c - 2, (Nat.sub_add_cancel hc2).symm⟩
  have e1 : c₀ + 2 - 2 = c₀ := Nat.add_sub_cancel c₀ 2
  have e2 : c₀ + 2 - 1 = c₀ + 1 := rfl
  rw [e1, e2]
  have hper := Restated.period_eq facts S
  have hηp := Restated.period_le_healingLengthη facts S gap
  rw [hper] at hηp
  simp only [confirmation_time_closed_srs facts, opening_closed_srs facts,
    opening_slot_closed_srs facts, action_closed_srs facts]
  rw [show wAttest S = 4 * (S.hc.R : Int) * S.E.Δ from rfl, hper]
  push_cast
  have hc0 : (0 : Int) ≤ (c₀ : Int) := Int.natCast_nonneg _
  have hRΔ : 12 ≤ 4 * (S.hc.R : Int) * S.E.Δ := by nlinarith
  refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith, ?_⟩
  intro hlen
  refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation
open Framework.StsMultisetLog
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Under `hmono` and `hawake`, if `tGAT ≤ S.a r − wAttest S`, `S.a r ≤ tE` and `v` is not held by
    the adversary at `S.a r`, then `v ∈ HonRound S Sched r`: the window `wAttest S` before `S.a r`
    contains the rule's grade-2 window of round `r`. -/
theorem honRound_of_notAdv_inPhase (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (tGAT tE : Int)
    (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    {r : Round} {v : V} (hlo : tGAT ≤ (Restated.Vocabulary.Execution.Setup.a M S r) - wAttest S) (hhi : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ tE)
    (hv : v ∉ Sched.adv ((Restated.Vocabulary.Execution.Setup.a M S r))) :
    v ∈ Restated.HonRound M S Sched r := by
  have he := facts.gr.early_g2_eq S r
  have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
  have hd := S.E.Δ_pos
  have hW : wAttest S = 4 * (S.hc.R : Int) * S.E.Δ := rfl
  have h : (Restated.Vocabulary.Execution.Setup.a M S r) - wAttest S ≤ M.early S.E S.hc r .g2 - S.E.Δ := by
    show M.a S.hc S.E.Δ r - wAttest S ≤ _
    rw [he, hW]; nlinarith
  exact Finset.mem_sdiff.2
    ⟨mem_awakeThroughout_of_notAdv_inPhase Sched tGAT tE hmono hawake (le_trans hlo h) hhi le_rfl hv, hv⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation
open Framework.StsMultisetLog
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Under the premises of `claimConfirmedAfterHealingStatement` at `tE`, if `2 ≤ c`,
    `tGAT + (healingLengthη S gap + period) ≤ tc (o_{c − 2} + 2)`, `S.a c ≤ tE`, and the opening
    proposers of rounds `c` and `c − 1` are not held by the adversary at their opening slots'
    confirmation times, then `RecordsSettledAtSettleTick S Sched x tE'` holds at
    `tE' = tc (o_{c − 1} + 2)`. -/
theorem recordsSettledAtSettleTick_atStrongRound (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (tGAT tE : Int) (gap : Nat)
    (hgap : gap + 2 ≤ S.cfg.K)
    (hgst : S.E.t_GST ≤ tGAT) (hmono : Sched.MonotoneCorruption)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hsync : Restated.SynchronyFromWake M S x) (hmult : AwakeAtMultiples S Sched)
    (hcatch : Restated.CatchUpOnWake M S x)
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
    {c : Round} (hc2 : 2 ≤ c)
    (hlen₁ : tGAT + (Restated.healingLengthη M S gap + (Restated.constants M S).period)
      ≤ M.confirmation_time S.E ((M.opening_slot S.hc (c - 2)) + 2))
    (hcE : (Restated.Vocabulary.Execution.Setup.a M S c) ≤ tE)
    (hopening : S.E.proposer ((M.opening_slot S.hc c)) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c))))
    (hopeningPrev : S.E.proposer ((M.opening_slot S.hc (c - 1))) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc (c - 1))))) :
    ∀ (r : Round) (n : Nat) (v : V),
      Restated.switchRound M S (M.confirmation_time S.E ((M.opening_slot S.hc (c - 1)) + 2)) + 1 ≤ r →
      Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S r)) →
      v ∉ Sched.adv ((Restated.Vocabulary.Execution.Setup.a M S r)) →
      r = Restated.switchRound M S (M.confirmation_time S.E ((M.opening_slot S.hc (c - 1)) + 2)) + 1 →
      Restated.RecordsAncestorOfHonestHeads M S Sched x v (n + 1) := by
  have hd : (1 : Int) ≤ S.E.Δ := S.E.Δ_pos
  set tE₁ : Int := M.confirmation_time S.E ((M.opening_slot S.hc (c - 2)) + 2) with htE₁
  obtain ⟨h12, h2a, hk₀lo, hopa, hwin⟩ := Restated.settle_instants facts S hc2 tGAT gap
  obtain ⟨hlo7, hloA, hwin8⟩ := hwin hlen₁
  have hsw₁ : Restated.switchRound M S tE₁ = c - 2 := Restated.switchRound_confirmation_third facts S (c - 2)
  have hsw₂ : Restated.switchRound M S (M.confirmation_time S.E ((M.opening_slot S.hc (c - 1)) + 2))
      = c - 1 := Restated.switchRound_confirmation_third facts S (c - 1)
  have hc12 : c - 1 + 1 = c := Nat.sub_add_cancel (le_trans (by decide) hc2)
  have htE₁ : tE₁ ≤ tE := le_trans (le_of_lt h12) (le_trans h2a hcE)
  -- the premises at `tE₁`
  have hthird₁ := third_of_later S Sched tE tE₁ htE₁ hthird
  have hawake₁ := awake_of_later Sched tGAT tE tE₁ htE₁ hawake
  have hrec₁ := Restated.strongOpeningsRecurFrom_of_later facts S Sched tGAT tE tE₁ gap htE₁ hrec
  have hsl₁ := sleepinessW_of_later S Sched tGAT tE tE₁ hmono hawake hwin8 hsl
  have hrs₁ := Restated.roundSleepinessW_of_later facts S Sched tGAT tE tE₁ hmono hawake hwin8 hrs
  have hcs₁ := Restated.committeeSleepinessW_of_later facts S Sched tGAT tE tE₁ hmono hawake hcom hwin8 hcs
  have hlow₁ := Restated.hlow_of_premises_l85f facts S Sched x tGAT tE₁ gap hgap hlen₁ hgst hmono hexec
    hsync hmult hcv htd hcom hthird₁ hawake₁ hrec₁ hsl₁ hrs₁ hcs₁
  have hlen₁' : tGAT + Restated.healingLengthη M S gap ≤ tE₁ := Restated.healingLength_le_of_kit_l76 facts S hlen₁
  have hprev₁ := Restated.basePreviousRoundSGCompatibleWithAnchor_atRound facts S Sched x tGAT tE₁ gap
    hlen₁ hgst hmono hexec hsync hmult hcv hcom hthird₁ hawake₁ hrec₁
  have hclear₁ : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r →
      r ≤ Restated.switchRound M S tE₁ →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round) (n₀ : Nat),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE₁ →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S r)) →
      Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T :=
    fun r hrD' hrW => Restated.baseClearFGSource_atRound_of_premises facts S Sched x tGAT tE₁ gap hgst
      hmono hexec hsync hmult hcv hcom hthird₁ hawake₁ r
      ((Restated.deadlineRoundW_le_rebased facts S tGAT gap).trans hrD') hrW
  have hB'₁ := Restated.baseJustifiedHighAtSwitchRoundW_of_hlow facts S Sched x tGAT tE₁ gap hlow₁
  obtain ⟨n_W, T_W, hnW, hAW, hJswitch, hbase⟩ := Restated.afterPhaseJointSwitchRound_of_premises facts S Sched
    x tGAT tE₁ gap hgap hlen₁ hgst hmono hexec hsync hmult hcatch hcv htd hcom
    hthird₁ hawake₁ hrec₁ hsl₁ hrs₁ hcs₁ hlow₁
  -- the deadline round is well before `c`
  have hc3 : Restated.deadlineRoundW M S tGAT gap + 3 ≤ c := by
    obtain ⟨c₁, hc₁lo, hc₁hi, -, -⟩ := Restated.exists_strongWindow_before_rebasedDeadlineRoundW facts S Sched
      (Restated.runAll M S Sched x (S.E.proposer 0) 0) hgst hlen₁' hrec₁
    have hreb := Restated.rebasedDeadlineRoundW_le_switchRound facts S tGAT tE₁ gap
      (Restated.runAll M S Sched x (S.E.proposer 0) 0) hgst hlen₁'
    rw [hsw₁] at hreb
    exact nat_add_three_le_c7 hc₁lo hc₁hi hreb
  intro r n v _ hn hv hreq
  rw [hsw₂, hc12] at hreq
  subst hreq
  have hvS : v ∉ Sched.adv ((Restated.Vocabulary.Execution.Setup.a M S r)) := hv
  -- the tick step at the opening of round `r − 1`
  have hop0 : 0 < M.opening S.E S.hc (r - 1) := by
    rw [opening_closed_srs facts, opening_slot_closed_srs facts]
    have hr1 : 1 ≤ r - 1 := (nat_sub_one_c7 hc3).1
    have hR : 0 < S.hc.R := lt_of_lt_of_le (by decide) S.hc.R_ge_three
    have : 0 < (r - 1) * S.hc.R := Nat.mul_pos hr1 hR
    have : (0 : Int) < (((r - 1) * S.hc.R : Nat) : Int) := by exact_mod_cast this
    nlinarith
  obtain ⟨k₀, hk₀⟩ := Restated.exists_tickStepAt facts x htd hop0
  have hpos : 0 < (M.opening_slot S.hc (r - 1)) := by
    rw [opening_slot_closed_srs facts]
    exact Nat.mul_pos (nat_sub_one_c7 hc3).1 (lt_of_lt_of_le (by decide) S.hc.R_ge_three)
  have hnew := Restated.stableRoot_new_atStrongRound facts S Sched x hsync hmono hawake hgst hcv hexec hmult
    hthird hcom hrec hc3 hopening hopeningPrev hn hcE hvS hk₀ hpos
  have hconfA : (Restated.Vocabulary.Execution.Setup.a M S r) = M.confirmation_time S.E ((M.opening_slot S.hc r)) :=
    Restated.a_eq_confirmation_opening_l58 facts S r
  rw [hconfA] at hnew
  have hn' : Restated.tickStepAt M x n (M.confirmation_time S.E ((M.opening_slot S.hc r))) := by
    rw [← hconfA]; exact hn
  obtain ⟨hk₀1, hk₀0⟩ := Restated.tickStepAt_time facts x hk₀
  obtain ⟨hn1, hn0⟩ := Restated.tickStepAt_time facts x hn
  have hk₀n : k₀ ≤ n := by
    by_contra hcon
    have h1 := Restated.time_mono_int facts S Sched x (Nat.succ_le_of_lt (Nat.lt_of_not_le hcon))
    rw [hn1] at h1
    linarith
  have hk₀' : M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE₁)) + 1)
      ≤ (x[k₀].time : Int) := by
    rw [hsw₁]; linarith
  have hreader : ∀ s : Slot, (x[k₀].time : Int) < M.confirmation_time S.E s →
      M.confirmation_time S.E s ≤ M.confirmation_time S.E ((M.opening_slot S.hc r)) →
      v ∈ Sched.awakeThroughout (slotStart S.E.Δ s - S.E.Δ) (M.confirmation_time S.E s) ∧
        HonestThroughTime Sched (M.confirmation_time S.E s) v ∧
        v ∈ Restated.HonRound M S Sched ((M.round_of S.hc (s + 1))) := by
    intro s hs0 hs1
    rw [← hconfA] at hs1
    have hsop : M.opening S.E S.hc (r - 1) ≤ M.confirmation_time S.E s := by
      linarith
    have hslo : tGAT ≤ slotStart S.E.Δ s - S.E.Δ := by
      rw [confirmation_time_closed_srs facts] at hsop
      rw [slotStart_closed]
      linarith
    refine ⟨mem_awakeThroughout_of_notAdv_inPhase Sched tGAT tE hmono hawake hslo
        (le_trans hs1 hcE) hs1 hvS,
      fun t ht => fun hadv => hvS (hmono t ((Restated.Vocabulary.Execution.Setup.a M S r)) (le_trans ht hs1) hadv), ?_⟩
    -- the round of `s + 1` is `r − 1` or `r`
    have hsl1 : (M.opening_slot S.hc (r - 1)) ≤ s + 1 := by
      have h := hsop
      rw [opening_closed_srs facts, confirmation_time_closed_srs facts] at h
      have h' : 4 * S.E.Δ * (((M.opening_slot S.hc (r - 1)) : Nat) : Int)
          < 4 * S.E.Δ * ((s : Int) + 2) := by linarith
      have := lt_of_mul_lt_mul_left h' (by linarith)
      have : (((M.opening_slot S.hc (r - 1)) : Nat) : Int) ≤ (s : Int) + 1 := by linarith
      exact_mod_cast this
    have hsl2 : s ≤ (M.opening_slot S.hc r) := by
      have h := hs1
      rw [hconfA] at h
      exact Restated.slot_le_of_confirmation_time_le facts S h
    have hr'lo : r - 1 ≤ (M.round_of S.hc (s + 1)) := by
      by_contra hcon
      have h1 := facts.gr.lt_opening_slot_round_of_succ S.hc (s + 1)
      have h2 := facts.gr.opening_slot_mono S (Nat.succ_le_of_lt (Nat.lt_of_not_le hcon))
      exact nat_lt_le_le_absurd_c7 h1 h2 hsl1
    have hr'hi : (M.round_of S.hc (s + 1)) ≤ r := by
      by_contra hcon
      have h1 := facts.gr.opening_slot_round_of_le_slot S.hc (s + 1)
      have h2 := facts.gr.opening_slot_mono S (Nat.succ_le_of_lt (Nat.lt_of_not_le hcon))
      rw [facts.gr.opening_slot_succ] at h2
      exact nat_round_hi_absurd_c7 h1 h2 hsl2 S.hc.R_ge_three
    have hAr : (Restated.Vocabulary.Execution.Setup.a M S ((M.round_of S.hc (s + 1)))) ≤ (Restated.Vocabulary.Execution.Setup.a M S r) := Restated.action_mono facts S hr'hi
    have hAlo : (Restated.Vocabulary.Execution.Setup.a M S (r - 1)) ≤ (Restated.Vocabulary.Execution.Setup.a M S ((M.round_of S.hc (s + 1)))) := Restated.action_mono facts S hr'lo
    refine Restated.honRound_of_notAdv_inPhase facts S Sched tGAT tE hmono hawake (by linarith)
      (le_trans hAr hcE) (fun hadv => hvS (hmono _ _ hAr hadv))
  -- the grade-2 awake test at every confirmation tick of the window
  have hrun : ∀ s : Slot, (x[k₀].time : Int) < M.confirmation_time S.E s →
      M.confirmation_time S.E s ≤ M.confirmation_time S.E ((M.opening_slot S.hc r)) →
      ∀ m : Nat, Restated.tickStepAt M x m (M.confirmation_time S.E s) →
      M.awake_for_grade2 (Setup.alwaysAwake S) v
        (Record.wakeStage M Sched (M.confirmation_time S.E s) x[m] v) (M.round_of S.hc (s + 1)) := by
    intro s hs0 hs1 m hm
    rw [← hconfA] at hs1
    have hsop : M.opening S.E S.hc (r - 1) ≤ M.confirmation_time S.E s := by
      linarith
    have hsl1 : (M.opening_slot S.hc (r - 1)) ≤ s + 1 := by
      have h := hsop
      rw [opening_closed_srs facts, confirmation_time_closed_srs facts] at h
      have h' : 4 * S.E.Δ * (((M.opening_slot S.hc (r - 1)) : Nat) : Int)
          < 4 * S.E.Δ * ((s : Int) + 2) := by linarith
      have := lt_of_mul_lt_mul_left h' (by linarith)
      have : (((M.opening_slot S.hc (r - 1)) : Nat) : Int) ≤ (s : Int) + 1 := by linarith
      exact_mod_cast this
    have hr'lo : r - 1 ≤ (M.round_of S.hc (s + 1)) := by
      by_contra hcon
      have h1 := facts.gr.lt_opening_slot_round_of_succ S.hc (s + 1)
      have h2 := facts.gr.opening_slot_mono S (Nat.succ_le_of_lt (Nat.lt_of_not_le hcon))
      exact nat_lt_le_le_absurd_c7 h1 h2 hsl1
    have hlo : tGAT ≤ M.early S.E S.hc (M.round_of S.hc (s + 1)) .g2 - S.E.Δ := by
      have he := facts.gr.early_g2_eq S (M.round_of S.hc (s + 1))
      have ha : M.a S.hc S.E.Δ (M.round_of S.hc (s + 1)) =
          4 * S.E.Δ * (S.hc.R : Int) * ((M.round_of S.hc (s + 1) : Nat) : Int) + 6 * S.E.Δ :=
        action_closed_srs facts S (M.round_of S.hc (s + 1))
      have ho := opening_closed_srs facts S (r - 1)
      rw [opening_slot_closed_srs facts] at ho
      have hcast : ((r - 1 : Nat) : Int) ≤ ((M.round_of S.hc (s + 1) : Nat) : Int) := by
        exact_mod_cast hr'lo
      have hRΔ : (0 : Int) ≤ 4 * S.E.Δ * (S.hc.R : Int) := by positivity
      have hmul := mul_le_mul_of_nonneg_left hcast hRΔ
      rw [Nat.cast_mul] at ho
      linarith
    obtain ⟨τ, hl, hτ⟩ := id hm
    rw [← hτ]
    refine facts.ndRun.run_fact_g2_at S Sched x m τ (M.round_of S.hc (s + 1)) v hl ?_ ?_ ?_
    · have h1 := facts.gr.early_g2_le_opening S (M.round_of S.hc (s + 1))
      have h3 := facts.gr.opening_eq_proposal_time S.E S.hc (M.round_of S.hc (s + 1))
      have h4 := facts.sch.proposal_time_mono S.E
        (facts.gr.opening_slot_round_of_le_slot S.hc (s + 1))
      have h5 := facts.sch.proposal_time_succ_lt_confirmation_time S.E s
      rw [hτ]
      linarith
    · rw [hτ]
      exact mem_awakeThroughout_of_notAdv_inPhase Sched tGAT tE hmono hawake hlo
        (le_trans hs1 hcE) hs1 hvS
    · rw [hτ]
      exact fun t ht hadv => hvS (hmono t ((Restated.Vocabulary.Execution.Setup.a M S r))
        (le_trans ht hs1) hadv)
  obtain ⟨hS, hC⟩ := Restated.records_good_of_new_root_window facts S Sched x tE₁ hexec hmono htd hcatch tGAT gap
    hgst hlen₁' hsync hthird₁ hawake₁ hrs₁ hmult hcv hcs₁ hcom hrec₁ hprev₁ hclear₁
    hB'₁ hnW hAW hJswitch (r₀ := Restated.switchRound M S tE₁) le_rfl
    (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _)) hbase hk₀n hk₀' hn'
    hreader hrun hnew
  have hslot : S.E.slotOf (x[n + 1].time : Int) + 2 = (M.opening_slot S.hc r) + 3 := by
    rw [hn1, Restated.slotOf_action facts]
  unfold Restated.RecordsAncestorOfHonestHeads
  rw [hslot]
  exact ⟨hS, hC⟩

end

end DecoupledConsensusModel.Sts.Restated
