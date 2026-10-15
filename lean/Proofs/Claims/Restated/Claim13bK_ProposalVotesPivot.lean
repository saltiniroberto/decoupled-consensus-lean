import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bK_ConeChain
import Proofs.Claims.Restated.Claim13bK_ConfirmedInclusion
import Proofs.Claims.Restated.Claim13bK_ConfirmedRecord
import Proofs.Claims.Restated.Claim13bK_ConfirmedWake
import Proofs.Claims.Restated.Claim13bK_FinBeforeTick
import Proofs.Claims.Restated.Claim13bK_Frame
import Proofs.Claims.Restated.Claim13bK_HeadsPersist
import Proofs.Claims.Restated.Claim13bK_LiveConfirmedSlots
import Proofs.Claims.Restated.Claim13bK_PrevHeadsStep
import Proofs.Claims.Restated.Claim13bStepCone
import Proofs.Claims.Restated.Claim13bStepConeIter
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bW_Schedule
import Proofs.Claims.Restated.Claim13beRoute3_82
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActive
import Model.Conditions.Claim13bInvariantActiveJoint
import Model.Conditions.Claim13bInvariantActiveSinceW
import Model.Conditions.Claim13bK_ConfirmedSettle
import Model.Conditions.Claim13bK_FinBeforeTick
import Model.Conditions.Claim13bK_ProposalVotesPivot
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
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bK_ProposalVotesPivot
import Proofs.Claims.Restated.Claim13bK_PrevHeadsStepRecv

/-!
# Slot instants and the starts of honest walks

Closed forms and orderings of the slot and round instants, and the theorems that the block an honest
proposer's or voter's walk starts from is an ancestor of every honest head of the previous slot,
stated over a model `M : Record.Model V`.
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
local macro "pCW% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13bK_ConfirmedWake)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- A slot's proposal instant in closed form: `proposal_time s = 4Δs`. -/
theorem proposal_time_closed_g1 (facts : Record.Facts M) (S : Setup V) (s : Slot) :
    M.proposal_time S.E s = 4 * S.E.Δ * (s : Int) := by
  have h1 := (facts.sch.slot_instants_l55 S.E s).2.2.2.2.2
  have h2 := facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E s
  rw [slotStart_closed] at h2
  linarith

/-- The opening instant of round `r` is `4 * Δ` times round `r`'s opening slot. -/
private theorem opening_closed_pv (facts : Record.Facts M) (S : Setup V) (r : Round) :
    M.opening S.E S.hc r = 4 * S.E.Δ * (((M.opening_slot S.hc r) : Nat) : Int) := by
  rw [facts.gr.opening_eq_proposal_time S.E S.hc r, Restated.proposal_time_closed_g1 facts S]

/-- A round's action instant is six delays after its opening instant. -/
private theorem action_eq_opening_add_pv (facts : Record.Facts M) (S : Setup V) (r : Round) :
    Restated.Vocabulary.Execution.Setup.a M S r = M.opening S.E S.hc r + 6 * S.E.Δ := by
  have h1 : Restated.Vocabulary.Execution.Setup.a M S r
      = M.confirmation_time S.E (M.opening_slot S.hc r) :=
    facts.sch.a_eq_confirmation_time S.hc S.E r
  have h2 := (facts.sch.slot_instants_l55 S.E (M.opening_slot S.hc r)).2.2.2.2.2
  rw [h1, facts.gr.opening_eq_proposal_time S.E S.hc r]
  exact h2

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- A slot's Goldfish vote instant in closed form: `vote_time s = 4Δs + Δ`. -/
theorem vote_time_closed_g1 (facts : Record.Facts M) (S : Setup V) (s : Slot) :
    M.vote_time S.E s = 4 * S.E.Δ * (s : Int) + S.E.Δ := by
  have h1 := (facts.sch.slot_instants_l55 S.E s).1
  have h2 := Restated.proposal_time_closed_g1 facts S s
  linarith

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If `s ≤ o_{ρ+1} + 1`, then `vote_time s ≤ S.a (ρ + 1) − 1`. -/
theorem vote_time_le_action_sub_one_g1 (facts : Record.Facts M) (S : Setup V) {s : Slot} {ρ : Round}
    (h : s ≤ (M.opening_slot S.hc (ρ + 1)) + 1) :
    M.vote_time S.E s ≤ (Restated.Vocabulary.Execution.Setup.a M S (ρ + 1)) - 1 := by
  have hd := S.E.Δ_pos
  have hI : (s : Int) ≤ (((M.opening_slot S.hc (ρ + 1)) : Nat) : Int) + 1 := by exact_mod_cast h
  have hm : 4 * S.E.Δ * (s : Int) ≤ 4 * S.E.Δ * ((((M.opening_slot S.hc (ρ + 1)) : Nat) : Int) + 1) :=
    mul_le_mul_of_nonneg_left hI (by linarith)
  have hd1 : (1 : Int) ≤ S.E.Δ := hd
  have he : 4 * S.E.Δ * ((((M.opening_slot S.hc (ρ + 1)) : Nat) : Int) + 1)
      = 4 * S.E.Δ * (((M.opening_slot S.hc (ρ + 1)) : Nat) : Int) + 4 * S.E.Δ := by ring
  rw [Restated.vote_time_closed_g1 facts S, action_eq_opening_add_pv facts S,
    opening_closed_pv facts S]
  linarith

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If `o_{ρ+1} ≤ s`, then `S.a ρ < proposal_time s`. -/
theorem action_lt_proposal_time_g1 (facts : Record.Facts M) (S : Setup V) {s : Slot} {ρ : Round}
    (h : (M.opening_slot S.hc (ρ + 1)) ≤ s) :
    (Restated.Vocabulary.Execution.Setup.a M S ρ) < M.proposal_time S.E s := by
  have hd := S.E.Δ_pos
  have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
  have hI : (((M.opening_slot S.hc (ρ + 1)) : Nat) : Int) ≤ (s : Int) := by exact_mod_cast h
  have hm : 4 * S.E.Δ * (((M.opening_slot S.hc (ρ + 1)) : Nat) : Int) ≤ 4 * S.E.Δ * (s : Int) :=
    mul_le_mul_of_nonneg_left hI (by linarith)
  have hsucc := facts.gr.action_succ_eq_add_rounds S ρ
  have h1 := action_eq_opening_add_pv facts S (ρ + 1)
  rw [opening_closed_pv facts S] at h1
  rw [Restated.proposal_time_closed_g1 facts S]
  nlinarith

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If `o_r ≤ s`, then round `r`'s opening instant is at or before `proposal_time s`. -/
theorem opening_le_proposal_time_g1 (facts : Record.Facts M) (S : Setup V) {s : Slot} {r : Round}
    (h : (M.opening_slot S.hc r) ≤ s) :
    M.opening S.E S.hc r ≤ M.proposal_time S.E s := by
  have hd := S.E.Δ_pos
  have hI : (((M.opening_slot S.hc r) : Nat) : Int) ≤ (s : Int) := by exact_mod_cast h
  rw [opening_closed_pv facts S, Restated.proposal_time_closed_g1 facts S]
  exact mul_le_mul_of_nonneg_left hI (by linarith)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- A slot's proposal instant is at or before its vote instant. -/
theorem proposal_time_le_vote_time_g1 (facts : Record.Facts M) (S : Setup V) (s : Slot) :
    M.proposal_time S.E s ≤ M.vote_time S.E s := by
  have hd := S.E.Δ_pos
  rw [Restated.proposal_time_closed_g1 facts S, Restated.vote_time_closed_g1 facts S]
  linarith

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- A slot's vote instant is at or before its confirmation instant. -/
theorem vote_time_le_confirmation_time_g1 (facts : Record.Facts M) (S : Setup V) (s : Slot) :
    M.vote_time S.E s ≤ M.confirmation_time S.E s :=
  facts.sch.Sts_vote_time_le_confirmation_time S s

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Round `r`'s grade-1 domain instant is its opening instant. -/
theorem domain_g1_eq_opening_g1 (facts : Record.Facts M) (S : Setup V) (r : Round) :
    M.domain S.E S.hc r .g1 = M.opening S.E S.hc r :=
  facts.gr.Sts_domain_g1_eq_opening S r

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Round `ρ + 1`'s grade-1 domain instant is at or after `S.a ρ` and before `S.a (ρ + 1)`. -/
theorem action_le_domain_g1_succ_g1 (facts : Record.Facts M) (S : Setup V) (ρ : Round) :
    (Restated.Vocabulary.Execution.Setup.a M S ρ) ≤ M.domain S.E S.hc (ρ + 1) .g1 ∧
      M.domain S.E S.hc (ρ + 1) .g1 < (Restated.Vocabulary.Execution.Setup.a M S (ρ + 1)) := by
  have hd := S.E.Δ_pos
  have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
  have h1 := facts.gr.Sts_domain_g1_eq_opening S (ρ + 1)
  have h2 := action_eq_opening_add_pv facts S (ρ + 1)
  have hsucc := facts.gr.action_succ_eq_add_rounds S ρ
  refine ⟨?_, ?_⟩ <;> nlinarith

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- A slot at or after round `ρ + 1`'s opening slot is in round `ρ + 1` or later. -/
theorem succ_le_round_of_g1 (facts : Record.Facts M) (S : Setup V) {s : Slot} {ρ : Round}
    (h : (M.opening_slot S.hc (ρ + 1)) ≤ s) : ρ + 1 ≤ (M.round_of S.hc s) := by
  by_contra hcon
  have hle : (M.round_of S.hc s) + 1 ≤ ρ + 1 := Nat.lt_of_not_le hcon
  have h1 := facts.gr.lt_opening_slot_round_of_succ S.hc s
  have h2 := facts.gr.opening_slot_mono S hle
  exact absurd (lt_of_lt_of_le (lt_of_lt_of_le h1 h2) h) (lt_irrefl s)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Under the run's premises, if the joint invariant holds at a round `ρ` at or after the switch
    round with an anchor `T` that is `T_W` or a descendant of it, and `t ≤ S.a (ρ + 1) − 1`, then at
    every step whose instant is at most `t` every validator's store records `h_max ≤ h(T) + 1`, and
    at every such step from the switch round's tick step on every validator honest through it holds
    a finalized block and a justified block that are ancestors of `T`. -/
theorem anchorBounds_of_joint (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (hcatch : Restated.CatchUpOnWake M S x)
    (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (hsync : Restated.SynchronyFromWake M S x) (hthird : ∀ t : Int, t ≤ tE →
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
    {ρ : Round} {n : Nat} {T : NamedBlock V}
    (hρ : Restated.switchRound M S tE ≤ ρ) (hTW : Block.Preceq T_W.erase T.erase)
    (hJ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x ρ n n_W T)
    {t : Int} (ht : t ≤ (Restated.Vocabulary.Execution.Setup.a M S (ρ + 1)) - 1) :
    (∀ (v : V) (n₁ : Nat), (x[n₁].time : Int) ≤ t →
        (x[n₁][v].st).st.core.h_max ≤ (M.derive_named S.E S.cfg T).h + 1) ∧
      (∀ (v : V) (n₁ : Nat), n_W ≤ n₁ → (x[n₁].time : Int) ≤ t → Restated.HonestThrough M Sched x n₁ v →
        Block.Preceq (x[n₁][v].st).st.core.F T.erase ∧
          Block.Preceq (x[n₁][v].st).st.core.J T.erase) := by
  obtain ⟨n', hn'⟩ := Restated.tick_field_at_succ facts S Sched x htd ρ
  have hJW := Restated.justified_preceq_anchor_ofJoint facts S Sched x tE hexec hmono htd tGAT gap hgst hlen
    hsync hthird hphase hrsW hmult hcv hcom hrec hprev hclear hB' hnW hAW hρ hTW hJ hn'
  have hcross : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (ρ + 1))) →
      Restated.StepFinalizedCrossingUnderAnchor M S Sched x ρ n'' T :=
    fun n'' h => Restated.stepFinalizedCrossingUnderAnchor_of_afterSwitch facts S Sched x hρ hnW
      hJ.toAfterPhaseInvariantOverActiveSetsSince
      (Restated.justified_preceq_anchor_ofJoint facts S Sched x tE hexec hmono htd tGAT gap hgst hlen hsync
        hthird hphase hrsW hmult hcv hcom hrec hprev hclear hB' hnW hAW hρ hTW hJ h)
  have hfin := Restated.fin_old_anchor_before_succ_tick_of_hypotheses facts (hcross := hcross) S Sched x tE
    hexec hmono tGAT gap hgst hlen hthird hphase hrsW hρ hJ.toAfterPhaseInvariantOverActiveSetsSince.toTop hn'
  have hmax := Restated.hMax_le_anchor_succ_before_succ_tick_of_hypotheses facts S Sched x tE hexec hmono tGAT
    gap hgst hlen hthird hphase hrsW hρ hJ.toAfterPhaseInvariantOverActiveSetsSince.toTop hn'
  refine ⟨fun v n₁ h1 => hmax v n₁ (Restated.le_tick_of_time_lt_action facts S Sched x hn' (le_trans h1 ht)),
    fun v n₁ hW h1 hv => ?_⟩
  have hle := Restated.le_tick_of_time_lt_action facts S Sched x hn' (le_trans h1 ht)
  exact ⟨hfin v n₁ hle hv, hJW v n₁ hW (Nat.le_succ_of_le hle) hv⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Under the run's premises and the joint invariant at the switch round, for every slot `s` at or
    after round `rW + 1`'s opening slot there is a block `T`, `T_W` or a descendant of it, such that
    every honest active member of slot `(s − 1)`'s committee votes for a descendant of `T`; at every
    step whose instant is at or before `s`'s vote instant every validator's store records
    `h_max ≤ h(T) + 1`; and at every such step from the switch round's tick step on every validator
    honest through it holds a finalized block and a justified block that are ancestors of `T`. -/
theorem exists_anchor_atSlot (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (hcatch : Restated.CatchUpOnWake M S x)
    (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (hsync : Restated.SynchronyFromWake M S x) (hthird : ∀ t : Int, t ≤ tE →
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
    {n₀ : Nat} {T₀ : NamedBlock V} (hTW₀ : Block.Preceq T_W.erase T₀.erase)
    (hJ₀ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x (Restated.switchRound M S tE) n₀ n_W T₀)
    {s : Slot} (hslot : (M.opening_slot S.hc (Restated.switchRound M S tE + 1)) ≤ s) :
    ∃ T : NamedBlock V, Block.Preceq T_W.erase T.erase ∧
      Restated.HeadsBelow M S Sched x T.erase (s - 1) ∧
      (∀ (v : V) (n₁ : Nat), (x[n₁].time : Int) ≤ M.vote_time S.E s →
        (x[n₁][v].st).st.core.h_max ≤ (M.derive_named S.E S.cfg T).h + 1) ∧
      (∀ (v : V) (n₁ : Nat), n_W ≤ n₁ → (x[n₁].time : Int) ≤ M.vote_time S.E s →
        Restated.HonestThrough M Sched x n₁ v →
        Block.Preceq (x[n₁][v].st).st.core.F T.erase ∧
          Block.Preceq (x[n₁][v].st).st.core.J T.erase) := by
  have hrecvAll : ∀ r' : Round, Restated.switchRound M S tE ≤ r' → Restated.NextRoundReceipts M S Sched x r' :=
    fun r' hr' => Restated.nextRoundReceipts_of_catchUp facts S Sched x hsync hcatch
      (Restated.gst_le_action_of_switchRound_le facts S tGAT tE gap hgst hlen hr')
  have hR3 := S.hc.R_ge_three
  set r := (M.round_of S.hc s) with hr_def
  have hr : Restated.switchRound M S tE + 1 ≤ r := Restated.succ_le_round_of_g1 facts S hslot
  have hr0 : (M.opening_slot S.hc r) ≤ s := facts.gr.opening_slot_round_of_le_slot S.hc s
  have hr1 : s < (M.opening_slot S.hc (r + 1)) := facts.gr.lt_opening_slot_round_of_succ S.hc s
  have hchain := Restated.exists_anchor_chain_secondSlot_withoutCatchUp_i1 (hrecvAll := hrecvAll) facts S Sched x tE hexec hmono htd
    tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hrec hprev hclear hB' hnW
    hAW hJswitch le_rfl hTW₀ hJ₀
  by_cases hA : (M.opening_slot S.hc r) + 2 ≤ s
  · -- `T` is the round-`r` anchor
    have hle : Restated.switchRound M S tE ≤ r := le_trans (Nat.le_succ _) hr
    obtain ⟨n_k, T_k, hJk, hWk, h2k⟩ := hchain (r - Restated.switchRound M S tE)
    rw [Nat.add_sub_cancel' hle] at hJk h2k
    have hheads : Restated.HeadsBelow M S Sched x T_k.erase (s - 1) := by
      rcases nat_pred_cases_g1 hA with h | h
      · exact Restated.headsBelow_range_ofJoint facts S Sched x tE hexec hmono htd tGAT gap hgst hlen hsync
          hthird hphase hrsW hmult hcv hcs hcom hrec hprev hclear hB' hnW hAW hle hWk hJk
          (s - 1) h (nat_pred_le_g1 hr1)
      · rw [h]
        rcases nat_sub_pos_or_eq_g1 hle with hpos | heq
        · exact h2k hpos
        · exact absurd (heq ▸ hr) (Nat.not_succ_le_self _)
    obtain ⟨hmax, hFJ⟩ := Restated.anchorBounds_of_joint facts S Sched x tE hexec hmono htd hcatch tGAT gap hgst
      hlen hsync hthird hphase hrsW hmult hcv hcs hcom hrec hprev hclear hB' hnW hAW
      hJswitch hle hWk hJk (Restated.vote_time_le_action_sub_one_g1 facts S (nat_le_succ_of_lt_g1 hr1))
    exact ⟨T_k, hWk, hheads, hmax, hFJ⟩
  · -- `s` is `o_r` or `o_r + 1`: `T` is the round-`(r − 1)` anchor
    obtain ⟨ρ, hρ⟩ : ∃ ρ : Round, r = ρ + 1 := ⟨r - 1, (Nat.succ_pred_eq_of_pos
      (lt_of_lt_of_le (Nat.succ_pos _) hr)).symm⟩
    rw [hρ] at hr hr0 hA
    have hle : Restated.switchRound M S tE ≤ ρ := Nat.le_of_succ_le_succ hr
    have hsucc := facts.gr.opening_slot_succ S.hc ρ
    rw [hsucc] at hr0 hA
    obtain ⟨h0, h1, h2⟩ := nat_firstSlots_g1 hR3 hr0 hA
    obtain ⟨n_k, T_k, hJk, hWk, -⟩ := hchain (ρ - Restated.switchRound M S tE)
    rw [Nat.add_sub_cancel' hle] at hJk
    have hheads : Restated.HeadsBelow M S Sched x T_k.erase (s - 1) :=
      Restated.headsBelow_range_ofJoint facts S Sched x tE hexec hmono htd tGAT gap hgst hlen hsync hthird
        hphase hrsW hmult hcv hcs hcom hrec hprev hclear hB' hnW hAW hle hWk hJk (s - 1) h0
        (by rw [hsucc]; exact h1)
    obtain ⟨hmax, hFJ⟩ := Restated.anchorBounds_of_joint facts S Sched x tE hexec hmono htd hcatch tGAT gap hgst
      hlen hsync hthird hphase hrsW hmult hcv hcs hcom hrec hprev hclear hB' hnW hAW
      hJswitch hle hWk hJk (Restated.vote_time_le_action_sub_one_g1 facts S (s := s) (by rw [hsucc]; exact h2))
    exact ⟨T_k, hWk, hheads, hmax, hFJ⟩

end

-- Folded in from the former module `Claim13bK_ProposalVotesPivotRecv.lean` (wake switch, lane S).
/-!
# Graded blocks are ancestors of the heads from the previous round, at a reader awake from t₀

`graded_headsBelow_fromPrevRound` of `Claim13bK_ProposalVotesPivot.lean` with the grade-1 reader
awake from some `t₀` at or before round `r`'s grade-1 late cutoff less `2 * Δ + 1` in place of
`S.a (r − 1)`, and its receipt of round `r − 1`'s honest attestations before round `r`'s grade-1
first cutoff.
-/


section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Under the run's premises and the joint invariant at the switch round, for a round `r` after the
    switch round: if `v` is awake from `t₀` to round `r`'s opening instant, with `t₀` at or before round
    `r`'s grade-1 late cutoff less `2 * Δ + 1`, receives round `r − 1`'s honest attestations before
    round `r`'s grade-1 first cutoff, is honest through that opening, and its store at the last step before round `r`'s grade-1 domain instant grades
    `C` at least 1 for round `r`, then every honest active member of the committee of every slot
    from `o_{r−1} + 2` on votes there for a descendant of `C`. -/
theorem graded_headsBelow_fromPrevRound_recv (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (hcatch : Restated.CatchUpOnWake M S x)
    (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (hsync : Restated.SynchronyFromWake M S x) (hthird : ∀ t : Int, t ≤ tE →
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
    {n₀ : Nat} {T₀ : NamedBlock V} (hTW₀ : Block.Preceq T_W.erase T₀.erase)
    (hJ₀ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x (Restated.switchRound M S tE) n₀ n_W T₀)
    {r : Round} (hr : Restated.switchRound M S tE + 1 ≤ r) {v : V}
    (t₀ : Int) (ht₀ : t₀ ≤ M.late S.E S.hc r .g1 - 1 - 2 * S.E.Δ)
    (hvaw : v ∈ Sched.awakeThroughout t₀ (M.opening S.E S.hc r))
    (hrecv : Restated.ReceivesRoundAttestationsBefore M S Sched x (r - 1) v (M.early S.E S.hc r .g1))
    (hvh : HonestThroughTime Sched (M.opening S.E S.hc r) v)
    {m : Nat} (hm : Restated.stepBeforeInstant M x m (M.domain S.E S.hc r .g1)) {C : Block V}
    (hC : M.gradeBool S.E (M.gradeView (M.toHealing (x[m][v].st).st.core))
      (x[m][v].st).st.core.F S.hc.η_SG r (M.early S.E S.hc r .g1)
      (M.late S.E S.hc r .g1) C ⇢ true)
    {s' : Slot} (hs' : (M.opening_slot S.hc (r - 1)) + 2 ≤ s') :
    Restated.HeadsBelow M S Sched x C s' := by
  have hrecvAll : ∀ r' : Round, Restated.switchRound M S tE ≤ r' → Restated.NextRoundReceipts M S Sched x r' :=
    fun r' hr' => Restated.nextRoundReceipts_of_catchUp facts S Sched x hsync hcatch
      (Restated.gst_le_action_of_switchRound_le facts S tGAT tE gap hgst hlen hr')
  have hW0 : 0 < Restated.switchRound M S tE := Restated.round_pos_of_switch facts S tGAT tE gap hgst hlen le_rfl
  obtain ⟨r₂, rfl⟩ : ∃ r₂ : Round, r = r₂ + 1 + 1 := nat_exists_add_two_g1 hW0 hr
  have e1 : r₂ + 1 + 1 - 1 = r₂ + 1 := rfl
  rw [e1] at hs' hrecv
  have hr1 : Restated.switchRound M S tE ≤ r₂ + 1 := Nat.le_of_succ_le_succ hr
  obtain ⟨n₁, T₁, hJ₁, -, hTW₁⟩ := Restated.anchor_at_later_round facts S Sched x tE hexec hmono htd hcatch
    tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hrec hprev hclear hB'
    hnW hAW hJswitch le_rfl hTW₀ hJ₀ hr1
  have hcross : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r₂ + 1 + 1))) →
      Restated.StepFinalizedCrossingUnderAnchor M S Sched x (r₂ + 1) n'' T₁ :=
    fun n'' h => Restated.stepFinalizedCrossingUnderAnchor_of_afterSwitch facts S Sched x hr1 hnW
      hJ₁.toAfterPhaseInvariantOverActiveSetsSince
      (Restated.justified_preceq_anchor_ofJoint facts S Sched x tE hexec hmono htd tGAT gap hgst hlen hsync
        hthird hphase hrsW hmult hcv hcom hrec hprev hclear hB' hnW hAW hr1 hTW₁ hJ₁ h)
  have hdomeq : M.domain S.E S.hc (r₂ + 1 + 1) .g1
      = M.opening S.E S.hc (r₂ + 1 + 1) := facts.gr.Sts_domain_g1_eq_opening S (r₂ + 1 + 1)
  have hdom : M.domain S.E S.hc (r₂ + 1 + 1) .g1 ≤ (Restated.Vocabulary.Execution.Setup.a M S (r₂ + 1 + 1)) :=
    facts.gr.domain_le_action S _ _
  have hawT : v ∈ Sched.awakeThroughout t₀ (M.domain S.E S.hc (r₂ + 1 + 1) .g1) := by
    rw [hdomeq]; exact hvaw
  have hvS : v ∉ Sched.adv (M.domain S.E S.hc (r₂ + 1 + 1) .g1) :=
    hvh _ (le_of_eq hdomeq)
  obtain ⟨v_1, hv_1, a, har, hai, has, C', hC', hac, hCC'⟩ :=
    Restated.graded_preceq_freshSG_at_awakeReader_recv facts (hcross := hcross) S Sched x tE hexec hmono htd hsync
      hmult tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr1
      hJ₁.toAfterPhaseInvariantOverActiveSetsSince.toTop hdom t₀ ht₀ hawT hrecv hvS hm C hC
  obtain ⟨n', hn'⟩ := Restated.tick_field_at_succ facts S Sched x htd (r₂ + 1)
  have hJT := Restated.justified_fromSecondSlot_ofJoint facts S Sched x tE hexec hmono htd tGAT gap hgst hlen
    hsync hthird hphase hrsW hmult hcv hcom hrec hprev hclear hB' hnW hAW hJswitch hr1 hTW₁ hJ₁ hn'
  obtain ⟨n_prev, hnp0⟩ := hJ₁.prevTick
  have hnp : Restated.tickStepAt M x n_prev ((Restated.Vocabulary.Execution.Setup.a M S r₂)) := hnp0
  rcases Restated.roundSG_preceq_anchor_or_headsBelow (hrecvR := Restated.nextRoundReceipts_of_catchUp facts S Sched x hsync hcatch
        (Restated.gst_le_action_of_switchRound_le facts S tGAT tE gap hgst hlen
          (by first | assumption | exact le_trans hr (Nat.le_succ _) | exact le_trans hr (Nat.le_add_right _ _) | exact Nat.le_succ_of_le hr | omega))) facts S Sched x tE hexec hmono htd hsync hmult hcom tGAT
      gap hgst hlen hcv hthird hphase hrsW hcs (r := r₂) hr1 hJ₁ hn' hcross hJT hnp v_1 hv_1
      a har hai has C' hC' hac with hCT | hheads
  · have hanc := Restated.anchor_ancestorOfHonestHeadsFrom facts S Sched x tE hexec hmono htd hcatch tGAT gap
      hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hrec hprev hclear hB' hnW hAW
      hJswitch hr1 hTW₁ hJ₁
    exact Restated.headsBelow_mono facts S Sched x (preceq_trans_Preceq hCC' hCT) (hanc s' hs')
  · have hR3 := S.hc.R_ge_three
    have hsucc := facts.gr.opening_slot_succ S.hc (r₂ + 1)
    have h2 : Restated.HeadsBelow M S Sched x C'.erase ((M.opening_slot S.hc (r₂ + 1)) + 2) :=
      hheads _ (Nat.le_succ _) (by rw [hsucc]; exact nat_add_two_le_add_succ_g1 hR3)
    have hmono' := facts.gr.opening_slot_mono S hr1
    have hA := Restated.ancestorOfHonestHeadsFrom_of_headsBelow_i1 (hrecvAll := hrecvAll) facts S Sched x tE hexec hmono htd tGAT gap
      hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hrec hprev hclear hB' hnW hAW
      hJswitch le_rfl hTW₀ hJ₀ (s := (M.opening_slot S.hc (r₂ + 1)) + 2) (Nat.add_le_add_right hmono' 2) h2
    exact Restated.headsBelow_mono facts S Sched x hCC' (hA s' hs')

end


section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Under the run's premises and the joint invariant at the switch round, for a slot `s` at or after
    round `rW + 1`'s opening slot, an instant `t` from `s`'s proposal instant to its vote instant,
    and a validator `v` awake at `t` and honest through `t`: for every outcome of the cache update
    at `t` on `v`'s cache, every block the walk's start can return under that cache's grade
    contract, on `v`'s store stamped with `t` and for the round of `s`, is an ancestor of the head
    every honest active member of slot `(s − 1)`'s committee votes for. -/
theorem readStart_headsBelow (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (hcatch : Restated.CatchUpOnWake M S x)
    (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (hsync : Restated.SynchronyFromWake M S x) (hthird : ∀ t : Int, t ≤ tE →
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
    {n₀ : Nat} {T₀ : NamedBlock V} (hTW₀ : Block.Preceq T_W.erase T₀.erase)
    (hJ₀ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x (Restated.switchRound M S tE) n₀ n_W T₀)
    {s : Slot} (hslot : (M.opening_slot S.hc (Restated.switchRound M S tE + 1)) ≤ s)
    {t : Int} (ht0 : M.proposal_time S.E s ≤ t) (ht1 : t ≤ M.vote_time S.E s)
    {k : Nat} (hk : Restated.tickStepAt M x k t) {v : V} (haw : v ∈ Sched.awake t)
    (hvh : HonestThroughTime Sched t v)
    (hwin : v ∈ Sched.awakeThroughout (M.early S.E S.hc (M.round_of S.hc s) .g1 - S.E.Δ) t) :
    ∀ c : M.Cache,
      M.onPhaseTick S.E S.hc (M.toHealing (x[k][v].st).st.core) t (x[k][v].st).cache ⇢ c →
    ∀ A : Block V,
      M.get_sg_root_with (M.gradeContract c) S.E S.hc
        (M.toHealing (M.ns_setClock S.E (x[k][v].st).st t).core) (M.round_of S.hc s) ⇢ A →
      Restated.HeadsBelow M S Sched x A (s - 1) := by
  intro c hc A hA
  have hR3 := S.hc.R_ge_three
  obtain ⟨hk1, hk0⟩ := Restated.tickStepAt_time facts x hk
  rw [facts.nd.gradeContract_sgRoot_eq_frameAnchor] at hA
  rcases facts.gr.Sts_anchor_cases S _ _ _ A hA with hfg | ⟨root, hroot, hpre⟩
  · -- the fork-choice root
    rw [hfg]
    obtain ⟨T, -, hH, -, hFJ⟩ := Restated.exists_anchor_atSlot facts S Sched x tE hexec hmono htd hcatch tGAT gap
      hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hrec hprev hclear hB' hnW hAW
      hJswitch hTW₀ hJ₀ hslot
    have hlt : (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)) < t :=
      lt_of_lt_of_le (Restated.action_lt_proposal_time_g1 facts S hslot) ht0
    have hWk : n_W ≤ k := by
      by_contra hcon
      have hle : k + 1 ≤ n_W := Nat.lt_of_not_le hcon
      have h1 := Restated.time_mono_int facts S Sched x hle
      have h2 := (Restated.tickStepAt_time facts x hnW).2
      linarith
    have hvk : Restated.HonestThrough M Sched x k v := fun t' ht' => hvh t' (by linarith)
    obtain ⟨hF, hJ⟩ := hFJ v k hWk (by linarith) hvk
    have hroot : Block.Preceq
        (M.get_fg_root
          (M.toHealing (M.ns_setClock S.E (x[k][v].st).st t).core).toFG) T.erase := by
      refine facts.fc.fgRoot_preceq ?_ ?_
      · rw [facts.hd.setClock_toHealing_F]; exact hF
      · rw [facts.hd.setClock_toHealing_J]; exact hJ
    exact Restated.headsBelow_mono facts S Sched x hroot hH
  · -- an ancestor of a grade-1 root of the frame
    obtain ⟨root₀, hc0', hroot0⟩ := facts.gr.readFrame_g1_provenance _ _ _ hroot
    obtain ⟨m, B, hm, hB, hroot0B⟩ :=
      Restated.framePhaseProvenance_onPhaseTick facts S hk
        (Restated.framePhaseProvenance_sts facts S Sched x v k) c hc _ .g1 root₀ hc0'
    have hawD : v ∈ Sched.awake (M.domain S.E S.hc ((M.round_of S.hc s)) .g1) :=
      Restated.framePhaseAwakeProvenance_onPhaseTick facts S Sched _ _ haw
        (Restated.framePhaseAwakeProvenance_sts facts S Sched x v k) c hc _ .g1 root₀ hc0'
    have hr : Restated.switchRound M S tE + 1 ≤ (M.round_of S.hc s) := Restated.succ_le_round_of_g1 facts S hslot
    obtain ⟨ρ, hρ⟩ : ∃ ρ : Round, (M.round_of S.hc s) = ρ + 1 := ⟨(M.round_of S.hc s) - 1,
      (Nat.succ_pred_eq_of_pos (lt_of_lt_of_le (Nat.succ_pos _) hr)).symm⟩
    rw [hρ] at hawD hm hB hr hwin
    have hr0 : (M.opening_slot S.hc (ρ + 1)) ≤ s := by
      rw [← hρ]; exact facts.gr.opening_slot_round_of_le_slot S.hc s
    have hopt : M.opening S.E S.hc (ρ + 1) ≤ t :=
      le_trans (Restated.opening_le_proposal_time_g1 facts S hr0) ht0
    have hd1 : (1 : Int) ≤ S.E.Δ := S.E.Δ_pos
    have hl0 := facts.gr.early_le_late S.E S.hc (ρ + 1) .g0
    have hl1 := facts.gr.late_g0_add_delta_le_late_g1 S (ρ + 1)
    have he0 := facts.gr.early_g1_add_delta_le_early_g0 S (ρ + 1)
    have hed := facts.gr.early_g1_le_domain_g1 S (ρ + 1)
    have hdo := facts.gr.Sts_domain_g1_eq_opening S (ρ + 1)
    have hlo := facts.gr.action_delta_le_early S S.hc.R_ge_three (Nat.lt_succ_self ρ)
    have h21 := facts.gr.early_g2_add_delta_le_early_g1 S (ρ + 1)
    have hrρ : Restated.switchRound M S tE ≤ ρ := Nat.le_of_succ_le_succ hr
    have hgstρ := Restated.gst_le_action_of_switchRound_le facts S tGAT tE gap hgst hlen hrρ
    have haρ : Restated.Vocabulary.Execution.Setup.a M S ρ ≤ M.early S.E S.hc (ρ + 1) .g1 - S.E.Δ := by
      show M.a S.hc S.E.Δ ρ ≤ _
      linarith
    have hvaw : v ∈ Sched.awakeThroughout (M.early S.E S.hc (ρ + 1) .g1 - S.E.Δ)
        (M.opening S.E S.hc (ρ + 1)) :=
      awakeThroughout_mono Sched hwin le_rfl hopt
    have hrecv : Restated.ReceivesRoundAttestationsBefore M S Sched x (ρ + 1 - 1) v
        (M.early S.E S.hc (ρ + 1) .g1) := by
      rw [Nat.add_sub_cancel]
      have h := Restated.receivesRoundAttestationsBefore_of_awakeFrom facts S Sched x hsync hcatch
        (r := ρ) (t₀ := M.early S.E S.hc (ρ + 1) .g1 - S.E.Δ) haρ (le_trans hgstρ haρ)
        (awakeThroughout_mono Sched hwin le_rfl (by linarith))
      have e : M.early S.E S.hc (ρ + 1) .g1 - S.E.Δ + S.E.Δ = M.early S.E S.hc (ρ + 1) .g1 := by ring
      rw [e] at h
      exact h
    have hvh' : HonestThroughTime Sched (M.opening S.E S.hc (ρ + 1)) v :=
      fun t' ht' => hvh t' (le_trans ht' (le_trans (Restated.opening_le_proposal_time_g1 facts S hr0) ht0))
    have hs' : (M.opening_slot S.hc (ρ + 1 - 1)) + 2 ≤ s - 1 := by
      rw [Nat.add_sub_cancel]
      rw [facts.gr.opening_slot_succ] at hr0
      exact nat_prev_round_third_le_pred_g1 hR3 hr0
    -- one outcome of the grade test of `B`: it is `true`
    obtain ⟨b, hb⟩ := facts.gr.gradeBool_nonempty S.E (M.gradeView (M.toHealing (x[m][v].st).st.core))
      (x[m][v].st).st.core.F S.hc.η_SG (ρ + 1) (M.early S.E S.hc (ρ + 1) .g1)
      (M.late S.E S.hc (ρ + 1) .g1) B
    obtain rfl := hB b hb
    have hHB := Restated.graded_headsBelow_fromPrevRound_recv facts S Sched x tE hexec hmono htd hcatch tGAT gap hgst
      hlen hsync hthird hphase hrsW hmult hcv hcs hcom hrec hprev hclear hB' hnW hAW
      hJswitch hTW₀ hJ₀ hr _ (by linarith) hvaw hrecv hvh' hm hb hs'
    exact Restated.headsBelow_mono facts S Sched x
      (preceq_trans_Preceq hpre (preceq_trans_Preceq hroot0 hroot0B)) hHB

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Under the run's premises and the joint invariant at the switch round, for a slot `s` at or after
    round `rW + 1`'s opening slot whose proposer is honest through `s`'s vote instant and awake at
    `s`'s proposal instant: for every node state of the proposer's proposal read, every block the
    walk's start can return under that state's grade contract, for the round of `s`, is an ancestor
    of the head every honest active member of slot `(s − 1)`'s committee votes for. -/
theorem proposalStart_headsBelow (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (hcatch : Restated.CatchUpOnWake M S x)
    (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (hsync : Restated.SynchronyFromWake M S x) (hthird : ∀ t : Int, t ≤ tE →
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
    {n₀ : Nat} {T₀ : NamedBlock V} (hTW₀ : Block.Preceq T_W.erase T₀.erase)
    (hJ₀ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x (Restated.switchRound M S tE) n₀ n_W T₀)
    {s : Slot} (hslot : (M.opening_slot S.hc (Restated.switchRound M S tE + 1)) ≤ s)
    (hprop : HonestThroughTime Sched (M.vote_time S.E s) (S.E.proposer s))
    (haw : S.E.proposer s ∈ Sched.awake (M.proposal_time S.E s))
    (hwin : S.E.proposer s ∈ Sched.awakeThroughout (M.early S.E S.hc (M.round_of S.hc s) .g1 - S.E.Δ)
      (M.proposal_time S.E s))
    {k : Nat} (hk : Restated.tickStepAt M x k (M.proposal_time S.E s)) :
    ∀ n : M.N, Restated.proposalReadOf M S (x[k][S.E.proposer s].st) s ⇢ n →
    ∀ A : Block V,
      M.get_sg_root_with (M.gradeContract n.cache) S.E S.hc
        (M.toHealing (Restated.proposalStoreAt M S (x[k][S.E.proposer s].st) s))
        (M.round_of S.hc s) ⇢ A →
      Restated.HeadsBelow M S Sched x A (s - 1) := by
  intro n hn A hA
  obtain ⟨c, hc, rfl⟩ := (pCW% returns_map_elim_cw) _ _ n hn
  rw [facts.nd.mkNode_cache] at hA
  exact Restated.readStart_headsBelow facts S Sched x tE hexec hmono htd hcatch tGAT gap hgst hlen hsync hthird
    hphase hrsW hmult hcv hcs hcom hrec hprev hclear hB' hnW hAW hJswitch hTW₀ hJ₀ hslot le_rfl
    (Restated.proposal_time_le_vote_time_g1 facts S s) hk haw
    (fun t' ht' => hprop t' (le_trans ht' (Restated.proposal_time_le_vote_time_g1 facts S s)))
    hwin c hc A hA

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Under the run's premises and the joint invariant at the switch round, for a slot `s` at or after
    round `rW + 1`'s opening slot and a member `v` of `HonSlot S Sched s`: for every node state of
    `v`'s slot-`s` vote read, every block `v`'s vote walk can start from under that state's grade
    contract is an ancestor of the head every honest active member of slot `(s − 1)`'s committee
    votes for. -/
theorem voteStart_headsBelow (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (hcatch : Restated.CatchUpOnWake M S x)
    (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (hsync : Restated.SynchronyFromWake M S x) (hthird : ∀ t : Int, t ≤ tE →
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
    {n₀ : Nat} {T₀ : NamedBlock V} (hTW₀ : Block.Preceq T_W.erase T₀.erase)
    (hJ₀ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x (Restated.switchRound M S tE) n₀ n_W T₀)
    {s : Slot} (hslot : (M.opening_slot S.hc (Restated.switchRound M S tE + 1)) ≤ s)
    {v : V} (hv : v ∈ Restated.HonSlot M S Sched s)
    {mr : Nat} (hmr : Restated.tickStepAt M x mr (M.vote_time S.E s)) :
    ∀ n : M.N, Restated.voteReadOf M S (x[mr][v].st) s ⇢ n →
    ∀ A : Block V,
      Restated.voteAnchorOf M (M.gradeContract n.cache) S.E S.hc
        (Restated.voteStoreAt M S (x[mr][v].st) s) ⇢ A →
      Restated.HeadsBelow M S Sched x A (s - 1) := by
  intro n hn A hA
  obtain ⟨c, hc, rfl⟩ := (pCW% returns_map_elim_cw) _ _ n hn
  rw [facts.nd.mkNode_cache, Restated.voteAnchorOf, Restated.voteStoreAt_slot facts] at hA
  exact Restated.readStart_headsBelow facts S Sched x tE hexec hmono htd hcatch tGAT gap hgst hlen hsync hthird
    hphase hrsW hmult hcv hcs hcom hrec hprev hclear hB' hnW hAW hJswitch hTW₀ hJ₀ hslot
    (Restated.proposal_time_le_vote_time_g1 facts S s) le_rfl hmr (Restated.awake_of_mem_HonSlot facts S Sched s hv)
    (fun t' ht' hin => ((Restated.mem_HonSlot facts).mp hv).2.2
      (hmono t' _ (le_trans ht' (Restated.vote_time_le_confirmation_time_g1 facts S s)) hin))
    (Restated.awakeThroughout_early_g1_of_mem_HonSlot facts S Sched hv)
    c hc A hA

end

end DecoupledConsensusModel.Sts.Restated
