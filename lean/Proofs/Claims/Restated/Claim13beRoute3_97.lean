import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bInvariantActiveSinceW
import Proofs.Claims.Restated.Claim13bK_FinalityStepWindow
import Proofs.Claims.Restated.Claim13bK_HjMono
import Proofs.Claims.Restated.Claim13bK_ProposalAdoption
import Proofs.Claims.Restated.Claim13bSGCompatible
import Proofs.Claims.Restated.Claim13beRoute3_76
import Proofs.Claims.Restated.Claim13beRoute3_83
import Proofs.Claims.Restated.Claim13beRoute3_85d
import Proofs.Claims.Restated.Claim13beRoute3_88
import Proofs.Claims.Restated.Claim13beRoute3_93
import Proofs.Claims.Restated.Claim13beRoute3_94
import Proofs.Claims.Restated.Claim13beRoute3_95
import Proofs.Claims.Restated.Claim13beRoute3_96
import Proofs.Claims.Restated.Vocabulary_Protocol_ChainState_ProposalBridge
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActiveJoint
import Model.Conditions.Claim13bInvariantActiveSinceW
import Model.Conditions.Claim13bK_ConfirmedSettle
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_72
import Model.Conditions.Claim13beRoute3_74
import Model.Conditions.Claim13beRoute3_83
import Model.Conditions.Claim13beRoute3_97
import Model.Conditions.RunAll
import Model.Conditions.RunVocabulary
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13bd
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Sts_Spec2Claims_ClaimFinalityLiveAfterHealing
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Statements_Instantiation_Proposals
import Model.Record.Wiring
import Proofs.Claims.Restated.Claim13bK_ConfirmedRecord
import Proofs.Claims.Spec2Claims.Claim13beRoute3_97

/-!
# Finality of an honest proposal at the sharp spacing

Theorems over a model `M : Record.Model V` about the run of the first `N` steps of an execution `x`,
read along the path it follows: the deadline places the switch round, the first window and the
window after a timeout at the sharp spacing, and an honest proposal is finalized.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

/-- Refers to a private theorem of `Proofs.Claims.Restated.Claim13bK_ConfirmedRecord` by name. -/
local macro "pCR% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13bK_ConfirmedRecord)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- Refers to a private theorem of `Proofs.Claims.Restated.Claim13beRoute3_58` by name. -/
local macro "p58% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_58)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- Refers to a private theorem of `Proofs.Claims.Restated.Claim13beRoute3_71` by name. -/
local macro "p71% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_71)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- Refers to a private theorem of `Proofs.Claims.Restated.Claim13beRoute3_83` by name. -/
local macro "p83% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_83)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- Refers to a private theorem of `Proofs.Claims.Restated.Claim13beRoute3_85f` by name. -/
local macro "p85f% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_85f)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Framework.StsMultisetLog

/-- If `proposal_time s + finalityDeadlineSharpLanded_f7 S gap ≤ tL`, then
    `s / R + (3 · gap + tD / R − 5) ≤ switchRound S tL`. -/
theorem switchRound_ge_of_deadline_f7 (facts : Record.Facts M) (S : Setup V) {s : Slot} {tL : Int} {gap : Nat}
    (hdead : M.proposal_time S.E s + Restated.finalityDeadlineSharpLanded_f7 M S gap ≤ tL) :
    s / S.hc.R + (3 * gap + S.cfg.timeoutDelay / S.hc.R - 5) ≤ Restated.switchRound M S tL := by
  apply Restated.switchRound_max facts
  have hslot : (M.opening_slot S.hc (s / S.hc.R)) ≤ s := by
    rw [(pCR% opening_slot_closed_cr) facts]; exact Nat.div_mul_le_self s S.hc.R
  have hp := facts.sch.proposal_time_mono S.E hslot
  rw [Restated.proposal_time_opening_eq_l85d facts] at hp
  have hD : Restated.finalityDeadlineSharpLanded_f7 M S gap =
      ((3 * gap + S.cfg.timeoutDelay / S.hc.R - 5 : Nat) : Int) * (Restated.constants M S).period +
        14 * S.E.Δ := rfl
  rw [hD, Restated.period_eq facts S] at hdead
  rw [(pCR% confirmation_time_closed_cr) facts, (pCR% opening_slot_closed_cr) facts]
  push_cast at hdead hp ⊢
  nlinarith

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Framework.StsMultisetLog

/-- If `t_GST ≤ tGAT`, `tGAT + healingLengthη S gap ≤ tL`, `strongOpeningsRecurFrom` holds from
    `tGAT` to `tL`, `deadlineRoundW S tGAT gap + 2 ≤ w ≤ r₀ ≤ s / R` and
    `proposal_time s + finalityDeadlineSharpLanded_f7 S gap ≤ tL`, then some round `c₁` with
    `s / R + 2 ≤ c₁` and `c₁ + 2 ≤ s / R + 1 + gap` has the proposers of `o_{c₁}`, `o_{c₁} + 1`,
    `o_{c₁} + 2`, `o_{c₁ − 1}` and `o_{c₁ − 2}` each not held at its own slot's confirmation
    instant. -/
theorem firstWindowSharp_f7 (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    {tGAT tL : Int} {gap : Nat}
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tL gap)
    (hgst : S.E.t_GST ≤ tGAT) (hlen' : tGAT + Restated.healingLengthη M S gap ≤ tL)
    {w r₀ : Round} (h1 : Restated.deadlineRoundW M S tGAT gap + 2 ≤ w) (h2 : w ≤ r₀) {s : Slot}
    (h3 : r₀ ≤ s / S.hc.R)
    (hdead : M.proposal_time S.E s + Restated.finalityDeadlineSharpLanded_f7 M S gap ≤ tL) :
    ∃ c₁ : Round, s / S.hc.R + 1 + 1 ≤ c₁ ∧ c₁ + 2 ≤ s / S.hc.R + 1 + gap ∧
      (∀ k < 3, S.E.proposer ((M.opening_slot S.hc c₁) + k) ∈
        notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c₁) + k))) ∧
      S.E.proposer ((M.opening_slot S.hc (c₁ - 1))) ∈
        notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc (c₁ - 1)))) ∧
      S.E.proposer ((M.opening_slot S.hc (c₁ - 2))) ∈
        notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc (c₁ - 2)))) := by
  have hRpos : 0 < S.hc.R := lt_of_lt_of_le (by decide) S.hc.R_ge_three
  have hm2 : 2 ≤ S.cfg.timeoutDelay / S.hc.R :=
    (Nat.le_div_iff_mul_le hRpos).mpr (by simpa only [Nat.mul_comm] using S.timeout_rounds.2)
  have hWs := Restated.switchRound_ge_of_deadline_f7 facts S hdead
  obtain ⟨hd, hW1, hcast, hgk⟩ := nat_firstSharp_f7 (Restated.deadlineRoundW M S tGAT gap) w r₀
    (s / S.hc.R) gap (S.cfg.timeoutDelay / S.hc.R) (Restated.switchRound M S tL) h1 h2 h3 hWs hm2
  obtain ⟨hlo0, -⟩ := Restated.window_in_phase_atRound facts S tGAT tL gap hgst hlen' hd hW1
  have hwa : wAttest S = 4 * (S.hc.R : Int) * S.E.Δ := rfl
  rw [Restated.action_eq_l85d facts, hwa, hcast] at hlo0
  have hslot : (M.opening_slot S.hc (s / S.hc.R)) ≤ s := by
    rw [(pCR% opening_slot_closed_cr) facts]; exact Nat.div_mul_le_self s S.hc.R
  have hp := facts.sch.proposal_time_mono S.E hslot
  rw [Restated.proposal_time_opening_eq_l85d facts] at hp
  have hD : Restated.finalityDeadlineSharpLanded_f7 M S gap =
      ((3 * gap + S.cfg.timeoutDelay / S.hc.R - 5 : Nat) : Int) * (Restated.constants M S).period +
        14 * S.E.Δ := rfl
  rw [hD] at hdead
  have hΔ : (1 : Int) ≤ S.E.Δ := S.E.Δ_pos
  have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
  have hper : (Restated.constants M S).period = 4 * S.E.Δ * (S.hc.R : Int) := Restated.period_eq facts S
  have hP : (12 : Int) ≤ 4 * S.E.Δ * (S.hc.R : Int) := by nlinarith
  have hgkP : ((gap : Int) - 1) * (4 * S.E.Δ * (S.hc.R : Int)) ≤
      ((3 * gap + S.cfg.timeoutDelay / S.hc.R - 5 : Nat) : Int) * (4 * S.E.Δ * (S.hc.R : Int)) :=
    mul_le_mul_of_nonneg_right hgk (by linarith)
  have hcast2 : (((s / S.hc.R + 1 : Nat) : Int)) = ((s / S.hc.R : Nat) : Int) + 1 := by
    push_cast; ring
  obtain ⟨c₁, hlo, hhi, hw⟩ := Restated.strongWindow_sharp_f7 facts S Sched hrec (a := s / S.hc.R + 1)
    (by rw [hper]; nlinarith) (by rw [hper, hcast2]; rw [hper] at hdead; nlinarith)
  exact ⟨c₁, hlo, hhi, hw⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Framework.StsMultisetLog
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- In an execution in which every tick has an outcome, along the path
    `W = Restated.runAllPath M S Sched x v₀ N`, if `P` is a proposal of `o_{c₁}` with `nj(P)` set,
    `3 ≤ gap` and `c₁ + tD / R + gap ≤ switchRound S tL + 2`, then some round `c₂` with
    `c₁ + tD / R ≤ c₂` and `c₂ + 3 ≤ c₁ + tD / R + gap` has its openings and slots `o_{c₂} + 1`,
    `o_{c₂} + 2` proposed by validators not held, and every block `P₂` the proposal duty of
    `o_{c₂} + 2` can return satisfies `P ⪯ P₂` and `h(P) < h_j(P₂)`. -/
theorem secondWindowAfterTimeoutSharp_f7 (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v₀ : V)
    (tGAT tE tL : Int) (gap : Nat)
    (hgap : gap + 2 ≤ S.cfg.K) (hg3 : 3 ≤ gap)
    (hlen : tGAT + (Restated.healingLengthη M S gap + (Restated.constants M S).period) ≤ tE) (hEL : tE ≤ tL)
    (hgst : S.E.t_GST ≤ tGAT) (hmono : Sched.MonotoneCorruption)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hsync : Restated.SynchronyFromWake M S x) (hmult : AwakeAtMultiples S Sched)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT) (htd : Restated.TimeDiverges M x)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hthird : ∀ t : Int, t ≤ tL →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tL →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tL gap)
    (hrsW : Restated.roundSleepinessW M S Sched tE) (hcs : Restated.committeeSleepinessW M S Sched tE)
    (hw : Restated.WakesAtActionInstants M S Sched) (hs : Restated.SleepsAfterActionInstants M S Sched)
    (hprev : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.BasePreviousRoundSGCompatibleWithAnchorAtRound M S Sched x v r N
        (Restated.runAllPath M S Sched x v N) T)
    (hclear : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round) (n₀ : Nat),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S r)) →
      Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T)
    (hB' : Restated.BaseJustifiedHighAtSwitchRoundW M S Sched x tGAT tE gap)
    {n_W : Nat} (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    {T_W : NamedBlock V} (hAW : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.switchRound M S tE) T_W)
    (hJswitch : ∀ (v : V) (n₁ : Nat),
      M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) - 1
        ≤ (x[n₁].time : Int) →
      n₁ ≤ n_W → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J T_W.erase)
    {r₀ : Round} {n₀ : Nat} {T₀ : NamedBlock V}
    (hr₀ : Restated.switchRound M S tE ≤ r₀) (hTW₀ : Block.Preceq T_W.erase T₀.erase)
    (hJ₀ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x r₀ n₀ n_W T₀)
    {N : Nat} (hNW : (x[N].time : Int) ≤ (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tL)))
    (hN : (x[N].time : Int) ≤ tL) (hWN : (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tL)) ≤ (x[N].time : Int))
    {T_D' : NamedBlock V}
    (hA : Restated.AnchorAtRound M S Sched x tGAT tL (Restated.rebasedDeadlineRoundW M S tGAT gap) T_D')
    {c₁ : Round} (hc₁ : r₀ + 2 ≤ c₁)
    (hc₁W : c₁ + S.cfg.timeoutDelay / S.hc.R + gap ≤ Restated.switchRound M S tL + 2)
    (hopening : S.E.proposer ((M.opening_slot S.hc c₁)) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c₁))))
    {P : NamedBlock V}
    (hnj : (M.derive_named S.E S.cfg P).nj = true) :
    let R : Record.Run V :=
      { Restated.runAll M S Sched x v₀ N with honest := notHeldAt Sched (x[N].time : Int) }
    let W := Restated.runAllPath M S Sched x v₀ N
    let wp := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc c₁))) (S.E.proposer (M.opening_slot S.hc c₁))
    ∀ cp : M.Cache,
      M.onPhaseTick S.E S.hc wp.st.core.toHealing (M.proposal_time S.E (M.opening_slot S.hc c₁)) wp.cache ⇢ cp →
      let pn := M.mkNode (M.ns_setClock S.E wp.st (M.proposal_time S.E (M.opening_slot S.hc c₁))) wp.record cp
      M.proposal_with (M.gradeContract cp) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc c₁))) pn.st ⇢ some P →
    ∃ c₂ : Round,
      c₁ + S.cfg.timeoutDelay / S.hc.R ≤ c₂ ∧
      c₂ + 3 ≤ c₁ + S.cfg.timeoutDelay / S.hc.R + gap ∧
      ((∀ k < 3, S.E.proposer ((M.opening_slot S.hc c₂) + k) ∈
          notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c₂) + k))) ∧
        S.E.proposer ((M.opening_slot S.hc (c₂ - 1))) ∈
          notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc (c₂ - 1)))) ∧
        S.E.proposer ((M.opening_slot S.hc (c₂ - 2))) ∈
          notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc (c₂ - 2))))) ∧
      (let wp₂ := W (strictEventIndex R (M.proposal_time S.E ((M.opening_slot S.hc c₂) + 2))) (S.E.proposer ((M.opening_slot S.hc c₂) + 2))
       ∀ cp₂ : M.Cache,
        M.onPhaseTick S.E S.hc wp₂.st.core.toHealing (M.proposal_time S.E ((M.opening_slot S.hc c₂) + 2)) wp₂.cache ⇢ cp₂ →
        let pn₂ := M.mkNode (M.ns_setClock S.E wp₂.st (M.proposal_time S.E ((M.opening_slot S.hc c₂) + 2))) wp₂.record cp₂
        ∀ o : Option (NamedBlock V),
          M.proposal_with (M.gradeContract cp₂) .poolAndCarried S.E S.hc
            ((Setup.alwaysAwake S).node (S.E.proposer ((M.opening_slot S.hc c₂) + 2))) pn₂.st ⇢ o →
          ∃ P₂ : NamedBlock V, o = some P₂ ∧
            NamedBlock.Preceq P P₂ ∧
            (M.derive_named S.E S.cfg P).h < (M.derive_named S.E S.cfg P₂).h_j) := by
  classical
  intro R W wp cp hcp pn hP
  have hrecE : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap :=
    fun t h1 h2 => hrec t h1 (h2.trans hEL)
  have hlen' : tGAT + Restated.healingLengthη M S gap ≤ tE := Restated.healingLength_le_of_kit_l76 facts S hlen
  have hlenL : tGAT + (Restated.healingLengthη M S gap + (Restated.constants M S).period) ≤ tL := hlen.trans hEL
  have hlenL' : tGAT + Restated.healingLengthη M S gap ≤ tL := Restated.healingLength_le_of_kit_l76 facts S hlenL
  have hRpos : 0 < S.hc.R := lt_of_lt_of_le (by decide) S.hc.R_ge_three
  have hm2 : 2 ≤ S.cfg.timeoutDelay / S.hc.R :=
    (Nat.le_div_iff_mul_le hRpos).mpr (by simpa only [Nat.mul_comm] using S.timeout_rounds.2)
  let rho₀ : Record.Run V := { honest := ∅, horizon := 0, events := [] }
  have hrDrW : Restated.deadlineRoundW M S tGAT gap + 2 ≤ Restated.switchRound M S tE :=
    (Restated.deadlineRoundW_add_two_le_rebased_l88 facts S Sched rho₀ hgst hlen' hrecE).trans
      (Restated.rebasedDeadlineRoundW_le_switchRound facts S tGAT tE gap rho₀ hgst hlen')
  obtain ⟨hr₀c₁, -, hd, hrg, hrest⟩ := nat_afterTimeoutSharp_f7 (Restated.deadlineRoundW M S tGAT gap)
    (Restated.switchRound M S tE) r₀ c₁ gap (S.cfg.timeoutDelay / S.hc.R) (Restated.switchRound M S tL) hrDrW hr₀ hm2
    hg3 hc₁ hc₁W
  obtain ⟨c₂, hc₂lo, hc₂hi, hw₂, hw₂p, hw₂pp⟩ :=
    Restated.strongWindow_sharp_ofRound_f7 facts S Sched hrec hgst hlenL' hd hrg
  obtain ⟨hlo, hhi, hc₂W, hc₂hi'⟩ := hrest c₂ hc₂lo hc₂hi
  have hf := Restated.admissibleFieldsOn_runAll_notHeld facts S Sched x v₀ N hsync hmono hawake hgst hcv hexec
    hmult hthird hN
  obtain ⟨cp', P', hcp', hP'⟩ := (p85f% exists_proposal₈₅f) facts hf.sorted hf.onePath
    (M.opening_slot S.hc c₂)
  obtain ⟨cpm, Pm, hcpm, hPm⟩ := (p85f% exists_proposal₈₅f) facts hf.sorted hf.onePath
    (M.opening_slot S.hc (c₂ - 1))
  obtain ⟨cpmm, Pmm, hcpmm, hPmm⟩ := (p85f% exists_proposal₈₅f) facts hf.sorted hf.onePath
    (M.opening_slot S.hc (c₂ - 2))
  refine ⟨c₂, hlo, hc₂hi', ⟨hw₂, hw₂p, hw₂pp⟩, ?_⟩
  intro wp₂ cp₂ hcp₂ pn₂ o ho
  obtain ⟨P₂, rfl⟩ := Restated.Vocabulary.Proofs.HealingSurface.proposedBlockAt_isSome facts
    (Setup.alwaysAwake S) R ((M.opening_slot S.hc c₂) + 2) o
    ⟨_, (p58% mkNode_mem_confirmationReadAt₅₈) hf.sorted hf.onePath _ _ cp₂ hcp₂,
      by rw [facts.nd.mkNode_cache]; exact ho⟩
  obtain ⟨hPP', hP'P₂, hlt⟩ := Restated.windowAfterTimeout_f2c facts S Sched x v₀ tGAT tE tL gap hgap hlen hEL
    hgst hmono hexec hsync hmult hcv htd hcom hthird hawake hrec hrsW hcs hw hs hprev hclear hB'
    hnW hAW hJswitch hr₀ hTW₀ hJ₀ hNW hN hA hr₀c₁ hlo hhi (Restated.voteHor_f2d facts S hc₂W hWN) hopening
    hw₂ hw₂p hw₂pp hnj cp hcp hP cp' hcp' hP' cp₂ hcp₂ ho cpm hcpm hPm cpmm hcpmm hPmm
  exact ⟨P₂, rfl, namedPreceq_trans_l85 hPP' hP'P₂, hlt⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Framework.StsMultisetLog
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- In an execution in which every tick has an outcome, along the path
    `W = Restated.runAllPath M S Sched x v₀ N`, with `3 ≤ gap`: some round `c₂` with `c₁ ≤ c₂` and
    `c₂ + 3 ≤ c₁ + tD / R + gap` has its openings and slots `o_{c₂} + 1`, `o_{c₂} + 2` proposed by
    validators not held, and every block `P₂` the proposal duty of `o_{c₂} + 2` can return satisfies
    `B' ⪯ P₂`, `h(B') < h_j(P₂)` and `h(T_D') ≤ h_j(P₂)`. -/
theorem secondWindowSharp_f7 (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v₀ : V)
    (tGAT tE tL : Int) (gap : Nat)
    (hgap : gap + 2 ≤ S.cfg.K) (hg3 : 3 ≤ gap)
    (hlen : tGAT + (Restated.healingLengthη M S gap + (Restated.constants M S).period) ≤ tE) (hEL : tE ≤ tL)
    (hgst : S.E.t_GST ≤ tGAT) (hmono : Sched.MonotoneCorruption)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hsync : Restated.SynchronyFromWake M S x) (hmult : AwakeAtMultiples S Sched)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT) (htd : Restated.TimeDiverges M x)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hthird : ∀ t : Int, t ≤ tL →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tL →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tL gap)
    (hrsW : Restated.roundSleepinessW M S Sched tE) (hcs : Restated.committeeSleepinessW M S Sched tE)
    (hw : Restated.WakesAtActionInstants M S Sched) (hs : Restated.SleepsAfterActionInstants M S Sched)
    (hprev : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.BasePreviousRoundSGCompatibleWithAnchorAtRound M S Sched x v r N
        (Restated.runAllPath M S Sched x v N) T)
    (hclear : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round) (n₀ : Nat),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S r)) →
      Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T)
    (hB' : Restated.BaseJustifiedHighAtSwitchRoundW M S Sched x tGAT tE gap)
    {n_W : Nat} (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    {T_W : NamedBlock V} (hAW : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.switchRound M S tE) T_W)
    (hJswitch : ∀ (v : V) (n₁ : Nat),
      M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) - 1
        ≤ (x[n₁].time : Int) →
      n₁ ≤ n_W → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J T_W.erase)
    {r₀ : Round} {n₀ : Nat} {T₀ : NamedBlock V}
    (hr₀ : Restated.switchRound M S tE ≤ r₀) (hTW₀ : Block.Preceq T_W.erase T₀.erase)
    (hJ₀ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x r₀ n₀ n_W T₀)
    {N : Nat} (hNW : (x[N].time : Int) ≤ (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tL)))
    (hN : (x[N].time : Int) ≤ tL) (hWN : (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tL)) ≤ (x[N].time : Int))
    {T_D' : NamedBlock V}
    (hA : Restated.AnchorAtRound M S Sched x tGAT tL (Restated.rebasedDeadlineRoundW M S tGAT gap) T_D')
    {B' : NamedBlock V} (hB'log : Restated.blockInLog M S Sched x B') {s : Slot}
    (hheads : Restated.AncestorOfHonestHeadsFrom M S Sched x B'.erase s)
    {c₁ : Round} (hsM : s ≤ (M.opening_slot S.hc (c₁ - 1))) (hc₁ : r₀ + 2 ≤ c₁)
    (hc₁W : c₁ + S.cfg.timeoutDelay / S.hc.R + gap ≤ Restated.switchRound M S tL + 2)
    (hprops : ∀ k < 3, S.E.proposer ((M.opening_slot S.hc c₁) + k) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c₁) + k)))
    (hopeningM : S.E.proposer ((M.opening_slot S.hc (c₁ - 1))) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc (c₁ - 1)))))
    (hopeningMM : S.E.proposer ((M.opening_slot S.hc (c₁ - 2))) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc (c₁ - 2))))) :
    let R : Record.Run V :=
      { Restated.runAll M S Sched x v₀ N with honest := notHeldAt Sched (x[N].time : Int) }
    let W := Restated.runAllPath M S Sched x v₀ N
    ∃ c₂ : Round,
      c₁ ≤ c₂ ∧ c₂ + 3 ≤ c₁ + S.cfg.timeoutDelay / S.hc.R + gap ∧
      ((∀ k < 3, S.E.proposer ((M.opening_slot S.hc c₂) + k) ∈
          notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c₂) + k))) ∧
        S.E.proposer ((M.opening_slot S.hc (c₂ - 1))) ∈
          notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc (c₂ - 1)))) ∧
        S.E.proposer ((M.opening_slot S.hc (c₂ - 2))) ∈
          notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc (c₂ - 2))))) ∧
      (let wp₂ := W (strictEventIndex R (M.proposal_time S.E ((M.opening_slot S.hc c₂) + 2))) (S.E.proposer ((M.opening_slot S.hc c₂) + 2))
       ∀ cp₂ : M.Cache,
        M.onPhaseTick S.E S.hc wp₂.st.core.toHealing (M.proposal_time S.E ((M.opening_slot S.hc c₂) + 2)) wp₂.cache ⇢ cp₂ →
        let pn₂ := M.mkNode (M.ns_setClock S.E wp₂.st (M.proposal_time S.E ((M.opening_slot S.hc c₂) + 2))) wp₂.record cp₂
        ∀ o : Option (NamedBlock V),
          M.proposal_with (M.gradeContract cp₂) .poolAndCarried S.E S.hc
            ((Setup.alwaysAwake S).node (S.E.proposer ((M.opening_slot S.hc c₂) + 2))) pn₂.st ⇢ o →
          ∃ P₂ : NamedBlock V, o = some P₂ ∧
            NamedBlock.Preceq B' P₂ ∧
            (M.derive_named S.E S.cfg B').h < (M.derive_named S.E S.cfg P₂).h_j ∧
            (M.derive_named S.E S.cfg T_D').h ≤ (M.derive_named S.E S.cfg P₂).h_j) := by
  classical
  intro R W
  have hrecE : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap :=
    fun t h1 h2 => hrec t h1 (h2.trans hEL)
  have hlen' : tGAT + Restated.healingLengthη M S gap ≤ tE := Restated.healingLength_le_of_kit_l76 facts S hlen
  have hRpos : 0 < S.hc.R := lt_of_lt_of_le (by decide) S.hc.R_ge_three
  have hm2 : 2 ≤ S.cfg.timeoutDelay / S.hc.R :=
    (Nat.le_div_iff_mul_le hRpos).mpr (by simpa only [Nat.mul_comm] using S.timeout_rounds.2)
  let rho₀ : Record.Run V := { honest := ∅, horizon := 0, events := [] }
  have hrDrW : Restated.deadlineRoundW M S tGAT gap + 2 ≤ Restated.switchRound M S tE :=
    (Restated.deadlineRoundW_add_two_le_rebased_l88 facts S Sched rho₀ hgst hlen' hrecE).trans
      (Restated.rebasedDeadlineRoundW_le_switchRound facts S tGAT tE gap rho₀ hgst hlen')
  have hrD'rW : Restated.rebasedDeadlineRoundW M S tGAT gap ≤ Restated.switchRound M S tE :=
    Restated.rebasedDeadlineRoundW_le_switchRound facts S tGAT tE gap rho₀ hgst hlen'
  obtain ⟨-, hcW, -, -, -⟩ := nat_afterTimeoutSharp_f7 (Restated.deadlineRoundW M S tGAT gap)
    (Restated.switchRound M S tE) r₀ c₁ gap (S.cfg.timeoutDelay / S.hc.R) (Restated.switchRound M S tL) hrDrW hr₀ hm2
    hg3 hc₁ hc₁W
  have hc₁3 := nat_clearSharp_f7 c₁ gap (S.cfg.timeoutDelay / S.hc.R) hm2 hg3
  have hq := nat_anchorRound_f2d _ _ _ _ hrD'rW hr₀ hc₁
  have hf := Restated.admissibleFieldsOn_runAll_notHeld facts S Sched x v₀ N hsync hmono hawake hgst hcv hexec
    hmult hthird hN
  obtain ⟨cp, P, hcp, hP⟩ := (p85f% exists_proposal₈₅f) facts hf.sorted hf.onePath
    (M.opening_slot S.hc c₁)
  obtain ⟨cpb, Pb, hcpb, hPb⟩ := (p85f% exists_proposal₈₅f) facts hf.sorted hf.onePath
    ((M.opening_slot S.hc c₁) + 2)
  obtain ⟨cp', P', hcp', hP'⟩ := (p85f% exists_proposal₈₅f) facts hf.sorted hf.onePath
    (M.opening_slot S.hc (c₁ - 1))
  obtain ⟨cp'', P'', hcp'', hP''⟩ := (p85f% exists_proposal₈₅f) facts hf.sorted hf.onePath
    (M.opening_slot S.hc (c₁ - 2))
  have hstep := fun (P₂ : NamedBlock V) =>
    Restated.windowStep_ofHeads_f2c facts S Sched x v₀ tGAT tE tL gap hlen hEL hgst
      hmono hexec hsync hmult hcv htd hcom hthird hawake hrec hrsW hcs hw hs hprev hclear hB' hnW
      hAW hJswitch hr₀ hTW₀ hJ₀ hNW hN hA hc₁ (Restated.voteHor_f2d facts S hcW hWN) hprops hopeningM hopeningMM
      (P := P) (P₂ := P₂) (P' := P') (P'' := P'') hB'log hheads hsM cp hcp hP
  have hB'P : NamedBlock.Preceq B' P := (hstep Pb cpb hcpb hPb cp' hcp' hP' cp'' hcp'' hP'').1
  have hopening : S.E.proposer ((M.opening_slot S.hc c₁)) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c₁))) := by
    simpa only [Nat.add_zero] using hprops 0 (by decide)
  obtain ⟨hAc, -, -, -, -, hpv⟩ := Restated.interiorInstants_l85d facts S c₁
  have hAcN : (Restated.Vocabulary.Execution.Setup.a M S c₁) ≤ (x[N].time : Int) := hAc.trans (hpv.trans (Restated.voteHor_f2d facts S hcW hWN))
  have htopP := Restated.openingProposal_height_ge_rebasedAnchor_l85d facts S Sched x v₀ N hsync hmono hawake
    hgst hcv hexec hmult hthird hN hcom hrec hA hq hAcN hopening cp hcp hP
  by_cases hnj : (M.derive_named S.E S.cfg P).nj = true
  ·
    have hB'h : (M.derive_named S.E S.cfg B').h ≤ (M.derive_named S.E S.cfg P).h :=
      facts.cs.derive_height_mono S.E S.cfg hB'P
    obtain ⟨c₂, hlo, hhi, hstrong, hall⟩ := Restated.secondWindowAfterTimeoutSharp_f7 facts S Sched
      x v₀ tGAT tE tL gap hgap hg3 hlen hEL hgst hmono hexec hsync hmult hcv htd hcom hthird hawake
      hrec hrsW hcs hw hs hprev hclear hB' hnW hAW hJswitch hr₀ hTW₀ hJ₀ hNW hN hWN hA hc₁ hc₁W
      hopening hnj cp hcp hP
    refine ⟨c₂, le_trans (Nat.le_add_right _ _) hlo, hhi, hstrong, ?_⟩
    intro wp₂ cp₂ hcp₂ pn₂ o ho
    obtain ⟨Q₂, hQ₂, hPQ₂, hlt⟩ := hall cp₂ hcp₂ o ho
    exact ⟨Q₂, hQ₂, namedPreceq_trans_l85 hB'P hPQ₂, lt_of_le_of_lt hB'h hlt, htopP.trans hlt.le⟩
  ·
    have hnjf : (M.derive_named S.E S.cfg P).nj = false := by
      simpa only [Bool.not_eq_true] using hnj
    refine ⟨c₁, le_rfl, hc₁3, ⟨hprops, hopeningM, hopeningMM⟩, ?_⟩
    intro wp₂ cp₂ hcp₂ pn₂ o ho
    obtain ⟨P₂, rfl⟩ := Restated.Vocabulary.Proofs.HealingSurface.proposedBlockAt_isSome facts
      (Setup.alwaysAwake S) R ((M.opening_slot S.hc c₁) + 2) o
      ⟨_, (p58% mkNode_mem_confirmationReadAt₅₈) hf.sorted hf.onePath _ _ cp₂ hcp₂,
        by rw [facts.nd.mkNode_cache]; exact ho⟩
    obtain ⟨-, hPP₂, hdisj⟩ := hstep P₂ cp₂ hcp₂ ho cp' hcp' hP' cp'' hcp'' hP''
    have hlt : (M.derive_named S.E S.cfg B').h <
        (M.derive_named S.E S.cfg P₂).h_j := by
      rcases hdisj with h | ⟨h, -⟩
      · exact h
      · exact absurd h hnj
    have htop := Restated.secondWindowClear_f2d facts S Sched x v₀ tGAT tE tL gap hlen hEL hgst hmono hexec hsync
      hmult hcv htd hcom hthird hawake hrec hrsW hcs hw hs hprev hclear hB' hnW hAW hJswitch hr₀
      hTW₀ hJ₀ hNW hN hWN hA hc₁ hcW hprops hopeningM hopeningMM hnjf
      cp hcp hP cp₂ hcp₂ ho cp' hcp' hP' cp'' hcp'' hP''
    exact ⟨P₂, rfl, namedPreceq_trans_l85 hB'P hPP₂, hlt, htop⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Framework.StsMultisetLog
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- In an execution in which every tick has an outcome, if
    `proposal_time s + finalityDeadlineSharpLanded_f7 S gap ≤ tL`, there is an instant `t`, at most
    the proposal instant of `s` plus `3 · gap + tD / R − 6` periods plus `9Δ`, such that every
    validator honest through a step `j` with `t ≤ x[j].time` has the honest proposal `B` of slot `s`
    as an ancestor of its finalized block there. -/
theorem honestProposal_finalizedDescendant_f7 (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v₀ : V)
    (tGAT tE tL : Int) (gap : Nat)
    (hgap : gap + 2 ≤ S.cfg.K)
    (hlen : tGAT + (Restated.healingLengthη M S gap + (Restated.constants M S).period) ≤ tE) (hEL : tE ≤ tL)
    (hgst : S.E.t_GST ≤ tGAT) (hmono : Sched.MonotoneCorruption)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hsync : Restated.SynchronyFromWake M S x) (hmult : AwakeAtMultiples S Sched)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT) (htd : Restated.TimeDiverges M x)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hthird : ∀ t : Int, t ≤ tL →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tL →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tL gap)
    (hrsW : Restated.roundSleepinessW M S Sched tE) (hcs : Restated.committeeSleepinessW M S Sched tE)
    (hw : Restated.WakesAtActionInstants M S Sched) (hs : Restated.SleepsAfterActionInstants M S Sched)
    (hprev : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.BasePreviousRoundSGCompatibleWithAnchorAtRound M S Sched x v r N
        (Restated.runAllPath M S Sched x v N) T)
    (hclear : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round) (n₀ : Nat),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S r)) →
      Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T)
    (hB' : Restated.BaseJustifiedHighAtSwitchRoundW M S Sched x tGAT tE gap)
    {n_W : Nat} (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    {T_W : NamedBlock V} (hAW : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.switchRound M S tE) T_W)
    (hJswitch : ∀ (v : V) (n₁ : Nat),
      M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) - 1
        ≤ (x[n₁].time : Int) →
      n₁ ≤ n_W → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J T_W.erase)
    {r₀ : Round} {n₀ : Nat} {T₀ : NamedBlock V}
    (hr₀ : Restated.switchRound M S tE ≤ r₀) (hTW₀ : Block.Preceq T_W.erase T₀.erase)
    (hJ₀ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x r₀ n₀ n_W T₀)
    {s : Slot} (hs0 : (M.opening_slot S.hc r₀) + 2 ≤ s)
    (hprop : HonestThroughTime Sched (M.vote_time S.E s) (S.E.proposer s))
    {i : Nat} {B : Block V} (hB : Restated.proposedBlockAtStep M S x i s B)
    (hi : (x[i].time : Int) ≤ M.vote_time S.E s)
    (hdead : M.proposal_time S.E s + Restated.finalityDeadlineSharpLanded_f7 M S gap ≤ tL) :
    ∃ t : Int,
      t ≤ M.proposal_time S.E s +
        ((3 * gap + S.cfg.timeoutDelay / S.hc.R - 6 : Nat) : Int) * (Restated.constants M S).period +
        9 * S.E.Δ ∧
      ∀ (v : V) (j : Nat), Restated.HonestThrough M Sched x j v → t ≤ (x[j].time : Int) →
        Block.Preceq B (x[j][v].st).st.core.F := by
  classical
  have hthirdE : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight :=
    fun t ht => hthird t (ht.trans hEL)
  have hphaseE : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t :=
    fun t h1 h2 => hawake t h1 (h2.trans hEL)
  have hrecE : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap :=
    fun t h1 h2 => hrec t h1 (h2.trans hEL)
  have hlen' : tGAT + Restated.healingLengthη M S gap ≤ tE := Restated.healingLength_le_of_kit_l76 facts S hlen
  have hlenL : tGAT + (Restated.healingLengthη M S gap + (Restated.constants M S).period) ≤ tL := hlen.trans hEL
  have hlenL' : tGAT + Restated.healingLengthη M S gap ≤ tL := Restated.healingLength_le_of_kit_l76 facts S hlenL
  have hRpos : 0 < S.hc.R := lt_of_lt_of_le (by decide) S.hc.R_ge_three
  have hm2 : 2 ≤ S.cfg.timeoutDelay / S.hc.R :=
    (Nat.le_div_iff_mul_le hRpos).mpr (by simpa only [Nat.mul_comm] using S.timeout_rounds.2)
  let rho₀ : Record.Run V := { honest := ∅, horizon := 0, events := [] }
  have hrDrW : Restated.deadlineRoundW M S tGAT gap + 2 ≤ Restated.switchRound M S tE :=
    (Restated.deadlineRoundW_add_two_le_rebased_l88 facts S Sched rho₀ hgst hlen' hrecE).trans
      (Restated.rebasedDeadlineRoundW_le_switchRound facts S tGAT tE gap rho₀ hgst hlen')
  have hr₀s : r₀ ≤ s / S.hc.R := by
    refine (Nat.le_div_iff_mul_le hRpos).mpr ?_
    have h := hs0
    rw [(pCR% opening_slot_closed_cr) facts] at h
    exact le_trans (Nat.le_add_right _ 2) h
  have hWs := Restated.switchRound_ge_of_deadline_f7 facts S hdead
  obtain ⟨c₁, hc₁lo, hc₁hi, hw₁, hw₁p, hw₁pp⟩ :=
    Restated.firstWindowSharp_f7 facts S Sched hrec hgst hlenL' hrDrW hr₀ hr₀s hdead
  obtain ⟨hg3, hc₁r, hc₁rs, hrs1, hc₁W⟩ := nat_secondSharp_f7 (Restated.deadlineRoundW M S tGAT gap)
    (Restated.switchRound M S tE) r₀ (s / S.hc.R) gap (S.cfg.timeoutDelay / S.hc.R) (Restated.switchRound M S tL) c₁
    hrDrW hr₀ hr₀s hWs hm2 hc₁lo hc₁hi
  have hct : M.confirmation_time S.E s ≤ tL := by
    have hslt : s < (s / S.hc.R + 1) * S.hc.R := by
      rw [Nat.add_mul, Nat.one_mul]; exact Nat.lt_div_mul_add hRpos
    have h2 : (s / S.hc.R + 1) * S.hc.R ≤ Restated.switchRound M S tL * S.hc.R :=
      Nat.mul_le_mul_right _ hrs1
    obtain ⟨hsle, hW0⟩ := nat_slotBound_f2d s S.hc.R (s / S.hc.R) (Restated.switchRound M S tL) hslt h2 hrs1
    have hsle' : s ≤ (M.opening_slot S.hc (Restated.switchRound M S tL)) + 2 := by
      rw [(pCR% opening_slot_closed_cr) facts]; exact hsle
    exact (facts.sch.confirmation_time_mono S hsle').trans (Restated.switchRound_spec facts S tL hW0)
  obtain ⟨m₀, hm₀⟩ := Restated.exists_tickStepAt facts x htd (Restated.action_pos facts S (Restated.switchRound M S tL))
  have hNeq : (x[m₀ + 1].time : Int) = (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tL)) := (Restated.tickStepAt_time facts x hm₀).1
  have hrDW : Restated.deadlineRoundW M S tGAT gap ≤ Restated.switchRound M S tL :=
    (Restated.deadlineRoundW_le_rebased facts S tGAT gap).trans
      (Restated.rebasedDeadlineRoundW_le_switchRound facts S tGAT tL gap rho₀ hgst hlenL')
  obtain ⟨-, hWE⟩ := Restated.window_in_phase_atRound facts S tGAT tL gap hgst hlenL' hrDW le_rfl
  have hNW : (x[m₀ + 1].time : Int) ≤ (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tL)) := le_of_eq hNeq
  have hWN : (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tL)) ≤ (x[m₀ + 1].time : Int) := le_of_eq hNeq.symm
  have hN : (x[m₀ + 1].time : Int) ≤ tL := hNW.trans hWE
  obtain ⟨T_D', hA⟩ := Restated.exists_anchorAtRound facts S Sched x hsync hmono hawake hgst hcv hexec hmult
    hthird hcom hrec hlenL' htd (Restated.deadlineRoundW_le_rebased facts S tGAT gap)
    (Restated.rebasedDeadlineRoundW_le_switchRound facts S tGAT tL gap rho₀ hgst hlenL')
  have hHeads := Restated.honestProposal_ancestorOfHonestHeadsFrom_i1b facts S Sched x tE hexec hmono htd tGAT
    gap hgst hlen' hsync hthirdE hphaseE hrsW hmult hcv hcs hcom hw hs hrecE hprev hclear hB' hnW
    hAW hJswitch hr₀ hTW₀ hJ₀ hawake hthird hrec hs0 hct hprop hB hi
  obtain ⟨B', hmem, hBe, -, -⟩ := hB
  have hB'log : Restated.blockInLog M S Sched x B' :=
    ⟨B', Or.inl ⟨i, _, hmem, rfl⟩, Proofs.NamedAncestry.named_self B'⟩
  have hsM : s ≤ (M.opening_slot S.hc (c₁ - 1)) := by
    rw [(pCR% opening_slot_closed_cr) facts]; exact nat_slotPrev_f2c S.hc.R s c₁ hRpos hc₁rs
  obtain ⟨c₂, hc₁₂, hc₂hi, ⟨hw₂, -, -⟩, hall₂⟩ := Restated.secondWindowSharp_f7 facts S
    Sched x v₀ tGAT tE tL gap hgap hg3 hlen hEL hgst hmono hexec hsync hmult hcv htd hcom hthird
    hawake hrec hrsW hcs hw hs hprev hclear hB' hnW hAW hJswitch hr₀ hTW₀ hJ₀ hNW hN hWN hA hB'log
    (hBe ▸ hHeads) hsM hc₁r hc₁W hw₁ hw₁p hw₁pp
  have hf := Restated.admissibleFieldsOn_runAll_notHeld facts S Sched x v₀ (m₀ + 1) hsync hmono hawake hgst
    hcv hexec hmult hthird hN
  obtain ⟨cp₂, P₂, hcp₂, hP₂⟩ := (p85f% exists_proposal₈₅f) facts hf.sorted hf.onePath
    ((M.opening_slot S.hc c₂) + 2)
  obtain ⟨P₂', hP₂eq, hB'P₂, hltB, htop₂⟩ := hall₂ cp₂ hcp₂ (some P₂) hP₂
  cases hP₂eq
  obtain ⟨hd₂, hg₂, hr₀c₂, hthirdR⟩ := nat_thirdSharp_f7 (Restated.deadlineRoundW M S tGAT gap)
    (Restated.switchRound M S tE) r₀ (s / S.hc.R) gap (S.cfg.timeoutDelay / S.hc.R) (Restated.switchRound M S tL) c₁ c₂
    hrDrW hr₀ hWs hm2 hg3 hc₁r hc₁hi hc₁₂ hc₂hi
  obtain ⟨c₃, hc₃lo, hc₃hi, hw₃, -, -⟩ :=
    Restated.strongWindow_sharp_ofRound_f7 facts S Sched hrec hgst hlenL' hd₂ hg₂
  obtain ⟨hc₃W, hc₃b, hd₃⟩ := hthirdR c₃ hc₃lo hc₃hi
  obtain ⟨cp₃₁, P₃₁, hcp₃₁, hP₃₁⟩ := (p85f% exists_proposal₈₅f) facts hf.sorted hf.onePath
    ((M.opening_slot S.hc c₃) + 1)
  have hP₂P₃₁ := Restated.thirdWindowParent_f2d facts S Sched x v₀ tGAT tE tL gap hlen hEL hgst hmono hexec hsync
    hmult hcv htd hcom hthird hawake hrec hrsW hcs hw hs hprev hclear hB' hnW hAW hJswitch hr₀
    hTW₀ hJ₀ hN hWN hr₀c₂ hc₃lo hc₃W (hw₂ 2 (by decide)) hw₃ cp₂ hcp₂ hP₂ cp₃₁ hcp₃₁ hP₃₁
  have hmonoJ := Restated.h_j_mono_chain facts S hP₂P₃₁
  have hBJ : Block.Preceq B'.erase (M.derive_named S.E S.cfg P₃₁).J :=
    Restated.preceq_justified_of_height_lt_f1b1 facts S.E S.cfg (namedPreceq_trans_l85 hB'P₂ hP₂P₃₁)
      (lt_of_lt_of_le hltB hmonoJ)
  have hstep := Restated.finalityStepWindow_joined_f1b1 facts S Sched x v₀ hlen hEL hsync hmono
    hawake hgst hcv hexec hmult hthird hcom hrec htd hA hd₃
    (by simpa only [Nat.add_zero] using hw₃ 0 (by decide))
    (hw₃ 1 (by decide)) (hw₃ 2 (by decide)) (n := m₀ + 1) (Restated.voteHor_f2d facts S hc₃W hWN)
    hNW (htop₂.trans hmonoJ) cp₃₁ hcp₃₁ hP₃₁
  refine ⟨M.vote_time S.E ((M.opening_slot S.hc c₃) + 2), Restated.voteTime_bound_f2b facts S hc₃b, ?_⟩
  intro v j hv hj
  have hvt : v ∈ notHeldAt Sched (M.vote_time S.E ((M.opening_slot S.hc c₃) + 2)) :=
    mem_notHeldAt.mpr (hv _ hj)
  rw [← hBe]
  exact preceq_trans_Preceq hBJ (hstep j hj v hvt)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Framework.StsMultisetLog
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- In an execution in which every tick has an outcome, under the premises of
    `honestProposal_finalizedDescendant_f7`, every validator honest through a step at or after the
    proposal instant of `s` plus `finalityDeadlineDirect S gap` has the honest proposal `B` of slot
    `s` as an ancestor of its finalized block there. -/
theorem honestProposal_finalizedAfterDeadline_f7 (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v₀ : V)
    (tGAT tE tL : Int) (gap : Nat)
    (hgap : gap + 2 ≤ S.cfg.K)
    (hlen : tGAT + (Restated.healingLengthη M S gap + (Restated.constants M S).period) ≤ tE) (hEL : tE ≤ tL)
    (hgst : S.E.t_GST ≤ tGAT) (hmono : Sched.MonotoneCorruption)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hsync : Restated.SynchronyFromWake M S x) (hmult : AwakeAtMultiples S Sched)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT) (htd : Restated.TimeDiverges M x)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hthird : ∀ t : Int, t ≤ tL →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tL →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tL gap)
    (hrsW : Restated.roundSleepinessW M S Sched tE) (hcs : Restated.committeeSleepinessW M S Sched tE)
    (hw : Restated.WakesAtActionInstants M S Sched) (hs : Restated.SleepsAfterActionInstants M S Sched)
    (hprev : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.BasePreviousRoundSGCompatibleWithAnchorAtRound M S Sched x v r N
        (Restated.runAllPath M S Sched x v N) T)
    (hclear : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round) (n₀ : Nat),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S r)) →
      Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T)
    (hB' : Restated.BaseJustifiedHighAtSwitchRoundW M S Sched x tGAT tE gap)
    {n_W : Nat} (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    {T_W : NamedBlock V} (hAW : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.switchRound M S tE) T_W)
    (hJswitch : ∀ (v : V) (n₁ : Nat),
      M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) - 1
        ≤ (x[n₁].time : Int) →
      n₁ ≤ n_W → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J T_W.erase)
    {r₀ : Round} {n₀ : Nat} {T₀ : NamedBlock V}
    (hr₀ : Restated.switchRound M S tE ≤ r₀) (hTW₀ : Block.Preceq T_W.erase T₀.erase)
    (hJ₀ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x r₀ n₀ n_W T₀)
    {s : Slot} (hs0 : (M.opening_slot S.hc r₀) + 2 ≤ s)
    (hprop : HonestThroughTime Sched (M.vote_time S.E s) (S.E.proposer s))
    {i : Nat} {B : Block V} (hB : Restated.proposedBlockAtStep M S x i s B)
    (hi : (x[i].time : Int) ≤ M.vote_time S.E s)
    (hdead : M.proposal_time S.E s + Restated.finalityDeadlineSharpLanded_f7 M S gap ≤ tL) :
    ∀ (v : V) (j : Nat), Restated.HonestThrough M Sched x j v →
      M.proposal_time S.E s + Restated.finalityDeadlineDirect M S gap ≤ (x[j].time : Int) →
      Block.Preceq B (x[j][v].st).st.core.F := by
  obtain ⟨t, ht, hF⟩ := Restated.honestProposal_finalizedDescendant_f7 facts S Sched x v₀ tGAT tE tL gap hgap
    hlen hEL hgst hmono hexec hsync hmult hcv htd hcom hthird hawake hrec hrsW hcs hw hs hprev
    hclear hB' hnW hAW hJswitch hr₀ hTW₀ hJ₀ hs0 hprop hB hi hdead
  intro v j hv hj
  have hD : Restated.finalityDeadlineDirect M S gap =
      ((3 * gap + S.cfg.timeoutDelay / S.hc.R - 6 : Nat) : Int) * (Restated.constants M S).period +
        9 * S.E.Δ := rfl
  rw [hD] at hj
  exact hF v j hv (by linarith)

end

end DecoupledConsensusModel.Sts.Restated
