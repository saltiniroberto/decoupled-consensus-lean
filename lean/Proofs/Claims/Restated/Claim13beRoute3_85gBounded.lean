import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bStepActiveJoint
import Proofs.Claims.Restated.Claim13bW_Schedule
import Proofs.Claims.Restated.Claim13beKitActiveSinceBounded
import Proofs.Claims.Restated.Claim13beRoute3_85g
import Model.Conditions.Claim13bInvariantActiveJoint
import Model.Conditions.Claim13bInvariantActiveSince
import Model.Conditions.Claim13bInvariantActiveSinceW
import Model.Conditions.Claim13bStepAnchor
import Model.Conditions.Claim13bStepFieldsAt
import Model.Conditions.Claim13beRoute3_72
import Model.Conditions.Claim13beRoute3_83
import Model.Conditions.RunAll
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13bd
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring

/-!
# The joint invariant after the switch round, stepped only up to a time `tHi`

The twins of the step lemmas of `lean/Proofs/Claims/Restated/Claim13beRoute3_85g.lean` in which the
step from round `r` to round `r + 1` is taken only when round `r + 1`'s action instant is at most
`tHi`: `afterPhaseJointRound_withoutCatchUp_bounded` (the step itself),
`afterPhaseStepOverActiveSetsJoint_withoutCatchUp_bounded`,
`afterPhaseInvariantOverActiveSetsJoint_of_stepFrom_bounded`,
`afterPhaseJoint_base_and_step_withoutCatchUp_bounded`, and `claim13be_conclusion_of_joint_bounded`,
which concludes for two reads the later of which is at least one period before `tHi`. The switch
round and the base stay at the phase end `tE`; `tHi` is a second time with `tE ≤ tHi`, up to which
every validator not held is awake from `tGAT` on (the hypothesis `hphaseHi`). The step is
proved from `afterPhaseJointRound_withoutCatchUp_l85f`; every other proof here calls the bounded
step only.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

local macro "p74% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_74)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- The step of `afterPhaseJointRound_withoutCatchUp_l85f`, taken only when round `r + 1`'s action
    instant is at most `tHi`, a time at or after the phase end `tE` up to which every validator not
    held is awake from `tGAT` on. Without the catch-up premise, at every round `r` at or after the
    switch round with `S.a (r + 1) ≤ tHi`, whose anchor `T` is `T_W` or a descendant of it and at which the
    joint invariant holds with tick step `n` and switch step `n_W`, with `n'` the tick step at
    `S.a (r + 1)`: the facts `StepFieldsAt` hold at `r`, `n`, `n'`, `T`, and for every choice `att`
    of the round-`(r + 1)` action attestations the joint invariant holds at round `r + 1` with tick
    step `n'`, the same switch step and the anchor `newAnchor S Sched x r n' att T`, of which `T` is
    an ancestor. -/
theorem afterPhaseJointRound_withoutCatchUp_bounded (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hsync : Restated.SynchronyFromWake M S x)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (tHi : Int) (hEHi : tE ≤ tHi)
    (hphaseHi : ∀ t : Int, tGAT ≤ t → t ≤ tHi →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE)
    (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hcs : Restated.committeeSleepinessW M S Sched tE)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    (hprev : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
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
        (Restated.runAllPath M S Sched x v N) T)
    (hclear : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
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
      Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T)
    (hB' : Restated.BaseJustifiedHighAtSwitchRoundW M S Sched x tGAT tE gap)
    {n_W : Nat} (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    {T_W : NamedBlock V} (hAW : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.switchRound M S tE) T_W)
    (hJswitch : ∀ (v : V) (n₁ : Nat),
      M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) - 1
        ≤ (x[n₁].time : Int) →
      n₁ ≤ n_W → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J T_W.erase)
    {r : Round} {n n' : Nat} {T : NamedBlock V}
    (hr : Restated.switchRound M S tE ≤ r) (hTW : Block.Preceq T_W.erase T.erase)
    (hJ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x r n n_W T)
    (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    (hrE : Restated.Vocabulary.Execution.Setup.a M S (r + 1) ≤ tHi) :
    Restated.StepFieldsAt M S Sched x tE r n n' T ∧
      ∀ att : V → NamedAttestation V, Restated.ActionAttestationsOf M S Sched x r n' att →
        Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x (r + 1) n' n_W
          (Restated.newAnchor M S Sched x r n' att T) ∧
        Block.Preceq T.erase (Restated.newAnchor M S Sched x r n' att T).erase := by
  have hopen : M.opening S.E S.hc r ≤ Restated.Vocabulary.Execution.Setup.a M S r := by
    show _ ≤ M.a S.hc S.E.Δ r
    rw [facts.gr.opening_eq_proposal_time, facts.sch.a_eq_confirmation_time]
    exact facts.sch.proposal_time_le_confirmation_time _ _
  exact Restated.afterPhaseJointRound_withoutCatchUp_l85f facts S Sched x tE hexec hmono htd
    tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hrec hprev hclear hB'
    hnW hAW hJswitch hr hTW hJ hn'
    (Restated.nextRoundReceipts_of_phase facts S Sched x hsync hmono hphaseHi
      (le_trans (Restated.tGAT_le_switchOpening facts S tGAT tE gap hgst hlen)
        (le_trans (Restated.switchOpening_le_opening facts S hr) hopen))
      hrE (Restated.gst_le_action_of_switchRound_le facts S tGAT tE gap hgst hlen hr))

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- Without the catch-up premise, with every validator not held awake from `tGAT` up to a time
    `tHi` at or after the phase end `tE`, from every round `r` at or after the switch round with
    `S.a (r + 1) ≤ tHi`, whose anchor `T` is `T_W` or a descendant of it and at which the joint
    invariant holds with tick step `n` and switch step `n_W`, the joint invariant carries to round
    `r + 1` with the same switch step and an anchor that is `T` or a descendant of `T`. -/
theorem afterPhaseStepOverActiveSetsJoint_withoutCatchUp_bounded (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hsync : Restated.SynchronyFromWake M S x)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (tHi : Int) (hEHi : tE ≤ tHi)
    (hphaseHi : ∀ t : Int, tGAT ≤ t → t ≤ tHi →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE)
    (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hcs : Restated.committeeSleepinessW M S Sched tE)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    (hprev : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
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
        (Restated.runAllPath M S Sched x v N) T)
    (hclear : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
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
      Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T)
    (hB' : Restated.BaseJustifiedHighAtSwitchRoundW M S Sched x tGAT tE gap)
    {n_W : Nat} (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    {T_W : NamedBlock V} (hAW : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.switchRound M S tE) T_W)
    (hJswitch : ∀ (v : V) (n₁ : Nat),
      M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) - 1
        ≤ (x[n₁].time : Int) →
      n₁ ≤ n_W → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J T_W.erase) :
    ∀ (r : Round) (n : Nat) (T : NamedBlock V), Restated.switchRound M S tE ≤ r →
      Restated.Vocabulary.Execution.Setup.a M S (r + 1) ≤ tHi →
      Block.Preceq T_W.erase T.erase →
      Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x r n n_W T →
      ∃ (n' : Nat) (T' : NamedBlock V),
        Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x (r + 1) n' n_W T' ∧
          Block.Preceq T.erase T'.erase := by
  intro r n T hr hrE hTW hJ
  obtain ⟨n', hn'⟩ := Restated.tick_field_at_succ facts S Sched x htd r
  have hne : ∀ q : V, ∃ a, a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S)
      (x[n'][q].st) q (r + 1) := fun q => by
    obtain ⟨na, hna⟩ := (p74% actionReadFrom_nonempty₇₄) facts (Setup.alwaysAwake S)
      (x[n'][q].st) (r + 1)
    obtain ⟨D, hD⟩ := facts.dt.attest_with_nonempty (M.gradeContract na.cache)
      (Setup.alwaysAwake S).E (Setup.alwaysAwake S).hc ((Setup.alwaysAwake S).node q) na.st na.record
    exact ⟨D.2.2, na, hna, D.1, D.2.1, hD⟩
  choose att hattq using hne
  have hatt : Restated.ActionAttestationsOf M S Sched x r n' att := fun q _ => hattq q
  obtain ⟨-, hstep⟩ := Restated.afterPhaseJointRound_withoutCatchUp_bounded facts S Sched x tE hexec hmono htd
    tGAT gap hgst hlen hsync hthird hphase tHi hEHi hphaseHi hrsW hmult hcv hcs hcom hrec hprev hclear hB'
    hnW hAW hJswitch hr hTW hJ hn' hrE
  obtain ⟨hJ', hTT'⟩ := hstep att hatt
  exact ⟨n', _, hJ', hTT'⟩


end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- If the joint invariant holds at the switch round `rW` with tick step and switch step `n_W` and
    anchor `T_W`, and it carries from every round `r` at or after `rW` with `S.a (r + 1) ≤ tHi`
    whose anchor is `T_W` or a descendant of it to round `r + 1`, then for every `k` with
    `S.a (rW + k) ≤ tHi` it holds at round `rW + k` with switch step `n_W` and an anchor that is
    `T_W` or a descendant of it. -/
theorem afterPhaseInvariantOverActiveSetsJoint_of_stepFrom_bounded (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE tHi : Int) {n_W : Nat}
    {T_W : NamedBlock V}
    (hbase : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x (Restated.switchRound M S tE) n_W n_W T_W)
    (hstep : ∀ (r : Round) (n : Nat) (T : NamedBlock V), Restated.switchRound M S tE ≤ r →
      Restated.Vocabulary.Execution.Setup.a M S (r + 1) ≤ tHi →
      Block.Preceq T_W.erase T.erase →
      Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x r n n_W T →
      ∃ (n' : Nat) (T' : NamedBlock V),
        Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x (r + 1) n' n_W T' ∧
          Block.Preceq T.erase T'.erase) :
    ∀ k : Nat, Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE + k) ≤ tHi →
      ∃ (n : Nat) (T : NamedBlock V),
        Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x (Restated.switchRound M S tE + k) n n_W T ∧
          Block.Preceq T_W.erase T.erase := by
  intro k
  induction k with
  | zero => intro _; exact ⟨n_W, T_W, hbase, (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _))⟩
  | succ k ih =>
    intro hk
    obtain ⟨n, T, hJ, hT⟩ := ih (le_trans (Restated.action_mono facts S (Nat.le_succ _)) hk)
    obtain ⟨n', T', hJ2, hTT'⟩ := hstep (Restated.switchRound M S tE + k) n T (Nat.le_add_right _ _) hk hT hJ
    exact ⟨n', T', hJ2, preceq_trans_Preceq hT hTT'⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- Without the catch-up premise, from the phase's premises and every validator not held awake from
    `tGAT` up to a time `tHi` at or after the phase end `tE`, if at every step from one instant
    before the vote instant of `o_rW + 1` up to the switch round's tick step every validator honest
    through that step holds a justified height at least that of every anchor at the re-based
    deadline round, then there are a step `n_W` that is the tick at `S.a rW` and a switch-round
    anchor `T_W` such that the joint invariant holds at `rW` with tick step and switch step `n_W`
    and anchor `T_W`, and from every round `r` at or after `rW` with `S.a (r + 1) ≤ tHi` whose anchor
    is `T_W` or a descendant of
    it, the joint invariant with switch step `n_W` carries to the next round with an anchor that is
    the round's anchor or a descendant of it. -/
theorem afterPhaseJoint_base_and_step_withoutCatchUp_bounded (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (tGAT tE : Int) (gap : Nat)
    (hgap : gap + 2 ≤ S.cfg.K)
    (hlen : tGAT + (Restated.healingLengthη M S gap + (Restated.constants M S).period) ≤ tE)
    (hgst : S.E.t_GST ≤ tGAT) (hmono : Sched.MonotoneCorruption)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hsync : Restated.SynchronyFromWake M S x) (hmult : AwakeAtMultiples S Sched)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (htd : Restated.TimeDiverges M x)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (tHi : Int) (hEHi : tE ≤ tHi)
    (hphaseHi : ∀ t : Int, tGAT ≤ t → t ≤ tHi →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    (hsl : sleepinessW S Sched tE) (hrs : Restated.roundSleepinessW M S Sched tE)
    (hcs : Restated.committeeSleepinessW M S Sched tE)
    (hlow : ∀ n_W : Nat, Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))) →
      ∀ T_D' : NamedBlock V,
      Restated.AnchorAtRound M S Sched x tGAT tE (Restated.rebasedDeadlineRoundW M S tGAT gap) T_D' →
      ∀ (v : V) (n₁ : Nat),
      M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) - 1
        ≤ (x[n₁].time : Int) →
      n₁ ≤ n_W → Restated.HonestThrough M Sched x n₁ v →
      (M.derive_named S.E S.cfg T_D').h ≤ (x[n₁][v].st).st.core.h_j) :
    ∃ (n_W : Nat) (T_W : NamedBlock V), Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))) ∧
      Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x (Restated.switchRound M S tE) n_W n_W T_W ∧
      ∀ (r : Round) (n : Nat) (T : NamedBlock V), Restated.switchRound M S tE ≤ r →
        Restated.Vocabulary.Execution.Setup.a M S (r + 1) ≤ tHi →
        Block.Preceq T_W.erase T.erase →
        Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x r n n_W T →
        ∃ (n' : Nat) (T' : NamedBlock V),
          Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x (r + 1) n' n_W T' ∧
            Block.Preceq T.erase T'.erase := by
  have hlen' : tGAT + Restated.healingLengthη M S gap ≤ tE := Restated.healingLength_le_of_kit_l76 facts S hlen
  have hprev := Restated.basePreviousRoundSGCompatibleWithAnchor_atRound facts S Sched x tGAT tE gap hlen hgst
    hmono hexec hsync hmult hcv hcom hthird hawake hrec
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
    fun r hrD' hrW => Restated.baseClearFGSource_atRound_of_premises facts S Sched x tGAT tE gap hgst hmono
      hexec hsync hmult hcv hcom hthird hawake r
      ((Restated.deadlineRoundW_le_rebased facts S tGAT gap).trans hrD') hrW
  have hB' : Restated.BaseJustifiedHighAtSwitchRoundW M S Sched x tGAT tE gap := by
    intro T_D' hAD' n_W hnW v hv
    have h1 := (Restated.tickStepAt_time facts x hnW).2
    have h2 := Restated.vote_time_succ_le_confirmation_time_l77 facts S ((M.opening_slot S.hc (Restated.switchRound M S tE)))
    rw [Restated.a_eq_confirmation_opening_l58 facts] at h1
    exact hlow n_W hnW T_D' hAD' v n_W (by linarith) le_rfl hv
  obtain ⟨n_W, T_W, hnW, hAW, hbase⟩ := Restated.afterPhaseInvariantOverActiveSetsJoint_at_switchRound facts S
    Sched x tGAT tE gap hgap hlen hgst hmono hexec hsync hmult hcv htd hcom hthird
    hawake hrec hsl hrs hcs hprev hclear hB'
  have hJswitch := Restated.justifiedAncestor_before_switchTick_of_justifiedHigh facts S Sched x tE hexec hmono
    htd tGAT gap hgst hlen' hsync hthird hawake hrs hmult hcv hcom hrec hprev hclear hnW hAW
    (hlow n_W hnW)
  exact ⟨n_W, T_W, hnW, hbase,
    Restated.afterPhaseStepOverActiveSetsJoint_withoutCatchUp_bounded facts S Sched x tE hexec hmono htd tGAT gap
      hgst hlen' hsync hthird hawake tHi hEHi hphaseHi hrs hmult hcv hcs hcom hrec
      hprev hclear hB'
      hnW hAW hJswitch⟩


end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- Without the catch-up premise, from the phase's premises and every validator not held awake from
    `tGAT` up to a time `tHi` at or after the phase end `tE`, if at every step from one instant
    before the vote instant of `o_rW + 1` up to the switch round's tick step every validator honest
    through that step holds a justified height at least that of every anchor at the re-based
    deadline round, then no two blocks finalized in the stores of two validators honest through
    their own reads at steps `i` and `j` conflict, provided the later of the two reads is at least
    one period before `tHi`. -/
theorem claim13be_conclusion_of_joint_bounded (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (tGAT tE : Int) (gap : Nat)
    (hgap : gap + 2 ≤ S.cfg.K)
    (hlen : tGAT + (Restated.healingLengthη M S gap + (Restated.constants M S).period) ≤ tE)
    (hgst : S.E.t_GST ≤ tGAT) (hmono : Sched.MonotoneCorruption)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hsync : Restated.SynchronyFromWake M S x) (hmult : AwakeAtMultiples S Sched)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (htd : Restated.TimeDiverges M x)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (tHi : Int) (hEHi : tE ≤ tHi)
    (hphaseHi : ∀ t : Int, tGAT ≤ t → t ≤ tHi →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    (hsl : sleepinessW S Sched tE) (hrs : Restated.roundSleepinessW M S Sched tE)
    (hcs : Restated.committeeSleepinessW M S Sched tE)
    (hlow : ∀ n_W : Nat, Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))) →
      ∀ T_D' : NamedBlock V,
      Restated.AnchorAtRound M S Sched x tGAT tE (Restated.rebasedDeadlineRoundW M S tGAT gap) T_D' →
      ∀ (v : V) (n₁ : Nat),
      M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) - 1
        ≤ (x[n₁].time : Int) →
      n₁ ≤ n_W → Restated.HonestThrough M Sched x n₁ v →
      (M.derive_named S.E S.cfg T_D').h ≤ (x[n₁][v].st).st.core.h_j) :
    ∀ (v₁ v₂ : V) (i j : Nat),
      Restated.HonestThrough M Sched x i v₁ → Restated.HonestThrough M Sched x j v₂ →
      max (x[i].time : Int) (x[j].time : Int) + (Restated.constants M S).period ≤ tHi →
      Block.Compatible (x[i][v₁].st).st.core.F (x[j][v₂].st).st.core.F := by
  obtain ⟨n_W, T_W, -, hbase, hstepJ⟩ := Restated.afterPhaseJoint_base_and_step_withoutCatchUp_bounded facts S
    Sched x tGAT tE gap hgap hlen hgst hmono hexec hsync hmult hcv htd hcom hthird
    hawake tHi hEHi hphaseHi hrec hsl hrs hcs hlow
  have hstep : ∀ (r : Round) (n : Nat) (T : NamedBlock V), Restated.switchRound M S tE ≤ r →
      Restated.Vocabulary.Execution.Setup.a M S (r + 1) ≤ tHi →
      Block.Preceq T_W.erase T.erase →
      Restated.AfterPhaseInvariantOverActiveSetsSince M S Sched x r n n_W T →
      ∃ (n' : Nat) (T' : NamedBlock V),
        Restated.AfterPhaseInvariantOverActiveSetsSince M S Sched x (r + 1) n' n_W T' ∧
          Block.Preceq T.erase T'.erase := by
    intro r n T hr hrE hTW hinvS
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hr
    obtain ⟨n₁, T₁, hJ₁, -⟩ :=
      Restated.afterPhaseInvariantOverActiveSetsJoint_of_stepFrom_bounded facts S Sched x tE tHi hbase hstepJ k
        (le_trans (Restated.action_mono facts S (Nat.le_succ _)) hrE)
    obtain rfl : n₁ = n := Restated.tickStepAt_unique facts x
      hJ₁.toAfterPhaseInvariantOverActiveSetsSince.tick hinvS.tick
    have hJ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x (Restated.switchRound M S tE + k) n₁ n_W T :=
      { toAfterPhaseInvariantOverActiveSetsSince := hinvS
        prevTick := hJ₁.prevTick
        prevHeads := hJ₁.prevHeads
        prevConfirmed := hJ₁.prevConfirmed
        gradedUnderPrevSG := hJ₁.gradedUnderPrevSG
        gradedUnderPrevSGPerformers := hJ₁.gradedUnderPrevSGPerformers }
    obtain ⟨n', T', hJ', hTT'⟩ := hstepJ _ n₁ T hr hrE hTW hJ
    exact ⟨n', T', hJ'.toAfterPhaseInvariantOverActiveSetsSince, hTT'⟩
  exact Restated.claim13be_conclusion_of_base_and_stepFrom_bounded facts S Sched x tE tHi n_W T_W
    hbase.toAfterPhaseInvariantOverActiveSetsSince hstep

end

end DecoupledConsensusModel.Sts.Restated
