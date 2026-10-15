import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bInvariantActiveSinceW
import Proofs.Claims.Restated.Claim13bK_JointBase
import Proofs.Claims.Restated.Claim13bStepActiveJoint
import Proofs.Claims.Restated.Claim13bStepGrade
import Proofs.Claims.Restated.Claim13beKitActiveSince
import Proofs.Claims.Restated.Claim13beRoute3_58
import Proofs.Claims.Restated.Claim13beRoute3_76
import Proofs.Claims.Restated.Claim13beRoute3_77
import Proofs.Claims.Restated.Claim13beRoute3_88
import Proofs.Claims.Restated.Claim13beRoute3_91
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActiveJoint
import Model.Conditions.Claim13bInvariantActiveSince
import Model.Conditions.Claim13bInvariantActiveSinceW
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_72
import Model.Conditions.Claim13beRoute3_74
import Model.Conditions.Claim13beRoute3_82
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

/-!
# `Claim13bfJoint.lean`, the joint route to claim 13bf over the record

The three theorems that prove claim 13bf from its premises alone, through the joint invariant
`AfterPhaseInvariantOverActiveSetsJoint`, over an arbitrary model `M : Record.Model V` and its
facts `facts : Record.Facts M`:

- `afterPhaseStepOverActiveSetsJoint_of_premises`: the joint invariant at a round at or after the
  switch round carries to the next round;
- `afterPhaseJoint_base_and_step_of_premises`: the joint invariant at the switch round's tick step,
  and the step of the first theorem from its anchor;
- `claim13bf_conclusion_of_joint`: the finalized blocks of any two validators honest through their
  own steps are compatible.

Restored on 2026-10-15 from the record pass's pages (`Claim13bfJoint.lean` whole, and the last
section of `Claim13bStepActiveJoint.lean`, at commit `f5587d90d`), with the imports and the
`Upstream` spellings mapped to this library's names. The statements and proofs are the record
pass's text. Inside the first proof of `afterPhaseJoint_base_and_step_of_premises` the regime of
`hclear` is read along the path of the run `R_N` that the execution `x` follows
(`Restated.runAllPath M S Sched x v N`), the form the theorems it calls have.
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

/-- Restated over the record from `afterPhaseStepOverActiveSetsJoint_of_premises`
    (`DecoupledConsensusStsProofs/Spec2Claims/Claim13bStepActiveJoint.lean:453`).

    **The after-phase step over the joint invariant, from the base anchor.**

    The plan's §9.1 signature: the premises of `afterPhaseStepOverActiveSetsSinceFrom_of_hypothesesW`
    (`Claim13bInvariantActiveSinceW.lean`), name for name and in its order, with `hyp` removed and
    `hcatch : CatchUpOnWake S x` added in its place, and the one switch-round input `hJswitch`
    (the page header, stage (1)). The switch step `n_W` is the premise's, as in
    `AfterPhaseStepOverActiveSetsSinceFrom` (`Claim13beRoute3_82.lean`), not quantified again in
    the conclusion.

    Route: `tick_field_at_succ` for the round-`(r + 1)` tick step, then
    `afterPhaseJointRound_of_premises`.

    Read aloud: on the premises of `afterPhaseJointRound_of_premises`, from every round `r` at or
    after the switch round whose anchor `T` is a descendant of `T_W` or `T_W` itself and at which
    the joint invariant holds with tick step `n` and switch step `n_W`, the joint invariant
    carries to round `r + 1` with the same switch step and an anchor that is a descendant of `T`
    or `T` itself.

    Where it reads the run, and where it deviates from the landed statement (one pass, cycle
    31): as `afterPhaseJointRound_of_premises`.

    Read aloud (over the record): the statement above holds, with the regime of `hprev` and `hclear`, and `hprev`'s
    conclusion, read along the path of the run `R_N` that `x` follows. -/
theorem afterPhaseStepOverActiveSetsJoint_of_premises (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (hcatch : Restated.CatchUpOnWake M S x)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hsync : Restated.SynchronyFromWake M S x)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE)
    (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hcs : Restated.committeeSleepinessW M S Sched tE)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hw : Restated.WakesAtActionInstants M S Sched) (hs : Restated.SleepsAfterActionInstants M S Sched)
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
      Block.Preceq T_W.erase T.erase →
      Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x r n n_W T →
      ∃ (n' : Nat) (T' : NamedBlock V),
        Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x (r + 1) n' n_W T' ∧
          Block.Preceq T.erase T'.erase := by
  intro r n T hr hTW hJ
  obtain ⟨n', hn'⟩ := Restated.tick_field_at_succ facts S Sched x htd r
  -- one choice of the round-`(r + 1)` action attestations: every action read can compute one
  -- (as `afterPhaseStepOverActiveSetsSinceFrom_of_hypotheses`, `Restated/Claim13beRoute3_82.lean`)
  have hne : ∀ q : V, ∃ a, a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S)
      (x[n'][q].st) q (r + 1) := fun q => by
    obtain ⟨na, hna⟩ := (p74% actionReadFrom_nonempty₇₄) facts (Setup.alwaysAwake S)
      (x[n'][q].st) (r + 1)
    obtain ⟨D, hD⟩ := facts.dt.attest_with_nonempty (M.gradeContract na.cache)
      (Setup.alwaysAwake S).E (Setup.alwaysAwake S).hc ((Setup.alwaysAwake S).node q) na.st na.record
    exact ⟨D.2.2, na, hna, D.1, D.2.1, hD⟩
  choose att hattq using hne
  have hatt : Restated.ActionAttestationsOf M S Sched x r n' att := fun q _ => hattq q
  obtain ⟨-, hstep⟩ := Restated.afterPhaseJointRound_of_premises facts S Sched x tE hexec hmono htd hcatch
    tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec hprev hclear hB'
    hnW hAW hJswitch hr hTW hJ hn'
  obtain ⟨hJ', hTT'⟩ := hstep att hatt
  exact ⟨n', _, hJ', hTT'⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- Restated over the record from `afterPhaseJoint_base_and_step_of_premises`
    (`DecoupledConsensusStsProofs/Spec2Claims/Claim13bfJoint.lean:79`).

    **A switch-round tick step `n_W` and anchor `T_W`, the joint invariant there, and the joint
    step from `T_W`, from the copy 13bf's premises for one execution and `hlow`.**

    Premises: those of `claim13bf_conclusion_of_step_overActiveSetsSince`
    (`Claim13bfKit.lean`) up to `hcs`, in its order, then `hlow` (the page header).

    Route. `hprev` is lane V3's `basePreviousRoundSGCompatibleWithAnchor_atRound`
    (`Claim13beRoute3_88.lean:295`); `hclear` is lane V4's `baseClearFGSource_atRound_of_premises`
    (`Claim13beRoute3_91.lean:114`) at `rD ≤ rD' ≤ r` (`deadlineRoundW_le_rebased`); (B′) is
    `hlow` at the tick step itself. Lane S6's `afterPhaseInvariantOverActiveSetsJoint_at_switchRound`
    gives `n_W`, `T_W` and the joint invariant at `rW`; lane S6's
    `justifiedAncestor_before_switchTick_of_justifiedHigh` turns `hlow` at `n_W` into `hJswitch`;
    lane S5's `afterPhaseStepOverActiveSetsJoint_of_premises` is the step.

    Read aloud: from the copy 13bf's premises, if at every step from one instant before the vote
    instant of `o_rW + 1` up to the switch round's tick step every validator honest through that
    step holds a justified height at least that of every round-`rD'` anchor, then there are a step
    `n_W` that is the sts tick at `S.a rW` and a switch-round anchor `T_W` such that the joint
    invariant holds at `rW` with tick step `n_W`, switch step `n_W` and anchor `T_W`, and from every
    round at or after `rW` whose anchor is `T_W` or a descendant of it, the joint invariant with
    switch step `n_W` carries to the next round with an anchor that is the round's anchor or a
    descendant of it.

    Where it deviates from the landed statement (one pass, cycle 31): it takes
    `htick`, that every tick has an outcome, last; the five theorems it calls take it. The rest is the landed statement.

    Read aloud (over the record): if every tick has an outcome, the statement above holds. -/
theorem afterPhaseJoint_base_and_step_of_premises (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (tGAT tE : Int) (gap : Nat)
    (hgap : gap + 2 ≤ S.cfg.K)
    (hlen : tGAT + (Restated.healingLengthη M S gap + (Restated.constants M S).period) ≤ tE)
    (hgst : S.E.t_GST ≤ tGAT) (hmono : Sched.MonotoneCorruption)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hsync : Restated.SynchronyFromWake M S x) (hmult : AwakeAtMultiples S Sched)
    (hwakes : Restated.WakesAtActionInstants M S Sched) (hsleeps : Restated.SleepsAfterActionInstants M S Sched)
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
  -- (B′) is `hlow` at the tick step itself
  have hB' : Restated.BaseJustifiedHighAtSwitchRoundW M S Sched x tGAT tE gap := by
    intro T_D' hAD' n_W hnW v hv
    have h1 := (Restated.tickStepAt_time facts x hnW).2
    have h2 := Restated.vote_time_succ_le_confirmation_time_l77 facts S ((M.opening_slot S.hc (Restated.switchRound M S tE)))
    rw [Restated.a_eq_confirmation_opening_l58 facts] at h1
    exact hlow n_W hnW T_D' hAD' v n_W (by linarith) le_rfl hv
  obtain ⟨n_W, T_W, hnW, hAW, hbase⟩ := Restated.afterPhaseInvariantOverActiveSetsJoint_at_switchRound facts S
    Sched x tGAT tE gap hgap hlen hgst hmono hexec hsync hmult hwakes hsleeps hcv htd hcom hthird
    hawake hrec hsl hrs hcs hprev hclear hB'
  have hJswitch := Restated.justifiedAncestor_before_switchTick_of_justifiedHigh facts S Sched x tE hexec hmono
    htd tGAT gap hgst hlen' hsync hthird hawake hrs hmult hcv hcom hrec hprev hclear hnW hAW
    (hlow n_W hnW)
  exact ⟨n_W, T_W, hnW, hbase,
    Restated.afterPhaseStepOverActiveSetsJoint_of_premises facts S Sched x tE hexec hmono htd hcatch tGAT gap
      hgst hlen' hsync hthird hawake hrs hmult hcv hcs hcom hwakes hsleeps hrec hprev hclear hB'
      hnW hAW hJswitch⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- Restated over the record from `claim13bf_conclusion_of_joint`
    (`DecoupledConsensusStsProofs/Spec2Claims/Claim13bfJoint.lean:173`).

    **The copy 13bf's conclusion for one execution, from its premises and `hlow`, without the four
    stage C fields.**

    Premises: those of `afterPhaseJoint_base_and_step_of_premises`, which are those of
    `claim13bf_conclusion_of_step_overActiveSetsSince` (`Claim13bfKit.lean`) up to `hcs`, with
    `hP`, `hf`, `hprev`, `hclear` and `hB` removed and `hlow` added. `hlow` names no top-level
    claim: it is a call-site input of `justifiedAncestor_before_switchTick_of_justifiedHigh`
    (`Claim13bK_JointBase.lean:1026`).

    Route. `afterPhaseJoint_base_and_step_of_premises` gives `n_W`, `T_W`, the joint invariant at
    `rW` and the joint step. The step from the base anchor over the invariant with the target
    clause since the switch round (`AfterPhaseStepOverActiveSetsSinceFrom`,
    `Claim13beRoute3_82.lean:615`) follows: given that invariant at round `r` with tick step `n` and
    anchor `T` with `T_W ⪯ T`, the joint induction (`afterPhaseInvariantOverActiveSetsJoint_of_stepFrom`)
    gives the joint invariant at `r` with some tick step, which is `n` (`tickStepAt_unique`); its
    three added clauses do not mention the anchor, so with the given invariant at `T` they make the
    joint invariant at `T`; the joint step carries it to `r + 1`, and `.toSince` reads the
    invariant there. Then `claim13be_conclusion_of_base_and_stepFrom_overActiveSetsSince`
    (`Claim13beKitActiveSince.lean:242`) at `hbase.toSince`.

    Read aloud: from the copy 13bf's premises, if at every step from one instant before the vote
    instant of `o_rW + 1` up to the switch round's tick step every validator honest through that
    step holds a justified height at least that of every round-`rD'` anchor, then no two blocks
    finalized in the stores of two validators honest through their own reads conflict.

    Where it deviates from the landed statement (one pass, cycle 31): it takes
    `htick`, that every tick has an outcome, last, as `afterPhaseJoint_base_and_step_of_premises`. The rest is the landed statement.

    Read aloud (over the record): if every tick has an outcome, the statement above holds. -/
theorem claim13bf_conclusion_of_joint (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (tGAT tE : Int) (gap : Nat)
    (hgap : gap + 2 ≤ S.cfg.K)
    (hlen : tGAT + (Restated.healingLengthη M S gap + (Restated.constants M S).period) ≤ tE)
    (hgst : S.E.t_GST ≤ tGAT) (hmono : Sched.MonotoneCorruption)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hsync : Restated.SynchronyFromWake M S x) (hmult : AwakeAtMultiples S Sched)
    (hwakes : Restated.WakesAtActionInstants M S Sched) (hsleeps : Restated.SleepsAfterActionInstants M S Sched)
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
      Block.Compatible (x[i][v₁].st).st.core.F (x[j][v₂].st).st.core.F := by
  obtain ⟨n_W, T_W, -, hbase, hstepJ⟩ := Restated.afterPhaseJoint_base_and_step_of_premises facts S Sched x
    tGAT tE gap hgap hlen hgst hmono hexec hsync hmult hwakes hsleeps hcatch hcv htd hcom hthird
    hawake hrec hsl hrs hcs hlow
  have hstep : Restated.AfterPhaseStepOverActiveSetsSinceFrom M S Sched x tE n_W T_W := by
    intro r n T hr hTW hinvS
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hr
    obtain ⟨n₁, T₁, hJ₁, -⟩ :=
      Restated.afterPhaseInvariantOverActiveSetsJoint_of_stepFrom facts S Sched x tE hbase hstepJ k
    obtain rfl : n₁ = n := Restated.tickStepAt_unique facts x
      hJ₁.toAfterPhaseInvariantOverActiveSetsSince.tick hinvS.tick
    have hJ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x (Restated.switchRound M S tE + k) n₁ n_W T :=
      { toAfterPhaseInvariantOverActiveSetsSince := hinvS
        prevTick := hJ₁.prevTick
        prevHeads := hJ₁.prevHeads
        prevConfirmed := hJ₁.prevConfirmed
        gradedUnderPrevSG := hJ₁.gradedUnderPrevSG }
    obtain ⟨n', T', hJ', hTT'⟩ := hstepJ _ n₁ T hr hTW hJ
    exact ⟨n', T', hJ'.toAfterPhaseInvariantOverActiveSetsSince, hTT'⟩
  exact Restated.claim13be_conclusion_of_base_and_stepFrom_overActiveSetsSince facts S Sched x tE n_W T_W
    hbase.toAfterPhaseInvariantOverActiveSetsSince hstep

end

end DecoupledConsensusModel.Sts.Restated
