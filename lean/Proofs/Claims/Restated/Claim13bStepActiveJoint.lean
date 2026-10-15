import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bInvariantActiveSinceW
import Proofs.Claims.Restated.Claim13bK_ConfirmedNew
import Proofs.Claims.Restated.Claim13bK_ConfirmedSafeAfter
import Proofs.Claims.Restated.Claim13bK_FgJustified
import Proofs.Claims.Restated.Claim13bK_Frame
import Proofs.Claims.Restated.Claim13bK_FrameNew
import Proofs.Claims.Restated.Claim13bK_GradeDescendant
import Proofs.Claims.Restated.Claim13bK_GradeOld
import Proofs.Claims.Restated.Claim13bK_GradeOldHeads
import Proofs.Claims.Restated.Claim13bK_HeadsNewAnchorJoint
import Proofs.Claims.Restated.Claim13bK_PrevHeadsStep
import Proofs.Claims.Restated.Claim13bPhaseSleepiness
import Proofs.Claims.Restated.Claim13bStepActiveAssembly
import Proofs.Claims.Restated.Claim13bStepActiveClauses
import Proofs.Claims.Restated.Claim13bStepAssembly
import Proofs.Claims.Restated.Claim13bStepConeIter
import Proofs.Claims.Restated.Claim13bStepFin
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13beRoute3_82
import Proofs.Claims.Restated.Claim13beRoute3_83
import Proofs.Claims.Restated.Projection
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActive
import Model.Conditions.Claim13bInvariantActiveJoint
import Model.Conditions.Claim13bInvariantActiveSince
import Model.Conditions.Claim13bInvariantActiveSinceW
import Model.Conditions.Claim13bInvariantActiveTop
import Model.Conditions.Claim13bK_FgJustified
import Model.Conditions.Claim13bK_FinBeforeTick
import Model.Conditions.Claim13bK_GradePairwise
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13bStepActiveAssembly
import Model.Conditions.Claim13bStepAnchor
import Model.Conditions.Claim13bStepAssembly
import Model.Conditions.Claim13bStepConeIter
import Model.Conditions.Claim13bStepFieldsAt
import Model.Conditions.Claim13bStepGrade
import Model.Conditions.Claim13bStepPairwise
import Model.Conditions.Claim13bStepSG
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

/-!
# The joint invariant from round to round

From the joint invariant at a round after the switch round: the fields of `StepFieldsAt` there, the
joint invariant at the next round, the anchor moving only forward, and by induction the joint
invariant at every round from the switch round on; stated over a model `M : Record.Model V`.
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
local macro "p83% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_83)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol
open Framework.StsMultisetLog

/-- If the invariant with the target clause since the switch round holds at round `r`, step `n_prev`
    is the sts tick at the action instant of round `r − 1`, and the facts `prevHeads`,
    `prevConfirmed` and `gradedUnderPrevSG` hold at `n_prev`, then the joint invariant holds at
    round `r`. -/
private theorem joint_of_prevTick_stepActiveJoint (facts : Record.Facts M)
    {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (Record.protocolOf M S) Sched} {r : Round} {n n_W n_prev : Nat} {T : NamedBlock V}
    (hinv : Restated.AfterPhaseInvariantOverActiveSetsSince M S Sched x r n n_W T)
    (hn_prev : Restated.tickStepAt M x n_prev ((Restated.Vocabulary.Execution.Setup.a M S (r - 1))))
    (hP : ∀ v_1 ∈ Restated.HonRound M S Sched (r - 1), ∀ a : NamedAttestation V,
      a.round = r - 1 → a.val_index = v_1 →
      (⟨v_1, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n_prev + 1].sent →
      ∀ C : NamedBlock V, C ∈ (x[n_prev + 1][v_1].st).st.bodies → a.confirmed = some C.root →
      Restated.HeadsBelow M S Sched x C.erase ((M.opening_slot S.hc r)))
    (hQ : Restated.ConfirmedCompatibleFreshSGOverHonRound M S Sched x (r - 1) n_prev n)
    (hG : ∀ v ∈ Restated.HonRound M S Sched r, ∀ p : Protocol.Phase,
      M.domain S.E S.hc r p ≤ (Restated.Vocabulary.Execution.Setup.a M S r) →
      ∀ m : Nat, Restated.stepBeforeInstant M x m (M.domain S.E S.hc r p) →
      ∀ B : Block V, ∀ b : Bool,
      M.gradeBool S.E (M.gradeView (M.toHealing (x[m][v].st).st.core))
          (x[m][v].st).st.core.F S.hc.η_SG r (M.early S.E S.hc r p)
          (M.late S.E S.hc r p) B ⇢ b → b = true →
      ∃ v_1 ∈ Restated.HonRound M S Sched (r - 1), ∃ a : NamedAttestation V,
        a.round = r - 1 ∧ a.val_index = v_1 ∧
        (⟨v_1, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n_prev + 1].sent ∧
        ∃ C : NamedBlock V, C ∈ (x[n_prev + 1][v_1].st).st.bodies ∧ a.confirmed = some C.root ∧
          Block.Preceq B C.erase) :
    Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x r n n_W T where
  toAfterPhaseInvariantOverActiveSetsSince := hinv
  prevTick := ⟨n_prev, hn_prev⟩
  prevHeads := fun n₂ hn₂ => by
    obtain rfl := Restated.tickStepAt_unique facts x hn₂ hn_prev
    exact hP
  prevConfirmed := fun n₂ hn₂ => by
    obtain rfl := Restated.tickStepAt_unique facts x hn₂ hn_prev
    exact hQ
  gradedUnderPrevSG := fun n₂ hn₂ => by
    obtain rfl := Restated.tickStepAt_unique facts x hn₂ hn_prev
    exact hG

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

/-- Under the run's premises and three clauses of the invariant at round `r` (its tick,
    height-ceiling and since-the-switch target clauses), whatever a validator honest through its own
    read holds as its justified block, at any step from `n_W` up to `n' + 1`, is an ancestor of `T`. -/
theorem justified_preceq_anchor_after_switchW_ofClauses (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
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
    (hrsW : Restated.roundSleepinessW M S Sched tE)
    (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
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
    {T_W : NamedBlock V} (hAW : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.switchRound M S tE) T_W)
    {n_W : Nat} (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    {r : Round} {n n' : Nat} {T : NamedBlock V}
    (hr : Restated.switchRound M S tE ≤ r)
    (hntick : Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S r)))
    (hceil : ∀ (v : V) (n₂ : Nat) (a : NamedAttestation V) (h' : Height)
      (entry : BlockId) (tmo : Bool),
      n₂ ≤ n + 1 → Restated.HonestThrough M Sched x n₂ v → a.val_index = v →
      (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n₂].sent →
      a.height_pair = NamedHeightPair.vote h' entry tmo →
      h' ≤ (M.derive_named S.E S.cfg T).h)
    (htgt : ∀ (v' : V) (n₂ : Nat) (a : NamedAttestation V) (h' : Height) (entry : BlockId)
        (tmo : Bool),
      n₂ ≤ n + 1 → Restated.HonestThrough M Sched x n₂ v' → a.val_index = v' →
      (⟨v', NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n₂].sent →
      (⟨v', NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∉ x[n_W].sent →
      a.height_pair = NamedHeightPair.vote h' entry tmo →
      h' ≤ (M.derive_named S.E S.cfg T).h →
      ∀ C : NamedBlock V, Restated.blockInLog M S Sched x C → C.root = entry →
      Block.Preceq C.erase T.erase)
    (hTW : Block.Preceq T_W.erase T.erase)
    (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1)))) :
    ∀ (v : V) (n₁ : Nat), n_W ≤ n₁ → n₁ ≤ n' + 1 → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J T.erase := by
  classical
  intro v n₁ hWn₁ hn₁ hv
  have hrsW' := Restated.roundSleepinessW_switchOpening_of_phase facts S Sched tGAT tE gap hgst hlen hmono
    hthird hphase hrsW
  have htE' := Restated.switchOpening_le_opening facts S (le_trans hr (Nat.le_succ r))
  rcases Restated.justified_honest_vote_before_succ_tick facts S Sched x hexec hmono hrsW' hn' htE' hn₁ hv with
    hgen | ⟨Jn, v', a, k, hJnmem, hJne, hkn', hktick, hround, hqhon, hidx, hsent, hpair⟩
  · rw [hgen]
    exact (preceq_eq_true_iff_Preceq.mp (Protocol.preceq_genesis _))
  · rw [← hJne]
    have hJnlog : Restated.blockInLog M S Sched x Jn := Restated.blockInLog_of_mem_bodies facts S Sched hv hJnmem
    have hkn : k ≤ n := Restated.tick_le_of_round_le facts S Sched x hktick hntick hround
    have hstep : k + 1 ≤ n + 1 := Nat.succ_le_succ hkn
    have hqk : Restated.HonestThrough M Sched x (k + 1) v' := fun t ht =>
      hqhon t (le_trans ht (Restated.time_mono_int facts S Sched x (Nat.succ_le_succ (Nat.le_of_lt hkn'))))
    by_cases hW : (⟨v', NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n_W].sent
    · -- a vote sent by the switch round's tick step
      have hrDW' : Restated.rebasedDeadlineRoundW M S tGAT gap ≤ Restated.switchRound M S tE :=
        Restated.rebasedDeadlineRoundW_le_switchRound facts S tGAT tE gap (Restated.runAll M S Sched x v 0) hgst hlen
      obtain ⟨T_D', hAD'⟩ := Restated.exists_anchorAtRound facts S Sched x hsync hmono hphase hgst hcv hexec
        hmult hthird hcom hrec hlen htd (Restated.deadlineRoundW_le_rebased facts S tGAT gap) hrDW'
      have hnWn : n_W ≤ n := Restated.tick_le_of_round_le facts S Sched x hnW hntick hr
      have hnn' : n + 1 ≤ n' := Restated.tick_succ_le_tick_succ_round facts S Sched x hntick hn'
      have hqW : Restated.HonestThrough M Sched x n_W v' := fun t ht =>
        hqhon t (le_trans ht (Restated.time_mono_int facts S Sched x (by omega)))
      have hvW : Restated.HonestThrough M Sched x n_W v := fun t ht =>
        hv t (le_trans ht (Restated.time_mono_int facts S Sched x hWn₁))
      have hlo : (M.derive_named S.E S.cfg T_D').h ≤ (x[n₁][v].st).st.core.h_j :=
        le_trans (hB' T_D' hAD' n_W hnW v hvW) (Restated.h_j_mono_sts facts S Sched x v hWn₁)
      exact preceq_trans_Preceq
        (Restated.honestVotes_onAnchorChain_since_roundW facts S Sched x hsync hmono hphase hgst hcv hexec
          hmult hthird hcom hrec hlen htd (Restated.deadlineRoundW_le_rebased facts S tGAT gap) hrDW' hprev
          hclear hAD' hAW hnW v' n_W a _ Jn.root false
          (Nat.le_succ n_W) hqW hidx hW hpair hlo Jn hJnlog rfl)
        hTW
    · -- a vote first sent after the switch round's tick step: the round-`r` clauses
      have hh := hceil v' (k + 1) a _ Jn.root false hstep hqk hidx hsent hpair
      exact htgt v' (k + 1) a _ Jn.root false hstep hqk hidx hsent hW hpair hh Jn
        hJnlog rfl

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

/-- Under the run's premises and the switch-round inputs, at a round `r` at or after the switch
    round whose anchor `T` is `T_W` or a descendant of it and at which the joint invariant holds
    with tick step `n` and switch step `n_W`, with `n'` the sts tick step at `S.a (r + 1)`:
    `StepFieldsAt` holds at `r`, `n`, `n'`, `T`; and for every choice `att` of the round-`(r + 1)`
    action attestations, the joint invariant holds at round `r + 1` with tick step `n'`, switch step
    `n_W` and the anchor `newAnchor` read along `att`, and `T` is an ancestor of that anchor. -/
theorem afterPhaseJointRound_of_premises (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
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
      Block.Preceq (x[n₁][v].st).st.core.J T_W.erase)
    {r : Round} {n n' : Nat} {T : NamedBlock V}
    (hr : Restated.switchRound M S tE ≤ r) (hTW : Block.Preceq T_W.erase T.erase)
    (hJ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x r n n_W T)
    (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1)))) :
    Restated.StepFieldsAt M S Sched x tE r n n' T ∧
      ∀ att : V → NamedAttestation V, Restated.ActionAttestationsOf M S Sched x r n' att →
        Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x (r + 1) n' n_W
          (Restated.newAnchor M S Sched x r n' att T) ∧
        Block.Preceq T.erase (Restated.newAnchor M S Sched x r n' att T).erase := by
  classical
  have hinvS := hJ.toAfterPhaseInvariantOverActiveSetsSince
  have hinv := hinvS.toTop
  have hctx : Restated.AnchoredRoundOverActiveSets M S Sched x tE r n T := ⟨hr, hinv⟩
  have hJW : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      ∀ (v : V) (n₁ : Nat), n_W ≤ n₁ → n₁ ≤ n'' + 1 → Restated.HonestThrough M Sched x n₁ v →
        Block.Preceq (x[n₁][v].st).st.core.J T.erase :=
    fun n'' h => Restated.justified_preceq_anchor_after_switchW facts S Sched x tE hexec hmono htd tGAT gap hgst
      hlen hsync hthird hphase hrsW hmult hcv hcom hrec hprev hclear hB' hAW hnW hr hinvS hTW h
  have hcross : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepFinalizedCrossingUnderAnchor M S Sched x r n'' T :=
    fun n'' h => Restated.stepFinalizedCrossingUnderAnchor_of_afterSwitch facts S Sched x hr hnW hinvS (hJW n'' h)
  have hjust : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepJustifiedRootUnderAnchor M S Sched x r n n'' T :=
    fun n'' h => Restated.stepJustifiedRootUnderAnchor_of_afterSwitch facts S Sched x hr hnW hinvS (hJW n'' h)
  have hP : ∀ v_1 ∈ Restated.HonRound M S Sched r, ∀ a : NamedAttestation V,
      a.round = r → a.val_index = v_1 →
      (⟨v_1, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n + 1].sent →
      ∀ C : NamedBlock V, C ∈ (x[n + 1][v_1].st).st.bodies → a.confirmed = some C.root →
      Restated.HeadsBelow M S Sched x C.erase ((M.opening_slot S.hc (r + 1))) := by
    rcases Nat.lt_or_ge (Restated.switchRound M S tE) r with hlt | hge
    · exact Restated.prevHeads_succ_afterPhase_ofAfterSwitch facts S Sched x tE hexec hmono htd hsync hmult hcom
        tGAT gap hgst hlen hcv hthird hphase hrsW hcs hw hs hnW hlt hJ hn' hcross (hJW n' hn')
    · have hrW : r = Restated.switchRound M S tE := le_antisymm hge hr
      refine Restated.prevHeads_succ_afterPhase facts S Sched x tE hexec hmono htd hsync hmult hcom tGAT gap hgst
        hlen hcv hthird hphase hrsW hcs hw hs hr hJ hn' hcross ?_
      intro v n₁ hlo hhi hvh
      by_cases hWn : n_W ≤ n₁
      · exact hJW n' hn' v n₁ hWn hhi hvh
      · rw [hrW] at hlo
        exact preceq_trans_Preceq (hJswitch v n₁ hlo (by omega) hvh) hTW
  have hQ : Restated.ConfirmedCompatibleFreshSGOverHonRound M S Sched x r n n' :=
    Restated.confirmedCompatibleFreshSG_of_openingHeads facts S Sched x tE hexec hmono htd hsync hmult hcom
      tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr hinv hcross hjust hw hn'
      (fun v_1 hv_1 a ha hav hsent C hC hconf _ _ => hP v_1 hv_1 a ha hav hsent C hC hconf)
      (by intro s _ _ m hm q hq; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono hm (facts.sch.vote_time_emod_delta S _) (Finset.mem_sdiff.2 ⟨Restated.awake_of_mem_HonSlot facts S Sched _ hq, fun h => ((Restated.mem_HonSlot facts).mp hq).2.2 (hmono _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E s) h)⟩)) (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›)
      (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›) (by intro v hv; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono hinv.tick (Restated.action_emod_delta facts S _) (Finset.mem_sdiff.2 ⟨mem_awake_of_awakeThroughout Sched (show v ∈ Sched.awakeThroughout (M.a S.hc S.E.Δ _ - wAttest S) (M.a S.hc S.E.Δ _) from (Finset.mem_sdiff.1 hv).1) (by linarith [twelve_delta_le_wAttest S, S.E.Δ_pos]) (le_refl _), (Finset.mem_sdiff.1 hv).2⟩))
  -- the fields other than `headsAtNewAnchor`, for every choice `att` of the round-`(r + 1)` action
  -- attestations
  have hCN : ∀ att : V → NamedAttestation V, Restated.ActionAttestationsOf M S Sched x r n' att →
      ∀ v ∈ Restated.HonRound M S Sched (r + 1),
      ∀ hs ∈ Restated.actionHealingStore M S (x[n'][v].st) (r + 1),
        Block.compatible hs.live_confirmed (Restated.newAnchor M S Sched x r n' att T).erase = true :=
    fun att hatt => Restated.confirmedNew_at_of_joint facts S Sched x tE hexec hmono htd hsync hmult hcom
      tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr hinv hcross hjust hw hn' hatt hQ
      (by intro s _ _ m hm q hq; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono hm (facts.sch.vote_time_emod_delta S _) (Finset.mem_sdiff.2 ⟨Restated.awake_of_mem_HonSlot facts S Sched _ hq, fun h => ((Restated.mem_HonSlot facts).mp hq).2.2 (hmono _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E s) h)⟩)) (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›)
      (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›) (by intro v hv; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono hinv.tick (Restated.action_emod_delta facts S _) (Finset.mem_sdiff.2 ⟨mem_awake_of_awakeThroughout Sched (show v ∈ Sched.awakeThroughout (M.a S.hc S.E.Δ _ - wAttest S) (M.a S.hc S.E.Δ _) from (Finset.mem_sdiff.1 hv).1) (by linarith [twelve_delta_le_wAttest S, S.E.Δ_pos]) (le_refl _), (Finset.mem_sdiff.1 hv).2⟩))
  have hnWn' : n_W ≤ n' := le_trans (Restated.tick_le_of_round_le facts S Sched x hnW hinv.tick hr)
    (Restated.tick_le_of_round_le facts S Sched x hinv.tick hn' (Nat.le_succ r))
  have hJact : ∀ v ∈ honestThroughSet Sched ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))),
      ∀ hs ∈ Restated.actionHealingStore M S (x[n'][v].st) (r + 1), Block.Preceq hs.J T.erase := by
    intro v hv hs hhs
    rw [Restated.actionHealingStore_J facts S _ _ hs hhs]
    have hvT : HonestThroughTime Sched ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) v := mem_honestThroughSet.mp hv
    have htn : (x[n'].time : Int) ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) := by
      rw [← (Restated.tickStepAt_time facts x hn').1]
      exact Restated.time_mono_int facts S Sched x (Nat.le_succ n')
    exact hJW n' hn' v n' hnWn' (Nat.le_succ n') (fun t ht => hvT t (le_trans ht htn))
  have hGP := Restated.gradePairwise_at_of_confirmedSafe facts S Sched x tE hexec hmono htd hsync hmult hcom
    tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr hinv hcross hjust hw hn' hJact hQ
    (by intro s _ _ m hm q hq; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono hm (facts.sch.vote_time_emod_delta S _) (Finset.mem_sdiff.2 ⟨Restated.awake_of_mem_HonSlot facts S Sched _ hq, fun h => ((Restated.mem_HonSlot facts).mp hq).2.2 (hmono _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E s) h)⟩)) (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›)
    (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›) (by intro v hv; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono hinv.tick (Restated.action_emod_delta facts S _) (Finset.mem_sdiff.2 ⟨mem_awake_of_awakeThroughout Sched (show v ∈ Sched.awakeThroughout (M.a S.hc S.E.Δ _ - wAttest S) (M.a S.hc S.E.Δ _) from (Finset.mem_sdiff.1 hv).1) (by linarith [twelve_delta_le_wAttest S, S.E.Δ_pos]) (le_refl _), (Finset.mem_sdiff.1 hv).2⟩))
  have hGD : ∀ att : V → NamedAttestation V, Restated.ActionAttestationsOf M S Sched x r n' att →
      ∀ v ∈ Restated.HonRound M S Sched (r + 1),
      ∀ p : Protocol.Phase, M.domain S.E S.hc (r + 1) p ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) →
      ∀ m : Nat, Restated.stepBeforeInstant M x m (M.domain S.E S.hc (r + 1) p) →
      ∀ B : Block V,
        M.gradeBool S.E (M.gradeView (M.toHealing (x[m][v].st).st.core))
            (x[m][v].st).st.core.F S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) p)
            (M.late S.E S.hc (r + 1) p) B ⇢ true →
        Block.Preceq T.erase B → B ≠ T.erase →
        Block.compatible B (Restated.newAnchor M S Sched x r n' att T).erase = true :=
    fun att hatt => Restated.gradeDescendant_at_of_confirmedSafe facts S Sched x tE hexec hmono htd hsync hmult
      tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr hinv hcross hn' hatt hQ
      (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›) (by intro v hv; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono hinv.tick (Restated.action_emod_delta facts S _) (Finset.mem_sdiff.2 ⟨mem_awake_of_awakeThroughout Sched (show v ∈ Sched.awakeThroughout (M.a S.hc S.E.Δ _ - wAttest S) (M.a S.hc S.E.Δ _) from (Finset.mem_sdiff.1 hv).1) (by linarith [twelve_delta_le_wAttest S, S.E.Δ_pos]) (le_refl _), (Finset.mem_sdiff.1 hv).2⟩))
  -- the clauses at round `r + 1` that the field `headsAtNewAnchor` reads
  have hTT' : ∀ att : V → NamedAttestation V, Restated.ActionAttestationsOf M S Sched x r n' att →
      Block.Preceq T.erase (Restated.newAnchor M S Sched x r n' att T).erase :=
    fun att hatt =>
      Restated.anchor_preceq_new_of_hypotheses_overActiveSets facts (hcross := hcross) (hjust := hjust)
        S Sched x tE hexec hmono htd
        tGAT gap hgst hlen hsync hmult hcv hthird hphase hrsW hcs hcom hw hctx hn' att hatt
  have hceil' := Restated.heightCeiling_field_of_hypotheses_overActiveSets facts S Sched x tE hexec hw hs
    hctx hn'
  have hgOld := Restated.gradeOld_of_premises facts S Sched x tE hexec hmono htd tGAT gap hgst hlen hsync
    hthird hphase hrsW hctx.1 hctx.2
    (Restated.freshSGHeadsAtLate_of_premises facts (hcross := hcross) S Sched x tE hexec hmono htd hsync hmult
      tGAT gap hgst hlen hcv hthird hphase hrsW hcs hctx.1 hctx.2
      (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›) (by intro v hv; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono hinv.tick (Restated.action_emod_delta facts S _) (Finset.mem_sdiff.2 ⟨mem_awake_of_awakeThroughout Sched (show v ∈ Sched.awakeThroughout (M.a S.hc S.E.Δ _ - wAttest S) (M.a S.hc S.E.Δ _) from (Finset.mem_sdiff.1 hv).1) (by linarith [twelve_delta_le_wAttest S, S.E.Δ_pos]) (le_refl _), (Finset.mem_sdiff.1 hv).2⟩)))
    (by intro v hv; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono hinv.tick (Restated.action_emod_delta facts S _) (Finset.mem_sdiff.2 ⟨mem_awake_of_awakeThroughout Sched (Restated.hawT_of_honRound_succ facts S Sched hv (Restated.action_mono facts S (Nat.le_succ _))) (le_refl _) (le_refl _), Restated.hwh_of_honRound_succ facts S Sched hmono hv⟩))
    (by intro v hv; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono hinv.tick (Restated.action_emod_delta facts S _) (Finset.mem_sdiff.2 ⟨mem_awake_of_awakeThroughout Sched (show v ∈ Sched.awakeThroughout (M.a S.hc S.E.Δ _ - wAttest S) (M.a S.hc S.E.Δ _) from (Finset.mem_sdiff.1 hv).1) (by linarith [twelve_delta_le_wAttest S, S.E.Δ_pos]) (le_refl _), (Finset.mem_sdiff.1 hv).2⟩))
  have hg1' := fun (att : V → NamedAttestation V)
      (hatt : Restated.ActionAttestationsOf M S Sched x r n' att) =>
    Restated.grade1_field_at_new_anchor_overActiveSets facts S Sched x (hTT' att hatt) hgOld (hGD att hatt)
  have htgt' := fun (att : V → NamedAttestation V)
      (hatt : Restated.ActionAttestationsOf M S Sched x r n' att) =>
    Restated.targetsSince_field_at_succ_ofWakes facts S Sched x hexec hw hs hinvS.tick hn' hatt
      hinvS.inPlay (hTT' att hatt)
      (fun q hq => hCN att hatt q
        (Restated.mem_honRound_of_mem_freshAttesters_ofWakes facts S Sched x hw hn' hq))
      (fun q hq => Restated.frameG2Old_of_gradeOld facts S Sched x r n'
        (Restated.newAnchor M S Sched x r n' att T) hn' (hg1' att hatt) q
        (Restated.mem_honRound_of_mem_freshAttesters_ofWakes facts S Sched x hw hn' hq))
      hinvS.heightCeiling hinvS.targetsSince
  -- the field `headsAtNewAnchor`
  obtain ⟨n'', hn''⟩ := Restated.tick_field_at_succ facts S Sched x htd (r + 1)
  have hheads : ∀ att : V → NamedAttestation V, Restated.ActionAttestationsOf M S Sched x r n' att →
      Restated.HeadsBelow M S Sched x (Restated.newAnchor M S Sched x r n' att T).erase
        ((M.opening_slot S.hc (r + 1)) + 2) := by
    intro att hatt
    have hTW' : Block.Preceq T_W.erase (Restated.newAnchor M S Sched x r n' att T).erase :=
      preceq_trans_Preceq hTW (hTT' att hatt)
    have hJ' := Restated.justified_preceq_anchor_after_switchW_ofClauses facts S Sched x tE hexec hmono
      htd tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcom hrec hprev hclear hB' hAW hnW
      (le_trans hr (Nat.le_succ r)) hn' (hceil' att hatt) (htgt' att hatt) hTW' hn''
    exact Restated.headsAtNewAnchor_of_joint facts S Sched x tE hexec hmono htd hsync hmult hcom tGAT gap
      hgst hlen hcv hthird hphase hrsW hcs hw hr hinv hcross hjust hnW hn' hn'' hatt (hTT' att hatt)
      (hceil' att hatt) hJ' hP hQ
  have hf : Restated.StepFieldsAt M S Sched x tE r n n' T := ⟨hCN, hGP, hGD, hheads⟩
  refine ⟨hf, fun att hatt => ?_⟩
  -- the invariant with the target clause since the switch round at round `r + 1`
  have hinv' : Restated.AfterPhaseInvariantOverActiveSetsSince M S Sched x (r + 1) n' n_W
      (Restated.newAnchor M S Sched x r n' att T) :=
    { tick := hn'
      inPlay := Restated.inPlay_field_of_hypotheses_overActiveSets facts S Sched x tE hctx att hatt
      anchorEntry := Restated.anchorEntry_field_of_hypotheses_overActiveSets facts S Sched x tE hctx att hatt
      band := Restated.band_field_of_hypotheses_overActiveSets facts S Sched x tE hexec hmono
        tGAT gap hgst hlen hthird hphase hrsW hctx hn' att hatt
      sg := Restated.sg_field_of_hypotheses_overActiveSets_ofFieldsAt facts (hcross := hcross) (hjust := hjust)
        S Sched x tE hexec hmono htd
        tGAT gap hgst hlen hsync hmult hcv hthird hphase hrsW hcs hcom hw hs hctx hn' hf att hatt
      sgPairwise := Restated.sgPairwise_field_of_hypotheses_overActiveSets_ofFieldsAt facts (hcross := hcross)
        (hjust := hjust) S Sched x tE hexec hmono htd
        tGAT gap hgst hlen hsync hmult hcv hthird hphase hrsW hcs hcom hw hs hctx hn' hf
      heads := Restated.heads_field_of_hypotheses_overActiveSets_ofFieldsAt facts S Sched x tE hf att hatt
      fin := Restated.fin_field_of_hypotheses_overActiveSets_ofFieldsAt facts (hcross := hcross) (hjust := hjust)
        S Sched x tE hexec hmono htd
        tGAT gap hgst hlen hsync hmult hcv hthird hphase hrsW hcs hcom hw hs hctx hn' hf att hatt
      -- the grade test's outcome `b` with `b = true`
      grade1 := fun w hw' p hp m hm B b hb hbt =>
        Restated.grade1_field_of_hypotheses_overActiveSets_ofFieldsAt facts (hcross := hcross)
          (hjust := hjust) S Sched x tE hexec hmono htd
          tGAT gap hgst hlen hsync hmult hcv hthird hphase hrsW hcs hcom hw hctx hn' hf att hatt
          w hw' p hp m hm B (hbt ▸ hb)
      heightCeiling := hceil' att hatt
      targetsTop := Restated.targetsTop_field_of_hypotheses_overActiveSets_ofFieldsAt facts (hcross := hcross)
        (hjust := hjust) S Sched x tE hexec hmono htd
        tGAT gap hgst hlen hsync hmult hcv hthird hphase hrsW hcs hcom hw hs hctx hn' hf att hatt
      targetsSince := htgt' att hatt }
  -- the three clauses about round `r` at round `r + 1`
  have hG : ∀ v ∈ Restated.HonRound M S Sched (r + 1), ∀ p : Protocol.Phase,
      M.domain S.E S.hc (r + 1) p ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) →
      ∀ m : Nat, Restated.stepBeforeInstant M x m (M.domain S.E S.hc (r + 1) p) →
      ∀ B : Block V, ∀ b : Bool,
      M.gradeBool S.E (M.gradeView (M.toHealing (x[m][v].st).st.core))
          (x[m][v].st).st.core.F S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) p)
          (M.late S.E S.hc (r + 1) p) B ⇢ b → b = true →
      ∃ v_1 ∈ Restated.HonRound M S Sched r, ∃ a : NamedAttestation V,
        a.round = r ∧ a.val_index = v_1 ∧
        (⟨v_1, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n + 1].sent ∧
        ∃ C : NamedBlock V, C ∈ (x[n + 1][v_1].st).st.bodies ∧ a.confirmed = some C.root ∧
          Block.Preceq B C.erase :=
    fun v hv p hdom m hm B b hB hb => by
      subst hb
      exact Restated.graded_preceq_freshSG_of_premises facts (hcross := hcross) S Sched x tE hexec hmono
        htd hsync hmult tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr hinv hv hdom hm B hB
        (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›) (by intro v hv; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono hinv.tick (Restated.action_emod_delta facts S _) (Finset.mem_sdiff.2 ⟨mem_awake_of_awakeThroughout Sched (show v ∈ Sched.awakeThroughout (M.a S.hc S.E.Δ _ - wAttest S) (M.a S.hc S.E.Δ _) from (Finset.mem_sdiff.1 hv).1) (by linarith [twelve_delta_le_wAttest S, S.E.Δ_pos]) (le_refl _), (Finset.mem_sdiff.1 hv).2⟩))
  exact ⟨joint_of_prevTick_stepActiveJoint facts hinv' hinv.tick hP hQ hG, hTT' att hatt⟩

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

/-- If the joint invariant holds at the switch round with tick step `n_W`, switch step `n_W` and
    anchor `T_W`, and from every round at or after the switch round whose anchor is `T_W` or a
    descendant of it the joint invariant carries to the next round with an anchor that is the
    round's anchor or a descendant of it, then for every `k` the joint invariant holds at round
    `switchRound S tE + k` with switch step `n_W` and an anchor that is `T_W` or a descendant of it. -/
theorem afterPhaseInvariantOverActiveSetsJoint_of_stepFrom (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) {n_W : Nat} {T_W : NamedBlock V}
    (hbase : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x (Restated.switchRound M S tE) n_W n_W T_W)
    (hstep : ∀ (r : Round) (n : Nat) (T : NamedBlock V), Restated.switchRound M S tE ≤ r →
      Block.Preceq T_W.erase T.erase →
      Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x r n n_W T →
      ∃ (n' : Nat) (T' : NamedBlock V),
        Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x (r + 1) n' n_W T' ∧
          Block.Preceq T.erase T'.erase) :
    ∀ k : Nat, ∃ (n : Nat) (T : NamedBlock V),
      Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x (Restated.switchRound M S tE + k) n n_W T ∧
        Block.Preceq T_W.erase T.erase := by
  intro k
  induction k with
  | zero => exact ⟨n_W, T_W, hbase, (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _))⟩
  | succ k ih =>
    obtain ⟨n, T, hJ, hT⟩ := ih
    obtain ⟨n', T', hJ2, hTT'⟩ := hstep (Restated.switchRound M S tE + k) n T (Nat.le_add_right _ _) hT hJ
    exact ⟨n', T', hJ2, preceq_trans_Preceq hT hTT'⟩

end

end DecoupledConsensusModel.Sts.Restated
