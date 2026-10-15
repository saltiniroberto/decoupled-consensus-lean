import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bK_ConfirmedAgree
import Proofs.Claims.Restated.Claim13bK_ConfirmedRecord
import Proofs.Claims.Restated.Claim13bK_ConfirmedSettle
import Proofs.Claims.Restated.Claim13bK_ConfirmedWake
import Proofs.Claims.Restated.Claim13bStepConeIter
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bW_Schedule
import Proofs.Claims.Restated.Projection
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActiveJoint
import Model.Conditions.Claim13bInvariantActiveSinceW
import Model.Conditions.Claim13bK_ConfirmedSettle
import Model.Conditions.Claim13bK_ConfirmedWake
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
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
import Model.Conditions.Sts_Spec2Claims_ClaimConfirmedAfterHealing
import Model.Conditions.Sts_Spec2Claims_ClaimStableLiveAfterHealing
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bK_StableRecord

/-!
# The stable output only extends after the settle instant

From the settle instant on, an honest validator's stable record, finalized block and stable output
are ancestors of every later honest head, and its stable output only extends; stated over a model
`M : Record.Model V`.
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

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If step `n_b` is the sts tick at instant `t` and the configuration after `i` steps is at or
    after `t`, then `n_b + 1 ≤ i`. -/
theorem succ_le_of_tickStepAt_le (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {n_b i : Nat} {t : Int} (hn_b : Restated.tickStepAt M x n_b t)
    (hi : t ≤ (x[i].time : Int)) : n_b + 1 ≤ i := by
  obtain ⟨-, hnb0⟩ := Restated.tickStepAt_time facts x hn_b
  by_contra hcon
  have := Restated.time_mono_int facts S Sched x (Nat.le_of_lt_succ (Nat.lt_of_not_le hcon))
  linarith

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- At the sts tick at slot `s`'s confirmation instant, for a validator `v` awake there, outside the
    adversary's set, whose tick there has an outcome and whose staged node state passes the grade-2
    awake test of slot `s + 1`'s round: if the stable root its confirmation update can read under
    one outcome of the cache update is a descendant of `X` or `X` itself, then `v`'s `latest_stable`
    after the tick is a descendant of `X` or `X` itself. -/
theorem latest_stable_preceq_of_stableRoot (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {n : Nat} {s : Slot}
    (hn : Restated.tickStepAt M x n (M.confirmation_time S.E s)) {v : V}
    (haw : v ∈ Sched.awake (M.confirmation_time S.E s) \
      Sched.adv (M.confirmation_time S.E s))
    {G X : Block V}
    {c : M.Cache} (hc : M.onPhaseTick S.E S.hc (M.toHealing (x[n][v].st).st.core)
      (M.confirmation_time S.E s) (x[n][v].st).cache ⇢ c)
    (hG : (M.gradeContract c).stableRoot S.E S.hc
          (M.toHealing (M.ns_setClock S.E (x[n][v].st).st
            (M.confirmation_time S.E s)).core)
          ((M.round_of S.hc) (M.ns_setClock S.E (x[n][v].st).st
            (M.confirmation_time S.E s)).core.s) ⇢ some G)
    (hXG : Block.Preceq X G)
    (hneTick : ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched (M.confirmation_time S.E s) x[n] v) (M.confirmation_time S.E s) ⇢ out)
    (hrun : M.awake_for_grade2 (Setup.alwaysAwake S) v
      (Record.wakeStage M Sched (M.confirmation_time S.E s) x[n] v) (M.round_of S.hc (s + 1))) :
    Block.Preceq X (x[n + 1][v].st).st.core.latest_stable := by
  obtain ⟨G', hG', hstab, -⟩ := Restated.records_after_confirmation_tick facts S Sched x hn haw
    hneTick hrun c hc (some G) hG
  have hGG : G' = G := (Option.some.inj hG').symm
  rw [hstab, hGG]
  exact preceq_trans_Preceq hXG (facts.hd.preceq_advance_confirmed_candidate _ _)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- On an sts execution whose clock diverges, under `committeeSleepinessW` from `tE` and when every
    tick of an awake honest validator has an outcome: if `v`'s `latest_stable` after `k` and after
    `k + 1` steps is an ancestor of every honest head from two slots after the configuration's slot
    on, and `v`'s finalized block after `k + 1` steps is an ancestor of every honest head from some
    slot `s_F` on, then `v`'s `get_stable` after `k` steps is an ancestor of its `get_stable` after
    `k + 1` steps. -/
theorem get_stable_succ_preceq (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (htd : Restated.TimeDiverges M x) {tE : Int}
    (hcs : Restated.committeeSleepinessW M S Sched tE) (v : V) (k : Nat) {s_F : Slot}
    (hpre : Restated.AncestorOfHonestHeadsFrom M S Sched x (x[k][v].st).st.core.latest_stable
      (S.E.slotOf (x[k].time : Int) + 2))
    (hpost : Restated.AncestorOfHonestHeadsFrom M S Sched x (x[k + 1][v].st).st.core.latest_stable
      (S.E.slotOf (x[k + 1].time : Int) + 2))
    (hF : Restated.AncestorOfHonestHeadsFrom M S Sched x (x[k + 1][v].st).st.core.F s_F)
    (hnr : ∀ (k τ : Nat) (u : V), x.lbl k = AtomicAction.tickAllAwake τ →
      (τ : Int) % S.E.Δ = 0 → u ∈ Sched.awake (τ : Int) \ Sched.adv (τ : Int) →
      (∀ t' ≤ (τ : Int), u ∉ Sched.adv t') →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) u (Record.wakeStage M Sched (τ : Int) x[k] u) (τ : Int) ⇢ out) :
    Block.Preceq (M.get_stable (x[k][v].st).st.core)
      (M.get_stable (x[k + 1][v].st).st.core) := by
  have hL := preceq_of_compatible_of_eq_or_not_preceq
    (Restated.compatible_of_ancestorOfHonestHeadsFrom_after facts S Sched x htd hcs hpre hpost)
    (Restated.records_succ_eq_or_not_preceq facts S Sched x v k hnr).1
  exact facts.hd.get_stable_preceq_of_fields _ _ (Restated.F_mono_succ facts S Sched x v k) hL
    (Restated.compatible_of_ancestorOfHonestHeadsFrom_after facts S Sched x htd hcs hF hpost)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- On an sts execution whose clock diverges, under `committeeSleepinessW` from `tE` and when every
    tick of an awake honest validator has an outcome: if `i ≤ j`, `v`'s `latest_stable` at every
    step `k` from `i` to `j` is an ancestor of every honest head from slot `slot(x[k].time) + 2` on,
    and `v`'s finalized block is too at every step `k` with `i < k ≤ j`, then `v`'s `get_stable`
    after `i` steps is an ancestor of its `get_stable` after `j` steps. -/
theorem get_stable_preceq_of_records_along (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (htd : Restated.TimeDiverges M x) {tE : Int}
    (hcs : Restated.committeeSleepinessW M S Sched tE) (v : V) {i j : Nat} (hij : i ≤ j)
    (hrec : ∀ k : Nat, i ≤ k → k ≤ j →
      Restated.AncestorOfHonestHeadsFrom M S Sched x (x[k][v].st).st.core.latest_stable
        (S.E.slotOf (x[k].time : Int) + 2))
    (hF : ∀ k : Nat, i < k → k ≤ j →
      Restated.AncestorOfHonestHeadsFrom M S Sched x (x[k][v].st).st.core.F
        (S.E.slotOf (x[k].time : Int) + 2))
    (hnr : ∀ (k τ : Nat) (u : V), x.lbl k = AtomicAction.tickAllAwake τ →
      (τ : Int) % S.E.Δ = 0 → u ∈ Sched.awake (τ : Int) \ Sched.adv (τ : Int) →
      (∀ t' ≤ (τ : Int), u ∉ Sched.adv t') →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) u (Record.wakeStage M Sched (τ : Int) x[k] u) (τ : Int) ⇢ out) :
    Block.Preceq (M.get_stable (x[i][v].st).st.core)
      (M.get_stable (x[j][v].st).st.core) := by
  suffices key : ∀ n : Nat, i ≤ n → n ≤ j →
      Block.Preceq (M.get_stable (x[i][v].st).st.core)
        (M.get_stable (x[n][v].st).st.core) from key j hij le_rfl
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => intro _; exact preceq_eq_true_iff_Preceq.mp (Block.preceq_self _)
  | succ n hin ih =>
    intro hnj
    exact preceq_trans_Preceq (ih (Nat.le_of_succ_le hnj))
      (Restated.get_stable_succ_preceq facts S Sched x htd hcs v n
        (hrec n hin (Nat.le_of_succ_le hnj)) (hrec (n + 1) (Nat.le_succ_of_le hin) hnj)
        (hF (n + 1) (Nat.lt_succ_of_le hin) hnj) hnr)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Under the run's premises, the joint invariant at the switch round and
    `RecordsSettledAtSettleTick`, if the configuration after `k` steps is at or after
    `confirmedSettleTime S tE` and `v` is honest through it, then `v`'s `latest_stable`, its
    finalized block and its `get_stable` after `k` steps are each an ancestor of every honest head
    from slot `slot(x[k].time) + 2` on. -/
theorem get_stable_ancestorOfHonestHeads_after_settle (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (hcatch : Restated.CatchUpOnWake M S x) (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (hsync : Restated.SynchronyFromWake M S x) (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight) (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t) (hrsW : Restated.roundSleepinessW M S Sched tE) (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT) (hcs : Restated.committeeSleepinessW M S Sched tE) (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched)) (hw : Restated.WakesAtActionInstants M S Sched) (hs : Restated.SleepsAfterActionInstants M S Sched) (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap) (hprev : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
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
    (hsettle : Restated.RecordsSettledAtSettleTick M S Sched x tE)
    {k : Nat} (hk : Restated.confirmedSettleTime M S tE ≤ (x[k].time : Int)) {v : V}
    (hv : Restated.HonestThrough M Sched x k v) :
    Restated.AncestorOfHonestHeadsFrom M S Sched x (x[k][v].st).st.core.latest_stable
        (S.E.slotOf (x[k].time : Int) + 2) ∧
      Restated.AncestorOfHonestHeadsFrom M S Sched x (x[k][v].st).st.core.F
        (S.E.slotOf (x[k].time : Int) + 2) ∧
      Restated.AncestorOfHonestHeadsFrom M S Sched x (M.get_stable (x[k][v].st).st.core)
        (S.E.slotOf (x[k].time : Int) + 2) := by
  obtain ⟨n_b, hn_b⟩ := Restated.tick_field_at_succ facts S Sched x htd (Restated.switchRound M S tE)
  have hkb : n_b + 1 ≤ k := Restated.succ_le_of_tickStepAt_le facts S Sched x hn_b hk
  have hL := (Restated.records_ancestorOfHonestHeads_after_settleTick facts S Sched x tE hexec hmono htd hcatch
    tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec hprev hclear hB'
    hnW hAW hJswitch hTW₀ hJ₀ hsettle hn_b v k hkb hv).1
  have hts : (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)) ≤ (x[k].time : Int) :=
    le_trans (Restated.action_mono facts S (Nat.le_succ _)) hk
  have hF := Restated.finalized_ancestorOfHonestHeadsFrom facts S Sched x tE hexec hmono htd hcatch tGAT gap
    hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec hprev hclear hB' hnW hAW
    hJswitch le_rfl hTW₀ hJ₀ hts hv
  exact ⟨hL, hF, Restated.ancestorOfHonestHeadsFrom_get_stable facts S Sched x _ hL hF⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Under the run's premises, the joint invariant at the switch round and
    `RecordsSettledAtSettleTick`: at the sts tick at the confirmation instant of a slot `s` at or
    after `confirmedSettleTime S tE`, for a validator `v` awake there, outside the adversary's set,
    honest through the configuration after the tick, and whose staged node state passes the grade-2
    awake test of slot `s + 1`'s round, if the stable root its confirmation update can read is a
    descendant of `X` or `X` itself, then `v`'s `latest_stable` and its `get_stable` after the tick
    are each a descendant of `X` or `X` itself. -/
theorem stable_records_preceq_after_confirmation_tick (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (hcatch : Restated.CatchUpOnWake M S x) (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (hsync : Restated.SynchronyFromWake M S x) (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight) (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t) (hrsW : Restated.roundSleepinessW M S Sched tE) (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT) (hcs : Restated.committeeSleepinessW M S Sched tE) (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched)) (hw : Restated.WakesAtActionInstants M S Sched) (hs : Restated.SleepsAfterActionInstants M S Sched) (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap) (hprev : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
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
    (hsettle : Restated.RecordsSettledAtSettleTick M S Sched x tE)
    {n : Nat} {s : Slot} (hn : Restated.tickStepAt M x n (M.confirmation_time S.E s))
    (hts : Restated.confirmedSettleTime M S tE ≤ M.confirmation_time S.E s) {v : V}
    (haw : v ∈ Sched.awake (M.confirmation_time S.E s) \
      Sched.adv (M.confirmation_time S.E s))
    (hvh : Restated.HonestThrough M Sched x (n + 1) v)
    {G X : Block V}
    {c : M.Cache} (hc : M.onPhaseTick S.E S.hc (M.toHealing (x[n][v].st).st.core)
      (M.confirmation_time S.E s) (x[n][v].st).cache ⇢ c)
    (hG : (M.gradeContract c).stableRoot S.E S.hc
          (M.toHealing (M.ns_setClock S.E (x[n][v].st).st
            (M.confirmation_time S.E s)).core)
          ((M.round_of S.hc) (M.ns_setClock S.E (x[n][v].st).st
            (M.confirmation_time S.E s)).core.s) ⇢ some G)
    (hXG : Block.Preceq X G)
    (hrun : M.awake_for_grade2 (Setup.alwaysAwake S) v
      (Record.wakeStage M Sched (M.confirmation_time S.E s) x[n] v) (M.round_of S.hc (s + 1))) :
    Block.Preceq X (x[n + 1][v].st).st.core.latest_stable ∧
      Block.Preceq X (M.get_stable (x[n + 1][v].st).st.core) := by
  have hdvd : M.confirmation_time S.E s % S.E.Δ = 0 := by
    rw [facts.sch.confirmation_time_eq_support_cutoff_succ]
    exact facts.sch.support_cutoff_emod_delta S (s + 1)
  have hLX := Restated.latest_stable_preceq_of_stableRoot facts S Sched x hn haw hc hG hXG
    (Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono hn hdvd haw)
    hrun
  have hk : Restated.confirmedSettleTime M S tE ≤ (x[n + 1].time : Int) := by
    rw [(Restated.tickStepAt_time facts x hn).1]; exact hts
  obtain ⟨hL, hF, -⟩ := Restated.get_stable_ancestorOfHonestHeads_after_settle facts S Sched x tE hexec hmono
    htd hcatch tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec hprev
    hclear hB' hnW hAW hJswitch hTW₀ hJ₀ hsettle hk hvh
  exact ⟨hLX, preceq_trans_Preceq hLX
    (facts.hd.get_stable_upper _ (Restated.compatible_of_ancestorOfHonestHeadsFrom_after facts S Sched x htd hcs hF hL)).2⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Under the run's premises, the joint invariant at the switch round and
    `RecordsSettledAtSettleTick`, no honest validator's stable output ever retreats from
    `confirmedSettleTime S tE` on, whether or not it is awake: at the later of two reads it is a
    descendant of the one held at the earlier. -/
theorem stableOnlyExtendsAfterHealing_of_settle (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (hcatch : Restated.CatchUpOnWake M S x) (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (hsync : Restated.SynchronyFromWake M S x) (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight) (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t) (hrsW : Restated.roundSleepinessW M S Sched tE) (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT) (hcs : Restated.committeeSleepinessW M S Sched tE) (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched)) (hw : Restated.WakesAtActionInstants M S Sched) (hs : Restated.SleepsAfterActionInstants M S Sched) (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap) (hprev : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
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
    (hsettle : Restated.RecordsSettledAtSettleTick M S Sched x tE) :
    Restated.StableOnlyExtendsAfterHealing M S Sched x (Restated.confirmedSettleTime M S tE) := by
  intro v i j hij hvj hti
  have hvk : ∀ k : Nat, k ≤ j → Restated.HonestThrough M Sched x k v := fun k hkj t' h =>
    hvj t' (le_trans h (Restated.time_mono_int facts S Sched x hkj))
  have hk : ∀ k : Nat, i ≤ k → Restated.confirmedSettleTime M S tE ≤ (x[k].time : Int) := fun k hik =>
    le_trans hti (Restated.time_mono_int facts S Sched x hik)
  refine Restated.get_stable_preceq_of_records_along facts S Sched x htd hcs v hij (fun k hik hkj => ?_)
    (fun k hik hkj => ?_) (facts.ndRun.tick_outcome_sts S Sched x hexec.idealization.root_injective hexec.honestRootsNew)
  · exact (Restated.get_stable_ancestorOfHonestHeads_after_settle facts S Sched x tE hexec hmono htd hcatch tGAT
      gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec hprev hclear hB' hnW
      hAW hJswitch hTW₀ hJ₀ hsettle (hk k hik) (hvk k hkj)).1
  · exact (Restated.get_stable_ancestorOfHonestHeads_after_settle facts S Sched x tE hexec hmono htd hcatch tGAT
      gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec hprev hclear hB' hnW
      hAW hJswitch hTW₀ hJ₀ hsettle (hk k (le_of_lt hik)) (hvk k hkj)).2.1

end

end DecoupledConsensusModel.Sts.Restated
