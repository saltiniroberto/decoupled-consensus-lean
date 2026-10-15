import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bPhaseSleepiness
import Proofs.Claims.Restated.Claim13bStepActionF
import Proofs.Claims.Restated.Claim13bStepAnchor
import Proofs.Claims.Restated.Claim13bStepAssembly
import Proofs.Claims.Restated.Claim13bStepFin
import Proofs.Claims.Restated.Claim13bStepGrade
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bStepQuorum
import Proofs.Claims.Restated.Projection
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActiveTop
import Model.Conditions.Claim13bK_FinBeforeTick
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13bStepAnchor
import Model.Conditions.Claim13bStepAssembly
import Model.Conditions.Claim13bStepGrade
import Model.Conditions.Claim13bStepKitTick
import Model.Conditions.Claim13bStepSG
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring
import Proofs.Claims.Restated.Claim13bStepFinRule

/-!
# Finalized blocks before the next round's tick

Tick-step ordering facts, and that up to the round-`(r + 1)` tick step every honest finalized block,
and the finalized block of every honest round-`(r + 1)` action read, is an ancestor of the round-`r`
anchor; with the finality and `targetsTop` clauses at round `r + 1`. Stated over a model
`M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If step `k` is the tick at `S.a ρ`, step `n'` is the tick at `S.a (r + 1)`, and `k < n'`, then
    `ρ ≤ r`. -/
theorem round_le_of_tick_lt (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {k n' : Nat} {ρ r : Round}
    (hk : Restated.tickStepAt M x k ((Restated.Vocabulary.Execution.Setup.a M S ρ))) (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1)))) (hlt : k < n') :
    ρ ≤ r := by
  have hle : ρ ≤ r + 1 := Restated.round_le_of_tick_le facts S Sched x hk hn' (Nat.le_of_lt hlt)
  rcases Nat.lt_or_ge ρ (r + 1) with h | h
  · exact Nat.le_of_lt_succ h
  · have heq : ρ = r + 1 := le_antisymm hle h
    subst heq
    exact absurd (Restated.tickStepAt_unique facts x hk hn') (Nat.ne_of_lt hlt)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If `m` is the last step strictly before `c`, step `n'` is the tick at `t`, and `c ≤ t`, then
    `m ≤ n'`. -/
theorem stepBefore_le_tick (facts : Record.Facts M) {S : Setup V} {Sched : Schedule V}
    (x : AtomicExec (Record.protocolOf M S) Sched) {c t : Int} {m n' : Nat}
    (hm : Restated.stepBeforeInstant M x m c) (hn' : Restated.tickStepAt M x n' t) (hc : c ≤ t) : m ≤ n' := by
  by_contra hcon
  have hlt : n' < m := Nat.lt_of_not_le hcon
  have h1 : (x[n' + 1].time : Int) < c := hm.1 n' hlt
  have h2 : (x[n' + 1].time : Int) = t := (Restated.tickStepAt_time facts x hn').1
  linarith

end

section
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The action time of round `ρ` is at or before the opening of round `ρ + 1`. -/
private theorem action_le_opening_succ_of_facts (facts : Record.Facts M) (S : Setup V) (ρ : Round) :
    (Restated.Vocabulary.Execution.Setup.a M S ρ) ≤ M.opening S.E S.hc (ρ + 1) := by
  have h1 := facts.gr.action_delta_le_early S S.hc.R_ge_three (Nat.lt_succ_self ρ)
  have h2 := facts.gr.early_g2_le_opening S (ρ + 1)
  have hd := S.E.Δ_pos
  show M.a S.hc S.E.Δ _ ≤ _
  linarith

/-- From any node state `before`, validator `v`'s round-`r` action read can compute some
    attestation. -/
private theorem actionAttestationFrom_nonempty_fbt (facts : Record.Facts M) (S : Setup V)
    (before : M.N) (v : V) (r : Round) :
    ∃ a, a ∈ Restated.actionAttestationFrom M S before v r := by
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc before.st.core.toHealing
    (Restated.Vocabulary.Execution.Setup.a M S r) before.cache
  obtain ⟨st, hst⟩ := facts.dt.duties_update_confirmation_with_nonempty (M.gradeContract c) S.E S.hc
    (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r))
    (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1)
  obtain ⟨D, hD⟩ := facts.dt.attest_with_nonempty (M.gradeContract (M.mkNode st before.record c).cache)
    S.E S.hc (S.node v) (M.mkNode st before.record c).st (M.mkNode st before.record c).record
  exact ⟨D.2.2, M.mkNode st before.record c, ⟨c, hc, st, hst, rfl⟩, D.1, D.2.1, hD⟩

/-- If `a` equals every attestation validator `q`'s round-`ρ` action read from `before` can compute,
    then `a`'s validator index is `q`. -/
private theorem val_index_of_eq_every_fbt (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (q : V) (ρ : Round) (a : NamedAttestation V)
    (heq : ∀ a' ∈ Restated.actionAttestationFrom M S before q ρ, a = a') :
    a.val_index = q := by
  obtain ⟨a₁, ha₁⟩ := actionAttestationFrom_nonempty_fbt facts S before q ρ
  rw [heq a₁ ha₁]
  exact Restated.actionAttestationFrom_val_index facts S before q ρ a₁ ha₁

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If the reshaped invariant holds at round `r` with tick step `n` and anchor `T`, step `n'` is the
    tick at `S.a (r + 1)`, and `roundSleepinessW` holds from a time `tE` at or before round
    `r + 1`'s opening, then the finalized block of a validator honest through its own read, at any
    step up to `n'`, is an ancestor of `T`. -/
theorem fin_old_anchor_before_succ_tick (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) {tE : Int}
    (hrsW : Restated.roundSleepinessW M S Sched tE)
    {r : Round} {n n' : Nat} {T : NamedBlock V}
    (hinv : Restated.AfterPhaseInvariantOverActiveSetsTop M S Sched x r n T)
    (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    (htE : tE ≤ M.opening S.E S.hc (r + 1))
    (hcross : Restated.StepFinalizedCrossingUnderAnchor M S Sched x r n' T) :
    ∀ (v : V) (n₁ : Nat), n₁ ≤ n' → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.F T.erase := by
  classical
  intro v n₁ hn₁ hv
  by_cases hsmall : n₁ ≤ n + 1
  · exact hinv.fin v n₁ hsmall hv
  by_cases hlow : ((x[n₁][v].st).st.core.σ (x[n₁][v].st).st.core.F).h
      < (M.derive_named S.E S.cfg T).h
  · exact hcross v n₁ (Nat.le_succ_of_le hn₁) hv hlow
  · have hbig : n + 1 ≤ n₁ := Nat.le_of_lt (Nat.lt_of_not_le hsmall)
    have hvn : Restated.HonestThrough M Sched x (n + 1) v := by
      intro t ht
      exact hv t (le_trans ht (Restated.time_mono_int facts S Sched x hbig))
    have htime : (x[n₁].time : Int) ≤ M.opening S.E S.hc (r + 1 + 1) := by
      refine le_trans (Restated.time_mono_int facts S Sched x (Nat.le_succ_of_le hn₁)) ?_
      rw [(Restated.tickStepAt_time facts x hn').1]
      exact action_le_opening_succ_of_facts facts S (r + 1)
    rcases Restated.finalized_honest_target_ofRoundSleepinessW facts S Sched x hexec hmono hrsW (r₀ := r + 1)
      (Nat.le_add_left 1 r) htE hv htime with
      hgen | ⟨X, q, a, k, tmo, hXmem, hFX, hkn₁, htick, hawk, hqk, -, heq, hsent, hpair⟩
    · rw [hgen]
      exact (preceq_eq_true_iff_Preceq.mp (Protocol.preceq_genesis _))
    · refine preceq_trans_Preceq hFX ?_
      have hround : a.round ≤ r :=
        Restated.round_le_of_tick_lt facts S Sched x htick hn' (Nat.lt_of_lt_of_le hkn₁ hn₁)
      have hkn : k ≤ n := Restated.tick_le_of_round_le facts S Sched x htick hinv.tick hround
      have hstep : k + 1 ≤ n + 1 := Nat.succ_le_succ hkn
      have hidx : a.val_index = q :=
        val_index_of_eq_every_fbt facts (Setup.alwaysAwake S) _ q a.round a heq
      have hh := hinv.heightCeiling q (k + 1) a _ X.root tmo hstep hqk hidx hsent hpair
      have heqh : ((x[n₁][v].st).st.core.σ (x[n₁][v].st).st.core.F).h
          = (M.derive_named S.E S.cfg T).h := le_antisymm hh (Nat.le_of_not_lt hlow)
      rw [heqh] at hpair
      exact hinv.targetsTop q (k + 1) a X.root tmo hstep hqk hidx hsent hpair X
        (Restated.blockInLog_of_mem_bodies facts S Sched hv hXmem) rfl

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If round `r` is at or after the switch round, the reshaped invariant holds at round `r` with
    tick step `n` and anchor `T`, step `n'` is the tick at `S.a (r + 1)`, and the phase
    premises about `tGAT`, the one-third bound, the phase-awake condition and
    `roundSleepinessW` hold, then the finalized block of a validator honest through its own read, at
    any step up to `n'`, is an ancestor of `T`. -/
theorem fin_old_anchor_before_succ_tick_of_hypotheses (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE)
    {r : Round} {n n' : Nat} {T : NamedBlock V}
    (hr : Restated.switchRound M S tE ≤ r) (hinv : Restated.AfterPhaseInvariantOverActiveSetsTop M S Sched x r n T)
    (hcross : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepFinalizedCrossingUnderAnchor M S Sched x r n'' T)
    (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1)))) :
    ∀ (v : V) (n₁ : Nat), n₁ ≤ n' → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.F T.erase :=
  Restated.fin_old_anchor_before_succ_tick facts S Sched x hexec hmono (tE := Restated.switchOpening M S tE)
    (Restated.roundSleepinessW_switchOpening_of_phase facts S Sched tGAT tE gap hgst hlen hmono hthird hphase
      hrsW)
    hinv hn' (Restated.switchOpening_le_opening facts S (le_trans hr (Nat.le_succ r))) (hcross n' hn')

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If every honest finalized block up to the round-`(r + 1)` tick step `n'` is an ancestor of `T`,
    then for every validator the adversary holds at no time up to `S.a (r + 1)`, every healing store
    its round-`(r + 1)` action read can compute has a finalized block that is an ancestor of `T`. -/
theorem actionF_preceq_old_anchor (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {r : Round} {n' : Nat} {T : NamedBlock V}
    (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    (hfin : ∀ (v : V) (n₁ : Nat), n₁ ≤ n' → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.F T.erase) :
    ∀ v ∈ honestThroughSet Sched ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))),
      ∀ hs ∈ Restated.actionHealingStore M S (x[n'][v].st) (r + 1),
        Block.Preceq (hs : M.HS).F T.erase := by
  intro v hv hs hhs
  rw [Restated.actionHealingStore_F facts S _ _ hs hhs]
  refine hfin v n' le_rfl ?_
  have hvT : HonestThroughTime Sched ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) v := mem_honestThroughSet.mp hv
  have htn : (x[n'].time : Int) ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) := by
    rw [← (Restated.tickStepAt_time facts x hn').1]
    exact Restated.time_mono_int facts S Sched x (Nat.le_succ n')
  intro t ht
  exact hvT t (le_trans ht htn)

end

end DecoupledConsensusModel.Sts.Restated
