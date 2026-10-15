import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13b
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13beRoute3_21
import Proofs.Claims.Restated.Claim13beRoute3_44
import Proofs.Claims.Restated.Claim13beRoute3_44UpTo
import Proofs.Claims.Restated.Claim13beRoute3_45
import Proofs.Claims.Restated.Claim13beRoute3_50
import Proofs.Claims.Restated.Claim13beRoute3_71
import Proofs.Claims.Restated.Claim13beRoute3_71UpTo
import Proofs.Claims.Restated.Claim13beRoute3_72
import Proofs.Claims.Restated.RunAll
import Proofs.Claims.Restated.Vocabulary_Execution_EmissionShape
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_Ladder
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActive
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.Claim13beRoute3_72
import Model.Conditions.ClaimAsyncK_DeliveryUpTo
import Model.Conditions.RunAll
import Model.Conditions.RunVocabulary
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13bd
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_ModelVocabulary_Healing_Schedule
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring

/-!
# The regime at the switch round, with synchrony up to a step

The band bound and the run-scoped regime seeded at the highest honest row, at a round of the phase
and at the switch round, with synchrony only up to `x[N].time`, stated over a model
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
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- With synchrony only up to `x[N].time`: under the theorem's hypotheses, with `n₀` the tick step
    at round `r`'s action instant and `N` a step at or after `n₀ + 1` whose time is at most
    `tAwakeEnd` and at least `S.a r`, the largest `Σ.h_max` an honest active attester of round `r`
    holds after `n₀` steps, minus one, is at most `topHonestRow S Sched x n₀`. -/
theorem hmaxRoundAt_sub_one_le_topHonestRow_atRound_upTo (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v : V)
    {tGAT tAwakeEnd : Int} {N : Nat}
    (hsync : Restated.SynchronyFromWakeBefore M S x (x[N].time : Int)) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tAwakeEnd → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tAwakeEnd →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    {r : Round} {n₀ : Nat} (hn₀ : Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S r)))
    (hn₀N : n₀ + 1 ≤ N) (hn : (x[N].time : Int) ≤ tAwakeEnd)
    (hrWN : (Restated.Vocabulary.Execution.Setup.a M S (r)) ≤ (x[N].time : Int)) :
    Restated.hmaxRoundAt M S Sched x (r) n₀ - 1 ≤ Restated.topHonestRow M S Sched x n₀ := by
  have hf := Restated.admissibleFieldsOn_runAll_notHeld_upTo facts S Sched x v N hsync hmono hawake hgst hcv hvalid
    hawm hthird hn
  have hHs : ∀ t t' : Int, t ≤ t' → notHeldAt Sched t' ⊆ notHeldAt Sched t :=
    fun _ _ h => notHeldAt_anti hmono h
  have hbelow := Restated.belowOneThirdOn_runAll_notHeld facts S Sched x v N hthird hn
  obtain ⟨hn₀1, -⟩ := Restated.tickStepAt_time facts x hn₀
  have hsup : Restated.hmaxRoundAt M S Sched x (r) n₀
      ≤ Restated.topHonestRow M S Sched x n₀ + 1 := by
    unfold Restated.hmaxRoundAt
    refine Finset.sup_le fun u _ => ?_
    show (x[n₀][u].st).st.core.h_max ≤ Restated.topHonestRow M S Sched x n₀ + 1
    by_cases hlarge : 1 < (x[n₀][u].st).st.core.h_max
    · have hread : Restated.runAllPath M S Sched x v N
          (Restated.strictEventIndex
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
            ((Restated.Vocabulary.Execution.Setup.a M S (r)))) u = x[n₀][u].st :=
        Restated.stateBeforeTime_runAll_tick facts S Sched x v hn₀ hn₀N u
      have hlarge' : 1 < (Restated.runAllPath M S Sched x v N
          (Restated.strictEventIndex
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
            ((Restated.Vocabulary.Execution.Setup.a M S (r)))) u).st.h_max := by
        rw [hread]; exact hlarge
      obtain ⟨b, tb, hb, hemit, htb, hrow, -⟩ :=
        Restated.frontier_confirmationWitnessOn facts (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ hf
          hHs (fun _ => Finset.subset_univ _)
          (honestWeightMajorityOn_of_belowOneThirdOn hbelow) hrWN hlarge'
      rw [hread] at hrow
      obtain ⟨k, -, hk, hsent⟩ := Restated.mem_sent_of_emits_runAll facts S Sched x v hemit
      obtain ⟨hk1, -⟩ := Restated.tickStepAt_time facts x hk
      have hkn : k + 1 ≤ n₀ + 1 := by
        by_contra hcon
        have hmono' : ((x[n₀ + 1].time : Nat) : Int) ≤ ((x[k + 1].time : Nat) : Int) := by
          exact_mod_cast Restated.time_mono facts S Sched x (by omega)
        have : (Restated.Vocabulary.Execution.Setup.a M S (r)) ≤ tb := by
          rw [← hn₀1, ← hk1]; exact hmono'
        exact absurd htb (not_lt.mpr this)
      have hbk : b.val_index ∈ Finset.univ \ Sched.adv (x[k + 1].time : Int) := by
        rw [hk1]
        exact hHs _ _ htb.le hb
      have hhon : Restated.HonestThrough M Sched x (k + 1) b.val_index :=
        Restated.honestThrough_of_mem_notHeld facts S Sched x (k + 1) hmono _ hbk
      obtain ⟨entry, tmo, hpair⟩ := heightPair_vote_of_height_l72 hrow
      have hle := Restated.honestRow_le_topHonestRow facts S Sched x hvalid.toUnforgeability
        ⟨b.val_index, k + 1, b, entry, tmo, hkn, hhon, rfl, hsent, hpair⟩
      exact Nat.sub_le_iff_le_add.mp hle
    · exact (Nat.le_of_not_lt hlarge).trans (Nat.le_add_left 1 _)
  exact Nat.sub_le_iff_le_add.mpr hsup

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
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- With synchrony only up to `x[N].time`: under the theorem's hypotheses, for a round `r` at or
    after the deadline round, with `n₀` the tick step at `S.a r` and `N` a step whose time lies
    between `S.a r` and `tAwakeEnd`, there is a run-scoped regime on `runAll M S Sched x v N`, read
    along `Restated.runAllPath M S Sched x v N` over the validators not held, from base round
    `roundAt S tGAT + η_SG + 2`, whose source round is at or before `r`, whose checkpoint's
    chain-state height is the larger of `topHonestRow S Sched x n₀` and the regime's height plus
    one, and that height is at least `topHonestRow S Sched x n₀` and at least the largest `Σ.h_max`
    of an honest active attester of round `r` after `n₀` steps minus one. -/
theorem switchRoundRegime_runAll_notHeld_atRound_upTo (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v : V)
    {tGAT tAwakeEnd : Int} {gap : Nat} {N : Nat}
    (hsync : Restated.SynchronyFromWakeBefore M S x (x[N].time : Int)) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tAwakeEnd → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tAwakeEnd →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tAwakeEnd gap)
    {r : Round} (hrD : Restated.deadlineRoundW M S tGAT gap ≤ r)
    {n₀ : Nat} (hn₀ : Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S r)))
    (hNlo : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int)) (hNhi : (x[N].time : Int) ≤ tAwakeEnd) :
    ∃ (blocked : Height) (first i : Nat) (a : NamedAttestation V) (ta : Int)
      (Cfg T Tprev : NamedBlock V) (c0 : Round),
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 ∧
      a.round ≤ r ∧
      (M.derive_named S.E S.cfg T).h = max (Restated.topHonestRow M S Sched x n₀) (blocked + 1) ∧
      Restated.topHonestRow M S Sched x n₀ ≤ (M.derive_named S.E S.cfg T).h ∧
      Restated.hmaxRoundAt M S Sched x (r) n₀ - 1
        ≤ (M.derive_named S.E S.cfg T).h := by
  classical
  have hdlrW : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S))
      (Restated.fgSafetyProgressDeadline (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.roundAt M S tGAT + S.hc.η_SG) gap (Setup.alwaysAwake S).extraRounds)
      ≤ (Restated.Vocabulary.Execution.Setup.a M S r) := by
    apply (Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone
    rw [Restated.fgSafetyProgressDeadline_eq_deadlineRoundW facts]
    exact hrD
  have hn : (x[N].time : Int) ≤ tAwakeEnd := hNhi
  have hrWN : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) := hNlo
  obtain ⟨hn₀1, hn₀0⟩ := Restated.tickStepAt_time facts x hn₀
  have hn₀N : n₀ + 1 ≤ N := by
    by_contra hcon
    have hle : ((x[N].time : Nat) : Int) ≤ ((x[n₀].time : Nat) : Int) := by
      exact_mod_cast Restated.time_mono facts S Sched x (by omega)
    linarith
  have hf := Restated.admissibleFieldsOn_runAll_notHeld_upTo facts S Sched x v N hsync hmono hawake hgst hcv hvalid
    hawm hthird hn
  have hHs : ∀ t t' : Int, t ≤ t' → notHeldAt Sched t' ⊆ notHeldAt Sched t :=
    fun _ _ h => notHeldAt_anti hmono h
  have hHsXb : ∀ t : Int, notHeldAt Sched t ⊆ (Finset.univ : Finset V) :=
    fun _ => Finset.subset_univ _
  have hX : ∀ t : Int, 0 ≤ t → notHeldAt Sched t ⊆ (Finset.univ : Finset V) :=
    fun _ _ => Finset.subset_univ _
  have hXXb : (Finset.univ : Finset V) ⊆ Finset.univ := Finset.Subset.refl _
  have hcomOn := Restated.honestCommitteesOn_notHeld facts S Sched hcom
  have hbelow := Restated.belowOneThirdOn_runAll_notHeld facts S Sched x v N hthird hn
  obtain ⟨hpost, -, hloOpen, -⟩ := Restated.roundAt_bounds_l71 facts S hgst
  have hgstR0 := Restated.Vocabulary.Proofs.HealingSurface.gstLagged_le_Γ_neg1_of_gst_le_a facts S (Restated.roundAt M S tGAT + S.hc.η_SG) hpost
  have hgstLo := Restated.lo_add_lag_le_Γ_neg1_l71 facts S (Restated.roundAt M S tGAT + S.hc.η_SG)
    (Restated.roundAt_lo_le_rGST_l71 facts S tGAT)
  obtain ⟨blocked, first, Tprev, hfirst, hbase⟩ :=
    Restated.exists_namedHeightRegimeBaseRun_before_fgSafetyProgressDeadline_runAll_notHeld_upTo facts S Sched x v N
      hsync hmono hawake hgst hcv hvalid hawm hthird hn hcom hrec (hdlrW.trans hrWN)
  have hband := Restated.hmaxRoundAt_sub_one_le_topHonestRow_atRound_upTo facts S Sched x v hsync hmono hawake hgst hcv
    hvalid hawm hthird hn₀ hn₀N hn hrWN
  by_cases hcase : blocked + 1 ≤ Restated.topHonestRow M S Sched x n₀
  · -- the row case
    obtain ⟨v', n', b, entry, tmo, hn', hv', hidx, hsent, hpair⟩ :=
      Restated.topHonestRow_spec_of_pos facts S Sched x (n₀ := n₀) (Nat.lt_of_lt_of_le (Nat.succ_pos _) hcase)
    obtain ⟨k, hkn', τ, hlbl, haw, hdvd, out, hout, hst, ho⟩ :=
      Restated.tick_of_honest_signed_upTo_taken facts S Sched x v' (NamedObject.attest b) (x[n'].time : Int) hv'
        hvalid.toUnforgeability (by rw [author_attest, hidx]) n' le_rfl hsent
    have hkN : k < N := by omega
    have hemit' := Restated.emits_runAllPath_of_tick facts S Sched x v hkN hlbl haw hdvd hout hst ho
    have hemit : Restated.Vocabulary.Execution.NamedRun.emits M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        b.val_index (Object.attest b) (τ : Int) := by
      rw [hidx]; exact hemit'
    have hτ : (τ : Int) = (Restated.Vocabulary.Execution.Setup.a M S b.round) := (Restated.Vocabulary.Proofs.Optimistic.emits_attest_shape facts _ _ hf.onePath hemit).2
    have hb : b.val_index ∈ notHeldAt Sched (τ : Int) := by
      rw [mem_notHeldAt, hidx]; exact (Finset.mem_sdiff.mp haw).2
    obtain ⟨n, hnEq⟩ : ∃ n : Nat, blocked + n + 1 = Restated.topHonestRow M S Sched x n₀ :=
      ⟨_, add_sub_succ_l72 _ _ hcase⟩
    have hrow : b.height_pair.erase.height? = some (blocked + n + 1) := by
      rw [hpair, hnEq]; exact height?_erase_vote_l72 _ _ _
    obtain ⟨first_n, i, a, ta, Cfg, T, Tprev', c0, hreg⟩ :=
      hbase.exists_regime_of_row_named facts hf hHs hHsXb hX hXXb hcomOn hbelow hgstR0 n hb
        hemit hrow hgstLo hloOpen
        (fun k hk u _ j hj => Restated.awake_g2_action_runAllPath facts S Sched x v N hmono hawake hn
          k hk u j hj)
    obtain ⟨-, hTheight'⟩ := hreg.checkpoint_runBlock facts hf hHsXb
    have hTheight : (M.derive_named S.E S.cfg T).h = blocked + n + 1 := hTheight'
    have hab : a.round ≤ b.round := hreg.minimal b (τ : Int) hb hemit hrow
    have hbrW : b.round ≤ r := by
      have hk1 : ((x[k + 1].time : Nat) : Int) = (τ : Int) := by
        exact_mod_cast (Restated.tickAllAwake_time facts S Sched x hlbl).2
      have hle : ((x[k + 1].time : Nat) : Int) ≤ ((x[n₀ + 1].time : Nat) : Int) := by
        exact_mod_cast Restated.time_mono facts S Sched x (by omega)
      apply (Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).le_iff_le.mp
      rw [← hτ, ← hn₀1, ← hk1]
      exact hle
    refine ⟨blocked + n, first_n, i, a, ta, Cfg, T, Tprev', c0, hreg, hab.trans hbrW, ?_, ?_, ?_⟩
    · rw [hTheight, hnEq, max_self]
    · rw [hTheight, hnEq]
    · rw [hTheight, hnEq]; exact hband
  · -- the closed case
    have htop : Restated.topHonestRow M S Sched x n₀ < blocked + 1 := Nat.lt_of_not_le hcase
    obtain ⟨i, a, ta, Cfg, T, hreg⟩ :=
      hbase.exists_regime_closed facts hf hHs hHsXb hX hXXb hbelow hgstR0 hgstLo hloOpen
    have hi := hreg.seed.indexLtStop.trans_le hfirst
    have hfilter := Restated.filter_eq_takeOn facts _ (notHeldAt Sched) Finset.univ hf
      (fun e => decide (e.time ≤ (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S))
        (fgSafetyProgressDeadline (Setup.alwaysAwake S)
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
          (Restated.roundAt M S tGAT + S.hc.η_SG) gap (Setup.alwaysAwake S).extraRounds)))
      (Restated.downward_le _)
    have hmem : Record.Event.tick a.val_index ta ∈
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } :
          Record.Run V).events.take (inclusiveEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
          ((Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S)) (fgSafetyProgressDeadline (Setup.alwaysAwake S)
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } :
              Record.Run V)
            (Restated.roundAt M S tGAT + S.hc.η_SG) gap (Setup.alwaysAwake S).extraRounds))) := by
      apply List.mem_of_getElem? (i := i)
      rw [List.getElem?_take_of_lt hi]
      exact hreg.seed.exactTick
    simp only [inclusiveEventIndex] at hmem
    rw [← hfilter] at hmem
    have hadl : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) a.round) ≤ (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S))
        (fgSafetyProgressDeadline (Setup.alwaysAwake S)
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
          (Restated.roundAt M S tGAT + S.hc.η_SG) gap (Setup.alwaysAwake S).extraRounds) := by
      simpa only [Record.Event.time, hreg.seed.actionTime_eq, decide_eq_true_eq, Record.Event.time] using
        (List.mem_filter.mp hmem).2
    have harW : a.round ≤ r :=
      (Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).le_iff_le.mp (hadl.trans hdlrW)
    obtain ⟨-, hTheight'⟩ := hreg.checkpoint_runBlock facts hf hHsXb
    have hTheight : (M.derive_named S.E S.cfg T).h = blocked + 1 := hTheight'
    refine ⟨blocked, first, i, a, ta, Cfg, T, Tprev, a.round, hreg, harW, ?_, ?_, ?_⟩
    · rw [hTheight, max_eq_right htop.le]
    · rw [hTheight]; exact htop.le
    · rw [hTheight]; exact hband.trans htop.le

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
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- With synchrony only up to the confirmation instant of the switch round's third slot: under the
    theorem's hypotheses, with `n₀` the tick step at the switch round's action instant and `N` a
    step whose time is that confirmation instant, there is a run-scoped regime on
    `runAll M S Sched x v N`, read along `Restated.runAllPath M S Sched x v N` over the validators
    not held, from base round `roundAt S tGAT + η_SG + 2`, whose source round is at or before the
    switch round, whose checkpoint's chain-state height is the larger of `topHonestRow S Sched x n₀`
    and the regime's height plus one, and that height is at least `topHonestRow S Sched x n₀` and at
    least the largest `Σ.h_max` of an honest active attester of the switch round after `n₀` steps
    minus one. -/
theorem switchRoundRegime_runAll_notHeld_upTo (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v : V)
    {tGAT tAwakeEnd : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWakeBefore M S x
      (M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tAwakeEnd)) + 2))) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tAwakeEnd → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tAwakeEnd →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tAwakeEnd gap)
    (hlen : tGAT + Restated.healingLengthη M S gap ≤ tAwakeEnd) (htd : Restated.TimeDiverges M x)
    {n₀ N : Nat} (hn₀ : Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tAwakeEnd))))
    (hN : (x[N].time : Int)
      = M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tAwakeEnd)) + 2)) :
    ∃ (blocked : Height) (first i : Nat) (a : NamedAttestation V) (ta : Int)
      (Cfg T Tprev : NamedBlock V) (c0 : Round),
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 ∧
      a.round ≤ Restated.switchRound M S tAwakeEnd ∧
      (M.derive_named S.E S.cfg T).h = max (Restated.topHonestRow M S Sched x n₀) (blocked + 1) ∧
      Restated.topHonestRow M S Sched x n₀ ≤ (M.derive_named S.E S.cfg T).h ∧
      Restated.hmaxRoundAt M S Sched x (Restated.switchRound M S tAwakeEnd) n₀ - 1
        ≤ (M.derive_named S.E S.cfg T).h := by
  obtain ⟨N', hN', hN'E, -, hrWN', -, -, -⟩ := Restated.switchRound_instants facts S Sched x tGAT tAwakeEnd
    gap ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
    hgst hlen htd
  have hNN' : (x[N].time : Int) = (x[N'].time : Int) := hN.trans hN'.symm
  have hsyncN : Restated.SynchronyFromWakeBefore M S x (x[N].time : Int) :=
    fun k w sm hsend hle haw => hsync k w sm hsend (le_trans hle (le_of_eq hN)) haw
  exact Restated.switchRoundRegime_runAll_notHeld_atRound_upTo facts S Sched x v hsyncN
    hmono hawake hgst hcv hvalid
    hawm hthird hcom hrec
    (Restated.deadlineRoundW_le_switchRound facts S tGAT tAwakeEnd gap
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      hgst hlen)
    hn₀ (by rw [hNN']; exact hrWN') (by rw [hNN']; exact hN'E)

end

end DecoupledConsensusModel.Sts.Restated
