import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13beRoute3_44
import Proofs.Claims.Restated.Claim13beRoute3_45
import Proofs.Claims.Restated.Claim13beRoute3_46
import Proofs.Claims.Restated.Claim13beRoute3_47b
import Proofs.Claims.Restated.Claim13beRoute3_48
import Proofs.Claims.Restated.Claim13beRoute3_49
import Proofs.Claims.Restated.Claim13beRoute3_49b
import Proofs.Claims.Restated.Claim13beRoute3_50
import Proofs.Claims.Restated.Claim13beRoute3_57b
import Proofs.Claims.Restated.Claim13beRoute3_63
import Proofs.Claims.Restated.Claim13beRoute3_68b
import Proofs.Claims.Restated.Claim13beRoute3_69
import Proofs.Claims.Restated.Claim13beRoute3_69b
import Proofs.Claims.Restated.Claim13beRoute3_70
import Proofs.Claims.Restated.Claim13beRoute3_70b
import Proofs.Claims.Restated.Vocabulary_Execution_EmissionShape
import Proofs.Claims.Restated.Vocabulary_Execution_HealthyLocalFacts
import Proofs.Claims.Restated.Vocabulary_Internal_Legacy_Instance
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_Ladder
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.RunAll
import Model.Conditions.RunVocabulary
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13bd
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedHeadReads
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_ModelVocabulary_Healing_Schedule
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_71

/-!
# Bounds on rounds after a time, and the progress deadline on the full run

Round and cutoff bounds from a time `tGAT` at or after `t_GST`, the grade-2 awake test along
`runAllPath`, the progress deadline for a run-scoped named base on the run `runAll`, and theorems
named under the run-scoped height regimes, stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

/-! ## Helpers -/

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

/-- The action instant of round `r` is at or before the earliest grade cutoff of round `r + 1`. -/
private theorem a_le_Γ_neg1_succ₇₁ (facts : Record.Facts M) (S : Setup V) (r : Round) :
    Restated.Vocabulary.Execution.Setup.a M S r ≤
      Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (r + 1) := by
  have h := facts.gr.action_add_delta_le_next_Γ_neg1 S r
  have hΔ := S.E.Δ_pos
  unfold Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 Restated.Vocabulary.Execution.Setup.a
  linarith

/-- Advancing by `k` rounds advances the earliest grade cutoff by `4ΔRk`. -/
private theorem Γ_neg1_add_rounds₇₁ (facts : Record.Facts M) (hc : HealConfig) (Δ : Time)
    (r k : Round) :
    Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M hc Δ (r + k) =
      Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M hc Δ r + 4 * Δ * ((hc.R * k : Nat) : Time) := by
  unfold Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 slotStart
  rw [facts.gr.opening_slot_add_mk]
  push_cast
  ring

/-- The action instant of round `ρ` is strictly before the opening of round `ρ + 1`. -/
private theorem a_lt_opening_succ₇₁ (facts : Record.Facts M) (S : Setup V) (ρ : Round) :
    (Restated.Vocabulary.Execution.Setup.a M S ρ) < M.opening S.E S.hc (ρ + 1) := by
  have h1 := facts.gr.action_delta_le_early S S.hc.R_ge_three (Nat.lt_succ_self ρ)
  have h2 := facts.gr.early_g2_le_opening S (ρ + 1)
  have hd := S.E.Δ_pos
  show M.a S.hc S.E.Δ _ < _
  linarith

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
local macro "fbn% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `DecoupledConsensusProofs.Generic.FGSafetyFrontierBandNamed)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- If `lo` is at or before round `r`'s action instant, then `lo + 4Δ·(R·readyLag)` is at or before
    round `r + 2`'s earliest grade cutoff `Γ_neg1 (r + 2)`. -/
theorem lo_add_lag_le_Γ_neg1_l71 (facts : Record.Facts M) (S : Setup V) (r : Round) {lo : Int}
    (hlo : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S r)) :
    lo + 4 * S.E.Δ * (S.hc.R * readyLag : Nat) ≤
      Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (r + 2) := by
  have hstep : (Restated.Vocabulary.Execution.Setup.a M S r) ≤
      Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (r + 1) :=
    a_le_Γ_neg1_succ₇₁ facts S r
  have hsplit : Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (r + 2)
      = Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (r + 1) +
        4 * S.E.Δ * ((S.hc.R * 1 : Nat) : Time) :=
    Γ_neg1_add_rounds₇₁ facts S.hc S.E.Δ (r + 1) 1
  have hlag : ((S.hc.R * readyLag : Nat) : Time) = ((S.hc.R * 1 : Nat) : Time) := by
    simp only [readyLag]
  rw [hsplit, hlag]
  linarith

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
local macro "fbn% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `DecoupledConsensusProofs.Generic.FGSafetyFrontierBandNamed)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- If `t_GST ≤ tGAT`, then with `ρ` the first round acting at or after `tGAT`,
    `t_GST ≤ S.a (ρ + η_SG)`, `tGAT + 1 ≤ S.a (ρ + η_SG + 2)`,
    `tGAT + 1 ≤ opening (ρ + η_SG + 2 − η_SG)` and `tGAT ≤ S.a (ρ + η_SG + 2)`. -/
theorem roundAt_bounds_l71 (facts : Record.Facts M) (S : Setup V) {tGAT : Int} (hgst : S.E.t_GST ≤ tGAT) :
    S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S (Restated.roundAt M S tGAT + S.hc.η_SG)) ∧
      tGAT + 1 ≤ (Restated.Vocabulary.Execution.Setup.a M S (Restated.roundAt M S tGAT + S.hc.η_SG + 2)) ∧
      tGAT + 1 ≤ M.opening S.E S.hc (Restated.roundAt M S tGAT + S.hc.η_SG + 2 - S.hc.η_SG) ∧
      tGAT ≤ (Restated.Vocabulary.Execution.Setup.a M S (Restated.roundAt M S tGAT + S.hc.η_SG + 2)) := by
  obtain ⟨hlt, hle, hopen⟩ := roundAt_bounds_nat_l71 (Restated.roundAt M S tGAT) S.hc.η_SG
  have hspec : tGAT ≤ (Restated.Vocabulary.Execution.Setup.a M S (Restated.roundAt M S tGAT)) :=
    Restated.Vocabulary.Statements.roundAt_spec facts S tGAT
  have hstrict : (Restated.Vocabulary.Execution.Setup.a M S (Restated.roundAt M S tGAT)) < (Restated.Vocabulary.Execution.Setup.a M S (Restated.roundAt M S tGAT + S.hc.η_SG + 2)) :=
    Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S hlt
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hgst.trans (hspec.trans ((Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone hle))
  · exact Int.add_one_le_iff.mpr (lt_of_le_of_lt hspec hstrict)
  · exact (Int.add_one_le_iff.mpr (lt_of_le_of_lt hspec
      (a_lt_opening_succ₇₁ facts S (Restated.roundAt M S tGAT)))).trans
        (facts.gr.NamedOutageClosure_opening_mono S hopen)
  · exact hspec.trans hstrict.le

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- If every validator not held by the adversary is awake throughout `[tGAT, tAwakeEnd]` and the
    time of step `n` is at or before `tAwakeEnd`, then along the run `runAll M S Sched x v n` every
    tick at round `k`'s action instant, for a round `k` whose grade-2 window starts at or after
    `tGAT + 1`, reads a node state passing the grade-2 test of round `k` under
    `Setup.alwaysAwake S`. -/
theorem awake_g2_action_runAllPath (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V) (n : Nat) {tGAT tAwakeEnd : Int}
    (hmono : Sched.MonotoneCorruption)
    -- Every validator not held by the adversary is awake at every instant of `[tGAT, tAwakeEnd]`.
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tAwakeEnd → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    -- The time of step `n` is at or before `tAwakeEnd`.
    (hn : (x[n].time : Int) ≤ tAwakeEnd) :
    ∀ (k : Round), tGAT + 1 ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ (u : V) (j : Nat),
      (Restated.runAll M S Sched x v n).events[j]? =
        some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) →
      M.awake_for_grade2 (Setup.alwaysAwake S) u (Restated.runAllPath M S Sched x v n j u) k := by
  intro k hlo u j he
  have hΔ : 0 < S.E.Δ := S.E.Δ_pos
  have hhor := (Restated.in_horizon_runAll_withHonest facts S Sched x v
    (Restated.runAll M S Sched x v n).honest n _ (List.mem_of_getElem? he)).2
  obtain ⟨k', -, hmem, hcases⟩ := Restated.runAllPath_at_event facts S Sched x v n j he
  have hnode : Record.Event.node
      (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k) : Record.Event V) = u := rfl
  simp only [hnode] at hmem hcases
  obtain ⟨τ', hl, hτ', hv, -⟩ := tick_mem_actionEventsOf hmem
  rcases hcases with ⟨t', he', -, -⟩ | ⟨t', he', hb, -⟩ | ⟨o, t', he', -, -⟩
  · cases he'
  · have htt : Restated.Vocabulary.Execution.Setup.a M S k = t' := (Record.Event.tick.inj he').2
    rw [hb, ← htt, hτ']
    have hhor' : (τ' : Int) ≤ tAwakeEnd := by rw [← hτ']; exact le_trans hhor hn
    have hearly : M.early S.E S.hc k .g2 = Restated.Vocabulary.Execution.Setup.a M S k - 11 * S.E.Δ :=
      facts.gr.early_g2_eq S k
    refine facts.ndRun.run_fact_g2_at S Sched x k' τ' k u hl ?_ ?_
      (honest_upTo_of_mono hmono hv)
    · rw [← hτ', hearly]
      linarith
    · refine Finset.singleton_subset_iff.1 (Finset.le_inf ?_)
      intro t ht
      obtain ⟨h0, h1⟩ := Finset.mem_Icc.1 ht
      exact Finset.singleton_subset_iff.2 (hawake t (by linarith) (by linarith) u
        (honest_upTo_of_mono hmono hv t h1))
  · cases he'

/-- Under the synchrony, corruption, awake, weight, committee and recurrence hypotheses of the
    signature, if the action instant of the progress deadline from `roundAt S tGAT + η_SG` is in the
    horizon of `runAll M S Sched x v n` with the validators not held as its honest set, then some
    run-scoped named base at round `roundAt S tGAT + η_SG + 2`, read along
    `Restated.runAllPath M S Sched x v n` over the validators not held, has its first crossing no
    later than the deadline's inclusive index. -/
theorem exists_namedHeightRegimeBaseRun_before_fgSafetyProgressDeadline_runAll_notHeld (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v : V) (n : Nat)
    {tGAT tAwakeEnd : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWake M S x) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tAwakeEnd → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tAwakeEnd →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hn : (x[n].time : Int) ≤ tAwakeEnd)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tAwakeEnd gap)
    (hhor : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S))
        (fgSafetyProgressDeadline (Setup.alwaysAwake S)
          ({ Restated.runAll M S Sched x v n with honest := notHeldAt Sched (x[n].time : Int) } : Record.Run V)
          (Restated.roundAt M S tGAT + S.hc.η_SG) gap (Setup.alwaysAwake S).extraRounds) ≤
      ({ Restated.runAll M S Sched x v n with honest := notHeldAt Sched (x[n].time : Int) } :
        Record.Run V).horizon) :
    ∃ (blocked : Height) (first : Nat) (Tprev : NamedBlock V),
      first ≤ inclusiveEventIndex
        ({ Restated.runAll M S Sched x v n with honest := notHeldAt Sched (x[n].time : Int) } : Record.Run V)
        ((Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S))
          (fgSafetyProgressDeadline (Setup.alwaysAwake S)
            ({ Restated.runAll M S Sched x v n with honest := notHeldAt Sched (x[n].time : Int) } : Record.Run V)
            (Restated.roundAt M S tGAT + S.hc.η_SG) gap (Setup.alwaysAwake S).extraRounds)) ∧
      Restated.NamedHeightRegimeBaseRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v n with honest := notHeldAt Sched (x[n].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v n)
        (fun t => Restated.runAllPath M S Sched x v n
          (strictEventIndex
            ({ Restated.runAll M S Sched x v n with honest := notHeldAt Sched (x[n].time : Int) } :
              Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ (Restated.roundAt M S tGAT + S.hc.η_SG + 2)
        blocked first Tprev := by
  obtain ⟨hpost, hlo, hloOpen, ht₀⟩ := Restated.roundAt_bounds_l71 facts S hgst
  exact Restated.exists_namedHeightRegimeBaseRun_before_fgSafetyProgressDeadlineOn facts
    (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ Finset.univ
    (Restated.admissibleFieldsOn_runAll_notHeld facts S Sched x v n hsync hmono hawake hgst hcv hvalid
      hawm hthird hn)
    (fun _ _ h => notHeldAt_anti hmono h) (fun _ => Finset.subset_univ _)
    (fun _ _ => Finset.subset_univ _) (Finset.subset_univ _)
    (Restated.honestCommitteesOn_notHeld facts S Sched hcom)
    (Restated.belowOneThirdOn_runAll_notHeld facts S Sched x v n hthird hn)
    (Restated.multiProposerRecurrenceOn_runAll_notHeld facts S Sched x v n hrec hn)
    (Setup.timeoutDelayBound _) hpost hhor hlo hloOpen ht₀
    (fun k hk u _ j hj => Restated.awake_g2_action_runAllPath facts S Sched x v n hmono hawake hn
      k hk u j hj)

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- With `ρ` the first round acting at or after `tGAT`, `tGAT + 1 ≤ S.a (ρ + η_SG)`. -/
theorem roundAt_lo_le_rGST_l71 (facts : Record.Facts M) (S : Setup V) (tGAT : Int) :
    tGAT + 1 ≤ (Restated.Vocabulary.Execution.Setup.a M S (Restated.roundAt M S tGAT + S.hc.η_SG)) := by
  have hspec : tGAT ≤ (Restated.Vocabulary.Execution.Setup.a M S (Restated.roundAt M S tGAT)) :=
    Restated.Vocabulary.Statements.roundAt_spec facts S tGAT
  have hlt : Restated.roundAt M S tGAT < Restated.roundAt M S tGAT + S.hc.η_SG :=
    Nat.lt_add_of_pos_right S.hc.η_SG_ge_one
  exact Int.add_one_le_iff.mpr (lt_of_le_of_lt hspec (Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S hlt))

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

local macro "p68% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Claims.Restated.Claim13beRoute3_68)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

end

/-! ## Theorems named under the run-scoped height regimes -/

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas

/-- Under the bundle with path `W`, a run-scoped named regime along `W` from base round `r0` has its
    source round `a.round` at or after `r0`. -/
theorem NamedHeightRegimeRunOn.r0_le_round_l71 (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} {Hs : Int → Finset V} {X Xb : Finset V} {lo : Int}
    {W : Nat → V → M.N} {Wt : Time → V → M.N}
    {r0 : Round} {blocked : Height} {first i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (h : Restated.NamedHeightRegimeRunOn M S rho W Wt Hs X Xb r0 blocked first i a ta Cfg T Tprev
      c0) :
    r0 ≤ a.round := by
  by_contra hnot
  have htimeLt : ta < (Restated.Vocabulary.Execution.Setup.a M S r0) := by
    rw [h.seed.actionTime_eq]
    exact Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S (Nat.lt_of_not_ge hnot)
  have htimeLe : (Restated.Vocabulary.Execution.Setup.a M S r0) ≤ ta :=
    Restated.le_time_of_index_geOn facts S Hs Xb hf
      ((strictEventIndex_le_inclusiveEventIndex rho
        ((Restated.Vocabulary.Execution.Setup.a M S r0))).trans h.seed.startLeIndex)
      h.seed.exactTick
  exact (not_le_of_gt htimeLt) htimeLe

/-- Under the bundle with path `W`, if `lo ≤ opening (r0 − η_SG)`, then
    `lo ≤ opening (a.round − η_SG)` for the source round `a.round` of a run-scoped named regime
    along `W`. -/
theorem NamedHeightRegimeRunOn.lo_le_opening_l71 (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} {Hs : Int → Finset V} {X Xb : Finset V} {lo : Int}
    {W : Nat → V → M.N} {Wt : Time → V → M.N}
    {r0 : Round} {blocked : Height} {first i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (h : Restated.NamedHeightRegimeRunOn M S rho W Wt Hs X Xb r0 blocked first i a ta Cfg T Tprev
      c0)
    (hloOpen : lo ≤ M.opening S.E S.hc (r0 - S.hc.η_SG)) :
    lo ≤ M.opening S.E S.hc (a.round - S.hc.η_SG) :=
  hloOpen.trans (facts.gr.NamedOutageClosure_opening_mono S
    (Nat.sub_le_sub_right (Restated.NamedHeightRegimeRunOn.r0_le_round_l71 facts hf h) _))

/-- Under the bundle with path `W`, if, over `X` along `W`, the height `blocked + 1` is first
    crossed at `first` and the height `blocked + n + 1` at `f`, then every height `blocked + m + 1`
    with `1 ≤ m ≤ n` is first crossed along `W` at some index. -/
theorem exists_crossings_below_top_namedOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb X : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {first : Nat} {blocked : Height}
    (hfirst : Restated.FirstHeightProgressAtOn M S rho W X (blocked + 1) first)
    {n f : Nat} (hfn : Restated.FirstHeightProgressAtOn M S rho W X (blocked + n + 1) f) :
    ∀ m : Nat, 1 ≤ m → m ≤ n →
      ∃ f' : Nat, Restated.FirstHeightProgressAtOn M S rho W X (blocked + m + 1) f' := by
  intro m hm1 hmn
  have hfirstLe : first ≤ f := by
    by_contra hn
    have hlt : f < first := Nat.lt_of_not_le hn
    have h1 := hfirst.before f hlt
    rw [hfn.frontier] at h1
    exact absurd h1 (Nat.not_le.mpr
      (Nat.succ_lt_succ
        (Nat.lt_succ_of_le (Nat.le_add_right blocked n))))
  rcases eq_or_lt_of_le hmn with heq | hlt
  · exact ⟨f, heq ▸ hfn⟩
  · obtain ⟨f', hff', -, hbefore', hfront⟩ :=
      Restated.exists_least_honestHMaxBeforeIndex_crossingOn facts S Hs Xb X hf hfirstLe
        (H := blocked + m + 1)
        (by rw [hfirst.frontier]
            exact Nat.succ_le_succ (Nat.add_le_add_left hm1 blocked))
        (by rw [hfn.frontier]
            exact Nat.succ_lt_succ
              (Nat.lt_succ_of_lt (Nat.add_lt_add_left hlt blocked)))
    refine ⟨f', ⟨hfirst.positive.trans hff', hfront, ?_⟩⟩
    intro i hi
    by_cases hif : i < first
    · exact (hfirst.before i hif).trans
        (Nat.succ_le_succ (Nat.le_add_right blocked m))
    · exact hbefore' i (Nat.le_of_not_lt hif) hi

end

/-! ## Successor regimes and the head ancestor after the deadline -/

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas

local macro "p49% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Claims.Restated.Claim13beRoute3_49)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

/-- The round-`r` action read computed from `before` has some node state. -/
private theorem actionReadFrom_nonempty₇₁w (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∃ n, n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r := by
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc before.st.core.toHealing
    (Restated.Vocabulary.Execution.Setup.a M S r) before.cache
  obtain ⟨st, hst⟩ := facts.dt.duties_update_confirmation_with_nonempty (M.gradeContract c) S.E S.hc
    (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r))
    (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1)
  exact ⟨_, c, hc, st, hst, rfl⟩

/-- An action instant is not negative. -/
private theorem a_nonneg₇₁w (facts : Record.Facts M) (S : Setup V) (r : Round) :
    0 ≤ Restated.Vocabulary.Execution.Setup.a M S r := by
  show 0 ≤ M.a S.hc S.E.Δ r
  rw [facts.sch.a_eq_confirmation_time]
  exact le_trans (facts.sch.Optimistic_proposal_time_nonneg S.E _)
    (facts.sch.proposal_time_le_confirmation_time S.E _)

/-- If round `r`'s action instant is strictly before slot `s`'s confirmation instant, then `s` is
    after round `r`'s opening slot. -/
private theorem firstInterior_le_of_action_lt_confirmation₇₁w (facts : Record.Facts M)
    (S : Setup V) {r : Round} {s : Slot}
    (h : Restated.Vocabulary.Execution.Setup.a M S r < M.confirmation_time S.E s) :
    M.opening_slot S.hc r + 1 ≤ s := by
  by_contra hnot
  have hle : s ≤ M.opening_slot S.hc r := Nat.le_of_lt_succ (Nat.lt_of_not_le hnot)
  have hmono := facts.sch.confirmation_time_mono S hle
  have ha : Restated.Vocabulary.Execution.Setup.a M S r =
      M.confirmation_time S.E (M.opening_slot S.hc r) :=
    facts.sch.a_eq_confirmation_time S.hc S.E r
  rw [ha] at h
  exact (not_le_of_gt h) hmono

/-- Under the bundle with path `W`, the committee majority and the weight bound, for a run-scoped
    named regime along `W` at `blocked` with source round `a.round`, if `1 ≤ blocked`, `first'`
    bounds the window at `blocked + 2` along `W`, `lo ≤ opening (a.round − η_SG)` and the grade-2
    awake hypothesis `hA` holds, then the named frame holds along `W` at `blocked + 1` up to
    `first' − 1`, with the regime's checkpoint `T` as previous checkpoint and `a.round + 1` as round
    bound. -/
theorem NamedHeightRegimeRunOn.frame_succ_main (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} {Hs : Int → Finset V} {X Xb : Finset V} {lo : Int}
    {W : Nat → V → M.N}
    {r0 : Round} {blocked : Height}
    {first i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hX : ∀ t : Int, 0 ≤ t → Hs t ⊆ X) (hXXb : X ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hbelow : BelowOneThirdOn S rho Hs)
    (h : Restated.NamedHeightRegimeRunOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs X Xb r0 blocked first i a ta Cfg T Tprev c0)
    (hblocked : 1 ≤ blocked)
    {first' : Nat}
    (hfirst' : Restated.HeightWindowAtOn M S rho W X (blocked + 1 + 1) first')
    (hlo : lo ≤ M.opening S.E S.hc (a.round - S.hc.η_SG))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S k + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    Restated.NamedHeightRegimeFrameOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs X Xb (blocked + 1) (first' - 1) T (a.round + 1) := by
  obtain ⟨hTrun, hTheight⟩ :=
    Restated.NamedHeightRegimeRunOn.checkpoint_runBlock facts hf hHsXb h
  obtain ⟨-, -, hpostPrev, -⟩ := Restated.loBounds_l70 facts S
    (Restated.PrefixFGSelectorConeAtOn.round_pos_l70 facts hf h.seed) hlo
  refine Restated.PrefixFGSelectorConeAtOn.heightRegimeFrame_succ_of_frameN facts Hs Xb X hf hHs
    hHsXb hX hXXb hcom hbelow h.seed h.crossing h.frame h.c0le h.ready hpostPrev h.minimal hblocked
    hfirst' h.checkpointPreceq hTrun h.checkpointErase hTheight ?_ ?_
  · intro b tb hb hemit hrow hround
    have htbHor : tb ≤ rho.horizon := by
      obtain ⟨k, hk, _⟩ := hemit
      have hin := (hf.in_horizon
        (Record.Event.tick b.val_index tb) (List.mem_of_getElem? hk)).2
      simpa only [Record.Event.time, Record.Event.time] using hin
    have htime : tb = Restated.Vocabulary.Execution.Setup.a M S b.round :=
      (Restated.Vocabulary.Proofs.Optimistic.emits_attest_shape facts S W hf.onePath hemit).2
    have hbA : b.val_index ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S b.round) := by
      rw [← htime]
      exact hHs _ _ htbHor hb
    exact
      Restated.PrefixFGSelectorConeAtOn.confirmationWitness_of_sameRound_honestHeightRow_of_frame_named
        facts hf hHs hHsXb hX hXXb h.seed h.crossing h.frame h.ready hbA hemit hrow hround hlo
  · intro r hr hhor w hw n hn B hB
    exact ((Restated.NamedHeightRegimeRunOn.laterHistory_main facts hf hHs hHsXb hX hXXb hcom
      hbelow h hr hlo hA).2 hhor).2 w hw n hn B hB

/-- Under the bundle with path `W`, the committee majority and the weight bound, for a run-scoped
    named regime along `W` at `blocked` with source round `a.round`, if `gstLagged ≤ Γ_neg1 r0`, the
    largest `h_max` over `X` in the world of `W` at `S.a r0` is less than `blocked`, `1 ≤ blocked`,
    `first'` bounds the window at `blocked + 2`, some member of the set for its emission instant
    emits along `W`, before `first'`, a row at height `blocked + 2`,
    `lo + 4Δ·(R·readyLag) ≤ Γ_neg1 r0`, `lo ≤ opening (a.round − η_SG)` and the grade-2 awake
    hypothesis `hA` holds, then some run-scoped named regime along `W` at `blocked + 1` with first
    crossing `first'` has previous checkpoint `T`, a later source round, and a checkpoint that is a
    descendant of `T`. -/
theorem NamedHeightRegimeRunOn.succ_of_row_named (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} {Hs : Int → Finset V} {X Xb : Finset V} {lo : Int}
    {W : Nat → V → M.N}
    {r0 : Round} {blocked : Height}
    {first i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hX : ∀ t : Int, 0 ≤ t → Hs t ⊆ X) (hXXb : X ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hbelow : BelowOneThirdOn S rho Hs)
    (h : Restated.NamedHeightRegimeRunOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs X Xb r0 blocked first i a ta Cfg T Tprev c0)
    (hgst : gstLagged S ≤ Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ r0)
    (hstart : (X.sup fun v =>
      (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r0)) v).st.h_max) <
        blocked)
    (hblocked : 1 ≤ blocked)
    {first' : Nat} (hwin : Restated.HeightWindowAtOn M S rho W X (blocked + 1 + 1) first')
    {i0 : Nat} {a0 : NamedAttestation V} {t0 : Time}
    (hiStop0 : i0 < first') (haHon0 : a0.val_index ∈ Hs t0)
    (hiEvent0 : rho.events[i0]? = some (Record.Event.tick a0.val_index t0))
    (hiOutput0 : ∃ out : M.N × List (NamedObject V),
      M.tick S a0.val_index (W i0 a0.val_index) t0 ⇢ out ∧ W (i0 + 1) a0.val_index = out.1 ∧
        Object.attest a0 ∈ out.2)
    (hrow0 : a0.height_pair.erase.height? = some (blocked + 1 + 1))
    (hgstLo : lo + 4 * S.E.Δ * (S.hc.R * readyLag : Nat) ≤
      Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ r0)
    (hlo : lo ≤ M.opening S.E S.hc (a.round - S.hc.η_SG))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S k + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    ∃ (i' : Nat) (a' : NamedAttestation V) (ta' : Time)
      (Cfg' T' : NamedBlock V),
      Restated.NamedHeightRegimeRunOn M S rho W (fun t => W (strictEventIndex rho t))
        Hs X Xb r0 (blocked + 1) first' i' a' ta' Cfg' T' T (a.round + 1) ∧
      a.round < a'.round ∧ Block.Preceq T.erase T'.erase := by
  classical
  have hframe' := Restated.NamedHeightRegimeRunOn.frame_succ_main facts hf hHs
    hHsXb hX hXXb hcom hbelow h hblocked hwin hlo hA
  let P : Round → Prop := fun r =>
    ∃ (j : Nat) (b : NamedAttestation V) (tb : Time),
      b.round = r ∧ j < first' ∧ b.val_index ∈ Hs tb ∧
        rho.events[j]? = some (Record.Event.tick b.val_index tb) ∧
        (∃ out : M.N × List (NamedObject V),
          M.tick S b.val_index (W j b.val_index) tb ⇢ out ∧ W (j + 1) b.val_index = out.1 ∧
            Object.attest b ∈ out.2) ∧
        b.height_pair.erase.height? = some (blocked + 1 + 1)
  have hex : ∃ r, P r :=
    ⟨a0.round, i0, a0, t0, rfl, hiStop0, haHon0, hiEvent0,
      hiOutput0, hrow0⟩
  obtain ⟨i', a', ta', har, hi, haHon, hevent, hout, hrow⟩ :=
    Nat.find_spec hex
  have hemit : Restated.Vocabulary.Execution.NamedRun.emits M S rho W a'.val_index
      (Object.attest a') ta' :=
    ⟨i', hevent, hout⟩
  have htime : ta' = Restated.Vocabulary.Execution.Setup.a M S a'.round :=
    (Restated.Vocabulary.Proofs.Optimistic.emits_attest_shape facts S W hf.onePath hemit).2
  have hminimal : ∀ (b : NamedAttestation V) (tb : Time),
      b.val_index ∈ Hs tb →
      Restated.Vocabulary.Execution.NamedRun.emits M S rho W b.val_index (Object.attest b) tb →
      b.height_pair.erase.height? = some (blocked + 1 + 1) →
      a'.round ≤ b.round := by
    intro b tb hbHon hbemit hbrow
    by_contra hnot
    have hlt : b.round < a'.round := Nat.lt_of_not_ge hnot
    have htb : tb < ta' := by
      rw [(Restated.Vocabulary.Proofs.Optimistic.emits_attest_shape facts S W hf.onePath hbemit).2,
        htime]
      exact Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S hlt
    obtain ⟨j, hj, hbout⟩ := hbemit
    have hjFirst : j < first' :=
      (Restated.attestationIndex_lt_of_time_ltOn facts hf hj hevent htb).trans hi
    have hPb : P b.round :=
      ⟨j, b, tb, rfl, hjFirst, hbHon, hj, hbout, hbrow⟩
    have hle := Nat.find_min' hex hPb
    rw [← har] at hle
    exact (not_le_of_gt hlt) hle
  have hiStart :
      inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r0) ≤ i' := by
    by_contra hnot
    obtain ⟨out, hout1, hout2, hout3⟩ := hout
    exact Restated.noLocalHeightPairBefore_of_frontier_ltOn facts S Hs Xb X hf hX
      (hstart.trans_le ((Nat.le_succ blocked).trans (Nat.le_succ _)))
      (Nat.lt_of_not_ge hnot) haHon hevent out hout1 hout2 hout3 hrow
  obtain ⟨n', hn'⟩ := actionReadFrom_nonempty₇₁w facts S
    (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a'.round)) a'.val_index)
    a'.round
  obtain ⟨o, ho⟩ := (p49% actionFGSource_nonempty₄₉) facts S n'
  obtain ⟨-, -, hsrc⟩ :=
    Restated.honestEmittedHeightRow_exactFGSelectorWitnessOn facts S Hs Xb (Hs ta') hf haHon
      hemit hrow n' hn'
  obtain ⟨B, _, _, hBmem, _, hBh, _, _⟩ := hsrc o ho
  have hpX : a'.val_index ∈ X := by
    have hta0 : 0 ≤ ta' := by
      rw [htime]
      exact a_nonneg₇₁w facts S a'.round
    exact hX _ hta0 haHon
  have hc0' : a.round + 1 ≤ a'.round :=
    Restated.NamedHeightRegimeRunOn.round_succ_le_of_higherBlock facts hf h hpX hn' hBmem hBh
  have hframeAt : Restated.NamedHeightRegimeFrameOn M S rho W
      (fun t => W (strictEventIndex rho t)) Hs X Xb (blocked + 1)
      (first' - 1) T a'.round := {
    floor := hframe'.floor
    prevRun := hframe'.prevRun
    prevHeight := hframe'.prevHeight
    rootBelow := hframe'.rootBelow
    sourceAbove := hframe'.sourceAbove }
  have hfrontierAt : (X.sup fun u => (W i' u).st.h_max) < blocked + 1 + 2 :=
    Nat.lt_succ_of_le (hwin.before i' hi)
  have hloOpen' : lo ≤ M.opening S.E S.hc (a'.round - S.hc.η_SG) :=
    hlo.trans (facts.gr.NamedOutageClosure_opening_mono S
      (Nat.sub_le_sub_right (Nat.le_of_succ_le hc0') _))
  obtain ⟨Cfg', T0, hseed', hpost', hG1'⟩ :=
    Restated.honestHeightRow_prefixFGSelectorCone_of_namedHeightRegimeFrameOn facts S Hs Xb X hf
      hHs hHsXb hX hXXb hgst hframeAt hiStart hi haHon hevent hout hrow
      hfrontierAt hgstLo hloOpen'
  obtain ⟨K, _hKmem, hKerase, hKheight, hKCfg, hKrun⟩ :=
    Restated.action_named_checkpointOn facts S Hs Xb hf (hHsXb _ hseed'.signerHonest) hn'
      (hseed'.sourceMem n' hn')
  have hKT0 : K.erase = T0 :=
    hKerase.trans hseed'.checkpointDerived.symm
  have hseedK : Restated.PrefixFGSelectorConeAtOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs Xb (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r0)) first'
      (blocked + 1) i' a' ta' Cfg' K.erase := by
    rw [hKT0]
    exact hseed'
  have hsigner' : a'.val_index ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S a'.round) := by
    rw [← htime]
    exact hseed'.signerHonest
  have hoCfg : Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n' ⇢ some Cfg'.erase := by
    have he := hseed'.exactFGSource n' hn' o ho
    rw [he] at ho
    exact ho
  have hTCfg' : NamedBlock.Preceq T Cfg' :=
    hframeAt.sourceAbove a'.val_index a'.round hsigner'
      (Nat.le_sub_one_of_lt (Restated.PrefixFGSelectorConeAtOn.actionPrefix_lt facts hf hseed'))
      (Restated.PrefixFGSelectorConeAtOn.actionHorizon facts hf hseed') n' hn' Cfg'
      (hseed'.sourceMem n' hn') hoCfg hseed'.sourceDerivedHeight
  have hTK : NamedBlock.Preceq T K := by
    rcases preceq_linear_Preceq (Proofs.NamedWire.erase_preceq hTCfg')
        (Proofs.NamedWire.erase_preceq hKCfg) with hTKraw | hKTRaw
    · obtain ⟨Q, hQK, hQerase⟩ :=
        Proofs.NamedAncestry.erased_ancestor_lift K hTKraw
      have hQrun : Restated.RunBlockOn M S rho W Xb Q :=
        Restated.blockInRun_of_ancestorOn facts S rho W Xb hKrun hQK
      have hQT : Q = T :=
        Restated.fixedRootNamed_run_eq_of_eraseOn facts hf hQrun hframeAt.prevRun hQerase
      rw [← hQT]
      exact hQK
    · obtain ⟨Q, hQT, hQerase⟩ :=
        Proofs.NamedAncestry.erased_ancestor_lift T hKTRaw
      have hQrun : Restated.RunBlockOn M S rho W Xb Q :=
        Restated.blockInRun_of_ancestorOn facts S rho W Xb hframeAt.prevRun hQT
      have hQK : Q = K :=
        Restated.fixedRootNamed_run_eq_of_eraseOn facts hf hQrun hKrun hQerase
      have hKT : NamedBlock.Preceq K T := by
        rw [← hQK]
        exact hQT
      have hmono := facts.cs.derive_height_mono S.E S.cfg hKT
      have hKsourceHeight :
          (M.derive_named S.E S.cfg K).h = blocked + 1 + 1 :=
        hKheight.trans hseed'.sourceDerivedHeight
      rw [hKsourceHeight] at hmono
      exact False.elim
        (Nat.not_succ_le_self (blocked + 1)
          (hmono.trans hframeAt.prevHeight))
  have hready := Restated.PrefixFGSelectorConeAtOn.ready_of_postGSTStart facts hf hseed' hgst
    (strictEventIndex_le_inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r0))
  obtain ⟨hTrun, _hTheight⟩ :=
    Restated.NamedHeightRegimeRunOn.checkpoint_runBlock facts hf hHsXb h
  refine ⟨i', a', ta', Cfg', K, {
    seed := hseedK
    checkpointPreceq := hKCfg
    checkpointErase := hKerase
    crossing := hwin
    frame := hframe'
    c0le := hc0'
    ready := hready
    postPrev := hpost'
    g1 := hG1'
    pred := ?_
    minimal := hminimal }, Nat.lt_of_succ_le hc0',
      Proofs.NamedWire.erase_preceq hTK⟩
  intro b tb hb hbemit _hbefore R hRrun _hRh hpair n hn hR _w _hw _time
    _hfrontier _hroot
  have hbrow : b.height_pair.erase.height? = some (blocked + 1) := by
    rw [hpair]
    rfl
  have htbA : tb = Restated.Vocabulary.Execution.Setup.a M S b.round :=
    (Restated.Vocabulary.Proofs.Optimistic.emits_attest_shape facts S W hf.onePath hbemit).2
  have hbtb : b.val_index ∈ Hs tb := by
    rw [htbA]
    exact hb
  have hRTerase : R.erase = T.erase :=
    Option.some.inj
      (Restated.NamedHeightRegimeRunOn.witness_eq facts hf hHs hHsXb hX hXXb hcom hbelow h
        hbtb hbemit hbrow hlo hA n hn _ hR)
  have hRT : R = T := Restated.fixedRootNamed_run_eq_of_eraseOn facts hf hRrun hTrun hRTerase
  rw [hRT]
  exact hTK

/-- Under the bundle with path `W`, the committee majority and the weight bound, for a run-scoped
    named regime along `W` at `blocked`, if `gstLagged ≤ Γ_neg1 r0`, the largest `h_max` over `X` in
    the world of `W` at `S.a r0` is less than `blocked`, `1 ≤ blocked`, `blocked + 2` is first
    crossed over `X` along `W` at `first'`, and the bounds `hgstLo`, `hlo` and `hA` hold, then some
    run-scoped named regime along `W` at `blocked + 1` with first crossing `first'` has previous
    checkpoint `T`, a later source round, and a checkpoint that is a descendant of `T`. -/
theorem NamedHeightRegimeRunOn.succ_named (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} {Hs : Int → Finset V} {X Xb : Finset V} {lo : Int}
    {W : Nat → V → M.N}
    {r0 : Round} {blocked : Height}
    {first i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hX : ∀ t : Int, 0 ≤ t → Hs t ⊆ X) (hXXb : X ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hbelow : BelowOneThirdOn S rho Hs)
    (h : Restated.NamedHeightRegimeRunOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs X Xb r0 blocked first i a ta Cfg T Tprev c0)
    (hgst : gstLagged S ≤ Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ r0)
    (hstart : (X.sup fun v =>
      (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r0)) v).st.h_max) <
        blocked)
    (hblocked : 1 ≤ blocked)
    {first' : Nat}
    (hfirst' : Restated.FirstHeightProgressAtOn M S rho W X (blocked + 1 + 1) first')
    (hgstLo : lo + 4 * S.E.Δ * (S.hc.R * readyLag : Nat) ≤
      Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ r0)
    (hlo : lo ≤ M.opening S.E S.hc (a.round - S.hc.η_SG))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S k + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    ∃ (i' : Nat) (a' : NamedAttestation V) (ta' : Time)
      (Cfg' T' : NamedBlock V),
      Restated.NamedHeightRegimeRunOn M S rho W (fun t => W (strictEventIndex rho t))
        Hs X Xb r0 (blocked + 1) first' i' a' ta' Cfg' T' T (a.round + 1) ∧
      a.round < a'.round ∧ Block.Preceq T.erase T'.erase := by
  have hcross : Restated.PrefixHeightCrossingWitnessOn M S rho W X Xb first' (blocked + 1) :=
    Restated.prefixHeightCrossingWitness_of_frontier_eqOn facts S Hs Xb X hf hXXb
      (Nat.succ_le_succ (Nat.zero_le blocked)) hfirst'.frontier
  have hT : ∀ (j : Nat) (e : Record.Event V), j < first' → rho.events[j]? = some e →
      e.time ≤ rho.horizon := by
    intro j e _ hj
    exact (hf.in_horizon e (List.mem_of_getElem? hj)).2
  obtain ⟨i0, a0, t0, -, hiStop0, haHon0, hiEvent0, hiOutput0, -, -, hrest⟩ :=
    Restated.prefixHeightCrossing_exactFGSelectorWitnessOn facts S Hs Xb X hf hHs
      (hbelow _ le_rfl) hT hcross
      (start := inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r0))
      (Restated.noLocalHeightPairBefore_of_frontier_ltOn facts S Hs Xb X hf hX
        (hstart.trans_le (Nat.le_succ blocked)))
  obtain ⟨n0, hn0⟩ := actionReadFrom_nonempty₇₁w facts S
    (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a0.round)) a0.val_index)
    a0.round
  obtain ⟨o0, ho0⟩ := (p49% actionFGSource_nonempty₄₉) facts S n0
  obtain ⟨_, _, _, _, _, _, _, hrow0⟩ := (hrest n0 hn0).2 o0 ho0
  have hrow0' :
      a0.height_pair.erase.height? = some (blocked + 1 + 1) := by
    rcases hrow0 with ht | ht <;> exact ht ▸ rfl
  have ht0Hor : t0 ≤ rho.horizon :=
    (hf.in_horizon _ (List.mem_of_getElem? hiEvent0)).2
  have haHonT0 : a0.val_index ∈ Hs t0 := hHs _ _ ht0Hor haHon0
  exact Restated.NamedHeightRegimeRunOn.succ_of_row_named facts hf hHs
    hHsXb hX hXXb hcom hbelow h hgst hstart hblocked
    (Restated.FirstHeightProgressAtOn.toWindow hfirst') hiStop0 haHonT0 hiEvent0 hiOutput0 hrow0'
    hgstLo hlo hA

/-- Under the bundle with path `W`, the committee majority and the weight bound, for a run-scoped
    named regime along `W` at `blocked`, if `gstLagged ≤ Γ_neg1 r0`, the largest `h_max` over `X` in
    the world of `W` at `S.a r0` is less than `blocked`, `1 ≤ blocked`, the largest `h_max` over `X`
    never exceeds `blocked + 2` along `W`, a member of the set for its emission instant emits along
    `W` a row at height `blocked + 2`, and the bounds `hgstLo`, `hlo` and `hA` hold, then some
    run-scoped named regime along `W` at `blocked + 1`, with the whole run as its window, has
    previous checkpoint `T`, a later source round, and a checkpoint that is a descendant of `T`. -/
theorem NamedHeightRegimeRunOn.succ_uncrossed_named (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} {Hs : Int → Finset V} {X Xb : Finset V} {lo : Int}
    {W : Nat → V → M.N}
    {r0 : Round} {blocked : Height}
    {first i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hX : ∀ t : Int, 0 ≤ t → Hs t ⊆ X) (hXXb : X ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hbelow : BelowOneThirdOn S rho Hs)
    (h : Restated.NamedHeightRegimeRunOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs X Xb r0 blocked first i a ta Cfg T Tprev c0)
    (hgst : gstLagged S ≤ Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ r0)
    (hstart : (X.sup fun v =>
      (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r0)) v).st.h_max) <
        blocked)
    (hblocked : 1 ≤ blocked)
    (hnever : ∀ j : Nat, (X.sup fun v => (W j v).st.h_max) ≤ blocked + 1 + 1)
    {b : NamedAttestation V} {tb : Time}
    (hb : b.val_index ∈ Hs tb)
    (hemit : Restated.Vocabulary.Execution.NamedRun.emits M S rho W b.val_index (Object.attest b) tb)
    (hrow : b.height_pair.erase.height? = some (blocked + 1 + 1))
    (hgstLo : lo + 4 * S.E.Δ * (S.hc.R * readyLag : Nat) ≤
      Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ r0)
    (hlo : lo ≤ M.opening S.E S.hc (a.round - S.hc.η_SG))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S k + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    ∃ (i' : Nat) (a' : NamedAttestation V) (ta' : Time)
      (Cfg' T' : NamedBlock V),
      Restated.NamedHeightRegimeRunOn M S rho W (fun t => W (strictEventIndex rho t))
        Hs X Xb r0 (blocked + 1) (rho.events.length + 1) i' a' ta' Cfg' T' T (a.round + 1) ∧
      a.round < a'.round ∧ Block.Preceq T.erase T'.erase := by
  obtain ⟨j, hj, hout⟩ := hemit
  have hjlt : j < rho.events.length :=
    (List.getElem?_eq_some_iff.mp hj).1
  exact Restated.NamedHeightRegimeRunOn.succ_of_row_named facts hf hHs
    hHsXb hX hXXb hcom hbelow h hgst hstart hblocked
    ⟨Nat.succ_pos _, fun k _ => hnever k⟩ (Nat.lt_succ_of_lt hjlt)
      hb hj hout hrow hgstLo hlo hA

/-- Under the bundle with path `W`, the committee majority and the weight bound, with `X` containing
    every set of the family from instant `0` and inside `Xb`, if `gstLagged ≤ Γ_neg1 r0`, a
    run-scoped named base holds along `W` at `blocked`, every height `blocked + m + 1` with
    `1 ≤ m ≤ n` is first crossed over `X` along `W` at some index,
    `lo + 4Δ·(R·readyLag) ≤ Γ_neg1 r0`, `lo ≤ opening (r0 − η_SG)` and the grade-2 awake hypothesis
    `hA` holds, then some run-scoped named regime holds along `W` at `blocked + n`. -/
theorem NamedHeightRegimeBaseRunOn.exists_regime_above_named (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} {Hs : Int → Finset V} {X Xb : Finset V} {lo : Int}
    {W : Nat → V → M.N}
    {r0 : Round} {blocked : Height} {first : Nat} {Tprev : NamedBlock V}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hX : ∀ t : Int, 0 ≤ t → Hs t ⊆ X) (hXXb : X ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hbelow : BelowOneThirdOn S rho Hs)
    (hgst : gstLagged S ≤ Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ r0)
    (h : Restated.NamedHeightRegimeBaseRunOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs X Xb r0 blocked first Tprev)
    (n : Nat)
    (hcross : ∀ m : Nat, 1 ≤ m → m ≤ n →
      ∃ f : Nat, Restated.FirstHeightProgressAtOn M S rho W X (blocked + m + 1) f)
    (hgstLo : lo + 4 * S.E.Δ * (S.hc.R * readyLag : Nat) ≤
      Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ r0)
    (hloOpen : lo ≤ M.opening S.E S.hc (r0 - S.hc.η_SG))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S k + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    ∃ (first_n i : Nat) (a : NamedAttestation V) (ta : Time)
      (Cfg T Tprev' : NamedBlock V) (c0 : Round),
      Restated.NamedHeightRegimeRunOn M S rho W (fun t => W (strictEventIndex rho t))
        Hs X Xb r0 (blocked + n) first_n i a ta Cfg T Tprev' c0 := by
  induction n with
  | zero =>
      obtain ⟨i, a, ta, Cfg, T, hreg⟩ :=
        Restated.NamedHeightRegimeBaseRunOn.exists_regime_closed facts hf hHs hHsXb hX hXXb
          hbelow hgst h hgstLo hloOpen
      exact ⟨first, i, a, ta, Cfg, T, Tprev, a.round, hreg⟩
  | succ n ih =>
      obtain ⟨first_n, i, a, ta, Cfg, T, Tprev', c0, hreg⟩ :=
        ih (fun m hm1 hmn => hcross m hm1 (hmn.trans (Nat.le_succ n)))
      obtain ⟨f, hfn⟩ :=
        hcross (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) (le_refl _)
      have hfn' : Restated.FirstHeightProgressAtOn M S rho W X
          (blocked + n + 1 + 1) f := hfn
      obtain ⟨i', a', ta', Cfg', T', h', -, -⟩ :=
        Restated.NamedHeightRegimeRunOn.succ_named facts hf hHs hHsXb
          hX hXXb hcom hbelow hreg hgst
          (h.start.trans_le (Nat.le_add_right blocked n))
          (h.positive.trans (Nat.le_add_right blocked n)) hfn' hgstLo
          (Restated.NamedHeightRegimeRunOn.lo_le_opening_l71 facts hf hreg hloOpen) hA
      exact ⟨f, i', a', ta', Cfg', T', T, a.round + 1, h'⟩

/-- Under the bundle with path `W`, the committee majority and the weight bound, with `X` containing
    every set of the family from instant `0` and inside `Xb`, if `gstLagged ≤ Γ_neg1 r0`, a
    run-scoped named base holds along `W` at `blocked`, a member of the set for its emission instant
    emits along `W` a row at height `blocked + n + 1`, and the bounds `hgstLo`, `hloOpen` and `hA`
    hold, then some run-scoped named regime holds along `W` at `blocked + n`. -/
theorem NamedHeightRegimeBaseRunOn.exists_regime_of_row_named (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} {Hs : Int → Finset V} {X Xb : Finset V} {lo : Int}
    {W : Nat → V → M.N}
    {r0 : Round} {blocked : Height} {first : Nat} {Tprev : NamedBlock V}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hX : ∀ t : Int, 0 ≤ t → Hs t ⊆ X) (hXXb : X ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hbelow : BelowOneThirdOn S rho Hs)
    (hgst : gstLagged S ≤ Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ r0)
    (h : Restated.NamedHeightRegimeBaseRunOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs X Xb r0 blocked first Tprev)
    (n : Nat) {b : NamedAttestation V} {tb : Time}
    (hb : b.val_index ∈ Hs tb)
    (hemit : Restated.Vocabulary.Execution.NamedRun.emits M S rho W b.val_index (Object.attest b) tb)
    (hrow : b.height_pair.erase.height? = some (blocked + n + 1))
    (hgstLo : lo + 4 * S.E.Δ * (S.hc.R * readyLag : Nat) ≤
      Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ r0)
    (hloOpen : lo ≤ M.opening S.E S.hc (r0 - S.hc.η_SG))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S k + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    ∃ (first_n i : Nat) (a : NamedAttestation V) (ta : Time)
      (Cfg T Tprev' : NamedBlock V) (c0 : Round),
      Restated.NamedHeightRegimeRunOn M S rho W (fun t => W (strictEventIndex rho t))
        Hs X Xb r0 (blocked + n) first_n i a ta Cfg T Tprev' c0 := by
  classical
  by_cases hcross : ∃ f : Nat,
      Restated.FirstHeightProgressAtOn M S rho W X (blocked + n + 1) f
  · obtain ⟨f, hfn⟩ := hcross
    exact Restated.NamedHeightRegimeBaseRunOn.exists_regime_above_named
      facts hf hHs hHsXb hX hXXb hcom hbelow hgst h n
      (Restated.exists_crossings_below_top_namedOn facts S Hs Xb X hf h.crossing hfn) hgstLo
      hloOpen hA
  · have hnever : ∀ j : Nat,
        (X.sup fun v => (W j v).st.h_max) ≤ blocked + n + 1 := by
      intro j
      by_contra hn
      obtain ⟨f, _, hfn⟩ := Restated.exists_firstHeightProgressAtOn facts S Hs Xb X hf
        (Nat.succ_le_succ (Nat.zero_le _)) (Nat.lt_of_not_le hn)
      exact hcross ⟨f, hfn⟩
    cases n with
    | zero =>
        exfalso
        have h1 := hnever first
        rw [h.crossing.frontier] at h1
        exact Nat.not_succ_le_self _ h1
    | succ n =>
        have hbX : b.val_index ∈ X := by
          have htb0 : 0 ≤ tb := by
            rw [(Restated.Vocabulary.Proofs.Optimistic.emits_attest_shape facts S W hf.onePath
              hemit).2]
            exact a_nonneg₇₁w facts S b.round
          exact hX _ htb0 hb
        obtain ⟨j, hj, hout⟩ := hemit
        have hfront : blocked + n + 1 + 1 ≤
            X.sup fun x => (W (j + 1) x).st.h_max :=
          Restated.honestEmittedHeight_le_honestHMaxBeforeIndexOn facts
            S Hs Xb X hf hbX hj hout (Nat.lt_succ_self j) hrow
        have hcrossings : ∀ m : Nat, 1 ≤ m → m ≤ n →
            ∃ f : Nat,
              Restated.FirstHeightProgressAtOn M S rho W X (blocked + m + 1) f := by
          intro m _ hmn
          obtain ⟨f, _, hfn⟩ := Restated.exists_firstHeightProgressAtOn facts S Hs Xb X hf
            (H := blocked + m + 1)
            (Nat.succ_le_succ (Nat.zero_le _))
            (lt_of_lt_of_le (Nat.succ_lt_succ (Nat.lt_succ_of_le
              (Nat.add_le_add_left hmn blocked))) hfront)
          exact ⟨f, hfn⟩
        obtain ⟨first_n, i, a, ta, Cfg, T, Tprev', c0, hreg⟩ :=
          Restated.NamedHeightRegimeBaseRunOn.exists_regime_above_named
            facts hf hHs hHsXb hX hXXb hcom hbelow hgst h n hcrossings
            hgstLo hloOpen hA
        obtain ⟨i', a', ta', Cfg', T', h', _, _⟩ :=
          Restated.NamedHeightRegimeRunOn.succ_uncrossed_named facts hf
            hHs hHsXb hX hXXb hcom hbelow hreg hgst
            (h.start.trans_le (Nat.le_add_right blocked n))
            (h.positive.trans (Nat.le_add_right blocked n))
            hnever hb ⟨j, hj, hout⟩ hrow hgstLo
            (Restated.NamedHeightRegimeRunOn.lo_le_opening_l71 facts hf hreg hloOpen) hA
        exact ⟨_, i', a', ta', Cfg', T', T, _, h'⟩

/-- Under the bundle with path `W`, the committee majority and the weight bound, with `X` containing
    every set of the family from instant `0` and inside `Xb`, if `gstLagged ≤ Γ_neg1 r0`, a
    run-scoped named base holds along `W` at `blocked` with first crossing by the inclusive index of
    `S.a deadline`, `read` is in the horizon, `s` is after the deadline's opening slot with
    `read ≤ confirmation_time s` and `vote_time s + Δ` in the horizon, and the bounds `hgstLo`,
    `hloOpen` and `hA` hold, then some run block `T` read through `Xb` along `W` has height at least
    `u`'s `h_max` in `W (strictEventIndex rho read)` minus one, and is an ancestor of every head
    every member of the set for `vote_time s` can vote at `s`. -/
theorem NamedHeightRegimeBaseRunOn.exists_namedCommonPreviousHeadAncestor_in_frontierBand_through_confirmation_after_deadline
    (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} {Hs : Int → Finset V} {X Xb : Finset V} {lo : Int}
    {W : Nat → V → M.N}
    {r0 : Round} {blocked : Height} {first : Nat} {Tprev : NamedBlock V}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hX : ∀ t : Int, 0 ≤ t → Hs t ⊆ X) (hXXb : X ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hbelow : BelowOneThirdOn S rho Hs)
    (hgst : gstLagged S ≤ Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ r0)
    (h : Restated.NamedHeightRegimeBaseRunOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs X Xb r0 blocked first Tprev)
    {deadline : Round}
    (hdeadline : first ≤
      inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S deadline))
    {read : Time} (hhor : read ≤ rho.horizon)
    {s : Slot} (hs : M.opening_slot S.hc deadline + 1 ≤ s)
    (hnext : read ≤ M.confirmation_time S.E s)
    (hshor : M.vote_time S.E s + S.E.Δ ≤ rho.horizon)
    {u : V} (_hu : u ∈ Hs read)
    (hgstLo : lo + 4 * S.E.Δ * (S.hc.R * readyLag : Nat) ≤
      Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ r0)
    (hloOpen : lo ≤ M.opening S.E S.hc (r0 - S.hc.η_SG))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S k + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    ∃ T : NamedBlock V,
      Restated.RunBlockOn M S rho W Xb T ∧
      (W (strictEventIndex rho read) u).st.h_max - 1 ≤ (M.derive_named S.E S.cfg T).h ∧
      ∀ w ∈ Hs (M.vote_time S.E s), ∀ cc : M.Cache,
        M.onPhaseTick S.E S.hc
          (W (strictEventIndex rho (M.vote_time S.E s)) w).st.core.toHealing
          (M.vote_time S.E s)
          (W (strictEventIndex rho (M.vote_time S.E s)) w).cache ⇢ cc →
        let n := M.mkNode
          (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) w).st
            (M.vote_time S.E s))
          (W (strictEventIndex rho (M.vote_time S.E s)) w).record cc
        ∀ Tr : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ Tr →
        ∀ L : Finset (GoldfishVote V),
          M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
        ∀ L' : Finset (GoldfishVote V),
          M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
        ∀ H : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
            (M.toHealing n.st.core) Tr L L' (n.st.core.s - 1) ⇢ H →
          Block.Preceq T.erase H := by
  by_cases hlow : (W (strictEventIndex rho read) u).st.h_max - 1 ≤ blocked + 1
  · obtain ⟨i, a, ta, Cfg, T, hreg⟩ :=
      Restated.NamedHeightRegimeBaseRunOn.exists_regime_closed facts hf hHs hHsXb hX hXXb
        hbelow hgst h hgstLo hloOpen
    have hi : i < inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S deadline) :=
      hreg.seed.indexLtStop.trans_le hdeadline
    have hfilter :
        rho.events.filter
            (fun e => decide (e.time ≤ Restated.Vocabulary.Execution.Setup.a M S deadline)) =
          rho.events.take
            (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S deadline)) := by
      simpa only [inclusiveEventIndex] using
        Restated.filter_eq_takeOn facts S Hs Xb hf _
          (Restated.downward_le (Restated.Vocabulary.Execution.Setup.a M S deadline))
    have hmem : Record.Event.tick a.val_index ta ∈
        rho.events.take
          (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S deadline)) := by
      apply List.mem_of_getElem? (i := i)
      rw [List.getElem?_take_of_lt hi]
      exact hreg.seed.exactTick
    rw [← hfilter] at hmem
    have haround : a.round ≤ deadline := by
      apply (Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).le_iff_le.mp
      simpa only [Record.Event.time, hreg.seed.actionTime_eq, decide_eq_true_eq, Record.Event.time] using
        (List.mem_filter.mp hmem).2
    obtain ⟨hTrun, hTheight⟩ :=
      Restated.NamedHeightRegimeRunOn.checkpoint_runBlock facts hf hHsXb hreg
    refine ⟨T, hTrun, ?_, ?_⟩
    · rw [hTheight]
      exact hlow
    · exact Restated.NamedHeightRegimeRunOn.heads_from_firstInterior facts hf hHs hHsXb hX
        hXXb hcom hbelow hreg
        ((Nat.add_le_add_right
          (facts.gr.opening_slot_le_of_le S.hc haround) 1).trans hs)
        hshor (Restated.NamedHeightRegimeRunOn.lo_le_opening_l71 facts hf hreg hloOpen) hA
  · have hlarge : 1 < (W (strictEventIndex rho read) u).st.h_max := by
      apply Nat.sub_pos_iff_lt.mp
      exact (Nat.zero_le (blocked + 1)).trans_lt
        (Nat.lt_of_not_ge hlow)
    obtain ⟨a, ta, ha, hemit, hta, hrow, -⟩ :=
      Restated.frontier_confirmationWitnessOn facts S Hs Xb hf hHs hHsXb
        (honestWeightMajorityOn_of_belowOneThirdOn hbelow) hhor hlarge
    have haTa : a.val_index ∈ Hs ta := hHs _ _ hta.le ha
    let n := ((W (strictEventIndex rho read) u).st.h_max - 1) - (blocked + 1)
    have heq : blocked + n + 1 = (W (strictEventIndex rho read) u).st.h_max - 1 := by
      calc
        blocked + n + 1 = n + (blocked + 1) := by ac_rfl
        _ = (W (strictEventIndex rho read) u).st.h_max - 1 := Nat.sub_add_cancel
          (Nat.le_of_lt (Nat.lt_of_not_ge hlow))
    have hrow' :
        a.height_pair.erase.height? = some (blocked + n + 1) := by
      rw [heq]
      exact hrow
    obtain ⟨first_n, i, source, tsource, Cfg, T, Tprev', c0, hreg⟩ :=
      Restated.NamedHeightRegimeBaseRunOn.exists_regime_of_row_named
        facts hf hHs hHsXb hX hXXb hcom hbelow hgst h n haTa hemit hrow'
        hgstLo hloOpen hA
    have hactionLt : Restated.Vocabulary.Execution.Setup.a M S a.round < read := by
      rw [← (Restated.Vocabulary.Proofs.Optimistic.emits_attest_shape facts S W hf.onePath hemit).2]
      exact hta
    have hsourceRound : source.round ≤ a.round :=
      hreg.minimal a ta haTa hemit hrow'
    have hslot : M.opening_slot S.hc source.round + 1 ≤ s :=
      (Nat.add_le_add_right
        (facts.gr.opening_slot_le_of_le S.hc hsourceRound) 1).trans
          (firstInterior_le_of_action_lt_confirmation₇₁w facts S
            (hactionLt.trans_le hnext))
    obtain ⟨hTrun, hTheight⟩ :=
      Restated.NamedHeightRegimeRunOn.checkpoint_runBlock facts hf hHsXb hreg
    refine ⟨T, hTrun, ?_, ?_⟩
    · rw [hTheight, heq]
    · exact Restated.NamedHeightRegimeRunOn.heads_from_firstInterior facts hf hHs hHsXb hX
        hXXb hcom hbelow hreg hslot hshor
        (Restated.NamedHeightRegimeRunOn.lo_le_opening_l71 facts hf hreg hloOpen) hA

/-- Under the bundle along `W`, the committee majority, the weight bound, the carrier recurrence
    within `gap` rounds from `t₀` and the timeout delay bound, if `t_GST ≤ S.a rGST`, `read` is at
    or after the action instant of the progress deadline from `rGST` and within the horizon, `s` is
    after the deadline's opening slot with `read ≤ confirmation_time s` and `vote_time s + Δ` within
    the horizon, `u` is in the set for `read`, `lo ≤ S.a rGST`, `lo ≤ opening (rGST + 2 − η_SG)`,
    `t₀ ≤ S.a (rGST + 2)` and the grade-2 awake hypothesis `hA` holds, then some run block `T` read
    through `Xb` along `W` has height at least `u`'s `h_max` in `W (strictEventIndex rho read)`
    minus one, and is an ancestor of every head every member of the set for `vote_time s` can vote
    at `s`. -/
theorem exists_namedCommonPreviousHeadAncestor_in_frontierBand_through_confirmation_after_GSTOn
    (facts : Record.Facts M) {delayExtra : Nat}
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hbelow : BelowOneThirdOn S rho Hs)
    {rGST gap : Round} {t₀ : Int}
    (hrec : Restated.MultiProposerRecurrenceOn M S Hs gap t₀ rho.horizon)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S rGST))
    {read : Time}
    (hread : (Restated.Vocabulary.Execution.Setup.a M S
      (fgSafetyProgressDeadline S rho rGST gap delayExtra)) ≤ read)
    (hhor : read ≤ rho.horizon)
    {s : Slot}
    (hs : (M.opening_slot S.hc)
      (fgSafetyProgressDeadline S rho rGST gap delayExtra) + 1 ≤ s)
    (hnext : read ≤ M.confirmation_time S.E s)
    (hshor : M.vote_time S.E s + S.E.Δ ≤ rho.horizon)
    {u : V} (hu : u ∈ Hs read)
    (hloPost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S rGST))
    (hloOpen : lo ≤ M.opening S.E S.hc (rGST + 2 - S.hc.η_SG))
    (ht₀ : t₀ ≤ (Restated.Vocabulary.Execution.Setup.a M S (rGST + 2)))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    ∃ T : NamedBlock V,
      Restated.RunBlockOn M S rho W Xb T ∧
      (W (strictEventIndex rho read) u).st.h_max - 1 ≤ (M.derive_named S.E S.cfg T).h ∧
      ∀ w ∈ Hs (M.vote_time S.E s), ∀ cc : M.Cache,
        M.onPhaseTick S.E S.hc
          (W (strictEventIndex rho (M.vote_time S.E s)) w).st.core.toHealing
          (M.vote_time S.E s)
          (W (strictEventIndex rho (M.vote_time S.E s)) w).cache ⇢ cc →
        let n := M.mkNode
          (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) w).st
            (M.vote_time S.E s))
          (W (strictEventIndex rho (M.vote_time S.E s)) w).record cc
        ∀ Tr : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ Tr →
        ∀ L : Finset (GoldfishVote V),
          M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
        ∀ L' : Finset (GoldfishVote V),
          M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
        ∀ H : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
            (M.toHealing n.st.core) Tr L L' (n.st.core.s - 1) ⇢ H →
          Block.Preceq T.erase H := by
  have hX : ∀ t : Int, 0 ≤ t → Hs t ⊆ Xb := fun t _ => hHsXb t
  have hXXb : Xb ⊆ Xb := Finset.Subset.refl _
  have hlo : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (rGST + 2)) :=
    hloPost.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.le_add_right rGST 2))
  obtain ⟨blocked, first, Tprev, hfirst, hbase⟩ :=
    Restated.exists_namedHeightRegimeBaseRun_before_fgSafetyProgressDeadlineOn facts
      S Hs Xb Xb hf hHs hHsXb hX hXXb hcom hbelow hrec hdelay hpost (hread.trans hhor)
      hlo hloOpen ht₀ hA
  exact Restated.NamedHeightRegimeBaseRunOn.exists_namedCommonPreviousHeadAncestor_in_frontierBand_through_confirmation_after_deadline
    facts hf hHs hHsXb hX hXXb hcom hbelow
    (Restated.Vocabulary.Proofs.HealingSurface.gstLagged_le_Γ_neg1_of_gst_le_a facts S rGST hpost)
    hbase hfirst hhor hs hnext hshor hu
    (Restated.lo_add_lag_le_Γ_neg1_l71 facts S rGST hloPost) hloOpen hA

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
local macro "p59% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_59)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

local macro "p64% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_64)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

end

end DecoupledConsensusModel.Sts.Restated
