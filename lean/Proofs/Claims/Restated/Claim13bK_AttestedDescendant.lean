import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bInvariantActive
import Proofs.Claims.Restated.Claim13bK_ConfirmedOld
import Proofs.Claims.Restated.Claim13bK_ConfirmedRecord
import Proofs.Claims.Restated.Claim13bK_ConfirmedRecordReaders
import Proofs.Claims.Restated.Claim13bK_FinBeforeTick
import Proofs.Claims.Restated.Claim13bK_Frame
import Proofs.Claims.Restated.Claim13bK_GradeOldHeads
import Proofs.Claims.Restated.Claim13bK_HeadsNewAnchor
import Proofs.Claims.Restated.Claim13bK_HeadsPersist
import Proofs.Claims.Restated.Claim13bK_InclusionAnchorTree
import Proofs.Claims.Restated.Claim13bK_InclusionTick
import Proofs.Claims.Restated.Claim13bK_LiveConfirmedSlots
import Proofs.Claims.Restated.Claim13bStepConeIter
import Proofs.Claims.Restated.Claim13bStepKitConfirm
import Proofs.Claims.Restated.Claim13bStepRoots
import Proofs.Claims.Restated.Claim13bStepSG
import Proofs.Claims.Restated.Claim13bW_Schedule
import Proofs.Claims.Restated.Claim13beRoute3_82
import Proofs.Claims.Restated.CommonViewOfFinalizedDescendantsFacts
import Proofs.Claims.Restated.Projection
import Proofs.Claims.Restated.Vocabulary_Execution_HealthyLocalFacts
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActive
import Model.Conditions.Claim13bInvariantActiveJoint
import Model.Conditions.Claim13bInvariantActiveSinceW
import Model.Conditions.Claim13bInvariantActiveTop
import Model.Conditions.Claim13bK_ConfirmedSettle
import Model.Conditions.Claim13bK_FinBeforeTick
import Model.Conditions.Claim13bK_Frame
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13bStepAssembly
import Model.Conditions.Claim13bStepCone
import Model.Conditions.Claim13bStepConeIter
import Model.Conditions.Claim13bStepKitTick
import Model.Conditions.Claim13bStepSG
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_5
import Model.Conditions.Claim13beRoute3_74
import Model.Conditions.Claim13beRoute3_83
import Model.Conditions.CommonViewOfFinalizedDescendantsFacts
import Model.Conditions.RunAll
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13bd
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Sts_Spec2Claims_Claim13bf
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_Grades_Main
import Model.Record.Wiring
import Proofs.Claims.Restated.Claim13bK_ConfirmedRecordReadersRecv

/-!
# The block an honest attester names as confirmed

Over a model `M : Record.Model V`: after the switch round, the block an honest active attester of
round `q` names as confirmed at `S.a q` is a descendant of every block `X` such that every honest
active member of the committee of round `q`'s opening slot votes for a descendant of `X`
(`attested_descendant_of_headsBelow`).
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
local macro "pHP% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13bK_HeadsPersist)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "pCW% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13bK_ConfirmedWake)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "pW% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13bK_ConfirmedStrongRoundWindow)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "pIT% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13bK_InclusionTick)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If `P` and `Q` lie on one chain and every honest active member of slot `s`'s committee votes
    there for a descendant of each, then some block `Z`, a descendant of `P` and of `Q`, has every
    such member voting for a descendant of `Z`. -/
theorem exists_join_headsBelow (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {s : Slot} {P Q : Block V}
    (h : Block.compatible P Q = true) (hP : Restated.HeadsBelow M S Sched x P s)
    (hQ : Restated.HeadsBelow M S Sched x Q s) :
    ∃ Z : Block V, Block.Preceq P Z ∧ Block.Preceq Q Z ∧ Restated.HeadsBelow M S Sched x Z s := by
  rcases compatible_cases h with hPQ | hQP
  · exact ⟨Q, hPQ, preceq_eq_true_iff_Preceq.mp (Block.preceq_self Q), hQ⟩
  · exact ⟨P, preceq_eq_true_iff_Preceq.mp (Block.preceq_self P), hQP, hP⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If `a + 2 ≤ q`, then `q − 1 + 1 = q` and `a ≤ q − 1`. -/
private theorem pred_facts_ad (a q : Nat) (h : a + 2 ≤ q) : q - 1 + 1 = q ∧ a ≤ q - 1 := by
  omega

/-- If `o₂ = o₁ + R`, `3 ≤ R` and `o₂ ≤ o`, then `o₁ + 2 ≤ o`. -/
private theorem slot_gap_ad (o₁ o₂ o R : Nat) (h2 : o₂ = o₁ + R) (hR : 3 ≤ R) (h1 : o₂ ≤ o) :
    o₁ + 2 ≤ o := by
  omega

/-- With the joint invariant at the switch round: if `q` is at least two rounds after the switch
    round, every honest active member of the committee of round `q`'s opening slot votes there for a
    descendant of `X`, `n` is the sts tick step at `S.a q`, `u` is an honest active attester of
    round `q`, and a round-`q` attestation `a` that `u`'s action can compute from its node state at
    step `n` names the root of a block `C` of `u`'s tree after the tick, then `X ⪯ C`. -/
theorem attested_descendant_of_headsBelow (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (hcatch : Restated.CatchUpOnWake M S x) (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (hsync : Restated.SynchronyFromWake M S x) (hthird : ∀ t : Int, t ≤ tE →
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
    {q : Round} (hq : Restated.switchRound M S tE + 2 ≤ q)
    {X : Block V} (hX : Restated.HeadsBelow M S Sched x X ((M.opening_slot S.hc q)))
    {n : Nat} (hn : Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S q))) {u : V} (hu : u ∈ Restated.HonRound M S Sched q)
    {C : NamedBlock V} (hC : C ∈ (x[n + 1][u].st).st.bodies)
    (a : NamedAttestation V)
    (ha : a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][u].st) u q)
    (hconf : a.confirmed = some C.root) :
    Block.Preceq X C.erase := by
  have hd := S.E.Δ_pos
  have hd1 : (1 : Int) ≤ S.E.Δ := hd
  obtain ⟨hqe, hq'⟩ := pred_facts_ad (Restated.switchRound M S tE) q hq
  obtain ⟨q', rfl⟩ : ∃ q' : Round, q = q' + 1 := ⟨q - 1, hqe.symm⟩
  replace hq' : Restated.switchRound M S tE ≤ q' := hq'
  -- the slot `s = o_q` and its condition
  have hsl : (M.opening_slot S.hc (Restated.switchRound M S tE + 1)) + 2 ≤ (M.opening_slot S.hc (q' + 1)) := by
    have h1 : (M.opening_slot S.hc (Restated.switchRound M S tE + 1 + 1)) ≤ (M.opening_slot S.hc (q' + 1)) :=
      facts.gr.opening_slot_mono S hq
    exact slot_gap_ad _ _ _ _ (facts.gr.opening_slot_succ S.hc (Restated.switchRound M S tE + 1)) S.hc.R_ge_three h1
  have hspos : 0 < (M.opening_slot S.hc (q' + 1)) :=
    lt_of_lt_of_le (by decide : (0 : Nat) < 2) (le_trans (Nat.le_add_left 2 _) hsl)
  have hop : (M.opening_slot S.hc (Restated.switchRound M S tE)) ≤ (M.opening_slot S.hc (Restated.switchRound M S tE + 1)) :=
    facts.gr.opening_slot_mono S (Nat.le_succ _)
  have hs0 : (M.opening_slot S.hc (Restated.switchRound M S tE)) + 2 ≤ (M.opening_slot S.hc (q' + 1)) :=
    le_trans (Nat.add_le_add_right hop 2) hsl
  have hta : M.confirmation_time S.E (M.opening_slot S.hc (q' + 1))
      = Restated.Vocabulary.Execution.Setup.a M S (q' + 1) :=
    Restated.confirmation_time_opening_slot facts S (q' + 1)
  have hm : Restated.tickStepAt M x n (M.confirmation_time S.E ((M.opening_slot S.hc (q' + 1)))) := by
    rw [hta]; exact hn
  obtain ⟨hn1, hn0⟩ := Restated.tickStepAt_time facts x hn
  have hvaw : u ∈ Sched.awakeThroughout (slotStart S.E.Δ ((M.opening_slot S.hc (q' + 1))) - S.E.Δ)
      (M.confirmation_time S.E ((M.opening_slot S.hc (q' + 1)))) :=
    Restated.honRound_awakeThroughout_confirmation facts S Sched (q' + 1) hu
  have hvhT : HonestThroughTime Sched ((Restated.Vocabulary.Execution.Setup.a M S (q' + 1))) u :=
    mem_honestThroughSet.1 (Restated.honRound_subset_honestThroughSet facts S Sched (q' + 1) hmono hu)
  have hvh' : HonestThroughTime Sched
      (M.confirmation_time S.E ((M.opening_slot S.hc (q' + 1)))) u := by
    rw [hta]; exact hvhT
  have hvh1 : Restated.HonestThrough M Sched x (n + 1) u := fun t ht => hvhT t (by rw [hn1] at ht; exact ht)
  have hvhn : Restated.HonestThrough M Sched x n u := fun t ht => hvhT t (by linarith)
  have hct : M.confirmation_time S.E ((M.opening_slot S.hc (q' + 1))) = slotStart S.E.Δ ((M.opening_slot S.hc (q' + 1))) + 6 * S.E.Δ :=
      (facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E ((M.opening_slot S.hc (q' + 1)))).symm
  have haw : u ∈ Sched.awake (M.confirmation_time S.E ((M.opening_slot S.hc (q' + 1)))) \
      Sched.adv (M.confirmation_time S.E ((M.opening_slot S.hc (q' + 1)))) :=
    Finset.mem_sdiff.2 ⟨mem_awake_of_awakeThroughout Sched hvaw (by rw [hct]; linarith) le_rfl,
      hvh' _ le_rfl⟩
  -- `u`'s tick at the confirmation instant has an outcome (a public instant, `u` awake and not
  -- held there)
  have hneConf : ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) u (Record.wakeStage M Sched (M.confirmation_time S.E
        ((M.opening_slot S.hc (q' + 1)))) x[n] u) (M.confirmation_time S.E ((M.opening_slot S.hc (q' + 1)))) ⇢ out :=
    Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono hm
      (by rw [hta]; exact Restated.action_emod_delta facts S (q' + 1)) haw
  -- the grade-2 awake test at `u`'s confirmation tick: that instant is round `(q' + 1)`'s action
  -- instant, the slot after the opening slot is in round `q' + 1`, and `u` is awake through
  -- `wAttest S ≥ 12Δ` before it, which covers the grade-2 window
  have hrunC : M.awake_for_grade2 (Setup.alwaysAwake S) u
      (Record.wakeStage M Sched (M.confirmation_time S.E ((M.opening_slot S.hc (q' + 1)))) x[n] u)
      (M.round_of S.hc ((M.opening_slot S.hc (q' + 1)) + 1)) := by
    have hround : M.round_of S.hc (M.opening_slot S.hc (q' + 1) + 1) = q' + 1 :=
      facts.gr.round_of_opening_slot_add S.hc (q' + 1)
        (lt_of_lt_of_le (by norm_num) S.hc.R_ge_three)
    rw [hround, hta]
    obtain ⟨τ, hlbl, hτ⟩ := hn
    refine Restated.run_fact_g2 facts S Sched x n τ (q' + 1) u hlbl hτ ?_ (by
      rw [hτ]
      exact Restated.honest_upTo_of_mono hmono (by rw [← hta]; exact haw))
    have hw := (Finset.mem_sdiff.1 hu).1
    have h12 := twelve_delta_le_wAttest S
    simp only [Restated.activeRoundW, Restated.attestersAt, Schedule.awakeThroughout, Finset.mem_inf,
      Finset.mem_Icc] at hw ⊢
    try rw [facts.gr.early_g2_eq S (q' + 1)] at hw
    rw [facts.gr.early_g2_eq S (q' + 1)]
    intro t ht
    exact hw t ⟨by linarith [ht.1], ht.2⟩
  -- the committee majority at a cutoff before slot `o_q + 1`
  obtain ⟨t', ht'E, ht's, ht'len, hcs'⟩ := Restated.exists_cone_cutoff facts S Sched tE hmono hcom tGAT gap
    hgst hlen hphase hcs (r := Restated.switchRound M S tE + 1) (Nat.le_succ _)
  have hanchor : t' ≤ slotStart S.E.Δ ((M.opening_slot S.hc (q' + 1)) + 1) :=
    le_trans ht's (slotStart_mono S (le_trans hsl (Nat.le_succ _)))
  have hslo : tGAT ≤ slotStart S.E.Δ ((M.opening_slot S.hc (q' + 1))) := by
    have h1 := Restated.tGAT_le_switchOpening facts S tGAT tE gap hgst hlen
    have h2 := Restated.switchOpening_le_opening facts S (tE := tE) (r := Restated.switchRound M S tE) le_rfl
    rw [(pHP% opening_eq_slotStart_hp) facts] at h2
    have h6 := slotStart_mono S (le_trans (Nat.le_add_right _ 2) hs0)
    linarith
  have hawake' : ∀ t : Int, tGAT ≤ t → t ≤ t' → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t :=
    fun t h0 h1 => hphase t h0 (le_trans h1 ht'E)
  have hthird' : ∀ t : Int, t ≤ t' →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight :=
    fun t h1 => hthird t (le_trans h1 ht'E)
  -- the one path of `u`'s round-`(q' + 1)` action the attestation `a` comes from: the node state
  -- `nd` of the action read, built from an outcome `c` of the cache update and an outcome `st`
  -- of the confirmation duty
  obtain ⟨nd, hnd, ns, rec, hatt⟩ := ha
  obtain ⟨c, hc0, st, hst0, hndeq⟩ := id hnd
  have hndst : nd.st = M.store_with_cache st c := by rw [hndeq]; exact facts.nd.mkNode_st _ _ _
  have hndc : nd.cache = c := by rw [hndeq]; exact facts.nd.mkNode_cache _ _ _
  have hc : M.onPhaseTick S.E S.hc (M.toHealing (x[n][u].st).st.core)
      (M.confirmation_time S.E (M.opening_slot S.hc (q' + 1))) (x[n][u].st).cache ⇢ c := by
    rw [hta]; exact hc0
  have hst : M.duties_update_confirmation_with (M.gradeContract c) S.E S.hc
      (M.ns_setClock S.E (x[n][u].st).st (M.confirmation_time S.E (M.opening_slot S.hc (q' + 1))))
      (M.opening_slot S.hc (q' + 1)) ⇢ st := by
    rw [hta, ← Restated.slotOf_a_sub_one facts S (q' + 1)]; exact hst0
  obtain ⟨D, hD⟩ := facts.dt.update_confirmation_with_nonempty (M.gradeContract c) S.E S.hc
    (Restated.confStoreAt M S (x[n][u].st) (M.opening_slot S.hc (q' + 1))) (M.opening_slot S.hc (q' + 1))
  have hDcore : st.core = D := facts.dt.named_update_confirmation_with_core _ _ _ _ _ st hst D hD
  -- one outcome `A` of the walk's start under `c`'s grade contract has the heads at `o_q`
  obtain ⟨A, hAo'⟩ := facts.fc.get_sg_root_with_nonempty (M.gradeContract c) S.E S.hc
    (M.toHealing (Restated.confStoreAt M S (x[n][u].st) (M.opening_slot S.hc (q' + 1))))
    (M.round_of S.hc (Restated.confStoreAt M S (x[n][u].st) (M.opening_slot S.hc (q' + 1))).s)
  have hAo : Restated.Vocabulary.Protocol.confAnchorWith M (M.gradeContract c) S.E S.hc
      (Restated.confStoreAt M S (x[n][u].st) (M.opening_slot S.hc (q' + 1))) ⇢ A := hAo'
  have hA : Restated.HeadsBelow M S Sched x A ((M.opening_slot S.hc (q' + 1))) :=
    Restated.confAnchor_headsBelow_atSlot facts S Sched x tE hexec hmono htd hcatch tGAT gap hgst hlen hsync
      hthird hphase hrsW hmult hcv hcs hcom hrec hprev hclear hB' hnW hAW hJswitch hTW₀ hJ₀
      hsl hm (Restated.honRound_grade2Window_confirmation facts S Sched (q' + 1) hu) hvh' c hc A hAo
  -- the anchor `T` of the round, the delivery condition, the block `Z`
  obtain ⟨r, nT, T, hr, hTW, hJ, -, hs1, hT⟩ := Restated.exists_joint_anchor_headsBelow_atSlot facts S Sched x
    tE hexec hmono htd hcatch tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom
    hrec hprev hclear hB' hnW hAW hJswitch hTW₀ hJ₀ (le_trans (Nat.le_add_right _ 2) hsl)
  have hinv := (pHP% joint_toTop_hp) hJ
  have hcross : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepFinalizedCrossingUnderAnchor M S Sched x r n'' T :=
    fun n'' h => Restated.stepFinalizedCrossingUnderAnchor_of_afterSwitch facts S Sched x hr hnW
      hJ.toAfterPhaseInvariantOverActiveSetsSince
      (Restated.justified_preceq_anchor_ofJoint facts S Sched x tE hexec hmono htd tGAT gap hgst hlen hsync
        hthird hphase hrsW hmult hcv hcom hrec hprev hclear hB' hnW hAW hr hTW hJ h)
  obtain ⟨n', hn'⟩ := Restated.tick_field_at_succ facts S Sched x htd r
  have hfin := Restated.fin_old_anchor_before_succ_tick_of_hypotheses facts S Sched x tE
    hexec hmono tGAT gap hgst hlen hthird hphase hrsW hr hinv hcross hn'
  have hunderT := Restated.deliveredDescendantUnderFinalized_anchor facts S Sched x hn' hfin tGAT
  have hunderTS := Restated.finalizedPreceqAtSteps_anchor facts S Sched x hn' hfin tGAT
  have hcut : M.support_cutoff S.E ((M.opening_slot S.hc (q' + 1))) ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) - 1 := by
    have e1 := (pIT% support_cutoff_eq_of_pos) facts S.E hspos
    have e2 := Restated.confirmation_time_opening_slot facts S (r + 1)
    have e3 := facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E ((M.opening_slot S.hc (r + 1)))
    have hmo := slotStart_mono S hs1
    linarith
  have hunderT' : Restated.DeliveredDescendantUnderFinalizedInPhase M S x tGAT
      (M.support_cutoff S.E ((M.opening_slot S.hc (q' + 1)))) T.erase := by
    intro d v v' B hlbl hvh h0 h1 hTB
    exact hunderT d v v' B hlbl hvh h0 (le_trans h1 hcut) hTB
  have hunderTS' : Restated.FinalizedPreceqAtStepsInPhase M S x tGAT
      (M.support_cutoff S.E ((M.opening_slot S.hc (q' + 1)))) T.erase :=
    fun d v hvh h0 h1 => hunderTS d v hvh h0 (le_trans h1 hcut)
  have hcomp : ∀ P Q : Block V, Restated.HeadsBelow M S Sched x P ((M.opening_slot S.hc (q' + 1))) →
      Restated.HeadsBelow M S Sched x Q ((M.opening_slot S.hc (q' + 1))) → Block.compatible P Q = true :=
    fun P Q hP hQ => Restated.compatible_of_headsBelow_after facts S Sched x htd hcs' hspos hanchor hP hQ
  have hAX := hcomp A X hA hX
  obtain ⟨Y, hAY, hXY, hY⟩ := Restated.exists_join_headsBelow facts S Sched x hAX hA hX
  obtain ⟨Z, hYZ, hTZ, hZ⟩ := Restated.exists_join_headsBelow facts S Sched x (hcomp Y T.erase hY hT) hY hT
  have hunderZ := Restated.deliveredDescendant_mono facts S Sched x hunderT' hTZ
  have hunderZS := Restated.finalizedPreceqAtSteps_mono facts S Sched x hunderTS' hTZ
  have hpath := Restated.confAnchorChainInTree_atSlot facts S Sched x tE hexec hmono htd hcatch tGAT gap hgst
    hlen hsync hthird hphase hrsW hmult hcv hcs hcom hrec hprev hclear hB' hnW hAW hJswitch
    hTW₀ hJ₀ hsl hm hvaw hvh' hZ c hc A hAo
  -- one path of the walk passes `Z`, and the action read's `live_confirmed` is its result
  obtain ⟨tm, htm⟩ := facts.sto.tau_nonempty (Restated.confStoreAt M S (x[n][u].st) (M.opening_slot S.hc (q' + 1)))
  have he : Restated.Vocabulary.Protocol.confVotes M S.E (Restated.confStoreAt M S (x[n][u].st) (M.opening_slot S.hc (q' + 1))) (M.opening_slot S.hc (q' + 1)) ⇢
      ((_root_.DecoupledConsensusModel.beforeCutoff tm (M.support_cutoff S.E (M.opening_slot S.hc (q' + 1)))
          ((Restated.confStoreAt M S (x[n][u].st) (M.opening_slot S.hc (q' + 1))).pool (M.opening_slot S.hc (q' + 1)))).filter
        (fun w => M.no_second_vote_in
          (_root_.DecoupledConsensusModel.beforeCutoff (Restated.confStoreAt M S (x[n][u].st) (M.opening_slot S.hc (q' + 1))).timestamp_vote
            (M.confirmation_time S.E (M.opening_slot S.hc (q' + 1))) ((Restated.confStoreAt M S (x[n][u].st) (M.opening_slot S.hc (q' + 1))).pool (M.opening_slot S.hc (q' + 1)))) w = true)) :=
    (pCW% returns_map_intro_cw) _ _ _ ((pCW% returns_map_intro_cw) _ _ _ htm)
  have hscore : ∀ B : Block V, ∃ gsc, M.goldfish_score S.E (Restated.confStoreAt M S (x[n][u].st) (M.opening_slot S.hc (q' + 1))).T
      ((_root_.DecoupledConsensusModel.beforeCutoff tm (M.support_cutoff S.E (M.opening_slot S.hc (q' + 1)))
          ((Restated.confStoreAt M S (x[n][u].st) (M.opening_slot S.hc (q' + 1))).pool (M.opening_slot S.hc (q' + 1)))).filter
        (fun w => M.no_second_vote_in
          (_root_.DecoupledConsensusModel.beforeCutoff (Restated.confStoreAt M S (x[n][u].st) (M.opening_slot S.hc (q' + 1))).timestamp_vote
            (M.confirmation_time S.E (M.opening_slot S.hc (q' + 1))) ((Restated.confStoreAt M S (x[n][u].st) (M.opening_slot S.hc (q' + 1))).pool (M.opening_slot S.hc (q' + 1)))) w = true))
      ((_root_.DecoupledConsensusModel.beforeCutoff tm (M.support_cutoff S.E (M.opening_slot S.hc (q' + 1)))
          ((Restated.confStoreAt M S (x[n][u].st) (M.opening_slot S.hc (q' + 1))).pool (M.opening_slot S.hc (q' + 1)))).filter
        (fun w => M.no_second_vote_in
          (_root_.DecoupledConsensusModel.beforeCutoff (Restated.confStoreAt M S (x[n][u].st) (M.opening_slot S.hc (q' + 1))).timestamp_vote
            (M.confirmation_time S.E (M.opening_slot S.hc (q' + 1))) ((Restated.confStoreAt M S (x[n][u].st) (M.opening_slot S.hc (q' + 1))).pool (M.opening_slot S.hc (q' + 1)))) w = true))
      (M.opening_slot S.hc (q' + 1)) B ⇢ gsc :=
    fun B => facts.fc.goldfish_score_nonempty _ _ _ _ _ _
  choose sc hsc using hscore
  obtain ⟨W, hWg⟩ := facts.fc.ghost_nonempty A (Restated.Vocabulary.Protocol.confTree M (Restated.confStoreAt M S (x[n][u].st) (M.opening_slot S.hc (q' + 1)))) sc
    (fun B => decide (Restated.Vocabulary.Protocol.confCount M S.E (Restated.confStoreAt M S (x[n][u].st) (M.opening_slot S.hc (q' + 1))) (M.opening_slot S.hc (q' + 1)) < 2 * sc B))
  obtain ⟨hZW, hel⟩ := Restated.walk_eligible_of_headsBelow_at_confirmation_tick
    (hr1 := Restated.one_le_round_of_of_opening_slot_le facts S (r := q' + 1) (Nat.le_add_left 1 _) le_rfl) facts S Sched x hexec hsync
    hmult htd hmono hgst hcv hawake' hthird' hcs' ht'len hunderZ
    hunderZS hspos hslo hanchor le_rfl hZ hm
    hvaw hvh' (M.gradeContract c) A hAo (preceq_trans_Preceq hAY hYZ) hpath
    (by intro mv hmv q hq; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono hmv (facts.sch.vote_time_emod_delta S _) (Finset.mem_sdiff.2 ⟨Restated.awake_of_mem_HonSlot facts S Sched _ hq, fun h => ((Restated.mem_HonSlot facts).mp hq).2.2 (hmono _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E (M.opening_slot S.hc (q' + 1))) h)⟩))
    (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›) _ he sc hsc W hWg
  have hlive := (pW% live_confirmed_after_confirmation_tick_outcome_csw) facts S Sched x hm haw
    hneConf hrunC c hc D hD
  have hDW := facts.hd.update_confirmation_with_live_confirmed_of_eligible (M.gradeContract c) S.E S.hc
    (Restated.confStoreAt M S (x[n][u].st) (M.opening_slot S.hc (q' + 1))) (M.opening_slot S.hc (q' + 1)) tm htm A hAo sc hsc W hWg hel D hD
  have hlc := Restated.actionHealingStore_live_confirmed facts S Sched x (s := (M.opening_slot S.hc (q' + 1)))
    (r := q' + 1) hta (Restated.slotOf_a_sub_one facts S (q' + 1)) hm haw hneConf hrunC
    (M.toHealing nd.st.core) ⟨nd, hnd, rfl⟩
  have hZlc : Block.Preceq Z (M.toHealing nd.st.core).live_confirmed := by
    rw [hlc, hlive, hDW]; exact hZW
  -- the action read's test passes at every block with the heads at `o_q`
  obtain ⟨n1, T1, hJ1, -, hTW1⟩ := Restated.anchor_at_later_round facts S Sched x tE hexec hmono htd hcatch
    tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hrec hprev hclear hB'
    hnW hAW hJswitch le_rfl hTW₀ hJ₀ hq'
  obtain ⟨n2, T2, hJ2, -, -⟩ := Restated.anchor_at_later_round facts S Sched x tE hexec hmono htd hcatch
    tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hrec hprev hclear hB'
    hnW hAW hJswitch le_rfl hTW₀ hJ₀ (Nat.le_succ_of_le hq')
  have hawT : u ∈ Sched.awakeThroughout (M.early S.E S.hc (q' + 1) .g2 - S.E.Δ)
      (M.domain S.E S.hc (q' + 1) .g0) :=
    awakeThroughout_mono Sched (Finset.mem_sdiff.1 hu).1 le_rfl (facts.gr.domain_le_action S (q' + 1) .g0)
  have ht₀u : M.early S.E S.hc (q' + 1) .g2 - S.E.Δ ≤ M.late S.E S.hc (q' + 1) .g0 - 1 - 2 * S.E.Δ := by
    have he := facts.gr.early_g2_eq S (q' + 1)
    have hl9 := Restated.action_sub_nine_delta_le_late facts S (q' + 1) .g0
    have hd1 : (1 : Int) ≤ S.E.Δ := S.E.Δ_pos
    rw [he]; linarith
  have hrecvu : Restated.ReceivesRoundAttestationsBefore M S Sched x q' u (M.early S.E S.hc (q' + 1) .g0) :=
    ((Restated.nextRoundReceipts_of_catchUp facts S Sched x hsync hcatch
      (Restated.gst_le_action_of_switchRound_le facts S tGAT tE gap hgst hlen hq')).1 u hu).mono
      (Restated.early_g2_le_early facts S (q' + 1) .g0)
  have hvS : u ∉ Sched.adv (M.domain S.E S.hc (q' + 1) .g0) :=
    hvhT _ (facts.gr.domain_le_action S (q' + 1) .g0)
  have hprep : Restated.FramePhaseProvenance M S x u c :=
    Restated.framePhaseProvenance_onPhaseTick facts S hm
      (Restated.framePhaseProvenance_sts facts S Sched x u n) c hc
  obtain ⟨g, hg0⟩ := facts.gr.read_nonempty (M.gradeContract nd.cache) S.E S.hc (M.toHealing nd.st.core) (q' + 1)
  have hg : M.frameGradeRead nd.cache S.E S.hc (M.toHealing nd.st.core) (q' + 1) ⇢ g :=
    (facts.nd.gradeContract_read _ _ _ _ _ g).1 hg0
  have hclr : ∀ B : Block V, Restated.HeadsBelow M S Sched x B ((M.opening_slot S.hc (q' + 1))) →
      g.clear B = true := by
    intro B hB
    rw [facts.gr.frameGradeRead_clear nd.cache S.E S.hc _ (q' + 1) g hg]
    by_cases hgz : ∃ root : Block V,
        (M.readFrame nd.cache (M.toHealing nd.st.core) (q' + 1)).g0 = some (some root)
    · obtain ⟨root, hroot⟩ := hgz
      rw [facts.gr.clear_of_g0 hroot]
      obtain ⟨root₀, h₀, hpre⟩ := facts.gr.readFrame_phase_provenance nd.cache
        (M.toHealing nd.st.core) (q' + 1) (p := .g0) ((facts.gr.phaseResult_g0 _).trans hroot)
      rw [hndc] at h₀
      obtain ⟨m, G, hmG, hG, hpreG⟩ := hprep (q' + 1) .g0 root₀ h₀
      obtain ⟨b, hb⟩ := facts.gr.gradeBool_nonempty S.E (M.gradeView (M.toHealing (x[m][u].st).st.core))
        (x[m][u].st).st.core.F S.hc.η_SG (q' + 1) (M.early S.E S.hc (q' + 1) .g0)
        (M.late S.E S.hc (q' + 1) .g0) G
      obtain rfl := hG b hb
      have hGheads := Restated.graded_ancestorOfHonestHeadsFrom_at_awakeReader_recv facts S Sched x tE hexec hmono htd
        hcatch tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hrec hprev
        hclear hB' hnW hAW hJswitch hq' hTW1 hJ1 hJ2 _ ht₀u hawT hrecvu hvS hmG hb
      exact compatible_of_compatible_of_preceq (hcomp B G hB (hGheads _ le_rfl))
        (preceq_trans_Preceq hpre hpreG)
    · exact facts.gr.clear_of_g0_ne (fun root hroot => hgz ⟨root, hroot⟩) B
  -- the clear walk answers a descendant of the deeper of `A` and `X`
  obtain ⟨Bc, hABc, hXBc, hBcY, hBc⟩ : ∃ Bc : Block V, Block.Preceq A Bc ∧ Block.Preceq X Bc ∧
      Block.Preceq Bc Y ∧ Restated.HeadsBelow M S Sched x Bc ((M.opening_slot S.hc (q' + 1))) := by
    rcases compatible_cases hAX with h | h
    · exact ⟨X, h, preceq_eq_true_iff_Preceq.mp (Block.preceq_self X), hXY, hX⟩
    · exact ⟨A, preceq_eq_true_iff_Preceq.mp (Block.preceq_self A), h, hAY, hA⟩
  -- the anchor of the action read is `A`: the read's store is the confirmation update's outcome
  -- `D`, which keeps the finalized block, the filtered tree and the fork-choice root of the
  -- clock-stamped store
  have hR := Restated.round_of_confStoreAt_opening_slot facts S (x[n][u].st) (q' + 1)
  have hA1 : M.anchor S.E S.hc
      (M.toHealing (Restated.confStoreAt M S (x[n][u].st) (M.opening_slot S.hc (q' + 1)))) (q' + 1)
      (M.readFrame c (M.toHealing (Restated.confStoreAt M S (x[n][u].st) (M.opening_slot S.hc (q' + 1))))
        (q' + 1)).g1 ⇢ A := by
    have h := hAo'
    rw [hR] at h
    exact (facts.nd.gradeContract_sgRoot_eq_frameAnchor c S.E S.hc _ (q' + 1) A).1 h
  have hAnd : M.anchor S.E S.hc (M.toHealing nd.st.core) (q' + 1)
      (M.readFrame nd.cache (M.toHealing nd.st.core) (q' + 1)).g1 ⇢ A := by
    rw [hndc, hndst, facts.nd.store_with_cache_readFrame, hDcore, facts.gr.readFrame_g1_eq_of_F c (q' + 1)
      (facts.hd.update_confirmation_with_toHealing_F _ _ _ _ _ D hD)]
    exact (facts.gr.anchor_eq_of_filtered_fg_root S.E S.hc (q' + 1) _
      (by rw [facts.nd.store_with_cache_get_filtered_block_tree, hDcore]
          exact facts.dt.update_confirmation_with_toHealing_filtered _ _ _ _ _ D hD)
      (by rw [facts.nd.store_with_cache_get_fg_root, hDcore]
          exact facts.dt.update_confirmation_with_toHealing_fg_root _ _ _ _ _ D hD) A).2 hA1
  have hanc : g.anchor = A := facts.gr.frameGradeRead_anchor nd.cache S.E S.hc _ (q' + 1) g hg A hAnd
  obtain ⟨Dd, hDd, hBcD⟩ := facts.gr.preceq_deepest_clear
    (floor := g.anchor)
    (C := (M.toHealing nd.st.core).live_confirmed)
    (test := g.clear)
    (preceq_trans_Preceq hBcY (preceq_trans_Preceq hYZ hZlc)) (by rw [hanc]; exact hABc)
    (hclr Bc hBc)
  have hsg : M.currentSGVote (M.toHealing nd.st.core) g = Dd :=
    facts.gr.Sts_currentSGVote_of_deepest_clear hDd
  -- the body `C` is `Dd`
  have hroot := Restated.attest_confirmed_eq_sgVote facts S (x[n][u].st) u (q' + 1) nd hnd
    (ns, rec, a) hatt g hg
  rw [hsg] at hroot
  have hroot' : a.confirmed = some Dd.root := hroot
  rw [hroot'] at hconf
  obtain ⟨E, hElog, hEe⟩ := Restated.exists_inLog_erase_actionSGVote facts S Sched x hvhn (q' + 1)
    nd hnd g hg
  rw [hsg] at hEe
  have hCE : C.erase = E.erase := by
    refine Restated.erase_eq_of_root_eq_inLog facts S Sched x hexec (Restated.blockInLog_of_mem_bodies facts S Sched hvh1 hC)
      hElog ?_
    rw [← Proofs.NamedWire.erase_root E, hEe]
    exact (Option.some_inj.mp hconf).symm
  rw [hCE, hEe]
  exact preceq_trans_Preceq hXBc hBcD

end

end DecoupledConsensusModel.Sts.Restated
