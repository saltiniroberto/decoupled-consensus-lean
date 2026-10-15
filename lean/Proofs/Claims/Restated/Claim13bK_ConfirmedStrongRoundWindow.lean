import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bK_ConfirmedRecord
import Proofs.Claims.Restated.Claim13bK_ConfirmedSettle
import Proofs.Claims.Restated.Claim13bK_HeadsPersist
import Proofs.Claims.Restated.Claim13bStepKitConfirm
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.ProcessIdempotent
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActive
import Model.Conditions.Claim13bInvariantActiveJoint
import Model.Conditions.Claim13bInvariantActiveSinceW
import Model.Conditions.Claim13bK_ConfirmedSettle
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
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Vocabulary.Protocol.Grades
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Protocol_Grades_Main
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring

/-!
# Confirmation ticks in the window of a strong round

What a confirmation tick writes to a validator's stable and confirmed records, and the conditions
under which both records stay ancestors of every honest head from a later slot on, stated over a
model `M : Record.Model V`.
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

/-! ## Helpers -/

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- The confirmation time of slot `s` is `4 * Δ * s + 6 * Δ`. -/
private theorem confirmation_time_closed_csw (facts : Record.Facts M) (E : Env V) (s : Slot) :
    M.confirmation_time E s = 4 * E.Δ * (s : Int) + 6 * E.Δ := by
  rw [← facts.sch.slotStart_add_six_delta_eq_confirmation_time E s, slotStart_closed]

/-- For every outcome `D` of the confirmation update of `st` at slot `s` under `contract`, there is
    a block `cand` such that `D`'s `latest_confirmed` is `floor_on_stable` of `D`'s `latest_stable`,
    `cand` and `st`'s `latest_confirmed`, and `cand` is `st`'s `latest_confirmed`, or
    `advance_confirmed` of it with `D`'s `live_confirmed`, or `advance_confirmed` of it with a block
    `G` that the contract's SG candidate selection at `st` and `s` can return as `some G`. -/
private theorem update_confirmation_with_latest_confirmed_candidate_csw (facts : Record.Facts M)
    (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig) (st : M.S) (s : Slot)
    (D : M.S) (hD : M.update_confirmation_with contract E hc st s ⇢ D) :
    ∃ cand : Block V,
      D.latest_confirmed = M.floor_on_stable D.latest_stable cand st.latest_confirmed ∧
      (cand = st.latest_confirmed ∨
        cand = M.advance_confirmed st.latest_confirmed D.live_confirmed ∨
        ∃ G : Block V, contract.confirmationSG E hc st.toHealing s ⇢ some G ∧
          cand = M.advance_confirmed st.latest_confirmed G) := by
  classical
  obtain ⟨tm, htm⟩ := facts.sto.tau_nonempty st
  obtain ⟨R, hR⟩ := facts.fc.get_sg_root_with_nonempty contract E hc st.toHealing
    (M.round_of hc st.s)
  obtain ⟨score, hscore⟩ : ∃ score : Block V → ℕ, ∀ B, M.goldfish_score E st.T
      ((beforeCutoff tm (M.support_cutoff E s) (st.pool s)).filter (fun u =>
        M.no_second_vote_in (beforeCutoff st.timestamp_vote (M.confirmation_time E s)
          (st.pool s)) u = true))
      ((beforeCutoff tm (M.support_cutoff E s) (st.pool s)).filter (fun u =>
        M.no_second_vote_in (beforeCutoff st.timestamp_vote (M.confirmation_time E s)
          (st.pool s)) u = true))
      s B ⇢ score B :=
    ⟨fun B => (facts.fc.goldfish_score_nonempty _ _ _ _ _ B).choose,
      fun B => (facts.fc.goldfish_score_nonempty _ _ _ _ _ B).choose_spec⟩
  obtain ⟨W, hW⟩ := facts.fc.ghost_nonempty R (M.get_filtered_block_tree st.toHealing.toFG) score
    (fun B => decide (M.voters_count E (beforeCutoff st.timestamp_vote (M.confirmation_time E s)
      (st.pool s)) s < 2 * score B))
  obtain ⟨cand, hfl, hcases⟩ := facts.hd.update_confirmation_with_latest_confirmed_cases
    contract E hc st s tm htm R hR score hscore W hW D hD
  refine ⟨cand, hfl, ?_⟩
  rcases hcases with h | ⟨hel, h⟩ | h
  · exact Or.inl h
  · right; left
    rw [facts.hd.update_confirmation_with_live_confirmed_of_eligible contract E hc st s tm htm R
      hR score hscore W hW hel D hD]
    exact h
  · exact Or.inr (Or.inr h)

/-- If the SG candidate selection of the grade contract of `c` at `st` and `s` can return `some G`,
    then every outcome of that contract's stable root at `st` and the round of `st`'s slot is
    `some G`. -/
private theorem confirmationSG_stableRoot_csw (facts : Record.Facts M) (c : M.Cache) (E : Env V)
    (hc : Protocol.HealConfig) (st : M.S) (s : Slot) {G : Block V}
    (hsel : (M.gradeContract c).confirmationSG E hc st.toHealing s ⇢ some G)
    (o : Option (Block V))
    (ho : (M.gradeContract c).stableRoot E hc st.toHealing (M.round_of hc st.s) ⇢ o) :
    o = some G :=
  facts.gr.frameSGCandidate_stableRoot c E hc st s (some G)
    ((facts.nd.gradeContract_confirmationSG c E hc st.toHealing s (some G)).1 hsel) rfl o
    ((facts.nd.gradeContract_stableRoot c E hc st.toHealing (M.round_of hc st.s) o).1 ho)

/-- If step `n` is the tick at slot `s`'s confirmation time, `w` is awake and not held there, its
    tick has an outcome and passes the grade-2 awake test of slot `s + 1`'s round, then for every
    outcome `c` of `w`'s cache update and every outcome `D` of the confirmation update at `s` under
    `c`'s grade contract, the `live_confirmed` `w` holds after the step is `D`'s. -/
private theorem live_confirmed_after_confirmation_tick_outcome_csw (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    {n : Nat} {s : Slot} (hn : Restated.tickStepAt M x n (M.confirmation_time S.E s)) {w : V}
    (haw : w ∈ Sched.awake (M.confirmation_time S.E s) \ Sched.adv (M.confirmation_time S.E s))
    (hneTick : ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) w (Record.wakeStage M Sched (M.confirmation_time S.E s) x[n] w) (M.confirmation_time S.E s) ⇢ out)
    -- `w`'s tick at step `n` passes the grade-2 awake test of slot `s + 1`'s round.
    (hrun : M.awake_for_grade2 (Setup.alwaysAwake S) w
      (Record.wakeStage M Sched (M.confirmation_time S.E s) x[n] w) (M.round_of S.hc (s + 1)))
    (c : M.Cache) (hc : M.onPhaseTick S.E S.hc (M.toHealing (x[n][w].st).st.core)
        (M.confirmation_time S.E s) (x[n][w].st).cache ⇢ c)
    (D : M.S) (hD : M.update_confirmation_with (M.gradeContract c) S.E S.hc
        (M.ns_setClock S.E (x[n][w].st).st (M.confirmation_time S.E s)).core s ⇢ D) :
    (x[n + 1][w].st).st.core.live_confirmed = D.live_confirmed := by
  have _hr_0 : M.reachedNode (x[n][w].st) := Record.reachedNode_sts facts S Sched x n w
  obtain ⟨t', hlbl, ht'⟩ := id hn
  have hct := facts.sch.confirmation_time_eq_support_cutoff_succ S.E s
  have hdvd : (t' : Int) % S.E.Δ = 0 := by
    rw [ht', hct]
    exact facts.sch.support_cutoff_emod_delta S (s + 1)
  have haw' : w ∈ Sched.awake (t' : Int) \ Sched.adv (t' : Int) := by rw [ht']; exact haw
  rcases Restated.st_succ_of_tick_awake facts S Sched x w hlbl haw' with
    ⟨out₁, hout, hst⟩ | ⟨hno, -⟩
  · rw [ht', hct] at hout
    rw [hct] at hc hD
    obtain ⟨DN, hDN⟩ := facts.dt.duties_update_confirmation_with_nonempty (M.gradeContract c) S.E
      S.hc (M.ns_setClock S.E (x[n][w].st).st (M.support_cutoff S.E (s + 1))) (s + 1 - 1)
    have hD' : M.update_confirmation_with (M.gradeContract c) S.E S.hc
        (M.ns_setClock S.E (x[n][w].st).st (M.support_cutoff S.E (s + 1))).core (s + 1 - 1) ⇢ D := by
      rw [Nat.add_sub_cancel]; exact hD
    have _hr_s1 := Record.reachedNode_wakeStage facts S Sched x (n) w (M.support_cutoff S.E (s + 1))
    rw [hst, facts.nd.on_tick_emit_confirmation_of_outcomes (Setup.alwaysAwake S) w _
        (s + 1) (Nat.succ_pos s) out₁ hout c
        (by rw [Record.wakeStage_st facts, Record.wakeStage_cache facts]; exact hc) DN
        (by rw [Record.wakeStage_st facts]; exact hDN)
        (by rw [Restated.alwaysAwake_alwaysAwake, ← hct]; exact hrun),
      facts.dt.named_update_confirmation_with_core _ _ _ _ _ DN hDN D hD']
  · obtain ⟨o, ho⟩ := hneTick
    rw [← ht'] at ho
    exact absurd ho (hno o)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- If slot `s`'s confirmation time is before slot `s'`'s, then `s < s'`. -/
theorem slot_lt_of_confirmation_time_lt (facts : Record.Facts M) (S : Setup V) {s s' : Slot}
    (h : M.confirmation_time S.E s < M.confirmation_time S.E s') : s < s' := by
  have hd := S.E.Δ_pos
  rw [confirmation_time_closed_csw facts, confirmation_time_closed_csw facts] at h
  have h' : 4 * S.E.Δ * (s : Int) < 4 * S.E.Δ * (s' : Int) := by linarith
  have := lt_of_mul_lt_mul_left h' (by linarith)
  exact_mod_cast this

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- A validator's `latest_stable` and `latest_confirmed` after `k` steps are blocks of its tree
    after `k` steps. -/
theorem records_mem_tree_sts (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V) (k : Nat) :
    (x[k][v].st).st.core.latest_stable ∈ (x[k][v].st).st.core.T ∧
      (x[k][v].st).st.core.latest_confirmed ∈ (x[k][v].st).st.core.T := by
  have h := (Restated.nodeInvariant_sts facts S Sched x k v).1.2
  exact ⟨h.2.2, h.2.1⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- On the premises of `afterPhaseJointRound_of_premises`, with the joint invariant at a round `r₀`
    at or after the switch round, if slot `s` is at or after `o_{r₀} + 2`, `m` is the tick step at
    slot `s`'s confirmation time, and `v` is awake, honest and a member of `HonRound S Sched r'` for
    the round `r'` of `s + 1`, then every stable root outcome `o` at that tick is `some G` for a
    block `G` that is an ancestor of every honest head from slot `s + 3` on, `v`'s new
    `latest_stable` is `advance_confirmed` of the old one with `G`, and `v`'s new `latest_confirmed`
    is `floor_on_stable` of the new `latest_stable`, a candidate and the old `latest_confirmed`, the
    candidate being the old `latest_confirmed` or `advance_confirmed` of it with a block that is an
    ancestor of every honest head from slot `s + 3` on. -/
theorem records_after_confirmation_tick_values (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (hcatch : Restated.CatchUpOnWake M S x) (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (hsync : Restated.SynchronyFromWake M S x) (hthird : ∀ t : Int, t ≤ tE →
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
    {r₀ : Round} {n₀ : Nat} {T₀ : NamedBlock V}
    (hr₀ : Restated.switchRound M S tE ≤ r₀) (hTW₀ : Block.Preceq T_W.erase T₀.erase)
    (hJ₀ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x r₀ n₀ n_W T₀)
    {s : Slot} (hs0 : (M.opening_slot S.hc r₀) + 2 ≤ s)
    {m : Nat} (hm : Restated.tickStepAt M x m (M.confirmation_time S.E s)) {v : V}
    (hvaw : v ∈ Sched.awakeThroughout (slotStart S.E.Δ s - S.E.Δ)
      (M.confirmation_time S.E s))
    (hvh : HonestThroughTime Sched (M.confirmation_time S.E s) v)
    (hvR : v ∈ Restated.HonRound M S Sched ((M.round_of S.hc (s + 1))))
    -- `v`'s tick at step `m` passes the grade-2 awake test of slot `s + 1`'s round.
    (hrun : M.awake_for_grade2 (Setup.alwaysAwake S) v
      (Record.wakeStage M Sched (M.confirmation_time S.E s) x[m] v) (M.round_of S.hc (s + 1))) :
    ∀ c : M.Cache, M.onPhaseTick S.E S.hc (M.toHealing (x[m][v].st).st.core)
        (M.confirmation_time S.E s) (x[m][v].st).cache ⇢ c →
    ∀ o : Option (Block V), (M.gradeContract c).stableRoot S.E S.hc
          (M.toHealing (M.ns_setClock S.E (x[m][v].st).st
            (M.confirmation_time S.E s)).core)
          ((M.round_of S.hc) (M.ns_setClock S.E (x[m][v].st).st
            (M.confirmation_time S.E s)).core.s) ⇢ o →
    ∃ G : Block V, o = some G ∧
      Restated.AncestorOfHonestHeadsFrom M S Sched x G (s + 3) ∧
      (x[m + 1][v].st).st.core.latest_stable
        = M.advance_confirmed (x[m][v].st).st.core.latest_stable G ∧
      ∃ cand : Block V,
        (x[m + 1][v].st).st.core.latest_confirmed
          = M.floor_on_stable (x[m + 1][v].st).st.core.latest_stable cand
              (x[m][v].st).st.core.latest_confirmed ∧
        (cand = (x[m][v].st).st.core.latest_confirmed ∨
          ∃ Y : Block V, Restated.AncestorOfHonestHeadsFrom M S Sched x Y (s + 3) ∧
            cand = M.advance_confirmed (x[m][v].st).st.core.latest_confirmed Y) := by
  intro c hc o ho
  have hd := S.E.Δ_pos
  have haw : v ∈ Sched.awake (M.confirmation_time S.E s) \
      Sched.adv (M.confirmation_time S.E s) :=
    Finset.mem_sdiff.2 ⟨mem_awake_of_awakeThroughout Sched hvaw
      (by rw [slotStart_closed, confirmation_time_closed_csw facts]; linarith) le_rfl,
      hvh _ le_rfl⟩
  have hdvd : M.confirmation_time S.E s % S.E.Δ = 0 := by
    rw [facts.sch.confirmation_time_eq_support_cutoff_succ]
    exact facts.sch.support_cutoff_emod_delta S (s + 1)
  have hneTick := Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew
    hmono hm hdvd haw
  obtain ⟨G, rfl, hstab, hconf⟩ := Restated.records_after_confirmation_tick facts S Sched x
    hm haw hneTick hrun c hc o ho
  have hroot : Restated.AncestorOfHonestHeadsFrom M S Sched x G (s + 3) :=
    Restated.stableRoot_ancestorOfHonestHeadsFrom facts S Sched x tE hexec hmono htd hcatch
      tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hrec hprev hclear hB'
      hnW hAW hJswitch hr₀ hTW₀ hJ₀ hs0 hm hvR hvh hc ho
  refine ⟨G, rfl, hroot, hstab, ?_⟩
  -- one outcome of the confirmation update, and the candidate it writes
  obtain ⟨D, hD⟩ := facts.dt.update_confirmation_with_nonempty (M.gradeContract c) S.E S.hc
    (M.ns_setClock S.E (x[m][v].st).st (M.confirmation_time S.E s)).core s
  obtain ⟨cand, hfl, hcases⟩ := update_confirmation_with_latest_confirmed_candidate_csw facts
    (M.gradeContract c) S.E S.hc _ s D hD
  have hDstab : D.latest_stable = (x[m + 1][v].st).st.core.latest_stable := by
    rw [facts.hd.update_confirmation_with_latest_stable_of_root _ _ _ _ _ (some G) ho rfl D hD,
      facts.hd.setClock_core_latest_stable, hstab]
  rw [facts.hd.setClock_core_latest_confirmed] at hfl hcases
  refine ⟨cand, ?_, ?_⟩
  · rw [hconf D hD, hfl, hDstab]
  rcases hcases with hcand | hcand | ⟨G', hsel, hcand⟩
  · exact Or.inl hcand
  · -- the eligible walk result is the `live_confirmed` written at the tick
    right
    have hJ1 := Restated.live_confirmed_ancestorOfHonestHeadsFrom_ofJoint facts S Sched x tE
      hexec hmono htd hcatch tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom
      hrec hprev hclear hB' hnW hAW hJswitch hr₀ hTW₀ hJ₀ hs0 hm hvaw hvh hrun
    rw [live_confirmed_after_confirmation_tick_outcome_csw facts S Sched x hm haw
      hneTick hrun c hc D hD] at hJ1
    exact ⟨D.live_confirmed,
      Restated.ancestorOfHonestHeadsFrom_mono facts S Sched x (Nat.le_add_right _ 2) hJ1, hcand⟩
  · -- the select candidate is the stable root
    right
    have hGG : G = G' := Option.some.inj
      (confirmationSG_stableRoot_csw facts c S.E S.hc _ s hsel (some G) ho)
    subst hGG
    exact ⟨G, hroot, hcand⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- On the premises of `records_after_confirmation_tick_values`, for a property `Q` of blocks that
    every ancestor of every honest head from slot `s₀ ≥ s + 3` on has, if `v`'s `latest_stable` and
    `latest_confirmed` after `m` steps have `Q`, so do they after `m + 1` steps. -/
theorem records_after_confirmation_tick_keep (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (hcatch : Restated.CatchUpOnWake M S x) (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (hsync : Restated.SynchronyFromWake M S x) (hthird : ∀ t : Int, t ≤ tE →
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
    {r₀ : Round} {n₀ : Nat} {T₀ : NamedBlock V}
    (hr₀ : Restated.switchRound M S tE ≤ r₀) (hTW₀ : Block.Preceq T_W.erase T₀.erase)
    (hJ₀ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x r₀ n₀ n_W T₀)
    {s : Slot} (hs0 : (M.opening_slot S.hc r₀) + 2 ≤ s)
    {m : Nat} (hm : Restated.tickStepAt M x m (M.confirmation_time S.E s)) {v : V}
    (hvaw : v ∈ Sched.awakeThroughout (slotStart S.E.Δ s - S.E.Δ)
      (M.confirmation_time S.E s))
    (hvh : HonestThroughTime Sched (M.confirmation_time S.E s) v)
    (hvR : v ∈ Restated.HonRound M S Sched ((M.round_of S.hc (s + 1))))
    -- `v`'s tick at step `m` passes the grade-2 awake test of slot `s + 1`'s round.
    (hrun : M.awake_for_grade2 (Setup.alwaysAwake S) v
      (Record.wakeStage M Sched (M.confirmation_time S.E s) x[m] v) (M.round_of S.hc (s + 1)))
    {s₀ : Slot} (hss₀ : s + 3 ≤ s₀) (Q : Block V → Prop)
    (hQ : ∀ B : Block V, Restated.AncestorOfHonestHeadsFrom M S Sched x B s₀ → Q B)
    (hS : Q (x[m][v].st).st.core.latest_stable) (hC : Q (x[m][v].st).st.core.latest_confirmed) :
    Q (x[m + 1][v].st).st.core.latest_stable ∧ Q (x[m + 1][v].st).st.core.latest_confirmed := by
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc (M.toHealing (x[m][v].st).st.core)
    (M.confirmation_time S.E s) (x[m][v].st).cache
  obtain ⟨o, ho'⟩ := facts.gr.frameStableRoot_nonempty c S.E S.hc
    (M.toHealing (M.ns_setClock S.E (x[m][v].st).st (M.confirmation_time S.E s)).core)
    ((M.round_of S.hc) (M.ns_setClock S.E (x[m][v].st).st (M.confirmation_time S.E s)).core.s)
  have ho := (facts.nd.gradeContract_stableRoot _ _ _ _ _ o).2 ho'
  obtain ⟨G, -, hGP, hstab, cand, hconf, hcand⟩ := Restated.records_after_confirmation_tick_values facts S Sched
    x tE hexec hmono htd hcatch tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom
    hrec hprev hclear hB' hnW hAW hJswitch hr₀ hTW₀ hJ₀ hs0 hm hvaw hvh hvR hrun c hc o ho
  have hgood : ∀ B : Block V, Restated.AncestorOfHonestHeadsFrom M S Sched x B (s + 3) → Q B :=
    fun B hB => hQ B (Restated.ancestorOfHonestHeadsFrom_mono facts S Sched x hss₀ hB)
  have hnewS : Q (x[m + 1][v].st).st.core.latest_stable := by
    rw [hstab]
    rcases facts.hd.advance_confirmed_values (x[m][v].st).st.core.latest_stable G with ⟨-, he⟩ | he
    · rw [he]; exact hS
    · rw [he]; exact hgood G hGP
  have hQcand : Q cand := by
    rcases hcand with h | ⟨Y, hY, h⟩
    · rw [h]; exact hC
    · rw [h]
      rcases facts.hd.advance_confirmed_values (x[m][v].st).st.core.latest_confirmed Y with ⟨-, he⟩ | he
      · rw [he]; exact hC
      · rw [he]; exact hgood Y hY
  refine ⟨hnewS, ?_⟩
  rw [hconf]
  rcases facts.hd.floor_on_stable_values (x[m + 1][v].st).st.core.latest_stable cand
      (x[m][v].st).st.core.latest_confirmed with ⟨-, he⟩ | ⟨-, he⟩ | he
  · rw [he]; exact hQcand
  · rw [he]; exact hC
  · rw [he]; exact hnewS

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- On the premises of `records_after_confirmation_tick_values`, for a set `X` of blocks and a slot
    `s₀ ≥ s + 3`, call a block new when no member of `X` is a descendant of it or equal to it. If
    every stable root `v` can use at the tick is new, and each of `v`'s two records after `m` steps
    is an ancestor of every honest head from `s₀` on whenever it is new, then `v`'s `latest_stable`
    and `latest_confirmed` after `m + 1` steps are ancestors of every honest head from `s₀` on. -/
theorem records_after_confirmation_tick_of_new_root (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (hcatch : Restated.CatchUpOnWake M S x) (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (hsync : Restated.SynchronyFromWake M S x) (hthird : ∀ t : Int, t ≤ tE →
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
    {r₀ : Round} {n₀ : Nat} {T₀ : NamedBlock V}
    (hr₀ : Restated.switchRound M S tE ≤ r₀) (hTW₀ : Block.Preceq T_W.erase T₀.erase)
    (hJ₀ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x r₀ n₀ n_W T₀)
    {s : Slot} (hs0 : (M.opening_slot S.hc r₀) + 2 ≤ s)
    {m : Nat} (hm : Restated.tickStepAt M x m (M.confirmation_time S.E s)) {v : V}
    (hvaw : v ∈ Sched.awakeThroughout (slotStart S.E.Δ s - S.E.Δ)
      (M.confirmation_time S.E s))
    (hvh : HonestThroughTime Sched (M.confirmation_time S.E s) v)
    (hvR : v ∈ Restated.HonRound M S Sched ((M.round_of S.hc (s + 1))))
    -- `v`'s tick at step `m` passes the grade-2 awake test of slot `s + 1`'s round.
    (hrun : M.awake_for_grade2 (Setup.alwaysAwake S) v
      (Record.wakeStage M Sched (M.confirmation_time S.E s) x[m] v) (M.round_of S.hc (s + 1)))
    {s₀ : Slot} (hss₀ : s + 3 ≤ s₀) (X : Finset (Block V))
    (hnew : ∀ c : M.Cache, M.onPhaseTick S.E S.hc (M.toHealing (x[m][v].st).st.core)
        (M.confirmation_time S.E s) (x[m][v].st).cache ⇢ c →
      ∀ G : Block V, (M.gradeContract c).stableRoot S.E S.hc
          (M.toHealing (M.ns_setClock S.E (x[m][v].st).st
            (M.confirmation_time S.E s)).core)
          ((M.round_of S.hc) (M.ns_setClock S.E (x[m][v].st).st
            (M.confirmation_time S.E s)).core.s) ⇢ some G →
      ∀ Y ∈ X, ¬ Block.Preceq G Y)
    (hS : (∀ Y ∈ X, ¬ Block.Preceq (x[m][v].st).st.core.latest_stable Y) →
      Restated.AncestorOfHonestHeadsFrom M S Sched x (x[m][v].st).st.core.latest_stable s₀)
    (hC : (∀ Y ∈ X, ¬ Block.Preceq (x[m][v].st).st.core.latest_confirmed Y) →
      Restated.AncestorOfHonestHeadsFrom M S Sched x (x[m][v].st).st.core.latest_confirmed s₀) :
    Restated.AncestorOfHonestHeadsFrom M S Sched x (x[m + 1][v].st).st.core.latest_stable s₀ ∧
      Restated.AncestorOfHonestHeadsFrom M S Sched x (x[m + 1][v].st).st.core.latest_confirmed s₀ := by
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc (M.toHealing (x[m][v].st).st.core)
    (M.confirmation_time S.E s) (x[m][v].st).cache
  obtain ⟨o, ho'⟩ := facts.gr.frameStableRoot_nonempty c S.E S.hc
    (M.toHealing (M.ns_setClock S.E (x[m][v].st).st (M.confirmation_time S.E s)).core)
    ((M.round_of S.hc) (M.ns_setClock S.E (x[m][v].st).st (M.confirmation_time S.E s)).core.s)
  have ho := (facts.nd.gradeContract_stableRoot _ _ _ _ _ o).2 ho'
  obtain ⟨G, rfl, hGP, hstab, cand, hconf, hcand⟩ := Restated.records_after_confirmation_tick_values facts S Sched
    x tE hexec hmono htd hcatch tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom
    hrec hprev hclear hB' hnW hAW hJswitch hr₀ hTW₀ hJ₀ hs0 hm hvaw hvh hvR hrun c hc o ho
  -- a descendant of a new block is new
  have hup : ∀ A B : Block V, Block.Preceq A B → (∀ Y ∈ X, ¬ Block.Preceq A Y) →
      ∀ Y ∈ X, ¬ Block.Preceq B Y :=
    fun A B hAB hA Y hY hBY => hA Y hY (preceq_trans_Preceq hAB hBY)
  have hGnew := hnew c hc G ho
  have hGgood := Restated.ancestorOfHonestHeadsFrom_mono facts S Sched x hss₀ hGP
  -- the new stable record: new and `Good`
  have hnewS : (∀ Y ∈ X, ¬ Block.Preceq (x[m + 1][v].st).st.core.latest_stable Y) ∧
      Restated.AncestorOfHonestHeadsFrom M S Sched x (x[m + 1][v].st).st.core.latest_stable s₀ := by
    rw [hstab]
    rcases facts.hd.advance_confirmed_values (x[m][v].st).st.core.latest_stable G with ⟨hGo, he⟩ | he
    · rw [he]
      have hon := hup G _ hGo hGnew
      exact ⟨hon, hS hon⟩
    · rw [he]; exact ⟨hGnew, hGgood⟩
  refine ⟨hnewS.2, ?_⟩
  -- the candidate, when new, is `Good`
  have hcandP : (∀ Y ∈ X, ¬ Block.Preceq cand Y) →
      Restated.AncestorOfHonestHeadsFrom M S Sched x cand s₀ := by
    intro hcn
    rcases hcand with h | ⟨Y', hY', h⟩
    · rw [h] at hcn ⊢; exact hC hcn
    · rw [h] at hcn ⊢
      rcases facts.hd.advance_confirmed_values (x[m][v].st).st.core.latest_confirmed Y' with ⟨-, he⟩ | he
      · rw [he] at hcn ⊢; exact hC hcn
      · rw [he]; exact Restated.ancestorOfHonestHeadsFrom_mono facts S Sched x hss₀ hY'
  rw [hconf]
  rcases facts.hd.floor_on_stable_values (x[m + 1][v].st).st.core.latest_stable cand
      (x[m][v].st).st.core.latest_confirmed with ⟨hsc, he⟩ | ⟨hso, he⟩ | he
  · rw [he]; exact hcandP (hup _ _ hsc hnewS.1)
  · rw [he]; exact hC (hup _ _ hso hnewS.1)
  · rw [he]; exact hnewS.2

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- On the premises of `afterPhaseJointRound_of_premises`, with the joint invariant at a round `r₀`
    at or after the switch round, if the configuration after `k₀ ≤ n` steps is after the
    confirmation time of slot `o_{r₀} + 1`, `n` is the tick step at slot `s_f`'s confirmation time,
    `v` is awake, honest and an honest active attester around every confirmation time after step
    `k₀` and at or before `s_f`'s, `v` passes the grade-2 awake test at each of those ticks, and no
    stable root `v` can use at the tick at `n` is an ancestor of, or equal to, a block of `v`'s tree
    after `k₀` steps, then `v`'s `latest_stable` and `latest_confirmed` after `n + 1` steps are
    ancestors of every honest head from slot `s_f + 3` on. -/
theorem records_good_of_new_root_window (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (hcatch : Restated.CatchUpOnWake M S x) (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (hsync : Restated.SynchronyFromWake M S x) (hthird : ∀ t : Int, t ≤ tE →
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
    {r₀ : Round} {n₀ : Nat} {T₀ : NamedBlock V}
    (hr₀ : Restated.switchRound M S tE ≤ r₀) (hTW₀ : Block.Preceq T_W.erase T₀.erase)
    (hJ₀ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x r₀ n₀ n_W T₀)
    {v : V} {k₀ n : Nat} {s_f : Slot} (hk₀n : k₀ ≤ n)
    (hk₀ : M.confirmation_time S.E ((M.opening_slot S.hc r₀) + 1) ≤ (x[k₀].time : Int))
    (hn : Restated.tickStepAt M x n (M.confirmation_time S.E s_f))
    (hreader : ∀ s : Slot, (x[k₀].time : Int) < M.confirmation_time S.E s →
      M.confirmation_time S.E s ≤ M.confirmation_time S.E s_f →
      v ∈ Sched.awakeThroughout (slotStart S.E.Δ s - S.E.Δ) (M.confirmation_time S.E s) ∧
        HonestThroughTime Sched (M.confirmation_time S.E s) v ∧
        v ∈ Restated.HonRound M S Sched ((M.round_of S.hc (s + 1))))
    -- At every confirmation tick of the window, `v`'s node state passes the grade-2 awake test of
    -- the round of the next slot.
    (hrun : ∀ s : Slot, (x[k₀].time : Int) < M.confirmation_time S.E s →
      M.confirmation_time S.E s ≤ M.confirmation_time S.E s_f →
      ∀ m : Nat, Restated.tickStepAt M x m (M.confirmation_time S.E s) →
      M.awake_for_grade2 (Setup.alwaysAwake S) v
        (Record.wakeStage M Sched (M.confirmation_time S.E s) x[m] v) (M.round_of S.hc (s + 1)))
    (hnew : ∀ c : M.Cache, M.onPhaseTick S.E S.hc (M.toHealing (x[n][v].st).st.core)
        (M.confirmation_time S.E s_f) (x[n][v].st).cache ⇢ c →
      ∀ G : Block V, (M.gradeContract c).stableRoot S.E S.hc
          (M.toHealing (M.ns_setClock S.E (x[n][v].st).st
            (M.confirmation_time S.E s_f)).core)
          ((M.round_of S.hc) (M.ns_setClock S.E (x[n][v].st).st
            (M.confirmation_time S.E s_f)).core.s) ⇢ some G →
      ∀ Y ∈ (x[k₀][v].st).st.core.T, ¬ Block.Preceq G Y) :
    Restated.AncestorOfHonestHeadsFrom M S Sched x (x[n + 1][v].st).st.core.latest_stable (s_f + 3) ∧
      Restated.AncestorOfHonestHeadsFrom M S Sched x (x[n + 1][v].st).st.core.latest_confirmed (s_f + 3) := by
  have hd := S.E.Δ_pos
  set X : Finset (Block V) := (x[k₀][v].st).st.core.T with hX
  set Q : Block V → Prop := fun B =>
    (∀ Y ∈ X, ¬ Block.Preceq B Y) → Restated.AncestorOfHonestHeadsFrom M S Sched x B (s_f + 3) with hQdef
  obtain ⟨hn1, hn0⟩ := Restated.tickStepAt_time facts x hn
  -- a confirmation tick at a step in `[k₀, n)` lies in the window
  have hwin : ∀ m : Nat, k₀ ≤ m → m < n → ∀ s : Slot,
      Restated.tickStepAt M x m (M.confirmation_time S.E s) →
      (M.opening_slot S.hc r₀) + 2 ≤ s ∧ s + 3 ≤ s_f + 3 ∧
        (x[k₀].time : Int) < M.confirmation_time S.E s ∧
        M.confirmation_time S.E s ≤ M.confirmation_time S.E s_f := by
    intro m hkm hmn s hm
    obtain ⟨hm1, hm0⟩ := Restated.tickStepAt_time facts x hm
    have h1 := Restated.time_mono_int facts S Sched x hkm
    have h2 := Restated.time_mono_int facts S Sched x (Nat.succ_le_of_lt hmn)
    have hlo : M.confirmation_time S.E ((M.opening_slot S.hc r₀) + 1)
        < M.confirmation_time S.E s := by linarith
    have hhi : M.confirmation_time S.E s < M.confirmation_time S.E s_f := by
      linarith
    exact ⟨Restated.slot_lt_of_confirmation_time_lt facts S hlo,
      Nat.add_le_add_right (Nat.le_of_lt (Restated.slot_lt_of_confirmation_time_lt facts S hhi)) 3,
      by linarith, le_of_lt hhi⟩
  -- the invariant along the window
  have key : ∀ m : Nat, k₀ ≤ m → m ≤ n →
      Q (x[m][v].st).st.core.latest_stable ∧ Q (x[m][v].st).st.core.latest_confirmed := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base =>
      intro _
      obtain ⟨hmS, hmC⟩ := Restated.records_mem_tree_sts facts S Sched x v k₀
      exact ⟨fun h => absurd (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _)) (h _ hmS),
        fun h => absurd (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _)) (h _ hmC)⟩
    | succ m hkm ih =>
      intro hmn
      obtain ⟨ihS, ihC⟩ := ih (Nat.le_of_succ_le hmn)
      rcases Restated.records_succ_cases facts S Sched x v m with ⟨h1, h2⟩ | ⟨s, hm, -⟩
      · rw [h1, h2]; exact ⟨ihS, ihC⟩
      · obtain ⟨hs0, hss, hlo, hhi⟩ := hwin m hkm (Nat.lt_of_succ_le hmn) s hm
        obtain ⟨hvaw, hvh, hvR⟩ := hreader s hlo hhi
        exact Restated.records_after_confirmation_tick_keep facts S Sched x tE hexec hmono htd hcatch tGAT gap
          hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hrec hprev hclear hB' hnW
          hAW hJswitch hr₀ hTW₀ hJ₀ hs0 hm hvaw hvh hvR (hrun s hlo hhi m hm) hss Q
          (fun B hB _ => hB) ihS ihC
  obtain ⟨hQS, hQC⟩ := key n hk₀n le_rfl
  -- the last tick
  have hs0f : (M.opening_slot S.hc r₀) + 2 ≤ s_f := by
    have h1 := Restated.time_mono_int facts S Sched x hk₀n
    have hlo : M.confirmation_time S.E ((M.opening_slot S.hc r₀) + 1)
        < M.confirmation_time S.E s_f := by linarith
    exact Restated.slot_lt_of_confirmation_time_lt facts S hlo
  have hlof : (x[k₀].time : Int) < M.confirmation_time S.E s_f := by
    have h1 := Restated.time_mono_int facts S Sched x hk₀n
    linarith
  obtain ⟨hvaw, hvh, hvR⟩ := hreader s_f hlof le_rfl
  exact Restated.records_after_confirmation_tick_of_new_root facts S Sched x tE hexec hmono htd hcatch tGAT gap
    hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hrec hprev hclear hB' hnW hAW
    hJswitch hr₀ hTW₀ hJ₀ hs0f hn hvaw hvh hvR (hrun s_f hlof le_rfl n hn) le_rfl X hnew hQS hQC

end

end DecoupledConsensusModel.Sts.Restated
