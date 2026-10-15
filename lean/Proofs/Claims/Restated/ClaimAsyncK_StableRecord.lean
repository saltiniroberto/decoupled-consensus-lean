import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bK_ConfirmedRecord
import Proofs.Claims.Restated.Claim13bK_ConfirmedSettle
import Proofs.Claims.Restated.Claim13bK_StableRecord
import Proofs.Claims.Restated.Claim13bStepConeIter
import Proofs.Claims.Restated.ProcessedFlip
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.ClaimAsyncK_StableRecord

/-!
# Stable records across steps

Theorems over a model `M : Record.Model V` with facts `facts : Record.Facts M`: how a validator's
stable record changes at a confirmation tick and stays unchanged at other steps, which store fields
a confirmation or action tick leaves unchanged, and when a stable root lies on one chain with, or
descends from, `P`.
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
open Framework.StsMultisetLog
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- At the tick at slot `s`'s confirmation instant, for a validator `w` awake there and not held,
    whose tick there has an outcome and passes the grade-2 awake test of slot `s + 1`'s round: if
    for every outcome `c` of `w`'s cache update there, every block `G` the stable root of `c`'s
    grade contract can return as `some G` is a descendant of `P`, or is compatible with `P` while
    `w`'s stable record before the tick is a descendant of `P`, then `w`'s stable record after the
    tick is a descendant of `P`. -/
theorem stable_record_step_at_confirmation_tick (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {n : Nat} {s : Slot}
    (hn : Restated.tickStepAt M x n (M.confirmation_time S.E s)) {w : V}
    (haw : w ∈ Sched.awake (M.confirmation_time S.E s) \
      Sched.adv (M.confirmation_time S.E s))
    {P : Block V}
    (hroot : ∀ c : M.Cache, M.onPhaseTick S.E S.hc (M.toHealing (x[n][w].st).st.core)
        (M.confirmation_time S.E s) (x[n][w].st).cache ⇢ c →
      ∀ G : Block V,
      (M.gradeContract c).stableRoot S.E S.hc
          (M.toHealing (M.ns_setClock S.E (x[n][w].st).st
            (M.confirmation_time S.E s)).core)
          ((M.round_of S.hc) (M.ns_setClock S.E (x[n][w].st).st
            (M.confirmation_time S.E s)).core.s) ⇢ some G →
      Block.Preceq P G ∨
        (Block.Compatible P G ∧ Block.Preceq P (x[n][w].st).st.core.latest_stable))
    (hneTick : ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) w (Record.wakeStage M Sched (M.confirmation_time S.E s) x[n] w) (M.confirmation_time S.E s) ⇢ out)
    -- `w`'s tick at step `n` passes the grade-2 awake test of slot `s + 1`'s round.
    (hrun : M.awake_for_grade2 (Setup.alwaysAwake S) w
      (Record.wakeStage M Sched (M.confirmation_time S.E s) x[n] w) (M.round_of S.hc (s + 1))) :
    Block.Preceq P (x[n + 1][w].st).st.core.latest_stable := by
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc (M.toHealing (x[n][w].st).st.core)
    (M.confirmation_time S.E s) (x[n][w].st).cache
  obtain ⟨o, ho'⟩ := facts.gr.frameStableRoot_nonempty c S.E S.hc
    (M.toHealing (M.ns_setClock S.E (x[n][w].st).st (M.confirmation_time S.E s)).core)
    ((M.round_of S.hc) (M.ns_setClock S.E (x[n][w].st).st (M.confirmation_time S.E s)).core.s)
  have ho := (facts.nd.gradeContract_stableRoot _ _ _ _ _ o).2 ho'
  obtain ⟨G, rfl, hstab, -⟩ :=
    Restated.records_after_confirmation_tick facts S Sched x hn haw hneTick hrun c hc _ ho
  rcases hroot c hc G ho with hPG | ⟨hcomp, hold⟩
  · exact Restated.latest_stable_preceq_of_stableRoot facts S Sched x hn haw hc ho hPG hneTick hrun
  · rcases compatible_cases (compatible_iff_Compatible.mp hcomp) with hPG | hGP
    · exact Restated.latest_stable_preceq_of_stableRoot facts S Sched x hn haw hc ho hPG hneTick hrun
    · have hGold := preceq_trans_Preceq hGP hold
      rw [hstab]
      rcases facts.hd.advance_confirmed_values (x[n][w].st).st.core.latest_stable G with
        ⟨-, he⟩ | he
      · rw [he]; exact hold
      · rcases facts.hd.advance_confirmed_eq_or_not_preceq (x[n][w].st).st.core.latest_stable G
          with he' | hn'
        · rw [he']; exact hold
        · rw [he] at hn'
          exact absurd hGold hn'

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If step `k` is not the tick at a confirmation instant at which `w` is awake and not held, then
    `w`'s stable record after step `k` is the one it held before. -/
theorem latest_stable_unchanged_off_confirmation (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (w : V) (k : Nat)
    (hnot : ¬ ∃ s : Slot, Restated.tickStepAt M x k (M.confirmation_time S.E s) ∧
      w ∈ Sched.awake (M.confirmation_time S.E s) \
        Sched.adv (M.confirmation_time S.E s)) :
    (x[k + 1][w].st).st.core.latest_stable = (x[k][w].st).st.core.latest_stable := by
  rcases Restated.records_succ_cases facts S Sched x w k with ⟨h1, -⟩ | hc
  · exact h1
  · exact absurd hc hnot

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If `w`'s stable record after `k` steps is a descendant of `P`, and, whenever step `k` is the
    tick at a slot `s`'s confirmation instant at which `w` is awake and not held, for every outcome
    `c` of `w`'s cache update there every block `G` the stable root of `c`'s grade contract can
    return as `some G` is compatible with `P`, then `w`'s stable record after `k + 1` steps is a
    descendant of `P`. -/
theorem preceq_latest_stable_succ (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (w : V) (k : Nat) {P : Block V}
    (hold : Block.Preceq P (x[k][w].st).st.core.latest_stable)
    (hroot : ∀ s : Slot, Restated.tickStepAt M x k (M.confirmation_time S.E s) →
      w ∈ Sched.awake (M.confirmation_time S.E s) \
        Sched.adv (M.confirmation_time S.E s) →
      ∀ c : M.Cache, M.onPhaseTick S.E S.hc (M.toHealing (x[k][w].st).st.core)
        (M.confirmation_time S.E s) (x[k][w].st).cache ⇢ c →
      ∀ G : Block V,
      (M.gradeContract c).stableRoot S.E S.hc
          (M.toHealing (M.ns_setClock S.E (x[k][w].st).st
            (M.confirmation_time S.E s)).core)
          ((M.round_of S.hc) (M.ns_setClock S.E (x[k][w].st).st
            (M.confirmation_time S.E s)).core.s) ⇢ some G →
      Block.Compatible P G)
    (hnr : ∀ (k τ : Nat) (u : V), x.lbl k = AtomicAction.tickAllAwake τ →
      (τ : Int) % S.E.Δ = 0 → u ∈ Sched.awake (τ : Int) \ Sched.adv (τ : Int) →
      (∀ t' ≤ (τ : Int), u ∉ Sched.adv t') →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) u (Record.wakeStage M Sched (τ : Int) x[k] u) (τ : Int) ⇢ out) :
    Block.Preceq P (x[k + 1][w].st).st.core.latest_stable := by
  by_cases hc : ∃ s : Slot, Restated.tickStepAt M x k (M.confirmation_time S.E s) ∧
      w ∈ Sched.awake (M.confirmation_time S.E s) \
        Sched.adv (M.confirmation_time S.E s)
  · obtain ⟨s, hn, haw⟩ := hc
    obtain ⟨t', hlbl, ht'⟩ := id hn
    have hdvd : (t' : Int) % S.E.Δ = 0 := by
      rw [ht', facts.sch.confirmation_time_eq_support_cutoff_succ]
      exact facts.sch.support_cutoff_emod_delta S (s + 1)
    have haw' : w ∈ Sched.awake (t' : Int) \ Sched.adv (t' : Int) := by rw [ht']; exact haw
    rcases Restated.st_succ_of_tick_awake facts S Sched x w hlbl haw' with
      ⟨out, hout, hst⟩ | ⟨-, hst⟩
    · rw [ht'] at hout
      by_cases hrun : M.awake_for_grade2 (Setup.alwaysAwake S) w
          (Record.wakeStage M Sched (M.confirmation_time S.E s) x[k] w) (M.round_of S.hc (s + 1))
      · -- the tick has an outcome and `w` passes the grade-2 awake test
        exact Restated.stable_record_step_at_confirmation_tick facts S Sched x hn haw
          (fun c hc' G hG => Or.inr ⟨hroot s hn haw c hc' G hG, hold⟩) ⟨out, hout⟩ hrun
      · -- the tick has an outcome and `w` fails the grade-2 awake test: the stable record is kept
        obtain ⟨-, hL⟩ :=
          facts.nd.tick_records_frame_of_not_awake_for_grade2 S w _ s out hout hrun
        rw [hst, hL, Record.wakeStage_st facts]
        exact hold
    · -- the tick has no outcome: the node state is the one the tick read
      rw [hst, Record.wakeStage_st facts]
      exact hold
  · rw [Restated.latest_stable_unchanged_off_confirmation facts S Sched x w k hc]
    exact hold

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If step `n` is the tick at slot `s`'s confirmation instant, then every validator `w`'s finalized
    block, justified block, justified height, largest height, block tree and bodies after the tick
    are those it held before. -/
theorem tick_tree_fields_at_confirmation (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {n : Nat} {s : Slot}
    (hn : Restated.tickStepAt M x n (M.confirmation_time S.E s)) (w : V) :
    (x[n + 1][w].st).st.core.F = (x[n][w].st).st.core.F ∧
      (x[n + 1][w].st).st.core.J = (x[n][w].st).st.core.J ∧
      (x[n + 1][w].st).st.core.h_j = (x[n][w].st).st.core.h_j ∧
      (x[n + 1][w].st).st.core.h_max = (x[n][w].st).st.core.h_max ∧
      (x[n + 1][w].st).st.core.T = (x[n][w].st).st.core.T ∧
      (x[n + 1][w].st).st.bodies = (x[n][w].st).st.bodies := by
  obtain ⟨t', hlbl, ht'⟩ := hn
  have hslot : S.E.slotOf (M.confirmation_time S.E s) = s + 1 :=
    facts.sch.Optimistic_slotOf_confirmation_time S.E s
  have hcs : M.confirmation_time S.E s = M.support_cutoff S.E (s + 1) :=
    facts.sch.confirmation_time_eq_support_cutoff_succ S.E s
  have hnp : M.confirmation_time S.E s
      ≠ M.proposal_time S.E (S.E.slotOf (M.confirmation_time S.E s)) := by
    rw [hslot, hcs]
    exact facts.sch.support_cutoff_ne_proposal_time S.E (s + 1)
  have hnv : M.confirmation_time S.E s
      ≠ M.vote_time S.E (S.E.slotOf (M.confirmation_time S.E s)) := by
    rw [hslot, hcs]
    exact facts.sch.support_cutoff_ne_vote_time S.E (s + 1)
  rcases Restated.st_succ_of_tick facts S Sched x w hlbl with ⟨-, out, hout, hst⟩ | hst
  · rw [hst]
    rw [ht'] at hout
    have h := facts.nd.tick_tree_fields_of_not_proposal_vote (Setup.alwaysAwake S) w _
      (M.confirmation_time S.E s) hnp hnv out hout
    rw [Record.wakeStage_st facts] at h
    exact h
  · rw [hst, Record.wakeStage_st facts]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If step `n` is the tick at round `ρ`'s action instant, then every validator `w`'s finalized
    block, justified block, justified height, largest height, block tree and bodies after the tick
    are those it held before. -/
theorem tick_tree_fields_at_action (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {n : Nat} {ρ : Nat}
    (hn : Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S ρ))) (w : V) :
    (x[n + 1][w].st).st.core.F = (x[n][w].st).st.core.F ∧
      (x[n + 1][w].st).st.core.J = (x[n][w].st).st.core.J ∧
      (x[n + 1][w].st).st.core.h_j = (x[n][w].st).st.core.h_j ∧
      (x[n + 1][w].st).st.core.h_max = (x[n][w].st).st.core.h_max ∧
      (x[n + 1][w].st).st.core.T = (x[n][w].st).st.core.T ∧
      (x[n + 1][w].st).st.bodies = (x[n][w].st).st.bodies := by
  rw [← Restated.confirmation_time_opening_slot facts S ρ] at hn
  exact Restated.tick_tree_fields_at_confirmation facts S Sched x hn w

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If the round-`r` frame read from the cache `c` at the store `st` holds the grade-2 entry `e`,
    `P` is `e` or an ancestor of `e`, and `P` and the store's fork-choice root lie on one chain,
    then every block `G` that the stable root of the grade contract of `c` at `st` and `r` can
    return as `some G` lies on one chain with `P`. -/
theorem stableRoot_compatible_of_frame (facts : Record.Facts M) (c : M.Cache) (E : Env V)
    (hc : Protocol.HealConfig) (st : M.HS) (r : Round) {P e G : Block V}
    (he : (M.readFrame c st r).g2 = some (some e)) (hPe : Block.Preceq P e)
    (hfg : Block.Compatible P (M.get_fg_root st.toFG))
    (hG : (M.gradeContract c).stableRoot E hc st r ⇢ some G) :
    Block.Compatible P G := by
  have hG := (facts.nd.gradeContract_stableRoot _ _ _ _ _ _).1 hG
  rcases facts.gr.frameStableRoot_cases c E hc st r _ hG rfl with hGr | ⟨e', he', hGe⟩
  · rw [hGr]; exact hfg
  · have hee : e' = e := by
      rw [he] at he'
      exact Option.some.inj (Option.some.inj he').symm
    rw [hee] at hGe
    exact compatible_iff_Compatible.mpr (compatible_of_preceq_common_Preceq hPe hGe)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If the round-`r` frame read from the cache `c` at the store `st` holds the grade-2 entry `e`,
    `P` is `e` or an ancestor of `e`, and `P` is in the store's filtered block tree or is an
    ancestor of its fork-choice root, then every block `G` that the stable root of the grade
    contract of `c` at `st` and `r` can return as `some G` is `P` or a descendant of `P`. -/
theorem stableRoot_preceq_of_frame (facts : Record.Facts M) (c : M.Cache) (E : Env V)
    (hc : Protocol.HealConfig) (st : M.HS) (r : Round) {P e G : Block V}
    (he : (M.readFrame c st r).g2 = some (some e)) (hPe : Block.Preceq P e)
    (hP : P ∈ M.get_filtered_block_tree st.toFG ∨
      Block.Preceq P (M.get_fg_root st.toFG))
    (hG : (M.gradeContract c).stableRoot E hc st r ⇢ some G) :
    Block.Preceq P G := by
  have hG := (facts.nd.gradeContract_stableRoot _ _ _ _ _ _).1 hG
  exact facts.gr.preceq_frameStableRoot c E hc st r he hPe hP _ hG rfl

end

end DecoupledConsensusModel.Sts.Restated
