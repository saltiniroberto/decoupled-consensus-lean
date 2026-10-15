import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bK_ConfirmedRecord
import Proofs.Claims.Restated.Claim13bK_ConfirmedRecordReaders
import Proofs.Claims.Restated.Claim13bK_ConfirmedSettle
import Proofs.Claims.Restated.Claim13bK_HeadsPersist
import Proofs.Claims.Restated.Projection
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActiveJoint
import Model.Conditions.Claim13bInvariantActiveSinceW
import Model.Conditions.Claim13bK_ConfirmedRecord
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
import Model.Conditions.Sts_Spec2Claims_ClaimConfirmedAfterHealing
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Vocabulary.Protocol.Grades
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Protocol_Grades_Main
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bK_ConfirmedAgree

/-!
# Agreement of confirmed outputs after healing

Two blocks that are ancestors of every honest head from some slot on lie on one chain; a validator's
confirmed output only extends while its records keep that property; and from
`RecordsSettledAtActionTicks`, confirmed outputs agree after the settle instant. Stated over a model
`M : Record.Model V` and its facts.
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
local macro "pW% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13bK_ConfirmedStrongRoundWindow)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog

/-- On an execution whose clock diverges, under `committeeSleepinessW` from `tE`, if every honest
    active committee member of every slot from `s_0` on votes for a descendant of `A`, and of every
    slot from `s_1` on for a descendant of `B`, then `A` and `B` lie on one chain. -/
theorem compatible_of_ancestorOfHonestHeadsFrom_after (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (htd : Restated.TimeDiverges M x) {tE : Int}
    (hcs : Restated.committeeSleepinessW M S Sched tE) {A B : Block V} {s_0 s_1 : Slot}
    (hA : Restated.AncestorOfHonestHeadsFrom M S Sched x A s_0)
    (hB : Restated.AncestorOfHonestHeadsFrom M S Sched x B s_1) :
    Block.compatible A B = true :=
  Restated.compatible_of_headsBelow_after facts S Sched x htd hcs (s := s_0 + s_1 + tE.toNat + 1)
    (Nat.succ_pos _) (le_slotStart_of_toNat S.E.Δ S.E.Δ_pos tE s_0 s_1)
    (hA _ (nat_le_sum_left_c4 s_0 s_1 tE.toNat)) (hB _ (nat_le_sum_right_c4 s_0 s_1 tE.toNat))

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog

/-- Every outcome of `update_confirmation_with` has as `latest_confirmed` the store's
    `latest_confirmed` or a block that is not an ancestor of it. -/
theorem update_confirmation_with_latest_confirmed_eq_or_not_preceq (facts : Record.Facts M)
    (contract : M.Contract) (E : Env V) (hc : Protocol.HealConfig)
    (st : M.S) (s : Slot) :
    ∀ D : M.S, M.update_confirmation_with contract E hc st s ⇢ D →
      (D.latest_confirmed = st.latest_confirmed ∨
        ¬ Block.Preceq D.latest_confirmed st.latest_confirmed) := by
  intro D hD
  obtain ⟨cand, hfl, hcases⟩ := (pW% update_confirmation_with_latest_confirmed_candidate_csw) facts
    contract E hc st s D hD
  rw [hfl]
  have hcand : cand = st.latest_confirmed ∨ ¬ Block.Preceq cand st.latest_confirmed := by
    rcases hcases with h | h | ⟨G, -, h⟩
    · exact Or.inl h
    · rw [h]; exact facts.hd.advance_confirmed_eq_or_not_preceq _ _
    · rw [h]; exact facts.hd.advance_confirmed_eq_or_not_preceq _ _
  rcases facts.hd.floor_on_stable_cases D.latest_stable cand
      st.latest_confirmed with h | h | h
  · rw [h]; exact hcand
  · exact Or.inl h
  · exact Or.inr h

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog

/-- Given that the ticks named by `hnr` have an outcome, step `k` leaves each of `v`'s
    `latest_stable` and `latest_confirmed` as it was, or replaces it with a block that is not an
    ancestor of the old one. -/
theorem records_succ_eq_or_not_preceq (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v : V) (k : Nat)
    (hnr : ∀ (k τ : Nat) (u : V), x.lbl k = AtomicAction.tickAllAwake τ →
      (τ : Int) % S.E.Δ = 0 → u ∈ Sched.awake (τ : Int) \ Sched.adv (τ : Int) →
      (∀ t' ≤ (τ : Int), u ∉ Sched.adv t') →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) u (Record.wakeStage M Sched (τ : Int) x[k] u) (τ : Int) ⇢ out) :
    ((x[k + 1][v].st).st.core.latest_stable = (x[k][v].st).st.core.latest_stable ∨
      ¬ Block.Preceq (x[k + 1][v].st).st.core.latest_stable
        (x[k][v].st).st.core.latest_stable) ∧
    ((x[k + 1][v].st).st.core.latest_confirmed = (x[k][v].st).st.core.latest_confirmed ∨
      ¬ Block.Preceq (x[k + 1][v].st).st.core.latest_confirmed
        (x[k][v].st).st.core.latest_confirmed) := by
  rcases Restated.records_succ_cases facts S Sched x v k with ⟨h1, h2⟩ | ⟨s, hm, haw⟩
  · exact ⟨Or.inl h1, Or.inl h2⟩
  · obtain ⟨t', hlbl, ht'⟩ := hm
    have hdvd : (t' : Int) % S.E.Δ = 0 := by
      rw [ht', facts.sch.confirmation_time_eq_support_cutoff_succ]
      exact facts.sch.support_cutoff_emod_delta S (s + 1)
    have haw' : v ∈ Sched.awake (t' : Int) \ Sched.adv (t' : Int) := by rw [ht']; exact haw
    rcases Restated.st_succ_of_tick_awake facts S Sched x v hlbl haw' with
      ⟨out, hout, hst⟩ | ⟨-, hst⟩
    · rw [ht'] at hout
      by_cases hrun : M.awake_for_grade2 (Setup.alwaysAwake S) v
          (Record.wakeStage M Sched (M.confirmation_time S.E s) x[k] v) (M.round_of S.hc (s + 1))
      · -- the tick has an outcome and `v` passes the grade-2 awake test
        obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc
          (M.toHealing (x[k][v].st).st.core) (M.confirmation_time S.E s) (x[k][v].st).cache
        obtain ⟨o, ho'⟩ := facts.gr.frameStableRoot_nonempty c S.E S.hc
          (M.toHealing (M.ns_setClock S.E (x[k][v].st).st (M.confirmation_time S.E s)).core)
          ((M.round_of S.hc)
            (M.ns_setClock S.E (x[k][v].st).st (M.confirmation_time S.E s)).core.s)
        have ho := (facts.nd.gradeContract_stableRoot _ _ _ _ _ o).2 ho'
        obtain ⟨G, -, hstab, hconf⟩ := Restated.records_after_confirmation_tick facts S Sched x
          ⟨t', hlbl, ht'⟩ haw ⟨out, hout⟩ hrun c hc o ho
        obtain ⟨D, hD⟩ := facts.dt.update_confirmation_with_nonempty (M.gradeContract c) S.E S.hc
          (M.ns_setClock S.E (x[k][v].st).st (M.confirmation_time S.E s)).core s
        refine ⟨?_, ?_⟩
        · rw [hstab]; exact facts.hd.advance_confirmed_eq_or_not_preceq _ _
        · rw [hconf D hD, ← facts.hd.setClock_core_latest_confirmed S.E (x[k][v].st).st
            (M.confirmation_time S.E s)]
          exact Restated.update_confirmation_with_latest_confirmed_eq_or_not_preceq facts _ _ _ _ _
            D hD
      · -- the tick has an outcome and `v` fails the grade-2 awake test: both records are kept
        obtain ⟨hC, hL⟩ :=
          facts.nd.tick_records_frame_of_not_awake_for_grade2 S v _ s out hout hrun
        rw [hst, hL, hC, Record.wakeStage_st facts]
        exact ⟨Or.inl rfl, Or.inl rfl⟩
    · -- the tick has no outcome: the node state is the one the tick read
      rw [hst, Record.wakeStage_st facts]
      exact ⟨Or.inl rfl, Or.inl rfl⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog

/-- On an execution whose clock diverges, under `committeeSleepinessW` from `tE`, if `v`'s two
    records after `k` and after `k + 1` steps satisfy `RecordsAncestorOfHonestHeads`, `v`'s
    finalized block after `k + 1` steps is an ancestor of every honest head from slot `s_F` on, and
    the ticks named by `hnr` have an outcome, then `v`'s `get_confirmed` after `k` steps is an
    ancestor of its `get_confirmed` after `k + 1` steps. -/
theorem get_confirmed_succ_preceq (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (htd : Restated.TimeDiverges M x) {tE : Int}
    (hcs : Restated.committeeSleepinessW M S Sched tE) (v : V) (k : Nat) {s_F : Slot}
    (hpre : Restated.RecordsAncestorOfHonestHeads M S Sched x v k)
    (hpost : Restated.RecordsAncestorOfHonestHeads M S Sched x v (k + 1))
    (hF : Restated.AncestorOfHonestHeadsFrom M S Sched x (x[k + 1][v].st).st.core.F s_F)
    (hnr : ∀ (k τ : Nat) (u : V), x.lbl k = AtomicAction.tickAllAwake τ →
      (τ : Int) % S.E.Δ = 0 → u ∈ Sched.awake (τ : Int) \ Sched.adv (τ : Int) →
      (∀ t' ≤ (τ : Int), u ∉ Sched.adv t') →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) u (Record.wakeStage M Sched (τ : Int) x[k] u) (τ : Int) ⇢ out) :
    Block.Preceq (M.get_confirmed (x[k][v].st).st.core)
      (M.get_confirmed (x[k + 1][v].st).st.core) := by
  obtain ⟨hLeq, hCeq⟩ := Restated.records_succ_eq_or_not_preceq facts S Sched x v k hnr
  have hL := preceq_of_compatible_of_eq_or_not_preceq
    (Restated.compatible_of_ancestorOfHonestHeadsFrom_after facts S Sched x htd hcs hpre.1 hpost.1) hLeq
  have hC := preceq_of_compatible_of_eq_or_not_preceq
    (Restated.compatible_of_ancestorOfHonestHeadsFrom_after facts S Sched x htd hcs hpre.2 hpost.2) hCeq
  set s₁ : Slot := S.E.slotOf (x[k + 1].time : Int) + 2 with hs₁
  have hLs : Restated.AncestorOfHonestHeadsFrom M S Sched x (x[k + 1][v].st).st.core.latest_stable
      (s₁ + s_F) :=
    Restated.ancestorOfHonestHeadsFrom_mono facts S Sched x (Nat.le_add_right _ _) hpost.1
  have hFs : Restated.AncestorOfHonestHeadsFrom M S Sched x (x[k + 1][v].st).st.core.F (s₁ + s_F) :=
    Restated.ancestorOfHonestHeadsFrom_mono facts S Sched x (Nat.le_add_left _ _) hF
  have hS := Restated.ancestorOfHonestHeadsFrom_get_stable facts S Sched x _ hLs hFs
  exact facts.hd.get_confirmed_preceq_of_fields _ _ (Restated.F_mono_succ facts S Sched x v k) hL hC
    (Restated.compatible_of_ancestorOfHonestHeadsFrom_after facts S Sched x htd hcs hF hpost.1)
    (Restated.compatible_of_ancestorOfHonestHeadsFrom_after facts S Sched x htd hcs hS hpost.2)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog

/-- On an execution whose clock diverges, under `committeeSleepinessW` from `tE`, if `i ≤ j`, `v`'s
    two records satisfy `RecordsAncestorOfHonestHeads` at every step from `i` to `j`, `v`'s
    finalized block at every step `k` with `i < k ≤ j` is an ancestor of every honest head from slot
    `slot(x[k].time) + 2` on, and the ticks named by `hnr` have an outcome, then `v`'s
    `get_confirmed` after `i` steps is an ancestor of its `get_confirmed` after `j` steps. -/
theorem get_confirmed_preceq_of_records_along (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (htd : Restated.TimeDiverges M x) {tE : Int}
    (hcs : Restated.committeeSleepinessW M S Sched tE) (v : V) {i j : Nat} (hij : i ≤ j)
    (hrec : ∀ k : Nat, i ≤ k → k ≤ j → Restated.RecordsAncestorOfHonestHeads M S Sched x v k)
    (hF : ∀ k : Nat, i < k → k ≤ j →
      Restated.AncestorOfHonestHeadsFrom M S Sched x (x[k][v].st).st.core.F
        (S.E.slotOf (x[k].time : Int) + 2))
    (hnr : ∀ (k τ : Nat) (u : V), x.lbl k = AtomicAction.tickAllAwake τ →
      (τ : Int) % S.E.Δ = 0 → u ∈ Sched.awake (τ : Int) \ Sched.adv (τ : Int) →
      (∀ t' ≤ (τ : Int), u ∉ Sched.adv t') →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) u (Record.wakeStage M Sched (τ : Int) x[k] u) (τ : Int) ⇢ out) :
    Block.Preceq (M.get_confirmed (x[i][v].st).st.core)
      (M.get_confirmed (x[j][v].st).st.core) := by
  suffices key : ∀ n : Nat, i ≤ n → n ≤ j →
      Block.Preceq (M.get_confirmed (x[i][v].st).st.core)
        (M.get_confirmed (x[n][v].st).st.core) from key j hij le_rfl
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => intro _; exact preceq_eq_true_iff_Preceq.mp (Block.preceq_self _)
  | succ n hin ih =>
    intro hnj
    exact preceq_trans_Preceq (ih (Nat.le_of_succ_le hnj))
      (Restated.get_confirmed_succ_preceq facts S Sched x htd hcs v n
        (hrec n hin (Nat.le_of_succ_le hnj)) (hrec (n + 1) (Nat.le_succ_of_le hin) hnj)
        (hF (n + 1) (Nat.lt_succ_of_le hin) hnj) hnr)

end


end DecoupledConsensusModel.Sts.Restated
