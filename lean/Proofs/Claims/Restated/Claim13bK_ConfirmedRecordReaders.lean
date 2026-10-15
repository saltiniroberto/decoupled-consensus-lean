import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bK_ConfirmedRecord
import Proofs.Claims.Restated.Claim13bK_ConfirmedSettle
import Proofs.Claims.Restated.Claim13bK_ConfirmedStrongRoundWindow
import Proofs.Claims.Restated.Claim13bK_Frame
import Proofs.Claims.Restated.Claim13bK_HeadsPersist
import Proofs.Claims.Restated.Claim13bK_LiveConfirmedSlots
import Proofs.Claims.Restated.Claim13bK_PrevHeadsStep
import Proofs.Claims.Restated.Claim13bStepConeIter
import Proofs.Claims.Restated.Claim13bStepKitConfirm
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bW_Schedule
import Proofs.Claims.Restated.Claim13beRoute3_82
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActive
import Model.Conditions.Claim13bInvariantActiveJoint
import Model.Conditions.Claim13bInvariantActiveSinceW
import Model.Conditions.Claim13bInvariantActiveTop
import Model.Conditions.Claim13bK_ConfirmedRecord
import Model.Conditions.Claim13bK_ConfirmedSettle
import Model.Conditions.Claim13bK_FinBeforeTick
import Model.Conditions.Claim13bK_Frame
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13bStepCone
import Model.Conditions.Claim13bStepConeIter
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
import Proofs.Claims.Restated.Claim13bK_ConfirmedRecordReadersRecv
import Proofs.Claims.Restated.Claim13bK_PrevHeadsStepRecv

/-!
# Confirmed records at readers given by their awake window

After the phase, a validator's stable root, two records and confirmed output are ancestors of every
honest head from some slot on, for a validator given by its awake window and its honesty through the
read. Stated over a model `M : Record.Model V` and its facts.
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
local macro "pCR% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13bK_ConfirmedRecord)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "pW% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13bK_ConfirmedStrongRoundWindow)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- Under its premises on the execution and the phase ending at `tE`, with the joint invariant at a
    round `r₀` at or after the switch round for an anchor that is `T_W` or a descendant of it: if
    `r₀ < r_b`, step `k₀`'s time is at or after `S.a r_b`, `v`'s two records satisfy
    `RecordsAncestorOfHonestHeads` after `k₀` steps, `k₀ ≤ N`, `v` is awake from `S.a (r_b − 1)` to
    every slot confirmation instant after `x[k₀].time` and at or before `x[N].time`, and `v` is
    honest through step `N`, then `v`'s two records satisfy `RecordsAncestorOfHonestHeads` after `N`
    steps. -/
theorem records_ancestorOfHonestHeads_of_base_honestThrough (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (hcatch : Restated.CatchUpOnWake M S x) (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (hsync : Restated.SynchronyFromWake M S x) (hthird : ∀ t : Int, t ≤ tE →
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
    {r_b : Round} (hrb : r₀ + 1 ≤ r_b) {k₀ : Nat} (hk₀ : (Restated.Vocabulary.Execution.Setup.a M S r_b) ≤ (x[k₀].time : Int))
    {v : V} (hbase : Restated.RecordsAncestorOfHonestHeads M S Sched x v k₀)
    {N : Nat} (hkN : k₀ ≤ N)
    (hwin : ∀ s : Slot, (x[k₀].time : Int) < M.confirmation_time S.E s →
      M.confirmation_time S.E s ≤ (x[N].time : Int) →
      v ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S (r_b - 1))) (M.confirmation_time S.E s))
    (hvh : Restated.HonestThrough M Sched x N v) :
    Restated.RecordsAncestorOfHonestHeads M S Sched x v N := by
  have hd := S.E.Δ_pos
  have hrb0 : 0 < r_b := Nat.lt_of_lt_of_le (Nat.succ_pos r₀) hrb
  suffices key : ∀ n : Nat, k₀ ≤ n → n ≤ N → Restated.RecordsAncestorOfHonestHeads M S Sched x v n from
    key N hkN le_rfl
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => intro _; exact hbase
  | succ n hkn ih =>
    intro hnN
    have ihn := ih (Nat.le_of_succ_le hnN)
    rcases Restated.records_succ_cases facts S Sched x v n with ⟨h1, h2⟩ | ⟨s, hm, haw⟩
    · have hsl : S.E.slotOf (x[n].time : Int) + 2 ≤ S.E.slotOf (x[n + 1].time : Int) + 2 :=
        Nat.add_le_add_right (slotOf_mono_sts S (Restated.time_mono_int facts S Sched x (Nat.le_succ n))) 2
      unfold Restated.RecordsAncestorOfHonestHeads
      rw [h1, h2]
      exact ⟨Restated.ancestorOfHonestHeadsFrom_mono facts S Sched x hsl ihn.1,
        Restated.ancestorOfHonestHeadsFrom_mono facts S Sched x hsl ihn.2⟩
    · obtain ⟨hn1, hn0⟩ := Restated.tickStepAt_time facts x hm
      have hslot : S.E.slotOf (x[n + 1].time : Int) = s + 1 := by
        rw [hn1]; exact facts.sch.Optimistic_slotOf_confirmation_time S.E s
      have htk : (x[k₀].time : Int) < M.confirmation_time S.E s := by
        have := Restated.time_mono_int facts S Sched x hkn; linarith
      have htN : M.confirmation_time S.E s ≤ (x[N].time : Int) := by
        rw [← hn1]; exact Restated.time_mono_int facts S Sched x hnN
      obtain ⟨hs1, hrr, hwinlo, -, -⟩ :=
        Restated.confirmation_tick_arith facts S hrb0 (lt_of_le_of_lt hk₀ htk)
      have hs0 : (M.opening_slot S.hc r₀) + 2 ≤ s := by
        have h1 := facts.gr.opening_slot_mono S hrb
        rw [facts.gr.opening_slot_succ] at h1
        exact nat_add_two_le_c3 h1 hs1 S.hc.R_ge_three
      have hwin' := hwin s htk htN
      have hvaw : v ∈ Sched.awakeThroughout (slotStart S.E.Δ s - S.E.Δ)
          (M.confirmation_time S.E s) := awakeThroughout_mono Sched hwin' hwinlo le_rfl
      have hvA : v ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S ((M.round_of S.hc (s + 1)) - 1)))
          (M.confirmation_time S.E s) :=
        awakeThroughout_mono Sched hwin' (Restated.action_mono facts S (Nat.sub_le_sub_right hrr 1)) le_rfl
      have hvh' : HonestThroughTime Sched (M.confirmation_time S.E s) v :=
        fun t ht => hvh t (le_trans ht htN)
      have hL : Restated.AncestorOfHonestHeadsFrom M S Sched x (x[n][v].st).st.core.latest_stable (s + 3) :=
        Restated.ancestorOfHonestHeadsFrom_mono facts S Sched x (Nat.add_le_add_right
          (by rw [← facts.sch.Optimistic_slotOf_confirmation_time S.E s]
              exact slotOf_mono_sts S (by linarith)) 2) ihn.1
      have hC : Restated.AncestorOfHonestHeadsFrom M S Sched x (x[n][v].st).st.core.latest_confirmed
          (s + 3) :=
        Restated.ancestorOfHonestHeadsFrom_mono facts S Sched x (Nat.add_le_add_right
          (by rw [← facts.sch.Optimistic_slotOf_confirmation_time S.E s]
              exact slotOf_mono_sts S (by linarith)) 2) ihn.2
      have hres : Restated.AncestorOfHonestHeadsFrom M S Sched x (x[n + 1][v].st).st.core.latest_stable
            (s + 3) ∧
          Restated.AncestorOfHonestHeadsFrom M S Sched x (x[n + 1][v].st).st.core.latest_confirmed
            (s + 3) := by
        by_cases hrun : M.awake_for_grade2 (Setup.alwaysAwake S) v
            (Record.wakeStage M Sched (M.confirmation_time S.E s) x[n] v) (M.round_of S.hc (s + 1))
        swap
        · obtain ⟨t', hlbl, ht'⟩ := id hm
          have haw' : v ∈ Sched.awake (t' : Int) \ Sched.adv (t' : Int) := by rw [ht']; exact haw
          rcases Restated.st_succ_of_tick_awake facts S Sched x v hlbl haw' with
            ⟨out, hout, hst⟩ | ⟨-, hst⟩
          · rw [ht'] at hout
            obtain ⟨hCk, hLk⟩ :=
              facts.nd.tick_records_frame_of_not_awake_for_grade2 S v _ s out hout hrun
            rw [hst, hLk, hCk, Record.wakeStage_st facts]
            exact ⟨hL, hC⟩
          · rw [hst, Record.wakeStage_st facts]
            exact ⟨hL, hC⟩
        have hd1 : (1 : Int) ≤ S.E.Δ := hd
        have hr'0 : 0 < M.round_of S.hc (s + 1) := lt_of_lt_of_le hrb0 hrr
        have hrW : Restated.switchRound M S tE ≤ M.round_of S.hc (s + 1) - 1 :=
          le_trans hr₀ (Nat.le_sub_of_add_le (le_trans hrb hrr))
        have hG := Restated.gst_le_action_of_switchRound_le facts S tGAT tE gap hgst hlen hrW
        have hS := facts.gr.action_delta_le_early S S.hc.R_ge_three (Nat.sub_lt hr'0 Nat.one_pos)
        have he := facts.gr.early_g2_eq S (M.round_of S.hc (s + 1))
        have hl9 := Restated.action_sub_nine_delta_le_late facts S (M.round_of S.hc (s + 1)) .g2
        obtain ⟨-, -, -, -, hup'⟩ := Restated.confirmation_tick_arith facts S hrb0 (lt_of_le_of_lt hk₀ htk)
        have hup : M.a S.hc S.E.Δ (M.round_of S.hc (s + 1)) ≤ M.confirmation_time S.E s + 4 * S.E.Δ := hup'
        have hA1 : M.a S.hc S.E.Δ (M.round_of S.hc (s + 1) - 1) + S.E.Δ ≤ M.confirmation_time S.E s := by
          linarith
        have ht₀ : M.a S.hc S.E.Δ (M.round_of S.hc (s + 1) - 1)
            ≤ M.late S.E S.hc (M.round_of S.hc (s + 1)) .g2 - 1 - 2 * S.E.Δ := by
          linarith
        have hrecv : Restated.ReceivesRoundAttestationsBefore M S Sched x ((M.round_of S.hc (s + 1)) - 1) v
            (M.early S.E S.hc (M.round_of S.hc (s + 1)) .g2) :=
          (Restated.receivesRoundAttestationsBefore_of_awakeFrom facts S Sched x hsync hcatch
            (r := M.round_of S.hc (s + 1) - 1) le_rfl hG
            (awakeThroughout_mono Sched hvA le_rfl hA1)).mono hS
        exact Restated.records_after_confirmation_tick_ancestorOfHonestHeadsFrom_ofAwake_recv facts S Sched x tE
          hexec hmono htd hcatch tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom
          hrec hprev hclear hB' hnW hAW hJswitch hr₀ hTW₀ hJ₀ hs0 (le_trans hrb hrr) hm hvaw
          _ ht₀ hvA hrecv hvh' hrun hL hC
      unfold Restated.RecordsAncestorOfHonestHeads
      rw [hslot]
      exact hres

end


end DecoupledConsensusModel.Sts.Restated
