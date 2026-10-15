import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bK_ConeChainUpTo
import Proofs.Claims.Restated.Claim13bK_HolderMargins
import Proofs.Claims.Restated.Projection
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActiveTop
import Model.Conditions.Claim13bK_FinBeforeTick
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13beRoute3_7
import Model.Conditions.ClaimAsyncK_DeliveryUpTo
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_Grades_Main
import Model.Record.Wiring

/-!
# Chain-in-tree facts from a held block, with synchrony up to a bound

The chain-in-tree fact `ConeAnchorChainInTree` from a held block or an eligible confirmation, with
synchrony assumed only up to round `r + 1`'s action instant, stated over a model
`M : Record.Model V` and its facts `facts : Record.Facts M`.
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
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If `v_1` holds `B` at a step at or after `tGAT` and more than a delay before slot `s`'s view
    freeze, `X` is an ancestor of `B` and a descendant of `T`, and every tick of an honest active
    member of slot `(s + 1)`'s committee before that slot's vote instant has an outcome
    (`hneTickW`), then every block strictly between an honest active reader's SG root and `X` is in
    that reader's slot-`(s + 1)` voter tree; synchrony is assumed up to `S.a (r + 1)` only. -/
theorem coneAnchorChainInTree_of_heldDescendant_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    {r : Round} (hsync : Restated.SynchronyFromWakeBefore M S x ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    (hmult : AwakeAtMultiples S Sched)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE) (hcs : Restated.committeeSleepinessW M S Sched tE)
    {n : Nat} {T : NamedBlock V}
    (hr : Restated.switchRound M S tE ≤ r) (hinv : Restated.AfterPhaseInvariantOverActiveSetsTop M S Sched x r n T)
    (hcross : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepFinalizedCrossingUnderAnchor M S Sched x r n'' T)
    {B : NamedBlock V} {v_1 : V} {m : Nat} (hBv_1 : B ∈ (x[m][v_1].st).st.bodies)
    (hv_1 : Restated.HonestThrough M Sched x m v_1) (hm : tGAT ≤ (x[m].time : Int))
    {X : Block V} (hXB : Block.Preceq X B.erase) (hTX : Block.Preceq T.erase X)
    {s : Slot} (hdeadline : (x[m].time : Int) + S.E.Δ < M.view_freeze S.E s)
    (hj : s + 1 ≤ (M.opening_slot S.hc (r + 1)) + 1)
    (hneTickW : ∀ w ∈ Restated.HonSlot M S Sched (s + 1), ∀ (n' : Nat) (t' : Int),
      Restated.tickStepAt M x n' t' → t' % S.E.Δ = 0 → w ∈ Sched.awake t' \ Sched.adv t' → t' < M.vote_time S.E (s + 1) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) w (Record.wakeStage M Sched t' x[n'] w) t' ⇢ out) :
    Restated.ConeAnchorChainInTree M S x X s :=
  Restated.coneAnchorChainInTree_mono facts S x hXB
    (Restated.coneAnchorChainInTree_of_holder_upTo facts (hcross := hcross) S Sched x tE hexec hmono htd hsync hmult
      tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr hinv hBv_1 hv_1 hm
      (preceq_trans_Preceq hTX hXB)
      (Restated.derive_height_le_of_anchor_preceq facts S Sched x hexec hinv
        (Restated.blockInLog_of_mem_bodies facts S Sched hv_1 hBv_1) (preceq_trans_Preceq hTX hXB))
      hdeadline hj hneTickW)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For every slot `s`, `slotStart s + 2Δ ≤ support_cutoff s`. -/
private theorem slotStart_add_two_delta_le_support_cutoff_holder (facts : Record.Facts M)
    (S : Setup V) (s : Slot) :
    slotStart S.E.Δ s + 2 * S.E.Δ ≤ M.support_cutoff S.E s := by
  have hd := S.E.Δ_pos
  have hvt := facts.sch.slotStart_add_delta_eq_vote_time S.E s
  have hp0 : slotStart S.E.Δ s ≤ M.proposal_time S.E s :=
    slotStart_le_of_le_slotOf S (facts.sch.Sts_proposal_time_nonneg S s)
      (le_of_eq (facts.sch.slotOf_proposal_time S.E s).symm)
  have hpv := facts.sch.proposal_time_lt_vote_time S.E s
  have hc0 : slotStart S.E.Δ s ≤ M.support_cutoff S.E s :=
    slotStart_le_of_le_slotOf S (le_of_lt (facts.sch.support_cutoff_pos S s))
      (le_of_eq (facts.sch.slotOf_support_cutoff S.E s).symm)
  have hcp := facts.sch.support_cutoff_ne_proposal_time S.E s
  have hcv := facts.sch.support_cutoff_ne_vote_time S.E s
  obtain ⟨a, ha⟩ := Int.dvd_of_emod_eq_zero (slotStart_emod_delta S s)
  obtain ⟨b, hb⟩ := Int.dvd_of_emod_eq_zero (facts.sch.proposal_time_emod_delta_inclX S.E s)
  obtain ⟨c, hc⟩ := Int.dvd_of_emod_eq_zero (facts.sch.support_cutoff_emod_delta S s)
  rw [ha, hb] at hp0
  rw [← hvt, ha, hb] at hpv
  rw [ha, hc] at hc0
  rw [hc, hb] at hcp
  rw [← hvt, hc, ha] at hcv
  rw [ha, hc]
  have hab : a ≤ b := le_of_mul_le_mul_left hp0 hd
  have hba : b < a + 1 :=
    lt_of_mul_lt_mul_left (by rw [mul_add, mul_one]; exact hpv) (le_of_lt hd)
  have hbeq : b = a := by omega
  subst hbeq
  have hac : b ≤ c := le_of_mul_le_mul_left hc0 hd
  have hc1 : c ≠ b := fun h => hcp (by rw [h])
  have hc2 : c ≠ b + 1 := fun h => hcv (by rw [h, mul_add, mul_one])
  have hc3 : b + 2 ≤ c := by omega
  nlinarith

/-- For every slot `s`, `support_cutoff s + Δ ≤ view_freeze s`. -/
private theorem support_cutoff_add_delta_le_view_freeze_holder (facts : Record.Facts M)
    (S : Setup V) (s : Slot) :
    M.support_cutoff S.E s + S.E.Δ ≤ M.view_freeze S.E s := by
  have hd := S.E.Δ_pos
  obtain ⟨k, hk⟩ := (facts.sch.publicTime_iff S (M.view_freeze S.E s)).mpr
    ⟨s, Or.inr (Or.inr (Or.inr rfl))⟩
  obtain ⟨c, hc⟩ := Int.dvd_of_emod_eq_zero (facts.sch.support_cutoff_emod_delta S s)
  have hlt := facts.sch.Sts_support_cutoff_lt_view_freeze S.E s
  rw [hk, hc] at hlt
  rw [hk, hc]
  have hck : c < (k : Int) := by
    by_contra hcon
    have h1 := mul_le_mul_of_nonneg_left (not_lt.mp hcon) (le_of_lt hd)
    rw [mul_comm] at h1
    linarith
  have hck1 : c + 1 ≤ (k : Int) := hck
  have h2 : S.E.Δ * (c + 1) ≤ S.E.Δ * (k : Int) :=
    mul_le_mul_of_nonneg_left hck1 (le_of_lt hd)
  rw [mul_add, mul_one] at h2
  rw [mul_comm (k : Int)]
  linarith

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If some outcome of an honest reader `q`'s slot-`s` confirmation eligibility test passes `H`, `X`
    is an ancestor of `H` and a descendant of `T`, slot `s` starts at or after `tGAT`, slot `s + 1`
    is at most one slot after round `r + 1`'s opening slot, and the ticks of `hneTickq` and
    `hneTickW` have outcomes, then every block strictly between an honest active reader's SG root
    and `X` is in that reader's slot-`(s + 1)` voter tree; synchrony is assumed up to `S.a (r + 1)`
    only. -/
theorem coneAnchorChainInTree_of_eligibleConfirmation_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    {r : Round} (hsync : Restated.SynchronyFromWakeBefore M S x ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    (hmult : AwakeAtMultiples S Sched)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE) (hcs : Restated.committeeSleepinessW M S Sched tE)
    {n : Nat} {T : NamedBlock V}
    (hr : Restated.switchRound M S tE ≤ r) (hinv : Restated.AfterPhaseInvariantOverActiveSetsTop M S Sched x r n T)
    (hcross : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepFinalizedCrossingUnderAnchor M S Sched x r n'' T)
    {s : Slot} {nq : Nat} {q : V} {H X : Block V}
    (hqaw : q ∈ Sched.awakeThroughout (slotStart S.E.Δ s - S.E.Δ)
      (M.confirmation_time S.E s))
    (hqh : HonestThroughTime Sched (M.confirmation_time S.E s) q)
    (el : Block V → Bool)
    (hel' : Restated.Vocabulary.Protocol.confEligible M S.E (x[nq][q].st).st.core s ⇢ el)
    (hel : el H = true)
    (hXH : Block.Preceq X H) (hTX : Block.Preceq T.erase X)
    (hlo : tGAT ≤ slotStart S.E.Δ s)
    (hj : s + 1 ≤ (M.opening_slot S.hc (r + 1)) + 1)
    (hneTickq : ∀ (n' : Nat) (t : Int), Restated.tickStepAt M x n' t → t % S.E.Δ = 0 → q ∈ Sched.awake t \ Sched.adv t →
      slotStart S.E.Δ s ≤ t → t ≤ M.confirmation_time S.E s →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) q (Record.wakeStage M Sched t x[n'] q) t ⇢ out)
    (hneTickW : ∀ w ∈ Restated.HonSlot M S Sched (s + 1), ∀ (n' : Nat) (t' : Int),
      Restated.tickStepAt M x n' t' → t' % S.E.Δ = 0 → w ∈ Sched.awake t' \ Sched.adv t' → t' < M.vote_time S.E (s + 1) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) w (Record.wakeStage M Sched t' x[n'] w) t' ⇢ out) :
    Restated.ConeAnchorChainInTree M S x X s := by
  obtain ⟨nc, Xn, hnc, hXn, hqnc, hHXn⟩ :=
    Restated.supporterHead_held_before_cut facts S Sched x htd hqaw hqh el hel' hel hneTickq
  have hd := S.E.Δ_pos
  have hncself := (Restated.tickStepAt_time facts x hnc).2
  have hsc : slotStart S.E.Δ s + 2 * S.E.Δ ≤ M.support_cutoff S.E s :=
    slotStart_add_two_delta_le_support_cutoff_holder facts S s
  have hvf : M.support_cutoff S.E s + S.E.Δ ≤ M.view_freeze S.E s :=
    support_cutoff_add_delta_le_view_freeze_holder facts S s
  exact Restated.coneAnchorChainInTree_of_heldDescendant_upTo facts S Sched x tE hexec hmono htd hsync hmult tGAT gap
    hgst hlen hcv hthird hphase hrsW hcs hr hinv hcross hXn hqnc (by linarith)
    (preceq_trans_Preceq hXH hHXn) hTX (by linarith) hj hneTickW

end

end DecoupledConsensusModel.Sts.Restated
