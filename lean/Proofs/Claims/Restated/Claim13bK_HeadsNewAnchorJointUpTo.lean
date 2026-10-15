import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bInvariantActive
import Proofs.Claims.Restated.Claim13bK_ConeAnchor
import Proofs.Claims.Restated.Claim13bK_ConeAnchorUpTo
import Proofs.Claims.Restated.Claim13bK_ConeChain
import Proofs.Claims.Restated.Claim13bK_ConeChainUpTo
import Proofs.Claims.Restated.Claim13bK_ConeSlotsUpTo
import Proofs.Claims.Restated.Claim13bK_ConfirmedOld
import Proofs.Claims.Restated.Claim13bK_ConfirmedOldUpTo
import Proofs.Claims.Restated.Claim13bK_FgJustified
import Proofs.Claims.Restated.Claim13bK_FinBeforeTick
import Proofs.Claims.Restated.Claim13bK_Frame
import Proofs.Claims.Restated.Claim13bK_FreshAttestersW
import Proofs.Claims.Restated.Claim13bK_GradeDescendantUpTo
import Proofs.Claims.Restated.Claim13bK_GradeOldHeads
import Proofs.Claims.Restated.Claim13bK_HeadsNewAnchorJoint
import Proofs.Claims.Restated.Claim13bK_HeadsNewAnchorUpTo
import Proofs.Claims.Restated.Claim13bK_HolderMarginsUpTo
import Proofs.Claims.Restated.Claim13bK_PrevHeadsStepUpTo
import Proofs.Claims.Restated.Claim13bPhaseSleepiness
import Proofs.Claims.Restated.Claim13bStepActionF
import Proofs.Claims.Restated.Claim13bStepAssembly
import Proofs.Claims.Restated.Claim13bStepConeIter
import Proofs.Claims.Restated.Claim13bStepFin
import Proofs.Claims.Restated.Claim13bStepKitConfirm
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bStepSGMove
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActive
import Model.Conditions.Claim13bInvariantActiveTop
import Model.Conditions.Claim13bK_ConeAnchor
import Model.Conditions.Claim13bK_ConeSlots
import Model.Conditions.Claim13bK_FgJustified
import Model.Conditions.Claim13bK_FinBeforeTick
import Model.Conditions.Claim13bK_FreshAttestersW
import Model.Conditions.Claim13bK_GradePairwise
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13bStepAnchor
import Model.Conditions.Claim13bStepAssembly
import Model.Conditions.Claim13bStepCone
import Model.Conditions.Claim13bStepConeIter
import Model.Conditions.Claim13bStepGrade
import Model.Conditions.Claim13bStepKitTick
import Model.Conditions.Claim13bStepSG
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedActionReads
import Proofs.Claims.Spec2Claims.Claim13bStepSGMove
import Model.Conditions.Claim13beRoute3_7
import Model.Conditions.ClaimAsyncK_DeliveryUpTo
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_Grades_Main
import Model.Record.Wiring

/-!
# Heads at the new anchor, with synchrony up to a bound

The theorems on the heads at round `(r + 1)`'s second and third slots and at the round-`(r + 1)`
anchor, with synchrony assumed only up to `S.a (r + 1)` or `S.a (r + 1) + Δ`.
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

/-- Synchrony from wake up to a bound `b'` gives it up to every bound `b ≤ b'`. -/
private theorem syncBefore_mono_jointU {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (Record.protocolOf M S) Sched} {b b' : Int} (hb : b ≤ b')
    (hs : Restated.SynchronyFromWakeBefore M S x b') : Restated.SynchronyFromWakeBefore M S x b :=
  fun k w sm hsend hle haw => hs k w sm hsend (le_trans hle hb) haw

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- With synchrony up to `S.a (r + 1)`: if `D` is an ancestor of `X`, and every block that a member
    of `HonRound S Sched r` names as confirmed in its round-`r` attestation, and holds right after
    the round-`r` tick, is compatible with `X`, then every block that a validator awake from `S.a r`
    to a round-`(r + 1)` phase's domain instant at or before `S.a (r + 1)`, and not held there, can
    grade at least 1 for round `r + 1` at the last step before that instant is compatible with `D`. -/
theorem graded_compatible_of_sgCompatible_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
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
    {D X : Block V} (hDX : Block.Preceq D X)
    (hX : ∀ v_1 ∈ Restated.HonRound M S Sched r, ∀ a : NamedAttestation V,
      a.round = r → a.val_index = v_1 →
      (⟨v_1, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n + 1].sent →
      ∀ C : NamedBlock V, C ∈ (x[n + 1][v_1].st).st.bodies → a.confirmed = some C.root →
      Block.compatible C.erase X = true) :
    ∀ v : V, v ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S r)) (M.domain S.E S.hc (r + 1) .g1) →
      v ∉ Sched.adv (M.domain S.E S.hc (r + 1) .g1) →
      ∀ m : Nat, Restated.stepBeforeInstant M x m (M.domain S.E S.hc (r + 1) .g1) →
      ∀ B : Block V,
        M.gradeBool S.E (M.gradeView (M.toHealing (x[m][v].st).st.core))
          (x[m][v].st).st.core.F S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) .g1)
          (M.late S.E S.hc (r + 1) .g1) B ⇢ true →
        Block.compatible B D = true := by
  intro v hawT hvS m hm B hB
  obtain ⟨v_1, hv_1, a, har, hai, has, C, hC, hac, hBC⟩ :=
    Restated.graded_preceq_freshSG_at_awakeReader_upTo facts (hcross := hcross) S Sched x tE hexec hmono htd hsync
      hmult tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr hinv
      (facts.gr.domain_le_action S (r + 1) .g1) hawT hvS hm B hB
  exact compatible_of_preceq_of_preceq hBC hDX (hX v_1 hv_1 a har hai has C hC hac)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- With synchrony up to `S.a (r + 1) + Δ`: if step `n''` is the tick step at `S.a (r + 2)`, `v_1`
    holds `Dn` among its bodies after `m` steps and is honest through `m`, the instant of `m` is at
    or after `tGAT` and strictly before `S.a (r + 1)`, every honest finalized block up to the
    instant `S.a (r + 2) − 1` is an ancestor of `Dn`, and every store's `h_max` up to step `n''` is
    at most one more than `Dn`'s chain-state height, then `ConeAnchorChainInTree` holds at `Dn` for
    the voters of round `(r + 1)`'s third slot. -/
theorem coneAnchorChainInTree_thirdSlot_ofHolder_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    {r : Round} (hsync : Restated.SynchronyFromWakeBefore M S x ((Restated.Vocabulary.Execution.Setup.a M S (r + 1)) + S.E.Δ))
    (hmult : AwakeAtMultiples S Sched)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hcs : Restated.committeeSleepinessW M S Sched tE)
    {n'' : Nat} (hn'' : Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1 + 1))))
    {Dn : NamedBlock V} {v_1 : V} {m : Nat} (hDv_1 : Dn ∈ (x[m][v_1].st).st.bodies)
    (hv_1 : Restated.HonestThrough M Sched x m v_1) (hm : tGAT ≤ (x[m].time : Int))
    (hmlt : (x[m].time : Int) < (Restated.Vocabulary.Execution.Setup.a M S (r + 1)))
    (hF : ∀ (v : V) (d : Nat), (x[d].time : Int) ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1 + 1)) - 1 →
      Restated.HonestThrough M Sched x d v → Block.Preceq (x[d][v].st).st.core.F Dn.erase)
    (hhmax : ∀ (v : V) (n₁ : Nat), n₁ ≤ n'' →
      (x[n₁][v].st).st.core.h_max ≤ (M.derive_named S.E S.cfg Dn).h + 1)
    (hneTickW : ∀ w ∈ Restated.HonSlot M S Sched ((M.opening_slot S.hc (r + 1)) + 1 + 1),
      ∀ (n' : Nat) (t' : Int),
      Restated.tickStepAt M x n' t' → t' % S.E.Δ = 0 → w ∈ Sched.awake t' \ Sched.adv t' → t' < M.vote_time S.E ((M.opening_slot S.hc (r + 1)) + 1 + 1) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) w (Record.wakeStage M Sched t' x[n'] w) t' ⇢ out) :
    Restated.ConeAnchorChainInTree M S x Dn.erase ((M.opening_slot S.hc (r + 1)) + 1) := by
  have hd := S.E.Δ_pos
  have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
  have hRd : 12 * S.E.Δ ≤ 4 * (S.hc.R : Int) * S.E.Δ := by nlinarith
  have hsucc := facts.gr.action_succ_eq_add_rounds S (r + 1)
  have hso : (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) = slotStart S.E.Δ ((M.opening_slot S.hc (r + 1))) + 6 * S.E.Δ := by
    rw [← Restated.confirmation_time_opening_slot facts S (r + 1)]; exact (facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E _).symm
  have hss1 : slotStart S.E.Δ ((M.opening_slot S.hc (r + 1)) + 1)
      = slotStart S.E.Δ ((M.opening_slot S.hc (r + 1))) + 4 * S.E.Δ := by
    exact slotStart_succ S.E.Δ _
  have hvf : M.view_freeze S.E ((M.opening_slot S.hc (r + 1)) + 1)
      = (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) + S.E.Δ :=
    (facts.sch.a_add_delta_eq_view_freeze S (r + 1)).symm
  have hvt : M.vote_time S.E ((M.opening_slot S.hc (r + 1)) + 1 + 1)
      = (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) - 5 * S.E.Δ + 4 * S.E.Δ * ((2 : Nat) : Int) :=
    Restated.vote_time_opening_slot_add facts S (r + 1) 2
  push_cast at hvt
  exact Restated.coneAnchorChainInTree_of_holder_of_bounds_upTo facts S Sched x hexec
    (syncBefore_mono_jointU hvf.le hsync) hmult htd hmono
    (tR := (Restated.Vocabulary.Execution.Setup.a M S (r + 1 + 1)) - 1) hgst hcv hphase hthird hcs (Restated.delta_le_of_healingLengthη facts S hlen)
    hDv_1 hv_1 hm hF
    (fun v d hd' => hhmax v d (Restated.le_tick_of_time_lt_action facts S Sched x hn'' hd'))
    (by rw [hvf]; linarith) (by rw [hvt]; linarith) hneTickW

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- With synchrony up to `S.a (r + 1)`: if round `r` is at or after the switch round, the invariant
    holds at round `r` with anchor `T`, step `n'` is the tick step at `S.a (r + 1)`, and
    `WakesAtActionInstants` holds, then every member of `HonSlot` of the slot after round
    `(r + 1)`'s opening slot votes there for a descendant of `T`. -/
theorem headsBelow_secondSlot_at_anchor_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    {r : Round} (hsync : Restated.SynchronyFromWakeBefore M S x ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    (hmult : AwakeAtMultiples S Sched)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
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
    (hjust : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepJustifiedRootUnderAnchor M S Sched x r n n'' T)
    (hw : Restated.WakesAtActionInstants M S Sched)
    {n' : Nat} (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1)))) :
    Restated.HeadsBelow M S Sched x T.erase ((M.opening_slot S.hc (r + 1)) + 1) := by
  have hd := S.E.Δ_pos
  have hd1 : (1 : Int) ≤ S.E.Δ := hd
  obtain ⟨t', ht'E, ht's, ht'len, hcs'⟩ :=
    Restated.exists_cone_cutoff facts S Sched tE hmono hcom tGAT gap hgst hlen hphase hcs hr
  have hcs2 := Restated.committeeSleepinessW_at_heads_slot facts S Sched tE hmono hcom tGAT gap hgst hlen hphase
    hcs hr
  have hfin := Restated.fin_old_anchor_before_succ_tick_of_hypotheses facts (hcross := hcross) S Sched x tE
    hexec hmono tGAT gap hgst hlen hthird hphase hrsW hr hinv hn'
  have hRs : (M.opening_slot S.hc r) + 2 ≤ (M.opening_slot S.hc (r + 1)) := by
    rw [facts.gr.opening_slot_succ]
    exact Nat.add_le_add_left (le_trans (by decide) S.hc.R_ge_three) _
  have hsR : M.support_cutoff S.E ((M.opening_slot S.hc (r + 1))) ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) - 1 := by
    have e1 := facts.sch.Sts_support_cutoff_lt_view_freeze S.E ((M.opening_slot S.hc (r + 1)))
    have e2 := facts.sch.view_freeze_lt_confirmation_time S.E ((M.opening_slot S.hc (r + 1)))
    rw [Restated.confirmation_time_opening_slot facts S (r + 1)] at e2
    have e1' := Int.add_one_le_of_lt e1
    have e2' := Int.add_one_le_of_lt e2
    linarith
  have hrange := Restated.headsBelow_range_afterPhase_upTo facts S Sched x hexec
    (syncBefore_mono_jointU (by linarith) hsync) hmult htd
    hmono hgst hcv
    (fun t h1 h2 => hphase t h1 (le_trans h2 ht'E))
    (fun t h => hthird t (le_trans h ht'E)) hcs' ht'len
    (Restated.deliveredDescendantUnderFinalized_anchor facts S Sched x hn' hfin tGAT)
    (Restated.finalizedPreceqAtSteps_anchor facts S Sched x hn' hfin tGAT)
    (s₀ := (M.opening_slot S.hc r) + 2) (s₁ := (M.opening_slot S.hc (r + 1)))
    (Nat.succ_pos _) ht's hsR
    (fun s h0 h1 => Restated.coneAnchorCompatible_range_at_anchor_upTo facts (hcross := hcross) (hjust := hjust) S
      Sched x tE hexec hmono htd hsync hmult tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr
      hinv hw (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›)
      (by intro v hv; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono hinv.tick (Restated.action_emod_delta facts S _) (Finset.mem_sdiff.2 ⟨mem_awake_of_awakeThroughout Sched (show v ∈ Sched.awakeThroughout (M.a S.hc S.E.Δ _ - wAttest S) (M.a S.hc S.E.Δ _) from (Finset.mem_sdiff.1 hv).1) (by linarith [twelve_delta_le_wAttest S, S.E.Δ_pos]) (le_refl _), (Finset.mem_sdiff.1 hv).2⟩)) s h0 h1)
    (fun s h0 h1 => Restated.coneAnchorChainInTree_at_anchor_of_committee_upTo facts (hcross := hcross) S Sched x tE
      hexec hmono htd hsync hmult tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr hinv hcs2
      (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›) s h0 h1)
    hinv.heads
    (by intro s _ _ m hm q hq; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono hm (facts.sch.vote_time_emod_delta S _) (Finset.mem_sdiff.2 ⟨Restated.awake_of_mem_HonSlot facts S Sched _ hq, fun h => ((Restated.mem_HonSlot facts).mp hq).2.2 (hmono _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E s) h)⟩))
    (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›)
  exact hrange _ (Nat.le_succ_of_le hRs) le_rfl

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- With synchrony up to `S.a (r + 1) + Δ`: if round `r` is at or after the switch round, every
    honest finalized block up to the instant `S.a (r + 2) − 1` is an ancestor of `Dn`, so is every
    block an honest validator justifies with `h_max = h_j + 1` from the tick step at `S.a r` on up
    to that instant, every store's `h_max` up to the tick step at `S.a (r + 2)` is at most one more
    than `Dn`'s chain-state height, an honest validator holds `Dn` at an instant in
    `[tGAT, S.a (r + 1))`, every block a validator awake from `S.a r` to round `(r + 1)`'s grade-1
    domain instant can grade at least 1 for round `r + 1` is compatible with `Dn`, and `HeadsBelow`
    holds for `Dn` at round `(r + 1)`'s second slot, then it holds for `Dn` at the third slot. -/
theorem headsBelow_thirdSlot_of_anchorFacts_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    {r : Round} (hsync : Restated.SynchronyFromWakeBefore M S x ((Restated.Vocabulary.Execution.Setup.a M S (r + 1)) + S.E.Δ))
    (hmult : AwakeAtMultiples S Sched)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hcs : Restated.committeeSleepinessW M S Sched tE)
    (hw : Restated.WakesAtActionInstants M S Sched)
    {n n'' : Nat} (hr : Restated.switchRound M S tE ≤ r)
    (hn : Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S r))) (hn'' : Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1 + 1))))
    {Dn : NamedBlock V}
    (hF : ∀ (v : V) (d : Nat), (x[d].time : Int) ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1 + 1)) - 1 →
      Restated.HonestThrough M Sched x d v → Block.Preceq (x[d][v].st).st.core.F Dn.erase)
    (hJ : ∀ (v : V) (d : Nat), n + 1 ≤ d → (x[d].time : Int) ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1 + 1)) - 1 →
      Restated.HonestThrough M Sched x d v →
      (x[d][v].st).st.core.h_max = (x[d][v].st).st.core.h_j + 1 →
      Block.Preceq (x[d][v].st).st.core.J Dn.erase)
    (hhmax : ∀ (v : V) (n₁ : Nat), n₁ ≤ n'' →
      (x[n₁][v].st).st.core.h_max ≤ (M.derive_named S.E S.cfg Dn).h + 1)
    {v_1 : V} {m : Nat} (hDv_1 : Dn ∈ (x[m][v_1].st).st.bodies)
    (hv_1 : Restated.HonestThrough M Sched x m v_1) (hm : tGAT ≤ (x[m].time : Int))
    (hmlt : (x[m].time : Int) < (Restated.Vocabulary.Execution.Setup.a M S (r + 1)))
    (hgc : ∀ v : V, v ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S r)) (M.domain S.E S.hc (r + 1) .g1) →
      v ∉ Sched.adv (M.domain S.E S.hc (r + 1) .g1) →
      ∀ m : Nat, Restated.stepBeforeInstant M x m (M.domain S.E S.hc (r + 1) .g1) →
      ∀ B : Block V,
        M.gradeBool S.E (M.gradeView (M.toHealing (x[m][v].st).st.core))
          (x[m][v].st).st.core.F S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) .g1)
          (M.late S.E S.hc (r + 1) .g1) B ⇢ true →
        Block.compatible B Dn.erase = true)
    (hprev : Restated.HeadsBelow M S Sched x Dn.erase ((M.opening_slot S.hc (r + 1)) + 1)) :
    Restated.HeadsBelow M S Sched x Dn.erase ((M.opening_slot S.hc (r + 1)) + 2) := by
  have hd := S.E.Δ_pos
  have hd1 : (1 : Int) ≤ S.E.Δ := hd
  have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
  have hRd : 12 * S.E.Δ ≤ 4 * (S.hc.R : Int) * S.E.Δ := by nlinarith
  have hsucc := facts.gr.action_succ_eq_add_rounds S r
  have hsucc1 := facts.gr.action_succ_eq_add_rounds S (r + 1)
  obtain ⟨t', ht'E, ht's, ht'len, hcs'⟩ :=
    Restated.exists_cone_cutoff facts S Sched tE hmono hcom tGAT gap hgst hlen hphase hcs hr
  have hRs : (M.opening_slot S.hc r) + 2 ≤ (M.opening_slot S.hc (r + 1)) + 1 := by
    rw [facts.gr.opening_slot_succ]
    exact Nat.le_succ_of_le (Nat.add_le_add_left (le_trans (by decide) S.hc.R_ge_three) _)
  have hso : (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) = slotStart S.E.Δ ((M.opening_slot S.hc (r + 1))) + 6 * S.E.Δ := by
    rw [← Restated.confirmation_time_opening_slot facts S (r + 1)]; exact (facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E _).symm
  have hss1 : slotStart S.E.Δ ((M.opening_slot S.hc (r + 1)) + 1)
      = slotStart S.E.Δ ((M.opening_slot S.hc (r + 1))) + 4 * S.E.Δ := by
    exact slotStart_succ S.E.Δ _
  have hsc1 : M.support_cutoff S.E ((M.opening_slot S.hc (r + 1)) + 1)
      = Restated.Vocabulary.Execution.Setup.a M S (r + 1) := by
    rw [← facts.sch.confirmation_time_eq_support_cutoff_succ,
      Restated.confirmation_time_opening_slot facts S (r + 1)]
  have hsR : M.support_cutoff S.E ((M.opening_slot S.hc (r + 1)) + 1)
      ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1 + 1)) - 1 := by
    rw [hsc1]; linarith
  have hvt : M.vote_time S.E ((M.opening_slot S.hc (r + 1)) + 1 + 1)
      = (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) - 5 * S.E.Δ + 4 * S.E.Δ * ((2 : Nat) : Int) :=
    Restated.vote_time_opening_slot_add facts S (r + 1) 2
  push_cast at hvt
  have hAB : Restated.ConeAnchorCompatible M S x Dn.erase ((M.opening_slot S.hc (r + 1)) + 1) :=
    Restated.coneAnchorCompatible_of_voteReads facts S x
      (Restated.voteGradeOneCompatible_of_gradedCompatible facts S Sched x hmono hw hgc (j := 2)
        (by have := S.hc.R_ge_three; omega) rfl)
      (Restated.voteFinJustCompatible_before_succ_succ_tick facts S Sched x hmono hn hF hJ
        (by rw [hvt]; linarith) (by rw [hvt]; linarith))
  have hpath := Restated.coneAnchorChainInTree_thirdSlot_ofHolder_upTo facts S Sched x tE hexec hmono htd hsync hmult
    tGAT gap hgst hlen hcv hthird hphase hcs hn'' hDv_1 hv_1 hm hmlt hF hhmax
    (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›)
  have hrange := Restated.headsBelow_range_afterPhase_upTo facts S Sched x hexec
    (syncBefore_mono_jointU (by rw [hsc1]; linarith) hsync)
    hmult htd hmono hgst hcv
    (fun t h1 h2 => hphase t h1 (le_trans h2 ht'E))
    (fun t h => hthird t (le_trans h ht'E)) hcs' ht'len
    (Restated.deliveredDescendant_before_succ_succ_tick facts S Sched x hF tGAT)
    (Restated.finalizedPreceqAtSteps_before_succ_succ_tick facts S Sched x hF tGAT)
    (s₀ := (M.opening_slot S.hc (r + 1)) + 1) (s₁ := (M.opening_slot S.hc (r + 1)) + 1)
    (Nat.succ_pos _) (le_trans ht's (slotStart_mono S hRs)) hsR
    (fun s h0 h1 => by
      have hs : s = (M.opening_slot S.hc (r + 1)) + 1 := le_antisymm h1 h0
      rw [hs]; exact hAB)
    (fun s h0 h1 => by
      have hs : s = (M.opening_slot S.hc (r + 1)) + 1 := le_antisymm h1 h0
      rw [hs]; exact hpath)
    hprev
    (by intro s _ _ m hm q hq; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono hm (facts.sch.vote_time_emod_delta S _) (Finset.mem_sdiff.2 ⟨Restated.awake_of_mem_HonSlot facts S Sched _ hq, fun h => ((Restated.mem_HonSlot facts).mp hq).2.2 (hmono _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E s) h)⟩))
    (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›)
  exact hrange _ (Nat.le_succ _) le_rfl

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Stamping a store's clock does not change the outcomes of the confirmation eligibility test for
    slot `s`. -/
private theorem confEligible_setClock_jointU (facts : Record.Facts M) (E : Env V) (st : M.NS)
    (t : Int) (s : Slot) :
    Restated.Vocabulary.Protocol.confEligible M E (M.ns_setClock E st t).core s
      = Restated.Vocabulary.Protocol.confEligible M E st.core s := by
  have htau : (M.ns_setClock E st t).core.tau = st.core.tau :=
    facts.sto.tau_eq_of_fields (facts.hd.Sts_setClock_core_T E st t)
      (facts.hd.setClock_core_timestamp_block E st t) (facts.hd.setClock_core_timestamp_vote E st t)
  have hpool : (M.ns_setClock E st t).core.pool s = st.core.pool s :=
    facts.hd.Sts_setClock_core_pool E st t s
  unfold Restated.Vocabulary.Protocol.confEligible
    Restated.Vocabulary.Protocol.confCount Restated.Vocabulary.Protocol.confVotes
    Restated.Vocabulary.Protocol.confEarly Restated.Vocabulary.Protocol.confLate
  rw [htau, hpool, facts.hd.setClock_core_timestamp_vote, facts.hd.Sts_setClock_core_T]

open scoped DC in
/-- If `m` can return `a`, then `f <$> m` can return `f a`. -/
private theorem returns_map_intro_jointU {α β : Type} (f : α → β) (m : DC.NDRE α) (a : α)
    (h : m ⇢ a) : (f <$> m) ⇢ f a := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image]
  exact ⟨_, h, rfl⟩

open scoped DC in
/-- `m >>= k` can return `b` exactly when `m` can return some `a` from which `k a` can return `b`. -/
private theorem returns_bind_iff_jointU {α β : Type} (m : DC.NDRE α) (k : α → DC.NDRE β) (b : β) :
    (m >>= k) ⇢ b ↔ ∃ a, m ⇢ a ∧ k a ⇢ b := by
  unfold Record.Returns
  simp only [ExceptT.run_bind, Set.bind_def]
  constructor
  · intro h
    obtain ⟨e, he, hb⟩ := Set.mem_iUnion₂.mp h
    cases e with
    | ok a => exact ⟨a, he, hb⟩
    | error err => simp at hb
  · rintro ⟨a, ha, hb⟩
    exact Set.mem_iUnion₂.mpr ⟨_, ha, hb⟩

open scoped DC in
/-- The lift of the set `s` can return `a` exactly when `a ∈ s`. -/
private theorem returns_lift_iff_jointU {α : Type} (s : Set α) (a : α) :
    (ExceptT.lift s : DC.NDRE α) ⇢ a ↔ a ∈ s := by
  unfold Record.Returns
  simp only [ExceptT.run_lift, Set.fmap_eq_image, Set.mem_image]
  constructor
  · rintro ⟨a', ha', he⟩
    cases he
    exact ha'
  · intro h
    exact ⟨a, h, rfl⟩

/-- At every node state `n`, `actionFGSource` can return some value. -/
private theorem actionFGSource_nonempty_jointU (facts : Record.Facts M) (S : Setup V)
    (n : M.N) : ∃ o, Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n ⇢ o := by
  obtain ⟨A2, hA2⟩ := facts.dt.grade2_block_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s)
  obtain ⟨o, ho⟩ := facts.dt.fg_source_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s) A2
  exact ⟨o, (returns_bind_iff_jointU _ _ _).2 ⟨A2, hA2, ho⟩⟩

/-- For every store `hs` the round-`r₁` action can give from `before`, `hs.live_confirmed` either
    passes some outcome of the confirmation eligibility test of `before`'s store for the slot before
    the action instant's, or is the `confRoot` of `before`'s store with its clock set to the action
    instant. -/
private theorem actionHealingStore_live_confirmed_cases_jointU (facts : Record.Facts M)
    (S : Setup V) (before : M.N) (r₁ : Round) (hs : M.HS)
    (hhs : hs ∈ Restated.actionHealingStore M S before r₁) :
    (∃ el : Block V → Bool, Restated.Vocabulary.Protocol.confEligible M S.E before.st.core
        (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r₁) - 1) ⇢ el ∧
        el hs.live_confirmed = true) ∨
      hs.live_confirmed
        = Restated.Vocabulary.Protocol.confRoot M
            (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core := by
  classical
  obtain ⟨c, hc, X, hX, st₀, hst₀, rfl⟩ := Restated.actionHealingStore_eq facts S before r₁ hs hhs
  obtain ⟨hF₀, hJ₀, hhj₀, hhm₀, hlc₀, hT₀, hs₀, hσ₀⟩ :=
    Restated.HS_fields_store_with_cache facts c hst₀
  simp only [hF₀, hJ₀, hhj₀, hhm₀, hlc₀, hT₀, hs₀, hσ₀] at *
  rw [Record.Model.HS.live_confirmed, facts.sto.toHealing_live_confirmed]
  by_cases hroot : X.live_confirmed = Restated.Vocabulary.Protocol.confRoot M
      (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core
  · exact Or.inr hroot
  · left
    obtain ⟨tm, htm⟩ := facts.sto.tau_nonempty
      (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core
    obtain ⟨R, hR⟩ := facts.fc.get_sg_root_with_nonempty (M.gradeContract c) S.E S.hc
      (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core.toHealing
      (M.round_of S.hc
        (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core.s)
    obtain ⟨score, hscore⟩ : ∃ score : Block V → ℕ, ∀ B, M.goldfish_score S.E
        (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core.T
        ((beforeCutoff tm (M.support_cutoff S.E (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r₁) - 1))
          ((M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core.pool
            (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r₁) - 1))).filter
          (fun u => M.no_second_vote_in (Restated.Vocabulary.Protocol.confLate M S.E
            (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core
            (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r₁) - 1)) u = true))
        ((beforeCutoff tm (M.support_cutoff S.E (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r₁) - 1))
          ((M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core.pool
            (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r₁) - 1))).filter
          (fun u => M.no_second_vote_in (Restated.Vocabulary.Protocol.confLate M S.E
            (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core
            (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r₁) - 1)) u = true))
        (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r₁) - 1) B ⇢ score B :=
      ⟨fun B => (facts.fc.goldfish_score_nonempty _ _ _ _ _ B).choose,
        fun B => (facts.fc.goldfish_score_nonempty _ _ _ _ _ B).choose_spec⟩
    obtain ⟨W, hW⟩ := facts.fc.ghost_nonempty R
      (M.get_filtered_block_tree
        (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core.toHealing.toFG)
      score
      (fun B => decide (Restated.Vocabulary.Protocol.confCount M S.E
        (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core
        (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r₁) - 1) < 2 * score B))
    have hwalk := facts.hd.update_confirmation_with_live_confirmed_walk_or_fgRoot
      (M.gradeContract c) S.E S.hc
      (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core
      (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r₁) - 1) tm htm R hR score hscore W hW X hX
    have hgen := facts.hd.update_confirmation_with_live_confirmed_genuine_or_fgRoot
      (M.gradeContract c) S.E S.hc
      (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core
      (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r₁) - 1) tm htm R hR score hscore W hW X hX
    rcases hwalk with hwalk | hfg
    · rcases hgen with ⟨-, -, hel⟩ | hfg
      · refine ⟨fun B => decide (Restated.Vocabulary.Protocol.confCount M S.E
          (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r₁)).core
          (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r₁) - 1) < 2 * score B), ?_, ?_⟩
        · rw [← confEligible_setClock_jointU facts S.E before.st
            (Restated.Vocabulary.Execution.Setup.a M S r₁)]
          refine (returns_bind_iff_jointU _ _ _).2 ⟨_, returns_map_intro_jointU _ _ _
            (returns_map_intro_jointU _ _ _ htm), ?_⟩
          refine (returns_bind_iff_jointU _ _ _).2 ⟨score, (returns_lift_iff_jointU _ _).2 hscore, ?_⟩
          exact (Record.returns_pure _ _).2 rfl
        · rw [hwalk]
          exact hel
      · exact absurd hfg hroot
    · exact absurd hfg hroot

/-- With synchrony up to `S.a (r + 1) + Δ`: for every choice `att` of the round-`(r + 1)` action
    attestations, with `T'` the anchor `newAnchor` gives along `att`, if round `r` is at or after
    the switch round, the invariant holds at round `r` with tick step `n` and anchor `T`, `T ⪯ T'`,
    no honest height vote signed up to step `n' + 1` names a height greater than `T'`'s, every
    honest justified block from step `n_W` to `n'' + 1` is an ancestor of `T'`, and the round-`r` SG
    blocks of the members of `HonRound S Sched r` are ancestors of the heads at round `(r + 1)`'s
    opening slot and compatible with the confirmed blocks of the members of
    `HonRound S Sched (r + 1)`, then every member of `HonSlot` of round `(r + 1)`'s third slot votes
    there for a descendant of `T'`. -/
theorem headsAtNewAnchor_of_joint_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    {r : Round} (hsync : Restated.SynchronyFromWakeBefore M S x ((Restated.Vocabulary.Execution.Setup.a M S (r + 1)) + S.E.Δ))
    (hmult : AwakeAtMultiples S Sched)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE) (hcs : Restated.committeeSleepinessW M S Sched tE)
    (hw : Restated.WakesAtActionInstants M S Sched)
    {n n' n'' n_W : Nat} {T : NamedBlock V}
    (hr : Restated.switchRound M S tE ≤ r) (hinv : Restated.AfterPhaseInvariantOverActiveSetsTop M S Sched x r n T)
    (hcross : ∀ n₀ : Nat, Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepFinalizedCrossingUnderAnchor M S Sched x r n₀ T)
    (hjust : ∀ n₀ : Nat, Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepJustifiedRootUnderAnchor M S Sched x r n n₀ T)
    (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1)))) (hn'' : Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1 + 1))))
    {att : V → NamedAttestation V} (hatt : Restated.ActionAttestationsOf M S Sched x r n' att)
    (hTT' : Block.Preceq T.erase (Restated.newAnchor M S Sched x r n' att T).erase)
    (hceil' : ∀ (v : V) (n₂ : Nat) (a : NamedAttestation V) (h' : Height)
      (entry : BlockId) (tmo : Bool),
      n₂ ≤ n' + 1 → Restated.HonestThrough M Sched x n₂ v → a.val_index = v →
      (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n₂].sent →
      a.height_pair = NamedHeightPair.vote h' entry tmo →
      h' ≤ (M.derive_named S.E S.cfg (Restated.newAnchor M S Sched x r n' att T)).h)
    (hJ' : ∀ (v : V) (n₁ : Nat), n_W ≤ n₁ → n₁ ≤ n'' + 1 → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J (Restated.newAnchor M S Sched x r n' att T).erase)
    (hP : ∀ v_1 ∈ Restated.HonRound M S Sched r, ∀ a : NamedAttestation V,
      a.round = r → a.val_index = v_1 →
      (⟨v_1, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n + 1].sent →
      ∀ C : NamedBlock V, C ∈ (x[n + 1][v_1].st).st.bodies → a.confirmed = some C.root →
      Restated.HeadsBelow M S Sched x C.erase ((M.opening_slot S.hc (r + 1))))
    (hQ : Restated.ConfirmedCompatibleFreshSGOverHonRound M S Sched x r n n') :
    Restated.HeadsBelow M S Sched x (Restated.newAnchor M S Sched x r n' att T).erase ((M.opening_slot S.hc (r + 1)) + 2) := by
  classical
  have hd := S.E.Δ_pos
  have hd1 : (1 : Int) ≤ S.E.Δ := hd
  have hsync1 : Restated.SynchronyFromWakeBefore M S x ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) :=
    syncBefore_mono_jointU (by linarith) hsync
  have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
  have hRd : 12 * S.E.Δ ≤ 4 * (S.hc.R : Int) * S.E.Δ := by nlinarith
  have hsucc := facts.gr.action_succ_eq_add_rounds S r
  have hsucc1 := facts.gr.action_succ_eq_add_rounds S (r + 1)
  have hn := hinv.tick
  obtain ⟨hn1, -⟩ := Restated.tickStepAt_time facts x hn
  obtain ⟨hn'1, hn'0⟩ := Restated.tickStepAt_time facts x hn'
  have hnn' : n + 1 ≤ n' := Restated.tick_succ_le_tick_succ_round facts S Sched x hn hn'
  have hnWn : n_W ≤ n := Restated.tick_le_of_round_le facts S Sched x hnW hn hr
  have hnWn' : n_W ≤ n' := by omega
  have hopen : M.opening S.E S.hc r ≤ Restated.Vocabulary.Execution.Setup.a M S r := by
    show _ ≤ M.a S.hc S.E.Δ r
    rw [facts.gr.opening_eq_proposal_time, facts.sch.a_eq_confirmation_time]
    exact facts.sch.proposal_time_le_confirmation_time _ _
  have htGAT : tGAT ≤ (Restated.Vocabulary.Execution.Setup.a M S r) :=
    le_trans (Restated.tGAT_le_switchOpening facts S tGAT tE gap hgst hlen)
      (le_trans (Restated.switchOpening_le_opening facts S hr) hopen)
  have hso : (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) = slotStart S.E.Δ ((M.opening_slot S.hc (r + 1))) + 6 * S.E.Δ := by
    rw [← Restated.confirmation_time_opening_slot facts S (r + 1)]; exact (facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E _).symm
  have hlo : tGAT ≤ slotStart S.E.Δ ((M.opening_slot S.hc (r + 1))) := by linarith
  have hRs : (M.opening_slot S.hc r) + 2 ≤ (M.opening_slot S.hc (r + 1)) := by
    rw [facts.gr.opening_slot_succ]
    exact Nat.add_le_add_left (le_trans (by decide) S.hc.R_ge_three) _
  obtain ⟨t', ht'E, ht's, ht'len, hcs'⟩ :=
    Restated.exists_cone_cutoff facts S Sched tE hmono hcom tGAT gap hgst hlen hphase hcs hr
  have hcs2 := Restated.committeeSleepinessW_at_heads_slot facts S Sched tE hmono hcom tGAT gap hgst hlen hphase
    hcs hr
  have hsE : t' ≤ slotStart S.E.Δ ((M.opening_slot S.hc (r + 1))) :=
    le_trans ht's (slotStart_mono S hRs)
  have hfinT := Restated.fin_old_anchor_before_succ_tick_of_hypotheses facts (hcross := hcross) S Sched x tE
    hexec hmono tGAT gap hgst hlen hthird hphase hrsW hr hinv hn'
  have hjustT := Restated.justified_old_anchor_before_succ_tick_of_hypotheses facts (hjust := hjust) S Sched x tE
    hexec hmono tGAT gap hgst hlen hthird hphase hrsW hr hinv hn'
  have hprevT := Restated.headsBelow_secondSlot_at_anchor_upTo facts S Sched x tE hexec hmono htd hsync1 hmult hcom
    tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr hinv hcross hjust hw hn'
  obtain ⟨T', hT'⟩ : ∃ T' : NamedBlock V, T' = Restated.newAnchor M S Sched x r n' att T := ⟨_, rfl⟩
  rw [← hT'] at hTT' hceil' hJ' ⊢
  have hF' := Restated.fin_preceq_before_succ_succ_tick facts S Sched x hn'' hnWn' hfinT hTT' hJ'
  have hJ'' := Restated.just_preceq_before_succ_succ_tick facts S Sched x hn'' hnWn' hjustT hTT' hJ'
  have hhmax' := Restated.hMax_le_anchor_succ_before_succ_tick_ofCeiling facts S Sched x hexec hmono
    (tE := Restated.switchOpening M S tE)
    (Restated.roundSleepinessW_switchOpening_of_phase facts S Sched tGAT tE gap hgst hlen hmono hthird hphase
      hrsW)
    hn' hceil' hn''
    (Restated.switchOpening_le_opening facts S (le_trans hr (Nat.le_add_right r 2)))
  have hvt1 : M.vote_time S.E ((M.opening_slot S.hc (r + 1)) + 1)
      = (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) - 5 * S.E.Δ + 4 * S.E.Δ * ((1 : Nat) : Int) :=
    Restated.vote_time_opening_slot_add facts S (r + 1) 1
  push_cast at hvt1
  have hFJ0 : Restated.VoteFinJustCompatible M S x T'.erase ((M.opening_slot S.hc (r + 1))) :=
    Restated.voteFinJustCompatible_before_succ_succ_tick facts S Sched x hmono hn hF' hJ''
      (by rw [hvt1]; linarith) (by rw [hvt1]; linarith)
  by_cases hex : ∃ C : NamedBlock V, Restated.NewAnchorSpec M S Sched x r n' att T C
  · -- the anchor moved to a block `NewAnchorSpec` describes
    have hchoice : T' = hex.choose := by
      rw [hT']
      show (if h : ∃ C : NamedBlock V, Restated.NewAnchorSpec M S Sched x r n' att T C then h.choose
        else T) = hex.choose
      rw [dif_pos hex]
    obtain ⟨q, hqW, hmem, h₀, tmo, hvote⟩ := hex.choose_spec.2.2.2
    rw [← hchoice] at hmem hvote
    have hq : q ∈ Restated.freshAttesters M S Sched x (r + 1) (n' + 1) :=
      Restated.freshAttestersW_subset_freshAttesters facts S Sched x (r + 1) (n' + 1) hqW
    obtain ⟨nr, hnr, ns, rec, hD⟩ := hatt q hqW
    obtain ⟨o, ho⟩ := actionFGSource_nonempty_jointU facts (Setup.alwaysAwake S) nr
    obtain ⟨Cfg, rfl, hpre⟩ :=
      Restated.entry_preceq_source facts S Sched x hexec hn' hq hmem rfl nr hnr
        (ns, rec, att q) hD hvote o ho
    have hCfg := ho
    have hhsq : M.toHealing nr.st.core ∈ Restated.actionHealingStore M S (x[n'][q].st) (r + 1) :=
      ⟨nr, hnr, rfl⟩
    have qH : q ∈ Restated.HonRound M S Sched (r + 1) :=
      Restated.freshAttestersW_subset_honRound facts S Sched x (le_of_eq hn'1.symm) hqW
    have hqn' : Restated.HonestThrough M Sched x n' q := fun t ht =>
      Restated.honestThrough_of_mem_freshAttestersW facts hqW t
        (le_trans ht (Restated.time_mono_int facts S Sched x (Nat.le_succ n')))
    have hqm : tGAT ≤ (x[n'].time : Int) := by linarith
    have hqlt : (x[n'].time : Int) < (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) := by linarith
    have hfinish : ∀ X : Block V, Block.Preceq T'.erase X →
        (∀ v_1 ∈ Restated.HonRound M S Sched r, ∀ a : NamedAttestation V,
          a.round = r → a.val_index = v_1 →
          (⟨v_1, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n + 1].sent →
          ∀ C : NamedBlock V, C ∈ (x[n + 1][v_1].st).st.bodies → a.confirmed = some C.root →
          Block.compatible C.erase X = true) →
        Restated.HeadsBelow M S Sched x T'.erase ((M.opening_slot S.hc (r + 1)) + 1) →
        Restated.HeadsBelow M S Sched x T'.erase ((M.opening_slot S.hc (r + 1)) + 2) := fun X hDX hX h1 =>
      Restated.headsBelow_thirdSlot_of_anchorFacts_upTo facts S Sched x tE hexec hmono htd hsync hmult hcom tGAT gap
        hgst hlen hcv hthird hphase hcs hw hr hn hn'' hF' hJ'' hhmax' hmem hqn' hqm hqlt
        (Restated.graded_compatible_of_sgCompatible_upTo facts (hcross := hcross) S Sched x tE hexec hmono htd hsync1
          hmult tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr hinv hDX hX)
        h1
    have hAB0 : ∀ X : Block V, Block.Preceq T'.erase X →
        (∀ v_1 ∈ Restated.HonRound M S Sched r, ∀ a : NamedAttestation V,
          a.round = r → a.val_index = v_1 →
          (⟨v_1, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n + 1].sent →
          ∀ C : NamedBlock V, C ∈ (x[n + 1][v_1].st).st.bodies → a.confirmed = some C.root →
          Block.compatible C.erase X = true) →
        Restated.ConeAnchorCompatible M S x T'.erase ((M.opening_slot S.hc (r + 1))) := fun X hDX hX =>
      Restated.coneAnchorCompatible_of_voteReads facts S x
        (Restated.voteGradeOneCompatible_of_gradedCompatible facts S Sched x hmono hw
          (Restated.graded_compatible_of_sgCompatible_upTo facts (hcross := hcross) S Sched x tE hexec hmono htd
            hsync1 hmult tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr hinv hDX hX)
          (j := 1) (by have := S.hc.R_ge_three; omega) rfl)
        hFJ0
    rcases Restated.source_cases facts S (x[n'][q].st) (r + 1) nr hnr Cfg hCfg with hlc | hQ2
    · -- the confirmation branch
      have hDX : Block.Preceq T'.erase (M.toHealing nr.st.core).live_confirmed :=
        preceq_trans_Preceq hpre hlc
      have hX : ∀ v_1 ∈ Restated.HonRound M S Sched r, ∀ a : NamedAttestation V,
          a.round = r → a.val_index = v_1 →
          (⟨v_1, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n + 1].sent →
          ∀ C : NamedBlock V, C ∈ (x[n + 1][v_1].st).st.bodies → a.confirmed = some C.root →
          Block.compatible C.erase (M.toHealing nr.st.core).live_confirmed = true :=
        fun v_1 hv_1 a har hai has C hC hac => hQ q qH v_1 hv_1 a har hai has C hC hac _ hhsq
      have hFq : Block.Preceq (M.toHealing nr.st.core).F T.erase := by
        rw [Restated.actionHealingStore_F facts S _ _ _ hhsq]; exact hfinT q n' le_rfl hqn'
      have hJq : (M.toHealing nr.st.core).h_max = (M.toHealing nr.st.core).h_j + 1 →
          Block.Preceq (M.toHealing nr.st.core).J T.erase := by
        intro hroot
        rw [Restated.actionHealingStore_h_max facts S _ _ _ hhsq,
          Restated.actionHealingStore_h_j facts S _ _ _ hhsq] at hroot
        rw [Restated.actionHealingStore_J facts S _ _ _ hhsq]
        exact hjustT q n' hnn' le_rfl hqn' hroot
      have hrootq := Restated.confRoot_setClock_preceq_ofAction facts S (x[n'][q].st) r _ hhsq hFq hJq
      have hct : M.confirmation_time S.E ((M.opening_slot S.hc (r + 1))) = (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) :=
        Restated.confirmation_time_opening_slot facts S (r + 1)
      have hn'c : Restated.tickStepAt M x n'
          (M.confirmation_time S.E ((M.opening_slot S.hc (r + 1)))) := by
        rw [hct]; exact hn'
      have hqaw := Restated.honRound_awakeThroughout_confirmation facts S Sched (r + 1) qH
      have hqA : q ∉ Sched.adv ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) := (Finset.mem_sdiff.1 qH).2
      have hqh : HonestThroughTime Sched
          (M.confirmation_time S.E ((M.opening_slot S.hc (r + 1)))) q :=
        fun t'' ht'' hin => hqA (hmono _ _ (by rw [← hct]; exact ht'') hin)
      have hpath0 : Restated.ConeAnchorChainInTree M S x T'.erase ((M.opening_slot S.hc (r + 1))) := by
        rcases actionHealingStore_live_confirmed_cases_jointU facts S (x[n'][q].st) (r + 1) _ hhsq with
          ⟨el, hel', hel⟩ | hlcR
        · rw [Restated.slotOf_a_sub_one facts S (r + 1)] at hel'
          exact Restated.coneAnchorChainInTree_of_eligibleConfirmation_upTo facts S Sched x tE hexec hmono htd hsync1
            hmult tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr hinv hcross hqaw hqh el hel' hel hDX
            hTT' hlo le_rfl (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›) (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›)
        · have hlc2 : Block.Preceq T'.erase (Restated.Vocabulary.Protocol.confRoot M
              (M.ns_setClock S.E (x[n'][q].st).st
                (M.confirmation_time S.E ((M.opening_slot S.hc (r + 1))))).core) := by
            rw [hct, ← hlcR]; exact hDX
          have heq : T'.erase = T.erase := Block.preceq_antisymm (preceq_eq_true_iff_Preceq.mpr (preceq_trans_Preceq hlc2 hrootq))
            (preceq_eq_true_iff_Preceq.mpr hTT')
          rw [heq]
          exact Restated.coneAnchorChainInTree_at_anchor_of_committee_upTo facts (hcross := hcross) S Sched x tE
            hexec hmono htd hsync1 hmult tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr hinv hcs2
            (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›) _ hRs le_rfl
      have hvf : M.view_freeze S.E ((M.opening_slot S.hc (r + 1))) ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) - 1 := by
        have e1 := facts.sch.view_freeze_lt_confirmation_time S.E ((M.opening_slot S.hc (r + 1)))
        rw [hct] at e1
        have e1' := Int.add_one_le_of_lt e1
        linarith
      have h1 := Restated.headsBelow_secondSlot_of_confirmed_afterPhase_upTo facts S Sched x hexec hsync1 hmult htd
        hmono hgst hcv (fun t h1 h2 => hphase t h1 (le_trans h2 ht'E))
        (fun t h => hthird t (le_trans h ht'E)) hcs' ht'len
        (Restated.deliveredDescendantUnderFinalized_anchor facts S Sched x hn' hfinT tGAT)
        (Restated.finalizedPreceqAtSteps_anchor facts S Sched x hn' hfinT tGAT) hlo hvf hn' qH _ hhsq rfl
        hTT' hDX hrootq hprevT (hAB0 _ hDX hX) hpath0 (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›)
        (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›)
      exact hfinish _ hDX hX h1
    · -- the grade-2 branch
      obtain ⟨g, hg⟩ := facts.gr.read_nonempty (M.gradeContract nr.cache) S.E S.hc
        (M.toHealing nr.st.core) (r + 1)
      obtain ⟨o2, ho2⟩ := facts.gr.grade2Block_nonempty (M.toHealing nr.st.core)
        (M.readFrame nr.cache (M.toHealing nr.st.core) (r + 1))
      have hgo2 := facts.nd.ModelProperties_gradeContract_read_Q2 nr.cache S.E S.hc
        (M.toHealing nr.st.core) (r + 1) g hg o2 ho2
      have hgQ := hQ2 g ((facts.nd.gradeContract_read nr.cache S.E S.hc (M.toHealing nr.st.core)
        (r + 1) g).1 hg)
      obtain ⟨root, hroot, hQroot⟩ := facts.gr.grade2Block_preceq_root o2 ho2 (hgo2.symm.trans hgQ)
      obtain ⟨m₂, G, hm₂, hGall, hrootG⟩ := Restated.actionFrame_g2_provenance facts S Sched x hn' q
        root _ ⟨nr, hnr, rfl⟩ hroot
      obtain ⟨bG, hbG⟩ := facts.gr.gradeBool_nonempty S.E
        (M.gradeView (M.toHealing (x[m₂][q].st).st.core)) (x[m₂][q].st).st.core.F S.hc.η_SG (r + 1)
        (M.early S.E S.hc (r + 1) .g2) (M.late S.E S.hc (r + 1) .g2) G
      have hG : M.gradeBool S.E (M.gradeView (M.toHealing (x[m₂][q].st).st.core))
          (x[m₂][q].st).st.core.F S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) .g2)
          (M.late S.E S.hc (r + 1) .g2) G ⇢ true := by
        rw [← hGall bG hbG]; exact hbG
      obtain ⟨v_2, hv_2, a₂, har₂, hai₂, has₂, C₂, hC₂, hac₂, hGC₂⟩ :=
        Restated.graded_preceq_freshSG_of_premises_upTo facts (hcross := hcross) S Sched x tE hexec hmono htd hsync1
          hmult tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr hinv qH
          (facts.gr.domain_le_action S (r + 1) .g2) hm₂ G hG (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›)
          (by intro v hv; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono hinv.tick (Restated.action_emod_delta facts S _) (Finset.mem_sdiff.2 ⟨mem_awake_of_awakeThroughout Sched (show v ∈ Sched.awakeThroughout (M.a S.hc S.E.Δ _ - wAttest S) (M.a S.hc S.E.Δ _) from (Finset.mem_sdiff.1 hv).1) (by linarith [twelve_delta_le_wAttest S, S.E.Δ_pos]) (le_refl _), (Finset.mem_sdiff.1 hv).2⟩))
      have hDX : Block.Preceq T'.erase C₂.erase :=
        preceq_trans_Preceq hpre (preceq_trans_Preceq hQroot (preceq_trans_Preceq hrootG hGC₂))
      have hX : ∀ v_1 ∈ Restated.HonRound M S Sched r, ∀ a : NamedAttestation V,
          a.round = r → a.val_index = v_1 →
          (⟨v_1, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n + 1].sent →
          ∀ C : NamedBlock V, C ∈ (x[n + 1][v_1].st).st.bodies → a.confirmed = some C.root →
          Block.compatible C.erase C₂.erase = true :=
        fun v_1 hv_1 a har hai has C hC hac =>
          hinv.sgPairwise v_1 hv_1 v_2 hv_2 a a₂ har hai has har₂ hai₂ has₂ C C₂ hC hac hC₂ hac₂
      have hv2h : Restated.HonestThrough M Sched x (n + 1) v_2 := fun t ht hin =>
        (Finset.mem_sdiff.1 hv_2).2 (hmono _ _ (by rw [hn1] at ht; exact ht) hin)
      have hvf : (x[n + 1].time : Int) + S.E.Δ
          < M.view_freeze S.E ((M.opening_slot S.hc (r + 1))) := by
        have hR3 : (M.opening_slot S.hc r) + 1 + 1 + 1 ≤ (M.opening_slot S.hc (r + 1)) := by
          rw [facts.gr.opening_slot_succ]
          exact Nat.add_le_add_left S.hc.R_ge_three _
        have e1 : Restated.Vocabulary.Execution.Setup.a M S r + S.E.Δ
            = M.view_freeze S.E ((M.opening_slot S.hc r) + 1) :=
          facts.sch.a_add_delta_eq_view_freeze S r
        have e2 := facts.sch.view_freeze_lt_vote_time_succ S.E ((M.opening_slot S.hc r) + 1)
        have e3 := facts.sch.vote_time_add_delta_le_confirmation_time S ((M.opening_slot S.hc r) + 1 + 1)
        have e4 := facts.sch.confirmation_time_eq_support_cutoff_succ S.E
          ((M.opening_slot S.hc r) + 1 + 1)
        have e5 := facts.sch.support_cutoff_mono S.E hR3
        have e6 := facts.sch.Sts_support_cutoff_lt_view_freeze S.E ((M.opening_slot S.hc (r + 1)))
        rw [hn1]; linarith
      have hpath0 : Restated.ConeAnchorChainInTree M S x T'.erase ((M.opening_slot S.hc (r + 1))) :=
        Restated.coneAnchorChainInTree_of_heldDescendant_upTo facts S Sched x tE hexec hmono htd hsync1 hmult tGAT gap
          hgst hlen hcv hthird hphase hrsW hcs hr hinv hcross hC₂ hv2h (by rw [hn1]; exact htGAT)
          hDX hTT' hvf le_rfl (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›)
      have h0 : Restated.HeadsBelow M S Sched x T'.erase ((M.opening_slot S.hc (r + 1))) :=
        fun w mw hw' hmw G hG => preceq_trans_Preceq hDX (hP v_2 hv_2 a₂ har₂ hai₂ has₂ C₂ hC₂ hac₂ w mw
          hw' hmw G hG)
      have hsc0 : M.support_cutoff S.E ((M.opening_slot S.hc (r + 1)))
          ≤ Restated.Vocabulary.Execution.Setup.a M S (r + 1) := by
        have e1 := facts.sch.Sts_support_cutoff_lt_view_freeze S.E ((M.opening_slot S.hc (r + 1)))
        have e2 := facts.sch.view_freeze_lt_confirmation_time S.E ((M.opening_slot S.hc (r + 1)))
        rw [Restated.confirmation_time_opening_slot facts S (r + 1)] at e2
        linarith
      have hsR : M.support_cutoff S.E ((M.opening_slot S.hc (r + 1)))
          ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1 + 1)) - 1 := by
        linarith
      have hpos : 0 < (M.opening_slot S.hc (r + 1)) := facts.gr.opening_slot_pos S (Nat.succ_pos r)
      have hrange := Restated.headsBelow_range_afterPhase_upTo facts S Sched x hexec
        (syncBefore_mono_jointU hsc0 hsync1) hmult htd hmono hgst hcv
        (fun t h1 h2 => hphase t h1 (le_trans h2 ht'E))
        (fun t h => hthird t (le_trans h ht'E)) hcs' ht'len
        (Restated.deliveredDescendant_before_succ_succ_tick facts S Sched x hF' tGAT)
        (Restated.finalizedPreceqAtSteps_before_succ_succ_tick facts S Sched x hF' tGAT)
        (s₀ := (M.opening_slot S.hc (r + 1))) (s₁ := (M.opening_slot S.hc (r + 1)))
        hpos hsE hsR
        (fun s h0' h1' => by
          have hs : s = (M.opening_slot S.hc (r + 1)) := le_antisymm h1' h0'
          rw [hs]; exact hAB0 _ hDX hX)
        (fun s h0' h1' => by
          have hs : s = (M.opening_slot S.hc (r + 1)) := le_antisymm h1' h0'
          rw [hs]; exact hpath0)
        h0
        (by intro s _ _ m hm q hq; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono hm (facts.sch.vote_time_emod_delta S _) (Finset.mem_sdiff.2 ⟨Restated.awake_of_mem_HonSlot facts S Sched _ hq, fun h => ((Restated.mem_HonSlot facts).mp hq).2.2 (hmono _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E s) h)⟩))
        (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›)
      exact hfinish _ hDX hX (hrange _ (Nat.le_succ _) le_rfl)
  · -- the anchor did not move: `T' = T`
    have hchoice : T' = T := by
      rw [hT']
      show (if h : ∃ C : NamedBlock V, Restated.NewAnchorSpec M S Sched x r n' att T C then h.choose
        else T) = T
      rw [dif_neg hex]
    rw [hchoice] at hF' hJ'' hhmax' ⊢
    obtain ⟨v₀, m₀, hTbody, hv₀h, hm₀, hm₀t⟩ :=
      Restated.exists_anchor_holder_of_committee facts S Sched x tE hexec hmono htd tGAT gap hgst hlen hr hinv
        hcs2
    exact Restated.headsBelow_thirdSlot_of_anchorFacts_upTo facts S Sched x tE hexec hmono htd hsync hmult hcom tGAT
      gap hgst hlen hcv hthird hphase hcs hw hr hn hn'' hF' hJ'' hhmax' hTbody hv₀h hm₀
      (by linarith)
      (fun v hawT hvS m hm B hB => Restated.grade1_compatible_at_awakeReader_upTo facts (hcross := hcross) S Sched x
        tE hexec hmono htd
        (syncBefore_mono_jointU (le_trans (facts.gr.late_le_domain S (r + 1) .g1) (facts.gr.domain_le_action S (r + 1) .g1)) hsync1)
        hmult tGAT gap hgst hlen hcv hthird hphase hrsW hcs hr hinv
        (facts.gr.domain_le_action S (r + 1) .g1) hawT hvS hm B hB (by intros; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono ‹_› ‹_› ‹_›)
        (by intro v hv; exact Restated.tick_outcome_of_tickStepAt facts S Sched x hexec.idealization.root_injective hexec.honestRootsNew hmono hinv.tick (Restated.action_emod_delta facts S _) (Finset.mem_sdiff.2 ⟨mem_awake_of_awakeThroughout Sched (show v ∈ Sched.awakeThroughout (M.a S.hc S.E.Δ _ - wAttest S) (M.a S.hc S.E.Δ _) from (Finset.mem_sdiff.1 hv).1) (by linarith [twelve_delta_le_wAttest S, S.E.Δ_pos]) (le_refl _), (Finset.mem_sdiff.1 hv).2⟩)))
      hprevT

end

end DecoupledConsensusModel.Sts.Restated
