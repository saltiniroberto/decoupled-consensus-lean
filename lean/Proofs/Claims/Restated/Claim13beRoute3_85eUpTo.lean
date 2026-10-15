import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariantActiveSinceW
import Proofs.Claims.Restated.Claim13beRoute3_41
import Proofs.Claims.Restated.Claim13beRoute3_44UpTo
import Proofs.Claims.Restated.Claim13beRoute3_46
import Proofs.Claims.Restated.Claim13beRoute3_76
import Proofs.Claims.Restated.Claim13beRoute3_83
import Proofs.Claims.Restated.Claim13beRoute3_85cUpTo
import Proofs.Claims.Restated.Claim13beRoute3_85e
import Model.Conditions.Claim13bInvariantActiveSinceW
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.Claim13beRoute3_72
import Model.Conditions.Claim13beRoute3_83
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
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Statements_Instantiation_Proposals
import Model.Record.Wiring

/-!
# Honest rows at an honest opening, with bounded synchrony

The theorem of `Claim13beRoute3_85e.lean` along the path an execution follows, with synchrony
assumed only up to the phase end `tE`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

local macro "p51% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_51)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p58% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_58)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p71% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_71)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- With synchrony assumed only up to `tE`, in the run of the execution `x` up to step `n`, along
    its path `W`, for a round `c` at least three rounds after the deadline round with honest
    openings at `c` and `c − 1` proposing `P` and `P'`, with `S.a c ≤ x[n].time ≤ S.a rW` and
    `h(T_0) ≤ h(P)`: either every round-`c` attestation of every validator not held at `S.a c` is
    `vote h(P) T_h(P) b`, with `b = false` when `nj(P) = false`, or every validator not held at
    `S.a c` has a justified height at least `h(P)` in `W`'s world strictly before `S.a c`. -/
theorem honestRow_atOpening_planned_runAll_l85e_upTo (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v₀ : V) (n : Nat)
    {tGAT tE : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWakeBefore M S x tE) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    (hlen : tGAT + (Restated.healingLengthη M S gap + (Restated.constants M S).period) ≤ tE) (htd : Restated.TimeDiverges M x)
    {T_0 : NamedBlock V}
    (hA0 : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.rebasedDeadlineRoundW M S tGAT gap) T_0)
    (hnW : (x[n].time : Int) ≤ (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)))
    {c : Round} (hc3 : Restated.deadlineRoundW M S tGAT gap + 3 ≤ c)
    (hhor : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c) ≤
      ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } :
        Record.Run V).horizon)
    (hopening : S.E.proposer ((M.opening_slot S.hc c)) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c))))
    (hopeningPrev : S.E.proposer ((M.opening_slot S.hc (c - 1))) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc (c - 1)))))
    {P P' : NamedBlock V}
    (htop : (M.derive_named S.E S.cfg T_0).h ≤ (M.derive_named S.E S.cfg P).h) :
    let R : Record.Run V :=
      { Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) }
    let W := Restated.runAllPath M S Sched x v₀ n
    let wp := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc c)))
      (S.E.proposer (M.opening_slot S.hc c))
    let wp' := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc (c - 1))))
      (S.E.proposer (M.opening_slot S.hc (c - 1)))
    ∀ cp : M.Cache,
      M.onPhaseTick S.E S.hc wp.st.core.toHealing
        (M.proposal_time S.E (M.opening_slot S.hc c)) wp.cache ⇢ cp →
      let pn := M.mkNode (M.ns_setClock S.E wp.st (M.proposal_time S.E (M.opening_slot S.hc c)))
        wp.record cp
      M.proposal_with (M.gradeContract cp) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc c))) pn.st ⇢ some P →
    ∀ cp' : M.Cache,
      M.onPhaseTick S.E S.hc wp'.st.core.toHealing
        (M.proposal_time S.E (M.opening_slot S.hc (c - 1))) wp'.cache ⇢ cp' →
      let pn' := M.mkNode
        (M.ns_setClock S.E wp'.st (M.proposal_time S.E (M.opening_slot S.hc (c - 1))))
        wp'.record cp'
      M.proposal_with (M.gradeContract cp') .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc (c - 1)))) pn'.st ⇢ some P' →
    (∀ u ∈ notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c)),
      ∀ nu ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (W (strictEventIndex R (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c)) u) c,
      ∀ D, M.duties_attest_with (M.gradeContract nu.cache) S.E S.hc ((Setup.alwaysAwake S).node u)
        nu.st nu.record ⇢ D →
      (D.2.2.height_pair =
            .vote (M.derive_named S.E S.cfg P).h
              (M.derive_named S.E S.cfg P).T_h.root false ∨
          D.2.2.height_pair =
            .vote (M.derive_named S.E S.cfg P).h
              (M.derive_named S.E S.cfg P).T_h.root true) ∧
        ((M.derive_named S.E S.cfg P).nj = false →
          D.2.2.height_pair =
            .vote (M.derive_named S.E S.cfg P).h
              (M.derive_named S.E S.cfg P).T_h.root false)) ∨
    (∀ w ∈ notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c)),
      (M.derive_named S.E S.cfg P).h ≤
        (W (strictEventIndex R (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c)) w).st.core.h_j) := by
  classical
  intro R W wp wp' cp hcp pn hP cp' hcp' pn' hP'
  by_cases hall : ∀ w ∈ notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c)),
      (M.derive_named S.E S.cfg P).h ≤
        (W (strictEventIndex R (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c)) w).st.core.h_j
  · exact Or.inr hall
  left
  push Not at hall
  obtain ⟨w₀, hw₀, hlt⟩ := hall
  have hHne : (M.derive_named S.E S.cfg P).h ≠ 0 := ((Nat.zero_le _).trans_lt hlt).ne'
  have hlen' : tGAT + Restated.healingLengthη M S gap ≤ tE := Restated.healingLength_le_of_kit_l76 facts S hlen
  have hrW : Restated.rebasedDeadlineRoundW M S tGAT gap ≤ Restated.switchRound M S tE :=
    Restated.rebasedDeadlineRoundW_le_switchRound facts S tGAT tE gap (Restated.runAll M S Sched x v₀ 0) hgst hlen'
  have hrD : Restated.deadlineRoundW M S tGAT gap ≤ Restated.switchRound M S tE :=
    (Restated.deadlineRoundW_le_rebased facts S tGAT gap).trans hrW
  obtain ⟨-, hWE⟩ := Restated.window_in_phase_atRound facts S tGAT tE gap hgst hlen' hrD le_rfl
  have hn : (x[n].time : Int) ≤ tE := hnW.trans hWE
  have hf := Restated.admissibleFieldsOn_runAll_notHeld_upTo facts S Sched x v₀ n (fun k w sm hsend hle haw => hsync k w sm hsend (le_trans hle hn) haw) hmono hawake hgst hcv hvalid
    hawm hthird hn
  have hHs : ∀ t t' : Int, t ≤ t' → notHeldAt Sched t' ⊆ notHeldAt Sched t :=
    fun _ _ h => notHeldAt_anti hmono h
  obtain ⟨-, hlo, hpropA⟩ := Restated.openingProposal_runBlock_runAll_l85c_upTo facts S Sched x v₀ n (fun k w sm hsend hle haw => hsync k w sm hsend (le_trans hle hn) haw) hmono
    hawake hgst hcv hvalid hawm hthird hn ((Nat.le_succ _).trans hc3) hhor hopening cp hcp hP
  have hagree := Restated.honestVotes_oneEntry_runAll_l85c_upTo facts S Sched x v₀ n hsync hmono hawake hgst hcv
    hvalid hawm hthird hcom hrec hlen htd hA0 hnW htop
  have hrows := fun (u : V) (hu : u ∈ notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c))) =>
    Restated.honestRow_atOpening_runAll_l85c_upTo facts S Sched x v₀ n hsync hmono hawake hgst hcv hvalid hawm hthird
      hcom hrec hlen htd hA0 hnW hc3 hhor hopening hopeningPrev htop hu cp hcp hP cp' hcp' hP'
  obtain ⟨n₀, hn₀, D₀, hD₀⟩ := (p51% actionAttestation_nonempty₅₁) facts (Setup.alwaysAwake S)
    (W (strictEventIndex R (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c)) w₀) c
    ((Setup.alwaysAwake S).node w₀)
  obtain ⟨b₀, hb₀⟩ : ∃ b₀ : Bool,
      D₀.2.2.height_pair =
        .vote (M.derive_named S.E S.cfg P).h
          (M.derive_named S.E S.cfg P).T_h.root b₀ := by
    rcases hrows w₀ hw₀ n₀ hn₀ D₀ hD₀ with ⟨hv | hv, -⟩ | ⟨-, -, -, -, hle⟩
    · exact ⟨false, hv⟩
    · exact ⟨true, hv⟩
    · exact absurd hle (not_le.mpr hlt)
  have hkc : tGAT + 1 ≤ M.early S.E S.hc c .g2 - S.E.Δ :=
    Restated.lo_le_early_g2_sub_delta_of_action_lt facts S (Restated.roundAt_lo_le_rGST_l71 facts S tGAT)
      (lt_of_le_of_lt (Restated.rGST_le_deadlineRoundW_l85c facts S tGAT gap)
        (lt_of_lt_of_le (Nat.lt_succ_self _) ((Nat.le_add_right _ 2).trans hc3)))
  have hemit₀ := Restated.honest_emits_exact_actionAttestationAtOn facts (Setup.alwaysAwake S)
    (notHeldAt Sched) Finset.univ hf c hw₀ hhor (hlo.trans hpropA)
    (fun j hj => Restated.awake_g2_action_runAllPath facts S Sched x v₀ n hmono hawake hn c hkc w₀ j hj)
    (fun j hj => hf.tick_outcome j _ _ hj) n₀ hn₀ D₀ hD₀
  intro u hu nu hnu D hD
  rcases hrows u hu nu hnu D hD with h1 | ⟨-, L, hL, hne, -⟩
  · exact h1
  exfalso
  have hcert := Restated.ownLock_certificateOn_l85e facts (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ
    hf (Finset.mem_univ u) c hHne nu hnu D hD hL
  obtain ⟨z, t, a, hemz, hzt, hpz⟩ := Restated.certificateOn_emittedVote_l85e facts (Setup.alwaysAwake S)
    (notHeldAt Sched) Finset.univ hf hHs
    (Restated.belowOneThird_runAll_notHeld_inPhase facts S Sched x n tE hthird hn) hcert
  exact hne (hagree z w₀ t _ a _ L _ false b₀ hemz hzt hpz hemit₀ hw₀ hb₀)

end

end DecoupledConsensusModel.Sts.Restated
