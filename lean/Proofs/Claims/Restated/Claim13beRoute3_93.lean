import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bInvariantActiveSinceW
import Proofs.Claims.Restated.Claim13bStepCone
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13beRoute3_41
import Proofs.Claims.Restated.Claim13beRoute3_44
import Proofs.Claims.Restated.Claim13beRoute3_46
import Proofs.Claims.Restated.Claim13beRoute3_47b
import Proofs.Claims.Restated.Claim13beRoute3_58
import Proofs.Claims.Restated.Claim13beRoute3_67
import Proofs.Claims.Restated.Claim13beRoute3_72
import Proofs.Claims.Restated.Claim13beRoute3_73
import Proofs.Claims.Restated.Claim13beRoute3_76
import Proofs.Claims.Restated.Claim13beRoute3_83
import Proofs.Claims.Restated.Claim13beRoute3_85c
import Proofs.Claims.Restated.Claim13beRoute3_85d
import Proofs.Claims.Restated.Claim13beRoute3_85e
import Proofs.Claims.Restated.Claim13beRoute3_86g
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActiveSinceW
import Model.Conditions.Claim13bK_ConfirmedSettle
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13bStepCone
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.Claim13beRoute3_72
import Model.Conditions.Claim13beRoute3_83
import Model.Conditions.Claim13beRoute3_92
import Model.Conditions.RunAll
import Model.Conditions.RunVocabulary
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13bd
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGrades
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedHeadReads
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Statements_Instantiation_Proposals
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_93

/-!
# Honest heads, justified entries and planned rows

Theorems over a model `M : Record.Model V` about the run of the first `N` steps of an execution `x`:
an ancestor of the honest heads is an ancestor of a later honest opening proposal, a store's
justified block is a run block that is its own entry, the rows of an honest opening round are
planned, and a bound on the vote instants of a window.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

/-- Refers to a private theorem of `Proofs.Claims.Restated.Claim13beRoute3_47b` by name. -/
local macro "p47b% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_47b)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- Refers to a private theorem of `Proofs.Claims.Restated.Claim13beRoute3_51` by name. -/
local macro "p51% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_51)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- Refers to a private theorem of `Proofs.Claims.Restated.Claim13beRoute3_58` by name. -/
local macro "p58% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_58)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- Refers to a private theorem of `Proofs.Claims.Restated.Claim13beRoute3_71` by name. -/
local macro "p71% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_71)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- Refers to a private theorem of `Proofs.Claims.Restated.Claim13beRoute3_73` by name. -/
local macro "p73% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_73)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- Refers to a private theorem of `Proofs.Claims.Restated.Claim13beRoute3_86c` by name. -/
local macro "p86c% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_86c)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- Refers to a private theorem of `Proofs.Claims.Restated.Claim13beRoute3_86g` by name. -/
local macro "p86g% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_86g)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Framework.StsMultisetLog

/-- The proposal instant of slot `s` is `4Δ · s`. -/
private theorem proposal_time_closed₉₃ (facts : Record.Facts M) (E : Env V) (hc : HealConfig)
    (s : Slot) : M.proposal_time E s = 4 * E.Δ * (s : Int) := by
  induction s with
  | zero =>
    have h := facts.sch.Γ_0_eq_proposal_time hc E 0
    rw [facts.gr.opening_slot_zero_mk] at h
    rw [← h]
    simp [slotStart]
  | succ s ih =>
    have h := (facts.sch.slot_instants_l55 E s).2.2.2.1
    rw [h, ih]
    push_cast
    ring

/-- In an execution in which every tick has an outcome, along the path
    `W := Restated.runAllPath M S Sched x v₀ N`, at an opening slot `o_c` after the progress
    deadline with `S.a c ≤ x[N].time`: if every head that an honest active committee member of a
    slot from `s₀ ≤ o_c` on can vote descends from `X`, then `X` is an ancestor of every block `P`
    the proposal duty of `o_c` can return. -/
theorem preceq_openingProposal_of_heads_f2b (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v₀ : V) (N : Nat)
    {tGAT tL tC : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWake M S x) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tL → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tL →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hn : (x[N].time : Int) ≤ tL)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tL gap)
    (htd : Restated.TimeDiverges M x) (hcs : Restated.committeeSleepinessW M S Sched tC)
    {c : Round} (hc : Restated.deadlineRoundW M S tGAT gap + 2 ≤ c)
    (hcsC : tC ≤ slotStart S.E.Δ ((M.opening_slot S.hc c) + 1))
    (hAc : (Restated.Vocabulary.Execution.Setup.a M S c) ≤ (x[N].time : Int))
    (hopening : S.E.proposer ((M.opening_slot S.hc c)) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c))))
    {P : NamedBlock V}
    {X : Block V} (hX : Restated.HeadsBelow M S Sched x X (M.opening_slot S.hc c)) :
    let R : Record.Run V :=
      { Restated.runAll M S Sched x v₀ N with honest := notHeldAt Sched (x[N].time : Int) }
    let W := Restated.runAllPath M S Sched x v₀ N
    let wp := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc c)))
      (S.E.proposer (M.opening_slot S.hc c))
    ∀ cp : M.Cache,
      M.onPhaseTick S.E S.hc wp.st.core.toHealing
        (M.proposal_time S.E (M.opening_slot S.hc c)) wp.cache ⇢ cp →
      let pn := M.mkNode (M.ns_setClock S.E wp.st (M.proposal_time S.E (M.opening_slot S.hc c)))
        wp.record cp
      M.proposal_with (M.gradeContract cp) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc c))) pn.st ⇢ some P →
    Block.Preceq X P.erase := by
  intro R W wp cp hcp pn hP
  have hadopt := (Restated.openingAdoption_at_strongWindow_afterDeadline facts S Sched x v₀ N hsync hmono hawake
    hgst hcv hvalid hawm hthird hn hcom hrec hc hAc hopening cp hcp hP).1
  have hmaj := Restated.majority_of_committeeSleepinessW facts S Sched hcs (s := (M.opening_slot S.hc c)) hcsC
  obtain ⟨w, hw⟩ : ((S.E.committee ((M.opening_slot S.hc c))) ∩
      Restated.HonSlot M S Sched ((M.opening_slot S.hc c))).Nonempty := by
    rw [Finset.inter_eq_right.2 (Restated.HonSlot_subset_committee facts S Sched _), ← Finset.card_pos]; omega
  have hwS : w ∈ Restated.HonSlot M S Sched ((M.opening_slot S.hc c)) := (Finset.mem_inter.mp hw).2
  obtain ⟨m, hm⟩ := Restated.exists_tickStepAt facts x htd
    (facts.sch.Optimistic_proposal_time_nonneg S.E ((M.opening_slot S.hc c)) |>.trans_lt
      (facts.sch.proposal_time_lt_vote_time S.E _))
  have hvc := facts.sch.Sts_vote_time_le_confirmation_time S ((M.opening_slot S.hc c))
  have hvlt : M.vote_time S.E ((M.opening_slot S.hc c)) < (Restated.Vocabulary.Execution.Setup.a M S c) := by
    rw [Restated.a_eq_confirmation_opening_l58 facts]
    have hΔ := S.E.Δ_pos
    have h := Restated.vote_time_add_delta_lt_confirmation_l67 facts S.E ((M.opening_slot S.hc c))
    linarith
  have hmN : m + 1 ≤ N := by
    by_contra hcon
    have hle : (x[N].time : Int) ≤ (x[m].time : Int) := Restated.time_mono_int facts S Sched x (by omega)
    have h0 := (Restated.tickStepAt_time facts x hm).2
    linarith
  have hwv : w ∈ notHeldAt Sched (M.vote_time S.E ((M.opening_slot S.hc c))) :=
    notHeldAt_anti hmono hvc (mem_notHeldAt.mpr ((Restated.mem_HonSlot facts).mp hwS).2.2)
  obtain ⟨G, cc, hcc, Tr, hTr, L, hL, L', hL', hG⟩ := (p86g% exists_headOutcome₈₆g) facts S
    (x[m][w].st) (M.vote_time S.E (M.opening_slot S.hc c))
  have hhead := hX w m hwS hm G
    (((p73% gfHeadFrom_returns_iff₇₃) facts S _ _ G).2 ⟨cc, hcc, _, rfl, Tr, hTr, L, hL, L', hL', hG⟩)
  have hst := Restated.stateBeforeTime_runAll_tick facts S Sched x v₀ hm hmN w
  have hadoptw := hadopt w hwv
  dsimp only [W, R] at hadoptw
  rw [hst] at hadoptw
  rw [← hadoptw cc hcc Tr hTr L hL L' hL' G hG]
  exact hhead

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Framework.StsMultisetLog

/-- Under the bundle along its path `W`, with every tick having an outcome and the validators
    outside the set for the horizon weighing less than a third: if `w ∈ Xb` and the justified height
    of `w`'s store in `W` before `read` is not `0`, then some run block `E₀` read through `Xb`
    erases to that store's justified block, has its justified height and is its own entry, and some
    validator in the set for an instant `t` emitted at `t` the target vote for that height and that
    block's root. -/
theorem storeJustified_runEntry_f2b (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hfb : Execution.BelowOneThird S (Hs rho.horizon))
    {w : V} (hw : w ∈ Xb) (read : Int)
    (hnz : (W (strictEventIndex rho read) w).st.h_j ≠ 0) :
    (∃ E₀ : NamedBlock V, Restated.RunBlockOn M S rho W Xb E₀ ∧
      E₀.erase = (W (strictEventIndex rho read) w).st.J ∧
      (M.derive_named S.E S.cfg E₀).h = (W (strictEventIndex rho read) w).st.h_j ∧
      (M.derive_named S.E S.cfg E₀).T_h = E₀.erase) ∧
    ∃ (z : V) (t : Int) (a : NamedAttestation V),
      (Restated.Vocabulary.Execution.Run.emits M S rho W z (Object.attest a) t) ∧ z ∈ Hs t ∧
        a.height_pair = NamedHeightPair.vote (W (strictEventIndex rho read) w).st.h_j
          (W (strictEventIndex rho read) w).st.J.root false := by
  have hcert := Restated.certificateOfStoreJustification_atStrictReadOn facts S Hs Xb hf hw read hnz
  obtain ⟨z, t, a, hem, hz, hpair⟩ := Restated.certificateOn_emittedVote_l85e facts S Hs Xb hf hHs hfb hcert
  refine ⟨?_, z, t, a, hem, hz, hpair⟩
  obtain ⟨E₀, hE₀run, hE₀root, hE₀h, hE₀T⟩ :=
    Restated.emittedVote_entry_l85c facts S Hs Xb hf hHsXb hem hz hpair
  obtain ⟨D, hDe, hDrun⟩ := Restated.runBlockOf_justified_atStrictReadOn facts S Hs Xb hf hw read
  have hroot : D.erase.root = E₀.erase.root := by
    rw [hDe, Proofs.NamedWire.erase_root, hE₀root]
  have hDE : D.erase = E₀.erase := Restated.runBlock_eq_of_root_eqOn facts W Xb hf.rootCollisionFree hDrun hE₀run hroot
  exact ⟨E₀, hE₀run, hDE ▸ hDe, hE₀h, hE₀T⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Framework.StsMultisetLog

/-- In an execution in which every tick has an outcome, along the path
    `W := Restated.runAllPath M S Sched x v₀ n`: if the store of some validator `w` in `W` before
    `S.a c` has justified height `h(P)` and a justified block with the root of `P`'s entry, then
    every validator not held at `S.a c` has every round-`c` attestation it can sign carrying
    `vote h(P) T_h(P) b`, with `b = false` when `nj(P) = false`. -/
theorem openingRowsPlanned_of_justifiedEntry_f2b (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v₀ : V) (n : Nat)
    {tGAT tE : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWake M S x) (hmono : Sched.MonotoneCorruption)
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
    (htop : (M.derive_named S.E S.cfg T_0).h ≤ (M.derive_named S.E S.cfg P).h)
    {w : V}
    (hwh : (Restated.runAllPath M S Sched x v₀ n
          (strictEventIndex
            ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } : Record.Run V)
            (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c)) w).st.h_j
        = (M.derive_named S.E S.cfg P).h)
    (hwJ : (Restated.runAllPath M S Sched x v₀ n
          (strictEventIndex
            ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } : Record.Run V)
            (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c)) w).st.J.root
        = (M.derive_named S.E S.cfg P).T_h.root) :
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
    Restated.OpeningRowsPlanned M S Sched x v₀ n c P := by
  classical
  intro R W wp wp' cp hcp pn hP cp' hcp' pn' hP'
  have hHne : (M.derive_named S.E S.cfg P).h ≠ 0 :=
    Nat.one_le_iff_ne_zero.mp (facts.cs.one_le_derive_named_h S.E S.cfg P)
  have hlen' : tGAT + Restated.healingLengthη M S gap ≤ tE := Restated.healingLength_le_of_kit_l76 facts S hlen
  have hrW : Restated.rebasedDeadlineRoundW M S tGAT gap ≤ Restated.switchRound M S tE :=
    Restated.rebasedDeadlineRoundW_le_switchRound facts S tGAT tE gap (Restated.runAll M S Sched x v₀ 0) hgst hlen'
  have hrD : Restated.deadlineRoundW M S tGAT gap ≤ Restated.switchRound M S tE :=
    (Restated.deadlineRoundW_le_rebased facts S tGAT gap).trans hrW
  obtain ⟨-, hWE⟩ := Restated.window_in_phase_atRound facts S tGAT tE gap hgst hlen' hrD le_rfl
  have hn : (x[n].time : Int) ≤ tE := hnW.trans hWE
  have hf := Restated.admissibleFieldsOn_runAll_notHeld facts S Sched x v₀ n hsync hmono hawake hgst hcv hvalid
    hawm hthird hn
  have hHs : ∀ t t' : Int, t ≤ t' → notHeldAt Sched t' ⊆ notHeldAt Sched t :=
    fun _ _ h => notHeldAt_anti hmono h
  have hbelow := Restated.belowOneThird_runAll_notHeld_inPhase facts S Sched x n tE hthird hn
  have hnz : (W (strictEventIndex R (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c)) w).st.h_j
      ≠ 0 := by rw [hwh]; exact hHne
  obtain ⟨-, z₀, t₀, a₀, hem₀, hz₀, hpair₀⟩ := Restated.storeJustified_runEntry_f2b facts (Setup.alwaysAwake S)
    (notHeldAt Sched) Finset.univ hf hHs (fun _ => Finset.subset_univ _) hbelow
    (Finset.mem_univ w) _ hnz
  rw [hwh, hwJ] at hpair₀
  have hagree := Restated.honestVotes_oneEntry_runAll_l85c facts S Sched x v₀ n hsync hmono hawake hgst hcv
    hvalid hawm hthird hcom hrec hlen htd hA0 hnW htop
  intro u hu nu hnu D hD
  rcases Restated.honestRow_atOpening_runAll_l85c facts S Sched x v₀ n hsync hmono hawake hgst hcv hvalid hawm
      hthird hcom hrec hlen htd hA0 hnW hc3 hhor hopening hopeningPrev htop hu cp hcp hP cp' hcp' hP'
      nu hnu D hD with
    h1 | ⟨-, L, hL, hne, -⟩
  · exact h1
  exfalso
  have hcert := Restated.ownLock_certificateOn_l85e facts (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ
    hf (Finset.mem_univ u) c hHne nu hnu D hD hL
  obtain ⟨z, t, a, hemz, hzt, hpz⟩ := Restated.certificateOn_emittedVote_l85e facts (Setup.alwaysAwake S)
    (notHeldAt Sched) Finset.univ hf hHs hbelow hcert
  exact hne (hagree z z₀ t t₀ a a₀ L _ false false hemz hzt hpz hem₀ hz₀ hpair₀)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Framework.StsMultisetLog
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If `c₂ ≤ s / R + K`, then the vote instant of `o_{c₂} + 2` is at most the proposal instant of
    `s` plus `K` periods plus `9Δ`. -/
theorem voteTime_bound_f2b (facts : Record.Facts M) (S : Setup V) {s : Slot} {c₂ K : Nat}
    (hc : c₂ ≤ s / S.hc.R + K) :
    M.vote_time S.E ((M.opening_slot S.hc c₂) + 2) ≤
      M.proposal_time S.E s + (K : Int) * (Restated.constants M S).period + 9 * S.E.Δ := by
  have hv1 := (facts.sch.slot_instants_l55 S.E (M.opening_slot S.hc c₂)).2.2.2.1
  have hv2 : M.vote_time S.E ((M.opening_slot S.hc c₂) + 2)
      = M.proposal_time S.E ((M.opening_slot S.hc c₂) + 1) + 5 * S.E.Δ :=
    (facts.sch.slot_instants_l55 S.E ((M.opening_slot S.hc c₂) + 1)).2.2.2.2.1
  have hv3 := Restated.proposal_time_opening_eq_l85d facts S c₂
  have hp := proposal_time_closed₉₃ facts S.E S.hc s
  have hslot : ((s / S.hc.R : Nat) : Int) * (S.hc.R : Int) ≤ (s : Int) := by
    exact_mod_cast Nat.div_mul_le_self s S.hc.R
  rw [Restated.period_eq facts S]
  have hΔ := S.E.Δ_pos
  have hR : (0 : Int) ≤ (S.hc.R : Int) := by positivity
  have hc' : (c₂ : Int) ≤ ((s / S.hc.R : Nat) : Int) + (K : Int) := by exact_mod_cast hc
  have hk : 4 * S.E.Δ * (S.hc.R : Int) * (c₂ : Int) ≤
      4 * S.E.Δ * (S.hc.R : Int) * (((s / S.hc.R : Nat) : Int) + (K : Int)) := by
    apply mul_le_mul_of_nonneg_left hc'
    positivity
  have hs4 : 4 * S.E.Δ * (((s / S.hc.R : Nat) : Int) * (S.hc.R : Int)) ≤ 4 * S.E.Δ * (s : Int) := by
    apply mul_le_mul_of_nonneg_left hslot
    positivity
  rw [hv2, hv1, hv3, hp]
  nlinarith [hk, hs4]

end

end DecoupledConsensusModel.Sts.Restated
