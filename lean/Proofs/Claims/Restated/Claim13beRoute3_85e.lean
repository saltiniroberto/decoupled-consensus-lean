import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariantActiveSinceW
import Proofs.Claims.Restated.Claim13beRoute3_41
import Proofs.Claims.Restated.Claim13beRoute3_44
import Proofs.Claims.Restated.Claim13beRoute3_45
import Proofs.Claims.Restated.Claim13beRoute3_46
import Proofs.Claims.Restated.Claim13beRoute3_47b
import Proofs.Claims.Restated.Claim13beRoute3_48
import Proofs.Claims.Restated.Claim13beRoute3_69
import Proofs.Claims.Restated.Claim13beRoute3_76
import Proofs.Claims.Restated.Claim13beRoute3_83
import Proofs.Claims.Restated.Claim13beRoute3_85c
import Proofs.Claims.Restated.Vocabulary_Execution_EmissionShape
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Claims.Restated.Vocabulary_Protocol_ValidatorClient_Bridge
import Model.Conditions.Claim13bInvariantActiveSinceW
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.Claim13beRoute3_72
import Model.Conditions.Claim13beRoute3_83
import Model.Conditions.RunAll
import Model.Conditions.RunVocabulary
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13bd
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Node
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Statements_Instantiation_Proposals
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_25

/-!
# Honest rows at an honest opening, with the lock case excluded

An own lock at a nonzero height is backed by a certificate, and a certificate has a signer that
emitted its vote. So at an honest opening after the deadline every honest row is the planned vote,
unless every honest validator already holds a justified height at least the opening proposal's
height. Stated over a model `M : Record.Model V`.
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
local macro "p85c% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_85c)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "pRT% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Vocabulary_Protocol_ValidatorClient_RecordTargetHistory)
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

/-- Along a path `W` of the run, if `v`'s signing record in the world before the `n`-th event holds
    the lock `T` at height `h`, then some earlier event is a tick of `v` whose outcome on the path
    sends an attestation whose finality pair is `(h, T)`. -/
private theorem recordLock_along₈₅e (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (v : V) :
    ∀ (n : Nat) {h : Height} {T : BlockId}, (W n v).record.legacy.lock h = some T →
      ∃ i : Nat, i < n ∧ ∃ (t : Int) (a : NamedAttestation V),
        rho.events[i]? = some (.tick v t) ∧
        ∃ out : M.N × List (NamedObject V), M.tick S v (W i v) t ⇢ out ∧ W (i + 1) v = out.1 ∧
          NamedObject.attest a ∈ out.2 ∧ a.finality_pair = some ⟨h, T⟩ := by
  intro n
  induction n with
  | zero =>
    intro h T hlock
    have h0 : W 0 = fun v' => M.initial S v' := Set.mem_singleton_iff.mp (hW 0).1
    have h1 : W 0 v = M.initial S v := congrFun h0 v
    rw [h1, facts.nd.initial_record_legacy_lock S v h] at hlock
    cases hlock
  | succ n ih =>
    intro h T hlock
    rcases (p85c% path_step₈₅c) hW n with ⟨-, hEq⟩ | ⟨e, hev, hstep⟩
    · rw [hEq] at hlock
      obtain ⟨i, hi, r⟩ := ih hlock
      exact ⟨i, Nat.lt_succ_of_lt hi, r⟩
    · by_cases he : ∃ t, e = .tick v t
      · obtain ⟨t, rfl⟩ := he
        simp only [Record.worldStepOf, Set.mem_setOf_eq] at hstep
        rcases hstep with ⟨out, hout, hEq⟩ | ⟨-, hEq⟩
        · have hv : W (n + 1) v = out.1 := by rw [hEq, Function.update_self]
          rw [hv] at hlock
          cases hpre : (W n v).record.legacy.lock h with
          | some X =>
            have hmono := facts.nd.lock_mono_on_tick_emit S v (W n v) t hpre out hout
            have hXT : X = T := Option.some.inj (hmono.symm.trans hlock)
            subst hXT
            obtain ⟨i, hi, r⟩ := ih hpre
            exact ⟨i, Nat.lt_succ_of_lt hi, r⟩
          | none =>
            obtain ⟨a, ha, hpair⟩ :=
              facts.nd.on_tick_emit_lock_introduced S v (W n v) t hpre out hout hlock
            exact ⟨n, Nat.lt_succ_self n, t, a, hev, out, hout, hv, ha, hpair⟩
        · rw [hEq] at hlock
          obtain ⟨i, hi, r⟩ := ih hlock
          exact ⟨i, Nat.lt_succ_of_lt hi, r⟩
      · rw [(pRT% rt_step_record) facts S (W n) (W (n + 1)) e v hstep (fun t h => he ⟨t, h⟩)]
          at hlock
        obtain ⟨i, hi, r⟩ := ih hlock
        exact ⟨i, Nat.lt_succ_of_lt hi, r⟩

/-- Under the bundle, if `v ∈ Xb` and `H ≠ 0`, then for every node state `n` of `v`'s round-`r`
    action read from `W (strictEventIndex rho (S.a r))` and every outcome `D` of `v`'s attestation
    duty on `n`: if the own lock at `H` of `v`'s record there, overridden by the finality pair of
    `D`'s attestation, names `L`, then a certificate for `L` at `H` exists along `W` over `Xb`. -/
theorem ownLock_certificateOn_l85e (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} (hv : v ∈ Xb) (r : Round) {H : Height} (hH : H ≠ 0) {L : BlockId} :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r,
    ∀ D, M.duties_attest_with (M.gradeContract n.cache) S.E S.hc (S.node v) n.st n.record ⇢ D →
    M.own_lock
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).record.legacy H
        D.2.2.finality_pair = some L →
    Restated.CertificateOn M S rho W Xb H L := by
  intro n hn D hD hlock
  have hW := hf.onePath
  have hcertOfRecordLock : ∀ {T : BlockId},
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v).record.legacy.lock H = some T →
        Restated.CertificateOn M S rho W Xb H T := by
    intro T hl
    obtain ⟨j, -, t, a, hevent, out, hout, hstep, hemitted, hpair⟩ :=
      recordLock_along₈₅e facts S hW v _ hl
    have hemit : (Restated.Vocabulary.Execution.Run.emits M S rho W v (Object.attest a) t) :=
      ⟨j, hevent, out, hout, hstep, hemitted⟩
    have hshape := Restated.Vocabulary.Proofs.Optimistic.emits_attest_shape facts S W hW hemit
    have hemit' : (Restated.Vocabulary.Execution.Run.emits M S rho W v (Object.attest a) ((Restated.Vocabulary.Execution.Setup.a M S a.round))) := by
      rw [← hshape.2]
      exact hemit
    obtain ⟨n', hn', D', hD'⟩ := (p51% actionAttestation_nonempty₅₁) facts S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round)) v) a.round
      (S.node v)
    have haeq : a = D'.2.2 :=
      ((Restated.action_run_emissionOn facts S rho Hs Xb hf v a.round a).mp hemit').2.2
        n' hn' D' hD'
    exact Restated.fixedRootActionFinalityPair_certificateOn facts S Hs Xb hf hv a.round hH
      n' hn' D' hD' (by rw [← haeq]; exact hpair)
  cases hfp : D.2.2.finality_pair with
  | none =>
    refine hcertOfRecordLock ?_
    rw [hfp, facts.vc.own_lock_none] at hlock
    exact hlock
  | some p =>
    rcases p with ⟨h, target⟩
    by_cases hh : h = H
    · subst hh
      have htarget : target = L := by
        rw [hfp, facts.vc.own_lock_some_self] at hlock
        exact Option.some.inj hlock
      subst htarget
      exact Restated.fixedRootActionFinalityPair_certificateOn facts S Hs Xb hf hv r hH n hn D hD hfp
    · refine hcertOfRecordLock ?_
      rw [hfp, facts.vc.own_lock_some_of_ne _ _ (p := ⟨h, target⟩) hh] at hlock
      exact hlock

/-- Under the bundle, with the family shrinking as time grows and the validators outside the set for
    the horizon weighing less than a third, a certificate for `L` at `H` along `W` read through `Xb`
    has a validator `w` that emitted along `W`, at some instant `t` whose set holds `w`, an
    attestation whose height pair is the target vote `(H, L)`. -/
theorem certificateOn_emittedVote_l85e (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    (hfb : Execution.BelowOneThird S (Hs rho.horizon))
    {H : Height} {L : BlockId} (hc : Restated.CertificateOn M S rho W Xb H L) :
    ∃ (w : V) (t : Int) (a : NamedAttestation V),
      (Restated.Vocabulary.Execution.Run.emits M S rho W w (Object.attest a) t) ∧ w ∈ Hs t ∧
        a.height_pair = NamedHeightPair.vote H L false := by
  classical
  obtain ⟨Q, hQ, hsig⟩ := hc
  obtain ⟨w, hwQ, hwX⟩ : ∃ w ∈ Q, w ∈ Hs rho.horizon := by
    by_contra hno
    push Not at hno
    have hempty : Q ∩ Hs rho.horizon = ∅ := by
      ext w
      simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]
      exact hno w
    have hmeet := Proofs.quorum_meets_set S.E (Hon := Hs rho.horizon) ((isQuorum_iff_q_le S.E Q).mpr hQ)
    rw [hempty] at hmeet
    have h0 : S.E.electorate.weightOf (∅ : Finset V) = 0 := weightOf_empty _
    have hq := Proofs.AlignedRoundLemmas.two_mul_W_le_three_mul_q S.E
    have hfb' : 3 * S.E.electorate.weightOf (Finset.univ \ Hs rho.horizon) < S.E.W := hfb
    omega
  obtain ⟨a, hra, hav, hhp⟩ := hsig w hwQ
  obtain ⟨row, t, herase, hem⟩ := Restated.runAttestation_emitsOn facts S Hs Xb hf hHs hra
    (by rw [hav]; exact hwX)
  rw [hav] at hem
  have ht : t ≤ rho.horizon := by
    obtain ⟨i, hi, -⟩ := hem
    exact (Restated.in_horizonOn facts hf _ (List.mem_of_getElem? hi)).2
  refine ⟨w, t, row, hem, hHs _ _ ht hwX, ?_⟩
  have hT : row.height_pair.erase = HeightPair.target H L := by
    have h1 : row.erase.height_pair = a.erase.height_pair := by rw [herase]
    rw [namedAttestation_erase_height_pair, namedAttestation_erase_height_pair, hhp,
      namedHeightPair_erase_vote_false] at h1
    exact h1
  exact vote_of_erase_target_l85c hT

/-- In the run of the execution `x` up to step `n`, along its path `W`, for a round `c` at least
    three rounds after the deadline round with honest openings at `c` and `c − 1` proposing `P` and
    `P'`, with `S.a c ≤ x[n].time ≤ S.a rW` and `h(T_0) ≤ h(P)`: either every round-`c` attestation
    of every validator not held at `S.a c` is `vote h(P) T_h(P) b`, with `b = false` when
    `nj(P) = false`, or every validator not held at `S.a c` has a justified height at least `h(P)`
    in `W`'s world strictly before `S.a c`. -/
theorem honestRow_atOpening_planned_runAll_l85e (facts : Record.Facts M)
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
  have hf := Restated.admissibleFieldsOn_runAll_notHeld facts S Sched x v₀ n hsync hmono hawake hgst hcv hvalid
    hawm hthird hn
  have hHs : ∀ t t' : Int, t ≤ t' → notHeldAt Sched t' ⊆ notHeldAt Sched t :=
    fun _ _ h => notHeldAt_anti hmono h
  obtain ⟨-, hlo, hpropA⟩ := Restated.openingProposal_runBlock_runAll_l85c facts S Sched x v₀ n hsync hmono
    hawake hgst hcv hvalid hawm hthird hn ((Nat.le_succ _).trans hc3) hhor hopening cp hcp hP
  have hagree := Restated.honestVotes_oneEntry_runAll_l85c facts S Sched x v₀ n hsync hmono hawake hgst hcv
    hvalid hawm hthird hcom hrec hlen htd hA0 hnW htop
  have hrows := fun (u : V) (hu : u ∈ notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c))) =>
    Restated.honestRow_atOpening_runAll_l85c facts S Sched x v₀ n hsync hmono hawake hgst hcv hvalid hawm hthird
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
