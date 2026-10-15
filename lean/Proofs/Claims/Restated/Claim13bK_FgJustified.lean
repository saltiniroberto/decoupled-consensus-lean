import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bK_FinBeforeTick
import Proofs.Claims.Restated.Claim13bPhaseSleepiness
import Proofs.Claims.Restated.Claim13bStepAnchor
import Proofs.Claims.Restated.Claim13bStepAssembly
import Proofs.Claims.Restated.Claim13bStepConeIter
import Proofs.Claims.Restated.Claim13bStepFin
import Proofs.Claims.Restated.Claim13bStepGrade
import Proofs.Claims.Restated.Claim13bStepKit
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bStepKitTick
import Proofs.Claims.Restated.Claim13bStepQuorum
import Proofs.Claims.Restated.Claim13bStepSGMove
import Proofs.Claims.Restated.ProcessIdempotent
import Proofs.Claims.Restated.Projection
import Proofs.Claims.Restated.Vocabulary_Protocol_ChainState_JustificationCertificates
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_JustificationCarrier
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActiveTop
import Model.Conditions.Claim13bK_FgJustified
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13bStepAssembly
import Model.Conditions.Claim13bStepKitTick
import Model.Conditions.Claim13bStepSG
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Execution_Runtime
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring

/-!
# Justified blocks of honest stores

That a store's justified block is genesis or a body named by a quorum of height votes, and by a vote
of an honest validator, and that from the round-`r` tick's successor up to the round-`(r + 1)` tick
step every honest justified block, and the justified block of every honest round-`(r + 1)` action
read, is an ancestor of the round-`r` anchor. Stated over a model `M : Record.Model V`.
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

/-- For a validator honest through step `i`, either its store's justified block is genesis, or the
    store holds a body `Jn` whose erasure is the justified block, the height the store records for
    its own finalized block is at most the store's `h_j`, and some quorum of the electorate has, for
    every member, an attestation included in a body of that store, signed by that member, whose
    height pair is a vote at `h_j` naming `Jn`. -/
theorem justified_certificate_sts (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {i : Nat} {v : V} (hv : Restated.HonestThrough M Sched x i v) :
    (x[i][v].st).st.core.J = Block.genesis ∨
      ∃ Jn : NamedBlock V, Jn ∈ (x[i][v].st).st.bodies ∧
        Jn.erase = (x[i][v].st).st.core.J ∧
        ((x[i][v].st).st.core.σ (x[i][v].st).st.core.F).h ≤ (x[i][v].st).st.core.h_j ∧
        ∃ Q : Finset V, S.E.electorate.IsQuorum Q ∧ ∀ signer ∈ Q,
          ∃ (carrier : NamedBlock V) (a : NamedAttestation V),
            carrier ∈ (x[i][v].st).st.bodies ∧ a ∈ carrier.attestations ∧
            a.val_index = signer ∧
            a.height_pair = NamedHeightPair.vote (x[i][v].st).st.core.h_j Jn.root false := by
  classical
  obtain ⟨D, hDmem, hDJ, hDh⟩ : ∃ D : NamedBlock V, D ∈ (x[i][v].st).st.bodies ∧
      (M.derive_named S.E S.cfg D).J = (x[i][v].st).st.core.J ∧
      (M.derive_named S.E S.cfg D).h_j = (x[i][v].st).st.core.h_j := by
    obtain ⟨w₁, hw₁, hwv⟩ := Record.stateBeforeOf_runOfM M S Sched x facts.nd.wake_events_or_id v i
    have h := Restated.Vocabulary.Proofs.NamedJustificationCarrier.justification_carrier_stateBefore facts
      (Setup.alwaysAwake S) (Record.runOfM M S Sched x v i) (Record.veventsOf M S Sched x v i).length v
      w₁ hw₁
    rw [hwv] at h
    exact h
  by_cases hz : (M.derive_named S.E S.cfg D).h_j = 0
  · left
    rw [← hDJ]
    exact facts.cs.justified_zero_is_genesis S.E S.cfg D hz
  · right
    have hinv := Restated.nodeInvariant_sts facts S Sched x i v
    have hcl : Restated.Vocabulary.Proofs.NamedStore.NamedParentClosed M (x[i][v].st).st := hinv.1.1.1.2.2.1
    obtain ⟨Jn, hJnD, hJne, Q, hQ, hsign⟩ :=
      Restated.Vocabulary.Proofs.NamedJustificationCertificates.justification_certificate facts S.E S.cfg D hz
    have hJnmem : Jn ∈ (x[i][v].st).st.bodies := Restated.mem_bodies_of_preceq hcl hDmem hJnD
    have hheight : ((x[i][v].st).st.core.σ (x[i][v].st).st.core.F).h
        ≤ (x[i][v].st).st.core.h_j := by
      rcases facts.cs.justified_ancestor_height S.E S.cfg D with
        h0 | ⟨J', hJ'D, hJ'e, hJ'h⟩
      · exact absurd h0 hz
      · have hJ'mem : J' ∈ (x[i][v].st).st.bodies := Restated.mem_bodies_of_preceq hcl hDmem hJ'D
        obtain ⟨Fb, hFbmem, hFbe, hFbσ⟩ := Restated.finalized_body_of_store facts S Sched x i v
        have herase : Block.Preceq Fb.erase J'.erase := by
          rw [hFbe, hJ'e, hDJ]
          exact Restated.F_preceq_J_sts facts S Sched x i v
        have hnamed : NamedBlock.Preceq Fb J' :=
          Restated.namedPreceq_of_blockInLog facts S Sched x hexec.idealization
            (Restated.blockInLog_of_mem_bodies facts S Sched hv hFbmem)
            (Restated.blockInLog_of_mem_bodies facts S Sched hv hJ'mem) herase
        rw [hFbσ, ← hDh, ← hJ'h]
        exact facts.cs.derive_height_mono S.E S.cfg hnamed
    refine ⟨Jn, hJnmem, by rw [hJne, hDJ], hheight, Q, hQ, ?_⟩
    intro signer hsigner
    obtain ⟨carrier, a, hcarrier, ha, hval, hpair⟩ := hsign signer hsigner
    refine ⟨carrier, a, Restated.mem_bodies_of_preceq hcl hDmem hcarrier, ha, hval, ?_⟩
    rw [hpair, hDh]

end

section
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The attestations `v`'s round-`r` action read can compute from the node state `v`'s tick reads at
    time `t` from configuration `c` are those it can compute from `v`'s node state in `c`. -/
private theorem actionAttestationFrom_wakeStageFgj (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (t : Int) (c : Config V (NamedObject V) M.N) (v : V) (r : Round) :
    Restated.actionAttestationFrom M S (Record.wakeStage M Sched t c v) v r =
      Restated.actionAttestationFrom M S (c[v].st) v r := by
  unfold Restated.actionAttestationFrom Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom
  rw [Record.wakeStage_st facts, Record.wakeStage_cache facts, Record.wakeStage_record facts]

/-- From any node state `before`, validator `v`'s round-`r` action read can compute some
    attestation. -/
private theorem actionAttestationFrom_nonempty_fgj (facts : Record.Facts M) (S : Setup V)
    (before : M.N) (v : V) (r : Round) :
    ∃ a, a ∈ Restated.actionAttestationFrom M S before v r := by
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc before.st.core.toHealing
    (Restated.Vocabulary.Execution.Setup.a M S r) before.cache
  obtain ⟨st, hst⟩ := facts.dt.duties_update_confirmation_with_nonempty (M.gradeContract c) S.E S.hc
    (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r))
    (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1)
  obtain ⟨D, hD⟩ := facts.dt.attest_with_nonempty (M.gradeContract (M.mkNode st before.record c).cache)
    S.E S.hc (S.node v) (M.mkNode st before.record c).st (M.mkNode st before.record c).record
  exact ⟨D.2.2, M.mkNode st before.record c, ⟨c, hc, st, hst, rfl⟩, D.1, D.2.1, hD⟩

/-- If `a` equals every attestation validator `q`'s round-`ρ` action read from `before` can compute,
    then `a`'s validator index is `q`. -/
private theorem val_index_of_eq_every_fgj (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (q : V) (ρ : Round) (a : NamedAttestation V)
    (heq : ∀ a' ∈ Restated.actionAttestationFrom M S before q ρ, a = a') :
    a.val_index = q := by
  obtain ⟨a₁, ha₁⟩ := actionAttestationFrom_nonempty_fgj facts S before q ρ
  rw [heq a₁ ha₁]
  exact Restated.actionAttestationFrom_val_index facts S before q ρ a₁ ha₁

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Either a validator's justified block is genesis, or its store holds a body `Jn` erasing to that
    justified block, the height the store records for its own finalized block is at most the store's
    `h_j`, and some validator `v'`, honest through the successor of its own send step and held by
    the adversary at no time up to the opening of round `r₀ + 1`, signed at its tick at that round's
    action time, a step before the read, an attestation `a` whose height pair is a vote at `h_j`
    naming `Jn`, and every attestation `v'`'s action read at that step can compute is `a`. -/
theorem justified_honest_target_ofRoundSleepinessW (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) {tE : Int}
    (hrsW : Restated.roundSleepinessW M S Sched tE)
    {r₀ : Round} (hr₀ : 1 ≤ r₀) (htE : tE ≤ M.opening S.E S.hc r₀)
    {i : Nat} {v : V} (hv : Restated.HonestThrough M Sched x i v)
    (hi : (x[i].time : Int) ≤ M.opening S.E S.hc (r₀ + 1)) :
    (x[i][v].st).st.core.J = Block.genesis ∨
      ∃ (Jn : NamedBlock V) (v' : V) (a : NamedAttestation V) (k : Nat),
        Jn ∈ (x[i][v].st).st.bodies ∧
        Jn.erase = (x[i][v].st).st.core.J ∧
        ((x[i][v].st).st.core.σ (x[i][v].st).st.core.F).h ≤ (x[i][v].st).st.core.h_j ∧
        k < i ∧ Restated.tickStepAt M x k ((Restated.Vocabulary.Execution.Setup.a M S a.round)) ∧ v' ∈ Sched.awake ((Restated.Vocabulary.Execution.Setup.a M S a.round)) ∧
        Restated.HonestThrough M Sched x (k + 1) v' ∧
        HonestThroughTime Sched (M.opening S.E S.hc (r₀ + 1)) v' ∧
        (∀ a' ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[k][v'].st) v' a.round,
          a = a') ∧
        (⟨v', NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[k + 1].sent ∧
        a.height_pair = NamedHeightPair.vote (x[i][v].st).st.core.h_j Jn.root false := by
  classical
  rcases Restated.justified_certificate_sts facts S Sched x hexec hv with
    hgen | ⟨Jn, hJnmem, hJne, hheight, Q, hQ, hsign⟩
  · exact Or.inl hgen
  · right
    obtain ⟨v', hqQ, hqadv⟩ := Restated.exists_nonAdv_of_quorum facts S Sched hrsW hr₀ htE
      ((isQuorum_iff_q_le S.E Q).mp hQ)
    have hqhon : Restated.HonestThrough M Sched x i v' := by
      intro t ht hmem
      exact hqadv (hmono t (M.opening S.E S.hc (r₀ + 1)) (le_trans ht hi) hmem)
    obtain ⟨carrier, a, hcarrier, ha, hval, hpair⟩ := hsign v' hqQ
    have hlog : (⟨a.val_index, NamedObject.attest a⟩ : SignedMsg V (NamedObject V))
        ∈ x[i].sent :=
      Restated.carried_vote_in_log facts S Sched x hexec hcarrier ha (by rw [hval]; exact hqhon)
    have hlog' : (⟨v', NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[i].sent := by
      rw [← hval]; exact hlog
    have hhonT : HonestThroughTime Sched ((x[i].time : Int)) v' := fun t ht => hqhon t ht
    obtain ⟨-, k, hki, htick, hawk, out, hout, hemit⟩ :=
      Restated.attest_round_of_sent facts S Sched x (tB := (x[i].time : Int)) hhonT
        hexec.toUnforgeability hval (le_refl _) hlog'
    have heq : ∀ a' ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[k][v'].st) v' a.round,
        a = a' := by
      rw [← actionAttestationFrom_wakeStageFgj facts (Setup.alwaysAwake S) Sched
        (Restated.Vocabulary.Execution.Setup.a M S a.round) x[k] v' a.round]
      have _hr_s1 := Record.reachedNode_wakeStage facts S Sched x (k) v' (Restated.Vocabulary.Execution.Setup.a M S a.round)
      have _hv_s2 := Record.runs_as_wakeStage facts S Sched x (k) v' (Restated.Vocabulary.Execution.Setup.a M S a.round)
      exact Restated.attest_of_tick_eq facts S v' _ a.round hout hemit
    obtain ⟨a₁, ha₁⟩ := actionAttestationFrom_nonempty_fgj facts (Setup.alwaysAwake S)
      (x[k][v'].st) v' a.round
    have hsent : (⟨v', NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[k + 1].sent := by
      rw [heq a₁ ha₁]
      -- the tick sends `a`, so the node state it reads passes the grade-2 awake test of `a`'s round
      exact Restated.attest_emitted_at_tick_from facts S Sched x htick hawk ⟨out, hout⟩
        (facts.nd.tick_attestation_fields (Setup.alwaysAwake S) v' _ _ (Record.runs_as_wakeStage facts S Sched x _ _ _) out hout a hemit).2.1 a₁ ha₁
    have hqk : Restated.HonestThrough M Sched x (k + 1) v' := by
      intro t ht hmem
      refine hqadv (hmono t (M.opening S.E S.hc (r₀ + 1)) ?_ hmem)
      exact le_trans ht
        (le_trans (Restated.time_mono_int facts S Sched x (Nat.succ_le_of_lt hki)) hi)
    have hqT : HonestThroughTime Sched (M.opening S.E S.hc (r₀ + 1)) v' :=
      fun t ht hmem => hqadv (hmono t (M.opening S.E S.hc (r₀ + 1)) ht hmem)
    exact ⟨Jn, v', a, k, hJnmem, hJne, hheight, hki, htick, (Finset.mem_sdiff.1 hawk).1, hqk,
      hqT, heq, hsent, hpair⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If step `n` is the tick at `S.a r` and step `n'` the tick at `S.a (r + 1)`, then `n + 1 ≤ n'`. -/
theorem tick_succ_le_tick_succ_round (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {r : Round} {n n' : Nat}
    (hn : Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S r))) (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1)))) : n + 1 ≤ n' := by
  by_contra hcon
  have hle : n' + 1 ≤ n + 1 := by omega
  have ht := Restated.time_mono_int facts S Sched x hle
  rw [(Restated.tickStepAt_time facts x hn').1, (Restated.tickStepAt_time facts x hn).1] at ht
  -- round `r + 1`'s action is `4 * R` delays after round `r`'s
  have h2 := facts.gr.action_succ_eq_add_rounds S r
  have hR : (0 : Int) < (S.hc.R : Int) := by
    have := S.hc.R_ge_three
    exact_mod_cast (show 0 < S.hc.R by omega)
  have hpos : (0 : Int) < 4 * (S.hc.R : Int) * S.E.Δ :=
    mul_pos (mul_pos (by norm_num) hR) S.E.Δ_pos
  linarith

end

section
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The action time of round `ρ` is at or before the opening of round `ρ + 1`. -/
private theorem action_le_opening_succ_of_facts (facts : Record.Facts M) (S : Setup V) (ρ : Round) :
    (Restated.Vocabulary.Execution.Setup.a M S ρ) ≤ M.opening S.E S.hc (ρ + 1) := by
  have h1 := facts.gr.action_delta_le_early S S.hc.R_ge_three (Nat.lt_succ_self ρ)
  have h2 := facts.gr.early_g2_le_opening S (ρ + 1)
  have hd := S.E.Δ_pos
  show M.a S.hc S.E.Δ _ ≤ _
  linarith

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If the reshaped invariant holds at round `r` with tick step `n` and anchor `T`, step `n'` is the
    tick at `S.a (r + 1)`, and `roundSleepinessW` holds from a time `tE` at or before round
    `r + 1`'s opening, then the justified block of a validator honest through its own read, at any
    step from `n + 1` up to `n'`, is an ancestor of `T`. -/
theorem justified_old_anchor_before_succ_tick (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) {tE : Int}
    (hrsW : Restated.roundSleepinessW M S Sched tE)
    {r : Round} {n n' : Nat} {T : NamedBlock V}
    (hinv : Restated.AfterPhaseInvariantOverActiveSetsTop M S Sched x r n T)
    (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    (htE : tE ≤ M.opening S.E S.hc (r + 1))
    (hjust : Restated.StepJustifiedRootUnderAnchor M S Sched x r n n' T) :
    ∀ (v : V) (n₁ : Nat), n + 1 ≤ n₁ → n₁ ≤ n' → Restated.HonestThrough M Sched x n₁ v →
      (x[n₁][v].st).st.core.h_max = (x[n₁][v].st).st.core.h_j + 1 →
      Block.Preceq (x[n₁][v].st).st.core.J T.erase := by
  classical
  intro v n₁ hbig hn₁ hv hroot
  by_cases hlow : (x[n₁][v].st).st.core.h_j < (M.derive_named S.E S.cfg T).h
  · exact hjust v n₁ hbig hn₁ hv hroot hlow
  have hvn : Restated.HonestThrough M Sched x (n + 1) v := by
    intro t ht
    exact hv t (le_trans ht (Restated.time_mono_int facts S Sched x hbig))
  have htime : (x[n₁].time : Int) ≤ M.opening S.E S.hc (r + 1 + 1) := by
    refine le_trans (Restated.time_mono_int facts S Sched x (Nat.le_succ_of_le hn₁)) ?_
    rw [(Restated.tickStepAt_time facts x hn').1]
    exact action_le_opening_succ_of_facts facts S (r + 1)
  rcases Restated.justified_honest_target_ofRoundSleepinessW facts S Sched x hexec hmono hrsW (r₀ := r + 1)
    (Nat.le_add_left 1 r) htE hv htime with
    hgen | ⟨Jn, q, a, k, hJnmem, hJne, hheight, hkn₁, htick, -, hqk, -, heq, hsent, hpair⟩
  · rw [hgen]
    exact (preceq_eq_true_iff_Preceq.mp (Protocol.preceq_genesis _))
  · rw [← hJne]
    have hround : a.round ≤ r :=
      Restated.round_le_of_tick_lt facts S Sched x htick hn' (Nat.lt_of_lt_of_le hkn₁ hn₁)
    have hkn : k ≤ n := Restated.tick_le_of_round_le facts S Sched x htick hinv.tick hround
    have hstep : k + 1 ≤ n + 1 := Nat.succ_le_succ hkn
    have hidx : a.val_index = q :=
      val_index_of_eq_every_fgj facts (Setup.alwaysAwake S) _ q a.round a heq
    have hh := hinv.heightCeiling q (k + 1) a _ Jn.root false hstep hqk hidx hsent hpair
    have heqh : (x[n₁][v].st).st.core.h_j = (M.derive_named S.E S.cfg T).h :=
      le_antisymm hh (Nat.le_of_not_lt hlow)
    rw [heqh] at hpair
    exact hinv.targetsTop q (k + 1) a Jn.root false hstep hqk hidx hsent hpair Jn
      (Restated.blockInLog_of_mem_bodies facts S Sched hv hJnmem) rfl

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If round `r` is at or after the switch round, the reshaped invariant holds at round `r` with
    tick step `n` and anchor `T`, step `n'` is the tick at `S.a (r + 1)`, and the phase
    premises about `tGAT`, the one-third bound, the phase-awake condition and
    `roundSleepinessW` hold, then the justified block of a validator honest through its own read, at
    any step from `n + 1` up to `n'`, is an ancestor of `T`. -/
theorem justified_old_anchor_before_succ_tick_of_hypotheses (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE)
    {r : Round} {n n' : Nat} {T : NamedBlock V}
    (hr : Restated.switchRound M S tE ≤ r) (hinv : Restated.AfterPhaseInvariantOverActiveSetsTop M S Sched x r n T)
    (hjust : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepJustifiedRootUnderAnchor M S Sched x r n n'' T)
    (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1)))) :
    ∀ (v : V) (n₁ : Nat), n + 1 ≤ n₁ → n₁ ≤ n' → Restated.HonestThrough M Sched x n₁ v →
      (x[n₁][v].st).st.core.h_max = (x[n₁][v].st).st.core.h_j + 1 →
      Block.Preceq (x[n₁][v].st).st.core.J T.erase :=
  Restated.justified_old_anchor_before_succ_tick facts S Sched x hexec hmono (tE := Restated.switchOpening M S tE)
    (Restated.roundSleepinessW_switchOpening_of_phase facts S Sched tGAT tE gap hgst hlen hmono hthird hphase
      hrsW)
    hinv hn' (Restated.switchOpening_le_opening facts S (le_trans hr (Nat.le_succ r))) (hjust n' hn')

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Every healing store a round's action read can compute has the justified block of the store it
    reads. -/
theorem actionHealingStore_J (facts : Record.Facts M) (S : Setup V) (before : M.N) (r₁ : Round) :
    ∀ hs ∈ Restated.actionHealingStore M S before r₁, hs.J = before.st.core.J := by
  intro hs hhs
  obtain ⟨c, hc, X, hX, st₀, hst₀, rfl⟩ := Restated.actionHealingStore_eq facts S before r₁ hs hhs
  obtain ⟨hF₀, hJ₀, hhj₀, hhm₀, hlc₀, hT₀, hs₀, hσ₀⟩ :=
    Restated.HS_fields_store_with_cache facts c hst₀
  simp only [hF₀, hJ₀, hhj₀, hhm₀, hlc₀, hT₀, hs₀, hσ₀] at *
  rw [Record.Model.HS.J, facts.dt.update_confirmation_with_toHealing_J _ _ _ _ _ X hX,
    facts.hd.setClock_toHealing_J]

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If every honest justified block from step `n + 1` up to the round-`(r + 1)` tick step `n'` is an
    ancestor of `T`, and `n + 1 ≤ n'`, then for every validator the adversary holds at no time up to
    `S.a (r + 1)` and every healing store `hs` its round-`(r + 1)` action read can compute, if
    `hs.h_max = hs.h_j + 1` then `hs`'s justified block is an ancestor of `T`. -/
theorem actionJ_preceq_old_anchor (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {r : Round} {n n' : Nat} {T : NamedBlock V}
    (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1)))) (hnn' : n + 1 ≤ n')
    (hjus : ∀ (v : V) (n₁ : Nat), n + 1 ≤ n₁ → n₁ ≤ n' → Restated.HonestThrough M Sched x n₁ v →
      (x[n₁][v].st).st.core.h_max = (x[n₁][v].st).st.core.h_j + 1 →
      Block.Preceq (x[n₁][v].st).st.core.J T.erase) :
    ∀ v ∈ honestThroughSet Sched ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))),
      ∀ hs ∈ Restated.actionHealingStore M S (x[n'][v].st) (r + 1),
        (hs : M.HS).h_max = hs.h_j + 1 → Block.Preceq hs.J T.erase := by
  intro v hv hs hhs hroot
  rw [Restated.actionHealingStore_h_max facts S _ _ hs hhs,
    Restated.actionHealingStore_h_j facts S _ _ hs hhs] at hroot
  rw [actionHealingStore_J facts S _ _ hs hhs]
  refine hjus v n' hnn' le_rfl ?_ hroot
  have hvT : HonestThroughTime Sched ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) v := mem_honestThroughSet.mp hv
  have htn : (x[n'].time : Int) ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) := by
    rw [← (Restated.tickStepAt_time facts x hn').1]
    exact Restated.time_mono_int facts S Sched x (Nat.le_succ n')
  intro t ht
  exact hvT t (le_trans ht htn)

end

end DecoupledConsensusModel.Sts.Restated
