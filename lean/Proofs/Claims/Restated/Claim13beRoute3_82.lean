import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bInvariantActiveSince
import Proofs.Claims.Restated.Claim13bK_FgJustified
import Proofs.Claims.Restated.Claim13bK_FinBeforeTick
import Proofs.Claims.Restated.Claim13bPhaseSleepiness
import Proofs.Claims.Restated.Claim13bStepActiveAssembly
import Proofs.Claims.Restated.Claim13bStepActiveSince
import Proofs.Claims.Restated.Claim13bStepAnchor
import Proofs.Claims.Restated.Claim13bStepAssembly
import Proofs.Claims.Restated.Claim13bStepConeIter
import Proofs.Claims.Restated.Claim13bStepFin
import Proofs.Claims.Restated.Claim13bStepGrade
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bStepKitStore
import Proofs.Claims.Restated.Claim13bStepKitTick
import Proofs.Claims.Restated.Claim13bStepQuorum
import Proofs.Claims.Restated.Claim13beRoute3_72
import Proofs.Claims.Restated.Claim13beRoute3_83
import Proofs.Claims.Restated.ProcessedFlip
import Proofs.Claims.Restated.Projection
import Proofs.Claims.Restated.RunAll
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_Staleness
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActiveSince
import Model.Conditions.Claim13bInvariantActiveTop
import Model.Conditions.Claim13bK_FgJustified
import Model.Conditions.Claim13bK_FinBeforeTick
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13bStepActiveAssembly
import Model.Conditions.Claim13bStepAnchor
import Model.Conditions.Claim13bStepAssembly
import Model.Conditions.Claim13bStepFieldsAt
import Model.Conditions.Claim13bStepKitTick
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_72
import Model.Conditions.Claim13beRoute3_74
import Model.Conditions.Claim13beRoute3_82
import Model.Conditions.Claim13beRoute3_83
import Model.Conditions.ProcessedFlip
import Model.Conditions.RunAll
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13bd
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring

/-!
# Justified and finalized blocks after the switch round

Theorems over a model `M : Record.Model V` and its facts about an execution `x`: the tick at a
round's action instant emits no block, a store's justified height never decreases, and from the
switch round's tick step on every honest justified and finalized block is an ancestor of the round's
anchor. From these, the after-phase step carries the invariant from each round at or after the
switch round to the next.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

local macro "pKS% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13bStepKitStore)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p74% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_74)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p83% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_83)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Whatever node state `st` the validator `v` holds, every outcome of its tick at a round's action
    instant emits no block. -/
theorem namedTick_action_emits_no_block (facts : Record.Facts M) (S : Setup V) (v : V) (st : M.N)
    (ρ : Round) (B : NamedBlock V) : ∀ out₁, M.tick (Setup.alwaysAwake S) v st ((Restated.Vocabulary.Execution.Setup.a M S ρ)) ⇢ out₁ → 
    ∀ (hn : M.reachedNode st := by trivial) (hv : M.runs_as st v := by trivial),
    NamedObject.block B ∉ out₁.2 := by
  intro out₁ hout _hn _hv
  -- case: the grade-2 awake test fails, and the tick sends nothing
  by_cases hrun : M.awake_for_grade2 (Setup.alwaysAwake S) v st ρ
  swap
  · rw [facts.nd.tick_at_action_asleep (Setup.alwaysAwake S) v st ρ out₁ hout hrun]
    simp
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty (Setup.alwaysAwake S).E (Setup.alwaysAwake S).hc
    st.st.core.toHealing (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) ρ) st.cache
  obtain ⟨st', hst'⟩ := facts.dt.duties_update_confirmation_with_nonempty (M.gradeContract c)
    (Setup.alwaysAwake S).E (Setup.alwaysAwake S).hc
    (M.ns_setClock (Setup.alwaysAwake S).E st.st
      (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) ρ))
    ((Setup.alwaysAwake S).E.slotOf (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) ρ) - 1)
  obtain ⟨D, hD⟩ := facts.dt.attest_with_nonempty (M.gradeContract c) (Setup.alwaysAwake S).E
    (Setup.alwaysAwake S).hc ((Setup.alwaysAwake S).node v) st' st.record
  rw [facts.nd.tick_at_action_awake (Setup.alwaysAwake S) v st ρ out₁ hout c hc st' hst' D hD hrun]
  simp

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If step `n'` is the tick at a round's action instant, a block `v`'s store holds after `n' + 1`
    steps includes an attestation `a`, and `a`'s signer is honest through `n' + 1`, then `a`, signed
    by its signer, is in the sent log after `n'` steps. -/
theorem carried_vote_in_log_before_tick (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {n' : Nat} {ρ : Round} (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S ρ))) {v : V}
    {carrier : NamedBlock V} (hc : carrier ∈ (x[n' + 1][v].st).st.bodies)
    {a : NamedAttestation V} (ha : a ∈ carrier.attestations)
    (hq : Restated.HonestThrough M Sched x (n' + 1) a.val_index) :
    (⟨a.val_index, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n'].sent := by
  have _hr_0 : M.reachedNode (x[0][v].st) := Record.reachedNode_sts facts S Sched x 0 v
  have _hr_1 : M.reachedNode (x[n' + 1][v].st) := Record.reachedNode_sts facts S Sched x (n' + 1) v
  classical
  have hnotgen : carrier ≠ NamedBlock.genesis := by
    intro hgen
    rw [hgen] at ha
    rw [named_genesis_attestations] at ha
    simp only [List.not_mem_nil] at ha
  have h0 : Restated.Vocabulary.Execution.Object.processed M (x[0][v].st).st
      (NamedObject.block carrier) = false := by
    rw [Record.st_zero M S Sched x v]
    simp only [Restated.Vocabulary.Execution.Object.processed, decide_eq_false_iff_not]
    exact fun h => hnotgen (facts.nd.initial_body_eq_genesis _ _ h)
  have hm : Restated.Vocabulary.Execution.Object.processed M (x[n' + 1][v].st).st
      (NamedObject.block carrier) = true := by
    simp only [Restated.Vocabulary.Execution.Object.processed, decide_eq_true_eq]
    exact hc
  obtain ⟨i, him, hf0, hf1⟩ :=
    Restated.exists_first_flip facts S Sched x v (NamedObject.block carrier) (n' + 1) h0 hm
  have hcarries : carries (NamedObject.block carrier) (NamedObject.attest a) :=
    Or.inr ⟨a, ha, rfl⟩
  have hauthor : NamedObject.author (NamedObject.attest a) = some a.val_index :=
    author_attest a
  rcases Restated.flip_step_cases facts S Sched x hf0 hf1 with
    ⟨sm, hlbl, -, -, hpay⟩ | ⟨τ, hlbl, haw, hdvd, out₁, hout₁, hst₁, hem⟩
  · have hsm : sm ∈ x[i].sent := (Restated.sent_of_deliver facts S Sched x hlbl).1
    have hmsg : sm.msg = NamedObject.block carrier := by
      rcases hpay with h | ⟨Bl, -, hcc⟩
      · exact h
      · exact hcc.elim
    have hhon : Restated.HonestThrough M Sched x i a.val_index := fun t ht =>
      hq t (le_trans ht (Restated.time_mono_int facts S Sched x (le_of_lt him)))
    have hres := hexec.carried i sm (NamedObject.attest a) a.val_index hsm
      (by rw [hmsg]; exact hcarries) hauthor hhon
    exact Restated.mem_sent_of_le facts x (Nat.le_of_lt_succ him) hres
  · rcases hem with hmem | ⟨Bl, -, hcc⟩
    · rcases Nat.lt_or_ge i n' with hlt | hge
      · have hsend := facts.nd.tick_send_eq_of_state (Setup.alwaysAwake S) v
          (Record.wakeStage M Sched (τ : Int) x[i] v) (τ : Int)
        have hsent := Restated.mem_sent_of_tick_of_state facts S Sched x hlbl haw hdvd hsend hout₁
          hst₁ hmem
        have hhon : Restated.HonestThrough M Sched x (i + 1) a.val_index := fun t ht =>
          hq t (le_trans ht (Restated.time_mono_int facts S Sched x (Nat.succ_le_of_lt him)))
        have hres := hexec.carried (i + 1) ⟨v, NamedObject.block carrier⟩
          (NamedObject.attest a) a.val_index hsent hcarries hauthor hhon
        exact Restated.mem_sent_of_le facts x (Nat.succ_le_of_lt hlt) hres
      · have hin : i = n' := le_antisymm (Nat.le_of_lt_succ him) hge
        subst hin
        obtain ⟨t', hl', ht'⟩ := hn'
        rw [hlbl] at hl'
        injection hl' with hτ
        subst hτ
        rw [ht'] at hout₁
        have _hr_s1 := Record.reachedNode_wakeStage facts S Sched x (i) v (Restated.Vocabulary.Execution.Setup.a M S ρ)
        have _hv_s1 := Record.runs_as_wakeStage facts S Sched x (i) v (Restated.Vocabulary.Execution.Setup.a M S ρ)
        exact absurd hmem (Restated.namedTick_action_emits_no_block facts S v _ ρ carrier out₁ hout₁)
    · exact hcc.elim

end

section
set_option autoImplicit false
open scoped DC
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For `i ≤ j`, the justified height of `v`'s store after `i` steps is at most the one after `j`
    steps. -/
theorem h_j_mono_sts (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v : V) {i j : Nat} (hij : i ≤ j) :
    (x[i][v].st).st.core.h_j ≤ (x[j][v].st).st.core.h_j := by
  have hlen : (Record.veventsOf M S Sched x v i).length ≤ (Record.veventsOf M S Sched x v j).length :=
    (Restated.vevents_prefix facts S Sched x v hij).length_le
  obtain ⟨w₁, hw₁, hw₁v⟩ := Restated.stateBefore_runOf_of_le facts S Sched x v hij
  obtain ⟨w₂, hw₂, hw₂v⟩ := (pKS% fold_veventsOf_drop) facts S Sched x v hij w₁ hw₁v
  have hw₂' : w₂ ∈ (((Record.runOfM M S Sched x v j).events.drop
      (Record.veventsOf M S Sched x v i).length).take
      ((Record.veventsOf M S Sched x v j).length - (Record.veventsOf M S Sched x v i).length)).foldlM
      (Record.worldStepOf M (Setup.alwaysAwake S)) w₁ := by
    show w₂ ∈ (((Record.veventsOf M S Sched x v j).drop
      (Record.veventsOf M S Sched x v i).length).take _).foldlM _ w₁
    rw [List.take_of_length_le (by simp)]
    exact hw₂
  have h := Restated.Vocabulary.Proofs.HealingSurface.stateBefore_h_j_mono facts
    (Setup.alwaysAwake S) (Record.runOfM M S Sched x v j) v hlen w₁ hw₁ w₂ hw₂'
  rw [hw₁v, hw₂v] at h
  exact h

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If the round-level sleepiness bound holds from an instant `tE` at or before round `(r + 1)`'s
    opening, step `n'` is the tick at `S.a (r + 1)`, and `v` is honest through a step `i ≤ n' + 1`,
    then `v`'s justified block after `i` steps is genesis, or `v`'s store holds a body `Jn` erasing
    to it and some validator honest through `n' + 1` signed an attestation of a round at most `r`,
    sent at that round's tick step, whose height pair is a vote at `v`'s `h_j` naming `Jn`. -/
theorem justified_honest_vote_before_succ_tick (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) {tE : Int}
    (hrsW : Restated.roundSleepinessW M S Sched tE)
    {r : Round} {n' : Nat} (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    (htE : tE ≤ M.opening S.E S.hc (r + 1))
    {i : Nat} (hi : i ≤ n' + 1) {v : V} (hv : Restated.HonestThrough M Sched x i v) :
    (x[i][v].st).st.core.J = Block.genesis ∨
      ∃ (Jn : NamedBlock V) (v' : V) (a : NamedAttestation V) (k : Nat),
        Jn ∈ (x[i][v].st).st.bodies ∧
        Jn.erase = (x[i][v].st).st.core.J ∧
        k < n' ∧ Restated.tickStepAt M x k ((Restated.Vocabulary.Execution.Setup.a M S a.round)) ∧ a.round ≤ r ∧
        Restated.HonestThrough M Sched x (n' + 1) v' ∧ a.val_index = v' ∧
        (⟨v', NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[k + 1].sent ∧
        a.height_pair = NamedHeightPair.vote (x[i][v].st).st.core.h_j Jn.root false := by
  classical
  rcases Restated.justified_certificate_sts facts S Sched x hexec hv with
    hgen | ⟨Jn, hJnmem, hJne, -, Q, hQ, hsign⟩
  · exact Or.inl hgen
  · right
    obtain ⟨v', hqQ, hqadv⟩ :=
      Restated.exists_nonAdv_of_quorum facts S Sched hrsW (r₀ := r + 1) (Nat.le_add_left 1 r) htE ((isQuorum_iff_q_le S.E Q).mp hQ)
    have htn' : (x[n' + 1].time : Int) ≤ M.opening S.E S.hc (r + 1 + 1) := by
      rw [(Restated.tickStepAt_time facts x hn').1]
      have h1 := facts.gr.action_delta_le_early S S.hc.R_ge_three (Nat.lt_succ_self (r + 1))
      have h2 := facts.gr.early_g2_le_opening S (r + 1 + 1)
      have hd := S.E.Δ_pos
      show M.a S.hc S.E.Δ _ ≤ _
      linarith
    have hqhon : Restated.HonestThrough M Sched x (n' + 1) v' := by
      intro t ht hmem
      exact hqadv (hmono t (M.opening S.E S.hc (r + 1 + 1)) (le_trans ht htn') hmem)
    obtain ⟨carrier, a, hcarrier, ha, hval, hpair⟩ := hsign v' hqQ
    have hlogn' : (⟨v', NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n'].sent := by
      rw [← hval]
      rcases Nat.lt_or_ge i (n' + 1) with hlt | hge
      · have hqi : Restated.HonestThrough M Sched x i a.val_index := by
          rw [hval]
          intro t ht
          exact hqhon t (le_trans ht (Restated.time_mono_int facts S Sched x hi))
        exact Restated.mem_sent_of_le facts x (Nat.le_of_lt_succ hlt)
          (Restated.carried_vote_in_log facts S Sched x hexec hcarrier ha hqi)
      · have hieq : i = n' + 1 := le_antisymm hi hge
        subst hieq
        exact Restated.carried_vote_in_log_before_tick facts S Sched x hexec hn' hcarrier ha
          (by rw [hval]; exact hqhon)
    have hhonT : HonestThroughTime Sched ((x[n'].time : Int)) v' := fun t ht =>
      hqhon t (le_trans ht (Restated.time_mono_int facts S Sched x (Nat.le_succ n')))
    obtain ⟨-, k, hkn', htick, hawk, out, hout, hmemout⟩ :=
      Restated.attest_round_of_sent facts S Sched x hhonT hexec.toUnforgeability hval (le_refl _) hlogn'
    obtain ⟨na, hna⟩ := (p74% actionReadFrom_nonempty₇₄) facts (Setup.alwaysAwake S)
      (x[k][v'].st) a.round
    obtain ⟨D, hD⟩ := facts.dt.attest_with_nonempty (M.gradeContract na.cache) (Setup.alwaysAwake S).E
      (Setup.alwaysAwake S).hc ((Setup.alwaysAwake S).node v') na.st na.record
    have _hr_s2 := Record.reachedNode_wakeStage facts S Sched x (k) v' (Restated.Vocabulary.Execution.Setup.a M S a.round)
    have _hv_s3 := Record.runs_as_wakeStage facts S Sched x (k) v' (Restated.Vocabulary.Execution.Setup.a M S a.round)
    have heq : a = D.2.2 :=
      Restated.attest_of_tick_eq facts S v' _ a.round hout hmemout D.2.2
        (by
          rw [Restated.actionAttestationFrom_wakeStage facts _ Sched _ x[k] v' a.round]
          exact ⟨na, hna, D.1, D.2.1, hD⟩)
    have hrun : M.awake_for_grade2 (Setup.alwaysAwake S) v'
        (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S a.round) x[k] v') a.round := by
      by_contra hno
      have hnil := facts.nd.tick_at_action_asleep (Setup.alwaysAwake S) v' _ a.round out hout hno
      rw [hnil] at hmemout
      simp at hmemout
    have hsent : (⟨v', NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[k + 1].sent := by
      have hs := Restated.attest_emitted_at_tick_from facts S Sched x htick hawk ⟨out, hout⟩ hrun D.2.2
        ⟨na, hna, D.1, D.2.1, hD⟩
      rw [← heq] at hs
      exact hs
    have hround : a.round ≤ r := Restated.round_le_of_tick_lt facts S Sched x htick hn' hkn'
    exact ⟨Jn, v', a, k, hJnmem, hJne, hkn', htick, hround, hqhon, hval, hsent, hpair⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Given the invariant's clauses at round `r` for tick step `n` (`hntick`), height ceiling
    (`hceil`) and targets since the switch round (`htgt`), and step `n'` the tick at `S.a (r + 1)`:
    whatever a validator honest through its own read holds as its justified block, at any step from
    the switch round's tick step `n_W` up to `n' + 1`, is an ancestor of `T`. -/
theorem justified_preceq_anchor_after_switch_ofClauses (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hsync : Restated.SynchronyFromWake M S x)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE)
    (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    (hprev : ∀ r : Round, Restated.deadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
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
        (Restated.runAllPath M S Sched x v N) T)
    (hclear : ∀ r : Round, Restated.deadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
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
      Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T)
    (hB : Restated.BaseJustifiedHighAtSwitchRound M S Sched x tGAT tE gap)
    {T_W : NamedBlock V} (hAW : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.switchRound M S tE) T_W)
    {n_W : Nat} (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    {r : Round} {n n' : Nat} {T : NamedBlock V}
    (hr : Restated.switchRound M S tE ≤ r)
    (hntick : Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S r)))
    (hceil : ∀ (v : V) (n₂ : Nat) (a : NamedAttestation V) (h' : Height)
      (entry : BlockId) (tmo : Bool),
      n₂ ≤ n + 1 → Restated.HonestThrough M Sched x n₂ v → a.val_index = v →
      (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n₂].sent →
      a.height_pair = NamedHeightPair.vote h' entry tmo →
      h' ≤ (M.derive_named S.E S.cfg T).h)
    (htgt : ∀ (v' : V) (n₂ : Nat) (a : NamedAttestation V) (h' : Height) (entry : BlockId)
        (tmo : Bool),
      n₂ ≤ n + 1 → Restated.HonestThrough M Sched x n₂ v' → a.val_index = v' →
      (⟨v', NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n₂].sent →
      (⟨v', NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∉ x[n_W].sent →
      a.height_pair = NamedHeightPair.vote h' entry tmo →
      h' ≤ (M.derive_named S.E S.cfg T).h →
      ∀ C : NamedBlock V, Restated.blockInLog M S Sched x C → C.root = entry →
      Block.Preceq C.erase T.erase)
    (hTW : Block.Preceq T_W.erase T.erase)
    (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1)))) :
    ∀ (v : V) (n₁ : Nat), n_W ≤ n₁ → n₁ ≤ n' + 1 → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J T.erase := by
  classical
  intro v n₁ hWn₁ hn₁ hv
  have hrsW' := Restated.roundSleepinessW_switchOpening_of_phase facts S Sched tGAT tE gap hgst hlen hmono
    hthird hphase hrsW
  have htE' := Restated.switchOpening_le_opening facts S (le_trans hr (Nat.le_succ r))
  rcases Restated.justified_honest_vote_before_succ_tick facts S Sched x hexec hmono hrsW' hn' htE' hn₁ hv with
    hgen | ⟨Jn, v', a, k, hJnmem, hJne, hkn', htk, hround, hqhon, hidx, hsent, hpair⟩
  · rw [hgen]
    exact (preceq_eq_true_iff_Preceq.mp (Protocol.preceq_genesis _))
  · rw [← hJne]
    have hJnlog : Restated.blockInLog M S Sched x Jn := Restated.blockInLog_of_mem_bodies facts S Sched hv hJnmem
    have hkn : k ≤ n := Restated.tick_le_of_round_le facts S Sched x htk hntick hround
    have hstep : k + 1 ≤ n + 1 := Nat.succ_le_succ hkn
    have hqk : Restated.HonestThrough M Sched x (k + 1) v' := fun t ht =>
      hqhon t (le_trans ht (Restated.time_mono_int facts S Sched x (Nat.succ_le_succ (Nat.le_of_lt hkn'))))
    by_cases hW : (⟨v', NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n_W].sent
    · -- case: a vote sent by the switch round's tick step
      have hrDW : Restated.deadlineRoundW M S tGAT gap ≤ Restated.switchRound M S tE :=
        Restated.deadlineRoundW_le_switchRound facts S tGAT tE gap (Restated.runAll M S Sched x v 0) hgst hlen
      obtain ⟨T_D, hAD⟩ := Restated.exists_anchorAtRound facts S Sched x hsync hmono hphase hgst hcv hexec hmult
        hthird hcom hrec hlen htd le_rfl hrDW
      have hnWn : n_W ≤ n := Restated.tick_le_of_round_le facts S Sched x hnW hntick hr
      have hnn' : n + 1 ≤ n' := Restated.tick_succ_le_tick_succ_round facts S Sched x hntick hn'
      have hqW : Restated.HonestThrough M Sched x n_W v' := fun t ht =>
        hqhon t (le_trans ht (Restated.time_mono_int facts S Sched x (by omega)))
      have hvW : Restated.HonestThrough M Sched x n_W v := fun t ht =>
        hv t (le_trans ht (Restated.time_mono_int facts S Sched x hWn₁))
      have hlo : (M.derive_named S.E S.cfg T_D).h ≤ (x[n₁][v].st).st.core.h_j :=
        le_trans (hB T_D hAD n_W hnW v hvW) (Restated.h_j_mono_sts facts S Sched x v hWn₁)
      exact preceq_trans_Preceq
        (Restated.honestVotes_onAnchorChain_since_deadlineRound facts S Sched x hsync hmono hphase hgst hcv hexec
          hmult hthird hcom hrec hlen htd hprev hclear hAD hAW hnW v' n_W a _ Jn.root false
          (Nat.le_succ n_W) hqW hidx hW hpair hlo Jn hJnlog rfl)
        hTW
    · -- case: a vote first sent after the switch round's tick step
      have hh := hceil v' (k + 1) a _ Jn.root false hstep hqk hidx hsent hpair
      exact htgt v' (k + 1) a _ Jn.root false hstep hqk hidx hsent hW hpair hh Jn
        hJnlog rfl

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If round `r` is at or after the switch round, the invariant `hinv` holds at round `r` with tick
    step `n`, switch step `n_W` and anchor `T`, a switch-round anchor `T_W` is an ancestor of `T`,
    and step `n'` is the tick at `S.a (r + 1)`, then whatever a validator honest through its own
    read holds as its justified block, at any step from `n_W` up to `n' + 1`, is an ancestor of `T`. -/
theorem justified_preceq_anchor_after_switch (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hsync : Restated.SynchronyFromWake M S x)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE)
    (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    (hprev : ∀ r : Round, Restated.deadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
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
        (Restated.runAllPath M S Sched x v N) T)
    (hclear : ∀ r : Round, Restated.deadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
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
      Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T)
    (hB : Restated.BaseJustifiedHighAtSwitchRound M S Sched x tGAT tE gap)
    {T_W : NamedBlock V} (hAW : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.switchRound M S tE) T_W)
    {n_W : Nat} (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    {r : Round} {n n' : Nat} {T : NamedBlock V}
    (hr : Restated.switchRound M S tE ≤ r)
    (hinv : Restated.AfterPhaseInvariantOverActiveSetsSince M S Sched x r n n_W T)
    (hTW : Block.Preceq T_W.erase T.erase)
    (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1)))) :
    ∀ (v : V) (n₁ : Nat), n_W ≤ n₁ → n₁ ≤ n' + 1 → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J T.erase := by
  exact Restated.justified_preceq_anchor_after_switch_ofClauses facts S Sched x tE hexec hmono htd tGAT gap hgst hlen
    hsync hthird hphase hrsW hmult hcv hcom hrec hprev hclear hB hAW hnW hr hinv.tick
    hinv.heightCeiling hinv.targetsSince hTW hn'

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If the invariant holds at round `r`, at or after the switch round, with tick step `n`, switch
    step `n_W` and anchor `T`, and every honest justified block from `n_W` up to `n' + 1` is an
    ancestor of `T`, then `StepFinalizedCrossingUnderAnchor` holds: every block a validator honest
    through its own read has finalized up to step `n' + 1`, at the heights that fact covers, is an
    ancestor of `T`. -/
theorem stepFinalizedCrossingUnderAnchor_of_afterSwitch (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {tE : Int}
    {r : Round} {n n' n_W : Nat} {T : NamedBlock V}
    (hr : Restated.switchRound M S tE ≤ r) (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    (hinv : Restated.AfterPhaseInvariantOverActiveSetsSince M S Sched x r n n_W T)
    (hJ : ∀ (v : V) (n₁ : Nat), n_W ≤ n₁ → n₁ ≤ n' + 1 → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J T.erase) :
    Restated.StepFinalizedCrossingUnderAnchor M S Sched x r n' T := by
  intro v n₁ hn₁ hv _
  by_cases hsmall : n₁ ≤ n + 1
  · exact hinv.fin v n₁ hsmall hv
  · have hnWn : n_W ≤ n := Restated.tick_le_of_round_le facts S Sched x hnW hinv.tick hr
    exact preceq_trans_Preceq (Restated.finalized_preceq_justified_sts facts S Sched x n₁ v)
      (hJ v n₁ (by omega) hn₁ hv)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Given the hypotheses of `stepFinalizedCrossingUnderAnchor_of_afterSwitch`, whatever a validator
    honest through its own read holds as its justified block, at any step from `n + 1` up to `n'`,
    is an ancestor of `T` (`StepJustifiedRootUnderAnchor`). -/
theorem stepJustifiedRootUnderAnchor_of_afterSwitch (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {tE : Int}
    {r : Round} {n n' n_W : Nat} {T : NamedBlock V}
    (hr : Restated.switchRound M S tE ≤ r) (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    (hinv : Restated.AfterPhaseInvariantOverActiveSetsSince M S Sched x r n n_W T)
    (hJ : ∀ (v : V) (n₁ : Nat), n_W ≤ n₁ → n₁ ≤ n' + 1 → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J T.erase) :
    Restated.StepJustifiedRootUnderAnchor M S Sched x r n n' T := by
  intro v n₁ hbig hn₁ hv _ _
  have hnWn : n_W ≤ n := Restated.tick_le_of_round_le facts S Sched x hnW hinv.tick hr
  exact hJ v n₁ (by omega) (Nat.le_succ_of_le hn₁) hv

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- With `n_W` the switch round's tick step and `T_W` a switch-round anchor, from every round at or
    after the switch round whose anchor is `T_W` or a descendant of it, the after-phase invariant
    since the switch round carries to the next round, with the same switch step and an anchor that
    is the previous one or a descendant of it. -/
theorem afterPhaseStepOverActiveSetsSinceFrom_of_hypotheses (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (hf : ∀ (r : Round) (n n' : Nat) (T : NamedBlock V),
      Restated.AnchoredRoundOverActiveSets M S Sched x tE r n T → Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepFieldsAt M S Sched x tE r n n' T)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hsync : Restated.SynchronyFromWake M S x)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE)
    (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hcs : Restated.committeeSleepinessW M S Sched tE)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hw : Restated.WakesAtActionInstants M S Sched) (hs : Restated.SleepsAfterActionInstants M S Sched)
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    (hprev : ∀ r : Round, Restated.deadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
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
        (Restated.runAllPath M S Sched x v N) T)
    (hclear : ∀ r : Round, Restated.deadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
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
      Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T)
    (hB : Restated.BaseJustifiedHighAtSwitchRound M S Sched x tGAT tE gap)
    {n_W : Nat} (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    {T_W : NamedBlock V} (hAW : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.switchRound M S tE) T_W) :
    Restated.AfterPhaseStepOverActiveSetsSinceFrom M S Sched x tE n_W T_W := by
  intro r n T hr hTW hinvS
  obtain ⟨n', hn'⟩ := Restated.tick_field_at_succ facts S Sched x htd r
  have hctx : Restated.AnchoredRoundOverActiveSets M S Sched x tE r n T := ⟨hr, hinvS.toTop⟩
  have hne : ∀ q : V, ∃ a, a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S)
      (x[n'][q].st) q (r + 1) := fun q => by
    obtain ⟨na, hna⟩ := (p74% actionReadFrom_nonempty₇₄) facts (Setup.alwaysAwake S)
      (x[n'][q].st) (r + 1)
    obtain ⟨D, hD⟩ := facts.dt.attest_with_nonempty (M.gradeContract na.cache)
      (Setup.alwaysAwake S).E (Setup.alwaysAwake S).hc ((Setup.alwaysAwake S).node q) na.st na.record
    exact ⟨D.2.2, na, hna, D.1, D.2.1, hD⟩
  choose att hattq using hne
  have hatt : Restated.ActionAttestationsOf M S Sched x r n' att := fun q _ => hattq q
  have hJ : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      ∀ (v : V) (n₁ : Nat), n_W ≤ n₁ → n₁ ≤ n'' + 1 → Restated.HonestThrough M Sched x n₁ v →
        Block.Preceq (x[n₁][v].st).st.core.J T.erase :=
    fun n'' h => Restated.justified_preceq_anchor_after_switch facts S Sched x tE hexec hmono htd tGAT gap hgst
      hlen hsync hthird hphase hrsW hmult hcv hcom hrec hprev hclear hB hAW hnW hr hinvS hTW h
  have hcross : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepFinalizedCrossingUnderAnchor M S Sched x r n'' T :=
    fun n'' h => Restated.stepFinalizedCrossingUnderAnchor_of_afterSwitch facts S Sched x hr hnW hinvS (hJ n'' h)
  have hjust : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepJustifiedRootUnderAnchor M S Sched x r n n'' T :=
    fun n'' h => Restated.stepJustifiedRootUnderAnchor_of_afterSwitch facts S Sched x hr hnW hinvS (hJ n'' h)
  have hf := hf r n n' T hctx hn'
  refine ⟨n', Restated.newAnchor M S Sched x r n' att T,
    ⟨hn', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact Restated.inPlay_field_of_hypotheses_overActiveSets facts S Sched x tE hctx att hatt
  · exact Restated.anchorEntry_field_of_hypotheses_overActiveSets facts S Sched x tE hctx att hatt
  · exact Restated.band_field_of_hypotheses_overActiveSets facts S Sched x tE hexec hmono
      tGAT gap hgst hlen hthird hphase hrsW hctx hn' att hatt
  · exact Restated.sg_field_of_hypotheses_overActiveSets_ofFieldsAt facts (hcross := hcross) (hjust := hjust)
      S Sched x tE hexec hmono htd
      tGAT gap hgst hlen hsync hmult hcv hthird hphase hrsW hcs hcom hw hs hctx hn' hf att hatt
  · exact Restated.sgPairwise_field_of_hypotheses_overActiveSets_ofFieldsAt facts (hcross := hcross) (hjust := hjust)
      S Sched x tE hexec hmono htd
      tGAT gap hgst hlen hsync hmult hcv hthird hphase hrsW hcs hcom hw hs hctx hn' hf
  · exact Restated.heads_field_of_hypotheses_overActiveSets_ofFieldsAt facts S Sched x tE hf att hatt
  · exact Restated.fin_field_of_hypotheses_overActiveSets_ofFieldsAt facts (hcross := hcross) (hjust := hjust)
      S Sched x tE hexec hmono htd
      tGAT gap hgst hlen hsync hmult hcv hthird hphase hrsW hcs hcom hw hs hctx hn' hf att hatt
  · intro w hw' p hp m hm B b hb hbt
    exact Restated.grade1_field_of_hypotheses_overActiveSets_ofFieldsAt facts (hcross := hcross) (hjust := hjust)
      S Sched x tE hexec hmono htd
      tGAT gap hgst hlen hsync hmult hcv hthird hphase hrsW hcs hcom hw hctx hn' hf att hatt
      w hw' p hp m hm B (hbt ▸ hb)
  · exact Restated.heightCeiling_field_of_hypotheses_overActiveSets facts S Sched x tE hexec hw hs hctx hn'
      att hatt
  · exact Restated.targetsTop_field_of_hypotheses_overActiveSets_ofFieldsAt facts (hcross := hcross) (hjust := hjust)
      S Sched x tE hexec hmono htd
      tGAT gap hgst hlen hsync hmult hcv hthird hphase hrsW hcs hcom hw hs hctx hn' hf att hatt
  · exact Restated.targetsSince_field_of_hypotheses_overActiveSets_ofFieldsAt facts S Sched x tE hexec hmono htd
      tGAT gap hgst hlen hsync hmult hcv hthird hphase hrsW hcs hcom hw hs hr hinvS
      hcross hjust hn' hf att hatt
  · exact Restated.anchor_preceq_new_of_hypotheses_overActiveSets facts (hcross := hcross) (hjust := hjust)
      S Sched x tE hexec hmono htd
      tGAT gap hgst hlen hsync hmult hcv hthird hphase hrsW hcs hcom hw hctx hn' att hatt

end

end DecoupledConsensusModel.Sts.Restated
