import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bK_FreshAttestersW
import Proofs.Claims.Restated.Claim13bStepAnchor
import Proofs.Claims.Restated.Claim13bStepFin
import Proofs.Claims.Restated.Claim13bStepGrade
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bStepKitTick
import Proofs.Claims.Restated.Claim13bStepQuorum
import Proofs.Claims.Restated.Claim13bW_FrameAsleep
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActive
import Model.Conditions.Claim13bK_FreshAttestersW
import Model.Conditions.Claim13bStepAnchor
import Model.Conditions.Claim13bStepKitTick
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring

/-!
# The height ceiling at the next round

No honest height vote names a height greater than the anchor's chain-state height, carried from
round `r` to round `r + 1`, with the bounds this gives on the stores' maximum heights at the
round-`(r + 1)` tick. Stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Execution

/-- From any node state `before`, validator `v`'s round-`r` action read can compute some
    attestation. -/
private theorem actionAttestationFrom_nonempty_ceil (facts : Record.Facts M) (S : Setup V)
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

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Under `WakesAtActionInstants` and `SleepsAfterActionInstants`: if no non-empty height vote
    signed at a step up to the round-`r` tick's successor by a validator honest through that step
    names a height greater than the round-`r` anchor `T`'s chain-state height (`hceilR`), then no
    such vote signed up to the round-`(r + 1)` tick's successor names a height greater than the
    chain-state height of the round-`(r + 1)` anchor read along `att`. -/
theorem heightCeiling_field_at_succ_of_fresh (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hw : Restated.WakesAtActionInstants M S Sched) (hs : Restated.SleepsAfterActionInstants M S Sched)
    {r : Round} {n n' : Nat} (hn : Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S r)))
    (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    {att : V → NamedAttestation V} (hatt : Restated.ActionAttestationsOf M S Sched x r n' att)
    (T : NamedBlock V)
    (hceilR : ∀ (v : V) (n₂ : Nat) (b : NamedAttestation V) (h₂ : Height)
      (entry₂ : BlockId) (tmo₂ : Bool),
      n₂ ≤ n + 1 → Restated.HonestThrough M Sched x n₂ v → b.val_index = v →
      (⟨v, NamedObject.attest b⟩ : SignedMsg V (NamedObject V)) ∈ x[n₂].sent →
      b.height_pair = NamedHeightPair.vote h₂ entry₂ tmo₂ →
      h₂ ≤ (M.derive_named S.E S.cfg T).h) :
    ∀ (v : V) (n₁ : Nat) (a : NamedAttestation V) (h' : Height)
      (entry : BlockId) (tmo : Bool),
      n₁ ≤ n' + 1 → Restated.HonestThrough M Sched x n₁ v → a.val_index = v →
      (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n₁].sent →
      a.height_pair = NamedHeightPair.vote h' entry tmo →
      h' ≤ (M.derive_named S.E S.cfg (Restated.newAnchor M S Sched x r n' att T)).h := by
  classical
  intro v n₁ a h' entry tmo hn₁ hhon hidx hsent hpair
  rw [Restated.newAnchor_height facts S Sched x hn' hatt T]
  have hhonT : HonestThroughTime Sched ((x[n₁].time : Int)) v := fun t ht => hhon t ht
  obtain ⟨-, k, hkn₁, htick, hawk, out, hout, hemit⟩ :=
    Restated.attest_round_of_sent facts S Sched x (tB := (x[n₁].time : Int)) hhonT
      hexec.toUnforgeability hidx (le_refl _) hsent
  -- every attestation the action read can compute is the one the tick emitted
  have heq : ∀ a' ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[k][v].st) v a.round,
      a = a' := by
    have hA : Restated.actionAttestationFrom M (Setup.alwaysAwake S)
        (Record.wakeStage M Sched ((Restated.Vocabulary.Execution.Setup.a M S a.round)) x[k] v) v
          a.round =
        Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[k][v].st) v a.round := by
      simp only [Restated.actionAttestationFrom,
        Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom, Record.wakeStage_st facts,
        Record.wakeStage_record facts, Record.wakeStage_cache facts]
    rw [← hA]
    have _hr_s1 := Record.reachedNode_wakeStage facts S Sched x (k) v (Restated.Vocabulary.Execution.Setup.a M S a.round)
    have _hv_s2 := Record.runs_as_wakeStage facts S Sched x (k) v (Restated.Vocabulary.Execution.Setup.a M S a.round)
    exact Restated.attest_of_tick_eq facts S v _ a.round hout hemit
  obtain ⟨a₁, ha₁⟩ := actionAttestationFrom_nonempty_ceil facts (Setup.alwaysAwake S) (x[k][v].st) v
    a.round
  have hvk : Restated.HonestThrough M Sched x (k + 1) v := by
    intro t ht
    exact hhon t (le_trans ht (Restated.time_mono_int facts S Sched x (Nat.succ_le_of_lt hkn₁)))
  have hkn' : k ≤ n' := Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hkn₁ hn₁)
  have hround : a.round ≤ r + 1 := Restated.round_le_of_tick_le facts S Sched x htick hn' hkn'
  rcases Nat.lt_or_ge a.round (r + 1) with hlt | hge
  · -- a round at or before `r`: clause `J9` at round `r` answers
    have hkn : k ≤ n := Restated.tick_le_of_round_le facts S Sched x htick hn (Nat.le_of_lt_succ hlt)
    have hsentk : (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V))
        ∈ x[k + 1].sent := by
      rw [heq a₁ ha₁]
      -- the tick emitted `a`, so its node state passed the grade-2 awake test of `a`'s round
      exact Restated.attest_emitted_at_tick_from facts S Sched x htick hawk ⟨out, hout⟩
        (facts.nd.tick_attestation_fields (Setup.alwaysAwake S) v _ _ (Record.runs_as_wakeStage facts S Sched x _ _ _) out hout a hemit).2.1 a₁ ha₁
    exact le_trans
      (hceilR v (k + 1) a h' entry tmo (Nat.succ_le_succ hkn) hvk hidx hsentk hpair)
      (le_max_left _ _)
  · -- round `r + 1`: the sender is active, so its height is one of the anchor's heights
    have hreq : a.round = r + 1 := le_antisymm hround hge
    have htick' : Restated.tickStepAt M x k ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) := by rw [← hreq]; exact htick
    have hkeq : k = n' := Restated.tickStepAt_unique facts x htick' hn'
    have hawk' : v ∈ Sched.awake ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) := by
      rw [← hreq]; exact (Finset.mem_sdiff.1 hawk).1
    have hvn' : Restated.HonestThrough M Sched x (n' + 1) v := by rw [← hkeq]; exact hvk
    have heq' : ∀ a' ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n'][v].st) v
        (r + 1), a = a' := by
      rw [← hreq, ← hkeq]; exact heq
    have ha₁' : a₁ ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n'][v].st) v
        (r + 1) := by
      rw [← hreq, ← hkeq]; exact ha₁
    have hfresh : v ∈ Restated.freshAttestersW M S Sched x (r + 1) (n' + 1) :=
      (Restated.mem_freshAttestersW facts).mpr
        ⟨Restated.active_of_nonEmpty_heightVote facts S Sched x hw hs hawk' a₁ ha₁'
          (by rw [← heq a₁ ha₁]; exact hpair), hvn'⟩
    have hvote : (att v).height_pair = NamedHeightPair.vote h' entry tmo := by
      rw [← heq' (att v) (hatt v hfresh)]; exact hpair
    have hmemh : h' ∈ Restated.freshVoteHeights M S Sched x r n' att :=
      (Restated.mem_freshVoteHeights facts).mpr ⟨v, hfresh, entry, tmo, hvote⟩
    exact le_trans (Finset.le_sup (f := id) hmemh) (le_max_right _ _)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If no non-empty height vote signed at a step up to the round-`r` tick's successor by a validator
    honest through that step names a height greater than the round-`r` anchor `T`'s chain-state
    height (`hceilR`), then, under `roundSleepinessW`, at the round-`(r + 1)` tick step the maximum
    height any validator's store records is at most `T`'s chain-state height plus one. -/
theorem hMax_le_anchorHeight_succ_ofHeightCeiling (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {tE : Int}
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption)
    (hrsW : Restated.roundSleepinessW M S Sched tE)
    {r : Round} {n n' : Nat} (hn : Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S r)))
    (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    (htE : tE ≤ M.opening S.E S.hc r) {T : NamedBlock V}
    (hceilR : ∀ (v : V) (n₂ : Nat) (b : NamedAttestation V) (h₂ : Height)
      (entry₂ : BlockId) (tmo₂ : Bool),
      n₂ ≤ n + 1 → Restated.HonestThrough M Sched x n₂ v → b.val_index = v →
      (⟨v, NamedObject.attest b⟩ : SignedMsg V (NamedObject V)) ∈ x[n₂].sent →
      b.height_pair = NamedHeightPair.vote h₂ entry₂ tmo₂ →
      h₂ ≤ (M.derive_named S.E S.cfg T).h)
    (v : V) :
    (x[n'][v].st).st.core.h_max ≤ (M.derive_named S.E S.cfg T).h + 1 := by
  have _hr_0 : M.reachedNode (x[n'][v].st) := Record.reachedNode_sts facts S Sched x n' v
  have _hv_0 : M.runs_as (x[n'][v].st) v := Record.runs_as_sts facts S Sched x n' v
  classical
  by_cases hsmall : (x[n'][v].st).st.core.h_max ≤ 1
  · exact le_trans hsmall (Nat.succ_le_succ (Nat.zero_le _))
  · obtain ⟨B, hBmem, hBh⟩ := Restated.hMax_attained_sts facts S Sched x n' v
    have hpos : 2 ≤ (M.derive_named S.E S.cfg B).h := by
      rw [hBh]
      exact Nat.succ_le_of_lt (not_le.mp hsmall)
    have hone : 1 ≤ (M.derive_named S.E S.cfg B).h :=
      le_trans (by decide) hpos
    obtain ⟨Q, hQ, hsign⟩ := Restated.carried_vote_of_tree_block facts S Sched x hBmem hpos
    obtain ⟨signer, hsigner, hhon⟩ :=
      Restated.exists_honest_quorum_signer_ofRoundSleepinessW facts S Sched x hmono hrsW hn' htE hQ
    obtain ⟨carrier, a, entry, tmo, hcmem, hrow, hval, hpair⟩ := hsign signer hsigner
    have hhon' : Restated.HonestThrough M Sched x n' signer := by
      intro t ht
      exact hhon t (le_trans ht (Restated.time_mono_int facts S Sched x (Nat.le_succ n')))
    have hlog : (⟨signer, NamedObject.attest a⟩ : SignedMsg V (NamedObject V))
        ∈ x[n'].sent := by
      rw [← hval]
      exact Restated.carried_vote_in_log facts S Sched x hexec hcmem hrow
        (by rw [hval]; exact hhon')
    have hhonT : HonestThroughTime Sched ((x[n'].time : Int)) signer := fun t ht => hhon' t ht
    obtain ⟨-, k, hkn', htick, hawk, out, hout, hemit⟩ :=
      Restated.attest_round_of_sent facts S Sched x (tB := (x[n'].time : Int)) hhonT
        hexec.toUnforgeability hval (le_refl _) hlog
    have hround : a.round ≤ r + 1 := Restated.round_le_of_tick_le facts S Sched x htick hn' (Nat.le_of_lt hkn')
    have hle : a.round ≤ r := by
      rcases Nat.lt_or_ge a.round (r + 1) with hlt | hge
      · exact Nat.le_of_lt_succ hlt
      · exfalso
        have hreq : a.round = r + 1 := le_antisymm hround hge
        have htick' : Restated.tickStepAt M x k ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) := by rw [← hreq]; exact htick
        have hkeq : k = n' := Restated.tickStepAt_unique facts x htick' hn'
        omega
    have hkn : k ≤ n := Restated.tick_le_of_round_le facts S Sched x htick hn hle
    have heq : ∀ a' ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[k][signer].st)
        signer a.round, a = a' := by
      have hA : Restated.actionAttestationFrom M (Setup.alwaysAwake S)
          (Record.wakeStage M Sched ((Restated.Vocabulary.Execution.Setup.a M S a.round)) x[k]
            signer) signer a.round =
          Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[k][signer].st) signer
            a.round := by
        simp only [Restated.actionAttestationFrom,
          Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom, Record.wakeStage_st facts,
          Record.wakeStage_record facts, Record.wakeStage_cache facts]
      rw [← hA]
      have _hr_s3 := Record.reachedNode_wakeStage facts S Sched x (k) signer (Restated.Vocabulary.Execution.Setup.a M S a.round)
      have _hv_s4 := Record.runs_as_wakeStage facts S Sched x (k) signer (Restated.Vocabulary.Execution.Setup.a M S a.round)
      exact Restated.attest_of_tick_eq facts S signer _ a.round hout hemit
    obtain ⟨a₁, ha₁⟩ := actionAttestationFrom_nonempty_ceil facts (Setup.alwaysAwake S)
      (x[k][signer].st) signer a.round
    have hsentk : (⟨signer, NamedObject.attest a⟩ : SignedMsg V (NamedObject V))
        ∈ x[k + 1].sent := by
      rw [heq a₁ ha₁]
      -- the tick emitted `a`, so its node state passed the grade-2 awake test of `a`'s round
      exact Restated.attest_emitted_at_tick_from facts S Sched x htick hawk ⟨out, hout⟩
        (facts.nd.tick_attestation_fields (Setup.alwaysAwake S) signer _ _ (Record.runs_as_wakeStage facts S Sched x _ _ _) out hout a hemit).2.1
        a₁ ha₁
    have hvk : Restated.HonestThrough M Sched x (k + 1) signer := by
      intro t ht
      exact hhon' t (le_trans ht (Restated.time_mono_int facts S Sched x (Nat.succ_le_of_lt hkn')))
    have hbound := hceilR signer (k + 1) a ((M.derive_named S.E S.cfg B).h - 1) entry tmo
      (Nat.succ_le_succ hkn) hvk hval hsentk hpair
    calc (x[n'][v].st).st.core.h_max
        = (M.derive_named S.E S.cfg B).h := hBh.symm
      _ = ((M.derive_named S.E S.cfg B).h - 1) + 1 := (Nat.sub_add_cancel hone).symm
      _ ≤ (M.derive_named S.E S.cfg T).h + 1 := Nat.succ_le_succ hbound

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If no non-empty height vote signed at a step up to the round-`r` tick's successor by a validator
    honest through that step names a height greater than the round-`r` anchor `T`'s chain-state
    height (`hceilR`), then, under `roundSleepinessW`, the largest `Σ.h_max` any honest active
    attester of round `r + 1` holds at step `n'`, less one, is at most the chain-state height of the
    round-`(r + 1)` anchor read along `att`. -/
theorem band_field_at_succ_overActiveSets_ofHeightCeiling (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {tE : Int}
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption)
    (hrsW : Restated.roundSleepinessW M S Sched tE)
    {r : Round} {n n' : Nat} (hn : Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S r)))
    (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    {att : V → NamedAttestation V} (hatt : Restated.ActionAttestationsOf M S Sched x r n' att)
    (htE : tE ≤ M.opening S.E S.hc r) (T : NamedBlock V)
    (hceilR : ∀ (v : V) (n₂ : Nat) (b : NamedAttestation V) (h₂ : Height)
      (entry₂ : BlockId) (tmo₂ : Bool),
      n₂ ≤ n + 1 → Restated.HonestThrough M Sched x n₂ v → b.val_index = v →
      (⟨v, NamedObject.attest b⟩ : SignedMsg V (NamedObject V)) ∈ x[n₂].sent →
      b.height_pair = NamedHeightPair.vote h₂ entry₂ tmo₂ →
      h₂ ≤ (M.derive_named S.E S.cfg T).h) :
    Restated.hmaxRoundAt M S Sched x (r + 1) n' - 1
      ≤ (M.derive_named S.E S.cfg (Restated.newAnchor M S Sched x r n' att T)).h := by
  classical
  have hsup : Restated.hmaxRoundAt M S Sched x (r + 1) n' ≤ (M.derive_named S.E S.cfg T).h + 1 := by
    simp only [Restated.hmaxRoundAt]
    refine Finset.sup_le ?_
    intro u _
    exact Restated.hMax_le_anchorHeight_succ_ofHeightCeiling facts S Sched x hexec hmono hrsW hn
      hn' htE hceilR u
  have hold : (M.derive_named S.E S.cfg T).h
      ≤ Restated.newAnchorHeight M S Sched x r n' att (M.derive_named S.E S.cfg T).h :=
    le_max_left _ _
  rw [Restated.newAnchor_height facts S Sched x hn' hatt T]
  exact Nat.sub_le_iff_le_add.mpr (le_trans hsup (Nat.succ_le_succ hold))

end

end DecoupledConsensusModel.Sts.Restated
