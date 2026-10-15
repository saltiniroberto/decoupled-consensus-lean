import Proofs.Claims.Restated.Claim13bW_Ceiling
import Proofs.Claims.Restated.Claim13bW_ScheduleRule

/-!
# The height ceiling at the next round's anchor, under the awake-test rule

The lemma of `Claim13bW_Ceiling.lean` that carries the height ceiling of honest height votes to the
round-`(r + 1)` anchor, with the activity of a round-`(r + 1)` sender read off the attestation it
sent. Stated over a model `M : Record.Model V`, its facts `facts : Record.Facts M`, whose field `ndWake` holds the converse awake facts.
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

/-- If no non-empty height vote
    signed at a step up to the round-`r` tick's successor by a validator honest through that step
    names a height greater than the round-`r` anchor `T`'s chain-state height (`hceilR`), then no
    such vote signed up to the round-`(r + 1)` tick's successor names a height greater than the
    chain-state height of the round-`(r + 1)` anchor read along `att`. -/
theorem heightCeiling_field_at_succ_rule (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
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
        ⟨by
          have htime := (Restated.tickStepAt_time facts x htick).1
          have h := Restated.honRound_of_attestation_sent facts S Sched x htick
            (by rw [hreq]; exact Restated.early_g2_sub_delta_nonneg facts S (Nat.le_add_left 1 r))
            hawk (fun t ht => hvk t (by rw [htime]; exact ht)) hout hemit rfl
          rw [hreq] at h
          exact (Finset.mem_sdiff.1 h).1, hvn'⟩
    have hvote : (att v).height_pair = NamedHeightPair.vote h' entry tmo := by
      rw [← heq' (att v) (hatt v hfresh)]; exact hpair
    have hmemh : h' ∈ Restated.freshVoteHeights M S Sched x r n' att :=
      (Restated.mem_freshVoteHeights facts).mpr ⟨v, hfresh, entry, tmo, hvote⟩
    exact le_trans (Finset.le_sup (f := id) hmemh) (le_max_right _ _)

end

end DecoupledConsensusModel.Sts.Restated
