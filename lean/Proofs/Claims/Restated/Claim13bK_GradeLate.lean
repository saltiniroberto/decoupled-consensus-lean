import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bK_FreshAttestersW
import Proofs.Claims.Restated.Claim13bStepGrade
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bStepKitRecord
import Proofs.Claims.Restated.Claim13bStepKitTick
import Proofs.Claims.Restated.RunAll
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bK_FreshAttestersW
import Model.Conditions.Claim13bStepGrade
import Model.Conditions.Claim13bStepKitTick
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring
import Proofs.Claims.Restated.WakeWindow
import Proofs.Claims.Restated.Claim13bK_GradeLateRecv
import Proofs.Claims.Restated.Claim13bStepKitDeliveryRecv

/-!
# Grades read at the late cutoff

Theorems on the round-`r` attestations of the members of `freshAttestersW`: their tokens are in a
receiver's views at round `r + 1`, a member opposes a block that is an ancestor of none of its SG
blocks, and a block graded at least 1 at round `r + 1` is an ancestor of some member's round-`r` SG
block.
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

/-- From any node state `before`, validator `v`'s round-`r` action can compute some attestation. -/
private theorem actionAttestationFrom_nonemptyLate (facts : Record.Facts M) (S : Setup V)
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

/-- If `v`'s tick at round `r`'s action instant from `st` has an outcome and `st` passes the grade-2
    awake test of round `r`, any two attestations `v`'s round-`r` action can compute from `st` are
    equal. -/
private theorem actionAttestationFrom_uniqueLate (facts : Record.Facts M) (S : Setup V) (v : V)
    (st : M.N) (r : Round)
    (hne : ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) v st (Restated.Vocabulary.Execution.Setup.a M S r) ⇢ out)
    (hrun : M.awake_for_grade2 (Setup.alwaysAwake S) v st r)
    {a a' : NamedAttestation V}
    (ha : a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) st v r)
    (ha' : a' ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) st v r) (hn : M.reachedNode st := by trivial)
    (hv : M.runs_as st v := by trivial) : a = a' := by
  obtain ⟨out, hout⟩ := hne
  have h1 := Restated.namedTick_emits_only_attest facts S v st r hrun out hout a ha
  have h2 := Restated.namedTick_emits_only_attest facts S v st r hrun out hout a' ha'
  rw [h1] at h2
  simpa using h2

/-- The attestations `v`'s round-`r` action can compute from the wake stage at `t` of configuration
    `c` are those it can compute from `v`'s node state in `c`. -/
private theorem actionAttestationFrom_wakeStageLate (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (t : Int) (c : Config V (NamedObject V) M.N) (v : V) (r : Round) :
    Restated.actionAttestationFrom M S (Record.wakeStage M Sched t c v) v r =
      Restated.actionAttestationFrom M S (c[v].st) v r := by
  unfold Restated.actionAttestationFrom Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom
  rw [Record.wakeStage_st facts, Record.wakeStage_cache facts, Record.wakeStage_record facts]

/-- A member `v_1` of `freshAttestersW S Sched x r m` not held by the adversary up to round `r`'s
    action instant passes, at the tick step `n` at that instant, the grade-2 awake test of round
    `r`. -/
private theorem awake_for_grade2_of_mem_freshAttestersW_gl (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    {r : Round} {n m : Nat} {v_1 : V}
    (hn : Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S r)))
    (hq : v_1 ∈ Restated.freshAttestersW M S Sched x r m)
    (hhon : ∀ t' ≤ Restated.Vocabulary.Execution.Setup.a M S r, v_1 ∉ Sched.adv t') :
    M.awake_for_grade2 (Setup.alwaysAwake S) v_1
      (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S r) x[n] v_1) r := by
  obtain ⟨τ, hlbl, hτ⟩ := id hn
  have hwin : v_1 ∈ Sched.awakeThroughout (M.early S.E S.hc r .g2 - S.E.Δ) (M.a S.hc S.E.Δ r) :=
    ((Restated.mem_freshAttestersW facts).mp hq).1
  exact Restated.run_fact_g2 facts S Sched x n τ r v_1 hlbl hτ hwin (by rw [hτ]; exact hhon)

/-- If step `n` is the tick step at `S.a r` and `v_1`'s tick there has an outcome and passes the
    grade-2 awake test of round `r`, then every attestation `v_1`'s round-`r` action can compute at
    step `n` was sent honestly at step `n`. -/
private theorem fresh_attest_honestSendLate (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    {r : Round} {n : Nat}
    (hn : Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S r)))
    {m : Nat} {v_1 : V} (hq : v_1 ∈ Restated.freshAttesters M S Sched x r m)
    (hnm : (x[n].time : Int) ≤ (x[m].time : Int))
    (hqr : v_1 ∉ Sched.adv ((Restated.Vocabulary.Execution.Setup.a M S r)))
    (hne : ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) v_1 (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S r) x[n] v_1)
        (Restated.Vocabulary.Execution.Setup.a M S r) ⇢ out)
    (hrun : M.awake_for_grade2 (Setup.alwaysAwake S) v_1
      (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S r) x[n] v_1) r) :
    ∀ a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][v_1].st) v_1 r,
    Restated.HonestSendAt M S x n (⟨v_1, NamedObject.attest a⟩
      : SignedMsg V (NamedObject V)) := by
  intro a ha
  obtain ⟨t', hlbl, ht'⟩ := id hn
  have hsent1 : (⟨v_1, NamedObject.attest a⟩
      : SignedMsg V (NamedObject V)) ∈ x[n + 1].sent - x[n].sent := by
    refine Restated.mem_sent_diff_of_tick facts S Sched x hlbl
      (by rw [ht']; exact Finset.mem_sdiff.2 ⟨Restated.awake_of_mem_freshAttesters facts hq, hqr⟩)
      ?_ ?_
    · rw [ht']
      intro out hout
      have _hr_s1 := Record.reachedNode_wakeStage facts S Sched x (n) v_1 (Restated.Vocabulary.Execution.Setup.a M S r)
      have _hv_s2 := Record.runs_as_wakeStage facts S Sched x (n) v_1 (Restated.Vocabulary.Execution.Setup.a M S r)
      exact Restated.namedTick_emits_attest facts S v_1 _ r hrun out hout a
        (by rw [actionAttestationFrom_wakeStageLate facts]; exact ha)
    · rw [ht']
      exact hne
  have hqn : HonestThroughTime Sched (x[n].time : Int) v_1 := fun t ht =>
    Restated.honestThrough_of_mem_freshAttesters facts hq t (le_trans ht hnm)
  exact And.intro hsent1 (hqn (x[n].time : Int) (le_refl _))

/-- Whether or not `v_0` already held the sender's head when the attestation was delivered at step
    `k`, at step `m` the attestation's SG-vote projection is in the pool of its round of `v_0`'s
    grade view, with a stamp at or before `x[k].time`. -/
private theorem fresh_token_pooled_stampedLate (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    {k m : Nat} {v_0 : V}
    {a : NamedAttestation V} (hkm : k ≤ m) (hk1m : k + 1 ≤ m)
    (hcase : a.erase.confirmed ∈ M.round_votes (x[k][v_0].st).st.core a.erase ∨
      (a ∈ (x[k + 1][v_0].st).st.sg_rows a.round ∧
        (x[k + 1][v_0].st).st.core.timestamp_sg_vote (M.sgVote a.erase)
          = some (((x[k][v_0].st).st.core.t : Stamp)))) :
    M.sgVote a.erase ∈ (M.gradeView (M.toHealing (x[m][v_0].st).st.core)).sg_votes a.round ∧
      ∃ stamp : Int, stamp ≤ (x[k].time : Int) ∧
        (x[m][v_0].st).st.core.timestamp_sg_vote (M.sgVote a.erase)
          = some ((stamp : Stamp)) := by
  have ha_eround : a.erase.round = a.round := namedAttestation_erase_round a
  rcases hcase with hheld | ⟨h1, hstamp⟩
  · obtain ⟨c, hcpool, hcidx, hcconf⟩ :=
      (Restated.Vocabulary.Proofs.Optimistic.mem_round_votes facts).mp hheld
    have hpv := Restated.poolView_sts facts S Sched x k v_0 a.erase.round
    have hclist := (facts.sto.Sts_mem_sg_pool_iff _ _ c).mp hcpool
    rw [hpv] at hclist
    obtain ⟨B, hB, hBc⟩ := List.mem_map.mp hclist
    obtain ⟨hBround, stamp, hstampLe, hts⟩ :=
      (Restated.sgRowData_sts facts S Sched x k v_0).2 a.erase.round B hB
    have hBmem : B ∈ (x[k][v_0].st).st.sg_rows B.round := by rw [hBround]; exact hB
    have hsg : M.sgVote B.erase = M.sgVote a.erase := by
      rw [hBc]
      have hcround : c.round = a.erase.round := by
        rw [← hBc]; exact (namedAttestation_erase_round B).trans hBround
      exact facts.sto.sgVote_eq_of_fields hcidx hcround hcconf
    obtain ⟨hmem_m, hts_m⟩ := Restated.sgRow_stamp_mono_sts facts S Sched x v_0 hkm hBmem
    refine ⟨?_, stamp, hstampLe, ?_⟩
    · have hpool := Restated.sgRow_erase_mem_pool_sts facts S Sched x m v_0 B hmem_m
      rw [hBround, ha_eround] at hpool
      rw [← hsg, facts.gr.gradeView_sg_votes]
      exact Finset.mem_image_of_mem M.sgVote hpool
    · rw [← hsg, hts_m, hts]
  · obtain ⟨hmem_m, hts_m⟩ := Restated.sgRow_stamp_mono_sts facts S Sched x v_0 hk1m h1
    refine ⟨?_, (x[k][v_0].st).st.core.t, Restated.clock_le_time_sts facts S Sched x k v_0, ?_⟩
    · have hpool := Restated.sgRow_erase_mem_pool_sts facts S Sched x m v_0 a hmem_m
      rw [facts.gr.gradeView_sg_votes]
      exact Finset.mem_image_of_mem M.sgVote hpool
    · rw [hts_m, hstamp]

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If `B` is an ancestor of no body of `v_1` after step `n` that `a` names, and that body resolves
    in `v_0`'s tree, then no outcome of the test whether the head `a` names covers `B` in `v_0`'s
    grade view is `true`. -/
private theorem fresh_not_headCoversLate (facts : Record.Facts M) {S : Setup V}
    {Sched : Schedule V} (x : AtomicExec (Record.protocolOf M S) Sched) {n m : Nat} {v_0 v_1 : V}
    {a : NamedAttestation V}
    (hfind : ∀ C : NamedBlock V, C ∈ (x[n + 1][v_1].st).st.bodies →
      a.confirmed = some C.root →
      Block.find? (x[m][v_0].st).st.core.T C.root = some C.erase)
    (hhead_mem : ∀ root : BlockId, a.confirmed = some root →
      ∃ C : NamedBlock V, C ∈ (x[n + 1][v_1].st).st.bodies ∧ C.root = root)
    {B : Block V}
    (hnot : ∀ C : NamedBlock V, C ∈ (x[n + 1][v_1].st).st.bodies →
      a.confirmed = some C.root → ¬ Block.Preceq B C.erase) :
    ∀ b, M.head_covers (M.gradeView (M.toHealing (x[m][v_0].st).st.core)).T B a.confirmed ⇢ b →
      ¬ b = true := by
  intro b hb hcover
  obtain ⟨root, head, hkey, hfindh, -, hpreceq⟩ :=
    facts.gr.exists_head_of_head_covers b hb hcover
  obtain ⟨C, hCbody, hCroot⟩ := hhead_mem root hkey
  have hconfC : a.confirmed = some C.root := by rw [hkey, hCroot]
  have hfindC' : Block.find? (x[m][v_0].st).st.core.T root = some C.erase := by
    rw [← hCroot]; exact hfind C hCbody hconfC
  rw [facts.gr.Sts_gradeView_T] at hfindh
  have hhead : head = C.erase := Option.some.inj (hfindh.symm.trans hfindC')
  exact hnot C hCbody hconfC (by rw [← hhead]; exact preceq_eq_true_iff_Preceq.1 hpreceq)

end

end DecoupledConsensusModel.Sts.Restated
