import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bK_FgJustified
import Proofs.Claims.Restated.Claim13bK_FinBeforeTick
import Proofs.Claims.Restated.Claim13bK_Frame
import Proofs.Claims.Restated.Claim13bK_FreshAttestersW
import Proofs.Claims.Restated.Claim13bK_GradeLate
import Proofs.Claims.Restated.Claim13bK_GradeOld
import Proofs.Claims.Restated.Claim13bK_GradeOldHeads
import Proofs.Claims.Restated.Claim13bPhaseSleepiness
import Proofs.Claims.Restated.Claim13bStepAssembly
import Proofs.Claims.Restated.Claim13bStepCone
import Proofs.Claims.Restated.Claim13bStepConeIter
import Proofs.Claims.Restated.Claim13bStepGrade
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bW_Schedule
import Proofs.Claims.Restated.Claim13beRoute3_3
import Proofs.Claims.Restated.CommonViewOfFinalizedDescendantsFacts
import Proofs.Claims.Restated.Projection
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActive
import Model.Conditions.Claim13bInvariantActiveTop
import Model.Conditions.Claim13bK_ConeAnchor
import Model.Conditions.Claim13bK_ConeSlots
import Model.Conditions.Claim13bK_FgJustified
import Model.Conditions.Claim13bK_FinBeforeTick
import Model.Conditions.Claim13bK_Frame
import Model.Conditions.Claim13bK_FreshAttestersW
import Model.Conditions.Claim13bK_GradeOldHeads
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13bStepAssembly
import Model.Conditions.Claim13bStepCone
import Model.Conditions.Claim13bStepKitTick
import Model.Conditions.CommonViewOfFinalizedDescendantsFacts
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bK_ConeAnchor
import Proofs.Claims.Restated.WakeWindow

/-!
# The SG root of a vote walk lies on one chain with the anchor

Over a model `M : Record.Model V`: `ConeAnchorCompatible` from the parts of the vote read (the
grade-1 roots of its frame, and the finalized and justified blocks), and at the round-`r` anchor for
the honest active committee members of round `r`'s later slots and of round `r + 1`'s opening slot
and the slot after it.
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

/-- For an outcome `n` of `before`'s slot-`s'` vote read, every SG root the vote duty can start from
    under `n`'s grade contract lies on one chain with `B` whenever every grade-1 root `n`'s frame
    holds for the round of `s'` does, and so do `before`'s finalized block and justified block. -/
theorem voteAnchor_compatible_of_parts (facts : Record.Facts M) (S : Setup V) (before : M.N) (s' : Slot)
    {B : Block V} {n : M.N} (hn : Restated.voteReadOf M S before s' ⇢ n)
    (hg1 : ∀ root : Block V,
      (M.readFrame n.cache
        (M.toHealing (Restated.voteStoreAt M S before s')) (M.round_of S.hc s')).g1 = some (some root) →
      Block.compatible root B = true)
    (hF : Block.compatible before.st.core.F B = true)
    (hJ : before.st.core.h_max = before.st.core.h_j + 1 →
      Block.compatible before.st.core.J B = true) :
    ∀ A, Restated.voteAnchorOf M (M.gradeContract n.cache) S.E S.hc
        (Restated.voteStoreAt M S before s') ⇢ A → Block.compatible A B = true := by
  intro A hA
  have hst : Restated.voteStoreAt M S before s' = (M.ns_setClock S.E
      before.st (M.vote_time S.E s')).core := rfl
  have hfg : Block.compatible
      (M.get_fg_root (M.toHealing (Restated.voteStoreAt M S before s')).toFG) B = true :=
    facts.fc.fgRoot_compatible_of_compatible (stH := (M.toHealing (Restated.voteStoreAt M S before s')))
      (by rw [hst, facts.hd.setClock_toHealing_F]; exact hF)
      (by rw [hst, facts.hd.setClock_toHealing_h_max, facts.hd.setClock_toHealing_h_j, facts.hd.setClock_toHealing_J]
          exact hJ)
  have hslot : (M.round_of S.hc (Restated.voteStoreAt M S before s').s) = (M.round_of S.hc s') := by
    rw [Restated.voteStoreAt_slot facts]
  have key : M.anchor S.E S.hc (M.toHealing (Restated.voteStoreAt M S before s'))
          ((M.round_of S.hc (Restated.voteStoreAt M S before s').s))
          (M.readFrame n.cache (M.toHealing (Restated.voteStoreAt M S before s'))
            ((M.round_of S.hc (Restated.voteStoreAt M S before s').s))).g1 ⇢ A :=
    (facts.nd.gradeContract_sgRoot_eq_frameAnchor _ _ _ _ _ _).1 hA
  rw [hslot] at key
  exact facts.gr.anchor_compatible S hg1 hfg A key

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- `ConeAnchorCompatible S x B s` from its two halves: if at slot `s + 1` every honest active
    member's vote-read grade-1 roots, and its finalized and justified blocks, lie on one chain with
    `B`, then so does the SG root its vote duty starts from. -/
theorem coneAnchorCompatible_of_voteReads (facts : Record.Facts M) (S : Setup V) {Sched : Schedule V} (x : AtomicExec (Record.protocolOf M S) Sched) {B : Block V} {s : Slot}
    (hg1 : Restated.VoteGradeOneCompatible M S x B s) (hFJ : Restated.VoteFinJustCompatible M S x B s) :
    Restated.ConeAnchorCompatible M S x B s := by
  intro v mr hv hmr n hn A hA
  exact Restated.voteAnchor_compatible_of_parts facts S (x[mr][v].st) (s + 1) hn (hg1 v mr hv hmr n hn)
    (hFJ v mr hv hmr).1 (hFJ v mr hv hmr).2 A hA

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If round `r` is at or after the switch round, the invariant holds at round `r` with tick step
    `n` and anchor `T`, and slot `s + 1`'s vote instant is strictly between `S.a r` and
    `S.a (r + 1)`, then every honest active member of slot `(s + 1)`'s committee holds, before its
    vote tick, a finalized block and a justified block that lie on one chain with `T`. -/
theorem voteFinJustCompatible_of_before_succ_tick (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE)
    {r : Round} {n : Nat} {T : NamedBlock V}
    (hr : Restated.switchRound M S tE ≤ r) (hinv : Restated.AfterPhaseInvariantOverActiveSetsTop M S Sched x r n T)
    (hcross : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepFinalizedCrossingUnderAnchor M S Sched x r n'' T)
    (hjust : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepJustifiedRootUnderAnchor M S Sched x r n n'' T)
    {s : Slot} (hlo : (Restated.Vocabulary.Execution.Setup.a M S r) < M.vote_time S.E (s + 1))
    (hhi : M.vote_time S.E (s + 1) < (Restated.Vocabulary.Execution.Setup.a M S (r + 1))) :
    Restated.VoteFinJustCompatible M S x T.erase s := by
  intro v mr hv hmr
  obtain ⟨n', hn'⟩ := Restated.tick_field_at_succ facts S Sched x htd r
  have hn := hinv.tick
  obtain ⟨hn1, hn0⟩ := Restated.tickStepAt_time facts x hn
  obtain ⟨hn'1, -⟩ := Restated.tickStepAt_time facts x hn'
  obtain ⟨-, hmr0⟩ := Restated.tickStepAt_time facts x hmr
  have hlow : n + 1 ≤ mr := by
    by_contra hcon
    have hle : mr ≤ n := by omega
    have h1 := Restated.time_mono_int facts S Sched x hle
    linarith
  have hhigh : mr ≤ n' := by
    by_contra hcon
    have hle : n' + 1 ≤ mr := by omega
    have h1 := Restated.time_mono_int facts S Sched x hle
    linarith
  have hct : (x[mr].time : Int) ≤ M.confirmation_time S.E (s + 1) := by
    have e : M.confirmation_time S.E (s + 1) = M.vote_time S.E (s + 1) + 5 * S.E.Δ := by
      have e1 := facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E (s + 1)
      have e2 := facts.sch.slotStart_add_delta_eq_vote_time S.E (s + 1)
      linarith
    have hd := S.E.Δ_pos
    linarith
  have hvh : Restated.HonestThrough M Sched x mr v := Restated.honestThrough_of_mem_HonSlot facts S Sched x hmono hv hct
  have hF := Restated.fin_old_anchor_before_succ_tick_of_hypotheses facts (hcross := hcross) S Sched x tE hexec hmono tGAT gap
    hgst hlen hthird hphase hrsW hr hinv hn' v mr hhigh hvh
  have hJ := Restated.justified_old_anchor_before_succ_tick_of_hypotheses facts (hjust := hjust) S Sched x tE hexec hmono tGAT gap
    hgst hlen hthird hphase hrsW hr hinv hn' v mr hlow hhigh hvh
  exact ⟨compatible_of_preceq_common_Preceq hF (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _)),
    fun hroot => compatible_of_preceq_common_Preceq (hJ hroot)
      (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _))⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

open scoped DC in
/-- If `f <$> m` can return `b`, then `m` can return some `a` with `f a = b`. -/
private theorem returns_map_elim_ca {α β : Type} (f : α → β) (m : DC.NDRE α) (b : β)
    (h : (f <$> m) ⇢ b) : ∃ a, m ⇢ a ∧ f a = b := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image] at h
  obtain ⟨e, he, hb⟩ := h
  cases e with
  | ok a => exact ⟨a, he, by simpa [Except.map] using hb⟩
  | error err => simp [Except.map] at hb

/-- Every outcome `n` of the vote read of `before` at slot `s` is made of `before`'s store with its
    clock set to slot `s`'s vote instant, `before`'s signing record, and an outcome `c` of the phase
    tick at that instant on `before`'s cache. -/
private theorem voteReadOf_cases_ca (S : Setup V) (before : M.N) (s : Slot) {n : M.N}
    (hn : Restated.voteReadOf M S before s ⇢ n) :
    ∃ c : M.Cache, M.onPhaseTick S.E S.hc before.st.core.toHealing (M.vote_time S.E s)
        before.cache ⇢ c ∧
      n = M.mkNode (M.ns_setClock S.E before.st (M.vote_time S.E s)) before.record c := by
  obtain ⟨c, hc, hcn⟩ := returns_map_elim_ca _ _ _ hn
  exact ⟨c, hc, hcn.symm⟩

/-- If `mr` is the sts tick step at slot `s'`'s vote instant, `n` is an outcome of `v`'s slot-`s'`
    vote read and `n`'s frame offers `root` as its grade-1 result for the round `ρ` of `s'`, then
    there are a step `m` before `ρ`'s grade-1 domain instant and a block `B` such that every outcome
    of the grade test of `B` on `v`'s store after `m` steps with the grade-1 cutoffs is `true`, and
    `root ⪯ B`. -/
theorem voteFrame_g1_provenance (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {s' : Slot} {mr : Nat}
    (hmr : Restated.tickStepAt M x mr (M.vote_time S.E s')) (v : V) (root : Block V)
    {n : M.N} (hn : Restated.voteReadOf M S (x[mr][v].st) s' ⇢ n)
    (h : (M.readFrame n.cache
        (M.toHealing (Restated.voteStoreAt M S (x[mr][v].st) s')) (M.round_of S.hc s')).g1 = some (some root)) :
    ∃ (m : Nat) (B : Block V),
      Restated.stepBeforeInstant M x m (M.domain S.E S.hc ((M.round_of S.hc s')) .g1) ∧
      (∀ b : Bool, M.gradeBool S.E (M.gradeView (M.toHealing (x[m][v].st).st.core))
        (x[m][v].st).st.core.F S.hc.η_SG ((M.round_of S.hc s'))
        (M.early S.E S.hc ((M.round_of S.hc s')) .g1)
        (M.late S.E S.hc ((M.round_of S.hc s')) .g1) B ⇢ b → b = true) ∧
      Block.Preceq root B := by
  obtain ⟨c, hc, rfl⟩ := voteReadOf_cases_ca S _ s' hn
  have hprep := Restated.framePhaseProvenance_onPhaseTick facts S hmr
    (Restated.framePhaseProvenance_sts facts S Sched x v mr) c hc
  obtain ⟨root₀, h₀, hpre⟩ := facts.gr.readFrame_g1_provenance _ _ _ h
  rw [facts.nd.mkNode_cache] at h₀
  obtain ⟨m, B, hm, hB, hpre'⟩ := hprep ((M.round_of S.hc s')) .g1 root₀ h₀
  exact ⟨m, B, hm, hB, preceq_trans_Preceq hpre hpre'⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For a validator `v` awake throughout `[S.a r, domain (r + 1) p]` and not held by the adversary
    at `domain (r + 1) p`, where `p` is a phase of round `r + 1` whose domain instant is at or
    before `S.a (r + 1)` and `m` is the last step before that instant, and for every member `v_1` of
    `freshAttestersW S Sched x r m`: the block every attestation of `v_1`'s round-`r` action names
    is in `v`'s tree at `m` under its root, stamped before the phase's late cutoff, and compatible
    with `v`'s finalized block at `m`. The hypotheses `hneTick` and `hneAtt` ask that `v`'s tick
    have an outcome at every whole multiple of `Δ` up to `S.a (r + 1)` at which `v` is awake and not
    held, and that `M.tick` on every honest active attester of round `r` at `S.a r` have an outcome. -/
theorem freshSGHeads_at_awakeReader (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (hsync : Restated.SynchronyFromWake M S x) (hmult : AwakeAtMultiples S Sched)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE) (hcs : Restated.committeeSleepinessW M S Sched tE)
    {r : Round} {n : Nat} {T : NamedBlock V}
    (hr : Restated.switchRound M S tE ≤ r) (hinv : Restated.AfterPhaseInvariantOverActiveSetsTop M S Sched x r n T)
    (hcross : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepFinalizedCrossingUnderAnchor M S Sched x r n'' T)
    {v : V} {p : Protocol.Phase}
    (hdom : M.domain S.E S.hc (r + 1) p ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)))
    (hawT : v ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S r)) (M.domain S.E S.hc (r + 1) p))
    (hvS : v ∉ Sched.adv (M.domain S.E S.hc (r + 1) p))
    {m : Nat} (hm : Restated.stepBeforeInstant M x m (M.domain S.E S.hc (r + 1) p))
    (hneTick : ∀ (n' : Nat) (t' : Int),
      Restated.tickStepAt M x n' t' → t' % S.E.Δ = 0 → v ∈ Sched.awake t' \ Sched.adv t' → t' ≤ Restated.Vocabulary.Execution.Setup.a M S (r + 1) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched t' x[n'] v) t' ⇢ out)
    (hneAtt : ∀ v_1 ∈ Restated.HonRound M S Sched r, ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) v_1 (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S r) x[n] v_1) (Restated.Vocabulary.Execution.Setup.a M S r) ⇢ out) :
    ∀ v_1 ∈ Restated.freshAttestersW M S Sched x r m, ∀ C : NamedBlock V,
      C ∈ (x[n + 1][v_1].st).st.bodies →
      ∀ a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][v_1].st) v_1 r,
      a.confirmed = some C.root →
      Block.find? (x[m][v].st).st.core.T C.root = some C.erase ∧
      stampedBefore (x[m][v].st).st.core.timestamp_block
        (M.late S.E S.hc (r + 1) p) C.erase = true ∧
      Block.compatible C.erase (x[m][v].st).st.core.F = true := by
  classical
  intro v_1 hv_1 C hCbody a ha hconf
  have hd := S.E.Δ_pos
  have hd1 : (1 : Int) ≤ S.E.Δ := hd
  obtain ⟨n', hn'⟩ := Restated.tick_field_at_succ facts S Sched x htd r
  have hfin := Restated.fin_old_anchor_before_succ_tick_of_hypotheses facts (hcross := hcross) S Sched x tE hexec hmono tGAT gap
    hgst hlen hthird hphase hrsW hr hinv hn'
  have hn := hinv.tick
  -- instants
  have hn1 : (x[n + 1].time : Int) = (Restated.Vocabulary.Execution.Setup.a M S r) := (Restated.tickStepAt_time facts x hn).1
  have hn'1 : (x[n' + 1].time : Int) = (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) := (Restated.tickStepAt_time facts x hn').1
  have ham : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[m].time : Int) := Restated.action_le_time_of_stepBefore facts S Sched x htd hm
  have htmd : (x[m].time : Int) ≤ M.domain S.E S.hc (r + 1) p :=
    le_of_lt (Restated.time_lt_domain_of_stepBefore facts S Sched x htd hm)
  have hlate := facts.gr.action_add_three_delta_le_late_succ S r p
  have hld := facts.gr.late_le_domain S (r + 1) p
  have hdm := Restated.domain_sub_one_le_time_of_stepBefore facts S Sched x htd hm
  -- a round opens at the proposal instant of its opening slot, which is at or before that slot's
  -- confirmation instant, the action instant
  have hopen : M.opening S.E S.hc r ≤ Restated.Vocabulary.Execution.Setup.a M S r := by
    show _ ≤ M.a S.hc S.E.Δ r
    rw [facts.gr.opening_eq_proposal_time, facts.sch.a_eq_confirmation_time]
    exact facts.sch.proposal_time_le_confirmation_time _ _
  have htGAT : tGAT ≤ (Restated.Vocabulary.Execution.Setup.a M S r) :=
    le_trans (Restated.tGAT_le_switchOpening facts S tGAT tE gap hgst hlen)
      (le_trans (Restated.switchOpening_le_opening facts S hr) hopen)
  -- honesty
  have hvm : Restated.HonestThrough M Sched x m v := fun t ht hin =>
    hvS (hmono t _ (le_trans ht htmd) hin)
  have hv1m : Restated.HonestThrough M Sched x m v_1 := Restated.honestThrough_of_mem_freshAttestersW facts hv_1
  have hv1n : Restated.HonestThrough M Sched x (n + 1) v_1 := fun t ht =>
    hv1m t (le_trans ht (by rw [hn1]; exact ham))
  -- `C` is compatible with the anchor
  have hqr : v_1 ∉ Sched.adv ((Restated.Vocabulary.Execution.Setup.a M S r)) := hv1m _ ham
  have hsent := Restated.fresh_attests facts S Sched x hn
    (Restated.freshAttestersW_subset_freshAttesters facts S Sched x r m hv_1) hqr
    (hneAtt v_1 (Restated.hfreshH_of_stepBefore facts S Sched x htd hm hv_1))
    -- the grade-2 awake test of `v_1`'s tick at step `n`: `v_1` is awake through `wAttest S ≥ 12Δ`
    -- before `S.a r`, which covers round `r`'s grade-2 window from one delay before its early
    -- cutoff `S.a r − 11Δ`, so `run_fact_g2` gives it
    (by
      have hw := ((Restated.mem_freshAttestersW facts).mp hv_1).1
      obtain ⟨τ, hlbl, hτ⟩ := id hn
      refine Restated.run_fact_g2 facts S Sched x n τ r v_1 hlbl hτ ?_ (by
        -- `v_1` is not held by the adversary at any instant up to `S.a r` (`hv1m`, `ham`)
        rw [hτ]
        exact fun t ht => hv1m t (le_trans ht ham))
      have h12 := twelve_delta_le_wAttest S
      have hΔ := S.E.Δ_pos
      simp only [Restated.activeRoundW, Schedule.awakeThroughout, Finset.mem_inf,
        Finset.mem_Icc] at hw ⊢
      rw [facts.gr.early_g2_eq S r]
      intro t ht
      exact hw t ⟨by linarith [ht.1], ht.2⟩) a ha
  have hCT : Block.compatible C.erase T.erase = true :=
    hinv.sg v_1 (Restated.hfreshH_of_stepBefore facts S Sched x htd hm hv_1) a
      (Restated.actionAttestationFrom_round facts (Setup.alwaysAwake S) _ v_1 r a ha)
      (Restated.actionAttestationFrom_val_index facts (Setup.alwaysAwake S) _ v_1 r a ha) hsent C
      hCbody hconf
  -- every honest finalized block up to `n'` is on one chain with `C`
  have hFC : ∀ (w : V) (d : Nat), d ≤ n' → Restated.HonestThrough M Sched x d w →
      Block.compatible (x[d][w].st).st.core.F C.erase = true := fun w d hd' hw =>
    Protocol.compatible_of_preceq_of_compatible (hfin w d hd' hw) (Protocol.compatible_comm hCT)
  have hmn' : m ≤ n' := Restated.stepBefore_le_tick facts x hm hn' (le_trans hdom le_rfl)
  have hlog : Restated.blockInLog M S Sched x C := Restated.blockInLog_of_mem_bodies facts S Sched hv1n hCbody
  -- the reader admits `C` at every delivery before `S.a (r + 1)`
  have hadm : Restated.ReaderAdmitsInPhase M S Sched x tGAT ((Restated.Vocabulary.Execution.Setup.a M S (r + 1)) - 1) v C := by
    intro d v_0 _ hvd _ hhi
    have hdn : d ≤ n' := by
      by_contra hcon
      have hle : n' + 1 ≤ d := by omega
      have h1 := Restated.time_mono_int facts S Sched x hle
      rw [hn'1] at h1
      linarith
    have hc := hFC v d hdn hvd
    rcases compatible_cases hc with hFCd | hCFd
    · exact Or.inl (preceq_eq_true_iff_Preceq.mpr hFCd)
    · exact Or.inr (Restated.mem_bodies_of_preceq_finalized facts S Sched x hexec hvd hlog hCFd)
  have hadmS : Restated.ReaderAdmitsAtStepsInPhase M S Sched x tGAT ((Restated.Vocabulary.Execution.Setup.a M S (r + 1)) - 1) v C := by
    intro d hvd _ hhi
    have hdn : d ≤ n' := by
      by_contra hcon
      have hle : n' + 1 ≤ d := by omega
      have h1 := Restated.time_mono_int facts S Sched x hle
      rw [hn'1] at h1
      linarith
    have hc := hFC v d hdn hvd
    rcases compatible_cases hc with hFCd | hCFd
    · exact Or.inl (preceq_eq_true_iff_Preceq.mpr hFCd)
    · exact Or.inr (Restated.mem_bodies_of_preceq_finalized facts S Sched x hexec hvd hlog hCFd)
  have hwaw : v ∈ Sched.awakeThroughout
      (M.late S.E S.hc (r + 1) p - 1 - 2 * S.E.Δ) (M.late S.E S.hc (r + 1) p - 1) :=
    awakeThroughout_mono Sched hawT (by linarith) (by linarith)
  obtain ⟨hmemT, σ, hσ, hσlt⟩ :=
    Restated.block_in_tree_of_holder_afterPhase_ofAdmits facts S Sched x hexec hsync hmult htd hmono hgst hcv
      hphase hthird hcs (Restated.delta_le_of_healingLengthη facts S hlen) hadm hadmS hCbody hv1n
      (by rw [hn1]; exact htGAT) (by rw [hn1]; linarith) (by linarith) (by linarith)
      (fun hin => hvS (hmono _ _ htmd hin)) hwaw
      (fun n'' t' h1 hΔ hq _ h3 => hneTick n'' t' h1 hΔ hq (le_trans h3 (le_trans htmd hdom)))
  refine ⟨?_, ?_, ?_⟩
  · rw [← Proofs.NamedWire.erase_root]
    exact Restated.find_of_mem_tree_honest facts S Sched x hexec hvm hmemT
  · exact stampedBefore_of_lt hσ (lt_of_lt_of_le hσlt (WithBot.coe_le_coe.mpr (by linarith)))
  · exact Protocol.compatible_comm (hFC v m hmn' hvm)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For a validator `v` awake at every instant from `S.a r` to the domain instant of a
    round-`(r + 1)` phase at or before `S.a (r + 1)`, and not held by the adversary at that instant:
    every block `v` grades at least 1 for round `r + 1` at the last step before that instant, with
    that phase's cutoffs, lies on one chain with the round-`r` anchor `T`. The hypotheses `hneTick`
    and `hneAtt` are those of `freshSGHeads_at_awakeReader`. -/
theorem grade1_compatible_at_awakeReader (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (hsync : Restated.SynchronyFromWake M S x) (hmult : AwakeAtMultiples S Sched)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE) (hcs : Restated.committeeSleepinessW M S Sched tE)
    {r : Round} {n : Nat} {T : NamedBlock V}
    (hr : Restated.switchRound M S tE ≤ r) (hinv : Restated.AfterPhaseInvariantOverActiveSetsTop M S Sched x r n T)
    (hcross : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepFinalizedCrossingUnderAnchor M S Sched x r n'' T)
    {v : V} {p : Protocol.Phase}
    (hdom : M.domain S.E S.hc (r + 1) p ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)))
    (hawT : v ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S r)) (M.domain S.E S.hc (r + 1) p))
    (hvS : v ∉ Sched.adv (M.domain S.E S.hc (r + 1) p))
    {m : Nat} (hm : Restated.stepBeforeInstant M x m (M.domain S.E S.hc (r + 1) p))
    (B : Block V)
    (hgrade : M.gradeBool S.E (M.gradeView (M.toHealing (x[m][v].st).st.core))
      (x[m][v].st).st.core.F S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) p)
      (M.late S.E S.hc (r + 1) p) B ⇢ true)
    (hneTick : ∀ (n' : Nat) (t' : Int),
      Restated.tickStepAt M x n' t' → t' % S.E.Δ = 0 → v ∈ Sched.awake t' \ Sched.adv t' → t' ≤ Restated.Vocabulary.Execution.Setup.a M S (r + 1) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched t' x[n'] v) t' ⇢ out)
    (hneAtt : ∀ v_1 ∈ Restated.HonRound M S Sched r, ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) v_1 (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S r) x[n] v_1) (Restated.Vocabulary.Execution.Setup.a M S r) ⇢ out) :
    Block.compatible B T.erase = true := by
  have hn := hinv.tick
  -- a round opens at the proposal instant of its opening slot, which is at or before that slot's
  -- confirmation instant, the action instant
  have hopen : M.opening S.E S.hc r ≤ Restated.Vocabulary.Execution.Setup.a M S r := by
    show _ ≤ M.a S.hc S.E.Δ r
    rw [facts.gr.opening_eq_proposal_time, facts.sch.a_eq_confirmation_time]
    exact facts.sch.proposal_time_le_confirmation_time _ _
  have hgstr : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S r) :=
    le_trans (Restated.gst_le_switchOpening facts S tGAT tE gap hgst hlen)
      (le_trans (Restated.switchOpening_le_opening facts S hr) hopen)
  have htm := Restated.time_le_action_succ_of_stepBefore facts S Sched x htd hdom hm
  have htmd : (x[m].time : Int) ≤ M.domain S.E S.hc (r + 1) p :=
    le_of_lt (Restated.time_lt_domain_of_stepBefore facts S Sched x htd hm)
  have ham : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[m].time : Int) := Restated.action_le_time_of_stepBefore facts S Sched x htd hm
  have hrs := Restated.roundSleepinessW_switchOpening_of_phase facts S Sched tGAT tE gap hgst hlen hmono hthird
    hphase hrsW
  exact Restated.grade1_of_sg_prevLate facts S Sched x hexec hsync htd hn hgstr (Restated.HonRound M S Sched r) hinv.sg hm
    (Restated.hfreshH_of_stepBefore facts S Sched x htd hm)
    (awakeThroughout_mono Sched hawT le_rfl htmd)
    (fun hin => hvS (hmono _ _ (le_trans ham htmd) hin))
    (Restated.hexp_of_domain facts S htm)
    (fun k hk v_1 hv_1 a ha _ => Restated.hroom_of_fresh facts S Sched x hexec hn
      (fun t ht => Restated.honestThrough_of_mem_freshAttestersW facts hv_1 t
        (le_trans ht (Restated.time_mono_int facts S Sched x (le_of_lt hk)))) a ha)
    (fun v_1 hv_1 a ha C hC hconf =>
      Restated.freshSGHeads_at_awakeReader facts (hcross := hcross) S Sched x tE hexec hmono htd hsync hmult tGAT gap hgst hlen hcv
        hthird hphase hrsW hcs hr hinv hdom hawT hvS hm hneTick hneAtt v_1 hv_1 C hC a ha hconf)
    (fun v_1 _ a ha root hconf => Restated.hhead_mem_of_tick facts S Sched x n r v_1 a ha root hconf)
    (Restated.hhalf_of_roundSleepinessW facts S Sched x hexec htd hmono hrs
      (Restated.switchOpening_le_opening facts S (le_trans hr (Nat.le_succ r))) hdom hm)
    B hgrade (hneTick n _ hn (Restated.action_emod_delta facts S r)
      (Finset.mem_sdiff.2 ⟨mem_awake_of_awakeThroughout Sched hawT le_rfl (le_trans ham htmd),
        fun hin => hvS (hmono _ _ (le_trans ham htmd) hin)⟩) (le_trans ham (le_trans htmd hdom)))
    (fun v_1 hv_1 => hneAtt v_1 (Restated.hfreshH_of_stepBefore facts S Sched x htd hm hv_1))

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The Goldfish vote instant of the slot `j` places after round `ρ`'s opening slot is
    `S.a ρ − 5Δ + 4jΔ`. -/
theorem vote_time_opening_slot_add (facts : Record.Facts M) (S : Setup V) (ρ : Round) (j : Nat) :
    M.vote_time S.E ((M.opening_slot S.hc ρ) + j)
      = (Restated.Vocabulary.Execution.Setup.a M S ρ) - 5 * S.E.Δ + 4 * S.E.Δ * (j : Int) := by
  have h1 := facts.sch.slotStart_add_delta_eq_vote_time S.E ((M.opening_slot S.hc ρ) + j)
  have h2 := facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E (M.opening_slot S.hc ρ)
  have h3 := facts.sch.a_eq_confirmation_time S.hc S.E ρ
  rw [slotStart_add] at h1
  show _ = M.a S.hc S.E.Δ ρ - _ + _
  linarith

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If round `r` is at or after the switch round, the invariant holds at round `r` with anchor `T`,
    and slot `s + 1` is round `r + 1`'s opening slot or the slot after it, then the SG root every
    honest active member of slot `(s + 1)`'s committee starts its vote walk from lies on one chain
    with `T`. The hypotheses `hneTick` and `hneAtt` ask for tick outcomes as in
    `grade1_compatible_at_awakeReader`, `hneTick` at every such member. -/
theorem coneAnchorCompatible_at_opening_slots (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (hsync : Restated.SynchronyFromWake M S x) (hmult : AwakeAtMultiples S Sched)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE) (hcs : Restated.committeeSleepinessW M S Sched tE)
    {r : Round} {n : Nat} {T : NamedBlock V}
    (hr : Restated.switchRound M S tE ≤ r) (hinv : Restated.AfterPhaseInvariantOverActiveSetsTop M S Sched x r n T)
    (hcross : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepFinalizedCrossingUnderAnchor M S Sched x r n'' T)
    (hjust : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepJustifiedRootUnderAnchor M S Sched x r n n'' T)
    {s : Slot} {j : Nat} (hj : j ≤ 1) (hs : s + 1 = (M.opening_slot S.hc (r + 1)) + j)
    (hneTick : ∀ v ∈ Restated.HonSlot M S Sched (s + 1), ∀ (n' : Nat) (t' : Int),
      Restated.tickStepAt M x n' t' → t' % S.E.Δ = 0 → v ∈ Sched.awake t' \ Sched.adv t' → t' ≤ Restated.Vocabulary.Execution.Setup.a M S (r + 1) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched t' x[n'] v) t' ⇢ out)
    (hneAtt : ∀ v_1 ∈ Restated.HonRound M S Sched r, ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) v_1 (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S r) x[n] v_1) (Restated.Vocabulary.Execution.Setup.a M S r) ⇢ out) :
    Restated.ConeAnchorCompatible M S x T.erase s := by
  have hd := S.E.Δ_pos
  have hd1 : (1 : Int) ≤ S.E.Δ := hd
  have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
  have hRd : 12 * S.E.Δ ≤ 4 * (S.hc.R : Int) * S.E.Δ := by nlinarith
  have hsucc := facts.gr.action_succ_eq_add_rounds S r
  have hj' : (j : Int) ≤ 1 := by exact_mod_cast hj
  have hj0 : (0 : Int) ≤ (j : Int) := by exact_mod_cast Nat.zero_le j
  have hvt : M.vote_time S.E (s + 1) = (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) - 5 * S.E.Δ + 4 * S.E.Δ * (j : Int) := by
    rw [hs]; exact Restated.vote_time_opening_slot_add facts S (r + 1) j
  have hjd : 4 * S.E.Δ * (j : Int) ≤ 4 * S.E.Δ := by nlinarith
  have hjd0 : 0 ≤ 4 * S.E.Δ * (j : Int) := by positivity
  have hround : (M.round_of S.hc (s + 1)) = r + 1 := by
    rw [hs]; exact facts.gr.round_of_opening_slot_add S.hc (r + 1) (by have := S.hc.R_ge_three; omega)
  have hdomEq : M.domain S.E S.hc (r + 1) .g1 + 5 * S.E.Δ
      ≤ Restated.Vocabulary.Execution.Setup.a M S (r + 1) :=
    facts.gr.domain_add_five_delta_le_action S (r + 1) .g1
  have hdom : M.domain S.E S.hc (r + 1) .g1 ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) := facts.gr.domain_le_action S (r + 1) .g1
  refine Restated.coneAnchorCompatible_of_voteReads facts S x ?_
    (Restated.voteFinJustCompatible_of_before_succ_tick facts (hcross := hcross) (hjust := hjust) S Sched x tE hexec hmono htd tGAT gap hgst hlen
      hthird hphase hrsW hr hinv (by rw [hvt]; linarith) (by rw [hvt]; linarith))
  intro v mr hv hmr nr hnr root hroot
  obtain ⟨m, B, hm, hB, hpre⟩ := Restated.voteFrame_g1_provenance facts S Sched x hmr v root hnr hroot
  rw [hround] at hm hB
  -- the voter's awake window
  have hact := ((Restated.mem_HonSlot facts).mp hv).1
  have hwin : v ∈ Sched.awakeThroughout (M.vote_time S.E (s + 1) - wVote S)
      (M.vote_time S.E (s + 1)) := by
    rw [← facts.sch.slotStart_add_delta_eq_vote_time S.E (s + 1)]; exact hact
  have hwv : wVote S = 4 * (S.hc.R : Int) * S.E.Δ + 2 * S.E.Δ := by
    unfold wVote; ring
  have hawT : v ∈ Sched.awakeThroughout ((Restated.Vocabulary.Execution.Setup.a M S r)) (M.domain S.E S.hc (r + 1) .g1) :=
    awakeThroughout_mono Sched hwin (by rw [hvt, hwv]; linarith)
      (by rw [hvt]; linarith)
  have hvS : v ∉ Sched.adv (M.domain S.E S.hc (r + 1) .g1) := by
    intro hin
    refine ((Restated.mem_HonSlot facts).mp hv).2.2 (hmono _ _ ?_ hin)
    have e : M.confirmation_time S.E (s + 1)
        = M.vote_time S.E (s + 1) + 5 * S.E.Δ := by
      have h1 := facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E (s + 1)
      have h2 := facts.sch.slotStart_add_delta_eq_vote_time S.E (s + 1)
      linarith
    rw [e, hvt]; linarith
  obtain ⟨b, hb⟩ := facts.gr.gradeBool_nonempty S.E (M.gradeView (M.toHealing (x[m][v].st).st.core))
    (x[m][v].st).st.core.F S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) .g1) (M.late S.E S.hc (r + 1) .g1) B
  have hbt := hB b hb
  subst hbt
  have hBT := Restated.grade1_compatible_at_awakeReader facts (hcross := hcross) S Sched x tE hexec hmono htd hsync hmult tGAT gap
    hgst hlen hcv hthird hphase hrsW hcs hr hinv hdom hawT hvS hm B hb (hneTick v hv) hneAtt
  exact Protocol.compatible_of_preceq_of_compatible hpre hBT

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Under `Sched.MonotoneCorruption` and `WakesAtActionInstants`, if the invariant holds at round
    `r` with anchor `T`, and slot `s + 1` is `j` places after round `r`'s opening slot with
    `3 ≤ j < R`, then every honest active member of slot `(s + 1)`'s committee has a vote-read
    grade-1 root that lies on one chain with `T`. -/
theorem voteGradeOneCompatible_at_round_slot_of_wakes (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hmono : Sched.MonotoneCorruption) (hw : Restated.WakesAtActionInstants M S Sched)
    {r : Round} {n : Nat} {T : NamedBlock V}
    (hinv : Restated.AfterPhaseInvariantOverActiveSetsTop M S Sched x r n T)
    {s : Slot} {j : Nat} (hj3 : 3 ≤ j) (hjR : j < S.hc.R)
    (hs : s + 1 = (M.opening_slot S.hc r) + j) :
    Restated.VoteGradeOneCompatible M S x T.erase s := by
  have hd := S.E.Δ_pos
  have hj3' : (3 : Int) ≤ (j : Int) := by exact_mod_cast hj3
  have hjR' : (j : Int) + 1 ≤ (S.hc.R : Int) := by exact_mod_cast hjR
  have h12 : 12 * S.E.Δ ≤ 4 * S.E.Δ * (j : Int) := by nlinarith
  have hjRd : 4 * S.E.Δ * (j : Int) + 4 * S.E.Δ ≤ 4 * (S.hc.R : Int) * S.E.Δ := by nlinarith
  have hvt : M.vote_time S.E (s + 1) = (Restated.Vocabulary.Execution.Setup.a M S r) - 5 * S.E.Δ + 4 * S.E.Δ * (j : Int) := by
    rw [hs]; exact Restated.vote_time_opening_slot_add facts S r j
  have hround : (M.round_of S.hc (s + 1)) = r := by
    rw [hs]; exact facts.gr.round_of_opening_slot_add S.hc r hjR
  intro v mr hv hmr nr hnr root hroot
  obtain ⟨m, B, hm, hB, hpre⟩ := Restated.voteFrame_g1_provenance facts S Sched x hmr v root hnr hroot
  rw [hround] at hm hB
  have hwin : v ∈ Sched.awakeThroughout (M.vote_time S.E (s + 1) - wVote S)
      (M.vote_time S.E (s + 1)) := by
    rw [← facts.sch.slotStart_add_delta_eq_vote_time S.E (s + 1)]
    exact ((Restated.mem_HonSlot facts).mp hv).1
  have hwv : wVote S = 4 * (S.hc.R : Int) * S.E.Δ + 2 * S.E.Δ := by
    unfold wVote; ring
  have hact : v ∈ Restated.activeRoundW M S Sched r :=
    Restated.active_of_awake_prev facts S Sched hw
      (mem_awake_of_awakeThroughout Sched hwin (by rw [hvt, hwv]; linarith)
        (by rw [hvt]; linarith))
      (mem_awake_of_awakeThroughout Sched hwin (by rw [hvt, hwv]; linarith)
        (by rw [hvt]; linarith))
  have hvR : v ∈ Restated.HonRound M S Sched r := by
    refine Finset.mem_sdiff.2 ⟨hact, fun hin => ((Restated.mem_HonSlot facts).mp hv).2.2 (hmono _ _ ?_ hin)⟩
    have e : M.confirmation_time S.E (s + 1)
        = M.vote_time S.E (s + 1) + 5 * S.E.Δ := by
      have e1 := facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E (s + 1)
      have e2 := facts.sch.slotStart_add_delta_eq_vote_time S.E (s + 1)
      linarith
    show (Restated.Vocabulary.Execution.Setup.a M S r) ≤ _
    rw [e, hvt]; linarith
  obtain ⟨b, hb⟩ := facts.gr.gradeBool_nonempty S.E (M.gradeView (M.toHealing (x[m][v].st).st.core))
    (x[m][v].st).st.core.F S.hc.η_SG r (M.early S.E S.hc r .g1) (M.late S.E S.hc r .g1) B
  exact Protocol.compatible_of_preceq_of_compatible hpre
    (hinv.grade1 v hvR .g1 (facts.gr.domain_le_action S r .g1) m hm B b hb (hB b hb))

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Under `Sched.MonotoneCorruption` and `WakesAtActionInstants`, if the invariant holds at round
    `r` with anchor `T`, then at every slot of round `r` from three places after its opening slot to
    its last, every honest active member's vote-read grade-1 root lies on one chain with `T`. -/
theorem voteGradeOneAtRoundSlots_of_wakes (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hmono : Sched.MonotoneCorruption) (hw : Restated.WakesAtActionInstants M S Sched)
    {r : Round} {n : Nat} {T : NamedBlock V}
    (hinv : Restated.AfterPhaseInvariantOverActiveSetsTop M S Sched x r n T) :
    ∀ s : Slot, (M.opening_slot S.hc r) + 3 ≤ s + 1 → s + 1 < (M.opening_slot S.hc (r + 1)) →
      Restated.VoteGradeOneCompatible M S x T.erase s := by
  intro s h1 h2
  rw [facts.gr.opening_slot_succ S.hc r] at h2
  obtain ⟨j, hj, hj3, hjR⟩ := slot_offset_aux _ _ _ h1 h2
  exact Restated.voteGradeOneCompatible_at_round_slot_of_wakes facts S Sched x hmono hw hinv hj3 hjR hj

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If round `r` is at or after the switch round, the invariant holds at round `r` with anchor `T`,
    and `WakesAtActionInstants` holds, then `ConeAnchorCompatible` holds at `T` for every slot `s`
    from round `r`'s third slot to round `r + 1`'s opening slot. The hypotheses `hneTick` and
    `hneAtt` ask for tick outcomes as in `coneAnchorCompatible_at_opening_slots`, `hneTick` at the
    committee members of every slot of the range. -/
theorem coneAnchorCompatible_range_at_anchor (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (hsync : Restated.SynchronyFromWake M S x) (hmult : AwakeAtMultiples S Sched)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE) (hcs : Restated.committeeSleepinessW M S Sched tE)
    {r : Round} {n : Nat} {T : NamedBlock V}
    (hr : Restated.switchRound M S tE ≤ r) (hinv : Restated.AfterPhaseInvariantOverActiveSetsTop M S Sched x r n T)
    (hcross : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepFinalizedCrossingUnderAnchor M S Sched x r n'' T)
    (hjust : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) →
      Restated.StepJustifiedRootUnderAnchor M S Sched x r n n'' T)
    (hw : Restated.WakesAtActionInstants M S Sched)
    (hneTick : ∀ s : Slot, (M.opening_slot S.hc r) + 2 ≤ s → s ≤ (M.opening_slot S.hc (r + 1)) →
      ∀ v ∈ Restated.HonSlot M S Sched (s + 1), ∀ (n' : Nat) (t' : Int),
      Restated.tickStepAt M x n' t' → t' % S.E.Δ = 0 → v ∈ Sched.awake t' \ Sched.adv t' → t' ≤ Restated.Vocabulary.Execution.Setup.a M S (r + 1) →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched t' x[n'] v) t' ⇢ out)
    (hneAtt : ∀ v_1 ∈ Restated.HonRound M S Sched r, ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) v_1 (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S r) x[n] v_1) (Restated.Vocabulary.Execution.Setup.a M S r) ⇢ out) :
    ∀ s : Slot, (M.opening_slot S.hc r) + 2 ≤ s → s ≤ (M.opening_slot S.hc (r + 1)) →
      Restated.ConeAnchorCompatible M S x T.erase s := by
  intro s hs0 hs1
  have hneS := hneTick s hs0 hs1
  rw [facts.gr.opening_slot_succ] at hs1
  rcases slot_cases_aux _ _ _ hs0 hs1 with ⟨j, hj, hj3, hjR, hlo3, hlast⟩ | ⟨j, hj, hsj⟩
  · -- round `r`'s slots: `s + 1 = opening_slot r + j` with `3 ≤ j ≤ R - 1`
    have hd := S.E.Δ_pos
    have hj3' : (3 : Int) ≤ (j : Int) := by exact_mod_cast hj3
    have hjR' : (j : Int) + 1 ≤ (S.hc.R : Int) := by exact_mod_cast hjR
    have hvt : M.vote_time S.E (s + 1) = (Restated.Vocabulary.Execution.Setup.a M S r) - 5 * S.E.Δ + 4 * S.E.Δ * (j : Int) := by
      rw [hj]; exact Restated.vote_time_opening_slot_add facts S r j
    have hsucc := facts.gr.action_succ_eq_add_rounds S r
    have h1 : 12 * S.E.Δ ≤ 4 * S.E.Δ * (j : Int) := by nlinarith
    have h2 : 4 * S.E.Δ * (j : Int) + 4 * S.E.Δ ≤ 4 * (S.hc.R : Int) * S.E.Δ := by nlinarith
    exact Restated.coneAnchorCompatible_of_voteReads facts S x
      (Restated.voteGradeOneAtRoundSlots_of_wakes facts S Sched x hmono hw hinv s hlo3
        (by rw [facts.gr.opening_slot_succ]; exact hlast))
      (Restated.voteFinJustCompatible_of_before_succ_tick facts (hcross := hcross) (hjust := hjust) S Sched x tE hexec hmono htd tGAT gap hgst hlen
        hthird hphase hrsW hr hinv (by rw [hvt]; linarith) (by rw [hvt]; linarith))
  · exact Restated.coneAnchorCompatible_at_opening_slots facts (hcross := hcross) (hjust := hjust) S Sched x tE hexec hmono htd hsync hmult tGAT gap
      hgst hlen hcv hthird hphase hrsW hcs hr hinv hj (by rw [facts.gr.opening_slot_succ]; exact hsj)
      hneS hneAtt

end

end DecoupledConsensusModel.Sts.Restated
