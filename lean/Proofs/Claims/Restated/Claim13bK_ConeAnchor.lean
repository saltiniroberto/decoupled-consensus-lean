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
import Proofs.Claims.Restated.Claim13bW_ReceiptRule
import Proofs.Claims.Restated.Claim13bK_ConeAnchorRecv
import Proofs.Claims.Restated.Claim13bInvariantGrade1RuleFacts

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
  have hd1 : (1 : Int) ≤ S.E.Δ := S.E.Δ_pos
  have hlo := facts.gr.action_delta_le_early S S.hc.R_ge_three (Nat.lt_succ_self r)
  have h21 := facts.gr.early_g2_add_delta_le_early_g1 S (r + 1)
  have he0 := facts.gr.early_g1_add_delta_le_early_g0 S (r + 1)
  have hl0 := facts.gr.early_le_late S.E S.hc (r + 1) .g0
  have hl1 := facts.gr.late_g0_add_delta_le_late_g1 S (r + 1)
  have ht₀ : Restated.Vocabulary.Execution.Setup.a M S r ≤ M.late S.E S.hc (r + 1) .g1 - 1 - 2 * S.E.Δ := by
    show M.a S.hc S.E.Δ r ≤ _
    linarith
  have hrecv := Restated.receives_of_awake_from_action facts S Sched x hsync .g1
    (Restated.gst_le_action_of_switchRound_le facts S tGAT tE gap hgst hlen hr) hawT
    (le_of_lt (lt_of_lt_of_le (Restated.action_delta_lt_domain_succ facts S r .g1) le_rfl))
  have hBT := Restated.grade1_compatible_at_awakeReader_recv facts (hcross := hcross) S Sched x tE hexec hmono htd hsync hmult tGAT gap
    hgst hlen hcv hthird hphase hrsW hcs hr hinv hdom _ ht₀ hawT hrecv hvS hm B hb (hneTick v hv) hneAtt
  exact Protocol.compatible_of_preceq_of_compatible hpre hBT

end

-- Folded in from the former module `Claim13bK_PrevHeadsStepRule.lean` (wake switch, lane S).
/-!
# A slot voter's grade-1 window and its receipt of the previous round's attestations

An honest active member of the committee of a slot of round `ρ` is awake at every time from round
`ρ`'s grade-1 window start to round `ρ`'s grade-1 domain instant, and is not held by the adversary
there. Under synchrony and catch-up, such a voter of a slot of round `r + 1` receives round `r`'s
honest attestations strictly before round `r + 1`'s grade-1 early cutoff. Stated over a model
`M : Record.Model V`.
-/

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Round `ρ`'s grade-1 window start minus one delay is a whole multiple of `Δ` from round `1` on. -/
theorem early_g1_sub_delta_emod (facts : Record.Facts M) (S : Setup V) {ρ : Round} (hρ : 0 < ρ) :
    (M.early S.E S.hc ρ .g1 - S.E.Δ) % S.E.Δ = 0 := by
  obtain ⟨k, hk⟩ := facts.gr.q10_early_g1_public S ρ hρ
  rw [hk, show (k : Int) * S.E.Δ - S.E.Δ = ((k : Int) - 1) * S.E.Δ by ring]
  exact Int.mul_emod_left _ _

/-- A member of `HonSlot S Sched (opening_slot ρ + j)`, with `j < R`, is awake at every time from
    round `ρ`'s grade-1 window start to round `ρ`'s grade-1 domain instant, and is not held by the
    adversary at that domain instant.

    Variables: `ρ` the round, `j` the slot's place in the round, `v` the voter. -/
theorem awakeThroughout_grade1_window_of_mem_honSlot (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (hmono : Sched.MonotoneCorruption)
    {ρ : Round} {j : Nat} (hjR : j < S.hc.R) {v : V}
    (hv : v ∈ Restated.HonSlot M S Sched ((M.opening_slot S.hc ρ) + j)) :
    v ∈ Sched.awakeThroughout (M.early S.E S.hc ρ .g1 - S.E.Δ) (M.domain S.E S.hc ρ .g1) ∧
      v ∉ Sched.adv (M.domain S.E S.hc ρ .g1) := by
  have hd := S.E.Δ_pos
  have hjR' : (j : Int) + 1 ≤ (S.hc.R : Int) := by exact_mod_cast hjR
  have hj0 : (0 : Int) ≤ (j : Int) := by exact_mod_cast Nat.zero_le j
  have hvt := Restated.vote_time_opening_slot_add facts S ρ j
  have he2 := facts.gr.early_g2_eq S ρ
  have he21 := facts.gr.early_g2_add_delta_le_early_g1 S ρ
  have hdom := facts.gr.domain_add_five_delta_le_action S ρ .g1
  change M.vote_time S.E ((M.opening_slot S.hc ρ) + j) = M.a S.hc S.E.Δ ρ - 5 * S.E.Δ + _ at hvt
  have hwin : v ∈ Sched.awakeThroughout
      (M.vote_time S.E ((M.opening_slot S.hc ρ) + j) - wVote S)
      (M.vote_time S.E ((M.opening_slot S.hc ρ) + j)) := by
    rw [← facts.sch.slotStart_add_delta_eq_vote_time S.E ((M.opening_slot S.hc ρ) + j)]
    exact ((Restated.mem_HonSlot facts).mp hv).1
  have hwv : wVote S = 4 * (S.hc.R : Int) * S.E.Δ + 2 * S.E.Δ := by unfold wVote; ring
  have hjd : 4 * S.E.Δ * (j : Int) + 4 * S.E.Δ ≤ 4 * (S.hc.R : Int) * S.E.Δ := by nlinarith
  have hj0d : 0 ≤ 4 * S.E.Δ * (j : Int) := by positivity
  refine ⟨awakeThroughout_mono Sched hwin ?_ ?_, fun hin => ?_⟩
  · rw [hvt, hwv]; linarith
  · rw [hvt]
    change M.domain S.E S.hc ρ .g1 + 5 * S.E.Δ ≤ M.a S.hc S.E.Δ ρ at hdom
    linarith
  · refine ((Restated.mem_HonSlot facts).mp hv).2.2 (hmono _ _ ?_ hin)
    have e6 := facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E ((M.opening_slot S.hc ρ) + j)
    have e1 := facts.sch.slotStart_add_delta_eq_vote_time S.E ((M.opening_slot S.hc ρ) + j)
    change M.domain S.E S.hc ρ .g1 + 5 * S.E.Δ ≤ M.a S.hc S.E.Δ ρ at hdom
    linarith

/-- Under synchrony and catch-up, a validator awake at every time from round `r + 1`'s grade-1 window
    start to its grade-1 domain instant, with `t_GST` at or before round `r`'s action instant,
    receives round `r`'s honest attestations strictly before round `r + 1`'s grade-1 early cutoff.

    Variables: `r` the round of the attestations, `v` the receiver. -/
theorem receivesRoundAttestationsBefore_of_grade1_window (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hsync : Restated.SynchronyFromWake M S x) (hcatch : Restated.CatchUpOnWake M S x)
    {r : Round} (hgst : S.E.t_GST ≤ Restated.Vocabulary.Execution.Setup.a M S r) {v : V}
    (hwin : v ∈ Sched.awakeThroughout (M.early S.E S.hc (r + 1) .g1 - S.E.Δ)
      (M.domain S.E S.hc (r + 1) .g1)) :
    Restated.ReceivesRoundAttestationsBefore M S Sched x r v (M.early S.E S.hc (r + 1) .g1) := by
  have hd := S.E.Δ_pos
  have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
  have hsucc := facts.gr.action_succ_eq_add_rounds S r
  have he2 := facts.gr.early_g2_eq S (r + 1)
  have he21 := facts.gr.early_g2_add_delta_le_early_g1 S (r + 1)
  have hle := facts.gr.early_g1_le_domain_g1 S (r + 1)
  change M.a S.hc S.E.Δ (r + 1) = M.a S.hc S.E.Δ r + 4 * (S.hc.R : Int) * S.E.Δ at hsucc
  change S.E.t_GST ≤ M.a S.hc S.E.Δ r at hgst
  have h12 : 12 * S.E.Δ ≤ 4 * (S.hc.R : Int) * S.E.Δ := by nlinarith
  have ht₀ : Restated.Vocabulary.Execution.Setup.a M S r ≤ M.early S.E S.hc (r + 1) .g1 - S.E.Δ := by
    change M.a S.hc S.E.Δ r ≤ _
    linarith
  have h := Restated.receivesRoundAttestationsBefore_of_awakeFrom facts S Sched x hsync hcatch
    (v := v) ht₀ (by linarith)
    (awakeThroughout_mono Sched hwin le_rfl (by linarith))
  rwa [sub_add_cancel] at h

/-- Under synchrony and catch-up, a member of `HonSlot S Sched (opening_slot (r + 1) + j)`, with
    `j < R`, receives round `r`'s honest attestations strictly before round `r + 1`'s grade-1 early
    cutoff, when `t_GST` is at or before round `r`'s action instant.

    Variables: `r` the round of the attestations, `j` the slot's place in round `r + 1`, `v` the
    voter. -/
theorem receivesRoundAttestationsBefore_of_mem_honSlot (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hmono : Sched.MonotoneCorruption)
    (hsync : Restated.SynchronyFromWake M S x) (hcatch : Restated.CatchUpOnWake M S x)
    {r : Round} (hgst : S.E.t_GST ≤ Restated.Vocabulary.Execution.Setup.a M S r)
    {j : Nat} (hjR : j < S.hc.R) {v : V}
    (hv : v ∈ Restated.HonSlot M S Sched ((M.opening_slot S.hc (r + 1)) + j)) :
    Restated.ReceivesRoundAttestationsBefore M S Sched x r v (M.early S.E S.hc (r + 1) .g1) :=
  Restated.receivesRoundAttestationsBefore_of_grade1_window facts S Sched x hsync hcatch hgst
    (Restated.awakeThroughout_grade1_window_of_mem_honSlot facts S Sched hmono hjR hv).1

end


-- Folded in from the former module `Claim13bK_HeadsNewAnchorJointRule.lean` (wake switch, lane S).
/-!
# Vote-read grade-1 roots of round `r + 1`'s voters, asked of the grade-1 readers that received round `r`'s attestations

`VoteGradeOneCompatible` at a slot of round `r + 1` from a compatibility hypothesis on the blocks a
validator grades at least 1 for round `r + 1`, asked only of the validators awake from some time
`t₀`, between round `r`'s action instant and round `r + 1`'s grade-1 window start, to round
`r + 1`'s grade-1 domain instant, that receive round `r`'s honest attestations before round
`r + 1`'s grade-1 early cutoff. Stated over a model `M : Record.Model V`.
-/

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Round `r`'s action instant is at or before round `r + 1`'s grade-1 window start. -/
theorem action_le_early_g1_succ_sub_delta (facts : Record.Facts M) (S : Setup V) (r : Round) :
    Restated.Vocabulary.Execution.Setup.a M S r ≤ M.early S.E S.hc (r + 1) .g1 - S.E.Δ := by
  have hd := S.E.Δ_pos
  have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
  have hsucc := facts.gr.action_succ_eq_add_rounds S r
  have he2 := facts.gr.early_g2_eq S (r + 1)
  have he21 := facts.gr.early_g2_add_delta_le_early_g1 S (r + 1)
  change M.a S.hc S.E.Δ (r + 1) = M.a S.hc S.E.Δ r + 4 * (S.hc.R : Int) * S.E.Δ at hsucc
  have h12 : 12 * S.E.Δ ≤ 4 * (S.hc.R : Int) * S.E.Δ := by nlinarith
  change M.a S.hc S.E.Δ r ≤ _
  linarith

/-- If every block that a grade-1 performer of round `r + 1` grades at least 1 for round `r + 1`, at
    the last step before round `r + 1`'s grade-1 domain instant, is compatible with `D`, and slot
    `s + 1` is `j < R` slots after round `(r + 1)`'s opening slot, then `VoteGradeOneCompatible` holds
    at `D` and `s`: every honest active member of slot `s + 1`'s committee is such a performer.

    Variables: `r` the round, `D` the block, `s` the slot before the voters' slot, `j` the voters'
    slot's place in round `r + 1`. -/
theorem voteGradeOneCompatible_of_gradedCompatible_rule (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hmono : Sched.MonotoneCorruption) {r : Round} {D : Block V}
    (hgc : ∀ v ∈ Restated.grade1PerformersW M S Sched (r + 1),
      ∀ m : Nat, Restated.stepBeforeInstant M x m (M.domain S.E S.hc (r + 1) .g1) →
      ∀ B : Block V,
        M.gradeBool S.E (M.gradeView (M.toHealing (x[m][v].st).st.core))
          (x[m][v].st).st.core.F S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) .g1)
          (M.late S.E S.hc (r + 1) .g1) B ⇢ true →
        Block.compatible B D = true)
    {s : Slot} {j : Nat} (hjR : j < S.hc.R) (hs : s + 1 = (M.opening_slot S.hc (r + 1)) + j) :
    Restated.VoteGradeOneCompatible M S x D s := by
  have hround : (M.round_of S.hc (s + 1)) = r + 1 := by
    rw [hs]; exact facts.gr.round_of_opening_slot_add S.hc (r + 1) hjR
  intro v mr hv hmr nr hnr root hroot
  obtain ⟨m, B, hm, hBall, hpre⟩ := Restated.voteFrame_g1_provenance facts S Sched x hmr v root hnr hroot
  rw [hround] at hm hBall
  obtain ⟨b, hb⟩ := facts.gr.gradeBool_nonempty S.E
    (M.gradeView (M.toHealing (x[m][v].st).st.core)) (x[m][v].st).st.core.F S.hc.η_SG (r + 1)
    (M.early S.E S.hc (r + 1) .g1) (M.late S.E S.hc (r + 1) .g1) B
  have hB : M.gradeBool S.E (M.gradeView (M.toHealing (x[m][v].st).st.core))
      (x[m][v].st).st.core.F S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) .g1)
      (M.late S.E S.hc (r + 1) .g1) B ⇢ true := by
    rw [← hBall b hb]; exact hb
  have hv' : v ∈ Restated.HonSlot M S Sched ((M.opening_slot S.hc (r + 1)) + j) := by
    rw [← hs]; exact hv
  have hvP : v ∈ Restated.grade1PerformersW M S Sched (r + 1) :=
    Finset.mem_sdiff.2 (Restated.awakeThroughout_grade1_window_of_mem_honSlot facts S Sched hmono hjR hv')
  exact Protocol.compatible_of_preceq_of_compatible hpre (hgc v hvP m hm B hB)

end


-- Folded in from the former module `Claim13bK_ConeAnchorRule.lean` (wake switch, lane S).
/-!
# Vote-read grade-1 roots at the later slots of a round, from its grade-1 readers

`VoteGradeOneCompatible` at the slots of round `r + 1` from three places after its opening slot to
its last, from a compatibility hypothesis on the blocks a validator grades at least 1 for round
`r + 1`, asked only of the validators awake from some time `t₀` to round `r + 1`'s grade-1 domain
instant that receive round `r`'s honest attestations before round `r + 1`'s grade-1 early cutoff.
Stated over a model `M : Record.Model V`.
-/

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution


end


section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If round `r` is at or after the switch round, the invariant holds at round `r` with anchor `T`, then `ConeAnchorCompatible` holds at `T` for every slot `s`
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
    have hgr1 : Restated.VoteGradeOneCompatible M S x T.erase s := by
      intro v mr hv hmr nr hnr root hroot
      obtain ⟨m, B, hm, hBall, hpre⟩ := Restated.voteFrame_g1_provenance facts S Sched x hmr v root hnr hroot
      have hround : (M.round_of S.hc (s + 1)) = r := by
        rw [hj]; exact facts.gr.round_of_opening_slot_add S.hc r hjR
      rw [hround] at hm hBall
      have hv' : v ∈ Restated.HonSlot M S Sched ((M.opening_slot S.hc r) + j) := by rw [← hj]; exact hv
      have hvP : v ∈ Restated.grade1PerformersW M S Sched r :=
        Finset.mem_sdiff.2 (Restated.awakeThroughout_grade1_window_of_mem_honSlot facts S Sched hmono hjR hv')
      obtain ⟨b, hb⟩ := facts.gr.gradeBool_nonempty S.E (M.gradeView (M.toHealing (x[m][v].st).st.core))
        (x[m][v].st).st.core.F S.hc.η_SG r (M.early S.E S.hc r .g1) (M.late S.E S.hc r .g1) B
      exact Protocol.compatible_of_preceq_of_compatible hpre
        (hinv.grade1Performers v hvP m hm B b hb (hBall b hb))
    exact Restated.coneAnchorCompatible_of_voteReads facts S x hgr1
      (Restated.voteFinJustCompatible_of_before_succ_tick facts (hcross := hcross) (hjust := hjust) S Sched x tE hexec hmono htd tGAT gap hgst hlen
        hthird hphase hrsW hr hinv (by rw [hvt]; linarith) (by rw [hvt]; linarith))
  · exact Restated.coneAnchorCompatible_at_opening_slots facts (hcross := hcross) (hjust := hjust) S Sched x tE hexec hmono htd hsync hmult tGAT gap
      hgst hlen hcv hthird hphase hrsW hcs hr hinv hj (by rw [facts.gr.opening_slot_succ]; exact hsj)
      hneS hneAtt

end

end DecoupledConsensusModel.Sts.Restated
