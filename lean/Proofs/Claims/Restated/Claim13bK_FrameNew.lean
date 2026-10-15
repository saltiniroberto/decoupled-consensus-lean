import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bInvariantActive
import Proofs.Claims.Restated.Claim13bK_Frame
import Proofs.Claims.Restated.Claim13bK_FreshAttestersW
import Proofs.Claims.Restated.Claim13bStepGrade
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bStepPairwise
import Proofs.Claims.Restated.Claim13bStepRoots
import Proofs.Claims.Restated.Claim13bW_Schedule
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActive
import Model.Conditions.Claim13bK_FreshAttestersW
import Model.Conditions.Claim13bStepAnchor
import Model.Conditions.Claim13bStepGrade
import Model.Conditions.Claim13bStepPairwise
import Model.Conditions.Claim13bStepSG
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13b
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring

/-!
# Grade-1 entries of action frames and the SG fields

Where the grade-1 entry of a round's action frame comes from, and the SG fields at a new anchor and
at the next round over the honest attesters `HonRound`, stated over a model `M : Record.Model V`.
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

/-- If some round-`r₁` action frame `f` `v` can read after the tick step at `S.a r₁` offers `root`
    as its grade-1 entry, then `root` is an ancestor of a block every outcome of whose grade test on
    `v`'s store, for round `r₁` at the step before the grade-1 domain time with the grade-1 cutoffs,
    is `true`. -/
theorem actionFrame_g1_provenance (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    {r₁ : Round} {n' : Nat} (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S r₁)))
    (v : V) (root : Block V)
    (f : M.Frame) (hf : f ∈ Restated.actionFrame M S (x[n'][v].st) r₁)
    (h : f.g1 = some (some root)) :
    ∃ (m : Nat) (B : Block V),
      Restated.stepBeforeInstant M x m (M.domain S.E S.hc r₁ .g1) ∧
      (∀ b : Bool, M.gradeBool S.E (M.gradeView (M.toHealing (x[m][v].st).st.core))
        (x[m][v].st).st.core.F S.hc.η_SG r₁ (M.early S.E S.hc r₁ .g1)
        (M.late S.E S.hc r₁ .g1) B ⇢ b → b = true) ∧
      Block.Preceq root B :=
  Restated.phaseResult_actionFrame_provenance facts S Sched x hn' v .g1 root f hf
    ((facts.gr.phaseResult_g1 _).trans h)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If every block whose grade test a member of `HonRound S Sched (r + 1)` runs for round `r + 1` at
    the step before a phase domain time at or before `S.a (r + 1)` can return `true` lies on one
    chain with `A`, then every grade-1 root of every round-`(r + 1)` action frame such a member can
    read after the tick step at `S.a (r + 1)` lies on one chain with `A`. -/
theorem frameG1_compatible_of_grade1 (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (r : Round) (n' : Nat) (A : NamedBlock V)
    (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    (hgrade : ∀ v ∈ Restated.HonRound M S Sched (r + 1),
      ∀ p : Protocol.Phase, M.domain S.E S.hc (r + 1) p ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) →
      ∀ m : Nat, Restated.stepBeforeInstant M x m (M.domain S.E S.hc (r + 1) p) →
      ∀ B : Block V,
        M.gradeBool S.E (M.gradeView (M.toHealing (x[m][v].st).st.core))
            (x[m][v].st).st.core.F S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) p)
            (M.late S.E S.hc (r + 1) p) B ⇢ true →
        Block.compatible B A.erase = true) :
    ∀ v ∈ Restated.HonRound M S Sched (r + 1),
      ∀ f ∈ Restated.actionFrame M S (x[n'][v].st) (r + 1), ∀ root : Block V,
      f.g1 = some (some root) →
      Block.compatible root A.erase = true := by
  intro v hv f hf root hroot
  obtain ⟨m, B, hm, hB, hpre⟩ :=
    Restated.actionFrame_g1_provenance facts S Sched x hn' v root f hf hroot
  obtain ⟨b, hb⟩ := facts.gr.gradeBool_nonempty S.E (M.gradeView (M.toHealing (x[m][v].st).st.core))
    (x[m][v].st).st.core.F S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) .g1)
    (M.late S.E S.hc (r + 1) .g1) B
  have htrue := hB b hb
  subst htrue
  exact Protocol.compatible_of_preceq_of_compatible hpre
    (hgrade v hv .g1 (facts.gr.domain_le_action S (r + 1) .g1) m hm B hb)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If validators wake only at action times and `n'` is the tick step at `S.a (r + 1)`, then every
    validator awake throughout the `4Δ` before `S.a (r + 1)` and honest through step `n' + 1` is in
    `HonRound S Sched (r + 1)`. -/
theorem mem_honRound_of_mem_freshAttesters_ofWakes (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (hw : Restated.WakesAtActionInstants M S Sched)
    {r : Round} {n' : Nat} (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1)))) {v : V}
    (hv : v ∈ Restated.freshAttesters M S Sched x (r + 1) (n' + 1)) :
    v ∈ Restated.HonRound M S Sched (r + 1) := by
  have hwin := ((Restated.mem_freshAttesters facts).mp hv).1
  simp only [Restated.activeRound] at hwin
  have hd := S.E.Δ_pos
  have hprev : v ∈ Sched.awake ((Restated.Vocabulary.Execution.Setup.a M S (r + 1)) - 1) :=
    mem_awake_of_awakeThroughout Sched hwin (by linarith) (by linarith)
  have hW : v ∈ Restated.freshAttestersW M S Sched x (r + 1) (n' + 1) :=
    (Restated.mem_freshAttestersW facts).mpr
      ⟨Restated.active_of_awake_prev facts S Sched hw (Restated.awake_of_mem_freshAttesters facts hv) hprev,
        Restated.honestThrough_of_mem_freshAttesters facts hv⟩
  exact Restated.freshAttestersW_subset_honRound facts S Sched x (le_of_eq (Restated.tickStepAt_time facts x hn').1.symm) hW

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Some node state `n` is in round `r₁`'s action read from `before`, and some grade read `g` is an
    outcome of `M.frameGradeRead` at `n`'s cache and healing store. -/
private theorem exists_actionRead_gradeRead_frameNew (facts : Record.Facts M) (S : Setup V)
    (before : M.N) (r₁ : Round) :
    ∃ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        before r₁,
      ∃ g, M.frameGradeRead n.cache S.E S.hc (M.toHealing n.st.core) r₁ ⇢ g := by
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc before.st.core.toHealing
    (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) r₁) before.cache
  obtain ⟨D, hD⟩ := facts.dt.duties_update_confirmation_with_nonempty (M.gradeContract c) S.E S.hc
    (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) r₁))
    (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) r₁) - 1)
  refine ⟨M.mkNode D before.record c, ⟨c, hc, D, hD, rfl⟩, ?_⟩
  obtain ⟨g, hg⟩ := facts.gr.read_nonempty (M.gradeContract (M.mkNode D before.record c).cache)
    S.E S.hc (M.toHealing (M.mkNode D before.record c).st.core) r₁
  exact ⟨g, (facts.nd.gradeContract_read _ _ _ _ _ g).1 hg⟩

/-- For a choice `att` of the round-`(r + 1)` action attestations, if the confirmed block of every
    honest active attester's round-`(r + 1)` action read meets `hconf`, the finalized and justified
    blocks of every round-`(r + 1)` action read of a validator honest through `S.a (r + 1)` meet
    `hF` and `hJpre`, and the grade-1 and grade-2 frame roots of every honest active attester of
    round `r + 1` lie on one chain with the round-`(r + 1)` anchor, then every SG block an honest
    active attester of round `r + 1` attested to at that round lies on one chain with the
    round-`(r + 1)` anchor read along `att`. -/
theorem sg_field_at_new_anchor_overActiveSets_ofFrameOverHonRound (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption)
    {r : Round} {n' : Nat} {T : NamedBlock V}
    (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    {att : V → NamedAttestation V} (hatt : Restated.ActionAttestationsOf M S Sched x r n' att)
    (hold : Block.Preceq T.erase (Restated.newAnchor M S Sched x r n' att T).erase)
    (hconf : ∀ v ∈ Restated.HonRound M S Sched (r + 1),
      ∀ hs ∈ Restated.actionHealingStore M S (x[n'][v].st) (r + 1),
      Block.compatible hs.live_confirmed
        (Restated.newAnchor M S Sched x r n' att T).erase = true)
    (hg1 : ∀ v ∈ Restated.HonRound M S Sched (r + 1),
      ∀ f ∈ Restated.actionFrame M S (x[n'][v].st) (r + 1), ∀ root : Block V,
      f.g1 = some (some root) →
      Block.compatible root (Restated.newAnchor M S Sched x r n' att T).erase = true)
    (hg2 : ∀ v ∈ Restated.HonRound M S Sched (r + 1),
      ∀ f ∈ Restated.actionFrame M S (x[n'][v].st) (r + 1), ∀ root : Block V,
      f.g2 = some (some root) →
      Block.compatible root (Restated.newAnchor M S Sched x r n' att T).erase = true)
    (hF : ∀ v ∈ honestThroughSet Sched ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))),
      ∀ hs ∈ Restated.actionHealingStore M S (x[n'][v].st) (r + 1),
      Block.Preceq hs.F (Restated.newAnchor M S Sched x r n' att T).erase)
    (hJpre : ∀ v ∈ honestThroughSet Sched ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))),
      ∀ hs ∈ Restated.actionHealingStore M S (x[n'][v].st) (r + 1),
      hs.h_max = hs.h_j + 1 → Block.Preceq hs.J T.erase) :
    ∀ v ∈ Restated.HonRound M S Sched (r + 1), ∀ a : NamedAttestation V,
      a.round = r + 1 → a.val_index = v →
      (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n' + 1].sent →
      ∀ C : NamedBlock V, C ∈ (x[n' + 1][v].st).st.bodies → a.confirmed = some C.root →
      Block.compatible C.erase (Restated.newAnchor M S Sched x r n' att T).erase = true := by
  have htH : (x[n' + 1].time : Int) ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) := le_of_eq (Restated.tickStepAt_time facts x hn').1
  intro v hv a haround hidx hsent C hC hconfC
  have hw : v ∈ honestThroughSet Sched ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) :=
    Restated.honRound_subset_honestThroughSet facts S Sched (r + 1) hmono hv
  -- one node state of the action read and one grade read at it
  obtain ⟨n, hn, g, hg⟩ := exists_actionRead_gradeRead_frameNew facts S (x[n'][v].st) (r + 1)
  have hhs : M.toHealing n.st.core ∈ Restated.actionHealingStore M S (x[n'][v].st) (r + 1) :=
    ⟨n, hn, rfl⟩
  have hf : M.readFrame n.cache (M.toHealing n.st.core) (r + 1)
      ∈ Restated.actionFrame M S (x[n'][v].st) (r + 1) := ⟨n, hn, rfl⟩
  have hroot := Restated.attest_confirmed_sgVote_root facts S Sched x hn' htH hw haround
    hexec.toUnforgeability hidx hsent hconfC n hn g hg
  have hfg : Block.compatible
      (M.get_fg_root (M.toHealing n.st.core).toFG)
      (Restated.newAnchor M S Sched x r n' att T).erase = true :=
    facts.fc.fgRoot_compatible_ofJustifiedBranch (hF v hw _ hhs)
      (fun hroot => compatible_of_preceq_common_Preceq
        (preceq_trans_Preceq (hJpre v hw _ hhs hroot) hold)
        (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _)))
  -- the anchor, grade-2 and SG vote steps, from `sgVote_compatible_at_read`
  have hsg := Restated.sgVote_compatible_at_read facts S (x[n'][v].st) (r + 1) n hn g hg
    (hconf v hv _ hhs) (hg1 v hv _ hf) (hg2 v hv _ hf) hfg
  have hvh : Restated.HonestThrough M Sched x n' v := fun t ht =>
    (mem_honestThroughSet.1 hw) t
      (le_trans ht (le_trans (Restated.time_mono_int facts S Sched x (Nat.le_succ n')) htH))
  obtain ⟨D, hD, hDe⟩ := Restated.exists_inLog_erase_actionSGVote facts S Sched x hvh (r + 1) n hn g hg
  refine Restated.rootResolves_of_collisionFree facts S Sched x hexec r n' att hatt T hn' v hw C D hC hD ?_ ?_
  · rw [hroot, ← hDe, Proofs.NamedWire.erase_root]
  · rw [hDe]; exact hsg

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For every choice `att` of attestations: if, for every honest active attester of round `r + 1`,
    the fork-choice root of its round-`(r + 1)` action read is an ancestor of the round-`(r + 1)`
    anchor and its SG walk's output lies on one chain with that anchor, and `GradePairwise` holds at
    any two such attesters' reads, then any two SG blocks that honest active attesters of round
    `r + 1` attested to at that round lie on one chain. -/
theorem sgPairwise_field_at_succ_overActiveSets_overHonRound (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption)
    {r : Round} {n' : Nat} {att : V → NamedAttestation V} {T : NamedBlock V}
    (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    (hfg : ∀ v ∈ Restated.HonRound M S Sched (r + 1),
      ∀ hs ∈ Restated.actionHealingStore M S (x[n'][v].st) (r + 1),
      Block.Preceq (M.get_fg_root hs.toFG) (Restated.newAnchor M S Sched x r n' att T).erase)
    (hwalk : ∀ v ∈ Restated.HonRound M S Sched (r + 1),
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (x[n'][v].st) (r + 1),
      ∀ g, M.frameGradeRead n.cache S.E S.hc (M.toHealing n.st.core) (r + 1) ⇢ g →
      Block.compatible (M.currentSGVote (M.toHealing n.st.core) g)
        (Restated.newAnchor M S Sched x r n' att T).erase = true)
    (hlc : ∀ v₁ ∈ Restated.HonRound M S Sched (r + 1), ∀ v₂ ∈ Restated.HonRound M S Sched (r + 1),
      ∀ hs₁ ∈ Restated.actionHealingStore M S (x[n'][v₁].st) (r + 1),
      ∀ hs₂ ∈ Restated.actionHealingStore M S (x[n'][v₂].st) (r + 1),
      Block.compatible hs₁.live_confirmed hs₂.live_confirmed = true)
    (hgrade : ∀ v₁ ∈ Restated.HonRound M S Sched (r + 1), ∀ v₂ ∈ Restated.HonRound M S Sched (r + 1),
      ∀ n₁ ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (x[n'][v₁].st) (r + 1),
      ∀ g₁, M.frameGradeRead n₁.cache S.E S.hc (M.toHealing n₁.st.core) (r + 1) ⇢ g₁ →
      ∀ n₂ ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (x[n'][v₂].st) (r + 1),
      ∀ g₂, M.frameGradeRead n₂.cache S.E S.hc (M.toHealing n₂.st.core) (r + 1) ⇢ g₂ →
      Restated.GradePairwise M (M.toHealing n₁.st.core) (M.toHealing n₂.st.core) g₁ g₂) :
    ∀ v₁ ∈ Restated.HonRound M S Sched (r + 1), ∀ v₂ ∈ Restated.HonRound M S Sched (r + 1),
      ∀ a₁ a₂ : NamedAttestation V,
      a₁.round = r + 1 → a₁.val_index = v₁ →
      (⟨v₁, NamedObject.attest a₁⟩ : SignedMsg V (NamedObject V)) ∈ x[n' + 1].sent →
      a₂.round = r + 1 → a₂.val_index = v₂ →
      (⟨v₂, NamedObject.attest a₂⟩ : SignedMsg V (NamedObject V)) ∈ x[n' + 1].sent →
      ∀ C₁ C₂ : NamedBlock V,
      C₁ ∈ (x[n' + 1][v₁].st).st.bodies → a₁.confirmed = some C₁.root →
      C₂ ∈ (x[n' + 1][v₂].st).st.bodies → a₂.confirmed = some C₂.root →
      Block.compatible C₁.erase C₂.erase = true := by
  have htH : (x[n' + 1].time : Int) ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) := le_of_eq (Restated.tickStepAt_time facts x hn').1
  have hsub : Restated.HonRound M S Sched (r + 1) ⊆ honestThroughSet Sched ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) :=
    Restated.honRound_subset_honestThroughSet facts S Sched (r + 1) hmono
  have honest : ∀ v ∈ honestThroughSet Sched ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))), Restated.HonestThrough M Sched x n' v :=
    fun v hv t ht => (mem_honestThroughSet.1 hv) t
      (le_trans ht (le_trans (Restated.time_mono_int facts S Sched x (Nat.le_succ n')) htH))
  intro v₁ hv₁ v₂ hv₂ a₁ a₂ ha₁r hi₁ hs₁ ha₂r hi₂ hs₂ C₁ C₂ hC₁ hc₁ hC₂ hc₂
  have hw₁ := hsub hv₁
  have hw₂ := hsub hv₂
  have hunf := hexec.toUnforgeability
  -- one node state of each action read and one grade read at it
  obtain ⟨n₁, hn₁, g₁, hg₁⟩ := exists_actionRead_gradeRead_frameNew facts S (x[n'][v₁].st) (r + 1)
  obtain ⟨n₂, hn₂, g₂, hg₂⟩ := exists_actionRead_gradeRead_frameNew facts S (x[n'][v₂].st) (r + 1)
  have hroot₁ := Restated.attest_confirmed_sgVote_root facts S Sched x hn' htH hw₁ ha₁r hunf hi₁
    hs₁ hc₁ n₁ hn₁ g₁ hg₁
  have hroot₂ := Restated.attest_confirmed_sgVote_root facts S Sched x hn' htH hw₂ ha₂r hunf hi₂
    hs₂ hc₂ n₂ hn₂ g₂ hg₂
  have hpair := Restated.sgVote_pairwise_compatible facts
    (hlc v₁ hv₁ v₂ hv₂ _ ⟨n₁, hn₁, rfl⟩ _ ⟨n₂, hn₂, rfl⟩)
    (hfg v₁ hv₁ _ ⟨n₁, hn₁, rfl⟩) (hfg v₂ hv₂ _ ⟨n₂, hn₂, rfl⟩)
    (hwalk v₁ hv₁ n₁ hn₁ g₁ hg₁) (hwalk v₂ hv₂ n₂ hn₂ g₂ hg₂)
    (hgrade v₁ hv₁ v₂ hv₂ n₁ hn₁ g₁ hg₁ n₂ hn₂ g₂ hg₂)
  obtain ⟨D₁, hD₁, hD₁e⟩ := Restated.exists_inLog_erase_actionSGVote facts S Sched x (honest v₁ hw₁)
    (r + 1) n₁ hn₁ g₁ hg₁
  obtain ⟨D₂, hD₂, hD₂e⟩ := Restated.exists_inLog_erase_actionSGVote facts S Sched x (honest v₂ hw₂)
    (r + 1) n₂ hn₂ g₂ hg₂
  refine Restated.rootResolvesPair_of_collisionFree facts S Sched x hexec r n' hn' v₁ hw₁ v₂ hw₂
    C₁ C₂ D₁ D₂ hC₁ hD₁ ?_ hC₂ hD₂ ?_ ?_
  · rw [hroot₁, ← hD₁e, Proofs.NamedWire.erase_root]
  · rw [hroot₂, ← hD₂e, Proofs.NamedWire.erase_root]
  · rw [hD₁e, hD₂e]; exact hpair

end

end DecoupledConsensusModel.Sts.Restated
