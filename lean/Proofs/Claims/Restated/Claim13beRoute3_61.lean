import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bStepConeIter
import Proofs.Claims.Restated.Claim13beRoute3_45
import Proofs.Claims.Restated.Claim13beRoute3_45b
import Proofs.Claims.Restated.Claim13beRoute3_46
import Proofs.Claims.Restated.Claim13beRoute3_47b
import Proofs.Claims.Restated.Claim13beRoute3_48
import Proofs.Claims.Restated.Claim13beRoute3_50
import Proofs.Claims.Restated.Claim13beRoute3_52
import Proofs.Claims.Restated.Claim13beRoute3_53b
import Proofs.Claims.Restated.Claim13beRoute3_54b
import Proofs.Claims.Restated.Claim13beRoute3_56b
import Proofs.Claims.Restated.Claim13beRoute3_58
import Proofs.Claims.Restated.Claim13beRoute3_59
import Proofs.Claims.Restated.Claim13beRoute3_60
import Proofs.Claims.Restated.Vocabulary_Execution_OutageInputs
import Proofs.Claims.Restated.Vocabulary_Execution_PreparedReadBridge
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_SGRepresentation
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_Interpolation
import Proofs.Vocabulary.Protocol.Grades.RelativeSupporter
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_RowTrace
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_TickBridges
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_42c
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.RunVocabulary
import Model.Conditions.Vocabulary_Internal_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_Definitions_NamedLifecycle
import Model.Conditions.Vocabulary_Internal_Definitions_NamedOutageEntry
import Model.Conditions.Vocabulary_Internal_Definitions_NamedResult23Statements
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGradeQueries
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGrades
import Model.Conditions.Vocabulary_Internal_Definitions_TickReads
import Model.Conditions.Vocabulary_Internal_HealingSurface
import Model.Conditions.Vocabulary_Internal_Internal_GradeReads
import Model.Conditions.Vocabulary_Internal_Invariants
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedConfirmationWalk
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedHeadReads
import Proofs.Vocabulary.Internal.Legacy.Definitions.NamedVoteConsumers
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedActionReads
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_MajoritySG_ForkChoice
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_ModelVocabulary_Healing_Schedule
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Adoption
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Agreement
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_SeedCeiling
import Model.Conditions.Vocabulary_Protocol_Grades_GoldfishConePersistence
import Model.Conditions.Vocabulary_Protocol_Grades_Main
import Model.Conditions.Vocabulary_Protocol_Grades_ProposalLifecycleCore
import Model.Conditions.Vocabulary_Protocol_Grades_RelativeCrossReader
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_Handlers_TickBridges
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring

/-!
# Anchors, relay steps and round-ceiling persistence along a path

Theorems over a model `M : Record.Model V` and its facts `facts : Record.Facts M`, with every store
read in a world of the bundle's path `W`: grade 1 of a selected Q2, the next-round regime from a
window, the voter and confirmation anchors after the previous round's action blocks, the relay steps
of the vote cone, and the persistence of an opening confirmation through a round ceiling.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

/-! ### Helpers -/

section
set_option autoImplicit false
open scoped DC
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Proofs.HealingSurface

/-- In a run sorted by key, the worlds strictly before the instant `t` are the worlds before the
    event of index `strictEventIndex rho t`. -/
private theorem stateBeforeTime_eq_strict₆₁ (S : Setup V) (rho : Record.Run V)
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f)) (t : Time) :
    Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t =
      Record.stateBeforeOf M S rho (strictEventIndex rho t) := by
  have hpre : rho.events.filter (fun e => decide (e.time < t)) =
      rho.events.take (rho.events.filter (fun e => decide (e.time < t))).length := by
    refine List.prefix_iff_eq_take.mp ?_
    rw [DecoupledConsensusModel.Proofs.Bridges.filter_eq_takeWhile_of_pairwise
      (R := fun e f => Record.Event.key e ≤ Record.Event.key f) ?_ _ hsorted]
    · exact List.takeWhile_prefix _
    · intro e f hk hf
      simp only [decide_eq_true_eq] at hf ⊢
      exact lt_of_le_of_lt (Restated.time_le_of_key_le hk) hf
  show (rho.events.filter (fun e => decide (e.time < t))).foldlM (Record.worldStepOf M S)
      (fun v => M.initial S v) =
    (rho.events.take (rho.events.filter (fun e => decide (e.time < t))).length).foldlM
      (Record.worldStepOf M S) (fun v => M.initial S v)
  rw [← hpre]

/-- In a run sorted by key, the world of a path `W` before the event of index
    `strictEventIndex rho t` is a world strictly before `t`. -/
private theorem mem_stateBeforeTime_along₆₁ {S : Setup V} {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (t : Time) :
    W (strictEventIndex rho t) ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t := by
  rw [stateBeforeTime_eq_strict₆₁ S rho hsorted]
  exact (hW _).1

/-- For every path `W` of `rho`, `W (m + k)` is among the worlds the events `m` to `m + k - 1` of
    `rho` lead to from `W m`. -/
private theorem onePath_reach₆₁ {S : Setup V} {rho : Record.Run V}
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (m : Nat) :
    ∀ k : Nat, W (m + k) ∈ ((rho.events.drop m).take k).foldlM (Record.worldStepOf M S) (W m) := by
  intro k
  induction k with
  | zero => exact Set.mem_singleton _
  | succ k ih =>
    have hstep := (hW (m + k)).2
    rw [Nat.add_sub_cancel_left] at hstep
    rw [List.take_add, List.foldlM_append, Set.bind_def, List.drop_drop]
    refine Set.mem_iUnion₂.mpr ⟨W (m + k), ih, ?_⟩
    rw [← Nat.add_assoc]
    exact hstep

/-- For every path `W` of `rho` and `m ≤ n`, `W n` is among the worlds the events `m` to `n - 1` of
    `rho` lead to from `W m`. -/
private theorem onePath_slice₆₁ {S : Setup V} {rho : Record.Run V}
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) {m n : Nat}
    (hmn : m ≤ n) :
    W n ∈ ((rho.events.drop m).take (n - m)).foldlM (Record.worldStepOf M S) (W m) := by
  have h := onePath_reach₆₁ W hW m (n - m)
  rwa [Nat.add_sub_of_le hmn] at h

/-- Along a path `W` of a run, for `j ≤ n`, the finalized block of `v`'s core store in `W j` is an
    ancestor of the one in `W n`. -/
private theorem F_mono_along₆₁ (facts : Record.Facts M) (S : Setup V) {rho : Record.Run V}
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (v : V)
    {j n : Nat} (hjn : j ≤ n) : Block.Preceq (W j v).st.core.F (W n v).st.core.F :=
  Restated.Vocabulary.Protocol.stateBefore_F_mono facts S rho v hjn (W j) (hW j).1 (W n)
    (onePath_slice₆₁ W hW hjn)

/-- The round-`r` action read from `before` has a node state `n` on which the grade-2 block read can
    return some `g` and the SG vote selector on `g` some block `B`. -/
private theorem exists_actionSG₆₁ (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∃ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      ∃ g, M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ g ∧
        ∃ B, M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc (M.toHealing n.st.core).s) g ⇢ B := by
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc before.st.core.toHealing
    (Restated.Vocabulary.Execution.Setup.a M S r) before.cache
  obtain ⟨st, hst⟩ := facts.dt.duties_update_confirmation_with_nonempty (M.gradeContract c) S.E
    S.hc (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r))
    (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1)
  refine ⟨M.mkNode st before.record c, ⟨c, hc, st, hst, rfl⟩, ?_⟩
  obtain ⟨g, hg⟩ := facts.dt.grade2_block_with_nonempty
    (M.gradeContract (M.mkNode st before.record c).cache) S.E S.hc
    (M.toHealing (M.mkNode st before.record c).st.core)
    (M.round_of S.hc (M.toHealing (M.mkNode st before.record c).st.core).s)
  obtain ⟨B, hB⟩ := facts.dt.get_sg_vote_with_nonempty
    (M.gradeContract (M.mkNode st before.record c).cache) S.E S.hc
    (M.toHealing (M.mkNode st before.record c).st.core)
    (M.round_of S.hc (M.toHealing (M.mkNode st before.record c).st.core).s) g
  exact ⟨g, hg, B, hB⟩

/-- Every node state of the round-`r` action read computed from `before` holds the bodies `before`
    holds. -/
private theorem actionReadFrom_bodies₆₁ (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ nr ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      nr.st.bodies = before.st.bodies := by
  rintro _ ⟨c, -, st, hst, rfl⟩
  rw [facts.nd.mkNode_st, facts.nd.store_with_cache_bodies,
    facts.dt.named_update_confirmation_with_bodies _ _ _ _ _ st hst,
    facts.hd.ModelProperties_setClock_bodies]

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Statements.Instantiation

/-- Under the bundle with path `W` and the weight bound, if `lo ≤ S.a q`, the cutoff `Γ_neg1` of
    round `q + 1` and round `q + 1`'s grade-1 domain instant are in the horizon, every action block
    of round `q` along `W` of every member of the set for `S.a q` is an ancestor of `C`, `w` is in
    the set for round `q + 1`'s grade-1 domain instant with its finalized block there an ancestor of
    `C`, every member of the set for `S.a q + Δ` is awake at `q`, and every outcome of the grade-1
    store grade of `A` at `w`'s store there is `true`, then `A` is an ancestor of `C`. -/
private theorem preceq_of_relativeG1_previousCarriers₆₁ (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hfb : BelowOneThirdOn S rho Hs)
    {q : Round}
    (hpost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S q))
    (hcut : Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (q + 1) ≤ rho.horizon)
    (hdomainHor : M.domain S.E S.hc (q + 1) .g1 ≤ rho.horizon)
    {C : Block V}
    (hupper : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)),
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v) q,
      ∀ g, M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ g →
      ∀ B, M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc (M.toHealing n.st.core).s) g ⇢ B →
        Block.Preceq B C)
    {w : V} (hw : w ∈ Hs (M.domain S.E S.hc (q + 1) .g1))
    (hFC : Block.Preceq
      (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g1)) w).st.core.F C)
    (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S q)) → M.awake_for_grade2 S u (W j u) q)
    {A : Block V}
    (hgA : ∀ b, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
      (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g1)) w).st (q + 1) .g1 A ⇢ b →
        b = true) :
    Block.Preceq A C := by
  have hW := hf.onePath
  obtain ⟨gA, hgA'⟩ := facts.gr.gradeBool_nonempty S.E
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g1)) w).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g1)) w).st.core.F
    S.hc.η_SG (q + 1) (M.early S.E S.hc (q + 1) .g1) (M.late S.E S.hc (q + 1) .g1) A
  have hgAtrue : gA = true := hgA gA hgA'
  have hlatest : q ∈ M.latest_window S.hc.η_SG (q + 1) := by
    simpa only [Nat.add_sub_cancel] using
      facts.fc.pred_mem_latest_window S.hc.η_SG (q + 1) S.hc.η_SG_ge_one (Nat.succ_pos q)
  have hactionDeadline : (Restated.Vocabulary.Execution.Setup.a M S q) + S.E.Δ ≤
      M.early S.E S.hc (q + 1) .g1 :=
    (facts.gr.action_delta_le_early S S.hc.R_ge_three (Nat.lt_succ_self q)).trans
      (facts.gr.q10_early_g2_le_early_g1 S (q + 1))
  have hactionHor : (Restated.Vocabulary.Execution.Setup.a M S q) ≤ rho.horizon :=
    (le_add_of_nonneg_right S.E.Δ_pos.le).trans
      ((facts.gr.action_add_delta_le_next_Γ_neg1 S q).trans hcut)
  have hearlyHor : M.early S.E S.hc (q + 1) .g1 ≤ rho.horizon :=
    (facts.gr.q10_early_g1_le_domain_g2 S (q + 1)).trans
      (by rw [← facts.gr.gammaNeg1_eq_domain_g2_succ S q]; exact hcut)
  have hearlyDomain : M.early S.E S.hc (q + 1) .g1 ≤ M.domain S.E S.hc (q + 1) .g1 :=
    (facts.gr.q10_early_g1_le_domain_g2 S (q + 1)).trans
      (facts.gr.q10_domain_g2_lt_domain_g1 S (q + 1)).le
  have hwE : w ∈ Hs (M.early S.E S.hc (q + 1) .g1) := hHs _ _ hearlyDomain hw
  have hmemE : ∀ v ∈ Hs (M.domain S.E S.hc (q + 1) .g1), v ∈ Hs (M.early S.E S.hc (q + 1) .g1) :=
    fun v hv => hHs _ _ hearlyDomain hv
  have hmemAD : ∀ v ∈ Hs (M.domain S.E S.hc (q + 1) .g1),
      v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q) + S.E.Δ) :=
    fun v hv => hHs _ _ (hactionDeadline.trans hearlyDomain) hv
  have hmemA : ∀ v ∈ Hs (M.domain S.E S.hc (q + 1) .g1),
      v ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S q) :=
    fun v hv => hHs _ _ (le_add_of_nonneg_right S.E.Δ_pos.le) (hmemAD v hv)
  have hvoteIn : ∀ v ∈ Hs (M.domain S.E S.hc (q + 1) .g1),
      ∃ (a : NamedAttestation V) (B : Block V) (Bn : NamedBlock V),
        a.val_index = v ∧ a.round = q ∧
        Restated.Vocabulary.Execution.NamedRun.emits M S rho W v (Object.attest a)
          (Restated.Vocabulary.Execution.Setup.a M S q) ∧
        a.confirmed = some B.root ∧ Bn.erase = B ∧ Restated.RunBlockOn M S rho W Xb Bn ∧
        Block.Preceq B C ∧
        ∀ Y, M.interpretedInputs
          (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g1)) w).st.core))
          (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g1)) w).st.core.F
          S.hc.η_SG (q + 1) (M.early S.E S.hc (q + 1) .g1) v ⇢ Y → M.sgVote a.erase ∈ Y := by
    intro v hv
    have hvA := hmemA v hv
    obtain ⟨nv, hnv, g, hg, B, hB⟩ := exists_actionSG₆₁ facts S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v) q
    obtain ⟨D, hD⟩ := facts.dt.attest_with_nonempty (M.gradeContract nv.cache) S.E S.hc (S.node v)
      nv.st nv.record
    have hem := Restated.honest_emits_actionAttestationAtOn facts S Hs Xb hf q hvA hactionHor hpost
      (hA v (hmemAD v hv)) (fun j hj => hf.tick_outcome j _ _ hj) nv hnv D hD
    have hsg := hem.2 g hg B hB
    have haval : D.2.2.val_index = v := by
      have h := congrArg Protocol.SGVote.val_index hsg
      rw [facts.sto.sgVote_val_index_eq_val_index, namedAttestation_erase_val_index] at h
      exact h
    have haround : D.2.2.round = q := by
      have h := congrArg Protocol.SGVote.round hsg
      rw [facts.sto.sgVote_round_eq_round, namedAttestation_erase_round] at h
      exact h
    have haconf : D.2.2.confirmed = some B.root := by
      have h := congrArg Protocol.SGVote.confirmed hsg
      rw [facts.sto.sgVote_confirmed_eq, namedAttestation_erase_confirmed] at h
      exact h
    obtain ⟨i, hi, -, -, -, -, hall⟩ :=
      Restated.Vocabulary.Proofs.NamedOutageInputs.emitted_attestation_head facts S rho W hW hem.1
    obtain ⟨ni, hni, -⟩ := exists_actionSG₆₁ facts S (W i v) D.2.2.round
    obtain ⟨H, hH, hHconf⟩ := hall ni hni
    have hHbody : H ∈ (W i v).st.bodies := by
      rw [← actionReadFrom_bodies₆₁ facts S _ _ ni hni]
      exact hH
    have hHrun : Restated.RunBlockOn M S rho W Xb H :=
      Restated.runBlock_of_stateBefore_memOn facts S W Xb (hHsXb _ hv) hHbody
    have hBmem : B ∈ (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v).st.core.T :=
      Restated.Vocabulary.Proofs.HealingSurface.actionSGBlockAt_mem_storeBeforeTime facts S rho v q _
        (mem_stateBeforeTime_along₆₁ hf.sorted hW _) nv hnv g hg B hB
    obtain ⟨Bn, hBnerase, hBnrun⟩ := Restated.runBlock_of_mem_core_T_stateBeforeTimeOn facts S Hs Xb
      hf (hHsXb _ hv) (Restated.Vocabulary.Execution.Setup.a M S q) hBmem
    have hrootEq : H.erase.root = Bn.erase.root := by
      rw [Proofs.NamedWire.erase_root, hBnerase]
      exact Option.some.inj (hHconf.symm.trans haconf)
    have hHB : H.erase = Bn.erase :=
      Restated.runBlock_eq_of_root_eqOn facts W Xb hf.rootCollisionFree hHrun hBnrun hrootEq
    have hBC : Block.Preceq B C := hupper v hvA nv hnv g hg B hB
    have hHC : Block.Preceq H.erase C := by
      rw [hHB, hBnerase]
      exact hBC
    have hmem := Restated.action_vote_mem_interpretedInputs_after_gst_common_upperOn facts
      S Hs Xb hf hHs hHsXb .g1 hlatest (hmemE v hv) hwE
      ⟨haval, haround, hem.1⟩ ⟨i, hi, ⟨ni, hni, hH⟩, hHconf⟩ hHC hFC
      (by rw [haround]; exact hpost)
      (by rw [haround, max_eq_left hpost]; exact hactionDeadline)
      hearlyDomain hearlyHor
    exact ⟨D.2.2, B, Bn, haval, haround, hem.1, haconf, hBnerase, hBnrun, hBC, hmem⟩
  have hwin : ∀ ins : V → Finset (Protocol.SGVote V),
      (∀ v, M.interpretedInputs
        (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g1)) w).st.core))
        (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g1)) w).st.core.F
        S.hc.η_SG (q + 1) (M.early S.E S.hc (q + 1) .g1) v ⇢ ins v) →
      S.E.electorate.weightOf (Finset.univ \ Hs (M.domain S.E S.hc (q + 1) .g1)) <
        S.E.electorate.weightOf ((Hs (M.domain S.E S.hc (q + 1) .g1)).filter
          fun v => (ins v).Nonempty) := by
    intro ins hins
    have hsubset : Hs (M.domain S.E S.hc (q + 1) .g1) ⊆
        (Hs (M.domain S.E S.hc (q + 1) .g1)).filter fun v => (ins v).Nonempty := by
      intro v hv
      obtain ⟨a, -, -, -, -, -, -, -, -, -, hmem⟩ := hvoteIn v hv
      exact Finset.mem_filter.2 ⟨hv, ⟨_, hmem _ (hins v)⟩⟩
    exact lt_of_lt_of_le
      (by simpa only [HonestWeightMajority] using
        honestWeightMajorityOn_of_belowOneThirdOn hfb _ hdomainHor)
      (S.E.electorate.weightOf_mono hsubset)
  obtain ⟨v, hv, I, hI, u, hu, head, hconf, hfind, -, hAhead, -, hmax⟩ :=
    facts.gr.exists_honest_max_positive_supporter_of_relativeGrade S.E S.hc hwin gA hgA' hgAtrue
  obtain ⟨a, B, Bn, haval, haround, hemit, haconf, hBnerase, hBnrun, hBC, hmem⟩ := hvoteIn v hv
  have hqle : q ≤ u.round := by
    have h := hmax (M.sgVote a.erase) (hmem I hI)
    rw [facts.sto.sgVote_round_eq_round, namedAttestation_erase_round, haround] at h
    exact h
  obtain ⟨R, hR⟩ := facts.gr.rawInputs_nonempty
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g1)) w).st.core))
    S.hc.η_SG (q + 1) (M.early S.E S.hc (q + 1) .g1) v
  obtain ⟨bu, hbu⟩ := facts.gr.bodyReady_nonempty
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g1)) w).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g1)) w).st.core.F
    (M.early S.E S.hc (q + 1) .g1) u
  have huraw := ((facts.gr.mem_interpretedInputs_iff I hI R hR bu hbu).mp hu).1
  obtain ⟨b, -, hbround, hbproj, huwindow, -, hbemit⟩ :=
    Restated.rawInputs_traceOn facts S rho Hs Xb hf hHs (M.domain S.E S.hc (q + 1) .g1)
      (M.early S.E S.hc (q + 1) .g1) w S.hc.η_SG (q + 1) v hv R hR huraw
  have hule : u.round ≤ q := Nat.le_of_lt_succ (facts.fc.window_bounds huwindow).2
  have huroundEq : u.round = q := Nat.le_antisymm hule hqle
  have hba : b = a := Restated.emits_attest_uniqueOn facts S Hs Xb hf hbemit hemit
    ((hbround.trans huroundEq).trans haround.symm)
  have huEq : u = M.sgVote a.erase := by
    rw [← hbproj, hba]
  have hheadRoot : head.root = B.root := by
    have huconf := congrArg Protocol.SGVote.confirmed huEq
    rw [facts.sto.sgVote_confirmed_eq, namedAttestation_erase_confirmed, hconf, haconf] at huconf
    exact Option.some.inj huconf
  have hheadMem : head ∈ (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g1)) w).st.core.T := by
    have h := Proofs.HealingLemmas.find?_mem hfind
    rw [facts.gr.Sts_gradeView_T] at h
    exact h
  obtain ⟨Headn, hHeaderase, hHeadrun⟩ := Restated.runBlock_of_mem_core_T_stateBeforeTimeOn facts
    S Hs Xb hf (hHsXb _ hw) (M.domain S.E S.hc (q + 1) .g1) hheadMem
  have hheadBnRoot : Headn.erase.root = Bn.erase.root := by
    rw [hHeaderase, hBnerase]
    exact hheadRoot
  have hheadB : head = B := by
    rw [← hHeaderase, ← hBnerase]
    exact Restated.runBlock_eq_of_root_eqOn facts W Xb hf.rootCollisionFree hHeadrun hBnrun hheadBnRoot
  rw [hheadB] at hAhead
  exact preceq_trans_Preceq hAhead hBC

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- Under the bundle with path `W`, if round `r`'s grade cutoffs are ready, `p` is in the set for
    `domain r g2`, `w` in the set for `domain r g1`, `n` is a node state of `p`'s round-`r` action
    read along `W` whose Q2 can return `some Q`, the cross-reader body condition holds for `p`, `w`,
    `Q`, and `lo ≤ opening (r − η_SG)`, then every outcome of the grade-1 store grade of `Q` at
    `w`'s store in `W (strictEventIndex rho (domain r g1))` is `true`. -/
theorem selectedG2_G1_at_read_after_cutoffOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {r : Round} (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho r)
    (_hhor : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ rho.horizon)
    {p w : V} (hp : p ∈ Hs (M.domain S.E S.hc r .g2)) (hw : w ∈ Hs (M.domain S.E S.hc r .g1))
    {Q : Block V} (n : M.N)
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) p) r)
    (hQ : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ some Q)
    (hguard : Restated.Vocabulary.Proofs.HealingSurface.CrossReaderBodyReadyGuard M S rho r p w
      (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) p)
      (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w) Q)
    (hlo : lo ≤ M.opening S.E S.hc (r - S.hc.η_SG)) :
    ∀ b, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
      (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st r .g1 Q ⇢ b → b = true := by
  have hG2 := Restated.selectedQ2_storeGrade_at_g2DomainOn facts S Hs Xb hf n hn hQ
  obtain ⟨b2, hb2⟩ := facts.gr.gradeBool_nonempty S.E
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) p).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) p).st.core.F
    S.hc.η_SG r (M.early S.E S.hc r .g2) (M.late S.E S.hc r .g2) Q
  have hb2t : b2 = true := hG2 b2 hb2
  subst hb2t
  exact Restated.storeGrade_g1_of_storeGrade_g2_cross_readerOn facts
    S rho Hs Xb hf hHs hHsXb r hlo ready.2 p w hp hw Q hb2 hguard

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Proofs.Optimistic
local macro "scs% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedCeilingStep)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- For any worlds `Wt` before each instant, if `S.E.t_GST ≤ S.a q`, the confirmation instant of the
    slot before round `q + 1`'s last slot is in the horizon, and at every read instant from `S.a q`
    to that confirmation instant the store in `Wt read` of every member of the set for that instant
    has `h_j + 2 ≤ Mh` and `h_max = Mh`, then the next-round regime read from `Wt` holds for `Mh`
    and `q`. -/
theorem roundCeilingNextRegime_of_windowOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} {Wt : Time → V → M.N} (Hs : Int → Finset V)
    {Mh : Height} {q : Round}
    (hpostAction : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S q))
    (hhor : M.confirmation_time S.E
      (Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S (q + 1) - 1) ≤ rho.horizon)
    (hwindow : ∀ read : Time, (Restated.Vocabulary.Execution.Setup.a M S q) ≤ read →
      read ≤ M.confirmation_time S.E
        (Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S (q + 1) - 1) →
      ∀ w ∈ Hs read, (Wt read w).st.h_j + 2 ≤ Mh ∧ (Wt read w).st.h_max = Mh) :
    Restated.RoundCeilingNextRegimeAtOn M S rho Wt Hs Mh q := by
  have hoPos : 0 < (M.opening_slot S.hc (q + 1)) := facts.gr.openingSlot_pos_l58 S (Nat.succ_pos q)
  have hlastPos : 0 < Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S (q + 1) :=
    Nat.zero_lt_of_lt (Restated.openingSlot_lt_seedRoundLastSlot_l58 facts S (q + 1))
  have hlastPredSucc : Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S (q + 1) - 1 + 1 =
      Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S (q + 1) :=
    Nat.sub_add_cancel (Nat.succ_le_iff.mpr hlastPos)
  have hopenLastPred : (M.opening_slot S.hc (q + 1)) ≤
      Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S (q + 1) - 1 :=
    Restated.openingSlot_le_seedRoundLastSlot_pred_l58 facts S (q + 1)
  have hprevOpen : (M.opening_slot S.hc q) + 2 ≤
      (M.opening_slot S.hc (q + 1)) := by
    rw [facts.gr.opening_slot_succ]
    exact Nat.add_le_add_left S.hc.R_ge_two ((M.opening_slot S.hc q))
  have hactionProposal : (Restated.Vocabulary.Execution.Setup.a M S q) ≤
      M.proposal_time S.E ((M.opening_slot S.hc (q + 1))) := by
    rw [← Restated.confirmation_time_opening_slot facts S q]
    exact le_of_lt
      (facts.sch.confirmationTime_lt_proposalTime_of_two_le S.E hprevOpen)
  have hproposalVote :
      M.proposal_time S.E ((M.opening_slot S.hc (q + 1))) ≤
        M.vote_time S.E ((M.opening_slot S.hc (q + 1))) :=
    le_of_lt (facts.sch.proposal_time_lt_vote_time S.E _)
  have hlastVoteConf : M.vote_time S.E
      (Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S (q + 1)) ≤
        M.confirmation_time S.E
          (Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S (q + 1) - 1) := by
    have h := facts.sch.vote_time_succ_add_delta_le_confirmation_time S.E
      (Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S (q + 1) - 1)
    rw [hlastPredSucc] at h
    exact (le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans h
  have hboundaryLow :
      M.proposal_time S.E ((M.opening_slot S.hc (q + 1))) <
        M.confirmation_time S.E
          ((M.opening_slot S.hc (q + 1)) - 1) := by
    have hpred : (M.opening_slot S.hc (q + 1)) - 1 + 1 =
        (M.opening_slot S.hc (q + 1)) :=
      Nat.sub_add_cancel (Nat.succ_le_iff.mpr hoPos)
    simpa only [hpred] using
      facts.sch.proposal_time_succ_lt_confirmation_time S.E
        ((M.opening_slot S.hc (q + 1)) - 1)
  have hlowConf : M.confirmation_time S.E
      ((M.opening_slot S.hc (q + 1)) - 1) ≤
        M.confirmation_time S.E
          (Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S (q + 1) - 1) :=
    Restated.confirmationTime_mono_l58 facts S.E
      ((Nat.sub_le _ 1).trans hopenLastPred)
  have hvoteRead : ∀ d : Slot, (M.opening_slot S.hc (q + 1)) ≤ d →
      d ≤ Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S (q + 1) → ∀ w ∈ Hs (M.vote_time S.E d),
        (Wt (M.vote_time S.E d) w).st.h_j + 2 ≤ Mh ∧ (Wt (M.vote_time S.E d) w).st.h_max = Mh := by
    intro d hdlo hdhi w hw
    refine hwindow _ ?_ ?_ w hw
    · exact hactionProposal.trans
        (hproposalVote.trans (facts.sch.vote_time_mono_slots S.E hdlo))
    · exact (facts.sch.vote_time_mono_slots S.E hdhi).trans hlastVoteConf
  have hconfRead : ∀ s : Slot,
      (M.opening_slot S.hc (q + 1)) - 1 ≤ s →
      s ≤ Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S (q + 1) - 1 → ∀ w ∈ Hs (M.confirmation_time S.E s),
        (Wt (M.confirmation_time S.E s) w).st.h_j + 2 ≤ Mh ∧
          (Wt (M.confirmation_time S.E s) w).st.h_max = Mh := by
    intro s hslo hshi w hw
    refine hwindow _ ?_ ?_ w hw
    · exact hactionProposal.trans
        ((le_of_lt hboundaryLow).trans
          (Restated.confirmationTime_mono_l58 facts S.E hslo))
    · exact Restated.confirmationTime_mono_l58 facts S.E hshi
  have hproposalRead : ∀ w ∈ Hs (M.proposal_time S.E ((M.opening_slot S.hc (q + 1)))),
        (Wt (M.proposal_time S.E ((M.opening_slot S.hc (q + 1)))) w).st.h_j + 2 ≤ Mh ∧
          (Wt (M.proposal_time S.E ((M.opening_slot S.hc (q + 1)))) w).st.h_max = Mh := by
    intro w hw
    exact hwindow _ hactionProposal
      ((le_of_lt hboundaryLow).trans hlowConf) w hw
  have haEq : (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) = M.confirmation_time S.E ((M.opening_slot S.hc (q + 1))) :=
    Restated.a_eq_confirmation_opening_l58 facts S (q + 1)
  have hactionRead : ∀ w ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q + 1))),
        (Wt (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) w).st.h_j + 2 ≤ Mh ∧
          (Wt (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) w).st.h_max = Mh := by
    intro w hw
    rw [haEq] at hw ⊢
    exact hconfRead ((M.opening_slot S.hc (q + 1)))
      (Nat.sub_le _ 1) hopenLastPred w hw
  have hstaged : ∀ (ns : M.NS) (t : Time),
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S ns.core t).h_max = ns.h_max ∧
        (Restated.Vocabulary.Proofs.Optimistic.tickStore M S ns.core t).h_j = ns.h_j := by
    intro ns t
    have hcore : Restated.Vocabulary.Proofs.Optimistic.tickStore M S ns.core t =
        (M.ns_setClock S.E ns t).core :=
      (facts.hd.setClock_core_eq_store_with_t_s S.E ns t).symm
    rw [hcore]
    refine ⟨facts.hd.setClock_core_h_max S.E ns t, ?_⟩
    rw [← facts.sto.toHealing_h_j, facts.hd.setClock_toHealing_h_j]
    rfl
  exact
    { postOpeningProposal := hpostAction.trans hactionProposal
      roundConfirmationInHorizon := hhor
      window :=
        { voteFrontier := by
            intro d hdlo hdhi w hw
            show (Restated.Vocabulary.Proofs.Optimistic.tickStore M S (Wt (M.vote_time S.E d) w).st.core
              (M.vote_time S.E d)).h_max = Mh
            rw [(hstaged _ _).1]
            exact (hvoteRead d hdlo (by rw [← hlastPredSucc]; exact hdhi) w hw).2
          voteGateOff := by
            intro d hdlo hdhi w hw
            show (Restated.Vocabulary.Proofs.Optimistic.tickStore M S (Wt (M.vote_time S.E d) w).st.core
              (M.vote_time S.E d)).h_j + 2 ≤ Mh
            rw [(hstaged _ _).2]
            exact (hvoteRead d hdlo (by rw [← hlastPredSucc]; exact hdhi) w hw).1
          confirmationFrontier := by
            intro s hslo hshi w hw
            rw [(hstaged _ _).1]
            exact (hconfRead s ((Nat.sub_le _ 1).trans hslo) hshi w hw).2
          confirmationGateOff := by
            intro s hslo hshi w hw
            rw [(hstaged _ _).2]
            exact (hconfRead s ((Nat.sub_le _ 1).trans hslo) hshi w hw).1 }
      boundaryConfirmationFrontier := by
        intro w hw
        rw [(hstaged _ _).1]
        exact (hconfRead ((M.opening_slot S.hc (q + 1)) - 1) (le_refl _)
            ((Nat.sub_le _ 1).trans hopenLastPred) w hw).2
      boundaryConfirmationGateOff := by
        intro w hw
        rw [(hstaged _ _).2]
        exact (hconfRead ((M.opening_slot S.hc (q + 1)) - 1) (le_refl _)
            ((Nat.sub_le _ 1).trans hopenLastPred) w hw).1
      actionFrontier := by
        intro w hw
        show (M.toHealing (Wt (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) w).st.core).toFG.h_max = Mh
        rw [facts.sto.Sts_toHealing_h_max]
        exact (hactionRead w hw).2
      actionGateOff := by
        intro w hw
        show (M.toHealing (Wt (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) w).st.core).toFG.h_j + 2
          ≤ Mh
        rw [facts.sto.toHealing_h_j]
        exact (hactionRead w hw).1
      proposalFrontier := fun w hw => (hproposalRead w hw).2
      proposalGateOff := fun w hw => (hproposalRead w hw).1 }

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Proofs.Optimistic
local macro "scs% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedCeilingStep)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Under the bundle with path `W` and the weight bound, if slot `s + 1` is in round `q + 1`,
    `lo ≤ S.a q`, round `q + 1`'s earliest grade cutoff and `vote_time (s + 1)` are in the horizon,
    every action block of round `q` along `W` of every member of the set for `S.a q` is an ancestor
    of `C`, `w` is in the set for `vote_time (s + 1)` with the finality root of its vote-duty store
    there an ancestor of `C`, every member of the set for `S.a q + Δ` is awake at `q`, and `c` is an
    outcome of `w`'s cache update there, then every anchor the vote read staged with `c` can give at
    the round of its slot is an ancestor of `C`. -/
theorem voterAnchorAt_preceq_of_previousCarriersOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hfb : BelowOneThirdOn S rho Hs)
    {q : Round} {s : Slot} (hround : (M.round_of S.hc (s + 1)) = q + 1)
    (hpost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S q))
    (hcut : Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (q + 1) ≤ rho.horizon)
    (hvoteHor : M.vote_time S.E (s + 1) ≤ rho.horizon)
    {C : Block V}
    (hupper : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)),
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v) q,
      ∀ g, M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ g →
      ∀ B, M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc (M.toHealing n.st.core).s) g ⇢ B →
        Block.Preceq B C)
    {w : V} (hw : w ∈ Hs (M.vote_time S.E (s + 1)))
    (hroot : Block.Preceq
      (M.get_fg_root
        (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1))).toFG) C)
    (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S q)) → M.awake_for_grade2 S u (W j u) q)
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.toHealing (M.vote_time S.E (s + 1))
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache ⇢ c) :
    ∀ A0 : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S
      (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
        (M.vote_time S.E (s + 1))) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c)
      (M.round_of S.hc (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
        (M.vote_time S.E (s + 1))) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c).st.core.s)
        ⇢ A0 →
    Block.Preceq A0 C := by
  intro A0 hA0
  have hW := hf.onePath
  set t := M.vote_time S.E (s + 1) with ht
  set wv := W (strictEventIndex rho t) w with hwv
  set n := M.mkNode (M.ns_setClock S.E wv.st t) wv.record c with hn
  have hcore : n.st = M.store_with_cache (M.ns_setClock S.E wv.st t) c := by
    rw [hn, facts.nd.mkNode_st]
  have hnmem : n ∈ Restated.Vocabulary.Internal.NamedRecoveryRead.voteDutyRead M S rho w (s + 1) :=
    ⟨W (strictEventIndex rho t), mem_stateBeforeTime_along₆₁ hf.sorted hW t, c, hc, rfl⟩
  have hvoteStore : Restated.Vocabulary.Proofs.Optimistic.voteStore M S wv.st.core (s + 1) =
      (M.ns_setClock S.E wv.st t).core :=
    (facts.hd.setClock_core_eq_store_with_t_s S.E wv.st t).symm
  rw [hvoteStore] at hroot
  rcases Restated.Vocabulary.Proofs.HealingSurface.voterAnchorAt_cases facts S rho w (s + 1) n hnmem
      A0 hA0 with hfg | ⟨root, A, hframe, hactive, hAA0⟩
  · rw [hfg, hcore]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    exact hroot
  · rw [hAA0]
    have hr : 0 < q + 1 := Nat.succ_pos q
    have hslo : (M.opening_slot S.hc (q + 1)) ≤ s + 1 := by
      rw [← hround]
      exact facts.gr.opening_slot_round_of_le_slot S.hc (s + 1)
    have hshi : s + 1 < (M.opening_slot S.hc ((q + 1) + 1)) := by
      rw [← hround]
      exact facts.gr.lt_opening_slot_round_of_succ S.hc (s + 1)
    have hnext : t ≤ M.opening S.E S.hc ((q + 1) + 1) := by
      rw [facts.gr.opening_eq_proposal_time]
      exact (facts.sch.voteTime_lt_nextProposal_l86d S.E (s + 1)).le.trans
        (facts.sch.proposal_time_mono S.E (Nat.succ_le_iff.mpr hshi))
    have hroundSt : M.round_of S.hc n.st.core.s = q + 1 := by
      rw [hcore]
      try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
      rw [facts.hd.Sts_setClock_core_s, ht, facts.sch.slotOf_vote_time]
      exact hround
    rw [hroundSt] at hframe
    have hdomainVote : M.domain S.E S.hc (q + 1) .g1 < t := by
      rw [facts.gr.Sts_domain_g1_eq_opening, facts.gr.opening_eq_proposal_time]
      exact (facts.sch.proposal_time_mono S.E hslo).trans_lt
        (facts.sch.proposal_time_lt_vote_time S.E (s + 1))
    have hwX : w ∈ Hs (M.domain S.E S.hc (q + 1) .g1) := hHs _ _ hdomainVote.le hw
    have hdomainHor : M.domain S.E S.hc (q + 1) .g1 ≤ rho.horizon :=
      hdomainVote.le.trans hvoteHor
    have hactionDeadline : (Restated.Vocabulary.Execution.Setup.a M S q) + S.E.Δ ≤
        M.early S.E S.hc (q + 1) .g1 :=
      (facts.gr.action_delta_le_early S S.hc.R_ge_three
        (Nat.lt_succ_self q)).trans
        (facts.gr.q10_early_g2_le_early_g1 S (q + 1))
    have hearlyDomain : M.early S.E S.hc (q + 1) .g1 ≤
        M.domain S.E S.hc (q + 1) .g1 :=
      (facts.gr.q10_early_g1_le_domain_g2 S (q + 1)).trans
        (facts.gr.q10_domain_g2_lt_domain_g1 S (q + 1)).le
    have hgatDomain : lo ≤ M.domain S.E S.hc (q + 1) .g1 :=
      hpost.trans ((le_add_of_nonneg_right S.E.Δ_pos.le).trans
        (hactionDeadline.trans hearlyDomain))
    obtain ⟨_hAtree, hAGrade⟩ := Restated.fixedRoot_activeVoterAnchor_g1_dataOn facts
      S Hs Xb hf hr hslo hround hnext hvoteHor hwX c hc hframe hactive hgatDomain
    have hFmono : Block.Preceq
        (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g1)) w).st.core.F wv.st.core.F :=
      F_mono_along₆₁ facts S hW w
        (Restated.strict_lengths_mono rho hdomainVote.le)
    have hFroot : Block.Preceq wv.st.core.F
        (M.get_fg_root (M.toHealing (M.ns_setClock S.E wv.st t).core).toFG) := by
      have hFJ := Restated.Vocabulary.Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
        facts S rho t w _ (mem_stateBeforeTime_along₆₁ hf.sorted hW t)
      have h := facts.fc.preceq_get_fg_root_of_F (st := (M.toHealing (M.ns_setClock S.E wv.st t).core).toFG)
        (by
          rw [facts.sto.Sts_toHealing_F, facts.sto.Sts_toHealing_J, facts.hd.setClock_core_F,
            facts.hd.setClock_core_J]
          exact preceq_eq_true_iff_Preceq.mpr hFJ)
      rw [facts.sto.Sts_toHealing_F, facts.hd.setClock_core_F] at h
      exact preceq_eq_true_iff_Preceq.mp h
    have hFC : Block.Preceq
        (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g1)) w).st.core.F C :=
      preceq_trans_Preceq hFmono (preceq_trans_Preceq hFroot hroot)
    exact preceq_of_relativeG1_previousCarriers₆₁ facts S Hs Xb hf hHs hHsXb hfb hpost hcut
      hdomainHor hupper hwX hFC hA hAGrade

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Proofs.Optimistic
local macro "scs% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedCeilingStep)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Under the bundle with path `W`, if `0 < r`, the instant `t` is in round `r` after its grade-1
    domain instant and not after `opening (r + 1)`, that domain instant is in the horizon, `w` is in
    the set for `domain r g1` with `lo ≤ domain r g1`, `c` is an outcome of `w`'s cache update at
    `t`, and the node state staged with `c` has grade-1 frame root `root` with active prefix `L`,
    then `L` is in the tree of `w`'s store in `W (strictEventIndex rho (domain r g1))` and every
    outcome of its grade-1 store grade there is `true`. -/
theorem activeConfirmationAnchor_g1_dataOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {r : Round} {t : Time} (hr : 0 < r)
    (hround : (M.round_of S.hc (S.E.slotOf t)) = r)
    (hdomain : M.domain S.E S.hc r .g1 < t)
    (hnext : t ≤ M.opening S.E S.hc (r + 1))
    (hreadHor : M.domain S.E S.hc r .g1 ≤ rho.horizon)
    {w : V} (hw : w ∈ Hs (M.domain S.E S.hc r .g1))
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc (W (strictEventIndex rho t) w).st.core.toHealing t
      (W (strictEventIndex rho t) w).cache ⇢ c)
    {root L : Block V}
    (hframe : (M.readFrame
      (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho t) w).st t)
        (W (strictEventIndex rho t) w).record c).cache
      (M.toHealing (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho t) w).st t)
        (W (strictEventIndex rho t) w).record c).st.core) r).g1 = some (some root))
    (hactive : M.activePrefix
      (M.get_filtered_block_tree
        (M.toHealing (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho t) w).st t)
          (W (strictEventIndex rho t) w).record c).st.core).toFG) root = some L)
    (hgat : lo ≤ M.domain S.E S.hc r .g1) :
    L ∈ (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st.core.T ∧
      ∀ b, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
        (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st r .g1 L ⇢ b → b = true := by
  set wt := W (strictEventIndex rho t) w with hwt
  set w1 := W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w with hw1
  obtain ⟨fr, hfr⟩ := facts.gr.freezeRoot_nonempty S.E (M.gradeView (M.toHealing w1.st.core))
    w1.st.core.F S.hc.η_SG r (M.early S.E S.hc r .g1) (M.late S.E S.hc r .g1)
  have hbase := Restated.frame_phase_completed_in_roundOn facts
    S rho Hs Xb hf w r hr .g1 hw t hdomain hnext hreadHor hgat
    (fun j hj => hf.tick_outcome j _ _ hj) fr hfr
  have hprepared := Restated.Vocabulary.Proofs.NamedOutageClosure.frame_phase_prepared_eq facts
    S rho w r .g1 t hround _ (W (strictEventIndex rho t))
    (mem_stateBeforeTime_along₆₁ hf.sorted hf.onePath _) hbase c hc
  have hreadFrame : (M.readFrame c (M.toHealing (M.ns_setClock S.E wt.st t).core) r).g1 =
      some (fr.map (fun B => M.clipGrade B wt.st.core.F)) := by
    rw [← facts.gr.phaseResult_g1]
    exact hprepared
  rewrite [facts.nd.mkNode_cache, facts.nd.mkNode_st] at hframe; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at hframe
  rewrite [facts.nd.mkNode_st] at hactive; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at hactive
  cases fr with
  | none =>
      rw [hframe] at hreadFrame
      simp at hreadFrame
  | some raw =>
      have hrootEq : root = M.clipGrade raw wt.st.core.F := by
        rw [hframe] at hreadFrame
        simpa using hreadFrame
      have hLroot : Block.Preceq L root := facts.gr.preceq_of_activePrefix_eq_some hactive
      have hLraw : Block.Preceq L raw := by
        rw [hrootEq] at hLroot
        exact preceq_trans_Preceq hLroot (facts.gr.q10_clip_preceq raw wt.st.core.F)
      have hrawTree : raw ∈ w1.st.core.T := by
        have h := facts.gr.mem_T_of_freezeRoot_eq_some (some raw) hfr rfl
        rw [facts.gr.Sts_gradeView_T] at h
        exact h
      have hLtree : L ∈ w1.st.core.T := by
        have hpc := Restated.Vocabulary.Proofs.NamedStoreBridge.parentClosed_stateBeforeTime facts S rho
          (M.domain S.E S.hc r .g1) w _ (mem_stateBeforeTime_along₆₁ hf.sorted hf.onePath _)
        unfold Restated.Vocabulary.Internal.ParentClosed Record.Model.GS.parent_closed at hpc
        have hL := Proofs.Records.mem_of_preceq hpc.2 L raw
          (by rw [facts.sto.toHealing_T]; exact hrawTree)
          (preceq_eq_true_iff_Preceq.mpr hLraw)
        rw [facts.sto.toHealing_T] at hL
        exact hL
      refine ⟨hLtree, ?_⟩
      intro b hb
      obtain ⟨braw, hbraw⟩ := facts.gr.gradeBool_nonempty S.E (M.gradeView (M.toHealing w1.st.core))
        w1.st.core.F S.hc.η_SG r (M.early S.E S.hc r .g1) (M.late S.E S.hc r .g1) raw
      have hrawTrue := facts.gr.gradeBool_of_freezeRoot_eq_some (some raw) hfr rfl braw hbraw
      exact facts.csAdded.confirmation_phaseGrade_mono S.E S.hc _ _ r .g1 hLraw braw hbraw
        hrawTrue b hb

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Proofs.Optimistic
local macro "scs% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedCeilingStep)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Under the bundle with path `W` and the weight bound, if slot `s + 1` is in round `q + 1`,
    `lo ≤ S.a q`, round `q + 1`'s earliest grade cutoff and `confirmation_time s` are in the
    horizon, every action block of round `q` along `W` of every member of the set for `S.a q` is an
    ancestor of `C`, `w` is in the set for `confirmation_time s` with the confirmation root of its
    store staged there an ancestor of `C`, every member of the set for `S.a q + Δ` is awake at `q`,
    and `c` is an outcome of `w`'s cache update there, then every confirmation anchor the read
    staged with `c` can give is an ancestor of `C`. -/
theorem confirmationAnchorAt_preceq_of_previousCarriersOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hfb : BelowOneThirdOn S rho Hs)
    {q : Round} {s : Slot} (hround : (M.round_of S.hc (s + 1)) = q + 1)
    (hpost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S q))
    (hcut : Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (q + 1) ≤ rho.horizon)
    (hconfHor : M.confirmation_time S.E s ≤ rho.horizon)
    {C : Block V}
    (hupper : ∀ v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q)),
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S q)) v) q,
      ∀ g, M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ g →
      ∀ B, M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc (M.toHealing n.st.core).s) g ⇢ B →
        Block.Preceq B C)
    {w : V} (hw : w ∈ Hs (M.confirmation_time S.E s))
    (hroot : Block.Preceq
      (Restated.Vocabulary.Protocol.confRoot M
        (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
          (W (strictEventIndex rho (M.confirmation_time S.E s)) w).st.core (M.confirmation_time S.E s)))
      C)
    (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S q) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S q)) → M.awake_for_grade2 S u (W j u) q)
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.confirmation_time S.E s)) w).st.core.toHealing (M.confirmation_time S.E s)
      (W (strictEventIndex rho (M.confirmation_time S.E s)) w).cache ⇢ c) :
    ∀ A0 : Block V, Restated.Vocabulary.Internal.namedConfirmationAnchor M S
      (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.confirmation_time S.E s)) w).st
        (M.confirmation_time S.E s)) (W (strictEventIndex rho (M.confirmation_time S.E s)) w).record c)
        ⇢ A0 →
    Block.Preceq A0 C := by
  intro A0 hA0
  have hW := hf.onePath
  set t := M.confirmation_time S.E s with ht
  set wv := W (strictEventIndex rho t) w with hwv
  set n := M.mkNode (M.ns_setClock S.E wv.st t) wv.record c with hn
  have hcore : n.st = M.store_with_cache (M.ns_setClock S.E wv.st t) c := by
    rw [hn, facts.nd.mkNode_st]
  have hnmem : n ∈ Restated.Vocabulary.Internal.NamedRecoveryRead.confirmationInputRead M S rho w s :=
    ⟨W (strictEventIndex rho t), mem_stateBeforeTime_along₆₁ hf.sorted hW t, c, hc, rfl⟩
  have hroot' : Block.Preceq (M.get_fg_root (M.toHealing (M.ns_setClock S.E wv.st t).core).toFG) C := by
    have h := hroot
    simp only [Restated.Vocabulary.Protocol.confRoot] at h
    rw [show Restated.Vocabulary.Proofs.Optimistic.tickStore M S wv.st.core t =
      (M.ns_setClock S.E wv.st t).core from
        (facts.hd.setClock_core_eq_store_with_t_s S.E wv.st t).symm] at h
    exact h
  rcases Restated.Vocabulary.Proofs.HealingSurface.confirmationAnchorAt_cases facts S rho w s n hnmem
      A0 hA0 with hfg | ⟨root, A, hframe, hactive, hAA0⟩
  · rw [hfg, hcore]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    exact hroot'
  · rw [hAA0]
    have hr : 0 < q + 1 := Nat.succ_pos q
    have hslo : (M.opening_slot S.hc (q + 1)) ≤ s + 1 := by
      rw [← hround]
      exact facts.gr.opening_slot_round_of_le_slot S.hc (s + 1)
    have hshi : s + 1 < (M.opening_slot S.hc ((q + 1) + 1)) := by
      rw [← hround]
      exact facts.gr.lt_opening_slot_round_of_succ S.hc (s + 1)
    have hdomain : M.domain S.E S.hc (q + 1) .g1 < t := by
      rw [facts.gr.Sts_domain_g1_eq_opening, facts.gr.opening_eq_proposal_time]
      exact (facts.sch.proposal_time_mono S.E hslo).trans_lt
        (facts.sch.proposal_time_succ_lt_confirmation_time S.E s)
    have hnext : t ≤ M.opening S.E S.hc ((q + 1) + 1) := by
      rw [facts.gr.opening_eq_proposal_time]
      exact (facts.sch.confirmationTime_lt_proposalTime_of_two_le S.E
        (Nat.succ_le_of_lt hshi)).le
    have hdomainHor : M.domain S.E S.hc (q + 1) .g1 ≤ rho.horizon := hdomain.le.trans hconfHor
    have hround' : (M.round_of S.hc) (S.E.slotOf t) = q + 1 := by
      rw [ht, facts.sch.Optimistic_slotOf_confirmation_time]
      exact hround
    have hroundSt : M.round_of S.hc n.st.core.s = q + 1 := by
      rw [hcore]
      try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
      rw [facts.hd.Sts_setClock_core_s, ht, facts.sch.Optimistic_slotOf_confirmation_time]
      exact hround
    rw [hroundSt] at hframe
    have hwX : w ∈ Hs (M.domain S.E S.hc (q + 1) .g1) := hHs _ _ hdomain.le hw
    have hactionDeadline : (Restated.Vocabulary.Execution.Setup.a M S q) + S.E.Δ ≤
        M.early S.E S.hc (q + 1) .g1 :=
      (facts.gr.action_delta_le_early S S.hc.R_ge_three
        (Nat.lt_succ_self q)).trans
        (facts.gr.q10_early_g2_le_early_g1 S (q + 1))
    have hearlyDomain : M.early S.E S.hc (q + 1) .g1 ≤
        M.domain S.E S.hc (q + 1) .g1 :=
      (facts.gr.q10_early_g1_le_domain_g2 S (q + 1)).trans
        (facts.gr.q10_domain_g2_lt_domain_g1 S (q + 1)).le
    have hgatDomain : lo ≤ M.domain S.E S.hc (q + 1) .g1 :=
      hpost.trans ((le_add_of_nonneg_right S.E.Δ_pos.le).trans
        (hactionDeadline.trans hearlyDomain))
    obtain ⟨_hAtree, hAGrade⟩ := Restated.activeConfirmationAnchor_g1_dataOn facts
      S Hs Xb hf hr hround' hdomain hnext hdomainHor hwX c hc hframe hactive hgatDomain
    have hFmono : Block.Preceq
        (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g1)) w).st.core.F wv.st.core.F :=
      F_mono_along₆₁ facts S hW w
        (Restated.strict_lengths_mono rho hdomain.le)
    have hFroot : Block.Preceq wv.st.core.F
        (M.get_fg_root (M.toHealing (M.ns_setClock S.E wv.st t).core).toFG) := by
      have hFJ := Restated.Vocabulary.Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
        facts S rho t w _ (mem_stateBeforeTime_along₆₁ hf.sorted hW t)
      have h := facts.fc.preceq_get_fg_root_of_F (st := (M.toHealing (M.ns_setClock S.E wv.st t).core).toFG)
        (by
          rw [facts.sto.Sts_toHealing_F, facts.sto.Sts_toHealing_J, facts.hd.setClock_core_F,
            facts.hd.setClock_core_J]
          exact preceq_eq_true_iff_Preceq.mpr hFJ)
      rw [facts.sto.Sts_toHealing_F, facts.hd.setClock_core_F] at h
      exact preceq_eq_true_iff_Preceq.mp h
    have hFC : Block.Preceq
        (W (strictEventIndex rho (M.domain S.E S.hc (q + 1) .g1)) w).st.core.F C :=
      preceq_trans_Preceq hFmono (preceq_trans_Preceq hFroot hroot')
    exact preceq_of_relativeG1_previousCarriers₆₁ facts S Hs Xb hf hHs hHsXb hfb hpost hcut
      hdomainHor hupper hwX hFC hA hAGrade

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Proofs.Optimistic
local macro "scs% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedCeilingStep)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-! ### Helpers for the relay steps -/

open scoped DC

/-- In a run sorted by key, the worlds strictly before the instant `t` are the worlds before the
    event of index `strictEventIndex rho t`. -/
private theorem stateBeforeTime_eq_strict₆₁s (S : Setup V) (rho : Record.Run V)
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f)) (t : Time) :
    Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t =
      Record.stateBeforeOf M S rho (strictEventIndex rho t) := by
  have hpre : rho.events.filter (fun e => decide (e.time < t)) =
      rho.events.take (rho.events.filter (fun e => decide (e.time < t))).length := by
    refine List.prefix_iff_eq_take.mp ?_
    rw [DecoupledConsensusModel.Proofs.Bridges.filter_eq_takeWhile_of_pairwise
      (R := fun e f => Record.Event.key e ≤ Record.Event.key f) ?_ _ hsorted]
    · exact List.takeWhile_prefix _
    · intro e f hk hf
      simp only [decide_eq_true_eq] at hf ⊢
      exact lt_of_le_of_lt (Restated.time_le_of_key_le hk) hf
  show (rho.events.filter (fun e => decide (e.time < t))).foldlM (Record.worldStepOf M S)
      (fun v => M.initial S v) =
    (rho.events.take (rho.events.filter (fun e => decide (e.time < t))).length).foldlM
      (Record.worldStepOf M S) (fun v => M.initial S v)
  rw [← hpre]

/-- In a run sorted by key, the world of a path `W` before the event of index
    `strictEventIndex rho t` is a world strictly before `t`. -/
private theorem mem_stateBeforeTime_along₆₁s {S : Setup V} {rho : Record.Run V}
    (hsorted : rho.events.Pairwise (fun e f => Record.Event.key e ≤ Record.Event.key f))
    {W : Nat → V → M.N} (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) (t : Time) :
    W (strictEventIndex rho t) ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t := by
  rw [stateBeforeTime_eq_strict₆₁s S rho hsorted]
  exact (hW _).1

/-- The store the slot-`s` vote duty reads from `n`'s core store is the core store of `n`'s store
    with its clock set to the slot's vote instant. -/
private theorem voteStore_eq₆₁s (facts : Record.Facts M) (S : Setup V) (n : M.N) (s : Slot) :
    Restated.Vocabulary.Proofs.Optimistic.voteStore M S n.st.core s =
      (M.ns_setClock S.E n.st (M.vote_time S.E s)).core := by
  rw [Restated.Vocabulary.Proofs.Optimistic.voteStore, Restated.Vocabulary.Proofs.Optimistic.tickStore,
    facts.hd.setClock_core_eq_store_with_t_s]

/-- The core store of `n`'s store with its clock set to `t` is the store `tickStore` stages from
    `n`'s core store at `t`. -/
private theorem setClock_core_tickStore₆₁s (facts : Record.Facts M) (S : Setup V) (n : M.N)
    (t : Time) :
    (M.ns_setClock S.E n.st t).core = Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core t := by
  rw [Restated.Vocabulary.Proofs.Optimistic.tickStore, facts.hd.setClock_core_eq_store_with_t_s]

/-- The SG root read under any grade contract from the healing view of a store with a cache written
    in is the one read from the store's own healing view. -/
private theorem sgRoot_store_with_cache₆₁s (facts : Record.Facts M) {E : Env V}
    {hc : Protocol.HealConfig} {st : M.NS} {c c' : M.Cache} {r : Round} {x : Block V} :
    M.get_sg_root_with (M.gradeContract c') E hc (M.toHealing (M.store_with_cache st c).core) r ⇢ x ↔
      M.get_sg_root_with (M.gradeContract c') E hc (M.toHealing st.core) r ⇢ x := by
  rw [facts.nd.gradeContract_sgRoot_eq_frameAnchor, facts.nd.gradeContract_sgRoot_eq_frameAnchor,
    facts.nd.store_with_cache_readFrame]
  exact facts.gr.anchor_eq_of_filtered_fg_root E hc r _
    (facts.nd.store_with_cache_get_filtered_block_tree st c) (facts.nd.store_with_cache_get_fg_root st c) x

omit [DecidableEq V] [Fintype V] in
/-- If `m` can return `a`, then `f <$> m` can return `f a`. -/
private theorem returns_map_intro₆₁s {α β : Type} (f : α → β) (m : DC.NDRE α) (a : α)
    (h : m ⇢ a) : (f <$> m) ⇢ f a := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image]
  exact ⟨_, h, rfl⟩

omit [DecidableEq V] [Fintype V] in
/-- `m >>= k` can return `b` exactly when `m` can return some `a` from which `k a` can return `b`. -/
private theorem returns_bind_iff₆₁s {α β : Type} (m : DC.NDRE α) (k : α → DC.NDRE β) (b : β) :
    (m >>= k) ⇢ b ↔ ∃ a, m ⇢ a ∧ k a ⇢ b := by
  unfold Record.Returns
  simp only [ExceptT.run_bind, Set.bind_def]
  constructor
  · intro h
    obtain ⟨e, he, hb⟩ := Set.mem_iUnion₂.mp h
    cases e with
    | ok a => exact ⟨a, he, hb⟩
    | error err => simp at hb
  · rintro ⟨a, ha, hb⟩
    exact Set.mem_iUnion₂.mpr ⟨_, ha, hb⟩

/-- The store `tickStore` stages from `n`'s core store has the tree of `n`'s core store. -/
private theorem tickStore_T₆₁s (facts : Record.Facts M) {S : Setup V} (n : M.N) (t : Time) :
    (Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core t).T = n.st.core.T := by
  rw [Restated.Vocabulary.Proofs.Optimistic.tickStore,
    ← facts.hd.setClock_core_eq_store_with_t_s S.E n.st t, facts.hd.Sts_setClock_core_T]

/-- The store `tickStore` stages from `n`'s core store has the `h_max` of `n`'s core store. -/
private theorem tickStore_h_max₆₁s (facts : Record.Facts M) {S : Setup V} (n : M.N) (t : Time) :
    (Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core t).h_max = n.st.core.h_max := by
  rw [Restated.Vocabulary.Proofs.Optimistic.tickStore,
    ← facts.hd.setClock_core_eq_store_with_t_s S.E n.st t, facts.hd.setClock_core_h_max]

/-- The store `tickStore` stages from `n`'s core store has the `h_j` of `n`'s core store. -/
private theorem tickStore_h_j₆₁s (facts : Record.Facts M) {S : Setup V} (n : M.N) (t : Time) :
    (Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core t).h_j = n.st.core.h_j := by
  rw [Restated.Vocabulary.Proofs.Optimistic.tickStore,
    ← facts.hd.setClock_core_eq_store_with_t_s S.E n.st t, ← facts.sto.toHealing_h_j,
    facts.hd.setClock_toHealing_h_j]

/-- The store `tickStore` stages from `n`'s core store has the FG root of `n`'s core store. -/
private theorem tickStore_fgRoot₆₁s (facts : Record.Facts M) {S : Setup V} (n : M.N) (t : Time) :
    M.get_fg_root (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core t)).toFG =
      M.get_fg_root (M.toHealing n.st.core).toFG :=
  facts.fc.get_fg_root_set_clock_slot _ _ _

/-- The store `tickStore` stages from `n`'s core store has the filtered block tree of `n`'s core
    store. -/
private theorem tickStore_filtered₆₁s (facts : Record.Facts M) {S : Setup V} (n : M.N) (t : Time) :
    M.get_filtered_block_tree
        (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M S n.st.core t)).toFG =
      M.get_filtered_block_tree (M.toHealing n.st.core).toFG :=
  facts.fc.get_filtered_block_tree_set_clock_slot _ _ _

/-- The late vote set of the store `tickStore` stages from `st` at `t` is the late vote set of `st`. -/
private theorem confLate_tickStore₆₁s (facts : Record.Facts M) (S : Setup V) (st : M.S) (t : Time)
    (s : Slot) :
    Restated.Vocabulary.Protocol.confLate M S.E (Restated.Vocabulary.Proofs.Optimistic.tickStore M S st t) s =
      Restated.Vocabulary.Protocol.confLate M S.E st s := by
  rw [Restated.Vocabulary.Protocol.confLate, Restated.Vocabulary.Protocol.confLate,
    Restated.Vocabulary.Proofs.Optimistic.tickStore, facts.sto.pool_set_clock_slot,
    facts.sto.store_with_t_s_timestamp_vote]

/-- Every SG root the grade contract of `n`'s cache can return for `n`'s healing store at round `r`
    is an outcome of `n`'s anchor at `r`. -/
private theorem nodeAnchor_of_sgRoot₆₁s (facts : Record.Facts M) (S : Setup V) (n : M.N) (r : Round)
    {R : Block V}
    (hR : M.get_sg_root_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core) r ⇢ R) :
    Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n r ⇢ R := by
  obtain ⟨G, hG⟩ := facts.gr.read_nonempty (M.gradeContract n.cache) S.E S.hc
    n.st.core.toHealing r
  have hanchor := (facts.nd.gradeContract_sgRoot_eq_frameAnchor n.cache S.E S.hc _ r R).1 hR
  have hGR : G.anchor = R := facts.nd.Sts_gradeContract_read_anchor n.cache S.E S.hc _ r G hG R hanchor
  rw [← hGR]
  unfold Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor Restated.Vocabulary.Internal.PhaseGrades.nodeRead
  unfold Record.Returns at hG ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image]
  exact ⟨_, hG, rfl⟩

/-- For every outcome `T` of the voter's filtered block tree of `st` at its slot, some outcome `K`
    of the voter candidate tree of `st` is `T`. -/
private theorem candidateTree_of_filtered₆₁s (facts : Record.Facts M) (E : Env V) (st : M.S)
    (T : Finset (Block V)) (hT : M.voter_filtered_block_tree E st st.s ⇢ T) :
    ∃ K : Finset (Block V),
      Restated.Vocabulary.Proofs.Optimistic.voter_candidate_tree M E (M.toHealing st) ⇢ K ∧ K = T := by
  obtain ⟨P0, hP0⟩ := facts.fc.voter_processed_block_tree_nonempty E
    (M.toHealing st).toFG.toSG.toGoldfishStore (M.toHealing st).s
  refine ⟨_, ?_, facts.fc.voter_candidate_tree_eq_protocol_voter_filtered_block_tree E st P0 hP0 T hT⟩
  unfold Restated.Vocabulary.Proofs.Optimistic.voter_candidate_tree
  exact (returns_bind_iff₆₁s _ _ _).2 ⟨P0, hP0, (Record.returns_pure _ _).2 rfl⟩

/-- The voter candidate tree of the core store of `st` with the cache `c` written in can return `K`
    exactly when that of `st`'s own core store can. -/
private theorem candidateTree_store_with_cache₆₁s (facts : Record.Facts M) (E : Env V) (st : M.NS)
    (c : M.Cache) (K : Finset (Block V)) :
    Restated.Vocabulary.Proofs.Optimistic.voter_candidate_tree M E
        (M.toHealing (M.store_with_cache st c).core) ⇢ K ↔
      Restated.Vocabulary.Proofs.Optimistic.voter_candidate_tree M E (M.toHealing st.core) ⇢ K := by
  have hs : ∀ x : M.S, (M.toHealing x).s = x.s := fun x => facts.sto.toHealing_gs_s x
  have hP : ∀ P : Finset (Block V),
      M.voter_processed_block_tree E (M.toHealing (M.store_with_cache st c).core).toFG.toSG.toGoldfishStore
        (M.toHealing (M.store_with_cache st c).core).s ⇢ P ↔
      M.voter_processed_block_tree E (M.toHealing st.core).toFG.toSG.toGoldfishStore
        (M.toHealing st.core).s ⇢ P := by
    intro P
    rw [hs, hs, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_voter_processed_block_tree]
  have hfrom : ∀ P : Finset (Block V),
      M.voter_processed_block_tree E (M.toHealing st.core).toFG.toSG.toGoldfishStore
        (M.toHealing st.core).s ⇢ P →
      M.get_filtered_block_tree_from (M.toHealing (M.store_with_cache st c).core).toFG P =
        M.get_filtered_block_tree_from (M.toHealing st.core).toFG P := by
    intro P hP0
    obtain ⟨X, hX⟩ := facts.fc.voter_filtered_block_tree_nonempty E st.core st.core.s
    have hX1 : M.voter_filtered_block_tree E (M.store_with_cache st c).core
        (M.store_with_cache st c).core.s ⇢ X := by
      rw [facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_voter_filtered_block_tree]
      exact hX
    rw [facts.fc.voter_candidate_tree_eq_protocol_voter_filtered_block_tree E _ P ((hP P).2 hP0) X hX1,
      facts.fc.voter_candidate_tree_eq_protocol_voter_filtered_block_tree E _ P hP0 X hX]
  unfold Restated.Vocabulary.Proofs.Optimistic.voter_candidate_tree
  rw [returns_bind_iff₆₁s, returns_bind_iff₆₁s]
  constructor
  · rintro ⟨P, hP1, hK⟩
    have hP0 := (hP P).1 hP1
    exact ⟨P, hP0, by rw [← hfrom P hP0]; exact hK⟩
  · rintro ⟨P, hP0, hK⟩
    exact ⟨P, (hP P).2 hP0, by rw [hfrom P hP0]; exact hK⟩

/-- For the node state `n` staged at `vote_time (s + 1)` from `w`'s node state in `W` with the cache
    outcome `c`, the body of the cone's vote inputs at `C` from the candidate fact, the FG root and
    the anchor of `n`'s store. -/
private theorem voteInputsBody₆₁s (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {w : V} {s : Slot} (hw : w ∈ Hs (M.view_freeze S.E s)) (hgat : lo ≤ M.view_freeze S.E s)
    {C : Block V}
    (hcand : ∀ K : Finset (Block V), Restated.Vocabulary.Proofs.Optimistic.voter_candidate_tree M S.E
        (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1))) ⇢ K → C ∈ K)
    (hroot : Block.Preceq
      (M.get_fg_root
        (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
          (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1))).toFG) C)
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.toHealing
      (M.vote_time S.E (s + 1)) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache ⇢ c) :
    let n := M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
      (M.vote_time S.E (s + 1))) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c
    (∀ A : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n
        (M.round_of S.hc n.st.core.s) ⇢ A → Block.Preceq A C) →
    ((∀ T : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T → C ∈ T) ∧
      Block.Preceq (M.get_fg_root (M.toHealing n.st.core).toFG) C ∧
      (∀ A : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n
          (M.round_of S.hc n.st.core.s) ⇢ A →
        Block.compatible A C = true) ∧
      (∀ A : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n
          (M.round_of S.hc n.st.core.s) ⇢ A →
        ∀ T : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T →
        ∀ D : Block V, Block.Preceq A D → D ≠ A → Block.Preceq D C → D ≠ C → D ∈ T)) := by
  intro n hanchor
  have hnst : n.st = M.store_with_cache (M.ns_setClock S.E
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st (M.vote_time S.E (s + 1))) c :=
    facts.nd.mkNode_st _ _ _
  have hX : (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
      (M.vote_time S.E (s + 1))).core = Restated.Vocabulary.Proofs.Optimistic.voteStore M S
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1) := by
    rw [voteStore_eq₆₁s facts]
  have hcandT : ∀ T : Finset (Block V),
      M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T → C ∈ T := by
    intro T hT
    have hT' := hT
    rw [hnst, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_voter_filtered_block_tree, hX] at hT'
    obtain ⟨K, hK, hKT⟩ := candidateTree_of_filtered₆₁s facts S.E _ T hT'
    rw [← hKT]
    exact hcand K hK
  refine ⟨hcandT, by rw [hnst, facts.nd.store_with_cache_get_fg_root, hX]; exact hroot,
    fun A hA => compatible_of_cases (Or.inl (hanchor A hA)), ?_⟩
  intro A hA T hT D hAD hDA hDC hDne
  exact Restated.votePathAt_of_candidateOn facts S Hs Xb hf hw c hc hgat T hT C (hcandT T hT)
    A hA D hAD hDA hDC hDne

/-- Under the bundle with path `W` and the committee majority, if the vote cone of `s` holds along
    `W` at `C` and every voter's read on `W` at `vote_time (s + 1)` has the body of the cone's vote
    inputs at `C`, with the timing and awake hypotheses of the signature, then the vote cone of
    `s + 1` holds along `W` at `C`. -/
private theorem coneSucc_of_voteBody₆₁s (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    {s : Slot} (hs : 0 < s)
    (hpost : lo ≤ M.vote_time S.E s)
    (hhor : M.confirmation_time S.E s ≤ rho.horizon)
    {C : Block V}
    (hvotes : Restated.NamedHonestVotesConeOn M S rho W Hs Xb s (fun X => Block.Preceq C X))
    (hinputs : ∀ w ∈ Hs (M.vote_time S.E (s + 1)), ∀ c : M.Cache, M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.toHealing
        (M.vote_time S.E (s + 1)) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache ⇢ c →
      let n := M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
        (M.vote_time S.E (s + 1))) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c
      ((∀ T : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T → C ∈ T) ∧
        Block.Preceq (M.get_fg_root (M.toHealing n.st.core).toFG) C ∧
        (∀ A : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n
            (M.round_of S.hc n.st.core.s) ⇢ A →
          Block.compatible A C = true) ∧
        (∀ A : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n
            (M.round_of S.hc n.st.core.s) ⇢ A →
          ∀ T : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T →
          ∀ D : Block V, Block.Preceq A D → D ≠ A → Block.Preceq D C → D ≠ C → D ∈ T)))
    (hrun : ∀ w ∈ S.E.committee (s + 1), w ∈ Hs (M.vote_time S.E (s + 1)) →
      ∀ j : Nat, rho.events[j]? = some (Record.Event.tick w (M.vote_time S.E (s + 1))) →
        M.awake_for_grade1 S w (W j w) (M.round_of S.hc (s + 1))) :
    Restated.NamedHonestVotesConeOn M S rho W Hs Xb (s + 1) (fun X => Block.Preceq C X) := by
  intro w hw hwcommittee
  have hrunw := hrun w hwcommittee hw
  set i := strictEventIndex rho (M.vote_time S.E (s + 1)) with hi_def
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc (W i w).st.core.toHealing
    (M.vote_time S.E (s + 1)) (W i w).cache
  set n := M.mkNode (M.ns_setClock S.E (W i w).st (M.vote_time S.E (s + 1))) (W i w).record c
    with hn_def
  obtain ⟨T, hT⟩ := facts.fc.voter_filtered_block_tree_nonempty S.E n.st.core n.st.core.s
  obtain ⟨L, hL⟩ := facts.fc.voter_view_nonempty S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore
    n.st.core.s
  obtain ⟨L', hL'⟩ := facts.fc.voter_support_view_nonempty S.E
    (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s
  obtain ⟨Hd, hHd⟩ := facts.fc.get_head_in_tree_with_layer_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) T L L' (n.st.core.s - 1)
  have hvoteHor : M.vote_time S.E (s + 1) ≤ rho.horizon :=
    le_trans (le_of_lt (lt_of_lt_of_le (lt_add_of_pos_right _ S.E.Δ_pos)
      (facts.sch.vote_time_succ_add_delta_le_confirmation_time S.E s))) hhor
  have hwCut : w ∈ Hs (M.support_cutoff S.E s) :=
    hHs _ _ (facts.sch.support_cutoff_le_vote_time_succ S.E s) hw
  have hhead : Block.Preceq C Hd :=
    Restated.fixedRoot_goldfishConeStepOn facts S Hs Xb hf hHs hHsXb hcom hs hpost hvoteHor
      hvotes hwCut c hc
      (by obtain ⟨h1, h2, h3, h4⟩ := hinputs w hw c hc; exact ⟨h1, h2, h3, h4⟩)
      T hT L hL L' hL' Hd hHd
  obtain ⟨H, hHerase, hHrun⟩ :=
    Restated.seedVoteDutyHead_runBlockOn facts S Hs Xb hf (hHsXb _ hw) (s + 1) c hc T hT L hL L' hL'
      Hd hHd
  refine ⟨H, ?_, hHrun, ?_⟩
  · rw [hHerase]
    exact hhead
  · rw [hHerase]
    exact Restated.seedVoteDutyHead_emitsOn facts S Hs Xb hf hw (Nat.succ_pos s) hwcommittee
      hvoteHor (hpost.trans (Restated.vote_time_mono_l58 facts S.E (Nat.le_succ s))) c hc hrunw
      T hT L hL L' hL' Hd hHd

/-- Under the bundle with path `W` and the committee majority, if the vote cone of `s` holds along
    `W` at `C`, `w`'s read `n` staged at `confirmation_time s` has the body of the cone's
    confirmation inputs at `C`, and `D` is confirmed with the grade contract of `c` on `w`'s store
    staged there, then `C` is an ancestor of `D`. -/
private theorem goldfishCone_confirmation_of_body₆₁s (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    {s : Slot} (hs : 0 < s)
    (hpost : lo ≤ M.vote_time S.E s)
    (hhor : M.confirmation_time S.E s ≤ rho.horizon)
    {C : Block V}
    (hnames : Restated.NamedHonestVotesConeOn M S rho W Hs Xb s (fun X => Block.Preceq C X))
    {w : V} (hw : w ∈ Hs (M.support_cutoff S.E s))
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.confirmation_time S.E s)) w).st.core.toHealing
      (M.confirmation_time S.E s) (W (strictEventIndex rho (M.confirmation_time S.E s)) w).cache ⇢ c) :
    let n := M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.confirmation_time S.E s)) w).st
      (M.confirmation_time S.E s)) (W (strictEventIndex rho (M.confirmation_time S.E s)) w).record c
    (C ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M n ∧
      Block.Preceq (M.get_fg_root (M.toHealing n.st.core).toFG) C ∧
      (∀ A : Block V, Restated.Vocabulary.Internal.namedConfirmationAnchor M S n ⇢ A →
        Block.compatible A C = true) ∧
      (∀ A : Block V, Restated.Vocabulary.Internal.namedConfirmationAnchor M S n ⇢ A →
        ∀ D : Block V, Block.Preceq A D → D ≠ A → Block.Preceq D C → D ≠ C →
          D ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M n)) →
    ∀ D : Block V, Restated.Vocabulary.Protocol.GenuineConfirmationWith M (M.gradeContract c) S.E S.hc
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.confirmation_time S.E s)) w).st.core
        (M.confirmation_time S.E s)) s D →
    Block.Preceq C D := by
  intro n hinputs D hgenuine
  obtain ⟨hinCand, hinRoot, hinAnchor, hinPath⟩ := hinputs
  have hcut : M.support_cutoff S.E s ≤ rho.horizon :=
    le_trans (facts.sch.Sts_support_cutoff_le_confirmation_time S.E s) hhor
  set tc := M.confirmation_time S.E s with htc
  set ww := W (strictEventIndex rho tc) w with hww
  set st := Restated.Vocabulary.Proofs.Optimistic.tickStore M S ww.st.core tc with hst
  have hncore : n.st = M.store_with_cache _ _ := facts.nd.mkNode_st _ _ _
  have hroot : Block.Preceq (Restated.Vocabulary.Protocol.confRoot M st) C := by
    have h := hinRoot
    rw [hncore] at h
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at h
    try rw [setClock_core_tickStore₆₁s facts S] at h
    exact h
  have hresolve := Restated.headsResolveIn_confStore_of_postHealingConeOn facts
    S Hs Xb hf hHs hHsXb hw hpost hcut hroot hnames
  have hsupport := Restated.coneSupport_confVotes_after_gstOn facts
    S Hs Xb hf hHs hHsXb hcom hs hpost hhor hnames hw hresolve
  have hvalid : Protocol.VoteSetValid S.E s (Restated.Vocabulary.Protocol.confLate M S.E st s) := by
    rw [hst, confLate_tickStore₆₁s facts S]
    exact Restated.voteSetValid_confLate_stateBeforeTimeOn facts S Hs Xb hf w tc s
  have hAnamed : ∀ A, Restated.Vocabulary.Protocol.confAnchorWith M (M.gradeContract c) S.E S.hc st ⇢ A →
      Restated.Vocabulary.Internal.namedConfirmationAnchor M S n ⇢ A := by
    intro A hA
    rw [Restated.Vocabulary.Internal.namedConfirmationAnchor, facts.nd.mkNode_cache, hncore]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    try rw [setClock_core_tickStore₆₁s facts S]
    rw [sgRoot_store_with_cache₆₁s facts, setClock_core_tickStore₆₁s facts S]
    exact hA
  obtain ⟨tm, htm⟩ := facts.sto.tau_nonempty st
  obtain ⟨A, hA⟩ := facts.fc.get_sg_root_with_nonempty (M.gradeContract c) S.E S.hc
    (M.toHealing st) (M.round_of S.hc st.s)
  have hu : Restated.Vocabulary.Protocol.confVotes M S.E st s ⇢
      ((_root_.DecoupledConsensusModel.beforeCutoff tm (M.support_cutoff S.E s) (st.pool s)).filter
        (fun u => M.no_second_vote_in
          (_root_.DecoupledConsensusModel.beforeCutoff st.timestamp_vote tc (st.pool s)) u = true)) :=
    returns_map_intro₆₁s _ _ _ (returns_map_intro₆₁s _ _ _ htm)
  have hscore : ∀ B' : Block V, ∃ g, M.goldfish_score S.E st.T
      ((_root_.DecoupledConsensusModel.beforeCutoff tm (M.support_cutoff S.E s) (st.pool s)).filter
        (fun u => M.no_second_vote_in
          (_root_.DecoupledConsensusModel.beforeCutoff st.timestamp_vote tc (st.pool s)) u = true))
      ((_root_.DecoupledConsensusModel.beforeCutoff tm (M.support_cutoff S.E s) (st.pool s)).filter
        (fun u => M.no_second_vote_in
          (_root_.DecoupledConsensusModel.beforeCutoff st.timestamp_vote tc (st.pool s)) u = true))
      s B' ⇢ g :=
    fun B' => facts.fc.goldfish_score_nonempty _ _ _ _ _ _
  choose sc hsc using hscore
  obtain ⟨H, hH⟩ := facts.fc.ghost_nonempty A (Restated.Vocabulary.Protocol.confTree M st) sc
    (fun B' => decide (Restated.Vocabulary.Protocol.confCount M S.E st s < 2 * sc B'))
  have helig := hgenuine.genuine A hA _ hu sc hsc H hH
  have hlive := facts.hd.update_confirmation_with_live_confirmed_of_eligible (M.gradeContract c)
    S.E S.hc st s tm htm A hA sc hsc H hH helig
  obtain ⟨st', hst'⟩ := facts.dt.update_confirmation_with_nonempty (M.gradeContract c) S.E S.hc st s
  have hDH : D = H := by
    rw [← hgenuine.selected st' hst', hlive st' hst']
  rw [hDH]
  have hcompat : Block.compatible A C = true := hinAnchor A (hAnamed A hA)
  rcases compatible_cases hcompat with hAC | hCA
  · have hpath : ∀ D' : Block V, Block.Preceq A D' → D' ≠ A → Block.Preceq D' C →
        D' ∈ Restated.Vocabulary.Protocol.confTree M st := by
      intro D' hAD hDne hD'C
      have hmem : D' ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M n := by
        by_cases hEq : D' = C
        · subst hEq
          exact hinCand
        · exact hinPath A (hAnamed A hA) D' hAD hDne hD'C hEq
      unfold Restated.Vocabulary.Internal.PhaseGrades.filteredTree at hmem
      rw [hncore] at hmem
      try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at hmem
      try rw [setClock_core_tickStore₆₁s facts S] at hmem
      exact hmem
    have hcs := hsupport _ hu
    exact facts.fc.ghost_passes_cone S.E st.T (Restated.Vocabulary.Protocol.confTree M st) _ _
      (Restated.Vocabulary.Protocol.confLate M S.E st s) s (Hs tc)
      hcs.majority hcs.counted hcs.sub hcs.no_equiv hcs.vote hvalid hAC hpath sc hsc H hH
  · exact preceq_trans_Preceq hCA
      (facts.fc.ghost_preceq A (Restated.Vocabulary.Protocol.confTree M st) sc _ H hH)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Proofs.Optimistic
local macro "scs% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedCeilingStep)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- A slot's vote instant is at most its view freeze, which is at most the next slot's vote instant;
    its support cutoff is at most its confirmation instant; and the next slot's vote instant is
    before its confirmation instant. -/
theorem relay_slot_instants_l61 (facts : Record.Facts M) (E : Env V) (s : Slot) :
    M.vote_time E s ≤ M.view_freeze E s ∧
      M.view_freeze E s ≤ M.vote_time E (s + 1) ∧
      M.support_cutoff E s ≤ M.confirmation_time E s ∧
      M.support_cutoff E s ≤ M.vote_time E (s + 1) ∧
      M.vote_time E (s + 1) < M.confirmation_time E s := by
  obtain ⟨h1, h2, h3, -, h5, h6⟩ := facts.sch.slot_instants_l55 E s
  have hΔ := E.Δ_pos
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [h1, h3]; linarith
  · rw [h3, h5]; linarith
  · rw [h2, h6]; linarith
  · rw [h2, h5]; linarith
  · rw [h5, h6]; linarith

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Proofs.Optimistic
local macro "scs% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedCeilingStep)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Under the bundle with path `W`, the weight bound and the slashable bound, if the committee of
    `s` voted descendants of `C`, a thin head of `s` of height at least `Mh − 1` is a descendant of
    `C`, every round-`r` action block of the set for `S.a r` is an ancestor of `C`, and every voter
    of the set for `vote_time (s + 1)` has vote-duty `h_max = Mh`, `h_j + 2 ≤ Mh` and its finality
    root an ancestor of `C`, with the timing and awake hypotheses of the signature, then every such
    voter's read on `W` has the body of the cone's vote inputs at `C`, and every outcome of its
    anchor is an ancestor of `C`. -/
theorem relayVoteInputs_stepOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hfb : BelowOneThirdOn S rho Hs)
    (hsb : Restated.SlashableBoundOn M S rho W Xb)
    {r : Round} {s : Slot} (hround : (M.round_of S.hc (s + 1)) = r + 1)
    (hpostAction : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S r))
    (hcut : Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (r + 1) ≤ rho.horizon)
    (hpost : lo ≤ M.vote_time S.E s)
    (hhor : M.confirmation_time S.E s ≤ rho.horizon)
    {C : Block V} {Mh : Height}
    (hvotes : Restated.NamedHonestVotesConeOn M S rho W Hs Xb s (fun X => Block.Preceq C X))
    (hthin : Restated.ThinHonestHeadAtOn M S rho W Hs Xb Mh s C)
    (hupper : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)),
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) u) r,
      ∀ g, M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ g →
      ∀ B, M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc (M.toHealing n.st.core).s) g ⇢ B →
        Block.Preceq B C)
    (hvoteFrontier : ∀ w ∈ Hs (M.vote_time S.E (s + 1)),
      (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1)).h_max = Mh)
    (hvoteGate : ∀ w ∈ Hs (M.vote_time S.E (s + 1)),
      (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1)).h_j + 2 ≤ Mh)
    (hvoteRoot : ∀ w ∈ Hs (M.vote_time S.E (s + 1)),
      Block.Preceq
        (M.get_fg_root
          (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
            (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1))).toFG) C)
    (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S r)) → M.awake_for_grade2 S u (W j u) r) :
    (∀ w ∈ Hs (M.vote_time S.E (s + 1)), ∀ c : M.Cache, M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.toHealing
        (M.vote_time S.E (s + 1)) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache ⇢ c →
      let n := M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
        (M.vote_time S.E (s + 1))) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c
      ((∀ T : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T → C ∈ T) ∧
        Block.Preceq (M.get_fg_root (M.toHealing n.st.core).toFG) C ∧
        (∀ A : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n
            (M.round_of S.hc n.st.core.s) ⇢ A →
          Block.compatible A C = true) ∧
        (∀ A : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n
            (M.round_of S.hc n.st.core.s) ⇢ A →
          ∀ T : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T →
          ∀ D : Block V, Block.Preceq A D → D ≠ A → Block.Preceq D C → D ≠ C → D ∈ T))) ∧
      ∀ w ∈ Hs (M.vote_time S.E (s + 1)), ∀ c : M.Cache, M.onPhaseTick S.E S.hc
          (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.toHealing
          (M.vote_time S.E (s + 1)) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache ⇢ c →
        let n := M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
          (M.vote_time S.E (s + 1))) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c
        ∀ A : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n
          (M.round_of S.hc n.st.core.s) ⇢ A → Block.Preceq A C := by
  obtain ⟨hvf1, hvf2, -, -, hvc⟩ := Restated.relay_slot_instants_l61 facts S.E s
  have hvoteHor : M.vote_time S.E (s + 1) ≤ rho.horizon := hvc.le.trans hhor
  have hanchor : ∀ w ∈ Hs (M.vote_time S.E (s + 1)), ∀ c : M.Cache, M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.toHealing
        (M.vote_time S.E (s + 1)) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache ⇢ c →
      let n := M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
        (M.vote_time S.E (s + 1))) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c
      ∀ A : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n
        (M.round_of S.hc n.st.core.s) ⇢ A → Block.Preceq A C := by
    intro w hw c hc
    exact Restated.voterAnchorAt_preceq_of_previousCarriersOn facts S Hs Xb hf hHs hHsXb hfb
      hround hpostAction hcut hvoteHor hupper hw (hvoteRoot w hw) hA c hc
  refine ⟨?_, hanchor⟩
  intro w hw c hc
  exact voteInputsBody₆₁s facts S Hs Xb hf (hHs _ _ hvf2 hw) (hpost.trans hvf1)
    (fun K hK => (Restated.seedRelayVoteFactsOn facts S Hs Xb hf hHs hHsXb hsb hpost hhor hvotes
      hthin hw (hvoteFrontier w hw) (hvoteGate w hw) (hvoteRoot w hw) c hc K hK).1)
    (hvoteRoot w hw) c hc (hanchor w hw c hc)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Proofs.Optimistic
local macro "scs% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedCeilingStep)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Under the hypotheses of `relayVoteInputs_stepOn`, if every member of the set for
    `confirmation_time s` has, at its store staged from `W`, `h_max = Mh`, `h_j + 2 ≤ Mh` and its
    confirmation root an ancestor of `C`, then every voter's read on `W` has the body of the cone's
    vote inputs at `C`, every confirmer's read on `W` has the body of the cone's confirmation inputs
    at `C`, and every outcome of every voter's anchor is an ancestor of `C`. -/
theorem relaySlotInputs_stepOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hfb : BelowOneThirdOn S rho Hs)
    (hsb : Restated.SlashableBoundOn M S rho W Xb)
    {r : Round} {s : Slot} (hround : (M.round_of S.hc (s + 1)) = r + 1)
    (hpostAction : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S r))
    (hcut : Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (r + 1) ≤ rho.horizon)
    (hpost : lo ≤ M.vote_time S.E s)
    (hhor : M.confirmation_time S.E s ≤ rho.horizon)
    {C : Block V} {Mh : Height}
    (hvotes : Restated.NamedHonestVotesConeOn M S rho W Hs Xb s (fun X => Block.Preceq C X))
    (hthin : Restated.ThinHonestHeadAtOn M S rho W Hs Xb Mh s C)
    (hupper : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r)),
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) u) r,
      ∀ g, M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ g →
      ∀ B, M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
          (M.round_of S.hc (M.toHealing n.st.core).s) g ⇢ B →
        Block.Preceq B C)
    (hvoteFrontier : ∀ w ∈ Hs (M.vote_time S.E (s + 1)),
      (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1)).h_max = Mh)
    (hvoteGate : ∀ w ∈ Hs (M.vote_time S.E (s + 1)),
      (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1)).h_j + 2 ≤ Mh)
    (hvoteRoot : ∀ w ∈ Hs (M.vote_time S.E (s + 1)),
      Block.Preceq
        (M.get_fg_root
          (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
            (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1))).toFG) C)
    (hconfFrontier : ∀ w ∈ Hs (M.confirmation_time S.E s),
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.confirmation_time S.E s)) w).st.core
        (M.confirmation_time S.E s)).h_max = Mh)
    (hconfGate : ∀ w ∈ Hs (M.confirmation_time S.E s),
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.confirmation_time S.E s)) w).st.core
        (M.confirmation_time S.E s)).h_j + 2 ≤ Mh)
    (hconfRoot : ∀ w ∈ Hs (M.confirmation_time S.E s),
      Block.Preceq (Restated.Vocabulary.Protocol.confRoot M
        (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
          (W (strictEventIndex rho (M.confirmation_time S.E s)) w).st.core
          (M.confirmation_time S.E s))) C)
    (hA : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S r)) → M.awake_for_grade2 S u (W j u) r) :
    (∀ w ∈ Hs (M.vote_time S.E (s + 1)), ∀ c : M.Cache, M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.toHealing
        (M.vote_time S.E (s + 1)) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache ⇢ c →
      let n := M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
        (M.vote_time S.E (s + 1))) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c
      ((∀ T : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T → C ∈ T) ∧
        Block.Preceq (M.get_fg_root (M.toHealing n.st.core).toFG) C ∧
        (∀ A : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n
            (M.round_of S.hc n.st.core.s) ⇢ A →
          Block.compatible A C = true) ∧
        (∀ A : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n
            (M.round_of S.hc n.st.core.s) ⇢ A →
          ∀ T : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T →
          ∀ D : Block V, Block.Preceq A D → D ≠ A → Block.Preceq D C → D ≠ C → D ∈ T))) ∧
    (∀ w ∈ Hs (M.confirmation_time S.E s), ∀ c : M.Cache, M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.confirmation_time S.E s)) w).st.core.toHealing
        (M.confirmation_time S.E s) (W (strictEventIndex rho (M.confirmation_time S.E s)) w).cache ⇢ c →
      let n := M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.confirmation_time S.E s)) w).st
        (M.confirmation_time S.E s)) (W (strictEventIndex rho (M.confirmation_time S.E s)) w).record c
      (C ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M n ∧
        Block.Preceq (M.get_fg_root (M.toHealing n.st.core).toFG) C ∧
        (∀ A : Block V, Restated.Vocabulary.Internal.namedConfirmationAnchor M S n ⇢ A →
          Block.compatible A C = true) ∧
        (∀ A : Block V, Restated.Vocabulary.Internal.namedConfirmationAnchor M S n ⇢ A →
          ∀ D : Block V, Block.Preceq A D → D ≠ A → Block.Preceq D C → D ≠ C →
            D ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M n))) ∧
      ∀ w ∈ Hs (M.vote_time S.E (s + 1)), ∀ c : M.Cache, M.onPhaseTick S.E S.hc
          (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.toHealing
          (M.vote_time S.E (s + 1)) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache ⇢ c →
        let n := M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
          (M.vote_time S.E (s + 1))) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c
        ∀ A : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n
          (M.round_of S.hc n.st.core.s) ⇢ A → Block.Preceq A C := by
  obtain ⟨-, -, hsc, -, -⟩ := Restated.relay_slot_instants_l61 facts S.E s
  obtain ⟨hvote, hvoteAnchor⟩ := Restated.relayVoteInputs_stepOn facts S Hs Xb hf hHs hHsXb hfb
    hsb hround hpostAction hcut hpost hhor hvotes hthin hupper hvoteFrontier hvoteGate hvoteRoot hA
  refine ⟨hvote, ?_, hvoteAnchor⟩
  intro w hw c hc n
  have hncore : n.st = M.store_with_cache _ _ := facts.nd.mkNode_st _ _ _
  have hfacts := Restated.seedRelayConfirmationFactsOn facts S Hs Xb hf hHs hHsXb hsb hpost hhor hvotes
    hthin (hHs _ _ hsc hw) (hconfFrontier w hw) (hconfGate w hw) (hconfRoot w hw) c hc
  have hanchor : ∀ A : Block V, Restated.Vocabulary.Internal.namedConfirmationAnchor M S n ⇢ A →
      Block.Preceq A C :=
    Restated.confirmationAnchorAt_preceq_of_previousCarriersOn facts S Hs Xb hf hHs hHsXb hfb
      hround hpostAction hcut hhor hupper hw (hconfRoot w hw) hA c hc
  refine ⟨?_, ?_, fun A hA => compatible_of_cases (Or.inl (hanchor A hA)), ?_⟩
  · unfold Restated.Vocabulary.Internal.PhaseGrades.filteredTree
    rw [hncore]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    try rw [setClock_core_tickStore₆₁s facts S]
    exact hfacts.1
  · rw [hncore]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    try rw [setClock_core_tickStore₆₁s facts S]
    exact hconfRoot w hw
  · intro A hA D h1 h2 h3 h4
    have h := hfacts.2 A hA D h1 h2 h3 h4
    unfold Restated.Vocabulary.Internal.PhaseGrades.filteredTree
    rw [hncore]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    try rw [setClock_core_tickStore₆₁s facts S]
    exact h

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Proofs.Optimistic
local macro "scs% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedCeilingStep)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Under the bundle with path `W`, if `w` is in `Xb`, `c` is an outcome of `w`'s cache update at
    `confirmation_time s`, and `D` is confirmed with the grade contract of `c` on `w`'s store staged
    at that instant, then `D` is the erasure of a run block along `W` through `Xb`. -/
theorem genuineConfirmation_runBlock_stepOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {w : V} (hw : w ∈ Xb) {s : Slot} {D : Block V}
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.confirmation_time S.E s)) w).st.core.toHealing
      (M.confirmation_time S.E s) (W (strictEventIndex rho (M.confirmation_time S.E s)) w).cache ⇢ c)
    (hD : Restated.Vocabulary.Protocol.GenuineConfirmationWith M (M.gradeContract c) S.E S.hc
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.confirmation_time S.E s)) w).st.core (M.confirmation_time S.E s))
      s D) :
    ∃ Dn : NamedBlock V, Dn.erase = D ∧ Restated.RunBlockOn M S rho W Xb Dn := by
  set t := M.confirmation_time S.E s with ht
  set ww := W (strictEventIndex rho t) with hww
  set st := Restated.Vocabulary.Proofs.Optimistic.tickStore M S (ww w).st.core t with hst
  have hwmem := mem_stateBeforeTime_along₆₁s hf.sorted hf.onePath t
  have hroot : M.get_fg_root (M.toHealing st).toFG ∈ M.get_filtered_block_tree (M.toHealing st).toFG := by
    have h1 := facts.fc.get_filtered_block_tree_toHealing_clock (ww w).st.core t (S.E.slotOf t)
    have h2 := facts.fc.get_fg_root_toHealing_clock (ww w).st.core t (S.E.slotOf t)
    simp only [Record.Model.S.toHealing] at h1 h2
    rw [hst, Restated.Vocabulary.Proofs.Optimistic.tickStore, h1, h2]
    exact Restated.Vocabulary.Proofs.HealingSurface.named_fgRoot_mem_filtered_stateBeforeTime facts S rho
      t w ww hwmem
  obtain ⟨R, hR⟩ := facts.fc.get_sg_root_with_nonempty (M.gradeContract c) S.E S.hc
    (M.toHealing st) (M.round_of S.hc st.s)
  obtain ⟨X, hX⟩ := facts.dt.update_confirmation_with_nonempty (M.gradeContract c) S.E S.hc st s
  have hlive := facts.dt.update_confirmation_with_live_confirmed_mem_filtered _ _ _ _ _ hroot R hR
    (facts.fc.get_sg_root_with_gradeContract_mem_filtered _ S.E S.hc _ _ hroot R hR) X hX
  rw [hD.selected X hX] at hlive
  have hDT : D ∈ (ww w).st.core.T := by
    have hmem := facts.fc.get_filtered_block_tree_subset _ hlive
    rw [facts.sto.toHealing_T, hst, tickStore_T₆₁s facts] at hmem
    exact hmem
  exact Restated.runBlock_of_mem_core_T_stateBeforeTimeOn facts S Hs Xb hf hw t hDT

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Proofs.Optimistic
local macro "scs% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedCeilingStep)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Under the bundle with path `W`, the committee majority and the slashable bound, if `C` is a
    round ceiling of `q` at `Mh` along `W` whose block is an ancestor of `D`, `s` is a later slot of
    the round before its last, and the vote cone of `s` holds along `W` at `D`, then every voter's
    read on `W` at `vote_time (s + 1)` and every confirmer's read on `W` at `confirmation_time s`
    have the bodies of the cone's inputs at `D`. -/
private theorem slotInputsBody_step₆₁s (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hsb : Restated.SlashableBoundOn M S rho W Xb)
    {Mh : Height} {q : Round} {C : NamedBlock V} {D : Block V}
    (h : Restated.RoundCeilingAtOn M S rho W (fun t => W (strictEventIndex rho t)) Hs Xb Mh q C)
    (hCD : Block.Preceq C.erase D)
    (hlo : lo ≤ M.vote_time S.E ((M.opening_slot S.hc q) - 1))
    {s : Slot} (hlo' : (M.opening_slot S.hc q) + 1 ≤ s)
    (hhi : s ≤ Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q - 1)
    (hcone : Restated.NamedHonestVotesConeOn M S rho W Hs Xb s (fun X => Block.Preceq D X))
    (hrun : ∀ w ∈ S.E.committee s, w ∈ Hs (M.vote_time S.E s) →
      ∀ j : Nat, rho.events[j]? = some (Record.Event.tick w (M.vote_time S.E s)) →
        M.awake_for_grade1 S w (W j w) (M.round_of S.hc s)) :
    (∀ w ∈ Hs (M.vote_time S.E (s + 1)), ∀ c : M.Cache, M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.toHealing
        (M.vote_time S.E (s + 1)) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache ⇢ c →
      let n := M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
        (M.vote_time S.E (s + 1))) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c
      ((∀ T : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T → D ∈ T) ∧
        Block.Preceq (M.get_fg_root (M.toHealing n.st.core).toFG) D ∧
        (∀ A : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n
            (M.round_of S.hc n.st.core.s) ⇢ A →
          Block.compatible A D = true) ∧
        (∀ A : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n
            (M.round_of S.hc n.st.core.s) ⇢ A →
          ∀ T : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T →
          ∀ D' : Block V, Block.Preceq A D' → D' ≠ A → Block.Preceq D' D → D' ≠ D → D' ∈ T))) ∧
    (∀ w ∈ Hs (M.confirmation_time S.E s), ∀ c : M.Cache, M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.confirmation_time S.E s)) w).st.core.toHealing
        (M.confirmation_time S.E s) (W (strictEventIndex rho (M.confirmation_time S.E s)) w).cache ⇢ c →
      let n := M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.confirmation_time S.E s)) w).st
        (M.confirmation_time S.E s)) (W (strictEventIndex rho (M.confirmation_time S.E s)) w).record c
      (D ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M n ∧
        Block.Preceq (M.get_fg_root (M.toHealing n.st.core).toFG) D ∧
        (∀ A : Block V, Restated.Vocabulary.Internal.namedConfirmationAnchor M S n ⇢ A →
          Block.compatible A D = true) ∧
        (∀ A : Block V, Restated.Vocabulary.Internal.namedConfirmationAnchor M S n ⇢ A →
          ∀ D' : Block V, Block.Preceq A D' → D' ≠ A → Block.Preceq D' D → D' ≠ D →
            D' ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M n))) := by
  have holast : (M.opening_slot S.hc q) < Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q :=
    Restated.openingSlot_lt_seedRoundLastSlot_l58 facts S q
  have hlastPos : 0 < Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q :=
    Nat.zero_lt_of_lt holast
  have hlastPred : Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q - 1 + 1 =
      Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q :=
    Nat.sub_add_cancel (Nat.succ_le_iff.mpr hlastPos)
  have hloOpenVote : lo ≤ M.vote_time S.E ((M.opening_slot S.hc q)) :=
    hlo.trans (Restated.vote_time_mono_l58 facts S.E (Nat.sub_le _ 1))
  have hslo : (M.opening_slot S.hc q) ≤ s := (Nat.le_succ _).trans hlo'
  have hsuccHi : s + 1 ≤ Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q := by
    rw [← hlastPred]
    exact Nat.succ_le_succ hhi
  have hshi : s ≤ Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q :=
    (Nat.le_succ s).trans hsuccHi
  have hslt : s < Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q :=
    lt_of_lt_of_le (Nat.lt_succ_self s) hsuccHi
  have hthin : Restated.ThinHonestHeadAtOn M S rho W Hs Xb Mh s D :=
    Restated.roundCeiling_thinHead_of_coneOn facts S Hs Xb hf hHs hHsXb hcom h hslo hshi hcone hlo
      hrun
  have hpostS : lo ≤ M.vote_time S.E s :=
    hloOpenVote.trans (Restated.vote_time_mono_l58 facts S.E hslo)
  have hhorS : M.confirmation_time S.E s ≤ rho.horizon :=
    (Restated.confirmationTime_mono_l58 facts S.E hhi).trans h.roundConfirmationInHorizon
  obtain ⟨hvf1, hvf2, hsc, -, -⟩ := Restated.relay_slot_instants_l61 facts S.E s
  constructor
  · intro w hw c hc
    have hfrontier := h.gateOff.voteFrontier (s + 1) (hslo.trans (Nat.le_succ s))
      (by simpa only [hlastPred] using hsuccHi) w hw
    have hgate := h.gateOff.voteGateOff (s + 1) (hslo.trans (Nat.le_succ s))
      (by simpa only [hlastPred] using hsuccHi) w hw
    have hrootC := h.aboveRoot.voteDuty (s + 1) (hslo.trans (Nat.le_succ s)) hsuccHi w hw
    have hrootD := Proofs.ModelProperties.Preceq_trans hrootC hCD
    refine voteInputsBody₆₁s facts S Hs Xb hf (hHs _ _ hvf2 hw) (hpostS.trans hvf1)
      (fun K hK => (Restated.seedRelayVoteFactsOn facts S Hs Xb hf hHs hHsXb hsb hpostS hhorS
        hcone hthin hw hfrontier hgate hrootD c hc K hK).1) hrootD c hc ?_
    intro A hA
    exact Proofs.ModelProperties.Preceq_trans
      (h.voteAnchor (s + 1) (hslo.trans (Nat.le_succ s)) hsuccHi w hw c hc A hA) hCD
  · intro w hw c hc n
    have hfrontier := h.gateOff.confirmationFrontier s hslo hhi w hw
    have hgate := h.gateOff.confirmationGateOff s hslo hhi w hw
    have hrootC := h.aboveRoot.confirmation s hslo hslt w hw
    have hrootD := Proofs.ModelProperties.Preceq_trans hrootC hCD
    have hncore : n.st = M.store_with_cache _ _ := facts.nd.mkNode_st _ _ _
    have hfacts := Restated.seedRelayConfirmationFactsOn facts S Hs Xb hf hHs hHsXb hsb hpostS hhorS
      hcone hthin (hHs _ _ hsc hw) hfrontier hgate hrootD c hc
    have hanchor : ∀ A : Block V, Restated.Vocabulary.Internal.namedConfirmationAnchor M S n ⇢ A →
        Block.Preceq A D := fun A hA =>
      Proofs.ModelProperties.Preceq_trans
        (h.confirmationAnchor s ((Nat.sub_le _ _).trans hslo) hslt w hw c hc A hA) hCD
    refine ⟨?_, ?_, fun A hA => compatible_of_cases (Or.inl (hanchor A hA)), ?_⟩
    · unfold Restated.Vocabulary.Internal.PhaseGrades.filteredTree
      rw [hncore]
      try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
      try rw [setClock_core_tickStore₆₁s facts S]
      exact hfacts.1
    · rw [hncore]
      try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
      try rw [setClock_core_tickStore₆₁s facts S]
      exact hrootD
    · intro A hA D' h1 h2 h3 h4
      have h' := hfacts.2 A hA D' h1 h2 h3 h4
      unfold Restated.Vocabulary.Internal.PhaseGrades.filteredTree
      rw [hncore]
      try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
      try rw [setClock_core_tickStore₆₁s facts S]
      exact h'

/-- Under the bundle with path `W`, the committee majority and the slashable bound, if `C` is a
    round ceiling of `q` at `Mh` along `W`, `v` is in the set for the opening slot's confirmation
    instant, `D` is confirmed with the grade contract of `c` on `v`'s store staged there,
    `lo ≤ vote_time (opening_slot q − 1)`, and `hrun` holds, then for every later slot `s` of the
    round the committee of `s` votes descendants of `D` along `W`, before the round's last slot the
    reads on `W` have the bodies of the cone's inputs at `D`, and every block a member of the set
    for `confirmation_time s` confirms is a descendant of `D`. -/
theorem roundCeiling_persistenceOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hsb : Restated.SlashableBoundOn M S rho W Xb)
    {Mh : Height} {q : Round} {C : NamedBlock V} {D : Block V}
    (h : Restated.RoundCeilingAtOn M S rho W (fun t => W (strictEventIndex rho t)) Hs Xb Mh q C)
    {v : V} (hv : v ∈ Hs (M.confirmation_time S.E ((M.opening_slot S.hc q))))
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q))) v).st.core.toHealing
      (M.confirmation_time S.E (M.opening_slot S.hc q))
      (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q))) v).cache ⇢ c)
    (hD : Restated.Vocabulary.Protocol.GenuineConfirmationWith M (M.gradeContract c) S.E S.hc
      (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.confirmation_time S.E (M.opening_slot S.hc q))) v).st.core
        (M.confirmation_time S.E (M.opening_slot S.hc q)))
      (M.opening_slot S.hc q) D)
    (hlo : lo ≤ M.vote_time S.E ((M.opening_slot S.hc q) - 1))
    (hrun : ∀ s : Slot, (M.opening_slot S.hc q) ≤ s →
      s ≤ Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q →
      ∀ w ∈ S.E.committee s, w ∈ Hs (M.vote_time S.E s) →
      ∀ j : Nat, rho.events[j]? = some (Record.Event.tick w (M.vote_time S.E s)) →
        M.awake_for_grade1 S w (W j w) (M.round_of S.hc s)) :
    (∀ s : Slot, (M.opening_slot S.hc q) + 1 ≤ s →
      s ≤ Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q →
        Restated.NamedHonestVotesConeOn M S rho W Hs Xb s (fun X => Block.Preceq D X)) ∧
    (∀ s : Slot, (M.opening_slot S.hc q) + 1 ≤ s →
      s < Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q →
      (∀ w ∈ Hs (M.vote_time S.E (s + 1)), ∀ c : M.Cache, M.onPhaseTick S.E S.hc
          (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.toHealing
          (M.vote_time S.E (s + 1)) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache ⇢ c →
        let n := M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
          (M.vote_time S.E (s + 1))) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c
        ((∀ T : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T → D ∈ T) ∧
          Block.Preceq (M.get_fg_root (M.toHealing n.st.core).toFG) D ∧
          (∀ A : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n
              (M.round_of S.hc n.st.core.s) ⇢ A →
            Block.compatible A D = true) ∧
          (∀ A : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n
              (M.round_of S.hc n.st.core.s) ⇢ A →
            ∀ T : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ T →
            ∀ D' : Block V, Block.Preceq A D' → D' ≠ A → Block.Preceq D' D → D' ≠ D → D' ∈ T))) ∧
      (∀ w ∈ Hs (M.confirmation_time S.E s), ∀ c : M.Cache, M.onPhaseTick S.E S.hc
          (W (strictEventIndex rho (M.confirmation_time S.E s)) w).st.core.toHealing
          (M.confirmation_time S.E s) (W (strictEventIndex rho (M.confirmation_time S.E s)) w).cache ⇢ c →
        let n := M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.confirmation_time S.E s)) w).st
          (M.confirmation_time S.E s)) (W (strictEventIndex rho (M.confirmation_time S.E s)) w).record c
        (D ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M n ∧
          Block.Preceq (M.get_fg_root (M.toHealing n.st.core).toFG) D ∧
          (∀ A : Block V, Restated.Vocabulary.Internal.namedConfirmationAnchor M S n ⇢ A →
            Block.compatible A D = true) ∧
          (∀ A : Block V, Restated.Vocabulary.Internal.namedConfirmationAnchor M S n ⇢ A →
            ∀ D' : Block V, Block.Preceq A D' → D' ≠ A → Block.Preceq D' D → D' ≠ D →
              D' ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M n)))) ∧
    (∀ s : Slot, (M.opening_slot S.hc q) + 1 ≤ s →
      s < Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q →
      ∀ w ∈ Hs (M.confirmation_time S.E s), ∀ E : Block V, ∀ cw : M.Cache,
        M.onPhaseTick S.E S.hc
          (W (strictEventIndex rho (M.confirmation_time S.E s)) w).st.core.toHealing
          (M.confirmation_time S.E s) (W (strictEventIndex rho (M.confirmation_time S.E s)) w).cache ⇢ cw →
        Restated.Vocabulary.Protocol.GenuineConfirmationWith M (M.gradeContract cw) S.E S.hc
          (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
            (W (strictEventIndex rho (M.confirmation_time S.E s)) w).st.core (M.confirmation_time S.E s))
          s E →
        Block.Preceq D E) := by
  have hopenPos : 0 < (M.opening_slot S.hc q) := facts.gr.openingSlot_pos_l58 S h.roundPositive
  have holast : (M.opening_slot S.hc q) < Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q :=
    Restated.openingSlot_lt_seedRoundLastSlot_l58 facts S q
  have hlastPos : 0 < Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q := Nat.zero_lt_of_lt holast
  have hlastPred : Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q - 1 + 1 = Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q :=
    Nat.sub_add_cancel (Nat.succ_le_iff.mpr hlastPos)
  have hosucc : (M.opening_slot S.hc q) + 1 ≤ Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q :=
    Nat.succ_le_iff.mpr holast
  have hrunO := hrun _ le_rfl (Nat.le_of_lt holast)
  have hloOpenVote : lo ≤ M.vote_time S.E ((M.opening_slot S.hc q)) :=
    hlo.trans (Restated.vote_time_mono_l58 facts S.E (Nat.sub_le _ 1))
  have hloOpenProposal : lo ≤ M.proposal_time S.E ((M.opening_slot S.hc q)) := by
    have h1 := Restated.vote_time_le_proposal_time_succ_l58 facts S.E ((M.opening_slot S.hc q) - 1)
    rw [Restated.openingSlot_pred_succ_l58 facts S h.roundPositive] at h1
    exact hlo.trans h1
  have hloVote : ∀ s : Slot, (M.opening_slot S.hc q) ≤ s → lo ≤ M.vote_time S.E s :=
    fun s hs => hloOpenVote.trans (Restated.vote_time_mono_l58 facts S.E hs)
  have hCD : Block.Preceq C.erase D :=
    Restated.roundCeiling_openingConfirmationOn facts S Hs Xb hf hHs hHsXb hcom h hv c hc hD hlo
      hrunO
  have hopeningHor : M.confirmation_time S.E
      ((M.opening_slot S.hc q)) ≤ rho.horizon :=
    (Restated.confirmationTime_mono_l58 facts S.E
      (Restated.openingSlot_le_seedRoundLastSlot_pred_l58 facts S q)).trans
      h.roundConfirmationInHorizon
  have hopeningVotes := Restated.roundCeiling_openingVotesOn facts S Hs Xb hf hHs hHsXb hcom h hlo
    hrunO
  obtain ⟨-, -, hscO, -, -⟩ := Restated.relay_slot_instants_l61 facts S.E ((M.opening_slot S.hc q))
  obtain ⟨x, hxHonest, hxCommittee, hDH⟩ :=
    Restated.genuineConfirmation_exists_honestVoteSupporter_ceilingOn facts
      S Hs Xb hf hHs hHsXb hcom (hHs _ _ hscO hv) hopenPos hloOpenVote hopeningHor c hc hD
      (fun x hx hxH j hj => hrunO x hx
        (hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E _) hxH) j hj)
  have hvoteConfO : M.vote_time S.E ((M.opening_slot S.hc q)) ≤
      M.confirmation_time S.E ((M.opening_slot S.hc q)) :=
    facts.sch.Protocol_vote_time_le_confirmation_time S.E _
  have hvoteHor : M.vote_time S.E ((M.opening_slot S.hc q)) ≤ rho.horizon :=
    hvoteConfO.trans hopeningHor
  set ix := strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q)) with hix_def
  obtain ⟨cx, hcx⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc (W ix x).st.core.toHealing
    (M.vote_time S.E (M.opening_slot S.hc q)) (W ix x).cache
  set nx := M.mkNode (M.ns_setClock S.E (W ix x).st (M.vote_time S.E (M.opening_slot S.hc q)))
    (W ix x).record cx with hnx_def
  obtain ⟨T, hT⟩ := facts.fc.voter_filtered_block_tree_nonempty S.E nx.st.core nx.st.core.s
  obtain ⟨L, hL⟩ := facts.fc.voter_view_nonempty S.E (M.toHealing nx.st.core).toFG.toSG.toGoldfishStore
    nx.st.core.s
  obtain ⟨L', hL'⟩ := facts.fc.voter_support_view_nonempty S.E
    (M.toHealing nx.st.core).toFG.toSG.toGoldfishStore nx.st.core.s
  obtain ⟨Hd, hHd⟩ := facts.fc.get_head_in_tree_with_layer_nonempty (M.gradeContract nx.cache) S.E S.hc
    (M.toHealing nx.st.core) T L L' (nx.st.core.s - 1)
  have hDHd : Block.Preceq D Hd := hDH cx hcx T hT L hL L' hL' Hd hHd
  obtain ⟨H, hHerase, hHrun⟩ :=
    Restated.seedVoteDutyHead_runBlockOn facts S Hs Xb hf (hHsXb _ hxHonest) ((M.opening_slot S.hc q))
      cx hcx T hT L hL L' hL' Hd hHd
  have hHemit := Restated.seedVoteDutyHead_emitsOn facts S Hs Xb hf (hHs _ _ hvoteConfO hxHonest)
    hopenPos hxCommittee hvoteHor hloOpenVote cx hcx
    (hrunO x hxCommittee (hHs _ _ hvoteConfO hxHonest)) T hT L hL L' hL' Hd hHd
  have hHemit' : (Restated.Vocabulary.Execution.Run.emits M S rho W x)
      (.gfVote ⟨x, (M.opening_slot S.hc q), H.erase.root⟩)
      (M.vote_time S.E ((M.opening_slot S.hc q))) := by
    rw [hHerase]
    exact hHemit
  have hH : Restated.NamedHonestHeadOn M S rho W Hs Xb ((M.opening_slot S.hc q)) H :=
    ⟨x, hxHonest, hxCommittee, hHrun, hHemit'⟩
  have hDH' : Block.Preceq D H.erase := by
    rw [hHerase]
    exact hDHd
  have hHthin : Mh - 1 ≤ (M.derive_named S.E S.cfg H).h :=
    Restated.roundCeiling_headThinOn facts S Hs Xb hf hHs hHsXb h (le_refl _) (Nat.le_of_lt holast)
      hH hlo hrunO
  have hH' : Restated.HonestHeadOn M S rho W Hs Xb ((M.opening_slot S.hc q)) H.erase :=
    ⟨x, hxHonest, hxCommittee, ⟨H, rfl, hHrun⟩, hHemit'⟩
  obtain ⟨hvfO1, hvfO2, -, hscvO, hvcO⟩ := Restated.relay_slot_instants_l61 facts S.E ((M.opening_slot S.hc q))
  have hconeSucc :=
    Restated.honestVotesCone_succ_of_genuineConfirmation_of_frozenVoteReadsOn facts
      S Hs Xb hf hHs hHsXb hv hloOpenProposal hopeningHor (contract := M.gradeContract c)
      ⟨hD.selected, hD.genuine⟩
      (fun w hw _ c' hc' => by
        set i := strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc q + 1)) with hi_def
        set st := Restated.Vocabulary.Proofs.Optimistic.voteStore M S (W i w).st.core
          (M.opening_slot S.hc q + 1) with hst_def
        have hduty0 : (M.ns_setClock S.E (W i w).st
            (M.vote_time S.E (M.opening_slot S.hc q + 1))).core = st := by
          rw [hst_def, voteStore_eq₆₁s facts]
        rw [facts.nd.mkNode_st]
        simp only [candidateTree_store_with_cache₆₁s facts, hduty0]
        have hrootC := h.aboveRoot.voteDuty ((M.opening_slot S.hc q) + 1) (Nat.le_succ _) hosucc w hw
        have hrootD := Proofs.ModelProperties.Preceq_trans hrootC hCD
        have hHprocessed := Restated.honestHead_voterProcessed_at_nextDuty_of_postHealingConeOn facts
          S Hs Xb hf hHs hHsXb hloOpenVote hopeningHor hopeningVotes hH' (hHs _ _ hscvO hw) hrootC
        obtain ⟨P0, hP0⟩ := facts.fc.voter_processed_block_tree_nonempty S.E
          (M.toHealing st).toFG.toSG.toGoldfishStore (M.toHealing st).s
        have hHP : H.erase ∈ P0 := hHprocessed P0 hP0
        have hHmem : H.erase ∈ (W i w).st.T := by
          have hdata := facts.fc.mem_T_of_mem_voter_processed_block_tree _ _ _ P0 hP0 hHP
          rw [facts.sto.toHealing_gs_T, hst_def, voteStore_eq₆₁s facts, facts.hd.Sts_setClock_core_T]
            at hdata
          exact hdata
        have hfrontier := h.gateOff.voteFrontier ((M.opening_slot S.hc q) + 1)
          (Nat.le_succ _) (by simpa only [hlastPred] using hosucc) w hw
        have hgate := h.gateOff.voteGateOff ((M.opening_slot S.hc q) + 1)
          (Nat.le_succ _) (by simpa only [hlastPred] using hosucc) w hw
        have hM : 1 ≤ Mh :=
          (Nat.succ_le_succ (Nat.zero_le 1)).trans ((Nat.le_add_left 2 st.h_j).trans hgate)
        have hvoteNextHor : M.vote_time S.E ((M.opening_slot S.hc q) + 1) ≤ rho.horizon :=
          hvcO.le.trans hopeningHor
        have hfilteredPre := Restated.frontierAncestor_filtered_of_gateOffOn facts
          S Hs Xb hf hsb (hHsXb _ hw) hvoteNextHor hHmem rfl hHrun hDH' hHthin hM
            (by simp only [Restated.Vocabulary.Proofs.Optimistic.voteStore,
                  tickStore_h_max₆₁s facts] at hfrontier
                exact hfrontier)
            (by simp only [Restated.Vocabulary.Proofs.Optimistic.voteStore,
                  tickStore_h_j₆₁s facts] at hgate
                exact hgate)
            (by simp only [Restated.Vocabulary.Proofs.Optimistic.voteStore,
                  tickStore_fgRoot₆₁s facts] at hrootD
                exact hrootD)
        have hfiltered : D ∈ M.get_filtered_block_tree (M.toHealing st).toFG := by
          rw [hst_def, Restated.Vocabulary.Proofs.Optimistic.voteStore, tickStore_filtered₆₁s facts]
          exact hfilteredPre
        have hmax : st.h_max ≤ (M.derive_named S.E S.cfg H).h + 1 := by
          rw [hfrontier]
          exact Nat.sub_le_iff_le_add.mp hHthin
        have hduty : (M.ns_setClock S.E (W i w).st
            (M.vote_time S.E (M.opening_slot S.hc q + 1))).core = st := by
          rw [hst_def, voteStore_eq₆₁s facts]
        have hcand := Restated.namedAncestorCandidate_of_processedDescendant_and_hMaxOn facts
          S Hs Xb hf hHsXb (hHs _ _ hvfO2 hw) (C := D) (H := H)
        simp only [← hi_def, hduty] at hcand
        refine ⟨M.get_filtered_block_tree_from (M.toHealing st).toFG P0, ?_,
          hcand P0 hP0 hHP hHrun hDH' hfiltered hmax (hloOpenVote.trans hvfO1)⟩
        unfold Restated.Vocabulary.Proofs.Optimistic.voter_candidate_tree
        exact (returns_bind_iff₆₁s _ _ _).2 ⟨P0, hP0, (Record.returns_pure _ _).2 rfl⟩)
      (fun w hw _ c' hc' R hR =>
        Proofs.ModelProperties.Preceq_trans
          (h.voteAnchor ((M.opening_slot S.hc q) + 1) (Nat.le_succ _) hosucc w hw c' hc' R
            (nodeAnchor_of_sgRoot₆₁s facts S _ _ hR)) hCD)
      (fun w hw hwc j hj => hrun _ (Nat.le_succ _) hosucc w hwc hw j hj)
  have hstep := fun (s : Slot) (hlo' : (M.opening_slot S.hc q) + 1 ≤ s)
      (hhi : s ≤ Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q - 1)
      (hcone : Restated.NamedHonestVotesConeOn M S rho W Hs Xb s (fun X => Block.Preceq D X)) =>
    slotInputsBody_step₆₁s facts S Hs Xb hf hHs hHsXb hcom hsb h hCD hlo hlo' hhi hcone
      (hrun s ((Nat.le_succ _).trans hlo') (hhi.trans (Nat.sub_le _ _)))
  have hfold : ∀ s : Slot, (M.opening_slot S.hc q) + 1 ≤ s →
      s ≤ Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q →
      Restated.NamedHonestVotesConeOn M S rho W Hs Xb s (fun X => Block.Preceq D X) := by
    intro s hlo'
    induction s, hlo' using Nat.le_induction with
    | base => intro _; exact hconeSucc
    | succ s hlo' ih =>
        intro hsuccHi
        have hshi : s ≤ Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q - 1 :=
          Nat.le_pred_of_lt
            (lt_of_lt_of_le (Nat.lt_succ_self s) hsuccHi)
        have hcone := ih (hshi.trans (Nat.sub_le _ _))
        have hslo : (M.opening_slot S.hc q) ≤ s := (Nat.le_succ _).trans hlo'
        have hsPos : 0 < s := lt_of_lt_of_le hopenPos hslo
        have hpostS : lo ≤ M.vote_time S.E s := hloVote s hslo
        have hhorS : M.confirmation_time S.E s ≤ rho.horizon :=
          (Restated.confirmationTime_mono_l58 facts S.E hshi).trans h.roundConfirmationInHorizon
        exact coneSucc_of_voteBody₆₁s facts S Hs Xb hf hHs hHsXb hcom hsPos hpostS hhorS hcone
          (hstep s hlo' hshi hcone).1 (hrun (s + 1) (hslo.trans (Nat.le_succ s)) hsuccHi)
  refine ⟨hfold, ?_, ?_⟩
  · intro s hlo' hhi
    exact hstep s hlo' (Nat.le_pred_of_lt hhi) (hfold s hlo' (Nat.le_of_lt hhi))
  intro s hlo' hhi w hw E cw hcw hE
  have hshi : s ≤ Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S q - 1 := Nat.le_pred_of_lt hhi
  have hcone := hfold s hlo' (hshi.trans (Nat.sub_le _ _))
  have hslo : (M.opening_slot S.hc q) ≤ s := (Nat.le_succ _).trans hlo'
  have hsPos : 0 < s := lt_of_lt_of_le hopenPos hslo
  have hpostS : lo ≤ M.vote_time S.E s := hloVote s hslo
  have hhorS : M.confirmation_time S.E s ≤ rho.horizon :=
    (Restated.confirmationTime_mono_l58 facts S.E hshi).trans h.roundConfirmationInHorizon
  obtain ⟨-, -, hsc, -, -⟩ := Restated.relay_slot_instants_l61 facts S.E s
  exact goldfishCone_confirmation_of_body₆₁s facts S Hs Xb hf hHs hHsXb hcom hsPos hpostS hhorS
    hcone (hHs _ _ hsc hw) cw hcw ((hstep s hlo' hshi hcone).2 w hw cw hcw) E hE

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Proofs.Optimistic
local macro "scs% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedCeilingStep)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Under the bundle with path `W` and the committee majority, if `0 < s`, `lo ≤ vote_time s`,
    `confirmation_time s` is in the horizon, the vote cone of `s` holds along `W` at `C`, every
    member of the set for `vote_time (s + 1)` has the cone's vote inputs at `C`, and `hrun` holds,
    then the vote cone of `s + 1` holds along `W` at `C`. -/
theorem honestVotesCone_succ_stepOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    {s : Slot} (hs : 0 < s)
    (hpost : lo ≤ M.vote_time S.E s)
    (hhor : M.confirmation_time S.E s ≤ rho.horizon)
    {C : Block V}
    (hvotes : Restated.NamedHonestVotesConeOn M S rho W Hs Xb s (fun X => Block.Preceq C X))
    (hinputs : ∀ w ∈ Hs (M.vote_time S.E (s + 1)), ∀ c : M.Cache,
      M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.toHealing
        (M.vote_time S.E (s + 1))
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache ⇢ c →
      Restated.Vocabulary.Proofs.HealingSurface.GoldfishConeVoteInputs M S rho s C w
        (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
          (M.vote_time S.E (s + 1))) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c))
    (hrun : ∀ w ∈ S.E.committee (s + 1), w ∈ Hs (M.vote_time S.E (s + 1)) →
      ∀ j : Nat, rho.events[j]? = some (Record.Event.tick w (M.vote_time S.E (s + 1))) →
        M.awake_for_grade1 S w (W j w) (M.round_of S.hc (s + 1))) :
    Restated.NamedHonestVotesConeOn M S rho W Hs Xb (s + 1) (fun X => Block.Preceq C X) :=
  Restated.seedHonestVotesCone_succOn facts S Hs Xb hf hHs hHsXb hcom hs hpost hhor hvotes
    hinputs hrun

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Proofs.Optimistic

end

section
set_option autoImplicit false
open scoped DC
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-! ## Grade 1 of the action FG source's Q2 -/

/-- If `f <$> m` can return `b`, then `m` can return some `a` with `f a = b`. -/
private theorem returns_map_elim₆₁p {α β : Type} (f : α → β) (m : DC.NDRE α) (b : β)
    (h : (f <$> m) ⇢ b) : ∃ a, m ⇢ a ∧ f a = b := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image] at h
  obtain ⟨e, he, hb⟩ := h
  cases e with
  | ok a => exact ⟨a, he, by simpa [Except.map] using hb⟩
  | error err => simp [Except.map] at hb

/-- Under the bundle with path `W`, if round `r`'s grade cutoffs are ready, `p` is in the set for
    `domain r g2`, `w` in the set for `domain r g1`, `n` is a node state of `p`'s round-`r` action
    read along `W` whose action FG source can return `some B`, the cross-reader body condition holds
    for `p`, `w` and every `Q` the Q2 of `n` can return, and `lo ≤ opening (r − η_SG)`, then every
    outcome of the Q2 of `n` is some `Q` whose grade-1 store grade at `w`'s store in
    `W (strictEventIndex rho (domain r g1))` has only `true` outcomes. -/
theorem actionFGSource_rawG1_at_read_after_cutoffOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {r : Round} (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho r)
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ rho.horizon)
    {p w : V} (hp : p ∈ Hs (M.domain S.E S.hc r .g2)) (hw : w ∈ Hs (M.domain S.E S.hc r .g1))
    {B : Block V} (n : M.N)
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) p) r)
    (hsource : Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n ⇢ some B)
    (hguard : ∀ Q, Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ some Q →
      Restated.Vocabulary.Proofs.HealingSurface.CrossReaderBodyReadyGuard M S rho r p w
        (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) p)
        (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w) Q)
    (hlo : lo ≤ M.opening S.E S.hc (r - S.hc.η_SG)) :
    ∀ o : Option (Block V), Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ o →
      ∃ Q : Block V, o = some Q ∧
        ∀ b, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
          (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st r .g1 Q ⇢ b → b = true := by
  have hmem := mem_stateBeforeTime_along₆₁ hf.sorted hf.onePath
    (Restated.Vocabulary.Execution.Setup.a M S r)
  have hnAt : n ∈ Restated.Vocabulary.Proofs.HealingSurface.actionReadAt M S rho p r := ⟨_, hmem, hn⟩
  have hround : M.round_of S.hc (M.toHealing n.st.core).s = r := by
    show M.round_of S.hc (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.s = r
    rw [facts.sto.toHealing_s]
    exact Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt_round facts S rho p r n hnAt
  have hsrc0 : (do
      let g ← M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
        (M.round_of S.hc (M.toHealing n.st.core).s)
      M.fg_source_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
        (M.round_of S.hc (M.toHealing n.st.core).s) g) ⇢ some B := hsource
  rw [hround] at hsrc0
  obtain ⟨A2, hA2, hsrc⟩ := (returns_bind_iff₆₁s _ _ _).1 hsrc0
  obtain ⟨Q2, hA2Q, -⟩ := facts.dt.fg_source_with_some _ _ _ _ _ _ hsrc rfl
  subst hA2Q
  intro o ho
  unfold Restated.Vocabulary.Internal.PhaseGrades.nodeQ2
    Restated.Vocabulary.Internal.PhaseGrades.nodeRead at ho
  obtain ⟨G, hG, hGo⟩ := returns_map_elim₆₁p _ _ _ ho
  have hGQ : some Q2 = G.Q2 := facts.dt.grade2_block_with_eq_read_Q2 _ _ _ _ _ G hG _ hA2
  have hoQ : o = some Q2 := by rw [← hGo, ← hGQ]
  have hq : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ some Q2 := by
    have h : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ G.Q2 :=
      returns_map_intro₆₁s (fun g : GradeRead V => g.Q2) _ G hG
    rwa [← hGQ] at h
  exact ⟨Q2, hoQ, Restated.selectedG2_G1_at_read_after_cutoffOn facts S Hs Xb hf hHs hHsXb
    ready hhor hp hw n hn hq (hguard Q2 hq) hlo⟩

/-- Under the bundle with path `W`, if round `r`'s grade cutoffs are ready, `p` is in the set for
    `domain r g2`, `n` is a node state of `p`'s round-`r` action read along `W` whose action FG
    source can return `some B`, the cross-reader body condition holds for `p`, every member `w` of
    the set for `domain r g1` and every `Q` the Q2 of `n` can return, and `lo ≤ opening (r − η_SG)`,
    then for every such `w` every outcome of the Q2 of `n` is some `Q` whose grade-1 store grade at
    `w`'s store in `W (strictEventIndex rho (domain r g1))` has only `true` outcomes. -/
theorem actionFGSource_rawG1_at_firstInteriorOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {r : Round} (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho r)
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ rho.horizon)
    {p : V} (hp : p ∈ Hs (M.domain S.E S.hc r .g2)) {B : Block V} (n : M.N)
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) p) r)
    (hsource : Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n ⇢ some B)
    (hguard : ∀ w, w ∈ Hs (M.domain S.E S.hc r .g1) → ∀ Q,
      Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ some Q →
      Restated.Vocabulary.Proofs.HealingSurface.CrossReaderBodyReadyGuard M S rho r p w
        (W (strictEventIndex rho (M.domain S.E S.hc r .g2)) p)
        (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w) Q)
    (hlo : lo ≤ M.opening S.E S.hc (r - S.hc.η_SG)) :
    ∀ w ∈ Hs (M.domain S.E S.hc r .g1),
      ∀ o : Option (Block V), Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ o →
      ∃ Q : Block V, o = some Q ∧
        ∀ b, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
          (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st r .g1 Q ⇢ b → b = true := by
  intro w hw
  exact Restated.actionFGSource_rawG1_at_read_after_cutoffOn facts
    S Hs Xb hf hHs hHsXb ready hhor hp hw n hn hsource (hguard w hw) hlo

end

end DecoupledConsensusModel.Sts.Restated
