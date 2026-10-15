import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bStepConeIter
import Proofs.Claims.Restated.Claim13beRoute3_45
import Proofs.Claims.Restated.Claim13beRoute3_46
import Proofs.Claims.Restated.Claim13beRoute3_47b
import Proofs.Claims.Restated.Claim13beRoute3_48
import Proofs.Claims.Restated.Claim13beRoute3_48b
import Proofs.Claims.Restated.Claim13beRoute3_49
import Proofs.Claims.Restated.Claim13beRoute3_50
import Proofs.Claims.Restated.Claim13beRoute3_50b
import Proofs.Claims.Restated.Claim13beRoute3_51
import Proofs.Claims.Restated.Claim13beRoute3_52
import Proofs.Claims.Restated.Claim13beRoute3_56
import Proofs.Claims.Restated.Claim13beRoute3_58
import Proofs.Claims.Restated.Claim13beRoute3_60b
import Proofs.Claims.Restated.Claim13beRoute3_62
import Proofs.Claims.Restated.Claim13beRoute3_65
import Proofs.Claims.Restated.Claim13beRoute3_67
import Proofs.Claims.Restated.Claim13beRoute3_68
import Proofs.Claims.Restated.Claim13beRoute3_69
import Proofs.Claims.Restated.Claim13beRoute3_69b
import Proofs.Claims.Restated.Vocabulary_Execution_HealthyLocalFacts
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Claims.Restated.Vocabulary_Execution_SeedCommonRootComplement
import Proofs.Claims.Restated.Vocabulary_ModelVocabulary_Healing_Schedule
import Proofs.Vocabulary.Protocol.ChainState.Chain
import Proofs.Vocabulary.ModelVocabulary
import Proofs.Claims.Restated.Vocabulary_Protocol_ChainState_CheckpointAlgebra
import Proofs.Vocabulary.Protocol.ChainState.DerivationGeometry
import Proofs.Claims.Restated.Vocabulary_Protocol_ChainState_ProposalBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Evidence_ProvenanceBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Head_PreparedProposalReadBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_Ladder
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_JustificationBound
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_42c
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.RunVocabulary
import Model.Conditions.Vocabulary_Internal_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGradeQueries
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGrades
import Model.Conditions.Vocabulary_Internal_Definitions_TickReads
import Model.Conditions.Vocabulary_Internal_HealingSurface
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ProposalSourcesInternal
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_ModelVocabulary_Healing_Schedule
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_Evidence_ProvenanceBridge
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_FinalityFilterRetention
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_SeedCeiling
import Proofs.Vocabulary.Protocol.ForkChoice.Views.ProposalCore
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Conditions.Vocabulary_Statements_Instantiation_Proposals
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13beRoute3_70b

/-!
# Fresh sources reach the next opening proposal

Theorems stated over a model `M : Record.Model V` along the path `W` of the bundle
`AdmissibleFieldsOn`: under `GateOffFrameAtOn`, a fresh FG source is active in, compatible with and
an ancestor of the next opening proposal's parent; named entries and justifications are unique; and
the largest `h_max` grows with eventual height progress.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

/-! ## Helpers -/

section
set_option autoImplicit false
open scoped DC
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface

/-- Along the path `W` of the bundle, the world before the event of index `strictEventIndex rho t`
    is a world strictly before `t`. -/
private theorem mem_stateBeforeTime_along₇₀b (facts : Record.Facts M) {S : Setup V} {rho : Record.Run V}
    {Hs : Int → Finset V} {Xb : Finset V} {lo : Int} {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo) (t : Time) :
    W (strictEventIndex rho t) ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t := by
  rw [Restated.stateBeforeTime_eq_stateBefore_strictEventIndexOn facts S Hs Xb hf t]
  exact (hf.onePath _).1

/-- For every path `W` of `rho`, `W (m + k)` is among the worlds the events `m` to `m + k - 1` of
    `rho` lead to from `W m`. -/
private theorem onePath_reach₇₀b {S : Setup V} {rho : Record.Run V}
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
private theorem onePath_slice₇₀b {S : Setup V} {rho : Record.Run V}
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W) {m n : Nat}
    (hmn : m ≤ n) :
    W n ∈ ((rho.events.drop m).take (n - m)).foldlM (Record.worldStepOf M S) (W m) := by
  have h := onePath_reach₇₀b W hW m (n - m)
  rwa [Nat.add_sub_of_le hmn] at h

/-- Every node state of the round-`r` action read computed from `before` holds `before`'s bodies. -/
private theorem actionReadFrom_bodies₇₀b (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ nr ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      nr.st.bodies = before.st.bodies := by
  rintro _ ⟨c, -, st, hst, rfl⟩
  rewrite [facts.nd.mkNode_st, facts.nd.store_with_cache_bodies]
  rw [facts.dt.named_update_confirmation_with_bodies _ _ _ _ _ st hst,
    facts.hd.ModelProperties_setClock_bodies]

omit [DecidableEq V] [Fintype V] in
/-- The number of events at or before `t` is the number of events strictly before `t + 1`. -/
private theorem inclusiveEventIndex_eq_strict_succ₇₀b (rho : Record.Run V) (t : Time) :
    inclusiveEventIndex rho t = strictEventIndex rho (t + 1) := by
  unfold inclusiveEventIndex strictEventIndex
  congr 1
  apply List.filter_congr
  intro e _
  simp only [decide_eq_decide]
  exact Int.lt_add_one_iff.symm

/-- If `m` can return `a`, then `f <$> m` can return `f a`. -/
private theorem returns_map_intro₇₀b {α β : Type} (f : α → β) (m : DC.NDRE α) (a : α)
    (h : m ⇢ a) : (f <$> m) ⇢ f a := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image]
  exact ⟨_, h, rfl⟩

/-- The anchor of a node state `n` at round `r` has an outcome. -/
private theorem nodeAnchor_nonempty₇₀b (facts : Record.Facts M) (S : Setup V) (n : M.N)
    (r : Round) :
    ∃ A : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n r ⇢ A := by
  obtain ⟨G, hG⟩ := facts.gr.read_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) r
  refine ⟨G.anchor, ?_⟩
  unfold Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor Restated.Vocabulary.Internal.PhaseGrades.nodeRead
  exact returns_map_intro₇₀b (fun g : DecoupledConsensusModel.Protocol.GradeRead V => g.anchor) _ G hG

/-- If the grade read at `n` for round `r` can return `G`, the grade-2 candidate read there can
    return `G.Q2`. -/
private theorem nodeQ2_of_read₇₀b (S : Setup V) (n : M.N) (r : Round)
    (G : DecoupledConsensusModel.Protocol.GradeRead V)
    (hG : (M.gradeContract n.cache).read S.E S.hc (M.toHealing n.st.core) r ⇢ G) :
    Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ G.Q2 := by
  unfold Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 Restated.Vocabulary.Internal.PhaseGrades.nodeRead
  exact returns_map_intro₇₀b (fun g : DecoupledConsensusModel.Protocol.GradeRead V => g.Q2) _ G hG

/-- The round-`r` action read from `before` has a node state `n` on which the grade-2 block read
    returns some `g` and the SG vote selector on `g` some block `B`. -/
private theorem exists_actionSG₇₀b (facts : Record.Facts M) (S : Setup V) (before : M.N)
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
  obtain ⟨g, hg⟩ := facts.dt.grade2_block_with_nonempty
    (M.gradeContract (M.mkNode st before.record c).cache) S.E S.hc
    (M.toHealing (M.mkNode st before.record c).st.core)
    (M.round_of S.hc (M.toHealing (M.mkNode st before.record c).st.core).s)
  obtain ⟨B, hB⟩ := facts.dt.get_sg_vote_with_nonempty
    (M.gradeContract (M.mkNode st before.record c).cache) S.E S.hc
    (M.toHealing (M.mkNode st before.record c).st.core)
    (M.round_of S.hc (M.toHealing (M.mkNode st before.record c).st.core).s) g
  exact ⟨_, ⟨c, hc, st, hst, rfl⟩, g, hg, B, hB⟩

/-- Setting the clock of `st` to `t` keeps the FG root of its core store. -/
private theorem setClock_fgRoot₇₀b (facts : Record.Facts M) (S : Setup V) (st : M.NS)
    (t : Time) :
    M.get_fg_root (M.toHealing (M.ns_setClock S.E st t).core).toFG =
      M.get_fg_root (M.toHealing st.core).toFG := by
  rw [facts.hd.setClock_core_eq_store_with_t_s]
  exact facts.fc.get_fg_root_toHealing_clock _ _ _

/-- A slot `d` from round `c`'s opening slot to its last slot is a slot of round `c`. -/
private theorem seedEntryRoundOf₇₀b (facts : Record.Facts M) (S : Setup V) {c : Round} {d : Slot}
    (hlo : (M.opening_slot S.hc c) ≤ d) (hhi : d ≤ (M.opening_slot S.hc (c + 1)) - 1) :
    (M.round_of S.hc d) = c := by
  have hR : 2 ≤ S.hc.R := S.hc.R_ge_two
  have hpos : 0 < (M.opening_slot S.hc c) + S.hc.R :=
    lt_of_lt_of_le (lt_of_lt_of_le Nat.zero_lt_two hR) (Nat.le_add_left _ _)
  rw [facts.gr.opening_slot_succ S.hc c] at hhi
  have hlt : d < (M.opening_slot S.hc c) + S.hc.R := lt_of_le_of_lt hhi (Nat.sub_lt hpos Nat.one_pos)
  have h := facts.gr.round_of_opening_slot_add S.hc c (Nat.sub_lt_left_of_lt_add hlo hlt)
  rw [Nat.add_sub_cancel' hlo] at h
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
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.Optimistic
local macro "ssc% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Execution.SeedSourceCapClosure)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- `support_cutoff (seedRoundLastSlot c) ≤ confirmation_time (opening_slot (c + 1))` and
    `proposal_time (opening_slot (c + 1)) ≤ confirmation_time (opening_slot (c + 1))`. -/
theorem nextOpening_instants_l70 (facts : Record.Facts M) (S : Setup V) (c : Round) :
    M.support_cutoff S.E (Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot M S c) ≤
        M.confirmation_time S.E ((M.opening_slot S.hc (c + 1))) ∧
      M.proposal_time S.E ((M.opening_slot S.hc (c + 1))) ≤
        M.confirmation_time S.E ((M.opening_slot S.hc (c + 1))) := by
  constructor
  · exact (facts.sch.Protocol_support_cutoff_le_confirmation_time S.E _).trans
      (Restated.confirmationTime_mono_l58 facts S.E (by unfold Restated.Vocabulary.Proofs.HealingSurface.seedRoundLastSlot; exact Nat.sub_le _ _))
  · exact facts.sch.proposal_time_le_confirmation_time S.E _

/-- Under the bundle along `W`, if `GateOffFrameAtOn` at `Mh` holds along `W` from round `c − 1` to
    `c + 1` and `Cn` is a run block along `W` at height at least `Mh − 1` erasing to `C`, then the
    proposer of the next opening slot, if in the set for its proposal instant, has in the world of
    `W` before that instant its FG root an ancestor of `C`, `h_max = Mh` and `h_j + 2 ≤ Mh`. -/
theorem seedSourceCap_nextProposal_frameOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {Mh : Height} {c : Round} (_hc : 1 ≤ c)
    (hframe : Restated.GateOffFrameAtOn M S rho (fun t => W (strictEventIndex rho t)) Hs Mh
      (c - 1) (c + 1))
    (_hpost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (c - 1)))
    (_hhor : (Restated.Vocabulary.Execution.Setup.a M S (c + 1)) ≤ rho.horizon)
    {C : Block V} {Cn : NamedBlock V} (hCerase : Cn.erase = C)
    (hCrun : Restated.RunBlockOn M S rho W Xb Cn)
    (hCband : Mh - 1 ≤ (M.derive_named S.E S.cfg Cn).h) :
    S.E.proposer (M.opening_slot S.hc (c + 1)) ∈
        Hs (M.proposal_time S.E (M.opening_slot S.hc (c + 1))) →
      Block.Preceq
        (M.get_fg_root
          (M.toHealing (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (c + 1))))
            (S.E.proposer (M.opening_slot S.hc (c + 1)))).st.core).toFG) C ∧
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (c + 1))))
        (S.E.proposer (M.opening_slot S.hc (c + 1)))).st.h_max = Mh ∧
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (c + 1))))
        (S.E.proposer (M.opening_slot S.hc (c + 1)))).st.h_j + 2 ≤ Mh := by
  intro hp
  have hpredC : (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) ≤ (Restated.Vocabulary.Execution.Setup.a M S c) := Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.sub_le c 1)
  have hdelay : (Restated.Vocabulary.Execution.Setup.a M S c) + S.E.Δ ≤
      M.proposal_time S.E ((M.opening_slot S.hc (c + 1))) :=
    Restated.Vocabulary.Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt facts S (Nat.lt_succ_self c)
  have hreadHi : M.proposal_time S.E ((M.opening_slot S.hc (c + 1))) ≤
      (Restated.Vocabulary.Execution.Setup.a M S (c + 1)) := by
    rw [Restated.a_eq_confirmation_opening_l58 facts S (c + 1)]
    exact facts.sch.proposal_time_le_confirmation_time S.E _
  have hfr : (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (c + 1))))
        (S.E.proposer (M.opening_slot S.hc (c + 1)))).st.core.h_j + 2 ≤ Mh ∧
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (c + 1))))
        (S.E.proposer (M.opening_slot S.hc (c + 1)))).st.core.h_max = Mh :=
    hframe (M.proposal_time S.E ((M.opening_slot S.hc (c + 1))))
      (hpredC.trans ((le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans hdelay))
      hreadHi (S.E.proposer ((M.opening_slot S.hc (c + 1)))) hp
  refine ⟨?_, hfr.2, hfr.1⟩
  rw [Restated.Vocabulary.Proofs.HealingSurface.fgRoot_eq_F_of_frame facts hfr.1 hfr.2]
  simpa only [hCerase] using
    Restated.finalizedRoot_preceq_of_bandOn facts S Hs Xb hf hHsXb hp hfr.1 hCrun hCband

/-- Under the bundle along `W`, if `GateOffFrameAtOn` at `Mh` holds along `W` from `c − 1` to
    `c + 1`, `lo ≤ S.a (c − 1)`, `S.a (c + 1)` is in the horizon, `v` is in the set for `S.a c`,
    `na` is a node state of its round-`c` action read along `W` holding the body `Cn`, a run block
    along `W` at height at least `Mh − 1` erasing to `C`, and the next opening proposer is in the
    set for its confirmation instant, then `C` is in the filtered block tree of the store that
    proposer's proposal duty reads along `W`. -/
theorem seedSourceCap_active_nextOpeningProposalOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {Mh : Height} {c : Round} (hc : 1 ≤ c)
    (hframe : Restated.GateOffFrameAtOn M S rho (fun t => W (strictEventIndex rho t)) Hs Mh
      (c - 1) (c + 1))
    (hpost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (c - 1)))
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S (c + 1)) ≤ rho.horizon)
    {v : V} (hv : v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S c))) {C : Block V}
    (na : M.N)
    (hna : na ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) v) c)
    (_hsource : Restated.Vocabulary.Internal.PhaseGrades.nodeFGSource M S na c ⇢ some C)
    {Cn : NamedBlock V} (hCbody : Cn ∈ na.st.bodies)
    (hCerase : Cn.erase = C) (hCrun : Restated.RunBlockOn M S rho W Xb Cn)
    (hCband : Mh - 1 ≤ (M.derive_named S.E S.cfg Cn).h)
    (hprop : S.E.proposer ((M.opening_slot S.hc (c + 1))) ∈
      Hs (M.confirmation_time S.E ((M.opening_slot S.hc (c + 1))))) :
    C ∈ M.get_filtered_block_tree
      (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.tickStore M S
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (c + 1))))
          (S.E.proposer (M.opening_slot S.hc (c + 1)))).st.core
        (M.proposal_time S.E (M.opening_slot S.hc (c + 1))))).toFG := by
  have hsb := hf.slashableBound
  have hpostC : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S c) :=
    hpost.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.sub_le c 1))
  have hdelay : (Restated.Vocabulary.Execution.Setup.a M S c) + S.E.Δ ≤
      M.proposal_time S.E ((M.opening_slot S.hc (c + 1))) :=
    Restated.Vocabulary.Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt facts S (Nat.lt_succ_self c)
  have hreadHi : M.proposal_time S.E ((M.opening_slot S.hc (c + 1))) ≤
      (Restated.Vocabulary.Execution.Setup.a M S (c + 1)) := by
    rw [Restated.a_eq_confirmation_opening_l58 facts S (c + 1)]
    exact facts.sch.proposal_time_le_confirmation_time S.E _
  have hreadHor := hreadHi.trans hhor
  have hpropRead : S.E.proposer ((M.opening_slot S.hc (c + 1))) ∈
      Hs (M.proposal_time S.E ((M.opening_slot S.hc (c + 1)))) :=
    hHs _ _ (Restated.nextOpening_instants_l70 facts S c).2 hprop
  have hpropRelay : S.E.proposer ((M.opening_slot S.hc (c + 1))) ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S c) + S.E.Δ) :=
    hHs _ _ hdelay hpropRead
  obtain ⟨hroot, hmax, hgate⟩ := Restated.seedSourceCap_nextProposal_frameOn facts S Hs Xb hf hHsXb hc
    hframe hpost hhor hCerase hCrun hCband hpropRead
  have hvis := Restated.actionConeWitness_visibleAtReader_after_gstOn facts S Hs Xb hf hHs hHsXb hv hpropRelay
    hna hCbody (by rw [hCerase]; exact Proofs.ModelProperties.Preceq_self C) hCband hpostC hdelay
    hreadHor hroot
  have hCT : C ∈ (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (c + 1))))
      (S.E.proposer (M.opening_slot S.hc (c + 1)))).st.T := by
    have hcoh := (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho
      (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (c + 1))))
      (S.E.proposer ((M.opening_slot S.hc (c + 1)))) _ (hf.onePath _).1).1.1.1
    have himage : Cn.erase ∈ (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (c + 1))))
        (S.E.proposer (M.opening_slot S.hc (c + 1)))).st.core.T := by
      rw [hcoh.1]
      exact Finset.mem_image.mpr ⟨Cn, hvis.1, rfl⟩
    rw [hCerase] at himage
    exact himage
  have hM : 1 ≤ Mh :=
    (Nat.succ_le_succ (Nat.zero_le 1)).trans
      ((Nat.le_add_left 2 _).trans hgate)
  have hfiltered := Restated.frontierBlock_filtered_of_gateOffOn facts S Hs Xb hf hsb (hHsXb _ hpropRead)
    hreadHor hCT hCerase hCrun hCband hM hmax hgate
  unfold Restated.Vocabulary.Proofs.Optimistic.tickStore
  show C ∈ M.get_filtered_block_tree (M.store_with_t_s _ _ _).toHealing.toFG
  rw [facts.fc.get_filtered_block_tree_set_clock_slot]
  exact hfiltered

/-- Under the bundle along `W` and the committee majority, if the votes of the set for the vote
    instant of `opening_slot c + 1` form, along `W`, a cone over `K` and a cone over `C`, then `K`
    and `C` are compatible. -/
theorem seedSourceCap_carrier_compatible_at_secondSlotOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    {c : Round} {K C : Block V}
    (hKcone : Restated.NamedHonestVotesConeOn M S rho W Hs Xb ((M.opening_slot S.hc c) + 1)
      (fun X => Block.Preceq K X))
    (hCcone : Restated.NamedHonestVotesConeOn M S rho W Hs Xb ((M.opening_slot S.hc c) + 1)
      (fun X => Block.Preceq C X)) :
    Block.compatible K C = true := by
  have hpositive : 0 < ((S.E.committee ((M.opening_slot S.hc c) + 1)) ∩
      Hs (M.confirmation_time S.E ((M.opening_slot S.hc c) + 1))).card := by
    have h := hcom ((M.opening_slot S.hc c) + 1)
    omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpositive
  have hxCommittee := (Finset.mem_inter.mp hx).1
  have hxHonest : x ∈ Hs (M.vote_time S.E ((M.opening_slot S.hc c) + 1)) :=
    hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E _) (Finset.mem_inter.mp hx).2
  obtain ⟨HK, hKHK, hHKrun, hKem⟩ := hKcone x hxHonest hxCommittee
  obtain ⟨HC, hCHC, hHCrun, hCem⟩ := hCcone x hxHonest hxCommittee
  have hemit := Restated.emits_gfVote_uniqueOn facts S Hs Xb hf hKem hCem rfl
  have hroot : HK.erase.root = HC.erase.root := congrArg GoldfishVote.head hemit
  have heq := Restated.runBlock_eq_of_root_eqOn facts W Xb hf.rootCollisionFree hHKrun hHCrun hroot
  rw [heq] at hKHK
  exact compatible_of_preceq_common_Preceq hKHK hCHC

/-- Under the bundle along `W`, the committee majority and the weight bound, if `GateOffFrameAtOn`
    at `Mh` holds along `W` from `c − 1` to `c + 1`, `lo ≤ S.a (c − 1)`, `S.a (c + 1)` is in the
    horizon, round `c` is ready, `v` in the set for `S.a c` has a node state `na` of its round-`c`
    action read along `W` whose FG source can be `C`, the erasure of a run block along `W` at height
    at least `Mh − 1`, the next opening proposer is in the set for its confirmation instant,
    `lo ≤ opening (c − η_SG)`, and the grade-2 awake hypotheses `hA` and `hAprev` hold, then every
    anchor the proposer's proposal read along `W` with the cache outcome `cp` can return is
    compatible with `C`. -/
theorem seedSourceCap_compatible_nextOpeningProposalAnchorOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hfb : BelowOneThirdOn S rho Hs)
    {Mh : Height} {c : Round} (hc : 1 ≤ c)
    (hframe : Restated.GateOffFrameAtOn M S rho (fun t => W (strictEventIndex rho t)) Hs Mh
      (c - 1) (c + 1))
    (hpost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (c - 1)))
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S (c + 1)) ≤ rho.horizon)
    (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho c)
    {v : V} (hv : v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S c))) {C : Block V}
    (na : M.N)
    (hna : na ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) v) c)
    (hsource : Restated.Vocabulary.Internal.PhaseGrades.nodeFGSource M S na c ⇢ some C)
    {Cn : NamedBlock V} (hCerase : Cn.erase = C) (hCrun : Restated.RunBlockOn M S rho W Xb Cn)
    (hCband : Mh - 1 ≤ (M.derive_named S.E S.cfg Cn).h)
    (hprop : S.E.proposer ((M.opening_slot S.hc (c + 1))) ∈
      Hs (M.confirmation_time S.E ((M.opening_slot S.hc (c + 1)))))
    (hloOpen : lo ≤ M.opening S.E S.hc (c - S.hc.η_SG))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k)
    (hAprev : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (c - 1)) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S (c - 1))) → M.awake_for_grade2 S u (W j u) (c - 1))
    (cp : M.Cache)
    (hcp : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (c + 1))))
        (S.E.proposer (M.opening_slot S.hc (c + 1)))).st.core.toHealing
      (M.proposal_time S.E (M.opening_slot S.hc (c + 1)))
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (c + 1))))
        (S.E.proposer (M.opening_slot S.hc (c + 1)))).cache ⇢ cp) :
    ∀ A0 : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S
        (M.mkNode (M.ns_setClock S.E
          (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (c + 1))))
            (S.E.proposer (M.opening_slot S.hc (c + 1)))).st
          (M.proposal_time S.E (M.opening_slot S.hc (c + 1))))
          (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (c + 1))))
            (S.E.proposer (M.opening_slot S.hc (c + 1)))).record cp)
        (M.round_of S.hc (M.mkNode (M.ns_setClock S.E
          (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (c + 1))))
            (S.E.proposer (M.opening_slot S.hc (c + 1)))).st
          (M.proposal_time S.E (M.opening_slot S.hc (c + 1))))
          (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (c + 1))))
            (S.E.proposer (M.opening_slot S.hc (c + 1)))).record cp).st.core.s) ⇢ A0 →
      Block.compatible A0 C = true := by
  intro A0 hA0
  have hround : M.round_of S.hc (M.opening_slot S.hc (c + 1)) = c + 1 :=
    facts.gr.round_of_opening_slot_eq_schedule S.hc (c + 1)
  have hopen : M.domain S.E S.hc (c + 1) .g1 =
      M.proposal_time S.E (M.opening_slot S.hc (c + 1)) := by
    rw [facts.gr.Sts_domain_g1_eq_opening, facts.gr.opening_eq_proposal_time]
  have hpropRead : S.E.proposer (M.opening_slot S.hc (c + 1)) ∈
      Hs (M.proposal_time S.E (M.opening_slot S.hc (c + 1))) :=
    hHs _ _ (Restated.nextOpening_instants_l70 facts S c).2 hprop
  have hproposalHor : M.proposal_time S.E (M.opening_slot S.hc (c + 1)) ≤ rho.horizon :=
    (facts.sch.proposal_time_le_confirmation_time S.E _).trans
      (by rw [← Restated.a_eq_confirmation_opening_l58 facts S (c + 1)]; exact hhor)
  have hroundTime : M.round_of S.hc (S.E.slotOf
      (M.proposal_time S.E (M.opening_slot S.hc (c + 1)))) = c + 1 := by
    rw [facts.sch.slotOf_proposal_time]
    exact hround
  have hdomainHor : M.domain S.E S.hc (c + 1) .g1 ≤ rho.horizon := by
    rw [hopen]
    exact hproposalHor
  obtain ⟨hrootW, -, -⟩ := Restated.seedSourceCap_nextProposal_frameOn facts S Hs Xb hf hHsXb hc
    hframe hpost hhor hCerase hCrun hCband hpropRead
  have hpostC : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S c) :=
    hpost.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.sub_le c 1))
  have hdelayP : (Restated.Vocabulary.Execution.Setup.a M S c) + S.E.Δ ≤
      M.proposal_time S.E (M.opening_slot S.hc (c + 1)) :=
    Restated.Vocabulary.Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt facts S
      (Nat.lt_succ_self c)
  have hdomainLo : (Restated.Vocabulary.Execution.Setup.a M S (c - 1)) ≤ M.domain S.E S.hc (c + 1) .g1 := by
    rw [hopen]
    exact (Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.sub_le c 1)).trans
      ((le_add_of_nonneg_right S.E.Δ_pos.le).trans hdelayP)
  have hdomainHi : M.domain S.E S.hc (c + 1) .g1 ≤ (Restated.Vocabulary.Execution.Setup.a M S (c + 1)) := by
    rw [hopen, Restated.a_eq_confirmation_opening_l58 facts S (c + 1)]
    exact facts.sch.proposal_time_le_confirmation_time S.E _
  set tp := M.proposal_time S.E (M.opening_slot S.hc (c + 1)) with htp
  set p := S.E.proposer (M.opening_slot S.hc (c + 1)) with hp
  set n := M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho tp) p).st tp)
    (W (strictEventIndex rho tp) p).record cp with hn
  have hcore : n.st = M.store_with_cache (M.ns_setClock S.E (W (strictEventIndex rho tp) p).st tp) cp := by
    rw [hn, facts.nd.mkNode_st]
  have hroundSt : M.round_of S.hc n.st.core.s = c + 1 := by
    rw [hcore]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    rw [facts.hd.Sts_setClock_core_s, htp, facts.sch.slotOf_proposal_time]
    exact hround
  have hnmem : n ∈ Restated.Vocabulary.Internal.NamedRecoveryRead.proposalDutyRead M S rho
      (M.opening_slot S.hc (c + 1)) :=
    ⟨W (strictEventIndex rho tp), mem_stateBeforeTime_along₇₀b facts hf tp, cp, hcp, rfl⟩
  have hrootC : Block.Preceq (M.get_fg_root (M.toHealing n.st.core).toFG) C := by
    rw [hcore]
    try simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    rw [setClock_fgRoot₇₀b facts S]
    exact hrootW
  rcases Restated.Vocabulary.Proofs.HealingSurface.proposalAnchor_cases facts S rho
      (M.opening_slot S.hc (c + 1)) n hnmem A0 hA0 with hfg | ⟨root, A, hframeA, hactive, hAA0⟩
  · rw [hfg]
    exact compatible_of_cases (Or.inl hrootC)
  rw [hAA0]
  rw [hroundSt] at hframeA
  obtain ⟨fr, hfr⟩ := facts.gr.freezeRoot_nonempty S.E
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc (c + 1) .g1)) p).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc (c + 1) .g1)) p).st.core.F
    S.hc.η_SG (c + 1) (M.early S.E S.hc (c + 1) .g1) (M.late S.E S.hc (c + 1) .g1)
  have hframeStore := Restated.preparedFrame_g1_eq_storeRoot_at_openingOn facts S rho Hs Xb
    hf p (c + 1) (Nat.succ_pos c) tp hpropRead hroundTime hopen hdomainHor cp hcp fr hfr
  have hfs := hframeA.symm.trans hframeStore
  rcases fr with _ | raw
  · cases hfs
  have hrootEq : root = M.clipGrade raw n.st.core.F := Option.some.inj (Option.some.inj hfs)
  have hAraw : Block.Preceq A raw := by
    have hLroot := facts.gr.preceq_of_activePrefix_eq_some hactive
    rw [hrootEq] at hLroot
    exact preceq_trans_Preceq hLroot (facts.gr.q10_clip_preceq raw _)
  obtain ⟨braw, hbraw⟩ := facts.gr.gradeBool_nonempty S.E
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc (c + 1) .g1)) p).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc (c + 1) .g1)) p).st.core.F
    S.hc.η_SG (c + 1) (M.early S.E S.hc (c + 1) .g1) (M.late S.E S.hc (c + 1) .g1) raw
  have hrawTrue := facts.gr.gradeBool_of_freezeRoot_eq_some (some raw) hfr rfl braw hbraw
  obtain ⟨gA, hgA⟩ := facts.gr.gradeBool_nonempty S.E
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc (c + 1) .g1)) p).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc (c + 1) .g1)) p).st.core.F
    S.hc.η_SG (c + 1) (M.early S.E S.hc (c + 1) .g1) (M.late S.E S.hc (c + 1) .g1) A
  have hgAtrue : gA = true :=
    facts.csAdded.confirmation_phaseGrade_mono S.E S.hc _ _ (c + 1) .g1 hAraw braw hbraw hrawTrue gA hgA
  subst hgAtrue
  have hprev : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (c + 1 - 1))),
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (c + 1 - 1))) u).st.h_max = Mh := by
    intro u hu
    rw [Nat.add_sub_cancel] at hu ⊢
    exact (hframe _ (Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.sub_le c 1))
      (Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.le_succ c)) u hu).2
  have hfrontier : ∀ w ∈ Hs (M.domain S.E S.hc (c + 1) .g1),
      (W (strictEventIndex rho (M.domain S.E S.hc (c + 1) .g1)) w).st.h_max = Mh := by
    intro w hw
    exact (hframe _ hdomainLo hdomainHi w hw).2
  have hgate : ∀ w ∈ Hs (M.domain S.E S.hc (c + 1) .g1),
      (W (strictEventIndex rho (M.domain S.E S.hc (c + 1) .g1)) w).st.h_j + 2 ≤ Mh := by
    intro w hw
    exact (hframe _ hdomainLo hdomainHi w hw).1
  have hAc := hA c (Restated.lo_le_early_g2_sub_delta_of_opening facts S hc hloOpen le_rfl)
  have hwindow0 := Restated.relativeCarrierWindowAt_of_gateOffOn facts S Hs Xb hf hHs hHsXb
    (r := c + 1) (p := .g1) (Nat.succ_pos c)
    (by rw [Nat.add_sub_cancel]; exact hpostC) hprev hfrontier hgate hdomainHor
    (by rw [Nat.add_sub_cancel]; exact hAc)
  have hwindow : Restated.RelativeCarrierWindowAtOn M S rho W
      (fun t => W (strictEventIndex rho t)) Hs c .g1 := by
    simpa only [Nat.add_sub_cancel] using hwindow0
  have hprevt : (Restated.Vocabulary.Execution.Setup.a M S (c + 1 - 1)) + S.E.Δ ≤ M.domain S.E S.hc (c + 1) .g1 := by
    rw [Nat.add_sub_cancel, hopen]
    exact hdelayP
  have hmajority : Restated.GradeFormingMajorityOn M S rho W Hs
      (Hs (M.domain S.E S.hc (c + 1) .g1)) (c + 1) :=
    Restated.gradeFormingMajority_of_admissible_belowOneThirdOn facts S Hs Xb hf hHs hfb
      (Nat.succ_pos c) hprevt hdomainHor
      (by simpa only [Nat.succ_sub_one, Nat.add_sub_cancel] using hpostC)
      (by simpa only [Nat.succ_sub_one, Nat.add_sub_cancel] using hAc)
  have hpropDom : p ∈ Hs (M.domain S.E S.hc (c + 1) .g1) := by
    rw [hopen]; exact hpropRead
  obtain ⟨u, huRound, hAK⟩ := Restated.relativeGrade_has_roundCarrierOn facts S Hs Xb
    (Hs (M.domain S.E S.hc (c + 1) .g1)) hf hHs hwindow hmajority (subset_refl _)
    hpropDom hgA
  have hu : u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S c)) :=
    ((Restated.honestRoundVoters_iffOn facts S rho W hf.onePath Hs u c).mp huRound).1
  obtain ⟨nr, hnr, g, hg, Bk, hBk⟩ := exists_actionSG₇₀b facts S
    (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) u) c
  have hABk : Block.Preceq A Bk := hAK nr hnr g hg Bk hBk
  have hdis := Restated.seedRoundDischarge_of_canonicityOn facts S Hs Xb hf hHs hHsXb hcom hfb hc
    hpost hhor hframe ready hloOpen hAprev
  have hCcone := Restated.freshFGSource_secondSlotConeOn facts S Hs Xb hf hHs hHsXb hcom hfb hc hframe
    hpost hhor ready (fun d hlod hhi w hw cw hcw =>
      Restated.voteDutyHead_band_at_dutyOn facts S Hs Xb hf hHs hHsXb hfb hc hframe hpost hhor hw hlod hhi
        (seedEntryRoundOf₇₀b facts S hlod hhi) hAprev cw hcw) hv na hna hsource ⟨Cn, hCerase, hCrun⟩
    hloOpen hAprev
  exact (ssc% seedSourceCap_compatible_ancestor_left) hABk
    (Restated.seedSourceCap_carrier_compatible_at_secondSlotOn facts S Hs Xb hf hHs hcom
      (hdis.claim1 u hu nr hnr g hg Bk hBk) hCcone)

/-- Under the premises of `seedSourceCap_compatible_nextOpeningProposalAnchorOn`, with `Cn` held at
    the node state `na` of `v`'s round-`c` action read along `W`, `C` is an ancestor of the parent
    of every proposal input the next opening proposer's read along `W` with the cache outcome `cp`
    can produce. -/
theorem seedSourceCap_preceq_nextOpeningParent_of_gateOffOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hfb : BelowOneThirdOn S rho Hs)
    {Mh : Height} {c : Round} (hc : 1 ≤ c)
    (hframe : Restated.GateOffFrameAtOn M S rho (fun t => W (strictEventIndex rho t)) Hs Mh
      (c - 1) (c + 1))
    (hpost : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (c - 1)))
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S (c + 1)) ≤ rho.horizon)
    (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho c)
    {v : V} (hv : v ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S c))) {C : Block V}
    (na : M.N)
    (hna : na ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) v) c)
    (hsource : Restated.Vocabulary.Internal.PhaseGrades.nodeFGSource M S na c ⇢ some C)
    {Cn : NamedBlock V} (hCbody : Cn ∈ na.st.bodies)
    (hCerase : Cn.erase = C) (hCrun : Restated.RunBlockOn M S rho W Xb Cn)
    (hCband : Mh - 1 ≤ (M.derive_named S.E S.cfg Cn).h)
    (hprop : S.E.proposer ((M.opening_slot S.hc (c + 1))) ∈
      Hs (M.confirmation_time S.E ((M.opening_slot S.hc (c + 1)))))
    (hloOpen : lo ≤ M.opening S.E S.hc (c - S.hc.η_SG))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k)
    (hAprev : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (c - 1)) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S (c - 1))) → M.awake_for_grade2 S u (W j u) (c - 1))
    (cp : M.Cache)
    (hcp : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (c + 1))))
        (S.E.proposer (M.opening_slot S.hc (c + 1)))).st.core.toHealing
      (M.proposal_time S.E (M.opening_slot S.hc (c + 1)))
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (c + 1))))
        (S.E.proposer (M.opening_slot S.hc (c + 1)))).cache ⇢ cp) :
    let n := M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (c + 1))))
          (S.E.proposer (M.opening_slot S.hc (c + 1)))).st
        (M.proposal_time S.E (M.opening_slot S.hc (c + 1))))
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc (c + 1))))
          (S.E.proposer (M.opening_slot S.hc (c + 1)))).record cp
    ∀ I : Protocol.ProposalInput V,
      Restated.Vocabulary.Protocol.proposal_input_with M (M.gradeContract n.cache) S.E S.hc
        (S.node (S.E.proposer (M.opening_slot S.hc (c + 1)))) (M.toHealing n.st.core) ⇢ I →
      Block.Preceq C I.parent := by
  intro n I hI
  obtain ⟨A0, hA0⟩ := nodeAnchor_nonempty₇₀b facts S n (M.round_of S.hc n.st.core.s)
  exact Restated.freshFGSource_preceq_nextOpeningParentOn facts S Hs Xb hf hHs hHsXb hcom hfb hc
    hframe hpost hhor ready hv na hna hsource hCerase hCrun hCband
    (hHs _ _ (Restated.nextOpening_instants_l70 facts S c).1 hprop)
    (Restated.seedSourceCap_active_nextOpeningProposalOn facts S Hs Xb hf hHs hHsXb hc hframe hpost hhor hv
      na hna hsource hCbody hCerase hCrun hCband hprop)
    hloOpen hAprev cp hcp A0 hA0
    (Restated.seedSourceCap_compatible_nextOpeningProposalAnchorOn facts S Hs Xb hf hHs hHsXb hcom hfb
      hc hframe hpost hhor ready hv na hna hsource hCerase hCrun hCband hprop hloOpen hA hAprev cp hcp A0
      hA0)
    I hI

/-- Under the bundle along `W`, the committee majority, the weight bound,
    `lo ≤ opening (r0 + 1 − η_SG)` and the grade-2 awake hypotheses `hA` and `hAr0`,
    `SeedPredPromotionInputsOn` holds from `r0` along `W`: every FG source a node state of the
    round-`(q' − 1)` action read of a member of the set for `S.a (q' − 1)` can return has height at
    most that of the parent of the next carrier opening proposal. -/
theorem seedPredPromotionInputs_of_publicOn (facts : Record.Facts M) {delayExtra : Nat}
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hfb : BelowOneThirdOn S rho Hs)
    (_hdelay : TimeoutDelayBound S delayExtra)
    {r0 gap : Round} {t₀ : Int} (_hrec : Restated.MultiProposerRecurrenceOn M S Hs gap t₀ rho.horizon)
    (hloOpen : lo ≤ M.opening S.E S.hc (r0 + 1 - S.hc.η_SG))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k)
    (hAr0 : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S r0) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S r0)) → M.awake_for_grade2 S u (W j u) r0) :
    Restated.SeedPredPromotionInputsOn M S rho W (fun t => W (strictEventIndex rho t)) Hs Xb r0
      delayExtra := by
  intro Mh q q' C C' B B' hM hgraded hcarrier hceiling hwindow hpred hspace hbase
    hcarrier' hceiling' hwindow' hpost hhor hframe hBrun hforms hretained
  refine { sourceHeightLeNextOpeningParent := ?_ }
  have hq2 : 2 ≤ q' :=
    (Nat.le_add_left 2 q).trans
      ((Nat.le_add_right (q + 2) delayExtra).trans hspace)
  have hcOne : 1 ≤ q' - 1 := by
    apply Nat.le_sub_of_add_le
    exact hq2
  have hcPred : (q' - 1) - 1 = q' - 2 := by
    rw [Nat.sub_sub]
  have hcSucc : (q' - 1) + 1 = q' := by
    exact Nat.sub_add_cancel (Nat.le_trans (by decide) hq2)
  have hpredSucc : q' - 2 + 1 = q' - 1 := by
    simpa only [hcPred] using Nat.sub_add_cancel hcOne
  have hloOpenQ : lo ≤ M.opening S.E S.hc (q' - 1 - S.hc.η_SG) :=
    hloOpen.trans (facts.gr.NamedOutageClosure_opening_mono S
      (Nat.sub_le_sub_right (seedPromotionBase_nat_l70 r0 q' hbase) _))
  have hloPred : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (q' - 2)) := by
    refine hloOpenQ.trans ((facts.gr.NamedOutageClosure_opening_mono S ?_).trans
      (by
        rw [facts.gr.opening_eq_proposal_time,
          Restated.a_eq_confirmation_opening_l58 facts S (q' - 2)]
        exact facts.sch.proposal_time_le_confirmation_time S.E _))
    rw [← hcPred]
    exact Nat.sub_le_sub_left S.hc.η_SG_ge_one (q' - 1)
  have hpostC : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S ((q' - 1) - 1)) := by
    simpa only [hcPred] using hloPred
  have hhorC : (Restated.Vocabulary.Execution.Setup.a M S ((q' - 1) + 1)) ≤ rho.horizon := by
    simpa only [hcSucc] using hhor
  have hcHor : (Restated.Vocabulary.Execution.Setup.a M S (q' - 1)) ≤ rho.horizon :=
    (Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.sub_le q' 1)).trans hhor
  have hready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho (q' - 1) := by
    constructor
    · have hlt : q' - 2 < q' - 1 := by
        rw [← hpredSucc]
        exact Nat.lt_succ_self _
      have hdeadline := facts.gr.action_delta_le_early S S.hc.R_ge_three hlt
      exact hpost.trans ((le_add_of_nonneg_right S.E.Δ_pos.le).trans hdeadline)
    · exact (facts.gr.domain_le_a S (q' - 1) .g0).trans hcHor
  have hframeC : Restated.GateOffFrameAtOn M S rho (fun t => W (strictEventIndex rho t)) Hs Mh
      ((q' - 1) - 1) ((q' - 1) + 1) := by
    intro read hlo hhi w hw
    rw [hcPred] at hlo
    rw [hcSucc] at hhi
    exact hframe read hlo hhi w hw
  obtain ⟨cq, hcq, hB'⟩ := hwindow'.proposal
  have hnmem : M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q')))
          (S.E.proposer (M.opening_slot S.hc q'))).st
        (M.proposal_time S.E (M.opening_slot S.hc q')))
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q')))
          (S.E.proposer (M.opening_slot S.hc q'))).record cq ∈
      Restated.Vocabulary.Statements.Instantiation.proposerReadAt M S rho (M.opening_slot S.hc q') :=
    ⟨W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q'))),
      mem_stateBeforeTime_along₇₀b facts hf _, cq, hcq, rfl⟩
  obtain ⟨I, hI⟩ := facts.dt.with_proposal_input_nonempty (M.gradeContract cq) S.E S.hc
    (S.node (S.E.proposer (M.opening_slot S.hc q')))
    (M.toHealing (M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q')))
          (S.E.proposer (M.opening_slot S.hc q'))).st
        (M.proposal_time S.E (M.opening_slot S.hc q')))
        (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc q')))
          (S.E.proposer (M.opening_slot S.hc q'))).record cq).st.core)
  obtain ⟨Parent, hParent?, hParentErase⟩ :=
    Restated.Vocabulary.Proofs.HealingSurface.proposedBlockAt_parent facts S rho
      (M.opening_slot S.hc q') _ hnmem
      (by rewrite [facts.nd.mkNode_cache, facts.nd.mkNode_st, facts.dt.proposal_with_store_with_cache]; exact hB') I
      (by rw [facts.nd.mkNode_cache]; exact hI)
  have hB'parent : B'.parent = Parent := by
    cases B' with
    | genesis => cases hParent?
    | node parent slot root votes support rows proposer =>
        rw [namedBlock_parent_node]
        exact Option.some.inj hParent?
  have hs'pos : 0 < (M.opening_slot S.hc q') := by
    exact facts.gr.opening_slot_pos_of_round_pos S.hc hwindow'.roundPositive
  have hproposalHor' : M.proposal_time S.E
      ((M.opening_slot S.hc q')) ≤ rho.horizon := by
    exact (facts.sch.proposal_time_le_confirmation_time S.E _).trans
      (by rw [Restated.confirmation_time_opening_slot facts S q']; exact hhor)
  have hprop' : S.E.proposer ((M.opening_slot S.hc q')) ∈
      Hs (M.confirmation_time S.E ((M.opening_slot S.hc q'))) := by
    simpa only [Nat.add_zero] using hcarrier' 0 (by decide)
  have hloProposal : lo ≤ M.proposal_time S.E ((M.opening_slot S.hc q')) := by
    refine hloPred.trans ((Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.sub_le_sub_left (by decide : 1 ≤ 2) q')).trans
      ((le_add_of_nonneg_right S.E.Δ_pos.le).trans ?_))
    have h := Restated.Vocabulary.Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt facts S
      (show q' - 1 < q' from Nat.sub_lt ((Nat.le_trans (by decide) hq2)) Nat.one_pos)
    exact h
  have hrunP' : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick (S.E.proposer (M.opening_slot S.hc q'))
      (M.proposal_time S.E (M.opening_slot S.hc q'))) →
      M.awake_for_grade1 S (S.E.proposer (M.opening_slot S.hc q'))
        (W j (S.E.proposer (M.opening_slot S.hc q'))) (M.round_of S.hc (M.opening_slot S.hc q')) := by
    have hwin : lo ≤ M.early S.E S.hc (M.round_of S.hc (M.opening_slot S.hc q')) .g1 - S.E.Δ := by
      rw [facts.gr.round_of_opening_slot_eq S.hc q']
      have h1 := Restated.lo_le_early_g2_sub_delta_of_action_lt facts S hloPred
        (Nat.sub_lt (Nat.le_trans (by decide) hq2) (by decide : 0 < 2))
      have h2 := facts.gr.q10_early_g2_le_early_g1 S q'
      linarith
    intro j hj
    exact hf.awake_g1 _ _ j _ (Or.inl rfl) hj
      (hHs _ _ (facts.sch.proposal_time_le_confirmation_time S.E _) hprop') hwin
  have hB'run : Restated.RunBlockOn M S rho W Xb B' :=
    Restated.proposedBlockAt_blockInRun_of_admissibleOn facts S Hs Xb hf hHs hHsXb
      ((M.opening_slot S.hc q')) hs'pos hprop' hproposalHor' hloProposal
      (fun j hj => hf.tick_outcome j _ _ hj) hrunP' cq hcq hB'
  have hParentRun : Restated.RunBlockOn M S rho W Xb B'.parent := by
    exact Restated.blockInRun_of_ancestorOn facts S rho W Xb hB'run
      (by simpa only [hB'parent] using
        ((ssc% seedSourceCap_namedParent_preceq) B'))
  intro v hv n hn Q hsource
  obtain ⟨D, hDbody, hDerase, hDrun, hσ⟩ :=
    Restated.seedFresh_namedSource_witnessOn facts S Hs Xb hf (hHsXb _ hv) n hn hsource
  have hvDom : v ∈ Hs (M.domain S.E S.hc (q' - 1) .g0) :=
    hHs _ _ (facts.gr.domain_le_a S (q' - 1) .g0) hv
  have hvG2 : v ∈ Hs (M.domain S.E S.hc (q' - 1) .g2) :=
    hHs _ _ (facts.gr.domain_le_domain_g0 S (q' - 1) .g2) hvDom
  have hwmem := mem_stateBeforeTime_along₇₀b facts hf
    (Restated.Vocabulary.Execution.Setup.a M S (q' - 1))
  have hactive : B.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M n :=
    Restated.Vocabulary.Proofs.HealingSurface.activeAtAction_of_retainedAtRead facts S (v := v)
      _ hwmem (hretained v hv) n hn
  obtain ⟨b, hb⟩ := facts.gr.gradeBool_nonempty S.E
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc (q' - 1) .g2)) v).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc (q' - 1) .g2)) v).st.core.F S.hc.η_SG (q' - 1)
    (M.early S.E S.hc (q' - 1) .g2) (M.late S.E S.hc (q' - 1) .g2) B.erase
  have hbtrue : b = true := (hforms v hvG2).2 b hb
  subst hbtrue
  obtain ⟨G, hG⟩ := facts.gr.read_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) (q' - 1)
  have hGq : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n (q' - 1) ⇢ G.Q2 :=
    nodeQ2_of_read₇₀b S n (q' - 1) G hG
  obtain ⟨Q2, hQ2, hCQ2⟩ :=
    Restated.preceq_actionQ2_of_domainGradeOn facts S Hs Xb hf hHs (Nat.succ_le_iff.mp hcOne)
      hcHor hvDom hloOpenQ (hforms v hvG2).1 hb n hn hactive _ hGq
  rw [hQ2] at hGq
  have hBQ : Block.Preceq B.erase Q :=
    Restated.Vocabulary.Proofs.HealingSurface.preceq_actionFGSource_of_actionQ2 facts S rho v (q' - 1) _
      hwmem n hn hGq hCQ2 hsource
  have hBDerase : Block.Preceq B.erase D.erase := by
    rw [hDerase]
    exact hBQ
  have hBD : NamedBlock.Preceq B D :=
    Restated.namedPreceq_of_runBlock_erase_preceqOn facts Hs Xb hf hBrun hDrun hBDerase
  have hDband : Mh - 1 ≤ (M.derive_named S.E S.cfg D).h := by
    have hmono := facts.cs.derive_height_mono S.E S.cfg hBD
    rw [hpred] at hmono
    exact hmono
  have hprop'' : S.E.proposer (M.opening_slot S.hc ((q' - 1) + 1)) ∈
      Hs (M.confirmation_time S.E (M.opening_slot S.hc ((q' - 1) + 1))) := by
    rw [hcSucc]; exact hprop'
  have hcq' : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc ((q' - 1) + 1))))
        (S.E.proposer (M.opening_slot S.hc ((q' - 1) + 1)))).st.core.toHealing
      (M.proposal_time S.E (M.opening_slot S.hc ((q' - 1) + 1)))
      (W (strictEventIndex rho (M.proposal_time S.E (M.opening_slot S.hc ((q' - 1) + 1))))
        (S.E.proposer (M.opening_slot S.hc ((q' - 1) + 1)))).cache ⇢ cq := by
    rw [hcSucc]; exact hcq
  have hAprevC : ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S (q' - 1 - 1)) + S.E.Δ),
      ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u
        (Restated.Vocabulary.Execution.Setup.a M S (q' - 1 - 1))) →
      M.awake_for_grade2 S u (W j u) (q' - 1 - 1) := by
    rw [hcPred]
    rcases eq_or_lt_of_le (Nat.le_sub_of_add_le hbase) with hb | hb
    · rw [← hb]
      exact hAr0
    · exact hA (q' - 2)
        (Restated.lo_le_early_g2_sub_delta_of_opening facts S (Nat.succ_pos r0) hloOpen hb)
  have hsourceParent := Restated.seedSourceCap_preceq_nextOpeningParent_of_gateOffOn facts
    S Hs Xb hf hHs hHsXb hcom hfb hcOne hframeC hpostC hhorC hready hv n hn hsource hDbody
      hDerase hDrun hDband hprop'' hloOpenQ hA hAprevC cq hcq'
  simp only [hcSucc] at hsourceParent
  have hsourceParent' : Block.Preceq Q I.parent :=
    hsourceParent I (by rw [facts.nd.mkNode_cache]; exact hI)
  have hDParentErase : Block.Preceq D.erase B'.parent.erase := by
    rw [hDerase, hB'parent, hParentErase]
    exact hsourceParent'
  have hDParent : NamedBlock.Preceq D B'.parent :=
    Restated.namedPreceq_of_runBlock_erase_preceqOn facts Hs Xb hf hDrun hParentRun
      hDParentErase
  have hσheight :
      ((M.toHealing n.st.core).σ Q).h =
        (M.derive_named S.E S.cfg D).h :=
    congrArg (fun X : M.CS => X.h) hσ
  calc
    ((M.toHealing n.st.core).σ Q).h =
        (M.derive_named S.E S.cfg D).h := hσheight
    _ ≤ (M.derive_named S.E S.cfg B'.parent).h :=
      facts.cs.derive_height_mono S.E S.cfg hDParent

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel.Proofs.Optimistic
local macro "hnd% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.ChainState.HeightRegimeNamedBaseDeadline)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- Under the bundle along `W`, two run blocks `A` and `B` along `W` read through `Xb`, each its own
    height entry, at the same height and with compatible erasures, are equal. -/
theorem namedEntries_eq_of_compatible_deadlineOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {A B : NamedBlock V} (hArun : Restated.RunBlockOn M S rho W Xb A)
    (hBrun : Restated.RunBlockOn M S rho W Xb B)
    (hAself : (M.derive_named S.E S.cfg A).T_h = A.erase)
    (hBself : (M.derive_named S.E S.cfg B).T_h = B.erase)
    (hh : (M.derive_named S.E S.cfg A).h =
      (M.derive_named S.E S.cfg B).h)
    (hcompat : Block.compatible A.erase B.erase = true) : A = B := by
  have hlinear : Block.Preceq A.erase B.erase ∨
      Block.Preceq B.erase A.erase :=
    compatible_cases hcompat
  rcases hlinear with hAB | hBA
  · have hABn := Restated.namedPreceq_of_runBlock_erase_preceqOn facts Hs Xb hf hArun hBrun hAB
    have hentry := facts.cs.entry_eq_on_plateau
      S.E S.cfg hABn hh
    have herase : A.erase = B.erase := hAself.symm.trans (hentry.trans hBself)
    exact hf.rootCollisionFree.root_injective A B hArun hBrun A B
      (Or.inl ((hnd% named_preceq_self_deadline) A))
      (Or.inr ((hnd% named_preceq_self_deadline) B))
      (by rw [← Proofs.NamedWire.erase_root A, ← Proofs.NamedWire.erase_root B, herase])
  · have hBAn := Restated.namedPreceq_of_runBlock_erase_preceqOn facts Hs Xb hf hBrun hArun hBA
    have hentry := facts.cs.entry_eq_on_plateau
      S.E S.cfg hBAn hh.symm
    have herase : B.erase = A.erase := hBself.symm.trans (hentry.trans hAself)
    exact (hf.rootCollisionFree.root_injective B A hBrun hArun B A
      (Or.inl ((hnd% named_preceq_self_deadline) B))
      (Or.inr ((hnd% named_preceq_self_deadline) A))
      (by rw [← Proofs.NamedWire.erase_root B, ← Proofs.NamedWire.erase_root A,
        herase])).symm

/-- Under the bundle and the slashable bound along `W`, if `C`, `BF` and `F` are run blocks along
    `W` through `Xb`, `F` is the self-entry of `BF`'s finalized block at `BF`'s finalized height,
    and `C`'s justified height is that height, then `C`'s justified block is `F`. -/
theorem namedJustified_eq_finalized_deadlineOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hsb : Restated.SlashableBoundOn M S rho W Xb)
    {C BF F : NamedBlock V} (hCrun : Restated.RunBlockOn M S rho W Xb C)
    (hBFrun : Restated.RunBlockOn M S rho W Xb BF) (hFrun : Restated.RunBlockOn M S rho W Xb F)
    (_hFpre : NamedBlock.Preceq F BF)
    (hFerase : F.erase = (M.derive_named S.E S.cfg BF).F)
    (hFheight : (M.derive_named S.E S.cfg F).h =
      (M.derive_named S.E S.cfg BF).h_F)
    (hFself : (M.derive_named S.E S.cfg F).T_h = F.erase)
    (hJheight : (M.derive_named S.E S.cfg C).h_j =
      (M.derive_named S.E S.cfg BF).h_F) :
    (M.derive_named S.E S.cfg C).J = F.erase := by
  have hJpos : 0 < (M.derive_named S.E S.cfg C).h_j := by
    rw [hJheight, ← hFheight]
    exact facts.cs.one_le_derive_named_h S.E S.cfg F
  obtain ⟨J, hJC, hJerase, hJheight', hJself⟩ :=
    Restated.Vocabulary.Proofs.NamedCheckpointAlgebra.namedJustification_selfTarget facts
      S.E S.cfg C hJpos
  have hlt : (M.derive_named S.E S.cfg BF).h_F <
      (M.derive_named S.E S.cfg C).h := by
    rw [← hJheight]
    exact ((facts.cs.chainOrder_derive_named S.E S.cfg C)).justified_below_height
  have hFCraw : Block.Preceq F.erase C.erase := by
    simpa only [hFerase] using
      (Restated.finalized_preceq_of_height_ltOn facts S rho W Xb C BF hsb hf.rootCollisionFree hCrun hBFrun hlt)
  have hFC : NamedBlock.Preceq F C :=
    Restated.namedPreceq_of_runBlock_erase_preceqOn facts Hs Xb hf hFrun hCrun hFCraw
  rcases (hnd% named_preceq_or_preceq_common_deadline) hJC hFC with hJF | hFJ
  · have hentry := facts.cs.entry_eq_on_plateau S.E S.cfg hJF
      (hJheight'.trans (hFheight.trans hJheight.symm).symm)
    have herase : J.erase = F.erase := hJself.symm.trans (hentry.trans hFself)
    exact hJerase.symm.trans herase
  · have hentry := facts.cs.entry_eq_on_plateau S.E S.cfg hFJ
      (hFheight.trans (hJheight.symm.trans hJheight'.symm))
    have herase : F.erase = J.erase := hFself.symm.trans (hentry.trans hJself)
    exact hJerase.symm.trans herase.symm

/-- If `X` is nonempty, in every world after the first `n` events some member `v` of `X` holds a
    body `B` whose finalized height is the largest, in that world, over the bodies of the members of
    `X`. -/
theorem exists_named_finalizedAt_recoveryPrefixFinalityHeightOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (X : Finset V) (n : Nat)
    (hne : X.Nonempty) :
    ∀ w ∈ Record.stateBeforeOf M S rho n,
    ∃ v ∈ X, ∃ B ∈ (w v).st.bodies,
      (M.derive_named S.E S.cfg B).h_F =
        X.sup fun u => (w u).st.bodies.sup fun C => (M.derive_named S.E S.cfg C).h_F := by
  classical
  intro w hw
  obtain ⟨v, hv, hsup⟩ := Finset.exists_mem_eq_sup X hne
    (fun u => (w u).st.bodies.sup
      (fun B => (M.derive_named S.E S.cfg B).h_F))
  have hgen : (NamedBlock.genesis : NamedBlock V) ∈ (w v).st.bodies :=
    ((Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho n v w hw).1.1.1.2.2.1).1
  obtain ⟨B, hB, hBsup⟩ := Finset.exists_mem_eq_sup
    (w v).st.bodies ⟨_, hgen⟩
    (fun B => (M.derive_named S.E S.cfg B).h_F)
  refine ⟨v, hv, B, hB, ?_⟩
  rw [hsup, hBsup]

/-- If in the worlds `Wi` the largest `h_max` over the family rises within every `lag` rounds from
    `r0`, then for every `k` with `S.a (r0 + k · lag)` in the horizon, the largest `h_max` in `Wi`
    over the set for `S.a (r0 + k · lag)` is at least that over the set for `S.a r0` plus `k`. -/
theorem honestHMaxAt_add_le_of_eventualHeightProgress_namedDeadlineOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) {r0 lag : Round} {Wi : Time → V → M.N}
    (h : 0 < lag ∧ ∀ r : Round, r0 ≤ r →
      (Restated.Vocabulary.Execution.Setup.a M S (r + lag)) ≤ rho.horizon →
      ((Hs (Restated.Vocabulary.Execution.Setup.a M S r)).sup fun u =>
          (Wi (Restated.Vocabulary.Execution.Setup.a M S r) u).st.core.h_max) <
        (Hs (Restated.Vocabulary.Execution.Setup.a M S (r + lag))).sup fun u =>
          (Wi (Restated.Vocabulary.Execution.Setup.a M S (r + lag)) u).st.core.h_max) (k : Nat)
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S (r0 + k * lag)) ≤ rho.horizon) :
    ((Hs (Restated.Vocabulary.Execution.Setup.a M S r0)).sup fun u =>
        (Wi (Restated.Vocabulary.Execution.Setup.a M S r0) u).st.core.h_max) + k ≤
      (Hs (Restated.Vocabulary.Execution.Setup.a M S (r0 + k * lag))).sup fun u =>
        (Wi (Restated.Vocabulary.Execution.Setup.a M S (r0 + k * lag)) u).st.core.h_max := by
  induction k with
  | zero => simp
  | succ k ih =>
      have e : r0 + (k + 1) * lag = r0 + k * lag + lag := by
        rw [Nat.add_mul, Nat.one_mul, Nat.add_assoc]
      have hle : r0 + k * lag ≤ r0 + (k + 1) * lag := by
        rw [e]
        exact Nat.le_add_right _ _
      have hhor' : (Restated.Vocabulary.Execution.Setup.a M S (r0 + k * lag)) ≤ rho.horizon :=
        (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hle).trans hhor
      rw [e] at hhor ⊢
      have hstep := h.2 (r0 + k * lag) (Nat.le_add_right r0 _) hhor
      have hk := ih hhor'
      exact Nat.succ_le_of_lt (lt_of_le_of_lt hk hstep)

/-- Under the bundle along `W`, if along `W` the largest `h_max` over the family rises within every
    `lag` rounds from `r0`, then for every `k` with `S.a (r0 + k · lag)` in the horizon, the largest
    `h_max` over the set for `S.a (r0 + k · lag)` in the world of `W` at its inclusive index is at
    least the largest `h_max` over the set for `S.a r0` in the world of `W` at its inclusive index
    plus `k`. -/
theorem honestHMaxBeforeIndex_ge_of_eventualHeightProgress_namedDeadlineOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {r0 lag : Round}
    (h : 0 < lag ∧ ∀ r : Round, r0 ≤ r →
      (Restated.Vocabulary.Execution.Setup.a M S (r + lag)) ≤ rho.horizon →
      ((Hs (Restated.Vocabulary.Execution.Setup.a M S r)).sup fun u =>
          (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) u).st.core.h_max) <
        (Hs (Restated.Vocabulary.Execution.Setup.a M S (r + lag))).sup fun u =>
          (W (inclusiveEventIndex rho
            (Restated.Vocabulary.Execution.Setup.a M S (r + lag))) u).st.core.h_max)
    (k : Nat) (hhor : (Restated.Vocabulary.Execution.Setup.a M S (r0 + k * lag)) ≤ rho.horizon) :
    ((Hs (Restated.Vocabulary.Execution.Setup.a M S r0)).sup fun v =>
        (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r0)) v).st.h_max) + k ≤
      (Hs (Restated.Vocabulary.Execution.Setup.a M S (r0 + k * lag))).sup fun v =>
        (W (inclusiveEventIndex rho
          (Restated.Vocabulary.Execution.Setup.a M S (r0 + k * lag))) v).st.h_max :=
  Restated.honestHMaxAt_add_le_of_eventualHeightProgress_namedDeadlineOn facts S Hs
    (Wi := fun t => W (inclusiveEventIndex rho t)) h k hhor

/-- Under the bundle along `W` and the weight majority, if `t + 1` is in the horizon, then for every
    set `X`, the largest `h_max` over `X` in the world of `W` at `t`'s inclusive index is at most
    the largest `h_max` over the set for `t` in that world plus one. -/
theorem honestHMaxBeforeIndexOn_inclusive_le_succ_l70 (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb X : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hmajority : HonestWeightMajorityOn S rho Hs)
    {t : Time} (hthor : t + 1 ≤ rho.horizon) :
    (X.sup fun v => (W (inclusiveEventIndex rho t) v).st.h_max) ≤
      ((Hs t).sup fun v => (W (inclusiveEventIndex rho t) v).st.h_max) + 1 := by
  apply Finset.sup_le
  intro v _hv
  rw [inclusiveEventIndex_eq_strict_succ₇₀b rho t]
  by_cases hlarge : 1 < (W (strictEventIndex rho (t + 1)) v).st.h_max
  · obtain ⟨b, tb, hb, hemit, ht, hrow, -⟩ :=
      Restated.frontier_confirmationWitnessOn facts S Hs Xb hf hHs hHsXb hmajority hthor hlarge
    have hbt : b.val_index ∈ Hs t := hHs _ _ (by linarith) hb
    have htb : tb ≤ t := Int.lt_add_one_iff.mp ht
    have hband := Restated.honestEmittedHeight_le_honestHMaxBeforeTimeOn facts
      S Hs Xb (Hs t) hf hbt hemit hrow htb
    have hle : strictEventIndex rho t ≤ strictEventIndex rho (t + 1) := by
      rw [← inclusiveEventIndex_eq_strict_succ₇₀b rho t]
      exact strictEventIndex_le_inclusiveEventIndex rho t
    have hmono : ((Hs t).sup fun x => (W (strictEventIndex rho t) x).st.h_max) ≤
        (Hs t).sup fun x => (W (strictEventIndex rho (t + 1)) x).st.h_max :=
      Restated.honestHMaxBeforeIndex_monoOn facts S rho (Hs t) hle _ (hf.onePath _).1 _
        (onePath_slice₇₀b W hf.onePath hle)
    calc (W (strictEventIndex rho (t + 1)) v).st.h_max
        = ((W (strictEventIndex rho (t + 1)) v).st.core.h_max - 1) + 1 :=
          (Nat.sub_add_cancel (Nat.le_of_lt hlarge)).symm
      _ ≤ ((Hs t).sup fun x => (W (strictEventIndex rho t) x).st.h_max) + 1 :=
          Nat.add_le_add_right hband 1
      _ ≤ _ := Nat.add_le_add_right hmono 1
  · have h1 : (W (strictEventIndex rho (t + 1)) v).st.h_max ≤ 1 := Nat.le_of_not_gt hlarge
    exact h1.trans (Nat.le_add_left 1 _)

/-- Under the bundle along `W`, with `X` inside `Xb` and every set of the family from instant `0` on
    inside `X`, if the largest `h_max` over `X` in the world `W stop` is less than `blocked + 2`,
    `BF` is a run block along `W` with finalized height `blocked` and `F` its finalized block's
    self-entry at height `blocked`, then the named frame over `X` along `W` holds at `blocked` up to
    `stop` with previous root `F`, for every round `c0`. -/
theorem namedHeightRegimeFrame_of_finalizedRunOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb X : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo) (hXXb : X ⊆ Xb)
    (hX : ∀ t : Int, 0 ≤ t → Hs t ⊆ X)
    {stop : Nat} {blocked : Height} {c0 : Round}
    (hfrontier : (X.sup fun u => (W stop u).st.core.h_max) < blocked + 2)
    {BF F : NamedBlock V} (hBFrun : Restated.RunBlockOn M S rho W Xb BF)
    (hFpre : NamedBlock.Preceq F BF)
    (hFerase : F.erase = (M.derive_named S.E S.cfg BF).F)
    (hFheight : (M.derive_named S.E S.cfg F).h = blocked)
    (hBFheight : (M.derive_named S.E S.cfg BF).h_F = blocked)
    (hFself : (M.derive_named S.E S.cfg F).T_h = F.erase) :
    Restated.NamedHeightRegimeFrameOn M S rho W (fun t => W (strictEventIndex rho t)) Hs X Xb
      blocked stop F c0 := by
  have hsb : Restated.SlashableBoundOn M S rho W Xb := hf.slashableBound
  have hFrun : Restated.RunBlockOn M S rho W Xb F :=
    Restated.blockInRun_of_ancestorOn facts S rho W Xb hBFrun hFpre
  have hFT : ∀ v ∈ X, ∀ n : Nat, n ≤ stop →
      Block.Preceq (W n v).st.core.F F.erase := by
    intro v hv n hn
    have hmem : W n ∈ Record.stateBeforeOf M S rho n := (hf.onePath n).1
    obtain ⟨C, hCmem, hCF, hCFbelow⟩ :=
      Restated.Vocabulary.Proofs.Bridges.storeFinalizationOnChain_stateBefore facts S rho n v
        (W n) hmem
    have hCrun : Restated.RunBlockOn M S rho W Xb C :=
      Restated.runBlock_of_stateBefore_memOn facts S W Xb (hXXb hv) hCmem
    have hmax : (W n v).st.core.h_max ≤ blocked + 1 :=
      (Restated.localHMax_le_honestHMaxBeforeIndexOn facts S rho X n hv (W n) hmem).trans
        ((Restated.honestHMaxBeforeIndex_monoOn facts S rho X hn (W n) hmem (W stop)
          (onePath_slice₇₀b W hf.onePath hn)).trans (Nat.le_of_lt_succ hfrontier))
    have hCle : (M.derive_named S.E S.cfg C).h_F ≤ blocked :=
      Nat.le_of_lt_succ (hCFbelow.trans_le hmax)
    by_cases hCzero : (M.derive_named S.E S.cfg C).h_F = 0
    · have hgen : (W n v).st.core.F = Block.genesis := by
        rw [← hCF]
        exact facts.cs.finalized_zero_is_genesis S.E S.cfg C hCzero
      rw [hgen]
      exact preceq_eq_true_iff_Preceq.mp (Protocol.preceq_genesis F.erase)
    · obtain ⟨FC, hFC, hFCerase, hFCheight, hFCself⟩ :=
        (facts.csAdded.finalized_is_entry S.E S.cfg C).resolve_left hCzero
      have hFCrun : Restated.RunBlockOn M S rho W Xb FC :=
        Restated.blockInRun_of_ancestorOn facts S rho W Xb hCrun hFC
      have hcompat := Restated.finalized_compatibleOn facts
        S rho W Xb C BF hsb hf.rootCollisionFree hCrun hBFrun
      have hfinalCompat : Block.compatible FC.erase F.erase = true := by
        simpa only [hFCerase, hFerase] using hcompat
      rcases Nat.lt_or_eq_of_le hCle with hClt | hCeq
      · have hpre := Restated.finalized_preceq_of_height_ltOn facts
          S rho W Xb F C hsb hf.rootCollisionFree hFrun hCrun
          (by rw [hFheight]; exact hClt)
        simpa only [hCF, hFCerase] using hpre
      · have hFCeqF := Restated.namedEntries_eq_of_compatible_deadlineOn facts S Hs Xb hf
          hFCrun hFrun hFCself hFself
          (hFCheight.trans (hCeq.trans hFheight.symm)) hfinalCompat
        rw [← hCF, ← hFCerase, hFCeqF]
        exact Proofs.ModelProperties.Preceq_self F.erase
  refine ⟨?_, hFrun, hFheight.le, ?_, ?_⟩
  · intro v hv n hn Y hYrun hYheight hFY
    exact preceq_trans_Preceq (hFT v hv n hn)
      (Proofs.NamedWire.erase_preceq hFY)
  · intro v hv n hn Q hQmem hQheight hFQ
    have hmem : W n ∈ Record.stateBeforeOf M S rho n := (hf.onePath n).1
    have hcoh := (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho n v
      (W n) hmem).1.1.1
    have hQraw : Q.erase ∈ (W n v).st.core.T := by
      rw [hcoh.1]
      exact Finset.mem_image_of_mem NamedBlock.erase hQmem
    have hview := Restated.Vocabulary.Proofs.NamedStoreBridge.derivedView_stateBefore facts S rho n v
      (W n) hmem Q hQmem
    have hQstored : ((W n v).st.core.σ Q.erase).h = blocked + 1 := by
      rw [hview, hQheight]
    have hmax : (W n v).st.core.h_max = blocked + 1 :=
      Restated.localHMax_eq_blocked_succ_of_rawMem_of_prefixFrontierOn facts
        S Hs Xb X hf hfrontier hv hn hQraw hQstored
    by_cases hgate : (W n v).st.core.h_max = (W n v).st.core.h_j + 1
    · obtain ⟨C, hCmem, hCJ, hChj⟩ :=
        Restated.Vocabulary.Proofs.Bridges.storeJustificationOnChain_stateBefore facts S rho n v
          (W n) hmem
      have hCrun : Restated.RunBlockOn M S rho W Xb C :=
        Restated.runBlock_of_stateBefore_memOn facts S W Xb (hXXb hv) hCmem
      have hjeq : (M.derive_named S.E S.cfg C).h_j = blocked := by
        rw [hChj]
        exact (Nat.add_right_cancel (hmax.symm.trans hgate)).symm
      have hJF := Restated.namedJustified_eq_finalized_deadlineOn facts S Hs Xb hf hsb
        hCrun hBFrun hFrun hFpre hFerase
        (hFheight.trans hBFheight.symm) hFself
        (hjeq.trans hBFheight.symm)
      rw [facts.fc.get_fg_root_toHealing_of_eq _ hgate]
      rw [← hCJ, hJF]
      exact Proofs.NamedWire.erase_preceq hFQ
    · rw [facts.fc.get_fg_root_toHealing_of_ne _ hgate]
      exact preceq_trans_Preceq (hFT v hv n hn)
        (Proofs.NamedWire.erase_preceq hFQ)
  · intro p r hp _hr _hhor n hn B hBmem hsource hBheight
    have hBrun : Restated.RunBlockOn M S rho W Xb B := by
      rw [actionReadFrom_bodies₇₀b facts S _ r n hn] at hBmem
      exact Restated.runBlock_of_stateBefore_memOn facts S W Xb
        (hXXb (hX _ (Restated.action_pos facts S r).le hp)) hBmem
    have hraw := Restated.finalized_preceq_of_height_ltOn facts
      S rho W Xb B BF hsb hf.rootCollisionFree hBrun hBFrun
      (by rw [hBFheight, hBheight]; exact Nat.lt_succ_self blocked)
    exact Restated.namedPreceq_of_runBlock_erase_preceqOn facts Hs Xb hf hFrun hBrun
      (by simpa only [hFerase] using hraw)

/-- Under the bundle along `W`, with `X` inside `Xb` weighing more than two thirds and every set of
    the family from instant `0` on inside `X`, if the first height crossing over `X` to
    `blocked + 1` along `W` is at `first`, the largest `h_max` over `X` in the world
    `W (inclusiveEventIndex rho (S.a r0))` is less than `blocked`, and `F` is the self-entry at
    height `blocked` of the finalized block of a run block `BF` along `W` with finalized height
    `blocked`, then the run-scoped named base along `W` holds at `r0`, `blocked` and `first` with
    previous root `F`. -/
theorem namedHeightRegimeBaseRun_of_finalizedOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb X : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo) (hXXb : X ⊆ Xb)
    (hX : ∀ t : Int, 0 ≤ t → Hs t ⊆ X)
    (hbelow : Execution.BelowOneThird S X)
    {r0 : Round} {first : Nat} {blocked : Height}
    (hfirst : Restated.FirstHeightProgressAtOn M S rho W X (blocked + 1) first)
    (hstart : (X.sup fun v =>
      (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r0)) v).st.h_max) <
        blocked)
    {BF F : NamedBlock V} (hBFrun : Restated.RunBlockOn M S rho W Xb BF)
    (hFpre : NamedBlock.Preceq F BF)
    (hFerase : F.erase = (M.derive_named S.E S.cfg BF).F)
    (hFheight : (M.derive_named S.E S.cfg F).h = blocked)
    (hBFheight : (M.derive_named S.E S.cfg BF).h_F = blocked)
    (hFself : (M.derive_named S.E S.cfg F).T_h = F.erase) :
    Restated.NamedHeightRegimeBaseRunOn M S rho W (fun t => W (strictEventIndex rho t)) Hs X Xb
      r0 blocked first F := by
  have hsb : Restated.SlashableBoundOn M S rho W Xb := hf.slashableBound
  have hFrun : Restated.RunBlockOn M S rho W Xb F :=
    Restated.blockInRun_of_ancestorOn facts S rho W Xb hBFrun hFpre
  obtain ⟨v, hv⟩ : X.Nonempty := by
    by_contra hempty
    have hm := AlignedRoundLemmas.honestWeightMajority_of_belowOneThird hbelow
    rw [HonestWeightMajority, Finset.not_nonempty_iff_eq_empty.mp hempty, weightOf_empty] at hm
    exact absurd hm (Nat.not_lt_zero _)
  have hone : 1 ≤ (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r0)) v).st.core.h_max :=
    Nat.succ_le_of_lt ((Nat.zero_le _).trans_lt
      (Restated.Vocabulary.Proofs.NamedJustificationBound.justificationBelowMax_stateBefore facts
        S rho _ v _ (hf.onePath _).1))
  have htwo : 2 ≤ blocked := Nat.succ_le_of_lt
    ((hone.trans (Finset.le_sup
      (f := fun u => (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r0)) u).st.h_max)
      hv)).trans_lt hstart)
  have hgenRun : Restated.RunBlockOn M S rho W Xb (NamedBlock.genesis : NamedBlock V) :=
    Restated.blockInRun_of_ancestorOn facts S rho W Xb hBFrun
      ((hnd% named_genesis_preceq_deadline) BF)
  have hnotGen : ∀ R : NamedBlock V, Restated.RunBlockOn M S rho W Xb R →
      (M.derive_named S.E S.cfg R).h = blocked → R.erase = Block.genesis → False := by
    intro R hRrun hRh hRgenErase
    have hRgen : R = NamedBlock.genesis :=
      hf.rootCollisionFree.root_injective R .genesis
        hRrun hgenRun R .genesis
        (Or.inl ((hnd% named_preceq_self_deadline) R))
        (Or.inr ((hnd% named_preceq_self_deadline) .genesis))
        (by
          calc
            R.root = R.erase.root := (Proofs.NamedWire.erase_root R).symm
            _ = Block.genesis.root := congrArg Block.root hRgenErase
            _ = (NamedBlock.genesis : NamedBlock V).erase.root := by
              rw [erase_named_genesis]
            _ = (NamedBlock.genesis : NamedBlock V).root :=
              Proofs.NamedWire.erase_root _)
    subst R
    have honeEq : 1 = blocked := by
      rw [facts.cs.derive_named_genesis_h] at hRh
      exact hRh
    rw [← honeEq] at htwo
    norm_num at htwo
  refine ⟨hfirst, hstart, (by exact (by decide : 1 ≤ 2).trans htwo), ?_, ?_⟩
  · intro c _hminimal
    exact Restated.namedHeightRegimeFrame_of_finalizedRunOn facts S Hs Xb X hf hXXb hX
      (Nat.lt_succ_of_le
        (hfirst.before _ (Nat.sub_lt hfirst.positive Nat.one_pos)))
      hBFrun hFpre hFerase hFheight hBFheight hFself
  · intro a ta _ha _hemit _hbefore R hRrun hRh _hpair n _hn _hR w hw time
      _hfrontier hroot Y _hYrun _hYheight hFY
    have hroot' : M.get_fg_root (M.toHealing (W (strictEventIndex rho time) w).st.core).toFG =
        R.erase := hroot
    generalize strictEventIndex rho time = m at hroot'
    have hmem : W m ∈ Record.stateBeforeOf M S rho m := (hf.onePath m).1
    by_cases hgate : (W m w).st.core.h_max = (W m w).st.core.h_j + 1
    · obtain ⟨C, hCmem, hCJ, _hChj⟩ :=
        Restated.Vocabulary.Proofs.Bridges.storeJustificationOnChain_stateBefore facts S rho m w
          (W m) hmem
      have hCrun : Restated.RunBlockOn M S rho W Xb C :=
        Restated.runBlock_of_stateBefore_memOn facts S W Xb (hXXb hw) hCmem
      have hRJ : R.erase = (M.derive_named S.E S.cfg C).J := by
        have h := hroot'.symm
        rw [facts.fc.get_fg_root_toHealing_of_eq _ hgate] at h
        exact h.trans hCJ.symm
      have hJpos : 0 < (M.derive_named S.E S.cfg C).h_j := by
        by_contra hz
        have hz' : (M.derive_named S.E S.cfg C).h_j = 0 := Nat.eq_zero_of_not_pos hz
        exact hnotGen R hRrun hRh
          (hRJ.trans (facts.cs.justified_zero_is_genesis S.E S.cfg C hz'))
      obtain ⟨J, hJC, hJerase, hJheight, hJself⟩ :=
        Restated.Vocabulary.Proofs.NamedCheckpointAlgebra.namedJustification_selfTarget facts
          S.E S.cfg C hJpos
      have hJrun : Restated.RunBlockOn M S rho W Xb J :=
        Restated.blockInRun_of_ancestorOn facts S rho W Xb hCrun hJC
      have hRJnamed : R = J :=
        hf.rootCollisionFree.root_injective R J hRrun hJrun R J
          (Or.inl ((hnd% named_preceq_self_deadline) R))
          (Or.inr ((hnd% named_preceq_self_deadline) J))
          (by rw [← Proofs.NamedWire.erase_root R, ← Proofs.NamedWire.erase_root J,
            hRJ, hJerase])
      have hjeq : (M.derive_named S.E S.cfg C).h_j = blocked := by
        rw [← hJheight, ← hRJnamed]
        exact hRh
      have hJF := Restated.namedJustified_eq_finalized_deadlineOn facts S Hs Xb hf hsb
        hCrun hBFrun hFrun hFpre hFerase
        (hFheight.trans hBFheight.symm) hFself
        (hjeq.trans hBFheight.symm)
      have hRFerase : R.erase = F.erase := hRJ.trans hJF
      have hRF : R = F :=
        hf.rootCollisionFree.root_injective R F hRrun hFrun R F
          (Or.inl ((hnd% named_preceq_self_deadline) R))
          (Or.inr ((hnd% named_preceq_self_deadline) F))
          (by rw [← Proofs.NamedWire.erase_root R, ← Proofs.NamedWire.erase_root F,
            hRFerase])
      rw [hRF]
      exact hFY
    · obtain ⟨C, hCmem, hCF, _hCFbelow⟩ :=
        Restated.Vocabulary.Proofs.Bridges.storeFinalizationOnChain_stateBefore facts S rho m w
          (W m) hmem
      have hCrun : Restated.RunBlockOn M S rho W Xb C :=
        Restated.runBlock_of_stateBefore_memOn facts S W Xb (hXXb hw) hCmem
      have hRFraw : R.erase = (M.derive_named S.E S.cfg C).F := by
        have h := hroot'.symm
        rw [facts.fc.get_fg_root_toHealing_of_ne _ hgate] at h
        exact h.trans hCF.symm
      have hCnz : ¬ (M.derive_named S.E S.cfg C).h_F = 0 := by
        intro hz'
        exact hnotGen R hRrun hRh
          (hRFraw.trans (facts.cs.finalized_zero_is_genesis S.E S.cfg C hz'))
      obtain ⟨FC, hFC, hFCerase, hFCheight, hFCself⟩ :=
        (facts.csAdded.finalized_is_entry S.E S.cfg C).resolve_left hCnz
      have hFCrun : Restated.RunBlockOn M S rho W Xb FC :=
        Restated.blockInRun_of_ancestorOn facts S rho W Xb hCrun hFC
      have hRFC : R = FC :=
        hf.rootCollisionFree.root_injective R FC hRrun hFCrun R FC
          (Or.inl ((hnd% named_preceq_self_deadline) R))
          (Or.inr ((hnd% named_preceq_self_deadline) FC))
          (by rw [← Proofs.NamedWire.erase_root R, ← Proofs.NamedWire.erase_root FC,
            hRFraw, hFCerase])
      have hFCblocked : (M.derive_named S.E S.cfg FC).h = blocked := by
        rw [← hRFC]
        exact hRh
      have hcompat := Restated.finalized_compatibleOn facts
        S rho W Xb C BF hsb hf.rootCollisionFree hCrun hBFrun
      have hentryEq := Restated.namedEntries_eq_of_compatible_deadlineOn facts S Hs Xb hf
        hFCrun hFrun hFCself hFself
        (hFCblocked.trans hFheight.symm)
        (by simpa only [hFCerase, hFerase] using hcompat)
      rw [hRFC, hentryEq]
      exact hFY

end

/-! ## Run-scoped bases from height progress -/

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel.Proofs.Optimistic

/-- Every action instant is at least `0`. -/
private theorem a_nonneg₇₀b (facts : Record.Facts M) (S : Setup V) (r : Round) :
    0 ≤ Restated.Vocabulary.Execution.Setup.a M S r := by
  show 0 ≤ M.a S.hc S.E.Δ r
  rw [facts.sch.a_eq_confirmation_time]
  exact le_trans (facts.sch.Optimistic_proposal_time_nonneg S.E _)
    (facts.sch.proposal_time_le_confirmation_time S.E _)

/-- Under the bundle along `W`, the committee majority and the weight bound, with `X` containing
    every set of the family from instant `0` and inside `Xb`, if the largest `h_max` over the family
    along `W` rises within every `lag` rounds from `r0`, `K` divides `H`, the largest `h_max` over
    `X` in the world of `W` at `r0`'s inclusive index plus `D + 1` is at most `H`, `H + 3` is at
    most the largest `h_max` over the set for `S.a r0` in that world plus `k`, and
    `S.a (r0 + k · lag)` is in the horizon, then some run-scoped named base along `W` at
    `blocked ≤ H + 1` has its first crossing no later than that instant's inclusive index. -/
theorem exists_namedHeightRegimeBaseRun_of_eventualHeightProgressOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb X : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hX : ∀ t : Int, 0 ≤ t → Hs t ⊆ X) (hXXb : X ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hbelow : BelowOneThirdOn S rho Hs)
    {r0 lag : Round}
    (hprog : 0 < lag ∧ ∀ r : Round, r0 ≤ r →
      (Restated.Vocabulary.Execution.Setup.a M S (r + lag)) ≤ rho.horizon →
      ((Hs (Restated.Vocabulary.Execution.Setup.a M S r)).sup fun u =>
          (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) u).st.core.h_max) <
        (Hs (Restated.Vocabulary.Execution.Setup.a M S (r + lag))).sup fun u =>
          (W (inclusiveEventIndex rho
            (Restated.Vocabulary.Execution.Setup.a M S (r + lag))) u).st.core.h_max)
    {H : Height} (hK : S.cfg.K ∣ H)
    (hH : (X.sup fun v =>
      (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r0)) v).st.h_max) +
        S.cfg.D + 1 ≤ H)
    {k : Nat}
    (hk : H + 3 ≤ ((Hs (Restated.Vocabulary.Execution.Setup.a M S r0)).sup fun v =>
      (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r0)) v).st.h_max) + k)
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S (r0 + k * lag)) ≤ rho.horizon) :
    ∃ (blocked : Height) (first : Nat) (Tprev : NamedBlock V),
      blocked ≤ H + 1 ∧
      first ≤ inclusiveEventIndex rho ((Restated.Vocabulary.Execution.Setup.a M S (r0 + k * lag))) ∧
      Restated.NamedHeightRegimeBaseRunOn M S rho W (fun t => W (strictEventIndex rho t)) Hs X Xb
        r0 blocked first Tprev := by
  have hbelowX : Execution.BelowOneThird S X :=
    belowOneThird_mono_l70 S (hX 0 le_rfl) (hbelow 0 hf.horizon_nonneg)
  have hreach : H + 3 ≤ X.sup fun v =>
      (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (r0 + k * lag))) v).st.h_max := by
    have hend := hk.trans (Restated.honestHMaxBeforeIndex_ge_of_eventualHeightProgress_namedDeadlineOn facts
      S Hs Xb hf hprog k hhor)
    exact hend.trans (Finset.sup_mono (hX _ (a_nonneg₇₀b facts S _)))
  obtain ⟨first, hstop, hfirst⟩ := Restated.exists_firstHeightProgressAtOn facts
    S Hs Xb X hf
    (H := H + 1) (Nat.succ_le_succ (Nat.zero_le H))
    ((Nat.add_le_add_left (by decide : 2 ≤ 3) H).trans hreach)
  have hstartH : (X.sup fun v =>
      (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r0)) v).st.h_max) < H :=
    lt_of_lt_of_le (Nat.lt_succ_of_le (Nat.le_add_right _ _)) hH
  have hmemFirst : W first ∈ Record.stateBeforeOf M S rho first := (hf.onePath first).1
  by_cases hrec : NjGap.RecoveryHeight S.cfg
      (X.sup fun u => (W first u).st.bodies.sup fun C => (M.derive_named S.E S.cfg C).h_F) H
  · have hbase := Restated.namedHeightRegimeBase_of_recoveryOn facts S Hs Xb X hf hXXb hX hbelowX
      hfirst
      (Restated.honestPrefixFinalityCap_recoveryPrefixFinalityHeightOn facts S rho X first
        (W first) hmemFirst)
      hrec hstartH
    exact ⟨H, first, .genesis, Nat.le_succ H, hstop,
      Restated.NamedHeightRegimeBaseRunOn.ofNamed hbase⟩
  · have hwithin : H ≤
        (X.sup fun u => (W first u).st.bodies.sup fun C => (M.derive_named S.E S.cfg C).h_F) +
          S.cfg.D := by
      have hnot : ¬ S.cfg.D < H -
          (X.sup fun u => (W first u).st.bodies.sup fun C => (M.derive_named S.E S.cfg C).h_F) := by
        intro hgap
        exact hrec ⟨hK, hgap⟩
      have hsub := Nat.sub_le_iff_le_add.mp (Nat.le_of_not_lt hnot)
      rw [Nat.add_comm]
      exact hsub
    have hneX : X.Nonempty := by
      obtain ⟨u, hu⟩ := Restated.honest_nonempty_of_committeesOn facts S Hs hcom 0
      have h0 : (0 : Int) ≤ M.confirmation_time S.E 0 :=
        le_trans (facts.sch.Optimistic_proposal_time_nonneg S.E _)
          (facts.sch.proposal_time_le_confirmation_time S.E _)
      exact ⟨u, hX _ h0 hu⟩
    obtain ⟨v, hv, B, hB, hBF⟩ :=
      Restated.exists_named_finalizedAt_recoveryPrefixFinalityHeightOn facts S X first hneX
        (W first) hmemFirst
    have hBrun : Restated.RunBlockOn M S rho W Xb B :=
      Restated.runBlock_of_stateBefore_memOn facts S W Xb (hXXb hv) hB
    have hheight : (M.derive_named S.E S.cfg B).h ≤ (W first v).st.h_max :=
      Restated.Vocabulary.Proofs.NamedStoreBridge.heights_le_hMax_stateBefore facts
        S rho first v (W first) hmemFirst B hB
    have hlocal : (W first v).st.h_max ≤ X.sup fun u => (W first u).st.h_max :=
      Finset.le_sup (f := fun u => (W first u).st.h_max) hv
    rw [hfirst.frontier] at hlocal
    have hstrict : (M.derive_named S.E S.cfg B).h_F < (M.derive_named S.E S.cfg B).h :=
      (facts.cs.chainOrder_derive_named S.E S.cfg B).heights_ordered.trans_lt
        (facts.cs.chainOrder_derive_named S.E S.cfg B).justified_below_height
    have hupper : (M.derive_named S.E S.cfg B).h_F ≤ H + 1 :=
      Nat.le_of_lt_succ (hstrict.trans_le (hheight.trans hlocal))
    have hstart : (X.sup fun v =>
        (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r0)) v).st.h_max) <
        (M.derive_named S.E S.cfg B).h_F := by
      rw [hBF]
      have h := hH.trans hwithin
      rw [Nat.add_right_comm] at h
      exact Nat.le_of_add_le_add_right h
    obtain ⟨next, hnext, hcross⟩ := Restated.exists_firstHeightProgressAtOn facts
      S Hs Xb X hf
      (H := (M.derive_named S.E S.cfg B).h_F + 1)
      (Nat.succ_le_succ (Nat.zero_le _))
      (((Nat.add_le_add_right hupper 1).trans_lt
        (Nat.lt_succ_self (H + 2))).trans_le hreach)
    have hpos : 0 < (M.derive_named S.E S.cfg B).h_F :=
      (Nat.zero_le _).trans_lt hstart
    obtain ⟨F, hFB, hFerase, hFheight, hFself⟩ :=
      (facts.csAdded.finalized_is_entry S.E S.cfg B).resolve_left (Nat.pos_iff_ne_zero.mp hpos)
    exact ⟨_, next, F, hupper, hnext,
      Restated.namedHeightRegimeBaseRun_of_finalizedOn facts S Hs Xb X hf hXXb hX hbelowX hcross hstart
        hBrun hFB hFerase hFheight rfl hFself⟩

/-- Under the bundle along `W`, the committee majority and the weight bound, with `X` containing
    every set of the family from instant `0` and inside `Xb`, if the carrier rounds recur within
    `gap` rounds from `t₀`, the timeout delay bound holds, `S.E.t_GST ≤ S.a rGST`, the progress
    deadline's action instant is in the horizon, `lo ≤ S.a (rGST + 2)`,
    `lo ≤ opening (rGST + 2 − η_SG)`, `t₀ ≤ S.a (rGST + 2)` and the grade-2 awake hypotheses hold,
    then some run-scoped named base along `W` at `rGST + 2` has its first crossing no later than the
    deadline's inclusive index. -/
theorem exists_namedHeightRegimeBaseRun_before_fgSafetyProgressDeadlineOn (facts : Record.Facts M)
    {delayExtra : Nat}
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb X : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hX : ∀ t : Int, 0 ≤ t → Hs t ⊆ X) (hXXb : X ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hbelow : BelowOneThirdOn S rho Hs)
    {rGST gap : Round} {t₀ : Int} (hrec : Restated.MultiProposerRecurrenceOn M S Hs gap t₀ rho.horizon)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S rGST))
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S (fgSafetyProgressDeadline S rho rGST gap delayExtra)) ≤
      rho.horizon)
    (hlo : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (rGST + 2)))
    (hloOpen : lo ≤ M.opening S.E S.hc (rGST + 2 - S.hc.η_SG))
    (ht₀ : t₀ ≤ (Restated.Vocabulary.Execution.Setup.a M S (rGST + 2)))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S k) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    ∃ (blocked : Height) (first : Nat) (Tprev : NamedBlock V),
      first ≤ inclusiveEventIndex rho
        ((Restated.Vocabulary.Execution.Setup.a M S (fgSafetyProgressDeadline S rho rGST gap delayExtra))) ∧
      Restated.NamedHeightRegimeBaseRunOn M S rho W (fun t => W (strictEventIndex rho t)) Hs X Xb
        (rGST + 2) blocked first Tprev := by
  let r0 := rGST + 2
  let L := progressLag' gap delayExtra
  let k := S.cfg.D + S.cfg.K + 5
  have hpost' : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S r0) :=
    hpost.trans ((Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone (by
      simpa only [r0] using Nat.le_add_right rGST 2))
  have hloOpen1 : lo ≤ M.opening S.E S.hc (r0 + 1 - S.hc.η_SG) :=
    hloOpen.trans (facts.gr.NamedOutageClosure_opening_mono S
      (Nat.sub_le_sub_right (Nat.le_succ _) _))
  have hprog := Restated.eventualHeightProgressFrom_of_seedOn facts S Hs Xb hf hHs hHsXb hcom
      hbelow hrec
      (Restated.heightProgressSeedFrom_of_canonicityOn facts S Hs Xb hf hHs hHsXb hcom hbelow
        hdelay hrec hpost'
        (Restated.seedPredPromotionInputs_of_publicOn facts S Hs Xb hf hHs hHsXb hcom hbelow
          hdelay hrec hloOpen1 hA
          (hA r0 (Restated.lo_le_early_g2_sub_delta_of_opening facts S (Nat.zero_lt_succ _) hloOpen
            le_rfl)))
        hlo hloOpen1 ht₀ hA)
      hdelay hpost'
      (fun hfix hpostRead hread hbound hhorEnd hcap hloRead ht₀Read hloOpenRead =>
        Restated.fixedRootProgress_of_rowsOn facts S Hs Xb hf hHs hHsXb hcom hbelow hrec hdelay
          hA
          (fun hfix' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 hp1 hp2 hB1 hl1 hl2 hfa hrd hmd hfm hab
              hpar hmat hsp hlo' hA' =>
            Restated.fixedRoot_sourceHeight_le_nextOpeningParentOn facts S Hs Xb hf hHs hHsXb
              hcom hbelow hfix' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 hp1 hp2 hB1 hl1 hl2 hfa hrd
              hmd hfm hab hpar hmat hsp hlo' hA')
          hfix hpostRead hread hbound hhorEnd hcap hloRead ht₀Read hloOpenRead)
      hlo hloOpen ht₀ hA
  let Mh := (Hs (Restated.Vocabulary.Execution.Setup.a M S r0)).sup fun v =>
    (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r0)) v).st.h_max
  obtain ⟨H, hH, hHupper, hrecovery⟩ :=
    exists_recoveryHeight_between S.cfg Mh (Mh + 1) (Nat.le_add_right Mh 1)
  have hK : S.cfg.K ∣ H := hrecovery.1
  have hdeadline : r0 + k * L =
      fgSafetyProgressDeadline S rho rGST gap delayExtra := by
    dsimp only [r0, k, L, fgSafetyProgressDeadline]
    ring
  have hendHor : (Restated.Vocabulary.Execution.Setup.a M S (r0 + k * L)) ≤ rho.horizon := by
    simpa only [hdeadline] using hhor
  have hLpos : 0 < L := by
    show 0 < progressLag' gap delayExtra
    unfold progressLag'
    exact Nat.lt_of_lt_of_le (by decide : 0 < 10)
      (Nat.le_add_right_of_le (Nat.le_add_left 10 _))
  have hkpos : 0 < k := by
    show 0 < S.cfg.D + S.cfg.K + 5
    omega
  have hkLpos : 0 < k * L := Nat.mul_pos hkpos hLpos
  have hstartHor : (Restated.Vocabulary.Execution.Setup.a M S r0) + 1 ≤ rho.horizon :=
    (Int.add_one_le_iff.mpr (Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S (Nat.lt_add_of_pos_right hkLpos))).trans
      hendHor
  have hstartBound : (X.sup fun v =>
      (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r0)) v).st.h_max) ≤
      Mh + 1 :=
    Restated.honestHMaxBeforeIndexOn_inclusive_le_succ_l70 facts S Hs Xb X hf hHs hHsXb
      (honestWeightMajorityOn_of_belowOneThirdOn hbelow) hstartHor
  have hH' : (X.sup fun v =>
      (W (inclusiveEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r0)) v).st.h_max) +
        S.cfg.D + 1 ≤ H :=
    (Nat.add_le_add_right (Nat.add_le_add_right hstartBound S.cfg.D) 1).trans hH
  have hk : H + 3 ≤ Mh + k := by
    calc
      H + 3 ≤ (Mh + 1 + S.cfg.D + S.cfg.K) + 3 :=
        Nat.add_le_add_right hHupper 3
      _ = Mh + (S.cfg.D + S.cfg.K + 4) := by ring
      _ ≤ Mh + k := Nat.add_le_add_left (Nat.le_succ _) Mh
  obtain ⟨blocked, first, Tprev, -, hfirst, hbase⟩ :=
    Restated.exists_namedHeightRegimeBaseRun_of_eventualHeightProgressOn facts
      S Hs Xb X hf hX hXXb hcom hbelow hprog hK hH' hk hendHor
  refine ⟨blocked, first, Tprev, ?_, hbase⟩
  rw [← hdeadline]
  exact hfirst

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.Optimistic

local macro "p56% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Claims.Restated.Claim13beRoute3_56)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p58% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Claims.Restated.Claim13beRoute3_58)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p68% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Claims.Restated.Claim13beRoute3_68)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

end

end DecoupledConsensusModel.Sts.Restated
