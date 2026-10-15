import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bStepConeIter
import Proofs.Claims.Restated.Claim13beRoute3_45
import Proofs.Claims.Restated.Claim13beRoute3_46
import Proofs.Claims.Restated.Claim13beRoute3_47
import Proofs.Claims.Restated.Claim13beRoute3_48
import Proofs.Claims.Restated.Claim13beRoute3_48b
import Proofs.Claims.Restated.Claim13beRoute3_50
import Proofs.Claims.Restated.Claim13beRoute3_53b
import Proofs.Claims.Restated.Claim13beRoute3_55
import Proofs.Claims.Restated.Claim13beRoute3_57
import Proofs.Claims.Restated.Claim13beRoute3_58
import Proofs.Claims.Restated.Claim13beRoute3_59
import Proofs.Claims.Restated.Claim13beRoute3_60
import Proofs.Claims.Restated.Claim13beRoute3_61
import Proofs.Claims.Restated.Claim13beRoute3_62
import Proofs.Claims.Restated.Claim13beRoute3_63
import Proofs.Claims.Restated.Vocabulary_Execution_EmissionShape
import Proofs.Claims.Restated.Vocabulary_Execution_HealthyLocalFacts
import Proofs.Claims.Restated.Vocabulary_Execution_OutageInputs
import Proofs.Claims.Restated.Vocabulary_Execution_PreparedReadBridge
import Proofs.Claims.Restated.Vocabulary_Execution_RecoveryActionLiveSourceSplit
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Claims.Restated.Vocabulary_ModelVocabulary_Healing_Schedule
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_ActionSourceCore
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_GradeDelivery
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_RecoveryProposalConfirmationRead
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_SeedEntryCanonical
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_Grades
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_RecoveryGenuineClearNextVote
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_RelativeOneChain
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_RowTrace
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_TickBridges
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_Action
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_PostHealingReuse
import Proofs.Claims.Restated.Vocabulary_Protocol_Store_BoundaryRows
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.RunVocabulary
import Model.Record.Wiring
import Proofs.Claims.Restated.Vocabulary_Execution_RecoveryFilterSchedule

/-!
# The selector cone's checkpoint along a path

Theorems on the structure `PrefixFGSelectorConeAtOn` over a model `M : Record.Model V` and its facts
`facts : Record.Facts M`, with every store read in a world of the bundle's path `W` and the seed
cone and frame taken at the worlds `fun t => W (strictEventIndex rho t)`: the named checkpoint and
its retention, the relative carrier window, the vote steps of the source and later rounds, the SG
emissions of later rounds, and the joint induction with the confirmation witness.
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
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open scoped DC

/-- The round-`r` action read computed from `before` has a node state. -/
private theorem actionReadFrom_nonempty₆₄ (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∃ n, n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r := by
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc before.st.core.toHealing
    (Restated.Vocabulary.Execution.Setup.a M S r) before.cache
  obtain ⟨st, hst⟩ := facts.dt.duties_update_confirmation_with_nonempty (M.gradeContract c) S.E S.hc
    (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r))
    (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1)
  exact ⟨_, c, hc, st, hst, rfl⟩

omit [DecidableEq V] [Fintype V] in
/-- `m >>= k` can return `b` exactly when `m` can return some `a` and `k a` can return `b`. -/
private theorem returns_bind_iff₆₄ {α β : Type} (m : DC.NDRE α) (k : α → DC.NDRE β)
    (b : β) : (m >>= k) ⇢ b ↔ ∃ a, m ⇢ a ∧ k a ⇢ b := by
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

/-- For every node state `n`, the action FG source read at `n` has an outcome. -/
private theorem actionFGSource_nonempty₆₄ (facts : Record.Facts M) (S : Setup V)
    (n : M.N) : ∃ o, Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n ⇢ o := by
  obtain ⟨A2, hA2⟩ := facts.dt.grade2_block_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s)
  obtain ⟨o, ho⟩ := facts.dt.fg_source_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s) A2
  exact ⟨o, (returns_bind_iff₆₄ _ _ _).2 ⟨A2, hA2, ho⟩⟩

/-- Every node state of the round-`r` action read computed from `before` holds `before`'s bodies. -/
private theorem actionReadFrom_bodies₆₄ (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r,
      n.st.bodies = before.st.bodies := by
  rintro _ ⟨c, -, st, hst, rfl⟩
  rewrite [facts.nd.mkNode_st, facts.nd.store_with_cache_bodies]
  rw [facts.dt.named_update_confirmation_with_bodies _ _ _ _ _ st hst,
    facts.hd.ModelProperties_setClock_bodies]

/-- The round-`r` action read computed from `M.wake n` gives exactly the node states it gives
    computed from `n`. -/
private theorem actionReadFrom_wake₆₄ (facts : Record.Facts M) (S : Setup V) (n : M.N) (r : Round) :
    Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (M.wake n) r =
      Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S n r := by
  unfold Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom
  rw [(facts.nd.wake_st_record n).1, (facts.nd.wake_st_record n).2, facts.nd.wake_cache n]

/-- Every action instant is at least `0`. -/
private theorem a_nonneg₆₄ (facts : Record.Facts M) (S : Setup V) (r : Round) :
    0 ≤ Restated.Vocabulary.Execution.Setup.a M S r := by
  show 0 ≤ M.a S.hc S.E.Δ r
  rw [facts.sch.a_eq_confirmation_time]
  exact le_trans (facts.sch.Optimistic_proposal_time_nonneg S.E _)
    (facts.sch.proposal_time_le_confirmation_time S.E _)

/-- The number of events strictly before the seed attestation's action instant is less than `stop`. -/
private theorem actionPrefix_lt₆₄ (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} {Hs : Int → Finset V} {Xb : Finset V} {lo : Int}
    {W : Nat → V → M.N} {Wt : Time → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {start stop : Nat} {blocked : Height} {i : Nat}
    {a : NamedAttestation V} {ta : Time} {Cfg : NamedBlock V} {T : Block V}
    (hseed : Restated.PrefixFGSelectorConeAtOn M S rho W Wt Hs Xb start stop blocked i a ta Cfg T) :
    strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round) < stop := by
  have hle : strictEventIndex rho ta ≤ i := by
    by_contra hnot
    have hlt : i < strictEventIndex rho ta := Nat.lt_of_not_ge hnot
    unfold strictEventIndex at hlt
    have hmem : Record.Event.tick a.val_index ta ∈
        rho.events.filter (fun e => decide (e.time < ta)) := by
      rw [Restated.filter_eq_takeOn facts S Hs Xb hf _ (Restated.downward_lt ta)]
      exact List.mem_of_getElem? (by
        rw [List.getElem?_take_of_lt hlt]
        exact hseed.exactTick)
    have himpossible := (List.mem_filter.mp hmem).2
    simp only [decide_eq_true_eq, Record.Event.time] at himpossible
    exact lt_irrefl ta himpossible
  rw [hseed.actionTime_eq] at hle
  exact hle.trans_lt hseed.indexLtStop

/-- The seed attestation's action instant is at most the run's horizon. -/
private theorem actionHorizon₆₄ (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} {Hs : Int → Finset V} {Xb : Finset V} {lo : Int}
    {W : Nat → V → M.N} {Wt : Time → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {start stop : Nat} {blocked : Height} {i : Nat}
    {a : NamedAttestation V} {ta : Time} {Cfg : NamedBlock V} {T : Block V}
    (hseed : Restated.PrefixFGSelectorConeAtOn M S rho W Wt Hs Xb start stop blocked i a ta Cfg T) :
    Restated.Vocabulary.Execution.Setup.a M S a.round ≤ rho.horizon := by
  have h := (hf.in_horizon (Record.Event.tick a.val_index ta)
    (List.mem_of_getElem? hseed.exactTick)).2
  simpa only [Record.Event.time, hseed.actionTime_eq, Record.Event.time] using h

/-- Under the bundle with path `W`, if `u` emits the attestation `b` at `t` along `W`, then at every
    event `j` of `rho` that is `u`'s tick at `t`, `u`'s node state in `W j` passes the grade-2 awake
    test of `b`'s round. -/
private theorem awake_g2_of_emits₆₄ (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} {Hs : Int → Finset V} {Xb : Finset V} {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {u : V} {b : NamedAttestation V} {t : Time}
    (hb : Restated.Vocabulary.Execution.NamedRun.emits M S rho W u (NamedObject.attest b) t) :
    ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u t) →
      M.awake_for_grade2 S u (W j u) b.round := by
  obtain ⟨i, hi, hiA⟩ :=
    Restated.Vocabulary.Proofs.Optimistic.emits_attest_awake facts S W hf.onePath hb
  intro j hj
  rw [← Restated.tick_index_eq_of_unique hf.tickIndexUnique hi hj]
  exact hiA

end

/-! ## The checkpoint and the relative carrier window -/

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open scoped DC

/-- Under the bundle with path `W`, if the selector cone holds for `a` with source `Cfg` and
    checkpoint `T`, and the named frame over `X` holds at `blocked` up to `first − 1`, then for
    every node state `n` of the signer's round-`a.round` action read along `W`, some named block `K`
    of `n`'s store erases to `T`, has height `blocked + 1`, is a run block along `W` through `Xb`,
    and is a descendant of `Tprev`. -/
theorem PrefixFGSelectorConeAtOn.namedCheckpoint_l64 (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} {Hs : Int → Finset V} {Xb X : Finset V} {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (_hX : ∀ t : Int, 0 ≤ t → Hs t ⊆ X)
    {start first : Nat} {blocked : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg Tprev : NamedBlock V} {T : Block V} {c0 : Round}
    (hseed : Restated.PrefixFGSelectorConeAtOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs Xb start first blocked i a ta Cfg T)
    (hframe : Restated.NamedHeightRegimeFrameOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs X Xb blocked (first - 1) Tprev c0) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round)) a.val_index)
        a.round,
    ∃ K : NamedBlock V,
      K ∈ n.st.bodies ∧
      K.erase = T ∧
      (M.derive_named S.E S.cfg K).h = blocked + 1 ∧
      Restated.RunBlockOn M S rho W Xb K ∧
      NamedBlock.Preceq Tprev K := by
  intro n hn
  have hsigner : a.val_index ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S a.round)) := by
    have h := hseed.signerHonest
    rw [hseed.actionTime_eq] at h
    exact h
  obtain ⟨K, hKsource, hKT0, hKheight0, hKCfg, hKrun⟩ :=
    Restated.action_named_checkpointOn facts S Hs Xb hf (hHsXb _ hsigner) hn (hseed.sourceMem n hn)
  have hKT : K.erase = T := hKT0.trans hseed.checkpointDerived.symm
  have hKheight : (M.derive_named S.E S.cfg K).h = blocked + 1 :=
    hKheight0.trans hseed.sourceDerivedHeight
  obtain ⟨o, ho⟩ := actionFGSource_nonempty₆₄ facts S n
  have hsrc : Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n ⇢ some Cfg.erase := by
    rw [← hseed.exactFGSource n hn o ho]
    exact ho
  have hTprevCfg : Block.Preceq Tprev.erase Cfg.erase :=
    Proofs.NamedWire.erase_preceq (hframe.sourceAbove a.val_index
      a.round hsigner (Nat.le_sub_one_of_lt (actionPrefix_lt₆₄ facts hf hseed))
      (actionHorizon₆₄ facts hf hseed) n hn Cfg (hseed.sourceMem n hn) hsrc
      hseed.sourceDerivedHeight)
  have hTprevK : NamedBlock.Preceq Tprev K := by
    rcases preceq_linear_Preceq hTprevCfg
        (Proofs.NamedWire.erase_preceq hKCfg) with hprevK | hKprev
    · exact Restated.namedPreceq_of_runBlock_erase_preceqOn facts Hs Xb hf hframe.prevRun hKrun
        hprevK
    · have hKTprev : NamedBlock.Preceq K Tprev :=
        Restated.namedPreceq_of_runBlock_erase_preceqOn facts Hs Xb hf hKrun hframe.prevRun hKprev
      have hmono := facts.cs.derive_height_mono S.E S.cfg hKTprev
      rw [hKheight] at hmono
      exact False.elim
        (Nat.not_succ_le_self blocked (hmono.trans hframe.prevHeight))
  exact ⟨K, hKsource, hKT, hKheight, hKrun, hTprevK⟩

/-- Under the bundle with path `W`, if the selector cone holds for `a` with checkpoint `T`, the
    window over `X` at `blocked + 1` holds before `first`, the named frame over `X` holds at
    `blocked` up to `first − 1`, `max (S.a a.round) lo + Δ ≤ read`, `read` is in the horizon and
    before `first`, `w` is in the set for `read`, and `lo ≤ S.a a.round`, then `w`'s store in
    `W (strictEventIndex rho read)` has `h_max = blocked + 1`, its FG root is an ancestor of `T`,
    and `T` is in its filtered tree. -/
theorem PrefixFGSelectorConeAtOn.checkpointFiltered_at_laterRead_of_frame_named
    (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} {Hs : Int → Finset V} {Xb X : Finset V} {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hX : ∀ t : Int, 0 ≤ t → Hs t ⊆ X) (hXXb : X ⊆ Xb)
    {start first : Nat} {blocked : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg Tprev : NamedBlock V} {T : Block V} {c0 : Round}
    (hseed : Restated.PrefixFGSelectorConeAtOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs Xb start first blocked i a ta Cfg T)
    (hfirst : Restated.HeightWindowAtOn M S rho W X (blocked + 1) first)
    (hframe : Restated.NamedHeightRegimeFrameOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs X Xb blocked (first - 1) Tprev c0)
    {read : Time}
    (hdelay : max ((Restated.Vocabulary.Execution.Setup.a M S a.round)) lo + S.E.Δ ≤ read)
    (hhor : read ≤ rho.horizon)
    (hbefore : strictEventIndex rho read < first)
    {w : V} (hw : w ∈ Hs read)
    (hlo : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S a.round)) :
    (W (strictEventIndex rho read) w).st.core.h_max = blocked + 1 ∧
      Block.Preceq (M.get_fg_root
        (M.toHealing (W (strictEventIndex rho read) w).st.core).toFG) T ∧
      T ∈ M.get_filtered_block_tree
        (M.toHealing (W (strictEventIndex rho read) w).st.core).toFG := by
  obtain ⟨n₀, hn₀⟩ := actionReadFrom_nonempty₆₄ facts S
    (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round)) a.val_index)
    a.round
  obtain ⟨K, hKsource, hKT, hKheight, hKrun, hTprevK⟩ :=
    hseed.namedCheckpoint_l64 facts hf hHsXb hX hframe n₀ hn₀
  have hsigner : a.val_index ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S a.round)) := by
    have h := hseed.signerHonest
    rw [hseed.actionTime_eq] at h
    exact h
  have hsignerSrc : a.val_index ∈
      Hs (max ((Restated.Vocabulary.Execution.Setup.a M S a.round)) lo) := by
    rw [max_eq_left hlo]
    exact hsigner
  have hreadNonneg : 0 ≤ read := by
    have := a_nonneg₆₄ facts S a.round
    have := S.E.Δ_pos
    have := le_max_left ((Restated.Vocabulary.Execution.Setup.a M S a.round)) lo
    linarith
  have hwX : w ∈ X := hX _ hreadNonneg hw
  have hprefix : strictEventIndex rho read ≤ first - 1 :=
    Nat.le_sub_one_of_lt hbefore
  have hfrontier : (X.sup fun u => (W (first - 1) u).st.core.h_max) < blocked + 2 := by
    have hstopLt : first - 1 < first :=
      Nat.sub_lt (Nat.zero_lt_of_lt hbefore) Nat.zero_lt_one
    exact (hfirst.before _ hstopLt).trans_lt
      (Nat.lt_succ_self (blocked + 1))
  have hFread : Block.Preceq
      (W (strictEventIndex rho read) w).st.core.F K.erase :=
    hframe.floor w hwX _ hprefix K hKrun
      (by rw [hKheight]; exact Nat.le_succ blocked) hTprevK
  have hKsourcePre : K ∈
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round))
        a.val_index).st.bodies := by
    rw [← actionReadFrom_bodies₆₄ facts S _ a.round n₀ hn₀]
    exact hKsource
  obtain ⟨hKtargetIndex, -, -⟩ :=
    Restated.healthy_head_body_at_read_after_gst_admitOn facts S rho Hs Xb hf hHs hHsXb
      a.val_index w K ((Restated.Vocabulary.Execution.Setup.a M S a.round)) read read hsignerSrc hw
        hKsourcePre hdelay (le_refl _) hhor hFread
  have hout := hframe.fgRoot_preceq_and_filteredMem facts
    Hs hf hXXb hfrontier hwX hprefix hKtargetIndex hKheight hTprevK
  have hmem := (hf.onePath (strictEventIndex rho read)).1
  have hcoh := (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho
    (strictEventIndex rho read) w _ hmem).1.1.1
  have hKraw : K.erase ∈ (W (strictEventIndex rho read) w).st.core.T := by
    rw [hcoh.1]
    exact Finset.mem_image_of_mem NamedBlock.erase hKtargetIndex
  have hKstored :
      ((W (strictEventIndex rho read) w).st.core.σ K.erase).h = blocked + 1 := by
    rw [Restated.Vocabulary.Proofs.NamedStoreBridge.derivedView_stateBefore facts S rho
      (strictEventIndex rho read) w _ hmem K hKtargetIndex, hKheight]
  have hmax := Restated.localHMax_eq_blocked_succ_of_rawMem_of_prefixFrontierOn facts
    S Hs Xb X hf hfrontier hwX hprefix hKraw hKstored
  exact ⟨hmax, by simpa only [hKT] using hout.1,
    by simpa only [hKT] using hout.2⟩

/-- Under the bundle with path `W`, if the selector cone holds for `a` with checkpoint `T`, the
    window over `X` at `blocked + 1` holds before `first`, the named frame over `X` holds at
    `blocked` up to `first − 1`, round `a.round` is ready, `a.round ≤ r`, every round-`r` emitter of
    the set for `S.a r` has every SG block of its action reads compatible with `T`, `S.a (r + 1)` is
    in the horizon and before `first`, and `lo ≤ opening (a.round − η_SG)`, then the relative
    carrier window holds along `W` at round `r` and phase `p`. -/
theorem PrefixFGSelectorConeAtOn.relativeCarrierWindow_of_previousSG_of_frame_named
    (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} {Hs : Int → Finset V} {Xb X : Finset V} {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hX : ∀ t : Int, 0 ≤ t → Hs t ⊆ X) (hXXb : X ⊆ Xb)
    {start first : Nat} {blocked : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg Tprev : NamedBlock V} {T : Block V} {c0 : Round}
    (hseed : Restated.PrefixFGSelectorConeAtOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs Xb start first blocked i a ta Cfg T)
    (hfirst : Restated.HeightWindowAtOn M S rho W X (blocked + 1) first)
    (hframe : Restated.NamedHeightRegimeFrameOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs X Xb blocked (first - 1) Tprev c0)
    (_ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho a.round)
    {r : Round} (hr : a.round ≤ r)
    (hsg : Restated.HonestSGEmissionsCompatibleAtRoundOn M S rho W
      (fun t => W (strictEventIndex rho t)) Hs r T)
    (hhor : (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) ≤ rho.horizon)
    (hbefore : strictEventIndex rho ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))) < first)
    (p : Phase)
    (hlo : lo ≤ M.opening S.E S.hc (a.round - S.hc.η_SG)) :
    Restated.RelativeCarrierWindowAtOn M S rho W (fun t => W (strictEventIndex rho t)) Hs r p := by
  have hΔ := S.E.Δ_pos
  have hopenA : M.opening S.E S.hc a.round ≤ Restated.Vocabulary.Execution.Setup.a M S a.round := by
    rw [← facts.gr.Sts_domain_g1_eq_opening S a.round]
    exact facts.gr.domain_le_a S a.round .g1
  have hloSource : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S a.round) :=
    hlo.trans ((facts.gr.NamedOutageClosure_opening_mono S (Nat.sub_le _ _)).trans hopenA)
  have haR : Restated.Vocabulary.Execution.Setup.a M S a.round ≤
      Restated.Vocabulary.Execution.Setup.a M S r :=
    Restated.Vocabulary.Proofs.Assembly.a_mono facts S hr
  have hloR : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S r) := hloSource.trans haR
  have hhorR : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ rho.horizon :=
    (Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.le_succ r)).trans hhor
  have hdomainA : M.domain S.E S.hc (r + 1) p ≤ Restated.Vocabulary.Execution.Setup.a M S (r + 1) :=
    facts.gr.domain_le_a S (r + 1) p
  have hdomainHor : M.domain S.E S.hc (r + 1) p ≤ rho.horizon := hdomainA.trans hhor
  have hdomainBefore : strictEventIndex rho (M.domain S.E S.hc (r + 1) p) < first :=
    (strictEventIndex_mono rho hdomainA).trans_lt hbefore
  have hdeltaEarly : (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ ≤
      M.early S.E S.hc (r + 1) .g2 :=
    facts.gr.action_delta_le_early S S.hc.R_ge_three (Nat.lt_succ_self r)
  have hearlyP : M.early S.E S.hc (r + 1) .g2 ≤ M.early S.E S.hc (r + 1) p := by
    cases p with
    | g0 => exact facts.gr.early_g2_le_early_g0 S.E S.hc (r + 1)
    | g1 => exact facts.gr.early_g2_le_early_g1 S.E S.hc (r + 1)
    | g2 => exact le_rfl
  have horder : M.early S.E S.hc (r + 1) p ≤ M.domain S.E S.hc (r + 1) p := by
    have h := facts.gr.early_add_two_delta_le_domain S (r + 1) p
    linarith
  have hsourceDelay : max ((Restated.Vocabulary.Execution.Setup.a M S a.round)) lo + S.E.Δ ≤
      M.domain S.E S.hc (r + 1) p := by
    rw [max_eq_left hloSource]
    linarith
  have hcut : M.early S.E S.hc (r + 1) p ≤ rho.horizon := horder.trans hdomainHor
  have hk : r ∈ M.latest_window S.hc.η_SG (r + 1) := by
    apply facts.fc.mem_latest_window
    · simpa only [Nat.add_sub_cancel] using
        Nat.sub_le_sub_left S.hc.η_SG_ge_one (r + 1)
    · exact Nat.lt_succ_self r
  rw [Restated.RelativeCarrierWindowAtOn]
  intro w hw u hu huEarly na hna g2 hg2 A hAsel I hI
  have hna' : na ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) u) r := hna
  obtain ⟨huHon, b, hbval, hbround, hbemit⟩ :=
    (Restated.honestRoundVoters_iffOn facts S rho W hf.onePath Hs u r).mp hu
  have huXb : u ∈ Xb := hHsXb _ huHon
  have hawake : ∀ j : Nat, rho.events[j]? =
      some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S r)) →
      M.awake_for_grade2 S u (W j u) r := by
    have h := awake_g2_of_emits₆₄ facts hf hbemit
    rwa [hbround] at h
  obtain ⟨D, hD⟩ := facts.dt.attest_with_nonempty (M.gradeContract na.cache) S.E S.hc (S.node u)
    na.st na.record
  have hmemT := (Restated.stateBeforeTime_eq_stateBefore_strictEventIndexOn facts S Hs Xb hf
    (Restated.Vocabulary.Execution.Setup.a M S r)).symm ▸
      (hf.onePath (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r))).1
  have hshape : D.2.2.val_index = u ∧ D.2.2.round = r ∧ D.2.2.confirmed = some A.root :=
    Restated.Vocabulary.Proofs.HealingSurface.actionAttestationAt_shape facts S rho u r na
      ⟨_, hmemT, hna'⟩ D hD g2 hg2 A hAsel
  have hemit : Restated.Vocabulary.Execution.NamedRun.emits M S rho W u (Object.attest D.2.2)
      ((Restated.Vocabulary.Execution.Setup.a M S r)) :=
    Restated.honest_emits_exact_actionAttestationAt_of_awakeOn facts S Hs Xb hf r huHon hawake
      hhorR hloR (fun j hj => hf.tick_outcome j _ _ hj) na hna' D hD
  obtain ⟨j, hj, -, -, -, -, hhead⟩ :=
    Restated.Vocabulary.Proofs.NamedOutageInputs.emitted_attestation_head facts S rho W hf.onePath
      hemit
  have hstate := Restated.action_read_indexOn facts S rho Hs Xb hf j u r hj
  have hnaJ : na ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (W j u)
      D.2.2.round := by
    rcases hstate with h | h
    · rw [h, hshape.2.1]
      exact hna'
    · rw [h, actionReadFrom_wake₆₄ facts, hshape.2.1]
      exact hna'
  obtain ⟨Hb, hHb, hconfirmed⟩ := hhead na hnaJ
  have hbodies := actionReadFrom_bodies₆₄ facts S _ r na hna'
  have hAmem : A ∈
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) u).st.core.T :=
    Restated.Vocabulary.Proofs.HealingSurface.actionSGBlockAt_mem_storeBeforeTime facts S rho u r
      _ hmemT na hna' g2 hg2 A hAsel
  obtain ⟨Dn, hDnBody, hDnErase⟩ :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore facts S rho
      (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) u _
      (hf.onePath _).1 hAmem
  have hDnRun : Restated.RunBlockOn M S rho W Xb Dn :=
    Restated.runBlock_of_stateBefore_memOn facts S W Xb huXb hDnBody
  have hHbRun : Restated.RunBlockOn M S rho W Xb Hb :=
    Restated.runBlock_of_stateBefore_memOn facts S W Xb huXb (by rw [← hbodies]; exact hHb)
  have hroot : Dn.root = Hb.root := by
    rw [← Proofs.NamedWire.erase_root Dn, hDnErase]
    exact Option.some.inj (hshape.2.2.symm.trans hconfirmed)
  have hDH : Dn = Hb :=
    hf.rootCollisionFree.root_injective Dn Hb hDnRun hHbRun Dn Hb
      (Or.inl (Proofs.NamedAncestry.named_self Dn))
      (Or.inr (Proofs.NamedAncestry.named_self Hb)) hroot
  have hHbErase : Hb.erase = A := by
    rw [← hDH, hDnErase]
  have hHbRoot : Hb.root = A.root := by
    rw [← Proofs.NamedWire.erase_root Hb, hHbErase]
  have hcarrierT : Block.compatible Hb.erase T = true := by
    rw [hHbErase]
    exact hsg u huHon na hna D hD hemit g2 hg2 A hAsel
  have hread := hseed.checkpointFiltered_at_laterRead_of_frame_named facts
    hf hHs hHsXb hX hXXb hfirst hframe hsourceDelay hdomainHor hdomainBefore hw hloSource
  have hFT : Block.Preceq
      (W (strictEventIndex rho (M.domain S.E S.hc (r + 1) p)) w).st.core.F T := by
    have h := facts.fc.q10_filtered_F hread.2.2
    rw [facts.sto.Sts_toHealing_F] at h
    exact h
  have hpostA : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S D.2.2.round) := by
    rw [hshape.2.1]
    exact hloR
  have hdeadline : max ((Restated.Vocabulary.Execution.Setup.a M S D.2.2.round)) lo + S.E.Δ ≤
      M.early S.E S.hc (r + 1) p := by
    rw [hshape.2.1, max_eq_left hloR]
    exact hdeltaEarly.trans hearlyP
  have hwEarly : w ∈ Hs (M.early S.E S.hc (r + 1) p) := hHs _ _ horder hw
  have hexact : ∀ {C : Block V}, Block.Preceq Hb.erase C →
      Block.Preceq (W (strictEventIndex rho (M.domain S.E S.hc (r + 1) p)) w).st.core.F C →
      ∃ y ∈ I, y.round = r ∧ y.confirmed = some A.root ∧
        Block.find? (W (strictEventIndex rho (M.domain S.E S.hc (r + 1) p)) w).st.core.T A.root =
          some A := by
    intro C hHC hFC
    have h := Restated.interpretedInputs_exact_of_honest_window_vote_after_gst_common_upperOn facts
      S Hs Xb hf hHs hHsXb (t := M.domain S.E S.hc (r + 1) p) p hk huEarly hwEarly
      ⟨hshape.1, hshape.2.1, hemit⟩ ⟨j, hj, ⟨na, hnaJ, hHb⟩, hconfirmed⟩ hHC hFC hpostA
      hdeadline horder hcut I hI
    rw [hHbErase, hHbRoot] at h
    exact h
  rcases (show Block.Preceq Hb.erase T ∨ Block.Preceq T Hb.erase from
    compatible_cases hcarrierT) with hHbT | hTHb
  · exact hexact hHbT hFT
  · exact hexact (Proofs.ModelProperties.Preceq_self Hb.erase) (preceq_trans_Preceq hFT hTHb)

/-- Under the bundle with path `W` and the committee majorities, if the selector cone holds for `a`
    with checkpoint `T`, the frame and window over `X` hold up to `first`, the slot-`s` votes of the
    set form a cone over `T`, every member of the set for `vote_time (s + 1)` has every outcome of
    the anchor of each of its vote-duty reads of `s + 1` compatible with `T`, `hrun` holds, and the
    timing hypotheses of the signature hold, then every member of the set for `vote_time (s + 1)`
    has every head of each of its vote-duty reads of `s + 1` a descendant of `T`, and the
    slot-`(s + 1)` votes of the set form a cone over `T`. -/
theorem PrefixFGSelectorConeAtOn.checkpointVoteStep_of_anchors_of_frame_named
    (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} {Hs : Int → Finset V} {Xb X : Finset V} {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hX : ∀ t : Int, 0 ≤ t → Hs t ⊆ X) (hXXb : X ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    {start first : Nat} {blocked : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg Tprev : NamedBlock V} {T : Block V} {c0 : Round}
    (hseed : Restated.PrefixFGSelectorConeAtOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs Xb start first blocked i a ta Cfg T)
    (hfirst : Restated.HeightWindowAtOn M S rho W X (blocked + 1) first)
    (hframe : Restated.NamedHeightRegimeFrameOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs X Xb blocked (first - 1) Tprev c0)
    {s : Slot} (hs : 0 < s)
    (hpost : lo ≤ M.vote_time S.E s)
    (hhor : M.confirmation_time S.E s ≤ rho.horizon)
    (hdelay : max ((Restated.Vocabulary.Execution.Setup.a M S a.round)) lo + S.E.Δ ≤
      M.vote_time S.E (s + 1))
    (hbefore : strictEventIndex rho (M.vote_time S.E (s + 1)) < first)
    (hvotes : Restated.NamedHonestVotesConeOn M S rho W Hs Xb s (fun Y => Block.Preceq T Y))
    (hanchors : ∀ w ∈ Hs (M.vote_time S.E (s + 1)), ∀ c : M.Cache,
      M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.toHealing
        (M.vote_time S.E (s + 1))
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache ⇢ c →
      ∀ A : Block V,
        Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S
          (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
            (M.vote_time S.E (s + 1))) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c)
          (M.round_of S.hc
            (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
              (M.vote_time S.E (s + 1)))
              (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c).st.core.s) ⇢ A →
        Block.compatible A T = true)
    (hlo : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S a.round))
    (hrun : ∀ w ∈ S.E.committee (s + 1), w ∈ Hs (M.vote_time S.E (s + 1)) → ∀ j : Nat,
      rho.events[j]? = some (Record.Event.tick w (M.vote_time S.E (s + 1))) →
      M.awake_for_grade1 S w (W j w) (M.round_of S.hc (s + 1))) :
    (∀ w ∈ Hs (M.vote_time S.E (s + 1)), ∀ c : M.Cache,
      M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.toHealing
        (M.vote_time S.E (s + 1))
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache ⇢ c →
      let n := M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
          (M.vote_time S.E (s + 1)))
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c
      ∀ Tr : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ Tr →
      ∀ L : Finset (GoldfishVote V),
        M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
      ∀ L' : Finset (GoldfishVote V),
        M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
      ∀ H : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
          (M.toHealing n.st.core) Tr L L' (n.st.core.s - 1) ⇢ H →
        Block.Preceq T H) ∧
      Restated.NamedHonestVotesConeOn M S rho W Hs Xb (s + 1) (fun Y => Block.Preceq T Y) := by
  have hvoteHor : M.vote_time S.E (s + 1) ≤ rho.horizon :=
    le_trans (le_of_lt (lt_of_lt_of_le (Int.lt_add_of_pos_right _ S.E.Δ_pos)
      (facts.sch.vote_time_succ_add_delta_le_confirmation_time S.E s))) hhor
  have hvoteLo : lo ≤ M.vote_time S.E (s + 1) :=
    hpost.trans (facts.sch.vote_time_mono_slots S.E (Nat.le_succ s))
  have hfreezeLe : lo ≤ M.view_freeze S.E s :=
    hpost.trans (facts.sch.vote_time_le_view_freeze S.E s)
  have hreads := fun w (hw : w ∈ Hs (M.vote_time S.E (s + 1))) =>
    hseed.checkpointFiltered_at_laterRead_of_frame_named facts
      hf hHs hHsXb hX hXXb hfirst hframe hdelay hvoteHor hbefore hw hlo
  obtain ⟨n₀, hn₀⟩ := actionReadFrom_nonempty₆₄ facts S
    (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round)) a.val_index)
    a.round
  obtain ⟨K, -, hKT, hKheight, hKrun, -⟩ :=
    hseed.namedCheckpoint_l64 facts hf hHsXb hX hframe n₀ hn₀
  have hinputs : ∀ w ∈ Hs (M.vote_time S.E (s + 1)), ∀ c : M.Cache,
      M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.toHealing
        (M.vote_time S.E (s + 1))
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache ⇢ c →
      Restated.Vocabulary.Proofs.HealingSurface.GoldfishConeVoteInputs' M S rho s T w
        (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
          (M.vote_time S.E (s + 1))) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c) := by
    intro w hw c hc
    refine { rootSide := ?_, anchor := hanchors w hw c hc }
    intro A hA Tr hTr
    have hdutyCore : Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1) =
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
          (M.vote_time S.E (s + 1))).core := by
      rw [Restated.Vocabulary.Proofs.Optimistic.voteStore,
        Restated.Vocabulary.Proofs.Optimistic.tickStore, facts.hd.setClock_core_eq_store_with_t_s]
    have hrootDuty : Block.Preceq
        (M.get_fg_root
          (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
            (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1))).toFG) T := by
      rw [Restated.Vocabulary.Proofs.Optimistic.voteStore,
        Restated.Vocabulary.Proofs.Optimistic.tickStore]
      exact (facts.fc.get_fg_root_set_clock_slot _ _ _).symm ▸ (hreads w hw).2.1
    have hrootN : Block.Preceq
        (M.get_fg_root
          (M.toHealing (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
            (M.vote_time S.E (s + 1))).core).toFG) T := by
      rw [← hdutyCore]
      exact hrootDuty
    have hmaxN : (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
        (M.vote_time S.E (s + 1))).core.h_max = blocked + 1 := by
      rw [facts.hd.setClock_core_h_max]
      exact (hreads w hw).1
    have hpositive : 0 < ((S.E.committee s) ∩ Hs (M.confirmation_time S.E s)).card := by
      have hcommittee := hcom s
      omega
    obtain ⟨u, hu⟩ := Finset.card_pos.mp hpositive
    have huCommittee : u ∈ S.E.committee s := (Finset.mem_inter.mp hu).1
    have huConf : u ∈ Hs (M.confirmation_time S.E s) := (Finset.mem_inter.mp hu).2
    obtain ⟨Y, hTY, hYrun, hYemit⟩ :=
      hvotes u (hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E s) huConf)
        huCommittee
    have hYhead : Restated.HonestHeadOn M S rho W Hs Xb s Y.erase :=
      ⟨u, huConf, huCommittee, ⟨Y, rfl, hYrun⟩, hYemit⟩
    obtain ⟨P, hP⟩ := facts.fc.voter_processed_block_tree_nonempty S.E
      (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1))).toFG.toSG.toGoldfishStore
      (M.toHealing (Restated.Vocabulary.Proofs.Optimistic.voteStore M S
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1))).s
    have hwSC : w ∈ Hs (M.support_cutoff S.E s) :=
      hHs _ _ (facts.sch.support_cutoff_le_vote_time_succ S.E s) hw
    have hprocessed : Y.erase ∈ P :=
      Restated.honestHead_voterProcessed_at_nextDuty_of_postHealingConeOn facts
        S Hs Xb hf hHs hHsXb hpost hhor hvotes hYhead hwSC hrootDuty P hP
    have hKY : NamedBlock.Preceq K Y :=
      Restated.namedPreceq_of_runBlock_erase_preceqOn facts Hs Xb hf hKrun hYrun
        (by rw [hKT]; exact hTY)
    have hKYheight : blocked + 1 ≤ (M.derive_named S.E S.cfg Y).h := by
      rw [← hKheight]
      exact facts.cs.derive_height_mono S.E S.cfg hKY
    have hYmem : Y.erase ∈
        (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
          (M.vote_time S.E (s + 1))) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record
          c).st.core.T := by
      have hmem := facts.fc.mem_T_of_mem_voter_processed_block_tree _ _ _ P hP hprocessed
      rw [facts.sto.toHealing_gs_T, hdutyCore] at hmem
      rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
      exact hmem
    have hstored := Restated.storedHeight_of_runBlock_mem_voteDutyReadOn facts
      S Hs Xb hf (hHsXb _ hw) hYrun c hYmem
    have hband : (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
          (M.vote_time S.E (s + 1))) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record
          c).st.core.h_max - 1 ≤
        ((M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
          (M.vote_time S.E (s + 1))) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record
          c).st.core.σ Y.erase).h := by
      rewrite [hstored, facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [hmaxN]
      exact (Nat.sub_le (blocked + 1) 1).trans hKYheight
    have hwVF : w ∈ Hs (M.view_freeze S.E s) :=
      hHs _ _ (le_of_lt (facts.sch.view_freeze_lt_vote_time_succ S.E s)) hw
    have hpath := Restated.namedCandidatePath_of_processedBandDescendantOn facts
      S Hs Xb hf hwVF hTY P hP hprocessed c hc hband
      (by rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; exact hrootN) hfreezeLe Tr hTr
    rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]
    exact Or.inl ⟨hrootN, hpath.1, fun B hAB hne hBC hne' => hpath.2 A hA B hAB hne hBC hne'⟩
  have hheads : ∀ w ∈ Hs (M.vote_time S.E (s + 1)), ∀ c : M.Cache,
      M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.toHealing
        (M.vote_time S.E (s + 1))
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache ⇢ c →
      let n := M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
          (M.vote_time S.E (s + 1)))
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c
      ∀ Tr : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ Tr →
      ∀ L : Finset (GoldfishVote V),
        M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
      ∀ L' : Finset (GoldfishVote V),
        M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
      ∀ H : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
          (M.toHealing n.st.core) Tr L L' (n.st.core.s - 1) ⇢ H →
        Block.Preceq T H := fun w hw c hc =>
    Restated.goldfishCone_stepOn'_GoldfishCone facts S Hs Xb hf hHs hHsXb hcom hs hpost
      hhor hvotes hw c hc (hinputs w hw c hc)
  refine ⟨hheads, ?_⟩
  intro w hw hcommittee
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc
    (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.toHealing
    (M.vote_time S.E (s + 1)) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache
  set n := M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
    (M.vote_time S.E (s + 1))) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c with hn
  obtain ⟨Tr, hTr⟩ := facts.fc.voter_filtered_block_tree_nonempty S.E n.st.core n.st.core.s
  obtain ⟨L, hL⟩ := facts.fc.voter_view_nonempty S.E
    (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s
  obtain ⟨L', hL'⟩ := facts.fc.voter_support_view_nonempty S.E
    (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s
  obtain ⟨Hd, hHd⟩ := facts.fc.get_head_in_tree_with_layer_nonempty (M.gradeContract n.cache) S.E
    S.hc (M.toHealing n.st.core) Tr L L' (n.st.core.s - 1)
  obtain ⟨Y, hYe, hYrun, hYemit⟩ :=
    Restated.named_voter_head_emitsOn facts S Hs Xb hf hHsXb hw (Nat.succ_pos s)
      hcommittee hvoteHor hvoteLo c hc (hrun w hcommittee hw) Tr hTr L hL L' hL' Hd hHd
  exact ⟨Y, hYe ▸ hheads w hw c hc Tr hTr L hL L' hL' Hd hHd, hYrun, hYemit⟩

end

/-! ## `activeVoterAnchor_compatible_actionFGSource_at_interior_namedOn` -/

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open scoped DC
local macro "p63% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_63)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

/-- If `m` can return `a` and `f a = b`, then `f <$> m` can return `b`. -/
private theorem returns_map_intro₆₄ {α β : Type} (f : α → β) (m : DC.NDRE α) (a : α) (b : β)
    (h : m ⇢ a) (hb : f a = b) : (f <$> m) ⇢ b := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image]
  exact ⟨.ok a, h, by simp [Except.map, hb]⟩

/-- Along the bundle's path `W`, if `n` is a node state of `v`'s round-`r` action read and the
    action FG source of `n` can return `some B`, then the FG source of `n` at round `r` can return
    `some B`. -/
private theorem nodeFGSource_of_actionFGSource₆₄ (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} {Hs : Int → Finset V} {Xb : Finset V} {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} {r : Round} {B : Block V} (n : M.N)
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r)
    (hsource : Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n ⇢ some B) :
    Restated.Vocabulary.Internal.PhaseGrades.nodeFGSource M S n r ⇢ some B := by
  have hmem := (p63% mem_stateBeforeTime_along₆₃) hf.sorted hf.onePath
    (Restated.Vocabulary.Execution.Setup.a M S r)
  have hnAt : n ∈ Restated.Vocabulary.Proofs.HealingSurface.actionReadAt M S rho v r := ⟨_, hmem, hn⟩
  have hround : M.round_of S.hc (M.toHealing n.st.core).s = r := by
    show M.round_of S.hc (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.s = r
    rw [facts.sto.toHealing_s]
    exact Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt_round facts S rho v r n hnAt
  have h : (do
      let g ← M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
        (M.round_of S.hc (M.toHealing n.st.core).s)
      M.fg_source_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
        (M.round_of S.hc (M.toHealing n.st.core).s) g) ⇢ some B := hsource
  rw [hround] at h
  exact h

/-- Under the bundle with path `W`, if `0 < r`, round `r` is ready, `S.a r` is within the horizon,
    `p` is in the set for `domain r g0` and `w` in the set for `domain r g1`, a node state `n` of
    `p`'s round-`r` action read along `W` has a Q2 that can return `some Q` and an action FG source
    that can return `some B`, every outcome of the grade-1 store grade of `L` at `w`'s store in
    `W (strictEventIndex rho (domain r .g1))` is `true`, `L` is the erasure of a body of `p`'s store
    in `W (strictEventIndex rho (domain r .g0))` and a descendant of `p`'s finalized block there,
    and `lo ≤ opening (r − η_SG)`, then `L` and `B` are compatible. -/
private theorem anchor_compatible_actionFGSource₆₄ (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {r : Round} (hr : 0 < r)
    (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho r)
    (hactionHor : Restated.Vocabulary.Execution.Setup.a M S r ≤ rho.horizon)
    {p w : V} (hp : p ∈ Hs (M.domain S.E S.hc r .g0))
    (hwG1 : w ∈ Hs (M.domain S.E S.hc r .g1))
    {Q B L : Block V} {n : M.N}
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) p) r)
    (hselected : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ some Q)
    (hsource : Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n ⇢ some B)
    (hLgrade1 : ∀ b : Bool, Restated.Vocabulary.Internal.PhaseGrades.storeGrade M S.E S.hc
      (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st r .g1 L ⇢ b → b = true)
    (hLbody : ∃ Ln : NamedBlock V, Ln.erase = L ∧
      Ln ∈ (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) p).st.bodies)
    (hFg0L : Block.Preceq (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) p).st.core.F L)
    (hlo : lo ≤ M.opening S.E S.hc (r - S.hc.η_SG)) :
    Block.compatible L B = true := by
  have hgst : lo ≤ M.early S.E S.hc r .g2 :=
    facts.gr.lo_le_early_g2_of_window_start S hr hlo
  have hg2g0 : M.domain S.E S.hc r .g2 ≤ M.domain S.E S.hc r .g0 :=
    facts.gr.domain_le_domain_g0 S r .g2
  have hpG2 : p ∈ Hs (M.domain S.E S.hc r .g2) := hHs _ _ hg2g0 hp
  have hguard := Restated.actionQ2_crossReaderBodyReadyGuard_historyOn facts
    S Hs Xb hf hHs hHsXb hr ready hp hgst n hn w hwG1 Q hselected
  have hQgrade1 := Restated.selectedG2_G1_at_read_after_cutoffOn facts
    S Hs Xb hf hHs hHsXb ready hactionHor hpG2 hwG1 n hn hselected hguard hlo
  obtain ⟨bL, hbL⟩ := facts.gr.gradeBool_nonempty S.E
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st.core.F
    S.hc.η_SG r (M.early S.E S.hc r .g1) (M.late S.E S.hc r .g1) L
  obtain ⟨bQ, hbQ⟩ := facts.gr.gradeBool_nonempty S.E
    (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st.core))
    (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st.core.F
    S.hc.η_SG r (M.early S.E S.hc r .g1) (M.late S.E S.hc r .g1) Q
  have hbLt : bL = true := hLgrade1 bL hbL
  have hLQ : Block.compatible L Q = true :=
    Restated.Vocabulary.Proofs.HealingSurface.graded_oneChain_at_reader facts S.E
      (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st.core))
      (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st.core.F
      S.hc.η_SG r (facts.gr.early_g1_le_late_g1 S r) bL hbL hbLt bQ hbQ (hQgrade1 bQ hbQ)
  have hmemA := (p63% mem_stateBeforeTime_along₆₃) hf.sorted hf.onePath
    (Restated.Vocabulary.Execution.Setup.a M S r)
  have hsourceNode := nodeFGSource_of_actionFGSource₆₄ facts S hf n hn hsource
  have hQB : Block.Preceq Q B :=
    Restated.Vocabulary.Proofs.HealingSurface.preceq_actionFGSource_of_actionQ2 facts S rho p r
      _ hmemA n hn hselected (Proofs.ModelProperties.Preceq_self Q) hsourceNode
  rcases compatible_cases hLQ with hLQ | hQL
  · exact compatible_of_cases (Or.inl (preceq_trans_Preceq hLQ hQB))
  · rcases Restated.Vocabulary.Proofs.HealingSurface.actionFGSource_genuineClear_or_selectedG2_named
        facts S rho p r _ hmemA n hn hselected hsource with hclear | hlocal
    · obtain ⟨_, _, _, hwalk, _, _⟩ := hclear
      obtain ⟨Ln, hLnErase, hLnG0⟩ := hLbody
      have hLtree : L ∈ (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) p).st.core.T := by
        have hcoh := (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho
          (strictEventIndex rho (M.domain S.E S.hc r .g0)) p _ (hf.onePath _).1).1.1.1
        rw [hcoh.1, ← hLnErase]
        exact Finset.mem_image_of_mem NamedBlock.erase hLnG0
      have hgstG1 : lo ≤ M.early S.E S.hc r .g1 :=
        hgst.trans (facts.gr.early_g2_le_early_g1 S.E S.hc r)
      have hforward : ∀ sender u key Head,
          ∀ I, M.interpretedInputs
            (M.gradeView (M.toHealing
              (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st.core))
            (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st.core.F
            S.hc.η_SG r (M.early S.E S.hc r .g1) sender ⇢ I → u ∈ I →
          ∀ cc, M.localCovers
            (M.gradeView (M.toHealing
              (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st.core))
            u.confirmed L ⇢ cc → cc = true →
          u.confirmed = some key →
          Block.find?
            (M.gradeView (M.toHealing
              (W (strictEventIndex rho (M.domain S.E S.hc r .g1)) w).st.core)).T
              key = some Head →
          Block.Preceq (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) p).st.core.F Head := by
        intro sender u key Head _ _ _ cc hcc hcct hconf hfind
        apply preceq_trans_Preceq hFg0L
        rw [hconf] at hcc
        exact facts.gr.preceq_of_localCovers_of_find cc hcc hcct hfind
      have hbelowReaders :=
        Restated.g1G0CrossReaderFinalizedBelow_of_finalitySafety_and_relayOn facts
          S Hs Xb hf hHs hHsXb hf.slashableBound hgstG1 ready.2 hwG1 hp hforward
      have hguard0 := Restated.g1G0CrossReaderBodyReadyGuard_of_finalizedBelowOn facts
        S Hs Xb hf hHs hHsXb hr hgstG1 ready.2 hwG1 hp hbelowReaders
      subst hbLt
      have hLgrade0 := Restated.storeGrade_g0_of_storeGrade_g1_cross_readerOn facts
        S rho Hs Xb hf hHs hHsXb r hlo ready.2 w p hwG1 hp L hbL hguard0
      obtain ⟨b0, hb0⟩ := facts.gr.gradeBool_nonempty S.E
        (M.gradeView (M.toHealing (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) p).st.core))
        (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) p).st.core.F
        S.hc.η_SG r (M.early S.E S.hc r .g0) (M.late S.E S.hc r .g0) L
      have hb0t : b0 = true := hLgrade0 b0 hb0
      subst hb0t
      have hQaction := Restated.Vocabulary.Proofs.HealingSurface.actionQ2_mem_filteredTree facts
        S rho p r _ hmemA n hn hselected
      have hFQ : Block.Preceq n.st.core.F Q := by
        have h := facts.fc.q10_filtered_F hQaction
        rw [facts.sto.Sts_toHealing_F] at h
        exact h
      have hFL : Block.Preceq n.st.core.F L := preceq_trans_Preceq hFQ hQL
      have hBclear : Restated.Vocabulary.Internal.PhaseGrades.nodeClear M S n r B ⇢ true := by
        obtain ⟨G, hG⟩ := facts.gr.read_nonempty (M.gradeContract n.cache) S.E S.hc
          (M.toHealing n.st.core) r
        have htest := facts.gr.deepest_clear_test (hwalk G hG)
        exact returns_map_intro₆₄ (fun g => g.clear B) _ G true hG htest
      have hlog0 : lo ≤ M.domain S.E S.hc r .g0 :=
        (hgst.trans (facts.gr.early_le_domain S r)).trans hg2g0
      exact Restated.relativeG0_compatible_clearSource_of_finalizedPreceq_historyOn facts
        S Hs Xb hf hr hactionHor hp hLtree hb0 hn hFL hBclear hlog0
    · subst hlocal
      exact compatible_of_cases (Or.inr hQL)

/-- Under the bundle with path `W`, if `0 < r`, round `r` is ready, `S.a r` is within the horizon,
    `p` is in the set for `domain r g0`, `d` is a slot of round `r` from its opening slot on whose
    vote instant is in the horizon, at most the next opening, and at least `Δ` after `domain r g0`,
    `w` is in the set for `vote_time d`, `n` is a node state of `p`'s round-`r` action read along
    `W` whose Q2 can return `some Q` and whose action FG source can return `some B`, `c` is an
    outcome of `w`'s cache update at `vote_time d` and the node state staged with `c` has the
    grade-1 frame root `root` and active prefix `L` under it, and `lo ≤ opening (r − η_SG)`, then
    `L` and `B` are compatible. -/
theorem activeVoterAnchor_compatible_actionFGSource_at_interior_namedOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {r : Round} (hr : 0 < r)
    (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho r)
    (hactionHor : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ rho.horizon)
    {p w : V} (hp : p ∈ Hs (M.domain S.E S.hc r .g0))
    {d : Slot} (hw : w ∈ Hs (M.vote_time S.E d))
    (hslo : (M.opening_slot S.hc r) ≤ d)
    (hround : (M.round_of S.hc d) = r)
    (hnext : M.vote_time S.E d ≤ M.opening S.E S.hc (r + 1))
    (hvoteHor : M.vote_time S.E d ≤ rho.horizon)
    (hsettled : M.domain S.E S.hc r .g0 + S.E.Δ ≤ M.vote_time S.E d)
    (_hactionSettled : (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ ≤ M.vote_time S.E d)
    {Q B root L : Block V} {n : M.N}
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) p) r)
    (hselected : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ some Q)
    (hsource : Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n ⇢ some B)
    (c : M.Cache)
    (hc : M.onPhaseTick S.E S.hc
      (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core.toHealing (M.vote_time S.E d)
      (W (strictEventIndex rho (M.vote_time S.E d)) w).cache ⇢ c)
    (hframe : (M.readFrame
      (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) w).st
        (M.vote_time S.E d)) (W (strictEventIndex rho (M.vote_time S.E d)) w).record c).cache
      (M.toHealing (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) w).st
        (M.vote_time S.E d)) (W (strictEventIndex rho (M.vote_time S.E d)) w).record c).st.core)
        r).g1 = some (some root))
    (hactive : M.activePrefix
      (Restated.Vocabulary.Internal.PhaseGrades.filteredTree M
        (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) w).st
          (M.vote_time S.E d)) (W (strictEventIndex rho (M.vote_time S.E d)) w).record c))
        root = some L)
    (hlo : lo ≤ M.opening S.E S.hc (r - S.hc.η_SG)) :
    Block.compatible L B = true := by
  have hΔ := S.E.Δ_pos
  have hgst : lo ≤ M.early S.E S.hc r .g2 :=
    facts.gr.lo_le_early_g2_of_window_start S hr hlo
  have hgstG1 : lo ≤ M.early S.E S.hc r .g1 :=
    hgst.trans (facts.gr.early_g2_le_early_g1 S.E S.hc r)
  have hlog1 : lo ≤ M.domain S.E S.hc r .g1 :=
    hgstG1.trans (facts.gr.early_g1_le_domain_g1 S r)
  have hg1g0 : M.domain S.E S.hc r .g1 ≤ M.domain S.E S.hc r .g0 :=
    facts.gr.domain_le_domain_g0 S r .g1
  have hlog0 : lo ≤ M.domain S.E S.hc r .g0 := hlog1.trans hg1g0
  have hwOut : w ∈ Hs (M.domain S.E S.hc r .g0 + S.E.Δ) := hHs _ _ hsettled hw
  have hwG1 : w ∈ Hs (M.domain S.E S.hc r .g1) := hHs _ _ (by linarith) hwOut
  obtain ⟨hLtreeG1, hLgrade1⟩ := Restated.fixedRoot_activeVoterAnchor_g1_dataOn facts
    S Hs Xb hf hr hslo hround hnext hvoteHor hwG1 c hc hframe hactive hlog1
  have hactive' : M.activePrefix (M.get_filtered_block_tree
      (M.toHealing (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) w).st
        (M.vote_time S.E d)).core).toFG) root = some L := by
    have h := hactive
    simp only [Restated.Vocabulary.Internal.PhaseGrades.filteredTree] at h
    rewrite [facts.nd.mkNode_st] at h; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at h
    exact h
  have hLvote := facts.gr.activePrefix_mem _ _ _ hactive'
  have hvoteFL : Block.Preceq
      (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core.F L := by
    have h := facts.fc.finalized_preceq_of_mem_get_filtered_block_tree hLvote
    rw [facts.sto.Sts_toHealing_F, facts.hd.setClock_core_F] at h
    exact h
  have hrelay : Block.Preceq
      (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) p).st.core.F
      (W (strictEventIndex rho (M.domain S.E S.hc r .g0 + S.E.Δ)) w).st.core.F :=
    Restated.finalized_preceq_of_evidence_deliveredOn facts
      S Hs Xb hf hHs hHsXb hf.slashableBound hp hwOut hlog0 rfl (hsettled.trans hvoteHor)
  have hmono : Block.Preceq
      (W (strictEventIndex rho (M.domain S.E S.hc r .g0 + S.E.Δ)) w).st.core.F
      (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core.F :=
    (p63% F_mono_along₆₃) facts S hf.onePath w
      (Restated.strict_lengths_mono rho hsettled)
  have hFg0L : Block.Preceq
      (W (strictEventIndex rho (M.domain S.E S.hc r .g0)) p).st.core.F L :=
    preceq_trans_Preceq hrelay (preceq_trans_Preceq hmono hvoteFL)
  obtain ⟨Ln, hLnG1, hLnErase⟩ :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime facts S rho
      (M.domain S.E S.hc r .g1) w _
      ((p63% mem_stateBeforeTime_along₆₃) hf.sorted hf.onePath _) hLtreeG1
  have hdeadline :
      max (M.domain S.E S.hc r .g1) lo + S.E.Δ ≤ M.domain S.E S.hc r .g0 := by
    rw [max_eq_left hlog1]
    exact facts.gr.domain_g1_add_delta_le_domain_g0 S r
  have hwSrc : w ∈ Hs (max (M.domain S.E S.hc r .g1) lo) := by
    rw [max_eq_left hlog1]
    exact hwG1
  obtain ⟨hLnG0, -, -⟩ :=
    Restated.healthy_head_body_at_read_after_gst_admitOn facts S rho Hs Xb hf hHs hHsXb w p Ln
      (M.domain S.E S.hc r .g1) (M.domain S.E S.hc r .g0) (M.domain S.E S.hc r .g0)
      hwSrc hp hLnG1 hdeadline (le_refl _) ready.2 (by rw [hLnErase]; exact hFg0L)
  exact anchor_compatible_actionFGSource₆₄ facts S Hs Xb hf hHs hHsXb hr ready hactionHor
    hp hwG1 hn hselected hsource hLgrade1 ⟨Ln, hLnErase, hLnG0⟩ hFg0L hlo

end

/-! ## The vote steps of the source round and of later rounds -/

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open scoped DC
local macro "p63% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_63)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

/-- Along the bundle's path `W`, if `n` is a node state of `v`'s round-`r` action read and the
    action FG source of `n` can return `some B`, then the Q2 of `n` at round `r` can return `some A`
    for some block `A`. -/
private theorem nodeQ2_some_of_actionFGSource₆₄ (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} {Hs : Int → Finset V} {Xb : Finset V} {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} {r : Round} {B : Block V} (n : M.N)
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r)
    (hsource : Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n ⇢ some B) :
    ∃ A : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ some A := by
  have hsrc0 := nodeFGSource_of_actionFGSource₆₄ facts S hf n hn hsource
  unfold Restated.Vocabulary.Internal.PhaseGrades.nodeFGSource at hsrc0
  obtain ⟨A2, hA2, hsrc⟩ := (returns_bind_iff₆₄ _ _ _).1 hsrc0
  obtain ⟨Q2, hA2Q, -⟩ := facts.dt.fg_source_with_some _ _ _ _ _ _ hsrc rfl
  subst hA2Q
  obtain ⟨G, hG⟩ := facts.gr.read_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) r
  have hGQ : G.Q2 = some Q2 :=
    (facts.dt.grade2_block_with_eq_read_Q2 _ _ _ _ _ G hG _ hA2).symm
  have h : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ G.Q2 :=
    returns_map_intro₆₄ (fun g : GradeRead V => g.Q2) _ G _ hG rfl
  rw [hGQ] at h
  exact ⟨Q2, h⟩

/-- Under the bundle with path `W`, if the selector cone holds for `a`, then `0 < a.round`. -/
private theorem round_pos₆₄ (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} {Hs : Int → Finset V} {Xb : Finset V} {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {start first : Nat} {blocked : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg : NamedBlock V} {T : Block V}
    (hseed : Restated.PrefixFGSelectorConeAtOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs Xb start first blocked i a ta Cfg T) :
    0 < a.round := by
  obtain ⟨n₀, hn₀⟩ := actionReadFrom_nonempty₆₄ facts S
    (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round)) a.val_index)
    a.round
  obtain ⟨o, ho⟩ := actionFGSource_nonempty₆₄ facts S n₀
  have hsrc : Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n₀ ⇢ some Cfg.erase := by
    rw [← hseed.exactFGSource n₀ hn₀ o ho]
    exact ho
  obtain ⟨A, hA⟩ := nodeQ2_some_of_actionFGSource₆₄ facts S hf n₀ hn₀ hsrc
  exact Restated.selectedQ2_round_pos_named_historyOn facts S Hs Xb hf hn₀ hA

/-- Under the bundle with path `W` and the committee majorities, if the selector cone holds for `a`
    with checkpoint `T`, the frame and window over `X` hold up to `first`, round `a.round` is ready,
    `0 < s`, `lo ≤ vote_time s`, slot `s`'s confirmation instant is in the horizon,
    `vote_time (s + 1)` is before `first`, slot `s + 1` is in round `a.round`,
    `S.a a.round + Δ ≤ vote_time (s + 1)`, the slot-`s` votes of the set form a cone over `T`, and
    `lo ≤ opening (a.round − η_SG)`, then every member of the set for `vote_time (s + 1)` has every
    head of each of its vote-duty reads of `s + 1` a descendant of `T`, and the slot-`(s + 1)` votes
    of the set form a cone over `T`. -/
theorem PrefixFGSelectorConeAtOn.checkpointVoteStep_of_source_of_frame_named
    (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} {Hs : Int → Finset V} {Xb X : Finset V} {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hX : ∀ t : Int, 0 ≤ t → Hs t ⊆ X) (hXXb : X ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    {start first : Nat} {blocked : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg Tprev : NamedBlock V} {T : Block V} {c0 : Round}
    (hseed : Restated.PrefixFGSelectorConeAtOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs Xb start first blocked i a ta Cfg T)
    (hfirst : Restated.HeightWindowAtOn M S rho W X (blocked + 1) first)
    (hframe : Restated.NamedHeightRegimeFrameOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs X Xb blocked (first - 1) Tprev c0)
    (_hc0 : c0 ≤ a.round)
    (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho a.round)
    (_hpostPrev : S.E.t_GST ≤ Restated.Vocabulary.Execution.Setup.a M S (a.round - 1))
    {s : Slot} (hs : 0 < s)
    (hpost : lo ≤ M.vote_time S.E s)
    (hhor : M.confirmation_time S.E s ≤ rho.horizon)
    (hbefore : strictEventIndex rho (M.vote_time S.E (s + 1)) < first)
    (hsround : M.round_of S.hc (s + 1) = a.round)
    (hactionSettled : Restated.Vocabulary.Execution.Setup.a M S a.round + S.E.Δ ≤
      M.vote_time S.E (s + 1))
    (hvotes : Restated.NamedHonestVotesConeOn M S rho W Hs Xb s (fun Y => Block.Preceq T Y))
    (hlo : lo ≤ M.opening S.E S.hc (a.round - S.hc.η_SG)) :
    (∀ w ∈ Hs (M.vote_time S.E (s + 1)), ∀ c : M.Cache,
      M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.toHealing
        (M.vote_time S.E (s + 1))
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache ⇢ c →
      let n := M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
          (M.vote_time S.E (s + 1)))
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c
      ∀ Tr : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ Tr →
      ∀ L : Finset (GoldfishVote V),
        M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
      ∀ L' : Finset (GoldfishVote V),
        M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
      ∀ H : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
          (M.toHealing n.st.core) Tr L L' (n.st.core.s - 1) ⇢ H →
        Block.Preceq T H) ∧
      Restated.NamedHonestVotesConeOn M S rho W Hs Xb (s + 1) (fun Y => Block.Preceq T Y) := by
  have hactionHor : Restated.Vocabulary.Execution.Setup.a M S a.round ≤ rho.horizon :=
    actionHorizon₆₄ facts hf hseed
  have hopenA : M.opening S.E S.hc a.round ≤ Restated.Vocabulary.Execution.Setup.a M S a.round := by
    rw [← facts.gr.Sts_domain_g1_eq_opening S a.round]
    exact facts.gr.domain_le_a S a.round .g1
  have hloSource : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S a.round) :=
    hlo.trans ((facts.gr.NamedOutageClosure_opening_mono S (Nat.sub_le _ _)).trans hopenA)
  have hdelay : max ((Restated.Vocabulary.Execution.Setup.a M S a.round)) lo + S.E.Δ ≤
      M.vote_time S.E (s + 1) := by
    rw [max_eq_left hloSource]
    exact hactionSettled
  have hvoteHor : M.vote_time S.E (s + 1) ≤ rho.horizon :=
    le_trans (le_of_lt (lt_of_lt_of_le (Int.lt_add_of_pos_right _ S.E.Δ_pos)
      (facts.sch.vote_time_succ_add_delta_le_confirmation_time S.E s))) hhor
  have hreads := fun w (hw : w ∈ Hs (M.vote_time S.E (s + 1))) =>
    hseed.checkpointFiltered_at_laterRead_of_frame_named facts
      hf hHs hHsXb hX hXXb hfirst hframe hdelay hvoteHor hbefore hw hloSource
  obtain ⟨n₀, hn₀⟩ := actionReadFrom_nonempty₆₄ facts S
    (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round)) a.val_index)
    a.round
  obtain ⟨o, ho⟩ := actionFGSource_nonempty₆₄ facts S n₀
  have hsrc : Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n₀ ⇢ some Cfg.erase := by
    rw [← hseed.exactFGSource n₀ hn₀ o ho]
    exact ho
  obtain ⟨A, hA⟩ := nodeQ2_some_of_actionFGSource₆₄ facts S hf n₀ hn₀ hsrc
  have hr : 0 < a.round := Restated.selectedQ2_round_pos_named_historyOn facts S Hs Xb hf hn₀ hA
  have hTCfg : Block.Preceq T Cfg.erase := by
    rw [hseed.checkpointDerived]
    exact facts.csAdded.derive_named_T_h_preceq S.E S.cfg Cfg
  have hsigner : a.val_index ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S a.round)) := by
    have h := hseed.signerHonest
    rw [hseed.actionTime_eq] at h
    exact h
  have hsignerG0 : a.val_index ∈ Hs (M.domain S.E S.hc a.round .g0) :=
    hHs _ _ (facts.gr.domain_le_a S a.round .g0) hsigner
  have hslo : (M.opening_slot S.hc a.round) ≤ s + 1 := by
    rw [← hsround]
    exact facts.gr.opening_slot_round_of_le_slot S.hc (s + 1)
  have hshi : s + 1 < (M.opening_slot S.hc (a.round + 1)) := by
    rw [← hsround]
    exact facts.gr.lt_opening_slot_round_of_succ S.hc (s + 1)
  have hnext : M.vote_time S.E (s + 1) ≤ M.opening S.E S.hc (a.round + 1) :=
    (facts.sch.voteTime_lt_nextProposal_l86d S.E (s + 1)).le.trans (by
      rw [facts.gr.opening_eq_proposal_time]
      exact facts.sch.proposal_time_mono S.E (Nat.succ_le_iff.mpr hshi))
  have hanchors : ∀ w ∈ Hs (M.vote_time S.E (s + 1)), ∀ c : M.Cache,
      M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.toHealing
        (M.vote_time S.E (s + 1))
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache ⇢ c →
      ∀ A0 : Block V,
        Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S
          (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
            (M.vote_time S.E (s + 1))) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c)
          (M.round_of S.hc
            (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
              (M.vote_time S.E (s + 1)))
              (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c).st.core.s) ⇢ A0 →
        Block.compatible A0 T = true := by
    intro w hw c hc A0 hA0
    have hmemV := (p63% mem_stateBeforeTime_along₆₃) hf.sorted hf.onePath
      (M.vote_time S.E (s + 1))
    rcases Restated.Vocabulary.Proofs.HealingSurface.voterAnchorAt_cases facts S rho w
        (s + 1) _ ⟨_, hmemV, c, hc, rfl⟩ A0 hA0 with hroot | hactive
    · rw [hroot]
      refine compatible_of_cases (Or.inl ?_)
      rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [facts.hd.setClock_core_eq_store_with_t_s]
      exact (facts.fc.get_fg_root_set_clock_slot _ _ _).symm ▸ (hreads w hw).2.1
    · obtain ⟨root, L, hframeL, hactiveL, hanchorL⟩ := hactive
      subst hanchorL
      have hroundDuty : M.round_of S.hc
          (M.mkNode (M.ns_setClock S.E
            (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
            (M.vote_time S.E (s + 1)))
            (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record
            c).st.core.s = a.round := by
        rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [facts.hd.Sts_setClock_core_s, facts.sch.slotOf_vote_time]
        exact hsround
      rw [hroundDuty] at hframeL
      have hsourceCompat :=
        Restated.activeVoterAnchor_compatible_actionFGSource_at_interior_namedOn facts
          S Hs Xb hf hHs hHsXb hr ready hactionHor hsignerG0 hw hslo hsround
          hnext hvoteHor
          ((add_le_add (facts.gr.domain_le_a S a.round .g0)
            (le_refl S.E.Δ)).trans hactionSettled)
          hactionSettled hn₀ hA hsrc c hc hframeL hactiveL hlo
      rcases compatible_cases hsourceCompat with hLC | hCL
      · exact compatible_of_cases (preceq_linear_Preceq hLC hTCfg)
      · exact compatible_of_cases (Or.inr (preceq_trans_Preceq hTCfg hCL))
  have hwin : lo ≤ M.early S.E S.hc (M.round_of S.hc (s + 1)) .g1 - S.E.Δ := by
    rw [hsround]
    have h0 := facts.gr.lo_le_early_g2_of_window_start S hr hlo
    have h1 := facts.gr.early_g2_add_delta_le_early_g1 S a.round
    linarith
  exact hseed.checkpointVoteStep_of_anchors_of_frame_named facts
    hf hHs hHsXb hX hXXb hcom hfirst hframe hs hpost hhor hdelay hbefore hvotes hanchors
      hloSource (fun w _ hw j hj => hf.awake_g1 _ _ j _ (Or.inr rfl) hj hw hwin)

/-- Under the bundle with path `W`, if every round-`r` emitter of the set for `S.a r` has every SG
    block of its action reads compatible with `T`, `lo ≤ S.a r`, the phase-`p` domain instant of
    round `r + 1` is in the horizon, and every member of the set for that instant has, in `W`
    strictly before it, a finalized block that is an ancestor of `T`, then the relative carrier
    window holds along `W` at round `r` and phase `p`. -/
private theorem relativeCarrierWindow_of_storeF₆₄ (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} {Hs : Int → Finset V} {Xb : Finset V} {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    {T : Block V} {r : Round}
    (hsg : Restated.HonestSGEmissionsCompatibleAtRoundOn M S rho W
      (fun t => W (strictEventIndex rho t)) Hs r T)
    (hloR : lo ≤ Restated.Vocabulary.Execution.Setup.a M S r)
    (p : Phase)
    (hdomainHor : M.domain S.E S.hc (r + 1) p ≤ rho.horizon)
    (hFT : ∀ w ∈ Hs (M.domain S.E S.hc (r + 1) p), Block.Preceq
      (W (strictEventIndex rho (M.domain S.E S.hc (r + 1) p)) w).st.core.F T) :
    Restated.RelativeCarrierWindowAtOn M S rho W (fun t => W (strictEventIndex rho t)) Hs r p := by
  have hΔ := S.E.Δ_pos
  have hdeltaEarly : (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ ≤
      M.early S.E S.hc (r + 1) .g2 :=
    facts.gr.action_delta_le_early S S.hc.R_ge_three (Nat.lt_succ_self r)
  have hearlyP : M.early S.E S.hc (r + 1) .g2 ≤ M.early S.E S.hc (r + 1) p := by
    cases p with
    | g0 => exact facts.gr.early_g2_le_early_g0 S.E S.hc (r + 1)
    | g1 => exact facts.gr.early_g2_le_early_g1 S.E S.hc (r + 1)
    | g2 => exact le_rfl
  have horder : M.early S.E S.hc (r + 1) p ≤ M.domain S.E S.hc (r + 1) p := by
    have h := facts.gr.early_add_two_delta_le_domain S (r + 1) p
    linarith
  have hhorR : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ rho.horizon := by linarith
  have hcut : M.early S.E S.hc (r + 1) p ≤ rho.horizon := horder.trans hdomainHor
  have hk : r ∈ M.latest_window S.hc.η_SG (r + 1) := by
    apply facts.fc.mem_latest_window
    · simpa only [Nat.add_sub_cancel] using
        Nat.sub_le_sub_left S.hc.η_SG_ge_one (r + 1)
    · exact Nat.lt_succ_self r
  rw [Restated.RelativeCarrierWindowAtOn]
  intro w hw u hu huEarly na hna g2 hg2 A hAsel I hI
  have hna' : na ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) u) r := hna
  obtain ⟨huHon, b, hbval, hbround, hbemit⟩ :=
    (Restated.honestRoundVoters_iffOn facts S rho W hf.onePath Hs u r).mp hu
  have huXb : u ∈ Xb := hHsXb _ huHon
  have hawake : ∀ j : Nat, rho.events[j]? =
      some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S r)) →
      M.awake_for_grade2 S u (W j u) r := by
    have h := awake_g2_of_emits₆₄ facts hf hbemit
    rwa [hbround] at h
  obtain ⟨D, hD⟩ := facts.dt.attest_with_nonempty (M.gradeContract na.cache) S.E S.hc (S.node u)
    na.st na.record
  have hmemT := (Restated.stateBeforeTime_eq_stateBefore_strictEventIndexOn facts S Hs Xb hf
    (Restated.Vocabulary.Execution.Setup.a M S r)).symm ▸
      (hf.onePath (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r))).1
  have hshape : D.2.2.val_index = u ∧ D.2.2.round = r ∧ D.2.2.confirmed = some A.root :=
    Restated.Vocabulary.Proofs.HealingSurface.actionAttestationAt_shape facts S rho u r na
      ⟨_, hmemT, hna'⟩ D hD g2 hg2 A hAsel
  have hemit : Restated.Vocabulary.Execution.NamedRun.emits M S rho W u (Object.attest D.2.2)
      ((Restated.Vocabulary.Execution.Setup.a M S r)) :=
    Restated.honest_emits_exact_actionAttestationAt_of_awakeOn facts S Hs Xb hf r huHon hawake
      hhorR hloR (fun j hj => hf.tick_outcome j _ _ hj) na hna' D hD
  obtain ⟨j, hj, -, -, -, -, hhead⟩ :=
    Restated.Vocabulary.Proofs.NamedOutageInputs.emitted_attestation_head facts S rho W hf.onePath
      hemit
  have hstate := Restated.action_read_indexOn facts S rho Hs Xb hf j u r hj
  have hnaJ : na ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (W j u)
      D.2.2.round := by
    rcases hstate with h | h
    · rw [h, hshape.2.1]
      exact hna'
    · rw [h, actionReadFrom_wake₆₄ facts, hshape.2.1]
      exact hna'
  obtain ⟨Hb, hHb, hconfirmed⟩ := hhead na hnaJ
  have hbodies := actionReadFrom_bodies₆₄ facts S _ r na hna'
  have hAmem : A ∈
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) u).st.core.T :=
    Restated.Vocabulary.Proofs.HealingSurface.actionSGBlockAt_mem_storeBeforeTime facts S rho u r
      _ hmemT na hna' g2 hg2 A hAsel
  obtain ⟨Dn, hDnBody, hDnErase⟩ :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore facts S rho
      (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) u _
      (hf.onePath _).1 hAmem
  have hDnRun : Restated.RunBlockOn M S rho W Xb Dn :=
    Restated.runBlock_of_stateBefore_memOn facts S W Xb huXb hDnBody
  have hHbRun : Restated.RunBlockOn M S rho W Xb Hb :=
    Restated.runBlock_of_stateBefore_memOn facts S W Xb huXb (by rw [← hbodies]; exact hHb)
  have hroot : Dn.root = Hb.root := by
    rw [← Proofs.NamedWire.erase_root Dn, hDnErase]
    exact Option.some.inj (hshape.2.2.symm.trans hconfirmed)
  have hDH : Dn = Hb :=
    hf.rootCollisionFree.root_injective Dn Hb hDnRun hHbRun Dn Hb
      (Or.inl (Proofs.NamedAncestry.named_self Dn))
      (Or.inr (Proofs.NamedAncestry.named_self Hb)) hroot
  have hHbErase : Hb.erase = A := by
    rw [← hDH, hDnErase]
  have hHbRoot : Hb.root = A.root := by
    rw [← Proofs.NamedWire.erase_root Hb, hHbErase]
  have hcarrierT : Block.compatible Hb.erase T = true := by
    rw [hHbErase]
    exact hsg u huHon na hna D hD hemit g2 hg2 A hAsel
  have hFTw : Block.Preceq
      (W (strictEventIndex rho (M.domain S.E S.hc (r + 1) p)) w).st.core.F T := hFT w hw
  have hpostA : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S D.2.2.round) := by
    rw [hshape.2.1]
    exact hloR
  have hdeadline : max ((Restated.Vocabulary.Execution.Setup.a M S D.2.2.round)) lo + S.E.Δ ≤
      M.early S.E S.hc (r + 1) p := by
    rw [hshape.2.1, max_eq_left hloR]
    exact hdeltaEarly.trans hearlyP
  have hwEarly : w ∈ Hs (M.early S.E S.hc (r + 1) p) := hHs _ _ horder hw
  have hexact : ∀ {C : Block V}, Block.Preceq Hb.erase C →
      Block.Preceq (W (strictEventIndex rho (M.domain S.E S.hc (r + 1) p)) w).st.core.F C →
      ∃ y ∈ I, y.round = r ∧ y.confirmed = some A.root ∧
        Block.find? (W (strictEventIndex rho (M.domain S.E S.hc (r + 1) p)) w).st.core.T A.root =
          some A := by
    intro C hHC hFC
    have h := Restated.interpretedInputs_exact_of_honest_window_vote_after_gst_common_upperOn facts
      S Hs Xb hf hHs hHsXb (t := M.domain S.E S.hc (r + 1) p) p hk huEarly hwEarly
      ⟨hshape.1, hshape.2.1, hemit⟩ ⟨j, hj, ⟨na, hnaJ, hHb⟩, hconfirmed⟩ hHC hFC hpostA
      hdeadline horder hcut I hI
    rw [hHbErase, hHbRoot] at h
    exact h
  rcases (show Block.Preceq Hb.erase T ∨ Block.Preceq T Hb.erase from
    compatible_cases hcarrierT) with hHbT | hTHb
  · exact hexact hHbT hFTw
  · exact hexact (Proofs.ModelProperties.Preceq_self Hb.erase) (preceq_trans_Preceq hFTw hTHb)

/-- Under the bundle with path `W`, the committee majorities and the weight bound, if the selector
    cone holds for `a` with checkpoint `T`, the frame and window over `X` hold up to `first`,
    `0 < s`, `lo ≤ vote_time s`, slot `s`'s confirmation instant is in the horizon,
    `vote_time (s + 1)` is before `first`, `a.round + 1 ≤ round_of (s + 1)`, the slot-`s` votes of
    the set form a cone over `T`, every round-`(round_of (s + 1) − 1)` emitter of the set has every
    SG block of its action reads compatible with `T`, `lo ≤ opening (a.round − η_SG)`, and every
    member of the set for that round's action instant plus `Δ` is awake at that round, then every
    member of the set for `vote_time (s + 1)` has every head of each of its vote-duty reads of
    `s + 1` a descendant of `T`, and the slot-`(s + 1)` votes of the set form a cone over `T`. -/
theorem PrefixFGSelectorConeAtOn.checkpointVoteStep_of_previousSGHistory_of_frame_named
    (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} {Hs : Int → Finset V} {Xb X : Finset V} {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hX : ∀ t : Int, 0 ≤ t → Hs t ⊆ X) (hXXb : X ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hfb : BelowOneThirdOn S rho Hs)
    {start first : Nat} {blocked : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg Tprev : NamedBlock V} {T : Block V} {c0 : Round}
    (hseed : Restated.PrefixFGSelectorConeAtOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs Xb start first blocked i a ta Cfg T)
    (hfirst : Restated.HeightWindowAtOn M S rho W X (blocked + 1) first)
    (hframe : Restated.NamedHeightRegimeFrameOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs X Xb blocked (first - 1) Tprev c0)
    (_ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho a.round)
    {s : Slot} (hs : 0 < s)
    (hpost : lo ≤ M.vote_time S.E s)
    (hhor : M.confirmation_time S.E s ≤ rho.horizon)
    (_hread : Restated.Vocabulary.Execution.Setup.a M S a.round ≤ M.vote_time S.E (s + 1))
    (hbefore : strictEventIndex rho (M.vote_time S.E (s + 1)) < first)
    (hc : a.round + 1 ≤ M.round_of S.hc (s + 1))
    (hvotes : Restated.NamedHonestVotesConeOn M S rho W Hs Xb s (fun Y => Block.Preceq T Y))
    (hsg : Restated.HonestSGEmissionsCompatibleAtRoundOn M S rho W
      (fun t => W (strictEventIndex rho t)) Hs (M.round_of S.hc (s + 1) - 1) T)
    (hlo : lo ≤ M.opening S.E S.hc (a.round - S.hc.η_SG))
    (hA : ∀ u ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S (M.round_of S.hc (s + 1) - 1) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S (M.round_of S.hc (s + 1) - 1))) → M.awake_for_grade2 S u (W j u) (M.round_of S.hc (s + 1) - 1)) :
    (∀ w ∈ Hs (M.vote_time S.E (s + 1)), ∀ c : M.Cache,
      M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.toHealing
        (M.vote_time S.E (s + 1))
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache ⇢ c →
      let n := M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
          (M.vote_time S.E (s + 1)))
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c
      ∀ Tr : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ Tr →
      ∀ L : Finset (GoldfishVote V),
        M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
      ∀ L' : Finset (GoldfishVote V),
        M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
      ∀ H : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
          (M.toHealing n.st.core) Tr L L' (n.st.core.s - 1) ⇢ H →
        Block.Preceq T H) ∧
      Restated.NamedHonestVotesConeOn M S rho W Hs Xb (s + 1) (fun Y => Block.Preceq T Y) := by
  have hΔ := S.E.Δ_pos
  obtain ⟨c, hcdef⟩ : ∃ c, c = M.round_of S.hc (s + 1) := ⟨_, rfl⟩
  obtain ⟨q, hqdef⟩ : ∃ q, q = c - 1 := ⟨_, rfl⟩
  rw [← hcdef] at hc hsg hA
  rw [← hqdef] at hsg hA
  have hcPos : 1 ≤ c := (Nat.succ_le_succ (Nat.zero_le a.round)).trans hc
  have hqSucc : q + 1 = c := by rw [hqdef]; exact Nat.sub_add_cancel hcPos
  have haQ : a.round ≤ q := by rw [hqdef]; exact Nat.le_sub_one_of_lt (Nat.lt_of_succ_le hc)
  have hopenA : M.opening S.E S.hc a.round ≤ Restated.Vocabulary.Execution.Setup.a M S a.round := by
    rw [← facts.gr.Sts_domain_g1_eq_opening S a.round]
    exact facts.gr.domain_le_a S a.round .g1
  have hloSource : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S a.round) :=
    hlo.trans ((facts.gr.NamedOutageClosure_opening_mono S (Nat.sub_le _ _)).trans hopenA)
  have hloQ : lo ≤ Restated.Vocabulary.Execution.Setup.a M S q :=
    hloSource.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S haQ)
  have hvoteHor : M.vote_time S.E (s + 1) ≤ rho.horizon :=
    le_trans (le_of_lt (lt_of_lt_of_le (Int.lt_add_of_pos_right _ S.E.Δ_pos)
      (facts.sch.vote_time_succ_add_delta_le_confirmation_time S.E s))) hhor
  have hslo : M.opening_slot S.hc c ≤ s + 1 := by
    rw [hcdef]
    exact facts.gr.opening_slot_round_of_le_slot S.hc (s + 1)
  have hdomainVote : M.domain S.E S.hc c .g1 ≤ M.vote_time S.E (s + 1) := by
    rw [facts.gr.Sts_domain_g1_eq_opening S c, facts.gr.opening_eq_proposal_time]
    exact (facts.sch.proposal_time_mono S.E hslo).trans
      (facts.sch.proposal_time_lt_vote_time S.E (s + 1)).le
  have hdomainHor : M.domain S.E S.hc c .g1 ≤ rho.horizon := hdomainVote.trans hvoteHor
  have hdomainBefore : strictEventIndex rho (M.domain S.E S.hc c .g1) < first :=
    (strictEventIndex_mono rho hdomainVote).trans_lt hbefore
  have hearlyDomain : M.early S.E S.hc c .g2 ≤ M.domain S.E S.hc c .g1 :=
    (facts.gr.early_g2_le_early_g1 S.E S.hc c).trans (facts.gr.early_g1_le_domain_g1 S c)
  have hphaseDelay : max ((Restated.Vocabulary.Execution.Setup.a M S a.round)) lo + S.E.Δ ≤
      M.domain S.E S.hc c .g1 := by
    rw [max_eq_left hloSource]
    exact (facts.gr.action_delta_le_early S S.hc.R_ge_three
      (Nat.lt_of_succ_le hc)).trans hearlyDomain
  have hsourceDelay : max ((Restated.Vocabulary.Execution.Setup.a M S a.round)) lo + S.E.Δ ≤
      M.vote_time S.E (s + 1) := hphaseDelay.trans hdomainVote
  have hreads := fun w (hw : w ∈ Hs (M.vote_time S.E (s + 1))) =>
    hseed.checkpointFiltered_at_laterRead_of_frame_named facts
      hf hHs hHsXb hX hXXb hfirst hframe hsourceDelay hvoteHor hbefore hw hloSource
  have hqc : q < c := by rw [← hqSucc]; exact Nat.lt_succ_self q
  subst hqSucc
  have hwindow : Restated.RelativeCarrierWindowAtOn M S rho W
      (fun t => W (strictEventIndex rho t)) Hs q .g1 := by
    refine relativeCarrierWindow_of_storeF₆₄ facts hf hHs hHsXb hsg hloQ .g1 hdomainHor ?_
    intro w hw
    have hread := hseed.checkpointFiltered_at_laterRead_of_frame_named facts
      hf hHs hHsXb hX hXXb hfirst hframe hphaseDelay hdomainHor hdomainBefore hw hloSource
    have h := facts.fc.q10_filtered_F hread.2.2
    rw [facts.sto.Sts_toHealing_F] at h
    exact h
  have hprevt : Restated.Vocabulary.Execution.Setup.a M S (q + 1 - 1) + S.E.Δ ≤
      M.domain S.E S.hc (q + 1) .g1 := by
    rw [Nat.add_sub_cancel]
    exact (facts.gr.action_delta_le_early S S.hc.R_ge_three hqc).trans hearlyDomain
  have hmajority : Restated.GradeFormingMajorityOn M S rho W Hs
      (Hs (M.domain S.E S.hc (q + 1) .g1)) (q + 1) :=
    Restated.gradeFormingMajority_of_admissible_belowOneThirdOn facts S Hs Xb hf hHs hfb
      (r := q + 1) (Nat.succ_pos q) hprevt hdomainHor
      (by rw [Nat.add_sub_cancel]; exact hloQ)
      (by rw [Nat.add_sub_cancel]; exact hA)
  have hloG1 : lo ≤ M.domain S.E S.hc (q + 1) .g1 := by
    have h := hprevt
    rw [Nat.add_sub_cancel] at h
    linarith
  have hanchors : ∀ w ∈ Hs (M.vote_time S.E (s + 1)), ∀ c : M.Cache,
      M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core.toHealing
        (M.vote_time S.E (s + 1))
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache ⇢ c →
      ∀ A0 : Block V,
        Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S
          (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
            (M.vote_time S.E (s + 1))) (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c)
          (M.round_of S.hc
            (M.mkNode (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
              (M.vote_time S.E (s + 1)))
              (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c).st.core.s) ⇢ A0 →
        Block.compatible A0 T = true := by
    intro w hw cc hcc
    have hroot : Block.Preceq
        (M.get_fg_root (M.toHealing (M.ns_setClock S.E
          (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
          (M.vote_time S.E (s + 1))).core).toFG) T := by
      rw [facts.hd.setClock_core_eq_store_with_t_s]
      exact (facts.fc.get_fg_root_set_clock_slot _ _ _).symm ▸ (hreads w hw).2.1
    exact Restated.voterAnchorAt_compatible_of_previousRelativeCarrierOn facts S Hs Xb
      (Hs (M.domain S.E S.hc (q + 1) .g1)) hf hHs hcdef.symm hvoteHor hwindow hmajority
      (subset_refl _) hsg (hHs _ _ hdomainVote hw) cc hcc hroot hloG1
  have hwin : lo ≤ M.early S.E S.hc (M.round_of S.hc (s + 1)) .g1 - S.E.Δ := by
    have hlt : a.round < M.round_of S.hc (s + 1) := by
      rw [← hcdef]
      exact Nat.lt_of_succ_le hc
    have h0 := facts.gr.action_delta_le_early S S.hc.R_ge_three hlt
    have h1 := facts.gr.early_g2_add_delta_le_early_g1 S (M.round_of S.hc (s + 1))
    have hΔ0 := S.E.Δ_pos
    linarith
  exact hseed.checkpointVoteStep_of_anchors_of_frame_named facts
    hf hHs hHsXb hX hXXb hcom hfirst hframe hs hpost hhor hsourceDelay hbefore hvotes
      hanchors hloSource (fun w _ hw j hj => hf.awake_g1 _ _ j _ (Or.inr rfl) hj hw hwin)

end

/-! ## `PrefixFGSelectorConeAtOn.sgEmissionsCompatible_laterRound_of_frame_named` -/

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open scoped DC
local macro "p63% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_63)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

omit [Fintype V] in
/-- An ancestor of a block compatible with `T` is compatible with `T`. -/
private theorem compatible_ancestor_left₆₄ {A B T : Block V} (hAB : Block.Preceq A B)
    (hBT : Block.compatible B T = true) : Block.compatible A T = true := by
  rcases compatible_cases hBT with hBT | hTB
  · exact compatible_of_cases (Or.inl (preceq_trans_Preceq hAB hBT))
  · exact compatible_of_cases (preceq_linear_Preceq hAB hTB)

/-- Under the bundle with path `W`, the committee majorities and the weight bound, if the selector
    cone holds for `a` with checkpoint `T`, the named frame over `X` holds at `blocked` up to
    `first − 1`, round `a.round` is ready, `a.round ≤ r`, every round-`r` emitter of the set for
    `S.a r` has every SG block of its action reads compatible with `T`, every member of the next
    opening slot's committee in the set for its vote instant votes a head descending from `T`,
    `S.a (r + 1)` is in the horizon and before `first`, `lo ≤ opening (a.round − η_SG)`, and every
    member of the set for `S.a r + Δ` is awake at `r`, then every round-`(r + 1)` emitter of the set
    for `S.a (r + 1)` has every SG block of its action reads compatible with `T`. -/
theorem PrefixFGSelectorConeAtOn.sgEmissionsCompatible_laterRound_of_frame_named
    (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} {Hs : Int → Finset V} {Xb X : Finset V} {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hX : ∀ t : Int, 0 ≤ t → Hs t ⊆ X)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hfb : BelowOneThirdOn S rho Hs)
    {start first : Nat} {blocked : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg Tprev : NamedBlock V} {T : Block V} {c0 : Round}
    (hseed : Restated.PrefixFGSelectorConeAtOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs Xb start first blocked i a ta Cfg T)
    (_hfirst : Restated.HeightWindowAtOn M S rho W X (blocked + 1) first)
    (hframe : Restated.NamedHeightRegimeFrameOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs X Xb blocked (first - 1) Tprev c0)
    (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho a.round)
    {r : Round} (hr : a.round ≤ r)
    (hsg : Restated.HonestSGEmissionsCompatibleAtRoundOn M S rho W
      (fun t => W (strictEventIndex rho t)) Hs r T)
    (hgf : Restated.NamedHonestVotesConeOn M S rho W Hs Xb (M.opening_slot S.hc (r + 1))
      (fun Y => Block.Preceq T Y))
    (hhor : Restated.Vocabulary.Execution.Setup.a M S (r + 1) ≤ rho.horizon)
    (hbefore : strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) < first)
    (hlo : lo ≤ M.opening S.E S.hc (a.round - S.hc.η_SG))
    (hA : ∀ u ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S r + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S r)) → M.awake_for_grade2 S u (W j u) r) :
    Restated.HonestSGEmissionsCompatibleAtRoundOn M S rho W
      (fun t => W (strictEventIndex rho t)) Hs (r + 1) T := by
  have hΔ := S.E.Δ_pos
  have hopenA : M.opening S.E S.hc a.round ≤ Restated.Vocabulary.Execution.Setup.a M S a.round := by
    rw [← facts.gr.Sts_domain_g1_eq_opening S a.round]
    exact facts.gr.domain_le_a S a.round .g1
  have hloSource : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S a.round) :=
    hlo.trans ((facts.gr.NamedOutageClosure_opening_mono S (Nat.sub_le _ _)).trans hopenA)
  have haR : Restated.Vocabulary.Execution.Setup.a M S a.round ≤
      Restated.Vocabulary.Execution.Setup.a M S r :=
    Restated.Vocabulary.Proofs.Assembly.a_mono facts S hr
  have hloR : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S r) := hloSource.trans haR
  have hpostSource : S.E.t_GST ≤ Restated.Vocabulary.Execution.Setup.a M S a.round :=
    ready.1.trans ((facts.gr.early_le_domain S a.round).trans
      (facts.gr.domain_le_a S a.round .g2))
  have hpost : S.E.t_GST ≤ Restated.Vocabulary.Execution.Setup.a M S r := hpostSource.trans haR
  have haRR : Restated.Vocabulary.Execution.Setup.a M S r ≤
      Restated.Vocabulary.Execution.Setup.a M S (r + 1) :=
    Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.le_succ r)
  have hhorR : (Restated.Vocabulary.Execution.Setup.a M S r) ≤ rho.horizon := haRR.trans hhor
  have hactionPrefix :
      strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) ≤ first - 1 :=
    Nat.le_sub_one_of_lt hbefore
  obtain ⟨n₀, hn₀⟩ := actionReadFrom_nonempty₆₄ facts S
    (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round)) a.val_index)
    a.round
  obtain ⟨K, hKsource, hKT, hKheight, hKrun, hTprevK⟩ :=
    hseed.namedCheckpoint_l64 facts hf hHsXb hX hframe n₀ hn₀
  have hsigner : a.val_index ∈ Hs ((Restated.Vocabulary.Execution.Setup.a M S a.round)) := by
    have h := hseed.signerHonest
    rw [hseed.actionTime_eq] at h
    exact h
  have hdeltaEarly : (Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ ≤
      M.early S.E S.hc (r + 1) .g2 :=
    facts.gr.action_delta_le_early S S.hc.R_ge_three (Nat.lt_succ_self r)
  have hearlyG1 : M.early S.E S.hc (r + 1) .g2 ≤ M.domain S.E S.hc (r + 1) .g1 :=
    (facts.gr.early_g2_le_early_g1 S.E S.hc (r + 1)).trans
      (facts.gr.early_g1_le_domain_g1 S (r + 1))
  have hG1A : M.domain S.E S.hc (r + 1) .g1 ≤ Restated.Vocabulary.Execution.Setup.a M S (r + 1) :=
    facts.gr.domain_le_a S (r + 1) .g1
  have hG1Hor : M.domain S.E S.hc (r + 1) .g1 ≤ rho.horizon := hG1A.trans hhor
  have hrNonneg := a_nonneg₆₄ facts S r
  have hfloor : ∀ (t : Int), 0 ≤ t → t ≤ Restated.Vocabulary.Execution.Setup.a M S (r + 1) →
      ∀ w ∈ Hs t, Block.Preceq (W (strictEventIndex rho t) w).st.core.F T := by
    intro t ht0 htA w hw
    rw [← hKT]
    exact hframe.floor w (hX _ ht0 hw) _ ((strictEventIndex_mono rho htA).trans hactionPrefix)
      K hKrun (by rw [hKheight]; exact Nat.le_succ blocked) hTprevK
  have hwindow : Restated.RelativeCarrierWindowAtOn M S rho W
      (fun t => W (strictEventIndex rho t)) Hs r .g1 :=
    relativeCarrierWindow_of_storeF₆₄ facts hf hHs hHsXb hsg hloR .g1 hG1Hor
      (hfloor _ (by linarith) hG1A)
  have hdeltaG1 : Restated.Vocabulary.Execution.Setup.a M S (r + 1 - 1) + S.E.Δ ≤
      M.domain S.E S.hc (r + 1) .g1 := by
    rw [Nat.add_sub_cancel]
    exact hdeltaEarly.trans hearlyG1
  have hmajority : Restated.GradeFormingMajorityOn M S rho W Hs
      (Hs (M.domain S.E S.hc (r + 1) .g1)) (r + 1) :=
    Restated.gradeFormingMajority_of_admissible_belowOneThirdOn facts S Hs Xb hf hHs hfb
      (r := r + 1) (Nat.succ_pos r) hdeltaG1 hG1Hor
      (by rw [Nat.add_sub_cancel]; exact hloR)
      (by rw [Nat.add_sub_cancel]; exact hA)
  have hKsourcePre : K ∈
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round))
        a.val_index).st.bodies := by
    rw [← actionReadFrom_bodies₆₄ facts S _ a.round n₀ hn₀]
    exact hKsource
  have hsourceDeadline : max ((Restated.Vocabulary.Execution.Setup.a M S a.round)) lo + S.E.Δ ≤
      Restated.Vocabulary.Execution.Setup.a M S (r + 1) := by
    rw [max_eq_left hloSource]
    linarith
  have hsignerSrc : a.val_index ∈
      Hs (max ((Restated.Vocabulary.Execution.Setup.a M S a.round)) lo) := by
    rw [max_eq_left hloSource]
    exact hsigner
  have hrNextNonneg := a_nonneg₆₄ facts S (r + 1)
  have hrootW : ∀ w ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S (r + 1)),
      Block.Preceq (M.get_fg_root (M.toHealing
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (r + 1))) w).st.core).toFG)
        T := by
    intro w hw
    have hwX : w ∈ X := hX _ hrNextNonneg hw
    have hFActionK : Block.Preceq
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (r + 1))) w).st.core.F
        K.erase := by
      rw [hKT]
      exact hfloor _ hrNextNonneg le_rfl w hw
    obtain ⟨hKtarget, -, -⟩ :=
      Restated.healthy_head_body_at_read_after_gst_admitOn facts S rho Hs Xb hf hHs hHsXb
        a.val_index w K (Restated.Vocabulary.Execution.Setup.a M S a.round)
        (Restated.Vocabulary.Execution.Setup.a M S (r + 1))
        (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) hsignerSrc hw
        hKsourcePre hsourceDeadline (le_refl _) hhor hFActionK
    rw [← hKT]
    exact hframe.rootBelow w hwX _ hactionPrefix K hKtarget hKheight hTprevK
  have readyNext : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho (r + 1) :=
    ⟨hpost.trans (by linarith), (facts.gr.domain_le_a S (r + 1) .g0).trans hhor⟩
  obtain ⟨_, hvt1, hsc1, _, _, hact1⟩ := Restated.openingInstants_l63 facts S (r + 1)
  have hopenProp : M.domain S.E S.hc (r + 1) .g1 =
      M.proposal_time S.E (M.opening_slot S.hc (r + 1)) := by
    rw [facts.gr.Sts_domain_g1_eq_opening S (r + 1), facts.gr.opening_eq_proposal_time]
  have hopenPost : lo ≤ M.vote_time S.E (M.opening_slot S.hc (r + 1)) := by linarith
  have hwinNext : lo ≤ M.early S.E S.hc (M.round_of S.hc (M.opening_slot S.hc (r + 1))) .g1 -
      S.E.Δ := by
    rw [facts.gr.round_of_opening_slot_eq S.hc (r + 1)]
    have h1 := facts.gr.early_g2_add_delta_le_early_g1 S (r + 1)
    linarith
  have hconfHor : M.confirmation_time S.E (M.opening_slot S.hc (r + 1)) ≤ rho.horizon := by
    rw [Restated.Vocabulary.Proofs.HealingSurface.opening_confirmation_time_eq_action facts S (r + 1)]
    exact hhor
  have hopen : 0 < M.opening_slot S.hc (r + 1) := facts.gr.opening_slot_pos S (Nat.succ_pos r)
  have hvoteConf : M.vote_time S.E (M.opening_slot S.hc (r + 1)) ≤
      M.confirmation_time S.E (M.opening_slot S.hc (r + 1)) :=
    facts.sch.Protocol_vote_time_le_confirmation_time S.E _
  have hheads : ∀ x ∈ Hs (M.confirmation_time S.E (M.opening_slot S.hc (r + 1))),
      x ∈ S.E.committee (M.opening_slot S.hc (r + 1)) →
      ∃ c : M.Cache, M.onPhaseTick S.E S.hc
          (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc (r + 1)))) x).st.core.toHealing
          (M.vote_time S.E (M.opening_slot S.hc (r + 1)))
          (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc (r + 1)))) x).cache ⇢ c ∧
      let n := M.mkNode
        (M.ns_setClock S.E
          (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc (r + 1)))) x).st
          (M.vote_time S.E (M.opening_slot S.hc (r + 1))))
        (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc (r + 1)))) x).record c
      ∃ Tr : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ Tr ∧
      ∃ L : Finset (GoldfishVote V),
        M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L ∧
      ∃ L' : Finset (GoldfishVote V),
        M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' ∧
      ∃ H : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
          (M.toHealing n.st.core) Tr L L' (n.st.core.s - 1) ⇢ H ∧
        Block.Preceq T H := by
    intro x hx hxc
    have hxVote : x ∈ Hs (M.vote_time S.E (M.opening_slot S.hc (r + 1))) :=
      hHs _ _ hvoteConf hx
    obtain ⟨Y, hTY, hYrun, hYemit⟩ := hgf x hxVote hxc
    obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc
      (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc (r + 1)))) x).st.core.toHealing
      (M.vote_time S.E (M.opening_slot S.hc (r + 1)))
      (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc (r + 1)))) x).cache
    refine ⟨c, hc, ?_⟩
    intro n
    obtain ⟨Tr, hTr⟩ := facts.fc.voter_filtered_block_tree_nonempty S.E n.st.core n.st.core.s
    obtain ⟨L, hL⟩ := facts.fc.voter_view_nonempty S.E
      (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s
    obtain ⟨L', hL'⟩ := facts.fc.voter_support_view_nonempty S.E
      (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s
    obtain ⟨Hd, hHd⟩ := facts.fc.get_head_in_tree_with_layer_nonempty (M.gradeContract n.cache)
      S.E S.hc (M.toHealing n.st.core) Tr L L' (n.st.core.s - 1)
    obtain ⟨H, hHerase, hHrun, hHemit⟩ :=
      Restated.voterHead_runBlock_and_emitsOn facts S Hs Xb hf hHsXb hxVote hopen hxc
        (hvoteConf.trans hconfHor) hopenPost c hc
        (fun j hj => hf.awake_g1 _ _ j _ (Or.inr rfl) hj hxVote hwinNext) Tr hTr L hL L' hL' Hd hHd
    have heq := Restated.emits_gfVote_uniqueOn facts S Hs Xb hf hYemit hHemit rfl
    have hroot : Y.root = H.root := by
      simpa only [Proofs.NamedWire.erase_root] using congrArg GoldfishVote.head heq
    have hYH : Y = H := hf.rootCollisionFree.root_injective
      Y H hYrun hHrun Y H (Or.inl (Proofs.NamedAncestry.named_self Y))
        (Or.inr (Proofs.NamedAncestry.named_self H)) hroot
    refine ⟨Tr, hTr, L, hL, L', hL', Hd, hHd, ?_⟩
    rw [← hHerase, ← hYH]
    exact hTY
  have hloEarly : lo ≤ M.early S.E S.hc (r + 1) .g2 := by linarith
  have hloOpen : lo ≤ M.opening S.E S.hc (r + 1 - S.hc.η_SG) :=
    hlo.trans (facts.gr.NamedOutageClosure_opening_mono S
      (Nat.sub_le_sub_right (Nat.le_succ_of_le hr) _))
  rw [Restated.HonestSGEmissionsCompatibleAtRoundOn]
  intro w hw n hn D hD _
  dsimp only
  intro A2 hA2 G hG
  have hn' : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (r + 1))) w) (r + 1) := hn
  have hmemA := (p63% mem_stateBeforeTime_along₆₃) hf.sorted hf.onePath
    (Restated.Vocabulary.Execution.Setup.a M S (r + 1))
  have hnAt : n ∈ Restated.Vocabulary.Proofs.HealingSurface.actionReadAt M S rho w (r + 1) :=
    ⟨_, hmemA, hn'⟩
  have hwSC : w ∈ Hs (M.support_cutoff S.E (M.opening_slot S.hc (r + 1))) :=
    hHs _ _ (by linarith) hw
  have hwG1 : w ∈ Hs (M.domain S.E S.hc (r + 1) .g1) := hHs _ _ hG1A hw
  have hrootN : Block.Preceq (M.get_fg_root (M.toHealing n.st.core).toFG) T := by
    rw [Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt_fgRoot_eq_storeBeforeTime facts S rho
      w (r + 1) _ hmemA n hn']
    exact hrootW w hw
  have hrootT : Block.compatible (M.get_fg_root (M.toHealing n.st.core).toFG) T = true :=
    compatible_of_cases (Or.inl hrootN)
  have hliveT : Block.compatible n.st.core.live_confirmed T = true := by
    rcases Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt_liveConfirmed_genuine_or_fgRoot
        facts S rho w (r + 1) _ hmemA n hn' with ⟨C, hC, hClive⟩ | ⟨R, hRroot, hRlive⟩
    · rw [← hClive]
      obtain ⟨c, hc, st, hst, rfl⟩ := hn'
      rw [facts.nd.mkNode_cache] at hC
      rw [← Restated.Vocabulary.Proofs.HealingSurface.opening_confirmation_time_eq_action facts S
        (r + 1)] at hc hC
      exact Protocol.compatible_comm
        (Restated.genuineConfirmation_compatible_of_priorProtectedHeadsOn facts
          S Hs Xb hf hHs hHsXb hcom hwSC hopen hopenPost hconfHor c hc hC hheads
          (fun x _ hxH j hj => hf.awake_g1 _ _ j _ (Or.inr rfl) hj
            (hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E _) hxH) hwinNext))
    · rw [← hRlive, hRroot, Restated.Vocabulary.Proofs.Optimistic.tickStore]
      exact compatible_of_cases (Or.inl
        ((facts.fc.get_fg_root_set_clock_slot _ _ _).symm ▸ hrootW w hw))
  obtain ⟨g, hg⟩ := facts.gr.read_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) (r + 1)
  have hgRead : Restated.Vocabulary.Internal.PhaseGrades.nodeRead M S n (r + 1) ⇢ g := hg
  have hanchorT : Block.compatible g.anchor T = true := by
    obtain ⟨an, han⟩ := facts.gr.anchor_nonempty S.E S.hc (M.toHealing n.st.core) (r + 1)
      (M.readFrame n.cache (M.toHealing n.st.core) (r + 1)).g1
    rw [facts.nd.ModelProperties_gradeContract_read_anchor n.cache S.E S.hc
      (M.toHealing n.st.core) (r + 1) g hg an han]
    rcases facts.gr.anchor_cases S.E S.hc _ _ _ an han with
      hroot | ⟨root, L, hframeL, hactiveL, hanchorL⟩
    · rw [hroot]
      exact hrootT
    · rw [hanchorL]
      have hLgrade := Restated.activeActionAnchor_storeGrade_g1_named_historyOn facts
        S Hs Xb hf (Nat.succ_pos r) readyNext hwG1 hn' hframeL hactiveL hloEarly
      obtain ⟨bL, hbL⟩ := facts.gr.gradeBool_nonempty S.E
        (M.gradeView (M.toHealing
          (W (strictEventIndex rho (M.domain S.E S.hc (r + 1) .g1)) w).st.core))
        (W (strictEventIndex rho (M.domain S.E S.hc (r + 1) .g1)) w).st.core.F
        S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) .g1) (M.late S.E S.hc (r + 1) .g1) L
      have hbLt : bL = true := hLgrade bL hbL
      subst hbLt
      obtain ⟨u, hu, hLu⟩ := Restated.relativeGrade_has_roundCarrierOn facts
        S Hs Xb (Hs (M.domain S.E S.hc (r + 1) .g1)) hf hHs hwindow hmajority
          (subset_refl _) hwG1 hbL
      obtain ⟨huHon, b, _, hbround, hbemit⟩ :=
        (Restated.honestRoundVoters_iffOn facts S rho W hf.onePath Hs u r).mp hu
      have hawake : ∀ j : Nat, rho.events[j]? =
          some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S r)) →
          M.awake_for_grade2 S u (W j u) r := by
        have h := awake_g2_of_emits₆₄ facts hf hbemit
        rwa [hbround] at h
      obtain ⟨nu, hnu⟩ := actionReadFrom_nonempty₆₄ facts S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) u) r
      obtain ⟨Du, hDu⟩ := facts.dt.attest_with_nonempty (M.gradeContract nu.cache) S.E S.hc
        (S.node u) nu.st nu.record
      have hemitU : Restated.Vocabulary.Execution.NamedRun.emits M S rho W u
          (Object.attest Du.2.2) ((Restated.Vocabulary.Execution.Setup.a M S r)) :=
        Restated.honest_emits_exact_actionAttestationAt_of_awakeOn facts S Hs Xb hf r huHon
          hawake hhorR hloR (fun j hj => hf.tick_outcome j _ _ hj) nu hnu Du hDu
      obtain ⟨A2u, hA2u⟩ := facts.dt.grade2_block_with_nonempty (M.gradeContract nu.cache) S.E
        S.hc (M.toHealing nu.st.core) (M.round_of S.hc (M.toHealing nu.st.core).s)
      obtain ⟨Bu, hBu⟩ := facts.dt.get_sg_vote_with_nonempty (M.gradeContract nu.cache) S.E S.hc
        (M.toHealing nu.st.core) (M.round_of S.hc (M.toHealing nu.st.core).s) A2u
      exact compatible_ancestor_left₆₄ (hLu nu hnu A2u hA2u Bu hBu)
        (hsg u huHon nu hnu Du hDu hemitU A2u hA2u Bu hBu)
  rcases Restated.Vocabulary.Proofs.HealingSurface.actionSGBlockAt_tiers facts S rho w (r + 1)
      n hnAt g hgRead A2 hA2 G hG with
    hwalk | ⟨Q, hQ, hout⟩ | ⟨_, _, hout⟩ | ⟨_, _, hout⟩
  · exact compatible_ancestor_left₆₄ hwalk.2.1 hliveT
  · rw [hout]
    have hq : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n (r + 1) ⇢ some Q :=
      returns_map_intro₆₄ (fun g : GradeRead V => g.Q2) _ g _ hgRead hQ
    have ha : Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M S n (r + 1) ⇢ g.anchor :=
      returns_map_intro₆₄ (fun g : GradeRead V => g.anchor) _ g _ hgRead rfl
    exact compatible_ancestor_left₆₄
      (Restated.actionQ2_preceq_actionAnchorOn facts S Hs Xb hf hHs hHsXb
        (Nat.succ_pos r) hhor hwG1 hloOpen n hn' hq g.anchor ha) hanchorT
  · rw [hout]
    exact hrootT
  · rw [hout]
    exact hanchorT

end

/-! ## The joint induction and the confirmation witness -/

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open scoped DC

local macro "p63% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_63)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

set_option linter.unusedVariables false

/-- At slot `d`: every outcome of the head at the vote-duty read of every member of the set for
    `vote_time d`, built with any outcome of the phase tick, is a descendant of `T`, and the
    slot-`d` votes of the set along `W` form a cone over `T`. -/
private abbrev HeadsCone₆₄c (M : Record.Model V) (S : Setup V) (rho : Record.Run V)
    (W : Nat → V → M.N) (Hs : Int → Finset V) (Xb : Finset V) (T : Block V) (d : Slot) : Prop :=
  (∀ w ∈ Hs (M.vote_time S.E d), ∀ c : M.Cache,
      M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core.toHealing
        (M.vote_time S.E d)
        (W (strictEventIndex rho (M.vote_time S.E d)) w).cache ⇢ c →
      let n := M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) w).st
          (M.vote_time S.E d))
        (W (strictEventIndex rho (M.vote_time S.E d)) w).record c
      ∀ Tr : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ Tr →
      ∀ L : Finset (GoldfishVote V),
        M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
      ∀ L' : Finset (GoldfishVote V),
        M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
      ∀ H : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
          (M.toHealing n.st.core) Tr L L' (n.st.core.s - 1) ⇢ H →
        Block.Preceq T H) ∧
      Restated.NamedHonestVotesConeOn M S rho W Hs Xb d
        (fun Y => Block.Preceq T Y)

/-- Under the bundle with path `W`, the committee majorities and the weight bound, if the selector
    cone holds for `a` with checkpoint `T`, the frame and window over `X` hold up to `first` from
    `c0 ≤ a.round`, round `a.round` is ready, `t_GST ≤ S.a (a.round − 1)`, `a.round ≤ c`,
    `lo ≤ opening (a.round − η_SG)`, and every member of the set for `S.a k + Δ` is awake at `k`,
    then (1) for every slot `d` of round `c` (after the opening slot when `c = a.round`) whose vote
    instant plus `Δ` is in the horizon and whose vote instant is before `first`, every head of every
    vote-duty read at `d` of a member of the set for `vote_time d` is a descendant of `T` and the
    slot-`d` votes of the set form a cone over `T`, and (2) if `S.a c` is in the horizon and before
    `first`, every round-`c` action emission of a member of the set for `S.a c` selects only blocks
    compatible with `T`. -/
theorem PrefixFGSelectorConeAtOn.checkpointProtection_and_SGHistory_of_source_of_frame_named
    (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} {Hs : Int → Finset V} {Xb X : Finset V} {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hX : ∀ t : Int, 0 ≤ t → Hs t ⊆ X) (hXXb : X ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hfb : BelowOneThirdOn S rho Hs)
    {start first : Nat} {blocked : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg Tprev : NamedBlock V} {T : Block V} {c0 : Round}
    (hseed : Restated.PrefixFGSelectorConeAtOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs Xb start first blocked i a ta Cfg T)
    (hfirst : Restated.HeightWindowAtOn M S rho W X (blocked + 1) first)
    (hframe : Restated.NamedHeightRegimeFrameOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs X Xb blocked (first - 1) Tprev c0)
    (hc0 : c0 ≤ a.round)
    (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho a.round)
    (hpostPrev : S.E.t_GST ≤ Restated.Vocabulary.Execution.Setup.a M S (a.round - 1))
    {c : Round} (hc : a.round ≤ c)
    (hlo : lo ≤ M.opening S.E S.hc (a.round - S.hc.η_SG))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S k + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    (∀ d, M.opening_slot S.hc c ≤ d → d < M.opening_slot S.hc (c + 1) →
      (c = a.round → M.opening_slot S.hc a.round + 1 ≤ d) →
      M.vote_time S.E d + S.E.Δ ≤ rho.horizon →
      strictEventIndex rho (M.vote_time S.E d) < first →
      (∀ w ∈ Hs (M.vote_time S.E d), ∀ c : M.Cache,
      M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core.toHealing
        (M.vote_time S.E d)
        (W (strictEventIndex rho (M.vote_time S.E d)) w).cache ⇢ c →
      let n := M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) w).st
          (M.vote_time S.E d))
        (W (strictEventIndex rho (M.vote_time S.E d)) w).record c
      ∀ Tr : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ Tr →
      ∀ L : Finset (GoldfishVote V),
        M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
      ∀ L' : Finset (GoldfishVote V),
        M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
      ∀ H : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
          (M.toHealing n.st.core) Tr L L' (n.st.core.s - 1) ⇢ H →
        Block.Preceq T H) ∧
      Restated.NamedHonestVotesConeOn M S rho W Hs Xb d
        (fun Y => Block.Preceq T Y)) ∧
    (Restated.Vocabulary.Execution.Setup.a M S c ≤ rho.horizon → strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c) < first →
      Restated.HonestSGEmissionsCompatibleAtRoundOn M S rho W
        (fun t => W (strictEventIndex rho t)) Hs c T) := by
  have hΔ := S.E.Δ_pos
  have hR := S.hc.R_ge_two
  have hopenPost : lo ≤ M.vote_time S.E (M.opening_slot S.hc a.round) := by
    obtain ⟨-, hvote, -⟩ := Restated.openingInstants_l63 facts S a.round
    have h1 := hlo.trans (facts.gr.NamedOutageClosure_opening_mono S
      (Nat.sub_le a.round S.hc.η_SG))
    have h2 : M.opening S.E S.hc a.round = M.proposal_time S.E (M.opening_slot S.hc a.round) :=
      facts.gr.opening_eq_proposal_time S.E S.hc a.round
    linarith
  have hconfHor : ∀ n d : Slot, n + 1 ≤ d → M.vote_time S.E d + S.E.Δ ≤ rho.horizon →
      M.confirmation_time S.E n ≤ rho.horizon := by
    intro n d hntop hhor
    have htime := facts.sch.vote_time_mono_slots S.E hntop
    obtain ⟨-, -, -, -, h5, h6⟩ := facts.sch.slot_instants_l55 S.E n
    linarith
  have hnextOpening : ∀ k : Round,
      Restated.Vocabulary.Execution.Setup.a M S k ≤ M.vote_time S.E (M.opening_slot S.hc (k + 1)) := by
    intro k
    have hdeltaEarly := facts.gr.action_delta_le_early S S.hc.R_ge_three (Nat.lt_succ_self k)
    have hearlyG1 := (facts.gr.early_g2_le_early_g1 S.E S.hc (k + 1)).trans
      (facts.gr.early_g1_le_domain_g1 S (k + 1))
    have hopenProp : M.domain S.E S.hc (k + 1) .g1 =
        M.proposal_time S.E (M.opening_slot S.hc (k + 1)) := by
      rw [facts.gr.Sts_domain_g1_eq_opening S (k + 1), facts.gr.opening_eq_proposal_time]
    obtain ⟨-, hvt1, -⟩ := Restated.openingInstants_l63 facts S (k + 1)
    linarith
  have hopenAction : ∀ k : Round,
      M.vote_time S.E (M.opening_slot S.hc k) + S.E.Δ ≤ Restated.Vocabulary.Execution.Setup.a M S k := by
    intro k
    obtain ⟨-, hvt, -, -, -, hact⟩ := Restated.openingInstants_l63 facts S k
    linarith
  have hsourceInterior : ∀ d,
      M.opening_slot S.hc a.round + 1 ≤ d →
      d < M.opening_slot S.hc (a.round + 1) →
      M.vote_time S.E d + S.E.Δ ≤ rho.horizon →
      strictEventIndex rho (M.vote_time S.E d) < first →
      HeadsCone₆₄c M S rho W Hs Xb T d := by
    intro d hdlo hdhi hhor hbefore
    have hbase : HeadsCone₆₄c M S rho W Hs Xb T (M.opening_slot S.hc a.round + 1) :=
      PrefixFGSelectorConeAtOn.checkpointProtection_firstInterior_of_frame_named facts hf hHs hHsXb hX hXXb hseed hfirst hframe hc0 ready hpostPrev hlo
    have hfold : ∀ n, M.opening_slot S.hc a.round + 1 ≤ n → n ≤ d →
        HeadsCone₆₄c M S rho W Hs Xb T n := by
      intro n hn
      induction n, hn using Nat.le_induction with
      | base => intro _; exact hbase
      | succ n hn ih =>
          intro hntop
          have hprev := ih (Nat.le_of_succ_le hntop)
          have htime := facts.sch.vote_time_mono_slots S.E hntop
          have hnRound : M.round_of S.hc (n + 1) = a.round :=
            facts.gr.round_of_eq_of_opening_succ_le_of_lt_next_opening S.hc
              (hn.trans (Nat.le_succ n)) (hntop.trans_lt hdhi)
          have hsettled : Restated.Vocabulary.Execution.Setup.a M S a.round + S.E.Δ ≤ M.vote_time S.E (n + 1) := by
            apply Restated.Vocabulary.Proofs.HealingSurface.action_add_delta_le_vote_of_lt facts S
            exact (Restated.Vocabulary.Protocol.action_lt_vote_time_two_after facts S
              a.round).trans_le (facts.sch.vote_time_mono_slots S.E (Nat.succ_le_succ hn))
          exact hseed.checkpointVoteStep_of_source_of_frame_named facts
            hf hHs hHsXb hX hXXb hcom hfirst hframe hc0 ready hpostPrev
              ((Nat.succ_pos _).trans_le hn)
              (hopenPost.trans (facts.sch.vote_time_mono_slots S.E ((Nat.le_succ _).trans hn)))
              (hconfHor n d hntop hhor)
              ((strictEventIndex_mono rho htime).trans_lt hbefore)
              hnRound hsettled hprev.2 hlo
    exact hfold d hdlo (le_refl _)
  have hbaseSG := hseed.sgEmissionsCompatible_of_source_of_frame_named facts
    hf hHs hHsXb hX hXXb hcom hfirst hframe hc0 ready hpostPrev hlo
  have hr0 : 0 < a.round := round_pos₆₄ facts hf hseed
  induction c, hc using Nat.le_induction with
  | base =>
      exact ⟨fun d _ hdhi hstart hhor hbefore => hsourceInterior d (hstart rfl) hdhi hhor hbefore,
        fun _ _ => hbaseSG⟩
  | succ c hc ih =>
      have hosSucc := facts.gr.opening_slot_succ_eq S.hc c
      have hnat : ∀ x y k : Nat, 2 ≤ k → y = x + k →
          x ≤ y - 1 ∧ y - 1 < y ∧ 0 < y - 1 ∧ x + 1 ≤ y - 1 ∧ x < y ∧
            ∀ n : Nat, y - 1 ≤ n → y ≤ n + 1 := by
        intro x y k h2 hy
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
      obtain ⟨hlastLo, hlastHi, hlastPos, -, -, hsuccLe⟩ := hnat _ _ _ hR hosSucc
      have hsourceOpen : M.opening_slot S.hc a.round ≤ M.opening_slot S.hc c :=
        facts.gr.opening_slot_le_of_le S.hc hc
      have hnextVotes : ∀ d, M.opening_slot S.hc (c + 1) ≤ d →
          d < M.opening_slot S.hc (c + 1 + 1) →
          M.vote_time S.E d + S.E.Δ ≤ rho.horizon →
          strictEventIndex rho (M.vote_time S.E d) < first →
          HeadsCone₆₄c M S rho W Hs Xb T d := by
        intro d hdlo hdhi hdhor hdbefore
        have hprevRead : Restated.Vocabulary.Execution.Setup.a M S c ≤ M.vote_time S.E d :=
          (hnextOpening c).trans (facts.sch.vote_time_mono_slots S.E hdlo)
        have hvoteHor : M.vote_time S.E d ≤ rho.horizon := by linarith
        have hprevSG := ih.2 (hprevRead.trans hvoteHor)
          ((strictEventIndex_mono rho hprevRead).trans_lt hdbefore)
        have hlastLe : M.opening_slot S.hc (c + 1) - 1 ≤ d := hlastHi.le.trans hdlo
        have hlastRead := facts.sch.vote_time_mono_slots S.E hlastLe
        have hlastCone : HeadsCone₆₄c M S rho W Hs Xb T (M.opening_slot S.hc (c + 1) - 1) :=
          ih.1 _ hlastLo hlastHi
            (by
              intro heq
              rw [heq] at hosSucc ⊢
              exact (hnat _ _ _ hR hosSucc).2.2.2.1)
            ((add_le_add hlastRead (le_refl S.E.Δ)).trans hdhor)
            ((strictEventIndex_mono rho hlastRead).trans_lt hdbefore)
        have hfold : ∀ n, M.opening_slot S.hc (c + 1) - 1 ≤ n → n ≤ d →
            HeadsCone₆₄c M S rho W Hs Xb T n := by
          intro n hn
          induction n, hn using Nat.le_induction with
          | base => intro _; exact hlastCone
          | succ n hn ihSlot =>
              intro hntop
              have hprev := ihSlot (Nat.le_of_succ_le hntop)
              have hnlo : M.opening_slot S.hc (c + 1) ≤ n + 1 := hsuccLe n hn
              have hnhi : n + 1 < M.opening_slot S.hc (c + 1 + 1) := hntop.trans_lt hdhi
              have hround : M.round_of S.hc (n + 1) = c + 1 := by
                rcases eq_or_lt_of_le hnlo with heq | hlt
                · rw [← heq]
                  exact facts.gr.round_of_opening_slot_eq_schedule S.hc (c + 1)
                · exact facts.gr.round_of_eq_of_opening_succ_le_of_lt_next_opening S.hc hlt hnhi
              have hnRead := facts.sch.vote_time_mono_slots S.E hntop
              have hnPost : lo ≤ M.vote_time S.E n :=
                hopenPost.trans (facts.sch.vote_time_mono_slots S.E
                  (hsourceOpen.trans (hlastLo.trans hn)))
              have hnSourceRead : Restated.Vocabulary.Execution.Setup.a M S a.round ≤ M.vote_time S.E (n + 1) :=
                (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hc).trans
                  ((hnextOpening c).trans (facts.sch.vote_time_mono_slots S.E hnlo))
              exact hseed.checkpointVoteStep_of_previousSGHistory_of_frame_named facts
                hf hHs hHsXb hX hXXb hcom hfb hfirst hframe ready (hlastPos.trans_le hn)
                  hnPost (hconfHor n d hntop hdhor) hnSourceRead
                    ((strictEventIndex_mono rho hnRead).trans_lt hdbefore)
                      (by rw [hround]; exact Nat.add_le_add_right hc 1)
                        hprev.2
                          (by rw [hround, Nat.add_sub_cancel]; exact hprevSG) hlo
                            (by
                              rw [hround, Nat.add_sub_cancel]
                              exact hA c
                                (Restated.lo_le_early_g2_sub_delta_of_opening facts S hr0 hlo hc))
        exact hfold d hlastLe (Nat.le_refl d)
      refine ⟨fun d hdlo hdhi _ hhor hbefore => hnextVotes d hdlo hdhi hhor hbefore, ?_⟩
      intro hhor hbefore
      have hprevAction := Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.le_succ c)
      have hprevSG := ih.2 (hprevAction.trans hhor)
        ((strictEventIndex_mono rho hprevAction).trans_lt hbefore)
      have hopenHi : M.opening_slot S.hc (c + 1) < M.opening_slot S.hc (c + 1 + 1) := by
        exact (hnat _ _ _ hR (facts.gr.opening_slot_succ_eq S.hc (c + 1))).2.2.2.2.1
      have hopenRead : M.vote_time S.E (M.opening_slot S.hc (c + 1)) ≤ Restated.Vocabulary.Execution.Setup.a M S (c + 1) := by
        linarith [hopenAction (c + 1)]
      have hopenCone := hnextVotes _ (Nat.le_refl _) hopenHi
        ((hopenAction (c + 1)).trans hhor)
        ((strictEventIndex_mono rho hopenRead).trans_lt hbefore)
      exact hseed.sgEmissionsCompatible_laterRound_of_frame_named facts
        hf hHs hHsXb hX hcom hfb hfirst hframe ready hc hprevSG hopenCone.2 hhor hbefore
          hlo (hA c (Restated.lo_le_early_g2_sub_delta_of_opening facts S hr0 hlo hc))

/-- Under the bundle with path `W`, the committee majorities and the weight bound, if the selector
    cone holds for `a` with checkpoint `T`, the frame and window over `X` hold up to `first` from
    `c0 ≤ a.round`, round `a.round` is ready, `t_GST ≤ S.a (a.round − 1)`, the signer of `c` is in
    the set for `S.a c.round` and emitted `c` along `W` at `tc` at height `blocked + 1`,
    `a.round ≤ c.round`, the events before `S.a c.round` are fewer than `first`,
    `lo ≤ opening (a.round − η_SG)`, and every member of the set for `S.a k + Δ` is awake at `k`,
    then every outcome of the FG confirmation witness of every node state of the signer's
    round-`c.round` action read along `W` is `some T`. -/
theorem PrefixFGSelectorConeAtOn.confirmationWitness_of_source_of_frame_named
    (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} {Hs : Int → Finset V} {Xb X : Finset V} {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hX : ∀ t : Int, 0 ≤ t → Hs t ⊆ X) (hXXb : X ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hfb : BelowOneThirdOn S rho Hs)
    {start first : Nat} {blocked : Height}
    {i : Nat} {a c : NamedAttestation V} {ta tc : Time}
    {Cfg Tprev : NamedBlock V} {T : Block V} {c0 : Round}
    (hseed : Restated.PrefixFGSelectorConeAtOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs Xb start first blocked i a ta Cfg T)
    (hfirst : Restated.HeightWindowAtOn M S rho W X (blocked + 1) first)
    (hframe : Restated.NamedHeightRegimeFrameOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs X Xb blocked (first - 1) Tprev c0)
    (hc0 : c0 ≤ a.round)
    (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho a.round)
    (hpostPrev : S.E.t_GST ≤ Restated.Vocabulary.Execution.Setup.a M S (a.round - 1))
    (hc : c.val_index ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S c.round))
    (hemit : Restated.Vocabulary.Execution.NamedRun.emits M S rho W c.val_index (Object.attest c) tc)
    (hrow : c.height_pair.erase.height? = some (blocked + 1))
    (hcr : a.round ≤ c.round)
    (hbefore : strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c.round) < first)
    (hlo : lo ≤ M.opening S.E S.hc (a.round - S.hc.η_SG))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S k + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c.round)) c.val_index) c.round,
    ∀ o : Option (Block V),
      Restated.Vocabulary.Proofs.HealingSurface.fgConfirmationWitness M S n ⇢ o → o = some T := by
  rcases eq_or_lt_of_le hcr with heq | hlt
  · exact hseed.confirmationWitness_of_sameRound_honestHeightRow_of_frame_named facts
      hf hHs hHsXb hX hXXb hfirst hframe ready hc hemit hrow heq hlo
  intro n hn o ho
  have hΔ := S.E.Δ_pos
  have hcX : c.val_index ∈ X := hX _ (a_nonneg₆₄ facts S c.round) hc
  obtain ⟨os, hos, hmap⟩ := (p63% returns_map_elim₆₃) _ _ _ ho
  obtain ⟨htime, -, hwit⟩ := Restated.honestEmittedHeightRow_exactFGSelectorWitnessOn facts
    S Hs Xb X hf hcX hemit hrow n hn
  obtain ⟨D, T', hsource', hDmem, -, hDheight, hT', -⟩ := hwit os hos
  subst hsource'
  have hoT' : o = some T' := by
    rw [← hmap]
    simp only [Option.map_some]
    rw [(p63% actionRead_σ_named₆₃w) facts S hf hn hDmem, hT']
  obtain ⟨r, hsucc⟩ : ∃ r : Round, r + 1 = c.round :=
    ⟨c.round - 1, Nat.sub_add_cancel ((Nat.succ_le_succ (Nat.zero_le a.round)).trans hlt)⟩
  have hr : a.round ≤ r := by
    have : a.round < r + 1 := hsucc ▸ hlt
    exact Nat.lt_succ_iff.mp this
  have hhorC : Restated.Vocabulary.Execution.Setup.a M S c.round ≤ rho.horizon := by
    obtain ⟨k, hk, _⟩ := hemit
    have hin := (hf.in_horizon (Record.Event.tick c.val_index tc) (List.mem_of_getElem? hk)).2
    simpa only [Record.Event.time, htime, Record.Event.time] using hin
  rw [← hsucc] at hc hbefore hn hhorC
  have hhor : Restated.Vocabulary.Execution.Setup.a M S (r + 1) ≤ rho.horizon := hhorC
  have hopenA : M.opening S.E S.hc a.round ≤ Restated.Vocabulary.Execution.Setup.a M S a.round := by
    rw [← facts.gr.Sts_domain_g1_eq_opening S a.round]
    exact facts.gr.domain_le_a S a.round .g1
  have hloSource : lo ≤ Restated.Vocabulary.Execution.Setup.a M S a.round :=
    hlo.trans ((facts.gr.NamedOutageClosure_opening_mono S (Nat.sub_le _ _)).trans hopenA)
  have hloR : lo ≤ Restated.Vocabulary.Execution.Setup.a M S r :=
    hloSource.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hr)
  have hprev := PrefixFGSelectorConeAtOn.checkpointProtection_and_SGHistory_of_source_of_frame_named
    facts hf hHs hHsXb hX hXXb hcom hfb hseed hfirst hframe hc0 ready hpostPrev
      hr hlo hA
  have hcurrent :=
    PrefixFGSelectorConeAtOn.checkpointProtection_and_SGHistory_of_source_of_frame_named
      facts hf hHs hHsXb hX hXXb hcom hfb hseed hfirst hframe hc0 ready hpostPrev
        (hr.trans (Nat.le_succ r)) hlo hA
  have hprevAction := Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.le_succ r)
  have hhorR : Restated.Vocabulary.Execution.Setup.a M S r ≤ rho.horizon := hprevAction.trans hhor
  have hsg := hprev.2 hhorR ((strictEventIndex_mono rho hprevAction).trans_lt hbefore)
  obtain ⟨_, hvt1, hsc1, _, _, hact1⟩ := Restated.openingInstants_l63 facts S (r + 1)
  have hopenHi : M.opening_slot S.hc (r + 1) < M.opening_slot S.hc (r + 1 + 1) := by
    rw [facts.gr.opening_slot_succ_eq S.hc (r + 1)]
    exact Nat.lt_add_of_pos_right (Nat.zero_lt_of_lt S.hc.R_ge_two)
  have hopenAction : M.vote_time S.E (M.opening_slot S.hc (r + 1)) + S.E.Δ ≤ Restated.Vocabulary.Execution.Setup.a M S (r + 1) := by
    linarith
  have hopenRead : M.vote_time S.E (M.opening_slot S.hc (r + 1)) ≤ Restated.Vocabulary.Execution.Setup.a M S (r + 1) := by
    linarith
  have hgf := (hcurrent.1 _ (Nat.le_refl _) hopenHi
    (fun heq' => False.elim ((Nat.not_succ_le_self r) (heq'.symm ▸ hr)))
    (hopenAction.trans hhor)
    ((strictEventIndex_mono rho hopenRead).trans_lt hbefore)).2
  have hdeltaEarly : Restated.Vocabulary.Execution.Setup.a M S r + S.E.Δ ≤ M.early S.E S.hc (r + 1) .g2 :=
    facts.gr.action_delta_le_early S S.hc.R_ge_three (Nat.lt_succ_self r)
  have hearlyG1 : M.early S.E S.hc (r + 1) .g2 ≤ M.domain S.E S.hc (r + 1) .g1 :=
    (facts.gr.early_g2_le_early_g1 S.E S.hc (r + 1)).trans
      (facts.gr.early_g1_le_domain_g1 S (r + 1))
  have hopenProp : M.domain S.E S.hc (r + 1) .g1 =
      M.proposal_time S.E (M.opening_slot S.hc (r + 1)) := by
    rw [facts.gr.Sts_domain_g1_eq_opening S (r + 1), facts.gr.opening_eq_proposal_time]
  have hpost : lo ≤ M.vote_time S.E (M.opening_slot S.hc (r + 1)) := by linarith
  have hwinNext : lo ≤ M.early S.E S.hc (M.round_of S.hc (M.opening_slot S.hc (r + 1))) .g1 -
      S.E.Δ := by
    rw [facts.gr.round_of_opening_slot_eq S.hc (r + 1)]
    have h1 := facts.gr.early_g2_add_delta_le_early_g1 S (r + 1)
    linarith
  have hr0 : 0 < a.round := round_pos₆₄ facts hf hseed
  have hca := Restated.Vocabulary.Proofs.HealingSurface.opening_confirmation_time_eq_action facts S
    (r + 1)
  have hconfHor : M.confirmation_time S.E (M.opening_slot S.hc (r + 1)) ≤ rho.horizon := by
    rw [hca]
    exact hhor
  have hopen : 0 < M.opening_slot S.hc (r + 1) := facts.gr.opening_slot_pos S (Nat.succ_pos r)
  have hvoteConf : M.vote_time S.E (M.opening_slot S.hc (r + 1)) ≤
      M.confirmation_time S.E (M.opening_slot S.hc (r + 1)) :=
    facts.sch.Protocol_vote_time_le_confirmation_time S.E _
  have hmemA := (p63% mem_stateBeforeTime_along₆₃) hf.sorted hf.onePath (Restated.Vocabulary.Execution.Setup.a M S (r + 1))
  obtain ⟨Q, hQ⟩ := nodeQ2_some_of_actionFGSource₆₄ facts S hf n hn hos
  have hsourceCompat : Block.compatible D.erase T = true := by
    rcases Restated.Vocabulary.Proofs.HealingSurface.actionFGSource_genuineClear_or_selectedG2_named
        facts S rho c.val_index (r + 1) _ hmemA n hn hQ hos with
      ⟨C, hgenuine, -, -, -, hDC⟩ | hselected
    · have hheads : ∀ x ∈ Hs (M.confirmation_time S.E (M.opening_slot S.hc (r + 1))),
          x ∈ S.E.committee (M.opening_slot S.hc (r + 1)) →
          ∃ c : M.Cache, M.onPhaseTick S.E S.hc
              (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc (r + 1)))) x).st.core.toHealing
              (M.vote_time S.E (M.opening_slot S.hc (r + 1)))
              (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc (r + 1)))) x).cache ⇢ c ∧
          let n := M.mkNode
            (M.ns_setClock S.E
              (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc (r + 1)))) x).st
              (M.vote_time S.E (M.opening_slot S.hc (r + 1))))
            (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc (r + 1)))) x).record c
          ∃ Tr : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ Tr ∧
          ∃ L : Finset (GoldfishVote V),
            M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L ∧
          ∃ L' : Finset (GoldfishVote V),
            M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' ∧
          ∃ H : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
              (M.toHealing n.st.core) Tr L L' (n.st.core.s - 1) ⇢ H ∧
            Block.Preceq T H := by
        intro x hx hxc
        have hxVote : x ∈ Hs (M.vote_time S.E (M.opening_slot S.hc (r + 1))) :=
          hHs _ _ hvoteConf hx
        obtain ⟨Y, hTY, hYrun, hYemit⟩ := hgf x hxVote hxc
        obtain ⟨cx, hcx⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc
          (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc (r + 1)))) x).st.core.toHealing
          (M.vote_time S.E (M.opening_slot S.hc (r + 1)))
          (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc (r + 1)))) x).cache
        refine ⟨cx, hcx, ?_⟩
        intro nx
        obtain ⟨Tr, hTr⟩ := facts.fc.voter_filtered_block_tree_nonempty S.E nx.st.core nx.st.core.s
        obtain ⟨L, hL⟩ := facts.fc.voter_view_nonempty S.E
          (M.toHealing nx.st.core).toFG.toSG.toGoldfishStore nx.st.core.s
        obtain ⟨L', hL'⟩ := facts.fc.voter_support_view_nonempty S.E
          (M.toHealing nx.st.core).toFG.toSG.toGoldfishStore nx.st.core.s
        obtain ⟨Hd, hHd⟩ := facts.fc.get_head_in_tree_with_layer_nonempty
          (M.gradeContract nx.cache) S.E S.hc (M.toHealing nx.st.core) Tr L L' (nx.st.core.s - 1)
        obtain ⟨H, hHerase, hHrun, hHemit⟩ :=
          Restated.voterHead_runBlock_and_emitsOn facts S Hs Xb hf hHsXb hxVote hopen hxc
            (hvoteConf.trans hconfHor) hpost cx hcx
            (fun j hj => hf.awake_g1 _ _ j _ (Or.inr rfl) hj hxVote hwinNext)
            Tr hTr L hL L' hL' Hd hHd
        have heqVote := Restated.emits_gfVote_uniqueOn facts S Hs Xb hf hYemit hHemit rfl
        have hroot : Y.root = H.root := by
          simpa only [Proofs.NamedWire.erase_root] using congrArg GoldfishVote.head heqVote
        have hYH : Y = H := hf.rootCollisionFree.root_injective
          Y H hYrun hHrun Y H (Or.inl (Proofs.NamedAncestry.named_self Y))
            (Or.inr (Proofs.NamedAncestry.named_self H)) hroot
        refine ⟨Tr, hTr, L, hL, L', hL', Hd, hHd, ?_⟩
        rw [← hHerase, ← hYH]
        exact hTY
      have hcSC : c.val_index ∈ Hs (M.support_cutoff S.E (M.opening_slot S.hc (r + 1))) :=
        hHs _ _ (by linarith) hc
      obtain ⟨c0', hc0', st0, hst0, hneq⟩ := hn
      have hcache : n.cache = c0' := by
        subst hneq
        exact facts.nd.mkNode_cache _ _ _
      rw [hcache] at hgenuine
      rw [← hca] at hc0' hgenuine
      have hTC := Restated.genuineConfirmation_compatible_of_priorProtectedHeadsOn facts
        S Hs Xb hf hHs hHsXb hcom hcSC hopen hpost hconfHor c0' hc0' hgenuine hheads
        (fun x _ hxH j hj => hf.awake_g1 _ _ j _ (Or.inr rfl) hj
          (hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E _) hxH) hwinNext)
      exact compatible_ancestor_left₆₄ hDC (Protocol.compatible_comm hTC)
    · rw [hselected]
      have hgrade := Restated.selectedQ2_storeGrade_at_g2DomainOn facts S Hs Xb hf n hn hQ
      have hwindow := hseed.relativeCarrierWindow_of_previousSG_of_frame_named facts
        hf hHs hHsXb hX hXXb hfirst hframe ready hr hsg hhor hbefore .g2 hlo
      have hdomA : M.domain S.E S.hc (r + 1) .g2 ≤ Restated.Vocabulary.Execution.Setup.a M S (r + 1) :=
        facts.gr.domain_le_a S (r + 1) .g2
      have hprevt : Restated.Vocabulary.Execution.Setup.a M S (r + 1 - 1) + S.E.Δ ≤ M.domain S.E S.hc (r + 1) .g2 := by
        rw [Nat.add_sub_cancel]
        exact hdeltaEarly.trans (facts.gr.early_le_domain S (r + 1))
      have hmajority : Restated.GradeFormingMajorityOn M S rho W Hs
          (Hs (M.domain S.E S.hc (r + 1) .g2)) (r + 1) :=
        Restated.gradeFormingMajority_of_admissible_belowOneThirdOn facts S Hs Xb hf hHs hfb
          (r := r + 1) (Nat.succ_pos r) hprevt (hdomA.trans hhor)
          (by rw [Nat.add_sub_cancel]; exact hloR)
          (by
            rw [Nat.add_sub_cancel]
            exact hA r (Restated.lo_le_early_g2_sub_delta_of_opening facts S hr0 hlo hr))
      have hcG2 : c.val_index ∈ Hs (M.domain S.E S.hc (r + 1) .g2) := hHs _ _ hdomA hc
      obtain ⟨bQ, hbQ⟩ := facts.gr.gradeBool_nonempty S.E
        (M.gradeView (M.toHealing
          (W (strictEventIndex rho (M.domain S.E S.hc (r + 1) .g2)) c.val_index).st.core))
        (W (strictEventIndex rho (M.domain S.E S.hc (r + 1) .g2)) c.val_index).st.core.F
        S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) .g2) (M.late S.E S.hc (r + 1) .g2) Q
      have hbQt : bQ = true := hgrade bQ hbQ
      subst hbQt
      obtain ⟨u, hu, hQu⟩ := Restated.relativeGrade_has_roundCarrierOn facts
        S Hs Xb (Hs (M.domain S.E S.hc (r + 1) .g2)) hf hHs hwindow hmajority
          (subset_refl _) hcG2 hbQ
      obtain ⟨huHon, b, _, hbround, hbemit⟩ :=
        (Restated.honestRoundVoters_iffOn facts S rho W hf.onePath Hs u r).mp hu
      have hawake : ∀ j : Nat, rho.events[j]? =
          some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S r)) →
          M.awake_for_grade2 S u (W j u) r := by
        have h := awake_g2_of_emits₆₄ facts hf hbemit
        rwa [hbround] at h
      obtain ⟨nu, hnu⟩ := actionReadFrom_nonempty₆₄ facts S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) u) r
      obtain ⟨Du, hDu⟩ := facts.dt.attest_with_nonempty (M.gradeContract nu.cache) S.E S.hc
        (S.node u) nu.st nu.record
      have hemitU : Restated.Vocabulary.Execution.NamedRun.emits M S rho W u
          (Object.attest Du.2.2) (Restated.Vocabulary.Execution.Setup.a M S r) :=
        Restated.honest_emits_exact_actionAttestationAt_of_awakeOn facts S Hs Xb hf r huHon
          hawake hhorR hloR (fun j hj => hf.tick_outcome j _ _ hj) nu hnu Du hDu
      obtain ⟨A2u, hA2u⟩ := facts.dt.grade2_block_with_nonempty (M.gradeContract nu.cache) S.E
        S.hc (M.toHealing nu.st.core) (M.round_of S.hc (M.toHealing nu.st.core).s)
      obtain ⟨Bu, hBu⟩ := facts.dt.get_sg_vote_with_nonempty (M.gradeContract nu.cache) S.E S.hc
        (M.toHealing nu.st.core) (M.round_of S.hc (M.toHealing nu.st.core).s) A2u
      exact compatible_ancestor_left₆₄ (hQu nu hnu A2u hA2u Bu hBu)
        (hsg u huHon nu hnu Du hDu hemitU A2u hA2u Bu hBu)
  have hsigner : a.val_index ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S a.round) := by
    have h := hseed.signerHonest
    rw [hseed.actionTime_eq] at h
    exact h
  obtain ⟨n₀, hn₀⟩ := actionReadFrom_nonempty₆₄ facts S
    (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round)) a.val_index) a.round
  obtain ⟨K, -, hKT, hKheight, hKrun, -⟩ :=
    hseed.namedCheckpoint_l64 facts hf hHsXb hX hframe n₀ hn₀
  have hCfgRun := Restated.actionBody_runBlock_named_historyOn facts
    S Hs Xb hf (hHsXb _ hsigner) hn₀ (hseed.sourceMem n₀ hn₀)
  have hDRun := Restated.actionBody_runBlock_named_historyOn facts
    S Hs Xb hf (hHsXb _ hc) hn hDmem
  have hKCfg : NamedBlock.Preceq K Cfg :=
    Restated.namedPreceq_of_runBlock_erase_preceqOn facts Hs Xb hf hKrun hCfgRun
      (by rw [hKT, hseed.checkpointDerived]
          exact facts.csAdded.derive_named_T_h_preceq S.E S.cfg Cfg)
  have h1 : (M.derive_named S.E S.cfg K).T_h = (M.derive_named S.E S.cfg Cfg).T_h :=
    facts.cs.entry_eq_on_plateau S.E S.cfg hKCfg (hKheight.trans hseed.sourceDerivedHeight.symm)
  have h2 : (M.derive_named S.E S.cfg K).T_h = (M.derive_named S.E S.cfg D).T_h := by
    rw [← hKT] at hsourceCompat
    rcases compatible_cases hsourceCompat with hpre | hpre
    · exact (facts.cs.entry_eq_on_plateau S.E S.cfg
        (Restated.namedPreceq_of_runBlock_erase_preceqOn facts Hs Xb hf hDRun hKrun hpre)
        (hDheight.trans hKheight.symm)).symm
    · exact facts.cs.entry_eq_on_plateau S.E S.cfg
        (Restated.namedPreceq_of_runBlock_erase_preceqOn facts Hs Xb hf hKrun hDRun hpre)
        (hKheight.trans hDheight.symm)
  have heq : T = T' := by
    rw [hT', ← h2, h1]
    exact hseed.checkpointDerived
  rw [hoT', heq]

end

end DecoupledConsensusModel.Sts.Restated
