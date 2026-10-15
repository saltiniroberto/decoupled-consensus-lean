import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13beRoute3_45
import Proofs.Claims.Restated.Claim13beRoute3_49
import Proofs.Claims.Restated.Claim13beRoute3_50
import Proofs.Claims.Restated.Claim13beRoute3_63
import Proofs.Claims.Restated.Vocabulary_Execution_EmissionShape
import Proofs.Claims.Restated.Vocabulary_Execution_HealthyLocalFacts
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_Action
import Model.Conditions.RunVocabulary
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring
import Proofs.Claims.Restated.Claim13beRoute3_64
import Proofs.Claims.Restated.Claim13beRoute3_47b
import Proofs.Claims.Restated.Claim13beRoute3_57
import Proofs.Claims.Restated.Claim13beRoute3_62
import Proofs.Claims.Restated.Claim13beRoute3_65
import Proofs.Claims.Restated.Claim13beRoute3_69b
import Proofs.Claims.Restated.Vocabulary_Execution_RecoveryFilterSchedule
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_PostHealingReuse
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_SafetyCompatibilityJoin

/-!
# Selector cones and run-scoped regimes: checkpoint protection

Theorems named under `PrefixFGSelectorConeAtOn` and `NamedHeightRegimeRunOn`, stated over a model
`M : Record.Model V` along the path `W` of the bundle `AdmissibleFieldsOn`: FG roots, voter heads
and votes after the source round descend from the checkpoint `T`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.Optimistic
local macro "rnh% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.Duties.Inputs.RecoveryInitialSourceNamedRunHistory)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- A round opens at or before its action instant. -/
private theorem incl_opening_le_a_l70 (facts : Record.Facts M) (S : Setup V) (r : Round) :
    M.opening S.E S.hc r ≤ Restated.Vocabulary.Execution.Setup.a M S r := by
  have h1 : Restated.Vocabulary.Execution.Setup.a M S r
      = M.confirmation_time S.E (M.opening_slot S.hc r) :=
    facts.sch.a_eq_confirmation_time S.hc S.E r
  have h2 := facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E (M.opening_slot S.hc r)
  have h3 : M.opening S.E S.hc r = slotStart S.E.Δ (M.opening_slot S.hc r) :=
    (facts.gr.opening_eq_proposal_time S.E S.hc r).trans
      (facts.sch.Γ_0_eq_proposal_time S.hc S.E r).symm
  have hd := S.E.Δ_pos
  rw [h1, h3]
  linarith

/-- If `0 < r` and `lo ≤ opening (r − η_SG)`, then `lo ≤ early r g2`,
    `lo ≤ vote_time (opening_slot r)`, `lo ≤ S.a (r − 1)` and `lo ≤ S.a r`. -/
theorem loBounds_l70 (facts : Record.Facts M) (S : Setup V) {r : Round} (hr : 0 < r) {lo : Int}
    (hlo : lo ≤ M.opening S.E S.hc (r - S.hc.η_SG)) :
    lo ≤ M.early S.E S.hc r .g2 ∧
      lo ≤ M.vote_time S.E ((M.opening_slot S.hc r)) ∧
      lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (r - 1)) ∧ lo ≤ (Restated.Vocabulary.Execution.Setup.a M S r) := by
  have hΔ := S.E.Δ_pos
  have hearly := facts.gr.lo_le_early_g2_of_window_start S hr hlo
  have hprev : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S (r - 1)) :=
    hlo.trans ((facts.gr.NamedOutageClosure_opening_mono S
      (Nat.sub_le_sub_left S.hc.η_SG_ge_one r)).trans
      (incl_opening_le_a_l70 facts S (r - 1)))
  have hcur : lo ≤ (Restated.Vocabulary.Execution.Setup.a M S r) :=
    hprev.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.sub_le r 1))
  obtain ⟨-, hvote, -, -, -, -⟩ := Restated.openingInstants_l63 facts S r
  have hopen : lo ≤ M.opening S.E S.hc r :=
    hlo.trans (facts.gr.NamedOutageClosure_opening_mono S (Nat.sub_le _ _))
  refine ⟨hearly, ?_, hprev, hcur⟩
  rw [hvote]
  have : M.opening S.E S.hc r = M.proposal_time S.E ((M.opening_slot S.hc r)) :=
    facts.gr.opening_eq_proposal_time S.E S.hc r
  linarith

end

/-! ## Theorems named under `PrefixFGSelectorConeAtOn` -/

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.Optimistic

open scoped DC in
/-- If `f <$> m` can return `b`, then `m` can return some `a` with `f a = b`. -/
private theorem returns_map_elim₇₀ {α β : Type} (f : α → β) (m : DC.NDRE α) (b : β)
    (h : (f <$> m) ⇢ b) : ∃ a, m ⇢ a ∧ f a = b := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image] at h
  obtain ⟨e, he, hb⟩ := h
  cases e with
  | ok a => exact ⟨a, he, by simpa [Except.map] using hb⟩
  | error err => simp [Except.map] at hb

open scoped DC in
/-- If `m` can return `a` and `k a` can return `b`, then `m >>= k` can return `b`. -/
private theorem returns_bind_intro₇₀ {α β : Type} (m : DC.NDRE α) (k : α → DC.NDRE β) (a : α)
    (b : β) (ha : m ⇢ a) (hb : k a ⇢ b) : (m >>= k) ⇢ b := by
  unfold Record.Returns at ha hb ⊢
  simp only [ExceptT.run_bind, Set.bind_def]
  exact Set.mem_iUnion₂.mpr ⟨.ok a, ha, hb⟩

/-- The round-`r` action read computed from `M.wake n` gives exactly the node states it gives
    computed from `n`. -/
private theorem actionReadFrom_wake₇₀ (facts : Record.Facts M) (S : Setup V) (n : M.N) (r : Round) :
    Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (M.wake n) r =
      Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S n r := by
  unfold Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom
  rw [(facts.nd.wake_st_record n).1, (facts.nd.wake_st_record n).2, facts.nd.wake_cache n]

/-- If the event at index `i` is a tick at `t`, the number of events strictly before `t` is at most
    `i`. -/
private theorem strictEventIndex_le_tickIndexOn₇₀ (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {i : Nat} {v : V} {t : Time}
    (hi : rho.events[i]? = some (Record.Event.tick v t)) :
    strictEventIndex rho t ≤ i := by
  by_contra hnot
  have hlt : i < strictEventIndex rho t := Nat.lt_of_not_ge hnot
  unfold strictEventIndex at hlt
  have hmem : Record.Event.tick v t ∈
      rho.events.filter (fun e => decide (e.time < t)) := by
    rw [Restated.filter_eq_takeOn facts S Hs Xb hf _ (Restated.downward_lt t)]
    exact List.mem_of_getElem? (by
      rw [List.getElem?_take_of_lt hlt]
      exact hi)
  have himpossible := (List.mem_filter.mp hmem).2
  simp only [decide_eq_true_eq, Record.Event.time] at himpossible
  exact lt_irrefl t himpossible

/-- The number of events strictly before the seed attestation's action instant is less than `stop`. -/
theorem PrefixFGSelectorConeAtOn.actionPrefix_lt (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} {Hs : Int → Finset V} {Xb : Finset V} {lo : Int}
    {W : Nat → V → M.N} {Wt : Time → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {start stop : Nat} {blocked : Height} {i : Nat}
    {a : NamedAttestation V} {ta : Time} {Cfg : NamedBlock V} {T : Block V}
    (hseed : Restated.PrefixFGSelectorConeAtOn M S rho W Wt Hs Xb start stop blocked i a ta Cfg T) :
    strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round) < stop := by
  have hle := strictEventIndex_le_tickIndexOn₇₀ facts S Hs Xb hf hseed.exactTick
  rw [hseed.actionTime_eq] at hle
  exact hle.trans_lt hseed.indexLtStop

/-- The seed attestation's action instant is at most the run's horizon. -/
theorem PrefixFGSelectorConeAtOn.actionHorizon (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} {Hs : Int → Finset V} {Xb : Finset V} {lo : Int}
    {W : Nat → V → M.N} {Wt : Time → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {start stop : Nat} {blocked : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg : NamedBlock V} {T : Block V}
    (hseed : Restated.PrefixFGSelectorConeAtOn M S rho W Wt Hs Xb start stop blocked i a ta Cfg T) :
    Restated.Vocabulary.Execution.Setup.a M S a.round ≤ rho.horizon := by
  have h := (hf.in_horizon (Record.Event.tick a.val_index ta)
    (List.mem_of_getElem? hseed.exactTick)).2
  simpa only [Record.Event.time, hseed.actionTime_eq, Record.Event.time] using h

/-- Under the bundle and the weight majority, if the selector cone holds for `a` along `W` and the
    window over `X` at `blocked + 1` holds before `first` along `W`, then for every read up to the
    action instant of round `a.round + 1`, in the horizon and at or after `lo`, every validator's
    store in `W (strictEventIndex rho read)` has `h_max` at most `blocked + 2`. -/
theorem PrefixFGSelectorConeAtOn.readFrontier_le_before_nextAction_run (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} {Hs : Int → Finset V} {Xb X : Finset V} {lo : Int}
    {W : Nat → V → M.N} {Wt : Time → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hX : ∀ t : Int, 0 ≤ t → Hs t ⊆ X)
    (hmajority : HonestWeightMajorityOn S rho Hs)
    {start first : Nat} {blocked : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg : NamedBlock V} {T : Block V}
    (hseed : Restated.PrefixFGSelectorConeAtOn M S rho W Wt Hs Xb start first blocked i a ta Cfg T)
    (hfirst : Restated.HeightWindowAtOn M S rho W X (blocked + 1) first)
    {read : Time} (hread : read ≤ Restated.Vocabulary.Execution.Setup.a M S (a.round + 1)) (w : V)
    (hreadHor : read ≤ rho.horizon) (hlo : lo ≤ read) :
    (W (strictEventIndex rho read) w).st.core.h_max ≤ blocked + 2 := by
  have hbound : (W (strictEventIndex rho read) w).st.core.h_max ≤
      (X.sup fun x => (W (strictEventIndex rho
        (Restated.Vocabulary.Execution.Setup.a M S (a.round + 1 - 1))) x).st.h_max) + 1 := by
    by_cases hlarge : 1 < (W (strictEventIndex rho read) w).st.h_max
    · obtain ⟨b, tb, hb, hemit, ht, hrow, _⟩ :=
        Restated.frontier_confirmationWitnessOn facts S Hs Xb hf hHs hHsXb hmajority hreadHor hlarge
      have hbX : b.val_index ∈ X := hX read (by linarith [hf.lo_pos]) hb
      have hshape := (Restated.Vocabulary.Proofs.Optimistic.emits_attest_shape facts S W hf.onePath hemit).2
      have hround : b.round < a.round + 1 := by
        by_contra hn
        have htime : Restated.Vocabulary.Execution.Setup.a M S b.round
            < Restated.Vocabulary.Execution.Setup.a M S (a.round + 1) := by
          simpa only [hshape] using ht.trans_le hread
        exact (not_lt_of_ge (Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.le_of_not_gt hn)))
          htime
      have htime : tb ≤ Restated.Vocabulary.Execution.Setup.a M S (a.round + 1 - 1) := by
        rw [hshape]
        exact Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.le_sub_one_of_lt hround)
      have hband := Restated.honestEmittedHeight_le_honestHMaxBeforeTimeOn facts
        S Hs Xb X hf hbX hemit hrow htime
      calc
        _ = ((W (strictEventIndex rho read) w).st.core.h_max - 1) + 1 :=
          (Nat.sub_add_cancel (Nat.le_of_lt hlarge)).symm
        _ ≤ _ := Nat.add_le_add_right hband 1
    · exact (Nat.le_of_not_gt hlarge).trans
        (Nat.succ_le_succ (Nat.zero_le _))
  simp only [Nat.add_sub_cancel] at hbound
  exact hbound.trans (Nat.add_le_add_right
    (hfirst.before _ (hseed.actionPrefix_lt facts hf)) 1)

open scoped DC in
/-- If the selector cone holds for `a`, then for every node state `n` of the action read staged at
    round `a.round` from the node state of `a`'s signer in `Wt (S.a a.round)`, every outcome of
    `n`'s round-`a.round` grade-2 candidate is some block `Q`. -/
theorem PrefixFGSelectorConeAtOn.exists_nodeQ2_l70 (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} {Hs : Int → Finset V} {Xb : Finset V}
    {W : Nat → V → M.N} {Wt : Time → V → M.N}
    {start first : Nat} {blocked : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg : NamedBlock V} {T : Block V}
    (hseed : Restated.PrefixFGSelectorConeAtOn M S rho W Wt Hs Xb start first blocked i a ta Cfg T) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (Wt (Restated.Vocabulary.Execution.Setup.a M S a.round) a.val_index) a.round,
    ∀ o : Option (Block V), Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n a.round ⇢ o →
      ∃ Q : Block V, o = some Q := by
  intro n hn o ho
  unfold Restated.Vocabulary.Internal.PhaseGrades.nodeQ2
    Restated.Vocabulary.Internal.PhaseGrades.nodeRead at ho
  obtain ⟨G, hG, rfl⟩ := returns_map_elim₇₀ _ _ _ ho
  have hround : (M.round_of S.hc (M.toHealing n.st.core).s) = a.round := by
    show (M.round_of S.hc (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.s) = a.round
    rw [facts.sto.toHealing_s]
    obtain ⟨c, -, st, hst, rfl⟩ := hn
    show (M.round_of S.hc) (M.mkNode st _ c).st.core.s = a.round
    rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; rw [(facts.dt.named_confirmation_clock _ _ _ _ _ st hst).2,
      facts.hd.ModelProperties_setClock_core_s]
    exact Restated.Vocabulary.Proofs.HealingLemmas.round_of_slotOf_a facts S a.round
  obtain ⟨A2, hA2⟩ := facts.dt.grade2_block_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) a.round
  obtain ⟨F, hF⟩ := facts.dt.fg_source_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) a.round A2
  have hsrc : Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n ⇢ F := by
    show (M.grade2_block_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
        (M.round_of S.hc (M.toHealing n.st.core).s) >>= fun g =>
      M.fg_source_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
        (M.round_of S.hc (M.toHealing n.st.core).s) g) ⇢ F
    rw [hround]
    exact returns_bind_intro₇₀ _ _ A2 F hA2 hF
  have hFe := hseed.exactFGSource n hn F hsrc
  exact facts.dt.read_Q2_isSome_of_fg_source_with_grade2 (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) a.round A2 hA2 F hF hFe G hG

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.Optimistic

local macro "p58% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Claims.Restated.Claim13beRoute3_58)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

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
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.Optimistic

open scoped DC in
/-- If `m` can return `a`, then `f <$> m` can return `f a`. -/
private theorem returns_map_intro₇₀r {α β : Type} (f : α → β) (m : DC.NDRE α) (a : α)
    (h : m ⇢ a) : (f <$> m) ⇢ f a := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image]
  exact ⟨_, h, rfl⟩

open scoped DC in
/-- The round-`r` action read computed from `before` has some node state. -/
private theorem actionReadFrom_nonempty₇₀r (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∃ n, n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r := by
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc before.st.core.toHealing
    (Restated.Vocabulary.Execution.Setup.a M S r) before.cache
  obtain ⟨st, hst⟩ := facts.dt.duties_update_confirmation_with_nonempty (M.gradeContract c) S.E S.hc
    (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r))
    (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1)
  exact ⟨_, c, hc, st, hst, rfl⟩

open scoped DC in
/-- The grade-2 candidate read at `n` for round `r` has an outcome. -/
private theorem nodeQ2_nonempty₇₀r (facts : Record.Facts M) (S : Setup V) (n : M.N) (r : Round) :
    ∃ o : Option (Block V), Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ o := by
  obtain ⟨G, hG⟩ := facts.gr.read_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) r
  refine ⟨G.Q2, ?_⟩
  unfold Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 Restated.Vocabulary.Internal.PhaseGrades.nodeRead
  exact returns_map_intro₇₀r (fun g : DecoupledConsensusModel.Protocol.GradeRead V => g.Q2) _ G hG

open scoped DC in
/-- Under the bundle along `W`, if `n` is a node state of `v`'s round-`r` action read from its node
    state in `W`'s world before `S.a r` and the Q2 of `n` can return `some Q`, then `0 < r`. -/
theorem runHistory_selectedQ2_round_posOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} {r : Round} {Q : Block V} {n : M.N}
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r)
    (hQ : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ some Q) :
    0 < r :=
  Restated.selectedQ2_round_pos_named_historyOn facts S Hs Xb hf hn hQ

/-- Under the bundle along `W`, if the selector cone holds for `a` along `W` with the worlds before
    each instant those of `W`, then `0 < a.round`. -/
theorem PrefixFGSelectorConeAtOn.round_pos_l70 (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} {Hs : Int → Finset V} {Xb : Finset V} {lo : Int}
    {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {start first : Nat} {blocked : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg : NamedBlock V} {T : Block V}
    (hseed : Restated.PrefixFGSelectorConeAtOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs Xb start first blocked i a ta Cfg T) :
    0 < a.round := by
  obtain ⟨n, hn⟩ := actionReadFrom_nonempty₇₀r facts S
    (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round)) a.val_index) a.round
  obtain ⟨o, ho⟩ := nodeQ2_nonempty₇₀r facts S n a.round
  obtain ⟨Q, rfl⟩ := hseed.exists_nodeQ2_l70 facts n hn o ho
  exact Restated.runHistory_selectedQ2_round_posOn facts S Hs Xb hf hn ho

/-- Under the bundle along `W`, if `v ∈ Xb` and `D` is a body of a node state `n` of `v`'s round-`r`
    action read from `W`'s world before `S.a r`, then `D` is a run block along `W` read through
    `Xb`. -/
theorem runHistory_actionBody_runBlockOn (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} (Hs : Int → Finset V) (Xb : Finset V) {lo : Int}
    {W : Nat → V → M.N} (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    {v : V} (hv : v ∈ Xb) {r : Round} {D : NamedBlock V} {n : M.N}
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) v) r)
    (hD : D ∈ n.st.bodies) :
    Restated.RunBlockOn M S rho W Xb D :=
  Restated.actionBody_runBlock_named_historyOn facts S Hs Xb hf hv hn hD

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.Optimistic

local macro "p63% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Claims.Restated.Claim13beRoute3_63)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

end

/-! ## Checkpoint protection along the path of the bundle -/

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.Optimistic
open scoped DC

local macro "p50% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Claims.Restated.Claim13beRoute3_50)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

local macro "p47b% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Claims.Restated.Claim13beRoute3_47b)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

local macro "p64% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Claims.Restated.Claim13beRoute3_64)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

set_option linter.unusedVariables false


/-- The round-`r` action read computed from `before` has some node state. -/
private theorem actionReadFrom_nonempty₇₀w (facts : Record.Facts M) (S : Setup V) (before : M.N)
    (r : Round) :
    ∃ n, n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S before r := by
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc before.st.core.toHealing
    (Restated.Vocabulary.Execution.Setup.a M S r) before.cache
  obtain ⟨st, hst⟩ := facts.dt.duties_update_confirmation_with_nonempty (M.gradeContract c) S.E S.hc
    (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r))
    (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1)
  exact ⟨_, c, hc, st, hst, rfl⟩

/-- An action instant is not negative. -/
private theorem a_nonneg₇₀w (facts : Record.Facts M) (S : Setup V) (r : Round) :
    0 ≤ Restated.Vocabulary.Execution.Setup.a M S r := by
  show 0 ≤ M.a S.hc S.E.Δ r
  rw [facts.sch.a_eq_confirmation_time]
  exact le_trans (facts.sch.Optimistic_proposal_time_nonneg S.E _)
    (facts.sch.proposal_time_le_confirmation_time S.E _)

/-- If `lo` is at or before one delay before the grade-2 window start of slot `s`'s round, every
    member of the set for `s`'s vote instant in `s`'s committee passes that round's grade-1 awake
    test on its node state before each of its ticks at that instant. -/
private theorem awake_g1_committee₇₀w (facts : Record.Facts M) {S : Setup V}
    {rho : Record.Run V} {Hs : Int → Finset V} {Xb : Finset V} {lo : Int} {W : Nat → V → M.N}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo) {s : Slot}
    (hwin : lo ≤ M.early S.E S.hc (M.round_of S.hc s) .g2 - S.E.Δ) :
    ∀ w ∈ Hs (M.vote_time S.E s), w ∈ S.E.committee s →
      ∀ j : Nat, rho.events[j]? = some (Record.Event.tick w (M.vote_time S.E s)) →
        M.awake_for_grade1 S w (W j w) (M.round_of S.hc s) := by
  intro w hw _ j hj
  have h2 := facts.gr.q10_early_g2_le_early_g1 S (M.round_of S.hc s)
  exact hf.awake_g1 _ _ j _ (Or.inr rfl) hj hw (by linarith)

/-- If `S.a r ≤ vote_time s`, then `r ≤ round_of s`. -/
private theorem round_le_round_of_of_action_le_vote₇₀w (facts : Record.Facts M) (S : Setup V)
    {r : Round} {s : Slot}
    (h : Restated.Vocabulary.Execution.Setup.a M S r ≤ M.vote_time S.E s) :
    r ≤ M.round_of S.hc s := by
  have hopen : M.opening_slot S.hc r ≤ s := by
    by_contra hlt
    have hlt' : s + 1 ≤ M.opening_slot S.hc r := Nat.lt_of_not_le hlt
    have h1 := facts.sch.voteTime_lt_nextProposal_l86d S.E s
    have h2 := facts.sch.proposal_time_le_confirmation_time S.E (s + 1)
    have h3 := facts.sch.confirmation_time_mono S hlt'
    have h4 : Restated.Vocabulary.Execution.Setup.a M S r =
        M.confirmation_time S.E (M.opening_slot S.hc r) :=
      facts.sch.a_eq_confirmation_time S.hc S.E r
    linarith
  have hmono := facts.gr.round_of_mono_sts S.hc hopen
  rwa [facts.gr.round_of_opening_slot_eq S.hc r] at hmono

/-- Under the bundle along `W`, the committee majority and the weight bound, if the selector cone
    holds for `a` with checkpoint `T`, the window over `X` at `blocked + 1` holds before `first`,
    the named frame over `X` holds at `blocked` up to `first − 1`, round `a.round` is ready and
    minimal, the old-root contract holds, `S.a (cut − 1)` is before `first`, `w ∈ X` has `h_max`
    greater than `blocked` in `W (strictEventIndex rho time)`, `C` is a body of `w`'s store there
    justified by its FG root, and a row `b` of a member of the set for `S.a b.round` before round
    `cut` targets `C`'s justification, with a node state of its signer's action read whose FG
    confirmation witness can return that root, then the FG root of `w`'s store is an ancestor of
    `T`. -/
theorem PrefixFGSelectorConeAtOn.oldTargetRoot_preceq_of_strictActionCut_of_frame_run
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
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hseed : Restated.PrefixFGSelectorConeAtOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs Xb start first blocked i a ta Cfg T.erase)
    (hfirst : Restated.HeightWindowAtOn M S rho W X (blocked + 1) first)
    (hframe : Restated.NamedHeightRegimeFrameOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs X Xb blocked (first - 1) Tprev c0)
    (hc0 : c0 ≤ a.round)
    (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho a.round)
    (hpostPrev : S.E.t_GST ≤ Restated.Vocabulary.Execution.Setup.a M S (a.round - 1))
    (hpred : Restated.NamedOldTargetRootBelowRunOn M S rho W
      (fun t => W (strictEventIndex rho t)) Hs X Xb first blocked T)
    (hminimal : ∀ (b : NamedAttestation V) (tb : Time),
      b.val_index ∈ Hs tb →
      Restated.Vocabulary.Execution.NamedRun.emits M S rho W b.val_index (Object.attest b) tb →
      b.height_pair.erase.height? = some (blocked + 1) →
      a.round ≤ b.round)
    {cut : Round}
    (hcut : strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S (cut - 1)) < first)
    {w : V} (hw : w ∈ X) {time : Time}
    (hfrontier : blocked < (W (strictEventIndex rho time) w).st.h_max)
    {C : NamedBlock V} (hC : C ∈ (W (strictEventIndex rho time) w).st.bodies)
    {b : NamedAttestation V} {tb : Time}
    (hb : b.val_index ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S b.round))
    (hemit : Restated.Vocabulary.Execution.NamedRun.emits M S rho W b.val_index (Object.attest b) tb)
    (hold : b.round < cut)
    (hpair : b.height_pair.erase = HeightPair.target
      (M.derive_named S.E S.cfg C).h_j
      (M.derive_named S.E S.cfg C).J.root)
    (hJ : (M.derive_named S.E S.cfg C).J =
      M.get_fg_root (M.toHealing (W (strictEventIndex rho time) w).st.core).toFG)
    {n : M.N}
    (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S b.round)) b.val_index)
      b.round)
    (hR : Restated.Vocabulary.Proofs.HealingSurface.fgConfirmationWitness M S n ⇢
      some (M.get_fg_root (M.toHealing (W (strictEventIndex rho time) w).st.core).toFG))
    (hlo : lo ≤ M.opening S.E S.hc (a.round - S.hc.η_SG))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S k + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    Block.Preceq
      (M.get_fg_root (M.toHealing (W (strictEventIndex rho time) w).st.core).toFG) T.erase := by
  have htime : tb = Restated.Vocabulary.Execution.Setup.a M S b.round :=
    (Restated.Vocabulary.Proofs.Optimistic.emits_attest_shape facts S W hf.onePath hemit).2
  have hbX : b.val_index ∈ X := hX _ (a_nonneg₇₀w facts S b.round) hb
  have hbTb : b.val_index ∈ Hs tb := by rw [htime]; exact hb
  have hactionLe : Restated.Vocabulary.Execution.Setup.a M S b.round ≤
      Restated.Vocabulary.Execution.Setup.a M S (cut - 1) :=
    Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.le_sub_one_of_lt hold)
  have hheightCap := hfirst.before _ hcut
  have hrow : b.height_pair.erase.height? = some (M.derive_named S.E S.cfg C).h_j := by
    simp only [hpair, HeightPair.height?]
  have hupper : (M.derive_named S.E S.cfg C).h_j ≤ blocked + 1 :=
    (Restated.honestEmittedHeight_le_honestHMaxBeforeTimeOn facts S Hs Xb X hf hbX hemit hrow
      (htime ▸ hactionLe)).trans hheightCap
  have hbefore : strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S b.round) < first :=
    (strictEventIndex_mono rho hactionLe).trans_lt hcut
  rcases facts.cs.justified_ancestor_height S.E S.cfg C with hz | ⟨K, hKC, hKerase, hKheight⟩
  · have hgen : (M.derive_named S.E S.cfg C).J = Block.genesis :=
      facts.cs.justified_zero_is_genesis S.E S.cfg C hz
    rw [← hJ, hgen]
    exact (preceq_eq_true_iff_Preceq.mp (Protocol.preceq_genesis T.erase))
  have hpc : Restated.Vocabulary.Proofs.NamedStore.NamedParentClosed M
      (W (strictEventIndex rho time) w).st :=
    (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho _ w _
      (hf.onePath _).1).1.1.1.2.2.1
  have hK : K ∈ (W (strictEventIndex rho time) w).st.bodies :=
    (p50% namedAncestor_mem₅₀b) hpc hC hKC
  have hKrun : Restated.RunBlockOn M S rho W Xb K :=
    Restated.runBlock_of_stateBefore_memOn facts S W Xb (hXXb hw) hK
  have hKR : K.erase =
      M.get_fg_root (M.toHealing (W (strictEventIndex rho time) w).st.core).toFG :=
    hKerase.trans hJ
  have hR' : Restated.Vocabulary.Proofs.HealingSurface.fgConfirmationWitness M S n ⇢ some K.erase := by
    rw [hKR]; exact hR
  by_cases heq : (M.derive_named S.E S.cfg C).h_j = blocked + 1
  · have hrowH : b.height_pair.erase.height? = some (blocked + 1) := heq ▸ hrow
    have hT := PrefixFGSelectorConeAtOn.confirmationWitness_of_source_of_frame_named facts hf hHs hHsXb hX hXXb hcom hfb hseed hfirst hframe hc0 ready
      hpostPrev hb hemit hrowH (hminimal b tb hbTb hemit hrowH) hbefore hlo hA n hn _ hR
    have hRT := Option.some.inj hT
    rw [hRT]
    exact (preceq_eq_true_iff_Preceq.mp (Block.preceq_self T.erase))
  · have hlow : (M.derive_named S.E S.cfg C).h_j ≤ blocked :=
      Nat.le_of_lt_succ (lt_of_le_of_ne hupper heq)
    have hKlow : (M.derive_named S.E S.cfg K).h ≤ blocked := by
      rw [hKheight]
      exact hlow
    rcases eq_or_lt_of_le hKlow with heqB | hlt
    · have hpairB : b.height_pair.erase = HeightPair.target blocked K.erase.root := by
        rw [hpair, ← hKheight, heqB, hKerase]
      rw [← hKR]
      exact Proofs.NamedWire.erase_preceq
        (hpred b tb hb hemit hbefore K hKrun heqB hpairB n hn hR' w hw time hfrontier hKR.symm)
    · have hlowPred : (M.derive_named S.E S.cfg K).h ≤ blocked - 1 := Nat.le_sub_one_of_lt hlt
      have hblockedPos : 0 < blocked := Nat.zero_lt_of_lt hlt
      have hfrontierPred : blocked - 1 + 1 < (W (strictEventIndex rho time) w).st.h_max := by
        rwa [Nat.sub_add_cancel (Nat.succ_le_iff.mpr hblockedPos)]
      obtain ⟨n₀, hn₀⟩ := actionReadFrom_nonempty₇₀w facts S
        (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round)) a.val_index)
        a.round
      obtain ⟨P, _, hPentry, hPheight0, _, hPrun⟩ :=
        Restated.action_named_checkpointOn facts S Hs Xb hf (hHsXb _ hseed.signerHonest) hn₀
          (hseed.sourceMem n₀ hn₀)
      have hPT : P.erase = T.erase := hPentry.trans hseed.checkpointDerived.symm
      have hPheight : (M.derive_named S.E S.cfg P).h = blocked + 1 :=
        hPheight0.trans hseed.sourceDerivedHeight
      have hlegacy : Restated.FinalizedRootsBelowAtReadOn M S rho
          (fun t => W (strictEventIndex rho t)) X (blocked - 1) P.erase :=
        Restated.finalizedRootsBelowAtRead_of_accountableOn facts S Hs Xb X hf hXXb
          hf.slashableBound hPrun (by
            rw [hPheight]
            exact (Nat.sub_le blocked 1).trans_lt (Nat.lt_succ_self blocked))
      have hout :=
        Restated.lowFGRoot_preceq_of_frontier_gap_of_finalizedRootsBelowOn facts S X
          (Wt := fun t => W (strictEventIndex rho t)) hw
          ((p47b% path_mem_stateBeforeTime₄₇b) facts S Hs Xb hf time)
          hlegacy hfrontierPred hK hKR hlowPred
      simpa only [hPT] using hout

local macro "p63% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Claims.Restated.Claim13beRoute3_63)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

/-- Under the hypotheses of
    `PrefixFGSelectorConeAtOn.oldTargetRoot_preceq_of_strictActionCut_of_frame_run`, for every read
    from `S.a a.round` to `S.a (a.round + 1)` in the horizon, every member of the set for the read
    has the FG root of its store in `W (strictEventIndex rho read)` an ancestor of `T`. -/
theorem PrefixFGSelectorConeAtOn.fgRoot_preceq_before_nextAction_of_frame_run
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
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hseed : Restated.PrefixFGSelectorConeAtOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs Xb start first blocked i a ta Cfg T.erase)
    (hfirst : Restated.HeightWindowAtOn M S rho W X (blocked + 1) first)
    (hframe : Restated.NamedHeightRegimeFrameOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs X Xb blocked (first - 1) Tprev c0)
    (hc0 : c0 ≤ a.round)
    (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho a.round)
    (hpostPrev : S.E.t_GST ≤ Restated.Vocabulary.Execution.Setup.a M S (a.round - 1))
    (hpred : Restated.NamedOldTargetRootBelowRunOn M S rho W
      (fun t => W (strictEventIndex rho t)) Hs X Xb first blocked T)
    (hminimal : ∀ (b : NamedAttestation V) (tb : Time),
      b.val_index ∈ Hs tb →
      Restated.Vocabulary.Execution.NamedRun.emits M S rho W b.val_index (Object.attest b) tb →
      b.height_pair.erase.height? = some (blocked + 1) →
      a.round ≤ b.round)
    {read : Time} (hlo' : Restated.Vocabulary.Execution.Setup.a M S a.round ≤ read)
    (hhi : read ≤ Restated.Vocabulary.Execution.Setup.a M S (a.round + 1))
    {w : V} (hw : w ∈ Hs read)
    (hreadHor : read ≤ rho.horizon)
    (hlo : lo ≤ M.opening S.E S.hc (a.round - S.hc.η_SG))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S k + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    Block.Preceq
      (M.get_fg_root (M.toHealing (W (strictEventIndex rho read) w).st.core).toFG) T.erase := by
  have hmajority : HonestWeightMajorityOn S rho Hs :=
    honestWeightMajorityOn_of_belowOneThirdOn hfb
  have hread0 : 0 ≤ read := (a_nonneg₇₀w facts S a.round).trans hlo'
  have hwX : w ∈ X := hX read hread0 hw
  obtain ⟨hloEarly, -, -, -⟩ := Restated.loBounds_l70 facts S (hseed.round_pos_l70 facts hf) hlo
  have hwView : w ∈ Hs (M.view_freeze S.E (M.opening_slot S.hc a.round)) := by
    refine hHs _ _ ?_ hw
    obtain ⟨-, -, -, hview, -, ha⟩ := Restated.openingInstants_l63 facts S a.round
    rw [hview]
    have := S.E.Δ_pos
    linarith
  have hwit := Restated.fgRoot_confirmationWitness_at_readOn facts S Hs Xb hf hHs hHsXb hmajority
      (hHsXb _ hw) read hreadHor
  dsimp only at hwit
  rcases hwit with hgen | ⟨C, hC, hJ, b, tb, hb, hemit, htb, hpair, hR⟩
  · rw [hgen]
    exact preceq_eq_true_iff_Preceq.mp (Protocol.preceq_genesis T.erase)
  · have ht : tb = Restated.Vocabulary.Execution.Setup.a M S b.round :=
      (Restated.Vocabulary.Proofs.Optimistic.emits_attest_shape facts S W hf.onePath hemit).2
    have hold : b.round < a.round + 1 := by
      by_contra hn
      have hle := Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.le_of_not_gt hn)
      exact (not_lt_of_ge hle) (ht ▸ htb.trans_le hhi)
    have hbAction : b.val_index ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S b.round) :=
      hHs _ _ (ht ▸ htb.le) hb
    have hcut : strictEventIndex rho
        (Restated.Vocabulary.Execution.Setup.a M S (a.round + 1 - 1)) < first := by
      simpa only [Nat.add_sub_cancel] using hseed.actionPrefix_lt facts hf
    obtain ⟨nb, hnb⟩ := actionReadFrom_nonempty₇₀w facts S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S b.round)) b.val_index)
      b.round
    obtain ⟨o, ho⟩ := (p63% actionFGSource_nonempty₆₃w) facts S nb
    exact hseed.oldTargetRoot_preceq_of_strictActionCut_of_frame_run facts
      hf hHs hHsXb hX hXXb hcom hfb hfirst hframe hc0 ready hpostPrev hpred
        hminimal hcut hwX
          (Nat.lt_of_succ_le
            (hseed.localFrontier_ge_from_source_of_frame_named facts
              hf hHs hHsXb hX hframe ready hlo' hwView hloEarly))
          hC hbAction hemit hold hpair hJ hnb (hR nb hnb o ho) hlo hA

/-- Under the hypotheses of
    `PrefixFGSelectorConeAtOn.oldTargetRoot_preceq_of_strictActionCut_of_frame_run`, for every read
    from `S.a a.round` on in the horizon, if every member of the set for `S.a r`, for each later
    round `r` with `S.a r` before the read, has every FG confirmation witness of its action read
    compatible with `T`, then every member of the set for the read has the FG root of its store in
    `W (strictEventIndex rho read)` compatible with `T`. -/
theorem PrefixFGSelectorConeAtOn.fgRoot_compatible_of_recentWitnessHistory_of_frame_run
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
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hseed : Restated.PrefixFGSelectorConeAtOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs Xb start first blocked i a ta Cfg T.erase)
    (hfirst : Restated.HeightWindowAtOn M S rho W X (blocked + 1) first)
    (hframe : Restated.NamedHeightRegimeFrameOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs X Xb blocked (first - 1) Tprev c0)
    (hc0 : c0 ≤ a.round)
    (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho a.round)
    (hpostPrev : S.E.t_GST ≤ Restated.Vocabulary.Execution.Setup.a M S (a.round - 1))
    (hpred : Restated.NamedOldTargetRootBelowRunOn M S rho W
      (fun t => W (strictEventIndex rho t)) Hs X Xb first blocked T)
    (hminimal : ∀ (b : NamedAttestation V) (tb : Time),
      b.val_index ∈ Hs tb →
      Restated.Vocabulary.Execution.NamedRun.emits M S rho W b.val_index (Object.attest b) tb →
      b.height_pair.erase.height? = some (blocked + 1) →
      a.round ≤ b.round)
    {read : Time} (hread : Restated.Vocabulary.Execution.Setup.a M S a.round ≤ read)
    (hhistory : ∀ r, a.round + 1 ≤ r → Restated.Vocabulary.Execution.Setup.a M S r < read →
      ∀ w ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S r), ∀ B : Block V,
        (∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
            (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) w) r,
          ∀ o, Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n ⇢ o →
            Restated.Vocabulary.Proofs.HealingSurface.fgConfirmationWitness M S n ⇢ some B) →
          Block.compatible B T.erase = true)
    {w : V} (hw : w ∈ Hs read)
    (hreadHor : read ≤ rho.horizon)
    (hlo : lo ≤ M.opening S.E S.hc (a.round - S.hc.η_SG))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S k + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    Block.compatible
      (M.get_fg_root (M.toHealing (W (strictEventIndex rho read) w).st.core).toFG) T.erase =
        true := by
  have hmajority : HonestWeightMajorityOn S rho Hs :=
    honestWeightMajorityOn_of_belowOneThirdOn hfb
  have hread0 : 0 ≤ read := (a_nonneg₇₀w facts S a.round).trans hread
  have hwX : w ∈ X := hX read hread0 hw
  obtain ⟨hloEarly, -, -, -⟩ := Restated.loBounds_l70 facts S (hseed.round_pos_l70 facts hf) hlo
  have hwView : w ∈ Hs (M.view_freeze S.E (M.opening_slot S.hc a.round)) := by
    refine hHs _ _ ?_ hw
    obtain ⟨-, -, -, hview, -, ha⟩ := Restated.openingInstants_l63 facts S a.round
    rw [hview]
    have := S.E.Δ_pos
    linarith
  apply Restated.fgRoot_compatible_of_bootstrap_and_recentActions_at_readOn facts S Hs Xb hf hHs
    hHsXb hmajority (hHsXb _ hw) hreadHor (cut := a.round + 1)
  · intro r hr ht v hv B hB
    exact compatible_of_cases (compatible_cases (hhistory r hr ht v hv B hB)).symm
  · intro C b tb
    dsimp only
    intro hC hJ hb hemit _ hold hpair hR
    have htb : tb = Restated.Vocabulary.Execution.Setup.a M S b.round :=
      (Restated.Vocabulary.Proofs.Optimistic.emits_attest_shape facts S W hf.onePath hemit).2
    have hbAction : b.val_index ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S b.round) := by
      rw [← htb]; exact hb
    have hcut : strictEventIndex rho
        (Restated.Vocabulary.Execution.Setup.a M S (a.round + 1 - 1)) < first := by
      simpa only [Nat.add_sub_cancel] using hseed.actionPrefix_lt facts hf
    have hfrontier : blocked < (W (strictEventIndex rho read) w).st.h_max :=
      Nat.lt_of_succ_le
        (hseed.localFrontier_ge_from_source_of_frame_named facts
          hf hHs hHsXb hX hframe ready hread hwView hloEarly)
    obtain ⟨nb, hnb⟩ := actionReadFrom_nonempty₇₀w facts S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S b.round)) b.val_index)
      b.round
    obtain ⟨o, ho⟩ := (p63% actionFGSource_nonempty₆₃w) facts S nb
    have hroot :=
      hseed.oldTargetRoot_preceq_of_strictActionCut_of_frame_run facts
        hf hHs hHsXb hX hXXb hcom hfb hfirst hframe hc0 ready hpostPrev hpred
          hminimal hcut hwX hfrontier hC hbAction hemit hold hpair hJ hnb (hR nb hnb o ho) hlo hA
    exact compatible_of_cases (Or.inr hroot)

/-- Under the hypotheses of
    `PrefixFGSelectorConeAtOn.oldTargetRoot_preceq_of_strictActionCut_of_frame_run`, if slot `s` is
    positive, at or after `lo` with its confirmation instant in the horizon, the source action
    instant is at most the vote instant of `s + 1`, the SG emissions of the round before the round
    of `s + 1` are compatible with `T`, every later-round FG confirmation witness read before the
    vote instant of `s + 1` is compatible with `T`, and the votes of slot `s` descend from `T`, then
    every outcome of the in-tree head at the vote-duty read of every member of the set for the vote
    instant of `s + 1` descends from `T`, and so do the votes of slot `s + 1` along `W`. -/
theorem PrefixFGSelectorConeAtOn.checkpointVoteStep_of_actionHistories_of_frame_run
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
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hseed : Restated.PrefixFGSelectorConeAtOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs Xb start first blocked i a ta Cfg T.erase)
    (hfirst : Restated.HeightWindowAtOn M S rho W X (blocked + 1) first)
    (hframe : Restated.NamedHeightRegimeFrameOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs X Xb blocked (first - 1) Tprev c0)
    (hc0 : c0 ≤ a.round)
    (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho a.round)
    (hpostPrev : S.E.t_GST ≤ Restated.Vocabulary.Execution.Setup.a M S (a.round - 1))
    (hpred : Restated.NamedOldTargetRootBelowRunOn M S rho W
      (fun t => W (strictEventIndex rho t)) Hs X Xb first blocked T)
    (hminimal : ∀ (b : NamedAttestation V) (tb : Time),
      b.val_index ∈ Hs tb →
      Restated.Vocabulary.Execution.NamedRun.emits M S rho W b.val_index (Object.attest b) tb →
      b.height_pair.erase.height? = some (blocked + 1) →
      a.round ≤ b.round)
    {s : Slot} (hs : 0 < s)
    (hpost : lo ≤ M.vote_time S.E s)
    (hhor : M.confirmation_time S.E s ≤ rho.horizon)
    (hsourceRead : Restated.Vocabulary.Execution.Setup.a M S a.round ≤ M.vote_time S.E (s + 1))
    (hc : 1 ≤ M.round_of S.hc (s + 1))
    (hsg : Restated.HonestSGEmissionsCompatibleAtRoundOn M S rho W
      (fun t => W (strictEventIndex rho t)) Hs (M.round_of S.hc (s + 1) - 1) T.erase)
    (hsgPost : lo ≤ Restated.Vocabulary.Execution.Setup.a M S (M.round_of S.hc (s + 1) - 1))
    (hhistory : ∀ r, a.round + 1 ≤ r →
      Restated.Vocabulary.Execution.Setup.a M S r < M.vote_time S.E (s + 1) →
      ∀ w ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S r),
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) w) r,
      ∀ B : Block V,
        Restated.Vocabulary.Proofs.HealingSurface.fgConfirmationWitness M S n ⇢ some B →
          Block.compatible B T.erase = true)
    (hgf : Restated.NamedHonestVotesConeOn M S rho W Hs Xb s
      (fun Y => Block.Preceq T.erase Y))
    (hlo : lo ≤ M.opening S.E S.hc (a.round - S.hc.η_SG))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S k + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k)
    (hAprev : ∀ u ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S (M.round_of S.hc (s + 1) - 1) + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S (M.round_of S.hc (s + 1) - 1))) → M.awake_for_grade2 S u (W j u) (M.round_of S.hc (s + 1) - 1)) :
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
        Block.Preceq T.erase H) ∧
      Restated.NamedHonestVotesConeOn M S rho W Hs Xb (s + 1)
        (fun Y => Block.Preceq T.erase Y) := by
  have hmajority : HonestWeightMajorityOn S rho Hs :=
    honestWeightMajorityOn_of_belowOneThirdOn hfb
  have hvoteHor : M.vote_time S.E (s + 1) ≤ rho.horizon :=
    le_trans (le_of_lt (lt_of_lt_of_le (Int.lt_add_of_pos_right _ S.E.Δ_pos)
      (facts.sch.vote_time_succ_add_delta_le_confirmation_time S.E s))) hhor
  have hvote0 : 0 ≤ M.vote_time S.E (s + 1) :=
    (a_nonneg₇₀w facts S a.round).trans hsourceRead
  have hdutyCore : ∀ w : V, Restated.Vocabulary.Proofs.Optimistic.voteStore M S
      (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core (s + 1) =
      (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
        (M.vote_time S.E (s + 1))).core := by
    intro w
    rw [Restated.Vocabulary.Proofs.Optimistic.voteStore,
      Restated.Vocabulary.Proofs.Optimistic.tickStore, facts.hd.setClock_core_eq_store_with_t_s]
  have hhistory' : ∀ r, a.round + 1 ≤ r →
      Restated.Vocabulary.Execution.Setup.a M S r < M.vote_time S.E (s + 1) →
      ∀ w ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S r), ∀ B : Block V,
        (∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
            (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) w) r,
          ∀ o, Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n ⇢ o →
            Restated.Vocabulary.Proofs.HealingSurface.fgConfirmationWitness M S n ⇢ some B) →
          Block.compatible B T.erase = true := by
    intro r hr ht w hw B hB
    obtain ⟨n, hn⟩ := actionReadFrom_nonempty₇₀w facts S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) w) r
    obtain ⟨o, ho⟩ := (p63% actionFGSource_nonempty₆₃w) facts S n
    exact hhistory r hr ht w hw n hn B (hB n hn o ho)
  have hroots : ∀ w ∈ Hs (M.vote_time S.E (s + 1)), Block.compatible
      (M.get_fg_root
        (M.toHealing (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
          (M.vote_time S.E (s + 1))).core).toFG) T.erase = true := by
    intro w hw
    have hroot := hseed.fgRoot_compatible_of_recentWitnessHistory_of_frame_run facts
      hf hHs hHsXb hX hXXb hcom hfb hfirst hframe hc0 ready hpostPrev         hpred hminimal hsourceRead hhistory' hw hvoteHor hlo hA
    rw [← hdutyCore w, Restated.Vocabulary.Proofs.Optimistic.voteStore,
      Restated.Vocabulary.Proofs.Optimistic.tickStore]
    exact (facts.fc.get_fg_root_set_clock_slot _ _ _).symm ▸ hroot
  obtain ⟨n₀, hn₀⟩ := actionReadFrom_nonempty₇₀w facts S
    (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round)) a.val_index)
    a.round
  obtain ⟨K, _, hKT0, hKheight0, _, hKrun⟩ :=
    Restated.action_named_checkpointOn facts S Hs Xb hf (hHsXb _ hseed.signerHonest) hn₀
      (hseed.sourceMem n₀ hn₀)
  have hKT : K.erase = T.erase := hKT0.trans hseed.checkpointDerived.symm
  have hKheight : (M.derive_named S.E S.cfg K).h = blocked + 1 :=
    hKheight0.trans hseed.sourceDerivedHeight
  have hrunV := awake_g1_committee₇₀w facts hf (s := s + 1)
    (Restated.lo_le_early_g2_sub_delta_of_opening facts S
      (Restated.PrefixFGSelectorConeAtOn.round_pos_l70 facts hf hseed) hlo
      (round_le_round_of_of_action_le_vote₇₀w facts S hsourceRead))
  refine Restated.goldfishCone_succ_of_runFrontierWitnessesOn facts
    S Hs Xb hf hHs hHsXb hcom hmajority hs hpost hhor hgf ?_ hroots ?_ hrunV
  · intro w _hw C hCerase hhigh hCrun b tb J hb hemit htb hrow nr hnr hselected _
    have hCK : C = K := by
      apply hf.rootCollisionFree.root_injective
        C K hCrun hKrun C K
          (Or.inl (Proofs.NamedAncestry.named_self C))
          (Or.inr (Proofs.NamedAncestry.named_self K))
      rw [← Proofs.NamedWire.erase_root C, hCerase, ← hKT,
        Proofs.NamedWire.erase_root]
    subst hCK
    have hbX : b.val_index ∈ X := hX _ hvote0 hb
    by_cases hold : b.round < a.round + 1
    · have htime : tb ≤ Restated.Vocabulary.Execution.Setup.a M S a.round := by
        rw [(Restated.Vocabulary.Proofs.Optimistic.emits_attest_shape facts S W hf.onePath hemit).2]
        exact Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.le_of_lt_succ hold)
      have hbound := Restated.honestEmittedHeight_le_honestHMaxBeforeTimeOn facts
        S Hs Xb X hf hbX hemit hrow htime
      have hfloor := hfirst.before _ (hseed.actionPrefix_lt facts hf)
      have hrowLe :
          (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
            (M.vote_time S.E (s + 1))).core.h_max - 1 ≤ (M.derive_named S.E S.cfg C).h := by
        rw [hKheight, ← hdutyCore w]
        exact hbound.trans hfloor
      exact False.elim ((Nat.not_lt_of_ge hrowLe) hhigh)
    · have htbA : tb = Restated.Vocabulary.Execution.Setup.a M S b.round :=
        (Restated.Vocabulary.Proofs.Optimistic.emits_attest_shape facts S W hf.onePath hemit).2
      have hbA : b.val_index ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S b.round) :=
        hHs _ _ (htbA ▸ htb.le) hb
      have hcompat := hhistory b.round (Nat.le_of_not_gt hold)
          (by simpa only [htbA] using htb)
          b.val_index hbA nr hnr (M.derive_named S.E S.cfg J).T_h hselected
      rw [hKT]
      exact DecoupledConsensusModel.Protocol.compatible_comm hcompat
  · intro w hw c hcc A hAnchor
    have hdomainEq : M.domain S.E S.hc (M.round_of S.hc (s + 1)) .g1 =
        M.proposal_time S.E (M.opening_slot S.hc (M.round_of S.hc (s + 1))) :=
      (facts.gr.Sts_domain_g1_eq_opening S _).trans (facts.gr.opening_eq_proposal_time _ _ _)
    have hdom : M.domain S.E S.hc (M.round_of S.hc (s + 1)) .g1 ≤ M.vote_time S.E (s + 1) := by
      rw [hdomainEq]
      exact (facts.sch.proposal_time_mono S.E
        (facts.gr.opening_slot_round_of_le_slot S.hc (s + 1))).trans
        (facts.sch.proposal_time_lt_vote_time S.E (s + 1)).le
    exact Restated.voterAnchorAt_compatible_of_previousSGHistory_namedOn facts
      S Hs Xb hf hHs hHsXb hfb hhor hc hsg hsgPost (hHs _ _ hdom hw) c hcc
      (by rewrite [facts.nd.mkNode_st]; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView]; exact hroots w hw)
      hAprev A hAnchor

local macro "p65% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Claims.Restated.Claim13beRoute3_65)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

local macro "rnh% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Vocabulary.Protocol.Duties.Inputs.RecoveryInitialSourceNamedRunHistory)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.HealingSurface ++ n.getId)))

/-- If `m` can return `a`, then `f <$> m` can return `f a`. -/
private theorem returns_map_intro₇₀w {α β : Type} (f : α → β) (m : DC.NDRE α) (a : α)
    (h : m ⇢ a) : (f <$> m) ⇢ f a := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image]
  exact ⟨_, h, rfl⟩

/-- The grade-2 candidate read at `n` for round `r` has an outcome. -/
private theorem nodeQ2_nonempty₇₀w (facts : Record.Facts M) (S : Setup V) (n : M.N) (r : Round) :
    ∃ o : Option (Block V), Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M S n r ⇢ o := by
  obtain ⟨G, hG⟩ := facts.gr.read_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.toHealing n.st.core) r
  refine ⟨G.Q2, ?_⟩
  unfold Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 Restated.Vocabulary.Internal.PhaseGrades.nodeRead
  exact returns_map_intro₇₀w (fun g : DecoupledConsensusModel.Protocol.GradeRead V => g.Q2) _ G hG

/-- Under the hypotheses of
    `PrefixFGSelectorConeAtOn.oldTargetRoot_preceq_of_strictActionCut_of_frame_run`, if `0 < s`,
    `lo ≤ vote_time s`, slot `s`'s confirmation instant is in the horizon, the vote instant of
    `s + 1` is between `S.a a.round` and `S.a (a.round + 1)` and before the next round's opening,
    slot `s + 1` is in round `a.round`, the source action's votes are settled by then, and the
    slot-`s` votes of the set form a cone over `T`, then every member of the set for the vote
    instant of `s + 1` has every outcome of its in-tree head there descending from `T`, and the
    slot-`(s + 1)` votes of the set form a cone over `T`. -/
theorem PrefixFGSelectorConeAtOn.checkpointVoteStep_beforeNextAction_of_frame_run
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
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hseed : Restated.PrefixFGSelectorConeAtOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs Xb start first blocked i a ta Cfg T.erase)
    (hfirst : Restated.HeightWindowAtOn M S rho W X (blocked + 1) first)
    (hframe : Restated.NamedHeightRegimeFrameOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs X Xb blocked (first - 1) Tprev c0)
    (hc0 : c0 ≤ a.round)
    (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho a.round)
    (hpostPrev : S.E.t_GST ≤ Restated.Vocabulary.Execution.Setup.a M S (a.round - 1))
    (hpred : Restated.NamedOldTargetRootBelowRunOn M S rho W
      (fun t => W (strictEventIndex rho t)) Hs X Xb first blocked T)
    (hminimal : ∀ (b : NamedAttestation V) (tb : Time),
      b.val_index ∈ Hs tb →
      Restated.Vocabulary.Execution.NamedRun.emits M S rho W b.val_index (Object.attest b) tb →
      b.height_pair.erase.height? = some (blocked + 1) →
      a.round ≤ b.round)
    {s : Slot} (hs : 0 < s)
    (hpost : lo ≤ M.vote_time S.E s)
    (hhor : M.confirmation_time S.E s ≤ rho.horizon)
    (hread : Restated.Vocabulary.Execution.Setup.a M S a.round ≤ M.vote_time S.E (s + 1))
    (hnext : M.vote_time S.E (s + 1) ≤ Restated.Vocabulary.Execution.Setup.a M S (a.round + 1))
    (hnextOpening : M.vote_time S.E (s + 1) ≤ M.opening S.E S.hc (a.round + 1))
    (hsround : M.round_of S.hc (s + 1) = a.round)
    (hactionSettled : Restated.Vocabulary.Execution.Setup.a M S a.round + S.E.Δ ≤
      M.vote_time S.E (s + 1))
    (hvotes : Restated.NamedHonestVotesConeOn M S rho W Hs Xb s
      (fun Y => Block.Preceq T.erase Y))
    (hlo : lo ≤ M.opening S.E S.hc (a.round - S.hc.η_SG))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S k + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
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
        Block.Preceq T.erase H) ∧
      Restated.NamedHonestVotesConeOn M S rho W Hs Xb (s + 1)
        (fun Y => Block.Preceq T.erase Y) := by
  have hmajority : HonestWeightMajorityOn S rho Hs :=
    honestWeightMajorityOn_of_belowOneThirdOn hfb
  have hvoteHor : M.vote_time S.E (s + 1) ≤ rho.horizon :=
    le_trans (le_of_lt (lt_of_lt_of_le (Int.lt_add_of_pos_right _ S.E.Δ_pos)
      (facts.sch.vote_time_succ_add_delta_le_confirmation_time S.E s))) hhor
  have hloVote : lo ≤ M.vote_time S.E (s + 1) :=
    hpost.trans (facts.sch.vote_time_mono_slots S.E (Nat.le_succ s))
  obtain ⟨n₀, hn₀⟩ := actionReadFrom_nonempty₇₀w facts S
    (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round)) a.val_index)
    a.round
  obtain ⟨P, _, hPentry, hPheight0, _, hPrun⟩ :=
    Restated.action_named_checkpointOn facts S Hs Xb hf (hHsXb _ hseed.signerHonest) hn₀
      (hseed.sourceMem n₀ hn₀)
  have hPT : P.erase = T.erase := hPentry.trans hseed.checkpointDerived.symm
  have hPheight : (M.derive_named S.E S.cfg P).h = blocked + 1 :=
    hPheight0.trans hseed.sourceDerivedHeight
  have hrootW : ∀ w ∈ Hs (M.vote_time S.E (s + 1)), Block.Preceq
      (M.get_fg_root
        (M.toHealing (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st.core).toFG)
      T.erase := fun w hw =>
    hseed.fgRoot_preceq_before_nextAction_of_frame_run facts
      hf hHs hHsXb hX hXXb hcom hfb hfirst hframe hc0 ready hpostPrev hpred
        hminimal hread hnext hw hvoteHor hlo hA
  have hparts := fun (w : V) (c : M.Cache) => (p65% dutyNode_parts₆₅) facts S
    (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w) (s + 1) c
  have hrunV := awake_g1_committee₇₀w facts hf (s := s + 1)
    (Restated.lo_le_early_g2_sub_delta_of_opening facts S
      (Restated.PrefixFGSelectorConeAtOn.round_pos_l70 facts hf hseed) hlo (le_of_eq hsround.symm))
  refine Restated.goldfishCone_succ_of_runFrontierWitnessesOn facts
    S Hs Xb hf hHs hHsXb hcom hmajority hs hpost hhor hvotes ?_ ?_ ?_ hrunV
  · intro w _hw C hCerase hhigh hCrun b tb K _hb _hemit _ht _hrow nr _hnr _hW _hKrun
    have hCP : C = P := by
      apply hf.rootCollisionFree.root_injective
        C P hCrun hPrun C P
          (Or.inl (Proofs.NamedAncestry.named_self C))
          (Or.inr (Proofs.NamedAncestry.named_self P))
      rw [← Proofs.NamedWire.erase_root C, hCerase, ← hPT,
        Proofs.NamedWire.erase_root]
    subst hCP
    have hupper := hseed.readFrontier_le_before_nextAction_run facts
      hf hHs hHsXb hX hmajority hfirst hnext w hvoteHor hloVote
    have hband :
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st
          (M.vote_time S.E (s + 1))).core.h_max - 1 ≤ blocked + 1 := by
      rw [facts.hd.setClock_core_h_max]
      exact Nat.sub_le_iff_le_add.mpr hupper
    rw [hPheight] at hhigh
    exact False.elim ((Nat.not_lt_of_ge hband) hhigh)
  · intro w hw
    have h := (hparts w (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).cache).2.2.2.2.2
    rewrite [facts.nd.mkNode_st] at h; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at h
    rw [h]
    exact compatible_of_cases (Or.inl (hrootW w hw))
  · intro w hw c hcc A hAnchor
    have hnmem : M.mkNode (M.ns_setClock S.E
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).st (M.vote_time S.E (s + 1)))
        (W (strictEventIndex rho (M.vote_time S.E (s + 1))) w).record c ∈
        Restated.Vocabulary.Internal.NamedRecoveryRead.voteDutyRead M S rho w (s + 1) :=
      ⟨W (strictEventIndex rho (M.vote_time S.E (s + 1))),
        (p65% mem_stateBeforeTime_along₆₅) hf.sorted hf.onePath _, c, hcc, rfl⟩
    rcases Restated.Vocabulary.Proofs.HealingSurface.voterAnchorAt_cases facts S rho w (s + 1) _
        hnmem A hAnchor with hroot | ⟨root, L, hframeL, hactiveL, hanchorL⟩
    · rw [hroot, (hparts w c).2.2.2.2.2]
      exact compatible_of_cases (Or.inl (hrootW w hw))
    · rw [hanchorL]
      have hr : 0 < a.round := hseed.round_pos_l70 facts hf
      have hslo : M.opening_slot S.hc a.round ≤ s + 1 := by
        rw [← hsround]
        exact facts.gr.opening_slot_round_of_le_slot S.hc (s + 1)
      rw [(hparts w c).2.2.1, hsround] at hframeL
      have hsigner : a.val_index ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S a.round) := by
        have h := hseed.signerHonest
        rw [hseed.actionTime_eq] at h
        exact h
      have hsignerG0 : a.val_index ∈ Hs (M.domain S.E S.hc a.round .g0) :=
        hHs _ _ (facts.gr.domain_le_a S a.round .g0) hsigner
      obtain ⟨o, ho⟩ := nodeQ2_nonempty₇₀w facts S n₀ a.round
      obtain ⟨Q, rfl⟩ := hseed.exists_nodeQ2_l70 facts n₀ hn₀ o ho
      obtain ⟨src, hsrc⟩ := (p63% actionFGSource_nonempty₆₃w) facts S n₀
      have hsrcEq := hseed.exactFGSource n₀ hn₀ src hsrc
      subst hsrcEq
      have hsourceCompat :=
        Restated.activeVoterAnchor_compatible_actionFGSource_at_interior_namedOn facts
          S Hs Xb hf hHs hHsXb hr ready (hseed.actionHorizon facts hf)
            hsignerG0 hw hslo hsround hnextOpening hvoteHor
            ((add_le_add (facts.gr.domain_le_a S a.round .g0)
              (le_refl S.E.Δ)).trans hactionSettled)
            hactionSettled hn₀ ho hsrc c hcc hframeL hactiveL hlo
      have hTCfg : Block.Preceq T.erase Cfg.erase := by
        rw [hseed.checkpointDerived]
        exact facts.csAdded.derive_named_T_h_preceq S.E S.cfg Cfg
      exact (rnh% runHistory_compatible_checkpoint_below) hsourceCompat hTCfg


/-- Under the hypotheses of
    `PrefixFGSelectorConeAtOn.oldTargetRoot_preceq_of_strictActionCut_of_frame_run`, for every slot
    `d` after the opening slot of round `a.round` and before the opening slot of round
    `a.round + 1`, with the vote instant of `d` plus `Δ` in the horizon, every member of the set for
    the vote instant of `d` has every outcome of its in-tree head at `d` descending from `T`, and
    the slot-`d` votes of the set form a cone over `T`. -/
theorem PrefixFGSelectorConeAtOn.checkpointProtection_sourceRound_of_frame_run
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
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hseed : Restated.PrefixFGSelectorConeAtOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs Xb start first blocked i a ta Cfg T.erase)
    (hfirst : Restated.HeightWindowAtOn M S rho W X (blocked + 1) first)
    (hframe : Restated.NamedHeightRegimeFrameOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs X Xb blocked (first - 1) Tprev c0)
    (hc0 : c0 ≤ a.round)
    (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho a.round)
    (hpostPrev : S.E.t_GST ≤ Restated.Vocabulary.Execution.Setup.a M S (a.round - 1))
    (hpred : Restated.NamedOldTargetRootBelowRunOn M S rho W
      (fun t => W (strictEventIndex rho t)) Hs X Xb first blocked T)
    (hminimal : ∀ (b : NamedAttestation V) (tb : Time),
      b.val_index ∈ Hs tb →
      Restated.Vocabulary.Execution.NamedRun.emits M S rho W b.val_index (Object.attest b) tb →
      b.height_pair.erase.height? = some (blocked + 1) →
      a.round ≤ b.round)
    {d : Slot} (hdlo : M.opening_slot S.hc a.round + 1 ≤ d)
    (hdhi : d < M.opening_slot S.hc (a.round + 1))
    (hhor : M.vote_time S.E d + S.E.Δ ≤ rho.horizon)
    (hlo : lo ≤ M.opening S.E S.hc (a.round - S.hc.η_SG))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S k + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
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
        Block.Preceq T.erase H) ∧
      Restated.NamedHonestVotesConeOn M S rho W Hs Xb d
        (fun Y => Block.Preceq T.erase Y) := by
  have hΔ := S.E.Δ_pos
  have hbase := PrefixFGSelectorConeAtOn.checkpointProtection_firstInterior_of_frame_named facts hf hHs hHsXb hX hXXb hseed hfirst hframe hc0 ready hpostPrev
    hlo
  obtain ⟨-, hopenPost, -, -⟩ := Restated.loBounds_l70 facts S (hseed.round_pos_l70 facts hf) hlo
  have hnHor : ∀ n, n + 1 ≤ d → M.confirmation_time S.E n ≤ rho.horizon := by
    intro n hntop
    have htime := facts.sch.vote_time_mono_slots S.E hntop
    obtain ⟨-, -, -, -, h5, h6⟩ := facts.sch.slot_instants_l55 S.E n
    linarith
  have hnext : ∀ n, n + 1 ≤ d →
      M.vote_time S.E (n + 1) ≤ Restated.Vocabulary.Execution.Setup.a M S (a.round + 1) := by
    intro n hntop
    have hle : n + 1 ≤ M.opening_slot S.hc (a.round + 1) := hntop.trans hdhi.le
    exact (facts.sch.vote_time_mono_slots S.E hle).trans
      (Restated.Vocabulary.Protocol.opening_vote_time_lt_action facts S (a.round + 1)).le
  have hnextOpening : ∀ n, n + 1 ≤ d →
      M.vote_time S.E (n + 1) ≤ M.opening S.E S.hc (a.round + 1) := by
    intro n hntop
    have hslot : n + 2 ≤ M.opening_slot S.hc (a.round + 1) :=
      Nat.succ_le_iff.mpr (hntop.trans_lt hdhi)
    have hvoteNext : M.vote_time S.E (n + 1) < M.proposal_time S.E (n + 2) :=
      lt_trans (Restated.vote_time_lt_support_cutoff_l49 facts S (n + 1))
        (facts.sch.support_cutoff_lt_proposal_time_succ S.E (n + 1))
    rw [facts.gr.opening_eq_proposal_time]
    exact hvoteNext.le.trans (facts.sch.proposal_time_mono S.E hslot)
  have hsround : ∀ n, M.opening_slot S.hc a.round + 1 ≤ n → n + 1 ≤ d →
      M.round_of S.hc (n + 1) = a.round := fun n hn hntop =>
    facts.gr.round_of_eq_of_opening_succ_le_of_lt_next_opening S.hc
      (hn.trans (Nat.le_succ n)) (hntop.trans_lt hdhi)
  have hsettled : ∀ n, M.opening_slot S.hc a.round + 1 ≤ n →
      Restated.Vocabulary.Execution.Setup.a M S a.round + S.E.Δ ≤ M.vote_time S.E (n + 1) := by
    intro n hn
    apply Restated.Vocabulary.Proofs.HealingSurface.action_add_delta_le_vote_of_lt facts S
    exact (Restated.Vocabulary.Protocol.action_lt_vote_time_two_after facts S a.round).trans_le
      (facts.sch.vote_time_mono_slots S.E (Nat.succ_le_succ hn))
  have hstep := fun (n : Slot) (hn : M.opening_slot S.hc a.round + 1 ≤ n) (hntop : n + 1 ≤ d)
      (hprev : Restated.NamedHonestVotesConeOn M S rho W Hs Xb n
        (fun Y => Block.Preceq T.erase Y)) =>
    hseed.checkpointVoteStep_beforeNextAction_of_frame_run facts
      hf hHs hHsXb hX hXXb hcom hfb hfirst hframe hc0 ready hpostPrev hpred
        hminimal ((Nat.succ_pos _).trans_le hn)
        (hopenPost.trans (facts.sch.vote_time_mono_slots S.E ((Nat.le_succ _).trans hn)))
        (hnHor n hntop)
        ((le_add_of_nonneg_right S.E.Δ_pos.le).trans (hsettled n hn))
        (hnext n hntop) (hnextOpening n hntop) (hsround n hn hntop) (hsettled n hn) hprev hlo hA
  have hcone : ∀ n, M.opening_slot S.hc a.round + 1 ≤ n → n ≤ d →
      Restated.NamedHonestVotesConeOn M S rho W Hs Xb n (fun Y => Block.Preceq T.erase Y) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => intro _; exact hbase.2
    | succ n hn ih =>
        intro hntop
        exact (hstep n hn hntop (ih (Nat.le_of_succ_le hntop))).2
  rcases Nat.eq_or_lt_of_le hdlo with heq | hlt
  · subst heq
    exact hbase
  · obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 :=
      ⟨d - 1, (Nat.sub_add_cancel (Nat.one_le_of_lt hlt)).symm⟩
    have hn : M.opening_slot S.hc a.round + 1 ≤ n := Nat.lt_succ_iff.mp hlt
    exact hstep n hn le_rfl (hcone n hn (Nat.le_succ n))

/-- Under the hypotheses of
    `PrefixFGSelectorConeAtOn.oldTargetRoot_preceq_of_strictActionCut_of_frame_run`, if the SG
    emissions of round `a.round` are compatible with `T` and the vote instant of the opening slot of
    round `a.round + 1` plus `Δ` is in the horizon, then the relative carrier window holds at round
    `a.round` for the grade-1 phase, along `W`. -/
theorem PrefixFGSelectorConeAtOn.relativeCarrierWindow_source_beforeNextAction_run
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
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hseed : Restated.PrefixFGSelectorConeAtOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs Xb start first blocked i a ta Cfg T.erase)
    (hfirst : Restated.HeightWindowAtOn M S rho W X (blocked + 1) first)
    (hframe : Restated.NamedHeightRegimeFrameOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs X Xb blocked (first - 1) Tprev c0)
    (hc0 : c0 ≤ a.round)
    (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho a.round)
    (hpostPrev : S.E.t_GST ≤ Restated.Vocabulary.Execution.Setup.a M S (a.round - 1))
    (hpred : Restated.NamedOldTargetRootBelowRunOn M S rho W
      (fun t => W (strictEventIndex rho t)) Hs X Xb first blocked T)
    (hminimal : ∀ (b : NamedAttestation V) (tb : Time),
      b.val_index ∈ Hs tb →
      Restated.Vocabulary.Execution.NamedRun.emits M S rho W b.val_index (Object.attest b) tb →
      b.height_pair.erase.height? = some (blocked + 1) →
      a.round ≤ b.round)
    (hsg : Restated.HonestSGEmissionsCompatibleAtRoundOn M S rho W
      (fun t => W (strictEventIndex rho t)) Hs a.round T.erase)
    (hhor : M.vote_time S.E (M.opening_slot S.hc (a.round + 1)) + S.E.Δ ≤ rho.horizon)
    (hlo : lo ≤ M.opening S.E S.hc (a.round - S.hc.η_SG))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S k + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    Restated.RelativeCarrierWindowAtOn M S rho W (fun t => W (strictEventIndex rho t)) Hs
      a.round .g1 := by
  have hΔ := S.E.Δ_pos
  obtain ⟨-, -, -, hloR⟩ := Restated.loBounds_l70 facts S (hseed.round_pos_l70 facts hf) hlo
  have hvoteHor : M.vote_time S.E (M.opening_slot S.hc (a.round + 1)) ≤ rho.horizon :=
    (le_add_of_nonneg_right S.E.Δ_pos.le).trans hhor
  have hdomainEq : M.domain S.E S.hc (a.round + 1) .g1 =
      M.proposal_time S.E (M.opening_slot S.hc (a.round + 1)) :=
    (facts.gr.Sts_domain_g1_eq_opening S _).trans (facts.gr.opening_eq_proposal_time _ _ _)
  have hdomainHor : M.domain S.E S.hc (a.round + 1) .g1 ≤ rho.horizon := by
    rw [hdomainEq]
    exact (facts.sch.proposal_time_lt_vote_time S.E _).le.trans hvoteHor
  have hdeltaEarly : Restated.Vocabulary.Execution.Setup.a M S a.round + S.E.Δ ≤
      M.early S.E S.hc (a.round + 1) .g2 :=
    facts.gr.action_delta_le_early S S.hc.R_ge_three (Nat.lt_succ_self a.round)
  have hearlyP : M.early S.E S.hc (a.round + 1) .g2 ≤ M.early S.E S.hc (a.round + 1) .g1 :=
    facts.gr.early_g2_le_early_g1 S.E S.hc (a.round + 1)
  have horder : M.early S.E S.hc (a.round + 1) .g1 ≤ M.domain S.E S.hc (a.round + 1) .g1 := by
    have h := facts.gr.early_add_two_delta_le_domain S (a.round + 1) .g1
    linarith
  have hreadLo : Restated.Vocabulary.Execution.Setup.a M S a.round ≤
      M.domain S.E S.hc (a.round + 1) .g1 := by
    linarith
  have hhorR : Restated.Vocabulary.Execution.Setup.a M S a.round ≤ rho.horizon :=
    hreadLo.trans hdomainHor
  have hcut : M.early S.E S.hc (a.round + 1) .g1 ≤ rho.horizon := horder.trans hdomainHor
  have hk : a.round ∈ M.latest_window S.hc.η_SG (a.round + 1) := by
    apply facts.fc.mem_latest_window
    · simpa only [Nat.add_sub_cancel] using
        Nat.sub_le_sub_left S.hc.η_SG_ge_one (a.round + 1)
    · exact Nat.lt_succ_self a.round
  rw [Restated.RelativeCarrierWindowAtOn]
  intro w hw u hu huEarly na hna g2 hg2 A hAsel I hI
  have hna' : na ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round)) u) a.round := hna
  obtain ⟨huHon, b, hbval, hbround, hbemit⟩ :=
    (Restated.honestRoundVoters_iffOn facts S rho W hf.onePath Hs u a.round).mp hu
  have huXb : u ∈ Xb := hHsXb _ huHon
  have hawake : ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u
      (Restated.Vocabulary.Execution.Setup.a M S a.round)) →
      M.awake_for_grade2 S u (W j u) a.round := by
    intro j hj
    obtain ⟨i, hi, h⟩ := Restated.Vocabulary.Proofs.Optimistic.emits_attest_awake facts S W hf.onePath hbemit
    rw [hbround] at h
    rw [← Restated.tick_index_eq_of_unique hf.tickIndexUnique hi hj]
    exact h
  obtain ⟨D, hD⟩ := facts.dt.attest_with_nonempty (M.gradeContract na.cache) S.E S.hc (S.node u)
    na.st na.record
  have hmemT := (Restated.stateBeforeTime_eq_stateBefore_strictEventIndexOn facts S Hs Xb hf
    (Restated.Vocabulary.Execution.Setup.a M S a.round)).symm ▸
      (hf.onePath (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round))).1
  have hshape : D.2.2.val_index = u ∧ D.2.2.round = a.round ∧ D.2.2.confirmed = some A.root :=
    Restated.Vocabulary.Proofs.HealingSurface.actionAttestationAt_shape facts S rho u a.round na
      ⟨_, hmemT, hna'⟩ D hD g2 hg2 A hAsel
  have hemit : Restated.Vocabulary.Execution.NamedRun.emits M S rho W u (Object.attest D.2.2)
      (Restated.Vocabulary.Execution.Setup.a M S a.round) :=
    Restated.honest_emits_exact_actionAttestationAt_of_awakeOn facts S Hs Xb hf a.round huHon
      hawake hhorR hloR (fun j hj => hf.tick_outcome j _ _ hj) na hna' D hD
  obtain ⟨j, hj, -, -, -, -, hhead⟩ :=
    Restated.Vocabulary.Proofs.NamedOutageInputs.emitted_attestation_head facts S rho W hf.onePath
      hemit
  have hnaJ : na ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (W j u)
      D.2.2.round := by
    rw [hshape.2.1]
    rcases Restated.action_read_indexOn facts S rho Hs Xb hf j u a.round hj with hstate | hstate
    · rw [hstate]
      exact hna'
    · rw [hstate, actionReadFrom_wake₇₀ facts]
      exact hna'
  obtain ⟨Hb, hHb, hconfirmed⟩ := hhead na hnaJ
  have hbodies := (p64% actionReadFrom_bodies₆₄) facts S _ a.round na hna'
  have hAmem : A ∈
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round)) u).st.core.T :=
    Restated.Vocabulary.Proofs.HealingSurface.actionSGBlockAt_mem_storeBeforeTime facts S rho u
      a.round _ hmemT na hna' g2 hg2 A hAsel
  obtain ⟨Dn, hDnBody, hDnErase⟩ :=
    Restated.Vocabulary.Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore facts S rho
      (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round)) u _
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
  have hcarrierT : Block.compatible Hb.erase T.erase = true := by
    rw [hHbErase]
    exact hsg u huHon na hna D hD hemit g2 hg2 A hAsel
  have hrootT := hseed.fgRoot_preceq_before_nextAction_of_frame_run facts
    hf hHs hHsXb hX hXXb hcom hfb hfirst hframe hc0 ready hpostPrev hpred hminimal
      hreadLo (facts.gr.domain_le_a S (a.round + 1) .g1) hw hdomainHor hlo hA
  have hFT : Block.Preceq
      (W (strictEventIndex rho (M.domain S.E S.hc (a.round + 1) .g1)) w).st.core.F T.erase :=
    preceq_trans_Preceq (Restated.finalizedRoot_preceq_fgRootOn facts S Hs Xb hf) hrootT
  have hpostA : lo ≤ Restated.Vocabulary.Execution.Setup.a M S D.2.2.round := by
    rw [hshape.2.1]
    exact hloR
  have hdeadline : max (Restated.Vocabulary.Execution.Setup.a M S D.2.2.round) lo + S.E.Δ ≤
      M.early S.E S.hc (a.round + 1) .g1 := by
    rw [hshape.2.1, max_eq_left hloR]
    exact hdeltaEarly.trans hearlyP
  have hwEarly : w ∈ Hs (M.early S.E S.hc (a.round + 1) .g1) := hHs _ _ horder hw
  have hexact : ∀ {C : Block V}, Block.Preceq Hb.erase C →
      Block.Preceq
        (W (strictEventIndex rho (M.domain S.E S.hc (a.round + 1) .g1)) w).st.core.F C →
      ∃ y ∈ I, y.round = a.round ∧ y.confirmed = some A.root ∧
        Block.find?
          (W (strictEventIndex rho (M.domain S.E S.hc (a.round + 1) .g1)) w).st.core.T A.root =
          some A := by
    intro C hHC hFC
    have h := Restated.interpretedInputs_exact_of_honest_window_vote_after_gst_common_upperOn facts
      S Hs Xb hf hHs hHsXb (t := M.domain S.E S.hc (a.round + 1) .g1) .g1 hk huEarly hwEarly
      ⟨hshape.1, hshape.2.1, hemit⟩ ⟨j, hj, ⟨na, hnaJ, hHb⟩, hconfirmed⟩ hHC hFC hpostA
      hdeadline horder hcut I hI
    rw [hHbErase, hHbRoot] at h
    exact h
  rcases (show Block.Preceq Hb.erase T.erase ∨ Block.Preceq T.erase Hb.erase from
    compatible_cases hcarrierT) with hHbT | hTHb
  · exact hexact hHbT hFT
  · exact hexact (Proofs.ModelProperties.Preceq_self Hb.erase) (preceq_trans_Preceq hFT hTHb)


/-- Under the hypotheses of
    `PrefixFGSelectorConeAtOn.oldTargetRoot_preceq_of_strictActionCut_of_frame_run`, if the vote
    instant of the opening slot of round `a.round + 1` plus `Δ` is in the horizon, every member of
    the set for that vote instant has every outcome of its in-tree head at that slot descending from
    `T`, and the votes of that slot of the set form a cone over `T`. -/
theorem PrefixFGSelectorConeAtOn.checkpointProtection_nextOpening_of_frame_run
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
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hseed : Restated.PrefixFGSelectorConeAtOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs Xb start first blocked i a ta Cfg T.erase)
    (hfirst : Restated.HeightWindowAtOn M S rho W X (blocked + 1) first)
    (hframe : Restated.NamedHeightRegimeFrameOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs X Xb blocked (first - 1) Tprev c0)
    (hc0 : c0 ≤ a.round)
    (ready : Restated.Vocabulary.Internal.HealingSurface.GradeRoundReady M S rho a.round)
    (hpostPrev : S.E.t_GST ≤ Restated.Vocabulary.Execution.Setup.a M S (a.round - 1))
    (hpred : Restated.NamedOldTargetRootBelowRunOn M S rho W
      (fun t => W (strictEventIndex rho t)) Hs X Xb first blocked T)
    (hminimal : ∀ (b : NamedAttestation V) (tb : Time),
      b.val_index ∈ Hs tb →
      Restated.Vocabulary.Execution.NamedRun.emits M S rho W b.val_index (Object.attest b) tb →
      b.height_pair.erase.height? = some (blocked + 1) →
      a.round ≤ b.round)
    (hhor : M.vote_time S.E (M.opening_slot S.hc (a.round + 1)) + S.E.Δ ≤ rho.horizon)
    (hlo : lo ≤ M.opening S.E S.hc (a.round - S.hc.η_SG))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S k + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    (∀ w ∈ Hs (M.vote_time S.E (M.opening_slot S.hc (a.round + 1))), ∀ c : M.Cache,
      M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc (a.round + 1)))) w).st.core.toHealing
        (M.vote_time S.E (M.opening_slot S.hc (a.round + 1)))
        (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc (a.round + 1)))) w).cache ⇢ c →
      let n := M.mkNode
        (M.ns_setClock S.E
          (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc (a.round + 1)))) w).st
          (M.vote_time S.E (M.opening_slot S.hc (a.round + 1))))
        (W (strictEventIndex rho (M.vote_time S.E (M.opening_slot S.hc (a.round + 1)))) w).record c
      ∀ Tr : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ Tr →
      ∀ L : Finset (GoldfishVote V),
        M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
      ∀ L' : Finset (GoldfishVote V),
        M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
      ∀ H : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
          (M.toHealing n.st.core) Tr L L' (n.st.core.s - 1) ⇢ H →
        Block.Preceq T.erase H) ∧
      Restated.NamedHonestVotesConeOn M S rho W Hs Xb (M.opening_slot S.hc (a.round + 1))
        (fun Y => Block.Preceq T.erase Y) := by
  have hΔ := S.E.Δ_pos
  obtain ⟨-, hpostOpen, -, hpostA⟩ :=
    Restated.loBounds_l70 facts S (hseed.round_pos_l70 facts hf) hlo
  have hsg := PrefixFGSelectorConeAtOn.sgEmissionsCompatible_of_source_of_frame_named facts hf hHs hHsXb hX hXXb hcom hseed hfirst hframe hc0 ready
    hpostPrev hlo
  have hwindow := hseed.relativeCarrierWindow_source_beforeNextAction_run facts
    hf hHs hHsXb hX hXXb hcom hfb hfirst hframe hc0 ready hpostPrev hpred hminimal
      hsg hhor hlo hA
  have hdomainEq : M.domain S.E S.hc (a.round + 1) .g1 =
      M.proposal_time S.E (M.opening_slot S.hc (a.round + 1)) :=
    (facts.gr.Sts_domain_g1_eq_opening S _).trans (facts.gr.opening_eq_proposal_time _ _ _)
  have hroundOpen : M.round_of S.hc (M.opening_slot S.hc (a.round + 1)) = a.round + 1 :=
    facts.gr.round_of_opening_slot_eq_schedule S.hc _
  have hbb := (rnh% runHistory_sourceLastSlot_bounds) (M.opening_slot S.hc a.round) S.hc.R
    S.hc.R_ge_two
  rw [← facts.gr.opening_slot_succ_eq S.hc a.round] at hbb
  generalize hlast : M.opening_slot S.hc (a.round + 1) - 1 = last at hbb
  obtain ⟨hb1, hb2, hb3, hb4⟩ := hbb
  rw [← hb4] at hhor hdomainEq hroundOpen ⊢
  have hlastHor : M.vote_time S.E last + S.E.Δ ≤ rho.horizon :=
    (add_le_add (facts.sch.vote_time_mono_slots S.E (Nat.le_succ last)) (le_refl S.E.Δ)).trans hhor
  have hcone := hseed.checkpointProtection_sourceRound_of_frame_run facts
    hf hHs hHsXb hX hXXb hcom hfb hfirst hframe hc0 ready hpostPrev hpred hminimal
      hb1 hb2 hlastHor hlo hA
  have hvoteHor : M.vote_time S.E (last + 1) ≤ rho.horizon :=
    (le_add_of_nonneg_right S.E.Δ_pos.le).trans hhor
  have hdomVote : M.domain S.E S.hc (a.round + 1) .g1 ≤ M.vote_time S.E (last + 1) := by
    rw [hdomainEq]
    exact (facts.sch.proposal_time_lt_vote_time S.E _).le
  have hdomainG1Hor : M.domain S.E S.hc (a.round + 1) .g1 ≤ rho.horizon :=
    hdomVote.trans hvoteHor
  have hsourceDelay : Restated.Vocabulary.Execution.Setup.a M S (a.round + 1 - 1) + S.E.Δ ≤
      M.domain S.E S.hc (a.round + 1) .g1 := by
    rw [Nat.add_sub_cancel]
    have h1 := facts.gr.action_delta_le_early S S.hc.R_ge_three (Nat.lt_succ_self a.round)
    have h2 := facts.gr.early_g2_le_early_g1 S.E S.hc (a.round + 1)
    have h3 := facts.gr.early_add_two_delta_le_domain S (a.round + 1) .g1
    linarith
  have hmajority : Restated.GradeFormingMajorityOn M S rho W Hs
      (Hs (M.domain S.E S.hc (a.round + 1) .g1)) (a.round + 1) :=
    Restated.gradeFormingMajority_of_admissible_belowOneThirdOn facts S Hs Xb hf hHs hfb
      (Nat.succ_pos a.round) hsourceDelay hdomainG1Hor
      hpostA (hA a.round (Restated.lo_le_early_g2_sub_delta_of_opening facts S
        (hseed.round_pos_l70 facts hf) hlo le_rfl))
  have hpost : lo ≤ M.vote_time S.E last :=
    hpostOpen.trans (facts.sch.vote_time_mono_slots S.E ((Nat.le_succ _).trans hb1))
  have hconfHor : M.confirmation_time S.E last ≤ rho.horizon := by
    obtain ⟨-, -, -, -, h5, h6⟩ := facts.sch.slot_instants_l55 S.E last
    linarith
  have hread : Restated.Vocabulary.Execution.Setup.a M S a.round ≤ M.vote_time S.E (last + 1) :=
    (Restated.Vocabulary.Proofs.HealingSurface.action_before_vote_of_round_lt facts S (by
      rw [hroundOpen]
      exact Nat.lt_succ_self a.round)).le
  have hnext : M.vote_time S.E (last + 1) ≤
      Restated.Vocabulary.Execution.Setup.a M S (a.round + 1) := by
    have h := (Restated.Vocabulary.Protocol.opening_vote_time_lt_action facts S (a.round + 1)).le
    rw [← hb4] at h
    exact h
  have hloVote : lo ≤ M.vote_time S.E (last + 1) :=
    hpost.trans (facts.sch.vote_time_mono_slots S.E (Nat.le_succ last))
  have hloDom : lo ≤ M.domain S.E S.hc (a.round + 1) .g1 := by
    have h := (le_add_of_nonneg_right S.E.Δ_pos.le).trans hsourceDelay
    rw [Nat.add_sub_cancel] at h
    exact hpostA.trans h
  have hrootW : ∀ w ∈ Hs (M.vote_time S.E (last + 1)), Block.Preceq
      (M.get_fg_root
        (M.toHealing (W (strictEventIndex rho (M.vote_time S.E (last + 1))) w).st.core).toFG)
      T.erase := fun w hw =>
    hseed.fgRoot_preceq_before_nextAction_of_frame_run facts
      hf hHs hHsXb hX hXXb hcom hfb hfirst hframe hc0 ready hpostPrev hpred
        hminimal hread hnext hw hvoteHor hlo hA
  have hrootN : ∀ w ∈ Hs (M.vote_time S.E (last + 1)), Block.Preceq
      (M.get_fg_root
        (M.toHealing (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (last + 1))) w).st
          (M.vote_time S.E (last + 1))).core).toFG) T.erase := by
    intro w hw
    have h := ((p65% dutyNode_parts₆₅) facts S
      (W (strictEventIndex rho (M.vote_time S.E (last + 1))) w) (last + 1)
      (W (strictEventIndex rho (M.vote_time S.E (last + 1))) w).cache).2.2.2.2.2
    rewrite [facts.nd.mkNode_st] at h; try simp only [facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at h
    rw [h]
    exact hrootW w hw
  obtain ⟨n₀, hn₀⟩ := actionReadFrom_nonempty₇₀w facts S
    (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S a.round)) a.val_index)
    a.round
  obtain ⟨P, _, hPentry, hPheight0, _, hPrun⟩ :=
    Restated.action_named_checkpointOn facts S Hs Xb hf (hHsXb _ hseed.signerHonest) hn₀
      (hseed.sourceMem n₀ hn₀)
  have hPT : P.erase = T.erase := hPentry.trans hseed.checkpointDerived.symm
  have hPheight : (M.derive_named S.E S.cfg P).h = blocked + 1 :=
    hPheight0.trans hseed.sourceDerivedHeight
  have hmajority' : HonestWeightMajorityOn S rho Hs :=
    honestWeightMajorityOn_of_belowOneThirdOn hfb
  have hrunV := awake_g1_committee₇₀w facts hf (s := last + 1) (by
    rw [hroundOpen]
    exact Restated.lo_le_early_g2_sub_delta_of_opening facts S
      (hseed.round_pos_l70 facts hf) hlo (Nat.le_succ _))
  refine Restated.goldfishCone_succ_of_runFrontierWitnessesOn facts
    S Hs Xb hf hHs hHsXb hcom hmajority' hb3 hpost hconfHor hcone.2 ?_ ?_ ?_ hrunV
  · intro w _hw C hCerase hhigh hCrun b tb K _hb' _hemit _ht _hrow nr _hnr _hW _hKrun
    have hCP : C = P := by
      apply hf.rootCollisionFree.root_injective
        C P hCrun hPrun C P
          (Or.inl (Proofs.NamedAncestry.named_self C))
          (Or.inr (Proofs.NamedAncestry.named_self P))
      rw [← Proofs.NamedWire.erase_root C, hCerase, ← hPT,
        Proofs.NamedWire.erase_root]
    subst hCP
    have hupper := hseed.readFrontier_le_before_nextAction_run facts
      hf hHs hHsXb hX hmajority' hfirst hnext w hvoteHor hloVote
    have hband :
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E (last + 1))) w).st
          (M.vote_time S.E (last + 1))).core.h_max - 1 ≤ blocked + 1 := by
      rw [facts.hd.setClock_core_h_max]
      exact Nat.sub_le_iff_le_add.mpr hupper
    rw [hPheight] at hhigh
    exact False.elim ((Nat.not_lt_of_ge hband) hhigh)
  · intro w hw
    exact compatible_of_cases (Or.inl (hrootN w hw))
  · intro w hw c hcc
    exact Restated.voterAnchorAt_compatible_of_previousRelativeCarrierOn facts
      S Hs Xb _ hf hHs hroundOpen hvoteHor hwindow hmajority (subset_refl _) hsg
        (hHs _ _ hdomVote hw) c hcc (hrootN w hw) hloDom

local macro "p62% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Claims.Restated.Claim13beRoute3_62)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

/-- Under the bundle along `W`, the committee majority and the weight bound, for a run-scoped named
    regime and every round `c` after its source round: at every slot `s` of round `c` whose vote
    instant plus `Δ` is in the horizon, every voter head of the set descends from `T` and the votes
    of slot `s` form a cone over `T`; and if round `c`'s action instant is in the horizon, the SG
    emissions of round `c` and every FG confirmation witness of round `c` of the set are compatible
    with `T`. -/
theorem NamedHeightRegimeRunOn.laterHistory_main (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} {Hs : Int → Finset V} {X Xb : Finset V} {lo : Int}
    {W : Nat → V → M.N}
    {r0 : Round} {blocked : Height}
    {first i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hX : ∀ t : Int, 0 ≤ t → Hs t ⊆ X) (hXXb : X ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hfb : BelowOneThirdOn S rho Hs)
    (h : Restated.NamedHeightRegimeRunOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs X Xb r0 blocked first i a ta Cfg T Tprev c0)
    {c : Round} (hc : a.round + 1 ≤ c)
    (hlo : lo ≤ M.opening S.E S.hc (a.round - S.hc.η_SG))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S k + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    (∀ s, M.round_of S.hc s = c →
      M.vote_time S.E s + S.E.Δ ≤ rho.horizon →
      (∀ w ∈ Hs (M.vote_time S.E s), ∀ cc : M.Cache,
        M.onPhaseTick S.E S.hc
          (W (strictEventIndex rho (M.vote_time S.E s)) w).st.core.toHealing
          (M.vote_time S.E s)
          (W (strictEventIndex rho (M.vote_time S.E s)) w).cache ⇢ cc →
        let n := M.mkNode
          (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) w).st
            (M.vote_time S.E s))
          (W (strictEventIndex rho (M.vote_time S.E s)) w).record cc
        ∀ Tr : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ Tr →
        ∀ L : Finset (GoldfishVote V),
          M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
        ∀ L' : Finset (GoldfishVote V),
          M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
        ∀ H : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
            (M.toHealing n.st.core) Tr L L' (n.st.core.s - 1) ⇢ H →
          Block.Preceq T.erase H) ∧
      Restated.NamedHonestVotesConeOn M S rho W Hs Xb s
        (fun Y => Block.Preceq T.erase Y)) ∧
    (Restated.Vocabulary.Execution.Setup.a M S c ≤ rho.horizon →
      Restated.HonestSGEmissionsCompatibleAtRoundOn M S rho W
        (fun t => W (strictEventIndex rho t)) Hs c T.erase ∧
      ∀ w ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S c),
      ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
          (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) w) c,
      ∀ B : Block V,
        Restated.Vocabulary.Proofs.HealingSurface.fgConfirmationWitness M S n ⇢ some B →
        Block.compatible B T.erase = true) := by
  have hΔ := S.E.Δ_pos
  have haEq : ∀ r : Round, Restated.Vocabulary.Execution.Setup.a M S r =
      M.confirmation_time S.E (M.opening_slot S.hc r) := fun r =>
    facts.sch.a_eq_confirmation_time S.hc S.E r
  obtain ⟨-, hsourceOpenPost, -, hsourceActionPost⟩ :=
    Restated.loBounds_l70 facts S (h.seed.round_pos_l70 facts hf) hlo
  have hsourceSG := PrefixFGSelectorConeAtOn.sgEmissionsCompatible_of_source_of_frame_named facts hf hHs hHsXb hX hXXb hcom h.seed h.crossing h.frame h.c0le
    h.ready h.postPrev hlo
  have hstrong : ∀ {read : Time},
      (∀ r, a.round + 1 ≤ r → Restated.Vocabulary.Execution.Setup.a M S r < read →
        ∀ w ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S r),
        ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
            (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) w) r,
        ∀ B : Block V,
          Restated.Vocabulary.Proofs.HealingSurface.fgConfirmationWitness M S n ⇢ some B →
            Block.compatible B T.erase = true) →
      ∀ r, a.round + 1 ≤ r → Restated.Vocabulary.Execution.Setup.a M S r < read →
        ∀ w ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S r), ∀ B : Block V,
          (∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
              (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) w) r,
            ∀ o, Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M S n ⇢ o →
              Restated.Vocabulary.Proofs.HealingSurface.fgConfirmationWitness M S n ⇢ some B) →
            Block.compatible B T.erase = true := by
    intro read hone r hr ht w hw B hB
    obtain ⟨n, hn⟩ := actionReadFrom_nonempty₇₀w facts S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) w) r
    obtain ⟨o, ho⟩ := (p63% actionFGSource_nonempty₆₃w) facts S n
    exact hone r hr ht w hw n hn B (hB n hn o ho)
  revert hc
  induction c using Nat.strong_induction_on with
  | h c ih =>
    intro hc
    have hAprevC := hA (c - 1)
      (Restated.lo_le_early_g2_sub_delta_of_opening facts S (h.seed.round_pos_l70 facts hf) hlo
        (Nat.le_sub_of_add_le hc))
    let P : Slot → Prop := fun d =>
      (∀ w ∈ Hs (M.vote_time S.E d), ∀ cc : M.Cache,
        M.onPhaseTick S.E S.hc
          (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core.toHealing
          (M.vote_time S.E d)
          (W (strictEventIndex rho (M.vote_time S.E d)) w).cache ⇢ cc →
        let n := M.mkNode
          (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) w).st
            (M.vote_time S.E d))
          (W (strictEventIndex rho (M.vote_time S.E d)) w).record cc
        ∀ Tr : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ Tr →
        ∀ L : Finset (GoldfishVote V),
          M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
        ∀ L' : Finset (GoldfishVote V),
          M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
        ∀ H : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
            (M.toHealing n.st.core) Tr L L' (n.st.core.s - 1) ⇢ H →
          Block.Preceq T.erase H) ∧
      Restated.NamedHonestVotesConeOn M S rho W Hs Xb d
        (fun Y => Block.Preceq T.erase Y)
    have hcpos : 1 ≤ c := (Nat.succ_le_succ (Nat.zero_le a.round)).trans hc
    have hp : c - 1 + 1 = c := Nat.sub_add_cancel hcpos
    have hpredlt : c - 1 < c := Nat.sub_lt (Nat.zero_lt_of_lt hcpos) Nat.zero_lt_one
    have hsourcePred : a.round ≤ c - 1 := Nat.le_sub_one_of_lt (Nat.lt_of_succ_le hc)
    have hsourceLt : a.round < c := Nat.lt_of_succ_le hc
    have hopenRound := facts.gr.round_of_opening_slot_eq_schedule S.hc c
    have hsourceRead : Restated.Vocabulary.Execution.Setup.a M S a.round ≤
        M.vote_time S.E (M.opening_slot S.hc c) :=
      (Restated.Vocabulary.Proofs.HealingSurface.action_before_vote_of_round_lt facts S (by
        rw [hopenRound]
        exact hsourceLt)).le
    have hopenPost : lo ≤ M.vote_time S.E (M.opening_slot S.hc c) :=
      hsourceOpenPost.trans (facts.sch.vote_time_mono_slots S.E
        (facts.gr.opening_slot_le_of_le S.hc hsourceLt.le))
    have hprevPost : lo ≤ Restated.Vocabulary.Execution.Setup.a M S (c - 1) :=
      hsourceActionPost.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hsourcePred)
    have hprevSG : Restated.Vocabulary.Execution.Setup.a M S (c - 1) ≤ rho.horizon →
        Restated.HonestSGEmissionsCompatibleAtRoundOn M S rho W
          (fun t => W (strictEventIndex rho t)) Hs (c - 1) T.erase := by
      intro hhor
      by_cases heq : c - 1 = a.round
      · rw [heq]
        exact hsourceSG
      · exact ((ih (c - 1) hpredlt
          (Nat.succ_le_of_lt (lt_of_le_of_ne hsourcePred (Ne.symm heq)))).2 hhor).1
    have hpriorFG : ∀ read, read ≤ Restated.Vocabulary.Execution.Setup.a M S c →
        read ≤ rho.horizon →
        ∀ r, a.round + 1 ≤ r → Restated.Vocabulary.Execution.Setup.a M S r < read →
        ∀ w ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S r),
        ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
            (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) w) r,
        ∀ B : Block V,
          Restated.Vocabulary.Proofs.HealingSurface.fgConfirmationWitness M S n ⇢ some B →
            Block.compatible B T.erase = true := by
      intro read hread hhor r hr ht w hw n hn B hB
      have hrc : r < c := by
        by_contra hn'
        exact (not_lt_of_ge
          (Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.le_of_not_gt hn')))
            (ht.trans_le hread)
      exact ((ih r hrc hr).2 (ht.le.trans hhor)).2 w hw n hn B hB
    have hopening : M.vote_time S.E (M.opening_slot S.hc c) + S.E.Δ ≤ rho.horizon →
        P (M.opening_slot S.hc c) := by
      intro hhor
      by_cases heq : c = a.round + 1
      · subst heq
        exact h.seed.checkpointProtection_nextOpening_of_frame_run facts
          hf hHs hHsXb hX hXXb hcom hfb h.crossing h.frame h.c0le h.ready h.postPrev
            h.pred h.minimal hhor hlo hA
      have hprev : a.round + 1 ≤ c - 1 :=
        Nat.le_sub_one_of_lt (lt_of_le_of_ne hc (Ne.symm heq))
      have hbb := (rnh% runHistory_laterLastSlot_bounds) (M.opening_slot S.hc (c - 1)) S.hc.R
        S.hc.R_ge_two
      rw [← facts.gr.opening_slot_succ_eq S.hc (c - 1), hp] at hbb
      generalize M.opening_slot S.hc c - 1 = last at hbb
      obtain ⟨hb1, hb2, hb3, hb4⟩ := hbb
      have hlastRound : M.round_of S.hc last = c - 1 :=
        facts.gr.round_of_eq_of_opening_succ_le_of_lt_next_opening S.hc hb1 (by rw [hp]; exact hb2)
      have hlastHor : M.vote_time S.E last + S.E.Δ ≤ rho.horizon :=
        (add_le_add (facts.sch.vote_time_mono_slots S.E hb2.le) (le_refl S.E.Δ)).trans hhor
      have hcone := ((ih (c - 1) hpredlt hprev).1 last hlastRound hlastHor).2
      have hreadHor : M.vote_time S.E (M.opening_slot S.hc c) ≤ rho.horizon :=
        (le_add_of_nonneg_right S.E.Δ_pos.le).trans hhor
      have hprevRead : Restated.Vocabulary.Execution.Setup.a M S (c - 1) ≤
          M.vote_time S.E (M.opening_slot S.hc c) :=
        (Restated.Vocabulary.Proofs.HealingSurface.action_before_vote_of_round_lt facts S (by
          rw [hopenRound]
          exact hpredlt)).le
      have hsg := hprevSG (hprevRead.trans hreadHor)
      have hlastPost : lo ≤ M.vote_time S.E last :=
        hsourceOpenPost.trans (facts.sch.vote_time_mono_slots S.E
          ((facts.gr.opening_slot_le_of_le S.hc hsourcePred).trans ((Nat.le_succ _).trans hb1)))
      have hhist := hpriorFG _
        (Restated.Vocabulary.Protocol.opening_vote_time_lt_action facts S c).le hreadHor
      rw [← hb4] at hhor hopenRound hsourceRead hhist ⊢
      have hconfHor : M.confirmation_time S.E last ≤ rho.horizon := by
        obtain ⟨-, -, -, -, h5, h6⟩ := facts.sch.slot_instants_l55 S.E last
        linarith
      exact h.seed.checkpointVoteStep_of_actionHistories_of_frame_run facts
        hf hHs hHsXb hX hXXb hcom hfb h.crossing h.frame h.c0le h.ready h.postPrev
          h.pred h.minimal hb3 hlastPost hconfHor hsourceRead
          (by rw [hopenRound]; exact hcpos)
          (by rw [hopenRound]; exact hsg)
          (by rw [hopenRound]; exact hprevPost)
          hhist hcone hlo hA (by rw [hopenRound]; exact hAprevC)
    have haction : Restated.Vocabulary.Execution.Setup.a M S c ≤ rho.horizon →
        Restated.HonestSGEmissionsCompatibleAtRoundOn M S rho W
          (fun t => W (strictEventIndex rho t)) Hs c T.erase ∧
        ∀ w ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S c),
        ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
            (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) w) c,
        ∀ B : Block V,
          Restated.Vocabulary.Proofs.HealingSurface.fgConfirmationWitness M S n ⇢ some B →
          Block.compatible B T.erase = true := by
      intro hhor
      have hvA : M.vote_time S.E (M.opening_slot S.hc c) + S.E.Δ ≤
          Restated.Vocabulary.Execution.Setup.a M S c := by
        obtain ⟨h1, -, -, -, -, h6⟩ := facts.sch.slot_instants_l55 S.E (M.opening_slot S.hc c)
        rw [haEq c]
        linarith
      have hcone := (hopening (hvA.trans hhor)).2
      have hsg := hprevSG
        ((Restated.Vocabulary.Proofs.Assembly.a_mono facts S hpredlt.le).trans hhor)
      have hroots : ∀ w ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S c),
          ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
            (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S c)) w) c,
          Block.compatible (M.get_fg_root (M.toHealing n.st.core).toFG) T.erase = true := by
        intro w hw n hn
        rw [(p62% actionReadFrom_fgRoot₆₂s) facts S _ c n hn]
        exact h.seed.fgRoot_compatible_of_recentWitnessHistory_of_frame_run facts
          hf hHs hHsXb hX hXXb hcom hfb h.crossing h.frame h.c0le h.ready h.postPrev
            h.pred h.minimal (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hsourceLt.le)
              (hstrong (hpriorFG _ (le_refl _) hhor)) hw hhor hlo hA
      have hconfHor : M.confirmation_time S.E (M.opening_slot S.hc c) ≤ rho.horizon := by
        rw [← haEq c]
        exact hhor
      rw [← hp] at hcone hhor hroots hopenPost hconfHor ⊢
      constructor
      · exact Restated.sgEmissionsCompatible_succ_of_previousSGHistory_and_openingVotes_namedOn
          facts S Hs Xb hf hHs hHsXb hcom hfb hsg hcone hprevPost hhor hroots hAprevC
      · intro w hw n hn B hB
        exact Restated.fgConfirmationWitness_compatible_of_previousSGHistory_and_openingVotes_namedOn
          facts S Hs Xb hf hHs hHsXb hcom hfb hsg hcone hprevPost hopenPost hconfHor hw hn
            (hroots w hw n hn) hB hAprevC
    refine ⟨?_, haction⟩
    intro s hround hhor
    have hslo : M.opening_slot S.hc c ≤ s := by
      rw [← hround]
      exact facts.gr.opening_slot_round_of_le_slot S.hc s
    have hshi : s < M.opening_slot S.hc (c + 1) := by
      rw [← hround]
      exact facts.gr.lt_opening_slot_round_of_succ S.hc s
    rcases eq_or_lt_of_le hslo with heq | hinterior
    · subst heq
      exact hopening hhor
    have hactionHor : Restated.Vocabulary.Execution.Setup.a M S c ≤ rho.horizon := by
      obtain ⟨-, -, -, -, h5, h6⟩ := facts.sch.slot_instants_l55 S.E (M.opening_slot S.hc c)
      have hm := facts.sch.vote_time_mono_slots S.E (Nat.succ_le_of_lt hinterior)
      rw [haEq c]
      linarith
    have hcurrent := haction hactionHor
    have hsg := hprevSG
      ((Restated.Vocabulary.Proofs.Assembly.a_mono facts S hpredlt.le).trans hactionHor)
    have hreadHor : M.vote_time S.E s ≤ rho.horizon :=
      (le_add_of_nonneg_right S.E.Δ_pos.le).trans hhor
    have hreadNext : M.vote_time S.E s ≤ Restated.Vocabulary.Execution.Setup.a M S (c + 1) :=
      (facts.sch.vote_time_mono_slots S.E hshi.le).trans
        (Restated.Vocabulary.Protocol.opening_vote_time_lt_action facts S _).le
    have hthroughFG : ∀ read, read ≤ M.vote_time S.E s →
        ∀ r, a.round + 1 ≤ r → Restated.Vocabulary.Execution.Setup.a M S r < read →
        ∀ w ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S r),
        ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
            (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S r)) w) r,
        ∀ B : Block V,
          Restated.Vocabulary.Proofs.HealingSurface.fgConfirmationWitness M S n ⇢ some B →
            Block.compatible B T.erase = true := by
      intro read hread r hr ht w hw n hn B hB
      have hrc : r < c + 1 := by
        by_contra hn'
        exact (not_lt_of_ge
          (Restated.Vocabulary.Proofs.Assembly.a_mono facts S (Nat.le_of_not_gt hn')))
            (ht.trans_le (hread.trans hreadNext))
      rcases eq_or_lt_of_le (Nat.le_of_lt_succ hrc) with heq | hlt
      · subst heq
        exact hcurrent.2 w hw n hn B hB
      · exact ((ih r hlt hr).2 (ht.le.trans (hread.trans hreadHor))).2 w hw n hn B hB
    have hopenPos : 0 < M.opening_slot S.hc c :=
      facts.gr.opening_slot_pos_of_round_pos S.hc (Nat.zero_lt_of_lt hcpos)
    have hroundD : ∀ d, M.opening_slot S.hc c ≤ d → d + 1 ≤ s → M.round_of S.hc (d + 1) = c :=
      fun d hd hds =>
        facts.gr.round_of_eq_of_opening_succ_le_of_lt_next_opening S.hc
          (Nat.succ_le_succ hd) (hds.trans_lt hshi)
    have hconfD : ∀ d, d + 1 ≤ s → M.confirmation_time S.E d ≤ rho.horizon := by
      intro d hds
      have htime := facts.sch.vote_time_mono_slots S.E hds
      obtain ⟨-, -, -, -, h5, h6⟩ := facts.sch.slot_instants_l55 S.E d
      linarith
    have hstep := fun (d : Slot) (hd : M.opening_slot S.hc c ≤ d) (hds : d + 1 ≤ s)
        (hprev : Restated.NamedHonestVotesConeOn M S rho W Hs Xb d
          (fun Y => Block.Preceq T.erase Y)) =>
      h.seed.checkpointVoteStep_of_actionHistories_of_frame_run facts
        hf hHs hHsXb hX hXXb hcom hfb h.crossing h.frame h.c0le h.ready h.postPrev
          h.pred h.minimal (hopenPos.trans_le hd)
          (hopenPost.trans (facts.sch.vote_time_mono_slots S.E hd)) (hconfD d hds)
          (hsourceRead.trans (facts.sch.vote_time_mono_slots S.E (hd.trans (Nat.le_succ d))))
          (by rw [hroundD d hd hds]; exact hcpos)
          (by rw [hroundD d hd hds]; exact hsg)
          (by rw [hroundD d hd hds]; exact hprevPost)
          (hthroughFG _ (facts.sch.vote_time_mono_slots S.E hds)) hprev hlo hA
          (by rw [hroundD d hd hds]; exact hAprevC)
    have hcone : ∀ d, M.opening_slot S.hc c ≤ d → d ≤ s →
        Restated.NamedHonestVotesConeOn M S rho W Hs Xb d (fun Y => Block.Preceq T.erase Y) := by
      intro d hd
      induction d, hd using Nat.le_induction with
      | base =>
          intro _
          exact (hopening ((add_le_add (facts.sch.vote_time_mono_slots S.E hslo)
            (le_refl S.E.Δ)).trans hhor)).2
      | succ d hd ihSlot =>
          intro hds
          exact (hstep d hd hds (ihSlot (Nat.le_of_succ_le hds))).2
    obtain ⟨d, rfl⟩ : ∃ d, s = d + 1 :=
      ⟨s - 1, (Nat.sub_add_cancel (Nat.one_le_of_lt hinterior)).symm⟩
    have hd : M.opening_slot S.hc c ≤ d := Nat.lt_succ_iff.mp hinterior
    exact hstep d hd le_rfl (hcone d hd (Nat.le_succ d))

/-- Under the bundle along `W`, the committee majority and the weight bound, for a run-scoped named
    regime, every row at height `blocked + 1` signed by a member of the set for its emission instant
    has, at every node state of its signer's action read, every outcome of the FG confirmation
    witness equal to `some T`. -/
theorem NamedHeightRegimeRunOn.witness_eq (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} {Hs : Int → Finset V} {X Xb : Finset V} {lo : Int}
    {W : Nat → V → M.N}
    {r0 : Round} {blocked : Height}
    {first i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hX : ∀ t : Int, 0 ≤ t → Hs t ⊆ X) (hXXb : X ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hfb : BelowOneThirdOn S rho Hs)
    (h : Restated.NamedHeightRegimeRunOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs X Xb r0 blocked first i a ta Cfg T Tprev c0)
    {b : NamedAttestation V} {tb : Time}
    (hb : b.val_index ∈ Hs tb)
    (hemit : Restated.Vocabulary.Execution.NamedRun.emits M S rho W b.val_index (Object.attest b) tb)
    (hrow : b.height_pair.erase.height? = some (blocked + 1))
    (hlo : lo ≤ M.opening S.E S.hc (a.round - S.hc.η_SG))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S k + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S
      (W (strictEventIndex rho (Restated.Vocabulary.Execution.Setup.a M S b.round)) b.val_index)
      b.round,
    ∀ o : Option (Block V),
      Restated.Vocabulary.Proofs.HealingSurface.fgConfirmationWitness M S n ⇢ o →
        o = some T.erase := by
  intro n hn o ho
  have htime : tb = Restated.Vocabulary.Execution.Setup.a M S b.round :=
    (Restated.Vocabulary.Proofs.Optimistic.emits_attest_shape facts S W hf.onePath hemit).2
  have hbA : b.val_index ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S b.round) := by
    rw [← htime]; exact hb
  obtain ⟨-, -, hpostPrevLo, -⟩ :=
    Restated.loBounds_l70 facts S (h.seed.round_pos_l70 facts hf) hlo
  rcases eq_or_lt_of_le (h.minimal b tb hb hemit hrow) with heq | hlt
  · exact h.seed.confirmationWitness_of_sameRound_honestHeightRow_of_frame_named facts
      hf hHs hHsXb hX hXXb h.crossing h.frame h.ready hbA hemit hrow heq hlo n hn o ho
  · obtain ⟨src, hsrc, hmap⟩ := (p63% returns_map_elim₆₃) _ _ _ ho
    obtain ⟨D, K, _hW, hDmem, hsource, hDheight, _hKmem, _hKerase, _hKheight, _hKD, _hshape⟩ :=
      Restated.honestHeightRow_confirmationWitnessOn facts S Hs Xb hf (hHsXb _ hb) hemit hrow
        n hn src hsrc
    subst hsource
    have hoD : o = some (M.derive_named S.E S.cfg D).T_h := by
      rw [← hmap]
      simp only [Option.map_some]
      rw [(p63% actionRead_σ_named₆₃w) facts S hf hn hDmem]
    have hhor : Restated.Vocabulary.Execution.Setup.a M S b.round ≤ rho.horizon := by
      obtain ⟨k, hk, _⟩ := hemit
      have hin := (hf.in_horizon (Record.Event.tick b.val_index tb) (List.mem_of_getElem? hk)).2
      simpa only [Record.Event.time, htime, Record.Event.time] using hin
    have hW' : Restated.Vocabulary.Proofs.HealingSurface.fgConfirmationWitness M S n ⇢
        some (M.derive_named S.E S.cfg D).T_h := hoD ▸ ho
    have hcompat := ((h.laterHistory_main facts hf hHs hHsXb hX hXXb
      hcom hfb hlt hlo hA).2 hhor).2 b.val_index hbA n hn _ hW'
    obtain ⟨hTrun, hTheight⟩ := h.checkpoint_runBlock facts hf hHsXb
    have heqTarget :=
      (h.seed.laterFGWitness_eq_or_extends_checkpoint_of_frameN facts
        Hs Xb X hf hcom hfb h.crossing h.frame h.c0le h.ready hpostPrevLo
        h.minimal h.checkpointPreceq hTrun h.checkpointErase hTheight
        hlt hhor (hHsXb _ hb) hn hDmem hW' hcompat).1 hDheight
    rw [hoD]
    exact congrArg some heqTarget

/-- Under the bundle along `W`, the committee majority and the weight bound, for a run-scoped named
    regime and a slot `s` of a round after the source round whose vote instant plus `Δ` is in the
    horizon, every member of the set for that vote instant has every outcome of its in-tree head at
    `s` descending from `T`. -/
theorem NamedHeightRegimeRunOn.heads (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} {Hs : Int → Finset V} {X Xb : Finset V} {lo : Int}
    {W : Nat → V → M.N}
    {r0 : Round} {blocked : Height}
    {first i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hX : ∀ t : Int, 0 ≤ t → Hs t ⊆ X) (hXXb : X ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hfb : BelowOneThirdOn S rho Hs)
    (h : Restated.NamedHeightRegimeRunOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs X Xb r0 blocked first i a ta Cfg T Tprev c0)
    {s : Slot} (hround : a.round + 1 ≤ M.round_of S.hc s)
    (hhor : M.vote_time S.E s + S.E.Δ ≤ rho.horizon)
    (hlo : lo ≤ M.opening S.E S.hc (a.round - S.hc.η_SG))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S k + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    ∀ w ∈ Hs (M.vote_time S.E s), ∀ cc : M.Cache,
      M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E s)) w).st.core.toHealing
        (M.vote_time S.E s)
        (W (strictEventIndex rho (M.vote_time S.E s)) w).cache ⇢ cc →
      let n := M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E s)) w).st
          (M.vote_time S.E s))
        (W (strictEventIndex rho (M.vote_time S.E s)) w).record cc
      ∀ Tr : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ Tr →
      ∀ L : Finset (GoldfishVote V),
        M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
      ∀ L' : Finset (GoldfishVote V),
        M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
      ∀ H : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
          (M.toHealing n.st.core) Tr L L' (n.st.core.s - 1) ⇢ H →
        Block.Preceq T.erase H :=
  ((h.laterHistory_main facts hf hHs hHsXb hX hXXb hcom hfb hround
    hlo hA).1 s rfl hhor).1

/-- Under the bundle along `W`, the committee majority and the weight bound, for a run-scoped named
    regime and a slot `d` after the opening slot of the source round whose vote instant plus `Δ` is
    in the horizon, every member of the set for that vote instant has every outcome of its in-tree
    head at `d` descending from `T`. -/
theorem NamedHeightRegimeRunOn.heads_from_firstInterior (facts : Record.Facts M)
    {S : Setup V} {rho : Record.Run V} {Hs : Int → Finset V} {X Xb : Finset V} {lo : Int}
    {W : Nat → V → M.N}
    {r0 : Round} {blocked : Height}
    {first i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hf : Restated.AdmissibleFieldsOn M S rho W Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t) (hHsXb : ∀ t : Int, Hs t ⊆ Xb)
    (hX : ∀ t : Int, 0 ≤ t → Hs t ⊆ X) (hXXb : X ⊆ Xb)
    (hcom : Restated.HonestCommitteesOn M S Hs)
    (hfb : BelowOneThirdOn S rho Hs)
    (h : Restated.NamedHeightRegimeRunOn M S rho W (fun t => W (strictEventIndex rho t))
      Hs X Xb r0 blocked first i a ta Cfg T Tprev c0)
    {d : Slot} (hdlo : M.opening_slot S.hc a.round + 1 ≤ d)
    (hhor : M.vote_time S.E d + S.E.Δ ≤ rho.horizon)
    (hlo : lo ≤ M.opening S.E S.hc (a.round - S.hc.η_SG))
    (hA : ∀ k : Round, lo ≤ M.early S.E S.hc k .g2 - S.E.Δ → ∀ u ∈ Hs (Restated.Vocabulary.Execution.Setup.a M S k + S.E.Δ), ∀ j : Nat, rho.events[j]? = some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M S k)) → M.awake_for_grade2 S u (W j u) k) :
    ∀ w ∈ Hs (M.vote_time S.E d), ∀ cc : M.Cache,
      M.onPhaseTick S.E S.hc
        (W (strictEventIndex rho (M.vote_time S.E d)) w).st.core.toHealing
        (M.vote_time S.E d)
        (W (strictEventIndex rho (M.vote_time S.E d)) w).cache ⇢ cc →
      let n := M.mkNode
        (M.ns_setClock S.E (W (strictEventIndex rho (M.vote_time S.E d)) w).st
          (M.vote_time S.E d))
        (W (strictEventIndex rho (M.vote_time S.E d)) w).record cc
      ∀ Tr : Finset (Block V), M.voter_filtered_block_tree S.E n.st.core n.st.core.s ⇢ Tr →
      ∀ L : Finset (GoldfishVote V),
        M.voter_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L →
      ∀ L' : Finset (GoldfishVote V),
        M.voter_support_view S.E (M.toHealing n.st.core).toFG.toSG.toGoldfishStore n.st.core.s ⇢ L' →
      ∀ H : Block V, M.get_head_in_tree_with_layer (M.gradeContract n.cache) S.E S.hc
          (M.toHealing n.st.core) Tr L L' (n.st.core.s - 1) ⇢ H →
        Block.Preceq T.erase H := by
  by_cases hdhi : d < M.opening_slot S.hc (a.round + 1)
  · exact (h.seed.checkpointProtection_sourceRound_of_frame_run facts
      hf hHs hHsXb hX hXXb hcom hfb h.crossing h.frame h.c0le h.ready h.postPrev
        h.pred h.minimal hdlo hdhi hhor hlo hA).1
  · have hround : a.round + 1 ≤ M.round_of S.hc d := by
      by_contra hn
      have hle : M.round_of S.hc d + 1 ≤ a.round + 1 := Nat.succ_le_of_lt (Nat.lt_of_not_ge hn)
      exact (Nat.not_lt_of_ge ((facts.gr.opening_slot_le_of_le S.hc hle).trans
        (Nat.le_of_not_lt hdhi))) (facts.gr.lt_opening_slot_round_of_succ S.hc d)
    exact h.heads facts hf hHs hHsXb hX hXXb hcom hfb hround hhor
      hlo hA

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
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.Optimistic

local macro "p58% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Claims.Restated.Claim13beRoute3_58)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

local macro "p64% " n:ident : term =>
  `(priv% $(Lean.mkIdent
      `Proofs.Claims.Restated.Claim13beRoute3_64)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

end

end DecoupledConsensusModel.Sts.Restated
