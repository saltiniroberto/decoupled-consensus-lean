import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.GradeBootstrapCore
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_ActionSourceCore
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_Grades
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_ProposalParent
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_SGArrival
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreRoots
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_Action
import Proofs.Claims.Restated.Vocabulary_Protocol_Store_RawSource
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGradeQueries
import Model.Conditions.Vocabulary_Internal_Definitions_TickReads
import Model.Conditions.Vocabulary_Internal_Invariants
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_ModelVocabulary_Healing_Schedule
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring

/-!
# Grade-read and SG-vote facts at a round's action

Facts about a validator's action read at round `r`, stated over a model `M : Record.Model V`: the SG
vote its attestation carries, the store and FG root of the action read, the SG block it selects, and
the ordering of action times.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution
open Internal.HealingSurface
open Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Protocol (HealConfig)
open Proofs.HealingLemmas

/-- For every world `w` before round `r`'s action time, every node state `n` of `v`'s action read
    from `w`, and every outcome `X` of the confirmation write, `n`'s store is some store `st` with
    some cache `c` written into it, and `st`'s core store is `X`. -/
private theorem actionRead_core (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (v : V)
    (r : Round) (w : V → M.N)
    (hw : w ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho
      (Restated.Vocabulary.Execution.Setup.a M S r))
    (n : M.N) (hn : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (w v) r)
    (X : M.S)
    (hX : M.update_confirmation_with (M.gradeContract n.cache) S.E S.hc
      (M.ns_setClock S.E (w v).st (Restated.Vocabulary.Execution.Setup.a M S r)).core
      (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1) ⇢ X) :
    ∃ st : M.NS, ∃ c : M.Cache, n.st = M.store_with_cache st c ∧ st.core = X := by
  obtain ⟨c, hc, st, hst, rfl⟩ := hn
  rw [facts.nd.mkNode_cache] at hX
  exact ⟨st, c, facts.nd.mkNode_st _ _ _,
    facts.dt.named_update_confirmation_with_core _ _ _ _ _ st hst X hX⟩

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution
open Internal.HealingSurface
open Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Protocol (HealConfig)
open Proofs.HealingLemmas

/-- For every world `w` before round `r`'s action time, every node state `n` of `v`'s action read
    from `w`, every outcome `D` of the attestation duty on `n`, and every block `B` the SG selector
    can pick from `n`, the SG projection of `D`'s attestation is the vote `⟨v, r, some B.root⟩`. -/
theorem Vocabulary.Proofs.HealingSurface.sgVote_actionAttestationAt (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (v : V) (r : Round) :
    ∀ w ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho (Restated.Vocabulary.Execution.Setup.a M S r),
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (w v) r,
      let gc := M.gradeContract n.cache
      let st := M.toHealing n.st.core
      let k := M.round_of S.hc st.s
      ∀ D, M.duties_attest_with gc S.E S.hc (S.node v) n.st n.record ⇢ D →
      ∀ A2, M.grade2_block_with gc S.E S.hc st k ⇢ A2 →
      ∀ B, M.get_sg_vote_with gc S.E S.hc st k A2 ⇢ B →
      M.sgVote D.2.2.erase = (⟨v, r, some B.root⟩ : Protocol.SGVote V) := by
  intro w hw n hn gc st k D hD A2 hA2 B hB
  obtain ⟨hval, hround, hconf⟩ :=
    Restated.Vocabulary.Proofs.HealingSurface.actionAttestationAt_shape facts S rho v r n ⟨w, hw, hn⟩
      D hD A2 hA2 B hB
  have hsplit : M.sgVote D.2.2.erase = ⟨D.2.2.val_index, D.2.2.round, D.2.2.confirmed⟩ := by
    rw [← facts.sto.sgVote_val, ← facts.sto.sgVote_round,
      ← facts.sto.sgVote_confirmed]
  rw [hsplit, hval, hround, hconf]

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution
open Internal.HealingSurface
open Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Protocol (HealConfig)
open Proofs.HealingLemmas

/-- The earliest grade cutoff of round `r + 1` is strictly before round `r + 1`'s action time. -/
theorem Vocabulary.Proofs.HealingSurface.next_Γ_neg1_lt_action (facts : Record.Facts M) (S : Setup V) (r : Round) :
    Restated.Vocabulary.Protocol.HealConfig.Γ_neg1 M S.hc S.E.Δ (r + 1) <
      (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) := by
  have h1 := facts.gr.gammaNeg1_eq_domain_g2_succ S r
  have h2 := facts.gr.domain_add_five_delta_le_action S (r + 1) .g2
  have hΔ := S.E.Δ_pos
  show slotStart S.E.Δ (M.opening_slot S.hc (r + 1)) - S.E.Δ < M.a S.hc S.E.Δ (r + 1)
  rw [h1]
  linarith

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution
open Internal.HealingSurface
open Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Protocol (HealConfig)
open Proofs.HealingLemmas

/-- The action time `Setup.a M S r` is strictly increasing in the round `r`. -/
theorem Vocabulary.Proofs.HealingSurface.action_strictMono (facts : Record.Facts M) (S : Setup V) : StrictMono (Restated.Vocabulary.Execution.Setup.a M S) := by
  refine strictMono_nat_of_lt_succ fun r => ?_
  show M.a S.hc S.E.Δ r < M.a S.hc S.E.Δ (r + 1)
  rw [facts.gr.a_add_rounds S r 1]
  have hRnat : 0 < S.hc.R := lt_of_lt_of_le (by omega) S.hc.R_ge_two
  have hR : (0 : Time) < (S.hc.R : Nat) := by
    exact_mod_cast hRnat
  have hinc : (0 : Time) < 4 * S.E.Δ * (S.hc.R : Nat) := by
    exact Int.mul_pos (Int.mul_pos (by norm_num) S.E.Δ_pos) hR
  simpa only [Nat.mul_one] using Int.lt_add_of_pos_right ((Restated.Vocabulary.Execution.Setup.a M S r)) hinc

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingSurface.GradeDeliveryRun
open Internal
open Execution
open Internal.HealingSurface
open Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Protocol (HealConfig)
open Proofs.HealingLemmas

/-- In every world `w` before event `i`, if the SG vote `u` is in the round-`k` bucket of `v`'s
    projected SG pool, then some named attestation row `a` of round `k` stored in `v`'s rows
    projects to `u`. -/
theorem Vocabulary.Proofs.HealingSurface.GradeDeliveryRun.exists_row_of_mem_sg_votes (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (i : Nat) (v : V)
    {u : Protocol.SGVote V} {k : Round} :
    ∀ w ∈ Record.stateBeforeOf M S rho i,
    u ∈ (M.toHealing (w v).st.core).toFG.toSG.sg_votes k →
    ∃ a : NamedAttestation V,
      a ∈ (w v).st.sg_rows a.round ∧
        a.round = k ∧ M.sgVote a.erase = u := by
  intro w hw hu
  have hu' : u ∈ (M.store_sg_pool (w v).st.core k).image M.sgVote := by
    rw [← facts.sto.ModelProperties_toHealing_sg_votes]
    exact hu
  obtain ⟨b, hb, hbu⟩ := Finset.mem_image.mp hu'
  have hpool := (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho i v w hw).1.1.1.2.2.2.1 k
  rw [facts.sto.ModelProperties_mem_sg_pool_iff, hpool] at hb
  obtain ⟨a, ha, hab⟩ := List.mem_map.mp hb
  have hround : a.round = k :=
    Restated.Vocabulary.Proofs.NamedRawSource.row_round_stateBefore facts S rho i v k a w hw ha
  exact ⟨a, by rw [hround]; exact ha, hround, by rw [hab]; exact hbu⟩

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingSurface.GradeDeliveryRun
open Internal
open Execution
open Internal.HealingSurface
open Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Protocol (HealConfig)
open Proofs.HealingLemmas

/-- In every world `w₁` before event `i`, for every `j ≥ i` and every SG vote `u` in a bucket of
    `v`'s projected SG pool, every world `w₂` reached from `w₁` by the events from `i` up to `j`
    leaves `v`'s receipt stamp of `u` as it was in `w₁`. -/
theorem Vocabulary.Proofs.HealingSurface.GradeDeliveryRun.stateBefore_timestamp_sg_vote_carry (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (v : V) {i : Nat} : ∀ w₁ ∈ Record.stateBeforeOf M S rho i,
    ∀ j : Nat, i ≤ j → ∀ {u : Protocol.SGVote V} {k : Round},
      u ∈ (M.toHealing (w₁ v).st.core).toFG.toSG.sg_votes k →
      ∀ w₂ ∈ ((rho.events.drop i).take (j - i)).foldlM (Record.worldStepOf M S) w₁,
      (w₂ v).st.core.timestamp_sg_vote u =
        (w₁ v).st.core.timestamp_sg_vote u := by
  intro w₁ hw₁ j hij u k hu w₂ hw₂
  obtain ⟨a, ha, -, hproj⟩ := Restated.Vocabulary.Proofs.HealingSurface.GradeDeliveryRun.exists_row_of_mem_sg_votes facts S rho i v w₁ hw₁ hu
  have hcarry := (Restated.Vocabulary.Proofs.NamedSGArrival.stateBefore_sg_row_stamp_mono facts S rho v hij w₁ hw₁ ha w₂ hw₂).2
  rw [← hproj]
  exact hcarry

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution
open Internal.HealingSurface
open Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Protocol (HealConfig)
open Proofs.HealingLemmas

/-- If the named store `st` satisfies the confirmation-membership invariant, so does `st` with the
    grade cache `c` written into it. -/
private theorem invariant_store_with_cache (facts : Record.Facts M) (E : Env V)
    (cfg : HeightConfig) (st : M.NS) (c : M.Cache)
    (h : Restated.Vocabulary.Proofs.NamedConfirmationMembership.Invariant M E cfg st) :
    Restated.Vocabulary.Proofs.NamedConfirmationMembership.Invariant M E cfg
      (M.store_with_cache st c) := by
  simp only [Restated.Vocabulary.Proofs.NamedConfirmationMembership.Invariant,
    Restated.Vocabulary.Proofs.NamedStoreRoots.Invariant, Restated.Vocabulary.Proofs.NamedStore.Coherent,
    Restated.Vocabulary.Proofs.NamedStore.TreeView, Restated.Vocabulary.Proofs.NamedStore.ErasureUnique,
    Restated.Vocabulary.Proofs.NamedStore.NamedParentClosed, Restated.Vocabulary.Proofs.NamedStore.PoolView,
    Restated.Vocabulary.Proofs.NamedStore.DerivedView, Restated.Vocabulary.Proofs.NamedStoreRoots.RootsInTree,
    Restated.Vocabulary.Proofs.NamedConfirmationMembership.Confirmed,
    facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView, facts.nd.store_with_cache_bodies,
    facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_sg_votes,
    facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau,
    facts.nd.store_with_cache_core_attestations] at h ⊢
  exact h

/-- For every world `w` before round `r`'s action time and every node state `n` of `v`'s action read
    from `w`, the store of `n` satisfies the confirmation-membership invariant. -/
theorem Vocabulary.Proofs.HealingSurface.actionRead_invariant (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (v : V) (r : Round) :
    ∀ w ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho (Restated.Vocabulary.Execution.Setup.a M S r),
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (w v) r,
    Restated.Vocabulary.Proofs.NamedConfirmationMembership.Invariant M S.E S.cfg n.st := by
  intro w hw n hn
  have hinv := facts.hd.invariant_clock S.E S.cfg _ ((Restated.Vocabulary.Execution.Setup.a M S r))
    (Restated.Vocabulary.Proofs.NamedRuntime.stateBeforeTime_invariants facts S rho
      ((Restated.Vocabulary.Execution.Setup.a M S r)) v w hw).1
  obtain ⟨c, hc, st, hst, rfl⟩ := hn
  rewrite [facts.nd.mkNode_st]
  exact invariant_store_with_cache facts S.E S.cfg st c
    (facts.dt.invariant_update_gradeContract c S.E S.hc S.cfg _ _ hinv st hst)

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution
open Internal.HealingSurface
open Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Protocol (HealConfig)
open Proofs.HealingLemmas

/-- For every world `w` before round `r`'s action time, every node state `n` of `v`'s action read
    from `w`, and every block `B` the SG selector can pick from `n`, `B` is in the tree of `n`'s
    store. -/
theorem Vocabulary.Proofs.HealingSurface.actionSGBlockAt_mem_actionStore (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (v : V) (r : Round) :
    ∀ w ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho (Restated.Vocabulary.Execution.Setup.a M S r),
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (w v) r,
      let gc := M.gradeContract n.cache
      let st := M.toHealing n.st.core
      let k := M.round_of S.hc st.s
      ∀ A2, M.grade2_block_with gc S.E S.hc st k ⇢ A2 →
      ∀ B, M.get_sg_vote_with gc S.E S.hc st k A2 ⇢ B → B ∈ n.st.core.T := by
  intro w hw n hn gc st k A2 hA2 B hB
  have hk : k = r := by
    show M.round_of S.hc (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.s = r
    rw [facts.sto.toHealing_s]
    exact Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt_round facts S rho v r n ⟨w, hw, hn⟩
  obtain ⟨G, hG⟩ := facts.gr.read_nonempty (M.gradeContract n.cache) S.E S.hc st r
  have hA2' : M.grade2_block_with (M.gradeContract n.cache) S.E S.hc st r ⇢ A2 := by
    rw [← hk]; exact hA2
  have hB' : M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc st r A2 ⇢ B := by
    rw [← hk]; exact hB
  have heq : B = M.currentSGVote st G :=
    facts.dt.get_sg_vote_with_gradeContract_grade2 n.cache S.E S.hc st r A2 hA2' G hG B hB'
  have hinv : Restated.Vocabulary.Proofs.NamedConfirmationMembership.Invariant M S.E S.cfg n.st :=
    Restated.Vocabulary.Proofs.HealingSurface.actionRead_invariant facts S rho v r w hw n hn
  obtain ⟨X, hX⟩ := facts.dt.update_confirmation_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.ns_setClock S.E (w v).st (Restated.Vocabulary.Execution.Setup.a M S r)).core
    (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1)
  have hT : n.st.core.T = (w v).st.core.T := by
    obtain ⟨st', c', hnst, hcore⟩ := actionRead_core facts S rho v r w hw n hn X hX
    rw [hnst, facts.nd.store_with_cache_core_T, hcore,
      facts.dt.update_confirmation_with_T _ _ _ _ _ X hX,
      facts.hd.ModelProperties_setClock_core_T]
  have hcl : ∀ B ∈ n.st.core.T, B.parent? = none ∨ B.parent ∈ n.st.core.T := by
    have h := Restated.Vocabulary.Proofs.NamedStoreBridge.parentClosed_stateBeforeTime facts S rho ((Restated.Vocabulary.Execution.Setup.a M S r)) v w hw
    unfold Restated.Vocabulary.Internal.ParentClosed Record.Model.GS.parent_closed at h
    rw [facts.sto.toHealing_T] at h
    rw [hT]
    exact h.2
  have hTT : st.T = n.st.core.T := by
    show (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.T = _
    rw [facts.sto.toHealing_T]
  have hlc : st.toFG.toSG.toGoldfishStore.live_confirmed ∈ n.st.core.T := by
    show (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.live_confirmed ∈ n.st.core.T
    rw [facts.sto.toHealing_live_confirmed]
    exact hinv.2.1
  have hroot : M.get_fg_root st.toFG ∈ n.st.core.T :=
    Restated.Vocabulary.Proofs.NamedStoreRoots.fg_root_mem facts n.st hinv.1.2
  have hanchor : G.anchor ∈ n.st.core.T := by
    obtain ⟨a, ha⟩ := facts.gr.anchor_nonempty S.E S.hc st r (M.readFrame n.cache st r).g1
    rw [facts.nd.ModelProperties_gradeContract_read_anchor n.cache S.E S.hc st r G hG a ha, ← hTT]
    exact Restated.Vocabulary.Proofs.NamedProposalParent.frame_anchor_mem facts S.E S.hc _ _ _
      (by rw [hTT]; exact hroot) a ha
  rw [heq]
  cases hdc : M.deepest_clear (some G.anchor) st.toFG.toSG.toGoldfishStore.live_confirmed
      G.clear with
  | some B =>
      rw [facts.gr.ModelProperties_currentSGVote_of_deepest_clear hdc]
      exact Proofs.Records.mem_of_preceq hcl B
        st.toFG.toSG.toGoldfishStore.live_confirmed hlc (facts.gr.deepest_clear_preceq hdc)
  | none =>
      cases hQ : G.Q2 with
      | some Q =>
          rw [facts.gr.currentSGVote_of_Q2 hdc hQ]
          obtain ⟨x, hx⟩ := facts.gr.grade2Block_nonempty st (M.readFrame n.cache st r)
          have hGx := facts.nd.ModelProperties_gradeContract_read_Q2 n.cache S.E S.hc st r G hG x hx
          exact Restated.Vocabulary.Proofs.HealingSurface.mem_T_of_mem_filteredTree facts
            (facts.gr.mem_filtered_of_grade2Block x hx (hGx.symm.trans hQ))
      | none =>
          by_cases hraw : G.rawG2
          · rw [facts.gr.currentSGVote_of_rawG2 hdc hQ hraw]
            exact hroot
          · rw [facts.gr.currentSGVote_of_not_rawG2 hdc hQ hraw]
            exact hanchor

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution
open Internal.HealingSurface
open Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Protocol (HealConfig)
open Proofs.HealingLemmas

/-- For every world `w` before round `r`'s action time, every node state `n` of `v`'s action read
    from `w`, and every block `B` the SG selector can pick from `n`, `B` is in the tree of `v`'s
    store in `w`. -/
theorem Vocabulary.Proofs.HealingSurface.actionSGBlockAt_mem_storeBeforeTime (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (v : V) (r : Round) :
    ∀ w ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho (Restated.Vocabulary.Execution.Setup.a M S r),
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (w v) r,
      let gc := M.gradeContract n.cache
      let st := M.toHealing n.st.core
      let k := M.round_of S.hc st.s
      ∀ A2, M.grade2_block_with gc S.E S.hc st k ⇢ A2 →
      ∀ B, M.get_sg_vote_with gc S.E S.hc st k A2 ⇢ B → B ∈ (w v).st.core.T :=
  by
    intro w hw n hn gc st k A2 hA2 B hB
    obtain ⟨X, hX⟩ := facts.dt.update_confirmation_with_nonempty (M.gradeContract n.cache) S.E S.hc
      (M.ns_setClock S.E (w v).st (Restated.Vocabulary.Execution.Setup.a M S r)).core
      (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1)
    have hT : n.st.core.T = (w v).st.core.T := by
      obtain ⟨st', c', hnst, hcore⟩ := actionRead_core facts S rho v r w hw n hn X hX
      rw [hnst, facts.nd.store_with_cache_core_T, hcore,
        facts.dt.update_confirmation_with_T _ _ _ _ _ X hX,
        facts.hd.ModelProperties_setClock_core_T]
    rw [← hT]
    exact Restated.Vocabulary.Proofs.HealingSurface.actionSGBlockAt_mem_actionStore facts S rho v r
      w hw n hn A2 hA2 B hB

end

section
open DecoupledConsensusModel.Proofs
open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Protocol (HealConfig)
open Internal
open Execution

/-- At a store whose FG root is its finalized block `st.F`, a viable `st.F` is in the filtered block
    tree. -/
theorem Vocabulary.Proofs.finalizedViable_mem_filtered (facts : Record.Facts M) {st : M.S}
    (hroot : M.get_fg_root (M.toHealing st).toFG = st.F)
    (h : Restated.Vocabulary.Proofs.FinalizedViable M st) :
    st.F ∈ M.get_filtered_block_tree (M.toHealing st).toFG := by
  unfold Restated.Vocabulary.Proofs.FinalizedViable Restated.Vocabulary.Protocol.V_tree at h
  rw [facts.fc.mem_viable_tree_iff] at h
  obtain ⟨⟨hC, hF⟩, W, hW, hCW, hh⟩ := h
  have hroot' : Block.Preceq (M.get_fg_root (M.toHealing st).toFG) st.F := by
    rw [hroot]
    exact Proofs.ModelProperties.Preceq_self _
  exact facts.fc.mem_get_filtered_block_tree_of_parts (M.toHealing st) hC hF hW hCW hh hroot'

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Protocol (HealConfig)
open Internal
open Execution
open Internal
open Execution
open Internal.HealingSurface
open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Protocol (HealConfig)
open Proofs.HealingLemmas

/-- For every world `w` before round `r`'s action time, every node state `n` of `v`'s action read
    from `w`, and every block `B` the SG selector can pick from `n`, the FG root of `n`'s store is
    an ancestor of, or is, `B`. -/
theorem Vocabulary.Proofs.HealingSurface.actionFGRoot_preceq_actionSGBlockAt (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (v : V) (r : Round) :
    ∀ w ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho (Restated.Vocabulary.Execution.Setup.a M S r),
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (w v) r,
      let gc := M.gradeContract n.cache
      let st := M.toHealing n.st.core
      let k := M.round_of S.hc st.s
      ∀ A2, M.grade2_block_with gc S.E S.hc st k ⇢ A2 →
      ∀ B, M.get_sg_vote_with gc S.E S.hc st k A2 ⇢ B →
      Block.Preceq (M.get_fg_root st.toFG) B := by
  intro w hw n hn gc st k A2 hA2 B hB
  have hk : k = r := by
    show M.round_of S.hc (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.s = r
    rw [facts.sto.toHealing_s]
    exact Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt_round facts S rho v r n ⟨w, hw, hn⟩
  obtain ⟨G, hG⟩ := facts.gr.read_nonempty (M.gradeContract n.cache) S.E S.hc st r
  have hA2' : M.grade2_block_with (M.gradeContract n.cache) S.E S.hc st r ⇢ A2 := by
    rw [← hk]; exact hA2
  have hB' : M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc st r A2 ⇢ B := by
    rw [← hk]; exact hB
  have heq : B = M.currentSGVote st G :=
    facts.dt.get_sg_vote_with_gradeContract_grade2 n.cache S.E S.hc st r A2 hA2' G hG B hB'
  have hanchor : Block.Preceq (M.get_fg_root st.toFG) G.anchor := by
    obtain ⟨a, ha⟩ := facts.gr.anchor_nonempty S.E S.hc st r (M.readFrame n.cache st r).g1
    rw [facts.nd.ModelProperties_gradeContract_read_anchor n.cache S.E S.hc st r G hG a ha]
    rcases facts.gr.anchor_cases S.E S.hc st r _ a ha with h | ⟨root, A, -, hp, h⟩
    · rw [h]
      exact Proofs.ModelProperties.Preceq_self _
    · rw [h]
      exact Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mp
        (facts.fc.preceq_get_fg_root_of_mem_filtered (facts.gr.activePrefix_mem _ root A hp))
  rw [heq]
  cases hdc : M.deepest_clear (some G.anchor) st.toFG.toSG.toGoldfishStore.live_confirmed
      G.clear with
  | some B =>
      rw [facts.gr.ModelProperties_currentSGVote_of_deepest_clear hdc]
      exact Proofs.ModelProperties.Preceq_trans hanchor
        (facts.gr.deepest_clear_floor_Preceq hdc)
  | none =>
      cases hQ : G.Q2 with
      | some Q =>
          rw [facts.gr.currentSGVote_of_Q2 hdc hQ]
          obtain ⟨x, hx⟩ := facts.gr.grade2Block_nonempty st (M.readFrame n.cache st r)
          have hGx := facts.nd.ModelProperties_gradeContract_read_Q2 n.cache S.E S.hc st r G hG x hx
          exact Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mp
            (facts.fc.preceq_get_fg_root_of_mem_filtered
              (facts.gr.mem_filtered_of_grade2Block x hx (hGx.symm.trans hQ)))
      | none =>
          by_cases hraw : G.rawG2
          · rw [facts.gr.currentSGVote_of_rawG2 hdc hQ hraw]
            exact Proofs.ModelProperties.Preceq_self _
          · rw [facts.gr.currentSGVote_of_not_rawG2 hdc hQ hraw]
            exact hanchor

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Protocol (HealConfig)
open Internal
open Execution
open Internal
open Execution
open Internal.HealingSurface
open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Protocol (HealConfig)
open Proofs.HealingLemmas

/-- For every world `w` before round `r`'s action time and every node state `n` of `v`'s action read
    from `w`, the store of `n` and `v`'s store in `w` have the same FG root. -/
theorem Vocabulary.Proofs.HealingSurface.actionStoreAt_fgRoot_eq_storeBeforeTime (facts : Record.Facts M)
    (S : Setup V) (rho : Record.Run V) (v : V) (r : Round) :
    ∀ w ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho (Restated.Vocabulary.Execution.Setup.a M S r),
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M S (w v) r,
    M.get_fg_root (M.toHealing n.st.core).toFG =
      M.get_fg_root
        (M.toHealing (w v).st.core).toFG := by
  intro w hw n hn
  obtain ⟨X, hX⟩ := facts.dt.update_confirmation_with_nonempty (M.gradeContract n.cache) S.E S.hc
    (M.ns_setClock S.E (w v).st (Restated.Vocabulary.Execution.Setup.a M S r)).core
    (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1)
  obtain ⟨st', c', hnst, hcore⟩ := actionRead_core facts S rho v r w hw n hn X hX
  rw [hnst, facts.nd.store_with_cache_get_fg_root, hcore,
    facts.dt.update_confirmation_with_toHealing_fg_root _ _ _ _ _ X hX,
    facts.hd.setClock_core_eq_store_with_t_s]
  exact facts.fc.get_fg_root_toHealing_clock _ _ _

end

end DecoupledConsensusModel.Sts.Restated
