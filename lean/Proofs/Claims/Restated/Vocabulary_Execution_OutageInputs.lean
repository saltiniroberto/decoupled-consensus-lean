import Proofs.Vocabulary.Execution.OutageInputs
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Claims.Restated.Vocabulary_Protocol_Duties_Inputs_ActionSources
import Proofs.Vocabulary.Protocol.Schedule.NamedTick
import Model.Conditions.Vocabulary_Internal_Definitions_NamedOutageEntry
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedActionReads
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Healing_Action
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring

/-!
# Emitted attestations and the action read

Theorems over a model `M : Record.Model V` and its facts `facts : Record.Facts M`: the stores the
action read of a round can give satisfy the confirmation-membership invariant, and, along a path `W`
of a run, an emitted attestation comes from its author's tick at its round's action time, is the row
of the attestation duty, and has its confirmed root held as a named block.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedOutageInputs
open Execution Internal.NamedOutageEntry

/-- If the named store `st` satisfies the confirmation-membership invariant, so does `st` with the
    grade cache `c` written into it. -/
private theorem invariant_store_with_cache (facts : Record.Facts M) (E : Env V)
    (cfg : Protocol.HeightConfig) (st : M.NS) (c : M.Cache)
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

/-- In every world before the `i`-th event of `rho`, the store of every node state the action read
    of round `r` from `v`'s node state can give satisfies the confirmation-membership invariant. -/
theorem Vocabulary.Proofs.NamedOutageInputs.action_read_invariant (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (i : Nat) (v : V) (r : Round) : ∀ w₁ ∈ Record.stateBeforeOf M S rho i,
    ∀ n ∈ Restated.Vocabulary.Internal.NamedOutageEntry.actionReadFrom M S (w₁ v) r,
    Restated.Vocabulary.Proofs.NamedConfirmationMembership.Invariant M S.E S.cfg n.st := by
  intro w₁ hw₁ n hn
  obtain ⟨c, hc, st, hst, rfl⟩ := hn
  rewrite [facts.nd.mkNode_st]
  exact invariant_store_with_cache facts S.E S.cfg st c
    (facts.dt.invariant_update_gradeContract c S.E S.hc S.cfg _ _
      (facts.hd.invariant_clock S.E S.cfg _ ((Restated.Vocabulary.Execution.Setup.a M S r))
        (Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_invariants facts S rho i v w₁ hw₁).1)
      st hst)

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedOutageInputs
open Execution Internal.NamedOutageEntry

/-- For every path `W` of `rho`, if `v` emits the attestation `a` at `t` along `W`, then some event
    `i` of `rho` is `v`'s tick at `t`, and some outcome of that tick from `v`'s node state in `W i`,
    with `v`'s node state in `W (i + 1)` as its node state, sends `a`; for every node state `n` the
    action read of `a`'s round from `v`'s node state in `W i` can give, every outcome of the
    attestation duty computed from `n` has the row `a`, and `a`'s round is the round of `n`'s slot;
    `a` is `v`'s; `t` is the action time of `a`'s round; and `v`'s node state in `W i` passes
    `M.awake_for_grade2` for `a`'s round. -/
theorem Vocabulary.Proofs.NamedOutageInputs.emitted_attestation_stages (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    {v : V} {a : NamedAttestation V} {t : Time}
    (hem : Restated.Vocabulary.Execution.NamedRun.emits M S rho W v (.attest a) t) :
    ∃ i : Nat, rho.events[i]? = some (.tick v t) ∧
      ∃ out : M.N × List (NamedObject V), M.tick S v (W i v) t ⇢ out ∧ W (i + 1) v = out.1 ∧
      NamedObject.attest a ∈ out.2 ∧
      (∀ n ∈ Restated.Vocabulary.Internal.NamedOutageEntry.actionReadFrom M S (W i v) a.round,
        (∀ D, M.duties_attest_with (M.gradeContract n.cache) S.E S.hc (S.node v)
          n.st n.record ⇢ D → D.2.2 = a) ∧
        a.round = (M.round_of S.hc n.st.core.s)) ∧
      a.val_index = v ∧
      t = (Restated.Vocabulary.Execution.Setup.a M S a.round) ∧
      M.awake_for_grade2 S v (W i v) a.round := by
  obtain ⟨i, hi, out, hout, hw, hmem⟩ := hem
  refine ⟨i, hi, out, hout, hw, hmem, ?_⟩
  have _hr : M.reachedNode (W i v) := facts.ndRun.stateBeforeOf_reachedNode S rho i (W i) (hW i).1 v
  have _hv : M.runs_as (W i v) v := facts.ndRun.stateBeforeOf_runs_as S rho i (W i) (hW i).1 v
  obtain ⟨ht, hawake, hval⟩ := facts.nd.tick_attestation_fields S v (W i v) t _hv out hout a hmem
  subst ht
  refine ⟨fun n hn => ⟨fun D hD => ?_, ?_⟩, hval, rfl, hawake⟩
  · rcases Restated.Vocabulary.Proofs.NamedActionSources.tick_at_action facts S v (W i v) a.round
      out hout n hn D hD with ⟨-, hout2⟩ | ⟨hno, -⟩
    · have ha := hmem
      rw [hout2] at ha
      simp only [List.mem_singleton, NamedObject.attest.injEq] at ha
      exact ha.symm
    · exact absurd hawake hno
  · exact ((Restated.Vocabulary.Proofs.NamedActionSources.action_timing facts S (W i v)
      a.round).2.2 n hn).symm

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedOutageInputs
open Execution Internal.NamedOutageEntry

/-- For every path `W` of `rho`, if `v` emits the attestation `a` at `t` along `W`, then some event
    `i` of `rho` is `v`'s tick at `t`, some outcome of that tick from `v`'s node state in `W i`,
    with `v`'s node state in `W (i + 1)` as its node state, sends `a`, and the store of every node
    state the action read of `a`'s round from `v`'s node state in `W i` can give holds a named block
    `H` whose root is `a`'s confirmed root. -/
theorem Vocabulary.Proofs.NamedOutageInputs.emitted_attestation_head (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    {v : V} {a : NamedAttestation V} {t : Time}
    (hem : Restated.Vocabulary.Execution.NamedRun.emits M S rho W v (.attest a) t) :
    ∃ i : Nat, rho.events[i]? = some (.tick v t) ∧
      ∃ out : M.N × List (NamedObject V), M.tick S v (W i v) t ⇢ out ∧ W (i + 1) v = out.1 ∧
      NamedObject.attest a ∈ out.2 ∧
      ∀ n ∈ Restated.Vocabulary.Internal.NamedOutageEntry.actionReadFrom M S (W i v) a.round,
        ∃ H : NamedBlock V, H ∈ n.st.bodies ∧ a.confirmed = some H.root := by
  obtain ⟨i, hi, out, hout, hw, hmem, hall, _⟩ :=
    Restated.Vocabulary.Proofs.NamedOutageInputs.emitted_attestation_stages facts S rho W hW hem
  refine ⟨i, hi, out, hout, hw, hmem, ?_⟩
  intro n hn
  have hinv := Restated.Vocabulary.Proofs.NamedOutageInputs.action_read_invariant facts S rho i v a.round
    (W i) (hW i).1 n hn
  let gc := M.gradeContract n.cache
  let hs := M.toHealing n.st.core
  let rd := M.round_of S.hc hs.toFG.toSG.toGoldfishStore.s
  obtain ⟨D, hD⟩ := facts.dt.attest_with_nonempty gc S.E S.hc (S.node v) n.st n.record
  have hrow : D.2.2 = a := (hall n hn).1 D hD
  obtain ⟨I, hI⟩ := facts.dt.with_attestation_input_nonempty gc S.E S.hc (S.node v) hs
  obtain ⟨A, hA⟩ := facts.dt.round_action_with_nonempty gc S.E S.hc (S.node v) hs n.record
  obtain ⟨A2, hA2⟩ := facts.dt.grade2_block_with_nonempty gc S.E S.hc hs rd
  obtain ⟨Wb, hWb⟩ := facts.dt.get_sg_vote_with_nonempty gc S.E S.hc hs rd A2
  obtain ⟨B, hB, hhead⟩ := facts.dt.attestation_input_head_gradeContract n.cache
    S.E S.hc S.cfg (S.node v) n.st hinv I hI
  have htree : n.st.core.T = n.st.bodies.image NamedBlock.erase := hinv.1.1.1
  rw [htree] at hB
  obtain ⟨H, hH, rfl⟩ := Finset.mem_image.mp hB
  refine ⟨H, hH, ?_⟩
  have hconfirmed : a.confirmed = some Wb.root := by
    rw [← hrow, facts.dt.attest_with_row gc S.E S.hc (S.node v) n.st n.record D hD A hA]
    exact facts.dt.round_action_with_confirmed gc S.E S.hc (S.node v) hs n.record A hA A2 hA2 Wb hWb
  rw [facts.dt.with_attestation_input_id_confirmed gc S.E S.hc (S.node v) hs I hI A2 hA2 Wb hWb]
    at hhead
  exact hconfirmed.trans (hhead.trans (congrArg some (Proofs.NamedWire.erase_root H)))

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedOutageInputs
open Execution Internal.NamedOutageEntry

/-- For every path `W` of `rho`, `emittedInRound` of `v` and round `k` along `W` is `true` exactly
    when some attestation of `v` for round `k` is emitted by `v` at round `k`'s action time along
    `W`. -/
theorem Vocabulary.Proofs.NamedOutageInputs.emittedInRound_iff (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    (v : V) (k : Round) :
    Restated.Vocabulary.Internal.NamedOutageEntry.emittedInRound M S rho W v k = true ↔
      ∃ a : NamedAttestation V, a.val_index = v ∧ a.round = k ∧
        Restated.Vocabulary.Execution.NamedRun.emits M S rho W v (.attest a)
          (Restated.Vocabulary.Execution.Setup.a M S k) := by
  rw [Restated.Vocabulary.Internal.NamedOutageEntry.emittedInRound]
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi, out, hout, hw, hany⟩
    obtain ⟨o, ho, hrow⟩ := List.any_eq_true.mp hany
    cases o with
    | block B => exact absurd hrow Bool.false_ne_true
    | gfVote u => exact absurd hrow Bool.false_ne_true
    | attest a =>
      have hf : a.val_index = v ∧ a.round = k := of_decide_eq_true hrow
      exact ⟨a, hf.1, hf.2, i, hi, out, hout, hw, ho⟩
  · rintro ⟨a, hval, hr, i, hi, out, hout, hw, ho⟩
    exact ⟨i, hi, out, hout, hw, List.any_eq_true.mpr ⟨.attest a, ho, decide_eq_true ⟨hval, hr⟩⟩⟩

end

end DecoupledConsensusModel.Sts.Restated
