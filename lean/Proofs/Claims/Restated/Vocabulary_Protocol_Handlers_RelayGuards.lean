import Proofs.Vocabulary.Protocol.Handlers.RelayGuards
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Execution_ReceiptCallsBase
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Vocabulary.Protocol.Schedule.NamedTick
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedReceiptCalls
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Record.Wiring

/-!
# The checks an accepted block passed

A block a validator accepts names its slot's proposer, has a parent of an earlier slot, and includes
only admissible attestations, read along a path of the run, stated over a model
`M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedRelayGuards
open Execution

/-- For every path `W` of `rho`, if `v` accepts the block `B` at the `i`-th event at `ta`, read
    along `W`, then `B` names its slot's proposer, `B`'s parent's slot is before `B`'s slot, and the
    attestations `B` includes pass the admission test. -/
theorem Vocabulary.Proofs.NamedRelayGuards.accepted_block_static_guards (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V)
    {i : Nat} {v : V} {B : NamedBlock V} {ta : Time}
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S rho W)
    (hacc : Restated.Vocabulary.Execution.NamedRun.acceptsAt M S rho W i v (.block B) ta) :
    B.erase.proposer? = some (S.E.proposer B.erase.slot) ∧
    B.erase.parent.slot < B.erase.slot ∧
    M.carried_attestations_admissible S.hc B.erase = true := by
  have _hr_0 : M.reachedNode (W i v) := facts.ndRun.stateBeforeOf_reachedNode S rho i (W i) (hW i).1 v
  have _hv_0 : M.runs_as (W i v) v := facts.ndRun.stateBeforeOf_runs_as S rho i (W i) (hW i).1 v
  have _hr_1 : M.reachedNode (W (i + 1) v) := facts.ndRun.stateBeforeOf_reachedNode S rho (i + 1) (W (i + 1)) (hW (i + 1)).1 v
  have _hv_1 : M.runs_as (W (i + 1) v) v := facts.ndRun.stateBeforeOf_runs_as S rho (i + 1) (W (i + 1)) (hW (i + 1)).1 v
  obtain ⟨⟨hproc, -⟩, hpre', hpost'⟩ := hacc
  have hpre : B ∉ (W i v).st.bodies := by
    simpa only [Restated.Vocabulary.Execution.Object.processed, decide_eq_false_iff_not] using hpre'
  have hpost : B ∈ (W (i + 1) v).st.bodies := by
    simpa only [Restated.Vocabulary.Execution.Object.processed, decide_eq_true_eq] using hpost'
  suffices h : ∃ st : M.NS, B ∉ st.bodies ∧
      B ∈ (M.on_block_with .alsoCarried S.E S.hc S.cfg st B).bodies by
    obtain ⟨st, h0, h1⟩ := h
    exact (facts.hd.new_body_guards S.E S.hc S.cfg st B h0 h1).2
  rcases hproc with ⟨t, -, out, hout, hw, hmem⟩ | ⟨t, hdel⟩
  · rw [hw] at hpost
    have hpre0 : B ∉ (M.ns_setClock S.E (W i v).st t).bodies := by
      rw [facts.hd.ModelProperties_setClock_bodies]
      exact hpre
    obtain ⟨⟨hs, ht, hprop⟩, hblock⟩ := facts.nd.block_mem_on_tick_emit S v (W i v) t out hout hmem
    obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc (W i v).st.core.toHealing t (W i v).cache
    obtain ⟨D, hD⟩ := facts.dt.propose_block_with_nonempty S v (W i v) t out hout
      (facts.nd.block_mem_on_tick_emit S v (W i v) t out hout hmem).1.1 (facts.nd.block_mem_on_tick_emit S v (W i v) t out hout hmem).1.2.1
      (facts.nd.block_mem_on_tick_emit S v (W i v) t out hout hmem).1.2.2
      (facts.nd.block_mem_on_tick_emit_awake S v (W i v) t out hout hmem) c hc
    by_cases hg1 : M.awake_for_grade1 S v (W i v) (M.round_of S.hc (S.E.slotOf t))
    swap
    · have hnot : ¬ (0 < S.E.slotOf t ∧ t = M.proposal_time S.E (S.E.slotOf t) ∧
          S.E.proposer (S.E.slotOf t) = (S.node v).val_index ∧
          M.awake_for_grade1 S v (W i v) (M.round_of S.hc (S.E.slotOf t))) :=
        fun h => hg1 h.2.2.2
      rw [((facts.nd.tick_bodies_and_coreT_from_proposal S v (W i v) t out hout).2
        (facts.ndRun.stateBeforeOf_runs_as S rho i (W i) (hW i).1 v) hnot).1] at hpost
      exact absurd hpost hpre0
    have hdue : 0 < S.E.slotOf t ∧ t = M.proposal_time S.E (S.E.slotOf t) ∧
        S.E.proposer (S.E.slotOf t) = (S.node v).val_index ∧
        M.awake_for_grade1 S v (W i v) (M.round_of S.hc (S.E.slotOf t)) :=
      ⟨hs, ht, hprop.trans (S.node_val_index v).symm, hg1⟩
    have _hrs : M.reachedStore (M.ns_setClock S.E (W i v).st t) :=
      facts.sto.reachedStore_setClock S.E _ t (facts.nd.reachedStore_of_node _ _hr_0)
    rw [((facts.nd.tick_bodies_and_coreT_from_proposal S v (W i v) t out hout).1 hdue c hc D hD).1,
      congrArg Prod.fst (facts.dt.propose_block_with_eq_of_snd _ _ _ _ _ _ D hD (hblock c hc D hD))]
      at hpost
    simp only [facts.nd.store_with_cache_bodies] at hpost
    exact ⟨_, hpre0, hpost⟩
  · rcases Restated.Vocabulary.Proofs.NamedRuntime.stateBefore_deliver facts S rho hdel (W i) (hW i).1
        (W (i + 1)) (hW i).2 with hproc | ⟨-, hsame⟩
    · rw [facts.nd.process_st S (W i v) _ (W (i + 1) v) hproc,
        facts.nd.make_grades_compatible_with_finalized_bodies, facts.nd.process_block] at hpost
      exact ⟨_, hpre, hpost⟩
    · rw [hsame] at hpost
      exact absurd hpost hpre

end

end DecoupledConsensusModel.Sts.Restated
