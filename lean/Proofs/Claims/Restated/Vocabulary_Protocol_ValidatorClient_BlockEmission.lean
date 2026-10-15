import Proofs.Vocabulary.Protocol.ValidatorClient.BlockEmission
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Node
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Record.Wiring

/-!
# The blocks a tick emits

The only block a tick emits is its proposal, sent at the slot's proposal time by the slot's
proposer, stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Protocol (Record)
open Internal
open Execution

/-- For every outcome `out` of `v`'s tick at `t` from the node state `n`, if `out` sends the block
    `B`, then the slot of `t` is positive, `t` is that slot's proposal time, `v` is that slot's
    proposer, and for every outcome `c` of the phase tick at `t` every outcome `D` of the proposal
    duty, run with the frame contract of `c` on `n`'s store with its clock set to `t`, has the block
    `B`. -/
theorem Vocabulary.Proofs.HealingSurface.block_mem_on_tick_emit (facts : Record.Facts M) (S : Setup V) (v : V) (n : M.N) (t : Time)
    {B : NamedBlock V} :
    ∀ out ∈ Restated.Vocabulary.Execution.on_tick_emit M S v n t, Object.block B ∈ out.2 →
    ∀ (hn : M.reachedNode n := by trivial) (hv : M.runs_as n v := by trivial),
    (0 < S.E.slotOf t ∧ t = M.proposal_time S.E (S.E.slotOf t) ∧
        S.E.proposer (S.E.slotOf t) = v) ∧
      ∀ c : M.Cache, M.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache ⇢ c →
      ∀ D : M.NS × Option (NamedBlock V),
        M.duties_propose_block_with (M.frameContract c) S.E S.hc S.cfg (S.node v)
          (M.ns_setClock S.E n.st t) ⇢ D →
        D.2 = some B :=
  fun out hout h _hn _hv => facts.nd.block_mem_on_tick_emit S v n t out hout h

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Protocol (Record)
open Internal
open Execution

/-- For every path `W` of `ρ`, if `u` emits the block `B` at `t` along `W`, then the slot of `B` is
    positive, `t` is that slot's proposal time, and `u` is that slot's proposer. -/
theorem Vocabulary.Proofs.HealingSurface.emits_block_shape (facts : Record.Facts M) (S : Setup V) (ρ : Record.Run V) {u : V} {B : NamedBlock V} {t : Time}
    (W : Nat → V → M.N) (hW : Restated.Vocabulary.Execution.NamedRun.OnePath M S ρ W)
    (h : (Restated.Vocabulary.Execution.Run.emits M S ρ W u (Object.block B) t)) :
    0 < B.slot ∧ t = M.proposal_time S.E B.slot ∧ S.E.proposer B.slot = u := by
  obtain ⟨i, hi, out, hout, -, hmem⟩ := h
  have _hr : M.reachedNode (W i u) := facts.ndRun.stateBeforeOf_reachedNode S ρ i (W i) (hW i).1 u
  have _hv : M.runs_as (W i u) u := facts.ndRun.stateBeforeOf_runs_as S ρ i (W i) (hW i).1 u
  obtain ⟨⟨hpos, htime, hprop⟩, hB⟩ :=
    Restated.Vocabulary.Proofs.HealingSurface.block_mem_on_tick_emit facts S u (W i u) t out hout hmem
  have hslot : B.slot = S.E.slotOf t := by
    obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc (W i u).st.core.toHealing t (W i u).cache
    obtain ⟨D, hD⟩ := facts.dt.propose_block_with_nonempty S u (W i u) t out hout
      (facts.nd.block_mem_on_tick_emit S u (W i u) t out hout hmem).1.1 (facts.nd.block_mem_on_tick_emit S u (W i u) t out hout hmem).1.2.1
      (facts.nd.block_mem_on_tick_emit S u (W i u) t out hout hmem).1.2.2
      (facts.nd.block_mem_on_tick_emit_awake S u (W i u) t out hout hmem) c hc
    have hB' := facts.dt.propose_block_with_slot _ S.E S.hc S.cfg (S.node u) _ D hD (hB c hc D hD)
    rwa [facts.hd.Sts_setClock_core_s] at hB'
  refine ⟨by rw [hslot]; exact hpos, by rw [hslot]; exact htime, ?_⟩
  rw [hslot]; exact hprop

end

end DecoupledConsensusModel.Sts.Restated
