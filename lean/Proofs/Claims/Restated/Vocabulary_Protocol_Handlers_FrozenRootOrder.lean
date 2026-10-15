import Proofs.Vocabulary.Protocol.Handlers.FrozenRootOrder
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_JustificationCarrier
import Model.Conditions.Vocabulary_Execution_Runtime
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_FGForkChoice_Finality
import Model.Conditions.Vocabulary_Model_Execution_Run
import Proofs.Vocabulary.Protocol.ChainState.Chain
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring

/-!
# The finalized block is an ancestor of the justified block

In every world of a run, a validator's finalized block is an ancestor of its justified block, and
when `h_max = h_j + 1` the justified block is viable and the FG root is in the filtered tree, stated
over a model `M : Record.Model V`.
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
open DecoupledConsensusModel.Proofs.NamedOutageClosure
open Execution Internal.NamedStableChainOutage
open DecoupledConsensusModel.Protocol Protocol

/-- In the node state validator `v` starts from under setup `S`, the finalized block is an ancestor
    of, or is, the justified block. -/
theorem Vocabulary.Proofs.NamedOutageClosure.frozen_initial (facts : Record.Facts M) (S : Setup V) (v : V) :
    Block.Preceq ((fun v' => M.initial S v') v : M.N).st.core.F
      ((fun v' => M.initial S v') v : M.N).st.core.J :=
  by
    show Block.Preceq (M.initial S v : M.N).st.core.F
      (M.initial S v : M.N).st.core.J
    rw [facts.nd.initial_st, facts.hd.initial_core_F,
      facts.hd.initial_core_J]
    exact Proofs.ModelProperties.Preceq_self _

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedOutageClosure
open Execution Internal.NamedStableChainOutage
open DecoupledConsensusModel.Protocol Protocol

private theorem frozen_step_record (facts : Record.Facts M) (S : Setup V) (w : V → M.N)
    (e : Record.Event V) (h : ∀ v, Block.Preceq (w v).st.core.F (w v).st.core.J) :
    ∀ w' ∈ Record.worldStepOf M S w e,
      ∀ v, Block.Preceq (w' v).st.core.F (w' v).st.core.J := by
  intro w' hw' v
  cases e with
  | wake u t =>
    obtain rfl : w' = Function.update w u (M.wake (w u)) := hw'
    by_cases hv : v = u
    · subst hv
      rw [Function.update_self, (facts.nd.wake_st_record (w v)).1]
      exact h v
    · rw [Function.update_of_ne hv]
      exact h v
  | tick u t =>
    simp only [Record.worldStepOf, Set.mem_setOf_eq] at hw'
    rcases hw' with ⟨out, hout, rfl⟩ | ⟨-, rfl⟩
    · by_cases hv : v = u
      · subst hv
        rw [Function.update_self]
        exact facts.nd.frozen_tick_preceq S v (w v) t (h v) out hout
      · rw [Function.update_of_ne hv]
        exact h v
    · exact h v
  | deliver u o t =>
    simp only [Record.worldStepOf, Set.mem_setOf_eq] at hw'
    rcases hw' with ⟨n', hn', rfl⟩ | ⟨-, rfl⟩
    · by_cases hv : v = u
      · subst hv
        rw [Function.update_self]
        exact facts.nd.frozen_process_preceq S (w v) o (h v) n' hn'
      · rw [Function.update_of_ne hv]
        exact h v
    · exact h v

private theorem frozen_fold_record (facts : Record.Facts M) (S : Setup V) :
    ∀ (l : List (Record.Event V)) (w : V → M.N),
      (∀ v, Block.Preceq (w v).st.core.F (w v).st.core.J) →
      ∀ w₂ ∈ l.foldlM (Record.worldStepOf M S) w,
        ∀ v, Block.Preceq (w₂ v).st.core.F (w₂ v).st.core.J := by
  intro l
  induction l with
  | nil =>
    intro w h w₂ hw₂
    obtain rfl := Set.mem_singleton_iff.mp hw₂
    exact h
  | cons e l ih =>
    intro w h w₂ hw₂
    rw [List.foldlM_cons, Set.bind_def] at hw₂
    obtain ⟨w', hw', hw₂'⟩ := Set.mem_iUnion₂.mp hw₂
    exact ih w' (frozen_step_record facts S w e h w' hw') w₂ hw₂'

/-- In every world before time `t`, `v`'s finalized block is an ancestor of, or is, its justified
    block. -/
theorem Vocabulary.Proofs.NamedOutageClosure.stateBeforeTime_F_preceq_J (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (t : Time) (v : V) : ∀ w₁ ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t,
    Block.Preceq (w₁ v).st.core.F
      (w₁ v).st.core.J := fun w₁ hw₁ =>
  frozen_fold_record facts S (rho.events.filter (fun e => decide (e.time < t)))
    (fun v' => M.initial S v')
    (Restated.Vocabulary.Proofs.NamedOutageClosure.frozen_initial facts S) w₁ hw₁ v

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedOutageClosure
open Execution Internal.NamedStableChainOutage
open DecoupledConsensusModel.Protocol Protocol

/-- In every world `w₁` before time `t`, if `v`'s `h_max` is its `h_j` plus one, then `v`'s
    justified block is in the viable tree of `v`'s FG view. -/
theorem Vocabulary.Proofs.NamedOutageClosure.justifiedRoot_viable_of_state (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (t : Time) (v : V) :
    ∀ w₁ ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t,
    (w₁ v).st.core.h_max = (w₁ v).st.core.h_j + 1 →
    (w₁ v).st.core.J ∈
      Restated.Vocabulary.Protocol.V_tree M (M.toHealing (w₁ v).st.core).toFG := by
  intro w₁ hw₁ hgate
  set st := (w₁ v).st with hst
  have hinv := Restated.Vocabulary.Proofs.NamedRuntime.stateBeforeTime_invariants facts S rho t v w₁ hw₁
  have hcoh : Restated.Vocabulary.Proofs.NamedStore.Coherent M S.E S.cfg st := hinv.1.1.1
  have hroots : Restated.Vocabulary.Proofs.NamedStoreRoots.RootsInTree M st := hinv.1.1.2
  obtain ⟨D, hD, hDJ, hDhj⟩ :=
    Restated.Vocabulary.Proofs.NamedJustificationCarrier.justification_carrier_stateBeforeTime facts S rho t v w₁ hw₁
  have hDorder := (facts.cs.chainOrder_derive_named S.E S.cfg D)
  have hDanchors := (facts.cs.derive_named_anchors_preceq S.E S.cfg D)
  have hDraw : D.erase ∈ st.core.T := by
    rw [hcoh.1]; exact Finset.mem_image_of_mem NamedBlock.erase hD
  have hDheight : st.core.h_max - 1 ≤ (st.core.σ D.erase).h := by
    rw [hcoh.2.2.2.2 D hD]
    have hlt : st.core.h_j < (M.derive_named S.E S.cfg D).h := by
      rw [← hDhj]; exact hDorder.justified_below_height
    have hgate' : st.core.h_max = st.core.h_j + 1 := hgate
    rw [hgate', Nat.add_sub_cancel]
    exact hlt.le
  have hJD : Block.Preceq st.core.J D.erase := by rw [← hDJ]; exact hDanchors.2
  unfold Restated.Vocabulary.Protocol.V_tree
  rw [facts.fc.mem_viable_tree_iff]
  unfold Record.Model.FGS.T
  rw [facts.sto.toHealing_T,
    facts.sto.ModelProperties_toHealing_F, facts.sto.ModelProperties_toHealing_σ,
    facts.sto.ModelProperties_toHealing_h_max]
  exact ⟨⟨hroots.2, Restated.Vocabulary.Proofs.NamedOutageClosure.stateBeforeTime_F_preceq_J facts S rho t v w₁ hw₁⟩, D.erase, hDraw, hJD, hDheight⟩

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedOutageClosure
open Execution Internal.NamedStableChainOutage
open DecoupledConsensusModel.Protocol Protocol

/-- In every world `w₁` before time `t`, if `v`'s `h_max` is its `h_j` plus one, then the FG root of
    `v`'s FG view is in its filtered block tree. -/
theorem Vocabulary.Proofs.NamedOutageClosure.justifiedRoot_mem_filtered (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (t : Time) (v : V) :
    ∀ w₁ ∈ Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t,
    (w₁ v).st.core.h_max = (w₁ v).st.core.h_j + 1 →
    M.get_fg_root
        (M.toHealing (w₁ v).st.core).toFG ∈
      M.get_filtered_block_tree
        (M.toHealing (w₁ v).st.core).toFG := by
  intro w₁ hw₁ hgate
  have hroot : M.get_fg_root (M.toHealing (w₁ v).st.core).toFG = (w₁ v).st.core.J :=
    facts.fc.get_fg_root_toHealing_of_eq _ hgate
  have hV := Restated.Vocabulary.Proofs.NamedOutageClosure.justifiedRoot_viable_of_state facts S rho t v w₁ hw₁ hgate
  rw [← hroot] at hV
  unfold Restated.Vocabulary.Protocol.V_tree at hV
  rw [facts.fc.mem_viable_tree_iff] at hV
  obtain ⟨⟨hC, hF⟩, W, hW, hCW, hh⟩ := hV
  exact facts.fc.mem_get_filtered_block_tree_of_parts (M.toHealing (w₁ v).st.core) hC hF hW hCW hh
    (Proofs.ModelProperties.Preceq_self _)

end

end DecoupledConsensusModel.Sts.Restated
