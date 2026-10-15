import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bStepFin
import Proofs.Claims.Restated.Claim13beRoute3_5
import Proofs.Claims.Restated.ProcessIdempotent
import Proofs.Claims.Restated.Projection
import Model.Conditions.CommonViewOfFinalizedDescendantsFacts
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Execution_Runtime
import Model.Conditions.Vocabulary_Protocol_Handlers_ConfirmationMembership
import Model.Conditions.Vocabulary_Protocol_Handlers_NamedStore
import Model.Conditions.Vocabulary_Protocol_Handlers_StoreRoots
import Model.Conditions.Vocabulary_Protocol_ValidatorClient_TickRecord
import Model.Record.Wiring

/-!
# Facts about stores under the common view among finalized descendants

Theorems over a model `M : Record.Model V` with facts `facts : Record.Facts M`: trees are closed
under ancestors, honest stores hold the ancestors of their finalized block, and
`CommonViewOfFinalizedDescendantsAt` serves every block the finalized block is compatible with.
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

/-- If `B` is in the tree of `v`'s store after `i` steps and `A` is an ancestor of `B`, then `A` is
    in that tree too. -/
theorem mem_T_of_preceq_sts (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (i : Nat) (v : V) {A B : Block V}
    (hB : B ∈ (x[i][v].st).st.core.T) (hAB : Block.Preceq A B) :
    A ∈ (x[i][v].st).st.core.T := by
  have hinv := Restated.nodeInvariant_sts facts S Sched x i v
  have hT : (x[i][v].st).st.core.T = (x[i][v].st).st.bodies.image NamedBlock.erase :=
    hinv.1.1.1.1
  have hcl : Restated.Vocabulary.Proofs.NamedStore.NamedParentClosed M (x[i][v].st).st := hinv.1.1.1.2.2.1
  refine Proofs.Records.mem_of_preceq ?_ A B hB (preceq_eq_true_iff_Preceq.mpr hAB)
  intro D hD
  refine Or.inr ?_
  rw [hT] at hD ⊢
  obtain ⟨E, hE, rfl⟩ := Finset.mem_image.mp hD
  rw [Proofs.NamedWire.erase_parent]
  exact Finset.mem_image_of_mem NamedBlock.erase (hcl.2 E hE)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If the adversary has held `v` at no time up to step `i`, the named block `C` is in play, and `C`
    is an ancestor of `v`'s finalized block at `i`, then `C` is among `v`'s bodies at `i`. -/
theorem mem_bodies_of_preceq_finalized (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {i : Nat} {v : V} (hv : Restated.HonestThrough M Sched x i v) {C : NamedBlock V}
    (hlog : Restated.blockInLog M S Sched x C)
    (hCF : Block.Preceq C.erase (x[i][v].st).st.core.F) :
    C ∈ (x[i][v].st).st.bodies := by
  obtain ⟨Fb, hFb, hFbe, -⟩ := Restated.finalized_body_of_store facts S Sched x i v
  have hFT : (x[i][v].st).st.core.F ∈ (x[i][v].st).st.core.T := by
    rw [Restated.bodies_image_eq_T facts S Sched x i v, ← hFbe]
    exact Finset.mem_image_of_mem NamedBlock.erase hFb
  exact Restated.mem_bodies_of_mem_T_honest facts S Sched x hexec hv hlog
    (Restated.mem_T_of_preceq_sts facts S Sched x i v hFT hCF)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Under `ExecutionValid` and `CommonViewOfFinalizedDescendantsAt` at `t₀`, a named block `B` that
    a validator honest through `t₀` holds at a step at or before `t₀` is held, at every step `j` at
    or after `t₀ + Δ`, by every validator honest through `j` and awake at `j` whose finalized block
    at `j` is an ancestor or a descendant of `B`. -/
theorem mem_bodies_of_compatible_of_narrowed (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) {t₀ : Int}
    (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x t₀)
    {i j : Nat} {v w : V} {B : NamedBlock V}
    (hi : (x[i].time : Int) ≤ t₀) (hv : HonestThroughTime Sched t₀ v)
    (hB : B ∈ (x[i][v].st).st.bodies)
    (hj : t₀ + S.E.Δ ≤ (x[j].time : Int)) (hw : Restated.HonestThrough M Sched x j w)
    (haw : AtomicAwake x j w)
    (hc : Block.compatible (x[j][w].st).st.core.F B.erase = true) :
    B ∈ (x[j][w].st).st.bodies := by
  rcases compatible_cases hc with h | h
  · exact hcv i j v w B hi hv hB hj hw haw h
  · exact Restated.mem_bodies_of_preceq_finalized facts S Sched x hexec hw
      (Restated.blockInLog_of_mem_bodies facts S Sched (fun t' ht => hv t' (le_trans ht hi)) hB) h

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If `FinalizedPreceqAtStepsInPhase M S x lo hi T` holds and `T` is an ancestor of `D`, then
    `FinalizedPreceqAtStepsInPhase M S x lo hi D` holds. -/
theorem finalizedPreceqAtSteps_mono (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {lo hi : Int} {T D : Block V}
    (h : Restated.FinalizedPreceqAtStepsInPhase M S x lo hi T) (hTD : Block.Preceq T D) :
    Restated.FinalizedPreceqAtStepsInPhase M S x lo hi D :=
  fun d v hh h1 h2 => preceq_trans_Preceq (h d v hh h1 h2) hTD

end

end DecoupledConsensusModel.Sts.Restated
