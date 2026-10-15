import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_Action
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGradeQueries
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGrades
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Record.Wiring

/-!
# The SG block equals the live confirmation

When the SG block a round action selects is its `live_confirmed` block, stated over a model
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
open DecoupledConsensusModel.Proofs.HealingSurface
open Internal
open Execution
open Internal.HealingSurface
open Internal.PhaseGrades

/-- For every node state `n` of `v`'s action read at round `r`, if `n`'s `live_confirmed` is `D`,
    the grade view of `n` is batch-aligned to `Can` at `r`, `Can` is an ancestor of `D`, and for an
    outcome `G` of `n`'s grade read at `r` the anchor of `G` is `A`, `A` is an ancestor of `Can`,
    and the clearance of `G` passes `D`, then every SG block selected from `n` is `D`. -/
theorem Vocabulary.Proofs.HealingSurface.actionSGBlockAt_eq_liveConfirmed_of_batchAligned (facts : Record.Facts M)
    (S : Setup V) {rho : Record.Run V} {v : V} {r : Round}
    {Can D A : Block V} :
    ∀ n ∈ Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt M S rho v r,
    n.st.core.live_confirmed = D →
    Restated.Vocabulary.Internal.PhaseGrades.BatchAlignedAt M S.hc (M.gradeView (M.toHealing n.st.core))
        n.st.core.F rho.honest r (Restated.Vocabulary.Internal.PhaseGrades.allPhasesCutoff M S.E S.hc r) Can →
    Block.Preceq Can D →
    ∀ G : Protocol.GradeRead V, Restated.Vocabulary.Internal.PhaseGrades.nodeRead M S n r ⇢ G →
    G.anchor = A →
    Block.Preceq A Can →
    G.clear D = true →
    (let gc := M.gradeContract n.cache
     let st := M.toHealing n.st.core
     let k := M.round_of S.hc st.s
     ∀ g : Option (Block V), M.grade2_block_with gc S.E S.hc st k ⇢ g →
     ∀ W : Block V, M.get_sg_vote_with gc S.E S.hc st k g ⇢ W → W = D) := by
  intro n hn hconfirmed _hbatch hCanD G hG hanchor hACan hclear
  have hwalk : M.deepest_clear (some G.anchor)
      (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.live_confirmed G.clear = some D := by
    rw [facts.sto.toHealing_live_confirmed, hconfirmed]
    refine facts.gr.deepest_clear_eq_tip ?_ hclear
    show Block.preceq G.anchor D = true
    rw [hanchor]
    exact Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mpr
      (Proofs.ModelProperties.Preceq_trans hACan hCanD)
  have hround : M.round_of S.hc (M.toHealing n.st.core).s = r := by
    show M.round_of S.hc (M.toHealing n.st.core).toFG.toSG.toGoldfishStore.s = r
    rw [facts.sto.toHealing_s]
    exact Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt_round facts S rho v r n hn
  show ∀ g : Option (Block V), M.grade2_block_with (M.gradeContract n.cache) S.E S.hc
      (M.toHealing n.st.core) (M.round_of S.hc (M.toHealing n.st.core).s) ⇢ g →
    ∀ W : Block V, M.get_sg_vote_with (M.gradeContract n.cache) S.E S.hc (M.toHealing n.st.core)
      (M.round_of S.hc (M.toHealing n.st.core).s) g ⇢ W → W = D
  rw [hround]
  intro g _ W hW
  exact facts.dt.get_sg_vote_with_gradeContract_of_deepest_clear n.cache S.E S.hc
    (M.toHealing n.st.core) r g G hG hwalk W hW

end

end DecoupledConsensusModel.Sts.Restated
