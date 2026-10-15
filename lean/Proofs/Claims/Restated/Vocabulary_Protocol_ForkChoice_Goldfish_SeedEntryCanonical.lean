import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.SeedEntryCanonical
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_Q31_actionSGBlock_tiers
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGrades
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Record.Wiring

/-!
# The cases of a round action's SG block

The cases of the block an honest round action's SG selector picks, stated over a model
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
open DecoupledConsensusModel.Statements.Instantiation
open Internal
open Execution
open Internal.HealingSurface
open Protocol
open Proofs.HealingLemmas
open Proofs.Optimistic

/-- For every node state `n` of `v`'s action read at round `r`, every outcome `g` of `n`'s grade
    read at `r`, and every block `B` the SG selector can return from `n`: either `B` is a descendant
    of, or is, `g`'s anchor, an ancestor of, or is, `n`'s `live_confirmed`, and `g` clears `B`; or
    `B` is `g`'s candidate; or `g` has no candidate, its raw grade-2 test holds and `B` is `n`'s FG
    root; or `g` has no candidate, its raw grade-2 test fails and `B` is `g`'s anchor. -/
theorem Vocabulary.Proofs.HealingSurface.actionSGBlockAt_tiers (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (v : V) (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Proofs.HealingSurface.actionReadAt M S rho v r,
    ∀ g, Restated.Vocabulary.Internal.PhaseGrades.nodeRead M S n r ⇢ g →
    let gc := M.gradeContract n.cache
    let st := (M.toHealing n.st.core)
    let k := (M.round_of S.hc st.s)
    ∀ g2, M.grade2_block_with gc S.E S.hc st k ⇢ g2 →
    ∀ B, M.get_sg_vote_with gc S.E S.hc st k g2 ⇢ B →
    (Block.Preceq g.anchor B ∧
      Block.Preceq B n.st.core.live_confirmed ∧
      g.clear B = true) ∨
    (∃ Q, g.Q2 = some Q ∧ B = Q) ∨
    (g.Q2 = none ∧ g.rawG2 ∧
      B = M.get_fg_root (M.toHealing n.st.core).toFG) ∨
    (g.Q2 = none ∧ ¬ g.rawG2 ∧ B = g.anchor) :=
  Restated.Vocabulary.Proofs.HealingLemmas.Rows.q31_actionsgblock_tiers facts S rho v r

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Internal
open Execution
open Internal.HealingSurface
open Protocol
open Proofs.HealingLemmas
open Proofs.Optimistic

/-- For every node state `n` of `v`'s action read at round `r` and every outcome `g` of `n`'s grade
    read at `r` whose raw grade-2 test holds, every block `B` the SG selector can return from `n` is
    a clear descendant of `g`'s anchor and an ancestor of `n`'s `live_confirmed`, or `g`'s
    candidate, or `n`'s FG root. -/
theorem Vocabulary.Proofs.HealingSurface.actionSGBlockAt_tiers_of_rawG2 (facts : Record.Facts M) (S : Setup V) (rho : Record.Run V) (v : V) (r : Round) :
    ∀ n ∈ Restated.Vocabulary.Proofs.HealingSurface.actionReadAt M S rho v r,
    ∀ g, Restated.Vocabulary.Internal.PhaseGrades.nodeRead M S n r ⇢ g →
    g.rawG2 →
    let gc := M.gradeContract n.cache
    let st := (M.toHealing n.st.core)
    let k := (M.round_of S.hc st.s)
    ∀ g2, M.grade2_block_with gc S.E S.hc st k ⇢ g2 →
    ∀ B, M.get_sg_vote_with gc S.E S.hc st k g2 ⇢ B →
    (Block.Preceq g.anchor B ∧
      Block.Preceq B n.st.core.live_confirmed ∧
      g.clear B = true) ∨
    (∃ Q, g.Q2 = some Q ∧ B = Q) ∨
    B = M.get_fg_root (M.toHealing n.st.core).toFG := by
  intro n hn g hg hraw gc st k g2 hg2 B hB
  rcases Restated.Vocabulary.Proofs.HealingSurface.actionSGBlockAt_tiers facts S rho v r n hn g hg g2 hg2
      B hB with h | h | ⟨-, -, h⟩ | ⟨-, hno, -⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · exact absurd hraw hno

end

end DecoupledConsensusModel.Sts.Restated
