import Proofs.Vocabulary.Internal.Definitions.PhaseGradeQueries
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGrades
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Record.Wiring

/-!
# Phase grade queries

The honest validators present by a cutoff, the window majority, aligned batches, the cutoff of all
phases, the node states of a reader, the filtered tree, and the tiers of an action's SG vote, stated
over a model `M : Record.Model V`, and their counterparts at `Record.Model.vocabulary`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol Execution Proofs.HealingSurface

/-- The sets of validators `v` of `Hon` whose interpreted inputs in the window by `cutoff` are
    nonempty, one set for every choice of an outcome of each validator's interpreted inputs. -/
def Vocabulary.Internal.PhaseGrades.honestPresent (M : Record.Model V) (hc : Protocol.HealConfig) (gv : M.GV)
    (F : Block V) (Hon : Finset V) (r : Round) (cutoff : Time) : DC.NDRE (Finset V) := do
  let ins ← (ExceptT.lift {ins : V → Finset (SGVote V) |
      ∀ v, M.interpretedInputs gv F hc.η_SG r cutoff v ⇢ ins v} : DC.NDRE (V → Finset (SGVote V)))
  pure (Hon.filter fun v => (ins v).Nonempty)

end

section
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol Execution Proofs.HealingSurface

/-- For every outcome `H` of `honestPresent`, the validators outside `Hon` weigh less than `H`. -/
def Vocabulary.Internal.PhaseGrades.WindowMajorityAt (M : Record.Model V) (E : Env V) (hc : Protocol.HealConfig) (gv : M.GV)
    (F : Block V) (Hon : Finset V) (r : Round) (cutoff : Time) : Prop :=
  ∀ H, Restated.Vocabulary.Internal.PhaseGrades.honestPresent M hc gv F Hon r cutoff ⇢ H →
    E.electorate.weightOf (Finset.univ \ Hon) < E.electorate.weightOf H

end

section
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol Execution Proofs.HealingSurface

/-- For every validator `v` of `Hon` and every outcome `I` of `v`'s interpreted inputs by `cutoff`,
    every block of `gv`'s tree whose root a latest-round vote of `I` confirms is an ancestor of
    `Can`. -/
def Vocabulary.Internal.PhaseGrades.BatchAlignedAt (M : Record.Model V) (hc : Protocol.HealConfig) (gv : M.GV)
    (F : Block V) (Hon : Finset V) (r : Round) (cutoff : Time) (Can : Block V) : Prop :=
  ∀ v ∈ Hon, ∀ I, M.interpretedInputs gv F hc.η_SG r cutoff v ⇢ I → ∀ u ∈ I,
    (∀ u' ∈ I, u'.round ≤ u.round) →
    ∀ head, u.confirmed = some head.root → Block.find? gv.T head.root = some head →
      Block.Preceq head Can

end

section
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol Execution Proofs.HealingSurface

/-- The G0 cutoff of round `r`, the earliest of the round's three phase cutoffs. -/
abbrev Vocabulary.Internal.PhaseGrades.allPhasesCutoff (M : Record.Model V) (E : Env V) (hc : Protocol.HealConfig) (r : Round) : Time :=
  M.late E hc r .g0

end

section
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol Execution Proofs.HealingSurface

/-- The set of node states `v` holds in some world that can hold before time `t`. -/
abbrev Vocabulary.Internal.PhaseGrades.readAt (M : Record.Model V) (S : Setup V) (rho : Record.Run V) (t : Time) (v : V) :
    DC.NDR M.N :=
  (fun w => w v) '' Restated.Vocabulary.Execution.NamedRun.stateBeforeTime M S rho t

end

section
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol Execution Proofs.HealingSurface

/-- The filtered block tree of the store of `n`. -/
abbrev Vocabulary.Internal.PhaseGrades.filteredTree (M : Record.Model V) (n : M.N) : Finset (Block V) :=
  M.get_filtered_block_tree (M.toHealing n.st.core).toFG

end

section
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol Execution Proofs.HealingSurface

/-- For every validator `v`, round `r`, node state `n` that `v` can hold at round `r`'s action,
    outcome `g` of `n`'s grade read at round `r`, and block `B` that `v`'s SG vote can select from
    `n`, `B` is a clear descendant of `g`'s anchor and an ancestor of `n`'s `live_confirmed`, or
    `g`'s active G2 candidate, or the FG root when raw G2 holds with no active candidate, or `g`'s
    anchor when raw G2 does not hold. -/
def Vocabulary.Internal.PhaseGrades.Q31_actionSGBlock_tiers (M : Record.Model V) (S : Setup V) (rho : Record.Run V) : Prop :=
  ∀ (v : V) (r : Round), ∀ n ∈ Restated.Vocabulary.Proofs.HealingSurface.actionReadAt M S rho v r,
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
    (g.Q2 = none ∧ ¬ g.rawG2 ∧ B = g.anchor)

end

/-! ## Agreement at `Record.Model.vocabulary` -/

section
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol Execution Proofs.HealingSurface

/-- At `Record.Model.vocabulary`, exactly one function gives every validator an outcome of its
    interpreted inputs by `cutoff`: the interpreted inputs themselves. -/
theorem Vocabulary.Internal.PhaseGrades.interpretedInputs_choice_vocabulary (gv : Protocol.GradeView V)
    (F : Block V) (η : Nat) (r : Round) (cutoff : Time) :
    {ins : V → Finset (SGVote V) | ∀ v, (Record.Model.vocabulary (V := V)).interpretedInputs gv F η r
        cutoff v ⇢ ins v} =
      {fun v => _root_.DecoupledConsensusModel.Protocol.interpretedInputs gv F η r cutoff v} := by
  ext ins
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro h
    funext v
    exact (Record.returns_pure _ _).1 (h v)
  · intro h v
    subst h
    exact (Record.returns_pure _ _).2 rfl

/-- At `Record.Model.vocabulary`, the restated `honestPresent` is the one outcome
    `DecoupledConsensusModel.Internal.PhaseGrades.honestPresent` computes. -/
@[record_vocabulary]
theorem Vocabulary.Internal.PhaseGrades.honestPresent_vocabulary_eq (hc : Protocol.HealConfig) (gv : Protocol.GradeView V) (F : Block V) (Hon : Finset V) (r : Round) (cutoff : Time) :
    Restated.Vocabulary.Internal.PhaseGrades.honestPresent (V := V) Record.Model.vocabulary hc gv F Hon r cutoff =
      pure (_root_.DecoupledConsensusModel.Internal.PhaseGrades.honestPresent (V := V) hc gv F Hon r cutoff) := by
  rw [Restated.Vocabulary.Internal.PhaseGrades.honestPresent,
    Vocabulary.Internal.PhaseGrades.interpretedInputs_choice_vocabulary, ← Set.pure_def,
    ExceptT.lift_pure, pure_bind]
  rfl

/-- At `Record.Model.vocabulary`, the restated `WindowMajorityAt` holds exactly when
    `DecoupledConsensusModel.Internal.PhaseGrades.WindowMajorityAt` does. -/
@[record_vocabulary]
theorem Vocabulary.Internal.PhaseGrades.WindowMajorityAt_vocabulary_eq (E : Env V) (hc : Protocol.HealConfig) (gv : Protocol.GradeView V) (F : Block V) (Hon : Finset V) (r : Round) (cutoff : Time) :
    _root_.DecoupledConsensusModel.Internal.PhaseGrades.WindowMajorityAt (V := V) E hc gv F Hon r cutoff ↔ Restated.Vocabulary.Internal.PhaseGrades.WindowMajorityAt (V := V) Record.Model.vocabulary E hc gv F Hon r cutoff := by
  simp only [Restated.Vocabulary.Internal.PhaseGrades.WindowMajorityAt,
    Vocabulary.Internal.PhaseGrades.honestPresent_vocabulary_eq, Record.returns_pure, forall_eq]
  exact Iff.rfl

/-- At `Record.Model.vocabulary`, the restated `BatchAlignedAt` holds exactly when
    `DecoupledConsensusModel.Internal.PhaseGrades.BatchAlignedAt` does. -/
@[record_vocabulary]
theorem Vocabulary.Internal.PhaseGrades.BatchAlignedAt_vocabulary_eq (hc : Protocol.HealConfig) (gv : Protocol.GradeView V) (F : Block V) (Hon : Finset V) (r : Round) (cutoff : Time) (Can : Block V) :
    _root_.DecoupledConsensusModel.Internal.PhaseGrades.BatchAlignedAt (V := V) hc gv F Hon r cutoff Can ↔ Restated.Vocabulary.Internal.PhaseGrades.BatchAlignedAt (V := V) Record.Model.vocabulary hc gv F Hon r cutoff Can := by
  simp only [Restated.Vocabulary.Internal.PhaseGrades.BatchAlignedAt, Record.Model.vocabulary,
    Record.returns_pure, forall_eq]
  rfl

/-- At `Record.Model.vocabulary`, the restated `allPhasesCutoff` is
    `DecoupledConsensusModel.Internal.PhaseGrades.allPhasesCutoff`. -/
@[record_vocabulary]
theorem Vocabulary.Internal.PhaseGrades.allPhasesCutoff_vocabulary_eq (E : Env V) (hc : Protocol.HealConfig) (r : Round) :
    _root_.DecoupledConsensusModel.Internal.PhaseGrades.allPhasesCutoff (V := V) E hc r = Restated.Vocabulary.Internal.PhaseGrades.allPhasesCutoff (V := V) Record.Model.vocabulary E hc r :=
  rfl

/-- At `Record.Model.vocabulary` and a run embedded by `Record.Run.ofVocabulary`, the restated `readAt`
    is the singleton of the value of `DecoupledConsensusModel.Internal.PhaseGrades.readAt`. -/
@[record_vocabulary]
theorem Vocabulary.Internal.PhaseGrades.readAt_vocabulary_eq (S : Setup V) (rho : Run V) (t : Time) (v : V) :
    Restated.Vocabulary.Internal.PhaseGrades.readAt (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) t v =
      {_root_.DecoupledConsensusModel.Internal.PhaseGrades.readAt (V := V) S rho t v} := by
  show (fun w => w v) '' Restated.Vocabulary.Execution.NamedRun.stateBeforeTime Record.Model.vocabulary S (Record.Run.ofVocabulary rho) t = _
  rw [Vocabulary.Execution.NamedRun.stateBeforeTime_vocabulary_eq]
  exact Set.image_singleton

/-- At `Record.Model.vocabulary`, the restated `filteredTree` is
    `DecoupledConsensusModel.Internal.PhaseGrades.filteredTree`. -/
@[record_vocabulary]
theorem Vocabulary.Internal.PhaseGrades.filteredTree_vocabulary_eq (n : NamedNodeState V) :
    _root_.DecoupledConsensusModel.Internal.PhaseGrades.filteredTree (V := V) n = Restated.Vocabulary.Internal.PhaseGrades.filteredTree (V := V) Record.Model.vocabulary n :=
  rfl

/-- At `Record.Model.vocabulary` and a run embedded by `Record.Run.ofVocabulary`, the restated
    `Q31_actionSGBlock_tiers` holds exactly when
    `DecoupledConsensusModel.Internal.PhaseGrades.Q31_actionSGBlock_tiers` does. -/
@[record_vocabulary]
theorem Vocabulary.Internal.PhaseGrades.Q31_actionSGBlock_tiers_vocabulary_eq (S : Setup V) (rho : Run V) :
    _root_.DecoupledConsensusModel.Internal.PhaseGrades.Q31_actionSGBlock_tiers (V := V) S rho ↔ Restated.Vocabulary.Internal.PhaseGrades.Q31_actionSGBlock_tiers (V := V) Record.Model.vocabulary S (Record.Run.ofVocabulary rho) := by
  unfold Restated.Vocabulary.Internal.PhaseGrades.Q31_actionSGBlock_tiers
  simp only [Vocabulary.Proofs.HealingSurface.actionReadAt_vocabulary_eq,
    Vocabulary.Internal.PhaseGrades.nodeRead_vocabulary_eq, Record.returns_pure, forall_eq]
  constructor
  · intro h v r n hn g2 hg2 B hB
    obtain rfl : n = _ := hn
    obtain rfl := (Record.returns_pure _ _).1 hg2
    obtain rfl := (Record.returns_pure _ _).1 hB
    exact h v r
  · intro h v r
    exact h v r _ rfl _ ((Record.returns_pure _ _).2 rfl) _ ((Record.returns_pure _ _).2 rfl)

end

end DecoupledConsensusModel.Sts.Restated
