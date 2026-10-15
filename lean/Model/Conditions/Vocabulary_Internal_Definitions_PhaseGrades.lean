import Proofs.Vocabulary.Internal.Definitions.PhaseGrades
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Record.Wiring

/-!
# Phase grades of a store and a node

The phase grade and root of a grade view and of a store, and the grade read, anchor, G2 candidate,
clearance, raw grade-2 test and FG source of a node state, as sets of outcomes over a model
`M : Record.Model V`, and their counterparts at `Record.Model.vocabulary`.
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
open Execution DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol

/-- The outcomes of the grade test of `B` in phase `p` of round `r`, on the grade view `gv` and the
    finalized block `F`. -/
def Vocabulary.Internal.PhaseGrades.phaseGrade (M : Record.Model V) (E : Env V) (hc : Protocol.HealConfig) (gv : M.GV)
    (F : Block V) (r : Round) (p : Phase) (B : Block V) : DC.NDRE Bool :=
  M.gradeBool E gv F hc.η_SG r (M.early E hc r p) (M.late E hc r p) B

end

section
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.PhaseGrades
open Execution DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol

/-- The outcomes of the root freeze of phase `p` of round `r`, on the grade view `gv` and the
    finalized block `F`. -/
def Vocabulary.Internal.PhaseGrades.phaseRoot (M : Record.Model V) (E : Env V) (hc : Protocol.HealConfig) (gv : M.GV)
    (F : Block V) (r : Round) (p : Phase) : DC.NDRE (Option (Block V)) :=
  M.freezeRoot E gv F hc.η_SG r (M.early E hc r p) (M.late E hc r p)

end

section
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.PhaseGrades
open Execution DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol

/-- The outcomes of `phaseGrade` on the grade view of `st`'s core store and its finalized block. -/
def Vocabulary.Internal.PhaseGrades.storeGrade (M : Record.Model V) (E : Env V) (hc : Protocol.HealConfig) (st : M.NS)
    (r : Round) (p : Phase) (B : Block V) : DC.NDRE Bool :=
  Restated.Vocabulary.Internal.PhaseGrades.phaseGrade M E hc st.core.toHealing.gradeView st.core.F r p B

end

section
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.PhaseGrades
open Execution DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol

/-- The outcomes of `phaseRoot` on the grade view of `st`'s core store and its finalized block. -/
def Vocabulary.Internal.PhaseGrades.storeRoot (M : Record.Model V) (E : Env V) (hc : Protocol.HealConfig) (st : M.NS)
    (r : Round) (p : Phase) : DC.NDRE (Option (Block V)) :=
  Restated.Vocabulary.Internal.PhaseGrades.phaseRoot M E hc st.core.toHealing.gradeView st.core.F r p

end

section
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.PhaseGrades
open Execution DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol

/-- The outcomes of the read of `n`'s grade contract on `n`'s core store at round `r`. -/
def Vocabulary.Internal.PhaseGrades.nodeRead (M : Record.Model V) (S : Setup V) (n : M.N) (r : Round) :
    DC.NDRE (Protocol.GradeRead V) :=
  M.read (M.gradeContract n.cache) S.E S.hc n.st.core.toHealing r

end

section
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.PhaseGrades
open Execution DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol

/-- The anchors of the outcomes of `nodeRead`. -/
def Vocabulary.Internal.PhaseGrades.nodeAnchor (M : Record.Model V) (S : Setup V) (n : M.N) (r : Round) :
    DC.NDRE (Block V) :=
  (fun g => g.anchor) <$> Restated.Vocabulary.Internal.PhaseGrades.nodeRead M S n r

end

section
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.PhaseGrades
open Execution DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol

/-- The optional grade-2 candidates of the outcomes of `nodeRead`. -/
def Vocabulary.Internal.PhaseGrades.nodeQ2 (M : Record.Model V) (S : Setup V) (n : M.N) (r : Round) :
    DC.NDRE (Option (Block V)) :=
  (fun g => g.Q2) <$> Restated.Vocabulary.Internal.PhaseGrades.nodeRead M S n r

end

section
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.PhaseGrades
open Execution DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol

/-- The clearance of `B` in each outcome of `nodeRead`. -/
def Vocabulary.Internal.PhaseGrades.nodeClear (M : Record.Model V) (S : Setup V) (n : M.N) (r : Round) (B : Block V) :
    DC.NDRE Bool :=
  (fun g => g.clear B) <$> Restated.Vocabulary.Internal.PhaseGrades.nodeRead M S n r

end

section
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.PhaseGrades
open Execution DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol

/-- Every grade read `nodeRead` can return has its raw grade-2 test true. -/
def Vocabulary.Internal.PhaseGrades.nodeRawG2 (M : Record.Model V) (S : Setup V) (n : M.N) (r : Round) : Prop :=
  ∀ g, Restated.Vocabulary.Internal.PhaseGrades.nodeRead M S n r ⇢ g → g.rawG2

end

section
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.PhaseGrades
open Execution DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol

/-- The outcomes of the FG source computed from `n`'s core store at round `r`, on each outcome of
    the grade-2 block computed from the same store. -/
def Vocabulary.Internal.PhaseGrades.nodeFGSource (M : Record.Model V) (S : Setup V) (n : M.N) (r : Round) :
    DC.NDRE (Option (Block V)) := do
  let g2 ← M.grade2_block_with (M.gradeContract n.cache) S.E S.hc n.st.core.toHealing r
  M.fg_source_with (M.gradeContract n.cache) S.E S.hc n.st.core.toHealing r g2

end

/-! ## Agreement at `Record.Model.vocabulary` -/

section
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.PhaseGrades
open Execution DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol

/-- At `Record.Model.vocabulary`, the restated `phaseGrade` is the one outcome
    `DecoupledConsensusModel.Internal.PhaseGrades.phaseGrade` computes. -/
@[record_vocabulary]
theorem Vocabulary.Internal.PhaseGrades.phaseGrade_vocabulary_eq (E : Env V) (hc : Protocol.HealConfig) (gv : Protocol.GradeView V) (F : Block V) (r : Round) (p : Phase) (B : Block V) :
    Restated.Vocabulary.Internal.PhaseGrades.phaseGrade (V := V) Record.Model.vocabulary E hc gv F r p B =
      pure (_root_.DecoupledConsensusModel.Internal.PhaseGrades.phaseGrade (V := V) E hc gv F r p B) :=
  rfl

/-- At `Record.Model.vocabulary`, the restated `phaseRoot` is the one outcome
    `DecoupledConsensusModel.Internal.PhaseGrades.phaseRoot` computes. -/
@[record_vocabulary]
theorem Vocabulary.Internal.PhaseGrades.phaseRoot_vocabulary_eq (E : Env V) (hc : Protocol.HealConfig) (gv : Protocol.GradeView V) (F : Block V) (r : Round) (p : Phase) :
    Restated.Vocabulary.Internal.PhaseGrades.phaseRoot (V := V) Record.Model.vocabulary E hc gv F r p =
      pure (_root_.DecoupledConsensusModel.Internal.PhaseGrades.phaseRoot (V := V) E hc gv F r p) :=
  rfl

/-- At `Record.Model.vocabulary`, the restated `storeGrade` is the one outcome
    `DecoupledConsensusModel.Internal.PhaseGrades.storeGrade` computes. -/
@[record_vocabulary]
theorem Vocabulary.Internal.PhaseGrades.storeGrade_vocabulary_eq (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.NamedStore V) (r : Round) (p : Phase) (B : Block V) :
    Restated.Vocabulary.Internal.PhaseGrades.storeGrade (V := V) Record.Model.vocabulary E hc st r p B =
      pure (_root_.DecoupledConsensusModel.Internal.PhaseGrades.storeGrade (V := V) E hc st r p B) :=
  rfl

/-- At `Record.Model.vocabulary`, the restated `storeRoot` is the one outcome
    `DecoupledConsensusModel.Internal.PhaseGrades.storeRoot` computes. -/
@[record_vocabulary]
theorem Vocabulary.Internal.PhaseGrades.storeRoot_vocabulary_eq (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.NamedStore V) (r : Round) (p : Phase) :
    Restated.Vocabulary.Internal.PhaseGrades.storeRoot (V := V) Record.Model.vocabulary E hc st r p =
      pure (_root_.DecoupledConsensusModel.Internal.PhaseGrades.storeRoot (V := V) E hc st r p) :=
  rfl

/-- At `Record.Model.vocabulary`, the restated `nodeRead` is the one outcome
    `DecoupledConsensusModel.Internal.PhaseGrades.nodeRead` computes. -/
@[record_vocabulary]
theorem Vocabulary.Internal.PhaseGrades.nodeRead_vocabulary_eq (S : Setup V) (n : NamedNodeState V) (r : Round) :
    Restated.Vocabulary.Internal.PhaseGrades.nodeRead (V := V) Record.Model.vocabulary S n r =
      pure (_root_.DecoupledConsensusModel.Internal.PhaseGrades.nodeRead (V := V) S n r) :=
  rfl

/-- At `Record.Model.vocabulary`, the restated `nodeAnchor` is the one outcome
    `DecoupledConsensusModel.Internal.PhaseGrades.nodeAnchor` computes. -/
@[record_vocabulary]
theorem Vocabulary.Internal.PhaseGrades.nodeAnchor_vocabulary_eq (S : Setup V) (n : NamedNodeState V) (r : Round) :
    Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor (V := V) Record.Model.vocabulary S n r =
      pure (_root_.DecoupledConsensusModel.Internal.PhaseGrades.nodeAnchor (V := V) S n r) := by
  rw [Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor, nodeRead_vocabulary_eq, map_pure]
  rfl

/-- At `Record.Model.vocabulary`, the restated `nodeQ2` is the one outcome
    `DecoupledConsensusModel.Internal.PhaseGrades.nodeQ2` computes. -/
@[record_vocabulary]
theorem Vocabulary.Internal.PhaseGrades.nodeQ2_vocabulary_eq (S : Setup V) (n : NamedNodeState V) (r : Round) :
    Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 (V := V) Record.Model.vocabulary S n r =
      pure (_root_.DecoupledConsensusModel.Internal.PhaseGrades.nodeQ2 (V := V) S n r) := by
  rw [Restated.Vocabulary.Internal.PhaseGrades.nodeQ2, nodeRead_vocabulary_eq, map_pure]
  rfl

/-- At `Record.Model.vocabulary`, the restated `nodeClear` is the one outcome
    `DecoupledConsensusModel.Internal.PhaseGrades.nodeClear` computes. -/
@[record_vocabulary]
theorem Vocabulary.Internal.PhaseGrades.nodeClear_vocabulary_eq (S : Setup V) (n : NamedNodeState V) (r : Round) (B : Block V) :
    Restated.Vocabulary.Internal.PhaseGrades.nodeClear (V := V) Record.Model.vocabulary S n r B =
      pure (_root_.DecoupledConsensusModel.Internal.PhaseGrades.nodeClear (V := V) S n r B) := by
  rw [Restated.Vocabulary.Internal.PhaseGrades.nodeClear, nodeRead_vocabulary_eq, map_pure]
  rfl

/-- At `Record.Model.vocabulary`, the restated `nodeRawG2` holds exactly when
    `DecoupledConsensusModel.Internal.PhaseGrades.nodeRawG2` does. -/
@[record_vocabulary]
theorem Vocabulary.Internal.PhaseGrades.nodeRawG2_vocabulary_eq (S : Setup V) (n : NamedNodeState V) (r : Round) :
    _root_.DecoupledConsensusModel.Internal.PhaseGrades.nodeRawG2 (V := V) S n r ↔ Restated.Vocabulary.Internal.PhaseGrades.nodeRawG2 (V := V) Record.Model.vocabulary S n r := by
  simp only [Restated.Vocabulary.Internal.PhaseGrades.nodeRawG2, nodeRead_vocabulary_eq,
    Record.returns_pure, forall_eq]
  rfl

/-- At `Record.Model.vocabulary`, the restated `nodeFGSource` is the one outcome
    `DecoupledConsensusModel.Internal.PhaseGrades.nodeFGSource` computes. -/
@[record_vocabulary]
theorem Vocabulary.Internal.PhaseGrades.nodeFGSource_vocabulary_eq (S : Setup V) (n : NamedNodeState V) (r : Round) :
    Restated.Vocabulary.Internal.PhaseGrades.nodeFGSource (V := V) Record.Model.vocabulary S n r =
      pure (_root_.DecoupledConsensusModel.Internal.PhaseGrades.nodeFGSource (V := V) S n r) := by
  simp only [Restated.Vocabulary.Internal.PhaseGrades.nodeFGSource, Record.Model.vocabulary, pure_bind]
  rfl

end

end DecoupledConsensusModel.Sts.Restated
