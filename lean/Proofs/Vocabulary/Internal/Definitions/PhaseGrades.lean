module
public import Model.Vocabulary.Execution.Node

@[expose] public section

/-!
# Phase-grade vocabulary

The relative grade `phaseGrade` of a block in a phase of a round, the phase's raw root `phaseRoot`,
and the node-level reads `nodeAnchor`, `nodeQ2`, `nodeClear`, `nodeRawG2` and `nodeFGSource` through
the contract the duty uses.
-/


namespace DecoupledConsensusModel.Internal.PhaseGrades
open Execution DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

/-- The executable relative grade of `B` in phase `p` of round `r`. -/
def phaseGrade (E : Env V) (hc : Protocol.HealConfig) (gv : Protocol.GradeView V)
    (F : Block V) (r : Round) (p : Phase) (B : Block V) : Bool :=
  gradeBool E gv F hc.η_SG r (early E hc r p) (late E hc r p) B

/-- The raw root of phase `p`: the deepest graded block of the tree. -/
def phaseRoot (E : Env V) (hc : Protocol.HealConfig) (gv : Protocol.GradeView V)
    (F : Block V) (r : Round) (p : Phase) : Option (Block V) :=
  freezeRoot E gv F hc.η_SG r (early E hc r p) (late E hc r p)

/-- Store-level grade at a named store's own view and finalized chain. -/
def storeGrade (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (r : Round) (p : Phase) (B : Block V) : Bool :=
  phaseGrade E hc st.core.toHealing.gradeView st.core.F r p B

def storeRoot (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (r : Round) (p : Phase) : Option (Block V) :=
  phaseRoot E hc st.core.toHealing.gradeView st.core.F r p

/-- The contract read the actual duty performs on a prepared node. -/
def nodeRead (S : Setup V) (n : NamedNodeState V) (r : Round) : Protocol.GradeRead V :=
  (NamedProfile.gradeContract n.cache).read S.E S.hc n.st.core.toHealing r

/-- The deepest completed G1 block, falling back to the FG root. -/
def nodeAnchor (S : Setup V) (n : NamedNodeState V) (r : Round) : Block V :=
  (nodeRead S n r).anchor

/-- The completed, clipped, active G2 candidate, if any. -/
def nodeQ2 (S : Setup V) (n : NamedNodeState V) (r : Round) : Option (Block V) :=
  (nodeRead S n r).Q2

/-- Clearance against the completed G0 root. -/
def nodeClear (S : Setup V) (n : NamedNodeState V) (r : Round) (B : Block V) : Bool :=
  (nodeRead S n r).clear B

def nodeRawG2 (S : Setup V) (n : NamedNodeState V) (r : Round) : Prop :=
  (nodeRead S n r).rawG2

def nodeFGSource (S : Setup V) (n : NamedNodeState V) (r : Round) : Option (Block V) :=
  Protocol.fg_source_with (NamedProfile.gradeContract n.cache) S.E S.hc
    n.st.core.toHealing r
    (Protocol.grade2_block_with (NamedProfile.gradeContract n.cache) S.E S.hc
      n.st.core.toHealing r)


end DecoupledConsensusModel.Internal.PhaseGrades

end
