module
public import Model.Vocabulary.Execution.Node

@[expose] public section

/-!
# Facts about `Execution.NamedProfile.gradeContract`

The grade contract a named node's cache selects, read field by field.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The anchor the grade contract of `c` reads at `st` and round `r` is `Protocol.anchor` at the
    grade-1 result of the round-`r` frame read from `c` at `st`. -/
theorem gradeContract_read_anchor (c : DecoupledConsensusModel.Protocol.Cache V) (E : Env V)
    (hc : Protocol.HealConfig) (st : Protocol.HealingStore V) (r : Round) :
    ((NamedProfile.gradeContract c).read E hc st r).anchor =
      DecoupledConsensusModel.Protocol.anchor E hc st r
        (DecoupledConsensusModel.Protocol.readFrame c st r).g1 := rfl

/-- The grade-2 candidate the grade contract of `c` reads at `st` and round `r` is the grade-2 block
    of the round-`r` frame read from `c` at `st`. -/
theorem gradeContract_read_Q2 (c : DecoupledConsensusModel.Protocol.Cache V) (E : Env V)
    (hc : Protocol.HealConfig) (st : Protocol.HealingStore V) (r : Round) :
    ((NamedProfile.gradeContract c).read E hc st r).Q2 =
      DecoupledConsensusModel.Protocol.grade2Block st
        (DecoupledConsensusModel.Protocol.readFrame c st r) := rfl

end DecoupledConsensusModel.Proofs.ModelProperties

end
