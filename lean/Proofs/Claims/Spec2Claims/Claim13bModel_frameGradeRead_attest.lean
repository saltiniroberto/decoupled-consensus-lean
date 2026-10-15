import Proofs.Claims.Spec2Claims.Claim13bStepSG

/-!
# Facts about `Protocol.frameGradeRead`

The anchor and test fields of the frame grade read.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.frameGradeRead

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The anchor field of `Protocol.frameGradeRead c E hc st r` is `Protocol.anchor` at `st`, the
    round `r` and the grade-1 result of the frame `Protocol.readFrame c st r`. -/
theorem frameGradeRead_anchor (c : Protocol.Cache V) (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.HealingStore V) (r : Round) :
    (Protocol.frameGradeRead c E hc st r).anchor
      = Protocol.anchor E hc st r (Protocol.readFrame c st r).g1 := rfl

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The test field of the frame grade read is `Protocol.clear` of the frame
    `Protocol.readFrame c st r`. -/
theorem frameGradeRead_clear (c : Protocol.Cache V) (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.HealingStore V) (r : Round) :
    (Protocol.frameGradeRead c E hc st r).clear = Protocol.clear (Protocol.readFrame c st r) :=
  rfl

end DecoupledConsensusModel.Sts

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]


end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]


end DecoupledConsensusModel.Sts
