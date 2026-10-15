import Model.Vocabulary.Execution.Node
import Proofs.Claims.ModelIrreducible

/-!
# Facts about `NamedProfile.gradeContract`: the SG root it supplies

Lemmas that unfold the named node's grade contract, `Protocol.frameContract`, whose read is
`Protocol.frameGradeRead`, and the SG root `Protocol.get_sg_root_with` a duty reads through it.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Execution.NamedProfile.gradeContract
  DecoupledConsensusModel.Protocol.anchor DecoupledConsensusModel.Protocol.frameContract
  DecoupledConsensusModel.Protocol.frameGradeRead DecoupledConsensusModel.Protocol.get_sg_root_with
  DecoupledConsensusModel.Protocol.grade2_block_with

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The SG root a duty reads through the grade contract of the cache `c`, at the store `st` and
    round `r`, is `Protocol.anchor` at the grade-1 result of the round-`r` frame read from `c` at
    `st`. -/
theorem gradeContract_sgRoot_eq_frameAnchor (c : Protocol.Cache V) (E : Env V)
    (hc : Protocol.HealConfig) (st : Protocol.HealingStore V) (r : Round) :
    Protocol.get_sg_root_with (NamedProfile.gradeContract c) E hc st r
      = Protocol.anchor E hc st r (Protocol.readFrame c st r).g1 := rfl

/-- The grade-2 block a duty reads through the grade contract of the cache `c`, at the store `st`
    and round `r`, is the grade-2 candidate of the frame grade read of `c` at `st` and `r`. -/
theorem gradeContract_grade2_block_with (c : Protocol.Cache V) (E : Env V)
    (hc : Protocol.HealConfig) (st : Protocol.HealingStore V) (r : Round) :
    Protocol.grade2_block_with (NamedProfile.gradeContract c) E hc st r
      = (Protocol.frameGradeRead c E hc st r).Q2 := rfl

/-- The raw grade-2 field of the grade read through the grade contract of the cache `c`, at the
    store `st` and round `r`, holds exactly when the grade-2 result of the round-`r` frame read from
    `c` at `st` is a completed block. -/
theorem gradeContract_read_rawG2 (c : Protocol.Cache V) (E : Env V)
    (hc : Protocol.HealConfig) (st : Protocol.HealingStore V) (r : Round) :
    ((NamedProfile.gradeContract c).read E hc st r).rawG2
      = ((((Protocol.readFrame c st r).g2.bind id).isSome = true) : Prop) := rfl

/-- The anchor field of the grade read through the grade contract of the cache `c`, at the store
    `st` and round `r`, is `Protocol.anchor` at the grade-1 result of the round-`r` frame read from
    `c` at `st`. -/
theorem gradeContract_read_anchor (c : Protocol.Cache V) (E : Env V)
    (hc : Protocol.HealConfig) (st : Protocol.HealingStore V) (r : Round) :
    ((NamedProfile.gradeContract c).read E hc st r).anchor
      = Protocol.anchor E hc st r (Protocol.readFrame c st r).g1 := rfl

end DecoupledConsensusModel.Sts
