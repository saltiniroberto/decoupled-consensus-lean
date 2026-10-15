import Model.Vocabulary.Protocol.Grades
import Proofs.Claims.Spec2Claims.Claim13bModel_clipGrade

/-!
# Facts about `Protocol.clipResult`

The clip of a phase result against a finalized block: a completed phase stays completed, and its
root, if any, is clipped by `Protocol.clipGrade`.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.clipResult

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- Clipping at `F` a completed phase result whose root is already clipped at `F` returns it
    unchanged. -/
theorem clipResult_some_map_clipGrade (F : Block V) (o : Option (Block V)) :
    Protocol.clipResult F (some (o.map (fun B => Protocol.clipGrade B F)))
      = some (o.map (fun B => Protocol.clipGrade B F)) := by
  cases o with
  | none => rfl
  | some B =>
      unfold Protocol.clipResult
      simp only [Option.map_some, clipGrade_clipGrade]

end DecoupledConsensusModel.Sts
