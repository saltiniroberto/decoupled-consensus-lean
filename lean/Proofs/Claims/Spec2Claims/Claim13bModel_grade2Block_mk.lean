import Model.Vocabulary.Protocol.Grades
import Proofs.Claims.ModelIrreducible
import Proofs.Vocabulary.Objects.AttestationCanonicality
import Proofs.Claims.Spec2Claims.Claim13bModel_activePrefix

/-!
# Facts about `Protocol.grade2Block` against a fixed block

A lemma that unfolds `Protocol.grade2Block`: the grade-2 block a frame offers is compatible with
every block its grade-2 root is compatible with.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.grade2Block

set_option autoImplicit false


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- If every grade-2 root of the frame is compatible with `T`, then the grade-2 block the frame
    offers at `stH` is compatible with `T`. -/
theorem Q2_compatible {stH : Protocol.HealingStore V} {T : Block V} {frame : Protocol.Frame V}
    (hg2 : ∀ root : Block V, frame.g2 = some (some root) → Block.compatible root T = true)
    {Q : Block V} (hQ : Protocol.grade2Block stH frame = some Q) :
    Block.compatible Q T = true := by
  unfold Protocol.grade2Block at hQ
  split at hQ
  · cases hframe : frame.g2 with
    | none => rw [hframe] at hQ; simp at hQ
    | some o =>
        cases o with
        | none => rw [hframe] at hQ; simp at hQ
        | some root =>
            rw [hframe] at hQ
            simp only [Option.bind, id] at hQ
            exact Protocol.compatible_of_preceq_of_compatible
              (preceq_of_activePrefix_eq_some hQ) (hg2 root hframe)
  · exact absurd hQ (by simp)

end DecoupledConsensusModel.Sts
