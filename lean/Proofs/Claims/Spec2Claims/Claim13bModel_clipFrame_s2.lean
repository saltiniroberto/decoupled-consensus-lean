import Model.Vocabulary.Protocol.Grades
import Proofs.Claims.Spec2Claims.Claim13bModel_clipGrade

/-!
# Facts about `Protocol.clipFrame`

The phase results of a frame clipped against a finalized block.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.clipFrame
  DecoupledConsensusModel.Protocol.clipResult DecoupledConsensusModel.Protocol.phaseResult

set_option autoImplicit false


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- If the frame clipped to `F` holds the root `root` for the phase `p`, then the unclipped frame
    holds there a root of which `root` is an ancestor. -/
theorem phaseResult_clipFrame {F : Block V} {f : Protocol.Frame V} {p : Protocol.Phase}
    {root : Block V}
    (h : Protocol.phaseResult (Protocol.clipFrame F f) p = some (some root)) :
    ∃ root₀ : Block V, Protocol.phaseResult f p = some (some root₀) ∧
      Block.Preceq root root₀ := by
  cases p <;>
  · simp only [Protocol.phaseResult, Protocol.clipFrame, Protocol.clipResult] at h ⊢
    obtain ⟨o, ho, hmap⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨B, hB, rfl⟩ := Option.map_eq_some_iff.1 hmap
    subst hB
    exact ⟨B, ho, clipGrade_preceq_self B F⟩

end DecoupledConsensusModel.Sts
