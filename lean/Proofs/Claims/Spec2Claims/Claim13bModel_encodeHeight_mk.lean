module
public import Model.Vocabulary.Protocol.ValidatorClient
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# The fields behind a named height vote

The codec `Protocol.NamedRecord.encodeHeight` returns a named height vote only from the fields it is
given.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.NamedRecord.encodeHeight

set_option autoImplicit false


namespace DecoupledConsensusModel.Sts

/-- If the codec returns a height vote for height `h₀` and root `entry`, then its fields were
    `some (h₀, entry, b)` for some Boolean `b`. -/
theorem fields_of_encodeHeight_vote (fields : Option (Height × BlockId × Bool))
    (pair : HeightPair) {h₀ : Height} {entry : BlockId} {tmo : Bool}
    (h : Protocol.NamedRecord.encodeHeight fields pair = NamedHeightPair.vote h₀ entry tmo) :
    ∃ b : Bool, fields = some (h₀, entry, b) := by
  unfold Protocol.NamedRecord.encodeHeight at h
  split at h
  · exact absurd h (by simp)
  · exact ⟨_, by injection h with e1 e2 _; rw [e1, e2]⟩
  · exact ⟨_, by injection h with e1 e2 _; rw [e1, e2]⟩
  · exact absurd h (by simp)

end DecoupledConsensusModel.Sts
