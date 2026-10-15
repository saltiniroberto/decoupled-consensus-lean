import Model.Vocabulary.Protocol.ValidatorClient
import Proofs.Claims.ModelIrreducible

/-!
# Facts about `Protocol.NamedRecord.encodeHeight`

The codec that writes a height pair as a named height pair.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.NamedRecord.encodeHeight

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

/-- Whatever `fields`, the codec writes the empty height pair as the empty named height pair. -/
theorem encodeHeight_empty (fields : Option (Height × BlockId × Bool)) :
    Protocol.NamedRecord.encodeHeight fields HeightPair.empty = NamedHeightPair.empty := by
  unfold Protocol.NamedRecord.encodeHeight
  cases fields <;> rfl

end DecoupledConsensusModel.Sts

namespace DecoupledConsensusModel.Sts

/-- The codec at fields `(h, e, ν)` gives a vote at `(H, e')` only when `h = H` and `e = e'`. -/
theorem encodeHeight_vote_inv_l85c {h H : Height} {e e' : BlockId} {ν b : Bool}
    {p : HeightPair}
    (hp : Protocol.NamedRecord.encodeHeight (some (h, e, ν)) p = .vote H e' b) :
    h = H ∧ e = e' := by
  cases p with
  | empty => simp [Protocol.NamedRecord.encodeHeight] at hp
  | timeout g =>
    simp only [Protocol.NamedRecord.encodeHeight, NamedHeightPair.vote.injEq] at hp
    exact ⟨hp.1, hp.2.1⟩
  | target g X =>
    simp only [Protocol.NamedRecord.encodeHeight, NamedHeightPair.vote.injEq] at hp
    exact ⟨hp.1, hp.2.1⟩

end DecoupledConsensusModel.Sts
