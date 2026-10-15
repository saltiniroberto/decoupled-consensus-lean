module

public import Model.Vocabulary.Protocol.Handlers
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# Facts about `Protocol.round_votes`

Lemmas that unfold the confirmed heads the store's attestation pool of a round holds for one
validator.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.round_votes

set_option autoImplicit false


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- `o` is in `Protocol.round_votes st a` exactly when some attestation of the store's pool of `a`'s
    round is signed by `a`'s validator and confirms `o`. -/
theorem mem_round_votes_iff (st : Protocol.Store V) (a : CombinedAttestation V)
    (o : Option BlockId) :
    o ∈ Protocol.round_votes st a ↔
      ∃ b ∈ st.sg_pool a.round, b.val_index = a.val_index ∧ b.confirmed = o := by
  unfold Protocol.round_votes
  constructor
  · intro h
    obtain ⟨b, hb, hbo⟩ := Finset.mem_image.mp h
    obtain ⟨hbp, hbi⟩ := Finset.mem_filter.mp hb
    exact ⟨b, hbp, hbi, hbo⟩
  · rintro ⟨b, hbp, hbi, hbo⟩
    exact Finset.mem_image.mpr ⟨b, Finset.mem_filter.mpr ⟨hbp, hbi⟩, hbo⟩

end DecoupledConsensusModel.Sts

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

end DecoupledConsensusModel.Sts

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- If the store's pool of `a`'s round holds `a`, then `a`'s confirmed head is in
    `Protocol.round_votes st a`. -/
theorem mem_round_votes_of_mem_sg_pool (st : Protocol.Store V) (a : CombinedAttestation V)
    (h : a ∈ st.sg_pool a.round) : a.confirmed ∈ Protocol.round_votes st a := by
  unfold Protocol.round_votes
  exact Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨h, rfl⟩)

end DecoupledConsensusModel.Sts
