module
public import Model.Vocabulary.Protocol.Store
public import Proofs.Vocabulary.ModelVocabulary.Goldfish.Store
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# More facts about `Protocol.Store.tau`

The resolution stamp map `Protocol.Store.tau`, which stamps a vote with the later of its own receipt
stamp and its head block's.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.Store.tau
  DecoupledConsensusModel.Protocol.resolution_time DecoupledConsensusModel.occurrenceMax

set_option autoImplicit false


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- Two stores with the same block tree, block stamps and vote stamps have the same resolution
    stamps. -/
theorem tau_eq_of_fields {st st' : Protocol.Store V} (hT : st.T = st'.T)
    (hb : st.timestamp_block = st'.timestamp_block)
    (hv : st.timestamp_vote = st'.timestamp_vote) : st.tau = st'.tau := by
  unfold Protocol.Store.tau
  rw [hT, hb, hv]

/-- If the store stamps `u` with `τ` and the block `X` that `u`'s head resolves to with `σ`, and the
    slot of `X` is at most `u`'s, then the resolution stamp of `u` is the larger of `τ` and `σ`. -/
theorem tau_eq_max (st : Protocol.Store V) {u : GoldfishVote V} {X : Block V}
    (hX : Block.find? st.T u.head = some X) (hXs : X.slot ≤ u.slot)
    {τ σ : Stamp} (hτ : st.timestamp_vote u = some τ) (hσ : st.timestamp_block X = some σ) :
    st.tau u = some (max τ σ) := by
  simp only [Protocol.Store.tau, Protocol.resolution_time, hX, if_pos hXs, hτ, hσ,
    occurrenceMax]

end DecoupledConsensusModel.Sts
