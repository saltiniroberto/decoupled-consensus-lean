module
public import Proofs.Vocabulary.ModelVocabulary.Goldfish.Store
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# The resolved stamp of a Goldfish vote

The resolved stamp `gs.tau u` of a vote is the larger of the vote's stamp and its head block's
stamp, when the head block's slot is at or before the vote's.
-/

-- The definitions this file unfolds, made locally semireducible.
set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.GoldfishStore.tau
  DecoupledConsensusModel.Protocol.resolution_time DecoupledConsensusModel.occurrenceMax

set_option autoImplicit false


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- If a Goldfish store stamps `u` with `τ` and the block `X` that `u`'s head resolves to with `σ`,
    and `X` is of a slot at or before `u`'s, then `gs.tau u` is `max τ σ`. -/
theorem tau_eq_max_gf (gs : Protocol.GoldfishStore V) {u : GoldfishVote V} {X : Block V}
    (hX : Block.find? gs.T u.head = some X) (hXs : X.slot ≤ u.slot)
    {τ σ : Stamp} (hτ : gs.timestamp_vote u = some τ) (hσ : gs.timestamp_block X = some σ) :
    gs.tau u = some (max τ σ) := by
  simp only [Protocol.GoldfishStore.tau, Protocol.resolution_time, hX, if_pos hXs, hτ, hσ,
    occurrenceMax]

end DecoupledConsensusModel.Sts
