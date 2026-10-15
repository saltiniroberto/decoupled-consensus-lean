import Model.Vocabulary.Protocol.StoreBase
import Proofs.Claims.ModelIrreducible

/-!
# The pool of a Goldfish store

A vote is in a Goldfish store's pool of a slot exactly when it is among the store's Goldfish votes
of that slot.
-/

-- The definitions this file unfolds, made locally semireducible.
set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.GoldfishStore.pool

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- The Goldfish vote `u` is in the slot-`s` pool of the Goldfish store `gs` if and only if `u` is
    among `gs`'s slot-`s` Goldfish votes. -/
theorem mem_goldfishStore_pool_iff (gs : Protocol.GoldfishStore V) (s : Slot)
    (u : GoldfishVote V) :
    u ∈ gs.pool s ↔ u ∈ gs.gf_votes s := by
  unfold Protocol.GoldfishStore.pool
  exact List.mem_toFinset

end DecoupledConsensusModel.Sts
