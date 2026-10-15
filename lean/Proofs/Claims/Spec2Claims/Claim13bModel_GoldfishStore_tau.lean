import Proofs.Vocabulary.ModelVocabulary.Goldfish.Store
import Proofs.Claims.ModelIrreducible

/-!
# Resolved stamps of Goldfish votes

A condition under which a Goldfish vote is stamped before a cutoff under the store's resolved vote
stamps `gs.tau`.
-/

-- The definitions this file unfolds, made locally semireducible.
set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.GoldfishStore.tau

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- If the head of the Goldfish vote `u` is found in the tree of the Goldfish store `gs` as the
    block `H`, the slot of `H` is at most the slot of `u`, `u` is stamped before the cutoff `Γ`
    under the store's vote stamps, and `H` is stamped before `Γ` under the store's block stamps,
    then `u` is stamped before `Γ` under the store's resolved vote stamps `gs.tau`. -/
theorem stampedBefore_tau_of (gs : Protocol.GoldfishStore V) {Γ : Time} {u : GoldfishVote V}
    {H : Block V} (hfind : Block.find? gs.T u.head = some H) (hslot : H.slot ≤ u.slot)
    (hv : stampedBefore gs.timestamp_vote Γ u = true)
    (hH : stampedBefore gs.timestamp_block Γ H = true) :
    stampedBefore gs.tau Γ u = true :=
  Protocol.stampedBefore_resolution_of hfind hslot hv hH

end DecoupledConsensusModel.Sts
