import Proofs.Vocabulary.Protocol.Handlers.AdoptionConstructor
import Proofs.Claims.ModelIrreducible
import Proofs.Vocabulary.ModelVocabulary.Goldfish.Store

/-!
# Facts about `Protocol.Store.tau`

The stamps of the store's Goldfish votes, resolved against its block tree.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.Store.tau

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- If the head of `u` is found in the tree of `st` as `H`, and `u` is stamped before `Γ` under
    `st.tau`, then `H` is stamped before `Γ` under the store's block stamps. -/
theorem stampedBefore_block_of_tau (st : Protocol.Store V) {Γ : Time} {u : GoldfishVote V}
    {H : Block V} (hfind : Block.find? st.T u.head = some H)
    (h : stampedBefore st.tau Γ u = true) :
    stampedBefore st.timestamp_block Γ H = true :=
  Protocol.HonestWeightMajority.stampedBefore_block_of_resolution hfind h

/-- If the head of `u` is found in the tree of `st` as `H`, and `u` is stamped before `Γ` under
    `st.tau`, then the slot of `H` is at most the slot of `u`. -/
theorem head_slot_le_of_tau (st : Protocol.Store V) {Γ : Time} {u : GoldfishVote V}
    {H : Block V} (hfind : Block.find? st.T u.head = some H)
    (h : stampedBefore st.tau Γ u = true) :
    H.slot ≤ u.slot :=
  Protocol.head_slot_le_of_resolution_time hfind h

/-- If `u` is stamped before `Γ` under `st.tau`, then `u` is stamped before `Γ` under
    `st.timestamp_vote`. -/
theorem stampedBefore_vote_of_tau (st : Protocol.Store V) {Γ : Time} {u : GoldfishVote V}
    (h : stampedBefore st.tau Γ u = true) :
    stampedBefore st.timestamp_vote Γ u = true :=
  Protocol.stampedBefore_of_resolution h

end DecoupledConsensusModel.Sts

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- If the head of `u` is found in the tree of `st` as `H`, the slot of `H` is at most `u`'s, and
    both `u` and `H` are stamped before `Γ`, then `u` is stamped before `Γ` under `st.tau`. -/
theorem stampedBefore_store_tau_of (st : Protocol.Store V) {Γ : Time} {u : GoldfishVote V}
    {H : Block V} (hfind : Block.find? st.T u.head = some H) (hslot : H.slot ≤ u.slot)
    (hv : stampedBefore st.timestamp_vote Γ u = true)
    (hH : stampedBefore st.timestamp_block Γ H = true) :
    stampedBefore st.tau Γ u = true :=
  Protocol.stampedBefore_resolution_of hfind hslot hv hH

end DecoupledConsensusModel.Sts
