import Model.Vocabulary.Protocol.Handlers
import Proofs.Claims.ModelIrreducible

/-!
# Facts about `Protocol.on_block_checked_using`

Further lemmas that unfold the receiver-side block wrapper.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.on_block_checked_using

set_option autoImplicit false


namespace DecoupledConsensusModel.Sts

variable {V : Type}

/-- If every attestation `B` includes is admissible, the checked block handler returns what `handle`
    returns on `st`. -/
theorem on_block_checked_using_eq_handle (handle : Protocol.Store V → Protocol.Store V)
    (hc : Protocol.HealConfig) (st : Protocol.Store V) {B : Block V}
    (h : Protocol.carried_attestations_admissible hc B = true) :
    Protocol.on_block_checked_using handle hc st B = handle st := by
  unfold Protocol.on_block_checked_using
  rw [if_pos h]

/-- If not every attestation `B` includes is admissible, the checked block handler returns `st`
    unchanged. -/
theorem on_block_checked_using_eq_self (handle : Protocol.Store V → Protocol.Store V)
    (hc : Protocol.HealConfig) (st : Protocol.Store V) {B : Block V}
    (h : ¬ Protocol.carried_attestations_admissible hc B = true) :
    Protocol.on_block_checked_using handle hc st B = st := by
  unfold Protocol.on_block_checked_using
  rw [if_neg h]

end DecoupledConsensusModel.Sts
