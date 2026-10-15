module
public import Model.Vocabulary.Protocol.Handlers

@[expose] public section

/-!
# Facts about `Protocol.on_block_checked_using`

The block handler behind the carried-round test, one fact for each outcome of the test.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

variable {V : Type} [DecidableEq V]

/-- If the carried attestations of `B` are admissible, the checked handler returns what `handle`
    returns on `st`. -/
theorem on_block_checked_using_of_admissible (handle : Protocol.Store V → Protocol.Store V)
    (hc : Protocol.HealConfig) (st : Protocol.Store V) {B : Block V}
    (h : Protocol.carried_attestations_admissible hc B = true) :
    Protocol.on_block_checked_using handle hc st B = handle st := by
  unfold Protocol.on_block_checked_using
  rw [if_pos h]

/-- If the carried attestations of `B` are not admissible, the checked handler returns `st`. -/
theorem on_block_checked_using_of_not_admissible (handle : Protocol.Store V → Protocol.Store V)
    (hc : Protocol.HealConfig) (st : Protocol.Store V) {B : Block V}
    (h : ¬ Protocol.carried_attestations_admissible hc B = true) :
    Protocol.on_block_checked_using handle hc st B = st := by
  unfold Protocol.on_block_checked_using
  rw [if_neg h]

end DecoupledConsensusModel.Proofs.ModelProperties

end
