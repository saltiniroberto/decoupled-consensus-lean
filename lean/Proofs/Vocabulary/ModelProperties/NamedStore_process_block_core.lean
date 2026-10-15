module
public import Model.Vocabulary.Protocol.Handlers

@[expose] public section

/-!
# Facts about `Protocol.NamedStore.process_block_core`

The named block core, one fact for each value of its test on the named parent.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

variable {V : Type} [DecidableEq V] [Fintype V]

/-- If the named parent of `B` is not among the bodies of `st`, the named block core returns `st`. -/
theorem process_block_core_of_parent_not_mem (E : Env V) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) {st : Protocol.NamedStore V} {B : NamedBlock V}
    (h : B.parent ∉ st.bodies) :
    Protocol.NamedStore.process_block_core E hc cfg st B = st := by
  unfold Protocol.NamedStore.process_block_core
  rw [if_pos h]

/-- If the named parent of `B` is among the bodies of `st`, the named block core returns the body
    commit of `B` over the store the checked block handler returns, which builds `B`'s chain state
    with `named_transition`. -/
theorem process_block_core_of_parent_mem (E : Env V) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) {st : Protocol.NamedStore V} {B : NamedBlock V}
    (h : B.parent ∈ st.bodies) :
    Protocol.NamedStore.process_block_core E hc cfg st B =
      Protocol.NamedStore.commitBlock st
        (Protocol.on_block_checked_using
          (fun current => Protocol.on_block_using E current B.erase
            (fun ps => Protocol.named_transition E cfg ps B)) hc st.core B.erase) B := by
  unfold Protocol.NamedStore.process_block_core
  rw [if_neg (not_not_intro h)]

end DecoupledConsensusModel.Proofs.ModelProperties

end
