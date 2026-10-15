module
public import Model.Vocabulary.Protocol.Handlers

@[expose] public section

/-!
# Facts about `Protocol.NamedStore.initial`

The initial named store and the fields of its core store.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

variable {V : Type} [DecidableEq V]

/-- The clock of the initial named store's core store is `0`. -/
theorem initial_core_t : (Protocol.NamedStore.initial : Protocol.NamedStore V).core.t = 0 := rfl

/-- The slot of the initial named store's core store is `0`. -/
theorem initial_core_s : (Protocol.NamedStore.initial : Protocol.NamedStore V).core.s = 0 := rfl

/-- The initial named store holds no SG row of any round. -/
theorem initial_sg_rows (r : Round) :
    (Protocol.NamedStore.initial : Protocol.NamedStore V).sg_rows r = [] := rfl

/-- The chain-state map of the initial named store's core store sends every block to the initial
    chain state. -/
theorem initial_core_σ :
    (Protocol.NamedStore.initial : Protocol.NamedStore V).core.σ =
      fun _ => Protocol.ChainState.initial := rfl

/-- In the initial named store's core store, `h_j < h_max`. -/
theorem initial_core_h_j_lt_h_max :
    (Protocol.NamedStore.initial : Protocol.NamedStore V).core.h_j <
      (Protocol.NamedStore.initial : Protocol.NamedStore V).core.h_max := Nat.zero_lt_one

/-- The block tree of the initial named store's core store holds the genesis block alone. -/
theorem initial_core_T :
    (Protocol.NamedStore.initial : Protocol.NamedStore V).core.T = {Block.genesis} := rfl

/-- The finalized block of the initial named store's core store is genesis. -/
theorem initial_core_F :
    (Protocol.NamedStore.initial : Protocol.NamedStore V).core.F = Block.genesis := rfl

/-- The justified block of the initial named store's core store is genesis. -/
theorem initial_core_J :
    (Protocol.NamedStore.initial : Protocol.NamedStore V).core.J = Block.genesis := rfl

/-- The `h_max` of the initial named store's core store is `1`. -/
theorem initial_core_h_max :
    (Protocol.NamedStore.initial : Protocol.NamedStore V).core.h_max = 1 := rfl

/-- The core store of the initial named store is `Store.init`. -/
theorem initial_core :
    (Protocol.NamedStore.initial : Protocol.NamedStore V).core = Protocol.Store.init := rfl

/-- The bodies of the initial named store are the named genesis block alone. -/
theorem initial_bodies :
    (Protocol.NamedStore.initial : Protocol.NamedStore V).bodies = {NamedBlock.genesis} := rfl

/-- The justified height of the initial named store's core store is `0`. -/
theorem initial_core_h_j :
    (Protocol.NamedStore.initial : Protocol.NamedStore V).core.h_j = 0 := rfl

/-- The Goldfish pool of the initial named store's core store is empty at every slot. -/
theorem initial_core_not_mem_pool (k : Slot) (u : GoldfishVote V) :
    u ∉ (Protocol.NamedStore.initial : Protocol.NamedStore V).core.pool k := by
  simp [Protocol.Store.pool, Protocol.NamedStore.initial, Protocol.Store.init]

/-- The SG pool of the initial named store's core store is empty at every round. -/
theorem initial_core_not_mem_sg_pool (r : Round) (a : CombinedAttestation V) :
    a ∉ (Protocol.NamedStore.initial : Protocol.NamedStore V).core.sg_pool r := by
  simp [Protocol.Store.sg_pool, Protocol.NamedStore.initial, Protocol.Store.init]

/-- In the initial named store's core store, every block's chain-state height is at most `h_max`. -/
theorem initial_core_σ_h_le_h_max (B : Block V) :
    ((Protocol.NamedStore.initial : Protocol.NamedStore V).core.σ B).h ≤
      (Protocol.NamedStore.initial : Protocol.NamedStore V).core.h_max := le_refl _

end DecoupledConsensusModel.Proofs.ModelProperties

end
