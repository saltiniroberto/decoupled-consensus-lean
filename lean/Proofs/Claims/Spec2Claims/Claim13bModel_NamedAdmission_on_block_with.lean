import Proofs.Vocabulary.Protocol.Handlers.Blocks
import Proofs.Claims.ModelIrreducible
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedAdmission_admit_carried

/-!
# The named block handler

Facts about `Protocol.NamedAdmission.on_block_with`, the named block core
`Protocol.NamedStore.process_block_core` followed by the admission of the block's attestations
`Protocol.NamedAdmission.admit_carried`.
-/

-- The definitions this file unfolds, made locally semireducible.
set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.NamedAdmission.admit_carried
  DecoupledConsensusModel.Protocol.NamedAdmission.on_block_with
  DecoupledConsensusModel.Protocol.NamedStore.process_block_core

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- A named block `D` among the bodies of the store the named block core returns on `st` and `B` is
    among the bodies of the store the named block handler returns on `st` and `B`, whatever the
    admission mode. -/
theorem mem_on_block_with_bodies_of_mem_core (admission : Protocol.CarriedAdmission) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (st : Protocol.NamedStore V)
    (B : NamedBlock V) {D : NamedBlock V}
    (hD : D ∈ (Protocol.NamedStore.process_block_core E hc cfg st B).bodies) :
    D ∈ (Protocol.NamedAdmission.on_block_with admission E hc cfg st B).bodies := by
  unfold Protocol.NamedAdmission.on_block_with Protocol.NamedAdmission.admit_carried
  split
  · rw [(Protocol.admit_rows_bodies_and_core_T hc B.attestations
      (Protocol.NamedStore.process_block_core E hc cfg st B)).1]
    exact hD
  · exact hD

end DecoupledConsensusModel.Sts

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The store `on_block_with` returns is either the store obtained by admitting `B`'s attestations
    one by one into the store the named block core returns, or that block-core store itself. -/
theorem on_block_with_cases (admission : Protocol.CarriedAdmission) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (st : Protocol.NamedStore V)
    (B : NamedBlock V) :
    Protocol.NamedAdmission.on_block_with admission E hc cfg st B =
        Protocol.NamedAdmission.admit_rows hc (Protocol.NamedStore.process_block_core E hc cfg st B)
          B.attestations ∨
      Protocol.NamedAdmission.on_block_with admission E hc cfg st B =
        Protocol.NamedStore.process_block_core E hc cfg st B := by
  unfold Protocol.NamedAdmission.on_block_with
  exact admit_carried_cases admission hc st _ B

end DecoupledConsensusModel.Sts

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- When `B` was not among the bodies of `st` and is among the bodies of the store the named block
    core returns, the named block handler returns the admission of `B`'s attestations into that
    store. -/
theorem on_block_with_of_new (admission : Protocol.CarriedAdmission) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (st : Protocol.NamedStore V)
    (B : NamedBlock V) (h0 : B ∉ st.bodies)
    (h1 : B ∈ (Protocol.NamedStore.process_block_core E hc cfg st B).bodies) :
    Protocol.NamedAdmission.on_block_with admission E hc cfg st B =
      Protocol.NamedAdmission.admit_rows hc
        (Protocol.NamedStore.process_block_core E hc cfg st B) B.attestations := by
  unfold Protocol.NamedAdmission.on_block_with Protocol.NamedAdmission.admit_carried
  rw [if_pos ⟨h0, h1⟩]

/-- Unless `B` was not among the bodies of `st` and is among the bodies of the store the named block
    core returns, the named block handler returns that store. -/
theorem on_block_with_of_not_new (admission : Protocol.CarriedAdmission) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (st : Protocol.NamedStore V)
    (B : NamedBlock V)
    (h : ¬ (B ∉ st.bodies ∧ B ∈ (Protocol.NamedStore.process_block_core E hc cfg st B).bodies)) :
    Protocol.NamedAdmission.on_block_with admission E hc cfg st B =
      Protocol.NamedStore.process_block_core E hc cfg st B := by
  unfold Protocol.NamedAdmission.on_block_with Protocol.NamedAdmission.admit_carried
  rw [if_neg h]

end DecoupledConsensusModel.Sts
