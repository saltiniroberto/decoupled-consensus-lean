module
public import Model.Vocabulary.Protocol.Handlers
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# The two cases of the named block handler

`Protocol.NamedAdmission.on_block_with` admits the block's attestations after the block core when
the block is new to the bodies, and returns the block core's store otherwise.
-/

-- The definitions this file unfolds, made locally semireducible.
set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.NamedAdmission.on_block_with
  DecoupledConsensusModel.Protocol.NamedAdmission.admit_carried

set_option autoImplicit false


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- If `B` is not among `st`'s bodies and is among the bodies of the store the named block core
    returns, then the named block handler on `B` returns the admission of `B`'s attestations into
    that store. -/
theorem on_block_with_of_new' (adm : Protocol.CarriedAdmission) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (st : Protocol.NamedStore V)
    (B : NamedBlock V)
    (h : B ∉ st.bodies ∧ B ∈ (Protocol.NamedStore.process_block_core E hc cfg st B).bodies) :
    Protocol.NamedAdmission.on_block_with adm E hc cfg st B
      = Protocol.NamedAdmission.admit_rows hc
          (Protocol.NamedStore.process_block_core E hc cfg st B) B.attestations := by
  unfold Protocol.NamedAdmission.on_block_with Protocol.NamedAdmission.admit_carried
  rw [if_pos h]

/-- Unless `B` is new to `st`'s bodies and among the bodies of the store the named block core
    returns, the named block handler on `B` returns that store. -/
theorem on_block_with_of_not_new' (adm : Protocol.CarriedAdmission) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (st : Protocol.NamedStore V)
    (B : NamedBlock V)
    (h : ¬ (B ∉ st.bodies ∧ B ∈ (Protocol.NamedStore.process_block_core E hc cfg st B).bodies)) :
    Protocol.NamedAdmission.on_block_with adm E hc cfg st B
      = Protocol.NamedStore.process_block_core E hc cfg st B := by
  unfold Protocol.NamedAdmission.on_block_with Protocol.NamedAdmission.admit_carried
  rw [if_neg h]

end DecoupledConsensusModel.Sts
