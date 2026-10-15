module
public import Proofs.Claims.ModelIrreducible
public import Proofs.Claims.Spec2Claims.Claim13bModel_NamedAdmission_admit_rows
public import Proofs.Claims.Spec2Claims.Claim13bModel_NamedStore_process_block_core

@[expose] public section

/-!
# What the named block handler adds

Facts about `NamedAdmission.on_block_with`: it only adds to the bodies, the Goldfish vote lists and
the lists `sg_rows`, and what it adds comes from the block it is handed.
-/

-- The definitions this file unfolds, made locally semireducible.
set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.NamedAdmission.on_block_with DecoupledConsensusModel.Protocol.NamedAdmission.admit_carried

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The named block handler either returns the store unchanged, or leaves `B` among its bodies. -/
theorem on_block_with_noop_or_mem (adm : CarriedAdmission) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (st : NamedStore V)
    (B : NamedBlock V) :
    NamedAdmission.on_block_with adm E hc cfg st B = st ∨
      B ∈ (NamedAdmission.on_block_with adm E hc cfg st B).bodies := by
  rw [NamedAdmission.on_block_with, NamedAdmission.admit_carried]
  split
  · rename_i hcond
    refine Or.inr ?_
    rw [admit_rows_bodies]
    exact hcond.2
  · rcases process_block_core_noop_or_mem E hc cfg st B with h | h
    · exact Or.inl h
    · exact Or.inr h

/-- The named block handler only adds to the named bodies. -/
theorem on_block_with_bodies_subset (adm : CarriedAdmission) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (st : NamedStore V)
    (B : NamedBlock V) :
    st.bodies ⊆ (NamedAdmission.on_block_with adm E hc cfg st B).bodies := by
  rw [NamedAdmission.on_block_with, NamedAdmission.admit_carried]
  split
  · rw [admit_rows_bodies]
    exact process_block_core_bodies_subset E hc cfg st B
  · exact process_block_core_bodies_subset E hc cfg st B

/-- The named block handler only adds to the Goldfish vote lists. -/
theorem on_block_with_gf_votes_subset (adm : CarriedAdmission) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (st : NamedStore V)
    (B : NamedBlock V) (k : Slot) :
    st.core.gf_votes k ⊆
      (NamedAdmission.on_block_with adm E hc cfg st B).core.gf_votes k := by
  rw [NamedAdmission.on_block_with, NamedAdmission.admit_carried]
  split
  · rw [admit_rows_gf_votes]
    exact process_block_core_gf_votes_subset E hc cfg st B k
  · exact process_block_core_gf_votes_subset E hc cfg st B k

/-- The named block handler only adds to the lists `sg_rows`. -/
theorem on_block_with_sg_rows_subset (adm : CarriedAdmission) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (st : NamedStore V)
    (B : NamedBlock V) (r : Round) :
    st.sg_rows r ⊆ (NamedAdmission.on_block_with adm E hc cfg st B).sg_rows r := by
  rw [NamedAdmission.on_block_with, NamedAdmission.admit_carried]
  split
  · intro y hy
    refine admit_rows_sg_rows_subset hc r B.attestations _ ?_
    rw [process_block_core_sg_rows]
    exact hy
  · rw [process_block_core_sg_rows]
    exact fun _ h => h

/-- The named block handler adds to the named bodies only the block it is handed. -/
theorem on_block_with_bodies_upper (adm : CarriedAdmission) (E : Env V) (hc : HealConfig)
    (cfg : HeightConfig) (st : NamedStore V) (B C : NamedBlock V) :
    C ∈ (NamedAdmission.on_block_with adm E hc cfg st B).bodies →
      C ∈ st.bodies ∨ C = B := by
  rw [NamedAdmission.on_block_with, NamedAdmission.admit_carried]
  split
  · rw [admit_rows_bodies]
    exact process_block_core_bodies_upper E hc cfg st B C
  · exact process_block_core_bodies_upper E hc cfg st B C

/-- The named block handler adds to the Goldfish vote lists only the Goldfish votes included in `B`,
    and only when `B` newly entered the block-core store's tree. -/
theorem on_block_with_gf_votes_upper (adm : CarriedAdmission) (E : Env V) (hc : HealConfig)
    (cfg : HeightConfig) (st : NamedStore V) (B : NamedBlock V) (k : Slot)
    (y : GoldfishVote V) :
    y ∈ (NamedAdmission.on_block_with adm E hc cfg st B).core.gf_votes k →
      y ∈ st.core.gf_votes k ∨
        (y ∈ B.gf_votes ∧ B.erase ∉ st.core.T ∧
          B.erase ∈ (NamedStore.process_block_core E hc cfg st B).core.T) := by
  rw [NamedAdmission.on_block_with, NamedAdmission.admit_carried]
  split
  · rw [admit_rows_gf_votes]
    exact process_block_core_gf_votes_upper E hc cfg st B k y
  · exact process_block_core_gf_votes_upper E hc cfg st B k y

/-- The named block handler adds to the lists `sg_rows` only the attestations included in `B`, and
    only when `B` newly entered the block-core store's bodies. -/
theorem on_block_with_sg_rows_upper (adm : CarriedAdmission) (E : Env V) (hc : HealConfig)
    (cfg : HeightConfig) (st : NamedStore V) (B : NamedBlock V) (r : Round)
    (y : NamedAttestation V) :
    y ∈ (NamedAdmission.on_block_with adm E hc cfg st B).sg_rows r →
      y ∈ st.sg_rows r ∨
        (y ∈ B.attestations ∧ B ∉ st.bodies ∧
          B ∈ (NamedStore.process_block_core E hc cfg st B).bodies) := by
  rw [NamedAdmission.on_block_with, NamedAdmission.admit_carried]
  split
  · rename_i hcond
    intro h
    rcases mem_sg_rows_admit_rows hc r B.attestations _ h with h' | h'
    · rw [process_block_core_sg_rows] at h'
      exact Or.inl h'
    · exact Or.inr ⟨h', hcond.1, hcond.2⟩
  · intro h
    rw [process_block_core_sg_rows] at h
    exact Or.inl h

end DecoupledConsensusModel.Sts
