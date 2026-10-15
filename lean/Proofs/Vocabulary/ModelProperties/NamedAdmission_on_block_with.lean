module
public import Proofs.Vocabulary.Protocol.Handlers.Admission
public import Proofs.Vocabulary.Protocol.Handlers.Invariants

@[expose] public section

/-!
# Facts about `Protocol.NamedAdmission.on_block_with`

The named block handler followed by the carried-row admission.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
private theorem admit_rows_core_F (hc : Protocol.HealConfig) (rows : List (NamedAttestation V)) :
    ∀ st : Protocol.NamedStore V,
      (Protocol.NamedAdmission.admit_rows hc st rows).core.F = st.core.F := by
  induction rows with
  | nil => intro st; rfl
  | cons row rows ih =>
    intro st
    change (Protocol.NamedAdmission.admit_rows hc
      (Protocol.NamedAdmission.admit_row hc st row) rows).core.F = st.core.F
    rw [ih, NamedAdmission.admit_row_core]
    exact on_sg_vote_F hc st.core row.erase

/-- The finalized block of the store `on_block_with` returns is that of the store
    `process_block_core` returns on the same arguments. -/
theorem on_block_with_core_F (admission : Protocol.CarriedAdmission) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig)
    (st : Protocol.NamedStore V) (B : NamedBlock V) :
    (Protocol.NamedAdmission.on_block_with admission E hc cfg st B).core.F =
      (Protocol.NamedStore.process_block_core E hc cfg st B).core.F := by
  cases admission with
  | alsoCarried =>
    unfold Protocol.NamedAdmission.on_block_with Protocol.NamedAdmission.admit_carried
    split_ifs
    · exact admit_rows_core_F hc _ _
    · rfl

end DecoupledConsensusModel.Proofs.ModelProperties

end
