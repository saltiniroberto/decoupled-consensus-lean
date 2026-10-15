module
public import Model.Vocabulary.Protocol.Handlers
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# The admission of named attestations

Facts about `NamedAdmission.admit_row`, the admission of one named attestation, and
`NamedAdmission.admit_rows`, the admission of a list of them.
-/

-- The definitions this file unfolds, made locally semireducible.
set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.NamedAdmission.admit_row
  DecoupledConsensusModel.Protocol.NamedAdmission.admit_rows

set_option autoImplicit false


namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V]

/-- Admitting a named attestation runs `on_sg_vote` on the core store with the attestation's
    erasure. -/
theorem admit_row_core' (hc : HealConfig) (st : NamedStore V) (row : NamedAttestation V) :
    (NamedAdmission.admit_row hc st row).core = on_sg_vote hc st.core row.erase := by
  dsimp only [NamedAdmission.admit_row]
  split <;> rfl

/-- Admitting a named attestation keeps the held bodies. -/
theorem admit_row_bodies' (hc : HealConfig) (st : NamedStore V) (row : NamedAttestation V) :
    (NamedAdmission.admit_row hc st row).bodies = st.bodies := by
  dsimp only [NamedAdmission.admit_row]
  split <;> rfl

/-- Admitting a named attestation keeps every attestation already in the lists `sg_rows`. -/
theorem sg_rows_admit_row_mono (hc : HealConfig) (st : NamedStore V) (row : NamedAttestation V)
    (r : Round) {y : NamedAttestation V} (h : y ∈ st.sg_rows r) :
    y ∈ (NamedAdmission.admit_row hc st row).sg_rows r := by
  dsimp only [NamedAdmission.admit_row]
  split
  · show y ∈ (if r = row.round then st.sg_rows r ++ [row] else st.sg_rows r)
    split
    · exact List.mem_append_left _ h
    · exact h
  · exact h

/-- Unless the erasure of `row` was not in the core store's pool for `row`'s round and is in the
    pool of the store `on_sg_vote` returns, admitting `row` keeps the lists `sg_rows` of `st`. -/
theorem admit_row_sg_rows_of_not_new (hc : HealConfig) (st : NamedStore V)
    (row : NamedAttestation V)
    (h : ¬ (row.erase ∉ st.core.sg_pool row.round ∧
      row.erase ∈ (on_sg_vote hc st.core row.erase).sg_pool row.round)) :
    (NamedAdmission.admit_row hc st row).sg_rows = st.sg_rows := by
  dsimp only [NamedAdmission.admit_row]
  rw [if_neg h]

/-- When the erasure of `row` was not in the core store's pool for `row`'s round and is in the pool
    of the store `on_sg_vote` returns, admitting `row` appends `row` to the list `sg_rows` of
    `row`'s round and keeps the other rounds' lists. -/
theorem admit_row_sg_rows_of_new (hc : HealConfig) (st : NamedStore V) (row : NamedAttestation V)
    (h : row.erase ∉ st.core.sg_pool row.round ∧
      row.erase ∈ (on_sg_vote hc st.core row.erase).sg_pool row.round) :
    (NamedAdmission.admit_row hc st row).sg_rows =
      fun r => if r = row.round then st.sg_rows r ++ [row] else st.sg_rows r := by
  dsimp only [NamedAdmission.admit_row]
  rw [if_pos h]

/-- Admitting the empty list of named attestations returns `st`. -/
theorem admit_rows_nil (hc : HealConfig) (st : NamedStore V) :
    NamedAdmission.admit_rows hc st [] = st := rfl

/-- Admitting the list `a :: rows` is admitting `a`, then admitting `rows` into the store that
    admission returns. -/
theorem admit_rows_cons (hc : HealConfig) (st : NamedStore V) (a : NamedAttestation V)
    (rows : List (NamedAttestation V)) :
    NamedAdmission.admit_rows hc st (a :: rows) =
      NamedAdmission.admit_rows hc (NamedAdmission.admit_row hc st a) rows := rfl

end DecoupledConsensusModel.Sts
