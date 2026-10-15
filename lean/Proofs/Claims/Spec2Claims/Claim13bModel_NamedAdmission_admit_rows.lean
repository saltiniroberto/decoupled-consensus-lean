module
public import Proofs.Claims.ModelIrreducible
public import Proofs.Claims.Spec2Claims.Claim13bModel_NamedAdmission_admit_row

@[expose] public section

/-!
# The admission of a list of named attestations

Facts about `NamedAdmission.admit_rows`: the bodies and Goldfish votes it leaves unchanged, and the
attestations it adds to the lists `sg_rows`.
-/

-- The definitions this file unfolds, made locally semireducible.
set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.NamedAdmission.admit_rows

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- Admitting a list of named attestations leaves the named bodies unchanged. -/
theorem admit_rows_bodies (hc : Protocol.HealConfig) :
    ∀ (rows : List (NamedAttestation V)) (st : NamedStore V),
      (NamedAdmission.admit_rows hc st rows).bodies = st.bodies
  | [], _ => rfl
  | a :: rows, st => by
      rw [NamedAdmission.admit_rows, List.foldl_cons,
        show rows.foldl (NamedAdmission.admit_row hc) (NamedAdmission.admit_row hc st a)
            = NamedAdmission.admit_rows hc (NamedAdmission.admit_row hc st a) rows from rfl,
        admit_rows_bodies hc rows, admit_row_bodies]

omit [Fintype V] in
/-- Admitting a list of named attestations leaves the Goldfish vote lists unchanged. -/
theorem admit_rows_gf_votes (hc : Protocol.HealConfig) :
    ∀ (rows : List (NamedAttestation V)) (st : NamedStore V),
      (NamedAdmission.admit_rows hc st rows).core.gf_votes = st.core.gf_votes
  | [], _ => rfl
  | a :: rows, st => by
      rw [NamedAdmission.admit_rows, List.foldl_cons,
        show rows.foldl (NamedAdmission.admit_row hc) (NamedAdmission.admit_row hc st a)
            = NamedAdmission.admit_rows hc (NamedAdmission.admit_row hc st a) rows from rfl,
        admit_rows_gf_votes hc rows, admit_row_gf_votes]

omit [Fintype V] in
/-- Admitting a list of named attestations only adds to the lists `sg_rows`. -/
theorem admit_rows_sg_rows_subset (hc : Protocol.HealConfig) (r : Round) :
    ∀ (rows : List (NamedAttestation V)) (st : NamedStore V),
      st.sg_rows r ⊆ (NamedAdmission.admit_rows hc st rows).sg_rows r
  | [], _ => fun _ h => h
  | a :: rows, st => by
      rw [NamedAdmission.admit_rows, List.foldl_cons,
        show rows.foldl (NamedAdmission.admit_row hc) (NamedAdmission.admit_row hc st a)
            = NamedAdmission.admit_rows hc (NamedAdmission.admit_row hc st a) rows from rfl]
      exact fun y hy =>
        admit_rows_sg_rows_subset hc r rows _ (admit_row_sg_rows_subset hc st a r hy)

omit [Fintype V] in
/-- Admitting a list `rows` of named attestations adds to the lists `sg_rows` only members of
    `rows`. -/
theorem mem_sg_rows_admit_rows (hc : HealConfig) (r : Round) :
    ∀ (rows : List (NamedAttestation V)) (st : NamedStore V) {y : NamedAttestation V},
      y ∈ (NamedAdmission.admit_rows hc st rows).sg_rows r → y ∈ st.sg_rows r ∨ y ∈ rows
  | [], _, _, h => Or.inl h
  | a :: rows, st, y, h => by
      rw [NamedAdmission.admit_rows, List.foldl_cons,
        show rows.foldl (NamedAdmission.admit_row hc) (NamedAdmission.admit_row hc st a)
            = NamedAdmission.admit_rows hc (NamedAdmission.admit_row hc st a) rows from rfl]
        at h
      rcases mem_sg_rows_admit_rows hc r rows _ h with h' | h'
      · rcases mem_sg_rows_admit_row hc st a r h' with h'' | h''
        · exact Or.inl h''
        · exact Or.inr (by rw [h'']; exact List.mem_cons_self)
      · exact Or.inr (List.mem_cons_of_mem _ h')

end DecoupledConsensusModel.Sts
