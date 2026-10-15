module
public import Proofs.Claims.ModelIrreducible
public import Proofs.Claims.Spec2Claims.Claim13bModel_on_sg_vote_mk

@[expose] public section

/-!
# The admission of one named attestation

Facts about `NamedAdmission.admit_row`: the bodies and Goldfish votes it leaves unchanged, and the
attestation rows it adds.
-/

-- The definitions this file unfolds, made locally semireducible.
set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.NamedAttestation.erase
  DecoupledConsensusModel.Protocol.NamedAdmission.admit_row

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- Admitting one named attestation leaves the named bodies unchanged. -/
theorem admit_row_bodies (hc : Protocol.HealConfig) (st : NamedStore V)
    (a : NamedAttestation V) :
    (NamedAdmission.admit_row hc st a).bodies = st.bodies := by
  simp only [NamedAdmission.admit_row]; split <;> rfl

omit [Fintype V] in
/-- Admitting one named attestation leaves the Goldfish vote lists unchanged. -/
theorem admit_row_gf_votes (hc : Protocol.HealConfig) (st : NamedStore V)
    (a : NamedAttestation V) :
    (NamedAdmission.admit_row hc st a).core.gf_votes = st.core.gf_votes := by
  simp only [NamedAdmission.admit_row]
  split <;> exact on_sg_vote_gf_votes hc st.core a.erase

omit [Fintype V] in
/-- Admitting one named attestation only adds to the named attestation lists `sg_rows`. -/
theorem admit_row_sg_rows_subset (hc : Protocol.HealConfig) (st : NamedStore V)
    (a : NamedAttestation V) (r : Round) :
    st.sg_rows r ⊆ (NamedAdmission.admit_row hc st a).sg_rows r := by
  simp only [NamedAdmission.admit_row]
  split
  · intro y hy
    by_cases hr : r = a.round
    · simp only [hr]
      exact List.mem_append_left _ (by rw [← hr]; exact hy)
    · simpa [hr] using hy
  · exact fun _ h => h

omit [Fintype V] in
/-- Admitting the named attestation `a` either returns the store unchanged, or leaves `a` in the
    store's list `sg_rows` of `a`'s round. -/
theorem admit_row_noop_or_mem (hc : Protocol.HealConfig) (st : NamedStore V)
    (a : NamedAttestation V) :
    NamedAdmission.admit_row hc st a = st ∨
      a ∈ (NamedAdmission.admit_row hc st a).sg_rows a.round := by
  by_cases hcond : a.erase ∉ st.core.sg_pool a.round ∧
      a.erase ∈ (on_sg_vote hc st.core a.erase).sg_pool a.round
  · refine Or.inr ?_
    rw [NamedAdmission.admit_row, if_pos hcond]
    show a ∈ (if a.round = a.round then st.sg_rows a.round ++ [a] else st.sg_rows a.round)
    rw [if_pos rfl]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  · refine Or.inl ?_
    have hafter : on_sg_vote hc st.core a.erase = st.core := by
      by_cases hmem : a.erase ∈ st.core.sg_pool a.round
      · exact on_sg_vote_eq_of_mem hc st.core a.erase hmem
      · rcases on_sg_vote_noop_or_mem hc st.core a.erase with h | h
        · exact h
        · exact absurd ⟨hmem, h⟩ hcond
    rw [NamedAdmission.admit_row, if_neg hcond, hafter]

omit [Fintype V] in
/-- Admitting the named attestation `a` adds no attestation other than `a` to the lists `sg_rows`. -/
theorem mem_sg_rows_admit_row (hc : HealConfig) (st : NamedStore V) (a : NamedAttestation V)
    (r : Round) {y : NamedAttestation V}
    (h : y ∈ (NamedAdmission.admit_row hc st a).sg_rows r) :
    y ∈ st.sg_rows r ∨ y = a := by
  simp only [NamedAdmission.admit_row] at h
  split at h
  · have h' : y ∈ (if r = a.round then st.sg_rows r ++ [a] else st.sg_rows r) := h
    by_cases hr : r = a.round
    · rw [if_pos hr] at h'
      rcases List.mem_append.1 h' with hy | hy
      · exact Or.inl hy
      · exact Or.inr (List.mem_singleton.1 hy)
    · rw [if_neg hr] at h'
      exact Or.inl h'
  · exact Or.inl h

end DecoupledConsensusModel.Sts
