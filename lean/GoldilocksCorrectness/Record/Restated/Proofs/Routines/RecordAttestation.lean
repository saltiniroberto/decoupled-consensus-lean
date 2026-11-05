module
public import GoldilocksCorrectness.Record.Facts
public import GoldilocksCorrectness.Proofs.Routines.Record

@[expose] public section

/-!
# The attestation the validator client builds and records, over a model

The theorems of `GoldilocksCorrectness/Proofs/Routines/Record.lean` on `create_attestation` and
`record_attestation` that execution proofs call, over a model `M`, with the client's answer read as
`AttestationFrom M n v h_c T_c h_j J h_F a` (the attestation `a` the validator client of the node
state `n` builds) and the record it writes as `AttestationRecorded M n a n'` (the anti-slashing
record of `n'` is `n`'s with `a` written into it): a timeout is at the source's height and is cast
only over a timeout or another target there, a lock of the written record is the old one or at the
justification height, and the contents sent grow by `a`'s content.

The recovery section at the end of the page states each landed theorem again at the record of a
node state `n.Λ`, and proves it from its record form at the spec's model `Model.goldilocks`: the
spec's client builds `a` exactly when `AttestationFrom` holds
(`create_attestation_snd_eq_some_iff`), and returns the record with `a` written into it
(`create_attestation_fst_of_some`, `attestationRecorded_of_record`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Record
open GoldilocksCorrectness.Record.Statements.Routines (AttestationFrom AttestationRecorded)

variable {V : Type} [DecidableEq V] [Fintype V]

/-- A timeout the validator client of `n` builds is at the source's height `h_c`, names `T_c`, and
is built only when `n`'s record holds a timeout at `h_c`, or a target at `h_c` for a block other
than `T_c`.

The variables:
- `M`: the model; `F`: its facts;
- `n`: the node state; `v`: the validator; `h_c`, `T_c`: the source's height and root;
- `h_j`, `J`, `h_F`: the head's justification height, justified root and finalization height;
- `a`: the attestation built.

Read aloud: a timeout the client builds is at the source and is cast only over an earlier timeout
or an earlier vote for another block at that height. -/
theorem create_attestation_timeout (M : GoldilocksModel V) (F : Facts M) (n : M.N) (v : V)
    (h_c : Height) (T_c : BlockId) (h_j : Height) (J : BlockId) (h_F : Height) (a : Attestation V)
    -- the validator client of `n` builds `a`
    (hSome : AttestationFrom M n v h_c T_c h_j J h_F a)
    -- `a` is a timeout
    (hτ : a.τ = true) :
    a.h = h_c ∧ a.T = T_c ∧
      (n.sentTimeout h_c = true ∨ ∃ T' : BlockId, n.sentTarget h_c = some T' ∧ T' ≠ T_c) := by
  obtain ⟨τ, hhp, -, rfl⟩ := hSome
  change τ = true at hτ
  subst hτ
  exact ⟨rfl, rfl, F.rd.height_pair_timeout hhp⟩

/-- A lock of the record `n'` that writes the attestation the validator client of `n` builds is a
lock of `n`'s record, or is at the justification height `h_j` the client is given: the only lock
written is that of the attestation's finality pair, which is `M.finality_pair n h_j J h_F`, at
`h_j`.

The variables:
- `M`: the model; `F`: its facts;
- `n`, `n'`: the node states before and after; `v`: the validator; `h_c`, `T_c`: the source's
  height and root; `h_j`, `J`, `h_F`: the head's justification height, justified root and
  finalization height; `a`: the attestation; `h`: the height of the lock; `T`: its block.

Read aloud: recording the client's attestation writes no lock other than at the justification
height. -/
theorem create_attestation_lock (M : GoldilocksModel V) (F : Facts M) (n n' : M.N) (v : V)
    (h_c : Height) (T_c : BlockId) (h_j : Height) (J : BlockId) (h_F : Height) (a : Attestation V)
    (h : Height) (T : BlockId)
    -- the validator client of `n` builds `a`
    (hSome : AttestationFrom M n v h_c T_c h_j J h_F a)
    -- `n'`'s record is `n`'s with `a` written into it
    (hRec : AttestationRecorded M n a n')
    -- `n'`'s record holds the lock `T` at `h`
    (hl : n'.sentLock h = some T) :
    n.sentLock h = some T ∨ h = h_j := by
  obtain ⟨τ, -, -, rfl⟩ := hSome
  rw [hRec.2.1 h] at hl
  cases hfp : M.finality_pair n h_j J h_F with
  | none =>
    simp only [hfp] at hl
    exact Or.inl hl
  | some q =>
    obtain ⟨hq, -⟩ := F.rd.finality_pair_some hfp
    simp only [hfp] at hl
    by_cases hle : h_c ≤ q.hf
    · simp only [hle, ite_true] at hl
      exact Or.inl hl
    · simp only [hle, ite_false] at hl
      by_cases hh : h = q.hf
      · right
        rw [hh, hq]
      · simp only [hh, ite_false] at hl
        exact Or.inl hl

/-- The record `n'` that writes the attestation `a` into `n`'s record holds every content `n`'s
record holds.

The variables:
- `M`: the model; `n`, `n'`: the node states before and after; `a`: the attestation.

Read aloud: recording an attestation keeps every content sent. -/
theorem create_attestation_sent_subset (M : GoldilocksModel V) (n n' : M.N) (a : Attestation V)
    -- `n'`'s record is `n`'s with `a` written into it
    (hRec : AttestationRecorded M n a n') :
    n.sentAttestations ⊆ n'.sentAttestations := by
  rw [hRec.1]
  exact Finset.subset_union_left

/-- The record `n'` that writes the attestation `a` into `n`'s record holds `a`'s content.

The variables:
- `M`: the model; `n`, `n'`: the node states before and after; `a`: the attestation.

Read aloud: a recorded attestation's content is among the contents sent. -/
theorem create_attestation_content_mem (M : GoldilocksModel V) {n n' : M.N} {a : Attestation V}
    -- `n'`'s record is `n`'s with `a` written into it
    (hRec : AttestationRecorded M n a n') :
    a.content ∈ n'.sentAttestations := by
  rw [hRec.1]
  exact Finset.mem_union_right _ (Finset.mem_singleton_self _)

/-- Writing the attestation `a` into `n`'s record adds `a`'s content to the contents sent.

The variables:
- `M`: the model; `n`, `n'`: the node states before and after; `a`: the attestation.

Read aloud: the contents sent after recording `a` are those before and `a`'s. -/
theorem record_attestation_sent (M : GoldilocksModel V) (n n' : M.N) (a : Attestation V)
    -- `n'`'s record is `n`'s with `a` written into it
    (hRec : AttestationRecorded M n a n') :
    n'.sentAttestations = n.sentAttestations ∪ {a.content} :=
  hRec.1

/-- The contents the record `n'` holds after writing the attestation `a` into `n`'s record are
those of `n`'s record and `a`'s.

The variables:
- `M`: the model; `n`, `n'`: the node states before and after; `a`: the attestation;
  `c`: a content.

Read aloud: a content is sent after recording `a` exactly when it was sent before or is `a`'s. -/
theorem mem_record_attestation_sent (M : GoldilocksModel V) {n n' : M.N} {a : Attestation V}
    {c : AttestationContent}
    -- `n'`'s record is `n`'s with `a` written into it
    (hRec : AttestationRecorded M n a n') :
    c ∈ n'.sentAttestations ↔ c ∈ n.sentAttestations ∨ c = a.content := by
  rw [hRec.1, Finset.mem_union, Finset.mem_singleton]

end GoldilocksCorrectness.Record.Proofs.Routines

namespace GoldilocksCorrectness.Record.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Record

/-! ## At the spec's model -/

/-- The landed `GoldilocksCorrectness.Proofs.Routines.create_attestation_timeout`, at the record
`n.Λ` of a node state, recovered from its record form at the spec's model.

Read aloud: the landed `create_attestation_timeout` holds at every node's record, as the
record's theorem at the spec's model. -/
theorem create_attestation_timeout_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (n : NodeState V),
      type_of% (@GoldilocksCorrectness.Proofs.Routines.create_attestation_timeout V n.Λ) := by
  intro n v h_c T_c h_j J h_F a hSome hτ
  exact create_attestation_timeout (Model.goldilocks (V := V)) goldilocksFacts n v h_c T_c h_j J h_F
    a ((create_attestation_snd_eq_some_iff n v h_c T_c h_j J h_F a).1 hSome) hτ

/-- The landed `GoldilocksCorrectness.Proofs.Routines.create_attestation_lock`, at the record
`n.Λ` of a node state, recovered from its record form at the spec's model: when the client builds
nothing it returns the record unchanged; when it builds `a`, it returns `n.Λ` with `a` written into
it, the record of the node state `{ n with Λ := … }` (`create_attestation_record`,
`create_attestation_fst_of_some`).

Read aloud: the landed `create_attestation_lock` holds at every node's record, as the
record's theorem at the spec's model. -/
theorem create_attestation_lock_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (n : NodeState V),
      type_of% (@GoldilocksCorrectness.Proofs.Routines.create_attestation_lock V n.Λ) := by
  intro n v h_c T_c h_j J h_F h T hl
  cases hb : (create_attestation n.Λ v h_c T_c h_j J h_F).2 with
  | none =>
    rw [(GoldilocksCorrectness.Proofs.Routines.create_attestation_record n.Λ v h_c T_c h_j J
      h_F).1 hb] at hl
    exact Or.inl hl
  | some a =>
    rw [create_attestation_fst_of_some n.Λ v h_c T_c h_j J h_F a hb] at hl
    exact create_attestation_lock (Model.goldilocks (V := V)) goldilocksFacts n
      { n with Λ := record_attestation n.Λ a } v h_c T_c h_j J h_F a h T
      ((create_attestation_snd_eq_some_iff n v h_c T_c h_j J h_F a).1 hb)
      (attestationRecorded_of_record n _ a rfl) hl

/-- The landed `GoldilocksCorrectness.Proofs.Routines.create_attestation_sent_subset`, at the
record `n.Λ` of a node state, recovered from its record form at the spec's model.

Read aloud: the landed `create_attestation_sent_subset` holds at every node's record, as the
record's theorem at the spec's model. -/
theorem create_attestation_sent_subset_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (n : NodeState V),
      type_of% (@GoldilocksCorrectness.Proofs.Routines.create_attestation_sent_subset V
        n.Λ) := by
  intro n v h_c T_c h_j J h_F
  cases hb : (create_attestation n.Λ v h_c T_c h_j J h_F).2 with
  | none =>
    rw [(GoldilocksCorrectness.Proofs.Routines.create_attestation_record n.Λ v h_c T_c h_j J
      h_F).1 hb]
  | some a =>
    rw [create_attestation_fst_of_some n.Λ v h_c T_c h_j J h_F a hb]
    exact create_attestation_sent_subset (Model.goldilocks (V := V)) n
      { n with Λ := record_attestation n.Λ a } a (attestationRecorded_of_record n _ a rfl)

/-- The landed `GoldilocksCorrectness.Proofs.Routines.create_attestation_content_mem`, at the
record `n.Λ` of a node state, recovered from its record form at the spec's model.

Read aloud: the landed `create_attestation_content_mem` holds at every node's record, as the
record's theorem at the spec's model. -/
theorem create_attestation_content_mem_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (n : NodeState V),
      type_of% (@GoldilocksCorrectness.Proofs.Routines.create_attestation_content_mem V
        n.Λ) := by
  intro n v h_c T_c h_j J h_F a ha
  rw [create_attestation_fst_of_some n.Λ v h_c T_c h_j J h_F a ha]
  exact create_attestation_content_mem (Model.goldilocks (V := V))
    (n' := { n with Λ := record_attestation n.Λ a }) (attestationRecorded_of_record n _ a rfl)

/-- The landed `GoldilocksCorrectness.Proofs.Routines.record_attestation_sent`, at the record
`n.Λ` of a node state, recovered from its record form at the spec's model.

Read aloud: the landed `record_attestation_sent` holds at every node's record, as the
record's theorem at the spec's model. -/
theorem record_attestation_sent_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (n : NodeState V),
      type_of% (@GoldilocksCorrectness.Proofs.Routines.record_attestation_sent V n.Λ) := by
  intro n a
  exact record_attestation_sent (Model.goldilocks (V := V)) n
    { n with Λ := record_attestation n.Λ a } a (attestationRecorded_of_record n _ a rfl)

/-- The landed `GoldilocksCorrectness.Proofs.Routines.mem_record_attestation_sent`, at the record
`n.Λ` of a node state, recovered from its record form at the spec's model.

Read aloud: the landed `mem_record_attestation_sent` holds at every node's record, as the
record's theorem at the spec's model. -/
theorem mem_record_attestation_sent_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (n : NodeState V),
      type_of% (@GoldilocksCorrectness.Proofs.Routines.mem_record_attestation_sent V n.Λ) := by
  intro n a c
  exact mem_record_attestation_sent (Model.goldilocks (V := V))
    (n' := { n with Λ := record_attestation n.Λ a }) (attestationRecorded_of_record n _ a rfl)

end GoldilocksCorrectness.Record.Proofs.Routines
