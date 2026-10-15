module
public import Model.Vocabulary.Protocol.Handlers
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# The two list cases of `admit_rows`

The admission `Protocol.NamedAdmission.admit_rows` of the empty list, and of a list with a first
attestation.
-/

-- The definitions this file unfolds, made locally semireducible.
set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.NamedAdmission.admit_rows

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

/-- Admitting the empty list of named attestations returns the named store it was given. -/
theorem admit_rows_nil' (hc : Protocol.HealConfig) (st : Protocol.NamedStore V) :
    Protocol.NamedAdmission.admit_rows hc st [] = st := by
  unfold Protocol.NamedAdmission.admit_rows
  rfl

/-- Admitting `row :: rows` into `st` is admitting `rows` into the store that admitting `row` into
    `st` returns. -/
theorem admit_rows_cons' (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (row : NamedAttestation V) (rows : List (NamedAttestation V)) :
    Protocol.NamedAdmission.admit_rows hc st (row :: rows)
      = Protocol.NamedAdmission.admit_rows hc (Protocol.NamedAdmission.admit_row hc st row)
          rows := by
  unfold Protocol.NamedAdmission.admit_rows
  rfl

end DecoupledConsensusModel.Sts
