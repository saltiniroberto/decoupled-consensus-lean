module
public import GoldilocksCorrectness.Proofs.Routines.Record

@[expose] public section

/-!
# The statements about the anti-slashing record

The audited statements of Lemma 72: the initial anti-slashing record is consistent
(`RecordConsistent`), and the validator client's `create_attestation` keeps a consistent record
consistent and writes the content of the attestation it returns into the record it returns. Each is
proved in `GoldilocksCorrectness/Proofs/Routines/Record.lean`.


-/

set_option autoImplicit false

open scoped DC

namespace GoldilocksCorrectness.Statements.Routines

open Goldilocks

variable {V : Type}

/-- **Lemma 72, the initial record is consistent.** The initial anti-slashing record
`SigningHistory.initial` satisfies `RecordConsistent`.

Why: it holds no content, and its arrays hold no target, no timeout and no lock.

Read aloud: the initial record is consistent. -/
theorem lem72_initial_record_consistent : RecordConsistent SigningHistory.initial :=
  GoldilocksCorrectness.Proofs.Routines.lem72_initial_record_consistent

/-- **Lemma 72, `create_attestation` keeps the record consistent.** When the anti-slashing record
`Λ` is consistent, the record `create_attestation` returns is consistent, and when it returns an
attestation, that attestation's content is in the record it returns.

Why: `create_attestation` either returns `Λ` unchanged, or writes one attestation whose vote
`already_sent` allowed and whose finality pair `finality_pair` allowed; a target is written only at
a height where `Λ` holds no content, a finality pair only at a height where every content of `Λ`
names its block and none is a timeout, and a vote at the height of a lock only for the lock's block.

The variables:
- `Λ`: the record; `v`: the validator; `h_c`, `T_c`: the height of its source and the root of the
  block that took the source into that height;
- `h_j`, `J`, `h_F`: the source's justification height, the root of its justified block and its
  finalization height.

Read aloud: `create_attestation` keeps a consistent record consistent, and when it returns an
attestation, that attestation's content is in the record it returns. -/
theorem lem72_create_attestation_consistent (Λ : SigningHistory) (v : V) (h_c : Height)
    (T_c : BlockId) (h_j : Height) (J : BlockId) (h_F : Height)
    (hΛ : RecordConsistent Λ) :
    RecordConsistent (create_attestation Λ v h_c T_c h_j J h_F).1 ∧
      ∀ a : Attestation V, (create_attestation Λ v h_c T_c h_j J h_F).2 = some a →
        a.content ∈ (create_attestation Λ v h_c T_c h_j J h_F).1.sent :=
  GoldilocksCorrectness.Proofs.Routines.lem72_create_attestation_consistent Λ v h_c T_c h_j J h_F hΛ

end GoldilocksCorrectness.Statements.Routines
