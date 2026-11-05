module
public import GoldilocksCorrectness.Proofs.Routines.Blocks
public import Goldilocks.FG.State

@[expose] public section

/-!
# The vocabulary of the statements about the certificates on a chain

Three definitions the statements about the certificates of a chain state read
(`CertificateStatements.lean`):

- `JustificationCertOn B h T`, a quorum of target votes at the height `h` for `T` included on
  the chain of `B`;
- `ProgressCertOn B h T`, a quorum of votes at the height `h` naming `T`, target votes or
  timeouts, included on the chain of `B`;
- `FinalityCertOn B h T`, a quorum of finality pairs `(h, T)` included on the chain of `B`.


-/

set_option autoImplicit false

open scoped DC

namespace GoldilocksCorrectness.Statements.Routines

open Goldilocks

variable {V : Type} [DecidableEq V] [Fintype V]

/-- `JustificationCertOn B h T`: a justification certificate on the chain of `B` for `(h, T)`: a
quorum of validators, each with a target vote at the height `h` for `T`'s root included in `B` or
in an ancestor of `B`.

The variables:
- `B`: the block whose chain holds the votes; `h`: the height of the votes; `T`: the block they
  name.

Read aloud: a quorum of validators have target votes at `h` for `T` included on `B`'s chain. -/
def JustificationCertOn (B : Block V) (h : Height) (T : Block V) : Prop :=
  ∃ A : Finset V, quorum V ≤ |A| ∧ ∀ v ∈ A, ∃ a : Attestation V, a.val_index = v ∧
    a.h = h ∧ a.T = T.root ∧ a.τ = false ∧ on_chain a B = true

/-- `ProgressCertOn B h T`: a progress certificate on the chain of `B` at `(h, T)`: a quorum of
validators, each with a vote at the height `h` naming `T`'s root, a target vote or a timeout,
included in `B` or in an ancestor of `B`.

The variables:
- `B`: the block whose chain holds the votes; `h`: the height of the votes; `T`: the block they
  name.

Read aloud: a quorum of validators have votes at `h` naming `T` included on `B`'s chain. -/
def ProgressCertOn (B : Block V) (h : Height) (T : Block V) : Prop :=
  ∃ A : Finset V, quorum V ≤ |A| ∧ ∀ v ∈ A, ∃ a : Attestation V, a.val_index = v ∧
    a.h = h ∧ a.T = T.root ∧ on_chain a B = true

/-- `FinalityCertOn B h T`: a finality certificate on the chain of `B` for `(h, T)`: a quorum of
validators, each with an attestation carrying the finality pair `(h, T.root)` included in `B` or
in an ancestor of `B`.

The variables:
- `B`: the block whose chain holds the attestations; `h`: the height of the finality pairs; `T`:
  the block they name.

Read aloud: a quorum of validators have attestations with the finality pair `(h, T)` included on
`B`'s chain. -/
def FinalityCertOn (B : Block V) (h : Height) (T : Block V) : Prop :=
  ∃ A : Finset V, quorum V ≤ |A| ∧ ∀ v ∈ A, ∃ a : Attestation V, a.val_index = v ∧
    a.finality_pair = some ⟨h, T.root⟩ ∧ on_chain a B = true

end GoldilocksCorrectness.Statements.Routines
