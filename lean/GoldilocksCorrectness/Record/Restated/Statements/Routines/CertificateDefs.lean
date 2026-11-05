module
public import GoldilocksCorrectness.Record.ModelSpellings
public import GoldilocksCorrectness.Record.ModelGoldilocks
public import GoldilocksCorrectness.Statements.Routines.CertificateDefs
public import GoldilocksCorrectness.Proofs.Routines.Accountable

@[expose] public section

/-! The landed definitions count against `quorum V` and read the votes on
`B`'s chain; at the spec's model the two forms are equivalent (`goldilocks_JustificationCertOn`,
`goldilocks_ProgressCertOn`, `goldilocks_FinalityCertOn`, in the simp set `record_goldilocks`):
a vote on `X`'s chain is on `B`'s chain when `X` is `B` or an ancestor of `B`, and conversely the
block `X` is `B` itself. The two forms are equivalent, not equal by definition.

Three theorems of no landed counterpart close the page: a certificate on `B`'s chain is one on the
chain of every descendant of `B`.
-/

set_option autoImplicit false

open scoped DC

namespace GoldilocksCorrectness.Record.Statements.Routines

open Goldilocks (Block Attestation Height)
open GoldilocksCorrectness.Record
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans on_chain_mono)

variable {V : Type} [DecidableEq V] [Fintype V]

/-- `JustificationCertOn M B h T`: a justification certificate on the chain of `B` for `(h, T)`,
in the model `M`: some block `X`, `B` or an ancestor of `B`, has a set `A` of validators reaching
the quorum at `X`, each with a target vote at the height `h` for `T`'s root included in `X` or in
an ancestor of `X`.

The variables:
- `M`: the model; `B`: the block whose chain holds the votes; `h`: the height of the votes; `T`:
  the block they name.

Read aloud: some block `X` of `B`'s chain has a set of validators, at least the quorum at `X`,
each with a target vote at `h` for `T` included on `X`'s chain. -/
def JustificationCertOn (M : GoldilocksModel V) (B : Block V) (h : Height) (T : Block V) : Prop :=
  ∃ X : Block V, X.AncestorEq B ∧ ∃ A : Finset V, M.quorumAt X ≤ |A| ∧ ∀ v ∈ A,
    ∃ a : Attestation V, a.val_index = v ∧ a.h = h ∧ a.T = T.root ∧ a.τ = false ∧
      M.on_chain a X = true

/-- `ProgressCertOn M B h T`: a progress certificate on the chain of `B` at `(h, T)`, in the model
`M`: some block `X`, `B` or an ancestor of `B`, has a set `A` of validators reaching the quorum at
`X`, each with a vote at the height `h` naming `T`'s root, a target vote or a timeout, included in
`X` or in an ancestor of `X`.

The variables:
- `M`: the model; `B`: the block whose chain holds the votes; `h`: the height of the votes; `T`:
  the block they name.

Read aloud: some block `X` of `B`'s chain has a set of validators, at least the quorum at `X`,
each with a vote at `h` naming `T` included on `X`'s chain. -/
def ProgressCertOn (M : GoldilocksModel V) (B : Block V) (h : Height) (T : Block V) : Prop :=
  ∃ X : Block V, X.AncestorEq B ∧ ∃ A : Finset V, M.quorumAt X ≤ |A| ∧ ∀ v ∈ A,
    ∃ a : Attestation V, a.val_index = v ∧ a.h = h ∧ a.T = T.root ∧ M.on_chain a X = true

/-- `FinalityCertOn M B h T`: a finality certificate on the chain of `B` for `(h, T)`, in the model
`M`: some block `X`, `B` or an ancestor of `B`, has a set `A` of validators reaching the quorum at
`X`, each with an attestation carrying the finality pair `(h, T.root)` included in `X` or in an
ancestor of `X`.

The variables:
- `M`: the model; `B`: the block whose chain holds the attestations; `h`: the height of the
  finality pairs; `T`: the block they name.

Read aloud: some block `X` of `B`'s chain has a set of validators, at least the quorum at `X`,
each with an attestation carrying the finality pair `(h, T)` included on `X`'s chain. -/
def FinalityCertOn (M : GoldilocksModel V) (B : Block V) (h : Height) (T : Block V) : Prop :=
  ∃ X : Block V, X.AncestorEq B ∧ ∃ A : Finset V, M.quorumAt X ≤ |A| ∧ ∀ v ∈ A,
    ∃ a : Attestation V, a.val_index = v ∧ a.finality_pair = some ⟨h, T.root⟩ ∧
      M.on_chain a X = true

/-! ## At the spec's model -/

/-- At the spec's model, a justification certificate in the record's form is one in the landed
form: from the landed form take `X = B`; from the record's, a vote on `X`'s chain is on `B`'s chain.

The variables:
- `B`: the block; `h`: the height; `T`: the block named.

Read aloud: for the spec's model, the two forms of a justification certificate say the same. -/
@[record_goldilocks]
theorem goldilocks_JustificationCertOn (B : Block V) (h : Height) (T : Block V) :
    GoldilocksCorrectness.Statements.Routines.JustificationCertOn B h T =
      JustificationCertOn (Model.goldilocks (V := V)) B h T := by
  apply propext
  constructor
  · rintro ⟨A, hA, hv⟩
    exact ⟨B, ancestorEq_refl B, A, hA, hv⟩
  · rintro ⟨X, hXB, A, hA, hv⟩
    refine ⟨A, hA, fun v hvA => ?_⟩
    obtain ⟨a, h1, h2, h3, h4, h5⟩ := hv v hvA
    exact ⟨a, h1, h2, h3, h4, on_chain_mono a hXB h5⟩

/-- At the spec's model, a progress certificate in the record's form is one in the landed form.

The variables:
- `B`: the block; `h`: the height; `T`: the block named.

Read aloud: for the spec's model, the two forms of a progress certificate say the same. -/
@[record_goldilocks]
theorem goldilocks_ProgressCertOn (B : Block V) (h : Height) (T : Block V) :
    GoldilocksCorrectness.Statements.Routines.ProgressCertOn B h T =
      ProgressCertOn (Model.goldilocks (V := V)) B h T := by
  apply propext
  constructor
  · rintro ⟨A, hA, hv⟩
    exact ⟨B, ancestorEq_refl B, A, hA, hv⟩
  · rintro ⟨X, hXB, A, hA, hv⟩
    refine ⟨A, hA, fun v hvA => ?_⟩
    obtain ⟨a, h1, h2, h3, h4⟩ := hv v hvA
    exact ⟨a, h1, h2, h3, on_chain_mono a hXB h4⟩

/-- At the spec's model, a finality certificate in the record's form is one in the landed form.

The variables:
- `B`: the block; `h`: the height; `T`: the block named.

Read aloud: for the spec's model, the two forms of a finality certificate say the same. -/
@[record_goldilocks]
theorem goldilocks_FinalityCertOn (B : Block V) (h : Height) (T : Block V) :
    GoldilocksCorrectness.Statements.Routines.FinalityCertOn B h T =
      FinalityCertOn (Model.goldilocks (V := V)) B h T := by
  apply propext
  constructor
  · rintro ⟨A, hA, hv⟩
    exact ⟨B, ancestorEq_refl B, A, hA, hv⟩
  · rintro ⟨X, hXB, A, hA, hv⟩
    refine ⟨A, hA, fun v hvA => ?_⟩
    obtain ⟨a, h1, h2, h3⟩ := hv v hvA
    exact ⟨a, h1, h2, on_chain_mono a hXB h3⟩

/-! ## Along a chain -/

/-- A justification certificate on the chain of `B` is one on the chain of every block of which `B`
is an ancestor.

The variables:
- `M`: the model; `B`, `B'`: the block and its descendant; `h`: the height; `T`: the block named.

Read aloud: a justification certificate on `B`'s chain is on the chain of every descendant of
`B`. -/
theorem justificationCertOn_of_ancestorEq (M : GoldilocksModel V) {B B' : Block V} {h : Height}
    {T : Block V}
    -- `B` is `B'` or an ancestor of `B'`
    (hBB' : B.AncestorEq B')
    -- the certificate on `B`'s chain
    (hc : JustificationCertOn M B h T) : JustificationCertOn M B' h T := by
  obtain ⟨X, hXB, hA⟩ := hc
  exact ⟨X, ancestorEq_trans hXB hBB', hA⟩

/-- A progress certificate on the chain of `B` is one on the chain of every block of which `B` is
an ancestor.

The variables:
- `M`: the model; `B`, `B'`: the block and its descendant; `h`: the height; `T`: the block named.

Read aloud: a progress certificate on `B`'s chain is on the chain of every descendant of `B`. -/
theorem progressCertOn_of_ancestorEq (M : GoldilocksModel V) {B B' : Block V} {h : Height}
    {T : Block V}
    -- `B` is `B'` or an ancestor of `B'`
    (hBB' : B.AncestorEq B')
    -- the certificate on `B`'s chain
    (hc : ProgressCertOn M B h T) : ProgressCertOn M B' h T := by
  obtain ⟨X, hXB, hA⟩ := hc
  exact ⟨X, ancestorEq_trans hXB hBB', hA⟩

/-- A finality certificate on the chain of `B` is one on the chain of every block of which `B` is
an ancestor.

The variables:
- `M`: the model; `B`, `B'`: the block and its descendant; `h`: the height; `T`: the block named.

Read aloud: a finality certificate on `B`'s chain is on the chain of every descendant of `B`. -/
theorem finalityCertOn_of_ancestorEq (M : GoldilocksModel V) {B B' : Block V} {h : Height}
    {T : Block V}
    -- `B` is `B'` or an ancestor of `B'`
    (hBB' : B.AncestorEq B')
    -- the certificate on `B`'s chain
    (hc : FinalityCertOn M B h T) : FinalityCertOn M B' h T := by
  obtain ⟨X, hXB, hA⟩ := hc
  exact ⟨X, ancestorEq_trans hXB hBB', hA⟩

end GoldilocksCorrectness.Record.Statements.Routines
