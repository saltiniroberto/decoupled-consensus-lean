import Spec.Fig6StateTransition

/-!
# Accountable safety — the statement

Conflicting blocks cannot both finalize unless at least `2q − W` weight is provably E1-
or E2-slashable. **Statements only**: each result is a named `Prop`, so nothing claims a
proof and `make check` stays green; proving one later means adding
`theorem … : AccountableSafety …` beside it. A proof of this statement over an earlier,
removed formalization lives on the `pre-consensus1-purge` branch
(`Analysis/Theorems.lean`, its Lemma 11) — a starting point, not a citation.
-/

set_option autoImplicit false

namespace Consensus1

variable {Validator : Type} [Roots] [DecidableEq Validator]

/-- **E2**, the second slashing condition: both height pairs carry the same height, both
    targets are named, and the targets differ. "Both targets are nonempty" is carried by
    the constructor — `HeightPair.target` is the pair `(h, T)` with `T ≠ ⊥`, and an
    empty-target or empty pair cannot match it.

    A condition on a pair of attestations, not on one validator: "two signed attestations
    **by one validator** are slashable" is the caller's to state, and
    `AccountableSafety`'s conclusion pins both to the same `v`. -/
def E2 (x y : Attestation Validator) : Prop :=
  ∃ h T T', x.heightPair = .target h T ∧ y.heightPair = .target h T' ∧ T ≠ T'

/-- **E1**, the first slashing condition: one attestation's finality pair is `(h, T)`,
    while the other's height pair sits at the same height with a different target —
    a named `T' ≠ T`, or the empty target `(h, ⊥)`. An empty height pair has height `⊥`
    and conflicts with neither; nothing here stops `x = y`, the two conflicting fields
    possibly sharing one signed attestation.

    `x` carries the finality pair and `y` the height pair, so E1 is asymmetric where E2
    is not; a caller wanting either order says so, as `AccountableSafety` does. -/
def E1 (x y : Attestation Validator) : Prop :=
  ∃ h T, x.finalityPair = .pair h T ∧
    ((∃ T', y.heightPair = .target h T' ∧ T' ≠ T) ∨ y.heightPair = .emptyTarget h)

/-- An attestation carried by some block of the chain ending at `B` — inclusion, the
    sense in which a chain holds the evidence for its own finalizations. -/
def IncludedOn (a : Attestation Validator) (B : Block Validator) : Prop :=
  ∃ Y, Y ⪯ B ∧ a ∈ Y.attestations

variable [Electorate Validator] [Params]

/-- The state of the chain ending at `B`: `state_transition` folded along the parent
    link from the genesis state. Store-free on purpose — the statements below quantify
    over blocks alone — and what every coherent store records: `process_block` writes
    `Σ.σ[B] = state_transition(Σ.σ[B.parent], B)` block by block, so on such a store
    `Σ.σ[B] = replay B`. Structural recursion on the parent link, like `ancestors`. -/
def replay : Block Validator → ChainState Validator
  | .genesis => ChainState.gen
  | .mk p s rt vs as => stateTransition (replay p) (.mk p s rt vs as)

/-- **Accountable safety** (statement only): conflicting blocks cannot both finalize
    unless at least `2q − W` weight — what two `q`-quorums must share, a third of the
    electorate — is provably E1- or E2-slashable.

    Read aloud: take two chains whose replayed states finalize conflicting blocks. Then
    there is a set of validators of weight at least `2q − W`, each of which signed two
    attestations, one included on each chain (in either order — which chain carries the
    finality commitment depends on which height is lower), that form an E1 or E2 pair. -/
def AccountableSafety (Validator : Type) [DecidableEq Validator]
    [Electorate Validator] : Prop :=
  ∀ B_F B_F' : Block Validator,
    ¬ Compatible (replay B_F).F (replay B_F').F →
    ∃ A : Finset Validator, w(A) ≥ 2 * q Validator - W Validator ∧
      ∀ v ∈ A, ∃ x y : Attestation Validator, x.validator = v ∧ y.validator = v ∧
        ((IncludedOn x B_F ∧ IncludedOn y B_F') ∨ (IncludedOn x B_F' ∧ IncludedOn y B_F)) ∧
        (E1 x y ∨ E2 x y)

end Consensus1
