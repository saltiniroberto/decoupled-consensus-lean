module
public import GoldilocksCorrectness.Proofs.Executions.HonestAccountable
public import GoldilocksCorrectness.Statements.Executions.UnforgeabilityStatements
public import GoldilocksCorrectness.Statements.Executions.InvariantStatements
public import GoldilocksCorrectness.Statements.Executions.AccountableStatements
public import GoldilocksCorrectness.Statements.Routines.AccountableStatements

@[expose] public section

/-!
# Slashable evidence and honest validators, the proofs

The audited statements are in `Statements/Executions/SlashableEvidenceStatements.lean`:

- `honest_never_slashable`: under unforgeability, two attestations of a validator honest up to a
  step, each in the sent log after that step on its own or included in a block, form no E1 and no
  E2 pair;
- `finalized_compatible_of_no_slashable`: when no two blocks held by honest validators are
  slashable between them, two honest validators' finalized blocks are compatible, or two different
  blocks of their two trees share a root.

## The kit

- `sent_attestation_recorded`: an attestation in the sent log, on its own or included in a block,
  its validator honest up to the step, has its content in that validator's record.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC

namespace GoldilocksCorrectness.Proofs.Executions

open Framework.StsMultisetLog (AtomicExec Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Executions
open GoldilocksCorrectness.Statements.Routines (E1 E2 SlashableBetween RootCollisionIn)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder] {S : Setup V} {Sched : Schedule V}

/-- Under unforgeability, an attestation `a` in the sent log after `i` steps, signed by some `w`
on its own or included in a block signed by `w`, with its validator outside the adversary set up
to the time after `i` steps, has its content in that validator's record after `i` steps.

Why: unforgeability puts `a` on the wire under its own validator's signature after `i` steps; that
message came from that validator's tick, whose record holds the content of `a` and only grows.

The variables:
- `x`: the execution; `hU`: unforgeability; `i`: the step; `a`: the attestation. -/
theorem sent_attestation_recorded (x : AtomicExec (protocol S) Sched)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace) {i : ℕ} {a : Attestation V}
    -- `a` is in the sent log after `i` steps, on its own or included in a block
    (hs : ∃ w : V, ((⟨w, .attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[i].sent ∨
      ∃ B : Block V, (⟨w, .block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i].sent ∧
        a ∈ B.attestations))
    (hH : HonestThrough x i a.val_index) :
    a.content ∈ (x[i][a.val_index].st).Λ.sent := by
  have hown : (⟨a.val_index, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[i].sent := by
    obtain ⟨w, hw | ⟨B, hB, haB⟩⟩ := hs
    · exact hU.unforgeable i ⟨w, .attest a⟩ a.val_index hw rfl hH
    · exact hU.carried i ⟨w, .block B⟩ (.attest a) a.val_index hB (Or.inr ⟨a, haB, rfl⟩) rfl hH
  obtain ⟨k', hk', -, -, -, hrec⟩ :=
    GoldilocksCorrectness.Statements.Executions.attestation_from_own_tick S Sched x hU i a hown hH
  exact record_sent_mono x a.val_index (by omega) hrec

/-- An honest validator is never slashable, the proof; the audited statement is in
`Statements/Executions/SlashableEvidenceStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `hU`: unforgeability; `i`: the step;
  `v`: the validator; `a`, `a'`: the two attestations. -/
theorem honest_never_slashable (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (i : ℕ) (v : V)
    -- `v` is outside the adversary set at every time up to the time after `i` steps
    (hv : HonestThroughTime Sched (x[i].time : Int) v)
    (a a' : Attestation V)
    -- the two attestations are `v`'s
    (ha : a.val_index = v) (ha' : a'.val_index = v)
    -- `a` is in the sent log after `i` steps, on its own or included in a block
    (hs : ∃ w : V, ((⟨w, .attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[i].sent ∨
      ∃ B : Block V, (⟨w, .block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i].sent ∧
        a ∈ B.attestations))
    -- `a'` is in the sent log after `i` steps, on its own or included in a block
    (hs' : ∃ w : V, ((⟨w, .attest a'⟩ : SignedMsg V (NamedObject V)) ∈ x[i].sent ∨
      ∃ B : Block V, (⟨w, .block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i].sent ∧
        a' ∈ B.attestations)) :
    ¬ E1 a a' ∧ ¬ E2 a a' := by
  subst ha
  have hc := sent_attestation_recorded x hU hs hv
  have hc' := sent_attestation_recorded x hU hs' (by rw [ha']; exact hv)
  rw [ha'] at hc'
  exact GoldilocksCorrectness.Statements.Routines.no_slashable_of_consistent _
    (recordConsistent_of_exec S Sched x i a.val_index) a a' hc hc'

/-- Finalized blocks agree when no blocks held by honest validators are slashable, the proof; the
audited statement is in `Statements/Executions/SlashableEvidenceStatements.lean`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `i`, `j`: the two steps; `v₁`, `v₂`:
  the two validators. -/
theorem finalized_compatible_of_no_slashable (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched)
    -- no two blocks held by honest validators, at any steps, are slashable between them
    (hNoSlash : ∀ (i' j' : ℕ) (w₁ w₂ : V), HonestThrough x i' w₁ → HonestThrough x j' w₂ →
      ∀ b₁ ∈ (x[i'][w₁].st).S.T, ∀ b₂ ∈ (x[j'][w₂].st).S.T, ¬ SlashableBetween b₁ b₂)
    (i j : ℕ) (v₁ v₂ : V) (hH₁ : HonestThrough x i v₁) (hH₂ : HonestThrough x j v₂) :
    (x[i][v₁].st).S.F.compatible (x[j][v₂].st).S.F = true ∨
      RootCollisionIn ((x[i][v₁].st).S.T ∪ (x[j][v₂].st).S.T) := by
  cases hc : (x[i][v₁].st).S.F.compatible (x[j][v₂].st).S.F
  · rcases lem73_accountable_safety S Sched x i j v₁ v₂ hc with
      ⟨b₁, hb₁, b₂, hb₂, hsl⟩ | hr
    · exact absurd hsl (hNoSlash i j v₁ v₂ hH₁ hH₂ b₁ hb₁ b₂ hb₂)
    · exact Or.inr hr
  · exact Or.inl rfl

end GoldilocksCorrectness.Proofs.Executions
