module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.HonestAccountable
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.SentUnforgeable
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.UnforgeabilityStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.InvariantStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.AccountableStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.AccountableStatementsValidatorClient

@[expose] public section

/-!
# SlashableEvidence, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/SlashableEvidence.lean`, over a model `M`
whose facts `F` hold, for a trace `x` whose node states are the model's. The audited statements are
in `Record/Restated/Statements/Executions/SlashableEvidenceStatements.lean`:

- `honest_never_slashable`: two attestations of a validator honest up to a step, each in the sent
  log after that step on its own or included in a block, form no E1 and no E2 pair;
- `finalized_compatible_of_no_slashable`: when no two blocks held by honest validators are
  slashable between them, two honest validators' finalized blocks are compatible, or two different
  blocks of their two trees share a root.

## The kit

- `sent_attestation_recorded`: an attestation in the sent log, on its own or included in a block,
  its validator honest up to the step, has its content in that validator's record.

The landed proofs read unforgeability, a premise of the old run; over the trace the protocol's half
of unforgeability is the theorem `sent_unforgeable`, from the run's facts `R` and the
environment's facts `E`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Proofs.Executions

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Record.Statements.Routines (SlashableBetween)
open GoldilocksCorrectness.Statements.Routines (E1 E2 RootCollisionIn)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder] {S : Setup V} {A : Activity V}
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- An attestation `a` in the sent log after `i` steps, signed by some `w` on its own or included
in a block signed by `w`, with its validator outside the adversary set up to the time after `i`
steps, has its content in that validator's record after `i` steps.

Why: `sent_unforgeable` puts `a` on the wire under its own validator's signature after `i` steps;
that message came from that validator's tick (`attestation_from_own_tick`), whose record holds the
content of `a` and only grows (`record_sent_mono`).

The variables:
- `M`: the model; `F`: its facts;
- `x`: the trace; `R`: the run's facts; `E`: the environment's facts; `i`: the step; `a`: the
  attestation. -/
theorem sent_attestation_recorded (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
        {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {i : ℕ} {a : Attestation V}
    -- `a` is in the sent log after `i` steps, on its own or included in a block
    (hs : ∃ w : V, ((⟨w, .attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent i ∨
      ∃ B : Block V, (⟨w, .block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent i ∧
        a ∈ B.attestations))
    (hH : x.HonestThrough A i a.val_index) :
    a.content ∈ (x.st i a.val_index).sentAttestations := by
  have hown : (⟨a.val_index, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent i := by
    obtain ⟨w, hw | ⟨B, hB, haB⟩⟩ := hs
    · exact (sent_unforgeable M F) R E i ⟨w, .attest a⟩ (.attest a) a.val_index hw (Or.inl rfl)
        rfl hH
    · exact (sent_unforgeable M F) R E i ⟨w, .block B⟩ (.attest a) a.val_index hB
        (Or.inr (Or.inr ⟨a, haB, rfl⟩)) rfl hH
  obtain ⟨k', hk', -, -, -, hrec⟩ := (attestation_from_own_tick M F) S A x R E i a hown hH
  exact (record_sent_mono M F) x R E a.val_index (by omega) hrec

/-- An honest validator is never slashable, the proof; the audited statement is in
`Record/Restated/Statements/Executions/SlashableEvidenceStatements.lean`.

The variables:
- `M`: the model; `F`: its facts;
- `S`: the setup; `A`: the activity; `x`: the trace; `R`: the run's facts; `E`: the environment's
  facts; `i`: the step; `v`: the validator; `a`, `a'`: the two attestations. -/
theorem honest_never_slashable (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (i : ℕ) (v : V)
    -- `v` is outside the adversary set at every time up to the time after `i` steps
    (hv : A.HonestThroughStep i v)
    (a a' : Attestation V)
    -- the two attestations are `v`'s
    (ha : a.val_index = v) (ha' : a'.val_index = v)
    -- `a` is in the sent log after `i` steps, on its own or included in a block
    (hs : ∃ w : V, ((⟨w, .attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent i ∨
      ∃ B : Block V, (⟨w, .block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent i ∧
        a ∈ B.attestations))
    -- `a'` is in the sent log after `i` steps, on its own or included in a block
    (hs' : ∃ w : V, ((⟨w, .attest a'⟩ : SignedMsg V (NamedObject V)) ∈ x.sent i ∨
      ∃ B : Block V, (⟨w, .block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent i ∧
        a' ∈ B.attestations)) :
    ¬ E1 a a' ∧ ¬ E2 a a' := by
  subst ha
  have hc := (sent_attestation_recorded M F) x R E hs hv
  have hc' := (sent_attestation_recorded M F) x R E hs' (by rw [ha']; exact hv)
  rw [ha'] at hc'
  exact (GoldilocksCorrectness.Record.Statements.Routines.no_slashable_of_consistent M F) _
    ((recordConsistent_of_exec M F) S A x R E i a.val_index) a a' hc hc'

/-- Finalized blocks agree when no blocks held by honest validators are slashable, the proof; the
audited statement is in `Record/Restated/Statements/Executions/SlashableEvidenceStatements.lean`.

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed;
- `S`: the setup; `A`: the activity; `x`: the trace; `R`: the run's facts (no promise of the
  environment is read); `i`, `j`: the two steps; `v₁`, `v₂`: the two validators. -/
theorem finalized_compatible_of_no_slashable (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    -- no two blocks held by honest validators, at any steps, are slashable between them
    (hNoSlash : ∀ (i' j' : ℕ) (w₁ w₂ : V), x.HonestThrough A i' w₁ → x.HonestThrough A j' w₂ →
      ∀ b₁ ∈ (x.st i' w₁).tree, ∀ b₂ ∈ (x.st j' w₂).tree, ¬ SlashableBetween M b₁ b₂)
    (i j : ℕ) (v₁ v₂ : V) (hH₁ : x.HonestThrough A i v₁) (hH₂ : x.HonestThrough A j v₂) :
    (x.st i v₁).finalized.compatible (x.st j v₂).finalized = true ∨
      RootCollisionIn ((x.st i v₁).tree ∪ (x.st j v₂).tree) := by
  cases hc : (x.st i v₁).finalized.compatible (x.st j v₂).finalized
  · rcases (lem73_accountable_safety_of_run M F Fx) S x R i j v₁ v₂ hc with
      ⟨b₁, hb₁, b₂, hb₂, hsl⟩ | hr
    · exact absurd hsl (hNoSlash i j v₁ v₂ hH₁ hH₂ b₁ hb₁ b₂ hb₂)
    · exact Or.inr hr
  · exact Or.inl rfl

end GoldilocksCorrectness.Record.Proofs.Executions
