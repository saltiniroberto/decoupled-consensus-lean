module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.SlashableEvidence

@[expose] public section

/-!
# SlashableEvidenceStatements, over a model

The statements of `GoldilocksCorrectness/Statements/Executions/SlashableEvidenceStatements.lean`,
over a model `M` whose facts `F` hold, for a trace `x` whose node states are the model's: slashable
evidence and honest validators. Each is a one-line call of the theorem of the same name of
`Record/Restated/Proofs/Executions/SlashableEvidence.lean`.

- `honest_never_slashable`: the attestations of a validator honest up to a step, in the sent log
  then, form no slashable pair;
- `finalized_compatible_of_no_slashable`: when no two blocks held by honest validators are
  slashable between them, two honest validators' finalized blocks are compatible, or a root
  collision hit their two trees.

Over the trace, unforgeability is no premise: the protocol's half of it is the theorem
`sent_unforgeable`, from the run's facts and the environment's facts.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Statements.Executions

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsNoDelivery)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Routines (SlashableBetween)
open GoldilocksCorrectness.Statements.Routines (E1 E2 RootCollisionIn)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- **An honest validator is never slashable.** Take a validator `v` outside the adversary set at
every time up to the time after `i` steps, and two attestations `a`, `a'` of `v`, each in the sent
log after `i` steps, signed on its own or included in a block; then `a` and `a'` form no E1 pair
and no E2 pair.

Why: the protocol's half of unforgeability (`sent_unforgeable`) puts each attestation on the wire
under `v`'s own signature, which came from `v`'s tick, so both contents are in `v`'s anti-slashing
record after `i` steps; that record is consistent, and a consistent record holds no E1 and no E2
pair.

The variables:
- `M`: the model; `F`: its facts;
- `S`: the setup; `A`: the activity; `x`: the trace; `R`: the run's facts; `E`: the environment's
  facts; `i`: the step; `v`: the validator; `a`, `a'`: the two attestations.

Read aloud: whatever the adversary has put on the wire, the attestations of a validator that has
never been adversarial form no slashable pair. -/
theorem honest_never_slashable (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsNoDelivery A x ΔClockAhead ΔClockBehind GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
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
    ¬ E1 a a' ∧ ¬ E2 a a' :=
  (GoldilocksCorrectness.Record.Proofs.Executions.honest_never_slashable M F) S A x R (E.withClass _) i v hv a a'
    ha ha' hs hs'

/-- **Finalized blocks agree when no blocks held by honest validators are slashable.** When no two
blocks held by validators honest through the steps they are read at are slashable between them
(`SlashableBetween M`), the finalized block of a validator `v₁` honest through step `i` and that of
a validator `v₂` honest through step `j` are compatible (one is the other or an ancestor of the
other); or two different blocks of the two trees taken together share a root.

Why: otherwise Lemma 73 gives a block of each tree that are slashable between them, which the
premise excludes.

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed;
- `S`: the setup; `A`: the activity; `x`: the trace; `R`: the run's facts (no promise of the
  environment is read); `i`, `j`: the two steps; `v₁`, `v₂`: the two validators.

Read aloud: with no slashable evidence between the chains honest validators hold, two honest
validators never finalize conflicting blocks, unless a root collision hit their two trees. -/
theorem finalized_compatible_of_no_slashable (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    -- no two blocks held by honest validators, at any steps, are slashable between them
    (hNoSlash : ∀ (i' j' : ℕ) (w₁ w₂ : V), x.HonestThrough A i' w₁ → x.HonestThrough A j' w₂ →
      ∀ b₁ ∈ (x.st i' w₁).tree, ∀ b₂ ∈ (x.st j' w₂).tree, ¬ SlashableBetween M b₁ b₂)
    (i j : ℕ) (v₁ v₂ : V) (hH₁ : x.HonestThrough A i v₁) (hH₂ : x.HonestThrough A j v₂) :
    (x.st i v₁).finalized.compatible (x.st j v₂).finalized = true ∨
      RootCollisionIn ((x.st i v₁).tree ∪ (x.st j v₂).tree) :=
  (GoldilocksCorrectness.Record.Proofs.Executions.finalized_compatible_of_no_slashable M F Fx) S A
    x R hNoSlash i j v₁ v₂ hH₁ hH₂

end GoldilocksCorrectness.Record.Statements.Executions
