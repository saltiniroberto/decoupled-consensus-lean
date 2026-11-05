module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.HonestAccountable

@[expose] public section

/-!
# HonestAccountableStatements, over a model

The statements of `GoldilocksCorrectness/Statements/Executions/HonestAccountableStatements.lean`,
over a model `M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: the honest
corollaries of accountable safety, Lemmas 74, 75, 76 and 76 (b). Each is the theorem of the same
name of `Record/Restated/Proofs/Executions/HonestAccountable.lean`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Statements.Executions

open GoldilocksCorrectness.Record.Statements.Routines (JustificationCertOn)
open GoldilocksCorrectness.Statements.Executions (Vocab.goldilocks)

open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Statements.Routines (RootCollisionIn)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- **Lemma 74, honest attestations are recorded.** Under unforgeability, take a block `B` that a
validator `w` holds after `j` steps, and an attestation `a` included in `B` or in an ancestor of
`B`, whose validator `a.val_index` is outside the adversary set at every time up to the time after
`j` steps; then the content of `a` is in that validator's anti-slashing record after `j` steps.

Why: the block of the chain that includes `a` is held too, and is not the genesis block, so `w`
put it on the wire at an earlier step; unforgeability puts `a` on the wire under its own
validator's signature by then, and that message came from the validator's tick, whose record
holds the content of `a` from then on. No honesty of `w` is needed: an adversarial validator's
node state changes at no step, so every block of a tree got there through a step of its holder.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `hU`: unforgeability; `j`: the step;
  `w`: the holder; `B`: the block; `a`: the attestation.



Read aloud: an attestation included on the chain of a block some validator holds, its validator
never in the adversary set up to now, is in that validator's own record. -/
theorem lem74_honest_attestations_recorded (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (j : ℕ) (w : V)
    (B : Block V) (a : Attestation V)
    -- `w`'s tree holds `B` after `j` steps
    (hB : B ∈ (x.st j w).tree)
    -- `a` is included in `B` or in an ancestor of `B`
    (ha : M.on_chain a B = true)
    (hH : x.HonestThrough A j a.val_index) :
    a.content ∈ (x.st j a.val_index).sentAttestations :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem74_honest_attestations_recorded M F) S A x R E
    j w B a hB ha hH

/-- **Lemma 75, honest finalized blocks are compatible.** Under unforgeability, and when fewer
than a third of the validators have been in the adversary set at some time up to the later of the
times after `i` and after `j` steps, the finalized block of `p₁`'s node state after `i` steps and
that of `p₂`'s node state after `j` steps are compatible (one is the other or an ancestor of the
other); or two different blocks of the two trees taken together share a root.

Why: otherwise Lemma 73 gives at least `2q − n` validators each holding two attestations, one on a
chain of each tree, meeting E1 or E2. Such a set has a member never in the adversary set up to the
later time (Lemma 65 (b)); both its attestations are in its record by Lemma 74, and a consistent
record holds no E1 and no E2 pair.

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `hU`: unforgeability; `i`, `j`: the
  two steps; `p₁`, `p₂`: the two validators.



Read aloud: when signatures are unforgeable and fewer than a third of the validators have been
adversarial up to the later of the two times, any two finalized blocks are compatible, or two
different blocks of the two trees share a root. -/
theorem lem75_honest_finalized_compatible (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (i j : ℕ) (p₁ p₂ : V)
    -- fewer than a third of the validators have been in the adversary set up to the later time
    (hAdv : A.AdversaryFewerThanThirdUntil x (validator_count V)
      (max (x.time i) (x.time j))) :
    (x.st i p₁).finalized.compatible (x.st j p₂).finalized = true ∨
      RootCollisionIn ((x.st i p₁).tree ∪ (x.st j p₂).tree) :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem75_honest_finalized_compatible M F Fx) S A
    x R E i j p₁ p₂ hAdv

/-- **Lemma 76, one justification per height among honest validators.** Under unforgeability, and
when fewer than a third of the validators have been in the adversary set at some time up to the
later of the times after `i` and after `j` steps, two justification certificates at one height
`h`, one for `T` on the chain of a block `B₁` that `p₁` holds after `i` steps and one for `T'` on
the chain of a block `B₂` that `p₂` holds after `j` steps, name blocks with the same root.

Why: otherwise Lemma 71 gives at least `2q − n` validators each with two target votes at `h` for
different blocks, one on each chain; such a set has a member never in the adversary set up to the
later time, whose record holds both by Lemma 74, and a consistent record holds no E2 pair.

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `hU`: unforgeability; `i`, `j`: the
  two steps; `p₁`, `p₂`: the two validators; `B₁`, `B₂`: the two held blocks; `h`: the height;
  `T`, `T'`: the two justified blocks.



Read aloud: under the same two assumptions, two justification certificates at one height, on the
chains of two held blocks, name blocks with the same root. -/
theorem lem76_honest_one_justification (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (i j : ℕ) (p₁ p₂ : V)
    -- fewer than a third of the validators have been in the adversary set up to the later time
    (hAdv : A.AdversaryFewerThanThirdUntil x (validator_count V)
      (max (x.time i) (x.time j)))
    (B₁ B₂ : Block V)
    -- `p₁`'s tree holds `B₁` after `i` steps
    (hB₁ : B₁ ∈ (x.st i p₁).tree)
    -- `p₂`'s tree holds `B₂` after `j` steps
    (hB₂ : B₂ ∈ (x.st j p₂).tree)
    (h : Height) (T T' : Block V)
    -- a justification certificate at `h` for `T` on the chain of `B₁`
    (hJ : JustificationCertOn M B₁ h T)
    -- a justification certificate at `h` for `T'` on the chain of `B₂`
    (hJ' : JustificationCertOn M B₂ h T') :
    T.root = T'.root :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem76_honest_one_justification M F Fx) S A x R E
    i j p₁ p₂ hAdv B₁ B₂ hB₁ hB₂ h T T' hJ hJ'

/-- **Lemma 76 (b), one justified block per height among honest validators.** Under the
assumptions of Lemma 76, when the two justified blocks `T` and `T'` are themselves in one of the
two trees, they are one block, or two different blocks of the two trees taken together share a
root.

Why: by Lemma 76 the two blocks have the same root; when they differ, they are two different
blocks of the two trees sharing a root.

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `hU`: unforgeability; `i`, `j`: the
  two steps; `p₁`, `p₂`: the two validators; `B₁`, `B₂`: the two held blocks; `h`: the height;
  `T`, `T'`: the two justified blocks.



Read aloud: two held blocks justified at one height on the chains of two held blocks are one
block, or two different held blocks share a root. -/
theorem lem76b_honest_one_justification_block (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (i j : ℕ) (p₁ p₂ : V)
    -- fewer than a third of the validators have been in the adversary set up to the later time
    (hAdv : A.AdversaryFewerThanThirdUntil x (validator_count V)
      (max (x.time i) (x.time j)))
    (B₁ B₂ : Block V)
    -- `p₁`'s tree holds `B₁` after `i` steps
    (hB₁ : B₁ ∈ (x.st i p₁).tree)
    -- `p₂`'s tree holds `B₂` after `j` steps
    (hB₂ : B₂ ∈ (x.st j p₂).tree)
    (h : Height) (T T' : Block V)
    -- a justification certificate at `h` for `T` on the chain of `B₁`
    (hJ : JustificationCertOn M B₁ h T)
    -- a justification certificate at `h` for `T'` on the chain of `B₂`
    (hJ' : JustificationCertOn M B₂ h T')
    -- `T` is in one of the two trees
    (hT : T ∈ (x.st i p₁).tree ∪ (x.st j p₂).tree)
    -- `T'` is in one of the two trees
    (hT' : T' ∈ (x.st i p₁).tree ∪ (x.st j p₂).tree) :
    T = T' ∨ RootCollisionIn ((x.st i p₁).tree ∪ (x.st j p₂).tree) :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem76b_honest_one_justification_block M F Fx) S
    A x R E i j p₁ p₂ hAdv B₁ B₂ hB₁ hB₂ h T T' hJ hJ' hT hT'

end GoldilocksCorrectness.Record.Statements.Executions

