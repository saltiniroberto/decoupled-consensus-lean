module
public import GoldilocksCorrectness.Proofs.Executions.HonestAccountable

@[expose] public section

/-!
# The honest corollaries of accountable safety

The audited statements about the blocks honest validators finalize and justify, under
`Unforgeability Vocab.goldilocks Sched x.toTrace` and fewer than a third of the validators in the adversary set up to the
compared steps, each proved in `GoldilocksCorrectness/Proofs/Executions/HonestAccountable.lean`:

- Lemma 74: an attestation included on the chain of a held block, its validator never in the
  adversary set up to the step, has its content in that validator's own record;
- Lemma 75: two node states read at two steps finalize compatible blocks, or two different blocks
  of their two trees share a root;
- Lemma 76: two justification certificates at one height on the chains of two held blocks name
  blocks with the same root;
- Lemma 76 (b): when the two justified blocks are held, they are one block, or two different held
  blocks share a root.


-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec Schedule)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Routines (JustificationCertOn RootCollisionIn)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

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
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `hU`: unforgeability; `j`: the step;
  `w`: the holder; `B`: the block; `a`: the attestation.



Read aloud: an attestation included on the chain of a block some validator holds, its validator
never in the adversary set up to now, is in that validator's own record. -/
theorem lem74_honest_attestations_recorded (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace) (j : ℕ) (w : V)
    (B : Block V) (a : Attestation V)
    -- `w`'s tree holds `B` after `j` steps
    (hB : B ∈ (x[j][w].st).S.T)
    -- `a` is included in `B` or in an ancestor of `B`
    (ha : on_chain a B = true)
    (hH : HonestThrough x j a.val_index) :
    a.content ∈ (x[j][a.val_index].st).Λ.sent :=
  GoldilocksCorrectness.Proofs.Executions.lem74_honest_attestations_recorded S Sched x hU j w B a
    hB ha hH

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
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `hU`: unforgeability; `i`, `j`: the
  two steps; `p₁`, `p₂`: the two validators.



Read aloud: when signatures are unforgeable and fewer than a third of the validators have been
adversarial up to the later of the two times, any two finalized blocks are compatible, or two
different blocks of the two trees share a root. -/
theorem lem75_honest_finalized_compatible (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace) (i j : ℕ) (p₁ p₂ : V)
    -- fewer than a third of the validators have been in the adversary set up to the later time
    (hAdv : AdversaryFewerThanThirdUntil Sched (validator_count V) (max (x[i].time : Int) (x[j].time : Int))) :
    (x[i][p₁].st).S.F.compatible (x[j][p₂].st).S.F = true ∨
      RootCollisionIn ((x[i][p₁].st).S.T ∪ (x[j][p₂].st).S.T) :=
  GoldilocksCorrectness.Proofs.Executions.lem75_honest_finalized_compatible S Sched x hU i j p₁ p₂
    hAdv

/-- **Lemma 76, one justification per height among honest validators.** Under unforgeability, and
when fewer than a third of the validators have been in the adversary set at some time up to the
later of the times after `i` and after `j` steps, two justification certificates at one height
`h`, one for `T` on the chain of a block `B₁` that `p₁` holds after `i` steps and one for `T'` on
the chain of a block `B₂` that `p₂` holds after `j` steps, name blocks with the same root.

Why: otherwise Lemma 71 gives at least `2q − n` validators each with two target votes at `h` for
different blocks, one on each chain; such a set has a member never in the adversary set up to the
later time, whose record holds both by Lemma 74, and a consistent record holds no E2 pair.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `hU`: unforgeability; `i`, `j`: the
  two steps; `p₁`, `p₂`: the two validators; `B₁`, `B₂`: the two held blocks; `h`: the height;
  `T`, `T'`: the two justified blocks.



Read aloud: under the same two assumptions, two justification certificates at one height, on the
chains of two held blocks, name blocks with the same root. -/
theorem lem76_honest_one_justification (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace) (i j : ℕ) (p₁ p₂ : V)
    -- fewer than a third of the validators have been in the adversary set up to the later time
    (hAdv : AdversaryFewerThanThirdUntil Sched (validator_count V) (max (x[i].time : Int) (x[j].time : Int)))
    (B₁ B₂ : Block V)
    -- `p₁`'s tree holds `B₁` after `i` steps
    (hB₁ : B₁ ∈ (x[i][p₁].st).S.T)
    -- `p₂`'s tree holds `B₂` after `j` steps
    (hB₂ : B₂ ∈ (x[j][p₂].st).S.T)
    (h : Height) (T T' : Block V)
    -- a justification certificate at `h` for `T` on the chain of `B₁`
    (hJ : JustificationCertOn B₁ h T)
    -- a justification certificate at `h` for `T'` on the chain of `B₂`
    (hJ' : JustificationCertOn B₂ h T') :
    T.root = T'.root :=
  GoldilocksCorrectness.Proofs.Executions.lem76_honest_one_justification S Sched x hU i j p₁ p₂
    hAdv B₁ B₂ hB₁ hB₂ h T T' hJ hJ'

/-- **Lemma 76 (b), one justified block per height among honest validators.** Under the
assumptions of Lemma 76, when the two justified blocks `T` and `T'` are themselves in one of the
two trees, they are one block, or two different blocks of the two trees taken together share a
root.

Why: by Lemma 76 the two blocks have the same root; when they differ, they are two different
blocks of the two trees sharing a root.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `hU`: unforgeability; `i`, `j`: the
  two steps; `p₁`, `p₂`: the two validators; `B₁`, `B₂`: the two held blocks; `h`: the height;
  `T`, `T'`: the two justified blocks.



Read aloud: two held blocks justified at one height on the chains of two held blocks are one
block, or two different held blocks share a root. -/
theorem lem76b_honest_one_justification_block (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace) (i j : ℕ) (p₁ p₂ : V)
    -- fewer than a third of the validators have been in the adversary set up to the later time
    (hAdv : AdversaryFewerThanThirdUntil Sched (validator_count V) (max (x[i].time : Int) (x[j].time : Int)))
    (B₁ B₂ : Block V)
    -- `p₁`'s tree holds `B₁` after `i` steps
    (hB₁ : B₁ ∈ (x[i][p₁].st).S.T)
    -- `p₂`'s tree holds `B₂` after `j` steps
    (hB₂ : B₂ ∈ (x[j][p₂].st).S.T)
    (h : Height) (T T' : Block V)
    -- a justification certificate at `h` for `T` on the chain of `B₁`
    (hJ : JustificationCertOn B₁ h T)
    -- a justification certificate at `h` for `T'` on the chain of `B₂`
    (hJ' : JustificationCertOn B₂ h T')
    -- `T` is in one of the two trees
    (hT : T ∈ (x[i][p₁].st).S.T ∪ (x[j][p₂].st).S.T)
    -- `T'` is in one of the two trees
    (hT' : T' ∈ (x[i][p₁].st).S.T ∪ (x[j][p₂].st).S.T) :
    T = T' ∨ RootCollisionIn ((x[i][p₁].st).S.T ∪ (x[j][p₂].st).S.T) :=
  GoldilocksCorrectness.Proofs.Executions.lem76b_honest_one_justification_block S Sched x hU i j
    p₁ p₂ hAdv B₁ B₂ hB₁ hB₂ h T T' hJ hJ' hT hT'

end GoldilocksCorrectness.Statements.Executions
