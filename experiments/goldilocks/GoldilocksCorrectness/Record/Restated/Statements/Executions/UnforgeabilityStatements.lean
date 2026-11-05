module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Unforgeability

@[expose] public section

/-!
# UnforgeabilityStatements, over a model

The statements of `GoldilocksCorrectness/Statements/Executions/UnforgeabilityStatements.lean`, over
a model `M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: under `Unforgeability`,
an attestation or a Goldfish vote of an honest validator on the wire came from that validator's
tick, and the votes are cast by their owners. Each is the theorem of the same name of
`Record/Restated/Proofs/Executions/Unforgeability.lean`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Statements.Executions

open GoldilocksCorrectness.Statements.Executions (Vocab.goldilocks author)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- **An honest attestation comes from its validator's tick.** Under unforgeability, an
attestation `a` on the wire after `k` steps under the signature of its own validator
`a.val_index`, that validator outside the adversary set at every time up to the time after `k`
steps, entered the wire at an earlier step `k'` that is the tick of every awake validator at some
time `t`; and after that step the content of `a` is in that validator's anti-slashing record.

Why: take the first step after which the message is on the wire. A delivery re-sends, under the
receiver's signature, only objects of a message already on the wire, which unforgeability puts
there under `a.val_index`'s signature already; an adversarial send is signed by a validator in
the adversary set; a forward re-sends a message already on the wire. So the step is a tick, whose
attestation is the one `create_attestation` builds, and the record the tick leaves holds its
content (Lemma 49).

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `hU`: unforgeability; `k`: the step;
  `a`: the attestation;
- `k'`: the step of the tick; `t`: its time.



Read aloud: an attestation on the wire under its own validator's signature, that validator never
in the adversary set up to now, was sent by that validator's tick, and its content is in that
validator's record from then on. -/
theorem attestation_from_own_tick (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (k : ℕ) (a : Attestation V)
    -- `a`'s validator's signed message with the attestation `a` is on the wire after `k` steps
    (hm : (⟨a.val_index, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent k)
    (hH : x.HonestThrough A k a.val_index) :
    ∃ k' < k, ∃ t : ℕ, x.lbl k' = Event.tick a.val_index t ∧
      (⟨a.val_index, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (k' + 1) - x.sent k' ∧
      a.content ∈ (x.st (k' + 1) a.val_index).sentAttestations :=
  (GoldilocksCorrectness.Record.Proofs.Executions.attestation_from_own_tick M F) S A x R E k a hm
    hH

/-- **An honest Goldfish vote comes from its validator's tick.** Under unforgeability, a Goldfish
vote `vote` on the wire after `k` steps under the signature of its own validator
`vote.val_index`, that validator outside the adversary set at every time up to the time after `k`
steps, entered the wire at an earlier step `k'` that is the tick of every awake validator at some
time `t`.

Why: as for an attestation; the first step after which the message is on the wire is a tick.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `hU`: unforgeability; `k`: the step;
  `vote`: the Goldfish vote;
- `k'`: the step of the tick; `t`: its time.



Read aloud: a Goldfish vote on the wire under its own validator's signature, that validator never
in the adversary set up to now, was sent by that validator's tick. -/
theorem vote_from_own_tick (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (k : ℕ) (vote : GoldfishVote V)
    -- `vote`'s validator's signed message with the vote is on the wire after `k` steps
    (hm : (⟨vote.val_index, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent k)
    (hH : x.HonestThrough A k vote.val_index) :
    ∃ k' < k, ∃ t : ℕ, x.lbl k' = Event.tick vote.val_index t ∧
      (⟨vote.val_index, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (k' + 1) - x.sent k' :=
  (GoldilocksCorrectness.Record.Proofs.Executions.vote_from_own_tick M F) S A x R E k vote hm hH

/-- **`VotesCastByOwner` from unforgeability.** When signatures are unforgeable and corruption is
permanent, every message a step puts on the wire that carries a Goldfish vote, as its object or in
the `votes` of its block, whose validator is outside the adversary set at the time the step starts
from, descends from that validator's own tick at a step no later than it (`VotesCastByOwner`).

Why: by permanent corruption the vote's validator was outside the adversary set at every earlier
time. A step other than a tick keeps the time, so unforgeability puts the vote's own signed
message on the wire after it, and that message came from the validator's tick. A tick puts on the
wire its own Goldfish vote, of the ticking validator, or its proposal, whose votes were in its
pool and so on the wire before the step.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `hU`: unforgeability; `hMono`:
  permanent corruption.



Read aloud: when signatures are unforgeable and corruption is permanent, every copy of a Goldfish
vote on the wire whose validator is honest at the step descends from that validator's own
tick. -/
theorem votesCastByOwner_of_unforgeability (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) : VotesCastByOwner M A x :=
  (GoldilocksCorrectness.Record.Proofs.Executions.votesCastByOwner_of_unforgeability M F) S A x R
    E

end GoldilocksCorrectness.Record.Statements.Executions

