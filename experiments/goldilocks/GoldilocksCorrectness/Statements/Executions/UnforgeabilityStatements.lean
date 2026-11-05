module
public import GoldilocksCorrectness.Proofs.Executions.Unforgeability

@[expose] public section

/-!
# The statements about unforgeability

The audited statements about the objects of honest validators on the wire, under
`Unforgeability Vocab.goldilocks Sched x.toTrace`, each proved in `GoldilocksCorrectness/Proofs/Executions/Unforgeability.lean`:

- an attestation on the wire under its own validator's signature, that validator outside the
  adversary set up to the step, came from that validator's tick, and its content is in that
  validator's record after the tick;
- a Goldfish vote on the wire under its own validator's signature, that validator outside the
  adversary set up to the step, came from that validator's tick;
- `VotesCastByOwner` follows from unforgeability and permanent corruption.


-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

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
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `hU`: unforgeability; `k`: the step;
  `a`: the attestation;
- `k'`: the step of the tick; `t`: its time.



Read aloud: an attestation on the wire under its own validator's signature, that validator never
in the adversary set up to now, was sent by that validator's tick, and its content is in that
validator's record from then on. -/
theorem attestation_from_own_tick (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace) (k : ℕ) (a : Attestation V)
    -- `a`'s validator's signed message with the attestation `a` is on the wire after `k` steps
    (hm : (⟨a.val_index, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[k].sent)
    (hH : HonestThrough x k a.val_index) :
    ∃ k' < k, ∃ t : ℕ, x.lbl k' = AtomicAction.tickAllAwake t ∧
      (⟨a.val_index, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈
        x[k' + 1].sent - x[k'].sent ∧
      a.content ∈ (x[k' + 1][a.val_index].st).Λ.sent :=
  GoldilocksCorrectness.Proofs.Executions.attestation_from_own_tick S Sched x hU k a hm hH

/-- **An honest Goldfish vote comes from its validator's tick.** Under unforgeability, a Goldfish
vote `vote` on the wire after `k` steps under the signature of its own validator
`vote.val_index`, that validator outside the adversary set at every time up to the time after `k`
steps, entered the wire at an earlier step `k'` that is the tick of every awake validator at some
time `t`.

Why: as for an attestation; the first step after which the message is on the wire is a tick.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `hU`: unforgeability; `k`: the step;
  `vote`: the Goldfish vote;
- `k'`: the step of the tick; `t`: its time.



Read aloud: a Goldfish vote on the wire under its own validator's signature, that validator never
in the adversary set up to now, was sent by that validator's tick. -/
theorem vote_from_own_tick (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace) (k : ℕ) (vote : GoldfishVote V)
    -- `vote`'s validator's signed message with the vote is on the wire after `k` steps
    (hm : (⟨vote.val_index, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x[k].sent)
    (hH : HonestThrough x k vote.val_index) :
    ∃ k' < k, ∃ t : ℕ, x.lbl k' = AtomicAction.tickAllAwake t ∧
      (⟨vote.val_index, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x[k' + 1].sent - x[k'].sent :=
  GoldilocksCorrectness.Proofs.Executions.vote_from_own_tick S Sched x hU k vote hm hH

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
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `hU`: unforgeability; `hMono`:
  permanent corruption.



Read aloud: when signatures are unforgeable and corruption is permanent, every copy of a Goldfish
vote on the wire whose validator is honest at the step descends from that validator's own
tick. -/
theorem votesCastByOwner_of_unforgeability (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hMono : Sched.MonotoneCorruption) : VotesCastByOwner S Sched x :=
  GoldilocksCorrectness.Proofs.Executions.votesCastByOwner_of_unforgeability S Sched x hU hMono

end GoldilocksCorrectness.Statements.Executions
