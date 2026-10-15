module
public import Model.Sts.Constants
public import Model.Sts.Interface

@[expose] public section

/-!
# The premises on the execution

The premises on the schedule (public times, honest committees, honest proposers), on the network
(synchrony, unforgeability, well-formed deliveries, diverging time) and the execution premises
bundled in `ExecutionValid`, stated over the sts framework's execution
`x : AtomicExec (protocol S) Sched`.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Schedule premises -/

/-- `t` is a whole multiple of the time unit `S.E.Δ`. -/
def PublicTime (S : Setup V) (t : Int) : Prop :=
  ∃ k : Nat, t = (k : Int) * S.E.Δ

/-- The validators honest through the instant `t`, as a `Finset`: those the adversary holds at no
    instant at or before `t`. -/
noncomputable def honestThroughSet (Sched : Schedule V) (t : Int) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => HonestThroughTime Sched t v)

/-- Every slot committee has a strict honest majority: for every slot `s`, the committee's size is
    less than twice the number of its members honest through `s`'s confirmation instant
    `Protocol.confirmation_time S.E s`. -/
def HonestCommittees (S : Setup V) (Sched : Schedule V) (I : Interface S Sched) : Prop :=
  ∀ s : Slot, (I.committee s).card <
    2 * ((I.committee s) ∩ honestThroughSet Sched (Protocol.confirmation_time S.E s)).card

/-- `s` is an opening slot, and for each of the first `C.proposerSlots` slots from `s` on, that
    slot's proposer is honest through that slot's confirmation instant. -/
def MultiProposerAt (S : Setup V) (Sched : Schedule V) (I : Interface S Sched)
    (C : Constants) (s : Slot) : Prop :=
  I.opening s ∧ ∀ k < C.proposerSlots,
    HonestThroughTime Sched (Protocol.confirmation_time S.E (s + k)) (I.proposer (s + k))

/-! ## Network premises -/

/-- After GST, every sent message reaches every awake validator within `S.E.Δ`: if a message is in
    the sent log at step `i`, step `j`'s time is at least `S.E.Δ` after both step `i`'s time and
    `S.E.t_GST`, `w` is awake at step `j`, and `w`'s store there does not exclude the message's
    payload, then the message is in `w`'s view at step `j`. -/
def Synchrony (S : Setup V) {Sched : Schedule V} (x : AtomicExec (protocol S) Sched) :
    Prop :=
  ∀ (i j : Nat) (w : V) (sm : SignedMsg V (NamedObject V)),
    sm ∈ x[i].sent →
    max (x[i].time : Int) S.E.t_GST + S.E.Δ ≤ (x[j].time : Int) →
    AtomicAwake x j w →
    NamedReceipt.excludes (x[j][w].st).st sm.msg = false →
    sm ∈ x[j][w].view

/-- A block carries exactly the Goldfish votes in its vote list and the attestations in its
    attestation list; nothing else carries anything. -/
def carries : NamedObject V → NamedObject V → Prop
  | .block B, o' =>
      (∃ u ∈ B.gf_votes, o' = .gfVote u) ∨ (∃ a ∈ B.attestations, o' = .attest a)
  | _, _ => False

/-- Signatures are unforgeable along the execution: a payload in the sent log, or carried by one,
    whose author is honest through that step is in the sent log under that author's own signature. -/
structure Unforgeability (S : Setup V) {Sched : Schedule V}
    (x : AtomicExec (protocol S) Sched) : Prop where
  /-- A logged message whose payload names an honest author is in the log under that
      author's own signature. -/
  unforgeable : ∀ (i : Nat) (sm : SignedMsg V (NamedObject V)) (u : V),
    sm ∈ x[i].sent → NamedObject.author sm.msg = some u → HonestThrough Sched x i u →
    (⟨u, sm.msg⟩ : SignedMsg V (NamedObject V)) ∈ x[i].sent
  /-- The same for every payload the logged message's payload carries. -/
  carried : ∀ (i : Nat) (sm : SignedMsg V (NamedObject V)) (o' : NamedObject V) (u : V),
    sm ∈ x[i].sent → carries sm.msg o' → NamedObject.author o' = some u →
    HonestThrough Sched x i u →
    (⟨u, o'⟩ : SignedMsg V (NamedObject V)) ∈ x[i].sent

/-- Time diverges: every clock reading `r` is at most the time of some configuration of the
    execution. -/
def TimeDiverges {S : Setup V} {Sched : Schedule V} (x : AtomicExec (protocol S) Sched) :
    Prop :=
  ∀ r : Nat, ∃ i : Nat, r ≤ x[i].time

/-- Every delivered payload passes the wire-shape test and has its dependencies present in the
    receiving validator's store. -/
structure DeliveryWellFormed (S : Setup V) {Sched : Schedule V}
    (x : AtomicExec (protocol S) Sched) : Prop where
  /-- A delivered payload is well formed on the wire. -/
  wire : ∀ (j : Nat) (w : V) (sm : SignedMsg V (NamedObject V)),
    x.lbl j = AtomicAction.deliver w sm → NamedReceipt.wellFormed S sm.msg = true
  /-- A delivered payload's dependencies are in the receiving store. -/
  deps : ∀ (j : Nat) (w : V) (sm : SignedMsg V (NamedObject V)),
    x.lbl j = AtomicAction.deliver w sm →
    NamedReceipt.depsPresent (x[j][w].st).st sm.msg = true

/-- An honest proposer's root is new: at the tick step at slot `s`'s proposal instant, if `s`'s
    proposer is held by the adversary at no instant up to then, no block the proposer holds at that
    step has the root `(S.node (S.E.proposer s)).new_root s` it gives its own proposal. -/
def HonestRootsNew (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched) :
    Prop :=
  ∀ (k τ : Nat) (s : Slot), x.lbl k = AtomicAction.tickAllAwake τ →
    (τ : Int) = Protocol.proposal_time S.E s →
    (∀ t' ≤ (τ : Int), S.E.proposer s ∉ Sched.adv t') →
    ∀ B ∈ Read.blocks x[k][S.E.proposer s].st, B.root ≠ (S.node (S.E.proposer s)).new_root s

/-- The execution premises: unforgeable signatures, well-formed deliveries, the interface's hash
    idealization, and new roots for honest proposals. -/
structure ExecutionValid (S : Setup V) (Sched : Schedule V) (I : Interface S Sched)
    (x : AtomicExec (protocol S) Sched) : Prop extends Unforgeability S x,
      DeliveryWellFormed S x where
  /-- The hash idealization the protocol assumes on the blocks of the execution. -/
  idealization : I.idealization x
  /-- An honest proposer's root is new. -/
  honestRootsNew : HonestRootsNew S Sched x

end DecoupledConsensusModel.Sts
