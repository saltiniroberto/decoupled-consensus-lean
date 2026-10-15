import Model.Sts.Conditions
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Sts_Interface
import Model.Record.Wiring

/-!
# The conditions on an execution

Honest committees and proposers, unforgeable signatures, diverging time, well-formed deliveries, new
roots for honest proposals, and the execution premises that bundle them, stated over a model
`M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Every slot's committee has a strict majority of members honest through the slot's confirmation
    instant `M.confirmation_time S.E s`. -/
def HonestCommittees (M : Record.Model V) (S : Setup V) (Sched : Schedule V) (I : Restated.Interface M S Sched) : Prop :=
  ∀ s : Slot, (I.committee s).card <
    2 * ((I.committee s) ∩ honestThroughSet Sched (M.confirmation_time S.E s)).card

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- `s` opens a period, and each of the first `C.proposerSlots` slots from `s` on has a proposer
    honest through that slot's confirmation instant. -/
def MultiProposerAt (M : Record.Model V) (S : Setup V) (Sched : Schedule V) (I : Restated.Interface M S Sched)
    (C : Constants) (s : Slot) : Prop :=
  I.opening s ∧ ∀ k < C.proposerSlots,
    HonestThroughTime Sched (M.confirmation_time S.E (s + k)) (I.proposer (s + k))

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Signatures are unforgeable along the execution `x`. -/
structure Unforgeability (M : Record.Model V) (S : Setup V) {Sched : Schedule V}
    (x : AtomicExec (Record.protocolOf M S) Sched) : Prop where
  /-- A message in the sent log whose payload names an author honest through that step is in the
      sent log under that author's own signature. -/
  unforgeable : ∀ (i : Nat) (sm : SignedMsg V (NamedObject V)) (u : V),
    sm ∈ x[i].sent → NamedObject.author sm.msg = some u → Restated.HonestThrough M Sched x i u →
    (⟨u, sm.msg⟩ : SignedMsg V (NamedObject V)) ∈ x[i].sent
  /-- A payload carried by a message in the sent log, naming an author honest through that step, is
      in the sent log under that author's own signature. -/
  carried : ∀ (i : Nat) (sm : SignedMsg V (NamedObject V)) (o' : NamedObject V) (u : V),
    sm ∈ x[i].sent → carries sm.msg o' → NamedObject.author o' = some u →
    Restated.HonestThrough M Sched x i u →
    (⟨u, o'⟩ : SignedMsg V (NamedObject V)) ∈ x[i].sent

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Every clock reading is at most the real time of some configuration of `x`. -/
def TimeDiverges (M : Record.Model V) {S : Setup V} {Sched : Schedule V} (x : AtomicExec (Record.protocolOf M S) Sched) :
    Prop :=
  ∀ r : Nat, ∃ i : Nat, r ≤ x[i].time

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Every payload a step of the execution delivers passes the wire test and the dependency test. -/
structure DeliveryWellFormed (M : Record.Model V) (S : Setup V) {Sched : Schedule V}
    (x : AtomicExec (Record.protocolOf M S) Sched) : Prop where
  /-- A delivered payload is well formed on the wire. -/
  wire : ∀ (j : Nat) (w : V) (sm : SignedMsg V (NamedObject V)),
    x.lbl j = AtomicAction.deliver w sm →
    (∀ B : NamedBlock V, sm.msg = NamedObject.block B →
      (∀ u ∈ B.gf_votes, u.slot + 1 = B.slot) ∧
        (∀ u ∈ B.gf_support_votes, u ∈ B.gf_votes) ∧
        (∀ u ∈ B.gf_votes, u.val_index ∈ S.E.committee u.slot)) ∧
    (∀ u : GoldfishVote V, sm.msg = NamedObject.gfVote u → u.val_index ∈ S.E.committee u.slot)
  /-- A delivered payload's dependencies are in the receiving store. -/
  deps : ∀ (j : Nat) (w : V) (sm : SignedMsg V (NamedObject V)),
    x.lbl j = AtomicAction.deliver w sm →
    ∀ B : NamedBlock V, sm.msg = NamedObject.block B → B.parent ∈ (x[j][w].st).st.bodies

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- An honest proposer's root is new: at the tick step at slot `s`'s proposal instant, if the
    adversary has held `s`'s proposer at no instant up to then, no block the proposer holds has the
    root `(S.node (S.E.proposer s)).new_root s`. -/
def HonestRootsNew (M : Record.Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) : Prop :=
  ∀ (k τ : Nat) (s : Slot), x.lbl k = AtomicAction.tickAllAwake τ →
    (τ : Int) = M.proposal_time S.E s →
    (∀ t' ≤ (τ : Int), S.E.proposer s ∉ Sched.adv t') →
    ∀ B ∈ Restated.Read.blocks M x[k][S.E.proposer s].st,
      B.root ≠ (S.node (S.E.proposer s)).new_root s

/-- The premises on an execution other than the network: unforgeable signatures, well-formed
    deliveries, the interface's hash idealization, and new roots for honest proposers. -/
structure ExecutionValid (M : Record.Model V) (S : Setup V) (Sched : Schedule V) (I : Restated.Interface M S Sched)
    (x : AtomicExec (Record.protocolOf M S) Sched) : Prop extends Restated.Unforgeability M S x,
      Restated.DeliveryWellFormed M S x where
  /-- The interface's hash idealization holds of the execution's blocks. -/
  idealization : I.idealization x
  /-- An honest proposer's root is new. -/
  honestRootsNew : Restated.HonestRootsNew M S Sched x

end

end DecoupledConsensusModel.Sts.Restated
