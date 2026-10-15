import Proofs.Instance.ObjectConstants
import Sts
import Model.Sts

/-!
# The spec's wiring over the model's object types

The spec's setup read from a `DecoupledConsensusModel.Execution.Setup` (`Setup.toSpec`), the spec's
dispatch on a `DecoupledConsensusModel.Execution.NamedObject`, the maps of the framework's messages,
views, events and step results, and `protocolOnVocabularyObjects S`, the spec's protocol at
`Setup.toSpec S` over that object type.
-/

set_option autoImplicit false

namespace SpecRecord

open Framework.StsMultisetLog
open Spec (NodeState Config Provisional External)

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The setup -/

/-- The spec's setup read from the set-up `S`: the parameters `Config.toSpec S.E S.hc S.cfg`, the
    provisional values `Provisional.toSpec S.E`, and the external values `External.toSpec S`. -/
def Setup.toSpec (S : DecoupledConsensusModel.Execution.Setup V) : Spec.Sts.Setup V where
  C := Config.toSpec S.E S.hc S.cfg
  P := Provisional.toSpec S.E
  X := External.toSpec S

/-- `Setup.toSpec` at `Setup.alwaysAwake S` is `Setup.toSpec S`. -/
@[simp] theorem Setup.toSpec_alwaysAwake (S : DecoupledConsensusModel.Execution.Setup V) :
    Setup.toSpec (DecoupledConsensusModel.Sts.Setup.alwaysAwake S) = Setup.toSpec S := rfl

/-! ## The dispatch and the re-sent objects -/

/-- The node state `n` after the object `o` is delivered to it: `Spec.Sts.receive` at the parameters
    of `Setup.toSpec S`, on `NamedObject.toSpec o`. -/
def receiveNamedObject (S : DecoupledConsensusModel.Execution.Setup V) (n : NodeState V)
    (o : DecoupledConsensusModel.Execution.NamedObject V) : NodeState V :=
  Spec.Sts.receive (Setup.toSpec S).C (Setup.toSpec S).P n
    (Spec.NamedObject.toSpec o)

/-- `receiveNamedObject S n o.toProof` is `Spec.Sts.receive` at the parameters of `Setup.toSpec S`,
    on `n` and `o`. -/
@[simp] theorem receiveNamedObject_toProof (S : DecoupledConsensusModel.Execution.Setup V)
    (n : NodeState V) (o : Spec.NamedObject V) :
    receiveNamedObject S n o.toProof =
      Spec.Sts.receive (Setup.toSpec S).C (Setup.toSpec S).P n o := by
  simp only [receiveNamedObject, Spec.NamedObject.toSpec_toProof]

omit [DecidableEq V] [Fintype V] in
/-- Mapping `Spec.Sts.relayedObjects o` by `toProof` gives
    `DecoupledConsensusModel.Sts.relayedObjects o.toProof`. -/
theorem toProof_relayedObjects (o : Spec.NamedObject V) :
    (Spec.Sts.relayedObjects o).map Spec.NamedObject.toProof =
      DecoupledConsensusModel.Sts.relayedObjects o.toProof := by
  cases o with
  | block B =>
      simp only [Spec.Sts.relayedObjects, DecoupledConsensusModel.Sts.relayedObjects,
        Spec.NamedObject.toProof, Multiset.map_add, Multiset.map_singleton,
        Multiset.map_coe, List.map_map, Spec.Block.toProofNamed_gf_votes,
        Spec.Block.toProofNamed_attestations]
      rfl
  | gfVote vote => rfl
  | attest a => rfl

/-! ## The framework's types, mapped -/

/-- The signed message `m` as a signed message over the spec's objects: the same signer, the object
    mapped by `NamedObject.toSpec`. -/
def SignedMsg.toSpec (m : SignedMsg V (DecoupledConsensusModel.Execution.NamedObject V)) :
    SignedMsg V (Spec.NamedObject V) :=
  ⟨m.sender, Spec.NamedObject.toSpec m.msg⟩

omit [DecidableEq V] [Fintype V] in
/-- `SignedMsg.toSpec` is injective. -/
theorem SignedMsg.toSpec_injective :
    Function.Injective
      (SignedMsg.toSpec : SignedMsg V (DecoupledConsensusModel.Execution.NamedObject V) →
        SignedMsg V (Spec.NamedObject V)) := by
  intro a b h
  cases a with
  | mk sa ma =>
    cases b with
    | mk sb mb =>
      simp only [SignedMsg.toSpec, SignedMsg.mk.injEq] at h
      obtain ⟨hs, hm⟩ := h
      have hm' := congrArg Spec.NamedObject.toProof hm
      simp only [Spec.NamedObject.toProof_toSpec] at hm'
      rw [hs, hm']

/-- The view `view` as a view over the spec's objects, each signed message mapped by
    `SignedMsg.toSpec`. -/
def View.toSpec (view : View V (DecoupledConsensusModel.Execution.NamedObject V)) :
    View V (Spec.NamedObject V) :=
  view.map ⟨SignedMsg.toSpec, SignedMsg.toSpec_injective⟩

/-- The framework event `e` as an event over the spec's objects: the same event, a delivered message
    mapped by `SignedMsg.toSpec`. -/
def Event.toSpec :
    Event V (DecoupledConsensusModel.Execution.NamedObject V) Empty →
      Event V (Spec.NamedObject V) Empty
  | .tick => .tick
  | .recv m => .recv (SignedMsg.toSpec m)
  | .wake => .wake
  | .custom ev => .custom ev

/-- The result `res` as a result over `DecoupledConsensusModel.Execution.NamedObject V`: the same
    node state, each object sent mapped by `NamedObject.toProof`. -/
def NodeStepResult.toProof (res : NodeStepResult (NodeState V) (Spec.NamedObject V)) :
    NodeStepResult (NodeState V) (DecoupledConsensusModel.Execution.NamedObject V) :=
  { state := res.state, send := res.send.map Spec.NamedObject.toProof }

/-- The result `res` as a result over the spec's objects: the same node state, each object sent
    mapped by `NamedObject.toSpec`. -/
def NodeStepResult.toSpec
    (res : NodeStepResult (NodeState V) (DecoupledConsensusModel.Execution.NamedObject V)) :
    NodeStepResult (NodeState V) (Spec.NamedObject V) :=
  { state := res.state, send := res.send.map Spec.NamedObject.toSpec }

omit [DecidableEq V] [Fintype V] in
/-- `NodeStepResult.toSpec res.toProof` is `res`. -/
@[simp] theorem NodeStepResult.toSpec_toProof
    (res : NodeStepResult (NodeState V) (Spec.NamedObject V)) :
    NodeStepResult.toSpec (NodeStepResult.toProof res) = res := by
  cases res
  simp only [NodeStepResult.toSpec, NodeStepResult.toProof, Multiset.map_map,
    Function.comp_def, Spec.NamedObject.toSpec_toProof, Multiset.map_id']

omit [DecidableEq V] [Fintype V] in
/-- `NodeStepResult.toProof (NodeStepResult.toSpec res)` is `res`. -/
@[simp] theorem NodeStepResult.toProof_toSpec
    (res : NodeStepResult (NodeState V) (DecoupledConsensusModel.Execution.NamedObject V)) :
    NodeStepResult.toProof (NodeStepResult.toSpec res) = res := by
  cases res
  simp only [NodeStepResult.toSpec, NodeStepResult.toProof, Multiset.map_map,
    Function.comp_def, Spec.NamedObject.toProof_toSpec, Multiset.map_id']

/-! ## The spec's protocol over the model's object type -/

/-- The reaction of the node state `n` to the event `e` at the clock reading `t`:
    `Spec.Sts.reaction` at `Setup.toSpec S` and `Event.toSpec e`, its result mapped by
    `NodeStepResult.toProof`. -/
def reactionOnVocabularyObjects (S : DecoupledConsensusModel.Execution.Setup V) (n : NodeState V)
    (t : Int) (e : Event V (DecoupledConsensusModel.Execution.NamedObject V) Empty) :
    NodeStepResult (NodeState V) (DecoupledConsensusModel.Execution.NamedObject V) :=
  NodeStepResult.toProof (Spec.Sts.reaction (Setup.toSpec S) n t (Event.toSpec e))

/-- On a delivery of `m`, `reactionOnVocabularyObjects` runs `receiveNamedObject` on `m.msg` and sends
    `DecoupledConsensusModel.Sts.relayedObjects m.msg`. -/
theorem reactionOnVocabularyObjects_recv (S : DecoupledConsensusModel.Execution.Setup V)
    (n : NodeState V) (t : Int)
    (m : SignedMsg V (DecoupledConsensusModel.Execution.NamedObject V)) :
    reactionOnVocabularyObjects S n t (.recv m) =
      { state := receiveNamedObject S n m.msg,
        send := DecoupledConsensusModel.Sts.relayedObjects m.msg } := by
  simp only [reactionOnVocabularyObjects, Event.toSpec, Spec.Sts.reaction,
    NodeStepResult.toProof, SignedMsg.toSpec, toProof_relayedObjects,
    Spec.NamedObject.toProof_toSpec, receiveNamedObject]

/-- On a wake, `reactionOnVocabularyObjects` runs `Spec.wake` and sends nothing. -/
theorem reactionOnVocabularyObjects_wake (S : DecoupledConsensusModel.Execution.Setup V)
    (n : NodeState V) (t : Int) :
    reactionOnVocabularyObjects S n t .wake = { state := Spec.wake n, send := 0 } := by
  simp only [reactionOnVocabularyObjects, Event.toSpec, Spec.Sts.reaction,
    NodeStepResult.toProof, Multiset.map_zero]

/-- The spec's protocol at `Setup.toSpec S` over the object type
    `DecoupledConsensusModel.Execution.NamedObject V`: the initial node states of
    `Spec.Sts.protocol (Setup.toSpec S)`, and a step that is `reactionOnVocabularyObjects`. -/
def protocolOnVocabularyObjects (S : DecoupledConsensusModel.Execution.Setup V) :
    Framework.StsMultisetLog.Protocol V (DecoupledConsensusModel.Execution.NamedObject V)
      (NodeState V) Empty where
  init := (Spec.Sts.protocol (Setup.toSpec S)).init
  step _ r _view n e res := res = reactionOnVocabularyObjects S n (r : Int) e
  total := by
    intro _ r _view n e
    exact ⟨reactionOnVocabularyObjects S n (r : Int) e, rfl⟩
  enabled _ _ ev := ev.elim

/-- The initial node state of validator `p` in `protocolOnVocabularyObjects S` is
    `Spec.initial (Setup.toSpec S).C p`. -/
theorem protocolOnVocabularyObjects_init (S : DecoupledConsensusModel.Execution.Setup V) (p : V) :
    (protocolOnVocabularyObjects S).init p = Spec.initial (Setup.toSpec S).C p := rfl

/-- The step relation of `protocolOnVocabularyObjects S` holds exactly when the spec's step relation
    at `Setup.toSpec S` holds at the `toSpec` forms of the view, the event and the result. -/
theorem protocolOnVocabularyObjects_step_iff (S : DecoupledConsensusModel.Execution.Setup V)
    (p : V) (r : Nat) (view : View V (DecoupledConsensusModel.Execution.NamedObject V))
    (n : NodeState V) (e : Event V (DecoupledConsensusModel.Execution.NamedObject V) Empty)
    (res : NodeStepResult (NodeState V) (DecoupledConsensusModel.Execution.NamedObject V)) :
    (protocolOnVocabularyObjects S).step p r view n e res ↔
      (Spec.Sts.protocol (Setup.toSpec S)).step p r (View.toSpec view) n (Event.toSpec e)
        (NodeStepResult.toSpec res) := by
  show res = reactionOnVocabularyObjects S n (r : Int) e ↔
    NodeStepResult.toSpec res = Spec.Sts.reaction (Setup.toSpec S) n (r : Int) (Event.toSpec e)
  constructor
  · intro h
    rw [h, reactionOnVocabularyObjects, NodeStepResult.toSpec_toProof]
  · intro h
    rw [reactionOnVocabularyObjects, ← h, NodeStepResult.toProof_toSpec]

end SpecRecord
