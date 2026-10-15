module
public import Model.Vocabulary.Execution.Node
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import StsMultisetLog.Spec.Protocol

@[expose] public section

/-!
# The protocol model as a transition system

The protocol model placed in the shape of the sts framework's `Framework.StsMultisetLog.Protocol`.
On `tick` a validator runs `NamedNode.tick` when the clock reading is a multiple of `S.E.Δ` and does
nothing otherwise; on `recv m` it runs `NamedNode.process` and re-sends `relayedObjects m.msg`;
`wake` changes nothing. Every value is built from `Setup.alwaysAwake S`, so a validator's sleep is
decided by the framework's schedule alone.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- `S` with every node's `awake` field the constant `true`, every other field unchanged. -/
def Setup.alwaysAwake (S : Setup V) : Setup V :=
  { S with
    node := fun v => { S.node v with awake := fun _ => true }
    node_val_index := fun v => S.node_val_index v }

/-- The objects a validator re-sends when it is delivered the payload `m`: a block together with
    each of its Goldfish votes and attestations as a standalone payload, any other payload alone. -/
def relayedObjects : NamedObject V → Multiset (NamedObject V)
  | .block B => {NamedObject.block B}
      + (B.gf_votes.map NamedObject.gfVote : Multiset _)
      + (B.attestations.map NamedObject.attest : Multiset _)
  | o => {o}

/-- The reaction of the validator `p`, holding node state `n`, to the event `e` at the clock reading
    `t`: `tick` runs `NamedNode.tick` when `t % S.E.Δ = 0` and changes nothing otherwise, `recv m`
    runs `NamedNode.process` on `m.msg` and sends `relayedObjects m.msg`, and `wake` changes
    nothing. -/
def reaction (S : Setup V) (p : V) (n : NamedNodeState V) (t : Int)
    (e : Event V (NamedObject V) Empty) :
    NodeStepResult (NamedNodeState V) (NamedObject V) :=
  match e with
  | .tick =>
      if t % S.E.Δ = 0 then
        let out := NamedNode.tick (Setup.alwaysAwake S) p n t
        { state := out.1, send := (out.2 : Multiset (NamedObject V)) }
      else { state := n, send := 0 }
  | .recv m => { state := NamedNode.process (Setup.alwaysAwake S) n m.msg,
                 send := relayedObjects m.msg }
  | .wake => { state := n, send := 0 }
  | .custom ev => ev.elim

/-- The protocol model in the sts framework's shape, for the setup `S`: every validator starts at
    `NamedNode.initial`, and the step relation is the graph of `reaction`. -/
def protocol (S : Setup V) :
    Framework.StsMultisetLog.Protocol V (NamedObject V) (NamedNodeState V) Empty where
  init _ := NamedNode.initial
  step p r _view n e res := res = reaction S p n (r : Int) e
  total := by
    intro p r _view n e
    exact ⟨reaction S p n (r : Int) e, rfl⟩
  enabled _ _ ev := ev.elim

end DecoupledConsensusModel.Sts
