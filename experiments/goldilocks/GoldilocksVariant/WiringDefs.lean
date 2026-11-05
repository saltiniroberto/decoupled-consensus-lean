module
public import RStsVariant2
public import GoldilocksSts
public import GoldilocksCorrectness.Record.Model
public import GoldilocksCorrectness.Record.Restated.Statements.View.GoldilocksViewDefs
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs
public import GoldilocksCorrectness.Statements.Executions.UnforgeabilityDefs
public import GoldilocksCorrectness.Statements.Routines.AccountableDefs

@[expose] public section

/-!
# Goldilocks as a protocol of the real-time variant of the sts framework

The node of any Goldilocks model `M`, run by `RStsVariant2`, and what a statement over that variant
reads of it. Definitions only.

- `Registry`, `Readers`: what a statement reads of any protocol of the variant: a node state read
  as a view, the vocabulary of blocks and objects, the slashing evidence, the validator set at a
  block, and what a node serves to a peer that asks.
- `variantReactions`, `variantProtocolOf`: Goldilocks's node as a protocol of the variant.
- `Registry.ones`, `conflicts`, `variantReaders`: Goldilocks's readers.

Not on this page yet:
- holding a message the node cannot yet process and processing it later: today a block of a slot
  later than the node's clock's is refused, and a Goldfish vote of a later slot dropped, as the
  model's `receive` does;
- the validator set read at each block: today every validator counts, with weight one;
- a disk holding only the durable part of a state: today the whole state is written
  (`persist := id`).
-/

set_option autoImplicit false

namespace GoldilocksVariant

open Goldilocks (NamedObject RootOrder Block Attestation)
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record (GoldilocksModel)
open GoldilocksCorrectness.Statements.Network (ViewVocab)
open GoldilocksCorrectness.Statements.View (NodeView)

/-! ## 1. What a statement reads of a protocol of the variant -/

/-- The validator set as a chain has it at a block. -/
structure Registry (Node : Type) where
  /-- `weight v`: the weight of the validator `v`. -/
  weight : (v : Node) → ℕ
  /-- The validators that have entered and not exited. -/
  active : Finset Node
  /-- The validators that are slashed. -/
  slashed : Finset Node
  /-- The weight a quorum must reach. -/
  quorum : ℕ

/-- What a statement reads of a protocol whose node states are `NodeState`, whose messages are
`Msg` and whose blocks are `Block`: the vocabulary of blocks and messages, and four readers more. -/
structure Readers (Node Msg NodeState Block : Type) extends ViewVocab Node Block Msg where
  /-- `conflicts m m'`: the objects of `m` and `m'` are two objects one validator must not both
  have authored. -/
  conflicts : (m : Msg) → (m' : Msg) → Prop
  /-- `registry B`: the validator set at the block `B`. -/
  registry : (B : Block) → Registry Node
  /-- `view st`: the node state `st` read as a view. -/
  view : (st : NodeState) → NodeView Block
  /-- `serves t st m`: a node whose clock reads `t` and whose memory state is `st` serves `m` to a
  peer that asks. -/
  serves : (t : ℕ) → (st : NodeState) → (m : Msg) → Prop

/-! ## 2. The wiring -/

/-- `variantReactions M S n r e`: the reactions of a node of the model `M` holding the state `n`,
at the clock reading `r`, to the event `e`. At a tick, any `.ok` outcome of `M.tick` at `r`, its
objects sent in order, each to every validator; at a delivery, the state `M.receive` gives and
the objects `M.relayedObjects` relays, each sent to every validator. No reaction writes the disk.

The variables:
- `M`: the model; `S`: the setup; `n`: the node state; `r`: the clock reading; `e`: the event. -/
def variantReactions {V : Type} [DecidableEq V] [Fintype V] [RootOrder] (M : GoldilocksModel V)
    (S : Setup V) (n : M.N) (r : ℕ)
    (e : RStsVariant2.Event V (NamedObject V) Empty) :
    Set (RStsVariant2.NodeStepResult V M.N (NamedObject V)) :=
  match e with
  | .tick => { res | ∃ p : M.N × List (NamedObject V),
      Except.ok p ∈ M.tick S.C S.P S.X n (r : Int) ∧
      res = RStsVariant2.NodeStepResult.mk p.1
        (p.2.map (fun o => RStsVariant2.NodeEffect.send ⟨o, RStsVariant2.Recipients.all⟩)) }
  | .recv m => { res | res = RStsVariant2.NodeStepResult.mk (M.receive S.C S.P S.X n m.msg)
      ((M.relayedObjects m.msg).toList.map
        (fun o => RStsVariant2.NodeEffect.send ⟨o, RStsVariant2.Recipients.all⟩)) }
  | .custom ev => ev.elim

/-- `variantProtocolOf M S`: the node of the model `M` with the setup `S`, as a protocol of
`RStsVariant2`. A step is a reaction of `variantReactions`, or, when there is none, the state kept
and nothing sent; the protocol has no event of its own; the whole state is written to the disk; a
restart with the boot reading `t` gives `M.wake n t`.

A validator that comes online at the clock value `t` starts in the state `M.wake (M.initial S.C v) t`:
`awakeSince` is `none` until its first tick.

The variables:
- `M`: the model; `S`: the setup. -/
def variantProtocolOf {V : Type} [DecidableEq V] [Fintype V] [RootOrder] (M : GoldilocksModel V)
    (S : Setup V) :
    RStsVariant2.Protocol V (NamedObject V) M.N Empty where
  init t v := M.wake (M.initial S.C v) (t : Int)
  step _ r n e res :=
    res ∈ variantReactions M S n r e ∨
      (variantReactions M S n r e = ∅ ∧ res = { state := n, effects := [] })
  total := by
    classical
    intro _ r n e
    by_cases h : (variantReactions M S n r e).Nonempty
    · obtain ⟨res, hres⟩ := h
      exact ⟨res, Or.inl hres⟩
    · exact ⟨{ state := n, effects := [] }, Or.inr ⟨Set.not_nonempty_iff_eq_empty.mp h, rfl⟩⟩
  enabled _ _ ev := ev.elim
  persist := id
  restart t _ n := M.wake n (t : Int)

/-! ## 3. Goldilocks's readers -/

/-- `Registry.ones V`: every validator active, none slashed, each of weight one, and the quorum
`quorum V`, two thirds of the validator count rounded up.

The variables:
- `V`: the validators. -/
def Registry.ones (V : Type) [DecidableEq V] [Fintype V] : Registry V where
  weight _ := 1
  active := Finset.univ
  slashed := ∅
  quorum := Goldilocks.quorum V

/-- `conflicts o o'`: `o` and `o'` are attestations `a`, `a'` with `E1 a a'` or `E2 a a'`: `a`
carries a finality pair `(h, T)` and `a'` is a vote at `h` naming a block other than `T`, or the
two are target votes at one height for different blocks.

The variables:
- `o`, `o'`: the two objects. -/
def conflicts {V : Type} [DecidableEq V] [Fintype V] (o o' : NamedObject V) : Prop :=
  ∃ a a' : Attestation V, o = .attest a ∧ o' = .attest a' ∧
    (GoldilocksCorrectness.Statements.Routines.E1 a a' ∨
      GoldilocksCorrectness.Statements.Routines.E2 a a')

/-- `variantReaders M S`: what a statement reads of `variantProtocolOf M S`: a node state as its
finalized block, its confirmed tip and its tree (`nodeView M`); the blocks and objects as
`Vocab.goldilocks` reads them; `conflicts` as the slashing evidence; `Registry.ones V` at every
block; and `servesMin` as what a node serves.

The variables:
- `M`: the model; `S`: the setup (its parameters give the slot of a clock reading). -/
def variantReaders {V : Type} [DecidableEq V] [Fintype V] [RootOrder] (M : GoldilocksModel V)
    (S : Setup V) :
    Readers V (NamedObject V) M.N (Block V) where
  toViewVocab := GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks
  conflicts := conflicts
  registry _ := Registry.ones V
  view := GoldilocksCorrectness.Record.Statements.View.nodeView M
  serves t n o := GoldilocksCorrectness.Record.Statements.AbstractTrace.servesMin M S.C n t o

end GoldilocksVariant
