module
public import GoldilocksCorrectness.Record.ModelGoldilocks
public import GoldilocksCorrectness.Record.ScheduleFacts
public import GoldilocksCorrectness.Record.ScheduleGoldilocks
public import GoldilocksCorrectness.Record.NodeInvFacts
public import GoldilocksCorrectness.Record.NodeInvGoldilocks
public import GoldilocksCorrectness.Record.ChainStateFacts
public import GoldilocksCorrectness.Record.ChainStateGoldilocks
public import GoldilocksCorrectness.Record.ReaderFacts
public import GoldilocksCorrectness.Record.ReaderGoldilocks
public import GoldilocksCorrectness.Record.InitialFacts
public import GoldilocksCorrectness.Record.InitialGoldilocks
public import GoldilocksCorrectness.Record.WakeFacts
public import GoldilocksCorrectness.Record.WakeGoldilocks
public import GoldilocksCorrectness.Record.ReceiveFacts
public import GoldilocksCorrectness.Record.ReceiveGoldilocks
public import GoldilocksCorrectness.Record.TickFacts
public import GoldilocksCorrectness.Record.TickGoldilocks
public import GoldilocksCorrectness.Record.NodeInvAddedFacts
public import GoldilocksCorrectness.Record.NodeInvAddedGoldilocks
public import GoldilocksCorrectness.Record.InitialAddedFacts
public import GoldilocksCorrectness.Record.InitialAddedGoldilocks
public import GoldilocksCorrectness.Record.ReceiveAddedFacts
public import GoldilocksCorrectness.Record.ReceiveAddedGoldilocks
public import GoldilocksCorrectness.Record.TickAddedFacts
public import GoldilocksCorrectness.Record.TickAddedGoldilocks
public import GoldilocksCorrectness.Record.TickFacts2
public import GoldilocksCorrectness.Record.TickGoldilocks2
public import GoldilocksCorrectness.Record.TickFacts3
public import GoldilocksCorrectness.Record.TickGoldilocks3

@[expose] public section

/-!
# The facts a model owes

`Facts M` gathers, for a model `M`, the facts of its slot layout and of each of its seven
families, one field each, each a structure of statements about the members:

- `sched`, the slot layout's facts, `ScheduleFacts` (`ScheduleFacts.lean`);
- `cs`, the chain state of a block, `ChainStateFacts` (`ChainStateFacts.lean`);
- `rd`, the readers derived from a node state, `ReaderFacts` (`ReaderFacts.lean`);
- `init`, the initial node state, `InitialFacts` (`InitialFacts.lean`);
- `wk`, the wake, `WakeFacts` (`WakeFacts.lean`);
- `rcv`, the receipt of an object, `ReceiveFacts` (`ReceiveFacts.lean`);
- `tk`, the tick, part 1: the facts that read no duty's computation, `TickFacts1`
  (`TickFacts.lean`);
- `nd`, the model's node invariant, `NodeInvFacts` (`NodeInvFacts.lean`);
- `ndAdded`, the readers that read the stored chain states and the stored greatest height, under
  the node invariant, `NodeInvAddedFacts` (`NodeInvAddedFacts.lean`), added beside `nd`;
- `initAdded`, `rcvAdded`, `tkAdded`, the facts of the initial state, the receipt and the tick
  that read those readers or the greatest height, `InitialAddedFacts`, `ReceiveAddedFacts`,
  `TickAddedFacts` (`InitialAddedFacts.lean`, `ReceiveAddedFacts.lean`, `TickAddedFacts.lean`),
  added beside `init`, `rcv`, `tk`;
- `tk2`, the tick, part 2: the locks and the confirmation at the vote time and the support cutoff,
  `TickFacts2` (`TickFacts2.lean`);
- `tk3`, the tick, part 3: the vote, the block and the attestation the tick sends, and what the
  validator client builds, `TickFacts3` (`TickFacts3.lean`).
- `wake_wake`, two wakes in a row are one wake, at the second time.

A statement over the record takes one hypothesis `F : Facts M` and reads the fact it calls as
a field of a field (`F.cs.…`, `F.tk.…`).
`goldilocksFacts` is the spec's model's proof.
-/

set_option autoImplicit false

namespace GoldilocksCorrectness.Record

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The facts a model owes, one field for the slot layout and one per family.

Read aloud: the model `M` satisfies the facts of its slot layout, chain state, readers, initial
state, wake, receipt, tick and node invariant. -/
structure Facts (M : GoldilocksModel V) : Prop where
  /-- The slot layout's facts. -/
  sched : ScheduleFacts M.toSlotLayout
  /-- The facts about the chain state of a block, `M.chainStateOf C B`. -/
  cs : ChainStateFacts M
  /-- The facts about the readers derived from a node state. -/
  rd : ReaderFacts M
  /-- The facts about the initial node state `M.initial C v`. -/
  init : InitialFacts M
  /-- The facts about the node state after a wake at the time `t`, `M.wake n t`. -/
  wk : WakeFacts M
  /-- The facts about the node state after a delivery, `M.receive C P X n o`. -/
  rcv : ReceiveFacts M
  /-- The facts about the outcomes of a tick, `M.tick C P X n t`, part 1: those that read no
  duty's computation. -/
  tk : TickFacts1 M
  /-- The facts about the model's node invariant `M.nodeInv C P X n`. -/
  nd : NodeInvFacts M
  /-- The defining equations, under the node invariant, of the six readers that read the stored
  chain states and the stored greatest height. -/
  ndAdded : NodeInvAddedFacts M
  /-- The facts about the initial node state added beside `init`. -/
  initAdded : InitialAddedFacts M
  /-- The facts about the node state after a delivery added beside `rcv`. -/
  rcvAdded : ReceiveAddedFacts M
  /-- The facts about the outcomes of a tick added beside `tk`. -/
  tkAdded : TickAddedFacts M
  /-- The facts about the outcomes of a tick, part 2: the locks and the confirmation at the vote
  time and the support cutoff. -/
  tk2 : TickFacts2 M
  /-- The facts about the outcomes of a tick, part 3: the objects its duties send, and the
  attestation the validator client builds. -/
  tk3 : TickFacts3 M
  /-- Two wakes in a row are one wake, at the second time: waking `M.wake n t₁` at the time `t₂`
  gives `M.wake n t₂`. The trace layer reads it at a restart that follows a restart with no
  completed step between.

  Read aloud: a node woken at `t₁` and then at `t₂` is in the state of the node woken at `t₂`
  only. -/
  wake_wake : ∀ (n : M.N) (t₁ t₂ : Goldilocks.Time), M.wake (M.wake n t₁) t₂ = M.wake n t₂

/-- The spec's model satisfies the facts.

Read aloud: Goldilocks satisfies every fact the record asks of a model. -/
theorem goldilocksFacts : Facts (Model.goldilocks (V := V)) :=
  ⟨scheduleFacts_goldilocks, chainStateFacts_goldilocks, readerFacts_goldilocks,
    initialFacts_goldilocks, wakeFacts_goldilocks, receiveFacts_goldilocks,
    tickFacts1_goldilocks, nodeInvFacts_goldilocks, nodeInvAddedFacts_goldilocks,
    initialAddedFacts_goldilocks, receiveAddedFacts_goldilocks, tickAddedFacts_goldilocks,
    tickFacts2_goldilocks, tickFacts3_goldilocks, wakeWake_goldilocks⟩

end GoldilocksCorrectness.Record
