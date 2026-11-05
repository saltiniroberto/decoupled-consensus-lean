module
public import GoldilocksCorrectness.Record.InitialFacts
public import GoldilocksCorrectness.Record.ModelGoldilocks
import all Goldilocks.FG.State
import all Goldilocks.FG.ValidatorClient
import all Goldilocks.AC.State
import all Goldilocks.Node

@[expose] public section

/-!
# The spec's initial-state facts

`initialFacts_goldilocks`: the spec's model satisfies `InitialFacts`. At `Model.goldilocks` the
initial state is the spec's `initial C v`; each field holds by definition (this page sees the
spec's bodies of `initial`, `proposal_window_start`, `FGState.initial`, `ACState.initial` and
`SigningHistory.initial`: the landed `initial_eq` of
`GoldilocksCorrectness/Proofs/Routines/Node.lean` is proved the same way).
-/

set_option autoImplicit false

namespace GoldilocksCorrectness.Record

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The spec's model satisfies the facts about the initial node state.

Read aloud: a Goldilocks node starts with the genesis block alone, nothing held, nothing signed,
its clock at zero and its wake time the first proposal window's start. -/
theorem initialFacts_goldilocks : InitialFacts (Model.goldilocks (V := V)) where
  initial_tree := fun _ _ => rfl
  initial_finalized := fun _ _ => rfl
  initial_justified := fun _ _ => rfl
  initial_justifiedHeight := fun _ _ => rfl
  initial_attestationsHeld := fun _ _ => rfl
  initial_votesHeld := fun _ _ _ => rfl
  initial_stamps := fun _ _ => ⟨fun _ => rfl, fun _ => rfl⟩
  initial_savedConfirmation := fun _ _ _ => rfl
  initial_lockEntries := fun _ _ => rfl
  initial_fastBlocks := fun _ _ => rfl
  initial_latestConfirmed := fun _ _ => rfl
  initial_sent := fun _ _ => ⟨fun _ => ⟨rfl, rfl, rfl⟩, rfl⟩
  initial_clock := fun _ _ => ⟨rfl, rfl⟩
  initial_awakeSince := fun _ _ => rfl

end GoldilocksCorrectness.Record
