module
public import GoldilocksCorrectness.Record.Wiring
public import GoldilocksCorrectness.Record.ModelSpellings
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.RunFactsDefs
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ActivityDefs
public import GoldilocksCorrectness.Statements.AbstractTrace.DeliveryDefs
public import GoldilocksCorrectness.Statements.Executions.ExecutionDefs
public import GoldilocksCorrectness.Statements.Executions.UnforgeabilityDefs

@[expose] public section

/-!
# ExecutionDefs, over a model

The definitions of `GoldilocksCorrectness/Statements/Executions/ExecutionDefs.lean` over a model
`M`, for a trace `x` of the model's node under the activity `A`: the blocks honest validators hold,
and the assumptions the statements take on the trace, each read through the record's node readers.
The trace's own readers (the step before a time, a validator's node state then, the node state a
tick starts from) are those of `GoldilocksCorrectness/Statements/AbstractTrace/TraceDefs.lean`. The
object classes `acObject` and `fgObject` name no member; the statements read the landed ones.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ)

namespace GoldilocksCorrectness.Record.Statements.Executions

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (DREBOutcomesOk)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V)

/-! ## Reading the trace -/

section Reading

/-- `inHonestTree M A x B`: some validator holds the block `B` in its FG state's tree after some step
of `x`, and is outside the adversary set at that step's time.

The variables:
- `M`: the model;
- `A`: the activity; `x`: the trace; `B`: the block.

Read aloud: an honest validator holds `B` at some point of the trace. -/
def inHonestTree (A : Activity V) (x : Trace V (NamedObject V) M.N) (B : Block V) : Prop :=
  ∃ (i : ℕ) (v : V), x.Honest A i v ∧ B ∈ (x.st i v).tree

/-- `inHonestTreeBy M A x t B`: some validator holds the block `B` in its FG state's tree in the
state some step `i` of `x` leaves (`x.st (i + 1) v`), where step `i` is at a time at most `t` and the
validator is outside the adversary set at step `i`.

The variables:
- `M`: the model;
- `A`: the activity; `x`: the trace; `t`: the bound on the time; `B`: the block.

Read aloud: an honest validator holds `B` right after some step at a time at most `t`. -/
def inHonestTreeBy (A : Activity V) (x : Trace V (NamedObject V) M.N) (t : ℝ) (B : Block V) :
    Prop :=
  ∃ (i : ℕ) (v : V), x.Honest A i v ∧ x.time i ≤ t ∧ B ∈ (x.st (i + 1) v).tree

end Reading

/-! ## The times -/

/-! ## The object classes -/

/-! ## The assumptions -/

section Assumptions

variable (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)

/-- Every honest awake validator's tick answers: at every step `i` that is the tick of a validator
`v` to the reading `t`, with `v` awake and outside the adversary set after step `i`, every outcome of
the model's `tick` at `t` from the node state that tick starts from (`x.tickInput v t`) is an answer,
and an outcome exists.

The validator is read at the tick's step, not after every step whose time is `t`.

The variables:
- `M`: the model;
- `S`: the setup; `A`: the activity; `x`: the trace; `i`: the step; `t`: the reading of the tick;
  `v`: the validator.

Read aloud: an honest awake validator's tick never fails. -/
def TicksSucceed : Prop :=
  ∀ (i t : ℕ) (v : V), x.lbl i = Event.tick v t →
    v ∈ A.active i →
      (∀ r ∈ M.tick S.C S.P S.X (x.tickInput v t) (t : Int),
        ∃ p : M.N × List (NamedObject V), r = .ok p) ∧
      (M.tick S.C S.P S.X (x.tickInput v t) (t : Int)).Nonempty

/-- Roots name blocks within the honest trees: two blocks that honest validators hold, at any
steps, and that have the same root are the same block.

The variables:
- `M`: the model;
- `x`: the execution; `B`, `B'`: the two blocks.

Read aloud: within what honest validators ever hold, a root names one block. -/
def RootsNameBlocks : Prop :=
  ∀ B B' : Block V, inHonestTree M A x B → inHonestTree M A x B' → B.root = B'.root → B = B'

/-- `RootsNameBlocksUntil M S Sched x t`: two blocks that honest validators hold at steps at times
at most `t`, and that have the same root, are the same block. It is `RootsNameBlocks M S Sched x`
with the blocks restricted to those held by the time `t` (`inHonestTreeBy`).

The variables:
- `M`: the model;
- `x`: the execution; `t`: the bound on the time; `B`, `B'`: the two blocks.

Read aloud: within what honest validators hold by the time `t`, a root names one block. -/
def RootsNameBlocksUntil (t : ℝ) : Prop :=
  ∀ B B' : Block V, inHonestTreeBy M A x t B → inHonestTreeBy M A x t B' → B.root = B'.root → B = B'

/-- A block compatible with a validator's finalized block is delivered to the validator only when
the validator holds its parent: at every step that delivers a signed message carrying a block
other than the genesis block to a validator, if the block is compatible with that validator's
finalized block `S.F`, that validator's FG state holds the block's parent in its tree `S.T`.
Nothing is assumed of a block that conflicts with the receiver's finalized block: synchrony may
require such a block to be delivered to a validator that refused its parent and never will hold
it, and the unrestricted form would then allow no execution.

The variables:
- `M`: the model;
- `x`: the execution; `j`: the step of the delivery; `v`: the receiver; `sm`: the signed message;
  `B`: the block it carries.

Read aloud: a block that does not conflict with a validator's finalized block reaches that
validator only once the validator holds its parent. -/
def ParentHeldAtDelivery : Prop :=
  ∀ (j : ℕ) (v : V) (sm : SignedMsg V (NamedObject V)) (B : Block V),
    x.lbl j = Event.deliver v sm →
    -- the delivered message carries the block `B`, not the genesis block
    sm.msg = NamedObject.block B → B ≠ Block.genesis →
    -- `B` does not conflict with the receiver's finalized block
    (x.st j v).finalized.compatible B = true →
    B.parent ∈ (x.st j v).tree

/-- Nobody casts a Goldfish vote in an honest validator's name: whenever a step `i` puts on the
wire a signed message carrying the Goldfish vote `vote`, as the object or in the `votes` of a
block, and `vote.val_index` is honest at that step's time, some step `k ≤ i` is the tick of
`vote.val_index` to a reading `t` and puts the signed message `⟨vote.val_index, .gfVote vote⟩` on
the wire. A relayed object is signed by the relayer, so the signer of the message says nothing of who
cast the vote; the assumption is therefore about the vote's own validator. Signatures are not
modelled, and this is the unforgeability they would give.

The variables:
- `M`: the model;
- `A`: the activity; `x`: the trace; `i`: the step of the send; `sm`: the signed message; `vote`:
  the Goldfish vote it carries;
- `k`: the step of the voter's own send; `t`: the reading of that tick.

Read aloud: every copy of an honest validator's Goldfish vote on the wire descends from that
validator's own tick. -/
def VotesCastByOwner : Prop :=
  ∀ (i : ℕ) (sm : SignedMsg V (NamedObject V)) (vote : GoldfishVote V),
    sm ∈ x.sent (i + 1) - x.sent i →
    -- `sm` carries `vote`, as its object or in the `votes` of the block it carries
    (sm.msg = NamedObject.gfVote vote ∨
      ∃ B : Block V, sm.msg = NamedObject.block B ∧ vote ∈ B.votes) →
    vote.val_index ∉ A.corrupted i →
    ∃ (k t : ℕ), k ≤ i ∧ x.lbl k = Event.tick vote.val_index t ∧
      (⟨vote.val_index, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (k + 1) - x.sent k

end Assumptions

end GoldilocksCorrectness.Record.Statements.Executions

