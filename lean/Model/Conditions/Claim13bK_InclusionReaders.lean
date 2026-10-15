import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Sts_Interface
import Model.Record.Wiring

/-!
# An honest proposal is in every later confirmed output

The conditions `ConfirmedIncludedAtSlot` and `ConfirmedIncludedFromSlot`, stated over a model
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
open DecoupledConsensusModel.Statements.Instantiation
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If slot `s`'s proposer is honest through `s`'s vote time, then every block that proposer put in
    the sent log `x[i].sent` at a step `i` no later than that vote time is an ancestor of the
    confirmed output of every validator honest through its read and awake throughout the vote window
    of its read's slot, at every read from `s`'s proposal time plus the confirmation delay on. -/
def ConfirmedIncludedAtSlot (M : Record.Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (s : Slot) : Prop :=
  HonestThroughTime Sched (M.vote_time S.E s) (S.E.proposer s) →
    ∀ (i : Nat) (B : Block V), Restated.proposedBlockAtStep M S x i s B →
      (x[i].time : Int) ≤ M.vote_time S.E s →
      ∀ (v : V) (j : Nat), Restated.HonestThrough M Sched x j v →
        M.proposal_time S.E s + confirmedInclusionDelay S ≤ (x[j].time : Int) →
        v ∈ activeAtW S Sched (S.E.slotOf (x[j].time : Int)) →
        Block.Preceq B (M.get_confirmed (x[j][v].st).st.core)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- `ConfirmedIncludedAtSlot` holds at every slot from `s₀` on. -/
def ConfirmedIncludedFromSlot (M : Record.Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (s₀ : Slot) : Prop :=
  ∀ s : Slot, s₀ ≤ s → Restated.ConfirmedIncludedAtSlot M S Sched x s

end

end DecoupledConsensusModel.Sts.Restated
