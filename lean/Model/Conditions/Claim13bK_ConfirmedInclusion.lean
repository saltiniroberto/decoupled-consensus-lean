import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Claim13bStepConeIter
import Model.Conditions.Sts_Interface
import Model.Record.Wiring

/-!
# An honest proposal is voted for at its own slot

The condition `HonestProposalHeadsAtOwnSlot`, stated over a model `M : Record.Model V`.
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

/-- For every slot `s` from `s₀` on whose confirmation time is at most `tHi` and whose proposer is
    honest through its vote time, and every block `B` that proposer proposed at a step `i` no later
    than that vote time, every honest active member of slot `s`'s committee votes at slot `s` for a
    descendant of `B`. -/
def HonestProposalHeadsAtOwnSlot (M : Record.Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (s₀ : Slot) (tHi : Int) : Prop :=
  ∀ (s : Slot) (i : Nat) (B : Block V), s₀ ≤ s →
    M.confirmation_time S.E s ≤ tHi →
    HonestThroughTime Sched (M.vote_time S.E s) (S.E.proposer s) →
    Restated.proposedBlockAtStep M S x i s B → (x[i].time : Int) ≤ M.vote_time S.E s →
    Restated.HeadsBelow M S Sched x B s

end

end DecoupledConsensusModel.Sts.Restated
