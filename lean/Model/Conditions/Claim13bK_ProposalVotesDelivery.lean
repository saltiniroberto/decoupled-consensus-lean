import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Claim13bK_ProposalVotesPivot
import Model.Conditions.Sts_Interface
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bK_ProposalVotesDelivery

/-!
# The proposer's views and the finalized blocks up to a time

The proposer's raw view `proposerVotesOf` and support view `proposerSupportOf` at the proposal read,
and the condition `FinalizedBelowUpTo`, stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- The slot-`(s − 1)` votes the store of slot `s`'s proposal read pools, as a vote set. -/
def proposerVotesOf (M : Record.Model V) (S : Setup V) (before : M.N) (s : Slot) :
    Finset (GoldfishVote V) :=
  (M.proposer_view (M.toHealing (Restated.proposalStoreAt M S before s)).toFG.toSG.toGoldfishStore s).toFinset

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- The outcomes of the proposer's support view at slot `s`'s proposal read, each as a vote set. -/
def proposerSupportOf (M : Record.Model V) (S : Setup V) (before : M.N) (s : Slot) :
    DC.NDRE (Finset (GoldfishVote V)) :=
  (fun L : List (GoldfishVote V) => L.toFinset) <$>
    M.proposer_support_view (M.toHealing (Restated.proposalStoreAt M S before s)).toFG.toSG.toGoldfishStore
      s

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- At every step from `n_W` on whose time is at most `t`, every validator honest through that step
    holds a finalized block that is an ancestor of `C`. -/
def FinalizedBelowUpTo (M : Record.Model V) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (n_W : Nat) (t : Int) (C : Block V) : Prop :=
  ∀ (v : V) (n₁ : Nat), n_W ≤ n₁ → (x[n₁].time : Int) ≤ t → Restated.HonestThrough M Sched x n₁ v →
    Block.Preceq (x[n₁][v].st).st.core.F C

end

end DecoupledConsensusModel.Sts.Restated
