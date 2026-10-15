import Proofs.Vocabulary.Protocol.Store.BoundaryRows
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring

/-!
# An earlier action precedes a later G2 domain time

With at least three slots per round, an earlier round's action time is at most a later round's G2
domain time, stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.NamedOutageClosure
open Execution Internal.NamedOutageEntry Internal.NamedStableChainOutage DecoupledConsensusModel.Protocol

/-- If `3 ≤ S.hc.R` and `q < r`, then round `q`'s action time is at most round `r`'s G2 domain time. -/
theorem Vocabulary.Proofs.NamedOutageClosure.action_le_domain (facts : Record.Facts M) (S : Setup V) {q r : Round} (hR : 3 ≤ S.hc.R) (hqr : q < r) :
    (Restated.Vocabulary.Execution.Setup.a M S q) ≤ M.domain S.E S.hc r .g2 := by
  refine le_trans ?_ ((facts.gr.action_delta_le_early S hR hqr).trans (facts.gr.early_le_domain S r))
  simpa only [add_zero] using Int.add_le_add_left S.E.Δ_pos.le ((Restated.Vocabulary.Execution.Setup.a M S q))

end

end DecoupledConsensusModel.Sts.Restated
