import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bK_ProposalVotesPivot

/-!
# The proposal read

The node states `proposalReadOf` a slot's proposal duty reads, and the store `proposalStoreAt` of
that read, stated over a model `M : Record.Model V`.
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

/-- The node states made of `before`'s store with the clock of slot `s`'s proposal time written into
    it, `before`'s signing record, and an outcome of the phase tick at that time on `before`'s
    cache. -/
def proposalReadOf (M : Record.Model V) (S : Setup V) (before : M.N) (s : Slot) : DC.NDRE M.N :=
  (fun c => M.mkNode (M.ns_setClock S.E before.st (M.proposal_time S.E s)) before.record c) <$>
    M.onPhaseTick S.E S.hc before.st.core.toHealing (M.proposal_time S.E s) before.cache

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- The store slot `s`'s proposal duty reads: `before`'s store with the clock and the slot of slot
    `s`'s proposal time written into it. -/
def proposalStoreAt (M : Record.Model V) (S : Setup V) (before : M.N) (s : Slot) : M.S :=
  (M.ns_setClock S.E before.st (M.proposal_time S.E s)).core

end

end DecoupledConsensusModel.Sts.Restated
