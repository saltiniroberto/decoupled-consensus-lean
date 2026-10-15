import Proofs.Vocabulary.Protocol.ValidatorClient.FinalityPairCore
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Record.Wiring

/-!
# The head read by a round action

The set of Goldfish heads a round action can read under a grade contract, stated over a model
`M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Protocol (Record create_attestation finality_pair height_pair own_lock
  record_attestation)
open Protocol (HealConfig)
open Proofs.Records (LockCompatible)

/-- The heads a round action can read under `contract`: the outcomes `H` such that, for some choice
    `res` of one outcome of `M.resolved st.T u` per vote `u`, `H` is an outcome of `M.get_head_with`
    from `st`'s pool at `st`'s slot, restricted to the votes `u` with `res u = true`. -/
def Vocabulary.Proofs.HealingSurface.actionHeadWith (M : Record.Model V) (contract : M.Contract) (E : Env V) (hc : HealConfig)
    (st : M.HS) : DC.NDRE (Block V) :=
  ExceptT.mk { x | ∃ res : GoldfishVote V → Bool, (∀ u, M.resolved st.T u ⇢ res u) ∧
    x ∈ (M.get_head_with contract E hc st (st.toFG.toSG.toGoldfishStore.pool st.s)
      ((st.toFG.toSG.toGoldfishStore.pool st.s).filter (fun u => res u = true)) st.s).run }

end

section
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Protocol (Record create_attestation finality_pair height_pair own_lock
  record_attestation)
open Protocol (HealConfig)
open Proofs.Records (LockCompatible)

end

end DecoupledConsensusModel.Sts.Restated
