module
public import Proofs.Vocabulary.Internal.Legacy.Definitions.NamedDutyReads
public import Proofs.Vocabulary.Internal.ModelVocabulary.Execution.Run
public import Proofs.Vocabulary.Internal.Legacy.Definitions.ProposalSourcesInternal
public import Proofs.Vocabulary.Internal.ModelVocabulary.Protocol.NamedStoreReads

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Head reads on prepared reads

The voter's head at a slot and the action head at a round, computed on the prepared duty reads.
-/


namespace DecoupledConsensusModel.Internal
open Execution Proofs.HealingSurface NamedRecoveryRead
variable {V : Type} [DecidableEq V] [Fintype V]

/-- The voter's head at slot `k`: the in-tree head on the vote-duty read, with the voter views of
    that read. -/
def voterHeadAt (S : Setup V) (rho : Run V) (v : V) (k : Slot) : Block V :=
  let n := voteDutyRead S rho v k
  let st := n.st.core
  Protocol.get_head_in_tree_with_layer (NamedProfile.gradeContract n.cache) S.E S.hc st.toHealing
    (Protocol.voter_filtered_block_tree S.E st st.s)
    (Protocol.voter_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s)
    (Protocol.voter_support_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s) (st.s - 1)

/-- The action head at round `r`: the head on the action-duty read, over the resolved pool of the
    read's slot. -/
def actionHeadAt (S : Setup V) (rho : Run V) (v : V) (r : Round) : Block V :=
  let n := actionDutyRead S rho v r
  let st := n.st.core
  Protocol.get_head_with (NamedProfile.gradeContract n.cache) S.E S.hc st.toHealing
    (st.pool st.s) ((st.pool st.s).filter (fun u => Protocol.resolved st.T u = true)) st.s

end DecoupledConsensusModel.Internal

end
