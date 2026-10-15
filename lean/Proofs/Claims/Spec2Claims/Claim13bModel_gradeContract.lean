import Model.Vocabulary.Execution.Node
import Proofs.Claims.ModelIrreducible
import Proofs.Vocabulary.Protocol.ValidatorClient.RecordClean

/-!
# Facts about `NamedProfile.gradeContract`

Lemmas that unfold the grade contract the named node runs with, the frame contract
`Protocol.frameContract` at the node's cache.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Execution.NamedProfile.gradeContract
  DecoupledConsensusModel.Protocol.currentSGVote DecoupledConsensusModel.Protocol.frameContract
  DecoupledConsensusModel.Protocol.frameGradeRead DecoupledConsensusModel.Protocol.frameSGCandidate
  DecoupledConsensusModel.Protocol.frameStableRoot

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The stable root of the named node's grade contract at the cache `c` is `frameStableRoot c`. -/
theorem gradeContract_stableRoot (c : Protocol.Cache V) :
    (NamedProfile.gradeContract c).stableRoot = Protocol.frameStableRoot c := rfl

/-- The confirmation mode of the named node's grade contract at the cache `c` is `optional` with the
    select candidate `frameSGCandidate c`. -/
theorem gradeContract_confirmationSG (c : Protocol.Cache V) :
    (NamedProfile.gradeContract c).confirmationSG
      = Protocol.ConfirmationSGCandidate.optional (Protocol.frameSGCandidate c) := rfl

/-- The SG vote of the named node's grade contract at the cache `c` is `Protocol.currentSGVote`. -/
theorem gradeContract_sgVote (c : Protocol.Cache V) :
    (NamedProfile.gradeContract c).sgVote = Protocol.currentSGVote := rfl

/-- The grade read of the named node's grade contract at the cache `c` is
    `Protocol.frameGradeRead c`. -/
theorem gradeContract_read (c : Protocol.Cache V) (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.HealingStore V) (r : Round) :
    (NamedProfile.gradeContract c).read E hc st r = Protocol.frameGradeRead c E hc st r := rfl

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- If the store `st`'s justified and finalized blocks are in its tree and the round action,
    computed with the node's grade contract at the cache `c` on `st`'s healing view, carries the
    finality pair `(h, T)`, then some block of `st`'s tree has a chain state whose justified height
    is `h`. -/
theorem round_action_head_mem_gradeContract (c : Protocol.Cache V) (E : Env V)
    (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : Protocol.Store V)
    (record : Protocol.NamedRecord) (hJ : st.J ∈ st.T) (hF : st.F ∈ st.T)
    {h : Height} {T : BlockId}
    (hp : (Protocol.NamedActions.round_action_with (NamedProfile.gradeContract c) E hc nd
        st.toHealing record).2.finality_pair = some ⟨h, T⟩) :
    ∃ Hd ∈ st.T, (st.σ Hd).h_j = h :=
  Proofs.round_action_head_mem_frame c E hc nd st record hJ hF hp

end DecoupledConsensusModel.Sts
