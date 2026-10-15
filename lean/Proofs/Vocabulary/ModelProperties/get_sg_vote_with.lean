module
public import Model.Vocabulary.Execution.Node

@[expose] public section

/-!
# Facts about `Protocol.get_sg_vote_with`

The selected SG vote under the grade contract a named node's cache selects.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Under the grade contract of `c`, if the deepest block of the live confirmed chain that descends
    from the contract's anchor and passes its clearance test is `B`, the selected SG vote is `B`,
    whatever grade-2 candidate is supplied. -/
theorem get_sg_vote_with_gradeContract_of_deepest_clear
    (c : DecoupledConsensusModel.Protocol.Cache V) (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.HealingStore V) (r : Round) (A_G2 : Option (Block V)) {B : Block V}
    (h : Protocol.deepest_clear (some ((NamedProfile.gradeContract c).read E hc st r).anchor)
      st.live_confirmed ((NamedProfile.gradeContract c).read E hc st r).clear = some B) :
    Protocol.get_sg_vote_with (NamedProfile.gradeContract c) E hc st r A_G2 = B := by
  unfold Protocol.get_sg_vote_with
  unfold NamedProfile.gradeContract DecoupledConsensusModel.Protocol.frameContract at h ⊢
  unfold Protocol.currentSGVote
  simp only [h]

/-- Under the grade contract of `c`, the SG vote selected with the contract's own grade-2 candidate
    is `Protocol.currentSGVote` of `st` and the contract's grade read. -/
theorem get_sg_vote_with_gradeContract_grade2
    (c : DecoupledConsensusModel.Protocol.Cache V) (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.HealingStore V) (r : Round) :
    Protocol.get_sg_vote_with (NamedProfile.gradeContract c) E hc st r
        (Protocol.grade2_block_with (NamedProfile.gradeContract c) E hc st r) =
      Protocol.currentSGVote st ((NamedProfile.gradeContract c).read E hc st r) := rfl

end DecoupledConsensusModel.Proofs.ModelProperties

end
