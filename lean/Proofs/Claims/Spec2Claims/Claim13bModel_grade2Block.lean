import Proofs.Claims.Spec2Claims.Claim13bModel_frameStableRoot
import Proofs.Claims.Spec2Claims.Claim13bModel_activePrefix

/-!
# Facts about `Protocol.grade2Block`

Lemmas that unfold the grade-2 block of a frame read, the `Q2` field of the frame contract's grade
read. The main one says that the grade-2 block, when there is one, is the frame stable root at the
same frame.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Execution.NamedProfile.gradeContract
  DecoupledConsensusModel.Protocol.allClosed DecoupledConsensusModel.Protocol.cacheAtRound
  DecoupledConsensusModel.Protocol.clipFrame DecoupledConsensusModel.Protocol.clipResult
  DecoupledConsensusModel.Protocol.frameContract DecoupledConsensusModel.Protocol.frameGradeRead
  DecoupledConsensusModel.Protocol.grade2Block DecoupledConsensusModel.Protocol.readFrame

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The `Q2` field of the named node's grade read at the store `st` and round `r` is
    `grade2Block st (readFrame c st r)`. -/
theorem gradeContract_read_Q2 (c : Protocol.Cache V) (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.HealingStore V) (r : Round) :
    ((NamedProfile.gradeContract c).read E hc st r).Q2
      = Protocol.grade2Block st (Protocol.readFrame c st r) := rfl

/-- If two stores `st` and `st'` have the same finalized block and the same filtered tree, and the
    grade-2 block of the frame read at `st'` is `Q`, then the frame stable root at `st` is `Q`. -/
theorem frameStableRoot_of_grade2Block (c : Protocol.Cache V) (E : Env V)
    (hc : Protocol.HealConfig) (st st' : Protocol.HealingStore V) (r : Round)
    (hF : st'.F = st.F)
    (htree : Protocol.get_filtered_block_tree st'.toFG = Protocol.get_filtered_block_tree st.toFG)
    {Q : Block V} (h : Protocol.grade2Block st' (Protocol.readFrame c st' r) = some Q) :
    Protocol.frameStableRoot c E hc st r = some Q := by
  have hframe : Protocol.readFrame c st' r = Protocol.readFrame c st r := by
    unfold Protocol.readFrame
    rw [hF]
  unfold Protocol.grade2Block at h
  rw [hframe, htree] at h
  split_ifs at h
  exact frameStableRoot_of_projection c E hc st r h

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- If two healing stores have the same filtered block tree, the grade-2 block of any frame is the
    same at both. -/
theorem grade2Block_eq_of_filtered_eq {st st' : Protocol.HealingStore V}
    (frame : Protocol.Frame V)
    (h : Protocol.get_filtered_block_tree st.toFG = Protocol.get_filtered_block_tree st'.toFG) :
    Protocol.grade2Block st frame = Protocol.grade2Block st' frame := by
  unfold Protocol.grade2Block
  rw [h]

end DecoupledConsensusModel.Sts

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- If `Protocol.grade2Block stH frame` is `Q`, the frame's grade-2 entry is a block `root` with
    `Q ⪯ root`. -/
theorem grade2Block_preceq_root {stH : Protocol.HealingStore V} {frame : Protocol.Frame V}
    {Q : Block V} (hQ : Protocol.grade2Block stH frame = some Q) :
    ∃ root : Block V, frame.g2 = some (some root) ∧ Block.Preceq Q root := by
  unfold Protocol.grade2Block at hQ
  split at hQ
  · cases hframe : frame.g2 with
    | none => rw [hframe] at hQ; simp at hQ
    | some o =>
        cases o with
        | none => rw [hframe] at hQ; simp at hQ
        | some root =>
            rw [hframe] at hQ
            simp only [Option.bind, id] at hQ
            exact ⟨root, rfl, preceq_of_activePrefix_eq_some hQ⟩
  · exact absurd hQ (by simp)

end DecoupledConsensusModel.Sts
