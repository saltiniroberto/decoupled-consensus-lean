module
public import Model.Vocabulary.Protocol.Grades

@[expose] public section

/-!
# Facts about `Protocol.currentSGVote`

The SG vote a grade read selects, one fact per case of the selection.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

variable {V : Type} [DecidableEq V]

/-- If the deepest block of the live confirmed chain that descends from the read's anchor and passes
    the clearance test is `B`, the selected SG vote is `B`. -/
theorem currentSGVote_of_deepest_clear {st : Protocol.HealingStore V}
    {grades : Protocol.GradeRead V} {B : Block V}
    (h : Protocol.deepest_clear (some grades.anchor) st.live_confirmed grades.clear = some B) :
    Protocol.currentSGVote st grades = B := by
  unfold Protocol.currentSGVote
  simp only [h]

/-- If no block of the live confirmed chain descends from the read's anchor and passes the clearance
    test, and the read's grade-2 candidate is `Q`, the selected SG vote is `Q`. -/
theorem currentSGVote_of_Q2 {st : Protocol.HealingStore V} {grades : Protocol.GradeRead V}
    {Q : Block V}
    (h : Protocol.deepest_clear (some grades.anchor) st.live_confirmed grades.clear = none)
    (hQ : grades.Q2 = some Q) :
    Protocol.currentSGVote st grades = Q := by
  unfold Protocol.currentSGVote
  simp only [h, hQ]

/-- If no block of the live confirmed chain descends from the read's anchor and passes the clearance
    test, the read has no grade-2 candidate, and it reports a raw grade-2 result, the selected SG
    vote is the store's FG root. -/
theorem currentSGVote_of_rawG2 {st : Protocol.HealingStore V} {grades : Protocol.GradeRead V}
    (h : Protocol.deepest_clear (some grades.anchor) st.live_confirmed grades.clear = none)
    (hQ : grades.Q2 = none) (hraw : grades.rawG2) :
    Protocol.currentSGVote st grades = Protocol.get_fg_root st.toFG := by
  unfold Protocol.currentSGVote
  simp only [h, hQ, if_pos hraw]

/-- If no block of the live confirmed chain descends from the read's anchor and passes the clearance
    test, the read has no grade-2 candidate, and it reports no raw grade-2 result, the selected SG
    vote is the read's anchor. -/
theorem currentSGVote_of_not_rawG2 {st : Protocol.HealingStore V}
    {grades : Protocol.GradeRead V}
    (h : Protocol.deepest_clear (some grades.anchor) st.live_confirmed grades.clear = none)
    (hQ : grades.Q2 = none) (hraw : ¬ grades.rawG2) :
    Protocol.currentSGVote st grades = grades.anchor := by
  unfold Protocol.currentSGVote
  simp only [h, hQ, if_neg hraw]

end DecoupledConsensusModel.Proofs.ModelProperties

end
