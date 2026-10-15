module
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.Walk
public import Proofs.Vocabulary.Internal.Definitions.PhaseGrades
public import Proofs.Vocabulary.Protocol.Grades.LegacyVocabulary
public import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Logic.Equiv.PartialEquiv
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar

@[expose] public section

/-!
# Round-zero reductions

Round zero has no earlier grade batch and no relative-SG window, so the grade summaries, the direct
support, grade 1 and the fresh anchor all reduce to their empty forms.
-/


namespace DecoupledConsensusModel
namespace Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

omit [DecidableEq V] [Fintype V] in

@[simp] theorem round_batch_zero (gv : Protocol.GradeView V) :
    Protocol.round_batch gv 0 = ∅ := by
  simp [Protocol.round_batch]

omit [Fintype V] in

@[simp] theorem batch_first_empty (ts : TimestampMap (Protocol.SGVote V)) :
    Protocol.batch_first? ts ∅ = none := by
  exact pickUnique?_empty rfl

omit [Fintype V] in
/-- Every validator has the empty grade summary in round zero. -/
@[simp] theorem summary_zero (gv : Protocol.GradeView V) (v : V) :
    Protocol.summary gv 0 v = ⟨none, none, none⟩ := by
  simp [Protocol.summary, Protocol.equivocation_instant, Protocol.sg_votes_by]

/-- Direct grade support is zero in round zero. -/
@[simp] theorem direct_support_zero (E : Env V) (gv : Protocol.GradeView V)
    (Γ_h Γ_e : Time) (B : Block V) :
    Protocol.direct_support E gv 0 Γ_h Γ_e B = 0 := by
  simp [Protocol.direct_support,
    occurrenceBefore, occurrenceAtLeast, Electorate.weightOf]

/-- Grade 1 is false in round zero. -/
@[simp] theorem G1_zero (E : Env V) (gv : Protocol.GradeView V)
    (hc : Protocol.HealConfig) (B : Block V) :
    Protocol.G1 E gv hc 0 B = false := by
  simp [Protocol.G1, Env.m, Electorate.strictMajorityThreshold]


/-- The fresh grade-1 anchor is absent in round zero. -/
@[simp] theorem fresh_anchor_zero (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.HealingStore V) :
    Protocol.fresh_anchor E hc st 0 = none := by
  rw [Protocol.fresh_anchor]
  have hempty :
      (Protocol.get_filtered_block_tree st.toFG).filter
          (fun B => Protocol.G1 E st.gradeView hc 0 B = true) = ∅ := by
    ext B
    simp
  rw [hempty]
  unfold Block.deepest?
  exact pickUnique?_empty rfl

/-- The relative-SG expiry window is empty in round zero. -/
@[simp] theorem latest_window_zero (η_SG : Round) :
    Protocol.latest_window η_SG 0 = [] := by
  simp [Protocol.latest_window]

end Protocol
end DecoupledConsensusModel

end
