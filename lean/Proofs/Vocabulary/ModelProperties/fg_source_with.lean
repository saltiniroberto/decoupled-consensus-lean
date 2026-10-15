module
public import Model.Vocabulary.Protocol.Duties.Inputs

@[expose] public section

/-!
# Facts about `Protocol.fg_source_with`

The contract's FG source for a grade-2 candidate.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

variable {V : Type} [DecidableEq V] [Fintype V]

/-- If the FG source at the contract's own grade-2 candidate for round `r` is some block, the
    contract's read for round `r` has a grade-2 candidate. -/
theorem read_Q2_isSome_of_fg_source_with_grade2 (contract : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.HealingStore V) (r : Round)
    {B : Block V}
    (h : Protocol.fg_source_with contract E hc st r
      (Protocol.grade2_block_with contract E hc st r) = some B) :
    ∃ A, (contract.read E hc st r).Q2 = some A := by
  unfold Protocol.grade2_block_with at h
  cases hQ : (contract.read E hc st r).Q2 with
  | none =>
    rw [hQ] at h
    simp [Protocol.fg_source_with] at h
  | some A => exact ⟨A, rfl⟩

/-- If the deepest block of the live confirmed chain that descends from the candidate `q` and passes
    the contract's clearance test is `W`, the FG source at `q` is `W`. -/
theorem fg_source_with_some_of_deepest_clear (contract : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.HealingStore V) (r : Round)
    {q W : Block V}
    (h : Protocol.deepest_clear (some q) st.live_confirmed
      (contract.read E hc st r).clear = some W) :
    Protocol.fg_source_with contract E hc st r (some q) = some W := by
  simp only [Protocol.fg_source_with, h]

/-- If no block of the live confirmed chain descends from the candidate `q` and passes the
    contract's clearance test, the FG source at `q` is `q`. -/
theorem fg_source_with_some_of_deepest_clear_none (contract : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.HealingStore V) (r : Round)
    {q : Block V}
    (h : Protocol.deepest_clear (some q) st.live_confirmed
      (contract.read E hc st r).clear = none) :
    Protocol.fg_source_with contract E hc st r (some q) = some q := by
  simp only [Protocol.fg_source_with, h]

end DecoupledConsensusModel.Proofs.ModelProperties

end
