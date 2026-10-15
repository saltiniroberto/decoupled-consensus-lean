module
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.Walk
public import Proofs.Vocabulary.Protocol.Grades.LegacyVocabulary
public import Mathlib.CategoryTheory.Category.Basic
import Proofs.Vocabulary.Objects.Ancestry
import Proofs.Vocabulary.Objects.Weights
import Proofs.Vocabulary.Protocol.ValidatorClient.Engine
import Mathlib.Tactic.ENatToNat

@[expose] public section


namespace DecoupledConsensusModel
namespace Proofs
namespace Optimistic

open Protocol (ChainState)
open Protocol (GradeView HealConfig)
open Protocol (SGVote)
open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Tie-breaks and batch order -/

omit [DecidableEq V] [Fintype V] in
/-- The head tie-break `head_lt` is irreflexive. -/
theorem head_lt_irrefl (h : Option BlockId) : Protocol.head_lt h h = false := by
  cases h <;> simp [Protocol.head_lt]

omit [DecidableEq V] [Fintype V] in

/-- The batch order is irreflexive. -/
theorem batch_before_irrefl (ts : TimestampMap (SGVote V)) (u : SGVote V) :
    Protocol.batch_before ts u u = false := by
  unfold Protocol.batch_before
  cases hx : ts u with
  | none => simpa using head_lt_irrefl u.confirmed
  | some y => simp [head_lt_irrefl]


omit [Fintype V] in
/-- The first vote of a set with at most one member is that member. -/
theorem batch_first?_of_card_le_one {ts : TimestampMap (SGVote V)}
    {S : Finset (SGVote V)} {u : SGVote V} (hu : u ∈ S) (hcard : S.card ≤ 1) :
    Protocol.batch_first? ts S = some u := by
  have huniq := Finset.card_le_one.mp hcard
  refine Protocol.pickUnique?_eq_some hu ?_ (fun a ha _ => huniq a ha u hu)
  simp only [Protocol.is_first_in, decide_eq_true_eq]
  intro w hw
  rw [huniq w hw u hu]
  exact batch_before_irrefl ts u


omit [Fintype V] in

/-- A batch with at most one vote has no equivocation instant. -/
theorem equivocation_instant_eq_none {ts : TimestampMap (SGVote V)}
    {batch : Finset (SGVote V)} (hcard : batch.card ≤ 1) :
    Protocol.equivocation_instant ts batch = none := by
  unfold Protocol.equivocation_instant
  cases hf : Protocol.batch_first? ts batch with
  | none => rfl
  | some first =>
    have hfmem : first ∈ batch := by
      unfold Protocol.batch_first? at hf
      exact Proofs.Engine.pickUnique?_mem hf
    have hempty : batch.filter (fun u => u.confirmed ≠ first.confirmed) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr ?_
      intro u hu
      simp only [not_not]
      rw [Finset.card_le_one.mp hcard u hu first hfmem]
    simp only [hempty, Protocol.batch_first?, pickUnique?]
    rw [dif_neg (by rintro ⟨a, ⟨ha, -⟩, -⟩; exact absurd ha (by simp))]


end Optimistic
end Proofs
end DecoupledConsensusModel

end
