module
public import Proofs.Vocabulary.ModelVocabulary.Substrate.Time
public import Model.Vocabulary.Protocol.StoreBase

@[expose] public section

/-!
# Resolution-time bounds

Facts relating a Goldfish vote's resolution time to the receipt stamps of the vote and of the block
it names.
-/

namespace DecoupledConsensusModel
namespace Protocol

section Resolution

variable {V : Type} [DecidableEq V]

/-- A vote resolved before `Γ` was received before `Γ`. -/
theorem stampedBefore_of_resolution {T : Finset (Block V)}
    {tb : TimestampMap (Block V)} {tv : TimestampMap (GoldfishVote V)} {Γ : Time}
    {vote : GoldfishVote V}
    (h : stampedBefore (resolution_time T tb tv) Γ vote = true) :
    stampedBefore tv Γ vote = true := by
  simp only [stampedBefore_eq_occurrenceBefore, resolution_time] at h ⊢
  cases hf : Block.find? T vote.head with
  | none => rw [hf] at h; exact absurd h (by simp [occurrenceBefore])
  | some H =>
      rw [hf] at h
      by_cases hslot : H.slot ≤ vote.slot
      · simp [hslot] at h
        exact occurrenceBefore_of_max_left h
      · simp [hslot, occurrenceBefore] at h

/-- A vote naming the block `H` of its own slot or earlier is resolved before `Γ` when both the vote
    and `H` were received before `Γ`. -/
theorem stampedBefore_resolution_of {T : Finset (Block V)}
    {tb : TimestampMap (Block V)} {tv : TimestampMap (GoldfishVote V)} {Γ : Time}
    {vote : GoldfishVote V} {H : Block V}
    (hfind : Block.find? T vote.head = some H) (hslot : H.slot ≤ vote.slot)
    (hv : stampedBefore tv Γ vote = true) (hH : stampedBefore tb Γ H = true) :
    stampedBefore (resolution_time T tb tv) Γ vote = true := by
  simp only [stampedBefore_eq_occurrenceBefore, resolution_time, hfind, hslot] at hv hH ⊢
  exact occurrenceBefore_max hv hH

/-- A vote resolved before `Γ` names a block of its own slot or earlier. -/
theorem head_slot_le_of_resolution_time {T : Finset (Block V)}
    {tb : TimestampMap (Block V)} {tv : TimestampMap (GoldfishVote V)} {Γ : Time}
    {vote : GoldfishVote V} {H : Block V}
    (hfind : Block.find? T vote.head = some H)
    (hτ : stampedBefore (resolution_time T tb tv) Γ vote = true) :
    H.slot ≤ vote.slot := by
  simp only [stampedBefore_eq_occurrenceBefore, resolution_time, hfind] at hτ
  by_contra hslot
  simp [hslot, occurrenceBefore] at hτ

end Resolution

end Protocol
end DecoupledConsensusModel

end
