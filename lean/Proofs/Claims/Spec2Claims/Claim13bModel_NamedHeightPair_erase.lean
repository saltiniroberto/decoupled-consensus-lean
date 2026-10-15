import Model.Vocabulary.Objects.NamedBlocks
import Proofs.Claims.ModelIrreducible
import Proofs.Vocabulary.Internal.ModelVocabulary.Substrate.Pairs

/-!
# Facts about `NamedHeightPair.erase`

The lemmas that unfold `NamedHeightPair.erase`, which forgets the names a named height pair carries:
a vote with the timeout flag set becomes a timeout at its height, a vote without it becomes a target
at its height and entry.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.NamedHeightPair.erase

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

/-- A named vote at height `h` for `entry` without the timeout flag erases to the target pair at `h`
    for `entry`. -/
theorem namedHeightPair_erase_vote_false (h : Height) (entry : BlockId) :
    (NamedHeightPair.vote h entry false).erase = HeightPair.target h entry := rfl

/-- A named vote at height `h` erases to a pair at height `h`, whatever the timeout flag. -/
theorem namedHeightPair_erase_vote_height? (h : Height) (entry : BlockId) (tmo : Bool) :
    (NamedHeightPair.vote h entry tmo).erase.height? = some h := by
  cases tmo <;> rfl

/-- The empty named height pair erases to the empty height pair. -/
theorem namedHeightPair_erase_empty : NamedHeightPair.empty.erase = HeightPair.empty := rfl

/-- A named vote at height `h` with the timeout flag erases to the timeout pair at `h`. -/
theorem namedHeightPair_erase_vote_true (h : Height) (entry : BlockId) :
    (NamedHeightPair.vote h entry true).erase = HeightPair.timeout h := rfl

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

/-- A named height pair whose erasure is the timeout at `h` is a timeout vote at `h` with some
    entry. -/
theorem vote_of_erase_timeout_l85c {p : NamedHeightPair} {h : Height}
    (hp : p.erase = HeightPair.timeout h) : ∃ e, p = .vote h e true := by
  cases p with
  | empty => simp [NamedHeightPair.erase] at hp
  | vote h' e b =>
    cases b with
    | false => simp [NamedHeightPair.erase] at hp
    | true =>
      simp only [NamedHeightPair.erase, if_true, HeightPair.timeout.injEq] at hp
      exact ⟨e, by rw [hp]⟩

/-- A named height pair whose erasure is the target `(h, T)` is the target vote `(h, T)`. -/
theorem vote_of_erase_target_l85c {p : NamedHeightPair} {h : Height} {T : BlockId}
    (hp : p.erase = HeightPair.target h T) : p = .vote h T false := by
  cases p with
  | empty => simp [NamedHeightPair.erase] at hp
  | vote h' e b =>
    cases b with
    | true => simp [NamedHeightPair.erase] at hp
    | false =>
      simp only [NamedHeightPair.erase, Bool.false_eq_true, if_false,
        HeightPair.target.injEq] at hp
      rw [hp.1, hp.2]

end DecoupledConsensusModel.Sts
