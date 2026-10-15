import Model.Vocabulary.Protocol.ForkChoice.Goldfish
import Proofs.Claims.ModelIrreducible

/-!
# Facts on `Protocol.voters_count`

The number of validators that participate in a vote set.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.participates
  DecoupledConsensusModel.Protocol.raw_participants
  DecoupledConsensusModel.Protocol.raw_voters_count DecoupledConsensusModel.Protocol.voters_count
  DecoupledConsensusModel.Protocol.votes_by

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Two vote sets with the same participating validators have the same `Protocol.voters_count`, at
    any two slots. -/
theorem voters_count_eq_of_participates (E : Env V) {votes votes' : Finset (GoldfishVote V)}
    (s s' : Slot)
    (h : ∀ w : V, Protocol.participates votes w = Protocol.participates votes' w) :
    Protocol.voters_count E votes s = Protocol.voters_count E votes' s' := by
  simp only [Protocol.voters_count, Protocol.raw_voters_count, Protocol.raw_participants, h]

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]


/-- If every validator of `X` participates in `votes`, then `X` has at most
    `Protocol.voters_count E votes s` members. -/
theorem card_le_voters_count_of_participates (E : Env V) (votes : Finset (GoldfishVote V))
    (s : Slot) (X : Finset V) (h : ∀ x ∈ X, Protocol.participates votes x = true) :
    X.card ≤ Protocol.voters_count E votes s := by
  unfold Protocol.voters_count Protocol.raw_voters_count Protocol.raw_participants
  exact Finset.card_le_card (fun x hx => Finset.mem_filter.mpr ⟨Finset.mem_univ x, h x hx⟩)

end DecoupledConsensusModel.Sts

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

end DecoupledConsensusModel.Sts
