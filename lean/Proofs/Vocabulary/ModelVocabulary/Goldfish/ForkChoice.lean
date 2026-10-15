module
public import Model.Vocabulary.Protocol.ForkChoice.Goldfish

@[expose] public section

/-!
# Goldfish vote counts

The validity condition on a Goldfish vote set, its participant, equivocator and supporter sets, and
the committee-filtered participant forms, which agree with the raw ones on a valid vote set.
-/

namespace DecoupledConsensusModel
namespace Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Raw and committee-filtered counts -/

/-- A vote set is valid at slot `s` when every vote in it is of slot `s` and its voter is in the
    slot-`s` committee. -/
def VoteSetValid (E : Env V) (s : Slot) (votes : Finset (GoldfishVote V)) : Prop :=
  ∀ u ∈ votes, u.slot = s ∧ u.val_index ∈ E.committee s

namespace VoteSetValid

/-- Validity is inherited by every subset. -/
theorem mono {E : Env V} {s : Slot} {votes support : Finset (GoldfishVote V)}
    (hvalid : VoteSetValid E s votes) (hsub : support ⊆ votes) :
    VoteSetValid E s support := by
  intro u hu
  exact hvalid u (hsub hu)

end VoteSetValid

/-- The equivocators of `votes`, `raw_equivocators votes`; the arguments `E` and `s` are unused. -/
def equivocators (_E : Env V) (votes : Finset (GoldfishVote V)) (_s : Slot) :
    Finset V :=
  raw_equivocators votes

/-- The participants of `votes`, `raw_participants votes`; the arguments `E` and `s` are unused. -/
def participants (_E : Env V) (votes : Finset (GoldfishVote V)) (_s : Slot) :
    Finset V :=
  raw_participants votes

/-- The participants of `votes` that are in the slot-`s` committee. -/
def committee_participants (E : Env V) (votes : Finset (GoldfishVote V))
    (s : Slot) : Finset V :=
  (E.committee s).filter (fun v => participates votes v = true)

/-- The number of participants of `votes` that are in the slot-`s` committee. -/
def committee_voters_count (E : Env V) (votes : Finset (GoldfishVote V))
    (s : Slot) : Nat :=
  (committee_participants E votes s).card

/-- The supporters of `B` in `votes` and `support_votes` at slot `s`,
    `raw_supporters T votes support_votes s B`; the argument `E` is unused. -/
def goldfishSupporters (_E : Env V) (T : Finset (Block V))
    (votes support_votes : Finset (GoldfishVote V)) (s : Slot) (B : Block V) :
    Finset V :=
  raw_supporters T votes support_votes s B

/-! ## Raw and committee-filtered counts agree -/

private theorem committee_of_mem_votes_by
    {E : Env V} {s : Slot} {votes : Finset (GoldfishVote V)}
    (hvalid : VoteSetValid E s votes) {v : V} {u : GoldfishVote V}
    (hu : u ∈ votes_by votes v) : v ∈ E.committee s := by
  rw [votes_by, Finset.mem_filter] at hu
  have hc := (hvalid u hu.1).2
  simpa [hu.2] using hc

private theorem committee_of_participates
    {E : Env V} {s : Slot} {votes : Finset (GoldfishVote V)}
    (hvalid : VoteSetValid E s votes) {v : V}
    (hv : participates votes v = true) : v ∈ E.committee s := by
  rw [participates, decide_eq_true_eq] at hv
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hv
  exact committee_of_mem_votes_by hvalid hu

/-- On a valid vote set, raw and committee-filtered participants agree. -/
theorem raw_participants_eq_committee_participants
    {E : Env V} {s : Slot} {votes : Finset (GoldfishVote V)}
    (hvalid : VoteSetValid E s votes) :
    raw_participants votes = committee_participants E votes s := by
  ext v
  simp only [raw_participants, committee_participants, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · intro hv
    exact ⟨committee_of_participates hvalid hv, hv⟩
  · intro hv
    exact hv.2

/-- On a valid vote set, raw and committee-filtered voter counts agree. -/
theorem raw_voters_count_eq_committee_voters_count
    {E : Env V} {s : Slot} {votes : Finset (GoldfishVote V)}
    (hvalid : VoteSetValid E s votes) :
    raw_voters_count votes = committee_voters_count E votes s := by
  rw [raw_voters_count, committee_voters_count,
    raw_participants_eq_committee_participants hvalid]

end Protocol
end DecoupledConsensusModel

end
