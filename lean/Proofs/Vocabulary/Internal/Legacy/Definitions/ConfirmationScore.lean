module
public import Model.Vocabulary.Protocol.Store
public import Model.Vocabulary.Execution.Objects

@[expose] public section

/-!
# Confirmation score and eligibility

The early and late vote sets, the score and the eligibility test of the confirmation evaluation.
-/


namespace DecoupledConsensusModel
namespace Internal
open Execution
variable {V : Type} [DecidableEq V] [Fintype V]

/-- The early vote set of the confirmation evaluation: the slot-`s` pool votes whose `tau` stamp is
    before the support cutoff. -/
def confirmationEarly (E : Env V) (st : Protocol.Store V) (s : Slot) :
    Finset (GoldfishVote V) :=
  beforeCutoff st.tau (Protocol.support_cutoff E s) (st.pool s)

/-- The late vote set of the confirmation evaluation: the slot-`s` pool votes whose receipt stamp is
    before the confirmation time. -/
def confirmationLate (E : Env V) (st : Protocol.Store V) (s : Slot) :
    Finset (GoldfishVote V) :=
  beforeCutoff st.timestamp_vote (Protocol.confirmation_time E s) (st.pool s)

/-- The non-equivocating votes of the early set. -/
def confirmationVotes (E : Env V) (st : Protocol.Store V) (s : Slot) :
    Finset (GoldfishVote V) :=
  (confirmationEarly E st s).filter
    (fun u => Protocol.no_second_vote_in (confirmationLate E st s) u = true)

/-- The confirmation score of `B`. -/
def confirmationScore (E : Env V) (st : Protocol.Store V) (s : Slot)
    (B : Block V) : Nat :=
  Protocol.goldfish_score E st.T (confirmationVotes E st s)
    (confirmationVotes E st s) s B

/-- The confirmation eligibility test of `B`. -/
def confirmationEligible (E : Env V) (st : Protocol.Store V) (s : Slot)
    (B : Block V) : Bool :=
  decide (Protocol.voters_count E (confirmationLate E st s) s <
    2 * confirmationScore E st s B)

end Internal
end DecoupledConsensusModel

end
