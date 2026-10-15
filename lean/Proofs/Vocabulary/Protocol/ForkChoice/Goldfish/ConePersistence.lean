module
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.Agreement

@[expose] public section

/-!
# A cone of honest support gives a supporter majority

When every honest committee member's vote supports a descendant of `B`, `B`'s supporters are a
strict majority of the participants.
-/

namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Under `ConeSupport` for the descendants of `B` on a valid vote set, `B`'s supporters are a
    strict majority of the participants. -/
theorem supporterMajority_of_cone
    (E : Env V) {T : Finset (Block V)}
    {votes support : Finset (GoldfishVote V)} {s : Slot}
    {Hon : Finset V} {B : Block V}
    (hcone : Proofs.Optimistic.ConeSupport E T votes support votes s Hon
      (fun X => Block.Preceq B X))
    (hvalid : Protocol.VoteSetValid E s votes) :
    Protocol.voters_count E votes s <
      2 * (Protocol.goldfishSupporters E T votes support s B).card := by
  have hsub : (E.committee s) ∩ Hon ⊆
      Protocol.goldfishSupporters E T votes support s B :=
    hcone.subset_supporters (by
      intro X hBX
      exact hBX)
  have hcard := Finset.card_le_card hsub
  have hcount := hcone.count_lt hvalid
  omega

end Protocol
end DecoupledConsensusModel

end
