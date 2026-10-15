module
public import Proofs.Vocabulary.Protocol.Schedule.RecoveryHandoffCore
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

@[expose] public section

/-!
# Next-vote adoption from a frozen candidate

Next-vote adoption of a block `D` from the voter candidate tree and the SG root of an honest
validator's confirmation read at the next slot's vote time.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- If `D` is in the voter candidate tree of `w`'s confirmation read at slot `s + 1`'s vote time,
    and that read's SG root is an ancestor of `D`, then `NamedNextVoteAdoption` holds for `D` at
    `w`. -/
theorem nextVoteAdoption_of_frozenCandidateAtRead
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest)
    {s : Slot} {D : Block V}
    (hpost : S.E.t_GST ≤ Protocol.proposal_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {w : V} (hw : w ∈ rho.honest)
    (hcandidate : D ∈ Proofs.Optimistic.voter_candidate_tree S.E
      (NamedActionReads.confirmationReadFrom S
        (Run.stateBeforeTime S rho (Protocol.vote_time S.E (s + 1)) w)
        (Protocol.vote_time S.E (s + 1))).st.core.toHealing)
    (hanchor : Block.Preceq
      (Protocol.get_sg_root_with
        (NamedProfile.gradeContract
          (NamedActionReads.confirmationReadFrom S
            (Run.stateBeforeTime S rho (Protocol.vote_time S.E (s + 1)) w)
            (Protocol.vote_time S.E (s + 1))).cache)
        S.E S.hc
        (NamedActionReads.confirmationReadFrom S
          (Run.stateBeforeTime S rho (Protocol.vote_time S.E (s + 1)) w)
          (Protocol.vote_time S.E (s + 1))).st.core.toHealing
        (S.hc.round_of
          (NamedActionReads.confirmationReadFrom S
            (Run.stateBeforeTime S rho (Protocol.vote_time S.E (s + 1)) w)
            (Protocol.vote_time S.E (s + 1))).st.core.s)) D) :
    NamedNextVoteAdoption S rho
      (Proofs.Optimistic.confStore S rho v s) s D w := by
  have hdata := hcandidate
  simp only [Proofs.Optimistic.voter_candidate_tree,
    Protocol.get_filtered_block_tree_from,
    Protocol.viable_tree, Protocol.finalized_descendants,
    Protocol.viable, Finset.mem_filter, decide_eq_true_eq] at hdata
  have hroot : Block.Preceq
      (Protocol.get_fg_root
        (NamedActionReads.confirmationReadFrom S
          (Run.stateBeforeTime S rho (Protocol.vote_time S.E (s + 1)) w)
          (Protocol.vote_time S.E (s + 1))).st.core.toHealing.toFG) D :=
    hdata.2
  exact nextVoteAdoption_of_recovery_after_gst
    S adm hv hw hpost hhor hroot hanchor hcandidate


#print axioms nextVoteAdoption_of_frozenCandidateAtRead

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
