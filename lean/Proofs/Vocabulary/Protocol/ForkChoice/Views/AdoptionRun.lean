module
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.Adoption

@[expose] public section

/-!
# Next-vote adoption

The structure `NamedNextVoteAdoption`: the facts at an honest validator's next-slot vote duty that
carry a block confirmed at slot `s` into that validator's Goldfish vote.
-/

namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]


/-- The facts at `w`'s vote duty for slot `s + 1` that make its Goldfish vote adopt `B`: the
    confirmation support of `source` is transported to the vote view, the support view is contained
    in the vote view, the SG root is compatible with `B`, and the path from the SG root to `B` is in
    the candidate tree. -/
structure NamedNextVoteAdoption (S : Setup V) (rho : Run V)
    (source : Protocol.Store V) (s : Slot) (B : Block V) (w : V) : Prop where
  transport :
    let read := NamedActionReads.confirmationReadFrom S
      (Run.stateBeforeTime S rho (Protocol.vote_time S.E (s + 1)) w)
      (Protocol.vote_time S.E (s + 1))
    AdoptionTransport source.T read.st.core.T
      (confVotes S.E source s) (confLate S.E source s)
      (Protocol.voter_view S.E read.st.core.toHealing.toFG.toSG.toGoldfishStore read.st.core.s)
      (Protocol.voter_support_view S.E read.st.core.toHealing.toFG.toSG.toGoldfishStore read.st.core.s)
      B
  support_subset :
    let read := NamedActionReads.confirmationReadFrom S
      (Run.stateBeforeTime S rho (Protocol.vote_time S.E (s + 1)) w)
      (Protocol.vote_time S.E (s + 1))
    Protocol.voter_support_view S.E read.st.core.toHealing.toFG.toSG.toGoldfishStore read.st.core.s ⊆
      Protocol.voter_view S.E read.st.core.toHealing.toFG.toSG.toGoldfishStore read.st.core.s
  anchor :
    let read := NamedActionReads.confirmationReadFrom S
      (Run.stateBeforeTime S rho (Protocol.vote_time S.E (s + 1)) w)
      (Protocol.vote_time S.E (s + 1))
    Block.compatible
      (Protocol.get_sg_root_with (NamedProfile.gradeContract read.cache)
        S.E S.hc read.st.core.toHealing (S.hc.round_of read.st.core.s)) B = true
  path :
    let read := NamedActionReads.confirmationReadFrom S
      (Run.stateBeforeTime S rho (Protocol.vote_time S.E (s + 1)) w)
      (Protocol.vote_time S.E (s + 1))
    Block.Preceq
        (Protocol.get_sg_root_with (NamedProfile.gradeContract read.cache)
          S.E S.hc read.st.core.toHealing (S.hc.round_of read.st.core.s)) B →
      ∀ C : Block V,
        Block.Preceq
            (Protocol.get_sg_root_with (NamedProfile.gradeContract read.cache)
              S.E S.hc read.st.core.toHealing (S.hc.round_of read.st.core.s)) C →
        C ≠ Protocol.get_sg_root_with (NamedProfile.gradeContract read.cache)
          S.E S.hc read.st.core.toHealing (S.hc.round_of read.st.core.s) →
        Block.Preceq C B →
        C ∈ Protocol.voter_filtered_block_tree S.E read.st.core read.st.core.s
  run :
    let read := NamedActionReads.confirmationReadFrom S
      (Run.stateBeforeTime S rho (Protocol.vote_time S.E (s + 1)) w)
      (Protocol.vote_time S.E (s + 1))
    ∃ C : NamedBlock V,
      C.erase = Protocol.get_head_in_tree_with_layer
        (NamedProfile.gradeContract read.cache) S.E S.hc read.st.core.toHealing
        (Protocol.voter_filtered_block_tree S.E read.st.core read.st.core.s)
        (Protocol.voter_view S.E read.st.core.toHealing.toFG.toSG.toGoldfishStore read.st.core.s)
        (Protocol.voter_support_view S.E read.st.core.toHealing.toFG.toSG.toGoldfishStore read.st.core.s)
        (read.st.core.s - 1) ∧ RunBlock S rho C
  emit : ∀ u : GoldfishVote V,
    let read := NamedActionReads.confirmationReadFrom S
      (Run.stateBeforeTime S rho (Protocol.vote_time S.E (s + 1)) w)
      (Protocol.vote_time S.E (s + 1))
    (Protocol.NamedDuties.goldfish_vote_with
      (NamedProfile.gradeContract read.cache) S.E S.hc (S.node w) read.st).2 = some u →
    rho.emits S w (Object.gfVote u) (Protocol.vote_time S.E (s + 1))


end Protocol
end DecoupledConsensusModel

end
