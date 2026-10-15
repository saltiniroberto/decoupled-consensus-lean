module

public import Model.Vocabulary.Protocol.Duties.Proposals
public import Proofs.Claims.ModelIrreducible
public import Proofs.Vocabulary.ModelProperties.NamedDuties_goldfish_vote_with
public import Proofs.Vocabulary.Protocol.Handlers.Invariants

@[expose] public section

/-!
# Facts about `NamedDuties.goldfish_vote_with`

The lemmas that unfold the named-store wrapper of the Goldfish vote duty,
`NamedDuties.goldfish_vote_with`.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Block.root
  DecoupledConsensusModel.Env.committee
  DecoupledConsensusModel.Protocol.NamedDuties.goldfish_vote_with
  DecoupledConsensusModel.Protocol.goldfish_vote_with

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The vote, if any, that the named Goldfish vote duty returns on `st` is the vote the Goldfish
    vote duty returns on the core store of `st`. -/
theorem namedDuties_goldfish_vote_with_snd (contract : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V) :
    (Protocol.NamedDuties.goldfish_vote_with contract E hc nd st).2
      = (Protocol.goldfish_vote_with contract E hc nd st.core).2 := rfl

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- If the named Goldfish vote duty signs the vote `u` on `st`, then the head of `u` is the root of
    the head `get_head_in_tree_with_layer` computes over the vote tree, the vote view and the
    support view of `st`'s core store at `st`'s slot. -/
theorem namedDuties_goldfish_vote_with_snd_head (contract : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    {u : GoldfishVote V}
    (h : (Protocol.NamedDuties.goldfish_vote_with contract E hc nd st).2 = some u) :
    u.head = (Protocol.get_head_in_tree_with_layer contract E hc st.core.toHealing
      (Protocol.voter_filtered_block_tree E st.core st.core.s)
      (Protocol.voter_view E st.core.toHealing.toFG.toSG.toGoldfishStore st.core.s)
      (Protocol.voter_support_view E st.core.toHealing.toFG.toSG.toGoldfishStore st.core.s)
      (st.core.s - 1)).root := by
  by_cases hcom : nd.val_index ∈ E.committee st.core.s
  · rw [Proofs.ModelProperties.goldfish_vote_with_snd_of_mem_committee contract E hc nd st hcom]
      at h
    exact (congrArg GoldfishVote.head (Option.some.inj h)).symm
  · rw [namedDuties_goldfish_vote_with_snd] at h
    simp [Protocol.goldfish_vote_with, hcom] at h

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The core store of the store the named Goldfish vote duty returns is the store the core Goldfish
    vote duty returns on the core store of `st`. -/
theorem namedDuties_goldfish_vote_with_fst_core (contract : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V) :
    (Protocol.NamedDuties.goldfish_vote_with contract E hc nd st).1.core =
      (Protocol.goldfish_vote_with contract E hc nd st.core).1 := rfl

end DecoupledConsensusModel.Sts


namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]


end DecoupledConsensusModel.Sts

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The named Goldfish vote duty keeps the finalized block of `st`'s core store. -/
theorem namedDuties_goldfish_vote_with_fst_core_F (contract : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V) :
    (Protocol.NamedDuties.goldfish_vote_with contract E hc nd st).1.core.F = st.core.F := by
  rw [namedDuties_goldfish_vote_with_fst_core]
  simp only [Protocol.goldfish_vote_with]
  split_ifs
  · exact Proofs.on_goldfish_vote_checked_F E st.core _
  · rfl

/-- The named Goldfish vote duty keeps the named rows of `st`. -/
theorem namedDuties_goldfish_vote_with_fst_sg_rows (contract : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V) :
    (Protocol.NamedDuties.goldfish_vote_with contract E hc nd st).1.sg_rows = st.sg_rows := rfl

/-- The named Goldfish vote duty keeps the bodies of `st`. -/
theorem namedDuties_goldfish_vote_with_fst_bodies (contract : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V) :
    (Protocol.NamedDuties.goldfish_vote_with contract E hc nd st).1.bodies = st.bodies := rfl

/-- The store the Goldfish vote duty returns is `st`, or the store the checked Goldfish-vote handler
    returns on `st` and some vote `u`. -/
theorem goldfish_vote_with_fst_cases (contract : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : Protocol.Store V) :
    (Protocol.goldfish_vote_with contract E hc nd st).1 = st ∨
      ∃ u : GoldfishVote V,
        (Protocol.goldfish_vote_with contract E hc nd st).1 =
          Protocol.on_goldfish_vote_checked E st u := by
  simp only [Protocol.goldfish_vote_with]
  split
  · exact Or.inr ⟨_, rfl⟩
  · exact Or.inl rfl

end DecoupledConsensusModel.Sts
