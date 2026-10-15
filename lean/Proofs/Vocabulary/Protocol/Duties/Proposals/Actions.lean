module
public import Proofs.Vocabulary.Protocol.Grades.ProposalParent
public import Proofs.Vocabulary.Protocol.ValidatorClient.Record
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.Walk
public import Proofs.Vocabulary.Internal.ModelVocabulary.Substrate.NamedBlocks
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

@[expose] public section

/-!
# The named proposal and round action

The named proposal and round action as built from one shared read: the parent body lookup, the
proposal's fields, and the fields of the action row.
-/
namespace DecoupledConsensusModel.Proofs.NamedActions
open Protocol.NamedActions
variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- A successful parent lookup returns a body of the store whose erasure is the requested parent. -/
theorem parent_body_spec (st : Protocol.NamedStore V) (parent : Block V)
    (B : NamedBlock V) (h : parentBody? st parent = some B) :
    B ∈ st.bodies ∧ B.erase = parent := by
  unfold parentBody? pickUnique? at h
  split at h
  · rename_i hex
    rw [Option.some_inj] at h
    subst B
    have hs := Finset.choose_spec (fun B : NamedBlock V => decide (B.erase = parent) = true)
      st.bodies hex
    exact ⟨Finset.choose_mem _ _ hex, of_decide_eq_true hs.2⟩
  · simp at h

omit [Fintype V] in
/-- In a store with `NamedStore.ErasureUnique`, the parent lookup returns the body whose erasure is
    the requested parent. -/
theorem parent_body_eq_some (st : Protocol.NamedStore V) (parent : Block V)
    (B : NamedBlock V) (hB : B ∈ st.bodies) (he : B.erase = parent)
    (hu : NamedStore.ErasureUnique st) : parentBody? st parent = some B := by
  apply Protocol.pickUnique?_eq_some hB (by simp [he])
  intro C hC hp
  exact hu C hC B hB ((of_decide_eq_true hp).trans he.symm)


/-- `proposal_with` builds the block from one proposal input and the named row selector, when the
    parent lookup succeeds. -/
theorem proposal_shared_read (contract : Protocol.GradeContract V)
    (source : Protocol.ProposalRowSource) (E : Env V) (hc : Protocol.HealConfig)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) :
    proposal_with contract source E hc nd st =
      let input := Protocol.proposal_input_with contract E hc nd st.core.toHealing
      (parentBody? st input.parent).map fun parent =>
        NamedBlock.node parent input.slot input.root input.gf_votes input.gf_support_votes
          (Protocol.NamedProposalRows.proposalRows parent
            (Protocol.NamedProposalRows.select source hc st)) input.proposer := rfl

/-- When the parent lookup returns `parent`, `proposal_with` returns the block built on `parent`
    from the proposal input. -/
theorem proposal_eq_of_parent (contract : Protocol.GradeContract V)
    (source : Protocol.ProposalRowSource) (E : Env V) (hc : Protocol.HealConfig)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) (parent : NamedBlock V)
    (hp : parentBody? st
      (Protocol.proposal_input_with contract E hc nd st.core.toHealing).parent = some parent) :
    proposal_with contract source E hc nd st =
      some (let input := Protocol.proposal_input_with contract E hc nd st.core.toHealing
        NamedBlock.node parent input.slot input.root input.gf_votes input.gf_support_votes
          (Protocol.NamedProposalRows.proposalRows parent
            (Protocol.NamedProposalRows.select source hc st)) input.proposer) := by
  rw [proposal_shared_read]
  simp only [hp, Option.map_some]

/-- A proposal `B` has a parent that is a body of the store and erases to the input's parent, and
    its slot, root, Goldfish votes, support votes, proposer and attestations are those of the input
    and the row selector. -/
theorem proposal_payload (contract : Protocol.GradeContract V)
    (source : Protocol.ProposalRowSource) (E : Env V) (hc : Protocol.HealConfig)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) (B : NamedBlock V)
    (hout : proposal_with contract source E hc nd st = some B) :
    let input := Protocol.proposal_input_with contract E hc nd st.core.toHealing
    B.parent ∈ st.bodies ∧ B.parent.erase = input.parent ∧
    B.slot = input.slot ∧ B.root = input.root ∧
    B.gf_votes = input.gf_votes ∧ B.gf_support_votes = input.gf_support_votes ∧
    B.attestations = Protocol.NamedProposalRows.proposalRows B.parent
      (Protocol.NamedProposalRows.select source hc st) ∧ B.proposer? = some input.proposer := by
  rw [proposal_shared_read] at hout
  dsimp only at hout ⊢
  cases hp : parentBody? st
      (Protocol.proposal_input_with contract E hc nd st.core.toHealing).parent with
  | none => simp [hp] at hout
  | some parent =>
    rw [hp] at hout
    have he := Option.some.inj hout
    subst B
    obtain ⟨hm, he⟩ := parent_body_spec st _ parent hp
    exact ⟨hm, he, rfl, rfl, rfl, rfl, rfl, rfl⟩


/-- Under `NamedStoreRoots.Invariant`, the parent of the proposal input under the frame contract is
    the erasure of a body that the parent lookup returns. -/
theorem runtime_parent_body_some
    (cache : DecoupledConsensusModel.Protocol.Cache V) (E : Env V) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) (nd : Protocol.Node V)
    (st : Protocol.NamedStore V) (h : Proofs.NamedStoreRoots.Invariant E cfg st) :
    ∃ B ∈ st.bodies, B.erase =
      (Protocol.proposal_input_with (DecoupledConsensusModel.Protocol.frameContract cache)
        E hc nd st.core.toHealing).parent ∧
      parentBody? st (Protocol.proposal_input_with (DecoupledConsensusModel.Protocol.frameContract cache)
        E hc nd st.core.toHealing).parent = some B := by
  obtain ⟨B, ⟨hB, he⟩, _⟩ :=
    NamedProposalParent.proposal_parent_named_body_unique cache E hc cfg nd st h
  exact ⟨B, hB, he, parent_body_eq_some st _ B hB he h.1.2.1⟩

/-- Under `NamedStoreRoots.Invariant`, `proposal_with` under the frame contract returns a block. -/
theorem runtime_proposal_some
    (cache : DecoupledConsensusModel.Protocol.Cache V) (source : Protocol.ProposalRowSource)
    (E : Env V) (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (h : Proofs.NamedStoreRoots.Invariant E cfg st) :
    ∃ B, proposal_with (DecoupledConsensusModel.Protocol.frameContract cache) source E hc nd st = some B := by
  obtain ⟨parent, _, _, hp⟩ := runtime_parent_body_some cache E hc cfg nd st h
  exact ⟨_, proposal_eq_of_parent (DecoupledConsensusModel.Protocol.frameContract cache)
    source E hc nd st parent hp⟩


/-- The named round action creates its row from the attestation input with the node's record. -/
theorem round_action_shared_read (contract : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V)
    (st : Protocol.HealingStore V) (record : Protocol.NamedRecord) :
    round_action_with contract E hc nd st record =
      Protocol.NamedRecord.create record
        (creatorInput (Protocol.attestation_input_with contract E hc nd st)) := rfl


/-- If the named round action's row has height pair `.vote h entry timeout`, the attestation input's
    fields are `(h, entry, nu)` for some `nu`. -/
theorem round_action_names_source (contract : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V)
    (st : Protocol.HealingStore V) (record : Protocol.NamedRecord)
    (h : Height) (entry : BlockId) (timeout : Bool)
    (hp : (round_action_with contract E hc nd st record).2.height_pair =
      .vote h entry timeout) :
    ∃ nu, (Protocol.attestation_input_with contract E hc nd st).fields =
      some (h, entry, nu) := by
  rw [round_action_shared_read] at hp
  exact NamedRecord.create_names_source record
    (creatorInput (Protocol.attestation_input_with contract E hc nd st)) hp


#print axioms parent_body_spec
#print axioms parent_body_eq_some
#print axioms proposal_shared_read
#print axioms proposal_eq_of_parent
#print axioms proposal_payload
#print axioms runtime_parent_body_some
#print axioms runtime_proposal_some
#print axioms round_action_shared_read
#print axioms round_action_names_source
end DecoupledConsensusModel.Proofs.NamedActions

end
