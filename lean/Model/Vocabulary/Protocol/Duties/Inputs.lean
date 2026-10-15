module
public import Model.Vocabulary.Objects.Blocks
public import Model.Vocabulary.Protocol.ForkChoice.Head

@[expose] public section

/-!
# Duty inputs and vote choices

The inputs the proposal and attestation duties read, and the SG and finality-gadget vote choices
made through a grade contract.
-/

section
namespace DecoupledConsensusModel.Protocol

structure ProposalInput (V : Type) where
  parent : Block V
  slot : Slot
  root : BlockId
  gf_votes : List (GoldfishVote V)
  gf_support_votes : List (GoldfishVote V)
  proposer : V

/-- The input the attestation duty reads: the validator, the round, the SG vote, the source's
    height, entry root and `nj` flag, and the head's `h_j`, `J` and `h_F`. -/
structure AttestationInput (V : Type) where
  val_index : V
  round : Round
  confirmed : Option BlockId
  fields : Option (Height × BlockId × Bool)
  h_j : Height
  J : BlockId
  h_F : Height

end DecoupledConsensusModel.Protocol
end

section
/-! ## The proposal and round action -/

namespace DecoupledConsensusModel
namespace Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Builds the proposal input (parent head, slot, root, the proposer's votes and support votes,
    proposer) from the store and passes it to `use`. -/
def with_proposal_input {Result : Type} (contract : GradeContract V)
    (E : Env V) (hc : HealConfig) (nd : Protocol.Node V) (st : HealingStore V)
    (use : ProposalInput V → Result) : Result :=
  let s := st.s
  let votes := Protocol.proposer_view st.toFG.toSG.toGoldfishStore s
  let support_votes := Protocol.proposer_support_view st.toFG.toSG.toGoldfishStore s
  let H := get_head_with contract E hc st votes.toFinset support_votes.toFinset (s - 1)
  use ⟨H, s, nd.new_root s, votes, support_votes, nd.val_index⟩

/-! ## The round action -/

/-- The contract's grade-2 candidate for round `r`. -/
def grade2_block_with (contract : GradeContract V)
    (E : Env V) (hc : HealConfig) (st : HealingStore V) (r : Round) :
    Option (Block V) :=
  (contract.read E hc st r).Q2

/-- The SG vote for round `r`, with the grade-2 candidate `A_G2` supplied by the caller. -/
def get_sg_vote_with (contract : GradeContract V)
    (E : Env V) (hc : HealConfig) (st : HealingStore V) (r : Round)
    (A_G2 : Option (Block V)) : Block V :=
  contract.sgVote st { contract.read E hc st r with Q2 := A_G2 }

/-- The finality-gadget source for the grade-2 candidate `A_G2`: the block `deepest_clear` returns,
    or `A_G2` itself when it returns none; `none` when `A_G2` is `none`. -/
def fg_source_with (contract : GradeContract V)
    (E : Env V) (hc : HealConfig) (st : HealingStore V) (r : Round)
    (A_G2 : Option (Block V)) : Option (Block V) :=
  match A_G2 with
  | none => none
  | some q =>
    match deepest_clear (some q) st.live_confirmed
        (contract.read E hc st r).clear with
    | some B => some B
    | none => some q

/-- The finality-gadget fields of the attestation: the source's height, entry root and `nj` flag,
    and the head's `h_j`, `J` root and `h_F`. -/
def get_fg_vote_with (contract : GradeContract V)
    (E : Env V) (hc : HealConfig) (st : HealingStore V) (r : Round)
    (A_G2 : Option (Block V)) :
    Option (Height × BlockId × Bool) × Height × BlockId × Height :=
  let votes := st.pool st.s
  let support_votes :=
    (st.pool st.s).filter (fun u => Protocol.resolved st.T u = true)
  let H := get_head_with contract E hc st votes support_votes st.s
  ((fg_source_with contract E hc st r A_G2).map
      (fun q => ((st.σ q).h, (st.σ q).T_h.root, (st.σ q).nj)),
    (st.σ H).h_j, (st.σ H).J.root, (st.σ H).h_F)

/-- Builds the attestation input for the current round from the store and passes it to `use`. -/
def with_attestation_input {Result : Type} (contract : GradeContract V)
    (E : Env V) (hc : HealConfig) (nd : Protocol.Node V) (st : HealingStore V)
    (use : AttestationInput V → Result) : Result :=
  let r := hc.round_of st.s
  let A_G2 := grade2_block_with contract E hc st r
  let fg := get_fg_vote_with contract E hc st r A_G2
  use ⟨nd.val_index, r, some (get_sg_vote_with contract E hc st r A_G2).root,
    fg.1, fg.2.1, fg.2.2.1, fg.2.2.2⟩

end Protocol
end DecoupledConsensusModel
end

end
