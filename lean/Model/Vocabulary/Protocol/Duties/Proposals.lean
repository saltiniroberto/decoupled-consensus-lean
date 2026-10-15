module
public import Mathlib.Data.Finset.Sort
public import Model.Vocabulary.Protocol.Handlers
public import Model.Vocabulary.Protocol.Duties.Inputs
public import Model.Vocabulary.Protocol.ValidatorClient

@[expose] public section

/-!
# Proposal and vote duties

The rows an honest proposal includes, the proposal itself, and the Goldfish vote, confirmation and
attestation duties over the named store.
-/

section
/-! ## Proposal rows -/
namespace DecoupledConsensusModel
namespace Protocol

inductive ProposalRowSource where
  | poolAndCarried
  deriving DecidableEq, Repr

namespace ProposalRows
variable {V : Type} [DecidableEq V]

/-- The SG admission window: round `r` lies in `[round(s) − η_SG, round(s)]` for the store's slot
    `s`. -/
def inWindow (hc : Protocol.HealConfig) (st : Store V) (r : Round) : Bool :=
  decide (hc.round_of st.s - hc.η_SG ≤ r ∧ r ≤ hc.round_of st.s)

end ProposalRows
end Protocol
end DecoupledConsensusModel
end

section
namespace DecoupledConsensusModel.Protocol.NamedProposalRows
variable {V : Type} [DecidableEq V]

def processedRows (hc : Protocol.HealConfig) (st : NamedStore V) : List (NamedAttestation V) :=
  (List.range (hc.round_of st.core.s + 1)).flatMap st.sg_rows

def orderedRoots (st : NamedStore V) : List BlockId :=
  (st.bodies.image NamedBlock.root).sort (fun a b => a ≤ b)

/-- The store's named blocks, one per root of `orderedRoots st`; a root held by more than one block
    is skipped. -/
def orderedBodies (st : NamedStore V) : List (NamedBlock V) :=
  (orderedRoots st).filterMap fun root =>
    pickUnique? st.bodies (fun B => decide (B.root = root))

def eligibleBody (hc : Protocol.HealConfig) (st : NamedStore V) (B : NamedBlock V) : Bool :=
  ProposalRows.inWindow hc st.core (hc.round_of B.slot) &&
    carried_attestations_admissible hc B.erase

def poolRows (hc : Protocol.HealConfig) (st : NamedStore V) : List (NamedAttestation V) :=
  (processedRows hc st).filter (fun row => ProposalRows.inWindow hc st.core row.round)

def carriedRows (hc : Protocol.HealConfig) (st : NamedStore V) : List (NamedAttestation V) :=
  (orderedBodies st).flatMap fun B =>
    if eligibleBody hc st B then
      B.attestations.filter (fun row => ProposalRows.inWindow hc st.core row.round)
    else []

def select (source : ProposalRowSource) (hc : Protocol.HealConfig) (st : NamedStore V) :
    List (NamedAttestation V) :=
  poolRows hc st ++ carriedRows hc st

/-- The named attestations included in a block and all its ancestors. -/
def chainRows : NamedBlock V → List (NamedAttestation V)
  | .genesis => []
  | .node p _ _ _ _ rows _ => rows ++ chainRows p

def excludeOnChain (head : NamedBlock V) (rows : List (NamedAttestation V)) :
    List (NamedAttestation V) := rows.filter (fun row => !decide (row ∈ chainRows head))

/-- Keep the first two distinct full rows of each (validator, round), in list
order; later rows of that pair and repeated rows are dropped. -/
def capPerSigner (rows : List (NamedAttestation V)) : List (NamedAttestation V) :=
  rows.foldl (fun acc row =>
    if row ∈ acc ||
        decide (2 ≤ (acc.filter (fun a =>
          decide (a.val_index = row.val_index ∧ a.round = row.round))).length)
    then acc else acc ++ [row]) []

/-- The honest proposal's rows: drop rows already on the parent chain, then keep at most two
    distinct rows per (validator, round). -/
def proposalRows (parent : NamedBlock V) (rows : List (NamedAttestation V)) :
    List (NamedAttestation V) :=
  capPerSigner (excludeOnChain parent rows)

end DecoupledConsensusModel.Protocol.NamedProposalRows
end

section
/-! ## Named proposal and attestation -/
namespace DecoupledConsensusModel.Protocol.NamedActions
variable {V : Type} [DecidableEq V] [Fintype V]

/-- The unique named block of the store that erases to `parent`. -/
def parentBody? (st : Protocol.NamedStore V) (parent : Block V) : Option (NamedBlock V) :=
  pickUnique? st.bodies (fun B => decide (B.erase = parent))

/-- The honest named proposal: a block on the named parent with the proposal input's slot, root,
    votes and proposer, and `proposalRows` of the selected rows; `none` when the parent's named
    block is not found. -/
def proposal_with (contract : GradeContract V) (source : Protocol.ProposalRowSource)
    (E : Env V) (hc : HealConfig) (nd : Protocol.Node V)
    (st : Protocol.NamedStore V) : Option (NamedBlock V) :=
  with_proposal_input contract E hc nd st.core.toHealing fun input =>
    (parentBody? st input.parent).map fun parent =>
      NamedBlock.node parent input.slot input.root input.gf_votes input.gf_support_votes
        (Protocol.NamedProposalRows.proposalRows parent
          (Protocol.NamedProposalRows.select source hc st)) input.proposer

/-- The signing record's input built from an attestation input. -/
def creatorInput (input : AttestationInput V) : Protocol.NamedRecord.Input V :=
  ⟨input.val_index, input.round, input.confirmed, input.fields,
    input.h_j, input.J, input.h_F⟩

/-- The round action: the signing record creates the named attestation from the attestation input;
    returns the updated record and the attestation. -/
def round_action_with (contract : GradeContract V)
    (E : Env V) (hc : HealConfig) (nd : Protocol.Node V)
    (st : HealingStore V) (record : Protocol.NamedRecord) :
    Protocol.NamedRecord × NamedAttestation V :=
  with_attestation_input contract E hc nd st fun input =>
    Protocol.NamedRecord.create record (creatorInput input)

end DecoupledConsensusModel.Protocol.NamedActions
end

section
/-! ## Named duties -/
namespace DecoupledConsensusModel.Protocol.NamedDuties
variable {V : Type} [DecidableEq V] [Fintype V]

/-- The proposal duty: build the honest named proposal and add it, with the objects it carries, to
    the store; the store is unchanged when no proposal is built. -/
def propose_block_with (contract : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig)
    (nd : Protocol.Node V) (st : NamedStore V) : NamedStore V × Option (NamedBlock V) :=
  match Protocol.NamedActions.proposal_with contract .poolAndCarried E hc nd st with
  | none => (st, none)
  | some B => (NamedAdmission.on_block_with .alsoCarried E hc cfg st B, some B)

/-- The Goldfish vote duty on the core store; returns the new store and the vote, if any. -/
def goldfish_vote_with (contract : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V)
    (st : NamedStore V) : NamedStore V × Option (GoldfishVote V) :=
  let out := Protocol.goldfish_vote_with contract E hc nd st.core
  ({ st with core := out.1 }, out.2)

/-- The confirmation update on the core store at slot `s`. -/
def update_confirmation_with (contract : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (st : NamedStore V) (s : Slot) : NamedStore V :=
  { st with core := Protocol.update_confirmation_with contract E hc st.core s }

/-- The attestation duty: create the named attestation from the store, add it to the store, and
    return the new store, the new signing record and the attestation. -/
def attest_with (contract : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V)
    (st : NamedStore V) (record : Protocol.NamedRecord) :
    NamedStore V × Protocol.NamedRecord × NamedAttestation V :=
  let out := Protocol.NamedActions.round_action_with contract E hc nd st.core.toHealing record
  (NamedAdmission.admit_row hc st out.2, out.1, out.2)

end DecoupledConsensusModel.Protocol.NamedDuties
end

end
