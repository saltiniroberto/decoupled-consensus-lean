module
public import Model.Vocabulary.Execution.Setup
public import Model.Vocabulary.Protocol.Store
public import Model.Vocabulary.Protocol.ChainState

@[expose] public section

/-!
# Finality slashing evidence

The attestations a chain and a store hold, slashability between two evidence sets, and the slashable
weight `2q − W` used by accountable finality.
-/

namespace DecoupledConsensusModel

open Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The attestations included in `B` and its ancestors: `⋃_{C ⪯ B} C.attestations`. -/
def chain_attestations : Block V → Finset (CombinedAttestation V)
  | .genesis => ∅
  | .node p _ _ _ _ ats _ => ats.toFinset ∪ chain_attestations p

/-- The attestations included in the blocks of the store's tree and their ancestors. -/
def store_attestations (st : Protocol.Store V) : Finset (CombinedAttestation V) :=
  st.T.biUnion chain_attestations

/-- Validator `i` is slashable between two evidence sets: an attestation of `i` from each, together
    satisfying E1 or E2; `a = b` is allowed. -/
def SlashableBetween (A₁ A₂ : Finset (CombinedAttestation V)) (i : V) : Prop :=
  ∃ a ∈ A₁, ∃ b ∈ A₂, a.val_index = i ∧ b.val_index = i ∧ Protocol.Slashable a b

/-- The intersection weight bound `w(S) ≥ 2q − W`, written `2q ≤ W + w(S)`. -/
def HasIntersectionWeight (E : Env V) (S : Finset V) : Prop :=
  2 * E.q ≤ E.W + E.electorate.weightOf S

/-- Some set of validators of weight at least `2q − W` is slashable between the two evidence sets. -/
def HasSlashableWeightBetween (E : Env V)
    (A₁ A₂ : Finset (CombinedAttestation V)) : Prop :=
  ∃ S : Finset V, HasIntersectionWeight E S ∧ ∀ i ∈ S, SlashableBetween A₁ A₂ i

end DecoupledConsensusModel

end
