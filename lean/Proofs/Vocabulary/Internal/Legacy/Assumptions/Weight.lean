module
public import Model.Vocabulary.Protocol.Evidence
public import Proofs.Vocabulary.Internal.ModelVocabulary.Execution.Run

@[expose] public section

/-!
# Fault assumptions

The honest committee majority `HonestCommittees`, the weight bound `BelowOneThird`, and the
accountable bound `SlashableBound`.
-/

namespace DecoupledConsensusModel
namespace Execution

open Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Every slot committee has a strict honest majority by count. -/
def HonestCommittees (S : Setup V) (H : Finset V) : Prop :=
  ∀ s : Slot, (S.E.committee s).card < 2 * ((S.E.committee s) ∩ H).card

/-- Faulty validators, the complement of `H`, hold less than one third of the total validator
    weight. -/
def BelowOneThird (S : Setup V) (H : Finset V) : Prop :=
  3 * S.E.electorate.weightOf (Finset.univ \ H) < S.E.W

/-- No two named run blocks expose, through their erased chain evidence, slashable weight of at
    least `2q − W`. -/
def SlashableBound (S : Setup V) (ρ : Run V) : Prop :=
  ∀ B₁ B₂ : NamedBlock V, RunBlock S ρ B₁ → RunBlock S ρ B₂ →
    ¬ HasSlashableWeightBetween S.E
      (chain_attestations B₁.erase) (chain_attestations B₂.erase)

end Execution
end DecoupledConsensusModel

end
