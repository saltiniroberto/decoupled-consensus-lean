module
public import Model.Vocabulary.Protocol.Grades

@[expose] public section

/-!
# Weights and equivocation among tokens

The weight of a validator set under a weight function, and equivocation among received tokens at one
round.
-/
namespace DecoupledConsensusModel.Protocol

variable {Key Block : Type*}

section Weights

variable {V : Type*} [Fintype V] [DecidableEq V]

def weight (w : V → Nat) (s : Finset V) : Nat := ∑ v ∈ s, w v

noncomputable def coverSupporters (covers : Key → Block → Prop)
    (early late raw : V → Finset (Token Key)) (B : Block) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => Supports covers (early v) (late v) (raw v) B)

noncomputable def opponents (covers : Key → Block → Prop)
    (early late raw : V → Finset (Token Key)) (B : Block) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => Opposes covers (early v) (late v) (raw v) B)

noncomputable def grade (w : V → Nat) (covers : Key → Block → Prop)
    (early late raw : V → Finset (Token Key)) (B : Block) : Prop :=
  weight w (opponents covers early late raw B) <
    weight w (coverSupporters covers early late raw B)

end Weights

/-- Equivocation at round `k`: two tokens of `raw` at round `k` with different keys. -/
def EquivocationAt (raw : Finset (Token Key)) (k : Nat) : Prop :=
  ∃ x ∈ raw, ∃ y ∈ raw, x.round = k ∧ y.round = k ∧ x.key ≠ y.key

end DecoupledConsensusModel.Protocol

end
