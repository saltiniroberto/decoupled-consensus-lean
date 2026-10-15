module
public import Model.Vocabulary.Protocol.Handlers
public import Model.Vocabulary.Statements.Instantiation.Certificates

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Derived-state invariants over named blocks

Store invariants that read a held body's chain state through `derive_named`.
-/


namespace DecoupledConsensusModel.Internal
open Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

/-- Every held body's cached chain state is its named derivation. -/
def NamedDerivedStateAgrees (E : Env V) (cfg : HeightConfig)
    (st : Protocol.NamedStore V) : Prop :=
  ∀ B ∈ st.bodies, st.core.σ B.erase = derive_named E cfg B

/-- The named derivation of `C` justifies `T` at height `h`. -/
def NamedJustifiedAt (E : Env V) (cfg : HeightConfig) (C : NamedBlock V) (T : Block V)
    (h : Height) : Prop :=
  (derive_named E cfg C).J = T ∧ (derive_named E cfg C).h_j = h

/-- Every held body's named justification height is at most the store's current one. -/
def NamedNoHighJustifications (E : Env V) (cfg : HeightConfig)
    (st : Protocol.NamedStore V) : Prop :=
  ∀ B ∈ st.bodies, (derive_named E cfg B).h_j ≤ st.core.h_j

end DecoupledConsensusModel.Internal

end
