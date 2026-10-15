module
public import Proofs.Vocabulary.Objects.BlockVisibilityCore
public import Proofs.Vocabulary.Generic.PostGSTCarrierAdmissionCore
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.GradeBootstrapCore
public import Proofs.Vocabulary.Objects.FixedHeightRootCore
public import Proofs.Vocabulary.Protocol.Handlers.HMaxCore
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section


namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]


omit [Fintype V] in
private theorem mem_named_chain_attestations_own_l1
    {A : NamedBlock V} {a : NamedAttestation V}
    (ha : a ∈ A.attestations) :
    a ∈ Protocol.named_chain_attestations A := by
  cases A with
  | genesis => simp [NamedBlock.attestations] at ha
  | node p s r gv gsv rows proposer =>
      exact Finset.mem_union_right _ (List.mem_toFinset.mpr ha)


namespace DecoupledConsensusModel.Proofs.HealingSurface
end DecoupledConsensusModel.Proofs.HealingSurface

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
