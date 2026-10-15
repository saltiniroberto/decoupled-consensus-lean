module
public import Proofs.Vocabulary.Objects.FixedHeightRootCore
import Proofs.Vocabulary.Execution.Acceptance
import Proofs.Vocabulary.Generic.PostGSTCarrierAdmissionCore
import Proofs.Vocabulary.Protocol.Handlers.HMaxCore
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

@[expose] public section

/-!
# Attestations of a named chain

A private fact: a named block's own attestations are among those of its chain.
-/


namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]


omit [Fintype V] in
private theorem mem_named_chain_attestations_own {A : NamedBlock V} {a : NamedAttestation V}
    (ha : a ∈ A.attestations) : a ∈ Protocol.named_chain_attestations A := by
  cases A with
  | genesis => simp [NamedBlock.attestations] at ha
  | node p s r gv gsv rows proposer =>
      exact Finset.mem_union_right _ (List.mem_toFinset.mpr ha)


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
