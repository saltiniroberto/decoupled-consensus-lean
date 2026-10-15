module
public import Model.Vocabulary.Protocol.ChainState
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# Facts about `Protocol.Slashable` and `Protocol.slashable`

The Boolean slashing test `Protocol.slashable` and its proposition `Protocol.Slashable`, on one page
because their names differ only in the case of one letter.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.sameValidator

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type} [DecidableEq V]

section ChainStateBodies

attribute [local semireducible] Protocol.slashable Protocol.e1Slashable Protocol.e2Slashable
  Protocol.Slashable

/-- If `e1Fields left right` and `e2Fields left right` are both `false`, then `slashable left right`
    is `false`, whoever signed the two attestations. -/
theorem slashable_eq_false_of_fields (left right : CombinedAttestation V)
    (h1 : Protocol.e1Fields left right = false) (h2 : Protocol.e2Fields left right = false) :
    Protocol.slashable left right = false := by
  simp [Protocol.slashable, Protocol.e1Slashable, Protocol.e2Slashable, h1, h2]

/-- `left` and `right` are not slashable exactly when `slashable left right` is `false`. -/
theorem not_Slashable_iff (left right : CombinedAttestation V) :
    ¬ Protocol.Slashable left right ↔ Protocol.slashable left right = false := by
  simp [Protocol.Slashable]

end ChainStateBodies

end DecoupledConsensusModel.Sts
