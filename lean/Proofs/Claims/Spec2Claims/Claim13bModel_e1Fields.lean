module
public import Model.Vocabulary.Protocol.ChainState
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# Facts about `Protocol.e1Fields`

The E1 field conflict between two attestations, before the one-signer test.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

variable {V : Type}

section ChainStateBodies

attribute [local semireducible] Protocol.e1Fields

/-- If neither attestation's finality pair, when present, conflicts with the other attestation's
    height pair, then `e1Fields left right` is `false`. -/
theorem e1Fields_eq_false_of (left right : CombinedAttestation V)
    (hleft : ∀ p : FinalityPair, left.finality_pair = some p →
      Protocol.conflictsWithFinality right.height_pair p = false)
    (hright : ∀ q : FinalityPair, right.finality_pair = some q →
      Protocol.conflictsWithFinality left.height_pair q = false) :
    Protocol.e1Fields left right = false := by
  unfold Protocol.e1Fields
  cases hl : left.finality_pair with
  | none =>
      cases hr : right.finality_pair with
      | none => rfl
      | some q => simp [hright q hr]
  | some p =>
      cases hr : right.finality_pair with
      | none => simp [hleft p hl]
      | some q => simp [hleft p hl, hright q hr]

end ChainStateBodies

end DecoupledConsensusModel.Sts
