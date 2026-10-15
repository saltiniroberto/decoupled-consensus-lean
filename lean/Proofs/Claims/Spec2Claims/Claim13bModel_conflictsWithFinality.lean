module
public import Model.Vocabulary.Protocol.ChainState
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# Facts about `Protocol.conflictsWithFinality`

Whether a height pair conflicts with a finality pair.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

section ChainStateBodies

attribute [local semireducible] Protocol.conflictsWithFinality

/-- If `hp` is not the timeout at `p.height`, and is a target at `p.height` only for `p.target`,
    then `conflictsWithFinality hp p` is `false`. -/
theorem conflictsWithFinality_eq_false_of (hp : HeightPair) (p : FinalityPair)
    (htimeout : hp ≠ .timeout p.height)
    (htarget : ∀ U : BlockId, hp = .target p.height U → U = p.target) :
    Protocol.conflictsWithFinality hp p = false := by
  cases hp with
  | empty => rfl
  | timeout g =>
      have hg : g ≠ p.height := fun h => htimeout (by rw [h])
      simp [Protocol.conflictsWithFinality, hg]
  | target g U =>
      by_cases hg : g = p.height
      · subst hg
        simp [Protocol.conflictsWithFinality, htarget U rfl]
      · simp [Protocol.conflictsWithFinality, hg]

end ChainStateBodies

end DecoupledConsensusModel.Sts
