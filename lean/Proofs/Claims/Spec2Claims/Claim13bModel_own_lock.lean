import Model.Vocabulary.Protocol.ValidatorClient
import Proofs.Claims.ModelIrreducible

/-!
# Facts about `Protocol.own_lock`

Lemmas that unfold the validator's own lock at a height, read from the finality pair of the
attestation being built when that pair is at the height, and from the record otherwise.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.own_lock

set_option autoImplicit false


namespace DecoupledConsensusModel.Sts

/-- Without a finality pair, the validator's lock at height `h` is the lock its record `Λ` holds at
    `h`. -/
theorem own_lock_none (Λ : Protocol.Record) (h : Height) :
    Protocol.own_lock Λ h none = Λ.lock h := rfl

/-- When the finality pair `p` is at a height other than `h`, the validator's lock at height `h` is
    the lock its record `Λ` holds at `h`. -/
theorem own_lock_some_of_ne (Λ : Protocol.Record) (h : Height) {p : FinalityPair}
    (hp : p.height ≠ h) : Protocol.own_lock Λ h (some p) = Λ.lock h := by
  simp only [Protocol.own_lock, if_neg hp]

end DecoupledConsensusModel.Sts

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts


/-- If the finality pair `p` is not at height `h`, the lock the record `Λ` gives at height `h` with
    `p` is the record's own lock at `h`. -/
theorem own_lock_some_of_ne_explicit (Λ : Protocol.Record) (h : Height) (p : FinalityPair)
    (hne : ¬ p.height = h) :
    Protocol.own_lock Λ h (some p) = Λ.lock h := by
  simp only [Protocol.own_lock, if_neg hne]

end DecoupledConsensusModel.Sts

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts


/-- If the finality pair's height `h'` is not `h`, the own lock at height `h` of the record `Λ` with
    that pair is the lock `Λ` holds at `h`. -/
theorem own_lock_some_pair_of_ne (Λ : Protocol.Record) {h h' : Height} (J : BlockId)
    (hne : h' ≠ h) : Protocol.own_lock Λ h (some ⟨h', J⟩) = Λ.lock h := by
  unfold Protocol.own_lock
  exact if_neg hne

end DecoupledConsensusModel.Sts
