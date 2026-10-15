module
public import Proofs.Vocabulary.Protocol.Handlers.NamedStore
public import Proofs.Vocabulary.Protocol.Handlers.Admission

@[expose] public section

/-!
# Facts about `Execution.NamedReceiptCalls.postCore`

The named store after the core block call.
-/

namespace DecoupledConsensusModel.Proofs.ModelProperties

open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- If the erasure of `B` is already in the tree of `before`, the core call on `B` keeps the bodies
    of `before`. -/
theorem postCore_bodies_of_erase_mem (S : Setup V) (before : Protocol.NamedStore V)
    (B : NamedBlock V) (h : B.erase ∈ before.core.T) :
    (NamedReceiptCalls.postCore S before B).bodies = before.bodies :=
  Proofs.NamedStore.existing_geometry_keeps_bodies S.E S.hc S.cfg before B h

/-- The core call keeps a coherent store coherent. -/
theorem coherent_postCore (S : Setup V) (before : Protocol.NamedStore V) (B : NamedBlock V)
    (h : Proofs.NamedStore.Coherent S.E S.cfg before) :
    Proofs.NamedStore.Coherent S.E S.cfg (NamedReceiptCalls.postCore S before B) :=
  Proofs.NamedStore.coherent_process_block S.E S.hc S.cfg before B h

/-- The core call keeps the clock and the slot. -/
theorem postCore_clock (S : Setup V) (before : Protocol.NamedStore V) (B : NamedBlock V) :
    (NamedReceiptCalls.postCore S before B).core.t = before.core.t ∧
      (NamedReceiptCalls.postCore S before B).core.s = before.core.s :=
  Proofs.NamedAdmission.process_block_clock S.E S.hc S.cfg before B

/-- If `B` is not among the bodies of `before` and is among those after the core call,
    `on_block_with` on `B` at `before` returns the store that admitting `B`'s rows one by one
    returns, started from the store after the core call. -/
theorem on_block_with_eq_admit_rows_postCore (S : Setup V) (before : Protocol.NamedStore V)
    (B : NamedBlock V) (hnew : B ∉ before.bodies)
    (hheld : B ∈ (NamedReceiptCalls.postCore S before B).bodies) :
    Protocol.NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg before B =
      Protocol.NamedAdmission.admit_rows S.hc (NamedReceiptCalls.postCore S before B)
        B.attestations := by
  unfold Protocol.NamedAdmission.on_block_with Protocol.NamedAdmission.admit_carried
  exact if_pos (⟨hnew, hheld⟩ : B ∉ before.bodies ∧
    B ∈ (NamedReceiptCalls.postCore S before B).bodies)

/-- Otherwise, `on_block_with` on `B` at `before` returns the store after the core call. -/
theorem on_block_with_eq_postCore_of_not_new (S : Setup V) (before : Protocol.NamedStore V)
    (B : NamedBlock V)
    (h : ¬ (B ∉ before.bodies ∧ B ∈ (NamedReceiptCalls.postCore S before B).bodies)) :
    Protocol.NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg before B =
      NamedReceiptCalls.postCore S before B := by
  unfold Protocol.NamedAdmission.on_block_with Protocol.NamedAdmission.admit_carried
  exact if_neg h

end DecoupledConsensusModel.Proofs.ModelProperties

end
