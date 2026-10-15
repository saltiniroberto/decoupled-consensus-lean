import Proofs.Claims.Spec2Claims.Claim13beRoute3_23
import Proofs.Claims.Spec2Claims.Claim13bModel_author
import Proofs.Claims.Spec2Claims.Claim13bModel_round_of
import Proofs.Vocabulary.ModelProperties.NamedStore_process_block_core
import Proofs.Claims.Spec2Claims.Claim13bModel_on_sg_vote
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedAttestation_erase
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedAdmission_admit_row_s4
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedAdmission_on_block_with

/-!
# The first flip of a Boolean, and the rows across the block core

A Boolean that turns from `false` to `true` between two indices flips at some index between them,
and `NamedStore.process_block_core` leaves the named rows unchanged.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- A Boolean `p` with `p a = false` and `p b = true`, `a ≤ b`, turns from `false` to `true` at some
    `m` with `a ≤ m < b`. -/
theorem exists_flip_between (p : Nat → Bool) {a b : Nat} (hab : a ≤ b) (ha : p a = false)
    (hb : p b = true) : ∃ m, a ≤ m ∧ m < b ∧ p m = false ∧ p (m + 1) = true := by
  induction b, hab using Nat.le_induction with
  | base => rw [ha] at hb; exact absurd hb (by simp)
  | succ b hab ih =>
      by_cases hpb : p b = true
      · obtain ⟨m, ham, hmb, h0, h1⟩ := ih hpb
        exact ⟨m, ham, Nat.lt_succ_of_lt hmb, h0, h1⟩
      · exact ⟨b, hab, Nat.lt_succ_self b, Bool.eq_false_iff.2 hpb, hb⟩

/-- `NamedStore.process_block_core` leaves the named rows `sg_rows` unchanged. -/
theorem process_block_core_sg_rows_eq (S : Setup V) (st : Protocol.NamedStore V)
    (B : NamedBlock V) :
    (Protocol.NamedStore.process_block_core S.E S.hc S.cfg st B).sg_rows = st.sg_rows := by
  by_cases hp : B.parent ∈ st.bodies
  · rw [Proofs.ModelProperties.process_block_core_of_parent_mem S.E S.hc S.cfg hp]
    exact Proofs.NamedStore.commit_rows st _ B
  · rw [Proofs.ModelProperties.process_block_core_of_parent_not_mem S.E S.hc S.cfg hp]

end DecoupledConsensusModel.Sts
