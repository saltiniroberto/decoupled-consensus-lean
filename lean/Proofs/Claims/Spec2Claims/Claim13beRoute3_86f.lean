import Proofs.Claims.Spec2Claims.Claim13beRoute3_86e
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.ConePersistence
import Proofs.Claims.Spec2Claims.Claim13bModel_goldfish_fork_choice
import Proofs.Claims.Spec2Claims.Claim13bModel_opening_slot_mk

/-!
# Opening-slot arithmetic two rounds after a deadline

The round and slot inequalities for an opening at a round `m` with `D + 2 ≤ m`.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Statements.Instantiation

variable {V : Type} [DecidableEq V] [Fintype V]

section OpeningPivot

/-- If `2 ≤ R`, `y + R = start` and `x + 2R ≤ start`, then `x + 1 ≤ start − 1`, `x + 2 ≤ start`,
    `y + 1 ≤ start − 1`, `0 < start − 1`, `start − 1 + 1 = start` and `x + 2 ≤ start − 1`. -/
theorem openingBookkeeping_l86f (x y R start : Nat) (hR : 2 ≤ R) (hy : y + R = start)
    (hx : x + 2 * R ≤ start) :
    x + 1 ≤ start - 1 ∧ x + 2 ≤ start ∧ y + 1 ≤ start - 1 ∧ 0 < start - 1 ∧
      start - 1 + 1 = start ∧ x + 2 ≤ start - 1 := by
  omega

/-- If `D + 2 ≤ m`, then `m − 2 + 1 = m − 1`, `m − 1 + 1 = m` and `D ≤ m − 2`. -/
theorem roundArith_l86f (D m : Nat) (hm : D + 2 ≤ m) :
    m - 2 + 1 = m - 1 ∧ m - 1 + 1 = m ∧ D ≤ m - 2 := by
  omega

/-- If `D + 2 ≤ m`, then with `start` the opening slot of `m` and `d = start − 1`:
    `opening_slot D + 1 ≤ d`, `opening_slot D + 2 ≤ start`, `opening_slot (m − 1) + 1 ≤ d`, `0 < d`,
    `d + 1 = start`, `m − 2 + 1 = m − 1`, `m − 1 + 1 = m`, `D ≤ m − 2` and `opening_slot D + 2 ≤ d`. -/
theorem openingSlots_l86f (S : Setup V) {D m : Round} (hm : D + 2 ≤ m) :
    S.hc.opening_slot D + 1 ≤ S.hc.opening_slot m - 1 ∧
      S.hc.opening_slot D + 2 ≤ S.hc.opening_slot m ∧
      S.hc.opening_slot (m - 1) + 1 ≤ S.hc.opening_slot m - 1 ∧
      0 < S.hc.opening_slot m - 1 ∧
      S.hc.opening_slot m - 1 + 1 = S.hc.opening_slot m ∧
      m - 2 + 1 = m - 1 ∧ m - 1 + 1 = m ∧ D ≤ m - 2 ∧
      S.hc.opening_slot D + 2 ≤ S.hc.opening_slot m - 1 := by
  obtain ⟨hcEq, hqE, hcD⟩ := roundArith_l86f D m hm
  have hy : S.hc.opening_slot (m - 1) + S.hc.R = S.hc.opening_slot m := by
    rw [← opening_slot_succ_mk, hqE]
  have hx : S.hc.opening_slot D + 2 * S.hc.R ≤ S.hc.opening_slot m := by
    have h := opening_slot_le_of_le_mk S.hc hm
    rwa [opening_slot_add_mk] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := openingBookkeeping_l86f _ _ _ _ S.hc.R_ge_two hy hx
  exact ⟨h1, h2, h3, h4, h5, hcEq, hqE, hcD, h6⟩

end OpeningPivot


end DecoupledConsensusModel.Sts
