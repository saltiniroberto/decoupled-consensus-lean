module
public import Model.Vocabulary.Protocol.Grades
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# Facts about `Protocol.HealConfig.opening_slot`, as a module file

Lemmas that unfold a round's opening slot, for module files.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.HealConfig.opening_slot

set_option autoImplicit false


namespace DecoupledConsensusModel.Sts

/-- The opening slot of round `0` is slot `0`. -/
theorem opening_slot_zero_mk (hc : Protocol.HealConfig) : hc.opening_slot 0 = 0 :=
  Nat.zero_mul hc.R

/-- If `r ≤ r'`, the opening slot of round `r` is at most that of round `r'`. -/
theorem opening_slot_le_of_le_mk (hc : Protocol.HealConfig) {r r' : Round} (h : r ≤ r') :
    hc.opening_slot r ≤ hc.opening_slot r' :=
  Nat.mul_le_mul_right _ h

/-- The opening slot of round `r + 1` is the opening slot of round `r` plus `R`. -/
theorem opening_slot_succ_mk (hc : Protocol.HealConfig) (r : Round) :
    hc.opening_slot (r + 1) = hc.opening_slot r + hc.R :=
  Nat.succ_mul r hc.R

/-- The opening slot of round `r + k` is the opening slot of round `r` plus `k * R`. -/
theorem opening_slot_add_mk (hc : Protocol.HealConfig) (r k : Round) :
    hc.opening_slot (r + k) = hc.opening_slot r + k * hc.R :=
  Nat.add_mul r k hc.R

end DecoupledConsensusModel.Sts
