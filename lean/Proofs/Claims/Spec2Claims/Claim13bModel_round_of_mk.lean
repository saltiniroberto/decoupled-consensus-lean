module
public import Model.Vocabulary.Protocol.Grades
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# Facts about `Protocol.HealConfig.round_of`, as a module file

The round a slot belongs to is monotone in the slot.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.HealConfig.round_of

set_option autoImplicit false


namespace DecoupledConsensusModel.Sts

/-- If `s_0 ≤ s_1`, the round of `s_0` is at most the round of `s_1`. -/
theorem round_of_mono_sts (hc : Protocol.HealConfig) {s_0 s_1 : Slot} (h : s_0 ≤ s_1) :
    hc.round_of s_0 ≤ hc.round_of s_1 :=
  Nat.div_le_div_right h

end DecoupledConsensusModel.Sts
