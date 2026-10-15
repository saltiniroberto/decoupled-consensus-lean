module
public import Model.Vocabulary.Protocol.ForkChoice.Goldfish
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# Facts about `Protocol.latest_window`

Lemmas that unfold `Protocol.latest_window`, the list of the rounds from `r − η` to `r − 1` a
round-`r` grade reads.
-/

set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.latest_window

set_option autoImplicit false


namespace DecoupledConsensusModel.Sts

/-- A round in `latest_window eta r` is at least `r − eta`. -/
theorem mem_latest_window_ge {eta r k : Round} (hk : k ∈ Protocol.latest_window eta r) :
    r - eta ≤ k := by
  simp only [Protocol.latest_window] at hk
  exact (List.mem_range'_1.mp hk).1

/-- A round in `latest_window eta r` is strictly less than `r`. -/
theorem mem_latest_window_lt {eta r k : Round} (hk : k ∈ Protocol.latest_window eta r) :
    k < r := by
  simp only [Protocol.latest_window] at hk
  obtain ⟨_, h2⟩ := List.mem_range'_1.mp hk
  exact Nat.lt_of_lt_of_le h2 (Nat.sub_add_min_cancel r eta).le

end DecoupledConsensusModel.Sts
