module

public import Model.Vocabulary.Protocol.Grades
public import Proofs.Claims.ModelIrreducible

@[expose] public section

/-!
# Clean raw tokens

An introduction and an elimination rule for `Protocol.CleanFrom raw k`, the proposition that no two
raw tokens of one round, from round `k` on, carry different keys.
-/

-- The definitions this file unfolds, made locally semireducible.
set_option allowUnsafeReducibility true in
attribute [local semireducible] DecoupledConsensusModel.Protocol.CleanFrom

set_option autoImplicit false


namespace DecoupledConsensusModel.Sts

variable {Key : Type*}

/-- If any two tokens of `raw` of the same round, at least `k`, carry the same key, then `raw` is
    clean from round `k` on. -/
theorem cleanFrom_intro {raw : Finset (Protocol.Token Key)} {k : Nat}
    (h : ∀ x ∈ raw, ∀ y ∈ raw, k ≤ x.round → x.round = y.round → x.key = y.key) :
    Protocol.CleanFrom raw k := by
  unfold Protocol.CleanFrom
  exact h

/-- If `raw` is clean from round `k` on, then two of its tokens `x` and `y` of the same round, at
    least `k`, carry the same key. -/
theorem key_eq_of_cleanFrom {raw : Finset (Protocol.Token Key)} {k : Nat}
    (h : Protocol.CleanFrom raw k) (x : Protocol.Token Key) (hx : x ∈ raw)
    (y : Protocol.Token Key) (hy : y ∈ raw) (hkx : k ≤ x.round) (hxy : x.round = y.round) :
    x.key = y.key := by
  unfold Protocol.CleanFrom at h
  exact h x hx y hy hkx hxy

end DecoupledConsensusModel.Sts
