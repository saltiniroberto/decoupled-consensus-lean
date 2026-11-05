module
public import StsMultisetLog.Spec.Schedule
public import StsRefinement.TimeMap

@[expose] public section

/-!
# The schedule read through a time map

A refined tick at `T` runs the tick of every validator awake and honest at `T`, from one
snapshot. The refining execution must have the same validators acting, and a delivery at any
refining time `t` must be enabled at the refined time `τ t`. So the refining schedule is the
refined schedule read through `τ` (`ScheduleOver`): validators wake, sleep and are corrupted only
at refining times that move refined time.
-/

set_option autoImplicit false

namespace StsRefinement

open Framework.StsMultisetLog

variable {Node : Type}

/-- **The schedule read through `τ`.** `ScheduleOver τ S₁ S₂`: at every time `t`, the refining
schedule `S₁` has the awake set and the adversary set the refined schedule `S₂` has at `τ t`; at
negative times the two agree. Read aloud: the refining schedule is the refined schedule seen on
the refining clock, so it changes only where refined time moves. -/
def ScheduleOver (τ : TimeMap) (S₁ S₂ : Schedule Node) : Prop :=
  (∀ t : ℕ, S₁.awake (t : Int) = S₂.awake ((τ t : ℕ) : Int) ∧
    S₁.adv (t : Int) = S₂.adv ((τ t : ℕ) : Int)) ∧
  ∀ z : Int, z < 0 → S₁.awake z = S₂.awake z ∧ S₁.adv z = S₂.adv z

/-- Honesty through a time reads through `τ`: `v` is outside `S₁`'s adversary set at every time
up to `t` exactly when it is outside `S₂`'s at every time up to `τ t`. -/
theorem honestThrough_over {τ : TimeMap} {S₁ S₂ : Schedule Node} (hS : ScheduleOver τ S₁ S₂)
    (t : ℕ) (v : Node) :
    (∀ z : Int, z ≤ (t : Int) → v ∉ S₁.adv z) ↔ (∀ z : Int, z ≤ ((τ t : ℕ) : Int) → v ∉ S₂.adv z) := by
  constructor
  · intro h z hz
    rcases lt_or_ge z 0 with hneg | hnn
    · rw [← (hS.2 z hneg).2]; exact h z (by omega)
    · obtain ⟨t', ht', he⟩ := τ.exists_eq_of_le t z.toNat (by omega)
      have := h (t' : Int) (by omega)
      rw [(hS.1 t').2, he] at this
      rwa [Int.toNat_of_nonneg hnn] at this
  · intro h z hz
    rcases lt_or_ge z 0 with hneg | hnn
    · rw [(hS.2 z hneg).2]; exact h z (by omega)
    · have hz' : z = ((z.toNat : ℕ) : Int) := (Int.toNat_of_nonneg hnn).symm
      rw [hz', (hS.1 z.toNat).2]
      exact h _ (by have := τ.mono (show z.toNat ≤ t by omega); omega)

/-- Awake throughout `[t, t']` is awake at each time of it. -/
theorem mem_awakeThroughout_iff' [Fintype Node] [DecidableEq Node] {Sch : Schedule Node}
    {t t' : Int} {v : Node} :
    v ∈ Sch.awakeThroughout t t' ↔ ∀ t'' : Int, t ≤ t'' → t'' ≤ t' → v ∈ Sch.awake t'' := by
  classical
  unfold Schedule.awakeThroughout
  constructor
  · intro h t'' h1 h2
    exact Finset.mem_of_subset (Finset.inf_le (Finset.mem_Icc.2 ⟨h1, h2⟩)) h
  · intro h
    refine Finset.singleton_subset_iff.1 (Finset.le_inf ?_)
    intro t'' ht''
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 ht''
    exact Finset.singleton_subset_iff.2 (h t'' h1 h2)

end StsRefinement
