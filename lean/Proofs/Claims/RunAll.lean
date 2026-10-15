module
public import Proofs.Claims.Projection
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar

@[expose] public section

/-!
# One run carrying every validator's events

`runAll` is the run made of the events every validator contributes over the first `n` steps of an
sts execution, with `v` alone honest; `stepEvents` and `runEvents` build its event list. The file
also states which objects a delivery re-sends.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The event list of the whole run -/

/-- The events every validator contributes at the sts step `k`, one validator after another in the
    order of `Finset.univ.toList`. -/
noncomputable def stepEvents (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (k : Nat) : List (NamedEvent V) :=
  (Finset.univ : Finset V).toList.flatMap
    (fun v₀ => actionEvents S Sched v₀ (x[k].time : Int) (x.lbl k))

/-- The events of every validator over the first `n` steps of the sts execution `x`, in step order. -/
noncomputable def runEvents (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) : Nat → List (NamedEvent V)
  | 0 => []
  | n + 1 => runEvents S Sched x n ++ stepEvents S Sched x n

/-- The run made of every validator's events over the first `n` sts steps, in which `v` alone is
    honest. -/
noncomputable def runAll (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (v : V) (n : Nat) : NamedRun V :=
  { honest := {v}
    horizon := (x[n].time : Int)
    events := runEvents S Sched x n }

/-- The objects re-sent on the delivery of `m` are `m` itself and the objects `m` carries. -/
theorem mem_relayedObjects_iff (m o : NamedObject V) :
    o ∈ relayedObjects m ↔ o = m ∨ carries m o := by
  cases m with
  | block B =>
      simp only [relayedObjects, carries, Multiset.mem_add, Multiset.mem_singleton,
        Multiset.mem_coe, List.mem_map]
      constructor
      · rintro ((h | ⟨u, hu, rfl⟩) | ⟨a, ha, rfl⟩)
        · exact Or.inl h
        · exact Or.inr (Or.inl ⟨u, hu, rfl⟩)
        · exact Or.inr (Or.inr ⟨a, ha, rfl⟩)
      · rintro (h | ⟨u, hu, rfl⟩ | ⟨a, ha, rfl⟩)
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr ⟨u, hu, rfl⟩)
        · exact Or.inr ⟨a, ha, rfl⟩
  | gfVote u => simp [relayedObjects, carries]
  | attest a => simp [relayedObjects, carries]

end DecoupledConsensusModel.Sts
