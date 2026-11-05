module
public import GoldilocksCorrectness.Record.NodeInvFacts
public import GoldilocksCorrectness.Proofs.Routines.Node
public import GoldilocksCorrectness.Proofs.Routines.NodeTick
public import GoldilocksCorrectness.Proofs.Routines.Wiring
public import GoldilocksCorrectness.Proofs.Routines.NodeCore
public import GoldilocksCorrectness.Proofs.Routines.HeightCacheAttained

@[expose] public section

/-!
# The spec's node-invariant facts

`nodeInvFacts_goldilocks`: the spec's model satisfies `NodeInvFacts`, its node invariant being the
library's `NodeInv` together with `HeightCacheAttained` of the node's FG state. The five structural
fields are the library's theorems about `NodeInv` and about `HeightCacheAttained`
(`Proofs/Routines/HeightCacheAttained.lean`), the tick's read through its set of outcomes; the
tick's outcome and its failures read `NodeInv` alone. Each consequence field projects one clause
of `NodeInv`, the first conjunct; the three whose condition reads a chain state
(`AttestationsValid`, `JustificationCacheBounds`, `JustifiedHeight`) pass the clause through its
equivalence at the spec's model, whose hypotheses are other clauses of `NodeInv`: the node's chain
states of its tree are the blocks' own, the parents of the tree's blocks are in the tree, and the
justified block is in the tree. The clause `RecordConsistent` passes through its equation at the
spec's model, the two structures having the same fields.
-/

set_option autoImplicit false

namespace GoldilocksCorrectness.Record

open GoldilocksCorrectness.Record.Statements.Routines (goldilocks_AttestationsValid
  goldilocks_JustificationCacheBounds goldilocks_JustifiedHeight goldilocks_RecordConsistent)

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The spec's model satisfies the node-invariant facts.

Read aloud: Goldilocks' node invariant satisfies every fact the record asks of a model's. -/
theorem nodeInvFacts_goldilocks : NodeInvFacts (Model.goldilocks (V := V)) where
  initial_nodeInv C P X v :=
    ⟨GoldilocksCorrectness.Proofs.Routines.initial_nodeInv C P X v,
      GoldilocksCorrectness.Proofs.Routines.initial_heightCacheAttained C v⟩
  tick_nodeInv C P X n t h ht _ _ hm := by
    have h₁ := GoldilocksCorrectness.Proofs.Routines.DREBPost.of_outcome
      (GoldilocksCorrectness.Proofs.Routines.tick_nodeInv C P X n t h.1 ht) hm
    have h₂ := GoldilocksCorrectness.Proofs.Routines.DREBPost.of_outcome
      (GoldilocksCorrectness.Proofs.Routines.tick_heightCacheAttained C P X n t h.2) hm
    exact ⟨⟨h₁.1, h₂⟩, h₁.2⟩
  wake_nodeInv C P X n t h ht :=
    have h₁ := GoldilocksCorrectness.Proofs.Routines.wake_nodeInv C P X n t h.1 ht
    ⟨⟨h₁.1, GoldilocksCorrectness.Proofs.Routines.wake_heightCacheAttained n t h.2⟩, h₁.2⟩
  receive_nodeInv C P X n o h :=
    have h₁ := GoldilocksCorrectness.Proofs.Routines.receive_nodeInv C P X n o h.1
    ⟨⟨h₁.1, GoldilocksCorrectness.Proofs.Routines.receive_heightCacheAttained C P X n o h.2⟩, h₁.2⟩
  tick_ok C P X n t h ht := by
    obtain ⟨r, hr⟩ := GoldilocksCorrectness.Proofs.Routines.tick_ok C P X n t h.1 ht []
    refine ⟨⟨_, Goldilocks.DREB.run_mem_outcomes (Goldilocks.tick C P X n t)⟩, fun e he => ?_⟩
    have h' := Goldilocks.DREB.run_eq_of_mem_outcomes (d := Goldilocks.tick C P X n t) he
    rw [hr] at h'
    cases h'
  nodeInv_core := fun ⟨h, hc⟩ => ⟨GoldilocksCorrectness.Proofs.Routines.NodeInv.core h, hc⟩
  tick_nodeInvCore C P X n t h _ _ hm := by
    have h₁ := GoldilocksCorrectness.Proofs.Routines.DREBPost.of_outcome
      (GoldilocksCorrectness.Proofs.Routines.tick_nodeInvCore C P X n t h.1) hm
    have h₂ := GoldilocksCorrectness.Proofs.Routines.DREBPost.of_outcome
      (GoldilocksCorrectness.Proofs.Routines.tick_heightCacheAttained C P X n t h.2) hm
    exact ⟨⟨h₁.1, h₂⟩, h₁.2⟩
  wake_nodeInvCore C P X n t h :=
    have h₁ := GoldilocksCorrectness.Proofs.Routines.wake_nodeInvCore C P X n t h.1
    ⟨⟨h₁.1, GoldilocksCorrectness.Proofs.Routines.wake_heightCacheAttained n t h.2⟩, h₁.2⟩
  receive_nodeInvCore C P X n o h :=
    have h₁ := GoldilocksCorrectness.Proofs.Routines.receive_nodeInvCore C P X n o h.1
    ⟨⟨h₁.1, GoldilocksCorrectness.Proofs.Routines.receive_heightCacheAttained C P X n o h.2⟩, h₁.2⟩
  nodeInvCore_treeClosed := fun ⟨h, _⟩ => h.2.2.1
  nodeInvCore_poolKeyed := fun ⟨h, _⟩ => h.1
  nodeInvCore_treeStamped := fun ⟨h, _⟩ => h.2.2.2.2.1
  nodeInvCore_rootsNameBlocksIn := fun ⟨h, _⟩ => h.2.2.2.2.2.2.2.1.1
  nodeInvCore_finalizedAncestorJustified := fun ⟨h, _⟩ => h.2.2.2.2.2.2.2.1.2.1.1
  nodeInvCore_justificationCacheBounds := fun ⟨h, _⟩ =>
    (goldilocks_JustificationCacheBounds _ _ h.2.2.2.2.2.1).1 h.2.2.2.2.2.2.2.1.2.2.1
  nodeInvCore_justifiedHeight := fun ⟨h, _⟩ =>
    (goldilocks_JustifiedHeight _ _ h.2.2.2.2.2.1 h.2.2.2.2.2.2.2.1.2.2.2.2.1).1
      h.2.2.2.2.2.2.2.1.2.2.2.1
  nodeInvCore_justifiedInTree := fun ⟨h, _⟩ => h.2.2.2.2.2.2.2.1.2.2.2.2.1
  nodeInvCore_lockBelowJustified := fun ⟨h, _⟩ => h.2.2.2.2.2.2.2.1.2.2.2.2.2.1
  nodeInvCore_recordConsistent := fun ⟨h, _⟩ =>
    Eq.mp (goldilocks_RecordConsistent _) h.2.2.2.2.2.2.2.1.2.2.2.2.2.2
  nodeInv_poolKeyed := fun ⟨h, _⟩ => h.1
  nodeInv_poolStamped := fun ⟨h, _⟩ => h.2.1
  nodeInv_treeClosed := fun ⟨h, _⟩ => h.2.2.1
  nodeInv_finalized_mem_tree := fun ⟨h, _⟩ => h.2.2.2.1
  nodeInv_treeStamped := fun ⟨h, _⟩ => h.2.2.2.2.1
  nodeInv_attestationsValid := fun ⟨h, _⟩ =>
    (goldilocks_AttestationsValid _ _ h.2.2.2.2.2.1 (fun B hB hg => (h.2.2.1.2 B hB hg).1)).1
      h.2.2.2.2.2.2.1
  nodeInv_stampOrder := fun ⟨h, _⟩ => h.2.2.2.2.2.2.2.2.1
  nodeInv_rootsNameBlocksIn := fun ⟨h, _⟩ => h.2.2.2.2.2.2.2.2.2.1.1
  nodeInv_finalizedAncestorJustified := fun ⟨h, _⟩ => h.2.2.2.2.2.2.2.2.2.1.2.1.1
  nodeInv_justificationCacheBounds := fun ⟨h, _⟩ =>
    (goldilocks_JustificationCacheBounds _ _ h.2.2.2.2.2.1).1
      h.2.2.2.2.2.2.2.2.2.1.2.2.1
  nodeInv_justifiedHeight := fun ⟨h, _⟩ =>
    (goldilocks_JustifiedHeight _ _ h.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.1.2.2.2.2.1).1
      h.2.2.2.2.2.2.2.2.2.1.2.2.2.1
  nodeInv_justifiedInTree := fun ⟨h, _⟩ => h.2.2.2.2.2.2.2.2.2.1.2.2.2.2.1
  nodeInv_lockBelowJustified := fun ⟨h, _⟩ => h.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.1
  nodeInv_recordConsistent := fun ⟨h, _⟩ =>
    Eq.mp (goldilocks_RecordConsistent _) h.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2
  nodeInv_poolAttestationsWellFormed := fun ⟨h, _⟩ => h.2.2.2.2.2.2.2.2.2.2

end GoldilocksCorrectness.Record
