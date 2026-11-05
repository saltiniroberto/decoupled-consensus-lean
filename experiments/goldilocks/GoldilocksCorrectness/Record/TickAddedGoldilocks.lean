module
public import GoldilocksCorrectness.Record.TickAddedFacts
public import GoldilocksCorrectness.Record.ModelGoldilocks
public import GoldilocksCorrectness.Record.NodeInvGoldilocks
public import GoldilocksCorrectness.Record.NodeInvAddedGoldilocks
public import GoldilocksCorrectness.Proofs.Routines.Node
public import GoldilocksCorrectness.Proofs.Routines.NodeReach
public import GoldilocksCorrectness.Proofs.Routines.DREPost
import all Goldilocks.Node

@[expose] public section

/-!
# The spec's tick: the relations that read the greatest height

`tickAddedFacts_goldilocks`: the spec's model satisfies `TickAddedFacts`. The two relations are the
landed `tick_witnessedFrom` and `tick_reachFrom`, read through the tick's set of outcomes and the
equivalences of `CachesWitnessed` and `ReadyFor` at the spec's model, whose hypothesis (the stored
greatest height is `hMax`) the node invariant gives before and after the tick (`hMax_goldilocks`,
and the field `tick_nodeInv` of `nodeInvFacts_goldilocks`, which asks a time no earlier than the
clock). The justification height `S.h_j` does not decrease along the tick (`tick_h_j_le`): only
the finality update writes it, and only with a value at least the old one.
-/

set_option autoImplicit false

namespace GoldilocksCorrectness.Record

open GoldilocksCorrectness.Record.Proofs.Routines (goldilocks_CachesWitnessed goldilocks_ReadyFor)

variable {V : Type} [DecidableEq V] [Fintype V]

section

open Goldilocks
open GoldilocksCorrectness.Proofs.Routines (DREBPost DREBPost.bind DREBPost.bind_any DREBPost.ite
  DREBPost.pure on_block_eq attest_caches record_awake_frame fg_on_block_justification)

variable [RootOrder]

/-- Receiving a block never lowers the justification height `S.h_j`.

Why: a refused block changes nothing; an accepted block goes through `fg_on_block`, whose finality
update keeps `S.h_j` or raises it.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `B`: the block. -/
theorem on_block_h_j_le (C : Config) (P : Provisional V) (X : External V) (n : NodeState V)
    (B : Block V) : n.S.h_j ≤ (on_block C P X n B).S.h_j := by
  rw [on_block_eq]
  split
  · exact (fg_on_block_justification C n.S B).2.1
  · exact le_rfl

/-- Every answer of the proposal never lowers the justification height: it ends by receiving the
proposed block.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state. -/
theorem propose_block_h_j_le (C : Config) (P : Provisional V) (X : External V) (n : NodeState V) :
    DREBPost (propose_block C P X n) (fun n' => n.S.h_j ≤ n'.S.h_j) := by
  simp only [propose_block]
  repeat' first
    | exact DREBPost.pure (on_block_h_j_le C P X n _)
    | refine DREBPost.bind_any (fun _ => ?_)

/-- Every answer of the node's tick never lowers the justification height `S.h_j`: the wake
record, the clock and the tick of the available chain keep the FG state, the proposal receives its
own block, and the attestation keeps the justification height.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `t`: the time. -/
theorem tick_h_j_le (C : Config) (P : Provisional V) (X : External V) (n : NodeState V)
    (t : Time) : DREBPost (tick C P X n t) (fun n' => n.S.h_j ≤ n'.S.h_j) := by
  obtain ⟨hS, -, -, -⟩ := record_awake_frame n t
  simp only [tick]
  refine DREBPost.bind_any (fun A' => ?_)
  have hq : n.S.h_j ≤ ({ { record_awake n t with t := t } with A := A' } : NodeState V).S.h_j :=
    le_of_eq (congrArg FGState.h_j hS).symm
  refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
  · refine DREBPost.bind (P := fun n' => n.S.h_j ≤ n'.S.h_j)
      ((propose_block_h_j_le C P X _).mono (fun _ h' => le_trans hq h')) (fun n₄ h₄ => ?_)
    refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
    · exact DREBPost.bind (attest_caches C n₄) (fun _ h₅ =>
        DREBPost.pure (le_trans h₄ (le_of_eq h₅.2.2.1.symm)))
    · exact DREBPost.pure h₄
  · refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
    · exact DREBPost.bind (attest_caches C _) (fun _ h₅ =>
        DREBPost.pure (le_trans hq (le_of_eq h₅.2.2.1.symm)))
    · exact DREBPost.pure hq

end

/-- The spec's model satisfies the added facts of the tick.

Read aloud: Goldilocks' tick keeps the witnesses of its caches, finalizes along the chains it is
ready for, and never lowers its justified height. -/
theorem tickAddedFacts_goldilocks : TickAddedFacts (Model.goldilocks (V := V)) where
  tick_witnessedFrom C P X n t n' sent hm h ht := by
    have h' := (nodeInvFacts_goldilocks.tick_nodeInv C P X n t h ht n' sent hm).1
    have hw := GoldilocksCorrectness.Proofs.Routines.DREBPost.of_outcome
      (GoldilocksCorrectness.Proofs.Routines.tick_witnessedFrom C P X n t h.1.2.2.2.2.2.1) hm
    exact ⟨hw.1, fun hc =>
      (goldilocks_CachesWitnessed C n' (hMax_goldilocks h').symm).1
        (hw.2 ((goldilocks_CachesWitnessed C n (hMax_goldilocks h).symm).2 hc))⟩
  tick_reachFrom C P X D n t n' sent hm h := by
    have hr := GoldilocksCorrectness.Proofs.Routines.DREBPost.of_outcome
      (GoldilocksCorrectness.Proofs.Routines.tick_reachFrom C P X D n t) hm
    exact ⟨hr.1, hr.2.1, fun h1 h2 h3 =>
      hr.2.2 h1 h2 ((goldilocks_ReadyFor C D n h.1.2.2.2.2.2.1 (hMax_goldilocks h).symm).2 h3)⟩
  tick_justifiedHeight_mono C P X n t n' sent hm _ _ :=
    GoldilocksCorrectness.Proofs.Routines.DREBPost.of_outcome (tick_h_j_le C P X n t) hm
  tick_justifiedHeight_mono_of_core C P X n t n' sent hm _ :=
    GoldilocksCorrectness.Proofs.Routines.DREBPost.of_outcome (tick_h_j_le C P X n t) hm

end GoldilocksCorrectness.Record
