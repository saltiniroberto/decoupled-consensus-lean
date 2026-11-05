module
public import GoldilocksCorrectness.Proofs.Routines.Lemma19
import all Goldilocks.Config
import all Goldilocks.FG.State
import all Goldilocks.Node

@[expose] public section

/-!
# What the node routines keep of the blocks a tree reaches

`on_block_reachFrom`, `propose_block_reachFrom`, `tick_reachFrom`: the handlers keep the relation
`ReachFrom`; `tick_block_unique`: two blocks the tick of one node state at one time sends are one
block, the block its proposal builds.

They read the node routines and node states alone: no execution.

Moved here unchanged from the execution pages.
-/

set_option autoImplicit false

open scoped DC
open DC (DRE)

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks

-- An index `x[i]` into an execution has the valid-index predicate `fun _ _ => True`; this rule,
-- local to the file, proves it at once.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- Receiving a block relates the node state to the result. -/
theorem on_block_reachFrom (C : Config) (P : Provisional V) (X : External V) (D : Block V)
    (n : NodeState V) (B : Block V) : ReachFrom C D n (on_block C P X n B) := by
  rw [on_block_eq]
  by_cases hb : block_admissible C P X n B = true
  swap
  · rw [if_neg hb]
    exact reachFrom_of_frame C D rfl rfl
  rw [if_pos hb]
  obtain ⟨-, -, hpar, hFB, -, hslot, -⟩ := block_admissible_facts C P X n B hb
  obtain ⟨hT', -, -⟩ := fg_on_block_eq C n.S B
  refine ⟨?_, fg_on_block_F C n.S B, fun hDn hDn' hR => ?_⟩
  · show n.S.T ⊆ (fg_on_block C n.S B).T
    rw [hT']
    exact Finset.subset_union_left
  · have hDn'' : D ∈ (fg_on_block C n.S B).T := hDn'
    rw [hT'] at hDn''
    have hDB : D = B := by
      rcases Finset.mem_union.1 hDn'' with h | h
      · exact absurd h hDn
      · exact Finset.mem_singleton.1 h
    subst hDB
    have hDg : D ≠ Block.genesis := by
      intro h
      subst h
      simp only [Block.parent, Block.slot] at hslot
      exact absurd hslot (lt_irrefl _)
    exact fg_on_block_F_reaches C n.S D hR hDn hpar hFB hDg

/-- Every answer of the proposal relates the node state to the answer. -/
theorem propose_block_reachFrom (C : Config) (P : Provisional V) (X : External V) (D : Block V)
    (n : NodeState V) :
    DREBPost (propose_block C P X n) (fun n' => ReachFrom C D n n') := by
  simp only [propose_block]
  repeat' first
    | exact DREBPost.pure (on_block_reachFrom C P X D n _)
    | refine DREBPost.bind_any (fun _ => ?_)

/-- Every answer of the node's tick relates the node state to the answer. -/
theorem tick_reachFrom (C : Config) (P : Provisional V) (X : External V) (D : Block V)
    (n : NodeState V) (t : Time) :
    DREBPost (tick C P X n t) (fun n' => ReachFrom C D n n') := by
  obtain ⟨hS, -, -, -⟩ := record_awake_frame n t
  simp only [tick]
  refine DREBPost.bind_any (fun A' => ?_)
  have hq : ReachFrom C D n { { record_awake n t with t := t } with A := A' } :=
    reachFrom_of_frame C D (congrArg FGState.T hS) (congrArg FGState.F hS)
  have hS₁ : ({ { record_awake n t with t := t } with A := A' } : NodeState V).S = n.S := hS
  refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
  · refine DREBPost.bind (P := fun n' => ReachFrom C D n n')
      ((propose_block_reachFrom C P X D _).mono
        (fun _ h' => reachFrom_frame_trans C D hS₁ h')) (fun n₄ h₄ => ?_)
    refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
    · exact DREBPost.bind (attest_caches C n₄) (fun _ h₅ =>
        DREBPost.pure (reachFrom_trans_frame C D h₄ h₅.1 h₅.2.2.2))
    · exact DREBPost.pure h₄
  · refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
    · exact DREBPost.bind (attest_caches C _) (fun _ h₅ =>
        DREBPost.pure (reachFrom_trans_frame C D hq h₅.1 h₅.2.2.2))
    · exact DREBPost.pure hq

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- Two blocks the tick of one node state at one time sends are one block: both are the block
its proposal builds.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `t`: the time;
- `n'`, `sent`: the tick's answer; `B`, `B'`: the two blocks. -/
theorem tick_block_unique (C : Config) (P : Provisional V) (X : External V) (n n' : NodeState V)
    (t : Time) (sent : List (NamedObject V)) (B B' : Block V)
    (hRun : .ok (n', sent) ∈ (tick C P X n t).outcomes)
    (hB : NamedObject.block B ∈ sent) (hB' : NamedObject.block B' ∈ sent) : B = B' := by
  have hL := (GoldilocksCorrectness.Proofs.Routines.tick_block C P X n t).of_outcome hRun
  obtain ⟨-, -, -, pr, hpr, hBeq⟩ := hL B hB
  obtain ⟨-, -, -, pr', hpr', hBeq'⟩ := hL B' hB'
  have hpp : pr = pr' := by
    rw [hpr] at hpr'
    exact Except.ok.inj hpr'
  rw [hBeq, hBeq', hpp]

end

end GoldilocksCorrectness.Proofs.Routines
