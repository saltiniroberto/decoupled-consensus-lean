module
public import GoldilocksCorrectness.Proofs.Routines.ACInterface
public import GoldilocksCorrectness.Proofs.Routines.ConfirmedTip
public import GoldilocksCorrectness.Proofs.Routines.FGState
public import GoldilocksCorrectness.Proofs.Routines.Sends
public import GoldilocksCorrectness.Statements.Routines.NodeDefs
public import GoldilocksCorrectness.Statements.Routines.NodeCoreDefs
public import GoldilocksCorrectness.Proofs.Routines.PoolInv
import all Goldilocks.AC.Interface
import all Goldilocks.AC.State
import all Goldilocks.Config
import all Goldilocks.FG.ChainState
import all Goldilocks.FG.State
import all Goldilocks.FG.ValidatorClient
import all Goldilocks.Node
import all GoldilocksCorrectness.Statements.Routines.ScheduleDefs

@[expose] public section

/-!
# What each node routine does to a node state

The relations between two node states that the node routines keep, with their `refl`, `trans` and
`of_frame` lemmas: `StampsAt`, `StepFrom` (the clock and the stamps), `TreeGrows`, `AttPoolGrows`,
`ChainsInPool` (the block tree and the pools), `NewObjectsIn` (what a step adds), `FinalizedFrom`,
`JustifiedFrom`, `CachesFrom`, `ReachFrom`, `WitnessedFrom` (the FG state's caches),
`RecordFromSent` (the signing record); and, for each node routine `on_block`, `on_attestation`,
`on_ac_message`, `attest`, `propose_block`, `record_awake`, `wake`, `tick` and the state `initial`,
what it keeps of those relations and of the node invariant `NodeInv` (Lemma 11's routine cases:
`on_block_nodeInv`, …, `tick_nodeInv`), what it adds to the trees and the pools, what it stamps,
and how it moves the stored `awakeSince`.

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
variable {V : Type} [DecidableEq V] [Fintype V]

section

variable [RootOrder]

omit [Fintype V] [RootOrder] in
/-- `block_admissible` answers true when each of its eight tests passes: the block is well
formed; its slot is at most the slot of the node's clock; no block of the tree has its root; the
tree holds its parent; the finalized block is an ancestor of it or it; its proposer is its slot's;
its parent's slot is earlier; every attestation it includes is valid against its parent's chain
state.

The variables:
- `C`, `P`, `X`: the parameters, the given values, the digest; `n`: the node state; `B`: the
  block. -/
theorem block_admissible_of (C : Config) (P : Provisional V) (X : External V) (n : NodeState V)
    (B : Block V)
    -- `B` is well formed
    (hwf : block_well_formed P X B = true)
    -- `B`'s slot is not later than the slot of the node's clock
    (hslot : B.slot ≤ C.slot n.t)
    -- no block of the tree has `B`'s root
    (hroot : ∀ B' ∈ n.S.T, B'.root ≠ B.root)
    -- the tree holds `B`'s parent
    (hpar : B.parent ∈ n.S.T)
    -- the finalized block is an ancestor of `B`, or `B`
    (hF : n.S.F.AncestorEq B)
    -- `B`'s proposer is its slot's
    (hprop : B.proposer? = some (P.proposer B.slot))
    -- `B`'s parent's slot is earlier than `B`'s
    (hps : B.parent.slot < B.slot)
    -- every attestation of `B` is valid against the parent's chain state
    (hatt : ∀ a ∈ B.attestations, valid_attestation (n.S.σ B.parent) a = true) :
    block_admissible C P X n B = true := by
  have h3 : ¬ ∃ B' ∈ n.S.T, B'.root = B.root := fun ⟨B', h1, h2⟩ => hroot B' h1 h2
  have h5 : n.S.F.ancestorEq B = true := hF
  simp only [block_admissible, Id.run]
  repeat' split
  all_goals first
    | rfl
    | (exfalso
       rename_i h
       first
         | (simp [hwf] at h; done)
         | exact Nat.not_lt.mpr hslot h
         | exact h3 h
         | exact h hpar
         | (simp [h5] at h; done)
         | exact h hprop
         | (simp [hps] at h; done)
         | (obtain ⟨a, ha, h⟩ := h; simp [fun_getElem, hatt a ha] at h))

end

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]

/-- `StampsAt n n'`: every block of `n'`'s tree that is not in `n`'s tree, and every Goldfish vote
`n'` holds under a slot that `n` does not hold under that slot, is stamped `n'.t` in `n'`.

The variables:
- `n`, `n'`: the two node states.

Read aloud: what `n'` holds beyond `n` is stamped with `n'`'s clock. -/
def StampsAt (n n' : NodeState V) : Prop :=
  (∀ B ∈ n'.S.T, B ∉ n.S.T → n'.A.timestamp_block B = some (n'.t : Stamp)) ∧
    ACStampsAt n.A n'.A n'.t

omit [DecidableEq V] [Fintype V] in
/-- A node state holds nothing beyond itself. -/
theorem StampsAt.refl (n : NodeState V) : StampsAt n n :=
  ⟨fun _ hB hn => absurd hB hn, ACStampsAt.refl n.A n.t⟩

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- Receiving an attestation keeps the tree, the AC state and the clock.

The variables:
- `n`: the node state; `a`: the attestation. -/
theorem on_attestation_frame (n : NodeState V) (a : Attestation V) :
    (on_attestation n a).S.T = n.S.T ∧ (on_attestation n a).A = n.A ∧
      (on_attestation n a).t = n.t := by
  simp only [on_attestation, Id.run]
  split
  · exact ⟨rfl, rfl, rfl⟩
  · exact ⟨(fg_on_attestation_keeps n.S a).1, rfl, rfl⟩

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]

section

variable [RootOrder]

omit [DecidableEq V] [Fintype V] [RootOrder] in
/-- `StampsAt` reads only the FG state and the AC state of the node state it starts from. -/
theorem StampsAt.congr_left {n₀ n n' : NodeState V} (hS : n₀.S = n.S) (hA : n₀.A = n.A)
    (h : StampsAt n₀ n') : StampsAt n n' := by
  unfold StampsAt at h ⊢
  rw [← hS, ← hA]
  exact h

end

end

section

open GoldilocksCorrectness.Statements.Routines (chainStateOf)

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- `FinalizedFrom C n n'`: `n'`'s tree holds `n`'s, and `n'`'s finalized block is `n`'s or the
finalized block of the chain state of a block of `n'`'s tree.

The variables:
- `C`: the parameters; `n`, `n'`: the two node states.

Read aloud: `n'` holds `n`'s tree, and its finalized block is `n`'s or comes from a chain it
holds. -/
def FinalizedFrom (C : Config) (n n' : NodeState V) : Prop :=
  n.S.T ⊆ n'.S.T ∧
    (n'.S.F = n.S.F ∨ ∃ B ∈ n'.S.T, n'.S.F = (chainStateOf C B).F)

omit [RootOrder] in
/-- A node state is related to itself. -/
theorem finalizedFrom_refl (C : Config) (n : NodeState V) : FinalizedFrom C n n :=
  ⟨Finset.Subset.refl _, Or.inl rfl⟩

omit [RootOrder] in
/-- `FinalizedFrom` is transitive. -/
theorem finalizedFrom_trans (C : Config) {n n' n'' : NodeState V} (h : FinalizedFrom C n n')
    (h' : FinalizedFrom C n' n'') : FinalizedFrom C n n'' := by
  obtain ⟨hT, hF⟩ := h
  obtain ⟨hT', hF'⟩ := h'
  refine ⟨hT.trans hT', ?_⟩
  rcases hF' with hF' | ⟨B, hB, hBF⟩
  · rcases hF with hF | ⟨B, hB, hBF⟩
    · exact Or.inl (hF'.trans hF)
    · exact Or.inr ⟨B, hT' hB, hF'.trans hBF⟩
  · exact Or.inr ⟨B, hB, hBF⟩

omit [RootOrder] in
/-- A routine that keeps the tree and the finalized block relates its input to its output.

The variables:
- `C`: the parameters; `n`, `n'`: the input and the output. -/
theorem finalizedFrom_of_frame (C : Config) {n n' : NodeState V} (hT : n'.S.T = n.S.T)
    (hF : n'.S.F = n.S.F) : FinalizedFrom C n n' :=
  ⟨by rw [hT], Or.inl hF⟩

end

end

section

open GoldilocksCorrectness.Statements.Routines (chainStateOf)
open GoldilocksCorrectness.Statements.Routines (ChainStatesComputed)

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

omit [Fintype V] [RootOrder] in
/-- Receiving an attestation keeps the tree and the finalized block.

The variables:
- `n`: the node state; `a`: the attestation. -/
theorem on_attestation_frame_S (n : NodeState V) (a : Attestation V) :
    (on_attestation n a).S.T = n.S.T ∧ (on_attestation n a).S.F = n.S.F := by
  simp only [on_attestation, Id.run]
  split
  · exact ⟨rfl, rfl⟩
  · exact ⟨(fg_on_attestation_keeps n.S a).1, (fg_on_attestation_keeps n.S a).2.2⟩

/-- Every answer of the attestation duty keeps the tree and the finalized block: it writes the
anti-slashing record, and may receive its own attestation.

The variables:
- `C`: the parameters; `n`: the node state. -/
theorem attest_frame_S (C : Config) (n : NodeState V) :
    DREBPost (attest C n) (fun n' => n'.S.T = n.S.T ∧ n'.S.F = n.S.F) := by
  simp only [attest]
  repeat' first
    | exact DREBPost.pure ⟨rfl, rfl⟩
    | exact DREBPost.pure (on_attestation_frame_S _ _)
    | refine DREBPost.dite (fun _ => ?_) (fun _ => ?_)
    | refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
    | refine DREBPost.bind_any (fun _ => ?_)

end

end

section

open GoldilocksCorrectness.Statements.Routines (FinalizedFromChain)

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

omit [RootOrder] in
/-- The initial node state satisfies `FinalizedFromChain`: its finalized block is the genesis
block, the finalized block of the genesis block's chain state.

The variables:
- `C`: the parameters; `v`: the validator. -/
theorem initial_finalizedFromChain (C : Config) (v : V) :
    FinalizedFromChain C (initial C v).S :=
  ⟨Block.genesis, Finset.mem_singleton_self _, rfl⟩

end

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- `ChainsInPool n`: every attestation included in a block of `n`'s tree, or in one of its
ancestors, is in `n`'s pool.

The variables:
- `n`: the node state.

Read aloud: what the validator's chains include, its pool holds. -/
def ChainsInPool (n : NodeState V) : Prop :=
  ∀ Y ∈ n.S.T, ∀ a : Attestation V, on_chain a Y = true → a ∈ n.S.attestations

end

section

open GoldilocksCorrectness.Statements.Routines (chainStateOf)

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- `JustifiedFrom C n n'`: `n'`'s justified block is `n`'s, or the justified block of the chain
state `chainStateOf C D` of some block `D`.

The variables:
- `C`: the parameters; `n`, `n'`: the two node states.

Read aloud: `n'`'s justified block is `n`'s or comes from a chain. -/
def JustifiedFrom (C : Config) (n n' : NodeState V) : Prop :=
  n'.S.J = n.S.J ∨ ∃ D : Block V, n'.S.J = (chainStateOf C D).J

omit [RootOrder] in
/-- A node state is related to itself. -/
theorem justifiedFrom_refl (C : Config) (n : NodeState V) : JustifiedFrom C n n :=
  Or.inl rfl

omit [RootOrder] in
/-- `JustifiedFrom` is transitive. -/
theorem justifiedFrom_trans (C : Config) {n n' n'' : NodeState V} (h : JustifiedFrom C n n')
    (h' : JustifiedFrom C n' n'') : JustifiedFrom C n n'' := by
  rcases h' with h' | h'
  · rcases h with h | h
    · exact Or.inl (h'.trans h)
    · obtain ⟨D, hD⟩ := h
      exact Or.inr ⟨D, h'.trans hD⟩
  · exact Or.inr h'

omit [RootOrder] in
/-- A routine that keeps the justified block relates its input to its output.

The variables:
- `C`: the parameters; `n`, `n'`: the input and the output. -/
theorem justifiedFrom_of_frame (C : Config) {n n' : NodeState V} (hJ : n'.S.J = n.S.J) :
    JustifiedFrom C n n' :=
  Or.inl hJ

end

end

section

open GoldilocksCorrectness.Statements.Routines (chainStateOf)
open GoldilocksCorrectness.Statements.Routines (ChainStatesComputed)

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

omit [Fintype V] [RootOrder] in
/-- Receiving an attestation keeps the justified block.

The variables:
- `n`: the node state; `a`: the attestation. -/
theorem on_attestation_J (n : NodeState V) (a : Attestation V) :
    (on_attestation n a).S.J = n.S.J := by
  simp only [on_attestation, Id.run]
  split
  · rfl
  · exact fg_on_attestation_J n.S a

/-- Every answer of the attestation duty keeps the justified block: it writes the anti-slashing
record, and may receive its own attestation.

The variables:
- `C`: the parameters; `n`: the node state. -/
theorem attest_J (C : Config) (n : NodeState V) :
    DREBPost (attest C n) (fun n' => n'.S.J = n.S.J) := by
  simp only [attest]
  repeat' first
    | exact DREBPost.pure rfl
    | exact DREBPost.pure (on_attestation_J _ _)
    | refine DREBPost.dite (fun _ => ?_) (fun _ => ?_)
    | refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
    | refine DREBPost.bind_any (fun _ => ?_)

end

end

section

open GoldilocksCorrectness.Statements.Routines (PoolAttestationsWellFormed)

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]

section

variable [RootOrder]

omit [Fintype V] [RootOrder] in
/-- Receiving a well-formed attestation keeps every attestation of the pool well formed: the pool
gains that attestation, or nothing.

The variables:
- `S`: the FG state; `a`: the attestation. -/
theorem fg_on_attestation_wf (S : FGState V) (a : Attestation V)
    -- every attestation of the pool is well formed
    (hS : PoolAttestationsWellFormed S)
    -- `a` is well formed
    (ha : attestation_well_formed a = true) :
    PoolAttestationsWellFormed (fg_on_attestation S a) := by
  simp only [fg_on_attestation, Id.run]
  split
  · intro a' ha'
    rcases List.mem_append.1 ha' with h | h
    · exact hS a' h
    · rw [List.mem_singleton.1 h]
      exact ha
  · exact hS

omit [Fintype V] [RootOrder] in
/-- Receiving the attestations of a list in order, each well formed, keeps every attestation of
the pool well formed.

The variables:
- `l`: the attestations; `S`: the FG state. -/
theorem fg_on_attestations_wf (l : List (Attestation V)) (S : FGState V)
    -- every attestation of the pool is well formed
    (hS : PoolAttestationsWellFormed S)
    -- every attestation of `l` is well formed
    (hl : ∀ a ∈ l, attestation_well_formed a = true) :
    PoolAttestationsWellFormed
      (forIn (m := Id) l S (fun a X => Pure.pure (ForInStep.yield (fg_on_attestation X a)))) :=
  forIn_yield_inv l S (fun X a => fg_on_attestation X a) PoolAttestationsWellFormed hS
    (fun X a ha hX => fg_on_attestation_wf X a hX (hl a ha))

/-- Accepting a block whose attestations are well formed keeps every attestation of the pool well
formed: the pool gains the block's attestations, or some of them.

The variables:
- `C`: the parameters; `S`: the FG state; `B`: the block. -/
theorem fg_on_block_wf (C : Config) (S : FGState V) (B : Block V)
    -- every attestation of the pool is well formed
    (hS : PoolAttestationsWellFormed S)
    -- every attestation `B` includes is well formed
    (hB : ∀ a ∈ B.attestations, attestation_well_formed a = true) :
    PoolAttestationsWellFormed (fg_on_block C S B) := by
  set S₁ : FGState V := { S with
    σ := Function.update S.σ B (state_transition C (S.σ B.parent) B)
    T := S.T ∪ {B} } with hS₁
  have hdef : fg_on_block C S B = forIn (m := Id) B.attestations
      (update_finality S₁ (S₁.σ B))
      (fun a X => Pure.pure (ForInStep.yield (fg_on_attestation X a))) := rfl
  rw [hdef]
  refine fg_on_attestations_wf B.attestations _ (fun a ha => ?_) hB
  rw [update_finality_attestations] at ha
  exact hS a ha

end

end

end

section

open GoldilocksCorrectness.Statements.Routines (LockBelowJustified NodeInv
  PoolAttestationsWellFormed StampOrder TreeClosed TreeStamped)
open GoldilocksCorrectness.Statements.Routines (AttestationsValid ChainStatesComputed
  FinalizedAncestorJustified HeightCacheBounds JustificationCacheBounds JustifiedHeight
  JustifiedInTree)

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- What a block the node accepts satisfies: it is well formed, not in the tree, its parent is in
the tree, the finalized block is an ancestor of it, it has its slot's proposer, its parent is of
an earlier slot, and its attestations are valid against its parent's chain state.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `B`: the block. -/
theorem block_admissible_facts (C : Config) (P : Provisional V) (X : External V)
    (n : NodeState V) (B : Block V) (h : block_admissible C P X n B = true) :
    block_well_formed P X B = true ∧ B ∉ n.S.T ∧ B.parent ∈ n.S.T ∧ n.S.F.AncestorEq B ∧
      B.proposer? = some (P.proposer B.slot) ∧ B.parent.slot < B.slot ∧
      ∀ a ∈ B.attestations, valid_attestation (n.S.σ B.parent) a = true := by
  simp only [block_admissible, Id.run] at h
  split at h
  · exact absurd h Bool.false_ne_true
  rename_i h1
  split at h
  · exact absurd h Bool.false_ne_true
  split at h
  · exact absurd h Bool.false_ne_true
  rename_i h3
  split at h
  · exact absurd h Bool.false_ne_true
  rename_i h4
  split at h
  · exact absurd h Bool.false_ne_true
  rename_i h5
  split at h
  · exact absurd h Bool.false_ne_true
  rename_i h6
  split at h
  · exact absurd h Bool.false_ne_true
  rename_i h7
  split at h
  · exact absurd h Bool.false_ne_true
  rename_i h8
  have h5' : n.S.F.ancestorEq B = true := by simpa using h5
  refine ⟨by simpa using h1, fun hB => h3 ⟨B, hB, rfl⟩, by simpa using h4, h5',
    by simpa using h6, by simpa using h7, fun a ha => ?_⟩
  by_contra hne
  exact h8 ⟨a, ha, by simpa [fun_getElem] using hne⟩

omit [Fintype V] in
/-- A block the node accepts has a root no block of the tree has: case 3 of `block_admissible`.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `B`: the block. -/
theorem block_admissible_root_fresh (C : Config) (P : Provisional V) (X : External V)
    (n : NodeState V) (B : Block V) (h : block_admissible C P X n B = true) :
    ∀ B' ∈ n.S.T, B'.root ≠ B.root := by
  simp only [block_admissible, Id.run] at h
  split at h
  · exact absurd h Bool.false_ne_true
  split at h
  · exact absurd h Bool.false_ne_true
  split at h
  · exact absurd h Bool.false_ne_true
  rename_i h3
  exact fun B' hB' hr => h3 ⟨B', hB', hr⟩

omit [Fintype V] in
/-- Every attestation a well-formed block includes is well formed: the first test of
`block_well_formed`.

The variables:
- `P`, `X`: the values; `B`: the block. -/
theorem block_well_formed_attestations {P : Provisional V} {X : External V} {B : Block V}
    -- `B` is well formed
    (h : block_well_formed P X B = true) :
    -- then every attestation `B` includes is well formed
    ∀ a ∈ B.attestations, attestation_well_formed a = true := by
  simp only [block_well_formed, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1

open GoldilocksCorrectness.Statements.Routines (NodeInvCore NodeInvClock StampsBounded StampOrder PoolKeyed PoolStamped)

/-- The node invariant gives its clock-free part.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state.

Read aloud: a node state satisfying the invariant satisfies its clock-free part. -/
theorem NodeInv.core {C : Config} {P : Provisional V} {X : External V} {n : NodeState V}
    (h : NodeInv C P X n) : NodeInvCore C P X n := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, -, -, h10, h11⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h10, h11⟩

/-- The node invariant gives its clock part.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state.

Read aloud: a node state satisfying the invariant satisfies its clock part. -/
theorem NodeInv.clock {C : Config} {P : Provisional V} {X : External V} {n : NodeState V}
    (h : NodeInv C P X n) : NodeInvClock n :=
  ⟨h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1⟩

/-- The clock-free part and the clock part give the node invariant.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state.

Read aloud: the two parts together are the node invariant. -/
theorem nodeInv_of_core {C : Config} {P : Provisional V} {X : External V} {n : NodeState V}
    (h : NodeInvCore C P X n) (hc : NodeInvClock n) : NodeInv C P X n := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h10, h11⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, hc.1, hc.2, h10, h11⟩

/-- `NodeInvCore` transfers to a node state with the same tree, chain states, finalized block,
justified block, justification height, cache `h_max`, block stamps and anti-slashing record, a pool
satisfying `PoolInv`, and every attestation of its pool of attestations well formed; no condition on
the clocks. `nodeInv_of_frame` without its clock condition and its stamp bound.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`, `n'`: the two node states.

Read aloud: the clock-free part moves to a node state that keeps what it reads. -/
theorem nodeInvCore_of_frame {C : Config} {P : Provisional V} {X : External V}
    {n n' : NodeState V}
    (h : NodeInvCore C P X n) (hT : n'.S.T = n.S.T) (hσ : n'.S.σ = n.S.σ) (hF : n'.S.F = n.S.F)
    (hJ : n'.S.J = n.S.J) (hhm : n'.S.h_max = n.S.h_max) (hhj : n'.S.h_j = n.S.h_j)
    (hΛ : n'.Λ = n.Λ) (hTB : n'.A.timestamp_block = n.A.timestamp_block)
    (hV : PoolInv P n'.A) (hW : PoolAttestationsWellFormed n'.S) :
    NodeInvCore C P X n' := by
  obtain ⟨-, -, hC, hFT, hTS, hCS, hAV, ⟨hR, ⟨hFJ, hHC⟩, ⟨hJCB, hJH, hJIT, hLBJ, hRC⟩⟩, -⟩ := h
  refine ⟨hV.1, hV.2, ?_, ?_, ?_, ?_, ?_, ⟨?_, ⟨?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩⟩, hW⟩
  · unfold TreeClosed; rw [hT]; exact hC
  · rw [hF, hT]; exact hFT
  · unfold TreeStamped; rw [hT, hTB]; exact hTS
  · unfold ChainStatesComputed; rw [hT, hσ]; exact hCS
  · unfold AttestationsValid; rw [hT, hσ]; exact hAV
  · rw [hT]; exact hR
  · unfold FinalizedAncestorJustified; rw [hF, hJ]; exact hFJ
  · unfold HeightCacheBounds; rw [hT, hσ, hhm]; exact hHC
  · unfold JustificationCacheBounds; rw [hT, hF, hσ, hhj]; exact hJCB
  · unfold JustifiedHeight; rw [hJ, hσ, hhj]; exact hJH
  · unfold JustifiedInTree; rw [hJ, hT]; exact hJIT
  · unfold LockBelowJustified; rw [hΛ, hhj]; exact hLBJ
  · rw [hΛ]; exact hRC

/-- `NodeInv` transfers to a node state with the same tree, chain states, finalized block,
justified block, justification height, cache `h_max`, block stamps and anti-slashing record, a
clock no earlier, a pool satisfying `VotesInv` at its clock, and every attestation of its pool of
attestations well formed.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`, `n'`: the two node states. -/
theorem nodeInv_of_frame {C : Config} {P : Provisional V} {X : External V} {n n' : NodeState V}
    (h : NodeInv C P X n) (hT : n'.S.T = n.S.T) (hσ : n'.S.σ = n.S.σ) (hF : n'.S.F = n.S.F)
    (hJ : n'.S.J = n.S.J) (hhm : n'.S.h_max = n.S.h_max) (hhj : n'.S.h_j = n.S.h_j)
    (hΛ : n'.Λ = n.Λ)
    (hTB : n'.A.timestamp_block = n.A.timestamp_block) (ht : n.t ≤ n'.t)
    (hV : VotesInv P n'.A n'.t) (hW : PoolAttestationsWellFormed n'.S) : NodeInv C P X n' := by
  -- the clock-free part by its twin; the clock part: the block stamps are at most the old clock, so
  -- at most the new one, the vote stamps by `hV`, and the stamp order is read on the same tree and
  -- block stamps
  refine nodeInv_of_core (nodeInvCore_of_frame (NodeInv.core h) hT hσ hF hJ hhm hhj hΛ hTB ⟨hV.1, hV.2.1⟩ hW)
    ⟨⟨?_, hV.2.2⟩, ?_⟩
  · intro B hB τ hτ
    rw [hT] at hB
    rw [hTB] at hτ
    exact le_trans (h.2.2.2.2.2.2.2.1.1 B hB τ hτ) (WithBot.coe_le_coe.mpr ht)
  · unfold StampOrder; rw [hT, hTB]; exact h.2.2.2.2.2.2.2.2.1

end

end

section

open GoldilocksCorrectness.Statements.Routines (LockBelowJustified NodeInv
  PoolAttestationsWellFormed TreeClosed)
open GoldilocksCorrectness.Statements.Routines (chainStateOf)
open GoldilocksCorrectness.Statements.Routines (ChainStatesComputed JustificationCacheBounds)

section

open Goldilocks
open GoldilocksCorrectness.Statements.Routines (RecordConsistent)
variable {V : Type} [DecidableEq V] [Fintype V]

section

variable [RootOrder]

/-- `on_block` written as the `if` on `block_admissible` it is. -/
theorem on_block_eq (C : Config) (P : Provisional V) (X : External V) (n : NodeState V)
    (B : Block V) :
    on_block C P X n B = if block_admissible C P X n B = true then
      { n with S := fg_on_block C n.S B, A := ac_on_block C P n.A n.t B } else n := by
  simp only [on_block, Id.run]
  cases block_admissible C P X n B <;> rfl

open GoldilocksCorrectness.Statements.Routines (NodeInvCore NodeInvClock StampsBounded StampOrder PoolKeyed PoolStamped)

/-- Receiving a block keeps `NodeInvCore`, the validator and the clock. `on_block_nodeInv` without
its two stamp cases.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `B`: the block.

Read aloud: receiving a block keeps the clock-free part. -/
theorem on_block_nodeInvCore (C : Config) (P : Provisional V) (X : External V) (n : NodeState V)
    (B : Block V) (h : NodeInvCore C P X n) :
    NodeInvCore C P X (on_block C P X n B) ∧ (on_block C P X n B).v = n.v ∧
      (on_block C P X n B).t = n.t := by
  rw [on_block_eq]
  by_cases hb : block_admissible C P X n B = true
  swap
  · rw [if_neg hb]; exact ⟨h, rfl, rfl⟩
  rw [if_pos hb]
  refine ⟨?_, rfl, rfl⟩
  obtain ⟨hwf, hBT, hpar, hFB, hprop, hslot, hatt⟩ := block_admissible_facts C P X n B hb
  have hfresh := block_admissible_root_fresh C P X n B hb
  obtain ⟨hK, hS, ⟨hgen, hcl⟩, hFT, hTS, hCS, hAV,
    ⟨hR, ⟨hFJ, hHC⟩, ⟨hJCB, hJH, hJIT, hLBJ, hRC⟩⟩, hW⟩ := h
  obtain ⟨hT', hσ', hF'⟩ := fg_on_block_eq C n.S B
  have hTB' := ac_on_block_timestamp_block C P n.A n.t B
  have hV' := ac_on_block_poolInv C P n.A n.t B ⟨hK, hS⟩
  -- a block of the new tree is `B` or a block of the old tree
  have hmem : ∀ B'' ∈ (fg_on_block C n.S B).T, B'' = B ∨ B'' ∈ n.S.T := by
    intro B'' hB''
    rw [hT'] at hB''
    rcases Finset.mem_union.mp hB'' with h' | h'
    · exact Or.inr h'
    · exact Or.inl (Finset.mem_singleton.mp h')
  -- the parent of a non-genesis block of the new tree is in the old tree, so it is not `B`
  have hparOld : ∀ B'' ∈ (fg_on_block C n.S B).T, B'' ≠ Block.genesis → B''.parent ∈ n.S.T := by
    intro B'' hB'' hne
    rcases hmem B'' hB'' with rfl | h'
    · exact hpar
    · exact (hcl B'' h' hne).1
  have hne_of : ∀ B'' ∈ n.S.T, B'' ≠ B := fun B'' h' he => hBT (he ▸ h')
  have hcl' : TreeClosed P X (fg_on_block C n.S B) := by
    refine ⟨by rw [hT']; exact Finset.mem_union_left _ hgen, fun B'' hB'' hne => ?_⟩
    have hp := hparOld B'' hB'' hne
    refine ⟨by rw [hT']; exact Finset.mem_union_left _ hp, ?_⟩
    rcases hmem B'' hB'' with rfl | h'
    · exact ⟨hwf, hprop, hslot⟩
    · exact (hcl B'' h' hne).2
  -- the chain states of the new tree are computed
  have hCS' : ChainStatesComputed C (fg_on_block C n.S B) := by
    intro B'' hB''
    show (fg_on_block C n.S B).σ B'' = chainStateOf C B''
    rw [hσ', Function.update_apply]
    split
    · rename_i he
      subst he
      cases B'' with
      | genesis => exact absurd hgen hBT
      | node p s r votes support ats v =>
          rw [hCS _ hpar]
          rfl
    · rename_i hne
      rcases hmem B'' hB'' with h' | h'
      · exact absurd h' hne
      · exact hCS B'' h'
  obtain ⟨hJCB', hJH', hJIT'⟩ := fg_on_block_justified C n.S B
    (fun B'' h1 h2 => (hcl'.2 B'' h1 h2).1) hCS hCS' hBT hFB hFJ hJCB hJH hJIT
  have hhj := (fg_on_block_justification C n.S B).2.1
  refine ⟨hV'.1, hV'.2, hcl', ?_, ?_, hCS', ?_,
    ⟨?_, ⟨fg_on_block_finalizedAncestorJustified C n.S B hFJ,
      fg_on_block_heightCacheBounds C n.S B hHC⟩,
      ⟨hJCB', hJH', hJIT', fun h T hl => le_trans (hLBJ h T hl) hhj, hRC⟩⟩,
    fg_on_block_wf C n.S B hW (block_well_formed_attestations hwf)⟩
  · -- the finalized block is in the new tree
    show (fg_on_block C n.S B).F ∈ (fg_on_block C n.S B).T
    rcases hF' with hF' | ⟨B', hB', hanc⟩
    · rw [hF', hT']; exact Finset.mem_union_left _ hFT
    · exact ancestors_mem (fun B'' h1 h2 => (hcl'.2 B'' h1 h2).1) (by rw [hT']; exact hB') hanc
  · -- every block of the new tree is stamped
    intro B'' hB''
    show (ac_on_block C P n.A n.t B).timestamp_block B'' ≠ none
    rw [hTB', Function.update_apply]
    split
    · simp
    · rename_i hne
      rcases hmem B'' hB'' with h' | h'
      · exact absurd h' hne
      · exact hTS B'' h'
  · -- the attestations of the new tree are valid
    intro B'' hB'' hne a ha
    show valid_attestation ((fg_on_block C n.S B).σ B''.parent) a = true
    have hp := hparOld B'' hB'' hne
    rw [hσ', Function.update_apply, if_neg (hne_of _ hp)]
    rcases hmem B'' hB'' with rfl | h'
    · exact hatt a ha
    · exact hAV B'' h' hne a ha
  · -- no two blocks of the new tree share a root: `B`'s root is new
    intro B₁ hB₁ B₂ hB₂ hr
    rcases hmem B₁ hB₁ with rfl | h₁ <;> rcases hmem B₂ hB₂ with rfl | h₂
    · rfl
    · exact absurd hr.symm (hfresh B₂ h₂)
    · exact absurd hr (hfresh B₁ h₁)
    · exact hR B₁ h₁ B₂ h₂ hr

/-- Receiving a block keeps `NodeInv`, the validator and the clock. A refused block changes
nothing; an accepted block is new, its parent is held, and it passed every check `NodeInv` records
of a tree block, so the block, its chain state and its stamp `n.t` extend the invariant.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `B`: the block. -/
theorem on_block_nodeInv (C : Config) (P : Provisional V) (X : External V) (n : NodeState V)
    (B : Block V) (h : NodeInv C P X n) :
    NodeInv C P X (on_block C P X n B) ∧ (on_block C P X n B).v = n.v ∧
      (on_block C P X n B).t = n.t := by
  -- the clock-free part by its twin; the clock part: the new block is stamped with the clock, after
  -- its parent's stamp, and the other stamps are kept
  obtain ⟨hcore, hv, ht⟩ := on_block_nodeInvCore C P X n B (NodeInv.core h)
  refine ⟨nodeInv_of_core hcore ?_, hv, ht⟩
  rw [on_block_eq]
  by_cases hb : block_admissible C P X n B = true
  swap
  · rw [if_neg hb]; exact (NodeInv.clock h)
  rw [if_pos hb]
  obtain ⟨-, hBT, hpar, -, -, -, -⟩ := block_admissible_facts C P X n B hb
  obtain ⟨hK, hS, ⟨-, hcl⟩, -, hTS, -, -, ⟨hSB1, hSB2⟩, hSO, -, -⟩ := h
  obtain ⟨hT', -, -⟩ := fg_on_block_eq C n.S B
  have hTB' := ac_on_block_timestamp_block C P n.A n.t B
  have hV' := ac_on_block_votesInv C P n.A n.t n.t B ⟨hK, hS, hSB2⟩ le_rfl
  have hmem : ∀ B'' ∈ (fg_on_block C n.S B).T, B'' = B ∨ B'' ∈ n.S.T := by
    intro B'' hB''
    rw [hT'] at hB''
    rcases Finset.mem_union.mp hB'' with h' | h'
    · exact Or.inr h'
    · exact Or.inl (Finset.mem_singleton.mp h')
  have hparOld : ∀ B'' ∈ (fg_on_block C n.S B).T, B'' ≠ Block.genesis → B''.parent ∈ n.S.T := by
    intro B'' hB'' hne
    rcases hmem B'' hB'' with rfl | h'
    · exact hpar
    · exact (hcl B'' h' hne).1
  have hne_of : ∀ B'' ∈ n.S.T, B'' ≠ B := fun B'' h' he => hBT (he ▸ h')
  refine ⟨⟨?_, hV'.2.2⟩, ?_⟩
  · -- the block stamps are at most the clock
    intro B'' hB'' τ hτ
    change (ac_on_block C P n.A n.t B).timestamp_block B'' = some τ at hτ
    rw [hTB', Function.update_apply] at hτ
    split at hτ
    · cases hτ
      exact le_rfl
    · rename_i hne
      rcases hmem B'' hB'' with h' | h'
      · exact absurd h' hne
      · exact hSB1 B'' h' τ hτ
  · -- every block is stamped no earlier than its parent
    intro B'' hB'' hne
    show ∃ τ τ' : Stamp, (ac_on_block C P n.A n.t B).timestamp_block B''.parent = some τ ∧
      (ac_on_block C P n.A n.t B).timestamp_block B'' = some τ' ∧ τ ≤ τ'
    have hp := hparOld B'' hB'' hne
    rw [hTB', Function.update_apply, Function.update_apply, if_neg (hne_of _ hp)]
    rcases hmem B'' hB'' with rfl | h'
    · rw [if_pos rfl]
      obtain ⟨τ, hτ⟩ := Option.ne_none_iff_exists'.mp (hTS _ hp)
      exact ⟨τ, n.t, hτ, rfl, hSB1 _ hp τ hτ⟩
    · rw [if_neg (hne_of _ h')]
      exact hSO B'' h' hne

omit [RootOrder] in
/-- Receiving a Goldfish vote keeps `NodeInv`, the validator and the clock.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `vote`: the vote. -/
theorem on_ac_message_nodeInv (C : Config) (P : Provisional V) (X : External V)
    (n : NodeState V) (vote : GoldfishVote V) (h : NodeInv C P X n) :
    NodeInv C P X (on_ac_message C P n vote) ∧ (on_ac_message C P n vote).v = n.v ∧
      (on_ac_message C P n vote).t = n.t := by
  have he : on_ac_message C P n vote = { n with A := on_goldfish_vote C P n.A n.t vote } := rfl
  rw [he]
  refine ⟨nodeInv_of_frame h rfl rfl rfl rfl rfl rfl rfl
    (on_goldfish_vote_timestamp_block C P n.A n.t vote)
    le_rfl (on_goldfish_vote_votesInv C P n.A n.t n.t vote ⟨h.1, h.2.1, h.2.2.2.2.2.2.2.1.2⟩
      le_rfl) h.2.2.2.2.2.2.2.2.2.2, rfl, rfl⟩

omit [RootOrder] in
/-- Receiving an attestation keeps `NodeInv`, the validator and the clock.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `a`: the attestation. -/
theorem on_attestation_nodeInv (C : Config) (P : Provisional V) (X : External V)
    (n : NodeState V) (a : Attestation V) (h : NodeInv C P X n) :
    NodeInv C P X (on_attestation n a) ∧ (on_attestation n a).v = n.v ∧
      (on_attestation n a).t = n.t := by
  simp only [on_attestation, Id.run]
  split
  · exact ⟨h, rfl, rfl⟩
  · rename_i hwf
    have ha : attestation_well_formed a = true := by simpa using hwf
    obtain ⟨h1, h2, h3⟩ := fg_on_attestation_keeps n.S a
    obtain ⟨h4, h5⟩ := fg_on_attestation_caches n.S a
    exact ⟨nodeInv_of_frame h h1 h2 h3 h4 h5 (fg_on_attestation_h_j n.S a) rfl rfl le_rfl
      ⟨h.1, h.2.1, h.2.2.2.2.2.2.2.1.2⟩
      (fg_on_attestation_wf n.S a h.2.2.2.2.2.2.2.2.2.2 ha), rfl, rfl⟩

omit [RootOrder] in
/-- Waking at a time `t` no earlier than the clock keeps `NodeInv` and the validator and sets
the clock to `t`: it writes `awakeSince` and the clock only, and every stamp held stays at most the
clock.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `t`: the wake time. -/
theorem wake_nodeInv (C : Config) (P : Provisional V) (X : External V) (n : NodeState V)
    (t : Time) (h : NodeInv C P X n) (ht : n.t ≤ t) :
    NodeInv C P X (wake n t) ∧ (wake n t).v = n.v ∧ (wake n t).t = t :=
  ⟨nodeInv_of_frame h (n' := wake n t) rfl rfl rfl rfl rfl rfl rfl rfl ht
    (VotesInv.mono ⟨h.1, h.2.1, h.2.2.2.2.2.2.2.1.2⟩ ht) h.2.2.2.2.2.2.2.2.2.2, rfl, rfl⟩

omit [DecidableEq V] [Fintype V] [RootOrder] in
/-- Recording the time of a wake keeps the FG state, the AC state, the validator and the clock.

The variables:
- `n`: the node state; `t`: the time. -/
theorem record_awake_frame (n : NodeState V) (t : Time) :
    (record_awake n t).S = n.S ∧ (record_awake n t).A = n.A ∧ (record_awake n t).v = n.v ∧
      (record_awake n t).t = n.t := by
  simp only [record_awake, Id.run]
  split <;> exact ⟨rfl, rfl, rfl, rfl⟩

omit [DecidableEq V] [Fintype V] [RootOrder] in
/-- Recording the time of a wake keeps the anti-slashing record.

The variables:
- `n`: the node state; `t`: the time. -/
theorem record_awake_keeps_record (n : NodeState V) (t : Time) : (record_awake n t).Λ = n.Λ := by
  simp only [record_awake, Id.run]
  split <;> rfl

/-- Every answer of the proposal keeps `NodeInv`, the validator and the clock: it ends by
receiving the proposed block.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state. -/
theorem propose_block_nodeInv (C : Config) (P : Provisional V) (X : External V)
    (n : NodeState V) (h : NodeInv C P X n) :
    DREBPost (propose_block C P X n)
      (fun n' => NodeInv C P X n' ∧ n'.v = n.v ∧ n'.t = n.t) := by
  simp only [propose_block]
  repeat' first
    | exact DREBPost.pure (on_block_nodeInv C P X n _ h)
    | refine DREBPost.bind_any (fun _ => ?_)

open GoldilocksCorrectness.Statements.Routines (NodeInvCore NodeInvClock StampsBounded StampOrder PoolKeyed PoolStamped)

omit [RootOrder] in
/-- `NodeInvCore` holds of the node state with its anti-slashing record replaced by `Λ'`, when it
holds of the node state, `LockBelowJustified` holds of the new node state and `Λ'` is consistent.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `Λ'`: the new record.

Read aloud: a consistent record below the justification height keeps the clock-free part. -/
theorem nodeInvCore_of_record {C : Config} {P : Provisional V} {X : External V} {n : NodeState V}
    (h : NodeInvCore C P X n) (Λ' : SigningHistory) (hL : LockBelowJustified { n with Λ := Λ' })
    (hR : RecordConsistent Λ') : NodeInvCore C P X { n with Λ := Λ' } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, ⟨h10, h11, ⟨h12, h13, h14, -, -⟩⟩, h15⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, ⟨h10, h11, ⟨h12, h13, h14, hL, hR⟩⟩, h15⟩

omit [RootOrder] in
/-- `NodeInv` holds of the node state with its anti-slashing record replaced by `Λ'`, when it holds
of the node state, `LockBelowJustified` holds of the new node state and `Λ'` is consistent.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `Λ'`: the new record. -/
theorem nodeInv_of_record {C : Config} {P : Provisional V} {X : External V} {n : NodeState V}
    (h : NodeInv C P X n) (Λ' : SigningHistory) (hL : LockBelowJustified { n with Λ := Λ' })
    (hR : RecordConsistent Λ') : NodeInv C P X { n with Λ := Λ' } :=
  nodeInv_of_core (nodeInvCore_of_record (NodeInv.core h) Λ' hL hR) (NodeInv.clock (n := n) h)

omit [RootOrder] in
/-- The record `fg_attest` returns keeps `NodeInv`, when the head is a block of the tree of which
the finalized block is an ancestor, or which is the finalized block: its new lock is at the head's
justification height, which `JustificationCacheBounds` bounds by the cache `h_j`, and it is
consistent (Lemma 72).

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `source`, `head`: the blocks
  the attestation is built from. -/
theorem fg_attest_nodeInv {C : Config} {P : Provisional V} {X : External V} {n : NodeState V}
    (h : NodeInv C P X n) (source head : Block V)
    -- the head is a block of the tree, and the finalized block is it or an ancestor of it
    (hhead : head ∈ n.S.T) (hFh : n.S.F.AncestorEq head) :
    NodeInv C P X { n with Λ := (fg_attest n.S n.Λ n.v source head).1 } := by
  have hJCB : JustificationCacheBounds n.S := h.2.2.2.2.2.2.2.2.2.1.2.2.1
  have hLBJ : LockBelowJustified n := h.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.1
  have hRC : RecordConsistent n.Λ := h.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2
  refine nodeInv_of_record h _ (fun hh T hl => ?_) ?_
  · rw [fg_attest_eq] at hl
    rcases create_attestation_lock _ _ _ _ _ _ _ hh T hl with hl' | hh'
    · exact hLBJ hh T hl'
    · show hh ≤ n.S.h_j
      rw [hh']
      exact hJCB head hhead hFh
  · rw [fg_attest_eq]
    exact (GoldilocksCorrectness.Proofs.Routines.lem72_create_attestation_consistent _ _ _ _ _ _ _
      hRC).1

/-- Every answer of the attestation duty keeps `NodeInv`, the validator and the clock: it writes
the anti-slashing record from a head of the tree on the finalized block's chain, and may receive
its own attestation.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state. -/
theorem attest_nodeInv (C : Config) (P : Provisional V) (X : External V) (n : NodeState V)
    (h : NodeInv C P X n) :
    DREBPost (attest C n) (fun n' => NodeInv C P X n' ∧ n'.v = n.v ∧ n'.t = n.t) := by
  have hhead := ac_to_fg_head_mem C n.A n.S n.t h.2.2.2.1 h.2.2.2.2.2.2.2.2.2.1.2.2.2.2.1
    h.2.2.2.2.2.2.2.2.2.1.2.1.1
  simp only [attest]
  refine DREBPost.bind (DREBPost.liftM hhead) (fun fi hfi => ?_)
  have hrec : ∀ source : Block V,
      NodeInv C P X { n with Λ := (fg_attest n.S n.Λ n.v source fi.head).1 } :=
    fun source => fg_attest_nodeInv h source fi.head hfi.1 hfi.2
  obtain ⟨src?, head⟩ := fi
  repeat' first
    | exact DREBPost.pure ⟨h, rfl, rfl⟩
    | exact DREBPost.pure ⟨hrec _, rfl, rfl⟩
    | exact DREBPost.pure (on_attestation_nodeInv C P X _ _ (hrec _))
    | refine DREBPost.dite (fun _ => ?_) (fun _ => ?_)
    | refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
    | refine DREBPost.bind_any (fun _ => ?_)

/-- The proposal keeps "`NodeInv`, the validator `v` and the clock `t`". -/
theorem propose_block_from {C : Config} {P : Provisional V} {X : External V} {v : V} {t : Time}
    (n : NodeState V) (h : NodeInv C P X n ∧ n.v = v ∧ n.t = t) :
    DREBPost (propose_block C P X n) (fun n' => NodeInv C P X n' ∧ n'.v = v ∧ n'.t = t) :=
  (propose_block_nodeInv C P X n h.1).mono
    (fun _ h' => ⟨h'.1, h'.2.1.trans h.2.1, h'.2.2.trans h.2.2⟩)

/-- The attestation duty keeps "`NodeInv`, the validator `v` and the clock `t`". -/
theorem attest_from {C : Config} {P : Provisional V} {X : External V} {v : V} {t : Time}
    (n : NodeState V) (h : NodeInv C P X n ∧ n.v = v ∧ n.t = t) :
    DREBPost (attest C n) (fun n' => NodeInv C P X n' ∧ n'.v = v ∧ n'.t = t) :=
  (attest_nodeInv C P X n h.1).mono
    (fun _ h' => ⟨h'.1, h'.2.1.trans h.2.1, h'.2.2.trans h.2.2⟩)

/-- Every answer of the node's tick at a time `t` no earlier than its clock satisfies `NodeInv`,
keeps the validator, and has the clock `t`: the tick sets the clock to `t` first, so every stamp
held stays at most the clock, and every routine it runs stamps with `t`.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `t`: the time. -/
theorem tick_nodeInv (C : Config) (P : Provisional V) (X : External V) (n : NodeState V)
    (t : Time) (h : NodeInv C P X n) (ht : n.t ≤ t) :
    DREBPost (tick C P X n t) (fun n' => NodeInv C P X n' ∧ n'.v = n.v ∧ n'.t = t) := by
  obtain ⟨hS, hA, hv, -⟩ := record_awake_frame n t
  have hV : VotesInv P (record_awake n t).A t := by
    rw [hA]
    exact VotesInv.mono ⟨h.1, h.2.1, h.2.2.2.2.2.2.2.1.2⟩ ht
  have h2 : NodeInv C P X { record_awake n t with t := t } :=
    nodeInv_of_frame h (n' := { record_awake n t with t := t }) (by show _ = _; rw [hS])
      (by show _ = _; rw [hS]) (by show _ = _; rw [hS]) (by show _ = _; rw [hS])
      (by show _ = _; rw [hS]) (by show _ = _; rw [hS]) (record_awake_keeps_record n t)
      (by show _ = _; rw [hA]) ht hV
      (by show PoolAttestationsWellFormed (record_awake n t).S; rw [hS]
          exact h.2.2.2.2.2.2.2.2.2.2)
  simp only [tick]
  refine DREBPost.bind (ac_on_tick_votesInv C P _ _ t t _ _ _ hV le_rfl) (fun A' hA' => ?_)
  have hq : NodeInv C P X { { record_awake n t with t := t } with A := A' } ∧
      ({ { record_awake n t with t := t } with A := A' } : NodeState V).v = n.v ∧
      ({ { record_awake n t with t := t } with A := A' } : NodeState V).t = t :=
    ⟨nodeInv_of_frame h2 rfl rfl rfl rfl rfl rfl rfl hA'.2 le_rfl hA'.1 h2.2.2.2.2.2.2.2.2.2.2,
      hv, rfl⟩
  -- the proposal, when it runs, then the attestation, when it runs
  refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
  · refine DREBPost.bind (propose_block_from _ hq) (fun n₄ h₄ => ?_)
    refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
    · exact DREBPost.bind (attest_from _ h₄) (fun _ h₅ => DREBPost.pure h₅)
    · exact DREBPost.pure h₄
  · refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
    · exact DREBPost.bind (attest_from _ hq) (fun _ h₅ => DREBPost.pure h₅)
    · exact DREBPost.pure hq

end

end

end

section

open GoldilocksCorrectness.Statements.Routines (chainStateOf)
open GoldilocksCorrectness.Statements.Routines (ChainStatesComputed)

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- Receiving a block, from a node state whose chain states of its tree are the blocks' own,
relates the node state to the result. A refused block changes nothing. An accepted block enters
the tree, and the finalized block is kept or becomes the finalized block of the chain state
computed for the block, which is the block's own since its parent is in the tree.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `B`: the block. -/
theorem on_block_finalizedFrom (C : Config) (P : Provisional V) (X : External V)
    (n : NodeState V) (B : Block V)
    -- the chain states of `n`'s tree are the blocks' own
    (hCS : ChainStatesComputed C n.S) :
    FinalizedFrom C n (on_block C P X n B) := by
  rw [on_block_eq]
  by_cases hb : block_admissible C P X n B = true
  swap
  · rw [if_neg hb]; exact finalizedFrom_refl C n
  rw [if_pos hb]
  obtain ⟨-, -, hpar, -, -, hslot, -⟩ := block_admissible_facts C P X n B hb
  obtain ⟨hT', -, -⟩ := fg_on_block_eq C n.S B
  refine ⟨?_, ?_⟩
  · show n.S.T ⊆ (fg_on_block C n.S B).T
    rw [hT']
    exact Finset.subset_union_left
  · show (fg_on_block C n.S B).F = n.S.F ∨
      ∃ B' ∈ (fg_on_block C n.S B).T, (fg_on_block C n.S B).F = (chainStateOf C B').F
    rcases fg_on_block_F_cases C n.S B with hF | hF
    · exact Or.inl hF
    · refine Or.inr ⟨B, by rw [hT']; exact Finset.mem_union_right _ (Finset.mem_singleton_self B),
        ?_⟩
      rw [hF, hCS B.parent hpar]
      cases B with
      | genesis =>
          simp only [Block.parent, Block.slot] at hslot
          exact absurd hslot (lt_irrefl _)
      | node p s r votes support ats v => rfl

/-- Every answer of the proposal, from a node state whose chain states of its tree are the blocks'
own, relates the node state to the answer: it ends by receiving the proposed block.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state. -/
theorem propose_block_finalizedFrom (C : Config) (P : Provisional V) (X : External V)
    (n : NodeState V)
    -- the chain states of `n`'s tree are the blocks' own
    (hCS : ChainStatesComputed C n.S) :
    DREBPost (propose_block C P X n) (fun n' => FinalizedFrom C n n') := by
  simp only [propose_block]
  repeat' first
    | exact DREBPost.pure (on_block_finalizedFrom C P X n _ hCS)
    | refine DREBPost.bind_any (fun _ => ?_)

/-- Every answer of the node's tick, from a node state whose chain states of its tree are the
blocks' own, relates the node state to the answer: the wake record, the clock and the tick of the
available chain keep the FG state, the proposal relates, and the attestation keeps the tree and
the finalized block.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `t`: the time. -/
theorem tick_finalizedFrom (C : Config) (P : Provisional V) (X : External V) (n : NodeState V)
    (t : Time)
    -- the chain states of `n`'s tree are the blocks' own
    (hCS : ChainStatesComputed C n.S) :
    DREBPost (tick C P X n t) (fun n' => FinalizedFrom C n n') := by
  obtain ⟨hS, -, -, -⟩ := record_awake_frame n t
  simp only [tick]
  refine DREBPost.bind_any (fun A' => ?_)
  have hq : FinalizedFrom C n { { record_awake n t with t := t } with A := A' } :=
    finalizedFrom_of_frame C (by show (record_awake n t).S.T = n.S.T; rw [hS])
      (by show (record_awake n t).S.F = n.S.F; rw [hS])
  have hCS₁ : ChainStatesComputed C
      ({ { record_awake n t with t := t } with A := A' } : NodeState V).S := by
    show ChainStatesComputed C (record_awake n t).S
    rw [hS]
    exact hCS
  -- the proposal, when it runs, then the attestation, when it runs
  refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
  · refine DREBPost.bind (P := fun n' => FinalizedFrom C n n')
      ((propose_block_finalizedFrom C P X _ hCS₁).mono
        (fun _ h' => finalizedFrom_trans C hq h')) (fun n₄ h₄ => ?_)
    refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
    · exact DREBPost.bind (attest_frame_S C n₄) (fun _ h₅ =>
        DREBPost.pure (finalizedFrom_trans C h₄ (finalizedFrom_of_frame C h₅.1 h₅.2)))
    · exact DREBPost.pure h₄
  · refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
    · exact DREBPost.bind (attest_frame_S C _) (fun _ h₅ =>
        DREBPost.pure (finalizedFrom_trans C hq (finalizedFrom_of_frame C h₅.1 h₅.2)))
    · exact DREBPost.pure hq

end

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- Receiving a block keeps `ChainsInPool`: an accepted block's parent is held, so what its
parent's chain includes is in the pool already, and the attestations the block includes are
received into the pool.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `B`: the block. -/
theorem on_block_chainsInPool (C : Config) (P : Provisional V) (X : External V)
    (n : NodeState V) (B : Block V) (h : ChainsInPool n) : ChainsInPool (on_block C P X n B) := by
  rw [on_block_eq]
  split
  · rename_i hadm
    obtain ⟨-, -, hpar, -⟩ := block_admissible_facts C P X n B hadm
    intro Y hY a ha
    have hT := (fg_on_block_eq C n.S B).1
    change Y ∈ (fg_on_block C n.S B).T at hY
    change a ∈ (fg_on_block C n.S B).attestations
    rw [hT] at hY
    rcases Finset.mem_union.1 hY with hY | hY
    · exact fg_on_block_pool C n.S B a (h Y hY a ha)
    · rw [Finset.mem_singleton.1 hY] at ha
      cases B with
      | genesis => simp [on_chain, attestations_on_chain] at ha
      | node p s r votes support ats v =>
          simp only [on_chain, attestations_on_chain, decide_eq_true_eq, List.mem_append] at ha
          rcases ha with ha | ha
          · exact fg_on_block_holds C n.S _ a ha
          · exact fg_on_block_pool C n.S _ a (h p hpar a (by simpa [on_chain] using ha))
  · exact h

/-- Every answer of the proposal keeps `ChainsInPool`.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state. -/
theorem propose_block_chainsInPool (C : Config) (P : Provisional V) (X : External V)
    (n : NodeState V) (h : ChainsInPool n) :
    DREBPost (propose_block C P X n) ChainsInPool := by
  simp only [propose_block]
  repeat' first
    | exact DREBPost.pure (on_block_chainsInPool C P X n _ h)
    | refine DREBPost.bind_any (fun _ => ?_)

end

section

open GoldilocksCorrectness.Statements.Routines (chainStateOf)
open GoldilocksCorrectness.Statements.Routines (ChainStatesComputed)

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- Receiving a block, from a node state whose chain states of its tree are the blocks' own,
relates the node state to the result. A refused block changes nothing. An accepted block keeps the
justified block or writes the justified block of the chain state computed for the block, which is
the block's own since its parent is in the tree.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `B`: the block. -/
theorem on_block_justifiedFrom (C : Config) (P : Provisional V) (X : External V)
    (n : NodeState V) (B : Block V)
    -- the chain states of `n`'s tree are the blocks' own
    (hCS : ChainStatesComputed C n.S) :
    JustifiedFrom C n (on_block C P X n B) := by
  rw [on_block_eq]
  by_cases hb : block_admissible C P X n B = true
  swap
  · rw [if_neg hb]; exact justifiedFrom_refl C n
  rw [if_pos hb]
  obtain ⟨-, -, hpar, -, -, hslot, -⟩ := block_admissible_facts C P X n B hb
  show (fg_on_block C n.S B).J = n.S.J ∨ ∃ D : Block V, (fg_on_block C n.S B).J = (chainStateOf C D).J
  rcases fg_on_block_J_cases C n.S B with hJ | hJ
  · exact Or.inl hJ
  · refine Or.inr ⟨B, ?_⟩
    rw [hJ, hCS B.parent hpar]
    cases B with
    | genesis =>
        simp only [Block.parent, Block.slot] at hslot
        exact absurd hslot (lt_irrefl _)
    | node p s r votes support ats v => rfl

/-- Every answer of the proposal, from a node state whose chain states of its tree are the blocks'
own, relates the node state to the answer: it ends by receiving the proposed block.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state. -/
theorem propose_block_justifiedFrom (C : Config) (P : Provisional V) (X : External V)
    (n : NodeState V)
    -- the chain states of `n`'s tree are the blocks' own
    (hCS : ChainStatesComputed C n.S) :
    DREBPost (propose_block C P X n) (fun n' => JustifiedFrom C n n') := by
  simp only [propose_block]
  repeat' first
    | exact DREBPost.pure (on_block_justifiedFrom C P X n _ hCS)
    | refine DREBPost.bind_any (fun _ => ?_)

/-- Every answer of the node's tick, from a node state whose chain states of its tree are the
blocks' own, relates the node state to the answer: the wake record, the clock and the tick of the
available chain keep the FG state, the proposal relates, and the attestation keeps the justified
block.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `t`: the time. -/
theorem tick_justifiedFrom (C : Config) (P : Provisional V) (X : External V) (n : NodeState V)
    (t : Time)
    -- the chain states of `n`'s tree are the blocks' own
    (hCS : ChainStatesComputed C n.S) :
    DREBPost (tick C P X n t) (fun n' => JustifiedFrom C n n') := by
  obtain ⟨hS, -, -, -⟩ := record_awake_frame n t
  simp only [tick]
  refine DREBPost.bind_any (fun A' => ?_)
  have hq : JustifiedFrom C n { { record_awake n t with t := t } with A := A' } :=
    justifiedFrom_of_frame C (congrArg FGState.J hS)
  have hCS₁ : ChainStatesComputed C
      ({ { record_awake n t with t := t } with A := A' } : NodeState V).S := by
    show ChainStatesComputed C (record_awake n t).S
    rw [hS]
    exact hCS
  -- the proposal, when it runs, then the attestation, when it runs
  refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
  · refine DREBPost.bind (P := fun n' => JustifiedFrom C n n')
      ((propose_block_justifiedFrom C P X _ hCS₁).mono
        (fun _ h' => justifiedFrom_trans C hq h')) (fun n₄ h₄ => ?_)
    refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
    · exact DREBPost.bind (attest_J C n₄) (fun _ h₅ =>
        DREBPost.pure (justifiedFrom_trans C h₄ (justifiedFrom_of_frame C h₅)))
    · exact DREBPost.pure h₄
  · refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
    · exact DREBPost.bind (attest_J C _) (fun _ h₅ =>
        DREBPost.pure (justifiedFrom_trans C hq (justifiedFrom_of_frame C h₅)))
    · exact DREBPost.pure hq

end

end

section

open GoldilocksCorrectness.Statements.Routines (NodeInv)

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]

/-- The node state a validator starts from satisfies `NodeInv`: the pool is empty, and the tree
holds the genesis block alone, stamped `genesisStamp`, with the initial chain state.

The variables:
- `C`, `P`, `X`: the parameters and the values; `v`: the validator. -/
theorem initial_nodeInv (C : Config) (P : Provisional V) (X : External V) (v : V) :
    NodeInv C P X (initial C v) := by
  have hT : ∀ B ∈ (initial C v).S.T, B = Block.genesis := fun B hB => Finset.mem_singleton.mp hB
  have hgen : (Block.genesis : Block V) ∈ (initial C v).S.T := Finset.mem_singleton_self _
  have hnil : ∀ s : Slot, (initial C v).A.gf_votes s = [] := fun _ => rfl
  refine ⟨fun s vote hv => ?_, fun s vote hv => ?_, ⟨hgen, fun B hB hne => absurd (hT B hB) hne⟩,
    hgen, fun B hB => ?_, fun B hB => ?_, fun B hB hne => absurd (hT B hB) hne,
    ⟨fun B hB τ hτ => ?_, fun s vote hv => ?_⟩, fun B hB hne => absurd (hT B hB) hne,
    ⟨fun B hB B' hB' _ => (hT B hB).trans (hT B' hB').symm, ⟨ancestorEq_refl _, fun B hB => le_rfl⟩,
      ⟨fun B hB _ => le_rfl, Or.inl rfl, hgen, (fun h T hl => by cases hl),
        GoldilocksCorrectness.Proofs.Routines.lem72_initial_record_consistent⟩⟩,
    fun a ha => ?_⟩
  · rw [hnil] at hv; cases hv
  · rw [hnil] at hv; cases hv
  · rw [hT B hB]; simp [initial, ACState.initial]
  · rw [hT B hB]; rfl
  · rw [hT B hB] at hτ
    have hτ' : some genesisStamp = some τ := hτ
    cases hτ'
    exact bot_le
  · rw [hnil] at hv; cases hv
  · -- the pool of attestations is empty
    simp [initial, FGState.initial] at ha

end

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- Every answer of the attestation duty keeps the tree of the FG state: it writes the
anti-slashing record and, through `on_attestation`, the attestation pool only.

The variables:
- `C`: the parameters; `n`: the node state. -/
theorem attest_T (C : Config) (n : NodeState V) :
    DREBPost (attest C n) (fun n' => n'.S.T = n.S.T) := by
  simp only [attest]
  repeat' first
    | exact DREBPost.pure rfl
    | exact DREBPost.pure (on_attestation_frame _ _).1
    | refine DREBPost.dite (fun _ => ?_) (fun _ => ?_)
    | refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
    | refine DREBPost.bind_any (fun _ => ?_)

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]

/-- `AttPoolGrows n n'`: every attestation of the pool of `n` is in the pool of `n'`.

The variables:
- `n`, `n'`: the two node states. -/
def AttPoolGrows (n n' : NodeState V) : Prop :=
  ∀ a ∈ n.S.attestations, a ∈ n'.S.attestations

omit [DecidableEq V] [Fintype V] in
/-- A node state's pool is in its own pool. -/
theorem AttPoolGrows.refl (n : NodeState V) : AttPoolGrows n n := fun _ h => h

omit [DecidableEq V] [Fintype V] in
/-- `AttPoolGrows` composes. -/
theorem AttPoolGrows.trans {n n' n'' : NodeState V} (h : AttPoolGrows n n')
    (h' : AttPoolGrows n' n'') : AttPoolGrows n n'' := fun a ha => h' a (h a ha)

omit [DecidableEq V] [Fintype V] in
/-- A node state with the same FG state has the same pool. -/
theorem AttPoolGrows.of_S {n n' : NodeState V} (hS : n'.S = n.S) : AttPoolGrows n n' :=
  fun a ha => by rw [hS]; exact ha

omit [Fintype V] in
/-- Receiving the attestation `a` keeps the pool, and holds `a` when it is well formed.

The variables:
- `n`: the node state; `a`: the attestation. -/
theorem on_attestation_pool (n : NodeState V) (a : Attestation V) :
    AttPoolGrows n (on_attestation n a) ∧
      (attestation_well_formed a = true → a ∈ (on_attestation n a).S.attestations) := by
  simp only [on_attestation, Id.run]
  split
  · rename_i h
    refine ⟨AttPoolGrows.refl n, fun hw => ?_⟩
    simp [hw] at h
  · exact ⟨(fg_on_attestation_pool n.S a).1, fun _ => (fg_on_attestation_pool n.S a).2⟩

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

omit [Fintype V] [RootOrder] in
/-- `ChainsInPool` is kept by a change that keeps the tree and grows the pool.

The variables:
- `n`, `n'`: the two node states. -/
theorem ChainsInPool.of_tree_pool {n n' : NodeState V} (h : ChainsInPool n)
    (hT : n'.S.T = n.S.T) (hP : AttPoolGrows n n') : ChainsInPool n' := by
  intro Y hY a ha
  rw [hT] at hY
  exact hP a (h Y hY a ha)

omit [Fintype V] [RootOrder] in
/-- `ChainsInPool` is kept by a change that keeps the FG state.

The variables:
- `n`, `n'`: the two node states. -/
theorem ChainsInPool.of_S {n n' : NodeState V} (h : ChainsInPool n) (hS : n'.S = n.S) :
    ChainsInPool n' :=
  h.of_tree_pool (by rw [hS]) (AttPoolGrows.of_S hS)

omit [Fintype V] [RootOrder] in
/-- Receiving an attestation keeps `ChainsInPool`: it keeps the tree and grows the pool.

The variables:
- `n`: the node state; `a`: the attestation. -/
theorem on_attestation_chainsInPool (n : NodeState V) (a : Attestation V) (h : ChainsInPool n) :
    ChainsInPool (on_attestation n a) := by
  refine h.of_tree_pool ?_ (on_attestation_pool n a).1
  simp only [on_attestation, Id.run]
  split
  · rfl
  · exact (fg_on_attestation_keeps n.S a).1

/-- Every answer of the attestation duty keeps `ChainsInPool`.

The variables:
- `C`: the parameters; `n`: the node state. -/
theorem attest_chainsInPool (C : Config) (n : NodeState V) (h : ChainsInPool n) :
    DREBPost (attest C n) ChainsInPool := by
  simp only [attest]
  repeat' first
    | exact DREBPost.pure h
    | exact DREBPost.pure (on_attestation_chainsInPool _ _ (h.of_S rfl))
    | exact DREBPost.pure (h.of_S rfl)
    | refine DREBPost.dite (fun _ => ?_) (fun _ => ?_)
    | refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
    | refine DREBPost.bind_any (fun _ => ?_)

/-- Every answer of the tick keeps `ChainsInPool`: the wake record, the clock and the tick of
the available chain leave the FG state, and the proposal and the attestation duty keep it.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `t`: the time. -/
theorem tick_chainsInPool (C : Config) (P : Provisional V) (X : External V) (n : NodeState V)
    (t : Time) (h : ChainsInPool n) :
    DREBPost (tick C P X n t) ChainsInPool := by
  obtain ⟨hS, -, -, -⟩ := record_awake_frame n t
  simp only [tick]
  refine DREBPost.bind_any (fun A' => ?_)
  have hq : ChainsInPool { { record_awake n t with t := t } with A := A' } := h.of_S hS
  refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
  · refine DREBPost.bind (propose_block_chainsInPool C P X _ hq) (fun n₄ h₄ => ?_)
    refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
    · exact DREBPost.bind (attest_chainsInPool C _ h₄) (fun _ h₅ => DREBPost.pure h₅)
    · exact DREBPost.pure h₄
  · refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
    · exact DREBPost.bind (attest_chainsInPool C _ hq) (fun _ h₅ => DREBPost.pure h₅)
    · exact DREBPost.pure hq

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]
variable [RootOrder]

/-- Receiving a block keeps the pool.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `B`: the block. -/
theorem on_block_pool (C : Config) (P : Provisional V) (X : External V) (n : NodeState V)
    (B : Block V) : AttPoolGrows n (on_block C P X n B) := by
  rw [on_block_eq]
  split
  · exact fg_on_block_pool C n.S B
  · exact AttPoolGrows.refl n

/-- Every answer of the proposal keeps the pool.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state. -/
theorem propose_block_pool (C : Config) (P : Provisional V) (X : External V)
    (n : NodeState V) :
    DREBPost (propose_block C P X n) (fun n' => AttPoolGrows n n') := by
  simp only [propose_block]
  repeat' first
    | exact DREBPost.pure (on_block_pool C P X n _)
    | refine DREBPost.bind_any (fun _ => ?_)

/-- Every answer of the attestation duty keeps the pool.

The variables:
- `C`: the parameters; `n`: the node state. -/
theorem attest_pool (C : Config) (n : NodeState V) :
    DREBPost (attest C n) (fun n' => AttPoolGrows n n') := by
  simp only [attest]
  repeat' first
    | exact DREBPost.pure (AttPoolGrows.refl n)
    | exact DREBPost.pure (fun a ha => (on_attestation_pool _ _).1 a ha)
    | refine DREBPost.dite (fun _ => ?_) (fun _ => ?_)
    | refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
    | refine DREBPost.bind_any (fun _ => ?_)

/-- Every answer of the tick keeps the pool: the wake record, the clock and the tick of the
available chain leave the FG state, and the proposal and the attestation duty keep the pool.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `t`: the time. -/
theorem tick_pool (C : Config) (P : Provisional V) (X : External V) (n : NodeState V)
    (t : Time) :
    DREBPost (tick C P X n t) (fun n' => AttPoolGrows n n') := by
  obtain ⟨hS, -, -, -⟩ := record_awake_frame n t
  simp only [tick]
  refine DREBPost.bind_any (fun A' => ?_)
  have hq : AttPoolGrows n { { record_awake n t with t := t } with A := A' } :=
    AttPoolGrows.of_S hS
  refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
  · refine DREBPost.bind ((propose_block_pool C P X _).mono (fun _ h => hq.trans h))
      (fun n₄ h₄ => ?_)
    refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
    · exact DREBPost.bind ((attest_pool C _).mono (fun _ h => h₄.trans h))
        (fun _ h₅ => DREBPost.pure h₅)
    · exact DREBPost.pure h₄
  · refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
    · exact DREBPost.bind ((attest_pool C _).mono (fun _ h => hq.trans h))
        (fun _ h₅ => DREBPost.pure h₅)
    · exact DREBPost.pure hq

end

section

open GoldilocksCorrectness.Statements.Routines (chainStateOf)
open GoldilocksCorrectness.Statements.Routines (ChainStatesComputed)

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- `CachesFrom C H OnChain n n'`: `n'`'s tree holds `n`'s, and when every block of `n'`'s tree
satisfies `JustifiedOnChainWith`, `CachesOnChainWith` passes from `n`'s FG state to `n'`'s.

The variables:
- `C`: the parameters; `H`: the threshold; `OnChain`: the set of blocks; `n`, `n'`: the two node
  states. -/
def CachesFrom (C : Config) (H : ℕ) (OnChain : Block V → Prop) (n n' : NodeState V) : Prop :=
  n.S.T ⊆ n'.S.T ∧
    ((∀ B ∈ n'.S.T, JustifiedOnChainWith C H OnChain B) →
      CachesOnChainWith C H OnChain n.S → CachesOnChainWith C H OnChain n'.S)

omit [RootOrder] in
/-- A node state is related to itself. -/
theorem cachesFrom_refl (C : Config) (H : ℕ) (OnChain : Block V → Prop) (n : NodeState V) :
    CachesFrom C H OnChain n n :=
  ⟨Finset.Subset.refl _, fun _ h => h⟩

omit [RootOrder] in
/-- `CachesFrom` is transitive. -/
theorem cachesFrom_trans (C : Config) (H : ℕ) (OnChain : Block V → Prop) {n n' n'' : NodeState V}
    (h : CachesFrom C H OnChain n n') (h' : CachesFrom C H OnChain n' n'') :
    CachesFrom C H OnChain n n'' :=
  ⟨h.1.trans h'.1, fun hB hc => h'.2 hB (h.2 (fun B hB' => hB B (h'.1 hB')) hc)⟩

omit [RootOrder] in
/-- A routine that keeps the tree, the justified block, the justification height and the
finalized block relates its input to its output. -/
theorem cachesFrom_of_frame (C : Config) (H : ℕ) (OnChain : Block V → Prop) {n n' : NodeState V}
    (hT : n'.S.T = n.S.T) (hJ : n'.S.J = n.S.J) (hhj : n'.S.h_j = n.S.h_j)
    (hF : n'.S.F = n.S.F) : CachesFrom C H OnChain n n' := by
  refine ⟨by rw [hT], fun _ hc => ?_⟩
  unfold CachesOnChainWith at hc ⊢
  rw [hJ, hhj, hF]
  exact hc

/-- **Kit fact, receiving a block.** From a node state whose chain states of its tree are the
blocks' own, receiving a block relates the node state to the result: a refused block changes
nothing; an accepted block enters the tree, and its chain state, computed from its parent's, is
its own.

The variables:
- `C`, `P`, `X`: the parameters and the values; `H`: the threshold; `OnChain`: the set of blocks;
  `n`: the node state; `B`: the block. -/
theorem on_block_cachesFrom (C : Config) (P : Provisional V) (X : External V) (H : ℕ)
    (OnChain : Block V → Prop) (n : NodeState V) (B : Block V)
    -- the chain states of `n`'s tree are the blocks' own
    (hCS : ChainStatesComputed C n.S) :
    CachesFrom C H OnChain n (on_block C P X n B) := by
  rw [on_block_eq]
  by_cases hb : block_admissible C P X n B = true
  swap
  · rw [if_neg hb]; exact cachesFrom_refl C H OnChain n
  rw [if_pos hb]
  obtain ⟨-, -, hpar, -, -, hslot, -⟩ := block_admissible_facts C P X n B hb
  obtain ⟨hT', -, -⟩ := fg_on_block_eq C n.S B
  have hBT : B ∈ (fg_on_block C n.S B).T := by
    rw [hT']; exact Finset.mem_union_right _ (Finset.mem_singleton_self B)
  refine ⟨?_, fun hB hc => ?_⟩
  · show n.S.T ⊆ (fg_on_block C n.S B).T
    rw [hT']
    exact Finset.subset_union_left
  · have hst : state_transition C (n.S.σ B.parent) B = chainStateOf C B := by
      rw [hCS B.parent hpar]
      cases B with
      | genesis =>
          simp only [Block.parent, Block.slot] at hslot
          exact absurd hslot (lt_irrefl _)
      | node p s r votes support ats v => rfl
    refine fg_on_block_cachesOnChainWith C H OnChain n.S B hc ?_
    rw [hst]
    exact hB B hBT

omit [Fintype V] [RootOrder] in
/-- Receiving an attestation keeps the tree, the justified block, the justification height and
the finalized block.

The variables:
- `n`: the node state; `a`: the attestation. -/
theorem on_attestation_caches (n : NodeState V) (a : Attestation V) :
    (on_attestation n a).S.T = n.S.T ∧ (on_attestation n a).S.J = n.S.J ∧
      (on_attestation n a).S.h_j = n.S.h_j ∧ (on_attestation n a).S.F = n.S.F := by
  simp only [on_attestation, fg_on_attestation, Id.run]
  split
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · split <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- Every answer of the attestation duty keeps the tree, the justified block, the justification
height and the finalized block.

The variables:
- `C`: the parameters; `n`: the node state. -/
theorem attest_caches (C : Config) (n : NodeState V) :
    DREBPost (attest C n) (fun n' => n'.S.T = n.S.T ∧ n'.S.J = n.S.J ∧ n'.S.h_j = n.S.h_j ∧
      n'.S.F = n.S.F) := by
  simp only [attest]
  repeat' first
    | exact DREBPost.pure ⟨rfl, rfl, rfl, rfl⟩
    | exact DREBPost.pure (on_attestation_caches _ _)
    | refine DREBPost.dite (fun _ => ?_) (fun _ => ?_)
    | refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
    | refine DREBPost.bind_any (fun _ => ?_)

/-- Every answer of the proposal, from a node state whose chain states of its tree are the blocks'
own, relates the node state to the answer: it ends by receiving the proposed block.

The variables:
- `C`, `P`, `X`: the parameters and the values; `H`: the threshold; `OnChain`: the set of blocks;
  `n`: the node state. -/
theorem propose_block_cachesFrom (C : Config) (P : Provisional V) (X : External V) (H : ℕ)
    (OnChain : Block V → Prop) (n : NodeState V)
    -- the chain states of `n`'s tree are the blocks' own
    (hCS : ChainStatesComputed C n.S) :
    DREBPost (propose_block C P X n) (fun n' => CachesFrom C H OnChain n n') := by
  simp only [propose_block]
  repeat' first
    | exact DREBPost.pure (on_block_cachesFrom C P X H OnChain n _ hCS)
    | refine DREBPost.bind_any (fun _ => ?_)

/-- Every answer of the node's tick, from a node state whose chain states of its tree are the
blocks' own, relates the node state to the answer: the wake record, the clock and the tick of the
available chain keep the FG state, the proposal receives its own block, and the attestation keeps
the caches.

The variables:
- `C`, `P`, `X`: the parameters and the values; `H`: the threshold; `OnChain`: the set of blocks;
  `n`: the node state; `t`: the time. -/
theorem tick_cachesFrom (C : Config) (P : Provisional V) (X : External V) (H : ℕ)
    (OnChain : Block V → Prop) (n : NodeState V) (t : Time)
    -- the chain states of `n`'s tree are the blocks' own
    (hCS : ChainStatesComputed C n.S) :
    DREBPost (tick C P X n t) (fun n' => CachesFrom C H OnChain n n') := by
  obtain ⟨hS, -, -, -⟩ := record_awake_frame n t
  simp only [tick]
  refine DREBPost.bind_any (fun A' => ?_)
  have hq : CachesFrom C H OnChain n { { record_awake n t with t := t } with A := A' } :=
    cachesFrom_of_frame C H OnChain (congrArg FGState.T hS) (congrArg FGState.J hS)
      (congrArg FGState.h_j hS) (congrArg FGState.F hS)
  have hCS₁ : ChainStatesComputed C
      ({ { record_awake n t with t := t } with A := A' } : NodeState V).S := by
    show ChainStatesComputed C (record_awake n t).S
    rw [hS]
    exact hCS
  refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
  · refine DREBPost.bind (P := fun n' => CachesFrom C H OnChain n n')
      ((propose_block_cachesFrom C P X H OnChain _ hCS₁).mono
        (fun _ h' => cachesFrom_trans C H OnChain hq h')) (fun n₄ h₄ => ?_)
    refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
    · exact DREBPost.bind (attest_caches C n₄) (fun _ h₅ =>
        DREBPost.pure (cachesFrom_trans C H OnChain h₄
          (cachesFrom_of_frame C H OnChain h₅.1 h₅.2.1 h₅.2.2.1 h₅.2.2.2)))
    · exact DREBPost.pure h₄
  · refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
    · exact DREBPost.bind (attest_caches C _) (fun _ h₅ =>
        DREBPost.pure (cachesFrom_trans C H OnChain hq
          (cachesFrom_of_frame C H OnChain h₅.1 h₅.2.1 h₅.2.2.1 h₅.2.2.2)))
    · exact DREBPost.pure hq

end

end

section

open GoldilocksCorrectness.Statements.Routines (confirmedOf)

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

omit [Fintype V] [RootOrder] in
/-- The confirmed tip of `n` is an ancestor of, or equal to, that of `n'`, when `n`'s finalized
block is an ancestor of, or equal to, `n'`'s; `n'`'s record is a block of its tree compatible
with its finalized block; and `n`'s record is an ancestor of, or equal to, `n'`'s finalized block
or `n'`'s record.

Why: `n'`'s confirmed tip is a descendant of, or equal to, both `n'`'s finalized block and `n'`'s
record: it is the record when the finalized block is an ancestor of it or itself, and otherwise
the finalized block, of which the record, compatible with it, is then an ancestor. `n`'s
confirmed tip is `n`'s record or `n`'s finalized block.

The variables:
- `n`, `n'`: the two node states. -/
theorem confirmedOf_ancestorEq_of {n n' : NodeState V}
    -- `n`'s finalized block is an ancestor of, or equal to, `n'`'s
    (hFF : n.S.F.AncestorEq n'.S.F)
    -- `n'`'s record is a block of its tree
    (hL'T : n'.A.latest_confirmed ∈ n'.S.T)
    -- `n'`'s record is compatible with its finalized block
    (hL'F' : n'.A.latest_confirmed.compatible n'.S.F = true)
    -- `n`'s record is an ancestor of, or equal to, `n'`'s finalized block or `n'`'s record
    (hkey : n.A.latest_confirmed.AncestorEq n'.S.F ∨
      n.A.latest_confirmed.AncestorEq n'.A.latest_confirmed) :
    (confirmedOf n).AncestorEq (confirmedOf n') := by
  have hc' : n'.S.F.AncestorEq (confirmedOf n') ∧
      n'.A.latest_confirmed.AncestorEq (confirmedOf n') := by
    rcases ac_confirmed_cases n'.A (fg_to_ac n'.S) with ⟨hin, h⟩ | ⟨hout, h⟩
    · show n'.S.F.AncestorEq (ac_confirmed n'.A (fg_to_ac n'.S)) ∧
        n'.A.latest_confirmed.AncestorEq (ac_confirmed n'.A (fg_to_ac n'.S))
      rw [h]
      exact ⟨((mem_fg_to_ac_tree _ _).1 hin).2, ancestorEq_refl _⟩
    · show n'.S.F.AncestorEq (ac_confirmed n'.A (fg_to_ac n'.S)) ∧
        n'.A.latest_confirmed.AncestorEq (ac_confirmed n'.A (fg_to_ac n'.S))
      rw [h]
      refine ⟨ancestorEq_refl _, ?_⟩
      rcases (compatible_iff _ _).1 hL'F' with h1 | h1
      · exact h1
      · exact absurd ((mem_fg_to_ac_tree _ _).2 ⟨hL'T, h1⟩) hout
  rcases ac_confirmed_cases n.A (fg_to_ac n.S) with ⟨-, h⟩ | ⟨-, h⟩
  · show (ac_confirmed n.A (fg_to_ac n.S)).AncestorEq (confirmedOf n')
    rw [h]
    rcases hkey with h1 | h1
    · exact ancestorEq_trans h1 hc'.1
    · exact ancestorEq_trans h1 hc'.2
  · show (ac_confirmed n.A (fg_to_ac n.S)).AncestorEq (confirmedOf n')
    rw [h]
    exact ancestorEq_trans hFF hc'.1

end

end

section

open GoldilocksCorrectness.Statements.Routines (chainStateOf)

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- `ReachFrom C D n n'`: `n'`'s tree holds `n`'s, `n'`'s finalized block is `n`'s or a descendant
of it, and when `D` enters the tree from `n` to `n'` and `n`'s FG state is `ReadyFor` `D`, `n'`'s
finalized block is `D`'s or a descendant of it.

The variables:
- `C`: the parameters; `D`: the block; `n`, `n'`: the two node states. -/
def ReachFrom (C : Config) (D : Block V) (n n' : NodeState V) : Prop :=
  n.S.T ⊆ n'.S.T ∧ n.S.F.AncestorEq n'.S.F ∧
    (D ∉ n.S.T → D ∈ n'.S.T → ReadyFor C D n.S → (chainStateOf C D).F.AncestorEq n'.S.F)

omit [RootOrder] in
theorem reachFrom_of_frame (C : Config) (D : Block V) {n n' : NodeState V}
    (hT : n'.S.T = n.S.T) (hF : n'.S.F = n.S.F) : ReachFrom C D n n' := by
  refine ⟨by rw [hT], by rw [hF]; exact ancestorEq_refl _, fun h1 h2 _ => ?_⟩
  rw [hT] at h2
  exact absurd h2 h1

omit [RootOrder] in
theorem reachFrom_frame_trans (C : Config) (D : Block V) {n n₁ n₂ : NodeState V}
    (h₁ : n₁.S = n.S) (h : ReachFrom C D n₁ n₂) : ReachFrom C D n n₂ := by
  obtain ⟨h1, h2, h3⟩ := h
  rw [h₁] at h1 h2 h3
  exact ⟨h1, h2, h3⟩

omit [RootOrder] in
theorem reachFrom_trans_frame (C : Config) (D : Block V) {n n₁ n₂ : NodeState V}
    (h : ReachFrom C D n n₁) (hT : n₂.S.T = n₁.S.T) (hF : n₂.S.F = n₁.S.F) :
    ReachFrom C D n n₂ := by
  obtain ⟨h1, h2, h3⟩ := h
  rw [← hT, ← hF] at *
  exact ⟨h1, h2, h3⟩

end

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]

/-- `TreeGrows n n'`: `n'`'s tree holds `n`'s; `n`'s finalized block is an ancestor of `n'`'s, or
`n'`'s; for every slot, `n`'s Goldfish votes of that slot are a prefix of `n'`'s; every block of
`n`'s tree has the same stamp in `n'`; and every vote of `n`'s pool has the same stamp in `n'`.

The variables:
- `n`, `n'`: the two node states.

Read aloud: `n'` holds every block and vote `n` holds, with the same stamps, and its finalized
block is `n`'s or a descendant of it. -/
def TreeGrows (n n' : NodeState V) : Prop :=
  n.S.T ⊆ n'.S.T ∧ n.S.F.AncestorEq n'.S.F ∧ (∀ s : Slot, n.A.gf_votes s <+: n'.A.gf_votes s) ∧
    (∀ B ∈ n.S.T, n'.A.timestamp_block B = n.A.timestamp_block B) ∧
    ∀ s : Slot, ∀ vote ∈ n.A.gf_votes s, n'.A.timestamp_vote vote = n.A.timestamp_vote vote

omit [Fintype V] in
/-- A node state holds its own blocks, votes and stamps. -/
theorem TreeGrows.refl (n : NodeState V) : TreeGrows n n :=
  ⟨Finset.Subset.refl _, ancestorEq_refl _, fun _ => List.prefix_refl _, fun _ _ => rfl,
    fun _ _ _ => rfl⟩

omit [Fintype V] in
/-- `TreeGrows` is transitive. -/
theorem TreeGrows.trans {n n' n'' : NodeState V} (h : TreeGrows n n') (h' : TreeGrows n' n'') :
    TreeGrows n n'' := by
  obtain ⟨hT, hF, hV, hB, hS⟩ := h
  obtain ⟨hT', hF', hV', hB', hS'⟩ := h'
  refine ⟨hT.trans hT', ancestorEq_trans hF hF', fun s => (hV s).trans (hV' s),
    fun B hBT => ?_, fun s vote hv => ?_⟩
  · rw [hB' B (hT hBT), hB B hBT]
  · rw [hS' s vote ((hV s).subset hv), hS s vote hv]

omit [Fintype V] in
/-- `TreeGrows` from a node state to one with the same FG state and block stamps, and an AC state
that holds the first's votes and stamps. -/
theorem TreeGrows.of_ac {n n' : NodeState V} (hS : n'.S = n.S)
    (hTB : n'.A.timestamp_block = n.A.timestamp_block) (hA : ACGrows n.A n'.A) :
    TreeGrows n n' := by
  refine ⟨by rw [hS], by rw [hS]; exact ancestorEq_refl _, hA.1, fun B _ => by rw [hTB], hA.2⟩

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- `StampsAt` composes along `TreeGrows` when the clock is kept: what `n''` holds beyond `n` is
beyond `n` in `n'`, stamped `n'.t` there and kept, or beyond `n'` in `n''`. -/
theorem StampsAt.trans {n n' n'' : NodeState V} (h : StampsAt n n') (hg : TreeGrows n' n'')
    (h' : StampsAt n' n'') (ht : n''.t = n'.t) : StampsAt n n'' := by
  refine ⟨fun B hB hn => ?_, ?_⟩
  · by_cases hB' : B ∈ n'.S.T
    · rw [hg.2.2.2.1 B hB', ht]
      exact h.1 B hB' hn
    · exact h'.1 B hB hB'
  · rw [ht]
    exact h.2.trans ⟨hg.2.2.1, hg.2.2.2.2⟩ (ht ▸ h'.2)

/-- The facts a routine keeps along a tick, from the node state `n₀`, at the time `τ`: the pool
filed by slot, `TreeGrows n₀ n'`, `StampsAt n₀ n'`, and the clock `τ`.

The variables:
- `n₀`: the node state the tick started from; `τ`: the time; `n'`: the node state reached.

Read aloud: `n'` is `n₀` grown, with what it holds beyond `n₀` stamped `τ`, at the clock `τ`. -/
def StepFrom (n₀ : NodeState V) (τ : Time) (n' : NodeState V) : Prop :=
  SlotKeyed n'.A ∧ TreeGrows n₀ n' ∧ StampsAt n₀ n' ∧ n'.t = τ

omit [Fintype V] in
/-- `StepFrom` composes: a step from `n` at its own clock, after a step from `n₀` to `n` at `τ`,
is a step from `n₀` at `τ`. -/
theorem StepFrom.trans {n₀ n n' : NodeState V} {τ : Time} (h : StepFrom n₀ τ n)
    (h' : StepFrom n n.t n') : StepFrom n₀ τ n' := by
  obtain ⟨-, hg, hs, ht⟩ := h
  obtain ⟨hk', hg', hs', ht'⟩ := h'
  exact ⟨hk', hg.trans hg', hs.trans hg' hs' ht', ht'.trans ht⟩

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]

section

variable [RootOrder]

omit [Fintype V] [RootOrder] in
/-- Receiving a Goldfish vote is a step from the node state at its clock: a vote it adds is
stamped with the clock.

The variables:
- `C`, `P`: the parameters and the values; `n`: the node state; `vote`: the vote. -/
theorem on_ac_message_step (C : Config) (P : Provisional V) (n : NodeState V)
    (vote : GoldfishVote V) (hk : SlotKeyed n.A) : StepFrom n n.t (on_ac_message C P n vote) := by
  have he : on_ac_message C P n vote = { n with A := on_goldfish_vote C P n.A n.t vote } := rfl
  rw [he]
  obtain ⟨k1, k2, k3, k4⟩ := on_goldfish_vote_grows C P n.A n.t vote hk
  exact ⟨k1, TreeGrows.of_ac rfl k3 k2, ⟨fun _ hB hn => absurd hB hn, k4⟩, rfl⟩

end

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- Receiving an attestation keeps the pool filed by slot and grows the node state: it writes the
FG state's pool of attestations only.

The variables:
- `n`: the node state; `a`: the attestation. -/
theorem on_attestation_grows (n : NodeState V) (a : Attestation V) (hk : SlotKeyed n.A) :
    SlotKeyed (on_attestation n a).A ∧ TreeGrows n (on_attestation n a) := by
  simp only [on_attestation, Id.run]
  split
  · exact ⟨hk, TreeGrows.refl n⟩
  · obtain ⟨h1, -, h3⟩ := fg_on_attestation_keeps n.S a
    refine ⟨hk, ?_, ?_, fun _ => List.prefix_refl _, fun _ _ => rfl, fun _ _ _ => rfl⟩
    · show n.S.T ⊆ (fg_on_attestation n.S a).T
      rw [h1]
    · show n.S.F.AncestorEq (fg_on_attestation n.S a).F
      rw [h3]
      exact ancestorEq_refl _

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- Receiving an attestation is a step from the node state at its clock: it adds no block and no
vote.

The variables:
- `n`: the node state; `a`: the attestation. -/
theorem on_attestation_step (n : NodeState V) (a : Attestation V) (hk : SlotKeyed n.A) :
    StepFrom n n.t (on_attestation n a) := by
  obtain ⟨hk', hg⟩ := on_attestation_grows n a hk
  obtain ⟨hT, hA, ht⟩ := on_attestation_frame n a
  refine ⟨hk', hg, ⟨fun B hB hn => absurd (hT ▸ hB) hn, ?_⟩, ht⟩
  rw [hA, ht]
  exact ACStampsAt.refl n.A n.t

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]

section

variable [RootOrder]

/-- Every answer of the attestation duty is a step from the node state at its clock: it writes the
anti-slashing record, and may receive its own attestation.

The variables:
- `C`: the parameters; `n`: the node state. -/
theorem attest_step (C : Config) (n : NodeState V) (hk : SlotKeyed n.A) :
    DREBPost (attest C n) (StepFrom n n.t) := by
  simp only [attest]
  repeat' first
    | exact DREBPost.pure ⟨hk, TreeGrows.refl n, StampsAt.refl n, rfl⟩
    | exact DREBPost.pure (on_attestation_step _ _ (by exact hk))
    | refine DREBPost.dite (fun _ => ?_) (fun _ => ?_)
    | refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
    | refine DREBPost.bind_any (fun _ => ?_)

/-- The attestation duty keeps "a step from `n₀` at `τ`". -/
theorem attest_step_from {C : Config} {n₀ : NodeState V} {τ : Time} (n : NodeState V)
    (h : StepFrom n₀ τ n) : DREBPost (attest C n) (StepFrom n₀ τ) :=
  (attest_step C n h.1).mono (fun _ h' => h.trans h')

end

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]

section

variable [RootOrder]

/-- Receiving a block keeps the pool filed by slot and grows the node state. A refused block
changes nothing. An accepted block enters the tree, moves the finalized block only to a
descendant, admits the block's votes, and stamps the block, which was not in the tree, so no stamp
of a block of the tree is rewritten.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `B`: the block. -/
theorem on_block_grows (C : Config) (P : Provisional V) (X : External V) (n : NodeState V)
    (B : Block V) (hk : SlotKeyed n.A) :
    SlotKeyed (on_block C P X n B).A ∧ TreeGrows n (on_block C P X n B) := by
  rw [on_block_eq]
  by_cases hb : block_admissible C P X n B = true
  swap
  · rw [if_neg hb]; exact ⟨hk, TreeGrows.refl n⟩
  rw [if_pos hb]
  obtain ⟨-, hBT, -⟩ := block_admissible_facts C P X n B hb
  obtain ⟨hT', -, -⟩ := fg_on_block_eq C n.S B
  obtain ⟨k1, k2, k3, -⟩ := ac_on_block_grows C P n.A n.t B hk
  refine ⟨k1, ?_, fg_on_block_F C n.S B, k2.1, ?_, k2.2⟩
  · show n.S.T ⊆ (fg_on_block C n.S B).T
    rw [hT']
    exact Finset.subset_union_left
  · intro B' hB'
    show (ac_on_block C P n.A n.t B).timestamp_block B' = n.A.timestamp_block B'
    rw [k3, Function.update_apply, if_neg]
    rintro rfl
    exact hBT hB'

omit [Fintype V] [RootOrder] in
/-- Receiving a Goldfish vote keeps the pool filed by slot and grows the node state.

The variables:
- `C`, `P`: the parameters and the values; `n`: the node state; `vote`: the vote. -/
theorem on_ac_message_grows (C : Config) (P : Provisional V) (n : NodeState V)
    (vote : GoldfishVote V) (hk : SlotKeyed n.A) :
    SlotKeyed (on_ac_message C P n vote).A ∧ TreeGrows n (on_ac_message C P n vote) := by
  have he : on_ac_message C P n vote = { n with A := on_goldfish_vote C P n.A n.t vote } := rfl
  rw [he]
  obtain ⟨k1, k2, k3, -⟩ := on_goldfish_vote_grows C P n.A n.t vote hk
  exact ⟨k1, TreeGrows.of_ac rfl k3 k2⟩

/-- Every answer of the proposal keeps the pool filed by slot and grows the node state: it ends by
receiving the proposed block.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state. -/
theorem propose_block_grows (C : Config) (P : Provisional V) (X : External V)
    (n : NodeState V) (hk : SlotKeyed n.A) :
    DREBPost (propose_block C P X n) (fun n' => SlotKeyed n'.A ∧ TreeGrows n n') := by
  simp only [propose_block]
  repeat' first
    | exact DREBPost.pure (on_block_grows C P X n _ hk)
    | refine DREBPost.bind_any (fun _ => ?_)

/-- Every answer of the attestation duty keeps the pool filed by slot and grows the node state: it
writes the anti-slashing record, and may receive its own attestation.

The variables:
- `C`: the parameters; `n`: the node state. -/
theorem attest_grows (C : Config) (n : NodeState V) (hk : SlotKeyed n.A) :
    DREBPost (attest C n) (fun n' => SlotKeyed n'.A ∧ TreeGrows n n') := by
  simp only [attest]
  repeat' first
    | exact DREBPost.pure ⟨hk, TreeGrows.refl n⟩
    | exact DREBPost.pure (on_attestation_grows _ _ (by exact hk))
    | refine DREBPost.dite (fun _ => ?_) (fun _ => ?_)
    | refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
    | refine DREBPost.bind_any (fun _ => ?_)

/-- The proposal keeps "filed by slot, and grown from `n₀`". -/
theorem propose_block_grows_from {C : Config} {P : Provisional V} {X : External V}
    {n₀ : NodeState V} (n : NodeState V) (h : SlotKeyed n.A ∧ TreeGrows n₀ n) :
    DREBPost (propose_block C P X n) (fun n' => SlotKeyed n'.A ∧ TreeGrows n₀ n') :=
  (propose_block_grows C P X n h.1).mono (fun _ h' => ⟨h'.1, h.2.trans h'.2⟩)

/-- The attestation duty keeps "filed by slot, and grown from `n₀`". -/
theorem attest_grows_from {C : Config} {n₀ : NodeState V} (n : NodeState V)
    (h : SlotKeyed n.A ∧ TreeGrows n₀ n) :
    DREBPost (attest C n) (fun n' => SlotKeyed n'.A ∧ TreeGrows n₀ n') :=
  (attest_grows C n h.1).mono (fun _ h' => ⟨h'.1, h.2.trans h'.2⟩)

/-- Every answer of the node's tick keeps the pool filed by slot and grows the node state: the
wake record and the clock write no field `TreeGrows` reads, the tick of the available chain holds
the pool's votes and stamps and keeps the block stamps, and the proposal and the attestation each
grow the node state.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `t`: the time. -/
theorem tick_grows (C : Config) (P : Provisional V) (X : External V) (n : NodeState V)
    (t : Time) (hk : SlotKeyed n.A) :
    DREBPost (tick C P X n t) (fun n' => SlotKeyed n'.A ∧ TreeGrows n n') := by
  obtain ⟨hS, hA, -, -⟩ := record_awake_frame n t
  have hk' : SlotKeyed (record_awake n t).A := by rw [hA]; exact hk
  simp only [tick]
  refine DREBPost.bind (ac_on_tick_grows C P _ _ t _ _ _ hk') (fun A' hA' => ?_)
  have hg : ACGrows n.A A' := by
    have h := hA'.2.1
    rw [hA] at h
    exact h
  have htb : A'.timestamp_block = n.A.timestamp_block := by
    rw [hA'.2.2.1, hA]
  have hq : SlotKeyed ({ { record_awake n t with t := t } with A := A' } : NodeState V).A ∧
      TreeGrows n { { record_awake n t with t := t } with A := A' } :=
    ⟨hA'.1, TreeGrows.of_ac hS htb hg⟩
  -- the proposal, when it runs, then the attestation, when it runs
  refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
  · refine DREBPost.bind (propose_block_grows_from _ hq) (fun n₄ h₄ => ?_)
    refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
    · exact DREBPost.bind (attest_grows_from _ h₄) (fun _ h₅ => DREBPost.pure h₅)
    · exact DREBPost.pure h₄
  · refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
    · exact DREBPost.bind (attest_grows_from _ hq) (fun _ h₅ => DREBPost.pure h₅)
    · exact DREBPost.pure hq

end

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]

section

variable [RootOrder]

/-- Receiving a block is a step from the node state at its clock: an accepted block, which was not
in the tree, is stamped with the clock, and so is every vote it adds.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `B`: the block. -/
theorem on_block_step (C : Config) (P : Provisional V) (X : External V) (n : NodeState V)
    (B : Block V) (hk : SlotKeyed n.A) : StepFrom n n.t (on_block C P X n B) := by
  have hg := on_block_grows C P X n B hk
  rw [on_block_eq] at hg ⊢
  by_cases hb : block_admissible C P X n B = true
  swap
  · rw [if_neg hb]; exact ⟨hk, TreeGrows.refl n, StampsAt.refl n, rfl⟩
  rw [if_pos hb] at hg ⊢
  obtain ⟨-, hBT, -⟩ := block_admissible_facts C P X n B hb
  obtain ⟨hT', -, -⟩ := fg_on_block_eq C n.S B
  obtain ⟨-, -, k3, k4⟩ := ac_on_block_grows C P n.A n.t B hk
  refine ⟨hg.1, hg.2, ⟨fun B' hB' hn => ?_, k4⟩, rfl⟩
  show (ac_on_block C P n.A n.t B).timestamp_block B' = some (n.t : Stamp)
  change B' ∈ (fg_on_block C n.S B).T at hB'
  rw [hT'] at hB'
  rcases Finset.mem_union.mp hB' with h | h
  · exact absurd h hn
  · rw [Finset.mem_singleton.mp h, k3, Function.update_self]

/-- Every answer of the proposal is a step from the node state at its clock: it ends by receiving
the proposed block.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state. -/
theorem propose_block_step (C : Config) (P : Provisional V) (X : External V) (n : NodeState V)
    (hk : SlotKeyed n.A) : DREBPost (propose_block C P X n) (StepFrom n n.t) := by
  simp only [propose_block]
  repeat' first
    | exact DREBPost.pure (on_block_step C P X n _ hk)
    | refine DREBPost.bind_any (fun _ => ?_)

/-- The proposal keeps "a step from `n₀` at `τ`". -/
theorem propose_block_step_from {C : Config} {P : Provisional V} {X : External V}
    {n₀ : NodeState V} {τ : Time} (n : NodeState V) (h : StepFrom n₀ τ n) :
    DREBPost (propose_block C P X n) (StepFrom n₀ τ) :=
  (propose_block_step C P X n h.1).mono (fun _ h' => h.trans h')

/-- Every answer of the node's tick at the time `t` is a step from the node state at `t`: the
tick sets the clock to `t` first, and every block and vote it adds is stamped `t`.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `t`: the time. -/
theorem tick_step (C : Config) (P : Provisional V) (X : External V) (n : NodeState V)
    (t : Time) (hk : SlotKeyed n.A) : DREBPost (tick C P X n t) (StepFrom n t) := by
  obtain ⟨hS, hA, -, -⟩ := record_awake_frame n t
  have hk' : SlotKeyed (record_awake n t).A := by rw [hA]; exact hk
  simp only [tick]
  refine DREBPost.bind (ac_on_tick_grows C P _ _ t _ _ _ hk') (fun A' hA' => ?_)
  have hg : ACGrows n.A A' := by
    have h := hA'.2.1
    rw [hA] at h
    exact h
  have htb : A'.timestamp_block = n.A.timestamp_block := by
    rw [hA'.2.2.1, hA]
  have hst : ACStampsAt n.A A' t := by
    have h := hA'.2.2.2
    rw [hA] at h
    exact h
  have hq : StepFrom n t { { record_awake n t with t := t } with A := A' } := by
    refine ⟨hA'.1, TreeGrows.of_ac hS htb hg, ⟨fun B hB hn => ?_, hst⟩, rfl⟩
    have hB' : B ∈ (record_awake n t).S.T := hB
    rw [hS] at hB'
    exact absurd hB' hn
  -- the proposal, when it runs, then the attestation, when it runs
  refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
  · refine DREBPost.bind (propose_block_step_from _ hq) (fun n₄ h₄ => ?_)
    refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
    · exact DREBPost.bind (attest_step_from _ h₄) (fun _ h₅ => DREBPost.pure h₅)
    · exact DREBPost.pure h₄
  · refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
    · exact DREBPost.bind (attest_step_from _ hq) (fun _ h₅ => DREBPost.pure h₅)
    · exact DREBPost.pure hq

end

end

section

open GoldilocksCorrectness.Statements.Routines (NodeInv)
open GoldilocksCorrectness.Statements.Routines (PoolStamped)

section

open Goldilocks
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn)
variable {V : Type} [DecidableEq V] [Fintype V]

section

variable [RootOrder]

omit [RootOrder] in
/-- On a node state satisfying `NodeInv`, no two blocks of the tree of the frame `fg_to_ac n.S`
share a root.

The variables:
- `C`: the configuration; `P`: the provisional parameters; `X`: the digest; `n`: the node
  state. -/
theorem nodeInv_frameRoots {C : Config} {P : Provisional V} {X : External V} {n : NodeState V}
    (h : NodeInv C P X n) : RootsNameBlocksIn (fg_to_ac n.S).tree :=
  fun B hB B' hB' hr => h.2.2.2.2.2.2.2.2.2.1.1 B ((mem_fg_to_ac_tree _ _).1 hB).1 B'
    ((mem_fg_to_ac_tree _ _).1 hB').1 hr

omit [RootOrder] in
/-- On a node state satisfying `NodeInv`, every block of the tree of the frame `fg_to_ac n.S` is
stamped.

The variables:
- `C`: the configuration; `P`: the provisional parameters; `X`: the digest; `n`: the node
  state. -/
theorem nodeInv_frameStamped {C : Config} {P : Provisional V} {X : External V} {n : NodeState V}
    (h : NodeInv C P X n) : ∀ H ∈ (fg_to_ac n.S).tree, n.A.timestamp_block H ≠ none :=
  fun H hH => h.2.2.2.2.1 H ((mem_fg_to_ac_tree _ _).1 hH).1

omit [RootOrder] in
/-- On a node state satisfying `NodeInv`, every vote of the pool is stamped.

The variables:
- `C`: the configuration; `P`: the provisional parameters; `X`: the digest; `n`: the node
  state. -/
theorem nodeInv_poolStamped {C : Config} {P : Provisional V} {X : External V} {n : NodeState V}
    (h : NodeInv C P X n) : PoolStamped n.A := h.2.1

end

end

end

section

open GoldilocksCorrectness.Statements.Routines (ChainStatesComputed)

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- `WitnessedFrom C n n'`: `n'`'s tree holds `n`'s, and `CachesWitnessed` passes from `n`'s FG
state to `n'`'s.

The variables:
- `C`: the parameters; `n`, `n'`: the two node states. -/
def WitnessedFrom (C : Config) (n n' : NodeState V) : Prop :=
  n.S.T ⊆ n'.S.T ∧ (CachesWitnessed C n.S → CachesWitnessed C n'.S)

omit [RootOrder] in
theorem witnessedFrom_refl (C : Config) (n : NodeState V) : WitnessedFrom C n n :=
  ⟨Finset.Subset.refl _, id⟩

omit [RootOrder] in
theorem witnessedFrom_trans (C : Config) {n n' n'' : NodeState V} (h : WitnessedFrom C n n')
    (h' : WitnessedFrom C n' n'') : WitnessedFrom C n n'' :=
  ⟨h.1.trans h'.1, fun hc => h'.2 (h.2 hc)⟩

omit [RootOrder] in
/-- A routine that keeps the tree, the justified block, the caches and the finalized block relates
its input to its output. -/
theorem witnessedFrom_of_frame (C : Config) {n n' : NodeState V} (hT : n'.S.T = n.S.T)
    (hJ : n'.S.J = n.S.J) (hj : n'.S.h_j = n.S.h_j) (hm : n'.S.h_max = n.S.h_max)
    (hF : n'.S.F = n.S.F) : WitnessedFrom C n n' := by
  refine ⟨by rw [hT], fun ⟨⟨D, hD, h1, h2⟩, ⟨X, hX, h3⟩, ⟨W, hW, h4, h5⟩⟩ => ?_⟩
  refine ⟨⟨D, hT ▸ hD, hJ ▸ h1, hj ▸ h2⟩, ⟨X, hT ▸ hX, hm ▸ h3⟩, ⟨W, hT ▸ hW, hF ▸ h4, ?_⟩⟩
  rw [hm]
  exact h5

/-- Receiving a block, from a node state whose chain states of its tree are the blocks' own,
relates the node state to the result. -/
theorem on_block_witnessedFrom (C : Config) (P : Provisional V) (X : External V)
    (n : NodeState V) (B : Block V) (hCS : ChainStatesComputed C n.S) :
    WitnessedFrom C n (on_block C P X n B) := by
  rw [on_block_eq]
  by_cases hb : block_admissible C P X n B = true
  swap
  · rw [if_neg hb]; exact witnessedFrom_refl C n
  rw [if_pos hb]
  obtain ⟨-, -, hpar, hFB, -, hslot, -⟩ := block_admissible_facts C P X n B hb
  have hg : B ≠ Block.genesis := by
    rintro rfl
    simp only [Block.parent, Block.slot] at hslot
    exact absurd hslot (lt_irrefl _)
  obtain ⟨hT', -, -⟩ := fg_on_block_eq C n.S B
  refine ⟨?_, fun hW => fg_on_block_witnessed C n.S B hCS hpar hFB hg hW⟩
  show n.S.T ⊆ (fg_on_block C n.S B).T
  rw [hT']
  exact Finset.subset_union_left

omit [Fintype V] [RootOrder] in
/-- Receiving an attestation keeps the tree, the justified block, the caches and the finalized
block. -/
theorem on_attestation_witness_keeps (n : NodeState V) (a : Attestation V) :
    (on_attestation n a).S.T = n.S.T ∧ (on_attestation n a).S.J = n.S.J ∧
      (on_attestation n a).S.h_j = n.S.h_j ∧ (on_attestation n a).S.h_max = n.S.h_max ∧
      (on_attestation n a).S.F = n.S.F := by
  simp only [on_attestation, Id.run]
  split
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · obtain ⟨h1, -, h3, h4, h5, h6⟩ := fg_on_attestation_witness_keeps n.S a
    exact ⟨h1, h3, h4, h5, h6⟩

/-- Every answer of the attestation duty keeps the tree, the justified block, the caches and the
finalized block. -/
theorem attest_witness_keeps (C : Config) (n : NodeState V) :
    DREBPost (attest C n) (fun n' => WitnessedFrom C n n') := by
  simp only [attest]
  repeat' first
    | exact DREBPost.pure (witnessedFrom_refl C _)
    | exact DREBPost.pure (witnessedFrom_of_frame C rfl rfl rfl rfl rfl)
    | exact DREBPost.pure (witnessedFrom_of_frame C (on_attestation_witness_keeps _ _).1
        (on_attestation_witness_keeps _ _).2.1 (on_attestation_witness_keeps _ _).2.2.1
        (on_attestation_witness_keeps _ _).2.2.2.1 (on_attestation_witness_keeps _ _).2.2.2.2)
    | refine DREBPost.dite (fun _ => ?_) (fun _ => ?_)
    | refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
    | refine DREBPost.bind_any (fun _ => ?_)

/-- Every answer of the proposal relates the node state to the answer. -/
theorem propose_block_witnessedFrom (C : Config) (P : Provisional V) (X : External V)
    (n : NodeState V) (hCS : ChainStatesComputed C n.S) :
    DREBPost (propose_block C P X n) (fun n' => WitnessedFrom C n n') := by
  simp only [propose_block]
  repeat' first
    | exact DREBPost.pure (on_block_witnessedFrom C P X n _ hCS)
    | refine DREBPost.bind_any (fun _ => ?_)

/-- Every answer of the node's tick relates the node state to the answer. -/
theorem tick_witnessedFrom (C : Config) (P : Provisional V) (X : External V) (n : NodeState V)
    (t : Time) (hCS : ChainStatesComputed C n.S) :
    DREBPost (tick C P X n t) (fun n' => WitnessedFrom C n n') := by
  obtain ⟨hS, -, -, -⟩ := record_awake_frame n t
  simp only [tick]
  refine DREBPost.bind_any (fun A' => ?_)
  have hq : WitnessedFrom C n { { record_awake n t with t := t } with A := A' } :=
    witnessedFrom_of_frame C (by show (record_awake n t).S.T = n.S.T; rw [hS])
      (by show (record_awake n t).S.J = n.S.J; rw [hS])
      (by show (record_awake n t).S.h_j = n.S.h_j; rw [hS])
      (by show (record_awake n t).S.h_max = n.S.h_max; rw [hS])
      (by show (record_awake n t).S.F = n.S.F; rw [hS])
  have hCS₁ : ChainStatesComputed C
      ({ { record_awake n t with t := t } with A := A' } : NodeState V).S := by
    show ChainStatesComputed C (record_awake n t).S
    rw [hS]
    exact hCS
  refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
  · refine DREBPost.bind (P := fun n' => WitnessedFrom C n n')
      ((propose_block_witnessedFrom C P X _ hCS₁).mono
        (fun _ h' => witnessedFrom_trans C hq h')) (fun n₄ h₄ => ?_)
    refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
    · exact DREBPost.bind (attest_witness_keeps C n₄) (fun _ h₅ =>
        DREBPost.pure (witnessedFrom_trans C h₄ h₅))
    · exact DREBPost.pure h₄
  · refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
    · exact DREBPost.bind (attest_witness_keeps C _) (fun _ h₅ =>
        DREBPost.pure (witnessedFrom_trans C hq h₅))
    · exact DREBPost.pure hq

end

end

section

open Goldilocks

section

variable {V : Type} [DecidableEq V] [Fintype V]

/-- `NewObjectsIn C n n' l`: every Goldfish vote `n'` holds under a slot that `n` does not hold
under it is carried by an object of the list `l`; and every block of `n'`'s tree that is not in
`n`'s is, as a block, an object of `l`, of a slot at most the slot of `n'`'s clock.

The variables:
- `C`: the parameters; `n`, `n'`: the two node states; `l`: the list of objects.

Read aloud: what `n'` holds beyond `n` is in `l`, and its new blocks are not of a later slot than
its clock's. -/
def NewObjectsIn (C : Config) (n n' : NodeState V) (l : List (NamedObject V)) : Prop :=
  (∀ s : Slot, ∀ vote ∈ n'.A.gf_votes s, vote ∉ n.A.gf_votes s → ∃ o ∈ l, Carried o vote) ∧
    ∀ B ∈ n'.S.T, B ∉ n.S.T → NamedObject.block B ∈ l ∧ B.slot ≤ C.slot n'.t

omit [DecidableEq V] [Fintype V] in
/-- A node state with the tree and the votes of `n` holds nothing beyond `n`. -/
theorem NewObjectsIn.of_same {C : Config} {n n' : NodeState V} {l : List (NamedObject V)}
    (hT : n'.S.T = n.S.T) (hV : n'.A.gf_votes = n.A.gf_votes) : NewObjectsIn C n n' l := by
  refine ⟨fun s vote hv hn => ?_, fun B hB hn => ?_⟩
  · rw [hV] at hv
    exact absurd hv hn
  · rw [hT] at hB
    exact absurd hB hn

omit [Fintype V] in
/-- `NewObjectsIn` composes when the clock is kept: what `n₂` holds beyond `n` is beyond `n` in
`n₁`, or beyond `n₁` in `n₂`. -/
theorem NewObjectsIn.trans {C : Config} {n n₁ n₂ : NodeState V} {l₁ l₂ : List (NamedObject V)}
    (h : NewObjectsIn C n n₁ l₁) (h' : NewObjectsIn C n₁ n₂ l₂) (ht : n₂.t = n₁.t) :
    NewObjectsIn C n n₂ (l₁ ++ l₂) := by
  refine ⟨fun s vote hv hn => ?_, fun B hB hn => ?_⟩
  · by_cases hv₁ : vote ∈ n₁.A.gf_votes s
    · obtain ⟨o, ho, hc⟩ := h.1 s vote hv₁ hn
      exact ⟨o, List.mem_append_left _ ho, hc⟩
    · obtain ⟨o, ho, hc⟩ := h'.1 s vote hv hv₁
      exact ⟨o, List.mem_append_right _ ho, hc⟩
  · by_cases hB₁ : B ∈ n₁.S.T
    · obtain ⟨ho, hs⟩ := h.2 B hB₁ hn
      exact ⟨List.mem_append_left _ ho, by rw [ht]; exact hs⟩
    · obtain ⟨ho, hs⟩ := h'.2 B hB hB₁
      exact ⟨List.mem_append_right _ ho, hs⟩

end

end

section

open Goldilocks

section

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- A block the node accepts is not of a slot later than the slot of the node's clock.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `B`: the block. -/
theorem block_admissible_slot [RootOrder] (C : Config) (P : Provisional V) (X : External V)
    (n : NodeState V) (B : Block V) (h : block_admissible C P X n B = true) :
    B.slot ≤ C.slot n.t := by
  simp only [block_admissible, Id.run] at h
  split at h
  · exact absurd h Bool.false_ne_true
  split at h
  · exact absurd h Bool.false_ne_true
  rename_i h2
  exact Nat.le_of_not_lt h2

end

end

section

open Goldilocks

section

variable {V : Type} [DecidableEq V] [Fintype V]
variable [RootOrder]

/-- Receiving the block `B` adds to the pool only votes of `B.votes`, adds to the tree only `B`,
of a slot at most the slot of the node's clock, and keeps the clock.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `B`: the block. -/
theorem on_block_new (C : Config) (P : Provisional V) (X : External V) (n : NodeState V)
    (B : Block V) :
    (∀ s : Slot, ∀ vote ∈ (on_block C P X n B).A.gf_votes s, vote ∉ n.A.gf_votes s →
        vote ∈ B.votes) ∧
      (∀ B' ∈ (on_block C P X n B).S.T, B' ∉ n.S.T → B' = B ∧ B.slot ≤ C.slot n.t) ∧
      (on_block C P X n B).t = n.t := by
  rw [on_block_eq]
  by_cases hb : block_admissible C P X n B = true
  swap
  · rw [if_neg hb]
    exact ⟨fun _ _ hv hn => absurd hv hn, fun _ hB hn => absurd hB hn, rfl⟩
  rw [if_pos hb]
  obtain ⟨hT', -, -⟩ := fg_on_block_eq C n.S B
  refine ⟨ac_on_block_new_votes C P n.A n.t B, fun B' hB' hn => ?_, rfl⟩
  change B' ∈ (fg_on_block C n.S B).T at hB'
  rw [hT'] at hB'
  rcases Finset.mem_union.mp hB' with h | h
  · exact absurd h hn
  · exact ⟨Finset.mem_singleton.mp h, block_admissible_slot C P X n B hb⟩

/-- Every answer of the proposal adds to the pool only votes of the block it broadcast, and to
the tree only that block, of a slot at most the slot of the node's clock, which it keeps.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state. -/
theorem propose_block_prov (C : Config) (P : Provisional V) (X : External V) (n : NodeState V) :
    DREBSpec (fun n' l => NewObjectsIn C n n' l ∧ n'.t = n.t) (propose_block C P X n) := by
  simp only [propose_block]
  refine DREBSpec.bind_liftPost (DREPost.true _) (fun p _ => ?_)
  obtain ⟨H, votes, support⟩ := p
  refine DREBSpec.broadcast_pure _ ?_
  obtain ⟨h1, h2, h3⟩ := on_block_new C P X n (Block.node H (C.slot n.t)
    (X.digest H.root (C.slot n.t) (proposal_attestations n.S H) votes support) votes support
    (proposal_attestations n.S H) n.v)
  refine ⟨⟨fun s vote hv hn => ⟨_, List.mem_singleton_self _, Or.inr ⟨_, rfl, h1 s vote hv hn⟩⟩,
    fun B hB hn => ?_⟩, h3⟩
  obtain ⟨rfl, hs⟩ := h2 B hB hn
  exact ⟨List.mem_singleton_self _, by rw [h3]; exact hs⟩

omit [Fintype V] [RootOrder] in
/-- Receiving an attestation adds nothing to the pool or the tree, and keeps the clock.

The variables:
- `C`: the parameters; `n`: the node state; `a`: the attestation; `l`: any list of objects. -/
theorem on_attestation_prov (C : Config) (n : NodeState V) (a : Attestation V)
    (l : List (NamedObject V)) :
    NewObjectsIn C n (on_attestation n a) l ∧ (on_attestation n a).t = n.t := by
  obtain ⟨hT, hA, ht⟩ := on_attestation_frame n a
  exact ⟨NewObjectsIn.of_same hT (by rw [hA]), ht⟩

/-- Every answer of the attestation duty adds nothing to the pool or the tree, and keeps the
clock.

The variables:
- `C`: the parameters; `n`: the node state. -/
theorem attest_prov (C : Config) (n : NodeState V) :
    DREBSpec (fun n' l => NewObjectsIn C n n' l ∧ n'.t = n.t) (attest C n) := by
  simp only [attest]
  repeat' first
    | exact DREBSpec.pure ⟨NewObjectsIn.of_same rfl rfl, rfl⟩
    | exact DREBSpec.broadcast_pure _ (on_attestation_prov C _ _ _)
    | refine DREBSpec.bind_liftPost (DREPost.true _) (fun _ _ => ?_)
    | refine DREBSpec.dite (fun _ => ?_) (fun _ => ?_)

/-- Every answer of the node's tick at the time `t` adds to the pool only votes carried by an
object it sent, and to the tree only blocks it sent, of a slot at most the slot of `t`; its clock
is `t`.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `t`: the time. -/
theorem tick_prov (C : Config) (P : Provisional V) (X : External V) (n : NodeState V)
    (t : Time) : DREBSpec (fun n' l => NewObjectsIn C n n' l ∧ n'.t = t) (tick C P X n t) := by
  obtain ⟨hS, hA, -, -⟩ := record_awake_frame n t
  simp only [tick]
  refine DREBSpec.bind' (ac_on_tick_prov C P _ _ t _ _ _) (fun A' l₁ h₁ => ?_)
  have hq : NewObjectsIn C n { { record_awake n t with t := t } with A := A' } l₁ ∧
      ({ { record_awake n t with t := t } with A := A' } : NodeState V).t = t := by
    refine ⟨⟨fun s vote hv hn => ⟨_, h₁ s vote hv (by
        show vote ∉ (record_awake n t).A.gf_votes s
        rw [hA]
        exact hn), Or.inl rfl⟩, fun B hB hn => ?_⟩, rfl⟩
    have hB' : B ∈ (record_awake n t).S.T := hB
    rw [hS] at hB'
    exact absurd hB' hn
  -- the proposal, when it runs, then the attestation, when it runs
  refine DREBSpec.ite (fun _ => ?_) (fun _ => ?_)
  · refine DREBSpec.bind' (propose_block_prov C P X _) (fun n₄ l₂ h₂ => ?_)
    have h₄ : NewObjectsIn C n n₄ (l₁ ++ l₂) ∧ n₄.t = t :=
      ⟨hq.1.trans h₂.1 h₂.2, h₂.2.trans hq.2⟩
    refine DREBSpec.ite (fun _ => ?_) (fun _ => ?_)
    · refine DREBSpec.bind' (attest_prov C _) (fun n₅ l₃ h₃ => DREBSpec.pure ?_)
      have h₅ := h₄.1.trans h₃.1 h₃.2
      simp only [List.append_nil, List.append_assoc] at h₅ ⊢
      exact ⟨h₅, h₃.2.trans h₄.2⟩
    · refine DREBSpec.pure ?_
      simp only [List.append_nil]
      exact h₄
  · refine DREBSpec.ite (fun _ => ?_) (fun _ => ?_)
    · refine DREBSpec.bind' (attest_prov C _) (fun n₅ l₃ h₃ => DREBSpec.pure ?_)
      have h₅ := hq.1.trans h₃.1 h₃.2
      simp only [List.append_nil] at h₅ ⊢
      exact ⟨h₅, h₃.2.trans hq.2⟩
    · refine DREBSpec.pure ⟨?_, hq.2⟩
      rw [List.append_nil]
      exact hq.1

end

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- `RecordFromSent n n' l`: every content of the record of `n'` is a content of the record of `n`,
or the content of an attestation of `l` whose validator is `n.v`.

The variables:
- `n`: the node state before; `n'`: the node state after; `l`: the objects sent between.

Read aloud: the record grows only by what was sent, by `n`'s own validator. -/
def RecordFromSent (n n' : NodeState V) (l : List (NamedObject V)) : Prop :=
  ∀ b ∈ n'.Λ.sent, b ∈ n.Λ.sent ∨
    ∃ a : Attestation V, NamedObject.attest a ∈ l ∧ a.content = b ∧ a.val_index = n.v

omit [DecidableEq V] [Fintype V] [RootOrder] in
/-- A node state with the record of `n` records only what `n` records. -/
theorem RecordFromSent.of_Λ {n n' : NodeState V} {l : List (NamedObject V)}
    (h : n'.Λ = n.Λ) : RecordFromSent n n' l := by
  intro b hb
  rw [h] at hb
  exact Or.inl hb

end

section

open GoldilocksCorrectness.Statements.Routines (TreeClosed)

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

omit [Fintype V] [RootOrder] in
/-- **Kit fact, a strict ancestor has a smaller slot.** In a tree closed under parents with every
parent of an earlier slot (`TreeClosed`), a block that is an ancestor of a block `D` of the tree,
other than `D`, has a slot less than `D`'s.

The variables:
- `P`, `X`: the values; `S`: the FG state; `B`: the ancestor; `D`: the block of the tree.

Read aloud: going back along a held chain the slots decrease. -/
theorem slot_lt_of_ancestorEq_of_treeClosed {P : Provisional V} {X : External V}
    {S : FGState V} (hTC : TreeClosed P X S) {B D : Block V}
    -- `D` is a block of the tree
    (hD : D ∈ S.T)
    -- `B` is an ancestor of `D` other than `D`
    (hBD : B.AncestorEq D) (hne : B ≠ D) :
    B.slot < D.slot := by
  induction D with
  | genesis =>
      exact absurd ((ancestorEq_genesis_iff B).1 hBD) hne
  | node p s r votes support ats v ih =>
      rcases (ancestorEq_node_iff B p s r votes support ats v).1 hBD with h | h
      · exact absurd h hne
      · obtain ⟨hpT, -, -, hps⟩ := hTC.2 _ hD (fun h' => by cases h')
        have hps' : p.slot < s := hps
        by_cases hBp : B = p
        · rw [hBp]
          exact hps'
        · have := ih hpT h hBp
          exact lt_trans this hps'

end

end

section

open Goldilocks

section

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- What the proposal sends: exactly one object, a block.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state;
- `B`: the block sent.

Read aloud: the proposal sends its block and nothing else. -/
theorem propose_block_sends (C : Config) (P : Provisional V) (X : External V)
    (n : NodeState V) :
    DREBEmits (fun l => ∃ B : Block V, l = [NamedObject.block B]) (propose_block C P X n) := by
  simp only [propose_block]
  refine DREBEmits.bind_nil (DREBEmits.liftM _)
    (fun p => ?_)
  obtain ⟨H, votes, support⟩ := p
  exact (DREBEmits.broadcast_then _ (fun _ => DREBEmits.pure rfl)).mono (fun _ hl => ⟨_, hl⟩)

/-- What the attestation duty sends: nothing, or one attestation.

The variables:
- `C`: the parameters; `n`: the node state;
- `a`: the attestation sent.

Read aloud: the attestation duty sends at most its attestation. -/
theorem attest_sends (C : Config) (n : NodeState V) :
    DREBEmits (fun l => l = [] ∨ ∃ a : Attestation V, l = [NamedObject.attest a])
      (attest C n) := by
  simp only [attest]
  repeat' first
    | exact DREBEmits.pure (Or.inl rfl)
    | refine DREBEmits.bind_nil (DREBEmits.liftM _) (fun _ => ?_)
    | refine DREBEmits.bind_nil (DREBEmits.monadLift _) (fun _ => ?_)
    | refine DREBEmits.dite (fun _ => ?_) (fun _ => ?_)
    | refine DREBEmits.ite (fun _ => ?_) (fun _ => ?_)
    | exact (DREBEmits.broadcast_then _ (fun _ => DREBEmits.pure rfl)).mono
        (fun _ hl => Or.inr ⟨_, hl⟩)

/-- What the node's tick at the time `t` appends to the objects sent: at most one Goldfish vote,
the node's own for the slot of `t`, sent at that slot's vote time.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `t`: the time. -/
theorem tick_emits (C : Config) (P : Provisional V) (X : External V) (n : NodeState V)
    (t : Time) : DREBEmits (TickVotes C n.v t) (tick C P X n t) := by
  simp only [tick]
  refine (DREBEmits.bind (L₂ := NoVote) (ac_on_tick_sends C P _ _ t _ _ _)
    (fun _ => ?_)).mono ?_
  · refine DREBEmits.ite (fun _ => ?_) (fun _ => ?_)
    · refine (DREBEmits.bind (L₂ := NoVote) (propose_block_sends C P X _)
        (fun _ => ?_)).mono (fun _ h => noVote_block_append h)
      refine DREBEmits.ite (fun _ => ?_) (fun _ => ?_)
      · exact (DREBEmits.bind (L₂ := NoVote) (attest_sends C _)
          (fun _ => DREBEmits.pure noVote_nil)).mono (fun _ h => noVote_attest_append h)
      · exact DREBEmits.pure noVote_nil
    · refine DREBEmits.ite (fun _ => ?_) (fun _ => ?_)
      · exact (DREBEmits.bind (L₂ := NoVote) (attest_sends C _)
          (fun _ => DREBEmits.pure noVote_nil)).mono (fun _ h => noVote_attest_append h)
      · exact DREBEmits.pure noVote_nil
  · intro l h
    have hv := (record_awake_frame n t).2.2.1
    have h' := tickVotes_of_append h
    rw [hv] at h'
    exact h'

/-- What the node's tick at the time `t` sends, run from nothing sent: every Goldfish vote it
sends is of the node's validator `n.v`, for the slot of `t`, and `t` is that slot's vote time; and
it sends at most one Goldfish vote.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `t`: the time;
- `n'`, `sent`: the tick's answer, the node state and the objects sent.

Read aloud: a tick votes once, as itself, for the slot of its time, and only at that slot's vote
time. -/
theorem tick_sends (C : Config) (P : Provisional V) (X : External V) (n : NodeState V)
    (t : Time) {n' : NodeState V} {sent : List (NamedObject V)}
    -- `.ok (n', sent)` is an outcome of the tick at `t`
    (h : .ok (n', sent) ∈ (tick C P X n t).outcomes) :
    (∀ vote : GoldfishVote V, NamedObject.gfVote vote ∈ sent →
        vote.val_index = n.v ∧ vote.slot = C.slot t ∧ t = C.t_ (C.slot t) + C.Δ) ∧
      (sent.filter isGfVote).length ≤ 1 := by
  exact (tick_emits C P X n t).of_outcome h

end

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- `tick_emits_proposal` of `Lemma90Inclusion.lean`, copied: a tick at the start `t` of a slot
`s > 0`, of the slot's proposer, whose wake record passes the proposal test, sends a block.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `t`: the time. -/
theorem tick_emits_proposalJ (C : Config) (P : Provisional V) (X : External V) (n : NodeState V)
    (t : Time) :
    DREBEmits (fun l => 0 < C.slot t → t = C.t_ (C.slot t) → n.v = P.proposer (C.slot t) →
        (record_awake n t).awake_since (proposal_window_start C (C.slot t)) = true →
        ∃ B : Block V, NamedObject.block B ∈ l)
      (tick C P X n t) := by
  have hv := (record_awake_frame n t).2.2.1
  simp only [tick]
  refine (DREBEmits.bind (L₂ := fun l => 0 < C.slot t → t = C.t_ (C.slot t) →
      n.v = P.proposer (C.slot t) →
      (record_awake n t).awake_since (proposal_window_start C (C.slot t)) = true →
      ∃ B : Block V, NamedObject.block B ∈ l)
    (ac_on_tick_emits_vote C P _ _ t _ _ _) (fun _ => ?_)).mono ?_
  · refine DREBEmits.ite (fun _ => ?_) (fun hc => ?_)
    · refine (DREBEmits.bind (L₂ := fun _ => True) (propose_block_sends C P X _)
        (fun _ => ?_)).mono ?_
      · refine DREBEmits.ite (fun _ => ?_) (fun _ => ?_)
        · exact (DREBEmits.bind (L₂ := fun _ => True) (attest_sends C _)
            (fun _ => DREBEmits.pure trivial)).mono (fun _ _ => trivial)
        · exact DREBEmits.pure trivial
      · rintro _ ⟨l₁, l₂, rfl, ⟨B, rfl⟩, -⟩ - - - -
        exact ⟨B, List.mem_append_left _ (List.mem_singleton_self _)⟩
    · refine DREBEmits.ite (fun _ => ?_) (fun _ => ?_)
      · refine (DREBEmits.bind (L₂ := fun _ => True) (attest_sends C _)
          (fun _ => DREBEmits.pure trivial)).mono ?_
        intro _ _ h0 ht hp ha
        exfalso; apply hc
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨⟨⟨h0, ht⟩, by rw [hv]; exact hp⟩, ha⟩
      · refine DREBEmits.pure ?_
        intro h0 ht hp ha
        exfalso; apply hc
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨⟨⟨h0, ht⟩, by rw [hv]; exact hp⟩, ha⟩
  · rintro _ ⟨l₁, l₂, rfl, -, h2⟩ h0 ht hp ha
    obtain ⟨B, hB⟩ := h2 h0 ht hp ha
    exact ⟨B, List.mem_append_right _ hB⟩

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- A tick at the start `t` of a slot `s > 0`, of the slot's proposer, whose wake record passes the
proposal test, sends a block.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `t`: the time. -/
theorem tick_emits_proposal (C : Config) (P : Provisional V) (X : External V) (n : NodeState V)
    (t : Time) :
    DREBEmits (fun l => 0 < C.slot t → t = C.t_ (C.slot t) → n.v = P.proposer (C.slot t) →
        (record_awake n t).awake_since (proposal_window_start C (C.slot t)) = true →
        ∃ B : Block V, NamedObject.block B ∈ l)
      (tick C P X n t) := by
  have hv := (record_awake_frame n t).2.2.1
  simp only [tick]
  refine (DREBEmits.bind (L₂ := fun l => 0 < C.slot t → t = C.t_ (C.slot t) →
      n.v = P.proposer (C.slot t) →
      (record_awake n t).awake_since (proposal_window_start C (C.slot t)) = true →
      ∃ B : Block V, NamedObject.block B ∈ l)
    (ac_on_tick_emits_vote C P _ _ t _ _ _) (fun _ => ?_)).mono ?_
  · refine DREBEmits.ite (fun _ => ?_) (fun hc => ?_)
    · refine (DREBEmits.bind (L₂ := fun _ => True) (propose_block_sends C P X _)
        (fun _ => ?_)).mono ?_
      · refine DREBEmits.ite (fun _ => ?_) (fun _ => ?_)
        · exact (DREBEmits.bind (L₂ := fun _ => True) (attest_sends C _)
            (fun _ => DREBEmits.pure trivial)).mono (fun _ _ => trivial)
        · exact DREBEmits.pure trivial
      · rintro _ ⟨l₁, l₂, rfl, ⟨B, rfl⟩, -⟩ - - - -
        exact ⟨B, List.mem_append_left _ (List.mem_singleton_self _)⟩
    · refine DREBEmits.ite (fun _ => ?_) (fun _ => ?_)
      · refine (DREBEmits.bind (L₂ := fun _ => True) (attest_sends C _)
          (fun _ => DREBEmits.pure trivial)).mono ?_
        intro _ _ h0 ht hp ha
        exfalso; apply hc
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨⟨⟨h0, ht⟩, by rw [hv]; exact hp⟩, ha⟩
      · refine DREBEmits.pure ?_
        intro h0 ht hp ha
        exfalso; apply hc
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨⟨⟨h0, ht⟩, by rw [hv]; exact hp⟩, ha⟩
  · rintro _ ⟨l₁, l₂, rfl, -, h2⟩ h0 ht hp ha
    obtain ⟨B, hB⟩ := h2 h0 ht hp ha
    exact ⟨B, List.mem_append_right _ hB⟩

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- What the node's tick at `t` sends, when `t` is the vote time of its slot, the duty test of
that slot passes on the state after the wake is recorded, and the node's validator is a member of
the committee of that slot: a Goldfish vote of the node's validator for that slot.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `t`: the time.

Read aloud: at the vote time, an awake committee member's tick sends its vote. -/
theorem tick_emits_vote (C : Config) (P : Provisional V) (X : External V) (n : NodeState V)
    (t : Time) :
    DREBEmits (fun l => t = C.t_ (C.slot t) + C.Δ →
        (record_awake n t).awake_since (duty_window_start C (C.slot t)) = true →
        n.v ∈ P.committee (C.slot t) →
        ∃ h : BlockId, NamedObject.gfVote (GoldfishVote.mk n.v (C.slot t) h) ∈ l)
      (tick C P X n t) := by
  have hv := (record_awake_frame n t).2.2.1
  simp only [tick]
  refine (DREBEmits.bind (L₂ := fun _ => True) (ac_on_tick_emits_vote C P _ _ t _ _ _)
    (fun _ => ?_)).mono ?_
  · refine DREBEmits.ite (fun _ => ?_) (fun _ => ?_)
    · refine (DREBEmits.bind (L₂ := fun _ => True) (propose_block_sends C P X _)
        (fun _ => ?_)).mono (fun _ _ => trivial)
      refine DREBEmits.ite (fun _ => ?_) (fun _ => ?_)
      · exact (DREBEmits.bind (L₂ := fun _ => True) (attest_sends C _)
          (fun _ => DREBEmits.pure trivial)).mono (fun _ _ => trivial)
      · exact DREBEmits.pure trivial
    · refine DREBEmits.ite (fun _ => ?_) (fun _ => ?_)
      · exact (DREBEmits.bind (L₂ := fun _ => True) (attest_sends C _)
          (fun _ => DREBEmits.pure trivial)).mono (fun _ _ => trivial)
      · exact DREBEmits.pure trivial
  · rintro _ ⟨l₁, l₂, rfl, h1, -⟩ ht hb hK
    obtain ⟨h, hh⟩ := h1 ht hb (by rw [hv]; exact hK)
    rw [hv] at hh
    exact ⟨h, List.mem_append_left _ hh⟩

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- Every answer of the proposal keeps `awakeSince`: it ends by receiving the proposed block,
which writes the FG state and the AC state only.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state. -/
theorem propose_block_awakeSince (C : Config) (P : Provisional V) (X : External V)
    (n : NodeState V) :
    DREBPost (propose_block C P X n) (fun n' => n'.awakeSince = n.awakeSince) := by
  simp only [propose_block]
  repeat' first
    | exact DREBPost.pure (by rw [on_block_eq]; split <;> rfl)
    | refine DREBPost.bind_any (fun _ => ?_)

/-- Every answer of the attestation duty keeps `awakeSince`: it writes the anti-slashing record and
the FG state only.

The variables:
- `C`: the parameters; `n`: the node state. -/
theorem attest_awakeSince (C : Config) (n : NodeState V) :
    DREBPost (attest C n) (fun n' => n'.awakeSince = n.awakeSince) := by
  simp only [attest]
  repeat' first
    | exact DREBPost.pure rfl
    | exact DREBPost.pure (by simp only [on_attestation, Id.run]; split <;> rfl)
    | refine DREBPost.dite (fun _ => ?_) (fun _ => ?_)
    | refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
    | refine DREBPost.bind_any (fun _ => ?_)

/-- A tick's answer has the `awakeSince` its first step, `record_awake`, wrote: the clock, the
tick of the available chain and the duties write other fields.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `t`: the time;
- `n'`, `sent`: an `.ok` outcome of the tick, the node state and the objects sent.

Read aloud: a tick writes `awakeSince` only by recording the time of a wake. -/
theorem tick_awakeSince (C : Config) (P : Provisional V) (X : External V)
    (n n' : NodeState V) (t : Time) (sent : List (NamedObject V))
    (hRun : .ok (n', sent) ∈ (tick C P X n t).outcomes) :
    n'.awakeSince = (record_awake n t).awakeSince := by
  have h : DREBPost (tick C P X n t)
      (fun n' => n'.awakeSince = (record_awake n t).awakeSince) := by
    simp only [tick]
    refine DREBPost.bind_any (fun A₁ => ?_)
    refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
    · refine DREBPost.bind (propose_block_awakeSince C P X _) (fun n₄ h₄ => ?_)
      refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
      · refine DREBPost.bind (attest_awakeSince C n₄) ?_
        intro n₅ h₅
        exact DREBPost.pure (h₅.trans h₄)
      · exact DREBPost.pure h₄
    · refine DREBPost.ite (fun _ => ?_) (fun _ => ?_)
      · refine DREBPost.bind (attest_awakeSince C _) ?_
        intro n₅ h₅
        exact DREBPost.pure h₅
      · exact DREBPost.pure rfl
  exact DREBPost.of_outcome h hRun

omit [DecidableEq V] [Fintype V] [RootOrder] in
/-- `record_awake` keeps a present `awakeSince`.

The variables:
- `n`: the node state; `t`: the time of the tick; `τ`: the stored time. -/
theorem record_awake_awakeSince_some {n : NodeState V} {t τ : Time}
    (h : n.awakeSince = some τ) : (record_awake n t).awakeSince = some τ := by
  simp only [record_awake, Id.run, h, reduceCtorEq, dite_false]
  exact h

omit [DecidableEq V] [Fintype V] [RootOrder] in
/-- `record_awake` at `t` writes `some t` over an absent `awakeSince`.

The variables:
- `n`: the node state; `t`: the time of the tick. -/
theorem record_awake_awakeSince_none {n : NodeState V} {t : Time}
    (h : n.awakeSince = none) : (record_awake n t).awakeSince = some t := by
  simp only [record_awake, Id.run, h, dite_true]
  rfl

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

omit [DecidableEq V] [Fintype V] [RootOrder] in
/-- **Kit fact, the duty test read back on the stored `awakeSince`.** When the test of the wake
rule for `t₀` passes on the state `record_awake n t` and `t₀ < t`, the stored `awakeSince` of `n`
is some `τ ≤ t₀`.

Why: an absent `awakeSince` becomes `t`, which fails the test for `t₀ < t`; a present one is kept.

The variables:
- `n`: the node state; `t`: the time of the tick; `t₀`: the time the test compares with. -/
theorem awakeSince_of_record_awake {n : NodeState V} {t t₀ : Time}
    -- the test for `t₀` passes on the state the tick's first step leaves
    (h : (record_awake n t).awake_since t₀ = true)
    -- `t₀` is before the tick
    (hlt : t₀ < t) :
    ∃ τ : Time, n.awakeSince = some τ ∧ τ ≤ t₀ := by
  cases hn : n.awakeSince with
  | none =>
      have hr := record_awake_awakeSince_none (t := t) hn
      simp only [NodeState.awake_since, Id.run, hr, ne_eq, reduceCtorEq, not_false_eq_true,
        dite_true, Option.value, Option.get_some] at h
      exact absurd (lt_of_le_of_lt (of_decide_eq_true h) hlt) (lt_irrefl _)
  | some τ =>
      have hr := record_awake_awakeSince_some (t := t) hn
      simp only [NodeState.awake_since, Id.run, hr, ne_eq, reduceCtorEq, not_false_eq_true,
        dite_true, Option.value, Option.get_some] at h
      exact ⟨τ, rfl, of_decide_eq_true h⟩

end

section

open Goldilocks

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The wake and the initial node state, as equations

Added by the record migration, step 1f, for the execution proofs that read a field of `wake n` or
of `initial C v`. -/

/-- **What a wake leaves.** `wake n t` is `n` with `awakeSince` set to `none` and the clock set
to `t`, every other field kept.

The variables:
- `n`: the node state; `t`: the wake time.

Read aloud: waking forgets the time since which the node has been awake and sets the clock to the
wake time, and nothing else. -/
theorem wake_eq (n : NodeState V) (t : Time) : wake n t = { n with awakeSince := none, t := t } :=
  by rfl

/-- **What receiving a Goldfish vote leaves.** `on_ac_message C P n vote` is `n` with its AC state
replaced by `on_goldfish_vote C P n.A n.t vote`, every other field kept: the AC interface's
`ac_on_message` is the vote handler `on_goldfish_vote` at the node's clock.

The variables:
- `C`, `P`: the parameters and the values; `n`: the node state; `vote`: the vote.

Read aloud: a received Goldfish vote changes the AC state alone, as the vote handler does at the
node's clock. -/
theorem on_ac_message_eq (C : Config) (P : Provisional V) (n : NodeState V)
    (vote : GoldfishVote V) :
    on_ac_message C P n vote = { n with A := on_goldfish_vote C P n.A n.t vote } := by rfl

/-- **The form check of a block, as a condition.** `block_well_formed P X B` answers `true` exactly
when every attestation `B` includes is well formed (`attestation_well_formed`), its payload passes
`ac_valid_payload P B`, and its root is the digest of its parent's root, its slot, its
attestations, its Goldfish votes and its support votes.

The variables:
- `P`, `X`: the values and the digest; `B`: the block.

Read aloud: a block is well formed when its attestations are, its payload is valid, and its root is
the digest of its contents. -/
theorem block_well_formed_iff (P : Provisional V) (X : External V) (B : Block V) :
    block_well_formed P X B = true ↔
      ((∀ a ∈ B.attestations, attestation_well_formed a = true) ∧ ac_valid_payload P B = true) ∧
        B.root = X.digest B.parent.root B.slot B.attestations B.votes B.support_votes := by
  simp only [block_well_formed, Bool.and_eq_true, decide_eq_true_eq]

/-- **The initial node state, written out.** The node state `initial C v` a node of the validator
`v` starts from has the validator `v`, the clock `0`, the initial FG state `FGState.initial`, the
initial AC state `ACState.initial`, the initial anti-slashing record `SigningHistory.initial`, and
`awakeSince` equal to `proposal_window_start C 0`.

The variables:
- `C`: the parameters; `v`: the validator.

Read aloud: a node starts at time `0` from the initial FG state, AC state and record. -/
theorem initial_eq (C : Config) (v : V) :
    initial C v =
      { v := v, t := 0, S := FGState.initial, A := ACState.initial, Λ := SigningHistory.initial,
        awakeSince := proposal_window_start C 0 } := by rfl

end

end GoldilocksCorrectness.Proofs.Routines
