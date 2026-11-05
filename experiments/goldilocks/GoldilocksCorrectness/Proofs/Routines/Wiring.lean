module
public import GoldilocksCorrectness.Proofs.Routines.Node
public import GoldilocksSts
public import GoldilocksCorrectness.Proofs.Routines.Attestation
public import GoldilocksCorrectness.Proofs.Routines.NodeReach
public import GoldilocksCorrectness.Proofs.Routines.PeriodLocks
public import GoldilocksCorrectness.Statements.Routines.ReceiveDefs
import all Goldilocks.AC.ForkChoice
import all Goldilocks.AC.Interface
import all Goldilocks.AC.State
import all Goldilocks.Config
import all Goldilocks.FG.State
import all Goldilocks.Node

@[expose] public section

/-!
# What receiving an object does to a node state

`mem_T_receive_block`: a block delivered to a node that holds it, or whose test
`block_admissible` it passes, is in the node's block tree after the delivery.

`receive_step`, `receive_new`, `receive_new_slot`, `receive_pool`, `receive_grows`,
`receive_chainsInPool`, `receive_finalizedFrom`, `receive_justifiedFrom`, `receive_cachesFrom`,
`receive_reachFrom`, `receive_witnessedFrom`, `receive_awakeSince`, `receive_Λ`, `receive_nodeInv`:
what receiving an object keeps of the relations between node states of `Proofs/Routines/Node.lean`
and of the node invariant `NodeInv`, and what it adds; `reaction_tick_cachesFrom`: the same for a
tick's reaction; `mem_relayedObjects_iff`, `mem_relayedObjects_self`, `gfVote_mem_relayedObjects`,
`gfVote_mem_relayedObjects_block`: the objects a received object relays;
`anchor_extends_B_of_inv_orTwoPast`: the AC fork choice's anchor of a node state holding a live
lock entry on a block `B` is `B` or a descendant of `B` (statement on
`Statements/Routines/ReceiveStatements.lean`).

They read the node routines and node states alone: no execution.

Moved here unchanged from the execution pages.
-/

set_option autoImplicit false

open scoped DC
open DC (DRE)

namespace GoldilocksCorrectness.Proofs.Routines

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]

section

variable [RootOrder]

/-- A block delivered to a node that holds it, or whose test it passes, is in the node's tree
after the delivery.

The variables:
- `C`, `P`, `X`: the parameters, the given values, the digest; `n`: the node state; `B`: the
  block. -/
theorem mem_T_receive_block (C : Config) (P : Provisional V) (X : External V) (n : NodeState V)
    (B : Block V)
    -- the node holds `B`, or `B` passes the test
    (h : B ∈ n.S.T ∨ block_admissible C P X n B = true) :
    B ∈ (Goldilocks.Sts.receive C P X n (NamedObject.block B)).S.T := by
  show B ∈ (on_block C P X n B).S.T
  rw [on_block_eq]
  split
  · show B ∈ (fg_on_block C n.S B).T
    rw [(fg_on_block_eq C n.S B).1]
    exact Finset.mem_union_right _ (Finset.mem_singleton_self B)
  · rename_i ha
    rcases h with h | h
    · exact h
    · exact absurd h ha

end

end

end GoldilocksCorrectness.Proofs.Routines

namespace GoldilocksCorrectness.Proofs.Routines

open Goldilocks

/-- `omega` after the `abbrev`s `Height` and `Slot` are unfolded in the goal and in every
hypothesis: `omega` does not see a fact stated at either. -/
local macro "omega_nat" : tactic =>
  `(tactic| ((try dsimp only) <;> (try unfold Height at *) <;> (try unfold Slot at *) <;> omega))

-- An index `x[i]` into an execution has the valid-index predicate `fun _ _ => True`; this rule,
-- local to the file, proves it at once.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]

section

variable [RootOrder]

/-- The wiring's dispatch of a delivered object is a step from the node state at its clock.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `o`: the object. -/
theorem receive_step (C : Config) (P : Provisional V) (X : External V) (n : NodeState V)
    (o : NamedObject V) (hk : SlotKeyed n.A) :
    StepFrom n n.t (Goldilocks.Sts.receive C P X n o) := by
  cases o with
  | block B => exact on_block_step C P X n B hk
  | gfVote vote => exact on_ac_message_step C P n vote hk
  | attest a => exact on_attestation_step n a hk

end

end

section

open GoldilocksCorrectness.Statements.Routines (ChainStatesComputed)

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- The wiring's dispatch of a delivered object, from a node state whose chain states of its tree
are the blocks' own, relates the node state to the result.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `o`: the object. -/
theorem receive_finalizedFrom (C : Config) (P : Provisional V) (X : External V)
    (n : NodeState V) (o : NamedObject V)
    -- the chain states of `n`'s tree are the blocks' own
    (hCS : ChainStatesComputed C n.S) :
    FinalizedFrom C n (Goldilocks.Sts.receive C P X n o) := by
  cases o with
  | block B => exact on_block_finalizedFrom C P X n B hCS
  | gfVote vote => exact finalizedFrom_of_frame C rfl rfl
  | attest a =>
      obtain ⟨hT, hF⟩ := on_attestation_frame_S n a
      exact finalizedFrom_of_frame C hT hF

end

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- The wiring's dispatch of a delivered object keeps `ChainsInPool`.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `o`: the object. -/
theorem receive_chainsInPool (C : Config) (P : Provisional V) (X : External V) (n : NodeState V)
    (o : NamedObject V) (h : ChainsInPool n) :
    ChainsInPool (Goldilocks.Sts.receive C P X n o) := by
  cases o with
  | block B => exact on_block_chainsInPool C P X n B h
  | gfVote vote => exact h.of_S rfl
  | attest a => exact on_attestation_chainsInPool n a h

end

section

open GoldilocksCorrectness.Statements.Routines (ChainStatesComputed)

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- The wiring's dispatch of a delivered object, from a node state whose chain states of its tree
are the blocks' own, relates the node state to the result.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `o`: the object. -/
theorem receive_justifiedFrom (C : Config) (P : Provisional V) (X : External V)
    (n : NodeState V) (o : NamedObject V)
    -- the chain states of `n`'s tree are the blocks' own
    (hCS : ChainStatesComputed C n.S) :
    JustifiedFrom C n (Goldilocks.Sts.receive C P X n o) := by
  cases o with
  | block B => exact on_block_justifiedFrom C P X n B hCS
  | gfVote vote => exact justifiedFrom_of_frame C rfl
  | attest a => exact justifiedFrom_of_frame C (on_attestation_J n a)

end

end

section

open GoldilocksCorrectness.Statements.Routines (NodeInv)

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]

section

variable [RootOrder]

/-- The wiring's dispatch of a delivered object keeps `NodeInv`, the validator and the clock.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `o`: the object. -/
theorem receive_nodeInv (C : Config) (P : Provisional V) (X : External V) (n : NodeState V)
    (o : NamedObject V) (h : NodeInv C P X n) :
    NodeInv C P X (Goldilocks.Sts.receive C P X n o) ∧
      (Goldilocks.Sts.receive C P X n o).v = n.v ∧ (Goldilocks.Sts.receive C P X n o).t = n.t := by
  cases o with
  | block B => exact on_block_nodeInv C P X n B h
  | gfVote vote => exact on_ac_message_nodeInv C P X n vote h
  | attest a => exact on_attestation_nodeInv C P X n a h

end

end

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]
variable [RootOrder]

/-- The wiring's dispatch of a delivered object keeps the pool.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `o`: the object. -/
theorem receive_pool (C : Config) (P : Provisional V) (X : External V) (n : NodeState V)
    (o : NamedObject V) : AttPoolGrows n (Goldilocks.Sts.receive C P X n o) := by
  cases o with
  | block B => exact on_block_pool C P X n B
  | gfVote vote => exact AttPoolGrows.refl n
  | attest a => exact (on_attestation_pool n a).1

end

section

open GoldilocksCorrectness.Statements.Routines (ChainStatesComputed)

section

open Goldilocks
open Goldilocks.Sts (Setup)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- The wiring's dispatch of a delivered object, from a node state whose chain states of its tree
are the blocks' own, relates the node state to the result.

The variables:
- `C`, `P`, `X`: the parameters and the values; `H`: the threshold; `OnChain`: the set of blocks;
  `n`: the node state; `o`: the object. -/
theorem receive_cachesFrom (C : Config) (P : Provisional V) (X : External V) (H : ℕ)
    (OnChain : Block V → Prop) (n : NodeState V) (o : NamedObject V)
    -- the chain states of `n`'s tree are the blocks' own
    (hCS : ChainStatesComputed C n.S) :
    CachesFrom C H OnChain n (Goldilocks.Sts.receive C P X n o) := by
  cases o with
  | block B => exact on_block_cachesFrom C P X H OnChain n B hCS
  | gfVote vote => exact cachesFrom_of_frame C H OnChain rfl rfl rfl rfl
  | attest a =>
      obtain ⟨hT, hJ, hhj, hF⟩ := on_attestation_caches n a
      exact cachesFrom_of_frame C H OnChain hT hJ hhj hF

/-- Every `.ok` outcome of the tick, from a node state whose chain states of its tree are the
blocks' own, relates the node state to the outcome's node state.

The variables:
- `S`: the setup; `H`: the threshold; `OnChain`: the set of blocks; `n`: the node state; `r`: the
  reading; `n'`, `sent`: the outcome, the node state and the objects sent. -/
theorem reaction_tick_cachesFrom (S : Setup V) (H : ℕ) (OnChain : Block V → Prop)
    (n n' : NodeState V) (r : Int) (sent : List (NamedObject V))
    -- `.ok (n', sent)` is an outcome of the tick at `r`
    (hok : .ok (n', sent) ∈ (tick S.C S.P S.X n r).outcomes)
    -- the chain states of `n`'s tree are the blocks' own
    (hCS : ChainStatesComputed S.C n.S) :
    CachesFrom S.C H OnChain n n' :=
  DREBPost.of_outcome (tick_cachesFrom S.C S.P S.X H OnChain n r hCS) hok

end

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- The wiring's dispatch of a delivered object relates the node state to the result. -/
theorem receive_reachFrom (C : Config) (P : Provisional V) (X : External V) (D : Block V)
    (n : NodeState V) (o : NamedObject V) :
    ReachFrom C D n (Goldilocks.Sts.receive C P X n o) := by
  cases o with
  | block B => exact on_block_reachFrom C P X D n B
  | gfVote vote => exact reachFrom_of_frame C D rfl rfl
  | attest a =>
      obtain ⟨hT, -, -, hF⟩ := on_attestation_caches n a
      exact reachFrom_of_frame C D hT hF

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]

section

variable [RootOrder]

/-- The wiring's dispatch of a delivered object keeps the pool filed by slot and grows the node
state.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `o`: the object. -/
theorem receive_grows (C : Config) (P : Provisional V) (X : External V) (n : NodeState V)
    (o : NamedObject V) (hk : SlotKeyed n.A) :
    SlotKeyed (Goldilocks.Sts.receive C P X n o).A ∧
      TreeGrows n (Goldilocks.Sts.receive C P X n o) := by
  cases o with
  | block B => exact on_block_grows C P X n B hk
  | gfVote vote => exact on_ac_message_grows C P n vote hk
  | attest a => exact on_attestation_grows n a hk

end

end

section

open GoldilocksCorrectness.Statements.Routines (CachesCompatibleWith)
open GoldilocksCorrectness.Statements.Routines (chainStateOf)
open GoldilocksCorrectness.Statements.Routines (ChainStatesComputed)

section

open Goldilocks
open Goldilocks.Sts (Setup)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

section

open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn)

/-- **The anchor of a lock holder is `B` or a descendant of `B`, with the finality gadget not
contested or two past `B`.** The proof; the audited statement is in
`Statements/Executions/PeriodChainBlockStatements.lean`. The proof of `anchor_extends_B_of_inv`,
with the viable head on `B`'s chain found by cases on `h(B) + 2 ≤ h_max`: when it holds, the held
block at `h_max` descends from `B` (`hTwo`) and is viable, `head_height_floor` (the least chain-state height a viable block may have) being at most
`h_max` in both branches of `head_height_floor`; when it does not, the FG state is not contested
and the original argument runs (`head_height_floor` is `h_max − 1`, at most `h(B)`, and `B` is viable).

The variables:
- `S`: the setup; `n`: the node state; `B`: the locked block; `t`: the time; `H`: the threshold
  of the old attestations; `d`: the lock's deadline. -/
theorem anchor_extends_B_of_inv_orTwoPast (S : Setup V) (n : NodeState V) (B : Block V)
    (t : Time) (H : ℕ) (d : Time)
    (hlock : LockEntry.mk B d ∈ n.A.lock_entries)
    (hlive : is_live (fg_to_ac n.S) t (LockEntry.mk B d) = true)
    (hlocks : ∀ e ∈ n.A.lock_entries, is_live (fg_to_ac n.S) t e = true → e.B.compatible B = true)
    (hC : CachesCompatibleWith S B H n)
    (hTwo : ∀ D ∈ n.S.T, (chainStateOf S.C B).h + 2 ≤ (chainStateOf S.C D).h → B.AncestorEq D)
    (hNC : fg_contest n.S = false ∨ (chainStateOf S.C B).h + 2 ≤ n.S.h_max)
    (hWit : ∃ D ∈ n.S.T, (chainStateOf S.C D).h = n.S.h_max)
    (hRootsT : RootsNameBlocksIn n.S.T)
    (hσ : ChainStatesComputed S.C n.S) :
    B.AncestorEq (get_anchor n.A (fg_to_ac n.S) t) := by
  have hJB := hC.2.1
  have hFJ := hC.2.2.2.2
  have hFr : n.S.F.AncestorEq (get_fc_root n.S) :=
    GoldilocksCorrectness.Proofs.Routines.F_ancestorEq_get_fc_root _ hFJ
  have hrJF : get_fc_root n.S = n.S.J ∨ get_fc_root n.S = n.S.F := by
    simp only [get_fc_root, Id.run]
    split
    · exact Or.inl rfl
    · exact Or.inr rfl
  -- the root of the fork choice is compatible with `B`
  have hrB : (get_fc_root n.S).AncestorEq B ∨ B.AncestorEq (get_fc_root n.S) := by
    rcases hrJF with h | h <;> rw [h]
    · exact hJB
    · rcases hJB with hJB | hBJ
      · exact Or.inl (ancestorEq_trans hFJ hJB)
      · exact ancestorEq_compatible hFJ hBJ
  have hroot : (fg_to_ac n.S).fc_root = get_fc_root n.S := rfl
  rcases hrB with hrB | hBr
  swap
  · rw [← hroot] at hBr
    exact ancestorEq_trans hBr (fc_root_ancestorEq_get_anchor _ _ _)
  -- `B` is in the frame's tree, live
  have hBΦ : B ∈ (fg_to_ac n.S).tree := by
    simp only [is_live, Bool.and_eq_true, decide_eq_true_eq] at hlive
    exact hlive.2
  have hBT : B ∈ n.S.T ∧ n.S.F.AncestorEq B :=
    (GoldilocksCorrectness.Proofs.Routines.mem_fg_to_ac_tree _ _).1 hBΦ
  -- a viable head that is `B` or a descendant of `B`
  have hW : ∃ W ∈ (fg_to_ac n.S).tree ∩ (fg_to_ac n.S).viable_heads, B.AncestorEq W := by
    obtain ⟨D, hD, hDh⟩ := hWit
    have hviable : ∀ W : Block V, W ∈ n.S.T → B.AncestorEq W →
        head_height_floor n.S ≤ (chainStateOf S.C W).h →
        W ∈ (fg_to_ac n.S).tree ∩ (fg_to_ac n.S).viable_heads := by
      intro W hWT hBW hWh
      have hWΦ : W ∈ (fg_to_ac n.S).tree :=
        (GoldilocksCorrectness.Proofs.Routines.mem_fg_to_ac_tree _ _).2
          ⟨hWT, ancestorEq_trans hBT.2 hBW⟩
      refine Finset.mem_inter.2 ⟨hWΦ, ?_⟩
      show W ∈ ({D ∈ (fg_to_ac n.S).tree | (get_fc_root n.S).ancestorEq D && is_viable n.S D} :
        Finset (Block V))
      rw [Finset.mem_filter]
      refine ⟨hWΦ, ?_⟩
      have h1 : (get_fc_root n.S).ancestorEq W = true := ancestorEq_trans hrB hBW
      have h2 : is_viable n.S W = true := by
        simp only [is_viable, decide_eq_true_eq]
        show head_height_floor n.S ≤ (n.S.σ W).h
        rw [hσ W hWT]
        exact hWh
      rw [h1, h2]
      rfl
    -- `head_height_floor` is at most `h_max`
    have hfloor_le : head_height_floor n.S ≤ n.S.h_max := by
      simp only [head_height_floor, Id.run]
      split
      · exact le_rfl
      · exact Nat.sub_le _ _
    by_cases h2 : (chainStateOf S.C B).h + 2 ≤ n.S.h_max
    · -- the block at `h_max` is a descendant of `B`, and viable whatever `head_height_floor` is
      have hBD := hTwo D hD (by rw [hDh]; exact h2)
      exact ⟨D, hviable D hD hBD (by rw [hDh]; exact hfloor_le), hBD⟩
    · -- not contested: `head_height_floor` is `h_max − 1`, and `B` is viable
      have hNC' : fg_contest n.S = false := hNC.resolve_right h2
      have hfloor : head_height_floor n.S = n.S.h_max - 1 := by
        simp only [head_height_floor, Id.run, hNC']
        rfl
      exact ⟨B, hviable B hBT.1 (ancestorEq_refl B) (by rw [hfloor]; omega_nat),
        ancestorEq_refl B⟩
  -- `B` is a locked block of the viable tree
  have hBL : B ∈ ({D ∈ viable_tree (fg_to_ac n.S) (fg_to_ac n.S).tree |
      is_locked n.A (fg_to_ac n.S) t D} : Finset (Block V)) := by
    rw [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · simp only [viable_tree, Finset.mem_filter, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hBΦ, hrB, hW⟩
    · simp only [is_locked, decide_eq_true_eq]
      exact ⟨_, hlock, hlive, ancestorEq_refl B⟩
  have hRL : RootsNameBlocksIn ({D ∈ viable_tree (fg_to_ac n.S) (fg_to_ac n.S).tree |
      is_locked n.A (fg_to_ac n.S) t D} : Finset (Block V)) := by
    intro X hX Y hY hXY
    have hX' := (Finset.mem_filter.1 (Finset.mem_filter.1 hX).1).1
    have hY' := (Finset.mem_filter.1 (Finset.mem_filter.1 hY).1).1
    exact hRootsT X ((GoldilocksCorrectness.Proofs.Routines.mem_fg_to_ac_tree _ _).1 hX').1
      Y ((GoldilocksCorrectness.Proofs.Routines.mem_fg_to_ac_tree _ _).1 hY').1 hXY
  obtain ⟨X, hX⟩ := deepest?_isSome _ ⟨B, hBL⟩ hRL
  have hanc : get_anchor n.A (fg_to_ac n.S) t = X := by
    simp only [get_anchor, Id.run, hX, ne_eq, reduceCtorEq, not_false_eq_true, dite_true,
      Option.value, Option.get_some]
    rfl
  rw [hanc]
  -- `X` is compatible with `B` and at least as deep
  have hXL := deepest?_mem hX
  have hXlocked := (Finset.mem_filter.1 hXL).2
  simp only [is_locked, decide_eq_true_eq] at hXlocked
  obtain ⟨e, he, hel, hXe⟩ := hXlocked
  have hXB := compatible_of_ancestorEq_compatible hXe (hlocks e he hel)
  have hdeep := (mem_of_pickUnique?_eq_some hX).2
  simp only [Block.isDeepestIn, decide_eq_true_eq] at hdeep
  have hBX := hdeep B hBL
  simp only [Block.deeper, Bool.or_eq_false_iff, decide_eq_false_iff_not, Bool.and_eq_false_imp,
    decide_eq_true_eq] at hBX
  rcases (compatible_iff X B).1 hXB with hXB' | hBX'
  · have hdle := depth_le_of_ancestorEq hXB'
    have : X = B := eq_of_ancestorEq_of_depth hXB' (by omega)
    rw [this]
    exact ancestorEq_refl B
  · exact hBX'

end

end

end

section

open GoldilocksCorrectness.Statements.Routines (ChainStatesComputed)

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- The wiring's dispatch of a delivered object relates the node state to the result. -/
theorem receive_witnessedFrom (C : Config) (P : Provisional V) (X : External V)
    (n : NodeState V) (o : NamedObject V) (hCS : ChainStatesComputed C n.S) :
    WitnessedFrom C n (Goldilocks.Sts.receive C P X n o) := by
  cases o with
  | block B => exact on_block_witnessedFrom C P X n B hCS
  | gfVote vote => exact witnessedFrom_of_frame C rfl rfl rfl rfl rfl
  | attest a =>
      obtain ⟨h1, h2, h3, h4, h5⟩ := on_attestation_witness_keeps n a
      exact witnessedFrom_of_frame C h1 h2 h3 h4 h5

end

end

section

open Goldilocks

section

variable {V : Type} [DecidableEq V] [Fintype V]
variable [RootOrder]

/-- The wiring's dispatch of the delivered object `o` adds to the pool only votes `o` carries, and
to the tree only `o`'s block, of a slot at most the slot of the node's clock, which it keeps.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `o`: the object. -/
theorem receive_new (C : Config) (P : Provisional V) (X : External V) (n : NodeState V)
    (o : NamedObject V) :
    (∀ s : Slot, ∀ vote ∈ (Goldilocks.Sts.receive C P X n o).A.gf_votes s,
        vote ∉ n.A.gf_votes s → Carried o vote) ∧
      (∀ B ∈ (Goldilocks.Sts.receive C P X n o).S.T, B ∉ n.S.T →
        o = NamedObject.block B ∧ B.slot ≤ C.slot (Goldilocks.Sts.receive C P X n o).t) := by
  cases o with
  | block B =>
      obtain ⟨h1, h2, h3⟩ := on_block_new C P X n B
      refine ⟨fun s vote hv hn => Or.inr ⟨B, rfl, h1 s vote hv hn⟩, fun B' hB hn => ?_⟩
      obtain ⟨rfl, hs⟩ := h2 B' hB hn
      exact ⟨rfl, by
        show B'.slot ≤ C.slot (on_block C P X n B').t
        rw [h3]
        exact hs⟩
  | gfVote vote =>
      refine ⟨fun s vote' hv hn => Or.inl ?_, fun B hB hn => absurd hB hn⟩
      rw [on_goldfish_vote_new C P n.A n.t vote s vote' hv hn]
  | attest a =>
      obtain ⟨hT, hA, -⟩ := on_attestation_frame n a
      refine ⟨fun s vote hv hn => ?_, fun B hB hn => ?_⟩
      · change vote ∈ (on_attestation n a).A.gf_votes s at hv
        rw [hA] at hv
        exact absurd hv hn
      · change B ∈ (on_attestation n a).S.T at hB
        rw [hT] at hB
        exact absurd hB hn

end

end

section

open Goldilocks

section

open Goldilocks.Sts (relayedObjects)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

omit [DecidableEq V] [Fintype V] [RootOrder] in
/-- The objects the wiring re-sends on a delivery include the delivered object. -/
theorem mem_relayedObjects_self (o : NamedObject V) : o ∈ relayedObjects o := by
  cases o <;> simp [relayedObjects]

end

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]

section

variable [RootOrder]

/-- The wiring's dispatch of a delivered object adds to the pool only votes with a slot at most
the slot of the node's clock.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `o`: the object.

Read aloud: a receipt admits no vote of a slot later than the node's. -/
theorem receive_new_slot (C : Config) (P : Provisional V) (X : External V) (n : NodeState V)
    (o : NamedObject V) :
    ∀ s : Slot, ∀ vote ∈ (Goldilocks.Sts.receive C P X n o).A.gf_votes s,
      vote ∉ n.A.gf_votes s → vote.slot ≤ C.slot n.t := by
  intro s vote hv hn
  cases o with
  | block B =>
      change vote ∈ (on_block C P X n B).A.gf_votes s at hv
      rw [on_block_eq] at hv
      split at hv
      · exact ac_on_block_new_slot C P n.A n.t B s vote hv hn
      · exact absurd hv hn
  | gfVote vote' =>
      change vote ∈ (on_goldfish_vote C P n.A n.t vote').gf_votes s at hv
      obtain ⟨rfl, hs⟩ := on_goldfish_vote_new_slot C P n.A n.t vote' s vote hv hn
      exact hs
  | attest a =>
      change vote ∈ (on_attestation n a).A.gf_votes s at hv
      rw [(on_attestation_frame n a).2.1] at hv
      exact absurd hv hn

end

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]

section

open Goldilocks.Sts (relayedObjects)
variable [RootOrder]

omit [DecidableEq V] [Fintype V] [RootOrder] in
/-- The objects the wiring re-sends for a block include, as Goldfish-vote objects, the votes the
block includes.

The variables:
- `B`: the block; `vote`: a vote of `B.votes`. -/
theorem gfVote_mem_relayedObjects_block {B : Block V} {vote : GoldfishVote V}
    (h : vote ∈ B.votes) : NamedObject.gfVote vote ∈ relayedObjects (NamedObject.block B) := by
  simp only [relayedObjects, Multiset.mem_add, Multiset.mem_coe, List.mem_map]
  exact Or.inl (Or.inr ⟨vote, h, rfl⟩)

omit [DecidableEq V] [Fintype V] [RootOrder] in
/-- An object that carries a Goldfish vote has that vote among the objects the wiring re-sends
for it.

The variables:
- `o`: the object; `vote`: the vote it carries. -/
theorem gfVote_mem_relayedObjects {o : NamedObject V} {vote : GoldfishVote V}
    (h : Carried o vote) : NamedObject.gfVote vote ∈ relayedObjects o := by
  rcases h with rfl | ⟨B, rfl, hB⟩
  · exact mem_relayedObjects_self _
  · exact gfVote_mem_relayedObjects_block hB

end

end

section

open Goldilocks

section

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- The wiring's dispatch of a delivered object keeps the record.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `o`: the object. -/
theorem receive_Λ (C : Config) (P : Provisional V) (X : External V) (n : NodeState V)
    (o : NamedObject V) : (Goldilocks.Sts.receive C P X n o).Λ = n.Λ := by
  cases o with
  | block B =>
      show (on_block C P X n B).Λ = _
      rw [on_block_eq]
      split <;> rfl
  | gfVote vote => rfl
  | attest a => exact on_attestation_Λ _ _

end

end

section

open GoldilocksCorrectness.Statements.Routines (carries)

section

open Goldilocks

section

open Goldilocks.Sts (relayedObjects)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

omit [DecidableEq V] [Fintype V] [RootOrder] in
/-- The objects the wiring re-sends for `o` are `o` and the objects `o` carries.

The variables:
- `o`: the delivered object; `o'`: an object. -/
theorem mem_relayedObjects_iff {o o' : NamedObject V} :
    o' ∈ relayedObjects o ↔ o' = o ∨ carries o o' := by
  cases o with
  | block B =>
      simp only [relayedObjects, carries, Multiset.mem_add, Multiset.mem_singleton,
        Multiset.mem_coe, List.mem_map]
      constructor
      · rintro ((h | ⟨vote, hv, rfl⟩) | ⟨a, ha, rfl⟩)
        · exact Or.inl h
        · exact Or.inr (Or.inl ⟨vote, hv, rfl⟩)
        · exact Or.inr (Or.inr ⟨a, ha, rfl⟩)
      · rintro (h | ⟨vote, hv, rfl⟩ | ⟨a, ha, rfl⟩)
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr ⟨vote, hv, rfl⟩)
        · exact Or.inr ⟨a, ha, rfl⟩
  | gfVote vote =>
      simp only [relayedObjects, carries, Multiset.mem_singleton, or_false]
  | attest a =>
      simp only [relayedObjects, carries, Multiset.mem_singleton, or_false]

end

end

end

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- The wiring's dispatch of a delivered object keeps `awakeSince`.

The variables:
- `C`, `P`, `X`: the parameters and the values; `n`: the node state; `o`: the object delivered.

Read aloud: a delivery does not change the time since which the node has been awake. -/
theorem receive_awakeSince (C : Config) (P : Provisional V) (X : External V) (n : NodeState V)
    (o : NamedObject V) : (Goldilocks.Sts.receive C P X n o).awakeSince = n.awakeSince := by
  cases o with
  | block B =>
      show (on_block C P X n B).awakeSince = _
      rw [on_block_eq]
      split <;> rfl
  | gfVote vote => rfl
  | attest a =>
      show (on_attestation n a).awakeSince = _
      simp only [on_attestation, Id.run]
      split <;> rfl

end

end GoldilocksCorrectness.Proofs.Routines
