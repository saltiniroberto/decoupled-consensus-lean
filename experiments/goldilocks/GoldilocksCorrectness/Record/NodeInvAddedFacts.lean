module
public import GoldilocksCorrectness.Record.ModelSpellings
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.FGStateDefs

@[expose] public section

/-!
# The readers that read the stored chain states and the stored greatest height, under the node invariant

`NodeInvAddedFacts M` holds, for a model `M`, the defining equations of the six readers of a node
state that the spec computes from the node's stored chain states or its stored greatest chain-state
height: `fg_contest`, `head_height_floor`, `get_fc_root`, `is_viable`, `proposal_attestations` and
`block_admissible`. Each is stated for a node state `n` satisfying the model's node invariant
`M.nodeInv C P X n`, with the chain state of a block written `M.chainStateOf C B` and the greatest
chain-state height of the tree written `hMax M C n`; `is_viable` and `proposal_attestations` also
take the block they read to be in `n`'s tree. These are consequences of the node invariant, added
beside `NodeInvFacts` (whose fields are not changed). This file holds the structure only.
-/

set_option autoImplicit false

open scoped DC

namespace GoldilocksCorrectness.Record

open Goldilocks (Config Provisional External Block Attestation)
open GoldilocksCorrectness.Record.Statements.Routines (hMax)

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The defining equations of the six readers of a node state that read its stored chain states or
its stored greatest height, under the model's node invariant.

Read aloud: on a node state satisfying the invariant, the contest test, the least height of a
viable block, the fgroot, viability, the attestations a proposal includes and the admission test of
a block are what the chain states of the blocks and the greatest height of the tree say. -/
structure NodeInvAddedFacts (M : GoldilocksModel V) : Prop where
  /-- On a node state `n` satisfying the model's node invariant, `M.fg_contest n` is false when the
      greatest chain-state height `hMax M C n` of `n`'s tree is not `n.justifiedHeight + 1`, and
      otherwise answers whether some block `B` of the tree, `n.finalized` or a descendant of it, has
      the chain-state height `hMax M C n` and is neither `n.justified` nor a descendant of it.

      Read aloud: under the invariant, the node is contested when its greatest height is one more
      than its justification height and some block of that height on the finalized block's chain is
      off the justified block's chain. -/
  fg_contest_eq : ∀ {C : Config} {P : Provisional V} {X : External V} {n : M.N},
    M.nodeInv C P X n →
      M.fg_contest n = if hMax M C n ≠ n.justifiedHeight + 1 then false
        else decide (∃ B ∈ n.tree, n.finalized.ancestorEq B ∧
          (M.chainStateOf C B).h = hMax M C n ∧ ¬ n.justified.ancestorEq B)

  /-- On a node state `n` satisfying the clock-free part of the node invariant,
      `M.nodeInvCore C P X n`, `M.fg_contest n` is false when the greatest height `hMax M C n` is not
      one more than the justification height, and otherwise answers whether some block `B` of the
      tree, `n.finalized` or a descendant of it, has the chain-state height `hMax M C n` and is
      neither `n.justified` nor a descendant of it. Added for a validator in the adversary set, for
      which only the clock-free part of Lemma 11 holds.

      Read aloud: under the clock-free part, the node is contested when its greatest height is one
      more than its justification height and some block of that height on the finalized block's
      chain is off the justified block's chain. -/
  fg_contest_eq_of_core : ∀ {C : Config} {P : Provisional V} {X : External V} {n : M.N},
    M.nodeInvCore C P X n →
      M.fg_contest n = if hMax M C n ≠ n.justifiedHeight + 1 then false
        else decide (∃ B ∈ n.tree, n.finalized.ancestorEq B ∧
          (M.chainStateOf C B).h = hMax M C n ∧ ¬ n.justified.ancestorEq B)

  /-- On a node state `n` satisfying the model's node invariant, `M.head_height_floor n` is
      `hMax M C n` when `M.fg_contest n` holds, and `hMax M C n - 1` otherwise.

      Read aloud: under the invariant, the least chain-state height a viable block may have is the
      tree's greatest height when the node is contested, and one less otherwise. -/
  head_height_floor_eq : ∀ {C : Config} {P : Provisional V} {X : External V} {n : M.N},
    M.nodeInv C P X n →
      M.head_height_floor n = if M.fg_contest n then hMax M C n else hMax M C n - 1

  /-- On a node state `n` satisfying the clock-free part of the node invariant,
      `M.nodeInvCore C P X n`, `M.head_height_floor n` is `hMax M C n` when `M.fg_contest n` holds,
      and `hMax M C n - 1` otherwise. Added for a validator in the adversary set, for which only the
      clock-free part of Lemma 11 holds.

      Read aloud: under the clock-free part, the least chain-state height a viable block may have
      is the tree's greatest height when the node is contested, and one less otherwise. -/
  head_height_floor_eq_of_core : ∀ {C : Config} {P : Provisional V} {X : External V} {n : M.N},
    M.nodeInvCore C P X n →
      M.head_height_floor n = if M.fg_contest n then hMax M C n else hMax M C n - 1

  /-- On a node state `n` satisfying the model's node invariant, the fgroot `M.get_fc_root n` is
      `n.justified` when `hMax M C n = n.justifiedHeight + 1` and `M.fg_contest n` is false, and
      `n.finalized` otherwise.

      Read aloud: under the invariant, the fgroot is the justified block when the greatest height
      is one more than the justification height and the node is not contested, and the finalized
      block otherwise. -/
  get_fc_root_eq : ∀ {C : Config} {P : Provisional V} {X : External V} {n : M.N},
    M.nodeInv C P X n →
      M.get_fc_root n =
        if hMax M C n = n.justifiedHeight + 1 && !M.fg_contest n then n.justified else n.finalized

  /-- On a node state `n` satisfying the clock-free part of the node invariant,
      `M.nodeInvCore C P X n`, the fgroot `M.get_fc_root n` is `n.justified` when
      `hMax M C n = n.justifiedHeight + 1` and `M.fg_contest n` is false, and `n.finalized`
      otherwise. Added for a validator in the adversary set, for which only the clock-free part of
      Lemma 11 holds.

      Read aloud: under the clock-free part, the fgroot is the justified block when the greatest
      height is one more than the justification height and the node is not contested, and the
      finalized block otherwise. -/
  get_fc_root_eq_of_core : ∀ {C : Config} {P : Provisional V} {X : External V} {n : M.N},
    M.nodeInvCore C P X n →
      M.get_fc_root n =
        if hMax M C n = n.justifiedHeight + 1 && !M.fg_contest n then n.justified else n.finalized

  /-- On a node state `n` satisfying the model's node invariant, a block `B` of `n`'s tree is viable
      exactly when `M.head_height_floor n` is at most its chain-state height
      `(M.chainStateOf C B).h`.

      Read aloud: under the invariant, a block of the tree is viable when its chain-state height is
      at least the least height a viable block may have. -/
  is_viable_eq : ∀ {C : Config} {P : Provisional V} {X : External V} {n : M.N} {B : Block V},
    M.nodeInv C P X n → B ∈ n.tree →
      M.is_viable n B = decide (M.head_height_floor n ≤ (M.chainStateOf C B).h)

  /-- On a node state `n` satisfying the clock-free part of the node invariant,
      `M.nodeInvCore C P X n`, a block `B` of `n`'s tree is viable exactly when
      `M.head_height_floor n` is at most its chain-state height `(M.chainStateOf C B).h`. Added for a
      validator in the adversary set, for which only the clock-free part of Lemma 11 holds
.

      Read aloud: under the clock-free part, a block of the tree is viable when its chain-state
      height is at least the least height a viable block may have. -/
  is_viable_eq_of_core : ∀ {C : Config} {P : Provisional V} {X : External V} {n : M.N}
    {B : Block V}, M.nodeInvCore C P X n → B ∈ n.tree →
      M.is_viable n B = decide (M.head_height_floor n ≤ (M.chainStateOf C B).h)

  /-- On a node state `n` satisfying the model's node invariant, a proposal on a block `H` of `n`'s
      tree includes, in the order `n` holds them, the attestations `n` holds that are valid against
      `H`'s chain state `M.chainStateOf C H` and not included on `H`'s chain.

      Read aloud: under the invariant, a proposal on a block of the tree includes the held
      attestations valid against that block's chain state and not yet on its chain. -/
  proposal_attestations_eq :
    ∀ {C : Config} {P : Provisional V} {X : External V} {n : M.N} {H : Block V},
    M.nodeInv C P X n → H ∈ n.tree →
      M.proposal_attestations n H =
        n.attestationsHeld.filter
          (fun a => M.valid_attestation (M.chainStateOf C H) a && !M.on_chain a H)

  /-- On a node state `n` satisfying the model's node invariant, the node admits a block `B` exactly
      when `B` is well formed; its slot is at most the slot of `n`'s clock; no block of the tree
      has `B`'s root; the tree holds `B`'s parent; `n.finalized` is `B` or an ancestor of `B`; `B`'s
      proposer is its slot's; its parent's slot is earlier than its own; and every attestation `B`
      includes is valid against the chain state `M.chainStateOf C B.parent` of its parent.

      Read aloud: under the invariant, a node admits a well-formed block of a slot it has reached,
      with a new root, its parent held, on the finalized block's chain, from its slot's proposer,
      of a later slot than its parent, whose attestations are valid against its parent's chain
      state. -/
  block_admissible_iff :
    ∀ {C : Config} {P : Provisional V} {X : External V} {n : M.N} (B : Block V),
    M.nodeInv C P X n →
      (M.block_admissible C P X n B = true ↔
        M.block_well_formed P X B = true ∧ B.slot ≤ C.slot n.t ∧
          (∀ B' ∈ n.tree, B'.root ≠ B.root) ∧ B.parent ∈ n.tree ∧
          n.finalized.AncestorEq B ∧ B.proposer? = some (P.proposer B.slot) ∧
          B.parent.slot < B.slot ∧
          ∀ a ∈ B.attestations, M.valid_attestation (M.chainStateOf C B.parent) a = true)

end GoldilocksCorrectness.Record
