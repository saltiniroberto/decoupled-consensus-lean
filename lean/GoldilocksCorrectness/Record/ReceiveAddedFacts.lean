module
public import GoldilocksCorrectness.Record.ModelSpellings
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.FGCachesDefs

@[expose] public section

/-!
# The receipt: the admission of a block, and the relations that read the greatest height

`ReceiveAddedFacts M` holds, for a model `M`, five facts of a delivery added beside `ReceiveFacts`
(whose fields are not changed): a delivered block enters the tree exactly when the node admits it
(`M.block_admissible`); an admitted block is stamped with the clock; and, from a node state
satisfying the model's node invariant, a delivery keeps the witnesses of the node's justification
and greatest chain-state height (`CachesWitnessed`), moves the finalized block only to `D`'s
finalized block or a descendant of it when a block `D` enters the tree on a node ready for it
(`ReadyFor`), and never lowers the justified height. The two relations are written out, as the landed `WitnessedFrom` and `ReachFrom` say
them, over the record's readers and the greatest chain-state height `hMax`. This file holds
the structure only.
-/

set_option autoImplicit false

open scoped DC

namespace GoldilocksCorrectness.Record

open Goldilocks (Config Provisional External RootOrder Block NamedObject Stamp)
open GoldilocksCorrectness.Record.Proofs.Routines (CachesWitnessed ReadyFor)

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The facts of `M` about the node state after a delivery added beside `ReceiveFacts`.

Read aloud: a delivered block enters the tree when the node admits it, stamped with the clock; and
a delivery keeps the witnesses of the node's caches and finalizes along the chains it is ready for. -/
structure ReceiveAddedFacts (M : GoldilocksModel V) : Prop where
  /-- After the delivery of a block `B`, a block `B'` is in the tree exactly when it was in `n`'s
      tree, or it is `B` and the node admits `B`.

      Read aloud: a delivered block enters the tree when the node admits it, and nothing else
      does. -/
  mem_tree_receive_block : ∀ [RootOrder] (C : Config) (P : Provisional V) (X : External V)
      (n : M.N) (B B' : Block V),
    B' ∈ (M.receive C P X n (NamedObject.block B)).tree ↔
      B' ∈ n.tree ∨ (B' = B ∧ M.block_admissible C P X n B = true)
  /-- A block `B` the node admits is stamped, after its delivery, with the node's clock `n.t`.

      Read aloud: an admitted block is stamped with the clock. -/
  receive_block_stamped : ∀ [RootOrder] (C : Config) (P : Provisional V) (X : External V)
      (n : M.N) (B : Block V),
    M.block_admissible C P X n B = true →
      (M.receive C P X n (NamedObject.block B)).blockStamp B = some (n.t : Stamp)
  /-- From a node state `n` satisfying the model's node invariant, a delivery gives a node state
      whose tree holds `n`'s, and which satisfies `CachesWitnessed M C` when `n` does (the landed
      `WitnessedFrom`).

      Read aloud: a delivery keeps the node's justification and its greatest chain-state height
      witnessed by blocks of its tree. -/
  receive_witnessedFrom : ∀ [RootOrder] (C : Config) (P : Provisional V) (X : External V)
      (n : M.N) (o : NamedObject V),
    M.nodeInv C P X n →
      n.tree ⊆ (M.receive C P X n o).tree ∧
        (CachesWitnessed M C n → CachesWitnessed M C (M.receive C P X n o))
  /-- From a node state `n` satisfying the model's node invariant, a delivery gives a node state
      whose tree holds `n`'s and whose finalized block is `n`'s or a descendant of it; and when a
      block `D` enters the tree on the delivery and `n` is ready for `D` (`ReadyFor M C D n`), the
      finalized block after it is the finalized block of `D`'s chain state or a descendant of it
      (the landed `ReachFrom`).

      Read aloud: a delivery finalizes along the chain of a block it accepts when the node was
      ready for that block. -/
  receive_reachFrom : ∀ [RootOrder] (C : Config) (P : Provisional V) (X : External V)
      (D : Block V) (n : M.N) (o : NamedObject V),
    M.nodeInv C P X n →
      n.tree ⊆ (M.receive C P X n o).tree ∧
        n.finalized.AncestorEq (M.receive C P X n o).finalized ∧
        (D ∉ n.tree → D ∈ (M.receive C P X n o).tree → ReadyFor M C D n →
          (M.chainStateOf C D).F.AncestorEq (M.receive C P X n o).finalized)
  /-- A delivery never lowers the justified height: from a node state `n` satisfying the model's
      node invariant, a delivery of an object `o` gives a node state whose `justifiedHeight` is at
      least `n`'s.
      Read aloud: an honest delivery never lowers the justified height. -/
  receive_justifiedHeight_mono : ∀ [RootOrder] (C : Config) (P : Provisional V) (X : External V)
      (n : M.N) (o : NamedObject V),
    M.nodeInv C P X n →
      M.justifiedHeight n ≤ M.justifiedHeight (M.receive C P X n o)
  /-- A delivery never lowers the justified height, under the clock-free part of the node
      invariant: from a node state `n` satisfying `M.nodeInvCore C P X n`, a delivery of an object
      `o` gives a node state whose `justifiedHeight` is at least `n`'s. Added for a validator in the
      adversary set, for which only the clock-free part of Lemma 11 holds.
      Read aloud: a delivery never lowers the justified height. -/
  receive_justifiedHeight_mono_of_core : ∀ [RootOrder] (C : Config) (P : Provisional V)
      (X : External V) (n : M.N) (o : NamedObject V),
    M.nodeInvCore C P X n →
      M.justifiedHeight n ≤ M.justifiedHeight (M.receive C P X n o)

end GoldilocksCorrectness.Record
