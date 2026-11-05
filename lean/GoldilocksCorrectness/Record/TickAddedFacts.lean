module
public import GoldilocksCorrectness.Record.ModelSpellings
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.FGCachesDefs

@[expose] public section

/-!
# The tick: the relations that read the greatest height

`TickAddedFacts M` holds, for a model `M`, three facts of a tick added beside `TickFacts1` (whose
fields are not changed, and which parts 2 and 3 of the tick's family leave unchanged as well):
from a node state satisfying the model's node invariant, a tick keeps the witnesses of the node's
justification and greatest chain-state height (`CachesWitnessed`), moves the finalized block
only to `D`'s finalized block or a descendant of it when a block `D` enters the tree on a node
ready for it (`ReadyFor`), and never lowers the justified height. The two relations are written out, as the landed `WitnessedFrom` and
`ReachFrom` say them, over the record's readers and the greatest chain-state height `hMax`. This
file holds the structure only.
-/

set_option autoImplicit false

open scoped DC

namespace GoldilocksCorrectness.Record

open Goldilocks (Config Provisional External RootOrder Block NamedObject Time)
open GoldilocksCorrectness.Record.Proofs.Routines (CachesWitnessed ReadyFor)

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The facts of `M` about the outcomes of a tick added beside `TickFacts1`.

Read aloud: a tick keeps the witnesses of the node's caches and finalizes along the chains it is
ready for. -/
structure TickAddedFacts (M : GoldilocksModel V) : Prop where
  /-- From a node state `n` satisfying the model's node invariant, a tick at a time `t` no earlier
      than `n`'s clock gives a node state whose tree holds `n`'s, and which satisfies
      `CachesWitnessed M C` when `n` does (the landed `WitnessedFrom`).

      Read aloud: a tick keeps the node's justification and its greatest chain-state height
      witnessed by blocks of its tree. -/
  tick_witnessedFrom : ∀ [RootOrder] (C : Config) (P : Provisional V) (X : External V) (n : M.N)
      (t : Time) (n' : M.N) (sent : List (NamedObject V)),
    .ok (n', sent) ∈ M.tick C P X n t → M.nodeInv C P X n → n.t ≤ t →
      n.tree ⊆ n'.tree ∧ (CachesWitnessed M C n → CachesWitnessed M C n')
  /-- From a node state `n` satisfying the model's node invariant, a tick gives a node state whose
      tree holds `n`'s and whose finalized block is `n`'s or a descendant of it; and when a block
      `D` enters the tree on the tick and `n` is ready for `D` (`ReadyFor M C D n`), the finalized
      block after it is the finalized block of `D`'s chain state or a descendant of it (the landed
      `ReachFrom`).

      Read aloud: a tick finalizes along the chain of a block it accepts when the node was ready
      for that block. -/
  tick_reachFrom : ∀ [RootOrder] (C : Config) (P : Provisional V) (X : External V) (D : Block V)
      (n : M.N) (t : Time) (n' : M.N) (sent : List (NamedObject V)),
    .ok (n', sent) ∈ M.tick C P X n t → M.nodeInv C P X n →
      n.tree ⊆ n'.tree ∧ n.finalized.AncestorEq n'.finalized ∧
        (D ∉ n.tree → D ∈ n'.tree → ReadyFor M C D n →
          (M.chainStateOf C D).F.AncestorEq n'.finalized)
  /-- A tick never lowers the justified height: from a node state `n` satisfying the model's node
      invariant, a tick at a time `t` no earlier than `n`'s clock gives a node state whose
      `justifiedHeight` is at least `n`'s.
      Read aloud: an honest tick never lowers the justified height. -/
  tick_justifiedHeight_mono : ∀ [RootOrder] (C : Config) (P : Provisional V) (X : External V) (n : M.N)
      (t : Time) (n' : M.N) (sent : List (NamedObject V)),
    .ok (n', sent) ∈ M.tick C P X n t → M.nodeInv C P X n → n.t ≤ t →
      M.justifiedHeight n ≤ M.justifiedHeight n'
  /-- A tick never lowers the justified height, under the clock-free part of the node invariant
      and at any time: from a node state `n` satisfying `M.nodeInvCore C P X n`, a tick at a time `t`
      gives a node state whose `justifiedHeight` is at least `n`'s. Added for a validator in the
      adversary set, for which only the clock-free part of Lemma 11 holds and whose clock may go back
.
      Read aloud: a tick never lowers the justified height, whatever the clock. -/
  tick_justifiedHeight_mono_of_core : ∀ [RootOrder] (C : Config) (P : Provisional V) (X : External V)
      (n : M.N) (t : Time) (n' : M.N) (sent : List (NamedObject V)),
    .ok (n', sent) ∈ M.tick C P X n t → M.nodeInvCore C P X n →
      M.justifiedHeight n ≤ M.justifiedHeight n'

end GoldilocksCorrectness.Record
