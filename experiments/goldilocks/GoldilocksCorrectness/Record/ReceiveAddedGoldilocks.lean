module
public import GoldilocksCorrectness.Record.ReceiveAddedFacts
public import GoldilocksCorrectness.Record.ModelGoldilocks
public import GoldilocksCorrectness.Record.NodeInvGoldilocks
public import GoldilocksCorrectness.Record.NodeInvAddedGoldilocks
public import GoldilocksCorrectness.Proofs.Routines.Wiring
public import GoldilocksCorrectness.Proofs.Routines.ACInterface
public import GoldilocksCorrectness.Record.TickAddedGoldilocks
import all Goldilocks.Node

@[expose] public section

/-!
# The spec's receipt: the admission of a block, and the relations that read the greatest height

`receiveAddedFacts_goldilocks`: the spec's model satisfies `ReceiveAddedFacts`. A delivered block
goes to `on_block`, which accepts it into the FG state (`fg_on_block`, whose tree is the old one
with the block) and admits it into the AC state at the clock (`ac_on_block`, which stamps it) when
`block_admissible` holds, and changes nothing otherwise (`on_block_eq`). The two relations are the
landed `receive_witnessedFrom` and `receive_reachFrom`, read through the equivalences of
`CachesWitnessed` and `ReadyFor` at the spec's model, whose hypothesis (the stored greatest height
is `hMax`) the node invariant gives before and after the delivery (`hMax_goldilocks`, and the
field `receive_nodeInv` of `nodeInvFacts_goldilocks`). The justification height does not decrease
along a delivery: a block goes through `on_block` (`on_block_h_j_le`), an attestation through
`on_attestation`, which keeps it, and a Goldfish vote reaches the AC state only.
-/

set_option autoImplicit false

namespace GoldilocksCorrectness.Record

open Goldilocks (Stamp)
open GoldilocksCorrectness.Record.Proofs.Routines (goldilocks_CachesWitnessed goldilocks_ReadyFor)

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The spec's model satisfies the added facts of the receipt.

Read aloud: Goldilocks' delivery admits a block into the tree when it passes the test, stamps it
with the clock, keeps the witnesses of its caches, finalizes along the chains it is ready for, and
never lowers its justified height. -/
theorem receiveAddedFacts_goldilocks : ReceiveAddedFacts (Model.goldilocks (V := V)) where
  mem_tree_receive_block C P X n B B' := by
    show B' ∈ (Goldilocks.on_block C P X n B).S.T ↔
      B' ∈ n.S.T ∨ (B' = B ∧ Goldilocks.block_admissible C P X n B = true)
    rw [GoldilocksCorrectness.Proofs.Routines.on_block_eq]
    split
    · rename_i ha
      show B' ∈ (Goldilocks.fg_on_block C n.S B).T ↔ _
      rw [(GoldilocksCorrectness.Proofs.Routines.fg_on_block_eq C n.S B).1]
      simp [ha, or_comm]
    · rename_i ha
      simp [ha]
  receive_block_stamped C P X n B h := by
    show (Goldilocks.on_block C P X n B).A.timestamp_block B = some (n.t : Stamp)
    rw [GoldilocksCorrectness.Proofs.Routines.on_block_eq,
      if_pos (show Goldilocks.block_admissible C P X n B = true from h)]
    show (Goldilocks.ac_on_block C P n.A n.t B).timestamp_block B = some (n.t : Stamp)
    rw [GoldilocksCorrectness.Proofs.Routines.ac_on_block_timestamp_block]
    exact Function.update_self _ _ _
  receive_witnessedFrom C P X n o h := by
    have h' := (nodeInvFacts_goldilocks.receive_nodeInv C P X n o h).1
    have hw := GoldilocksCorrectness.Proofs.Routines.receive_witnessedFrom C P X n o
      h.1.2.2.2.2.2.1
    exact ⟨hw.1, fun hc =>
      (goldilocks_CachesWitnessed C _ (hMax_goldilocks h').symm).1
        (hw.2 ((goldilocks_CachesWitnessed C n (hMax_goldilocks h).symm).2 hc))⟩
  receive_reachFrom C P X D n o h := by
    have hr := GoldilocksCorrectness.Proofs.Routines.receive_reachFrom C P X D n o
    exact ⟨hr.1, hr.2.1, fun h1 h2 h3 =>
      hr.2.2 h1 h2 ((goldilocks_ReadyFor C D n h.1.2.2.2.2.2.1 (hMax_goldilocks h).symm).2 h3)⟩
  receive_justifiedHeight_mono C P X n o _ := by
    show n.S.h_j ≤ (Goldilocks.Sts.receive C P X n o).S.h_j
    cases o with
    | block B => exact on_block_h_j_le C P X n B
    | gfVote vote => exact le_rfl
    | attest a =>
        exact le_of_eq (GoldilocksCorrectness.Proofs.Routines.on_attestation_caches n a).2.2.1.symm
  receive_justifiedHeight_mono_of_core C P X n o _ := by
    show n.S.h_j ≤ (Goldilocks.Sts.receive C P X n o).S.h_j
    cases o with
    | block B => exact on_block_h_j_le C P X n B
    | gfVote vote => exact le_rfl
    | attest a =>
        exact le_of_eq (GoldilocksCorrectness.Proofs.Routines.on_attestation_caches n a).2.2.1.symm

end GoldilocksCorrectness.Record
