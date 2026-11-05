module
public import GoldilocksCorrectness.Proofs.Routines.FinalityPair

@[expose] public section

/-!
# The statements about the finality pair, carried by an attestation and counted by a block

The audited statements about the finality pair an attestation carries, proved in
`GoldilocksCorrectness/Proofs/Routines/FinalityPair.lean`:

- Lemma 92, `lem92_attestation_carries_finality_pair`: an attestation built from a record clean
  at the justification height carries the finality pair of the justification;
- Lemma 93, `lem93_block_finalizes_pending`: a block whose parent's chain state has a pending
  justification, and that brings the finality pairs naming it to a quorum, has a finalization
  height at least the pending height.


-/

set_option autoImplicit false

open scoped DC

namespace GoldilocksCorrectness.Statements.Routines

open Goldilocks
open GoldilocksCorrectness.Statements.Routines (chainStateOf)

variable {V : Type} [DecidableEq V] [Fintype V]

omit [DecidableEq V] [Fintype V] in
/-- **Lemma 92, the attestation carries the finality pair.** When `create_attestation` with the
source's height `h_c` and root `T_c`, and the head's justification height `h_j`, justified root
`J` and finalization height `h_F`, builds an attestation `a`, `h_F < h_j < h_c`, and the record `Λ`
holds at `h_j` no target other than `J`, no timeout and no lock other than `J`, then `a` is at the
height `h_c` and carries the finality pair `(h_j, J)`.

Why: `finality_pair`'s four tests pass, so it returns `(h_j, J)`; `height_pair` gives a vote at
`h_c`; step 4 of `create_attestation` keeps the pair, its height `h_j` being less than `h_c`.

The variables:
- `Λ`: the anti-slashing record; `v`: the validator;
- `h_c`, `T_c`: the source's height and the root of the block that took the source into that
  height;
- `h_j`, `J`, `h_F`: the head's justification height, justified root and finalization height;
- `a`: the attestation built.

Read aloud: a clean record attaches the justification the head saw.

 -/
theorem lem92_attestation_carries_finality_pair (Λ : SigningHistory) (v : V)
    (h_c : Height) (T_c : BlockId) (h_j : Height) (J : BlockId) (h_F : Height)
    (a : Attestation V)
    -- `create_attestation` builds `a`
    (hSome : (create_attestation Λ v h_c T_c h_j J h_F).2 = some a)
    -- the head's justification is not finalized
    (hlt : h_F < h_j)
    -- the justification height is less than the source's height
    (hj : h_j < h_c)
    -- the record holds at `h_j` no target, or the target `J`
    (hTarget : Λ.target h_j = none ∨ Λ.target h_j = some J)
    -- the record holds no timeout at `h_j`
    (hTimeout : Λ.timeout h_j = false)
    -- the record holds at `h_j` no lock, or the lock `J`
    (hLock : Λ.lock h_j = none ∨ Λ.lock h_j = some J) :
    a.h = h_c ∧ a.finality_pair = some (FinalityPair.mk h_j J) :=
  GoldilocksCorrectness.Proofs.Routines.lem92_attestation_carries_finality_pair Λ v h_c T_c h_j J
    h_F a hSome hlt hj hTarget hTimeout hLock

/-- **Lemma 93, a block including a quorum of finality pairs finalizes the pair.** When the chain
state of `B`'s parent `H'` has a pending justification at the height `j` naming the block `T`, and
every member `v` of a quorum `Q` is counted in the parent's finality participation at `j` or has
an attestation included in `B` with the finality pair `(j, T.root)`, the chain state of `B` has a
finalization height at least `j`.

Why: counting `B`'s attestations adds every such `v` to the finality participation at `j` (the
pair names a pending justification) and keeps those already there, so the participation at `j` is
a quorum; the pending justifications are in strictly increasing order of heights, so the first
step of `process_height_events` leaves the quorate pending justification of greatest height, at a
height at least `j`; nothing after it writes `h_F`.

The variables:
- `C`: the parameters; `B`: the block; `H'`: its parent;
- `j`, `T`: the height and the block of the pending justification; `Q`: the quorum.

Read aloud: a quorum's finality pairs finalize what they name.

 -/
theorem lem93_block_finalizes_pending (C : Config) (B H' : Block V) (j : Height) (T : Block V)
    (Q : Finset V)
    -- `H'` is `B`'s parent
    (hParent : B.parent = H')
    -- the parent's chain state has a pending justification at `j` naming `T`
    (hPending : ∃ e ∈ (chainStateOf C H').pending_finality, e.j = j ∧ e.T = T)
    -- `Q` is a quorum
    (hQ : quorum V ≤ |Q|)
    -- every member of `Q` is counted at `j` in the parent's chain state, or has an attestation
    -- included in `B` with the finality pair `(j, T.root)`
    (hAtts : ∀ v ∈ Q, v ∈ (chainStateOf C H').finality_participation j ∨
      ∃ a ∈ B.attestations, a.val_index = v ∧ a.finality_pair = some (FinalityPair.mk j T.root)) :
    j ≤ (chainStateOf C B).h_F :=
  GoldilocksCorrectness.Proofs.Routines.lem93_block_finalizes_pending C B H' j T Q hParent
    hPending hQ hAtts

end GoldilocksCorrectness.Statements.Routines
