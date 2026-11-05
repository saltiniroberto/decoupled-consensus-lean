module
public import GoldilocksCorrectness.Proofs.Routines.Accountable

@[expose] public section

/-!
# The statements about accountable safety at the chain level

The audited statements about the slashing conditions and the finalized blocks of two chains, each
proved in `GoldilocksCorrectness/Proofs/Routines/Accountable.lean`:

- a consistent anti-slashing record holds no E1 and no E2 pair;
- Lemma 68: a chain whose height passed the height at which another chain finalized a block holds
  that block, or `2q − n` validators hold E1 pairs across the two chains, or two different blocks
  of the two chains share a root;
- Lemma 69: of two chains, the one with the lower finalization height finalized the other's
  finalized block or an ancestor of it, or `2q − n` validators hold E1 or E2 pairs, or a root is
  shared;
- Lemma 70: two chains with conflicting finalized blocks leave `2q − n` slashable validators, or a
  shared root;
- Lemma 71: two justification certificates at one height leave `2q − n` validators with E2 pairs,
  or name blocks of one root.
-/

set_option autoImplicit false

open scoped DC

namespace GoldilocksCorrectness.Statements.Routines

open Goldilocks
open GoldilocksCorrectness.Statements.Routines (chainStateOf)

variable {V : Type} [DecidableEq V] [Fintype V]

omit [DecidableEq V] [Fintype V] in
/-- **A consistent record forbids the slashing conditions.** Two attestations whose contents a
consistent anti-slashing record holds form no E1 and no E2 pair.

Why: a consistent record holds no two target contents at one height for different blocks
(`oneTarget`), and every content it holds at the height of a finality pair it holds names that
pair's block (`lockKept`).

The variables:
- `Λ`: the record; `a`, `a'`: the two attestations.

Read aloud: two attestations whose contents a consistent record holds form no E1 and no E2 pair.

 -/
theorem no_slashable_of_consistent (Λ : SigningHistory) (hΛ : RecordConsistent Λ)
    (a a' : Attestation V)
    -- the record holds the content of `a`
    (ha : a.content ∈ Λ.sent)
    -- the record holds the content of `a'`
    (ha' : a'.content ∈ Λ.sent) :
    ¬ E1 a a' ∧ ¬ E2 a a' :=
  GoldilocksCorrectness.Proofs.Routines.no_slashable_of_consistent Λ hΛ a a' ha ha'

/-- **Lemma 68, past finalized.** When the height of the chain state of `B'` is greater than the
finalization height of the chain state of `B`, the finalized block of `B`'s chain state is `B'` or
an ancestor of `B'`; or at least `2 * quorum V - validator_count V` validators each signed an
attestation with that finality pair included on the chain of `B` and a vote at its height for
another block included on the chain of `B'`; or two different blocks of the two chains share a
root.

Why: at finalization height `0` the finalized block is the genesis block. Otherwise the finality
certificate of Lemma 66 is a quorum on the chain of `B`, and the block of `B'`'s chain that raised
the height past the finalization height carries a progress certificate at that height (Lemma 67),
a quorum of votes naming one block; the two quorums meet in `2q − n` validators (Lemma 65), and
when the voted block's root is the finalized block's, the two blocks are one.

The variables:
- `C`: the parameters; `B`, `B'`: the two blocks.

Read aloud: a chain whose height passed the height at which another chain finalized a block holds
that block, or at least `2q − n` validators each signed an E1 pair across the two chains, or two
different blocks of the two chains share a root.

 -/
theorem lem68_past_finalized (C : Config) (B B' : Block V)
    -- the height of the chain state of `B'` is greater than the finalization height of `B`'s
    (hlt : (chainStateOf C B).h_F < (chainStateOf C B').h) :
    (chainStateOf C B).F.AncestorEq B' ∨
      (∃ A : Finset V, 2 * quorum V - validator_count V ≤ |A| ∧
        ∀ v ∈ A, ∃ a a' : Attestation V, a.val_index = v ∧ a'.val_index = v ∧
          on_chain a B = true ∧ on_chain a' B' = true ∧ E1 a a') ∨
      RootCollisionOn B B' :=
  GoldilocksCorrectness.Proofs.Routines.lem68_past_finalized C B B' hlt

/-- **Lemma 69, finalized chain.** When the finalization height of the chain state of `B` is at
most that of `B'`, the finalized block of `B`'s chain state is that of `B'`'s or an ancestor of
it; or at least `2 * quorum V - validator_count V` validators each signed an attestation included
on the chain of `B` and one included on the chain of `B'` that together meet E1 or E2; or two
different blocks of the two chains share a root.

Why: at finalization height `0` the finalized block is the genesis block. When the heights
differ, Lemma 68 places the lower finalized block on the other chain, where it is an ancestor of
the other finalized block since the chain-state heights grow along a chain. When they are equal,
the two justification certificates at that height leave `2q − n` E2 pairs or name one root
(Lemma 71).

The variables:
- `C`: the parameters; `B`, `B'`: the two blocks.

Read aloud: when the first chain's finalization height is at most the second's, the first chain's
finalized block is the second's or an ancestor of it, or at least `2q − n` validators each signed
an E1 or E2 pair across the two chains, or two different blocks of the two chains share a root.

 -/
theorem lem69_finalized_chain (C : Config) (B B' : Block V)
    -- the finalization height of `B`'s chain state is at most `B'`'s
    (hle : (chainStateOf C B).h_F ≤ (chainStateOf C B').h_F) :
    (chainStateOf C B).F.AncestorEq (chainStateOf C B').F ∨
      (∃ A : Finset V, 2 * quorum V - validator_count V ≤ |A| ∧
        ∀ v ∈ A, ∃ a a' : Attestation V, a.val_index = v ∧ a'.val_index = v ∧
          on_chain a B = true ∧ on_chain a' B' = true ∧ (E1 a a' ∨ E2 a a')) ∨
      RootCollisionOn B B' :=
  GoldilocksCorrectness.Proofs.Routines.lem69_finalized_chain C B B' hle

/-- **Lemma 70, accountable safety at the chain level.** When the finalized blocks of the chain
states of `B` and `B'` are not compatible (neither is the other or an ancestor of the other),
`SlashableBetween B B'` holds, or two different blocks of the two chains share a root.

Why: Lemma 69 in the order of the two finalization heights; its first disjunct makes the two
finalized blocks compatible.

The variables:
- `C`: the parameters; `B`, `B'`: the two blocks.

Read aloud: when the blocks two chains finalized conflict, at least `2q − n` validators each signed
two attestations, one included on each chain, meeting E1 or E2, or two different blocks of the two
chains share a root.

 -/
theorem lem70_accountable_safety_chain (C : Config) (B B' : Block V)
    -- neither finalized block is the other or an ancestor of the other
    (hConflict : (chainStateOf C B).F.compatible (chainStateOf C B').F = false) :
    SlashableBetween B B' ∨ RootCollisionOn B B' :=
  GoldilocksCorrectness.Proofs.Routines.lem70_accountable_safety_chain C B B' hConflict

/-- **Lemma 71, one justification per height.** A justification certificate at the height `h` for
`T` on the chain of `B` and one for `T'` on the chain of `B'` leave at least
`2 * quorum V - validator_count V` validators each with a target vote at `h` included on the chain
of `B` and one included on the chain of `B'`, for different blocks; or `T` and `T'` have the same
root.

Why: the two quorums meet in `2q − n` validators (Lemma 65), and each of them voted at `h` for
`T`'s root on one chain and for `T'`'s on the other.

The variables:
- `B`, `B'`: the two blocks whose chains hold the certificates; `h`: the height; `T`, `T'`: the
  blocks the certificates name.

Read aloud: two justification certificates at one height, on two chains, for `T` and `T'`: at
least `2q − n` validators each signed an E2 pair across the two chains, or `T` and `T'` have the
same root.

 -/
theorem lem71_one_justification_per_height (B B' : Block V) (h : Height) (T T' : Block V)
    -- a justification certificate at `h` for `T` on the chain of `B`
    (hJ : JustificationCertOn B h T)
    -- a justification certificate at `h` for `T'` on the chain of `B'`
    (hJ' : JustificationCertOn B' h T') :
    (∃ A : Finset V, 2 * quorum V - validator_count V ≤ |A| ∧
      ∀ v ∈ A, ∃ a a' : Attestation V, a.val_index = v ∧ a'.val_index = v ∧
        on_chain a B = true ∧ on_chain a' B' = true ∧ E2 a a') ∨
      T.root = T'.root :=
  GoldilocksCorrectness.Proofs.Routines.lem71_one_justification_per_height B B' h T T' hJ hJ'

end GoldilocksCorrectness.Statements.Routines
