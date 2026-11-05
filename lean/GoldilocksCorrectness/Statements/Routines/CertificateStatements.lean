module
public import GoldilocksCorrectness.Proofs.Routines.Certificates

@[expose] public section

/-!
# The statements about the certificates of a chain state

The audited statements about quorums and the certificates a chain state rests on, proved in
`GoldilocksCorrectness/Proofs/Routines/Certificates.lean`:

- Lemma 65 and Lemma 65 (b): two quorums share at least `2q − n` validators, and `2q − n` is at
  least a third of the validators;
- Lemma 66: the justified block, every pending justification and the finalized block of a chain
  state have their certificates on the chain;
- Lemma 67: a chain whose height passed `h` has a block that raised the height from `h` to
  `h + 1`, with a progress certificate at `h`.
-/

set_option autoImplicit false

open scoped DC

namespace GoldilocksCorrectness.Statements.Routines

open Goldilocks
open GoldilocksCorrectness.Statements.Routines (chainStateOf)

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Lemma 65, quorum intersection -/

/-- **Lemma 65, quorum intersection.** Two quorums `A` and `A'` share at least
`2 * quorum V - validator_count V` validators.

Why: `|A ∪ A'| + |A ∩ A'| = |A| + |A'|`, and `|A ∪ A'|` is at most the number of validators.

The variables:
- `A`, `A'`: the two sets of validators.

Read aloud: two quorums share at least `2q − n` validators.

 -/
theorem lem65_quorum_intersection (A A' : Finset V)
    -- `A` is a quorum
    (hA : quorum V ≤ |A|)
    -- `A'` is a quorum
    (hA' : quorum V ≤ |A'|) :
    2 * quorum V - validator_count V ≤ |A ∩ A'| :=
  GoldilocksCorrectness.Proofs.Routines.lem65_quorum_intersection A A' hA hA'

omit [DecidableEq V] in
/-- **Lemma 65 (b), the intersection threshold.** The number of validators is at most three
times `2 * quorum V - validator_count V`, and at most twice the quorum.

Why: `quorum V = (2 * validator_count V + 2) / 3`.

Read aloud: `2q − n` is at least a third of the validators, and the subtraction truncates nothing.

 -/
theorem lem65b_quorum_threshold :
    validator_count V ≤ 3 * (2 * quorum V - validator_count V) ∧
      validator_count V ≤ 2 * quorum V :=
  GoldilocksCorrectness.Proofs.Routines.lem65b_quorum_threshold

/-! ## Lemma 66, the certificates behind a chain state -/

/-- **Lemma 66, the certificates behind a chain state.** For the chain state of `B`: when its
justification height is at least `1`, its justified block has a justification certificate at that
height on `B`'s chain, is `B` or an ancestor of `B`, and has its own chain state at that height;
every pending justification likewise; and when its finalization height is at least `1`, its
finalized block has a justification and a finality certificate at that height on `B`'s chain, is
`B` or an ancestor of `B`, and has its own chain state at that height.

Why: by induction on `B`, every validator a chain state counts has its attestation included on
the chain; a justification is written from a quorum of target votes, a finalization from a
pending justification whose finality participation is a quorum, and the pending heights are
strictly increasing, so that participation is read against one pending justification.

The variables:
- `C`: the parameters; `B`: the block.

Read aloud: the justified block, every pending justification and the finalized block of a chain
state each have their certificates included on the chain, and each is a block of the chain whose
own chain state is at the height named.

 -/
theorem lem66_chain_state_certified (C : Config) (B : Block V) :
    (1 ≤ (chainStateOf C B).h_j →
      JustificationCertOn B (chainStateOf C B).h_j (chainStateOf C B).J ∧
      (chainStateOf C B).J.AncestorEq B ∧
      (chainStateOf C (chainStateOf C B).J).h = (chainStateOf C B).h_j) ∧
    (∀ e ∈ (chainStateOf C B).pending_finality,
      JustificationCertOn B e.j e.T ∧ e.T.AncestorEq B ∧ (chainStateOf C e.T).h = e.j) ∧
    (1 ≤ (chainStateOf C B).h_F →
      JustificationCertOn B (chainStateOf C B).h_F (chainStateOf C B).F ∧
      FinalityCertOn B (chainStateOf C B).h_F (chainStateOf C B).F ∧
      (chainStateOf C B).F.AncestorEq B ∧
      (chainStateOf C (chainStateOf C B).F).h = (chainStateOf C B).h_F) :=
  GoldilocksCorrectness.Proofs.Routines.lem66_chain_state_certified C B

/-! ## Lemma 67, the first advance past a height -/

/-- **Lemma 67, the first advance past a height.** When `1 ≤ h` and the chain state of `B` has a
height greater than `h`, some block `Y`, `B` or an ancestor of `B` and not the genesis block, has
a parent at the height `h` and is itself at the height `h + 1`; the parent's `T_h` is an ancestor
of `Y`, and `Y`'s chain holds a progress certificate at `h` for the parent's `T_h`.

Why: the height rises by at most one per block from `1` at the genesis block, so the chain has a
block whose parent is at `h` and that is at `h + 1`; that block raised the height through the
justification branch or the timeout branch, so a quorum of its pre-event target participation or
progress set voted at `h` naming the parent's `T_h`, each vote included on its chain.

The variables:
- `C`: the parameters; `B`: the block; `h`: the height.

Read aloud: a chain whose height passed `h` has a block that raised the height from `h` to
`h + 1`, carrying a quorum of votes at `h` naming the entry of height `h`, which is an ancestor of
that block.

 -/
theorem lem67_first_advance (C : Config) (B : Block V) (h : Height)
    -- `h` is at least `1`
    (h1 : 1 ≤ h)
    -- the chain state of `B` has a height greater than `h`
    (hlt : h < (chainStateOf C B).h) :
    ∃ Y : Block V, Y.AncestorEq B ∧ Y ≠ Block.genesis ∧
      (chainStateOf C Y.parent).h = h ∧ (chainStateOf C Y).h = h + 1 ∧
      (chainStateOf C Y.parent).T_h.AncestorEq Y ∧
      ProgressCertOn Y h (chainStateOf C Y.parent).T_h :=
  GoldilocksCorrectness.Proofs.Routines.lem67_first_advance C B h h1 hlt

/-- **Lemma 67 (b), the first advance past a height, with its branch.** Lemma 67's conclusion
(`lem67_first_advance`): when `1 ≤ h` and the chain state of `B` has a height greater than `h`,
some block `Y`, `B` or an ancestor of `B` and not the genesis block, has a parent at the height
`h` and is itself at the height `h + 1`; the parent's `T_h` is an ancestor of `Y`, and `Y`'s chain
holds a progress certificate at `h` for the parent's `T_h`; and in addition, `Y`'s chain holds a
justification certificate at `h` for the parent's `T_h`, or `Y`'s slot is at least `δt` after the
slot of the parent's `T_h`.

Why: Lemma 67's proof; at the block that raised the height, the height events took the
justification branch, whose quorum is of target votes, or the timeout branch, whose test is
`T_h.slot + δt ≤ s` at the block's slot.

The variables:
- `C`: the parameters; `B`: the block; `h`: the height.

Read aloud: a height was left by a quorum of targets, or by a progress quorum once the timeout
had passed.

 -/
theorem lem67b_first_advance_cases (C : Config) (B : Block V) (h : Height)
    -- `h` is at least `1`
    (h1 : 1 ≤ h)
    -- the chain state of `B` has a height greater than `h`
    (hlt : h < (chainStateOf C B).h) :
    ∃ Y : Block V, Y.AncestorEq B ∧ Y ≠ Block.genesis ∧
      (chainStateOf C Y.parent).h = h ∧ (chainStateOf C Y).h = h + 1 ∧
      (chainStateOf C Y.parent).T_h.AncestorEq Y ∧
      ProgressCertOn Y h (chainStateOf C Y.parent).T_h ∧
      (JustificationCertOn Y h (chainStateOf C Y.parent).T_h ∨
        (chainStateOf C Y.parent).T_h.slot + C.δt ≤ Y.slot) :=
  GoldilocksCorrectness.Proofs.Routines.lem67b_first_advance_cases C B h h1 hlt

end GoldilocksCorrectness.Statements.Routines
