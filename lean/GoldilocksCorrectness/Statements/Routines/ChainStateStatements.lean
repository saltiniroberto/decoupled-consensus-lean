module
public import GoldilocksCorrectness.Proofs.Routines.ChainState
public import GoldilocksCorrectness.Proofs.Routines.ChainStateOf

@[expose] public section

/-!
# The statements about the chain state of a block, and the certificate

The audited statements about the state transition `state_transition C σ B`, the chain state of a
block `B` computed from the chain state `σ` of its parent, proved in
`GoldilocksCorrectness/Proofs/Routines/ChainState.lean`:

- Lemma 47, parts (a) to (c): the bounds on the heights, the height rising by at most one, and
  the block `T_h` that took the chain into its height;
- Lemma 51 and Lemma 51b: a quorum of votes at the parent's height is a certificate, and a
  progress quorum raises the height at a late enough slot;
- Lemma 52: a valid pool attestation not on the parent's chain is included in a proposal;
- the kit facts `valid_attestation_of_height` and `create_attestation_well_formed`.
-/

set_option autoImplicit false

open scoped DC

namespace GoldilocksCorrectness.Statements.Routines

open Goldilocks

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Lemma 47, parts (a) to (c), over the state transition -/

/-- **Lemma 47 (a), the bounds on the heights, over the state transition.** When the parent's
chain state `σ` has its justification height less than its height, its finalization height at
most its justification height, and every pending justification at a height at most its
justification height, so does the chain state of `B`; and its height is at least `1`.

Why: counting the attestations keeps the heights and the pending justifications; the loop over
the pending justifications sets `h_F` to `σ.h_F` or to a pending height, both at most `σ.h_j`; the
justification branch sets `h_j` to `σ.h`, appends a pending justification at `σ.h`, and raises the
height to `σ.h + 1`; the timeout branch raises the height; otherwise the heights stay.

The variables:
- `C`: the parameters; `σ`: the chain state of `B`'s parent; `B`: the block.

Read aloud: along a block, the justification height stays less than the height, the finalization
height stays at most the justification height, and every pending justification stays at a height
at most the justification height.

 -/
theorem lem47a_state_transition_bounds (C : Config) (σ : ChainState V) (B : Block V)
    -- the parent's justification height is less than its height
    (hj : σ.h_j < σ.h)
    -- the parent's finalization height is at most its justification height
    (hF : σ.h_F ≤ σ.h_j)
    -- every pending justification of the parent is at a height at most its justification height
    (hpend : ∀ e ∈ σ.pending_finality, e.j ≤ σ.h_j) :
    1 ≤ (state_transition C σ B).h ∧
      (state_transition C σ B).h_j < (state_transition C σ B).h ∧
      (state_transition C σ B).h_F ≤ (state_transition C σ B).h_j ∧
      ∀ e ∈ (state_transition C σ B).pending_finality, e.j ≤ (state_transition C σ B).h_j :=
  GoldilocksCorrectness.Proofs.Routines.lem47a_state_transition_bounds C σ B hj hF hpend

/-- **Lemma 47 (b), the height rises by at most one, over the state transition.** The chain
state of `B` has the parent's height, or the parent's height plus one.

Why: only `advance_height` writes the height, and at most once.

The variables:
- `C`: the parameters; `σ`: the chain state of `B`'s parent; `B`: the block.

Read aloud: a block's height is its parent's, or one more.

 -/
theorem lem47b_state_transition_height (C : Config) (σ : ChainState V) (B : Block V) :
    (state_transition C σ B).h = σ.h ∨ (state_transition C σ B).h = σ.h + 1 :=
  GoldilocksCorrectness.Proofs.Routines.lem47b_state_transition_height C σ B

/-- **Lemma 47 (c), the block that took the chain into its height, over the state transition.**
When the chain state of `B` keeps the parent's height, it keeps the parent's `T_h`; when it
raises the height by one, its `T_h` is `B`.

Why: counting the attestations makes `B` the latest block; `advance_height` writes `T_h` from the
latest block; otherwise `T_h` is kept.

The variables:
- `C`: the parameters; `σ`: the chain state of `B`'s parent; `B`: the block.

Read aloud: `T_h` changes exactly when the height does, and then to the block that raised it.

 -/
theorem lem47c_state_transition_T_h (C : Config) (σ : ChainState V) (B : Block V) :
    ((state_transition C σ B).h = σ.h → (state_transition C σ B).T_h = σ.T_h) ∧
      ((state_transition C σ B).h = σ.h + 1 → (state_transition C σ B).T_h = B) :=
  GoldilocksCorrectness.Proofs.Routines.lem47c_state_transition_T_h C σ B

/-! ## Lemmas 51 and 51b, the certificate -/

/-- **Lemma 51, a quorum of votes at the parent's height is a certificate.** When the block `B`
includes, for every member of a quorum `Q`, an attestation of that member at the parent's height
`σ.h` naming `σ.T_h`, the chain state of `B` has the height `σ.h + 1`, or keeps `σ.h` with `Q`
counted in its progress set and `B`'s slot less than `δt` slots after `σ.T_h`'s; and when every
one of those attestations is a target, the chain state of `B` has the height `σ.h + 1`, the
justified block `σ.T_h` and the justification height `σ.h`.

Why: counting the attestations keeps `σ.h` and `σ.T_h` and adds each member of `Q` to the
progress set, and to the target participation when its attestation is a target; then the
justification branch runs when the targets are a quorum, else the timeout branch when the
progress set is a quorum and the slot condition holds; when neither, the height stays, and the
slot condition is what failed.

The variables:
- `C`: the parameters; `σ`: the chain state of `B`'s parent; `B`: the block;
- `Q`: the validators whose attestations `B` includes.

Read aloud: a quorum of votes for `(σ.h, σ.T_h)` in one block is a certificate: targets justify
`σ.T_h` and raise the height; mixed votes fill the progress set and raise the height once the
block's slot is `δt` past `σ.T_h`'s.

 -/
theorem lem51_quorum_is_certificate (C : Config) (σ : ChainState V) (B : Block V) (Q : Finset V)
    -- `Q` is a quorum
    (hQ : quorum V ≤ Q.card)
    -- `B` includes, for every member of `Q`, an attestation of it at the height `σ.h` naming
    -- `σ.T_h`
    (hAtts : ∀ v ∈ Q, ∃ a ∈ B.attestations, a.val_index = v ∧ a.h = σ.h ∧ a.T = σ.T_h.root) :
    ((state_transition C σ B).h = σ.h + 1 ∨
      ((state_transition C σ B).h = σ.h ∧ Q ⊆ (state_transition C σ B).progress ∧
        B.slot < σ.T_h.slot + C.δt)) ∧
    ((∀ v ∈ Q, ∃ a ∈ B.attestations, a.val_index = v ∧ a.h = σ.h ∧ a.T = σ.T_h.root ∧
        a.τ = false) →
      (state_transition C σ B).h = σ.h + 1 ∧ (state_transition C σ B).J = σ.T_h ∧
        (state_transition C σ B).h_j = σ.h) :=
  GoldilocksCorrectness.Proofs.Routines.lem51_quorum_is_certificate C σ B Q hQ hAtts

/-- **Lemma 51b, the progress quorum advances the height at the timeout slot.** When the parent's
chain state has a quorum in its progress set and `B`'s slot is at least `δt` slots after
`σ.T_h`'s, the chain state of `B` has the height `σ.h + 1`, whatever `B` includes.

Why: counting the attestations only adds to the progress set, and keeps `σ.T_h`; then either the
justification branch or the timeout branch raises the height.

The variables:
- `C`: the parameters; `σ`: the chain state of `B`'s parent; `B`: the block.

Read aloud: once a progress quorum is on chain, the first block of a late enough slot raises the
height, honest or not.

 -/
theorem lem51b_progress_quorum_advances (C : Config) (σ : ChainState V) (B : Block V)
    -- the parent's progress set is a quorum
    (hQ : quorum V ≤ σ.progress.card)
    -- `B`'s slot is at least `δt` slots after the slot of `σ.T_h`
    (hSlot : σ.T_h.slot + C.δt ≤ B.slot) :
    (state_transition C σ B).h = σ.h + 1 :=
  GoldilocksCorrectness.Proofs.Routines.lem51b_progress_quorum_advances C σ B hQ hSlot

/-! ## Lemma 52 and the kit facts on attestations -/

omit [Fintype V] in
/-- **Lemma 52, a valid pool attestation not on the parent's chain is included.** An attestation
of the FG state's pool that is valid against the chain state `S.σ H` and not included in `H` or an
ancestor of `H` is among the attestations a block on `H` includes, `proposal_attestations S H`.

Why: `proposal_attestations` filters the pool by exactly these two tests.

The variables:
- `S`: the FG state; `H`: the parent of the proposal; `a`: the attestation.

Read aloud: the proposal includes every valid pool attestation its chain does not already hold.

 -/
theorem lem52_pool_attestation_included [RootOrder] (S : FGState V) (H : Block V)
    (a : Attestation V)
    -- `a` is in the pool of `S`
    (hPool : a ∈ S.attestations)
    -- `a` is valid against the chain state of `H`
    (hValid : valid_attestation (S.σ H) a = true)
    -- `a` is not included in `H` or in an ancestor of `H`
    (hNew : on_chain a H = false) :
    a ∈ proposal_attestations S H :=
  GoldilocksCorrectness.Proofs.Routines.lem52_pool_attestation_included S H a hPool hValid hNew

omit [DecidableEq V] [Fintype V] in
/-- **Kit fact, an attestation at the parent's height naming its `T_h` is valid.** An attestation
at the height `σ.h` naming `σ.T_h` is valid against the chain state `σ`.

Why: the first case of `valid_attestation`.

The variables:
- `σ`: the chain state; `a`: the attestation.

Read aloud: a vote for the chain's current height and block may be included.

 -/
theorem valid_attestation_of_height (σ : ChainState V) (a : Attestation V)
    -- `a` is at the height `σ.h`
    (hh : a.h = σ.h)
    -- `a` names `σ.T_h`
    (hT : a.T = σ.T_h.root) : valid_attestation σ a = true :=
  GoldilocksCorrectness.Proofs.Routines.valid_attestation_of_height σ a hh hT

omit [DecidableEq V] [Fintype V] in
/-- **Kit fact, an attestation the validator client builds is well formed.** When the source's
height `h_c` is at least `1`, the attestation `create_attestation` builds is well formed
(`attestation_well_formed`): its height is `h_c`, and its finality pair, when kept, is at a height
less than `h_c`.

Why: every vote `height_pair` computes is at `h_c`, and `create_attestation` drops the finality
pair when its height is at least the vote's.

The variables:
- `Λ`: the anti-slashing record; `v`: the validator;
- `h_c`, `T_c`: the source's height and the root of the block that took it there;
- `h_j`, `J`, `h_F`: the head's justification height, justified root and finalization height;
- `a`: the attestation built.

Read aloud: what the validator client sends passes the form check of a received attestation.

 -/
theorem create_attestation_well_formed (Λ : SigningHistory) (v : V) (h_c : Height)
    (T_c : BlockId) (h_j : Height) (J : BlockId) (h_F : Height) (a : Attestation V)
    -- the source's height is at least `1`
    (h1 : 1 ≤ h_c)
    -- `create_attestation` builds `a`
    (hBuilt : (create_attestation Λ v h_c T_c h_j J h_F).2 = some a) :
    attestation_well_formed a = true :=
  GoldilocksCorrectness.Proofs.Routines.create_attestation_well_formed Λ v h_c T_c h_j J h_F a
    h1 hBuilt

end GoldilocksCorrectness.Statements.Routines

namespace GoldilocksCorrectness.Statements.Routines

section

open Goldilocks
variable {V : Type} [DecidableEq V] [Fintype V]

/-- **Lemma 47, the chain-state facts.** For the chain states `chainStateOf C B` and
`chainStateOf C D`:
(a) the height is at least `1`, the justification height is less than the height, and the
finalization height is at most the justification height;
(b) a non-genesis block's height is its parent's or its parent's plus one;
(c) a non-genesis block that keeps its parent's height keeps its parent's `T_h`, and a block that
raises the height has itself as `T_h`;
(d) when `B` is an ancestor of `D` or `D` itself, `B`'s height is at most `D`'s;
(e) when moreover the two heights are equal, the two `T_h` are equal.

Why: `chainStateOf` is the state transition from the parent's chain state, so (a) to (c) are
Lemma 47 (a) to (c) over the state transition, (a) by induction on the block from the genesis
block's chain state (height `1`, justification and finalization heights `0`, nothing pending);
(d) and (e) are inductions on the ancestry from `D` down to `B`, over (b) and (c).

The variables:
- `C`: the parameters; `B`, `D`: the blocks.

Read aloud: along a chain the height rises by at most one per block, `T_h` changes exactly when
the height does, and two blocks of one chain at the same height have the same `T_h`.

 -/
theorem lem47_chain_state_heights (C : Config) (B D : Block V) :
    (1 ≤ (chainStateOf C B).h ∧ (chainStateOf C B).h_j < (chainStateOf C B).h ∧
      (chainStateOf C B).h_F ≤ (chainStateOf C B).h_j) ∧
    (B ≠ Block.genesis →
      ((chainStateOf C B).h = (chainStateOf C B.parent).h ∨
        (chainStateOf C B).h = (chainStateOf C B.parent).h + 1)) ∧
    (B ≠ Block.genesis →
      ((chainStateOf C B).h = (chainStateOf C B.parent).h →
        (chainStateOf C B).T_h = (chainStateOf C B.parent).T_h) ∧
      ((chainStateOf C B).h = (chainStateOf C B.parent).h + 1 → (chainStateOf C B).T_h = B)) ∧
    (B.AncestorEq D → (chainStateOf C B).h ≤ (chainStateOf C D).h) ∧
    (B.AncestorEq D → (chainStateOf C B).h = (chainStateOf C D).h →
      (chainStateOf C B).T_h = (chainStateOf C D).T_h) :=
  GoldilocksCorrectness.Proofs.Routines.lem47_chain_state_heights C B D

/-- **Lemma 47 (f), the justified block is the entry block of its height.** When `D`'s chain state
has the justification height `H` and `1 ≤ H`, some block `Y` that is an ancestor of `D` or `D`
itself has the height `H`, and `Y`'s `T_h` is the justified block of `D`'s chain state.

Why: the justification of a chain state is its parent's, or the parent's height with the parent's
`T_h`; the genesis block's justification height is `0`, so a justification height `H ≥ 1` was
written at an ancestor-or-self of `D` whose parent has the height `H`.

The variables:
- `C`: the parameters; `D`: the block whose justification is read; `H`: its justification height.

Read aloud: the justified block of a chain is the entry block of its justification height on that
chain, the genesis block excepted.

 -/
theorem lem47f_justified_is_entry (C : Config) (D : Block V) (H : Height)
    -- `D`'s chain state has the justification height `H`
    (hH : (chainStateOf C D).h_j = H)
    -- `H` is at least `1`
    (h1 : 1 ≤ H) :
    ∃ Y : Block V, Y.AncestorEq D ∧ (chainStateOf C Y).h = H ∧
      (chainStateOf C Y).T_h = (chainStateOf C D).J :=
  GoldilocksCorrectness.Proofs.Routines.exists_ancestor_of_h_j C D H hH h1

end

end GoldilocksCorrectness.Statements.Routines
