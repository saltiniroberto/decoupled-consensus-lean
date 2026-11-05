module
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Attestation
public import GoldilocksCorrectness.Statements.Routines.AttestationStatements

@[expose] public section

/-!
# The statements about the attestation duty, over a model

The audited statements of `GoldilocksCorrectness/Statements/Routines/AttestationStatements.lean`
over a model `M` whose facts `F` hold, each the statement form of its proof on
`Record/Restated/Proofs/Routines/Attestation.lean`: Lemma 48 (the source), Lemma 48b (the anchor is
the locked block), Lemmas 49 and 49b (the tick's facts T8 and T8b), Lemma 50 (what the validator
client sends at a height) and the kit fact `h_max_le_of_viable`. The kit fact
`fast_blocks_ancestorEq_saved` is restated with the confirmation update
(`Record/Restated/Statements/Routines/ConfirmationStatements.lean`).

The recovery section states Lemmas 48, 48b and 50 again, as the landed statements (`type_of%`),
and proves each from its record form at the spec's model, as the proof page's recoveries do.
Lemmas 49 and 49b and `h_max_le_of_viable` have no recovery, for the reasons that page gives.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Statements.Routines

open Goldilocks
open GoldilocksCorrectness.Record
open GoldilocksCorrectness.Statements.Routines (TieBreak WalkStep)

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Lemmas 48 and 48b -/

/-- **Lemma 48 over the record, the source of the attestation duty.** When `B` is a fast block of
`n'`, every fast block of `n'` is `B` or an ancestor of `B`, and `B` is in the viable tree of the
tree of `n`'s frame, the deepest fast block of `n'` in that viable tree is `B`.

The variables:
- `M`: the model; `n`: the node state whose frame is read; `n'`: the node state whose fast blocks
  are read; `B`: the fast block.

Read aloud: the duty's source is the fast block that every other fast block is an ancestor of,
when it is in the viable tree. -/
theorem lem48_attestation_source [RootOrder] {M : GoldilocksModel V} (n n' : M.N) (B : Block V)
    -- `B` is a fast block of `n'`
    (hFast : B ∈ n'.fastBlocks)
    -- every fast block of `n'` is `B` or an ancestor of `B`
    (hAnc : ∀ B' ∈ n'.fastBlocks, B'.AncestorEq B)
    -- `B` is in the viable tree of the tree of `n`'s frame
    (hViable : B ∈ M.viable_tree (M.fg_to_ac n) (M.fg_to_ac n).tree) :
    Block.deepest? (n'.fastBlocks ∩ M.viable_tree (M.fg_to_ac n) (M.fg_to_ac n).tree) = some B :=
  GoldilocksCorrectness.Record.Proofs.Routines.lem48_attestation_source M n n' B hFast hAnc
    hViable

/-- **Lemma 48b over the record, the anchor is the locked block.** When `B` is locked at `t` by a
live entry of `E`, every live entry of `E` is on `B` or an ancestor of `B`, and `B` is in the viable
tree of `Φ.tree`, the anchor over `Φ` with `E` is `B`, and every block reached by walk steps from
it, at the model's tie-break, is `B` or a descendant of `B`.

The variables:
- `M`: the model; `Φ`: the frame; `E`: the lock entries; `t`: the time; `B`: the locked block.

Read aloud: the deepest live lock is the anchor, and a walk only descends from it. -/
theorem lem48b_anchor_is_locked_block [RootOrder] {M : GoldilocksModel V} (Φ : Frame V)
    (E : Finset M.LE) (t : Time) (B : Block V)
    -- `B` is locked at `t` by a live entry of `E`
    (hLocked : ∃ e ∈ E, t < e.d ∧ e.B ∈ Φ.tree ∧ B.ancestorEq e.B = true)
    -- every entry of `E` live at `t` is on `B` or an ancestor of `B`
    (hLocks : ∀ e ∈ E, t < e.d → e.B ∈ Φ.tree → e.B.AncestorEq B)
    -- `B` is in the viable tree of `Φ.tree`
    (hViable : B ∈ M.viable_tree Φ Φ.tree) :
    AnchorAt M Φ E t = B ∧
      ∀ (score : Block V → DC.DRE ℕ) (eligible : Block V → DC.DRE Bool) (H : Block V),
        Relation.ReflTransGen (@WalkStep V M.tieBreak (M.viable_tree Φ Φ.tree) score eligible)
          (AnchorAt M Φ E t) H → B.AncestorEq H :=
  GoldilocksCorrectness.Record.Proofs.Routines.lem48b_anchor_is_locked_block M Φ E t B hLocked
    hLocks hViable

/-! ## Lemmas 49 and 49b -/

/-- **Lemma 49 over the record, the attestation a tick sends is the duty's.** An attestation `a`
that a tick sends, from a node state satisfying the model's node invariant, is sent at the action
time of the round of the slot of `t`, by a node awake since that slot's duty window started; its
source is the deepest fast block of `n'` in the viable tree of `n`'s frame's tree, its head the end
of the walk counting `n`'s votes of the slot from the anchor over `n`'s frame with the lock entries
of `n'`; it is what `n`'s validator client builds from the chain states of the source and the head;
and the record of `n'` is `n`'s with it written in.

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the values and the digest; `n`: the node state; `t`: the time;
- `n'`, `sent`: the tick's answer; `a`: the attestation sent.

Read aloud: an attestation a tick sends is the awake node's attestation at the round's action time,
built by its validator client from the deepest fast block in the viable tree and the end of the
walk, and the node records it. -/
theorem lem49_tick_attests [RootOrder] {M : GoldilocksModel V} (F : Facts M) (C : Config)
    (P : Provisional V) (X : External V) (n n' : M.N) (t : Time) (sent : List (NamedObject V))
    (a : Attestation V)
    -- `.ok (n', sent)` is an outcome of the tick at `t`
    (hRun : .ok (n', sent) ∈ M.tick C P X n t)
    -- `n` satisfies the model's node invariant
    (hInv : M.nodeInv C P X n)
    -- the tick sent `a`
    (hAtt : NamedObject.attest a ∈ sent) :
    t = C.a_ (C.round (C.slot t)) ∧ AwakeFor M C n (C.slot t) ∧
      ∃ source head : Block V,
        Block.deepest? (n'.fastBlocks ∩ M.viable_tree (M.fg_to_ac n) (M.fg_to_ac n).tree) =
          some source ∧
        PoolHeadOf M C n (AnchorAt M (M.fg_to_ac n) n'.lockEntries t) t (C.slot t) head ∧
        AttestationFrom M n n.v (M.chainStateOf C source).h (M.chainStateOf C source).T_h.root
          (M.chainStateOf C head).h_j (M.chainStateOf C head).J.root
          (M.chainStateOf C head).h_F a ∧
        AttestationRecorded M n a n' :=
  GoldilocksCorrectness.Record.Proofs.Routines.lem49_tick_attests M F C P X n n' t sent a hRun
    hInv hAtt

/-- **Lemma 49b over the record, the duty runs.** A tick at the action time of the round of the
slot of `t`, from a node state satisfying the model's node invariant and awake since that slot's
duty window started, sends the attestation the validator client builds from the deepest fast block
of `n'` in the viable tree of `n`'s frame's tree and the end of the walk counting `n`'s votes of
the slot.

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the values and the digest; `n`: the node state; `t`: the time;
- `n'`, `sent`: the tick's answer; `a`: the attestation built; `source`, `head`: its source and
  head.

Read aloud: at the action time, an awake node with a source sends what its validator client
builds. -/
theorem lem49b_attestation_duty_runs [RootOrder] {M : GoldilocksModel V} (F : Facts M) (C : Config)
    (P : Provisional V) (X : External V) (n n' : M.N) (t : Time) (sent : List (NamedObject V))
    (a : Attestation V) (source head : Block V)
    -- `.ok (n', sent)` is an outcome of the tick at `t`
    (hRun : .ok (n', sent) ∈ M.tick C P X n t)
    -- `n` satisfies the model's node invariant
    (hInv : M.nodeInv C P X n)
    -- `t` is the action time of the round of its slot
    (hAction : t = C.a_ (C.round (C.slot t)))
    -- the node has been awake since the start of the duty window of the slot of `t`
    (hAwake : AwakeFor M C n (C.slot t))
    -- `source` is the deepest fast block of `n'` in the viable tree of `n`'s frame's tree
    (hSource : Block.deepest? (n'.fastBlocks ∩ M.viable_tree (M.fg_to_ac n) (M.fg_to_ac n).tree) =
      some source)
    -- `head` is the end of the walk counting `n`'s votes of the slot of `t`
    (hHead : PoolHeadOf M C n (AnchorAt M (M.fg_to_ac n) n'.lockEntries t) t (C.slot t) head)
    -- the validator client builds `a` from the source's and the head's chain states
    (hBuilt : AttestationFrom M n n.v (M.chainStateOf C source).h
      (M.chainStateOf C source).T_h.root (M.chainStateOf C head).h_j
      (M.chainStateOf C head).J.root (M.chainStateOf C head).h_F a) :
    NamedObject.attest a ∈ sent :=
  GoldilocksCorrectness.Record.Proofs.Routines.lem49b_attestation_duty_runs M F C P X n n' t sent a
    source head hRun hInv hAction hAwake hSource hHead hBuilt

/-! ## Lemma 50 -/

/-- **Lemma 50 over the record, what the validator client sends at a height.** For the node state
`n`, the validator `v`, a source at the height `h_c` with the root `T_c`, and a head with the
justification height `h_j`, the justified root `J` and the finalization height `h_F`: when `n`'s
record holds no lock at `h_c`, or holds the lock `T_c` there and every attestation it sent at `h_c`
names `T_c`; when `J = T_c` if `h_j = h_c`; and when every target the record holds was sent, every
target it sent is recorded and every timeout it sent is recorded, then the validator client builds
an attestation of `v` at `h_c` naming `T_c`, or builds none and the record already sent an
attestation at `h_c` naming `T_c`. And when nothing the record sent is at `h_c`, and it holds no
timeout and no target there, it builds a target.

The variables:
- `M`: the model; `F`: its facts;
- `n`: the node state; `v`: the validator; `h_c`, `T_c`: the source's height and root;
- `h_j`, `J`, `h_F`: the head's justification height, justified root and finalization height.

Read aloud: a validator whose record does not lock it onto another block at the source's height
sends a vote for `(h_c, T_c)`, unless it already has; at a fresh height the vote is a target. -/
theorem lem50_attestation_sent_at_source {M : GoldilocksModel V} (F : Facts M) (n : M.N) (v : V)
    (h_c : Height) (T_c : BlockId) (h_j : Height) (J : BlockId) (h_F : Height)
    -- the record holds no lock at `h_c`, or the lock `T_c` with every attestation sent at `h_c`
    -- naming `T_c`
    (hLock : n.sentLock h_c = none ∨
      (n.sentLock h_c = some T_c ∧ ∀ b ∈ n.sentAttestations, b.h = h_c → b.T = T_c))
    -- a justification at `h_c` is of `T_c`
    (hJ : h_j = h_c → J = T_c)
    -- a target the record holds was sent
    (hTargetSent : ∀ (h : Height) (T : BlockId), n.sentTarget h = some T →
      ∃ b ∈ n.sentAttestations, b.h = h ∧ b.T = T)
    -- a target the record sent is recorded
    (hSentTarget : ∀ b ∈ n.sentAttestations, b.τ = false → n.sentTarget b.h ≠ none)
    -- a timeout the record sent is recorded
    (hSentTimeout : ∀ b ∈ n.sentAttestations, b.τ = true → n.sentTimeout b.h = true) :
    ((∃ a : Attestation V, AttestationFrom M n v h_c T_c h_j J h_F a ∧
        a.val_index = v ∧ a.h = h_c ∧ a.T = T_c) ∨
      ((∀ a : Attestation V, ¬ AttestationFrom M n v h_c T_c h_j J h_F a) ∧
        ∃ b ∈ n.sentAttestations, b.h = h_c ∧ b.T = T_c)) ∧
    ((∀ b ∈ n.sentAttestations, b.h ≠ h_c) → n.sentTimeout h_c = false →
      n.sentTarget h_c = none →
      ∃ a : Attestation V, AttestationFrom M n v h_c T_c h_j J h_F a ∧
        a.val_index = v ∧ a.h = h_c ∧ a.T = T_c ∧ a.τ = false) :=
  GoldilocksCorrectness.Record.Proofs.Routines.lem50_attestation_sent_at_source M F n v h_c T_c h_j
    J h_F hLock hJ hTargetSent hSentTarget hSentTimeout

/-! ## The kit fact -/

/-- **Kit fact over the record, a viable block's height is at least the greatest height minus
one.** When `B` is a block of `n`'s tree viable in `n`, and `n` satisfies the model's node
invariant, `hMax M C n ≤ (M.chainStateOf C B).h + 1`.

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the given values, the digest; `n`: the node state;
- `hI`: `n` satisfies the model's node invariant; `B`: the block.

Read aloud: a viable block is at the greatest height minus one or more. -/
theorem h_max_le_of_viable {M : GoldilocksModel V} (F : Facts M) (C : Config) (P : Provisional V)
    (X : External V) (n : M.N) (hI : M.nodeInv C P X n) (B : Block V)
    -- `B` is a block of the tree
    (hB : B ∈ n.tree)
    -- `B` is viable in `n`
    (hV : M.is_viable n B = true) :
    hMax M C n ≤ (M.chainStateOf C B).h + 1 :=
  GoldilocksCorrectness.Record.Proofs.Routines.h_max_le_of_viable M F C P X n hI B hB hV

/-! ## At the spec's model -/

/-- The landed statement `lem48_attestation_source`, recovered from its record form at the spec's
model, at the AC state `n'.A` and the frame `fg_to_ac n.S` of node states `n`, `n'`.

Read aloud: the landed Lemma 48 holds at the AC state and the frame of every pair of node
states. -/
theorem lem48_attestation_source_recovered {V : Type} [DecidableEq V] [Fintype V] [RootOrder] :
    ∀ (C : Config) (n n' : NodeState V) (t : Time) (B : Block V),
      type_of% (@GoldilocksCorrectness.Statements.Routines.lem48_attestation_source V _ _ _ C n'.A
        (fg_to_ac n.S) t B) := by
  intro C n n' t B
  exact GoldilocksCorrectness.Record.Proofs.Routines.lem48_attestation_source_recovered C n n' t B

/-- The landed statement `lem48b_anchor_is_locked_block`, recovered from its record form at the
spec's model.

Read aloud: the landed Lemma 48b holds, as the record's theorem at the spec's model. -/
theorem lem48b_anchor_is_locked_block_recovered {V : Type} [DecidableEq V] [Fintype V]
    [RootOrder] :
    type_of% (@GoldilocksCorrectness.Statements.Routines.lem48b_anchor_is_locked_block V _ _ _) := by
  exact GoldilocksCorrectness.Record.Proofs.Routines.lem48b_anchor_is_locked_block_recovered

/-- The landed statement `lem50_attestation_sent_at_source`, recovered from its record form at the
spec's model, at the anti-slashing record `n.Λ` of every node state `n`.

Read aloud: the landed Lemma 50 holds at the record of every node state. -/
theorem lem50_attestation_sent_at_source_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (n : NodeState V),
      type_of% (@GoldilocksCorrectness.Statements.Routines.lem50_attestation_sent_at_source V
        n.Λ) := by
  intro n
  exact GoldilocksCorrectness.Record.Proofs.Routines.lem50_attestation_sent_at_source_recovered n

end GoldilocksCorrectness.Record.Statements.Routines
