module
public import GoldilocksCorrectness.Proofs.Routines.Attestation

@[expose] public section

/-!
# The statements about the attestation duty

The audited statements about the attestation duty at the routine level, proved in
`GoldilocksCorrectness/Proofs/Routines/Attestation.lean`:

- Lemma 48, `lem48_attestation_source`: the duty's source is the fast block every other fast
  block is an ancestor of, when it is in the viable tree;
- Lemma 48b, `lem48b_anchor_is_locked_block`: the deepest live lock is the anchor, and the duty's
  head descends from it;
- Lemma 49, `lem49_tick_attests`: an attestation a tick sends is the one the validator client
  builds at the round's action time from the source's height pair and the head's finality pair;
- Lemma 49b, `lem49b_attestation_duty_runs`: at the action time, an awake validator with a source
  sends what the client builds;
- Lemma 50, `lem50_attestation_sent_at_source`: a validator whose record does not lock it onto
  another block at the source's height sends a vote for the source, unless it already has; at a
  fresh height the vote is a target;
- the kit facts `h_max_le_of_viable` and `fast_blocks_ancestorEq_saved`.
-/

set_option autoImplicit false

open scoped DC

open DC (DRE)

namespace GoldilocksCorrectness.Statements.Routines

open Goldilocks

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-! ## The kit facts -/

omit [Fintype V] [RootOrder] in
/-- **Kit fact, a viable block's height is at least the cache minus one.** When `B` is viable at
the FG state `S`, `S.h_max ≤ (S.σ B).h + 1`.

Why: `head_height_floor S` (the least chain-state height a viable block may have) is `S.h_max` or `S.h_max − 1`, and a viable block's height is
at least `head_height_floor`.

The variables:
- `S`: the FG state whose test is read; `B`: the block.

Read aloud: a viable block is at height `h_max − 1` or more, for the `h_max` of the FG state the
test reads.

 -/
theorem h_max_le_of_viable (S : FGState V) (B : Block V)
    -- `B` is viable at `S`
    (hV : is_viable S B = true) :
    S.h_max ≤ (S.σ B).h + 1 :=
  GoldilocksCorrectness.Proofs.Routines.h_max_le_of_viable S B hV

/-- **Kit fact, every fast block of the update's answer is the saved confirmation or an ancestor
of it.** When the confirmation update of a slot `s ≠ 0` answers `A'` and saves the confirmation
`C'` for the slot `s − 1`, every fast block of `A'` is `C'` or an ancestor of `C'`.

Why: the update empties the fast blocks, and writes them only when it saves a block `H` and no
live lock vetoes it, as the blocks of the path of the ancestors of `H` that pass the fast test;
at `s = 0` it answers its input unchanged, whose fast blocks and saved confirmations are
arbitrary, so the slot `s ≠ 0` is a hypothesis.

The variables:
- `C`: the parameters; `P`: the values, with the committees;
- `A`, `A'`: the AC state before and after the update; `Φ`: the frame;
- `t`: the time of the update; `s`: the slot of the update; `C'`: the saved confirmation.

Read aloud: the fast blocks of an update are on the chain of the confirmation it saves.

 -/
theorem fast_blocks_ancestorEq_saved (C : Config) (P : Provisional V) (A A' : ACState V)
    (Φ : Frame V) (t : Time) (s : Slot) (C' : Block V)
    -- the slot of the update is not `0`
    (hs : s ≠ 0)
    -- the confirmation update of slot `s` answers `A'`
    (hUpdate : update_confirmation C P A Φ t s = .ok A')
    -- `A'` saves the confirmation `C'` for the slot `s − 1`
    (hSaved : A'.saved_confirmation (s - 1) = some C') :
    ∀ L ∈ A'.fast_blocks, L.AncestorEq C' :=
  GoldilocksCorrectness.Proofs.Routines.fast_blocks_ancestorEq_saved C P A A' Φ t s C' hs hUpdate
    hSaved

/-! ## Lemmas 48 and 48b -/

/-- **Lemma 48, the source of the attestation duty.** When `B` is a fast block of `A`, every fast
block of `A` is `B` or an ancestor of `B`, and `B` is in the viable tree of `Φ.tree`, every answer
`fi` of `ac_to_fg C A Φ t` has the source `B`.

Why: the source is the deepest block (`Block.deepest?`) of the fast blocks in the viable tree;
`B` is one of them, and every other is a strict ancestor of `B`, hence strictly less deep.

The variables:
- `C`: the parameters; `A`: the AC state; `Φ`: the frame; `t`: the time; `B`: the fast block.

Read aloud: the duty's source is the fast block that every other fast block is an ancestor of,
when it is in the viable tree.

 -/
theorem lem48_attestation_source (C : Config) (A : ACState V) (Φ : Frame V) (t : Time)
    (B : Block V)
    -- `B` is a fast block of `A`
    (hFast : B ∈ A.fast_blocks)
    -- every fast block of `A` is `B` or an ancestor of `B`
    (hAnc : ∀ B' ∈ A.fast_blocks, B'.AncestorEq B)
    -- `B` is in the viable tree of `Φ.tree`
    (hViable : B ∈ viable_tree Φ Φ.tree) :
    ∀ fi : FGInput V, ac_to_fg C A Φ t = .ok fi → fi.source = some B :=
  GoldilocksCorrectness.Proofs.Routines.lem48_attestation_source C A Φ t B hFast hAnc hViable

/-- **Lemma 48b, the anchor is the locked block.** When `B` is locked at `t`, every live lock
entry of `A` is on `B` or an ancestor of `B`, and `B` is in the viable tree of `Φ.tree`, the
anchor `get_anchor A Φ t` is `B`, and every head `ac_to_fg C A Φ t` answers is `B` or a
descendant of `B`.

Why: the anchor is the deepest locked block of the viable tree; every locked block is an ancestor
of a live entry's block, hence of `B`, and `B` is locked; the walk for the head starts at the
anchor and only descends.

The variables:
- `C`: the parameters; `A`: the AC state; `Φ`: the frame; `t`: the time; `B`: the locked block.

Read aloud: the deepest live lock is the anchor, and the walk only descends from it.

 -/
theorem lem48b_anchor_is_locked_block (C : Config) (A : ACState V) (Φ : Frame V) (t : Time)
    (B : Block V)
    -- `B` is locked at `t`
    (hLocked : is_locked A Φ t B = true)
    -- every lock entry of `A` live at `t` is on `B` or an ancestor of `B`
    (hLocks : ∀ e ∈ A.lock_entries, is_live Φ t e = true → e.B.AncestorEq B)
    -- `B` is in the viable tree of `Φ.tree`
    (hViable : B ∈ viable_tree Φ Φ.tree) :
    get_anchor A Φ t = B ∧
      ∀ fi : FGInput V, ac_to_fg C A Φ t = .ok fi → B.AncestorEq fi.head :=
  GoldilocksCorrectness.Proofs.Routines.lem48b_anchor_is_locked_block C A Φ t B hLocked hLocks
    hViable

/-! ## Lemmas 49 and 49b -/

/-- **Lemma 49, the attestation a tick sends is the duty's.** If the tick at `t` answered and sent
the attestation `a`, then `t` is the action time of the round of its slot, and, for the answer
`fi` of `ac_to_fg` on the tick's final AC state over the frame of the node's FG state, with the
source `source`, `a` is the attestation `create_attestation` builds from the node's record, the
height and `T_h` of the source's chain state, and the justification height, justified root and
finalization height of the head's chain state; and the tick's final record is the record it
returns.

Why: the tick of the available chain sends only Goldfish votes and the proposal only a block, so
the attestation duty sent `a`, inside its `if`, at the action time; the proposal does not run
then, the start of a slot never being the action time of its round; the duty reads the FG state,
the record and the validator the tick started with, and the AC state the tick of the available
chain left, which it keeps.

The variables:
- `C`, `P`, `X`: the parameters, the values and the digest; `n`: the node state the tick starts
  from; `t`: the time of the tick;
- `n'`, `sent`: the tick's answer, the node state and the objects sent; `a`: the attestation.

Read aloud: an attestation a tick sends is the one the validator client built at the round's
action time from the source's height pair and the head's finality pair.

 -/
theorem lem49_tick_attests (C : Config) (P : Provisional V) (X : External V)
    (n n' : NodeState V) (t : Time) (sent : List (NamedObject V)) (a : Attestation V)
    -- `.ok (n', sent)` is an outcome of the tick at `t`
    (hRun : .ok (n', sent) ∈ (tick C P X n t).outcomes)
    -- the tick sent `a`
    (hAtt : NamedObject.attest a ∈ sent) :
    t = C.a_ (C.round (C.slot t)) ∧
    ∃ (fi : FGInput V) (source : Block V),
      ac_to_fg C n'.A (fg_to_ac n.S) t = .ok fi ∧ fi.source = some source ∧
      (create_attestation n.Λ n.v (n.S.σ source).h (n.S.σ source).T_h.root
        (n.S.σ fi.head).h_j (n.S.σ fi.head).J.root (n.S.σ fi.head).h_F).2 = some a ∧
      n'.Λ = (create_attestation n.Λ n.v (n.S.σ source).h (n.S.σ source).T_h.root
        (n.S.σ fi.head).h_j (n.S.σ fi.head).J.root (n.S.σ fi.head).h_F).1 :=
  GoldilocksCorrectness.Proofs.Routines.lem49_tick_attests C P X n n' t sent a hRun hAtt

/-- **Lemma 49b, the duty runs.** If the tick at the action time of its slot's round answered, the
node had been awake since the duty window's start, `ac_to_fg` on the tick's final AC state answers
`fi` with the source `source`, and `create_attestation` on them builds `a`, then the tick sent
`a`.

Why: the duty's `if` holds, the proposal's does not (the start of a slot is never the action time
of its round), and the duty sends what `fg_attest` builds, reading the AC state the tick of the
available chain left, which the tick's final AC state is.

The variables:
- `C`, `P`, `X`: the parameters, the values and the digest; `n`: the node state the tick starts
  from; `t`: the time of the tick;
- `n'`, `sent`: the tick's answer, the node state and the objects sent; `a`: the attestation;
- `fi`: the answer of `ac_to_fg`; `source`: its source.

Read aloud: at the action time, an awake validator with a source sends what the client builds.

 -/
theorem lem49b_attestation_duty_runs (C : Config) (P : Provisional V) (X : External V)
    (n n' : NodeState V) (t : Time) (sent : List (NamedObject V)) (a : Attestation V)
    (fi : FGInput V) (source : Block V)
    -- `.ok (n', sent)` is an outcome of the tick at `t`
    (hRun : .ok (n', sent) ∈ (tick C P X n t).outcomes)
    -- `t` is the action time of the round of its slot
    (hAction : t = C.a_ (C.round (C.slot t)))
    -- the node has been awake since the start of the duty window of the slot of `t`, or earlier
    (hAwake : ∃ τ : Time, n.awakeSince = some τ ∧ τ ≤ duty_window_start C (C.slot t))
    -- `ac_to_fg` on the tick's final AC state answers `fi`
    (hInput : ac_to_fg C n'.A (fg_to_ac n.S) t = .ok fi)
    -- `fi` has the source `source`
    (hSource : fi.source = some source)
    -- `create_attestation` on the source's and the head's chain states builds `a`
    (hBuilt : (create_attestation n.Λ n.v (n.S.σ source).h (n.S.σ source).T_h.root
        (n.S.σ fi.head).h_j (n.S.σ fi.head).J.root (n.S.σ fi.head).h_F).2 = some a) :
    NamedObject.attest a ∈ sent :=
  GoldilocksCorrectness.Proofs.Routines.lem49b_attestation_duty_runs C P X n n' t sent a fi
    source hRun hAction hAwake hInput hSource hBuilt

/-! ## Lemma 50 -/

omit [DecidableEq V] [Fintype V] [RootOrder] in
/-- **Lemma 50, what the validator client sends at a height.** For the anti-slashing record `Λ`,
the validator `v`, a source at the height `h_c` with the root `T_c`, and a head with the
justification height `h_j`, the justified root `J` and the finalization height `h_F`: when the
record holds no lock at `h_c`, or holds the lock `T_c` there and every attestation it sent at
`h_c` names `T_c`; when `J = T_c` if `h_j = h_c`; and when every target the record holds was sent,
every target it sent is recorded and every timeout it sent is recorded, then `create_attestation`
builds an attestation of `v` at `h_c` naming `T_c`, or builds none and the record already sent an
attestation at `h_c` naming `T_c`. And when nothing the record sent is at `h_c`, and it holds no
timeout and no target there, it builds a target.

Why: `height_pair` gives the timeout for `T_c` when a timeout is recorded at `h_c`; otherwise the
lock it reads at `h_c` is the record's or the finality pair's, `T_c` or none, and it gives the
target for `T_c`, or the timeout for `T_c` when another target is recorded. `already_sent` forbids
the vote only when the record sent an attestation at `h_c` naming `T_c`: a timeout for `T_c`, or,
for a target, an attestation at `h_c`, which is a target naming `T_c` by the three record facts.



The variables:
- `Λ`: the record; `v`: the validator; `h_c`, `T_c`: the source's height and the root of the block
  that took the source into that height;
- `h_j`, `J`, `h_F`: the head's justification height, justified root and finalization height.

Read aloud: a validator whose record does not lock it onto another block at the source's height
sends a vote for `(h_c, T_c)`, unless it already has; at a fresh height the vote is a target. -/
theorem lem50_attestation_sent_at_source (Λ : SigningHistory) (v : V) (h_c : Height)
    (T_c : BlockId) (h_j : Height) (J : BlockId) (h_F : Height)
    -- the record holds no lock at `h_c`, or the lock `T_c` with every attestation sent at `h_c`
    -- naming `T_c`
    (hLock : Λ.lock h_c = none ∨
      (Λ.lock h_c = some T_c ∧ ∀ b ∈ Λ.sent, b.h = h_c → b.T = T_c))
    -- a justification at `h_c` is of `T_c`
    (hJ : h_j = h_c → J = T_c)
    -- a target the record holds was sent
    (hTargetSent : ∀ (h : Height) (T : BlockId), Λ.target h = some T →
      ∃ b ∈ Λ.sent, b.h = h ∧ b.T = T)
    -- a target the record sent is recorded
    (hSentTarget : ∀ b ∈ Λ.sent, b.τ = false → Λ.target b.h ≠ none)
    -- a timeout the record sent is recorded
    (hSentTimeout : ∀ b ∈ Λ.sent, b.τ = true → Λ.timeout b.h = true) :
    ((∃ a : Attestation V, (create_attestation Λ v h_c T_c h_j J h_F).2 = some a ∧
        a.val_index = v ∧ a.h = h_c ∧ a.T = T_c) ∨
      ((create_attestation (V := V) Λ v h_c T_c h_j J h_F).2 = none ∧
        ∃ b ∈ Λ.sent, b.h = h_c ∧ b.T = T_c)) ∧
    ((∀ b ∈ Λ.sent, b.h ≠ h_c) → Λ.timeout h_c = false → Λ.target h_c = none →
      ∃ a : Attestation V, (create_attestation Λ v h_c T_c h_j J h_F).2 = some a ∧
        a.val_index = v ∧ a.h = h_c ∧ a.T = T_c ∧ a.τ = false) :=
  GoldilocksCorrectness.Proofs.Routines.lem50_attestation_sent_at_source Λ v h_c T_c h_j J h_F
    hLock hJ hTargetSent hSentTarget hSentTimeout

end GoldilocksCorrectness.Statements.Routines
