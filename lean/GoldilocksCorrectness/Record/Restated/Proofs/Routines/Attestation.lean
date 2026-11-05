module
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.ACInterface
public import GoldilocksCorrectness.Proofs.Routines.Attestation
import all Goldilocks.AC.State

@[expose] public section

/-!
# Attestation, over a model: Lemmas 48, 48b, 49, 49b, 50 and the height of a viable block

The theorems of `GoldilocksCorrectness/Proofs/Routines/Attestation.lean` over a model `M` whose
facts `F` hold:

- Lemma 48: the source of the attestation duty is the fast block every other fast block is an
  ancestor of, when it is in the viable tree; stated on the equation of `Block.deepest?` the tick's
  fact T8 gives the source by;
- Lemma 48b: the anchor over a frame with a set of lock entries is the locked block every live
  entry's block is an ancestor of, and every walk from it ends at a descendant;
- Lemmas 49 and 49b: the tick's facts T8 and T8b (`TickFacts3`);
- Lemma 50: the field `attestation_sent_at_source` of `TickFacts3`, over the readers of the
  node's anti-slashing record and `AttestationFrom`;
- `h_max_le_of_viable`: a viable block of the tree has a chain-state height at least the greatest
  chain-state height minus one, under the node invariant.

The page's other theorems read the spec's routines of the broadcast monad (`attest`, `tick`) or
open the client's routines (`own_lock`, `height_pair`), and are what the instance of `TickFacts3`
uses; `fast_blocks_ancestorEq_saved` is restated with the confirmation update
(`Record/Restated/Proofs/Routines/Confirmation.lean`).

The recovery section states each landed theorem that has a record form again, as the landed
statement (`type_of%`), and proves it from its record form at the spec's model. Lemmas 49 and 49b
have none: their landed statements name the answers of `ac_to_fg` and `create_attestation`, which
the record does not have. `h_max_le_of_viable` has none: its landed statement reads the stored chain
state of a block of any tree, and the record reads the chain state of a block of the tree only.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Record
open GoldilocksCorrectness.Statements.Routines (TieBreak WalkStep WalkEnd)
open GoldilocksCorrectness.Record.Statements.Routines (AnchorAt LockedViableBlocks hMax AwakeFor
  PoolHeadOf AttestationFrom AttestationRecorded)
open GoldilocksCorrectness.Proofs.Routines (deepest?_mem deepest?_eq_some depth_le_of_ancestorEq
  eq_of_ancestorEq_of_depth ancestorEq_trans)

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
theorem lem48_attestation_source [RootOrder] (M : GoldilocksModel V) (n n' : M.N) (B : Block V)
    -- `B` is a fast block of `n'`
    (hFast : B ∈ n'.fastBlocks)
    -- every fast block of `n'` is `B` or an ancestor of `B`
    (hAnc : ∀ B' ∈ n'.fastBlocks, B'.AncestorEq B)
    -- `B` is in the viable tree of the tree of `n`'s frame
    (hViable : B ∈ M.viable_tree (M.fg_to_ac n) (M.fg_to_ac n).tree) :
    Block.deepest? (n'.fastBlocks ∩ M.viable_tree (M.fg_to_ac n) (M.fg_to_ac n).tree) = some B :=
  deepest?_eq_some (Finset.mem_inter.mpr ⟨hFast, hViable⟩)
    (fun D hD => depth_le_of_ancestorEq (hAnc D (Finset.mem_inter.mp hD).1))
    (fun D hD hd => eq_of_ancestorEq_of_depth (hAnc D (Finset.mem_inter.mp hD).1) hd.ge)

/-- **Lemma 48b over the record, the anchor is the locked block.** When `B` is locked at `t` by an
entry of `E` (a live entry, its deadline after `t` and its block in `Φ.tree`, whose block is `B` or
a descendant of `B`), every live entry of `E` is on `B` or an ancestor of `B`, and `B` is in the
viable tree of `Φ.tree`, the anchor over `Φ` with `E` is `B`, and every block reached by walk steps
from it, at the model's tie-break, is `B` or a descendant of `B`.

The variables:
- `M`: the model; `Φ`: the frame; `E`: the lock entries; `t`: the time; `B`: the locked block.

Read aloud: the deepest live lock is the anchor, and a walk only descends from it. -/
theorem lem48b_anchor_is_locked_block [RootOrder] (M : GoldilocksModel V) (Φ : Frame V)
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
          (AnchorAt M Φ E t) H → B.AncestorEq H := by
  have hanc : ∀ D ∈ LockedViableBlocks M Φ E t, D.AncestorEq B := by
    intro D hD
    obtain ⟨-, e, he, h1, h2, h3⟩ := (mem_lockedViableBlocks M Φ E t D).1 hD
    exact ancestorEq_trans h3 (hLocks e he h1 h2)
  have hD : Block.deepest? (LockedViableBlocks M Φ E t) = some B :=
    deepest?_eq_some ((mem_lockedViableBlocks M Φ E t B).2 ⟨hViable, hLocked⟩)
      (fun D hD' => depth_le_of_ancestorEq (hanc D hD'))
      (fun D hD' hd => eq_of_ancestorEq_of_depth (hanc D hD') hd.ge)
  have hanchor : AnchorAt M Φ E t = B := by
    unfold AnchorAt
    generalize hD' : Block.deepest? (LockedViableBlocks M Φ E t) = D
    rw [hD'] at hD
    subst hD
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, dite_true, Option.value, Option.get_some]
  refine ⟨hanchor, fun score eligible H hH => ?_⟩
  rw [hanchor] at hH
  letI : TieBreak V := M.tieBreak
  exact GoldilocksCorrectness.Proofs.Routines.ancestorEq_of_walkSteps hH

section

variable (M : GoldilocksModel V) (F : Facts M)
include M F

/-! ## Lemmas 49 and 49b -/

/-- **Lemma 49 over the record, the attestation a tick sends is the duty's.** The tick's fact T8
(`TickFacts3.tick_attestation`).

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the values and the digest; `n`: the node state; `t`: the time;
- `n'`, `sent`: the tick's answer; `a`: the attestation sent.

Read aloud: an attestation a tick sends is the one the validator client built at the round's
action time from the deepest fast block in the viable tree and the end of the walk. -/
theorem lem49_tick_attests [RootOrder] (C : Config) (P : Provisional V) (X : External V)
    (n n' : M.N) (t : Time) (sent : List (NamedObject V)) (a : Attestation V)
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
  F.tk3.tick_attestation C P X n t n' sent a hRun hInv hAtt

/-- **Lemma 49b over the record, the duty runs.** The tick's fact T8b
(`TickFacts3.tick_attestation_sent`).

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the values and the digest; `n`: the node state; `t`: the time;
- `n'`, `sent`: the tick's answer; `a`: the attestation built; `source`, `head`: its source and
  head.

Read aloud: at the action time, an awake node with a source sends what its validator client
builds. -/
theorem lem49b_attestation_duty_runs [RootOrder] (C : Config) (P : Provisional V) (X : External V)
    (n n' : M.N) (t : Time) (sent : List (NamedObject V)) (a : Attestation V)
    (source head : Block V)
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
  F.tk3.tick_attestation_sent C P X n t n' sent a source head hRun hInv hAction hAwake hSource
    hHead hBuilt

/-! ## Lemma 50 -/

/-- **Lemma 50 over the record, what the validator client sends at a height.** The field
`TickFacts3.attestation_sent_at_source`.

The variables:
- `M`: the model; `F`: its facts;
- `n`: the node state; `v`: the validator; `h_c`, `T_c`: the source's height and the root of the
  block that took the source into that height;
- `h_j`, `J`, `h_F`: the head's justification height, justified root and finalization height.

Read aloud: a validator whose record does not lock it onto another block at the source's height
sends a vote for `(h_c, T_c)`, unless it already has; at a fresh height the vote is a target. -/
theorem lem50_attestation_sent_at_source (n : M.N) (v : V) (h_c : Height) (T_c : BlockId)
    (h_j : Height) (J : BlockId) (h_F : Height)
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
  F.tk3.attestation_sent_at_source n v h_c T_c h_j J h_F hLock hJ hTargetSent hSentTarget
    hSentTimeout

/-! ## The kit fact -/

/-- **Kit fact over the record, a viable block's height is at least the greatest height minus
one.** When `B` is a block of `n`'s tree viable in `n`, and `n` satisfies the model's node
invariant, `hMax M C n ≤ (M.chainStateOf C B).h + 1`.

Why: the least chain-state height of a viable block is `hMax M C n` or `hMax M C n - 1`
(`head_height_floor_eq`), and a viable block of the tree is at least that high (`is_viable_eq`).

The variables:
- `M`: the model; `F`: its facts;
- `C`, `P`, `X`: the parameters, the given values, the digest; `n`: the node state;
- `hI`: `n` satisfies the model's node invariant; `B`: the block.

Read aloud: a viable block is at the greatest height minus one or more. -/
theorem h_max_le_of_viable (C : Config) (P : Provisional V) (X : External V) (n : M.N)
    (hI : M.nodeInv C P X n) (B : Block V)
    -- `B` is a block of the tree
    (hB : B ∈ n.tree)
    -- `B` is viable in `n`
    (hV : M.is_viable n B = true) :
    hMax M C n ≤ (M.chainStateOf C B).h + 1 := by
  rw [F.ndAdded.is_viable_eq hI hB, decide_eq_true_eq, F.ndAdded.head_height_floor_eq hI] at hV
  split at hV
  all_goals ((try unfold Height at *); omega)

end

/-! ## At the spec's model -/

/-- The landed `GoldilocksCorrectness.Proofs.Routines.lem48_attestation_source`, recovered from its
record form at the spec's model, at the AC state `n'.A` and the frame `fg_to_ac n.S` of node states
`n`, `n'`: the source of `ac_to_fg` is the deepest fast block in the viable tree
(`ac_to_fg_eq_ok_facts`).

Read aloud: the landed Lemma 48 holds at the AC state and the frame of every pair of node
states. -/
theorem lem48_attestation_source_recovered {V : Type} [DecidableEq V] [Fintype V] [RootOrder] :
    ∀ (C : Config) (n n' : NodeState V) (t : Time) (B : Block V),
      type_of% (@GoldilocksCorrectness.Proofs.Routines.lem48_attestation_source V _ _ _ C n'.A
        (fg_to_ac n.S) t B) := by
  intro C n n' t B hFast hAnc hViable fi hfi
  rw [(ac_to_fg_eq_ok_facts hfi).1]
  exact lem48_attestation_source Model.goldilocks n n' B hFast hAnc hViable

/-- The landed `GoldilocksCorrectness.Proofs.Routines.lem48b_anchor_is_locked_block`, recovered from
its record form at the spec's model: the spec's anchor is `AnchorAt` over the frame with the AC
state's lock entries (`goldilocks_get_anchor_eq_anchorAt_frame`), and the head of `ac_to_fg` is
reached by walk steps from it at the Goldilocks tie-break (`walkSteps_of_ghost_eq_ok`).

Read aloud: the landed Lemma 48b holds, as the record's theorem at the spec's model. -/
theorem lem48b_anchor_is_locked_block_recovered {V : Type} [DecidableEq V] [Fintype V]
    [RootOrder] :
    type_of% (@GoldilocksCorrectness.Proofs.Routines.lem48b_anchor_is_locked_block V _ _ _) := by
  intro C A Φ t B hLocked hLocks hViable
  have hL : ∃ e ∈ A.lock_entries, t < e.d ∧ e.B ∈ Φ.tree ∧ B.ancestorEq e.B = true := by
    simp only [is_locked, is_live, decide_eq_true_eq, Bool.and_eq_true] at hLocked
    obtain ⟨e, he, ⟨h1, h2⟩, h3⟩ := hLocked
    exact ⟨e, he, h1, h2, h3⟩
  have hLs : ∀ e ∈ A.lock_entries, t < e.d → e.B ∈ Φ.tree → e.B.AncestorEq B :=
    fun e he h1 h2 => hLocks e he (by simp [is_live, h1, h2])
  have h := lem48b_anchor_is_locked_block Model.goldilocks Φ A.lock_entries t B hL hLs hViable
  have hga := goldilocks_get_anchor_eq_anchorAt_frame A Φ t
  refine ⟨hga.trans h.1, fun fi hfi => ?_⟩
  obtain ⟨-, sv, -, hfc⟩ := ac_to_fg_eq_ok_facts hfi
  rw [GoldilocksCorrectness.Proofs.Routines.goldfish_fork_choice_eq, hga] at hfc
  exact h.2 _ _ _ (GoldilocksCorrectness.Proofs.Routines.walkSteps_of_ghost_eq_ok hfc)

/-- The landed `GoldilocksCorrectness.Proofs.Routines.lem50_attestation_sent_at_source`, recovered
from its record form at the spec's model, at the anti-slashing record `n.Λ` of every node state
`n`: `create_attestation` builds `a` exactly when `a` is `AttestationFrom` of `n`
(`create_attestation_snd_eq_some_iff`).

Read aloud: the landed Lemma 50 holds at the record of every node state. -/
theorem lem50_attestation_sent_at_source_recovered {V : Type} [DecidableEq V] [Fintype V] :
    ∀ (n : NodeState V),
      type_of% (@GoldilocksCorrectness.Proofs.Routines.lem50_attestation_sent_at_source V
        n.Λ) := by
  intro n v h_c T_c h_j J h_F hLock hJ hTS hST hSTo
  obtain ⟨h1, h2⟩ := lem50_attestation_sent_at_source Model.goldilocks goldilocksFacts n v h_c T_c
    h_j J h_F hLock hJ hTS hST hSTo
  refine ⟨?_, fun hn ht hT => ?_⟩
  · rcases h1 with ⟨a, ha, hav⟩ | ⟨hno, hb⟩
    · exact Or.inl ⟨a, (create_attestation_snd_eq_some_iff n v h_c T_c h_j J h_F a).2 ha, hav⟩
    · refine Or.inr ⟨?_, hb⟩
      cases hc : (create_attestation n.Λ v h_c T_c h_j J h_F).2 with
      | none => rfl
      | some a =>
        exact absurd ((create_attestation_snd_eq_some_iff n v h_c T_c h_j J h_F a).1 hc) (hno a)
  · obtain ⟨a, ha, hav⟩ := h2 hn ht hT
    exact ⟨a, (create_attestation_snd_eq_some_iff n v h_c T_c h_j J h_F a).2 ha, hav⟩

end GoldilocksCorrectness.Record.Proofs.Routines
