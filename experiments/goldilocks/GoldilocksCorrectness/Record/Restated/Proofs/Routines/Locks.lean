module
public import GoldilocksCorrectness.Record.Facts
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.TickLocksGoldilocks
public import GoldilocksCorrectness.Proofs.Routines.Locks
public import GoldilocksCorrectness.Proofs.Routines.PeriodLocks

@[expose] public section

/-!
# The revocation of the locks, over a model

The theorems of `GoldilocksCorrectness/Proofs/Routines/Locks.lean`,
`GoldilocksCorrectness/Proofs/Routines/Confirmation.lean` and
`GoldilocksCorrectness/Proofs/Routines/PeriodLocks.lean` about the revocation of the locks
(`revoke_locks`) and the opponents of a block, over a model `M`: each takes the record's predicate
`LocksRevoked M P n t s n'` where the landed theorem takes the spec's answer, and the record's
`Opposes` and `OpponentsOf` where it takes the spec's `opposes` and `opponents`.

`opposes_iff`, `mem_opponentsOf` and `exists_vote_of_mem_opponentsOf` restate
`opposes_eq_ok`, `mem_opponents_of_eq_ok` and `exists_vote_of_mem_opponents` over the record's
definitions; the landed three are about the spec's routines, which the record does not have, and
are what the bridge at the spec's model uses (`TickLocksGoldilocks.lean`). `revoke_locks_zero`
restates the landed equation at slot `0` as what `LocksRevoked` says there.

The recovery section states the other landed theorems again, as the landed statement
(`type_of%`), at the AC state `n.A` and the frame `fg_to_ac n.S` of a node state `n`, and proves
each from its record form at the spec's model, through the bridge `locksRevoked_at_node`. Each
recovery takes, as a hypothesis the landed theorem does not have, that no two blocks of the tree of
`fg_to_ac n.S` share a root (the bridge reads the record's `Opposes` and the resolution time
through it), or the spec's node invariant where the landed statement names the spec's
`opponents`, whose answer the invariant's stamps give.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

namespace GoldilocksCorrectness.Record.Proofs.Routines

open Goldilocks
open GoldilocksCorrectness.Record
open GoldilocksCorrectness.Record.Statements.Routines (Opposes OpponentsOf ResolvesAt LocksRevoked
  MoveCandidate MovesTo locksRevoked_at_node opponentsOf_of_opponents_eq_ok
  opponents_answers_of_nodeInv lockEntry_eq_mk)
open GoldilocksCorrectness.Statements.Routines (RootsNameBlocksIn)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl)

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The opponents -/

/-- `Opposes M n B' vote` holds exactly when some block of the tree of `M.fg_to_ac n` has the
vote's head as its root and conflicts with `B'` (the record form of `opposes_eq_ok`).

The variables:
- `M`: the model; `n`: the node state; `B'`: the block; `vote`: the vote.

Read aloud: a vote opposes `B'` exactly when its head block conflicts with `B'`. -/
theorem opposes_iff (M : GoldilocksModel V) (n : M.N) (B' : Block V) (vote : GoldfishVote V) :
    Opposes M n B' vote ↔
      ∃ H ∈ (M.fg_to_ac n).tree, H.root = vote.head ∧ H.conflicts B' = true :=
  Iff.rfl

/-- Every validator not in `eqv` with a vote in `votes` that resolves and opposes `B'` is in the
opponents of `B'` (the record form of `mem_opponents_of_eq_ok`).

The variables:
- `M`: the model; `n`: the node state; `votes`, `eqv`: the votes counted and the validators
  counted out; `B'`: the block; `o`: the opponents; `vote`: the vote; `v`: its validator; `y`:
  its resolution time.

Read aloud: a resolving opposing vote makes its validator an opponent. -/
theorem mem_opponentsOf {M : GoldilocksModel V} {n : M.N} {votes : Finset (GoldfishVote V)}
    {eqv : Finset V} {B' : Block V} {o : Finset V} (h : OpponentsOf M n votes eqv B' o)
    {vote : GoldfishVote V} {v : V}
    -- the vote is one of `votes`, by `v`
    (hvote : vote ∈ votes) (hval : vote.val_index = v)
    -- `v` is not counted out
    (hne : v ∉ eqv)
    -- the vote resolves at `y`
    {y : Stamp} (hτ : ResolvesAt M n vote y)
    -- the vote opposes `B'`
    (hopp : Opposes M n B' vote) :
    v ∈ o :=
  (h v).2 ⟨hne, vote, hvote, hval, ⟨y, hτ⟩, hopp⟩

/-- Every opponent of `B'` has a vote among `votes` that opposes `B'` (the record form of
`exists_vote_of_mem_opponents`).

The variables:
- `M`: the model; `n`: the node state; `votes`, `eqv`: the votes counted and the validators
  counted out; `B'`: the block; `o`: the opponents; `v`: the opponent.

Read aloud: an opponent has an opposing vote. -/
theorem exists_vote_of_mem_opponentsOf {M : GoldilocksModel V} {n : M.N}
    {votes : Finset (GoldfishVote V)} {eqv : Finset V} {B' : Block V} {o : Finset V}
    (h : OpponentsOf M n votes eqv B' o) {v : V} (hv : v ∈ o) :
    ∃ vote ∈ votes, vote.val_index = v ∧ Opposes M n B' vote := by
  obtain ⟨-, vote, hvote, hval, -, hopp⟩ := (h v).1 hv
  exact ⟨vote, hvote, hval, hopp⟩

/-! ## The revocation -/

/-- After the revocation of the locks of slot `s ≥ 1`, every lock entry left is on a block of the
tree of `M.fg_to_ac n` (the record form of `revoke_locks_entry_mem_tree`).

The variables:
- `M`: the model; `P`: the provisional parameters; `n`, `n'`: the node states before and after;
- `t`: the time; `s`: the slot.

Read aloud: every lock left by the revocation is on a block of the tree. -/
theorem revoke_locks_entry_mem_tree {M : GoldilocksModel V} {P : Provisional V} {n n' : M.N}
    {t : Time} {s : Slot}
    -- the slot is not the first
    (hs : 1 ≤ s)
    -- the revocation of slot `s` leaves `n'`
    (hRevoke : LocksRevoked M P n t s n') :
    ∀ e ∈ n'.lockEntries, e.B ∈ (M.fg_to_ac n).tree := by
  rcases hRevoke with ⟨h0, -⟩ | ⟨-, h1, -⟩
  · exact absurd h0 (Nat.one_le_iff_ne_zero.1 hs)
  · intro e he
    obtain ⟨e₀, -, -, -, hmt⟩ := h1 e he
    exact hmt.1.1

/-- The revocation of slot `0` leaves exactly the lock entries of `n` whose deadline is after `t`
(the record form of `revoke_locks_zero`).

The variables:
- `M`: the model; `P`: the provisional parameters; `n`, `n'`: the node states before and after;
- `t`: the time.

Read aloud: at slot `0` the revocation only deletes the expired locks. -/
theorem revoke_locks_zero {M : GoldilocksModel V} {P : Provisional V} {n n' : M.N} {t : Time}
    (hRevoke : LocksRevoked M P n t 0 n') :
    ∀ e : M.LE, e ∈ n'.lockEntries ↔ e ∈ n.lockEntries ∧ t < e.d := by
  rcases hRevoke with ⟨-, h⟩ | ⟨h, -⟩
  · exact h
  · exact absurd h (by decide)

/-- After the revocation of the locks of slot `s ≠ 0`, every lock entry left is on a block whose
opponents among the slot-`(s − 1)` votes, the equivocators counted out, are, counted twice, fewer
than the committee of slot `s − 1` (the record form of `revoke_locks_entry_opponents_lt`).

The variables:
- `M`: the model; `P`: the provisional parameters; `n`, `n'`: the node states before and after;
- `t`: the time; `s`: the slot; `e`: the entry.

Read aloud: a lock left by the revocation is on a block fewer than half of the committee
oppose. -/
theorem revoke_locks_entry_opponents_lt {M : GoldilocksModel V} {P : Provisional V}
    {n n' : M.N} {t : Time} {s : Slot} (hs : s ≠ 0) (hRevoke : LocksRevoked M P n t s n')
    (e : M.LE) (he : e ∈ n'.lockEntries) :
    ∃ o : Finset V, OpponentsOf M n (M.votesHeldSet n (s - 1))
        (M.equivocators (M.votesHeldSet n (s - 1))) e.B o ∧
      2 * o.card < (P.committee (s - 1)).card := by
  rcases hRevoke with ⟨h0, -⟩ | ⟨-, h1, -⟩
  · exact absurd h0 hs
  · obtain ⟨e₀, -, -, -, hmt⟩ := h1 e he
    exact hmt.1.2.2.2

/-- The revocation of slot `s' ≠ 0` keeps, as an entry with the same block and deadline, a live
lock entry of `n` on a block other than the genesis block whose opponents, counted twice, are fewer
than the committee of slot `s' − 1` (the record form of `revoke_locks_keeps_entry`; an entry of
an arbitrary model is named by its block and deadline).

The variables:
- `M`: the model; `F`: its facts; `P`: the provisional parameters; `n`, `n'`: the node states
  before and after; `t`: the time; `s'`: the slot; `e`: the entry.

Read aloud: a live lock fewer than half of the committee oppose survives the revocation. -/
theorem revoke_locks_keeps_entry {M : GoldilocksModel V} (F : Facts M) {P : Provisional V}
    {n n' : M.N} {t : Time} {s' : Slot} (e : M.LE)
    (hs' : s' ≠ 0) (hrev : LocksRevoked M P n t s' n')
    (he : e ∈ n.lockEntries) (hlive : M.is_live n t e = true) (hgen : e.B ≠ Block.genesis)
    (hopp : ∀ o : Finset V, OpponentsOf M n (M.votesHeldSet n (s' - 1))
      (M.equivocators (M.votesHeldSet n (s' - 1))) e.B o →
      2 * o.card < (P.committee (s' - 1)).card) :
    ∃ e' ∈ n'.lockEntries, e'.B = e.B ∧ e'.d = e.d := by
  classical
  have hT : e.B ∈ (M.fg_to_ac n).tree := by
    have h := hlive
    rw [F.rd.is_live_eq] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.2
  -- the opponents of `e.B`
  let votes := M.votesHeldSet n (s' - 1)
  let o : Finset V := Finset.univ.filter fun v => v ∉ M.equivocators votes ∧
    ∃ vote ∈ votes, vote.val_index = v ∧ (∃ y : Stamp, ResolvesAt M n vote y) ∧
      Opposes M n e.B vote
  have hOpp : OpponentsOf M n votes (M.equivocators votes) e.B o := fun v => by
    simp only [o, Finset.mem_filter, Finset.mem_univ, true_and]
  have hmt : MovesTo M P n s' e e.B :=
    ⟨⟨hT, hgen, ancestorEq_refl _, o, hOpp, hopp o hOpp⟩, fun _ h => h.2.2.1⟩
  rcases hrev with ⟨h0, -⟩ | ⟨-, -, h2⟩
  · exact absurd h0 hs'
  · exact h2 e he hlive e.B hmt

/-- After the revocation of the locks of slot `s ≥ 1`, no lock entry left is on the genesis block
(the record form of `revoke_locks_entry_ne_genesis`).

The variables:
- `M`: the model; `P`: the provisional parameters; `n`, `n'`: the node states before and after;
- `t`: the time; `s`: the slot.

Read aloud: no lock left by the revocation is on the genesis block. -/
theorem revoke_locks_entry_ne_genesis {M : GoldilocksModel V} {P : Provisional V} {n n' : M.N}
    {t : Time} {s : Slot}
    (hs : 1 ≤ s)
    (hRevoke : LocksRevoked M P n t s n') :
    ∀ e ∈ n'.lockEntries, e.B ≠ Block.genesis := by
  rcases hRevoke with ⟨h0, -⟩ | ⟨-, h1, -⟩
  · exact absurd h0 (Nat.one_le_iff_ne_zero.1 hs)
  · intro e he
    obtain ⟨e₀, -, -, -, hmt⟩ := h1 e he
    exact hmt.1.2.1

/-! ## At the spec's model -/

/-- The landed `GoldilocksCorrectness.Proofs.Routines.revoke_locks_entry_mem_tree`, recovered from
its record form at the spec's model, at the AC state `n.A` and the frame `fg_to_ac n.S` of every
node state `n` whose frame's tree has no two blocks sharing a root.

Read aloud: the landed theorem holds at every node state whose frame's roots name its blocks. -/
theorem revoke_locks_entry_mem_tree_recovered {V : Type} [DecidableEq V] [Fintype V] [RootOrder] :
    ∀ (P : Provisional V) (n : NodeState V) (A' : ACState V) (t : Time) (s : Slot),
      RootsNameBlocksIn (fg_to_ac n.S).tree →
      type_of% (@GoldilocksCorrectness.Proofs.Routines.revoke_locks_entry_mem_tree V _ _ _ P n.A A' (fg_to_ac n.S) t s) := by
  intro P n A' t s hR hs hRevoke
  exact revoke_locks_entry_mem_tree hs
    (locksRevoked_at_node P n t s A' hR (Nat.one_le_iff_ne_zero.1 hs) hRevoke)

/-- The landed `GoldilocksCorrectness.Proofs.Routines.revoke_locks_entry_opponents_lt`, recovered
from its record form at the spec's model, at the AC state `n.A` and the frame `fg_to_ac n.S` of
every node state `n` satisfying the spec's node invariant.

Read aloud: the landed theorem holds at every node state satisfying the invariant. -/
theorem revoke_locks_entry_opponents_lt_recovered {V : Type} [DecidableEq V] [Fintype V] [RootOrder] :
    ∀ (C : Config) (P : Provisional V) (X : External V) (n : NodeState V) (A' : ACState V) (t : Time) (s : Slot),
      (Model.goldilocks (V := V)).nodeInv C P X n →
      type_of% (@GoldilocksCorrectness.Proofs.Routines.revoke_locks_entry_opponents_lt V _ _ _ P n.A A' (fg_to_ac n.S) t s) := by
  intro C P X n A' t s hI hs hRevoke e he
  have hR := GoldilocksCorrectness.Proofs.Routines.nodeInv_frameRoots hI.1
  obtain ⟨o, ho, hlt⟩ := revoke_locks_entry_opponents_lt hs
    (locksRevoked_at_node P n t s A' hR hs hRevoke) e he
  obtain ⟨o', ho'⟩ := opponents_answers_of_nodeInv hI.1 (s - 1) e.B
  have hoo : o' = o := Finset.ext fun v =>
    ((opponentsOf_of_opponents_eq_ok n ⟨rfl, rfl, rfl⟩ hR ho') v).trans (ho v).symm
  exact ⟨o', ho', hoo ▸ hlt⟩

/-- The landed `GoldilocksCorrectness.Proofs.Routines.revoke_locks_keeps_entry`, recovered from its
record form at the spec's model, at the AC state `n.A` and the frame `fg_to_ac n.S` of every node
state `n` satisfying the spec's node invariant.

Read aloud: the landed theorem holds at every node state satisfying the invariant. -/
theorem revoke_locks_keeps_entry_recovered {V : Type} [DecidableEq V] [Fintype V] [RootOrder] :
    ∀ (C : Config) (P : Provisional V) (X : External V) (n : NodeState V) (A' : ACState V) (t : Time) (s' : Slot) (e : LockEntry V),
      (Model.goldilocks (V := V)).nodeInv C P X n →
      type_of% (@GoldilocksCorrectness.Proofs.Routines.revoke_locks_keeps_entry V _ _ _ P n.A A' (fg_to_ac n.S) t s' e) := by
  intro C P X n A' t s' e hI hs' hrev he hlive hgen hopp
  have hR := GoldilocksCorrectness.Proofs.Routines.nodeInv_frameRoots hI.1
  obtain ⟨e', he', hB, hd⟩ := revoke_locks_keeps_entry goldilocksFacts (n := n)
    (n' := { n with A := A' }) e hs' (locksRevoked_at_node P n t s' A' hR hs' hrev) he hlive hgen
    (fun o ho => by
      obtain ⟨o', ho'⟩ := opponents_answers_of_nodeInv hI.1 (s' - 1) e.B
      have hoo : o' = o := Finset.ext fun v =>
        ((opponentsOf_of_opponents_eq_ok n ⟨rfl, rfl, rfl⟩ hR ho') v).trans (ho v).symm
      exact hoo ▸ hopp o' ho')
  have hee : e' = e := lockEntry_eq_mk hB hd
  exact hee ▸ he'

/-- The landed `GoldilocksCorrectness.Proofs.Routines.revoke_locks_entry_ne_genesis`, recovered
from its record form at the spec's model, at the AC state `n.A` and the frame `fg_to_ac n.S` of
every node state `n` whose frame's tree has no two blocks sharing a root.

Read aloud: the landed theorem holds at every node state whose frame's roots name its blocks. -/
theorem revoke_locks_entry_ne_genesis_recovered {V : Type} [DecidableEq V] [Fintype V] [RootOrder] :
    ∀ (P : Provisional V) (n : NodeState V) (A' : ACState V) (t : Time) (s : Slot),
      RootsNameBlocksIn (fg_to_ac n.S).tree →
      type_of% (@GoldilocksCorrectness.Proofs.Routines.revoke_locks_entry_ne_genesis V _ _ _ P n.A A' (fg_to_ac n.S) t s) := by
  intro P n A' t s hR hs hRevoke
  exact revoke_locks_entry_ne_genesis hs
    (locksRevoked_at_node P n t s A' hR (Nat.one_le_iff_ne_zero.1 hs) hRevoke)

end GoldilocksCorrectness.Record.Proofs.Routines
