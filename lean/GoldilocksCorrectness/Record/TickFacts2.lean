module
public import GoldilocksCorrectness.Record.ModelSpellings
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.TickDefs

@[expose] public section

/-!
# The facts of the tick, part 2: the locks and the confirmation

`TickFacts2 M` holds, for a model `M`, what its tick does to the lock entries, the saved
confirmations, the fast blocks and the record of the confirmed tip at two duty times of the slot
of its time `t`, of every answer `(n', sent)` of the tick `M.tick C P X n t`:

- at the vote time `C.t_ (C.slot t) + C.Δ`, a node satisfying the model's node invariant and awake
  since the slot's duty window started (`AwakeFor`) revokes its locks: `LocksRevoked`;
- at the support cutoff `C.t_ (C.slot t) + 2 * C.Δ`, such a node updates its confirmation:
  `ConfirmationUpdated`;
- at either of the two times, a node not awake since the slot's duty window started deletes the
  lock entries whose deadline is not after `t`, and changes no other lock entry, no saved
  confirmation, no fast block and not the record of the confirmed tip.

Away from the two times, part 1 (`TickFacts1`, `TickFacts.lean`) says what the tick does to these
readers. The predicates are on `Record/Restated/Statements/Routines/TickDefs.lean`. This file holds
the structure only.
-/

set_option autoImplicit false

open scoped DC

namespace GoldilocksCorrectness.Record

open Goldilocks (Config Provisional External RootOrder Block GoldfishVote NamedObject Slot Time)
open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor LocksRevoked ConfirmationUpdated)

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The facts of `M` about the outcomes of a tick, `M.tick C P X n t`, part 2: what it does to the
locks and the confirmation at the vote time and at the support cutoff of the slot of `t`.

Read aloud: at the vote time an awake node's tick revokes the locks, at the support cutoff it
updates the confirmation, and a node not awake at either time only deletes the expired locks. -/
structure TickFacts2 (M : GoldilocksModel V) : Prop where
  /-- T4. A tick at the vote time of the slot of `t`, from a node state satisfying the model's node
      invariant and awake since that slot's duty window started, leaves the lock entries of the
      revocation of that slot (`LocksRevoked`).

      Read aloud: at the vote time, an awake node's tick revokes its locks. -/
  tick_voteTime_locks : ∀ [RootOrder] (C : Config) (P : Provisional V) (X : External V)
      (n : M.N) (t : Time) (n' : M.N) (sent : List (NamedObject V)),
    .ok (n', sent) ∈ M.tick C P X n t → M.nodeInv C P X n → t = C.t_ (C.slot t) + C.Δ →
      AwakeFor M C n (C.slot t) → LocksRevoked M P n t (C.slot t) n'
  /-- T4 under the clock-free part of the node invariant. A tick at the vote time of the slot of `t`,
      from a node state satisfying `M.nodeInvCore C P X n` and awake since that slot's duty window
      started, leaves the lock entries of the revocation of that slot (`LocksRevoked`). Added for a
      validator in the adversary set, for which only the clock-free part of Lemma 11 holds
.

      Read aloud: at the vote time, an awake node's tick revokes its locks, whatever its stamps. -/
  tick_voteTime_locks_of_core : ∀ [RootOrder] (C : Config) (P : Provisional V) (X : External V)
      (n : M.N) (t : Time) (n' : M.N) (sent : List (NamedObject V)),
    .ok (n', sent) ∈ M.tick C P X n t → M.nodeInvCore C P X n → t = C.t_ (C.slot t) + C.Δ →
      AwakeFor M C n (C.slot t) → LocksRevoked M P n t (C.slot t) n'
  /-- T6. A tick at the support cutoff of the slot of `t`, from a node state satisfying the model's
      node invariant and awake since that slot's duty window started, leaves what the
      confirmation update of that slot leaves (`ConfirmationUpdated`).

      Read aloud: at the support cutoff, an awake node's tick updates its confirmation. -/
  tick_supportCutoff_confirmation : ∀ [RootOrder] (C : Config) (P : Provisional V)
      (X : External V) (n : M.N) (t : Time) (n' : M.N) (sent : List (NamedObject V)),
    .ok (n', sent) ∈ M.tick C P X n t → M.nodeInv C P X n → t = C.t_ (C.slot t) + 2 * C.Δ →
      AwakeFor M C n (C.slot t) → ConfirmationUpdated M C P n t (C.slot t) n'
  /-- T6 under the clock-free part of the node invariant. A tick at the support cutoff of the slot of
      `t`, from a node state satisfying `M.nodeInvCore C P X n` and awake since that slot's duty
      window started, leaves what the confirmation update of that slot leaves
      (`ConfirmationUpdated`). Added for a validator in the adversary set, for which only the
      clock-free part of Lemma 11 holds.

      Read aloud: at the support cutoff, an awake node's tick updates its confirmation, whatever its
      stamps. -/
  tick_supportCutoff_confirmation_of_core : ∀ [RootOrder] (C : Config) (P : Provisional V)
      (X : External V) (n : M.N) (t : Time) (n' : M.N) (sent : List (NamedObject V)),
    .ok (n', sent) ∈ M.tick C P X n t → M.nodeInvCore C P X n → t = C.t_ (C.slot t) + 2 * C.Δ →
      AwakeFor M C n (C.slot t) → ConfirmationUpdated M C P n t (C.slot t) n'
  /-- A tick at the vote time or at the support cutoff of the slot of `t`, from a node state not
      awake since that slot's duty window started, leaves exactly `n`'s lock entries whose deadline
      is after `t`, and `n`'s saved confirmations, fast blocks and record of the confirmed tip.

      Read aloud: at the two duty times, a node not awake for the slot only deletes its expired
      locks. -/
  tick_dutyTime_not_awake : ∀ [RootOrder] (C : Config) (P : Provisional V) (X : External V)
      (n : M.N) (t : Time) (n' : M.N) (sent : List (NamedObject V)),
    .ok (n', sent) ∈ M.tick C P X n t →
      (t = C.t_ (C.slot t) + C.Δ ∨ t = C.t_ (C.slot t) + 2 * C.Δ) →
      ¬ AwakeFor M C n (C.slot t) →
        n'.lockEntries = {e ∈ n.lockEntries | t < e.d} ∧
          M.savedConfirmation n' = M.savedConfirmation n ∧ n'.fastBlocks = n.fastBlocks ∧
          n'.latestConfirmed = n.latestConfirmed

end GoldilocksCorrectness.Record
