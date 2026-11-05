module
public import GoldilocksCorrectness.Proofs.Executions.Lemma21
public import GoldilocksCorrectness.Proofs.Executions.Lemma36a

@[expose] public section

/-!
# The next slot's honest Goldfish vote extends a block an honest validator finds eligible

The audited statement of G2 over executions, `lem21_goldfish_vote_extends_eligible_block`, proved
in `GoldilocksCorrectness/Proofs/Executions/Lemma21.lean`.

Its corollary over a confirmation, `lem36a_confirmed_block_extended_by_next_honest_votes`, is
proved in `GoldilocksCorrectness/Proofs/Executions/Lemma36a.lean`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ voteTime supportCutoff viewFreeze)

open GoldilocksCorrectness.Statements.Routines (EarlySupporterOf)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Routines (expireLocks)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **Lemma 21, the next slot's honest vote extends a block an honest validator finds eligible.**
In an execution where every time is reached, corruption is permanent, blocks and Goldfish votes
are delivered within `Δ` after `GST` (synchrony from the receiver's wake, and catch-up on wake),
a root names one block among what honest validators hold, a block
reaches a validator only once it holds the parent: if `GST` is at most the support cutoff of slot
`s`; `v` is awake and honest at every time from the vote time `t₃` of slot `s + 1` to the support
cutoff `t₂` of slot `s + 1`; `w` is awake and honest at every time from the support cutoff of slot
`s` to the view freeze of slot `s`; on `v`'s node state before `t₂`, each
member of `Sup` has exactly one slot-`s` vote, resolved strictly before `S.C.t_ s + 2 · S.C.Δ`,
whose head is the root of a block of `v`'s frame tree that is `B` or a descendant of `B`
(`EarlySupporterOf`), and the validators with a slot-`s` vote in `v`'s pool are fewer than twice
`Sup`; on `w`'s node state before `t₃`, the root of the fork choice is compatible with `B` (F2),
when that root is `B` or an ancestor of `B` some block of `w`'s voter tree for slot `s + 1` that is
`B` or a descendant of `B` is a viable head (F3), and the block of every lock entry live at `t₃`
that `w`'s revocation of slot `s + 1` leaves is compatible with `B` (G4's condition); and `w` put
the Goldfish vote `vote` on the wire at its tick at `t₃` — then `vote`'s head is the root of a block
that is `B` or a descendant of `B`.



Why: `w`'s tick at `t₃` sent `vote`, so its head is the root of the end `H_w` of the Goldfish fork
choice from the anchor of `w`'s revoked AC state (Lemma 14). Each member `u` of `Sup` has its vote
in `v`'s pool before the support cutoff `c` of slot `s`; `v` re-sent it, so it reaches `w` before
the view freeze of slot `s`; `w` holds no second vote of `u` then, since every vote `w` re-sent
before `t₃` reaches `v` before `t₂`, where `u` has one vote; the vote's head reaches `w` before the
view freeze too, so the vote is counted at `w` as `u`'s only vote, a support vote for `B`'s chain.
Every validator with a vote `w` counts has a vote at `v` for the same reason, so `w`'s voters are
fewer than twice `Sup`. The anchor is compatible with `B` (Lemma 6, with the lock condition and
F2) and starts towards `B` (Lemma 7, with F3, the path blocks being ancestors of a supporter's head
stamped before the view freeze), so the fork choice ends at `B` or a descendant of `B` (Lemma 2).
When instead `B` is an ancestor of `w`'s finalized block, `B` is an ancestor of `fc_root` (Lemma
46), of the anchor, and so of `H_w`, which is the anchor or a descendant of it.



The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s`: the slot of the votes;
- `Sup`: the early supporters of `B`'s chain at `v`; `B`: the block `v` finds eligible;
- `v`: the validator whose confirmation update of slot `s` finds `B` eligible; `w`: the voter of
  slot `s + 1`;
- `vote`: the Goldfish vote `w` sent at the vote time of slot `s + 1`.

Read aloud: if the honest `v`'s state at the support cutoff of slot `s + 1` has a set `Sup` of
early supporters of `B`'s chain with fewer than twice `Sup` voters, `v` is awake and honest from the
vote time of slot `s + 1` to that cutoff, the honest `w` is awake from the support cutoff to the
view freeze of slot `s`, F2 and F3 hold for `B` at `w`, and no live lock `w`'s revocation leaves
conflicts with `B`, then `w`'s vote of slot `s + 1` is for `B` or a descendant of `B`.

Roots name blocks until `supportCutoff S (s + 1)`: Lemma 64, which the proof calls with `t_w :=
voteTime S (s + 1)`, takes blocks as held up to one delay after `w`'s fork choice. -/
theorem lem21_goldfish_vote_extends_eligible_block (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s : ℕ) (Sup : Finset V) (B : Block V) (v w : V)
    (vote : GoldfishVote V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s + 1)))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hGST : GST ≤ supportCutoff S s)
    -- `v`, awake and honest from the vote time to the support cutoff of slot `s + 1`
    (hv : ∀ t : ℕ, voteTime S (s + 1) ≤ t → t ≤ supportCutoff S (s + 1) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    -- `w`, awake and honest from the support cutoff to the view freeze of slot `s`
    (hw : ∀ t : ℕ, supportCutoff S s ≤ t → t ≤ viewFreeze S s →
      w ∈ Sched.awake (t : Int) ∧ w ∉ Sched.adv (t : Int))
    -- `B` is eligible at `v`'s update of slot `s`: each member of `Sup` is an early supporter of
    -- `B`'s chain at `v`, and `v`'s late voters are fewer than twice `Sup`
    (hSup : ∀ u ∈ Sup, EarlySupporterOf S.C (stateBefore x (supportCutoff S (s + 1)) v).A
      (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S) s B u)
    (hEligible : voters_count ((stateBefore x (supportCutoff S (s + 1)) v).A.pool s) <
      2 * Sup.card)
    -- the finality-gadget conditions at `w`, on its state before `voteTime S (s + 1)`
    (hF2 : (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).fc_root.compatible B = true)
    (hF3 : (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).fc_root.AncestorEq B →
      ∀ tree : Finset (Block V),
        voter_block_tree S.C (stateBefore x (voteTime S (s + 1)) w).A
          (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) (s + 1) = .ok tree →
        ∃ W ∈ tree, W ∈ (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).viable_heads ∧
          B.AncestorEq W)
    -- no live lock entry `w`'s revocation leaves conflicts with `B`
    (hLocks : ∀ A' : ACState V,
      revoke_locks S.P (expireLocks (stateBefore x (voteTime S (s + 1)) w).A
        ((voteTime S (s + 1) : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
        ((voteTime S (s + 1) : ℕ) : Int) (s + 1) = .ok A' →
      ∀ e ∈ A'.lock_entries,
        is_live (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
          ((voteTime S (s + 1) : ℕ) : Int) e = true → e.B.compatible B = true)
    (hSend : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (s + 1)) ∧
      (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent) :
    ∃ H_w : Block V, vote.head = H_w.root ∧ B.AncestorEq H_w :=
  GoldilocksCorrectness.Proofs.Executions.lem21_goldfish_vote_extends_eligible_block S Sched x GST
    s Sup B v w vote hDiv hMono hSync hCatch hRoots hParent hGST hv hw hSup hEligible
    hF2 hF3 hLocks hSend

/-- **Lemma 36a, a confirmed block is extended by the next slot's honest votes.** In an execution
where every time is reached, corruption is permanent, blocks and Goldfish votes are delivered
within `Δ` after `GST` (synchrony from the receiver's wake, and catch-up on wake),
a root names one block among what honest validators hold, and a block reaches a
validator only once it holds the parent: if `GST` is at most the support cutoff of slot `s`; `v` is
awake and honest at every time from the vote time `t₃` of slot `s + 1` to the support cutoff `t₂`
of slot `s + 1`; `w` is awake and honest at every time from the support cutoff to the view freeze
of slot `s`; `v`'s confirmation update of slot `s + 1`, on its node state before `t₂` with the
expired lock entries removed, answers `A'`, and `A'` saves `C'` as the confirmation of slot `s`;
on `w`'s node state before `t₃`, the root of the fork choice is compatible with `C'` (F2), when that
root is `C'` or an ancestor of `C'` some block of `w`'s voter tree for slot `s + 1` that is `C'` or
a descendant of `C'` is a viable head (F3), and the block of every lock entry live at `t₃` that
`w`'s revocation of slot `s + 1` leaves is compatible with `C'`; and `w` put the Goldfish vote
`vote` on the wire at its tick at `t₃` — then `vote`'s head is the root of a block that is `C'` or a
descendant of `C'`.

Why: Lemma 36, at the block `C'` itself, gives a set `Sup` of early supporters of `C'` at `v`, with
the validators holding a slot-`s` vote in `v`'s pool before `t₂` fewer than twice `Sup`; its
hypothesis on the pool's stamps holds, every vote in the pool before `t₂` being stamped before
`t₂`. Removing the expired lock entries changes neither the pool nor the stamps, so these are the
hypotheses of Lemma 21 for `B := C'`, which concludes.



The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s`: the slot whose confirmation `v`'s
  update of slot `s + 1` saves;
- `C'`: the saved confirmation; `v`: the validator whose update saves it; `A'`: that update's
  answer;
- `w`: the voter of slot `s + 1`; `vote`: the Goldfish vote `w` sent at the vote time of slot
  `s + 1`.

Read aloud: if the honest `v`'s confirmation update at the support cutoff of slot `s + 1` saves
`C'` as the confirmation of slot `s`, `v` being awake and honest from the vote time of slot
`s + 1` to that cutoff, then every honest voter `w` of slot `s + 1` that is awake from the support
cutoff to the view freeze of slot `s`, meets F2 and F3 for `C'`, and has no live lock left by its
revocation that conflicts with `C'`, votes for `C'` or a descendant of `C'`.

Roots name blocks until `supportCutoff S (s + 1)`: Lemma 21, which the proof calls, takes blocks
as held up to one delay after `w`'s vote time of slot `s + 1`. -/
theorem lem36a_confirmed_block_extended_by_next_honest_votes (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s : ℕ) (C' : Block V) (v w : V) (A' : ACState V)
    (vote : GoldfishVote V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s + 1)))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hGST : GST ≤ supportCutoff S s)
    -- `v`, awake and honest from the vote time to the support cutoff of slot `s + 1`
    (hv : ∀ t : ℕ, voteTime S (s + 1) ≤ t → t ≤ supportCutoff S (s + 1) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    -- `w`, awake and honest from the support cutoff to the view freeze of slot `s`
    (hw : ∀ t : ℕ, supportCutoff S s ≤ t → t ≤ viewFreeze S s →
      w ∈ Sched.awake (t : Int) ∧ w ∉ Sched.adv (t : Int))
    -- `v`'s update of slot `s + 1`, on its state before the support cutoff with the expired lock
    -- entries removed, answers `A'`
    (hUpdate : update_confirmation S.C S.P
        (expireLocks (stateBefore x (supportCutoff S (s + 1)) v).A
          ((supportCutoff S (s + 1) : ℕ) : Int))
        (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S)
        ((supportCutoff S (s + 1) : ℕ) : Int) (s + 1) = .ok A')
    -- `A'` saves `C'` as the confirmation of slot `s`
    (hSaved : A'.saved_confirmation s = some C')
    -- the finality-gadget conditions at `w`, on its state before `voteTime S (s + 1)`
    (hF2 : (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).fc_root.compatible C' = true)
    (hF3 : (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).fc_root.AncestorEq C' →
      ∀ tree : Finset (Block V),
        voter_block_tree S.C (stateBefore x (voteTime S (s + 1)) w).A
          (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) (s + 1) = .ok tree →
        ∃ W ∈ tree, W ∈ (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).viable_heads ∧
          C'.AncestorEq W)
    -- no live lock entry `w`'s revocation leaves conflicts with `C'`
    (hLocks : ∀ A'' : ACState V,
      revoke_locks S.P (expireLocks (stateBefore x (voteTime S (s + 1)) w).A
        ((voteTime S (s + 1) : ℕ) : Int)) (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
        ((voteTime S (s + 1) : ℕ) : Int) (s + 1) = .ok A'' →
      ∀ e ∈ A''.lock_entries,
        is_live (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S)
          ((voteTime S (s + 1) : ℕ) : Int) e = true → e.B.compatible C' = true)
    -- `w` put `vote` on the wire at its tick at the vote time of slot `s + 1`
    (hSend : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (s + 1)) ∧
      (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent) :
    ∃ H_w : Block V, vote.head = H_w.root ∧ C'.AncestorEq H_w :=
  GoldilocksCorrectness.Proofs.Executions.lem36a_confirmed_block_extended_by_next_honest_votes S
    Sched x GST s C' v w A' vote hDiv hMono hSync hCatch hRoots hParent hGST hv hw hUpdate
    hSaved hF2 hF3 hLocks hSend

end GoldilocksCorrectness.Statements.Executions
