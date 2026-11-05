module
public import GoldilocksCorrectness.Statements.Executions.HonestChainStatements
public import GoldilocksCorrectness.Statements.Executions.AsyncDeliveryStatements
public import GoldilocksCorrectness.Proofs.Executions.Lemma78UpTo
public import GoldilocksCorrectness.Proofs.Executions.Lemma79UpTo

@[expose] public section

/-!
# `HonestChainStatements.lean` with the delivery premises up to a bound

The theorems of `GoldilocksCorrectness/Statements/Executions/HonestChainStatements.lean` that name
a delivery premise, restated with `SynchronyFromWakeUpTo` and `CatchUpOnWakeUpTo` at a bound on
the deadlines. The bound
of each twin is the latest ordinary deadline `max t GST + Δ` of a send its proof reads, written in
the twin's own parameters.

* `lem78_update_confirmation_extends_voter_majority_chain`, `lem79_honestChainExtends_step`

No `axiom`, no `native_decide`, no `sorry`. The landed page is imported, never edited.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ voteTime supportCutoff dutyWindowStart)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Routines (CountedVotes expireLocks)
variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **Lemma 78, an honest confirmation update over a voter majority's chain.** In an execution
where every time is reached, corruption is permanent, blocks and Goldfish votes are delivered
within `Δ` after `GST` (synchrony from the receiver's wake, and catch-up on wake),
a root names one block among what honest validators hold, a block reaches a
validator only once it holds the parent, and nobody votes in an honest validator's name: if `GST`
is at most the vote time of slot `s`; every `u ∈ Hs` is in the slot-`s` committee, honest through
the support cutoff `c` of slot `s + 1`, put its slot-`s` vote for `H u` on the wire at its tick at
the vote time of slot `s`, and holds `H u`, a block that is `B` or a descendant of `B`, in its tree
then; the validators with a slot-`s` vote in `v`'s pool before `c` are fewer than twice `Hs`; `v`
is awake and honest at every time from the duty window's start of slot `s + 1` to `c`; and `v`'s
finalized block before `c` is compatible with `B` — then the confirmation of slot `s` that `v`
holds right after `c`, when it holds one, is `B` or a descendant of `B`.

Why: the state right after `c` holds the confirmation the update of slot `s + 1` saved
(`update_state_of_duty`). When `v`'s finalized block is `B` or an ancestor of `B`, Lemma 12 at `c`
delivers every member's vote to `v`, held early, and Lemma 77 makes the saved confirmation `B` or a
descendant of `B`. When `B` is an ancestor of `v`'s finalized block, the saved confirmation is that
finalized block or a descendant of it (`saved_confirmation_F_ancestorEq`). This is Lemma 27 with
the votes on `B`'s chain in place of votes for `B`, the finalized block compatible with `B` in
place of an ancestor of `B`, without its conditions that `B` is not the genesis block and on the
locks, and concluding on the saved confirmation only.

The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s`: the slot of the votes;
- `Hs`: the honest voters of slot `s`; `H`: the block each voter's vote is for;
- `B`: the block every vote of `Hs` extends; `v`: the validator running the confirmation update of
  slot `s + 1`.

Read aloud: if every member of `Hs` is a member of the slot-`s` committee, honest through the
support cutoff of slot `s + 1`, that sent at the vote time of slot `s` a vote for a block it holds
that is `B` or a descendant of `B`; the members of `Hs` are more than half of the validators with a
slot-`s` vote in `v`'s pool before that cutoff; `v` is awake and honest from the duty window's
start of slot `s + 1` to that cutoff; and `v`'s finalized block before the cutoff is compatible with
`B` — then the confirmation of slot `s` that `v` holds right after the cutoff, when it holds one,
is `B` or a descendant of `B`.

Roots name blocks until `supportCutoff S s`: the bound of the Lemma 12 call at slot `s` its
proof passes the premise to.

Restated with the delivery premises up to `supportCutoff S s`: the slot-`s` votes reach `v` by then (`lem12_honest_vote_delivered_until_upTo`). -/
theorem lem78_update_confirmation_extends_voter_majority_chain_upTo (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (GST s : ℕ) (Hs : Finset V) (H : V → Block V) (B : Block V) (v : V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S s))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S s))
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S s))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    (hGST : GST ≤ voteTime S s)
    -- every member of `Hs` is a member of the slot-`s` committee, honest through the support
    -- cutoff of slot `s + 1`, that sent its slot-`s` vote for `H u`, a block it holds that is `B`
    -- or a descendant of `B`
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ Sched.adv (supportCutoff S (s + 1) : Int) ∧
      (∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
          SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) ∧
      H u ∈ (stateBefore x (voteTime S s) u).S.T ∧ B.AncestorEq (H u))
    -- the validators with a slot-`s` vote in `v`'s pool before the cutoff are fewer than twice
    -- `Hs`
    (hVoters : voters_count ((stateBefore x (supportCutoff S (s + 1)) v).A.pool s) <
      2 * Hs.card)
    -- `v` is awake and honest from the duty window's start of slot `s + 1` to the cutoff
    (hv : ∀ t : ℕ, dutyWindowStart S (s + 1) ≤ t → t ≤ supportCutoff S (s + 1) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    -- `v`'s finalized block before the cutoff is compatible with `B`
    (hF : (stateBefore x (supportCutoff S (s + 1)) v).S.F.compatible B = true) :
    -- then `v`'s confirmation of slot `s` right after the cutoff is on `B`'s chain
    ∀ C' : Block V,
      (stateBefore x (supportCutoff S (s + 1) + 1) v).A.saved_confirmation s = some C' →
      B.AncestorEq C' :=
  GoldilocksCorrectness.Proofs.Executions.lem78_update_confirmation_extends_voter_majority_chain_upTo S
    Sched x GST s Hs H B v hDiv hMono hSync hCatch hRoots hParent hOwner hGST hHs hVoters hv
    hF

/-- **Lemma 79, the step of the slot invariant restricted to a block.** In an execution where every
time is reached, corruption is permanent, blocks and Goldfish votes are delivered within `Δ` after
`GST` (synchrony from the receiver's wake, and catch-up on wake), a root
names one block among what honest validators hold, a block reaches a validator only once it holds
the parent, and nobody votes in an honest validator's name: if `GST` is at most the vote time of
slot `s'`; `HonestChainExtends S Sched x Hon B s'` holds; the members of `Hon` are awake and honest
from the duty window's start of slot `s' + 1` to the support cutoff of slot `s' + 2`; for each of
the slots `s'` and `s' + 1`, every member of `Hs` of that slot is a member of `Hon` and of that
slot's committee that put a vote of that slot on the wire at its tick at that slot's vote time; at
every member `w` voting at slot `s' + 1`, the validators with a vote among those `w` counts are
fewer than twice `Hs s'`, the root of `w`'s fork choice is compatible with `B`, and, when that root
is `B` or an ancestor of `B`, some block of `w`'s voter tree on `B`'s chain is a viable head; and at
every member `v` running the update of slot `s' + 2`, the slot-`(s' + 1)` voters of `v`'s pool
before the support cutoff of slot `s' + 2` are fewer than twice `Hs (s' + 1)`, and `v`'s finalized
block then is compatible with `B` — then `HonestChainExtends S Sched x Hon B (s' + 1)` holds.



Why: the three clauses at slot `s' + 1` are Lemmas 79a, 79b and 79c; Lemma 79c reads Lemma 79a's
conclusion.

The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s'`: the slot of the invariant;
- `Hon`: the validators the invariant is read at; `Hs`: the honest voters of each slot;
- `B`: the block.

Read aloud: the invariant at slot `s'` gives the invariant at slot `s' + 1`, when the members stay
awake and honest through the next slot, the honest voters of each slot are a majority of the voters
the members count, and the members' finalized blocks and fork-choice roots are compatible with `B`.

Roots name blocks until `supportCutoff S (s' + 1)`: Lemma 79c, which the proof calls, takes
blocks as held up to the support cutoff of slot `s' + 1`; Lemma 79a reads earlier.

Restated with the delivery premises up to `supportCutoff S (s' + 1)`: the slot-`(s' + 1)` votes reach every updater by then (`lem79c_honestChainExtends_confirmations_step_upTo`). -/
theorem lem79_honestChainExtends_step_upTo (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched)
    (GST s' : ℕ) (Hon : Finset V) (Hs : ℕ → Finset V) (B : Block V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S (s' + 1)))
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject (supportCutoff S (s' + 1)))
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s' + 1)))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    (hGST : GST ≤ voteTime S s')
    -- the slot invariant restricted to `B` holds at slot `s'`
    (hInv : HonestChainExtends S Sched x Hon B s')
    -- the members of `Hon` are awake and honest from the duty window's start of slot `s' + 1` to
    -- the support cutoff of slot `s' + 2`
    (hHon : ∀ v ∈ Hon, ∀ t : ℕ, dutyWindowStart S (s' + 1) ≤ t → t ≤ supportCutoff S (s' + 2) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    -- the honest voters of slots `s'` and `s' + 1`, members of `Hon` and of the slot's committee
    -- that sent a vote of the slot at its vote time
    (hHs : ∀ s₀ : ℕ, s₀ = s' ∨ s₀ = s' + 1 → ∀ u ∈ Hs s₀, u ∈ Hon ∧ u ∈ S.P.committee s₀ ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s₀ ∧
        ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S s₀) ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x[i + 1].sent - x[i].sent)
    -- the voter bound at every member voting at slot `s' + 1`
    (hVotersW : ∀ w ∈ Hon, ∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes S.C (stateBefore x (voteTime S (s' + 1)) w).A
        (fg_to_ac (stateBefore x (voteTime S (s' + 1)) w).S) (s' + 1) votes support_votes →
      voters_count votes < 2 * (Hs s').card)
    -- the voter bound at every member running the update of slot `s' + 2`
    (hVotersV : ∀ v ∈ Hon,
      voters_count ((stateBefore x (supportCutoff S (s' + 2)) v).A.pool (s' + 1)) <
        2 * (Hs (s' + 1)).card)
    -- at every member voting at slot `s' + 1`, the root of its fork choice is compatible with `B`
    (hF2 : ∀ w ∈ Hon,
      (fg_to_ac (stateBefore x (voteTime S (s' + 1)) w).S).fc_root.compatible B = true)
    -- at every member voting at slot `s' + 1`, when that root is `B` or an ancestor of `B`, a
    -- block of its voter tree on `B`'s chain is a viable head
    (hF3 : ∀ w ∈ Hon,
      (fg_to_ac (stateBefore x (voteTime S (s' + 1)) w).S).fc_root.AncestorEq B →
      ∀ tree : Finset (Block V),
        voter_block_tree S.C (stateBefore x (voteTime S (s' + 1)) w).A
          (fg_to_ac (stateBefore x (voteTime S (s' + 1)) w).S) (s' + 1) = .ok tree →
        ∃ W ∈ tree, W ∈ (fg_to_ac (stateBefore x (voteTime S (s' + 1)) w).S).viable_heads ∧
          B.AncestorEq W)
    -- the finalized block of every member running the update of slot `s' + 2` is compatible
    -- with `B`
    (hFv : ∀ v ∈ Hon,
      (stateBefore x (supportCutoff S (s' + 2)) v).S.F.compatible B = true) :
    -- then the slot invariant restricted to `B` holds at slot `s' + 1`
    HonestChainExtends S Sched x Hon B (s' + 1) :=
  GoldilocksCorrectness.Proofs.Executions.lem79_honestChainExtends_step_upTo S Sched x GST s' Hon Hs B
    hDiv hMono hSync hCatch hRoots hParent hOwner hGST hInv hHon hHs hVotersW hVotersV hF2
    hF3 hFv

end GoldilocksCorrectness.Statements.Executions

