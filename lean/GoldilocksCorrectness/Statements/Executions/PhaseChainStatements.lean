module
public import GoldilocksCorrectness.Proofs.Executions.PhaseChain

@[expose] public section

/-!
# The chain machinery of the phase

The audited statements, proved in `GoldilocksCorrectness/Proofs/Executions/PhaseChain.lean`:

- `lem89s_phase_step`, the chain step inside the phase over the member sets of two consecutive
  slots: both invariants carried from slot `s'` to slot `s' + 1`;
- Lemma 89c, `lem89c_rebase`, the re-base: one slot after every member's fork-choice root is one
  block `R`, with the members awake and honest to the support cutoff of slot `s + 1`, the slot
  invariant restricted to `R` holds;
- Lemma 45b, `lem45b_honest_vote_extends_lock_held`, Lemma 45's conclusion in the held form of
  `HonestChainExtends`'s first clause.


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
open GoldilocksCorrectness.Statements.Routines (expireLocks)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-! ## The phase step -/

/-- **The phase step.** In an execution where every time is reached, corruption is
permanent, blocks and Goldfish votes are delivered within `Δ` after `GST` (synchrony from the
receiver's wake, and catch-up on wake), a root names one block among
what honest validators hold, a block reaches a validator only once it holds the parent, and nobody
votes in an honest validator's name: if `GST` is at most the vote time of slot `s'`; the members
of `Hon` are awake and honest from the duty window's start of slot `s'` to the support cutoff of
slot `s' + 1`; the members of `Hon' ⊆ Hon` are awake and honest from the duty window's start of
slot `s' + 1` to the support cutoff of slot `s' + 2`; the committee of slot `s'` has fewer than
twice its members in `Hon`, and that of slot `s' + 1` fewer than twice its members in `Hon'`;
`ChainInvFor S Sched x Hon 𝓒 s'` holds; every member of `Hon` satisfies
`LiveLocksOnFamilyAt S Sched x 𝓒 s'`; and `StepFrameAt S Sched x C s' w` holds at every member `w`
of `Hon'` for every block `C` of `𝓒` and every confirmation `C` of slot `s'` a member of `Hon'`
holds right after the support cutoff of slot `s' + 1` — then, for the family of the blocks of `𝓒`
and the blocks that are such a confirmation or an ancestor of one, `ChainInvFor` holds at slot
`s' + 1` at `Hon'`, and every member of `Hon'` satisfies `LiveLocksOnFamilyAt` at slot `s' + 1`.

Why: the chain step `lem89s_chain_step` with the voters `Hon`, the members `Hon'` and the updaters
`Hon'`: each member of `Hon'` is in `Hon`, and the invariant's third clause at `Hon' ⊆ Hon` puts
every block of `𝓒` on the chain of every confirmation of slot `s'` a member of `Hon'` holds. Then
the lock invariant's step `liveLocksOnFamilyAt_step` at every member of `Hon'`, whose own
confirmation of slot `s'` is in the extended family.

The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s'`: the slot of the step;
- `Hon`: the voters of slot `s'`; `Hon'`: the members of slot `s' + 1`; `𝓒`: the family.

Read aloud: inside the phase, the honest chain grows by the confirmations of slot `s'`, each
slot's members awake and honest only through their own slot's update.



Roots name blocks until `supportCutoff S (s' + 1)`: the proof reads `lem89s_chain_step` at slot
`s'`, whose bound is that time. -/
theorem lem89s_phase_step (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s' : ℕ) (Hon Hon' : Finset V) (𝓒 : Block V → Prop)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s' + 1)))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hGST : GST ≤ voteTime S s')
    -- the voters of slot `s'`: awake and honest from the duty window's start of slot `s'` to
    -- the support cutoff of slot `s' + 1`
    (hHon : ∀ v ∈ Hon, ∀ t : ℕ, dutyWindowStart S s' ≤ t → t ≤ supportCutoff S (s' + 1) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    -- the members of slot `s' + 1`: awake and honest from the duty window's start of slot
    -- `s' + 1` to the support cutoff of slot `s' + 2`
    (hHon' : ∀ v ∈ Hon', ∀ t : ℕ, dutyWindowStart S (s' + 1) ≤ t → t ≤ supportCutoff S (s' + 2) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    -- the members of slot `s' + 1` are voters of slot `s'`
    (hSub : Hon' ⊆ Hon)
    -- the committee majorities of slots `s'` and `s' + 1`
    (hCommittee : (S.P.committee s').card < 2 * (S.P.committee s' ∩ Hon).card)
    (hCommittee' : (S.P.committee (s' + 1)).card < 2 * (S.P.committee (s' + 1) ∩ Hon').card)
    -- the chain invariant at slot `s'` for the family
    (hInv : ChainInvFor S Sched x Hon 𝓒 s')
    -- the lock invariant at slot `s'` at the voters
    (hLocks : ∀ u ∈ Hon, LiveLocksOnFamilyAt S Sched x 𝓒 s' u)
    -- the frame conditions of the step, for every block of the family and every member's
    -- confirmation of slot `s'`
    (hStep : ∀ C : Block V, (𝓒 C ∨ ∃ v ∈ Hon',
        (stateBefore x (supportCutoff S (s' + 1) + 1) v).A.saved_confirmation s' = some C) →
      ∀ w ∈ Hon', StepFrameAt S Sched x C s' w) :
    -- then both invariants at slot `s' + 1` for the extended family
    ChainInvFor S Sched x Hon' (fun C => 𝓒 C ∨ ∃ v ∈ Hon', ∃ C' : Block V,
      (stateBefore x (supportCutoff S (s' + 1) + 1) v).A.saved_confirmation s' = some C' ∧
      C.AncestorEq C') (s' + 1) ∧
    ∀ u ∈ Hon', LiveLocksOnFamilyAt S Sched x (fun C => 𝓒 C ∨ ∃ v ∈ Hon', ∃ C' : Block V,
      (stateBefore x (supportCutoff S (s' + 1) + 1) v).A.saved_confirmation s' = some C' ∧
      C.AncestorEq C') (s' + 1) u :=
  GoldilocksCorrectness.Proofs.Executions.lem89s_phase_step S Sched x GST s' Hon Hon' 𝓒 hDiv hMono
    hSync hCatch hRoots hParent hOwner hGST hHon hHon' hSub hCommittee hCommittee' hInv
    hLocks hStep

/-! ## The re-base -/

/-- **Lemma 89c, the re-base.** In an execution where every time is reached, corruption is
permanent, blocks and Goldfish votes are delivered within `Δ` after `GST` (synchrony from the
receiver's wake, and catch-up on wake), a root names one block among
what honest validators hold, a block reaches a validator only once it holds the parent, and nobody
votes in an honest validator's name: if `GST` is at most the vote time of slot `s`; the members of
`Hon` are awake and honest from the duty window's start of slot `s` to the support cutoff of slot
`s + 1`; the committee of slot `s` has fewer than twice its members in `Hon`; every member's
fork-choice root before the vote time of slot `s` is `R`; and every member's finalized block
before the support cutoff of slot `s + 1` is compatible with `R` — then
`HonestChainExtends S Sched x Hon R s` holds.

Why: every honest vote names a block on the chain of its voter's own root, `R`
(`vote_extends_own_root`); the committee members of `Hon` voting for `R`'s chain reach every
member's pool by the support cutoff of slot `s` (Lemma 12), so Lemma 5 leaves every lock of the
revocation of slot `s + 1` compatible with `R`, unless the member's finalized block is already on
`R`'s chain and every entry descends from it; Lemma 78 puts the confirmations on `R`'s chain.

Why the members' window ends at the support cutoff of slot `s + 1`, and not at the vote time of
slot `s + 1`, one delay earlier: Lemma 78 reads the slot-`s` vote of each committee member of `Hon`
as its only slot-`s` vote in the updater's pool before that cutoff, which needs the member honest at
the cutoff; a member corrupted after the vote time of slot `s + 1` could put a second slot-`s` vote
on the wire before it. The planned caller, the re-base after a switch, reads this lemma at the
validators honest at the support cutoff of slot `s + 1`, who are honest at every earlier time and,
in the phase, awake.

The committee majority of slot `s + 1` and the hypothesis `1 ≤ s` of the plan's statement are not
hypotheses: the proof reads neither.

The statement of record.

The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s`: the slot;
- `Hon`: the members; `R`: the common root.

Read aloud: when every member's fork choice before the vote time of slot `s` is rooted at `R`, no
member's finalized block conflicts with `R`, and the members stay awake and honest through the
update of slot `s`, the honest chain re-forms on `R` in one slot.



Roots name blocks until `supportCutoff S s`: the proof reads Lemma 12 and Lemma 78 at slot `s`,
whose bounds are that time. -/
theorem lem89c_rebase (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s : ℕ) (Hon : Finset V) (R : Block V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S s))
    (hParent : ParentHeldAtDelivery S Sched x) (hOwner : VotesCastByOwner S Sched x)
    (hGST : GST ≤ voteTime S s)
    -- the members: awake and honest from the duty window's start of slot `s` to the support
    -- cutoff of slot `s + 1`
    (hHon : ∀ v ∈ Hon, ∀ t : ℕ, dutyWindowStart S s ≤ t → t ≤ supportCutoff S (s + 1) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    -- the committee majority of slot `s`
    (hCommittee : (S.P.committee s).card < 2 * (S.P.committee s ∩ Hon).card)
    -- every member's fork-choice root before the vote time of slot `s` is `R`
    (hRoot : ∀ w ∈ Hon, get_fc_root (stateBefore x (voteTime S s) w).S = R)
    -- no member's finalized block before the support cutoff of slot `s + 1` conflicts with `R`
    (hF : ∀ v ∈ Hon, (stateBefore x (supportCutoff S (s + 1)) v).S.F.compatible R = true) :
    -- then the slot invariant restricted to `R` at slot `s`
    HonestChainExtends S Sched x Hon R s :=
  GoldilocksCorrectness.Proofs.Executions.lem89c_rebase S Sched x GST s Hon R hDiv hMono hSync
    hCatch hRoots hParent hOwner hGST hHon hCommittee hRoot hF

/-! ## Lemma 45b -/

/-- **Lemma 45b, a lock whose window is after `GST` is extended by the next slot's honest votes,
the held form.** Lemma 45's hypotheses (`lem45_honest_vote_extends_lock_of_post_GST_window`): in
an execution where every time is reached, corruption is permanent, blocks and Goldfish votes are
delivered within `Δ` after `GST` (synchrony from the receiver's wake, and catch-up on wake),
a root names one block among what honest validators hold, and a block reaches
a validator only once it holds the parent: if `GST` is at most the support cutoff of
slot `s + 1 − S.C.k`; `v` is awake and honest from the duty window's start of slot `s + 1` to its
support cutoff, and `w` from that start to its vote time; `v`'s update of slot `s + 1` answers `A'`
with `e` a lock entry of slot `s` it holds; on `w`'s state before the vote time of slot `s + 1`,
the root of `w`'s fork choice is compatible with `e`'s block, and, when that root is `e`'s block or
an ancestor of it, some block of `w`'s voter tree for slot `s + 1` that is `e`'s block or a
descendant of it is a viable head; and `w` put the Goldfish vote `vote` on the wire at its tick at
the vote time of slot `s + 1` — then `vote` is `w`'s slot-`(s + 1)` vote for a block `H_w` of `w`'s
tree before that vote time, and `H_w` is `e`'s block or a descendant of it.

Why: Lemma 45's proof, ending in Lemma 21b, which keeps the walk's end held, in place of Lemma 21.
Lemma 45b is to Lemma 45 what Lemma 26b is to Lemma 26 and Lemma 36b to Lemma 36a.

The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s`: the slot of the lock;
- `v`: the validator whose update of slot `s + 1` adds the lock entry `e`; `A'`: that update's
  answer; `w`: the voter of slot `s + 1`; `vote`: its Goldfish vote.

Read aloud: under Lemma 45's hypotheses, `w`'s vote is its slot-`(s + 1)` vote for a block of its
own tree before that vote time that is the lock's block or a descendant of it.



Roots name blocks until `supportCutoff S (s + 1)`: the proof reads Lemma 42 and Lemma 21b at
slot `s`, and Lemma 31 at a slot `s' < s`, whose bounds are at most that time. -/
theorem lem45b_honest_vote_extends_lock_held (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched)
    (GST s : ℕ) (v w : V) (A' : ACState V) (e : LockEntry V) (vote : GoldfishVote V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s + 1)))
    (hParent : ParentHeldAtDelivery S Sched x)
    -- the network is synchronous from the support cutoff of slot `s + 1 − C.k` on
    (hGST : GST ≤ supportCutoff S (s + 1 - S.C.k))
    -- `v` is awake and honest from the duty window's start of slot `s + 1` to its support cutoff
    (hv : ∀ t : ℕ, dutyWindowStart S (s + 1) ≤ t → t ≤ supportCutoff S (s + 1) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    -- `w` is awake and honest from the duty window's start of slot `s + 1` to its vote time
    (hw : ∀ t : ℕ, dutyWindowStart S (s + 1) ≤ t → t ≤ voteTime S (s + 1) →
      w ∈ Sched.awake (t : Int) ∧ w ∉ Sched.adv (t : Int))
    -- `v`'s update of slot `s + 1` answers `A'`, with `e` the lock entry of slot `s` it adds
    (hUpdate : update_confirmation S.C S.P
        (expireLocks (stateBefore x (supportCutoff S (s + 1)) v).A
          ((supportCutoff S (s + 1) : ℕ) : Int))
        (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S)
        ((supportCutoff S (s + 1) : ℕ) : Int) (s + 1) = .ok A')
    (he : e ∈ A'.lock_entries)
    (hd : e.d = S.C.t_ (s + S.C.k) + 5 * S.C.Δ)
    -- the finality-gadget conditions at `w`, relative to the lock block (as Lemma 21's)
    (hF2 : (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).fc_root.compatible e.B = true)
    (hF3 : (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).fc_root.AncestorEq e.B →
      ∀ tree : Finset (Block V),
        voter_block_tree S.C (stateBefore x (voteTime S (s + 1)) w).A
          (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S) (s + 1) = .ok tree →
        ∃ W ∈ tree, W ∈ (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).viable_heads ∧
          e.B.AncestorEq W)
    -- `w` put `vote` on the wire at its tick at the vote time of slot `s + 1`
    (hSend : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (voteTime S (s + 1)) ∧
      (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent) :
    -- then `vote` is `w`'s vote for a block it holds on the lock block's chain
    ∃ H_w ∈ (stateBefore x (voteTime S (s + 1)) w).S.T,
      vote = GoldfishVote.mk w (s + 1) H_w.root ∧ e.B.AncestorEq H_w :=
  GoldilocksCorrectness.Proofs.Executions.lem45b_honest_vote_extends_lock_held S Sched x GST s v w
    A' e vote hDiv hMono hSync hCatch hRoots hParent hGST hv hw hUpdate he hd hF2 hF3 hSend

end GoldilocksCorrectness.Statements.Executions
