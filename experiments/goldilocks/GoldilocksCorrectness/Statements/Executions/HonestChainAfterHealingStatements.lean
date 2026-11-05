module
public import GoldilocksCorrectness.Proofs.Executions.Lemma81

@[expose] public section

/-!
# The honest chain after the healed slot

The audited statements, proved in `GoldilocksCorrectness/Proofs/Executions/Lemma81.lean`:

- Lemma 36b, `lem36b_confirmed_block_extended_held`, Lemma 36a's conclusion in the held form of
  `HonestChainExtends`'s first clause;
- the chain step `lem89s_chain_step`, shared with Lemma 89: the chain
  invariant at slot `s'` for a family of blocks gives the invariant at slot `s' + 1` for the family
  extended by the confirmations of slot `s'`;
- the step of the lock invariant at one member, `liveLocksOnFamilyAt_step`;
- Lemma 81b, `lem81b_chain_step`, the chain step's instance after the healed slot;
- Lemma 81, `lem81_confirmations_chain`, the honest confirmations form a chain from the healed
  slot;
- `onHonestChain_compatible`, two blocks on the honest chain are compatible.

The definitions they read are in `HonestChainAfterHealingDefs.lean` (`StepFrameAt`, `ChainInvFor`,
`LiveLocksOnFamilyAt`, `VoterFrameOnChainAt`, `UpdaterFinalizedOnChainAt`) and in `SleepyDefs.lean`.


-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff viewFreeze
  dutyWindowStart)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Routines (expireLocks)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-! ## Lemma 36b -/

/-- **Lemma 36b, a confirmed block is extended by the next slot's honest votes, the held form.**
Lemma 36a's hypotheses (`EligibleBlockVoteStatements.lean`): in an execution where every time is
reached, corruption is permanent, blocks and Goldfish votes are delivered within `Δ` after `GST`
(synchrony from the receiver's wake, and catch-up on wake), a root
names one block among what honest validators hold, and a block reaches a validator only once it
holds the parent: if `GST` is at most the support cutoff of slot `s`; `v` is awake and honest at
every time from the vote time of slot `s + 1` to the support cutoff of slot `s + 1`; `w` is awake
and honest at every time from the support cutoff of slot `s` to the view freeze of slot `s`; `v`'s
confirmation update of slot `s + 1`, on its state before the support cutoff of slot `s + 1` with
the expired lock entries removed, answers `A'`, which saves `C'` as the confirmation of slot `s`;
on `w`'s state before the vote time of slot `s + 1`, the root of `w`'s fork choice is compatible
with `C'`, and, when that root is `C'`
or an ancestor of `C'`, some block of `w`'s voter tree for slot `s + 1` that is `C'` or a
descendant of `C'` is a viable head; the block of every lock entry live at the vote time of slot
`s + 1` that `w`'s revocation of slot `s + 1` leaves is compatible with `C'`; and `w` put the
Goldfish vote `vote` on the wire at its tick at the vote time of slot `s + 1` — then `vote` is
`w`'s slot-`(s + 1)` vote for a block `H_w` of `w`'s tree before that vote time, and `H_w` is `C'`
or a descendant of `C'`.

Why: Lemma 36a's proof, with Lemma 21 in the held form (the vote's validator and slot from Lemma
14, the walk's end in `w`'s tree as Lemma 26b's proof shows). Lemma 36a concludes only that the
vote's head is the root of some block on `C'`'s chain; the first clause of `HonestChainExtends`
needs the block held. Lemma 36b is to Lemma 36a what Lemma 26b is to Lemma 26.




The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s`: the slot whose confirmation `v`'s
  update of slot `s + 1` saves;
- `C'`: the saved confirmation; `v`: the validator whose update saves it; `A'`: that update's
  answer;
- `w`: the voter of slot `s + 1`; `vote`: the Goldfish vote `w` sent at the vote time of slot
  `s + 1`.

Read aloud: under Lemma 36a's hypotheses, `w`'s vote is its slot-`(s + 1)` vote for a block of its
own tree before that vote time that is `C'` or a descendant of `C'`.

Roots name blocks until `supportCutoff S (s + 1)`: Lemma 21b, which the proof calls, takes
blocks as held up to one delay after `w`'s vote time of slot `s + 1`. -/
theorem lem36b_confirmed_block_extended_held (S : Setup V) (Sched : Schedule V)
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
    -- the root of `w`'s fork choice is compatible with `C'`
    (hF2 : (fg_to_ac (stateBefore x (voteTime S (s + 1)) w).S).fc_root.compatible C' = true)
    -- when that root is `C'` or an ancestor of `C'`, a block of `w`'s voter tree on `C'`'s chain
    -- is a viable head
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
    -- then `vote` is `w`'s vote for a block it holds on `C'`'s chain
    ∃ H_w ∈ (stateBefore x (voteTime S (s + 1)) w).S.T,
      vote = GoldfishVote.mk w (s + 1) H_w.root ∧ C'.AncestorEq H_w :=
  GoldilocksCorrectness.Proofs.Executions.lem36b_confirmed_block_extended_held S Sched x GST s C'
    v w A' vote hDiv hMono hSync hCatch hRoots hParent hGST hv hw hUpdate hSaved hF2 hF3
    hLocks hSend

/-! ## The chain step -/

/-- **The chain step.** In an execution where every time is reached,
corruption is permanent, blocks and Goldfish votes are delivered within `Δ` after `GST` (synchrony
from the receiver's wake, and catch-up on wake), a root names one block
among what honest validators hold, a block reaches a validator only once it holds the parent, and
nobody votes in an honest validator's name. Take three sets: `Hon`, honest active validators of
slot `s'` (the voters of slot `s'`, at which the invariant is read); `Hon'`, honest active
validators of slot `s' + 1` (the members at slot `s' + 1`); and `Upd`, updaters of slot `s'` (whose
confirmations of slot `s'` join the family), with every member of `Hon'` in `Upd`. Suppose: `GST`
is at most the vote time of slot `s'`; the committee of slot `s'` has fewer than twice the members
it shares with `Hon`, and the committee of slot `s' + 1` fewer than twice those it shares with
`Hon'`; `ChainInvFor S Sched x Hon 𝓒 s'` holds; every member of `Hon'` is in `Hon` or holds no
lock entry live at the vote time of slot `s' + 1` on its state before that time; every member of
`Hon` satisfies `LiveLocksOnFamilyAt S Sched x 𝓒 s'`; every block of `𝓒` is `C'` or an ancestor of
`C'` for every confirmation `C'` of slot `s'` a member of `Upd` holds right after the support
cutoff of slot `s' + 1`; and `StepFrameAt S Sched x C s' w` holds at every member `w` of `Hon'` for
every block `C` of `𝓒` and every such confirmation `C`. Then
`ChainInvFor` holds at slot `s' + 1`, read at `Hon'`, for the family of the blocks of `𝓒` and the
blocks that are a confirmation of slot `s'` of a member of `Upd` or an ancestor of one.

Why: for a block of `𝓒`, the first clause is Lemma 26b with the votes of `S.P.committee s' ∩ Hon`
(the first clause at slot `s'`), the second clause comes from where a live lock comes from
(`revoked_lock_source`: the member's own confirmation of slot `s'`, which extends the block, or a
lock left by its revocation of slot `s' + 1`, compatible by the second clause at slot `s'`), and
the third is Lemma 78 with the votes of `S.P.committee (s' + 1) ∩ Hon'` (the first clause just
proved). For a new confirmation `C'`, the first clause is Lemma 36b at `C'`, whose lock condition
is the lock invariant (each live lock is on the chain of a block of `𝓒`, an ancestor of `C'`); the
second clause uses Lemma 32 (two updaters' confirmations of slot `s'` are compatible) and the lock
invariant; the third is Lemma 78 again. An ancestor of a new confirmation inherits the three clauses from it
(`honestChainExtends_of_ancestorEq`). A member of `Hon'` outside `Hon` holds no live lock, so its
revocation of slot `s' + 1` leaves none (Lemma 38). `probe_lem89_1.lean`'s `hs1 : 1 ≤ s'` is not used and is
not a hypothesis.

The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s'`: the slot of the step;
- `Hon`: the voters of slot `s'`; `Hon'`: the members at slot `s' + 1`; `Upd`: the updaters whose
  confirmations of slot `s'` join the family; `𝓒`: the family of blocks.

Read aloud: the honest chain grows by the confirmations of slot `s'`: when the voters of slot `s'`
satisfy the invariant for every block of the family and their live locks are on its chain, the
members of slot `s' + 1` satisfy it for every block of the family and every block of a new
confirmation's chain.

Roots name blocks until `supportCutoff S (s' + 1)`: Lemmas 36b, 32 and 78, which the proof calls
at the slots `s'` and `s' + 1`, take blocks as held up to the support cutoff of slot `s' + 1`;
Lemma 26b reads earlier. -/
theorem lem89s_chain_step (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s' : ℕ) (Hon Hon' Upd : Finset V)
    (𝓒 : Block V → Prop)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s' + 1)))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    (hGST : GST ≤ voteTime S s')
    -- the voters of slot `s'` are honest active validators of slot `s'`
    (hHon : Hon ⊆ honestActiveAt S Sched s')
    -- the members at slot `s' + 1` are honest active validators of slot `s' + 1`
    (hHon' : Hon' ⊆ honestActiveAt S Sched (s' + 1))
    -- the updaters are updaters of slot `s'`
    (hUpd : Upd ⊆ updaterAt S Sched s')
    -- every member at slot `s' + 1` is one of the updaters
    (hHonUpd : Hon' ⊆ Upd)
    -- the committee majorities at slots `s'` and `s' + 1`
    (hCommittee : |S.P.committee s'| < 2 * |S.P.committee s' ∩ Hon|)
    (hCommittee' : |S.P.committee (s' + 1)| < 2 * |S.P.committee (s' + 1) ∩ Hon'|)
    -- the chain invariant at slot `s'` for the family
    (hInv : ChainInvFor S Sched x Hon 𝓒 s')
    -- a member at slot `s' + 1` outside `Hon` holds no live lock at the vote time of slot `s' + 1`
    (hNew : ∀ u ∈ Hon', u ∈ Hon ∨
      ∀ e ∈ (stateBefore x (voteTime S (s' + 1)) u).A.lock_entries,
        is_live (fg_to_ac (stateBefore x (voteTime S (s' + 1)) u).S)
          ((voteTime S (s' + 1) : ℕ) : Int) e = false)
    -- the lock invariant at slot `s'` at the voters
    (hLocks : ∀ u ∈ Hon, LiveLocksOnFamilyAt S Sched x 𝓒 s' u)
    -- every block of the family is on the chain of every updater's confirmation of slot `s'`
    (hConfExt : ∀ C : Block V, 𝓒 C → ∀ v ∈ Upd, ∀ C' : Block V,
      (stateBefore x (supportCutoff S (s' + 1) + 1) v).A.saved_confirmation s' = some C' →
      C.AncestorEq C')
    -- the frame conditions of the step, for every block of the family and every updater's
    -- confirmation of slot `s'`
    (hStep : ∀ C : Block V, (𝓒 C ∨ ∃ v ∈ Upd,
        (stateBefore x (supportCutoff S (s' + 1) + 1) v).A.saved_confirmation s' = some C) →
      ∀ w ∈ Hon', StepFrameAt S Sched x C s' w) :
    -- then the chain invariant at slot `s' + 1` for the extended family
    ChainInvFor S Sched x Hon' (fun C => 𝓒 C ∨ ∃ v ∈ Upd, ∃ C' : Block V,
      (stateBefore x (supportCutoff S (s' + 1) + 1) v).A.saved_confirmation s' = some C' ∧
      C.AncestorEq C') (s' + 1) :=
  GoldilocksCorrectness.Proofs.Executions.lem89s_chain_step S Sched x GST s' Hon Hon' Upd 𝓒 hDiv
    hMono hSync hCatch hRoots hParent hOwner hGST hHon hHon' hUpd hHonUpd hCommittee
    hCommittee' hInv hNew hLocks hConfExt hStep

/-- **The step of the lock invariant, at one member.** In an execution where every
time is reached: when `u` is awake and honest at every time from the
duty window's start of slot `s' + 2` to the vote time of slot `s' + 2`, every block of `𝓒` is a
block of `𝓒'`, `u`'s saved confirmation of slot `s'` right after the support cutoff of slot
`s' + 1` is a block of `𝓒'`, and `LiveLocksOnFamilyAt S Sched x 𝓒 s' u` holds — then
`LiveLocksOnFamilyAt S Sched x 𝓒' (s' + 1) u` holds.

Why: a lock entry `u`'s revocation of slot `s' + 2` leaves live is on an ancestor of a block of an
entry of `u`'s state then (Lemma 38). That entry was added by `u`'s update of slot `s' + 1`, on its
saved confirmation of slot `s'` or an ancestor of it, or by an earlier update, and then an entry
for it survived the revocation of slot `s' + 1` live, on a descendant of its block (Lemmas 39, 41
and 13, as in `live_locks_compatible_of_honestChainExtends`); the invariant at slot `s'` puts that
one on the chain of a block of `𝓒`.


The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `𝓒`, `𝓒'`: the families before and after the step; `s'`: the slot; `u`: the validator.

Read aloud: if `u` stays awake and honest through the next slot's vote, and its new confirmation
joins the family, its live locks stay on the chain of the family. -/
theorem liveLocksOnFamilyAt_step (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (𝓒 𝓒' : Block V → Prop) (s' : ℕ) (u : V)
    -- every time is reached
    (hDiv : TimeDiverges x.toTrace)
    -- `u` is awake and honest from the duty window's start of slot `s' + 2` to the vote time of
    -- slot `s' + 2`
    (hHon : ∀ t : ℕ, dutyWindowStart S (s' + 2) ≤ t → t ≤ voteTime S (s' + 2) →
      u ∈ Sched.awake (t : Int) ∧ u ∉ Sched.adv (t : Int))
    -- the family grows
    (hSub : ∀ C : Block V, 𝓒 C → 𝓒' C)
    -- `u`'s confirmation of slot `s'` joins the family
    (hOwn : ∀ C : Block V,
      (stateBefore x (supportCutoff S (s' + 1) + 1) u).A.saved_confirmation s' = some C → 𝓒' C)
    -- the lock invariant at slot `s'`
    (hPrev : LiveLocksOnFamilyAt S Sched x 𝓒 s' u) :
    -- then the lock invariant at slot `s' + 1`
    LiveLocksOnFamilyAt S Sched x 𝓒' (s' + 1) u :=
  GoldilocksCorrectness.Proofs.Executions.liveLocksOnFamilyAt_step S Sched x 𝓒 𝓒' s' u hDiv
    hHon hSub hOwn hPrev

/-! ## Lemma 81b and Lemma 81 -/

/-- **Lemma 81b, the chain step after the healed slot.** In an execution where every time is
reached, corruption is permanent, blocks and Goldfish votes are delivered within `Δ` after `GST`
(synchrony from the receiver's wake, and catch-up on wake), a root
names one block among what honest validators hold, a block reaches a validator only once it holds
the parent, and nobody votes in an honest validator's name: if `GST` is at most the vote time of
slot `s`; `s₀ ≤ s`; committee sleepiness holds from `anchor`, and slot `s + 1` starts at or after
`anchor`; at slot `s`, `HonestChainExtends` holds at the honest active validators of slot `s` for
every block on the honest chain of the slots before `s` (`Inv s`); every honest active validator
of slot `s` satisfies the lock invariant for that chain; every honest active validator of slot
`s + 1` satisfies `VoterFrameOnChainAt S Sched x s₀ (s + 1)` and
`UpdaterFinalizedOnChainAt S Sched x s₀ (s + 1)`; and every updater of slot `s` satisfies
`UpdaterFinalizedOnChainAt S Sched x s₀ s` — then `HonestChainExtends` holds at slot `s + 1` at
the honest active validators of slot `s + 1` for every block on the honest chain of the slots
before `s + 1` (`Inv (s + 1)`).

Why: the chain step `lem89s_chain_step` with `Hon := honestActiveAt S Sched s`,
`Hon' := honestActiveAt S Sched (s + 1)`, `Upd := updaterAt S Sched s` and the family the chain of
the slots before `s`. The committee majorities come from committee sleepiness (Lemma 88); a member
of slot `s + 1` outside `honestActiveAt S Sched s` slept in the window before the duty window of
slot `s + 1` (`mem_honestActiveAt_or_slept`) and holds no live lock (`lock_free_after_wake`); every
chain block before `s` is an ancestor of every updater's confirmation of slot `s` by Lemma 78 at
the updater, its voters the honest active committee members of slot `s`; the frame conditions of
the step are the two frame definitions at slot `s + 1`. The chain before `s + 1` is the chain
before `s` and the updaters' confirmations of slot `s` with their ancestors. The brief's `hs₀ : s₀ < s`, `GST ≤ voteTime S s₀`
and `anchor ≤ slotStart S s₀` are replaced by what the proof reads: `s₀ ≤ s`, `GST ≤ voteTime S
s` and `anchor ≤ slotStart S (s + 1)`; the frame condition at slot `s + 1`'s updaters is read at
the honest active validators of slot `s + 1` only.

The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s₀`: the first slot of the chain;
  `s`: the slot of the step; `anchor`: the time from which committee sleepiness holds.

Read aloud: `Inv s` and the lock invariant at slot `s` give `Inv (s + 1)`.

Roots name blocks until `supportCutoff S (s + 1)`: the chain step, which the proof calls at slot
`s`, takes blocks as held up to the support cutoff of slot `s + 1`. -/
theorem lem81b_chain_step (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ s anchor : ℕ)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s + 1)))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    (hGST : GST ≤ voteTime S s)
    -- the step is at or after the first slot of the chain
    (hs₀ : s₀ ≤ s)
    -- committee sleepiness from `anchor`, and slot `s + 1` starts at or after `anchor`
    (hSleepK : CommitteeSleepiness S Sched anchor)
    (hAnchor : anchor ≤ slotStart S (s + 1))
    -- `Inv s`
    (hInv : ChainInvFor S Sched x (honestActiveAt S Sched s) (OnHonestChainBefore S Sched x s₀ s) s)
    -- the lock invariant at slot `s`
    (hLocks : ∀ u ∈ honestActiveAt S Sched s,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ s) s u)
    -- the frame conditions at slot `s + 1`'s members
    (hVoterFrame : ∀ w ∈ honestActiveAt S Sched (s + 1),
      VoterFrameOnChainAt S Sched x s₀ (s + 1) w)
    -- the frame condition at slot `s`'s updaters
    (hUpdaterFrame : ∀ v ∈ updaterAt S Sched s, UpdaterFinalizedOnChainAt S Sched x s₀ s v)
    (hUpdaterFrame' : ∀ w ∈ honestActiveAt S Sched (s + 1),
      UpdaterFinalizedOnChainAt S Sched x s₀ (s + 1) w) :
    -- then `Inv (s + 1)`
    ChainInvFor S Sched x (honestActiveAt S Sched (s + 1))
      (OnHonestChainBefore S Sched x s₀ (s + 1)) (s + 1) :=
  GoldilocksCorrectness.Proofs.Executions.lem81b_chain_step S Sched x GST s₀ s anchor hDiv hMono
    hSync hCatch hRoots hParent hOwner hGST hs₀ hSleepK hAnchor hInv hLocks hVoterFrame
    hUpdaterFrame hUpdaterFrame'

/-- **Lemma 81, the honest confirmations form a chain from the healed slot.** In an execution
where every time is reached, corruption is permanent, blocks and Goldfish votes are delivered
within `Δ` after `GST` (synchrony from the receiver's wake, and catch-up on wake),
a root names one block among what honest validators hold, a block reaches a
validator only once it holds the parent, and nobody votes in an honest validator's name: if `GST`
is at most the vote time of slot `s₀`; committee sleepiness holds from `anchor`, and slot `s₀ + 1`
starts at or after `anchor`; `B₀`'s slot is at least `s₀`; `HonestChainExtends` holds for `B₀` at
slot `s₀` at the honest active validators of slot `s₀`; every updater of slot `s₀` holds `B₀` as
its confirmation of slot `s₀` right after the support cutoff of slot `s₀ + 1`; and at every slot
`s > s₀`, every honest active validator of slot `s` satisfies `VoterFrameOnChainAt S Sched x s₀ s`
and every updater of slot `s` satisfies `UpdaterFinalizedOnChainAt S Sched x s₀ s` — then
`ConfirmationsChain S Sched x s₀` holds.

Why: by induction on `s > s₀`, `Inv s` and the lock invariant at slot `s` for the chain before
`s`. At `s₀ + 1`, the chain step at slot `s₀` with the family of `B₀` and its ancestors (the
invariant restricted to an ancestor follows from the one for `B₀`,
`honestChainExtends_of_ancestorEq`; the lock invariant at slot `s₀` from `B₀`'s slot,
`liveLocksOnFamilyAt_base`); after it, Lemma 81b and `liveLocksOnFamilyAt_step`. Then two
confirmations of slots `s < s'` are ordered by Lemma 78 at the later updater under `Inv s'`, and
two of one slot are compatible by Lemma 32. `hB₀slot` is read only at the base of the lock
induction. The
brief's `anchor ≤ slotStart S s₀` is replaced by what the proof reads, `anchor ≤ slotStart S
(s₀ + 1)`.

The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s₀`: the healed slot; `anchor`: the
  time from which committee sleepiness holds; `B₀`: the block every updater of slot `s₀` saved.

Read aloud: from the healed slot, where every updater saved `B₀` and the slot invariant restricted
to `B₀` holds for the honest active validators, under committee sleepiness and the frame
conditions relative to the chain so far at every later slot, the honest confirmations form a
chain. -/
theorem lem81_confirmations_chain (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ anchor : ℕ) (B₀ : Block V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocks S Sched x)
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    (hGST : GST ≤ voteTime S s₀)
    -- committee sleepiness from `anchor`, and slot `s₀ + 1` starts at or after `anchor`
    (hSleepK : CommitteeSleepiness S Sched anchor)
    (hAnchor : anchor ≤ slotStart S (s₀ + 1))
    -- `B₀`'s slot is at least `s₀`
    (hB₀slot : s₀ ≤ B₀.slot)
    -- the slot invariant restricted to `B₀` at slot `s₀`
    (hBase : HonestChainExtends S Sched x (honestActiveAt S Sched s₀) B₀ s₀)
    -- every updater of slot `s₀` saved `B₀`
    (hBaseSaved : ∀ v ∈ updaterAt S Sched s₀,
      (stateBefore x (supportCutoff S (s₀ + 1) + 1) v).A.saved_confirmation s₀ = some B₀)
    -- the frame conditions relative to the chain so far at every later slot
    (hVoterFrame : ∀ s : ℕ, s₀ < s → ∀ w ∈ honestActiveAt S Sched s,
      VoterFrameOnChainAt S Sched x s₀ s w)
    (hUpdaterFrame : ∀ s : ℕ, s₀ < s → ∀ v ∈ updaterAt S Sched s,
      UpdaterFinalizedOnChainAt S Sched x s₀ s v) :
    -- then the honest confirmations form a chain from slot `s₀`
    ConfirmationsChain S Sched x s₀ :=
  GoldilocksCorrectness.Proofs.Executions.lem81_confirmations_chain S Sched x GST s₀ anchor B₀ hDiv
    hMono hSync hCatch hRoots hParent hOwner hGST hSleepK hAnchor hB₀slot hBase hBaseSaved
    hVoterFrame hUpdaterFrame

/-- **Two blocks on the honest chain are compatible.** When the honest confirmations form a chain
from slot `s₀`, two blocks on the honest chain from slot `s₀` are compatible.

Why: each is an ancestor of, or equal to, an updater's confirmation; of two such confirmations the
one of the earlier slot is an ancestor of the other, and two of one slot are compatible; ancestors
of two compatible blocks are compatible.

The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution; `s₀`: the first slot of the chain;
- `B`, `B'`: the two blocks.

Read aloud: two blocks on the honest chain are on one chain. -/
theorem onHonestChain_compatible (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ : ℕ) (B B' : Block V)
    -- the honest confirmations form a chain from slot `s₀`
    (hChain : ConfirmationsChain S Sched x s₀)
    -- both blocks are on the honest chain
    (hB : OnHonestChain S Sched x s₀ B) (hB' : OnHonestChain S Sched x s₀ B') :
    B.compatible B' = true :=
  GoldilocksCorrectness.Proofs.Executions.onHonestChain_compatible S Sched x s₀ B B' hChain hB hB'

/-- **Lemma 81's induction before a slot.** In an execution where every time is reached,
corruption is permanent, blocks and Goldfish votes are delivered within `Δ` after `GST`
(synchrony from the receiver's wake, and catch-up on wake), a root
names one block among what honest validators hold by the support cutoff of slot `n − 1`, a block
reaches a validator only once it holds the parent, and nobody votes in an honest validator's name:
if `GST` is at most the vote time of slot `s₀`; committee sleepiness holds from `anchor`, and slot
`s₀ + 1` starts at or after `anchor`; `B₀`'s slot is at least `s₀`; `HonestChainExtends` holds for
`B₀` at slot `s₀` at the honest active validators of slot `s₀`; every updater of slot `s₀` holds
`B₀` as its confirmation of slot `s₀` right after the support cutoff of slot `s₀ + 1`; and at every
slot `s` with `s₀ < s < n`, every honest active validator of slot `s` satisfies
`VoterFrameOnChainAt S Sched x s₀ s` and every updater of slot `s` satisfies
`UpdaterFinalizedOnChainAt S Sched x s₀ s` — then at every slot `s` with `s₀ < s < n` the chain
invariant `ChainInvFor` holds at the honest active validators of slot `s` for the chain before `s`,
and every honest active validator of slot `s` satisfies the lock invariant `LiveLocksOnFamilyAt`
for the chain before `s`.

Why: the induction of `lem81_inv`, stopped before `n`: at `s₀ + 1` the chain step at slot `s₀`
with the family of `B₀` and its ancestors; after it, Lemma 81b and `liveLocksOnFamilyAt_step`.
The conclusion at a slot `s` reads the chain step at slot `s − 1`, which takes blocks as held up to
the support cutoff of slot `s`, at most that of slot `n − 1`.

The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s₀`: the healed slot; `anchor`: the
  time from which committee sleepiness holds; `n`: the bound on the slots; `B₀`: the block every
  updater of slot `s₀` saved.

Read aloud: from the healed slot on and before slot `n`, every honest vote, live lock and
confirmation extends the chain so far, provided roots name blocks up to the support cutoff of slot
`n − 1` and `VoterFrameOnChainAt`, `UpdaterFinalizedOnChainAt` hold at the slots before `n`.

 `lem81_inv` is its instance at `n := s + 1`. -/
theorem lem81_inv_before (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ anchor n : ℕ) (B₀ : Block V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    -- a root names one block among what honest validators hold by the support cutoff of slot
    -- `n − 1`
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (n - 1)))
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    (hGST : GST ≤ voteTime S s₀)
    -- committee sleepiness from `anchor`, and slot `s₀ + 1` starts at or after `anchor`
    (hSleepK : CommitteeSleepiness S Sched anchor)
    (hAnchor : anchor ≤ slotStart S (s₀ + 1))
    -- `B₀`'s slot is at least `s₀`
    (hB₀slot : s₀ ≤ B₀.slot)
    -- the slot invariant restricted to `B₀` at slot `s₀`
    (hBase : HonestChainExtends S Sched x (honestActiveAt S Sched s₀) B₀ s₀)
    -- every updater of slot `s₀` saved `B₀`
    (hBaseSaved : ∀ v ∈ updaterAt S Sched s₀,
      (stateBefore x (supportCutoff S (s₀ + 1) + 1) v).A.saved_confirmation s₀ = some B₀)
    -- `VoterFrameOnChainAt` and `UpdaterFinalizedOnChainAt` at every slot after `s₀` and before
    -- `n`
    (hVoterFrame : ∀ s : ℕ, s₀ < s → s < n → ∀ w ∈ honestActiveAt S Sched s,
      VoterFrameOnChainAt S Sched x s₀ s w)
    (hUpdaterFrame : ∀ s : ℕ, s₀ < s → s < n → ∀ v ∈ updaterAt S Sched s,
      UpdaterFinalizedOnChainAt S Sched x s₀ s v) :
    -- then the chain invariant and the lock invariant hold at every slot after `s₀` and before `n`
    ∀ s : ℕ, s₀ < s → s < n →
      ChainInvFor S Sched x (honestActiveAt S Sched s) (OnHonestChainBefore S Sched x s₀ s) s ∧
      ∀ u ∈ honestActiveAt S Sched s,
        LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ s) s u :=
  GoldilocksCorrectness.Proofs.Executions.lem81_inv_before S Sched x GST s₀ anchor n B₀ hDiv hMono
    hSync hCatch hRoots hParent hOwner hGST hSleepK hAnchor hB₀slot hBase hBaseSaved
    hVoterFrame hUpdaterFrame

/-- **Lemma 81's induction.** Under Lemma 81's hypotheses (`lem81_confirmations_chain`): in an
execution where every time is reached, corruption is permanent, blocks and Goldfish votes are
delivered within `Δ` after `GST` (synchrony from the receiver's wake, and catch-up on wake),
a root names one block among what honest validators hold, a block reaches a
validator only once it holds the parent, and nobody votes in an honest validator's name: if `GST`
is at most the vote time of slot `s₀`; committee sleepiness holds from `anchor`, and slot `s₀ + 1`
starts at or after `anchor`; `B₀`'s slot is at least `s₀`; `HonestChainExtends` holds for `B₀` at
slot `s₀` at the honest active validators of slot `s₀`; every updater of slot `s₀` holds `B₀` as
its confirmation of slot `s₀` right after the support cutoff of slot `s₀ + 1`; and at every slot
`s > s₀`, every honest active validator of slot `s` satisfies `VoterFrameOnChainAt S Sched x s₀ s`
and every updater of slot `s` satisfies `UpdaterFinalizedOnChainAt S Sched x s₀ s` — then at every
slot `s > s₀` the chain invariant `ChainInvFor` holds at the honest active validators of slot `s`
for the chain before `s`, and every honest active validator of slot `s` satisfies the lock
invariant `LiveLocksOnFamilyAt` for the chain before `s`.

Why: the induction on `s > s₀` of Lemma 81's proof, exported: at `s₀ + 1` the chain step at slot
`s₀` with the family of `B₀` and its ancestors; after it, Lemma 81b and
`liveLocksOnFamilyAt_step`.

The variables:
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s₀`: the healed slot; `anchor`: the
  time from which committee sleepiness holds; `B₀`: the block every updater of slot `s₀` saved.

Read aloud: from the healed slot on, every honest vote, live lock and confirmation extends the
chain so far.

 -/
theorem lem81_inv (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ anchor : ℕ) (B₀ : Block V)
    (hDiv : TimeDiverges x.toTrace)
    (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocks S Sched x)
    (hParent : ParentHeldAtDelivery S Sched x)
    (hOwner : VotesCastByOwner S Sched x)
    (hGST : GST ≤ voteTime S s₀)
    -- committee sleepiness from `anchor`, and slot `s₀ + 1` starts at or after `anchor`
    (hSleepK : CommitteeSleepiness S Sched anchor)
    (hAnchor : anchor ≤ slotStart S (s₀ + 1))
    -- `B₀`'s slot is at least `s₀`
    (hB₀slot : s₀ ≤ B₀.slot)
    -- the slot invariant restricted to `B₀` at slot `s₀`
    (hBase : HonestChainExtends S Sched x (honestActiveAt S Sched s₀) B₀ s₀)
    -- every updater of slot `s₀` saved `B₀`
    (hBaseSaved : ∀ v ∈ updaterAt S Sched s₀,
      (stateBefore x (supportCutoff S (s₀ + 1) + 1) v).A.saved_confirmation s₀ = some B₀)
    -- the frame conditions relative to the chain so far at every later slot
    (hVoterFrame : ∀ s : ℕ, s₀ < s → ∀ w ∈ honestActiveAt S Sched s,
      VoterFrameOnChainAt S Sched x s₀ s w)
    (hUpdaterFrame : ∀ s : ℕ, s₀ < s → ∀ v ∈ updaterAt S Sched s,
      UpdaterFinalizedOnChainAt S Sched x s₀ s v) :
    -- then the chain invariant and the lock invariant hold at every slot after `s₀`
    ∀ s : ℕ, s₀ < s →
      ChainInvFor S Sched x (honestActiveAt S Sched s) (OnHonestChainBefore S Sched x s₀ s) s ∧
      ∀ u ∈ honestActiveAt S Sched s,
        LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ s) s u :=
  GoldilocksCorrectness.Proofs.Executions.lem81_inv S Sched x GST s₀ anchor B₀ hDiv hMono hSync
    hCatch hRoots hParent hOwner hGST hSleepK hAnchor hB₀slot hBase hBaseSaved hVoterFrame
    hUpdaterFrame

end GoldilocksCorrectness.Statements.Executions
