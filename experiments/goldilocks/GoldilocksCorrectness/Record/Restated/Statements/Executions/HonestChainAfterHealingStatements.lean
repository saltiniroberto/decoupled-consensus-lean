module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma81
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# HonestChainAfterHealingStatements, over a model

The statements of
`GoldilocksCorrectness/Statements/Executions/HonestChainAfterHealingStatements.lean`, over a model
`M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: Lemma 81, after the healed round
the honest confirmations stay on the honest chain, with its chain step, its lock invariant's step,
Lemma 81 (b) and the slot invariant it carries from slot to slot. Each is the theorem of the same
name of `Record/Restated/Proofs/Executions/Lemma81.lean`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff viewFreeze
  dutyWindowStart)

namespace GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor ConfirmationUpdated CountedVotes
  CountedVotesAt EarlySupporterOf LocksRevoked TreeClosed VoterTree VoterTreeAt)
open GoldilocksCorrectness.Statements.Executions (acObject)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Statements.Routines (expireLocks)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-! ## Lemma 36b -/

/-- **Lemma 36b, a confirmed block is extended by the next slot's honest votes, the held form.**
Lemma 36a's hypotheses (`EligibleBlockVoteStatements.lean`): in an execution where every time is
reached, corruption is permanent, blocks and Goldfish votes are delivered within `Δ` after `GST`
(synchrony from the receiver's wake, and catch-up on wake), a root
names one block among what honest validators hold, and a block reaches a validator only once it
holds the parent: if `GST` is at most the support cutoff of slot `s`; `v` is awake and honest from
the duty window's start of slot `s + 1` up to its tick to the support cutoff of slot `s + 1`; `w` is active from a time `tStartW`, more than `ΔClockAhead + ΔClockBehind` before the view freeze of slot `s` less `max (3 * Δ S) Δs`, up to its tick to that view freeze; `v`'s
confirmation update of slot `s + 1`, on its state before the support cutoff of slot `s + 1` with
the expired lock entries removed, leaves `n'` (`ConfirmationUpdated`), which saves `C'` as the
confirmation of slot `s`;
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
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s`: the slot whose confirmation `v`'s
  update of slot `s + 1` saves;
- `C'`: the saved confirmation; `v`: the validator whose update saves it; `n'`: the node state that
  update leaves;
- `w`: the voter of slot `s + 1`; `tStartW`: the start of `w`'s window; `vote`: the Goldfish vote `w` sent at the vote time of slot
  `s + 1`.

Read aloud: under Lemma 36a's hypotheses, `w`'s vote is its slot-`(s + 1)` vote for a block of its
own tree before that vote time that is `C'` or a descendant of `C'`.

Roots name blocks until `M.supportCutoff S.C (s + 1)`: Lemma 21b, which the proof calls, takes
blocks as held up to one delay after `w`'s vote time of slot `s + 1`. -/
theorem lem36b_confirmed_block_extended_held (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s : ℕ) (C' : Block V) (v w : V) (n' : M.N)
    (vote : GoldfishVote V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C (s + 1)))
    (hParent : ParentHeldAtDelivery M x)
    (hGST : GST + max (Δ S) Δs ≤ M.viewFreeze S.C s)
    -- `v`, awake and honest from the duty window's start of slot `s + 1` up to its tick to that
    -- slot's support cutoff
    (hv : v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.supportCutoff S.C (s + 1)))
    (tStartW : ℤ) (htStartW :
      (tStartW : ℝ) + ΔClockAhead + ΔClockBehind < ((M.viewFreeze S.C s - max (3 * Δ S) Δs : ℕ) : ℝ))
    -- `w` is active from `tStartW` up to its tick to the view freeze of slot `s`
    (hw : w ∈ A.activeThroughoutToTick x tStartW (M.viewFreeze S.C s))
    -- `w` is active for the sync delay after the support cutoff of slot `s + 1` less one delay or one sync
    -- delay, whichever is longer (the holder's window,: Lemma 21b reads `w` as a holder through
    -- Lemma 64)
    (hw₀ : w ∈ A.activeThroughout x ((M.supportCutoff S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    -- `v`'s update of slot `s + 1`, on its state before the support cutoff with the expired lock
    -- entries removed, leaves `n'`
    (hUpdate : ConfirmationUpdated M S.C S.P (x.tickInput v (M.supportCutoff S.C (s + 1)))
      ((M.supportCutoff S.C (s + 1) : ℕ) : Int) (s + 1) n')
    -- `n'` saves `C'` as the confirmation of slot `s`
    (hSaved : n'.savedConfirmation s = some C')
    -- the root of `w`'s fork choice is compatible with `C'`
    (hF2 : (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.compatible C' = true)
    -- when that root is `C'` or an ancestor of `C'`, a block of `w`'s voter tree on `C'`'s chain
    -- is a viable head
    (hF3 : (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.AncestorEq C' →
      ∃ W, VoterTreeAt M (x.tickInput w (M.voteTime S.C (s + 1)))
          (S.C.t_ ((s + 1) - 1) + 3 * S.C.Δ) (s + 1) W ∧
        W ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).viable_heads ∧
          C'.AncestorEq W)
    -- no live lock entry `w`'s revocation leaves conflicts with `C'`
    (hLocks : ∀ (n'' : M.N) (sent : List (NamedObject V)),
      .ok (n'', sent) ∈ M.tick S.C S.P S.X (x.tickInput w (M.voteTime S.C (s + 1)))
        ((M.voteTime S.C (s + 1) : ℕ) : Int) →
      AwakeFor M S.C (x.tickInput w (M.voteTime S.C (s + 1))) (s + 1) →
      ∀ e ∈ M.lockEntries n'',
        M.is_live (x.tickInput w (M.voteTime S.C (s + 1)))
          ((M.voteTime S.C (s + 1) : ℕ) : Int) e = true → e.B.compatible C' = true)
    -- `w` put `vote` on the wire at its tick at the vote time of slot `s + 1`
    (hSend : ∃ i : ℕ, x.lbl i = Event.tick w (M.voteTime S.C (s + 1)) ∧
      (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i) :
    -- then `vote` is `w`'s vote for a block it holds on `C'`'s chain
    ∃ H_w ∈ (x.tickInput w (M.voteTime S.C (s + 1))).tree,
      vote = GoldfishVote.mk w (s + 1) H_w.root ∧ C'.AncestorEq H_w :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem36b_confirmed_block_extended_held M F U) S
    A x R GST s C' v w n' vote E hNet hSkew hRedeliver Sy hΔs hRoots hParent hGST hv tStartW htStartW hw hw₀
    hUpdate hSaved hF2 hF3 hLocks hSend

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
`Hon'`; `ChainInvFor M S Sched x (Hon M) 𝓒 s'` holds; every member of `Hon'` is in `Hon` or holds no
lock entry live at the vote time of slot `s' + 1` on its state before that time; every member of
`Hon` satisfies `LiveLocksOnFamilyAt M S Sched x 𝓒 s'`; every block of `𝓒` is `C'` or an ancestor of
`C'` for every confirmation `C'` of slot `s'` a member of `Upd` holds right after the support
cutoff of slot `s' + 1`; and `StepFrameAt M S Sched x C s' w` holds at every member `w` of `Hon'`
for every block `C` of `𝓒` and every such confirmation `C`. Then
`ChainInvFor` holds at slot `s' + 1`, read at `Hon'`, for the family of the blocks of `𝓒` and the
blocks that are a confirmation of slot `s'` of a member of `Upd` or an ancestor of one.

Why: for a block of `𝓒`, the first clause is Lemma 26b with the votes of `S.P.committee s' ∩ Hon M`
(the first clause at slot `s'`), the second clause comes from where a live lock comes from
(`revoked_lock_source`: the member's own confirmation of slot `s'`, which extends the block, or a
lock left by its revocation of slot `s' + 1`, compatible by the second clause at slot `s'`), and
the third is Lemma 78 with the votes of `S.P.committee (s' + 1) ∩ Hon'` (the first clause just
proved). For a new confirmation `C'`, the first clause is Lemma 36b at `C'`, whose lock condition
is the lock invariant (each live lock is on the chain of a block of `𝓒`, an ancestor of `C'`); the
second clause uses Lemma 32 (two updaters' confirmations of slot `s'` are compatible) and the lock
invariant; the third is Lemma 78 again. An ancestor of a new confirmation inherits the three clauses
from it (`honestChainExtends_of_ancestorEq`). A member of `Hon'` outside `Hon` holds no live lock,
so its revocation of slot `s' + 1` leaves none (Lemma 38). `probe_lem89_1.lean`'s `hs1 : 1 ≤ s'` is not used and is
not a hypothesis.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s'`: the slot of the step;
- `Hon`: the voters of slot `s'`; `Hon'`: the members at slot `s' + 1`; `Upd`: the updaters whose
  confirmations of slot `s'` join the family; `𝓒`: the family of blocks.

Read aloud: the honest chain grows by the confirmations of slot `s'`: when the voters of slot `s'`
satisfy the invariant for every block of the family and their live locks are on its chain, the
members of slot `s' + 1` satisfy it for every block of the family and every block of a new
confirmation's chain.

Roots name blocks until `M.supportCutoff S.C (s' + 1)`, where Lemma 36b reads them, and up to every
validator's tick to a clock value at most that cutoff: Lemmas 78 and
32 read them up to the updaters' own ticks to the cutoff, which can come after its real time; Lemma 26b
reads them up to the voter's tick to the support cutoff of slot `s'`. -/
theorem lem89s_chain_step (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s' : ℕ) (Hon Hon' Upd : Finset V)
    (𝓒 : Block V → Prop)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C (s' + 1)))
    -- roots name blocks also up to every validator's tick to a clock value at most the support cutoff of slot `s' + 1`
    -- ('s shape: Lemmas 78 and 32 read them up to the updaters' own ticks to that cutoff)
    (hRootsTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (s' + 1) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s')
    -- the voters of slot `s'` are honest active validators of slot `s'`
    (hHon : Hon ⊆ honestActiveAt M S A x s')
    -- the members at slot `s' + 1` are honest active validators of slot `s' + 1`
    (hHon' : Hon' ⊆ honestActiveAt M S A x (s' + 1))
    -- the updaters are updaters of slot `s'`
    (hUpd : Upd ⊆ updaterAt M S A x s')
    -- every member at slot `s' + 1` is one of the updaters
    (hHonUpd : Hon' ⊆ Upd)
    -- the committee majorities at slots `s'` and `s' + 1`
    (hCommittee : |S.P.committee s'| < 2 * |S.P.committee s' ∩ Hon|)
    (hCommittee' : |S.P.committee (s' + 1)| < 2 * |S.P.committee (s' + 1) ∩ Hon'|)
    -- the chain invariant at slot `s'` for the family
    (hInv : ChainInvFor M S A x Hon 𝓒 s')
    -- a member at slot `s' + 1` outside `Hon` holds no live lock at the vote time of slot `s' + 1`
    (hNew : ∀ u ∈ Hon', u ∈ Hon ∨
      ∀ e ∈ (x.tickInput u (M.voteTime S.C (s' + 1))).lockEntries,
        M.is_live (x.tickInput u (M.voteTime S.C (s' + 1)))
          ((M.voteTime S.C (s' + 1) : ℕ) : Int) e = false)
    -- the lock invariant at slot `s'` at the voters
    (hLocks : ∀ u ∈ Hon, LiveLocksOnFamilyAt M S A x 𝓒 s' u)
    -- every block of the family is on the chain of every updater's confirmation of slot `s'`
    (hConfExt : ∀ C : Block V, 𝓒 C → ∀ v ∈ Upd, ∀ C' : Block V,
      (x.tickOutput v (M.supportCutoff S.C (s' + 1))).savedConfirmation s' = some C' →
      C.AncestorEq C')
    -- the frame conditions of the step, for every block of the family and every updater's
    -- confirmation of slot `s'`
    (hStep : ∀ C : Block V, (𝓒 C ∨ ∃ v ∈ Upd,
        (x.tickOutput v (M.supportCutoff S.C (s' + 1))).savedConfirmation s' = some C) →
      ∀ w ∈ Hon', StepFrameAt M S A x C s' w) :
    -- then the chain invariant at slot `s' + 1` for the extended family
    ChainInvFor M S A x Hon' (fun C => 𝓒 C ∨ ∃ v ∈ Upd, ∃ C' : Block V,
      (x.tickOutput v (M.supportCutoff S.C (s' + 1))).savedConfirmation s' = some C' ∧
      C.AncestorEq C') (s' + 1) :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem89s_chain_step M F U) S A x R GST s' Hon Hon'
    Upd 𝓒 E hNet hSkew hRedeliver Sy hΔs hRoots hRootsTick hParent hOwner hGST hHon hHon' hUpd hHonUpd hCommittee
    hCommittee' hInv hNew hLocks hConfExt hStep

/-- **The step of the lock invariant, at one member.** In an execution where every
time is reached: when `u` is awake and honest at every time from the
duty window's start of slot `s' + 2` to the vote time of slot `s' + 2`, every block of `𝓒` is a
block of `𝓒'`, `u`'s saved confirmation of slot `s'` right after the support cutoff of slot
`s' + 1` is a block of `𝓒'`, and `LiveLocksOnFamilyAt M S Sched x 𝓒 s' u` holds — then every lock
entry of every node state `u`'s revocation of slot `s' + 2` at its vote time can leave
(`LocksRevoked`), live then, is on a block of `𝓒'` or an ancestor of one: the condition of
`LiveLocksOnFamilyAt M S Sched x 𝓒' (s' + 1) u` on every state the revocation can leave
(`liveLocksOnFamilyAt_of_locksRevoked` gives the condition itself).

The landed statement reads the answer of the revocation; the twin reads every node state the
revocation can leave (`LocksRevoked`), the form of Lemma 79b's twin, which recovers the landed
statement at every answer; a caller holding an outcome of the tick at a vote time, from a state
awake for the slot, reaches it by `locksRevoked_of_voteTime_outcome`.

Why: a lock entry `u`'s revocation of slot `s' + 2` leaves live is on an ancestor of a block of an
entry of `u`'s state then (Lemma 38). That entry was added by `u`'s update of slot `s' + 1`, on its
saved confirmation of slot `s'` or an ancestor of it, or by an earlier update, and then an entry
for it survived the revocation of slot `s' + 1` live, on a descendant of its block (Lemmas 39, 41
and 13, as in `live_locks_compatible_of_honestChainExtends_tick`); the invariant at slot `s'` puts that
one on the chain of a block of `𝓒`.


The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `𝓒`, `𝓒'`: the families before and after the step; `s'`: the slot; `u`: the validator.

Read aloud: if `u` stays awake and honest through the next slot's vote, and its new confirmation
joins the family, its live locks stay on the chain of the family. -/
theorem liveLocksOnFamilyAt_step (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (𝓒 𝓒' : Block V → Prop) (s' : ℕ) (u : V)
    -- every time is reached
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    -- the two clock bounds together are less than `Δ`
    (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S)
    -- `u` is awake and honest at every step from its tick to a clock value at most the duty window's
    -- start of slot `s' + 2` up to its tick to the vote time of slot `s' + 2`
    (hHon : u ∈ A.activeThroughoutToTick x (M.dutyWindowStart S.C (s' + 2) : ℤ) (M.voteTime S.C (s' + 2)))
    -- the family grows
    (hSub : ∀ C : Block V, 𝓒 C → 𝓒' C)
    -- `u`'s confirmation of slot `s'` joins the family
    (hOwn : ∀ C : Block V,
      (x.tickOutput u (M.supportCutoff S.C (s' + 1))).savedConfirmation s' = some C → 𝓒' C)
    -- the lock invariant at slot `s'`
    (hPrev : LiveLocksOnFamilyAt M S A x 𝓒 s' u) :
    -- then the lock invariant at slot `s' + 1`
    ∀ n' : M.N,
      LocksRevoked M S.P (x.tickInput u (M.voteTime S.C (s' + 2)))
        ((M.voteTime S.C (s' + 2) : ℕ) : Int) (s' + 2) n' →
      ∀ e ∈ M.lockEntries n',
        M.is_live (x.tickInput u (M.voteTime S.C (s' + 2)))
          ((M.voteTime S.C (s' + 2) : ℕ) : Int) e = true →
        ∃ D : Block V, 𝓒' D ∧ e.B.AncestorEq D :=
  (GoldilocksCorrectness.Record.Proofs.Executions.liveLocksOnFamilyAt_step M F U) S A x R 𝓒 𝓒' s'
    u E hSkew hHon hSub hOwn hPrev

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
`s + 1` satisfies `VoterFrameOnChainAt M S Sched x s₀ (s + 1)` and
`UpdaterFinalizedOnChainAt M S Sched x s₀ (s + 1)`; and every updater of slot `s` satisfies
`UpdaterFinalizedOnChainAt M S Sched x s₀ s` — then `HonestChainExtends` holds at slot `s + 1` at
the honest active validators of slot `s + 1` for every block on the honest chain of the slots
before `s + 1` (`Inv (s + 1)`).

Why: the chain step `lem89s_chain_step` with `Hon M := honestActiveAt M S Sched s`,
`Hon' := honestActiveAt M S Sched (s + 1)`, `Upd := updaterAt M S Sched s` and the family the chain
of the slots before `s`. The committee majorities come from committee sleepiness (Lemma 88); a
member of slot `s + 1` outside `honestActiveAt M S Sched s` slept in the window before the duty
window of slot `s + 1` (`mem_honestActiveAt_or_slept`) and holds no live lock
(`lock_free_after_wake`); every chain block before `s` is an ancestor of every updater's
confirmation of slot `s` by Lemma 78 at the updater, its voters the honest active committee members
of slot `s`; the frame conditions of the step are the two frame definitions at slot `s + 1`. The
chain before `s + 1` is the chain before `s` and the updaters' confirmations of slot `s` with their
ancestors. The brief's
`hs₀ : s₀ < s`, `GST ≤ M.voteTime S.C s₀` and `anchor ≤ M.slotStart S.C s₀` are replaced by what the
proof reads: `s₀ ≤ s`, `GST ≤ voteTime S s` and `anchor ≤ M.slotStart S.C (s + 1)`; the frame
condition at slot `s + 1`'s updaters is read at the honest active validators of slot `s + 1` only.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s₀`: the first slot of the chain;
  `s`: the slot of the step; `anchor`: the time from which committee sleepiness holds.

Read aloud: `Inv s` and the lock invariant at slot `s` give `Inv (s + 1)`.

Roots name blocks until `M.supportCutoff S.C (s + 1)`, and up to every validator's tick to a clock value
at most that cutoff (`hRootsTick`): the chain step, which the proof calls at slot `s`, reads both. -/
theorem lem81b_chain_step (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ s anchor : ℕ)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C (s + 1)))
    -- roots name blocks also up to every validator's tick to a clock value at most the support cutoff of slot `s + 1`
    -- ('s shape: Lemmas 78 and 32 read them up to the updaters' own ticks to that cutoff)
    (hRootsTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (s + 1) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s)
    -- the step is at or after the first slot of the chain
    (hs₀ : s₀ ≤ s)
    -- committee sleepiness from `anchor` for the slots whose update is at most `M.supportCutoff S.C (s + 2)`, and slot `s + 1` starts at or after `anchor`
    (hSleepK : CommitteeSleepinessUntil M S A x anchor (M.supportCutoff S.C (s + 2)))
    (hAnchor : anchor ≤ M.slotStart S.C (s + 1))
    -- `Inv s`
    (hInv : ChainInvFor M S A x (honestActiveAt M S A x s)
      (OnHonestChainBefore M S A x s₀ s) s)
    -- the lock invariant at slot `s`
    (hLocks : ∀ u ∈ honestActiveAt M S A x s,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ s) s u)
    -- the frame conditions at slot `s + 1`'s members
    (hVoterFrame : ∀ w ∈ honestActiveAt M S A x (s + 1),
      VoterFrameOnChainAt M S A x s₀ (s + 1) w)
    -- the frame condition at slot `s`'s updaters
    (hUpdaterFrame : ∀ v ∈ updaterAt M S A x s, UpdaterFinalizedOnChainAt M S A x s₀ s v)
    (hUpdaterFrame' : ∀ w ∈ honestActiveAt M S A x (s + 1),
      UpdaterFinalizedOnChainAt M S A x s₀ (s + 1) w) :
    -- then `Inv (s + 1)`
    ChainInvFor M S A x (honestActiveAt M S A x (s + 1))
      (OnHonestChainBefore M S A x s₀ (s + 1)) (s + 1) :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem81b_chain_step M F U) S A x R GST s₀ s anchor
    E hNet hSkew hRedeliver Sy hΔs hRoots hRootsTick hParent hOwner hGST hs₀ hSleepK hAnchor hInv hLocks hVoterFrame
    hUpdaterFrame hUpdaterFrame'

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
`VoterFrameOnChainAt M S Sched x s₀ s` and every updater of slot `s` satisfies
`UpdaterFinalizedOnChainAt M S Sched x s₀ s` — then at every slot `s` with `s₀ < s < n` the chain
invariant `ChainInvFor` holds at the honest active validators of slot `s` for the chain before `s`,
and every honest active validator of slot `s` satisfies the lock invariant `LiveLocksOnFamilyAt`
for the chain before `s`.

Why: the induction of `lem81_inv`, stopped before `n`: at `s₀ + 1` the chain step at slot `s₀`
with the family of `B₀` and its ancestors; after it, Lemma 81b and `liveLocksOnFamilyAt_step`.
The conclusion at a slot `s` reads the chain step at slot `s − 1`, which takes blocks as held up to
the support cutoff of slot `s`, at most that of slot `n − 1`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s₀`: the healed slot; `anchor`: the
  time from which committee sleepiness holds; `n`: the bound on the slots; `B₀`: the block every
  updater of slot `s₀` saved.

Read aloud: from the healed slot on and before slot `n`, every honest vote, live lock and
confirmation extends the chain so far, provided roots name blocks up to the support cutoff of slot
`n − 1` and `VoterFrameOnChainAt`, `UpdaterFinalizedOnChainAt` hold at the slots before `n`.

 `lem81_inv` is its instance at `n := s + 1`. -/
theorem lem81_inv_before (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ anchor n : ℕ) (B₀ : Block V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- a root names one block among what honest validators hold by the support cutoff of slot
    -- `n − 1`
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C (n - 1)))
    -- roots name blocks also up to the real time of every validator's tick to a clock value at most the
    -- support cutoff of slot `n − 1`
    (hRootsTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (n - 1) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀)
    -- committee sleepiness from `anchor` for the slots whose update is at most `M.supportCutoff S.C n`, and slot `s₀ + 1` starts at or after `anchor`
    (hSleepK : CommitteeSleepinessUntil M S A x anchor (M.supportCutoff S.C n))
    (hAnchor : anchor ≤ M.slotStart S.C (s₀ + 1))
    -- `B₀`'s slot is at least `s₀`
    (hB₀slot : s₀ ≤ B₀.slot)
    -- the slot invariant restricted to `B₀` at slot `s₀`
    (hBase : HonestChainExtends M S A x (honestActiveAt M S A x s₀) B₀ s₀)
    -- every updater of slot `s₀` saved `B₀`
    (hBaseSaved : ∀ v ∈ updaterAt M S A x s₀,
      (x.tickOutput v (M.supportCutoff S.C (s₀ + 1))).savedConfirmation s₀ = some B₀)
    -- `VoterFrameOnChainAt` and `UpdaterFinalizedOnChainAt` at every slot after `s₀` and before
    -- `n`
    (hVoterFrame : ∀ s : ℕ, s₀ < s → s < n → ∀ w ∈ honestActiveAt M S A x s,
      VoterFrameOnChainAt M S A x s₀ s w)
    (hUpdaterFrame : ∀ s : ℕ, s₀ < s → s < n → ∀ v ∈ updaterAt M S A x s,
      UpdaterFinalizedOnChainAt M S A x s₀ s v) :
    -- then the chain invariant and the lock invariant hold at every slot after `s₀` and before `n`
    ∀ s : ℕ, s₀ < s → s < n →
      ChainInvFor M S A x (honestActiveAt M S A x s)
        (OnHonestChainBefore M S A x s₀ s) s ∧
      ∀ u ∈ honestActiveAt M S A x s,
        LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ s) s u :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem81_inv_before M F U) S A x R GST s₀ anchor n
    B₀ E hNet hSkew hRedeliver Sy hΔs hRoots hRootsTick hParent hOwner hGST hSleepK hAnchor hB₀slot hBase hBaseSaved
    hVoterFrame hUpdaterFrame

end GoldilocksCorrectness.Record.Statements.Executions

