module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.PhaseChain
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# PhaseChainStatements, over a model

The statements of `GoldilocksCorrectness/Statements/Executions/PhaseChainStatements.lean`, over a
model `M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: the phase step, the
re-base of the chain invariant at a common fork-choice root, and Lemma 45b. Each is the theorem of
the same name of `Record/Restated/Proofs/Executions/PhaseChain.lean`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ voteTime supportCutoff dutyWindowStart)

namespace GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor ConfirmationUpdated CountedVotes
  LocksRevoked VoterTreeAt)
open GoldilocksCorrectness.Statements.Executions (acObject)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Statements.Routines (expireLocks)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-! ## The phase step -/

/-- **The phase step.** In an execution where every time is reached, corruption is
permanent, blocks and Goldfish votes are delivered within `Δ` after `GST` (synchrony from the
receiver's wake, and catch-up on wake), a root names one block among
what honest validators hold, a block reaches a validator only once it holds the parent, and nobody
votes in an honest validator's name: if `GST` is at most the vote time of slot `s'`; the members
of `Hon` are awake and honest from the duty window's start of slot `s'` to the support cutoff of
slot `s' + 1`; the members of `Hon' ⊆ Hon M` are awake and honest from the duty window's start of
slot `s' + 1` to the support cutoff of slot `s' + 2`; the committee of slot `s'` has fewer than
twice its members in `Hon`, and that of slot `s' + 1` fewer than twice its members in `Hon'`;
`ChainInvFor M S Sched x (Hon M) 𝓒 s'` holds; every member of `Hon` satisfies
`LiveLocksOnFamilyAt M S Sched x 𝓒 s'`; and `StepFrameAt M S Sched x C s' w` holds at every member
`w` of `Hon'` for every block `C` of `𝓒` and every confirmation `C` of slot `s'` a member of `Hon'`
holds right after the support cutoff of slot `s' + 1` — then, for the family of the blocks of `𝓒`
and the blocks that are such a confirmation or an ancestor of one, `ChainInvFor` holds at slot
`s' + 1` at `Hon'`, and every member of `Hon'` satisfies `LiveLocksOnFamilyAt` at slot `s' + 1`.

Why: the chain step `lem89s_chain_step` with the voters `Hon`, the members `Hon'` and the updaters
`Hon'`: each member of `Hon'` is in `Hon`, and the invariant's third clause at `Hon' ⊆ Hon M` puts
every block of `𝓒` on the chain of every confirmation of slot `s'` a member of `Hon'` holds. Then
the lock invariant's step `liveLocksOnFamilyAt_step` at every member of `Hon'`, whose own
confirmation of slot `s'` is in the extended family.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s'`: the slot of the step;
- `Hon`: the voters of slot `s'`; `Hon'`: the members of slot `s' + 1`; `𝓒`: the family.

Read aloud: inside the phase, the honest chain grows by the confirmations of slot `s'`, each
slot's members awake and honest only through their own slot's update.



Roots name blocks until `M.supportCutoff S.C (s' + 1)`: the proof reads `lem89s_chain_step` at slot
`s'`, whose bound is that time. -/
theorem lem89s_phase_step (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s' : ℕ) (Hon Hon' : Finset V) (𝓒 : Block V → Prop)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C (s' + 1)))
    -- roots name blocks also up to the real time of every validator's tick to a clock value at most the
    -- support cutoff of slot `s' + 1`
    (hRootsTick : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (s' + 1) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x) (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s')
    -- the voters of slot `s'` are honest active validators of slot `s'`
    (hHon : Hon ⊆ honestActiveAt M S A x s')
    -- the members of slot `s' + 1` are honest active validators of slot `s' + 1`
    (hHon' : Hon' ⊆ honestActiveAt M S A x (s' + 1))
    -- the members of slot `s' + 1` are voters of slot `s'`
    (hSub : Hon' ⊆ Hon)
    -- the committee majorities of slots `s'` and `s' + 1`
    (hCommittee : (S.P.committee s').card < 2 * (S.P.committee s' ∩ Hon).card)
    (hCommittee' : (S.P.committee (s' + 1)).card < 2 * (S.P.committee (s' + 1) ∩ Hon').card)
    -- the chain invariant at slot `s'` for the family
    (hInv : ChainInvFor M S A x Hon 𝓒 s')
    -- the lock invariant at slot `s'` at the voters
    (hLocks : ∀ u ∈ Hon, LiveLocksOnFamilyAt M S A x 𝓒 s' u)
    -- the frame conditions of the step, for every block of the family and every member's
    -- confirmation of slot `s'`
    (hStep : ∀ C : Block V, (𝓒 C ∨ ∃ v ∈ Hon',
        (x.tickOutput v (M.supportCutoff S.C (s' + 1))).savedConfirmation s' = some C) →
      ∀ w ∈ Hon', StepFrameAt M S A x C s' w) :
    -- then both invariants at slot `s' + 1` for the extended family
    ChainInvFor M S A x Hon' (fun C => 𝓒 C ∨ ∃ v ∈ Hon', ∃ C' : Block V,
      (x.tickOutput v (M.supportCutoff S.C (s' + 1))).savedConfirmation s' = some C' ∧
      C.AncestorEq C') (s' + 1) ∧
    ∀ u ∈ Hon', LiveLocksOnFamilyAt M S A x (fun C => 𝓒 C ∨ ∃ v ∈ Hon', ∃ C' : Block V,
      (x.tickOutput v (M.supportCutoff S.C (s' + 1))).savedConfirmation s' = some C' ∧
      C.AncestorEq C') (s' + 1) u :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem89s_phase_step M F U) S A x R GST s' Hon Hon' 𝓒 E hNet hSkew hRedeliver Sy hΔs
    hRoots hRootsTick hParent hOwner hGST hHon hHon' hSub hCommittee hCommittee' hInv hLocks hStep

/-! ## The re-base -/

open Classical in
/-- **Lemma 89c, the re-base.** In an execution where every time is reached, corruption is
permanent, blocks and Goldfish votes are delivered within `Δ` after `GST` (synchrony from the
receiver's wake, and catch-up on wake), a root names one block among
what honest validators hold, a block reaches a validator only once it holds the parent, and nobody
votes in an honest validator's name: if `GST` is at most the vote time of slot `s`; every member of
`Hon` is awake and honest from a tick at or before the duty window's start of slot `s` up to its own tick to
the vote time of slot `s`, runs the update of slot `s` (awake and honest from a tick at or before the duty window's
start of slot `s + 1` up to its own tick to the support cutoff of slot `s + 1`), and is outside the adversary set at
every honest validator's tick to that cutoff; the committee of slot `s` has fewer than twice its members in `Hon`; every member's
fork-choice root at its tick to the vote time of slot `s` is `R`; and every member's finalized block
at its tick to the support cutoff of slot `s + 1` is compatible with `R` — then
`HonestChainExtends M S Sched x (Hon M) R s` holds.

Why: every honest vote names a block on the chain of its voter's own root, `R`
(`vote_extends_own_root`); the committee members of `Hon` voting for `R`'s chain reach every
member's pool by the support cutoff of slot `s` (Lemma 12), so Lemma 5 leaves every lock of the
revocation of slot `s + 1` compatible with `R`, unless the member's finalized block is already on
`R`'s chain and every entry descends from it; Lemma 78 puts the confirmations on `R`'s chain.

Why the members are read three ways: as voters, awake and honest up to their own tick to the vote time of
slot `s` (`hHonVote`, the wake test of that tick); as updaters, awake and honest up to their own tick to the
support cutoff of slot `s + 1` (`hHonUpd`); and as honest at every honest validator's tick to that cutoff
(`hHonTick`). Lemma 78 reads the slot-`s` vote of each committee member of `Hon` as its only slot-`s` vote in
the updater's pool at the updater's tick to that cutoff, which needs the member honest at that tick
(`hHonTick`); a member corrupted after the vote time of slot `s + 1` could put a second slot-`s` vote on the
wire before it. The planned caller, the re-base after a switch, reads this lemma at the
validators honest at the support cutoff of slot `s + 1`, who are honest at every earlier time and,
in the phase, awake.

The committee majority of slot `s + 1` and the hypothesis `1 ≤ s` of the plan's statement are not
hypotheses: the proof reads neither.

The statement of record.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s`: the slot;
- `Hon`: the members; `R`: the common root.

Read aloud: when every member's fork choice at its tick to the vote time of slot `s` is rooted at `R`, no
member's finalized block at its tick to the support cutoff of slot `s + 1` conflicts with `R`, the members stay awake
and honest through the update of slot `s`, each runs that update, and no member is in the adversary set at
a tick of an honest validator to that cutoff, the honest chain re-forms on `R` in one slot.



Roots name blocks up to every validator's tick to a clock value at most `M.supportCutoff S.C s`: the proof
reads Lemma 12 and Lemma 78 at slot `s` at the validators' own ticks to that cutoff. -/
theorem lem89c_rebase (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (Run : RunFacts M S x) (GST s : ℕ) (Hon : Finset V) (R : Block V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- roots name blocks up to every validator's tick to a clock value at most the support cutoff of slot `s`
    (hRoots : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C s →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x) (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s)
    -- every member is awake and honest from the start of its slot-`s` window, `duty_window_start S.C s`, up to its own
    -- tick to the vote time of slot `s`
    (hHonVote : ∀ v ∈ Hon, v ∈ A.activeThroughoutToTick x (duty_window_start S.C s) (M.voteTime S.C s))
    -- each member runs the update of slot `s`: it ticks to the support cutoff of slot `s + 1`, active up to that tick
    -- from a tick at or before the duty window's start of slot `s + 1`
    (hHonUpd : ∀ v ∈ Hon, v ∈ updaterAt M S A x s)
    -- no member is in the adversary set at a step where a validator outside it ticks to the support cutoff of
    -- slot `s + 1` (, the second honesty read of)
    (hHonTick : ∀ u ∈ Hon, u ∉ Finset.univ.filter (fun u => ∃ (k : ℕ) (w : V),
      x.lbl k = Event.tick w (M.supportCutoff S.C (s + 1)) ∧ w ∉ A.corrupted k ∧ u ∈ A.corrupted k))
    -- the committee majority of slot `s`
    (hCommittee : (S.P.committee s).card < 2 * (S.P.committee s ∩ Hon).card)
    -- every member's fork-choice root at its tick to the vote time of slot `s` is `R`
    (hRoot : ∀ w ∈ Hon, M.get_fc_root (x.tickInput w (M.voteTime S.C s)) = R)
    -- no member's finalized block at its tick to the support cutoff of slot `s + 1` conflicts with `R`
    (hF : ∀ v ∈ Hon,
        (x.tickInput v (M.supportCutoff S.C (s + 1))).finalized.compatible R = true) :
    -- then the slot invariant restricted to `R` at slot `s`
    HonestChainExtends M S A x Hon R s :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem89c_rebase M F U) S A x Run GST s Hon R E hNet hSkew hRedeliver Sy hΔs
    hRoots hParent hOwner hGST hHonVote hHonUpd hHonTick hCommittee hRoot hF

/-! ## Lemma 45b -/

/-- **Lemma 45b, a lock whose window is after `GST` is extended by the next slot's honest votes,
the held form.** Lemma 45's hypotheses (`lem45_honest_vote_extends_lock_of_post_GST_window`): in
an execution where every time is reached, corruption is permanent, blocks and Goldfish votes are
delivered within `Δ` after `GST` (synchrony from the receiver's wake, and catch-up on wake),
a root names one block among what honest validators hold, and a block reaches
a validator only once it holds the parent: if `GST + max (Δ S) Δs` is at most the view freeze of
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
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s`: the slot of the lock;
- `v`: the validator whose update of slot `s + 1` adds the lock entry `e`; `A'`: that update's
  answer; `w`: the voter of slot `s + 1`; `vote`: its Goldfish vote.

Read aloud: under Lemma 45's hypotheses, `w`'s vote is its slot-`(s + 1)` vote for a block of its
own tree before that vote time that is the lock's block or a descendant of it.



Roots name blocks until `M.supportCutoff S.C (s + 1)`: the proof reads Lemma 42 and Lemma 21b at
slot `s`, and Lemma 31 at a slot `s' < s`, whose bounds are at most that time. -/
theorem lem45b_honest_vote_extends_lock_held (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (GST s : ℕ) (v w : V) (e : M.LE) (vote : GoldfishVote V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (M.supportCutoff S.C (s + 1)))
    (hParent : ParentHeldAtDelivery M x)
    -- the network is synchronous from the support cutoff of slot `s + 1 − C.k` on
    (hGST : GST + max (Δ S) Δs ≤ M.viewFreeze S.C (s + 1 - S.C.k))
    -- `v` is awake and honest from the duty window's start of slot `s + 1` to its support cutoff
    (hv : v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.supportCutoff S.C (s + 1)))
    -- `w` is awake and honest from the duty window's start of slot `s + 1` to its vote time
    -- `w` ticks to the vote time of slot `s + 1`, active up to that tick from the trace's start or from its own tick
    -- to a clock value at most `tStartW`, more than both clock bounds before the window start Lemma 42 reads; `v` and
    -- `w` are active through the sync delay after the two read times of Lemma 42's sync facts
    (tStartW : ℤ) (htStartW : (tStartW : ℝ) + ΔClockAhead + ΔClockBehind <
      ((M.viewFreeze S.C s - max (3 * Δ S) Δs : ℕ) : ℝ))
    (hw : w ∈ A.activeThroughoutToTick x tStartW (M.voteTime S.C (s + 1)))
    (hv₀ : v ∈ A.activeThroughout x ((M.viewFreeze S.C s - max (Δ S) Δs : ℕ) : ℝ)
      (((M.viewFreeze S.C s - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hw₀ : w ∈ A.activeThroughout x ((M.supportCutoff S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C (s + 1) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (n' : M.N) (sent : List (NamedObject V))
    -- `v`'s update of slot `s + 1` leaves `n'`, with `e` the lock entry of slot `s` it adds
    (hUpdate : .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (M.supportCutoff S.C (s + 1)))
        ((M.supportCutoff S.C (s + 1) : ℕ) : Int))
    (hAwake : AwakeFor M S.C (x.tickInput v (M.supportCutoff S.C (s + 1))) (s + 1))
    (he : e ∈ M.lockEntries n')
    (hd : e.d = S.C.t_ (s + S.C.k) + 5 * S.C.Δ)
    -- the finality-gadget conditions at `w`, relative to the lock block (as Lemma 21's)
    (hF2 : (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.compatible e.B = true)
    (hF3 : (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).fc_root.AncestorEq e.B →
      ∃ W, VoterTreeAt M (x.tickInput w (M.voteTime S.C (s + 1)))
        (S.C.t_ ((s + 1) - 1) + 3 * S.C.Δ) (s + 1) W ∧ W ∈
          (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s + 1)))).viable_heads ∧
          e.B.AncestorEq W)
    -- `w` put `vote` on the wire at its tick at the vote time of slot `s + 1`
    (hSend : ∃ i : ℕ, x.lbl i = Event.tick w (M.voteTime S.C (s + 1)) ∧
      (⟨w, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i) :
    -- then `vote` is `w`'s vote for a block it holds on the lock block's chain
    ∃ H_w ∈ (x.tickInput w (M.voteTime S.C (s + 1))).tree,
      vote = GoldfishVote.mk w (s + 1) H_w.root ∧ e.B.AncestorEq H_w :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem45b_honest_vote_extends_lock_held M F U) S A x R GST s v
    w e vote E hNet hSkew hRedeliver Sy hΔs hRoots hParent hGST hv tStartW htStartW hw hv₀ hw₀ n' sent hUpdate hAwake he hd hF2 hF3 hSend

end GoldilocksCorrectness.Record.Statements.Executions

