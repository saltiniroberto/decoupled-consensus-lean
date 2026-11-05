module
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.HonestChainDefs
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.TickUpdateState
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma78
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma79
public import GoldilocksCorrectness.Statements.Executions.HonestChainStatements
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# HonestChainStatements, over a model

The statements of `GoldilocksCorrectness/Statements/Executions/HonestChainStatements.lean`, over a
model `M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: the step of the slot
invariant restricted to a block (Lemmas 79, 79a, 79b, 79c), the kit theorem on live locks, Lemma 78
and the two facts on the state an update of a duty leaves. Each is the theorem of the same name of
`Record/Restated/Proofs/Executions/TickUpdateState.lean`, `Lemma78.lean` or `Lemma79.lean`.
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

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor)
open GoldilocksCorrectness.Record.Statements.Routines (EarlySupporterOf)
open GoldilocksCorrectness.Statements.Executions (acObject)
open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor LocksRevoked VoterTreeAt)
open GoldilocksCorrectness.Record.Statements.Routines (CountedVotes)

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

/-! ## The tick at a support cutoff -/

/-- **The tick at the support cutoff leaves the update's answer, the awake form.** Write `c` for
the support cutoff of slot `s + 1`. In an execution where every time is reached:
when `v` ticks to `c` and that tick starts from a state awake since the duty window's start of
slot `s + 1` or earlier, the tick at `c` from `v`'s state
before `c` has an outcome `(n'', sent)`, that state is awake for slot `s + 1`, and `v`'s state
before `c + 1` has `n''`'s saved confirmations, fast blocks, lock entries and record of the
confirmed tip.

Why: the tick at `c` answers (`ticksSucceed_of_exec`) and runs the update (Lemma 15, `c` being
the support cutoff of its slot and the duty test passing); nothing after that tick and before the
next one changes those four fields.

The landed statement names the answer `A''` of the confirmation update; the twin names the outcome
of the tick the step took, under the wake condition, as its proof page's twin does.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `s`: the slot before the cutoff's slot; `v`: the validator.

Read aloud: the state right after the support cutoff holds what an outcome of the tick there
holds. -/
theorem update_state_of_duty (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s : ℕ) (v : V)
    -- every time is reached
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    -- `v` ticks to the support cutoff of slot `s + 1` at the step `i`
    {i : ℕ} (hl₂ : x.lbl i = Event.tick v (M.supportCutoff S.C (s + 1)))
    -- `v`'s tick there starts from a record of awakeness passing the duty test of slot `s + 1`
    (hAw : ∃ τ : Time, (x.tickInput v (M.supportCutoff S.C (s + 1))).awakeSince = some τ ∧ τ ≤ duty_window_start S.C (s + 1)) :
    -- then the tick at the cutoff has an outcome `(n'', sent)` from an awake state, and the state
    -- right after the cutoff has its four fields
    ∃ (n'' : M.N) (sent : List (NamedObject V)),
      .ok (n'', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (M.supportCutoff S.C (s + 1)))
        ((M.supportCutoff S.C (s + 1) : ℕ) : Int) ∧
      AwakeFor M S.C (x.tickInput v (M.supportCutoff S.C (s + 1))) (s + 1) ∧
      (x.tickOutput v (M.supportCutoff S.C (s + 1))).savedConfirmation =
        M.savedConfirmation n'' ∧
      (x.tickOutput v (M.supportCutoff S.C (s + 1))).fastBlocks = M.fastBlocks n'' ∧
      (x.tickOutput v (M.supportCutoff S.C (s + 1))).lockEntries = M.lockEntries n'' ∧
      (x.tickOutput v (M.supportCutoff S.C (s + 1))).latestConfirmed =
        M.latestConfirmed n'' :=
  (GoldilocksCorrectness.Record.Proofs.Executions.update_state_of_tick M F U) S A x R s v E hl₂
    hAw

/-- **A lock of slot `s` in hand means its holder ran the update of slot `s + 1`.** Write `c` for
the support cutoff of slot `s + 1`. In an execution where every time is reached: when `v` holds
before `t` a lock entry `e` with the deadline of a lock of slot `s`, `S.C.t_ (s + S.C.k) + 5 ·
S.C.Δ`, and `c` is before `t`, then `v` ticks to `c` and is awake and honest from the duty window's
start of slot `s + 1` up to that tick (`A.activeThroughoutToTick`), its tick at `c` started from a
record of awakeness since the duty window's start of slot `s + 1` or earlier, the tick at `c`
from `v`'s state before `c` had an outcome `(n'', sent)`, that state awake for slot `s + 1`, and
`v`'s state before `c + 1` has `n''`'s saved confirmations and lock entries.

Why: the entry is traced to the update of the slot its deadline names (Lemma 39's invariant), so
right after the tick at `c` an entry with that deadline is held, and none is held before it; the
step of that tick changed the lock entries, and of what a step does to them only the update at the
support cutoff adds an entry with a new deadline.

The landed statement names the answer `A''` of the confirmation update; the twin names the outcome
of the tick the step took, as its proof page's twin does.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `t`: the time; `s`: the slot of the lock; `v`: the validator; `e`: the lock entry.

Read aloud: a lock of slot `s` in hand means the holder ran the update of slot `s + 1`, awake, and
kept what an outcome of its tick there holds. -/
theorem update_state_of_lock_entry (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (t s : ℕ) (v : V) (e : M.LE)
    -- every time is reached
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    -- `e` is a lock entry of `v`'s state before `t`
    (he : e ∈ (x.stateBefore t v).lockEntries)
    -- `e` has the deadline of a lock of slot `s`
    (hd : e.d = S.C.t_ (s + S.C.k) + 5 * S.C.Δ)
    -- the support cutoff of slot `s + 1` is before `t`
    (hts : M.supportCutoff S.C (s + 1) < t) :
    v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.supportCutoff S.C (s + 1)) ∧
    (∃ τ : Time, (x.tickInput v (M.supportCutoff S.C (s + 1))).awakeSince = some τ ∧ τ ≤ duty_window_start S.C (s + 1)) ∧
    ∃ (n'' : M.N) (sent : List (NamedObject V)),
      .ok (n'', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (M.supportCutoff S.C (s + 1)))
        ((M.supportCutoff S.C (s + 1) : ℕ) : Int) ∧
      AwakeFor M S.C (x.tickInput v (M.supportCutoff S.C (s + 1))) (s + 1) ∧
      (x.tickOutput v (M.supportCutoff S.C (s + 1))).savedConfirmation =
        M.savedConfirmation n'' ∧
      (x.tickOutput v (M.supportCutoff S.C (s + 1))).lockEntries = M.lockEntries n'' :=
  (GoldilocksCorrectness.Record.Proofs.Executions.update_state_of_lock_entry M F U) S A x R t s v
    e E he hd hts

/-! ## Lemma 78 -/

/-- **Lemma 78, an honest confirmation update over a voter majority's chain.** In an execution
where every time is reached, corruption is permanent, blocks and Goldfish votes are delivered
within `Δ` after `GST` (synchrony from the receiver's wake, and catch-up on wake),
a root names one block among what honest validators hold, a block reaches a
validator only once it holds the parent, and nobody votes in an honest validator's name: if `GST`
is at most the vote time of slot `s`; every `u ∈ Hs` is in the slot-`s` committee, honest through
the support cutoff `c` of slot `s + 1`, put its slot-`s` vote for `H u` on the wire at its tick at
the vote time of slot `s`, and holds `H u`, a block that is `B` or a descendant of `B`, in its tree
then; the validators with a slot-`s` vote in `v`'s pool before `c` are fewer than twice `Hs`; `v`
ticks to `c` and is awake and honest after every step from the duty window's start of slot `s + 1`
up to that tick (`A.activeThroughoutToTick`); and `v`'s finalized block before `c` is compatible
with `B` — then the confirmation of slot `s` that `v` holds right after `c`, when it holds one, is
`B` or a descendant of `B`.

Why: the state right after `c` holds the confirmation the update of slot `s + 1` saved
(`update_state_of_tick`, at `v`'s tick to `c`). When `v`'s finalized block is `B` or an ancestor of `B`, Lemma 12 at `c`
delivers every member's vote to `v`, held early, and Lemma 77 makes the saved confirmation `B` or a
descendant of `B`. When `B` is an ancestor of `v`'s finalized block, the saved confirmation is that
finalized block or a descendant of it (`saved_confirmation_F_ancestorEq`). This is Lemma 27 with
the votes on `B`'s chain in place of votes for `B`, the finalized block compatible with `B` in
place of an ancestor of `B`, without its conditions that `B` is not the genesis block and on the
locks, and concluding on the saved confirmation only.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s`: the slot of the votes;
- `Hs`: the honest voters of slot `s`; `H`: the block each voter's vote is for;
- `B`: the block every vote of `Hs` extends; `v`: the validator running the confirmation update of
  slot `s + 1`.

Read aloud: if every member of `Hs` is a member of the slot-`s` committee, outside the adversary set at
`v`'s tick to the support cutoff of slot `s + 1`, that sent at the vote time of slot `s` a vote for a
block it holds that is `B` or a descendant of `B`, and that is active through the sync delay after Lemma 12's
read time `supportCutoff s − max (2 * Δ S) Δs`; the members of `Hs` are more than half of the validators with a
slot-`s` vote in `v`'s pool before that cutoff; `v` is awake and honest from the duty window's
start of slot `s + 1` up to its own tick to that cutoff; roots name blocks up to `v`'s tick to the support
cutoff of slot `s`; and `v`'s finalized block before the cutoff is compatible with
`B` — then the confirmation of slot `s` that `v` holds right after the cutoff, when it holds one,
is `B` or a descendant of `B`.

Roots name blocks until the real time of `v`'s own tick to `M.supportCutoff S.C s`: the bound of the Lemma 12 call at slot `s` its
proof passes the premise to. -/
theorem lem78_update_confirmation_extends_voter_majority_chain (U : UniformSchedule M.toSlotLayout)
    (S : Setup V)
    (A : Activity V) (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (GST s : ℕ) (Hs : Finset V) (H : V → Block V) (B : Block V) (v : V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C s))))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s)
    -- every member of `Hs` is a member of the slot-`s` committee, outside the adversary set
    -- at `v`'s tick to the support cutoff of slot `s + 1`, that sent its slot-`s` vote for `H u`, a block it holds that is `B`
    -- or a descendant of `B`
    (hHs : ∀ u ∈ Hs, u ∈ S.P.committee s ∧ u ∉ A.corrupted (x.tickStep v (M.supportCutoff S.C (s + 1))) ∧
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s) ∧
        (⟨u, NamedObject.gfVote (GoldfishVote.mk u s (H u).root)⟩ :
    -- then `v`'s confirmation of slot `s` right after the cutoff is on `B`'s chain
          SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) ∧
      H u ∈ (x.tickInput u (M.voteTime S.C s)).tree ∧ B.AncestorEq (H u))
    -- every voter is active in every configuration in force at a real time of `[t₀, t₀ + Δs]`, `t₀` the sync
    -- fact's read time `supportCutoff s − max (2 * Δ S) Δs` (:'s holder clause)
    (hHold : ∀ u ∈ Hs, u ∈ A.activeThroughout x ((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ)
      (((M.supportCutoff S.C s - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    -- the validators with a slot-`s` vote in `v`'s pool before the cutoff are fewer than twice
    -- `Hs`
    (hVoters : M.voters_count (M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (s + 1))) s) <
      2 * Hs.card)
    -- `v` is awake and honest from the duty window's start of slot `s + 1` up to its tick to the cutoff
    (hv : v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.supportCutoff S.C (s + 1)))
    -- `v`'s finalized block before the cutoff is compatible with `B`
    (hF : (x.tickInput v (M.supportCutoff S.C (s + 1))).finalized.compatible B = true) :
    -- then `v`'s confirmation of slot `s` right after the cutoff is on `B`'s chain
    ∀ C' : Block V,
      (x.tickOutput v (M.supportCutoff S.C (s + 1))).savedConfirmation s = some C' →
      B.AncestorEq C' :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem78_update_confirmation_extends_voter_majority_chain M F U)
    S A x R GST s Hs H B v E hNet hSkew hRedeliver Sy hΔs hRoots hParent hOwner hGST hHs hHold hVoters hv hF

/-! ## The live locks under the invariant -/

/-- **The live locks of a member are compatible with `B`, read at the member's tick.** In an execution where every
time is reached: when `HonestChainExtends M S Sched x Hon B s'` holds, `w` is a member of `Hon` that ticks to the vote
time of slot `s' + 1`, active at every step up to that tick from the trace's start or from its own tick to a clock
value at most the duty window's start of slot `s' + 2`, and the clock value `c` is greater than the support cutoff of
slot `s' + 1` and at most the vote time of slot `s' + 2`, then every lock entry of the state `w`'s tick to `c` starts
from whose deadline is greater than `c` is on a block compatible with `B`.

Why: the entry was added by `w`'s confirmation update of a slot `s₁ + 1`, at its tick to the support cutoff of that
slot, before its tick to `c`, so `s₁ ≤ s'` (the clocks of one validator do not go back), on a block that is the saved
confirmation of slot `s₁` or an ancestor of it, and its block is that block or an ancestor of it (Lemma 39). When
`s₁ = s'`, the saved confirmation is the one the third clause of the invariant reads, `B` or a descendant of `B`.
When `s₁ < s'`, the deadline being greater than `c` makes `s₁ + S.C.k ≥ s' + 1` (Lemma 41); `w`'s tick to the vote
time of slot `s' + 1` comes after its tick to the support cutoff of slot `s₁ + 1` and before its tick to `c`, from a
state awake for slot `s' + 1`, and ran the revocation (Lemma 13); an entry with the entry's deadline, on its block or a
descendant of it, survived the revocation live (Lemma 39's trace), and the second clause of the invariant makes it
compatible with `B`. the
window starts at the duty window's start of slot `s' + 2`; read at the tick's input in place of the real
time `t` of `dev`'s form.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `Hon`: the validators the invariant is read at; `B`: the block; `s'`: the slot of the
  invariant; `c`: the clock value of the tick; `w`: the member.

Read aloud: between the update of slot `s' + 1` and the revocation of slot `s' + 2`, every lock that has not expired
in the state a member's tick starts from is on a block compatible with `B`. -/
theorem live_locks_compatible_of_honestChainExtends_tick (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (Hon : Finset V) (B : Block V) (s' c : ℕ) (w : V)
    -- every time is reached
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    -- the slot invariant restricted to `B` holds at slot `s'`
    (hInv : HonestChainExtends M S A x Hon B s')
    -- `w` is a member of `Hon`
    (hw : w ∈ Hon)
    -- `w` ticks to the vote time of slot `s' + 1`, active at every step up to that tick from the trace's start or
    -- from its own tick to a clock value at most the duty window's start of slot `s' + 2` (, F-48-1)
    (hHon : w ∈ A.activeThroughoutToTick x ((M.dutyWindowStart S.C (s' + 2) : ℕ) : ℤ) (M.voteTime S.C (s' + 1)))
    -- `c` is greater than the support cutoff of slot `s' + 1`
    (hc1 : M.supportCutoff S.C (s' + 1) < c)
    -- `c` is at most the vote time of slot `s' + 2`
    (hc2 : c ≤ M.voteTime S.C (s' + 2)) :
    -- then every entry of the state `w`'s tick to `c` starts from, with its deadline greater than `c`, is
    -- compatible with `B`
    ∀ e ∈ (x.tickInput w c).lockEntries, ((c : ℕ) : Int) < e.d →
      e.B.compatible B = true :=
  (GoldilocksCorrectness.Record.Proofs.Executions.live_locks_compatible_of_honestChainExtends_tick M F U)
    S A x R Hon B s' c w E hInv hw hHon hc1 hc2

/-! ## Lemma 79, the step -/

open Classical in
/-- **Lemma 79a, the first clause of the step.** In an execution where every time is reached,
corruption is permanent, blocks and Goldfish votes are delivered within `Δ` after `GST`
(synchrony from the receiver's wake, and catch-up on wake), a root
names one block among what honest validators hold, a block reaches a validator only once it holds
the parent, and nobody votes in an honest validator's name: if `GST` is at most the vote time of
slot `s'`; `HonestChainExtends M S Sched x Hon B s'` holds; the members of `Hon` are awake and
honest from the duty window's start of slot `s' + 1` to the vote time of slot `s' + 1`; every member
of `Hs` is a member of `Hon` and of the slot-`s'` committee that put a slot-`s'` vote on the wire at
its tick at the vote time of slot `s'`; at every member `w` voting at slot `s' + 1`, the validators
with a vote among those `w` counts are fewer than twice `Hs`, the root of `w`'s fork choice is
compatible with `B`, and, when that root is `B`
or an ancestor of `B`, some block of `w`'s voter tree on `B`'s chain is a viable head — then every
slot-`(s' + 1)` vote a member put on the wire at its tick at the vote time of slot `s' + 1` is its
vote for a block it holds then that is `B` or a descendant of `B`.

Why: the first clause of the invariant makes each member of `Hs` an honest voter of slot `s'` for a
block it holds on `B`'s chain, and the second clause gives the lock condition at the vote time of
slot `s' + 1`; Lemma 26b with `R := B` concludes.



The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s'`: the slot of the invariant;
- `Hon`: the validators the invariant is read at; `Hs`: the honest voters of slot `s'`;
- `B`: the block.

Read aloud: under the invariant at slot `s'`, the members' votes of slot `s' + 1` are for blocks
they hold on `B`'s chain.

Roots name blocks up to every validator's tick to a clock value at most `M.supportCutoff S.C s'`: Lemma 26b,
which the proof calls at slot `s'`, takes them up to the voter's own tick to that cutoff, which can come after
its real time. -/
theorem lem79a_honestChainExtends_votes_step (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (GST s' : ℕ) (Hon : Finset V) (Hs : Finset V) (B : Block V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- roots name blocks up to every validator's tick to a clock value at most the support cutoff of slot `s'`
    (hRoots : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C s' →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s')
    -- the slot invariant restricted to `B` holds at slot `s'`
    (hInv : HonestChainExtends M S A x Hon B s')
    -- the members of `Hon` are awake and honest from the duty window's start of slot `s' + 1` to
    -- the vote time of slot `s' + 1`
    (hHon : ∀ v ∈ Hon, v ∈ A.activeThroughout x (M.dutyWindowStart S.C (s' + 1)) (M.voteTime S.C (s' + 1)))
    -- no member is in the adversary set at a step where a validator outside it ticks to the vote time of slot
    -- `s' + 1` (the second honesty read,; Lemma 26b reads the voters' honesty at the member's tick)
    (hHonTick : ∀ u ∈ Hon, u ∉ Finset.univ.filter (fun u => ∃ (k : ℕ) (w : V),
      x.lbl k = Event.tick w (M.voteTime S.C (s' + 1)) ∧ w ∉ A.corrupted k ∧ u ∈ A.corrupted k))
    -- every member of `Hs` is a member of `Hon` and of the slot-`s'` committee that sent a
    -- slot-`s'` vote at the vote time of slot `s'`
    (hHs : ∀ u ∈ Hs, u ∈ Hon ∧ u ∈ S.P.committee s' ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s' ∧
        ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s') ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x.sent (i + 1) - x.sent i)
    -- at every member voting at slot `s' + 1`, the validators it counts are fewer than twice `Hs`
    (hVotersW : ∀ w ∈ Hon, ∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes M S.C (x.tickInput w (M.voteTime S.C (s' + 1))) (s' + 1) votes
        support_votes →
      M.voters_count votes < 2 * Hs.card)
    -- at every member voting at slot `s' + 1`, the root of its fork choice is compatible with `B`
    (hF2 : ∀ w ∈ Hon,
      (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s' + 1)))).fc_root.compatible B = true)
    -- at every member voting at slot `s' + 1`, when that root is `B` or an ancestor of `B`, a
    -- block of its voter tree on `B`'s chain is a viable head
    (hF3 : ∀ w ∈ Hon,
      (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s' + 1)))).fc_root.AncestorEq B →
      ∃ W, VoterTreeAt M (x.tickInput w (M.voteTime S.C (s' + 1)))
          (S.C.t_ ((s' + 1) - 1) + 3 * S.C.Δ) (s' + 1) W ∧
        W ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s' + 1)))).viable_heads ∧
        B.AncestorEq W) :
    -- then the first clause holds at slot `s' + 1`
    ∀ u ∈ Hon, ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (s' + 1)) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x.sent (i + 1) - x.sent i) →
      ∃ H_u ∈ (x.tickInput u (M.voteTime S.C (s' + 1))).tree,
        vote = GoldfishVote.mk u (s' + 1) H_u.root ∧ B.AncestorEq H_u :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem79a_honestChainExtends_votes_step M F U) S
    A x R GST s' Hon Hs B E hNet hSkew hRedeliver Sy hΔs hRoots hParent hOwner hGST hInv hHon hHonTick hHs
    hVotersW hF2 hF3

/-- **Lemma 79b, the second clause of the step.** In an execution where every time is reached:
when `HonestChainExtends M S Sched x Hon B s'` holds and every member of
`Hon` ticks to the vote time of slot `s' + 1`, active at every step up to that tick from the trace's start or from
its own tick to a clock value at most the duty window's start of slot `s' + 2`, then for every member `w` and every node state `n'` that `w`'s revocation of slot `s' + 2`
at its vote time may leave from `w`'s node state then, the block of every lock entry of `n'` live
then is compatible with `B`.

Why: every entry the revocation leaves is on the block of an entry of `w`'s state then, or an
ancestor of it, whose deadline is after that time (Lemma 38); that entry is compatible with `B`
(`live_locks_compatible_of_honestChainExtends_tick` at the vote time of slot `s' + 2`), and so is every
ancestor of its block.
The landed conclusion reads every answer of the landed revocation; the twin reads every node
state that revocation may leave (`LocksRevoked`, the shape of Lemma 42's twin), as its proof page's
twin does.
  it asks nothing
of a member after that tick.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `s'`: the slot of the invariant; `Hon`: the validators the invariant is read at; `B`: the block.

Read aloud: under the invariant at slot `s'`, the live locks the members' revocations of slot
`s' + 2` leave are compatible with `B`. -/
theorem lem79b_honestChainExtends_locks_step (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (s' : ℕ) (Hon : Finset V) (B : Block V)
    -- every time is reached
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    -- the slot invariant restricted to `B` holds at slot `s'`
    (hInv : HonestChainExtends M S A x Hon B s')
    -- every member of `Hon` ticks to the vote time of slot `s' + 1`, active at every step up to that tick from the
    -- trace's start or from its own tick to a clock value at most the duty window's start of slot `s' + 2`
    --
    (hHon : ∀ v ∈ Hon, v ∈ A.activeThroughoutToTick x ((M.dutyWindowStart S.C (s' + 2) : ℕ) : ℤ) (M.voteTime S.C (s' + 1))) :
    -- then the second clause holds at slot `s' + 1`
    ∀ w ∈ Hon, ∀ n' : M.N,
      LocksRevoked M S.P (x.tickInput w (M.voteTime S.C (s' + 2)))
        ((M.voteTime S.C (s' + 2) : ℕ) : Int) (s' + 2) n' →
      ∀ e ∈ M.lockEntries n',
        M.is_live (x.tickInput w (M.voteTime S.C (s' + 2)))
          ((M.voteTime S.C (s' + 2) : ℕ) : Int) e = true → e.B.compatible B = true :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem79b_honestChainExtends_locks_step M F U) S
    A x R s' Hon B E hInv hHon

open Classical in
/-- **Lemma 79c, the third clause of the step.** In an execution where every time is reached,
corruption is permanent, blocks and Goldfish votes are delivered within `Δ` after `GST`
(synchrony from the receiver's wake, and catch-up on wake), a root
names one block among what honest validators hold, a block reaches a validator only once it holds
the parent, and nobody votes in an honest validator's name: if `GST` is at most the vote time of
slot `s' + 1`; every slot-`(s' + 1)` vote a member of `Hon` put on the wire at its tick at the vote
time of slot `s' + 1` is its vote for a block it holds then that is `B` or a descendant of `B` (the
first clause at slot `s' + 1`, Lemma 79a's conclusion); the members of `Hon` are awake and honest
from the duty window's start of slot `s' + 2` to the support cutoff of slot `s' + 2`; every member
of `Hs` is a member of `Hon` and of the slot-`(s' + 1)` committee that put a slot-`(s' + 1)` vote on
the wire at its tick at the vote time of slot `s' + 1`; at every member `v`, the validators with a
slot-`(s' + 1)` vote in the pool of the state `v`'s tick to the support cutoff of slot `s' + 2`
starts from are fewer than twice `Hs`, and that state's finalized block is compatible with `B` — then every confirmation of slot
`s' + 1` a member holds right after the support cutoff of slot `s' + 2` is `B` or a descendant of
`B`.

Why: Lemma 78 at slot `s' + 1`, each member of `Hs` voting for a block it holds on `B`'s chain.


The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s'`: the slot of the invariant;
- `Hon`: the validators the invariant is read at; `Hs`: the honest voters of slot `s' + 1`;
- `B`: the block.

Read aloud: when the members' votes of slot `s' + 1` are on `B`'s chain, their confirmations of slot
`s' + 1` are too.

Roots name blocks up to every validator's tick to a clock value at most `M.supportCutoff S.C (s' + 1)`: Lemma 78,
which the proof calls at slot `s' + 1`, reads them at each member's own tick to that cutoff. -/
theorem lem79c_honestChainExtends_confirmations_step (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (GST s' : ℕ) (Hon : Finset V) (Hs : Finset V) (B : Block V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- roots name blocks up to every validator's tick to a clock value at most the support cutoff of slot `s' + 1`
    (hRoots : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (s' + 1) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C (s' + 1))
    -- every member's slot-`(s' + 1)` vote is for a block it holds on `B`'s chain
    (hVotes : ∀ u ∈ Hon, ∀ vote : GoldfishVote V,
      (∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (s' + 1)) ∧
        (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x.sent (i + 1) - x.sent i) →
      ∃ H_u ∈ (x.tickInput u (M.voteTime S.C (s' + 1))).tree,
        vote = GoldfishVote.mk u (s' + 1) H_u.root ∧ B.AncestorEq H_u)
    -- each member runs the update of slot `s' + 1`: it ticks to the support cutoff of slot `s' + 2`, active up to that
    -- tick from a tick at or before the duty window's start of slot `s' + 2`
    (hHon : ∀ v ∈ Hon, v ∈ updaterAt M S A x (s' + 1))
    -- no member is in the adversary set at a step where a validator outside it ticks to the support cutoff of
    -- slot `s' + 2` (, the second honesty read of)
    (hHonTick : ∀ u ∈ Hon, u ∉ Finset.univ.filter (fun u => ∃ (k : ℕ) (w : V),
      x.lbl k = Event.tick w (M.supportCutoff S.C (s' + 2)) ∧ w ∉ A.corrupted k ∧ u ∈ A.corrupted k))
    -- every member of `Hs` is a member of `Hon` and of the slot-`(s' + 1)` committee that sent a
    -- slot-`(s' + 1)` vote at the vote time of slot `s' + 1`
    (hHs : ∀ u ∈ Hs, u ∈ Hon ∧ u ∈ S.P.committee (s' + 1) ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s' + 1 ∧
        ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C (s' + 1)) ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x.sent (i + 1) - x.sent i)
    -- at every member, the slot-`(s' + 1)` voters of the pool its tick to the support cutoff of
    -- slot `s' + 2` starts from are fewer than twice `Hs`
    (hVotersV : ∀ v ∈ Hon,
      M.voters_count (M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (s' + 2))) (s' + 1)) <
        2 * Hs.card)
    -- at every member, its finalized block before that cutoff is compatible with `B`
    (hFv : ∀ v ∈ Hon,
      (x.tickInput v (M.supportCutoff S.C (s' + 2))).finalized.compatible B = true) :
    -- then the third clause holds at slot `s' + 1`
    ∀ v ∈ Hon, ∀ C' : Block V,
      (x.tickOutput v (M.supportCutoff S.C (s' + 2))).savedConfirmation (s' + 1) = some C' →
      B.AncestorEq C' :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem79c_honestChainExtends_confirmations_step M F U)
    S A x R GST s' Hon Hs B E hNet hSkew hRedeliver Sy hΔs hRoots hParent hOwner hGST hVotes hHon hHonTick hHs
    hVotersV hFv

open Classical in
/-- **Lemma 79, the step of the slot invariant restricted to a block.** In an execution where every
time is reached, corruption is permanent, blocks and Goldfish votes are delivered within `Δ` after
`GST` (synchrony from the receiver's wake, and catch-up on wake), a root
names one block among what honest validators hold, a block reaches a validator only once it holds
the parent, and nobody votes in an honest validator's name: if `GST` is at most the vote time of
slot `s'`; `HonestChainExtends M S Sched x Hon B s'` holds; the members of `Hon` are awake and
honest from the duty window's start of slot `s' + 1` to the support cutoff of slot `s' + 2`; for
each of the slots `s'` and `s' + 1`, every member of `Hs` of that slot is a member of `Hon` and of
that slot's committee that put a vote of that slot on the wire at its tick at that slot's vote time;
at every member `w` voting at slot `s' + 1`, on the state `w`'s tick to the vote time of slot
`s' + 1` starts from, the validators with a vote among those `w` counts are fewer than twice
`Hs s'`, the root of `w`'s fork choice is compatible with `B`, and, when that root is `B` or an
ancestor of `B`, some block of `w`'s voter tree on `B`'s chain is a viable head; and at every member
`v` running the update of slot `s' + 2`, on the state `v`'s tick to the support cutoff of slot
`s' + 2` starts from, the slot-`(s' + 1)` voters of `v`'s pool are fewer than twice `Hs (s' + 1)`,
and its finalized block is compatible with `B` — then `HonestChainExtends M S Sched x Hon B (s' + 1)` holds.



Why: the three clauses at slot `s' + 1` are Lemmas 79a, 79b and 79c; Lemma 79c reads Lemma 79a's
conclusion.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `Sched`: the schedule; `x`: the execution;
- `GST`: the time from which the network is synchronous; `s'`: the slot of the invariant;
- `Hon`: the validators the invariant is read at; `Hs`: the honest voters of each slot;
- `B`: the block.

Read aloud: the invariant at slot `s'` gives the invariant at slot `s' + 1`, when the members stay
awake and honest through the next slot, the honest voters of each slot are a majority of the voters
the members count, and the members' finalized blocks and fork-choice roots are compatible with `B`.

Roots name blocks up to every validator's tick to a clock value at most `M.supportCutoff S.C (s' + 1)`: Lemma 79c,
which the proof calls, reads them there; Lemma 79a reads them up to the support cutoff of slot `s'`. -/
theorem lem79_honestChainExtends_step (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (GST s' : ℕ) (Hon : Finset V) (Hs : ℕ → Finset V) (B : Block V)
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    -- roots name blocks up to every validator's tick to a clock value at most the support cutoff of slot `s' + 1`
    (hRoots : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.supportCutoff S.C (s' + 1) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    (hOwner : VotesCastByOwner M A x)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s')
    -- the slot invariant restricted to `B` holds at slot `s'`
    (hInv : HonestChainExtends M S A x Hon B s')
    -- the members of `Hon` are active at every real time from the duty window's start of slot `s' + 1` to its vote
    -- time (Lemma 79a's read), and each runs the update of slot `s' + 1`
    (hHon : ∀ v ∈ Hon, v ∈ A.activeThroughout x (M.dutyWindowStart S.C (s' + 1)) (M.voteTime S.C (s' + 1)))
    (hHonUpd : ∀ v ∈ Hon, v ∈ updaterAt M S A x (s' + 1))
    -- no member is in the adversary set at a step where a validator outside it ticks to the support cutoff of
    -- slot `s' + 2` (, the second honesty read of)
    (hHonTick : ∀ u ∈ Hon, u ∉ Finset.univ.filter (fun u => ∃ (k : ℕ) (w : V),
      x.lbl k = Event.tick w (M.supportCutoff S.C (s' + 2)) ∧ w ∉ A.corrupted k ∧ u ∈ A.corrupted k))
    -- the honest voters of slots `s'` and `s' + 1`, members of `Hon` and of the slot's committee
    -- that sent a vote of the slot at its vote time
    (hHs : ∀ s₀ : ℕ, s₀ = s' ∨ s₀ = s' + 1 → ∀ u ∈ Hs s₀, u ∈ Hon ∧ u ∈ S.P.committee s₀ ∧
      ∃ vote : GoldfishVote V, vote.val_index = u ∧ vote.slot = s₀ ∧
        ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s₀) ∧
          (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x.sent (i + 1) - x.sent i)
    -- the voter bound at every member voting at slot `s' + 1`
    (hVotersW : ∀ w ∈ Hon, ∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes M S.C (x.tickInput w (M.voteTime S.C (s' + 1))) (s' + 1) votes
        support_votes →
      M.voters_count votes < 2 * (Hs s').card)
    -- the voter bound at every member running the update of slot `s' + 2`
    (hVotersV : ∀ v ∈ Hon,
      M.voters_count (M.votesHeldSet (x.tickInput v (M.supportCutoff S.C (s' + 2))) (s' + 1)) <
        2 * (Hs (s' + 1)).card)
    -- at every member voting at slot `s' + 1`, the root of its fork choice is compatible with `B`
    (hF2 : ∀ w ∈ Hon,
      (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s' + 1)))).fc_root.compatible B = true)
    -- at every member voting at slot `s' + 1`, when that root is `B` or an ancestor of `B`, a
    -- block of its voter tree on `B`'s chain is a viable head
    (hF3 : ∀ w ∈ Hon,
      (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s' + 1)))).fc_root.AncestorEq B →
      ∃ W, VoterTreeAt M (x.tickInput w (M.voteTime S.C (s' + 1)))
          (S.C.t_ ((s' + 1) - 1) + 3 * S.C.Δ) (s' + 1) W ∧
        W ∈ (M.fg_to_ac (x.tickInput w (M.voteTime S.C (s' + 1)))).viable_heads ∧
        B.AncestorEq W)
    -- the finalized block of every member running the update of slot `s' + 2` is compatible
    -- with `B`
    (hFv : ∀ v ∈ Hon,
      (x.tickInput v (M.supportCutoff S.C (s' + 2))).finalized.compatible B = true) :
    -- then the slot invariant restricted to `B` holds at slot `s' + 1`
    HonestChainExtends M S A x Hon B (s' + 1) :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem79_honestChainExtends_step M F U) S A x R GST
    s' Hon Hs B E hNet hSkew hRedeliver Sy hΔs hRoots hParent hOwner hGST hInv hHon hHonUpd hHonTick hHs hVotersW hVotersV
    hF2 hF3 hFv

end GoldilocksCorrectness.Record.Statements.Executions

