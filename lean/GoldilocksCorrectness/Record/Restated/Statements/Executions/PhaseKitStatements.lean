module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.PhaseKit
public import GoldilocksCorrectness.Statements.Executions.PhaseKitStatements
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# PhaseKitStatements, over a model

The statements of `GoldilocksCorrectness/Statements/Executions/PhaseKitStatements.lean`, over a
model `M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: the kit of the phase, an
honest Goldfish vote names a block on the chain of its voter's fork-choice root, the only slot-`s`
block an honest validator holds is the honest proposer's, every frame of a node state has a viable
head, a lock at the justified height of a state in box 2 is on its justified block, the counting
hypotheses of a round from a committee majority, and the
restrictions of the round's members and of the chain invariant. Each is the theorem of the same name
of `Record/Restated/Proofs/Executions/PhaseKit.lean`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff dutyWindowStart)

namespace GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (hMax)
open GoldilocksCorrectness.Record.Statements.Routines (BoxTwo ChainStatesComputed CountedVotes
  HeightCacheBounds)
open GoldilocksCorrectness.Statements.Executions (Vocab.goldilocks acObject author)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- **An honest vote extends its voter's root.** A Goldfish vote that `u`'s tick put on the wire
at the vote time of slot `s'` names the root of a block `H_u` that `u` holds before that time, and
`u`'s fork-choice root then is `H_u` or an ancestor of it.

Why: the vote names the end of the Goldfish fork choice from the anchor (Lemma 14); the end is the
anchor or a block of the viable tree of the voter's tree, and the anchor is the fork-choice root
or a descendant of it.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s'`: the slot; `u`: the voter;
  `vote`: the vote.



Read aloud: an honest Goldfish vote names a block its voter holds, on the chain of the voter's own
fork-choice root. -/
theorem vote_extends_own_root (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (s' : ℕ) (u : V) (vote : GoldfishVote V)
    -- `u` put `vote` on the wire at its tick at the vote time of slot `s'`
    (hSend : ∃ i : ℕ, x.lbl i = Event.tick u (M.voteTime S.C s') ∧
      (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) :
    ∃ H_u ∈ (x.tickInput u (M.voteTime S.C s')).tree, vote.head = H_u.root ∧
      (M.get_fc_root (x.tickInput u (M.voteTime S.C s'))).AncestorEq H_u :=
  (GoldilocksCorrectness.Record.Proofs.Executions.vote_extends_own_root M F) S A x R E s' u vote
    hSend

/-- **The only block of a slot.** Under unforgeability, when `p` is the proposer of slot `s`,
honest at every time up to `t`, and its tick at the start of slot `s` put `B` on the wire, every
block of slot `s` that a validator `w` holds before `t` is `B`.

Why: `w` relayed the block, which names `p` as its proposer; unforgeability puts it on the wire
under `p`'s own signature, sent by `p`'s own tick, which sends a block only at the start of the
block's slot (Lemma 19); one tick runs at that time, and it sends one block.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `hU`: unforgeability; `s`: the slot;
  `t`: the time; `B`: the proposal; `B₁`: the held block; `p`: the proposer; `w`: the holder.



Read aloud: the only slot-`s` block a validator holds before `t` is the honest proposer's. -/
theorem only_block_of_unforgeability (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (s t : ℕ) (B B₁ : Block V)
    (p w : V)
    -- `p` is outside the adversary set at every time up to `t`
    (hp : A.HonestThroughTime x t p) (hps : S.P.proposer s = p)
    -- `p`'s tick at the start of slot `s` put `B` on the wire
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p (M.slotStart S.C s) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    -- `w` holds `B₁` before `t`, and `B₁` is of slot `s`
    (hB₁ : B₁ ∈ (x.stateBefore t w).tree) (hslot : B₁.slot = s) :
    B₁ = B :=
  (GoldilocksCorrectness.Record.Proofs.Executions.only_block_of_unforgeability M F U) S A x R E s
    t B B₁ p w hp hps hPropose hB₁ hslot

/-- **Every frame has a viable head.** The frame `v`'s node state before `t` gives the available
chain has a viable head.

Why: in box 3 the block that makes the state contested is one; in box 2 the justified block is one;
otherwise a block on the finalized block's chain at a chain-state height at least the greatest
chain-state height minus one is one, and the finality update keeps such a block at every step.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t`: the time; `v`: the validator.



Read aloud: every frame of a node state has a viable head. -/
theorem frame_has_viable_head (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (t : ℕ) (v : V) :
    ∃ W : Block V, W ∈ (M.fg_to_ac (x.stateBefore t v)).viable_heads :=
  (GoldilocksCorrectness.Record.Proofs.Executions.frame_has_viable_head M F) S A x R E t v

/-- **The locks in box 2.** Under unforgeability, and when fewer than a third of the validators
have been in the adversary set up to `t`: when `p`'s node state before `t` is in box 2 with the
justified block `J₀`, every lock `T'` that `v`'s record holds before `t` at `p`'s greatest
chain-state height minus one is `J₀`'s root.

Why: the lock was written by an attestation of `v`'s tick whose finality pair is the justification
of a block `v` held, at that height; `p`'s justified block is the justification of a block `p`
holds, at the same height; two justification certificates at one height name one root (Lemma 76).

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `hU`: unforgeability; `t`: the time;
  `v`: the validator whose record is read; `p`: the validator in box 2; `J₀`: its justified block;
  `T'`: the lock.



Read aloud: in box 2 at the justified height, every lock is on the justified block. -/
theorem lockBox_of_one_justification (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (t : ℕ) (v p : V)
    (J₀ : Block V) (T' : BlockId)
    -- fewer than a third of the validators have been in the adversary set up to `t`
    (hAdv : A.AdversaryFewerThanThirdUntil x (validator_count V) t)
    (hBox : BoxTwo M S.C (x.stateBefore t p) J₀)
    -- `v`'s record before `t` holds the lock `T'` at `p`'s greatest chain-state height minus one
    (hLock : (x.stateBefore t v).sentLock (hMax M S.C (x.stateBefore t p) - 1) = some T') :
    T' = J₀.root :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lockBox_of_one_justification M F Fx) S A x R E
    t v p J₀ T' hAdv hBox hLock

/-- **The counting hypotheses from a committee majority in `Hon`.** When more than half of the
committee of slot `s` is in `Hon`, the committee has at most twice its members in `Hon`, the
validators with a slot-`s` vote in any node state's pool are fewer than twice them, and so are the
validators of any set of slot-`s` votes a slot-`(s + 1)` vote counts. Lemma 88
(`lem88_counting_of_committeeSleepiness`, `Statements/Executions/SleepyStatements.lean`) is this
fact with the honest active validators of slot `s` for `Hon` and the majority from committee
sleepiness; its page is not edited.

Why: the pool's votes and the counted votes are from the committee of slot `s`.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s`: the slot; `t`: the time;
  `Hon`: the validators; `v`: the validator whose state is read.



Read aloud: a committee majority in `Hon` bounds the committee, the pool and the counted votes of
the slot by twice the committee's members in `Hon`. -/
theorem counting_of_committee_majority (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (s t : ℕ) (Hon : Finset V) (v : V)
    -- more than half of the committee of slot `s` is in `Hon`
    (hMaj : (S.P.committee s).card < 2 * (S.P.committee s ∩ Hon).card) :
    (S.P.committee s).card ≤ 2 * (S.P.committee s ∩ Hon).card ∧
    M.voters_count (M.votesHeldSet (x.stateBefore t v) s) < 2 * (S.P.committee s ∩ Hon).card ∧
    (∀ votes support_votes : Finset (GoldfishVote V),
      CountedVotes M S.C (x.stateBefore t v) (s + 1)
        votes support_votes →
      M.voters_count votes < 2 * (S.P.committee s ∩ Hon).card) :=
  (GoldilocksCorrectness.Record.Proofs.Executions.counting_of_committee_majority M F) S A x R E s t
    Hon v hMaj

/-- **The round's members shrink.** With permanent corruption, a later round's members are among
an earlier round's, and the validators honest at `tAwakeEnd` are among the members of a round
whose next honest round opening slot's support cutoff is at most `tAwakeEnd`.

Why: the members are read at the support cutoff of the next opening's slot, and a validator in the
adversary set stays in it.

The variables:
- `M`: the model; `F`: its facts;
- `S`: the setup; `Sched`: the schedule; `s'' ≤ s'''`: the two slots; `tAwakeEnd`: the time.
- `R`: the run's facts (the time moves by at most one per step and never back).



Read aloud: a later round's members are among an earlier round's, and the phase set is among every
round's. -/
theorem roundMembers_mono (S : Setup V) (A : Activity V) (s'' s''' tAwakeEnd : ℕ)
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (h : s'' ≤ s''')
    -- the support cutoff of the later slot is at most `tAwakeEnd`
    (hEnd : M.supportCutoff S.C s''' ≤ tAwakeEnd) :
    roundMembers M S A x s''' ⊆ roundMembers M S A x s'' ∧
      Finset.univ \ A.corruptedAtTime x tAwakeEnd ⊆ roundMembers M S A x s''' :=
  (GoldilocksCorrectness.Record.Proofs.Executions.roundMembers_mono M F) S A s'' s''' tAwakeEnd
    R E h hEnd

/-- **The chain invariant restricts.** `ChainInvFor` at a set of members holds at every subset of
it.

Why: each clause is a statement about each member.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `Hon' ⊆ Hon M`: the two sets;
  `𝓒`: the family; `s'`: the slot.



Read aloud: the chain invariant restricts to a subset of the members. -/
theorem chainInvFor_mono (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (Hon Hon' : Finset V) (𝓒 : Block V → Prop) (s' : ℕ)
    -- `Hon'` is a subset of `Hon`
    (hSub : Hon' ⊆ Hon) (hInv : ChainInvFor M S A x Hon 𝓒 s') :
    ChainInvFor M S A x Hon' 𝓒 s' :=
  (GoldilocksCorrectness.Record.Proofs.Executions.chainInvFor_mono M F) S A x Hon Hon' 𝓒 s' hSub
    hInv

/-- **`HonestChainExtends` restricts.** `HonestChainExtends` at a set of members holds at every
subset of it.

Why: each clause is a statement about each member.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `Hon' ⊆ Hon M`: the two sets;
  `B`: the block; `s'`: the slot.



Read aloud: `HonestChainExtends` restricts to a subset of the members. -/
theorem honestChainExtends_mono (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (Hon Hon' : Finset V) (B : Block V) (s' : ℕ)
    -- `Hon'` is a subset of `Hon`
    (hSub : Hon' ⊆ Hon) (hInv : HonestChainExtends M S A x Hon B s') :
    HonestChainExtends M S A x Hon' B s' :=
  (GoldilocksCorrectness.Record.Proofs.Executions.honestChainExtends_mono M F) S A x Hon Hon' B
    s' hSub hInv

omit [RootOrder] in
/-- **The committee majority from committee sleepiness.** When committee sleepiness holds from
`anchor` and slot `s + 1` starts at or after `anchor`, more than half of the committee of slot `s`
is among the validators honest at the support cutoff of slot `s + 1`, the members
`roundMembers M S Sched (s + 1)`. This is the hypothesis `hMaj` of `counting_of_committee_majority`
with `Hon M := roundMembers M S Sched (s + 1)`: the one committee premise gives, at every slot it
constrains, the counting of that slot inside the slot's member set.

Why: committee sleepiness at slot `s + 1` makes the members of the committee of slot `s` in
`honestActiveAt M S Sched s` more than the rest of that committee, so more than half of it; and
`honestActiveAt M S Sched s` is inside `roundMembers M S Sched (s + 1)`, both being outside the
adversary set at the support cutoff of slot `s + 1`.

The variables:
- `M`: the model; `F`: its facts;
- `S`: the setup; `Sched`: the schedule; `anchor`: the time from which committee sleepiness
  holds; `s`: the slot; `T`: the time up to which committee sleepiness is read.



Read aloud: from committee sleepiness, the committee of slot `s` has a majority among the
validators honest at the update of slot `s`. -/
theorem committee_majority_of_committeeSleepiness (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)
    (anchor s : ℕ) {T : ℕ} (hSleepK : CommitteeSleepinessUntil M S A x anchor T)
    -- slot `s + 1` starts at or after `anchor`
    (hs : anchor ≤ M.slotStart S.C (s + 1))
    -- the update of slot `s` is at most `T`
    (hT : M.supportCutoff S.C (s + 1) ≤ T) :
    (S.P.committee s).card < 2 * (S.P.committee s ∩ roundMembers M S A x (s + 1)).card :=
  (GoldilocksCorrectness.Record.Proofs.Executions.committee_majority_of_committeeSleepiness M F) S
    A x anchor s hSleepK hs hT

/-- **The members of a slot are honest active.** In the phase, at a slot `s` whose duty window
starts at or after `tGAT` and whose update runs by `tAwakeEnd`, every validator honest at the
support cutoff of slot `s + 1` is in `honestActiveAt M S Sched s`, and every validator honest at the
support cutoff of slot `s + 2` is honest at the support cutoff of slot `s + 1`.

Why: the first inclusion is the phase premise `hActive` at slot `s`; a validator in the
adversary set after a step whose time is at most the support cutoff of slot `s + 1` is in it after a
step whose time is at most the later support cutoff of slot `s + 2`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`: the setup; `Sched`: the schedule; `tGAT`, `tAwakeEnd`: the ends of the interval in which
  every honest validator is awake; `s`: the slot.
- `R`: the run's facts (the time moves by at most one per step and never back).



Read aloud: in the phase, every validator honest at the slot's update is awake through the slot's
duties and honest at its update, and the next slot's members are among this slot's. -/
theorem roundMembers_subset_honestActiveAt (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (tGAT tAwakeEnd s : ℕ)
    {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    -- at every slot of the phase, every validator honest at the slot's update is an honest active validator and an
    -- updater of the slot
    (hActive : ∀ s : ℕ, tGAT ≤ M.dutyWindowStart S.C s → M.supportCutoff S.C (s + 1) ≤ tAwakeEnd →
      ∀ v : V, v ∉ A.corruptedAtTime x (M.supportCutoff S.C (s + 1)) →
        v ∈ honestActiveAt M S A x s ∧ v ∈ updaterAt M S A x s)
    -- the duty window of slot `s` starts at or after `tGAT`
    (hsw : tGAT ≤ M.dutyWindowStart S.C s)
    -- the support cutoff of slot `s + 1` is at most `tAwakeEnd`
    (hEnd : M.supportCutoff S.C (s + 1) ≤ tAwakeEnd) :
    roundMembers M S A x (s + 1) ⊆ honestActiveAt M S A x s ∧
    roundMembers M S A x (s + 2) ⊆ roundMembers M S A x (s + 1) :=
  (GoldilocksCorrectness.Record.Proofs.Executions.roundMembers_subset_honestActiveAt M F U) S A
    tGAT tAwakeEnd s R E hActive hsw hEnd

end GoldilocksCorrectness.Record.Statements.Executions

