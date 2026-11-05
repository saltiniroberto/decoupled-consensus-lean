module
public import GoldilocksCorrectness.Proofs.Executions.Lemma96
public import GoldilocksCorrectness.Proofs.Executions.Lemma107
public import GoldilocksCorrectness.Proofs.Executions.Lemma94Pair
public import GoldilocksCorrectness.Proofs.Executions.Lemma95Pair
public import GoldilocksCorrectness.Proofs.Executions.Lemma97

@[expose] public section

/-!
# Finality liveness after healing: the round steps

The audited statements of the round steps of finality liveness after healing
, proved in
`GoldilocksCorrectness/Proofs/Executions/Lemma94.lean`, `Lemma95.lean` and `Lemma96.lean`:

- `round_attesters_target_after_healing`, the part of Lemma 94 that holds: every honest active
  validator of an honest round opening slot after the hand-over puts on the wire, by the round's
  action time, a target at the proposal's height naming the root of its `T_h`;
- `consecutive_openings_height_step`, the first two conjuncts of Lemma 95: for two consecutive
  honest round opening slots, the first with a quorum of honest active validators, the second
  proposal descends from the first and is at a greater height;
- Lemma 96, `lem96_consecutive_openings_justified`: for three consecutive honest round opening
  slots, the first two with a quorum of honest active validators, and the timeout at least two
  rounds less one slot, the third proposal's justification height is at least the second
  proposal's height;
- Lemma 107, `lem107_honest_attestations_at_most_opening_height`: for an honest round opening slot
  after the hand-over, every attestation an honest awake validator put on the wire at a tick
  before the action time of the next round has height at most the proposal's height;
- Lemma 94, `lem94_round_attesters_after_healing`: with every honest attestation sent before the
  round's action time at a height at most `h_j(B)` (`hOldJ`) and `H < h_j(B)` (`hHJ`), every honest
  active validator of the honest round opening slot puts on the wire, at the action time itself, a
  target at the proposal's height that carries the finality pair `(h_j(B), J(B))` when
  `h_F(B) < h_j(B)`;
- Lemma 95, `lem95_consecutive_openings_step`: the hypotheses of `consecutive_openings_height_step`
  with `hOldJ` and `hHJ` for the first proposal `B`; its two conjuncts, and the third,
  `h_j(B) ≤ h_F(B')`: the second proposal finalizes at least the first proposal's justification
  height;
- three facts the composition reads, proved on this page: `two_R_le_δt_succ_of_seq`, the timeout
  condition `2R ≤ δt + 1` from the phase's spacing clause; `eight_le_m_of_openings`, the phase has
  at least nine honest round opening slots; `oldAttestationsAtMost_mono`, a bound on the old honest
  attestations can be raised;
- Lemma 97, `lem97_reader_finalized`: for an honest proposal `D` of an honest round opening slot
  after the hand-over, whose slot's support cutoff is at most the reading time `T`, every
  validator honest through a step at a time at most `T` and awake for one whole delay between the
  proposal's slot start and that step has `D`'s finalized block, or a descendant of it, as its
  finalized block (proved in `Lemma97.lean`).

Lemma 94 as probed (`scratch/goldilocks_fl/probe_fl_2.lean`, `lem94_round_attesters_after_healing_sig`)
has the clause on the finality pair without `hOldJ` and `hHJ`, and Lemma 95 as probed has the
third conjunct without them; The proofs of Lemmas 107, 94 and 95 are in
`Lemma107.lean`, `Lemma94Pair.lean` and `Lemma95Pair.lean`.

The definitions they read are in `FinalityLivenessDefs.lean`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC

open GoldilocksCorrectness.Statements.Routines (Δ Δ_F slotStart voteTime supportCutoff)

open GoldilocksCorrectness.Statements.Routines (chainStateOf)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **The round's attesters after healing: their targets (the part of Lemma 94 that holds).** In
an execution where every time is reached, corruption is permanent, blocks and Goldfish votes are
delivered within `Δ` after `GST` (synchrony from the receiver's wake, and catch-up on wake), a root
names one block among what honest validators hold by the support cutoff of slot `s + 1`, a block
reaches a validator only once it holds the parent, and nobody votes in an honest validator's name;
under unforgeability, with fewer than a quorum of validators ever in the adversary set and committee
sleepiness from `anchor`, at or before `x[i₂].time`; with `GST` at most the vote time of slot `s₀`
and the support cutoff of slot `s₀ + 1` at or before `x[i₂].time`; with the updaters'
confirmations of the slots from `s₀` to `s` forming one chain, the chain invariant and the lock
invariant at every slot after `s₀` and at most `s`, the lock invariant at the healed slot `s₀`
itself, every honest attestation sent before the support cutoff of slot `s₀ + 1` of height at most
`H`, and the caches of every validator honest at a step at a time from `x[i₂].time` to the support
cutoff of slot `s + 1` on the honest chain with justification height greater than `H`: for the
round `r` whose first slot `s = r * R` starts after `x[i₂].time` and is an honest round opening slot
(`HonestOpenerAt S Sched s`), whose proposer's tick at the start of slot `s` put `B` on the wire,
with no block the proposer held before the start of slot `s` having `B`'s root, every member `u` of
`honestActiveAt S Sched s` put on the wire, at a tick at a time at most the support cutoff of slot
`s + 1`, a target of its own at the height of `B`'s chain state naming the root of `B`'s `T_h`.

Why: `u` updates slot `s + 1` saving `B` fast, with its fork-choice root on `B`'s chain, its
`head_height_floor` at most `B`'s height (Lemma 91 (d) and the certificate route), `B` in its tree
and its record at `B`'s height clean of a lock on another block (Lemma 83's justification form);
Lemma 61 then gives the attestation at the action time, or one already sent at that height naming
the same root; either is a target (`no_honest_timeout_after_healing` on the chain before slot
`s + 1`).

Read aloud: every honest active validator of an honest round opening slot after healing attests
for the proposal's height by the round's action time, with a target.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₂`: the hand-over step; `H`: the threshold;
- `r`: the round; `s`: its first slot; `B`: the proposal; `u`: the member.

 the probe's statement without its clause on
the finality pair (finding F1). The probe's `hTicks` is gone; `hChain` is read before
slot `s + 1`, `ht₀` is the non-strict form the inclusion takes. -/
theorem round_attesters_target_after_healing (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ anchor i₂ H r s : ℕ) (B : Block V) (u : V)
    -- every time is reached
    (hDiv : TimeDiverges x.toTrace)
    -- corruption is permanent
    (hMono : Sched.MonotoneCorruption)
    -- blocks and Goldfish votes are delivered within `Δ` after `GST`
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    -- a root names one block among what honest validators hold by the support cutoff of `s + 1`
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s + 1)))
    -- a block reaches a validator only once it holds the parent
    (hParent : ParentHeldAtDelivery S Sched x)
    -- nobody votes in an honest validator's name
    (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    -- fewer than a quorum of validators are ever in the adversary set
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    -- committee sleepiness from `anchor`, at or before the hand-over step's time
    (hSleepK : CommitteeSleepiness S Sched anchor) (hAnchor : anchor ≤ x[i₂].time)
    (hGST : GST ≤ voteTime S s₀) (ht₀ : supportCutoff S (s₀ + 1) ≤ x[i₂].time)
    -- the updaters' confirmations of the slots from `s₀` to `s` form one chain
    (hChain : ConfirmationsChainBefore S Sched x s₀ (s + 1))
    -- the chain invariant and the lock invariant at the slots after `s₀` and at most `s`
    (hInv : ∀ s' : ℕ, s₀ < s' → s' ≤ s →
      ChainInvFor S Sched x (honestActiveAt S Sched s') (OnHonestChainBefore S Sched x s₀ s') s')
    (hLocks : ∀ s' : ℕ, s₀ < s' → s' ≤ s → ∀ w ∈ honestActiveAt S Sched s',
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ s') s' w)
    -- the lock invariant at the healed slot itself
    (hLocks₀ : ∀ w ∈ honestActiveAt S Sched s₀,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ (s₀ + 1)) s₀ w)
    -- every honest attestation sent before the support cutoff of `s₀ + 1` has height at most `H`
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    -- the caches of the honest validators from the hand-over to the support cutoff of `s + 1`
    (hCaches : ∀ (j : ℕ) (w : V), x[i₂].time ≤ x[j].time → x[j].time ≤ supportCutoff S (s + 1) →
      w ∉ Sched.adv (x[j].time : Int) → CachesOnChain S Sched x s₀ H (x[j][w].st))
    -- `s` is the first slot of round `r`, starting after the hand-over step's time
    (hs : s = r * S.C.R) (hAfter : x[i₂].time < slotStart S s)
    -- `s` is an honest round opening slot
    (hOpener : HonestOpenerAt S Sched s)
    -- the proposer's tick at the start of `s` put `B` on the wire
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s) ∧
      (⟨S.P.proposer s, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent)
    -- no block the proposer held before the start of `s` has `B`'s root
    (hNoCollision : ¬ RootCollisionAtProposal S Sched x s B)
    -- `u` is an honest active validator of `s`
    (hu : u ∈ honestActiveAt S Sched s) :
    ∃ (i t : ℕ) (a : Attestation V), x.lbl i = AtomicAction.tickAllAwake t ∧
      t ≤ supportCutoff S (s + 1) ∧
      (⟨u, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent ∧
      a.val_index = u ∧ a.h = (chainStateOf S.C B).h ∧ a.T = (chainStateOf S.C B).T_h.root ∧
      a.τ = false :=
  GoldilocksCorrectness.Proofs.Executions.round_attesters_target_after_healing S Sched x GST s₀
    anchor i₂ H r s B u hDiv hMono hSync hCatch hRoots hParent hOwner hU hAdvQ hSleepK hAnchor hGST
    ht₀ hChain hInv hLocks hLocks₀ hOld hCaches hs hAfter hOpener hPropose hNoCollision hu

/-- **Two consecutive honest round opening slots after healing: the height step (Lemma 95, its
first two conjuncts).** In an execution where every time is reached, corruption is permanent,
blocks and Goldfish votes are delivered within `Δ` after `GST` and attestations within `Δ_F`
(synchrony from the receiver's wake, and catch-up on wake), a root names one block among what
honest validators hold by the vote time of slot `(r + 1) * R`, a block reaches a validator only once
it holds the parent, and nobody votes in an honest validator's name; under unforgeability, with
fewer than a quorum of validators ever in the adversary set and committee sleepiness from `anchor`,
at or before `x[i₂].time`; with `GST` at most the vote time of slot `s₀` and the support cutoff of
slot `s₀ + 1` at or before `x[i₂].time`; with the updaters' confirmations of the slots from `s₀` to
before `(r + 1) * R − 1` forming one chain, the chain invariant and the lock invariant at every slot
after `s₀` and at most `(r + 1) * R − 1`, the lock invariant at the healed slot `s₀` itself, every
honest attestation sent before the support cutoff of slot `s₀ + 1` of height at most `H`, and the
caches of every validator honest at a step at a time from `x[i₂].time` to the vote time of slot
`(r + 1) * R` on the honest chain with justification height greater than `H`; with
`Δ_F + Δ ≤ 4Δ(k + 1)`: for the rounds `r` and `r + 1` whose first slots are honest round
opening slots, the first starting after `x[i₂].time` and with a quorum of honest active validators
(`QuorumActiveAt`), whose proposers' ticks at their starts put `B` and `B'` on the wire, with no
block either proposer held before its slot's start having its proposal's root: `B` is `B'` or an
ancestor of `B'`, and `B'`'s chain-state height is at least `B`'s plus one.

Why: `B'`'s parent extends the chain before slot `(r + 1) * R − 1`, which holds `B`; when the
parent is at `B`'s height, the quorum's targets at that height naming `T_h(B)`'s root reach the
proposer of `(r + 1) * R` by its slot's start (the parameter condition covers a proposer that woke
after the round's action time), and Lemma 53 puts `B'` at the next height.

Read aloud: the next honest round opening slot extends the previous one's proposal and raises the
height.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₂`: the hand-over step; `H`: the threshold;
- `r`: the first round; `B`, `B'`: the two proposals.

 the probe's statement without its third
conjunct (finding F1). The probe's `hTicks` is gone; `hChain`, `hInv` and `hLocks` are
read before slot `(r + 1) * R − 1`, `ht₀` is the non-strict form the inclusion takes. -/
theorem consecutive_openings_height_step (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ anchor i₂ H r : ℕ) (B B' : Block V)
    -- every time is reached
    (hDiv : TimeDiverges x.toTrace)
    -- corruption is permanent
    (hMono : Sched.MonotoneCorruption)
    -- blocks and Goldfish votes are delivered within `Δ` after `GST`
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    -- attestations are delivered within `Δ_F` after `GST`
    (hSyncF : SynchronyFromWake Sched x.toTrace (Δ_F S) GST fgObject)
    (hCatchF : CatchUpOnWake Sched x.toTrace (Δ_F S) GST fgObject)
    -- a root names one block among what honest validators hold by the vote time of `(r + 1) R`
    (hRoots : RootsNameBlocksUntil S Sched x (voteTime S ((r + 1) * S.C.R)))
    -- a block reaches a validator only once it holds the parent
    (hParent : ParentHeldAtDelivery S Sched x)
    -- nobody votes in an honest validator's name
    (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    -- fewer than a quorum of validators are ever in the adversary set
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    -- committee sleepiness from `anchor`, at or before the hand-over step's time
    (hSleepK : CommitteeSleepiness S Sched anchor) (hAnchor : anchor ≤ x[i₂].time)
    (hGST : GST ≤ voteTime S s₀) (ht₀ : supportCutoff S (s₀ + 1) ≤ x[i₂].time)
    -- the updaters' confirmations of the slots from `s₀` to before `(r + 1) R − 1` form one chain
    (hChain : ConfirmationsChainBefore S Sched x s₀ ((r + 1) * S.C.R - 1))
    -- the chain invariant and the lock invariant at the slots after `s₀`, at most `(r + 1) R − 1`
    (hInv : ∀ s' : ℕ, s₀ < s' → s' ≤ (r + 1) * S.C.R - 1 →
      ChainInvFor S Sched x (honestActiveAt S Sched s') (OnHonestChainBefore S Sched x s₀ s') s')
    (hLocks : ∀ s' : ℕ, s₀ < s' → s' ≤ (r + 1) * S.C.R - 1 → ∀ w ∈ honestActiveAt S Sched s',
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ s') s' w)
    -- the lock invariant at the healed slot itself
    (hLocks₀ : ∀ w ∈ honestActiveAt S Sched s₀,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ (s₀ + 1)) s₀ w)
    -- every honest attestation sent before the support cutoff of `s₀ + 1` has height at most `H`
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    -- the caches of the honest validators from the hand-over to the vote time of `(r + 1) R`
    (hCaches : ∀ (j : ℕ) (w : V), x[i₂].time ≤ x[j].time →
      x[j].time ≤ voteTime S ((r + 1) * S.C.R) →
      w ∉ Sched.adv (x[j].time : Int) → CachesOnChain S Sched x s₀ H (x[j][w].st))
    -- the attestations of a round reach a proposer that woke at its proposal window's start
    (hParam : Δ_F S + Δ S ≤ 4 * Δ S * (S.C.k + 1))
    -- the first slot of round `r` starts after the hand-over step's time
    (hAfter : x[i₂].time < slotStart S (r * S.C.R))
    -- the two first slots are honest round opening slots
    (hOpener : HonestOpenerAt S Sched (r * S.C.R))
    (hOpener' : HonestOpenerAt S Sched ((r + 1) * S.C.R))
    -- a quorum of honest active validators at the first
    (hQuorum : QuorumActiveAt S Sched (r * S.C.R))
    -- the two proposers' ticks put `B` and `B'` on the wire
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S (r * S.C.R)) ∧
      (⟨S.P.proposer (r * S.C.R), NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent)
    (hPropose' : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S ((r + 1) * S.C.R)) ∧
      (⟨S.P.proposer ((r + 1) * S.C.R), NamedObject.block B'⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent)
    -- no block either proposer held before its slot's start has its proposal's root
    (hNoCol : ¬ RootCollisionAtProposal S Sched x (r * S.C.R) B)
    (hNoCol' : ¬ RootCollisionAtProposal S Sched x ((r + 1) * S.C.R) B') :
    B.AncestorEq B' ∧ (chainStateOf S.C B).h + 1 ≤ (chainStateOf S.C B').h :=
  GoldilocksCorrectness.Proofs.Executions.consecutive_openings_height_step S Sched x GST s₀ anchor
    i₂ H r B B' hDiv hMono hSync hCatch hSyncF hCatchF hRoots hParent hOwner hU hAdvQ hSleepK
    hAnchor hGST ht₀ hChain hInv hLocks hLocks₀ hOld hCaches hParam hAfter hOpener hOpener'
    hQuorum hPropose hPropose' hNoCol hNoCol'

/-- **Lemma 96, three consecutive honest round opening slots justify the middle proposal's
height.** In an execution where every time is reached, corruption is permanent, blocks and
Goldfish votes are delivered within `Δ` after `GST` and attestations within `Δ_F` (synchrony from
the receiver's wake, and catch-up on wake), a root names one block among what honest validators
hold by the vote time of slot `(r + 1) * R`, a block reaches a validator only once it holds the
parent, and nobody votes in an honest validator's name; under unforgeability, with fewer than a
quorum of validators ever in the adversary set and committee sleepiness from `anchor`, at or before
`x[i₂].time`; with `GST` at most the vote time of slot `s₀` and the support cutoff of slot `s₀ + 1`
at or before `x[i₂].time`; with the updaters' confirmations of the slots from `s₀` to before
`(r + 1) * R − 1` forming one chain, the chain invariant and the lock invariant at every slot after
`s₀` and at most `(r + 1) * R − 1`, the lock invariant at the healed slot `s₀` itself, every honest
attestation sent before the support cutoff of slot `s₀ + 1` of height at most `H`, and the caches
of every validator honest at a step at a time from `x[i₂].time` to the vote time of slot
`(r + 1) * R` on the honest chain with justification height greater than `H`; with
`Δ_F + Δ ≤ 4Δ(k + 1)` and `2R ≤ δt + 1`: for the rounds `r − 1`, `r`, `r + 1`, with
`r ≥ 1`, whose first slots are honest round opening slots, the first starting after `x[i₂].time`,
the first two with a quorum of honest active validators (`QuorumActiveAt`), whose proposers' ticks
at their starts put `Bprev`, `B` and `B'` on the wire, with no block any of the three proposers held
before its slot's start having its proposal's root: the justification height of `B'`'s chain state
is at least the height of `B`'s.

Why: the height step at `r − 1`, `r` puts `B`'s entry `T_h(B)` strictly after `Bprev`, at a slot
after `(r − 1) R`. The block `Y` that takes `B'`'s chain past `h(B)` either justified `h(B)`, and the
justification height only rises along a chain, or passed the timeout test,
`T_h(B).slot + δt ≤ Y.slot ≤ (r + 1) R`; with `2R ≤ δt + 1` that leaves `Y = B'` with its parent at
`h(B)`, and then the quorum's targets make `B'` justify `T_h(B)` (Lemma 53), at the height `h(B)`.

Read aloud: with the timeout longer than two rounds less one slot, the next honest round opening
slot justifies the height the previous one's proposal reached.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₂`: the hand-over step; `H`: the threshold;
- `r`: the middle round; `Bprev`, `B`, `B'`: the proposals of the rounds `r − 1`, `r`, `r + 1`.

 The probe's `hTicks` is gone; `hChain`,
`hInv` and `hLocks` are read before slot `(r + 1) * R − 1`, `ht₀` is the non-strict form the
inclusion takes. -/
theorem lem96_consecutive_openings_justified (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ anchor i₂ H r : ℕ) (Bprev B B' : Block V)
    -- every time is reached
    (hDiv : TimeDiverges x.toTrace)
    -- corruption is permanent
    (hMono : Sched.MonotoneCorruption)
    -- blocks and Goldfish votes are delivered within `Δ` after `GST`
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    -- attestations are delivered within `Δ_F` after `GST`
    (hSyncF : SynchronyFromWake Sched x.toTrace (Δ_F S) GST fgObject)
    (hCatchF : CatchUpOnWake Sched x.toTrace (Δ_F S) GST fgObject)
    -- a root names one block among what honest validators hold by the vote time of `(r + 1) R`
    (hRoots : RootsNameBlocksUntil S Sched x (voteTime S ((r + 1) * S.C.R)))
    -- a block reaches a validator only once it holds the parent
    (hParent : ParentHeldAtDelivery S Sched x)
    -- nobody votes in an honest validator's name
    (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    -- fewer than a quorum of validators are ever in the adversary set
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    -- committee sleepiness from `anchor`, at or before the hand-over step's time
    (hSleepK : CommitteeSleepiness S Sched anchor) (hAnchor : anchor ≤ x[i₂].time)
    (hGST : GST ≤ voteTime S s₀) (ht₀ : supportCutoff S (s₀ + 1) ≤ x[i₂].time)
    -- the updaters' confirmations of the slots from `s₀` to before `(r + 1) R − 1` form one chain
    (hChain : ConfirmationsChainBefore S Sched x s₀ ((r + 1) * S.C.R - 1))
    -- the chain invariant and the lock invariant at the slots after `s₀`, at most `(r + 1) R − 1`
    (hInv : ∀ s' : ℕ, s₀ < s' → s' ≤ (r + 1) * S.C.R - 1 →
      ChainInvFor S Sched x (honestActiveAt S Sched s') (OnHonestChainBefore S Sched x s₀ s') s')
    (hLocks : ∀ s' : ℕ, s₀ < s' → s' ≤ (r + 1) * S.C.R - 1 → ∀ w ∈ honestActiveAt S Sched s',
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ s') s' w)
    -- the lock invariant at the healed slot itself
    (hLocks₀ : ∀ w ∈ honestActiveAt S Sched s₀,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ (s₀ + 1)) s₀ w)
    -- every honest attestation sent before the support cutoff of `s₀ + 1` has height at most `H`
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    -- the caches of the honest validators from the hand-over to the vote time of `(r + 1) R`
    (hCaches : ∀ (j : ℕ) (w : V), x[i₂].time ≤ x[j].time →
      x[j].time ≤ voteTime S ((r + 1) * S.C.R) →
      w ∉ Sched.adv (x[j].time : Int) → CachesOnChain S Sched x s₀ H (x[j][w].st))
    -- the attestations of a round reach a proposer that woke at its proposal window's start
    (hParam : Δ_F S + Δ S ≤ 4 * Δ S * (S.C.k + 1))
    -- the timeout is at least two rounds less one slot
    (hδt : 2 * S.C.R ≤ S.C.δt + 1)
    -- the middle round is not the first, and the first slot of round `r − 1` starts after the
    -- hand-over step's time
    (hr : 1 ≤ r) (hAfter : x[i₂].time < slotStart S ((r - 1) * S.C.R))
    -- the three first slots are honest round opening slots
    (hOpenerPrev : HonestOpenerAt S Sched ((r - 1) * S.C.R))
    (hOpener : HonestOpenerAt S Sched (r * S.C.R))
    (hOpener' : HonestOpenerAt S Sched ((r + 1) * S.C.R))
    -- a quorum of honest active validators at the first two
    (hQuorumPrev : QuorumActiveAt S Sched ((r - 1) * S.C.R))
    (hQuorum : QuorumActiveAt S Sched (r * S.C.R))
    -- the three proposers' ticks put `Bprev`, `B` and `B'` on the wire
    (hProposePrev : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S ((r - 1) * S.C.R)) ∧
      (⟨S.P.proposer ((r - 1) * S.C.R), NamedObject.block Bprev⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent)
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S (r * S.C.R)) ∧
      (⟨S.P.proposer (r * S.C.R), NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent)
    (hPropose' : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S ((r + 1) * S.C.R)) ∧
      (⟨S.P.proposer ((r + 1) * S.C.R), NamedObject.block B'⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent)
    -- no block any of the three proposers held before its slot's start has its proposal's root
    (hNoColPrev : ¬ RootCollisionAtProposal S Sched x ((r - 1) * S.C.R) Bprev)
    (hNoCol : ¬ RootCollisionAtProposal S Sched x (r * S.C.R) B)
    (hNoCol' : ¬ RootCollisionAtProposal S Sched x ((r + 1) * S.C.R) B') :
    (chainStateOf S.C B).h ≤ (chainStateOf S.C B').h_j :=
  GoldilocksCorrectness.Proofs.Executions.lem96_consecutive_openings_justified S Sched x GST s₀
    anchor i₂ H r Bprev B B' hDiv hMono hSync hCatch hSyncF hCatchF hRoots hParent hOwner hU hAdvQ
    hSleepK hAnchor hGST ht₀ hChain hInv hLocks hLocks₀ hOld hCaches hParam hδt hr hAfter
    hOpenerPrev hOpener hOpener' hQuorumPrev hQuorum hProposePrev hPropose hPropose' hNoColPrev
    hNoCol hNoCol'

/-- **Lemma 107, the honest attestations up to the next round's action time are at most the
opening proposal's height.** In an execution where every time is reached, corruption is permanent,
blocks and Goldfish votes are delivered within `Δ` after `GST` (synchrony from the receiver's wake,
and catch-up on wake), a root names one block among what honest validators hold by the support
cutoff of slot `s + 1`, a block reaches a validator only once it holds the parent, and nobody votes
in an honest validator's name; under unforgeability, with fewer than a quorum of validators ever in
the adversary set and committee sleepiness from `anchor`, at or before `x[i₂].time`; with `GST` at
most the vote time of slot `s₀` and the support cutoff of slot `s₀ + 1` at or before
`x[i₂].time`; with the updaters' confirmations of the slots from `s₀` to before `s` forming one
chain, the chain invariant and the lock invariant at every slot after `s₀` and at most `s`, the
lock invariant at the healed slot `s₀` itself, every honest attestation sent before the support
cutoff of slot `s₀ + 1` of height at most `H`, and the caches of every validator honest at a step
at a time from `x[i₂].time` to the support cutoff of slot `s + 1` on the honest chain with
justification height greater than `H`: for the round `r` whose first slot `s = r * R` starts after
`x[i₂].time` and is an honest round opening slot (`HonestOpenerAt S Sched s`), whose proposer's
tick at the start of slot `s` put `B` on the wire, with no block the proposer held before the start
of slot `s` having `B`'s root, every attestation an honest awake validator put on the wire at a
tick before the support cutoff of slot `(r + 1) * R + 1` (the action time of round `r + 1`) has
height at most the height of `B`'s chain state.

Why: an attestation sent before the support cutoff of slot `s₀ + 1` has height at most `H`, which
is less than `B`'s height. From then on, Lemma 82 sends it at the support cutoff of a slot
`s_a + 1`, a round's first slot (the time is a round's action time, Lemma 49) before
`(r + 1) * R`, so `s_a ≤ s`, and names an entry `E` of the honest chain at slot `s_a` at its height;
`E` is `B` or an ancestor of `B` (the chain before `s` ends at `B`, and an updater's confirmation
of `s` is `B`), so its height is at most `B`'s (Lemma 47 (d)).

Read aloud: up to the next round's attestations, no honest validator has attested at a height
greater than the proposal of an honest round opening slot.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₂`: the hand-over step; `H`: the threshold;
- `r`: the round; `s`: its first slot; `B`: the proposal.

 -/
theorem lem107_honest_attestations_at_most_opening_height (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ anchor i₂ H r s : ℕ) (B : Block V)
    -- every time is reached
    (hDiv : TimeDiverges x.toTrace)
    -- corruption is permanent
    (hMono : Sched.MonotoneCorruption)
    -- blocks and Goldfish votes are delivered within `Δ` after `GST`
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    -- a root names one block among what honest validators hold by the support cutoff of `s + 1`
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s + 1)))
    -- a block reaches a validator only once it holds the parent
    (hParent : ParentHeldAtDelivery S Sched x)
    -- nobody votes in an honest validator's name
    (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    -- fewer than a quorum of validators are ever in the adversary set
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    -- committee sleepiness from `anchor`, at or before the hand-over step's time
    (hSleepK : CommitteeSleepiness S Sched anchor) (hAnchor : anchor ≤ x[i₂].time)
    (hGST : GST ≤ voteTime S s₀) (ht₀ : supportCutoff S (s₀ + 1) ≤ x[i₂].time)
    -- the updaters' confirmations of the slots from `s₀` to before `s` form one chain
    (hChain : ConfirmationsChainBefore S Sched x s₀ s)
    -- the chain invariant and the lock invariant at the slots after `s₀` and at most `s`
    (hInv : ∀ s' : ℕ, s₀ < s' → s' ≤ s →
      ChainInvFor S Sched x (honestActiveAt S Sched s') (OnHonestChainBefore S Sched x s₀ s') s')
    (hLocks : ∀ s' : ℕ, s₀ < s' → s' ≤ s → ∀ w ∈ honestActiveAt S Sched s',
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ s') s' w)
    -- the lock invariant at the healed slot itself
    (hLocks₀ : ∀ w ∈ honestActiveAt S Sched s₀,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ (s₀ + 1)) s₀ w)
    -- every honest attestation sent before the support cutoff of `s₀ + 1` has height at most `H`
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    -- the caches of the honest validators from the hand-over to the support cutoff of `s + 1`
    (hCaches : ∀ (j : ℕ) (w : V), x[i₂].time ≤ x[j].time → x[j].time ≤ supportCutoff S (s + 1) →
      w ∉ Sched.adv (x[j].time : Int) → CachesOnChain S Sched x s₀ H (x[j][w].st))
    -- `s` is the first slot of round `r`, starting after the hand-over step's time
    (hs : s = r * S.C.R) (hAfter : x[i₂].time < slotStart S s)
    -- `s` is an honest round opening slot
    (hOpener : HonestOpenerAt S Sched s)
    -- the proposer's tick at the start of `s` put `B` on the wire
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s) ∧
      (⟨S.P.proposer s, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent)
    -- no block the proposer held before the start of `s` has `B`'s root
    (hNoCollision : ¬ RootCollisionAtProposal S Sched x s B) :
    OldAttestationsAtMost S Sched x (supportCutoff S ((r + 1) * S.C.R + 1))
      (chainStateOf S.C B).h :=
  GoldilocksCorrectness.Proofs.Executions.lem107_honest_attestations_at_most_opening_height S Sched
    x GST s₀ anchor i₂ H r s B hDiv hMono hSync hCatch hRoots hParent hOwner hU hAdvQ hSleepK
    hAnchor hGST ht₀ hChain hInv hLocks hLocks₀ hOld hCaches hs hAfter hOpener hPropose
    hNoCollision

/-- **Lemma 94, the round's attesters after healing carry the finality pair.** In an execution
where every time is reached, corruption is permanent, blocks and Goldfish votes are delivered within
`Δ` after `GST` (synchrony from the receiver's wake, and catch-up on wake), a root names one block
among what honest validators hold by the support cutoff of slot `s + 1`, a block reaches a validator
only once it holds the parent, and nobody votes in an honest validator's name; under
unforgeability, with fewer than a quorum of validators ever in the adversary set and committee
sleepiness from `anchor`, at or before `x[i₂].time`; with `GST` at most the vote time of slot `s₀`
and the support cutoff of slot `s₀ + 1` at or before `x[i₂].time`; with the updaters'
confirmations of the slots from `s₀` to `s` forming one chain, the chain invariant and the lock
invariant at every slot after `s₀` and at most `s`, the lock invariant at the healed slot `s₀`
itself, every honest attestation sent before the support cutoff of slot `s₀ + 1` of height at most
`H`, and the caches of every validator honest at a step at a time from `x[i₂].time` to the support
cutoff of slot `s + 1` on the honest chain with justification height greater than `H`: for the
round `r` whose first slot `s = r * R` starts after `x[i₂].time` and is an honest round opening slot
(`HonestOpenerAt S Sched s`), whose proposer's tick at the start of slot `s` put `B` on the wire,
with no block the proposer held before the start of slot `s` having `B`'s root; when every
attestation an honest awake validator put on the wire at a tick before the support cutoff of slot
`s + 1` (the round's action time) has height at most the justification height of `B`'s chain state
(`hOldJ`), and `H` is less than that justification height (`hHJ`): every member `u` of
`honestActiveAt S Sched s` put on the wire, at its tick at the support cutoff of slot `s + 1`
itself, a target of its own at the height of `B`'s chain state naming the root of `B`'s `T_h`, which
carries the finality pair `(h_j(B), J(B))` (the justification height of `B`'s chain state and the
root of its justified block) when the finalization height of `B`'s chain state is less than its
justification height.

Why: `u`'s record holds nothing at `h(B)` (`hOldJ`, `h_j(B) < h(B)`), so its tick at the action
time builds a fresh target at `h(B)` from the head `D` the duty reads, `B` or a descendant of `B`
(Lemma 48b). A justification on `D`'s chain at a height greater than `h_j(B)`, or a finalization
at a height at least `h_j(B)`, would have an honest member whose attestation, sent before the action
time, has a height greater than `h_j(B)` (Lemma 66), against `hOldJ`: so `h_j(D) = h_j(B)`,
`h_F(D) < h_j(B)`, and `J(D) = J(B)`.
`u`'s record at `h_j(B) > H` holds no timeout, and no target or lock but `J(B)`'s root (Lemmas 82
and 83, the honest chain before `s` ending at `B`). Lemma 92 attaches the pair.

Read aloud: when no honest validator has attested above `B`'s justification height before the
round's action time, and that height is greater than the threshold, every honest active validator
of the honest round opening slot attests for `B`'s height at the action time, vouching for `B`'s
justification when it is not yet finalized.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₂`: the hand-over step; `H`: the threshold;
- `r`: the round; `s`: its first slot; `B`: the proposal; `u`: the member.

 -/
theorem lem94_round_attesters_after_healing (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ anchor i₂ H r s : ℕ) (B : Block V) (u : V)
    -- every time is reached
    (hDiv : TimeDiverges x.toTrace)
    -- corruption is permanent
    (hMono : Sched.MonotoneCorruption)
    -- blocks and Goldfish votes are delivered within `Δ` after `GST`
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    -- a root names one block among what honest validators hold by the support cutoff of `s + 1`
    (hRoots : RootsNameBlocksUntil S Sched x (supportCutoff S (s + 1)))
    -- a block reaches a validator only once it holds the parent
    (hParent : ParentHeldAtDelivery S Sched x)
    -- nobody votes in an honest validator's name
    (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    -- fewer than a quorum of validators are ever in the adversary set
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    -- committee sleepiness from `anchor`, at or before the hand-over step's time
    (hSleepK : CommitteeSleepiness S Sched anchor) (hAnchor : anchor ≤ x[i₂].time)
    (hGST : GST ≤ voteTime S s₀) (ht₀ : supportCutoff S (s₀ + 1) ≤ x[i₂].time)
    -- the updaters' confirmations of the slots from `s₀` to `s` form one chain
    (hChain : ConfirmationsChainBefore S Sched x s₀ (s + 1))
    -- the chain invariant and the lock invariant at the slots after `s₀` and at most `s`
    (hInv : ∀ s' : ℕ, s₀ < s' → s' ≤ s →
      ChainInvFor S Sched x (honestActiveAt S Sched s') (OnHonestChainBefore S Sched x s₀ s') s')
    (hLocks : ∀ s' : ℕ, s₀ < s' → s' ≤ s → ∀ w ∈ honestActiveAt S Sched s',
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ s') s' w)
    -- the lock invariant at the healed slot itself
    (hLocks₀ : ∀ w ∈ honestActiveAt S Sched s₀,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ (s₀ + 1)) s₀ w)
    -- every honest attestation sent before the support cutoff of `s₀ + 1` has height at most `H`
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    -- the caches of the honest validators from the hand-over to the support cutoff of `s + 1`
    (hCaches : ∀ (j : ℕ) (w : V), x[i₂].time ≤ x[j].time → x[j].time ≤ supportCutoff S (s + 1) →
      w ∉ Sched.adv (x[j].time : Int) → CachesOnChain S Sched x s₀ H (x[j][w].st))
    -- `s` is the first slot of round `r`, starting after the hand-over step's time
    (hs : s = r * S.C.R) (hAfter : x[i₂].time < slotStart S s)
    -- `s` is an honest round opening slot
    (hOpener : HonestOpenerAt S Sched s)
    -- the proposer's tick at the start of `s` put `B` on the wire
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s) ∧
      (⟨S.P.proposer s, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent)
    -- no block the proposer held before the start of `s` has `B`'s root
    (hNoCollision : ¬ RootCollisionAtProposal S Sched x s B)
    -- hOldJ: no honest attestation at a height greater than `h_j(B)` before the action time
    (hOldJ : OldAttestationsAtMost S Sched x (supportCutoff S (s + 1)) (chainStateOf S.C B).h_j)
    -- hHJ: `B`'s justification height is greater than the threshold
    (hHJ : H < (chainStateOf S.C B).h_j)
    -- `u` is an honest active validator of `s`
    (hu : u ∈ honestActiveAt S Sched s) :
    ∃ (i : ℕ) (a : Attestation V), x.lbl i = AtomicAction.tickAllAwake (supportCutoff S (s + 1)) ∧
      (⟨u, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent ∧
      a.val_index = u ∧ a.h = (chainStateOf S.C B).h ∧ a.T = (chainStateOf S.C B).T_h.root ∧
      a.τ = false ∧
      ((chainStateOf S.C B).h_F < (chainStateOf S.C B).h_j →
        a.finality_pair =
          some (FinalityPair.mk (chainStateOf S.C B).h_j (chainStateOf S.C B).J.root)) :=
  GoldilocksCorrectness.Proofs.Executions.lem94_round_attesters_after_healing S Sched x GST s₀
    anchor i₂ H r s B u hDiv hMono hSync hCatch hRoots hParent hOwner hU hAdvQ hSleepK hAnchor hGST
    ht₀ hChain hInv hLocks hLocks₀ hOld hCaches hs hAfter hOpener hPropose hNoCollision hOldJ hHJ
    hu

/-- **Lemma 95, two consecutive honest round opening slots after healing: the height step and the
finalization.** In an execution where every time is reached, corruption is permanent, blocks and
Goldfish votes are delivered within `Δ` after `GST` and attestations within `Δ_F` (synchrony from
the receiver's wake, and catch-up on wake), a root names one block among what honest validators
hold by the vote time of slot `(r + 1) * R`, a block reaches a validator only once it holds the
parent, and nobody votes in an honest validator's name; under unforgeability, with fewer than a
quorum of validators ever in the adversary set and committee sleepiness from `anchor`, at or before
`x[i₂].time`; with `GST` at most the vote time of slot `s₀` and the support cutoff of slot `s₀ + 1`
at or before `x[i₂].time`; with the updaters' confirmations of the slots from `s₀` to before
`(r + 1) * R − 1` forming one chain, the chain invariant and the lock invariant at every slot after
`s₀` and at most `(r + 1) * R − 1`, the lock invariant at the healed slot `s₀` itself, every honest
attestation sent before the support cutoff of slot `s₀ + 1` of height at most `H`, and the caches
of every validator honest at a step at a time from `x[i₂].time` to the vote time of slot
`(r + 1) * R` on the honest chain with justification height greater than `H`; with
`Δ_F + Δ ≤ 4Δ(k + 1)`: for the rounds `r` and `r + 1` whose first slots are honest round
opening slots, the first starting after `x[i₂].time` and with a quorum of honest active validators
(`QuorumActiveAt`), whose proposers' ticks at their starts put `B` and `B'` on the wire, with no
block either proposer held before its slot's start having its proposal's root; when every
attestation an honest awake validator put on the wire at a tick before the support cutoff of slot
`r * R + 1` (the action time of round `r`) has height at most the justification height of `B`'s
chain state (`hOldJ`), and `H` is less than that justification height (`hHJ`): `B` is `B'` or an
ancestor of `B'`, `B'`'s chain-state height is at least `B`'s plus one, and `B'`'s finalization
height is at least `B`'s justification height.

Why: the first two conjuncts are `consecutive_openings_height_step`'s. For the third, when
`h_F(B) < h_j(B)`: every member of the quorum sent at the action time of round `r` the target of
Lemma 94, carrying the pair `(h_j(B), J(B))`, and it reaches the proposer of `(r + 1) * R` before
its slot starts. Every justification on the chain from `B` to `B'`'s parent is at a height at most
`h(B)` (Lemma 107 at `r`, through the honest member of its certificate, Lemma 66), so the pair stays
pending there, with at most one pair after it (`K_W ≥ 2`), unless it is already finalized. A
member's attestation already on the parent's chain was counted for the pair; one not on it is
valid against the parent and included in `B'` (Lemma 52). Lemma 93 finalizes the pair at `B'`.

Read aloud: when no honest validator has attested above `B`'s justification height before round
`r`'s action time, and that height is greater than the threshold, the next honest round opening
slot extends the previous one's proposal, raises the height, and finalizes the previous proposal's
justification.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₂`: the hand-over step; `H`: the threshold;
- `r`: the first round; `B`, `B'`: the two proposals.

 -/
theorem lem95_consecutive_openings_step (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ anchor i₂ H r : ℕ) (B B' : Block V)
    -- every time is reached
    (hDiv : TimeDiverges x.toTrace)
    -- corruption is permanent
    (hMono : Sched.MonotoneCorruption)
    -- blocks and Goldfish votes are delivered within `Δ` after `GST`
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    -- attestations are delivered within `Δ_F` after `GST`
    (hSyncF : SynchronyFromWake Sched x.toTrace (Δ_F S) GST fgObject)
    (hCatchF : CatchUpOnWake Sched x.toTrace (Δ_F S) GST fgObject)
    -- a root names one block among what honest validators hold by the vote time of `(r + 1) R`
    (hRoots : RootsNameBlocksUntil S Sched x (voteTime S ((r + 1) * S.C.R)))
    -- a block reaches a validator only once it holds the parent
    (hParent : ParentHeldAtDelivery S Sched x)
    -- nobody votes in an honest validator's name
    (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    -- fewer than a quorum of validators are ever in the adversary set
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    -- committee sleepiness from `anchor`, at or before the hand-over step's time
    (hSleepK : CommitteeSleepiness S Sched anchor) (hAnchor : anchor ≤ x[i₂].time)
    (hGST : GST ≤ voteTime S s₀) (ht₀ : supportCutoff S (s₀ + 1) ≤ x[i₂].time)
    -- the updaters' confirmations of the slots from `s₀` to before `(r + 1) R − 1` form one chain
    (hChain : ConfirmationsChainBefore S Sched x s₀ ((r + 1) * S.C.R - 1))
    -- the chain invariant and the lock invariant at the slots after `s₀`, at most `(r + 1) R − 1`
    (hInv : ∀ s' : ℕ, s₀ < s' → s' ≤ (r + 1) * S.C.R - 1 →
      ChainInvFor S Sched x (honestActiveAt S Sched s') (OnHonestChainBefore S Sched x s₀ s') s')
    (hLocks : ∀ s' : ℕ, s₀ < s' → s' ≤ (r + 1) * S.C.R - 1 → ∀ w ∈ honestActiveAt S Sched s',
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ s') s' w)
    -- the lock invariant at the healed slot itself
    (hLocks₀ : ∀ w ∈ honestActiveAt S Sched s₀,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ (s₀ + 1)) s₀ w)
    -- every honest attestation sent before the support cutoff of `s₀ + 1` has height at most `H`
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    -- the caches of the honest validators from the hand-over to the vote time of `(r + 1) R`
    (hCaches : ∀ (j : ℕ) (w : V), x[i₂].time ≤ x[j].time →
      x[j].time ≤ voteTime S ((r + 1) * S.C.R) →
      w ∉ Sched.adv (x[j].time : Int) → CachesOnChain S Sched x s₀ H (x[j][w].st))
    -- the attestations of a round reach a proposer that woke at its proposal window's start
    (hParam : Δ_F S + Δ S ≤ 4 * Δ S * (S.C.k + 1))
    -- the first slot of round `r` starts after the hand-over step's time
    (hAfter : x[i₂].time < slotStart S (r * S.C.R))
    -- the two first slots are honest round opening slots
    (hOpener : HonestOpenerAt S Sched (r * S.C.R))
    (hOpener' : HonestOpenerAt S Sched ((r + 1) * S.C.R))
    -- a quorum of honest active validators at the first
    (hQuorum : QuorumActiveAt S Sched (r * S.C.R))
    -- the two proposers' ticks put `B` and `B'` on the wire
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S (r * S.C.R)) ∧
      (⟨S.P.proposer (r * S.C.R), NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent)
    (hPropose' : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S ((r + 1) * S.C.R)) ∧
      (⟨S.P.proposer ((r + 1) * S.C.R), NamedObject.block B'⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent)
    -- no block either proposer held before its slot's start has its proposal's root
    (hNoCol : ¬ RootCollisionAtProposal S Sched x (r * S.C.R) B)
    (hNoCol' : ¬ RootCollisionAtProposal S Sched x ((r + 1) * S.C.R) B')
    -- hOldJ: no honest attestation at a height greater than `h_j(B)` before round `r`'s action
    -- time
    (hOldJ : OldAttestationsAtMost S Sched x (supportCutoff S (r * S.C.R + 1))
      (chainStateOf S.C B).h_j)
    -- hHJ: `B`'s justification height is greater than the threshold
    (hHJ : H < (chainStateOf S.C B).h_j) :
    B.AncestorEq B' ∧ (chainStateOf S.C B).h + 1 ≤ (chainStateOf S.C B').h ∧
      (chainStateOf S.C B).h_j ≤ (chainStateOf S.C B').h_F :=
  GoldilocksCorrectness.Proofs.Executions.lem95_consecutive_openings_step S Sched x GST s₀ anchor
    i₂ H r B B' hDiv hMono hSync hCatch hSyncF hCatchF hRoots hParent hOwner hU hAdvQ hSleepK
    hAnchor hGST ht₀ hChain hInv hLocks hLocks₀ hOld hCaches hParam hAfter hOpener hOpener'
    hQuorum hPropose hPropose' hNoCol hNoCol' hOldJ hHJ

/-! ## Three facts the composition reads -/

omit [RootOrder] in
/-- **The timeout is at least two rounds less one slot, from the phase's spacing clause.** When the
honest round opening slots `r 0 < … < r m` of `HonestOpeningSeq` number at least three (`2 ≤ m`),
`2R ≤ δt + 1`.

Why: the spacing clause at `i = 0` gives `r 2 * R ≤ r 0 * R + δt + 1`, and the sequence is strictly
increasing, so `r 0 + 2 ≤ r 2`.

The variables:
- `S`, `Sched`: the setup, the schedule; `r`: the rounds of the honest round opening slots; `m`:
  the index of the last one; `tF`, `tL`: the times the sequence lies between.

Read aloud: the phase's spacing clause, at two consecutive rounds, is the timeout condition Lemma
96 reads; the finality statement derives it and does not take it.

 -/
theorem two_R_le_δt_succ_of_seq (S : Setup V) (Sched : Schedule V) (r : ℕ → ℕ)
    (m tF tL : ℕ)
    -- `r 0 < … < r m` are honest round opening slots between `tF` and `tL`
    (hSeq : HonestOpeningSeq S Sched r m tF tL)
    -- at least three of them
    (hm : 2 ≤ m) :
    2 * S.C.R ≤ S.C.δt + 1 := by
  have h01 : r 0 < r 1 := hSeq.mono 0 (by omega)
  have h12 : r 1 < r 2 := hSeq.mono 1 (by omega)
  have hsp : r 2 * S.C.R ≤ r 0 * S.C.R + S.C.δt + 1 := hSeq.spacing 0 hm
  have h2 : r 0 + 2 ≤ r 2 := by omega
  have hmul : r 0 * S.C.R + 2 * S.C.R ≤ r 2 * S.C.R := by
    rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ h2
  omega

omit [RootOrder] in
/-- **The phase has at least nine honest round opening slots.** The span premise of record,
`OpeningsOutsideWaitsAndWindows S r m`, asks nine of the honest round opening slots `r 0, …, r m`
outside every two spans of `δt` slots and five spans of `k + 2` slots; so `8 ≤ m`.

Why: at any choice of the spans, nine indices of `0, …, m` pass the filter, and the filter keeps at
most the `m + 1` indices.

The variables:
- `S`: the setup; `r`: the rounds of the honest round opening slots; `m`: the index of the last
  one.

Read aloud: nine honest round opening slots outside the spans are nine of the sequence's.

 -/
theorem eight_le_m_of_openings (S : Setup V) (r : ℕ → ℕ) (m : ℕ)
    -- nine honest round opening slots outside every two spans of `δt` slots and five spans of
    -- `k + 2` slots
    (hm : OpeningsOutsideWaitsAndWindows S r m) : 8 ≤ m := by
  have h := hm (fun _ : Fin 2 => 0) (fun _ : Fin 5 => 0)
  have h9 : 9 ≤ (Finset.range (m + 1)).card := le_trans h (Finset.card_filter_le _ _)
  rw [Finset.card_range] at h9
  omega

/-- **A bound on the old honest attestations can be raised.** When every attestation an honest
awake validator put on the wire at a tick before `t₀` has height at most `H`, and `H ≤ H'`, every
such attestation has height at most `H'`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `t₀`: the time before which the
  attestations are read; `H`, `H'`: the two bounds.

Read aloud: a bound on the heights of the honest attestations before `t₀` stays a bound when it is
raised.

 -/
theorem oldAttestationsAtMost_mono (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (t₀ H H' : ℕ)
    -- every honest attestation sent before `t₀` has height at most `H`
    (h : OldAttestationsAtMost S Sched x t₀ H)
    -- `H` is at most `H'`
    (hle : H ≤ H') :
    OldAttestationsAtMost S Sched x t₀ H' :=
  fun i t v a hl ht hA hH hs => le_trans (h i t v a hl ht hA hH hs) hle

/-! ## The reader -/

/-- **Lemma 97, the reader finalizes what an honest proposal's chain finalized.** In an execution
where every time is reached, corruption is permanent, blocks and Goldfish votes are delivered
within `Δ` after `GST` (synchrony from the receiver's wake, and catch-up on wake), a root names one
block among what honest validators hold by the reading time `T`, a block reaches a validator only
once it holds the parent, and nobody votes in an honest validator's name; under unforgeability,
with fewer than a quorum of validators ever in the adversary set and committee sleepiness from
`anchor`, at or before `x[i₂].time`; with `GST` at most the vote time of slot `s₀` and the support
cutoff of slot `s₀ + 1` at or before `x[i₂].time`; with, for every slot whose update is at most
`T`, the updaters' confirmations from `s₀` up to it forming one chain and the chain invariant and
the lock invariant at it, the lock invariant at the healed slot `s₀` itself, every honest
attestation sent before the support cutoff of slot `s₀ + 1` of height at most `H`, and the caches
of every validator honest at a step at a time from `x[i₂].time` to `T` on the honest chain with
justification height greater than `H`: for the honest round opening slot `s_D = r_D * R` starting
after `x[i₂].time`, whose support cutoff is at most `T`, whose proposer's tick at its start put
`D` on the wire, with no block the proposer held before that start having `D`'s root, and with `D`'s
height greater than `H`, every validator `v` honest through a step `j` at a time at most `T` and
awake for one whole delay between the start of slot `s_D` and the time of step `j` has, at step
`j`, `D`'s finalized block or a descendant of it as its finalized block.

Why: `D` is on the honest chain, so the honest justified blocks and the certificates' entries at
the rounds' first slots whose update ran by `T` are compatible with it. The reader receives `D`
within the delay it is awake for. When `D` enters its tree, its justified block is `F(D)` or a
descendant of it, or of a smaller justification height, and every block of its tree higher than
`D` descends from `F(D)` (a certificate at `D`'s height names the honest chain's entry there), so
the finality update moves its finalized block to `F(D)` if it was not already at or past it.

Read aloud: whoever is awake for a delay after an honest round opening slot's proposal has
finalized at least what that proposal's chain finalized.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₂`: the hand-over step; `H`: the threshold; `T`: the reading time;
- `r_D`, `s_D`: the round and its first slot; `D`: the proposal; `j`: the reader's step; `v`: the
  reader.

 -/
theorem lem97_reader_finalized (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ anchor i₂ H T r_D s_D j : ℕ) (D : Block V) (v : V)
    -- every time is reached
    (hDiv : TimeDiverges x.toTrace)
    -- corruption is permanent
    (hMono : Sched.MonotoneCorruption)
    -- blocks and Goldfish votes are delivered within `Δ` after `GST`
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    -- a root names one block among what honest validators hold by `T`
    (hRoots : RootsNameBlocksUntil S Sched x T)
    -- a block reaches a validator only once it holds the parent
    (hParent : ParentHeldAtDelivery S Sched x)
    -- nobody votes in an honest validator's name
    (hOwner : VotesCastByOwner S Sched x)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    -- fewer than a quorum of validators are ever in the adversary set
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    -- committee sleepiness from `anchor`, at or before the hand-over step's time
    (hSleepK : CommitteeSleepiness S Sched anchor) (hAnchor : anchor ≤ x[i₂].time)
    (hGST : GST ≤ voteTime S s₀) (ht₀ : supportCutoff S (s₀ + 1) ≤ x[i₂].time)
    -- the updaters' confirmations up to every slot whose update is at most `T` form one chain
    (hChain : ∀ σ : ℕ, supportCutoff S (σ + 1) ≤ T →
      ConfirmationsChainBefore S Sched x s₀ (σ + 1))
    -- the chain invariant and the lock invariant at the slots whose update is at most `T`
    (hInv : ∀ s' : ℕ, s₀ < s' → supportCutoff S (s' + 1) ≤ T →
      ChainInvFor S Sched x (honestActiveAt S Sched s') (OnHonestChainBefore S Sched x s₀ s') s')
    (hLocks : ∀ s' : ℕ, s₀ < s' → supportCutoff S (s' + 1) ≤ T →
      ∀ w ∈ honestActiveAt S Sched s',
        LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ s') s' w)
    -- the lock invariant at the healed slot itself
    (hLocks₀ : ∀ w ∈ honestActiveAt S Sched s₀,
      LiveLocksOnFamilyAt S Sched x (OnHonestChainBefore S Sched x s₀ (s₀ + 1)) s₀ w)
    -- every honest attestation sent before the support cutoff of `s₀ + 1` has height at most `H`
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    -- the caches of the honest validators from the hand-over to `T`
    (hCaches : ∀ (j' : ℕ) (w : V), x[i₂].time ≤ x[j'].time → x[j'].time ≤ T →
      w ∉ Sched.adv (x[j'].time : Int) → CachesOnChain S Sched x s₀ H (x[j'][w].st))
    -- `s_D` is the first slot of round `r_D`, its support cutoff at most `T`, starting after the
    -- hand-over step's time
    (hsD : s_D = r_D * S.C.R) (hT : supportCutoff S s_D ≤ T)
    (hAfter : x[i₂].time < slotStart S s_D)
    -- `s_D` is an honest round opening slot
    (hOpener : HonestOpenerAt S Sched s_D)
    -- the proposer's tick at the start of `s_D` put `D` on the wire
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s_D) ∧
      (⟨S.P.proposer s_D, NamedObject.block D⟩ : SignedMsg V (NamedObject V)) ∈
        x[i + 1].sent - x[i].sent)
    -- no block the proposer held before the start of `s_D` has `D`'s root
    (hNoCol : ¬ RootCollisionAtProposal S Sched x s_D D)
    -- `D`'s height is greater than the threshold
    (hHD : H < (chainStateOf S.C D).h)
    -- the reader: honest through step `j`, at a time at most `T`, awake for one whole delay
    -- between the start of `s_D` and the time of step `j`
    (hv : HonestThrough x j v) (hjT : x[j].time ≤ T)
    (hAwake : AwakeForDelayWithin S Sched (Δ S) v (slotStart S s_D) x[j].time) :
    (chainStateOf S.C D).F.AncestorEq (x[j][v].st).S.F :=
  GoldilocksCorrectness.Proofs.Executions.lem97_reader_finalized S Sched x GST s₀ anchor i₂ H T
    r_D s_D j D v hDiv hMono hSync hCatch hRoots hParent hOwner hU hAdvQ hSleepK hAnchor hGST ht₀
    hChain hInv hLocks hLocks₀ hOld hCaches hsD hT hAfter hOpener hPropose hNoCol hHD hv hjT hAwake

end GoldilocksCorrectness.Statements.Executions
