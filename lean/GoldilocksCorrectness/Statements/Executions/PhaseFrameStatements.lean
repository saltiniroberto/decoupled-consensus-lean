module
public import GoldilocksCorrectness.Proofs.Executions.PhaseFrame

@[expose] public section

/-!
# The frame facts of the phase

The audited statements about the blocks honest validators hold and the heights honest
attestations name, each proved in `GoldilocksCorrectness/Proofs/Executions/PhaseFrame.lean`:

- Lemma 89a, `lem68_honest_past_finalized`: the block finalized by the chain state of a block an
  honest validator holds is an ancestor of, or equal to, every block an honest validator holds at a
  greater chain-state height;
- `lem89b_at`: an honest validator's `h_max` before `t` is at least the height of every honest
  attestation sent at least one delay earlier, when `GST + Δ ≤ t`, fewer than a third of the
  validators have been in the adversary set up to `t`, and the validator is awake and honest from
  `t − Δ` to `t`; on the delivery and roots premises up to a bound `b ≥ t`;
- Lemma 89b, `lem89b_h_max_ge_attested`: in the phase, an honest validator's `h_max` is at least
  the height of every honest attestation sent at least one delay earlier (the instance of
  `lem89b_at`);
- Lemma 89h, `lem89h_threshold`: every honest attestation sent before the action time of the
  round opening at slot `s₀` has height at most the proposal's chain-state height plus one;
- `attested_height_bound`: when every honest attestation of a tick at a time at most the time of
  step `i` has height at most `A`, every block a validator holds after `i` steps has chain-state
  height at most `A + 1`.


-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC

open GoldilocksCorrectness.Statements.Routines (Δ slotStart supportCutoff)

open GoldilocksCorrectness.Statements.Routines (chainStateOf)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicAction AtomicExec Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **Lemma 89a, Lemma 68's honest corollary.** Under unforgeability and roots naming blocks among
what honest validators hold, take a block `B` that `p` holds after `i` steps and a block `B'` that
`w` holds after `j` steps, each holder honest at its step, with `B'`'s chain-state height greater
than the finalization height of `B`'s chain state, and fewer than a third of the validators in the
adversary set up to the later of the two times; then the finalized block of `B`'s chain state is
`B'` or an ancestor of `B'`.

Why: otherwise Lemma 68 gives at least `2q − n` validators each with an E1 pair across the two
chains, one of which has never been in the adversary set (Lemma 65 (b)) and holds both in its
consistent record (Lemma 74); or two different blocks of the two chains share a root, both held by
honest validators.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `hU`: unforgeability; `hRoots`: roots
  name blocks; `i`, `j`: the two steps; `p`, `w`: the two holders; `B`, `B'`: the two blocks.



Read aloud: the block finalized by the chain state of a block `p` holds at step `i` is `B'` or an
ancestor of `B'`, when `B'`, held by `w` at step `j`, has a chain-state height greater than that
finalization height, both holders are honest at their steps, and fewer than a third of the
validators have been corrupted up to the later of the two times.

Roots name blocks until `tR`, at least `max x[i].time x[j].time`: the proof compares an ancestor of
`B`, held after `i` steps, with an ancestor of `B'`, held after `j` steps. -/
theorem lem68_honest_past_finalized (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace) {tR : ℕ}
    (hRoots : RootsNameBlocksUntil S Sched x tR) (i j : ℕ) (p w : V) (B B' : Block V)
    -- fewer than a third of the validators have been in the adversary set up to the later time
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (max (x[i].time : Int) (x[j].time : Int)))
    -- `p` is honest after `i` steps, and `w` after `j` steps
    (hp : p ∉ Sched.adv (x[i].time : Int)) (hw : w ∉ Sched.adv (x[j].time : Int))
    -- `p` holds `B` after `i` steps, and `w` holds `B'` after `j` steps
    (hB : B ∈ (x[i][p].st).S.T) (hB' : B' ∈ (x[j][w].st).S.T)
    -- the chain-state height of `B'` is greater than the finalization height of `B`'s
    (hlt : (chainStateOf S.C B).h_F < (chainStateOf S.C B').h)
    -- the latest time the proof takes a block as held is at most the bound
    (htR : max x[i].time x[j].time ≤ tR) :
    (chainStateOf S.C B).F.AncestorEq B' :=
  GoldilocksCorrectness.Proofs.Executions.lem68_honest_past_finalized S Sched x hU hRoots i j p w
    B B' hThird hp hw hB hB' hlt htR

/-- **Lemma 89b over the reader's time.** From `GST + Δ` on, with fewer than a third of the
validators in the adversary set up to `t`: when the step `i` is `u`'s tick at `t'` and puts `u`'s
attestation `a` on the wire, `t'` is at least one delay before `t`, and `v` is awake and honest at
every time from `t − Δ` to `t`, the height of `a` is at most `v`'s `h_max` before `t`.

Why: Lemma 89b's proof, which reads of the phase only these four facts: `a`'s height is the
chain-state height of a block `D` that `u` held (Lemma 49); `D` reaches `v` within one delay unless
it conflicts with `v`'s finalized block, and then it is at a height at most that block's
finalization height (Lemma 89a), less than `v`'s `h_max`; a block `v` holds is at a height at most
`h_max` (Lemma 46).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous;
- `t`: the time `v`'s state is read before; `t'`: the time of `u`'s tick; `i`: its step; `b`: the
  bound on the deadlines;
- `u`: the attester; `v`: the validator whose `h_max` is read; `a`: the attestation.



Read aloud: an honest validator awake for the last delay before `t` has, before `t`, an `h_max` at
least the height of every honest attestation sent at least one delay before `t`, once `t` is one
delay after `GST` and fewer than a third of the validators have been corrupted up to `t`.

Restated with the delivery and roots premises up to `b`, the latest deadline being `t` (the
attestation's source block, which `u` holds before `t' ≤ t − Δ S`, reaching `v` by `t`). -/
theorem lem89b_at (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST t t' i b : ℕ) (u v : V) (a : Attestation V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject b)
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject b)
    (hRoots : RootsNameBlocksUntil S Sched x b)
    (hParent : ParentHeldAtDelivery S Sched x) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    -- `t` is at least one delay after `GST`
    (hGST : GST + Δ S ≤ t)
    -- fewer than a third of the validators have been in the adversary set up to `t`
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (t : Int))
    -- `t` is at least one delay after `t'`
    (ht' : t' + Δ S ≤ t)
    -- `v` is awake and honest at every time from `t − Δ S` to `t`
    (hv : ∀ t'' : ℕ, t - Δ S ≤ t'' → t'' ≤ t →
      v ∈ Sched.awake (t'' : Int) ∧ v ∉ Sched.adv (t'' : Int))
    -- the step `i` is `u`'s tick at `t'`, and put `u`'s attestation `a` on the wire
    (hSend : x.lbl i = AtomicAction.tickAllAwake t' ∧
      (⟨u, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    -- the latest deadline the proof reads is at most the bound
    (hb : t ≤ b) :
    a.h ≤ (stateBefore x t v).S.h_max :=
  GoldilocksCorrectness.Proofs.Executions.lem89b_at S Sched x GST t t' i b u v a hDiv hMono hSync
    hCatch hRoots hParent hU hGST hThird ht' hv hSend hb

/-- **Lemma 89b, the honest `h_max` keeps up with the honest attestations.** In the phase
`[tGAT, tAwakeEnd]`, from `GST` on, every validator honest at a time of the phase awake then and
fewer than a third of the validators in the adversary set up to `tAwakeEnd`: when the step `i` is
`u`'s tick at `t'` and puts `u`'s attestation `a` on the wire, and `v` is honest at a time `t` of
the phase at least one delay into it and at least one delay after `t'`, the height of `a` is at
most `v`'s `h_max` before `t`.

Why: `a`'s height is the chain-state height of a block `D` that `u` held (Lemma 49); `D` reaches
`v` within one delay unless it conflicts with `v`'s finalized block, and then it is at a height at
most that block's finalization height (Lemma 89a), less than `v`'s `h_max`; a block `v` holds is
at a height at most `h_max` (Lemma 46).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST ≤ tGAT ≤ tAwakeEnd`: the phase;
- `t`: the time `v`'s state is read before; `t'`: the time of `u`'s tick; `i`: its step;
- `u`: the attester; `v`: the validator whose `h_max` is read; `a`: the attestation.



Read aloud: in the phase, no honest validator's `h_max` lags more than one delay behind the heights
honest attestations name.

Roots name blocks until `t`: `lem89b_at`, which the proof calls with `b := t`, takes blocks as held
up to `t`. -/
theorem lem89b_h_max_ge_attested (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd t t' i : ℕ) (u v : V)
    (a : Attestation V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x t)
    (hParent : ParentHeldAtDelivery S Sched x) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    -- the phase starts from `GST` on
    (hGST : GST ≤ tGAT)
    -- fewer than a third of the validators have been in the adversary set up to the phase's end
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    -- every validator honest at a time of the phase is awake then
    (hAwake : ∀ t'' : ℕ, tGAT ≤ t'' → t'' ≤ tAwakeEnd →
      ∀ w : V, w ∉ Sched.adv (t'' : Int) → w ∈ Sched.awake (t'' : Int))
    -- `t` is at least one delay into the phase, and at least one delay after `t'`
    (ht : tGAT + Δ S ≤ t) (ht' : t' + Δ S ≤ t) (htEnd : t ≤ tAwakeEnd)
    -- `v` is honest at `t`
    (hv : v ∉ Sched.adv (t : Int))
    -- the step `i` is `u`'s tick at `t'`, and put `u`'s attestation `a` on the wire
    (hSend : x.lbl i = AtomicAction.tickAllAwake t' ∧
      (⟨u, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent) :
    a.h ≤ (stateBefore x t v).S.h_max :=
  GoldilocksCorrectness.Proofs.Executions.lem89b_h_max_ge_attested S Sched x GST tGAT tAwakeEnd t
    t' i u v a hDiv hMono hSync hCatch hRoots hParent hU hGST hThird hAwake ht ht' htEnd hv
    hSend

/-- **Lemma 89h, the threshold.** In the phase `[tGAT, tAwakeEnd]`, from `GST` on, every validator
honest at a time of the phase awake then and fewer than a third of the validators in the adversary
set up to `tAwakeEnd`, take the
round `r₀` whose first slot `s₀ ≥ 1` starts at least one delay into the phase and whose action
time is in the phase, and the block `B₀` that `p₀`, honest at the start of slot `s₀`, put on the
wire at its tick then, with `B₀`'s parent in the viable tree of `p₀`'s frame before that start;
then every attestation an honest awake validator put on the wire at a tick before the action time
of round `r₀` has height at most `B₀`'s chain-state height plus one.

Why: such a tick is at the action time of an earlier round, so at least one delay before the start
of slot `s₀` (`R ≥ 2`); Lemma 89b bounds the attestation's height by `p₀`'s `h_max` before that
start, which is at most `head_height_floor` at `p₀` (the least chain-state height a viable block may have) plus one, and `head_height_floor` is at most `B₀`'s height (Lemma 58's
corollary).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST ≤ tGAT ≤ tAwakeEnd`: the phase;
- `r₀`: the round; `s₀`: its first slot; `B₀`: the proposal; `p₀`: its proposer.



Read aloud: every honest attestation sent before the action time of the healed round has height
at most `h(B₀) + 1`.

Roots name blocks until `slotStart S s₀`: `lem89b_at`, which the proof calls at `p₀` before the
start of slot `s₀`, takes blocks as held up to that start. -/
theorem lem89h_threshold (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST tGAT tAwakeEnd r₀ s₀ : ℕ) (B₀ : Block V) (p₀ : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (slotStart S s₀))
    (hParent : ParentHeldAtDelivery S Sched x) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    -- the phase starts from `GST` on
    (hGST : GST ≤ tGAT)
    -- fewer than a third of the validators have been in the adversary set up to the phase's end
    (hThird : AdversaryFewerThanThirdUntil Sched (validator_count V) (tAwakeEnd : Int))
    -- every validator honest at a time of the phase is awake then
    (hAwake : ∀ t : ℕ, tGAT ≤ t → t ≤ tAwakeEnd →
      ∀ w : V, w ∉ Sched.adv (t : Int) → w ∈ Sched.awake (t : Int))
    -- `s₀` is the first slot of round `r₀`, and not slot `0`
    (hs₀ : s₀ = r₀ * S.C.R) (hs₁ : 1 ≤ s₀)
    -- slot `s₀` starts at least one delay into the phase, and its round acts inside the phase
    (hFirst : tGAT + Δ S ≤ slotStart S s₀) (hEnd : supportCutoff S (s₀ + 1) ≤ tAwakeEnd)
    -- `p₀` is honest at the start of slot `s₀`
    (hp₀ : p₀ ∉ Sched.adv ((slotStart S s₀ : ℕ) : Int))
    -- `p₀`'s tick at the start of slot `s₀` put `B₀` on the wire
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s₀) ∧
      (⟨p₀, NamedObject.block B₀⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    -- `B₀`'s parent is in the viable tree of `p₀`'s frame before the start of slot `s₀`
    (hParentIn : B₀.parent ∈ viable_tree (fg_to_ac (stateBefore x (slotStart S s₀) p₀).S)
      (fg_to_ac (stateBefore x (slotStart S s₀) p₀).S).tree) :
    OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) ((chainStateOf S.C B₀).h + 1) :=
  GoldilocksCorrectness.Proofs.Executions.lem89h_threshold S Sched x GST tGAT tAwakeEnd r₀ s₀ B₀
    p₀ hDiv hMono hSync hCatch hRoots hParent hU hGST hThird hAwake hs₀ hs₁ hFirst hEnd hp₀
    hPropose hParentIn

/-- **The height bound from the old attestations.** Under unforgeability, with fewer than a third
of the validators in the adversary set up to the time of step `i`: when every attestation that a
validator awake and honest at a tick at a time at most `x[i].time` put on the wire at that tick has
height at most `A`, every block `D` that `v` holds after `i` steps has chain-state height at most
`A + 1`.

Why: otherwise Lemma 67 gives an ancestor `Y` of `D` at height `A + 2` whose chain includes a
certificate at height `A + 1`; its quorum has a member `u` never in the adversary set up to
`x[i].time` (Lemma 65 (b)); `u`'s attestation at height `A + 1` included on `Y`'s chain is in `u`'s
record (Lemma 74), so it was put on the wire by `u`'s own tick at a step before `i`, at a time at
most `x[i].time`, and `hOld` bounds its height by `A`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `hU`: unforgeability;
- `i`: the step; `A`: the bound on the heights of the honest attestations; `v`: the holder;
  `D`: the block.



Read aloud: if no honest attestation of a tick up to the current time is at a height greater than
`A`, every block `v` holds has height at most `A + 1`. -/
theorem attested_height_bound (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace) (i A : ℕ) (v : V)
    (D : Block V)
    -- fewer than a third of the validators have been in the adversary set up to step `i`'s time
    (hAdv : AdversaryFewerThanThirdUntil Sched (validator_count V) (x[i].time : Int))
    -- every honest attestation of a tick at a time at most `x[i].time` has height at most `A`
    (hOld : OldAttestationsAtMost S Sched x (x[i].time + 1) A)
    -- `v` holds `D` after `i` steps
    (hD : D ∈ (x[i][v].st).S.T) :
    (chainStateOf S.C D).h ≤ A + 1 :=
  GoldilocksCorrectness.Proofs.Executions.attested_height_bound S Sched x hU i A v D hAdv hOld hD

end GoldilocksCorrectness.Statements.Executions
