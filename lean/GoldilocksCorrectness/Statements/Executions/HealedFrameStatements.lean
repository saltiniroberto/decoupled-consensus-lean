module
public import GoldilocksCorrectness.Proofs.Executions.Lemma91

@[expose] public section

/-!
# Lemma 91: the frame facts after healing

The audited statements, proved in `GoldilocksCorrectness/Proofs/Executions/Lemma91.lean`: from the
end of the healing phase, with the caches of every honest validator on the honest chain (Lemma 84),
the honest confirmations forming a chain, the old
attestations at most `H` (Lemma 89) and fewer than a quorum ever corrupted (Lemma 87):

- Lemma 91 (b), `lem91b_voter_head_height_floor_le_parent`: a voter's `head_height_floor` is at
  most the height of a block extending the chain before `s − 1` and reaching `m − 1`;
- Lemma 91 (c), `lem91c_proposer_h_max_le_voter_h_max`: the voter's `h_max` is at least the
  proposer's; `lem91c_at`, the same over the proposer's reading time `t` and the voter's
  `t + Δ`, on the delivery and roots premises up to a bound `b` (Lemma 91 (c) is its instance at
  `t := slotStart S s`, `b := voteTime S s`);
- Lemma 91 (d), `lem91d_not_contested`: no honest FG state is contested;
- Lemma 91 (e), `lem91e_proposal_height_ge_h_max`: the honest proposal reaches the proposer's
  `h_max`;
- Lemma 91 (f), `lem91f_voter_root_on_chain_before`: the root of an honest fork choice is on the
  chain before the slot after every attestation sent by then.

Here `m` is the `h_max` of the proposer's FG state before the start of the proposal's slot. Lemma
91 (a), `lem91a_attested_height_le_proposer_h_max`, is not landed; the letters (b) to (f) are kept.


-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ slotStart voteTime supportCutoff)

open GoldilocksCorrectness.Statements.Routines (chainStateOf)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **Lemma 91 (b), `head_height_floor` at the voter (the least chain-state height a viable block may have) is at most the proposal's parent's height**. In
an execution where every time is reached and corruption is permanent, under unforgeability and
when fewer than a quorum of validators are ever in the adversary set: let slot `s` start after the
time `x[i₁].time`; let the updaters' confirmations of the slots from `s₀` to before `s − 1` form
one chain (`ConfirmationsChainBefore`); let every honest
attestation sent before the support cutoff of slot `s₀ + 1` have height at most `H`; let every
validator honest at a step at a time at least `x[i₁].time` have its caches on the honest chain with
justification height greater than `H` (`CachesOnChain`); let `p` be honest at the start of slot
`s` and `w` honest at the vote time of slot `s`; and let `Q` be a block that every block on the
honest chain before slot `s − 1` is an ancestor of, or equal to, and whose chain-state height is at
least `m − 1`, with `m` the `h_max` of `p`'s FG state before the start of slot `s`. Then
`head_height_floor` of `w`'s FG state before the vote time of slot `s` is at most `Q`'s chain-state
height.

Why: `w`'s FG state is not contested (Lemma 91 (d)), so its `head_height_floor` is `h_max_w − 1`. When
`h_max_w ≤ m`, `hQ` closes. Otherwise `w` holds a block at `h_max_w` and the block that raised its
chain past `h_max_w − 1` carries a progress certificate at `h_max_w − 1 ≥ m > H` (Lemma 67); the
certificate route names an entry of the chain at that height, confirmed at a slot `s_a` whose
support cutoff of slot `s_a + 1` is before the vote time of slot `s`, so `s_a + 2 ≤ s`: the entry is
on the chain before `s − 1`, an ancestor of `Q`, and its height is at most `Q`'s (Lemma 47 (d)).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `s`: the slot
  of the proposal; `i₁`: the step at the phase's end; `H`: the threshold;
- `p`: the proposer of slot `s`; `w`: the voter; `Q`: the block (the proposal's parent where it is
  used).

Read aloud: after healing the voter's least viable height never passes a block that extends the
chain before `s − 1` and reaches `m − 1`, such as the honest proposal's parent.

 -/
theorem lem91b_voter_head_height_floor_le_parent (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ s i₁ H : ℕ) (p w : V) (Q : Block V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hs : x[i₁].time < slotStart S s)
    (hChain : ConfirmationsChainBefore S Sched x s₀ (s - 1))
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → u ∉ Sched.adv (x[j].time : Int) →
      CachesOnChain S Sched x s₀ H (x[j][u].st))
    (hp : p ∉ Sched.adv ((slotStart S s : ℕ) : Int))
    (hw : w ∉ Sched.adv ((voteTime S s : ℕ) : Int))
    (hParentChain : ∀ C : Block V, OnHonestChainBefore S Sched x s₀ (s - 1) C → C.AncestorEq Q)
    (hQ : (stateBefore x (slotStart S s) p).S.h_max - 1 ≤ (chainStateOf S.C Q).h) :
    head_height_floor (stateBefore x (voteTime S s) w).S ≤ (chainStateOf S.C Q).h :=
  GoldilocksCorrectness.Proofs.Executions.lem91b_voter_head_height_floor_le_parent S Sched x s₀ s i₁
    H p w Q hDiv hMono hU hAdvQ hs hChain hOld hCaches hp hw hParentChain hQ

/-- **Lemma 91 (b), `head_height_floor` at the voter is at most the proposal's parent's height**. In an
execution where every time is reached and corruption is permanent, under unforgeability and when
fewer than a quorum of validators are ever in the adversary set: let slot `s` start after the time
`x[i₁].time`; let the updaters' confirmations of the slots from `s₀` to before `s − 1` form one
chain (`ConfirmationsChainBefore`); let every honest attestation sent before the support cutoff of
slot `s₀ + 1` have height at most `H`; let every validator honest at a step at a time from
`x[i₁].time` to `voteTime S s` have its caches on the honest chain with justification height greater
than `H` (`CachesOnChain`); let `p` be honest at the start of slot `s` and `w` honest at the vote
time of slot `s`; and let `Q` be a block that every block on the honest chain before slot `s − 1` is
an ancestor of, or equal to, and whose chain-state height is at least `m − 1`, with `m` the `h_max`
of `p`'s FG state before the start of slot `s`. Then `head_height_floor` of `w`'s FG state before
the vote time of slot `s` is at most `Q`'s chain-state height.

Why: `w`'s FG state is not contested (Lemma 91 (d)), so its `head_height_floor` is `h_max_w − 1`. When
`h_max_w ≤ m`, `hQ` closes. Otherwise `w` holds a block at `h_max_w` and the block that raised its
chain past `h_max_w − 1` carries a progress certificate at `h_max_w − 1 ≥ m > H` (Lemma 67); the
certificate route names an entry of the chain at that height, confirmed at a slot `s_a` whose
support cutoff of slot `s_a + 1` is before the vote time of slot `s`, so `s_a + 2 ≤ s`: the entry is
on the chain before `s − 1`, an ancestor of `Q`, and its height is at most `Q`'s (Lemma 47 (d)).

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `s`: the slot
  of the proposal; `i₁`: the step at the phase's end; `H`: the threshold;
- `p`: the proposer of slot `s`; `w`: the voter; `Q`: the block (the proposal's parent where it is
  used).

Read aloud: after healing the voter's least viable height never passes a block that extends the
chain before `s − 1` and reaches `m − 1`, such as the honest proposal's parent.



Caches up to `voteTime S s`: the proof reads `p`'s caches before the start of slot `s` and `w`'s
before the vote time of slot `s`.  -/
theorem lem91b_voter_head_height_floor_le_parent_until (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ s i₁ H : ℕ) (p w : V) (Q : Block V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hs : x[i₁].time < slotStart S s)
    (hChain : ConfirmationsChainBefore S Sched x s₀ (s - 1))
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → x[j].time ≤ voteTime S s →
      u ∉ Sched.adv (x[j].time : Int) → CachesOnChain S Sched x s₀ H (x[j][u].st))
    (hp : p ∉ Sched.adv ((slotStart S s : ℕ) : Int))
    (hw : w ∉ Sched.adv ((voteTime S s : ℕ) : Int))
    (hParentChain : ∀ C : Block V, OnHonestChainBefore S Sched x s₀ (s - 1) C → C.AncestorEq Q)
    (hQ : (stateBefore x (slotStart S s) p).S.h_max - 1 ≤ (chainStateOf S.C Q).h) :
    head_height_floor (stateBefore x (voteTime S s) w).S ≤ (chainStateOf S.C Q).h :=
  GoldilocksCorrectness.Proofs.Executions.lem91b_voter_head_height_floor_le_parent_until S Sched x
    s₀ s i₁ H p w Q hDiv hMono hU hAdvQ hs hChain hOld hCaches hp hw hParentChain hQ

/-- **Lemma 91 (c) over the proposer's reading time.** In an execution where every time is reached,
corruption is permanent, blocks and Goldfish votes are delivered within `Δ` after `GST` to a
receiver awake by a time at most `b` (synchrony from the receiver's wake, and catch-up on wake, up
to `b`), a root names one block among what honest validators hold by
`b`, and a block reaches a validator only once it holds the parent; under unforgeability and when
fewer than a quorum of validators are ever in the adversary set: let `GST` be at most `t`, `t` at
least `1` and later than `x[i₁].time`; let the honest confirmations form a chain from slot `s₀`;
let every honest attestation sent before the support cutoff of slot `s₀ + 1` have height at most
`H`; let every validator honest at a step at a time at least `x[i₁].time` have its caches on the
honest chain with justification height greater than `H`; let `p` be honest at `t`, and `w` awake
and honest at every time from `t` to `t + Δ S`; and let `t + Δ S` be at most `b`. Then the `h_max`
of `p`'s FG state before `t` is at most that of `w`'s FG state before `t + Δ S`.

Why: Lemma 91 (c)'s proof, with `slotStart S s` written `t` and `voteTime S s` written `t + Δ S`;
that proof reads of the slot only `GST ≤ slotStart S s` and `1 ≤ slotStart S s`. `p` holds a
block `Y` at `m := h_max_p`; the block that raised `Y`'s chain past `m − 1` carries a progress
certificate at `m − 1 > H`, naming the chain's entry `E` at `m − 1`, an ancestor of `Y`. `w`'s
justified block `J_w` is on the chain, an entry. If `J_w` is `E` or an ancestor of `E`, `w`'s
finalized block is compatible with `Y`, `Y` reaches `w` by `t + Δ S`, and `m ≤ h_max_w`.
Otherwise `J_w`'s height is at least `m`, and `J_w` is in `w`'s tree.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `t`: the time `p`'s state is read before; `i₁`:
  the step at the phase's end; `H`: the threshold; `b`: the bound on the deadlines; `p`: the
  proposer; `w`: the voter.



Read aloud: after healing, a validator awake for the delay after `t` knows, before `t + Δ`, a
height at least as great as a validator honest at `t` knows before `t`.

Roots name blocks until `b`, at least `t + Δ S`: `p`'s block `Y` reaches `w` by `t + Δ S`, and the
blocks the proof compares are held by then. -/
theorem lem91c_at (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ t i₁ H b : ℕ) (p w : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject b)
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject b)
    (hRoots : RootsNameBlocksUntil S Sched x b)
    (hParent : ParentHeldAtDelivery S Sched x) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hGST : GST ≤ t) (ht1 : 1 ≤ t) (hi : x[i₁].time < t)
    (hChain : ConfirmationsChain S Sched x s₀)
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → u ∉ Sched.adv (x[j].time : Int) →
      CachesOnChain S Sched x s₀ H (x[j][u].st))
    (hp : p ∉ Sched.adv (t : Int))
    (hw : ∀ t' : ℕ, t ≤ t' → t' ≤ t + Δ S →
      w ∈ Sched.awake (t' : Int) ∧ w ∉ Sched.adv (t' : Int))
    -- the latest deadline the proof reads is at most the bound
    (hb : t + Δ S ≤ b) :
    (stateBefore x t p).S.h_max ≤ (stateBefore x (t + Δ S) w).S.h_max :=
  GoldilocksCorrectness.Proofs.Executions.lem91c_at S Sched x GST s₀ t i₁ H b p w hDiv hMono hSync
    hCatch hRoots hParent hU hAdvQ hGST ht1 hi hChain hOld hCaches hp hw hb

/-- **Lemma 91 (c) over the proposer's reading time.** In an execution where every time is reached,
corruption is permanent, blocks and Goldfish votes are delivered within `Δ` after `GST` to a
receiver awake by a time at most `b` (synchrony from the receiver's wake, and catch-up on wake, up
to `b`), a root names one block among what honest validators hold by
`b`, and a block reaches a validator only once it holds the parent; under unforgeability and when
fewer than a quorum of validators are ever in the adversary set: let `GST` be at most `t`, `t` at
least `1` and later than `x[i₁].time`; let the updaters' confirmations of the slots from `s₀` to
before `s'` form one chain (`ConfirmationsChainBefore`), `s'` greater than every slot whose next
slot's support cutoff is before `t + Δ S`; let every honest attestation sent before the support
cutoff of slot `s₀ + 1` have height at most `H`; let every validator honest at a step at a time from
`x[i₁].time` to `t + Δ S` have its caches on the
honest chain with justification height greater than `H`; let `p` be honest at `t`, and `w` awake and
honest at every time from `t` to `t + Δ S`; and let `t + Δ S` be at most `b`. Then the `h_max` of
`p`'s FG state before `t` is at most that of `w`'s FG state before `t + Δ S`.

Why: Lemma 91 (c)'s proof, with `slotStart S s` written `t` and `voteTime S s` written `t + Δ S`;
that proof reads of the slot only `GST ≤ slotStart S s` and `1 ≤ slotStart S s`. `p` holds a
block `Y` at `m := h_max_p`; the block that raised `Y`'s chain past `m − 1` carries a progress
certificate at `m − 1 > H`, naming the chain's entry `E` at `m − 1`, an ancestor of `Y`. `w`'s
justified block `J_w` is on the chain, an entry. If `J_w` is `E` or an ancestor of `E`, `w`'s
finalized block is compatible with `Y`, `Y` reaches `w` by `t + Δ S`, and `m ≤ h_max_w`.
Otherwise `J_w`'s height is at least `m`, and `J_w` is in `w`'s tree.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `t`: the time `p`'s state is read before; `i₁`:
  the step at the phase's end; `H`: the threshold; `b`: the bound on the deadlines; `s'`: the
  bound on the slots of the chain; `p`: the proposer; `w`: the voter.



Read aloud: after healing, a validator awake for the delay after `t` knows, before `t + Δ`, a
height at least as great as a validator honest at `t` knows before `t`.

Roots name blocks until `b`, at least `t + Δ S`: `p`'s block `Y` reaches `w` by `t + Δ S`, and the
blocks the proof compares are held by then.

On the chain before `s'`: the two blocks compared, the entry `E` and `w`'s justified block, are on
the chain at slots whose next slot's support cutoff is before `t + Δ S` (Lemma 83, under the roots
premise). The landed form is the instance at `s' := t + Δ S`.

Caches up to `t + Δ S`: the proof reads `p`'s caches before `t` and `w`'s before `t + Δ S`.  -/
theorem lem91c_at_until (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ t i₁ H b s' : ℕ) (p w : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWakeUpTo S Sched x (Δ S) GST acObject b)
    (hCatch : CatchUpOnWakeUpTo S Sched x (Δ S) GST acObject b)
    (hRoots : RootsNameBlocksUntil S Sched x b)
    (hParent : ParentHeldAtDelivery S Sched x) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hGST : GST ≤ t) (ht1 : 1 ≤ t) (hi : x[i₁].time < t)
    (hChain : ConfirmationsChainBefore S Sched x s₀ s')
    -- every slot whose next slot's support cutoff is before `t + Δ S` is less than `s'`
    (hs' : ∀ s_a : ℕ, supportCutoff S (s_a + 1) < t + Δ S → s_a < s')
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → x[j].time ≤ t + Δ S →
      u ∉ Sched.adv (x[j].time : Int) → CachesOnChain S Sched x s₀ H (x[j][u].st))
    (hp : p ∉ Sched.adv (t : Int))
    (hw : ∀ t' : ℕ, t ≤ t' → t' ≤ t + Δ S →
      w ∈ Sched.awake (t' : Int) ∧ w ∉ Sched.adv (t' : Int))
    -- the latest deadline the proof reads is at most the bound
    (hb : t + Δ S ≤ b) :
    (stateBefore x t p).S.h_max ≤ (stateBefore x (t + Δ S) w).S.h_max :=
  GoldilocksCorrectness.Proofs.Executions.lem91c_at_until S Sched x GST s₀ t i₁ H b s' p w hDiv
    hMono hSync hCatch hRoots hParent hU hAdvQ hGST ht1 hi hChain hs' hOld hCaches hp hw hb

/-- **Lemma 91 (c), the voter is at least as far as the proposer.** In an execution where every
time is reached, corruption is permanent, blocks and Goldfish votes are delivered within `Δ` after
`GST` (synchrony from the receiver's wake, and catch-up on wake), a
root names one block among what honest validators hold, and a block reaches a validator only once
it holds the parent; under unforgeability and when fewer than a quorum of validators are ever in
the adversary set: let `GST` be at most the vote time of slot `s₀`; let the support cutoff of slot
`s₀ + 1` be at most `x[i₁].time`, and slot `s` start after it; let the honest confirmations form a
chain from slot `s₀`; let every honest attestation sent before the support cutoff of slot `s₀ + 1`
have height at most `H`; let every validator honest at a step at a time at least `x[i₁].time` have
its caches on the honest chain with justification height greater than `H`; let `p` be honest at
the start of slot `s`, and `w` awake and honest at every time from the start of slot `s` to its
vote time. Then the `h_max` of `p`'s FG state before the start of slot `s` is at most that of
`w`'s FG state before the vote time of slot `s`.

Why: `p` holds a block `Y` at `m := h_max_p`; the block that raised `Y`'s chain past `m − 1`
carries a progress certificate at `m − 1 > H`, naming the chain's entry `E` at `m − 1`, an
ancestor of `Y`. `w`'s justified block `J_w` is on the chain, an entry. If `J_w` is `E` or an
ancestor of `E`, `w`'s finalized block is compatible with `Y`, `Y` reaches `w` within `Δ`
(`mem_T_before_add_delay`), and `m ≤ h_max_w`. Otherwise `E` is a strict ancestor of `J_w`, so
`J_w`'s height is at least `m` (two entries of the chain at one height are one block), and `J_w`
is in `w`'s tree.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `s`: the slot; `i₁`: the step at the phase's end;
  `H`: the threshold; `p`: the proposer; `w`: the voter.

Read aloud: after healing, a voter awake through the slot's start knows a height at least as great
as the proposer's.



Roots name blocks until `voteTime S s`: `lem91c_at`, which the proof calls with `b := voteTime S
s`, takes blocks as held up to that time (`p`'s block reaching `w` by the vote time; the entry
of the honest chain the certificate route names, held by the support cutoff of its slot, a time
before `slotStart S s`). -/
theorem lem91c_proposer_h_max_le_voter_h_max (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ s i₁ H : ℕ) (p w : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (voteTime S s))
    (hParent : ParentHeldAtDelivery S Sched x) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hGST : GST ≤ voteTime S s₀) (ht₀ : supportCutoff S (s₀ + 1) ≤ x[i₁].time)
    (hs : x[i₁].time < slotStart S s)
    (hChain : ConfirmationsChain S Sched x s₀)
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → u ∉ Sched.adv (x[j].time : Int) →
      CachesOnChain S Sched x s₀ H (x[j][u].st))
    (hp : p ∉ Sched.adv ((slotStart S s : ℕ) : Int))
    (hw : ∀ t' : ℕ, slotStart S s ≤ t' → t' ≤ voteTime S s →
      w ∈ Sched.awake (t' : Int) ∧ w ∉ Sched.adv (t' : Int)) :
    (stateBefore x (slotStart S s) p).S.h_max ≤ (stateBefore x (voteTime S s) w).S.h_max :=
  GoldilocksCorrectness.Proofs.Executions.lem91c_proposer_h_max_le_voter_h_max S Sched x GST s₀ s i₁
    H p w hDiv hMono hSync hCatch hRoots hParent hU hAdvQ hGST ht₀ hs hChain hOld hCaches hp
    hw

/-- **Lemma 91 (c), the voter is at least as far as the proposer.** In an execution where every time
is reached, corruption is permanent, blocks and Goldfish votes are delivered within `Δ` after `GST`
(synchrony from the receiver's wake, and catch-up on wake), a root names
one block among what honest validators hold, and a block reaches a validator only once it holds the
parent; under unforgeability and when fewer than a quorum of validators are ever in the adversary
set: let `GST` be at most the vote time of slot `s₀`; let the support cutoff of slot `s₀ + 1` be at
most `x[i₁].time`, and slot `s` start after it; let the updaters' confirmations of the slots from
`s₀` to before `s − 1` form one chain (`ConfirmationsChainBefore`); let every honest attestation
sent before the support cutoff of slot `s₀ + 1` have height at most `H`; let every validator honest
at a step at a time from `x[i₁].time` to `voteTime S s` have
its caches on the honest chain with justification height greater than `H`; let `p` be honest at the
start of slot `s`, and `w` awake and honest at every time from the start of slot `s` to its vote
time. Then the `h_max` of `p`'s FG state before the start of slot `s` is at most that of `w`'s FG
state before the vote time of slot `s`.

Why: `p` holds a block `Y` at `m := h_max_p`; the block that raised `Y`'s chain past `m − 1`
carries a progress certificate at `m − 1 > H`, naming the chain's entry `E` at `m − 1`, an
ancestor of `Y`. `w`'s justified block `J_w` is on the chain, an entry. If `J_w` is `E` or an
ancestor of `E`, `w`'s finalized block is compatible with `Y`, `Y` reaches `w` within `Δ`
(`mem_T_before_add_delay`), and `m ≤ h_max_w`. Otherwise `E` is a strict ancestor of `J_w`, so
`J_w`'s height is at least `m` (two entries of the chain at one height are one block), and `J_w`
is in `w`'s tree.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `s`: the slot; `i₁`: the step at the phase's end;
  `H`: the threshold; `p`: the proposer; `w`: the voter.

Read aloud: after healing, a voter awake through the slot's start knows a height at least as great
as the proposer's.



Roots name blocks until `voteTime S s`: `lem91c_at`, which the proof calls with `b := voteTime S s`,
takes blocks as held up to that time (`p`'s block reaching `w` by the vote time; the entry of the
honest chain the certificate route names, held by the support cutoff of its slot, a time before
`slotStart S s`).

On the chain before `s − 1`: the blocks compared are on the chain at slots whose next slot's
support cutoff is before the vote time of slot `s`, so less than `s − 1`.

Caches up to `voteTime S s`: the proof reads `p`'s caches before the start of slot `s` and `w`'s
before the vote time of slot `s`.  -/
theorem lem91c_proposer_h_max_le_voter_h_max_until (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST s₀ s i₁ H : ℕ) (p w : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hSync : SynchronyFromWake Sched x.toTrace (Δ S) GST acObject)
    (hCatch : CatchUpOnWake Sched x.toTrace (Δ S) GST acObject)
    (hRoots : RootsNameBlocksUntil S Sched x (voteTime S s))
    (hParent : ParentHeldAtDelivery S Sched x) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hGST : GST ≤ voteTime S s₀) (ht₀ : supportCutoff S (s₀ + 1) ≤ x[i₁].time)
    (hs : x[i₁].time < slotStart S s)
    (hChain : ConfirmationsChainBefore S Sched x s₀ (s - 1))
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → x[j].time ≤ voteTime S s →
      u ∉ Sched.adv (x[j].time : Int) → CachesOnChain S Sched x s₀ H (x[j][u].st))
    (hp : p ∉ Sched.adv ((slotStart S s : ℕ) : Int))
    (hw : ∀ t' : ℕ, slotStart S s ≤ t' → t' ≤ voteTime S s →
      w ∈ Sched.awake (t' : Int) ∧ w ∉ Sched.adv (t' : Int)) :
    (stateBefore x (slotStart S s) p).S.h_max ≤ (stateBefore x (voteTime S s) w).S.h_max :=
  GoldilocksCorrectness.Proofs.Executions.lem91c_proposer_h_max_le_voter_h_max_until S Sched x GST
    s₀ s i₁ H p w hDiv hMono hSync hCatch hRoots hParent hU hAdvQ hGST ht₀ hs hChain hOld
    hCaches hp hw

/-- **Lemma 91 (d), no honest FG state is contested after healing.** In an execution where every
time is reached and corruption is permanent, under unforgeability and when fewer than a quorum of
validators are ever in the adversary set: let the updaters' confirmations of the slots from `s₀`
to before `s'` form one chain (`ConfirmationsChainBefore`); let every honest attestation sent
before the support cutoff of slot `s₀ + 1` have height at most `H`; let every validator honest at
a step at a time at least `x[i₁].time` have its caches on the honest chain with justification
height greater than `H`. Then at every step `i` at a time at least `x[i₁].time` such that every
slot `s_a` whose support cutoff of slot `s_a + 1` is at most that time is less than `s'`, the FG
state of a validator `v` honest at that time is not contested (`fg_contest`), and its
`head_height_floor` is its `h_max − 1`.

Why: a contested state holds a block `D` at `h_max = h_j + 1` of which the justified block `J` is
not an ancestor. The block that raised `D`'s chain past `h_j` carries a progress certificate at
`h_j > H` for the `T_h` of its parent (Lemma 67), an ancestor of `D`; the certificate route names
by its root an entry of the honest chain at `h_j`, confirmed at a slot whose update ran by the
step, so before slot `s'`; `J`'s own justification certificate (Lemma 66) names by `J`'s root
another such entry, and the two entries are one block (two entries at one height on the chain
before `s'` are one block). So the `T_h` and `J` have one root and are in `v`'s tree, so they are
one block (`RootsNameBlocksIn`), and `J` is an ancestor of `D`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `i₁`: the step
  at the phase's end; `i`: the step; `s'`: the bound on the slot; `H`: the threshold; `v`: the
  validator.

Read aloud: after healing there is one justification per height, so nothing contests, and the
least viable height is `h_max − 1`.

 -/
theorem lem91d_not_contested (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ i₁ i s' H : ℕ) (v : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hChain : ConfirmationsChainBefore S Sched x s₀ s')
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → u ∉ Sched.adv (x[j].time : Int) →
      CachesOnChain S Sched x s₀ H (x[j][u].st))
    (hi : x[i₁].time ≤ x[i].time) (hv : v ∉ Sched.adv (x[i].time : Int))
    (hs' : ∀ s_a : ℕ, supportCutoff S (s_a + 1) ≤ x[i].time → s_a < s') :
    fg_contest (x[i][v].st).S = false ∧
      head_height_floor (x[i][v].st).S = (x[i][v].st).S.h_max - 1 :=
  GoldilocksCorrectness.Proofs.Executions.lem91d_not_contested S Sched x s₀ i₁ i s' H v hDiv hMono
    hU hAdvQ hChain hOld hCaches hi hv hs'

/-- **Lemma 91 (d), no honest FG state is contested after healing.** In an execution where every
time is reached and corruption is permanent, under unforgeability and when fewer than a quorum of
validators are ever in the adversary set: let the updaters' confirmations of the slots from `s₀`
to before `s'` form one chain (`ConfirmationsChainBefore`); let every honest attestation sent
before the support cutoff of slot `s₀ + 1` have height at most `H`; let every validator honest at
a step at a time from `x[i₁].time` to `x[i].time` have its caches on the honest chain with
justification height greater than `H`. Then at every step `i` at a time at least `x[i₁].time` such
that every slot `s_a` whose support cutoff of slot `s_a + 1` is at most that time is less than
`s'`, the FG state of a validator `v` honest at that time is not contested (`fg_contest`), and its
`head_height_floor` is its `h_max − 1`.

Why: a contested state holds a block `D` at `h_max = h_j + 1` of which the justified block `J` is
not an ancestor. The block that raised `D`'s chain past `h_j` carries a progress certificate at
`h_j > H` for the `T_h` of its parent (Lemma 67), an ancestor of `D`; the certificate route names
by its root an entry of the honest chain at `h_j`, confirmed at a slot whose update ran by the
step, so before slot `s'`; `J`'s own justification certificate (Lemma 66) names by `J`'s root
another such entry, and the two entries are one block (two entries at one height on the chain
before `s'` are one block). So the `T_h` and `J` have one root and are in `v`'s tree, so they are
one block (`RootsNameBlocksIn`), and `J` is an ancestor of `D`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `i₁`: the step
  at the phase's end; `i`: the step; `s'`: the bound on the slot; `H`: the threshold; `v`: the
  validator.

Read aloud: after healing there is one justification per height, so nothing contests, and the
least viable height is `h_max − 1`.



Caches up to `x[i].time`: the proof reads `v`'s caches at step `i` only.  -/
theorem lem91d_not_contested_until (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ i₁ i s' H : ℕ) (v : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hChain : ConfirmationsChainBefore S Sched x s₀ s')
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → x[j].time ≤ x[i].time →
      u ∉ Sched.adv (x[j].time : Int) → CachesOnChain S Sched x s₀ H (x[j][u].st))
    (hi : x[i₁].time ≤ x[i].time) (hv : v ∉ Sched.adv (x[i].time : Int))
    (hs' : ∀ s_a : ℕ, supportCutoff S (s_a + 1) ≤ x[i].time → s_a < s') :
    fg_contest (x[i][v].st).S = false ∧
      head_height_floor (x[i][v].st).S = (x[i][v].st).S.h_max - 1 :=
  GoldilocksCorrectness.Proofs.Executions.lem91d_not_contested_until S Sched x s₀ i₁ i s' H v hDiv
    hMono hU hAdvQ hChain hOld hCaches hi hv hs'

/-- **Lemma 91 (e), the honest proposal reaches the proposer's `h_max`.** In an execution where
every time is reached and corruption is permanent, a root names one block among what honest
validators hold; under unforgeability and when fewer than a quorum of validators are ever in the
adversary set: let slot `s` start after `x[i₁].time`; let the updaters' confirmations of the slots
from `s₀` to before `s − 1` form one chain (`ConfirmationsChainBefore`); let every honest
attestation sent before the support cutoff of slot `s₀ + 1` have height at most `H`; let every
validator honest at a step at a time at least `x[i₁].time` have its caches on the honest chain
with justification height greater than `H`; let `p` be honest at the start of slot `s`, and its
tick at the start of slot `s` put `B` on the wire; let `B`'s parent have a chain-state height at least `head_height_floor` of `p`'s FG state before the start of slot `s`,
and every block on the honest chain before slot `s − 1` be an ancestor of `B`'s parent, or it.
Then `B`'s chain-state height is at least `m`, the `h_max` of `p`'s FG state before the start of
slot `s`.

Why: `p` holds a block `Y` at `m`; the block `Y₁` that raised `Y`'s chain past `m − 1` carries a
progress certificate at `m − 1 > H` for its parent's `T_h`, which is the chain's entry `E` at
`m − 1`, confirmed at a slot `s_a` with `s_a + 2 ≤ s`, so an ancestor of `B`'s parent; every
attestation of the certificate is in `p`'s pool (`pool_holds_chain_attestations`). If `B`'s parent
is at `m` or more, so is `B`. Otherwise the parent is at `m − 1` (Lemma 91 (d)), `E` is its `T_h`,
and Lemma 53 puts `B` at `m`, or at `m − 1` with `B.slot < E.slot + δt`; the second is excluded by
the branch that raised `Y₁`'s chain (Lemma 67 (b)): a justification certificate makes Lemma 53's
second part put `B` at `m`, and a timeout gives `E.slot + δt ≤ Y₁.slot ≤ s = B.slot`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `s`: the slot;
  `i₁`: the step at the phase's end; `H`: the threshold; `p`: the proposer; `B`: the proposal.

Read aloud: an honest proposer always includes the certificate that reached the greatest height it
knows.



Roots name blocks until `slotStart S s`: the proof compares a block `p` holds before `slotStart
S s` (the entry `T_h` of a chain state on `p`'s chain) with the entry of the honest chain at a
slot whose update ran by then. -/
theorem lem91e_proposal_height_ge_h_max (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ s i₁ H : ℕ) (p : V) (B : Block V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hRoots : RootsNameBlocksUntil S Sched x (slotStart S s)) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hs : x[i₁].time < slotStart S s)
    (hChain : ConfirmationsChainBefore S Sched x s₀ (s - 1))
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → u ∉ Sched.adv (x[j].time : Int) →
      CachesOnChain S Sched x s₀ H (x[j][u].st))
    (hp : p ∉ Sched.adv ((slotStart S s : ℕ) : Int))
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    (hParentHeightP : head_height_floor (stateBefore x (slotStart S s) p).S ≤
      (chainStateOf S.C B.parent).h)
    (hParentChain : ∀ C : Block V, OnHonestChainBefore S Sched x s₀ (s - 1) C →
      C.AncestorEq B.parent) :
    (stateBefore x (slotStart S s) p).S.h_max ≤ (chainStateOf S.C B).h :=
  GoldilocksCorrectness.Proofs.Executions.lem91e_proposal_height_ge_h_max S Sched x s₀ s i₁ H p B
    hDiv hMono hRoots hU hAdvQ hs hChain hOld hCaches hp hPropose hParentHeightP hParentChain

/-- **Lemma 91 (e), the honest proposal reaches the proposer's `h_max`.** In an execution where
every time is reached and corruption is permanent, a root names one block among what honest
validators hold; under unforgeability and when fewer than a quorum of validators are ever in the
adversary set: let slot `s` start after `x[i₁].time`; let the updaters' confirmations of the slots
from `s₀` to before `s − 1` form one chain (`ConfirmationsChainBefore`); let every honest
attestation sent before the support cutoff of slot `s₀ + 1` have height at most `H`; let every
validator honest at a step at a time from `x[i₁].time` to `slotStart S s` have its caches on the
honest chain with justification height greater than `H`; let `p` be honest at the start of slot `s`,
and its tick at the start of slot `s` put `B` on the wire; let `B`'s parent have a chain-state
height at least `head_height_floor` of `p`'s FG state before the start of slot `s`, and every block
on the honest chain before slot `s − 1` be an ancestor of `B`'s parent, or it. Then `B`'s
chain-state height is at least `m`, the `h_max` of `p`'s FG state before the start of slot `s`.

Why: `p` holds a block `Y` at `m`; the block `Y₁` that raised `Y`'s chain past `m − 1` carries a
progress certificate at `m − 1 > H` for its parent's `T_h`, which is the chain's entry `E` at
`m − 1`, confirmed at a slot `s_a` with `s_a + 2 ≤ s`, so an ancestor of `B`'s parent; every
attestation of the certificate is in `p`'s pool (`pool_holds_chain_attestations`). If `B`'s parent
is at `m` or more, so is `B`. Otherwise the parent is at `m − 1` (Lemma 91 (d)), `E` is its `T_h`,
and Lemma 53 puts `B` at `m`, or at `m − 1` with `B.slot < E.slot + δt`; the second is excluded by
the branch that raised `Y₁`'s chain (Lemma 67 (b)): a justification certificate makes Lemma 53's
second part put `B` at `m`, and a timeout gives `E.slot + δt ≤ Y₁.slot ≤ s = B.slot`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `s`: the slot;
  `i₁`: the step at the phase's end; `H`: the threshold; `p`: the proposer; `B`: the proposal.

Read aloud: an honest proposer always includes the certificate that reached the greatest height it
knows.



Roots name blocks until `slotStart S s`: the proof compares a block `p` holds before `slotStart S s`
(the entry `T_h` of a chain state on `p`'s chain) with the entry of the honest chain at a slot whose
update ran by then.

Caches up to `slotStart S s`: the proof reads `p`'s caches before the start of slot `s`.  -/
theorem lem91e_proposal_height_ge_h_max_until (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ s i₁ H : ℕ) (p : V) (B : Block V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hRoots : RootsNameBlocksUntil S Sched x (slotStart S s)) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hs : x[i₁].time < slotStart S s)
    (hChain : ConfirmationsChainBefore S Sched x s₀ (s - 1))
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → x[j].time ≤ slotStart S s →
      u ∉ Sched.adv (x[j].time : Int) → CachesOnChain S Sched x s₀ H (x[j][u].st))
    (hp : p ∉ Sched.adv ((slotStart S s : ℕ) : Int))
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s) ∧
      (⟨p, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    (hParentHeightP : head_height_floor (stateBefore x (slotStart S s) p).S ≤
      (chainStateOf S.C B.parent).h)
    (hParentChain : ∀ C : Block V, OnHonestChainBefore S Sched x s₀ (s - 1) C →
      C.AncestorEq B.parent) :
    (stateBefore x (slotStart S s) p).S.h_max ≤ (chainStateOf S.C B).h :=
  GoldilocksCorrectness.Proofs.Executions.lem91e_proposal_height_ge_h_max_until S Sched x s₀ s i₁ H
    p B hDiv hMono hRoots hU hAdvQ hs hChain hOld hCaches hp hPropose hParentHeightP hParentChain

/-- **Lemma 91 (f), the root of an honest fork choice is on the chain before `s'`.** In an execution
where every time is reached and corruption is permanent, a root names one block among what honest
validators hold; under unforgeability and when fewer than a quorum of validators are ever in the
adversary set: let every honest attestation sent before the support cutoff of slot `s₀ + 1` have
height at most `H`; let every validator honest at a step at a time at least
`x[i₁].time` have its caches on the honest chain with justification height greater than `H`. Then
at a step `j` at a time at least `x[i₁].time`, for `w` honest at that time and a slot `s'` such
that every slot `s_a` whose support cutoff of slot `s_a + 1` is at most that time is less than
`s'`, the root of `w`'s fork choice (`fc_root` of the frame) is on the honest chain before slot
`s'`.

Why: the root is the justified block `J` or the finalized block, an ancestor of `J`. `J` is the
justified block of a chain state of a block `D` of `w`'s tree (`CachesWitnessed`), certified on
`D`'s chain at `h_j > H` (Lemma 66); the certificate route names an entry of the chain at `h_j`,
confirmed at a slot `s_a` whose support cutoff is at most the step's time, so `s_a < s'`; that
entry and `J` have one root and are held by honest validators, so they are one block
.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `i₁`: the step
  at the phase's end; `j`: the step; `s'`: the bound on the slot; `H`: the threshold; `w`: the
  validator.

Read aloud: the root of an honest fork choice is on the chain confirmed by the attestations sent
by then.



Roots name blocks until `x[j].time`: the proof compares `w`'s justified block, held after `j`
steps, with the entry of the honest chain at a slot whose update ran by `x[j].time`. -/
theorem lem91f_voter_root_on_chain_before (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ i₁ j s' H : ℕ) (w : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hRoots : RootsNameBlocksUntil S Sched x x[j].time) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (u : V), x[i₁].time ≤ x[j].time → u ∉ Sched.adv (x[j].time : Int) →
      CachesOnChain S Sched x s₀ H (x[j][u].st))
    (hj : x[i₁].time ≤ x[j].time) (hw : w ∉ Sched.adv (x[j].time : Int))
    (hs' : ∀ s_a : ℕ, supportCutoff S (s_a + 1) ≤ x[j].time → s_a < s') :
    OnHonestChainBefore S Sched x s₀ s' (fg_to_ac (x[j][w].st).S).fc_root :=
  GoldilocksCorrectness.Proofs.Executions.lem91f_voter_root_on_chain_before S Sched x s₀ i₁ j s' H w
    hDiv hMono hRoots hU hAdvQ hOld hCaches hj hw hs'

/-- **Lemma 91 (f), the root of an honest fork choice is on the chain before `s'`.** In an execution
where every time is reached and corruption is permanent, a root names one block among what honest
validators hold; under unforgeability and when fewer than a quorum of validators are ever in the
adversary set: let every honest attestation sent before the support cutoff of slot `s₀ + 1` have
height at most `H`; let every validator honest at a step at a time from `x[i₁].time` to `x[j].time`
have its caches on the honest chain with justification height greater than `H`. Then at a step `j`
at a time at least `x[i₁].time`, for `w` honest at that time and a slot `s'` such that every slot
`s_a` whose support cutoff of slot `s_a + 1` is at most that time is less than `s'`, the root of
`w`'s fork choice (`fc_root` of the frame) is on the honest chain before slot `s'`.

Why: the root is the justified block `J` or the finalized block, an ancestor of `J`. `J` is the
justified block of a chain state of a block `D` of `w`'s tree (`CachesWitnessed`), certified on
`D`'s chain at `h_j > H` (Lemma 66); the certificate route names an entry of the chain at `h_j`,
confirmed at a slot `s_a` whose support cutoff is at most the step's time, so `s_a < s'`; that
entry and `J` have one root and are held by honest validators, so they are one block
.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s₀`: the healed slot; `i₁`: the step
  at the phase's end; `j`: the step; `s'`: the bound on the slot; `H`: the threshold; `w`: the
  validator.

Read aloud: the root of an honest fork choice is on the chain confirmed by the attestations sent
by then.



Roots name blocks until `x[j].time`: the proof compares `w`'s justified block, held after `j`
steps, with the entry of the honest chain at a slot whose update ran by `x[j].time`.

Caches up to `x[j].time`: the proof reads `w`'s caches at step `j` only.  -/
theorem lem91f_voter_root_on_chain_before_until (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (s₀ i₁ j s' H : ℕ) (w : V)
    (hDiv : TimeDiverges x.toTrace) (hMono : Sched.MonotoneCorruption)
    (hRoots : RootsNameBlocksUntil S Sched x x[j].time) (hU : Unforgeability Vocab.goldilocks Sched x.toTrace)
    (hAdvQ : ∀ t : Int, AdversaryFewerThanQuorumUntil Sched (quorum V) t)
    (hOld : OldAttestationsAtMost S Sched x (supportCutoff S (s₀ + 1)) H)
    (hCaches : ∀ (k : ℕ) (u : V), x[i₁].time ≤ x[k].time → x[k].time ≤ x[j].time →
      u ∉ Sched.adv (x[k].time : Int) → CachesOnChain S Sched x s₀ H (x[k][u].st))
    (hj : x[i₁].time ≤ x[j].time) (hw : w ∉ Sched.adv (x[j].time : Int))
    (hs' : ∀ s_a : ℕ, supportCutoff S (s_a + 1) ≤ x[j].time → s_a < s') :
    OnHonestChainBefore S Sched x s₀ s' (fg_to_ac (x[j][w].st).S).fc_root :=
  GoldilocksCorrectness.Proofs.Executions.lem91f_voter_root_on_chain_before_until S Sched x s₀ i₁ j
    s' H w hDiv hMono hRoots hU hAdvQ hOld hCaches hj hw hs'

end GoldilocksCorrectness.Statements.Executions
