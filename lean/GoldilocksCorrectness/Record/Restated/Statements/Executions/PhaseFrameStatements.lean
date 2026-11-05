module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.PhaseFrame
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# PhaseFrameStatements, over a model

The statements of `GoldilocksCorrectness/Statements/Executions/PhaseFrameStatements.lean`, over a
model `M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: Lemma 68's honest
corollary (Lemma 89a), the greatest chain-state height of an honest validator keeps up with the
honest attestations (Lemma 89b), the threshold (Lemma 89h) and the height bound from the old
attestations, read with the greatest chain-state height `hMax M S.C n` of the node's tree in place
of the cache `h_max`. Each is the theorem of the same name of
`Record/Restated/Proofs/Executions/PhaseFrame.lean`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC

open GoldilocksCorrectness.Statements.Routines (Δ slotStart supportCutoff)

namespace GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery EnvFactsDeliveryUpTo SyncedWithin SyncedWithinUpTo)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Record.Statements.Routines (hMax)
open GoldilocksCorrectness.Statements.Executions (Vocab.goldilocks acObject)

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
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `hU`: unforgeability; `hRoots`: roots
  name blocks; `i`, `j`: the two steps; `p`, `w`: the two holders; `B`, `B'`: the two blocks.



Read aloud: the block finalized by the chain state of a block `p` holds at step `i` is `B'` or an
ancestor of `B'`, when `B'`, held by `w` at step `j`, has a chain-state height greater than that
finalization height, both holders are honest at their steps, and fewer than a third of the
validators have been corrupted up to the later of the two times.

Roots name blocks until `tR`, at least `max x[i].time x[j].time`: the proof compares an ancestor of
`B`, held after `i` steps, with an ancestor of `B'`, held after `j` steps. -/
theorem lem68_honest_past_finalized (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {tR : ℕ}
    (hRoots : RootsNameBlocksUntil M A x tR) (i j : ℕ) (p w : V) (B B' : Block V)
    -- fewer than a third of the validators have been in the adversary set up to the later time
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V)
      (max (x.time i) (x.time j)))
    -- `p` is honest after `i` steps, and `w` after `j` steps
    (hp : p ∉ A.corrupted i) (hw : w ∉ A.corrupted j)
    -- `p` holds `B` after `i` steps, and `w` holds `B'` after `j` steps
    (hB : B ∈ (x.st i p).tree) (hB' : B' ∈ (x.st j w).tree)
    -- the chain-state height of `B'` is greater than the finalization height of `B`'s
    (hlt : (M.chainStateOf S.C B).h_F < (M.chainStateOf S.C B').h)
    -- the latest time the proof takes a block as held is at most the bound
    (htR : max (x.time i) (x.time j) ≤ tR) :
    (M.chainStateOf S.C B).F.AncestorEq B' :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem68_honest_past_finalized M F Fx) S A x R E
    hRoots i j p w B B' hThird hp hw hB hB' hlt htR

/-- **Lemma 89b over the reader's time.** From `GST + max (Δ S) Δs` on, with fewer than a third of
the validators in the adversary set up to `t`: when the step `i` is `u`'s tick at `t'` and puts
`u`'s attestation `a` on the wire, `t'` is at least one delay before `t`, `v` is awake and honest at
every time from `t − max (Δ S) Δs` to `t`, and `u` is awake and honest at every time from
`t − max (Δ S) Δs` to the later of that time and `t'`, the height of `a` is at most `v`'s greatest
chain-state height in its tick input at `t`.

Why: Lemma 89b's proof, which reads of the phase only these four facts: `a`'s height is the
chain-state height of a block `D` that `u` held (Lemma 49); `D` reaches `v` within one delay unless
it conflicts with `v`'s finalized block, and then it is at a height at most that block's
finalization height (Lemma 89a), less than `v`'s greatest chain-state height; a block `v` holds is
at a height at most that height (Lemma 46).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous;
- `t`: the clock value of `v`'s tick whose input is read; `t'`: the time of `u`'s tick; `i`: its step; `b`: the
  bound on the deadlines;
- `u`: the attester; `v`: the validator whose greatest chain-state height is read; `a`: the
  attestation.



Read aloud: from a time `t₀` after `GST` and at least one delay or one sync delay before
`t`, with `v` active from `t₀` up to its tick to `t` and `u` active from `t₀` for one sync delay, fewer
than a third of the validators corrupted up to the real time of `v`'s tick to `t`, and `u`'s attestation
sent at its tick to `t' ≤ t − Δ S`, the attestation's height is at most `v`'s greatest chain-state height at
its tick to `t`. -/
theorem lem89b_at (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST t t' i b t₀ : ℕ) (u v : V) (a : Attestation V)
    {Δs : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDeliveryUpTo A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks b) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (Sy : SyncedWithinUpTo A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST b)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep v t)))
    (hParent : ParentHeldAtDelivery M x)
    -- the window starts at `t₀`, from `GST` on, at least the recovery delay `max (Δ S) Δs` before `t`
    (hGST : GST ≤ t₀) (ht₀ : t₀ + max (Δ S) Δs ≤ t)
    -- fewer than a third of the validators have been in the adversary set up to the real time of `v`'s
    -- tick to `t`
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) (x.time (x.tickStep v t)))
    -- `t` is at least one delay after `t'`
    (ht' : t' + Δ S ≤ t)
    -- `v` is active after every step whose real time is at least `t₀`, up to its tick to `t`, which exists
    (hv : ∀ i : ℕ, (t₀ : ℝ) ≤ x.time i → i ≤ x.tickStep v t → v ∈ A.active i)
    (hvk : ∃ k : ℕ, x.lbl k = Event.tick v t)
    -- `v` ticked to the clock value one delay before `t`
    (hvt : ∃ k : ℕ, x.lbl k = Event.tick v (t - Δ S))
    -- `u` is awake and honest at every time from `t₀` for one sync delay
    (hu : u ∈ A.activeThroughout x t₀ (t₀ + Δs))
    -- the step `i` is `u`'s tick at `t'`, and put `u`'s attestation `a` on the wire
    (hSend : x.lbl i = Event.tick u t' ∧
      (⟨u, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    -- the latest deadline the proof reads is at most the bound
    (hb : t ≤ b) :
    a.h ≤ hMax M S.C (x.tickInput v t) :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem89b_at M F U Fx) S A x R GST t t' i b t₀ u v a
    E hNet hSkew hRedeliver Sy hΔs hRoots hParent hGST ht₀ hThird ht' hv hvk hvt hu hSend hb

/-- **Lemma 89b, the honest greatest chain-state height keeps up with the honest attestations.** In
the phase `[tGAT, tAwakeEnd]`, from `GST` on, every validator honest at a time of the phase awake
then and fewer than a third of the validators in the adversary set up to `tAwakeEnd`: when the step
`i` is `u`'s tick at `t'` and puts `u`'s attestation `a` on the wire, `u` is honest at the later of
`t'` and `t − max (Δ S) Δs`, and `v` is honest at a time `t` of the phase at least `max (Δ S) Δs`
into it and at least one delay after `t'`, the height of `a` is at most `v`'s greatest chain-state
height in its tick input at `t`.

Why: `a`'s height is the chain-state height of a block `D` that `u` held (Lemma 49); `D` reaches
`v` within one delay unless it conflicts with `v`'s finalized block, and then it is at a height at
most that block's finalization height (Lemma 89a), less than `v`'s greatest chain-state height; a
block `v` holds is at a height at most that height (Lemma 46).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST ≤ tGAT ≤ tAwakeEnd`: the phase;
- `t`: the clock value of `v`'s tick whose input is read; `t'`: the time of `u`'s tick; `i`: its step;
- `u`: the attester; `v`: the validator whose greatest chain-state height is read; `a`: the
  attestation.



Read aloud: in the phase, no honest validator's greatest chain-state height lags more than one delay
behind the heights honest attestations name.

Roots name blocks until the real time of `v`'s tick to `t`: `lem89b_at`, which the proof calls with
`b := t`, compares `v`'s finalized block at that tick. -/
theorem lem89b_h_max_ge_attested (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd t t' i : ℕ) (u v : V)
    (a : Attestation V)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep v t)))
    (hParent : ParentHeldAtDelivery M x)
    -- the phase starts from `GST` on
    (hGST : GST ≤ tGAT)
    -- fewer than a third of the validators have been in the adversary set up to the phase's end
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    -- every validator honest at a time of the phase is awake then
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    -- `t` is at least `max (Δ S) Δs` into the phase, and at least one delay after `t'`
    (ht : tGAT + max (Δ S) Δs ≤ t) (ht' : t' + Δ S ≤ t) (htEnd : t ≤ tAwakeEnd)
    -- `v`'s tick to `t` is in the phase
    (htEndv : x.time (x.tickStep v t) ≤ tAwakeEnd)
    -- `v` is awake and honest from `max (Δ S) Δs` before `t` to its tick to `t`
    (hv : v ∈ A.activeThroughoutToTick x ((t - max (Δ S) Δs : ℕ) : ℤ) t)
    -- `v` ticked to the clock value one delay before `t`
    (hvt : ∃ k : ℕ, x.lbl k = Event.tick v (t - Δ S))
    -- `u` is honest at the later of its tick and one sync delay after `max (Δ S) Δs` before `t`
    (hu : u ∉ A.corruptedAtTime x (max t' ((t - max (Δ S) Δs) + Δs)))
    -- the step `i` is `u`'s tick at `t'`, and put `u`'s attestation `a` on the wire
    (hSend : x.lbl i = Event.tick u t' ∧
      (⟨u, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) :
    a.h ≤ hMax M S.C (x.tickInput v t) :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem89b_h_max_ge_attested M F U Fx) S A x R GST
    tGAT tAwakeEnd t t' i u v a E hNet hSkew hRedeliver Sy hΔs hRoots hParent hGST hThird hAwake ht ht'
    htEnd htEndv hv hvt hu hSend

/-- **Lemma 89h, the threshold.** In the phase `[tGAT, tAwakeEnd]`, from `GST` on, every validator
honest at a time of the phase awake then and fewer than a third of the validators in the adversary
set up to `tAwakeEnd`, take the
round `r₀` whose first slot `s₀ ≥ 1` starts at least `max (Δ S) Δs` into the phase and whose
action time is in the phase, and the block `B₀` that `p₀`, honest at the start of slot `s₀`, put on the
wire at its tick then, with `B₀`'s parent in the viable tree of `p₀`'s frame before that start;
then every attestation an honest awake validator put on the wire at a tick before the action time
of round `r₀` has height at most `B₀`'s chain-state height plus one.

Why: such a tick is at the action time of an earlier round, so at least one delay before the start
of slot `s₀` (`R ≥ 2`); Lemma 89b bounds the attestation's height by `p₀`'s greatest chain-state
height before that start, which is at most `head_height_floor` at `p₀` plus one, and that is at
most `B₀`'s height (Lemma 58's
corollary).

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST ≤ tGAT ≤ tAwakeEnd`: the phase;
- `r₀`: the round; `s₀`: its first slot; `B₀`: the proposal; `p₀`: its proposer.



Read aloud: every honest attestation sent before the action time of the healed round has height
at most `h(B₀) + 1`.

Roots name blocks until the real time of `p₀`'s tick to the start of slot `s₀`: `lem89b_at`, which the
proof calls at `p₀`'s tick there, compares `p₀`'s finalized block at that tick. -/
theorem lem89h_threshold (U : UniformSchedule M.toSlotLayout) (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST tGAT tAwakeEnd r₀ s₀ : ℕ) (B₀ : Block V) (p₀ : V)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (x.time (x.tickStep p₀ (M.slotStart S.C s₀))))
    (hParent : ParentHeldAtDelivery M x)
    -- the phase starts from `GST` on
    (hGST : GST ≤ tGAT)
    -- fewer than a third of the validators have been in the adversary set up to the phase's end
    (hThird : A.AdversaryFewerThanThirdUntil x (validator_count V) tAwakeEnd)
    -- every validator honest at a time of the phase is awake then
    (hAwake : ∀ (i : ℕ) (v : V), x.time i ≤ tAwakeEnd → (tGAT : ℝ) ≤ x.time (i + 1) →
      v ∉ A.corrupted i → v ∈ A.awake i)
    -- `s₀` is the first slot of round `r₀`, and not slot `0`
    (hs₀ : s₀ = r₀ * S.C.R) (hs₁ : 1 ≤ s₀)
    -- slot `s₀` starts at least `max (Δ S) Δs` into the phase, and its round acts inside the phase
    (hFirst : tGAT + max (Δ S) Δs ≤ M.slotStart S.C s₀) (hEnd : M.supportCutoff S.C (s₀ + 1) ≤ tAwakeEnd)
    -- `p₀` is honest at the start of slot `s₀`
    (hp₀ : p₀ ∉ A.corruptedAtTime x (M.slotStart S.C s₀))
    -- `p₀` ticked to the clock value one delay before the start of slot `s₀`
    (hp₀t : ∃ k : ℕ, x.lbl k = Event.tick p₀ (M.slotStart S.C s₀ - Δ S))
    -- `p₀`'s tick at the start of slot `s₀` put `B₀` on the wire
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick p₀ (M.slotStart S.C s₀) ∧
      (⟨p₀, NamedObject.block B₀⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    -- `B₀`'s parent is in the viable tree of `p₀`'s frame before the start of slot `s₀`
    (hParentIn : B₀.parent ∈ M.viable_tree (M.fg_to_ac (x.tickInput p₀ (M.slotStart S.C s₀)))
      (M.fg_to_ac (x.tickInput p₀ (M.slotStart S.C s₀))).tree) :
    OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1))
      ((M.chainStateOf S.C B₀).h + 1) :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem89h_threshold M F U Fx) S A x R GST tGAT
    tAwakeEnd r₀ s₀ B₀ p₀ E hNet hSkew hRedeliver Sy hΔs hRoots hParent hGST hThird hAwake hs₀ hs₁
    hFirst hEnd hp₀ hp₀t hPropose hParentIn

/-- **The height bound from the old attestations.** Under unforgeability, with fewer than a third
of the validators in the adversary set up to the time of step `i`: when every attestation that a
validator honest at `tH` put on the wire at a tick at a step before `i` has height at most `A`, every block `D` that `v` holds after `i` steps has chain-state height at most
`A + 1`.

Why: otherwise Lemma 67 gives an ancestor `Y` of `D` at height `A + 2` whose chain includes a
certificate at height `A + 1`; its quorum has a member `u` never in the adversary set up to
`x[i].time` (Lemma 65 (b)); `u`'s attestation at height `A + 1` included on `Y`'s chain is in `u`'s
record (Lemma 74), so it was put on the wire by `u`'s own tick at a step before `i`, and `hOld` bounds
its height by `A`.

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `hU`: unforgeability;
- `i`: the step; `A`: the bound on the heights of the honest attestations; `v`: the holder;
  `D`: the block.



Read aloud: if no honest attestation put on the wire by a tick at a step before `i` is at a height
greater than `A`, every block `v` holds after step `i` has height at most `A + 1`. -/
theorem attested_height_bound (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (Act : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy Act x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (i A : ℕ) (v : V)
    (D : Block V) (tH : ℕ)
    -- the time the senders' honesty is read at is at least step `i`'s time
    (htH : x.time i ≤ tH)
    -- fewer than a third of the validators have been in the adversary set up to `tH`
    (hAdv : Act.AdversaryFewerThanThirdUntil x (validator_count V) tH)
    -- every attestation put on the wire by a tick at a step before `i`, by a validator honest at `tH`, has
    -- height at most `A`
    (hOld : ∀ (k t : ℕ) (u : V) (a : Attestation V), k < i → x.lbl k = Event.tick u t →
      u ∉ Act.corruptedAtTime x tH →
      (⟨u, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (k + 1) - x.sent k → a.h ≤ A)
    -- `v` holds `D` after `i` steps
    (hD : D ∈ (x.st i v).tree) :
    (M.chainStateOf S.C D).h ≤ A + 1 :=
  (GoldilocksCorrectness.Record.Proofs.Executions.attested_height_bound M F Fx) S Act x R E i A v D
    tH htH hAdv hOld hD

end GoldilocksCorrectness.Record.Statements.Executions

