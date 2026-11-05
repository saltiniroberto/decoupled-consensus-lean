module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma94
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma107
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma89rTargets
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.HeightAttestationStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Proofs.Executions.Lemma94
public import GoldilocksCorrectness.Proofs.Executions.Lemma89rTargets
public import GoldilocksCorrectness.Statements.Executions.HeightAttestationStatements
public import GoldilocksCorrectness.Proofs.Routines.Schedule
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# Lemma95, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Lemma95.lean`, over a model `M` whose facts
`F` hold, for an execution `x` of `protocolOf M S`: the proposer of an honest round opening slot an
honest active validator of it, and the step between the honest round opening slots of two
consecutive rounds. The page's routine-level theorems are the facts' fields or have their twins in
phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ Δ_F slotStart voteTime supportCutoff
  dutyWindowStart proposalWindowStart)
open GoldilocksCorrectness.Proofs.Routines (dutyWindowStart_mono dutyWindowStart_succ_le_slotStart
  one_le_Δ proposalWindowStart_add_Δ_F_le proposalWindowStart_eq slotStart_eq slotStart_mono
  slot_after_healed_round supportCutoff_eq supportCutoff_succ_add_Δ_F_le_slotStart voteTime_eq)

namespace GoldilocksCorrectness.Record.Proofs.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery EnvFactsSync SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Proofs.Executions (mem_awakeThroughout_of_forall)

open GoldilocksCorrectness.Record.Statements.Routines (AwakeFor hMax le_hMax IsEntry VoterTreeAt JustifiedInTree AnchorAt)

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (Vocab.goldilocks acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (expireLocks)
open GoldilocksCorrectness.Proofs.Routines (ancestorEq_refl ancestorEq_trans compatible_iff)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

-- An index `x[i]` into an execution has the valid-index predicate `fun _ _ => True`; this rule,
-- local to the file, proves it at once.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- `omega` after the `abbrev`s `Height` and `Slot` are unfolded in the goal and in every
hypothesis: `omega` does not see a fact stated at either. -/
local macro "omega_nat" : tactic =>
  `(tactic| ((try dsimp only) <;> (try unfold Height at *) <;> (try unfold Slot at *) <;> omega))

/-! ## The members' justified height, and the delivery to the pool -/

/-- **Kit fact, `attested_height_bound` with the quorum bound.** A block `D` that `v` holds after
step `i` has a chain-state height at most `A + 1`, when fewer than a quorum of validators have been
in the adversary set up to the time of step `i` and every honest attestation sent at a tick to a
clock value less than `t₀` has height at most `A`, for a `t₀` greater than the time of step `i` plus
`ΔClockAhead` (the most a validator's clock runs ahead of real time).

Why: as `attested_height_bound` (`Proofs/Executions/PhaseFrame.lean`): an ancestor of `D` at height
`A + 2` carries a certificate at height `A + 1` (Lemma 67); its quorum has a member honest through
the time of step `i`, since fewer than a quorum are in the adversary set; that member's attestation
at height `A + 1` is in its record (Lemma 74), so its own tick sent it before step `i`, against the
bound. The quorum form sits beside the form with the third bound.

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed;
- `S`, `Act`, `x`: the setup, the activity, the execution; `R`: the run's facts; `E`: the delivery
  promise; `i`: the step; `A`: the bound; `v`: the holder; `D`: the block.

Read aloud: a held block is at most one height higher than every honest attestation sent so far,
when fewer than a quorum have been corrupted. -/
theorem attested_height_bound_quorum (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (Act : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy Act x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (i A : ℕ) (v : V)
    (D : Block V)
    (tH : ℕ) (htH : x.time i ≤ tH)
    (hAdvQ : Act.AdversaryFewerThanQuorumUntil x (quorum V) tH)
    -- the old attestations are read up to a time `t₀` greater than the time of step `i` plus
    -- `ΔClockAhead`: a tick before step `i` is to a clock value at most that
    (t₀ : ℝ) (ht₀ : x.time i + ΔClockAhead < t₀)
    (hOld : OldAttestationsAtMostHonestAt M S Act x t₀ tH A)
    (hD : D ∈ (x.st i v).tree) :
    (M.chainStateOf S.C D).h ≤ A + 1 := by
  by_contra hcon
  have hlt : A + 1 < (M.chainStateOf S.C D).h := Nat.lt_of_not_le hcon
  obtain ⟨Y, hYD, -, -, -, -, X, hXY, Q, hQ, hQm⟩ :=
    (GoldilocksCorrectness.Record.Statements.Routines.lem67_first_advance M F) S.C D (A + 1) (Nat.succ_pos A) hlt
  have hY := (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S Act x R E i v D Y hD hYD
  have hX := (GoldilocksCorrectness.Record.Statements.Executions.ancestors_mem_T_of_exec M F) S Act x R E i v Y X hY hXY
  rw [GoldilocksCorrectness.Record.quorumAt_eq_quorum Fx F.sched X] at hQ
  -- the certificate's quorum has a member `u` honest through the time of step `i` (the quorum bound)
  obtain ⟨u, huQ, hHuH⟩ : ∃ u ∈ Q, Act.HonestThroughTime x tH u := by
    by_contra hno
    have hall : ∀ w ∈ Q, ∃ k : ℕ, x.time k ≤ tH ∧ w ∈ Act.corrupted k := by
      intro w hw
      by_contra hn
      exact hno ⟨w, hw, fun k hk ha => hn ⟨k, hk, ha⟩⟩
    have h3 := hAdvQ Q hall
    omega
  have hHu : x.HonestThrough Act i u := (honestThrough_of_time_le M F) x R hHuH htH
  obtain ⟨b, hbu, hbh, -, hon⟩ := hQm u huQ
  have hrec := (lem74_honest_attestations_recorded M F) S Act x R E i v X b hX hon
    (by rw [hbu]; exact hHu)
  rw [hbu] at hrec
  obtain ⟨j, t', a', hj, hl, -, hsent, -, hcont, -⟩ :=
    (record_content_sent_step M F) S Act x R E u i b.content hrec
  have ht' : (t' : ℝ) < t₀ := by
    have h1 := ((time_of_lbl_tick M) x R E hl).1.1
    have h2 := (time_mono M) x R (show j ≤ i by omega)
    linarith
  have ha' := hOld j t' u a' hl ht'
    (Activity.not_mem_corruptedAtTime.2 fun k hk => hHuH k hk) hsent
  have hab : a'.h = b.h := congrArg AttestationContent.h hcont
  rw [hab, hbh] at ha'
  exact Nat.not_succ_le_self A ha'

/-- **Kit fact, a justified height bounded by the old honest attestations.** Every validator's
justified height before a time `t`, honest or not, is at most `Hh` when every honest attestation
sent at a tick to a clock value less than a later time `c`, with `t + ΔClockAhead < c`, has height at
most `Hh` and fewer than a quorum of validators are ever in the adversary set.

Why: the caches witness a block `D` of the validator's tree whose chain state's justification
height is the justified height (`cachesWitnessed_of_exec`); Lemma 47 puts it less than `D`'s height,
which is at most `Hh + 1` by `attested_height_bound_quorum`.

The variables:
- `M`: the model; `F`: its facts; `Fx`: its validators are fixed;
- `S`, `A`, `x`: the setup, the activity, the execution; `R`: the run's facts; `E`: the delivery
  promise; `t`: the time; `c`: the bound's time; `Hh`: the bound; `u`: the validator.

Read aloud: no validator has justified past the height every honest attestation so far is at most. -/
theorem justifiedHeight_le_of_oldAttestations (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (t c Hh : ℕ) (u : V)
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) c)
    (hOld : OldAttestationsAtMostHonestAt M S A x c c Hh) (hc : t < c)
    -- `t` plus the most a validator's clock runs ahead of real time is at most `c`
    (hcA : (t : ℝ) + ΔClockAhead < c) :
    M.justifiedHeight (x.stateBefore t u) ≤ Hh := by
  have hti := (time_stepBefore_le M) x R E t
  obtain ⟨⟨D, hD, -, hj⟩, -, -⟩ := (cachesWitnessed_of_exec M F) S A x R E (x.stepBefore t) u
  have hDh := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C D D).1.2.1
  have hb := attested_height_bound_quorum M F Fx S A x R E (x.stepBefore t) Hh u D c
    (by have : (t : ℝ) < c := by exact_mod_cast hc
        linarith) (hAdvQ.mono le_rfl) c (by linarith) hOld hD
  show (x.st (x.stepBefore t) u).justifiedHeight ≤ Hh
  rw [hj]
  unfold Height at *
  omega

/-- **Kit fact, a delivered attestation is in the pool.** An attestation `v`'s tick at `t'` put on
the wire, delivered to `q` at a step `d` before `q`'s last step before `t₁`, is in `q`'s pool before
`t₁`.

Why: the tick's attestation is well formed (`tick_attestation_well_formed`); the receive at `d`
admits it to the pool (`receive_attestation_held`), which only grows.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `A`, `x`: the setup, the activity, the execution; `R`: the run's facts; `E`: the delivery
  promise; `t₁`: the time the pool is read before; `q`: the receiver;
- `j`, `t'`: the step and the time of the send; `v`: the sender; `a`: the attestation.

Read aloud: an attestation a tick sent and delivered to `q` before `t₁` is in `q`'s pool before
`t₁`. -/
theorem attestation_in_pool_of_delivery (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (t₁ : ℕ) (q : V) (j t' : ℕ) (v : V) (a : Attestation V)
    (hl : x.lbl j = Event.tick v t')
    (hsent : (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (j + 1) - x.sent j)
    (hdel : ∃ d : ℕ, x.lbl d = Event.deliver q ⟨v, NamedObject.attest a⟩ ∧ d < x.stepBefore t₁) :
    a ∈ (x.stateBefore t₁ q).attestationsHeld := by
  obtain ⟨d, hld, hd⟩ := hdel
  have hWF := (tick_attestation_well_formed M F) S A x R E j t' v a hl hsent
  obtain ⟨-, hstep⟩ := (deliver_step_state M F) x R E hld
  have hin : a ∈ (x.st (d + 1) q).attestationsHeld := by
    rw [hstep]
    exact F.rcv.receive_attestation_held S.C S.P S.X _ a hWF
  exact (pool_grows_of_le M F) x R E q hd a hin

/-- **Kit fact, an attestation delivered or already held is in the pool.** An attestation `v`'s tick
at `t'` put on the wire, delivered to `q` at a step before `q`'s last step before `t₁`, or among
`q`'s attestations before `tq ≤ t₁`, is in `q`'s pool before `t₁`.

Why: the first case is `attestation_in_pool_of_delivery`; in the second, `q`'s pool only grows
(`pool_grows_of_le`) from its last step before `tq` to its last step before `t₁`
(`stepBefore_mono`). The form the consumers of Lemma 98's premise `hDelF` read.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `A`, `x`: the setup, the activity, the execution; `R`: the run's facts; `E`: the delivery
  promise; `tq`: the time the attestation may already be held before; `t₁`: the time the pool is
  read before; `q`: the receiver;
- `j`, `t'`: the step and the time of the send; `v`: the sender; `a`: the attestation.

Read aloud: an attestation a tick sent, delivered to `q` before `t₁` or held by `q` before
`tq ≤ t₁`, is in `q`'s pool before `t₁`. -/
theorem attestation_in_pool_of_delivery_or_held (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (tq t₁ : ℕ) (htq : tq ≤ t₁) (q : V) (j t' : ℕ) (v : V) (a : Attestation V)
    (hl : x.lbl j = Event.tick v t')
    (hsent : (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (j + 1) - x.sent j)
    (hdel : (∃ d : ℕ, x.lbl d = Event.deliver q ⟨v, NamedObject.attest a⟩ ∧ d < x.stepBefore t₁) ∨
      a ∈ (x.stateBefore tq q).attestationsHeld) :
    a ∈ (x.stateBefore t₁ q).attestationsHeld := by
  rcases hdel with hdel | hheld
  · exact (attestation_in_pool_of_delivery M F) S A x R E hNet hSkew hRedeliver t₁ q j t' v a hl hsent hdel
  · exact (pool_grows_of_le M F) x R E q ((stepBefore_mono M) x R E htq) a hheld

/-- **Kit fact, an attestation delivered before the receiver's tick or already held is in the
tick's input.** An attestation `v`'s tick at `t'` put on the wire, delivered to `q` at a step before
`q`'s tick to the clock value `c`, or among `q`'s attestations before `tq`, where `q`'s last step
before `tq` is not after that tick, is in `q`'s pool in the state its tick to `c` reads.

Why: the first case as `attestation_in_pool_of_delivery`, the receive at `d` admitting it to the
pool, which only grows (`pool_grows_of_le`) from `d + 1` to the tick's step; in the second, the pool
grows from `q`'s last step before `tq` to the tick's step (`hle`). The tick-input twin of
`attestation_in_pool_of_delivery_or_held`, for the delivery line `hDel` of Lemmas 95 and
96 read at the opener's tick: the proposal of a slot is computed on the
opener's tick input to the slot's start.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `A`, `x`: the setup, the activity, the execution; `R`: the run's facts; `E`: the delivery
  promise; `tq`: the time the attestation may already be held before; `q`: the receiver; `c`: the
  clock value of `q`'s tick; `hle`: `q`'s last step before `tq` is at most that tick's step;
- `j`, `t'`: the step and the time of the send; `v`: the sender; `a`: the attestation.

Read aloud: an attestation a tick sent, delivered to `q` before `q`'s tick to `c` or held by `q`
before `tq`, with `q`'s last step before `tq` not after that tick, is in `q`'s pool when it ticks
to `c`. -/
theorem attestation_in_tickInput_of_delivery_or_held (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    (tq : ℕ) (q : V) (c : ℕ) (hle : x.stepBefore tq ≤ x.tickStep q c) (j t' : ℕ) (v : V) (a : Attestation V)
    (hl : x.lbl j = Event.tick v t')
    (hsent : (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (j + 1) - x.sent j)
    (hdel : (∃ d : ℕ, x.lbl d = Event.deliver q ⟨v, NamedObject.attest a⟩ ∧ d < x.tickStep q c) ∨
      a ∈ (x.stateBefore tq q).attestationsHeld) :
    a ∈ (x.tickInput q c).attestationsHeld := by
  show a ∈ (x.st (x.tickStep q c) q).attestationsHeld
  rcases hdel with ⟨d, hld, hd⟩ | hheld
  · have hWF := (tick_attestation_well_formed M F) S A x R E j t' v a hl hsent
    obtain ⟨-, hstep⟩ := (deliver_step_state M F) x R E hld
    have hin : a ∈ (x.st (d + 1) q).attestationsHeld := by
      rw [hstep]
      exact F.rcv.receive_attestation_held S.C S.P S.X _ a hWF
    exact (pool_grows_of_le M F) x R E q hd a hin
  · exact (pool_grows_of_le M F) x R E q hle a hheld

/-- **Kit theorem, a round's attestation reaches the next opener, by the sync fact.** For a round
`r'` whose next round's first slot `s' = (r' + 1) * R` is an honest round opening slot, with `GST`
at least `4Δ(k + 1)` before the delay after the start of `s'` (so `GST` is at or before the proposal
window's start of `s'`, and that window is not cut at `0`): an attestation that `u`, active at that
proposal window's start, put on the wire at a tick up to the round's action time, outside the
adversary set then, and whose height is at least `u`'s justified height at the proposal window's
start, is delivered to the proposer of `s'` before its tick to the start of `s'`, or is held
by that proposer before the proposal window's start of `s'`.

Why: `attestation_delivered_of_tick_send` with `tq` the proposal window's start of `s'` and `t₁` the
start of `s'`, the send bounded by the later of the round's action time and `tq`. The deadlines: the
action time plus `Δ_F` is at most the start of `s'` (`supportCutoff_succ_add_Δ_F_le_slotStart`); the
proposal window's start plus `Δ_F` (`hParam`) and plus `Δs_F` (`hΔs_F`) is at most it. The proposer
of `s'` is active at every step from the window's start to its tick to the start of `s'`: before the
start of `s'` minus `ΔClockAhead` by `hHoldQ`, which covers the steps before its wake tick
when that tick is at a real time after the window's start, and from then on by `HonestOpenerAt`. The second
case is the sync fact's case of a receiver that already holds the attestation; it covers
`u` being the proposer of `s'` itself, to which nothing delivers its own attestation. The delivery
line `hDelF` of the restated Lemma 98 is built from it at the corollary with the sync fact.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`: the setup, the activity, the execution; `R`: the run's facts; `GST`: the time from
  which the network is synchronous; `r'`: the round; `E`, `E_F`: the delivery promises; `Sy_F`: the
  sync fact for attestations, with the sync delay `Δs_F`;
- `u`: the sender; `j`, `t'`: the step and the time of the send; `a`: the attestation.

Read aloud: after `GST`, a round's attestation whose sender is still active, and still serves it,
when the next opener's proposal window opens reaches that opener before its slot, when that opener is
active at every step from its proposal window's start to its slot's start. -/
theorem attestations_reach_opener_of_sync (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST r' : ℕ)
    {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {ΔNet_F : ℕ} (E_F : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)
    {Δs_F : ℕ} (Sy_F : SyncedWithin A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST)
    (hΔs_F : (Δs_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S ∨ (Δs_F : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind ≤ 4 * Δ S * S.C.k)
    (hParam : (Δ_F S : ℝ) + Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * (S.C.k + 1))
    -- `GST` is at least `4Δ(k + 1)` before one delay after the start of slot `(r' + 1) * R`
    (hGSTw : GST + 4 * Δ S * (S.C.k + 1) ≤ M.slotStart S.C ((r' + 1) * S.C.R) + Δ S)
    (hOpener' : HonestOpenerAt M S A x ((r' + 1) * S.C.R))
    -- the next opener is active at every step at a real time from its proposal window's start to its slot's start
    --
    (hHoldQ : S.P.proposer ((r' + 1) * S.C.R) ∈ A.activeThroughout x ((M.proposalWindowStart S.C ((r' + 1) * S.C.R) : ℕ) : ℝ)
      ((M.slotStart S.C ((r' + 1) * S.C.R) : ℕ) : ℝ))
    (u : V)
    (hu : u ∈ A.activeThroughout x (M.proposalWindowStart S.C ((r' + 1) * S.C.R))
      ((M.proposalWindowStart S.C ((r' + 1) * S.C.R) : ℕ) + Δs_F))
    (j t' : ℕ) (a : Attestation V) (hl : x.lbl j = Event.tick u t')
    (ht' : t' ≤ M.supportCutoff S.C (r' * S.C.R + 1))
    (hsent : (⟨u, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (j + 1) - x.sent j)
    (hjust : M.justifiedHeight (x.stateBefore (M.proposalWindowStart S.C ((r' + 1) * S.C.R)) u) ≤ a.h) :
    (∃ d : ℕ, x.lbl d = Event.deliver (S.P.proposer ((r' + 1) * S.C.R)) ⟨u, NamedObject.attest a⟩ ∧
      d < x.tickStep (S.P.proposer ((r' + 1) * S.C.R)) (M.slotStart S.C ((r' + 1) * S.C.R))) ∨
    a ∈ (x.stateBefore (M.proposalWindowStart S.C ((r' + 1) * S.C.R)) (S.P.proposer ((r' + 1) * S.C.R))).attestationsHeld := by
  have hΔ := one_le_Δ S
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  have hR := S.C.R_ge_two
  obtain ⟨q0, hq0⟩ : ∃ q0 : ℕ, (r' + 1) * S.C.R = q0 + 2 := by
    have : 1 * S.C.R ≤ (r' + 1) * S.C.R := Nat.mul_le_mul_right _ (by omega)
    exact ⟨(r' + 1) * S.C.R - 2, by omega⟩
  -- the real values of the times involved
  have hst : M.slotStart S.C ((r' + 1) * S.C.R) = 4 * Δ S * ((r' + 1) * S.C.R) :=
    (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S _
  have hstR : ((M.slotStart S.C ((r' + 1) * S.C.R) : ℕ) : ℝ) = 4 * (Δ S : ℝ) * (((r' + 1) * S.C.R : ℕ) : ℝ) := by
    rw [hst]; push_cast; ring
  have hpwR : ((proposal_window_start S.C ((r' + 1) * S.C.R) : ℤ) : ℝ) =
      4 * (Δ S : ℝ) * (((r' + 1) * S.C.R : ℕ) : ℝ) + Δ S - 4 * (Δ S : ℝ) * ((S.C.k : ℝ) + 1) := by
    rw [hq0, GoldilocksCorrectness.Proofs.Routines.proposal_window_start_eq S q0, duty_window_start_real S (q0 + 1)]
    push_cast; ring
  have hcut := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_succ_add_Δ_F_le_slotStart
    M.toSlotLayout F.sched) S (r' * S.C.R)
  rw [show r' * S.C.R + S.C.R = (r' + 1) * S.C.R by rw [Nat.add_mul, Nat.one_mul]] at hcut
  have hk1R : (4 * Δ S * (S.C.k + 1) : ℝ) = 4 * (Δ S : ℝ) * ((S.C.k : ℝ) + 1) := by ring
  rw [hk1R] at hParam
  set q := S.P.proposer ((r' + 1) * S.C.R) with hqdef
  set c' := M.slotStart S.C ((r' + 1) * S.C.R) with hc'def
  set pws := M.proposalWindowStart S.C ((r' + 1) * S.C.R) with hpwsdef
  have hc'1 : 1 ≤ c' := by
    rw [hst]; have : 1 ≤ (r' + 1) * S.C.R := by omega
    exact Nat.one_le_iff_ne_zero.2 (by positivity)
  -- the proposal window's start of `s'` is `4Δ(k + 1)` before one delay after `c'`, and at or after `GST`
  have hpw := U.proposalWindowStart_eq S ((r' + 1) * S.C.R)
  have hpwN : pws + 4 * Δ S * (S.C.k + 1) = c' + Δ S := by omega
  have hGSTpw : GST ≤ pws := by omega
  have hpwNR : ((pws : ℕ) : ℝ) + 4 * (Δ S : ℝ) * ((S.C.k : ℝ) + 1) = (c' : ℝ) + Δ S := by
    have : ((pws + 4 * Δ S * (S.C.k + 1) : ℕ) : ℝ) = ((c' + Δ S : ℕ) : ℝ) := by rw [hpwN]
    push_cast at this; linarith
  -- the deadlines: `pws` plus the longer of the two attestation delays is at most `c'` (`hParam`, `hΔs_F`)
  have hFN : pws + Δ_F S ≤ c' := by
    have : ((pws + Δ_F S : ℕ) : ℝ) ≤ ((c' : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have hsFN : pws + Δs_F ≤ c' := by
    have : ((pws + Δs_F : ℕ) : ℝ) ≤ ((c' : ℕ) : ℝ) := by
      push_cast
      have hΔ1 : (1 : ℝ) ≤ Δ S := by exact_mod_cast hΔ
      rcases hΔs_F with h | h
      · linarith
      · have hkk : (4 * Δ S * S.C.k : ℝ) = 4 * (Δ S : ℝ) * ((S.C.k : ℝ) + 1) - 4 * Δ S := by ring
        linarith
    exact_mod_cast this
  have hmaxN : pws + max (Δ_F S) Δs_F ≤ c' := by
    rcases le_total (Δ_F S) Δs_F with h | h
    · rw [max_eq_right h]; exact hsFN
    · rw [max_eq_left h]; exact hFN
  -- the proposer `q` of `s'` ticks to `c'` at `kQ`; from `c' − ΔClockAhead` on it is active up to its tick to the
  -- support cutoff of `s' + 1` (`HonestOpenerAt`)
  have hcut1 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S ((r' + 1) * S.C.R + 1)
  have hvt1 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S ((r' + 1) * S.C.R + 1)
  have hst1 : M.slotStart S.C ((r' + 1) * S.C.R + 1) = c' + 4 * Δ S := by
    rw [hc'def, (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U),
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add, Nat.mul_one]
  have hcut1R : ((M.supportCutoff S.C ((r' + 1) * S.C.R + 1) : ℕ) : ℝ) = (c' : ℝ) + 6 * Δ S := by
    have : M.supportCutoff S.C ((r' + 1) * S.C.R + 1) = c' + 6 * Δ S := by omega
    rw [this]; push_cast; ring
  obtain ⟨kR, hkR, hwinR⟩ := (tick_window_of_activeThroughoutToTick_int M) x R E hOpener'.1
    (t₀ := (c' : ℝ) - ΔClockAhead) (by rw [hpwR]; rw [← hstR] at *; linarith)
  have hkRt := (E.tick_active kR q _ hkR).2.1
  obtain ⟨kQ, hkQ, hkQ1, hkQ2⟩ := E.tick_of_active c' hc'1 q (fun i h1 h2 => hwinR i h1
    ((lt_of_time_lt M) x R (by rw [hcut1R] at hkRt; linarith)).le)
  have hkQeq : x.tickStep q c' = kQ := (tickStep_eq_of_lbl M) x E hkQ
  rw [hkQeq]
  have hkQt := (E.tick_active kQ q c' hkQ).2.1
  have hkQkR : kQ ≤ kR := ((lt_of_time_lt M) x R (by rw [hcut1R] at hkRt; linarith)).le
  -- `q` is active at every step from the real time `pws` up to `kQ`: before `c' − ΔClockAhead` by `hHoldQ`
  --, from it on by `HonestOpenerAt`
  have hwin : ∀ i : ℕ, ((pws : ℕ) : ℝ) ≤ x.time i → i ≤ kQ → q ∈ A.active i := by
    intro i hi hik
    by_cases hc : (c' : ℝ) - ΔClockAhead ≤ x.time i
    · exact hwinR i hc (hik.trans hkQkR)
    · exact (Activity.mem_activeThroughout).1 hHoldQ i (by linarith) (le_trans hi (htime (Nat.le_succ i)))
  -- the step before `pws` is the one every step at a real time less than `pws` leads to
  have hsb : ∀ k : ℕ, x.time k < ((pws : ℕ) : ℝ) → ((pws : ℕ) : ℝ) ≤ x.time (k + 1) → x.stepBefore pws = k := by
    intro k hk1 hk2
    apply le_antisymm
    · by_contra hlt
      have := ((lt_stepBefore_iff M) x R E).1 (Nat.lt_of_not_le hlt)
      linarith
    · by_contra hlt
      have h1 := (le_time_stepBefore_succ M) x R E pws
      have := htime (show x.stepBefore pws + 1 ≤ k by omega)
      linarith
  -- the sync fact read at `pws`: the send is at most the later of the round's action time and `pws`
  have hcutN : M.supportCutoff S.C (r' * S.C.R + 1) + Δ_F S ≤ c' := hcut
  rcases (attestation_delivered_of_tick_send M F) S A x R GST (max (M.supportCutoff S.C (r' * S.C.R + 1)) pws) c'
      ((pws : ℕ) : ℝ) q E hNet hSkew hRedeliver E_F hNet_F hSkew_F Sy_F
      (le_max_of_le_right hGSTpw) (by rcases le_total (M.supportCutoff S.C (r' * S.C.R + 1)) pws with h | h <;>
        [rw [max_eq_right h]; rw [max_eq_left h]] <;> omega)
      (by omega) (by exact_mod_cast hmaxN) kQ hkQ hwin j t' u a hl (le_max_of_le_left ht') hsent
      (fun _ => by rw [Nat.ceil_natCast]; exact hu)
      (fun _ k hk1 hk2 => by rw [← hsb k hk1 hk2]; exact hjust) with h | ⟨-, k, hk1, hk2, hka⟩
  · exact Or.inl h
  · right
    show a ∈ (x.st (x.stepBefore pws) q).attestationsHeld
    rw [hsb k hk1 hk2]
    exact hka

/-- **Kit theorem, a round's attestation reaches the next opener, by the catch-up promise.** For a
round `r'` whose next round's first slot `s' = (r' + 1) * R` is an honest round opening slot, with
`GST` at least `4Δ(k + 1)` before the delay after the start of `s'`: an attestation that `u`, outside
the adversary set then, put on the wire at a tick up to the round's action time is delivered to the
proposer of `s'` before its tick to the start of `s'`, when attestations are delivered
within `Δ_F` after the later of their time and `GST`, and a validator that wakes is delivered its
backlog within `Δw_F` after the later of its wake and `GST`, with the longer of `Δ_F` and `Δw_F`
plus one delay at most `4Δ(k + 1)`.

Why: the proposer of `s'` is awake and outside the adversary set from its proposal window's start
`t₀` through the start of `s'` (`HonestOpenerAt`). `delivered_before_stepBefore_of_honest_send` with
the deadline the start of `s'`: the send is at least `Δ_F` before it (the action time plus `Δ_F` is
at most the start of `s'`), and `t₀` and `GST` are each at least `Δw_F` before it (`hParam`,
`GST ≤ t₀`). No condition on `u` after the send is needed.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `A`, `x`: the setup, the activity, the execution; `R`: the run's facts; `GST`: the time from
  which the network is synchronous; `r'`: the round; `E`: the delivery promise for blocks and votes;
  `E_F`: the delivery and catch-up promises for attestations, with the catch-up delay `Δw_F`; `hWS`:
  the trace is wake-shaped;
- `u`: the sender; `j`, `t'`: the step and the time of the send; `a`: the attestation.

Read aloud: after `GST`, when a waking validator is caught up within `Δw_F`, a round's attestation
reaches the next opener before its slot. -/
theorem attestations_reach_opener_of_catchUp (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST r' : ℕ)
    {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {Δw_F : ℕ}
    {ΔNet_F : ℕ} (E_F : EnvFactsSync A x ΔClockAhead ΔClockBehind ΔNet_F Δw_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)

    -- the longer of the attestation delay and the attestation catch-up delay, plus one delay and the two clock
    -- bounds, is less than `4Δ(k + 1)`
    (hParam : (max (Δ_F S) Δw_F : ℝ) + Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * (S.C.k + 1))
    -- `GST` is at least `4Δ(k + 1)` before one delay after the start of slot `(r' + 1) * R`
    (hGSTw : GST + 4 * Δ S * (S.C.k + 1) ≤ M.slotStart S.C ((r' + 1) * S.C.R) + Δ S)
    (hOpener' : HonestOpenerAt M S A x ((r' + 1) * S.C.R))
    (u : V) (j t' : ℕ) (a : Attestation V) (hl : x.lbl j = Event.tick u t')
    (ht' : t' ≤ M.supportCutoff S.C (r' * S.C.R + 1))
    (hsent : (⟨u, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (j + 1) - x.sent j)
    -- `u`'s justified height at the next proposal window's start is at most the attestation's height
    -- (not needed by the proof)
    (_hjust : M.justifiedHeight (x.stateBefore (M.proposalWindowStart S.C ((r' + 1) * S.C.R)) u) ≤ a.h) :
    ∃ d : ℕ, x.lbl d = Event.deliver (S.P.proposer ((r' + 1) * S.C.R)) ⟨u, NamedObject.attest a⟩ ∧
      d < x.tickStep (S.P.proposer ((r' + 1) * S.C.R)) (M.slotStart S.C ((r' + 1) * S.C.R)) := by
  have hΔ := one_le_Δ S
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have htime : Monotone x.time := fun _ _ h => R.time_mono h
  have hR := S.C.R_ge_two
  obtain ⟨q0, hq0⟩ : ∃ q0 : ℕ, (r' + 1) * S.C.R = q0 + 2 := by
    have : 1 * S.C.R ≤ (r' + 1) * S.C.R := Nat.mul_le_mul_right _ (by omega)
    exact ⟨(r' + 1) * S.C.R - 2, by omega⟩
  -- the real values of the times involved
  have hst : M.slotStart S.C ((r' + 1) * S.C.R) = 4 * Δ S * ((r' + 1) * S.C.R) :=
    (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S _
  have hstR : ((M.slotStart S.C ((r' + 1) * S.C.R) : ℕ) : ℝ) = 4 * (Δ S : ℝ) * (((r' + 1) * S.C.R : ℕ) : ℝ) := by
    rw [hst]; push_cast; ring
  have hpwR : ((proposal_window_start S.C ((r' + 1) * S.C.R) : ℤ) : ℝ) =
      4 * (Δ S : ℝ) * (((r' + 1) * S.C.R : ℕ) : ℝ) + Δ S - 4 * (Δ S : ℝ) * ((S.C.k : ℝ) + 1) := by
    rw [hq0, GoldilocksCorrectness.Proofs.Routines.proposal_window_start_eq S q0, duty_window_start_real S (q0 + 1)]
    push_cast; ring
  have hcut := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_succ_add_Δ_F_le_slotStart
    M.toSlotLayout F.sched) S (r' * S.C.R)
  rw [show r' * S.C.R + S.C.R = (r' + 1) * S.C.R by rw [Nat.add_mul, Nat.one_mul]] at hcut
  have hcutR : ((M.supportCutoff S.C (r' * S.C.R + 1) : ℕ) : ℝ) + Δ_F S ≤ ((M.slotStart S.C ((r' + 1) * S.C.R) : ℕ) : ℝ) := by
    exact_mod_cast hcut
  have hGSTR : (GST : ℝ) + 4 * Δ S * ((S.C.k : ℝ) + 1) ≤ ((M.slotStart S.C ((r' + 1) * S.C.R) : ℕ) : ℝ) + Δ S := by
    exact_mod_cast hGSTw
  have hmxF : (Δ_F S : ℝ) ≤ (max (Δ_F S) Δw_F : ℝ) := by exact_mod_cast le_max_left (Δ_F S) Δw_F
  have hmxW : (Δw_F : ℝ) ≤ (max (Δ_F S) Δw_F : ℝ) := by exact_mod_cast le_max_right (Δ_F S) Δw_F
  have hk1R : (4 * Δ S * (S.C.k + 1) : ℝ) = 4 * (Δ S : ℝ) * ((S.C.k : ℝ) + 1) := by ring
  rw [hk1R] at hParam
  -- the proposer `q` of `s'` ticks to the start of `s'` at `kQ`, at a real time at least that start minus
  -- `ΔClockAhead`: it is active from a real time before it up to its tick to the support cutoff of `s' + 1`
  set q := S.P.proposer ((r' + 1) * S.C.R) with hqdef
  set c' := M.slotStart S.C ((r' + 1) * S.C.R) with hc'def
  have hc'1 : 1 ≤ c' := by
    rw [hst]; have : 1 ≤ (r' + 1) * S.C.R := by omega
    exact Nat.one_le_iff_ne_zero.2 (by positivity)
  have hcut1 := (GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S ((r' + 1) * S.C.R + 1)
  have hvt1 := (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S ((r' + 1) * S.C.R + 1)
  have hst1 : M.slotStart S.C ((r' + 1) * S.C.R + 1) = c' + 4 * Δ S := by
    rw [hc'def, (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U),
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U), Nat.mul_add, Nat.mul_one]
  have hcut1R : ((M.supportCutoff S.C ((r' + 1) * S.C.R + 1) : ℕ) : ℝ) = (c' : ℝ) + 6 * Δ S := by
    have : M.supportCutoff S.C ((r' + 1) * S.C.R + 1) = c' + 6 * Δ S := by omega
    rw [this]; push_cast; ring
  obtain ⟨kR, hkR, hwinR⟩ := (tick_window_of_activeThroughoutToTick_int M) x R E hOpener'.1
    (t₀ := (c' : ℝ) - ΔClockAhead) (by rw [hpwR]; rw [← hstR] at *; linarith)
  have hkRt := (E.tick_active kR q _ hkR).2.1
  obtain ⟨kQ, hkQ, hkQ1, hkQ2⟩ := E.tick_of_active c' hc'1 q (fun i h1 h2 => hwinR i h1
    ((lt_of_time_lt M) x R (by rw [hcut1R] at hkRt; linarith)).le)
  have hkQeq : x.tickStep q c' = kQ := (tickStep_eq_of_lbl M) x E hkQ
  rw [hkQeq]
  have hqkQ : q ∈ A.active kQ := (E.tick_active kQ q c' hkQ).1
  have hqaw : q ∈ A.awake kQ := Activity.mem_awake_of_mem_active hqkQ
  have hqh : q ∉ A.corrupted kQ := Activity.not_mem_corrupted_of_mem_active hqkQ
  -- the send: by `u`, honest at it, at a real time at most the round's action time plus `ΔClockBehind`
  have hhon : u ∉ A.corrupted j := E.not_mem_corrupted_of_tick hl
  obtain ⟨⟨-, hTj⟩, -, hTj1⟩ := (time_of_lbl_tick M) x R E hl
  have ht'R : (t' : ℝ) ≤ ((M.supportCutoff S.C (r' * S.C.R + 1) : ℕ) : ℝ) := by exact_mod_cast ht'
  have hjkQ : j < kQ := (lt_of_time_lt M) x R (by linarith)
  -- the message's ordinary deadline is at most `c' − ΔClockAhead`, so at most the time of `kQ`
  have hdl : max (x.time (j + 1)) (GST : ℝ) + ΔNet_F ≤ (c' : ℝ) - ΔClockAhead := by
    rcases le_total (x.time (j + 1)) (GST : ℝ) with h' | h'
    · rw [max_eq_right h']; linarith
    · rw [max_eq_left h']; linarith
  -- an attestation has no release clock value: the re-delivery premises are empty
  have hrel : ∀ (rr j₀ k₁ t₁ : ℕ), releaseOf M S.C (NamedObject.attest a) = some rr → j < j₀ →
      x.lbl j₀ = Event.deliver q ⟨u, NamedObject.attest a⟩ → ¬ x.ReactedAtLeast j₀ q rr → j₀ < k₁ → k₁ ≤ kQ →
      x.lbl k₁ = Event.tick q t₁ → rr ≤ t₁ →
      (∀ (l t'' : ℕ), j₀ < l → l < k₁ → x.lbl l = Event.tick q t'' → t'' < rr) →
      x.time (k₁ + 1) + ΔRedeliver ≤ x.time kQ :=
    fun _ _ _ _ hr => absurd hr (by simp [releaseOf])
  by_cases hrs : ∃ rr : ℕ, j < rr ∧ rr < kQ ∧ ∃ (tR : ℕ) (keep : Bool), x.lbl rr = Event.restart q tR keep
  · -- the last restart `rr` of `q` before `kQ`, after the send: the catch-up promise
    obtain ⟨rr, ⟨hjr, hrkQ, tR, keep, hlr⟩, hmax⟩ : ∃ rr : ℕ,
        (j < rr ∧ rr < kQ ∧ ∃ (tR : ℕ) (keep : Bool), x.lbl rr = Event.restart q tR keep) ∧
        ∀ r'' : ℕ, rr < r'' → r'' ≤ kQ →
          ¬ (j < r'' ∧ r'' < kQ ∧ ∃ (tR : ℕ) (keep : Bool), x.lbl r'' = Event.restart q tR keep) := by
      classical
      obtain ⟨rr, hr⟩ := hrs
      exact ⟨Nat.findGreatest (fun rr => j < rr ∧ rr < kQ ∧ ∃ (tR : ℕ) (keep : Bool),
          x.lbl rr = Event.restart q tR keep) kQ,
        Nat.findGreatest_spec (P := fun rr => j < rr ∧ rr < kQ ∧ ∃ (tR : ℕ) (keep : Bool),
          x.lbl rr = Event.restart q tR keep) (le_of_lt hr.2.1) hr,
        fun r'' h1 h2 => Nat.findGreatest_is_greatest h1 h2⟩
    have hact : ∀ i : ℕ, rr < i → i ≤ kQ → q ∈ A.active i := by
      intro i h1 h2
      refine Activity.mem_active.2 ⟨?_, fun hc => hqh (E.corrupted_mono i kQ h2 hc)⟩
      by_contra hni
      obtain ⟨m', hm1, hm2, tR', keep', hm'⟩ := (exists_restart_of_not_awake M) x E h2 hni hqaw
      exact hmax m' (by omega) hm2.le ⟨by omega, hm2, tR', keep', hm'⟩
    -- the restart is before `q`'s tick to a clock value at most the proposal window's start of `s'`
    have hnaw : q ∉ A.awake rr := (E.restart_crashed rr q tR keep hlr).1
    have hrT : x.time rr ≤ ((proposal_window_start S.C ((r' + 1) * S.C.R) : ℤ) : ℝ) + ΔClockBehind := by
      obtain ⟨k'', hk'', hcase⟩ := Activity.mem_activeThroughoutToTick.1 hOpener'.1
      have hk''R : k'' = kR := E.tick_unique _ _ q _ hk'' hkR
      subst hk''R
      have hkQkR : kQ ≤ k'' := ((lt_of_time_lt M) x R (by rw [hcut1R] at hkRt; linarith)).le
      rcases hcase with h1 | ⟨ka, -, ca, hca, hka, h2⟩
      · exact absurd (Activity.mem_awake_of_mem_active (h1 rr (by omega))) hnaw
      · have hrka : rr < ka := by
          by_contra hc
          exact hnaw (Activity.mem_awake_of_mem_active (h2 rr (by omega) (by omega)))
        have := htime hrka.le
        have hkat := (E.tick_active ka q _ hka).2.2
        have hca' : ((ca : ℤ) : ℝ) ≤ ((proposal_window_start S.C ((r' + 1) * S.C.R) : ℤ) : ℝ) := by
          exact_mod_cast hca
        push_cast at hca'
        linarith
    obtain ⟨jd, -, hjdk, hlj, -, -⟩ := E_F.caught_up j rr q ⟨u, NamedObject.attest a⟩ tR keep _ kQ c'
      ⟨hsent, hhon⟩ trivial hlr hjr rfl hrkQ hkQ
      (max_le (by linarith) (by
        rcases le_total (x.time rr) (GST : ℝ) with h' | h'
        · rw [max_eq_right h']; rw [hpwR] at hrT; linarith
        · rw [max_eq_left h']; rw [hpwR] at hrT; linarith)) hact
      (fun rr' j₀ k₁ t₁ hr _ => hrel rr' j₀ k₁ t₁ hr (by omega))
    exact ⟨jd, hlj, hjdk⟩
  · -- no restart of `q` between the send and `kQ`: the delivery promise
    have hact : ∀ i : ℕ, j + 1 ≤ i → i ≤ kQ → q ∈ A.active i := by
      intro i h1 h2
      refine Activity.mem_active.2 ⟨?_, fun hc => hqh (E.corrupted_mono i kQ h2 hc)⟩
      by_contra hni
      obtain ⟨m', hm1, hm2, tR', keep', hm'⟩ := (exists_restart_of_not_awake M) x E h2 hni hqaw
      exact hrs ⟨m', by omega, hm2, tR', keep', hm'⟩
    obtain ⟨jd, -, hjdk, hlj, -, -⟩ := E_F.delivered j kQ q ⟨u, NamedObject.attest a⟩ c' _
      ⟨hsent, hhon⟩ trivial hkQ hjkQ hact rfl (by linarith) hrel
    exact ⟨jd, hlj, hjdk⟩

/-! ## The height step -/

/-- **Kit fact, the rows at each updater's own tick from the rows at every tick up to a clock value**. When roots name blocks and the honest caches are on the chain up to the real time of every tick to a
clock value at most `c`, fewer than a quorum of validators are in the adversary set up to `tB`, and every such tick is
at a real time at most `tB`: for every updater `v` of slot `s` whose tick is to the support cutoff of slot `s + 1`, at
most `c`, the same three rows hold up to the real time of `v`'s tick.

Why: an updater of `s` ticks to the support cutoff of `s + 1` (`updaterAt` is a reader up to that tick), at the step
`x.tickStep v (M.supportCutoff S.C (s + 1))` (`tickStep_eq_of_lbl`).

The variables:
- `M`: the model; `F`: its facts;
- `S`, `A`, `x`: the setup, the activity, the execution; `E`: the environment's facts; `s₀`: the healed slot; `H`: the
  threshold; `i₂`: the hand-over step; `s`: the slot; `c`: the clock value; `tB`: the time of the adversary bound.

Read aloud: rows that hold at every tick up to a clock value hold at each updater's tick to the next support cutoff. -/
theorem updater_rows_of_tick_rows (S : Setup V) (A : Activity V) (x : Trace V (NamedObject V) M.N)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ}
    (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject
      GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (s₀ H i₂ s c : ℕ) (tB : ℝ) (hcle : M.supportCutoff S.C (s + 1) ≤ c)
    (hRootsK : ∀ (k : ℕ) (u : V) (c' : ℕ), x.lbl k = Event.tick u c' → c' ≤ c →
      RootsNameBlocksUntil M A x (x.time k))
    (hCachesK : ∀ (k : ℕ) (u : V) (c' : ℕ), x.lbl k = Event.tick u c' → c' ≤ c →
      ∀ (j : ℕ) (w : V), x.time i₂ ≤ x.time j → x.time j ≤ x.time k → w ∉ A.corrupted j →
        CachesOnChain M S A x s₀ H (x.st j w))
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) tB)
    (hkV : ∀ (k : ℕ) (u : V) (c' : ℕ), x.lbl k = Event.tick u c' → c' ≤ c → x.time k ≤ tB) :
    (∀ v ∈ updaterAt M S A x s,
      RootsNameBlocksUntil M A x (x.time (x.tickStep v (M.supportCutoff S.C (s + 1))))) ∧
    (∀ v ∈ updaterAt M S A x s,
      A.AdversaryFewerThanQuorumUntil x (quorum V) (x.time (x.tickStep v (M.supportCutoff S.C (s + 1))))) ∧
    (∀ v ∈ updaterAt M S A x s, ∀ (j : ℕ) (w : V), x.time i₂ ≤ x.time j →
      x.time j ≤ x.time (x.tickStep v (M.supportCutoff S.C (s + 1))) → w ∉ A.corrupted j →
      CachesOnChain M S A x s₀ H (x.st j w)) := by
  have hU : ∀ v ∈ updaterAt M S A x s, ∃ k, x.lbl k = Event.tick v (M.supportCutoff S.C (s + 1)) ∧
      x.tickStep v (M.supportCutoff S.C (s + 1)) = k := by
    intro v hv
    obtain ⟨k, hk, -⟩ := Activity.mem_activeThroughoutToTick.1 hv
    exact ⟨k, hk, (tickStep_eq_of_lbl M) x E hk⟩
  refine ⟨fun v hv => ?_, fun v hv => ?_, fun v hv j w h₁ h₂ h₃ => ?_⟩
  · obtain ⟨k, hk, hks⟩ := hU v hv
    rw [hks]; exact hRootsK k v _ hk hcle
  · obtain ⟨k, hk, hks⟩ := hU v hv
    rw [hks]; exact hAdvQ.mono (hkV k v _ hk hcle)
  · obtain ⟨k, hk, hks⟩ := hU v hv
    rw [hks] at h₂; exact hCachesK k v _ hk hcle j w h₁ h₂ h₃

/-- **Kit theorem, two consecutive honest round opening slots: the height step.** For the rounds
`r`, `r + 1` whose first slots `s = r * R` and `s' = (r + 1) * R` are honest round opening slots,
`s` starting after the hand-over step `i₂`, with a quorum of honest active validators at `s`, the
proposals `B` of `s` and `B'` of `s'` with no root collision at their proposers, and
`Δ_F + Δ ≤ 4Δ(k + 1)`: `B` is of slot `s` and `B'` of slot `s'`; `B` is `B'`'s parent or an
ancestor of it; `B'`'s parent is an ancestor of `B'`, which is not the genesis block and which the
proposer of `s'` holds at its tick to the vote time of `s'`; `B'`'s height is at least `B`'s plus one; and
when `B'`'s parent is at `B`'s height, `B'`'s justified block is `B`'s `T_h`.

Why: `B` is on the chain before `s' − 1` (every updater of `s` saves it), so `B'`'s parent extends
it (`honest_proposal_extends_chain_until` at `s'`). When the parent is at `B`'s height, its `T_h` is
`B`'s (Lemma 47 (e)); every member of the quorum has a target at `B`'s height naming `T_h(B)`'s
root in the proposer of `s'`'s pool before `t_{s'}`; so Lemma 53 puts `B'` at the next height with
`T_h(B)` justified.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₂`: the hand-over step; `H`: the threshold;
- `r`: the round; `B`, `B'`: the two proposals.

Read aloud: between the honest round opening slots of two consecutive rounds, the first proposal is
an ancestor of the second's parent, the height grows by at least one, and the justified block
follows when the parent is at the first proposal's height. -/
theorem consecutive_openings_step_kit (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ anchor i₂ H r : ℕ) (B B' : Block V)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {ΔNet_F : ℕ} (E_F : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    {Δs_F : ℕ} (Sy_F : SyncedWithin A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST)
    (hΔs_F : (Δs_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S ∨ (Δs_F : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind ≤ 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (M.voteTime S.C ((r + 1) * S.C.R)))
    (hRootsK : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.voteTime S.C ((r + 1) * S.C.R) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    -- fewer than a quorum of validators have been in the adversary set up to the support cutoff of slot `(r + 1) * S.C.R + 1`
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (M.supportCutoff S.C ((r + 1) * S.C.R + 1)))
    (hSleepK : CommitteeSleepinessUntil M S A x anchor (M.supportCutoff S.C ((r + 1) * S.C.R))) (hAnchor : anchor ≤ x.time i₂)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀) (ht₀ : M.supportCutoff S.C (s₀ + 1) ≤ x.time i₂)
    (hChain : ConfirmationsChainBefore M S A x s₀ ((r + 1) * S.C.R - 1))
    (hInv : ∀ s' : ℕ, s₀ < s' → s' ≤ (r + 1) * S.C.R - 1 →
      ChainInvFor M S A x (honestActiveAt M S A x s')
        (OnHonestChainBefore M S A x s₀ s') s')
    (hLocks : ∀ s' : ℕ, s₀ < s' → s' ≤ (r + 1) * S.C.R - 1 → ∀ w ∈ honestActiveAt M S A x s',
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ s') s' w)
    (hLocks₀ : ∀ w ∈ honestActiveAt M S A x s₀,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ (s₀ + 1)) s₀ w)
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (w : V), x.time i₂ ≤ x.time j →
      x.time j ≤ M.voteTime S.C ((r + 1) * S.C.R) →
      w ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st j w))
    (hCachesK : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.voteTime S.C ((r + 1) * S.C.R) →
      ∀ (j : ℕ) (w : V), x.time i₂ ≤ x.time j → x.time j ≤ x.time k → w ∉ A.corrupted j →
        CachesOnChain M S A x s₀ H (x.st j w))
    (hParam : Δ_F S + Δ S ≤ 4 * Δ S * (S.C.k + 1))
    (hAfter : x.time i₂ < M.slotStart S.C (r * S.C.R) ∧
      ∀ k : ℕ, x.lbl k = Event.tick (S.P.proposer (r * S.C.R)) (M.slotStart S.C (r * S.C.R)) → x.time i₂ < x.time k)
    (hOpener : HonestOpenerAt M S A x (r * S.C.R))
    (hOpener' : HonestOpenerAt M S A x ((r + 1) * S.C.R))
    (hQuorum : QuorumActiveAt M S A x (r * S.C.R))
    -- every attestation a member of round `r`'s honest active validators put on the wire at a tick up to the round's
    -- action time, with the member's justified height at the next opener's proposal-window start at most its
    -- height, is delivered to the next opener before its tick to its slot's start, or held by it before its
    -- proposal window starts
    (hDel : ∀ u ∈ honestActiveAt M S A x (r * S.C.R), ∀ (j t' : ℕ) (a : Attestation V),
      x.lbl j = Event.tick u t' → t' ≤ M.supportCutoff S.C (r * S.C.R + 1) →
      (⟨u, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (j + 1) - x.sent j →
      M.justifiedHeight (x.stateBefore (M.proposalWindowStart S.C ((r + 1) * S.C.R)) u) ≤ a.h →
      (∃ d : ℕ, x.lbl d = Event.deliver (S.P.proposer ((r + 1) * S.C.R)) ⟨u, NamedObject.attest a⟩ ∧
        d < x.tickStep (S.P.proposer ((r + 1) * S.C.R)) (M.slotStart S.C ((r + 1) * S.C.R))) ∨
      a ∈ (x.stateBefore (M.proposalWindowStart S.C ((r + 1) * S.C.R)) (S.P.proposer ((r + 1) * S.C.R))).attestationsHeld)
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick (S.P.proposer (r * S.C.R)) (M.slotStart S.C (r * S.C.R)) ∧
      (⟨S.P.proposer (r * S.C.R), NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i)
    (hPropose' : ∃ i : ℕ, x.lbl i = Event.tick (S.P.proposer ((r + 1) * S.C.R)) (M.slotStart S.C ((r + 1) * S.C.R)) ∧
      (⟨S.P.proposer ((r + 1) * S.C.R), NamedObject.block B'⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i)
    (hNoCol : ¬ RootCollisionAtProposal M S A x (r * S.C.R) B)
    (hNoCol' : ¬ RootCollisionAtProposal M S A x ((r + 1) * S.C.R) B')
    (hHold : ∀ σ : ℕ, r * S.C.R - 1 ≤ σ → σ ≤ r * S.C.R → ∀ u ∈ honestActiveAt M S A x σ, u ∈ S.P.committee σ →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C σ - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C σ - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hHold' : ∀ u ∈ honestActiveAt M S A x ((r + 1) * S.C.R - 1), u ∈ S.P.committee ((r + 1) * S.C.R - 1) →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C ((r + 1) * S.C.R - 1) - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C ((r + 1) * S.C.R - 1) - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hHoldP : S.P.proposer (r * S.C.R) ∈ A.activeThroughout x ((M.slotStart S.C (r * S.C.R) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C (r * S.C.R) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hHoldP' : S.P.proposer ((r + 1) * S.C.R) ∈ A.activeThroughout x ((M.slotStart S.C ((r + 1) * S.C.R) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C ((r + 1) * S.C.R) - max (Δ S) Δs : ℕ) : ℝ) + Δs)) :
    B.slot = r * S.C.R ∧ B'.slot = (r + 1) * S.C.R ∧ B.AncestorEq B'.parent ∧
      B'.parent.AncestorEq B' ∧ B' ≠ Block.genesis ∧
      B' ∈ (x.tickInput (S.P.proposer ((r + 1) * S.C.R)) (M.voteTime S.C ((r + 1) * S.C.R))).tree ∧
      (M.chainStateOf S.C B).h + 1 ≤ (M.chainStateOf S.C B').h ∧
      ((M.chainStateOf S.C B'.parent).h = (M.chainStateOf S.C B).h →
        (M.chainStateOf S.C B').J = (M.chainStateOf S.C B).T_h) := by
  have hR := S.C.R_ge_two
  have hΔ := one_le_Δ S
  have hA0 := E.ahead_nonneg
  have hB0 := E.behind_nonneg
  have hΔR : (1 : ℝ) ≤ (Δ S : ℝ) := by exact_mod_cast hΔ
  have hRR : (2 : ℝ) ≤ (S.C.R : ℝ) := by exact_mod_cast hR
  have hΔRR : 2 * (Δ S : ℝ) ≤ (Δ S : ℝ) * (S.C.R : ℝ) := by nlinarith
  have hΔF0 : (0 : ℝ) ≤ (Δ_F S : ℝ) := by positivity
  have hss' : (r + 1) * S.C.R = r * S.C.R + S.C.R := by rw [Nat.add_mul, Nat.one_mul]
  obtain ⟨hs2, -, -⟩ := (GoldilocksCorrectness.Record.Proofs.Routines.slot_after_healed_round M.toSlotLayout F.sched) S
    s₀ (r * S.C.R) (by exact_mod_cast lt_of_le_of_lt ht₀ hAfter.1)
  -- the two slots `s = q + 2` and `s' = q' + 2`, with `q' = q + R`
  generalize hsd : r * S.C.R = s at *
  generalize hs'd : (r + 1) * S.C.R = s' at *
  obtain ⟨q, rfl⟩ : ∃ q, s = q + 2 := ⟨s - 2, by omega⟩
  obtain ⟨q', rfl⟩ : ∃ q', s' = q' + 2 := ⟨s' - 2, by omega⟩
  have hq'q : ((q' : ℕ) : ℝ) = (q : ℝ) + (S.C.R : ℝ) := by exact_mod_cast (show q' = q + S.C.R by omega)
  have hsub' : q' + 2 - 1 = q' + 1 := by omega
  rw [hsub'] at hHold'
  -- the times of the slots
  have hsR : ∀ σ : ℕ, ((M.slotStart S.C σ : ℕ) : ℝ) = 4 * (Δ S : ℝ) * (σ : ℝ) := fun σ => by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S σ]; push_cast; ring
  have hvR : ∀ σ : ℕ, ((M.voteTime S.C σ : ℕ) : ℝ) = 4 * (Δ S : ℝ) * (σ : ℝ) + Δ S := fun σ => by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S σ,
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S σ]; push_cast; ring
  have hcR : ∀ σ : ℕ, ((M.supportCutoff S.C σ : ℕ) : ℝ) = 4 * (Δ S : ℝ) * (σ : ℝ) + 2 * Δ S := fun σ => by
    rw [(GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_eq M.toSlotLayout F.sched U) S σ,
      (GoldilocksCorrectness.Record.Proofs.Routines.voteTime_eq M.toSlotLayout F.sched U) S σ,
      (GoldilocksCorrectness.Record.Proofs.Routines.slotStart_eq M.toSlotLayout F.sched U) S σ]; push_cast; ring
  -- the updaters of `s` tick to the support cutoff of `s + 1`, a clock value at most the vote time of `s'`
  have hcle : M.supportCutoff S.C (q + 2 + 1) ≤ M.voteTime S.C (q' + 2) := by
    have e1 := hcR (q + 2 + 1)
    have e2 := hvR (q' + 2)
    push_cast at e1 e2
    have : ((M.supportCutoff S.C (q + 2 + 1) : ℕ) : ℝ) ≤ ((M.voteTime S.C (q' + 2) : ℕ) : ℝ) := by
      rw [e1, e2, hq'q]; nlinarith
    exact_mod_cast this
  -- a tick to a clock value at most the vote time of `s'` is at a real time at most the support cutoff of `s' + 1`
  have hkV : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.voteTime S.C (q' + 2) →
      x.time k ≤ ((M.supportCutoff S.C (q' + 2 + 1) : ℕ) : ℝ) := by
    intro k u c hk hc
    have h1 := (E.tick_active k u c hk).2.2
    have hcR' : (c : ℝ) ≤ ((M.voteTime S.C (q' + 2) : ℕ) : ℝ) := by exact_mod_cast hc
    have e1 := hvR (q' + 2)
    have e2 := hcR (q' + 2 + 1)
    push_cast at e1 e2
    linarith
  -- the rows the round's callees read at each updater's own tick (, T-RC86-1)
  obtain ⟨hRootsU, hAdvQU, hCachesU⟩ := (updater_rows_of_tick_rows M F) S A x E s₀ H i₂ (q + 2) _ _ hcle hRootsK
    hCachesK hAdvQ hkV
  have hSleepS := hSleepK.mono M ((GoldilocksCorrectness.Record.Proofs.Routines.supportCutoff_mono M.toSlotLayout F.sched) S
    (show q + 2 + 1 ≤ q' + 2 by omega))
  have hChainS : ConfirmationsChainBefore M S A x s₀ (q + 2) :=
    fun a b c d e f h1 h2 h3 => hChain a b c d e f h1 h2 (by omega)
  have hChainS1 : ConfirmationsChainBefore M S A x s₀ (q + 2 + 1) :=
    fun a b c d e f h1 h2 h3 => hChain a b c d e f h1 h2 (by omega)
  have hInvS := fun s'' (h₁ : s₀ < s'') (h₂ : s'' ≤ q + 2) => hInv s'' h₁ (by omega)
  have hLocksS := fun s'' (h₁ : s₀ < s'') (h₂ : s'' ≤ q + 2) => hLocks s'' h₁ (by omega)
  -- the chain at `s`: `B` is saved by every updater of `s`, among them the proposer of `s`
  obtain ⟨-, hBslot, hSaved, -⟩ := (round_chain_frame_after_healing M F U Fx) S A x R GST s₀ anchor i₂ H (q + 2) B
    E hNet hSkew hRedeliver Sy hΔs hRootsU hParent hAdvQU hSleepS hAnchor hGST ht₀ hChainS hInvS hLocksS hLocks₀
    hOld hCachesU hAfter hOpener hPropose hNoCol hHold hHoldP
  have hpU : S.P.proposer (q + 2) ∈ updaterAt M S A x (q + 2) :=
    (honestActiveAt_subset_updaterAt M F) S A x R E (q + 2) ((opener_mem_honestActiveAt M F U) S A R E q hOpener)
  have hBon : OnHonestChainAt M S A x s₀ (q + 2) B :=
    ⟨by omega, _, hpU, B, hSaved _ hpU, ancestorEq_refl B⟩
  -- the proposal of `s'` extends the chain before `s' − 1`; its proposer's tick is after the hand-over step
  obtain ⟨ip', hl', hsent'⟩ := hPropose'
  have hAfter' : x.time i₂ < ((M.slotStart S.C (q' + 2) : ℕ) : ℝ) := by
    have h0 := hAfter.1
    rw [hsR] at h0 ⊢
    push_cast at h0 ⊢
    rw [hq'q]; nlinarith
  have hip' : x.time i₂ < x.time ip' := by
    have h1 := (E.tick_active ip' _ _ hl').2.1
    have h0 := hAfter.1
    rw [hsR] at h0 h1
    push_cast at h0 h1
    rw [hq'q] at h1
    nlinarith
  have hLk' := (locks_before_of_locks_le M F) S A x s₀ q' (fun s'' h₁ h₂ => hLocks s'' h₁ (by omega))
    hLocks₀ (by omega)
  obtain ⟨hPC, hB'slot, hB'ne, hPB', -, hTree⟩ := (honest_proposal_extends_chain_until M F U Fx) S A x R
    GST s₀ anchor i₂ H q' ip' B' E hNet hSkew hRedeliver Sy hΔs hRootsK hParent
    (fun k u c hk hc => hAdvQ.mono (hkV k u c hk hc)) hSleepK hAnchor hGST
    (fun a b c d e f h1 h2 h3 => hChain a b c d e f h1 h2 (by omega))
    (fun s'' h₁ h₂ => hInv s'' h₁ (by omega)) (fun s'' h₁ h₂ => hLocks s'' h₁ (by omega)) hOld
    (fun k w c hk hc j u h₁ h₂ h₃ => hCachesK k w c hk hc j u ((time_mono M) x R h₁.le) h₂ h₃)
    ht₀ (by omega) hAfter' hip' hLk' hHold'
    ⟨hOpener'.1, fun h => hOpener'.2 (Finset.mem_union_left _ (Finset.mem_union_left _ h))⟩ hHoldP' hl' hsent'
    (fun B'' hB'' h => hNoCol' ⟨B'', hB'', h⟩)
  have hBP : B.AncestorEq B'.parent := hPC B ⟨q + 2, by omega, hBon⟩
  -- the next opener holds `B'` at its tick to its slot's vote time (, item 4)
  have hB'T : B' ∈ (x.tickInput (S.P.proposer (q' + 2)) (M.voteTime S.C (q' + 2))).tree :=
    hTree _ ((opener_mem_honestActiveAt M F U) S A R E q' hOpener')
  refine ⟨hBslot, hB'slot, hBP, hPB', hB'ne, hB'T, ?_⟩
  -- the height step
  have hPh := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C B B'.parent).2.2.2.1 hBP
  have hB'h := ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C B'.parent B').2.2.2.1 hPB'
  by_cases heq : (M.chainStateOf S.C B'.parent).h = (M.chainStateOf S.C B).h
  · have hTh : (M.chainStateOf S.C B).T_h = (M.chainStateOf S.C B'.parent).T_h :=
      ((GoldilocksCorrectness.Record.Proofs.Routines.lem47_chain_state_heights M F) S.C B B'.parent).2.2.2.2 hBP heq.symm
    -- every honest attestation sent before the support cutoff of `s' + 1` is at most `h(B)` (Lemma 107 at round `r`),
    -- so every member's justified height before the proposal window of `s'` is at most `h(B)`
    have h107 := (lem107_honest_attestations_at_most_opening_height M F U Fx) S A x R GST s₀ anchor i₂ H r (q + 2) B
      E hNet hSkew hRedeliver Sy hΔs hRootsU hParent hAdvQU hSleepS hAnchor hGST ht₀ hChainS hInvS hLocksS hLocks₀
      hOld hCachesU hsd.symm hAfter hOpener hPropose hNoCol hHold hHoldP
    rw [hs'd] at h107
    have hpw := (GoldilocksCorrectness.Record.Proofs.Routines.proposalWindowStart_add_Δ_F_le M.toSlotLayout F.sched U) S
      (show S.C.R ≤ q' + 2 by omega) hParam
    have hpwR : ((M.proposalWindowStart S.C (q' + 2) : ℕ) : ℝ) + Δ_F S ≤ ((M.slotStart S.C (q' + 2) : ℕ) : ℝ) := by
      exact_mod_cast hpw
    have hstc : ((M.slotStart S.C (q' + 2) : ℕ) : ℝ) < ((M.supportCutoff S.C (q' + 2 + 1) : ℕ) : ℝ) := by
      rw [hsR, hcR]; push_cast; nlinarith
    have hpwA : ((M.proposalWindowStart S.C (q' + 2) : ℕ) : ℝ) + ΔClockAhead <
        ((M.supportCutoff S.C (q' + 2 + 1) : ℕ) : ℝ) := by
      linarith
    have hpwc : M.proposalWindowStart S.C (q' + 2) < M.supportCutoff S.C (q' + 2 + 1) := by
      have : ((M.proposalWindowStart S.C (q' + 2) : ℕ) : ℝ) < ((M.supportCutoff S.C (q' + 2 + 1) : ℕ) : ℝ) := by
        linarith
      exact_mod_cast this
    have hselq : ∀ u : V,
        M.justifiedHeight (x.stateBefore (M.proposalWindowStart S.C (q' + 2)) u) ≤ (M.chainStateOf S.C B).h :=
      fun u => (justifiedHeight_le_of_oldAttestations M F Fx) S A x R E _ _ _ u hAdvQ h107 hpwc hpwA
    -- the proposal window of `s'` starts before the next opener's tick to its slot's start
    have hle : x.stepBefore (M.proposalWindowStart S.C (q' + 2)) ≤
        x.tickStep (S.P.proposer (q' + 2)) (M.slotStart S.C (q' + 2)) := by
      rw [(tickStep_eq_of_lbl M) x E hl']
      exact (stepBefore_le_of_le_time_st M F) R E (by have := (E.tick_active ip' _ _ hl').2.1; linarith)
    -- every member's target at `B`'s height naming `T_h(B)`'s root is in the next opener's tick input
    have hPoolτ : ∀ u ∈ honestActiveAt M S A x (q + 2), ∃ a ∈
        (x.tickInput (S.P.proposer (q' + 2)) (M.slotStart S.C (q' + 2))).attestationsHeld,
        a.val_index = u ∧ a.h = (M.chainStateOf S.C B'.parent).h ∧
          a.T = (M.chainStateOf S.C B'.parent).T_h.root ∧ a.τ = false := by
      intro u hu
      obtain ⟨i, t, a, hli, ht, hsi, hav, hah, haT, hτ⟩ := (round_attesters_target_after_healing M F U Fx) S A x R
        GST s₀ anchor i₂ H r (q + 2) B u E hNet hSkew hRedeliver Sy hΔs hRootsU hParent hAdvQU hSleepS hAnchor hGST
        ht₀ hChainS1 hInvS hLocksS hLocks₀ hOld hCachesU hsd.symm hAfter hOpener hPropose hNoCol hHold hHoldP hu
      have hdel := hDel u hu i t a hli ht hsi (by rw [hah]; exact hselq u)
      exact ⟨a, (attestation_in_tickInput_of_delivery_or_held M F) S A x R E hNet hSkew hRedeliver _ _ _ hle i t u a
        hli hsi hdel, hav, by rw [hah, heq], by rw [haT, hTh], hτ⟩
    have h53 := (lem53_next_honest_proposal_carries_certificate M F U Fx) S A x R E (q' + 2) (S.P.proposer (q' + 2)) B'
      B'.parent (honestActiveAt M S A x (q + 2)) ⟨ip', hl', hsent'⟩ rfl hQuorum
      (fun u hu => by
        obtain ⟨a, ha, hav, hah, haT, -⟩ := hPoolτ u hu
        exact ⟨a, ha, hav, hah, haT⟩)
    have h2 := h53.2 hPoolτ
    exact ⟨by rw [h2.1, heq], fun _ => by rw [h2.2, hTh]⟩
  · exact ⟨by omega_nat, fun h => absurd h heq⟩

/-- **Two consecutive honest round opening slots after healing: the height step (Lemma 95, its
first two conjuncts).** The proof; the audited statement is in
`Statements/Executions/FinalityLivenessStatements.lean`. It is `consecutive_openings_step_kit` with
`B'`'s parent an ancestor of `B'`.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous; `s₀`: the healed slot; `anchor`: the time from which committee
  sleepiness holds; `i₂`: the hand-over step; `H`: the threshold;
- `r`: the first round; `B`, `B'`: the two proposals.

Read aloud: the next honest round opening slot extends the previous one's proposal and raises the
height. -/
theorem consecutive_openings_height_step (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST s₀ anchor i₂ H r : ℕ) (B B' : Block V)
    
    {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GST (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    {ΔNet_F : ℕ} (E_F : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)
    {Δs : ℕ} (Sy : SyncedWithin A x (servesMin M S.C) acObject (releaseOf M S.C) ΔRedeliver Δs GST)
    (hΔs : (max (Δ S) Δs : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind < 4 * Δ S * S.C.k)
    {Δs_F : ℕ} (Sy_F : SyncedWithin A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST)
    (hΔs_F : (Δs_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S ∨ (Δs_F : ℝ) + 3 * Δ S + ΔClockAhead + ΔClockBehind ≤ 4 * Δ S * S.C.k)
    (hRoots : RootsNameBlocksUntil M A x (M.voteTime S.C ((r + 1) * S.C.R)))
    (hRootsK : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.voteTime S.C ((r + 1) * S.C.R) →
      RootsNameBlocksUntil M A x (x.time k))
    (hParent : ParentHeldAtDelivery M x)
    -- fewer than a quorum of validators have been in the adversary set up to the support cutoff of slot `(r + 1) * S.C.R + 1`
    (hAdvQ : A.AdversaryFewerThanQuorumUntil x (quorum V) (M.supportCutoff S.C ((r + 1) * S.C.R + 1)))
    (hSleepK : CommitteeSleepinessUntil M S A x anchor (M.supportCutoff S.C ((r + 1) * S.C.R))) (hAnchor : anchor ≤ x.time i₂)
    (hGST : GST + max (Δ S) Δs ≤ M.supportCutoff S.C s₀) (ht₀ : M.supportCutoff S.C (s₀ + 1) ≤ x.time i₂)
    (hChain : ConfirmationsChainBefore M S A x s₀ ((r + 1) * S.C.R - 1))
    (hInv : ∀ s' : ℕ, s₀ < s' → s' ≤ (r + 1) * S.C.R - 1 →
      ChainInvFor M S A x (honestActiveAt M S A x s')
        (OnHonestChainBefore M S A x s₀ s') s')
    (hLocks : ∀ s' : ℕ, s₀ < s' → s' ≤ (r + 1) * S.C.R - 1 → ∀ w ∈ honestActiveAt M S A x s',
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ s') s' w)
    (hLocks₀ : ∀ w ∈ honestActiveAt M S A x s₀,
      LiveLocksOnFamilyAt M S A x (OnHonestChainBefore M S A x s₀ (s₀ + 1)) s₀ w)
    (hOld : OldAttestationsAtMostHonestAt M S A x (M.supportCutoff S.C (s₀ + 1)) (M.supportCutoff S.C (s₀ + 1)) H)
    (hCaches : ∀ (j : ℕ) (w : V), x.time i₂ ≤ x.time j →
      x.time j ≤ M.voteTime S.C ((r + 1) * S.C.R) →
      w ∉ A.corrupted j → CachesOnChain M S A x s₀ H (x.st j w))
    (hCachesK : ∀ (k : ℕ) (u : V) (c : ℕ), x.lbl k = Event.tick u c → c ≤ M.voteTime S.C ((r + 1) * S.C.R) →
      ∀ (j : ℕ) (w : V), x.time i₂ ≤ x.time j → x.time j ≤ x.time k → w ∉ A.corrupted j →
        CachesOnChain M S A x s₀ H (x.st j w))
    (hParam : Δ_F S + Δ S ≤ 4 * Δ S * (S.C.k + 1))
    (hAfter : x.time i₂ < M.slotStart S.C (r * S.C.R) ∧
      ∀ k : ℕ, x.lbl k = Event.tick (S.P.proposer (r * S.C.R)) (M.slotStart S.C (r * S.C.R)) → x.time i₂ < x.time k)
    (hOpener : HonestOpenerAt M S A x (r * S.C.R))
    (hOpener' : HonestOpenerAt M S A x ((r + 1) * S.C.R))
    (hQuorum : QuorumActiveAt M S A x (r * S.C.R))
    -- every attestation a member of round `r`'s honest active validators put on the wire at a tick up to the round's
    -- action time, with the member's justified height at the next opener's proposal-window start at most its
    -- height, is delivered to the next opener before its tick to its slot's start, or held by it before its
    -- proposal window starts
    (hDel : ∀ u ∈ honestActiveAt M S A x (r * S.C.R), ∀ (j t' : ℕ) (a : Attestation V),
      x.lbl j = Event.tick u t' → t' ≤ M.supportCutoff S.C (r * S.C.R + 1) →
      (⟨u, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (j + 1) - x.sent j →
      M.justifiedHeight (x.stateBefore (M.proposalWindowStart S.C ((r + 1) * S.C.R)) u) ≤ a.h →
      (∃ d : ℕ, x.lbl d = Event.deliver (S.P.proposer ((r + 1) * S.C.R)) ⟨u, NamedObject.attest a⟩ ∧
        d < x.tickStep (S.P.proposer ((r + 1) * S.C.R)) (M.slotStart S.C ((r + 1) * S.C.R))) ∨
      a ∈ (x.stateBefore (M.proposalWindowStart S.C ((r + 1) * S.C.R)) (S.P.proposer ((r + 1) * S.C.R))).attestationsHeld)
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick (S.P.proposer (r * S.C.R)) (M.slotStart S.C (r * S.C.R)) ∧
      (⟨S.P.proposer (r * S.C.R), NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i)
    (hPropose' : ∃ i : ℕ, x.lbl i = Event.tick (S.P.proposer ((r + 1) * S.C.R)) (M.slotStart S.C ((r + 1) * S.C.R)) ∧
      (⟨S.P.proposer ((r + 1) * S.C.R), NamedObject.block B'⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i)
    (hNoCol : ¬ RootCollisionAtProposal M S A x (r * S.C.R) B)
    (hNoCol' : ¬ RootCollisionAtProposal M S A x ((r + 1) * S.C.R) B')
    (hHold : ∀ σ : ℕ, r * S.C.R - 1 ≤ σ → σ ≤ r * S.C.R → ∀ u ∈ honestActiveAt M S A x σ, u ∈ S.P.committee σ →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C σ - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C σ - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hHold' : ∀ u ∈ honestActiveAt M S A x ((r + 1) * S.C.R - 1), u ∈ S.P.committee ((r + 1) * S.C.R - 1) →
      u ∈ A.activeThroughout x ((M.supportCutoff S.C ((r + 1) * S.C.R - 1) - max (2 * Δ S) Δs : ℕ) : ℝ)
        (((M.supportCutoff S.C ((r + 1) * S.C.R - 1) - max (2 * Δ S) Δs : ℕ) : ℝ) + Δs))
    (hHoldP : S.P.proposer (r * S.C.R) ∈ A.activeThroughout x ((M.slotStart S.C (r * S.C.R) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C (r * S.C.R) - max (Δ S) Δs : ℕ) : ℝ) + Δs))
    (hHoldP' : S.P.proposer ((r + 1) * S.C.R) ∈ A.activeThroughout x ((M.slotStart S.C ((r + 1) * S.C.R) - max (Δ S) Δs : ℕ) : ℝ)
      (((M.slotStart S.C ((r + 1) * S.C.R) - max (Δ S) Δs : ℕ) : ℝ) + Δs)) :
    B.AncestorEq B' ∧ (M.chainStateOf S.C B).h + 1 ≤ (M.chainStateOf S.C B').h := by
  obtain ⟨-, -, hBP, hPB', -, -, hstep, -⟩ := (consecutive_openings_step_kit M F U Fx) S A x R GST s₀ anchor
    i₂ H r B B' E hNet hSkew hRedeliver E_F hNet_F hSkew_F Sy hΔs Sy_F hΔs_F hRoots hRootsK hParent hAdvQ hSleepK
    hAnchor hGST ht₀ hChain hInv hLocks hLocks₀ hOld hCaches hCachesK hParam hAfter hOpener hOpener'
    hQuorum hDel hPropose hPropose' hNoCol hNoCol' hHold hHold' hHoldP hHoldP'
  exact ⟨ancestorEq_trans hBP hPB', hstep⟩

end GoldilocksCorrectness.Record.Proofs.Executions

