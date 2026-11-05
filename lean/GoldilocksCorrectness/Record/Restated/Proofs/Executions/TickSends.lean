module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Steps
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.InvariantStatements
public import GoldilocksCorrectness.Proofs.Executions.TickSends

@[expose] public section

/-!
# TickSends, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/TickSends.lean` that read an execution,
over a model `M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: a signed message
that enters the sent log at the tick of every awake validator was sent by an outcome of that
validator's tick in the model, and an honest validator's ticks put at most one Goldfish vote per
slot on the wire, from the field `tick_sends` of `F.tk`. `isGfVote_block`, `isGfVote_attest` and
`eq_of_filter_isGfVote` name no member and read no execution; the twins read the landed ones.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Proofs.Routines (DREBEmits DREBEmits.bind DREBEmits.bind_nil
  DREBEmits.broadcast_then DREBEmits.dite DREBEmits.ite DREBEmits.liftM DREBEmits.monadLift
  DREBEmits.pure NoVote TickVotes isGfVote noVote_attest_append noVote_block_append noVote_nil
  tickVotes_of_append)

open GoldilocksCorrectness.Proofs.Routines (ac_on_tick_sends)

open GoldilocksCorrectness.Proofs.Routines (tick_sends)

namespace GoldilocksCorrectness.Record.Proofs.Executions

open GoldilocksCorrectness.Proofs.Executions (eq_of_filter_isGfVote)

open Goldilocks
open GoldilocksCorrectness.Record.Statements.Executions

/-! ## The kit -/

section Kit

variable {V : Type} [DecidableEq V] [Fintype V]
variable (M : GoldilocksModel V) (F : Facts M)
include F

end Kit

/-! ## The routines -/

section Routines

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

end Routines

/-! ## The steps -/

section Steps

open Framework.StsMultisetLog (SignedMsg TickAllAwakeWake tickAllAwakeUpdate_getElem_react)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks.Sts (Setup)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder] {S : Setup V} {A : Activity V}
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- What a tick puts on the wire, per step: the ticking validator is active at the tick's step, and
every object it puts on the wire under its signature is sent by an `.ok` outcome of its tick, from
the node state the tick starts from, which is the node state after the step.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `i`: the step; `t`: the
  reading of the tick; `p`: the signer; `o`: the object.

Read aloud: what a tick puts on the wire is what an active validator's tick sent. -/
theorem tick_send_step_outcome_per_step {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) {i t : ℕ} {p : V}
    {o : NamedObject V}
    -- the step `i` is `p`'s tick to `t`
    (hl : x.lbl i = Event.tick p t)
    -- the step `i` put `⟨p, o⟩` on the wire
    (hm : (⟨p, o⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) :
    p ∈ A.active i ∧
      ∃ (n' : M.N) (sent : List (NamedObject V)),
        .ok (n', sent) ∈ (M.tick S.C S.P S.X (x.tickInput p t) (t : Int)) ∧
          o ∈ sent ∧ x.st (i + 1) p = n' ∧
          ∀ o' : NamedObject V,
            (⟨p, o'⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i → o' ∈ sent := by
  have hts := (tickStep_eq_of_lbl M) x E hl
  have hin : x.tickInput p t = x.st i p := by
    unfold Trace.tickInput
    rw [hts]
  obtain ⟨n', sent, hok, hst, hsent⟩ := R.tick i p t hl
  have hput : ∀ o' : NamedObject V,
      (⟨p, o'⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i → o' ∈ sent := by
    intro o' ho'
    rw [hsent, add_tsub_cancel_left] at ho'
    obtain ⟨m', hm', heq⟩ := Multiset.mem_map.1 ho'
    injection heq with _ hmo
    subst hmo
    exact Multiset.mem_coe.1 hm'
  exact ⟨(E.tick_active i p t hl).1, n', sent, by rw [hin]; exact hok, hput o hm, hst, hput⟩

/-- A signed message that enters the sent log at a validator's tick to `t` is signed by a validator
active at the tick's step; its object is in the list sent by an `.ok` outcome of that validator's
tick, from the node state the tick starts from; the validator holds that outcome's node state after
the step; and every object the step put on the wire under the validator's signature is in that
list.

 This is `tick_send_step_outcome_per_step`, under the name its callers use.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `i`: the step; `t`: the
  value of the tick; `p`: the signer; `o`: the object.

Read aloud: what a tick puts on the wire was sent by the tick of a validator active at that step, in
one outcome, whose node state the validator then holds and which sent everything the step put on
the wire under its signature. -/
theorem tick_send_step_outcome {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) {i t : ℕ} {p : V}
    {o : NamedObject V}
    -- the step `i` is `p`'s tick to `t`
    (hl : x.lbl i = Event.tick p t)
    -- the step `i` put `⟨p, o⟩` on the wire
    (hm : (⟨p, o⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) :
    p ∈ A.active i ∧
      ∃ (n' : M.N) (sent : List (NamedObject V)),
        .ok (n', sent) ∈ (M.tick S.C S.P S.X (x.tickInput p t) (t : Int)) ∧
          o ∈ sent ∧ x.st (i + 1) p = n' ∧
          ∀ o' : NamedObject V,
            (⟨p, o'⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i → o' ∈ sent :=
  (tick_send_step_outcome_per_step M F R E) hl hm

/-- A signed message that enters the sent log at a validator's tick to `t` is signed by a validator
active at the tick's step, and its object is in the list sent by an `.ok` outcome of that
validator's tick, from the node state the tick starts from. The wake stage sends nothing.



The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `i`: the step; `t`: the time of the tick; `p`: the signer; `o`: the object;
- `n'`, `sent`: the outcome of `p`'s tick, the node state and the objects sent.

Read aloud: what a tick puts on the wire is what the tick of a validator active at that step
sent. -/
theorem tick_send_of_honestSendAt {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) {i t : ℕ} {p : V}
    {o : NamedObject V}
    -- the step `i` is the tick of every awake validator at `t`
    (hl : x.lbl i = Event.tick p t)
    -- the step `i` put `⟨p, o⟩` on the wire
    (hm : (⟨p, o⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) :
    p ∈ A.active i ∧
      ∃ (n' : M.N) (sent : List (NamedObject V)),
        .ok (n', sent) ∈ (M.tick S.C S.P S.X (x.tickInput p t) (t : Int)) ∧
          o ∈ sent := by
  obtain ⟨hp, n', sent, hok, ho, -, -⟩ := (tick_send_step_outcome M F R E) hl hm
  exact ⟨hp, n', sent, hok, ho⟩

/-- A signed message that enters the sent log at a validator's tick to `t` is signed by a validator
active at that step, and its object is in the list sent by an `.ok` outcome of that validator's
tick, from the node state the tick starts from: `tick_send_of_honestSendAt` with the signer active
at the tick's step (`tick_active`) in place of active after every step read as `t`, which a tick
does not give.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `i`: the step; `t`: the
  reading of the tick; `p`: the signer; `o`: the object;
- `n'`, `sent`: the outcome of `p`'s tick, the node state and the objects sent.

Read aloud: what a tick puts on the wire is what the tick of a validator active at that step
sent. -/
theorem tick_send_of_honestSendAt_per_step {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) {i t : ℕ} {p : V}
    {o : NamedObject V}
    -- the step `i` is `p`'s tick to `t`
    (hl : x.lbl i = Event.tick p t)
    -- the step `i` put `⟨p, o⟩` on the wire
    (hm : (⟨p, o⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i) :
    p ∈ A.active i ∧
      ∃ (n' : M.N) (sent : List (NamedObject V)),
        .ok (n', sent) ∈ (M.tick S.C S.P S.X (x.tickInput p t) (t : Int)) ∧
          o ∈ sent := by
  obtain ⟨hp, n', sent, hok, ho, -, -⟩ := (tick_send_step_outcome_per_step M F R E) hl hm
  exact ⟨hp, n', sent, hok, ho⟩

/-- A validator's Goldfish votes for one slot, each put on the wire by the validator at the tick
of every awake validator at some time, are one vote: each tick's vote is for the slot of its time
and sent only at that slot's vote time, so the two ticks are at the same time, hence the same step
(`tickAllAwake_unique`), and that tick sends at most one Goldfish vote.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `i`, `j`: the two steps; `t`, `t'`: their times; `u`: the validator;
  `vote`, `vote'`: the two votes.

Read aloud: an honest validator's ticks put at most one Goldfish vote per slot on the wire. -/
theorem honest_vote_sent_once {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) {i j t t' : ℕ} {u : V}
    {vote vote' : GoldfishVote V}
    -- the steps `i` and `j` are the ticks of every awake validator at `t` and `t'`
    (hi : x.lbl i = Event.tick u t) (hj : x.lbl j = Event.tick u t')
    -- `u` put `vote` on the wire at `i`, and `vote'` at `j`
    (hsi : (⟨u, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
      x.sent (i + 1) - x.sent i)
    (hsj : (⟨u, NamedObject.gfVote vote'⟩ : SignedMsg V (NamedObject V)) ∈
      x.sent (j + 1) - x.sent j)
    -- the two votes are for the same slot
    (hslot : vote.slot = vote'.slot) : vote = vote' := by
  obtain ⟨-, n₁, sent₁, hrun₁, hm₁, -, hall₁⟩ := (tick_send_step_outcome_per_step M F R E) hi hsi
  obtain ⟨-, n₂, sent₂, hrun₂, hm₂, -, -⟩ := (tick_send_step_outcome_per_step M F R E) hj hsj
  obtain ⟨hv₁, hone₁⟩ := F.tk.tick_sends S.C S.P S.X _ _ _ _ hrun₁
  obtain ⟨hv₂, -⟩ := F.tk.tick_sends S.C S.P S.X _ _ _ _ hrun₂
  obtain ⟨-, hs₁, ht₁⟩ := hv₁ vote hm₁
  obtain ⟨-, hs₂, ht₂⟩ := hv₂ vote' hm₂
  have htt : (t : Int) = (t' : Int) := by
    rw [ht₁, ht₂, ← hs₁, ← hs₂, hslot]
  have htt' : t = t' := by exact_mod_cast htt
  subst htt'
  have hij : i = j := E.tick_unique i j u t hi hj
  subst hij
  -- every object the step put on the wire under `u`'s signature is in the first outcome's list
  exact eq_of_filter_isGfVote hone₁ hm₁ (hall₁ _ hsj)

end Steps

end GoldilocksCorrectness.Record.Proofs.Executions

