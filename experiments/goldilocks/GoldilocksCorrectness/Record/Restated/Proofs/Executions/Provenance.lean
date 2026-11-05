module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Clock
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.TickSends
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Wiring
public import GoldilocksCorrectness.Proofs.Executions.Provenance
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption

@[expose] public section

/-!
# Provenance, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Provenance.lean` that read an execution,
over a model `M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: a delivered message
was in the sent log; what a step adds to a validator's votes held and tree was put on the wire, by
the facts of the tick (`F.tk.tick_prov`) and of the receipt (`F.rcv.receive_new`), and what it adds
to its attestations held, by `F.tk.tick_prov_attestations` and `F.rcv.receive_new_attestations`;
and along an execution, every vote and every attestation a validator holds was put on the wire
(`pool_vote_sent`, `held_attestation_sent`), and every non-genesis block of its tree was put on the
wire by the validator itself.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Proofs.Routines (Carried DREBSpec DREBSpec.bind' DREBSpec.bind_liftPost
  DREBSpec.broadcast_pure DREBSpec.dite DREBSpec.ite DREBSpec.of_outcome DREBSpec.pure
  DREPost.true forIn_yield_inv)

open GoldilocksCorrectness.Proofs.Routines (fg_on_block_eq)

open GoldilocksCorrectness.Proofs.Routines (ac_on_block_new_votes ac_on_tick_prov
  on_goldfish_vote_new)

open GoldilocksCorrectness.Proofs.Routines (on_attestation_frame on_block_new tick_prov)

open GoldilocksCorrectness.Proofs.Routines (acState_initial_eq fgState_initial_eq initial_eq)

open GoldilocksCorrectness.Proofs.Routines (receive_new)

namespace GoldilocksCorrectness.Record.Proofs.Executions

open Goldilocks
open GoldilocksCorrectness.Record.Statements.Executions

/-! ## The kit -/

section Kit

variable {V : Type} [DecidableEq V] [Fintype V]
variable (M : GoldilocksModel V) (F : Facts M)
include F

end Kit

/-! ## The relation -/

section Relation

variable {V : Type} [DecidableEq V] [Fintype V]
variable (M : GoldilocksModel V) (F : Facts M)
include F

end Relation

/-! ## The routines -/

section Routines

variable {V : Type} [DecidableEq V] [Fintype V]
variable (M : GoldilocksModel V) (F : Facts M)
include F

variable [RootOrder]

end Routines

/-! ## The steps -/

section Steps

open Framework.StsMultisetLog (SignedMsg TickAllAwakeWake nodeStep_iff_exists)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks.Sts (Setup relayedObjects)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder] {S : Setup V} {A : Activity V}
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- A delivered message was in the sent log when it was delivered: the enabling condition of a
delivery.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `d`: the step of the delivery; `v`: the receiver; `sm`: the signed
  message.

Read aloud: a delivered message was in the sent log. -/
theorem delivered_mem_sent {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {d : ℕ} {v : V}
    {sm : SignedMsg V (NamedObject V)}
    -- the step `d` delivers `sm` to `v`
    (hl : x.lbl d = Event.deliver v sm) : sm ∈ x.sent d := by
  exact (R.deliver d v sm hl).1

/-- A delivery to `v` puts on the wire, signed by `v`, every object the wiring re-sends for the
delivered object.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `d`: the step of the delivery; `v`: the receiver; `sm`: the signed message;
  `o`: an object re-sent.

Read aloud: what a delivery adds was put on the wire. -/
theorem step_sent_of_delivery {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {d : ℕ} {v : V}
    {sm : SignedMsg V (NamedObject V)}
    -- the step `d` delivers `sm` to `v`
    (hl : x.lbl d = Event.deliver v sm) {o : NamedObject V}
    -- `o` is re-sent for the delivered object
    (ho : o ∈ M.relayedObjects sm.msg) :
    (⟨v, o⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (d + 1) - x.sent d := by
  rw [(R.deliver d v sm hl).2.2, add_tsub_cancel_left]
  exact Multiset.mem_map.2 ⟨o, ho, rfl⟩

/-- At the tick of every awake validator at `t`, a validator awake and outside the adversary set
at `t` puts on the wire, signed by itself, every object its tick sends from the node state the
tick starts from.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `i`: the step; `t`: the time of the tick; `v`: the validator;
- `n'`, `sent`: an `.ok` outcome of `v`'s tick; `o`: an object of `sent`.

Over the record: the model's tick may have several outcomes, so the outcome is the one the
step took (`tick_step_outcome`); the landed statement, of every outcome, holds of a tick with one
outcome, the spec's.

Read aloud: what a tick adds was put on the wire by the validator. -/
theorem step_sent_of_tick_send {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) {i t : ℕ} {v : V}
    -- the step `i` is the tick of every awake validator at `t`
    (hl : x.lbl i = Event.tick v t)
    -- `v` is awake and outside the adversary set at `t`
    (hmem : v ∈ A.awakeAtTime x t \ A.corruptedAtTime x t) :
    ∃ (n' : M.N) (sent : List (NamedObject V)),
      .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v t) (t : Int) ∧
        x.st (i + 1) v = n' ∧ ∀ o ∈ sent, (⟨v, o⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i :=
  (tick_step_outcome M F) x R E hl (Finset.mem_sdiff.1 hmem).1 (Finset.mem_sdiff.1 hmem).2

/-- A Goldfish vote that enters a validator's pool of a slot at a step is carried by an object
that validator put on the wire at that step: its own tick's send, or the re-send of the object
delivered to it.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `k`: the step; `v`: the validator; `s`: the slot; `vote`: the vote;
- `o`: the object put on the wire.

Read aloud: a vote a step adds was put on the wire. -/
theorem step_pool_new (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) {k : ℕ} {v : V} {s : Slot}
    {vote : GoldfishVote V}
    -- `vote` is in `v`'s votes of slot `s` after the step
    (hv : vote ∈ (x.st (k + 1) v).votesHeld s)
    -- `vote` is not in `v`'s votes of slot `s` before the step
    (hn : vote ∉ (x.st k v).votesHeld s) :
    ∃ o : NamedObject V, Carried o vote ∧
      (⟨v, o⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (k + 1) - x.sent k := by
  rcases (step_cases_per_step M F) x R E k v with h | ⟨t, n', sent, hl, -, hok, h, hw⟩ |
      ⟨sm, hl, -, h⟩ | ⟨⟨tR, keep, hl⟩, -, -⟩
  · rw [h] at hv
    exact absurd hv hn
  · rw [h] at hv
    have hin : x.tickInput v t = x.st k v := by
      unfold Trace.tickInput
      rw [(tickStep_eq_of_lbl M) x E hl]
    rw [hin] at hok
    have hP := F.tk.tick_prov S.C S.P S.X _ (t : Int) n' sent hok
    obtain ⟨o, ho, hc⟩ := hP.1 s vote hv hn
    exact ⟨o, hc, hw o ho⟩
  · rw [h] at hv
    exact ⟨sm.msg, (F.rcv.receive_new S.C S.P S.X _ sm.msg).1 s vote hv hn,
      (step_sent_of_delivery M F) R hl
        ((GoldilocksCorrectness.Record.Proofs.Routines.mem_relayedObjects_self M F) sm.msg)⟩
  · have hv' : vote ∈ M.votesHeld (x.st (k + 1) v) s := hv
    rw [(wake_case_votesHeld M F) x R hl] at hv'
    exact absurd hv' hn

/-- A block that enters a validator's tree at a step was put on the wire by that validator at
that step, as its own proposal or as the re-send of the block delivered to it; the validator was
outside the adversary set in the configuration the step starts from, and the block's slot is at most the slot
of the validator's clock after the step.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `k`: the step; `v`: the validator; `B`: the block.

Read aloud: a block a step adds was put on the wire. -/
theorem step_tree_new (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) {k : ℕ} {v : V} {B : Block V}
    -- `B` is in `v`'s tree after the step
    (hB : B ∈ (x.st (k + 1) v).tree)
    -- `B` is not in `v`'s tree before the step
    (hn : B ∉ (x.st k v).tree) :
    (⟨v, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (k + 1) - x.sent k ∧
      v ∉ A.corrupted k ∧ B.slot ≤ S.C.slot (x.st (k + 1) v).t := by
  rcases (step_cases_per_step M F) x R E k v with h | ⟨t, n', sent, hl, hact, hok, h, hw⟩ |
      ⟨sm, hl, hact, h⟩ | ⟨⟨tR, keep, hl⟩, -, -⟩
  · rw [h] at hB
    exact absurd hB hn
  · rw [h]
    rw [h] at hB
    have hin : x.tickInput v t = x.st k v := by
      unfold Trace.tickInput
      rw [(tickStep_eq_of_lbl M) x E hl]
    rw [hin] at hok
    have hP := F.tk.tick_prov S.C S.P S.X _ (t : Int) n' sent hok
    obtain ⟨h1, h2⟩ := hP.2 B hB hn
    exact ⟨hw _ h1, Activity.not_mem_corrupted_of_mem_active hact, h2⟩
  · rw [h]
    rw [h] at hB
    obtain ⟨hmsg, hs⟩ := (F.rcv.receive_new S.C S.P S.X _ sm.msg).2 B hB hn
    refine ⟨(step_sent_of_delivery M F) R hl ?_, Activity.not_mem_corrupted_of_mem_active hact, hs⟩
    rw [hmsg]
    exact (GoldilocksCorrectness.Record.Proofs.Routines.mem_relayedObjects_self M F) _
  · rw [(wake_case_tree M F) x R hl] at hB
    exact absurd hB hn

/-- An attestation that enters a validator's held attestations at a step was put on the wire by
that validator at that step, alone or inside a block: its own tick's send, or the re-send of the
object delivered to it.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `k`: the step; `v`: the validator; `a`: the attestation;
- `o`: the object put on the wire.

Read aloud: an attestation a step adds was put on the wire, alone or inside a block. -/
theorem step_attestation_new (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) {k : ℕ} {v : V}
    {a : Attestation V}
    -- `v` holds `a` after the step
    (ha : a ∈ (x.st (k + 1) v).attestationsHeld)
    -- `v` does not hold `a` before the step
    (hn : a ∉ (x.st k v).attestationsHeld) :
    ∃ o : NamedObject V, (o = NamedObject.attest a ∨
        ∃ B : Block V, o = NamedObject.block B ∧ a ∈ B.attestations) ∧
      (⟨v, o⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (k + 1) - x.sent k := by
  rcases (step_cases_per_step M F) x R E k v with h | ⟨t, n', sent, hl, hmem, hok, h, hw⟩ |
      ⟨sm, hl, -, h⟩ | ⟨⟨tRw, keepw, hlw⟩, -, h⟩
  · rw [h] at ha
    exact absurd ha hn
  · rw [h] at ha
    have hin : x.tickInput v t = x.st k v := by
      unfold Trace.tickInput
      rw [(tickStep_eq_of_lbl M) x E hl]
    rw [hin] at hok
    rcases F.tk.tick_prov_attestations S.C S.P S.X _ (t : Int) n' sent hok a ha hn with
      h1 | ⟨B, hB, hB'⟩
    · exact ⟨_, Or.inl rfl, hw _ h1⟩
    · exact ⟨_, Or.inr ⟨B, rfl, hB'⟩, hw _ hB⟩
  · rw [h] at ha
    exact ⟨sm.msg, F.rcv.receive_new_attestations S.C S.P S.X _ sm.msg a ha hn,
      (step_sent_of_delivery M F) R hl
        ((GoldilocksCorrectness.Record.Proofs.Routines.mem_relayedObjects_self M F) sm.msg)⟩
  · rw [h tRw keepw hlw] at ha
    have ha' : a ∈ M.attestationsHeld (M.wake (x.st k v) (tRw : Int)) := ha
    rw [(F.wk.wake_readers _ _).2.2.2.2.2.2.1] at ha'
    exact absurd ha' hn

end Steps

/-! ## Along an execution -/

section Execution

open Framework.StsMultisetLog (SignedMsg)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks.Sts (Setup)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder] {S : Setup V} {A : Activity V}
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- `PoolCovered M Q n`: every Goldfish vote of `n`'s pool of every slot satisfies `Q`.

The variables:
- `M`: the model; `F`: its facts;
- `Q`: the condition; `n`: the node state.

Read aloud: every vote `n` holds satisfies `Q`. -/
def PoolCovered (Q : GoldfishVote V → Prop) (n : M.N) : Prop :=
  ∀ s : Slot, ∀ vote ∈ M.votesHeldSet n s, Q vote

/-- `TreeCovered M Q n`: every block of `n`'s tree other than the genesis block satisfies `Q`.

The variables:
- `M`: the model; `F`: its facts;
- `Q`: the condition; `n`: the node state.

Read aloud: every non-genesis block `n` holds satisfies `Q`. -/
def TreeCovered (Q : Block V → Prop) (n : M.N) : Prop :=
  ∀ B ∈ n.tree, B ≠ Block.genesis → Q B

/-- Every Goldfish vote of a validator's pool at a step entered the sent log at an earlier step,
as a Goldfish vote or inside a block.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `k`: the step; `v`: the validator; `s`: the slot; `vote`: the vote;
- `i`: the step of the send; `sm`: the signed message.

Read aloud: every vote a validator holds was put on the wire. -/
theorem pool_vote_sent (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) {k : ℕ} {v : V} {s : Slot}
    {vote : GoldfishVote V}
    -- `v`'s pool of slot `s` holds `vote` at `k`
    (hv : vote ∈ M.votesHeldSet (x.st k v) s) :
    ∃ i < k, ∃ sm ∈ x.sent (i + 1) - x.sent i, sm.msg = NamedObject.gfVote vote ∨
      ∃ B : Block V, sm.msg = NamedObject.block B ∧ vote ∈ B.votes := by
  induction k with
  | zero =>
      rw [(getElem_zero_st M F) x R] at hv
      have h' := ((GoldilocksCorrectness.Record.Proofs.Routines.mem_pool_iff M F) _ _ _).1 hv
      rw [F.init.initial_votesHeld S.C v s] at h'
      exact absurd h' List.not_mem_nil
  | succ k ih =>
      by_cases hk : vote ∈ M.votesHeldSet (x.st k v) s
      · obtain ⟨i, hi, sm, hsm, hc⟩ := ih hk
        exact ⟨i, by omega, sm, hsm, hc⟩
      · obtain ⟨o, hc, ho⟩ := (step_pool_new M F) x R E
          (((GoldilocksCorrectness.Record.Proofs.Routines.mem_pool_iff M F) _ _ _).1 hv)
          (fun h => hk (((GoldilocksCorrectness.Record.Proofs.Routines.mem_pool_iff M F) _ _ _).2 h))
        exact ⟨k, by omega, ⟨v, o⟩, ho, hc⟩

/-- Every attestation a validator holds at a step entered the sent log at an earlier step, as an
attestation or inside a block.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `k`: the step; `v`: the validator; `a`: the attestation;
- `i`: the step of the send; `sm`: the signed message.

Read aloud: every attestation a validator holds was put on the wire at an earlier step, alone or
inside a block. -/
theorem held_attestation_sent (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) {k : ℕ} {v : V}
    {a : Attestation V}
    -- `v` holds `a` at `k`
    (ha : a ∈ (x.st k v).attestationsHeld) :
    ∃ i < k, ∃ sm ∈ x.sent (i + 1) - x.sent i, sm.msg = NamedObject.attest a ∨
      ∃ B : Block V, sm.msg = NamedObject.block B ∧ a ∈ B.attestations := by
  induction k with
  | zero =>
      rw [(getElem_zero_st M F) x R, F.init.initial_attestationsHeld S.C v] at ha
      exact absurd ha List.not_mem_nil
  | succ k ih =>
      by_cases hk : a ∈ (x.st k v).attestationsHeld
      · obtain ⟨i, hi, sm, hsm, hc⟩ := ih hk
        exact ⟨i, by omega, sm, hsm, hc⟩
      · obtain ⟨o, hc, ho⟩ := (step_attestation_new M F) x R E ha hk
        exact ⟨k, by omega, ⟨v, o⟩, ho, hc⟩

/-- Every validator's pool at every step is covered by "entered the sent log at an earlier step,
as a Goldfish vote or inside a block".

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `k`: the step; `v`: the validator.

Read aloud: every vote a validator holds was put on the wire, at every step. -/
theorem poolCovered_sent (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (k : ℕ) (v : V) :
    PoolCovered M (fun vote => ∃ i < k, ∃ sm ∈ x.sent (i + 1) - x.sent i,
      sm.msg = NamedObject.gfVote vote ∨
        ∃ B : Block V, sm.msg = NamedObject.block B ∧ vote ∈ B.votes) (x.st k v) :=
  fun _ _ hv => (pool_vote_sent M F) x R E hv

/-- Every Goldfish vote of a validator's pool of a slot before the time `t` entered the sent log,
as a Goldfish vote or inside a block, at a step before `stepBefore M x t`.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `t`: the time; `v`: the validator; `s`: the slot; `vote`: the vote;
- `i`: the step of the send; `sm`: the signed message.

Read aloud: a vote held before `t` was put on the wire, alone or in a block, before `t`. -/
theorem pool_vote_sent_before {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {t : ℕ} {v : V} {s : Slot} {vote : GoldfishVote V}
    -- `v`'s pool of slot `s` before `t` holds `vote`
    (hv : vote ∈ M.votesHeldSet (x.stateBefore t v) s) :
    ∃ i < x.stepBefore t, ∃ sm ∈ x.sent (i + 1) - x.sent i,
      sm.msg = NamedObject.gfVote vote ∨
        ∃ B : Block V, sm.msg = NamedObject.block B ∧ vote ∈ B.votes :=
  (pool_vote_sent M F) x R E (k := x.stepBefore t) hv

/-- Every non-genesis block of a validator's tree at a step was put on the wire by that validator
at an earlier step, the step at which it entered the tree: the validator was outside the
adversary set when the step started, its clock after the step was in a slot at least the block's, and
its tree after the step holds the block.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `k`: the step; `v`: the validator; `B`: the block;
- `i`: the step of the send.

Read aloud: every non-genesis block of a validator's tree was put on the wire by the validator at
the step after which its tree first holds it. -/
theorem tree_block_relayed_entry (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) {k : ℕ} {v : V} {B : Block V}
    -- `v`'s tree holds `B` at `k`
    (hB : B ∈ (x.st k v).tree)
    -- `B` is not the genesis block
    (hg : B ≠ Block.genesis) :
    ∃ i < k, (⟨v, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i ∧
      v ∉ A.corrupted i ∧ B.slot ≤ S.C.slot (x.st (i + 1) v).t ∧
      B ∈ (x.st (i + 1) v).tree := by
  classical
  have hex : ∃ m : ℕ, B ∈ (x.st m v).tree := ⟨k, hB⟩
  have h0 : B ∉ (x.st 0 v).tree := by
    rw [(getElem_zero_st M F) x R, F.init.initial_tree S.C v]
    intro h
    exact hg (Finset.mem_singleton.1 h)
  have hpos : Nat.find hex ≠ 0 := by
    intro h
    exact h0 (h ▸ Nat.find_spec hex)
  have hle : Nat.find hex ≤ k := Nat.find_min' hex hB
  obtain ⟨i, hi⟩ : ∃ i : ℕ, Nat.find hex = i + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hni : B ∉ (x.st i v).tree := Nat.find_min hex (by omega)
  have hi1 : B ∈ (x.st (i + 1) v).tree := hi ▸ Nat.find_spec hex
  obtain ⟨h1, h2, h3⟩ := (step_tree_new M F) x R E hi1 hni
  exact ⟨i, by omega, h1, h2, h3, hi1⟩

/-- Every non-genesis block of a validator's tree at a step was put on the wire by that validator
at an earlier step, at which it was outside the adversary set when the step started and after which
its clock was in a slot at least the block's (`tree_block_relayed_entry` without the tree after
the step).

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `k`: the step; `v`: the validator; `B`: the block;
- `i`: the step of the send.

Read aloud: every non-genesis block of a validator's tree was put on the wire by the validator. -/
theorem tree_block_relayed (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) {k : ℕ} {v : V} {B : Block V}
    -- `v`'s tree holds `B` at `k`
    (hB : B ∈ (x.st k v).tree)
    -- `B` is not the genesis block
    (hg : B ≠ Block.genesis) :
    ∃ i < k, (⟨v, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i ∧
      v ∉ A.corrupted i ∧ B.slot ≤ S.C.slot (x.st (i + 1) v).t := by
  obtain ⟨i, hi, h1, h2, h3, -⟩ := (tree_block_relayed_entry M F) x R E hB hg
  exact ⟨i, hi, h1, h2, h3⟩

/-- Every validator's tree at every step is covered by "put on the wire by the validator at an
earlier step, honest when it started, with its clock after it in a slot at least the block's".

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `k`: the step; `v`: the validator.

Read aloud: every non-genesis block of a validator's tree was put on the wire by the validator, at
every step. -/
theorem treeCovered_relayed (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (k : ℕ) (v : V) :
    TreeCovered M (fun B => ∃ i < k, (⟨v, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i ∧
      v ∉ A.corrupted i ∧ B.slot ≤ S.C.slot (x.st (i + 1) v).t) (x.st k v) :=
  fun _ hB hg => (tree_block_relayed M F) x R E hB hg

/-- A non-genesis block a validator holds before the time `t` was put on the wire by that
validator itself, as a re-send of the delivery that admitted it or as its own proposal, at a step
before `stepBefore M x t`; the validator was honest then if it is honest at `t` (corruption is
permanent, `Sched.MonotoneCorruption`); and its clock after that step was in a slot at least the
block's (`block_admissible`'s test that the block's slot is not later than the node's).

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `t`: the time; `v`: the validator; `B`: the block;
- `i`: the step of the send.

Read aloud: a non-genesis block `v` holds before `t` was put on the wire by `v` itself, at a step
before `t`, honest then if honest at `t`, and with `v`'s clock then in a slot at least the
block's. -/
theorem tree_block_relayed_before {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x)
    -- corruption is permanent
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) {t : ℕ} {v : V} {B : Block V}
    -- `v`'s tree before `t` holds `B`
    (hB : B ∈ (x.stateBefore t v).tree)
    -- `B` is not the genesis block
    (hg : B ≠ Block.genesis) :
    ∃ i < x.stepBefore t, (⟨v, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (i + 1) - x.sent i ∧
      (v ∉ A.corruptedAtTime x t → v ∉ A.corrupted i) ∧
      S.C.slot ((x.st (i + 1) v).t) ≥ B.slot := by
  obtain ⟨i, hi, h1, h2, h3⟩ := (tree_block_relayed M F) x R E (k := x.stepBefore t) hB hg
  exact ⟨i, hi, h1, fun _ => h2, h3⟩

/-- A block that a validator outside the adversary set after `k` steps holds at `k` has a slot at
most the slot of the validator's clock value after `k` steps: it entered the tree at an earlier
step with the clock value then in a slot at least the block's (`tree_block_relayed`), and an honest
validator's clock value never goes back (`clockValue_mono`). The genesis block has slot `0`.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `k`: the step; `v`: the
  validator; `B`: the block.

Read aloud: an honest validator holds no block of a slot later than the slot of its own clock
value. -/
theorem slot_le_clockValue_of_mem_tree {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {k : ℕ} {v : V} {B : Block V}
    -- `v` is outside the adversary set after `k` steps
    (hv : v ∉ A.corrupted k)
    -- `v`'s tree holds `B` at `k`
    (hB : B ∈ (x.st k v).tree) :
    B.slot ≤ S.C.slot ((x.clockValue k v : ℕ) : Int) := by
  by_cases hg : B = Block.genesis
  · subst hg
    exact Nat.zero_le _
  obtain ⟨i, hi, -, -, hslot⟩ := (tree_block_relayed M F) x R E hB hg
  rw [(clock_eq_clockValue M F) x R (i + 1) v] at hslot
  exact hslot.trans (GoldilocksCorrectness.Proofs.Routines.slot_mono_int S
    (by exact_mod_cast E.clockValue_mono (show i + 1 ≤ k by omega) hv))

/-- An honest validator's clock value at the step of its tick to `t > 0` is less than `t` when the
tick reads a present `awakeSince`: the clock value was set by an earlier tick, to a value at most `t`
(`clock_mono`) and not `t` (`tick_unique`); a restart sets `awakeSince` to `none`, and only a tick
sets it again (`no_restart_of_tickInput_awakeSince_some`); the initial clock `0` is less than `t`.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `R`: the run's facts; `E`: the environment's facts; `i`: the step of the tick;
  `v`: the validator; `t`: the tick's clock value; `τ`: the `awakeSince` the tick reads.

Read aloud: a tick that reads a present `awakeSince` moves an honest validator's clock forward. -/
theorem clockValue_lt_of_tick_awakeSince_some {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {i t : ℕ} {v : V} {τ : Time}
    -- step `i` is `v`'s tick to `t`, a positive clock value
    (hl : x.lbl i = Event.tick v t) (ht : 0 < t)
    -- the tick reads a present `awakeSince`
    (hτ : (x.st i v).awakeSince = some τ) :
    x.clockValue i v < t := by
  have hv : v ∉ A.corrupted i :=
    Activity.not_mem_corrupted_of_mem_active (E.tick_active i v t hl).1
  have hts : x.tickStep v t = i := (tickStep_eq_of_lbl M) x E hl
  rcases x.clockValue_cases i v with ⟨h0, -⟩ | ⟨j, hj, hset, hno⟩
  · rw [h0]; exact ht
  · rcases hset with hset | ⟨keep, hset⟩
    · have hle := E.clock_mono j i v _ t hj hv (Or.inl hset) (Or.inl hl)
      have hne : x.clockValue i v ≠ t := fun h => by
        rw [h] at hset
        exact absurd (E.tick_unique j i v t hset hl) (by omega)
      omega
    · have hτ' : (x.tickInput v t).awakeSince = some τ := by
        unfold Trace.tickInput; rw [hts]; exact hτ
      exact absurd hset ((no_restart_of_tickInput_awakeSince_some M F) x R E hτ' (by omega)
        (fun l t' h1 h2 => (hno l h1 (by omega)).1 t') _ keep)

end Execution

end GoldilocksCorrectness.Record.Proofs.Executions

