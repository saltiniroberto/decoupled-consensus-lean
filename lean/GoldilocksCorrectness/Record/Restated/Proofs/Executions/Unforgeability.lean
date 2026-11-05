module
public import GoldilocksCorrectness.Record.Restated.Statements.Executions.UnforgeabilityDefs
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Provenance
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.RoundKit
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.AttestationStatements
public import GoldilocksCorrectness.Record.Restated.Statements.Routines.ProposalStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Record
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Attestation
public import GoldilocksCorrectness.Record.Restated.Proofs.Routines.Wiring
public import GoldilocksCorrectness.Statements.Executions.UnforgeabilityDefs
public import GoldilocksCorrectness.Statements.Routines.AttestationStatements
public import GoldilocksCorrectness.Statements.Routines.ProposalStatements
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Corruption
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.SentUnforgeable

@[expose] public section

/-!
# Unforgeability, over a model

The theorems of `GoldilocksCorrectness/Proofs/Executions/Unforgeability.lean`, over a model `M`
whose facts `F` hold, for an execution `x` of `protocolOf M S`: under `Unforgeability`, an object of
an honest validator on the wire came from that validator's tick, and the votes are cast by their
owners. The page's routine-level theorems are the facts' fields or have their twins in phase A.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (carries)

open GoldilocksCorrectness.Proofs.Routines (ac_on_tick_sends)

open GoldilocksCorrectness.Proofs.Routines (on_block_eq tick_record_grows tick_sends)

open GoldilocksCorrectness.Proofs.Routines (wake_eq)

open GoldilocksCorrectness.Proofs.Routines (mem_relayedObjects_iff receive_Λ)

namespace GoldilocksCorrectness.Record.Proofs.Executions

open Goldilocks
open GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Statements.Executions (Vocab.goldilocks author)
open GoldilocksCorrectness.Proofs.Routines (DREBRel DREBRel.bind DREBRel.pure DREBRel.ite
  DREBRel.liftM DREBRel.broadcast DREBRel.of_emits DREBRel.mono record_awake_Λ on_attestation_Λ
  create_attestation_cases propose_block_Λ_rel)

/-! ## What the routines write into the anti-slashing record -/

section Routines

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]
variable (M : GoldilocksModel V) (F : Facts M)
include F

end Routines

/-! ## The sent log, the views and the steps -/

section Steps

open Framework.StsMultisetLog (AtomicStep SignedMsg atomic_sent_mono nodeStep_iff_exists tickAllAwakeUpdate_getElem_view applyNodeStepResult_view applyNodeStepResult_sent receive_view_self receive_view_other receive_sent)
open GoldilocksCorrectness.Statements.AbstractTrace (Event Trace Activity EnvFacts)
open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsBy)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (RunFacts)
open GoldilocksCorrectness.Statements.Executions (acObject fgObject)
open GoldilocksCorrectness.Statements.Routines (Δ Δ_F)
open Goldilocks.Sts (Setup relayedObjects)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder] {S : Setup V} {A : Activity V}
variable (M : GoldilocksModel V) (F : Facts M)
include F

/-- The sent log grows along the execution.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `i ≤ j`: the two steps.

Read aloud: the sent log after step `i` is contained in the sent log after every later step `j`. -/
theorem sent_le_of_le (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {i j : ℕ} (hij : i ≤ j) :
    x.sent i ≤ x.sent j := by
  exact R.sent_le hij

/-- A message of the sent log after `i` steps is in the sent log after every later step.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `i ≤ j`: the two steps; `sm`: the message.

Read aloud: a message of the sent log after step `i` is in the sent log after every later step. -/
theorem mem_sent_of_le (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {i j : ℕ}
    {sm : SignedMsg V (NamedObject V)} (hsm : sm ∈ x.sent i) (hij : i ≤ j) :
    sm ∈ x.sent j :=
  Multiset.mem_of_le ((sent_le_of_le M F) x R hij) hsm

/-- A message a step put on the wire is in the sent log after it.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `i`: the step; `sm`: the message.

Read aloud: a message that step `i` put on the wire is in the sent log after that step. -/
theorem mem_sent_of_mem_sub (x : Trace V (NamedObject V) M.N) {i : ℕ}
    {sm : SignedMsg V (NamedObject V)} (hsm : sm ∈ x.sent (i + 1) - x.sent i) :
    sm ∈ x.sent (i + 1) :=
  Multiset.mem_of_le (Multiset.sub_le_self _ _) hsm

/-- What a delivery to `p` puts on the wire is signed by `p` and is an object the wiring re-sends
for the delivered object.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `k`: the step of the delivery; `p`: the receiver; `m`: the delivered
  message; `p'`, `o`: the signer and the object of a message the step put on the wire.

Read aloud: every message a delivery to `p` puts on the wire is signed by `p` and carries an object
the wiring re-sends for the delivered message. -/
theorem sent_of_delivery_step {x : Trace V (NamedObject V) M.N} (R : RunFacts M S x) {k : ℕ} {p : V}
    {m : SignedMsg V (NamedObject V)}
    -- the step `k` delivers `m` to `p`
    (hl : x.lbl k = Event.deliver p m) {p' : V} {o : NamedObject V}
    -- the step `k` put `⟨p', o⟩` on the wire
    (hm : (⟨p', o⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (k + 1) - x.sent k) :
    p' = p ∧ o ∈ M.relayedObjects m.msg := by
  obtain ⟨-, -, hsent⟩ := R.deliver k p m hl
  rw [hsent, add_tsub_cancel_left] at hm
  obtain ⟨o', ho', heq⟩ := Multiset.mem_map.1 hm
  injection heq with h1 h2
  subst h1 h2
  exact ⟨rfl, ho'⟩

/-- Honesty through a later step is honesty through an earlier one.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `i ≤ j`: the two steps; `v`: the validator.

Read aloud: a validator honest through step `j` is honest through every earlier step `i`. -/
theorem honestThrough_of_le (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {i j : ℕ} {v : V}
    (hij : i ≤ j) (h : x.HonestThrough A j v) : x.HonestThrough A i v :=
  fun i' hi' => h i' (le_trans hi' hij)

/-- Honesty through a time is honesty through every step whose time is at most it.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `i`: the step; `t`: the time; `v`: the validator.

Read aloud: a validator outside the adversary set up to time `t` is honest through every step whose
time is at most `t`. -/
theorem honestThrough_of_time_le (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {i : ℕ}
    {t : ℝ} {v : V} (h : A.HonestThroughTime x t v)
    -- the time after `i` steps is at most `t`
    (hi : x.time i ≤ t) : x.HonestThrough A i v :=
  fun i' hi' => h i' (le_trans (R.time_mono hi') hi)

/-- **The spec lemma, generic in the object.** Under unforgeability, a message on the wire after
`k` steps, signed by the validator `v` its object is attributed to, `v` outside the adversary set
up to the time after `k` steps, entered the wire at an earlier step `k'` that is the tick of every
awake validator at some time `t`.

Why: take the first step after which the message is on the wire. A delivery re-sends, under the
receiver's signature, objects of a message already on the wire, so `Unforgeability` puts the
message there already; an adversarial send is signed by a validator in the adversary set; a
forward re-sends a message of a view, already on the wire.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `hU`: unforgeability; `k`: the step; `v`: the validator; `o`: the object;
- `k'`: the step of the first send; `t`: its time.

Read aloud: under unforgeability, a message on the wire signed by the validator its object is
attributed to, that validator honest through the step, was first put on the wire by a tick. -/
theorem authored_from_own_tick (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {k : ℕ} {v : V} {o : NamedObject V}
    -- the object is attributed to `v`
    (ho : author o = some v)
    -- `v`'s signed message with the object `o` is on the wire after `k` steps
    (hm : (⟨v, o⟩ : SignedMsg V (NamedObject V)) ∈ x.sent k)
    (hH : x.HonestThrough A k v) :
    ∃ k' < k, ∃ t : ℕ, x.lbl k' = Event.tick v t ∧
      (⟨v, o⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (k' + 1) - x.sent k' := by
  classical
  have hex : ∃ m : ℕ, (⟨v, o⟩ : SignedMsg V (NamedObject V)) ∈ x.sent m := ⟨k, hm⟩
  have h0 : (⟨v, o⟩ : SignedMsg V (NamedObject V)) ∉ x.sent 0 := by
    rw [R.sent_zero]
    exact Multiset.notMem_zero _
  have hpos : Nat.find hex ≠ 0 := by
    intro h
    exact h0 (h ▸ Nat.find_spec hex)
  have hle : Nat.find hex ≤ k := Nat.find_min' hex hm
  obtain ⟨k', hk'⟩ : ∃ k' : ℕ, Nat.find hex = k' + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hni : (⟨v, o⟩ : SignedMsg V (NamedObject V)) ∉ x.sent k' := Nat.find_min hex (by omega)
  have hi1 : (⟨v, o⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (k' + 1) := hk' ▸ Nat.find_spec hex
  have hdiff : (⟨v, o⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (k' + 1) - x.sent k' := by
    rw [Multiset.mem_sub, Multiset.count_eq_zero.2 hni]
    exact Multiset.count_pos.2 hi1
  have hH' : x.HonestThrough A k' v := (honestThrough_of_le M F) x R (by omega) hH
  cases hl : x.lbl k' with
  | tick p t =>
      -- the tick puts on the wire only messages signed by the ticking validator
      obtain ⟨n', sent, -, -, hsent⟩ := R.tick k' p t hl
      have hd := hdiff
      rw [hsent, add_tsub_cancel_left] at hd
      obtain ⟨o', -, heq⟩ := Multiset.mem_map.1 hd
      injection heq with h1 h2
      subst h1
      exact ⟨k', by omega, t, hl, hdiff⟩
  | restart p tR keep =>
      exfalso
      exact hni (by rw [← (R.restart k' p tR keep hl).2]; exact hi1)
  | deliver p m =>
      exfalso
      obtain ⟨-, hrel⟩ := (sent_of_delivery_step M F) R hl hdiff
      have hmem : m ∈ x.sent k' := (R.deliver k' p m hl).1
      rcases (F.rcv.mem_relayedObjects_iff _ _).1 hrel with h | ⟨B, hB, hc⟩
      · subst h
        exact hni ((sent_unforgeable M F) R E k' m m.msg v hmem (Or.inl rfl) ho hH')
      · exact hni ((sent_unforgeable M F) R E k' m o v hmem (Or.inr (by rw [hB]; exact hc)) ho hH')
  | other =>
      exfalso
      rcases E.other_sent k' _ hl hdiff with h | ⟨hadv, -⟩
      · exact hni h
      · exact hH' _ le_rfl hadv

/-- An attestation that a tick put on the wire under `v`'s signature has its content in `v`'s
record after that step.

Why: the tick's attestation is the one `create_attestation` builds (Lemma 49), and the tick's
final record is the one `create_attestation` returns, which holds the attestation's content.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `i`: the step; `t`: the time of the tick; `v`: the signer; `a`: the
  attestation.

Read aloud: an attestation a tick put on the wire under `v`'s signature has its content in `v`'s
record after that step. -/
theorem attest_sent_recorded (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) {i t : ℕ} {v : V}
    {a : Attestation V}
    -- the step `i` is the tick of every awake validator at `t`
    (hl : x.lbl i = Event.tick v t)
    -- the step `i` put `v`'s signed message with the attestation `a` on the wire
    (hm : (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈
      x.sent (i + 1) - x.sent i) :
    a.content ∈ (x.st (i + 1) v).sentAttestations := by
  obtain ⟨-, n', sent, hrun, ho, hst, -⟩ := (tick_send_step_outcome M F) R E hl hm
  have hInvT : M.nodeInv S.C S.P S.X (x.tickInput v t) :=
    (lem11_node_invariant M F S A x R E (x.tickStep v t) v
      (E.not_mem_corrupted_of_tick (x.lbl_tickStep ⟨i, hl⟩))).1
  obtain ⟨-, -, source, head, -, -, -, hrec, -⟩ :=
    (GoldilocksCorrectness.Record.Statements.Routines.lem49_tick_attests F) S.C S.P S.X _ n' _ sent a
      hrun hInvT ho
  rw [hst, hrec]
  exact Finset.mem_union_right _ (Finset.mem_singleton_self _)

/-- A step keeps every content of a validator's record.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `i`: the step; `v`: the validator.

Read aloud: a step keeps every content of a validator's record. -/
theorem step_record_mono (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (i : ℕ) (v : V) :
    (x.st i v).sentAttestations ⊆ (x.st (i + 1) v).sentAttestations := by
  rcases (step_cases M F) x R E i v with h | ⟨t, n', sent, hl, -, hrun, h, -⟩ | ⟨sm, -, -, h⟩ |
      ⟨⟨tRw, keepw, hlw⟩, -, h⟩
  · rw [h]
  · -- the tick's input state is the state after `i` steps, `i` being the tick's step
    have hin : x.tickInput v t = x.st i v := by
      unfold Trace.tickInput
      rw [(tickStep_eq_of_lbl M) x E hl]
    rw [hin] at hrun
    rw [h]
    exact F.tk.tick_record_grows S.C S.P S.X _ _ _ _ hrun
  · -- a delivery keeps what the node has signed (the field `receive_Λ`)
    rw [h, show (M.receive S.C S.P S.X (x.st i v) sm.msg).sentAttestations =
      (x.st i v).sentAttestations from (F.rcv.receive_Λ S.C S.P S.X (x.st i v) sm.msg).2.2.2]
  · -- a wake keeps what the node has signed (the field `wake_readers`)
    rw [h tRw keepw hlw]
    exact le_of_eq (F.wk.wake_readers _ _).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.symm

/-- The contents of a validator's record grow along the execution.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `v`: the validator; `i ≤ j`: the two steps.

Read aloud: the contents of a validator's record grow along the execution. -/
theorem record_sent_mono (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (v : V) {i j : ℕ} (hij : i ≤ j) :
    (x.st i v).sentAttestations ⊆ (x.st j v).sentAttestations := by
  induction j, hij using Nat.le_induction with
  | base => exact Finset.Subset.refl _
  | succ j _ ih => exact ih.trans ((step_record_mono M F) x R E j v)

/-- The spec lemma for attestations, the proof; the audited statement is in
`Statements/Executions/UnforgeabilityStatements.lean`.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `hU`: unforgeability; `k`: the step;
  `a`: the attestation.

Read aloud: an attestation on the wire under its own validator's signature, that validator never in
the adversary set up to now, was sent by that validator's tick, and its content is in that
validator's record from then on. -/
theorem attestation_from_own_tick (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (k : ℕ) (a : Attestation V)
    -- `a`'s validator's signed message with the attestation `a` is on the wire after `k` steps
    (hm : (⟨a.val_index, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent k)
    (hH : x.HonestThrough A k a.val_index) :
    ∃ k' < k, ∃ t : ℕ, x.lbl k' = Event.tick a.val_index t ∧
      (⟨a.val_index, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (k' + 1) - x.sent k' ∧
      a.content ∈ (x.st (k' + 1) a.val_index).sentAttestations := by
  obtain ⟨k', hk', t, hl, hd⟩ := (authored_from_own_tick M F) x R E rfl hm hH
  exact ⟨k', hk', t, hl, hd, (attest_sent_recorded M F) x R E hl hd⟩

/-- The spec lemma for Goldfish votes, the proof; the audited statement is in
`Statements/Executions/UnforgeabilityStatements.lean`.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `hU`: unforgeability; `k`: the step;
  `vote`: the Goldfish vote.

Read aloud: a Goldfish vote on the wire under its own validator's signature, that validator never in
the adversary set up to now, was sent by that validator's tick. -/
theorem vote_from_own_tick (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (k : ℕ) (vote : GoldfishVote V)
    -- `vote`'s validator's signed message with the vote is on the wire after `k` steps
    (hm : (⟨vote.val_index, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent k)
    (hH : x.HonestThrough A k vote.val_index) :
    ∃ k' < k, ∃ t : ℕ, x.lbl k' = Event.tick vote.val_index t ∧
      (⟨vote.val_index, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
        x.sent (k' + 1) - x.sent k' :=
  (authored_from_own_tick M F) x R E rfl hm hH

/-- Under unforgeability, a message on the wire after `k` steps that carries the Goldfish vote
`vote`, as its object or in the `votes` of its block, puts `vote`'s own signed message on the wire
by then, when `vote`'s validator is outside the adversary set up to the time after `k` steps.

The variables:
- `M`: the model; `F`: its facts;
- `x`: the execution; `hU`: unforgeability; `k`: the step; `sm`: the message; `vote`: the vote.

Read aloud: under unforgeability, a message on the wire that carries a Goldfish vote, as its object
or in its block's votes, puts that vote's own signed message on the wire by then, when the vote's
validator is honest through the step. -/
theorem own_vote_mem_sent (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    {k : ℕ} {sm : SignedMsg V (NamedObject V)} {vote : GoldfishVote V}
    -- `sm` is on the wire after `k` steps
    (hsm : sm ∈ x.sent k)
    -- `sm` carries `vote`, as its object or in the `votes` of the block it carries
    (hc : sm.msg = NamedObject.gfVote vote ∨
      ∃ B : Block V, sm.msg = NamedObject.block B ∧ vote ∈ B.votes)
    (hH : x.HonestThrough A k vote.val_index) :
    (⟨vote.val_index, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈ x.sent k := by
  rcases hc with hc | ⟨B, hB, hvB⟩
  · have h := (sent_unforgeable M F) R E k sm (.gfVote vote) vote.val_index hsm (Or.inl hc.symm)
      rfl hH
    exact h
  · exact (sent_unforgeable M F) R E k sm (.gfVote vote) vote.val_index hsm
      (Or.inr (by rw [hB]; exact Or.inl ⟨vote, hvB, rfl⟩)) rfl hH

/-- `VotesCastByOwner` from unforgeability and permanent corruption, the proof; the audited
statement is in `Statements/Executions/UnforgeabilityStatements.lean`.

Why: a vote's validator outside the adversary set at the step's time was outside it at every
earlier time. When the step is not a tick, it keeps the time, so the message it put on the wire
and `vote`'s own signed message are on the wire after it, and `vote` came from its validator's
tick. When it is a tick, the message is the tick's own Goldfish vote, of the ticking validator, or
its proposal, whose votes were in its pool, hence on the wire before the step.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `hU`: unforgeability; `hMono`:
  permanent corruption.

Read aloud: when signatures are unforgeable and corruption is permanent, every copy of a Goldfish
vote on the wire whose validator is honest at the step descends from that validator's own tick. -/
theorem votesCastByOwner_of_unforgeability (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) : VotesCastByOwner M A x := by
  intro i sm vote hsm hc hadv
  have hH : x.HonestThrough A i vote.val_index := E.honestThroughStep_of_not_mem hadv
  by_cases ho : x.lbl i = Event.other
  · -- a step of another kind: `sm` was on the wire already, or it forges no honest validator
    rcases E.other_sent i sm ho hsm with hold | ⟨-, hforge⟩
    · have hown := (own_vote_mem_sent M F) x R E hold hc hH
      obtain ⟨k', hk', t', hl', hd⟩ := (authored_from_own_tick M F) x R E rfl hown hH
      exact ⟨k', t', by omega, hl', hd⟩
    · have hown : (⟨vote.val_index, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x.sent i := by
        rcases hc with hc | ⟨B, hB, hvB⟩
        · exact hforge _ _ (Or.inl hc.symm) rfl hH
        · exact hforge _ _ (Or.inr (by rw [hB]; exact Or.inl ⟨vote, hvB, rfl⟩)) rfl hH
      obtain ⟨k', hk', t', hl', hd⟩ := (authored_from_own_tick M F) x R E rfl hown hH
      exact ⟨k', t', by omega, hl', hd⟩
  · -- a tick, a restart or a delivery: the vote's own message was on the wire before the step, or
    -- the step is the vote's validator's tick that put it there (read per step: the validator's
    -- honesty is read up to the step `i` only)
    have hcases : (⟨vote.val_index, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
          x.sent i ∨
        ∃ t' : ℕ, x.lbl i = Event.tick vote.val_index t' ∧
          (⟨vote.val_index, NamedObject.gfVote vote⟩ : SignedMsg V (NamedObject V)) ∈
            x.sent (i + 1) - x.sent i := by
      rcases hl : x.lbl i with ⟨p, t⟩ | ⟨p, tR, keep⟩ | ⟨p, m⟩ | _
      · -- a tick of `p`: `sm` is `p`'s own object
        obtain ⟨n', sent, hok, -, hsent⟩ := R.tick i p t hl
        have hd := hsm
        rw [hsent, add_tsub_cancel_left] at hd
        obtain ⟨o', ho', heq⟩ := Multiset.mem_map.1 hd
        have ho'' : o' ∈ sent := by simpa using ho'
        obtain ⟨hI, hvI, -⟩ := (lem11_node_invariant M F S A x R E i p (E.not_mem_corrupted_of_tick hl))
        subst heq
        rcases hc with hc | ⟨B, hB, hvB⟩
        · -- `p`'s own Goldfish vote: `p` is the vote's validator
          have hc' : o' = NamedObject.gfVote vote := hc
          subst hc'
          obtain ⟨-, hvi, -⟩ :=
            F.tk3.tick_vote_head S.C S.P S.X (x.st i p) (t : Int) n' sent vote hok hI ho''
          have hp : vote.val_index = p := by rw [hvi, hvI]
          rw [hp]
          exact Or.inr ⟨t, rfl, hsm⟩
        · -- `p`'s proposal: its votes are of `p`'s pool, on the wire before the step
          have hc' : o' = NamedObject.block B := hB
          subst hc'
          obtain ⟨-, -, -, -, H, votes, support_votes, hvotes, -, -, hBdef⟩ :=
            F.tk3.tick_proposal S.C S.P S.X (x.st i p) (t : Int) n' sent B hok hI ho''
          have hvote' : vote ∈ (x.st i p).votesHeld (S.C.slot (t : Int) - 1) := by
            rw [← hvotes]
            rw [hBdef] at hvB
            exact hvB
          obtain ⟨i', hi', sm', hsm', hc''⟩ := (pool_vote_sent M F) x R E (k := i)
            (((GoldilocksCorrectness.Record.Proofs.Routines.mem_pool_iff M F) _ _ _).2 hvote')
          have hsm'i : sm' ∈ x.sent i :=
            (mem_sent_of_le M F) x R ((mem_sent_of_mem_sub M F) x hsm') (by omega)
          exact Or.inl ((own_vote_mem_sent M F) x R E hsm'i hc'' hH)
      · -- a restart sends nothing
        exfalso
        have hd := hsm
        rw [(R.restart i p tR keep hl).2] at hd
        have hc0 := Multiset.count_pos.2 hd
        rw [Multiset.count_sub] at hc0
        omega
      · -- a delivery: `sm` relays an object of the delivered message `m`, on the wire before
        obtain ⟨hm, -, hsent⟩ := R.deliver i p m hl
        have hd := hsm
        rw [hsent, add_tsub_cancel_left] at hd
        obtain ⟨o', ho', heq⟩ := Multiset.mem_map.1 hd
        subst heq
        have hcm : m.msg = NamedObject.gfVote vote ∨
            ∃ B : Block V, m.msg = NamedObject.block B ∧ vote ∈ B.votes := by
          rcases (F.rcv.mem_relayedObjects_iff _ _).1 ho' with hmo | ⟨B, hB, hvo⟩
          · rw [← hmo]
            exact hc
          · rcases hvo with ⟨vote', hvote', rfl⟩ | ⟨a, -, rfl⟩
            · rcases hc with hc | ⟨B', hB', -⟩
              · have hv' : vote' = vote := NamedObject.gfVote.inj hc
                subst hv'
                exact Or.inr ⟨B, hB, hvote'⟩
              · exact absurd hB' nofun
            · rcases hc with hc | ⟨B', hB', -⟩
              · exact absurd hc nofun
              · exact absurd hB' nofun
        exact Or.inl ((own_vote_mem_sent M F) x R E hm hcm hH)
      · exact absurd hl ho
    rcases hcases with hold | ⟨t', hlt, hnew⟩
    · obtain ⟨k', hk', t'', hl', hd⟩ := (authored_from_own_tick M F) x R E rfl hold hH
      exact ⟨k', t'', by omega, hl', hd⟩
    · exact ⟨i, t', le_rfl, hlt, hnew⟩

end Steps

end GoldilocksCorrectness.Record.Proofs.Executions

