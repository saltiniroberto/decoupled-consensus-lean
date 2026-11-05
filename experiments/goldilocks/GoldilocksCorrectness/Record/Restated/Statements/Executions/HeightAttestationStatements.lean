module
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma54
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma55
public import GoldilocksCorrectness.Record.Restated.Proofs.Executions.Lemma53
public import GoldilocksCorrectness.Record.Restated.Statements.AbstractTrace.ServesDefs

@[expose] public section

/-!
# HeightAttestationStatements, over a model

The statements of `GoldilocksCorrectness/Statements/Executions/HeightAttestationStatements.lean`,
over a model `M` whose facts `F` hold, for an execution `x` of `protocolOf M S`: the attestations of
a round and the block after them (Lemmas 53, 54 and 55). Each is the theorem of the same name of
`Record/Restated/Proofs/Executions/Lemma53.lean`, `Record/Restated/Proofs/Executions/Lemma54.lean`
or `Record/Restated/Proofs/Executions/Lemma55.lean`.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ_F slotStart supportCutoff dutyWindowStart)

namespace GoldilocksCorrectness.Record.Statements.Executions
open GoldilocksCorrectness.Record.Statements.AbstractTrace (releaseOf)

open GoldilocksCorrectness.Statements.AbstractTrace (EnvFactsDelivery SyncedWithin)
open GoldilocksCorrectness.Record.Statements.AbstractTrace (servesMin)

open GoldilocksCorrectness.Statements.Executions (fgObject)

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

/-! ## Lemma 54 -/

/-- **Kit theorem, an honest attestation is in the pool one delay or one sync delay after the later
of its send and `GST`.** In an execution that reaches every time, with attestations delivered within
`Δ_F S` after `GST` and the sync fact for attestations: an attestation `a`, well formed, that `v`,
active from `t` through `max t GST`, put on the wire at its tick at `t`, and still serves at `GST`
when `t < GST`, is in the pool of every validator `w` active from a time more than both clock bounds before
`max t GST` up to its tick to `max t GST + max (Δ_F S) Δs_F`, on the node state that tick starts from
.

Why: when the send is from `GST` on, synchrony from the send delivers `a` to `w`, active since the
send; when it is before `GST`, `v` holds `a` from its tick on and serves it at `GST`, and the sync
fact at `GST` delivers it. The delivery appends a well-formed attestation to the pool, and the pool
only grows.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `A`, `x`: the setup, the activity, the execution; `GST`: the time from which the network is
  synchronous; `Δs_F`: the sync delay for attestations;
- `t`: the time of the send; `v`: the sender; `w`: the receiver; `a`: the attestation.

Read aloud: an attestation that `v`, active from its send through `max t GST` and still serving it
at `GST`, put on the wire at its tick at `t` is held, before `max t GST + max (Δ_F S) Δs_F`, by every
validator active from more than both clock bounds before `max t GST` up to its tick to one delivery
delay or one sync delay, whichever is longer, after it, on the node state that tick starts from.

  -/
theorem attestation_in_pool_by_GST (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST t : ℕ) (v w : V) (a : Attestation V)
    {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    -- attestations are delivered within `Δ_F S` after `GST`, to a receiver active since the send
    {ΔNet_F : ℕ} (E_F : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)

    -- what an honest active validator would serve reaches every validator active from then within `Δs_F`
    {Δs_F : ℕ} (Sy_F : SyncedWithin A x (servesMin M S.C) fgObject (releaseOf M S.C) ΔRedeliver Δs_F GST)
    -- `v` is active from the send through `Δs_F` after `max t GST`, the time it serves `a` at
    (hvA : v ∈ A.activeThroughout x t (max t GST + Δs_F))
    -- when the send is before `GST`, `v` still serves `a` at `GST`: its justified height just before `GST`
    -- is at most `a`'s height
    (hserve : t < GST → M.justifiedHeight (x.stateBefore GST v) ≤ a.h)
    -- `v` put `a` on the wire at its tick at `t`
    (hSend : ∃ i : ℕ, x.lbl i = Event.tick v t ∧
      (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    -- `w`'s window starts at `tStart`, more than `ΔClockAhead + ΔClockBehind` before `max t GST`, and
    -- ends at its tick to `max t GST + max (Δ_F S) Δs_F`
    (tStart : ℤ) (htStart : (tStart : ℝ) + ΔClockAhead + ΔClockBehind < ((max t GST : ℕ) : ℝ))
    (hw : w ∈ A.activeThroughoutToTick x tStart (max t GST + max (Δ_F S) Δs_F))
    -- `a` is well formed
    (hWF : M.attestation_well_formed a = true) :
    a ∈ (x.tickInput w (max t GST + max (Δ_F S) Δs_F)).attestationsHeld :=
  (GoldilocksCorrectness.Record.Proofs.Executions.attestation_in_pool_by_GST M F) S A x R GST t v w a E hNet hSkew hRedeliver E_F hNet_F hSkew_F
    Sy_F hvA hserve hSend (GoldilocksCorrectness.Record.Proofs.Executions.tick_window_ahead_of_activeThroughoutToTick_int M x R E hw htStart) hWF

/-- **Lemma 54, an honest attestation is delivered.** In an execution that reaches every time,
with permanent corruption and attestations delivered within `Δ_F S` after `GST`: an attestation
`a`, well formed, that `v` put on the wire at its tick at `t ≥ GST` is in the pool
of every validator `w` active from a time more than both clock bounds before `t` up to its tick to
`t + Δ_F S`, on the node state `w`'s tick
to `t + Δ_F S` starts from.

Why: the environment delivers `a` to `w` at a step before `w`'s tick to `t + Δ_F S`; the pool
admits a well-formed attestation and only grows.

Why the tick's input: the delivery promise of the environment
puts the delivery at a step before `w`'s tick to `t + Δ_F S`; the conclusion reads that bound
directly, on the node state that tick starts from, whatever the order of the deliveries and the
ticks at one time.

The variables:
- `M`: the model; `F`: its facts;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous;
- `t`: the time of the send; `v`: the sender; `w`: the receiver; `a`: the attestation.

Read aloud: after `GST`, an attestation an honest validator put on the wire at its tick at `t` is
in the pool of every validator active from more than both clock bounds before `t` up to its tick to
`t + Δ_F`, in the node state
that validator's tick to `t + Δ_F` reads.

 -/
theorem lem54_honest_attestation_delivered (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) (GST t : ℕ) (v w : V) (a : Attestation V)
    -- the execution reaches every time
    {GSTe : ℕ} {ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} {ΔNet : ℕ} (E : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet ΔRedeliver GSTe (releaseOf M S.C) acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet : (ΔNet : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S) (hSkew : (ΔClockAhead : ℝ) + ΔClockBehind < Δ S) (hRedeliver : (ΔRedeliver : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ S)
    -- corruption is permanent
    -- attestations are delivered within `Δ_F S` after `GST`
    {ΔNet_F : ℕ} (E_F : EnvFactsDelivery A x ΔClockAhead ΔClockBehind ΔNet_F ΔRedeliver GST (releaseOf M S.C) fgObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks) (hNet_F : (ΔNet_F : ℝ) + ΔClockAhead + ΔClockBehind ≤ Δ_F S) (hSkew_F : (ΔClockAhead : ℝ) + ΔClockBehind < Δ_F S)
    -- and to a receiver that wakes, within `Δ_F S` after the later of its wake and `GST`
    -- the send is at or after `GST`
    (hGST : GST ≤ t)
    -- `v` put `a` on the wire at its tick at `t`
    (hSend : ∃ i : ℕ, x.lbl i = Event.tick v t ∧
      (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    -- `w`'s window starts at `tStart`, more than `ΔClockAhead + ΔClockBehind` before `t`, and
    -- ends at its tick to `t + Δ_F S`
    (tStart : ℤ) (htStart : (tStart : ℝ) + ΔClockAhead + ΔClockBehind < (t : ℝ))
    (hw : w ∈ A.activeThroughoutToTick x tStart (t + Δ_F S))
    -- `a` is well formed
    (hWF : M.attestation_well_formed a = true) :
    a ∈ (x.tickInput w (t + Δ_F S)).attestationsHeld :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem54_honest_attestation_delivered M F) S A x R
    GST t v w a E hNet hSkew hRedeliver E_F hNet_F hSkew_F hGST hSend (GoldilocksCorrectness.Record.Proofs.Executions.tick_window_ahead_of_activeThroughoutToTick_int M x R E hw htStart) hWF

/-! ## Lemma 55 -/

/-- **Lemma 55, every honest validator with the honest proposal as its source attests for its
height.** Write `s` for the first slot of round `r`, `a_r` for its action time, which is the support
cutoff of slot `s + 1`, `H` for the height of `B`'s chain state and `T` for the root of its `T_h`.
In an execution that reaches every time, with permanent corruption:
when `v` is awake and honest from the duty window's start of slot `s + 1` up to its tick to `a_r`; an outcome of
`v`'s tick at `a_r` has `B` saved and fast; every lock entry of that outcome live at `a_r` is `B` or
an ancestor of `B`; `B` is in `v`'s viable tree at `a_r`; and `v`'s record before `a_r` holds no
lock at `H`, or a lock on `T` with every attestation sent at `H` naming `T`: then `v` put at its
tick at `a_r` an attestation of `v` at `H` naming `T` on the wire, or its record before `a_r`
already holds one sent at `H` naming `T`.

Why: `v`'s tick at `a_r` passes the duty test and runs the update of slot `s + 1`, then the
attestation duty on its answer; the source is `B`, the head descends from `B`, so a justification
the head reads at `H` is of `T`, and the validator client builds the attestation for `(H, T)`
unless the record already sent one.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `r`: the round; `s`: its first slot;
- `B`: the source; `v`: the validator; `n'`, `sent`: an outcome of `v`'s tick at the support cutoff
  of slot `s + 1`.

Read aloud: every honest validator that confirmed the round's first honest proposal, and is not
locked on another block at its height, has voted for `(H, T)` by the end of its tick at `a_r`.

 -/
theorem lem55_honest_validator_attests_for_height (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (r s : ℕ) (B : Block V) (v : V) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    -- `s` is the first slot of round `r`, so the action time of `r` is the support cutoff
    -- of slot `s + 1`
    (hs : s = r * S.C.R)
    -- `v` is awake and honest from the duty window's start of slot `s + 1` up to its tick to `a_r`
    (hv : v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.supportCutoff S.C (s + 1)))
    (n' : M.N) (sent : List (NamedObject V))
    -- `v`'s update of slot `s + 1` at `a_r` leaves `n'`
    (hUpdate : .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (M.supportCutoff S.C (s + 1))) ((M.supportCutoff S.C (s + 1) : ℕ) : Int))
    (hAwake : GoldilocksCorrectness.Record.Statements.Routines.AwakeFor M S.C (x.tickInput v (M.supportCutoff S.C (s + 1))) (s + 1))
    -- `n'` saves `B` as the confirmation of slot `s`
    (hSaved : M.savedConfirmation n' s = some B)
    -- `B` is a fast block of `n'`
    (hFast : B ∈ M.fastBlocks n')
    -- every lock entry of `n'` live at `a_r` is on `B` or an ancestor of `B`
    (hLocks : ∀ e ∈ M.lockEntries n',
      M.is_live (x.tickInput v (M.supportCutoff S.C (s + 1)))
        ((M.supportCutoff S.C (s + 1) : ℕ) : Int) e = true → e.B.AncestorEq B)
    -- `B` is in `v`'s viable tree at `a_r`
    (hViable : B ∈ M.viable_tree (M.fg_to_ac (x.tickInput v (M.supportCutoff S.C (s + 1))))
      (M.fg_to_ac (x.tickInput v (M.supportCutoff S.C (s + 1)))).tree)
    -- `v`'s record before `a_r` holds no lock at `H`, or the lock `T` with every attestation it
    -- sent at `H` naming `T`
    (hRecord : (x.tickInput v (M.supportCutoff S.C (s + 1))).sentLock (M.chainStateOf S.C B).h = none ∨
      ((x.tickInput v (M.supportCutoff S.C (s + 1))).sentLock (M.chainStateOf S.C B).h =
          some (M.chainStateOf S.C B).T_h.root ∧
        ∀ b ∈ (x.tickInput v (M.supportCutoff S.C (s + 1))).sentAttestations,
          b.h = (M.chainStateOf S.C B).h → b.T = (M.chainStateOf S.C B).T_h.root)) :
    (∃ (i : ℕ) (a : Attestation V), x.lbl i = Event.tick v (M.supportCutoff S.C (s + 1)) ∧
      (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i ∧
      a.val_index = v ∧ a.h = (M.chainStateOf S.C B).h ∧ a.T = (M.chainStateOf S.C B).T_h.root) ∨
    (∃ b ∈ (x.tickInput v (M.supportCutoff S.C (s + 1))).sentAttestations,
      b.h = (M.chainStateOf S.C B).h ∧ b.T = (M.chainStateOf S.C B).T_h.root) :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem55_honest_validator_attests_for_height M F U) S
    A x R r s B v E hs hv n' sent hUpdate hAwake hSaved hFast hLocks hViable hRecord

/-- **Corollary of Lemma 55, a fresh height gets a target.** Under Lemma 55's hypotheses, when
nothing `v`'s record before `a_r` sent is at `H`, `v` put at its tick at `a_r` a target of `v` at
`H` naming `T` on the wire. Here `s` is the first slot of round `r`, `a_r` the support cutoff of
slot `s + 1`, `H` the height of `B`'s chain state and `T` the root of its `T_h`.

Why: Lemma 55's route to the attestation the validator client builds; with nothing sent at `H`,
the record holds no timeout and no target at `H` (it records exactly what it sent), so the client
builds a target.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `r`: the round; `s`: its first slot;
- `B`: the source; `v`: the validator; `n'`, `sent`: an outcome of `v`'s tick at the support cutoff
  of slot `s + 1`.

Read aloud: a validator whose record holds nothing at `B`'s height sends a target.

 -/
theorem lem55_target_of_fresh_height (U : UniformSchedule M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x)
    (r s : ℕ) (B : Block V) (v : V) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    -- `s` is the first slot of round `r`, so the action time of `r` is the support cutoff
    -- of slot `s + 1`
    (hs : s = r * S.C.R)
    -- `v` is awake and honest from the duty window's start of slot `s + 1` up to its tick to `a_r`
    (hv : v ∈ A.activeThroughoutToTick x (duty_window_start S.C (s + 1)) (M.supportCutoff S.C (s + 1)))
    (n' : M.N) (sent : List (NamedObject V))
    -- `v`'s update of slot `s + 1` at `a_r` leaves `n'`
    (hUpdate : .ok (n', sent) ∈ M.tick S.C S.P S.X (x.tickInput v (M.supportCutoff S.C (s + 1))) ((M.supportCutoff S.C (s + 1) : ℕ) : Int))
    (hAwake : GoldilocksCorrectness.Record.Statements.Routines.AwakeFor M S.C (x.tickInput v (M.supportCutoff S.C (s + 1))) (s + 1))
    -- `n'` saves `B` as the confirmation of slot `s`
    (hSaved : M.savedConfirmation n' s = some B)
    -- `B` is a fast block of `n'`
    (hFast : B ∈ M.fastBlocks n')
    -- every lock entry of `n'` live at `a_r` is on `B` or an ancestor of `B`
    (hLocks : ∀ e ∈ M.lockEntries n',
      M.is_live (x.tickInput v (M.supportCutoff S.C (s + 1)))
        ((M.supportCutoff S.C (s + 1) : ℕ) : Int) e = true → e.B.AncestorEq B)
    -- `B` is in `v`'s viable tree at `a_r`
    (hViable : B ∈ M.viable_tree (M.fg_to_ac (x.tickInput v (M.supportCutoff S.C (s + 1))))
      (M.fg_to_ac (x.tickInput v (M.supportCutoff S.C (s + 1)))).tree)
    -- `v`'s record before `a_r` holds no lock at `H`, or the lock `T` with every attestation it
    -- sent at `H` naming `T`
    (hRecord : (x.tickInput v (M.supportCutoff S.C (s + 1))).sentLock (M.chainStateOf S.C B).h = none ∨
      ((x.tickInput v (M.supportCutoff S.C (s + 1))).sentLock (M.chainStateOf S.C B).h =
          some (M.chainStateOf S.C B).T_h.root ∧
        ∀ b ∈ (x.tickInput v (M.supportCutoff S.C (s + 1))).sentAttestations,
          b.h = (M.chainStateOf S.C B).h → b.T = (M.chainStateOf S.C B).T_h.root))
    -- nothing `v`'s record before `a_r` sent is at `H`
    (hFresh : ∀ b ∈ (x.tickInput v (M.supportCutoff S.C (s + 1))).sentAttestations,
      b.h ≠ (M.chainStateOf S.C B).h) :
    ∃ (i : ℕ) (a : Attestation V), x.lbl i = Event.tick v (M.supportCutoff S.C (s + 1)) ∧
      (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i ∧
      a.val_index = v ∧ a.h = (M.chainStateOf S.C B).h ∧ a.T = (M.chainStateOf S.C B).T_h.root ∧
      a.τ = false :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem55_target_of_fresh_height M F U) S A x R r s
    B v E hs hv n' sent hUpdate hAwake hSaved hFast hLocks hViable hRecord hFresh

/-! ## Lemma 53 -/

/-- **Lemma 53, the next honest proposal carries the certificate.** When `q` put the block `B'` on
the wire at its tick at the start of slot `s''`, `B'`'s parent is `H'`, and for every member `u` of
a quorum `Q` the pool of `q` before that start holds an attestation of `u` at the height of `H'`'s
chain state naming the root of its `T_h`: then `B'`'s chain state has that height plus one, or
keeps it with `Q` in its progress set and `B'`'s slot less than `δt` after `T_h`'s; and when every
one of those attestations is a target, `B'`'s chain state has that height plus one and `H'`'s `T_h`
as its justified block.

Why: a message a tick puts on the wire is what an honest awake validator's tick sent, so `B'` is
`q`'s proposal, which includes every attestation of `q`'s pool valid against `H'`'s
chain state and not on `H'`'s chain; an attestation of the pool at `H'`'s height naming its `T_h`
is valid, and one already on `H'`'s chain is counted in `H'`'s chain state; so every member of `Q`
is counted, and a quorum counted at a height is a certificate.

The variables:
- `M`: the model; `F`: its facts; `U`: its slot layout is uniform; `Fx`: its validators are fixed;
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s''`: the slot of the proposal;
- `q`: the proposer; `B'`: the block; `H'`: its parent; `Q`: the quorum.

Read aloud: the next honest block on `H'` includes the quorum's votes, and so is at the next
height or carries the progress quorum; with target votes, it justifies `H'`'s `T_h`.

 -/
theorem lem53_next_honest_proposal_carries_certificate (U : UniformSchedule M.toSlotLayout)
    (Fx : FixedValidators M.toSlotLayout)
    (S : Setup V) (A : Activity V)
    (x : Trace V (NamedObject V) M.N) (R : RunFacts M S x) {deadline} {release ΔRedeliver} {ΔClockAhead ΔClockBehind : ℝ} (E : EnvFactsBy A x ΔClockAhead ΔClockBehind deadline release ΔRedeliver acObject GoldilocksCorrectness.Statements.Executions.Vocab.goldilocks)
    (s'' : ℕ) (q : V) (B' H' : Block V) (Q : Finset V)
    -- `q` put `B'` on the wire at its tick at the start of slot `s''`
    (hPropose : ∃ i : ℕ, x.lbl i = Event.tick q (M.slotStart S.C s'') ∧
      (⟨q, NamedObject.block B'⟩ : SignedMsg V (NamedObject V)) ∈ x.sent (i + 1) - x.sent i)
    -- `B'`'s parent is `H'`
    (hParent : B'.parent = H')
    -- `Q` is a quorum
    (hQ : quorum V ≤ Q.card)
    -- for every member of `Q`, `q`'s pool before the start of slot `s''` holds an attestation of
    -- it at `H'`'s height naming `H'`'s `T_h`
    (hPool : ∀ u ∈ Q, ∃ a ∈ (x.tickInput q (M.slotStart S.C s'')).attestationsHeld,
      a.val_index = u ∧ a.h = (M.chainStateOf S.C H').h ∧ a.T = (M.chainStateOf S.C H').T_h.root) :
    ((M.chainStateOf S.C B').h = (M.chainStateOf S.C H').h + 1 ∨
      ((M.chainStateOf S.C B').h = (M.chainStateOf S.C H').h ∧
        Q ⊆ (M.chainStateOf S.C B').progress ∧
        B'.slot < (M.chainStateOf S.C H').T_h.slot + S.C.δt)) ∧
    ((∀ u ∈ Q, ∃ a ∈ (x.tickInput q (M.slotStart S.C s'')).attestationsHeld,
        a.val_index = u ∧ a.h = (M.chainStateOf S.C H').h ∧
        a.T = (M.chainStateOf S.C H').T_h.root ∧ a.τ = false) →
      (M.chainStateOf S.C B').h = (M.chainStateOf S.C H').h + 1 ∧
        (M.chainStateOf S.C B').J = (M.chainStateOf S.C H').T_h) :=
  (GoldilocksCorrectness.Record.Proofs.Executions.lem53_next_honest_proposal_carries_certificate M F U Fx)
    S A x R E s'' q B' H' Q hPropose hParent hQ hPool

end GoldilocksCorrectness.Record.Statements.Executions

