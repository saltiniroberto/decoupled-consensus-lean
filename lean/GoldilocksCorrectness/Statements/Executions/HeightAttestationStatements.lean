module
public import GoldilocksCorrectness.Proofs.Executions.Lemma54
public import GoldilocksCorrectness.Proofs.Executions.Lemma55
public import GoldilocksCorrectness.Proofs.Executions.Lemma53

@[expose] public section

/-!
# The attestations that raise the height, over executions

The audited statements about the attestations of a round and the block after them, each proved in
its own file under `GoldilocksCorrectness/Proofs/Executions/`:

- `attestation_in_pool_by_GST` and Lemma 54, `lem54_honest_attestation_delivered`: an attestation
  an honest validator puts on the wire is in the pool of every validator awake and honest for one
  `Δ_F` after the later of its send time and `GST`;
- Lemma 55, `lem55_honest_validator_attests_for_height`, and its corollary
  `lem55_target_of_fresh_height`: every honest validator whose source at the round's action time is
  the round's first block attests at that block's height naming the block that took its chain into
  that height, unless it already has; at a fresh height the attestation is a target;
- Lemma 53, `lem53_next_honest_proposal_carries_certificate`: the next honest proposal on that
  chain, with a quorum of those attestations in its proposer's pool, raises the height or carries
  the progress quorum.
-/

open GoldilocksCorrectness.Statements.Network

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (Δ_F slotStart supportCutoff dutyWindowStart)

open GoldilocksCorrectness.Statements.Routines (chainStateOf)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec AtomicAction Schedule SignedMsg)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)
open GoldilocksCorrectness.Statements.Routines (expireLocks)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-! ## Lemma 54 -/

/-- **Kit theorem, an honest attestation is in the pool one `Δ_F` after the later of its send and
`GST`.** In an execution that reaches every time, with permanent corruption and attestations
delivered within `Δ_F S` after `GST`: an attestation `a`, well formed, that `v`, honest at `t`,
put on the wire at its tick at `t` is in the pool of every validator `w` awake and honest from
`max t GST` through `max t GST + Δ_F S`, on `w`'s node state before `max t GST + Δ_F S`.

Why: the network delivers `a` to `w` strictly before `max t GST + Δ_F S`; the delivery appends a
well-formed attestation to the pool, and the pool only grows.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous;
- `t`: the time of the send; `v`: the sender; `w`: the receiver; `a`: the attestation.

Read aloud: a send before `GST` reaches every validator awake and honest for one `Δ_F` after
`GST`, and a later send every validator awake and honest for one `Δ_F` after it.

 -/
theorem attestation_in_pool_by_GST (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST t : ℕ) (v w : V) (a : Attestation V)
    -- the execution reaches every time
    (hDiv : TimeDiverges x.toTrace)
    -- corruption is permanent
    (hMono : Sched.MonotoneCorruption)
    -- attestations are delivered within `Δ_F S` after `GST`, to a receiver awake throughout
    (hSyncF : SynchronyFromWake Sched x.toTrace (Δ_F S) GST fgObject)
    -- and to a receiver that wakes, within `Δ_F S` after the later of its wake and `GST`
    (hCatchF : CatchUpOnWake Sched x.toTrace (Δ_F S) GST fgObject)
    -- `v` is honest at `t`
    (hv : v ∉ Sched.adv (t : Int))
    -- `v` put `a` on the wire at its tick at `t`
    (hSend : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake t ∧
      (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    -- `w` is awake and honest from `max t GST` through `max t GST + Δ_F S`
    (hw : ∀ t' : ℕ, max t GST ≤ t' → t' ≤ max t GST + Δ_F S →
      w ∈ Sched.awake (t' : Int) ∧ w ∉ Sched.adv (t' : Int))
    -- `a` is well formed
    (hWF : attestation_well_formed a = true) :
    a ∈ (stateBefore x (max t GST + Δ_F S) w).S.attestations :=
  GoldilocksCorrectness.Proofs.Executions.attestation_in_pool_by_GST S Sched x GST t v w a hDiv
    hMono hSyncF hCatchF hv hSend hw hWF

/-- **Lemma 54, an honest attestation is delivered.** In an execution that reaches every time,
with permanent corruption and attestations delivered within `Δ_F S` after `GST`: an attestation
`a`, well formed, that `v`, honest at `t ≥ GST`, put on the wire at its tick at `t` is in the pool
of every validator `w` awake and honest from `t` through `t + Δ_F S`, on `w`'s node state before
`t + Δ_F S`.

Why: the kit theorem `attestation_in_pool_by_GST`, where `max t GST = t`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `GST`: the time from which the
  network is synchronous;
- `t`: the time of the send; `v`: the sender; `w`: the receiver; `a`: the attestation.

Read aloud: after `GST`, an attestation an honest validator put on the wire at its tick at `t` is
in the pool of every validator awake and honest from `t` through `t + Δ_F`, on that validator's
node state before `t + Δ_F`.

 -/
theorem lem54_honest_attestation_delivered (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (GST t : ℕ) (v w : V) (a : Attestation V)
    -- the execution reaches every time
    (hDiv : TimeDiverges x.toTrace)
    -- corruption is permanent
    (hMono : Sched.MonotoneCorruption)
    -- attestations are delivered within `Δ_F S` after `GST`
    (hSyncF : SynchronyFromWake Sched x.toTrace (Δ_F S) GST fgObject)
    -- and to a receiver that wakes, within `Δ_F S` after the later of its wake and `GST`
    (hCatchF : CatchUpOnWake Sched x.toTrace (Δ_F S) GST fgObject)
    -- the send is at or after `GST`
    (hGST : GST ≤ t)
    -- `v` is honest at `t`
    (hv : v ∉ Sched.adv (t : Int))
    -- `v` put `a` on the wire at its tick at `t`
    (hSend : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake t ∧
      (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    -- `w` is awake and honest from `t` through `t + Δ_F S`
    (hw : ∀ t' : ℕ, t ≤ t' → t' ≤ t + Δ_F S →
      w ∈ Sched.awake (t' : Int) ∧ w ∉ Sched.adv (t' : Int))
    -- `a` is well formed
    (hWF : attestation_well_formed a = true) :
    a ∈ (stateBefore x (t + Δ_F S) w).S.attestations :=
  GoldilocksCorrectness.Proofs.Executions.lem54_honest_attestation_delivered S Sched x GST t v w a
    hDiv hMono hSyncF hCatchF hGST hv hSend hw hWF

/-! ## Lemma 55 -/

/-- **Lemma 55, every honest validator with the honest proposal as its source attests for its
height.** Write `s` for the first slot of round `r`, `a_r` for its action time, which is the support
cutoff of slot `s + 1`, `H` for the height of `B`'s chain state and `T` for the root of its `T_h`.
In an execution that reaches every time, with permanent corruption:
when `v` is awake and honest from the duty window's start of slot `s + 1` to `a_r`; `v`'s update of
slot `s + 1` answers `A'` with `B` saved and fast; every lock entry of `A'` live at `a_r` is `B` or
an ancestor of `B`; `B` is in `v`'s viable tree at `a_r`; and `v`'s record before `a_r` holds no
lock at `H`, or a lock on `T` with every attestation sent at `H` naming `T`: then `v` put at its tick
at `a_r` an attestation of `v` at `H` naming `T` on the wire, or its record before `a_r` already
holds one sent at `H` naming `T`.

Why: `v`'s tick at `a_r` passes the duty test and runs the update of slot `s + 1`, then the
attestation duty on its answer; the source is `B`, the head descends from `B`, so a justification
the head reads at `H` is of `T`, and the validator client builds the attestation for `(H, T)`
unless the record already sent one.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `r`: the round; `s`: its first slot;
- `B`: the source; `v`: the validator; `A'`: the answer of `v`'s update of slot `s + 1`.

Read aloud: every honest validator that confirmed the round's first honest proposal, and is not
locked on another block at its height, has voted for `(H, T)` by the end of its tick at `a_r`.

 -/
theorem lem55_honest_validator_attests_for_height (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched)
    (r s : ℕ) (B : Block V) (v : V) (A' : ACState V)
    -- the execution reaches every time
    (hDiv : TimeDiverges x.toTrace)
    -- corruption is permanent
    (hMono : Sched.MonotoneCorruption)
    -- `s` is the first slot of round `r`, so the action time of `r` is the support cutoff
    -- of slot `s + 1`
    (hs : s = r * S.C.R)
    -- `v` is awake and honest from the duty window's start of slot `s + 1` to `a_r`
    (hv : ∀ t : ℕ, dutyWindowStart S (s + 1) ≤ t → t ≤ supportCutoff S (s + 1) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    -- `v`'s update of slot `s + 1` at `a_r` answers `A'`
    (hUpdate : update_confirmation S.C S.P
        (expireLocks (stateBefore x (supportCutoff S (s + 1)) v).A
          ((supportCutoff S (s + 1) : ℕ) : Int))
        (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S)
        ((supportCutoff S (s + 1) : ℕ) : Int) (s + 1) = .ok A')
    -- `A'` saves `B` as the confirmation of slot `s`
    (hSaved : A'.saved_confirmation s = some B)
    -- `B` is a fast block of `A'`
    (hFast : B ∈ A'.fast_blocks)
    -- every lock entry of `A'` live at `a_r` is on `B` or an ancestor of `B`
    (hLocks : ∀ e ∈ A'.lock_entries,
      is_live (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S)
        ((supportCutoff S (s + 1) : ℕ) : Int) e = true → e.B.AncestorEq B)
    -- `B` is in `v`'s viable tree at `a_r`
    (hViable : B ∈ viable_tree (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S)
      (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S).tree)
    -- `v`'s record before `a_r` holds no lock at `H`, or the lock `T` with every attestation it
    -- sent at `H` naming `T`
    (hRecord : (stateBefore x (supportCutoff S (s + 1)) v).Λ.lock (chainStateOf S.C B).h = none ∨
      ((stateBefore x (supportCutoff S (s + 1)) v).Λ.lock (chainStateOf S.C B).h =
          some (chainStateOf S.C B).T_h.root ∧
        ∀ b ∈ (stateBefore x (supportCutoff S (s + 1)) v).Λ.sent,
          b.h = (chainStateOf S.C B).h → b.T = (chainStateOf S.C B).T_h.root)) :
    (∃ (i : ℕ) (a : Attestation V), x.lbl i = AtomicAction.tickAllAwake (supportCutoff S (s + 1)) ∧
      (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent ∧
      a.val_index = v ∧ a.h = (chainStateOf S.C B).h ∧ a.T = (chainStateOf S.C B).T_h.root) ∨
    (∃ b ∈ (stateBefore x (supportCutoff S (s + 1)) v).Λ.sent,
      b.h = (chainStateOf S.C B).h ∧ b.T = (chainStateOf S.C B).T_h.root) :=
  GoldilocksCorrectness.Proofs.Executions.lem55_honest_validator_attests_for_height S Sched x r s
    B v A' hDiv hMono hs hv hUpdate hSaved hFast hLocks hViable hRecord

/-- **Corollary of Lemma 55, a fresh height gets a target.** Under Lemma 55's hypotheses, when
nothing `v`'s record before `a_r` sent is at `H`, `v` put at its tick at `a_r` a target of `v` at
`H` naming `T` on the wire. Here `s` is the first slot of round `r`, `a_r` the support cutoff of
slot `s + 1`, `H` the height of `B`'s chain state and `T` the root of its `T_h`.

Why: Lemma 55's route to the attestation the validator client builds; with nothing sent at `H`,
the record holds no timeout and no target at `H` (it records exactly what it sent), so the client
builds a target.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `r`: the round; `s`: its first slot;
- `B`: the source; `v`: the validator; `A'`: the answer of `v`'s update of slot `s + 1`.

Read aloud: a validator whose record holds nothing at `B`'s height sends a target.

 -/
theorem lem55_target_of_fresh_height (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched)
    (r s : ℕ) (B : Block V) (v : V) (A' : ACState V)
    -- the execution reaches every time
    (hDiv : TimeDiverges x.toTrace)
    -- corruption is permanent
    (hMono : Sched.MonotoneCorruption)
    -- `s` is the first slot of round `r`, so the action time of `r` is the support cutoff
    -- of slot `s + 1`
    (hs : s = r * S.C.R)
    -- `v` is awake and honest from the duty window's start of slot `s + 1` to `a_r`
    (hv : ∀ t : ℕ, dutyWindowStart S (s + 1) ≤ t → t ≤ supportCutoff S (s + 1) →
      v ∈ Sched.awake (t : Int) ∧ v ∉ Sched.adv (t : Int))
    -- `v`'s update of slot `s + 1` at `a_r` answers `A'`
    (hUpdate : update_confirmation S.C S.P
        (expireLocks (stateBefore x (supportCutoff S (s + 1)) v).A
          ((supportCutoff S (s + 1) : ℕ) : Int))
        (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S)
        ((supportCutoff S (s + 1) : ℕ) : Int) (s + 1) = .ok A')
    -- `A'` saves `B` as the confirmation of slot `s`
    (hSaved : A'.saved_confirmation s = some B)
    -- `B` is a fast block of `A'`
    (hFast : B ∈ A'.fast_blocks)
    -- every lock entry of `A'` live at `a_r` is on `B` or an ancestor of `B`
    (hLocks : ∀ e ∈ A'.lock_entries,
      is_live (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S)
        ((supportCutoff S (s + 1) : ℕ) : Int) e = true → e.B.AncestorEq B)
    -- `B` is in `v`'s viable tree at `a_r`
    (hViable : B ∈ viable_tree (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S)
      (fg_to_ac (stateBefore x (supportCutoff S (s + 1)) v).S).tree)
    -- `v`'s record before `a_r` holds no lock at `H`, or the lock `T` with every attestation it
    -- sent at `H` naming `T`
    (hRecord : (stateBefore x (supportCutoff S (s + 1)) v).Λ.lock (chainStateOf S.C B).h = none ∨
      ((stateBefore x (supportCutoff S (s + 1)) v).Λ.lock (chainStateOf S.C B).h =
          some (chainStateOf S.C B).T_h.root ∧
        ∀ b ∈ (stateBefore x (supportCutoff S (s + 1)) v).Λ.sent,
          b.h = (chainStateOf S.C B).h → b.T = (chainStateOf S.C B).T_h.root))
    -- nothing `v`'s record before `a_r` sent is at `H`
    (hFresh : ∀ b ∈ (stateBefore x (supportCutoff S (s + 1)) v).Λ.sent,
      b.h ≠ (chainStateOf S.C B).h) :
    ∃ (i : ℕ) (a : Attestation V), x.lbl i = AtomicAction.tickAllAwake (supportCutoff S (s + 1)) ∧
      (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent ∧
      a.val_index = v ∧ a.h = (chainStateOf S.C B).h ∧ a.T = (chainStateOf S.C B).T_h.root ∧
      a.τ = false :=
  GoldilocksCorrectness.Proofs.Executions.lem55_target_of_fresh_height S Sched x r s B v A' hDiv
    hMono hs hv hUpdate hSaved hFast hLocks hViable hRecord hFresh

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
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `s''`: the slot of the proposal;
- `q`: the proposer; `B'`: the block; `H'`: its parent; `Q`: the quorum.

Read aloud: the next honest block on `H'` includes the quorum's votes, and so is at the next
height or carries the progress quorum; with target votes, it justifies `H'`'s `T_h`.

 -/
theorem lem53_next_honest_proposal_carries_certificate (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched)
    (s'' : ℕ) (q : V) (B' H' : Block V) (Q : Finset V)
    -- `q` put `B'` on the wire at its tick at the start of slot `s''`
    (hPropose : ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s'') ∧
      (⟨q, NamedObject.block B'⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent)
    -- `B'`'s parent is `H'`
    (hParent : B'.parent = H')
    -- `Q` is a quorum
    (hQ : quorum V ≤ Q.card)
    -- for every member of `Q`, `q`'s pool before the start of slot `s''` holds an attestation of
    -- it at `H'`'s height naming `H'`'s `T_h`
    (hPool : ∀ u ∈ Q, ∃ a ∈ (stateBefore x (slotStart S s'') q).S.attestations,
      a.val_index = u ∧ a.h = (chainStateOf S.C H').h ∧ a.T = (chainStateOf S.C H').T_h.root) :
    ((chainStateOf S.C B').h = (chainStateOf S.C H').h + 1 ∨
      ((chainStateOf S.C B').h = (chainStateOf S.C H').h ∧
        Q ⊆ (chainStateOf S.C B').progress ∧
        B'.slot < (chainStateOf S.C H').T_h.slot + S.C.δt)) ∧
    ((∀ u ∈ Q, ∃ a ∈ (stateBefore x (slotStart S s'') q).S.attestations,
        a.val_index = u ∧ a.h = (chainStateOf S.C H').h ∧
        a.T = (chainStateOf S.C H').T_h.root ∧ a.τ = false) →
      (chainStateOf S.C B').h = (chainStateOf S.C H').h + 1 ∧
        (chainStateOf S.C B').J = (chainStateOf S.C H').T_h) :=
  GoldilocksCorrectness.Proofs.Executions.lem53_next_honest_proposal_carries_certificate S Sched x
    s'' q B' H' Q hPropose hParent hQ hPool

end GoldilocksCorrectness.Statements.Executions
