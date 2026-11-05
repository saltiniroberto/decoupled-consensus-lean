module
public import GoldilocksCorrectness.Statements.Executions.PhaseDefs
public import GoldilocksCorrectness.Statements.Executions.HealedAttestationDefs
public import GoldilocksCorrectness.Statements.Executions.ConfirmedTipDefs
public import GoldilocksCorrectness.Statements.Executions.QuietRoundDefs
public import GoldilocksCorrectness.Statements.Routines.TickDefs
public import GoldilocksCorrectness.Statements.Routines.ScheduleDefs

@[expose] public section

/-!
# Lemma 89: the definitions

The definitions the events of the phase read:

- `anchorCW S tGAT`, the time from which the one committee premise of the phase holds;
- `RootOffChainAt S Sched x w t X` and `HeadHeightFloorPastAt S Sched x w t h`, the two events at
  a validator's frame;
- `RootIncompatibleAt S Sched x w t X` and `FinalizedIncompatibleAt S Sched x w t X`, a
  validator's root or finalized block conflicting with a block;
- `WindowConfirmation S Sched x Hon a b X`, a member's confirmation of a slot of a window;
- `ConfirmationsChainOn S Sched x Hon a b`, the members' confirmations of a range of slots
  forming one chain;
- `JustifiedWitness S Y h J`, a block whose chain state justified `J` at the height `h`;
- `FrontWindowStable S Sched x Hon s_w s'`, the frames of the members stable through a window of
  slots.

The definitions of Lemma 89's proof on the fast-confirmation route:

- `aR S r`, the action time of round `r`;
- `Hon S Sched σ`, the member set of slot `σ`, `roundMembers S Sched (σ + 1)`;
- `HonestAttestationAt`, an honest validator's attestation put on the wire at a tick;
- `OldHeightAttained`, the bound `H₂` on the old attestations is attained (or is `0`);
- `FastFamily`, the fast block `L`, its ancestors, and every member confirmation of a slot from
  `L`'s round's first slot on, with their ancestors;
- `FastFamilyFrom`, the fast block `L`, its ancestors, and every member confirmation of a slot
  from a given slot on, with their ancestors;
- `RoundBaseAt`, the three facts of a round's first slot that the round's base needs;
- `ProposalAt`, an honest round opening slot's proposal;
- `RootCollisionAtOpening`, the collision disjunct of the top statements;
- `Spoiled`, `QuietWithBase`, the kinds of an opening the count of the climb reads.
- `ForkChoiceChangeAt`, a validator's root moving to its justified block other than an ancestor
  of its old root, or its `head_height_floor` rising.


-/

set_option autoImplicit false

open scoped DC
open DC (DRE)

open GoldilocksCorrectness.Statements.Routines (slotStart voteTime supportCutoff)

open GoldilocksCorrectness.Statements.Routines (chainStateOf)

namespace GoldilocksCorrectness.Statements.Executions

open Framework.StsMultisetLog (AtomicExec Schedule)
open Framework.StsMultisetLog (AtomicAction SignedMsg)
open GoldilocksCorrectness.Statements.View (projectTrace nodeView RootCollisionAtOpeningV)
open Goldilocks
open Goldilocks.Sts (Setup)
open GoldilocksCorrectness.Wiring (protocol)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- `RootOffChainAt S Sched x w t X`: `w`'s fork-choice root before time `t` is not `X` or an
ancestor of `X`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution;
- `w`: the validator; `t`: the time; `X`: the block.

Read aloud: `w`'s root has left `X`'s chain. -/
def RootOffChainAt (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (w : V) (t : ℕ) (X : Block V) : Prop :=
  ¬ (get_fc_root (stateBefore x t w).S).AncestorEq X

/-- `RootIncompatibleAt S Sched x w t X`: `w`'s fork-choice root before time `t` is neither `X`
or an ancestor of `X` nor a descendant of `X`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution;
- `w`: the validator; `t`: the time; `X`: the block.

Read aloud: `w`'s root conflicts with `X`. -/
def RootIncompatibleAt (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (w : V) (t : ℕ) (X : Block V) : Prop :=
  ¬ ((get_fc_root (stateBefore x t w).S).compatible X = true)

/-- `FinalizedIncompatibleAt S Sched x w t X`: `w`'s finalized block before time `t` is neither
`X` or an ancestor of `X` nor a descendant of `X`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution;
- `w`: the validator; `t`: the time; `X`: the block.

Read aloud: `w`'s finalized block conflicts with `X`. -/
def FinalizedIncompatibleAt (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (w : V) (t : ℕ) (X : Block V) : Prop :=
  ¬ ((stateBefore x t w).S.F.compatible X = true)

/-- `WindowConfirmation S Sched x Hon a b X`: `X` is the confirmation some member of `Hon (σ + 1)`
saved for a slot `σ` from `a` to `b`, on its node state right after the support cutoff of slot
`σ + 1`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution;
- `Hon`: one member set per slot; `a`, `b`: the first and the last slot; `X`: the block.

Read aloud: `X` is a member's confirmation of a slot from `a` to `b`. -/
def WindowConfirmation (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (Hon : ℕ → Finset V) (a b : ℕ) (X : Block V) : Prop :=
  ∃ σ, a ≤ σ ∧ σ ≤ b ∧ ∃ v ∈ Hon (σ + 1),
    (stateBefore x (supportCutoff S (σ + 1) + 1) v).A.saved_confirmation σ = some X

/-- `ConfirmationsChainOn S Sched x Hon a b`: for any two slots `σ ≤ σ'` from `a` to `b`, a
confirmation a member of `Hon (σ + 1)` saved for slot `σ` is an ancestor of, or equal to, one a
member of `Hon (σ' + 1)` saved for slot `σ'` when `σ < σ'`, and compatible with it when `σ = σ'`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution;
- `Hon`: one member set per slot; `a`, `b`: the first and the last slot.

Read aloud: the members' confirmations of the slots from `a` to `b` form one chain; the honest
chain does not switch between `a` and `b`. -/
def ConfirmationsChainOn (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (Hon : ℕ → Finset V) (a b : ℕ) : Prop :=
  ∀ (σ σ' : ℕ) (v v' : V) (C C' : Block V), a ≤ σ → σ ≤ σ' → σ' ≤ b →
    v ∈ Hon (σ + 1) → v' ∈ Hon (σ' + 1) →
    (stateBefore x (supportCutoff S (σ + 1) + 1) v).A.saved_confirmation σ = some C →
    (stateBefore x (supportCutoff S (σ' + 1) + 1) v').A.saved_confirmation σ' = some C' →
    (σ < σ' → C.AncestorEq C') ∧ (σ = σ' → C.compatible C' = true)

omit [RootOrder] in
/-- `JustifiedWitness S Y h J`: the chain state of `Y` has justified `J` at the height `h`: its
justification height is `h` and its justified block is `J`.

The variables:
- `S`: the setup; `Y`: the block; `h`: the height; `J`: the justified block.

Read aloud: `Y`'s chain justified `J` at `h`, and nothing after. -/
def JustifiedWitness (S : Setup V) (Y : Block V) (h : Height) (J : Block V) : Prop :=
  (chainStateOf S.C Y).h_j = h ∧ (chainStateOf S.C Y).J = J

/-- `HeadHeightFloorPastAt S Sched x w t h`: `w`'s `head_height_floor` before time `t` (the least
chain-state height of a viable block in its state) is greater than `h`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution;
- `w`: the validator; `t`: the time; `h`: the height.

Read aloud: `w` finds no block of chain-state height `h` viable. -/
def HeadHeightFloorPastAt (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (w : V) (t : ℕ) (h : Height) : Prop :=
  h < head_height_floor (stateBefore x t w).S

/-- `FrontWindowStable S Sched x Hon s_w s'`: the frames of the members are stable from slot
`s_w + k − 1` to slot `s'`:

1. at every slot `s₁` from `s_w + k − 1` to `s' − 1`, every member of `Hon (s₁ + 1)` satisfies
   `StepFrameAt` relative to every confirmation a member of `Hon (σ + 1)` saved for a slot `σ`
   from `s_w + k − 1` to `s₁`;
2. every member of `Hon s'` has its fork-choice root before the vote time of slot `s' + 1` on the
   chain of a live lock block of a member or of a confirmation of slot `s' − 1` of a member.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution;
- `Hon`: one member set per slot; `s_w`: the slot the window is counted from; `s'`: its last
  slot.

Read aloud: through the window no member's frame leaves the chain of the members'
confirmations, and at its last slot every member's root is on the chain of a member's live lock or
confirmation. -/
def FrontWindowStable (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (Hon : ℕ → Finset V) (s_w s' : ℕ) : Prop :=
  (∀ s₁, s_w + S.C.k - 1 ≤ s₁ → s₁ < s' →
    ∀ σ, s_w + S.C.k - 1 ≤ σ → σ ≤ s₁ → ∀ v ∈ Hon (σ + 1), ∀ C : Block V,
      (stateBefore x (supportCutoff S (σ + 1) + 1) v).A.saved_confirmation σ = some C →
      ∀ w ∈ Hon (s₁ + 1), StepFrameAt S Sched x C s₁ w) ∧
  (∀ w ∈ Hon s', ∃ D : Block V,
    ((∃ u ∈ Hon s', ∃ e ∈ (stateBefore x (voteTime S (s' + 1)) u).A.lock_entries,
        is_live (fg_to_ac (stateBefore x (voteTime S (s' + 1)) u).S)
          ((voteTime S (s' + 1) : ℕ) : Int) e = true ∧ e.B = D) ∨
      ∃ v ∈ Hon s',
        (stateBefore x (supportCutoff S s' + 1) v).A.saved_confirmation (s' - 1) = some D) ∧
    (get_fc_root (stateBefore x (voteTime S (s' + 1)) w).S).AncestorEq D)

omit [DecidableEq V] [Fintype V] [RootOrder] in
/-- `aR S r`: the action time of round `r`, the support cutoff of slot `r * R + 1`, where the
confirmation update of slot `r * R` runs and the attestation duty follows it.

Read aloud: `slotStart S (r * R) + 6Δ`. -/
def aR (S : Setup V) (r : ℕ) : ℕ := supportCutoff S (r * S.C.R + 1)

omit [RootOrder] in
/-- `Hon S Sched σ`: the member set of slot `σ`, the validators outside the adversary set at the
support cutoff of slot `σ + 1`, where the update of slot `σ` runs (`roundMembers S Sched (σ + 1)`).
Every updater of slot `σ` (`updaterAt S Sched σ`) is a member of `Hon S Sched σ`.

Read aloud: the validators honest at the update of slot `σ`. -/
def Hon (S : Setup V) (Sched : Schedule V) (σ : ℕ) : Finset V := roundMembers S Sched (σ + 1)

/-- `HonestAttestationAt S Sched x t v a`: the step `i` that is the tick of every awake validator at
the time `t` puts on the wire the attestation `a` of `v`, with `v` awake and outside the adversary
set at `t`.

Read aloud: `v`, honest and awake at `t`, sent `a` at its tick at `t`. -/
def HonestAttestationAt (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (t : ℕ) (v : V) (a : Attestation V) : Prop :=
  ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake t ∧ v ∈ Sched.awake (t : Int) ∧
    v ∉ Sched.adv (t : Int) ∧
    (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[i + 1].sent - x[i].sent

/-- `OldHeightAttained S Sched x T₁ H₂`: every attestation an honest awake validator put on the wire
at a tick before `T₁` has height at most `H₂` (`OldAttestationsAtMost`), and `H₂` is `0` or the
height of such an attestation. This is the threshold `H₂` of the route, taken in the landed form
(the senders honest at the send): the greatest height of an honest attestation before `T₁`.

Read aloud: `H₂` is the greatest height any honest validator attested before `T₁`. -/
def OldHeightAttained (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (T₁ H₂ : ℕ) : Prop :=
  OldAttestationsAtMost S Sched x T₁ H₂ ∧
    (H₂ = 0 ∨ ∃ (t : ℕ) (v : V) (a : Attestation V), t < T₁ ∧
      HonestAttestationAt S Sched x t v a ∧ a.h = H₂)

/-- `FastFamily S Sched x r L s C`: `C` is `L` or an ancestor of `L`, or `C` is a confirmation some
member of `Hon S Sched σ` saved for a slot `σ` from `r * R` to before `s`, or an ancestor of one.
This is the family part A's chain invariant is read for at slot `s`: closed under ancestors, so
that every anchor, root and lock block on the chain is in it.

Read aloud: the fast block's line and every confirmation the members saved since its round. -/
def FastFamily (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (r : ℕ) (L : Block V) (s : ℕ) (C : Block V) : Prop :=
  C.AncestorEq L ∨
    ∃ σ : ℕ, r * S.C.R ≤ σ ∧ σ < s ∧ ∃ v ∈ Hon S Sched σ, ∃ C' : Block V,
      (stateBefore x (supportCutoff S (σ + 1) + 1) v).A.saved_confirmation σ = some C' ∧
      C.AncestorEq C'

/-- `FastFamilyFrom S Sched x s₁ L s C`: `C` is `L` or an ancestor of `L`, or `C` is a confirmation
some member of `Hon S Sched σ` saved for a slot `σ` from `s₁` to before `s`, or an ancestor of one.
`FastFamily S Sched x r L s` is the case `s₁ = r * R`. Part A reads it with `s₁ = r * R + k`: the
members' confirmations of the slots `r * R` to `r * R + k − 1` are left out, because a lock made
before slot `r * R + 1` on a strict descendant of `L` can pull honest votes onto one branch above
`L` while a member confirms a block on another, and a member's root can later conflict with that
confirmation.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution;
- `s₁`: the first slot whose confirmations are in the family; `L`: the fast block;
- `s`: the slot the family is read at (its confirmations are those of slots before `s`);
- `C`: the block.

Read aloud: the fast block's line and every confirmation the members saved from slot `s₁` on. -/
def FastFamilyFrom (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (s₁ : ℕ) (L : Block V) (s : ℕ) (C : Block V) : Prop :=
  C.AncestorEq L ∨
    ∃ σ : ℕ, s₁ ≤ σ ∧ σ < s ∧ ∃ v ∈ Hon S Sched σ, ∃ C' : Block V,
      (stateBefore x (supportCutoff S (σ + 1) + 1) v).A.saved_confirmation σ = some C' ∧
      C.AncestorEq C'

/-- `RoundBaseAt S Sched x B s`: the three facts of the first slot `s` of a round with the honest
proposal `B` that the round's base reads: before the vote time of slot `s`, every member of
`Hon S Sched s` has its fork-choice root `B.parent` or an ancestor of it and its
`head_height_floor` (the least chain-state height of a viable block in its state) at most the
chain-state height of `B.parent`; before the action time `supportCutoff S (s + 1)`, every member
has its root `B` or an ancestor of `B` and its `head_height_floor` at most `B`'s chain-state
height; and every lock entry a member's revocation of slot `s` leaves live is on `B.parent` or an
ancestor of it. The first two are the first two clauses of `QuietRound`; the third is `lem80wq`'s
`hLocksW`.

Read aloud: at the round's first slot the members' frames follow the proposal's parent and then
the proposal, and no live lock pulls a vote off the parent's chain. -/
def RoundBaseAt (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (B : Block V) (s : ℕ) : Prop :=
  (∀ w ∈ Hon S Sched s, (get_fc_root (stateBefore x (voteTime S s) w).S).AncestorEq B.parent ∧
    head_height_floor (stateBefore x (voteTime S s) w).S ≤ (chainStateOf S.C B.parent).h) ∧
  (∀ v ∈ Hon S Sched s, (get_fc_root (stateBefore x (supportCutoff S (s + 1)) v).S).AncestorEq B ∧
    head_height_floor (stateBefore x (supportCutoff S (s + 1)) v).S ≤ (chainStateOf S.C B).h) ∧
  (∀ w ∈ Hon S Sched s, ∀ A' : ACState V,
    revoke_locks S.P (GoldilocksCorrectness.Statements.Routines.expireLocks
      (stateBefore x (voteTime S s) w).A ((voteTime S s : ℕ) : Int))
      (fg_to_ac (stateBefore x (voteTime S s) w).S) ((voteTime S s : ℕ) : Int) s = .ok A' →
    ∀ e ∈ A'.lock_entries,
      is_live (fg_to_ac (stateBefore x (voteTime S s) w).S) ((voteTime S s : ℕ) : Int) e = true →
      e.B.AncestorEq B.parent)

/-- `ProposalAt S Sched x s B`: the proposer of slot `s` put the block `B` on the wire at its tick
at the start of slot `s`.

Read aloud: `B` is slot `s`'s proposal. -/
def ProposalAt (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (s : ℕ) (B : Block V) : Prop :=
  ∃ i : ℕ, x.lbl i = AtomicAction.tickAllAwake (slotStart S s) ∧
    (⟨S.P.proposer s, NamedObject.block B⟩ : SignedMsg V (NamedObject V)) ∈
      x[i + 1].sent - x[i].sent

/-- `RootCollisionAtOpening S Sched x r m`: for some opening `i ≤ m`, the proposer of slot
`r i * R` put a block `B` on the wire at its tick at that slot's start, and some block the
proposer held before that start has `B`'s root.

Defined as its view form: `RootCollisionAtOpeningV` with
Goldilocks's vocabulary `Vocab.goldilocks`, on the view of `x`, `projectTrace nodeView x.toTrace`,
whose node states are read as each validator's finalized block, confirmed tip (`confirmedOf`) and
held blocks. `rootCollisionAtOpening_unfold` (`Proofs/View/Bridges.lean`) reads it on the
execution's node states.

Read aloud: some honest round opening slot's proposal has the root of a block its proposer already held. -/
def RootCollisionAtOpening (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (r : ℕ → ℕ) (m : ℕ) : Prop :=
  RootCollisionAtOpeningV Vocab.goldilocks S (projectTrace nodeView x.toTrace) r m

/-- `Spoiled S Sched x r i`: opening `i` of the sequence `r` is not quiet relative to its own
confirmations: some proposal `B` of its first slot fails `QuietRoundOnConfirmations` with the
member sets `Hon S Sched` and the next opening's first slot `r (i + 1) * R`.

Read aloud: opening `i`'s round is spoiled. -/
def Spoiled (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (r : ℕ → ℕ) (i : ℕ) : Prop :=
  ∃ B : Block V, ProposalAt S Sched x (r i * S.C.R) B ∧
    ¬ QuietRoundOnConfirmations S Sched x (Hon S Sched) B (r i * S.C.R) (r (i + 1) * S.C.R)

/-- `QuietWithBase S Sched x r i`: opening `i` is quiet relative to its own confirmations and the
window of `2k − 1` slots before its first slot is stable (`FrontWindowStable` with the member sets
`Hon S Sched`).

Read aloud: opening `i`'s round is quiet and has its base. -/
def QuietWithBase (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (r : ℕ → ℕ) (i : ℕ) : Prop :=
  (∀ B : Block V, ProposalAt S Sched x (r i * S.C.R) B →
    QuietRoundOnConfirmations S Sched x (Hon S Sched) B (r i * S.C.R) (r (i + 1) * S.C.R)) ∧
  FrontWindowStable S Sched x (Hon S Sched) (r i * S.C.R - 2 * S.C.k) (r i * S.C.R - 1)

/-- `ForkChoiceChangeAt S Sched x w t`: at the time `t`, `w`'s fork choice changes in a way a window
can fail on: after `t`, `w`'s `h_max` is its `h_j + 1` and its root (`get_fc_root` of its FG state
before `t + 1`) is its justified block `J`, so that `get_fc_root` returns `J` by its first case, and
that root is neither `w`'s root before `t` nor an ancestor of it; or `w`'s `head_height_floor`
after `t` is greater than before.

A root that moves to an ancestor (from `J` to `F`) is not a change here: everything compatible with
the old root is compatible with the new one. During the climb such a move comes with a rise of
`head_height_floor` or with no change at all. A root that moves from
`F` to a descendant `J` through `get_fc_root`'s first case is a change: blocks off `J`'s chain leave
the fork choice. The conjunct `h_max = h_j + 1` leaves
out one case: `w`'s finalized block moves onto its justified block while `h_max ≥ h_j + 2`, so that
the root, `get_fc_root`'s second case (the finalized block), happens to equal `J`. That move
changes no viable head of `w`.

The variables:
- `S`, `Sched`, `x`: the setup, the schedule, the execution; `w`: the validator; `t`: the time.

Read aloud: at `t`, `w`'s root becomes its justified block through the case `h_max = h_j + 1`,
other than an ancestor of its old root, or its least viable height rises. -/
def ForkChoiceChangeAt (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (w : V) (t : ℕ) : Prop :=
  (get_fc_root (stateBefore x (t + 1) w).S = (stateBefore x (t + 1) w).S.J ∧
    (stateBefore x (t + 1) w).S.h_max = (stateBefore x (t + 1) w).S.h_j + 1 ∧
    ¬ (get_fc_root (stateBefore x (t + 1) w).S).AncestorEq (get_fc_root (stateBefore x t w).S)) ∨
  head_height_floor (stateBefore x t w).S < head_height_floor (stateBefore x (t + 1) w).S

end GoldilocksCorrectness.Statements.Executions
