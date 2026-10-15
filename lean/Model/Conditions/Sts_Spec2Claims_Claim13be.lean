import Model.Sts.Spec2Claims.Claim13be
import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13bd
import Model.Record.Wiring

/-!
# Network, wake and sleepiness premises

Honest sends, synchrony from wake, the active and attesting validators of a round, the sleepiness
premises, and the common view at the start of a phase, stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Step `k` put `sm` on the wire, and `sm`'s signer is not held by the adversary at `x[k].time`,
    the instant step `k` starts from. -/
def HonestSendAt (M : Record.Model V) (S : Setup V) {Sched : Schedule V} (x : AtomicExec (Record.protocolOf M S) Sched)
    (k : Nat) (sm : SignedMsg V (NamedObject V)) : Prop :=
  sm ∈ x[k + 1].sent - x[k].sent ∧ sm.sender ∉ Sched.adv (x[k].time : Int)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- A message an honest validator put on the wire at step `k` is delivered, at a step after `k` and
    at an instant strictly before the deadline `max (x[k].time) S.E.t_GST + S.E.Δ`, to every
    validator awake at every instant from `x[k + 1].time` through that deadline. -/
def SynchronyFromWake (M : Record.Model V) (S : Setup V) {Sched : Schedule V} (x : AtomicExec (Record.protocolOf M S) Sched) :
    Prop :=
  ∀ (k : Nat) (w : V) (sm : SignedMsg V (NamedObject V)),
    Restated.HonestSendAt M S x k sm →
    w ∈ Sched.awakeThroughout (x[k + 1].time : Int)
      (max (x[k].time : Int) S.E.t_GST + S.E.Δ) →
    ∃ d : Nat, k < d ∧ x.lbl d = AtomicAction.deliver w sm ∧
      (x[k].time : Int) ≤ (x[d].time : Int) ∧
      (x[d].time : Int) < max (x[k].time : Int) S.E.t_GST + S.E.Δ

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The validators awake throughout `wAttest S` before round `r`'s action instant. -/
def activeRoundW (M : Record.Model V) (S : Setup V) (Sched : Schedule V) (r : Nat) : Finset V :=
  Sched.awakeThroughout ((M.a S.hc S.E.Δ r) - wAttest S) ((M.a S.hc S.E.Δ r))

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The validators the awake rule lets attest at round `r`: awake at every time from one delay before
    round `r`'s grade-2 first cutoff to round `r`'s action instant. -/
def attestersAt (M : Record.Model V) (S : Setup V) (Sched : Schedule V) (r : Nat) : Finset V :=
  Sched.awakeThroughout (M.early S.E S.hc r .g2 - S.E.Δ) ((M.a S.hc S.E.Δ r))

/-- The validators the awake rule lets vote at slot `s`: awake at every time from one delay before
    the grade-1 first cutoff of `s`'s round (`11Δ` before that round's action instant) to `s`'s vote
    instant, one delay after the slot's start. -/
def votersAt (M : Record.Model V) (S : Setup V) (Sched : Schedule V) (s : Slot) : Finset V :=
  Sched.awakeThroughout ((M.a S.hc S.E.Δ (M.round_of S.hc s)) - 11 * S.E.Δ) (slotStart S.E.Δ s + S.E.Δ)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- The validators the awake rule lets attest at some round of `[lo, hi]` (the union of
    `attestersAt` over those rounds). -/
def attestersIn (M : Record.Model V) (S : Setup V) (Sched : Schedule V) (lo hi : Nat) : Finset V :=
  (Finset.Icc lo hi).biUnion (Restated.attestersAt M S Sched)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- At every round `r₀ ≥ 1` opening at or after `anchor`, the members of `activeRoundW` at round
    `r₀ − 1` outside the adversary at the next opening outweigh the adversary at the next opening
    together with every other attester of the rounds `r₀ − η_SG` to `r₀ − 1`. -/
def roundSleepinessW (M : Record.Model V) (S : Setup V) (Sched : Schedule V) (anchor : Int) : Prop :=
  ∀ r₀ : Nat, 1 ≤ r₀ → anchor ≤ M.opening S.E S.hc r₀ →
    S.E.electorate.weightOf
        (Sched.adv (M.opening S.E S.hc (r₀ + 1)) ∪
          (Restated.attestersIn M S Sched (r₀ - S.hc.η_SG) (r₀ - 1) \
            (Restated.activeRoundW M S Sched (r₀ - 1) \ Sched.adv (M.opening S.E S.hc (r₀ + 1)))))
      < S.E.electorate.weightOf
          (Restated.activeRoundW M S Sched (r₀ - 1) \ Sched.adv (M.opening S.E S.hc (r₀ + 1)))

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- At every slot `s ≥ 1` starting at or after `anchor`, the members of slot `s − 1`'s committee in
    `activeAtW` and outside the adversary at that slot's confirmation instant outnumber the other
    committee members that the awake rule lets vote at `s − 1` or that the adversary holds at its
    confirmation instant. -/
def committeeSleepinessW (M : Record.Model V) (S : Setup V) (Sched : Schedule V) (anchor : Int) : Prop :=
  ∀ s : Slot, 1 ≤ s → anchor ≤ slotStart S.E.Δ s →
    ((S.E.committee (s - 1) ∩
        (Restated.votersAt M S Sched (s - 1) ∪ Sched.adv (M.confirmation_time S.E (s - 1)))) \
      (activeAtW S Sched (s - 1) \ Sched.adv (M.confirmation_time S.E (s - 1)))).card
      < ((activeAtW S Sched (s - 1) ∩ S.E.committee (s - 1)) \
          Sched.adv (M.confirmation_time S.E (s - 1))).card

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Every named block that a validator honest through `tGAT` holds at a step at or before `tGAT` is
    held, at every step from `tGAT + Δ` on, by every validator honest through that step and awake
    there. -/
def CommonViewAtGAT (M : Record.Model V) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (tGAT : Int) : Prop :=
  ∀ (i j : Nat) (v w : V) (B : NamedBlock V),
    (x[i].time : Int) ≤ tGAT → HonestThroughTime Sched tGAT v →
    B ∈ Restated.Read.blocks M x[i][v].st →
    tGAT + S.E.Δ ≤ (x[j].time : Int) → Restated.HonestThrough M Sched x j w → AtomicAwake x j w →
    B ∈ Restated.Read.blocks M x[j][w].st

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- Every named block `B` that a validator honest through `t₀` holds at a step at or before `t₀` is
    held, at every step from `t₀ + Δ` on, by every validator honest through that step, awake there,
    and whose finalized block is an ancestor of `B` or `B` itself. -/
def CommonViewOfFinalizedDescendantsAt (M : Record.Model V) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (t₀ : Int) : Prop :=
  ∀ (i j : Nat) (v w : V) (B : NamedBlock V),
    (x[i].time : Int) ≤ t₀ → HonestThroughTime Sched t₀ v →
    B ∈ Restated.Read.blocks M x[i][v].st →
    t₀ + S.E.Δ ≤ (x[j].time : Int) → Restated.HonestThrough M Sched x j w → AtomicAwake x j w →
    Block.Preceq (Restated.Read.finalized M x[j][w].st) B.erase →
    B ∈ Restated.Read.blocks M x[j][w].st

end

end DecoupledConsensusModel.Sts.Restated
