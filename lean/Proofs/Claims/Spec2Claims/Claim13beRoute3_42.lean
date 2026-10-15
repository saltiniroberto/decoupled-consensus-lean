import Model.Sts.Spec2Claims.Claim13bd
import Proofs.Claims.VocabularyAssumptionsLemmas
import Proofs.Claims.Spec2Claims.Claim13bModel_opening
import Proofs.Claims.Spec2Claims.Claim13bModel_a

/-!
# Validators not held at an instant, carrier rounds, and run blocks over a set

The set `notHeldAt` of validators the adversary does not hold at an instant; carrier rounds and
their recurrence for a family of validator sets indexed by instants; and the run blocks of a run
read through the stores of a given set.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The validators not held at an instant -/

/-- The validators the adversary does not hold at `t`: every validator outside `Sched.adv t`. -/
def notHeldAt (Sched : Schedule V) (t : Int) : Finset V :=
  Finset.univ \ Sched.adv t

omit [Fintype V] in
/-- `v` is in `notHeldAt Sched t` exactly when `v ∉ Sched.adv t`. -/
theorem mem_notHeldAt [Fintype V] {Sched : Schedule V} {t : Int} {v : V} :
    v ∈ notHeldAt Sched t ↔ v ∉ Sched.adv t := by
  simp [notHeldAt]

/-- Under monotone corruption, every validator not held at `t'` is not held at any `t ≤ t'`. -/
theorem notHeldAt_anti {Sched : Schedule V} (hmono : Sched.MonotoneCorruption) {t t' : Int}
    (h : t ≤ t') : notHeldAt Sched t' ⊆ notHeldAt Sched t := by
  intro v hv
  rw [mem_notHeldAt] at hv ⊢
  exact fun hmem => hv (hmono t t' h hmem)

/-- A validator the adversary holds at no instant up to `t` is not held at `t`. -/
theorem honestThroughSet_subset_notHeldAt (Sched : Schedule V) (t : Int) :
    honestThroughSet Sched t ⊆ notHeldAt Sched t := by
  intro v hv
  exact mem_notHeldAt.2 ((mem_honestThroughSet.1 hv) t le_rfl)

/-- Under monotone corruption, a validator not held at `t` is honest through `t`. -/
theorem honestThroughTime_of_mem_notHeldAt {Sched : Schedule V}
    (hmono : Sched.MonotoneCorruption) {t : Int} {v : V} (hv : v ∈ notHeldAt Sched t) :
    HonestThroughTime Sched t v :=
  fun _ ht' => mem_notHeldAt.1 (notHeldAt_anti hmono ht' hv)

/-! ## Carrier rounds for a family of sets -/

/-- Round `r` is a carrier round for the family `Hs`: for `k = 0, 1, 2`, the proposer of slot
    `S.hc.opening_slot r + k` is in `Hs` at that slot's confirmation instant. -/
def ProposerCarrierAtOn (S : Setup V) (Hs : Int → Finset V) (r : Round) : Prop :=
  ∀ k : Nat, k < 3 → S.E.proposer (S.hc.opening_slot r + k) ∈
    Hs (Protocol.confirmation_time S.E (S.hc.opening_slot r + k))

/-- For every round `r` whose opening slot is proposed at or after `t₀` and whose window of `gap`
    rounds ends by `tEnd`, some round from `r` to `r + gap` is a carrier round for `Hs`. -/
def MultiProposerRecurrenceOn (S : Setup V) (Hs : Int → Finset V) (gap : Nat)
    (t₀ tEnd : Int) : Prop :=
  ∀ r : Round, t₀ ≤ Protocol.proposal_time S.E (S.hc.opening_slot r) →
    Protocol.proposal_time S.E (S.hc.opening_slot r) + (gap : Int) * (S.a 1 - S.a 0) ≤ tEnd →
    ∃ r' : Round, r ≤ r' ∧ r' ≤ r + gap ∧ ProposerCarrierAtOn S Hs r'

/-! ## Run blocks read through a set -/

/-- `B` is delivered as an object in `rho`, or some member of `Xb` holds `B` among its bodies after
    some prefix of `rho`'s events. -/
def directBlockInRunOn (S : Setup V) (rho : NamedRun V) (Xb : Finset V) (B : NamedBlock V) :
    Prop :=
  NamedObject.block B ∈ rho.objects ∨
    ∃ v ∈ Xb, ∃ i : Nat, B ∈ (NamedRun.stateBefore S rho i v).st.bodies

/-- `A` is an ancestor of a block that `directBlockInRunOn` admits for `rho` and `Xb`. -/
def blockInRunOn (S : Setup V) (rho : NamedRun V) (Xb : Finset V) (A : NamedBlock V) : Prop :=
  ∃ B : NamedBlock V, directBlockInRunOn S rho Xb B ∧ A.Preceq B

/-- `A` is a run block of `rho` read through the stores of `Xb`; the same as `blockInRunOn`. -/
def RunBlockOn (S : Setup V) (rho : NamedRun V) (Xb : Finset V) (A : NamedBlock V) : Prop :=
  blockInRunOn S rho Xb A

end DecoupledConsensusModel.Sts
