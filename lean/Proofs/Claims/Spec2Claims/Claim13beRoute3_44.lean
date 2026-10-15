import Proofs.Claims.Spec2Claims.Claim13bStepFin
import Proofs.Claims.Spec2Claims.Claim13beRoute3_5
import Proofs.Claims.Spec2Claims.Claim13beRoute3_40
import Proofs.Claims.Spec2Claims.Claim13beRoute3_43
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedAttestation_erase
import Proofs.Claims.Spec2Claims.Claim13bModel_Env_W
import Proofs.Claims.Spec2Claims.Claim13bModel_weightOf

/-!
# Per-instant admissibility fields

The bundle `AdmissibleFieldsOn` of the run fields read with the honest set given per instant by a
family `Hs`, and the fact that some validator is not held at the instant `0`.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

section Definitions

open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic

/-! ## The bundle of admissibility fields -/

/-- The fields of a run read with the honest set taken from the family `Hs` at the instant each
    field reads it, from the lower instant `lo` on, and with run blocks read through `Xb`: the
    events are sorted and in the horizon, ticks are public and indexed once, deliveries are
    well-formed with their dependencies present, honest validators tick, broadcast and relay blocks,
    Goldfish votes and attestations within `S.E.Δ`, honest authors emitted what is processed under
    their name, and no two run blocks collide on a root or carry slashable weight. -/
structure AdmissibleFieldsOn (S : Setup V) (rho : NamedRun V) (Hs : Int → Finset V)
    (Xb : Finset V) (lo : Int) : Prop where
  lo_pos : 0 < lo
  horizon_nonneg : 0 ≤ rho.horizon
  sorted : rho.events.Pairwise (fun e f => NamedEvent.key e ≤ NamedEvent.key f)
  in_horizon : ∀ e ∈ rho.events, 0 ≤ NamedEvent.time e ∧ NamedEvent.time e ≤ rho.horizon
  tick_public : ∀ v t, NamedEvent.tick v t ∈ rho.events → PublicTime S t
  tickIndexUnique : TickIndexUnique rho
  wire : ∀ (i : Nat) (v : V) (o : NamedObject V) (t : Int),
    rho.events[i]? = some (.deliver v o t) → NamedReceipt.wellFormed S o = true
  deps : ∀ (i : Nat) (v : V) (o : NamedObject V) (t : Int),
    rho.events[i]? = some (.deliver v o t) →
      NamedReceipt.depsPresent (NamedRun.stateBefore S rho i v).st o = true
  tick_total : ∀ t : Int, lo ≤ t → ∀ v ∈ Hs t, PublicTime S t → t ≤ rho.horizon →
    NamedEvent.tick v t ∈ rho.events
  broadcast : ∀ (v : V) (o : NamedObject V) (t : Int), v ∈ Hs t →
    NamedRun.emits S rho v o t → ∀ w ∈ Hs (t + S.E.Δ), lo ≤ t → t + S.E.Δ ≤ rho.horizon →
      NamedReceipt.excludes (NamedRun.stateBeforeTime S rho (t + S.E.Δ) w).st o = false →
      ∃ t', t ≤ t' ∧ t' < t + S.E.Δ ∧ ∃ j : Nat, NamedRun.actualHandlesAt S rho j w o t'
  relay_block : ∀ (v : V) (i : Nat) (B : NamedBlock V) (t : Int), v ∈ Hs (max t lo) →
    NamedRun.acceptsAt S rho i v (.block B) t → ∀ w ∈ Hs (max t lo + S.E.Δ),
      NamedReceipt.processed (NamedRun.stateBefore S rho (i + 1) w).st (.block B) = false →
      max t lo + S.E.Δ ≤ rho.horizon →
      NamedReceipt.excludes
          (NamedRun.stateBeforeTime S rho (max t lo + S.E.Δ) w).st (.block B) = false →
      ∃ t', t ≤ t' ∧ t' < max t lo + S.E.Δ ∧
        ∃ j : Nat, NamedRun.actualHandlesAt S rho j w (.block B) t'
  relay_block_admit : ∀ (v : V) (i : Nat) (B : NamedBlock V) (t : Int), v ∈ Hs (max t lo) →
    NamedRun.acceptsAt S rho i v (.block B) t → ∀ w ∈ Hs (max t lo + S.E.Δ),
      NamedReceipt.processed (NamedRun.stateBefore S rho (i + 1) w).st (.block B) = false →
      max t lo + S.E.Δ ≤ rho.horizon →
      NamedReceipt.excludes
          (NamedRun.stateBeforeTime S rho (max t lo + S.E.Δ) w).st (.block B) = false →
      ∃ t', t ≤ t' ∧ t' < max t lo + S.E.Δ ∧
        ∃ j : Nat, NamedRun.actualHandlesAt S rho j w (.block B) t' ∧
          (rho.events[j]? = some (.deliver w (.block B) t') →
            B.erase.slot ≤ (NamedRun.stateBefore S rho j w).st.core.s)
  relay_gf_vote : ∀ (v : V) (i : Nat) (u : GoldfishVote V) (t : Int), v ∈ Hs t →
    NamedRun.acceptsAt S rho i v (.gfVote u) t →
    NamedRun.processesAtIndex S rho i v (.gfVote u) → lo ≤ t → ∀ w ∈ Hs (t + S.E.Δ),
      NamedReceipt.processed (NamedRun.stateBefore S rho (i + 1) w).st (.gfVote u) = false →
      t + S.E.Δ ≤ rho.horizon →
      ∃ t', t ≤ t' ∧ t' < t + S.E.Δ ∧
        ∃ j : Nat, NamedRun.actualHandlesAt S rho j w (.gfVote u) t'
  relay_gf_vote_handled : ∀ (v : V) (i : Nat) (u : GoldfishVote V) (t : Int), v ∈ Hs t →
    NamedRun.acceptsAt S rho i v (.gfVote u) t → lo ≤ t → ∀ w ∈ Hs (t + S.E.Δ),
      NamedReceipt.processed (NamedRun.stateBefore S rho (i + 1) w).st (.gfVote u) = false →
      t + S.E.Δ ≤ rho.horizon →
      ∃ t', t ≤ t' ∧ t' < t + S.E.Δ ∧
        ∃ j : Nat, NamedRun.actualHandlesAt S rho j w (.gfVote u) t'
  two_cutoff : ∀ (r : Round) (c₂ : Int) (source : V) (i : Nat) (a : NamedAttestation V)
    (t : Int), source ∈ Hs t →
    NamedRun.acceptsAt S rho i source (.attest a) t → lo ≤ t → t < c₂ →
    a.round ∈ Protocol.latest_window S.hc.η_SG r → ∀ target ∈ Hs (t + S.E.Δ),
      NamedReceipt.processed (NamedRun.stateBefore S rho (i + 1) target).st (.attest a) = false →
      c₂ + S.E.Δ ≤ rho.horizon →
      ∃ td, Protocol.opening S.E S.hc a.round ≤ td ∧ td < c₂ + S.E.Δ ∧
        ∃ j : Nat, NamedRun.actualHandlesAt S rho j target (.attest a) td
  unforgeable : ∀ (v : V) (o : NamedObject V) (t : Int), NamedRun.processes S rho v o t →
    ∀ u ∈ Hs t, o.author = some u → ∃ t', t' ≤ t ∧ NamedRun.emits S rho u o t'
  carried_gf : ∀ (v : V) (B : NamedBlock V) (t : Int), NamedRun.processes S rho v (.block B) t →
    ∀ u ∈ B.gf_votes, u.val_index ∈ Hs t →
      ∃ t', t' ≤ t ∧ NamedRun.emits S rho u.val_index (.gfVote u) t'
  carried_attest : ∀ (v : V) (B : NamedBlock V) (t : Int),
    NamedRun.processes S rho v (.block B) t →
    ∀ a ∈ B.attestations, a.val_index ∈ Hs t →
      ∃ t', t' ≤ t ∧ NamedRun.emits S rho a.val_index (.attest a) t'
  rootCollisionFree : RootCollisionFreeOn S rho Xb
  slashableBound : SlashableBoundOn S rho Xb

end Definitions

/-- If the adversary holds less than a third of the total weight at every instant up to `tAwakeEnd`,
    and `0 ≤ tAwakeEnd`, some validator is not held at the instant `0`. -/
theorem exists_notHeld_zero (S : Setup V) (Sched : Schedule V) {tAwakeEnd : Int}
    (hthird : ∀ t : Int, t ≤ tAwakeEnd →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (h0 : 0 ≤ tAwakeEnd) : ∃ u : V, u ∉ Sched.adv 0 := by
  by_contra hne
  push Not at hne
  have huniv : Sched.adv 0 = Finset.univ := Finset.eq_univ_of_forall hne
  have h := hthird 0 h0
  rw [huniv] at h
  have hw : S.E.electorate.weightOf (Finset.univ : Finset V) = S.E.electorate.totalWeight :=
    weightOf_univ S.E.electorate
  omega

section AtRn

variable (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched) (v : V)
  (n : Nat) {tGAT tAwakeEnd : Int}
  (hsync : SynchronyFromWake S x) (hmono : Sched.MonotoneCorruption)
  (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tAwakeEnd → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
  (hgst : S.E.t_GST ≤ tGAT) (hcv : CommonViewOfFinalizedDescendantsAt S Sched x tGAT)
  (hvalid : ExecutionValid S Sched (interface S Sched) x)
  (hawm : AwakeAtMultiples S Sched)
  (hthird : ∀ t : Int, t ≤ tAwakeEnd →
    3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
  (hn : (x[n].time : Int) ≤ tAwakeEnd)

end AtRn

end DecoupledConsensusModel.Sts
