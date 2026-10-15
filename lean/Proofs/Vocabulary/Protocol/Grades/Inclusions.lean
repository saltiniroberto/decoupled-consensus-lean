module
public import Proofs.Vocabulary.Protocol.Store.BoundaryRows
public import Proofs.Vocabulary.Protocol.ChainState.JustificationCertificates
public import Proofs.Vocabulary.Protocol.Handlers.MaximumCarrier
public import Proofs.Vocabulary.Protocol.Handlers.JustificationCarrier
public import Proofs.Vocabulary.Protocol.ChainState.EntryHeight
public import Proofs.Vocabulary.Internal.Definitions.NamedJointOutage
public import Proofs.Vocabulary.Protocol.Handlers.RelayGuards
import Proofs.Vocabulary.Protocol.Handlers.FinalizationBridge
import Proofs.Vocabulary.Protocol.ChainState.FinalityCertificates
import Proofs.Vocabulary.Execution.HealthyLocalFacts
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar

@[expose] public section

/-!
# Expiry-window arithmetic

Membership of `k` in `latest_window η r` is exactly `r − η ≤ k < r`.
-/
namespace DecoupledConsensusModel.Proofs.NamedOutageClosure
open Execution Internal.NamedOutageEntry Internal.NamedStableChainOutage
open Internal.NamedJointOutage DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

local instance decidableNeedsSGInclusions (S : Setup V) (rho : NamedRun V)
    (P : NamedBlock V) (r : Round) (v : V) :
    Decidable (NeedsSG S rho P r v) :=
  inferInstanceAs (Decidable (¬ Block.Preceq P.erase
    (NamedRun.readAt S rho (domain S.E S.hc r .g1) v).st.core.F))


/-! ## Window arithmetic -/


private theorem window_witness : ∀ eta r k : Nat, r - eta ≤ k → k < r →
    k - (r - eta) < min r eta ∧ k = r - eta + (k - (r - eta)) := by
  intro eta r k h1 h2
  exact ⟨by omega, by omega⟩

/-- `r − η ≤ k < r` puts `k` in `latest_window η r`. -/
theorem mem_latest_window {eta r k : Round} (hlo : r - eta ≤ k) (hhi : k < r) :
    k ∈ Protocol.latest_window eta r := by
  simp only [Protocol.latest_window, List.mem_range', Nat.one_mul]
  exact ⟨k - (r - eta), (window_witness eta r k hlo hhi).1,
    (window_witness eta r k hlo hhi).2⟩

/-- Membership of `k` in `latest_window eta r` gives `r − eta ≤ k < r`. -/
theorem window_bounds {eta r k : Nat} (hk : k ∈ Protocol.latest_window eta r) :
    r - eta ≤ k ∧ k < r := by
  simp only [Protocol.latest_window, List.mem_range', Nat.one_mul] at hk
  obtain ⟨i, hi, heq⟩ := hk
  omega


end DecoupledConsensusModel.Proofs.NamedOutageClosure

end
