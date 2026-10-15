module
public import Proofs.Vocabulary.Execution.EmissionShape
public import Proofs.Vocabulary.ModelProperties.Store_toHealing
public import Proofs.Vocabulary.ModelProperties.Block_Preceq
public import Proofs.Vocabulary.ModelProperties.get_sg_root_with
public import Proofs.Vocabulary.Protocol.Handlers.SGArrival
public import Proofs.Vocabulary.Protocol.ChainState.ProposalBridge
public import Proofs.Vocabulary.Internal.Definitions.NamedResult23Statements
import Proofs.Vocabulary.Execution.HealthyLocalFacts
import Proofs.Vocabulary.Protocol.ChainState.EntryHeight
import Proofs.Vocabulary.Protocol.Schedule.SlotInduction
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.RingTheory.WittVector.IsPoly

@[expose] public section


namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution
open Protocol (derive_named)
open Internal.NamedRecoveryRead

variable {V : Type} [DecidableEq V] [Fintype V]


/-! ## Proposal times and round actions -/

/-- Slot proposal times are monotone. -/
theorem proposal_time_mono_local (E : Env V) {s s' : Slot} (h : s ≤ s') :
    Protocol.proposal_time E s ≤ Protocol.proposal_time E s' := by
  unfold Protocol.proposal_time Env.t slotStart
  have hfactor : (0 : Time) ≤ 4 * E.Δ := by
    have hd : (0 : Time) ≤ E.Δ := le_of_lt E.Δ_pos
    exact Int.mul_nonneg (by norm_num) hd
  apply Int.mul_le_mul_of_nonneg_left
  · exact_mod_cast h
  · exact hfactor

/-- If a round action is earlier than the proposal time of slot `s`, one more network delay still
    ends no later than that proposal. -/
theorem action_add_delta_le_proposal_of_lt
    (S : Setup V) {r : Round} {s : Slot}
    (hlt : S.a r < Protocol.proposal_time S.E s) :
    S.a r + S.E.Δ ≤ Protocol.proposal_time S.E s := by
  let k := S.hc.opening_slot r
  have hprev : Protocol.proposal_time S.E (k + 1) < S.a r := by
    have heq : Protocol.proposal_time S.E (k + 1) + 2 * S.E.Δ = S.a r := by
      unfold Protocol.proposal_time Env.t Setup.a Protocol.HealConfig.a slotStart
      simp only [k, Protocol.HealConfig.opening_slot]
      push_cast
      ring
    calc
      Protocol.proposal_time S.E (k + 1) <
          Protocol.proposal_time S.E (k + 1) + 2 * S.E.Δ :=
        lt_add_of_pos_right _ (Int.mul_pos (by norm_num) S.E.Δ_pos)
      _ = S.a r := heq
  have hslots : k + 2 ≤ s := by
    by_contra hnot
    have hslt : s < k + 2 := Nat.lt_of_not_ge hnot
    have hs : s ≤ k + 1 := Nat.lt_succ_iff.mp (by
      simpa only [Nat.succ_eq_add_one] using hslt)
    have hm := proposal_time_mono_local S.E hs
    have : S.a r < Protocol.proposal_time S.E (k + 1) :=
      lt_of_lt_of_le hlt hm
    exact (not_lt_of_ge (le_of_lt hprev)) this
  have hnext : S.a r + S.E.Δ ≤ Protocol.proposal_time S.E (k + 2) := by
    have heq : S.a r + 2 * S.E.Δ = Protocol.proposal_time S.E (k + 2) := by
      unfold Protocol.proposal_time Env.t Setup.a Protocol.HealConfig.a slotStart
      simp only [k, Protocol.HealConfig.opening_slot]
      push_cast
      ring
    have hd0 : (0 : Time) ≤ S.E.Δ := le_of_lt S.E.Δ_pos
    have hd12 : S.E.Δ ≤ 2 * S.E.Δ := by
      calc
        S.E.Δ = 1 * S.E.Δ := by ring
        _ ≤ 2 * S.E.Δ :=
          Int.mul_le_mul_of_nonneg_right (by norm_num) hd0
    calc
      S.a r + S.E.Δ ≤ S.a r + 2 * S.E.Δ :=
        add_le_add (le_refl _) hd12
      _ = Protocol.proposal_time S.E (k + 2) := heq
  exact le_trans hnext (proposal_time_mono_local S.E hslots)

/-- A round action earlier than a slot proposal belongs to a round no later
than that proposal's round. -/
theorem action_round_le_of_lt_proposal
    (S : Setup V) {r : Round} {s : Slot}
    (hlt : S.a r < Protocol.proposal_time S.E s) :
    r ≤ S.hc.round_of s := by
  let k := S.hc.opening_slot r
  have hprev : Protocol.proposal_time S.E (k + 1) < S.a r := by
    have heq : Protocol.proposal_time S.E (k + 1) + 2 * S.E.Δ = S.a r := by
      unfold Protocol.proposal_time Env.t Setup.a Protocol.HealConfig.a slotStart
      simp only [k, Protocol.HealConfig.opening_slot]
      push_cast
      ring
    calc
      Protocol.proposal_time S.E (k + 1) <
          Protocol.proposal_time S.E (k + 1) + 2 * S.E.Δ :=
        lt_add_of_pos_right _ (Int.mul_pos (by norm_num) S.E.Δ_pos)
      _ = S.a r := heq
  have hslots : k + 1 ≤ s := by
    by_contra hnot
    have hslt : s < k + 1 := Nat.lt_of_not_ge hnot
    have hs : s ≤ k := Nat.lt_succ_iff.mp (by
      simpa only [Nat.succ_eq_add_one] using hslt)
    have hm := proposal_time_mono_local S.E hs
    have hkk : Protocol.proposal_time S.E k < S.a r :=
      lt_of_le_of_lt (proposal_time_mono_local S.E (Nat.le_succ k)) hprev
    have : S.a r < Protocol.proposal_time S.E k :=
      lt_of_lt_of_le hlt hm
    exact (not_lt_of_ge (le_of_lt hkk)) this
  rw [← Proofs.HealingLemmas.round_of_opening_succ S.hc r]
  exact Nat.div_le_div_right hslots


/-! ## Heights of named derivations -/


/-- Every named derivation has height at least one: genesis derives the initial
chain state, and each node either keeps its parent's height or advances it. -/
theorem one_le_derive_named_h (E : Env V) (cfg : Protocol.HeightConfig) :
    ∀ B : NamedBlock V, 1 ≤ (derive_named E cfg B).h := by
  intro B
  induction B with
  | genesis => exact Nat.le_refl 1
  | node p sl r gv sup rows pr ih =>
      rcases Proofs.NamedEntryHeight.derive_node_height_cases E cfg p sl r gv sup rows pr with
        hstay | hup
      · rw [hstay]
        exact ih
      · rw [hup]
        exact le_trans ih (Nat.le_succ _)


end Protocol
end DecoupledConsensusModel

end
