module
public import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.ActionSourceCore
public import Proofs.Vocabulary.Protocol.Store.RawSource
public import Proofs.Vocabulary.Protocol.ChainState.ProposalBridge
public import Proofs.Vocabulary.ModelProperties.Store_toHealing
public import Proofs.Vocabulary.ModelProperties.Store_sg_pool
public import Proofs.Vocabulary.ModelProperties.get_sg_vote_with
public import Proofs.Vocabulary.ModelProperties.get_sg_root_with
public import Proofs.Vocabulary.ModelProperties.currentSGVote
public import Proofs.Vocabulary.ModelProperties.deepest_clear
public import Proofs.Vocabulary.ModelProperties.Block_Preceq
public import Proofs.Vocabulary.ModelProperties.NamedProfile_gradeContract
public import Proofs.Vocabulary.ModelProperties.NamedDuties_update_confirmation_with
public import Proofs.Vocabulary.ModelProperties.update_confirmation_with
public import Proofs.Vocabulary.ModelProperties.confirmationReadFrom
public import Proofs.Vocabulary.ModelProperties.NamedStore_setClock
public import Proofs.Vocabulary.ModelProperties.get_fg_root
import Proofs.Vocabulary.Generic.PostGSTCarrierAdmissionCore
import Proofs.Vocabulary.Objects.BlockVisibilityCore
import Proofs.Vocabulary.Protocol.Grades.Ladder
import Proofs.Vocabulary.Protocol.Schedule.Action
import Proofs.Vocabulary.Protocol.Schedule.SlotInduction
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.RingTheory.WittVector.IsPoly
import Proofs.Vocabulary.Protocol.ForkChoice.Goldfish.RetainedRows

@[expose] public section

/-!
# The round-action SG vote and its store

The SG vote a validator emits at a round's action, the facts that its block is in the action store
and in the store before the action, the honest-weight threshold bound, and the viability of `Σ.F`
across `update_finality`.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Protocol (HealConfig)
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]


/-! ## The honest-weight threshold -/

/-- A strict honest-weight majority has at least the grade threshold `m = floor(W/2) + 1`. -/
theorem honestWeight_ge_m
    {S : Setup V} {H : Finset V} (hmajority : HonestWeightMajority S H) :
    S.E.m ≤ S.E.electorate.weightOf H := by
  have hsum := S.E.electorate.weightOf_add_weightOf_sdiff H
  unfold HonestWeightMajority at hmajority
  unfold Env.m Electorate.strictMajorityThreshold
  omega


/-! ## The round-action SG vote -/

/-- The SG vote emitted by validator `v` at round `r`'s action. -/
def actionSGVoteAt (S : Setup V) (rho : Run V) (v : V) (r : Round) :
    Protocol.SGVote V :=
  ⟨v, r, some (actionSGBlockAt S rho v r).root⟩


/-- The SG vote of the attestation `actionAttestationAt S rho v r` is `actionSGVoteAt S rho v r`. -/
theorem sgVote_actionAttestationAt
    (S : Setup V) (rho : Run V) (v : V) (r : Round) :
    Protocol.sgVote (actionAttestationAt S rho v r).erase =
      actionSGVoteAt S rho v r := by
  obtain ⟨hval, hround, hconf⟩ := actionAttestationAt_shape S rho v r
  have hsplit : Protocol.sgVote (actionAttestationAt S rho v r).erase =
      ⟨(actionAttestationAt S rho v r).val_index,
        (actionAttestationAt S rho v r).round,
        (actionAttestationAt S rho v r).confirmed⟩ := by
    rw [← NamedOutageClosure.sgVote_val, ← NamedOutageClosure.sgVote_round,
      ← NamedOutageClosure.sgVote_confirmed]
  rw [hsplit, hval, hround, hconf]
  rfl


/-- One delay after `S.a r` is at most the earliest grade cutoff of round `r + 1`. -/
theorem action_add_delta_le_next_Γ_neg1
    (S : Setup V) (r : Round) :
    S.a r + S.E.Δ ≤ S.hc.Γ_neg1 S.E.Δ (r + 1) := by
  have hR : (2 : Time) ≤ (S.hc.R : Nat) := by
    exact_mod_cast S.hc.R_ge_two
  change S.hc.a S.E.Δ r + S.E.Δ ≤ S.hc.Γ_neg1 S.E.Δ (r + 1)
  unfold Protocol.HealConfig.a Protocol.HealConfig.Γ_neg1
    Protocol.HealConfig.opening_slot slotStart
  push_cast
  have hfour : (8 : Time) ≤ 4 * (S.hc.R : Time) := by
    have hm := Int.mul_le_mul_of_nonneg_left hR (by norm_num : (0 : Time) ≤ 4)
    norm_num at hm ⊢
    exact hm
  have hfactor : (0 : Time) ≤ 4 * (S.hc.R : Time) - 8 :=
    sub_nonneg.mpr hfour
  have hprod : (0 : Time) ≤ S.E.Δ * (4 * (S.hc.R : Time) - 8) :=
    Int.mul_nonneg (le_of_lt S.E.Δ_pos) hfactor
  calc
    4 * S.E.Δ * (r * S.hc.R) + 6 * S.E.Δ + S.E.Δ =
        4 * S.E.Δ * (r * S.hc.R) + 7 * S.E.Δ := by ring
    _ ≤ 4 * S.E.Δ * (r * S.hc.R) + 7 * S.E.Δ +
        S.E.Δ * (4 * S.hc.R - 8) := Int.le_add_of_nonneg_right hprod
    _ = 4 * S.E.Δ * ((r + 1) * S.hc.R) - S.E.Δ := by ring


/-- The node state of `v` read at the round-`r` G2 domain time. -/
def relativeG2Read (S : Setup V) (rho : Run V) (r : Round) (v : V) :
    NamedNodeState V :=
  readAt S rho (domain S.E S.hc r .g2) v


namespace GradeDeliveryRun


end GradeDeliveryRun

/-! ## The round-action SG block is in the store -/

/-- The action store of `v` in round `r` satisfies the confirmation-membership invariant. -/
theorem actionRead_invariant (S : Setup V) (rho : Run V) (v : V) (r : Round) :
    Proofs.NamedConfirmationMembership.Invariant S.E S.cfg (actionStoreAt S rho v r).st := by
  apply Proofs.ModelProperties.invariant_update_gradeContract
  rw [Proofs.ModelProperties.confirmationReadFrom_st]
  exact Proofs.NamedConfirmationMembership.invariant_clock S.E S.cfg _ (S.a r)
    (Proofs.NamedRuntime.stateBeforeTime_invariants S rho (S.a r) v).1


/-- The SG block `v` chooses at round `r`'s action is a processed block of its action store. -/
theorem actionSGBlockAt_mem_actionStore
    (S : Setup V) (rho : Run V) (v : V) (r : Round) :
    actionSGBlockAt S rho v r ∈ (actionStoreAt S rho v r).T := by
  set n := actionReadAt S rho v r with hn
  set st := n.st.core.toHealing with hst
  set grades := (NamedProfile.gradeContract n.cache).read S.E S.hc st r with hgr
  have hk : S.hc.round_of st.s = r := by
    rw [hst, Proofs.ModelProperties.toHealing_s]
    exact actionStoreAt_round S rho v r
  have heq : actionSGBlockAt S rho v r = Protocol.currentSGVote st grades := by
    show Protocol.get_sg_vote_with (NamedProfile.gradeContract n.cache) S.E S.hc st
        (S.hc.round_of st.s)
        (Protocol.grade2_block_with (NamedProfile.gradeContract n.cache) S.E S.hc st
          (S.hc.round_of st.s)) = Protocol.currentSGVote st grades
    rw [hk]
    exact Proofs.ModelProperties.get_sg_vote_with_gradeContract_grade2 n.cache S.E S.hc st r
  have hinv : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg n.st :=
    actionRead_invariant S rho v r
  have hpc : ParentClosed n.st.core := by
    have h := Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho (S.a r) v
    have hT : n.st.core.T = (rho.stateBeforeTime S (S.a r) v).st.core.T := by
      show (Protocol.NamedDuties.update_confirmation_with _ S.E S.hc
        (NamedActionReads.confirmationReadFrom S _ (S.a r)).st _).core.T = _
      rw [Proofs.ModelProperties.named_update_confirmation_with_core,
        Proofs.ModelProperties.update_confirmation_with_T,
        Proofs.ModelProperties.confirmationReadFrom_st,
        Proofs.ModelProperties.setClock_core_T]
    rw [parentClosed_iff] at h ⊢
    rw [hT]
    exact h
  have hlc : st.live_confirmed ∈ n.st.core.T := by
    rw [hst, Proofs.ModelProperties.toHealing_live_confirmed]
    exact hinv.2.1
  have hroot : Protocol.get_fg_root st.toFG ∈ n.st.core.T :=
    Proofs.NamedStoreRoots.fg_root_mem n.st hinv.1.2
  have hanchor : grades.anchor ∈ n.st.core.T := by
    rw [hgr, Proofs.ModelProperties.gradeContract_read_anchor,
      ← Proofs.ModelProperties.toHealing_T]
    exact Proofs.NamedProposalParent.frame_anchor_mem S.E S.hc _ _ _
      (by rw [Proofs.ModelProperties.toHealing_T]; exact hroot)
  have hgoal : (actionStoreAt S rho v r).T = n.st.core.T := rfl
  rw [hgoal, heq]
  cases hdc : Protocol.deepest_clear (some grades.anchor) st.live_confirmed
      grades.clear with
  | some B =>
      rw [Proofs.ModelProperties.currentSGVote_of_deepest_clear hdc]
      exact Proofs.Records.mem_of_preceq ((parentClosed_iff n.st.core).mp hpc).2 B
        st.live_confirmed hlc (Proofs.Engine.deepest_clear_preceq hdc)
  | none =>
      cases hQ : grades.Q2 with
      | some Q =>
          rw [Proofs.ModelProperties.currentSGVote_of_Q2 hdc hQ]
          exact mem_T_of_mem_filteredTree (actionQ2_mem_filteredTree S rho v r hQ)
      | none =>
          by_cases hraw : grades.rawG2
          · rw [Proofs.ModelProperties.currentSGVote_of_rawG2 hdc hQ hraw]
            exact hroot
          · rw [Proofs.ModelProperties.currentSGVote_of_not_rawG2 hdc hQ hraw]
            exact hanchor

/-- The SG block `v` chooses at round `r`'s action is already in its store before time `S.a r`. -/
theorem actionSGBlockAt_mem_storeBeforeTime
    (S : Setup V) (rho : Run V) (v : V) (r : Round) :
    actionSGBlockAt S rho v r ∈
      (rho.storeBeforeTime S v (S.a r)).T :=
  by
    have hT : (actionStoreAt S rho v r).T = (rho.storeBeforeTime S v (S.a r)).T := by
      show (Protocol.NamedDuties.update_confirmation_with _ S.E S.hc
        (NamedActionReads.confirmationReadFrom S _ (S.a r)).st _).core.T = _
      rw [Proofs.ModelProperties.named_update_confirmation_with_core,
        Proofs.ModelProperties.update_confirmation_with_T,
        Proofs.ModelProperties.confirmationReadFrom_st,
        Proofs.ModelProperties.setClock_core_T]
      rfl
    rw [← hT]
    exact actionSGBlockAt_mem_actionStore S rho v r


end HealingSurface

open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Protocol (HealConfig)
open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- `Σ.F` is in the viable tree of the store. -/
def FinalizedViable (st : Protocol.Store V) : Prop :=
  st.F ∈ Protocol.V_tree st.toHealing.toFG

omit [Fintype V] in
/-- `FinalizedViable`, unfolded: it reads only the fields `T`, `σ`, `F` and `h_max`. -/
theorem finalizedViable_iff (st : Protocol.Store V) :
    FinalizedViable st ↔
      st.F ∈ st.T ∧ ∃ W ∈ st.T, Block.preceq st.F W = true ∧
        st.h_max - 1 ≤ (st.σ W).h := by
  simp only [FinalizedViable, Protocol.V_tree, Protocol.viable_tree,
    Protocol.finalized_descendants, Protocol.viable, Finset.mem_filter,
    decide_eq_true_eq, Protocol.Store.toHealing]
  constructor
  · rintro ⟨⟨hT, -⟩, W, hW, hFW, hh⟩
    exact ⟨hT, W, hW, hFW, hh⟩
  · rintro ⟨hT, W, hW, hFW, hh⟩
    exact ⟨⟨hT, Block.preceq_self _⟩, W, hW, hFW, hh⟩

omit [Fintype V] in
/-- `FinalizedViable` carries over between stores that agree on `T`, `σ`, `F` and `h_max`. -/
theorem finalizedViable_of_eq {st st' : Protocol.Store V} (hT : st'.T = st.T)
    (hσ : st'.σ = st.σ) (hF : st'.F = st.F) (hmax : st'.h_max = st.h_max)
    (h : FinalizedViable st) : FinalizedViable st' := by
  rw [finalizedViable_iff, hT, hσ, hF, hmax]
  exact (finalizedViable_iff st).mp h

omit [Fintype V] in
/-- `update_finality` keeps `Σ.F` viable, given a processed block `B` with `Σ.F ⪯ B` whose chain
    state is `σ`. -/
theorem finalizedViable_update_finality (st : Protocol.Store V) (σ : ChainState V)
    {B : Block V} (hB : B ∈ st.T) (hσB : st.σ B = σ)
    (hFB : Block.preceq st.F B = true)
    (h : FinalizedViable st) :
    FinalizedViable (Protocol.update_finality st σ) := by
  obtain ⟨hFT, W, hW, hFW, hh⟩ := (finalizedViable_iff st).mp h
  rw [finalizedViable_iff]
  have hwit : ∃ W' ∈ st.T, Block.preceq st.F W' = true ∧
      max st.h_max σ.h - 1 ≤ (st.σ W').h := by
    have hstep1 : ∀ a b x : Nat, a - 1 ≤ x → b - 1 ≤ x → max a b - 1 ≤ x := by
      intro a b x h1 h2
      omega
    have hstep2 : ∀ a b c : Nat, a ≤ b → b - 1 ≤ c → a - 1 ≤ c := by
      intro a b c h1 h2
      omega
    have hBh : (st.σ B).h = σ.h := by rw [hσB]
    rcases Nat.le_total σ.h st.h_max with hle | hle
    · exact ⟨W, hW, hFW, hstep1 _ _ _ hh (hstep2 _ _ _ hle hh)⟩
    · refine ⟨B, hB, hFB, hstep1 _ _ _ ?_ ?_⟩
      · rw [hBh]
        exact hstep2 _ _ _ hle (Nat.sub_le _ _)
      · rw [hBh]
        exact Nat.sub_le _ _
  simp only [Protocol.update_finality]
  split_ifs with h₁ h₂ h₃
  ·
    simp only [Bool.and_eq_true, decide_eq_true_eq, Protocol.viable_tree,
      Protocol.finalized_descendants, Protocol.viable, Finset.mem_filter,
      decide_eq_true_eq] at h₂
    exact ⟨h₂.2.1.1, h₂.2.2⟩
  · exact ⟨hFT, hwit⟩
  · simp only [Bool.and_eq_true, decide_eq_true_eq, Protocol.viable_tree,
      Protocol.finalized_descendants, Protocol.viable, Finset.mem_filter,
      decide_eq_true_eq] at h₃
    exact ⟨h₃.2.1.1, h₃.2.2⟩
  · exact ⟨hFT, hwit⟩


namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Protocol (HealConfig)
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]


/-! ## The FG root at the action store -/

/-- The action store of `v` in round `r` and its store before time `S.a r` have the same FG root. -/
theorem actionStoreAt_fgRoot_eq_storeBeforeTime
    (S : Setup V) (rho : Run V) (v : V) (r : Round) :
    Protocol.get_fg_root
        (actionStoreAt S rho v r).toHealing.toFG =
      Protocol.get_fg_root
        (rho.storeBeforeTime S v (S.a r)).toHealing.toFG := by
  show Protocol.get_fg_root (Protocol.NamedDuties.update_confirmation_with _ S.E S.hc
      (NamedActionReads.confirmationReadFrom S
        (NamedRun.stateBeforeTime S rho (S.a r) v) (S.a r)).st _).core.toHealing.toFG = _
  rw [Proofs.ModelProperties.named_update_confirmation_with_core,
    Proofs.ModelProperties.update_confirmation_with_toHealing_fg_root,
    Proofs.ModelProperties.confirmationReadFrom_st_core]
  exact Proofs.ModelProperties.get_fg_root_toHealing_clock _ _ _


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
