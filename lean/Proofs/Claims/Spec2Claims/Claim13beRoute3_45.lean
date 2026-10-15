import Proofs.Claims.Spec2Claims.Claim13beRoute3_44
import Proofs.Vocabulary.Protocol.ForkChoice.Views.VoteSetValidityCore
import Proofs.Claims.Spec2Claims.Claim13bModel_HasSlashableWeightBetween
import Proofs.Claims.Spec2Claims.Claim13bModel_SlashableBetween
import Proofs.Claims.Spec2Claims.Claim13bModel_Prec
import Proofs.Claims.Spec2Claims.Claim13bModel_RootInjectiveBelow
import Proofs.Claims.Spec2Claims.Claim13bModel_matchesEntry
import Proofs.Claims.Spec2Claims.Claim13bModel_beforeCutoff
import Proofs.Claims.Spec2Claims.Claim13bModel_Store_tau
import Proofs.Claims.Spec2Claims.Claim13bModel_Env_W
import Proofs.Claims.Spec2Claims.Claim13bModel_weightOf
import Proofs.Claims.Spec2Claims.Claim13bModel_propose_block_with_inclG2
import Proofs.Claims.Spec2Claims.Claim13bModel_get_filtered_block_tree_inclG5
import Proofs.Claims.Spec2Claims.Claim13bModel_get_fg_root
import Proofs.Claims.Spec2Claims.Claim13bModel_actionStoreAt
import Proofs.Claims.Spec2Claims.Claim13bModel_round_votes
import Proofs.Claims.Spec2Claims.Claim13bModel_on_sg_vote
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedReceiptCalls_postCore
import Proofs.Claims.Spec2Claims.Claim13bModel_update_confirmation_with
import Proofs.Claims.Spec2Claims.Claim13bModel_occurrenceBefore
import Proofs.Claims.Spec2Claims.Claim13bModel_late

/-!
# Per-instant forms of run and store lemmas

Lemmas over a run with its honest set replaced by the family `Hs : Int → Finset V`, run blocks read
through `Xb`, and the run's premises given by the bundle `AdmissibleFieldsOn`.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Proofs.HealingLemmas
open DecoupledConsensusModel.Internal.NamedRecoveryRead

variable {V : Type} [DecidableEq V] [Fintype V]

/-- If `v ∈ Xb` holds `C` after the first `i` events, `C` is a run block read through `Xb`. -/
theorem runBlock_of_stateBefore_memOn (S : Setup V) {ρ : Run V} (Xb : Finset V) {v : V}
    (hv : v ∈ Xb) {i : Nat} {C : NamedBlock V}
    (hC : C ∈ (ρ.stateBefore S i v).st.bodies) : RunBlockOn S ρ Xb C :=
  ⟨C, Or.inr ⟨v, hv, i, hC⟩, Proofs.NamedAncestry.named_self C⟩

/-- The state before time `t` is the state after some prefix of the events, every one of them
    strictly before `t`. -/
theorem stateBeforeTime_eq_stateBeforeOn (S : Setup V) {ρ : Run V} (Hs : Int → Finset V)
    (Xb : Finset V) {lo : Int}
    (hf : AdmissibleFieldsOn S ρ Hs Xb lo) (t : Time) :
    ∃ n : Nat, ρ.stateBeforeTime S t = ρ.stateBefore S n ∧
      ∀ (j : Nat) (e : Event V), j < n → ρ.events[j]? = some e → e.time < t :=
  (Proofs.Bridges.filtered_fold_eq_stateBefore_of_sorted S hf.sorted
    (p := fun e => decide (e.time < t))
    (fun e f hk hfnd => by
      simp only [decide_eq_true_eq] at hfnd ⊢
      exact lt_of_le_of_lt (Proofs.Bridges.time_le_of_key_le hk) hfnd)).imp fun _ h =>
    ⟨h.1, fun j e hj hget => by simpa using h.2 j e hj hget⟩

/-- If `B` is in the run read through `Xb` and `A ⪯ B`, then `A` is in the run read through `Xb`. -/
theorem blockInRun_of_ancestorOn (S : Setup V) (rho : NamedRun V) (Xb : Finset V)
    {A B : NamedBlock V}
    (hB : blockInRunOn S rho Xb B) (hAB : NamedBlock.Preceq A B) :
    blockInRunOn S rho Xb A := by
  obtain ⟨C, hC, hBC⟩ := hB
  exact ⟨C, hC, (priv% Proofs.Vocabulary.Execution.Runtime
    DecoupledConsensusModel.Proofs.NamedRuntime.named_preceq_trans) hAB hBC⟩

/-- Under the slashable bound and root-collision freedom through `Xb`, for run blocks `C` and `D`
    read through `Xb`, if `D`'s finalized height is less than `C`'s height then `D`'s finalized
    block is an ancestor of `C`. -/
theorem finalized_preceq_of_height_ltOn
    (S : Setup V) (rho : NamedRun V) (Xb : Finset V) (C D : NamedBlock V)
    (hsb : SlashableBoundOn S rho Xb)
    (hroot : RootCollisionFreeOn S rho Xb)
    (hC : blockInRunOn S rho Xb C) (hD : blockInRunOn S rho Xb D)
    (hlt : (derive_named S.E S.cfg D).h_F < (derive_named S.E S.cfg C).h) :
    Block.Preceq (derive_named S.E S.cfg D).F C.erase := by
  by_cases hz : (derive_named S.E S.cfg D).h_F = 0
  · rw [NamedFinalityCertificates.finalized_zero_is_genesis S.E S.cfg D hz]
    exact (preceq_eq_true_iff_Preceq.mp (Protocol.preceq_genesis C.erase))
  · obtain ⟨F, hFD, hFE, Qf, hQf, hwf⟩ :=
      NamedFinalityCertificates.finality_certificate S.E S.cfg D hz
    obtain ⟨X, hXC, _hXheight, Qc, hQc, hwc⟩ :=
      NamedFinalityCertificates.height_crossing S.E S.cfg C
        (derive_named S.E S.cfg D).h_F (Nat.one_le_iff_ne_zero.mpr hz) hlt
    by_cases hroots : X.root = F.root
    · have hXF : X = F :=
        hroot.root_injective C D hC hD X F (Or.inl hXC) (Or.inr hFD) hroots
      rw [← hFE, ← hXF]
      exact Proofs.NamedWire.erase_preceq hXC
    · exfalso
      apply hsb C D hC hD
      refine hasSlashableWeightBetween_intro (Qc ∩ Qf) (quorum_intersection S.E hQc hQf) ?_
      intro signer hsigner
      obtain ⟨hc, hf⟩ := Finset.mem_inter.mp hsigner
      obtain ⟨carrierA, a, hcarrierA, ha, hav, hamatch⟩ := hwc signer hc
      obtain ⟨carrierB, b, hcarrierB, hb, hbv, hbfinal⟩ := hwf signer hf
      refine slashableBetween_intro a.erase
        ((priv% Proofs.Vocabulary.Protocol.ChainState.FinalityComparison
          DecoupledConsensusModel.Proofs.NamedFinalizationBridge.on_chain_erase_mem) hcarrierA ha)
        b.erase ((priv% Proofs.Vocabulary.Protocol.ChainState.FinalityComparison
          DecoupledConsensusModel.Proofs.NamedFinalizationBridge.on_chain_erase_mem) hcarrierB hb) ?_ ?_ ?_
      · rw [namedAttestation_erase_val_index]; exact hav
      · rw [namedAttestation_erase_val_index]; exact hbv
      · exact (priv% Proofs.Vocabulary.Protocol.ChainState.FinalityComparison
          DecoupledConsensusModel.Proofs.NamedFinalizationBridge.matching_finality_e1) a b
          (derive_named S.E S.cfg D).h_F X.root F.root
          (hav.trans hbv.symm) hamatch hbfinal hroots

section RawRelay

open DecoupledConsensusModel.Internal.NamedOutageEntry
open DecoupledConsensusModel.Internal.NamedStableChainOutage
open DecoupledConsensusModel.Proofs.NamedRawRelay

local macro "rr% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Vocabulary.Protocol.Handlers.RawRelay)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.NamedRawRelay ++ n.getId)))

end RawRelay

section HealthyLateRelay

open DecoupledConsensusModel.Internal.NamedOutageEntry
open DecoupledConsensusModel.Proofs.NamedRawRelay
open DecoupledConsensusModel.Proofs.NamedHealthyLateRelay

local macro "hl% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Vocabulary.Protocol.Handlers.HealthyLateRelay)
    $(Lean.mkIdent (`DecoupledConsensusModel.Proofs.NamedHealthyLateRelay ++ n.getId)))

end HealthyLateRelay

end DecoupledConsensusModel.Sts
