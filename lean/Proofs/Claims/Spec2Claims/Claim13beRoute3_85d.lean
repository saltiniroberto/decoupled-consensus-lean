import Proofs.Claims.Spec2Claims.Claim13bInvariantActiveSinceW
import Proofs.Claims.Spec2Claims.Claim13beRoute3_78
import Proofs.Claims.Spec2Claims.Claim13beRoute3_85
import Proofs.Claims.Spec2Claims.Claim13beRoute3_86f
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedBlock_parent
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedBlock_erase
import Proofs.Claims.Spec2Claims.Claim13bModel_opening_slot
import Proofs.Claims.Spec2Claims.Claim13bModel_opening
import Proofs.Claims.Spec2Claims.Claim13bModel_get_filtered_block_tree
import Proofs.Claims.Spec2Claims.Claim13bModel_confirmationReadFrom
import Proofs.Claims.Spec2Claims.Claim13bModel_setClock_incl
import Proofs.Claims.Spec2Claims.Claim13bModel_support_cutoff
import Proofs.Claims.Spec2Claims.Claim13bModel_Preceq
import Proofs.Claims.Spec2Claims.Claim13bModel_proposal_time_inclG1
import Proofs.Claims.Spec2Claims.Claim13bModel_get_fg_root
import Proofs.Claims.Spec2Claims.Claim13bModel_toHealing
import Proofs.Claims.Spec2Claims.Claim13bModel_readFrame_attest
import Proofs.Claims.Spec2Claims.Claim13bModel_freezeRoot
import Proofs.Claims.Spec2Claims.Claim13bModel_gradeView
import Proofs.Claims.Spec2Claims.Claim13bModel_rawInputs
import Proofs.Claims.Spec2Claims.Claim13bModel_interpretedInputs
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedDuties_update_confirmation_with
import Proofs.Claims.Spec2Claims.Claim13bModel_a_mk_s4
import Proofs.Claims.Spec2Claims.Claim13bModel_vote_time
import Proofs.Claims.Spec2Claims.Claim13bModel_confirmation_time
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedBlock_Preceq
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedBlock_slot

/-!
# Window round arithmetic and the window's justification

Round inequalities over `Nat` for two windows of rounds, the first step up from a block's height
along a chain, and the justification a window's third proposal carries over chain states. `h(B)` is
the chain-state height `(Protocol.derive_named E cfg B).h` and `h_j(B)` its justified height.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation

variable {V : Type} [DecidableEq V] [Fintype V]

section Windows

open Framework.StsMultisetLog

/-- If `rD + 2L + 2 = cb`, `cb + g ≤ w` and `L = 7g + 22 + 4e`, then `rD ≤ w`, `rD ≤ rD + g + 1 + 1`
    and `rD + g + 1 + 1 + g ≤ w`. -/
theorem windows_pre_nat_l85d (rD L cb g w e : Nat) (hs : rD + 2 * L + 2 = cb) (hη : cb + g ≤ w)
    (hL : L = 7 * g + 22 + 4 * e) :
    rD ≤ w ∧ rD ≤ rD + g + 1 + 1 ∧ rD + g + 1 + 1 + g ≤ w := by
  subst hL; omega

/-- If `rD + 2L + 2 = cb`, `cb + g ≤ w`, `L = 7g + 22 + 4e`, `e = m − 2`, `2 ≤ m` and
    `rD + g + 1 + 1 + 2 ≤ c₁ ≤ rD + g + 1 + 1 + g`, then `rD ≤ c₁ + m − 2` and `c₁ + m − 2 + g ≤ w`. -/
theorem windows_mid_nat_l85d (rD L cb g w e m c₁ : Nat) (hs : rD + 2 * L + 2 = cb)
    (hη : cb + g ≤ w) (hL : L = 7 * g + 22 + 4 * e) (he : e = m - 2) (hm : 2 ≤ m)
    (h1lo : rD + g + 1 + 1 + 2 ≤ c₁) (h1hi : c₁ ≤ rD + g + 1 + 1 + g) :
    rD ≤ c₁ + m - 2 ∧ c₁ + m - 2 + g ≤ w := by
  subst hL he; omega

/-- If `rD + 2L + 2 = cb`, `cb + g ≤ w`, `L = 7g + 22 + 4e`, `e = m − 2`, `2 ≤ m`,
    `rD + g + 1 + 1 + 2 ≤ c₁ ≤ rD + g + 1 + 1 + g` and `c₁ + m − 2 + 2 ≤ c₂ ≤ c₁ + m − 2 + g`, then
    `rD + g + 1 + 3 ≤ c₁`, `c₁ + m ≤ c₂`, `c₂ ≤ c₁ + m + g` and `c₂ + 1 ≤ w`. -/
theorem windows_all_nat_l85d (rD L cb g w e m c₁ c₂ : Nat) (hs : rD + 2 * L + 2 = cb)
    (hη : cb + g ≤ w) (hL : L = 7 * g + 22 + 4 * e) (he : e = m - 2) (hm : 2 ≤ m)
    (h1lo : rD + g + 1 + 1 + 2 ≤ c₁) (h1hi : c₁ ≤ rD + g + 1 + 1 + g)
    (h2lo : c₁ + m - 2 + 2 ≤ c₂) (h2hi : c₂ ≤ c₁ + m - 2 + g) :
    rD + g + 1 + 3 ≤ c₁ ∧ c₁ + m ≤ c₂ ∧ c₂ ≤ c₁ + m + g ∧ c₂ + 1 ≤ w := by
  subst hL he; omega

end Windows

section ChainGeneral

variable (E : Env V) (cfg : Protocol.HeightConfig)

/-- If `A ⪯ Z` and `h(A) < h(Z)`, some block `node p …` with `A ⪯ p` and `node p … ⪯ Z` has
    `h(p) = h(A)` and `h(node p …) = h(A) + 1`. -/
theorem exists_step_up_l85d {A Z : NamedBlock V} (hAZ : NamedBlock.Preceq A Z)
    (hlt : (Protocol.derive_named E cfg A).h < (Protocol.derive_named E cfg Z).h) :
    ∃ (p : NamedBlock V) (s : Slot) (root : BlockId) (votes support : List (GoldfishVote V))
      (rows : List (NamedAttestation V)) (proposer : V),
      NamedBlock.Preceq A p ∧
      NamedBlock.Preceq (.node p s root votes support rows proposer) Z ∧
      (Protocol.derive_named E cfg p).h = (Protocol.derive_named E cfg A).h ∧
      (Protocol.derive_named E cfg (.node p s root votes support rows proposer)).h =
        (Protocol.derive_named E cfg A).h + 1 := by
  induction Z with
  | genesis =>
    rw [namedPreceq_genesis_iff_l85] at hAZ
    subst hAZ
    exact absurd hlt (lt_irrefl _)
  | node p s root votes support rows proposer ih =>
    rcases namedPreceq_node_iff_l85.mp hAZ with heq | hAp
    · rw [heq] at hlt; exact absurd hlt (lt_irrefl _)
    · have hpZ : NamedBlock.Preceq p (.node p s root votes support rows proposer) :=
        namedBlock_Preceq_parent_node p s root votes support rows proposer
      have hAph := Proofs.NamedEntryHeight.derive_height_mono E cfg hAp
      by_cases hlt' : (Protocol.derive_named E cfg A).h < (Protocol.derive_named E cfg p).h
      · obtain ⟨p', s', root', votes', support', rows', proposer', h1, h2, h3, h4⟩ := ih hAp hlt'
        exact ⟨p', s', root', votes', support', rows', proposer', h1,
          namedPreceq_trans_l85 h2 hpZ, h3, h4⟩
      · have hpA : (Protocol.derive_named E cfg p).h = (Protocol.derive_named E cfg A).h :=
          Nat.le_antisymm (Nat.le_of_not_lt hlt') hAph
        refine ⟨p, s, root, votes, support, rows, proposer, hAp,
          Proofs.NamedAncestry.named_self _, hpA, ?_⟩
        rcases Proofs.NamedEntryHeight.derive_node_height_cases E cfg p s root votes support
            rows proposer with hc | hc
        · change (Protocol.derive_named E cfg (.node p s root votes support rows proposer)).h
            = (Protocol.derive_named E cfg p).h at hc
          rw [hc, hpA] at hlt; exact absurd hlt (lt_irrefl _)
        · change (Protocol.derive_named E cfg (.node p s root votes support rows proposer)).h
            = (Protocol.derive_named E cfg p).h + 1 at hc
          rw [hc, hpA]

/-- If slots increase along `P2`'s chain, `Pc` and `P2` are not genesis, `Pc`'s `nj` bit is clear,
    `Pm ⪯ parent(Pc)`, `Pm` is at slot `om`, `Pc ⪯ parent(P2)`,
    `parent(P2).slot + 1 ≤ om + timeoutDelay`, and the two coverage hypotheses `hcov2` and `hcovc`
    hold, then `h(Pc) ≤ h_j(P2)`. -/
theorem windowJustified_l85d {Pm Pc P2 : NamedBlock V} {om : Slot}
    (hsl : ∀ X : NamedBlock V, NamedBlock.Preceq X P2 → X ≠ .genesis →
      X.parent.slot < X.slot)
    (hPcne : Pc ≠ .genesis) (hP2ne : P2 ≠ .genesis)
    (hnj : (Protocol.derive_named E cfg Pc).nj = false)
    (hPm : NamedBlock.Preceq Pm Pc.parent) (hPmslot : Pm.slot = om)
    (hPcQ : NamedBlock.Preceq Pc P2.parent)
    (hQslot : P2.parent.slot + 1 ≤ om + cfg.timeoutDelay)
    (hcov2 : (Protocol.derive_named E cfg P2.parent).h = (Protocol.derive_named E cfg Pc).h →
      (Protocol.derive_named E cfg P2.parent).T_h = (Protocol.derive_named E cfg Pc).T_h →
      HealingSurface.NamedTargetQuorumCoveredByChild E
        (Protocol.derive_named E cfg P2.parent) P2)
    (hcovc : (Protocol.derive_named E cfg Pm).h = (Protocol.derive_named E cfg Pc).h →
      (Protocol.derive_named E cfg Pc.parent).h = (Protocol.derive_named E cfg Pc).h →
      (Protocol.derive_named E cfg Pc.parent).T_h = (Protocol.derive_named E cfg Pm).T_h →
      HealingSurface.NamedTargetQuorumCoveredByChild E
        (Protocol.derive_named E cfg Pc.parent) Pc) :
    (Protocol.derive_named E cfg Pc).h ≤ (Protocol.derive_named E cfg P2).h_j := by
  have hQ2 : NamedBlock.Preceq P2.parent P2 := parent_namedPreceq_l85 P2
  have hPcP2 : NamedBlock.Preceq Pc P2 := namedPreceq_trans_l85 hPcQ hQ2
  by_cases hQH : (Protocol.derive_named E cfg P2.parent).h = (Protocol.derive_named E cfg Pc).h
  · have hT : (Protocol.derive_named E cfg P2.parent).T_h =
        (Protocol.derive_named E cfg Pc).T_h :=
      (Proofs.NamedEntryHeight.entry_eq_on_plateau E cfg hPcQ hQH.symm).symm
    have hnjQ : (Protocol.derive_named E cfg P2.parent).nj = false := by
      rw [← nj_eq_on_plateau_l85 E cfg hPcQ hQH.symm]; exact hnj
    have hJ := HealingSurface.namedJustifiedAt_of_targetQuorumCoveredByChild E cfg hP2ne
      (hcov2 hQH hT) hnjQ
    rw [hJ.1.2, hQH]
  · have hlt : (Protocol.derive_named E cfg Pc).h < (Protocol.derive_named E cfg P2.parent).h :=
      lt_of_le_of_ne (Proofs.NamedEntryHeight.derive_height_mono E cfg hPcQ) (Ne.symm hQH)
    obtain ⟨p, s, root, votes, support, rows, proposer, hPcp, hXQ, hph, hXh⟩ :=
      exists_step_up_l85d E cfg hPcQ hlt
    have hXP2 : NamedBlock.Preceq (.node p s root votes support rows proposer) P2 :=
      namedPreceq_trans_l85 hXQ hQ2
    have hup : (Protocol.derive_named E cfg (.node p s root votes support rows proposer)).h
        = (Protocol.derive_named E cfg p).h + 1 := by rw [hXh, hph]
    rcases advance_cases_l85 E cfg p s root votes support rows proposer hup with
      hj | hnj' | hmat
    · rw [← hph, ← hj]
      exact HealingSurface.namedJustification_le_of_preceq E cfg hXP2
    · rw [← nj_eq_on_plateau_l85 E cfg hPcp hph.symm, hnj] at hnj'
      exact absurd hnj' Bool.false_ne_true
    · exfalso
      have hTp : (Protocol.derive_named E cfg Pc).T_h = (Protocol.derive_named E cfg p).T_h :=
        Proofs.NamedEntryHeight.entry_eq_on_plateau E cfg hPcp hph.symm
      obtain ⟨E₀, hE₀, -, hE₀h, hE₀s⟩ := entry_named_l85 E cfg Pc
      have hXslot : (NamedBlock.node p s root votes support rows proposer).slot ≤
          P2.parent.slot :=
        (slot_le_of_namedPreceq_l85 hsl hXQ hQ2).1
      have hE₀lt : E₀.slot < om := by
        rw [hE₀s, hTp]
        exact nat_entry_lt_l85 _ _ _ _
          (hmat.trans (by simpa only [named_node_slot] using hXslot)) hQslot
      have hPmPc : NamedBlock.Preceq Pm Pc :=
        namedPreceq_trans_l85 hPm (parent_namedPreceq_l85 Pc)
      rcases namedPreceq_total_l85 hE₀ hPmPc with hE₀Pm | hPmE₀
      · have h1 := Proofs.NamedEntryHeight.derive_height_mono E cfg hE₀Pm
        have h2 := Proofs.NamedEntryHeight.derive_height_mono E cfg hPm
        have h3 := Proofs.NamedEntryHeight.derive_height_mono E cfg (parent_namedPreceq_l85 Pc)
        have hparH : (Protocol.derive_named E cfg Pc.parent).h =
            (Protocol.derive_named E cfg Pc).h :=
          Nat.le_antisymm h3 (hE₀h ▸ h1.trans h2)
        have hPmH : (Protocol.derive_named E cfg Pm).h = (Protocol.derive_named E cfg Pc).h :=
          Nat.le_antisymm (h2.trans h3) (hE₀h ▸ h1)
        have hTpar : (Protocol.derive_named E cfg Pc.parent).T_h =
            (Protocol.derive_named E cfg Pm).T_h :=
          (Proofs.NamedEntryHeight.entry_eq_on_plateau E cfg hPm
            (hPmH.trans hparH.symm)).symm
        have hnjpar : (Protocol.derive_named E cfg Pc.parent).nj = false := by
          rw [nj_eq_on_plateau_l85 E cfg (parent_namedPreceq_l85 Pc) hparH]; exact hnj
        have hJc := HealingSurface.namedJustifiedAt_of_targetQuorumCoveredByChild E cfg
          hPcne (hcovc hPmH hparH hTpar) hnjpar
        have := hJc.2
        rw [hparH] at this
        exact absurd this (Nat.succ_ne_self _).symm
      · have hsl' := (slot_le_of_namedPreceq_l85 hsl hPmE₀
          (namedPreceq_trans_l85 hE₀ hPcP2)).1
        rw [hPmslot] at hsl'
        exact absurd hE₀lt (Nat.not_lt.mpr hsl')

end ChainGeneral

section WindowParent

open Framework.StsMultisetLog
open DecoupledConsensusModel.Internal.PhaseGrades

omit [Fintype V] in
/-- If the erasure of `X` has its parent's slot less than its own, so has `X`. -/
theorem named_parent_slot_lt_of_erase_l85d {X : NamedBlock V}
    (h : X.erase.parent.slot < X.erase.slot) : X.parent.slot < X.slot := by
  rw [Proofs.NamedWire.erase_parent, Proofs.NamedWire.erase_slot,
    Proofs.NamedWire.erase_slot] at h
  exact h

end WindowParent

end DecoupledConsensusModel.Sts
