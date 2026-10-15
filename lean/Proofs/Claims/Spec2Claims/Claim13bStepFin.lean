import Proofs.Claims.Spec2Claims.Claim13bStepSGMove
import Proofs.Vocabulary.Protocol.Grades.JointHistoryGaps
import Proofs.Claims.Spec2Claims.Claim13bModel_readFrame_attest
import Proofs.Claims.Spec2Claims.Claim13bModel_readFrame_cs
import Proofs.Claims.Spec2Claims.Claim13bModel_onPhaseTick_mk_s2
import Proofs.Claims.Spec2Claims.Claim13bModel_domain_attest
import Proofs.Claims.Spec2Claims.Claim13bModel_domain
import Proofs.Claims.Spec2Claims.Claim13bModel_grade2Block
import Proofs.Claims.Spec2Claims.Claim13bModel_frameGradeRead_attest
import Proofs.Claims.Spec2Claims.Claim13bModel_Preceq
import Proofs.Claims.Spec2Claims.Claim13bModel_Env_q

/-!
# The finalization quorum on a chain

A chain finalized at a non-zero height includes, on itself, a quorum of height votes for that
height's entry block.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- If the replay of `D` finalizes at a non-zero height `h_F`, then two ancestors of `D` have
    chain-state height `h_F`: the finalized block `Fn`, which its own replay names as that height's
    entry, and a block `X`; and some quorum `Q` has, for each member, an attestation under that
    member's name, included in an ancestor of `D`, whose height pair is a vote for height `h_F`
    naming `X.root`. -/
theorem finalized_entry_quorum (E : Env V) (cfg : Protocol.HeightConfig) (D : NamedBlock V)
    (hnz : (Protocol.derive_named E cfg D).h_F ≠ 0) :
    ∃ Fn X : NamedBlock V, NamedBlock.Preceq Fn D ∧ NamedBlock.Preceq X D ∧
      Fn.erase = (Protocol.derive_named E cfg D).F ∧
      (Protocol.derive_named E cfg Fn).h = (Protocol.derive_named E cfg D).h_F ∧
      (Protocol.derive_named E cfg Fn).T_h = Fn.erase ∧
      (Protocol.derive_named E cfg X).h = (Protocol.derive_named E cfg D).h_F ∧
      ∃ Q : Finset V, E.electorate.IsQuorum Q ∧ ∀ signer ∈ Q,
        ∃ (carrier : NamedBlock V) (a : NamedAttestation V) (tmo : Bool),
          NamedBlock.Preceq carrier D ∧ a ∈ carrier.attestations ∧ a.val_index = signer ∧
          a.height_pair
            = NamedHeightPair.vote (Protocol.derive_named E cfg D).h_F X.root tmo := by
  classical
  obtain ⟨Fn, hFnD, hFnerase, hFnh, hFnentry⟩ :=
    (finalized_is_entry E cfg D).resolve_left hnz
  have hpos : 1 ≤ (Protocol.derive_named E cfg D).h_F := Nat.one_le_iff_ne_zero.mpr hnz
  have hlt : (Protocol.derive_named E cfg D).h_F < (Protocol.derive_named E cfg D).h :=
    (Proofs.NamedDerivationGeometry.chainOrder_derive_named E cfg D).finalized_below_height
  obtain ⟨X, hXD, hXh, Q, hQ, hw⟩ :=
    Proofs.NamedFinalityCertificates.height_crossing E cfg D
      (Protocol.derive_named E cfg D).h_F hpos hlt
  refine ⟨Fn, X, hFnD, hXD, hFnerase, hFnh, hFnentry, hXh, Q, hQ, ?_⟩
  intro signer hsigner
  obtain ⟨carrier, a, hcarrier, ha, hval, hmatch⟩ := hw signer hsigner
  obtain ⟨tmo, htmo⟩ := vote_of_matchesEntry hmatch
  exact ⟨carrier, a, tmo, hcarrier, ha, hval, htmo⟩

end DecoupledConsensusModel.Sts
