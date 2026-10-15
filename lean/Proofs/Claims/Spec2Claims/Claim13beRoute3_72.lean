import Proofs.Claims.Spec2Claims.Claim13beRoute3_71
import Proofs.Claims.Spec2Claims.Claim13bKit
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedHeightPair_erase

/-!
# The highest honest height row and the deadline round

The highest height an honest validator has voted by a given step, the deadline round
`deadlineRoundW`, and the round and height-pair facts used at the switch round.
-/

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

section AtRn

open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- Some validator `v`, honest through the instant of some step `n' ≤ n₀ + 1`, has in the sent log
    `x[n'].sent` an attestation signed by itself whose height pair is a vote at height `h`. -/
def HonestRowAt (S : Setup V) (Sched : Schedule V) (x : AtomicExec (protocol S) Sched)
    (n₀ : Nat) (h : Height) : Prop :=
  ∃ (v : V) (n' : Nat) (a : NamedAttestation V) (entry : BlockId) (tmo : Bool),
    n' ≤ n₀ + 1 ∧ HonestThrough Sched x n' v ∧ a.val_index = v ∧
      (⟨v, NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n'].sent ∧
      a.height_pair = NamedHeightPair.vote h entry tmo

open Classical in
/-- The largest height `h` with `HonestRowAt S Sched x n₀ h`, searched up to the largest `Σ.h_max`
    any validator holds after `n₀ + 1` steps; `0` when there is none. -/
noncomputable def topHonestRow (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (protocol S) Sched) (n₀ : Nat) : Height :=
  Nat.findGreatest (HonestRowAt S Sched x n₀)
    ((Finset.univ : Finset V).sup fun w : V => (x[n₀ + 1][w].st).st.core.h_max)

/-- `progressLag' gap (Setup.alwaysAwake S).extraRounds = 7 · gap + 22 + 4 · S.extraRounds`. -/
theorem progressLag_alwaysAwake_eq_l72 (S : Setup V) (gap : Nat) :
    Proofs.HealingSurface.progressLag' gap (Setup.alwaysAwake S).extraRounds
      = 7 * gap + 22 + 4 * S.extraRounds := by
  unfold Proofs.HealingSurface.progressLag' Proofs.HealingSurface.seedLag
  show 4 * gap + 12 + 2 * S.extraRounds + 3 * gap + 10 + 2 * S.extraRounds = _
  ring

/-- `r + η + 1 + (1 + A) + 2L + 2 = r + 1 + 1 + (1 + A) + 2L + 1 + η`. -/
theorem deadline_slack_nat_l72 (r A L η : Nat) :
    r + η + 1 + (1 + A) + 2 * L + 2 = r + 1 + 1 + (1 + A) + 2 * L + 1 + η := by
  omega

/-- The deadline round `roundAt S tGAT + η_SG + 1 + (1 + (D + K + 5) · L)`, with
    `L = progressLag' gap S.extraRounds`. -/
noncomputable def deadlineRoundW (S : Setup V) (tGAT : Int) (gap : Nat) : Round :=
  roundAt S tGAT + S.hc.η_SG + 1 +
    (1 + (S.cfg.D + S.cfg.K + 5) * Proofs.HealingSurface.progressLag' gap S.extraRounds)

/-- The erasure of `vote h entry tmo` has height `h`, whatever the timeout flag. -/
theorem height?_erase_vote_l72 (h : Height) (entry : BlockId) (tmo : Bool) :
    (NamedHeightPair.vote h entry tmo).erase.height? = some h :=
  DecoupledConsensusModel.Sts.namedHeightPair_erase_vote_height? h entry tmo

/-- If the erasure of `hp` has height `h`, then `hp` is a vote at height `h` with some entry and
    some timeout flag. -/
theorem heightPair_vote_of_height_l72 {hp : NamedHeightPair} {h : Height}
    (he : hp.erase.height? = some h) :
    ∃ entry tmo, hp = .vote h entry tmo := by
  cases hp with
  | empty =>
    rw [DecoupledConsensusModel.Sts.namedHeightPair_erase_empty] at he
    simp [HeightPair.height?] at he
  | vote h' entry tmo =>
    have hEq : h' = h := by
      rw [DecoupledConsensusModel.Sts.namedHeightPair_erase_vote_height?] at he
      exact Option.some.inj he
    exact ⟨entry, tmo, by rw [hEq]⟩

/-- If `b + 1 ≤ t`, then `b + (t − (b + 1)) + 1 = t`. -/
theorem add_sub_succ_l72 (b t : Nat) (h : b + 1 ≤ t) : b + (t - (b + 1)) + 1 = t := by
  omega

end AtRn

end DecoupledConsensusModel.Sts
