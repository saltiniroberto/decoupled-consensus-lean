module
public import Proofs.Vocabulary.Protocol.Duties.Inputs.ActionSources
public import Proofs.Vocabulary.Execution.Wire
public import Proofs.Vocabulary.Objects.Weights
public import Proofs.Vocabulary.Internal.Definitions.NamedStableChainOutage
public import Proofs.Vocabulary.ModelProperties.NamedDuties_update_confirmation_with
public import Proofs.Vocabulary.ModelProperties.confirmationReadFrom
public import Proofs.Vocabulary.ModelProperties.NamedNode_tick
public import Proofs.Vocabulary.ModelProperties.NamedDuties_attest_with
public import Proofs.Vocabulary.ModelProperties.round_action_with
public import Proofs.Vocabulary.ModelProperties.with_attestation_input
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

/-!
# Inputs of a round action

The node state an emitted attestation's round action reads, the attestation's stages and head, and
the honest voters of a round.
-/
namespace DecoupledConsensusModel.Proofs.NamedOutageInputs
open Execution Internal.NamedOutageEntry
variable {V : Type} [DecidableEq V] [Fintype V]

omit [DecidableEq V] [Fintype V] in
private theorem no_attest_proposal (p : Prop) [Decidable p]
    (body : Option (NamedBlock V)) (a : NamedAttestation V) :
    NamedObject.attest a ∉ (if p then
      match body with
      | none => []
      | some B => [NamedObject.block B]
    else []) := by
  split_ifs <;> cases body <;> simp

omit [DecidableEq V] [Fintype V] in
private theorem no_attest_vote (p : Prop) [Decidable p]
    (vote : Option (GoldfishVote V)) (a : NamedAttestation V) :
    NamedObject.attest a ∉ (if p then vote.toList.map NamedObject.gfVote else []) := by
  split_ifs <;> cases vote <;> simp

private theorem attestation_suffix_fields (gc : Protocol.GradeContract V) (S : Setup V)
    (v : V) (st : Protocol.NamedStore V) (record : Protocol.NamedRecord)
    (t : Time) (a : NamedAttestation V) (prior : List (NamedObject V))
    (hprefix : NamedObject.attest a ∉ prior)
    (h : NamedObject.attest a ∈ (if t = S.a (S.hc.round_of st.core.s) ∧
        (S.node v).awake (S.hc.round_of st.core.s) = true then
      let out := Protocol.NamedDuties.attest_with gc S.E S.hc (S.node v) st record
      (out.1, out.2.1, prior ++ [NamedObject.attest out.2.2])
    else (st, record, prior)).2.2) :
    t = S.a a.round ∧ (S.node v).awake a.round = true ∧ a.val_index = v := by
  split_ifs at h with hact
  · simp only [List.mem_append, List.mem_singleton, hprefix, false_or,
      NamedObject.attest.injEq] at h
    subst a
    exact ⟨hact.1, hact.2, S.node_val_index v⟩
  · exact False.elim (hprefix h)

/-- An attestation a tick emits at `t` has `t = S.a a.round`, its emitter awake at that round, and
    the emitter as its validator. -/
private theorem tick_attestation_fields (gc : Protocol.GradeContract V) (S : Setup V)
    (v : V) (st : Protocol.NamedStore V) (record : Protocol.NamedRecord)
    (t : Time) (a : NamedAttestation V)
    (h : NamedObject.attest a ∈
      (Protocol.NamedTick.tick gc S.E S.hc S.cfg (S.node v) st record t).2.2) :
    t = S.a a.round ∧ (S.node v).awake a.round = true ∧ a.val_index = v := by
  rw [NamedTick.tick_computed_duties] at h
  dsimp only at h
  apply attestation_suffix_fields gc S v _ record t a _ ?_ h
  simp only [List.mem_append, no_attest_vote, or_false]
  exact no_attest_proposal _ _ a


private theorem action_read_round (S : Setup V) (before : NamedNodeState V) (r : Round) :
    S.hc.round_of (actionReadFrom S before r).st.core.s = r :=
  (NamedActionSources.action_timing S before r).2.2

/-- At the action time of round `r`, a tick emits the attest duty's output on the action read when
    `v` is awake at `r`, and nothing otherwise. -/
private theorem tick_at_action (S : Setup V) (v : V) (before : NamedNodeState V) (r : Round) :
    (Execution.NamedNode.tick S v before (S.a r)).2 =
      let n := actionReadFrom S before r
      let gc := NamedProfile.gradeContract n.cache
      if (S.node v).awake r = true then
        [NamedObject.attest
          (Protocol.NamedDuties.attest_with gc S.E S.hc (S.node v) n.st n.record).2.2]
      else [] :=
  NamedActionSources.tick_at_action S v before r

theorem action_read_invariant (S : Setup V) (rho : NamedRun V)
    (i : Nat) (v : V) (r : Round) :
    Proofs.NamedConfirmationMembership.Invariant S.E S.cfg
      (actionReadFrom S (NamedRun.stateBefore S rho i v) r).st := by
  apply Proofs.ModelProperties.invariant_update_gradeContract
  rw [Proofs.ModelProperties.confirmationReadFrom_st]
  exact Proofs.NamedConfirmationMembership.invariant_clock S.E S.cfg _ (S.a r)
    (Proofs.NamedRuntime.stateBefore_invariants S rho i v).1

theorem emitted_attestation_stages (S : Setup V) (rho : NamedRun V)
    {v : V} {a : NamedAttestation V} {t : Time}
    (hem : NamedRun.emits S rho v (.attest a) t) :
    ∃ i : Nat, rho.events[i]? = some (.tick v t) ∧
      NamedObject.attest a ∈ NamedRun.emittedAt S rho i v t ∧
      let before := NamedRun.stateBefore S rho i v
      let n := actionReadFrom S before a.round
      let gc := NamedProfile.gradeContract n.cache
      (Protocol.NamedDuties.attest_with gc S.E S.hc (S.node v)
        n.st n.record).2.2 = a ∧
      a.val_index = v ∧ a.round = S.hc.round_of n.st.core.s ∧
      t = S.a a.round ∧ (S.node v).awake a.round = true := by
  obtain ⟨i, hi, ho⟩ := hem
  have ho' : NamedObject.attest a ∈
      (Execution.NamedNode.tick S v (NamedRun.stateBefore S rho i v) t).2 := ho
  rw [Proofs.ModelProperties.tick_snd_frameContract] at ho'
  obtain ⟨ht, hawake, hval⟩ := tick_attestation_fields _ S v _ _ t a ho'
  subst t
  have ha := ho
  change NamedObject.attest a ∈
    (Execution.NamedNode.tick S v (NamedRun.stateBefore S rho i v) (S.a a.round)).2 at ha
  rw [tick_at_action] at ha
  simp only [if_pos hawake, List.mem_singleton, NamedObject.attest.injEq] at ha
  exact ⟨i, hi, ho, ha.symm, hval, (action_read_round S _ a.round).symm, rfl, hawake⟩

theorem emitted_attestation_head (S : Setup V) (rho : NamedRun V)
    {v : V} {a : NamedAttestation V} {t : Time}
    (hem : NamedRun.emits S rho v (.attest a) t) :
    ∃ i : Nat, rho.events[i]? = some (.tick v t) ∧
      NamedObject.attest a ∈ NamedRun.emittedAt S rho i v t ∧
      let n := actionReadFrom S (NamedRun.stateBefore S rho i v) a.round
      ∃ H : NamedBlock V, H ∈ n.st.bodies ∧ a.confirmed = some H.root := by
  obtain ⟨i, hi, ho, hrow, _⟩ := emitted_attestation_stages S rho hem
  refine ⟨i, hi, ho, ?_⟩
  let n := actionReadFrom S (NamedRun.stateBefore S rho i v) a.round
  have hinv := action_read_invariant S rho i v a.round
  obtain ⟨B, hB, hhead⟩ := Proofs.ModelProperties.attestation_input_head_gradeContract n.cache
    S.E S.hc S.cfg (S.node v) n.st hinv
  have htree : n.st.core.T = n.st.bodies.image NamedBlock.erase := hinv.1.1.1
  rw [htree] at hB
  obtain ⟨H, hH, rfl⟩ := Finset.mem_image.mp hB
  refine ⟨H, hH, ?_⟩
  have hconfirmed := congrArg NamedAttestation.confirmed hrow
  rw [Proofs.ModelProperties.attest_with_row, Proofs.ModelProperties.round_action_with_confirmed]
    at hconfirmed
  change (Protocol.with_attestation_input (NamedProfile.gradeContract n.cache)
    S.E S.hc (S.node v) n.st.core.toHealing id).confirmed = _ at hhead
  rw [Proofs.ModelProperties.with_attestation_input_id_confirmed] at hhead
  exact hconfirmed.symm.trans (hhead.trans (congrArg some (Proofs.NamedWire.erase_root H)))

theorem emittedInRound_iff (S : Setup V) (rho : NamedRun V) (v : V) (k : Round) :
    emittedInRound S rho v k = true ↔
      ∃ a : NamedAttestation V, a.val_index = v ∧ a.round = k ∧
        NamedRun.emits S rho v (.attest a) (S.a k) := by
  constructor
  · intro h
    obtain ⟨i, _, hs⟩ := List.any_eq_true.mp h
    cases he : rho.events[i]? with
    | none => simp [he] at hs
    | some e =>
      cases e with
      | deliver u o t => simp [he] at hs
      | tick u t =>
        by_cases hg : u = v ∧ t = S.a k
        · simp only [he, if_pos hg] at hs
          obtain ⟨o, ho, hrow⟩ := List.any_eq_true.mp hs
          cases o with
          | block B => cases hrow
          | gfVote b => cases hrow
          | attest a =>
            have hf : a.val_index = v ∧ a.round = k := of_decide_eq_true hrow
            refine ⟨a, hf.1, hf.2, ?_⟩
            obtain ⟨rfl, rfl⟩ := hg
            exact ⟨i, he, ho⟩
        · simp only [he, if_neg hg, Bool.false_eq_true] at hs
  · rintro ⟨a, hval, hr, i, hi, ho⟩
    apply List.any_eq_true.mpr
    refine ⟨i, List.mem_range.mpr (List.getElem?_eq_some_iff.mp hi).1, ?_⟩
    simp only [hi]
    apply List.any_eq_true.mpr
    exact ⟨NamedObject.attest a, ho, decide_eq_true ⟨hval, hr⟩⟩

theorem honestRoundVoters_iff (S : Setup V) (rho : NamedRun V) (v : V) (k : Round) :
    v ∈ honestRoundVoters S rho k ↔ v ∈ rho.honest ∧
      ∃ a : NamedAttestation V, a.val_index = v ∧ a.round = k ∧
        NamedRun.emits S rho v (.attest a) (S.a k) := by
  simp only [honestRoundVoters, Finset.mem_filter, emittedInRound_iff]

private theorem window_bounds {eta r k : Nat} (hk : k ∈ Protocol.latest_window eta r) :
    r - eta ≤ k ∧ k < r := by
  simp only [Protocol.latest_window, List.mem_range', Nat.one_mul] at hk
  obtain ⟨i, hi, heq⟩ := hk
  omega

theorem historical_of_vote (S : Setup V) (rho : NamedRun V)
    {u : V} {k r : Round} (hlo : r - S.hc.η_SG ≤ k) (hbefore : k + 1 < r)
    (hvote : u ∈ honestRoundVoters S rho k) :
    u ∈ historicalHonestVoters S rho r := by
  apply Finset.mem_biUnion.mpr
  refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hlo, hbefore⟩, hvote⟩
  exact Nat.lt_trans (Nat.lt_succ_self k) hbefore

theorem stale_of_eligible_vote (S : Setup V) (rho : NamedRun V)
    {u : V} {k r : Round} (hwindow : k ∈ Protocol.latest_window S.hc.η_SG r)
    (hvote : u ∈ honestRoundVoters S rho k)
    (hnot : u ∉ honestRoundVoters S rho (r - 1)) :
    u ∈ staleHistoricalVoters S rho r := by
  obtain ⟨hlo, hlt⟩ := window_bounds hwindow
  have hne : k ≠ r - 1 := by intro heq; exact hnot (heq ▸ hvote)
  have before : ∀ k r : Nat, k < r → k ≠ r - 1 → k + 1 < r := by
    intro k r h1 h2
    omega
  have hbefore := before k r hlt hne
  exact Finset.mem_sdiff.mpr ⟨historical_of_vote S rho hlo hbefore hvote, hnot⟩

#print axioms action_read_invariant
#print axioms emitted_attestation_stages
#print axioms emitted_attestation_head
end DecoupledConsensusModel.Proofs.NamedOutageInputs

end
