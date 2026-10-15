module
public import Proofs.Vocabulary.Execution.Runtime
public import Proofs.Vocabulary.Protocol.Duties.Proposals.Actions
public import Proofs.Vocabulary.ModelProperties.NamedDuties_update_confirmation_with
public import Proofs.Vocabulary.ModelProperties.confirmationReadFrom
public import Proofs.Vocabulary.ModelProperties.NamedDuties_attest_with
public import Proofs.Vocabulary.ModelProperties.with_attestation_input
public import Proofs.Vocabulary.ModelProperties.Store_toHealing
import Proofs.Vocabulary.Execution.HealthyLocalFacts
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

@[expose] public section

/-!
# The round action's read, emission and FG source

Facts about a node's tick at a round's action time: the read it acts on, the attestation it emits,
and the FG source and witness behind that attestation's height pair.
-/
namespace DecoupledConsensusModel.Proofs.NamedActionSources
open Execution NamedActionReads
variable {V : Type} [DecidableEq V] [Fintype V]

private theorem action_slot_pos (S : Setup V) (r : Round) :
    0 < S.E.slotOf (S.a r) := by
  rw [Setup.a, Protocol.a_eq_support_cutoff_succ, Proofs.Optimistic.slotOf_support_cutoff]
  exact Nat.zero_lt_succ _

private theorem action_support_time (S : Setup V) (r : Round) :
    S.a r = Protocol.support_cutoff S.E (S.E.slotOf (S.a r)) := by
  rw [Setup.a, Protocol.a_eq_support_cutoff_succ, Proofs.Optimistic.slotOf_support_cutoff]

private theorem action_read_round (S : Setup V) (before : NamedNodeState V) (r : Round) :
    S.hc.round_of (actionReadFrom S before r).st.core.s = r :=
  Proofs.HealingLemmas.round_of_slotOf_a S r

/-- At round `r`'s action time, the tick emits the attestation `attest_with` computes on the action
    read when `v` is awake at round `r`, and nothing otherwise. -/
theorem tick_at_action (S : Setup V) (v : V) (before : NamedNodeState V) (r : Round) :
    (Execution.NamedNode.tick S v before (S.a r)).2 =
      let n := actionReadFrom S before r
      let gc := NamedProfile.gradeContract n.cache
      if (S.node v).awake r = true then
        [NamedObject.attest
          (Protocol.NamedDuties.attest_with gc S.E S.hc (S.node v) n.st n.record).2.2]
      else [] := by
  have hpos := action_slot_pos S r
  have hs := action_support_time S r
  have hp : ¬ (0 < S.E.slotOf (S.a r) ∧
      S.a r = Protocol.proposal_time S.E (S.E.slotOf (S.a r)) ∧
      S.E.proposer (S.E.slotOf (S.a r)) = (S.node v).val_index) := by
    intro h
    exact Proofs.Optimistic.support_cutoff_ne_proposal_time S.E _ (hs.symm.trans h.2.1)
  have hv : ¬ (0 < S.E.slotOf (S.a r) ∧
      S.a r = Protocol.vote_time S.E (S.E.slotOf (S.a r))) := by
    intro h
    exact Proofs.Optimistic.support_cutoff_ne_vote_time S.E _ (hs.symm.trans h.2)
  change (Protocol.NamedTick.tick (NamedProfile.gradeContract (preparedCache S before (S.a r)))
    S.E S.hc S.cfg (S.node v) before.st before.record (S.a r)).2.2 = _
  rw [NamedTick.tick_computed_duties]
  simp only [if_neg hp, if_neg hv, if_pos (And.intro hpos hs), List.nil_append]
  have hround : S.hc.round_of (Protocol.NamedDuties.update_confirmation_with
      (NamedProfile.gradeContract (preparedCache S before (S.a r))) S.E S.hc
      (Protocol.NamedStore.setClock S.E before.st (S.a r)) (S.E.slotOf (S.a r) - 1)).core.s = r :=
    Proofs.HealingLemmas.round_of_slotOf_a S r
  simp only [hround, true_and]
  split_ifs <;> rfl


theorem frame_fg_source_mem (S : Setup V) (cache : DecoupledConsensusModel.Protocol.Cache V)
    (st : Protocol.NamedStore V) (r : Round)
    (hinv : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg st)
    {raw : Block V}
    (hs : Protocol.fg_source_with (NamedProfile.gradeContract cache)
      S.E S.hc st.core.toHealing r
      (Protocol.grade2_block_with (NamedProfile.gradeContract cache)
        S.E S.hc st.core.toHealing r) = some raw) : raw ∈ st.core.T := by
  unfold Protocol.fg_source_with at hs
  cases hQ : Protocol.grade2_block_with (NamedProfile.gradeContract cache)
      S.E S.hc st.core.toHealing r with
  | none => simp [hQ] at hs
  | some q =>
    simp only [hQ] at hs
    cases hd : Protocol.deepest_clear (some q) st.core.toHealing.live_confirmed
        ((NamedProfile.gradeContract cache).read S.E S.hc st.core.toHealing r).clear with
    | none =>
      rw [hd] at hs
      have he : q = raw := Option.some.inj hs
      rw [← he]
      exact Proofs.NamedConfirmationMembership.runtime_Q2_mem cache
        S.E S.hc st.core.toHealing r q hQ
    | some B =>
      rw [hd] at hs
      have he : B = raw := Option.some.inj hs
      rw [← he]
      exact Proofs.NamedStoreRoots.core_ancestor_mem S.E S.cfg st hinv.1.1
        hinv.2.1 (Proofs.Engine.deepest_clear_preceq hd)


/-- Round `r`'s action time falls in a positive slot, is that slot's support cutoff, and the action
    read's slot is in round `r`. -/
theorem action_timing (S : Setup V) (before : NamedNodeState V) (r : Round) :
    0 < S.E.slotOf (S.a r) ∧
    S.a r = Protocol.support_cutoff S.E (S.E.slotOf (S.a r)) ∧
    S.hc.round_of (actionReadFrom S before r).st.core.s = r :=
  ⟨action_slot_pos S r, action_support_time S r, action_read_round S before r⟩

/-- On a run with `NamedScheduleWellFormed`, the node state before an action tick at index `i` is
    the node state before the action time. -/
theorem action_read_index (S : Setup V) (rho : Run V) :
    NamedScheduleWellFormed S rho →
    ∀ i v r, rho.events[i]? = some (.tick v (S.a r)) →
      NamedRun.stateBefore S rho i v = NamedRun.stateBeforeTime S rho (S.a r) v := by
  intro hs i v r hi
  exact Proofs.NamedRuntime.tick_prefix_eq_strict S rho hs.sorted hs.nodup hi

/-- On a run with `NamedScheduleWellFormed`, the action tick at index `i` emits
    `actionAttestationAt S rho v r` when `v` is awake at round `r`, and nothing otherwise. -/
theorem action_emission (S : Setup V) (rho : Run V) :
    NamedScheduleWellFormed S rho →
    ∀ i v r, rho.events[i]? = some (.tick v (S.a r)) →
      (NamedRun.emittedAt S rho i v (S.a r) =
        if (S.node v).awake r = true then
          [.attest (Proofs.HealingSurface.actionAttestationAt S rho v r)] else []) := by
  intro hs i v r hi
  unfold NamedRun.emittedAt
  rw [tick_at_action, action_read_index S rho hs i v r hi]
  rfl

/-- On a run with `NamedScheduleWellFormed`, `v` emits the attestation `row` at round `r`'s action
    time exactly when the run has that tick, `v` is awake at round `r`, and `row` is
    `actionAttestationAt S rho v r`. -/
theorem action_run_emission (S : Setup V) (rho : Run V) :
    NamedScheduleWellFormed S rho →
    ∀ v r (row : NamedAttestation V), NamedRun.emits S rho v (.attest row) (S.a r) ↔
      (∃ i : Nat, rho.events[i]? = some (NamedEvent.tick v (S.a r))) ∧
      (S.node v).awake r = true ∧ row = Proofs.HealingSurface.actionAttestationAt S rho v r := by
  intro hs v r row
  constructor
  · rintro ⟨i, hi, hrow⟩
    rw [action_emission S rho hs i v r hi] at hrow
    by_cases hawake : (S.node v).awake r = true
    · simp only [if_pos hawake, List.mem_singleton, NamedObject.attest.injEq] at hrow
      exact ⟨⟨i, hi⟩, hawake, hrow⟩
    · simp only [if_neg hawake, List.not_mem_nil] at hrow
  · rintro ⟨⟨i, hi⟩, hawake, rfl⟩
    refine ⟨i, hi, ?_⟩
    rw [action_emission S rho hs i v r hi, if_pos hawake]
    exact List.mem_singleton_self _

/-- If the action attestation's height pair is `.vote h entry timeout`, the action read has an FG
    source `Cfg` whose chain state has height `h` and height-target root `entry`. -/
theorem action_source (S : Setup V) (rho : Run V) (v : V) (r : Round) :
    ∀ h entry timeout,
      (Proofs.HealingSurface.actionAttestationAt S rho v r).height_pair = .vote h entry timeout →
      ∃ Cfg, Proofs.HealingSurface.actionFGSource S (Proofs.HealingSurface.actionReadAt S rho v r) =
          some Cfg ∧
        ((Proofs.HealingSurface.actionReadAt S rho v r).st.core.σ Cfg).h = h ∧
        ((Proofs.HealingSurface.actionReadAt S rho v r).st.core.σ Cfg).T_h.root = entry := by
  intro h entry timeout hp
  let n := Proofs.HealingSurface.actionReadAt S rho v r
  let gc := NamedProfile.gradeContract n.cache
  have hpair : (Protocol.NamedActions.round_action_with gc S.E S.hc
      (S.node v) n.st.core.toHealing n.record).2.height_pair = .vote h entry timeout := by
    have h0 : (Protocol.NamedDuties.attest_with gc S.E S.hc (S.node v) n.st
        n.record).2.2.height_pair = .vote h entry timeout := hp
    rw [Proofs.ModelProperties.attest_with_row] at h0
    exact h0
  obtain ⟨nu, hfields⟩ := Proofs.NamedActions.round_action_names_source gc S.E S.hc
    (S.node v) n.st.core.toHealing n.record h entry timeout hpair
  change (Protocol.with_attestation_input gc S.E S.hc (S.node v) n.st.core.toHealing id).fields =
    some (h, entry, nu) at hfields
  rw [Proofs.ModelProperties.with_attestation_input_id_fields,
    Proofs.ModelProperties.toHealing_σ] at hfields
  obtain ⟨Cfg, hCfg, hvalues⟩ := Option.map_eq_some_iff.mp hfields
  exact ⟨Cfg, hCfg, congrArg Prod.fst hvalues,
    congrArg (fun x : Height × BlockId × Bool => x.2.1) hvalues⟩

private theorem action_read_invariant (S : Setup V) (rho : Run V) (v : V) (r : Round) :
    Proofs.NamedConfirmationMembership.Invariant S.E S.cfg
      (Proofs.HealingSurface.actionReadAt S rho v r).st := by
  apply Proofs.ModelProperties.invariant_update_gradeContract
  rw [Proofs.ModelProperties.confirmationReadFrom_st]
  exact Proofs.NamedConfirmationMembership.invariant_clock S.E S.cfg _ (S.a r)
    (Proofs.NamedRuntime.stateBeforeTime_invariants S rho (S.a r) v).1

/-- The action read's FG source `Cfg` is the erasure of a body `C` of the read, its chain state is
    `derive_named` of `C`, and the read's confirmation witness is `C`'s height target. -/
theorem action_witness (S : Setup V) (rho : Run V) (v : V) (r : Round) :
    ∀ Cfg, Proofs.HealingSurface.actionFGSource S (Proofs.HealingSurface.actionReadAt S rho v r) =
        some Cfg →
      ∃ C : NamedBlock V,
        C ∈ (Proofs.HealingSurface.actionReadAt S rho v r).st.bodies ∧ C.erase = Cfg ∧
        (Proofs.HealingSurface.actionReadAt S rho v r).st.core.σ Cfg =
          Protocol.derive_named S.E S.cfg C ∧
        Proofs.HealingSurface.fgConfirmationWitness S (Proofs.HealingSurface.actionReadAt S rho v r) =
          some (Protocol.derive_named S.E S.cfg C).T_h := by
  intro Cfg hCfg
  let n := Proofs.HealingSurface.actionReadAt S rho v r
  have hinv : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg n.st :=
    action_read_invariant S rho v r
  have hcoh : Proofs.NamedStore.Coherent S.E S.cfg n.st := hinv.1.1
  have hmem : Cfg ∈ n.st.core.T := frame_fg_source_mem S n.cache n.st
    (S.hc.round_of n.st.core.toHealing.s) hinv hCfg
  rw [hcoh.1] at hmem
  obtain ⟨C, hC, hErase⟩ := Finset.mem_image.mp hmem
  have hDerived : n.st.core.σ Cfg = Protocol.derive_named S.E S.cfg C := by
    rw [← hErase]
    exact hcoh.2.2.2.2 C hC
  refine ⟨C, hC, hErase, hDerived, ?_⟩
  change (Proofs.HealingSurface.actionFGSource S n).map (fun B => (n.st.core.σ B).T_h) = _
  rw [hCfg, Option.map_some, hDerived]

end DecoupledConsensusModel.Proofs.NamedActionSources

end
