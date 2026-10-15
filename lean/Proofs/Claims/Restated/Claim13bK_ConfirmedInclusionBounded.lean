import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bW_Schedule
import Proofs.Claims.Restated.Claim13beRoute3_85gBounded
import Proofs.Claims.Restated.Claim13bK_ConfirmedOld
import Proofs.Claims.Restated.Claim13bK_HeadsPersist
import Proofs.Claims.Restated.Claim13bK_LiveConfirmedSlots
import Proofs.Claims.Restated.Claim13bK_PrevHeadsStep
import Proofs.Claims.Restated.Claim13bStepConeIter
import Proofs.Claims.Restated.Claim13beRoute3_82
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActiveJoint
import Model.Conditions.Claim13bInvariantActiveSince
import Model.Conditions.Claim13bInvariantActiveSinceW
import Model.Conditions.Claim13bK_ConfirmedInclusion
import Model.Conditions.Claim13bK_ConfirmedSettle
import Model.Conditions.Claim13bK_FgJustified
import Model.Conditions.Claim13bK_FinBeforeTick
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13bStepAnchor
import Model.Conditions.Claim13bStepConeIter
import Model.Conditions.Claim13bStepFieldsAt
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_74
import Model.Conditions.Claim13beRoute3_83
import Model.Conditions.RunAll
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13bd
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring

/-!
# Anchor chains and honest heads with no catch-up premise, stepped only up to a time `tHi`

The twins of `exists_anchor_chain_withoutCatchUp_i1` and
`exists_anchor_chain_secondSlot_withoutCatchUp_i1`
(`lean/Proofs/Claims/Restated/Claim13bK_ConfirmedInclusion.lean`) that reach only the rounds
`r + k` with `S.a (r + k) ≤ tHi`, through the bounded step
`afterPhaseJointRound_withoutCatchUp_bounded`. The switch round and the base stay at the phase end
`tE`; `tHi` is a second time with `tE ≤ tHi`, up to which every validator not held is awake from
`tGAT` on (the hypothesis `hphaseHi`). The twins of the four honest-heads lemmas of that file
(`anchor_ancestorOfHonestHeadsFrom_withoutCatchUp_i1`, `headsBelow_persist_rounds_withoutCatchUp_i1`,
`ancestorOfHonestHeadsFrom_of_compatible_anchor_withoutCatchUp_i1`,
`ancestorOfHonestHeadsFrom_of_headsBelow_i1`) and of `honestProposal_ancestorOfHonestHeadsFrom_i1`
step only through these two chains, and conclude for a slot `s'` only when the round containing
`s'` has its action instant at or before `tHi`. Stated over a model `M : Record.Model V` and its
facts.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

local macro "pLCS% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13bK_LiveConfirmedSlots)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- After a healing phase from `tGAT` (at or after GST) of length `healingLengthη` ending at `tL`, the
    action instant of the switch round of `tL` is at least one delay before `tL`. -/
theorem action_switchRound_add_delta_le_b (facts : Record.Facts M) (S : Setup V) (tGAT tL : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tL) :
    Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tL) + S.E.Δ ≤ tL := by
  have hne : Restated.switchRound M S tL ≠ 0 :=
    Nat.pos_iff_ne_zero.mp (Restated.one_le_switchRound facts S tGAT tL gap hgst hlen)
  have h1 := Restated.switchRound_spec facts S tL hne
  have h2 := facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E
    ((M.opening_slot S.hc (Restated.switchRound M S tL)) + 2)
  have h3 := Restated.confirmation_time_opening_slot facts S (Restated.switchRound M S tL)
  have h4 := facts.sch.slotStart_add_six_delta_eq_confirmation_time S.E
    (M.opening_slot S.hc (Restated.switchRound M S tL))
  have h5 : slotStart S.E.Δ ((M.opening_slot S.hc (Restated.switchRound M S tL)) + 2) =
      slotStart S.E.Δ (M.opening_slot S.hc (Restated.switchRound M S tL)) + 8 * S.E.Δ := by
    rw [slotStart_closed, slotStart_closed]; push_cast; ring
  have hd := S.E.Δ_pos
  linarith

/-- Inside the phase extended to `tHi`: with every validator not held at a time of `[tGAT, tHi]` awake
    at that time, corruption only growing, round `r` at or after the switch round and
    `S.a r + Δ ≤ tHi`, `NextRoundReceipts` holds at round `r`: a member of `HonRound (r + 1)` or a
    grade-1 performer of round `r + 1` is awake on `[S.a r, S.a r + Δ]`, and synchrony delivers. -/
theorem nextRoundReceipts_of_phase_delta_b (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hsync : Restated.SynchronyFromWake M S x) (hmono : Sched.MonotoneCorruption) {tHi : Int}
    (hphaseHi : ∀ t : Int, tGAT ≤ t → t ≤ tHi → ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    {r : Round} (hr : Restated.switchRound M S tE ≤ r)
    (hhi : Restated.Vocabulary.Execution.Setup.a M S r + S.E.Δ ≤ tHi) :
    Restated.NextRoundReceipts M S Sched x r := by
  have hopen : M.opening S.E S.hc r ≤ Restated.Vocabulary.Execution.Setup.a M S r := by
    show _ ≤ M.a S.hc S.E.Δ r
    rw [facts.gr.opening_eq_proposal_time, facts.sch.a_eq_confirmation_time]
    exact facts.sch.proposal_time_le_confirmation_time _ _
  have hlo : tGAT ≤ Restated.Vocabulary.Execution.Setup.a M S r :=
    le_trans (Restated.tGAT_le_switchOpening facts S tGAT tE gap hgst hlen)
      (le_trans (Restated.switchOpening_le_opening facts S hr) hopen)
  have hgstr := Restated.gst_le_action_of_switchRound_le facts S tGAT tE gap hgst hlen hr
  have hle1 := Restated.action_delta_lt_domain_succ facts S r .g1
  have hle2 := Restated.action_delta_lt_domain_succ facts S r .g2
  have hdom1 := facts.gr.domain_le_action S (r + 1) .g1
  have hdom2 := facts.gr.domain_le_action S (r + 1) .g2
  have hawk : ∀ v : V, ∀ t₁ : Int, Restated.Vocabulary.Execution.Setup.a M S r + S.E.Δ ≤ t₁ →
      v ∉ Sched.adv t₁ →
      v ∈ Sched.awakeThroughout (Restated.Vocabulary.Execution.Setup.a M S r)
        (Restated.Vocabulary.Execution.Setup.a M S r + S.E.Δ) := fun v t₁ ht₁ hv =>
    mem_awakeThroughout_of_forall Sched fun t h0 h1 =>
      hphaseHi t (le_trans hlo h0) (le_trans h1 hhi) v (fun h => hv (hmono t _ (le_trans h1 ht₁) h))
  refine ⟨fun v hv => ?_, fun v hv => ?_⟩
  · exact (Restated.receivesRoundAttestationsBefore_of_sync facts S Sched x hsync hgstr
      (hawk v _ (le_of_lt (lt_of_lt_of_le hle2 hdom2)) (Finset.mem_sdiff.1 hv).2)).mono
      (Restated.action_delta_le_early_succ facts S r)
  · exact (Restated.receivesRoundAttestationsBefore_of_sync facts S Sched x hsync hgstr
      (hawk v _ (le_of_lt hle1) (Finset.mem_sdiff.1 hv).2)).mono
      (le_trans (Restated.action_delta_le_early_succ facts S r) (Restated.early_g2_le_early facts S (r + 1) .g1))

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Under its premises on the execution and the phase ending at `tE`, with every validator not held
    awake from `tGAT` up to a time `tHi` at or after `tE`, if round `r` is at or after
    the switch round, `T_W` is an ancestor of `T`, and the joint invariant holds at round `r` with
    tick step `n`, switch step `n_W` and anchor `T`, then for every `k` with `S.a (r + k) ≤ tHi` there
    are a tick step `n_k` and an anchor `T_k` such that the joint invariant holds at round `r + k` with them and `n_W`,
    and `T` and `T_W` are both ancestors of `T_k`. -/
theorem exists_anchor_chain_withoutCatchUp_bounded (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hsync : Restated.SynchronyFromWake M S x)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (tHi : Int) (hEHi : tE ≤ tHi)
    (hphaseHi : ∀ t : Int, tGAT ≤ t → t ≤ tHi →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE)
    (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hcs : Restated.committeeSleepinessW M S Sched tE)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    (hprev : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.BasePreviousRoundSGCompatibleWithAnchorAtRound M S Sched x v r N
        (Restated.runAllPath M S Sched x v N) T)
    (hclear : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round) (n₀ : Nat),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S r)) →
      Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T)
    (hB' : Restated.BaseJustifiedHighAtSwitchRoundW M S Sched x tGAT tE gap)
    {n_W : Nat} (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    {T_W : NamedBlock V} (hAW : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.switchRound M S tE) T_W)
    (hJswitch : ∀ (v : V) (n₁ : Nat),
      M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) - 1
        ≤ (x[n₁].time : Int) →
      n₁ ≤ n_W → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J T_W.erase)
    {r : Round} {n : Nat} {T : NamedBlock V}
    (hr : Restated.switchRound M S tE ≤ r) (hTW : Block.Preceq T_W.erase T.erase)
    (hJ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x r n n_W T) :
    ∀ k : Nat, Restated.Vocabulary.Execution.Setup.a M S (r + k) ≤ tHi →
      ∃ (n_k : Nat) (T_k : NamedBlock V),
      Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x (r + k) n_k n_W T_k ∧
        Block.Preceq T.erase T_k.erase ∧ Block.Preceq T_W.erase T_k.erase := by
  intro k
  induction k with
  | zero => intro _; exact ⟨n, T, hJ, preceq_eq_true_iff_Preceq.mp (Block.preceq_self _), hTW⟩
  | succ k ih =>
    intro hk
    obtain ⟨n_k, T_k, hJk, hTk, hWk⟩ := ih (le_trans (Restated.action_mono facts S (Nat.le_succ _)) hk)
    obtain ⟨n', hn'⟩ := Restated.tick_field_at_succ facts S Sched x htd (r + k)
    obtain ⟨att, hatt⟩ := (pLCS% exists_actionAttestationsOf_lcs) facts S Sched x (r + k) n'
    obtain ⟨-, hstep⟩ := Restated.afterPhaseJointRound_withoutCatchUp_bounded facts S Sched x tE hexec hmono htd
      tGAT gap hgst hlen hsync hthird hphase tHi hEHi hphaseHi hrsW hmult hcv hcs hcom hrec hprev hclear hB'
      hnW hAW hJswitch (le_trans hr (Nat.le_add_right r k)) hWk hJk hn' hk
    obtain ⟨hJ', hTT'⟩ := hstep att hatt
    exact ⟨n', _, hJ', preceq_trans_Preceq hTk hTT', preceq_trans_Preceq hWk hTT'⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Under its premises on the execution and the phase ending at `tE`, with every validator not held
    awake from `tGAT` up to a time `tHi` at or after `tE`, if round `r` is at or after
    the switch round, `T_W` is an ancestor of `T`, and the joint invariant holds at round `r` with
    anchor `T`, then for every `k` with `S.a (r + k) ≤ tHi` there are a tick step `n_k` and an anchor
    `T_k` such that the joint invariant holds at round `r + k` with them, `T_W` is an ancestor of `T_k`, and, when
    `k > 0`, every honest active member of the committee of the slot after round `r + k`'s opening
    slot votes for a descendant of `T_k`. -/
theorem exists_anchor_chain_secondSlot_withoutCatchUp_bounded (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hsync : Restated.SynchronyFromWake M S x)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (tHi : Int) (hEHi : tE ≤ tHi)
    (hphaseHi : ∀ t : Int, tGAT ≤ t → t ≤ tHi →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE)
    (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hcs : Restated.committeeSleepinessW M S Sched tE)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    (hprev : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.BasePreviousRoundSGCompatibleWithAnchorAtRound M S Sched x v r N
        (Restated.runAllPath M S Sched x v N) T)
    (hclear : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round) (n₀ : Nat),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S r)) →
      Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T)
    (hB' : Restated.BaseJustifiedHighAtSwitchRoundW M S Sched x tGAT tE gap)
    {n_W : Nat} (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    {T_W : NamedBlock V} (hAW : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.switchRound M S tE) T_W)
    (hJswitch : ∀ (v : V) (n₁ : Nat),
      M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) - 1
        ≤ (x[n₁].time : Int) →
      n₁ ≤ n_W → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J T_W.erase)
    {r : Round} {n : Nat} {T : NamedBlock V}
    (hr : Restated.switchRound M S tE ≤ r) (hTW : Block.Preceq T_W.erase T.erase)
    (hJ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x r n n_W T) :
    ∀ k : Nat, Restated.Vocabulary.Execution.Setup.a M S (r + k) ≤ tHi →
      ∃ (n_k : Nat) (T_k : NamedBlock V),
      Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x (r + k) n_k n_W T_k ∧
        Block.Preceq T_W.erase T_k.erase ∧
        (0 < k → Restated.HeadsBelow M S Sched x T_k.erase ((M.opening_slot S.hc (r + k)) + 1)) := by
  intro k
  induction k with
  | zero => intro _; exact ⟨n, T, hJ, hTW, fun h => absurd h (Nat.lt_irrefl 0)⟩
  | succ k ih =>
    intro hk
    obtain ⟨n_k, T_k, hJk, hWk, -⟩ := ih (le_trans (Restated.action_mono facts S (Nat.le_succ _)) hk)
    have hrk : Restated.switchRound M S tE ≤ r + k := le_trans hr (Nat.le_add_right r k)
    obtain ⟨n', hn'⟩ := Restated.tick_field_at_succ facts S Sched x htd (r + k)
    obtain ⟨n'', hn''⟩ := Restated.tick_field_at_succ facts S Sched x htd (r + k + 1)
    obtain ⟨att, hatt⟩ := (pLCS% exists_actionAttestationsOf_lcs) facts S Sched x (r + k) n'
    obtain ⟨-, hstep⟩ := Restated.afterPhaseJointRound_withoutCatchUp_bounded facts S Sched x tE hexec hmono htd
      tGAT gap hgst hlen hsync hthird hphase tHi hEHi hphaseHi hrsW hmult hcv hcs hcom hrec hprev hclear hB'
      hnW hAW hJswitch hrk hWk hJk hn' hk
    obtain ⟨hJ', hTT'⟩ := hstep att hatt
    have hinvS := hJk.toAfterPhaseInvariantOverActiveSetsSince
    have hJW : ∀ n₀ : Nat, Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S (r + k + 1))) →
        ∀ (v : V) (n₁ : Nat), n_W ≤ n₁ → n₁ ≤ n₀ + 1 → Restated.HonestThrough M Sched x n₁ v →
          Block.Preceq (x[n₁][v].st).st.core.J T_k.erase :=
      fun n₀ h => Restated.justified_preceq_anchor_ofJoint facts S Sched x tE hexec hmono htd tGAT gap hgst hlen
        hsync hthird hphase hrsW hmult hcv hcom hrec hprev hclear hB' hnW hAW hrk hWk hJk h
    have hcross : ∀ n₀ : Nat, Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S (r + k + 1))) →
        Restated.StepFinalizedCrossingUnderAnchor M S Sched x (r + k) n₀ T_k :=
      fun n₀ h => Restated.stepFinalizedCrossingUnderAnchor_of_afterSwitch facts S Sched x hrk hnW hinvS
        (hJW n₀ h)
    have hjust : ∀ n₀ : Nat, Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S (r + k + 1))) →
        Restated.StepJustifiedRootUnderAnchor M S Sched x (r + k) n_k n₀ T_k :=
      fun n₀ h => Restated.stepJustifiedRootUnderAnchor_of_afterSwitch facts S Sched x hrk hnW hinvS (hJW n₀ h)
    have hTW' := preceq_trans_Preceq hWk hTT'
    have hJ'' := Restated.justified_preceq_anchor_ofJoint facts S Sched x tE hexec hmono htd tGAT gap hgst hlen
      hsync hthird hphase hrsW hmult hcv hcom hrec hprev hclear hB' hnW hAW
      (le_trans hrk (Nat.le_succ _)) hTW' hJ' hn''
    have h2 := Restated.headsBelow_secondSlot_at_newAnchor facts S Sched x tE hexec hmono htd hsync hmult hcom
      tGAT gap hgst hlen hcv hthird hphase hrsW hcs hrk hinvS.toTop hcross hjust hnW hn' hn'' hatt
      hTT' hJ'' (hJ'.prevHeads n_k hinvS.tick) (hJ'.prevConfirmed n_k hinvS.tick)
    have hrecvRk : Restated.NextRoundReceipts M S Sched x (r + k) :=
      Restated.nextRoundReceipts_of_phase_delta_b facts S Sched x tE tGAT gap hgst hlen hsync hmono hphaseHi hrk
        (le_trans (le_of_lt (lt_of_lt_of_le (Restated.action_delta_lt_domain_succ facts S (r + k) .g1)
          (facts.gr.domain_le_action S (r + k + 1) .g1))) hk)
    exact ⟨n', _, hJ', hTW', fun _ => h2 hrecvRk⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If round `ρ`'s opening slot is at or before slot `s`, and the round containing `s` has its
    action instant at or before `tHi`, then round `ρ`'s action instant is at or before `tHi`. -/
theorem action_le_of_opening_slot_le_bounded (facts : Record.Facts M) (S : Setup V) {ρ : Round} {s : Slot}
    {tHi : Int} (h : (M.opening_slot S.hc ρ) ≤ s)
    (hb : Restated.Vocabulary.Execution.Setup.a M S (M.round_of S.hc s) ≤ tHi) :
    Restated.Vocabulary.Execution.Setup.a M S ρ ≤ tHi := by
  have hρ : ρ ≤ M.round_of S.hc s := by
    by_contra hcon
    have h1 := facts.gr.lt_opening_slot_round_of_succ S.hc s
    have h2 : (M.opening_slot S.hc ((M.round_of S.hc s) + 1)) ≤ (M.opening_slot S.hc ρ) :=
      facts.gr.opening_slot_mono S (Nat.succ_le_of_lt (Nat.lt_of_not_le hcon))
    exact Nat.lt_irrefl s (lt_of_lt_of_le h1 (le_trans h2 h))
  exact le_trans (Restated.action_mono facts S hρ) hb

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Under its premises on the execution and the phase ending at `tE`, with every validator not held
    awake from `tGAT` up to a time `tHi` at or after `tE`, if round `r` is at or after the switch
    round, `T_W` is an ancestor of `T`, and the joint invariant holds at round `r` with anchor `T`,
    then for every slot `s'` from two after round `r`'s opening slot on whose round has its action
    instant at or before `tHi`, every honest active member of slot `s'`'s committee votes for a
    descendant of `T`. The twin of `anchor_ancestorOfHonestHeadsFrom_withoutCatchUp_i1` that steps
    only through `exists_anchor_chain_withoutCatchUp_bounded`. -/
theorem anchor_ancestorOfHonestHeadsFrom_withoutCatchUp_bounded (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hsync : Restated.SynchronyFromWake M S x)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (tHi : Int) (hEHi : tE ≤ tHi)
    (hphaseHi : ∀ t : Int, tGAT ≤ t → t ≤ tHi →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE)
    (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hcs : Restated.committeeSleepinessW M S Sched tE)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    (hprev : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.BasePreviousRoundSGCompatibleWithAnchorAtRound M S Sched x v r N
        (Restated.runAllPath M S Sched x v N) T)
    (hclear : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round) (n₀ : Nat),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S r)) →
      Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T)
    (hB' : Restated.BaseJustifiedHighAtSwitchRoundW M S Sched x tGAT tE gap)
    {n_W : Nat} (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    {T_W : NamedBlock V} (hAW : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.switchRound M S tE) T_W)
    (hJswitch : ∀ (v : V) (n₁ : Nat),
      M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) - 1
        ≤ (x[n₁].time : Int) →
      n₁ ≤ n_W → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J T_W.erase)
    {r : Round} {n : Nat} {T : NamedBlock V}
    (hr : Restated.switchRound M S tE ≤ r) (hTW : Block.Preceq T_W.erase T.erase)
    (hJ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x r n n_W T) :
    ∀ s' : Slot, (M.opening_slot S.hc r) + 2 ≤ s' →
      Restated.Vocabulary.Execution.Setup.a M S (M.round_of S.hc s') + S.E.Δ ≤ tHi →
      Restated.HeadsBelow M S Sched x T.erase s' := by
  intro s hs0 hsb
  obtain ⟨k, hk0, hk1⟩ := facts.gr.exists_round_of_slot S.hc r hs0
  have hkb : Restated.Vocabulary.Execution.Setup.a M S (r + k) ≤ tHi :=
    Restated.action_le_of_opening_slot_le_bounded facts S (le_trans (Nat.le_add_right _ 2) hk0) (le_trans (le_add_of_nonneg_right S.E.Δ_pos.le) hsb)
  obtain ⟨n_k, T_k, hJk, hTk, hWk⟩ := Restated.exists_anchor_chain_withoutCatchUp_bounded facts S Sched x tE hexec hmono htd
      tGAT gap hgst hlen hsync hthird hphase tHi hEHi hphaseHi hrsW hmult hcv hcs hcom
      hrec hprev hclear hB' hnW hAW hJswitch
    hr hTW hJ k hkb
  exact Restated.headsBelow_mono facts S Sched x hTk
    (Restated.headsBelow_range_ofJoint facts S Sched x tE hexec hmono htd tGAT gap hgst hlen hsync hthird hphase
      hrsW hmult hcv hcs hcom hrec hprev hclear hB' hnW hAW
      (le_trans hr (Nat.le_add_right r k)) hWk hJk s hk0 hk1)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Under its premises on the execution and the phase ending at `tE`, with every validator not held
    awake from `tGAT` up to a time `tHi` at or after `tE`, for every `k`, every round `r + 1` at or
    after the switch round with the joint invariant at an anchor `T` that is `T_W` or a descendant
    of it, every descendant `B` of `T`, and every slot `s` from `o_{r+1} + 1` to `o_{r+2} + 1` at
    which every honest active committee member votes for a descendant of `B`, the same holds at
    every slot `s'` from `s` to `o_{r+1+k+1} + 1` whose round has its action instant at or before
    `tHi`, where `o_r` is round `r`'s opening slot. The twin of
    `headsBelow_persist_rounds_withoutCatchUp_i1` that steps only through the bounded chains. -/
theorem headsBelow_persist_rounds_withoutCatchUp_bounded (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hsync : Restated.SynchronyFromWake M S x)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (tHi : Int) (hEHi : tE ≤ tHi)
    (hphaseHi : ∀ t : Int, tGAT ≤ t → t ≤ tHi →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE)
    (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hcs : Restated.committeeSleepinessW M S Sched tE)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    (hprev : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.BasePreviousRoundSGCompatibleWithAnchorAtRound M S Sched x v r N
        (Restated.runAllPath M S Sched x v N) T)
    (hclear : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round) (n₀ : Nat),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S r)) →
      Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T)
    (hB' : Restated.BaseJustifiedHighAtSwitchRoundW M S Sched x tGAT tE gap)
    {n_W : Nat} (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    {T_W : NamedBlock V} (hAW : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.switchRound M S tE) T_W)
    (hJswitch : ∀ (v : V) (n₁ : Nat),
      M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) - 1
        ≤ (x[n₁].time : Int) →
      n₁ ≤ n_W → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J T_W.erase)
    {B : Block V} :
    ∀ (k : Nat) (r : Round) (n : Nat) (T : NamedBlock V),
      Restated.switchRound M S tE ≤ r + 1 → Block.Preceq T_W.erase T.erase →
      Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x (r + 1) n n_W T →
      Block.Preceq T.erase B →
      ∀ s : Slot, (M.opening_slot S.hc (r + 1)) + 1 ≤ s → s ≤ (M.opening_slot S.hc (r + 1 + 1)) + 1 →
      Restated.HeadsBelow M S Sched x B s →
      ∀ s' : Slot, s ≤ s' → s' ≤ (M.opening_slot S.hc (r + 1 + k + 1)) + 1 →
        Restated.Vocabulary.Execution.Setup.a M S (M.round_of S.hc s') + S.E.Δ ≤ tHi →
        Restated.HeadsBelow M S Sched x B s' := by
  intro k
  induction k with
  | zero =>
    intro r n T hr hTW hJ hTB s hs0 hs1 hbase s' h0 h1 hsb
    obtain ⟨n', hn'⟩ := Restated.tick_field_at_succ facts S Sched x htd (r + 1)
    obtain ⟨n_prev, hnp0⟩ := hJ.prevTick
    have hnp : Restated.tickStepAt M x n_prev ((Restated.Vocabulary.Execution.Setup.a M S r)) := hnp0
    have hJT := Restated.justified_fromSecondSlot_ofJoint facts S Sched x tE hexec hmono htd tGAT gap hgst hlen
      hsync hthird hphase hrsW hmult hcv hcom hrec hprev hclear hB' hnW hAW hJswitch hr hTW hJ hn'
    have hcross : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1 + 1))) →
        Restated.StepFinalizedCrossingUnderAnchor M S Sched x (r + 1) n'' T :=
      fun n'' h => Restated.stepFinalizedCrossingUnderAnchor_of_afterSwitch facts S Sched x hr hnW hJ.toAfterPhaseInvariantOverActiveSetsSince
        (Restated.justified_preceq_anchor_ofJoint facts S Sched x tE hexec hmono htd tGAT gap hgst hlen hsync
          hthird hphase hrsW hmult hcv hcom hrec hprev hclear hB' hnW hAW hr hTW hJ h)
    have hround : r + 1 ≤ M.round_of S.hc s' := by
      have h := facts.gr.round_of_mono_sts S.hc
        (show M.opening_slot S.hc (r + 1) ≤ s' from le_trans (Nat.le_succ _) (le_trans hs0 h0))
      rwa [facts.gr.round_of_opening_slot_eq] at h
    have hrecvR : Restated.NextRoundReceipts M S Sched x (r + 1) :=
      Restated.nextRoundReceipts_of_phase_delta_b facts S Sched x tE tGAT gap hgst hlen hsync hmono hphaseHi hr
        (by have := Restated.action_mono facts S hround; linarith)
    exact Restated.headsBelow_roundStep (hrecvR := hrecvR) facts S Sched x tE hexec hmono htd hsync hmult hcom tGAT gap hgst hlen
      hcv hthird hphase hrsW hcs hr hJ hn' hcross hJT hnp hTB hs0 hs1 hbase s' h0 h1
  | succ k ih =>
    intro r n T hr hTW hJ hTB s hs0 hs1 hbase s' h0 h1 hsb
    obtain ⟨n', hn'⟩ := Restated.tick_field_at_succ facts S Sched x htd (r + 1)
    obtain ⟨n_prev, hnp0⟩ := hJ.prevTick
    have hnp : Restated.tickStepAt M x n_prev ((Restated.Vocabulary.Execution.Setup.a M S r)) := hnp0
    have hJT := Restated.justified_fromSecondSlot_ofJoint facts S Sched x tE hexec hmono htd tGAT gap hgst hlen
      hsync hthird hphase hrsW hmult hcv hcom hrec hprev hclear hB' hnW hAW hJswitch hr hTW hJ hn'
    have hcross : ∀ n'' : Nat, Restated.tickStepAt M x n'' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1 + 1))) →
        Restated.StepFinalizedCrossingUnderAnchor M S Sched x (r + 1) n'' T :=
      fun n'' h => Restated.stepFinalizedCrossingUnderAnchor_of_afterSwitch facts S Sched x hr hnW hJ.toAfterPhaseInvariantOverActiveSetsSince
        (Restated.justified_preceq_anchor_ofJoint facts S Sched x tE hexec hmono htd tGAT gap hgst hlen hsync
          hthird hphase hrsW hmult hcv hcom hrec hprev hclear hB' hnW hAW hr hTW hJ h)
    have hround : r + 1 ≤ M.round_of S.hc s' := by
      have h := facts.gr.round_of_mono_sts S.hc
        (show M.opening_slot S.hc (r + 1) ≤ s' from le_trans (Nat.le_succ _) (le_trans hs0 h0))
      rwa [facts.gr.round_of_opening_slot_eq] at h
    have hrecvR : Restated.NextRoundReceipts M S Sched x (r + 1) :=
      Restated.nextRoundReceipts_of_phase_delta_b facts S Sched x tE tGAT gap hgst hlen hsync hmono hphaseHi hr
        (by have := Restated.action_mono facts S hround; linarith)
    have hstep := Restated.headsBelow_roundStep (hrecvR := hrecvR) facts S Sched x tE hexec hmono htd hsync hmult hcom tGAT gap hgst
      hlen hcv hthird hphase hrsW hcs hr hJ hn' hcross hJT hnp hTB hs0 hs1 hbase
    by_cases hle : s' ≤ (M.opening_slot S.hc (r + 1 + 1)) + 1
    · exact hstep s' h0 hle
    have hlt : (M.opening_slot S.hc (r + 1 + 1)) + 1 + 1 ≤ s' := Nat.lt_of_not_le hle
    -- the one chain step reaches round `r + 2`, whose opening slot is at or before `s'`
    have hb2 : Restated.Vocabulary.Execution.Setup.a M S (r + 1 + 1) ≤ tHi :=
      Restated.action_le_of_opening_slot_le_bounded facts S
        (Nat.le_of_succ_le (Nat.le_of_succ_le hlt)) (le_trans (le_add_of_nonneg_right S.E.Δ_pos.le) hsb)
    obtain ⟨n_1, T_1, hJ1, hW1, h2⟩ := Restated.exists_anchor_chain_secondSlot_withoutCatchUp_bounded facts S Sched x tE hexec hmono htd
      tGAT gap hgst hlen hsync hthird hphase tHi hEHi hphaseHi hrsW hmult hcv hcs hcom
      hrec hprev hclear hB' hnW hAW hJswitch
      hr hTW hJ 1 hb2
    have hT1 : Restated.HeadsBelow M S Sched x T_1.erase ((M.opening_slot S.hc (r + 1 + 1)) + 1) :=
      h2 (Nat.succ_pos 0)
    have hB2 : Restated.HeadsBelow M S Sched x B ((M.opening_slot S.hc (r + 1 + 1)) + 1) := hstep _ hs1 le_rfl
    have hr2 : Restated.switchRound M S tE ≤ r + 1 + 1 := le_trans hr (Nat.le_succ _)
    obtain ⟨t', -, ht's, -, hcs'⟩ :=
      Restated.exists_cone_cutoff_at_opening facts S Sched tE hmono hcom tGAT gap hgst hlen hphase hcs hr2
    have hpos : 0 < (M.opening_slot S.hc (r + 1 + 1)) + 1 := Nat.succ_pos _
    have hcomp := Restated.compatible_of_headsBelow_after facts S Sched x htd hcs' hpos
      (le_trans ht's (slotStart_mono S (Nat.le_succ_of_le (Nat.le_succ _)))) hT1 hB2
    rcases compatible_cases hcomp with hT1B | hBT1
    · have e : r + 1 + (k + 1) + 1 = r + 1 + 1 + k + 1 := by ring
      rw [e] at h1
      exact ih (r + 1) n_1 T_1 hr2 hW1 hJ1 hT1B _ le_rfl (Nat.succ_le_succ
        (by rw [facts.gr.opening_slot_succ S.hc (r + 1 + 1)]; exact Nat.le_add_right _ _)) hB2 s'
        (Nat.le_of_succ_le hlt) h1 hsb
    · have hanc := Restated.anchor_ancestorOfHonestHeadsFrom_withoutCatchUp_bounded facts S Sched x tE hexec
        hmono htd tGAT gap hgst hlen hsync hthird hphase tHi hEHi hphaseHi hrsW hmult hcv hcs hcom
        hrec hprev hclear hB' hnW hAW hJswitch hr2 hW1 hJ1
      exact Restated.headsBelow_mono facts S Sched x hBT1 (hanc s' hlt hsb)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Under its premises on the execution and the phase ending at `tE`, with every validator not held
    awake from `tGAT` up to a time `tHi` at or after `tE`, if round `r` is at or after the switch
    round, `T_W` is an ancestor of `T`, the joint invariant holds at round `r` with anchor `T`, slot
    `s` is between `o_r + 1` and `o_{r+1} + 1` (`o_r` being round `r`'s opening slot), `B` lies on
    one chain with `T`, and every honest active member of slot `s`'s committee votes for a
    descendant of `B`, then the same holds at every slot `s'` from `s` on whose round has its action
    instant at or before `tHi`. The twin of
    `ancestorOfHonestHeadsFrom_of_compatible_anchor_withoutCatchUp_i1`. -/
theorem ancestorOfHonestHeadsFrom_of_compatible_anchor_withoutCatchUp_bounded (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hsync : Restated.SynchronyFromWake M S x)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (tHi : Int) (hEHi : tE ≤ tHi)
    (hphaseHi : ∀ t : Int, tGAT ≤ t → t ≤ tHi →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE)
    (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hcs : Restated.committeeSleepinessW M S Sched tE)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    (hprev : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.BasePreviousRoundSGCompatibleWithAnchorAtRound M S Sched x v r N
        (Restated.runAllPath M S Sched x v N) T)
    (hclear : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round) (n₀ : Nat),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S r)) →
      Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T)
    (hB' : Restated.BaseJustifiedHighAtSwitchRoundW M S Sched x tGAT tE gap)
    {n_W : Nat} (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    {T_W : NamedBlock V} (hAW : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.switchRound M S tE) T_W)
    (hJswitch : ∀ (v : V) (n₁ : Nat),
      M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) - 1
        ≤ (x[n₁].time : Int) →
      n₁ ≤ n_W → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J T_W.erase)
    {r : Round} {n : Nat} {T : NamedBlock V}
    (hr : Restated.switchRound M S tE ≤ r) (hTW : Block.Preceq T_W.erase T.erase)
    (hJ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x r n n_W T)
    {s : Slot} (hs0 : (M.opening_slot S.hc r) + 1 ≤ s) (hs1 : s ≤ (M.opening_slot S.hc (r + 1)) + 1)
    {B : Block V} (hBT : Block.compatible B T.erase = true)
    (hB : Restated.HeadsBelow M S Sched x B s) :
    ∀ s' : Slot, s ≤ s' →
      Restated.Vocabulary.Execution.Setup.a M S (M.round_of S.hc s') + S.E.Δ ≤ tHi →
      Restated.HeadsBelow M S Sched x B s' := by
  obtain ⟨r₀, rfl⟩ : ∃ r₀ : Round, r = r₀ + 1 :=
    ⟨r - 1, (Nat.succ_pred_eq_of_pos (Restated.round_pos_of_switch facts S tGAT tE gap hgst hlen hr)).symm⟩
  rcases compatible_cases hBT with hBT | hTB
  · intro s' hs' hsb
    by_cases heq : s' = s
    · rw [heq]; exact hB
    have hlt : s < s' := lt_of_le_of_ne hs' (Ne.symm heq)
    have h2 : (M.opening_slot S.hc (r₀ + 1)) + 2 ≤ s' := Nat.succ_le_of_lt (lt_of_le_of_lt hs0 hlt)
    exact Restated.headsBelow_mono facts S Sched x hBT
      (Restated.anchor_ancestorOfHonestHeadsFrom_withoutCatchUp_bounded facts S Sched x tE hexec hmono htd
      tGAT gap hgst hlen hsync hthird hphase tHi hEHi hphaseHi hrsW hmult hcv hcs hcom
      hrec hprev hclear hB' hnW hAW hJswitch
        hr hTW hJ s' h2 hsb)
  · intro s' hs' hsb
    exact Restated.headsBelow_persist_rounds_withoutCatchUp_bounded facts S Sched x tE hexec hmono htd
      tGAT gap hgst hlen hsync hthird hphase tHi hEHi hphaseHi hrsW hmult hcv hcs hcom
      hrec hprev hclear hB' hnW hAW hJswitch s' r₀ n T
      hr hTW hJ hTB s hs0 hs1 hB s' hs' (Nat.le_succ_of_le (facts.gr.le_opening_slot_far S.hc r₀ s')) hsb

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Under its premises on the execution and the phase ending at `tE`, with every validator not held
    awake from `tGAT` up to a time `tHi` at or after `tE`, if the joint invariant holds at a round
    `r₀` at or after the switch round with an anchor that is `T_W` or a descendant of it, slot `s`
    is at least two after round `r₀`'s opening slot, and every honest active member of slot `s`'s
    committee votes for a descendant of `B`, then the same holds at every slot `s'` from `s` on
    whose round has its action instant at or before `tHi`. The twin of
    `ancestorOfHonestHeadsFrom_of_headsBelow_i1`. -/
theorem ancestorOfHonestHeadsFrom_of_headsBelow_bounded (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hsync : Restated.SynchronyFromWake M S x)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (tHi : Int) (hEHi : tE ≤ tHi)
    (hphaseHi : ∀ t : Int, tGAT ≤ t → t ≤ tHi →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE)
    (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hcs : Restated.committeeSleepinessW M S Sched tE)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    (hprev : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.BasePreviousRoundSGCompatibleWithAnchorAtRound M S Sched x v r N
        (Restated.runAllPath M S Sched x v N) T)
    (hclear : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round) (n₀ : Nat),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S r)) →
      Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T)
    (hB' : Restated.BaseJustifiedHighAtSwitchRoundW M S Sched x tGAT tE gap)
    {n_W : Nat} (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    {T_W : NamedBlock V} (hAW : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.switchRound M S tE) T_W)
    (hJswitch : ∀ (v : V) (n₁ : Nat),
      M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) - 1
        ≤ (x[n₁].time : Int) →
      n₁ ≤ n_W → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J T_W.erase)
    {r₀ : Round} {n₀ : Nat} {T₀ : NamedBlock V}
    (hr₀ : Restated.switchRound M S tE ≤ r₀) (hTW₀ : Block.Preceq T_W.erase T₀.erase)
    (hJ₀ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x r₀ n₀ n_W T₀)
    {s : Slot} (hs0 : (M.opening_slot S.hc r₀) + 2 ≤ s)
    {B : Block V} (hB : Restated.HeadsBelow M S Sched x B s) :
    ∀ s' : Slot, s ≤ s' →
      Restated.Vocabulary.Execution.Setup.a M S (M.round_of S.hc s') + S.E.Δ ≤ tHi →
      Restated.HeadsBelow M S Sched x B s' := by
  intro s' hs' hsb
  obtain ⟨k, hk0, hk1⟩ := facts.gr.exists_round_of_slot S.hc r₀ (s := s + 1) (Nat.le_succ_of_le hs0)
  have hsk0 : (M.opening_slot S.hc (r₀ + k)) + 1 ≤ s := Nat.le_of_succ_le_succ hk0
  have hsk1 : s ≤ (M.opening_slot S.hc (r₀ + k + 1)) := Nat.le_of_succ_le_succ hk1
  have hrk : Restated.switchRound M S tE ≤ r₀ + k := le_trans hr₀ (Nat.le_add_right r₀ k)
  -- the chain reaches the round containing `s - 1`, at or before the round containing `s'`
  have hkb : Restated.Vocabulary.Execution.Setup.a M S (r₀ + k) ≤ tHi :=
    Restated.action_le_of_opening_slot_le_bounded facts S (le_trans (Nat.le_of_succ_le hsk0) hs') (le_trans (le_add_of_nonneg_right S.E.Δ_pos.le) hsb)
  obtain ⟨n_k, T_k, hJk, hWk, h2k⟩ := Restated.exists_anchor_chain_secondSlot_withoutCatchUp_bounded facts S Sched x tE hexec hmono htd
      tGAT gap hgst hlen hsync hthird hphase tHi hEHi hphaseHi hrsW hmult hcv hcs hcom
      hrec hprev hclear hB' hnW hAW hJswitch
    hr₀ hTW₀ hJ₀ k hkb
  have hHs : Restated.HeadsBelow M S Sched x T_k.erase s := by
    by_cases hsk : (M.opening_slot S.hc (r₀ + k)) + 2 ≤ s
    · exact Restated.headsBelow_range_ofJoint facts S Sched x tE hexec hmono htd tGAT gap hgst hlen hsync hthird
        hphase hrsW hmult hcv hcs hcom hrec hprev hclear hB' hnW hAW hrk hWk hJk s hsk
        (Nat.le_succ_of_le hsk1)
    · have hseq : s = (M.opening_slot S.hc (r₀ + k)) + 1 :=
        le_antisymm (Nat.le_of_lt_succ (Nat.lt_of_not_le hsk)) hsk0
      have hkpos : 0 < k := by
        rcases Nat.eq_zero_or_pos k with hk | hk
        · subst hk; exact absurd hs0 (by simpa using hsk)
        · exact hk
      rw [hseq]; exact h2k hkpos
  obtain ⟨t', -, ht's, -, hcs'⟩ :=
    Restated.exists_cone_cutoff facts S Sched tE hmono hcom tGAT gap hgst hlen hphase hcs hrk
  have hanchor : t' ≤ slotStart S.E.Δ (s + 1) := le_trans ht's (slotStart_mono S hk0)
  have hpos : 0 < s := Nat.lt_of_lt_of_le (Nat.succ_pos _) hsk0
  have hcomp : Block.compatible B T_k.erase = true :=
    Restated.compatible_of_headsBelow_after facts S Sched x htd hcs' hpos hanchor hB hHs
  exact Restated.ancestorOfHonestHeadsFrom_of_compatible_anchor_withoutCatchUp_bounded facts S Sched x tE hexec hmono htd
      tGAT gap hgst hlen hsync hthird hphase tHi hEHi hphaseHi hrsW hmult hcv hcs hcom
      hrec hprev hclear hB' hnW hAW hJswitch
    hrk hWk hJk hsk0 (Nat.le_succ_of_le hsk1) hcomp hB s' hs' hsb

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Under its premises on the execution and the phase ending at `tE`, with every validator not held
    awake from `tGAT` up to a time `tHi` at or after `tE`, if the joint invariant holds at a round
    `r₀` at or after the switch round with an anchor that is `T_W` or a descendant of it,
    `HonestProposalHeadsAtOwnSlot` holds from slot `s₀` up to `tHi`, slot `s` is at or after both
    `s₀` and two after round `r₀`'s opening slot, its confirmation instant is at or before `tHi`,
    and its proposer, honest up to its vote instant, proposed `B` at a step at or before that
    instant, then every honest active committee member of every slot `s'` from `s` on whose round
    has its action instant at or before `tHi` votes for a descendant of `B`. The twin of
    `honestProposal_ancestorOfHonestHeadsFrom_i1`. -/
theorem honestProposal_ancestorOfHonestHeadsFrom_bounded (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x)
    (tGAT : Int) (gap : Nat)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hsync : Restated.SynchronyFromWake M S x)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (tHi : Int) (hEHi : tE ≤ tHi)
    (hphaseHi : ∀ t : Int, tGAT ≤ t → t ≤ tHi →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t)
    (hrsW : Restated.roundSleepinessW M S Sched tE)
    (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hcs : Restated.committeeSleepinessW M S Sched tE)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    (hprev : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.BasePreviousRoundSGCompatibleWithAnchorAtRound M S Sched x v r N
        (Restated.runAllPath M S Sched x v N) T)
    (hclear : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
      ∀ (v : V) (N : Nat) (blocked : Height) (first i : Nat) (a : NamedAttestation V)
      (ta : Int) (Cfg T Tprev : NamedBlock V) (c0 : Round) (n₀ : Nat),
      (Restated.Vocabulary.Execution.Setup.a M S r) ≤ (x[N].time : Int) → (x[N].time : Int) ≤ tE →
      Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N)
        (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
        (notHeldAt Sched) Finset.univ Finset.univ
        (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0 →
      a.round = r → Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S r)) →
      Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T)
    (hB' : Restated.BaseJustifiedHighAtSwitchRoundW M S Sched x tGAT tE gap)
    {n_W : Nat} (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    {T_W : NamedBlock V} (hAW : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.switchRound M S tE) T_W)
    (hJswitch : ∀ (v : V) (n₁ : Nat),
      M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) - 1
        ≤ (x[n₁].time : Int) →
      n₁ ≤ n_W → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J T_W.erase)
    {r₀ : Round} {n₀ : Nat} {T₀ : NamedBlock V}
    (hr₀ : Restated.switchRound M S tE ≤ r₀) (hTW₀ : Block.Preceq T_W.erase T₀.erase)
    (hJ₀ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x r₀ n₀ n_W T₀)
    {s₀ : Slot} (hadopt : Restated.HonestProposalHeadsAtOwnSlot M S Sched x s₀ tHi)
    {s : Slot} (hs0 : (M.opening_slot S.hc r₀) + 2 ≤ s) (hs₀ : s₀ ≤ s)
    (hct : M.confirmation_time S.E s ≤ tHi)
    (hprop : HonestThroughTime Sched (M.vote_time S.E s) (S.E.proposer s))
    {i : Nat} {B : Block V} (hB : Restated.proposedBlockAtStep M S x i s B)
    (hi : (x[i].time : Int) ≤ M.vote_time S.E s) :
    ∀ s' : Slot, s ≤ s' →
      Restated.Vocabulary.Execution.Setup.a M S (M.round_of S.hc s') + S.E.Δ ≤ tHi →
      Restated.HeadsBelow M S Sched x B s' :=
  Restated.ancestorOfHonestHeadsFrom_of_headsBelow_bounded facts S Sched x tE hexec hmono htd
      tGAT gap hgst hlen hsync hthird hphase tHi hEHi hphaseHi hrsW hmult hcv hcs hcom
      hrec hprev hclear hB' hnW hAW hJswitch
    hr₀ hTW₀ hJ₀ hs0 (hadopt s i B hs₀ hct hprop hB hi)

end

end DecoupledConsensusModel.Sts.Restated
