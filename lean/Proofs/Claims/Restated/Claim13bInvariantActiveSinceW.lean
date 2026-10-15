import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bK_FgJustified
import Proofs.Claims.Restated.Claim13bKit
import Proofs.Claims.Restated.Claim13bPhaseSleepiness
import Proofs.Claims.Restated.Claim13bStepActiveAssembly
import Proofs.Claims.Restated.Claim13bStepActiveSince
import Proofs.Claims.Restated.Claim13bStepAssembly
import Proofs.Claims.Restated.Claim13bStepConeIter
import Proofs.Claims.Restated.Claim13bStepFin
import Proofs.Claims.Restated.Claim13bStepGrade
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bStepKitTick
import Proofs.Claims.Restated.Claim13beRoute3_15
import Proofs.Claims.Restated.Claim13beRoute3_72
import Proofs.Claims.Restated.Claim13beRoute3_75
import Proofs.Claims.Restated.Claim13beRoute3_82
import Proofs.Claims.Restated.Claim13beRoute3_83
import Proofs.Claims.Restated.Constants
import Proofs.Claims.Restated.Projection
import Proofs.Claims.Restated.RunAll
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActiveSince
import Model.Conditions.Claim13bInvariantActiveSinceW
import Model.Conditions.Claim13bInvariantActiveTop
import Model.Conditions.Claim13bK_FgJustified
import Model.Conditions.Claim13bK_FinBeforeTick
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13bStepActiveAssembly
import Model.Conditions.Claim13bStepAnchor
import Model.Conditions.Claim13bStepAssembly
import Model.Conditions.Claim13bStepKitTick
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_72
import Model.Conditions.Claim13beRoute3_74
import Model.Conditions.Claim13beRoute3_82
import Model.Conditions.Claim13beRoute3_83
import Model.Conditions.RunAll
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13bd
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bInvariantActiveSinceW

/-!
# Honest votes and justified blocks after the switch round

Over a model `M : Record.Model V`: the order of the deadline round, the re-based deadline round and
the switch round; a strong window before the re-based deadline round; honest height votes sent by
the switch round name ancestors of the switch round's anchor; and honest justified blocks after the
switch round are ancestors of the round's anchor. The hypotheses `hprev` and `hclear` are read along
the path `Restated.runAllPath M S Sched x v N` that the execution `x` follows.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

local macro "p74% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_74)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p83% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_83)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- `deadlineRoundW S tGAT gap ≤ rebasedDeadlineRoundW S tGAT gap`. -/
theorem deadlineRoundW_le_rebased (facts : Record.Facts M) (S : Setup V) (tGAT : Int) (gap : Nat) :
    Restated.deadlineRoundW M S tGAT gap ≤ Restated.rebasedDeadlineRoundW M S tGAT gap :=
  rebased_nat_le_l0W _ _

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- If `t_GST ≤ tGAT` and `tGAT + healingLengthη S gap ≤ tE`, then
    `rebasedDeadlineRoundW S tGAT gap ≤ switchRound S tE`. -/
theorem rebasedDeadlineRoundW_le_switchRound (facts : Record.Facts M) (S : Setup V) (tGAT tE : Int) (gap : Nat)
    (rho : Record.Run V) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) :
    Restated.rebasedDeadlineRoundW M S tGAT gap ≤ Restated.switchRound M S tE := by
  have hη : Restated.cutBoundW M S tGAT gap + gap ≤ Restated.switchRound M S tE :=
    Restated.hη_of_healingLengthη' facts S tGAT tE gap hgst hlen
  have hs : Restated.deadlineRoundW M S tGAT gap + 2 * (7 * gap + 22 + 4 * S.extraRounds) + 2
      = Restated.cutBoundW M S tGAT gap :=
    Restated.fgSafetyProgressDeadline_add_slack_eq_cutBoundW_l72 facts S rho tGAT gap
  exact rebased_nat_le_switch_l0W _ _ _ _ _ hs hη

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- If `t_GST ≤ tGAT`, `tGAT + healingLengthη S gap ≤ tE` and `strongOpeningsRecurFrom` holds, then
    some round `c₁` with `rD + 2 ≤ c₁` and `c₁ + 1 ≤ rD'` has `MultiProposerAt` at its opening slot,
    and every opening slot proposed in the two periods before that slot has a proposer honest
    through its confirmation instant. -/
theorem exists_strongWindow_before_rebasedDeadlineRoundW (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    {tGAT tE : Int} {gap : Nat} (rho : Record.Run V)
    (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE)
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap) :
    ∃ c₁ : Round, Restated.deadlineRoundW M S tGAT gap + 2 ≤ c₁ ∧
      c₁ + 1 ≤ Restated.rebasedDeadlineRoundW M S tGAT gap ∧
      Restated.MultiProposerAt M S Sched (Restated.interface M S Sched) (Restated.constants M S) ((M.opening_slot S.hc c₁)) ∧
      ∀ s' : Slot, (Restated.interface M S Sched).opening s' →
        (Restated.interface M S Sched).proposalTime ((M.opening_slot S.hc c₁)) - 2 * (Restated.constants M S).period ≤
          (Restated.interface M S Sched).proposalTime s' →
        (Restated.interface M S Sched).proposalTime s' <
          (Restated.interface M S Sched).proposalTime ((M.opening_slot S.hc c₁)) →
        HonestThroughTime Sched (M.confirmation_time S.E s')
          ((Restated.interface M S Sched).proposer s') := by
  have hrW : Restated.rebasedDeadlineRoundW M S tGAT gap ≤ Restated.switchRound M S tE :=
    Restated.rebasedDeadlineRoundW_le_switchRound facts S tGAT tE gap rho hgst hlen
  have hrDW : Restated.deadlineRoundW M S tGAT gap ≤ Restated.switchRound M S tE :=
    (Restated.deadlineRoundW_le_rebased facts S tGAT gap).trans hrW
  obtain ⟨hlo0, -⟩ := Restated.window_in_phase_atRound facts S tGAT tE gap hgst hlen le_rfl hrDW
  obtain ⟨-, hWE⟩ := Restated.switchRound_window_in_phase facts S tGAT tE gap hgst hlen
  have hgW : Restated.deadlineRoundW M S tGAT gap + gap ≤ Restated.switchRound M S tE :=
    rebased_nat_gap_l0W _ _ _ hrW
  have hmonoA : (Restated.Vocabulary.Execution.Setup.a M S (Restated.deadlineRoundW M S tGAT gap + gap)) ≤ (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)) :=
    (Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone hgW
  have hper : (Restated.constants M S).period = 4 * S.E.Δ * (S.hc.R : Int) := Restated.period_eq facts S
  have hwa : wAttest S = 4 * (S.hc.R : Int) * S.E.Δ := rfl
  have hΔ := S.E.Δ_pos
  have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
  have hP : (0 : Int) < 4 * S.E.Δ * (S.hc.R : Int) := by positivity
  have hpa : ∀ r : Round, M.proposal_time S.E ((M.opening_slot S.hc r)) + 6 * S.E.Δ = (Restated.Vocabulary.Execution.Setup.a M S r) := by
    intro r
    rw [← facts.sch.Γ_0_eq_proposal_time S.hc S.E r,
      facts.sch.slotStart_add_six_delta_eq_confirmation_time]
    exact Restated.confirmation_time_opening_slot facts S r
  have hpadd : ∀ r m : Round, M.proposal_time S.E ((M.opening_slot S.hc (r + m)))
      = M.proposal_time S.E ((M.opening_slot S.hc r)) + (m : Int) * (Restated.constants M S).period := by
    intro r m
    have h1 := hpa (r + m)
    have h2 := hpa r
    have h3 := Restated.action_add_eq_add_period_mul facts S r m
    linarith
  have hpos : (0 : Int) < (Restated.constants M S).period := (Restated.constants_holds facts S).period_pos
  have hstart :
      tGAT ≤ M.proposal_time S.E ((M.opening_slot S.hc (Restated.deadlineRoundW M S tGAT gap))) := by
    have h1 := hpa (Restated.deadlineRoundW M S tGAT gap)
    rw [hwa] at hlo0
    nlinarith
  have hwin : M.proposal_time S.E ((M.opening_slot S.hc (Restated.deadlineRoundW M S tGAT gap)))
      + (gap : Int) * (Restated.constants M S).period ≤ tE := by
    have h1 := hpadd (Restated.deadlineRoundW M S tGAT gap) gap
    have h2 := hpa (Restated.deadlineRoundW M S tGAT gap + gap)
    linarith
  obtain ⟨s, hlo, hhi, hmp, hprevs⟩ := hrec _ hstart hwin
  obtain ⟨c₁, rfl⟩ := hmp.1
  refine ⟨c₁, ?_, ?_, hmp, hprevs⟩
  · change M.proposal_time S.E ((M.opening_slot S.hc (Restated.deadlineRoundW M S tGAT gap)))
        + 2 * (Restated.constants M S).period ≤ M.proposal_time S.E ((M.opening_slot S.hc c₁)) at hlo
    by_contra hc
    have hc' : c₁ ≤ Restated.deadlineRoundW M S tGAT gap + 1 := Nat.le_of_lt_succ (Nat.lt_of_not_le hc)
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hc'
    have h1 := hpadd c₁ k
    have h2 := hpadd (Restated.deadlineRoundW M S tGAT gap) 1
    rw [← hk] at h1
    have hk0 : (0 : Int) ≤ (k : Int) := by positivity
    push_cast at h2
    nlinarith
  · change M.proposal_time S.E ((M.opening_slot S.hc c₁)) ≤
        M.proposal_time S.E ((M.opening_slot S.hc (Restated.deadlineRoundW M S tGAT gap)))
          + (gap : Int) * (Restated.constants M S).period at hhi
    have hc : c₁ ≤ Restated.deadlineRoundW M S tGAT gap + gap := by
      by_contra hc
      have hc' : Restated.deadlineRoundW M S tGAT gap + gap + 1 ≤ c₁ := Nat.lt_of_not_le hc
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hc'
      have h1 := hpadd (Restated.deadlineRoundW M S tGAT gap + gap + 1) k
      have h2 := hpadd (Restated.deadlineRoundW M S tGAT gap) (gap + 1)
      rw [← hk] at h1
      rw [← Nat.add_assoc] at h2
      have hk0 : (0 : Int) ≤ (k : Int) := by positivity
      push_cast at h2
      nlinarith
    exact rebased_nat_window_l0W _ _ _ hc

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- With `hprev` and `hclear` assumed only at rounds from `r₀` to the switch round, along the path
    of `R_N` that `x` follows: if `rD ≤ r₀ ≤ rW`, `T_0` is a round-`r₀` anchor, `T_W` a switch-round
    anchor and `n_W` the switch round's tick step, then every non-empty height vote authored and
    signed up to step `n_W + 1` by a validator honest through its send, at a height at least
    `h(T_0)`, names an ancestor of `T_W`. -/
theorem honestVotes_onAnchorChain_since_roundW (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    {tGAT tE : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWake M S x) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (htd : Restated.TimeDiverges M x)
    {r₀ : Round} (hr₀ : Restated.deadlineRoundW M S tGAT gap ≤ r₀) (hr₀W : r₀ ≤ Restated.switchRound M S tE)
    (hprev : ∀ r : Round, r₀ ≤ r → r ≤ Restated.switchRound M S tE →
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
    (hclear : ∀ r : Round, r₀ ≤ r → r ≤ Restated.switchRound M S tE →
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
    {T_0 T_W : NamedBlock V}
    (hA0 : Restated.AnchorAtRound M S Sched x tGAT tE r₀ T_0)
    (hAW : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.switchRound M S tE) T_W)
    {n_W : Nat} (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)))) :
    ∀ (v' : V) (n' : Nat) (b : NamedAttestation V) (h' : Height) (entry : BlockId) (tmo : Bool),
      n' ≤ n_W + 1 → Restated.HonestThrough M Sched x n' v' → b.val_index = v' →
      (⟨v', NamedObject.attest b⟩ : SignedMsg V (NamedObject V)) ∈ x[n'].sent →
      b.height_pair = NamedHeightPair.vote h' entry tmo →
      (M.derive_named S.E S.cfg T_0).h ≤ h' →
      ∀ C : NamedBlock V, Restated.blockInLog M S Sched x C → C.root = entry →
      Block.Preceq C.erase T_W.erase := by
  intro v' n' b h' entry tmo hn' hv' hidx hsent hpair hlo C hC hCroot
  subst hidx
  have hunf := hvalid.toUnforgeability
  have hthr : HonestThroughTime Sched (x[n'].time : Int) b.val_index := hv'
  -- the vote is its signer's round action attestation, sent at the round's tick step `k`; its
  -- list is in the sent log after the step
  obtain ⟨k, hkn', τ, hlbl, haw, hdvd, out, hout, hst, hmemout⟩ :=
    Restated.tick_of_honest_signed_upTo_taken facts S Sched x b.val_index (NamedObject.attest b)
      (x[n'].time : Int) hthr hunf (by rw [author_attest]) n' le_rfl hsent
  have hsentk : (⟨b.val_index, NamedObject.attest b⟩ : SignedMsg V (NamedObject V)) ∈ x[k + 1].sent :=
    Restated.mem_sent_of_tick_of_state facts S Sched x hlbl haw hdvd
      (facts.nd.tick_send_eq_of_state (Setup.alwaysAwake S) b.val_index _ (τ : Int)) hout hst hmemout
  obtain ⟨Wr, hWr, hemits⟩ :=
    Restated.emits_runAll_of_tick facts S Sched x b.val_index hkn' hlbl haw hdvd hout hmemout
  obtain ⟨-, hτ0⟩ :=
    Restated.Vocabulary.Proofs.Optimistic.emits_attest_shape facts (Setup.alwaysAwake S) Wr hWr hemits
  have hτ : (τ : Int) = (Restated.Vocabulary.Execution.Setup.a M S b.round) := hτ0
  have hk : Restated.tickStepAt M x k ((Restated.Vocabulary.Execution.Setup.a M S b.round)) :=
    ⟨τ, hlbl, hτ⟩
  rw [hτ] at hout haw
  -- a node state `n` of the signer's round action read staged from its node state at step `k`,
  -- and an outcome `D` of its attestation duty there: the vote is `D`'s attestation
  obtain ⟨n, hnk⟩ := (p74% actionReadFrom_nonempty₇₄) facts (Setup.alwaysAwake S)
    (x[k][b.val_index].st) b.round
  obtain ⟨D, hD⟩ := facts.dt.attest_with_nonempty (M.gradeContract n.cache) (Setup.alwaysAwake S).E
    (Setup.alwaysAwake S).hc ((Setup.alwaysAwake S).node b.val_index) n.st n.record
  have _hr_s1 := Record.reachedNode_wakeStage facts S Sched x (k) b.val_index (Restated.Vocabulary.Execution.Setup.a M S b.round)
  have _hv_s2 := Record.runs_as_wakeStage facts S Sched x (k) b.val_index (Restated.Vocabulary.Execution.Setup.a M S b.round)
  have hbD : b = D.2.2 :=
    Restated.attest_of_tick_eq facts S b.val_index _ b.round hout hmemout D.2.2
      (by
        rw [Restated.actionAttestationFrom_wakeStage facts _ Sched _ x[k] b.val_index b.round]
        exact ⟨n, hnk, D.1, D.2.1, hD⟩)
  have hkhon : Restated.HonestThrough M Sched x (k + 1) b.val_index := fun t ht =>
    hv' t (ht.trans (Restated.time_mono_int facts S Sched x (Nat.succ_le_of_lt hkn')))
  obtain ⟨hk1, hk0⟩ := Restated.tickStepAt_time facts x hk
  obtain ⟨hnW1, -⟩ := Restated.tickStepAt_time facts x hnW
  have hρW : b.round ≤ Restated.switchRound M S tE := by
    apply (Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).le_iff_le.mp
    rw [← hk1, ← hnW1]
    exact Restated.time_mono_int facts S Sched x (by omega)
  by_cases hρ0 : r₀ ≤ b.round
  · -- from the round `r₀` on: `hprev` and `hclear` at the vote's round
    have hρD : Restated.deadlineRoundW M S tGAT gap ≤ b.round := hr₀.trans hρ0
    obtain ⟨Tρ, hAρ⟩ := Restated.exists_anchorAtRound facts S Sched x hsync hmono hawake hgst hcv hvalid hawm
      hthird hcom hrec hlen htd hρD hρW
    have hnot : (⟨b.val_index, NamedObject.attest b⟩ : SignedMsg V (NamedObject V)) ∉ x[k].sent := by
      intro hmem
      obtain ⟨-, k', hk'k, hk', -⟩ := Restated.attest_round_of_sent facts S Sched x hthr hunf rfl
        (Restated.time_mono_int facts S Sched x (le_of_lt hkn')) hmem
      have hkk := Restated.tickStepAt_unique facts x hk' hk
      omega
    have hh'ρ : h' ≤ (M.derive_named S.E S.cfg Tρ).h := by
      rw [Restated.anchorAtRound_height facts S Sched x hsync hmono hawake hgst hcv hvalid hawm hthird
        hAρ hk]
      exact Restated.honestRow_le_topHonestRow facts S Sched x hunf (n₀ := k)
        ⟨b.val_index, k + 1, b, entry, tmo, le_rfl, hkhon, rfl, hsentk, hpair⟩
    have hCρ := Restated.targetsSince_of_anchorAtRound facts S Sched x hsync hmono hawake hgst hcv hvalid hawm
      hthird hcom hlen hρD hρW (hprev _ hρ0 hρW) (hclear _ hρ0 hρW) hAρ k hk b.val_index (k + 1) b h'
      entry tmo le_rfl hkhon rfl hsentk hnot hpair hh'ρ C hC hCroot
    exact preceq_trans_Preceq hCρ
      (Restated.anchorAtRound_preceq_of_le facts S Sched x hsync hmono hawake hgst hcv hvalid hawm hthird hcom
        hrec hlen htd hρD hρW le_rfl hAρ hAW)
  · -- before the round `r₀`: the clause `targetsTop` of the round-`r₀` anchor
    have hlt : (Restated.Vocabulary.Execution.Setup.a M S b.round) < (Restated.Vocabulary.Execution.Setup.a M S r₀) :=
      (Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S) (Nat.lt_of_not_le hρ0)
    obtain ⟨v0, N0, n0, blocked0, first0, i0, a0, ta0, Cfg0, Tprev0, c00, hn0, hN0lo, hN0hi,
      hreg0, -, -⟩ := id hA0
    obtain ⟨hn01, -⟩ := Restated.tickStepAt_time facts x hn0
    have hkn0 : k + 1 ≤ n0 + 1 := by
      by_contra hcon
      have hmn : ((x[n0 + 1].time : Nat) : Int) ≤ ((x[k].time : Nat) : Int) := by
        exact_mod_cast Restated.time_mono facts S Sched x (by omega)
      linarith
    have hh'0 : h' ≤ (M.derive_named S.E S.cfg T_0).h := by
      rw [Restated.anchorAtRound_height facts S Sched x hsync hmono hawake hgst hcv hvalid hawm hthird
        hA0 hn0]
      exact Restated.honestRow_le_topHonestRow facts S Sched x hunf (n₀ := n0)
        ⟨b.val_index, k + 1, b, entry, tmo, hkn0, hkhon, rfl, hsentk, hpair⟩
    have hheq : h' = (M.derive_named S.E S.cfg T_0).h := le_antisymm hh'0 hlo
    rw [hheq] at hpair
    have hC0 := Restated.targetsTop_atRound facts S Sched x v0 hsync hmono hawake hgst hcv hvalid hawm hthird hcom
      hN0lo hN0hi hreg0 hn0 b.val_index (k + 1) b entry tmo hkn0 hkhon rfl hsentk hpair C hC hCroot
    exact preceq_trans_Preceq hC0
      (Restated.anchorAtRound_preceq_of_le facts S Sched x hsync hmono hawake hgst hcv hvalid hawm hthird hcom
        hrec hlen htd hr₀ hr₀W le_rfl hA0 hAW)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- With `hprev` and `hclear` assumed only at rounds from `rD'` to the switch round, along the path
    of `R_N` that `x` follows: if `T_W` is a switch-round anchor, `n_W` the switch round's tick
    step, round `r` at or after the switch round, the invariant holds at round `r` with tick step
    `n`, switch step `n_W` and anchor `T`, `T_W ⪯ T`, and step `n'` is the sts tick at
    `S.a (r + 1)`, then the justified block of every validator honest through its own state, at any
    step from `n_W` up to `n' + 1`, is an ancestor of `T`. -/
theorem justified_preceq_anchor_after_switchW (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
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
    (hrsW : Restated.roundSleepinessW M S Sched tE)
    (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
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
    {T_W : NamedBlock V} (hAW : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.switchRound M S tE) T_W)
    {n_W : Nat} (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    {r : Round} {n n' : Nat} {T : NamedBlock V}
    (hr : Restated.switchRound M S tE ≤ r)
    (hinv : Restated.AfterPhaseInvariantOverActiveSetsSince M S Sched x r n n_W T)
    (hTW : Block.Preceq T_W.erase T.erase)
    (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1)))) :
    ∀ (v : V) (n₁ : Nat), n_W ≤ n₁ → n₁ ≤ n' + 1 → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J T.erase := by
  classical
  intro v n₁ hWn₁ hn₁ hv
  have hrsW' := Restated.roundSleepinessW_switchOpening_of_phase facts S Sched tGAT tE gap hgst hlen hmono
    hthird hphase hrsW
  have htE' := Restated.switchOpening_le_opening facts S (le_trans hr (Nat.le_succ r))
  rcases Restated.justified_honest_vote_before_succ_tick facts S Sched x hexec hmono hrsW' hn' htE' hn₁ hv with
    hgen | ⟨Jn, v', a, k, hJnmem, hJne, hkn', hktick, hround, hqhon, hidx, hsent, hpair⟩
  · rw [hgen]
    exact (preceq_eq_true_iff_Preceq.mp (Protocol.preceq_genesis _))
  · rw [← hJne]
    have hJnlog : Restated.blockInLog M S Sched x Jn := Restated.blockInLog_of_mem_bodies facts S Sched hv hJnmem
    have hkn : k ≤ n := Restated.tick_le_of_round_le facts S Sched x hktick hinv.tick hround
    have hstep : k + 1 ≤ n + 1 := Nat.succ_le_succ hkn
    have hqk : Restated.HonestThrough M Sched x (k + 1) v' := fun t ht =>
      hqhon t (le_trans ht (Restated.time_mono_int facts S Sched x (Nat.succ_le_succ (Nat.le_of_lt hkn'))))
    by_cases hW : (⟨v', NamedObject.attest a⟩ : SignedMsg V (NamedObject V)) ∈ x[n_W].sent
    · -- a vote sent by the switch round's tick step: the anchor chain from round `rD'`
      have hrDW' : Restated.rebasedDeadlineRoundW M S tGAT gap ≤ Restated.switchRound M S tE :=
        Restated.rebasedDeadlineRoundW_le_switchRound facts S tGAT tE gap (Restated.runAll M S Sched x v 0) hgst hlen
      obtain ⟨T_D', hAD'⟩ := Restated.exists_anchorAtRound facts S Sched x hsync hmono hphase hgst hcv hexec
        hmult hthird hcom hrec hlen htd (Restated.deadlineRoundW_le_rebased facts S tGAT gap) hrDW'
      have hnWn : n_W ≤ n := Restated.tick_le_of_round_le facts S Sched x hnW hinv.tick hr
      have hnn' : n + 1 ≤ n' := Restated.tick_succ_le_tick_succ_round facts S Sched x hinv.tick hn'
      have hqW : Restated.HonestThrough M Sched x n_W v' := fun t ht =>
        hqhon t (le_trans ht (Restated.time_mono_int facts S Sched x (by omega)))
      have hvW : Restated.HonestThrough M Sched x n_W v := fun t ht =>
        hv t (le_trans ht (Restated.time_mono_int facts S Sched x hWn₁))
      have hlo : (M.derive_named S.E S.cfg T_D').h ≤ (x[n₁][v].st).st.core.h_j :=
        le_trans (hB' T_D' hAD' n_W hnW v hvW) (Restated.h_j_mono_sts facts S Sched x v hWn₁)
      exact preceq_trans_Preceq
        (Restated.honestVotes_onAnchorChain_since_roundW facts S Sched x hsync hmono hphase hgst hcv hexec
          hmult hthird hcom hrec hlen htd (Restated.deadlineRoundW_le_rebased facts S tGAT gap) hrDW' hprev
          hclear hAD' hAW hnW v' n_W a _ Jn.root false
          (Nat.le_succ n_W) hqW hidx hW hpair hlo Jn hJnlog rfl)
        hTW
    · -- a vote first sent after the switch round's tick step: the round-`r` clauses
      have hh := hinv.heightCeiling v' (k + 1) a _ Jn.root false hstep hqk hidx hsent hpair
      exact hinv.targetsSince v' (k + 1) a _ Jn.root false hstep hqk hidx hsent hW hpair hh Jn
        hJnlog rfl

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingLemmas
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

end

end DecoupledConsensusModel.Sts.Restated
