import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bK_ConfirmedInclusionBounded
import Proofs.Claims.Restated.Claim13bK_ProposalAdoption

/-!
# Honest proposals' heads with no catch-up premise, up to a time `tHi`

The twin of `honestProposal_ancestorOfHonestHeadsFrom_i1b`
(`lean/Proofs/Claims/Restated/Claim13bK_ProposalAdoption.lean`) whose conclusion holds only at the
slots whose round has its action instant at or before `tHi`, proved through the bounded twins of
`lean/Proofs/Claims/Restated/Claim13bK_ConfirmedInclusionBounded.lean`. Stated over a model
`M : Record.Model V` and its facts.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Under its premises on the execution and the phase ending at `tE`, with every validator not held
    awake from `tGAT` up to a time `tHi` at or after `tE`, fewer than a third of the weight held at
    every time up to `tHi`, and strong openings recurring up to `tHi`: if the joint invariant holds
    at a round `r₀` at or after the switch round with an anchor that is `T_W` or a descendant of it,
    slot `s` is at least two after round `r₀`'s opening slot with its confirmation instant at or
    before `tHi`, and `s`'s proposer, not held up to `s`'s vote instant, sent `B` by that instant,
    then every honest active member of the committee of every slot `s'` from `s` on whose round has
    its action instant at or before `tHi` votes for a descendant of `B`. The twin of
    `honestProposal_ancestorOfHonestHeadsFrom_i1b`. -/
theorem honestProposal_ancestorOfHonestHeadsFrom_fromSwitch_bounded (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
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
    (hthirdHi : ∀ t : Int, t ≤ tHi →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hrecHi : Restated.strongOpeningsRecurFrom M S Sched tGAT tHi gap)
    {s : Slot} (hs0 : (M.opening_slot S.hc r₀) + 2 ≤ s)
    (hct : M.confirmation_time S.E s ≤ tHi)
    (hprop : HonestThroughTime Sched (M.vote_time S.E s) (S.E.proposer s))
    {i : Nat} {B : Block V} (hB : Restated.proposedBlockAtStep M S x i s B)
    (hi : (x[i].time : Int) ≤ M.vote_time S.E s) :
    ∀ s' : Slot, s ≤ s' →
      Restated.Vocabulary.Execution.Setup.a M S (M.round_of S.hc s') + S.E.Δ ≤ tHi →
      Restated.HeadsBelow M S Sched x B s' := by
  have hadopt := Restated.honestProposalHeadsAtOwnSlot_fromSwitch_i1b facts S Sched x hsync hmono hphaseHi hgst
    hcv hexec hmult hthirdHi hcom hrecHi hlen hrec
  have hs₀ : (M.opening_slot S.hc (Restated.switchRound M S tE)) ≤ s :=
    (facts.gr.opening_slot_mono S hr₀).trans ((Nat.le_add_right _ 2).trans hs0)
  exact Restated.honestProposal_ancestorOfHonestHeadsFrom_bounded facts S Sched x tE hexec hmono htd
    tGAT gap hgst hlen hsync hthird hphase tHi hEHi hphaseHi hrsW hmult hcv hcs hcom
    hrec hprev hclear hB' hnW hAW hJswitch
    hr₀ hTW₀ hJ₀ hadopt hs0 hs₀ hct hprop hB hi

end

end DecoupledConsensusModel.Sts.Restated
