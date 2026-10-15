import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bInvariantActiveSince
import Proofs.Claims.Restated.Claim13bK_ConfirmedRecord
import Proofs.Claims.Restated.Claim13bK_ConfirmedSettleUpTo
import Proofs.Claims.Restated.Claim13bK_Frame
import Proofs.Claims.Restated.Claim13bK_HeadsPersistUpTo
import Proofs.Claims.Restated.Claim13bK_LiveConfirmedSlotsUpTo
import Proofs.Claims.Restated.Claim13bK_PrevHeadsStep
import Proofs.Claims.Restated.Claim13bStepConeIter
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bStepKitTick
import Proofs.Claims.Restated.Claim13bW_Schedule
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActive
import Model.Conditions.Claim13bInvariantActiveJoint
import Model.Conditions.Claim13bInvariantActiveSinceW
import Model.Conditions.Claim13bK_ConfirmedRecordUpTo
import Model.Conditions.Claim13bK_Frame
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13bStepCone
import Model.Conditions.Claim13bStepConeIter
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_74
import Model.Conditions.Claim13beRoute3_83
import Model.Conditions.ClaimAsyncK_DeliveryUpTo
import Model.Conditions.RunAll
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13bd
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_Grades_Main
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bK_ConfirmedRecordUpTo

/-!
# The confirmation records after the phase, up to a slot

The joint invariant at later rounds, and the stable root, the finalized block and the two outputs as
ancestors of the honest heads of the slots up to `sEnd`, with synchrony assumed only up to a bound
`b₀`, with the slot and bound arithmetic they use. Stated over a model `M : Record.Model V` and its
facts.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

local macro "p83% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_83)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog

/-- Synchrony from wake up to `b'` gives synchrony from wake up to every `b ≤ b'`. -/
private theorem SynchronyFromWakeBefore.monoU {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (Record.protocolOf M S) Sched} {b b' : Int}
    (hs : Restated.SynchronyFromWakeBefore M S x b') (facts : Record.Facts M) (hb : b ≤ b') :
    Restated.SynchronyFromWakeBefore M S x b :=
  fun k w sm hsend hle haw => hs k w sm hsend (le_trans hle hb) haw

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- `RecordsAncestorOfHonestHeadsTo` up to `sEnd` gives it up to every `sEnd' ≤ sEnd`. -/
theorem RecordsAncestorOfHonestHeadsTo.mono_end (facts : Record.Facts M) {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (Record.protocolOf M S) Sched} {v : V} {k : Nat} {sEnd sEnd' : Slot}
    (hle : sEnd' ≤ sEnd) (h : Restated.RecordsAncestorOfHonestHeadsTo M S Sched x v k sEnd) :
    Restated.RecordsAncestorOfHonestHeadsTo M S Sched x v k sEnd' :=
  ⟨h.1.mono_end facts hle, h.2.mono_end facts hle⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If `sEnd < s`, `AncestorOfHonestHeadsFromTo` holds for every block over the empty range of slots
    from `s` to `sEnd`. -/
theorem ancestorOfHonestHeadsFromTo_of_lt (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {B : Block V} {s sEnd : Slot} (h : sEnd < s) :
    Restated.AncestorOfHonestHeadsFromTo M S Sched x B s sEnd :=
  fun _ h1 h2 => absurd (le_trans h1 h2) (Nat.not_le.2 h)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If `ρ ≤ round_of (sEnd − 2)`, then
    `max tE (S.a ρ + Δ) ≤ max tE (S.a (round_of (sEnd − 2) + 1))`. -/
theorem anchorBound_le_headsBound (facts : Record.Facts M) (S : Setup V) (tE : Int) {ρ : Round} {sEnd : Slot}
    (h : ρ ≤ (M.round_of S.hc (sEnd - 2))) :
    max tE ((Restated.Vocabulary.Execution.Setup.a M S ρ) + S.E.Δ) ≤ max tE ((Restated.Vocabulary.Execution.Setup.a M S ((M.round_of S.hc (sEnd - 2)) + 1))) :=
  max_le_max le_rfl (le_trans (Restated.action_add_delta_le_succ facts S ρ) (Restated.action_mono facts S (Nat.succ_le_succ h)))

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If `s + 2 ≤ sEnd`, then `round_of s ≤ round_of (sEnd − 2)`. -/
theorem round_of_le_round_of_sub_two (facts : Record.Facts M) (S : Setup V) {s sEnd : Slot} (h : s + 2 ≤ sEnd) :
    (M.round_of S.hc s) ≤ (M.round_of S.hc (sEnd - 2)) :=
  facts.gr.round_of_mono_sts S.hc (nat_le_sub_two_of_add_two_8b h)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Under its premises on the execution and the phase ending at `tE`, with synchrony up to `b₀`
    where `max tE (S.a r + Δ) ≤ b₀`: if the joint invariant holds at a round `r₀` at or after the
    switch round with an anchor `T₀` that is `T_W` or a descendant of it, and `r₀ ≤ r`, then it
    holds at round `r` with some tick step and some anchor that is a descendant of both `T₀` and
    `T_W`. -/
theorem anchor_at_later_round_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) {b₀ : Int} (hsync : Restated.SynchronyFromWakeBefore M S x b₀) (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight) (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t) (hrsW : Restated.roundSleepinessW M S Sched tE) (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT) (hcs : Restated.committeeSleepinessW M S Sched tE) (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched)) (hw : Restated.WakesAtActionInstants M S Sched) (hs : Restated.SleepsAfterActionInstants M S Sched) (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap) (hprev : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
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
        (Restated.runAllPath M S Sched x v N) T) (hclear : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
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
      Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T) (hB' : Restated.BaseJustifiedHighAtSwitchRoundW M S Sched x tGAT tE gap) {n_W : Nat} (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)))) {T_W : NamedBlock V} (hAW : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.switchRound M S tE) T_W) (hJswitch : ∀ (v : V) (n₁ : Nat),
      M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) - 1
        ≤ (x[n₁].time : Int) →
      n₁ ≤ n_W → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J T_W.erase)
    {r₀ : Round} {n₀ : Nat} {T₀ : NamedBlock V}
    (hr₀ : Restated.switchRound M S tE ≤ r₀) (hTW₀ : Block.Preceq T_W.erase T₀.erase)
    (hJ₀ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x r₀ n₀ n_W T₀)
    {r : Round} (hr : r₀ ≤ r) (hb₀ : max tE ((Restated.Vocabulary.Execution.Setup.a M S r) + S.E.Δ) ≤ b₀) :
    ∃ (n : Nat) (T : NamedBlock V),
      Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x r n n_W T ∧
        Block.Preceq T₀.erase T.erase ∧ Block.Preceq T_W.erase T.erase := by
  obtain ⟨n, T, hJ, h1, h2⟩ := Restated.exists_anchor_chain_upTo facts S Sched x tE hexec hmono htd
    tGAT gap hgst hlen (r := r₀) (kEnd := r - r₀)
    (hsync.monoU facts (by rw [Nat.add_sub_cancel' hr]; exact hb₀)) hthird hphase hrsW hmult hcv hcs hcom
    hw hs hrec hprev hclear hB' hnW hAW hJswitch hr₀ hTW₀ hJ₀ (r - r₀) le_rfl
  rw [Nat.add_sub_cancel' hr] at hJ
  exact ⟨n, T, hJ, h1, h2⟩

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Under its premises on the execution and the phase ending at `tE`, with synchrony up to `b₀`
    where `max tE (S.a (round_of (sEnd − 2) + 1)) ≤ b₀`, and the joint invariant at a round `r₀` at
    or after the switch round for an anchor that is `T_W` or a descendant of it: if slot `s` is at
    least two after round `r₀`'s opening slot, `m` is the tick step at slot `s`'s confirmation
    instant, `v` is in `HonRound` of the round of `s + 1` and honest through that instant, `c` is an
    outcome of `v`'s phase tick there, and `some G` is an outcome of the stable root of `c`'s grade
    contract at the clock-stamped store's round, then `G` is an ancestor of every honest head of the
    slots from `s + 3` to `sEnd`. -/
theorem stableRoot_ancestorOfHonestHeadsFrom_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) {b₀ : Int} (hsync : Restated.SynchronyFromWakeBefore M S x b₀) (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight) (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t) (hrsW : Restated.roundSleepinessW M S Sched tE) (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT) (hcs : Restated.committeeSleepinessW M S Sched tE) (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched)) (hw : Restated.WakesAtActionInstants M S Sched) (hs : Restated.SleepsAfterActionInstants M S Sched) (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap) (hprev : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
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
        (Restated.runAllPath M S Sched x v N) T) (hclear : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
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
      Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T) (hB' : Restated.BaseJustifiedHighAtSwitchRoundW M S Sched x tGAT tE gap) {n_W : Nat} (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)))) {T_W : NamedBlock V} (hAW : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.switchRound M S tE) T_W) (hJswitch : ∀ (v : V) (n₁ : Nat),
      M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) - 1
        ≤ (x[n₁].time : Int) →
      n₁ ≤ n_W → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J T_W.erase) {sEnd : Slot}
    {r₀ : Round} {n₀ : Nat} {T₀ : NamedBlock V}
    (hr₀ : Restated.switchRound M S tE ≤ r₀) (hTW₀ : Block.Preceq T_W.erase T₀.erase)
    (hJ₀ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x r₀ n₀ n_W T₀)
    {s : Slot} (hs0 : (M.opening_slot S.hc r₀) + 2 ≤ s)
    {m : Nat} (hm : Restated.tickStepAt M x m (M.confirmation_time S.E s)) {v : V}
    (hvR : v ∈ Restated.HonRound M S Sched ((M.round_of S.hc (s + 1))))
    (hvh : HonestThroughTime Sched (M.confirmation_time S.E s) v)
    {G : Block V} {c : M.Cache}
    (hc : M.onPhaseTick S.E S.hc (M.toHealing (x[m][v].st).st.core)
        (M.confirmation_time S.E s) (x[m][v].st).cache ⇢ c)
    (hG : (M.gradeContract c).stableRoot S.E S.hc
          (M.toHealing (M.ns_setClock S.E (x[m][v].st).st
            (M.confirmation_time S.E s)).core)
          ((M.round_of S.hc) (M.ns_setClock S.E (x[m][v].st).st
            (M.confirmation_time S.E s)).core.s) ⇢ some G)
    (hb₀ : max tE ((Restated.Vocabulary.Execution.Setup.a M S ((M.round_of S.hc (sEnd - 2)) + 1))) ≤ b₀) :
    Restated.AncestorOfHonestHeadsFromTo M S Sched x G (s + 3) sEnd := by
  by_cases hE : s + 3 ≤ sEnd
  swap
  · exact Restated.ancestorOfHonestHeadsFromTo_of_lt facts S Sched x (Nat.lt_of_not_le hE)
  have hsE : Restated.SynchronyFromWakeBefore M S x tE := hsync.monoU facts (le_trans (le_max_left _ _) hb₀)
  have hR0 : (M.round_of S.hc s) ≤ (M.round_of S.hc (sEnd - 2)) :=
    Restated.round_of_le_round_of_sub_two facts S (le_trans (Nat.le_succ _) hE)
  have hR1 : (M.round_of S.hc (s + 1)) ≤ (M.round_of S.hc (sEnd - 2)) :=
    Restated.round_of_le_round_of_sub_two facts S hE
  have hslot : (M.ns_setClock S.E (x[m][v].st).st
      (M.confirmation_time S.E s)).core.s = s + 1 := by
    rw [facts.hd.Sts_setClock_core_s]; exact facts.sch.Optimistic_slotOf_confirmation_time S.E s
  have hG := (facts.nd.gradeContract_stableRoot _ _ _ _ _ _).1 hG
  rw [hslot] at hG
  rcases facts.gr.frameStableRoot_cases _ _ _ _ _ _ hG rfl with hroot | ⟨root, hg2, hGroot⟩
  · -- the fork-choice root
    obtain ⟨hm1, hm0⟩ := Restated.tickStepAt_time facts x hm
    have hvm : Restated.HonestThrough M Sched x m v := fun t ht => hvh t (by linarith)
    have hrs0 := facts.gr.opening_slot_round_of_le_slot S.hc s
    have hrs1 := facts.gr.lt_opening_slot_round_of_succ S.hc s
    have hrr : r₀ ≤ (M.round_of S.hc s) := by
      by_contra hcon
      exact nat_lt_absurd_c3 hs0 hrs1
        (facts.gr.opening_slot_mono S (Nat.succ_le_of_lt (Nat.lt_of_not_le hcon)))
    obtain ⟨n, T, hJ, -, hTW⟩ := Restated.anchor_at_later_round_upTo facts S Sched x tE hexec hmono htd
      tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec hprev hclear hB'
      hnW hAW hJswitch hr₀ hTW₀ hJ₀ hrr (le_trans (Restated.anchorBound_le_headsBound facts S tE hR0) hb₀)
    have hr : Restated.switchRound M S tE ≤ (M.round_of S.hc s) := le_trans hr₀ hrr
    have hroot' : Block.Preceq (Restated.Vocabulary.Protocol.confRoot M (Restated.confStoreAt M S (x[m][v].st) s)) T.erase :=
      Restated.confRoot_preceq_anchor_atSlot_upTo facts S Sched x tE hexec hmono htd tGAT gap hgst hlen hsE
        hthird hphase hrsW hmult hcv hcom hrec hprev hclear hB' hnW hAW hr hTW hJ hrs0
        (Nat.le_of_lt hrs1) hm hvm
    have hGT : Block.Preceq G T.erase := by rw [hroot]; exact hroot'
    have hanc := Restated.anchor_ancestorOfHonestHeadsFrom_upTo facts S Sched x tE hexec hmono htd tGAT gap
      hgst hlen (hsync.monoU facts hb₀) hthird hphase hrsW hmult hcv hcs hcom hw hs hrec hprev hclear
      hB' hnW hAW hJswitch hr hTW hJ
    exact Restated.ancestorOfHonestHeadsFrom_mono_upTo facts S Sched x (nat_le_add3_c3 hrs0)
      (Restated.ancestorOfHonestHeadsFrom_of_preceq_upTo facts S Sched x hGT hanc)
  · -- an ancestor of the grade-2 entry of the round's frame
    obtain ⟨root₀, hc0, hroot0⟩ := facts.gr.readFrame_g2_provenance _ _ _ hg2
    have hprov := Restated.framePhaseProvenance_onPhaseTick facts S hm
      (Restated.framePhaseProvenance_sts facts S Sched x v m) c hc
    obtain ⟨m', B, hm', hB, hroot0B⟩ := hprov _ .g2 root₀ hc0
    have hrs0 := facts.gr.opening_slot_round_of_le_slot S.hc (s + 1)
    have hrs1 := facts.gr.lt_opening_slot_round_of_succ S.hc (s + 1)
    have hrr : r₀ ≤ (M.round_of S.hc (s + 1)) := by
      by_contra hcon
      exact nat_lt_absurd_c3 (Nat.le_succ_of_le hs0) hrs1
        (facts.gr.opening_slot_mono S (Nat.succ_le_of_lt (Nat.lt_of_not_le hcon)))
    have hpos : 0 < (M.round_of S.hc (s + 1)) :=
      lt_of_lt_of_le (Restated.round_pos_of_switch facts S tGAT tE gap hgst hlen hr₀) hrr
    obtain ⟨r₁, hr₁⟩ : ∃ r₁ : Round, (M.round_of S.hc (s + 1)) = r₁ + 1 :=
      ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
    rw [hr₁] at hvR hB hm' hrr hrs0 hR1
    obtain ⟨n, T, hJ, -, hTW⟩ := Restated.anchor_at_later_round_upTo facts S Sched x tE hexec hmono htd
      tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec hprev hclear hB'
      hnW hAW hJswitch hr₀ hTW₀ hJ₀ hrr (le_trans (Restated.anchorBound_le_headsBound facts S tE hR1) hb₀)
    obtain ⟨b, hb⟩ := facts.gr.gradeBool_nonempty S.E
      (M.gradeView (M.toHealing (x[m'][v].st).st.core)) (x[m'][v].st).st.core.F S.hc.η_SG
      (r₁ + 1) (M.early S.E S.hc (r₁ + 1) .g2) (M.late S.E S.hc (r₁ + 1) .g2) B
    have hBt : M.gradeBool S.E (M.gradeView (M.toHealing (x[m'][v].st).st.core))
        (x[m'][v].st).st.core.F S.hc.η_SG (r₁ + 1) (M.early S.E S.hc (r₁ + 1) .g2)
        (M.late S.E S.hc (r₁ + 1) .g2) B ⇢ true := hB b hb ▸ hb
    have hBP := Restated.graded_ancestorOfHonestHeadsFrom_upTo facts S Sched x tE hexec hmono htd tGAT gap
      hgst hlen (hsync.monoU facts hb₀) hthird hphase hrsW hmult hcv hcs hcom hw hs hrec hprev hclear
      hB' hnW hAW hJswitch (le_trans hr₀ hrr) hTW hJ hvR .g2 (facts.gr.domain_le_action S _ _) hm' hBt
    exact Restated.ancestorOfHonestHeadsFrom_mono_upTo facts S Sched x (Nat.add_le_add_right hrs0 2)
      (Restated.ancestorOfHonestHeadsFrom_of_preceq_upTo facts S Sched x
        (preceq_trans_Preceq hGroot (preceq_trans_Preceq hroot0 hroot0B)) hBP)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Under its premises on the execution and the phase ending at `tE`, with synchrony up to `b₀`
    where `max tE (S.a (round_of (sEnd − 2) + 1)) ≤ b₀`, and the joint invariant at a round `r₀` at
    or after the switch round for an anchor that is `T_W` or a descendant of it: if step `k`'s time
    is at or after `S.a r₀` and `v` is honest through step `k`, then `v`'s finalized block after `k`
    steps is an ancestor of every honest head of the slots from `slot(x[k].time) + 2` to `sEnd`. -/
theorem finalized_ancestorOfHonestHeadsFrom_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) {b₀ : Int} (hsync : Restated.SynchronyFromWakeBefore M S x b₀) (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight) (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t) (hrsW : Restated.roundSleepinessW M S Sched tE) (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT) (hcs : Restated.committeeSleepinessW M S Sched tE) (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched)) (hw : Restated.WakesAtActionInstants M S Sched) (hs : Restated.SleepsAfterActionInstants M S Sched) (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap) (hprev : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
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
        (Restated.runAllPath M S Sched x v N) T) (hclear : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
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
      Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T) (hB' : Restated.BaseJustifiedHighAtSwitchRoundW M S Sched x tGAT tE gap) {n_W : Nat} (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)))) {T_W : NamedBlock V} (hAW : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.switchRound M S tE) T_W) (hJswitch : ∀ (v : V) (n₁ : Nat),
      M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) - 1
        ≤ (x[n₁].time : Int) →
      n₁ ≤ n_W → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J T_W.erase) {sEnd : Slot}
    {r₀ : Round} {n₀ : Nat} {T₀ : NamedBlock V}
    (hr₀ : Restated.switchRound M S tE ≤ r₀) (hTW₀ : Block.Preceq T_W.erase T₀.erase)
    (hJ₀ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x r₀ n₀ n_W T₀)
    {k : Nat} (hk : (Restated.Vocabulary.Execution.Setup.a M S r₀) ≤ (x[k].time : Int)) {v : V} (hvk : Restated.HonestThrough M Sched x k v)
    (hb₀ : max tE ((Restated.Vocabulary.Execution.Setup.a M S ((M.round_of S.hc (sEnd - 2)) + 1))) ≤ b₀) :
    Restated.AncestorOfHonestHeadsFromTo M S Sched x (x[k][v].st).st.core.F
      (S.E.slotOf (x[k].time : Int) + 2) sEnd := by
  by_cases hE : S.E.slotOf (x[k].time : Int) + 2 ≤ sEnd
  swap
  · exact Restated.ancestorOfHonestHeadsFromTo_of_lt facts S Sched x (Nat.lt_of_not_le hE)
  have hsE : Restated.SynchronyFromWakeBefore M S x tE := hsync.monoU facts (le_trans (le_max_left _ _) hb₀)
  obtain ⟨r, har, hra⟩ := Restated.exists_action_round facts S (le_trans (Restated.action_mono facts S (Nat.zero_le r₀)) hk)
  have hrr : r₀ ≤ r := Nat.le_of_lt_succ (Restated.round_lt_of_action_lt facts S (lt_of_le_of_lt hk hra))
  have hsl : (M.opening_slot S.hc r) + 1 ≤ S.E.slotOf (x[k].time : Int) := by
    rw [← Restated.slotOf_action facts S r]; exact slotOf_mono_sts S har
  have hRr : r ≤ (M.round_of S.hc (sEnd - 2)) :=
    facts.gr.le_round_of_sub_two S.hc (le_trans (Nat.add_le_add_right (Nat.le_succ_of_le hsl) 1) hE)
  obtain ⟨n, T, hJ, -, hTW⟩ := Restated.anchor_at_later_round_upTo facts S Sched x tE hexec hmono htd
    tGAT gap hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec hprev hclear hB'
    hnW hAW hJswitch hr₀ hTW₀ hJ₀ hrr (le_trans (Restated.anchorBound_le_headsBound facts S tE hRr) hb₀)
  have hr : Restated.switchRound M S tE ≤ r := le_trans hr₀ hrr
  obtain ⟨n', hn'⟩ := Restated.tick_field_at_succ facts S Sched x htd r
  have hkn' : k ≤ n' + 1 := by
    by_contra hcon
    have h1 := Restated.time_mono_int facts S Sched x (Nat.le_of_lt (Nat.lt_of_not_le hcon))
    rw [(Restated.tickStepAt_time facts x hn').1] at h1
    linarith
  have hWk : n_W ≤ k := by
    by_contra hcon
    have h1 := Restated.time_mono_int facts S Sched x (Nat.le_of_lt (Nat.lt_of_not_le hcon))
    have h2 := (Restated.tickStepAt_time facts x hnW).2
    have h3 := Restated.action_mono facts S hr₀
    linarith
  have hJT := Restated.justified_preceq_anchor_ofJoint_upTo facts S Sched x tE hexec hmono htd tGAT gap hgst
    hlen hsE hthird hphase hrsW hmult hcv hcom hrec hprev hclear hB' hnW hAW hr hTW hJ hn' v k
    hWk hkn' hvk
  have hanc := Restated.anchor_ancestorOfHonestHeadsFrom_upTo facts S Sched x tE hexec hmono htd tGAT gap
    hgst hlen (hsync.monoU facts hb₀) hthird hphase hrsW hmult hcv hcs hcom hw hs hrec hprev hclear hB'
    hnW hAW hJswitch hr hTW hJ
  exact Restated.ancestorOfHonestHeadsFrom_mono_upTo facts S Sched x
    (Nat.le_succ_of_le (Nat.add_le_add_right hsl 1))
    (Restated.ancestorOfHonestHeadsFrom_of_preceq_upTo facts S Sched x
      (preceq_trans_Preceq (Restated.finalized_preceq_justified_sts facts S Sched x k v) hJT) hanc)

end

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Under its premises on the execution and the phase ending at `tE`, with synchrony up to `b₀`
    where `max tE (S.a (round_of (sEnd − 2) + 1)) ≤ b₀`, and the joint invariant at a round `r₀` at
    or after the switch round for an anchor that is `T_W` or a descendant of it: if step `k`'s time
    is at or after `S.a r₀`, `v` is honest through step `k`, and `v`'s two records after `k` steps
    satisfy `RecordsAncestorOfHonestHeadsTo` up to `sEnd`, then `v`'s `get_stable` and
    `get_confirmed` after `k` steps are ancestors of every honest head of the slots from
    `slot(x[k].time) + 2` to `sEnd`. -/
theorem outputs_ancestorOfHonestHeads_of_records_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) {b₀ : Int} (hsync : Restated.SynchronyFromWakeBefore M S x b₀) (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight) (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t) (hrsW : Restated.roundSleepinessW M S Sched tE) (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT) (hcs : Restated.committeeSleepinessW M S Sched tE) (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched)) (hw : Restated.WakesAtActionInstants M S Sched) (hs : Restated.SleepsAfterActionInstants M S Sched) (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap) (hprev : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
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
        (Restated.runAllPath M S Sched x v N) T) (hclear : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
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
      Restated.BaseClearFGSourceCompatibleWithAnchorAtRound M S Sched x r n₀ T) (hB' : Restated.BaseJustifiedHighAtSwitchRoundW M S Sched x tGAT tE gap) {n_W : Nat} (hnW : Restated.tickStepAt M x n_W ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)))) {T_W : NamedBlock V} (hAW : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.switchRound M S tE) T_W) (hJswitch : ∀ (v : V) (n₁ : Nat),
      M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) - 1
        ≤ (x[n₁].time : Int) →
      n₁ ≤ n_W → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.J T_W.erase) {sEnd : Slot}
    {r₀ : Round} {n₀ : Nat} {T₀ : NamedBlock V}
    (hr₀ : Restated.switchRound M S tE ≤ r₀) (hTW₀ : Block.Preceq T_W.erase T₀.erase)
    (hJ₀ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x r₀ n₀ n_W T₀)
    {k : Nat} (hk : (Restated.Vocabulary.Execution.Setup.a M S r₀) ≤ (x[k].time : Int)) {v : V} (hvk : Restated.HonestThrough M Sched x k v)
    (hrecs : Restated.RecordsAncestorOfHonestHeadsTo M S Sched x v k sEnd)
    (hb₀ : max tE ((Restated.Vocabulary.Execution.Setup.a M S ((M.round_of S.hc (sEnd - 2)) + 1))) ≤ b₀) :
    Restated.AncestorOfHonestHeadsFromTo M S Sched x (M.get_stable (x[k][v].st).st.core)
        (S.E.slotOf (x[k].time : Int) + 2) sEnd ∧
      Restated.AncestorOfHonestHeadsFromTo M S Sched x (M.get_confirmed (x[k][v].st).st.core)
        (S.E.slotOf (x[k].time : Int) + 2) sEnd := by
  have hF := Restated.finalized_ancestorOfHonestHeadsFrom_upTo facts S Sched x tE hexec hmono htd tGAT gap
    hgst hlen hsync hthird hphase hrsW hmult hcv hcs hcom hw hs hrec hprev hclear hB' hnW hAW
    hJswitch hr₀ hTW₀ hJ₀ hk hvk hb₀
  have hS := Restated.ancestorOfHonestHeadsFrom_get_stable_upTo facts S Sched x _ hrecs.1 hF
  exact ⟨hS, Restated.ancestorOfHonestHeadsFrom_get_confirmed_upTo facts S Sched x _ hS (fun _ => hrecs.2)⟩

end

end DecoupledConsensusModel.Sts.Restated
