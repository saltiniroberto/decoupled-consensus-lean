import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bSGCompatible
import Proofs.Claims.Restated.Claim13bStepGrade
import Proofs.Claims.Restated.Claim13beRoute3_21
import Proofs.Claims.Restated.Claim13beRoute3_44
import Proofs.Claims.Restated.Claim13beRoute3_44UpTo
import Proofs.Claims.Restated.Claim13beRoute3_45
import Proofs.Claims.Restated.Claim13beRoute3_45b
import Proofs.Claims.Restated.Claim13beRoute3_46
import Proofs.Claims.Restated.Claim13beRoute3_47b
import Proofs.Claims.Restated.Claim13beRoute3_48
import Proofs.Claims.Restated.Claim13beRoute3_48b
import Proofs.Claims.Restated.Claim13beRoute3_50
import Proofs.Claims.Restated.Claim13beRoute3_58
import Proofs.Claims.Restated.Claim13beRoute3_64b
import Proofs.Claims.Restated.Claim13beRoute3_65
import Proofs.Claims.Restated.Claim13beRoute3_68
import Proofs.Claims.Restated.Claim13beRoute3_70
import Proofs.Claims.Restated.Claim13beRoute3_71
import Proofs.Claims.Restated.Claim13beRoute3_72
import Proofs.Claims.Restated.Claim13beRoute3_74UpTo
import Proofs.Claims.Restated.Claim13beRoute3_77
import Proofs.Claims.Restated.Claim13beRoute3_78
import Proofs.Claims.Restated.Claim13beRoute3_78UpTo
import Proofs.Claims.Restated.Claim13beRoute3_79
import Proofs.Claims.Restated.Claim13beRoute3_79UpTo
import Proofs.Claims.Restated.Claim13beRoute3_80
import Proofs.Claims.Restated.RunAll
import Proofs.Claims.Restated.Vocabulary_Execution_ExcludesRefute
import Proofs.Claims.Restated.Vocabulary_Execution_HealthyLocalFacts
import Proofs.Claims.Restated.Vocabulary_Execution_OutageInputs
import Proofs.Claims.Restated.Vocabulary_Execution_Runtime
import Proofs.Claims.Restated.Vocabulary_ModelVocabulary_Healing_Schedule
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_SeedEntryCanonical
import Proofs.Claims.Restated.Vocabulary_Protocol_Grades_RecoveryGenuineClearNextVote
import Proofs.Vocabulary.Protocol.Grades.RelativeSupporter
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_MajoritySG_ForkChoice
import Proofs.Claims.Restated.Vocabulary_Protocol_Handlers_StoreBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_Action
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_SlotInduction
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.Claim13beRoute3_72
import Model.Conditions.Claim13beRoute3_74
import Model.Conditions.Claim13beRoute3_79
import Model.Conditions.ClaimAsyncK_DeliveryUpTo
import Model.Conditions.RunAll
import Model.Conditions.RunVocabulary
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Internal_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_Definitions_NamedLifecycle
import Model.Conditions.Vocabulary_Internal_Definitions_NamedOutageEntry
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGradeQueries
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGrades
import Model.Conditions.Vocabulary_Internal_Definitions_TickReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedDutyReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_NamedHeadReads
import Proofs.Vocabulary.Internal.Legacy.Definitions.NamedVoteConsumers
import Proofs.Vocabulary.ModelVocabulary
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedActionReads
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_Agreement
import Model.Conditions.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Model.Conditions.Vocabulary_Protocol_Grades_GoldfishConePersistence
import Model.Conditions.Vocabulary_Protocol_Grades_ProposalLifecycleCore
import Model.Conditions.Vocabulary_Protocol_Handlers_TickBridges
import Model.Record.Wiring

/-!
# The second-slot cone at the switch round, with synchrony up to the third slot

Each theorem here is the theorem of the same name without `_upTo`, stated over a model
`M : Record.Model V` and its facts, with synchrony assumed only up to `x[N].time`, the confirmation
instant of the switch round's third slot.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

local macro "p63% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_63)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p64b% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_64b)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p65% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_65)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p68% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_68)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p69b% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_69b)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p70% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_70)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p72% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_72)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p73% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_73)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p74% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_74)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p77% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_77)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p78% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_78)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p74u% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_74UpTo)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p80% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_80)
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

/-- In the regime `hreg` along `runAllPath M S Sched x v N`, with `rW = switchRound M S tE` and
    synchrony assumed only up to `x[N].time`: every validator `w` in `notHeldAt Sched` at the vote
    instant of slot `opening_slot rW + 1` has, at its vote store of that slot, `h_max` at most one
    more than the chain-state height of any run block `Hn` along the path descending from `T`. -/
theorem hmax_at_secondSlot_of_checkpointPreceq_l80_upTo (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v : V)
    {tGAT tE : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWakeBefore M S x
      (M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 2))) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (htd : Restated.TimeDiverges M x)
    {N : Nat}
    (hN : (x[N].time : Int)
      = M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 2))
    {blocked : Height} {first i : Nat} {a : NamedAttestation V} {ta : Int}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hreg : Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N)
      (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
      (notHeldAt Sched) Finset.univ Finset.univ
      (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0)
    (harW : a.round ≤ Restated.switchRound M S tE)
    {n₀ : Nat} (hn₀ : Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    (htop : Restated.topHonestRow M S Sched x n₀ ≤ (M.derive_named S.E S.cfg T).h) :
    ∀ w ∈ notHeldAt Sched
        (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1)),
    ∀ Hn : NamedBlock V,
      Restated.RunBlockOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N) Finset.univ Hn →
      Block.Preceq T.erase Hn.erase →
        (Restated.Vocabulary.Proofs.Optimistic.voteStore M (Setup.alwaysAwake S)
            (Restated.runAllPath M S Sched x v N
              (Restated.strictEventIndex
                ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
                (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1))) w).st.core
            ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1)).h_max ≤
          (M.derive_named S.E S.cfg Hn).h + 1 := by
  intro w hw Hn hHrun hTH
  obtain ⟨N', hN', hN'E, -, -, -, -, -⟩ := Restated.switchRound_instants facts S Sched x tGAT tE gap
    ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
    hgst hlen htd
  have hn : (x[N].time : Int) ≤ tE := by rw [hN.trans hN'.symm]; exact hN'E
  have hf := Restated.admissibleFieldsOn_runAll_notHeld_upTo facts S Sched x v N
    (fun k wv sm hsend hle haw => hsync k wv sm hsend (le_trans hle (le_of_eq hN)) haw)
    hmono hawake hgst hcv hvalid
    hawm hthird hn
  have hHs : ∀ t t' : Int, t ≤ t' → notHeldAt Sched t' ⊆ notHeldAt Sched t :=
    fun _ _ h => notHeldAt_anti hmono h
  have hHsXb : ∀ t : Int, notHeldAt Sched t ⊆ (Finset.univ : Finset V) :=
    fun _ => Finset.subset_univ _
  have hbelow := Restated.belowOneThirdOn_runAll_notHeld facts S Sched x v N hthird hn
  have hTrun := (hreg.checkpoint_runBlock facts hf hHsXb).1
  have hTHh : (M.derive_named S.E S.cfg T).h ≤ (M.derive_named S.E S.cfg Hn).h :=
    facts.cs.derive_height_mono S.E S.cfg
      (Restated.namedPreceq_of_runBlock_erase_preceqOn facts (notHeldAt Sched) Finset.univ hf hTrun hHrun hTH)
  have hvote := Restated.vote_time_openingSucc_lt_action_l78 facts S (Restated.switchRound M S tE)
  have hthor : M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) ≤
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } :
        Record.Run V).horizon := by
    show _ ≤ (x[N].time : Int)
    rw [hN]
    exact le_trans (le_of_lt (Int.lt_add_of_pos_right _ S.E.Δ_pos))
      (Restated.vote_time_add_delta_le_confirmation_l78 facts S (Nat.le_succ _))
  obtain ⟨hn₀1, -⟩ := Restated.tickStepAt_time facts x hn₀
  have hrow : (Restated.runAllPath M S Sched x v N
      (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1))) w).st.core.h_max ≤
      Restated.topHonestRow M S Sched x n₀ + 1 := by
    by_cases hlarge : 1 < (Restated.runAllPath M S Sched x v N
      (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1))) w).st.core.h_max
    · obtain ⟨b, tb, hb, hemit, htb, hrowb, -⟩ :=
        Restated.frontier_confirmationWitnessOn facts (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ hf
          hHs hHsXb (honestWeightMajorityOn_of_belowOneThirdOn hbelow) hthor hlarge
      obtain ⟨k, -, hk, hsent⟩ := Restated.mem_sent_of_emits_runAll facts S Sched x v hemit
      obtain ⟨hk1, -⟩ := Restated.tickStepAt_time facts x hk
      have hkn : k + 1 ≤ n₀ + 1 := by
        by_contra hcon
        have hmono' : ((x[n₀ + 1].time : Nat) : Int) ≤ ((x[k + 1].time : Nat) : Int) := by
          exact_mod_cast Restated.time_mono facts S Sched x (by omega)
        have : (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)) ≤ tb := by
          rw [← hn₀1, ← hk1]; exact hmono'
        linarith
      have hbk : b.val_index ∈ Finset.univ \ Sched.adv (x[k + 1].time : Int) := by
        rw [hk1]
        exact hHs _ _ htb.le hb
      have hhon : Restated.HonestThrough M Sched x (k + 1) b.val_index :=
        Restated.honestThrough_of_mem_notHeld facts S Sched x (k + 1) hmono _ hbk
      obtain ⟨entry, tmo, hpair⟩ := heightPair_vote_of_height_l72 hrowb
      have hle := Restated.honestRow_le_topHonestRow facts S Sched x hvalid.toUnforgeability
        ⟨b.val_index, k + 1, b, entry, tmo, hkn, hhon, rfl, hsent, hpair⟩
      exact Nat.sub_le_iff_le_add.mp hle
    · exact (Nat.le_of_not_lt hlarge).trans (Nat.le_add_left 1 _)
  rw [Restated.Vocabulary.Proofs.Optimistic.voteStore, (p77% tickStore_h_max₇₇) facts]
  exact hrow.trans (Nat.add_le_add_right (htop.trans hTHh) 1)

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

/-- In the regime `hreg` along `runAllPath M S Sched x v N`, with `rW = switchRound M S tE`,
    synchrony assumed only up to `x[N].time`, and the round-`(rW − 1)` SG blocks ancestors of the
    opening-slot votes of `rW` (`hP`): if `T ⪯ B` and every committee member of `opening_slot rW` in
    `notHeldAt Sched` at its vote instant votes a run block descending from `B`, then for every
    validator in `notHeldAt Sched` at the vote instant of `opening_slot rW + 1`, every anchor of its
    vote read at that slot is on one chain with `B`. -/
theorem anchor_compatible_of_openingCone_l80_upTo (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v : V)
    {tGAT tE : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWakeBefore M S x
      (M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 2))) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (htd : Restated.TimeDiverges M x)
    {N : Nat}
    (hN : (x[N].time : Int)
      = M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 2))
    {blocked : Height} {first i : Nat} {a : NamedAttestation V} {ta : Int}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hreg : Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N)
      (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
      (notHeldAt Sched) Finset.univ Finset.univ
      (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0)
    (harW : a.round ≤ Restated.switchRound M S tE)
    {n₀ : Nat} (hn₀ : Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    (htop : Restated.topHonestRow M S Sched x n₀ ≤ (M.derive_named S.E S.cfg T).h)
    (hP : ∀ nprev : V → M.N,
      (∀ u : V, nprev u ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (Restated.runAllPath M S Sched x v N
          (Restated.strictEventIndex
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
            (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE - 1))) u)
        (Restated.switchRound M S tE - 1)) →
      Restated.BasePreviousRoundSGBelowOpeningVotes M S Sched x v tE N
        (Restated.runAllPath M S Sched x v N) nprev)
    {B : Block V} (hTB : Block.Preceq T.erase B)
    (hcone : Restated.NamedHonestVotesConeOn M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N) (notHeldAt Sched) Finset.univ
      ((M.opening_slot S.hc (Restated.switchRound M S tE))) (fun X => Block.Preceq B X)) :
    ∀ w ∈ notHeldAt Sched (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1)),
      ∀ cw : M.Cache, M.onPhaseTick S.E S.hc
          (Restated.runAllPath M S Sched x v N
            (Restated.strictEventIndex
              ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
              (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1))) w).st.core.toHealing
          (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1))
          (Restated.runAllPath M S Sched x v N
            (Restated.strictEventIndex
              ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
              (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1))) w).cache ⇢ cw →
      ∀ A : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M (Setup.alwaysAwake S)
          (M.mkNode
            (M.ns_setClock S.E
              (Restated.runAllPath M S Sched x v N
                (Restated.strictEventIndex
                  ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
                  (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1))) w).st
              (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1)))
            (Restated.runAllPath M S Sched x v N
              (Restated.strictEventIndex
                ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
                (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1))) w).record cw)
          (M.round_of S.hc (M.mkNode
            (M.ns_setClock S.E
              (Restated.runAllPath M S Sched x v N
                (Restated.strictEventIndex
                  ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
                  (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1))) w).st
              (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1)))
            (Restated.runAllPath M S Sched x v N
              (Restated.strictEventIndex
                ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
                (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1))) w).record cw).st.core.s) ⇢ A →
        Block.compatible A B = true := by
  intro w hw cw hcw A hA
  obtain ⟨N', hN', hN'E, -, -, -, -, -⟩ := Restated.switchRound_instants facts S Sched x tGAT tE gap
    ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
    hgst hlen htd
  have hn : (x[N].time : Int) ≤ tE := by rw [hN.trans hN'.symm]; exact hN'E
  have hf := Restated.admissibleFieldsOn_runAll_notHeld_upTo facts S Sched x v N
    (fun k wv sm hsend hle haw => hsync k wv sm hsend (le_trans hle (le_of_eq hN)) haw)
    hmono hawake hgst hcv hvalid
    hawm hthird hn
  have hHs : ∀ t t' : Int, t ≤ t' → notHeldAt Sched t' ⊆ notHeldAt Sched t :=
    fun _ _ h => notHeldAt_anti hmono h
  have hHsXb : ∀ t : Int, notHeldAt Sched t ⊆ (Finset.univ : Finset V) :=
    fun _ => Finset.subset_univ _
  have hcomOn := Restated.honestCommitteesOn_notHeld facts S Sched hcom
  have hbelow := Restated.belowOneThirdOn_runAll_notHeld facts S Sched x v N hthird hn
  obtain ⟨-, -, hloOpen, -⟩ := Restated.roundAt_bounds_l71 facts S hgst
  have hlo := hreg.lo_le_opening_l71 facts hf hloOpen
  have hapos : 0 < a.round := hreg.seed.round_pos_l70 facts hf
  obtain ⟨hpredle, hrW1⟩ := pred_le_pred_pos_l74 a.round (Restated.switchRound M S tE) hapos harW
  obtain ⟨-, hloVote, hloPrev, -⟩ := Restated.loBounds_l70 facts S hapos hlo
  have hoPos : 0 < (M.opening_slot S.hc (Restated.switchRound M S tE)) :=
    facts.gr.opening_slot_pos_of_round_pos S.hc (lt_of_lt_of_le hapos harW)
  have hpostVote : tGAT + 1 ≤ M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE))) :=
    hloVote.trans (facts.sch.vote_time_mono_slots S.E (facts.gr.opening_slot_mono S harW))
  have hconfHor : M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE))) ≤
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } :
        Record.Run V).horizon := by
    show _ ≤ (x[N].time : Int)
    rw [hN]
    exact facts.sch.confirmation_time_mono_l78 S (Nat.le_add_right _ 2)
  have hpositive : 0 < (((Setup.alwaysAwake S).E.committee
      ((M.opening_slot S.hc (Restated.switchRound M S tE)))) ∩
      notHeldAt Sched (M.confirmation_time (Setup.alwaysAwake S).E
        ((M.opening_slot S.hc (Restated.switchRound M S tE))))).card := by
    have hc := hcomOn ((M.opening_slot S.hc (Restated.switchRound M S tE)))
    omega
  obtain ⟨y, hy⟩ := Finset.card_pos.mp hpositive
  have hycomm : y ∈ S.E.committee ((M.opening_slot S.hc (Restated.switchRound M S tE))) :=
    (Finset.mem_inter.mp hy).1
  have hyVote : y ∈ notHeldAt Sched
      (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)))) :=
    hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E _) (Finset.mem_inter.mp hy).2
  obtain ⟨cc, hcc, Tr, hTr, L, hL, L', hL', H, hH⟩ := (p78% exists_voteHead₇₈) facts (Setup.alwaysAwake S)
    (Restated.runAllPath M S Sched x v N
      (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE))))) y)
    ((M.opening_slot S.hc (Restated.switchRound M S tE)))
  obtain ⟨Hy, hHyErase, hHyRun⟩ := Restated.seedVoteDutyHead_runBlockOn facts (Setup.alwaysAwake S)
    (notHeldAt Sched) Finset.univ hf (hHsXb _ hyVote) ((M.opening_slot S.hc (Restated.switchRound M S tE)))
    cc hcc Tr hTr L hL L' hL' H hH
  have hvoteHorO : M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE))) ≤
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } :
        Record.Run V).horizon :=
    (facts.sch.Protocol_vote_time_le_confirmation_time S.E _).trans hconfHor
  have hrunY : ∀ j : Nat,
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } :
          Record.Run V).events[j]? =
        some (Record.Event.tick y (M.vote_time S.E (M.opening_slot S.hc (Restated.switchRound M S tE)))) →
      M.awake_for_grade1 (Setup.alwaysAwake S) y (Restated.runAllPath M S Sched x v N j y)
        (M.round_of S.hc (M.opening_slot S.hc (Restated.switchRound M S tE))) := by
    intro j hj
    have hpredLt : Restated.switchRound M S tE - 1 < Restated.switchRound M S tE :=
      Nat.sub_lt hrW1 Nat.one_pos
    have hwin : tGAT + 1 ≤ M.early S.E S.hc
        (M.round_of S.hc (M.opening_slot S.hc (Restated.switchRound M S tE))) .g1 - S.E.Δ := by
      rw [facts.gr.round_of_opening_slot_eq S.hc _]
      have h1 := facts.gr.action_delta_le_early S S.hc.R_ge_three hpredLt
      have h2 := facts.gr.q10_early_g2_le_early_g1 S (Restated.switchRound M S tE)
      have h3 : tGAT + 1 ≤ M.a S.hc S.E.Δ (Restated.switchRound M S tE - 1) :=
        hloPrev.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hpredle)
      linarith
    exact hf.awake_g1 _ _ j _ (Or.inr rfl) hj hyVote hwin
  have hHyEmit := Restated.seedVoteDutyHead_emitsOn facts (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ
    hf hyVote hoPos hycomm hvoteHorO hpostVote cc hcc hrunY Tr hTr L hL L' hL' H hH
  have hvoteEq : ∀ X : NamedBlock V,
      Restated.RunBlockOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N) Finset.univ X →
      Restated.Vocabulary.Execution.NamedRun.emits M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N) y
        (NamedObject.gfVote ⟨y, (M.opening_slot S.hc (Restated.switchRound M S tE)), X.erase.root⟩)
        (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)))) →
      X.erase = H := by
    intro X hXrun hXemit
    rw [← hHyErase]
    exact Restated.runBlock_eq_of_root_eqOn facts _ Finset.univ hf.rootCollisionFree hXrun hHyRun (by
      rw [hHyErase]
      exact congrArg GoldfishVote.head
        (Restated.emits_gfVote_uniqueOn facts (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ hf hXemit
          hHyEmit rfl))
  have hBy : Block.Preceq B H := by
    obtain ⟨X, hBX, hXrun, hXemit⟩ := hcone y hyVote hycomm
    rw [← hvoteEq X hXrun hXemit]
    exact hBX
  have hsg : Restated.HonestSGEmissionsCompatibleAtRoundOn M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N)
      (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
      (notHeldAt Sched) (Restated.switchRound M S tE - 1) B := by
    intro u hu nu hnu D hD hemit gc stu k A2' hA2' G' hG'
    obtain ⟨nprev, hnprev, hnprevu⟩ := (p80% exists_actionReads_choice₈₀) facts (Setup.alwaysAwake S)
      (Restated.runAllPath M S Sched x v N
        (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
          (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE - 1))))
      (Restated.switchRound M S tE - 1) u nu hnu
    have hPu := hP nprev hnprev u hu
    rw [hnprevu] at hPu
    obtain ⟨X, hXu, hXrun, hXemit⟩ := hPu D hD hemit A2' hA2' G' hG' y hyVote hycomm
    rw [hvoteEq X hXrun hXemit] at hXu
    exact compatible_of_preceq_common_Preceq hXu hBy
  have hmemW := (p69b% mem_stateBeforeTime_along₆₉b) hf.sorted hf.onePath
    (M.vote_time (Setup.alwaysAwake S).E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1))
  have hroot : Block.compatible
      (M.get_fg_root (M.toHealing (M.mkNode
        (M.ns_setClock S.E
          (Restated.runAllPath M S Sched x v N
            (Restated.strictEventIndex
              ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
              (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1))) w).st
          (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1)))
        (Restated.runAllPath M S Sched x v N
          (Restated.strictEventIndex
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
            (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1))) w).record cw).st.core).toFG)
      B = true := by
    refine (congrArg (fun R => Block.compatible R B)
      (Restated.fgRoot_voteDutyRead_eq_l78 facts (Setup.alwaysAwake S) _ w _ _ hmemW cw hcw)).trans ?_
    exact compatible_of_preceq_common_Preceq
      (preceq_trans_Preceq
        (Restated.fgRoot_comparable_anchor_at_secondSlot_upTo facts S Sched x v hsync hmono hawake hgst hcv hvalid
          hawm hthird hcom hlen htd hN hreg harW hn₀ htop w hw) hTB)
      (preceq_eq_true_iff_Preceq.mp (Block.preceq_self _))
  have hr := Restated.round_of_openingSucc_l78 facts S (Restated.switchRound M S tE)
  have hwdom : w ∈ notHeldAt Sched (M.domain S.E S.hc
      ((M.round_of S.hc ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1))) .g1) := by
    rw [hr]
    exact hHs _ _ (Restated.domain_g1_le_vote_openingSucc_l78 facts S (Restated.switchRound M S tE)) hw
  have hr' : (M.round_of (Setup.alwaysAwake S).hc ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1)) =
      Restated.switchRound M S tE := hr
  have hkPrev : tGAT + 1 ≤ M.early S.E S.hc (Restated.switchRound M S tE - 1) .g2 - S.E.Δ := by
    have hr0 := Restated.NamedHeightRegimeRunOn.r0_le_round_l71 facts hf hreg
    have hη := S.hc.η_SG_ge_one
    have h1 : (Restated.roundAt M S tGAT : Nat) + 1 + 2 ≤
        (Restated.roundAt M S tGAT : Nat) + S.hc.η_SG + 2 :=
      Nat.add_le_add_right (Nat.add_le_add_left hη _) 2
    have h2 : (Restated.roundAt M S tGAT : Nat) + 1 + 2 ≤ (Restated.switchRound M S tE : Nat) :=
      h1.trans (hr0.trans harW)
    have hA1 : tGAT + 1 ≤
        Restated.Vocabulary.Execution.Setup.a M S (Restated.roundAt M S tGAT + 1) :=
      Int.add_one_le_iff.mpr (lt_of_le_of_lt (Restated.Vocabulary.Statements.roundAt_spec facts S tGAT)
        (Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S (Nat.lt_succ_self _)))
    exact Restated.lo_le_early_g2_sub_delta_of_action_lt facts S hA1
      (Restated.lt_pred_of_add_two_le_l54 h2)
  exact Restated.voterAnchorAt_compatible_of_previousSGHistory_namedOn facts (Setup.alwaysAwake S)
    (notHeldAt Sched) Finset.univ hf hHs hHsXb hbelow hconfHor (by rw [hr']; exact hrW1)
    (by rw [hr']; exact hsg) (by rw [hr']; exact hloPrev.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hpredle))
    hwdom cw hcw hroot
    (by
      rw [hr']
      exact fun u _ j hj => Restated.awake_g2_action_runAllPath facts S Sched x v N hmono hawake
        hn (Restated.switchRound M S tE - 1) hkPrev u j hj) A hA

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

/-- In the regime `hreg` along `runAllPath M S Sched x v N`, with `rW = switchRound M S tE`,
    synchrony assumed only up to `x[N].time`, and the round-`(rW − 1)` SG blocks ancestors of the
    opening-slot votes of `rW` (`hP`): if `T ⪯ B` and every committee member of `opening_slot rW` in
    `notHeldAt Sched` at its vote instant votes a run block descending from `B`, then so does every
    committee member of `opening_slot rW + 1` in `notHeldAt Sched` at its vote instant. -/
theorem secondSlotCone_of_openingCone_l80_upTo (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v : V)
    {tGAT tE : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWakeBefore M S x
      (M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 2))) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (htd : Restated.TimeDiverges M x)
    {N : Nat}
    (hN : (x[N].time : Int)
      = M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 2))
    {blocked : Height} {first i : Nat} {a : NamedAttestation V} {ta : Int}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hreg : Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N)
      (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
      (notHeldAt Sched) Finset.univ Finset.univ
      (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0)
    (harW : a.round ≤ Restated.switchRound M S tE)
    {n₀ : Nat} (hn₀ : Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    (htop : Restated.topHonestRow M S Sched x n₀ ≤ (M.derive_named S.E S.cfg T).h)
    (hP : ∀ nprev : V → M.N,
      (∀ u : V, nprev u ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (Restated.runAllPath M S Sched x v N
          (Restated.strictEventIndex
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
            (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE - 1))) u)
        (Restated.switchRound M S tE - 1)) →
      Restated.BasePreviousRoundSGBelowOpeningVotes M S Sched x v tE N
        (Restated.runAllPath M S Sched x v N) nprev)
    {B : Block V} (hTB : Block.Preceq T.erase B)
    (hcone : Restated.NamedHonestVotesConeOn M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N) (notHeldAt Sched) Finset.univ
      ((M.opening_slot S.hc (Restated.switchRound M S tE))) (fun X => Block.Preceq B X)) :
    Restated.NamedHonestVotesConeOn M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N) (notHeldAt Sched) Finset.univ
      ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) (fun X => Block.Preceq B X) := by
  obtain ⟨N', hN', hN'E, -, -, -, -, -⟩ := Restated.switchRound_instants facts S Sched x tGAT tE gap
    ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
    hgst hlen htd
  have hn : (x[N].time : Int) ≤ tE := by rw [hN.trans hN'.symm]; exact hN'E
  have hf := Restated.admissibleFieldsOn_runAll_notHeld_upTo facts S Sched x v N
    (fun k wv sm hsend hle haw => hsync k wv sm hsend (le_trans hle (le_of_eq hN)) haw)
    hmono hawake hgst hcv hvalid
    hawm hthird hn
  have hHs : ∀ t t' : Int, t ≤ t' → notHeldAt Sched t' ⊆ notHeldAt Sched t :=
    fun _ _ h => notHeldAt_anti hmono h
  have hHsXb : ∀ t : Int, notHeldAt Sched t ⊆ (Finset.univ : Finset V) :=
    fun _ => Finset.subset_univ _
  have hcomOn := Restated.honestCommitteesOn_notHeld facts S Sched hcom
  obtain ⟨-, -, hloOpen, -⟩ := Restated.roundAt_bounds_l71 facts S hgst
  have hlo := hreg.lo_le_opening_l71 facts hf hloOpen
  have hapos : 0 < a.round := hreg.seed.round_pos_l70 facts hf
  obtain ⟨hpredle, hrW1⟩ := pred_le_pred_pos_l74 a.round (Restated.switchRound M S tE) hapos harW
  obtain ⟨-, hloVote, hloPrev, -⟩ := Restated.loBounds_l70 facts S hapos hlo
  have hoPos : 0 < (M.opening_slot S.hc (Restated.switchRound M S tE)) :=
    facts.gr.opening_slot_pos_of_round_pos S.hc (lt_of_lt_of_le hapos harW)
  have hconfHor : M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE))) ≤
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } :
        Record.Run V).horizon := by
    show _ ≤ (x[N].time : Int)
    rw [hN]
    exact facts.sch.confirmation_time_mono_l78 S (Nat.le_add_right _ 2)
  have hpredLt : Restated.switchRound M S tE - 1 < Restated.switchRound M S tE := Nat.sub_lt hrW1 Nat.one_pos
  have hpredProp : (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE - 1)) ≤
      M.proposal_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE))) := by
    have h1 := Restated.Vocabulary.Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt facts S hpredLt
    exact (le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans h1
  have hpostProp : tGAT + 1 ≤
      M.proposal_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE))) :=
    (hloPrev.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hpredle)).trans hpredProp
  have hwinW : tGAT + 1 ≤ M.early S.E S.hc (Restated.switchRound M S tE) .g1 - S.E.Δ := by
    have h1 := facts.gr.action_delta_le_early S S.hc.R_ge_three hpredLt
    have h2 := facts.gr.q10_early_g2_le_early_g1 S (Restated.switchRound M S tE)
    have h3 : tGAT + 1 ≤ M.a S.hc S.E.Δ (Restated.switchRound M S tE - 1) :=
      hloPrev.trans (Restated.Vocabulary.Proofs.Assembly.a_mono facts S hpredle)
    linarith
  have hrunW : ∀ d : Slot, (M.opening_slot S.hc (Restated.switchRound M S tE)) ≤ d →
      d ≤ (M.opening_slot S.hc (Restated.switchRound M S tE)) + 1 →
      ∀ w ∈ S.E.committee d, w ∈ notHeldAt Sched (M.vote_time S.E d) →
      ∀ j : Nat, ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } :
          Record.Run V).events[j]? = some (Record.Event.tick w (M.vote_time S.E d)) →
        M.awake_for_grade1 (Setup.alwaysAwake S) w (Restated.runAllPath M S Sched x v N j w)
          (M.round_of S.hc d) := by
    intro d hd1 hd2 w _ hw j hj
    have hround : M.round_of S.hc d = Restated.switchRound M S tE := by
      rcases Nat.lt_or_ge d ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) with h | h
      · rw [le_antisymm (Nat.lt_succ_iff.mp h) hd1]
        exact facts.gr.round_of_opening_slot_eq S.hc _
      · rw [le_antisymm hd2 h]
        exact facts.gr.HealingLemmas_round_of_opening_succ S.hc _
    have hwin : tGAT + 1 ≤ M.early S.E S.hc (M.round_of S.hc d) .g1 - S.E.Δ := by
      rw [hround]
      exact hwinW
    exact hf.awake_g1 _ _ j _ (Or.inr rfl) hj hw hwin
  exact Restated.honestVotesCone_succ_of_cone_hMaxOn facts (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ
    hf hHs hHsXb hcomOn hoPos hpostProp hconfHor hcone
    (fun w hw => Or.inl (preceq_trans_Preceq
      (Restated.fgRoot_comparable_anchor_at_secondSlot_upTo facts S Sched x v hsync hmono hawake hgst hcv hvalid
        hawm hthird hcom hlen htd hN hreg harW hn₀ htop w hw) hTB))
    (fun w hw _ Hn hHrun hBH => Restated.hmax_at_secondSlot_of_checkpointPreceq_l80_upTo facts S Sched x v hsync
      hmono hawake hgst hcv hvalid hawm hthird hcom hlen htd hN hreg harW hn₀ htop w hw Hn hHrun
      (preceq_trans_Preceq hTB hBH))
    (Restated.anchor_compatible_of_openingCone_l80_upTo facts S Sched x v hsync hmono hawake hgst hcv hvalid hawm
      hthird hcom hlen htd hN hreg harW hn₀ htop hP hTB hcone)
    hrunW

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

/-- In the regime `hreg` along `runAllPath M S Sched x v N`, with `rW = switchRound M S tE`,
    synchrony assumed only up to `x[N].time`, `hP`, and `hprev` (when the source round is `rW`,
    every round-`(rW − 1)` SG emission is on one chain with `T`): for a validator `v'` in
    `notHeldAt Sched` at `S.a rW`, a phase `p` whose domain instant is at or before `S.a rW`, and a
    block `B` that can pass the relative phase-`p` grade test of round `rW` at `v'`'s store before
    that instant, every committee member of `opening_slot rW + 1` in `notHeldAt Sched` at its vote
    instant votes along the path a run block descending from `B`. -/
theorem gradedBlock_cone_at_secondSlot_upTo (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v : V)
    {tGAT tE : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWakeBefore M S x
      (M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 2))) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (htd : Restated.TimeDiverges M x)
    {N : Nat}
    (hN : (x[N].time : Int)
      = M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 2))
    {blocked : Height} {first i : Nat} {a : NamedAttestation V} {ta : Int}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hreg : Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N)
      (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
      (notHeldAt Sched) Finset.univ Finset.univ
      (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0)
    (harW : a.round ≤ Restated.switchRound M S tE)
    {n₀ : Nat} (hn₀ : Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    (htop : Restated.topHonestRow M S Sched x n₀ ≤ (M.derive_named S.E S.cfg T).h)
    (hP : ∀ nprev : V → M.N,
      (∀ u : V, nprev u ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (Restated.runAllPath M S Sched x v N
          (Restated.strictEventIndex
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
            (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE - 1))) u)
        (Restated.switchRound M S tE - 1)) →
      Restated.BasePreviousRoundSGBelowOpeningVotes M S Sched x v tE N
        (Restated.runAllPath M S Sched x v N) nprev)
    (hprev : a.round = Restated.switchRound M S tE →
      Restated.BasePreviousRoundSGCompatibleWithAnchor M S Sched x v tE N
        (Restated.runAllPath M S Sched x v N) T)
    {v' : V} (hv' : v' ∈ notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    {p : Protocol.Phase}
    (hdom : M.domain S.E S.hc (Restated.switchRound M S tE) p ≤ (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)))
    {B : Block V}
    (hB : M.gradeBool S.E
      (M.gradeView (M.toHealing (Restated.runAllPath M S Sched x v N
        (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
          (M.domain S.E S.hc (Restated.switchRound M S tE) p)) v').st.core))
      (Restated.runAllPath M S Sched x v N
        (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
          (M.domain S.E S.hc (Restated.switchRound M S tE) p)) v').st.core.F
      S.hc.η_SG (Restated.switchRound M S tE) (M.early S.E S.hc (Restated.switchRound M S tE) p)
        (M.late S.E S.hc (Restated.switchRound M S tE) p) B ⇢ true) :
    Restated.NamedHonestVotesConeOn M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N) (notHeldAt Sched) Finset.univ
      ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) (fun X => Block.Preceq B X) := by
  obtain ⟨N', hN', hN'E, -, -, -, -, -⟩ := Restated.switchRound_instants facts S Sched x tGAT tE gap
    ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
    hgst hlen htd
  have hn : (x[N].time : Int) ≤ tE := by rw [hN.trans hN'.symm]; exact hN'E
  have hrWN : (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)) ≤ (x[N].time : Int) := by
    rw [hN]; exact Restated.action_le_confirmation_third facts S _
  have hf := Restated.admissibleFieldsOn_runAll_notHeld_upTo facts S Sched x v N
    (fun k wv sm hsend hle haw => hsync k wv sm hsend (le_trans hle (le_of_eq hN)) haw)
    hmono hawake hgst hcv hvalid hawm hthird hn
  obtain ⟨hrW1, hpost, hsg⟩ := (p74u% grade1_inputs₇₄u) facts S Sched x v hmono hgst hthird hcom hrWN hn hf
    hreg harW (fun h => hprev h) (facts.ndRun.tick_outcome_sts S Sched x hvalid.idealization.root_injective hvalid.honestRootsNew)
    (Restated.awake_g2_action_runAllPath facts S Sched x v N hmono hawake hn)
  have hHs : ∀ t t' : Int, t ≤ t' → notHeldAt Sched t' ⊆ notHeldAt Sched t :=
    fun _ _ h => notHeldAt_anti hmono h
  have hHsXb : ∀ t : Int, notHeldAt Sched t ⊆ (Finset.univ : Finset V) :=
    fun _ => Finset.subset_univ _
  have hbelow := Restated.belowOneThirdOn_runAll_notHeld facts S Sched x v N hthird hn
  have hdomainHor : M.domain S.E S.hc (Restated.switchRound M S tE) p ≤
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V).horizon := by
    show _ ≤ (x[N].time : Int)
    exact hdom.trans hrWN
  have hwdom : v' ∈ notHeldAt Sched (M.domain S.E S.hc (Restated.switchRound M S tE) p) :=
    hHs _ _ hdom hv'
  obtain ⟨n, hnA⟩ := (p73% actionReadFrom_nonempty₇₃) facts (Setup.alwaysAwake S)
    (Restated.runAllPath M S Sched x v N
      (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))) v')
    (Restated.switchRound M S tE)
  have hmemA := (p69b% mem_stateBeforeTime_along₆₉b) hf.sorted hf.onePath
    (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (Restated.switchRound M S tE))
  have hFT : Block.Preceq
      (Restated.runAllPath M S Sched x v N
        (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
          (M.domain S.E S.hc (Restated.switchRound M S tE) p)) v').st.core.F T.erase := by
    have h1 := (p77% F_mono_along₇₇) facts (Setup.alwaysAwake S) hf.onePath v'
      ((p65% strictEventIndex_mono₆₅)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) hdom)
    have h2 := (p77% F_preceq_fgRoot_along₇₇) facts (Setup.alwaysAwake S) hf.sorted hf.onePath v'
      (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))
    have h3 := Restated.actionFgRoot_preceq_checkpoint_at_switchRound_upTo facts S Sched x v hsync hmono hawake hgst
      hcv hvalid hawm hthird hcom hlen htd hN hreg harW hn₀ htop v' hv' n hnA
    rw [Restated.Vocabulary.Proofs.HealingSurface.actionStoreAt_fgRoot_eq_storeBeforeTime facts
      (Setup.alwaysAwake S) _ v' (Restated.switchRound M S tE) _ hmemA n hnA] at h3
    exact preceq_trans_Preceq h1 (preceq_trans_Preceq h2 h3)
  have hkPrev : tGAT + 1 ≤ M.early S.E S.hc (Restated.switchRound M S tE - 1) .g2 - S.E.Δ := by
    have hr0 := Restated.NamedHeightRegimeRunOn.r0_le_round_l71 facts hf hreg
    have hη := S.hc.η_SG_ge_one
    have h1 : (Restated.roundAt M S tGAT : Nat) + 1 + 2 ≤
        (Restated.roundAt M S tGAT : Nat) + S.hc.η_SG + 2 :=
      Nat.add_le_add_right (Nat.add_le_add_left hη _) 2
    have h2 : (Restated.roundAt M S tGAT : Nat) + 1 + 2 ≤ (Restated.switchRound M S tE : Nat) :=
      h1.trans (hr0.trans harW)
    have hA1 : tGAT + 1 ≤
        Restated.Vocabulary.Execution.Setup.a M S (Restated.roundAt M S tGAT + 1) :=
      Int.add_one_le_iff.mpr (lt_of_le_of_lt (Restated.Vocabulary.Statements.roundAt_spec facts S tGAT)
        (Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S (Nat.lt_succ_self _)))
    exact Restated.lo_le_early_g2_sub_delta_of_action_lt facts S hA1
      (Restated.lt_pred_of_add_two_le_l54 h2)
  obtain ⟨u, hu, hall⟩ := Restated.phaseGrade_preceq_previousSGBlock_l80 facts (Setup.alwaysAwake S)
    (notHeldAt Sched) Finset.univ hf hHs hHsXb hbelow hrW1 hpost hdomainHor hwdom hFT hsg hB
    (fun u _ j hj => Restated.awake_g2_action_runAllPath facts S Sched x v N hmono hawake
      hn (Restated.switchRound M S tE - 1) hkPrev u j hj)
  obtain ⟨nu, hnu, g, hg, Bk, hBk⟩ := (p65% exists_actionSG₆₅) facts (Setup.alwaysAwake S)
    (Restated.runAllPath M S Sched x v N
      (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE - 1))) u)
    (Restated.switchRound M S tE - 1)
  obtain ⟨D, hD⟩ := facts.dt.attest_with_nonempty (M.gradeContract nu.cache) (Setup.alwaysAwake S).E
    (Setup.alwaysAwake S).hc ((Setup.alwaysAwake S).node u) nu.st nu.record
  obtain ⟨hemit, hBall⟩ := hall nu hnu D hD
  have hBX : Block.Preceq B Bk := hBall g hg Bk hBk
  have hXT : Block.compatible Bk T.erase = true := hsg u hu nu hnu D hD hemit g hg Bk hBk
  have hcheck := Restated.checkpointCone_at_secondSlot_upTo facts S Sched x v hsync hmono hawake hgst hcv hvalid
    hawm hthird hcom hlen htd hN hreg harW
  rcases compatible_cases hXT with hXT' | hTX
  · exact Restated.namedHonestVotesConeOn_of_preceq_l78 facts (preceq_trans_Preceq hBX hXT') hcheck
  · rcases preceq_linear_Preceq hBX hTX with hBT | hTB
    · exact Restated.namedHonestVotesConeOn_of_preceq_l78 facts hBT hcheck
    · obtain ⟨nprev, hnprev, hnprevu⟩ := (p80% exists_actionReads_choice₈₀) facts (Setup.alwaysAwake S)
        (Restated.runAllPath M S Sched x v N
          (Restated.strictEventIndex
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
            (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE - 1))))
        (Restated.switchRound M S tE - 1) u nu hnu
      have hPu := hP nprev hnprev u hu
      rw [hnprevu] at hPu
      exact Restated.secondSlotCone_of_openingCone_l80_upTo facts S Sched x v hsync hmono hawake hgst hcv hvalid
        hawm hthird hcom hlen htd hN hreg harW hn₀ htop hP hTB
        (Restated.namedHonestVotesConeOn_of_preceq_l78 facts hBX (hPu D hD hemit g hg Bk hBk))

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

/-- Given the hypotheses of `gradedBlock_cone_at_secondSlot_upTo`: for a validator `v'` in
    `notHeldAt Sched` at `S.a rW` and a node state `n` of its round-`rW` action read whose grade-2
    selection can return `some Q`, every committee member of `opening_slot rW + 1` in
    `notHeldAt Sched` at its vote instant votes along the path a run block descending from `Q`. -/
theorem nodeQ2Tier_cone_at_secondSlot_upTo (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v : V)
    {tGAT tE : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWakeBefore M S x
      (M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 2))) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (htd : Restated.TimeDiverges M x)
    {N : Nat}
    (hN : (x[N].time : Int)
      = M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 2))
    {blocked : Height} {first i : Nat} {a : NamedAttestation V} {ta : Int}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hreg : Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N)
      (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
      (notHeldAt Sched) Finset.univ Finset.univ
      (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0)
    (harW : a.round ≤ Restated.switchRound M S tE)
    {n₀ : Nat} (hn₀ : Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    (htop : Restated.topHonestRow M S Sched x n₀ ≤ (M.derive_named S.E S.cfg T).h)
    (hP : ∀ nprev : V → M.N,
      (∀ u : V, nprev u ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (Restated.runAllPath M S Sched x v N
          (Restated.strictEventIndex
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
            (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE - 1))) u)
        (Restated.switchRound M S tE - 1)) →
      Restated.BasePreviousRoundSGBelowOpeningVotes M S Sched x v tE N
        (Restated.runAllPath M S Sched x v N) nprev)
    (hprev : a.round = Restated.switchRound M S tE →
      Restated.BasePreviousRoundSGCompatibleWithAnchor M S Sched x v tE N
        (Restated.runAllPath M S Sched x v N) T)
    {v' : V} (hv' : v' ∈ notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    {n : M.N}
    (hnA : n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (Restated.runAllPath M S Sched x v N
          (Restated.strictEventIndex
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
            (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))) v')
        (Restated.switchRound M S tE))
    {Q : Block V}
    (hQ : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M (Setup.alwaysAwake S) n
      (Restated.switchRound M S tE) ⇢ some Q) :
    Restated.NamedHonestVotesConeOn M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N) (notHeldAt Sched) Finset.univ
      ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1) (fun X => Block.Preceq Q X) := by
  obtain ⟨N', hN', hN'E, -, -, -, -, -⟩ := Restated.switchRound_instants facts S Sched x tGAT tE gap
    ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
    hgst hlen htd
  have hn : (x[N].time : Int) ≤ tE := by rw [hN.trans hN'.symm]; exact hN'E
  have hrWN : (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)) ≤ (x[N].time : Int) := by
    rw [hN]; exact Restated.action_le_confirmation_third facts S _
  have hf := Restated.admissibleFieldsOn_runAll_notHeld_upTo facts S Sched x v N
    (fun k wv sm hsend hle haw => hsync k wv sm hsend (le_trans hle (le_of_eq hN)) haw)
    hmono hawake hgst hcv hvalid
    hawm hthird hn
  have hHs : ∀ t t' : Int, t ≤ t' → notHeldAt Sched t' ⊆ notHeldAt Sched t :=
    fun _ _ h => notHeldAt_anti hmono h
  have hHsXb : ∀ t : Int, notHeldAt Sched t ⊆ (Finset.univ : Finset V) :=
    fun _ => Finset.subset_univ _
  obtain ⟨-, -, hloOpen, -⟩ := Restated.roundAt_bounds_l71 facts S hgst
  have hlo := hreg.lo_le_opening_l71 facts hf hloOpen
  have hapos : 0 < a.round := hreg.seed.round_pos_l70 facts hf
  obtain ⟨hpredle, hrW1⟩ := pred_le_pred_pos_l74 a.round (Restated.switchRound M S tE) hapos harW
  have hloOpenRW : tGAT + 1 ≤ M.opening S.E S.hc (Restated.switchRound M S tE - S.hc.η_SG) :=
    hlo.trans (facts.gr.NamedOutageClosure_opening_mono S (Nat.sub_le_sub_right harW _))
  have hvG0 : v' ∈ notHeldAt Sched (M.domain S.E S.hc (Restated.switchRound M S tE) .g0) :=
    hHs _ _ (facts.gr.domain_le_a S _ .g0) hv'
  have hhorA : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (Restated.switchRound M S tE)) ≤
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V).horizon := by
    show _ ≤ (x[N].time : Int)
    exact hrWN
  have hG1 := Restated.namedG1At_of_nodeQ2On facts (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ hf
    hHs hHsXb hrW1 hhorA hloOpenRW v' hvG0 Q n hnA hQ
  exact Restated.gradedBlock_cone_at_secondSlot_upTo facts S Sched x v hsync hmono hawake hgst hcv hvalid hawm
    hthird hcom hlen htd hN hreg harW hn₀ htop hP hprev hv' (p := .g1)
    (facts.gr.domain_le_a S _ .g1)
    ((p65% storeGrade_true_of_all₆₅) facts (Setup.alwaysAwake S).E (Setup.alwaysAwake S).hc _
      (Restated.switchRound M S tE) .g1 Q hG1)

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

/-- Given the hypotheses of `gradedBlock_cone_at_secondSlot_upTo`: for a validator `v'` in
    `notHeldAt Sched` at `S.a rW`, every node state `n` of its round-`rW` action read and every
    anchor `A` of `n` at round `rW`, every committee member of `opening_slot rW + 1` in
    `notHeldAt Sched` at its vote instant votes along the path a run block descending from `A`. -/
theorem anchorTier_cone_at_secondSlot_upTo (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v : V)
    {tGAT tE : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWakeBefore M S x
      (M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 2))) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (htd : Restated.TimeDiverges M x)
    {N : Nat}
    (hN : (x[N].time : Int)
      = M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 2))
    {blocked : Height} {first i : Nat} {a : NamedAttestation V} {ta : Int}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hreg : Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N)
      (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
      (notHeldAt Sched) Finset.univ Finset.univ
      (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0)
    (harW : a.round ≤ Restated.switchRound M S tE)
    {n₀ : Nat} (hn₀ : Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    (htop : Restated.topHonestRow M S Sched x n₀ ≤ (M.derive_named S.E S.cfg T).h)
    (hP : ∀ nprev : V → M.N,
      (∀ u : V, nprev u ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (Restated.runAllPath M S Sched x v N
          (Restated.strictEventIndex
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
            (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE - 1))) u)
        (Restated.switchRound M S tE - 1)) →
      Restated.BasePreviousRoundSGBelowOpeningVotes M S Sched x v tE N
        (Restated.runAllPath M S Sched x v N) nprev)
    (hprev : a.round = Restated.switchRound M S tE →
      Restated.BasePreviousRoundSGCompatibleWithAnchor M S Sched x v tE N
        (Restated.runAllPath M S Sched x v N) T)
    {v' : V} (hv' : v' ∈ notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)))) :
    ∀ n ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (Restated.runAllPath M S Sched x v N
          (Restated.strictEventIndex
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
            (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))) v')
        (Restated.switchRound M S tE),
    ∀ A : Block V, Restated.Vocabulary.Internal.PhaseGrades.nodeAnchor M (Setup.alwaysAwake S) n
        (Restated.switchRound M S tE) ⇢ A →
    Restated.NamedHonestVotesConeOn M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N) (notHeldAt Sched) Finset.univ
      ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 1)
      (fun X => Block.Preceq A X) := by
  intro n hnA A hA
  obtain ⟨N', hN', hN'E, -, -, -, -, -⟩ := Restated.switchRound_instants facts S Sched x tGAT tE gap
    ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
    hgst hlen htd
  have hn : (x[N].time : Int) ≤ tE := by rw [hN.trans hN'.symm]; exact hN'E
  have hrWN : (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)) ≤ (x[N].time : Int) := by
    rw [hN]; exact Restated.action_le_confirmation_third facts S _
  have hf := Restated.admissibleFieldsOn_runAll_notHeld_upTo facts S Sched x v N
    (fun k wv sm hsend hle haw => hsync k wv sm hsend (le_trans hle (le_of_eq hN)) haw)
    hmono hawake hgst hcv hvalid
    hawm hthird hn
  have hmemA := (p69b% mem_stateBeforeTime_along₆₉b) hf.sorted hf.onePath
    (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (Restated.switchRound M S tE))
  rcases Restated.actionAnchor_cases_l80 facts (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      v' (Restated.switchRound M S tE) n ⟨_, hmemA, hnA⟩ A hA with
    hfg | ⟨root, L, hframe, hactive, hAL⟩
  · rw [hfg]
    exact Restated.namedHonestVotesConeOn_of_preceq_l78 facts
      (Restated.actionFgRoot_preceq_checkpoint_at_switchRound_upTo facts S Sched x v hsync hmono hawake hgst hcv
        hvalid hawm hthird hcom hlen htd hN hreg harW hn₀ htop v' hv' n hnA)
      (Restated.checkpointCone_at_secondSlot_upTo facts S Sched x v hsync hmono hawake hgst hcv hvalid hawm hthird
        hcom hlen htd hN hreg harW)
  · rw [hAL]
    have hHs : ∀ t t' : Int, t ≤ t' → notHeldAt Sched t' ⊆ notHeldAt Sched t :=
      fun _ _ h => notHeldAt_anti hmono h
    obtain ⟨-, -, hloOpen, -⟩ := Restated.roundAt_bounds_l71 facts S hgst
    have hlo := hreg.lo_le_opening_l71 facts hf hloOpen
    have hapos : 0 < a.round := hreg.seed.round_pos_l70 facts hf
    obtain ⟨hpredle, hrW1⟩ := pred_le_pred_pos_l74 a.round (Restated.switchRound M S tE) hapos harW
    have hloOpenRW : tGAT + 1 ≤ M.opening S.E S.hc (Restated.switchRound M S tE - S.hc.η_SG) :=
      hlo.trans (facts.gr.NamedOutageClosure_opening_mono S (Nat.sub_le_sub_right harW _))
    have hgatG2 : tGAT + 1 ≤ M.domain S.E S.hc (Restated.switchRound M S tE) .g2 :=
      (facts.gr.lo_le_early_g2_of_window_start S hrW1 hloOpenRW).trans
        (facts.gr.early_le_domain S _)
    have hgat : tGAT + 1 ≤ M.domain S.E S.hc (Restated.switchRound M S tE) .g1 :=
      hgatG2.trans (facts.gr.domain_g2_le_domain_g1 S (Restated.switchRound M S tE))
    have hvG1 : v' ∈ notHeldAt Sched (M.domain S.E S.hc (Restated.switchRound M S tE) .g1) :=
      hHs _ _ (facts.gr.domain_le_a S _ .g1) hv'
    have hhorA : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (Restated.switchRound M S tE)) ≤
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V).horizon := by
      show _ ≤ (x[N].time : Int)
      exact hrWN
    have hG1 := Restated.activeActionAnchor_storeGrade_g1_actionHistoryOn facts (Setup.alwaysAwake S)
      (notHeldAt Sched) Finset.univ hf hrW1 hhorA hvG1 n hnA hframe hactive hgat
    exact Restated.gradedBlock_cone_at_secondSlot_upTo facts S Sched x v hsync hmono hawake hgst hcv hvalid hawm
      hthird hcom hlen htd hN hreg harW hn₀ htop hP hprev hv' (p := .g1)
      (facts.gr.domain_le_a S _ .g1)
      ((p65% storeGrade_true_of_all₆₅) facts (Setup.alwaysAwake S).E (Setup.alwaysAwake S).hc _
        (Restated.switchRound M S tE) .g1 L hG1)

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

/-- In the regime `hreg` along `runAllPath M S Sched x v N`, with `rW = switchRound M S tE`,
    synchrony assumed only up to `x[N].time`, `hP` and `hprev`: the round-`rW` SG blocks of any two
    validators in `notHeldAt Sched` at `S.a rW` lie on one chain (`BaseSGOneChainAtSwitchRound`). -/
theorem baseSGOneChainAtSwitchRound_of_prevCompatible_upTo (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v : V)
    {tGAT tE : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWakeBefore M S x
      (M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 2))) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (htd : Restated.TimeDiverges M x)
    {N : Nat}
    (hN : (x[N].time : Int)
      = M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 2))
    {blocked : Height} {first i : Nat} {a : NamedAttestation V} {ta : Int}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hreg : Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N)
      (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
      (notHeldAt Sched) Finset.univ Finset.univ
      (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0)
    (harW : a.round ≤ Restated.switchRound M S tE)
    {n₀ : Nat} (hn₀ : Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    (htop : Restated.topHonestRow M S Sched x n₀ ≤ (M.derive_named S.E S.cfg T).h)
    (hP : ∀ nprev : V → M.N,
      (∀ u : V, nprev u ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (Restated.runAllPath M S Sched x v N
          (Restated.strictEventIndex
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
            (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE - 1))) u)
        (Restated.switchRound M S tE - 1)) →
      Restated.BasePreviousRoundSGBelowOpeningVotes M S Sched x v tE N
        (Restated.runAllPath M S Sched x v N) nprev)
    (hprev : a.round = Restated.switchRound M S tE →
      Restated.BasePreviousRoundSGCompatibleWithAnchor M S Sched x v tE N
        (Restated.runAllPath M S Sched x v N) T) :
    Restated.BaseSGOneChainAtSwitchRound M S Sched x v tE N := by
  obtain ⟨N', hN', hN'E, -, -, -, -, -⟩ := Restated.switchRound_instants facts S Sched x tGAT tE gap
    ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
    hgst hlen htd
  have hn : (x[N].time : Int) ≤ tE := by rw [hN.trans hN'.symm]; exact hN'E
  have hf := Restated.admissibleFieldsOn_runAll_notHeld_upTo facts S Sched x v N
    (fun k wv sm hsend hle haw => hsync k wv sm hsend (le_trans hle (le_of_eq hN)) haw)
    hmono hawake hgst hcv hvalid
    hawm hthird hn
  have hHs : ∀ t t' : Int, t ≤ t' → notHeldAt Sched t' ⊆ notHeldAt Sched t :=
    fun _ _ h => notHeldAt_anti hmono h
  have hcomOn := Restated.honestCommitteesOn_notHeld facts S Sched hcom
  have hmemA := (p69b% mem_stateBeforeTime_along₆₉b) hf.sorted hf.onePath
    (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) (Restated.switchRound M S tE))
  unfold Restated.BaseSGOneChainAtSwitchRound
  refine Restated.honestActionCarriersOneChainAt_of_secondSlotConeOn facts (Setup.alwaysAwake S)
    (notHeldAt Sched) Finset.univ hf hHs hcomOn ?_
  intro v' hv' n hnA g2 hg2 Bv hBv
  obtain ⟨gr, hgr⟩ := facts.gr.read_nonempty (M.gradeContract n.cache) (Setup.alwaysAwake S).E
    (Setup.alwaysAwake S).hc n.st.core.toHealing (Restated.switchRound M S tE)
  rcases Restated.Vocabulary.Proofs.HealingSurface.actionSGBlockAt_tiers facts (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      v' (Restated.switchRound M S tE) n ⟨_, hmemA, hnA⟩ gr hgr g2 hg2 Bv hBv with
    ⟨-, hclear, -⟩ | ⟨Q, hQ, hEq⟩ | ⟨-, -, hEq⟩ | ⟨-, -, hEq⟩
  · exact Restated.clearTier_cone_at_secondSlot_upTo facts S Sched x v hsync hmono hawake hgst hcv hvalid hawm
      hthird hcom hlen htd hN hreg harW hn₀ htop hP hv' hnA hg2 hBv hclear
  · rw [hEq]
    have hQ' := (p77% returns_map_intro₇₇) (fun g : Protocol.GradeRead V => g.Q2) _ gr hgr
    rw [hQ] at hQ'
    exact Restated.nodeQ2Tier_cone_at_secondSlot_upTo facts S Sched x v hsync hmono hawake hgst hcv hvalid hawm
      hthird hcom hlen htd hN hreg harW hn₀ htop hP hprev hv' hnA hQ'
  · refine Restated.fgRootTier_cone_at_secondSlot_upTo facts S Sched x v hsync hmono hawake hgst hcv hvalid hawm
      hthird hcom hlen htd hN hreg harW hn₀ htop hv' hnA hg2 hBv ?_
    rw [hEq]
    exact preceq_eq_true_iff_Preceq.mp (Block.preceq_self _)
  · rw [hEq]
    exact Restated.anchorTier_cone_at_secondSlot_upTo facts S Sched x v hsync hmono hawake hgst hcv hvalid hawm
      hthird hcom hlen htd hN hreg harW hn₀ htop hP hprev hv' n hnA gr.anchor
      ((p77% returns_map_intro₇₇) (fun g : Protocol.GradeRead V => g.anchor) _ gr hgr)

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

/-- In the regime `hreg` along `runAllPath M S Sched x v N`, with `rW = switchRound M S tE`, source
    round `rW`, and synchrony assumed only up to `x[N].time`: if the round-`(rW − 1)` SG blocks of
    the emitting validators in `notHeldAt Sched` at `S.a (rW − 1)` are ancestors of every
    opening-slot vote of `rW` by a committee member in `notHeldAt Sched` at its vote instant (`hP`),
    then every such SG block is on one chain with `T` (`BasePreviousRoundSGCompatibleWithAnchor`). -/
theorem basePreviousRoundSGCompatibleWithAnchor_of_belowOpeningVotes_upTo (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v : V)
    {tGAT tE : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWakeBefore M S x
      (M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 2))) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (htd : Restated.TimeDiverges M x)
    {N : Nat}
    (hN : (x[N].time : Int)
      = M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 2))
    {blocked : Height} {first i : Nat} {a : NamedAttestation V} {ta : Int}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hreg : Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N)
      (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
      (notHeldAt Sched) Finset.univ Finset.univ
      (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0)
    (harW : a.round = Restated.switchRound M S tE)
    (hP : ∀ nprev : V → M.N,
      (∀ u : V, nprev u ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (Restated.runAllPath M S Sched x v N
          (Restated.strictEventIndex
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
            (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE - 1))) u)
        (Restated.switchRound M S tE - 1)) →
      Restated.BasePreviousRoundSGBelowOpeningVotes M S Sched x v tE N
        (Restated.runAllPath M S Sched x v N) nprev) :
    Restated.BasePreviousRoundSGCompatibleWithAnchor M S Sched x v tE N
      (Restated.runAllPath M S Sched x v N) T := by
  obtain ⟨N', hN', hN'E, -, -, -, -, -⟩ := Restated.switchRound_instants facts S Sched x tGAT tE gap
    ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
    hgst hlen htd
  have hn : (x[N].time : Int) ≤ tE := by rw [hN.trans hN'.symm]; exact hN'E
  have hf := Restated.admissibleFieldsOn_runAll_notHeld_upTo facts S Sched x v N
    (fun k wv sm hsend hle haw => hsync k wv sm hsend (le_trans hle (le_of_eq hN)) haw)
    hmono hawake hgst hcv hvalid
    hawm hthird hn
  have hHs : ∀ t t' : Int, t ≤ t' → notHeldAt Sched t' ⊆ notHeldAt Sched t :=
    fun _ _ h => notHeldAt_anti hmono h
  have hHsXb : ∀ t : Int, notHeldAt Sched t ⊆ (Finset.univ : Finset V) :=
    fun _ => Finset.subset_univ _
  have hX : ∀ t : Int, 0 ≤ t → notHeldAt Sched t ⊆ (Finset.univ : Finset V) :=
    fun _ _ => Finset.subset_univ _
  have hXXb : (Finset.univ : Finset V) ⊆ Finset.univ := Finset.Subset.refl _
  have hcomOn := Restated.honestCommitteesOn_notHeld facts S Sched hcom
  obtain ⟨-, -, hloOpen, -⟩ := Restated.roundAt_bounds_l71 facts S hgst
  have hlo := hreg.lo_le_opening_l71 facts hf hloOpen
  have hapos : 0 < a.round := hreg.seed.round_pos_l70 facts hf
  obtain ⟨-, hloVote, -, -⟩ := Restated.loBounds_l70 facts S hapos hlo
  have hoPos : 0 < (M.opening_slot S.hc (Restated.switchRound M S tE)) :=
    facts.gr.opening_slot_pos_of_round_pos S.hc (lt_of_lt_of_le hapos harW.le)
  have hSc : (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)) =
      M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE))) := by
    rw [Restated.Vocabulary.Execution.Setup.a, facts.sch.a_eq_confirmation_time]
  have hcut : M.support_cutoff S.E ((M.opening_slot S.hc (Restated.switchRound M S tE))) ≤
      (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)) := by
    rw [hSc]
    exact facts.sch.Protocol_support_cutoff_le_confirmation_time S.E _
  have hpostVote : tGAT + 1 ≤ M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE))) := by
    rw [← harW]
    exact hloVote
  have hwinW : tGAT + 1 ≤ M.early S.E S.hc
      (M.round_of S.hc (M.opening_slot S.hc (Restated.switchRound M S tE))) .g1 - S.E.Δ := by
    rw [facts.gr.round_of_opening_slot_eq S.hc _]
    have h := Restated.NamedHeightRegimeRunOn.r0_le_round_l71 facts hf hreg
    rw [harW] at h
    have h1 : Restated.roundAt M S tGAT + 1 < Restated.roundAt M S tGAT + S.hc.η_SG + 2 := by
      rw [Nat.add_assoc]
      exact Nat.add_lt_add_left (Nat.lt_add_left S.hc.η_SG Nat.one_lt_two) _
    have hlt : Restated.roundAt M S tGAT + 1 < Restated.switchRound M S tE := lt_of_lt_of_le h1 h
    have hA1 : tGAT + 1 ≤
        Restated.Vocabulary.Execution.Setup.a M S (Restated.roundAt M S tGAT + 1) :=
      Int.add_one_le_iff.mpr (lt_of_le_of_lt (Restated.Vocabulary.Statements.roundAt_spec facts S tGAT)
        (Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S (Nat.lt_succ_self _)))
    have hA1' : tGAT + 1 ≤ M.a S.hc S.E.Δ (Restated.roundAt M S tGAT + 1) := hA1
    have h2 := facts.gr.action_delta_le_early S S.hc.R_ge_three hlt
    have h3 := facts.gr.q10_early_g2_le_early_g1 S (Restated.switchRound M S tE)
    linarith
  have hrunY : ∀ y ∈ notHeldAt Sched (M.vote_time S.E (M.opening_slot S.hc (Restated.switchRound M S tE))),
      ∀ j : Nat, ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } :
          Record.Run V).events[j]? =
        some (Record.Event.tick y (M.vote_time S.E (M.opening_slot S.hc (Restated.switchRound M S tE)))) →
      M.awake_for_grade1 (Setup.alwaysAwake S) y (Restated.runAllPath M S Sched x v N j y)
        (M.round_of S.hc (M.opening_slot S.hc (Restated.switchRound M S tE))) :=
    fun y hy j hj => hf.awake_g1 _ _ j _ (Or.inr rfl) hj hy hwinW
  have hconfHor : M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE))) ≤
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } :
        Record.Run V).horizon := by
    show _ ≤ (x[N].time : Int)
    rw [hN]
    exact facts.sch.confirmation_time_mono_l78 S (Nat.le_add_right _ 2)
  have hvoteHorO : M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE))) ≤
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } :
        Record.Run V).horizon :=
    (facts.sch.Protocol_vote_time_le_confirmation_time S.E _).trans hconfHor
  have hTCfg : Block.Preceq T.erase Cfg.erase := by
    rw [hreg.seed.checkpointDerived]
    exact facts.csAdded.derive_named_T_h_preceq S.E S.cfg Cfg
  have htail : ∀ y ∈ notHeldAt Sched
      (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)))),
      y ∈ S.E.committee ((M.opening_slot S.hc (Restated.switchRound M S tE))) →
      ∀ (H : Block V) (Hy : NamedBlock V), Hy.erase = H →
      Restated.RunBlockOn M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N) Finset.univ Hy →
      Restated.Vocabulary.Execution.NamedRun.emits M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v N) y
        (NamedObject.gfVote ⟨y, (M.opening_slot S.hc (Restated.switchRound M S tE)), H.root⟩)
        (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)))) →
      Block.Preceq T.erase H →
      Restated.BasePreviousRoundSGCompatibleWithAnchor M S Sched x v tE N
        (Restated.runAllPath M S Sched x v N) T := by
    intro y hyVote hycomm H Hy hHyErase hHyRun hHyEmit hTy
    unfold Restated.BasePreviousRoundSGCompatibleWithAnchor
    intro u hu nu hnu D hD hemit gc stu k A2' hA2' G' hG'
    obtain ⟨nprev, hnprev, hnprevu⟩ := (p80% exists_actionReads_choice₈₀) facts (Setup.alwaysAwake S)
      (Restated.runAllPath M S Sched x v N
        (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
          (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE - 1))))
      (Restated.switchRound M S tE - 1) u nu hnu
    have hPu := hP nprev hnprev u hu
    rw [hnprevu] at hPu
    obtain ⟨X, hXu, hXrun, hXemit⟩ := hPu D hD hemit A2' hA2' G' hG' y hyVote hycomm
    have hXH : X.erase = Hy.erase :=
      Restated.runBlock_eq_of_root_eqOn facts _ Finset.univ hf.rootCollisionFree hXrun hHyRun (by
        rw [hHyErase]
        exact congrArg GoldfishVote.head
          (Restated.emits_gfVote_uniqueOn facts (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ hf hXemit
            hHyEmit rfl))
    rw [hXH, hHyErase] at hXu
    exact compatible_of_preceq_common_Preceq hXu hTy
  have hmemWa := (p69b% mem_stateBeforeTime_along₆₉b) hf.sorted hf.onePath
    (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) a.round)
  obtain ⟨na, hna⟩ := (p73% actionReadFrom_nonempty₇₃) facts (Setup.alwaysAwake S)
    (Restated.runAllPath M S Sched x v N
      (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
        (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) a.round)) a.val_index) a.round
  obtain ⟨oQ, hoQ⟩ := (p70% nodeQ2_nonempty₇₀w) facts (Setup.alwaysAwake S) na a.round
  obtain ⟨Q, hQeq⟩ := hreg.seed.exists_nodeQ2_l70 facts na hna oQ hoQ
  rw [hQeq] at hoQ
  obtain ⟨oB, hoB⟩ := (p63% actionFGSource_nonempty₆₃w) facts (Setup.alwaysAwake S) na
  rw [hreg.seed.exactFGSource na hna oB hoB] at hoB
  have hsplit := Restated.Vocabulary.Proofs.HealingSurface.actionFGSource_genuineClear_or_selectedG2_named facts
    (Setup.alwaysAwake S) _ a.val_index a.round _ hmemWa na hna hoQ hoB
  rcases hsplit with ⟨Ca, hCa, -, -, -, hCfgCa⟩ | hCfgQ
  · -- case: `Cfg` is a clear block, an ancestor of the confirmation `Ca` (satisfying `GenuineConfirmation`)
    have hsigner : a.val_index ∈ notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))) := by
      have h := hreg.seed.signerHonest
      rw [hreg.seed.actionTime_eq, harW] at h
      exact h
    obtain ⟨ca, hca, sta, -, rfl⟩ := hna
    rw [facts.nd.mkNode_cache] at hCa
    have hca' : M.onPhaseTick S.E S.hc
        (Restated.runAllPath M S Sched x v N
          (Restated.strictEventIndex
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
            (Restated.Vocabulary.Execution.Setup.a M S a.round)) a.val_index).st.core.toHealing
        (Restated.Vocabulary.Execution.Setup.a M S a.round)
        (Restated.runAllPath M S Sched x v N
          (Restated.strictEventIndex
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
            (Restated.Vocabulary.Execution.Setup.a M S a.round)) a.val_index).cache ⇢ ca := hca
    have hCa' : Restated.Vocabulary.Protocol.GenuineConfirmationWith M (M.gradeContract ca) S.E S.hc
        (Restated.Vocabulary.Proofs.Optimistic.tickStore M (Setup.alwaysAwake S)
          (Restated.runAllPath M S Sched x v N
            (Restated.strictEventIndex
              ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
              (Restated.Vocabulary.Execution.Setup.a M S a.round)) a.val_index).st.core
          (M.confirmation_time S.E (M.opening_slot S.hc a.round)))
        (M.opening_slot S.hc a.round) Ca := hCa
    rw [harW, hSc] at hca' hCa'
    obtain ⟨y, hy, hycomm, hCy⟩ :=
      Restated.genuineConfirmation_exists_honestVoteSupporter_ceilingOn facts (Setup.alwaysAwake S)
        (notHeldAt Sched) Finset.univ hf hHs hHsXb hcomOn (hHs _ _ hcut hsigner) hoPos hpostVote
        hconfHor ca hca' hCa'
        (fun y _ hy j hj => hrunY y
          (hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E _) hy) j hj)
    have hyVote : y ∈ notHeldAt Sched
        (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)))) :=
      hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E _) hy
    obtain ⟨cc, hcc, Tr, hTr, L, hL, L', hL', H, hH⟩ := (p78% exists_voteHead₇₈) facts (Setup.alwaysAwake S)
      (Restated.runAllPath M S Sched x v N
        (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
          (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE))))) y)
      ((M.opening_slot S.hc (Restated.switchRound M S tE)))
    obtain ⟨Hy, hHyErase, hHyRun⟩ := Restated.seedVoteDutyHead_runBlockOn facts (Setup.alwaysAwake S)
      (notHeldAt Sched) Finset.univ hf (hHsXb _ hyVote) ((M.opening_slot S.hc (Restated.switchRound M S tE)))
      cc hcc Tr hTr L hL L' hL' H hH
    have hHyEmit := Restated.seedVoteDutyHead_emitsOn facts (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ
      hf hyVote hoPos hycomm hvoteHorO hpostVote cc hcc (hrunY y hyVote) Tr hTr L hL L' hL' H hH
    exact htail y hyVote hycomm H Hy hHyErase hHyRun hHyEmit
      (preceq_trans_Preceq (preceq_trans_Preceq hTCfg hCfgCa) (hCy cc hcc Tr hTr L hL L' hL' H hH))
  · -- case: `Cfg` is the selected grade-2 block
    rw [← hCfgQ] at hoQ
    have hpositive : 0 < (((Setup.alwaysAwake S).E.committee
        ((M.opening_slot S.hc (Restated.switchRound M S tE)))) ∩
        notHeldAt Sched (M.confirmation_time (Setup.alwaysAwake S).E
          ((M.opening_slot S.hc (Restated.switchRound M S tE))))).card := by
      have hc := hcomOn ((M.opening_slot S.hc (Restated.switchRound M S tE)))
      omega
    obtain ⟨y, hyI⟩ := Finset.card_pos.mp hpositive
    have hycomm : y ∈ S.E.committee ((M.opening_slot S.hc (Restated.switchRound M S tE))) :=
      (Finset.mem_inter.mp hyI).1
    have hyVote : y ∈ notHeldAt Sched
        (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)))) :=
      hHs _ _ (facts.sch.Protocol_vote_time_le_confirmation_time S.E _) (Finset.mem_inter.mp hyI).2
    have hyA : y ∈ notHeldAt Sched
        (M.vote_time S.E ((M.opening_slot S.hc a.round))) := by
      rw [harW]
      exact hyVote
    have hCfgy := hreg.seed.selectedSource_preceq_openingHead_of_namedFrame_history facts hf hHs
      hHsXb hX hXXb hreg.crossing hreg.frame hreg.ready hna hoQ hyA hlo
    rw [harW] at hCfgy
    obtain ⟨cc, hcc, Tr, hTr, L, hL, L', hL', H, hH⟩ := (p78% exists_voteHead₇₈) facts (Setup.alwaysAwake S)
      (Restated.runAllPath M S Sched x v N
        (Restated.strictEventIndex
          ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
          (M.vote_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE))))) y)
      ((M.opening_slot S.hc (Restated.switchRound M S tE)))
    obtain ⟨Hy, hHyErase, hHyRun⟩ := Restated.seedVoteDutyHead_runBlockOn facts (Setup.alwaysAwake S)
      (notHeldAt Sched) Finset.univ hf (hHsXb _ hyVote) ((M.opening_slot S.hc (Restated.switchRound M S tE)))
      cc hcc Tr hTr L hL L' hL' H hH
    have hHyEmit := Restated.seedVoteDutyHead_emitsOn facts (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ
      hf hyVote hoPos hycomm hvoteHorO hpostVote cc hcc (hrunY y hyVote) Tr hTr L hL L' hL' H hH
    exact htail y hyVote hycomm H Hy hHyErase hHyRun hHyEmit
      (preceq_trans_Preceq hTCfg (hCfgy cc hcc Tr hTr L hL L' hL' H hH))

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

/-- In the regime `hreg` along `runAllPath M S Sched x v N`, with `rW = switchRound M S tE`,
    synchrony assumed only up to `x[N].time`, and `hP`: the round-`rW` SG blocks of any two
    validators in `notHeldAt Sched` at `S.a rW` lie on one chain (`BaseSGOneChainAtSwitchRound`). -/
theorem baseSGOneChainAtSwitchRound_of_premises_upTo (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v : V)
    {tGAT tE : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWakeBefore M S x
      (M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 2))) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (htd : Restated.TimeDiverges M x)
    {N : Nat}
    (hN : (x[N].time : Int)
      = M.confirmation_time S.E ((M.opening_slot S.hc (Restated.switchRound M S tE)) + 2))
    {blocked : Height} {first i : Nat} {a : NamedAttestation V} {ta : Int}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hreg : Restated.NamedHeightRegimeRunOn M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v N)
      (fun t => Restated.runAllPath M S Sched x v N (Restated.strictEventIndex
        ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V) t))
      (notHeldAt Sched) Finset.univ Finset.univ
      (Restated.roundAt M S tGAT + S.hc.η_SG + 2) blocked first i a ta Cfg T Tprev c0)
    (harW : a.round ≤ Restated.switchRound M S tE)
    {n₀ : Nat} (hn₀ : Restated.tickStepAt M x n₀ ((Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE))))
    (htop : Restated.topHonestRow M S Sched x n₀ ≤ (M.derive_named S.E S.cfg T).h)
    (hP : ∀ nprev : V → M.N,
      (∀ u : V, nprev u ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (Restated.runAllPath M S Sched x v N
          (Restated.strictEventIndex
            ({ Restated.runAll M S Sched x v N with honest := notHeldAt Sched (x[N].time : Int) } : Record.Run V)
            (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE - 1))) u)
        (Restated.switchRound M S tE - 1)) →
      Restated.BasePreviousRoundSGBelowOpeningVotes M S Sched x v tE N
        (Restated.runAllPath M S Sched x v N) nprev) :
    Restated.BaseSGOneChainAtSwitchRound M S Sched x v tE N :=
  Restated.baseSGOneChainAtSwitchRound_of_prevCompatible_upTo facts S Sched x v hsync hmono hawake hgst hcv hvalid
    hawm hthird hcom hlen htd hN hreg harW hn₀ htop hP
    (fun heq => Restated.basePreviousRoundSGCompatibleWithAnchor_of_belowOpeningVotes_upTo facts S Sched x v hsync
      hmono hawake hgst hcv hvalid hawm hthird hcom hlen htd hN hreg heq hP)

end

end DecoupledConsensusModel.Sts.Restated
