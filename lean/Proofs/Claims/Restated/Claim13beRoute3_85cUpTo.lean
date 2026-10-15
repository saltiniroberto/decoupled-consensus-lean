import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bInvariantActiveSinceW
import Proofs.Claims.Restated.Claim13bInvariantActiveSinceWUpTo
import Proofs.Claims.Restated.Claim13bStepConeIter
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13beRoute3_44
import Proofs.Claims.Restated.Claim13beRoute3_44UpTo
import Proofs.Claims.Restated.Claim13beRoute3_51
import Proofs.Claims.Restated.Claim13beRoute3_71
import Proofs.Claims.Restated.Claim13beRoute3_72
import Proofs.Claims.Restated.Claim13beRoute3_76
import Proofs.Claims.Restated.Claim13beRoute3_83
import Proofs.Claims.Restated.Claim13beRoute3_83UpTo
import Proofs.Claims.Restated.Claim13beRoute3_85bUpTo
import Proofs.Claims.Restated.Claim13beRoute3_85c
import Proofs.Claims.Restated.Claim13beRoute3_88UpTo
import Proofs.Claims.Restated.Claim13beRoute3_91UpTo
import Proofs.Claims.Restated.Vocabulary_Execution_EmissionShape
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Proofs.Claims.Restated.Vocabulary_Protocol_Schedule_PostHealingContinuation
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActiveSinceW
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13beRoute3_42
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.Claim13beRoute3_72
import Model.Conditions.Claim13beRoute3_74
import Model.Conditions.Claim13beRoute3_83
import Model.Conditions.ClaimAsyncK_DeliveryUpTo
import Model.Conditions.RunAll
import Model.Conditions.RunVocabulary
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13bd
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Protocol_NamedStoreReads
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Statements_Instantiation_Proposals
import Model.Record.Wiring

/-!
# Honest attestation rows at the FG source's height, with bounded synchrony

The theorems of `Claim13beRoute3_85c.lean` along the path an execution follows, with synchrony
assumed only up to `x[n].time` or the phase end `tE`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

local macro "p51% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_51)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p58% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_58)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p71% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_71)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "p85c% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_85c)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel.Proofs.HealingLemmas

/-- With synchrony assumed only up to `tE`, in the run of the execution `x` up to step `n`, if `T_0`
    is an anchor at the re-based deadline round, `x[n].time` is at most the switch round's action
    instant and `h(T_0) ≤ H`, then any two attestations emitted along the execution's path by
    validators not held at their instants, with votes at height `H`, name the same entry root. -/
theorem honestVotes_oneEntry_runAll_l85c_upTo (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v₀ : V) (n : Nat)
    {tGAT tE : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWakeBefore M S x tE) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    (hlen : tGAT + (Restated.healingLengthη M S gap + (Restated.constants M S).period) ≤ tE) (htd : Restated.TimeDiverges M x)
    {T_0 : NamedBlock V}
    (hA0 : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.rebasedDeadlineRoundW M S tGAT gap) T_0)
    (hnW : (x[n].time : Int) ≤ (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)))
    {H : Height} (htop : (M.derive_named S.E S.cfg T_0).h ≤ H) :
    ∀ (w₁ w₂ : V) (t₁ t₂ : Int) (a₁ a₂ : NamedAttestation V) (e₁ e₂ : BlockId) (b₁ b₂ : Bool),
      Restated.Vocabulary.Execution.NamedRun.emits M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v₀ n) w₁ (Object.attest a₁) t₁ →
      w₁ ∈ notHeldAt Sched t₁ → a₁.height_pair = .vote H e₁ b₁ →
      Restated.Vocabulary.Execution.NamedRun.emits M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v₀ n) w₂ (Object.attest a₂) t₂ →
      w₂ ∈ notHeldAt Sched t₂ → a₂.height_pair = .vote H e₂ b₂ → e₁ = e₂ := by
  have hlen' : tGAT + Restated.healingLengthη M S gap ≤ tE := Restated.healingLength_le_of_kit_l76 facts S hlen
  have hrW : Restated.rebasedDeadlineRoundW M S tGAT gap ≤ Restated.switchRound M S tE :=
    Restated.rebasedDeadlineRoundW_le_switchRound facts S tGAT tE gap (Restated.runAll M S Sched x v₀ 0) hgst hlen'
  have hrD : Restated.deadlineRoundW M S tGAT gap ≤ Restated.switchRound M S tE :=
    (Restated.deadlineRoundW_le_rebased facts S tGAT gap).trans hrW
  obtain ⟨-, hWE⟩ := Restated.window_in_phase_atRound facts S tGAT tE gap hgst hlen' hrD le_rfl
  have hn : (x[n].time : Int) ≤ tE := hnW.trans hWE
  have hf := Restated.admissibleFieldsOn_runAll_notHeld_upTo facts S Sched x v₀ n (fun k w sm hsend hle haw => hsync k w sm hsend (le_trans hle hn) haw) hmono hawake hgst hcv hvalid
    hawm hthird hn
  obtain ⟨T_W, hAW⟩ := Restated.exists_anchorAtRound_upTo facts S Sched x hsync hmono hawake hgst hcv hvalid hawm
    hthird hcom hrec hlen' htd hrD le_rfl
  obtain ⟨n_W, hnWt⟩ := Restated.exists_tickStepAt facts x htd (Restated.action_pos facts S (Restated.switchRound M S tE))
  have hprev := Restated.basePreviousRoundSGCompatibleWithAnchor_atRound_upTo facts S Sched x tGAT tE gap hlen hgst
    hmono hvalid hsync hawm hcv hcom hthird hawake hrec
  have hclear := Restated.baseClearFGSource_atRound_of_premises_upTo facts (gap := gap) S Sched x tGAT tE hgst hmono
    hvalid hsync hawm hcv hcom hthird hawake
  have hun := Restated.honestVotes_onAnchorChain_since_roundW_upTo facts S Sched x hsync hmono hawake hgst hcv hvalid
    hawm hthird hcom hrec hlen' htd (Restated.deadlineRoundW_le_rebased facts S tGAT gap) hrW
    (fun r hr1 hr2 => hprev r hr1 hr2)
    (fun r hr1 hr2 => hclear r ((Restated.deadlineRoundW_le_rebased facts S tGAT gap).trans hr1) hr2)
    hA0 hAW hnWt
  have hzero : ∃ u : V, u ∉ Sched.adv 0 :=
    exists_notHeld_zero S Sched hthird (le_trans (Int.natCast_nonneg _) hn)
  have hunder : ∀ (w : V) (t : Int) (a : NamedAttestation V) (e : BlockId) (b : Bool),
      Restated.Vocabulary.Execution.NamedRun.emits M (Setup.alwaysAwake S)
        ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } : Record.Run V)
        (Restated.runAllPath M S Sched x v₀ n) w (Object.attest a) t →
      w ∈ notHeldAt Sched t → a.height_pair = .vote H e b →
      ∃ E₀ : NamedBlock V, Restated.RunBlockOn M (Setup.alwaysAwake S)
          ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } : Record.Run V)
          (Restated.runAllPath M S Sched x v₀ n) Finset.univ E₀ ∧ E₀.root = e ∧
        (M.derive_named S.E S.cfg E₀).h = H ∧
        (M.derive_named S.E S.cfg E₀).T_h = E₀.erase ∧
        Block.Preceq E₀.erase T_W.erase := by
    intro w t a e b hem hw hp
    obtain ⟨E₀, hE₀run, hE₀root, hE₀h, hE₀T⟩ := Restated.emittedVote_entry_l85c facts (Setup.alwaysAwake S)
      (notHeldAt Sched) Finset.univ hf (fun _ => Finset.subset_univ _) hem hw hp
    obtain ⟨k, hkn, hk, hsent⟩ := Restated.mem_sent_of_emits_runAll facts S Sched x v₀ hem
    obtain ⟨hk1, hk0⟩ := Restated.tickStepAt_time facts x hk
    obtain ⟨hW1, -⟩ := Restated.tickStepAt_time facts x hnWt
    have hkW : k + 1 ≤ n_W + 1 := by
      by_contra hlt
      have h1 : (x[n_W + 1].time : Int) ≤ x[k].time := Restated.time_mono_int facts S Sched x (by omega)
      have h2 : (x[k + 1].time : Int) ≤ x[n].time := Restated.time_mono_int facts S Sched x (by omega)
      omega
    have hval : a.val_index = w :=
      (Restated.Vocabulary.Proofs.Optimistic.emits_attest_shape facts _ _ hf.onePath hem).1
    have hhon : Restated.HonestThrough M Sched x (k + 1) w := by
      intro t' ht' hadv
      exact (mem_notHeldAt.1 hw) (hmono t' t (by rw [← hk1]; exact ht') hadv)
    have hlog := Restated.blockInLog_of_blockInRunOn_univ facts S Sched x v₀ _ n hmono hzero hE₀run
    exact ⟨E₀, hE₀run, hE₀root, hE₀h, hE₀T,
      hun w (k + 1) a H e b hkW hhon hval hsent hp htop E₀ hlog hE₀root⟩
  intro w₁ w₂ t₁ t₂ a₁ a₂ e₁ e₂ b₁ b₂ hem₁ hw₁ hp₁ hem₂ hw₂ hp₂
  obtain ⟨E₁, hE₁run, hE₁root, hE₁h, hE₁T, hE₁W⟩ := hunder w₁ t₁ a₁ e₁ b₁ hem₁ hw₁ hp₁
  obtain ⟨E₂, hE₂run, hE₂root, hE₂h, hE₂T, hE₂W⟩ := hunder w₂ t₂ a₂ e₂ b₂ hem₂ hw₂ hp₂
  rw [← hE₁root, ← hE₂root]
  exact Restated.entryRoot_eq_of_underCommon_l85c facts (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ hf
    hE₁run hE₂run (hE₁h.trans hE₂h.symm) hE₁T hE₂T hE₁W hE₂W

/-- With synchrony assumed only up to `tE`, in the run of the execution `x` up to step `n`, with
    `T_0` an anchor at the re-based deadline round and `x[n].time` at most the switch round's action
    instant: for a round `q` with `tGAT + 1 ≤ S.a q` within the horizon, a run block `P` with
    `h(T_0) ≤ h(P)`, and `u` not held at `S.a q` that passes the grade-2 awake test of round `q`,
    every round-`q` attestation of `u` at an action node state whose FG source can return `P`'s
    erasure is either `vote h(P) T_h(P) b`, with `b = false` when `nj(P) = false`, or empty, with
    `u`'s own lock at `h(P)` naming a block other than `T_h(P)` and `h(P)` at most `u`'s justified
    height strictly before `S.a q`. -/
theorem honestRow_atSourceHeight_runAll_l85c_upTo (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v₀ : V) (n : Nat)
    {tGAT tE : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWakeBefore M S x tE) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    (hlen : tGAT + (Restated.healingLengthη M S gap + (Restated.constants M S).period) ≤ tE) (htd : Restated.TimeDiverges M x)
    {T_0 : NamedBlock V}
    (hA0 : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.rebasedDeadlineRoundW M S tGAT gap) T_0)
    (hnW : (x[n].time : Int) ≤ (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)))
    {q : Round}
    (hhor : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) q) ≤
      ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } :
        Record.Run V).horizon)
    (hgat : tGAT + 1 ≤ (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) q))
    {P : NamedBlock V}
    (hPrun : Restated.RunBlockOn M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v₀ n) Finset.univ P)
    (htop : (M.derive_named S.E S.cfg T_0).h ≤ (M.derive_named S.E S.cfg P).h)
    {u : V} (hu : u ∈ notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) q)))
    -- `u`'s node state before each of its ticks at `S.a q` passes the grade-2 awake test of round
    -- `q`.
    (hrun : ∀ j : Nat,
      ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } :
        Record.Run V).events[j]? =
        some (Record.Event.tick u (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) q)) →
      M.awake_for_grade2 (Setup.alwaysAwake S) u (Restated.runAllPath M S Sched x v₀ n j u) q) :
    ∀ nu ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
      (Restated.runAllPath M S Sched x v₀ n
        (strictEventIndex
          ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } : Record.Run V)
          (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) q)) u) q,
    Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M (Setup.alwaysAwake S) nu ⇢ some P.erase →
    ∀ D, M.duties_attest_with (M.gradeContract nu.cache) S.E S.hc ((Setup.alwaysAwake S).node u)
      nu.st nu.record ⇢ D →
    ((D.2.2.height_pair =
          .vote (M.derive_named S.E S.cfg P).h
            (M.derive_named S.E S.cfg P).T_h.root false ∨
        D.2.2.height_pair =
          .vote (M.derive_named S.E S.cfg P).h
            (M.derive_named S.E S.cfg P).T_h.root true) ∧
      ((M.derive_named S.E S.cfg P).nj = false →
        D.2.2.height_pair =
          .vote (M.derive_named S.E S.cfg P).h
            (M.derive_named S.E S.cfg P).T_h.root false)) ∨
    (D.2.2.height_pair = .empty ∧
      ∃ locked : BlockId,
        M.own_lock
            (Restated.runAllPath M S Sched x v₀ n
              (strictEventIndex
                ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } : Record.Run V)
                (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) q)) u).record.legacy
            (M.derive_named S.E S.cfg P).h
            D.2.2.finality_pair = some locked ∧
        locked ≠ (M.derive_named S.E S.cfg P).T_h.root ∧
        (M.derive_named S.E S.cfg P).h ≤
          (Restated.runAllPath M S Sched x v₀ n
            (strictEventIndex
              ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } : Record.Run V)
              (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) q)) u).st.core.h_j) := by
  have hlen' : tGAT + Restated.healingLengthη M S gap ≤ tE := Restated.healingLength_le_of_kit_l76 facts S hlen
  have hrW : Restated.rebasedDeadlineRoundW M S tGAT gap ≤ Restated.switchRound M S tE :=
    Restated.rebasedDeadlineRoundW_le_switchRound facts S tGAT tE gap (Restated.runAll M S Sched x v₀ 0) hgst hlen'
  have hrD : Restated.deadlineRoundW M S tGAT gap ≤ Restated.switchRound M S tE :=
    (Restated.deadlineRoundW_le_rebased facts S tGAT gap).trans hrW
  obtain ⟨-, hWE⟩ := Restated.window_in_phase_atRound facts S tGAT tE gap hgst hlen' hrD le_rfl
  have hn : (x[n].time : Int) ≤ tE := hnW.trans hWE
  have hf := Restated.admissibleFieldsOn_runAll_notHeld_upTo facts S Sched x v₀ n (fun k w sm hsend hle haw => hsync k w sm hsend (le_trans hle hn) haw) hmono hawake hgst hcv hvalid
    hawm hthird hn
  have hagree := Restated.honestVotes_oneEntry_runAll_l85c_upTo facts S Sched x v₀ n hsync hmono hawake hgst hcv
    hvalid hawm hthird hcom hrec hlen htd hA0 hnW htop
  exact Restated.honestRow_atSource_engine_l85c facts (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ hf
    (fun _ _ h => notHeldAt_anti hmono h) (fun _ => Finset.subset_univ _) hPrun hagree hu hhor
    hgat hrun

/-- With synchrony assumed only up to `x[n].time`, in the run of the execution `x` up to step `n`,
    along its path `W`: let `C` be a run block at height `H` with entry root `T`, an ancestor of the
    parent of a slot-`s` proposal `B` at height `H`, with `tGAT + 1 ≤ S.a r`,
    `S.a r + Δ ≤ proposal_time s ≤ x[n].time`, the proposer not held at `S.a r + Δ`, round `r` in
    the row window of the proposer's read, and `v` not held at `proposal_time s` and passing the
    grade-2 awake test of round `r`. Then every round-`r` attestation of `v` at an action node state
    whose FG source can return `C`'s erasure that carries `(H, T)` as a vote or a timeout is on the
    named chain of `B`'s parent with `v` in its progress set (and in its target participation for a
    target vote), or among `B`'s own attestations. -/
theorem honestRow_coveredAtProposal_runAll_l85c_upTo (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v₀ : V) (n : Nat)
    {tGAT tAwakeEnd : Int}
    (hsync : Restated.SynchronyFromWakeBefore M S x (x[n].time : Int)) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tAwakeEnd → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tAwakeEnd →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hn : (x[n].time : Int) ≤ tAwakeEnd)
    {r : Round} {C : NamedBlock V} {H : Height} {T : BlockId}
    (hCrun : Restated.RunBlockOn M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v₀ n) Finset.univ C)
    (hCheight : (M.derive_named S.E S.cfg C).h = H)
    (hCtarget : (M.derive_named S.E S.cfg C).T_h.root = T)
    {s : Slot} {B : NamedBlock V}
    (hCP : NamedBlock.Preceq C B.parent)
    (hPheight : (M.derive_named S.E S.cfg B.parent).h = H)
    (hprop : S.E.proposer s ∈ notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) r) + S.E.Δ))
    (hhor : M.proposal_time S.E s ≤
      ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } :
        Record.Run V).horizon)
    (hpost : tGAT + 1 ≤ (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) r))
    (hdelay : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) r) + S.E.Δ ≤ M.proposal_time S.E s)
    {v : V} (hv : v ∈ notHeldAt Sched (M.proposal_time S.E s))
    -- `v`'s node state before each of its ticks at `S.a r` passes the grade-2 awake test of round
    -- `r`.
    (hrun : ∀ j : Nat,
      ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } :
        Record.Run V).events[j]? =
        some (Record.Event.tick v (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) r)) →
      M.awake_for_grade2 (Setup.alwaysAwake S) v (Restated.runAllPath M S Sched x v₀ n j v) r) :
    let R : Record.Run V :=
      { Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) }
    let W := Restated.runAllPath M S Sched x v₀ n
    let wb := W (strictEventIndex R (M.proposal_time S.E s)) (S.E.proposer s)
    ∀ cb : M.Cache,
      M.onPhaseTick S.E S.hc wb.st.core.toHealing (M.proposal_time S.E s) wb.cache ⇢ cb →
      let pnb := M.mkNode (M.ns_setClock S.E wb.st (M.proposal_time S.E s)) wb.record cb
      M.proposal_with (M.gradeContract cb) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer s)) pnb.st ⇢ some B →
      M.inWindow S.hc pnb.st.core r = true →
    ∀ nv ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
      (W (strictEventIndex R (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) r)) v) r,
    Restated.Vocabulary.Proofs.HealingSurface.actionFGSource M (Setup.alwaysAwake S) nv ⇢ some C.erase →
    ∀ D, M.duties_attest_with (M.gradeContract nv.cache) S.E S.hc ((Setup.alwaysAwake S).node v)
      nv.st nv.record ⇢ D →
    (D.2.2.height_pair = .vote H T false ∨ D.2.2.height_pair = .vote H T true) →
    ((D.2.2 ∈ Protocol.named_chain_attestations B.parent ∧
        v ∈ (M.derive_named S.E S.cfg B.parent).progress ∧
        (D.2.2.height_pair = .vote H T false →
          v ∈ (M.derive_named S.E S.cfg B.parent).target_participation)) ∨
      D.2.2 ∈ B.attestations) := by
  intro R W wb cb hcb pnb hB hinWindow nv hnv hsrc D hD hpair
  have hf := Restated.admissibleFieldsOn_runAll_notHeld_upTo facts S Sched x v₀ n hsync hmono hawake hgst hcv hvalid
    hawm hthird hn
  obtain ⟨hCpre, -⟩ := Restated.sourceBody_of_actionFGSource_l85c facts (Setup.alwaysAwake S) (notHeldAt Sched)
    Finset.univ hf (Finset.mem_univ v) hCrun hnv hsrc
  have hst : pnb.st = M.store_with_cache (M.ns_setClock S.E wb.st (M.proposal_time S.E s)) cb :=
    facts.nd.mkNode_st _ _ _
  rw [hst, facts.dt.proposal_with_store_with_cache] at hB
  rw [hst] at hinWindow
  simp only [facts.nd.store_with_cache_bodies, facts.nd.store_with_cache_sg_rows, facts.nd.store_with_cache_core_T, facts.nd.store_with_cache_core_F, facts.nd.store_with_cache_core_J, facts.nd.store_with_cache_core_s, facts.nd.store_with_cache_core_t, facts.nd.store_with_cache_core_h_max, facts.nd.store_with_cache_core_h_j, facts.nd.store_with_cache_core_σ, facts.nd.store_with_cache_core_timestamp_block, facts.nd.store_with_cache_core_timestamp_vote, facts.nd.store_with_cache_core_timestamp_sg_vote, facts.nd.store_with_cache_core_gf_votes, facts.nd.store_with_cache_core_pool, facts.nd.store_with_cache_core_live_confirmed, facts.nd.store_with_cache_core_latest_confirmed, facts.nd.store_with_cache_core_latest_stable, facts.nd.store_with_cache_core_sg_votes, facts.nd.store_with_cache_core_sg_pool, facts.nd.store_with_cache_core_tau, facts.nd.store_with_cache_core_attestations, facts.nd.store_with_cache_get_fg_root, facts.nd.store_with_cache_get_filtered_block_tree, facts.nd.store_with_cache_voter_filtered_block_tree, facts.nd.store_with_cache_voter_processed_block_tree, facts.nd.store_with_cache_voter_view, facts.nd.store_with_cache_voter_support_view, facts.nd.store_with_cache_proposer_view, facts.nd.store_with_cache_proposer_support_view, facts.nd.store_with_cache_get_head_in_tree_with_layer, facts.nd.store_with_cache_get_head_in_tree_with, facts.nd.store_with_cache_grade2_block_with, facts.nd.store_with_cache_get_sg_vote_with, facts.nd.store_with_cache_onPhaseTick, facts.nd.store_with_cache_readFrame, facts.nd.store_with_cache_frameGradeRead, facts.nd.store_with_cache_currentSGVote, facts.nd.store_with_cache_inWindow, facts.nd.store_with_cache_store_pool, facts.nd.store_with_cache_gradeView] at hinWindow
  exact Restated.actionAttestationAt_coveredAtProposal_ofBodyOn_l85c facts (Setup.alwaysAwake S)
    (notHeldAt Sched) Finset.univ hf (fun _ _ h => notHeldAt_anti hmono h) hCheight hCtarget
    cb hcb hB hCP hPheight hprop hhor hpost hdelay hv hCpre hinWindow hrun nv hnv D hD hpair

/-- With synchrony assumed only up to `x[n].time`, in the run of the execution `x` up to step `n`,
    along its path `W`, for a round `c` at least two rounds after `deadlineRoundW S tGAT gap` within
    the horizon whose opening proposer is not held at the opening slot's confirmation instant: every
    proposal `P` of that proposer's read on `W` is a run block read through every validator, and
    `tGAT + 1 ≤ proposal_time (o_c) ≤ S.a c`. -/
theorem openingProposal_runBlock_runAll_l85c_upTo (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v₀ : V) (n : Nat)
    {tGAT tAwakeEnd : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWakeBefore M S x (x[n].time : Int)) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tAwakeEnd → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tAwakeEnd →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hn : (x[n].time : Int) ≤ tAwakeEnd)
    {c : Round} (hc : Restated.deadlineRoundW M S tGAT gap + 2 ≤ c)
    (hhor : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c) ≤
      ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } :
        Record.Run V).horizon)
    (hopening : S.E.proposer ((M.opening_slot S.hc c)) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c))))
    {P : NamedBlock V} :
    let R : Record.Run V :=
      { Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) }
    let W := Restated.runAllPath M S Sched x v₀ n
    let wp := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc c)))
      (S.E.proposer (M.opening_slot S.hc c))
    ∀ cp : M.Cache,
      M.onPhaseTick S.E S.hc wp.st.core.toHealing
        (M.proposal_time S.E (M.opening_slot S.hc c)) wp.cache ⇢ cp →
      let pn := M.mkNode (M.ns_setClock S.E wp.st (M.proposal_time S.E (M.opening_slot S.hc c)))
        wp.record cp
      M.proposal_with (M.gradeContract cp) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc c))) pn.st ⇢ some P →
    Restated.RunBlockOn M (Setup.alwaysAwake S) R W Finset.univ P ∧
      tGAT + 1 ≤ M.proposal_time S.E ((M.opening_slot S.hc c)) ∧
      M.proposal_time S.E ((M.opening_slot S.hc c)) ≤ (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c) := by
  intro R W wp cp hcp pn hP
  have hf := Restated.admissibleFieldsOn_runAll_notHeld_upTo facts S Sched x v₀ n hsync hmono hawake hgst hcv hvalid
    hawm hthird hn
  obtain ⟨-, htwo, -, hpos, -⟩ := facts.gr.openingSlots_l86f S hc
  have hstartPos : 0 < (M.opening_slot S.hc c) := Nat.lt_of_lt_of_le hpos (Nat.sub_le _ _)
  have hpropA : M.proposal_time S.E ((M.opening_slot S.hc c)) ≤ (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c) := by
    have h : M.confirmation_time S.E ((M.opening_slot S.hc c)) = (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c) :=
      Restated.confirmation_time_opening_slot facts (Setup.alwaysAwake S) c
    have h' := facts.sch.proposal_time_le_confirmation_time S.E ((M.opening_slot S.hc c))
    linarith
  have hlo : tGAT + 1 ≤ M.proposal_time S.E ((M.opening_slot S.hc c)) := by
    have h1 := Restated.roundAt_lo_le_rGST_l71 facts S tGAT
    have h2 : (Restated.Vocabulary.Execution.Setup.a M S (Restated.roundAt M S tGAT + S.hc.η_SG)) ≤ (Restated.Vocabulary.Execution.Setup.a M S (Restated.deadlineRoundW M S tGAT gap)) :=
      (Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone (Restated.rGST_le_deadlineRoundW_l85c facts S tGAT gap)
    have h3 := Restated.Vocabulary.Protocol.action_lt_proposal_time_two_after facts S (Restated.deadlineRoundW M S tGAT gap)
    have h4 := facts.sch.proposal_time_mono S.E htwo
    linarith
  have hst : pn.st = M.store_with_cache
      (M.ns_setClock S.E wp.st (M.proposal_time S.E (M.opening_slot S.hc c))) cp :=
    facts.nd.mkNode_st _ _ _
  rw [hst, facts.dt.proposal_with_store_with_cache] at hP
  have hwinC : tGAT + 1 ≤ M.early S.E S.hc c .g1 - S.E.Δ := by
    have h1 := Restated.roundAt_lo_le_rGST_l71 facts S tGAT
    have hlt : Restated.roundAt M S tGAT + S.hc.η_SG < c :=
      lt_of_le_of_lt (Restated.rGST_le_deadlineRoundW_l85c facts S tGAT gap)
        (lt_of_lt_of_le (Nat.lt_succ_self _) ((Nat.le_succ _).trans hc))
    have h2 := facts.gr.action_delta_le_early S S.hc.R_ge_three hlt
    have h3 := facts.gr.q10_early_g2_le_early_g1 S c
    have h4 : tGAT + 1 ≤ M.a S.hc S.E.Δ (Restated.roundAt M S tGAT + S.hc.η_SG) := h1
    linarith
  exact ⟨Restated.proposedBlock_runBlockOn facts (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ hf
    (fun _ _ h => notHeldAt_anti hmono h) (fun _ => Finset.subset_univ _) hstartPos hopening
    (hpropA.trans hhor) hlo (fun j hj => hf.tick_outcome j _ _ hj)
    (fun j hj => hf.awake_g1 _ _ j _ (Or.inl rfl) hj
      (notHeldAt_anti hmono (facts.sch.proposal_time_le_confirmation_time S.E _) hopening)
      (by
        show tGAT + 1 ≤ M.early S.E S.hc (M.round_of S.hc (M.opening_slot S.hc c)) .g1 - S.E.Δ
        rw [facts.gr.round_of_opening_slot_eq]; exact hwinC)) cp hcp hP, hlo, hpropA⟩

/-- With synchrony assumed only up to `tE`, in the run of the execution `x` up to step `n`, along
    its path `W`, for a round `c` at least three rounds after the deadline round with honest
    openings at `c` and `c − 1` proposing `P` and `P'`, with `S.a c ≤ x[n].time ≤ S.a rW`,
    `h(T_0) ≤ h(P)` and `u` not held at `S.a c`: every round-`c` attestation of `u` is either
    `vote h(P) T_h(P) b`, with `b = false` when `nj(P) = false`, or empty, with `u`'s own lock at
    `h(P)` naming a block other than `T_h(P)` and `h(P)` at most `u`'s justified height strictly
    before `S.a c`. -/
theorem honestRow_atOpening_runAll_l85c_upTo (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v₀ : V) (n : Nat)
    {tGAT tE : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWakeBefore M S x tE) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tE → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap)
    (hlen : tGAT + (Restated.healingLengthη M S gap + (Restated.constants M S).period) ≤ tE) (htd : Restated.TimeDiverges M x)
    {T_0 : NamedBlock V}
    (hA0 : Restated.AnchorAtRound M S Sched x tGAT tE (Restated.rebasedDeadlineRoundW M S tGAT gap) T_0)
    (hnW : (x[n].time : Int) ≤ (Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE)))
    {c : Round} (hc3 : Restated.deadlineRoundW M S tGAT gap + 3 ≤ c)
    (hhor : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c) ≤
      ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } :
        Record.Run V).horizon)
    (hopening : S.E.proposer ((M.opening_slot S.hc c)) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c))))
    (hopeningPrev : S.E.proposer ((M.opening_slot S.hc (c - 1))) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc (c - 1)))))
    {P P' : NamedBlock V}
    (htop : (M.derive_named S.E S.cfg T_0).h ≤ (M.derive_named S.E S.cfg P).h)
    {u : V} (hu : u ∈ notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c))) :
    let R : Record.Run V :=
      { Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) }
    let W := Restated.runAllPath M S Sched x v₀ n
    let wp := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc c)))
      (S.E.proposer (M.opening_slot S.hc c))
    let wp' := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc (c - 1))))
      (S.E.proposer (M.opening_slot S.hc (c - 1)))
    ∀ cp : M.Cache,
      M.onPhaseTick S.E S.hc wp.st.core.toHealing
        (M.proposal_time S.E (M.opening_slot S.hc c)) wp.cache ⇢ cp →
      let pn := M.mkNode (M.ns_setClock S.E wp.st (M.proposal_time S.E (M.opening_slot S.hc c)))
        wp.record cp
      M.proposal_with (M.gradeContract cp) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc c))) pn.st ⇢ some P →
    ∀ cp' : M.Cache,
      M.onPhaseTick S.E S.hc wp'.st.core.toHealing
        (M.proposal_time S.E (M.opening_slot S.hc (c - 1))) wp'.cache ⇢ cp' →
      let pn' := M.mkNode
        (M.ns_setClock S.E wp'.st (M.proposal_time S.E (M.opening_slot S.hc (c - 1))))
        wp'.record cp'
      M.proposal_with (M.gradeContract cp') .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc (c - 1)))) pn'.st ⇢ some P' →
    ∀ nu ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
      (W (strictEventIndex R (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c)) u) c,
    ∀ D, M.duties_attest_with (M.gradeContract nu.cache) S.E S.hc ((Setup.alwaysAwake S).node u)
      nu.st nu.record ⇢ D →
    ((D.2.2.height_pair =
          .vote (M.derive_named S.E S.cfg P).h
            (M.derive_named S.E S.cfg P).T_h.root false ∨
        D.2.2.height_pair =
          .vote (M.derive_named S.E S.cfg P).h
            (M.derive_named S.E S.cfg P).T_h.root true) ∧
      ((M.derive_named S.E S.cfg P).nj = false →
        D.2.2.height_pair =
          .vote (M.derive_named S.E S.cfg P).h
            (M.derive_named S.E S.cfg P).T_h.root false)) ∨
    (D.2.2.height_pair = .empty ∧
      ∃ locked : BlockId,
        M.own_lock
            (W (strictEventIndex R (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c)) u).record.legacy
            (M.derive_named S.E S.cfg P).h
            D.2.2.finality_pair = some locked ∧
        locked ≠ (M.derive_named S.E S.cfg P).T_h.root ∧
        (M.derive_named S.E S.cfg P).h ≤
          (W (strictEventIndex R (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c)) u).st.core.h_j) := by
  intro R W wp wp' cp hcp pn hP cp' hcp' pn' hP' nu hnu D hD
  have hlen' : tGAT + Restated.healingLengthη M S gap ≤ tE := Restated.healingLength_le_of_kit_l76 facts S hlen
  have hrW : Restated.rebasedDeadlineRoundW M S tGAT gap ≤ Restated.switchRound M S tE :=
    Restated.rebasedDeadlineRoundW_le_switchRound facts S tGAT tE gap (Restated.runAll M S Sched x v₀ 0) hgst hlen'
  have hrD : Restated.deadlineRoundW M S tGAT gap ≤ Restated.switchRound M S tE :=
    (Restated.deadlineRoundW_le_rebased facts S tGAT gap).trans hrW
  obtain ⟨-, hWE⟩ := Restated.window_in_phase_atRound facts S tGAT tE gap hgst hlen' hrD le_rfl
  have hn : (x[n].time : Int) ≤ tE := hnW.trans hWE
  obtain ⟨hPrun, hlo, hpropA⟩ := Restated.openingProposal_runBlock_runAll_l85c_upTo facts S Sched x v₀ n (fun k w sm hsend hle haw => hsync k w sm hsend (le_trans hle hn) haw) hmono
    hawake hgst hcv hvalid hawm hthird hn ((Nat.le_succ _).trans hc3) hhor hopening cp hcp hP
  obtain ⟨o, ho⟩ := (p51% actionFGSource_nonempty₅₁) facts (Setup.alwaysAwake S) nu
  have hsrc := Restated.fgSource_eq_openingProposal_runAll_notHeld_upTo facts S Sched x v₀ n (fun k w sm hsend hle haw => hsync k w sm hsend (le_trans hle hn) haw) hmono hawake hgst
    hcv hvalid hawm hthird hn hcom hrec hc3 hhor hopening hopeningPrev cp hcp hP cp' hcp' hP'
    u hu nu hnu o ho
  rw [hsrc] at ho
  have hkc : tGAT + 1 ≤ M.early S.E S.hc c .g2 - S.E.Δ :=
    Restated.lo_le_early_g2_sub_delta_of_action_lt facts S (Restated.roundAt_lo_le_rGST_l71 facts S tGAT)
      (lt_of_le_of_lt (Restated.rGST_le_deadlineRoundW_l85c facts S tGAT gap)
        (lt_of_lt_of_le (Nat.lt_succ_self _) ((Nat.le_add_right _ 2).trans hc3)))
  exact Restated.honestRow_atSourceHeight_runAll_l85c_upTo facts S Sched x v₀ n hsync hmono hawake hgst hcv hvalid
    hawm hthird hcom hrec hlen htd hA0 hnW hhor (hlo.trans hpropA) hPrun htop hu
    (fun j hj => Restated.awake_g2_action_runAllPath facts S Sched x v₀ n hmono hawake hn c hkc u j hj)
    nu hnu ho D hD

/-- With synchrony assumed only up to `x[n].time`, in the run of the execution `x` up to step `n`,
    along its path `W`, for a round `c` at least three rounds after the deadline round with honest
    openings at `c` and `c − 1` proposing `P` and `P'`: if `P` is an ancestor of the parent of a
    slot-`s` proposal `B` at height `h(P)`, the slot-`s` proposer is not held at `S.a c + Δ`,
    `S.a c + Δ ≤ proposal_time s ≤ x[n].time`, `v` is not held at `proposal_time s` and round `c` is
    in the row window of the proposer's read, then every round-`c` attestation of `v` that carries
    `(h(P), T_h(P))` as a vote or a timeout is on the named chain of `B`'s parent with `v` in its
    progress set (and in its target participation for a target vote), or among `B`'s own
    attestations. -/
theorem openingRow_coveredAtProposal_runAll_l85c_upTo (facts : Record.Facts M)
    (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched)
    (v₀ : V) (n : Nat)
    {tGAT tAwakeEnd : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWakeBefore M S x (x[n].time : Int)) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tAwakeEnd → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tAwakeEnd →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hn : (x[n].time : Int) ≤ tAwakeEnd)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tAwakeEnd gap)
    {c : Round} (hc3 : Restated.deadlineRoundW M S tGAT gap + 3 ≤ c)
    (hhor : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c) ≤
      ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } :
        Record.Run V).horizon)
    (hopening : S.E.proposer ((M.opening_slot S.hc c)) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c))))
    (hopeningPrev : S.E.proposer ((M.opening_slot S.hc (c - 1))) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc (c - 1)))))
    {P P' : NamedBlock V}
    {s : Slot} {B : NamedBlock V}
    (hPB : NamedBlock.Preceq P B.parent)
    (hBheight : (M.derive_named S.E S.cfg B.parent).h =
      (M.derive_named S.E S.cfg P).h)
    (hprop : S.E.proposer s ∈ notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c) + S.E.Δ))
    (hphor : M.proposal_time S.E s ≤
      ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } :
        Record.Run V).horizon)
    (hdelay : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c) + S.E.Δ ≤ M.proposal_time S.E s)
    {v : V} (hv : v ∈ notHeldAt Sched (M.proposal_time S.E s)) :
    let R : Record.Run V :=
      { Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) }
    let W := Restated.runAllPath M S Sched x v₀ n
    let wp := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc c)))
      (S.E.proposer (M.opening_slot S.hc c))
    let wp' := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc (c - 1))))
      (S.E.proposer (M.opening_slot S.hc (c - 1)))
    let wb := W (strictEventIndex R (M.proposal_time S.E s)) (S.E.proposer s)
    ∀ cp : M.Cache,
      M.onPhaseTick S.E S.hc wp.st.core.toHealing
        (M.proposal_time S.E (M.opening_slot S.hc c)) wp.cache ⇢ cp →
      let pn := M.mkNode (M.ns_setClock S.E wp.st (M.proposal_time S.E (M.opening_slot S.hc c)))
        wp.record cp
      M.proposal_with (M.gradeContract cp) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc c))) pn.st ⇢ some P →
    ∀ cp' : M.Cache,
      M.onPhaseTick S.E S.hc wp'.st.core.toHealing
        (M.proposal_time S.E (M.opening_slot S.hc (c - 1))) wp'.cache ⇢ cp' →
      let pn' := M.mkNode
        (M.ns_setClock S.E wp'.st (M.proposal_time S.E (M.opening_slot S.hc (c - 1))))
        wp'.record cp'
      M.proposal_with (M.gradeContract cp') .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc (c - 1)))) pn'.st ⇢ some P' →
    ∀ cb : M.Cache,
      M.onPhaseTick S.E S.hc wb.st.core.toHealing (M.proposal_time S.E s) wb.cache ⇢ cb →
      let pnb := M.mkNode (M.ns_setClock S.E wb.st (M.proposal_time S.E s)) wb.record cb
      M.proposal_with (M.gradeContract cb) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer s)) pnb.st ⇢ some B →
      M.inWindow S.hc pnb.st.core c = true →
    ∀ nv ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
      (W (strictEventIndex R (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c)) v) c,
    ∀ D, M.duties_attest_with (M.gradeContract nv.cache) S.E S.hc ((Setup.alwaysAwake S).node v)
      nv.st nv.record ⇢ D →
    (D.2.2.height_pair = .vote (M.derive_named S.E S.cfg P).h
          (M.derive_named S.E S.cfg P).T_h.root false ∨
      D.2.2.height_pair = .vote (M.derive_named S.E S.cfg P).h
          (M.derive_named S.E S.cfg P).T_h.root true) →
    ((D.2.2 ∈ Protocol.named_chain_attestations B.parent ∧
        v ∈ (M.derive_named S.E S.cfg B.parent).progress ∧
        (D.2.2.height_pair = .vote (M.derive_named S.E S.cfg P).h
            (M.derive_named S.E S.cfg P).T_h.root false →
          v ∈ (M.derive_named S.E S.cfg B.parent).target_participation)) ∨
      D.2.2 ∈ B.attestations) := by
  intro R W wp wp' wb cp hcp pn hP cp' hcp' pn' hP' cb hcb pnb hB hinWindow nv hnv D hD hpair
  obtain ⟨hPrun, hlo, hpropA⟩ := Restated.openingProposal_runBlock_runAll_l85c_upTo facts S Sched x v₀ n hsync hmono
    hawake hgst hcv hvalid hawm hthird hn ((Nat.le_succ _).trans hc3) hhor hopening cp hcp hP
  have hvA : v ∈ notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c)) :=
    notHeldAt_anti hmono ((le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans hdelay) hv
  obtain ⟨o, ho⟩ := (p51% actionFGSource_nonempty₅₁) facts (Setup.alwaysAwake S) nv
  have hsrc := Restated.fgSource_eq_openingProposal_runAll_notHeld_upTo facts S Sched x v₀ n hsync hmono hawake hgst
    hcv hvalid hawm hthird hn hcom hrec hc3 hhor hopening hopeningPrev cp hcp hP cp' hcp' hP'
    v hvA nv hnv o ho
  rw [hsrc] at ho
  have hkc : tGAT + 1 ≤ M.early S.E S.hc c .g2 - S.E.Δ :=
    Restated.lo_le_early_g2_sub_delta_of_action_lt facts S (Restated.roundAt_lo_le_rGST_l71 facts S tGAT)
      (lt_of_le_of_lt (Restated.rGST_le_deadlineRoundW_l85c facts S tGAT gap)
        (lt_of_lt_of_le (Nat.lt_succ_self _) ((Nat.le_add_right _ 2).trans hc3)))
  exact Restated.honestRow_coveredAtProposal_runAll_l85c_upTo facts S Sched x v₀ n hsync hmono hawake hgst hcv hvalid
    hawm hthird hn hPrun rfl rfl hPB hBheight hprop hphor (hlo.trans hpropA) hdelay hv
    (fun j hj => Restated.awake_g2_action_runAllPath facts S Sched x v₀ n hmono hawake hn c hkc v j hj)
    cb hcb hB hinWindow nv hnv ho D hD hpair

end

end DecoupledConsensusModel.Sts.Restated
