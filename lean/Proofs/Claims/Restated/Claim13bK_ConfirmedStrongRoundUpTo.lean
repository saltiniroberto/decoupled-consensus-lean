import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bK_ConfirmedStrongRound
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13beRoute3_44
import Proofs.Claims.Restated.Claim13beRoute3_44UpTo
import Proofs.Claims.Restated.Claim13beRoute3_46
import Proofs.Claims.Restated.Claim13beRoute3_48b
import Proofs.Claims.Restated.Claim13beRoute3_71
import Proofs.Claims.Restated.Claim13beRoute3_72
import Proofs.Claims.Restated.Claim13beRoute3_85b
import Proofs.Claims.Restated.Claim13beRoute3_85bUpTo
import Proofs.Claims.Restated.Vocabulary_Protocol_ChainState_ProposalBridge
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_GradePersistence
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.Claim13beRoute3_72
import Model.Conditions.ClaimAsyncK_DeliveryUpTo
import Model.Conditions.RunAll
import Model.Conditions.RunVocabulary
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13bd
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGradeQueries
import Model.Conditions.Vocabulary_Internal_Definitions_PhaseGrades
import Model.Conditions.Vocabulary_Internal_Internal_GradeReads
import Model.Conditions.Vocabulary_Internal_Legacy_Definitions_ActionSources
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Run
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Statements_Instantiation_Proposals
import Model.Record.Wiring
import Proofs.Claims.Spec2Claims.Claim13bModel_Preceq

/-!
# The stable root at a strong round, with synchrony up to the action time

The stable root a validator writes at its tick at round `c`'s action time is a descendant of the
proposal at the previous round's opening slot, and has no descendant in the tree the validator held
at the opening of the previous round, with synchrony assumed only up to `S.a c`. Stated over a model
`M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

/-- A private theorem of `Claim13beRoute3_64b`, by name. -/
local macro "p64b% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_64b)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- A private theorem of `Claim13beRoute3_58`, by name. -/
local macro "p58% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_58)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- A private theorem of `Claim13beRoute3_71`, by name. -/
local macro "p71% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_71)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Framework.StsMultisetLog
open scoped DC
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If `SynchronyFromWakeBefore` holds up to `b'` and `b ≤ b'`, it holds up to `b`. -/
private theorem SynchronyFromWakeBefore.monoU {S : Setup V} {Sched : Schedule V}
    {x : AtomicExec (Record.protocolOf M S) Sched} {b b' : Int}
    (hs : Restated.SynchronyFromWakeBefore M S x b') (facts : Record.Facts M) (hb : b ≤ b') :
    Restated.SynchronyFromWakeBefore M S x b :=
  fun k w sm hsend hle haw => hs k w sm hsend (le_trans hle hb) haw

omit [DecidableEq V] [Fintype V] in
/-- If `m` can return `a`, then `f <$> m` can return `f a`. -/
private theorem returns_map_intro_csr {α β : Type} (f : α → β) (m : DC.NDRE α) (a : α)
    (h : m ⇢ a) : (f <$> m) ⇢ f a := by
  unfold Record.Returns at h ⊢
  simp only [ExceptT.run_map, Set.fmap_eq_image, Set.mem_image]
  exact ⟨_, h, rfl⟩

/-- With synchrony assumed only up to `S.a c`: at a round `c` with
    `deadlineRoundW S tGAT gap + 3 ≤ c`, whose opening proposer and the previous round's are not
    held by the adversary at their opening slots' confirmation times, every proposal outcome of the
    proposer of `c − 1`'s opening slot is `some P'` for a named block `P'` of that slot, and every
    stable root `G` that a validator `v` not held at `S.a c` can use at its tick at `S.a c` is a
    descendant of `P'` or `P'` itself. -/
theorem stableRoot_preceq_prevOpeningProposal_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    {tGAT tAwakeEnd : Int} {gap : Nat} {c : Round}
    (hsync : Restated.SynchronyFromWakeBefore M S x
      ((Restated.Vocabulary.Execution.Setup.a M S c)))
    (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tAwakeEnd → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tAwakeEnd →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tAwakeEnd gap)
    (hc3 : Restated.deadlineRoundW M S tGAT gap + 3 ≤ c)
    (hopening : S.E.proposer ((M.opening_slot S.hc c)) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c))))
    (hopeningPrev : S.E.proposer ((M.opening_slot S.hc (c - 1))) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc (c - 1)))))
    {n : Nat} (hn : Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S c)))
    (hcE : (Restated.Vocabulary.Execution.Setup.a M S c) ≤ tAwakeEnd)
    {v : V} (hv : v ∉ Sched.adv ((Restated.Vocabulary.Execution.Setup.a M S c))) :
    let R : Record.Run V :=
      { Restated.runAll M S Sched x v (n + 1) with honest := notHeldAt Sched (x[n + 1].time : Int) }
    let W := Restated.runAllPath M S Sched x v (n + 1)
    let wp' := W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc (c - 1))))
      (S.E.proposer (M.opening_slot S.hc (c - 1)))
    ∀ cp' : M.Cache,
      M.onPhaseTick S.E S.hc wp'.st.core.toHealing
        (M.proposal_time S.E (M.opening_slot S.hc (c - 1))) wp'.cache ⇢ cp' →
      let pn' := M.mkNode
        (M.ns_setClock S.E wp'.st (M.proposal_time S.E (M.opening_slot S.hc (c - 1))))
        wp'.record cp'
      ∀ p : Option (NamedBlock V),
        M.proposal_with (M.gradeContract cp') .poolAndCarried S.E S.hc
          ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc (c - 1)))) pn'.st ⇢ p →
      ∃ P' : NamedBlock V, p = some P' ∧ P'.slot = (M.opening_slot S.hc (c - 1)) ∧
        ∀ cc : M.Cache,
          M.onPhaseTick S.E S.hc (M.toHealing (x[n][v].st).st.core)
            ((Restated.Vocabulary.Execution.Setup.a M S c)) (x[n][v].st).cache ⇢ cc →
        ∀ G : Block V,
          (M.gradeContract cc).stableRoot S.E S.hc
            (M.toHealing (M.ns_setClock S.E (x[n][v].st).st
              ((Restated.Vocabulary.Execution.Setup.a M S c))).core)
            ((M.round_of S.hc (M.ns_setClock S.E (x[n][v].st).st
              ((Restated.Vocabulary.Execution.Setup.a M S c))).core.s)) ⇢ some G →
          Block.Preceq P'.erase G := by
  intro R W wp' cp' hcp' pn' p hp
  have hN : (x[n + 1].time : Int) = (Restated.Vocabulary.Execution.Setup.a M S c) :=
    (Restated.tickStepAt_time facts x hn).1
  have hNE : (x[n + 1].time : Int) ≤ tAwakeEnd := by rw [hN]; exact hcE
  have hhor : (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c) ≤ R.horizon := by
    show (Restated.Vocabulary.Execution.Setup.a M S c) ≤ (x[n + 1].time : Int)
    exact le_of_eq hN.symm
  have hf : Restated.AdmissibleFieldsOn M (Setup.alwaysAwake S) R W (notHeldAt Sched) Finset.univ
      (tGAT + 1) :=
    Restated.admissibleFieldsOn_runAll_notHeld_upTo facts S Sched x v (n + 1)
      (hsync.monoU facts (le_of_eq hN)) hmono hawake hgst hcv hvalid hawm hthird hNE
  -- the proposal of round `c − 1`: every outcome is a named block of slot `o_{c − 1}`
  have hpmem : p ∈ Restated.Vocabulary.Statements.Instantiation.proposedBlockAt M
      (Setup.alwaysAwake S) R (M.opening_slot S.hc (c - 1)) :=
    ⟨pn', (p58% mkNode_mem_confirmationReadAt₅₈) hf.sorted hf.onePath _ _ cp' hcp',
      by rw [facts.nd.mkNode_cache]; exact hp⟩
  obtain ⟨P', rfl⟩ := Restated.Vocabulary.Proofs.HealingSurface.proposedBlockAt_isSome facts
    (Setup.alwaysAwake S) R (M.opening_slot S.hc (c - 1)) p hpmem
  have hslot : P'.slot = (M.opening_slot S.hc (c - 1)) :=
    Restated.Vocabulary.Proofs.HealingSurface.proposedBlockAt_slot facts (Setup.alwaysAwake S) R
      (M.opening_slot S.hc (c - 1)) _ hpmem rfl
  refine ⟨P', rfl, hslot, ?_⟩
  -- a proposal of round `c`, from one outcome of its proposer's read on `W`
  obtain ⟨cp, hcp⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc
    (W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc c)))
      (S.E.proposer (M.opening_slot S.hc c))).st.core.toHealing
    (M.proposal_time S.E (M.opening_slot S.hc c))
    (W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc c)))
      (S.E.proposer (M.opening_slot S.hc c))).cache
  obtain ⟨p0, hp0⟩ := facts.dt.proposal_with_nonempty (M.gradeContract cp) .poolAndCarried S.E S.hc
    ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc c)))
    (M.mkNode (M.ns_setClock S.E
      (W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc c)))
        (S.E.proposer (M.opening_slot S.hc c))).st
      (M.proposal_time S.E (M.opening_slot S.hc c)))
      (W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc c)))
        (S.E.proposer (M.opening_slot S.hc c))).record cp).st
  have hp0mem : p0 ∈ Restated.Vocabulary.Statements.Instantiation.proposedBlockAt M
      (Setup.alwaysAwake S) R (M.opening_slot S.hc c) :=
    ⟨_, (p58% mkNode_mem_confirmationReadAt₅₈) hf.sorted hf.onePath _ _ cp hcp,
      by rw [facts.nd.mkNode_cache]; exact hp0⟩
  obtain ⟨P, rfl⟩ := Restated.Vocabulary.Proofs.HealingSurface.proposedBlockAt_isSome facts
    (Setup.alwaysAwake S) R (M.opening_slot S.hc c) p0 hp0mem
  have hforms := Restated.namedGradeFormsAt_prevOpeningProposal_runAll_notHeld_upTo facts S Sched x
    v (n + 1) (hsync.monoU facts (le_of_eq hN)) hmono hawake hgst hcv hvalid hawm hthird hNE hcom
    hrec hc3 hhor hopening
    hopeningPrev cp hcp hp0 cp' hcp' hp
  obtain ⟨hpost, -, hloOpen, ht₀⟩ := Restated.roundAt_bounds_l71 facts S hgst
  have hm2 : fgSafetyProgressDeadline (Setup.alwaysAwake S) R
      (Restated.roundAt M S tGAT + S.hc.η_SG) gap (Setup.alwaysAwake S).extraRounds + 2 ≤ c := by
    rw [Restated.fgSafetyProgressDeadline_eq_deadlineRoundW facts]
    exact (Nat.le_succ _).trans hc3
  have hact := Restated.prevOpeningProposal_activeAtAction_afterDeadlineOn facts
    (Setup.alwaysAwake S) (notHeldAt Sched) Finset.univ hf
    (fun _ _ h => notHeldAt_anti hmono h) (fun _ => Finset.subset_univ _)
    (Restated.honestCommitteesOn_notHeld facts S Sched hcom)
    (Restated.belowOneThirdOn_runAll_notHeld facts S Sched x v (n + 1) hthird hNE)
    (Restated.multiProposerRecurrenceOn_runAll_notHeld facts S Sched x v (n + 1) hrec hNE)
    (Setup.timeoutDelayBound _) hpost hm2 hhor hopening cp hcp hp0
    (Restated.roundAt_lo_le_rGST_l71 facts S tGAT) hloOpen ht₀
    (fun k u hk _ j hj => Restated.awake_g2_action_runAllPath facts S Sched x v (n + 1) hmono hawake hNE
      k hk u j hj)
    (by rw [Restated.fgSafetyProgressDeadline_eq_deadlineRoundW facts]; exact hc3)
    hopeningPrev cp' hcp' hp
  have hvS : v ∈ notHeldAt Sched ((Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c)) :=
    mem_notHeldAt.2 hv
  have hvG0 : v ∈ notHeldAt Sched
      (M.domain (Setup.alwaysAwake S).E (Setup.alwaysAwake S).hc c .g0) :=
    notHeldAt_anti hmono (facts.gr.domain_le_a (Setup.alwaysAwake S) c .g0) hvS
  have hlo := Restated.lo_le_opening_afterDeadline_l85b facts (Setup.alwaysAwake S) hm2 hloOpen
  have hc0 : 0 < c := lt_of_lt_of_le (Nat.succ_pos _) hc3
  have hbefore : W (strictEventIndex R
      (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c)) v = x[n][v].st :=
    Restated.stateBeforeTime_runAll_tick facts S Sched x v hn (le_refl (n + 1)) v
  have hmemA := (p64b% mem_stateBeforeTime_along₆₄b) hf.sorted hf.onePath
    (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c)
  intro cc hcc G hG
  -- a node state of `v`'s round-`c` action read on `W` whose cache is `cc`
  obtain ⟨st', hst'⟩ := facts.dt.duties_update_confirmation_with_nonempty (M.gradeContract cc)
    S.E S.hc
    (M.ns_setClock S.E (x[n][v].st).st ((Restated.Vocabulary.Execution.Setup.a M S c)))
    (S.E.slotOf ((Restated.Vocabulary.Execution.Setup.a M S c)) - 1)
  obtain ⟨nu, hnu, hcache⟩ : ∃ nu : M.N,
      nu ∈ Restated.Vocabulary.Execution.NamedActionReads.actionReadFrom M (Setup.alwaysAwake S)
        (W (strictEventIndex R
          (Restated.Vocabulary.Execution.Setup.a M (Setup.alwaysAwake S) c)) v) c ∧
      nu.cache = cc := by
    refine ⟨M.mkNode st' (x[n][v].st).record cc, ?_, facts.nd.mkNode_cache _ _ _⟩
    rw [hbefore]
    exact ⟨cc, hcc, st', hst', rfl⟩
  have hactiveN : P'.erase ∈ Restated.Vocabulary.Internal.PhaseGrades.filteredTree M nu :=
    Restated.Vocabulary.Proofs.HealingSurface.activeAtAction_of_retainedAtRead facts
      (Setup.alwaysAwake S) _ hmemA (hact v hvS) nu hnu
  obtain ⟨Gr, hGr⟩ := facts.gr.read_nonempty (M.gradeContract nu.cache) S.E S.hc
    (M.toHealing nu.st.core) c
  have hq0 : Restated.Vocabulary.Internal.PhaseGrades.nodeQ2 M (Setup.alwaysAwake S) nu c ⇢ Gr.Q2 :=
    returns_map_intro_csr (fun g : Protocol.GradeRead V => g.Q2) _ Gr hGr
  obtain ⟨Q, hQ, hPQ⟩ := Restated.namedGradeFormsAt_preceq_actionQ2On facts (Setup.alwaysAwake S)
    (notHeldAt Sched) Finset.univ hf (fun _ _ h => notHeldAt_anti hmono h) hc0 hhor hforms
    hvG0 nu hnu hactiveN hlo Gr.Q2 hq0
  rw [hQ] at hq0
  have hroot := Restated.stableRoot_eq_actionQ2_runAll facts S Sched x v hn (le_refl (n + 1))
    nu hnu hq0 (some G) (by rw [hcache]; exact hG)
  rw [Option.some.inj hroot]
  exact hPQ

/-- Under the premises of `stableRoot_preceq_prevOpeningProposal_upTo`, if `k₀` is the tick step at
    the opening time of round `c − 1` and that round's opening slot is positive, then no stable root
    `G` that `v` can use at its tick at `S.a c` is an ancestor of, or equal to, a block of `v`'s
    tree after `k₀` steps. -/
theorem stableRoot_new_atStrongRound_upTo (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    {tGAT tAwakeEnd : Int} {gap : Nat} {c : Round}
    (hsync : Restated.SynchronyFromWakeBefore M S x
      ((Restated.Vocabulary.Execution.Setup.a M S c)))
    (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tAwakeEnd → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tAwakeEnd →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched))
    (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tAwakeEnd gap)
    (hc3 : Restated.deadlineRoundW M S tGAT gap + 3 ≤ c)
    (hopening : S.E.proposer ((M.opening_slot S.hc c)) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c))))
    (hopeningPrev : S.E.proposer ((M.opening_slot S.hc (c - 1))) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc (c - 1)))))
    {n : Nat} (hn : Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S c)))
    (hcE : (Restated.Vocabulary.Execution.Setup.a M S c) ≤ tAwakeEnd)
    {v : V} (hv : v ∉ Sched.adv ((Restated.Vocabulary.Execution.Setup.a M S c)))
    {k₀ : Nat} (hk₀ : Restated.tickStepAt M x k₀ (M.opening S.E S.hc (c - 1)))
    (hpos : 0 < (M.opening_slot S.hc (c - 1))) :
    ∀ cc : M.Cache,
      M.onPhaseTick S.E S.hc (M.toHealing (x[n][v].st).st.core)
        ((Restated.Vocabulary.Execution.Setup.a M S c)) (x[n][v].st).cache ⇢ cc →
    ∀ G : Block V,
      (M.gradeContract cc).stableRoot S.E S.hc
        (M.toHealing (M.ns_setClock S.E (x[n][v].st).st
          ((Restated.Vocabulary.Execution.Setup.a M S c))).core)
        ((M.round_of S.hc (M.ns_setClock S.E (x[n][v].st).st
          ((Restated.Vocabulary.Execution.Setup.a M S c))).core.s)) ⇢ some G →
      ∀ Y ∈ (x[k₀][v].st).st.core.T, ¬ Block.Preceq G Y := by
  intro cc hcc G hG Y hY hGY
  let R : Record.Run V :=
    { Restated.runAll M S Sched x v (n + 1) with honest := notHeldAt Sched (x[n + 1].time : Int) }
  let W := Restated.runAllPath M S Sched x v (n + 1)
  -- one proposal outcome of the proposer of `o_{c − 1}` on `W`
  obtain ⟨cp', hcp'⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc
    (W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc (c - 1))))
      (S.E.proposer (M.opening_slot S.hc (c - 1)))).st.core.toHealing
    (M.proposal_time S.E (M.opening_slot S.hc (c - 1)))
    (W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc (c - 1))))
      (S.E.proposer (M.opening_slot S.hc (c - 1)))).cache
  obtain ⟨p, hp⟩ := facts.dt.proposal_with_nonempty (M.gradeContract cp') .poolAndCarried S.E S.hc
    ((Setup.alwaysAwake S).node (S.E.proposer (M.opening_slot S.hc (c - 1))))
    (M.mkNode (M.ns_setClock S.E
      (W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc (c - 1))))
        (S.E.proposer (M.opening_slot S.hc (c - 1)))).st
      (M.proposal_time S.E (M.opening_slot S.hc (c - 1))))
      (W (strictEventIndex R (M.proposal_time S.E (M.opening_slot S.hc (c - 1))))
        (S.E.proposer (M.opening_slot S.hc (c - 1)))).record cp').st
  obtain ⟨P', -, hslot, hpre⟩ := Restated.stableRoot_preceq_prevOpeningProposal_upTo facts S Sched x
    hsync hmono hawake hgst hcv hvalid hawm hthird hcom hrec hc3 hopening hopeningPrev hn hcE hv
    cp' hcp' p hp
  have hPY : Block.Preceq P'.erase Y := preceq_trans_Preceq (hpre cc hcc G hG) hGY
  -- the step `k₀` is at or before `n`
  have hk₀n : k₀ + 1 ≤ n + 1 := by
    by_contra hcon
    have h1 := Restated.time_mono_int facts S Sched x (Nat.le_of_lt (Nat.lt_of_not_le hcon))
    rw [(Restated.tickStepAt_time facts x hn).1, (Restated.tickStepAt_time facts x hk₀).1] at h1
    exact absurd h1 (not_le.2 (Restated.opening_pred_lt_action facts S c))
  have hN : (x[n + 1].time : Int) = (Restated.Vocabulary.Execution.Setup.a M S c) :=
    (Restated.tickStepAt_time facts x hn).1
  have hNE : (x[n + 1].time : Int) ≤ tAwakeEnd := by rw [hN]; exact hcE
  have hf : Restated.AdmissibleFieldsOn M (Setup.alwaysAwake S) R W (notHeldAt Sched) Finset.univ
      (tGAT + 1) :=
    Restated.admissibleFieldsOn_runAll_notHeld_upTo facts S Sched x v (n + 1)
      (hsync.monoU facts (le_of_eq hN)) hmono hawake hgst hcv hvalid hawm hthird hNE
  have hbefore : W (strictEventIndex R (M.opening S.E S.hc (c - 1))) v = x[k₀][v].st :=
    Restated.stateBeforeTime_runAll_tick facts S Sched x v hk₀ hk₀n v
  have hYR : Y ∈ (W (strictEventIndex R (M.proposal_time S.E ((M.opening_slot S.hc (c - 1)))))
      v).st.core.T := by
    rw [← facts.gr.opening_eq_proposal_time, hbefore]
    exact hY
  have hlt := Restated.block_slot_lt_of_mem_before_proposalOn facts (Setup.alwaysAwake S)
    (notHeldAt Sched) Finset.univ hf hpos hYR
  have hle := Restated.preceq_slot_le_of_mem_storeBeforeTimeOn facts (Setup.alwaysAwake S)
    (notHeldAt Sched) Finset.univ hf Y hYR P'.erase hPY
  rw [NamedWire.erase_slot, hslot] at hle
  exact absurd hlt (not_lt.2 hle)

end

section
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Statements.Instantiation
open Framework.StsMultisetLog
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

end

end DecoupledConsensusModel.Sts.Restated
