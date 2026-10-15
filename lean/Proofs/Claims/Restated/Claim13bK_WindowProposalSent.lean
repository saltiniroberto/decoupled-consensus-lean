import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13b
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13beRoute3_44
import Proofs.Claims.Restated.Claim13beRoute3_45
import Proofs.Claims.Restated.Claim13beRoute3_50b
import Proofs.Claims.Restated.Claim13beRoute3_71
import Proofs.Claims.Restated.Claim13beRoute3_72
import Proofs.Claims.Restated.Claim13beRoute3_85c
import Proofs.Claims.Restated.Claim13beRoute3_85d
import Proofs.Claims.Restated.ProcessedFlip
import Proofs.Claims.Restated.RunAll
import Proofs.Claims.Restated.Vocabulary_Protocol_ForkChoice_Goldfish_GradeBootstrapCore
import Proofs.Claims.Restated.Vocabulary_Protocol_ValidatorClient_BlockEmission
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13beRoute3_44
import Model.Conditions.Claim13beRoute3_72
import Model.Conditions.RunAll
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Conditions.Vocabulary_Statements_Instantiation_Proposals
import Model.Record.Wiring

/-!
# A slot's honest proposer sends one block

Tick steps at one instant are one step, a proposed block comes from the proposer's own tick at the
proposal instant, and an honest proposer sends at most one block of its slot; stated over a model
`M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

/-- Names a private theorem of `Proofs.Claims.Restated.Claim13beRoute3_58`. -/
local macro "p58% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_58)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- Names a private theorem of `Proofs.Claims.Restated.Claim13beRoute3_71`. -/
local macro "p71% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beRoute3_71)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation

/-- If steps `k` and `k'` of the sts execution are both the tick at `t`, then `k = k'`. -/
theorem tickStepAt_unique_g1 (facts : Record.Facts M) {S : Setup V} {Sched : Schedule V}
    (x : AtomicExec (Record.protocolOf M S) Sched) {k k' : Nat} {t : Int}
    (h : Restated.tickStepAt M x k t) (h' : Restated.tickStepAt M x k' t) : k = k' := by
  obtain ⟨h1, h0⟩ := Restated.tickStepAt_time facts x h
  obtain ⟨h1', h0'⟩ := Restated.tickStepAt_time facts x h'
  rcases lt_trichotomy k k' with hlt | heq | hgt
  · exfalso
    have hle : (x[k + 1].time : Int) ≤ (x[k'].time : Int) := by
      exact_mod_cast Restated.time_mono facts S Sched x (Nat.succ_le_of_lt hlt)
    linarith
  · exact heq
  · exfalso
    have hle : (x[k' + 1].time : Int) ≤ (x[k].time : Int) := by
      exact_mod_cast Restated.time_mono facts S Sched x (Nat.succ_le_of_lt hgt)
    linarith

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation

/-- In an sts execution with unforgeable signatures, if `s`'s proposer is honest through the instant
    of `x[i]` and `proposedBlockAtStep S x i s B` holds, then some step `k < i` is the tick at `s`'s
    proposal instant, and some outcome of the proposer's tick there sends a named block of slot `s`
    whose erasure is `B`. -/
theorem signedProposal_tick_g1 (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hunf : Restated.Unforgeability M S x) {i : Nat} {s : Slot}
    {B : Block V}
    (hprop : HonestThroughTime Sched (x[i].time : Int) (S.E.proposer s))
    (hB : Restated.proposedBlockAtStep M S x i s B) :
    ∃ k < i, ∃ B' : NamedBlock V, B'.erase = B ∧ B'.slot = s ∧
      Restated.tickStepAt M x k (M.proposal_time S.E s) ∧
      ∃ t : Nat, x.lbl k = AtomicAction.tickAllAwake t ∧
        (t : Int) = M.proposal_time S.E s ∧
        ∃ out : M.N × List (NamedObject V),
          M.tick (Setup.alwaysAwake S) (S.E.proposer s)
            (Record.wakeStage M Sched (t : Int) x[k] (S.E.proposer s)) (t : Int) ⇢ out ∧
          NamedObject.block B' ∈ out.2 := by
  obtain ⟨B', hmem, hBe, hBslot, hauth⟩ := hB
  have hauthor : NamedObject.author (NamedObject.block B') = some (S.E.proposer s) :=
    (author_block B').trans hauth
  obtain ⟨k, hki, t, hl, haw, out, hout, hemit⟩ :=
    Restated.tick_of_honest_signed_upTo facts S Sched x (S.E.proposer s) (.block B') (x[i].time : Int) hprop
      hunf hauthor i le_rfl hmem
  obtain ⟨W, hW, hemi⟩ :=
    Restated.emits_runAll_of_tick facts S Sched x (S.E.proposer s) hki hl haw hout hemit
  have ht : (t : Int) = M.proposal_time S.E s := by
    have h := (Restated.Vocabulary.Proofs.HealingSurface.emits_block_shape facts (Setup.alwaysAwake S) _
      W hW hemi).2.1
    rw [hBslot] at h
    exact h
  exact ⟨k, hki, B', hBe, hBslot, ⟨t, hl, ht⟩, t, hl, ht, out, hout, hemit⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation

/-- In an sts execution with unforgeable signatures, if `s`'s proposer is honest through the
    instants of `x[i]` and of `x[j]`, and `proposedBlockAtStep S x i s B` and
    `proposedBlockAtStep S x j s B'` hold, then `B = B'`. -/
theorem proposedBlockAtStep_unique_g1 (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hunf : Restated.Unforgeability M S x) {i j : Nat} {s : Slot}
    {B B' : Block V}
    (hi : HonestThroughTime Sched (x[i].time : Int) (S.E.proposer s))
    (hj : HonestThroughTime Sched (x[j].time : Int) (S.E.proposer s))
    (hB : Restated.proposedBlockAtStep M S x i s B) (hB' : Restated.proposedBlockAtStep M S x j s B') :
    B = B' := by
  obtain ⟨k, -, P, hPe, -, hk, t, hl, -, out, hout, hmem⟩ :=
    Restated.signedProposal_tick_g1 facts S Sched x hunf hi hB
  obtain ⟨k', -, P', hPe', -, hk', t', hl', -, out', hout', hmem'⟩ :=
    Restated.signedProposal_tick_g1 facts S Sched x hunf hj hB'
  have hkk : k = k' := Restated.tickStepAt_unique_g1 facts x hk hk'
  subst hkk
  have htt : t = t' := by
    rw [hl] at hl'
    exact AtomicAction.tickAllAwake.inj hl'
  subst htt
  have _hr_s1 := Record.reachedNode_wakeStage facts S Sched x (k) (S.E.proposer s) (↑t)
  have _hv_s2 := Record.runs_as_wakeStage facts S Sched x (k) (S.E.proposer s) (↑t)
  have h1 := (Restated.Vocabulary.Proofs.HealingSurface.block_mem_on_tick_emit facts (Setup.alwaysAwake S)
    (S.E.proposer s) _ (t : Int) out hout hmem).2
  have _hr_s3 := Record.reachedNode_wakeStage facts S Sched x (k) (S.E.proposer s) (↑t)
  have _hv_s4 := Record.runs_as_wakeStage facts S Sched x (k) (S.E.proposer s) (↑t)
  have h2 := (Restated.Vocabulary.Proofs.HealingSurface.block_mem_on_tick_emit facts (Setup.alwaysAwake S)
    (S.E.proposer s) _ (t : Int) out' hout' hmem').2
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty (Setup.alwaysAwake S).E (Setup.alwaysAwake S).hc
    (Record.wakeStage M Sched (t : Int) x[k] (S.E.proposer s)).st.core.toHealing (t : Int)
    (Record.wakeStage M Sched (t : Int) x[k] (S.E.proposer s)).cache
  have hbm := facts.nd.block_mem_on_tick_emit (Setup.alwaysAwake S) (S.E.proposer s) _ (t : Int) out hout hmem
  obtain ⟨D, hD⟩ := facts.dt.propose_block_with_nonempty (Setup.alwaysAwake S) (S.E.proposer s) _ (t : Int)
    out hout hbm.1.1 hbm.1.2.1 hbm.1.2.2
    (facts.nd.block_mem_on_tick_emit_awake (Setup.alwaysAwake S) (S.E.proposer s) _ (t : Int) out hout hmem) c hc
  have hPP : P = P' := Option.some_inj.mp ((h1 c hc D hD).symm.trans (h2 c hc D hD))
  rw [← hPe, ← hPe', hPP]

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation

/-- If `AdmissibleFieldsOn` holds along the path the execution follows for a family `Hs` that
    shrinks as time grows, `0 < s`, `s`'s proposer is in `Hs` at `s`'s confirmation instant and
    passes the grade-1 awake test of `s`'s round at its proposal tick, and `s`'s proposal instant is
    in `[lo, x[n].time]`, then every proposal `P` of that proposer's read on that path is of slot
    `s`, and some step `k < n` is the tick at `s`'s proposal instant with
    `proposedBlockAtStep S x (k + 1) s P.erase`. -/
theorem proposedBlockAtStep_of_proposedBlockAtOn_g1 (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v₀ : V)
    {n : Nat} {s : Slot} {P : NamedBlock V}
    {Hs : Int → Finset V} {Xb : Finset V} {lo : Int}
    (hf : Restated.AdmissibleFieldsOn M (Setup.alwaysAwake S)
      ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } : Record.Run V)
      (Restated.runAllPath M S Sched x v₀ n) Hs Xb lo)
    (hHs : ∀ t t' : Int, t ≤ t' → Hs t' ⊆ Hs t)
    (hs : 0 < s) (hprop : S.E.proposer s ∈ Hs (M.confirmation_time S.E s))
    (hhor : M.proposal_time S.E s ≤ (x[n].time : Int))
    (hlo : lo ≤ M.proposal_time S.E s)
    (hnr : ∀ (k τ : Nat) (u : V), x.lbl k = AtomicAction.tickAllAwake τ →
      (τ : Int) % S.E.Δ = 0 → u ∈ Sched.awake (τ : Int) \ Sched.adv (τ : Int) →
      (∀ t' ≤ (τ : Int), u ∉ Sched.adv t') →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) u (Record.wakeStage M Sched (τ : Int) x[k] u) (τ : Int) ⇢ out)
    (hrun : ∀ j : Nat,
      ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } :
          Record.Run V).events[j]? =
        some (Record.Event.tick (S.E.proposer s) (M.proposal_time S.E s)) →
      M.awake_for_grade1 (Setup.alwaysAwake S) (S.E.proposer s)
        (Restated.runAllPath M S Sched x v₀ n j (S.E.proposer s)) (M.round_of S.hc s)) :
    let R : Record.Run V :=
      { Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) }
    let W := Restated.runAllPath M S Sched x v₀ n
    let wp := W (Restated.strictEventIndex R (M.proposal_time S.E s))
      (S.E.proposer s)
    ∀ cp : M.Cache,
      M.onPhaseTick S.E S.hc wp.st.core.toHealing
        (M.proposal_time S.E s) wp.cache ⇢ cp →
      let pn := M.mkNode (M.ns_setClock S.E wp.st (M.proposal_time S.E s))
        wp.record cp
      M.proposal_with (M.gradeContract cp) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer s)) pn.st ⇢ some P →
    P.slot = s ∧ ∃ k : Nat, k < n ∧ Restated.tickStepAt M x k (M.proposal_time S.E s) ∧
      Restated.proposedBlockAtStep M S x (k + 1) s P.erase := by
  intro R W wp cp hcp pn hP
  have hPclock : M.proposal_with (M.gradeContract cp)
      Protocol.ProposalRowSource.poolAndCarried S.E S.hc
      ((Setup.alwaysAwake S).node (S.E.proposer s))
      (M.ns_setClock S.E wp.st (M.proposal_time S.E s)) ⇢ some P := by
    have h := hP
    rw [show pn.st = M.store_with_cache (M.ns_setClock S.E wp.st (M.proposal_time S.E s)) _ from
      facts.nd.mkNode_st _ _ _, facts.dt.proposal_with_store_with_cache] at h
    exact h
  obtain ⟨hslot, hemit⟩ := Restated.proposalTickOn facts (Setup.alwaysAwake S) Hs Xb hf hHs s hs
    hprop hhor hlo (fun j hj => hf.tick_outcome j _ _ hj) hrun cp hcp hPclock
  obtain ⟨k, hk, hktick, hsent⟩ := Restated.mem_sent_of_emits_runAll facts S Sched x v₀ hemit
  have hauth : NamedObject.author (NamedObject.block P) = some (S.E.proposer s) :=
    Restated.author_of_emits facts (Setup.alwaysAwake S) _ W hf.onePath hemit
  exact ⟨hslot, k, hk, hktick, P, hsent, rfl, hslot, (author_block P).symm.trans hauth⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation

/-- Under synchrony from wake, monotone corruption, every validator not held by the adversary awake
    from `tGAT` to `tL`, `t_GST ≤ tGAT`, the common view at `tGAT`, a valid execution,
    `AwakeAtMultiples` and the adversary under a third of the weight up to `tL`: for a step `n` with
    `x[n].time ≤ tL` and a slot `s > 0` whose proposal instant is in `[tGAT + 1, x[n].time]`, whose
    proposer is not held at `s`'s confirmation instant and passes the grade-1 awake test of `s`'s
    round at its proposal tick, every proposal `P` of that proposer's read on the path the execution
    follows is of slot `s`, is sent as `proposedBlockAtStep S x k s P.erase` at a step `k` whose
    instant is `s`'s proposal instant, and every block `B` with `proposedBlockAtStep S x i s B` at a
    step `i` whose instant is at or before `s`'s confirmation instant is `P.erase`. -/
theorem windowProposalSent_g1 (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v₀ : V) (n : Nat)
    {tGAT tL : Int}
    (hsync : Restated.SynchronyFromWake M S x) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tL → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tL →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hn : (x[n].time : Int) ≤ tL)
    {s : Slot} {P : NamedBlock V} (hs : 0 < s)
    (hlo : tGAT + 1 ≤ M.proposal_time S.E s)
    (hhor : M.proposal_time S.E s ≤ (x[n].time : Int))
    (hprop : S.E.proposer s ∈ notHeldAt Sched (M.confirmation_time S.E s))
    (hrun : ∀ j : Nat,
      ({ Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) } :
          Record.Run V).events[j]? =
        some (Record.Event.tick (S.E.proposer s) (M.proposal_time S.E s)) →
      M.awake_for_grade1 (Setup.alwaysAwake S) (S.E.proposer s)
        (Restated.runAllPath M S Sched x v₀ n j (S.E.proposer s)) (M.round_of S.hc s)) :
    let R : Record.Run V :=
      { Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) }
    let W := Restated.runAllPath M S Sched x v₀ n
    let wp := W (Restated.strictEventIndex R (M.proposal_time S.E s))
      (S.E.proposer s)
    ∀ cp : M.Cache,
      M.onPhaseTick S.E S.hc wp.st.core.toHealing
        (M.proposal_time S.E s) wp.cache ⇢ cp →
      let pn := M.mkNode (M.ns_setClock S.E wp.st (M.proposal_time S.E s))
        wp.record cp
      M.proposal_with (M.gradeContract cp) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer s)) pn.st ⇢ some P →
    P.slot = s ∧
      (∃ k : Nat, (x[k].time : Int) = M.proposal_time S.E s ∧
        Restated.proposedBlockAtStep M S x k s P.erase) ∧
      ∀ (i : Nat) (B : Block V),
        (x[i].time : Int) ≤ M.confirmation_time S.E s →
        Restated.proposedBlockAtStep M S x i s B → B = P.erase := by
  intro R W wp cp hcp pn hP
  have hf := Restated.admissibleFieldsOn_runAll_notHeld facts S Sched x v₀ n hsync hmono hawake hgst hcv hvalid
    hawm hthird hn
  have hHs : ∀ t t' : Int, t ≤ t' → notHeldAt Sched t' ⊆ notHeldAt Sched t :=
    fun _ _ h => notHeldAt_anti hmono h
  obtain ⟨hslot, k, -, hktick, hsent⟩ :=
    Restated.proposedBlockAtStep_of_proposedBlockAtOn_g1 facts S Sched x v₀ hf hHs hs hprop hhor hlo
      (fun k τ u hl _ => facts.ndRun.tick_outcome_sts S Sched x hvalid.idealization.root_injective hvalid.honestRootsNew k τ u hl) hrun cp hcp hP
  have hk1 : (x[k + 1].time : Int) = M.proposal_time S.E s := (Restated.tickStepAt_time facts x hktick).1
  have hhon : HonestThroughTime Sched (M.confirmation_time S.E s) (S.E.proposer s) :=
    fun t' ht' hadv => (mem_notHeldAt.mp hprop) (hmono _ _ ht' hadv)
  have hunf : Restated.Unforgeability M S x := hvalid.toUnforgeability
  refine ⟨hslot, ⟨k + 1, hk1, hsent⟩, ?_⟩
  intro i B hi hB
  refine Restated.proposedBlockAtStep_unique_g1 facts S Sched x hunf
    (fun t' ht' => hhon t' (ht'.trans hi))
    (fun t' ht' => hhon t' (ht'.trans (by
      rw [hk1]; exact facts.sch.proposal_time_le_confirmation_time S.E s)))
    hB hsent

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation

/-- For a slot `s` at or after the opening slot of round `deadlineRoundW M S tGAT gap + 1`, `0 < s`
    and `tGAT + 1 ≤ proposal_time S.E s`. -/
theorem windowSlot_bounds_g1 (facts : Record.Facts M) (S : Setup V) (tGAT : Int) (gap : Nat) {s : Slot}
    (hs : (M.opening_slot S.hc (Restated.deadlineRoundW M S tGAT gap + 1)) ≤ s) :
    0 < s ∧ tGAT + 1 ≤ M.proposal_time S.E s := by
  set d := Restated.deadlineRoundW M S tGAT gap with hd
  refine ⟨lt_of_lt_of_le (facts.gr.opening_slot_pos S (Nat.succ_pos d)) hs, ?_⟩
  have h1 : tGAT + 1 ≤ (Restated.Vocabulary.Execution.Setup.a M S d) :=
    (Restated.roundAt_lo_le_rGST_l71 facts S tGAT).trans
      ((Restated.Vocabulary.Proofs.HealingSurface.action_strictMono facts S).monotone (Restated.rGST_le_deadlineRoundW_l85c facts S tGAT gap))
  have h2 : (Restated.Vocabulary.Execution.Setup.a M S d) < M.proposal_time S.E ((M.opening_slot S.hc (d + 1))) := by
    rw [Restated.action_eq_l85d facts S, Restated.proposal_time_opening_eq_l85d facts S]
    have hR : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast S.hc.R_ge_three
    have hΔ : 0 < S.E.Δ := S.E.Δ_pos
    push_cast
    nlinarith
  exact h1.trans (h2.le.trans (facts.sch.proposal_time_mono S.E hs))

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation

/-- Under the premises of `windowProposalSent_g1`, for a step `n` with `x[n].time ≤ tL` and a slot
    `s` at or after the opening slot of round `deadlineRoundW M S tGAT gap + 1`, whose proposal
    instant is at or before `x[n].time` and whose proposer is not held at `s`'s confirmation
    instant: every outcome of the proposal of that proposer's read on the path the execution follows
    is `some P` for a named block `P` of slot `s` with `proposedBlockAtStep S x k s P.erase` at a
    step `k` whose instant is `s`'s proposal instant, and every block `B` with
    `proposedBlockAtStep S x i s B` at a step `i` whose instant is at or before `s`'s confirmation
    instant is `P.erase`. -/
theorem windowSlotProposalSent_g1 (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v₀ : V) (n : Nat)
    {tGAT tL : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWake M S x) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tL → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tL →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hn : (x[n].time : Int) ≤ tL)
    {s : Slot} (hs : (M.opening_slot S.hc (Restated.deadlineRoundW M S tGAT gap + 1)) ≤ s)
    (hhor : M.proposal_time S.E s ≤ (x[n].time : Int))
    (hprop : S.E.proposer s ∈ notHeldAt Sched (M.confirmation_time S.E s)) :
    let R : Record.Run V :=
      { Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) }
    let W := Restated.runAllPath M S Sched x v₀ n
    let wp := W (Restated.strictEventIndex R (M.proposal_time S.E s))
      (S.E.proposer s)
    ∀ cp : M.Cache,
      M.onPhaseTick S.E S.hc wp.st.core.toHealing
        (M.proposal_time S.E s) wp.cache ⇢ cp →
      let pn := M.mkNode (M.ns_setClock S.E wp.st (M.proposal_time S.E s))
        wp.record cp
      ∀ o : Option (NamedBlock V),
      M.proposal_with (M.gradeContract cp) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer s)) pn.st ⇢ o →
    ∃ P : NamedBlock V, o = some P ∧
      P.slot = s ∧
      (∃ k : Nat, (x[k].time : Int) = M.proposal_time S.E s ∧
        Restated.proposedBlockAtStep M S x k s P.erase) ∧
      ∀ (i : Nat) (B : Block V),
        (x[i].time : Int) ≤ M.confirmation_time S.E s →
        Restated.proposedBlockAtStep M S x i s B → B = P.erase := by
  intro R W wp cp hcp pn o ho
  obtain ⟨hspos, hlo⟩ := Restated.windowSlot_bounds_g1 facts S tGAT gap hs
  have hf := Restated.admissibleFieldsOn_runAll_notHeld facts S Sched x v₀ n hsync hmono hawake hgst hcv hvalid
    hawm hthird hn
  have hHs : ∀ t t' : Int, t ≤ t' → notHeldAt Sched t' ⊆ notHeldAt Sched t :=
    fun _ _ h => notHeldAt_anti hmono h
  have hoclock : M.proposal_with (M.gradeContract cp)
      Protocol.ProposalRowSource.poolAndCarried S.E S.hc
      ((Setup.alwaysAwake S).node (S.E.proposer s))
      (M.ns_setClock S.E wp.st (M.proposal_time S.E s)) ⇢ o := by
    have h := ho
    rw [show pn.st = M.store_with_cache (M.ns_setClock S.E wp.st (M.proposal_time S.E s)) _ from
      facts.nd.mkNode_st _ _ _, facts.dt.proposal_with_store_with_cache] at h
    exact h
  -- the proposer passes the grade-1 awake test at its proposal tick
  have hround : Restated.deadlineRoundW M S tGAT gap + 1 ≤ M.round_of S.hc s := by
    have h := facts.gr.round_of_mono S.hc hs
    rwa [facts.gr.round_of_opening_slot_eq S.hc] at h
  have hwin : tGAT + 1 ≤ M.early S.E S.hc (M.round_of S.hc s) .g1 - S.E.Δ := by
    have h0 := Restated.lo_le_early_g2_sub_delta_of_action_lt facts S
      (Restated.roundAt_lo_le_rGST_l71 facts S tGAT)
      (lt_of_le_of_lt (Restated.rGST_le_deadlineRoundW_l85c facts S tGAT gap)
        (Nat.lt_of_succ_le hround))
    have h1 := facts.gr.early_g2_add_delta_le_early_g1 S (M.round_of S.hc s)
    have hΔ := S.E.Δ_pos
    linarith
  have hrun : ∀ j : Nat, R.events[j]? =
        some (Record.Event.tick (S.E.proposer s) (M.proposal_time S.E s)) →
      M.awake_for_grade1 (Setup.alwaysAwake S) (S.E.proposer s) (W j (S.E.proposer s))
        (M.round_of S.hc s) :=
    fun j hj => hf.awake_g1 _ _ j _ (Or.inl rfl) hj
      (hHs _ _ (facts.sch.proposal_time_le_confirmation_time S.E _) hprop) hwin
  obtain ⟨P, hoP, -, -⟩ := Restated.proposedBlockAt_emits_of_honestOn facts (Setup.alwaysAwake S)
    (notHeldAt Sched) Finset.univ hf hHs s hspos hprop hhor hlo (fun j hj => hf.tick_outcome j _ _ hj)
    hrun cp hcp o hoclock
  subst hoP
  exact ⟨P, rfl, Restated.windowProposalSent_g1 facts S Sched x v₀ n hsync hmono hawake hgst hcv hvalid
    hawm hthird hn hspos hlo hhor hprop hrun cp hcp ho⟩

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation

/-- `windowSlotProposalSent_g1` at the slot `o_c + k` of a round `c` with
    `deadlineRoundW M S tGAT gap + 1 ≤ c`: every outcome of that slot's proposal on the path the
    execution follows is `some P` for a named block `P` of that slot, sent at the slot's proposal
    instant, and every block of `proposedBlockAtStep` for that slot at a step whose instant is at or
    before the slot's confirmation instant is `P.erase`. -/
theorem windowOpeningProposalSent_g1 (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (v₀ : V) (n : Nat)
    {tGAT tL : Int} {gap : Nat}
    (hsync : Restated.SynchronyFromWake M S x) (hmono : Sched.MonotoneCorruption)
    (hawake : ∀ t : Int, tGAT ≤ t → t ≤ tL → ∀ v : V, v ∉ Sched.adv t →
      v ∈ Sched.awake t)
    (hgst : S.E.t_GST ≤ tGAT) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (hawm : AwakeAtMultiples S Sched)
    (hthird : ∀ t : Int, t ≤ tL →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight)
    (hn : (x[n].time : Int) ≤ tL)
    {c : Round} (hc : Restated.deadlineRoundW M S tGAT gap + 1 ≤ c) (k : Nat)
    (hhor : M.proposal_time S.E ((M.opening_slot S.hc c) + k) ≤ (x[n].time : Int))
    (hprop : S.E.proposer ((M.opening_slot S.hc c) + k) ∈
      notHeldAt Sched (M.confirmation_time S.E ((M.opening_slot S.hc c) + k))) :
    let R : Record.Run V :=
      { Restated.runAll M S Sched x v₀ n with honest := notHeldAt Sched (x[n].time : Int) }
    let W := Restated.runAllPath M S Sched x v₀ n
    let wp := W (Restated.strictEventIndex R (M.proposal_time S.E ((M.opening_slot S.hc c) + k)))
      (S.E.proposer ((M.opening_slot S.hc c) + k))
    ∀ cp : M.Cache,
      M.onPhaseTick S.E S.hc wp.st.core.toHealing
        (M.proposal_time S.E ((M.opening_slot S.hc c) + k)) wp.cache ⇢ cp →
      let pn := M.mkNode (M.ns_setClock S.E wp.st (M.proposal_time S.E ((M.opening_slot S.hc c) + k)))
        wp.record cp
      ∀ o : Option (NamedBlock V),
      M.proposal_with (M.gradeContract cp) .poolAndCarried S.E S.hc
        ((Setup.alwaysAwake S).node (S.E.proposer ((M.opening_slot S.hc c) + k))) pn.st ⇢ o →
    ∃ P : NamedBlock V, o = some P ∧
      P.slot = (M.opening_slot S.hc c) + k ∧
      (∃ j : Nat, (x[j].time : Int) = M.proposal_time S.E ((M.opening_slot S.hc c) + k) ∧
        Restated.proposedBlockAtStep M S x j ((M.opening_slot S.hc c) + k) P.erase) ∧
      ∀ (i : Nat) (B : Block V),
        (x[i].time : Int) ≤ M.confirmation_time S.E ((M.opening_slot S.hc c) + k) →
        Restated.proposedBlockAtStep M S x i ((M.opening_slot S.hc c) + k) B → B = P.erase :=
  Restated.windowSlotProposalSent_g1 facts S Sched x v₀ n hsync hmono hawake hgst hcv hvalid hawm hthird hn
    ((facts.gr.opening_slot_mono S hc).trans (Nat.le_add_right _ _)) hhor hprop

end

end DecoupledConsensusModel.Sts.Restated
