import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bK_WindowProposalSent
import Proofs.Claims.Restated.ProcessedFlip
import Proofs.Claims.Restated.RunAll
import Proofs.Claims.Restated.Vocabulary_Protocol_ValidatorClient_BlockEmission
import Model.Conditions.Claim13bInvariant
import Model.Conditions.RunAll
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Conditions.Vocabulary_Internal_ModelVocabulary_Execution_NamedRun
import Model.Record.Wiring

/-!
# An awake proposer's block exists

An honest proposer awake at its proposal instant puts a block of its slot in the sent log there,
stated over a model `M : Record.Model V` and its facts `facts : Record.Facts M`. The proposer's wake
window starts at the member `M.proposal_wake_start`.
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

/-- If `v` reacts at the tick step `k` and `v`'s tick
    there has an outcome, then some outcome of that tick has every object of its list in the sent
    log after the step, signed by `v`. -/
private theorem sent_of_tick_outcome_ie (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    {k t : Nat} {v : V} (hl : x.lbl k = AtomicAction.tickAllAwake t)
    (haw : v ∈ Sched.awake (t : Int) \ Sched.adv (t : Int))
    (hne : ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched (t : Int) x[k] v) (t : Int) ⇢ out) :
    ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) v (Record.wakeStage M Sched (t : Int) x[k] v) (t : Int) ⇢ out ∧
      ∀ o ∈ out.2, (⟨v, o⟩ : SignedMsg V (NamedObject V)) ∈ x[k + 1].sent := by
  have hs : AtomicStep (Record.protocolOf M S) Sched (x.lbl k) x[k] x[k + 1] := x.step k
  rw [hl] at hs
  obtain ⟨-, w, tk, hwake, htick, hc⟩ := hs
  obtain ⟨out, hout, htkv⟩ := (priv% Proofs.Claims.Restated.RunAll
    DecoupledConsensusModel.Sts.Restated.tick_outcome_of_step) S Sched hwake htick haw hne
  refine ⟨out, hout, fun o ho => ?_⟩
  have hsent : x[k + 1].sent = x[k].sent
      + (Sched.awake (t : Int) \ Sched.adv (t : Int)).sum
          (fun q => ((w q).send + (tk q).send).map (SignedMsg.mk q)) := by
    rw [hc]; rfl
  rw [hsent]
  refine Multiset.mem_add.2 (Or.inr (Multiset.mem_sum.2 ⟨v, haw, ?_⟩))
  refine Multiset.mem_map.2 ⟨o, Multiset.mem_add.2 (Or.inr ?_), rfl⟩
  rw [htkv]
  exact Multiset.mem_coe.2 ho

/-- For a slot `s > 0` whose proposer is awake and not held at `s`'s proposal instant, if the
    proposer's tick there has an outcome (`hne`) and every outcome emits a block (`hprop`), then
    some step at that instant has in its sent log a block of slot `s` authored and signed by the
    proposer. -/
theorem proposalExists_of_awake (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (htd : Restated.TimeDiverges M x) {s : Slot} (hs : 0 < s)
    (hawake : S.E.proposer s ∈ Sched.awake (M.proposal_time S.E s))
    (hnotadv : S.E.proposer s ∉ Sched.adv (M.proposal_time S.E s))
    (hprop : ∀ (k : Nat),
      x.lbl k = AtomicAction.tickAllAwake (M.proposal_time S.E s).toNat →
      ∀ (out : M.N × List (NamedObject V)),
      M.tick (Setup.alwaysAwake S) (S.E.proposer s)
        (Record.wakeStage M Sched (M.proposal_time S.E s) x[k] (S.E.proposer s))
        (M.proposal_time S.E s) ⇢ out →
      ∃ B : NamedBlock V, NamedObject.block B ∈ out.2)
    (hne : ∀ k : Nat, x.lbl k = AtomicAction.tickAllAwake (M.proposal_time S.E s).toNat →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) (S.E.proposer s)
          (Record.wakeStage M Sched (M.proposal_time S.E s) x[k] (S.E.proposer s))
          (M.proposal_time S.E s) ⇢ out) :
    ∃ (i : Nat) (B : Block V), Restated.proposedBlockAtStep M S x i s B ∧
      (x[i].time : Int) = M.proposal_time S.E s := by
  obtain ⟨k, t', hl, ht'⟩ :=
    Restated.exists_tickStepAt facts x htd (facts.sch.proposal_time_pos_of_slot_pos S.E hs)
  have haw : S.E.proposer s ∈ Sched.awake (t' : Int) \ Sched.adv (t' : Int) := by
    rw [ht']; exact Finset.mem_sdiff.2 ⟨hawake, hnotadv⟩
  have hdvd : (t' : Int) % S.E.Δ = 0 := by
    rw [ht']; exact facts.sch.proposal_time_emod_delta_inclX S.E s
  have ht'n : (M.proposal_time S.E s).toNat = t' := by rw [← ht']; exact Int.toNat_natCast t'
  have hneK : ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) (S.E.proposer s)
        (Record.wakeStage M Sched (t' : Int) x[k] (S.E.proposer s)) (t' : Int) ⇢ out := by
    rw [ht']; exact hne k (by rw [ht'n]; exact hl)
  obtain ⟨out, hout, hall⟩ := sent_of_tick_outcome_ie facts S Sched x hl haw hneK
  obtain ⟨B', hB'⟩ := hprop k (by rw [ht'n]; exact hl) out (by rw [← ht']; exact hout)
  have hsent := hall _ hB'
  obtain ⟨W, hW, hemits⟩ := Restated.emits_runAll_of_tick facts S Sched x (S.E.proposer s) (n := k + 1)
    (Nat.lt_succ_self k) hl haw hout hB'
  have hshape := Restated.Vocabulary.Proofs.HealingSurface.emits_block_shape facts (Setup.alwaysAwake S) _
    W hW hemits
  have hslot : B'.slot = s := by
    have h1 : M.proposal_time S.E B'.slot = M.proposal_time S.E s := by
      rw [← ht']; exact hshape.2.1.symm
    have h2 := facts.sch.slotOf_proposal_time S.E B'.slot
    rw [h1, facts.sch.slotOf_proposal_time S.E s] at h2
    exact h2.symm
  have hauth : NamedObject.author (NamedObject.block B') = some (S.E.proposer s) :=
    Restated.author_of_emits facts (Setup.alwaysAwake S) _ W hW hemits
  refine ⟨k + 1, B'.erase, ⟨B', hsent, rfl, hslot, (author_block B').symm.trans hauth⟩, ?_⟩
  exact (Restated.tickStepAt_time facts x ⟨t', hl, ht'⟩).1

/-- On a valid execution whose clock diverges, for a slot `s > 0` whose proposer is not held up to
    `s`'s vote instant and is awake from `M.proposal_wake_start S s` to `s`'s proposal instant, some
    step at the proposal instant has in its sent log a block `B` of slot `s` authored and signed by
    the proposer, and every block of slot `s` the proposer sent by `s`'s vote instant is `B`. -/
theorem proposalExistsUnique_of_awake (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (htd : Restated.TimeDiverges M x) {s : Slot} (hs : 0 < s)
    (hhon : HonestThroughTime Sched (M.vote_time S.E s) (S.E.proposer s))
    (hawake : S.E.proposer s ∈ Sched.awakeThroughout (M.proposal_wake_start S s) (M.proposal_time S.E s)) :
    ∃ (i : Nat) (B : Block V), Restated.proposedBlockAtStep M S x i s B ∧
      (x[i].time : Int) = M.proposal_time S.E s ∧
      ∀ (j : Nat) (B' : Block V), (x[j].time : Int) ≤ M.vote_time S.E s →
        Restated.proposedBlockAtStep M S x j s B' → B' = B := by
  have hpv : M.proposal_time S.E s ≤ M.vote_time S.E s :=
    (facts.sch.proposal_time_lt_vote_time S.E s).le
  have haw : S.E.proposer s ∈ Sched.awake (M.proposal_time S.E s) :=
    mem_awake_of_awakeThroughout Sched hawake (facts.sch.proposal_wake_start_le_proposal_time S s) le_rfl
  obtain ⟨i, B, hB, hi⟩ :=
    Restated.proposalExists_of_awake facts S Sched x htd hs haw (hhon _ hpv)
      (fun k hk out hout => facts.ndRun.tick_emits_proposal_inclX S Sched x k hk
        (fun t' ht' => hhon t' (ht'.trans hpv)) hs hawake out (by
        have hlt := facts.sch.proposal_wake_start_lt_proposal_time S s
        have hprev : S.E.proposer s ∈ Sched.awake (M.proposal_time S.E s - 1) :=
          mem_awake_of_awakeThroughout Sched hawake (by omega) (by omega)
        have hne : S.E.proposer s ∉ (Sched.awake (M.proposal_time S.E s) \
            Sched.adv (M.proposal_time S.E s)) \ Sched.awake (M.proposal_time S.E s - 1) :=
          fun h => (Finset.mem_sdiff.1 h).2 hprev
        unfold Record.wakeStage at hout
        rw [if_neg hne] at hout
        exact hout))
      (fun k hk => by
        have hpos : (0 : Int) ≤ M.proposal_time S.E s :=
          (facts.sch.proposal_time_pos_of_slot_pos S.E hs).le
        have hc : ((M.proposal_time S.E s).toNat : Int) = M.proposal_time S.E s :=
          Int.toNat_of_nonneg hpos
        have h := facts.ndRun.tick_outcome_sts S Sched x hvalid.idealization.root_injective hvalid.honestRootsNew k _
          (S.E.proposer s) hk
          (by rw [hc]; exact Finset.mem_sdiff.2 ⟨haw, hhon _ hpv⟩)
          (by rw [hc]; exact fun t' ht' => hhon t' (ht'.trans hpv))
        rw [hc] at h
        exact h)
  refine ⟨i, B, hB, hi, ?_⟩
  intro j B' hj hB'
  exact Restated.proposedBlockAtStep_unique_g1 facts S Sched x hvalid.toUnforgeability
    (fun t' ht' => hhon t' (ht'.trans hj))
    (fun t' ht' => hhon t' (ht'.trans (hi ▸ hpv))) hB' hB

/-- On a valid execution whose clock diverges, for an instant `tE > 0` and a slot `s` proposed at or
    after `tE` whose proposer is not held up to `s`'s vote instant and is awake from
    `M.proposal_wake_start S s` to `s`'s proposal instant, some step at the proposal instant has in
    its sent log a block of slot `s` authored and signed by the proposer. -/
theorem confirmedIncludedExists_inclX (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hvalid : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (htd : Restated.TimeDiverges M x) {tE : Int} (htE : 0 < tE) (s : Slot)
    (hsE : tE ≤ M.proposal_time S.E s) :
    HonestThroughTime Sched (M.vote_time S.E s) (S.E.proposer s) →
    S.E.proposer s ∈ Sched.awakeThroughout (M.proposal_wake_start S s) (M.proposal_time S.E s) →
  ∃ (i : Nat) (B : Block V), Restated.proposedBlockAtStep M S x i s B ∧
      (x[i].time : Int) = M.proposal_time S.E s := by
  intro hhon hawake
  have hs : 0 < s := facts.sch.slot_pos_of_proposal_time_pos_inclX S.E (lt_of_lt_of_le htE hsE)
  obtain ⟨i, B, hB, hi, -⟩ :=
    Restated.proposalExistsUnique_of_awake facts S Sched x hvalid htd hs hhon hawake
  exact ⟨i, B, hB, hi⟩

end

end DecoupledConsensusModel.Sts.Restated
