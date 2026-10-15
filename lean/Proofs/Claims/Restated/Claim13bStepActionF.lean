import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bStepConeIter
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bStepAnchor
import Model.Conditions.Claim13bStepSG
import Model.Conditions.Sts_Interface
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring

/-!
# The finalized and fork-choice blocks of the action read

A round's action read keeps the reader's finalized block, and the fork-choice root of an honest
action read is an ancestor of the new anchor; stated over a model `M : Record.Model V`.
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

/-- Every store round `r₁`'s action can read from `before` has the finalized block of `before`'s
    store. -/
theorem actionHealingStore_F (facts : Record.Facts M) (S : Setup V) (before : M.N) (r₁ : Round) :
    ∀ hs ∈ Restated.actionHealingStore M S before r₁, hs.F = before.st.core.F := by
  intro hs hhs
  obtain ⟨c, hc, X, hX, st₀, hst₀, rfl⟩ := Restated.actionHealingStore_eq facts S before r₁ hs hhs
  obtain ⟨hF₀, hJ₀, hhj₀, hhm₀, hlc₀, hT₀, hs₀, hσ₀⟩ :=
    Restated.HS_fields_store_with_cache facts c hst₀
  simp only [hF₀, hJ₀, hhj₀, hhm₀, hlc₀, hT₀, hs₀, hσ₀] at *
  rw [Record.Model.HS.F, facts.hd.update_confirmation_with_toHealing_F _ _ _ _ _ X hX,
    facts.hd.setClock_toHealing_F]

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- If whatever a validator honest through its own read has finalized, at any step up to the
    successor of the tick step `n'` at `S.a (r + 1)`, is an ancestor of `A`, then for every
    validator `v` honest through `S.a (r + 1)`, the finalized block of every store round `(r + 1)`'s
    action can read from `v`'s node state at step `n'` is an ancestor of `A`. -/
theorem actionHealingStore_F_preceq_of_fin (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) {r : Round} {n' : Nat} {A : NamedBlock V}
    (hn' : Restated.tickStepAt M x n' ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))))
    (hfin : ∀ (v : V) (n₁ : Nat), n₁ ≤ n' + 1 → Restated.HonestThrough M Sched x n₁ v →
      Block.Preceq (x[n₁][v].st).st.core.F A.erase) :
    ∀ v ∈ honestThroughSet Sched ((Restated.Vocabulary.Execution.Setup.a M S (r + 1))),
      ∀ hs ∈ Restated.actionHealingStore M S (x[n'][v].st) (r + 1),
      Block.Preceq hs.F A.erase := by
  have htH : (x[n' + 1].time : Int) ≤ (Restated.Vocabulary.Execution.Setup.a M S (r + 1)) := le_of_eq (Restated.tickStepAt_time facts x hn').1
  intro v hv hs hhs
  have hvh : Restated.HonestThrough M Sched x n' v := fun t ht =>
    (mem_honestThroughSet.1 hv) t
      (le_trans ht (le_trans (Restated.time_mono_int facts S Sched x (Nat.le_succ n')) htH))
  rw [Restated.actionHealingStore_F facts S _ _ hs hhs]
  exact hfin v n' (Nat.le_succ n') hvh

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution

/-- For every choice `att` of attestations, if the round-`r` anchor `T` is an ancestor of the
    round-`(r + 1)` anchor read along `att`, then for every validator `v` honest through `tH'` and
    every store `hs` round `(r + 1)`'s action can read from `v`'s node state at step `n'`: if `hs`'s
    finalized block is an ancestor of the round-`(r + 1)` anchor and, when `hs`'s `h_max` is one
    more than its justified height, `hs`'s justified block is an ancestor of `T`, then the
    fork-choice root of `hs` is an ancestor of the round-`(r + 1)` anchor. -/
theorem fgRoot_preceq_at_reads_ofNewAnchorF (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    {tH' : Int} {r : Round} {n' : Nat} {att : V → NamedAttestation V} {T : NamedBlock V}
    (hold : Block.Preceq T.erase (Restated.newAnchor M S Sched x r n' att T).erase) :
    ∀ v ∈ honestThroughSet Sched tH',
      ∀ hs ∈ Restated.actionHealingStore M S (x[n'][v].st) (r + 1),
      Block.Preceq hs.F (Restated.newAnchor M S Sched x r n' att T).erase →
      (hs.h_max = hs.h_j + 1 → Block.Preceq hs.J T.erase) →
      Block.Preceq (M.get_fg_root hs.toFG)
        (Restated.newAnchor M S Sched x r n' att T).erase := by
  intro v hv hs hhs hF hJpre
  exact facts.fc.fgRoot_preceq_ofJustifiedBranch hF
    (fun hroot => preceq_trans_Preceq (hJpre hroot) hold)

end

end DecoupledConsensusModel.Sts.Restated
