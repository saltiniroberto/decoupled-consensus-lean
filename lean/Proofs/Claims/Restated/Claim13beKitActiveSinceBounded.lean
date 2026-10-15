import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bInvariant
import Proofs.Claims.Restated.Claim13bKit
import Proofs.Claims.Restated.Claim13bW_Schedule
import Proofs.Claims.Restated.Claim13beKitActiveSince
import Model.Conditions.Claim13bInvariantActiveSince
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring

/-!
# Safety up to a time `tHi`, from a step that is taken only up to `tHi`

The twins of `afterPhaseInvariantOverActiveSetsSince_of_stepFrom` and
`claim13be_conclusion_of_base_and_stepFrom_overActiveSetsSince`
(`lean/Proofs/Claims/Restated/Claim13beKitActiveSince.lean`) for a step from round `r` to round
`r + 1` that is assumed only when round `r + 1`'s action instant is at most `tHi`. The switch round
stays the one of the phase end `tE`; `tHi` is a second time, the last one the step may reach. The
invariant then reaches every round from the switch round on whose action instant is at most `tHi`,
and the conclusion holds for two reads at steps `i` and `j` with
`max (x[i].time) (x[j].time) + period ≤ tHi`: the least round whose action instant is after both
reads has its action instant at most one period after the later read.
Stated over a model `M : Record.Model V`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

local macro "pKAS% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13beKitActiveSince)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))

section
set_option autoImplicit false
open DecoupledConsensusModel.Execution
open Framework.StsMultisetLog
open DecoupledConsensusModel.Statements.Instantiation

/-- If `AfterPhaseInvariantOverActiveSetsSince` holds at the switch round `rW` with step `n₀`,
    switch step `n₀` and anchor `T₀`, and the invariant carries from every round `r` at or after
    `rW` whose anchor is `T₀` or a descendant of it to round `r + 1` whenever round `r + 1`'s
    action instant is at most `tHi`, then for every `k` such that round `rW + k`'s action instant is
    at most `tHi` the invariant holds at round `rW + k`, with switch step `n₀` and an anchor that is
    `T₀` or a descendant of `T₀`. -/
theorem afterPhaseInvariantOverActiveSetsSince_of_stepFrom_bounded (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE tHi : Int)
    {n₀ : Nat} {T₀ : NamedBlock V}
    (hbase : Restated.AfterPhaseInvariantOverActiveSetsSince M S Sched x (Restated.switchRound M S tE) n₀ n₀ T₀)
    (hstep : ∀ (r : Round) (n : Nat) (T : NamedBlock V), Restated.switchRound M S tE ≤ r →
      Restated.Vocabulary.Execution.Setup.a M S (r + 1) ≤ tHi →
      Block.Preceq T₀.erase T.erase →
      Restated.AfterPhaseInvariantOverActiveSetsSince M S Sched x r n n₀ T →
      ∃ (n' : Nat) (T' : NamedBlock V),
        Restated.AfterPhaseInvariantOverActiveSetsSince M S Sched x (r + 1) n' n₀ T' ∧
          Block.Preceq T.erase T'.erase) :
    ∀ k : Nat, Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE + k) ≤ tHi →
      ∃ (n : Nat) (T : NamedBlock V),
        Restated.AfterPhaseInvariantOverActiveSetsSince M S Sched x (Restated.switchRound M S tE + k) n n₀ T ∧
          Block.Preceq T₀.erase T.erase := by
  intro k
  induction k with
  | zero => intro _; exact ⟨n₀, T₀, hbase, preceq_eq_true_iff_Preceq.mp (Block.preceq_self _)⟩
  | succ k ih =>
    intro hk
    obtain ⟨n, T, hinv, hT⟩ := ih (le_trans (Restated.action_mono facts S (Nat.le_succ _)) hk)
    obtain ⟨n', T', hinv2, hTT'⟩ :=
      hstep (Restated.switchRound M S tE + k) n T (Nat.le_add_right _ _) hk hT hinv
    exact ⟨n', T', hinv2, preceq_trans_Preceq hT hTT'⟩

/-- If `AfterPhaseInvariantOverActiveSetsSince` holds at the switch round `rW` with step `n₀`,
    switch step `n₀` and anchor `T₀`, and the invariant carries from every round `r` at or after
    `rW` whose anchor is `T₀` or a descendant of it to round `r + 1` whenever round `r + 1`'s
    action instant is at most `tHi`, then any two blocks finalized in the stores of two validators
    honest through their own reads at steps `i` and `j` are compatible, provided the later of the
    two reads is at least one period before `tHi`. -/
theorem claim13be_conclusion_of_base_and_stepFrom_bounded (facts : Record.Facts M) (S : Setup V)
    (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE tHi : Int)
    (n₀ : Nat) (T₀ : NamedBlock V)
    (hbase : Restated.AfterPhaseInvariantOverActiveSetsSince M S Sched x (Restated.switchRound M S tE) n₀ n₀ T₀)
    (hstep : ∀ (r : Round) (n : Nat) (T : NamedBlock V), Restated.switchRound M S tE ≤ r →
      Restated.Vocabulary.Execution.Setup.a M S (r + 1) ≤ tHi →
      Block.Preceq T₀.erase T.erase →
      Restated.AfterPhaseInvariantOverActiveSetsSince M S Sched x r n n₀ T →
      ∃ (n' : Nat) (T' : NamedBlock V),
        Restated.AfterPhaseInvariantOverActiveSetsSince M S Sched x (r + 1) n' n₀ T' ∧
          Block.Preceq T.erase T'.erase) :
    ∀ (v₁ v₂ : V) (i j : Nat),
      Restated.HonestThrough M Sched x i v₁ → Restated.HonestThrough M Sched x j v₂ →
      max (x[i].time : Int) (x[j].time : Int) + (Restated.constants M S).period ≤ tHi →
      Block.Compatible (x[i][v₁].st).st.core.F (x[j][v₂].st).st.core.F := by
  classical
  intro v₁ v₂ i j hhon₁ hhon₂ hread
  -- the least round from the switch round on whose action instant is past both reads
  have hex : ∃ k : Nat, max (x[i].time : Int) (x[j].time : Int)
      < Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE + k) :=
    (pKAS% exists_action_gt_kas) facts S (Restated.switchRound M S tE) (max (x[i].time : Int) (x[j].time : Int))
  have hk := Nat.find_spec hex
  -- the invariant at that round: the base, or the bounded chain, whose last round's action instant
  -- is at most one period after the later read
  have hinvk : ∃ (n : Nat) (T : NamedBlock V),
      Restated.AfterPhaseInvariantOverActiveSetsSince M S Sched x
        (Restated.switchRound M S tE + Nat.find hex) n n₀ T := by
    rcases hfind : Nat.find hex with _ | k'
    · exact ⟨n₀, T₀, hbase⟩
    · have hmin : ¬ max (x[i].time : Int) (x[j].time : Int)
          < Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE + k') :=
        Nat.find_min hex (by omega)
      have hper := Restated.action_succ_eq_add_period facts S (Restated.switchRound M S tE + k')
      have hle : Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE + (k' + 1)) ≤ tHi := by
        show Restated.Vocabulary.Execution.Setup.a M S (Restated.switchRound M S tE + k' + 1) ≤ tHi
        rw [hper]
        linarith [not_lt.mp hmin]
      obtain ⟨n, T, hinv, -⟩ :=
        Restated.afterPhaseInvariantOverActiveSetsSince_of_stepFrom_bounded facts S Sched x tE tHi hbase hstep
          (k' + 1) hle
      exact ⟨n, T, hinv⟩
  obtain ⟨n, T, hinv⟩ := hinvk
  obtain ⟨htick1, -⟩ := Restated.tickStepAt_time facts x hinv.tick
  have hi : i ≤ n + 1 := by
    by_contra hcon
    have hle : (x[n + 1].time : Int) ≤ (x[i].time : Int) := by
      exact_mod_cast Restated.time_mono facts S Sched x (Nat.le_of_lt (Nat.lt_of_not_le hcon))
    have hmx : (x[i].time : Int) ≤ max (x[i].time : Int) (x[j].time : Int) := le_max_left _ _
    rw [htick1] at hle
    linarith
  have hj : j ≤ n + 1 := by
    by_contra hcon
    have hle : (x[n + 1].time : Int) ≤ (x[j].time : Int) := by
      exact_mod_cast Restated.time_mono facts S Sched x (Nat.le_of_lt (Nat.lt_of_not_le hcon))
    have hmx : (x[j].time : Int) ≤ max (x[i].time : Int) (x[j].time : Int) := le_max_right _ _
    rw [htick1] at hle
    linarith
  -- both finalized blocks are ancestors of that round's one anchor
  exact compatible_iff_Compatible.mpr
    (compatible_of_preceq_common_Preceq (hinv.fin v₁ i hi hhon₁) (hinv.fin v₂ j hj hhon₂))

end

end DecoupledConsensusModel.Sts.Restated
