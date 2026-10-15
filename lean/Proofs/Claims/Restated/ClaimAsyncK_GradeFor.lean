import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bK_FreshAttestersW
import Proofs.Claims.Restated.Claim13bK_GradeOld
import Proofs.Claims.Restated.Claim13bStepGrade
import Proofs.Claims.Restated.Claim13bStepKitTick
import Proofs.Claims.Restated.ClaimAsyncK_GradeAgainst
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bK_FreshAttestersW
import Model.Conditions.Claim13bStepKitTick
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Sts_Spec2Claims_ClaimStableThroughAsyncPeriod
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring

/-!
# Grading a block from the tokens that cover it

Theorems over a model `M : Record.Model V` with facts `facts : Record.Facts M`: honest validators
whose tokens cover `P` support `P`, the counted attesters outweigh the other holders of a raw token,
and from these `P` is graded at round `r + 1` while no block conflicting with `P` is
(`gradeBool_base_of_tokens`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace DecoupledConsensusModel.Sts.Restated

open scoped DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V]
variable {M : Record.Model V}

/-- From any node state `before`, validator `v`'s round-`r` action read can compute some
    attestation. -/
private theorem actionAttestationFrom_nonemptyGradeFor (facts : Record.Facts M)
    (S : DecoupledConsensusModel.Execution.Setup V)
    (before : M.N) (v : V) (r : Round) :
    ∃ a, a ∈ Restated.actionAttestationFrom M S before v r := by
  obtain ⟨c, hc⟩ := facts.gr.onPhaseTick_nonempty S.E S.hc before.st.core.toHealing
    (Restated.Vocabulary.Execution.Setup.a M S r) before.cache
  obtain ⟨st, hst⟩ := facts.dt.duties_update_confirmation_with_nonempty (M.gradeContract c) S.E S.hc
    (M.ns_setClock S.E before.st (Restated.Vocabulary.Execution.Setup.a M S r))
    (S.E.slotOf (Restated.Vocabulary.Execution.Setup.a M S r) - 1)
  obtain ⟨D, hD⟩ := facts.dt.attest_with_nonempty (M.gradeContract (M.mkNode st before.record c).cache)
    S.E S.hc (S.node v) (M.mkNode st before.record c).st (M.mkNode st before.record c).record
  exact ⟨D.2.2, M.mkNode st before.record c, ⟨c, hc, st, hst, rfl⟩, D.1, D.2.1, hD⟩

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If `ρ ≥ 1`, `m` is the last step before round `ρ`'s phase-`p` instant, corruption is monotone,
    and the adversary does not hold `v` at the opening of round `ρ + 1`, then the adversary holds
    `v` at no time up to step `m`. -/
theorem honestThrough_of_not_adv_opening_succ (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (htd : Restated.TimeDiverges M x)
    (hmono : Sched.MonotoneCorruption) {ρ : Nat} (hρ : 1 ≤ ρ) {m : Nat}
    {p : Protocol.Phase} (hm : Restated.stepBeforeInstant M x m (M.domain S.E S.hc ρ p)) {v : V}
    (hv : v ∉ Sched.adv (M.opening S.E S.hc (ρ + 1))) :
    Restated.HonestThrough M Sched x m v := by
  obtain ⟨ρ', rfl⟩ : ∃ ρ', ρ = ρ' + 1 := ⟨ρ - 1, by omega⟩
  have hnext : Restated.Vocabulary.Execution.Setup.a M S (ρ' + 1) ≤ M.opening S.E S.hc (ρ' + 1 + 1) := by
    have h1 := facts.gr.action_delta_le_early S S.hc.R_ge_three (Nat.lt_succ_self (ρ' + 1))
    have h2 := facts.gr.early_g2_le_opening S (ρ' + 1 + 1)
    have hd := S.E.Δ_pos
    show M.a S.hc S.E.Δ _ ≤ _
    linarith
  have htm : (x[m].time : Int) ≤ M.opening S.E S.hc (ρ' + 1 + 1) :=
    le_trans (Restated.time_le_action_succ_of_stepBefore facts S Sched x htd (facts.gr.domain_le_action S _ p) hm)
      hnext
  intro t ht hmem
  exact hv (hmono _ _ (le_trans ht htm) hmem)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Under the participation premise `fixedRoundSleepinessCountedW S Sched r`, for a round `ρ` from
    `r + 1` to `r + η_SG + 1`, at the last step before round `ρ`'s phase-`p` instant, and with
    `raw u` an outcome of `u`'s raw view at the late cutoff for every validator `u`: the validators
    with a non-empty `raw u`, other than the members of
    `activeRoundWThroughNextCountedAt S Sched r ρ` that the adversary does not hold at the opening
    of round `ρ + 1`, weigh less than those members. -/
theorem hhalf_of_fixedRoundSleepinessCountedW (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (htd : Restated.TimeDiverges M x) (hmono : Sched.MonotoneCorruption) {r : Nat}
    (hfix : Restated.fixedRoundSleepinessCountedW M S Sched r) {ρ : Nat} (hρ₁ : r + 1 ≤ ρ)
    (hρ₂ : ρ ≤ r + S.hc.η_SG + 1) {m : Nat} {w : V} {p : Protocol.Phase}
    (hm : Restated.stepBeforeInstant M x m (M.domain S.E S.hc ρ p))
    (raw : V → Finset (Protocol.Token (Option BlockId)))
    (hraw : ∀ u, M.rawView (M.gradeView (M.toHealing (x[m][w].st).st.core)) S.hc.η_SG ρ
      (M.late S.E S.hc ρ p) u ⇢ raw u) :
    S.E.electorate.weightOf
        ((Finset.univ.filter (fun v_1 => (raw v_1).Nonempty))
          \ (Restated.activeRoundWThroughNextCountedAt M S Sched r ρ \
              Sched.adv (M.opening S.E S.hc (ρ + 1))))
      < S.E.electorate.weightOf
          (Restated.activeRoundWThroughNextCountedAt M S Sched r ρ \
            Sched.adv (M.opening S.E S.hc (ρ + 1))) := by
  classical
  have hbound := hfix ρ hρ₁ hρ₂
  have hcover : (Finset.univ.filter (fun v_1 => (raw v_1).Nonempty))
          \ (Restated.activeRoundWThroughNextCountedAt M S Sched r ρ \
              Sched.adv (M.opening S.E S.hc (ρ + 1)))
      ⊆ Sched.adv (M.opening S.E S.hc (ρ + 1)) ∪
          (Restated.attestersIn M S Sched (ρ - S.hc.η_SG) (ρ - 1) \
            (Restated.activeRoundWThroughNextCountedAt M S Sched r ρ \
              Sched.adv (M.opening S.E S.hc (ρ + 1)))) := by
    intro v hv
    obtain ⟨hvhold, hvH⟩ := Finset.mem_sdiff.1 hv
    by_cases hadv : v ∈ Sched.adv (M.opening S.E S.hc (ρ + 1))
    · exact Finset.mem_union_left _ hadv
    refine Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨?_, hvH⟩)
    have hvm : Restated.HonestThrough M Sched x m v :=
      Restated.honestThrough_of_not_adv_opening_succ facts S Sched x htd hmono (by omega) hm hadv
    obtain ⟨tok, htok⟩ := (Finset.mem_filter.1 hvhold).2
    obtain ⟨Y, hY⟩ := facts.gr.rawInputs_nonempty
      (M.gradeView (M.toHealing (x[m][w].st).st.core)) S.hc.η_SG ρ (M.late S.E S.hc ρ p) v
    obtain ⟨u, hu, -⟩ := (facts.gr.mem_rawView_iff _ _ _ _ _ _ _ (hraw v) Y hY).mp htok
    obtain ⟨⟨k, hkw, huk⟩, huidx, -⟩ := facts.gr.rawInputs_mem_window _ _ _ _ _ Y hY hu
    have hukround : u.round = k := Restated.sgVotesRoundIndexed_sts facts S Sched x m w k u huk
    have hu' : u ∈ (M.gradeView (M.toHealing (x[m][w].st).st.core)).sg_votes u.round := by
      rw [hukround]; exact huk
    obtain ⟨-, -, hawk, -⟩ := Restated.token_of_honest_sender facts S Sched x hexec hvm hu' huidx
    rw [hukround] at hawk
    have hlo : ρ - S.hc.η_SG ≤ k := facts.fc.mem_latest_window_ge hkw
    have hhi : k < ρ := facts.fc.mem_latest_window_lt hkw
    simp only [Restated.attestersIn, Finset.mem_biUnion, Finset.mem_Icc]
    exact ⟨k, ⟨hlo, Nat.le_sub_one_of_lt hhi⟩, hawk⟩
  exact lt_of_le_of_lt (S.E.electorate.weightOf_mono hcover) hbound

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- For `ρ ≥ 1`, every member of `activeRoundWThroughNextCountedAt S Sched r ρ` that the adversary
    does not hold at the opening of round `ρ + 1` is honest through the last step before round `ρ`'s
    phase-`p` instant. -/
theorem honestThrough_of_mem_countedAt (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched) (htd : Restated.TimeDiverges M x)
    (hmono : Sched.MonotoneCorruption) {r ρ : Nat} (hρ : 1 ≤ ρ) {m : Nat}
    {p : Protocol.Phase} (hm : Restated.stepBeforeInstant M x m (M.domain S.E S.hc ρ p)) {v : V}
    (hv : v ∈ Restated.activeRoundWThroughNextCountedAt M S Sched r ρ \
      Sched.adv (M.opening S.E S.hc (ρ + 1))) :
    Restated.HonestThrough M Sched x m v :=
  Restated.honestThrough_of_not_adv_opening_succ facts S Sched x htd hmono hρ hm (Finset.mem_sdiff.1 hv).2

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If the adversary has held `v_1` at no time up to step `m`, and `tok` is a round-`q` token of
    `v_1` in an outcome `X` of `v`'s raw view, then at some tick step `n` at `S.a q`, every
    round-`q` attestation that `v_1`'s action can compute from its node state at `n` names the root
    `tok` names. -/
theorem rawView_key_of_honest_at (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {m : Nat} {v v_1 : V} (hv_1 : Restated.HonestThrough M Sched x m v_1) {ρ q : Nat} {c : Int}
    {tok : Protocol.Token (Option BlockId)}
    {X : Finset (Protocol.Token (Option BlockId))}
    (hX : M.rawView (M.gradeView (M.toHealing (x[m][v].st).st.core)) S.hc.η_SG ρ c v_1 ⇢ X)
    (htok : tok ∈ X)
    (hround : tok.round = q) :
    ∃ n : Nat, Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S q)) ∧
      ∀ a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][v_1].st) v_1 q,
        tok.key = a.confirmed := by
  obtain ⟨Y, hY⟩ := facts.gr.rawInputs_nonempty
    (M.gradeView (M.toHealing (x[m][v].st).st.core)) S.hc.η_SG ρ c v_1
  obtain ⟨y, hy, hyt⟩ := (facts.gr.mem_rawView_iff _ _ _ _ _ tok X hX Y hY).mp htok
  obtain ⟨⟨k, -, hyk⟩, hyidx, -⟩ := facts.gr.rawInputs_mem_window _ _ _ _ _ Y hY hy
  have hykround : y.round = k := Restated.sgVotesRoundIndexed_sts facts S Sched x m v k y hyk
  have hymem : y ∈ (M.gradeView (M.toHealing (x[m][v].st).st.core)).sg_votes y.round := by
    rw [hykround]; exact hyk
  obtain ⟨n', htick', -, hyeq⟩ :=
    Restated.token_of_honest_sender facts S Sched x hexec hv_1 hymem hyidx
  have hyq : y.round = q := by rw [← facts.gr.token_round y, hyt]; exact hround
  rw [hyq] at htick' hyeq
  refine ⟨n', htick', fun a ha => ?_⟩
  rw [← hyt, facts.gr.token_key, hyeq a ha, facts.sto.sgVote_confirmed]

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Let `v_1` be honest through step `m` and `q₀` a round. If some token of `v_1` in the outcome
    `Re` of `w`'s early ready view has round at least `q₀`, and every token of `v_1` of round at
    least `q₀` in the outcome `Wl` of `w`'s raw view at the late cutoff names a root that resolves
    in `w`'s tree to `P` or a descendant of `P`, then every outcome of the test whether `v_1`
    supports `P` in `w`'s grade view is `true`. -/
theorem positive_of_tokens_cover (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    {m : Nat} {w v_1 : V} (hv_1 : Restated.HonestThrough M Sched x m v_1) {ρ q₀ : Nat}
    {p : Protocol.Phase} {P : Block V}
    {Re : Finset (Protocol.Token (Option BlockId))}
    (hRe : M.readyView (M.gradeView (M.toHealing (x[m][w].st).st.core))
        (x[m][w].st).st.core.F S.hc.η_SG ρ (M.early S.E S.hc ρ p) v_1 ⇢ Re)
    (hready : ∃ tok ∈ Re, q₀ ≤ tok.round)
    {Wl : Finset (Protocol.Token (Option BlockId))}
    (hWl : M.rawView (M.gradeView (M.toHealing (x[m][w].st).st.core)) S.hc.η_SG ρ
        (M.late S.E S.hc ρ p) v_1 ⇢ Wl)
    (hcover : ∀ tok ∈ Wl, q₀ ≤ tok.round →
      ∃ (root : BlockId) (B : Block V), tok.key = some root ∧
        Block.find? (M.gradeView (M.toHealing (x[m][w].st).st.core)).T root = some B ∧
        Block.Preceq P B) :
    ∀ b : Bool, M.positive (M.gradeView (M.toHealing (x[m][w].st).st.core)) (x[m][w].st).st.core.F
      S.hc.η_SG ρ (M.early S.E S.hc ρ p) (M.late S.E S.hc ρ p) v_1 P ⇢ b → b = true := by
  intro b hb
  have hel := facts.gr.early_le_late S.E S.hc ρ p
  obtain ⟨t₀, ht₀, hq₀⟩ := hready
  obtain ⟨u₀, hu₀, hmax⟩ := Finset.exists_max_image Re (fun t => t.round) ⟨t₀, ht₀⟩
  have hu₀q : q₀ ≤ u₀.round := le_trans hq₀ (hmax t₀ ht₀)
  obtain ⟨Xe, hXe⟩ := facts.gr.rawView_nonempty (M.gradeView (M.toHealing (x[m][w].st).st.core))
    S.hc.η_SG ρ (M.early S.E S.hc ρ p) v_1
  have hu₀raw : u₀ ∈ Wl :=
    facts.gr.rawView_mono _ S.hc.η_SG ρ hel v_1 Xe hXe Wl hWl
      (facts.gr.readyView_subset_rawView _ _ S.hc.η_SG ρ _ v_1 Re hRe Xe hXe hu₀)
  have hcov' : ∀ k, M.head_covers (M.gradeView (M.toHealing (x[m][w].st).st.core)).T P k ⇢
      (fun k => (facts.gr.head_covers_nonempty
        (M.gradeView (M.toHealing (x[m][w].st).st.core)).T P k).choose) k :=
    fun k => (facts.gr.head_covers_nonempty _ P k).choose_spec
  have hcovers : ∀ tok ∈ Wl, q₀ ≤ tok.round →
      (fun k => (facts.gr.head_covers_nonempty
        (M.gradeView (M.toHealing (x[m][w].st).st.core)).T P k).choose) tok.key = true := by
    intro tok htok hq
    obtain ⟨root, B, hkey, hfind, hPB⟩ := hcover tok htok hq
    rw [hkey]
    exact facts.gr.head_covers_of_find hfind hPB _ (hcov' (some root))
  obtain ⟨Rl, hRl⟩ := facts.gr.readyView_nonempty (M.gradeView (M.toHealing (x[m][w].st).st.core))
    (x[m][w].st).st.core.F S.hc.η_SG ρ (M.late S.E S.hc ρ p) v_1
  refine facts.gr.positive_of_conditions _ _ S.hc.η_SG ρ _ _ v_1 P u₀ Re hRe hu₀ hmax _ hcov'
    (hcovers u₀ hu₀raw hu₀q) Wl hWl ?_ Rl hRl ?_ b hb
  · intro y hy z hz _ hyz
    obtain ⟨n₁, htick₁, hk₁⟩ :=
      Restated.rawView_key_of_honest_at facts S Sched x hexec hv_1 hWl hy rfl
    obtain ⟨n₂, htick₂, hk₂⟩ :=
      Restated.rawView_key_of_honest_at facts S Sched x hexec hv_1 hWl hz hyz.symm
    have hnn : n₂ = n₁ := Restated.tickStepAt_unique facts x htick₂ htick₁
    subst hnn
    obtain ⟨a, ha⟩ := actionAttestationFrom_nonemptyGradeFor facts (Setup.alwaysAwake S)
      (x[n₂][v_1].st) v_1 y.round
    rw [hk₁ a ha, hk₂ a ha]
  · intro y hy hlt
    exact hcovers y (facts.gr.readyView_subset_rawView _ _ S.hc.η_SG ρ _ v_1 Rl hRl Wl hWl hy)
      (le_trans hu₀q (le_of_lt hlt))

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- At the last step before round `r + 1`'s phase-`p` instant, under `roundSleepinessW S Sched tE`
    for a time `tE` at or before the opening of round `r + 1`: if `Re u` and `Wl u` are outcomes of
    `u`'s early ready view and late raw view for every validator `u`, every member of
    `freshAttestersW S Sched x r m` has a token of round at least `r` in its `Re`, and every token
    of such a member in its `Wl` of a round at least `r` names a root resolving in `w`'s tree to a
    descendant of `P`, then every outcome of `w`'s grade test for `P` at round `r + 1` and phase `p`
    is `true`, and every outcome of the test for a block `Q` not on one chain with `P` is `false`. -/
theorem gradeBool_base_of_tokens (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (htd : Restated.TimeDiverges M x) (hmono : Sched.MonotoneCorruption) {tE : Int}
    (hrs : Restated.roundSleepinessW M S Sched tE) {r : Nat}
    (htE : tE ≤ M.opening S.E S.hc (r + 1)) {m : Nat} {w : V} {p : Protocol.Phase}
    (hm : Restated.stepBeforeInstant M x m (M.domain S.E S.hc (r + 1) p)) {P : Block V}
    (Re : V → Finset (Protocol.Token (Option BlockId)))
    (hRe : ∀ u, M.readyView (M.gradeView (M.toHealing (x[m][w].st).st.core))
      (x[m][w].st).st.core.F S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) p) u ⇢ Re u)
    (hready : ∀ v_1 ∈ Restated.freshAttestersW M S Sched x r m, ∃ tok ∈ Re v_1, r ≤ tok.round)
    (Wl : V → Finset (Protocol.Token (Option BlockId)))
    (hWl : ∀ u, M.rawView (M.gradeView (M.toHealing (x[m][w].st).st.core)) S.hc.η_SG (r + 1)
      (M.late S.E S.hc (r + 1) p) u ⇢ Wl u)
    (hcover : ∀ v_1 ∈ Restated.freshAttestersW M S Sched x r m,
      ∀ tok ∈ Wl v_1, r ≤ tok.round →
        ∃ (root : BlockId) (B : Block V), tok.key = some root ∧
          Block.find? (M.gradeView (M.toHealing (x[m][w].st).st.core)).T root = some B ∧
          Block.Preceq P B) :
    (∀ g : Bool, M.gradeBool S.E (M.gradeView (M.toHealing (x[m][w].st).st.core))
        (x[m][w].st).st.core.F S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) p)
        (M.late S.E S.hc (r + 1) p) P ⇢ g → g = true) ∧
      ∀ Q : Block V, ¬ Block.Compatible P Q →
        ∀ g : Bool, M.gradeBool S.E (M.gradeView (M.toHealing (x[m][w].st).st.core))
          (x[m][w].st).st.core.F S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) p)
          (M.late S.E S.hc (r + 1) p) Q ⇢ g → g = false := by
  have hel := facts.gr.early_le_late S.E S.hc (r + 1) p
  have hpos : ∀ v_1 ∈ Restated.freshAttestersW M S Sched x r m, ∀ b : Bool,
      M.positive (M.gradeView (M.toHealing (x[m][w].st).st.core)) (x[m][w].st).st.core.F
        S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) p)
        (M.late S.E S.hc (r + 1) p) v_1 P ⇢ b → b = true :=
    fun v_1 hv_1 => Restated.positive_of_tokens_cover facts S Sched x hexec
      (Restated.honestThrough_of_mem_freshAttestersW facts hv_1) (hRe v_1) (hready v_1 hv_1)
      (hWl v_1) (hcover v_1 hv_1)
  have hw := fun raw hraw => Restated.hhalf_of_roundSleepinessW facts S Sched x hexec htd
    hmono hrs htE (v_0 := w) (facts.gr.domain_le_action S (r + 1) p) hm raw hraw
  have hposf : ∀ u, M.positive (M.gradeView (M.toHealing (x[m][w].st).st.core))
      (x[m][w].st).st.core.F S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) p)
      (M.late S.E S.hc (r + 1) p) u P ⇢
      (fun u => (facts.gr.positive_nonempty (M.gradeView (M.toHealing (x[m][w].st).st.core))
        (x[m][w].st).st.core.F S.hc.η_SG (r + 1) (M.early S.E S.hc (r + 1) p)
        (M.late S.E S.hc (r + 1) p) u P).choose) u :=
    fun u => (facts.gr.positive_nonempty _ _ _ _ _ _ u P).choose_spec
  exact ⟨fun g hg => facts.gr.gradeBool_of_supporters S.E _ _ _ _ _ _ P _ _ hposf Wl hWl hel
      (fun u hu => hpos u hu _ (hposf u)) (hw Wl hWl) g hg,
    fun Q hPQ => Restated.notGraded_of_conflicting_supporters facts S.E _ _ _ _ _ _ P Q _ hel hpos
      hw hPQ⟩

end

end DecoupledConsensusModel.Sts.Restated
