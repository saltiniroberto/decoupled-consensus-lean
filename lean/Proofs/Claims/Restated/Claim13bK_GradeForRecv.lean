import Model.Record.ModelSpellings
import Proofs.Vocabulary.ModelVocabularyFacts
import Proofs.Claims.Restated.Claim13bK_AttestedDescendant
import Proofs.Claims.Restated.Claim13bK_ConfirmedRecord
import Proofs.Claims.Restated.Claim13bK_FinBeforeTick
import Proofs.Claims.Restated.Claim13bK_FreshAttestersW
import Proofs.Claims.Restated.Claim13bK_GradeLate
import Proofs.Claims.Restated.Claim13bK_GradeOld
import Proofs.Claims.Restated.Claim13bK_LiveConfirmedSlots
import Proofs.Claims.Restated.Claim13bPhaseSleepiness
import Proofs.Claims.Restated.Claim13bStepAssembly
import Proofs.Claims.Restated.Claim13bStepConeIter
import Proofs.Claims.Restated.Claim13bStepGrade
import Proofs.Claims.Restated.Claim13bStepKitDelivery
import Proofs.Claims.Restated.Claim13bStepKitTick
import Proofs.Claims.Restated.Claim13bStepSG
import Proofs.Claims.Restated.Claim13beRoute3_82
import Model.Conditions.Claim13bInvariant
import Model.Conditions.Claim13bInvariantActiveJoint
import Model.Conditions.Claim13bInvariantActiveSinceW
import Model.Conditions.Claim13bInvariantActiveTop
import Model.Conditions.Claim13bK_FinBeforeTick
import Model.Conditions.Claim13bK_FreshAttestersW
import Model.Conditions.Claim13bKit
import Model.Conditions.Claim13bSGCompatible
import Model.Conditions.Claim13bStepAssembly
import Model.Conditions.Claim13bStepConeIter
import Model.Conditions.Claim13bStepKitTick
import Model.Conditions.Claim13bStepSG
import Model.Conditions.Claim13beRoute3_42b
import Model.Conditions.Claim13beRoute3_74
import Model.Conditions.Claim13beRoute3_83
import Model.Conditions.RunAll
import Model.Conditions.Sts_Conditions
import Model.Conditions.Sts_Constants
import Model.Conditions.Sts_Interface
import Model.Conditions.Sts_Spec2Claims_Claim13bd
import Model.Conditions.Sts_Spec2Claims_Claim13be
import Model.Conditions.Sts_Spec2Claims_Claim13bf
import Model.Conditions.Vocabulary_Model_Execution_Setup
import Model.Record.Wiring
import Proofs.Claims.Restated.Claim13bK_GradeFor
import Proofs.Claims.Restated.Claim13bK_GradeLateRecv

/-!
# Grades for a descendant at a reader, from a receipt

`positive_of_fresh`, `gradeBool_of_fresh` and `gradeBool_of_headsBelow_of_stamp` of
`Claim13bK_GradeFor.lean` with the reader `v`'s awake window replaced by its receipt of round `q`'s
honest attestations before round `q + 1`'s first cutoff of the phase read and its honesty through
the read.
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
local macro "pHP% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13bK_HeadsPersist)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "pCW% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13bK_ConfirmedWake)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
local macro "pW% " n:ident : term =>
  `(priv% $(Lean.mkIdent `Proofs.Claims.Restated.Claim13bK_ConfirmedStrongRoundWindow)
    $(Lean.mkIdent (`DecoupledConsensusModel.Sts.Restated ++ n.getId)))
/-- From any node state `before`, validator `v`'s round-`r` action can compute some attestation. -/
private theorem actionAttestationFrom_nonempty_gf (facts : Record.Facts M)
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

/-- If `v` receives round `q`'s honest attestations before round `q + 1`'s first cutoff of phase
    `p` and is honest through step `m`, every tick of a validator awake and not held up to it has an
    outcome, and every block a member's
    round-`q` attestation names resolves in `v`'s tree, is stamped before the phase's early cutoff,
    is on one chain with `v`'s finalized block and is a descendant of `X` or `X` itself, then every
    outcome of the test whether a member `v_1` of `freshAttestersW S Sched x q m` supports `X` in
    `v`'s grade view for round `q + 1` at phase `p` is `true`. -/
theorem positive_of_fresh_recv (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (htd : Restated.TimeDiverges M x)
    {q : Round} {n : Nat} (hn : Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S q))) (hgst : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S q))
    {m : Nat} {v : V} {p : Protocol.Phase}
    (hm : Restated.stepBeforeInstant M x m (M.domain S.E S.hc (q + 1) p))
    (hrecv : Restated.ReceivesRoundAttestationsBefore M S Sched x q v (M.early S.E S.hc (q + 1) p))
    (hwm : HonestThroughTime Sched (x[m].time : Int) v)
    (hexp : (M.round_of S.hc (S.E.slotOf (x[m].time : Int))) ≤ q + S.hc.η_SG)
    (hroom : ∀ k : Nat, k < m → ∀ v_1 ∈ Restated.freshAttestersW M S Sched x q m,
      ∀ a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][v_1].st) v_1 q,
      x.lbl k = AtomicAction.deliver v ⟨v_1, NamedObject.attest a⟩ →
      (M.round_votes (x[k][v].st).st.core a.erase).card ≠ 2)
    (hheads : ∀ v_1 ∈ Restated.freshAttestersW M S Sched x q m, ∀ C : NamedBlock V,
      C ∈ (x[n + 1][v_1].st).st.bodies →
      ∀ a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][v_1].st) v_1 q,
      a.confirmed = some C.root →
      Block.find? (x[m][v].st).st.core.T C.root = some C.erase ∧
      stampedBefore (x[m][v].st).st.core.timestamp_block
        (M.early S.E S.hc (q + 1) p) C.erase = true ∧
      Block.compatible C.erase (x[m][v].st).st.core.F = true)
    {X : Block V}
    (hcov : ∀ v_1 ∈ Restated.freshAttestersW M S Sched x q m, ∀ C : NamedBlock V,
      C ∈ (x[n + 1][v_1].st).st.bodies →
      ∀ a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][v_1].st) v_1 q,
      a.confirmed = some C.root →
      Block.Preceq X C.erase)
    {v_1 : V} (hv_1 : v_1 ∈ Restated.freshAttestersW M S Sched x q m)
    -- Every tick of a validator awake and not held by the adversary up to it has an outcome.
    (hnr : ∀ (k τ : Nat) (u : V), x.lbl k = AtomicAction.tickAllAwake τ →
      u ∈ Sched.awake (τ : Int) \ Sched.adv (τ : Int) →
      (∀ t' ≤ (τ : Int), u ∉ Sched.adv t') →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) u (Record.wakeStage M Sched (τ : Int) x[k] u) (τ : Int) ⇢ out)
    (hneAtt : ∃ out : M.N × List (NamedObject V),
      M.tick (Setup.alwaysAwake S) v_1 (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S q) x[n] v_1)
        (Restated.Vocabulary.Execution.Setup.a M S q) ⇢ out) :
    ∀ b : Bool, M.positive (M.gradeView (M.toHealing (x[m][v].st).st.core)) (x[m][v].st).st.core.F
      S.hc.η_SG (q + 1) (M.early S.E S.hc (q + 1) p) (M.late S.E S.hc (q + 1) p)
      v_1 X ⇢ b → b = true := by
  intro b hb
  have hv1m : Restated.HonestThrough M Sched x m v_1 := Restated.honestThrough_of_mem_freshAttestersW facts hv_1
  obtain ⟨a, ha⟩ := actionAttestationFrom_nonempty_gf facts (Setup.alwaysAwake S) (x[n][v_1].st) v_1 q
  have hsome : ∃ root : BlockId, a.confirmed = some root := by
    obtain ⟨n_1, hn_1, ns, rec, hD⟩ := id ha
    obtain ⟨g, hg⟩ := facts.gr.read_nonempty (M.gradeContract n_1.cache) S.E S.hc
      (M.toHealing n_1.st.core) q
    rw [facts.nd.gradeContract_read] at hg
    exact ⟨_, Restated.attest_confirmed_eq_sgVote facts S (x[n][v_1].st) v_1 q n_1 hn_1
      (ns, rec, a) hD g hg⟩
  obtain ⟨root, hrootc⟩ := hsome
  obtain ⟨C, hCbody, hCroot⟩ := Restated.hhead_mem_of_tick facts S Sched x n q v_1 a ha root hrootc
  have hconfC : a.confirmed = some C.root := by rw [hCroot]; exact hrootc
  obtain ⟨hfind, hstamped, hcompat⟩ := hheads v_1 hv_1 C hCbody a ha hconfC
  have hfind' : Block.find? (M.gradeView (M.toHealing (x[m][v].st).st.core)).T C.root = some C.erase := by
    rw [facts.gr.Sts_gradeView_T]; exact hfind
  obtain ⟨X2, hX2⟩ := facts.gr.rawInputs_nonempty (M.gradeView (M.toHealing (x[m][v].st).st.core))
    S.hc.η_SG (q + 1) (M.early S.E S.hc (q + 1) p) v_1
  obtain ⟨Xe, hXe⟩ := facts.gr.rawInputs_nonempty (M.gradeView (M.toHealing (x[m][v].st).st.core))
    S.hc.η_SG (q + 1) (M.early S.E S.hc (q + 1) p) v_1
  have hraw2 := Restated.fresh_token_in_viewLate_recv facts S Sched x htd hexec.toUnforgeability hn hgst hm
    hrecv hwm hexp hroom hv_1 hnr hneAtt a ha X2 hX2
  have hraw := facts.gr.rawInputs_mono
    (M.gradeView (M.toHealing (x[m][v].st).st.core)) S.hc.η_SG (q + 1)
    le_rfl v_1 X2 hX2 Xe hXe hraw2
  have hsgconf : (M.sgVote a.erase).confirmed = some C.root := by
    rw [facts.sto.sgVote_confirmed]; exact hconfC
  obtain ⟨bb, hbb⟩ := facts.gr.bodyReady_nonempty (M.gradeView (M.toHealing (x[m][v].st).st.core))
    (x[m][v].st).st.core.F (M.early S.E S.hc (q + 1) p) (M.sgVote a.erase)
  have hready : bb = true :=
    facts.gr.bodyReady_of_head _ _ _ _ hsgconf hfind'
      (by rw [facts.gr.gradeView_timestamp_block]; exact hstamped) hcompat bb hbb
  obtain ⟨Re, hRe⟩ := facts.gr.readyView_nonempty (M.gradeView (M.toHealing (x[m][v].st).st.core))
    (x[m][v].st).st.core.F S.hc.η_SG (q + 1) (M.early S.E S.hc (q + 1) p) v_1
  have hmem := facts.gr.token_mem_readyView _ _ _ _ _ _ Xe hXe hraw bb hbb hready Re hRe
  have hround : (M.token (M.sgVote a.erase)).round = q := by
    rw [facts.gr.token_round, facts.sto.sgVote_round]
    exact Restated.actionAttestationFrom_round facts (Setup.alwaysAwake S) _ v_1 q a ha
  have hkey : (M.token (M.sgVote a.erase)).key = some C.root := by
    rw [facts.gr.token_key]; exact hsgconf
  obtain ⟨Xr, hXr⟩ := facts.gr.rawView_nonempty (M.gradeView (M.toHealing (x[m][v].st).st.core))
    S.hc.η_SG (q + 1) (M.early S.E S.hc (q + 1) p) v_1
  obtain ⟨Wl, hWl⟩ := facts.gr.rawView_nonempty (M.gradeView (M.toHealing (x[m][v].st).st.core))
    S.hc.η_SG (q + 1) (M.late S.E S.hc (q + 1) p) v_1
  obtain ⟨Rl, hRl⟩ := facts.gr.readyView_nonempty (M.gradeView (M.toHealing (x[m][v].st).st.core))
    (x[m][v].st).st.core.F S.hc.η_SG (q + 1) (M.late S.E S.hc (q + 1) p) v_1
  have hcov' : ∀ k, M.head_covers (M.gradeView (M.toHealing (x[m][v].st).st.core)).T X k ⇢
      (fun k => (facts.gr.head_covers_nonempty
        (M.gradeView (M.toHealing (x[m][v].st).st.core)).T X k).choose) k :=
    fun k => (facts.gr.head_covers_nonempty _ X k).choose_spec
  refine facts.gr.positive_of_conditions _ _ S.hc.η_SG (q + 1) _ _ v_1 X _ Re hRe hmem ?_ _ hcov'
    ?_ Wl hWl ?_ Rl hRl ?_ b hb
  · intro y hy
    rw [hround]
    exact Restated.rawView_round_le facts S Sched x m v q _ v_1 Xr hXr y
      (facts.gr.readyView_subset_rawView _ _ _ _ _ _ Re hRe Xr hXr hy)
  · rw [hkey]
    exact facts.gr.head_covers_of_find hfind' (hcov v_1 hv_1 C hCbody a ha hconfC) _
      (hcov' (some C.root))
  · intro y hy z hz hle hyz
    rw [hround] at hle
    have hyq : y.round = q := le_antisymm (Restated.rawView_round_le facts S Sched x m v q _ v_1 Wl hWl y hy) hle
    have hzq : z.round = q := hyz.symm.trans hyq
    rw [Restated.rawView_key_of_honest facts S Sched x hexec hn hv1m hWl hy hyq a ha,
      Restated.rawView_key_of_honest facts S Sched x hexec hn hv1m hWl hz hzq a ha]
  · intro y hy hlt
    rw [hround] at hlt
    exact absurd (Restated.rawView_round_le facts S Sched x m v q _ v_1 Wl hWl y
      (facts.gr.readyView_subset_rawView _ _ _ _ _ _ Rl hRl Wl hWl hy)) (not_le.mpr hlt)

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- Under the hypotheses of `positive_of_fresh_recv`, if the validators holding a raw token in `v`'s view
    at the late cutoff, other than the members of `freshAttestersW S Sched x q m`, weigh less than
    those members, then every outcome of `v`'s grade test for `X` at round `q + 1` and phase `p` is
    `true`. -/
theorem gradeBool_of_fresh_recv (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V)
    (x : AtomicExec (Record.protocolOf M S) Sched)
    (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x)
    (htd : Restated.TimeDiverges M x)
    {q : Round} {n : Nat} (hn : Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S q))) (hgst : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S q))
    {m : Nat} {v : V} {p : Protocol.Phase}
    (hm : Restated.stepBeforeInstant M x m (M.domain S.E S.hc (q + 1) p))
    (hrecv : Restated.ReceivesRoundAttestationsBefore M S Sched x q v (M.early S.E S.hc (q + 1) p))
    (hwm : HonestThroughTime Sched (x[m].time : Int) v)
    (hexp : (M.round_of S.hc (S.E.slotOf (x[m].time : Int))) ≤ q + S.hc.η_SG)
    (hroom : ∀ k : Nat, k < m → ∀ v_1 ∈ Restated.freshAttestersW M S Sched x q m,
      ∀ a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][v_1].st) v_1 q,
      x.lbl k = AtomicAction.deliver v ⟨v_1, NamedObject.attest a⟩ →
      (M.round_votes (x[k][v].st).st.core a.erase).card ≠ 2)
    (hheads : ∀ v_1 ∈ Restated.freshAttestersW M S Sched x q m, ∀ C : NamedBlock V,
      C ∈ (x[n + 1][v_1].st).st.bodies →
      ∀ a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][v_1].st) v_1 q,
      a.confirmed = some C.root →
      Block.find? (x[m][v].st).st.core.T C.root = some C.erase ∧
      stampedBefore (x[m][v].st).st.core.timestamp_block
        (M.early S.E S.hc (q + 1) p) C.erase = true ∧
      Block.compatible C.erase (x[m][v].st).st.core.F = true)
    {X : Block V}
    (hcov : ∀ v_1 ∈ Restated.freshAttestersW M S Sched x q m, ∀ C : NamedBlock V,
      C ∈ (x[n + 1][v_1].st).st.bodies →
      ∀ a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][v_1].st) v_1 q,
      a.confirmed = some C.root →
      Block.Preceq X C.erase)
    (raw : V → Finset (Protocol.Token (Option BlockId)))
    (hraw : ∀ u, M.rawView (M.gradeView (M.toHealing (x[m][v].st).st.core)) S.hc.η_SG (q + 1)
      (M.late S.E S.hc (q + 1) p) u ⇢ raw u)
    (hhalf : S.E.electorate.weightOf
        ((Finset.univ.filter (fun v_1 => (raw v_1).Nonempty))
          \ Restated.freshAttestersW M S Sched x q m)
      < S.E.electorate.weightOf (Restated.freshAttestersW M S Sched x q m))
    -- Every tick of a validator awake and not held by the adversary up to it has an outcome.
    (hnr : ∀ (k τ : Nat) (u : V), x.lbl k = AtomicAction.tickAllAwake τ →
      u ∈ Sched.awake (τ : Int) \ Sched.adv (τ : Int) →
      (∀ t' ≤ (τ : Int), u ∉ Sched.adv t') →
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) u (Record.wakeStage M Sched (τ : Int) x[k] u) (τ : Int) ⇢ out)
    (hneAtt : ∀ v_1 ∈ Restated.freshAttestersW M S Sched x q m,
      ∃ out : M.N × List (NamedObject V),
        M.tick (Setup.alwaysAwake S) v_1 (Record.wakeStage M Sched (Restated.Vocabulary.Execution.Setup.a M S q) x[n] v_1)
          (Restated.Vocabulary.Execution.Setup.a M S q) ⇢ out) :
    ∀ g : Bool, M.gradeBool S.E (M.gradeView (M.toHealing (x[m][v].st).st.core)) (x[m][v].st).st.core.F
      S.hc.η_SG (q + 1) (M.early S.E S.hc (q + 1) p) (M.late S.E S.hc (q + 1) p)
      X ⇢ g → g = true := by
  intro g hg
  have hposf : ∀ u, M.positive (M.gradeView (M.toHealing (x[m][v].st).st.core))
      (x[m][v].st).st.core.F S.hc.η_SG (q + 1) (M.early S.E S.hc (q + 1) p)
      (M.late S.E S.hc (q + 1) p) u X ⇢
      (fun u => (facts.gr.positive_nonempty (M.gradeView (M.toHealing (x[m][v].st).st.core))
        (x[m][v].st).st.core.F S.hc.η_SG (q + 1) (M.early S.E S.hc (q + 1) p)
        (M.late S.E S.hc (q + 1) p) u X).choose) u :=
    fun u => (facts.gr.positive_nonempty _ _ _ _ _ _ u X).choose_spec
  exact facts.gr.gradeBool_of_supporters S.E _ _ _ _ _ _ X (Restated.freshAttestersW M S Sched x q m)
    _ hposf raw hraw (facts.gr.early_le_late S.E S.hc (q + 1) p)
    (fun u hu => Restated.positive_of_fresh_recv facts S Sched x hexec htd hn hgst hm hrecv hwm hexp hroom
      hheads hcov hu hnr (hneAtt u hu) _ (hposf u))
    hhalf g hg

end

section
set_option autoImplicit false
open Framework.StsMultisetLog
open DecoupledConsensusModel.Execution
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| exact True.intro)

/-- If `q` is at least two rounds after the switch round, every honest active member of the
    committee of round `q`'s opening slot votes there for a descendant of `X`, `v` receives
    round `q`'s honest attestations before round `q + 1`'s first cutoff of phase `p` and is not held
    at `domain (q + 1) p`, and every block a
    member's round-`q` attestation names resolves in `v`'s tree after `m` steps with a stamp
    strictly before round `q + 1`'s early cutoff of phase `p`, then every outcome of `v`'s grade
    test for `X` at round `q + 1` and phase `p` after `m` steps is `true`. -/
theorem gradeBool_of_headsBelow_of_stamp_recv (facts : Record.Facts M) (S : Setup V) (Sched : Schedule V) (x : AtomicExec (Record.protocolOf M S) Sched) (tE : Int) (hexec : Restated.ExecutionValid M S Sched (Restated.interface M S Sched) x) (hmono : Sched.MonotoneCorruption) (htd : Restated.TimeDiverges M x) (hcatch : Restated.CatchUpOnWake M S x) (tGAT : Int) (gap : Nat) (hgst : S.E.t_GST ≤ tGAT) (hlen : tGAT + Restated.healingLengthη M S gap ≤ tE) (hsync : Restated.SynchronyFromWake M S x) (hthird : ∀ t : Int, t ≤ tE →
      3 * S.E.electorate.weightOf (Sched.adv t) < S.E.electorate.totalWeight) (hphase : ∀ t : Int, tGAT ≤ t → t ≤ tE →
      ∀ v : V, v ∉ Sched.adv t → v ∈ Sched.awake t) (hrsW : Restated.roundSleepinessW M S Sched tE) (hmult : AwakeAtMultiples S Sched) (hcv : Restated.CommonViewOfFinalizedDescendantsAt M S Sched x tGAT) (hcs : Restated.committeeSleepinessW M S Sched tE) (hcom : Restated.HonestCommittees M S Sched (Restated.interface M S Sched)) (hrec : Restated.strongOpeningsRecurFrom M S Sched tGAT tE gap) (hprev : ∀ r : Round, Restated.rebasedDeadlineRoundW M S tGAT gap ≤ r → r ≤ Restated.switchRound M S tE →
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
    {n₀ : Nat} {T₀ : NamedBlock V} (hTW₀ : Block.Preceq T_W.erase T₀.erase)
    (hJ₀ : Restated.AfterPhaseInvariantOverActiveSetsJoint M S Sched x (Restated.switchRound M S tE) n₀ n_W T₀)
    {q : Round} (hq : Restated.switchRound M S tE + 2 ≤ q)
    {X : Block V} (hX : Restated.HeadsBelow M S Sched x X ((M.opening_slot S.hc q)))
    {n : Nat} (hn : Restated.tickStepAt M x n ((Restated.Vocabulary.Execution.Setup.a M S q)))
    {p : Protocol.Phase} {m : Nat}
    (hm : Restated.stepBeforeInstant M x m (M.domain S.E S.hc (q + 1) p))
    {v : V} (hrecv : Restated.ReceivesRoundAttestationsBefore M S Sched x q v (M.early S.E S.hc (q + 1) p))
    (hvS : v ∉ Sched.adv (M.domain S.E S.hc (q + 1) p))
    (hstamp : ∀ v_1 ∈ Restated.freshAttestersW M S Sched x q m, ∀ C : NamedBlock V,
      C ∈ (x[n + 1][v_1].st).st.bodies →
      ∀ a ∈ Restated.actionAttestationFrom M (Setup.alwaysAwake S) (x[n][v_1].st) v_1 q,
      a.confirmed = some C.root →
      Block.find? (x[m][v].st).st.core.T C.root = some C.erase ∧
      stampedBefore (x[m][v].st).st.core.timestamp_block
        (M.early S.E S.hc (q + 1) p) C.erase = true) :
    ∀ g : Bool, M.gradeBool S.E (M.gradeView (M.toHealing (x[m][v].st).st.core)) (x[m][v].st).st.core.F
      S.hc.η_SG (q + 1) (M.early S.E S.hc (q + 1) p) (M.late S.E S.hc (q + 1) p)
      X ⇢ g → g = true := by
  have hr : Restated.switchRound M S tE ≤ q := le_trans (Nat.le_add_right _ 2) hq
  have hdom : M.domain S.E S.hc (q + 1) p ≤ (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) := facts.gr.domain_le_action S (q + 1) p
  have hmd : (x[m].time : Int) < M.domain S.E S.hc (q + 1) p :=
    Restated.time_lt_domain_of_stepBefore facts S Sched x htd hm
  have htm : (x[m].time : Int) ≤ (Restated.Vocabulary.Execution.Setup.a M S (q + 1)) :=
    Restated.time_le_action_succ_of_stepBefore facts S Sched x htd hdom hm
  have ham : (Restated.Vocabulary.Execution.Setup.a M S q) ≤ (x[m].time : Int) := Restated.action_le_time_of_stepBefore facts S Sched x htd hm
  have hopen : M.opening S.E S.hc q ≤ Restated.Vocabulary.Execution.Setup.a M S q := by
    show _ ≤ M.a S.hc S.E.Δ q
    rw [facts.gr.opening_eq_proposal_time, facts.sch.a_eq_confirmation_time]
    exact facts.sch.proposal_time_le_confirmation_time _ _
  have hgstq : S.E.t_GST ≤ (Restated.Vocabulary.Execution.Setup.a M S q) :=
    le_trans (Restated.gst_le_switchOpening facts S tGAT tE gap hgst hlen)
      (le_trans (Restated.switchOpening_le_opening facts S hr) hopen)
  have hvm : Restated.HonestThrough M Sched x m v := fun t ht hin =>
    hvS (hmono t _ (le_trans ht (le_of_lt hmd)) hin)
  obtain ⟨n', hn'⟩ := Restated.tick_field_at_succ facts S Sched x htd q
  have hmn' : m ≤ n' := Restated.stepBefore_le_tick facts x hm hn' hdom
  have hrs := Restated.roundSleepinessW_switchOpening_of_phase facts S Sched tGAT tE gap hgst hlen hmono hthird
    hphase hrsW
  have hrawf : ∀ u, M.rawView (M.gradeView (M.toHealing (x[m][v].st).st.core)) S.hc.η_SG (q + 1)
      (M.late S.E S.hc (q + 1) p) u ⇢
      (fun u => (facts.gr.rawView_nonempty (M.gradeView (M.toHealing (x[m][v].st).st.core))
        S.hc.η_SG (q + 1) (M.late S.E S.hc (q + 1) p) u).choose) u :=
    fun u => (facts.gr.rawView_nonempty _ _ _ _ u).choose_spec
  refine Restated.gradeBool_of_fresh_recv facts S Sched x hexec htd hn hgstq hm hrecv hvm (Restated.hexp_of_domain facts S htm)
    (fun k hk v_1 hv_1 a ha _ => Restated.hroom_of_fresh facts S Sched x hexec hn
      (fun t ht => Restated.honestThrough_of_mem_freshAttestersW facts hv_1 t
        (le_trans ht (Restated.time_mono_int facts S Sched x (le_of_lt hk)))) a ha)
    ?_ ?_ _ hrawf
    (Restated.hhalf_of_roundSleepinessW facts S Sched x hexec htd hmono hrs
      (Restated.switchOpening_le_opening facts S (le_trans hr (Nat.le_succ q)))
      (Restated.eta_le_of_switchRound_le facts S tGAT tE gap hgst hlen hr) hdom hm _ hrawf)
    (facts.ndRun.tick_outcome_sts S Sched x hexec.idealization.root_injective hexec.honestRootsNew)
    (fun v_1 hv_1 => Restated.tick_outcome_of_tickStepAt facts S Sched x
      hexec.idealization.root_injective hexec.honestRootsNew hmono hn (Restated.action_emod_delta facts S q)
      (Finset.mem_sdiff.2 ⟨Restated.awake_of_mem_freshAttesters facts
          (Restated.freshAttestersW_subset_freshAttesters facts S Sched x q m hv_1),
        Restated.honestThrough_of_mem_freshAttestersW facts hv_1 _ ham⟩))
  · intro v_1 hv_1 C hC a ha hconf
    obtain ⟨hfind, hst⟩ := hstamp v_1 hv_1 C hC a ha hconf
    exact ⟨hfind, hst, Protocol.compatible_comm
      (Restated.fresh_attested_compatible_finalized facts S Sched x tE hexec hmono htd hcatch tGAT gap hgst hlen
        hsync hthird hphase hrsW hmult hcv hcs hcom hrec hprev hclear hB' hnW hAW hJswitch
        hTW₀ hJ₀ hr hn hn' hm hv_1 hC a ha hconf v m hmn' hvm)⟩
  · intro v_1 hv_1 C hC a ha hconf
    exact Restated.attested_descendant_of_headsBelow facts S Sched x tE hexec hmono htd hcatch tGAT gap hgst hlen
      hsync hthird hphase hrsW hmult hcv hcs hcom hrec hprev hclear hB' hnW hAW hJswitch
      hTW₀ hJ₀ hq hX hn (Restated.hfreshH_of_stepBefore facts S Sched x htd hm hv_1) hC a ha hconf

end

end DecoupledConsensusModel.Sts.Restated
