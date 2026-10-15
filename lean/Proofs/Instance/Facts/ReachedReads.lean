import Proofs.Instance.Model
import Model.Record.Facts
import Proofs.Instance.Facts.GradesRun
import Proofs.Instance.Facts.Grades
import Proofs.Instance.Facts.ConfirmationTree

/-!
# Reached reads and the cache-writing core equations, at `Model.specDraft`

Proofs at `Model.specDraft` of six fields of `NodeFacts`: writing saved grades changes none of four
core readers, the node states of a confirmation read and of the confirmation duty are reached, and a
wake keeps the validator a node state runs as.
-/

set_option autoImplicit false

namespace SpecDraftRecord.ReachedReads

open DecoupledConsensusModel DecoupledConsensusModel.Sts DecoupledConsensusModel.Sts.Record
open DecoupledConsensusModel.Execution
open SpecDraftRecord.NoRaise SpecDraftRecord.GradesRunFacts
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

omit [DecidableEq V] [Fintype V] [Inhabited V] in
/-- Saved grades whose blocks are blocks of `T` satisfy the claim that every computed result's block
    is a block of `T`. -/
theorem claim_of_contractInTree {T : Finset (Spec.Block V)}
    {c : Spec.SavedGrades V} (h : Spec.Store.ContractInTree T c) :
    CacheClaim c (fun _ _ G => ∀ g, G = some g → g ∈ T) := by
  have key : ∀ (r : Round) (f : Spec.RoundGrades V), f ∈ [c.current, c.next] →
      FrameClaim r f (fun _ _ G => ∀ g, G = some g → g ∈ T) := by
    intro r f hf p G hG g hg
    subst hg
    have hmem : res f p ∈ [f.g0, f.g1, f.g2] := by
      cases p <;> simp [res, Spec.Protocol.phaseResult,
        Spec.Protocol.Phase.toSpec]
    exact h f hf (res f p) hmem g hG
  exact ⟨key _ _ (by simp), key _ _ (by simp)⟩

/-- An outcome of the cache update `onPhaseTick` at `t` from a node state whose saved grades hold
    blocks of its tree holds blocks of that tree. -/
theorem contractInTree_onPhaseTick (E : Env V) (hc : Protocol.HealConfig)
    (n : (Model.specDraft (V := V)).N) (t : Time) (c : (Model.specDraft (V := V)).Cache)
    (hcon : Spec.Store.ContractInTree n.val.st.T n.val.st.saved_grades)
    (h : (Model.specDraft (V := V)).onPhaseTick E hc n.st.core.toHealing t n.cache ⇢ c) :
    Spec.Store.ContractInTree n.val.st.T c := by
  obtain ⟨S', hS', rfl, -⟩ := GradesFacts.sd_onPhaseTick_ok h
  have hok : StoreOk n.val.st := n.property
  have hS'' : Spec.Protocol.update_grades
      (Spec.Config.toSpec E hc unreadHeightConfig) (Spec.Provisional.toSpec E)
      n.val.st t = .ok S' := hS'
  exact contractInTree_of_claim (memClaim_update_grades hok hS'' (claim_of_contractInTree hcon))

end SpecDraftRecord.ReachedReads

namespace DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

open SpecDraftRecord
open DecoupledConsensusModel.Execution
open scoped DC

/-- The field `store_with_cache_core_sg_votes` of `NodeFacts` at `Model.specDraft`: writing saved
    grades keeps the core store's `sg_votes`. -/
theorem _root_.SpecDraftRecord.NodeFacts.specDraft_store_with_cache_core_sg_votes :
    ∀ (st : (Model.specDraft (V := V)).NS) (c : (Model.specDraft (V := V)).Cache),
      ((Model.specDraft (V := V)).store_with_cache st c).core.sg_votes = st.core.sg_votes := by
  intro st c
  rfl

/-- The field `store_with_cache_core_sg_pool` of `NodeFacts` at `Model.specDraft`: writing saved
    grades keeps the core store's attestation sets. -/
theorem _root_.SpecDraftRecord.NodeFacts.specDraft_store_with_cache_core_sg_pool :
    ∀ (st : (Model.specDraft (V := V)).NS) (c : (Model.specDraft (V := V)).Cache),
      (Model.specDraft (V := V)).store_sg_pool ((Model.specDraft (V := V)).store_with_cache st c).core = (Model.specDraft (V := V)).store_sg_pool st.core := by
  intro st c
  rfl

/-- The field `store_with_cache_core_tau` of `NodeFacts` at `Model.specDraft`: writing saved grades
    keeps the core store's `tau`. -/
theorem _root_.SpecDraftRecord.NodeFacts.specDraft_store_with_cache_core_tau :
    ∀ (st : (Model.specDraft (V := V)).NS) (c : (Model.specDraft (V := V)).Cache),
      ((Model.specDraft (V := V)).store_with_cache st c).core.tau = st.core.tau := by
  intro st c
  rfl

/-- The field `store_with_cache_core_attestations` of `NodeFacts` at `Model.specDraft`: writing
    saved grades keeps the core store's attestations. -/
theorem _root_.SpecDraftRecord.NodeFacts.specDraft_store_with_cache_core_attestations :
    ∀ (st : (Model.specDraft (V := V)).NS) (c : (Model.specDraft (V := V)).Cache),
      (Model.specDraft (V := V)).store_attestations ((Model.specDraft (V := V)).store_with_cache st c).core = (Model.specDraft (V := V)).store_attestations st.core := by
  intro st c
  rfl

/-- The field `reachedNode_confirmationRead` of `NodeFacts` at `Model.specDraft`: if a run reaches
    `n` and `c` is an outcome of the cache update at `t` from `n`, a run reaches the node state with
    `n`'s store with its clock set to `t`, `n`'s signing record and the cache `c`. -/
theorem _root_.SpecDraftRecord.NodeFacts.specDraft_reachedNode_confirmationRead :
    ∀ (E : DecoupledConsensusModel.Env V)
      (hc : DecoupledConsensusModel.Protocol.HealConfig) (n : (Model.specDraft (V := V)).N) (t : DecoupledConsensusModel.Time)
      (c : (Model.specDraft (V := V)).Cache),
      (Model.specDraft (V := V)).onPhaseTick E hc n.st.core.toHealing t n.cache ⇢ c → (Model.specDraft (V := V)).reachedNode n →
      (Model.specDraft (V := V)).reachedNode ((Model.specDraft (V := V)).mkNode ((Model.specDraft (V := V)).ns_setClock E n.st t) n.record c) := by
  intro E hc n t c h₁ h₂
  obtain ⟨hinv, hconf, hcontract⟩ := reached_elim h₂
  exact ⟨hinv, hconf, ReachedReads.contractInTree_onPhaseTick E hc n t c hcontract h₁⟩

/-- The field `reachedNode_confirmationDuty` of `NodeFacts` at `Model.specDraft`: if a run reaches
    `n`, `c` is an outcome of the cache update at `t` from `n`, and `st` an outcome of the
    confirmation duty with `c`'s grade contract on `n`'s store with its clock set to `t`, a run
    reaches the node state with the store `st`, `n`'s signing record and the cache `c`. -/
theorem _root_.SpecDraftRecord.NodeFacts.specDraft_reachedNode_confirmationDuty :
    ∀ (E : DecoupledConsensusModel.Env V)
      (hc : DecoupledConsensusModel.Protocol.HealConfig) (n : (Model.specDraft (V := V)).N) (t : DecoupledConsensusModel.Time)
      (c : (Model.specDraft (V := V)).Cache) (st : (Model.specDraft (V := V)).NS),
      (Model.specDraft (V := V)).onPhaseTick E hc n.st.core.toHealing t n.cache ⇢ c →
      (Model.specDraft (V := V)).duties_update_confirmation_with ((Model.specDraft (V := V)).gradeContract c) E hc ((Model.specDraft (V := V)).ns_setClock E n.st t)
        (E.slotOf t - 1) ⇢ st →
      (Model.specDraft (V := V)).reachedNode n → (Model.specDraft (V := V)).reachedNode ((Model.specDraft (V := V)).mkNode st n.record c) := by
  intro E hc n t c st h₁ h₂ h₃
  obtain ⟨hinv, hconf, hcontract⟩ := reached_elim h₃
  have hok : SpecDraftRecord.NoRaise.StoreOk n.val.st := n.property
  have hofI : Spec.Store.ofImage (Member.ns_setClock E n.val.st t) =
      Member.ns_setClock E n.val.st t :=
    Spec.Store.ofImage_eq_self _ hok.2.1 hok.2.2.2 hinv.1 hconf.1 hconf.2.1 hconf.2.2
  have hst' : Returns (Member.duties_update_confirmation_with c E hc
      (Member.ns_setClock E n.val.st t) (E.slotOf t - 1)) st.val := h₂
  unfold Member.duties_update_confirmation_with at hst'
  rw [returns_successOutcomes, hofI] at hst'
  generalize hY : ({ Member.ns_setClock E n.val.st t with saved_grades := _ } :
    Spec.Store V) = Y at hst'
  cases hu : Spec.Protocol.update_confirmation
      (Spec.Config.toSpec E hc unreadHeightConfig) Y (E.slotOf t - 1) with
  | error e => rw [hu] at hst'; cases hst'
  | ok out =>
    rw [hu] at hst'
    have hout : { out with saved_grades := c } = st.val := Except.ok.inj hst'
    have hYF : Y.F ∈ Y.T := by rw [← hY]; exact hok.2.2.2
    have hYJ : Y.J ∈ Y.T := by rw [← hY]; exact hinv.1
    have hYc : Y.latest_confirmed ∈ Y.T := by rw [← hY]; exact hconf.2.1
    have hYs : Y.latest_stable ∈ Y.T := by rw [← hY]; exact hconf.2.2
    obtain ⟨m1, m2, m3⟩ := SpecDraftRecord.NodeFacts.update_confirmation_mem hYF hYJ hYc hYs hu
    have hwo := SpecDraftRecord.NoRaise.update_confirmation_writes_only_confirmation hu
    generalize out.live_confirmed = a at hwo m1
    generalize out.latest_stable = b at hwo m3
    generalize out.latest_confirmed = d at hwo m2
    subst hwo
    subst hY
    show SubtypeEqualities.RunStoreInv { st.val with saved_grades := c } ∧
      HandlersRunFacts.ConfirmedInTree { st.val with saved_grades := c } ∧
      Spec.Store.ContractInTree st.val.T c
    rw [← hout]
    exact ⟨hinv, ⟨m1, m2, m3⟩, ReachedReads.contractInTree_onPhaseTick E hc n t c hcontract h₁⟩

end DecoupledConsensusModel.Sts.Record

namespace DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

open SpecDraftRecord
open DecoupledConsensusModel.Execution
open scoped DC

/-- The field `runs_as_wake` of `NodeFacts` at `Model.specDraft`: if `n` runs as `v`, so does
    `M.wake n`. -/
theorem _root_.SpecDraftRecord.NodeFacts.specDraft_runs_as_wake :
    ∀ (n : (Model.specDraft (V := V)).N) (v : V), (Model.specDraft (V := V)).runs_as n v → (Model.specDraft (V := V)).runs_as ((Model.specDraft (V := V)).wake n) v := by
  intro n v h₁
  exact h₁

end DecoupledConsensusModel.Sts.Record
