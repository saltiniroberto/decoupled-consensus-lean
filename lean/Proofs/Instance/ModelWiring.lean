import Proofs.Instance.Model
import Proofs.Instance.Wiring
import Model.Record.Wiring

/-!
# The record's wiring at the spec's model is the spec's protocol

The record's wired protocol `protocolOf M S` at `Model.specDraftBase` and at `Model.specDraft` has
the initial node states and the steps of the spec's protocol `Spec.Sts.protocol` at the setup
`Setup.toSpec S`.
-/

set_option autoImplicit false

namespace SpecDraftRecord

open Framework.StsMultisetLog
open DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-- The reactions the record's wiring allows at `Model.specDraftBase` are either the one reaction
    `reactionOnVocabularyObjects S n t e`, or none; when there are none, that reaction keeps `n` and
    sends nothing. -/
theorem reactionsOf_specDraftBase (S : DecoupledConsensusModel.Execution.Setup V) (p : V)
    (n : Spec.NodeState V) (t : Int)
    (e : Event V (DecoupledConsensusModel.Execution.NamedObject V) Empty) :
    reactionsOf (Model.specDraftBase (V := V)) S p n t e = {reactionOnVocabularyObjects S n t e} ∨
      (reactionsOf (Model.specDraftBase (V := V)) S p n t e = ∅ ∧
        reactionOnVocabularyObjects S n t e = { state := n, send := 0 }) := by
  cases e with
  | tick =>
    by_cases hΔ : t % S.E.Δ = 0
    · have hΔ' : t % (Setup.toSpec S).C.Δ = 0 := hΔ
      cases htick : (Spec.tick (Setup.toSpec S).C (Setup.toSpec S).P
          (Setup.toSpec S).X n t).run [] with
      | ok out =>
        left
        have hR : reactionOnVocabularyObjects S n t .tick =
            { state := out.1,
              send := ((out.2.map Spec.NamedObject.toProof :
                List (DecoupledConsensusModel.Execution.NamedObject V)) :
                  Multiset (DecoupledConsensusModel.Execution.NamedObject V)) } := by
          simp only [reactionOnVocabularyObjects, Event.toSpec, Spec.Sts.reaction, if_pos hΔ',
            htick, NodeStepResult.toProof, Multiset.map_coe]
        rw [hR]
        ext res
        simp only [reactionsOf, if_pos hΔ, Set.mem_setOf_eq]
        show (∃ o, successOutcomes (((Spec.tick (Setup.toSpec S).C (Setup.toSpec S).P
          (Setup.toSpec S).X n t).run []).map
            fun out => (out.1, out.2.map Spec.NamedObject.toProof)) ⇢ o ∧ _) ↔ _
        simp only [returns_successOutcomes, htick]
        constructor
        · rintro ⟨o, ho, hres⟩
          cases ho
          exact hres
        · intro hres
          exact ⟨_, rfl, hres⟩
      | error err =>
        right
        refine ⟨?_, ?_⟩
        · ext res
          simp only [reactionsOf, if_pos hΔ, Set.mem_setOf_eq, Set.mem_empty_iff_false,
            iff_false]
          show ¬ (∃ o, successOutcomes (((Spec.tick (Setup.toSpec S).C
            (Setup.toSpec S).P (Setup.toSpec S).X n t).run []).map
              fun out => (out.1, out.2.map Spec.NamedObject.toProof)) ⇢ o ∧ _)
          simp only [returns_successOutcomes, htick]
          rintro ⟨o, ho, -⟩
          cases ho
        · simp only [reactionOnVocabularyObjects, Event.toSpec, Spec.Sts.reaction, if_pos hΔ',
            htick, NodeStepResult.toProof, Multiset.map_zero]
    · left
      have hΔ' : ¬ t % (Setup.toSpec S).C.Δ = 0 := hΔ
      simp only [reactionsOf, if_neg hΔ, reactionOnVocabularyObjects, Event.toSpec,
        Spec.Sts.reaction, if_neg hΔ', NodeStepResult.toProof, Multiset.map_zero]
      rfl
  | recv m =>
    left
    rw [reactionOnVocabularyObjects_recv]
    ext res
    simp only [reactionsOf, Set.mem_setOf_eq]
    show (∃ n', pure (receiveNamedObject (DecoupledConsensusModel.Sts.Setup.alwaysAwake S) n m.msg)
      ⇢ n' ∧ _) ↔ _
    simp only [returns_pure]
    constructor
    · rintro ⟨n', hn', hres⟩
      rw [hres, hn']
      rfl
    · intro hres
      exact ⟨_, rfl, hres⟩
  | wake =>
    left
    rw [reactionOnVocabularyObjects_wake]
    rfl
  | custom ev => exact ev.elim

/-- The record's wired protocol at `Model.specDraftBase` starts every validator where the spec's
    protocol at `Setup.toSpec S` starts it. -/
theorem protocolOf_specDraftBase_init (S : DecoupledConsensusModel.Execution.Setup V) (v : V) :
    (protocolOf (Model.specDraftBase (V := V)) S).init v =
      (Spec.Sts.protocol (Setup.toSpec S)).init v := rfl

/-- A step of the record's wired protocol at `Model.specDraftBase` holds exactly when the step of
    the spec's protocol at `Setup.toSpec S` holds at the spec's counterparts of the view, the event
    and the result. -/
theorem protocolOf_specDraftBase_step_iff (S : DecoupledConsensusModel.Execution.Setup V) (p : V)
    (r : Nat) (view : View V (DecoupledConsensusModel.Execution.NamedObject V))
    (n : Spec.NodeState V)
    (e : Event V (DecoupledConsensusModel.Execution.NamedObject V) Empty)
    (res : NodeStepResult (Spec.NodeState V)
      (DecoupledConsensusModel.Execution.NamedObject V)) :
    (protocolOf (Model.specDraftBase (V := V)) S).step p r view n e res ↔
      (Spec.Sts.protocol (Setup.toSpec S)).step p r (View.toSpec view) n
        (Event.toSpec e) (NodeStepResult.toSpec res) := by
  rw [← protocolOnVocabularyObjects_step_iff]
  change _ ↔ res = reactionOnVocabularyObjects S n (r : Int) e
  rcases reactionsOf_specDraftBase S p n (r : Int) e with h | ⟨h, hR⟩
  · constructor
    · rintro (hres | ⟨hempty, -⟩)
      · exact Set.mem_singleton_iff.mp ((Set.ext_iff.mp h res).mp hres)
      · exact absurd (h.symm.trans hempty) (Set.singleton_ne_empty _)
    · intro hres
      exact Or.inl ((Set.ext_iff.mp h res).mpr (Set.mem_singleton_iff.mpr hres))
  · constructor
    · rintro (hres | ⟨-, hres⟩)
      · exact absurd ((Set.ext_iff.mp h res).mp hres) (Set.notMem_empty _)
      · rw [hR]
        exact hres
    · intro hres
      rw [hR] at hres
      exact Or.inr ⟨h, hres⟩

/-! ## At `Model.specDraft`, over the node subtype -/

/-- A result over the node subtype `OkNode V` as a result over the spec's node states: the node
    state's value, the same objects sent. -/
def NodeStepResult.val {O : Type} (res : NodeStepResult (OkNode V) O) : NodeStepResult (Spec.NodeState V) O :=
  { state := res.state.val, send := res.send }

omit [DecidableEq V] [Fintype V] [Inhabited V] in
/-- Two results over the node subtype are equal when their values are. -/
theorem NodeStepResult.val_injective {O : Type} {res res' : NodeStepResult (OkNode V) O}
    (h : NodeStepResult.val res = NodeStepResult.val res') : res = res' := by
  cases res
  cases res'
  simp only [NodeStepResult.val, NodeStepResult.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  rw [Subtype.ext h1, h2]

/-- The reactions at `Model.specDraft` from `n` are the results whose values are reactions at
    `Model.specDraftBase` from `n.val`. -/
theorem reactionsOf_specDraft_eq (S : DecoupledConsensusModel.Execution.Setup V) (p : V)
    (n : OkNode V) (t : Int)
    (e : Event V (DecoupledConsensusModel.Execution.NamedObject V) Empty) :
    reactionsOf (Model.specDraft (V := V)) S p n t e =
      {res | NodeStepResult.val res ∈ reactionsOf (Model.specDraftBase (V := V)) S p n.val t e} := by
  ext res
  cases e with
  | tick =>
    by_cases hΔ : t % S.E.Δ = 0
    · simp only [reactionsOf, if_pos hΔ, Set.mem_setOf_eq]
      constructor
      · rintro ⟨out, hout, rfl⟩
        exact ⟨(out.1.val, out.2), hout, rfl⟩
      · rintro ⟨out, hout, hres⟩
        refine ⟨(res.state, out.2), ?_, ?_⟩
        · have h1 : res.state.val = out.1 := congrArg NodeStepResult.state hres
          have hout' : Prod.map Subtype.val id (res.state, out.2) = out := Prod.ext h1 rfl
          change Returns (preimageOutcomes (Prod.map Subtype.val id) _) (res.state, out.2)
          rw [returns_preimageOutcomes, hout']
          exact hout
        · have h1 : res.state.val = out.1 := congrArg NodeStepResult.state hres
          apply NodeStepResult.val_injective
          rw [hres, ← h1]
          rfl
    · simp only [reactionsOf, if_neg hΔ, Set.mem_singleton_iff]
      constructor
      · rintro rfl
        rfl
      · intro h
        exact NodeStepResult.val_injective h
  | recv m =>
    simp only [reactionsOf, Set.mem_setOf_eq]
    constructor
    · rintro ⟨n', hn', rfl⟩
      exact ⟨n'.val, hn', rfl⟩
    · rintro ⟨n', hn', hres⟩
      refine ⟨res.state, ?_, ?_⟩
      · have h1 : res.state.val = n' := congrArg NodeStepResult.state hres
        change Returns (preimageOutcomes Subtype.val _) res.state
        rw [returns_preimageOutcomes, h1]
        exact hn'
      · have h1 : res.state.val = n' := congrArg NodeStepResult.state hres
        apply NodeStepResult.val_injective
        rw [hres, ← h1]
        rfl
  | wake =>
    simp only [reactionsOf, Set.mem_singleton_iff]
    constructor
    · rintro rfl
      rfl
    · intro h
      exact NodeStepResult.val_injective h
  | custom ev => exact ev.elim

/-- The reactions the record's wiring allows at `Model.specDraft` from `n` are the results whose
    value is `reactionOnVocabularyObjects S n.val t e`, or none; when there are none, that reaction
    keeps `n.val` and sends nothing. -/
theorem reactionsOf_specDraft (S : DecoupledConsensusModel.Execution.Setup V) (p : V)
    (n : OkNode V) (t : Int)
    (e : Event V (DecoupledConsensusModel.Execution.NamedObject V) Empty) :
    reactionsOf (Model.specDraft (V := V)) S p n t e =
        {res | NodeStepResult.val res = reactionOnVocabularyObjects S n.val t e} ∨
      (reactionsOf (Model.specDraft (V := V)) S p n t e = ∅ ∧
        reactionOnVocabularyObjects S n.val t e = { state := n.val, send := 0 }) := by
  rw [reactionsOf_specDraft_eq]
  rcases reactionsOf_specDraftBase S p n.val t e with h | ⟨h, hR⟩
  · left
    rw [h]
    rfl
  · right
    refine ⟨?_, hR⟩
    rw [h]
    rfl

/-- The record's wired protocol at `Model.specDraft` starts every validator at a node state whose
    value is where the spec's protocol at `Setup.toSpec S` starts it. -/
theorem protocolOf_specDraft_init (S : DecoupledConsensusModel.Execution.Setup V) (v : V) :
    ((protocolOf (Model.specDraft (V := V)) S).init v).val =
      (Spec.Sts.protocol (Setup.toSpec S)).init v := rfl

/-- When every step of the spec's node from `n.val` at this event leaves a store that meets
    `StoreOk`, a step of the record's wired protocol at `Model.specDraft` from `n` holds exactly
    when the step of the spec's protocol at `Setup.toSpec S` holds from `n.val` at the spec's
    counterparts of the view, the event and the result's value. -/
theorem protocolOf_specDraft_step_iff (S : DecoupledConsensusModel.Execution.Setup V) (p : V)
    (r : Nat) (view : View V (DecoupledConsensusModel.Execution.NamedObject V))
    (n : OkNode V)
    (e : Event V (DecoupledConsensusModel.Execution.NamedObject V) Empty)
    (res : NodeStepResult (OkNode V) (DecoupledConsensusModel.Execution.NamedObject V))
    -- every step of the spec's node from `n.val` at this event leaves a store that meets `StoreOk`
    (hok : ∀ res' : NodeStepResult (Spec.NodeState V) (Spec.NamedObject V),
      (Spec.Sts.protocol (Setup.toSpec S)).step p r (View.toSpec view) n.val (Event.toSpec e)
        res' → NoRaise.StoreOk res'.state.st) :
    (protocolOf (Model.specDraft (V := V)) S).step p r view n e res ↔
      (Spec.Sts.protocol (Setup.toSpec S)).step p r (View.toSpec view) n.val
        (Event.toSpec e) (NodeStepResult.toSpec (NodeStepResult.val res)) := by
  rw [← protocolOnVocabularyObjects_step_iff]
  change _ ↔ NodeStepResult.val res = reactionOnVocabularyObjects S n.val (r : Int) e
  have hR : NoRaise.StoreOk (reactionOnVocabularyObjects S n.val (r : Int) e).state.st :=
    hok (NodeStepResult.toSpec (reactionOnVocabularyObjects S n.val (r : Int) e))
      ((protocolOnVocabularyObjects_step_iff S p r view n.val e _).mp rfl)
  rcases reactionsOf_specDraft S p n (r : Int) e with h | ⟨h, hR'⟩
  · constructor
    · rintro (hres | ⟨hempty, -⟩)
      · rw [h] at hres
        exact hres
      · rw [h] at hempty
        have hmem : ({
              state := ⟨(reactionOnVocabularyObjects S n.val (r : Int) e).state, hR⟩
              send := (reactionOnVocabularyObjects S n.val (r : Int) e).send } :
              NodeStepResult (OkNode V) (DecoupledConsensusModel.Execution.NamedObject V)) ∈
            {res : NodeStepResult (OkNode V) (DecoupledConsensusModel.Execution.NamedObject V) |
              NodeStepResult.val res = reactionOnVocabularyObjects S n.val (r : Int) e} := rfl
        rw [hempty] at hmem
        exact absurd hmem (Set.notMem_empty _)
    · intro hres
      left
      rw [h]
      exact hres
  · constructor
    · rintro (hres | ⟨-, rfl⟩)
      · rw [h] at hres
        exact absurd hres (Set.notMem_empty _)
      · rw [hR']
        rfl
    · intro hres
      right
      refine ⟨h, NodeStepResult.val_injective ?_⟩
      rw [hres, hR']
      rfl

end SpecDraftRecord
