import Proofs.Instance.Facts.Duties
import Proofs.Instance.Facts.Node2
import Proofs.Instance.Facts.Grades

/-!
# Remaining fields of the duties and grades families

Proofs at `Model.spec` of fields of `DutiesFacts` and `GradesFacts` not proved elsewhere: the
two vote-insertion fields of the duties, the chain-state map after the confirmation update, and the
results of the phase tick.
-/

set_option autoImplicit false

namespace SpecRecord.DutiesFacts

open DecoupledConsensusModel DecoupledConsensusModel.Sts DecoupledConsensusModel.Sts.Record
open SpecRecord.ContractImages SpecRecord.NodeFacts
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

omit [Inhabited V] in
/-- Writing the saved grades satisfies `VIns`. -/
theorem vIns_with_saved_grades (P : Spec.Provisional V) (a : Spec.Store V)
    (x : Spec.SavedGrades V) : VIns P a { a with saved_grades := x } :=
  VIns.of_eq rfl rfl rfl rfl

omit [Inhabited V] in
/-- Reading the store through its tree and writing its saved grades satisfies `VIns`. -/
theorem vIns_ofImage_with (P : Spec.Provisional V) (a : Spec.Store V)
    (x : Spec.SavedGrades V) :
    VIns P a { Spec.Store.ofImage a with saved_grades := x } :=
  VIns.of_eq rfl rfl rfl rfl

omit [Inhabited V] in
/-- The spec's Goldfish vote duty satisfies `VIns`: it returns the store, or the store after the
    checked admission of the vote it makes. -/
theorem goldfish_vote_vIns {C : Spec.Config} {P : Spec.Provisional V} {v : V}
    {st : Spec.Store V} {l : List (Spec.NamedObject V)}
    {out : Spec.Store V × List (Spec.NamedObject V)}
    (h : (Spec.Protocol.goldfish_vote C P v st).run l = .ok out) :
    VIns P st out.1 := by
  unfold Spec.Protocol.goldfish_vote at h
  dsimp only at h
  rw [NoRaise.DREB.run_bind_ok_iff] at h
  obtain ⟨_, _, -, h⟩ := h
  rw [NoRaise.DREB.run_bind_ok_iff] at h
  obtain ⟨_, _, -, h⟩ := h
  rw [NoRaise.DREB.run_bind_ok_iff] at h
  obtain ⟨_, _, -, h⟩ := h
  rw [NoRaise.DREB.run_bind_ok_iff] at h
  obtain ⟨H, _, -, h⟩ := h
  split_ifs at h
  · rw [NoRaise.DREB.run_bind_ok_iff] at h
    obtain ⟨_, _, -, h⟩ := h
    rw [NoRaise.DREB.pure_run_ok_iff] at h
    subst h
    exact vIns_checked _ _ _
  · rw [NoRaise.DREB.pure_run_ok_iff] at h
    subst h
    exact VIns.of_eq rfl rfl rfl rfl

omit [Inhabited V] in
/-- The store of an outcome of the Goldfish vote duty member satisfies `VIns` from the store it is
    given. -/
theorem duties_goldfish_vote_with_vIns {c : Spec.SavedGrades V} {E : Env V}
    {hc : Protocol.HealConfig} {nd : Protocol.Node V} {st : Spec.Store V}
    {D : Spec.Store V × Option (GoldfishVote V)}
    (h : Returns (Member.duties_goldfish_vote_with c E hc nd st) D) :
    VIns (Spec.Provisional.toSpec E) st D.1 := by
  unfold Member.duties_goldfish_vote_with at h
  rw [returns_successOutcomes] at h
  obtain ⟨out, hout, e⟩ := except_map_eq_ok h
  rw [← e]
  exact (vIns_ofImage_with _ st _).trans
    ((goldfish_vote_vIns hout).trans (vIns_with_saved_grades _ _ c))

/-- The store of an outcome of the proposal duty member satisfies `VIns` from the store it is given. -/
theorem duties_propose_block_with_vIns {c : Spec.SavedGrades V} {E : Env V}
    {hc : Protocol.HealConfig} {cfg : Protocol.HeightConfig} {nd : Protocol.Node V}
    {st : Spec.Store V} {D : Spec.Store V × Option (NamedBlock V)}
    (h : Returns (Member.duties_propose_block_with c E hc cfg nd st) D) :
    VIns (Spec.Provisional.toSpec E) st D.1 := by
  obtain ⟨B, -, rfl⟩ := duties_propose_block_with_shape h
  exact (vIns_ofImage_with _ st _).trans
    ((vIns_on_block _ _ _ B).trans (vIns_with_saved_grades _ _ c))

/-- `VIns` from a store of the subtype to another gives the record's `InsertsAt` at any clock
    reading `c`. -/
theorem insertsAt_of_vIns (E : Env V) (c : Int) {a b : (Model.spec (V := V)).S}
    (hv : VIns (Spec.Provisional.toSpec E) a.val b.val) :
    Restated.InsertsAt (Model.spec (V := V)) E c a b := by
  have hp := poolStep_of_vIns (a := a) (b := b) hv
  intro hps hc
  obtain ⟨hcar, hsta⟩ := hp.1 hps
  refine ⟨hcar, hsta, ?_, hv.2.1, fun u hu hu' => ?_⟩
  · show b.val.t = _
    rw [hv.1]; exact hc
  · obtain ⟨e, hs, hcm⟩ := hp.2 hps u hu hu'
    refine ⟨?_, hs, ?_⟩
    · rw [e, ← hc]
    · simpa [Spec.Provisional.toSpec_committee] using hcm

/-- The field `insertsAt_named_propose` of `DutiesFacts` at `Model.spec`: for every outcome `D`
    of the proposal duty on `st`, the arrow `InsertsAt` at `c` runs from the core store of `st` to
    the core store of `D`'s named store. -/
theorem spec_insertsAt_named_propose :
    ∀ (E : Env V) (c : Int) (contract : (Model.spec (V := V)).Contract) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) (nd : Protocol.Node V) (st : (Model.spec (V := V)).NS)
    (D : (Model.spec (V := V)).NS × Option (NamedBlock V)), (Model.spec (V := V)).duties_propose_block_with contract E hc cfg nd st ⇢ D →
    Restated.InsertsAt (Model.spec (V := V)) E c st.core D.1.core := by
  intro E c contract hc cfg nd st D hD
  exact insertsAt_of_vIns E c
    (duties_propose_block_with_vIns ((returns_preimageOutcomes _ _ _).1 hD))

/-- The field `insertsAt_named_vote` of `DutiesFacts` at `Model.spec`: for every outcome `D` of
    the Goldfish vote duty on `st`, the arrow `InsertsAt` at `c` runs from the core store of `st` to
    the core store of `D`'s named store. -/
theorem spec_insertsAt_named_vote :
    ∀ (E : Env V) (c : Int) (contract : (Model.spec (V := V)).Contract) (hc : Protocol.HealConfig)
    (nd : Protocol.Node V) (st : (Model.spec (V := V)).NS)
    (D : (Model.spec (V := V)).NS × Option (GoldfishVote V)), (Model.spec (V := V)).duties_goldfish_vote_with contract E hc nd st ⇢ D →
    Restated.InsertsAt (Model.spec (V := V)) E c st.core D.1.core := by
  intro E c contract hc nd st D hD
  exact insertsAt_of_vIns E c
    (duties_goldfish_vote_with_vIns ((returns_preimageOutcomes _ _ _).1 hD))

/-- The field `update_confirmation_with_σ` of `DutiesFacts` at `Model.spec`: every outcome of
    the confirmation update has the chain-state map `σ` of the store it was given. -/
theorem spec_update_confirmation_with_σ : ∀ (contract : (Model.spec (V := V)).Contract) (E : Env V) (hc : Protocol.HealConfig) (st : (Model.spec (V := V)).S) (s : Slot) (st' : (Model.spec (V := V)).S), (Model.spec (V := V)).update_confirmation_with contract E hc st s ⇢ st' → st'.σ = st.σ := by
  intro contract E hc st s st' h
  obtain ⟨x1, x2, x3, he⟩ :=
    update_confirmation_with_shape ((returns_preimageOutcomes _ _ _).1 h)
  obtain ⟨v, hv⟩ := st'
  dsimp only at he
  subst he
  rfl

end SpecRecord.DutiesFacts

/-! ## The phase tick's results -/

namespace SpecRecord.RemainingKit

open Spec
open DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]

/-- What the spec's `update_grades` at `t` writes, result by result: with `A` the saved grades
    brought to the round of `t`, each result is `A`'s, or was pending in `A`, is due at `t`, and is
    computed by `graded_block`; then all are clipped against the store's finalized block. -/
theorem update_grades_value {C : Config} {P : Provisional V} {st st' : Store V} {t : Time}
    (h : Protocol.update_grades C P st t = .ok st') {ρ : Round} (hρ : C.round_of (C.slotOf t) = ρ)
    {A : SavedGrades V} (hA : Protocol.advance_to_round st.saved_grades ρ = A) :
    ∃ X : SavedGrades V,
      st'.saved_grades = Protocol.make_saved_grades_compatible_with st.F X ∧ X.round = A.round ∧
      X.current.g2 = A.current.g2 ∧ X.next.g0 = A.next.g0 ∧ X.next.g1 = A.next.g1 ∧
      ((X.current.g0 = A.current.g0 ∧ ¬ (t = C.opening ρ + C.Δ ∧ A.current.g0 = .pending)) ∨
        (A.current.g0 = .pending ∧ t = C.opening ρ + C.Δ ∧ ∃ sg G,
          Protocol.graded_block C P { st with saved_grades := sg } ρ (C.opening ρ - 3 * C.Δ)
            (C.opening ρ - 3 * C.Δ) = .ok G ∧ X.current.g0 = .computed G)) ∧
      ((X.current.g1 = A.current.g1 ∧ ¬ (t = C.opening ρ ∧ A.current.g1 = .pending)) ∨
        (A.current.g1 = .pending ∧ t = C.opening ρ ∧ ∃ sg G,
          Protocol.graded_block C P { st with saved_grades := sg } ρ (C.opening ρ - 4 * C.Δ)
            (C.opening ρ - 2 * C.Δ) = .ok G ∧ X.current.g1 = .computed G)) ∧
      ((X.next.g2 = A.next.g2 ∧ ¬ (t = C.opening (ρ + 1) - C.Δ ∧ A.next.g2 = .pending)) ∨
        (A.next.g2 = .pending ∧ t = C.opening (ρ + 1) - C.Δ ∧ ∃ sg G,
          Protocol.graded_block C P { st with saved_grades := sg } (ρ + 1)
            (C.opening (ρ + 1) - 5 * C.Δ) (C.opening (ρ + 1) - C.Δ) = .ok G ∧
            X.next.g2 = .computed G)) := by
  subst hρ hA
  simp only [Protocol.update_grades] at h
  repeat' (first
    | (split_ifs at h)
    | (obtain ⟨_, _, h⟩ := NoRaise.DRE.ok_of_bind h; try dsimp only at h))
  all_goals
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp only [Bool.and_eq_true, decide_eq_true_eq, not_and] at *
    refine ⟨_, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩ <;>
      first
        | exact Or.inl ⟨rfl, by tauto⟩
        | exact Or.inr ⟨by tauto, by tauto, _, _, by with_reducible assumption, rfl⟩

/-- The record's cutoffs and computation times at the spec's configuration, phase by phase: round
    `r`'s grade-0 cutoffs are both three delays before it opens and it is computed one delay after;
    the grade-1 cutoffs are four and two delays before, computed as it opens; the grade-2 cutoffs
    are five delays and one delay before, computed one delay before. -/
theorem cutoffs [Inhabited V] (E : DecoupledConsensusModel.Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig) (r : Round) :
    let C := Config.toSpec E hc unreadHeightConfig
    (Member.early E hc r .g0 = C.opening r - 3 * C.Δ ∧ Member.late E hc r .g0 = C.opening r - 3 * C.Δ ∧
      Member.domain E hc r .g0 = C.opening r + C.Δ) ∧
    (Member.early E hc r .g1 = C.opening r - 4 * C.Δ ∧ Member.late E hc r .g1 = C.opening r - 2 * C.Δ ∧
      Member.domain E hc r .g1 = C.opening r) ∧
    (Member.early E hc r .g2 = C.opening r - 5 * C.Δ ∧ Member.late E hc r .g2 = C.opening r - C.Δ ∧
      Member.domain E hc r .g2 = C.opening r - C.Δ) := by
  simp only [Member.early, Member.late, Member.domain, Member.lateOffset, Member.domainOffset,
    Config.early, Protocol.Phase.earlyOffset, Protocol.Phase.toSpec]
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩ <;> simp <;> ring

/-- The result of round `r` and phase `p` after the spec's grades update at `t` is the result of the
    saved grades brought to `t`'s round, clipped at `st.F`; or that result was pending, `t` is
    `Member.domain E hc r p`, and it is `graded_block` with the cutoffs `Member.early E hc r p` and
    `Member.late E hc r p`, clipped at `st.F`. -/
theorem tick_slot [Inhabited V] {E : DecoupledConsensusModel.Env V}
    {hc : DecoupledConsensusModel.Protocol.HealConfig} {st : Store V} {c : SavedGrades V}
    {t : Time} {S : Store V}
    (hS : Protocol.update_grades (Config.toSpec E hc unreadHeightConfig) (Provisional.toSpec E)
      { st with saved_grades := c } t = .ok S)
    (r : Round) (p : DecoupledConsensusModel.Protocol.Phase) :
    let C := Config.toSpec E hc unreadHeightConfig
    let A := Protocol.advance_to_round c (C.round_of (C.slotOf t))
    Protocol.phaseResult (Protocol.saved_round_grades S.saved_grades r) (Protocol.Phase.toSpec p) =
        Protocol.make_result_compatible_with st.F
          (Protocol.phaseResult (Protocol.saved_round_grades A r) (Protocol.Phase.toSpec p)) ∨
      (Protocol.phaseResult (Protocol.saved_round_grades A r) (Protocol.Phase.toSpec p) = .pending ∧
        t = Member.domain E hc r p ∧ ∃ sg G,
          Protocol.graded_block C (Provisional.toSpec E) { st with saved_grades := sg } r
            (Member.early E hc r p) (Member.late E hc r p) = .ok G ∧
          Protocol.phaseResult (Protocol.saved_round_grades S.saved_grades r) (Protocol.Phase.toSpec p) =
            Protocol.make_result_compatible_with st.F (.computed G)) := by
  intro C A
  obtain ⟨X, hX, hr, h2, n0, n1, k0, k1, k2⟩ := update_grades_value hS rfl (rfl : _ = A)
  have hAr : A.round = C.round_of (C.slotOf t) := NoRaise.advance_to_round_round _ _
  obtain ⟨⟨e0, l0, d0⟩, ⟨e1, l1, d1⟩, ⟨e2, l2, d2⟩⟩ := cutoffs E hc r
  rw [hX]
  unfold Protocol.saved_round_grades
  simp only [Protocol.make_saved_grades_compatible_with, hr]
  split_ifs with q1 q2
  · rw [q1, hAr] at e0 l0 d0 e1 l1 d1 ⊢
    rcases p with _ | _ | _ <;>
      simp only [Protocol.phaseResult, Protocol.Phase.toSpec, Protocol.make_round_grades_compatible_with,
        reduceCtorEq, if_true, if_false]
    · rcases k0 with ⟨e, -⟩ | ⟨hp, ht, sg, G, hG, e⟩
      · exact Or.inl (by rw [e])
      · exact Or.inr ⟨hp, by rw [d0]; exact ht, sg, G, by rw [e0, l0]; exact hG, by rw [e]⟩
    · rcases k1 with ⟨e, -⟩ | ⟨hp, ht, sg, G, hG, e⟩
      · exact Or.inl (by rw [e])
      · exact Or.inr ⟨hp, by rw [d1]; exact ht, sg, G, by rw [e1, l1]; exact hG, by rw [e]⟩
    · exact Or.inl (by rw [h2])
  · rw [q2, hAr] at e2 l2 d2 ⊢
    rcases p with _ | _ | _ <;>
      simp only [Protocol.phaseResult, Protocol.Phase.toSpec, Protocol.make_round_grades_compatible_with,
        reduceCtorEq, if_true, if_false]
    · exact Or.inl (by rw [n0])
    · exact Or.inl (by rw [n1])
    · rcases k2 with ⟨e, -⟩ | ⟨hp, ht, sg, G, hG, e⟩
      · exact Or.inl (by rw [e])
      · exact Or.inr ⟨hp, by rw [d2]; exact ht, sg, G, by rw [e2, l2]; exact hG, by rw [e]⟩
  · exact Or.inl (by rcases p with _ | _ | _ <;> rfl)

omit [DecidableEq V] [Fintype V] in
/-- A result of the saved grades brought to round `ρ` that is not pending is the result the saved
    grades held for that round and phase. -/
theorem srg_advance_value {c : SavedGrades V} {ρ r : Round} {q : Protocol.Phase}
    (h : Protocol.phaseResult (Protocol.saved_round_grades (Protocol.advance_to_round c ρ) r) q ≠
      .pending) :
    Protocol.phaseResult (Protocol.saved_round_grades (Protocol.advance_to_round c ρ) r) q =
      Protocol.phaseResult (Protocol.saved_round_grades c r) q := by
  simp only [Protocol.advance_to_round, Protocol.saved_round_grades] at h ⊢
  split_ifs at h ⊢ <;> (try simp only at *) <;>
    first
      | rfl
      | (exfalso; (try simp only [Spec.Round] at *); omega)
      | (exfalso; apply h; cases q <;> rfl)

omit [Fintype V] in
/-- The spec's clip of `g` (`GradesLocal.clipBlock g F`) is `g` or an ancestor of `g`. -/
theorem clipBlock_ancestorEq (g F : Block V) :
    (GradesLocal.clipBlock g F).ancestorEq g = true := by
  induction g with
  | genesis => simp [GradesLocal.clipBlock, Block.ancestorEq]
  | node p s r gv gsv ats v ih =>
    simp only [GradesLocal.clipBlock]
    split_ifs
    · simp [Block.ancestorEq]
    · simp [Block.ancestorEq, ih]

omit [Fintype V] in
/-- The image of the spec's clip of `x` against `F` is the image of `x` or an ancestor of it. -/
theorem preceq_dca (x F : Block V) :
    DecoupledConsensusModel.Block.Preceq (Protocol.deepest_compatible_ancestor x F).toProof
      x.toProof := by
  rw [GradesLocal.deepest_compatible_ancestor_eq]
  unfold DecoupledConsensusModel.Block.Preceq
  exact Block.toProof_preceq_of_ancestorEq _ _ (clipBlock_ancestorEq x F)

/-- The answer of the spec's `graded_block` on a store of the instance with any saved grades is,
    mapped, an outcome of the member `freezeRoot` at the store's grade view, finalized block and
    `η_SG`. -/
theorem freezeRoot_of_graded_block [Inhabited V] {E : DecoupledConsensusModel.Env V}
    {hc : DecoupledConsensusModel.Protocol.HealConfig} {st : (Model.spec (V := V)).HS}
    {sg : SavedGrades V}
    {r : Round} {t0 t1 : Time} {G : Option (Block V)}
    (h : Protocol.graded_block (Config.toSpec E hc unreadHeightConfig) (Provisional.toSpec E)
      { st.val with saved_grades := sg } r t0 t1 = .ok G) :
    (Model.spec (V := V)).freezeRoot E ((Model.spec (V := V)).gradeView st)
      st.toFG.F hc.η_SG r t0 t1 ⇢ G.map Block.toProof := by
  have hF : st.val.blockOfImage st.val.F.toProof = st.val.F :=
    Store.blockOfImage_toProof_of_injOn _ st.property.2.1.injOn_toProof st.property.2.2.2
  show DecoupledConsensusModel.Sts.Record.Returns (successOutcomes (Except.map
    (Option.map Block.toProof) (Protocol.freezeRoot (Provisional.toSpec E) (Member.gradeView st.val)
      (st.val.blockOfImage st.val.F.toProof) hc.η_SG r t0 t1))) _
  rw [returns_successOutcomes, hF]
  have e : Protocol.freezeRoot (Provisional.toSpec E) (Member.gradeView st.val) st.val.F hc.η_SG r
      t0 t1 = Protocol.graded_block (Config.toSpec E hc unreadHeightConfig) (Provisional.toSpec E)
        { st.val with saved_grades := sg } r t0 t1 := rfl
  rw [e, h]
  rfl

omit [Fintype V] in
/-- The spec's clip of a computed result holding the block `x`, mapped, holds the image of the clip
    of `x`. -/
theorem toProof_mrcw_some (F x : Block V) :
    (Protocol.make_result_compatible_with F (.computed (some x))).toProof =
      some (some (Protocol.deepest_compatible_ancestor x F).toProof) := rfl

/-- A time from the opening of round `r` to less than one slot later is in round `r`. -/
theorem round_of_opening_add (C : Config) (r : Round) {k : Int} (hk0 : 0 ≤ k) (hk : k < 4) :
    C.round_of (C.slotOf (C.opening r + k * C.Δ)) = r := by
  have hΔ := C.Δ_pos
  have hR : 0 < C.R := by have := C.R_ge_three; omega
  have hs : C.slotOf (C.opening r + k * C.Δ) = r * C.R := by
    apply NodeFacts.slotOf_of_bounds
    · simp only [Config.opening, Config.proposal_time]; push_cast; nlinarith
    · simp only [Config.opening, Config.proposal_time]; push_cast; nlinarith
  rw [hs]
  simp only [Config.round_of]
  exact Nat.mul_div_cancel r hR

/-- A block the spec's `freezeRoot` returns is a block of the store's tree. -/
theorem mem_T_of_freezeRoot {P : Provisional V} {st : Store V} {F : Block V} {η r : Round}
    {t0 t1 : Time} {x : Block V}
    (h : Protocol.freezeRoot P st F η r t0 t1 = .ok (some x)) : x ∈ st.T := by
  unfold Protocol.freezeRoot at h
  obtain ⟨w, hw, h⟩ := NoRaise.DRE.ok_of_bind h
  exact NodeFacts.filterM_ok_subset _ _ _ hw
    (GradesFacts.draft_deepest?_mem (Except.ok.inj h))

/-- On a store meeting `StoreOk`, the image of the spec's clip of a tree block against the finalized
    block is the record's `clipGrade` of the two images. -/
theorem toProof_dca_of_mem [Inhabited V] {st : Store V} (hok : NoRaise.StoreOk st) {x : Block V}
    (hx : x ∈ st.T) :
    (Protocol.deepest_compatible_ancestor x st.F).toProof =
      (Model.spec (V := V)).clipGrade x.toProof st.F.toProof := by
  have hinj := hok.2.1.injOn_toProof
  have e := GradesImages.dca_blockOfImage st hinj hok.2.2.1 x.toProof st.F.toProof
  rw [Store.blockOfImage_toProof_of_injOn st hinj hx,
    Store.blockOfImage_toProof_of_injOn st hinj hok.2.2.2] at e
  rw [e, Store.toProof_blockOfImage, GradesFacts.eq_clipGrade]
  rfl

/-- The member `freezeRoot` has at most one outcome. -/
theorem freezeRoot_unique [Inhabited V] {E : DecoupledConsensusModel.Env V}
    {gv : (Model.spec (V := V)).GV} {F : DecoupledConsensusModel.Block V} {η r : Round}
    {t0 t1 : Time} {a b : Option (DecoupledConsensusModel.Block V)}
    (ha : (Model.spec (V := V)).freezeRoot E gv F η r t0 t1 ⇢ a)
    (hb : (Model.spec (V := V)).freezeRoot E gv F η r t0 t1 ⇢ b) : a = b := by
  have ea := (returns_successOutcomes _ _).1 ha
  have eb := (returns_successOutcomes _ _).1 hb
  exact Except.ok.inj (ea.symm.trans eb)

end SpecRecord.RemainingKit

namespace SpecRecord.GradesFacts

open DecoupledConsensusModel DecoupledConsensusModel.Sts DecoupledConsensusModel.Sts.Record
open SpecRecord.RemainingKit
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-- The field `phaseResult_onPhaseTick` of `GradesFacts` at `Model.spec`: if a cache the phase
    tick at `t` leaves holds `root` for round `r₁` and phase `p`, then the cache before held a root
    there of which `root` is an ancestor, or `t` is that phase's domain time and `root` is an
    ancestor of a block passing the chosen grade test `g`. -/
theorem spec_phaseResult_onPhaseTick : ∀ (E : Env V) (hc : Protocol.HealConfig) (st : (Model.spec (V := V)).HS) (t : Int) (c : (Model.spec (V := V)).Cache) {r₁ : Round} {p : Protocol.Phase} {root : Block V}
    (c' : (Model.spec (V := V)).Cache) (hc' : (Model.spec (V := V)).onPhaseTick E hc st t c ⇢ c') (h : (Model.spec (V := V)).phaseResult ((Model.spec (V := V)).cacheAtRound c' r₁) p
    = some (some root)) (g : Block V → Bool) (hg : ∀ B, (Model.spec (V := V)).gradeBool E ((Model.spec (V := V)).gradeView st) st.toFG.F hc.η_SG r₁ ((Model.spec (V := V)).early E hc r₁ p)
    ((Model.spec (V := V)).late E hc r₁ p) B ⇢ g B), (∃ root₀ : Block V,
    (Model.spec (V := V)).phaseResult ((Model.spec (V := V)).cacheAtRound c r₁) p = some (some root₀) ∧
    Block.Preceq root root₀) ∨
    (t = (Model.spec (V := V)).domain E hc r₁ p ∧ ∃ B : Block V,
    g B = true ∧ Block.Preceq root B) := by
  intro E hc st t c r₁ p root c' hc' h g hg
  obtain ⟨S, hS, rfl, -⟩ := sd_onPhaseTick_ok hc'
  change (Spec.Protocol.phaseResult (Spec.Protocol.saved_round_grades
    S.saved_grades r₁) (Spec.Protocol.Phase.toSpec p)).toProof = some (some root) at h
  rcases tick_slot hS r₁ p with e | ⟨-, ht, sg, G, hG, e⟩
  · rw [e] at h
    generalize hR : Spec.Protocol.phaseResult (Spec.Protocol.saved_round_grades
      (Spec.Protocol.advance_to_round c _) r₁) _ = R at h
    rcases R with _ | _ | x
    · cases h
    · cases h
    · rw [toProof_mrcw_some] at h
      obtain rfl := Option.some.inj (Option.some.inj h)
      refine Or.inl ⟨x.toProof, ?_, preceq_dca x _⟩
      have hne : Spec.Protocol.phaseResult (Spec.Protocol.saved_round_grades
          (Spec.Protocol.advance_to_round c ((Spec.Config.toSpec E hc
            unreadHeightConfig).round_of ((Spec.Config.toSpec E hc
              unreadHeightConfig).slotOf t))) r₁) (Spec.Protocol.Phase.toSpec p) ≠
            Spec.GradeResult.pending := by
        rw [hR]; intro h; cases h
      have hv := srg_advance_value hne
      show (Spec.Protocol.phaseResult (Spec.Protocol.saved_round_grades c r₁)
        (Spec.Protocol.Phase.toSpec p)).toProof = _
      rw [← hv, hR]
      rfl
  · rw [e] at h
    rcases G with _ | x
    · cases h
    · rw [toProof_mrcw_some] at h
      obtain rfl := Option.some.inj (Option.some.inj h)
      have hfr := freezeRoot_of_graded_block hG
      exact Or.inr ⟨ht, x.toProof, spec_gradeBool_of_freezeRoot_eq_some _ hfr rfl _ (hg _),
        preceq_dca x _⟩

/-- The field `phaseResult_onPhaseTick_domain` of `GradesFacts` at `Model.spec`: if `r` is the
    round after the round of `t`, `t` is round `r`'s domain time for the phase `p`, and the cache
    `c` holds no result there, then every cache the phase tick at `t` leaves from `st` holds there
    every outcome of `Protocol.freezeRoot` of `st` with that phase's cutoffs, clipped to `st.F`. -/
theorem spec_phaseResult_onPhaseTick_domain : ∀ (E : Env V) (hc : Protocol.HealConfig) (st : (Model.spec (V := V)).HS) (t : Int) (c : (Model.spec (V := V)).Cache) {r : Round} {p : Protocol.Phase} (hρ : ((Model.spec (V := V)).round_of hc (E.slotOf t)) + 1 = r) (ht : t = (Model.spec (V := V)).domain E hc r p) (h : (Model.spec (V := V)).phaseResult ((Model.spec (V := V)).cacheAtRound c r) p = none)
    (c' : (Model.spec (V := V)).Cache) (hc' : (Model.spec (V := V)).onPhaseTick E hc st t c ⇢ c')
    (fr : Option (Block V)) (hfr : (Model.spec (V := V)).freezeRoot E ((Model.spec (V := V)).gradeView st) st.toFG.F hc.η_SG r ((Model.spec (V := V)).early E hc r p)
    ((Model.spec (V := V)).late E hc r p) ⇢ fr), (Model.spec (V := V)).phaseResult ((Model.spec (V := V)).cacheAtRound c' r) p
    = some (fr.map (fun B => (Model.spec (V := V)).clipGrade B st.toFG.F)) := by
  intro E hc st t c r p hρ ht h c' hc' fr hfr
  obtain ⟨S, hS, rfl, hρ'⟩ := sd_onPhaseTick_ok hc'
  have hr : (Spec.Config.toSpec E hc unreadHeightConfig).round_of
      ((Spec.Config.toSpec E hc unreadHeightConfig).slotOf t) + 1 = r := by
    rw [← hρ, ← hρ']
  obtain ⟨⟨-, -, d0⟩, ⟨-, -, d1⟩, ⟨e2, l2, d2⟩⟩ := cutoffs E hc r
  have hd : ∀ k : Int, 0 ≤ k → k < 4 →
      t ≠ (Spec.Config.toSpec E hc unreadHeightConfig).opening r +
        k * (Spec.Config.toSpec E hc unreadHeightConfig).Δ := by
    intro k hk0 hk e
    have := round_of_opening_add (Spec.Config.toSpec E hc unreadHeightConfig) r hk0 hk
    rw [← e] at this
    rw [this] at hr
    exact Nat.succ_ne_self r hr
  rcases p with _ | _ | _
  · exact ((hd 1 (by norm_num) (by norm_num)) (ht.trans (d0.trans (by ring)))).elim
  · exact ((hd 0 le_rfl (by norm_num)) (ht.trans (d1.trans (by ring)))).elim
  have ht2 := ht.trans d2
  have hfr2 : (Model.spec (V := V)).freezeRoot E ((Model.spec (V := V)).gradeView st)
      st.toFG.F hc.η_SG r ((Spec.Config.toSpec E hc unreadHeightConfig).opening r -
        5 * (Spec.Config.toSpec E hc unreadHeightConfig).Δ)
      ((Spec.Config.toSpec E hc unreadHeightConfig).opening r -
        (Spec.Config.toSpec E hc unreadHeightConfig).Δ) ⇢ fr := by
    rw [← e2, ← l2]; exact hfr
  obtain ⟨X, hX, hXr, -, -, -, -, -, k2⟩ := update_grades_value hS rfl rfl
  have hAr := NoRaise.advance_to_round_round c ((Spec.Config.toSpec E hc
    unreadHeightConfig).round_of ((Spec.Config.toSpec E hc unreadHeightConfig).slotOf t))
  have hpc : Spec.Protocol.phaseResult (Spec.Protocol.saved_round_grades c r)
      .g2 = .pending := Spec.GradeResult.toProof_eq_none.mp h
  subst hr
  have hpA : (Spec.Protocol.advance_to_round c ((Spec.Config.toSpec E hc
      unreadHeightConfig).round_of ((Spec.Config.toSpec E hc
        unreadHeightConfig).slotOf t))).next.g2 = .pending := by
    by_contra hne
    refine NoRaise.srg_advance_ne_pending_rev (q := .g2) (ρ := (Spec.Config.toSpec E hc
      unreadHeightConfig).round_of ((Spec.Config.toSpec E hc unreadHeightConfig).slotOf
        t)) ?_ hpc
    unfold Spec.Protocol.saved_round_grades
    rw [hAr, if_neg (Nat.succ_ne_self _), if_pos rfl]
    exact hne
  rcases k2 with ⟨-, hn⟩ | ⟨-, -, sg, G, hG, e⟩
  · exact absurd ⟨ht2, hpA⟩ hn
  obtain rfl := freezeRoot_unique hfr2 (freezeRoot_of_graded_block hG)
  show (Spec.Protocol.phaseResult (Spec.Protocol.saved_round_grades
    S.saved_grades _) .g2).toProof = _
  rw [hX]
  unfold Spec.Protocol.saved_round_grades
  simp only [Spec.Protocol.make_saved_grades_compatible_with, hXr, hAr,
    Spec.Protocol.phaseResult, Spec.Protocol.make_round_grades_compatible_with,
    e, reduceCtorEq, if_false, Nat.succ_ne_self, if_true]
  rcases G with _ | x
  · rfl
  · rw [toProof_mrcw_some]
    exact congrArg (fun y => some (some y)) (toProof_dca_of_mem st.property
      (mem_T_of_freezeRoot hG))

end SpecRecord.GradesFacts
