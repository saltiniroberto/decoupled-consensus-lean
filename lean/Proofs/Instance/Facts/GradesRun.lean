import Proofs.Instance.Facts.Node2
import Proofs.Instance.Facts.HandlersRun
import Proofs.Instance.Facts.Schedule

/-!
# The run facts of the grades family at `Model.spec`

Proofs of the fields of `GradesRunFacts` at `Model.spec` not proved elsewhere, and the bundle
`Model.spec_runFacts_grades`. Along every path of a run, every result of a validator's saved
grades is a block of its tree that comes from the initial frame or from the validator's own earlier
capture, clipped to its current finalized block.
-/

namespace SpecRecord.GradesRunFacts

open Spec
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Claims on the saved grades -/

/-- `res f p`: the result of the phase `p` in the round's grades `f`. -/
abbrev res (f : RoundGrades V) (p : DecoupledConsensusModel.Protocol.Phase) : GradeResult V :=
  Protocol.phaseResult f (Protocol.Phase.toSpec p)

/-- `FrameClaim r f Q`: every computed result `G` of phase `p` in the round's grades `f` satisfies
    `Q r p G`. -/
def FrameClaim (r : Round) (f : RoundGrades V)
    (Q : Round → DecoupledConsensusModel.Protocol.Phase → Option (Block V) → Prop) : Prop :=
  ∀ p G, res f p = .computed G → Q r p G

/-- `CacheClaim c Q`: every computed result of the saved grades `c` satisfies `Q` at its own round:
    the current grades at `c.round`, the next ones at `c.round + 1`. -/
def CacheClaim (c : SavedGrades V)
    (Q : Round → DecoupledConsensusModel.Protocol.Phase → Option (Block V) → Prop) : Prop :=
  FrameClaim c.round c.current Q ∧ FrameClaim (c.round + 1) c.next Q

/-- An answer `st'` of `update_grades` at `t` saves the saved grades `c₂` clipped at `st.F`, where
    `c₂` satisfies `Q` whenever every result of the store's saved grades brought to `t`'s round does
    and every block `graded_block` answers at a due instant does. -/
theorem update_grades_claim {C : Config} {P : Provisional V} {st st' : Store V} {t : Time}
    (h : Protocol.update_grades C P st t = .ok st')
    (Q : Round → DecoupledConsensusModel.Protocol.Phase → Option (Block V) → Prop)
    (hold : CacheClaim (Protocol.advance_to_round st.saved_grades (C.round_of (C.slotOf t))) Q)
    (hnew : ∀ (r : Round) (p : DecoupledConsensusModel.Protocol.Phase) (x : Option (Block V))
      (e l : Time) (g : SavedGrades V), t = C.opening r + Member.domainOffset p * C.Δ →
      e = C.opening r + Protocol.Phase.earlyOffset (Protocol.Phase.toSpec p) * C.Δ →
      l = C.opening r + Member.lateOffset p * C.Δ →
      Protocol.graded_block C P { st with saved_grades := g } r e l = .ok x → Q r p x) :
    ∃ c₂ : SavedGrades V, st'.saved_grades = Protocol.make_saved_grades_compatible_with st.F c₂ ∧
      CacheClaim c₂ Q := by
  simp only [Protocol.update_grades] at h
  repeat' (first
    | (split_ifs at h)
    | (obtain ⟨_, _, h⟩ := NoRaise.DRE.ok_of_bind h; try dsimp only at h))
  all_goals
    have h' := h
    simp only [pure, Except.pure, Except.ok.injEq] at h'
    subst h'
  all_goals
    simp only [Bool.and_eq_true, decide_eq_true_eq] at *
    try casesm* _ ∧ _
    refine ⟨_, rfl, ?_, ?_⟩ <;> intro p G hG <;> cases p <;>
      simp only [res, Protocol.phaseResult, Protocol.Phase.toSpec, reduceCtorEq, if_true,
        if_false, GradeResult.computed.injEq] at hG
  all_goals first
    | exact hold.1 _ G (by simpa [res, Protocol.phaseResult, Protocol.Phase.toSpec] using hG)
    | exact hold.2 _ G (by simpa [res, Protocol.phaseResult, Protocol.Phase.toSpec] using hG)
    | (subst hG
       dsimp only
       simp only [NoRaise.advance_to_round_round]
       refine hnew _ _ _ _ _ _ ?_ ?_ ?_ (by with_reducible assumption)
       all_goals (simp only [NoRaise.advance_to_round_round, Member.domainOffset,
         Member.lateOffset, Protocol.Phase.earlyOffset, Protocol.Phase.toSpec, reduceCtorEq, if_true,
         if_false] at *; first | ring1 | linarith))

omit [DecidableEq V] [Fintype V] in
/-- The round's grades with every result pending satisfy every claim. -/
theorem frameClaim_pending (r : Round)
    (Q : Round → DecoupledConsensusModel.Protocol.Phase → Option (Block V) → Prop) :
    FrameClaim r (Protocol.pending_round_grades : RoundGrades V) Q := by
  intro p G h
  cases p <;> simp [res, Protocol.phaseResult, Protocol.pending_round_grades,
    Protocol.Phase.toSpec] at h

omit [DecidableEq V] [Fintype V] in
/-- A claim on the saved grades is kept by `advance_to_round`. -/
theorem cacheClaim_advance (c : SavedGrades V) (ρ : Round)
    (Q : Round → DecoupledConsensusModel.Protocol.Phase → Option (Block V) → Prop)
    (h : CacheClaim c Q) : CacheClaim (Protocol.advance_to_round c ρ) Q := by
  unfold Protocol.advance_to_round
  split_ifs with h1 h2
  · exact h
  · subst ρ
    exact ⟨h.2, frameClaim_pending _ Q⟩
  · exact ⟨frameClaim_pending _ Q, frameClaim_pending _ Q⟩

omit [DecidableEq V] [Fintype V] in
/-- A claim on the saved grades is weakened along an implication. -/
theorem cacheClaim_mono {c : SavedGrades V}
    {Q Q' : Round → DecoupledConsensusModel.Protocol.Phase → Option (Block V) → Prop}
    (h : CacheClaim c Q) (hQ : ∀ r p G, Q r p G → Q' r p G) : CacheClaim c Q' :=
  ⟨fun p G hG => hQ _ p G (h.1 p G hG), fun p G hG => hQ _ p G (h.2 p G hG)⟩

omit [Fintype V] in
/-- A claim `Q` on the saved grades gives the claim `Q'` on the saved grades clipped at `F`, when
    every result satisfying `Q` satisfies `Q'` once clipped. -/
theorem cacheClaim_clip (F : Block V) (c : SavedGrades V)
    (Q Q' : Round → DecoupledConsensusModel.Protocol.Phase → Option (Block V) → Prop)
    (h : CacheClaim c Q)
    (hQ : ∀ r p G, Q r p G → Q' r p (G.map (fun g => Protocol.deepest_compatible_ancestor g F))) :
    CacheClaim (Protocol.make_saved_grades_compatible_with F c) Q' := by
  have e : ∀ x : GradeResult V, ∀ G, Protocol.make_result_compatible_with F x = .computed G →
      ∃ G₀, x = .computed G₀ ∧ G = G₀.map (fun g => Protocol.deepest_compatible_ancestor g F) := by
    intro x G hx
    rcases x with _ | _ | g
    · simp [Protocol.make_result_compatible_with, Id.run] at hx
    · simp [Protocol.make_result_compatible_with, Id.run, GradeResult.block] at hx
      exact ⟨none, rfl, (GradeResult.computed.inj hx).symm⟩
    · simp [Protocol.make_result_compatible_with, Id.run, GradeResult.block] at hx
      exact ⟨some g, rfl, (GradeResult.computed.inj hx).symm⟩
  have key : ∀ (r : Round) (f : RoundGrades V), FrameClaim r f Q →
      FrameClaim r (Protocol.make_round_grades_compatible_with F f) Q' := by
    intro r f hf p G hG
    cases p <;>
    · obtain ⟨G₀, h0, rfl⟩ := e _ _ hG
      exact hQ r _ G₀ (hf _ G₀ h0)
  exact ⟨key _ _ h.1, key _ _ h.2⟩

omit [DecidableEq V] [Fintype V] in
/-- A claim on the saved grades holds of every computed result `saved_round_grades` reads from them,
    at the round read. -/
theorem cacheClaim_lookup {c : SavedGrades V}
    {Q : Round → DecoupledConsensusModel.Protocol.Phase → Option (Block V) → Prop}
    (h : CacheClaim c Q) (r : Round) (p : DecoupledConsensusModel.Protocol.Phase)
    (G : Option (Block V)) (hG : res (Protocol.saved_round_grades c r) p = .computed G) :
    Q r p G := by
  unfold Protocol.saved_round_grades at hG
  split_ifs at hG with h1 h2
  · subst r; exact h.1 p G hG
  · subst r; exact h.2 p G hG
  · exact frameClaim_pending r Q p G hG

omit [Fintype V] in
/-- On a set `T` that holds the parent of each of its blocks and on which `Block.toProof` is
    injective, the image of a block's deepest ancestor compatible with `F ∈ T` is `clipGrade` of the
    images. -/
theorem toProof_dca_of_mem (T : Finset (Block V))
    (hinj : Set.InjOn (Block.toProof (V := V)) (↑T : Set (Block V)))
    (hpar : ∀ B ∈ T, B.parent ∈ T) {F : Block V} (hF : F ∈ T) :
    ∀ g ∈ T, (Protocol.deepest_compatible_ancestor g F).toProof =
      DecoupledConsensusModel.Protocol.clipGrade g.toProof F.toProof := by
  intro g hg
  rw [GradesLocal.deepest_compatible_ancestor_eq]
  induction g with
  | genesis =>
    rw [GradesLocal.clipBlock, Block.toProof, DecoupledConsensusModel.Protocol.clipGrade]
  | node p s root gv gsv ats v ih =>
    have hc := Block.toProof_compatible_of_injOn T hinj hpar hg hF
    have hp : p ∈ T := hpar _ hg
    show _ = DecoupledConsensusModel.Protocol.clipGrade (.node p.toProof s root.toProof
      (gv.map GoldfishVote.toProof) (gsv.map GoldfishVote.toProof) (ats.map Attestation.toProof)
      v) F.toProof
    rw [DecoupledConsensusModel.Protocol.clipGrade, GradesLocal.clipBlock]
    have hc' : DecoupledConsensusModel.Block.compatible (.node p.toProof s root.toProof
        (gv.map GoldfishVote.toProof) (gsv.map GoldfishVote.toProof)
        (ats.map Attestation.toProof) v) F.toProof =
        Block.compatible (.node p s root gv gsv ats v) F := hc
    rw [hc']
    split_ifs
    · rfl
    · exact ih hp

omit [Fintype V] in
/-- On a set that holds the parent of each of its blocks, the deepest compatible ancestor of a block
    of the set is a block of the set. -/
theorem dca_mem (T : Finset (Block V)) (hpar : ∀ B ∈ T, B.parent ∈ T) (F : Block V) :
    ∀ g ∈ T, Protocol.deepest_compatible_ancestor g F ∈ T := by
  intro g hg
  rw [GradesLocal.deepest_compatible_ancestor_eq]
  induction g with
  | genesis => rw [GradesLocal.clipBlock]; exact hg
  | node p s root gv gsv ats v ih =>
    rw [GradesLocal.clipBlock]
    split_ifs
    · exact hg
    · exact ih (hpar _ hg)

/-- A block `freezeRoot` answers is a block of the store's tree. -/
theorem freezeRoot_mem {P : Provisional V} {st : Store V} {F : Block V} {eta r : Round}
    {e l : Time} {D : Block V} (h : Protocol.freezeRoot P st F eta r e l = .ok (some D)) :
    D ∈ st.T := by
  unfold Protocol.freezeRoot at h
  obtain ⟨A, hA, h⟩ := NoRaise.DRE.ok_of_bind h
  have hD : Block.deepest? A = some D := Except.ok.inj h
  exact NodeFacts.filterM_ok_subset _ _ _ hA (GradesFacts.draft_deepest?_mem hD)

end SpecRecord.GradesRunFacts

/-! ## The tick and the receipt, on the saved grades -/

namespace SpecRecord.GradesRunFacts

open DecoupledConsensusModel
open DecoupledConsensusModel.Sts
open DecoupledConsensusModel.Sts.Record
open DecoupledConsensusModel.Execution
open SpecRecord.NoRaise
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-- The saved grades a tick of `Model.specBase` writes are those of the answer `st0` of
    `update_grades` on the node's store at `t`, clipped at the finalized block of the tick's final
    store. -/
theorem tick_saved {S : Setup V} {v : V} {n : Spec.NodeState V} {t : Time}
    {out : Spec.NodeState V × List (NamedObject V)}
    (hout : (Model.specBase (V := V)).tick S v n t ⇢ out) :
    ∃ st0 : Spec.Store V,
      Spec.Protocol.update_grades (Setup.toSpec S).C (Setup.toSpec S).P n.st t =
        .ok st0 ∧
      out.1.st.saved_grades =
        Spec.Protocol.make_saved_grades_compatible_with out.1.st.F st0.saved_grades := by
  obtain ⟨n', sent, hrun, rfl⟩ := (NodeFacts.tick_returns_iff S v n t out).mp hout
  obtain ⟨st0, st2, st3, st4, st5, sh5, l1, l2, h0, h1, h2, h3, h4, rfl⟩ :=
    NodeFacts.tick_run_ok hrun
  have hst : (Spec.record_awake n t).st = n.st := by rw [NodeFacts.record_awake_eq]
  rw [hst] at h0
  refine ⟨st0, h0, ?_⟩
  have e2 : st2.saved_grades = st0.saved_grades := by
    rcases h1 with ⟨B, rfl, -⟩ | ⟨rfl, -⟩
    · rw [NodeFacts.on_block_saved_grades]
    · rfl
  have e3 : st3.saved_grades = st2.saved_grades := by
    rcases h2 with ⟨u, rfl, -⟩ | ⟨rfl, -⟩
    · rw [NodeFacts.on_goldfish_vote_checked_saved_grades]
    · rfl
  have e4 : st4.saved_grades = st3.saved_grades := by
    rcases h3 with ⟨s', hc⟩ | rfl
    · rw [NodeFacts.update_confirmation_ok hc]
    · rfl
  have e5 : st5.saved_grades = st4.saved_grades := by
    rcases h4 with ⟨row, -, rfl, -⟩ | ⟨rfl, -, -⟩
    · rw [NodeFacts.admit_attestation_saved_grades]
    · rfl
  show (Spec.make_grades_compatible_with_finalized st5).saved_grades = _
  rw [← e2, ← e3, ← e4, ← e5]
  rfl

/-- A store reached by steps holds every block of the tree it was reached from. -/
theorem reach_T_subset {C : Spec.Config} {P : Spec.Provisional V} {τ : Time}
    {a b : Spec.Store V} (h : StoreSteps.StoreReach C P τ a b) : a.T ⊆ b.T := by
  induction h with
  | refl => exact subset_refl _
  | tail _ hs ih => exact fun X hX => (HandlersRunFacts.keepsBlocks_step hs X (ih hX)).1

/-- The member `freezeRoot` of `Model.spec` on the grade view of `st₀` has, as its one outcome,
    the image of the block `graded_block` answers on `st₀` for round `r` and phase `p`. -/
theorem freezeRoot_outcome (S : Setup V) (st₀ : OkStore V) (g : Spec.SavedGrades V)
    (r : Round) (p : DecoupledConsensusModel.Protocol.Phase)
    (x : Option (Spec.Block V)) (e l : Time)
    (he : e = (Setup.toSpec S).C.opening r +
      Spec.Protocol.Phase.earlyOffset (Spec.Protocol.Phase.toSpec p) *
        (Setup.toSpec S).C.Δ)
    (hl : l = (Setup.toSpec S).C.opening r + Member.lateOffset p * (Setup.toSpec S).C.Δ)
    (hx : Spec.Protocol.graded_block (Setup.toSpec S).C (Setup.toSpec S).P
      { st₀.val with saved_grades := g } r e l = .ok x)
    (fr : Option (DecoupledConsensusModel.Block V))
    (hfr : (Model.spec (V := V)).freezeRoot S.E
      ((Model.spec (V := V)).gradeView ((Model.spec (V := V)).toHealing st₀))
      st₀.val.F.toProof S.hc.η_SG r
      ((Model.spec (V := V)).early S.E S.hc r p)
      ((Model.spec (V := V)).late S.E S.hc r p) ⇢ fr) :
    fr = x.map Spec.Block.toProof := by
  subst he hl
  have hx' : Spec.Protocol.freezeRoot (Spec.Provisional.toSpec S.E)
      (Member.gradeView st₀.val) st₀.val.F S.hc.η_SG r
      ((Model.spec (V := V)).early S.E S.hc r p)
      ((Model.spec (V := V)).late S.E S.hc r p) = .ok x := hx
  have h1 : Except.map (Option.map Spec.Block.toProof)
      (Spec.Protocol.freezeRoot (Spec.Provisional.toSpec S.E)
        (Member.gradeView st₀.val) ((Member.gradeView st₀.val).blockOfImage st₀.val.F.toProof)
        S.hc.η_SG r ((Model.spec (V := V)).early S.E S.hc r p)
        ((Model.spec (V := V)).late S.E S.hc r p)) = .ok fr :=
    (returns_successOutcomes _ _).mp hfr
  rw [Spec.Store.blockOfImage_toProof_of_injOn (Member.gradeView st₀.val)
    st₀.property.2.1.injOn_toProof st₀.property.2.2.2, hx'] at h1
  exact (Except.ok.inj h1).symm

/-! ## Where a completed result comes from, along one path of a run -/

/-- `Origin S rho W i v r p root F`: either `r` is round `0` and `root` is empty, or some event `j`
    before event `i` is `v`'s tick at `domain r p`, and `root` is every outcome of the frozen root
    `v`'s store in `W j` computes for round `r` and phase `p`, clipped to `F`. -/
def Origin (S : Setup V) (rho : Record.Run V) (W : Nat → V → (Model.spec (V := V)).N)
    (i : Nat) (v : V) (r : Round) (p : DecoupledConsensusModel.Protocol.Phase)
    (root : Option (DecoupledConsensusModel.Block V)) (F : DecoupledConsensusModel.Block V) : Prop :=
  (r = 0 ∧ root = none) ∨ ∃ (j : Nat) (t : Time),
    j < i ∧ rho.events[j]? = some (.tick v t) ∧ t = (Model.spec (V := V)).domain S.E S.hc r p ∧
    ∀ fr : Option (DecoupledConsensusModel.Block V), (Model.spec (V := V)).freezeRoot S.E
      ((Model.spec (V := V)).gradeView ((Model.spec (V := V)).toHealing (W j v).st.core))
      (W j v).st.core.F S.hc.η_SG r
      ((Model.spec (V := V)).early S.E S.hc r p)
      ((Model.spec (V := V)).late S.E S.hc r p) ⇢ fr →
    root = fr.map (fun B => (Model.spec (V := V)).clipGrade B F)

/-- `Origin` holds at every later event index. -/
theorem origin_mono {S : Setup V} {rho : Record.Run V} {W : Nat → V → (Model.spec (V := V)).N}
    {i k : Nat} {v : V} {r : Round} {p : DecoupledConsensusModel.Protocol.Phase}
    {root : Option (DecoupledConsensusModel.Block V)} {F : DecoupledConsensusModel.Block V}
    (h : Origin S rho W i v r p root F) (hik : i ≤ k) : Origin S rho W k v r p root F := by
  rcases h with h | ⟨j, t, hj, he, ht, hr⟩
  · exact Or.inl h
  · exact Or.inr ⟨j, t, lt_of_lt_of_le hj hik, he, ht, hr⟩

/-- Clipping at `F` then at a descendant `G` of `F` is clipping at `G`. -/
theorem clipGrade_after (B F G : DecoupledConsensusModel.Block V) (hFG : Block.Preceq F G) :
    (Model.spec (V := V)).clipGrade ((Model.spec (V := V)).clipGrade B F) G =
      (Model.spec (V := V)).clipGrade B G := by
  rw [GradesFacts.eq_clipGrade]
  exact (priv% Proofs.Vocabulary.Protocol.Grades.CacheProvenance
    DecoupledConsensusModel.Proofs.NamedCacheProvenance.clip_after_advance) B F G hFG

/-- An origin read against `F` gives the origin of the result clipped at a descendant `G` of `F`,
    read against `G`. -/
theorem origin_clip {S : Setup V} {rho : Record.Run V} {W : Nat → V → (Model.spec (V := V)).N}
    {i : Nat} {v : V} {r : Round} {p : DecoupledConsensusModel.Protocol.Phase}
    {root : Option (DecoupledConsensusModel.Block V)} {F G : DecoupledConsensusModel.Block V}
    (h : Origin S rho W i v r p root F) (hFG : Block.Preceq F G) :
    Origin S rho W i v r p (root.map (fun B => (Model.spec (V := V)).clipGrade B G)) G := by
  rcases h with ⟨hr, rfl⟩ | ⟨j, t, hj, he, ht, hr⟩
  · exact Or.inl ⟨hr, rfl⟩
  · refine Or.inr ⟨j, t, hj, he, ht, fun fr hfr => ?_⟩
    rw [hr fr hfr, Option.map_map]
    congr 1
    funext B
    exact clipGrade_after B F G hFG

/-- `Good S rho W k v T F`: the claim on a saved result that its block, if any, is a block of `T`,
    and that its image has the origin `Origin` at index `k`, read against `F`. -/
def Good (S : Setup V) (rho : Record.Run V) (W : Nat → V → (Model.spec (V := V)).N) (k : Nat)
    (v : V) (T : Finset (Spec.Block V)) (F : DecoupledConsensusModel.Block V) :
    Round → DecoupledConsensusModel.Protocol.Phase → Option (Spec.Block V) → Prop :=
  fun r p G => (∀ g, G = some g → g ∈ T) ∧
    Origin S rho W k v r p (G.map Spec.Block.toProof) F

/-- `Pre S rho W k v T F`: the claim on a saved result that its block, if any, is a block of `T`,
    and that its image clipped at `F` has the origin `Origin` at index `k`, read against `F`. -/
def Pre (S : Setup V) (rho : Record.Run V) (W : Nat → V → (Model.spec (V := V)).N) (k : Nat)
    (v : V) (T : Finset (Spec.Block V)) (F : DecoupledConsensusModel.Block V) :
    Round → DecoupledConsensusModel.Protocol.Phase → Option (Spec.Block V) → Prop :=
  fun r p G => (∀ g, G = some g → g ∈ T) ∧
    Origin S rho W k v r p ((G.map Spec.Block.toProof).map
      (fun B => (Model.spec (V := V)).clipGrade B F)) F

/-- `Good` gives `Pre` at the same `F`. -/
theorem pre_of_good {S : Setup V} {rho : Record.Run V} {W : Nat → V → (Model.spec (V := V)).N}
    {k : Nat} {v : V} {T : Finset (Spec.Block V)} {F : DecoupledConsensusModel.Block V}
    {r : Round} {p : DecoupledConsensusModel.Protocol.Phase} {G : Option (Spec.Block V)}
    (h : Good S rho W k v T F r p G) : Pre S rho W k v T F r p G :=
  ⟨h.1, origin_clip h.2 (Proofs.ModelProperties.Preceq_self _)⟩

/-- Saved grades satisfying `Pre` at `T₀` and `F₀`, clipped at the finalized block of a store `st₁`
    whose tree holds `T₀` and whose finalized block's image descends from `F₀`, satisfy `Good` at
    `st₁`'s tree and finalized block. -/
theorem claim_clip {S : Setup V} {rho : Record.Run V} {W : Nat → V → (Model.spec (V := V)).N}
    {k : Nat} {v : V} {T₀ : Finset (Spec.Block V)} {F₀ : DecoupledConsensusModel.Block V}
    {c : Spec.SavedGrades V} {st₁ : Spec.Store V}
    (h : CacheClaim c (Pre S rho W k v T₀ F₀)) (hsub : T₀ ⊆ st₁.T) (hok : StoreOk st₁)
    (hF : Block.Preceq F₀ st₁.F.toProof) :
    CacheClaim (Spec.Protocol.make_saved_grades_compatible_with st₁.F c)
      (Good S rho W k v st₁.T st₁.F.toProof) := by
  refine cacheClaim_clip st₁.F c _ _ h ?_
  intro r p G ⟨hT, hO⟩
  have hinj : Set.InjOn (Spec.Block.toProof (V := V)) (↑st₁.T : Set _) :=
    hok.2.1.injOn_toProof
  have hpar := hok.2.2.1
  have himg : (G.map (fun g => Spec.Protocol.deepest_compatible_ancestor g st₁.F)).map
      Spec.Block.toProof = (G.map Spec.Block.toProof).map
        (fun B => (Model.spec (V := V)).clipGrade B st₁.F.toProof) := by
    cases G with
    | none => rfl
    | some g =>
      simp only [Option.map_some]
      rw [toProof_dca_of_mem st₁.T hinj hpar hok.2.2.2 g (hsub (hT g rfl)),
        GradesFacts.eq_clipGrade]
      rfl
  refine ⟨?_, ?_⟩
  · intro g hg
    cases G with
    | none => cases hg
    | some g₀ =>
      cases hg
      exact dca_mem st₁.T hpar st₁.F g₀ (hsub (hT g₀ rfl))
  · rw [himg]
    have h2 := origin_clip hO hF
    rwa [Option.map_map, show ((fun B => (Model.spec (V := V)).clipGrade B st₁.F.toProof) ∘
      (fun B => (Model.spec (V := V)).clipGrade B F₀)) =
        (fun B => (Model.spec (V := V)).clipGrade B st₁.F.toProof) from
          funext (fun B => clipGrade_after B F₀ st₁.F.toProof hF)] at h2

/-- `RunClaim S rho W i v`: every result of `v`'s saved grades in the world `W i` satisfies `Good`
    at index `i`, `v`'s tree and the image of `v`'s finalized block. -/
def RunClaim (S : Setup V) (rho : Record.Run V) (W : Nat → V → (Model.spec (V := V)).N)
    (i : Nat) (v : V) : Prop :=
  CacheClaim (W i v).val.st.saved_grades
    (Good S rho W i v (W i v).val.st.T (W i v).val.st.F.toProof)

/-- Folding the event at index `k` from `w` leads to `w'` exactly when there is no event at `k` and
    `w' = w`, or there is one and `w'` is a world it can lead to from `w`. -/
theorem path_step {S : Setup V} {l : List (Record.Event V)} {k : Nat}
    {w w' : V → (Model.spec (V := V)).N}
    (h : w' ∈ ((l.drop k).take 1).foldlM (worldStepOf (Model.spec (V := V)) S) w) :
    (l[k]? = none ∧ w' = w) ∨
      ∃ e, l[k]? = some e ∧ w' ∈ worldStepOf (Model.spec (V := V)) S w e := by
  cases hd : l.drop k with
  | nil =>
    rw [hd] at h
    left
    refine ⟨?_, h⟩
    have hlen : l.length ≤ k := List.drop_eq_nil_iff.mp hd
    exact List.getElem?_eq_none hlen
  | cons e es =>
    rw [hd] at h
    right
    refine ⟨e, ?_, ?_⟩
    · have h1 := congrArg List.head? hd
      rw [List.head?_drop] at h1
      simpa using h1
    · simp only [List.take_succ_cons, List.take_zero, List.foldlM_cons, Set.bind_def] at h
      obtain ⟨w'', hw'', hw'⟩ := Set.mem_iUnion₂.mp h
      have e' : w' = w'' := hw'
      rw [e']
      exact hw''

/-- `RunClaim` holds at the initial world. -/
theorem runClaim_init (S : Setup V) (rho : Record.Run V)
    (W : Nat → V → (Model.spec (V := V)).N)
    (h0 : W 0 = fun u => (Model.spec (V := V)).initial S u) (v : V) :
    RunClaim S rho W 0 v := by
  unfold RunClaim
  rw [h0]
  show CacheClaim Spec.Protocol.initial_saved_grades _
  refine ⟨?_, frameClaim_pending _ _⟩
  intro p G hG
  have hG' : G = none := by
    cases p <;> simp [res, Spec.Protocol.phaseResult,
      Spec.Protocol.initial_saved_grades, Spec.Protocol.empty_round_grades,
      Spec.Protocol.Phase.toSpec] at hG <;> exact hG.symm
  subst hG'
  exact And.intro (fun g hg => absurd hg (by simp)) (Or.inl ⟨rfl, rfl⟩)

/-- A validator whose store an event leaves unchanged keeps `RunClaim` at the next index. -/
theorem runClaim_same {S : Setup V} {rho : Record.Run V}
    {W : Nat → V → (Model.spec (V := V)).N} {i : Nat} {v : V}
    (hst : (W (i + 1) v).val.st = (W i v).val.st) (h : RunClaim S rho W i v) :
    RunClaim S rho W (i + 1) v := by
  unfold RunClaim at h ⊢
  rw [hst]
  exact cacheClaim_mono h (fun r p G hG => ⟨hG.1, origin_mono hG.2 (Nat.le_succ i)⟩)

/-- `v`'s receipt of an object keeps `RunClaim`. -/
theorem runClaim_process {S : Setup V} {rho : Record.Run V}
    {W : Nat → V → (Model.spec (V := V)).N} {i : Nat} {v : V} {o : NamedObject V}
    {n' : (Model.spec (V := V)).N}
    (hn' : (Model.spec (V := V)).process S (W i v) o ⇢ n') (hv : W (i + 1) v = n')
    (h : RunClaim S rho W i v) : RunClaim S rho W (i + 1) v := by
  unfold RunClaim at h ⊢
  rw [hv]
  have hF := NodeFacts.spec_node_process_F S (W i v) o n' hn'
  have he : n'.val = receiveNamedObject S (W i v).val o :=
    (NodeFacts.process_returns_iff S (W i v).val n'.val o).mp hn'
  have hk := NodeFacts.keeps_receipt_process S (W i v).val.st o
  have hpre : CacheClaim (W i v).val.st.saved_grades
      (Pre S rho W (i + 1) v (W i v).val.st.T (W i v).val.st.F.toProof) :=
    cacheClaim_mono h (fun r p G hG => pre_of_good ⟨hG.1, origin_mono hG.2 (Nat.le_succ i)⟩)
  have hst : n'.val.st = Spec.make_grades_compatible_with_finalized
      (Member.receipt_process S (W i v).val.st o) := by
    rw [he, NodeFacts.receiveNamedObject_eq]
  have hsg : n'.val.st.saved_grades = Spec.Protocol.make_saved_grades_compatible_with
      n'.val.st.F (W i v).val.st.saved_grades := by
    rw [hst, ← hk.2.2.2.2.1]
    rfl
  have hT : (W i v).val.st.T ⊆ n'.val.st.T := by
    rw [hst]
    exact hk.2.2.1
  rw [hsg]
  exact claim_clip hpre hT n'.property hF

/-- `v`'s tick at `t`, the event at index `i`, keeps `RunClaim`. -/
theorem runClaim_tick {S : Setup V} {rho : Record.Run V}
    {W : Nat → V → (Model.spec (V := V)).N} {i : Nat} {v : V} {t : Time}
    {out : (Model.spec (V := V)).N × List (NamedObject V)}
    (hout : (Model.spec (V := V)).tick S v (W i v) t ⇢ out) (hv : W (i + 1) v = out.1)
    (he : rho.events[i]? = some (.tick v t)) (h : RunClaim S rho W i v) :
    RunClaim S rho W (i + 1) v := by
  unfold RunClaim at h ⊢
  rw [hv]
  obtain ⟨st0, hupd, hsg⟩ := tick_saved (v := v) (out := (out.1.val, out.2)) hout
  have hpre : CacheClaim (W i v).val.st.saved_grades
      (Pre S rho W (i + 1) v (W i v).val.st.T (W i v).val.st.F.toProof) :=
    cacheClaim_mono h (fun r p G hG => pre_of_good ⟨hG.1, origin_mono hG.2 (Nat.le_succ i)⟩)
  have hadv := cacheClaim_advance _
    ((Setup.toSpec S).C.round_of ((Setup.toSpec S).C.slotOf t)) _ hpre
  obtain ⟨c₂, hc₂, hcl⟩ := update_grades_claim hupd _ hadv (by
    intro r p x e l g ht hE hL hx
    refine ⟨fun g' hg' => ?_, Or.inr ⟨i, t, Nat.lt_succ_self i, he, ht, fun fr hfr => ?_⟩⟩
    · subst hg'
      exact freezeRoot_mem hx
    · have hfr' : (Model.spec (V := V)).freezeRoot S.E
          ((Model.spec (V := V)).gradeView ((Model.spec (V := V)).toHealing
            (⟨(W i v).val.st, (W i v).property⟩ : OkStore V)))
          (W i v).val.st.F.toProof S.hc.η_SG r
          ((Model.spec (V := V)).early S.E S.hc r p)
          ((Model.spec (V := V)).late S.E S.hc r p) ⇢ fr := hfr
      rw [freezeRoot_outcome S ⟨(W i v).val.st, (W i v).property⟩ g r p x e l hE hL hx fr hfr'])
  have hc3 : CacheClaim st0.saved_grades
      (Good S rho W (i + 1) v (W i v).val.st.T (W i v).val.st.F.toProof) := by
    rw [hc₂]
    exact claim_clip hcl subset_rfl (W i v).property (Proofs.ModelProperties.Preceq_self _)
  have hT : (W i v).val.st.T ⊆ out.1.val.st.T :=
    reach_T_subset (HandlersRunFacts.spec_tick_reach S v (W i v) t out hout)
  have hF := NodeFacts.spec_node_tick_F S v (W i v) t out hout
  rw [hsg]
  exact claim_clip (cacheClaim_mono hc3 (fun r p G hG => pre_of_good hG)) hT out.1.property hF

/-- Along every path `W` of a run from the initial world, `RunClaim` holds at every index the path
    reaches, for every validator. -/
theorem runClaim_path (S : Setup V) (rho : Record.Run V)
    (W : Nat → V → (Model.spec (V := V)).N)
    (h0 : W 0 = fun u => (Model.spec (V := V)).initial S u) :
    ∀ i : Nat, (∀ k < i, W (k + 1) ∈ ((rho.events.drop k).take 1).foldlM
        (worldStepOf (Model.spec (V := V)) S) (W k)) →
      ∀ v, RunClaim S rho W i v := by
  intro i
  induction i with
  | zero => exact fun _ v => runClaim_init S rho W h0 v
  | succ i ih =>
    intro hpath v
    have hi := ih (fun k hk => hpath k (Nat.lt_succ_of_lt hk)) v
    rcases path_step (hpath i (Nat.lt_succ_self i)) with ⟨-, hW⟩ | ⟨e, he, hW⟩
    · exact runClaim_same (by rw [hW]) hi
    · cases e with
      | wake u t' =>
        simp only [worldStepOf, Set.mem_singleton_iff] at hW
        refine runClaim_same ?_ hi
        rw [hW]
        by_cases hu : v = u
        · subst hu
          rw [Function.update_self]
          exact HandlersRunFacts.spec_wake_st _
        · rw [Function.update_of_ne hu]
      | tick u t =>
        simp only [worldStepOf, Set.mem_setOf_eq] at hW
        rcases hW with ⟨out, hout, hW⟩ | ⟨-, hW⟩
        · by_cases hu : v = u
          · subst hu
            exact runClaim_tick hout (by rw [hW, Function.update_self]) he hi
          · exact runClaim_same (by rw [hW, Function.update_of_ne hu]) hi
        · exact runClaim_same (by rw [hW]) hi
      | deliver u o t =>
        simp only [worldStepOf, Set.mem_setOf_eq] at hW
        rcases hW with ⟨n', hn', hW⟩ | ⟨-, hW⟩
        · by_cases hu : v = u
          · subst hu
            exact runClaim_process hn' (by rw [hW, Function.update_self]) hi
          · exact runClaim_same (by rw [hW, Function.update_of_ne hu]) hi
        · exact runClaim_same (by rw [hW]) hi

/-! ## Paths through a fold of events -/

/-- A world a fold of the first `i` events of `l` reaches from `w₀` lies on a path from `w₀`, each
    world one step from the one before. -/
theorem path_of_fold (S : Setup V) :
    ∀ (l : List (Record.Event V)) (i : Nat) (w₀ w₁ : V → (Model.spec (V := V)).N),
      w₁ ∈ (l.take i).foldlM (worldStepOf (Model.spec (V := V)) S) w₀ →
      ∃ W : Nat → V → (Model.spec (V := V)).N, W 0 = w₀ ∧ W i = w₁ ∧
        ∀ k < i, W (k + 1) ∈ ((l.drop k).take 1).foldlM
          (worldStepOf (Model.spec (V := V)) S) (W k) := by
  intro l
  induction l with
  | nil =>
    intro i w₀ w₁ h
    have e : w₁ = w₀ := by simpa using h
    exact ⟨fun _ => w₀, rfl, e.symm, fun k _ => by simp⟩
  | cons e l ih =>
    intro i w₀ w₁ h
    cases i with
    | zero =>
      have e' : w₁ = w₀ := by simpa using h
      exact ⟨fun _ => w₀, rfl, e'.symm, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
    | succ i =>
      rw [List.take_succ_cons, List.foldlM_cons, Set.bind_def] at h
      obtain ⟨w', hw', h⟩ := Set.mem_iUnion₂.mp h
      obtain ⟨W, h0, hi, hstep⟩ := ih i w' w₁ h
      refine ⟨fun k => Nat.casesOn k w₀ (fun k => W k), rfl, hi, ?_⟩
      intro k hk
      cases k with
      | zero =>
        show W 0 ∈ (([e] ++ l).drop 0 |>.take 1).foldlM _ w₀
        rw [h0]
        simp only [List.drop_zero, List.singleton_append, List.take_succ_cons, List.take_zero,
          List.foldlM_cons, Set.bind_def]
        exact Set.mem_iUnion₂.mpr ⟨w', hw', rfl⟩
      | succ k =>
        exact hstep k (Nat.lt_of_succ_lt_succ hk)

/-- On a path from the initial world, the world at index `k` is one the first `k` events of the run
    can lead to. -/
theorem path_stateBefore (S : Setup V) (rho : Record.Run V)
    (W : Nat → V → (Model.spec (V := V)).N)
    (h0 : W 0 = fun u => (Model.spec (V := V)).initial S u) (i : Nat)
    (hstep : ∀ k < i, W (k + 1) ∈ ((rho.events.drop k).take 1).foldlM
      (worldStepOf (Model.spec (V := V)) S) (W k)) :
    ∀ k ≤ i, W k ∈ stateBeforeOf (Model.spec (V := V)) S rho k := by
  intro k
  induction k with
  | zero =>
    intro _
    rw [h0]
    show _ ∈ ([] : List (Record.Event V)).foldlM _ _
    rfl
  | succ k ih =>
    intro hk
    unfold stateBeforeOf
    rw [List.take_add, List.foldlM_append, Set.bind_def]
    exact Set.mem_iUnion₂.mpr ⟨W k, ih (Nat.le_of_succ_le hk), hstep k (Nat.lt_of_succ_le hk)⟩

/-- On a path, the world at index `m` is one the events `j` to `m - 1` lead to from the world at
    index `j`. -/
theorem path_segment (S : Setup V) (rho : Record.Run V)
    (W : Nat → V → (Model.spec (V := V)).N) (i : Nat)
    (hstep : ∀ k < i, W (k + 1) ∈ ((rho.events.drop k).take 1).foldlM
      (worldStepOf (Model.spec (V := V)) S) (W k)) (j : Nat) :
    ∀ m, j ≤ m → m ≤ i → W m ∈ ((rho.events.drop j).take (m - j)).foldlM
      (worldStepOf (Model.spec (V := V)) S) (W j) := by
  intro m hjm
  induction m, hjm using Nat.le_induction with
  | base =>
    intro _
    rw [Nat.sub_self, List.take_zero]
    rfl
  | succ m hjm ih =>
    intro hm
    rw [show m + 1 - j = (m - j) + 1 by omega, List.take_add, List.foldlM_append, Set.bind_def,
      List.drop_drop, show j + (m - j) = m by omega]
    exact Set.mem_iUnion₂.mpr ⟨W m, ih (Nat.le_of_succ_le hm), hstep m (Nat.lt_of_succ_le hm)⟩

/-! ## The fields `completed_phase_origin` and `completed_phase_origin_along` -/

/-- A completed result the record reads from a validator's saved grades on a path is the image of a
    saved result satisfying `Good` at its round and phase. -/
theorem origin_of_path (S : Setup V) (rho : Record.Run V)
    (W : Nat → V → (Model.spec (V := V)).N)
    (h0 : W 0 = fun u => (Model.spec (V := V)).initial S u) (i : Nat)
    (hstep : ∀ k < i, W (k + 1) ∈ ((rho.events.drop k).take 1).foldlM
      (worldStepOf (Model.spec (V := V)) S) (W k))
    (v : V) (r : Round) (p : DecoupledConsensusModel.Protocol.Phase)
    (root : Option (DecoupledConsensusModel.Block V))
    (h : (Model.spec (V := V)).phaseResult
      ((Model.spec (V := V)).cacheAtRound (W i v).cache r) p = some root) :
    Origin S rho W i v r p root (W i v).val.st.F.toProof := by
  have hc := runClaim_path S rho W h0 i hstep v
  have h' : (res (Spec.Protocol.saved_round_grades (W i v).val.st.saved_grades r)
      p).toProof = some root := h
  cases hG : res (Spec.Protocol.saved_round_grades (W i v).val.st.saved_grades r) p with
  | pending => rw [hG] at h'; cases h'
  | computed G =>
    rw [hG] at h'
    have e : root = G.map Spec.Block.toProof := (Option.some.inj h').symm
    subst e
    exact (cacheClaim_lookup hc r p G hG).2

/-- The field `completed_phase_origin_along` of `GradesRunFacts` at `Model.spec`: on every path
    `W` of `rho`, a completed result `root` for round `r` and phase `p` in `v`'s cache at `W i` is
    empty at round 0, or is every outcome of the frozen root `v`'s store computed at an earlier tick
    of `v` at `domain r p`, clipped to `v`'s finalized block in `W i`. -/
theorem spec_completed_phase_origin_along : ∀ (S : Setup V) (rho : Record.Run V)
    (W : Nat → V → (Model.spec (V := V)).N),
    (∀ i : Nat, W i ∈ stateBeforeOf (Model.spec (V := V)) S rho i ∧
      W (i + 1) ∈ ((rho.events.drop i).take (i + 1 - i)).foldlM
        (worldStepOf (Model.spec (V := V)) S) (W i)) →
    ∀ (i : Nat) (v : V) (r : Round) (p : DecoupledConsensusModel.Protocol.Phase)
      (root : Option (DecoupledConsensusModel.Block V)),
    (Model.spec (V := V)).phaseResult
      ((Model.spec (V := V)).cacheAtRound (W i v).cache r) p = some root →
    (r = 0 ∧ root = none) ∨ ∃ (j : Nat) (t : Time),
      j < i ∧ rho.events[j]? = some (.tick v t) ∧ t = (Model.spec (V := V)).domain S.E S.hc r p ∧
      ∀ fr : Option (DecoupledConsensusModel.Block V), (Model.spec (V := V)).freezeRoot S.E
        ((Model.spec (V := V)).gradeView ((Model.spec (V := V)).toHealing (W j v).st.core))
        (W j v).st.core.F S.hc.η_SG r
        ((Model.spec (V := V)).early S.E S.hc r p)
        ((Model.spec (V := V)).late S.E S.hc r p) ⇢ fr →
      root = fr.map (fun B => (Model.spec (V := V)).clipGrade B (W i v).st.core.F) := by
  intro S rho W hW i v r p root h
  have h0 : W 0 = fun u => (Model.spec (V := V)).initial S u := (hW 0).1
  have hstep : ∀ k < i, W (k + 1) ∈ ((rho.events.drop k).take 1).foldlM
      (worldStepOf (Model.spec (V := V)) S) (W k) := fun k _ => by
    have := (hW k).2
    rwa [Nat.add_sub_cancel_left] at this
  exact origin_of_path S rho W h0 i hstep v r p root h

/-- The field `completed_phase_origin` of `GradesRunFacts` at `Model.spec`: a completed result
    `root` for round `r` and phase `p` in `v`'s cache in a world `w₁` before event `i` is empty at
    round 0, or is every outcome of the frozen root `v`'s store computed, in a world before an
    earlier tick `j` of `v` at `domain r p` that leads to `w₁`, clipped to `v`'s finalized block in
    `w₁`. -/
theorem spec_completed_phase_origin : ∀ (S : Setup V) (rho : Record.Run V) (i : Nat) (v : V)
    (r : Round) (p : DecoupledConsensusModel.Protocol.Phase)
    (root : Option (DecoupledConsensusModel.Block V)),
    ∀ w₁ ∈ stateBeforeOf (Model.spec (V := V)) S rho i,
    (Model.spec (V := V)).phaseResult
      ((Model.spec (V := V)).cacheAtRound (w₁ v).cache r) p = some root →
    (r = 0 ∧ root = none) ∨ ∃ (j : Nat) (t : Time),
      j < i ∧ rho.events[j]? = some (.tick v t) ∧ t = (Model.spec (V := V)).domain S.E S.hc r p ∧
      ∃ w ∈ stateBeforeOf (Model.spec (V := V)) S rho j,
      w₁ ∈ ((rho.events.drop j).take (i - j)).foldlM (worldStepOf (Model.spec (V := V)) S) w ∧
      ∀ fr : Option (DecoupledConsensusModel.Block V), (Model.spec (V := V)).freezeRoot S.E
        ((Model.spec (V := V)).gradeView ((Model.spec (V := V)).toHealing (w v).st.core))
        (w v).st.core.F S.hc.η_SG r
        ((Model.spec (V := V)).early S.E S.hc r p)
        ((Model.spec (V := V)).late S.E S.hc r p) ⇢ fr →
      root = fr.map (fun B => (Model.spec (V := V)).clipGrade B (w₁ v).st.core.F) := by
  intro S rho i v r p root w₁ hw₁ h
  obtain ⟨W, h0, hi, hstep⟩ := path_of_fold S rho.events i _ w₁ hw₁
  subst hi
  rcases origin_of_path S rho W h0 i hstep v r p root h with hz | ⟨j, t, hj, he, ht, hr⟩
  · exact Or.inl hz
  · exact Or.inr ⟨j, t, hj, he, ht, W j, path_stateBefore S rho W h0 i hstep j hj.le,
      path_segment S rho W i hstep j i hj.le le_rfl, hr⟩

end SpecRecord.GradesRunFacts

/-! ## The results the grades update keeps -/

namespace SpecRecord.GradesRunFacts

open Spec
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]

/-- `update_grades` keeps every computed result of the saved grades brought to `t`'s round, clipped
    at the store's finalized block. -/
theorem update_grades_kept {C : Config} {P : Provisional V} {st st' : Store V} {t : Time}
    (h : Protocol.update_grades C P st t = .ok st') (r : Round)
    (p : DecoupledConsensusModel.Protocol.Phase)
    (hne : res (Protocol.saved_round_grades
      (Protocol.advance_to_round st.saved_grades (C.round_of (C.slotOf t))) r) p ≠ .pending) :
    res (Protocol.saved_round_grades st'.saved_grades r) p =
      Protocol.make_result_compatible_with st.F (res (Protocol.saved_round_grades
        (Protocol.advance_to_round st.saved_grades (C.round_of (C.slotOf t))) r) p) := by
  have hround := NoRaise.advance_to_round_round st.saved_grades (C.round_of (C.slotOf t))
  simp only [Protocol.update_grades] at h
  repeat' (first
    | (split_ifs at h)
    | (obtain ⟨_, _, h⟩ := NoRaise.DRE.ok_of_bind h; try dsimp only at h))
  all_goals
    have h' := h
    simp only [pure, Except.pure, Except.ok.injEq] at h'
    subst h'
  all_goals
    simp only [Bool.and_eq_true, decide_eq_true_eq] at *
    try casesm* _ ∧ _
    unfold Protocol.saved_round_grades at hne ⊢
    simp only [Protocol.make_saved_grades_compatible_with,
      Protocol.make_round_grades_compatible_with] at hne ⊢
    split_ifs at hne ⊢ <;> cases p <;>
      simp only [res, Protocol.phaseResult, Protocol.Phase.toSpec, reduceCtorEq, if_true,
        if_false] at hne ⊢
  all_goals first | rfl | exact absurd (by with_reducible assumption) hne

omit [Fintype V] in
/-- Clipping a result at `F` twice is clipping it once. -/
theorem mrc_idem (F : Block V) (x : GradeResult V) :
    Protocol.make_result_compatible_with F (Protocol.make_result_compatible_with F x) =
      Protocol.make_result_compatible_with F x := by
  have hkeep : ∀ g : Block V, g.compatible F = true →
      Protocol.deepest_compatible_ancestor g F = g := by
    intro g hg
    rw [GradesLocal.deepest_compatible_ancestor_eq]
    cases g with
    | genesis => rw [GradesLocal.clipBlock]
    | node p s root gv gsv ats v => rw [GradesLocal.clipBlock, if_pos hg]
  rcases x with _ | _ | g
  · rfl
  · rfl
  · show GradeResult.computed (some (Protocol.deepest_compatible_ancestor
        (Protocol.deepest_compatible_ancestor g F) F)) =
      GradeResult.computed (some (Protocol.deepest_compatible_ancestor g F))
    rw [hkeep _ (SubtypeEqualities.deepest_compatible_ancestor_compatible g F)]

omit [DecidableEq V] [Fintype V] in
/-- The grades of round `ρ` in the saved grades brought to `ρ` are the grades of round `ρ` in the
    saved grades. -/
theorem srg_advance_self (c : SavedGrades V) (ρ : Round) :
    Protocol.saved_round_grades (Protocol.advance_to_round c ρ) ρ =
      Protocol.saved_round_grades c ρ := by
  unfold Protocol.advance_to_round
  by_cases h1 : ρ = c.round
  · rw [if_pos h1]
  · rw [if_neg h1]
    by_cases h2 : ρ = c.round + 1
    · rw [if_pos h2]
      unfold Protocol.saved_round_grades
      simp [h2]
    · rw [if_neg h2]
      unfold Protocol.saved_round_grades
      simp [h1, h2]

omit [DecidableEq V] [Fintype V] in
/-- Saved grades whose blocks are all in `T` satisfy `Store.ContractInTree T c`. -/
theorem contractInTree_of_claim {T : Finset (Block V)} {c : SavedGrades V}
    (h : CacheClaim c (fun _ _ G => ∀ g, G = some g → g ∈ T)) : Store.ContractInTree T c := by
  intro fr hfr g hg G hG
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hfr hg
  have key : ∀ (f : RoundGrades V) (r : Round),
      FrameClaim r f (fun _ _ G => ∀ g, G = some g → g ∈ T) →
      ∀ x ∈ [f.g0, f.g1, f.g2], x = .computed (some G) → G ∈ T := by
    intro f r hf x hx hxG
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact hf .g0 (some G) hxG G rfl
    · exact hf .g1 (some G) hxG G rfl
    · exact hf .g2 (some G) hxG G rfl
  rcases hfr with rfl | rfl
  · exact key _ _ h.1 g (by simpa using hg) hG
  · exact key _ _ h.2 g (by simpa using hg) hG

end SpecRecord.GradesRunFacts

/-! ## The field `frame_phase_prepared_eq_of_outcomes` -/

namespace SpecRecord.GradesRunFacts

open DecoupledConsensusModel
open DecoupledConsensusModel.Sts
open DecoupledConsensusModel.Sts.Record
open DecoupledConsensusModel.Execution
open SpecRecord.NoRaise
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-- In every world a list of events leads to from the initial world, every block of every
    validator's saved grades is a block of its tree. -/
theorem memClaim_of_fold (S : Setup V) (es : List (Record.Event V))
    (w : V → (Model.spec (V := V)).N)
    (hw : w ∈ es.foldlM (worldStepOf (Model.spec (V := V)) S)
      (fun u => (Model.spec (V := V)).initial S u)) (v : V) :
    CacheClaim (w v).val.st.saved_grades
      (fun _ _ G => ∀ g, G = some g → g ∈ (w v).val.st.T) := by
  let rho : Record.Run V := ⟨∅, 0, es⟩
  have hw' : w ∈ (rho.events.take es.length).foldlM (worldStepOf (Model.spec (V := V)) S)
      (fun u => (Model.spec (V := V)).initial S u) := by
    rw [show rho.events.take es.length = es from List.take_length]
    exact hw
  obtain ⟨W, h0, hn, hstep⟩ := path_of_fold S rho.events es.length _ w hw'
  have hc := runClaim_path S rho W h0 es.length hstep v
  unfold RunClaim at hc
  rw [hn] at hc
  exact cacheClaim_mono hc (fun r p G hG => hG.1)

omit [Inhabited V] in
/-- If the blocks of the saved grades are blocks of the tree `T` of a store, the saved grades
    `update_grades` writes on it hold blocks of `T` only. -/
theorem memClaim_update_grades {C : Spec.Config} {P : Spec.Provisional V}
    {st st' : Spec.Store V} {t : Time} (hok : StoreOk st)
    (h : Spec.Protocol.update_grades C P st t = .ok st')
    (hmem : CacheClaim st.saved_grades (fun _ _ G => ∀ g, G = some g → g ∈ st.T)) :
    CacheClaim st'.saved_grades (fun _ _ G => ∀ g, G = some g → g ∈ st.T) := by
  obtain ⟨c₂, hc₂, hcl⟩ := update_grades_claim h (fun _ _ G => ∀ g, G = some g → g ∈ st.T)
    (cacheClaim_advance _ _ _ hmem) (fun r p x e l g ht he hl hx g' hg' => by
      subst hg'
      exact freezeRoot_mem hx)
  rw [hc₂]
  refine cacheClaim_clip _ _ _ _ hcl (fun r p G hG g hg => ?_)
  cases G with
  | none => cases hg
  | some g₀ =>
    cases hg
    exact dca_mem _ hok.2.2.1 _ _ (hG g₀ rfl)

/-- The field `frame_phase_prepared_eq_of_outcomes` of `GradesRunFacts` at `Model.spec`: if the
    frame `v`'s node state reads for round `r` has the result `root` at phase `p`, then every
    outcome of the phase tick at `u`, in round `r`, reads the same result. -/
theorem spec_frame_phase_prepared_eq_of_outcomes : ∀ (S : Setup V) (rho : Record.Run V)
    (v : V) (r : Round) (p : DecoupledConsensusModel.Protocol.Phase) (u : Time)
    (_hround : (Model.spec (V := V)).round_of S.hc (S.E.slotOf u) = r)
    (root : Option (DecoupledConsensusModel.Block V)) (w : V → (Model.spec (V := V)).N)
    (_hw : w ∈ (rho.events.filter (fun e => decide (e.time < u))).foldlM
      (worldStepOf (Model.spec (V := V)) S) (fun x => (Model.spec (V := V)).initial S x))
    (_hbase : (Model.spec (V := V)).phaseResult ((Model.spec (V := V)).readFrame (w v).cache
      ((Model.spec (V := V)).toHealing (w v).st.core) r) p = some root)
    (c : (Model.spec (V := V)).Cache)
    (_hc : (Model.spec (V := V)).onPhaseTick S.E S.hc (w v).st.core.toHealing u (w v).cache ⇢ c),
    (Model.spec (V := V)).phaseResult ((Model.spec (V := V)).readFrame c
      ((Model.spec (V := V)).toHealing
        ((Model.spec (V := V)).ns_setClock S.E (w v).st u).core) r) p = some root := by
  intro S rho v r p u hround root w hw hbase c hc
  have hok : StoreOk (w v).val.st := (w v).property
  have hmem := memClaim_of_fold S _ w hw v
  have hL : (Model.spec (V := V)).phaseResult ((Model.spec (V := V)).readFrame
      (w v).cache ((Model.spec (V := V)).toHealing (w v).st.core) r) p =
      (Spec.Protocol.make_result_compatible_with (w v).val.st.F
        (res (Spec.Protocol.saved_round_grades (w v).val.st.saved_grades r) p)).toProof := by
    show (Spec.Protocol.phaseResult (Spec.Protocol.round_grades
      { (w v).val.st with saved_grades :=
          (w v).val.st.contractOfImage (w v).val.st.saved_grades } r)
      (Spec.Protocol.Phase.toSpec p)).toProof = _
    rw [Spec.Store.contractOfImage_of_distinctRoots _ hok.2.1
      (contractInTree_of_claim hmem)]
    cases p <;> rfl
  rw [hL] at hbase
  obtain ⟨S', hS', rfl, hρ⟩ := GradesFacts.sd_onPhaseTick_ok hc
  have hρr : (Spec.Config.toSpec S.E S.hc unreadHeightConfig).round_of
      ((Spec.Config.toSpec S.E S.hc unreadHeightConfig).slotOf u) = r := hρ.trans hround
  have hmem' := memClaim_update_grades hok hS' hmem
  have hne : res (Spec.Protocol.saved_round_grades
      (Spec.Protocol.advance_to_round (w v).val.st.saved_grades
        ((Spec.Config.toSpec S.E S.hc unreadHeightConfig).round_of
          ((Spec.Config.toSpec S.E S.hc unreadHeightConfig).slotOf u))) r) p ≠
        .pending := by
    rw [hρr, srg_advance_self]
    intro hp
    rw [hp] at hbase
    cases hbase
  have hkept := update_grades_kept hS' r p hne
  rw [hρr, srg_advance_self] at hkept
  show (Spec.Protocol.phaseResult (Spec.Protocol.round_grades
    { Member.ns_setClock S.E (w v).val.st u with saved_grades :=
        (Member.ns_setClock S.E (w v).val.st u).contractOfImage S'.saved_grades } r)
    (Spec.Protocol.Phase.toSpec p)).toProof = some root
  rw [Spec.Store.contractOfImage_of_distinctRoots
    (Member.ns_setClock S.E (w v).val.st u) hok.2.1 (contractInTree_of_claim hmem')]
  have hR : (Spec.Protocol.phaseResult (Spec.Protocol.round_grades
      { Member.ns_setClock S.E (w v).val.st u with saved_grades := S'.saved_grades } r)
      (Spec.Protocol.Phase.toSpec p)) =
      Spec.Protocol.make_result_compatible_with (w v).val.st.F
        (res (Spec.Protocol.saved_round_grades S'.saved_grades r) p) := by
    cases p <;> rfl
  have hkept' : res (Spec.Protocol.saved_round_grades S'.saved_grades r) p =
      Spec.Protocol.make_result_compatible_with (w v).val.st.F
        (res (Spec.Protocol.saved_round_grades (w v).val.st.saved_grades r) p) := hkept
  rw [hR, hkept', mrc_idem]
  exact hbase

end SpecRecord.GradesRunFacts

/-! ## The grade-2 block a duty reads -/

namespace SpecRecord.GradesRunFacts

open Spec
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- The deepest compatible ancestor of `g` is an ancestor of `g`, or `g` itself. -/
theorem dca_ancestorEq (g F : Block V) :
    (Protocol.deepest_compatible_ancestor g F).ancestorEq g = true := by
  rw [GradesLocal.deepest_compatible_ancestor_eq]
  induction g with
  | genesis =>
    rw [GradesLocal.clipBlock]
    simp [Block.ancestorEq]
  | node p s root gv gsv ats v ih =>
    rw [GradesLocal.clipBlock]
    split_ifs
    · simp [Block.ancestorEq]
    · simp only [Block.ancestorEq, Bool.or_eq_true, decide_eq_true_eq]
      exact Or.inr ih

omit [Fintype V] in
/-- A result the clip at `F` makes `computed (some G)` was `computed (some g)`, with `G` the clip of
    `g`. -/
theorem mrc_some {F : Block V} {x : GradeResult V} {G : Block V}
    (h : Protocol.make_result_compatible_with F x = .computed (some G)) :
    ∃ g, x = .computed (some g) ∧ G = Protocol.deepest_compatible_ancestor g F := by
  rcases x with _ | _ | g
  · cases h
  · cases h
  · exact ⟨g, rfl, (Option.some.inj (GradeResult.computed.inj h)).symm⟩

omit [Fintype V] in
/-- The block of `grade2Block`'s answer `some q` is an ancestor of the grade-2 block of the round's
    grades, or that block itself. -/
theorem grade2Block_some {st : Store V} {grades : RoundGrades V} {q : Block V}
    (h : Protocol.grade2Block st grades = .ok (some q)) :
    ∃ G, grades.g2 = .computed (some G) ∧ q.ancestorEq G = true := by
  unfold Protocol.grade2Block at h
  obtain ⟨Gs, hGs, h⟩ := NoRaise.DRE.of_bind_ok h
  obtain ⟨G, hG, -, hqG⟩ := GradesFacts.draft_active_prefix_some (Except.ok.inj h)
  refine ⟨G, ?_, hqG⟩
  rcases grades with ⟨g0, g1, g2⟩
  cases g2 with
  | pending => cases hGs
  | computed X =>
    cases g1 with
    | pending => cases hGs
    | computed Y =>
      cases g0 with
      | pending => cases hGs
      | computed Z =>
        have e : Gs = ⟨X, Y, Z⟩ := (Except.ok.inj hGs).symm
        subst e
        rw [← hG]

omit [Fintype V] in
/-- The grade-2 block of round `r`'s grades on a store whose saved grades are `c` of round `r`, read
    through a tree, filled and clipped, has an image that is an ancestor of, or equal to, the image
    of `c`'s round-`r` grade-2 block. -/
theorem round_g2_of_contract {X : Store V} {c : SavedGrades V} {r : Round} (hround : c.round = r)
    {G : Block V}
    (h : (Protocol.round_grades
      { Store.ofImage X with
        saved_grades := SpecRecord.fill (Protocol.advance_to_round (X.contractOfImage c) r) }
      r).g2 = .computed (some G)) :
    ∃ g, c.current.g2 = .computed (some g) ∧
      DecoupledConsensusModel.Block.Preceq G.toProof g.toProof := by
  subst hround
  have hadv : Protocol.advance_to_round (X.contractOfImage c) c.round = X.contractOfImage c := by
    unfold Protocol.advance_to_round
    exact if_pos rfl
  have hsrg : Protocol.saved_round_grades (SpecRecord.fill (X.contractOfImage c)) c.round =
      fillRound (X.roundGradesOfImage c.current) := by
    unfold Protocol.saved_round_grades
    exact (if_pos rfl).trans rfl
  have h' : Protocol.make_result_compatible_with (Store.ofImage X).F
      (fillResult (X.resultOfImage c.current.g2)) = .computed (some G) := by
    rw [← h]
    show _ = (Protocol.make_round_grades_compatible_with _
      (Protocol.saved_round_grades (SpecRecord.fill (Protocol.advance_to_round (X.contractOfImage c)
        c.round)) c.round)).g2
    rw [hadv, hsrg]
    rfl
  obtain ⟨b, hb, rfl⟩ := mrc_some h'
  rcases hx : c.current.g2 with _ | _ | g
  · rw [hx] at hb; cases hb
  · rw [hx] at hb; cases hb
  · rw [hx] at hb
    have hb' : b = X.blockOfImage g.toProof :=
      (Option.some.inj (GradeResult.computed.inj hb)).symm
    subst hb'
    refine ⟨g, rfl, ?_⟩
    have h1 := Block.toProof_preceq_of_ancestorEq _ _
      (dca_ancestorEq (X.blockOfImage g.toProof) (Store.ofImage X).F)
    rw [Store.toProof_blockOfImage] at h1
    exact DecoupledConsensusModel.Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mp h1

end SpecRecord.GradesRunFacts

/-! ## The fields `q2_capture_at_action_read` and `q2_capture_at_action_read_along` -/

namespace SpecRecord.GradesRunFacts

open DecoupledConsensusModel
open DecoupledConsensusModel.Sts
open DecoupledConsensusModel.Sts.Record
open DecoupledConsensusModel.Execution
open SpecRecord.NoRaise
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-- On a path of the run, the grade-2 block a duty reads at round `r`'s action instant is an
    ancestor of, or equal to, a G2 root `v` froze at its own earlier tick at `domain r .g2`. -/
theorem q2_of_path (S : Setup V) (rho : Record.Run V)
    (W : Nat → V → (Model.spec (V := V)).N)
    (h0 : W 0 = fun u => (Model.spec (V := V)).initial S u) (i : Nat)
    (hstep : ∀ k < i, W (k + 1) ∈ ((rho.events.drop k).take 1).foldlM
      (worldStepOf (Model.spec (V := V)) S) (W k))
    (v : V) (r : Round) (q : DecoupledConsensusModel.Block V) (c : (Model.spec (V := V)).Cache)
    (hc : (Model.spec (V := V)).onPhaseTick S.E S.hc (W i v).st.core.toHealing
      ((Model.spec (V := V)).a S.hc S.E.Δ r) (W i v).cache ⇢ c)
    (st : (Model.spec (V := V)).NS)
    (hq : (Model.spec (V := V)).grade2_block_with
      ((Model.spec (V := V)).gradeContract
        ((Model.spec (V := V)).mkNode st (W i v).record c).cache) S.E S.hc
      ((Model.spec (V := V)).toHealing
        ((Model.spec (V := V)).mkNode st (W i v).record c).st.core) r ⇢ some q) :
    ∃ (j : Nat) (raw : DecoupledConsensusModel.Block V),
      j < i ∧
      rho.events[j]? = some (.tick v ((Model.spec (V := V)).domain S.E S.hc r .g2)) ∧
      (∀ fr : Option (DecoupledConsensusModel.Block V), (Model.spec (V := V)).freezeRoot S.E
        ((Model.spec (V := V)).gradeView ((Model.spec (V := V)).toHealing (W j v).st.core))
        (W j v).st.core.F S.hc.η_SG r
        ((Model.spec (V := V)).early S.E S.hc r .g2)
        ((Model.spec (V := V)).late S.E S.hc r .g2) ⇢ fr → fr = some raw) ∧
      Block.Preceq q raw := by
  obtain ⟨S', hS', rfl, hρ⟩ := GradesFacts.sd_onPhaseTick_ok hc
  have hra : (Spec.Config.toSpec S.E S.hc unreadHeightConfig).round_of
      ((Spec.Config.toSpec S.E S.hc unreadHeightConfig).slotOf
        ((Model.spec (V := V)).a S.hc S.E.Δ r)) = r :=
    hρ.trans (ScheduleFacts.spec_round_of_slotOf_a S r)
  have hcr : S'.saved_grades.round = r := (NoRaise.update_grades_results hS').1.trans hra
  have hq' : Returns (Member.grade2_block_with S'.saved_grades S.E S.hc
      { st.val with saved_grades := S'.saved_grades } r) (some q) := hq
  obtain ⟨Q2, hQ2, hQ⟩ := ContractImages.grade2_block_with_shape hq'
  obtain ⟨q', rfl, rfl⟩ : ∃ q', Q2 = some q' ∧ q = q'.toProof := by
    cases Q2 with
    | none => cases hQ
    | some q' => exact ⟨q', rfl, Option.some.inj hQ⟩
  obtain ⟨G, hG2, hqG⟩ := grade2Block_some hQ2
  obtain ⟨g₄, hg₄, hGg₄⟩ := round_g2_of_contract hcr hG2
  have hsrg' : res (Spec.Protocol.saved_round_grades S'.saved_grades r) .g2 =
      .computed (some g₄) := by
    unfold Spec.Protocol.saved_round_grades
    rw [if_pos hcr.symm]
    exact hg₄
  have k := (NoRaise.update_grades_pending_iff hS').2.2.1
  have hc1 := k.mp (by rw [hg₄]; simp)
  have hne : res (Spec.Protocol.saved_round_grades
      (Spec.Protocol.advance_to_round (W i v).val.st.saved_grades
        ((Spec.Config.toSpec S.E S.hc unreadHeightConfig).round_of
          ((Spec.Config.toSpec S.E S.hc unreadHeightConfig).slotOf
            ((Model.spec (V := V)).a S.hc S.E.Δ r)))) r) .g2 ≠ .pending := by
    unfold Spec.Protocol.saved_round_grades
    rw [if_pos (by rw [NoRaise.advance_to_round_round, hra])]
    exact hc1
  have hkept := update_grades_kept hS' r .g2 hne
  have hkept' : res (Spec.Protocol.saved_round_grades S'.saved_grades r) .g2 =
      Spec.Protocol.make_result_compatible_with (W i v).val.st.F
        (res (Spec.Protocol.saved_round_grades (W i v).val.st.saved_grades r) .g2) := by
    have e := hkept
    rw [hra, srg_advance_self] at e
    exact e
  rw [hsrg'] at hkept'
  obtain ⟨g₅, hg₅, rfl⟩ := mrc_some hkept'.symm
  have hph : (Model.spec (V := V)).phaseResult
      ((Model.spec (V := V)).cacheAtRound (W i v).cache r) .g2 = some (some g₅.toProof) := by
    show (res (Spec.Protocol.saved_round_grades (W i v).val.st.saved_grades r)
      .g2).toProof = _
    rw [hg₅]
    rfl
  rcases origin_of_path S rho W h0 i hstep v r .g2 _ hph with ⟨-, hnone⟩ | ⟨j, t, hj, he, ht, hr⟩
  · cases hnone
  subst ht
  obtain ⟨Gf, hGf⟩ := NoRaise.freezeRoot_ok (Spec.Provisional.toSpec S.E)
    ((Model.spec (V := V)).gradeView
      ((Model.spec (V := V)).toHealing (W j v).st.core)).property.2.1
    ((Model.spec (V := V)).gradeView
      ((Model.spec (V := V)).toHealing (W j v).st.core)).property.1
    (((Model.spec (V := V)).gradeView
      ((Model.spec (V := V)).toHealing (W j v).st.core)).val.blockOfImage (W j v).st.core.F)
    S.hc.η_SG r ((Model.spec (V := V)).early S.E S.hc r .g2)
    ((Model.spec (V := V)).late S.E S.hc r .g2)
  have hfr0 : (Model.spec (V := V)).freezeRoot S.E
      ((Model.spec (V := V)).gradeView ((Model.spec (V := V)).toHealing (W j v).st.core))
      (W j v).st.core.F S.hc.η_SG r
      ((Model.spec (V := V)).early S.E S.hc r .g2)
      ((Model.spec (V := V)).late S.E S.hc r .g2) ⇢ Gf.map Spec.Block.toProof :=
    (returns_successOutcomes _ _).mpr (by rw [hGf]; rfl)
  have hroot := hr _ hfr0
  cases Gf with
  | none => cases hroot
  | some raw' =>
    have hclip : g₅.toProof = (Model.spec (V := V)).clipGrade raw'.toProof
        (W i v).st.core.F := Option.some.inj hroot
    refine ⟨j, raw'.toProof, hj, he, fun fr hfr => ?_, ?_⟩
    · have e := (returns_successOutcomes _ _).mp hfr
      rw [hGf] at e
      exact (Except.ok.inj e).symm
    · have h1 : Block.Preceq q'.toProof G.toProof :=
        Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mp
          (Spec.Block.toProof_preceq_of_ancestorEq _ _ hqG)
      have h2 : Block.Preceq (Spec.Protocol.deepest_compatible_ancestor g₅
          (W i v).val.st.F).toProof g₅.toProof :=
        Proofs.ModelProperties.preceq_eq_true_iff_Preceq.mp
          (Spec.Block.toProof_preceq_of_ancestorEq _ _ (dca_ancestorEq _ _))
      have h3 : Block.Preceq g₅.toProof raw'.toProof := by
        rw [hclip]
        exact GradesFacts.spec_q10_clip_preceq _ _
      exact Proofs.ModelProperties.Preceq_trans h1
        (Proofs.ModelProperties.Preceq_trans hGg₄ (Proofs.ModelProperties.Preceq_trans h2 h3))

/-- The field `q2_capture_at_action_read_along` of `GradesRunFacts` at `Model.spec`: on every
    path `W` of `rho`, if the grade-2 block read after the phase tick at round `r`'s action instant
    can be `some q`, then some event `j` before event `i` is `v`'s tick at `domain r .g2`, every
    outcome of the G2 root frozen from `v`'s store in `W j` is `some raw`, and `q` is an ancestor of
    `raw`. -/
theorem spec_q2_capture_at_action_read_along : ∀ (S : Setup V) (rho : Record.Run V)
    (W : Nat → V → (Model.spec (V := V)).N),
    (∀ i : Nat, W i ∈ stateBeforeOf (Model.spec (V := V)) S rho i ∧
      W (i + 1) ∈ ((rho.events.drop i).take (i + 1 - i)).foldlM
        (worldStepOf (Model.spec (V := V)) S) (W i)) →
    ∀ (i : Nat) (v : V) (r : Round) (q : DecoupledConsensusModel.Block V),
    ∀ (c : (Model.spec (V := V)).Cache), (Model.spec (V := V)).onPhaseTick S.E S.hc
      (W i v).st.core.toHealing ((Model.spec (V := V)).a S.hc S.E.Δ r) (W i v).cache ⇢ c →
    ∀ (st : (Model.spec (V := V)).NS), (Model.spec (V := V)).duties_update_confirmation_with
      ((Model.spec (V := V)).gradeContract c) S.E S.hc
      ((Model.spec (V := V)).ns_setClock S.E (W i v).st ((Model.spec (V := V)).a S.hc S.E.Δ r))
      (S.E.slotOf ((Model.spec (V := V)).a S.hc S.E.Δ r) - 1) ⇢ st →
    (Model.spec (V := V)).grade2_block_with
      ((Model.spec (V := V)).gradeContract
        ((Model.spec (V := V)).mkNode st (W i v).record c).cache) S.E S.hc
      ((Model.spec (V := V)).toHealing
        ((Model.spec (V := V)).mkNode st (W i v).record c).st.core) r ⇢ some q →
    ∃ (j : Nat) (raw : DecoupledConsensusModel.Block V),
      j < i ∧
      rho.events[j]? = some (.tick v ((Model.spec (V := V)).domain S.E S.hc r .g2)) ∧
      (∀ fr : Option (DecoupledConsensusModel.Block V), (Model.spec (V := V)).freezeRoot S.E
        ((Model.spec (V := V)).gradeView ((Model.spec (V := V)).toHealing (W j v).st.core))
        (W j v).st.core.F S.hc.η_SG r
        ((Model.spec (V := V)).early S.E S.hc r .g2)
        ((Model.spec (V := V)).late S.E S.hc r .g2) ⇢ fr → fr = some raw) ∧
      Block.Preceq q raw := by
  intro S rho W hW i v r q c hc st _ hq
  have h0 : W 0 = fun u => (Model.spec (V := V)).initial S u := (hW 0).1
  have hstep : ∀ k < i, W (k + 1) ∈ ((rho.events.drop k).take 1).foldlM
      (worldStepOf (Model.spec (V := V)) S) (W k) := fun k _ => by
    have := (hW k).2
    rwa [Nat.add_sub_cancel_left] at this
  exact q2_of_path S rho W h0 i hstep v r q c hc st hq

/-- The field `q2_capture_at_action_read` of `GradesRunFacts` at `Model.spec`: for a world `w₁`
    before event `i`, if the grade-2 block read after the phase tick at round `r`'s action instant
    can be `q`, then some event `j` before event `i` is `v`'s tick at `domain r .g2`, and in some
    world before event `j` that leads to `w₁` every outcome of the G2 root frozen from `v`'s store
    is `some raw`, with `q` an ancestor of `raw`. -/
theorem spec_q2_capture_at_action_read : ∀ (S : Setup V) (rho : Record.Run V) (i : Nat)
    (v : V) (r : Round) (q : DecoupledConsensusModel.Block V),
    ∀ w₁ ∈ stateBeforeOf (Model.spec (V := V)) S rho i,
    ∀ (c : (Model.spec (V := V)).Cache), (Model.spec (V := V)).onPhaseTick S.E S.hc
      (w₁ v).st.core.toHealing ((Model.spec (V := V)).a S.hc S.E.Δ r) (w₁ v).cache ⇢ c →
    ∀ (st : (Model.spec (V := V)).NS), (Model.spec (V := V)).duties_update_confirmation_with
      ((Model.spec (V := V)).gradeContract c) S.E S.hc
      ((Model.spec (V := V)).ns_setClock S.E (w₁ v).st ((Model.spec (V := V)).a S.hc S.E.Δ r))
      (S.E.slotOf ((Model.spec (V := V)).a S.hc S.E.Δ r) - 1) ⇢ st →
    (Model.spec (V := V)).grade2_block_with
      ((Model.spec (V := V)).gradeContract
        ((Model.spec (V := V)).mkNode st (w₁ v).record c).cache) S.E S.hc
      ((Model.spec (V := V)).toHealing
        ((Model.spec (V := V)).mkNode st (w₁ v).record c).st.core) r ⇢ some q →
    ∃ (j : Nat) (raw : DecoupledConsensusModel.Block V),
      j < i ∧
      rho.events[j]? = some (.tick v ((Model.spec (V := V)).domain S.E S.hc r .g2)) ∧
      ∃ w ∈ stateBeforeOf (Model.spec (V := V)) S rho j,
      w₁ ∈ ((rho.events.drop j).take (i - j)).foldlM (worldStepOf (Model.spec (V := V)) S) w ∧
      (∀ fr : Option (DecoupledConsensusModel.Block V), (Model.spec (V := V)).freezeRoot S.E
        ((Model.spec (V := V)).gradeView ((Model.spec (V := V)).toHealing (w v).st.core))
        (w v).st.core.F S.hc.η_SG r
        ((Model.spec (V := V)).early S.E S.hc r .g2)
        ((Model.spec (V := V)).late S.E S.hc r .g2) ⇢ fr → fr = some raw) ∧
      Block.Preceq q raw := by
  intro S rho i v r q w₁ hw₁ c hc st _ hq
  obtain ⟨W, h0, hi, hstep⟩ := path_of_fold S rho.events i _ w₁ hw₁
  subst hi
  obtain ⟨j, raw, hj, he, hfr, hqr⟩ := q2_of_path S rho W h0 i hstep v r q c hc st hq
  exact ⟨j, raw, hj, he, W j, path_stateBefore S rho W h0 i hstep j hj.le,
    path_segment S rho W i hstep j i hj.le le_rfl, hfr, hqr⟩

end SpecRecord.GradesRunFacts

/-! ## The bundle -/

namespace DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-- Every field of `GradesRunFacts` holds at `Model.spec`. -/
theorem Model.spec_runFacts_grades : GradesRunFacts (Model.spec (V := V)) where
  completed_phase_origin := SpecRecord.GradesRunFacts.spec_completed_phase_origin
  phaseResult_initial_some := SpecRecord.GradesRunFacts.spec_phaseResult_initial_some
  q2_capture_at_action_read := SpecRecord.GradesRunFacts.spec_q2_capture_at_action_read
  frame_phase_prepared_eq_of_outcomes :=
    SpecRecord.GradesRunFacts.spec_frame_phase_prepared_eq_of_outcomes
  completed_phase_origin_along :=
    SpecRecord.GradesRunFacts.spec_completed_phase_origin_along
  q2_capture_at_action_read_along :=
    SpecRecord.GradesRunFacts.spec_q2_capture_at_action_read_along

end DecoupledConsensusModel.Sts.Record
