import Proofs.Instance.Model
import Proofs.Instance.Facts.Remaining
import Proofs.Instance.Facts.GradesRun
import Proofs.Instance.Facts.Schedule
import Proofs.Instance.Equalities.Fill

/-!
# The cache update's grades and the tick's confirmation records

Proofs, at `Model.specDraft`, of four fields of `GradesFacts` about the cache update `onPhaseTick`
and two fields of `NodeFacts` about the tick at a slot's support cutoff.
-/

set_option autoImplicit false

namespace SpecDraftRecord.GradesReached

open DecoupledConsensusModel DecoupledConsensusModel.Sts DecoupledConsensusModel.Sts.Record
open SpecDraftRecord SpecDraftRecord.RemainingKit SpecDraftRecord.GradesFacts
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

omit [DecidableEq V] [Fintype V] [Inhabited V] in
/-- Bringing the saved grades to their own round or the next keeps the grades of that round. -/
theorem srg_advance_of_round {c : Spec.SavedGrades V} {ρ r : Round}
    (hr : (ρ = c.round ∧ (r = c.round ∨ r = c.round + 1)) ∨ (ρ = c.round + 1 ∧ r = c.round + 1)) :
    Spec.Protocol.saved_round_grades (Spec.Protocol.advance_to_round c ρ) r =
      Spec.Protocol.saved_round_grades c r := by
  rcases hr with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp [Spec.Protocol.advance_to_round, Spec.Protocol.saved_round_grades]

omit [DecidableEq V] [Fintype V] [Inhabited V] in
/-- A computed block of the grades of any round, read from saved grades whose blocks are tree
    blocks, is a tree block. -/
theorem mem_of_inTree {T : Finset (Spec.Block V)} {c : Spec.SavedGrades V}
    (hin : Spec.Store.ContractInTree T c) {r : Round} {q : Spec.Protocol.Phase}
    {x : Spec.Block V}
    (h : Spec.Protocol.phaseResult (Spec.Protocol.saved_round_grades c r) q =
      .computed (some x)) : x ∈ T := by
  unfold Spec.Protocol.saved_round_grades at h
  split_ifs at h
  · exact hin c.current (by simp) _ (by cases q <;> simp [Spec.Protocol.phaseResult] at h ⊢ ) x h
  · exact hin c.next (by simp) _ (by cases q <;> simp [Spec.Protocol.phaseResult] at h ⊢ ) x h
  · cases q <;> simp [Spec.Protocol.phaseResult, Spec.Protocol.pending_round_grades] at h

/-- `phaseResult_onPhaseTick_kept` holds when every block the cache holds is a tree block. -/
theorem kept_of_inTree : ∀ (E : Env V) (hc : Protocol.HealConfig) (st : (Model.specDraft (V := V)).HS) (t : Int) (c : (Model.specDraft (V := V)).Cache)
    (hin : Spec.Store.ContractInTree st.val.T c) {r : Round} {p : Protocol.Phase} {e : Block V} (h : (Model.specDraft (V := V)).phaseResult ((Model.specDraft (V := V)).cacheAtRound c r) p = some (some e)) (hr : (((Model.specDraft (V := V)).round_of hc (E.slotOf t)) = c.round ∧ (r = c.round ∨ r = c.round + 1)) ∨
    (((Model.specDraft (V := V)).round_of hc (E.slotOf t)) = c.round + 1 ∧ r = c.round + 1)) (c' : (Model.specDraft (V := V)).Cache), (Model.specDraft (V := V)).onPhaseTick E hc st t c ⇢ c' → (Model.specDraft (V := V)).phaseResult ((Model.specDraft (V := V)).cacheAtRound c' r) p
    = some (some ((Model.specDraft (V := V)).clipGrade e st.toFG.F)) := by
  intro E hc st t c hin r p e h hr c' hc'
  obtain ⟨S, hS, rfl, hρ⟩ := sd_onPhaseTick_ok hc'
  rw [← hρ] at hr
  have hA := srg_advance_of_round hr
  change (Spec.Protocol.phaseResult (Spec.Protocol.saved_round_grades c r)
    (Spec.Protocol.Phase.toSpec p)).toProof = some (some e) at h
  generalize hR : Spec.Protocol.phaseResult (Spec.Protocol.saved_round_grades c r)
    (Spec.Protocol.Phase.toSpec p) = R at h
  rcases R with _ | _ | x
  · cases h
  · cases h
  obtain rfl := Option.some.inj (Option.some.inj h)
  have hx := mem_of_inTree hin hR
  show (Spec.Protocol.phaseResult (Spec.Protocol.saved_round_grades
    S.saved_grades r) (Spec.Protocol.Phase.toSpec p)).toProof = _
  rcases tick_slot hS r p with k | ⟨hp, -⟩
  · rw [k, hA, hR, toProof_mrcw_some, toProof_dca_of_mem st.property hx]
    rfl
  · rw [hA, hR] at hp; cases hp

/-- `onPhaseTick_phase_of_align` holds when every block the cache holds is a tree block. -/
theorem phase_of_align_of_inTree : ∀ (E : DecoupledConsensusModel.Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig) (st : (Model.specDraft (V := V)).HS) (t : DecoupledConsensusModel.Time) (c : (Model.specDraft (V := V)).Cache)
    (hin : Spec.Store.ContractInTree st.val.T c) (r : DecoupledConsensusModel.Round) (p : DecoupledConsensusModel.Protocol.Phase), (Model.specDraft (V := V)).phaseResult ((Model.specDraft (V := V)).cacheAtRound ((Model.specDraft (V := V)).alignRound c (((Model.specDraft (V := V)).round_of hc (E.slotOf t)))) r) p ≠ Option.none → ∀ c'' : (Model.specDraft (V := V)).Cache, (Model.specDraft (V := V)).onPhaseTick E hc st t c ⇢ c'' → (Model.specDraft (V := V)).phaseResult ((Model.specDraft (V := V)).cacheAtRound c'' r) p = (Model.specDraft (V := V)).clipResult st.toFG.F ((Model.specDraft (V := V)).phaseResult ((Model.specDraft (V := V)).cacheAtRound ((Model.specDraft (V := V)).alignRound c (((Model.specDraft (V := V)).round_of hc (E.slotOf t)))) r) p) := by
  intro E hc st t c hin r p hne c'' hc''
  obtain ⟨S, hS, rfl, hρ⟩ := sd_onPhaseTick_ok hc''
  rw [← hρ] at hne ⊢
  have hne' : Spec.Protocol.phaseResult (Spec.Protocol.saved_round_grades
      (Spec.Protocol.advance_to_round c
        (NoRaise.roundAt (Spec.Config.toSpec E hc unreadHeightConfig) t)) r)
      (Spec.Protocol.Phase.toSpec p) ≠ .pending := (sd_phaseResult_ne_none _ _).1 hne
  show (Spec.Protocol.phaseResult (Spec.Protocol.saved_round_grades
    S.saved_grades r) (Spec.Protocol.Phase.toSpec p)).toProof = _
  rcases tick_slot hS r p with k | ⟨hp, -⟩
  swap
  · exact absurd hp hne'
  rw [k]
  have hv := srg_advance_value hne'
  change _ = Member.clipResult st.val.F.toProof (Spec.Protocol.phaseResult
    (Spec.Protocol.saved_round_grades (Spec.Protocol.advance_to_round c
      (NoRaise.roundAt (Spec.Config.toSpec E hc unreadHeightConfig) t)) r)
      (Spec.Protocol.Phase.toSpec p)).toProof
  revert hne' hv
  generalize Spec.Protocol.phaseResult (Spec.Protocol.saved_round_grades
    (Spec.Protocol.advance_to_round c
      (NoRaise.roundAt (Spec.Config.toSpec E hc unreadHeightConfig) t)) r)
      (Spec.Protocol.Phase.toSpec p) = R
  intro hne' hv
  rcases R with _ | _ | x
  · exact absurd rfl hne'
  · rfl
  · rw [toProof_mrcw_some, toProof_dca_of_mem st.property (mem_of_inTree hin hv.symm)]
    rfl

/-- A time one delay before round `ρ` opens, when it is not negative, is not in round `ρ`. -/
theorem round_of_before_opening (C : Spec.Config) (ρ : Round)
    (h0 : 0 ≤ C.opening ρ - C.Δ) : C.round_of (C.slotOf (C.opening ρ - C.Δ)) ≠ ρ := by
  have hΔ := C.Δ_pos
  have hR : 0 < C.R := by have := C.R_ge_three; omega
  have hρ : 1 ≤ ρ * C.R := by
    rcases Nat.eq_zero_or_pos ρ with e | e
    · subst e; simp [Spec.Config.opening, Spec.Config.proposal_time] at h0; time_omega
    · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hs : C.slotOf (C.opening ρ - C.Δ) = ρ * C.R - 1 := by
    apply NodeFacts.slotOf_of_bounds
    · simp only [Spec.Config.opening, Spec.Config.proposal_time]
      rw [Nat.cast_sub hρ]; push_cast; nlinarith
    · simp only [Spec.Config.opening, Spec.Config.proposal_time]
      rw [Nat.cast_sub hρ]; push_cast; nlinarith
  rw [hs]
  simp only [Spec.Config.round_of]
  have : (ρ * C.R - 1) / C.R < ρ := (Nat.div_lt_iff_lt_mul hR).mpr (Nat.sub_lt hρ Nat.one_pos)
  exact Nat.ne_of_lt this

/-- `phaseResult_onPhaseTick_domain_ne_none` holds at times that are not negative. -/
theorem domain_ne_none_of_nonneg : ∀ (E : Env V) (hc : Protocol.HealConfig) (st : (Model.specDraft (V := V)).HS) (t : Int) (c : (Model.specDraft (V := V)).Cache)
    (ht0 : 0 ≤ t) {r : Round} {p : Protocol.Phase} (hr : r = ((Model.specDraft (V := V)).round_of hc (E.slotOf t)) ∨ r = ((Model.specDraft (V := V)).round_of hc (E.slotOf t)) + 1) (ht : t = (Model.specDraft (V := V)).domain E hc r p) (c' : (Model.specDraft (V := V)).Cache), (Model.specDraft (V := V)).onPhaseTick E hc st t c ⇢ c' → (Model.specDraft (V := V)).phaseResult ((Model.specDraft (V := V)).cacheAtRound c' r) p ≠ none := by
  intro E hc st t c ht0 r p hr ht c' hc'
  change t = Member.domain E hc r p at ht
  obtain ⟨S, hS, rfl, hρ⟩ := sd_onPhaseTick_ok hc'
  rw [← hρ] at hr
  rw [sd_phaseResult_ne_none]
  have k := NoRaise.update_grades_pending_iff hS
  have kr := (NoRaise.update_grades_results hS).1
  obtain ⟨⟨-, -, d0⟩, ⟨-, -, d1⟩, ⟨-, -, d2⟩⟩ := cutoffs E hc r
  have hd : ∀ j : Int, 0 ≤ j → j < 4 → t = (Spec.Config.toSpec E hc unreadHeightConfig).opening r +
      j * (Spec.Config.toSpec E hc unreadHeightConfig).Δ →
      NoRaise.roundAt (Spec.Config.toSpec E hc unreadHeightConfig) t = r := by
    intro j hj0 hj e; rw [e]; exact round_of_opening_add _ r hj0 hj
  change Spec.Protocol.phaseResult (Spec.Protocol.saved_round_grades
    S.saved_grades r) (Spec.Protocol.Phase.toSpec p) ≠ _
  unfold Spec.Protocol.saved_round_grades
  rw [kr]
  rcases hr with rfl | rfl <;> rcases p with _ | _ | _ <;>
    simp only [Spec.Protocol.phaseResult, Spec.Protocol.Phase.toSpec,
      if_true, if_false, reduceCtorEq, Nat.succ_ne_self, ne_eq]
  · exact k.1.2 (Or.inr (ht.trans (d0.trans (by ring))))
  · exact k.2.1.2 (Or.inr (ht.trans d1))
  · have e := ht.trans d2
    exact (round_of_before_opening _ _ (e ▸ ht0) (by rw [← e])).elim
  · exact absurd (hd 1 (by norm_num) (by norm_num) (ht.trans (d0.trans (by ring)))) (Nat.succ_ne_self _).symm
  · exact absurd (hd 0 le_rfl (by norm_num) (ht.trans (d1.trans (by ring)))) (Nat.succ_ne_self _).symm
  · exact k.2.2.2.2.2.2 (Or.inr (ht.trans d2))

/-- `phaseResult_onPhaseTick_domain_current` holds at times that are not negative. -/
theorem domain_current_of_nonneg : ∀ (E : Env V) (hc : Protocol.HealConfig) (st : (Model.specDraft (V := V)).HS) (t : Int) (c : (Model.specDraft (V := V)).Cache)
    (ht0 : 0 ≤ t) {r : Round} {p : Protocol.Phase} (hρ : ((Model.specDraft (V := V)).round_of hc (E.slotOf t)) = r) (ht : t = (Model.specDraft (V := V)).domain E hc r p) (h : (Model.specDraft (V := V)).phaseResult ((Model.specDraft (V := V)).cacheAtRound c r) p = none)
    (c' : (Model.specDraft (V := V)).Cache) (hc' : (Model.specDraft (V := V)).onPhaseTick E hc st t c ⇢ c')
    (fr : Option (Block V)) (hfr : (Model.specDraft (V := V)).freezeRoot E ((Model.specDraft (V := V)).gradeView st) st.toFG.F hc.η_SG r ((Model.specDraft (V := V)).early E hc r p)
    ((Model.specDraft (V := V)).late E hc r p) ⇢ fr), (Model.specDraft (V := V)).phaseResult ((Model.specDraft (V := V)).cacheAtRound c' r) p
    = some (fr.map (fun B => (Model.specDraft (V := V)).clipGrade B st.toFG.F)) := by
  intro E hc st t c ht0 r p hρ ht h c' hc' fr hfr
  change t = Member.domain E hc r p at ht
  change (Model.specDraft (V := V)).freezeRoot E ((Model.specDraft (V := V)).gradeView st)
    st.toFG.F hc.η_SG r (Member.early E hc r p) (Member.late E hc r p) ⇢ fr at hfr
  obtain ⟨S, hS, rfl, hρ'⟩ := sd_onPhaseTick_ok hc'
  have hr : (Spec.Config.toSpec E hc unreadHeightConfig).round_of
      ((Spec.Config.toSpec E hc unreadHeightConfig).slotOf t) = r := by
    rw [← hρ, ← hρ']
  obtain ⟨⟨e0, l0, d0⟩, ⟨e1, l1, d1⟩, ⟨-, -, d2⟩⟩ := cutoffs E hc r
  obtain ⟨X, hX, hXr, -, -, -, k0, k1, -⟩ := update_grades_value hS rfl rfl
  have hAr := NoRaise.advance_to_round_round c ((Spec.Config.toSpec E hc
    unreadHeightConfig).round_of ((Spec.Config.toSpec E hc unreadHeightConfig).slotOf t))
  have hpc : Spec.Protocol.phaseResult (Spec.Protocol.saved_round_grades c r)
      (Spec.Protocol.Phase.toSpec p) = .pending :=
    Spec.GradeResult.toProof_eq_none.mp h
  subst hr
  have hpA : Spec.Protocol.phaseResult (Spec.Protocol.advance_to_round c
      ((Spec.Config.toSpec E hc unreadHeightConfig).round_of
        ((Spec.Config.toSpec E hc unreadHeightConfig).slotOf t))).current
      (Spec.Protocol.Phase.toSpec p) = .pending := by
    by_contra hne
    refine NoRaise.srg_advance_ne_pending_rev (ρ := (Spec.Config.toSpec E hc
      unreadHeightConfig).round_of ((Spec.Config.toSpec E hc unreadHeightConfig).slotOf
        t)) ?_ hpc
    unfold Spec.Protocol.saved_round_grades
    rw [hAr, if_pos rfl]
    exact hne
  show (Spec.Protocol.phaseResult (Spec.Protocol.saved_round_grades
    S.saved_grades _) (Spec.Protocol.Phase.toSpec p)).toProof = _
  rw [hX]
  unfold Spec.Protocol.saved_round_grades
  simp only [Spec.Protocol.make_saved_grades_compatible_with, hXr, hAr, if_true]
  rcases p with _ | _ | _
  · rcases k0 with ⟨-, hn⟩ | ⟨-, -, sg, G, hG, e⟩
    · exact absurd ⟨ht.trans d0, hpA⟩ hn
    have hfr2 := hfr
    rw [e0, l0] at hfr2
    obtain rfl := freezeRoot_unique hfr2 (freezeRoot_of_graded_block hG)
    simp only [Spec.Protocol.phaseResult, Spec.Protocol.Phase.toSpec,
      Spec.Protocol.make_round_grades_compatible_with, e, if_true]
    rcases G with _ | x
    · rfl
    · rw [toProof_mrcw_some]
      exact congrArg (fun y => some (some y)) (toProof_dca_of_mem st.property (mem_T_of_freezeRoot hG))
  · rcases k1 with ⟨-, hn⟩ | ⟨-, -, sg, G, hG, e⟩
    · exact absurd ⟨ht.trans d1, hpA⟩ hn
    have hfr2 := hfr
    rw [e1, l1] at hfr2
    obtain rfl := freezeRoot_unique hfr2 (freezeRoot_of_graded_block hG)
    simp only [Spec.Protocol.phaseResult, Spec.Protocol.Phase.toSpec,
      Spec.Protocol.make_round_grades_compatible_with, e, if_true, if_false, reduceCtorEq]
    rcases G with _ | x
    · rfl
    · rw [toProof_mrcw_some]
      exact congrArg (fun y => some (some y)) (toProof_dca_of_mem st.property (mem_T_of_freezeRoot hG))
  · have e := ht.trans d2
    exact (round_of_before_opening _ _ (e ▸ ht0) (by rw [← e])).elim

end SpecDraftRecord.GradesReached

/-! ## The tick at a support cutoff -/

namespace SpecDraftRecord.GradesReached

open DecoupledConsensusModel
open DecoupledConsensusModel.Sts
open DecoupledConsensusModel.Sts.Record
open DecoupledConsensusModel.Execution
open SpecDraftRecord.NoRaise
open SpecDraftRecord.GradesRunFacts
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

omit [DecidableEq V] [Fintype V] [Inhabited V] in
/-- If the saved grades `c` hold blocks of `T` only, every result they hold is a block of `T` or
    none. -/
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

omit [Inhabited V] in
/-- A tick that runs the confirmation duty and neither the proposal nor the Goldfish vote duty
    returns the three confirmation records of `update_confirmation` run on the store the grades
    update leaves, with its clock and slot set to `t`. -/
theorem tick_confirmation {C : Spec.Config} {P : Spec.Provisional V}
    {X : Spec.External V} {n n' : Spec.NodeState V}
    {t : Spec.Time} {sent : List (Spec.NamedObject V)}
    (h : (Spec.tick C P X n t).run [] = .ok (n', sent))
    (hC : NodeFacts.condC C n t) (hP : ¬ NodeFacts.condP C P n t)
    (hV : ¬ NodeFacts.condV C n t) :
    ∃ st0 st4 : Spec.Store V,
      Spec.Protocol.update_grades C P n.st t = .ok st0 ∧
      Spec.Protocol.update_confirmation C { st0 with t := t, s := C.slotOf t }
        (C.slotOf t - 1) = .ok st4 ∧
      n'.st.live_confirmed = st4.live_confirmed ∧ n'.st.latest_stable = st4.latest_stable ∧
      n'.st.latest_confirmed = st4.latest_confirmed := by
  obtain ⟨st0, st2, st3, st4, st5, sh5, l1, l2, h0, -, hP0, -, hV0, hC1, -, hA1, hA0, rfl⟩ :=
    NodeFacts.tick_steps h
  have e2 := (hP0 hP).1
  have e3 := (hV0 hV).1
  have hU := hC1 hC
  rw [e3, e2] at hU
  refine ⟨st0, st4, h0, hU, ?_⟩
  have k : st5.live_confirmed = st4.live_confirmed ∧ st5.latest_stable = st4.latest_stable ∧
      st5.latest_confirmed = st4.latest_confirmed := by
    by_cases ha : NodeFacts.condA C n t
    · obtain ⟨row, -, rfl, -⟩ := hA1 ha
      obtain ⟨at', ts, e⟩ := NodeFacts.admit_attestation_frame C st4 row
      rw [e]
      exact ⟨rfl, rfl, rfl⟩
    · rw [(hA0 ha).1]
      exact ⟨rfl, rfl, rfl⟩
  exact k

end SpecDraftRecord.GradesReached

/-! ## The tick at a support cutoff against the confirmation members -/

namespace SpecDraftRecord.GradesReached

open DecoupledConsensusModel
open DecoupledConsensusModel.Sts
open DecoupledConsensusModel.Sts.Record
open DecoupledConsensusModel.Execution
open SpecDraftRecord.NoRaise
open SpecDraftRecord.GradesRunFacts
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-- At a reached node state `n`, a tick that runs the confirmation duty and neither the proposal nor
    the Goldfish vote duty holds the three confirmation records of `update_confirmation` as the
    confirmation members run it, on the saved grades `c` of an outcome of the cache update
    `onPhaseTick` at `t`. -/
theorem member_confirmation (S : Setup V) (v : V) (n : (Model.specDraft (V := V)).N) (t : Int)
    (hn : (Model.specDraft (V := V)).reachedNode n) {s : Slot} (hslot : S.E.slotOf t = s)
    (out : (Model.specDraft (V := V)).N × List (NamedObject V))
    (hout : (Model.specDraft (V := V)).tick S v n t ⇢ out)
    (c : (Model.specDraft (V := V)).Cache)
    (hc : (Model.specDraft (V := V)).onPhaseTick S.E S.hc n.st.core.toHealing t n.cache ⇢ c)
    (hC : NodeFacts.condC (Setup.toSpec S).C n.val t)
    (hP : ¬ NodeFacts.condP (Setup.toSpec S).C (Setup.toSpec S).P n.val t)
    (hV : ¬ NodeFacts.condV (Setup.toSpec S).C n.val t) :
    ∃ st4 : Spec.Store V,
      Spec.Protocol.update_confirmation
        (Spec.Config.toSpec S.E S.hc unreadHeightConfig)
        { (Spec.Store.ofImage (Member.ns_setClock S.E n.val.st t)) with
          saved_grades := Spec.Protocol.advance_to_round
            ((Member.ns_setClock S.E n.val.st t).contractOfImage c)
            ((Spec.Config.toSpec S.E S.hc unreadHeightConfig).round_of
              (Member.ns_setClock S.E n.val.st t).s) }
        (s - 1) = .ok st4 ∧
      out.1.val.st.live_confirmed = st4.live_confirmed ∧
      out.1.val.st.latest_stable = st4.latest_stable ∧
      out.1.val.st.latest_confirmed = st4.latest_confirmed := by
  obtain ⟨hinv, hconf, hcontract⟩ := reached_elim hn
  have hok : StoreOk n.val.st := n.property
  obtain ⟨sent, hrun, -⟩ := NodeFacts.tick_out S v n t out hout
  obtain ⟨st0, st4, h0, hU, e1, e2, e3⟩ := tick_confirmation hrun hC hP hV
  obtain ⟨S', hS', rfl, -⟩ := GradesFacts.sd_onPhaseTick_ok hc
  have hS'' : Spec.Protocol.update_grades (Setup.toSpec S).C (Setup.toSpec S).P
      n.val.st t = .ok S' := hS'
  rw [h0] at hS''
  obtain rfl : st0 = S' := Except.ok.inj hS''
  have hin : Spec.Store.ContractInTree n.val.st.T st0.saved_grades :=
    contractInTree_of_claim (memClaim_update_grades hok h0 (claim_of_contractInTree hcontract))
  have hofI : Spec.Store.ofImage (Member.ns_setClock S.E n.val.st t) =
      Member.ns_setClock S.E n.val.st t :=
    Spec.Store.ofImage_eq_self _ hok.2.1 hok.2.2.2 hinv.1 hconf.1 hconf.2.1 hconf.2.2
  have hcoi : (Member.ns_setClock S.E n.val.st t).contractOfImage st0.saved_grades =
      st0.saved_grades :=
    Spec.Store.contractOfImage_of_distinctRoots _ hok.2.1 hin
  have hround : (Spec.Config.toSpec S.E S.hc unreadHeightConfig).round_of
      (Member.ns_setClock S.E n.val.st t).s = st0.saved_grades.round :=
    (NodeFacts.update_grades_ok h0).2.symm
  have hadv : Spec.Protocol.advance_to_round st0.saved_grades
      ((Spec.Config.toSpec S.E S.hc unreadHeightConfig).round_of
        (Member.ns_setClock S.E n.val.st t).s) = st0.saved_grades := by
    rw [hround]
    unfold Spec.Protocol.advance_to_round
    rw [if_pos rfl]
  rw [hofI, hcoi, hadv]
  refine ⟨st4, ?_, e1, e2, e3⟩
  have e0 := (NodeFacts.update_grades_ok h0).1
  rw [e0] at hU
  have hU' : Spec.Protocol.update_confirmation
      (Spec.Config.toSpec S.E S.hc unreadHeightConfig)
      { (Member.ns_setClock S.E n.val.st t) with saved_grades := st0.saved_grades }
      ((Setup.toSpec S).C.slotOf t - 1) = .ok st4 := hU
  have hsl : (Setup.toSpec S).C.slotOf t = s :=
    (Spec.Config.toSpec_slotOf (E := S.E) (hc := S.hc) (cfg := S.cfg) t).trans hslot
  rw [hsl] at hU'
  exact hU'

/-- At a time `t` that is the support cutoff of a slot `s > 0` and neither its proposal time nor its
    Goldfish vote time, a node state that passes the grade-2 awake test of `s`'s round passes the
    tick's confirmation test and fails its proposal and vote tests. -/
theorem conds_of_support_cutoff (S : Setup V) (v : V) (n : (Model.specDraft (V := V)).N)
    (t : Int) (s : Slot) (hs : 0 < s) (hslot : S.E.slotOf t = s)
    (ht : t = (Model.specDraft (V := V)).support_cutoff S.E s)
    (hp : t ≠ (Model.specDraft (V := V)).proposal_time S.E s)
    (hv : t ≠ (Model.specDraft (V := V)).vote_time S.E s)
    (hrun : (Model.specDraft (V := V)).awake_for_grade2 (Setup.alwaysAwake S) v n
      ((Model.specDraft (V := V)).round_of S.hc s)) :
    NodeFacts.condC (Setup.toSpec S).C n.val t ∧
      ¬ NodeFacts.condP (Setup.toSpec S).C (Setup.toSpec S).P n.val t ∧
      ¬ NodeFacts.condV (Setup.toSpec S).C n.val t := by
  have hsl : (Setup.toSpec S).C.slotOf t = s :=
    (Spec.Config.toSpec_slotOf (E := S.E) (hc := S.hc) (cfg := S.cfg) t).trans hslot
  obtain ⟨a, ha, hle⟩ := hrun
  have haw : (Spec.record_awake n.val t).awake_since
      (Spec.grade2_window_start (Setup.toSpec S).C
        ((Setup.toSpec S).C.round_of ((Setup.toSpec S).C.slotOf t))) = true := by
    rw [hsl]
    exact (NodeFacts.record_awake_awake_since _ _ _).mpr (Or.inl ⟨a, ha, hle⟩)
  refine ⟨⟨by rw [hsl]; exact hs, ?_⟩, ?_, ?_⟩
  · simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨?_, haw⟩
    rw [hsl]
    exact ht
  · rintro ⟨-, h⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    rw [hsl] at h
    exact hp h.1.1
  · rintro ⟨-, h⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    rw [hsl] at h
    exact hv h.1

end SpecDraftRecord.GradesReached

namespace DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

open SpecDraftRecord
open DecoupledConsensusModel.Execution
open scoped DC

theorem _root_.SpecDraftRecord.NodeFacts.specDraft_on_tick_emit_confirmation_of_outcomes :
    ∀ (S : Setup V) (v : V) (n : (Model.specDraft (V := V)).N) (s : Slot) (hs : 0 < s)
      (out : (Model.specDraft (V := V)).N × List (NamedObject V)) (hout : (Model.specDraft (V := V)).tick S v n ((Model.specDraft (V := V)).support_cutoff S.E s) ⇢ out)
      (c : (Model.specDraft (V := V)).Cache) (hc : (Model.specDraft (V := V)).onPhaseTick S.E S.hc n.st.core.toHealing ((Model.specDraft (V := V)).support_cutoff S.E s) n.cache ⇢ c)
      (D : (Model.specDraft (V := V)).NS) (hD : (Model.specDraft (V := V)).duties_update_confirmation_with ((Model.specDraft (V := V)).gradeContract c) S.E S.hc
        ((Model.specDraft (V := V)).ns_setClock S.E n.st ((Model.specDraft (V := V)).support_cutoff S.E s)) (s - 1) ⇢ D)
      (hrun : (Model.specDraft (V := V)).awake_for_grade2 (Setup.alwaysAwake S) v n ((Model.specDraft (V := V)).round_of S.hc s))
      (hn : (Model.specDraft (V := V)).reachedNode n),
      out.1.st.core.live_confirmed = D.core.live_confirmed := by
  intro S v n s hs out hout c hc D hD hrun hn
  obtain ⟨hinv, hconf, hcontract⟩ := reached_elim hn
  have hsl := ScheduleFacts.specDraft_slotOf_support_cutoff (V := V) S.E s
  obtain ⟨hC, hP, hV⟩ := GradesReached.conds_of_support_cutoff S v n _ s hs hsl rfl
    (ScheduleFacts.specDraft_support_cutoff_ne_proposal_time S.E s)
    (ScheduleFacts.specDraft_support_cutoff_ne_vote_time S.E s) hrun
  obtain ⟨st4, hU, e1, -, -⟩ := GradesReached.member_confirmation S v n _ hn hsl out hout c hc hC hP hV
  have hD1 : Returns (Member.duties_update_confirmation_with c S.E S.hc
      (Member.ns_setClock S.E n.val.st ((Model.specDraft (V := V)).support_cutoff S.E s)) (s - 1))
      D.val := hD
  unfold Member.duties_update_confirmation_with at hD1
  rw [returns_successOutcomes, update_confirmation_fill_ok _ _ _ _ hU] at hD1
  have hD2 := Except.ok.inj hD1
  have k : D.val.live_confirmed = st4.live_confirmed := by rw [← hD2]
  exact congrArg Spec.Block.toProof (e1.trans k.symm)

theorem _root_.SpecDraftRecord.NodeFacts.specDraft_tick_records_at_confirmation_of_outcomes :
    ∀ (S : Setup V) (v : V) (n : (Model.specDraft (V := V)).N) (t : Int),
      0 < S.E.slotOf t → t ≠ (Model.specDraft (V := V)).proposal_time S.E (S.E.slotOf t) →
      t ≠ (Model.specDraft (V := V)).vote_time S.E (S.E.slotOf t) → t = (Model.specDraft (V := V)).support_cutoff S.E (S.E.slotOf t) →
      (Model.specDraft (V := V)).awake_for_grade2 (Setup.alwaysAwake S) v n ((Model.specDraft (V := V)).round_of S.hc (S.E.slotOf t)) →
      ∀ (out : (Model.specDraft (V := V)).N × List (NamedObject V)), (Model.specDraft (V := V)).tick S v n t ⇢ out →
      ∀ (c : (Model.specDraft (V := V)).Cache), (Model.specDraft (V := V)).onPhaseTick S.E S.hc n.st.core.toHealing t n.cache ⇢ c →
      ∀ (D : (Model.specDraft (V := V)).S), (Model.specDraft (V := V)).update_confirmation_with ((Model.specDraft (V := V)).gradeContract c) S.E S.hc
        ((Model.specDraft (V := V)).ns_setClock S.E n.st t).core (S.E.slotOf t - 1) ⇢ D →
      ∀ (hn : (Model.specDraft (V := V)).reachedNode n),
      out.1.st.core.latest_stable = D.latest_stable ∧
        out.1.st.core.latest_confirmed = D.latest_confirmed := by
  intro S v n t h₁ h₂ h₃ h₄ h₅ out h₆ c h₇ D h₈ hn
  obtain ⟨hinv, hconf, hcontract⟩ := reached_elim hn
  obtain ⟨hC, hP, hV⟩ := GradesReached.conds_of_support_cutoff S v n t _ h₁ rfl h₄ h₂ h₃ h₅
  obtain ⟨st4, hU, -, e2, e3⟩ := GradesReached.member_confirmation S v n t hn rfl out h₆ c h₇ hC hP hV
  have hD1 : Returns (Member.update_confirmation_with c S.E S.hc
      (Member.ns_setClock S.E n.val.st t) (S.E.slotOf t - 1)) D.val := h₈
  unfold Member.update_confirmation_with at hD1
  rw [returns_successOutcomes, update_confirmation_fill_ok _ _ _ _ hU] at hD1
  have hD2 := Except.ok.inj hD1
  have k2 : D.val.latest_stable = st4.latest_stable := by rw [← hD2]
  have k3 : D.val.latest_confirmed = st4.latest_confirmed := by rw [← hD2]
  exact ⟨congrArg Spec.Block.toProof (e2.trans k2.symm),
    congrArg Spec.Block.toProof (e3.trans k3.symm)⟩


open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Proofs.Engine
open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Protocol (HealConfig)
open Internal
open Internal.PhaseGrades DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol (Token Supports Opposes)
open DecoupledConsensusModel.Proofs.HealingLemmas
open Execution (Setup)
open Protocol (GradeView HealConfig)
open Protocol (SGVote)
open Execution
open DecoupledConsensusModel.Proofs.HealingSurface
open Protocol (HeightConfig)
open Protocol (own_lock)
open Internal.HealingSurface
open Proofs.HealingLemmas
open Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Statements.Instantiation
open Internal.NamedRecoveryRead
open DecoupledConsensusModel.Proofs.ModelProperties
open DecoupledConsensusModel.Proofs.NamedConfirmationMembership
open Protocol
open Execution Internal.NamedOutageEntry
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol
open Execution Internal.NamedOutageEntry DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol (Token Supports Opposes CleanFrom)
open Internal Execution Internal.PhaseGrades DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol (Token Supports Opposes)
open DecoupledConsensusModel.Proofs.NamedProposalParent
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Internal.HealingSurface
open DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Proofs.Optimistic
open DecoupledConsensusModel.Internal.NamedRecoveryRead
open DecoupledConsensusModel.Protocol (Token Supports Opposes CleanFrom)
open scoped DC

theorem _root_.SpecDraftRecord.GradesFacts.specDraft_phaseResult_onPhaseTick_kept :
    ∀ (E : Env V) (hc : Protocol.HealConfig) (st : (Model.specDraft (V := V)).HS) (t : Int) (c : (Model.specDraft (V := V)).Cache) {r : Round} {p : Protocol.Phase} {e : Block V} (h : (Model.specDraft (V := V)).phaseResult ((Model.specDraft (V := V)).cacheAtRound c r) p = some (some e)) (hr : (((Model.specDraft (V := V)).round_of hc (E.slotOf t)) = c.round ∧ (r = c.round ∨ r = c.round + 1)) ∨
      (((Model.specDraft (V := V)).round_of hc (E.slotOf t)) = c.round + 1 ∧ r = c.round + 1)) (c' : (Model.specDraft (V := V)).Cache), (Model.specDraft (V := V)).onPhaseTick E hc st t c ⇢ c' → ∀ (hn : (Model.specDraft (V := V)).reachedRead st c), (Model.specDraft (V := V)).phaseResult ((Model.specDraft (V := V)).cacheAtRound c' r) p
      = some (some ((Model.specDraft (V := V)).clipGrade e st.toFG.F)) := by
  intro E hc st t c r p e h hr c' h₁ hn
  obtain ⟨hinv, hconf, hcontract⟩ := reachedRead_elim hn
  exact GradesReached.kept_of_inTree E hc st t c hcontract h hr c' h₁

theorem _root_.SpecDraftRecord.GradesFacts.specDraft_onPhaseTick_phase_of_align :
    ∀ (E : DecoupledConsensusModel.Env V) (hc : DecoupledConsensusModel.Protocol.HealConfig) (st : (Model.specDraft (V := V)).HS) (t : DecoupledConsensusModel.Time) (c : (Model.specDraft (V := V)).Cache) (r : DecoupledConsensusModel.Round) (p : DecoupledConsensusModel.Protocol.Phase), (Model.specDraft (V := V)).phaseResult ((Model.specDraft (V := V)).cacheAtRound ((Model.specDraft (V := V)).alignRound c (((Model.specDraft (V := V)).round_of hc (E.slotOf t)))) r) p ≠ Option.none → ∀ c'' : (Model.specDraft (V := V)).Cache, (Model.specDraft (V := V)).onPhaseTick E hc st t c ⇢ c'' → ∀ (hn : (Model.specDraft (V := V)).reachedRead st c), (Model.specDraft (V := V)).phaseResult ((Model.specDraft (V := V)).cacheAtRound c'' r) p = (Model.specDraft (V := V)).clipResult st.toFG.F ((Model.specDraft (V := V)).phaseResult ((Model.specDraft (V := V)).cacheAtRound ((Model.specDraft (V := V)).alignRound c (((Model.specDraft (V := V)).round_of hc (E.slotOf t)))) r) p) := by
  intro E hc st t c r p h₁ c'' h₂ hn
  obtain ⟨hinv, hconf, hcontract⟩ := reachedRead_elim hn
  exact GradesReached.phase_of_align_of_inTree E hc st t c hcontract r p h₁ c'' h₂

theorem _root_.SpecDraftRecord.GradesFacts.specDraft_phaseResult_onPhaseTick_domain_current :
    ∀ (E : Env V) (hc : Protocol.HealConfig) (st : (Model.specDraft (V := V)).HS) (t : Int) (ht0 : 0 ≤ t) (c : (Model.specDraft (V := V)).Cache) {r : Round} {p : Protocol.Phase} (hρ : ((Model.specDraft (V := V)).round_of hc (E.slotOf t)) = r) (ht : t = (Model.specDraft (V := V)).domain E hc r p) (h : (Model.specDraft (V := V)).phaseResult ((Model.specDraft (V := V)).cacheAtRound c r) p = none)
      (c' : (Model.specDraft (V := V)).Cache) (hc' : (Model.specDraft (V := V)).onPhaseTick E hc st t c ⇢ c')
      (fr : Option (Block V)) (hfr : (Model.specDraft (V := V)).freezeRoot E ((Model.specDraft (V := V)).gradeView st) st.toFG.F hc.η_SG r ((Model.specDraft (V := V)).early E hc r p)
      ((Model.specDraft (V := V)).late E hc r p) ⇢ fr), (Model.specDraft (V := V)).phaseResult ((Model.specDraft (V := V)).cacheAtRound c' r) p
      = some (fr.map (fun B => (Model.specDraft (V := V)).clipGrade B st.toFG.F)) := by
  intro E hc st t ht0 c r p hρ ht h c' hc' fr hfr
  exact GradesReached.domain_current_of_nonneg E hc st t c ht0 hρ ht h c' hc' fr hfr

theorem _root_.SpecDraftRecord.GradesFacts.specDraft_phaseResult_onPhaseTick_domain_ne_none :
    ∀ (E : Env V) (hc : Protocol.HealConfig) (st : (Model.specDraft (V := V)).HS) (t : Int) (ht0 : 0 ≤ t) (c : (Model.specDraft (V := V)).Cache) {r : Round} {p : Protocol.Phase} (hr : r = ((Model.specDraft (V := V)).round_of hc (E.slotOf t)) ∨ r = ((Model.specDraft (V := V)).round_of hc (E.slotOf t)) + 1) (ht : t = (Model.specDraft (V := V)).domain E hc r p) (c' : (Model.specDraft (V := V)).Cache), (Model.specDraft (V := V)).onPhaseTick E hc st t c ⇢ c' → (Model.specDraft (V := V)).phaseResult ((Model.specDraft (V := V)).cacheAtRound c' r) p ≠ none := by
  intro E hc st t ht0 c r p hr ht c' h₁
  exact GradesReached.domain_ne_none_of_nonneg E hc st t c ht0 hr ht c' h₁

end DecoupledConsensusModel.Sts.Record
