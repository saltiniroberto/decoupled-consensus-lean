import Proofs.Instance.Model
import Proofs.Instance.Facts.GradesRun
import Proofs.Instance.Facts.NonEmpty

/-!
# The tick fields at `Model.spec`

Thirteen tick fields of `NodeFacts` proved at `Model.spec`, each assuming the node state runs
as the validator `v`. At each duty time the tick is shown to be the member duties of `S.node v`
followed by the clip of the saved grades, and each field is read off that.
-/

set_option autoImplicit false

namespace SpecRecord.TickReached

open DecoupledConsensusModel DecoupledConsensusModel.Execution DecoupledConsensusModel.Sts
open DecoupledConsensusModel.Sts.Record
open SpecRecord.NodeFacts
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

omit [Inhabited V] in
/-- The tick, step by step, with the run of each duty it takes. -/
theorem tick_detail {C : Spec.Config} {P : Spec.Provisional V}
    {X : Spec.External V} {n n' : Spec.NodeState V}
    {t : Spec.Time} {sent : List (Spec.NamedObject V)}
    (h : (Spec.tick C P X n t).run [] = .ok (n', sent)) :
    ∃ (st0 st2 st3 st4 st5 : Spec.Store V) (sh5 : Spec.SigningHistory)
      (l1 l2 : List (Spec.NamedObject V)),
      Spec.Protocol.update_grades C P n.st t = .ok st0 ∧
      (condP C P n t → (Spec.Protocol.propose_block C P X n.v
          { st0 with t := t, s := C.slotOf t }).run [] = .ok (st2, l1)) ∧
      (¬ condP C P n t → st2 = { st0 with t := t, s := C.slotOf t } ∧ l1 = []) ∧
      (condV C n t → (Spec.Protocol.goldfish_vote C P n.v st2).run l1 = .ok (st3, l2)) ∧
      (¬ condV C n t → st3 = st2 ∧ l2 = l1) ∧
      (condC C n t → Spec.Protocol.update_confirmation C st3 (C.slotOf t - 1) = .ok st4) ∧
      (¬ condC C n t → st4 = st3) ∧
      (condA C n t → (Spec.Protocol.attest C n.v st4 n.signingHistory).run l2 =
          .ok ((st5, sh5), sent)) ∧
      (¬ condA C n t → st5 = st4 ∧ sh5 = n.signingHistory ∧ sent = l2) ∧
      n' = { v := n.v, st := Spec.make_grades_compatible_with_finalized st5,
             signingHistory := sh5, awakeSince := (Spec.record_awake n t).awakeSince } := by
  unfold condP condV condC condA
  rw [tick_eq_tickChain] at h
  unfold tickChain at h
  dsimp only at h
  rw [run_bind_ok] at h
  obtain ⟨st0, l0, h0, h⟩ := h
  rw [liftM_run] at h0
  obtain ⟨h0, rfl⟩ := h0
  rw [run_bind_ok] at h
  obtain ⟨st2, l1, h1, h⟩ := h
  rw [run_bind_ok] at h
  obtain ⟨st3, l2, h2, h⟩ := h
  rw [run_bind_ok] at h
  obtain ⟨st4, l3, h3, h⟩ := h
  rw [run_bind_ok] at h
  obtain ⟨⟨st5, sh5⟩, l4, h4, h⟩ := h
  unfold optStep at h1 h2 h3 h4
  rw [pure_run] at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rw [record_awake_st] at h0
  simp only [record_awake_v, record_awake_sh] at h1 h2 h3 h4 ⊢
  have h3' : l3 = l2 := by
    split_ifs at h3
    · rw [liftM_run] at h3; exact h3.2
    · rw [pure_run] at h3; simp only [Prod.mk.injEq] at h3; exact h3.2
  subst h3'
  refine ⟨st0, st2, st3, st4, st5, sh5, l1, l3, h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · intro hc
    rw [if_pos hc] at h1
    exact h1
  · intro hc
    rw [if_neg hc, pure_run] at h1
    simp only [Prod.mk.injEq] at h1
    exact ⟨h1.1, h1.2⟩
  · intro hc
    rw [if_pos hc] at h2
    exact h2
  · intro hc
    rw [if_neg hc, pure_run] at h2
    simp only [Prod.mk.injEq] at h2
    exact ⟨h2.1, h2.2⟩
  · intro hc
    rw [if_pos hc, liftM_run] at h3
    exact h3.1
  · intro hc
    rw [if_neg hc, pure_run] at h3
    simp only [Prod.mk.injEq] at h3
    exact h3.1
  · intro hc
    rw [if_pos hc] at h4
    exact h4
  · intro hc
    rw [if_neg hc, pure_run] at h4
    simp only [Prod.mk.injEq] at h4
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h4
    exact ⟨rfl, rfl, rfl⟩

end SpecRecord.TickReached


namespace SpecRecord.TickReached

open DecoupledConsensusModel DecoupledConsensusModel.Execution DecoupledConsensusModel.Sts
open DecoupledConsensusModel.Sts.Record
open SpecRecord.NodeFacts SpecRecord.NoRaise
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-!
## Which of the tick's tests can hold together

The proposal, the vote, the confirmation and the attestation fall at `0`, `1`, `2` and `6` delays
into a slot or a round: the proposal and the vote never fall with another duty, and the attestation
always falls with the confirmation.
-/

/-- Two schedule instants `4 Δ a + k Δ` and `4 Δ b + k' Δ` with `k − k'` not a multiple of `4`
differ. -/
theorem sched_ne {Δ : Int} (hΔ : 0 < Δ) (a b k : Int) (hk : ¬ (4 : Int) ∣ k) :
    4 * Δ * a ≠ 4 * Δ * b + k * Δ := by
  intro h
  have h2 : Δ * (4 * (a - b) - k) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · omega
  · omega

omit [Inhabited V] in
/-- The proposal test holds only at the proposal time `4 Δ s` of the slot `s` of `t`. -/
theorem condP_time {C : Spec.Config} {P : Spec.Provisional V}
    {n : Spec.NodeState V} {t : Spec.Time} (h : condP C P n t) :
    t = 4 * C.Δ * ((C.slotOf t : Nat) : Int) := by
  obtain ⟨-, h⟩ := h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1

omit [DecidableEq V] [Fintype V] [Inhabited V] in
theorem condV_time {C : Spec.Config} {n : Spec.NodeState V}
    {t : Spec.Time} (h : condV C n t) :
    t = 4 * C.Δ * ((C.slotOf t : Nat) : Int) + 1 * C.Δ := by
  obtain ⟨-, h⟩ := h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  have e := h.1
  simp only [Spec.Config.vote_time, Spec.Config.proposal_time] at e
  linarith

omit [DecidableEq V] [Fintype V] [Inhabited V] in
theorem condC_time {C : Spec.Config} {n : Spec.NodeState V}
    {t : Spec.Time} (h : condC C n t) :
    t = 4 * C.Δ * ((C.slotOf t : Nat) : Int) + 2 * C.Δ := by
  obtain ⟨-, h⟩ := h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  have e := h.1
  simp only [Spec.Config.gf_confirmation_time, Spec.Config.proposal_time] at e
  linarith

omit [DecidableEq V] [Fintype V] [Inhabited V] in
theorem condA_time {C : Spec.Config} {n : Spec.NodeState V}
    {t : Spec.Time} (h : condA C n t) :
    t = 4 * C.Δ * (((C.round_of (C.slotOf t) * C.R : Nat)) : Int) + 6 * C.Δ := by
  simp only [condA, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

omit [Inhabited V] in
theorem condP_not_condV {C : Spec.Config} {P : Spec.Provisional V}
    {n : Spec.NodeState V} {t : Spec.Time} (h : condP C P n t) :
    ¬ condV C n t := fun h' => by
  have e := (condP_time h).symm.trans (condV_time h')
  exact sched_ne C.Δ_pos ((C.slotOf t : Nat) : Int) ((C.slotOf t : Nat) : Int) 1 (by decide) (by linarith)

omit [Inhabited V] in
theorem condP_not_condC {C : Spec.Config} {P : Spec.Provisional V}
    {n : Spec.NodeState V} {t : Spec.Time} (h : condP C P n t) :
    ¬ condC C n t := fun h' => by
  have e := (condP_time h).symm.trans (condC_time h')
  exact sched_ne C.Δ_pos ((C.slotOf t : Nat) : Int) ((C.slotOf t : Nat) : Int) 2 (by decide) (by linarith)

omit [Inhabited V] in
theorem condP_not_condA {C : Spec.Config} {P : Spec.Provisional V}
    {n : Spec.NodeState V} {t : Spec.Time} (h : condP C P n t) :
    ¬ condA C n t := fun h' => by
  have e := (condP_time h).symm.trans (condA_time h')
  exact sched_ne C.Δ_pos ((C.slotOf t : Nat) : Int) (((C.round_of (C.slotOf t) * C.R : Nat)) : Int) 6 (by decide) (by linarith)

omit [DecidableEq V] [Fintype V] [Inhabited V] in
theorem condV_not_condC {C : Spec.Config} {n : Spec.NodeState V}
    {t : Spec.Time} (h : condV C n t) : ¬ condC C n t := fun h' => by
  have e := (condV_time h).symm.trans (condC_time h')
  have hΔ := C.Δ_pos
  linarith

omit [DecidableEq V] [Fintype V] [Inhabited V] in
theorem condV_not_condA {C : Spec.Config} {n : Spec.NodeState V}
    {t : Spec.Time} (h : condV C n t) : ¬ condA C n t := fun h' => by
  have e := (condV_time h).symm.trans (condA_time h')
  exact sched_ne C.Δ_pos ((C.slotOf t : Nat) : Int) (((C.round_of (C.slotOf t) * C.R : Nat)) : Int) 5 (by decide) (by linarith)

omit [DecidableEq V] [Fintype V] [Inhabited V] in
/-- When the attestation test holds, the confirmation test holds too. -/
theorem condC_of_condA {C : Spec.Config} {n : Spec.NodeState V}
    {t : Spec.Time} (h : condA C n t) : condC C n t := by
  have ht := h
  simp only [condA, Bool.and_eq_true, decide_eq_true_eq] at ht
  have hs : C.slotOf t = C.round_of (C.slotOf t) * C.R + 1 := by
    conv_lhs => rw [ht.1]
    exact slotOf_attestation_time C _
  refine ⟨by rw [hs]; exact Nat.succ_pos _, ?_⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨?_, ht.2⟩
  conv_lhs => rw [ht.1]
  simp only [Spec.Config.round_attestation_time, Spec.Config.opening,
    Spec.Config.gf_confirmation_time, Spec.Config.proposal_time]
  have hsI : ((C.slotOf t : Nat) : Int) =
      ((C.round_of (C.slotOf t) : Nat) : Int) * ((C.R : Nat) : Int) + 1 := by exact_mod_cast hs
  push_cast
  first
    | linear_combination (4 * C.Δ) * hsI
    | linear_combination (-4 * C.Δ) * hsI

end SpecRecord.TickReached


namespace SpecRecord.TickReached

open DecoupledConsensusModel DecoupledConsensusModel.Execution DecoupledConsensusModel.Sts
open DecoupledConsensusModel.Sts.Record
open SpecRecord.NodeFacts SpecRecord.NoRaise SpecRecord.GradesRunFacts
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-! ## The store a member duty hands the spec, at a reached store -/

/-- `Inv3 st`: `st` meets `StoreOk`, `RunStoreInv` and `ConfirmedInTree`. -/
def Inv3 (st : Spec.Store V) : Prop :=
  StoreOk st ∧ SubtypeEqualities.RunStoreInv st ∧ HandlersRunFacts.ConfirmedInTree st

/-- If `st'` follows from `st` by store steps and has distinct roots, `Inv3 st` gives `Inv3 st'`. -/
theorem inv3_reach {C : Spec.Config} {P : Spec.Provisional V} {τ : Time}
    {st st' : Spec.Store V} (h : StoreSteps.StoreReach C P τ st st')
    (hd : DistinctRoots st'.T) (hq : Inv3 st) : Inv3 st' :=
  HandlersRunFacts.reach_induction_ok Inv3
    (fun a b hs hd' q => by
      obtain ⟨hb1, hb2⟩ := HandlersRunFacts.base_step hs hd' ⟨q.1, q.2.1⟩
      exact ⟨hb1, hb2, HandlersRunFacts.confirmedInTree_step hs q.1 q.2.1 q.2.2⟩) h hd hq

omit [Fintype V] [Inhabited V] in
/-- Saved grades already at round `r` are brought to `r` unchanged. -/
theorem advance_to_round_self (c : Spec.SavedGrades V) {r : Spec.Round}
    (h : c.round = r) : Spec.Protocol.advance_to_round c r = c := by
  unfold Spec.Protocol.advance_to_round
  rw [if_pos h.symm]

/-- On a store `X` with `Inv3`, and saved grades `c` of tree blocks at round `r`, the store a member
    duty builds before the fill is `X` with the saved grades `c`. -/
theorem handed_eq (X : Spec.Store V) (hX : Inv3 X) {c : Spec.SavedGrades V}
    (hc : Spec.Store.ContractInTree X.T c) {r : Spec.Round} (hr : c.round = r) :
    ({ Spec.Store.ofImage X with
        saved_grades := Spec.Protocol.advance_to_round (X.contractOfImage c) r } :
      Spec.Store V) = { X with saved_grades := c } := by
  obtain ⟨hok, hR, hC⟩ := hX
  rw [Spec.Store.ofImage_eq_self X hok.2.1 hok.2.2.2 hR.1 hC.1 hC.2.1 hC.2.2,
    Spec.Store.contractOfImage_of_distinctRoots X hok.2.1 hc, advance_to_round_self c hr]

omit [Fintype V] [Inhabited V] in
/-- Saved grades whose blocks are blocks of `T` hold, in every computed result, a block of `T` or
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

/-- For an outcome `c` of the phase tick at `t` on a reached node state, the grades update of the
    tick at `t` on the node's store answers a store whose saved grades are `c`, at the round of
    `t`'s slot and holding blocks of the node's tree only. -/
theorem onPhaseTick_eq (S : Setup V) (n : (Model.spec (V := V)).N) (t : Time)
    (hn : (Model.spec (V := V)).reachedNode n) {c : (Model.spec (V := V)).Cache}
    (hc : (Model.spec (V := V)).onPhaseTick S.E S.hc n.st.core.toHealing t n.cache ⇢ c) :
    ∃ st0 : Spec.Store V,
      Spec.Protocol.update_grades (Setup.toSpec S).C (Setup.toSpec S).P n.val.st t =
        .ok st0 ∧ c = st0.saved_grades ∧
      st0 = { n.val.st with saved_grades := c } ∧
      c.round = (Setup.toSpec S).C.round_of ((Setup.toSpec S).C.slotOf t) ∧
      Spec.Store.ContractInTree n.val.st.T c := by
  obtain ⟨st0, h0, rfl, -⟩ := SpecRecord.GradesFacts.sd_onPhaseTick_ok hc
  have h0' : Spec.Protocol.update_grades (Setup.toSpec S).C (Setup.toSpec S).P
      n.val.st t = .ok st0 := h0
  obtain ⟨e0, hr⟩ := update_grades_ok h0'
  refine ⟨st0, h0', rfl, e0, hr, ?_⟩
  exact contractInTree_of_claim (memClaim_update_grades n.property h0'
    (claim_of_contractInTree (reached_elim hn).2.2))

/-- At a reached node state, the store staged for the tick's duties with the phase tick's saved
    grades written meets `Inv3` and is the store the spec's tick runs its duties on. -/
theorem staged_eq (S : Setup V) (n : (Model.spec (V := V)).N) (t : Time)
    (hn : (Model.spec (V := V)).reachedNode n) {c : Spec.SavedGrades V}
    {st0 : Spec.Store V} (e0 : st0 = { n.val.st with saved_grades := c }) :
    ({ ((Model.spec (V := V)).ns_setClock S.E n.st t).val with saved_grades := c } :
      Spec.Store V) = { st0 with t := t, s := (Setup.toSpec S).C.slotOf t } ∧
    Inv3 ((Model.spec (V := V)).ns_setClock S.E n.st t).val := by
  refine ⟨by rw [e0]; rfl, ?_⟩
  obtain ⟨h1, h2, -⟩ := reached_elim hn
  exact ⟨((Model.spec (V := V)).ns_setClock S.E n.st t).property, h1, h2⟩

omit [Inhabited V] in
/-- Two external inputs with the same new root for `v` give `v` the same proposal duty. -/
theorem propose_block_external {C : Spec.Config} {P : Spec.Provisional V}
    {X₁ X₂ : Spec.External V} {v : V} (h : X₁.new_root v = X₂.new_root v)
    (st : Spec.Store V) :
    Spec.Protocol.propose_block C P X₁ v st =
      Spec.Protocol.propose_block C P X₂ v st := by
  unfold Spec.Protocol.propose_block Spec.Protocol.build_proposal
    Spec.Protocol.proposal_input
  rw [h]

/-! ## Each member duty returns the spec's answer -/

/-- On a store `X` with `Inv3`, under saved grades `c` of tree blocks at `X`'s round, where the
    spec's proposal of `v` on `X` with saved grades `c` answers `st2` and the objects `l`, every
    outcome of the member proposal duty of `S.node v` under `c` is `st2` with `c` written and the
    first block of `l`. -/
theorem propose_member_eq (S : Setup V) (v : V) (X : OkStore V) (hX : Inv3 X.val)
    {c : Spec.SavedGrades V} (hc : Spec.Store.ContractInTree X.val.T c)
    (hr : c.round = (Setup.toSpec S).C.round_of X.val.s)
    {st2 : Spec.Store V} {l : List (Spec.NamedObject V)}
    (hrun : (Spec.Protocol.propose_block (Setup.toSpec S).C (Setup.toSpec S).P
      (Setup.toSpec S).X v { X.val with saved_grades := c }).run [] = .ok (st2, l))
    {D : (Model.spec (V := V)).NS × Option (NamedBlock V)}
    (hD : (Model.spec (V := V)).duties_propose_block_with c S.E S.hc S.cfg (S.node v) X ⇢ D) :
    D.1.val = { st2 with saved_grades := c } ∧
      D.2 = (Member.firstSentBlock l).map Spec.Block.toProofNamed := by
  have hext : (Member.externalOfNode (S.node v)).new_root (S.node v).val_index =
      (Setup.toSpec S).X.new_root (S.node v).val_index := by
    rw [S.node_val_index]; rfl
  have h' : (Spec.Protocol.propose_block (Spec.Config.toSpec S.E S.hc S.cfg)
      (Spec.Provisional.toSpec S.E) (Member.externalOfNode (S.node v)) (S.node v).val_index
      { Spec.Store.ofImage X.val with saved_grades :=
        (Spec.Protocol.advance_to_round (X.val.contractOfImage c)
          ((Spec.Config.toSpec S.E S.hc S.cfg).round_of X.val.s)) }).run [] =
        .ok (st2, l) := by
    rw [handed_eq X.val hX hc (r := (Spec.Config.toSpec S.E S.hc S.cfg).round_of X.val.s) hr,
      propose_block_external hext, S.node_val_index]
    exact hrun
  have hr1 := Member.duties_propose_block_with_returns_of_ok c S.E S.hc S.cfg (S.node v) X.val h'
  have hr2 := (returns_preimageOutcomes _ _ _).1 hD
  unfold Member.duties_propose_block_with at hr1 hr2
  rw [returns_successOutcomes] at hr1 hr2
  have e := Except.ok.inj (hr2.symm.trans hr1)
  exact ⟨congrArg Prod.fst e, congrArg Prod.snd e⟩

/-- On a store `X` with `Inv3`, under saved grades `c` of tree blocks at `X`'s round, every outcome
    of the member vote duty of `S.node v` under `c` is the spec's vote duty's answer on `X` with
    saved grades `c`. -/
theorem vote_member_eq (S : Setup V) (v : V) (X : OkStore V) (hX : Inv3 X.val)
    {c : Spec.SavedGrades V} (hc : Spec.Store.ContractInTree X.val.T c)
    (hr : c.round = (Setup.toSpec S).C.round_of X.val.s)
    {st3 : Spec.Store V} {l : List (Spec.NamedObject V)}
    (hrun : (Spec.Protocol.goldfish_vote (Setup.toSpec S).C (Setup.toSpec S).P
      v { X.val with saved_grades := c }).run [] = .ok (st3, l))
    {D : (Model.spec (V := V)).NS × Option (GoldfishVote V)}
    (hD : (Model.spec (V := V)).duties_goldfish_vote_with c S.E S.hc (S.node v) X ⇢ D) :
    D.1.val = { st3 with saved_grades := c } ∧
      D.2 = (Member.firstSentGoldfishVote l).map Spec.GoldfishVote.toProof := by
  have h' : (Spec.Protocol.goldfish_vote
      (Spec.Config.toSpec S.E S.hc unreadHeightConfig)
      (Spec.Provisional.toSpec S.E) (S.node v).val_index
      { Spec.Store.ofImage X.val with saved_grades :=
        (Spec.Protocol.advance_to_round (X.val.contractOfImage c)
          ((Spec.Config.toSpec S.E S.hc unreadHeightConfig).round_of X.val.s)) }).run [] =
        .ok (st3, l) := by
    rw [handed_eq X.val hX hc
      (r := (Spec.Config.toSpec S.E S.hc unreadHeightConfig).round_of X.val.s) hr,
      S.node_val_index]
    exact hrun
  have hr1 := Member.duties_goldfish_vote_with_returns_of_ok c S.E S.hc (S.node v) X.val h'
  have hr2 := (returns_preimageOutcomes _ _ _).1 hD
  unfold Member.duties_goldfish_vote_with at hr1 hr2
  rw [returns_successOutcomes] at hr1 hr2
  have e := Except.ok.inj (hr2.symm.trans hr1)
  exact ⟨congrArg Prod.fst e, congrArg Prod.snd e⟩

/-- On a store `X` with `Inv3`, under saved grades `c` of tree blocks at `X`'s round, every outcome
    of the member confirmation duty of slot `s` under `c` is the spec's confirmation's answer on `X`
    with saved grades `c`. -/
theorem confirm_member_eq (S : Setup V) (X : OkStore V) (hX : Inv3 X.val)
    {c : Spec.SavedGrades V} (hc : Spec.Store.ContractInTree X.val.T c)
    (hr : c.round = (Setup.toSpec S).C.round_of X.val.s) (s : Slot)
    {st4 : Spec.Store V}
    (hrun : Spec.Protocol.update_confirmation (Setup.toSpec S).C
      { X.val with saved_grades := c } s = .ok st4)
    {st : (Model.spec (V := V)).NS}
    (hst : (Model.spec (V := V)).duties_update_confirmation_with c S.E S.hc X s ⇢ st) :
    st.val = { st4 with saved_grades := c } := by
  have h' : Spec.Protocol.update_confirmation
      (Spec.Config.toSpec S.E S.hc unreadHeightConfig)
      { Spec.Store.ofImage X.val with saved_grades :=
        (Spec.Protocol.advance_to_round (X.val.contractOfImage c)
          ((Spec.Config.toSpec S.E S.hc unreadHeightConfig).round_of X.val.s)) } s =
        .ok st4 := by
    rw [handed_eq X.val hX hc
      (r := (Spec.Config.toSpec S.E S.hc unreadHeightConfig).round_of X.val.s) hr]
    exact hrun
  have hr1 := Member.duties_update_confirmation_with_returns_of_ok c S.E S.hc X.val s h'
  have hr2 := (returns_preimageOutcomes _ _ _).1 hst
  unfold Member.duties_update_confirmation_with at hr1 hr2
  rw [returns_successOutcomes] at hr1 hr2
  exact Except.ok.inj (hr2.symm.trans hr1)

/-- On a store `X` with `Inv3`, under saved grades `c` of tree blocks at `X`'s round, every outcome
    of the member attestation duty of `S.node v` with signing history `sh` is the spec's attestation
    duty's answer on `X` with saved grades `c`, which sends the attestation `row`. -/
theorem attest_member_eq (S : Setup V) (v : V) (X : OkStore V) (hX : Inv3 X.val)
    {c : Spec.SavedGrades V} (hc : Spec.Store.ContractInTree X.val.T c)
    (hr : c.round = (Setup.toSpec S).C.round_of X.val.s) (sh : Spec.SigningHistory)
    {st5 : Spec.Store V} {sh5 : Spec.SigningHistory}
    {row : Spec.Attestation V}
    (hrun : (Spec.Protocol.attest (Setup.toSpec S).C v
      { X.val with saved_grades := c } sh).run [] =
        .ok ((st5, sh5), [Spec.NamedObject.attest row]))
    {D : (Model.spec (V := V)).NS × (Model.spec (V := V)).NR × NamedAttestation V}
    (hD : (Model.spec (V := V)).duties_attest_with c S.E S.hc (S.node v) X sh ⇢ D) :
    D.1.val = { st5 with saved_grades := c } ∧ D.2.1 = sh5 ∧ D.2.2 = row.toProofNamed := by
  have h' : (Spec.Protocol.attest
      (Spec.Config.toSpec S.E S.hc unreadHeightConfig) (S.node v).val_index
      { Spec.Store.ofImage X.val with saved_grades :=
        (Spec.Protocol.advance_to_round (X.val.contractOfImage c)
          ((Spec.Config.toSpec S.E S.hc unreadHeightConfig).round_of X.val.s)) } sh).run [] =
        .ok ((st5, sh5), [Spec.NamedObject.attest row]) := by
    rw [handed_eq X.val hX hc
      (r := (Spec.Config.toSpec S.E S.hc unreadHeightConfig).round_of X.val.s) hr,
      S.node_val_index]
    exact hrun
  have hr1 := Member.duties_attest_with_returns_of_ok c S.E S.hc (S.node v) X.val sh h'
    (a := row) rfl
  have hr2 := (returns_preimageOutcomes _ _ _).1 hD
  unfold Member.duties_attest_with at hr1 hr2
  rw [returns_successOutcomes] at hr1 hr2
  have e := Except.ok.inj (hr2.symm.trans hr1)
  exact ⟨congrArg Prod.fst e, congrArg (fun x => x.2.1) e, congrArg (fun x => x.2.2) e⟩

end SpecRecord.TickReached


namespace SpecRecord.TickReached

open DecoupledConsensusModel DecoupledConsensusModel.Execution DecoupledConsensusModel.Sts
open DecoupledConsensusModel.Sts.Record
open SpecRecord.NodeFacts SpecRecord.NoRaise
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-! ## Each member duty has the spec's answer as an outcome -/

/-- The member proposal duty has the spec's answer as an outcome. -/
theorem propose_member_exists (S : Setup V) (v : V) (X : OkStore V) (hX : Inv3 X.val)
    {c : Spec.SavedGrades V} (hc : Spec.Store.ContractInTree X.val.T c)
    (hr : c.round = (Setup.toSpec S).C.round_of X.val.s)
    {st2 : Spec.Store V} {l : List (Spec.NamedObject V)}
    (hrun : (Spec.Protocol.propose_block (Setup.toSpec S).C (Setup.toSpec S).P
      (Setup.toSpec S).X v { X.val with saved_grades := c }).run [] = .ok (st2, l))
    (hok : StoreOk st2) :
    ∃ D : (Model.spec (V := V)).NS × Option (NamedBlock V),
      (Model.spec (V := V)).duties_propose_block_with c S.E S.hc S.cfg (S.node v) X ⇢ D ∧
      D.1.val = { st2 with saved_grades := c } := by
  have hext : (Member.externalOfNode (S.node v)).new_root (S.node v).val_index =
      (Setup.toSpec S).X.new_root (S.node v).val_index := by
    rw [S.node_val_index]; rfl
  have h' : (Spec.Protocol.propose_block (Spec.Config.toSpec S.E S.hc S.cfg)
      (Spec.Provisional.toSpec S.E) (Member.externalOfNode (S.node v)) (S.node v).val_index
      { Spec.Store.ofImage X.val with saved_grades :=
        (Spec.Protocol.advance_to_round (X.val.contractOfImage c)
          ((Spec.Config.toSpec S.E S.hc S.cfg).round_of X.val.s)) }).run [] =
        .ok (st2, l) := by
    rw [handed_eq X.val hX hc (r := (Spec.Config.toSpec S.E S.hc S.cfg).round_of X.val.s) hr,
      propose_block_external hext, S.node_val_index]
    exact hrun
  exact ⟨(⟨{ st2 with saved_grades := c }, NonEmpty.storeOk_with_saved_grades hok c⟩,
    (Member.firstSentBlock l).map Spec.Block.toProofNamed),
    (returns_preimageOutcomes _ _ _).2
      (Member.duties_propose_block_with_returns_of_ok c S.E S.hc S.cfg (S.node v) X.val h'), rfl⟩

/-- The member Goldfish vote duty has the spec's answer as an outcome. -/
theorem vote_member_exists (S : Setup V) (v : V) (X : OkStore V) (hX : Inv3 X.val)
    {c : Spec.SavedGrades V} (hc : Spec.Store.ContractInTree X.val.T c)
    (hr : c.round = (Setup.toSpec S).C.round_of X.val.s)
    {st3 : Spec.Store V} {l : List (Spec.NamedObject V)}
    (hrun : (Spec.Protocol.goldfish_vote (Setup.toSpec S).C (Setup.toSpec S).P
      v { X.val with saved_grades := c }).run [] = .ok (st3, l))
    (hok : StoreOk st3) :
    ∃ D : (Model.spec (V := V)).NS × Option (GoldfishVote V),
      (Model.spec (V := V)).duties_goldfish_vote_with c S.E S.hc (S.node v) X ⇢ D ∧
      D.1.val = { st3 with saved_grades := c } := by
  have h' : (Spec.Protocol.goldfish_vote
      (Spec.Config.toSpec S.E S.hc unreadHeightConfig)
      (Spec.Provisional.toSpec S.E) (S.node v).val_index
      { Spec.Store.ofImage X.val with saved_grades :=
        (Spec.Protocol.advance_to_round (X.val.contractOfImage c)
          ((Spec.Config.toSpec S.E S.hc unreadHeightConfig).round_of X.val.s)) }).run [] =
        .ok (st3, l) := by
    rw [handed_eq X.val hX hc
      (r := (Spec.Config.toSpec S.E S.hc unreadHeightConfig).round_of X.val.s) hr,
      S.node_val_index]
    exact hrun
  exact ⟨(⟨{ st3 with saved_grades := c }, NonEmpty.storeOk_with_saved_grades hok c⟩,
    (Member.firstSentGoldfishVote l).map Spec.GoldfishVote.toProof),
    (returns_preimageOutcomes _ _ _).2
      (Member.duties_goldfish_vote_with_returns_of_ok c S.E S.hc (S.node v) X.val h'), rfl⟩

/-- The member confirmation duty has the spec's answer as an outcome. -/
theorem confirm_member_exists (S : Setup V) (X : OkStore V) (hX : Inv3 X.val)
    {c : Spec.SavedGrades V} (hc : Spec.Store.ContractInTree X.val.T c)
    (hr : c.round = (Setup.toSpec S).C.round_of X.val.s) (s : Slot)
    {st4 : Spec.Store V}
    (hrun : Spec.Protocol.update_confirmation (Setup.toSpec S).C
      { X.val with saved_grades := c } s = .ok st4)
    (hok : StoreOk st4) :
    ∃ st : (Model.spec (V := V)).NS,
      (Model.spec (V := V)).duties_update_confirmation_with c S.E S.hc X s ⇢ st ∧
      st.val = { st4 with saved_grades := c } := by
  have h' : Spec.Protocol.update_confirmation
      (Spec.Config.toSpec S.E S.hc unreadHeightConfig)
      { Spec.Store.ofImage X.val with saved_grades :=
        (Spec.Protocol.advance_to_round (X.val.contractOfImage c)
          ((Spec.Config.toSpec S.E S.hc unreadHeightConfig).round_of X.val.s)) } s =
        .ok st4 := by
    rw [handed_eq X.val hX hc
      (r := (Spec.Config.toSpec S.E S.hc unreadHeightConfig).round_of X.val.s) hr]
    exact hrun
  exact ⟨⟨{ st4 with saved_grades := c }, NonEmpty.storeOk_with_saved_grades hok c⟩,
    (returns_preimageOutcomes _ _ _).2
      (Member.duties_update_confirmation_with_returns_of_ok c S.E S.hc X.val s h'), rfl⟩

/-- The member attestation duty has the spec's answer as an outcome. -/
theorem attest_member_exists (S : Setup V) (v : V) (X : OkStore V) (hX : Inv3 X.val)
    {c : Spec.SavedGrades V} (hc : Spec.Store.ContractInTree X.val.T c)
    (hr : c.round = (Setup.toSpec S).C.round_of X.val.s) (sh : Spec.SigningHistory)
    {st5 : Spec.Store V} {sh5 : Spec.SigningHistory}
    {row : Spec.Attestation V}
    (hrun : (Spec.Protocol.attest (Setup.toSpec S).C v
      { X.val with saved_grades := c } sh).run [] =
        .ok ((st5, sh5), [Spec.NamedObject.attest row]))
    (hok : StoreOk st5) :
    ∃ D : (Model.spec (V := V)).NS × (Model.spec (V := V)).NR × NamedAttestation V,
      (Model.spec (V := V)).duties_attest_with c S.E S.hc (S.node v) X sh ⇢ D ∧
      D.1.val = { st5 with saved_grades := c } := by
  have h' : (Spec.Protocol.attest
      (Spec.Config.toSpec S.E S.hc unreadHeightConfig) (S.node v).val_index
      { Spec.Store.ofImage X.val with saved_grades :=
        (Spec.Protocol.advance_to_round (X.val.contractOfImage c)
          ((Spec.Config.toSpec S.E S.hc unreadHeightConfig).round_of X.val.s)) } sh).run [] =
        .ok ((st5, sh5), [Spec.NamedObject.attest row]) := by
    rw [handed_eq X.val hX hc
      (r := (Spec.Config.toSpec S.E S.hc unreadHeightConfig).round_of X.val.s) hr,
      S.node_val_index]
    exact hrun
  exact ⟨(⟨{ st5 with saved_grades := c }, NonEmpty.storeOk_with_saved_grades hok c⟩, sh5,
    row.toProofNamed),
    (returns_preimageOutcomes _ _ _).2
      (Member.duties_attest_with_returns_of_ok c S.E S.hc (S.node v) X.val sh h' (a := row) rfl), rfl⟩

end SpecRecord.TickReached


namespace SpecRecord.TickReached

open DecoupledConsensusModel DecoupledConsensusModel.Execution DecoupledConsensusModel.Sts
open DecoupledConsensusModel.Sts.Record
open SpecRecord.NodeFacts SpecRecord.NoRaise
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-! ## The tick at a reached node state running as `v`, duty by duty -/

omit [Fintype V] [Inhabited V] in
/-- A store with saved grades `c` written, when it already holds `c`, is itself. -/
theorem with_saved_grades_self (st : Spec.Store V) {c : Spec.SavedGrades V}
    (h : st.saved_grades = c) : ({ st with saved_grades := c } : Spec.Store V) = st := by
  rw [← h]

/-- When the tick from a reached node state running as `v` proposes, its store is the clip of the
    store the member proposal duty of `S.node v` returns on the staged store, and it sends that
    duty's block alone. -/
theorem proposal_tick (S : Setup V) (v : V) (n : (Model.spec (V := V)).N) (t : Time)
    (out : (Model.spec (V := V)).N × List (NamedObject V))
    (hout : (Model.spec (V := V)).tick S v n t ⇢ out)
    (hn : (Model.spec (V := V)).reachedNode n) (hv : n.val.v = v)
    (hcP : condP (Setup.toSpec S).C (Setup.toSpec S).P n.val t)
    {c : (Model.spec (V := V)).Cache}
    (hc : (Model.spec (V := V)).onPhaseTick S.E S.hc n.st.core.toHealing t n.cache ⇢ c)
    {D : (Model.spec (V := V)).NS × Option (NamedBlock V)}
    (hD : (Model.spec (V := V)).duties_propose_block_with c S.E S.hc S.cfg (S.node v)
      ((Model.spec (V := V)).ns_setClock S.E n.st t) ⇢ D) :
    ∃ (st2 : Spec.Store V) (B : Spec.Block V),
      out.1.val.st = Spec.make_grades_compatible_with_finalized st2 ∧ D.1.val = st2 ∧
      out.2 = [NamedObject.block B.toProofNamed] ∧ D.2 = some B.toProofNamed := by
  obtain ⟨sent, hrun, hsent⟩ := NodeFacts.tick_out S v n t out hout
  obtain ⟨st0, st2, st3, st4, st5, sh5, l1, l2, h0, hP1, -, -, hV0, -, hC0, -, hA0, hn'⟩ :=
    tick_detail hrun
  obtain ⟨B, hst2, hl1⟩ := NodeFacts.propose_block_run (hP1 hcP)
  obtain ⟨hst3, hl2⟩ := hV0 (condP_not_condV hcP)
  have hst4 := hC0 (condP_not_condC hcP)
  obtain ⟨hst5, -, hs⟩ := hA0 (condP_not_condA hcP)
  obtain ⟨st0', h0', hc0, e0, hr, hct⟩ := onPhaseTick_eq S n t hn hc
  obtain rfl : st0' = st0 := Except.ok.inj (h0'.symm.trans h0)
  obtain ⟨hstage, hinv⟩ := staged_eq S n t hn e0
  have hrun' : (Spec.Protocol.propose_block (Setup.toSpec S).C (Setup.toSpec S).P
      (Setup.toSpec S).X v { ((Model.spec (V := V)).ns_setClock S.E n.st t).val with
        saved_grades := c }).run [] = .ok (st2, l1) := by
    rw [hstage, ← hv]; exact hP1 hcP
  obtain ⟨hD1, hD2⟩ := propose_member_eq S v _ hinv hct hr hrun' hD
  have hsg : st2.saved_grades = c := by
    rw [hst2, NodeFacts.on_block_saved_grades, hc0]
  refine ⟨st2, B, ?_, ?_, ?_, ?_⟩
  · rw [hn', hst5, hst4, hst3]
  · rw [hD1, with_saved_grades_self st2 hsg]
  · rw [hsent, hs, hl2, hl1]; rfl
  · rw [hD2, hl1]; rfl

/-- When the tick from a reached node state running as `v` runs the vote duty, its store is the clip
    of the store the member vote duty of `S.node v` returns on the staged store, and it sends what
    that duty sends: nothing, or `v`'s vote for the slot of `t`. -/
theorem vote_tick (S : Setup V) (v : V) (n : (Model.spec (V := V)).N) (t : Time)
    (out : (Model.spec (V := V)).N × List (NamedObject V))
    (hout : (Model.spec (V := V)).tick S v n t ⇢ out)
    (hn : (Model.spec (V := V)).reachedNode n) (hv : n.val.v = v)
    (hcV : condV (Setup.toSpec S).C n.val t)
    {c : (Model.spec (V := V)).Cache}
    (hc : (Model.spec (V := V)).onPhaseTick S.E S.hc n.st.core.toHealing t n.cache ⇢ c)
    {D : (Model.spec (V := V)).NS × Option (GoldfishVote V)}
    (hD : (Model.spec (V := V)).duties_goldfish_vote_with c S.E S.hc (S.node v)
      ((Model.spec (V := V)).ns_setClock S.E n.st t) ⇢ D) :
    ∃ (st3 : Spec.Store V) (l : List (Spec.NamedObject V)),
      out.1.val.st = Spec.make_grades_compatible_with_finalized st3 ∧ D.1.val = st3 ∧
      out.2 = l.map Spec.NamedObject.toProof ∧
      D.2 = (Member.firstSentGoldfishVote l).map Spec.GoldfishVote.toProof ∧
      (l = [] ∨ ∃ root, l = [Spec.NamedObject.gfVote
        ⟨v, (Setup.toSpec S).C.slotOf t, root⟩]) := by
  obtain ⟨sent, hrun, hsent⟩ := NodeFacts.tick_out S v n t out hout
  obtain ⟨st0, st2, st3, st4, st5, sh5, l1, l2, h0, -, hP0, hV1, -, -, hC0, -, hA0, hn'⟩ :=
    tick_detail hrun
  have hP : ¬ condP (Setup.toSpec S).C (Setup.toSpec S).P n.val t := fun h => condP_not_condV h hcV
  obtain ⟨hst2, hl1⟩ := hP0 hP
  have hst4 := hC0 (condV_not_condC hcV)
  obtain ⟨hst5, -, hs⟩ := hA0 (condV_not_condA hcV)
  obtain ⟨st0', h0', hc0, e0, hr, hct⟩ := onPhaseTick_eq S n t hn hc
  obtain rfl : st0' = st0 := Except.ok.inj (h0'.symm.trans h0)
  obtain ⟨hstage, hinv⟩ := staged_eq S n t hn e0
  have hrun3 := hV1 hcV
  rw [hl1, hst2] at hrun3
  have hrun' : (Spec.Protocol.goldfish_vote (Setup.toSpec S).C (Setup.toSpec S).P
      v { ((Model.spec (V := V)).ns_setClock S.E n.st t).val with
        saved_grades := c }).run [] = .ok (st3, l2) := by
    rw [hstage, ← hv]; exact hrun3
  obtain ⟨hD1, hD2⟩ := vote_member_eq S v _ hinv hct hr hrun' hD
  have hsg : st3.saved_grades = c := by
    rcases NodeFacts.goldfish_vote_run hrun3 with ⟨e, -⟩ | ⟨u, e, -⟩
    · rw [e, hc0]
    · rw [e, NodeFacts.on_goldfish_vote_checked_saved_grades, hc0]
  refine ⟨st3, l2, ?_, ?_, ?_, hD2, ?_⟩
  · rw [hn', hst5, hst4]
  · rw [hD1, with_saved_grades_self st3 hsg]
  · rw [hsent, hs]
  · obtain ⟨votes, sup, tree, H, -, -, -, -, hsent'⟩ :=
      SpecRecord.ContractImages.goldfish_vote_sent hrun3
    rcases hsent' with ⟨-, hl⟩ | ⟨-, hl⟩
    · right
      refine ⟨H.root, ?_⟩
      have hl' : l2 = _ := hl
      rw [hl', hv]
      rfl
    · left; exact hl

/-- When the tick from a reached node state running as `v` attests, it is the member confirmation
    duty on the staged store, then the member attestation duty of `S.node v`, then the clip, and it
    sends that attestation alone. -/
theorem action_tick (S : Setup V) (v : V) (n : (Model.spec (V := V)).N) (t : Time)
    (out : (Model.spec (V := V)).N × List (NamedObject V))
    (hout : (Model.spec (V := V)).tick S v n t ⇢ out)
    (hn : (Model.spec (V := V)).reachedNode n) (hv : n.val.v = v)
    (hcA : condA (Setup.toSpec S).C n.val t)
    {c : (Model.spec (V := V)).Cache}
    (hc : (Model.spec (V := V)).onPhaseTick S.E S.hc n.st.core.toHealing t n.cache ⇢ c)
    {st : (Model.spec (V := V)).NS}
    (hst : (Model.spec (V := V)).duties_update_confirmation_with c S.E S.hc
      ((Model.spec (V := V)).ns_setClock S.E n.st t) ((Setup.toSpec S).C.slotOf t - 1) ⇢ st)
    {D : (Model.spec (V := V)).NS × (Model.spec (V := V)).NR × NamedAttestation V}
    (hD : (Model.spec (V := V)).duties_attest_with c S.E S.hc (S.node v) st n.record ⇢ D) :
    ∃ (st5 : Spec.Store V) (row : Spec.Attestation V),
      out.1.val.st = Spec.make_grades_compatible_with_finalized st5 ∧ D.1.val = st5 ∧
      out.2 = [NamedObject.attest row.toProofNamed] ∧ D.2.2 = row.toProofNamed := by
  obtain ⟨sent, hrun, hsent⟩ := NodeFacts.tick_out S v n t out hout
  obtain ⟨st0, st2, st3, st4, st5, sh5, l1, l2, h0, -, hP0, -, hV0, hC1, -, hA1, -, hn'⟩ :=
    tick_detail hrun
  have hcC := condC_of_condA hcA
  obtain ⟨hst2, hl1⟩ := hP0 (fun h => condP_not_condA h hcA)
  obtain ⟨hst3, hl2⟩ := hV0 (fun h => condV_not_condA h hcA)
  obtain ⟨st0', h0', hc0, e0, hr, hct⟩ := onPhaseTick_eq S n t hn hc
  obtain rfl : st0' = st0 := Except.ok.inj (h0'.symm.trans h0)
  obtain ⟨hstage, hinv⟩ := staged_eq S n t hn e0
  have hrun4 := hC1 hcC
  rw [hst3, hst2] at hrun4
  have hrunc : Spec.Protocol.update_confirmation (Setup.toSpec S).C
      { ((Model.spec (V := V)).ns_setClock S.E n.st t).val with saved_grades := c }
      ((Setup.toSpec S).C.slotOf t - 1) = .ok st4 := by
    rw [hstage]; exact hrun4
  have hstv := confirm_member_eq S _ hinv hct hr _ hrunc hst
  have e4 := NodeFacts.update_confirmation_ok hrun4
  have hsg4 : st4.saved_grades = c := by rw [e4, hc0]
  have hst' : st.val = st4 := by rw [hstv, with_saved_grades_self st4 hsg4]
  have hT4 : st4.T = n.val.st.T := by rw [e4, e0]
  have hinv4 : Inv3 st.val := by
    rw [hst']
    refine inv3_reach (Relation.ReflTransGen.single
      (StoreSteps.update_confirmation_step _ (Setup.toSpec S).P t _ st4 _ hrun4)) ?_ ?_
    · rw [hT4]; exact n.property.2.1
    · rw [← hstage]; exact hinv
  have hct4 : Spec.Store.ContractInTree st.val.T c := by rw [hst', hT4]; exact hct
  have hr4 : c.round = (Setup.toSpec S).C.round_of st.val.s := by
    rw [hst', e4, e0, hr]
  obtain ⟨row, hb, hst5, hs⟩ := NodeFacts.attest_run (hA1 hcA)
  rw [hl2, hl1] at hs
  have hruna : (Spec.Protocol.attest (Setup.toSpec S).C v
      { st.val with saved_grades := c } n.record).run [] =
        .ok ((st5, sh5), [Spec.NamedObject.attest row]) := by
    have hA := hA1 hcA
    rw [hl2, hl1, hs, List.nil_append] at hA
    rw [with_saved_grades_self _ (by rw [hst']; exact hsg4), hst', ← hv]
    exact hA
  obtain ⟨hD1, -, hD3⟩ := attest_member_eq S v st hinv4 hct4 hr4 _ hruna hD
  have hsg5 : st5.saved_grades = c := by
    rw [hst5, NodeFacts.admit_attestation_saved_grades, hsg4]
  refine ⟨st5, row, ?_, ?_, ?_, hD3⟩
  · rw [hn']
  · rw [hD1, with_saved_grades_self st5 hsg5]
  · rw [hsent, hs]; rfl

end SpecRecord.TickReached


namespace SpecRecord.TickReached

open DecoupledConsensusModel DecoupledConsensusModel.Execution DecoupledConsensusModel.Sts
open DecoupledConsensusModel.Sts.Record
open SpecRecord.NodeFacts SpecRecord.NoRaise
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-! ## The tick's tests from the record's hypotheses -/

omit [DecidableEq V] [Fintype V] [Inhabited V] in
/-- Slot `s`'s proposal time is in slot `s`. -/
theorem slotOf_proposal_time (C : Spec.Config) (s : Spec.Slot) :
    C.slotOf (C.proposal_time s) = s := by
  have hΔ := C.Δ_pos
  apply slotOf_of_bounds
  · simp only [Spec.Config.proposal_time]; exact le_refl _
  · simp only [Spec.Config.proposal_time]; nlinarith

omit [DecidableEq V] [Fintype V] [Inhabited V] in
/-- Slot `s`'s vote time is in slot `s`. -/
theorem slotOf_vote_time (C : Spec.Config) (s : Spec.Slot) :
    C.slotOf (C.vote_time s) = s := by
  have hΔ := C.Δ_pos
  apply slotOf_of_bounds
  · simp only [Spec.Config.vote_time, Spec.Config.proposal_time]; linarith
  · simp only [Spec.Config.vote_time, Spec.Config.proposal_time]; nlinarith

omit [Fintype V] [Inhabited V] in
/-- The wake test of the tick reads `awakeSince` when it is set. -/
theorem awake_since_of {n : Spec.NodeState V} {t x : Spec.Time}
    (h : ∃ a, n.awakeSince = some a ∧ a ≤ x) :
    (Spec.record_awake n t).awake_since x = true :=
  (record_awake_awake_since n t x).mpr (Or.inl h)

/-- The proposal test holds at slot `s`'s proposal time for a node state of `s`'s proposer that
    passes the grade-1 awake test of `s`'s round. -/
theorem condP_of (S : Setup V) (v : V) (n : (Model.spec (V := V)).N) {s : Slot} (hs : 0 < s)
    (hpr : S.E.proposer s = n.val.v)
    (hrun : (Model.spec (V := V)).awake_for_grade1 S v n ((Model.spec (V := V)).round_of S.hc s)) :
    condP (Setup.toSpec S).C (Setup.toSpec S).P n.val ((Model.spec (V := V)).proposal_time S.E s) := by
  have hslot : (Setup.toSpec S).C.slotOf ((Model.spec (V := V)).proposal_time S.E s) = s :=
    slotOf_proposal_time (Setup.toSpec S).C s
  refine ⟨by rw [hslot]; exact hs, ?_⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rw [hslot]
  exact ⟨⟨rfl, hpr⟩, awake_since_of hrun⟩

/-- The vote test holds at slot `s`'s vote time for a node state that passes the grade-1 awake test
    of `s`'s round. -/
theorem condV_of (S : Setup V) (v : V) (n : (Model.spec (V := V)).N) {s : Slot} (hs : 0 < s)
    (hrun : (Model.spec (V := V)).awake_for_grade1 S v n ((Model.spec (V := V)).round_of S.hc s)) :
    condV (Setup.toSpec S).C n.val ((Model.spec (V := V)).vote_time S.E s) := by
  have hslot : (Setup.toSpec S).C.slotOf ((Model.spec (V := V)).vote_time S.E s) = s :=
    slotOf_vote_time (Setup.toSpec S).C s
  refine ⟨by rw [hslot]; exact hs, ?_⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rw [hslot]
  exact ⟨rfl, awake_since_of hrun⟩

/-- The attestation test holds at round `r`'s action time for a node state that passes the grade-2
    awake test of `r`. -/
theorem condA_of (S : Setup V) (v : V) (n : (Model.spec (V := V)).N) (r : Round)
    (hrun : (Model.spec (V := V)).awake_for_grade2 S v n r) :
    condA (Setup.toSpec S).C n.val ((Model.spec (V := V)).a S.hc S.E.Δ r) := by
  have hs : (Setup.toSpec S).C.slotOf ((Model.spec (V := V)).a S.hc S.E.Δ r) =
      r * (Setup.toSpec S).C.R + 1 := slotOf_attestation_time _ r
  have hr : (Setup.toSpec S).C.round_of (r * (Setup.toSpec S).C.R + 1) = r :=
    round_of_first_succ _ r
  simp only [condA, Bool.and_eq_true, decide_eq_true_eq]
  rw [hs, hr]
  exact ⟨rfl, awake_since_of hrun⟩

end SpecRecord.TickReached


namespace SpecRecord.TickReached

open DecoupledConsensusModel DecoupledConsensusModel.Execution DecoupledConsensusModel.Sts
open DecoupledConsensusModel.Sts.Record
open SpecRecord.NodeFacts SpecRecord.NoRaise
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-- A tick that does not propose keeps every attestation the node's store holds in each round. -/
theorem tick_rows_grow {C : Spec.Config} {P : Spec.Provisional V}
    {X : Spec.External V} {n n' : Spec.NodeState V}
    {t : Spec.Time} {sent : List (Spec.NamedObject V)}
    (h : (Spec.tick C P X n t).run [] = .ok (n', sent)) (hc : ¬ condP C P n t) :
    ∀ r x, x ∈ n.st.attestations r → x ∈ n'.st.attestations r := by
  obtain ⟨st0, st2, st3, st4, st5, sh5, l1, l2, h0, -, hP0, hV1, hV0, hC1, hC0, hA1, hA0, hn'⟩ :=
    tick_detail h
  intro r x hx
  have e2 : st2.attestations = n.st.attestations := by
    rw [(hP0 hc).1, (update_grades_ok h0).1]
  have e3 : st3.attestations = st2.attestations := by
    by_cases hv : condV C n t
    · rcases goldfish_vote_run (hV1 hv) with ⟨e, -⟩ | ⟨u, e, -⟩
      · rw [e]
      · obtain ⟨gv, tv, e'⟩ := on_goldfish_vote_checked_frame P st2 u
        rw [e, e']
    · rw [(hV0 hv).1]
  have e4 : st4.attestations = st3.attestations := by
    by_cases hcc : condC C n t
    · rw [update_confirmation_ok (hC1 hcc)]
    · rw [hC0 hcc]
  have h5 : x ∈ st5.attestations r := by
    have hx4 : x ∈ st4.attestations r := by rw [e4, e3, e2]; exact hx
    by_cases ha : condA C n t
    · obtain ⟨row, -, hst5, -⟩ := attest_run (hA1 ha)
      have hsub := (rowsAt_admit C st4 row).2.2 r
      have hp : x ∈ st4.sg_pool r := by
        simp only [Spec.Store.sg_pool, StoreSteps.getElem_fn, List.mem_toFinset]
        exact hx4
      have hq := hsub hp
      rw [← hst5] at hq
      simpa only [Spec.Store.sg_pool, StoreSteps.getElem_fn, List.mem_toFinset] using hq
    · rw [(hA0 ha).1]; exact hx4
  rw [hn']
  exact h5

end SpecRecord.TickReached


namespace SpecRecord.TickReached

open DecoupledConsensusModel DecoupledConsensusModel.Execution DecoupledConsensusModel.Sts
open DecoupledConsensusModel.Sts.Record
open SpecRecord.NodeFacts SpecRecord.NoRaise
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-- `m >>= f` can return `b` when `m` can return `a` and `f a` can return `b`. -/
theorem returns_bind_of {α β : Type} {m : DC.NDRE α} {f : α → DC.NDRE β} {a : α} {b : β}
    (h1 : m ⇢ a) (h2 : f a ⇢ b) : (m >>= f) ⇢ b := by
  unfold Returns at *
  simp only [ExceptT.run_bind, Set.bind_def, Set.mem_iUnion]
  exact ⟨_, h1, h2⟩

/-- When the tick from a reached node state running as `v` proposes, the member proposal duty of
    `S.node v` on the staged store under the phase tick's cache `c` has an outcome. -/
theorem propose_outcome (S : Setup V) (v : V) (n : (Model.spec (V := V)).N) (t : Time)
    (out : (Model.spec (V := V)).N × List (NamedObject V))
    (hout : (Model.spec (V := V)).tick S v n t ⇢ out)
    (hn : (Model.spec (V := V)).reachedNode n) (hv : n.val.v = v)
    (hcP : condP (Setup.toSpec S).C (Setup.toSpec S).P n.val t)
    {c : (Model.spec (V := V)).Cache}
    (hc : (Model.spec (V := V)).onPhaseTick S.E S.hc n.st.core.toHealing t n.cache ⇢ c) :
    ∃ D : (Model.spec (V := V)).NS × Option (NamedBlock V),
      (Model.spec (V := V)).duties_propose_block_with c S.E S.hc S.cfg (S.node v)
        ((Model.spec (V := V)).ns_setClock S.E n.st t) ⇢ D := by
  obtain ⟨sent, hrun, -⟩ := NodeFacts.tick_out S v n t out hout
  obtain ⟨st0, st2, st3, st4, st5, sh5, l1, l2, h0, hP1, -, -, hV0, -, hC0, -, hA0, hn'⟩ :=
    tick_detail hrun
  obtain ⟨B, hst2, -⟩ := NodeFacts.propose_block_run (hP1 hcP)
  obtain ⟨hst3, -⟩ := hV0 (condP_not_condV hcP)
  have hst4 := hC0 (condP_not_condC hcP)
  obtain ⟨hst5, -, -⟩ := hA0 (condP_not_condA hcP)
  obtain ⟨st0', h0', hc0, e0, hr, hct⟩ := onPhaseTick_eq S n t hn hc
  obtain rfl : st0' = st0 := Except.ok.inj (h0'.symm.trans h0)
  obtain ⟨hstage, hinv⟩ := staged_eq S n t hn e0
  have hext : (Member.externalOfNode (S.node v)).new_root (S.node v).val_index =
      (Setup.toSpec S).X.new_root (S.node v).val_index := by
    rw [S.node_val_index]; rfl
  set X := (Model.spec (V := V)).ns_setClock S.E n.st t with hX
  have h' : (Spec.Protocol.propose_block (Spec.Config.toSpec S.E S.hc S.cfg)
      (Spec.Provisional.toSpec S.E) (Member.externalOfNode (S.node v)) (S.node v).val_index
      { Spec.Store.ofImage X.val with saved_grades :=
        (Spec.Protocol.advance_to_round (X.val.contractOfImage c)
          ((Spec.Config.toSpec S.E S.hc S.cfg).round_of X.val.s)) }).run [] =
        .ok (st2, l1) := by
    rw [handed_eq X.val hinv hct (r := (Spec.Config.toSpec S.E S.hc S.cfg).round_of X.val.s) hr,
      propose_block_external hext, S.node_val_index, hstage, ← hv]
    exact hP1 hcP
  have hr1 := Member.duties_propose_block_with_returns_of_ok c S.E S.hc S.cfg (S.node v) X.val h'
  have hok5 : StoreOk (Spec.make_grades_compatible_with_finalized st5) := by
    have h := out.1.property
    rw [hn'] at h
    exact h
  have hok2 : StoreOk st2 := by
    rw [hst5, hst4, hst3] at hok5
    exact NonEmpty.storeOk_with_saved_grades hok5 st2.saved_grades
  exact ⟨(⟨{ st2 with saved_grades := c }, NonEmpty.storeOk_with_saved_grades hok2 c⟩,
    (Member.firstSentBlock l1).map Spec.Block.toProofNamed),
    (returns_preimageOutcomes _ _ _).2 hr1⟩

end SpecRecord.TickReached


namespace SpecRecord.TickReached

open DecoupledConsensusModel DecoupledConsensusModel.Execution DecoupledConsensusModel.Sts
open DecoupledConsensusModel.Sts.Record
open SpecRecord.NodeFacts
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

omit [Inhabited V] in
/-- The objects a tick sends before its attestation step are blocks and Goldfish votes. -/
theorem no_attest_before {C : Spec.Config} {P : Spec.Provisional V}
    {X : Spec.External V} {v : V} {c1 c2 : Prop}
    {st1 st2 st3 : Spec.Store V} {l1 l2 : List (Spec.NamedObject V)}
    (hP1 : c1 → (Spec.Protocol.propose_block C P X v st1).run [] = .ok (st2, l1))
    (hP0 : ¬ c1 → st2 = st1 ∧ l1 = [])
    (hV1 : c2 → (Spec.Protocol.goldfish_vote C P v st2).run l1 = .ok (st3, l2))
    (hV0 : ¬ c2 → st3 = st2 ∧ l2 = l1) (row : Spec.Attestation V) :
    Spec.NamedObject.attest row ∉ l2 := by
  have h1 : Spec.NamedObject.attest row ∉ l1 := by
    by_cases hc : c1
    · obtain ⟨B, -, hl⟩ := propose_block_run (hP1 hc)
      rw [hl]; simp
    · rw [(hP0 hc).2]; simp
  by_cases hc : c2
  · rcases goldfish_vote_run (hV1 hc) with ⟨-, hl⟩ | ⟨u, -, hl⟩
    · rw [hl]; exact h1
    · rw [hl]; simp [h1]
  · rw [(hV0 hc).2]; exact h1

/-- The store the tick's attestation step reads is at the slot of `t`. -/
theorem attest_store_slot {C : Spec.Config} {P : Spec.Provisional V}
    {X : Spec.External V} {v : V} {t : Spec.Time} {c1 c2 c3 : Prop}
    {st0 st2 st3 st4 : Spec.Store V} {l1 l2 : List (Spec.NamedObject V)}
    (hP1 : c1 → (Spec.Protocol.propose_block C P X v
      { st0 with t := t, s := C.slotOf t }).run [] = .ok (st2, l1))
    (hP0 : ¬ c1 → st2 = { st0 with t := t, s := C.slotOf t } ∧ l1 = [])
    (hV1 : c2 → (Spec.Protocol.goldfish_vote C P v st2).run l1 = .ok (st3, l2))
    (hV0 : ¬ c2 → st3 = st2 ∧ l2 = l1)
    (hC1 : c3 → Spec.Protocol.update_confirmation C st3 (C.slotOf t - 1) = .ok st4)
    (hC0 : ¬ c3 → st4 = st3) :
    st4.s = C.slotOf t := by
  have h2 : st2.s = C.slotOf t := by
    by_cases hc : c1
    · obtain ⟨B, hst, -⟩ := propose_block_run (hP1 hc)
      rw [hst, HandlersFacts.on_block_s, HandlersFacts.admitBlockCore_s]
    · rw [(hP0 hc).1]
  have h3 : st3.s = C.slotOf t := by
    by_cases hc : c2
    · rcases goldfish_vote_run (hV1 hc) with ⟨hst, -⟩ | ⟨u, hst, -⟩
      · rw [hst]; exact h2
      · obtain ⟨gv, tv, e⟩ := on_goldfish_vote_checked_frame P st2 u
        rw [hst, e]; exact h2
    · rw [(hV0 hc).1]; exact h2
  by_cases hc : c3
  · rw [update_confirmation_ok (hC1 hc)]; exact h3
  · rw [hC0 hc]; exact h3

/-- An attestation the tick sends when the attestation test holds is `create` of the node's signing
    history on an input of the node's validator and of the round of `t`'s slot. -/
theorem tick_attest_input_round {C : Spec.Config} {P : Spec.Provisional V}
    {X : Spec.External V} {n n' : Spec.NodeState V}
    {t : Spec.Time} {sent : List (Spec.NamedObject V)}
    (h : (Spec.tick C P X n t).run [] = .ok (n', sent))
    {row : Spec.Attestation V} (hrow : Spec.NamedObject.attest row ∈ sent) :
    condA C n t ∧ ∃ i : Spec.Protocol.AttestationInput V, i.val_index = n.v ∧
      i.round = C.round_of (C.slotOf t) ∧ row = (Spec.Protocol.create n.signingHistory i).2 := by
  obtain ⟨st0, st2, st3, st4, st5, sh5, l1, l2, -, hP1, hP0, hV1, hV0, hC1, hC0, hA1, hA0, -⟩ :=
    tick_detail h
  have hnot := no_attest_before hP1 hP0 hV1 hV0 row
  by_cases ha : condA C n t
  · obtain ⟨row', hb, -, hs⟩ := attest_run (hA1 ha)
    rw [hs] at hrow
    rcases List.mem_append.mp hrow with hm | hm
    · exact absurd hm hnot
    · have e : row = row' := by
        have := List.mem_singleton.mp hm
        cases this; rfl
      subst e
      obtain ⟨i, -, hiv, hir, hp⟩ := SpecRecord.ContractImages.build_attestation_shape hb
      refine ⟨ha, i, hiv, ?_, congrArg Prod.snd hp⟩
      rw [hir, attest_store_slot hP1 hP0 hV1 hV0 hC1 hC0]
  · rw [(hA0 ha).2.2] at hrow
    exact absurd hrow hnot

end SpecRecord.TickReached


namespace DecoupledConsensusModel.Sts.Record

open DecoupledConsensusModel.Execution
open scoped DC
open SpecRecord SpecRecord.TickReached SpecRecord.NodeFacts
open SpecRecord.NoRaise (StoreOk)

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-- The field `block_mem_on_tick_emit` of `NodeFacts` at `Model.spec`: if `n` is reached and
    runs as `v`, a block `B` that `v`'s tick at `t` sends is sent at the proposal time of `t`'s
    slot, a slot after genesis whose proposer is `v`, and is the block of every outcome of the
    member proposal duty of `S.node v` on `n`'s store staged to `t` under every outcome of the phase
    tick. -/
theorem _root_.SpecRecord.NodeFacts.spec_block_mem_on_tick_emit :
    ∀ (S : Setup V) (v : V) (n : (Model.spec (V := V)).N) (t : Time)
      (out : (Model.spec (V := V)).N × List (NamedObject V)) (hout : (Model.spec (V := V)).tick S v n t ⇢ out) {B : NamedBlock V}
      (h : NamedObject.block B ∈ out.2)
      (hn : (Model.spec (V := V)).reachedNode n) (hv : (Model.spec (V := V)).runs_as n v),
      (0 < S.E.slotOf t ∧ t = (Model.spec (V := V)).proposal_time S.E (S.E.slotOf t) ∧
          S.E.proposer (S.E.slotOf t) = v) ∧
        ∀ (c : (Model.spec (V := V)).Cache), (Model.spec (V := V)).onPhaseTick S.E S.hc n.st.core.toHealing t n.cache ⇢ c →
        ∀ (D : (Model.spec (V := V)).NS × Option (NamedBlock V)),
          (Model.spec (V := V)).duties_propose_block_with ((Model.spec (V := V)).frameContract c) S.E S.hc S.cfg (S.node v)
            ((Model.spec (V := V)).ns_setClock S.E n.st t) ⇢ D →
          D.2 = some B := by
  intro S v n t out hout B h hn hv
  have hv' : n.val.v = v := hv
  obtain ⟨sent, hrun, hsent⟩ := NodeFacts.tick_out S v n t out hout
  obtain ⟨st0, st2, st3, st4, st5, sh5, l1, l2, h0, hP1, -, -, hV0, -, -, -, hA0, -⟩ :=
    tick_detail hrun
  rw [hsent] at h
  obtain ⟨o, ho, hoB⟩ := List.mem_map.mp h
  rcases NodeFacts.tick_sent hrun ho with ⟨B', rfl, hcP⟩ | ⟨u, rfl, -⟩ | ⟨row, rfl, -⟩
  · simp only [Spec.NamedObject.toProof, NamedObject.block.injEq] at hoB
    subst hoB
    obtain ⟨B'', -, hl1⟩ := NodeFacts.propose_block_run (hP1 hcP)
    have hs : sent = [Spec.NamedObject.block B''] := by
      rw [(hA0 (condP_not_condA hcP)).2.2, (hV0 (condP_not_condV hcP)).2, hl1]; rfl
    rw [hs, List.mem_singleton, Spec.NamedObject.block.injEq] at ho
    subst ho
    have hcP' := hcP
    obtain ⟨hpos, hc⟩ := hcP'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · rw [← NodeFacts.slotOf_eq]; exact hpos
    · rw [← NodeFacts.slotOf_eq]; exact hc.1.1
    · rw [← NodeFacts.slotOf_eq, ← hv']; exact hc.1.2
    · intro c hc' D hD
      obtain ⟨st0', h0', -, e0, hr, hct⟩ := onPhaseTick_eq S n t hn hc'
      obtain rfl : st0' = st0 := Except.ok.inj (h0'.symm.trans h0)
      obtain ⟨hstage, hinv⟩ := staged_eq S n t hn e0
      have hrun' : (Spec.Protocol.propose_block (Setup.toSpec S).C (Setup.toSpec S).P
          (Setup.toSpec S).X v { ((Model.spec (V := V)).ns_setClock S.E n.st t).val with
            saved_grades := c }).run [] = .ok (st2, l1) := by
        rw [hstage, ← hv']; exact hP1 hcP
      obtain ⟨-, hD2⟩ := propose_member_eq S v _ hinv hct hr hrun' hD
      rw [hD2, hl1]
      rfl
  · simp only [Spec.NamedObject.toProof, reduceCtorEq] at hoB
  · simp only [Spec.NamedObject.toProof, reduceCtorEq] at hoB

/-- The field `named_tick_preserves` of `NodeFacts` at `Model.spec`: if `n` is reached and runs
    as `v`, and `P` holds of `n`'s store staged to `t` and is kept by writing saved grades, by the
    clip and by every member duty of `S.node v`, then `P` holds of the store of every outcome of
    `v`'s tick at `t`. -/
theorem _root_.SpecRecord.NodeFacts.spec_named_tick_preserves :
    ∀ (P : (Model.spec (V := V)).NS → Prop) (S : Setup V) (v : V) (n : (Model.spec (V := V)).N) (t : Time)
      (hp : ∀ c : (Model.spec (V := V)).Cache, (Model.spec (V := V)).onPhaseTick S.E S.hc n.st.core.toHealing t n.cache ⇢ c →
        ∀ st, P st → ∀ D : (Model.spec (V := V)).NS × Option (NamedBlock V),
          (Model.spec (V := V)).duties_propose_block_with ((Model.spec (V := V)).frameContract c) S.E S.hc S.cfg (S.node v) st ⇢ D → P D.1)
      (hv : ∀ c : (Model.spec (V := V)).Cache, (Model.spec (V := V)).onPhaseTick S.E S.hc n.st.core.toHealing t n.cache ⇢ c →
        ∀ st, P st → ∀ D : (Model.spec (V := V)).NS × Option (GoldfishVote V),
          (Model.spec (V := V)).duties_goldfish_vote_with ((Model.spec (V := V)).frameContract c) S.E S.hc (S.node v) st ⇢ D → P D.1)
      (hcf : ∀ c : (Model.spec (V := V)).Cache, (Model.spec (V := V)).onPhaseTick S.E S.hc n.st.core.toHealing t n.cache ⇢ c →
        ∀ st s, P st → ∀ st' : (Model.spec (V := V)).NS,
          (Model.spec (V := V)).duties_update_confirmation_with ((Model.spec (V := V)).frameContract c) S.E S.hc st s ⇢ st' → P st')
      (ha : ∀ c : (Model.spec (V := V)).Cache, (Model.spec (V := V)).onPhaseTick S.E S.hc n.st.core.toHealing t n.cache ⇢ c →
        ∀ st record, P st → ∀ D : (Model.spec (V := V)).NS × (Model.spec (V := V)).NR × NamedAttestation V,
          (Model.spec (V := V)).duties_attest_with ((Model.spec (V := V)).frameContract c) S.E S.hc (S.node v) st record ⇢ D → P D.1)
      (hsc : ∀ st c, P st → P ((Model.spec (V := V)).store_with_cache st c))
      (hmg : ∀ st, P st → P ((Model.spec (V := V)).make_grades_compatible_with_finalized st))
      (h : P ((Model.spec (V := V)).ns_setClock S.E n.st t))
      (out : (Model.spec (V := V)).N × List (NamedObject V)) (hout : (Model.spec (V := V)).tick S v n t ⇢ out)
      (hn : (Model.spec (V := V)).reachedNode n) (hruns : (Model.spec (V := V)).runs_as n v),
      P out.1.st := by
  intro P S v n t hp hv hcf ha hsc hmg h out hout hn hruns
  have hv' : n.val.v = v := hruns
  obtain ⟨c, hc⟩ := SpecRecord.GradesFacts.spec_onPhaseTick_nonempty S.E S.hc
    n.st.core.toHealing t n.cache
  obtain ⟨sent, hrun, -⟩ := NodeFacts.tick_out S v n t out hout
  obtain ⟨st0, st2, st3, st4, st5, sh5, l1, l2, h0, hP1, hP0, hV1, hV0, hC1, hC0, hA1, hA0, hn'⟩ :=
    tick_detail hrun
  obtain ⟨st0', h0', hc0, e0, hr, hct⟩ := onPhaseTick_eq S n t hn hc
  obtain rfl : st0 = st0' := Except.ok.inj (h0.symm.trans h0')
  obtain ⟨hstage, hinv⟩ := staged_eq S n t hn e0
  set X := (Model.spec (V := V)).ns_setClock S.E n.st t with hX
  set X1 := (Model.spec (V := V)).store_with_cache X c with hX1
  have hPX1 : P X1 := hsc X c h
  have hX1v : X1.val = { st0 with t := t, s := (Setup.toSpec S).C.slotOf t } := hstage
  have hinv1 : Inv3 X1.val := hinv
  have hw : ({ X1.val with saved_grades := c } : Spec.Store V) =
      { st0 with t := t, s := (Setup.toSpec S).C.slotOf t } := hstage
  have hokout : StoreOk (Spec.make_grades_compatible_with_finalized st5) := by
    have h' := out.1.property
    rw [hn'] at h'
    exact h'
  have hok5 : StoreOk st5 := NonEmpty.storeOk_with_saved_grades hokout st5.saved_grades
  have hout5 : out.1.val.st = Spec.make_grades_compatible_with_finalized st5 := by
    rw [hn']
  suffices key : ∃ Y : (Model.spec (V := V)).NS, P Y ∧ Y.val = st5 by
    obtain ⟨Y, hPY, hY⟩ := key
    have e : out.1.st = (Model.spec (V := V)).make_grades_compatible_with_finalized Y :=
      Subtype.ext (by show out.1.val.st = _; rw [hout5, ← hY]; rfl)
    rw [e]
    exact hmg Y hPY
  by_cases hcP : condP (Setup.toSpec S).C (Setup.toSpec S).P n.val t
  · -- the proposal alone
    have hrunp := hP1 hcP
    obtain ⟨B, hst2, -⟩ := NodeFacts.propose_block_run hrunp
    obtain ⟨hst3, -⟩ := hV0 (condP_not_condV hcP)
    have hst4 := hC0 (condP_not_condC hcP)
    obtain ⟨hst5, -, -⟩ := hA0 (condP_not_condA hcP)
    have hok2 : StoreOk st2 := by rw [← hst3, ← hst4, ← hst5]; exact hok5
    have hrunp' : (Spec.Protocol.propose_block (Setup.toSpec S).C (Setup.toSpec S).P
        (Setup.toSpec S).X v { X1.val with saved_grades := c }).run [] = .ok (st2, l1) := by
      rw [hw, ← hv']; exact hrunp
    obtain ⟨D, hD, hD1⟩ := propose_member_exists S v X1 hinv1 hct hr hrunp' hok2
    have hsg : st2.saved_grades = c := by
      rw [hst2, NodeFacts.on_block_saved_grades, hc0]
    refine ⟨D.1, hp c hc X1 hPX1 D hD, ?_⟩
    rw [hD1, with_saved_grades_self st2 hsg, hst5, hst4, hst3]
  by_cases hcV : condV (Setup.toSpec S).C n.val t
  · -- the vote alone
    obtain ⟨hst2, hl1⟩ := hP0 hcP
    have hrunv := hV1 hcV
    rw [hl1, hst2] at hrunv
    have hst4 := hC0 (condV_not_condC hcV)
    obtain ⟨hst5, -, -⟩ := hA0 (condV_not_condA hcV)
    have hok3 : StoreOk st3 := by rw [← hst4, ← hst5]; exact hok5
    have hrunv' : (Spec.Protocol.goldfish_vote (Setup.toSpec S).C (Setup.toSpec S).P
        v { X1.val with saved_grades := c }).run [] = .ok (st3, l2) := by
      rw [hw, ← hv']; exact hrunv
    obtain ⟨D, hD, hD1⟩ := vote_member_exists S v X1 hinv1 hct hr hrunv' hok3
    have hsg : st3.saved_grades = c := by
      rcases NodeFacts.goldfish_vote_run hrunv with ⟨e, -⟩ | ⟨u, e, -⟩
      · rw [e, hc0]
      · rw [e, NodeFacts.on_goldfish_vote_checked_saved_grades, hc0]
    refine ⟨D.1, hv c hc X1 hPX1 D hD, ?_⟩
    rw [hD1, with_saved_grades_self st3 hsg, hst5, hst4]
  obtain ⟨hst2, hl1⟩ := hP0 hcP
  obtain ⟨hst3, hl2⟩ := hV0 hcV
  by_cases hcC : condC (Setup.toSpec S).C n.val t
  · -- the confirmation, then the attestation when it runs
    have hrunc := hC1 hcC
    rw [hst3, hst2] at hrunc
    have hrunc' : Spec.Protocol.update_confirmation (Setup.toSpec S).C
        { X1.val with saved_grades := c } ((Setup.toSpec S).C.slotOf t - 1) = .ok st4 := by
      rw [hw]; exact hrunc
    have e4 := NodeFacts.update_confirmation_ok hrunc
    have hT4 : st4.T = n.val.st.T := by rw [e4, e0]
    have hok1 : StoreOk ({ st0 with t := t, s := (Setup.toSpec S).C.slotOf t } :
        Spec.Store V) := by rw [← hX1v]; exact X1.property
    have hok4 : StoreOk st4 := NonEmpty.storeOk_update_confirmation hrunc hok1
    obtain ⟨st', hst', hst'v⟩ := confirm_member_exists S X1 hinv1 hct hr _ hrunc' hok4
    have hP' := hcf c hc X1 _ hPX1 st' hst'
    have hsg4 : st4.saved_grades = c := by rw [e4, hc0]
    have hst'4 : st'.val = st4 := by rw [hst'v, with_saved_grades_self st4 hsg4]
    by_cases hcA : condA (Setup.toSpec S).C n.val t
    · have hinv4 : Inv3 st'.val := by
        rw [hst'4]
        refine inv3_reach (Relation.ReflTransGen.single
          (StoreSteps.update_confirmation_step _ (Setup.toSpec S).P t _ st4 _ hrunc)) ?_ ?_
        · rw [hT4]; exact n.property.2.1
        · rw [← hX1v]; exact hinv1
      have hct4 : Spec.Store.ContractInTree st'.val.T c := by
        rw [hst'4, hT4]; exact hct
      have hr4 : c.round = (Setup.toSpec S).C.round_of st'.val.s := by
        rw [hst'4, e4, e0, hr]
      have hruna := hA1 hcA
      obtain ⟨row, -, hst5, hs⟩ := NodeFacts.attest_run hruna
      rw [hl2, hl1] at hs
      rw [hl2, hl1, hs, List.nil_append] at hruna
      have hruna' : (Spec.Protocol.attest (Setup.toSpec S).C v
          { st'.val with saved_grades := c } n.record).run [] =
            .ok ((st5, sh5), [Spec.NamedObject.attest row]) := by
        rw [with_saved_grades_self _ (by rw [hst'4]; exact hsg4), hst'4, ← hv']
        exact hruna
      obtain ⟨D, hD, hD1⟩ := attest_member_exists S v st' hinv4 hct4 hr4 _ hruna' hok5
      have hsg5 : st5.saved_grades = c := by
        rw [hst5, NodeFacts.admit_attestation_saved_grades, hsg4]
      exact ⟨D.1, ha c hc st' n.record hP' D hD, by rw [hD1, with_saved_grades_self st5 hsg5]⟩
    · obtain ⟨hst5, -, -⟩ := hA0 hcA
      exact ⟨st', hP', by rw [hst'4, hst5]⟩
  · -- no duty
    have hst4 := hC0 hcC
    obtain ⟨hst5, -, -⟩ := hA0 (fun h => hcC (condC_of_condA h))
    refine ⟨X1, hPX1, ?_⟩
    rw [hX1v, hst5, hst4, hst3, hst2]

/-- The field `gfVote_emitted_shape` of `NodeFacts` at `Model.spec`: if `n` is reached and runs
    as `v`, a Goldfish vote `u` that `v`'s tick at `t` sends is sent at the vote time of `t`'s slot,
    a slot after genesis, is the vote of every outcome of the member vote duty of `S.node v` there,
    is signed by `v` and is for `t`'s slot. -/
theorem _root_.SpecRecord.NodeFacts.spec_gfVote_emitted_shape :
    ∀ (S : Setup V) (v : V) (n : (Model.spec (V := V)).N) (t : Time)
      (out : (Model.spec (V := V)).N × List (NamedObject V)) (hout : (Model.spec (V := V)).tick S v n t ⇢ out) (u : GoldfishVote V),
      NamedObject.gfVote u ∈ out.2 →
      ∀ (hn : (Model.spec (V := V)).reachedNode n) (hv : (Model.spec (V := V)).runs_as n v),
      0 < S.E.slotOf t ∧ t = (Model.spec (V := V)).vote_time S.E (S.E.slotOf t) ∧
        (∀ c : (Model.spec (V := V)).Cache, (Model.spec (V := V)).onPhaseTick S.E S.hc n.st.core.toHealing t n.cache ⇢ c →
          ∀ D : (Model.spec (V := V)).NS × Option (GoldfishVote V),
            (Model.spec (V := V)).duties_goldfish_vote_with ((Model.spec (V := V)).frameContract c) S.E S.hc (S.node v)
              ((Model.spec (V := V)).ns_setClock S.E n.st t) ⇢ D → D.2 = some u) ∧
        u.val_index = v ∧ u.slot = S.E.slotOf t := by
  intro S v n t out hout u h₁ hn hv
  have hv' : n.val.v = v := hv
  obtain ⟨sent, hrun, hsent⟩ := NodeFacts.tick_out S v n t out hout
  have h₁' := h₁
  rw [hsent] at h₁'
  obtain ⟨o, ho, hou⟩ := List.mem_map.mp h₁'
  have hcV : condV (Setup.toSpec S).C n.val t := by
    rcases NodeFacts.tick_sent hrun ho with ⟨B, rfl, -⟩ | ⟨u', rfl, hc⟩ | ⟨row, rfl, -⟩
    · simp only [Spec.NamedObject.toProof, reduceCtorEq] at hou
    · exact hc
    · simp only [Spec.NamedObject.toProof, reduceCtorEq] at hou
  obtain ⟨c₀, hc₀⟩ := SpecRecord.GradesFacts.spec_onPhaseTick_nonempty S.E S.hc
    n.st.core.toHealing t n.cache
  obtain ⟨D₀, hD₀⟩ := SpecRecord.DutiesFacts.spec_goldfish_vote_with_nonempty c₀ S.E S.hc
    (S.node v) ((Model.spec (V := V)).ns_setClock S.E n.st t)
  obtain ⟨st3, l, -, -, hout2, -, hl⟩ := vote_tick S v n t out hout hn hv' hcV hc₀ hD₀
  have hu : ∃ root, u = Spec.GoldfishVote.toProof ⟨v, (Setup.toSpec S).C.slotOf t, root⟩ ∧
      l = [Spec.NamedObject.gfVote ⟨v, (Setup.toSpec S).C.slotOf t, root⟩] := by
    rw [hout2] at h₁
    rcases hl with rfl | ⟨root, rfl⟩
    · exact absurd h₁ (by simp)
    · refine ⟨root, ?_, rfl⟩
      simp only [List.map_cons, List.map_nil, List.mem_singleton,
        Spec.NamedObject.toProof, NamedObject.gfVote.injEq] at h₁
      exact h₁
  obtain ⟨root, rfl, hl'⟩ := hu
  have hc' := hcV
  obtain ⟨hpos, hc'⟩ := hc'
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc'
  refine ⟨?_, ?_, ?_, rfl, ?_⟩
  · rw [← NodeFacts.slotOf_eq]; exact hpos
  · rw [← NodeFacts.slotOf_eq]; exact hc'.1
  · intro c hc D hD
    obtain ⟨st3', l', -, -, hout2', hD2, hl2⟩ := vote_tick S v n t out hout hn hv' hcV hc hD
    have el : l'.map Spec.NamedObject.toProof = l.map Spec.NamedObject.toProof := by
      rw [← hout2, ← hout2']
    rw [hl'] at el
    rcases hl2 with rfl | ⟨root', rfl⟩
    · simp at el
    · simp only [List.map_cons, List.map_nil, Spec.NamedObject.toProof, List.cons.injEq,
        NamedObject.gfVote.injEq, and_true] at el
      rw [hD2]
      simp [Member.firstSentGoldfishVote, el]
  · show (Setup.toSpec S).C.slotOf t = S.E.slotOf t
    exact NodeFacts.slotOf_eq S t

/-- The field `tick_bodies_and_coreT_from_proposal` of `NodeFacts` at `Model.spec`: if `n` is
    reached and runs as `v`, then when `v` proposes at `t` the bodies and the tree of every outcome
    of `v`'s tick at `t` are those of every outcome of the member proposal duty, and otherwise those
    of `n`'s store staged to `t`. -/
theorem _root_.SpecRecord.NodeFacts.spec_tick_bodies_and_coreT_from_proposal :
    ∀ (S : Setup V) (v : V) (n : (Model.spec (V := V)).N) (t : Time)
      (out : (Model.spec (V := V)).N × List (NamedObject V)) (hout : (Model.spec (V := V)).tick S v n t ⇢ out)
      (hn : (Model.spec (V := V)).reachedNode n) (hv : (Model.spec (V := V)).runs_as n v),
      let s := S.E.slotOf t
      let st0 := (Model.spec (V := V)).ns_setClock S.E n.st t
      ((0 < s ∧ t = (Model.spec (V := V)).proposal_time S.E s ∧ S.E.proposer s = (S.node v).val_index ∧
          (Model.spec (V := V)).awake_for_grade1 S v n ((Model.spec (V := V)).round_of S.hc s)) →
        ∀ c : (Model.spec (V := V)).Cache, (Model.spec (V := V)).onPhaseTick S.E S.hc n.st.core.toHealing t n.cache ⇢ c →
        ∀ D : (Model.spec (V := V)).NS × Option (NamedBlock V),
          (Model.spec (V := V)).duties_propose_block_with ((Model.spec (V := V)).frameContract c) S.E S.hc S.cfg (S.node v) st0 ⇢ D →
          out.1.st.bodies = D.1.bodies ∧ out.1.st.core.T = D.1.core.T) ∧
      ((Model.spec (V := V)).runs_as n v →
        ¬ (0 < s ∧ t = (Model.spec (V := V)).proposal_time S.E s ∧ S.E.proposer s = (S.node v).val_index ∧
          (Model.spec (V := V)).awake_for_grade1 S v n ((Model.spec (V := V)).round_of S.hc s)) →
        out.1.st.bodies = st0.bodies ∧ out.1.st.core.T = st0.core.T) := by
  intro S v n t out hout hn hv
  have hv' : n.val.v = v := hv
  dsimp only
  refine ⟨?_, ?_⟩
  · rintro ⟨hpos, ht, hpr, hrun⟩ c hc D hD
    have hcP : condP (Setup.toSpec S).C (Setup.toSpec S).P n.val t := by
      have h := condP_of S v n hpos (hpr.trans (by rw [S.node_val_index, ← hv'])) hrun
      rwa [← ht] at h
    obtain ⟨st2, B', hout1, hD1, -, -⟩ := proposal_tick S v n t out hout hn hv' hcP hc hD
    refine ⟨?_, ?_⟩
    · show Member.bodies out.1.val.st = Member.bodies D.1.val
      rw [hout1, hD1]
      rfl
    · show Member.store_T out.1.val.st = Member.store_T D.1.val
      rw [hout1, hD1]
      rfl
  · intro _ hnot
    obtain ⟨sent, hrun, -⟩ := NodeFacts.tick_out S v n t out hout
    have hcP : ¬ condP (Setup.toSpec S).C (Setup.toSpec S).P n.val t := by
      intro hcP
      apply hnot
      have hc := hcP
      obtain ⟨hpos, hc⟩ := hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨a, ha, hle⟩ := awake_of_condP hcP
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [← NodeFacts.slotOf_eq]; exact hpos
      · rw [← NodeFacts.slotOf_eq]; exact hc.1.1
      · rw [← NodeFacts.slotOf_eq, S.node_val_index, ← hv']; exact hc.1.2
      · refine ⟨a, ha, ?_⟩
        rw [← NodeFacts.slotOf_eq]; exact hle
    obtain ⟨hT, -⟩ := tick_treeEq_of_not_condP hrun hcP
    refine ⟨?_, ?_⟩
    · show Member.bodies out.1.val.st = Member.bodies n.val.st
      unfold Member.bodies
      rw [hT]
    · show out.1.val.st.T.image Spec.Block.toProof =
        n.val.st.T.image Spec.Block.toProof
      rw [hT]

/-- The field `tick_at_action_awake` of `NodeFacts` at `Model.spec`: if `before` is reached,
    runs as `v` and is awake for round `r`'s grade-2 test, every outcome of `v`'s tick at `r`'s
    action time sends exactly the attestation of the member attestation duty on the member
    confirmation's store. -/
theorem _root_.SpecRecord.NodeFacts.spec_tick_at_action_awake :
    ∀ (S : Setup V) (v : V) (before : (Model.spec (V := V)).N) (r : Round)
      (out : (Model.spec (V := V)).N × List (NamedObject V)) (hout : (Model.spec (V := V)).tick S v before ((Model.spec (V := V)).a S.hc S.E.Δ r) ⇢ out)
      (c : (Model.spec (V := V)).Cache) (hc : (Model.spec (V := V)).onPhaseTick S.E S.hc before.st.core.toHealing ((Model.spec (V := V)).a S.hc S.E.Δ r) before.cache ⇢ c)
      (st : (Model.spec (V := V)).NS) (hst : (Model.spec (V := V)).duties_update_confirmation_with ((Model.spec (V := V)).gradeContract c) S.E S.hc
        ((Model.spec (V := V)).ns_setClock S.E before.st ((Model.spec (V := V)).a S.hc S.E.Δ r)) (S.E.slotOf ((Model.spec (V := V)).a S.hc S.E.Δ r) - 1) ⇢ st)
      (D : (Model.spec (V := V)).NS × (Model.spec (V := V)).NR × NamedAttestation V)
      (hD : (Model.spec (V := V)).duties_attest_with ((Model.spec (V := V)).gradeContract c) S.E S.hc (S.node v) st before.record ⇢ D)
      (hrun : (Model.spec (V := V)).awake_for_grade2 S v before r)
      (hn : (Model.spec (V := V)).reachedNode before) (hv : (Model.spec (V := V)).runs_as before v),
      out.2 = [NamedObject.attest D.2.2] := by
  intro S v before r out hout c hc st hst D hD hrun hn hv
  have hv' : before.val.v = v := hv
  have hcA := condA_of S v before r hrun
  rw [← NodeFacts.slotOf_eq] at hst
  obtain ⟨st5, row, -, -, hout2, hD3⟩ := action_tick S v before _ out hout hn hv' hcA hc hst hD
  rw [hout2, hD3]

/-- The field `on_tick_emit_vote_mem_of_outcomes` of `NodeFacts` at `Model.spec`: if `n` is
    reached, runs as `v` and is awake for the grade-1 test of slot `s`'s round, the vote `u` of an
    outcome of the member vote duty at `s`'s vote time is sent by every outcome of `v`'s tick there. -/
theorem _root_.SpecRecord.NodeFacts.spec_on_tick_emit_vote_mem_of_outcomes :
    ∀ (S : Setup V) (v : V) (n : (Model.spec (V := V)).N) (s : Slot) (hs : 0 < s)
      {u : GoldfishVote V}
      (c : (Model.spec (V := V)).Cache) (hc : (Model.spec (V := V)).onPhaseTick S.E S.hc n.st.core.toHealing ((Model.spec (V := V)).vote_time S.E s) n.cache ⇢ c)
      (D : (Model.spec (V := V)).NS × Option (GoldfishVote V))
      (hD : (Model.spec (V := V)).duties_goldfish_vote_with ((Model.spec (V := V)).gradeContract c) S.E S.hc (S.node v)
        ((Model.spec (V := V)).ns_setClock S.E n.st ((Model.spec (V := V)).vote_time S.E s)) ⇢ D)
      (hu : D.2 = some u)
      (out : (Model.spec (V := V)).N × List (NamedObject V)) (hout : (Model.spec (V := V)).tick S v n ((Model.spec (V := V)).vote_time S.E s) ⇢ out)
      (hrun : (Model.spec (V := V)).awake_for_grade1 S v n ((Model.spec (V := V)).round_of S.hc s))
      (hn : (Model.spec (V := V)).reachedNode n) (hv : (Model.spec (V := V)).runs_as n v),
      NamedObject.gfVote u ∈ out.2 := by
  intro S v n s hs u c hc D hD hu out hout hrun hn hv
  have hv' : n.val.v = v := hv
  have hcV := condV_of S v n hs hrun
  obtain ⟨st3, l, -, -, hout2, hD2, hl⟩ := vote_tick S v n _ out hout hn hv' hcV hc hD
  rw [hu] at hD2
  rcases hl with rfl | ⟨root, rfl⟩
  · simp [Member.firstSentGoldfishVote] at hD2
  · simp only [Member.firstSentGoldfishVote, List.findSome?_cons, Option.map_some,
      Option.some.injEq] at hD2
    rw [hout2, hD2]
    exact List.mem_singleton_self _

/-- The field `on_tick_emit_proposal_mem_of_outcomes` of `NodeFacts` at `Model.spec`: if `n` is
    reached, runs as `v`, `v` is slot `s`'s proposer, and `n` is awake for the grade-1 test of `s`'s
    round, the block of every outcome of the member proposal duty at `s`'s proposal time is sent by
    every outcome of `v`'s tick there. -/
theorem _root_.SpecRecord.NodeFacts.spec_on_tick_emit_proposal_mem_of_outcomes :
    ∀ (S : Setup V) (v : V) (n : (Model.spec (V := V)).N) (s : Slot) (hs : 0 < s)
      (hpr : S.E.proposer s = (S.node v).val_index) {B : NamedBlock V}
      (c : (Model.spec (V := V)).Cache) (hc : (Model.spec (V := V)).onPhaseTick S.E S.hc n.st.core.toHealing ((Model.spec (V := V)).proposal_time S.E s) n.cache ⇢ c)
      (D : (Model.spec (V := V)).NS × Option (NamedBlock V))
      (hD : (Model.spec (V := V)).duties_propose_block_with ((Model.spec (V := V)).gradeContract c) S.E S.hc S.cfg (S.node v)
        ((Model.spec (V := V)).ns_setClock S.E n.st ((Model.spec (V := V)).proposal_time S.E s)) ⇢ D)
      (hB : D.2 = some B)
      (out : (Model.spec (V := V)).N × List (NamedObject V)) (hout : (Model.spec (V := V)).tick S v n ((Model.spec (V := V)).proposal_time S.E s) ⇢ out)
      (hrun : (Model.spec (V := V)).awake_for_grade1 S v n ((Model.spec (V := V)).round_of S.hc s))
      (hn : (Model.spec (V := V)).reachedNode n) (hv : (Model.spec (V := V)).runs_as n v),
      NamedObject.block B ∈ out.2 := by
  intro S v n s hs hpr B c hc D hD hB out hout hrun hn hv
  have hv' : n.val.v = v := hv
  have hcP := condP_of S v n hs (hpr.trans (by rw [S.node_val_index, ← hv'])) hrun
  obtain ⟨st2, B', -, -, hout2, hD2⟩ := proposal_tick S v n _ out hout hn hv' hcP hc hD
  rw [hB] at hD2
  rw [hout2, Option.some.inj hD2]
  exact List.mem_singleton_self _

/-- The field `on_tick_emit_proposal_timestamp_block_of_outcomes` of `NodeFacts` at
    `Model.spec`: if `n` is reached, runs as `v`, `v` is slot `s`'s proposer, and `n` is awake
    for the grade-1 test of `s`'s round, every outcome of `v`'s tick at `s`'s proposal time has the
    block stamps of every outcome of the member proposal duty there. -/
theorem _root_.SpecRecord.NodeFacts.spec_on_tick_emit_proposal_timestamp_block_of_outcomes :
    ∀ (S : Setup V) (v : V) (n : (Model.spec (V := V)).N) (s : Slot) (hs : 0 < s)
      (hprop : S.E.proposer s = (S.node v).val_index)
      (c : (Model.spec (V := V)).Cache) (hc : (Model.spec (V := V)).onPhaseTick S.E S.hc n.st.core.toHealing ((Model.spec (V := V)).proposal_time S.E s) n.cache ⇢ c)
      (D : (Model.spec (V := V)).NS × Option (NamedBlock V))
      (hD : (Model.spec (V := V)).duties_propose_block_with ((Model.spec (V := V)).gradeContract c) S.E S.hc S.cfg (S.node v)
        ((Model.spec (V := V)).ns_setClock S.E n.st ((Model.spec (V := V)).proposal_time S.E s)) ⇢ D)
      (out : (Model.spec (V := V)).N × List (NamedObject V)) (hout : (Model.spec (V := V)).tick S v n ((Model.spec (V := V)).proposal_time S.E s) ⇢ out)
      (hrun : (Model.spec (V := V)).awake_for_grade1 S v n ((Model.spec (V := V)).round_of S.hc s))
      (hn : (Model.spec (V := V)).reachedNode n) (hv : (Model.spec (V := V)).runs_as n v),
      out.1.st.core.timestamp_block = D.1.core.timestamp_block := by
  intro S v n s hs hprop c hc D hD out hout hrun hn hv
  have hv' : n.val.v = v := hv
  have hcP := condP_of S v n hs (hprop.trans (by rw [S.node_val_index, ← hv'])) hrun
  obtain ⟨st2, B', hout1, hD1, -, -⟩ := proposal_tick S v n _ out hout hn hv' hcP hc hD
  show Member.store_timestamp_block out.1.val.st = Member.store_timestamp_block D.1.val
  rw [hout1, hD1]
  rfl

/-- The field `tick_fields_from_proposal` of `NodeFacts` at `Model.spec`: if `n` is reached,
    runs as `v`, `v` is the proposer of `t`'s slot, `t` is that slot's proposal time and `n` is
    awake for its grade-1 test, every outcome of `v`'s tick at `t` has the Goldfish votes and vote
    stamps of every outcome of the member proposal duty there. -/
theorem _root_.SpecRecord.NodeFacts.spec_tick_fields_from_proposal :
    ∀ (S : Setup V) (v : V) (n : (Model.spec (V := V)).N) (t : Time)
      (out : (Model.spec (V := V)).N × List (NamedObject V)) (hout : (Model.spec (V := V)).tick S v n t ⇢ out)
      (hdue : 0 < S.E.slotOf t ∧ t = (Model.spec (V := V)).proposal_time S.E (S.E.slotOf t) ∧
        S.E.proposer (S.E.slotOf t) = (S.node v).val_index)
      (hrun : (Model.spec (V := V)).awake_for_grade1 S v n ((Model.spec (V := V)).round_of S.hc (S.E.slotOf t))),
      ∀ c : (Model.spec (V := V)).Cache, (Model.spec (V := V)).onPhaseTick S.E S.hc n.st.core.toHealing t n.cache ⇢ c →
      ∀ D : (Model.spec (V := V)).NS × Option (NamedBlock V),
        (Model.spec (V := V)).duties_propose_block_with ((Model.spec (V := V)).frameContract c) S.E S.hc S.cfg (S.node v)
          ((Model.spec (V := V)).ns_setClock S.E n.st t) ⇢ D →
        ∀ (hn : (Model.spec (V := V)).reachedNode n) (hv : (Model.spec (V := V)).runs_as n v),
        out.1.st.core.gf_votes = D.1.core.gf_votes ∧
          out.1.st.core.timestamp_vote = D.1.core.timestamp_vote := by
  intro S v n t out hout hdue hrun c h₁ D h₂ hn hv
  have hv' : n.val.v = v := hv
  obtain ⟨hpos, ht, hpr⟩ := hdue
  have hcP : condP (Setup.toSpec S).C (Setup.toSpec S).P n.val t := by
    have h := condP_of S v n hpos (hpr.trans (by rw [S.node_val_index, ← hv'])) hrun
    rwa [← ht] at h
  obtain ⟨st2, B', hout1, hD1, -, -⟩ := proposal_tick S v n t out hout hn hv' hcP h₁ h₂
  refine ⟨?_, ?_⟩
  · show Member.store_gf_votes out.1.val.st = Member.store_gf_votes D.1.val
    rw [hout1, hD1]
    rfl
  · show Member.store_timestamp_vote out.1.val.st = Member.store_timestamp_vote D.1.val
    rw [hout1, hD1]
    rfl

/-- The field `advance_tick_of_stage1` of `NodeFacts` at `Model.spec`: if `n` is reached, runs
    as `v` and is awake for the grade-1 test of `t`'s round, and every outcome of `tickStage1` under
    every outcome of the phase tick satisfies `NamedFinalityAdvance`, then so does the store of
    every outcome of `v`'s tick at `t`. -/
theorem _root_.SpecRecord.NodeFacts.spec_advance_tick_of_stage1 :
    ∀ (S : Setup V) (v : V) (n : (Model.spec (V := V)).N) (t : Time)
      (out : (Model.spec (V := V)).N × List (NamedObject V)) (hout : (Model.spec (V := V)).tick S v n t ⇢ out)
      (hrun : (Model.spec (V := V)).awake_for_grade1 S v n ((Model.spec (V := V)).round_of S.hc (S.E.slotOf t))),
      (∀ c : (Model.spec (V := V)).Cache, (Model.spec (V := V)).onPhaseTick S.E S.hc n.st.core.toHealing t n.cache ⇢ c →
        ∀ st₁ : (Model.spec (V := V)).NS,
          Restated.Vocabulary.Proofs.HealingSurface.tickStage1 (Model.spec (V := V)) S ((Model.spec (V := V)).frameContract c) (S.node v) n.st t ⇢ st₁ →
          Restated.Vocabulary.Proofs.HealingSurface.NamedFinalityAdvance (Model.spec (V := V)) S st₁) →
      ∀ (hn : (Model.spec (V := V)).reachedNode n) (hv : (Model.spec (V := V)).runs_as n v),
      Restated.Vocabulary.Proofs.HealingSurface.NamedFinalityAdvance (Model.spec (V := V)) S out.1.st := by
  intro S v n t out hout hrun h₁ hn hv
  have hv' : n.val.v = v := hv
  obtain ⟨c, hc⟩ := SpecRecord.GradesFacts.spec_onPhaseTick_nonempty S.E S.hc
    n.st.core.toHealing t n.cache
  have key : ∃ st₁ : (Model.spec (V := V)).NS,
      Restated.Vocabulary.Proofs.HealingSurface.tickStage1 (Model.spec (V := V)) S
        ((Model.spec (V := V)).frameContract c) (S.node v) n.st t ⇢ st₁ ∧
      out.1.st.bodies = st₁.bodies ∧ out.1.st.core.F = st₁.core.F := by
    by_cases hcP : condP (Setup.toSpec S).C (Setup.toSpec S).P n.val t
    · obtain ⟨D, hD⟩ := propose_outcome S v n t out hout hn hv' hcP hc
      obtain ⟨st2, B, hout1, hD1, -, -⟩ := proposal_tick S v n t out hout hn hv' hcP hc hD
      have hcond : 0 < S.E.slotOf t ∧ t = (Model.spec (V := V)).proposal_time S.E (S.E.slotOf t) ∧
          S.E.proposer (S.E.slotOf t) = (S.node v).val_index := by
        have hc' := hcP
        obtain ⟨hpos, hc'⟩ := hc'
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc'
        refine ⟨?_, ?_, ?_⟩
        · rw [← NodeFacts.slotOf_eq]; exact hpos
        · rw [← NodeFacts.slotOf_eq]; exact hc'.1.1
        · rw [← NodeFacts.slotOf_eq, S.node_val_index, ← hv']; exact hc'.1.2
      refine ⟨D.1, ?_, ?_, ?_⟩
      · unfold Restated.Vocabulary.Proofs.HealingSurface.tickStage1
        rw [if_pos hcond]
        exact returns_bind_of hD ((returns_pure _ _).mpr rfl)
      · show Member.bodies out.1.val.st = Member.bodies D.1.val
        rw [hout1, hD1]; rfl
      · show out.1.val.st.F.toProof = D.1.val.F.toProof
        rw [hout1, hD1]; rfl
    · obtain ⟨sent, hrun', -⟩ := NodeFacts.tick_out S v n t out hout
      have hcond : ¬ (0 < S.E.slotOf t ∧
          t = (Model.spec (V := V)).proposal_time S.E (S.E.slotOf t) ∧
          S.E.proposer (S.E.slotOf t) = (S.node v).val_index) := by
        rintro ⟨hpos, ht, hpr⟩
        apply hcP
        have h := condP_of S v n hpos (hpr.trans (by rw [S.node_val_index, ← hv'])) hrun
        rwa [← ht] at h
      obtain ⟨hT, hF, -⟩ := tick_treeEq_of_not_condP hrun' hcP
      refine ⟨(Model.spec (V := V)).ns_setClock S.E n.st t, ?_, ?_, ?_⟩
      · unfold Restated.Vocabulary.Proofs.HealingSurface.tickStage1
        rw [if_neg hcond]
        exact (returns_pure _ _).mpr rfl
      · show Member.bodies out.1.val.st = Member.bodies n.val.st
        unfold Member.bodies
        rw [hT]
      · show out.1.val.st.F.toProof = n.val.st.F.toProof
        rw [hF]
  obtain ⟨st₁, h₁', hb, hF⟩ := key
  have hadv := h₁ c hc st₁ h₁'
  intro D hD
  rw [hF]
  exact hadv D (hb ▸ hD)

/-- The field `action_tick_store_of_outcomes` of `NodeFacts` at `Model.spec`: if `before` is
    reached, runs as `v` and is awake for round `r`'s grade-2 test, every outcome of `v`'s tick at
    `r`'s action time has the attestations of the member attestation duty's store. -/
theorem _root_.SpecRecord.NodeFacts.spec_action_tick_store_of_outcomes :
    ∀ (S : Setup V) (v : V) (before : (Model.spec (V := V)).N) (r : Round)
      (hrun : (Model.spec (V := V)).awake_for_grade2 S v before r)
      (out : (Model.spec (V := V)).N × List (NamedObject V)) (hout : (Model.spec (V := V)).tick S v before ((Model.spec (V := V)).a S.hc S.E.Δ r) ⇢ out)
      (c : (Model.spec (V := V)).Cache) (hc : (Model.spec (V := V)).onPhaseTick S.E S.hc before.st.core.toHealing ((Model.spec (V := V)).a S.hc S.E.Δ r)
        before.cache ⇢ c)
      (st : (Model.spec (V := V)).NS) (hst : (Model.spec (V := V)).duties_update_confirmation_with ((Model.spec (V := V)).gradeContract c) S.E S.hc
        ((Model.spec (V := V)).ns_setClock S.E before.st ((Model.spec (V := V)).a S.hc S.E.Δ r)) (S.E.slotOf ((Model.spec (V := V)).a S.hc S.E.Δ r) - 1) ⇢ st)
      (D : (Model.spec (V := V)).NS × (Model.spec (V := V)).NR × NamedAttestation V)
      (hD : (Model.spec (V := V)).duties_attest_with ((Model.spec (V := V)).gradeContract c) S.E S.hc (S.node v) st before.record ⇢ D)
      (hn : (Model.spec (V := V)).reachedNode before) (hv : (Model.spec (V := V)).runs_as before v),
      out.1.st.sg_rows = D.1.sg_rows := by
  intro S v before r hrun out hout c hc st hst D hD hn hv
  have hv' : before.val.v = v := hv
  have hcA := condA_of S v before r hrun
  rw [← NodeFacts.slotOf_eq] at hst
  obtain ⟨st5, row, hout1, hD1, -, -⟩ := action_tick S v before _ out hout hn hv' hcA hc hst hD
  show Member.sg_rows out.1.val.st = Member.sg_rows D.1.val
  rw [hout1, hD1]
  rfl

/-- The field `tick_rows_after_proposal_of_outcomes` of `NodeFacts` at `Model.spec`: if `n` is
    reached and runs as `v`, then when `v` proposes at `t` every attestation the member proposal
    duty's store holds is held by every outcome of `v`'s tick at `t`, and otherwise every
    attestation of `n`'s store staged to `t` is. -/
theorem _root_.SpecRecord.NodeFacts.spec_tick_rows_after_proposal_of_outcomes :
    ∀ (S : Setup V) (v : V) (n : (Model.spec (V := V)).N) (t : Time)
      (out : (Model.spec (V := V)).N × List (NamedObject V)) (hout : (Model.spec (V := V)).tick S v n t ⇢ out)
      (hn : (Model.spec (V := V)).reachedNode n) (hv : (Model.spec (V := V)).runs_as n v),
      let s := S.E.slotOf t
      let st0 := (Model.spec (V := V)).ns_setClock S.E n.st t
      ((0 < s ∧ t = (Model.spec (V := V)).proposal_time S.E s ∧ S.E.proposer s = (S.node v).val_index ∧
          (Model.spec (V := V)).awake_for_grade1 S v n ((Model.spec (V := V)).round_of S.hc s)) →
        ∀ c : (Model.spec (V := V)).Cache, (Model.spec (V := V)).onPhaseTick S.E S.hc n.st.core.toHealing t n.cache ⇢ c →
        ∀ D : (Model.spec (V := V)).NS × Option (NamedBlock V),
          (Model.spec (V := V)).duties_propose_block_with ((Model.spec (V := V)).frameContract c) S.E S.hc S.cfg (S.node v) st0 ⇢ D →
          ∀ a : NamedAttestation V, a ∈ D.1.sg_rows a.round → a ∈ out.1.st.sg_rows a.round) ∧
      (¬ (0 < s ∧ t = (Model.spec (V := V)).proposal_time S.E s ∧ S.E.proposer s = (S.node v).val_index ∧
          (Model.spec (V := V)).awake_for_grade1 S v n ((Model.spec (V := V)).round_of S.hc s)) →
        ∀ a : NamedAttestation V, a ∈ st0.sg_rows a.round → a ∈ out.1.st.sg_rows a.round) := by
  intro S v n t out hout hn hv
  have hv' : n.val.v = v := hv
  dsimp only
  refine ⟨?_, ?_⟩
  · rintro ⟨hpos, ht, hpr, hrun⟩ c hc D hD a ha
    have hcP : condP (Setup.toSpec S).C (Setup.toSpec S).P n.val t := by
      have h := condP_of S v n hpos (hpr.trans (by rw [S.node_val_index, ← hv'])) hrun
      rwa [← ht] at h
    obtain ⟨st2, B', hout1, hD1, -, -⟩ := proposal_tick S v n t out hout hn hv' hcP hc hD
    have e : Member.sg_rows out.1.val.st = Member.sg_rows D.1.val := by
      rw [hout1, hD1]; rfl
    show a ∈ Member.sg_rows out.1.val.st a.round
    rw [e]
    exact ha
  · intro hnot a ha
    obtain ⟨sent, hrun, -⟩ := NodeFacts.tick_out S v n t out hout
    have hcP : ¬ condP (Setup.toSpec S).C (Setup.toSpec S).P n.val t := by
      intro hcP
      apply hnot
      have hc := hcP
      obtain ⟨hpos, hc⟩ := hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨a, ha, hle⟩ := awake_of_condP hcP
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [← NodeFacts.slotOf_eq]; exact hpos
      · rw [← NodeFacts.slotOf_eq]; exact hc.1.1
      · rw [← NodeFacts.slotOf_eq, S.node_val_index, ← hv']; exact hc.1.2
      · refine ⟨a, ha, ?_⟩
        rw [← NodeFacts.slotOf_eq]; exact hle
    have ha' : a ∈ (n.val.st.attestations a.round).map Spec.Attestation.toProofNamed := ha
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha'
    show x.toProofNamed ∈ (out.1.val.st.attestations x.toProofNamed.round).map
      Spec.Attestation.toProofNamed
    exact List.mem_map_of_mem (tick_rows_grow hrun hcP _ x hx)

/-- The field `tick_attestation_fields` of `NodeFacts` at `Model.spec`: if `n` runs as `v`,
    every attestation `a` that `v`'s tick at `t` sends is of the round whose action time is `t`, `n`
    passes the grade-2 awake test of that round, and `a` is signed by `v`. -/
theorem _root_.SpecRecord.NodeFacts.spec_tick_attestation_fields :
    ∀ (S : Setup V) (v : V) (n : (Model.spec (V := V)).N) (t : Time)
      (hv : (Model.spec (V := V)).runs_as n v)
      (out : (Model.spec (V := V)).N × List (NamedObject V)) (hout : (Model.spec (V := V)).tick S v n t ⇢ out)
      (a : NamedAttestation V) (h : NamedObject.attest a ∈ out.2),
      t = (Model.spec (V := V)).a S.hc S.E.Δ a.round ∧ (Model.spec (V := V)).awake_for_grade2 S v n a.round ∧ a.val_index = v := by
  intro S v n t hv out hout a h
  obtain ⟨sent, hrun, hsent⟩ := NodeFacts.tick_out S v n t out hout
  rw [hsent] at h
  obtain ⟨o, ho, hoa⟩ := List.mem_map.mp h
  cases o with
  | block B => simp only [Spec.NamedObject.toProof, reduceCtorEq] at hoa
  | gfVote u => simp only [Spec.NamedObject.toProof, reduceCtorEq] at hoa
  | attest row =>
    simp only [Spec.NamedObject.toProof, NamedObject.attest.injEq] at hoa
    subst hoa
    obtain ⟨hA, i, hiv, hir, rfl⟩ := TickReached.tick_attest_input_round hrun ho
    have hround : (Spec.Protocol.create n.val.signingHistory i).2.toProofNamed.round =
        (Setup.toSpec S).C.round_of ((Setup.toSpec S).C.slotOf t) := hir
    have hval : (Spec.Protocol.create n.val.signingHistory i).2.toProofNamed.val_index =
        n.val.v := hiv
    rw [hround, hval]
    refine ⟨?_, ?_, hv⟩
    · have ht := hA
      simp only [NodeFacts.condA, Bool.and_eq_true, decide_eq_true_eq] at ht
      exact ht.1
    · obtain ⟨a', ha', hle⟩ := NodeFacts.awake_of_condA hA
      exact ⟨a', ha', hle⟩

end DecoupledConsensusModel.Sts.Record

