import Proofs.Instance.Equalities.Images
import Proofs.Instance.Equalities.GradesImages
import Proofs.Instance.Equalities.ForkChoiceImages
import Proofs.Instance.Model
import Proofs.Instance.NoRaise.Routines

/-!
# Outcomes of the contract-reading members of `Model.spec`

The members of `Model.spec` that take a grade contract `c` run the spec's routine on the store
with its saved grades replaced by `c`. The lemmas of this file say what an outcome of such a member
is, read off the spec's routine.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace SpecRecord.ContractImages

open DecoupledConsensusModel DecoupledConsensusModel.Sts.Record
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-- The member `early` of `Model.spec` equals the member `early` of `Model.vocabulary`. -/
theorem early_eq (E : Env V) (hc : Protocol.HealConfig) (r : Round) (p : Protocol.Phase) :
    (Model.spec (V := V)).early E hc r p = (Model.vocabulary (V := V)).early E hc r p := by
  show Member.early E hc r p = Protocol.early E hc r p
  have h := toProof_early E hc unreadHeightConfig r (Spec.Protocol.Phase.toSpec p)
  have hp : (Spec.Protocol.Phase.toSpec p).toProof = p := by cases p <;> rfl
  rw [hp] at h
  exact h.symm

/-- The member `late` of `Model.spec` equals the member `late` of `Model.vocabulary`. -/
theorem late_eq (E : Env V) (hc : Protocol.HealConfig) (r : Round) (p : Protocol.Phase) :
    (Model.spec (V := V)).late E hc r p = (Model.vocabulary (V := V)).late E hc r p := by
  show Member.late E hc r p = Protocol.late E hc r p
  unfold Member.late Protocol.late
  rw [toProof_opening E hc unreadHeightConfig r]
  cases p <;> simp only [Member.lateOffset, Protocol.Phase.lateOffset] <;> rfl

/-- An outcome of the confirmation member under the contract `c` is the store `st` with its three
    confirmation records (`live_confirmed`, `latest_stable`, `latest_confirmed`) written and its
    saved grades set to `c`, and nothing else changed. -/
theorem update_confirmation_with_shape {c : Spec.SavedGrades V} {E : Env V}
    {hc : Protocol.HealConfig} {st st' : Spec.Store V} {s : Slot}
    (h : Returns (Member.update_confirmation_with c E hc st s) st') :
    ∃ x1 x2 x3, st' = { Spec.Store.ofImage st with live_confirmed := x1, latest_stable := x2, latest_confirmed := x3, saved_grades := c } := by
  unfold Member.update_confirmation_with at h
  rw [returns_successOutcomes] at h
  cases hu : Spec.Protocol.update_confirmation
      (Spec.Config.toSpec E hc unreadHeightConfig)
      { Spec.Store.ofImage st with saved_grades := fill (Spec.Protocol.advance_to_round
        (st.contractOfImage c)
        ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.s)) } s with
  | error e => rw [hu] at h; cases h
  | ok out =>
    rw [hu] at h
    have h' := Except.ok.inj h
    rw [NoRaise.update_confirmation_writes_only_confirmation hu] at h'
    exact ⟨_, _, _, h'.symm⟩

/-- If a result mapped by `f` answers `b`, the result answered some `a` with `f a = b`. -/
theorem except_map_eq_ok {α β : Type} {f : α → β} {x : DC.DRE α} {b : β}
    (h : Except.map f x = .ok b) : ∃ a, x = .ok a ∧ f a = b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, Except.ok.inj h⟩

omit [Inhabited V] in
/-- An answer of the spec's `Protocol.proposal_input` names the head `get_head_with` answers as
    parent, the store's slot, the slot's new root `X.new_root v`, the proposer's votes, the support
    votes `proposer_support_view` answers, and the proposer `v`. -/
theorem proposal_input_shape {C : Spec.Config} {X : Spec.External V} {v : V}
    {st : Spec.Store V} {i : Spec.Protocol.ProposalInput V}
    (h : Spec.Protocol.proposal_input C X v st = .ok i) :
    ∃ H sv, Spec.Protocol.proposer_support_view st st.s = .ok sv ∧
      Spec.Protocol.get_head_with C st
        (Spec.Protocol.proposer_view st st.s).toFinset sv.toFinset (st.s - 1) = .ok H ∧
      i = ⟨H, st.s, X.new_root v st.s, Spec.Protocol.proposer_view st st.s, sv, v⟩ := by
  unfold Spec.Protocol.proposal_input at h
  obtain ⟨sv, hsv, h⟩ := NoRaise.DRE.of_bind_ok h
  obtain ⟨H, hH, h⟩ := NoRaise.DRE.of_bind_ok h
  exact ⟨H, sv, hsv, hH, (Except.ok.inj h).symm⟩

omit [Inhabited V] in
/-- An answer of the spec's `Protocol.build_proposal` is the block built from an answer `i` of
    `proposal_input`, with `i`'s parent, slot, root, votes and proposer, carrying the attestations
    `proposal_attestations` keeps of an answer of `attestations_to_include`. -/
theorem build_proposal_shape {C : Spec.Config} {X : Spec.External V} {v : V}
    {st : Spec.Store V} {B : Spec.Block V}
    (h : Spec.Protocol.build_proposal C X v st = .ok B) :
    ∃ i rows, Spec.Protocol.proposal_input C X v st = .ok i ∧
      Spec.Protocol.attestations_to_include C st = .ok rows ∧
      B = .node i.parent i.slot i.root i.gf_votes i.gf_support_votes
        (Spec.Protocol.proposal_attestations i.parent rows) i.proposer := by
  unfold Spec.Protocol.build_proposal at h
  obtain ⟨i, hi, h⟩ := NoRaise.DRE.of_bind_ok h
  obtain ⟨rows, hrows, h⟩ := NoRaise.DRE.of_bind_ok h
  exact ⟨i, rows, hi, hrows, (Except.ok.inj h).symm⟩

omit [DecidableEq V] [Fintype V] [Inhabited V] in
/-- Every member of the answer of a raising filter of `l` is a member of `l`. -/
theorem list_filterM_subset {α : Type} (p : α → DC.DRE Bool) :
    ∀ (l l' : List α), l.filterM p = .ok l' → ∀ a ∈ l', a ∈ l := by
  intro l l' h a ha
  have e := ForkChoiceImages.list_filterM_eq_filter_of_ok p
    (fun a => match p a with | .ok b => b | .error _ => false)
    (fun a b hab => by simp only [hab]) l l' h
  rw [e] at ha
  exact List.mem_of_mem_filter ha

omit [DecidableEq V] [Fintype V] [Inhabited V] in
/-- The first Goldfish vote a duty sent, mapped by `toProof`, is the one
    `ChainStateToHandlers.sentGoldfishVote` reads. -/
theorem firstSentGoldfishVote_map (l : List (Spec.NamedObject V)) :
    (Member.firstSentGoldfishVote l).map Spec.GoldfishVote.toProof =
      ChainStateToHandlers.sentGoldfishVote l := by
  induction l with
  | nil => rfl
  | cons o l ih =>
    cases o <;> simp only [Member.firstSentGoldfishVote, ChainStateToHandlers.sentGoldfishVote,
      List.findSome?_cons, Option.map_some] at ih ⊢ <;> exact ih

open scoped DC in
/-- An outcome of the attestation duty member under `c` comes from an answer `p` of the spec's
    `Protocol.build_attestation`: the store after admitting the attestation `p.2` with `c` as its
    saved grades, the signing history `p.1`, and the attestation's image. -/
theorem duties_attest_with_shape {c : Spec.SavedGrades V} {E : Env V}
    {hc : Protocol.HealConfig} {nd : Protocol.Node V} {st : Spec.Store V}
    {sh : Spec.SigningHistory}
    {D : Spec.Store V × Spec.SigningHistory × NamedAttestation V}
    (h : Returns (Member.duties_attest_with c E hc nd st sh) D) :
    ∃ p, Spec.Protocol.build_attestation (Spec.Config.toSpec E hc unreadHeightConfig)
        nd.val_index { Spec.Store.ofImage st with saved_grades := fill (Spec.Protocol.advance_to_round
          (st.contractOfImage c) ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.s)) }
        sh = .ok p ∧
      D = ({ Spec.Protocol.admit_attestation (Spec.Config.toSpec E hc unreadHeightConfig)
          { Spec.Store.ofImage st with saved_grades := fill (Spec.Protocol.advance_to_round
            (st.contractOfImage c) ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.s)) }
          p.2 with saved_grades := c }, p.1, p.2.toProofNamed) := by
  unfold Member.duties_attest_with at h
  rw [returns_successOutcomes] at h
  obtain ⟨out, hout, h⟩ := NoRaise.DRE.of_bind_ok h
  unfold Spec.Protocol.attest at hout
  dsimp only at hout
  generalize hst' : ({ Spec.Store.ofImage st with saved_grades := fill (Spec.Protocol.advance_to_round
    (st.contractOfImage c) ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.s)) } :
    Spec.Store V) = st' at hout ⊢
  cases hb : Spec.Protocol.build_attestation
      (Spec.Config.toSpec E hc unreadHeightConfig) nd.val_index st' sh with
  | error e => rw [hb] at hout; cases hout
  | ok p =>
    rw [hb] at hout
    have h2 : (Except.ok ((Spec.Protocol.admit_attestation
        (Spec.Config.toSpec E hc unreadHeightConfig) st' p.2, p.1),
        [] ++ [Spec.NamedObject.attest p.2]) :
        DC.DRE ((Spec.Store V × Spec.SigningHistory) ×
          List (Spec.NamedObject V))) = .ok out := hout
    cases h2
    refine ⟨p, rfl, ?_⟩
    have h' : (Except.ok ({ Spec.Protocol.admit_attestation
        (Spec.Config.toSpec E hc unreadHeightConfig) st' p.2 with saved_grades := c },
        p.1, p.2.toProofNamed) : DC.DRE (Spec.Store V × Spec.SigningHistory ×
          NamedAttestation V)) = .ok D := h
    exact (Except.ok.inj h').symm

/-- An outcome of the member `round_action_with` under `c` is the signing history and the image of
    the attestation of an answer of the spec's `Protocol.build_attestation`. -/
theorem round_action_with_shape {c : Spec.SavedGrades V} {E : Env V}
    {hc : Protocol.HealConfig} {nd : Protocol.Node V} {st : Spec.Store V}
    {sh : Spec.SigningHistory}
    {A : Spec.SigningHistory × NamedAttestation V}
    (h : Returns (Member.round_action_with c E hc nd st sh) A) :
    ∃ p, Spec.Protocol.build_attestation (Spec.Config.toSpec E hc unreadHeightConfig)
        nd.val_index { Spec.Store.ofImage st with saved_grades := fill (Spec.Protocol.advance_to_round
          (st.contractOfImage c) ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.s)) }
        sh = .ok p ∧ A = (p.1, p.2.toProofNamed) := by
  unfold Member.round_action_with at h
  rw [returns_successOutcomes] at h
  obtain ⟨p, hp, e⟩ := except_map_eq_ok h
  exact ⟨p, hp, e.symm⟩

omit [Inhabited V] in
/-- An answer of the spec's `Protocol.build_attestation` is `create` of the signing history on an
    answer of `attestation_input`, for the validator `v` and the store's round. -/
theorem build_attestation_shape {C : Spec.Config} {v : V} {st : Spec.Store V}
    {sh : Spec.SigningHistory}
    {p : Spec.SigningHistory × Spec.Attestation V}
    (h : Spec.Protocol.build_attestation C v st sh = .ok p) :
    ∃ i, Spec.Protocol.attestation_input C v st = .ok i ∧ i.val_index = v ∧
      i.round = C.round_of st.s ∧ p = Spec.Protocol.create sh i := by
  unfold Spec.Protocol.build_attestation at h
  obtain ⟨i, hi, h⟩ := NoRaise.DRE.of_bind_ok h
  refine ⟨i, hi, ?_, ?_, (Except.ok.inj h).symm⟩ <;>
  · unfold Spec.Protocol.attestation_input at hi
    obtain ⟨a, -, hi⟩ := NoRaise.DRE.of_bind_ok hi
    obtain ⟨b, -, hi⟩ := NoRaise.DRE.of_bind_ok hi
    obtain ⟨d, -, hi⟩ := NoRaise.DRE.of_bind_ok hi
    cases Except.ok.inj hi
    rfl

omit [Inhabited V] in
/-- The spec's `admit_attestation` keeps the store's clock, slot and three confirmation records. -/
theorem admit_attestation_frame (C : Spec.Config) (st : Spec.Store V)
    (row : Spec.Attestation V) :
    (Spec.Protocol.admit_attestation C st row).t = st.t ∧
      (Spec.Protocol.admit_attestation C st row).s = st.s ∧
      (Spec.Protocol.admit_attestation C st row).live_confirmed = st.live_confirmed ∧
      (Spec.Protocol.admit_attestation C st row).latest_stable = st.latest_stable ∧
      (Spec.Protocol.admit_attestation C st row).latest_confirmed =
        st.latest_confirmed := by
  unfold Spec.Protocol.admit_attestation Spec.Protocol.add_attestation
  dsimp only [Id.run]
  split <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- An outcome of the proposal duty member under `c` comes from an answer `B` of the spec's
    `Protocol.build_proposal`: the store after `on_block` of `B` with `c` as its saved grades, and
    `some` of `B`'s named image. -/
theorem duties_propose_block_with_shape {c : Spec.SavedGrades V} {E : Env V}
    {hc : Protocol.HealConfig} {cfg : Protocol.HeightConfig} {nd : Protocol.Node V}
    {st : Spec.Store V} {D : Spec.Store V × Option (NamedBlock V)}
    (h : Returns (Member.duties_propose_block_with c E hc cfg nd st) D) :
    ∃ B, Spec.Protocol.build_proposal (Spec.Config.toSpec E hc cfg)
        (Member.externalOfNode nd) nd.val_index
        { Spec.Store.ofImage st with saved_grades := fill (Spec.Protocol.advance_to_round
          (st.contractOfImage c) ((Spec.Config.toSpec E hc cfg).round_of st.s)) } = .ok B ∧
      D = ({ Spec.Protocol.on_block (Spec.Config.toSpec E hc cfg)
          (Spec.Provisional.toSpec E)
          { Spec.Store.ofImage st with saved_grades := fill (Spec.Protocol.advance_to_round
            (st.contractOfImage c) ((Spec.Config.toSpec E hc cfg).round_of st.s)) } B with
          saved_grades := c }, some B.toProofNamed) := by
  unfold Member.duties_propose_block_with at h
  rw [returns_successOutcomes] at h
  obtain ⟨out, hout, e⟩ := except_map_eq_ok h
  unfold Spec.Protocol.propose_block at hout
  generalize hst' : ({ Spec.Store.ofImage st with saved_grades := fill (Spec.Protocol.advance_to_round
    (st.contractOfImage c) ((Spec.Config.toSpec E hc cfg).round_of st.s)) } :
    Spec.Store V) = st' at hout ⊢
  cases hb : Spec.Protocol.build_proposal (Spec.Config.toSpec E hc cfg)
      (Member.externalOfNode nd) nd.val_index st' with
  | error e => rw [hb] at hout; cases hout
  | ok B =>
    rw [hb] at hout
    have h2 : (Except.ok (Spec.Protocol.on_block (Spec.Config.toSpec E hc cfg)
        (Spec.Provisional.toSpec E) st' B, [] ++ [Spec.NamedObject.block B]) :
        DC.DRE (Spec.Store V × List (Spec.NamedObject V))) = .ok out := hout
    cases h2
    exact ⟨B, rfl, e.symm⟩

omit [Inhabited V] in
/-- An answer of the spec's Goldfish vote duty is the store, or the store after
    `on_goldfish_vote_checked` of the vote it sends: it writes only the Goldfish votes and their
    stamps. -/
theorem goldfish_vote_writes {C : Spec.Config} {P : Spec.Provisional V} {v : V}
    {st : Spec.Store V} {l : List (Spec.NamedObject V)}
    {out : Spec.Store V × List (Spec.NamedObject V)}
    (h : (Spec.Protocol.goldfish_vote C P v st).run l = .ok out) :
    ∃ x y, out.1 = { st with gf_votes := x, timestamp_vote := y } := by
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
    unfold Spec.Protocol.on_goldfish_vote_checked Spec.Protocol.on_goldfish_vote
    simp only [Id.run, pure]
    split_ifs <;> exact ⟨_, _, rfl⟩
  · rw [NoRaise.DREB.pure_run_ok_iff] at h
    subst h
    exact ⟨_, _, rfl⟩

/-- The store of an outcome of the Goldfish vote duty member under `c` is `st` with its Goldfish
    votes and their stamps written and its saved grades set to `c`, and nothing else changed. -/
theorem duties_goldfish_vote_with_shape {c : Spec.SavedGrades V} {E : Env V}
    {hc : Protocol.HealConfig} {nd : Protocol.Node V} {st : Spec.Store V}
    {D : Spec.Store V × Option (GoldfishVote V)}
    (h : Returns (Member.duties_goldfish_vote_with c E hc nd st) D) :
    ∃ x y,
      D.1 = { Spec.Store.ofImage st with gf_votes := x, timestamp_vote := y, saved_grades := c } := by
  unfold Member.duties_goldfish_vote_with at h
  rw [returns_successOutcomes] at h
  obtain ⟨out, hout, e⟩ := except_map_eq_ok h
  obtain ⟨x, y, hx⟩ := goldfish_vote_writes hout
  refine ⟨x, y, ?_⟩
  rw [← e]
  show { out.1 with saved_grades := c } = _
  rw [hx]

omit [Fintype V] [Inhabited V] in
/-- The spec's `get_sg_root_with` is `anchor` of the grade-1 result of the store's round. -/
theorem get_sg_root_with_eq_anchor (C : Spec.Config) (st : Spec.Store V) :
    Spec.Protocol.get_sg_root_with C st =
      Spec.Protocol.anchor st (Spec.Protocol.round_grades st (C.round_of st.s)).g1 := by
  unfold Spec.Protocol.get_sg_root_with Spec.Protocol.anchor
    Spec.Store.G1 Spec.Store.grade Spec.Protocol.get_sg_root
    Spec.Protocol.round_grades
  simp only [Id.run, pure, bind, Spec.Protocol.phaseResult]
  generalize (Spec.Protocol.make_round_grades_compatible_with st.F
      (Spec.Protocol.saved_round_grades st.saved_grades (C.round_of st.s))).g1 = g
  cases g with
  | pending => rfl
  | computed G =>
    simp only [Except.bind, Except.pure]
    by_cases h : Spec.Protocol.active_prefix st G = none
    · simp [h]
    · simp [h]

omit [Fintype V] [Inhabited V] in
/-- If `active_prefix st g` is `some X`, then `X` is in `get_filtered_block_tree st`. -/
theorem active_prefix_mem_filtered {st : Spec.Store V} {g : Option (Spec.Block V)}
    {X : Spec.Block V} (h : Spec.Protocol.active_prefix st g = some X) :
    X ∈ Spec.Protocol.get_filtered_block_tree st := by
  simp only [Spec.Protocol.active_prefix, Id.run, pure] at h
  split at h
  · simp only [Spec.Protocol.activePrefix, Spec.Block.deepest?] at h
    unfold Spec.pickUnique? at h
    split at h
    · rename_i hex
      rw [← Option.some.inj h]
      exact (Finset.mem_filter.mp (Finset.choose_mem _ _ hex)).1
    · cases h
  · cases h

omit [Fintype V] [Inhabited V] in
/-- The store's fgroot is an ancestor of, or equal to, every block of its filtered tree. -/
theorem fg_root_ancestorEq_of_mem_filtered {st : Spec.Store V} {B : Spec.Block V}
    (h : B ∈ Spec.Protocol.get_filtered_block_tree st) :
    (Spec.Protocol.get_fg_root st).ancestorEq B = true := by
  simp only [Spec.Protocol.get_filtered_block_tree,
    Spec.Protocol.get_filtered_block_tree_from, Id.run, pure, Finset.mem_filter] at h
  exact h.2

omit [Fintype V] [Inhabited V] in
/-- An answer of the spec's `anchor` is the store's fgroot or a block of its filtered tree. -/
theorem anchor_cases {st : Spec.Store V} {g1 : Spec.GradeResult V}
    {A : Spec.Block V} (h : Spec.Protocol.anchor st g1 = .ok A) :
    A = Spec.Protocol.get_fg_root st ∨ A ∈ Spec.Protocol.get_filtered_block_tree st := by
  unfold Spec.Protocol.anchor at h
  obtain ⟨G1, -, h⟩ := NoRaise.DRE.of_bind_ok h
  rw [← Except.ok.inj h]
  unfold Spec.Protocol.get_sg_root
  simp only [Id.run, pure]
  split
  · exact Or.inl rfl
  · rename_i hne
    obtain ⟨X, hX⟩ := Option.ne_none_iff_exists'.mp hne
    simp only [hX, Option.value]
    exact Or.inr (active_prefix_mem_filtered hX)

omit [Inhabited V] in
/-- One step of the spec's walk from `H`, when it steps, steps to a block of the tree whose parent
    is `H`. -/
theorem ghost_step_child {tree : Finset (Spec.Block V)}
    {score : Spec.Block V → DC.DRE Nat} {el : Spec.Block V → DC.DRE Bool}
    {H C : Spec.Block V}
    (h : Spec.Protocol.ghost_step tree score el H = .ok (some C)) :
    C ∈ tree ∧ C.parent? = some H := by
  classical
  unfold Spec.Protocol.ghost_step at h
  obtain ⟨children, hc, h⟩ := NoRaise.DRE.of_bind_ok h
  unfold Spec.Protocol.argmax? at h
  obtain ⟨best, hb, h⟩ := NoRaise.DRE.of_bind_ok h
  have hC : Spec.pickUnique? best (fun _ => true) = some C := Except.ok.inj h
  have hCb : C ∈ best := by
    unfold Spec.pickUnique? at hC
    split at hC
    · rename_i hex
      rw [← Option.some.inj hC]
      exact (Finset.choose_mem _ _ hex)
    · cases hC
  have hbs := ForkChoiceImages.filterM_eq_filter_of_ok_mem _
    (fun a => Spec.Protocol.is_best_in score children a = .ok true) children
    (fun a _ b hab => by
      constructor
      · intro hb'; rw [hab, hb']
      · intro h'; rw [hab] at h'; exact Except.ok.inj h') best hb
  rw [hbs] at hCb
  replace hCb := (Finset.mem_filter.mp hCb).1
  unfold Spec.Protocol.ghost_children at hc
  have hcs := ForkChoiceImages.filterM_eq_filter_of_ok_mem _
    (fun B => B.parent? = some H ∧ el B = .ok true) tree
    (fun a _ b hab => by
      by_cases hp : a.parent? = some H
      · simp only [hp, if_true] at hab
        simp [hp, hab]
      · simp only [hp, if_false] at hab
        have : b = false := (Except.ok.inj hab).symm
        simp [this, hp]) children hc
  rw [hcs, Finset.mem_filter] at hCb
  exact ⟨hCb.1, hCb.2.1⟩

omit [Fintype V] [Inhabited V] in
/-- A block whose parent is `H` is a descendant of every ancestor of `H`. -/
theorem ancestorEq_of_parent {A H C : Spec.Block V} (hp : C.parent? = some H)
    (h : A.ancestorEq H = true) : A.ancestorEq C = true := by
  cases C with
  | genesis => cases hp
  | node p s r v sv atts pr =>
    simp only [Spec.Block.parent?, Option.some.injEq] at hp
    subst hp
    simp [Spec.Block.ancestorEq, h]

omit [Fintype V] [Inhabited V] in
/-- Every block is an ancestor of, or equal to, itself. -/
theorem ancestorEq_self (B : Spec.Block V) : B.ancestorEq B = true := by
  cases B <;> simp [Spec.Block.ancestorEq]

omit [Inhabited V] in
/-- The spec's bounded walk from `H` answers `H` or a block of the tree, and every ancestor of `H`
    is an ancestor of, or equal to, the answer. -/
theorem ghost_walk_mem_ancestorEq {tree : Finset (Spec.Block V)}
    {score : Spec.Block V → DC.DRE Nat} {el : Spec.Block V → DC.DRE Bool}
    (n : Nat) (H R : Spec.Block V)
    (h : Spec.Protocol.ghost_walk tree score el n H = .ok R) :
    (R = H ∨ R ∈ tree) ∧ ∀ A : Spec.Block V, A.ancestorEq H = true → A.ancestorEq R = true := by
  induction n generalizing H with
  | zero =>
    have e : H = R := Except.ok.inj h
    subst e
    exact ⟨Or.inl rfl, fun _ hA => hA⟩
  | succ n ih =>
    simp only [Spec.Protocol.ghost_walk] at h
    obtain ⟨C?, hC?, h⟩ := NoRaise.DRE.of_bind_ok h
    cases C? with
    | none =>
      have e : H = R := Except.ok.inj h
      subst e
      exact ⟨Or.inl rfl, fun _ hA => hA⟩
    | some C =>
      obtain ⟨hCt, hCp⟩ := ghost_step_child hC?
      have h' : Spec.Protocol.ghost_walk tree score el n C = .ok R := h
      obtain ⟨hm, ha⟩ := ih C h'
      refine ⟨?_, fun A hA => ha A (ancestorEq_of_parent hCp hA)⟩
      rcases hm with rfl | hR
      · exact Or.inr hCt
      · exact Or.inr hR

/-- An outcome of the member `get_sg_root_with` under `c` is the image of an answer of the spec's
    `anchor` of the grade-1 result of round `r`, on the store with the saved grades read from `c` at
    round `r`. -/
theorem get_sg_root_with_shape {c : Spec.SavedGrades V} {E : Env V}
    {hc : Protocol.HealConfig} {st : Spec.Store V} {r : Round} {R : Block V}
    (h : Returns (Member.get_sg_root_with c E hc st r) R) :
    ∃ A, Spec.Protocol.anchor
        { Spec.Store.ofImage st with saved_grades := fill (Spec.Protocol.advance_to_round (st.contractOfImage c) r) }
        (Spec.Protocol.round_grades
          { Spec.Store.ofImage st with saved_grades := fill (Spec.Protocol.advance_to_round (st.contractOfImage c) r) }
          r).g1 = .ok A ∧ R = A.toProof := by
  unfold Member.get_sg_root_with at h
  rw [returns_successOutcomes] at h
  obtain ⟨A, hA, e⟩ := except_map_eq_ok h
  exact ⟨A, hA, e.symm⟩

/-- The anchor of an outcome of the member `read` under `c` is the image of the same answer of the
    spec's `anchor`. -/
theorem read_anchor_shape {c : Spec.SavedGrades V} {E : Env V}
    {hc : Protocol.HealConfig} {st : Spec.Store V} {r : Round}
    {G : Protocol.GradeRead V}
    (h : Returns (Member.read c E hc st r) G) :
    ∃ A, Spec.Protocol.anchor
        { Spec.Store.ofImage st with saved_grades := fill (Spec.Protocol.advance_to_round (st.contractOfImage c) r) }
        (Spec.Protocol.round_grades
          { Spec.Store.ofImage st with saved_grades := fill (Spec.Protocol.advance_to_round (st.contractOfImage c) r) }
          r).g1 = .ok A ∧ G.anchor = A.toProof := by
  unfold Member.read at h
  rw [returns_successOutcomes] at h
  obtain ⟨g, hg, e⟩ := except_map_eq_ok h
  unfold Spec.Protocol.round_grade_read at hg
  obtain ⟨A, hA, hg⟩ := NoRaise.DRE.of_bind_ok hg
  obtain ⟨Q2, -, hg⟩ := NoRaise.DRE.of_bind_ok hg
  obtain ⟨G0, -, hg⟩ := NoRaise.DRE.of_bind_ok hg
  obtain ⟨raw, -, hg⟩ := NoRaise.DRE.of_bind_ok hg
  cases Except.ok.inj hg
  exact ⟨A, hA, by rw [← e]; rfl⟩

/-- An outcome of the member `get_head_in_tree_with_layer` under `c` is the image of a block `X'`
    the spec's walk stops at, from an answer `A` of the spec's anchor of the store's round: `X'` is
    `A` or a block standing for a block of `tree`, and every ancestor of `A` is an ancestor of `X'`. -/
theorem get_head_in_tree_with_layer_shape {c : Spec.SavedGrades V} {E : Env V}
    {hc : Protocol.HealConfig} {st : Spec.Store V}
    {tree : Finset (Block V)} {votes support : Finset (GoldfishVote V)} {k : Slot} {X : Block V}
    (h : Returns (Member.get_head_in_tree_with_layer c E hc st tree votes support k) X) :
    ∃ A X', Spec.Protocol.anchor
        { Spec.Store.ofImage st with saved_grades := fill (Spec.Protocol.advance_to_round (st.contractOfImage c)
          ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.s)) }
        (Spec.Protocol.round_grades
          { Spec.Store.ofImage st with saved_grades := fill (Spec.Protocol.advance_to_round (st.contractOfImage c)
            ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.s)) }
          ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.s)).g1 = .ok A ∧
      (X' = A ∨ X' ∈ tree.map st.blockOfImageEmb) ∧
      (∀ B : Spec.Block V, B.ancestorEq A = true → B.ancestorEq X' = true) ∧
      X = X'.toProof := by
  unfold Member.get_head_in_tree_with_layer at h
  rw [returns_successOutcomes] at h
  obtain ⟨X', hX', e⟩ := except_map_eq_ok h
  unfold Spec.Protocol.get_head_in_tree_with_layer at hX'
  obtain ⟨A, hA, hX'⟩ := NoRaise.DRE.of_bind_ok hX'
  rw [get_sg_root_with_eq_anchor] at hA
  unfold Spec.Protocol.goldfish_fork_choice Spec.Protocol.ghost at hX'
  obtain ⟨hm, ha⟩ := ghost_walk_mem_ancestorEq _ _ _ hX'
  exact ⟨A, X', hA, hm, ha, e.symm⟩

/-- An outcome of the member `get_head_with` under `c` is the anchor or a block of the spec's
    filtered tree, and every ancestor of the anchor is an ancestor of it. -/
theorem get_head_with_shape {c : Spec.SavedGrades V} {E : Env V}
    {hc : Protocol.HealConfig} {st : Spec.Store V}
    {votes support : Finset (GoldfishVote V)} {k : Slot} {X : Block V}
    (h : Returns (Member.get_head_with c E hc st votes support k) X) :
    ∃ A X', Spec.Protocol.anchor
        { Spec.Store.ofImage st with saved_grades := fill (Spec.Protocol.advance_to_round (st.contractOfImage c)
          ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.s)) }
        (Spec.Protocol.round_grades
          { Spec.Store.ofImage st with saved_grades := fill (Spec.Protocol.advance_to_round (st.contractOfImage c)
            ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.s)) }
          ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.s)).g1 = .ok A ∧
      (X' = A ∨ X' ∈ Spec.Protocol.get_filtered_block_tree (Spec.Store.ofImage st)) ∧
      (∀ B : Spec.Block V, B.ancestorEq A = true → B.ancestorEq X' = true) ∧
      X = X'.toProof := by
  unfold Member.get_head_with at h
  rw [returns_successOutcomes] at h
  obtain ⟨X', hX', e⟩ := except_map_eq_ok h
  unfold Spec.Protocol.get_head_with Spec.Protocol.get_head_in_tree_with_layer at hX'
  obtain ⟨A, hA, hX'⟩ := NoRaise.DRE.of_bind_ok hX'
  rw [get_sg_root_with_eq_anchor] at hA
  unfold Spec.Protocol.goldfish_fork_choice Spec.Protocol.ghost at hX'
  obtain ⟨hm, ha⟩ := ghost_walk_mem_ancestorEq _ _ _ hX'
  exact ⟨A, X', hA, hm, ha, e.symm⟩

omit [Fintype V] [Inhabited V] in
/-- Every block of `chain_up n C` is an ancestor of, or equal to, `C`. -/
theorem ancestorEq_of_mem_chain_up :
    ∀ (n : ℕ) (C B : Spec.Block V), B ∈ Spec.Protocol.chain_up n C →
      B.ancestorEq C = true := by
  intro n
  induction n with
  | zero =>
    intro C B hB
    simp only [Spec.Protocol.chain_up, List.mem_singleton] at hB
    subst hB
    exact ancestorEq_self _
  | succ n ih =>
    intro C B hB
    cases C with
    | genesis =>
      simp [Spec.Protocol.chain_up, Spec.Block.parent?, Id.run, pure] at hB
      subst hB
      exact ancestorEq_self _
    | node p s r v sv atts pr =>
      simp [Spec.Protocol.chain_up, Spec.Block.parent?, Id.run, pure] at hB
      rcases hB with rfl | hB
      · exact ancestorEq_self _
      · exact ancestorEq_of_parent (H := p) rfl (ih p B hB)

omit [Fintype V] [Inhabited V] in
/-- An answer of the spec's `deepest_clear floor C test` is a descendant of, or equal to, `floor`,
    and an ancestor of, or equal to, `C`. -/
theorem deepest_clear_between {floor C B : Spec.Block V}
    {test : Spec.Block V → Bool}
    (h : Spec.Protocol.deepest_clear floor C test = some B) :
    floor.ancestorEq B = true ∧ B.ancestorEq C = true := by
  unfold Spec.Protocol.deepest_clear Spec.Block.deepest? at h
  unfold Spec.pickUnique? at h
  split at h
  · rename_i hex
    rw [← Option.some.inj h]
    have hm := Finset.mem_filter.mp (Finset.choose_mem _ _ hex)
    rw [Bool.and_eq_true] at hm
    exact ⟨hm.2.1, ancestorEq_of_mem_chain_up _ _ _ (List.mem_toFinset.mp hm.1)⟩
  · cases h

/-- An outcome of the member `fg_source_with` under `c`, for the candidate `some q`, is the image of
    the spec's deepest block between the block standing for `q` and the store's live confirmed block
    that passes a test, or the image of the block standing for `q`; for no candidate it is `none`. -/
theorem fg_source_with_shape {c : Spec.SavedGrades V} {E : Env V}
    {hc : Protocol.HealConfig} {st : Spec.Store V} {r : Round}
    {A_G2 : Option (Block V)} {o : Option (Block V)}
    (h : Returns (Member.fg_source_with c E hc st r A_G2) o) :
    (A_G2 = none ∧ o = none) ∨ ∃ q, A_G2 = some q ∧
      (o = some q ∨ ∃ B test, Spec.Protocol.deepest_clear (st.blockOfImage q)
        (Spec.Store.ofImage st).live_confirmed test = some B ∧
        o = some B.toProof) := by
  unfold Member.fg_source_with at h
  rw [returns_successOutcomes] at h
  obtain ⟨o', ho', e⟩ := except_map_eq_ok h
  unfold Spec.Protocol.fg_source_with at ho'
  cases A_G2 with
  | none =>
    left
    refine ⟨rfl, ?_⟩
    simp only [Option.map_none, ne_eq, not_true_eq_false, pure, Except.pure] at ho'
    rw [← e, ← Except.ok.inj ho']
    rfl
  | some q =>
    right
    refine ⟨q, rfl, ?_⟩
    simp only [Option.map_some, ne_eq, reduceCtorEq, not_false_eq_true, Option.value,
      Option.get_some] at ho'
    obtain ⟨G0, -, ho'⟩ := NoRaise.DRE.of_bind_ok ho'
    split at ho'
    · rename_i hne
      obtain ⟨B, hB⟩ := Option.ne_none_iff_exists'.mp hne
      right
      refine ⟨B, _, hB, ?_⟩
      rw [← e, ← Except.ok.inj ho']
      simp [hB, Option.value]
    · left
      rw [← e, ← Except.ok.inj ho']
      simp [Spec.Store.toProof_blockOfImage]

/-- An outcome of the member `read` under `c` carries the images of the spec's anchor and grade-2
    candidate of round `r`, on the store with the saved grades read from `c` at round `r`. -/
theorem read_shape {c : Spec.SavedGrades V} {E : Env V}
    {hc : Protocol.HealConfig} {st : Spec.Store V} {r : Round}
    {G : Protocol.GradeRead V}
    (h : Returns (Member.read c E hc st r) G) :
    ∃ Q2, Spec.Protocol.grade2Block
        { Spec.Store.ofImage st with saved_grades := fill (Spec.Protocol.advance_to_round (st.contractOfImage c) r) }
        (Spec.Protocol.round_grades
          { Spec.Store.ofImage st with saved_grades := fill (Spec.Protocol.advance_to_round (st.contractOfImage c) r) }
          r) = .ok Q2 ∧ G.Q2 = Q2.map Spec.Block.toProof := by
  unfold Member.read at h
  rw [returns_successOutcomes] at h
  obtain ⟨g, hg, e⟩ := except_map_eq_ok h
  unfold Spec.Protocol.round_grade_read at hg
  obtain ⟨A, -, hg⟩ := NoRaise.DRE.of_bind_ok hg
  obtain ⟨Q2, hQ2, hg⟩ := NoRaise.DRE.of_bind_ok hg
  obtain ⟨G0, -, hg⟩ := NoRaise.DRE.of_bind_ok hg
  obtain ⟨raw, -, hg⟩ := NoRaise.DRE.of_bind_ok hg
  cases Except.ok.inj hg
  exact ⟨Q2, hQ2, by rw [← e]; rfl⟩

/-- An outcome of the member `grade2_block_with` under `c` is the image of the spec's grade-2
    candidate of round `r`, on the store with the saved grades read from `c` at round `r`. -/
theorem grade2_block_with_shape {c : Spec.SavedGrades V} {E : Env V}
    {hc : Protocol.HealConfig} {st : Spec.Store V} {r : Round}
    {Q : Option (Block V)}
    (h : Returns (Member.grade2_block_with c E hc st r) Q) :
    ∃ Q2, Spec.Protocol.grade2Block
        { Spec.Store.ofImage st with saved_grades := fill (Spec.Protocol.advance_to_round (st.contractOfImage c) r) }
        (Spec.Protocol.round_grades
          { Spec.Store.ofImage st with saved_grades := fill (Spec.Protocol.advance_to_round (st.contractOfImage c) r) }
          r) = .ok Q2 ∧ Q = Q2.map Spec.Block.toProof := by
  unfold Member.grade2_block_with at h
  rw [returns_successOutcomes] at h
  obtain ⟨Q2, hQ2, e⟩ := except_map_eq_ok h
  exact ⟨Q2, hQ2, e.symm⟩

omit [Fintype V] [Inhabited V] in
/-- The root of the spec's SG vote depends on the grade read's grade-2 candidate only through its
    root. -/
theorem currentSGVote_root_congr (st : Spec.Store V) (g : Spec.Protocol.GradeRead V)
    {X Y : Option (Spec.Block V)} (h : X.map Spec.Block.root = Y.map Spec.Block.root) :
    (Spec.Protocol.currentSGVote st { g with Q2 := X }).root =
      (Spec.Protocol.currentSGVote st { g with Q2 := Y }).root := by
  unfold Spec.Protocol.currentSGVote
  cases X <;> cases Y <;> simp_all [Id.run, Option.value] <;> split <;> simp_all [pure]

omit [Fintype V] [Inhabited V] in
/-- Two grade-2 candidates with the same root give SG votes of round `r` with the same root. -/
theorem get_sg_vote_with_root_congr {st : Spec.Store V} {r : Round}
    {X Y : Option (Spec.Block V)} (h : X.map Spec.Block.root = Y.map Spec.Block.root)
    {W W' : Spec.Block V}
    (hW : Spec.Protocol.get_sg_vote_with st r X = .ok W)
    (hW' : Spec.Protocol.get_sg_vote_with st r Y = .ok W') : W.root = W'.root := by
  unfold Spec.Protocol.get_sg_vote_with at hW hW'
  obtain ⟨g, hg, hW⟩ := NoRaise.DRE.of_bind_ok hW
  obtain ⟨g', hg', hW'⟩ := NoRaise.DRE.of_bind_ok hW'
  have e : g = g' := Except.ok.inj (hg.symm.trans hg')
  subst e
  rw [← Except.ok.inj hW, ← Except.ok.inj hW']
  exact currentSGVote_root_congr st g h

omit [Inhabited V] in
/-- The confirmed root of an answer of the spec's `attestation_input` is the root of the SG vote of
    the store's round for the grade-2 candidate of that round. -/
theorem attestation_input_confirmed {C : Spec.Config} {v : V} {st : Spec.Store V}
    {i : Spec.Protocol.AttestationInput V}
    (h : Spec.Protocol.attestation_input C v st = .ok i) :
    ∃ A_G2 W, Spec.Protocol.grade2_block_with st (C.round_of st.s) = .ok A_G2 ∧
      Spec.Protocol.get_sg_vote_with st (C.round_of st.s) A_G2 = .ok W ∧
      i.confirmed = some W.root := by
  unfold Spec.Protocol.attestation_input at h
  obtain ⟨A_G2, hA, h⟩ := NoRaise.DRE.of_bind_ok h
  obtain ⟨⟨fields, h_j, J, h_F⟩, -, h⟩ := NoRaise.DRE.of_bind_ok h
  obtain ⟨W, hW, h⟩ := NoRaise.DRE.of_bind_ok h
  cases Except.ok.inj h
  exact ⟨A_G2, W, hA, hW, rfl⟩

/-- An outcome of the member `get_sg_vote_with` under `c` is the image of an answer of the spec's
    `get_sg_vote_with` of round `r`, on the store with the saved grades read from `c` at round `r`. -/
theorem get_sg_vote_with_shape {c : Spec.SavedGrades V} {E : Env V}
    {hc : Protocol.HealConfig} {st : Spec.Store V} {r : Round}
    {A_G2 : Option (Block V)} {W : Block V}
    (h : Returns (Member.get_sg_vote_with c E hc st r A_G2) W) :
    ∃ W', Spec.Protocol.get_sg_vote_with
        { Spec.Store.ofImage st with saved_grades := fill (Spec.Protocol.advance_to_round (st.contractOfImage c) r) }
        r (A_G2.map Spec.Block.toSpec) = .ok W' ∧ W = W'.toProof := by
  unfold Member.get_sg_vote_with at h
  rw [returns_successOutcomes] at h
  obtain ⟨W', hW', e⟩ := except_map_eq_ok h
  exact ⟨W', hW', e.symm⟩

omit [Fintype V] [Inhabited V] in
/-- Mapping a candidate by `toProof` and back by `toSpec` keeps its root. -/
theorem map_toSpec_toProof_root (Q : Option (Spec.Block V)) :
    ((Q.map Spec.Block.toProof).map Spec.Block.toSpec).map Spec.Block.root =
      Q.map Spec.Block.root := by
  cases Q with
  | none => rfl
  | some B =>
    simp only [Option.map_some, Option.some.injEq]
    rw [ForkChoiceImages.toSpec_root, Spec.Block.toProof_root,
      Spec.BlockId.toSpec_toProof]

omit [Fintype V] [Inhabited V] in
/-- Mapping a list of Goldfish votes by `toProof` and back gives, as a set, the list's votes. -/
theorem map_voteToSpec_toFinset (l : List (Spec.GoldfishVote V)) :
    ((l.map Spec.GoldfishVote.toProof).toFinset).map ForkChoiceGrades.voteToSpecEmb =
      l.toFinset := by
  ext u
  simp only [Finset.mem_map, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    simpa [ForkChoiceGrades.voteToSpecEmb] using hw
  · intro hu
    exact ⟨_, ⟨u, hu, rfl⟩, by simp [ForkChoiceGrades.voteToSpecEmb]⟩

omit [Inhabited V] in
/-- The spec's Goldfish vote duty sends a vote for the root of the head it computes for the slot
    before the store's when the validator is in the slot's committee, and nothing otherwise. -/
theorem goldfish_vote_sent {C : Spec.Config} {P : Spec.Provisional V} {v : V}
    {st : Spec.Store V} {l : List (Spec.NamedObject V)}
    {out : Spec.Store V × List (Spec.NamedObject V)}
    (h : (Spec.Protocol.goldfish_vote C P v st).run l = .ok out) :
    ∃ votes sup tree H, Spec.Protocol.voter_view C st st.s = .ok votes ∧
      Spec.Protocol.voter_support_view C st st.s = .ok sup ∧
      Spec.Protocol.voter_filtered_block_tree C st st.s = .ok tree ∧
      Spec.Protocol.get_head_in_tree_with_layer C st tree votes sup (st.s - 1) = .ok H ∧
      ((v ∈ P.committee st.s ∧
          out.2 = l ++ [Spec.NamedObject.gfVote ⟨v, st.s, H.root⟩]) ∨
        (v ∉ P.committee st.s ∧ out.2 = l)) := by
  unfold Spec.Protocol.goldfish_vote at h
  dsimp only at h
  rw [NoRaise.DREB.run_bind_ok_iff] at h
  obtain ⟨votes, l1, h1, h⟩ := h
  rw [NoRaise.DREB.liftM_run_ok_iff] at h1
  obtain ⟨h1, rfl⟩ := h1
  rw [NoRaise.DREB.run_bind_ok_iff] at h
  obtain ⟨sup, l2, h2, h⟩ := h
  rw [NoRaise.DREB.liftM_run_ok_iff] at h2
  obtain ⟨h2, rfl⟩ := h2
  rw [NoRaise.DREB.run_bind_ok_iff] at h
  obtain ⟨tree, l3, h3, h⟩ := h
  rw [NoRaise.DREB.liftM_run_ok_iff] at h3
  obtain ⟨h3, rfl⟩ := h3
  rw [NoRaise.DREB.run_bind_ok_iff] at h
  obtain ⟨H, l4, h4, h⟩ := h
  rw [NoRaise.DREB.liftM_run_ok_iff] at h4
  obtain ⟨h4, rfl⟩ := h4
  refine ⟨votes, sup, tree, H, h1, h2, h3, h4, ?_⟩
  split_ifs at h with hv
  · rw [NoRaise.DREB.run_bind_ok_iff] at h
    obtain ⟨_, l5, h5, h⟩ := h
    rw [NoRaise.DREB.pure_run_ok_iff] at h
    subst h
    have e5 := Except.ok.inj h5
    simp only [Prod.mk.injEq, true_and] at e5
    subst e5
    exact Or.inl ⟨hv, rfl⟩
  · rw [NoRaise.DREB.pure_run_ok_iff] at h
    subst h
    exact Or.inr ⟨hv, rfl⟩

/-- An answer of the spec's `voter_filtered_block_tree` holds only blocks of the store's tree. -/
theorem voter_filtered_block_tree_subset {C : Spec.Config} {st : Spec.Store V}
    {s : Slot} {T : Finset (Spec.Block V)}
    (h : Spec.Protocol.voter_filtered_block_tree C st s = .ok T) : T ⊆ st.T := by
  unfold Spec.Protocol.voter_filtered_block_tree at h
  obtain ⟨P, hP, h⟩ := NoRaise.DRE.of_bind_ok h
  rw [← Except.ok.inj h]
  intro B hB
  rw [ForkChoiceImages.draft_filtered_from_def] at hB
  simp only [Spec.Protocol.viable_tree, Spec.Protocol.finalized_descendants,
    Finset.mem_filter] at hB
  exact ForkChoiceImages.processed_subset_of_ok C st s hP hB.1.1.1

omit [Fintype V] [Inhabited V] in
/-- Mapping a set of Goldfish votes by `toProof` and back gives the same set. -/
theorem map_toProofEmb_voteToSpec (S : Finset (Spec.GoldfishVote V)) :
    (S.map Spec.GoldfishVote.toProofEmb).map ForkChoiceGrades.voteToSpecEmb = S := by
  ext u
  simp [ForkChoiceGrades.voteToSpecEmb]

/-- The vote of an outcome of the Goldfish vote duty member under `c` is, for the outcomes of the
    members giving the voter's tree, views and head in that tree for the slot before the store's,
    the vote of the node's validator for the head's root when the validator is in the slot's
    committee, and none otherwise. -/
theorem duties_goldfish_vote_with_snd_spec {c : Spec.SavedGrades V} {E : Env V}
    {hc : Protocol.HealConfig} {nd : Protocol.Node V} {st : SpecRecord.OkStore V}
    {D : Spec.Store V × Option (GoldfishVote V)}
    (hD : Returns (Member.duties_goldfish_vote_with c E hc nd st.val) D)
    {tree : Finset (Block V)} {votes support : Finset (GoldfishVote V)} {H : Block V}
    (htree : Returns (Member.voter_filtered_block_tree E st.val st.val.s) tree)
    (hvotes : Returns (Member.voter_view E st.val st.val.s) votes)
    (hsupport : Returns (Member.voter_support_view E st.val st.val.s) support)
    (hH : Returns (Member.get_head_in_tree_with_layer c E hc st.val tree votes support
      (st.val.s - 1)) H) :
    D.2 = if nd.val_index ∈ E.committee st.val.s then some ⟨nd.val_index, st.val.s, H.root⟩
      else none := by
  unfold Member.duties_goldfish_vote_with at hD
  rw [returns_successOutcomes] at hD
  obtain ⟨out, hout, e⟩ := except_map_eq_ok hD
  obtain ⟨vd, sd, td, Hd, h1, h2, h3, h4, hsent⟩ := goldfish_vote_sent hout
  obtain ⟨T', hT', rfl⟩ := except_map_eq_ok ((returns_successOutcomes _ _).1 htree)
  obtain ⟨V', hV', rfl⟩ := except_map_eq_ok ((returns_successOutcomes _ _).1 hvotes)
  obtain ⟨S', hS', rfl⟩ := except_map_eq_ok ((returns_successOutcomes _ _).1 hsupport)
  have eT : td = T' := Except.ok.inj (h3.symm.trans hT')
  have eV : vd = V' := Except.ok.inj (h1.symm.trans hV')
  have eS : sd = S' := Except.ok.inj (h2.symm.trans hS')
  subst eT eV eS
  obtain ⟨H', hH', rfl⟩ := except_map_eq_ok ((returns_successOutcomes _ _).1 hH)
  have hsub := voter_filtered_block_tree_subset h3
  rw [ForkChoiceImages.image_map_blockOfImage_of_subset st hsub,
    map_toProofEmb_voteToSpec, map_toProofEmb_voteToSpec] at hH'
  have eH : Hd = H' := Except.ok.inj (h4.symm.trans hH')
  subst eH
  rw [← e]
  rcases hsent with ⟨hv, hl⟩ | ⟨hv, hl⟩
  · rw [Spec.Provisional.toSpec_committee] at hv
    replace hv : nd.val_index ∈ E.committee st.val.s := hv
    rw [if_pos hv]
    show (Member.firstSentGoldfishVote out.2).map Spec.GoldfishVote.toProof = _
    rw [hl]
    simp [Member.firstSentGoldfishVote, Spec.GoldfishVote.toProof,
      Spec.Block.toProof_root]
  · rw [Spec.Provisional.toSpec_committee] at hv
    replace hv : ¬ nd.val_index ∈ E.committee st.val.s := hv
    rw [if_neg hv]
    show (Member.firstSentGoldfishVote out.2).map Spec.GoldfishVote.toProof = _
    rw [hl]
    rfl


/-! ## The attestation input and the finality-gadget source -/

omit [Fintype V] [Inhabited V] in
/-- If the height pair the spec's `height_pair` signs is a vote at `h` for `T`, the fields were
    `(h, T, ν)` for some flag `ν`. -/
theorem height_pair_vote_fields {sh : Spec.SigningHistory}
    {fields : Option (Height × Spec.BlockId × Bool)}
    {fp : Option Spec.FinalityPair} {h : Height} {T : Spec.BlockId} {b : Bool}
    (hp : Spec.Protocol.height_pair sh fields fp = .vote h T b) :
    ∃ ν, fields = some (h, T, ν) := by
  unfold Spec.Protocol.height_pair at hp
  cases fields with
  | none => simp [Id.run] at hp
  | some f =>
    obtain ⟨h', T', ν⟩ := f
    refine ⟨ν, ?_⟩
    simp only [Id.run, ne_eq, reduceCtorEq, not_false_eq_true, Option.value, Option.get_some] at hp
    split_ifs at hp <;> cases hp <;> rfl

omit [DecidableEq V] [Fintype V] [Inhabited V] in
/-- The height pair of the attestation the spec's `create` builds from the input `i` is
    `height_pair` of the signing history at `i`'s fields and the finality pair `finality_pair` signs
    for `i`'s justification. -/
theorem create_height_pair (sh : Spec.SigningHistory)
    (i : Spec.Protocol.AttestationInput V) :
    (Spec.Protocol.create sh i).2.height_pair =
      Spec.Protocol.height_pair sh i.fields
        (Spec.Protocol.finality_pair sh i.h_j i.J i.h_F) := rfl

omit [Inhabited V] in
/-- The fields of an answer of the spec's `attestation_input` are the height, the root of the height
    target and the flag of the store's chain state at the finality-gadget source of the round's
    grade-2 candidate, and none when there is no source. -/
theorem attestation_input_fields {C : Spec.Config} {v : V} {st : Spec.Store V}
    {i : Spec.Protocol.AttestationInput V}
    (h : Spec.Protocol.attestation_input C v st = .ok i) :
    ∃ A_G2 src, Spec.Protocol.grade2_block_with st (C.round_of st.s) = .ok A_G2 ∧
      Spec.Protocol.fg_source_with st (C.round_of st.s) A_G2 = .ok src ∧
      i.fields = src.map (fun q => ((st.σ q).h, (st.σ q).T_h.root, (st.σ q).nj)) := by
  unfold Spec.Protocol.attestation_input at h
  obtain ⟨A_G2, hA, h⟩ := NoRaise.DRE.of_bind_ok h
  obtain ⟨⟨fields, h_j, J, h_F⟩, hf, h⟩ := NoRaise.DRE.of_bind_ok h
  obtain ⟨W, -, h⟩ := NoRaise.DRE.of_bind_ok h
  cases Except.ok.inj h
  unfold Spec.Protocol.get_fg_vote_with at hf
  obtain ⟨sv, -, hf⟩ := NoRaise.DRE.of_bind_ok hf
  obtain ⟨H, -, hf⟩ := NoRaise.DRE.of_bind_ok hf
  obtain ⟨src, hsrc, hf⟩ := NoRaise.DRE.of_bind_ok hf
  refine ⟨A_G2, src, hA, hsrc, ?_⟩
  cases src with
  | none =>
    simp [pure, Except.pure] at hf
    exact hf.1.symm
  | some q =>
    simp [pure, Except.pure, Option.value] at hf
    exact hf.1.symm

omit [Fintype V] [Inhabited V] in
/-- With no grade-2 candidate, the spec's finality-gadget source is none. -/
theorem fg_source_with_none (st : Spec.Store V) (r : Spec.Round) :
    Spec.Protocol.fg_source_with st r none = .ok none := rfl

omit [Fintype V] [Inhabited V] in
/-- An answer of the spec's `deepest_clear floor C test` is a block of the chain of `C`. -/
theorem deepest_clear_mem_chain {floor C B : Spec.Block V}
    {test : Spec.Block V → Bool}
    (h : Spec.Protocol.deepest_clear floor C test = some B) :
    B ∈ Spec.Protocol.chain_of C := by
  unfold Spec.Protocol.deepest_clear Spec.Block.deepest? at h
  unfold Spec.pickUnique? at h
  split at h
  · rename_i hex
    rw [← Option.some.inj h]
    exact List.mem_toFinset.mp (Finset.mem_filter.mp (Finset.choose_mem _ _ hex)).1
  · cases h

omit [Fintype V] [Inhabited V] in
/-- When `T` is parent-closed and holds a block `X` with the image of `C`, the image of every block
    of the chain of `C` is the image of a block of `T`. -/
theorem toProof_mem_image_of_mem_chain {T : Finset (Spec.Block V)}
    (hpar : NoRaise.ParentClosed T) {X C B : Spec.Block V} (hX : X ∈ T)
    (hXC : X.toProof = C.toProof) (hB : B ∈ Spec.Protocol.chain_of C) :
    B.toProof ∈ T.image Spec.Block.toProof := by
  have hc : ∀ D : Spec.Block V, DecoupledConsensusModel.Protocol.chain_of D.toProof =
      (Spec.Protocol.chain_of D).map Spec.Block.toProof := fun D => by
    unfold DecoupledConsensusModel.Protocol.chain_of Spec.Protocol.chain_of
    rw [Spec.Block.toProof_depth, Spec.Protocol.chain_up_toProof]
  have h1 : B.toProof ∈ (Spec.Protocol.chain_of X).map Spec.Block.toProof := by
    rw [← hc, hXC, hc]
    exact List.mem_map_of_mem hB
  obtain ⟨Y, hY, hYB⟩ := List.mem_map.mp h1
  exact Finset.mem_image.mpr ⟨Y, Spec.Protocol.mem_of_mem_chain_up hpar _ hX hY, hYB⟩

omit [Fintype V] [Inhabited V] in
/-- A block the spec's `grade2Block` answers is a block of the filtered tree. -/
theorem grade2Block_mem_filtered {st : Spec.Store V} {grades : Spec.RoundGrades V}
    {Q : Spec.Block V} (h : Spec.Protocol.grade2Block st grades = .ok (some Q)) :
    Q ∈ Spec.Protocol.get_filtered_block_tree st := by
  unfold Spec.Protocol.grade2Block at h
  obtain ⟨G, -, h⟩ := NoRaise.DRE.of_bind_ok h
  exact active_prefix_mem_filtered (Except.ok.inj h)

omit [Inhabited V] in
/-- An answer of the spec's `fg_source_with` for a candidate `q` is `q`, or the deepest block on the
    chain of the live confirmed block that descends from `q` and passes the grade-0 test of the
    round's grade-0 block. -/
theorem draft_fg_source_some_cases {st : Spec.Store V} {r : Spec.Round}
    {q : Spec.Block V} {o : Option (Spec.Block V)}
    (h : Spec.Protocol.fg_source_with st r (some q) = .ok o) :
    o = some q ∨ ∃ G0 B, (Spec.Protocol.round_grades st r).g0 = .computed G0 ∧
      Spec.Protocol.deepest_clear q st.live_confirmed
        (Spec.Protocol.G0_compatible G0) = some B ∧ o = some B := by
  unfold Spec.Protocol.fg_source_with at h
  simp only [ne_eq, reduceCtorEq, not_false_eq_true, Option.value, Option.get_some] at h
  obtain ⟨G0, hG0, h⟩ := NoRaise.DRE.of_bind_ok h
  have hg : (Spec.Protocol.round_grades st r).g0 = .computed G0 := by
    revert hG0
    cases (Spec.Protocol.round_grades st r).g0 with
    | pending => intro hG0; cases hG0
    | computed G => intro hG0; cases hG0; rfl
  split at h
  · rename_i hne
    obtain ⟨B, hB⟩ := Option.ne_none_iff_exists'.mp hne
    right
    refine ⟨G0, B, hg, hB, ?_⟩
    rw [← Except.ok.inj h]
    simp [hB, Option.value]
  · left
    exact (Except.ok.inj h).symm

omit [Fintype V] [Inhabited V] in
/-- The spec's `currentSGVote` is one of four blocks: the deepest clear block from the anchor to the
    live confirmed block, the grade-2 candidate, the fgroot, or the anchor. -/
theorem currentSGVote_cases (st : Spec.Store V) (g : Spec.Protocol.GradeRead V) :
    (∃ B, Spec.Protocol.deepest_clear g.anchor st.live_confirmed g.clear = some B ∧
        Spec.Protocol.currentSGVote st g = B) ∨
      (∃ Q, g.Q2 = some Q ∧ Spec.Protocol.currentSGVote st g = Q) ∨
      Spec.Protocol.currentSGVote st g = Spec.Protocol.get_fg_root st ∨
      Spec.Protocol.currentSGVote st g = g.anchor := by
  unfold Spec.Protocol.currentSGVote
  simp only [Id.run, pure, ne_eq]
  cases hd : Spec.Protocol.deepest_clear g.anchor st.live_confirmed g.clear with
  | some B => left; exact ⟨B, rfl, by simp [Option.value]⟩
  | none =>
    cases hq : g.Q2 with
    | some Q => right; left; exact ⟨Q, rfl, by simp [Option.value]⟩
    | none =>
      right; right
      cases g.rawG2
      · right; simp
      · left; simp

omit [Inhabited V] in
/-- The anchor of an answer of the spec's `round_grade_read` is the fgroot or a block of the
    filtered tree. -/
theorem round_grade_read_anchor_cases {st : Spec.Store V} {r : Spec.Round}
    {g : Spec.Protocol.GradeRead V}
    (h : Spec.Protocol.round_grade_read st r = .ok g) :
    g.anchor = Spec.Protocol.get_fg_root st ∨
      g.anchor ∈ Spec.Protocol.get_filtered_block_tree st := by
  unfold Spec.Protocol.round_grade_read at h
  obtain ⟨A, hA, h⟩ := NoRaise.DRE.of_bind_ok h
  obtain ⟨Q2, -, h⟩ := NoRaise.DRE.of_bind_ok h
  obtain ⟨G0, -, h⟩ := NoRaise.DRE.of_bind_ok h
  obtain ⟨raw, -, h⟩ := NoRaise.DRE.of_bind_ok h
  cases Except.ok.inj h
  exact anchor_cases hA

omit [Fintype V] [Inhabited V] in
/-- An answer `B` of the spec's `deepest_clear floor C test` is a block of the chain of `C`, a
    descendant of or equal to `floor`, that passes `test`. -/
theorem deepest_clear_spec {floor C B : Spec.Block V}
    {test : Spec.Block V → Bool}
    (h : Spec.Protocol.deepest_clear floor C test = some B) :
    B ∈ Spec.Protocol.chain_of C ∧ floor.ancestorEq B = true ∧ test B = true := by
  unfold Spec.Protocol.deepest_clear Spec.Block.deepest? at h
  unfold Spec.pickUnique? at h
  split at h
  · rename_i hex
    rw [← Option.some.inj h]
    have hm := Finset.mem_filter.mp (Finset.choose_mem _ _ hex)
    rw [Bool.and_eq_true] at hm
    exact ⟨List.mem_toFinset.mp hm.1, hm.2.1, hm.2.2⟩
  · cases h

omit [Fintype V] [Inhabited V] in
/-- The chain of the image of a block is the images of its chain. -/
theorem chain_of_toProof (D : Spec.Block V) :
    DecoupledConsensusModel.Protocol.chain_of D.toProof =
      (Spec.Protocol.chain_of D).map Spec.Block.toProof := by
  unfold DecoupledConsensusModel.Protocol.chain_of Spec.Protocol.chain_of
  rw [Spec.Block.toProof_depth, Spec.Protocol.chain_up_toProof]


/-! ## The confirmation records -/

/-- The blocks the confirmation update may write on the store `st`: the fgroot and the blocks of the
    filtered tree. -/
def ConfirmationGood (st : Spec.Store V) (X : Spec.Block V) : Prop :=
  X = Spec.Protocol.get_fg_root st ∨ X ∈ Spec.Protocol.get_filtered_block_tree st

omit [Inhabited V] in
/-- The spec's confirmation update on `st` writes as live confirmed block the fgroot or a block of
    the filtered tree; the stable record is such a block or is kept; the confirmation record is such
    a block, or is kept, or is the stable record as it was. -/
theorem update_confirmation_good {C : Spec.Config} {st st' : Spec.Store V}
    {s : Slot} (h : Spec.Protocol.update_confirmation C st s = .ok st') :
    ConfirmationGood st st'.live_confirmed ∧
      (ConfirmationGood st st'.latest_stable ∨ st'.latest_stable = st.latest_stable) ∧
      (ConfirmationGood st st'.latest_confirmed ∨ st'.latest_confirmed = st.latest_confirmed ∨
        st'.latest_confirmed = st.latest_stable) := by
  unfold Spec.Protocol.update_confirmation at h
  obtain ⟨_, -, h⟩ := NoRaise.DRE.of_bind_ok h
  obtain ⟨_, -, h⟩ := NoRaise.DRE.of_bind_ok h
  dsimp only at h
  obtain ⟨A, hA, h⟩ := NoRaise.DRE.of_bind_ok h
  obtain ⟨H, hH, h⟩ := NoRaise.DRE.of_bind_ok h
  obtain ⟨he, -, h⟩ := NoRaise.DRE.of_bind_ok h
  obtain ⟨G, hG, h⟩ := NoRaise.DRE.of_bind_ok h
  obtain ⟨S?, hS, h⟩ := NoRaise.DRE.of_bind_ok h
  have gA : ConfirmationGood st A := by
    rw [get_sg_root_with_eq_anchor] at hA
    exact anchor_cases hA
  have gH : ConfirmationGood st H := by
    unfold Spec.Protocol.ghost at hH
    rcases (ghost_walk_mem_ancestorEq _ _ _ hH).1 with e | e
    · rw [e]; exact gA
    · exact Or.inr e
  have gG : ConfirmationGood st G := by
    unfold Spec.Protocol.round_stable_root at hG
    obtain ⟨G2, -, hG⟩ := NoRaise.DRE.of_bind_ok hG
    rw [← Except.ok.inj hG]
    unfold Spec.Protocol.stable_root
    simp only [Id.run, pure]
    split
    · rename_i hne
      obtain ⟨X, hX⟩ := Option.ne_none_iff_exists'.mp hne
      simp only [hX, Option.value]
      exact Or.inr (active_prefix_mem_filtered hX)
    · exact Or.inl rfl
  have gS : ∀ X, S? = some X → ConfirmationGood st X := by
    intro X hX
    unfold Spec.Protocol.confirmation_candidate at hS
    obtain ⟨G2, -, hS⟩ := NoRaise.DRE.of_bind_ok hS
    rw [← Except.ok.inj hS] at hX
    exact Or.inr (active_prefix_mem_filtered hX)
  have adv : ∀ old cand : Spec.Block V,
      Spec.Protocol.advance_confirmed old cand = old ∨
        Spec.Protocol.advance_confirmed old cand = cand := by
    intro old cand
    unfold Spec.Protocol.advance_confirmed
    simp only [Id.run, pure]
    split <;> simp
  have flo : ∀ stable cand old : Spec.Block V,
      Spec.Protocol.floor_on_stable stable cand old = cand ∨
        Spec.Protocol.floor_on_stable stable cand old = old ∨
        Spec.Protocol.floor_on_stable stable cand old = stable := by
    intro stable cand old
    unfold Spec.Protocol.floor_on_stable
    simp only [Id.run, pure]
    split
    · simp
    · split <;> simp
  have advG : ∀ old X : Spec.Block V, ConfirmationGood st X →
      ConfirmationGood st (Spec.Protocol.advance_confirmed old X) ∨
        Spec.Protocol.advance_confirmed old X = old := by
    intro old X hX
    rcases adv old X with e | e <;> rw [e]
    · exact Or.inr rfl
    · exact Or.inl hX
  have gS' : ∀ hne : S? ≠ none, ConfirmationGood st (S?.value hne) := by
    intro hne
    obtain ⟨X, hX⟩ := Option.ne_none_iff_exists'.mp hne
    subst hX
    exact gS X rfl
  have gls := advG st.latest_stable G gG
  split_ifs at h with h1 h2 <;>
  · simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    refine ⟨?_, gls, ?_⟩
    · first | exact gH | exact Or.inl rfl
    · rcases flo (Spec.Protocol.advance_confirmed st.latest_stable G) _ st.latest_confirmed
        with e | e | e <;> rw [e]
      · first
        | exact Or.inr (Or.inl rfl)
        | (rcases advG st.latest_confirmed _ gH with g | g
           · exact Or.inl g
           · exact Or.inr (Or.inl g))
        | (rcases advG st.latest_confirmed _ (gS' _) with g | g
           · exact Or.inl g
           · exact Or.inr (Or.inl g))
      · exact Or.inr (Or.inl rfl)
      · rcases gls with g | g
        · exact Or.inl g
        · exact Or.inr (Or.inr g)


/-! ## The proposal's attestations -/

omit [Inhabited V] in
/-- The spec's `included_attestations_in_window`, its loop written out: for the store's blocks in
    the order `sorted_blocks` answers, the attestations of each block eligible under
    `may_repropose_attestations_of` whose round is in the admission window, concatenated. -/
theorem included_attestations_in_window_eq (C : Spec.Config) (st : Spec.Store V)
    {bodies : List (Spec.Block V)} (h : Spec.Protocol.sorted_blocks st = .ok bodies) :
    Spec.Protocol.included_attestations_in_window C st =
      .ok (bodies.flatMap fun B => if Spec.Protocol.may_repropose_attestations_of C st B then
        B.attestations.filter (fun row => Spec.Protocol.in_admission_window C st row.round)
        else []) := by
  have key : ∀ (l : List (Spec.Block V)) (acc : List (Spec.Attestation V)),
      forIn (m := DC.DRE) l acc (fun B r =>
        if Spec.Protocol.may_repropose_attestations_of C st B = true then
          pure (ForInStep.yield (r ++ B.attestations.filter
            (fun row => Spec.Protocol.in_admission_window C st row.round)))
        else pure (ForInStep.yield r)) =
      .ok (acc ++ l.flatMap fun B => if Spec.Protocol.may_repropose_attestations_of C st B then
        B.attestations.filter (fun row => Spec.Protocol.in_admission_window C st row.round)
        else []) := by
    intro l
    induction l with
    | nil => intro acc; simp [pure, Except.pure]
    | cons B l ih =>
      intro acc
      simp only [pure, Except.pure] at ih ⊢
      rw [List.forIn_cons]
      by_cases hB : Spec.Protocol.may_repropose_attestations_of C st B = true
      · simp only [hB, if_true, bind, Except.bind]
        rw [ih]
        simp [List.flatMap_cons, hB, List.append_assoc]
      · simp only [hB, Bool.false_eq_true, if_false, bind, Except.bind]
        rw [ih]
        simp [List.flatMap_cons, hB]
  unfold Spec.Protocol.included_attestations_in_window
  rw [h]
  dsimp only
  simp only [bind, Except.bind, key, List.nil_append]
  rfl

omit [Inhabited V] in
/-- Every block of an answer of the spec's `sorted_blocks` is a block of the store's tree. -/
theorem sorted_blocks_mem {st : Spec.Store V} {bodies : List (Spec.Block V)}
    (h : Spec.Protocol.sorted_blocks st = .ok bodies) : ∀ B ∈ bodies, B ∈ st.T := by
  unfold Spec.Protocol.sorted_blocks at h
  generalize Spec.Protocol.sorted_block_roots st = roots at h
  induction roots generalizing bodies with
  | nil =>
    simp [pure, Except.pure] at h
    subst h
    intro B hB; cases hB
  | cons root roots ih =>
    rw [List.mapM_cons] at h
    obtain ⟨B0, hB0, h⟩ := NoRaise.DRE.of_bind_ok h
    obtain ⟨bs, hbs, h⟩ := NoRaise.DRE.of_bind_ok h
    have e := Except.ok.inj h
    subst e
    intro B hB
    rcases List.mem_cons.mp hB with rfl | hB
    · cases hp : Spec.pickUnique? st.T (fun B => decide (B.root = root)) with
      | none => rw [hp] at hB0; cases hB0
      | some B' =>
        rw [hp] at hB0
        have e : B' = B := Except.ok.inj hB0
        subst e
        unfold Spec.pickUnique? at hp
        split at hp
        · rename_i hex
          rw [← Option.some.inj hp]
          exact Finset.choose_mem _ _ hex
        · cases hp
    · exact ih hbs B hB

omit [Inhabited V] in
/-- When the spec's `included_attestations_in_window` answers, `sorted_blocks` answers too and the
    attestations are read off its answer by `included_attestations_in_window_eq`. -/
theorem included_attestations_in_window_ok {C : Spec.Config} {st : Spec.Store V}
    {rows : List (Spec.Attestation V)}
    (h : Spec.Protocol.included_attestations_in_window C st = .ok rows) :
    ∃ bodies, Spec.Protocol.sorted_blocks st = .ok bodies ∧
      rows = bodies.flatMap fun B => if Spec.Protocol.may_repropose_attestations_of C st B then
        B.attestations.filter (fun row => Spec.Protocol.in_admission_window C st row.round)
        else [] := by
  cases hs : Spec.Protocol.sorted_blocks st with
  | error e =>
    unfold Spec.Protocol.included_attestations_in_window at h
    rw [hs] at h
    cases h
  | ok bodies =>
    rw [included_attestations_in_window_eq C st hs] at h
    exact ⟨bodies, rfl, (Except.ok.inj h).symm⟩

omit [Fintype V] [Inhabited V] in
/-- The spec's `capPerSigner` keeps only attestations of its list. -/
theorem capPerSigner_subset (atts : List (Spec.Attestation V)) :
    ∀ a ∈ Spec.Protocol.capPerSigner atts, a ∈ atts := by
  have key : ∀ (p : Spec.Attestation V → List (Spec.Attestation V) → Bool)
      (l acc : List (Spec.Attestation V)),
      ∀ a, a ∈ (Id.run (forIn (m := Id) l acc (fun x r =>
        if p x r = true then pure (ForInStep.yield (r ++ [x])) else pure (ForInStep.yield r)))) →
        a ∈ acc ∨ a ∈ l := by
    intro p l
    induction l with
    | nil => intro acc a ha; exact Or.inl ha
    | cons x l ih =>
      intro acc a ha
      rw [List.forIn_cons] at ha
      by_cases hp : p x acc = true
      · simp only [hp, if_true] at ha
        rcases ih _ a ha with h | h
        · rcases List.mem_append.mp h with h | h
          · exact Or.inl h
          · rw [List.mem_singleton.mp h]; exact Or.inr (List.mem_cons_self ..)
        · exact Or.inr (List.mem_cons_of_mem _ h)
      · simp only [hp, Bool.false_eq_true, if_false] at ha
        rcases ih _ a ha with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)
  intro a ha
  unfold Spec.Protocol.capPerSigner at ha
  rcases key _ atts [] a ha with h | h
  · cases h
  · exact h

omit [Inhabited V] in
/-- Every attestation an answer of the spec's `attestations_to_include` offers has a round at most
    the store's round. -/
theorem attestations_to_include_round_le {C : Spec.Config} {st : Spec.Store V}
    {rows : List (Spec.Attestation V)}
    (h : Spec.Protocol.attestations_to_include C st = .ok rows) :
    ∀ a ∈ rows, a.round ≤ C.round_of st.s := by
  unfold Spec.Protocol.attestations_to_include at h
  obtain ⟨carried, hc, h⟩ := NoRaise.DRE.of_bind_ok h
  cases Except.ok.inj h
  obtain ⟨bodies, -, rfl⟩ := included_attestations_in_window_ok hc
  have hw : ∀ r, Spec.Protocol.in_admission_window C st r = true → r ≤ C.round_of st.s := by
    intro r hr
    unfold Spec.Protocol.in_admission_window at hr
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
    exact hr.2
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · unfold Spec.Protocol.attestations_in_window at ha
    exact hw _ (List.mem_filter.mp ha).2
  · obtain ⟨B, -, hB⟩ := List.mem_flatMap.mp ha
    split at hB
    · exact hw _ (List.mem_filter.mp hB).2
    · cases hB

/-! ## The blocks the contract members read stand for their images -/

/-- The store a contract-taking member hands the spec at round `r`: `st` read through its tree, with
    the saved grades `c` read through the tree, brought to round `r` and filled. -/
abbrev contractStore (st : Spec.Store V) (c : Spec.SavedGrades V)
    (r : Round) : Spec.Store V :=
  { Spec.Store.ofImage st with saved_grades := fill (Spec.Protocol.advance_to_round (st.contractOfImage c) r) }

omit [Fintype V] [Inhabited V] in
/-- On a store with distinct roots and a parent-closed tree, every block of the chain of a block
    that stands for its image stands for its own image. -/
theorem blockOfImage_of_mem_chain (st : Spec.Store V) (hT : NoRaise.DistinctRoots st.T)
    (hpar : NoRaise.ParentClosed st.T) {C B : Spec.Block V}
    (hC : st.blockOfImage C.toProof = C) (hB : B ∈ Spec.Protocol.chain_of C) :
    st.blockOfImage B.toProof = B := by
  rw [← hC] at hB
  exact Spec.Protocol.chain_up_blockOfImage st hT.injOn_toProof hpar _ C.toProof B hB

omit [Fintype V] [Inhabited V] in
/-- The spec's deepest clear block between two blocks standing for their images, with a test `test'`
    that agrees with `test` on every block standing for its image, is, mapped,
    `DecoupledConsensusModel.Protocol.deepest_clear` between the images with `test`. -/
theorem deepest_clear_of_fixed (st : Spec.Store V) (hT : NoRaise.DistinctRoots st.T)
    (hpar : NoRaise.ParentClosed st.T) {A C : Spec.Block V}
    (hA : st.blockOfImage A.toProof = A) (hC : st.blockOfImage C.toProof = C)
    (test' : Spec.Block V → Bool) (test : Block V → Bool)
    (htest : ∀ B : Spec.Block V, st.blockOfImage B.toProof = B → test' B = test B.toProof) :
    (Spec.Protocol.deepest_clear A C test').map Spec.Block.toProof =
      DecoupledConsensusModel.Protocol.deepest_clear (some A.toProof) C.toProof test := by
  have e : Spec.Protocol.deepest_clear A C test' =
      Spec.Protocol.deepest_clear A C (fun B => test B.toProof) := by
    unfold Spec.Protocol.deepest_clear
    congr 1
    apply Finset.filter_congr
    intro B hB
    rw [htest B (blockOfImage_of_mem_chain st hT hpar hC (List.mem_toFinset.mp hB))]
  rw [e]
  have h := Spec.Protocol.deepest_clear_blockOfImage_image st hT.injOn_toProof hpar
    A.toProof C.toProof test
  rw [hA, hC] at h
  exact h

omit [Fintype V] [Inhabited V] in
/-- `deepest_clear_of_fixed` at the blocks standing for the record's blocks `a` and `y`. -/
theorem deepest_clear_blockOfImage_test (st : Spec.Store V)
    (hT : NoRaise.DistinctRoots st.T) (hpar : NoRaise.ParentClosed st.T)
    (a y : Block V) (test' : Spec.Block V → Bool) (test : Block V → Bool)
    (htest : ∀ B : Spec.Block V, st.blockOfImage B.toProof = B → test' B = test B.toProof) :
    (Spec.Protocol.deepest_clear (st.blockOfImage a) (st.blockOfImage y) test').map
        Spec.Block.toProof =
      DecoupledConsensusModel.Protocol.deepest_clear (some a) y test := by
  have h := deepest_clear_of_fixed st hT hpar (A := st.blockOfImage a) (C := st.blockOfImage y)
    (by rw [Spec.Store.toProof_blockOfImage])
    (by rw [Spec.Store.toProof_blockOfImage]) test' test htest
  rw [Spec.Store.toProof_blockOfImage, Spec.Store.toProof_blockOfImage] at h
  exact h

omit [Fintype V] [Inhabited V] in
/-- The member `deepest_clear` at the confirmed block of a store of the instance is
    `DecoupledConsensusModel.Protocol.deepest_clear` at the image of the store's confirmed block. -/
theorem member_deepest_clear_eq (st : OkStore V) (a : Option (Block V)) (test : Block V → Bool) :
    Member.deepest_clear a (Member.gs_live_confirmed st.val) test =
      DecoupledConsensusModel.Protocol.deepest_clear a st.val.live_confirmed.toProof test := by
  rw [Member.gs_live_confirmed, toProof_gs_live_confirmed]
  unfold Member.deepest_clear
  rw [Spec.Protocol.deepest_clear_toSpec]

omit [Fintype V] [Inhabited V] in
/-- The confirmed block of the contract store stands for its image. -/
theorem contractStore_live_confirmed_fixed (st : Spec.Store V)
    (c : Spec.SavedGrades V) (r : Round) :
    st.blockOfImage (contractStore st c r).live_confirmed.toProof =
      (contractStore st c r).live_confirmed := by
  show st.blockOfImage (st.blockOfImage st.live_confirmed.toProof).toProof =
    st.blockOfImage st.live_confirmed.toProof
  rw [Spec.Store.toProof_blockOfImage]

omit [Inhabited V] in
/-- The spec's anchor on the contract store stands for its image. -/
theorem contractStore_anchor_fixed (st : OkStore V) (c : Spec.SavedGrades V) (r : Round)
    {g1 : Spec.GradeResult V} {A : Spec.Block V}
    (hA : Spec.Protocol.anchor (contractStore st.val c r) g1 = .ok A) :
    st.val.blockOfImage A.toProof = A := by
  rcases anchor_cases hA with e | hm
  · have e' : A = st.val.blockOfImage (Spec.Protocol.get_fg_root st.val).toProof :=
      e.trans (Spec.Store.get_fg_root_ofImage st.val)
    rw [e', Spec.Store.toProof_blockOfImage]
  · exact Spec.Store.blockOfImage_toProof_of_injOn st.val st.property.2.1.injOn_toProof
      (GradesImages.filtered_subset (contractStore st.val c r) hm)

omit [Inhabited V] in
/-- On a block standing for its image, the spec's grade-0 test of the contract store's round grades
    is the member `clear` at the image. -/
theorem contractStore_clear_fixed (st : OkStore V) (c : Spec.SavedGrades V) (r : Round)
    {B : Spec.Block V} (hB : st.val.blockOfImage B.toProof = B)
    {G0 : Option (Spec.Block V)}
    (hG0 : (Spec.Protocol.round_grades (contractStore st.val c r) r).g0 = .computed G0) :
    Spec.Protocol.G0_compatible G0 B =
      Member.clear (Spec.Protocol.round_grades (contractStore st.val c r) r) B.toProof := by
  obtain ⟨-, hT, hpar, hF⟩ := st.property
  have hinj := hT.injOn_toProof
  have hrf := GradesImages.round_grades_ofImage_eq_fillRound_readFrame st.property c r
  have hfix := (GradesImages.gradeResultOfImage_readFrame st.val hinj hpar hF c r).1
  rw [hrf]
  rw [hrf] at hG0
  generalize (Member.readFrame c st.val r) = R at hG0 hfix ⊢
  rcases R with ⟨g0, g1, g2⟩
  rcases g0 with _ | _ | Z
  · simp only [fillRound, fillResult, Spec.GradeResult.computed.injEq] at hG0
    subst hG0
    simp [Spec.Protocol.G0_compatible, Member.clear, DecoupledConsensusModel.Protocol.clear,
      fillRound, fillResult, Spec.RoundGrades.toProof, Spec.GradeResult.toProof]
  · simp only [fillRound, fillResult, Spec.GradeResult.computed.injEq] at hG0
    subst hG0
    simp [Spec.Protocol.G0_compatible, Member.clear, DecoupledConsensusModel.Protocol.clear,
      fillRound, fillResult, Spec.RoundGrades.toProof, Spec.GradeResult.toProof]
  · simp only [fillRound, fillResult, Spec.GradeResult.computed.injEq] at hG0
    subst hG0
    have hZ : st.val.blockOfImage Z.toProof = Z := by
      simpa [ForkChoiceGrades.gradeResultOfImage, Spec.GradeResult.toProof] using hfix
    have hc := Spec.Store.blockOfImage_compatible st.val hinj hpar B.toProof Z.toProof
    rw [hB, hZ] at hc
    simp only [Spec.Protocol.G0_compatible, Id.run, Member.clear,
      DecoupledConsensusModel.Protocol.clear, fillRound, fillResult,
      Spec.RoundGrades.toProof, Spec.GradeResult.toProof]
    simpa [pure, Option.value] using hc

omit [Fintype V] [Inhabited V] in
/-- The image of the spec's SG vote depends on its store and grade read only through the images of
    the clearing walk's answer, the grade-2 candidate, the fgroot and the anchor, and the raw
    grade-2 test. -/
theorem currentSGVote_toProof_congr {st₁ st₂ : Spec.Store V}
    {g₁ g₂ : Spec.Protocol.GradeRead V}
    (hD : (Spec.Protocol.deepest_clear g₁.anchor st₁.live_confirmed g₁.clear).map
        Spec.Block.toProof =
      (Spec.Protocol.deepest_clear g₂.anchor st₂.live_confirmed g₂.clear).map
        Spec.Block.toProof)
    (hQ : g₁.Q2.map Spec.Block.toProof = g₂.Q2.map Spec.Block.toProof)
    (hr : g₁.rawG2 = g₂.rawG2)
    (hroot : (Spec.Protocol.get_fg_root st₁).toProof =
      (Spec.Protocol.get_fg_root st₂).toProof)
    (hA : g₁.anchor.toProof = g₂.anchor.toProof) :
    (Spec.Protocol.currentSGVote st₁ g₁).toProof =
      (Spec.Protocol.currentSGVote st₂ g₂).toProof := by
  unfold Spec.Protocol.currentSGVote
  simp only [Id.run, pure, ne_eq]
  cases h₁ : Spec.Protocol.deepest_clear g₁.anchor st₁.live_confirmed g₁.clear <;>
    cases h₂ : Spec.Protocol.deepest_clear g₂.anchor st₂.live_confirmed g₂.clear <;>
    rw [h₁, h₂] at hD <;> simp only [Option.map_none, Option.map_some, reduceCtorEq,
      Option.some.injEq] at hD
  · cases q₁ : g₁.Q2 <;> cases q₂ : g₂.Q2 <;> rw [q₁, q₂] at hQ <;>
      simp only [Option.map_none, Option.map_some, reduceCtorEq, Option.some.injEq] at hQ
    · rw [hr]
      cases g₂.rawG2 <;> simp [hroot, hA]
    · simp [Option.value, hQ]
  · simp [Option.value, hD]

omit [Fintype V] [Inhabited V] in
/-- An answer `g` of the spec's `round_grade_read` carries the anchor of the round's grade-1 result,
    the grade-0 test of the round's grade-0 block, and the grade-2 candidate of the round's grades. -/
theorem round_grade_read_parts {st : Spec.Store V} {r : Spec.Round}
    {g : Spec.Protocol.GradeRead V}
    (h : Spec.Protocol.round_grade_read st r = .ok g) :
    ∃ G0, Spec.Protocol.anchor st (Spec.Protocol.round_grades st r).g1 =
        .ok g.anchor ∧
      (Spec.Protocol.round_grades st r).g0 = .computed G0 ∧
      g.clear = Spec.Protocol.G0_compatible G0 ∧
      Spec.Protocol.grade2Block st (Spec.Protocol.round_grades st r) =
        .ok g.Q2 := by
  unfold Spec.Protocol.round_grade_read at h
  obtain ⟨A, hA, h⟩ := NoRaise.DRE.of_bind_ok h
  obtain ⟨Q2, hQ2, h⟩ := NoRaise.DRE.of_bind_ok h
  obtain ⟨G0, hG0, h⟩ := NoRaise.DRE.of_bind_ok h
  obtain ⟨raw, -, h⟩ := NoRaise.DRE.of_bind_ok h
  cases Except.ok.inj h
  have hg : (Spec.Protocol.round_grades st r).g0 = .computed G0 := by
    revert hG0
    cases (Spec.Protocol.round_grades st r).g0 with
    | pending => intro hG0; cases hG0
    | computed G => intro hG0; cases hG0; rfl
  exact ⟨G0, hA, hg, rfl, hQ2⟩

omit [Inhabited V] in
/-- For an answer `g` of the spec's grade read of round `r` on the contract store and a candidate
    `Q`, the image of the spec's SG vote with candidate `Q` is the member `currentSGVote` at `g`'s
    image, with the record's grade-0 test, and candidate `Q`'s image. -/
theorem currentSGVote_contractStore (st : OkStore V) (c : Spec.SavedGrades V) (r : Round)
    {g : Spec.Protocol.GradeRead V}
    (hg : Spec.Protocol.round_grade_read (contractStore st.val c r) r = .ok g)
    (Q : Option (Spec.Block V)) :
    (Spec.Protocol.currentSGVote (contractStore st.val c r) { g with Q2 := Q }).toProof =
      Member.currentSGVote st.val
        { g.toProof with
          clear := Member.clear (Spec.Protocol.round_grades (contractStore st.val c r) r),
          Q2 := Q.map Spec.Block.toProof } := by
  obtain ⟨G0, hA, hG0, eC, -⟩ := round_grade_read_parts hg
  have hAfix : st.val.blockOfImage g.anchor.toProof = g.anchor := contractStore_anchor_fixed st c r hA
  have hcl : ∀ B : Spec.Block V, st.val.blockOfImage B.toProof = B →
      g.clear B = Member.clear (Spec.Protocol.round_grades (contractStore st.val c r) r)
        B.toProof := fun B hB => by
    rw [eC]
    exact contractStore_clear_fixed st c r hB hG0
  have hD : Spec.Protocol.deepest_clear g.anchor (contractStore st.val c r).live_confirmed
        g.clear =
      Spec.Protocol.deepest_clear (st.val.blockOfImage g.anchor.toProof)
        (Spec.Store.ofImage st.val).live_confirmed
        (fun B => Member.clear (Spec.Protocol.round_grades (contractStore st.val c r) r)
          B.toProof) := by
    rw [hAfix]
    unfold Spec.Protocol.deepest_clear
    congr 1
    apply Finset.filter_congr
    intro B hB
    rw [hcl B (blockOfImage_of_mem_chain st.val st.property.2.1 st.property.2.2.1
      (contractStore_live_confirmed_fixed st.val c r) (List.mem_toFinset.mp hB))]
  unfold Member.currentSGVote
  apply currentSGVote_toProof_congr
  · exact congrArg (Option.map Spec.Block.toProof) hD
  · show Q.map Spec.Block.toProof =
      ((Q.map Spec.Block.toProof).map st.val.blockOfImage).map Spec.Block.toProof
    rw [Option.map_map, Option.map_map]
    congr 1
    funext B
    simp [Spec.Store.toProof_blockOfImage]
  · show g.rawG2 = decide (g.rawG2 = true)
    cases g.rawG2 <;> rfl
  · rfl
  · show g.anchor.toProof = (st.val.blockOfImage g.anchor.toProof).toProof
    rw [Spec.Store.toProof_blockOfImage]

omit [Inhabited V] in
/-- The spec's grade-2 candidate on the contract store, when there is one, stands for its image. -/
theorem grade2_block_with_contractStore_fixed (st : OkStore V) (c : Spec.SavedGrades V)
    (r : Round) {A : Option (Spec.Block V)}
    (h : Spec.Protocol.grade2_block_with (contractStore st.val c r) r = .ok A) :
    ∀ q, A = some q → st.val.blockOfImage q.toProof = q := by
  intro q hq
  subst hq
  exact Spec.Store.blockOfImage_toProof_of_injOn st.val st.property.2.1.injOn_toProof
    (GradesImages.filtered_subset (contractStore st.val c r) (grade2Block_mem_filtered h))

omit [Inhabited V] in
/-- The spec's finality-gadget source on the contract store, for a candidate standing for its image,
    stands for its image. -/
theorem fg_source_contractStore_fixed (st : OkStore V) (c : Spec.SavedGrades V) (r : Round)
    {A : Option (Spec.Block V)} (hA : ∀ q, A = some q → st.val.blockOfImage q.toProof = q)
    {src : Option (Spec.Block V)}
    (h : Spec.Protocol.fg_source_with (contractStore st.val c r) r A = .ok src) :
    ∀ q, src = some q → st.val.blockOfImage q.toProof = q := by
  intro q hq
  subst hq
  cases A with
  | none =>
    rw [fg_source_with_none] at h
    cases h
  | some a =>
    rcases draft_fg_source_some_cases h with e | ⟨G0, B, -, hB, e⟩
    · cases e
      exact hA q rfl
    · cases e
      exact blockOfImage_of_mem_chain st.val st.property.2.1 st.property.2.2.1
        (contractStore_live_confirmed_fixed st.val c r) (deepest_clear_mem_chain hB)

/-- The fields of the spec's attestation input on the contract store, mapped, are read off the
    record's chain state at the members' finality-gadget source. -/
theorem attestation_input_fields_image (st : OkStore V) {contract : Spec.SavedGrades V}
    {E : Env V} {hc : Protocol.HealConfig} {v : V} {i : Spec.Protocol.AttestationInput V}
    (hi : Spec.Protocol.attestation_input (Spec.Config.toSpec E hc unreadHeightConfig)
      v (contractStore st.val contract
        ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.val.s)) = .ok i)
    {A2 : Option (Block V)} (hA2 : Returns (Member.grade2_block_with contract E hc st.val
      ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.val.s)) A2)
    {F : Option (Block V)} (hF : Returns (Member.fg_source_with contract E hc st.val
      ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.val.s) A2) F) :
    i.fields.map (fun f => (f.1, f.2.1.toProof, f.2.2)) =
      F.map (fun q => ((Member.fg_σ st.val q).toProof.h, (Member.fg_σ st.val q).toProof.T_h.root,
        (Member.fg_σ st.val q).toProof.nj)) := by
  obtain ⟨A_G2, src, hA, hsrc, hfields⟩ := attestation_input_fields hi
  obtain ⟨Q2, h1, rfl⟩ := grade2_block_with_shape hA2
  have e : Q2 = A_G2 := Except.ok.inj (h1.symm.trans hA)
  subst e
  have hQfix := grade2_block_with_contractStore_fixed st contract _ hA
  unfold Member.fg_source_with at hF
  obtain ⟨src', hsrc', rfl⟩ := except_map_eq_ok ((returns_successOutcomes _ _).1 hF)
  have eQ : (Q2.map Spec.Block.toProof).map st.val.blockOfImage = Q2 := by
    cases Q2 with
    | none => rfl
    | some q => simp [hQfix q rfl]
  rw [eQ] at hsrc'
  have es : src' = src := Except.ok.inj (hsrc'.symm.trans hsrc)
  subst es
  have hsfix := fg_source_contractStore_fixed st contract _ hQfix hsrc
  rw [hfields]
  cases src' with
  | none => rfl
  | some q =>
    have hq := hsfix q rfl
    simp only [Option.map_some, Option.some.injEq]
    unfold Member.fg_σ
    rw [hq]
    simp [Spec.Protocol.ChainState.toProof, Spec.Block.toProof_root]


omit [Inhabited V] in
/-- The spec's head on the contract store stands for its image. -/
theorem get_head_with_contractStore_fixed (st : OkStore V) (c : Spec.SavedGrades V)
    (r : Round) {C : Spec.Config} {votes support : Finset (Spec.GoldfishVote V)}
    {s : Slot} {H : Spec.Block V}
    (h : Spec.Protocol.get_head_with C (contractStore st.val c r) votes support s = .ok H) :
    st.val.blockOfImage H.toProof = H := by
  unfold Spec.Protocol.get_head_with Spec.Protocol.get_head_in_tree_with_layer at h
  obtain ⟨A, hA, h⟩ := NoRaise.DRE.of_bind_ok h
  rw [get_sg_root_with_eq_anchor] at hA
  unfold Spec.Protocol.goldfish_fork_choice Spec.Protocol.ghost at h
  obtain ⟨hm, -⟩ := ghost_walk_mem_ancestorEq _ _ _ h
  rcases hm with rfl | hm
  · exact contractStore_anchor_fixed st c r hA
  · exact Spec.Store.blockOfImage_toProof_of_injOn st.val st.property.2.1.injOn_toProof
      (GradesImages.filtered_subset (contractStore st.val c r) hm)

/-- The members' support votes of slot `s`, the votes the outcomes `res` of the member `resolved`
    keep, written in the spec's type, are the spec's support votes. -/
theorem support_filter_eq (st : OkStore V) (s : Slot) (res : GoldfishVote V → Bool)
    (hres : ∀ u, (Model.spec (V := V)).resolved (st.val.T.image Spec.Block.toProof) u ⇢ res u)
    {S : Finset (Spec.GoldfishVote V)}
    (hS : (st.val.pool s).filterM (fun u => Spec.Protocol.resolved st.val.T u) = .ok S) :
    (((st.val.pool s).map Spec.GoldfishVote.toProofEmb).filter (fun u => res u = true)).map
      ForkChoiceGrades.voteToSpecEmb = S := by
  have hS' := ForkChoiceImages.filterM_eq_filter_of_ok _
    (fun u => DecoupledConsensusModel.Protocol.resolved (st.val.T.image Spec.Block.toProof)
      u.toProof = true)
    (fun a b h => by rw [ForkChoiceImages.resolved_toProof_of_ok st.property.2.1 a h]) _ _ hS
  have hr : ∀ u, res u =
      DecoupledConsensusModel.Protocol.resolved (st.val.T.image Spec.Block.toProof) u := by
    intro u
    have h := hres u
    rw [ForkChoiceImages.spec_resolved_eq] at h
    exact (returns_pure _ _).1 h
  rw [hS', Finset.filter_map, Finset.map_map]
  ext u
  simp [hr, ForkChoiceGrades.voteToSpecEmb]

omit [Inhabited V] in
/-- An answer of the spec's `get_fg_vote_with` is made of the head of the store's votes and support
    votes, and the justified height, the justified root and the finalized height of the head's chain
    state. -/
theorem get_fg_vote_with_parts {C : Spec.Config} {st : Spec.Store V}
    {r : Spec.Round} {A_G2 : Option (Spec.Block V)}
    {out : Option (Spec.Height × Spec.BlockId × Bool) × Spec.Height ×
      Spec.BlockId × Spec.Height}
    (h : Spec.Protocol.get_fg_vote_with C st r A_G2 = .ok out) :
    ∃ S H, (st.pool st.s).filterM (fun u => Spec.Protocol.resolved st.T u) = .ok S ∧
      Spec.Protocol.get_head_with C st (st.pool st.s) S st.s = .ok H ∧
      out.2 = ((st.σ H).h_j, (st.σ H).J.root, (st.σ H).h_F) := by
  unfold Spec.Protocol.get_fg_vote_with at h
  obtain ⟨S, hS, h⟩ := NoRaise.DRE.of_bind_ok h
  obtain ⟨H, hH, h⟩ := NoRaise.DRE.of_bind_ok h
  obtain ⟨src, -, h⟩ := NoRaise.DRE.of_bind_ok h
  refine ⟨S, H, hS, hH, ?_⟩
  cases src with
  | none =>
    simp [pure, Except.pure] at h
    rw [← h]
    rfl
  | some q =>
    simp [pure, Except.pure, Option.value] at h
    rw [← h]
    rfl

omit [Fintype V] [Inhabited V] in
/-- The contract store has the store's slot, tree, chain states, Goldfish votes and vote stamps. -/
theorem contractStore_fields (st : Spec.Store V) (c : Spec.SavedGrades V) (r : Round) :
    (contractStore st c r).s = st.s ∧ (contractStore st c r).T = st.T ∧
      (contractStore st c r).σ = st.σ ∧ (contractStore st c r).gf_votes = st.gf_votes ∧
      (contractStore st c r).timestamp_vote = st.timestamp_vote :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

omit [Fintype V] [Inhabited V] in
/-- The contract store's pool of slot `s` is the store's. -/
theorem contractStore_pool (st : Spec.Store V) (c : Spec.SavedGrades V) (r : Round)
    (s : Slot) : (contractStore st c r).pool s = st.pool s := rfl

omit [Inhabited V] in
/-- On a store of the instance whose justified block's image is the image of a tree block, the
    spec's head on the contract store is a tree block. -/
theorem get_head_with_contractStore_mem (st : OkStore V) (c : Spec.SavedGrades V)
    (r : Round) (hJ : st.val.J.toProof ∈ st.val.T.image Spec.Block.toProof)
    {C : Spec.Config} {votes support : Finset (Spec.GoldfishVote V)}
    {s : Slot} {H : Spec.Block V}
    (h : Spec.Protocol.get_head_with C (contractStore st.val c r) votes support s = .ok H) :
    H ∈ st.val.T := by
  have hinj := st.property.2.1.injOn_toProof
  unfold Spec.Protocol.get_head_with Spec.Protocol.get_head_in_tree_with_layer at h
  obtain ⟨A, hA, h⟩ := NoRaise.DRE.of_bind_ok h
  rw [get_sg_root_with_eq_anchor] at hA
  unfold Spec.Protocol.goldfish_fork_choice Spec.Protocol.ghost at h
  obtain ⟨hm, -⟩ := ghost_walk_mem_ancestorEq _ _ _ h
  have hAT : A ∈ st.val.T := by
    rcases anchor_cases hA with e | hm'
    · have e' : A = st.val.blockOfImage (Spec.Protocol.get_fg_root st.val).toProof :=
        e.trans (Spec.Store.get_fg_root_ofImage st.val)
      rw [e']
      unfold Spec.Protocol.get_fg_root
      simp only [Id.run, pure]
      split
      · obtain ⟨Y, hY, eY⟩ := Finset.mem_image.mp hJ
        rw [← eY, Spec.Store.blockOfImage_toProof_of_injOn st.val hinj hY]
        exact hY
      · rw [Spec.Store.blockOfImage_toProof_of_injOn st.val hinj st.property.2.2.2]
        exact st.property.2.2.2
    · exact GradesImages.filtered_subset (contractStore st.val c r) hm'
  rcases hm with rfl | hm
  · exact hAT
  · exact GradesImages.filtered_subset (contractStore st.val c r) hm

/-! ## The head is the fork choice from the root -/

/-- At a store of the instance, the tree is the set of the blocks standing for the images of its
    blocks. -/
theorem T_eq_map_blockOfImage (st : OkStore V) :
    st.val.T = (st.val.T.image Spec.Block.toProof).map st.val.blockOfImageEmb :=
  (ForkChoiceImages.image_map_blockOfImage_of_subset st (subset_refl _)).symm

/-- At a store of the instance, an answer of the spec's Goldfish fork choice from the block standing
    for `A` through the blocks standing for `tree` has as image
    `DecoupledConsensusModel.Protocol.goldfish_fork_choice` from `A` through `tree`, on the image of
    the store's tree and the chain states read at the blocks standing for the record's blocks. -/
theorem goldfish_fork_choice_store (st : OkStore V) (E : Env V) (A : Block V)
    (tree : Finset (Block V)) (votes support : Finset (GoldfishVote V)) (k : Slot)
    {Y : Spec.Block V}
    (h : Spec.Protocol.goldfish_fork_choice st.val.σ st.val.h_max st.val.T st.val.s
      (st.val.blockOfImage A) (tree.map st.val.blockOfImageEmb) (votes.map ForkChoiceGrades.voteToSpecEmb)
      (support.map ForkChoiceGrades.voteToSpecEmb) k = .ok Y) :
    Y.toProof = Protocol.goldfish_fork_choice E
      (fun C => (st.val.σ (st.val.blockOfImage C)).toProof) st.val.h_max
      (st.val.T.image Spec.Block.toProof) st.val.s A tree votes support k := by
  obtain ⟨-, hT, hpar, -⟩ := st.property
  have hinj := hT.injOn_toProof
  rw [T_eq_map_blockOfImage st] at h
  have e := ForkChoiceImages.goldfish_fork_choice_at st.val.blockOfImageEmb
    (Spec.Store.toProof_blockOfImage st.val)
    (Spec.Store.blockOfImage_ancestorEq st.val hinj hpar)
    (fun B => (Spec.Store.blockOfImage_parent st.val hinj hpar B).symm)
    E st.val.σ st.val.h_max _ st.val.s A tree votes support k h
  rw [e]
  exact Spec.Store.toProof_blockOfImage st.val _

omit [Inhabited V] in
/-- When the spec's SG root answers `A`, the spec's head in a tree is the spec's Goldfish fork
    choice from `A`. -/
theorem draft_layer_of_anchor {C : Spec.Config} {st : Spec.Store V}
    {tree : Finset (Spec.Block V)} {votes sv : Finset (Spec.GoldfishVote V)}
    {k : Slot} {A : Spec.Block V}
    (hA : Spec.Protocol.get_sg_root_with C st = .ok A) :
    Spec.Protocol.get_head_in_tree_with_layer C st tree votes sv k =
      Spec.Protocol.goldfish_fork_choice st.σ st.h_max st.T st.s A tree votes sv k := by
  unfold Spec.Protocol.get_head_in_tree_with_layer
  rw [hA]
  rfl

/-- At a store of the instance, when the spec's `anchor` of the contract store's round answers `A`,
    the member `get_head_in_tree_with_layer` answers
    `DecoupledConsensusModel.Protocol.goldfish_fork_choice` from `A`'s image through `tree`, on the
    image of the store's tree and the chain states read at the blocks standing for the record's
    blocks. -/
theorem member_get_head_in_tree_with_layer_eq_of_anchor (st : OkStore V)
    (c : Spec.SavedGrades V) (E : Env V) (hc : Protocol.HealConfig)
    (tree : Finset (Block V)) (votes support : Finset (GoldfishVote V)) (k : Slot)
    {A : Spec.Block V}
    (hA : Spec.Protocol.anchor
      (contractStore st.val c ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.val.s))
      (Spec.Protocol.round_grades
        (contractStore st.val c ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.val.s))
        ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.val.s)).g1 = .ok A) :
    Member.get_head_in_tree_with_layer c E hc st.val tree votes support k =
      pure (Protocol.goldfish_fork_choice E
        (fun C => (st.val.σ (st.val.blockOfImage C)).toProof) st.val.h_max
        (st.val.T.image Spec.Block.toProof) st.val.s A.toProof tree votes support k) := by
  have hfix := contractStore_anchor_fixed st c _ hA
  have hsg : Spec.Protocol.get_sg_root_with (Spec.Config.toSpec E hc unreadHeightConfig)
      (contractStore st.val c ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.val.s)) =
        .ok A := by
    rw [get_sg_root_with_eq_anchor]
    exact hA
  show successOutcomes (Except.map Spec.Block.toProof
    (Spec.Protocol.get_head_in_tree_with_layer (Spec.Config.toSpec E hc unreadHeightConfig)
      (contractStore st.val c ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.val.s))
      (tree.map st.val.blockOfImageEmb) (votes.map ForkChoiceGrades.voteToSpecEmb) (support.map ForkChoiceGrades.voteToSpecEmb) k)) = _
  rw [draft_layer_of_anchor hsg]
  obtain ⟨Y, hY⟩ := NoRaise.goldfish_fork_choice_ok st.property.2.1 st.val.σ st.val.h_max st.val.s A
    (tree.map st.val.blockOfImageEmb) (votes.map ForkChoiceGrades.voteToSpecEmb) (support.map ForkChoiceGrades.voteToSpecEmb) k
  show successOutcomes (Except.map Spec.Block.toProof
    (Spec.Protocol.goldfish_fork_choice st.val.σ st.val.h_max st.val.T st.val.s A
      (tree.map st.val.blockOfImageEmb) (votes.map ForkChoiceGrades.voteToSpecEmb) (support.map ForkChoiceGrades.voteToSpecEmb) k)) = _
  rw [hY]
  rw [← hfix] at hY
  have e := goldfish_fork_choice_store st E A.toProof tree votes support k hY
  show successOutcomes (.ok Y.toProof : DC.DRE (Block V)) = _
  rw [ForkChoiceImages.successOutcomes_ok, e]

/-- `member_get_head_in_tree_with_layer_eq_of_anchor`, from an outcome `R` of the member
    `get_sg_root_with` at the store's round. -/
theorem member_get_head_in_tree_with_layer_eq (st : OkStore V)
    (c : Spec.SavedGrades V) (E : Env V) (hc : Protocol.HealConfig)
    (tree : Finset (Block V)) (votes support : Finset (GoldfishVote V)) (k : Slot) {R : Block V}
    (hR : Returns (Member.get_sg_root_with c E hc st.val
      ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.val.s)) R) :
    Member.get_head_in_tree_with_layer c E hc st.val tree votes support k =
      pure (Protocol.goldfish_fork_choice E
        (fun C => (st.val.σ (st.val.blockOfImage C)).toProof) st.val.h_max
        (st.val.T.image Spec.Block.toProof) st.val.s R tree votes support k) := by
  obtain ⟨A, hA, rfl⟩ := get_sg_root_with_shape hR
  exact member_get_head_in_tree_with_layer_eq_of_anchor st c E hc tree votes support k hA

/-- At a store of the instance, the member `get_head_with` is the member
    `get_head_in_tree_with_layer` in the member `get_filtered_block_tree`. -/
theorem member_get_head_with_eq_layer (st : OkStore V) (c : Spec.SavedGrades V)
    (E : Env V) (hc : Protocol.HealConfig) (votes support : Finset (GoldfishVote V)) (k : Slot) :
    Member.get_head_with c E hc st.val votes support k =
      Member.get_head_in_tree_with_layer c E hc st.val (Member.get_filtered_block_tree st.val)
        votes support k := by
  have hQ : Spec.Protocol.get_filtered_block_tree (Spec.Store.ofImage st.val) ⊆
      st.val.T := GradesImages.filtered_subset _
  have e1 : (Member.get_filtered_block_tree st.val).map st.val.blockOfImageEmb =
      Spec.Protocol.get_filtered_block_tree
        (contractStore st.val c ((Spec.Config.toSpec E hc unreadHeightConfig).round_of st.val.s)) :=
    (ForkChoiceImages.image_map_blockOfImage_of_subset st hQ).trans
      (ForkChoiceImages.get_filtered_block_tree_congr rfl rfl rfl rfl rfl rfl)
  unfold Member.get_head_in_tree_with_layer
  rw [e1]
  rfl

end SpecRecord.ContractImages
