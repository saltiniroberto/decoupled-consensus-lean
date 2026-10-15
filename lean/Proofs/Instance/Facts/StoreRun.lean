import Proofs.Instance.Facts.Node2

/-!
# The store run facts at `Model.spec`

The five fields of `StoreRunFacts` proved at `Model.spec`, with the lemmas saying what each
write of the spec's store adds to the Goldfish vote lists and the attestation lists, and the bundle
`Model.spec_runFacts_store`.
-/

namespace SpecRecord.StoreRunFacts

open DecoupledConsensusModel
open DecoupledConsensusModel.Sts
open DecoupledConsensusModel.Sts.Record
open DecoupledConsensusModel.Execution
open scoped DC

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-! ## What each write of the store adds -/

omit [Inhabited V] in
/-- A vote in a slot's list after `on_goldfish_vote_checked P st u` was in that list before, or is
    `u`. -/
theorem gf_vote_new (P : Spec.Provisional V) (st : Spec.Store V)
    (u : Spec.GoldfishVote V) (k : Slot) (x : Spec.GoldfishVote V)
    (hx : x ∈ (Spec.Protocol.on_goldfish_vote_checked P st u).gf_votes k) :
    x ∈ st.gf_votes k ∨ x = u := by
  unfold Spec.Protocol.on_goldfish_vote_checked Spec.Protocol.on_goldfish_vote
    at hx
  simp only [Id.run, pure] at hx
  split_ifs at hx
  all_goals first
    | exact Or.inl hx
    | (simp only [Function.update_apply] at hx
       split_ifs at hx with hk
       · subst hk
         rcases List.mem_append.mp hx with h | h
         · exact Or.inl h
         · exact Or.inr (List.mem_singleton.mp h)
       · exact Or.inl hx)

omit [Inhabited V] in
/-- A vote in a slot's list after admitting the Goldfish votes of `L` one by one was in that list
    before, or is in `L`. -/
theorem gf_fold_new (P : Spec.Provisional V) (L : List (Spec.GoldfishVote V))
    (st : Spec.Store V) (k : Slot) (x : Spec.GoldfishVote V)
    (hx : x ∈ (L.foldl (Spec.Protocol.on_goldfish_vote_checked P) st).gf_votes k) :
    x ∈ st.gf_votes k ∨ x ∈ L := by
  induction L generalizing st with
  | nil => exact Or.inl hx
  | cons u L ih =>
    rcases ih _ hx with h | h
    · rcases gf_vote_new P st u k x h with h' | rfl
      · exact Or.inl h'
      · exact Or.inr List.mem_cons_self
    · exact Or.inr (List.mem_cons_of_mem _ h)

omit [Inhabited V] in
/-- A vote in a slot's list after `on_block C P st B` was in that list before, or `B` includes it. -/
theorem gf_block_new (C : Spec.Config) (P : Spec.Provisional V)
    (st : Spec.Store V) (B : Spec.Block V) (k : Slot)
    (x : Spec.GoldfishVote V)
    (hx : x ∈ (Spec.Protocol.on_block C P st B).gf_votes k) :
    x ∈ st.gf_votes k ∨ x ∈ B.gf_votes := by
  rcases StoreSteps.on_block_shape C P st B with e | ⟨-, σ', e⟩
  · rw [e] at hx
    exact Or.inl hx
  · rw [e] at hx
    obtain ⟨x1, y1, e1⟩ := StoreSteps.admit_attestations_writes C B.attestations
      (Spec.Protocol.update_finality (B.gf_votes.foldl
        (Spec.Protocol.on_goldfish_vote_checked P)
        { st with σ := Function.update st.σ B σ', T := st.T ∪ {B},
                  timestamp_block := Function.update st.timestamp_block B (some (st.t : Stamp)) }) B)
    rw [e1] at hx
    obtain ⟨a, b, c, d, e2⟩ := StoreSteps.update_finality_writes (B.gf_votes.foldl
        (Spec.Protocol.on_goldfish_vote_checked P)
        { st with σ := Function.update st.σ B σ', T := st.T ∪ {B},
                  timestamp_block := Function.update st.timestamp_block B (some (st.t : Stamp)) }) B
    rw [e2] at hx
    exact gf_fold_new P B.gf_votes
      { st with σ := Function.update st.σ B σ', T := st.T ∪ {B},
                timestamp_block := Function.update st.timestamp_block B (some (st.t : Stamp)) } k x hx

omit [Inhabited V] in
/-- `admit_attestation` keeps the Goldfish vote lists. -/
theorem gf_attest_eq (C : Spec.Config) (st : Spec.Store V)
    (row : Spec.Attestation V) :
    (Spec.Protocol.admit_attestation C st row).gf_votes = st.gf_votes := by
  obtain ⟨x, y, e⟩ := StoreSteps.admit_attestation_writes C st row
  rw [e]

omit [Inhabited V] in
/-- An attestation in a round's list after `admit_attestation C st a` was in that list before, or is
    `a`. -/
theorem att_new (C : Spec.Config) (st : Spec.Store V)
    (a : Spec.Attestation V) (r : Round) (x : Spec.Attestation V)
    (hx : x ∈ (Spec.Protocol.admit_attestation C st a).attestations r) :
    x ∈ st.attestations r ∨ x = a := by
  rcases StoreSteps.admit_attestation_cases C st a with e | ⟨-, e⟩
  · rw [e] at hx
    exact Or.inl hx
  · rw [e] at hx
    simp only [Function.update_apply] at hx
    split_ifs at hx with hk
    · subst hk
      rcases List.mem_append.mp hx with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_singleton.mp h)
    · exact Or.inl hx

omit [Inhabited V] in
/-- An attestation in a round's list after `admit_attestations C st L` was in that list before, or
    is in `L`. -/
theorem att_fold_new (C : Spec.Config) (L : List (Spec.Attestation V))
    (st : Spec.Store V) (r : Round) (x : Spec.Attestation V)
    (hx : x ∈ (Spec.Protocol.admit_attestations C st L).attestations r) :
    x ∈ st.attestations r ∨ x ∈ L := by
  rw [StoreSteps.admit_attestations_foldl] at hx
  induction L generalizing st with
  | nil => exact Or.inl hx
  | cons a L ih =>
    rcases ih _ hx with h | h
    · rcases att_new C st a r x h with h' | rfl
      · exact Or.inl h'
      · exact Or.inr List.mem_cons_self
    · exact Or.inr (List.mem_cons_of_mem _ h)

omit [Inhabited V] in
/-- An attestation in a round's list after `on_block C P st B` was in that list before, or `B`
    includes it. -/
theorem att_block_new (C : Spec.Config) (P : Spec.Provisional V)
    (st : Spec.Store V) (B : Spec.Block V) (r : Round)
    (x : Spec.Attestation V)
    (hx : x ∈ (Spec.Protocol.on_block C P st B).attestations r) :
    x ∈ st.attestations r ∨ x ∈ B.attestations := by
  rcases StoreSteps.on_block_shape C P st B with e | ⟨-, σ', e⟩
  · rw [e] at hx
    exact Or.inl hx
  · rw [e] at hx
    rcases att_fold_new C B.attestations _ r x hx with h | h
    · obtain ⟨a, b, c, d, e2⟩ := StoreSteps.update_finality_writes (B.gf_votes.foldl
          (Spec.Protocol.on_goldfish_vote_checked P)
          { st with σ := Function.update st.σ B σ', T := st.T ∪ {B},
                    timestamp_block := Function.update st.timestamp_block B (some (st.t : Stamp)) }) B
      rw [e2] at h
      obtain ⟨x1, y1, e1⟩ := StoreSteps.foldl_checked_writes P B.gf_votes
          { st with σ := Function.update st.σ B σ', T := st.T ∪ {B},
                    timestamp_block := Function.update st.timestamp_block B (some (st.t : Stamp)) }
      rw [e1] at h
      exact Or.inl h
    · exact Or.inr h

omit [Inhabited V] in
/-- `on_goldfish_vote_checked` keeps the attestation lists. -/
theorem att_vote_eq (P : Spec.Provisional V) (st : Spec.Store V)
    (u : Spec.GoldfishVote V) :
    (Spec.Protocol.on_goldfish_vote_checked P st u).attestations = st.attestations := by
  obtain ⟨x, y, e⟩ := StoreSteps.on_goldfish_vote_checked_writes P st u
  rw [e]

/-! ## The tick -/

omit [Inhabited V] in
/-- Every Goldfish vote and attestation in the node state a successful tick returns was in the node
    state before, or was sent by the tick, alone or included in a block it sent. -/
theorem tick_sources {S : Setup V} {n n' : Spec.NodeState V} {t : Time}
    {sent : List (Spec.NamedObject V)}
    (h : (Spec.tick (Setup.toSpec S).C (Setup.toSpec S).P (Setup.toSpec S).X n t).run [] =
      .ok (n', sent)) :
    (∀ (k : Slot) (x : Spec.GoldfishVote V), x ∈ n'.st.gf_votes k →
      x ∈ n.st.gf_votes k ∨ Spec.NamedObject.gfVote x ∈ sent ∨
        ∃ B : Spec.Block V, Spec.NamedObject.block B ∈ sent ∧ x ∈ B.gf_votes) ∧
    (∀ (r : Round) (x : Spec.Attestation V), x ∈ n'.st.attestations r →
      x ∈ n.st.attestations r ∨ Spec.NamedObject.attest x ∈ sent ∨
        ∃ B : Spec.Block V, Spec.NamedObject.block B ∈ sent ∧
          x ∈ B.attestations) := by
  obtain ⟨st0, st2, st3, st4, st5, sh5, l1, l2, h0, h2, h3, h4, h5, rfl⟩ := NodeFacts.tick_run_ok h
  have e0 := (NodeFacts.update_grades_ok h0).1
  have er : (Spec.record_awake n t).st = n.st := by rw [NodeFacts.record_awake_eq]
  have g0 : st0.gf_votes = n.st.gf_votes := by rw [e0, er]
  have a0 : st0.attestations = n.st.attestations := by rw [e0, er]
  have e4 : st4.gf_votes = st3.gf_votes ∧ st4.attestations = st3.attestations := by
    rcases h4 with ⟨s', hs'⟩ | rfl
    · have e := NodeFacts.update_confirmation_ok hs'
      constructor <;> rw [e]
    · exact ⟨rfl, rfl⟩
  have hl2 : ∀ o ∈ l2, o ∈ sent := by
    rcases h5 with ⟨row, -, -, rfl⟩ | ⟨-, -, rfl⟩
    · exact fun o ho => List.mem_append_left _ ho
    · exact fun o ho => ho
  have hl1 : ∀ o ∈ l1, o ∈ l2 := by
    rcases h3 with ⟨u, -, rfl⟩ | ⟨-, rfl⟩
    · exact fun o ho => List.mem_append_left _ ho
    · exact fun o ho => ho
  refine ⟨fun k x hx => ?_, fun r x hx => ?_⟩
  · have hx4 : x ∈ st4.gf_votes k := by
      rcases h5 with ⟨row, -, rfl, -⟩ | ⟨rfl, -, -⟩
      · have hx' : x ∈ (Spec.Protocol.admit_attestation _ st4 row).gf_votes k := hx
        rwa [gf_attest_eq] at hx'
      · exact hx
    rw [e4.1] at hx4
    have hx2 : x ∈ st2.gf_votes k ∨ Spec.NamedObject.gfVote x ∈ sent := by
      rcases h3 with ⟨u, rfl, hl⟩ | ⟨rfl, -⟩
      · rcases gf_vote_new _ st2 u k x hx4 with h' | rfl
        · exact Or.inl h'
        · exact Or.inr (hl2 _ (by rw [hl]; exact List.mem_append_right _ List.mem_cons_self))
      · exact Or.inl hx4
    rcases hx2 with hx2 | hs
    · rcases h2 with ⟨B, rfl, hl⟩ | ⟨rfl, -⟩
      · rcases gf_block_new _ _ _ B k x hx2 with h' | h'
        · rw [← g0]; exact Or.inl h'
        · exact Or.inr (Or.inr ⟨B, hl2 _ (hl1 _ (by rw [hl]; exact List.mem_cons_self)), h'⟩)
      · rw [← g0]; exact Or.inl hx2
    · exact Or.inr (Or.inl hs)
  · have hx4 : x ∈ st4.attestations r ∨ Spec.NamedObject.attest x ∈ sent := by
      rcases h5 with ⟨row, -, rfl, hs⟩ | ⟨rfl, -, -⟩
      · rcases att_new _ st4 row r x hx with h' | rfl
        · exact Or.inl h'
        · exact Or.inr (by rw [hs]; exact List.mem_append_right _ List.mem_cons_self)
      · exact Or.inl hx
    rcases hx4 with hx4 | hs
    · rw [e4.2] at hx4
      have hx3 : x ∈ st2.attestations r := by
        rcases h3 with ⟨u, rfl, -⟩ | ⟨rfl, -⟩
        · rwa [att_vote_eq] at hx4
        · exact hx4
      rcases h2 with ⟨B, rfl, hl⟩ | ⟨rfl, -⟩
      · rcases att_block_new _ _ _ B r x hx3 with h' | h'
        · rw [← a0]; exact Or.inl h'
        · exact Or.inr (Or.inr ⟨B, hl2 _ (hl1 _ (by rw [hl]; exact List.mem_cons_self)), h'⟩)
      · rw [← a0]; exact Or.inl hx3
    · exact Or.inr (Or.inl hs)

/-! ## The record's readers -/

omit [Fintype V] [Inhabited V] in
/-- A Goldfish vote of a block `B` maps into the votes `B.toProofNamed` includes. -/
theorem gf_toProofNamed {B : Spec.Block V} {x : Spec.GoldfishVote V}
    (h : x ∈ B.gf_votes) : x.toProof ∈ B.toProofNamed.gf_votes := by
  rw [← NodeFacts.toSpecNamed_gf_votes_map B.toProofNamed,
    Spec.Block.toSpecNamed_toProofNamed]
  exact List.mem_map_of_mem h

/-- An attestation that the spec form of a named block `B` includes maps to the erasure of an
    attestation `B` includes. -/
theorem att_of_toSpecNamed {B : NamedBlock V} {x : Spec.Attestation V}
    (h : x ∈ (Spec.Block.toSpecNamed B).attestations) :
    ∃ row ∈ B.attestations, x.toProof = row.erase := by
  rw [NodeFacts.toSpecNamed_attestations] at h
  obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp h
  refine ⟨row, hrow, ?_⟩
  rw [HandlersFacts.toProof_toSpecNamed_attestation, Spec.Attestation.toProof_toSpec]

/-- The field `tick_gf_votes_mem` of `StoreRunFacts` at `Model.spec`: for every outcome `out`
    of `v`'s tick at `t` from `n`, a vote `u` in the slot-`k` list of `out.1`'s core store is in the
    slot-`k` list of `n`'s core store, or `out` sends `u`, or `out` sends a block that includes `u`. -/
theorem spec_tick_gf_votes_mem : ∀ (S : Setup V) (v : V) (n : (Model.spec (V := V)).N)
    (t : Time) (k : Slot) {u : GoldfishVote V}
    (out : (Model.spec (V := V)).N × List (NamedObject V)),
    (Model.spec (V := V)).tick S v n t ⇢ out →
    u ∈ out.1.st.core.gf_votes k →
      u ∈ n.st.core.gf_votes k ∨ NamedObject.gfVote u ∈ out.2 ∨
        ∃ B : NamedBlock V, NamedObject.block B ∈ out.2 ∧ u ∈ B.gf_votes := by
  intro S v n t k u out hout hu
  obtain ⟨n', sent, hrun, heq⟩ := (NodeFacts.tick_returns_iff S v n.val t (out.1.val, out.2)).1 hout
  simp only [Prod.mk.injEq] at heq
  obtain ⟨e1, e2⟩ := heq
  change u ∈ (out.1.val.st.gf_votes k).map Spec.GoldfishVote.toProof at hu
  rw [e1] at hu
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hu
  rw [e2]
  rcases (tick_sources hrun).1 k x hx with h | h | ⟨B, hB, hxB⟩
  · exact Or.inl (List.mem_map_of_mem h)
  · exact Or.inr (Or.inl (List.mem_map_of_mem (f := Spec.NamedObject.toProof) h))
  · exact Or.inr (Or.inr ⟨B.toProofNamed,
      List.mem_map_of_mem (f := Spec.NamedObject.toProof) hB, gf_toProofNamed hxB⟩)

/-- The field `tick_sg_pool_mem` of `StoreRunFacts` at `Model.spec`: for every outcome `out` of
    `v`'s tick at `t` from `n`, a round-`r` attestation in the attestation set of `out`'s store is
    in that of `n`'s store, or an object `out` sends carries it. -/
theorem spec_tick_sg_pool_mem : ∀ (S : Setup V) (v : V) (n : (Model.spec (V := V)).N)
    (t : Time) (r : Round) {b : CombinedAttestation V}
    (out : (Model.spec (V := V)).N × List (NamedObject V)),
    (Model.spec (V := V)).tick S v n t ⇢ out →
    b ∈ out.1.st.core.sg_pool r →
      b ∈ n.st.core.sg_pool r ∨
        ∃ o ∈ out.2, DecoupledConsensusModel.Proofs.Optimistic.CarriesRow o b := by
  intro S v n t r b out hout hb
  obtain ⟨n', sent, hrun, heq⟩ := (NodeFacts.tick_returns_iff S v n.val t (out.1.val, out.2)).1 hout
  simp only [Prod.mk.injEq] at heq
  obtain ⟨e1, e2⟩ := heq
  change b ∈ (out.1.val.st.sg_pool r).image Spec.Attestation.toProof at hb
  rw [e1] at hb
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hb
  rw [StoreSteps.mem_sg_pool_iff] at hx
  rw [e2]
  rcases (tick_sources hrun).2 r x hx with h | h | ⟨B, hB, hxB⟩
  · left
    change x.toProof ∈ (n.val.st.sg_pool r).image Spec.Attestation.toProof
    exact Finset.mem_image_of_mem _ ((StoreSteps.mem_sg_pool_iff _ _ _).2 h)
  · refine Or.inr ⟨_, List.mem_map_of_mem (f := Spec.NamedObject.toProof) h, ?_⟩
    show x.toProof = x.toProofNamed.erase
    rw [Spec.Attestation.toProofNamed_erase]
  · refine Or.inr ⟨_, List.mem_map_of_mem (f := Spec.NamedObject.toProof) hB, ?_⟩
    have hx' : x ∈ (Spec.Block.toSpecNamed B.toProofNamed).attestations := by
      rw [Spec.Block.toSpecNamed_toProofNamed]; exact hxB
    exact att_of_toSpecNamed hx'

/-! ## The receipt -/

/-- The field `process_gf_votes_mem` of `StoreRunFacts` at `Model.spec`: for every node state
    `n'` that `n`'s receipt of `o` can return, a vote `u` in the slot-`k` list of `n'`'s core store
    is in the slot-`k` list of `n`'s core store, or `o` is `u`, or `o` is a block that includes `u`. -/
theorem spec_process_gf_votes_mem : ∀ (S : Setup V) (n : (Model.spec (V := V)).N)
    (o : NamedObject V) (k : Slot) {u : GoldfishVote V} (n' : (Model.spec (V := V)).N),
    (Model.spec (V := V)).process S n o ⇢ n' →
    u ∈ n'.st.core.gf_votes k →
      u ∈ n.st.core.gf_votes k ∨ o = NamedObject.gfVote u ∨
        ∃ B : NamedBlock V, o = NamedObject.block B ∧ u ∈ B.gf_votes := by
  intro S n o k u n' hn' hu
  change u ∈ (n'.val.st.gf_votes k).map Spec.GoldfishVote.toProof at hu
  rw [NodeFacts.process_val_st S n o n' hn'] at hu
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hu
  change x ∈ (Member.receipt_process S n.val.st o).gf_votes k at hx
  cases o with
  | block B =>
    rcases gf_block_new _ _ _ _ k x hx with h | h
    · exact Or.inl (List.mem_map_of_mem h)
    · refine Or.inr (Or.inr ⟨B, rfl, ?_⟩)
      rw [← NodeFacts.toSpecNamed_gf_votes_map B]
      exact List.mem_map_of_mem h
  | gfVote u0 =>
    rcases gf_vote_new _ _ _ k x hx with h | rfl
    · exact Or.inl (List.mem_map_of_mem h)
    · right; left
      rw [Spec.GoldfishVote.toProof_toSpec]
  | attest a =>
    have hx' : x ∈ (Spec.Protocol.admit_attestation _ n.val.st _).gf_votes k := hx
    rw [gf_attest_eq] at hx'
    exact Or.inl (List.mem_map_of_mem hx')

/-- The field `process_sg_pool_mem` of `StoreRunFacts` at `Model.spec`: for every node state
    `n'` that `n`'s receipt of `o` can return, a round-`r` attestation in the attestation set of
    `n'`'s store is in that of `n`'s store, or `o` carries it. -/
theorem spec_process_sg_pool_mem : ∀ (S : Setup V) (n : (Model.spec (V := V)).N)
    (o : NamedObject V) (r : Round) {b : CombinedAttestation V} (n' : (Model.spec (V := V)).N),
    (Model.spec (V := V)).process S n o ⇢ n' →
    b ∈ n'.st.core.sg_pool r →
      b ∈ n.st.core.sg_pool r ∨ DecoupledConsensusModel.Proofs.Optimistic.CarriesRow o b := by
  intro S n o r b n' hn' hb
  change b ∈ (n'.val.st.sg_pool r).image Spec.Attestation.toProof at hb
  rw [NodeFacts.process_val_st S n o n' hn'] at hb
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hb
  rw [StoreSteps.mem_sg_pool_iff] at hx
  change x ∈ (Member.receipt_process S n.val.st o).attestations r at hx
  have hold : x ∈ n.val.st.attestations r → x.toProof ∈ n.st.core.sg_pool r := fun h =>
    show x.toProof ∈ (n.val.st.sg_pool r).image Spec.Attestation.toProof from
      Finset.mem_image_of_mem _ ((StoreSteps.mem_sg_pool_iff _ _ _).2 h)
  cases o with
  | block B =>
    rcases att_block_new _ _ _ _ r x hx with h | h
    · exact Or.inl (hold h)
    · exact Or.inr (att_of_toSpecNamed h)
  | gfVote u0 =>
    have hx' : x ∈ (Spec.Protocol.on_goldfish_vote_checked _ n.val.st _).attestations r :=
      hx
    rw [att_vote_eq] at hx'
    exact Or.inl (hold hx')
  | attest a =>
    rcases att_new _ _ _ r x hx with h | rfl
    · exact Or.inl (hold h)
    · right
      show (Spec.Attestation.toSpecNamed a).toProof = a.erase
      rw [HandlersFacts.toProof_toSpecNamed_attestation, Spec.Attestation.toProof_toSpec]

/-! ## The rows along a run -/

/-- The field `row_round_stateBefore` of `StoreRunFacts` at `Model.spec`: for every world `w`
    that can hold before the `i`-th event of `rho`, a named row `a` in bucket `k` of `reader`'s
    store rows in `w` is a row of round `k`. -/
theorem spec_row_round_stateBefore : ∀ (S : Setup V) (rho : Record.Run V) (i : Nat)
    (reader : V) (k : Round) (a : NamedAttestation V) (w : V → (Model.spec (V := V)).N)
    (_hw : w ∈ stateBeforeOf (Model.spec (V := V)) S rho i)
    (_ha : a ∈ (w reader).st.sg_rows k), a.round = k := by
  intro S rho i reader k a w hw ha
  have hI := HandlersRunFacts.rows_fold_ok S (rho.events.take i) w hw reader
  obtain ⟨a', rfl⟩ := HandlersFacts.exists_namedAtt a
  exact hI k a' ((HandlersRunFacts.mem_sg_rows_iff (w reader).val.st k a').1 ha)

end SpecRecord.StoreRunFacts

namespace DecoupledConsensusModel.Sts.Record

variable {V : Type} [DecidableEq V] [Fintype V] [Inhabited V]

/-- Every field of `StoreRunFacts` holds at `Model.spec`. -/
theorem Model.spec_runFacts_store : StoreRunFacts (Model.spec (V := V)) where
  tick_sg_pool_mem := SpecRecord.StoreRunFacts.spec_tick_sg_pool_mem
  row_round_stateBefore := SpecRecord.StoreRunFacts.spec_row_round_stateBefore
  process_sg_pool_mem := SpecRecord.StoreRunFacts.spec_process_sg_pool_mem
  tick_gf_votes_mem := SpecRecord.StoreRunFacts.spec_tick_gf_votes_mem
  process_gf_votes_mem := SpecRecord.StoreRunFacts.spec_process_gf_votes_mem

end DecoupledConsensusModel.Sts.Record
