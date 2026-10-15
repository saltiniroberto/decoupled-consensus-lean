import Proofs.Instance.Objects

/-!
# The blocks the confirmation update writes

`Protocol.update_confirmation` writes into `live_confirmed`, `latest_stable` and `latest_confirmed`
only blocks of the store's tree `st.T`, when the store's `F`, `J`, `latest_confirmed` and
`latest_stable` are (`update_confirmation_mem`); one lemma for each block it can write.
-/

set_option autoImplicit false

namespace SpecRecord.NodeFacts

open scoped DC

section Walk

variable {V : Type} [DecidableEq V]

omit [DecidableEq V] in
/-- If `x >>= f` answers `b`, then `x` answers some `a` and `f a` answers `b`. -/
theorem dre_bind_ok {α β : Type} {x : DC.DRE α} {f : α → DC.DRE β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- If `s.filterM p` answers `v`, every member of `v` is a member of `s`. -/
theorem filterM_ok_subset {α : Type} [DecidableEq α] (p : α → DC.DRE Bool) (s v : Finset α)
    (h : s.filterM p = .ok v) : v ⊆ s := by
  classical
  induction s using Finset.induction_on generalizing v with
  | empty =>
      have hvv : (∅ : Finset α) = v := Except.ok.inj h
      rw [← hvv]
  | @insert a s ha ih =>
      simp only [Finset.filterM, Finset.fold_insert ha, Finset.unionM] at h
      obtain ⟨A, hA, h⟩ := dre_bind_ok h
      obtain ⟨B, hB, h⟩ := dre_bind_ok h
      have hvAB : A ∪ B = v := Except.ok.inj h
      have hAsub : A ⊆ {a} := by
        obtain ⟨b, -, hA⟩ := dre_bind_ok hA
        split at hA
        · rw [← Except.ok.inj hA]
        · rw [← Except.ok.inj hA]
          exact fun x hx => absurd hx (by simp)
      have hBsub : B ⊆ s := ih B hB
      rw [← hvAB]
      intro x hx
      rcases Finset.mem_union.mp hx with h1 | h1
      · rw [Finset.mem_singleton.mp (hAsub h1)]
        exact Finset.mem_insert_self a s
      · exact Finset.mem_insert_of_mem (hBsub h1)

/-- If `pickUnique? T p` is `some a`, then `a` is a member of `T`. -/
theorem pickUnique?_mem {α : Type} [DecidableEq α] {T : Finset α} {p : α → Bool} {a : α}
    (h : Spec.pickUnique? T p = some a) : a ∈ T := by
  unfold Spec.pickUnique? at h
  split at h
  · rename_i hex
    rw [← Option.some.inj h]
    exact Finset.choose_mem _ _ hex
  · cases h

/-- If `ghost_step tree score eligible H` answers `some C`, then `C` is a block of `tree`. -/
theorem ghost_step_mem {tree : Finset (Spec.Block V)}
    {score : Spec.Block V → DC.DRE Nat} {eligible : Spec.Block V → DC.DRE Bool}
    {H C : Spec.Block V}
    (h : Spec.Protocol.ghost_step tree score eligible H = .ok (some C)) : C ∈ tree := by
  unfold Spec.Protocol.ghost_step at h
  obtain ⟨children, hc, h⟩ := dre_bind_ok h
  unfold Spec.Protocol.argmax? at h
  obtain ⟨best, hb, h⟩ := dre_bind_ok h
  have hC : Spec.pickUnique? best (fun _ => true) = some C := Except.ok.inj h
  exact filterM_ok_subset _ _ _ hc (filterM_ok_subset _ _ _ hb (pickUnique?_mem hC))

/-- If `ghost_walk tree score eligible n H` answers `R`, then `R` is `H` or a block of `tree`. -/
theorem ghost_walk_mem {tree : Finset (Spec.Block V)}
    {score : Spec.Block V → DC.DRE Nat} {eligible : Spec.Block V → DC.DRE Bool}
    (n : Nat) (H R : Spec.Block V)
    (h : Spec.Protocol.ghost_walk tree score eligible n H = .ok R) :
    R = H ∨ R ∈ tree := by
  induction n generalizing H with
  | zero =>
      left
      exact (Except.ok.inj h).symm
  | succ n ih =>
      simp only [Spec.Protocol.ghost_walk] at h
      obtain ⟨C?, hC?, h⟩ := dre_bind_ok h
      cases C? with
      | none =>
          left
          exact (Except.ok.inj h).symm
      | some C =>
          right
          have hCt : C ∈ tree := ghost_step_mem hC?
          have h' : Spec.Protocol.ghost_walk tree score eligible n C = .ok R := h
          rcases ih C h' with rfl | hR
          · exact hCt
          · exact hR

/-- If `ghost A tree score eligible` answers `H`, then `H` is `A` or a block of `tree`. -/
theorem ghost_mem {A H : Spec.Block V} {tree : Finset (Spec.Block V)}
    {score : Spec.Block V → DC.DRE Nat} {eligible : Spec.Block V → DC.DRE Bool}
    (h : Spec.Protocol.ghost A tree score eligible = .ok H) : H = A ∨ H ∈ tree :=
  ghost_walk_mem _ _ _ h

end Walk

section Store

variable {V : Type} [DecidableEq V]

/-- Every block of `get_filtered_block_tree st` is a block of `st.T`. -/
theorem get_filtered_block_tree_subset (st : Spec.Store V) :
    Spec.Protocol.get_filtered_block_tree st ⊆ st.T := by
  intro B hB
  simp only [Spec.Protocol.get_filtered_block_tree,
    Spec.Protocol.get_filtered_block_tree_from, Spec.Protocol.viable_tree,
    Spec.Protocol.finalized_descendants, Id.run, pure, Finset.mem_filter] at hB
  exact hB.1.1.1

omit [DecidableEq V] in
/-- If `st.F` and `st.J` are blocks of `st.T`, then so is `get_fg_root st`. -/
theorem get_fg_root_mem {st : Spec.Store V} (hF : st.F ∈ st.T) (hJ : st.J ∈ st.T) :
    Spec.Protocol.get_fg_root st ∈ st.T := by
  simp only [Spec.Protocol.get_fg_root, Id.run, pure]
  split_ifs
  · exact hJ
  · exact hF

/-- If `active_prefix st g` is `some X`, then `X` is a block of `st.T`. -/
theorem active_prefix_mem {st : Spec.Store V} {g : Option (Spec.Block V)}
    {X : Spec.Block V} (h : Spec.Protocol.active_prefix st g = some X) :
    X ∈ st.T := by
  simp only [Spec.Protocol.active_prefix, Id.run, pure] at h
  split at h
  · simp only [Spec.Protocol.activePrefix, Spec.Block.deepest?] at h
    have hX := pickUnique?_mem h
    rw [Finset.mem_filter] at hX
    exact get_filtered_block_tree_subset st hX.1
  · cases h

/-- If `st.F` and `st.J` are blocks of `st.T` and `get_sg_root_with C st` answers `A`, then `A` is a
    block of `st.T`. -/
theorem get_sg_root_with_mem {C : Spec.Config} {st : Spec.Store V}
    {A : Spec.Block V} (hF : st.F ∈ st.T) (hJ : st.J ∈ st.T)
    (h : Spec.Protocol.get_sg_root_with C st = .ok A) : A ∈ st.T := by
  unfold Spec.Protocol.get_sg_root_with at h
  obtain ⟨G1, -, h⟩ := dre_bind_ok h
  dsimp only at h
  split at h
  · rename_i hne
    rw [← Except.ok.inj h]
    obtain ⟨X, hX⟩ := Option.ne_none_iff_exists'.mp hne
    simp only [hX, Option.value]
    exact active_prefix_mem hX
  · rw [← Except.ok.inj h]
    exact get_fg_root_mem hF hJ

/-- If `st.F` and `st.J` are blocks of `st.T` and `round_stable_root st r` answers `G`, then `G` is
    a block of `st.T`. -/
theorem round_stable_root_mem {st : Spec.Store V} {r : Spec.Round}
    {G : Spec.Block V} (hF : st.F ∈ st.T) (hJ : st.J ∈ st.T)
    (h : Spec.Protocol.round_stable_root st r = .ok G) : G ∈ st.T := by
  unfold Spec.Protocol.round_stable_root at h
  obtain ⟨G2, -, h⟩ := dre_bind_ok h
  rw [← Except.ok.inj h]
  simp only [Spec.Protocol.stable_root, Id.run, pure]
  split
  · rename_i hne
    obtain ⟨X, hX⟩ := Option.ne_none_iff_exists'.mp hne
    simp only [hX, Option.value]
    exact active_prefix_mem hX
  · exact get_fg_root_mem hF hJ

/-- If `confirmation_candidate C st` answers `some S`, then `S` is a block of `st.T`. -/
theorem confirmation_candidate_mem {C : Spec.Config} {st : Spec.Store V}
    {S : Spec.Block V}
    (h : Spec.Protocol.confirmation_candidate C st = .ok (some S)) : S ∈ st.T := by
  unfold Spec.Protocol.confirmation_candidate at h
  obtain ⟨G2, -, h⟩ := dre_bind_ok h
  exact active_prefix_mem (Except.ok.inj h)

/-- If `old` and `candidate` are members of a set `T`, so is `advance_confirmed old candidate`. -/
theorem advance_confirmed_mem {T : Finset (Spec.Block V)}
    {old candidate : Spec.Block V} (ho : old ∈ T) (hc : candidate ∈ T) :
    Spec.Protocol.advance_confirmed old candidate ∈ T := by
  simp only [Spec.Protocol.advance_confirmed, Id.run, pure]
  split_ifs
  · exact ho
  · exact hc

/-- If `stable`, `candidate` and `old` are members of a set `T`, so is
    `floor_on_stable stable candidate old`. -/
theorem floor_on_stable_mem {T : Finset (Spec.Block V)}
    {stable candidate old : Spec.Block V} (hs : stable ∈ T) (hc : candidate ∈ T)
    (ho : old ∈ T) : Spec.Protocol.floor_on_stable stable candidate old ∈ T := by
  simp only [Spec.Protocol.floor_on_stable, Id.run, pure]
  split_ifs
  · exact hc
  · exact ho
  · exact hs

/-- If `st.F`, `st.J`, `st.latest_confirmed` and `st.latest_stable` are blocks of `st.T` and
    `update_confirmation C st s` answers `st'`, then `st'.live_confirmed`, `st'.latest_confirmed`
    and `st'.latest_stable` are blocks of `st.T`. -/
theorem update_confirmation_mem [Fintype V] {C : Spec.Config}
    {st st' : Spec.Store V}
    {s : Spec.Slot} (hF : st.F ∈ st.T) (hJ : st.J ∈ st.T)
    (hlt : st.latest_confirmed ∈ st.T)
    (hls : st.latest_stable ∈ st.T)
    (h : Spec.Protocol.update_confirmation C st s = .ok st') :
    st'.live_confirmed ∈ st.T ∧ st'.latest_confirmed ∈ st.T ∧ st'.latest_stable ∈ st.T := by
  simp only [Spec.Protocol.update_confirmation] at h
  obtain ⟨_, -, h⟩ := dre_bind_ok h
  obtain ⟨_, -, h⟩ := dre_bind_ok h
  obtain ⟨A, hA, h⟩ := dre_bind_ok h
  obtain ⟨H, hH, h⟩ := dre_bind_ok h
  obtain ⟨He, -, h⟩ := dre_bind_ok h
  obtain ⟨G, hG, h⟩ := dre_bind_ok h
  obtain ⟨S?, hS, h⟩ := dre_bind_ok h
  have hAm := get_sg_root_with_mem hF hJ hA
  have hHm : H ∈ st.T := by
    rcases ghost_mem hH with rfl | hH'
    · exact hAm
    · exact get_filtered_block_tree_subset st hH'
  have hsm : Spec.Protocol.advance_confirmed st.latest_stable G ∈ st.T :=
    advance_confirmed_mem hls (round_stable_root_mem hF hJ hG)
  have hroot := get_fg_root_mem hF hJ
  have hSm : ∀ S, S? = some S → S ∈ st.T := by
    intro S hS'
    subst hS'
    exact confirmation_candidate_mem hS
  split_ifs at h with h1 h2
  · have h' := Except.ok.inj h
    subst h'
    exact ⟨hHm, floor_on_stable_mem hsm (advance_confirmed_mem hlt hHm) hlt, hsm⟩
  · have h' := Except.ok.inj h
    subst h'
    obtain ⟨X, hX⟩ := Option.ne_none_iff_exists'.mp h2
    have hXm := hSm X hX
    refine ⟨hroot, floor_on_stable_mem hsm (advance_confirmed_mem hlt ?_) hlt, hsm⟩
    simp only [hX, Option.value]
    exact hXm
  · have h' := Except.ok.inj h
    subst h'
    exact ⟨hroot, floor_on_stable_mem hsm hlt hlt, hsm⟩

end Store

end SpecRecord.NodeFacts
