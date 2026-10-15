import Proofs.Vocabulary.Protocol.ChainState.W4NamedJustificationMonotone
import Proofs.Claims.Spec2Claims.Claim13beRoute3_25
import Proofs.Claims.Spec2Claims.Claim13bModel_derive_named
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedBlock_Preceq
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedBlock_parent
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedBlock_slot
import Proofs.Claims.Spec2Claims.Claim13bModel_NamedBlock_attestations

/-!
# Named ancestry and the chain state along a chain

Facts about `NamedBlock` ancestry, slots, and the chain state `Protocol.derive_named` along a chain,
with no execution read. `h(B)` is the chain-state height `(Protocol.derive_named E cfg B).h` and
`T_h(B)` its entry block.
-/

set_option autoImplicit false

namespace DecoupledConsensusModel.Sts

open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Proofs

variable {V : Type} [DecidableEq V] [Fintype V]

section PureChain

omit [Fintype V] in
/-- Ancestry is transitive. -/
theorem namedPreceq_trans_l85 {A B C : NamedBlock V} (h1 : NamedBlock.Preceq A B)
    (h2 : NamedBlock.Preceq B C) : NamedBlock.Preceq A C := by
  induction C with
  | genesis =>
    rw [namedPreceq_genesis_iff_l85] at h2
    subst h2
    exact h1
  | node p s root votes support rows proposer ih =>
    rcases namedPreceq_node_iff_l85.mp h2 with rfl | hp
    · exact h1
    · exact namedPreceq_node_iff_l85.mpr (Or.inr (ih hp))

omit [Fintype V] in
/-- Genesis is an ancestor of every block. -/
theorem genesis_namedPreceq_l85 (B : NamedBlock V) : NamedBlock.Preceq .genesis B := by
  induction B with
  | genesis => exact namedPreceq_genesis_iff_l85.mpr rfl
  | node p s root votes support rows proposer ih =>
    exact namedPreceq_node_iff_l85.mpr (Or.inr ih)

omit [Fintype V] in
/-- A block's parent is an ancestor of it. -/
theorem parent_namedPreceq_l85 (B : NamedBlock V) : NamedBlock.Preceq B.parent B := by
  cases B with
  | genesis =>
    rw [namedBlock_parent_genesis]
    exact namedPreceq_genesis_iff_l85.mpr rfl
  | node p s root votes support rows proposer =>
    rw [namedBlock_parent_node]
    exact namedBlock_Preceq_parent_node p s root votes support rows proposer

omit [Fintype V] in
/-- Two ancestors of one block are ordered by ancestry. -/
theorem namedPreceq_total_l85 {A B C : NamedBlock V} (hA : NamedBlock.Preceq A C)
    (hB : NamedBlock.Preceq B C) : NamedBlock.Preceq A B ∨ NamedBlock.Preceq B A := by
  induction C with
  | genesis =>
    rw [namedPreceq_genesis_iff_l85] at hA hB
    subst hA; subst hB
    exact Or.inl (Proofs.NamedAncestry.named_self _)
  | node p s root votes support rows proposer ih =>
    rcases namedPreceq_node_iff_l85.mp hA with rfl | hAp
    · exact Or.inr hB
    · rcases namedPreceq_node_iff_l85.mp hB with rfl | hBp
      · exact Or.inl hA
      · exact ih hAp hBp

omit [Fintype V] in
/-- If every block `X ⪯ Z` other than genesis has its parent's slot less than its own, then along
    `Z`'s chain an ancestor's slot is at most its descendant's, and strictly smaller when the two
    differ. -/
theorem slot_le_of_namedPreceq_l85 {Z : NamedBlock V}
    (hsl : ∀ X : NamedBlock V, NamedBlock.Preceq X Z → X ≠ .genesis → X.parent.slot < X.slot)
    {A B : NamedBlock V} (hAB : NamedBlock.Preceq A B) (hBZ : NamedBlock.Preceq B Z) :
    A.slot ≤ B.slot ∧ (A ≠ B → A.slot < B.slot) := by
  induction B with
  | genesis =>
    rw [namedPreceq_genesis_iff_l85] at hAB
    subst hAB
    exact ⟨le_rfl, fun h => absurd rfl h⟩
  | node p s root votes support rows proposer ih =>
    have hpZ : NamedBlock.Preceq p Z :=
      namedPreceq_trans_l85 (namedBlock_Preceq_parent_node p s root votes support rows proposer)
        hBZ
    have hlt : p.slot < s := by
      have := hsl _ hBZ (by intro h; cases h)
      simpa only [namedBlock_parent_node, named_node_slot] using this
    rcases namedPreceq_node_iff_l85.mp hAB with rfl | hAp
    · exact ⟨le_rfl, fun h => absurd rfl h⟩
    · have := (ih hAp hpZ).1
      refine ⟨(this.trans (by rw [named_node_slot]; exact hlt.le)), fun _ => lt_of_le_of_lt this ?_⟩
      simpa only [named_node_slot] using hlt

variable (E : Env V) (cfg : Protocol.HeightConfig)

/-- If `A ⪯ B` and `h(A) = h(B)`, then `A` and `B` carry the same `nj` bit. -/
theorem nj_eq_on_plateau_l85 {A B : NamedBlock V} (hAB : NamedBlock.Preceq A B)
    (hh : (Protocol.derive_named E cfg A).h = (Protocol.derive_named E cfg B).h) :
    (Protocol.derive_named E cfg A).nj = (Protocol.derive_named E cfg B).nj := by
  induction B with
  | genesis =>
    rw [namedPreceq_genesis_iff_l85] at hAB
    subst hAB; rfl
  | node p s root votes support rows proposer ih =>
    rcases namedPreceq_node_iff_l85.mp hAB with rfl | hAp
    · rfl
    · have hle := Proofs.NamedEntryHeight.derive_height_mono E cfg hAp
      have hpB := Proofs.NamedEntryHeight.derive_height_mono E cfg
        (namedBlock_Preceq_parent_node p s root votes support rows proposer)
      have hpeq : (Protocol.derive_named E cfg p).h =
          (Protocol.derive_named E cfg (.node p s root votes support rows proposer)).h :=
        Nat.le_antisymm hpB (hh ▸ hle)
      rw [ih hAp (hh.trans hpeq.symm)]
      exact (derive_named_node_nj_of_h_eq E cfg p s root votes support rows proposer
        hpeq.symm).symm

/-- If `A ⪯ Z` and `h(A) ≤ m ≤ h(Z)`, then some `X` with `A ⪯ X ⪯ Z` has `h(X) = m`. -/
theorem exists_between_height_l85 {A Z : NamedBlock V} (hAZ : NamedBlock.Preceq A Z)
    {m : Height} (hlo : (Protocol.derive_named E cfg A).h ≤ m)
    (hhi : m ≤ (Protocol.derive_named E cfg Z).h) :
    ∃ X : NamedBlock V, NamedBlock.Preceq A X ∧ NamedBlock.Preceq X Z ∧
      (Protocol.derive_named E cfg X).h = m := by
  induction Z with
  | genesis =>
    rw [namedPreceq_genesis_iff_l85] at hAZ
    subst hAZ
    exact ⟨.genesis, Proofs.NamedAncestry.named_self _, Proofs.NamedAncestry.named_self _,
      Nat.le_antisymm hlo hhi⟩
  | node p s root votes support rows proposer ih =>
    rcases namedPreceq_node_iff_l85.mp hAZ with rfl | hAp
    · exact ⟨_, Proofs.NamedAncestry.named_self _, Proofs.NamedAncestry.named_self _,
        Nat.le_antisymm hlo hhi⟩
    · have hpZ : NamedBlock.Preceq p (.node p s root votes support rows proposer) :=
        namedBlock_Preceq_parent_node p s root votes support rows proposer
      by_cases hm : m ≤ (Protocol.derive_named E cfg p).h
      · obtain ⟨X, hAX, hXp, hXm⟩ := ih hAp hm
        exact ⟨X, hAX, namedPreceq_trans_l85 hXp hpZ, hXm⟩
      · rcases Proofs.NamedEntryHeight.derive_node_height_cases E cfg p s root votes support
          rows proposer with hc | hc
        · exact absurd (hc ▸ hhi) hm
        · refine ⟨_, hAZ, Proofs.NamedAncestry.named_self _, ?_⟩
          change (Protocol.derive_named E cfg (.node p s root votes support rows proposer)).h
            = (Protocol.derive_named E cfg p).h + 1 at hc
          rw [hc] at hhi ⊢
          exact Nat.le_antisymm (Nat.succ_le_of_lt (Nat.lt_of_not_le hm)) hhi

/-- Some ancestor `E₀` of `B` erases to `B`'s entry `T_h(B)`, is at `B`'s height, and has `T_h(B)`'s
    slot. -/
theorem entry_named_l85 (B : NamedBlock V) :
    ∃ E₀ : NamedBlock V, NamedBlock.Preceq E₀ B ∧
      E₀.erase = (Protocol.derive_named E cfg B).T_h ∧
      (Protocol.derive_named E cfg E₀).h = (Protocol.derive_named E cfg B).h ∧
      E₀.slot = (Protocol.derive_named E cfg B).T_h.slot := by
  obtain ⟨E₀, h1, h2, h3⟩ := Proofs.NamedEntryHeight.entry_ancestor_same_height E cfg B
  refine ⟨E₀, h1, h2, h3, ?_⟩
  rw [← h2, Proofs.NamedWire.erase_slot]

/-- If `e + d ≤ p` and `p + 1 ≤ o + d`, then `e < o`. -/
theorem nat_entry_lt_l85 (e d p o : Nat) (h1 : e + d ≤ p) (h2 : p + 1 ≤ o + d) : e < o := by
  omega

/-- If `Pc` is not genesis, `Pm ⪯ parent(Pc)`, `h(Pm) = h(Pc)`, and, when `parent(Pc)` is at that
    height with `Pm`'s entry, some quorum's members are each in the parent's progress set or sign a
    row of `Pc` matching the parent's height and entry, then
    `Pc.slot < T_h(Pc).slot + timeoutDelay`. -/
theorem climb_entryYoung_l85 {Pm Pc : NamedBlock V}
    (hPcne : Pc ≠ .genesis) (hPm : NamedBlock.Preceq Pm Pc.parent)
    (hh : (Protocol.derive_named E cfg Pm).h = (Protocol.derive_named E cfg Pc).h)
    (hcov : (Protocol.derive_named E cfg Pc.parent).h = (Protocol.derive_named E cfg Pc).h →
      (Protocol.derive_named E cfg Pc.parent).T_h = (Protocol.derive_named E cfg Pm).T_h →
      ∃ Q : Finset V, E.electorate.IsQuorum Q ∧ ∀ i ∈ Q,
        i ∈ (Protocol.derive_named E cfg Pc.parent).progress ∨
        ∃ a ∈ Pc.attestations, a.val_index = i ∧
          a.height_pair.matchesEntry (Protocol.derive_named E cfg Pc.parent).h
            (Protocol.derive_named E cfg Pc.parent).T_h.root = true) :
    Pc.slot < (Protocol.derive_named E cfg Pc).T_h.slot + cfg.timeoutDelay := by
  cases Pc with
  | genesis => exact absurd rfl hPcne
  | node p s root votes support rows proposer =>
    simp only [namedBlock_parent_node] at hPm hcov
    have h2 := Proofs.NamedEntryHeight.derive_height_mono E cfg hPm
    have h3 := Proofs.NamedEntryHeight.derive_height_mono E cfg
      (namedBlock_Preceq_parent_node p s root votes support rows proposer)
    have hpH : (Protocol.derive_named E cfg p).h =
        (Protocol.derive_named E cfg (.node p s root votes support rows proposer)).h :=
      Nat.le_antisymm h3 (hh ▸ h2)
    have hTp : (Protocol.derive_named E cfg p).T_h = (Protocol.derive_named E cfg Pm).T_h :=
      (Proofs.NamedEntryHeight.entry_eq_on_plateau E cfg hPm (hh.trans hpH.symm)).symm
    have hTc : (Protocol.derive_named E cfg (.node p s root votes support rows proposer)).T_h =
        (Protocol.derive_named E cfg p).T_h :=
      Proofs.NamedEntryHeight.node_entry_eq_of_height_eq E cfg p s root votes support rows
        proposer hpH.symm
    obtain ⟨Q, hQ, hcovQ⟩ := hcov hpH hTp
    rw [hTc]
    by_contra hnot
    have hmat : (Protocol.derive_named E cfg p).T_h.slot + cfg.timeoutDelay ≤ s := by
      simpa only [named_node_slot, not_lt] using hnot
    have hquorum : E.electorate.IsQuorum
        (Protocol.fold_rows (Protocol.TimeoutBinding.targeted V) (Protocol.derive_named E cfg p)
          (NamedBlock.node p s root votes support rows proposer).erase rows).progress := by
      apply Protocol.isQuorum_of_subset hQ
      intro i hi
      rcases hcovQ i hi with hold | ⟨a, ha, hai, hmatch⟩
      · exact fold_rows_progress_subset _ _ rows hold
      · rw [← hai]
        exact fold_rows_mem_progress_of_matching _ _
          (by simpa only [named_node_attestations] using ha) hmatch
    obtain ⟨hfh, hfT, -⟩ := fold_rows_fields_l85 (Protocol.derive_named E cfg p)
      (NamedBlock.node p s root votes support rows proposer).erase rows
    have hmat' : (Protocol.fold_rows (Protocol.TimeoutBinding.targeted V)
        (Protocol.derive_named E cfg p) (NamedBlock.node p s root votes support rows
          proposer).erase rows).T_h.slot + cfg.timeoutDelay ≤
        (Protocol.fold_rows (Protocol.TimeoutBinding.targeted V)
          (Protocol.derive_named E cfg p) (NamedBlock.node p s root votes support rows
            proposer).erase rows).s := by
      rw [hfT, fold_rows_s_l85, Proofs.NamedWire.erase_slot, named_node_slot]; exact hmat
    have hadv := NjGap.advances_of_progress_quorum E cfg hmat' hquorum
    rw [hfh] at hadv
    rw [← derive_node_l85] at hadv
    rw [hadv] at hpH
    exact absurd hpH (Nat.succ_ne_self _).symm

/-- If `a ≤ p` and `p + 1 ≤ a + k`, then `p − a < k`. -/
theorem nat_sub_lt_of_succ_le_l85 (p a k : Nat) (ha : a ≤ p) (h : p + 1 ≤ a + k) :
    p - a < k := by omega

/-- If `a ≤ p`, then `p + 1 − a − 1 = p − a`. -/
theorem nat_succ_sub_sub_l85 (p a : Nat) (h : a ≤ p) : p + 1 - a - 1 = p - a := by omega

/-- If `b + (j − 1)·d ≤ e` and `e + d ≤ s` with `1 ≤ j`, then `b + j·d ≤ s`. -/
theorem nat_spacing_step_l85 (b j d e s : Nat) (hj : 1 ≤ j) (h1 : b + (j - 1) * d ≤ e)
    (h2 : e + d ≤ s) : b + j * d ≤ s := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h1
  rw [Nat.succ_mul]
  omega

/-- If slots increase along `Z`'s chain, `A ⪯ Z`, `1 ≤ k`, `h_j(Z) < h(A)`, no `h(A) + j` with
    `1 ≤ j < k` is a multiple of `K`, and `h(A) + k ≤ h(Z)`, then
    `A.slot + 1 + (k − 1)·timeoutDelay ≤ Z.slot`. -/
theorem progress_spacing_l85 {A Z : NamedBlock V}
    (hsl : ∀ X : NamedBlock V, NamedBlock.Preceq X Z → X ≠ .genesis →
      X.parent.slot < X.slot)
    (hAZ : NamedBlock.Preceq A Z) {k : Nat} (hk : 1 ≤ k)
    (hnoJ : (Protocol.derive_named E cfg Z).h_j < (Protocol.derive_named E cfg A).h)
    (hK : ∀ j : Nat, 1 ≤ j → j < k → ¬ cfg.K ∣ (Protocol.derive_named E cfg A).h + j)
    (hreach : (Protocol.derive_named E cfg A).h + k ≤ (Protocol.derive_named E cfg Z).h) :
    A.slot + 1 + (k - 1) * cfg.timeoutDelay ≤ Z.slot := by
  have inv : ∀ X : NamedBlock V, NamedBlock.Preceq A X → NamedBlock.Preceq X Z →
      (Protocol.derive_named E cfg X).h ≤ (Protocol.derive_named E cfg A).h + k →
      (Protocol.derive_named E cfg X).h = (Protocol.derive_named E cfg A).h ∨
        A.slot + 1 + ((Protocol.derive_named E cfg X).h - (Protocol.derive_named E cfg A).h - 1)
          * cfg.timeoutDelay ≤ (Protocol.derive_named E cfg X).T_h.slot := by
    intro X
    induction X with
    | genesis =>
      intro hAX _ _
      rw [namedPreceq_genesis_iff_l85] at hAX
      subst hAX
      exact Or.inl rfl
    | node p s root votes support rows proposer ih =>
      intro hAX hXZ hXk
      rcases namedPreceq_node_iff_l85.mp hAX with heq | hAp
      · rw [heq]; exact Or.inl rfl
      have hpX : NamedBlock.Preceq p (.node p s root votes support rows proposer) :=
        namedBlock_Preceq_parent_node p s root votes support rows proposer
      have hpZ : NamedBlock.Preceq p Z := namedPreceq_trans_l85 hpX hXZ
      have hpXh := Proofs.NamedEntryHeight.derive_height_mono E cfg hpX
      have hAph := Proofs.NamedEntryHeight.derive_height_mono E cfg hAp
      have ihp := ih hAp hpZ (hpXh.trans hXk)
      rcases Proofs.NamedEntryHeight.derive_node_height_cases E cfg p s root votes support
          rows proposer with hc | hc
      · have hT := Proofs.NamedEntryHeight.node_entry_eq_of_height_eq E cfg p s root votes
          support rows proposer hc
        change (Protocol.derive_named E cfg (.node p s root votes support rows proposer)).h
          = (Protocol.derive_named E cfg p).h at hc
        rw [hc, hT]
        exact ihp
      · change (Protocol.derive_named E cfg (.node p s root votes support rows proposer)).h
          = (Protocol.derive_named E cfg p).h + 1 at hc
        right
        have hTX : (Protocol.derive_named E cfg (.node p s root votes support rows proposer)).T_h
            = (NamedBlock.node p s root votes support rows proposer).erase :=
          derive_named_node_T_h_of_height_succ E cfg p s root votes support rows proposer hc
        rw [hTX, Proofs.NamedWire.erase_slot]
        simp only [named_node_slot]
        by_cases hpA : (Protocol.derive_named E cfg p).h = (Protocol.derive_named E cfg A).h
        ·
          have hlt := (slot_le_of_namedPreceq_l85 hsl hAp hpZ).1
          have hps : p.slot < s := by
            have := hsl _ hXZ (by intro h; cases h)
            simpa only [namedBlock_parent_node, named_node_slot] using this
          rw [hc, hpA, Nat.add_sub_cancel_left, Nat.sub_self, Nat.zero_mul, Nat.add_zero]
          exact Nat.succ_le_of_lt (lt_of_le_of_lt hlt hps)
        ·
          have hbound := ihp.resolve_left hpA
          have hj1 : 1 ≤ (Protocol.derive_named E cfg p).h - (Protocol.derive_named E cfg A).h :=
            Nat.sub_pos_of_lt (lt_of_le_of_ne hAph (Ne.symm hpA))
          have hjk : (Protocol.derive_named E cfg p).h - (Protocol.derive_named E cfg A).h < k := by
            have := hc ▸ hXk
            exact nat_sub_lt_of_succ_le_l85 _ _ _ hAph this
          have hpeq : (Protocol.derive_named E cfg p).h = (Protocol.derive_named E cfg A).h +
              ((Protocol.derive_named E cfg p).h - (Protocol.derive_named E cfg A).h) :=
            (Nat.add_sub_cancel' hAph).symm
          rcases advance_cases_l85 E cfg p s root votes support rows proposer hc with
            hj | hnjp | hmat
          · exfalso
            have hjZ := HealingSurface.namedJustification_le_of_preceq E cfg hXZ
            rw [hj] at hjZ
            exact absurd (lt_of_le_of_lt (hAph.trans hjZ) hnoJ) (lt_irrefl _)
          · exfalso
            have hK' := hK _ hj1 hjk
            rw [← hpeq] at hK'
            rw [nj_false_of_not_dvd_l85 E cfg p hK'] at hnjp
            exact Bool.false_ne_true hnjp
          · rw [hc, nat_succ_sub_sub_l85 _ _ hAph]
            exact nat_spacing_step_l85 _ _ _ _ _ hj1 hbound hmat
  obtain ⟨X, hAX, hXZ, hXh⟩ := exists_between_height_l85 E cfg hAZ
    (m := (Protocol.derive_named E cfg A).h + k) (Nat.le_add_right _ _) hreach
  rcases inv X hAX hXZ (le_of_eq hXh) with hEq | hb
  · rw [hXh] at hEq
    have hk0 : k = 0 := Nat.add_left_cancel (hEq.trans (Nat.add_zero _).symm)
    exact absurd hk (by rw [hk0]; exact Nat.not_succ_le_zero 0)
  · rw [hXh, Nat.add_sub_cancel_left] at hb
    obtain ⟨E₀, hE₀X, -, -, hE₀s⟩ := entry_named_l85 E cfg X
    have hZZ : NamedBlock.Preceq Z Z := Proofs.NamedAncestry.named_self Z
    have h1 := (slot_le_of_namedPreceq_l85 hsl hE₀X hXZ).1
    have h2 := (slot_le_of_namedPreceq_l85 hsl hXZ hZZ).1
    rw [hE₀s] at h1
    exact hb.trans (h1.trans h2)

end PureChain

end DecoupledConsensusModel.Sts
