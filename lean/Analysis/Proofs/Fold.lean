import Analysis.Proofs.LockIn

set_option autoImplicit false

namespace Decoupled

open scoped Decoupled
open Framework.StsMultisetLog

namespace Proofs

section Store
variable {Node Root : Type} [DecidableEq Node] [DecidableEq Root] [Electorate Node] [Params]
  [BlockHash Node Root]

/-! ## Folding `on_block` -/

theorem onBlocks_nil (S : Store Node Root) : onBlocks S [] = S := rfl

theorem onBlocks_cons (S : Store Node Root) (B : Blk Node Root) (Bs : List (Blk Node Root)) :
    onBlocks S (B :: Bs) = onBlocks (onBlock S B) Bs := rfl

theorem onBlocks_append (S : Store Node Root) (Bs Cs : List (Blk Node Root)) :
    onBlocks S (Bs ++ Cs) = onBlocks (onBlocks S Bs) Cs := by
  simp only [onBlocks, List.foldl_append]

theorem storeInv_onBlocks {S : Store Node Root} (hinv : StoreInv S) :
    ∀ Bs : List (Blk Node Root), StoreInv (onBlocks S Bs)
  | [] => hinv
  | B :: Bs => by rw [onBlocks_cons]; exact storeInv_onBlocks (storeInv_onBlock hinv B) Bs

theorem onBlocks_T_mono (S : Store Node Root) :
    ∀ Bs : List (Blk Node Root), S.T ⊆ (onBlocks S Bs).T
  | [] => Finset.Subset.refl _
  | B :: Bs => by
      rw [onBlocks_cons]
      exact Finset.Subset.trans (onBlock_T_mono S B) (onBlocks_T_mono (onBlock S B) Bs)

theorem onBlocks_record_mono {S : Store Node Root}
    (hrec : ∀ B σB, S.σ B = some σB → postState B = .state σB) :
    ∀ (Bs : List (Blk Node Root)) {B : Blk Node Root} {σB : ChainState Node Root},
      S.σ B = some σB → (onBlocks S Bs).σ B = some σB
  | [], _, _, h => h
  | B' :: Bs, B, σB, h => by
      rw [onBlocks_cons]
      exact onBlocks_record_mono (fun _ _ hB => onBlock_recorded hrec _ _ hB) Bs
        (onBlock_record_mono hrec B' h)

omit [Electorate Node] [Params] in
theorem updates_T_sub_of {T₀ : Finset (Blk Node Root)} {S : Store Node Root}
    {J' F' : Blk Node Root} {h' : Nat} (h : S.T ⊆ T₀) :
    (updateFinalized (updateJustified S J' h') F').T ⊆ T₀ := by
  rw [updateFinalized_T, updateJustified_T]; exact h

theorem onBlock_T_sub (S : Store Node Root) (B' : Blk Node Root) :
    (onBlock S B').T ⊆ insert B' S.T := by
  simp only [onBlock, Id.run]
  repeat' split
  all_goals first
    | exact Finset.subset_insert _ _
    | exact updates_T_sub_of (Finset.union_subset (Finset.subset_insert _ _) (by simp))

/-- Every accepted block was folded in, or was accepted already. -/
theorem onBlocks_T_sub (S : Store Node Root) :
    ∀ (Bs : List (Blk Node Root)) (C : Blk Node Root), C ∈ (onBlocks S Bs).T →
      C ∈ S.T ∨ C ∈ Bs
  | [], C, hC => Or.inl hC
  | B :: Bs, C, hC => by
      rw [onBlocks_cons] at hC
      rcases onBlocks_T_sub (onBlock S B) Bs C hC with h | h
      · rcases Finset.mem_insert.1 (onBlock_T_sub S B h) with rfl | h
        · exact Or.inr (by simp)
        · exact Or.inl h
      · exact Or.inr (by simp [h])

theorem genesis_mem_onBlocks (Bs : List (Blk Node Root)) :
    (Blk.genesis : Blk Node Root) ∈ (onBlocks Store.gen Bs).T :=
  onBlocks_T_mono Store.gen Bs (Finset.mem_singleton_self _)

/-! ## The store-finalized block is accepted, with its whole chain -/

/-- The store's finalized block is itself accepted: it is genesis, or it sits on the chain of
    a record, and the tree is closed downward. -/
theorem F_mem_T {S : Store Node Root} (hinv : StoreInv S)
    (hg : (Blk.genesis : Blk Node Root) ∈ S.T) : S.F ∈ S.T := by
  rcases hinv.fProv with hgen | ⟨E, σE, hE, hF⟩
  · rw [hgen]; exact hg
  · have hET := record_mem_T hinv hE
    have hch := record_chained hinv hE
    have hL := record_L hinv hE
    have hFE : S.F ⪯ E := by
      rw [← hF, ← hL]; exact Preceq.trans hch.finJust hch.justLatest
    exact mem_T_of_preceq hinv E hET S.F hFE

/-! ## Acceptance -/

/-- The replay of a block whose parent is accepted is the block's own. -/
theorem replay_eq_postState {S : Store Node Root} (hinv : StoreInv S)
    {B P : Blk Node Root} (hP : B.parent = some P) (hPT : P ∈ S.T) :
    S.replay B = postState B := by
  obtain ⟨σP, hσP⟩ : ∃ σP, S.σ P = some σP := Option.isSome_iff_exists.1 ((hinv.domT P).1 hPT)
  have hpP : postState P = .state σP := record_postState hinv hσP
  cases B with
  | genesis => exact absurd hP (by simp [Blk.parent])
  | mk P₀ s n a r =>
      have hPP : P₀ = P := by
        have h3 : some P₀ = some P := hP
        injection h3
      subst hPP
      have hb : (Blk.mk P₀ s n a r).parent.bind S.σ = some σP := by
        simp only [Blk.parent, Option.bind_some]; exact hσP
      simp only [Store.replay, hb, postState, hpP]

omit [Electorate Node] [Params] in
theorem updates_T_mem {B : Blk Node Root} {S : Store Node Root} {J' F' : Blk Node Root}
    {h' : Nat} (h : B ∈ S.T) :
    B ∈ (updateFinalized (updateJustified S J' h') F').T := by
  rw [updateFinalized_T, updateJustified_T]; exact h

/-- A block that passes both asserts and replays is accepted. -/
theorem onBlock_mem_of_accept {S : Store Node Root} {B P : Blk Node Root}
    {σ' : ChainState Node Root} (hP : B.parent = some P) (hPT : P ∈ S.T)
    (hF : S.F ⪯ B) (hrep : S.replay B = .state σ') : B ∈ (onBlock S B).T := by
  simp only [onBlock, Id.run]
  split
  · rename_i P' hP'
    split_ifs with hadm
    · split
      · rename_i σ'' hrep'
        exact updates_T_mem (Finset.mem_union_right _ (Finset.mem_singleton_self _))
      · rename_i hbad
        rw [hrep] at hbad
        exact absurd hbad (by simp)
    · exfalso
      apply hadm
      have hPP : P' = P := by
        rw [hP] at hP'
        injection hP' with h3
        exact h3.symm
      subst hPP
      exact ⟨hPT, hF⟩
  · rename_i hnone
    rw [hP] at hnone
    exact absurd hnone (by simp)

omit [DecidableEq Node] [DecidableEq Root] [Electorate Node] [Params] [BlockHash Node Root] in
theorem exists_parent {B : Blk Node Root} (h : B ≠ Blk.genesis) : ∃ P, B.parent = some P := by
  cases B with
  | genesis => exact absurd rfl h
  | mk P s m a r => exact ⟨P, rfl⟩

theorem onBlocks_prefix_F (S : Store Node Root) (Bs : List (Blk Node Root)) (k : Nat) :
    (onBlocks S (Bs.take k)).F ⪯ (onBlocks S Bs).F := by
  conv_rhs => rw [← List.take_append_drop k Bs]
  rw [onBlocks_append]
  exact onBlocks_F _ _

/-! ## Every record's finalized block is at or below the fold's -/

omit [Params] [BlockHash Node Root] in
theorem gen_record_F : ∀ (E : Blk Node Root) (σE : ChainState Node Root),
    (Store.gen : Store Node Root).σ E = some σE →
      σE.F ⪯ (Store.gen : Store Node Root).F ∨ SlashableSet (Store.gen : Store Node Root).T E := by
  intro E σE hE
  have hE' : (if E = Blk.genesis then some (ChainState.gen : ChainState Node Root) else none)
      = some σE := hE
  split_ifs at hE' with hb
  injection hE' with h2
  rw [← h2]
  exact Or.inl (Preceq.refl _)

theorem onBlocks_record_F [PositiveWeight Node] {S₀ : Store Node Root} :
    ∀ (Bs : List (Blk Node Root)), StoreInv S₀ →
      (∀ E σE, S₀.σ E = some σE → σE.F ⪯ S₀.F ∨ SlashableSet S₀.T E) →
      ∀ E σE, (onBlocks S₀ Bs).σ E = some σE →
        σE.F ⪯ (onBlocks S₀ Bs).F ∨ SlashableSet (onBlocks S₀ Bs).T E
  | [], _, hbase, E, σE, h => hbase E σE h
  | B :: Bs, hinv, hbase, E, σE, h => by
      rw [onBlocks_cons] at h ⊢
      refine onBlocks_record_F Bs (storeInv_onBlock hinv B) ?_ E σE h
      intro E' σE' hE'
      by_cases hmem : E' ∈ S₀.T
      · obtain ⟨σ₀, hσ₀⟩ : ∃ σ₀, S₀.σ E' = some σ₀ :=
          Option.isSome_iff_exists.1 ((hinv.domT E').1 hmem)
        have hkeep : (onBlock S₀ B).σ E' = some σ₀ := onBlock_record_mono hinv.recorded B hσ₀
        have heq : σ₀ = σE' := by rw [hkeep] at hE'; injection hE'
        subst heq
        rcases hbase E' σ₀ hσ₀ with hpre | hev
        · exact Or.inl (Preceq.trans hpre (onBlock_F S₀ B))
        · exact Or.inr (SlashableSet.mono (onBlock_T_mono S₀ B) hev)
      · rcases onBlock_new_F hinv B hmem hE' with h1 | h1
        · exact Or.inl h1
        · exact Or.inr (SlashableSet.mono (onBlock_T_mono S₀ B) h1)

theorem fold_record_F [PositiveWeight Node] (Bs : List (Blk Node Root))
    {E : Blk Node Root} {σE : ChainState Node Root}
    (hE : (onBlocks Store.gen Bs).σ E = some σE) :
    σE.F ⪯ (onBlocks Store.gen Bs).F ∨ SlashableSet (onBlocks Store.gen Bs).T E :=
  onBlocks_record_F Bs storeInv_gen gen_record_F E σE hE

/-! ## Acceptance -/

theorem onBlocks_accept {Bs : List (Blk Node Root)} (hpf : ParentFirst Bs)
    {Fmax : Blk Node Root}
    (hFle : ∀ k : Nat, (onBlocks Store.gen (Bs.take k)).F ⪯ Fmax) :
    ∀ (n : Nat) (C : Blk Node Root), C ∈ Bs.take n → postState C ≠ invalid →
      (C ⪯ Fmax ∨ Fmax ⪯ C) → C ∈ (onBlocks Store.gen (Bs.take n)).T := by
  intro n
  induction n with
  | zero => intro C hC; simp at hC
  | succ n ih =>
      intro C hC hval hcomp
      by_cases hn : n < Bs.length
      case neg =>
        have he : Bs.take (n + 1) = Bs.take n := by
          rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
        rw [he] at hC ⊢
        exact ih C hC hval hcomp
      have hsplit : Bs.take (n + 1) = Bs.take n ++ [Bs[n]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hn]
        rfl
      rw [hsplit] at hC ⊢
      rw [onBlocks_append]
      have hfold : onBlocks (onBlocks Store.gen (Bs.take n)) [Bs[n]]
          = onBlock (onBlocks Store.gen (Bs.take n)) Bs[n] := rfl
      rw [hfold]
      obtain ⟨Sn, hSn⟩ : ∃ V : Store Node Root, V = onBlocks Store.gen (Bs.take n) := ⟨_, rfl⟩
      rw [← hSn]
      have hinvn : StoreInv Sn := by rw [hSn]; exact storeInv_onBlocks storeInv_gen _
      have hgn : (Blk.genesis : Blk Node Root) ∈ Sn.T := by rw [hSn]; exact genesis_mem_onBlocks _
      have hFn : Sn.F ⪯ Fmax := by rw [hSn]; exact hFle n
      have ihn : ∀ D ∈ Bs.take n, postState D ≠ invalid → (D ⪯ Fmax ∨ Fmax ⪯ D) → D ∈ Sn.T := by
        intro D hD hvD hcD; rw [hSn]; exact ih D hD hvD hcD
      rw [List.mem_append] at hC
      rcases hC with hC | hC
      · exact onBlock_T_mono Sn _ (ihn C hC hval hcomp)
      · have hCB : C = Bs[n] := by simpa using hC
        rw [← hCB]
        by_cases hCT : C ∈ Sn.T
        · exact onBlock_T_mono Sn C hCT
        have hCne : C ≠ Blk.genesis := fun hg => hCT (by rw [hg]; exact hgn)
        obtain ⟨P, hCP⟩ := exists_parent hCne
        obtain ⟨σC, hσC⟩ : ∃ σC, postState C = .state σC :=
          ⟨_, TransitionResult.state_get _ hval⟩
        have hPC : P ⪯ C := parent_preceq hCP
        have hcompP : P ⪯ Fmax ∨ Fmax ⪯ P := by
          rcases hcomp with h | h
          · exact Or.inl (Preceq.trans hPC h)
          · exact preceq_or_preceq C hPC h
        have hvalP : postState P ≠ invalid := by
          obtain ⟨σP, hσP⟩ := postState_ancestor C hPC hσC
          rw [hσP]; simp
        have hPT : P ∈ Sn.T := by
          rcases hpf n hn P (by rw [← hCB]; exact hCP) with hg | hmem
          · rw [hg]; exact hgn
          · exact ihn P hmem hvalP hcompP
        have hFC : Sn.F ⪯ C := by
          rcases hcomp with h | h
          · rcases preceq_or_preceq Fmax hFn h with g | g
            · exact g
            · exact absurd (mem_T_of_preceq hinvn Sn.F (F_mem_T hinvn hgn) C g) hCT
          · exact Preceq.trans hFn h
        have hrep : Sn.replay C = .state σC := by
          rw [replay_eq_postState hinvn hCP hPT]; exact hσC
        exact onBlock_mem_of_accept hCP hPT hFC hrep

/-- Two stores whose records are replays agree on any block both have recorded. -/
theorem record_agree {S S' : Store Node Root} (hinv : StoreInv S) (hinv' : StoreInv S')
    {B : Blk Node Root} {σB σB' : ChainState Node Root}
    (h : S.σ B = some σB) (h' : S'.σ B = some σB') : σB = σB' := by
  have g1 := record_postState hinv h
  have g2 := record_postState hinv' h'
  rw [g1] at g2
  injection g2

theorem record_of_mem {S : Store Node Root} (hinv : StoreInv S) {B : Blk Node Root}
    (hB : B ∈ S.T) : ∃ σB, S.σ B = some σB :=
  Option.isSome_iff_exists.1 ((hinv.domT B).1 hB)

omit [Electorate Node] [Params] [BlockHash Node Root] in
/-- Definition 11 (`hft:def:viable`) read the other way: a viable block has an accepted leaf
    above it whose recorded height meets the frontier. -/
theorem viableTree_witness {S : Store Node Root} {B : Blk Node Root} (h : B ∈ viableTree S) :
    B ∈ S.T ∧ ∃ (L : Blk Node Root) (σL : ChainState Node Root),
      L ∈ S.T ∧ (∀ C ∈ S.T, ¬ L ≺ C) ∧ B ⪯ L ∧ S.σ L = some σL ∧ σL.h ≥ S.hmax - 1 := by
  rw [viableTree, Finset.mem_filter] at h
  obtain ⟨hBT, L, hLT, hleaf, hBL, hany⟩ := h
  refine ⟨hBT, L, ?_⟩
  cases hL : S.σ L with
  | none => rw [hL] at hany; simp at hany
  | some σL =>
      rw [hL] at hany
      simp only [Option.any_some, decide_eq_true_eq] at hany
      exact ⟨σL, hLT, hleaf, hBL, rfl, hany⟩

/-! ## The evidence shape of Theorem 10 -/

/-- The accountable disjunct with two trees and no named finalizing chain: Theorem 10
    (`hft:thm:orderindep`)'s, where the evidence may sit on a chain either node accepted. -/
def SlashablePair (T T' : Finset (Blk Node Root)) : Prop :=
  Slashable (fun a => IncludedIn T a ∨ IncludedIn T' a)

omit [DecidableEq Node] [DecidableEq Root] [Params] [BlockHash Node Root] in
theorem SlashableSet.toPairLeft {T T' : Finset (Blk Node Root)} {B_F : Blk Node Root}
    (hBF : B_F ∈ T ∨ B_F ∈ T') (h : SlashableSet T B_F) : SlashablePair T T' := by
  obtain ⟨A, hw, hev⟩ := h
  refine ⟨A, hw, fun v hv => ?_⟩
  obtain ⟨a, b, ha, hb, hra, hrb, he⟩ := hev v hv
  refine ⟨a, b, ha, hb, ?_, ?_, he⟩
  · rcases hra with h1 | h1
    · exact hBF.imp (fun hf => ⟨B_F, hf, h1⟩) (fun hf => ⟨B_F, hf, h1⟩)
    · exact Or.inl h1
  · rcases hrb with h1 | h1
    · exact hBF.imp (fun hf => ⟨B_F, hf, h1⟩) (fun hf => ⟨B_F, hf, h1⟩)
    · exact Or.inl h1

omit [DecidableEq Node] [DecidableEq Root] [Params] [BlockHash Node Root] in
theorem SlashableSet.toPairRight {T T' : Finset (Blk Node Root)} {B_F : Blk Node Root}
    (hBF : B_F ∈ T ∨ B_F ∈ T') (h : SlashableSet T' B_F) : SlashablePair T T' := by
  obtain ⟨A, hw, hev⟩ := h
  refine ⟨A, hw, fun v hv => ?_⟩
  obtain ⟨a, b, ha, hb, hra, hrb, he⟩ := hev v hv
  refine ⟨a, b, ha, hb, ?_, ?_, he⟩
  · rcases hra with h1 | h1
    · exact hBF.imp (fun hf => ⟨B_F, hf, h1⟩) (fun hf => ⟨B_F, hf, h1⟩)
    · exact Or.inr h1
  · rcases hrb with h1 | h1
    · exact hBF.imp (fun hf => ⟨B_F, hf, h1⟩) (fun hf => ⟨B_F, hf, h1⟩)
    · exact Or.inr h1

end Store

/-! ## A validator's store is the fold of what was delivered to it -/

section Exec
variable {Node Root : Type} [DecidableEq Node] [DecidableEq Root] [Electorate Node] [Params]
  [BlockHash Node Root]

/-- The blocks one action delivers to `p`: what `deliveredBlocks` appends at each step. -/
def deliveredAt (a : Action Node (StoreMsg Node Root) Empty) (p : Node) :
    List (Blk Node Root) :=
  match a with
  | .deliver q m => if q = p then (match m.msg with | .block B => [B]) else []
  | _ => []

theorem deliveredBlocks_succ {sched : Schedule Node}
    (x : Exec (protocol (Node := Node) (Root := Root)) sched) (p : Node) (i : Nat) :
    deliveredBlocks x p (i + 1) = deliveredBlocks x p i ++ deliveredAt (x.lbl i) p := rfl

theorem reaction_recv_state (S : Store Node Root)
    (m : SignedMsg Node (StoreMsg Node Root)) :
    (reaction S (.recv m)).state = Decoupled.receive S m.msg := rfl

omit [DecidableEq Root] [Electorate Node] [Params] [BlockHash Node Root] in
theorem deliveredAt_self (p : Node) (m : SignedMsg Node (StoreMsg Node Root))
    {B : Blk Node Root} (hm : m.msg = .block B) :
    deliveredAt (.deliver p m) p = [B] := by
  simp [deliveredAt, hm]

omit [DecidableEq Root] [Electorate Node] [Params] [BlockHash Node Root] in
theorem deliveredAt_other {q p : Node} (h : q ≠ p)
    (m : SignedMsg Node (StoreMsg Node Root)) :
    deliveredAt (Action.deliver q m) p = ([] : List (Blk Node Root)) := by
  simp only [deliveredAt, if_neg h]

/-- One step folds exactly the blocks that step delivered to `p`. -/
theorem exec_step_delivered {sched : Schedule Node}
    (x : Exec (protocol (Node := Node) (Root := Root)) sched) (p : Node) (i : Nat) :
    x[i + 1][p].st = onBlocks (x[i][p].st) (deliveredAt (x.lbl i) p) := by
  refine Step.elim (motive := fun a c c' => c'[p].st = onBlocks (c[p].st) (deliveredAt a p))
    (x.step i) (fun d t => rfl) ?tick ?deliver ?wake
    (fun d q ev res he hp => ev.elim) (fun d q m he => rfl)
  case tick =>
    intro d q t res he hp
    have hres : res = reaction ((setClock q t d)[q].st) .tick := hp
    by_cases hqp : q = p
    · subst hqp
      rw [applyNodeStepResult_st_self, hres, setClock_st]
      rfl
    · rw [applyNodeStepResult_st_other hqp, setClock_st]
      rfl
  case deliver =>
    intro d q m res he hp
    have hres : res = reaction ((Framework.StsMultisetLog.receive q m d)[q].st) (.recv m) := hp
    by_cases hqp : q = p
    · subst hqp
      obtain ⟨B, hm⟩ : ∃ B, m.msg = StoreMsg.block B := by
        cases h : m.msg with
        | block B => exact ⟨B, rfl⟩
      rw [applyNodeStepResult_st_self, hres, receive_st, deliveredAt_self q m hm,
        reaction_recv_state, hm]
      rfl
    · rw [applyNodeStepResult_st_other hqp, receive_st, deliveredAt_other hqp]
      rfl
  case wake =>
    intro d q res he hp
    have hres : res = reaction (d[q].st) .wake := hp
    by_cases hqp : q = p
    · subst hqp
      rw [applyNodeStepResult_st_self, hres]
      rfl
    · rw [applyNodeStepResult_st_other hqp]
      rfl

/-- **A validator's store is the fold of what was delivered to it.** -/
theorem storeAt_eq_fold {sched : Schedule Node}
    (x : Exec (protocol (Node := Node) (Root := Root)) sched) (p : Node) :
    ∀ i : Nat, storeAt x p i = onBlocks Store.gen (deliveredBlocks x p i)
  | 0 => by
      have hn : x[0][p] = { clock := 0, st := protocol.init p, view := ∅ } := x.init.2.1 p
      show x[0][p].st = _
      rw [hn]
      rfl
  | i + 1 => by
      have h1 : storeAt x p (i + 1) = onBlocks (storeAt x p i) (deliveredAt (x.lbl i) p) :=
        exec_step_delivered x p i
      rw [h1, storeAt_eq_fold x p i, ← onBlocks_append, ← deliveredBlocks_succ]

end Exec

end Proofs

end Decoupled
