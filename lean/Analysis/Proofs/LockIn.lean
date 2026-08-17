import Analysis.Proofs.Acceptance

/-!
# Theorem 9 (`hft:thm:lockin`): lock-in

Three claims about a store that has processed a block justifying a finalized `F` at that
block's finalized height: the store root sits at or below `F`'s chain, `F` stays viable, and
every confirmation descends from `F`. The first two are Lemma 9 (`hft:lem:upgrade`) and
Lemma 10 (`hft:lem:viable-finalized`) applied directly — `upgrade` and `viable_of_height_lt`.

**All three are proved at one store, not chased across steps.** The paper says "at all future
times"; the execution wrapper reaches that by re-applying the store-level result at the later
store, where the record still exists (`reachesFrom_record`). Chasing `Σ.J` forward instead
would not work: `J` is not `⪯`-monotone, because `update_justified` compares keys, not
ancestry.

## The third claim, and where it departs from the paper

The paper splits on the cascade: if `Σ.hmax = Σ.h_j + 1` the walk-from block is `Σ.J ⪰ F` and
every confirmation descends from it; otherwise `Σ.hmax ≥ Σ.h_j + 2 ≥ h_f + 2`, so a confirmed
block sits at state-height above `h_f` and its Lemma 4 (`hft:lem:mainsafety`) puts `F` below
it. That is the argument here too, but the case split is done *inside the refutation*: rather
than proving the claim for every `C`, the proof asks classically whether some confirmation
fails to descend from `F`, and only that `C` has to be dealt with. Then each of the paper's
easy cases becomes a contradiction with `¬ F ⪯ C`, which is shorter than carrying the
disjunction through.

One step the paper leaves implicit: the second case needs `Σ.F ⪯ F` before `keyDom` can bound
`h_f` by `Σ.h_j`. It comes free — `F ⪯ Σ.J` (the first claim) and `Σ.F ⪯ Σ.J` (Theorem 4) make
`F` and `Σ.F` two ancestors of one block, hence comparable, and the other order gives
`F ⪯ Σ.F ⪯ Σ.R ⪯ C`, which is the contradiction again.
-/

set_option autoImplicit false

namespace Decoupled

open scoped Decoupled
open Framework.StsMultisetLog

namespace Proofs

section Store
variable {Node Root : Type} [DecidableEq Node] [DecidableEq Root] [Electorate Node] [Params]
  [BlockHash Node Root]

/-- **Lock-in at one store.** Read aloud: if some chain finalized `F` at height `h_f` and the
    store holds a recorded state whose justified pair is exactly `(F, h_f)`, then the store
    root descends from `F`, `F` is viable, and every block the fork choice may confirm
    descends from `F` — or a slashable set of weight `2q − W` is exhibited.

    See the module docstring for the shape of the third claim's proof. -/
theorem lockIn_store [PositiveWeight Node] {S : Store Node Root} (hinv : StoreInv S)
    (hFJ : S.F ⪯ S.J) {B_F F : Blk Node Root} {h_f : Nat}
    (hBF : postState B_F ≠ invalid)
    (hF : (postState' B_F).F = F) (hhF : (postState' B_F).h_F = h_f)
    {B : Blk Node Root} {σB : ChainState Node Root} (hB : S.σ B = some σB)
    (hJ : σB.J = F) (hhj : σB.h_j = h_f) :
    (F ⪯ S.J ∧ F ∈ viableTree S ∧ ∀ C, GetConfirmed S C → F ⪯ C) ∨ SlashableThirdOn S.T B_F := by
  -- `F` is on the record's chain, so the store has accepted it, and its height is below the
  -- store's maximum: `h_f = σB.h_j < σB.h ≤ Σ.hmax`.
  have hchB : Chained σB := record_chained hinv hB
  have hLB : σB.L = B := record_L hinv hB
  have hBT : B ∈ S.T := record_mem_T hinv hB
  have hFB : F ⪯ B := by rw [← hLB, ← hJ]; exact hchB.justLatest
  have hFT : F ∈ S.T := mem_T_of_preceq hinv B hBT F hFB
  have hlt : h_f < S.hmax := by
    have g1 := hchB.hj_lt_h
    have g2 := hinv.hmaxLe B σB hB
    omega
  rcases upgrade hinv hFJ hBF hF hhF hB hJ hhj with h1 | hev
  case inr => exact Or.inr hev
  rcases viable_of_height_lt hinv hBF hF hhF hFT hlt with h2 | hev
  case inr => exact Or.inr hev
  by_cases h3 : ∀ C, GetConfirmed S C → F ⪯ C
  · exact Or.inl ⟨h1, h2, h3⟩
  push Not at h3
  obtain ⟨C, hC, hFC⟩ := h3
  right
  -- the finalized height cannot be `0`: genesis precedes everything, `C` included
  have hσF : postState B_F = .state (postState' B_F hBF) := TransitionResult.state_get _ hBF
  have hcertF := certified_of_blockPostState (blockPostState_of_postState B_F hσF)
  have h1f : 1 ≤ h_f := by
    by_contra h0
    have hg : (postState' B_F hBF).F = .genesis := hcertF.fin0 (by rw [hhF]; omega)
    rw [hF] at hg
    exact hFC (by rw [hg]; exact genesis_preceq _)
  -- the cascade must be on its second branch, or `F ⪯ Σ.J ⪯ C`
  have hR : S.hmax ≠ S.h_j + 1 := by
    intro he
    have hRJ : S.R = S.J := by unfold Store.R; rw [if_pos he]
    exact hFC (Preceq.trans h1 (by rw [← hRJ]; exact hC.2.1))
  have hRF : S.R = S.F := by unfold Store.R; rw [if_neg hR]
  -- and the store-finalized block must be at or below `F`, or again `F ⪯ Σ.F ⪯ C`
  have hSFF : S.F ⪯ F := by
    rcases preceq_or_preceq S.J h1 hFJ with h | h
    · exact absurd (Preceq.trans h (by rw [← hRF]; exact hC.2.1)) hFC
    · exact h
  -- so `keyDom` applies at the record, and the frontier sits two above the store's key height
  have hkey := hinv.keyDom B σB hB (by rw [hJ]; exact hSFF)
  have hkey' : h_f ≤ S.h_j := by rcases hkey with h | ⟨h, -⟩ <;> omega
  obtain ⟨B₁, σ₁, hB₁, hJ₁, hh₁⟩ := hinv.jProv
  have hj_lt : S.h_j < S.hmax := by
    have g1 := (record_chained hinv hB₁).hj_lt_h
    have g2 := hinv.hmaxLe B₁ σ₁ hB₁
    omega
  -- the confirmed block is recorded at a state-height past `h_f`, which is Lemma 10's premise
  obtain ⟨σC, hσC, hhC⟩ := hC.2.2
  have hσC' : S.σ C = some σC := hσC
  have hltC : h_f < σC.h := by omega
  obtain ⟨A, hw, hev⟩ :=
    pastFinalized_evidence hBF hF hhF (record_postState hinv hσC') h1f hltC hFC
  refine ⟨A, hw, fun v hv => ?_⟩
  obtain ⟨a, b, hav, hbv, hai, hbi, he⟩ := hev v hv
  exact ⟨a, b, hav, hbv, Or.inl hai, IncludedOnEither.ofChain (record_mem_T hinv hσC') hbi, he⟩

end Store

section Exec
variable {Node Root : Type} [DecidableEq Node] [DecidableEq Root] [Electorate Node] [Params]
  [BlockHash Node Root]

/-- **Theorem 9 (`hft:thm:lockin`)'s content.** The store-level result at the later store: the
    record persists there (`reachesFrom_record`), and `StoreInv` and `F ⪯ J` hold at every
    store a validator holds. Nothing is chased across the steps — see the module docstring. -/
theorem lockIn [PositiveWeight Node] {sched : Schedule Node}
    {x : Exec (protocol (Node := Node) (Root := Root)) sched} {p : Node}
    {S S' : Store Node Root} (h : ReachesFrom x p S S')
    {B_F F : Blk Node Root} {h_f : Nat} {B : Blk Node Root}
    (hBF : postState B_F ≠ invalid)
    (hF : (postState' B_F).F = F) (hhf : (postState' B_F).h_F = h_f)
    (hB : get σB from S.σ B; σB.J = F ∧ σB.h_j = h_f) :
    (F ⪯ S'.J ∧ F ∈ viableTree S' ∧
      ∀ C, GetConfirmed S' C → F ⪯ C) ∨
      SlashableThird (fun a => IncludedOn a B_F ∨ IncludedOnSome a S'.T) := by
  obtain ⟨σB, hσB, hJ, hhj⟩ := hB
  have hσB' : S.σ B = some σB := hσB
  exact lockIn_store (reaches_storeInv (reaches_of_reachesFrom h))
    (reaches_FJ (reaches_of_reachesFrom h)) hBF hF hhf (reachesFrom_record h hσB') hJ hhj

end Exec

end Proofs

end Decoupled
