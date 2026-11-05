import LARuns.Goldilocks.Instance
import GoldilocksVariant.Final.Instance
import GoldilocksVariant.Final.RunFacts
import GoldilocksCorrectness.Record.Facts
import GoldilocksCorrectness.Record.Restated.Statements.Executions.OutputOrderStatements
import GoldilocksCorrectness.Record.Restated.Statements.Executions.SlashableEvidenceStatements
import GoldilocksCorrectness.Record.ScheduleGoldilocks

/-!
# Goldilocks's claims over its runs for the statements without healing premises

`goldilocks_satisfies_statement5_onRuns`: Goldilocks's specification satisfies statement 5 over its
runs, `GoldilocksSatisfiesStatement5OnRuns S`. The proof reads the run `π` as the trace
`toTrace (M.initial S.C) π` with the activity `activityOf π` (`GoldilocksVariant.Final.Projection`)
at the spec's model `M = Model.goldilocks`, and calls the restated statement
`finalized_ancestorEq_confirmed_of_exec` at the trace step `newIdx π i`, at which the trace holds the
run's configuration `i`.

`goldilocks_satisfies_statement6_onRuns`: Goldilocks's specification satisfies statement 6 over its
runs, `GoldilocksSatisfiesStatement6OnRuns S`, through the restated statement
`finalized_only_extends_of_exec` and the run's facts of the trace (`runFacts_toTrace`), which hold on
every run. `goldilocks_satisfies_statement7_onRuns`: statement 7 over its runs,
`GoldilocksSatisfiesStatement7OnRuns S`, through the restated statement
`finalized_compatible_of_no_slashable`.
-/

set_option autoImplicit false

namespace LARuns.GoldilocksInstance

open Goldilocks (NamedObject RootOrder Block NodeState Time)
open Goldilocks.Sts (Setup)
open GoldilocksVariant.Final (toTrace activityOf newIdx)
open GoldilocksCorrectness.Record (goldilocksFacts Model.goldilocks)

variable {V : Type} [DecidableEq V] [Fintype V] [RootOrder]

/-- **Statement 5 over Goldilocks's runs.** In every run of Goldilocks's node, seen through its
nodes' views, an honest node's finalized block is its confirmed tip or an ancestor of it.

Why: `v`'s view in configuration `i` is the view of its memory state there, which is the node state
of the trace `toTrace (M.initial S.C) π` at the trace step `newIdx π i`; `v`, honest in configuration
`i`, is honest in every earlier one (corruption is permanent), so honest through trace step
`newIdx π i`, whose earlier trace steps hold configurations up to `i`; the
restated statement `finalized_ancestorEq_confirmed_of_exec` then gives the conclusion, whose
finalized block and confirmed tip are the view's.

The variables:
- `S`: the setup. -/
theorem goldilocks_satisfies_statement5_onRuns (S : Setup V) :
    GoldilocksSatisfiesStatement5OnRuns S := by
  intro π _ _ v i l hl hH
  obtain ⟨lc, hlc, rfl⟩ := Option.map_eq_some_iff.mp hl
  have hH' : (toTrace ((Model.goldilocks (V := V)).initial S.C) π).HonestThrough (activityOf π)
      (newIdx π i) v := by
    intro i' hi'
    rw [GoldilocksVariant.Final.corrupted_activityOf]
    have hle := GoldilocksVariant.Final.origBefore_mono π hi'
    rw [GoldilocksVariant.Final.origBefore_newIdx] at hle
    exact fun h => hH (π.adv_mono hle h)
  have key := GoldilocksCorrectness.Record.Statements.Executions.finalized_ancestorEq_confirmed_of_exec
    (Model.goldilocks (V := V)) goldilocksFacts (activityOf π)
    (toTrace ((Model.goldilocks (V := V)).initial S.C) π) (newIdx π i) v hH'
  have hst : (toTrace ((Model.goldilocks (V := V)).initial S.C) π).st (newIdx π i) v = lc.st := by
    exact (GoldilocksVariant.Final.toTrace_st_newIdx _ π i v).trans
      (GoldilocksVariant.Final.lastKnownSt_of_some _ π hlc)
  have key' : ((Model.goldilocks (V := V)).finalized lc.st).AncestorEq
      ((Model.goldilocks (V := V)).ac_confirmed lc.st) := hst ▸ key
  exact key'

/-- **Statement 6 over Goldilocks's runs.** In every run of Goldilocks's node, seen through its
nodes' views, an honest node never abandons a block it has finalized.

Why: the views of `v` in configurations `i ≤ j` are the views of the node states of the trace
`toTrace (M.initial S.C) π` at the trace steps `newIdx π i ≤ newIdx π j`; `v`, honest in
configuration `j`, is honest through trace step `newIdx π j`; the trace meets the run's facts
(`runFacts_toTrace`), and the restated statement `finalized_only_extends_of_exec` gives the
conclusion.

The variables:
- `S`: the setup. -/
theorem goldilocks_satisfies_statement6_onRuns (S : Setup V) :
    GoldilocksSatisfiesStatement6OnRuns S := by
  intro π _ _ v i j l l' hij hl hl' hH
  obtain ⟨lc, hlc, rfl⟩ := Option.map_eq_some_iff.mp hl
  obtain ⟨lc', hlc', rfl⟩ := Option.map_eq_some_iff.mp hl'
  have hH' : (toTrace ((Model.goldilocks (V := V)).initial S.C) π).HonestThrough (activityOf π)
      (newIdx π j) v := by
    intro i' hi'
    rw [GoldilocksVariant.Final.corrupted_activityOf]
    have hle := GoldilocksVariant.Final.origBefore_mono π hi'
    rw [GoldilocksVariant.Final.origBefore_newIdx] at hle
    exact fun h => hH (π.adv_mono hle h)
  have key := GoldilocksCorrectness.Record.Statements.Executions.finalized_only_extends_of_exec
    (Model.goldilocks (V := V)) goldilocksFacts S (activityOf π)
    (toTrace ((Model.goldilocks (V := V)).initial S.C) π)
    (GoldilocksVariant.Final.runFacts_toTrace goldilocksFacts π) v (newIdx π i) (newIdx π j)
    ((GoldilocksVariant.Final.newIdx_strictMono π).monotone hij) hH'
  have hst : (toTrace ((Model.goldilocks (V := V)).initial S.C) π).st (newIdx π i) v = lc.st :=
    (GoldilocksVariant.Final.toTrace_st_newIdx _ π i v).trans
      (GoldilocksVariant.Final.lastKnownSt_of_some _ π hlc)
  have hst' : (toTrace ((Model.goldilocks (V := V)).initial S.C) π).st (newIdx π j) v = lc'.st :=
    (GoldilocksVariant.Final.toTrace_st_newIdx _ π j v).trans
      (GoldilocksVariant.Final.lastKnownSt_of_some _ π hlc')
  rw [hst, hst'] at key
  exact key

omit [RootOrder] in
/-- The node state the trace gives `v` at configuration `n` of `π` is `init v`, or the memory state
of a local state of `v` known in a configuration `m ≤ n`.

The variables:
- `init`: the node states before a local state is known; `π`: the run; `n`: the configuration;
  `v`: the validator. -/
theorem lastKnownSt_cases {Node Msg N Ev : Type} [DecidableEq Node] [DecidableEq Msg]
    {Pr : RStsVariant2.Protocol Node Msg N Ev} (init : Node → N) (π : RStsVariant2.Exec Pr)
    (n : ℕ) (v : Node) :
    GoldilocksVariant.Final.lastKnownSt init π n v = init v ∨
      ∃ (m : ℕ) (l : RStsVariant2.Local Node Msg N), m ≤ n ∧ π[m][v] = some l ∧
        GoldilocksVariant.Final.lastKnownSt init π n v = l.st := by
  induction n with
  | zero =>
    cases h : π[0][v] with
    | none => left; simp [GoldilocksVariant.Final.lastKnownSt, h]
    | some l => right; exact ⟨0, l, le_rfl, h, by simp [GoldilocksVariant.Final.lastKnownSt, h]⟩
  | succ n ih =>
    cases h : π[n + 1][v] with
    | none =>
      have he : GoldilocksVariant.Final.lastKnownSt init π (n + 1) v =
          GoldilocksVariant.Final.lastKnownSt init π n v := by
        simp [GoldilocksVariant.Final.lastKnownSt, h]
      rw [he]
      rcases ih with h0 | ⟨m, l, hm, hl, hst⟩
      · exact Or.inl h0
      · exact Or.inr ⟨m, l, by omega, hl, hst⟩
    | some l =>
      right
      exact ⟨n + 1, l, le_rfl, h, by simp [GoldilocksVariant.Final.lastKnownSt, h]⟩

/-- **Statement 7 over Goldilocks's runs.** In every run of Goldilocks's node, seen through its
nodes' views, with no slashable evidence between the blocks honest nodes hold, no two honest nodes
finalize conflicting blocks, unless a root collision hits the blocks they hold.

Why: the trace `toTrace (M.initial S.C) π` meets the run's facts (`runFacts_toTrace`), and the
restated statement `finalized_compatible_of_no_slashable` gives the conclusion at the trace steps
`newIdx π i`, `newIdx π j`. Its premise reads the trees of validators
honest through any trace step: each such tree is the tree of a view of a validator honest in a
configuration of `π` (`lastKnownSt_cases`), or the initial tree `{genesis}`, and the genesis block
is in the tree of `v₁`'s view in configuration `i` (`lem11_node_invariantCore_of_run`); the claim's
premise then excludes slashable evidence between them. The slashable evidence of the model is
Goldilocks's (`goldilocks_SlashableBetween`), and the two disjuncts are read through
`compatible_iff` and the roots.

The variables:
- `S`: the setup. -/
theorem goldilocks_satisfies_statement7_onRuns (S : Setup V) :
    GoldilocksSatisfiesStatement7OnRuns S := by
  intro π _ _ hNo v₁ v₂ i j l₁ l₂ hl₁ hH₁ hl₂ hH₂
  obtain ⟨lc₁, hlc₁, rfl⟩ := Option.map_eq_some_iff.mp hl₁
  obtain ⟨lc₂, hlc₂, rfl⟩ := Option.map_eq_some_iff.mp hl₂
  set x := toTrace ((Model.goldilocks (V := V)).initial S.C) π with hx
  have R := GoldilocksVariant.Final.runFacts_toTrace goldilocksFacts π
  -- honest in a configuration of `π` gives honest through the trace step that holds it
  have honest : ∀ (n : ℕ) (w : V), w ∉ π[n].adv → x.HonestThrough (activityOf π) (newIdx π n) w := by
    intro n w hw i' hi'
    rw [GoldilocksVariant.Final.corrupted_activityOf]
    have hle := GoldilocksVariant.Final.origBefore_mono π hi'
    rw [GoldilocksVariant.Final.origBefore_newIdx] at hle
    exact fun h => hw (π.adv_mono hle h)
  have hst : ∀ (n : ℕ) (w : V) (l : RStsVariant2.Local V (NamedObject V) (NodeState V)),
      π[n][w] = some l → x.st (newIdx π n) w = l.st := fun n w l h =>
    (GoldilocksVariant.Final.toTrace_st_newIdx _ π n w).trans
      (GoldilocksVariant.Final.lastKnownSt_of_some _ π h)
  -- the genesis block is in `v₁`'s tree in configuration `i`
  have hgen : Block.genesis ∈ lc₁.st.S.T := by
    have h := (goldilocksFacts.nd.nodeInvCore_treeClosed
      ((GoldilocksCorrectness.Record.Proofs.Executions.lem11_node_invariantCore_of_run
        (Model.goldilocks (V := V)) goldilocksFacts) S x R (newIdx π i) v₁).1).1
    rw [hst i v₁ lc₁ hlc₁] at h
    exact h
  -- a block of the tree of a validator honest through a trace step is in the tree of a view of a
  -- validator honest in a configuration of `π`
  have hview : ∀ (k : ℕ) (w : V), x.HonestThrough (activityOf π) k w → ∀ b ∈ (x.st k w).tree,
      ∃ (w' : V) (m : ℕ) (l : RStsVariant2.Local V (NamedObject V) (NodeState V)),
        π[m][w'] = some l ∧ w' ∉ π[m].adv ∧ b ∈ l.st.S.T := by
    intro k w hw b hb
    have hb' : b ∈ (GoldilocksVariant.Final.lastKnownSt (NodeState := NodeState V)
        (fun v => (Model.goldilocks (V := V)).initial S.C v) π
        (GoldilocksVariant.Final.origBefore π k) w).S.T := hb
    rcases lastKnownSt_cases (N := NodeState V) (fun v => (Model.goldilocks (V := V)).initial S.C v)
        π (GoldilocksVariant.Final.origBefore π k) w with h0 | ⟨m, l, hm, hl, he⟩
    · rw [h0] at hb'
      have hT0 : ((Model.goldilocks (V := V)).initial S.C w).tree = {Block.genesis} :=
        goldilocksFacts.init.initial_tree S.C w
      have hb'' : b ∈ ((Model.goldilocks (V := V)).initial S.C w).tree := hb'
      rw [hT0, Finset.mem_singleton] at hb''
      subst hb''
      exact ⟨v₁, i, lc₁, hlc₁, hH₁, hgen⟩
    · rw [he] at hb'
      have hadv : w ∉ π[GoldilocksVariant.Final.origBefore π k].adv := by
        have := hw k le_rfl
        rwa [GoldilocksVariant.Final.corrupted_activityOf] at this
      exact ⟨w, m, l, hl, fun h => hadv (π.adv_mono hm h), hb'⟩
  have hNoSlash : ∀ (i' j' : ℕ) (w₁ w₂ : V), x.HonestThrough (activityOf π) i' w₁ →
      x.HonestThrough (activityOf π) j' w₂ →
      ∀ b₁ ∈ (x.st i' w₁).tree, ∀ b₂ ∈ (x.st j' w₂).tree,
        ¬ GoldilocksCorrectness.Record.Statements.Routines.SlashableBetween
          (Model.goldilocks (V := V)) b₁ b₂ := by
    intro i' j' w₁ w₂ h₁ h₂ b₁ hb₁ b₂ hb₂
    obtain ⟨u₁, m₁, k₁, hk₁, ha₁, hT₁⟩ := hview i' w₁ h₁ b₁ hb₁
    obtain ⟨u₂, m₂, k₂, hk₂, ha₂, hT₂⟩ := hview j' w₂ h₂ b₂ hb₂
    rw [← GoldilocksCorrectness.Record.Statements.Routines.goldilocks_SlashableBetween]
    exact hNo u₁ u₂ m₁ m₂ (NodeViewOf.view k₁.st) (NodeViewOf.view k₂.st)
      (Option.map_eq_some_iff.mpr ⟨k₁, hk₁, rfl⟩) ha₁
      (Option.map_eq_some_iff.mpr ⟨k₂, hk₂, rfl⟩) ha₂ b₁ hT₁ b₂ hT₂
  have key := GoldilocksCorrectness.Record.Statements.Executions.finalized_compatible_of_no_slashable
    (Model.goldilocks (V := V)) goldilocksFacts GoldilocksCorrectness.Record.fixedValidators_goldilocks
    S (activityOf π) x R hNoSlash (newIdx π i) (newIdx π j) v₁ v₂ (honest i v₁ hH₁) (honest j v₂ hH₂)
  rw [hst i v₁ lc₁ hlc₁, hst j v₂ lc₂ hlc₂] at key
  rcases key with hc | ⟨X, hX, Y, hY, hr, hne⟩
  · left
    exact (GoldilocksCorrectness.Proofs.Routines.compatible_iff _ _).1 hc
  · right
    rw [Finset.mem_union] at hX hY
    exact ⟨X, Y, hX, hY, hr, hne⟩

end LARuns.GoldilocksInstance
